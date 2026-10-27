module

public import CFSG.Dihedral.OriginalFourgroupsGeneral
public import CFSG.Dihedral.GorensteinWalter
public import CFSG.Dihedral.GorensteinWalter.PSL2OddCentralizerNormalizer

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem normalizer_eq_centralizer_of_psl2_model
    (hR : d.R ≠ ⊥) (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : G ≃* PSL2 K) : d.N = d.C := by
  have ht := d.t_isInvolution_general
  have hte : BenderSuzuki.PFAppendixIII.IsInvolution (e d.t) := by
    refine ⟨?_, ?_⟩
    · intro h
      exact ht.1 (e.injective (by simpa using h))
    · simpa using congrArg e ht.2
  let X := d.R.map e.toMonoidHom
  have hXne : X ≠ ⊥ := by
    intro h
    apply hR
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa only [Subgroup.map_bot] using h
  have hXodd : ∀ x : PSL2 K, x ∈ X → Odd (orderOf x) := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
    change Odd (orderOf (e r))
    rw [e.orderOf_eq]
    exact d.R_odd.of_dvd_nat (d.R.orderOf_dvd_natCard hr)
  have hXcent : X ≤ Subgroup.centralizer ({e d.t} : Set (PSL2 K)) := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hrC : r ∈ Subgroup.centralizer ({d.t} : Set G) := by
      simpa only [d.centralizer, t] using d.R_le hr
    simpa using congrArg e (Subgroup.mem_centralizer_singleton_iff.mp hrC)
  have hN := psl2_odd_centralizer_normalizer hK hte X hXne hXodd hXcent
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  change (Subgroup.normalizer (d.R : Set G)).map e.toMonoidHom =
    d.C.map e.toMonoidHom
  rw [Subgroup.map_equiv_normalizer_eq, d.centralizer]
  change Subgroup.normalizer (X : Set (PSL2 K)) =
    (Subgroup.centralizer ({d.t} : Set G)).map e.toMonoidHom
  rw [CFSG.centralizer_singleton_map]
  exact hN

theorem aSeven_model_of_strict_normalizer [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hR : d.R ≠ ⊥) (hCN : d.C < d.N) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) := by
  rcases gorenstein_walter G hnonab d.S ⟨_, d.sylow_dihedral⟩ with
    h7 | ⟨p, k, hp, hpodd, hlarge, he⟩
  · exact h7
  · let : Fact p.Prime := hp
    have hk : 1 ≤ k := by
      by_contra h
      have hk0 : k = 0 := by omega
      simp [hk0] at hlarge
    have hfield : IsOddPrimePower (Nat.card (GaloisField p k)) :=
      ⟨p, k, hp.out, hpodd, hk, GaloisField.card p k (by omega)⟩
    exact (hCN.ne' (d.normalizer_eq_centralizer_of_psl2_model hR _ hfield he.some)).elim

end CFSG.DihedralBlueprint.OriginalData
