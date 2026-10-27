module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseReflection
public import CFSG.Dihedral.GorensteinWalter
public import CFSG.Dihedral.OriginalCosetModel
public import CFSG.GroupTheory.CentralizerMap

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem R_isCyclic_of_aSeven_model (e : G ≃* alternatingGroup (Fin 7)) :
    IsCyclic d.R := by
  by_cases hR : d.R = ⊥
  · rw [hR]
    infer_instance
  · let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card (d.R_card_of_aSeven_model hR e)

theorem R_isCyclic_of_psl2_model (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : G ≃* PSL2 K) : IsCyclic d.R := by
  have ht : BenderSuzuki.PFAppendixIII.IsInvolution (e d.t) := by
    refine ⟨?_, ?_⟩
    · intro h
      exact d.t_isInvolution_general.1 (e.injective (by simpa using h))
    · simpa only [map_pow, map_one] using congrArg e d.t_isInvolution_general.2
  obtain ⟨T, s, hTcyclic, _, _, _, _, htorus⟩ :=
    secondCase_reflection_psl2_torus K hK ht
  have hRodd : ∀ x : PSL2 K, x ∈ d.R.map e.toMonoidHom → Odd (orderOf x) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    change Odd (orderOf (e y))
    rw [e.orderOf_eq]
    exact d.R_odd.of_dvd_nat (d.R.orderOf_dvd_natCard hy)
  have hRC : d.R.map e.toMonoidHom ≤
      Subgroup.centralizer ({e d.t} : Set (PSL2 K)) := by
    rw [← centralizer_singleton_map]
    apply Subgroup.map_mono
    simpa only [d.centralizer, t] using d.R_le
  let : IsCyclic T := hTcyclic
  have hmap : IsCyclic (d.R.map e.toMonoidHom) :=
    Subgroup.isCyclic_of_le (htorus _ hRodd hRC)
  exact (MulEquiv.isCyclic (e.subgroupMap d.R)).mpr hmap

theorem R_isCyclic [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    IsCyclic d.R := by
  rcases gorenstein_walter G hnonab d.S
      ⟨2 ^ (d.n - 1), d.sylow_mulEquiv_dihedral⟩ with hA | hL
  · exact d.R_isCyclic_of_aSeven_model hA.some
  · obtain ⟨r, k, hr, hrodd, hsize, ⟨e⟩⟩ := hL
    let _ : Fact r.Prime := hr
    have hk : k ≠ 0 := by
      intro h
      simp [h] at hsize
    have hK : IsOddPrimePower (Nat.card (GaloisField r k)) :=
      ⟨r, k, hr.out, hrodd, by omega, GaloisField.card r k hk⟩
    exact d.R_isCyclic_of_psl2_model (GaloisField r k) hK e

theorem invertedSubgroup_le (H : Subgroup G) (v : G) :
    d.invertedSubgroup H v ≤ d.R ⊓ H := by
  apply (Subgroup.closure_le _).mpr
  intro u hu
  exact hu.1

theorem invertedSubgroup_isCyclic [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (H : Subgroup G) (v : G) :
    IsCyclic (d.invertedSubgroup H v) := by
  let : IsCyclic d.R := d.R_isCyclic hnonab
  exact Subgroup.isCyclic_of_le ((d.invertedSubgroup_le H v).trans inf_le_left)

end CFSG.DihedralBlueprint.OriginalData
