module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Rest7
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma65Comm
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.SemidihedralAut

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def Fin76bWFacts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B : Subgroup G), Rest6Config L z t T₀ E Q x β B →
    WFacts L t E

@[expose] def SemidihedralAutSolvable : Prop :=
  ∀ n : ℕ, 4 ≤ n → Group.IsSolvable (MulAut (SemidihedralGroup n))

theorem semidihedralAutSolvable : SemidihedralAutSolvable := fun n hn =>
  semidihedral_mulAut_isSolvable n hn

@[expose] def Fin76bLemma65bBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B : Subgroup G), Rest6Config L z t T₀ E Q x β B →
    WFacts L t E → ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (E : Set G) →
      (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) → z ∈ S →
      (∀ b ∈ B, ∀ s ∈ S, b * s = s * b) → Nonempty (S ≃* DihedralGroup 4)

theorem isSolvable_mulAut_of_dihedral {S : Type*} [Group S] [Finite S] {k : ℕ} (hk : 2 ≤ k)
    (e : S ≃* DihedralGroup (2 ^ k)) : Group.IsSolvable (MulAut S) := by
  have h2 : IsPGroup 2 (MulAut (DihedralGroup (2 ^ k))) :=
    CFSG.GorensteinWalter.dihedral_mulAut_is_twoGroup hk
  have h3 : IsPGroup 2 (MulAut S) := h2.of_equiv (MulAut.congr e).symm
  have := h3.isNilpotent
  infer_instance

theorem isSolvable_mulAut_congr {S S' : Type*} [Group S] [Group S'] (e : S ≃* S')
    (h : Group.IsSolvable (MulAut S')) : Group.IsSolvable (MulAut S) :=
  Group.isSolvable_of_isSolvable_injective (f := (MulAut.congr e).toMonoidHom)
    (MulAut.congr e).injective

@[expose] def Fin76bNoOrderEight : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B : Subgroup G), Rest6Config L z t T₀ E Q x β B →
    WFacts L t E → ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (E : Set G) →
      (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) → z ∈ S →
      (∀ b ∈ B, ∀ s ∈ S, b * s = s * b) → ∀ u ∈ S, orderOf u ≠ 8

@[expose] def Fin76bNoKleinFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B : Subgroup G), Rest6Config L z t T₀ E Q x β B →
    WFacts L t E → ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (E : Set G) →
      (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) → z ∈ S →
      (∀ b ∈ B, ∀ s ∈ S, b * s = s * b) → S ≠ zpowers z ⊔ zpowers t

theorem exists_orderOf_eight_dihedral {S : Type*} [Group S] {k : ℕ} (hk : 3 ≤ k)
    (e : S ≃* DihedralGroup (2 ^ k)) : ∃ u : S, orderOf u = 8 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  have h1 : orderOf (DihedralGroup.r 1 : DihedralGroup (2 ^ (j + 3))) = 2 ^ (j + 3) :=
    DihedralGroup.orderOf_r_one
  have hdvd : 2 ^ j ∣ orderOf (DihedralGroup.r 1 : DihedralGroup (2 ^ (j + 3))) := by
    rw [h1]; exact pow_dvd_pow 2 (by omega)
  refine ⟨e.symm (DihedralGroup.r 1 ^ (2 ^ j)), ?_⟩
  rw [MulEquiv.orderOf_eq, orderOf_pow_of_dvd (by positivity) hdvd, h1, pow_add,
    Nat.mul_div_cancel_left _ (by positivity)]
  norm_num

theorem exists_orderOf_eight_semidihedral {S : Type*} [Group S] {n : ℕ} (hn : 4 ≤ n)
    (e : S ≃* SemidihedralGroup n) : ∃ u : S, orderOf u = 8 := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
  have h1 : orderOf (CFSG.Semidihedral.r (j + 4)) = 2 ^ (j + 3) :=
    CFSG.Semidihedral.orderOf_r (j + 4) (by omega)
  have hdvd : 2 ^ j ∣ orderOf (CFSG.Semidihedral.r (j + 4)) := by
    rw [h1]; exact pow_dvd_pow 2 (by omega)
  refine ⟨e.symm (CFSG.Semidihedral.r (j + 4) ^ (2 ^ j)), ?_⟩
  rw [MulEquiv.orderOf_eq, orderOf_pow_of_dvd (by positivity) hdvd, h1, pow_add,
    Nat.mul_div_cancel_left _ (by positivity)]
  norm_num

theorem fin76bBound_of_residuals (h1 : Fin76bNoOrderEight) (h2 : Fin76bNoKleinFour) :
    Fin76bLemma65bBound := by
  intro G _ _ L z t T₀ E Q x β B hconf hW S hS2 hSC hSmax hzS hBS
  rcases hconf.shape S hS2 hSC hSmax hzS with hV | ⟨k, hk, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact absurd hV (h2 G L z t T₀ E Q x β B hconf hW S hS2 hSC hSmax hzS hBS)
  · by_cases hk3 : 3 ≤ k
    · obtain ⟨u, hu⟩ := exists_orderOf_eight_dihedral hk3 e
      exact absurd (by rw [Subgroup.orderOf_coe]; exact hu)
        (h1 G L z t T₀ E Q x β B hconf hW S hS2 hSC hSmax hzS hBS (u : G) u.2)
    · have hk2 : k = 2 := by omega
      subst hk2
      exact ⟨e⟩
  · obtain ⟨u, hu⟩ := exists_orderOf_eight_semidihedral hn e
    exact absurd (by rw [Subgroup.orderOf_coe]; exact hu)
      (h1 G L z t T₀ E Q x β B hconf hW S hS2 hSC hSmax hzS hBS (u : G) u.2)

theorem fin76bLemma65b_of_bound (hWF : Fin76bWFacts) (hB : Fin76bLemma65bBound) :
    Fin76bLemma65b := by
  have hSD : SemidihedralAutSolvable := semidihedralAutSolvable
  intro G _ _ L z t T₀ E Q x β B hconf S hS2 hSC hSmax hzS
  have hW : WFacts L t E := hWF G L z t T₀ E Q x β B hconf
  have hBS : ∀ b ∈ B, ∀ s ∈ S, b * s = s * b := by
    rcases hconf.shape S hS2 hSC hSmax hzS with hV | ⟨k, hk, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    ·
      intro b hb s hs
      have hbz : b * z = z * b := hconf.cfg.z_comm_of_mem_A (hconf.B_le hb)
      have hbt : b * t = t * b := mem_centralizer_singleton_iff.1 (hconf.B_cent hb)
      have hle : S ≤ centralizer ({b} : Set G) := by
        rw [hV, sup_le_iff, zpowers_le, zpowers_le]
        exact ⟨mem_centralizer_singleton_iff.2 hbz.symm, mem_centralizer_singleton_iff.2 hbt.symm⟩
      exact (mem_centralizer_singleton_iff.1 (hle hs)).symm
    · have : Group.IsSolvable (MulAut ↥S) := isSolvable_mulAut_of_dihedral hk e
      exact B_centralizes_S hconf.cfg hconf.econfig hW hconf.B_le hconf.B_cent hconf.B_iso hS2
        hSC hSmax hzS
    · have : Group.IsSolvable (MulAut ↥S) := isSolvable_mulAut_congr e (hSD n hn)
      exact B_centralizes_S hconf.cfg hconf.econfig hW hconf.B_le hconf.B_cent hconf.B_iso hS2
        hSC hSmax hzS
  exact ⟨hB G L z t T₀ E Q x β B hconf hW S hS2 hSC hSmax hzS hBS, hBS⟩

end CFSG.EvenSporadicStandard.Fin76b
