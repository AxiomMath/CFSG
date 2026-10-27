module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismUnitaryTransport

public section

namespace CFSG.ProperTwoGeneratedCore.UnitaryKernels

open CFSG.BenderSuzuki.MatrixGroups CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.ProperTwoGeneratedCore.RootCenter

universe u

theorem isSolvable_dihedralGroup (n : ℕ) [NeZero n] : Group.IsSolvable (DihedralGroup n) := by
  classical
  let R : Subgroup (DihedralGroup n) := Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup n)
  have hRnormal : R.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases g with i | i
    · refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      simp [DihedralGroup.r_mul_r]
    · refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
      simp [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.inv_sr]
  have : IsCyclic R := Subgroup.isCyclic_zpowers _
  let : CommGroup R := IsCyclic.commGroup
  have hRcard : Nat.card R = n := by rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have hQcard : Nat.card (DihedralGroup n ⧸ R) = 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup R
    rw [DihedralGroup.nat_card, hRcard] at h
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    exact (Nat.eq_of_mul_eq_mul_right hn h).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (DihedralGroup n ⧸ R) := isCyclic_of_prime_card hQcard
  let : CommGroup (DihedralGroup n ⧸ R) := IsCyclic.commGroup
  exact Group.isSolvable_of_ker_le_range R.subtype (QuotientGroup.mk' R)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

variable {X : Type*} [Group X]

theorem isSolvable_of_sup {A N D : Subgroup X} (hNA : N ≤ A) (hDA : D ≤ A) (hsup : N ⊔ D = A)
    (hnormal : (N.subgroupOf A).Normal) [Group.IsSolvable N] [Group.IsSolvable D] :
    Group.IsSolvable A := by
  have hN' : Group.IsSolvable (N.subgroupOf A) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hNA).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNA).injective
  have hD' : Group.IsSolvable (D.subgroupOf A) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hDA).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hDA).injective
  have htop : N.subgroupOf A ⊔ D.subgroupOf A = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNA hDA, hsup, Subgroup.subgroupOf_self]
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (N.subgroupOf A)).comp (D.subgroupOf A).subtype) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf A) y
    have hx : x ∈ ((N.subgroupOf A ⊔ D.subgroupOf A : Subgroup A) : Set A) := by
      rw [htop]
      exact Set.mem_univ x
    rw [Subgroup.normal_mul] at hx
    obtain ⟨n, hn, d, hd, rfl⟩ := hx
    refine ⟨⟨d, hd⟩, ?_⟩
    change QuotientGroup.mk' (N.subgroupOf A) d = QuotientGroup.mk' (N.subgroupOf A) (n * d)
    have hn1 : QuotientGroup.mk' (N.subgroupOf A) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [map_mul, hn1, one_mul]
  have : Group.IsSolvable (A ⧸ N.subgroupOf A) := Group.isSolvable_of_surjective hsurj
  exact Group.isSolvable_of_subgroup_quotient (N.subgroupOf A)

structure UnitaryRootCenterData {F : Type u} [Group F] (R U : Subgroup F) : Prop where
  mem_iff : ∀ x, x ∈ U ↔ x ∈ R ∧ ∀ y ∈ R, x * y = y * x
  sq_mem : ∀ x ∈ R, x ^ 2 ∈ U
  injOn_conj : Set.InjOn MulAut.conj (R : Set F)
  aut_sq : ∀ γ ∈ rootCenterAut R U, γ ^ 2 ∈ U.map MulAut.conj →
    γ ∈ R.map MulAut.conj ∨ γ ^ 2 = 1
  fix_eq : ∀ R₀ : Subgroup F, U ≤ R₀ → R₀ ≤ R → R₀.relIndex R ≤ 2 →
    {γ | γ ∈ rootCenterAut R U ∧ ∀ x ∈ R₀, γ x = x} = (U.map MulAut.conj : Set (MulAut F))
  solvable : Group.IsSolvable (rootCenterAut R U)

theorem sq_mem_unitaryRootCenter {K : Type} [Field K] [CharP K 2] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {x : ProjectiveSpecialUnitaryMatrixGroup J}
    (hx : x ∈ unitaryCoverRoot J hJ) : x ^ 2 ∈ unitaryRootCenter J hJ := by
  obtain ⟨c, rfl⟩ := hx
  exact ⟨c ^ 2, (mem_ker_firstCoord J).mpr (fst_pow_two J c), map_pow _ c 2⟩

theorem unitaryRootCenterData_of_mulEquiv {F : Type u} [Group F] {K : Type} [Field K] [Finite K]
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (e : F ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (S : Sylow 2 F) :
    Nat.card (S : Subgroup F) = (2 ^ f) ^ 3 ∧
      UnitaryRootCenterData (S : Subgroup F)
        ((CFSG.omega₁ (G := (S : Subgroup F)) (p := 2)).map (S : Subgroup F).subtype) := by
  have : CharP K 2 := charP_two_of_card f hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite F := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨⟨ε, hεR, hεU, -⟩, hmem, hinj, ⟨D, -, hsup, hnormal, -, ⟨hDe⟩⟩, hsq, hfix, -, -⟩ :=
    even_unitary_root_center_automorphisms_of_mulEquiv J f hf hcard hfixed hJ e S _ rfl
  set U := (CFSG.omega₁ (G := (S : Subgroup F)) (p := 2)).map (S : Subgroup F).subtype
  refine ⟨?_, ⟨hmem, ?_, hinj, hsq, hfix, ?_⟩⟩
  · rw [← hεR, Subgroup.card_map_of_injective ε.injective]
    exact (unitaryCoverRoot_nativeStructure J (2 ^ f) hcard hfixed hJ).1
  · intro x hx
    rw [← hεR] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    rw [← hεU, ← map_pow]
    exact Subgroup.mem_map_of_mem _ (sq_mem_unitaryRootCenter J hJ hr)
  · have hcR : (S : Subgroup F).map MulAut.conj ≤ rootCenterAut (S : Subgroup F) U := by
      rw [← hsup]
      exact le_sup_left
    have hDA : D ≤ rootCenterAut (S : Subgroup F) U := by
      rw [← hsup]
      exact le_sup_right
    have hSsolv : Group.IsSolvable (S : Subgroup F) := by
      have := (S.isPGroup').isNilpotent
      infer_instance
    have : Group.IsSolvable ((S : Subgroup F).map MulAut.conj) :=
      Group.isSolvable_of_surjective
        (MonoidHom.subgroupMap_surjective MulAut.conj (S : Subgroup F))
    have : NeZero (2 ^ f + 1) := ⟨by omega⟩
    have : Group.IsSolvable (DihedralGroup (2 ^ f + 1)) := isSolvable_dihedralGroup _
    have : Group.IsSolvable D :=
      Group.isSolvable_of_isSolvable_injective (f := hDe.toMonoidHom) hDe.injective
    exact isSolvable_of_sup hcR hDA hsup hnormal

end CFSG.ProperTwoGeneratedCore.UnitaryKernels
