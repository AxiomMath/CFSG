module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OFix

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Blueprint
open scoped commutatorElement

namespace E3S3O

variable {G : Type} [Group G] [Finite G]

theorem le_sup_oddCoreOf {r : ℕ} {Ω : Set (Subgroup G)} (hΩ : TypeRFam r Ω)
    {Pm : Set (Subgroup G)} (hPm : Pm ⊆ Ω)
    (hgen : ∀ M ∈ Pm, Subgroup.closure {x | x ∈ M ∧ IsPGroup 2 (Subgroup.zpowers x)} = M)
    {X : Subgroup G} (hX : X = ⨆ M ∈ Pm, M) (hPmX : ∀ M ∈ Pm, ∀ c ∈ X, conjSub c M ∈ Pm) {a : G}
    (ha2 : a * a = 1) (haX : a ∈ Subgroup.normalizer (X : Set G))
    (hc : ∀ y ∈ X, ⁅a, y⁆ ∈ oddCoreOf X) :
    X ≤ (⨆ M ∈ {M | M ∈ Pm ∧ XMem Ω a M}, coreAt a M) ⊔ oddCoreOf X := by
  classical
  set D := ⨆ M ∈ {M | M ∈ Pm ∧ XMem Ω a M}, coreAt a M with hD
  set N := oddCoreOf X with hNdef
  have hNodd : Odd (Nat.card N) := oddCoreOf_odd_natCard X
  have hXN : X ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hx)
  have haN : a ∈ Subgroup.normalizer (N : Set G) := mem_normalizer_oddCore_of_mem_normalizer haX
  have hNX : N ≤ X := oddCoreOf_le_self X
  have ha2' : IsPGroup 2 (Subgroup.zpowers a) := Balance.isPGroup_zpowers_of_mul_self_eq_one ha2
  have key : ∀ M ∈ Pm, ∀ Q₁, IsSylow2In Q₁ M → Q₁ ≤ D ⊔ N := by
    intro M hM Q₁ hQ₁
    have hMX : M ≤ X := hX ▸ le_iSup₂ (f := fun M (_ : M ∈ Pm) => M) M hM
    have hQ₁X : Q₁ ≤ X := hQ₁.1.trans hMX
    have hQ₁N : Q₁ ≤ Subgroup.normalizer (N : Set G) := hQ₁X.trans hXN
    have hQ₁H : IsSylow2In Q₁ (N ⊔ Q₁) :=
      Sec6Gen.isSylow2In_of_eq_sup_odd hNodd hQ₁N le_sup_right hQ₁.2.1 rfl
    have hH₁X : N ⊔ Q₁ ≤ X := sup_le hNX hQ₁X
    have haH : conjSub a (N ⊔ Q₁) = N ⊔ Q₁ := by
      have hle : conjSub a (N ⊔ Q₁) ≤ N ⊔ Q₁ := by
        intro y hy
        rw [mem_conjSub_iff] at hy
        have e : y = ⁅a, a⁻¹ * y * a⁆ * (a⁻¹ * y * a) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (N ⊔ Q₁).mul_mem (le_sup_left (a := N) (hc _ (hH₁X hy))) hy
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      exact (Subgroup.card_map_of_injective (K := N ⊔ Q₁) (f := (MulAut.conj a).toMonoidHom)
        (fun x y hxy => (MulAut.conj a).injective hxy)).symm.le
    have hQ₁aH : IsSylow2In (conjSub a Q₁) (N ⊔ Q₁) := by
      have h1 := hQ₁H.conj a
      rwa [haH] at h1
    obtain ⟨c, hcH, hcQ⟩ := S1916.IsSylow2In.exists_conj hQ₁H hQ₁aH
    obtain ⟨o, ho, q, hq, rfl⟩ := Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer hQ₁N hcH
    have hoQ : conjSub o Q₁ = conjSub a Q₁ := by
      rw [← hcQ, conjSub_mul, conjSub_eq_self_of_mem hq]
    have hperm : ∀ v ∈ Subgroup.zpowers a, ∃ n ∈ N, conjSub v Q₁ = conjSub n Q₁ := by
      intro v hv
      rcases Balance.Bootstrap.mem_zpowers_involution ha2 hv with rfl | rfl
      · exact ⟨1, N.one_mem, rfl⟩
      · exact ⟨o, ho, hoQ.symm⟩
    obtain ⟨n, hn, hnN⟩ :=
      exists_conj_normalizer_of_perm hNodd Q₁ ha2' (Subgroup.zpowers_le.mpr haN) hperm
    have haQ₂ := hnN (Subgroup.mem_zpowers a)
    have hnX : n ∈ X := hNX hn
    have hQ₂X : conjSub n Q₁ ≤ X := by
      intro y hy
      rw [mem_conjSub_iff] at hy
      have h1 := X.mul_mem (X.mul_mem hnX (hQ₁X hy)) (X.inv_mem hnX)
      simpa [mul_assoc] using h1
    have hQ₂M : IsSylow2In (conjSub n Q₁) (conjSub n M) := hQ₁.conj n
    have hQ₂a : conjSub n Q₁ ≤ Subgroup.centralizer ({a} : Set G) := by
      intro q hq
      have h1 : a * q * a⁻¹ ∈ conjSub n Q₁ := (Subgroup.mem_normalizer_iff.mp haQ₂ q).mp hq
      have h2 : ⁅a, q⁆ ∈ conjSub n Q₁ := by
        rw [commutatorElement_def]
        exact (conjSub n Q₁).mul_mem h1 ((conjSub n Q₁).inv_mem hq)
      have h3 : ⁅a, q⁆ = 1 := eq_one_of_isPGroup_of_mem_odd hNodd (hc q (hQ₂X hq))
        (hQ₂M.2.1.to_le (Subgroup.zpowers_le.mpr h2))
      rw [commutatorElement_eq_one_iff_mul_comm] at h3
      exact Subgroup.mem_centralizer_singleton_iff.mpr h3.symm
    have hM₂ : conjSub n M ∈ Pm := hPmX M hM n hnX
    obtain ⟨z₂, hz₂⟩ := Sec6Gen.exists_uniqueInvolution hΩ.hyp (hPm hM₂)
    have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ.hyp (mem_RSet_of_isSylow2In (hPm hM₂) hQ₂M)
    have hz₂Q : z₂ ∈ conjSub n Q₁ := T3.mem_of_isPGroup hz₂ hQ₂M.1 hQ₂M.2.1 (by omega)
    have haM₂ : a ∈ Subgroup.normalizer (conjSub n M : Set G) :=
      hΩ.tight _ (hPm hM₂) z₂ hz₂ (Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (hQ₂a hz₂Q)).symm)
    have hXM : XMem Ω a (conjSub n M) := ⟨hPm hM₂, haM₂, conjSub n Q₁, hQ₂M,
      fun r hr => Subgroup.mem_centralizer_singleton_iff.mp (hQ₂a hr)⟩
    have hQ₂D : conjSub n Q₁ ≤ D :=
      (le_coreAt a hQ₂M.2.1 hQ₂M.1 hQ₂a).trans (le_iSup₂ (f := fun M (_ : M ∈ {M | M ∈ Pm ∧
        XMem Ω a M}) => coreAt a M) _ ⟨hM₂, hXM⟩)
    intro y hy
    have hy' : n * y * n⁻¹ ∈ conjSub n Q₁ := conj_mem_conjSub hy
    have e : y = n⁻¹ * (n * y * n⁻¹) * n := by group
    rw [e]
    exact (D ⊔ N).mul_mem ((D ⊔ N).mul_mem (le_sup_right (a := D) (N.inv_mem hn))
      (le_sup_left (a := D) (hQ₂D hy'))) (le_sup_right (a := D) hn)
  have hM : ∀ M ∈ Pm, M ≤ D ⊔ N := by
    intro M hM
    rw [← hgen M hM, Subgroup.closure_le]
    rintro y ⟨hyM, hy2⟩
    obtain ⟨Q₁, hQ₁, hyQ⟩ := IsSylow2In.exists_ge hy2 (Subgroup.zpowers_le.mpr hyM)
    exact key M hM Q₁ hQ₁ (hyQ (Subgroup.mem_zpowers y))
  exact hX.le.trans (iSup₂_le hM)

omit [Finite G] in
theorem nonempty_mulEquiv_of_surjective {D H : Type*} [Group D] [Group H] [Finite D]
    (f : D →* H) (hf : Function.Surjective f) (hk : Odd (Nat.card f.ker))
    (hH : classicalInvolutionOddCore H = ⊥) :
    Nonempty (H ≃* D ⧸ classicalInvolutionOddCore D) := by
  have hle : f.ker ≤ classicalInvolutionOddCore D :=
    CFSG.ComponentClassification.OddCore.maximal D f.ker inferInstance hk
  have hge : classicalInvolutionOddCore D ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hmap : (classicalInvolutionOddCore D).map f ≤ classicalInvolutionOddCore H :=
      CFSG.ComponentClassification.OddCore.maximal H _
        ((classicalInvolutionOddCore_normal D).map f hf)
        ((CFSG.ComponentClassification.OddCore.odd_card D).of_dvd_nat (Subgroup.card_map_dvd _ f))
    rw [hH] at hmap
    exact Subgroup.mem_bot.mp (hmap ⟨x, hx, rfl⟩)
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (le_antisymm hle hge))⟩

omit [Finite G] in
theorem isSimpleGroup_of_lieModel {t : Assembly.LowTwoRank.StatedLieTag}
    (ht : t = .PSL ∨ t = .PSU) (h : LieModel G t 3 3 1) : IsSimpleGroup G := by
  rcases ht with rfl | rfl <;> rcases h with ⟨-, h⟩ | h | h | h
  all_goals first
    | exact (LieType.Simplicity.fam_PSL_simplicity G 3 3 1 h).2
    | exact (ClassicalGroups.Unitary.fam_PSU_simplicity G 3 3 1 h).2
    | (rcases h with ⟨-, ht, -⟩; simp [chevalleyExceptionalTags, reeTitsTags] at ht)

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
