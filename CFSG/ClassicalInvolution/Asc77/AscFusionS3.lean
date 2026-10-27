module

public import CFSG.ClassicalInvolution.Asc77.AscFusionS2
public import CFSG.ClassicalInvolution.Asc77.AscFusionR12

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ComponentClassification
open scoped commutatorElement MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem perfect_inner_centralizing_false (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hK : IsClassicalMember p f K z) {R : Subgroup G}
    (hRN : R ≤ Subgroup.normalizer (K : Set G)) (hRperf : ⁅R, R⁆ = R)
    (hinner : ∀ x ∈ R, ∃ b ∈ K, ∀ y ∈ K, x * y * x⁻¹ * (b * y * b⁻¹)⁻¹ ∈ oddCoreOf K)
    {u : G} (huR : u ∈ R) (hucen : ∀ x ∈ R, x * u = u * x) {g : G} (hgK : g ∈ K)
    (hgact : ∀ y ∈ K, u * y * u⁻¹ * (g * y * g⁻¹)⁻¹ ∈ oddCoreOf K)
    (hg2 : ∀ y ∈ K, ⁅g * g, y⁆ ∈ oddCoreOf K)
    (hgnt : ¬ ∀ y ∈ K, ⁅g, y⁆ ∈ oddCoreOf K) : False := by
  classical
  obtain ⟨e⟩ := hK.nonempty_equiv
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField hp2 hq
  have hF2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card _ hodd
  set Θ : R →* MulAut SL(2, GaloisField p f) := actSL e R hRN with hΘ
  set G₀ : SL(2, GaloisField p f) := chartMap e ⟨g, hgK⟩ with hG₀
  have hΘu : Θ ⟨u, huR⟩ = MulAut.conj G₀ := actSL_eq_conj e R hRN huR hgK hgact
  have hG₀nc : G₀ ∉ Subgroup.center SL(2, GaloisField p f) := fun hc =>
    hgnt ((comm_mem_oddCoreOf_iff_central e hgK).mpr hc)
  have hG₀sq : G₀ * G₀ = -1 := by
    have hg2K : g * g ∈ K := K.mul_mem hgK hgK
    have hc : chartMap e ⟨g * g, hg2K⟩ ∈ Subgroup.center SL(2, GaloisField p f) :=
      (comm_mem_oddCoreOf_iff_central e hg2K).mp hg2
    have e1 : chartMap e ⟨g * g, hg2K⟩ = G₀ * G₀ := by
      rw [hG₀, ← map_mul]; rfl
    rw [e1, mem_center_sl2_iff] at hc
    rcases hc with h1 | h1
    · exfalso
      have hinv : G₀⁻¹ = G₀ := inv_eq_of_mul_eq_one_right h1
      rcases CFSG.Semidihedral.OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self _ hF2 _ hinv with
        h2 | h2
      · exact hG₀nc (by rw [h2]; exact Subgroup.one_mem _)
      · exact hG₀nc (by rw [h2]; exact (mem_center_sl2_iff _).mpr (Or.inr rfl))
    · exact h1
  have hrange : ∀ x : R, ∃ h ∈ signNormalizer G₀, Θ x = MulAut.conj h := by
    rintro ⟨x, hx⟩
    obtain ⟨b, hb, hbx⟩ := hinner x hx
    have hΘx : Θ ⟨x, hx⟩ = MulAut.conj (chartMap e ⟨b, hb⟩) := actSL_eq_conj e R hRN hx hb hbx
    refine ⟨chartMap e ⟨b, hb⟩, ?_, hΘx⟩
    set h := chartMap e ⟨b, hb⟩ with hh
    have hcomm : MulAut.conj h * MulAut.conj G₀ = MulAut.conj G₀ * MulAut.conj h := by
      rw [← hΘx, ← hΘu, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hucen x hx)
    have hcon : ∀ s : SL(2, GaloisField p f),
        (h * G₀) * s * (h * G₀)⁻¹ = (G₀ * h) * s * (G₀ * h)⁻¹ := by
      intro s
      have := congrArg (fun φ : MulAut SL(2, GaloisField p f) => φ s) hcomm
      simpa [MulAut.conj_apply, mul_assoc] using this
    have hcen : (G₀ * h)⁻¹ * (h * G₀) ∈ Subgroup.center SL(2, GaloisField p f) := by
      rw [Subgroup.mem_center_iff]
      intro s
      have h1 := hcon s
      calc s * ((G₀ * h)⁻¹ * (h * G₀)) = (G₀ * h)⁻¹ * ((G₀ * h) * s * (G₀ * h)⁻¹) * (h * G₀) := by
            group
        _ = (G₀ * h)⁻¹ * ((h * G₀) * s * (h * G₀)⁻¹) * (h * G₀) := by rw [h1]
        _ = ((G₀ * h)⁻¹ * (h * G₀)) * s := by group
    rw [mem_center_sl2_iff] at hcen
    rw [mem_signNormalizer_iff]
    rcases hcen with h1 | h1
    · left
      exact (inv_mul_eq_one.mp h1).symm
    · right
      have h2 : h * G₀ = (G₀ * h) * (-1) := inv_mul_eq_iff_eq_mul.mp h1
      rw [h2, ← sl2_neg_one_central (G₀ * h), mul_assoc]
  set ψ : ↥(signNormalizer G₀) →* MulAut SL(2, GaloisField p f) :=
    (MulAut.conj : SL(2, GaloisField p f) →* MulAut SL(2, GaloisField p f)).comp
      (signNormalizer G₀).subtype with hψ
  have hsolv : Group.IsSolvable ↥(signNormalizer G₀) :=
    sl2_isSolvable_of_commute_pm hF2 G₀ hG₀sq _ (fun h hh => hh)
  have hsolvψ : Group.IsSolvable ↥ψ.range :=
    Group.isSolvable_of_surjective ψ.rangeRestrict_surjective
  have hle : Θ.range ≤ ψ.range := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨h, hh, hx⟩ := hrange x
    exact ⟨⟨h, hh⟩, by simp [hψ, hx]⟩
  have hsolvΘ : Group.IsSolvable ↥Θ.range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have hperfR : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.mpr hRperf
  have hperfΘ : Group.IsPerfect ↥Θ.range :=
    Group.IsPerfect.ofSurjective (f := Θ.rangeRestrict) Θ.rangeRestrict_surjective
  have hsub : Subsingleton ↥Θ.range := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable ↥Θ.range hsolvΘ
  have hΘ1 : Θ ⟨u, huR⟩ = 1 := by
    have : (⟨Θ ⟨u, huR⟩, ⟨_, rfl⟩⟩ : ↥Θ.range) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val this
  apply hG₀nc
  rw [Subgroup.mem_center_iff]
  intro s
  have h1 := congrArg (fun φ : MulAut SL(2, GaloisField p f) => φ s) (hΘu.symm.trans hΘ1)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc s * G₀ = (G₀ * s * G₀⁻¹) * G₀ := by rw [h1]
    _ = G₀ * s := by group

theorem inner_action_false (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K₀ : Subgroup G} {z₀ : G}
    (h₀ : IsClassicalMember p f K₀ z₀) {A B : Subgroup G} {a b : G}
    (hA : A ∈ CoreAssembly.conjClass K₀) (hB : B ∈ CoreAssembly.conjClass K₀)
    (hAa : IsUniqueInvolution A a) (hBb : IsUniqueInvolution B b) (hab : a * b = b * a)
    (haB : a ∈ Subgroup.normalizer (B : Set G)) (hT : ∀ y ∈ B, ⁅a, y⁆ ∈ oddCoreOf B)
    {g : G} (hgA : g ∈ A)
    (hgact : ∀ y ∈ A, b * y * b⁻¹ * (g * y * g⁻¹)⁻¹ ∈ oddCoreOf A)
    (hg2 : ∀ y ∈ A, ⁅g * g, y⁆ ∈ oddCoreOf A)
    (hgnt : ¬ ∀ y ∈ A, ⁅g, y⁆ ∈ oddCoreOf A) : False := by
  classical
  have hAmem : IsClassicalMember p f A a := isClassicalMember_of_mem_conjClass hp2 hq h₀ hA hAa
  have hBmem : IsClassicalMember p f B b := isClassicalMember_of_mem_conjClass hp2 hq h₀ hB hBb
  obtain ⟨J₀, hJ₀B, hJ₀fix, hJ₀perf, hJ₀qs, hJ₀sub, hJ₀2⟩ :=
    exists_trivial_action_lift hq hBmem haB hAa.sq hT
  have hbB : b ∈ B := hBb.mem
  have hbJ₀ : b ∈ J₀ := by
    refine hJ₀2 b hbB ?_ (isPGroup_zpowers_of_mul_self_eq_one hBb.sq hBb.ne_one)
    calc a * b * a⁻¹ = (b * a) * a⁻¹ := by rw [hab]
      _ = b := by group
  have hbcomm : ∀ y ∈ B, b * y = y * b := fun y hy => hBb.commute_of_mem hy
  have hlayer := trivialCore_le_twoLayer hBb.sq hBb.ne_one hbcomm hab.symm
    (subnormal_subgroupOf_member hBmem) hJ₀B hJ₀fix hJ₀perf hJ₀qs hJ₀sub
  set Y : Subgroup G := Subgroup.centralizer ({a} : Set G) with hY
  have hAY : A ≤ Y := isSubnormal_le hAmem.subnormal
  have hAcomp : TwoComponents.IsTwoComponent (A.subgroupOf Y) :=
    isTwoComponent_subgroupOf_of_perfect hAmem.subnormal hAmem.perfect.commutator_eq_top
      (isQuasisimple_oddQuot hq hAmem)
  have hJ₀Y : ∀ x ∈ J₀, x ∈ Y := by
    intro x hx
    rw [hY, Subgroup.mem_centralizer_singleton_iff]
    have h1 := hJ₀fix x hx
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hact : ∀ x ∈ J₀, x ∈ Subgroup.normalizer (A : Set G) ∧
      ∃ c ∈ A, ∀ y ∈ A, x * y * x⁻¹ * (c * y * c⁻¹)⁻¹ ∈ oddCoreOf A := fun x hx =>
    layer_acts_inner_sub hAY hAcomp (hJ₀Y x hx) (hlayer (show (⟨x, hJ₀Y x hx⟩ : ↥Y) ∈
      J₀.subgroupOf Y from hx))
  exact perfect_inner_centralizing_false hp2 hq hAmem (fun x hx => (hact x hx).1) hJ₀perf
    (fun x hx => (hact x hx).2) hbJ₀ (fun x hx => (hbcomm x (hJ₀B hx)).symm) hgA hgact hg2 hgnt

end CFSG.ClassicalInvolution.Asc77.AscFusion
