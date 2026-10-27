module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Setting
public import CFSG.Open.FusionDefs

public section

namespace CFSG.EvenSporadicStandard.SolomonRed

open Subgroup CFSG.Open

variable {K : Type*} [Group K]

theorem odd_of_zstar_eq_bot (hZ : fusionZStar K = ⊥) {N : Subgroup K} (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have h1 : N ≤ fusionOddCore K := le_sSup ⟨hN, hodd⟩
  have h2 : fusionOddCore K ≤ fusionZStar K := by
    intro x hx
    show QuotientGroup.mk' (fusionOddCore K) x ∈ Subgroup.center _
    have h3 : QuotientGroup.mk' (fusionOddCore K) x = 1 := (QuotientGroup.eq_one_iff x).2 hx
    rw [h3]
    exact one_mem _
  rw [hZ] at h2
  exact le_bot_iff.1 (h1.trans h2)

theorem center_of_zstar_eq_bot (hZ : fusionZStar K = ⊥) (x : K) (hx : ∀ y, y * x = x * y) :
    x = 1 := by
  have h1 : x ∈ fusionZStar K := by
    show QuotientGroup.mk' (fusionOddCore K) x ∈ Subgroup.center _
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
    rw [← map_mul, ← map_mul, hx y]
  rw [hZ, mem_bot] at h1
  exact h1

theorem eq_one_of_central_of_simple {A : Type*} [Group A] [IsSimpleGroup A]
    (hnab : ∃ a b : A, a * b ≠ b * a) {c : A} (hc : ∀ a, a * c = c * a) : c = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center A) with h | h
  · have h1 : c ∈ Subgroup.center A := Subgroup.mem_center_iff.2 hc
    rw [h, mem_bot] at h1
    exact h1
  · obtain ⟨a, b, hab⟩ := hnab
    have h1 : b ∈ Subgroup.center A := by rw [h]; exact mem_top b
    exact absurd (Subgroup.mem_center_iff.1 h1 a) hab

theorem exists_noncommute_of_center_eq_bot {A : Type*} [Group A] [Nontrivial A]
    (h : Subgroup.center A = ⊥) : ∃ a b : A, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := exists_ne (1 : A)
  have h1 : x ∈ Subgroup.center A := Subgroup.mem_center_iff.2 fun g => hcon g x
  rw [h, mem_bot] at h1
  exact hx h1

theorem z2_eq_of_ne_one {g₁ g₂ : Multiplicative (ZMod 2)} (h₁ : g₁ ≠ 1) (h₂ : g₂ ≠ 1) :
    g₁ = g₂ := by
  revert g₁ g₂
  decide

variable {z : K} {A : Type*} [Group A]

@[expose] def embA (e : ↥(centralizer ({z} : Set K)) ≃* Multiplicative (ZMod 2) × A) : A →* K :=
  (centralizer ({z} : Set K)).subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inr _ _))

theorem embA_apply (e : ↥(centralizer ({z} : Set K)) ≃* Multiplicative (ZMod 2) × A) (a : A) :
    embA e a = (e.symm (1, a) : K) := rfl

theorem embA_injective (e : ↥(centralizer ({z} : Set K)) ≃* Multiplicative (ZMod 2) × A) :
    Function.Injective (embA e) := by
  intro a b h
  have h1 : e.symm (1, a) = e.symm (1, b) := Subtype.ext h
  exact congrArg Prod.snd (e.symm.injective h1)

theorem embA_mem_cent (e : ↥(centralizer ({z} : Set K)) ≃* Multiplicative (ZMod 2) × A) (a : A) :
    embA e a ∈ centralizer ({z} : Set K) := (e.symm (1, a)).2

theorem conj_embA (e : ↥(centralizer ({z} : Set K)) ≃* Multiplicative (ZMod 2) × A)
    (dd : ↥(centralizer ({z} : Set K))) (a : A) :
    (dd : K) * embA e a * (dd : K)⁻¹ = embA e ((e dd).2 * a * (e dd).2⁻¹) := by
  have key : dd * e.symm (1, a) * dd⁻¹ = e.symm (1, (e dd).2 * a * (e dd).2⁻¹) := by
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, map_inv]
    ext
    · show (e dd).1 * 1 * (e dd).1⁻¹ = 1
      rw [mul_one]
      exact mul_inv_cancel _
    · simp
  exact congrArg Subtype.val key

section Zz

variable [IsSimpleGroup A]

@[expose] def zz (z : K) : ↥(centralizer ({z} : Set K)) := ⟨z, mem_centralizer_singleton_iff.2 rfl⟩

theorem zz_comm (x : ↥(centralizer ({z} : Set K))) : x * zz z = zz z * x :=
  Subtype.ext (mem_centralizer_singleton_iff.1 x.2)

theorem zz_snd (hnab : ∃ a b : A, a * b ≠ b * a)
    (e : ↥(centralizer ({z} : Set K)) ≃* Multiplicative (ZMod 2) × A) : (e (zz z)).2 = 1 := by
  refine eq_one_of_central_of_simple hnab fun a => ?_
  have h1 := zz_comm (e.symm (1, a))
  have h2 := congrArg e h1
  simp only [map_mul, MulEquiv.apply_symm_apply] at h2
  exact congrArg Prod.snd h2

theorem zz_fst_ne (hnab : ∃ a b : A, a * b ≠ b * a) (hz : z ≠ 1)
    (e : ↥(centralizer ({z} : Set K)) ≃* Multiplicative (ZMod 2) × A) : (e (zz z)).1 ≠ 1 := by
  intro h1
  apply hz
  have h3 : e (zz z) = 1 := Prod.ext h1 (zz_snd hnab e)
  have h4 : zz z = 1 := e.injective (by rw [h3, map_one])
  exact congrArg Subtype.val h4

omit [IsSimpleGroup A] in
theorem mem_range_of_fst_eq_one (e : ↥(centralizer ({z} : Set K)) ≃* Multiplicative (ZMod 2) × A)
    {d : K} (hd : d ∈ centralizer ({z} : Set K)) (hg : (e ⟨d, hd⟩).1 = 1) :
    d ∈ (embA e).range := by
  refine ⟨(e ⟨d, hd⟩).2, ?_⟩
  rw [embA_apply]
  have h1 : e.symm (1, (e ⟨d, hd⟩).2) = ⟨d, hd⟩ := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact Prod.ext hg.symm rfl
  exact congrArg Subtype.val h1

theorem mem_range_or_mul (hnab : ∃ a b : A, a * b ≠ b * a) (hz : z ≠ 1)
    (e : ↥(centralizer ({z} : Set K)) ≃* Multiplicative (ZMod 2) × A)
    {d : K} (hd : d ∈ centralizer ({z} : Set K)) :
    d ∈ (embA e).range ∨ d * z ∈ (embA e).range := by
  by_cases hg : (e ⟨d, hd⟩).1 = 1
  · exact Or.inl (mem_range_of_fst_eq_one e hd hg)
  · right
    have hdz : d * z ∈ centralizer ({z} : Set K) :=
      mul_mem hd (mem_centralizer_singleton_iff.2 rfl)
    refine mem_range_of_fst_eq_one e hdz ?_
    have h1 : (⟨d * z, hdz⟩ : ↥(centralizer ({z} : Set K))) = ⟨d, hd⟩ * zz z := rfl
    rw [h1, map_mul]
    have h2 : (e (zz z)).1 = (e ⟨d, hd⟩).1 := (z2_eq_of_ne_one hg (zz_fst_ne hnab hz e)).symm
    show (e ⟨d, hd⟩).1 * (e (zz z)).1 = 1
    rw [h2]
    revert hg
    generalize (e ⟨d, hd⟩).1 = g
    intro _
    revert g
    decide

theorem setting_of_equiv [Finite K] (hnab : ∃ a b : A, a * b ≠ b * a)
    (hz : orderOf z = 2) (hZ : fusionZStar K = ⊥)
    (e : ↥(centralizer ({z} : Set K)) ≃* Multiplicative (ZMod 2) × A) :
    Setting K z (embA e).range := by
  have hz2 : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz, sq] at h
    exact h
  have hne : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz
    omega
  have hinj := embA_injective e
  refine ⟨hz2, hne, ?_, ?_, ?_, ?_, ?_, fun N hN hodd => odd_of_zstar_eq_bot hZ hN hodd,
    center_of_zstar_eq_bot hZ⟩
  · rintro _ ⟨a, rfl⟩
    exact embA_mem_cent e a
  · rintro d hd _ ⟨a, rfl⟩
    exact ⟨(e ⟨d, hd⟩).2 * a * (e ⟨d, hd⟩).2⁻¹, (conj_embA e ⟨d, hd⟩ a).symm⟩
  · exact (MonoidHom.ofInjective hinj).symm.isSimpleGroup
  · obtain ⟨a, b, hab⟩ := hnab
    refine ⟨embA e a, ⟨a, rfl⟩, embA e b, ⟨b, rfl⟩, fun h => hab ?_⟩
    apply hinj
    rw [map_mul, map_mul]
    exact h
  · intro d hd hcomm
    have hz1 := zz_snd hnab e
    have hz2' := zz_fst_ne hnab hne e
    set dd : ↥(centralizer ({z} : Set K)) := ⟨d, hd⟩ with hdd
    have hd1 : (e dd).2 = 1 := by
      refine eq_one_of_central_of_simple hnab fun a => ?_
      have h1 : d * embA e a = embA e a * d := hcomm _ ⟨a, rfl⟩
      have h2 : dd * e.symm (1, a) = e.symm (1, a) * dd := Subtype.ext h1
      have h3 := congrArg e h2
      simp only [map_mul, MulEquiv.apply_symm_apply] at h3
      exact (congrArg Prod.snd h3).symm
    rw [mem_zpowers_iff_of_mul_self_eq_one hz2]
    by_cases hg : (e dd).1 = 1
    · left
      have h3 : e dd = 1 := Prod.ext hg hd1
      have h4 : dd = 1 := e.injective (by rw [h3, map_one])
      exact congrArg Subtype.val h4
    · right
      have h3 : e dd = e (zz z) := Prod.ext (z2_eq_of_ne_one hg hz2') (by rw [hd1, hz1])
      exact congrArg Subtype.val (e.injective h3)

end Zz

end CFSG.EvenSporadicStandard.SolomonRed
