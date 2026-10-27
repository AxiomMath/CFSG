module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieGamma
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieSL2Facts
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieDefs

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.Open CFSG.ComponentClassification.AS76b CFSG.ClassicalInvolution
open scoped MatrixGroups commutatorElement

variable {H : Type*} [Group H] {F : Type*} [Field F]

variable {B T X : Subgroup H}

theorem le_normalizer_inf {J X : Subgroup H} (hJX : J ≤ normalizer (X : Set H)) :
    J ≤ normalizer ((J ⊓ X : Subgroup H) : Set H) := by
  intro j hj
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨hyJ, hyX⟩ := Subgroup.mem_inf.mp hy
    exact Subgroup.mem_inf.mpr ⟨J.mul_mem (J.mul_mem hj hyJ) (J.inv_mem hj),
      (mem_normalizer_iff.mp (hJX hj) y).mp hyX⟩
  · intro hy
    obtain ⟨hyJ, hyX⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨?_, (mem_normalizer_iff.mp (hJX hj) y).mpr hyX⟩
    have := J.mul_mem (J.mul_mem (J.inv_mem hj) hyJ) hj
    simpa [mul_assoc] using this

theorem Hyp46.le_centralizer_of_le_normalizer [Finite H] [Finite F] (h : Hyp46 B T X)
    {J : Subgroup H}
    (e : J ≃* SL(2, F)) (hF : Odd (Nat.card F)) (hTJ : T ≤ normalizer (J : Set H))
    (hJX : J ≤ normalizer (X : Set H)) : T ≤ centralizer (J : Set H) := by
  have hN : J ⊓ X ≤ centralizer (J : Set H) :=
    le_centralizer_of_isTwoNilpotent e hF inf_le_left (le_normalizer_inf hJX)
      (h.twoNilpotent.mono inf_le_right) fun x hx k hxk =>
        h.sq_eq_one (Subgroup.mem_inf.mp hx).2 k hxk
  intro τ hτ
  refine mem_centralizer_of_commutator_mem e hF (hTJ hτ) fun x hx => hN ?_
  refine Subgroup.mem_inf.mpr ⟨J.mul_mem ((mem_normalizer_iff.mp (hTJ hτ) x).mp hx)
    (J.inv_mem hx), ?_⟩
  have e1 : τ * x * τ⁻¹ * x⁻¹ = τ * (x * τ⁻¹ * x⁻¹) := by group
  rw [e1]
  exact X.mul_mem (h.le_X hτ) ((mem_normalizer_iff.mp (hJX hx) τ⁻¹).mp (X.inv_mem (h.le_X hτ)))

theorem Hyp46.le_centralizer_of_inf_ne_bot [Finite H] [Finite F] (h : Hyp46 B T X) {J : Subgroup H}
    (e : J ≃* SL(2, F)) (hF : Odd (Nat.card F)) (hJB : J ≤ B) (hTJ : T ≤ normalizer (J : Set H))
    (hC : T ⊓ centralizer (J : Set H) ≠ ⊥) : T ≤ centralizer (J : Set H) := by
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hC
  have ht1' : t ≠ 1 := fun h1 => ht1 (Subtype.ext h1)
  obtain ⟨htT, htC⟩ := Subgroup.mem_inf.mp ht
  refine h.le_centralizer_of_le_normalizer e hF hTJ fun j hj =>
    h.inf_centralizer_le_of_mem htT ht1' (Subgroup.mem_inf.mpr ⟨mem_sup_right (hJB hj), ?_⟩)
  rw [mem_centralizer_singleton_iff]
  exact (mem_centralizer_iff.mp htC) j hj


theorem conj_mem_conjSubgroup {g x : H} {J : Subgroup H} (hx : x ∈ J) :
    MulAut.conj g x ∈ conjSubgroup g J := Subgroup.mem_map_of_mem _ hx

theorem mem_centralizer_singleton_of_conj {t y : H} (h : MulAut.conj t y = y) :
    y ∈ centralizer ({t} : Set H) := by
  rw [mem_centralizer_singleton_iff]
  rw [MulAut.conj_apply] at h
  calc y * t = t * y * t⁻¹ * t := by rw [h]
    _ = t * y := by group

theorem conj_conj_of_sq {t : H} (ht : t ^ 2 = 1) (x : H) :
    MulAut.conj t (MulAut.conj t x) = x := by
  rw [← MulAut.mul_apply, ← map_mul, ← sq, ht, map_one, MulAut.one_apply]

theorem conj_mem_of_mem_normalizer {t x : H} {B : Subgroup H} (ht : t ∈ normalizer (B : Set H))
    (hx : x ∈ B) : MulAut.conj t x ∈ B := (mem_normalizer_iff.mp ht x).mp hx

theorem Hyp46.le_normalizer_of_free [Finite H] [Finite F] (h : Hyp46 B T X) {J : Subgroup H}
    (e : J ≃* SL(2, F)) (hF : Odd (Nat.card F)) (hJB : J ≤ B) {u v : H} (hu : u ∈ T)
    (hv : v ∈ T) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv1 : u * v ≠ 1)
    (c1 : ∀ a ∈ J, ∀ b ∈ J, a * MulAut.conj u b = MulAut.conj u b * a)
    (c2 : ∀ a ∈ J, ∀ b ∈ J, a * MulAut.conj (u * v) b = MulAut.conj (u * v) b * a)
    (c3 : ∀ a ∈ J, ∀ b ∈ J,
      MulAut.conj u a * MulAut.conj (u * v) b = MulAut.conj (u * v) b * MulAut.conj u a) :
    J ≤ normalizer (X : Set H) := by
  have hT2 : ∀ t ∈ T, t ^ 2 = 1 := fun t ht => h.elem.2 t ht
  have hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have huvT : u * v ∈ T := T.mul_mem hu hv
  have hB : ∀ t ∈ T, ∀ x ∈ J, MulAut.conj t x ∈ T ⊔ B := fun t ht x hx =>
    mem_sup_right (conj_mem_of_mem_normalizer (h.le_normalizer ht) (hJB hx))
  have hsq : ∀ x ∈ J, x ^ 2 ∈ normalizer (X : Set H) := by
    intro x hx
    set xu := MulAut.conj u x
    set xuv := MulAut.conj (u * v) x
    have ha1 : x * xu ∈ normalizer (X : Set H) := by
      refine h.inf_centralizer_le_of_mem hu hu1 (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      · exact mul_mem (mem_sup_right (hJB hx)) (hB u hu x hx)
      · refine mem_centralizer_singleton_of_conj ?_
        rw [map_mul, conj_conj_of_sq (hT2 u hu)]
        exact (c1 x hx x hx).symm
    have ha2 : xu⁻¹ * xuv⁻¹ ∈ normalizer (X : Set H) := by
      refine h.inf_centralizer_le_of_mem hv hv1 (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      · exact mul_mem (inv_mem (hB u hu x hx)) (inv_mem (hB _ huvT x hx))
      · refine mem_centralizer_singleton_of_conj ?_
        have e1 : MulAut.conj v xu = xuv := by
          rw [← MulAut.mul_apply, ← map_mul, hcomm v hv u hu]
        have e2 : MulAut.conj v xuv = xu := by
          rw [← MulAut.mul_apply, ← map_mul, ← mul_assoc, hcomm v hv u hu, mul_assoc, ← sq,
            hT2 v hv, mul_one]
        rw [map_mul, map_inv, map_inv, e1, e2, ← mul_inv_rev, ← mul_inv_rev, c3 x hx x hx]
    have ha3 : xuv * x ∈ normalizer (X : Set H) := by
      refine h.inf_centralizer_le_of_mem huvT huv1 (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      · exact mul_mem (hB _ huvT x hx) (mem_sup_right (hJB hx))
      · refine mem_centralizer_singleton_of_conj ?_
        rw [map_mul, conj_conj_of_sq (hT2 _ huvT)]
        exact (c2 x hx x hx)
    have hprod : x ^ 2 = (x * xu) * (xu⁻¹ * xuv⁻¹) * (xuv * x) := by rw [sq]; group
    rw [hprod]
    exact mul_mem (mul_mem ha1 ha2) ha3
  refine le_of_forall_odd_mem e hF fun x hx hodd => ?_
  obtain ⟨m, hm⟩ := hodd
  have hxe : x = (x ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [hxe]
  exact pow_mem (hsq x hx) _

theorem le_normalizer_closure {J : Subgroup H} {S : Set H}
    (h : ∀ j ∈ J, ∀ s ∈ S, j * s * j⁻¹ ∈ closure S) : J ≤ normalizer (closure S : Set H) := by
  have key : ∀ j ∈ J, ∀ x ∈ closure S, j * x * j⁻¹ ∈ closure S := by
    intro j hj x hx
    refine closure_induction (p := fun x _ => j * x * j⁻¹ ∈ closure S) (fun s hs => h j hj s hs)
      ?_ ?_ ?_ hx
    · simp [one_mem]
    · intro a b _ _ ha hb
      have e : j * (a * b) * j⁻¹ = (j * a * j⁻¹) * (j * b * j⁻¹) := by group
      rw [e]
      exact mul_mem ha hb
    · intro a _ ha
      have e : j * a⁻¹ * j⁻¹ = (j * a * j⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem ha
  intro j hj
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key j hj x, fun hx => ?_⟩
  have := key j⁻¹ (inv_mem hj) _ hx
  simpa [mul_assoc] using this

theorem commutator_mem_of_commute {X : Subgroup H} {u a b : H} (hu : u ∈ X)
    (ha : a ∈ normalizer (X : Set H)) (hb : b ∈ normalizer (X : Set H))
    (hc : a * MulAut.conj u b⁻¹ = MulAut.conj u b⁻¹ * a) : ⁅a, b⁆ ∈ X := by
  rw [MulAut.conj_apply] at hc
  set c := u * b⁻¹ * u⁻¹ with hcdef
  have hw : b * c ∈ X := by
    have e : b * c = b * u * b⁻¹ * u⁻¹ := by rw [hcdef]; group
    rw [e]
    exact X.mul_mem ((mem_normalizer_iff.mp hb u).mp hu) (X.inv_mem hu)
  have h1 : a * (b * c) * a⁻¹ ∈ X := (mem_normalizer_iff.mp ha _).mp hw
  have hc' : c * a⁻¹ = a⁻¹ * c := by
    calc c * a⁻¹ = a⁻¹ * (a * c) * a⁻¹ := by group
      _ = a⁻¹ * (c * a) * a⁻¹ := by rw [hc]
      _ = a⁻¹ * c := by group
  have key : ⁅a, b⁆ = (a * (b * c) * a⁻¹) * (b * c)⁻¹ := by
    have e : a * (b * c) * a⁻¹ * (b * c)⁻¹ = a * b * (c * a⁻¹) * c⁻¹ * b⁻¹ := by group
    rw [e, hc', commutatorElement_def]
    group
  rw [key]
  exact X.mul_mem h1 (X.inv_mem hw)

theorem Hyp46.false_of_le_normalizer_of_commute [Finite H] [Finite F] (h : Hyp46 B T X)
    {J : Subgroup H}
    (e : J ≃* SL(2, F)) (hF : Odd (Nat.card F)) {u : H} (hu : u ∈ T)
    (c1 : ∀ a ∈ J, ∀ b ∈ J, a * MulAut.conj u b = MulAut.conj u b * a)
    (hJX : J ≤ normalizer (X : Set H)) : False := by
  have hN : J ⊓ X ≤ centralizer (J : Set H) :=
    le_centralizer_of_isTwoNilpotent e hF inf_le_left (le_normalizer_inf hJX)
      (h.twoNilpotent.mono inf_le_right) fun x hx k hxk =>
        h.sq_eq_one (Subgroup.mem_inf.mp hx).2 k hxk
  obtain ⟨a, ha, b, hb, hab⟩ := exists_commutator_not_mem_centralizer e
  refine hab (hN (Subgroup.mem_inf.mpr ⟨?_, ?_⟩))
  · rw [commutatorElement_def]
    exact J.mul_mem (J.mul_mem (J.mul_mem ha hb) (J.inv_mem ha)) (J.inv_mem hb)
  · exact commutator_mem_of_commute (h.le_X hu) (hJX ha) (hJX hb) (c1 a ha _ (J.inv_mem hb))

theorem Hyp46.le_normalizer_of_fixed [Finite H] [Finite F] (h : Hyp46 B T X) {J : Subgroup H}
    (e : J ≃* SL(2, F)) (hF : Odd (Nat.card F)) (hJB : J ≤ B) {u w : H} (hu : u ∈ T)
    (hw : w ∈ T) (hu1 : u ≠ 1) (hw1 : w ≠ 1) (huw1 : u * w ≠ 1)
    (hwJ : conjSubgroup w J = J)
    (c1 : ∀ a ∈ J, ∀ b ∈ J, a * MulAut.conj u b = MulAut.conj u b * a) :
    J ≤ normalizer (X : Set H) := by
  have hT2 : ∀ t ∈ T, t ^ 2 = 1 := fun t ht => h.elem.2 t ht
  have huwT : u * w ∈ T := T.mul_mem hu hw
  have hB : ∀ t ∈ T, ∀ x ∈ J, MulAut.conj t x ∈ T ⊔ B := fun t ht x hx =>
    mem_sup_right (conj_mem_of_mem_normalizer (h.le_normalizer ht) (hJB hx))
  have hwx : ∀ x ∈ J, MulAut.conj w x ∈ J := fun x hx => hwJ ▸ conj_mem_conjSubgroup hx
  have hwN : w ∈ normalizer (J : Set H) := by
    rw [mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hwx x hx, fun hx => ?_⟩
    have h1 : w * x * w⁻¹ ∈ conjSubgroup w J := hwJ.symm ▸ hx
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = x := by
      have := hyx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      exact mul_left_cancel (mul_right_cancel this)
    rw [← this]
    exact hy
  have hc : ∀ x ∈ J, MulAut.conj w x * x⁻¹ ∈ normalizer (X : Set H) := by
    intro x hx
    set y := MulAut.conj w x with hydef
    have hy : y ∈ J := hwx x hx
    have hb1 : y * MulAut.conj u y ∈ normalizer (X : Set H) := by
      refine h.inf_centralizer_le_of_mem hu hu1 (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      · exact mul_mem (mem_sup_right (hJB hy)) (hB u hu y hy)
      · refine mem_centralizer_singleton_of_conj ?_
        rw [map_mul, conj_conj_of_sq (hT2 u hu)]
        exact (c1 y hy y hy).symm
    have hσ : MulAut.conj (u * w) x = MulAut.conj u y := by
      rw [hydef, ← MulAut.mul_apply, ← map_mul]
    have hb2 : x * MulAut.conj (u * w) x ∈ normalizer (X : Set H) := by
      refine h.inf_centralizer_le_of_mem huwT huw1 (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      · exact mul_mem (mem_sup_right (hJB hx)) (hB _ huwT x hx)
      · refine mem_centralizer_singleton_of_conj ?_
        rw [map_mul, conj_conj_of_sq (hT2 _ huwT), hσ]
        exact (c1 x hx y hy).symm
    have e1 : y * x⁻¹ = (y * MulAut.conj u y) * (x * MulAut.conj (u * w) x)⁻¹ := by
      rw [hσ]; group
    rw [e1]
    exact mul_mem hb1 (inv_mem hb2)
  by_cases hcen : ∀ x ∈ J, w * x * w⁻¹ * x⁻¹ ∈ centralizer (J : Set H)
  · have hwC := mem_centralizer_of_commutator_mem e hF hwN hcen
    intro x hx
    refine h.inf_centralizer_le_of_mem hw hw1 (Subgroup.mem_inf.mpr
      ⟨mem_sup_right (hJB hx), ?_⟩)
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp hwC) x hx
  · push Not at hcen
    obtain ⟨x₀, hx₀, hnot⟩ := hcen
    set S : Set H := {y | ∃ x ∈ J, y = MulAut.conj w x * x⁻¹} with hS
    have hSJ : ∀ y ∈ S, y ∈ J := by
      rintro y ⟨x, hx, rfl⟩
      exact J.mul_mem (hwx x hx) (J.inv_mem hx)
    have hN₁J : closure S ≤ J := (Subgroup.closure_le _).mpr hSJ
    have hN₁X : closure S ≤ normalizer (X : Set H) :=
      (Subgroup.closure_le _).mpr fun y ⟨x, hx, hy⟩ =>
      hy ▸ hc x hx
    have hJN₁ : J ≤ normalizer (closure S : Set H) := by
      refine le_normalizer_closure fun j hj y ⟨x, hx, hy⟩ => ?_
      have e1 : j * y * j⁻¹ = (MulAut.conj w j * j⁻¹)⁻¹ *
          (MulAut.conj w (j * x) * (j * x)⁻¹) := by
        rw [hy]; simp only [map_mul, MulAut.conj_apply]; group
      rw [e1]
      exact mul_mem (inv_mem (subset_closure ⟨j, hj, rfl⟩))
        (subset_closure ⟨j * x, J.mul_mem hj hx, rfl⟩)
    set S₂ : Set H := {y | ∃ a ∈ closure S, ∃ b ∈ closure S, y = ⁅a, b⁆} with hS₂
    have hK₀X : closure S₂ ≤ X := (Subgroup.closure_le _).mpr fun y ⟨a, ha, b, hb, hy⟩ => hy ▸
      commutator_mem_of_commute (h.le_X hu) (hN₁X ha) (hN₁X hb)
        (c1 a (hN₁J ha) _ (J.inv_mem (hN₁J hb)))
    have hK₀J : closure S₂ ≤ J := (Subgroup.closure_le _).mpr fun y ⟨a, ha, b, hb, hy⟩ => by
      rw [hy, commutatorElement_def]
      exact J.mul_mem (J.mul_mem (J.mul_mem (hN₁J ha) (hN₁J hb)) (J.inv_mem (hN₁J ha)))
        (J.inv_mem (hN₁J hb))
    have hJK₀ : J ≤ normalizer (closure S₂ : Set H) := by
      refine le_normalizer_closure fun j hj y ⟨a, ha, b, hb, hy⟩ => subset_closure ?_
      refine ⟨j * a * j⁻¹, (mem_normalizer_iff.mp (hJN₁ hj) a).mp ha,
        j * b * j⁻¹, (mem_normalizer_iff.mp (hJN₁ hj) b).mp hb, ?_⟩
      rw [hy, commutatorElement_def, commutatorElement_def]
      group
    have hK₀C : closure S₂ ≤ centralizer (J : Set H) :=
      le_centralizer_of_isTwoNilpotent e hF hK₀J hJK₀ (h.twoNilpotent.mono hK₀X)
        fun x hx k hxk => h.sq_eq_one (hK₀X hx) k hxk
    by_cases hab : ∀ a ∈ closure S, ∀ b ∈ closure S, a * b = b * a
    · exfalso
      have hcent := le_centralizer_of_abelian e hF hN₁J hJN₁ hab
      exact hnot (hcent (subset_closure ⟨x₀, hx₀, by rw [MulAut.conj_apply]⟩))
    · push Not at hab
      obtain ⟨a, ha, b, hb, hab'⟩ := hab
      have hk : ⁅a, b⁆ ∈ closure S₂ := subset_closure ⟨a, ha, b, hb, rfl⟩
      have hk1 : ⁅a, b⁆ ≠ 1 := fun h1 => hab' (commutatorElement_eq_one_iff_mul_comm.mp h1)
      rcases eq_one_or_centralInv_of_mem_centralizer e (hK₀J hk) (hK₀C hk) with h1 | hz
      · exact absurd h1 hk1
      · have hzX : centralInv e ∈ X := hz ▸ hK₀X hk
        intro x hx
        refine h.inf_centralizer_le hzX (centralInv_ne_one e hF) 1 (by simpa using centralInv_sq e)
          (Subgroup.mem_inf.mpr ⟨mem_sup_right (hJB hx), ?_⟩)
        rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_iff.mp (centralInv_mem_centralizer e)) x hx

theorem Hyp46.false_of_moved [Finite H] [Finite F] (h : Hyp46 B T X) {J : Subgroup H}
    (e : J ≃* SL(2, F))
    (hF : Odd (Nat.card F)) (hJB : J ≤ B)
    (hcomm : ∀ t ∈ T, conjSubgroup t J = J ∨
      ∀ a ∈ J, ∀ b ∈ conjSubgroup t J, a * b = b * a)
    {u : H} (huT : u ∈ T) (hu : conjSubgroup u J ≠ J) : False := by
  have hT2 : ∀ t ∈ T, t ^ 2 = 1 := fun t ht => h.elem.2 t ht
  have hc : ∀ t ∈ T, conjSubgroup t J ≠ J →
      ∀ a ∈ J, ∀ b ∈ J, a * MulAut.conj t b = MulAut.conj t b * a := by
    intro t ht hne a ha b hb
    rcases hcomm t ht with h' | h'
    · exact absurd h' hne
    · exact h' a ha _ (conj_mem_conjSubgroup hb)
  have c1 := hc u huT hu
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply hu
    ext x
    simp only [conjSubgroup, map_one, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
      MulAut.one_apply, exists_eq_right]
  obtain ⟨v, hvT, hv1, hvu⟩ : ∃ v ∈ T, v ≠ 1 ∧ v ≠ u := by
    by_contra hcon
    push Not at hcon
    have hle : T ≤ zpowers u := fun t ht => by
      by_cases ht1 : t = 1
      · rw [ht1]; exact one_mem _
      · rw [hcon t ht ht1]; exact mem_zpowers u
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf u ≤ 2 := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one (hT2 u huT))
    have := h.four_le
    omega
  have huv1 : u * v ≠ 1 := by
    intro h1
    apply hvu
    have h2 : v = u⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2, inv_eq_of_mul_eq_one_left (by rw [← sq, hT2 u huT])]
  have huvT : u * v ∈ T := T.mul_mem huT hvT
  have hJX : J ≤ normalizer (X : Set H) := by
    by_cases hcase : conjSubgroup v J = J ∨ conjSubgroup (u * v) J = J
    · obtain ⟨w, hwT, hw1, huw1, hwJ⟩ :
          ∃ w ∈ T, w ≠ 1 ∧ u * w ≠ 1 ∧ conjSubgroup w J = J := by
        rcases hcase with hvJ | huvJ
        · exact ⟨v, hvT, hv1, huv1, hvJ⟩
        · refine ⟨u * v, huvT, huv1, ?_, huvJ⟩
          rw [← mul_assoc, ← sq, hT2 u huT, one_mul]
          exact hv1
      exact h.le_normalizer_of_fixed e hF hJB huT hwT hu1 hw1 huw1 hwJ c1
    · push Not at hcase
      obtain ⟨hvJ, huvJ⟩ := hcase
      have c2 := hc (u * v) huvT huvJ
      have c3 : ∀ a ∈ J, ∀ b ∈ J, MulAut.conj u a * MulAut.conj (u * v) b =
          MulAut.conj (u * v) b * MulAut.conj u a := by
        intro a ha b hb
        have h1 := congrArg (MulAut.conj u) (hc v hvT hvJ a ha b hb)
        rwa [map_mul, map_mul, ← MulAut.mul_apply, ← map_mul] at h1
      exact h.le_normalizer_of_free e hF hJB huT hvT hu1 hv1 huv1 c1 c2 c3
  exact h.false_of_le_normalizer_of_commute e hF huT c1 hJX

end CFSG.ComponentClassification.RankTwoOddLie
