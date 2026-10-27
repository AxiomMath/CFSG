module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseACloseBasic
public import CFSG.LocalAnalysis.OddStandard.Seitz77U
public import CFSG.LocalAnalysis.OddStandard.Seitz77UElem

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

section Split

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {F : Type} [Field F]
  [Finite F] [CharP F 2] {W S₁ S₀ W₀ : Subgroup G} {ι : G → F × F} {κ : G → F}
  {φ : G → RingAut F} (S : SylowA d W S₁ S₀ W₀ ι κ φ)

include S

namespace SylowA

omit [Finite G] in
theorem κ_one : κ 1 = 0 := (S.κ_eq_zero_iff 1 S₀.one_mem).2 W.one_mem

omit [Finite G] in
theorem κ_inv {s : G} (hs : s ∈ S₀) : κ s⁻¹ = -κ s := by
  have h := S.κ_add s hs s⁻¹ (S₀.inv_mem hs)
  rw [mul_inv_cancel, S.κ_one] at h
  linear_combination -h

theorem exists_yh {W' : Subgroup G} (hW'S₀ : W' ≤ S₀) (hW'ab : IsElemAbelian 2 W')
    (hκW' : ∀ b : F, ∃ w ∈ W', κ w = b) :
    ∃ (Y : Subgroup G) (yh : F → G), Y ≤ W' ∧ (∀ b, yh b ∈ Y) ∧ (∀ b, κ (yh b) = b) ∧
      ∀ b b', yh b * yh b' = yh (b + b') := by
  obtain ⟨Y, hYW', hYK, hdec⟩ := exists_complement_of_elem (K := W ⊓ W') (W' := W')
    (fun x hx y hy => comm_of_isElemAbelian_two hW'ab hx hy)
    (fun x hx => mul_self_of_isElemAbelian_two hW'ab hx)
  have hinj : ∀ y ∈ Y, ∀ y' ∈ Y, κ y = κ y' → y = y' := by
    intro y hy y' hy' h
    have hyS : y ∈ S₀ := hW'S₀ (hYW' hy)
    have hy'S : y' ∈ S₀ := hW'S₀ (hYW' hy')
    have h1 : κ (y * y'⁻¹) = 0 := by
      rw [S.κ_add y hyS y'⁻¹ (S₀.inv_mem hy'S), S.κ_inv hy'S, h, add_neg_cancel]
    have hmem : y * y'⁻¹ ∈ W := (S.κ_eq_zero_iff _ (S₀.mul_mem hyS (S₀.inv_mem hy'S))).1 h1
    have hmemY : y * y'⁻¹ ∈ Y := Y.mul_mem hy (Y.inv_mem hy')
    have h2 : y * y'⁻¹ ∈ Y ⊓ (W ⊓ W') := ⟨hmemY, hmem, hYW' hmemY⟩
    rw [hYK, Subgroup.mem_bot, mul_inv_eq_one] at h2
    exact h2
  have hsurj : ∀ b : F, ∃ y ∈ Y, κ y = b := by
    intro b
    obtain ⟨w, hwW', hwκ⟩ := hκW' b
    obtain ⟨z, hz, y, hy, rfl⟩ := hdec w hwW'
    refine ⟨y, hy, ?_⟩
    have hzS : z ∈ S₀ := hW'S₀ hz.2
    have hyS : y ∈ S₀ := hW'S₀ (hYW' hy)
    have hκz : κ z = 0 := (S.κ_eq_zero_iff z hzS).2 hz.1
    rw [S.κ_add z hzS y hyS, hκz, zero_add] at hwκ
    exact hwκ
  choose yh hyY hyκ using hsurj
  refine ⟨Y, yh, hYW', hyY, hyκ, fun b b' => hinj _ (Y.mul_mem (hyY b) (hyY b')) _ (hyY _) ?_⟩
  rw [S.κ_add _ (hW'S₀ (hYW' (hyY b))) _ (hW'S₀ (hYW' (hyY b'))), hyκ, hyκ, hyκ]

omit [Finite G] in
theorem wh_mul {wh : F × F → G} (hwW : ∀ p, wh p ∈ W) (hwι : ∀ p, ι (wh p) = p) (p q : F × F) :
    wh p * wh q = wh (p + q) :=
  S.ι_inj _ (W.mul_mem (hwW p) (hwW q)) _ (hwW _) (by
    rw [S.ι_add _ (hwW p) _ (hwW q), hwι, hwι, hwι])

omit [Finite G] in
theorem yh_mul_wh {yh : F → G} (hyS : ∀ b, yh b ∈ S₀) (hyκ : ∀ b, κ (yh b) = b)
    {wh : F × F → G} (hwW : ∀ p, wh p ∈ W) (hwι : ∀ p, ι (wh p) = p) (b x a : F) :
    yh b * wh (x, a) * (yh b)⁻¹ = wh (x + b * a, a) := by
  apply S.ι_inj _ (S.normal_W (S.S₀_le_S₁ (hyS b)) (hwW _)) _ (hwW _)
  rw [S.conj_ι _ (hyS b) _ (hwW _), hyκ, hwι, hwι]

omit [Finite G] in
theorem split_mul {yh : F → G} (hyS : ∀ b, yh b ∈ S₀) (hyκ : ∀ b, κ (yh b) = b)
    (hyadd : ∀ b b', yh b * yh b' = yh (b + b')) {wh : F × F → G} (hwW : ∀ p, wh p ∈ W)
    (hwι : ∀ p, ι (wh p) = p) {f : ↥(unipAll F) → G}
    (hf : ∀ g, f g = wh (coordC g - coordA g * coordB g, coordA g) * yh (coordB g))
    (g g' : ↥(unipAll F)) : f (g * g') = f g * f g' := by
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  obtain ⟨a', b', c', rfl⟩ := exists_uelt g'
  simp only [hf, uelt_mul, coordA_uelt, coordB_uelt, coordC_uelt]
  have h2 := S.yh_mul_wh hyS hyκ hwW hwι b (c' - a' * b') a'
  have h3 : yh b * wh (c' - a' * b', a') = wh (c' - a' * b' + b * a', a') * yh b := by
    rw [← h2, inv_mul_cancel_right]
  have e : ((c - a * b, a) : F × F) + (c' - a' * b' + b * a', a') =
      (c + c' + a * b' - (a + a') * (b + b'), a + a') :=
    Prod.ext (by
      simp only [Prod.fst_add]
      linear_combination (a' * b) * (CharTwo.two_eq_zero : (2 : F) = 0)) rfl
  calc wh (c + c' + a * b' - (a + a') * (b + b'), a + a') * yh (b + b')
      = wh ((c - a * b, a) + (c' - a' * b' + b * a', a')) * yh (b + b') := by rw [e]
    _ = wh (c - a * b, a) * wh (c' - a' * b' + b * a', a') * (yh b * yh b') := by
        rw [← S.wh_mul hwW hwι, hyadd]
    _ = wh (c - a * b, a) * (yh b * wh (c' - a' * b', a')) * yh b' := by
        rw [h3]; simp only [mul_assoc]
    _ = wh (c - a * b, a) * yh b * (wh (c' - a' * b', a') * yh b') := by simp only [mul_assoc]

omit [Finite G] in
theorem κ_wh_mul_yh {yh : F → G} (hyS : ∀ b, yh b ∈ S₀) (hyκ : ∀ b, κ (yh b) = b)
    {wh : F × F → G} (hwW : ∀ p, wh p ∈ W) (p : F × F) (b : F) : κ (wh p * yh b) = b := by
  have hS : wh p ∈ S₀ := S.W_le_S₀ (hwW p)
  rw [S.κ_add _ hS _ (hyS b), (S.κ_eq_zero_iff _ hS).2 (hwW p), hyκ, zero_add]

omit [Finite G] in
theorem eq_of_wh_mul_yh {yh : F → G} (hyS : ∀ b, yh b ∈ S₀) (hyκ : ∀ b, κ (yh b) = b)
    {wh : F × F → G} (hwW : ∀ p, wh p ∈ W) (hwι : ∀ p, ι (wh p) = p) {p p' : F × F} {b b' : F}
    (h : wh p * yh b = wh p' * yh b') : p = p' ∧ b = b' := by
  have hb : b = b' := by
    rw [← S.κ_wh_mul_yh hyS hyκ hwW p b, h, S.κ_wh_mul_yh hyS hyκ hwW p' b']
  subst hb
  refine ⟨?_, rfl⟩
  rw [← hwι p, mul_right_cancel h, hwι]

omit [Finite G] in
theorem wh_mul_yh_mem_iff {W' Y : Subgroup G} (hinf : W ⊓ W' = W₀) (hYW' : Y ≤ W')
    {yh : F → G} (hyY : ∀ b, yh b ∈ Y) {wh : F × F → G} (hwW : ∀ p, wh p ∈ W)
    (hwι : ∀ p, ι (wh p) = p) (p : F × F) (b : F) : wh p * yh b ∈ W' ↔ p.2 = 0 := by
  constructor
  · intro h
    have h1 : wh p ∈ W' := by
      have := W'.mul_mem h (W'.inv_mem (hYW' (hyY b)))
      rwa [mul_inv_cancel_right] at this
    have h2 : wh p ∈ W₀ := by rw [← hinf]; exact ⟨hwW p, h1⟩
    have h3 := (S.mem_W₀_iff.1 h2).2
    rwa [hwι] at h3
  · intro h
    have h1 : wh p ∈ W₀ := S.mem_W₀_iff.2 ⟨hwW p, by rw [hwι]; exact h⟩
    have h2 : wh p ∈ W ⊓ W' := by rw [hinf]; exact h1
    exact W'.mul_mem h2.2 (hYW' (hyY b))

theorem exists_equiv_unip_of_sections {W' Y : Subgroup G} (hW'S₀ : W' ≤ S₀)
    (hinf : W ⊓ W' = W₀) (hYW' : Y ≤ W') {yh : F → G} (hyY : ∀ b, yh b ∈ Y)
    (hyκ : ∀ b, κ (yh b) = b) (hyadd : ∀ b b', yh b * yh b' = yh (b + b'))
    {wh : F × F → G} (hwW : ∀ p, wh p ∈ W) (hwι : ∀ p, ι (wh p) = p) :
    ∃ e : ↥S₀ ≃* ↥(unipAll F), (∀ s : S₀, coordB (e s) = κ s) ∧
      (∀ s : S₀, (s : G) ∈ W ↔ e s ∈ radOne F) ∧ (∀ s : S₀, (s : G) ∈ W' ↔ e s ∈ radTwo F) := by
  have hyS : ∀ b, yh b ∈ S₀ := fun b => hW'S₀ (hYW' (hyY b))
  obtain ⟨f, hf⟩ : ∃ f : ↥(unipAll F) → G, ∀ g,
      f g = wh (coordC g - coordA g * coordB g, coordA g) * yh (coordB g) := ⟨_, fun _ => rfl⟩
  have hmem : ∀ g, f g ∈ S₀ := fun g => by
    rw [hf]
    exact S₀.mul_mem (S.W_le_S₀ (hwW _)) (hyS _)
  have hκ : ∀ g, κ (f g) = coordB g := fun g => by
    rw [hf]
    exact S.κ_wh_mul_yh hyS hyκ hwW _ _
  have hinj : Function.Injective f := by
    intro g g' h
    rw [hf, hf] at h
    obtain ⟨hp, hb⟩ := S.eq_of_wh_mul_yh hyS hyκ hwW hwι h
    have hA : coordA g = coordA g' := congrArg Prod.snd hp
    have hC := congrArg Prod.fst hp
    simp only at hC
    rw [hA, hb] at hC
    calc g = uelt (coordA g) (coordB g) (coordC g) := (uelt_coords g).symm
      _ = uelt (coordA g') (coordB g') (coordC g') := by rw [hA, hb, sub_left_inj.1 hC]
      _ = g' := uelt_coords g'
  let f' : ↥(unipAll F) →* ↥S₀ :=
    MonoidHom.mk' (fun g => ⟨f g, hmem g⟩)
      (fun g g' => Subtype.ext (S.split_mul hyS hyκ hyadd hwW hwι hf g g'))
  have hf'inj : Function.Injective f' := fun g g' h => hinj (congrArg Subtype.val h)
  have hbij : Function.Bijective f' :=
    hf'inj.bijective_of_nat_card_le (by rw [S.card_S₀, card_unipAll, S.card_F]; norm_num)
  obtain ⟨e, he⟩ : ∃ e : ↥S₀ ≃* ↥(unipAll F), ∀ s, f (e s) = (s : G) := by
    refine ⟨(MulEquiv.ofBijective f' hbij).symm, fun s => ?_⟩
    have h := (MulEquiv.ofBijective f' hbij).apply_symm_apply s
    rw [MulEquiv.ofBijective_apply] at h
    exact congrArg Subtype.val h
  have hB : ∀ s : S₀, coordB (e s) = κ s := fun s => by rw [← hκ, he]
  refine ⟨e, hB, fun s => ?_, fun s => ?_⟩
  · rw [mem_radOne, hB, S.κ_eq_zero_iff _ s.2]
  · rw [mem_radTwo, ← he s, hf, S.wh_mul_yh_mem_iff hinf hYW' hyY hwW hwι]

theorem exists_equiv_unip_of_split {W' : Subgroup G} (hW'S₀ : W' ≤ S₀)
    (hW'ab : IsElemAbelian 2 W') (hinf : W ⊓ W' = W₀) (hκW' : ∀ b : F, ∃ w ∈ W', κ w = b) :
    ∃ e : ↥S₀ ≃* ↥(unipAll F), (∀ s : S₀, coordB (e s) = κ s) ∧
      (∀ s : S₀, (s : G) ∈ W ↔ e s ∈ radOne F) ∧ (∀ s : S₀, (s : G) ∈ W' ↔ e s ∈ radTwo F) := by
  obtain ⟨Y, yh, hYW', hyY, hyκ, hyadd⟩ := S.exists_yh hW'S₀ hW'ab hκW'
  obtain ⟨wh, hwW, hwι⟩ : ∃ wh : F × F → G, (∀ p, wh p ∈ W) ∧ ∀ p, ι (wh p) = p := by
    choose wh hwW hwι using S.ι_surj
    exact ⟨wh, hwW, hwι⟩
  exact S.exists_equiv_unip_of_sections hW'S₀ hinf hYW' hyY hyκ hyadd hwW hwι

end SylowA

end Split

end CFSG.OddStandard.Seitz77
