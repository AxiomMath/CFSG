module

import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open scoped commutatorElement

private lemma faith_comm {G : Type*} [Group G] {E : Subgroup G} {p : ℕ}
    (hE : IsElemAbelian p E) {a b : G} (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a :=
  CFSG.Open.IsElemAbelian.comm hE ha hb

private lemma faith_commute_of_commutator {G : Type*} [Group G] {T : Subgroup G} {z : G}
    (hT : IsElemAbelian 2 T) (hz3 : z ^ 3 = 1) (hzT : z ∈ normalizer (T : Set G))
    (hW : ∀ t ∈ T, z * ⁅t, z⁆ = ⁅t, z⁆ * z) {t : G} (ht : t ∈ T) : z * t = t * z := by
  have hconj : ∀ s ∈ T, z * s * z⁻¹ ∈ T := fun s hs => (mem_normalizer_iff.1 hzT s).1 hs
  obtain ⟨a, ha_def⟩ : ∃ a, a = z * t * z⁻¹ := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b, b = z * a * z⁻¹ := ⟨_, rfl⟩
  have ha : a ∈ T := ha_def ▸ hconj t ht
  have hb : b ∈ T := hb_def ▸ hconj a ha
  have hsq : ∀ s ∈ T, s⁻¹ = s := fun s hs =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hT.2 s hs)
  have h1 : a * b⁻¹ = t * a⁻¹ := by
    have e1 : a * b⁻¹ = z * ⁅t, z⁆ * z⁻¹ := by
      rw [commutatorElement_def, hb_def, ha_def]; group
    have e2 : t * a⁻¹ = ⁅t, z⁆ := by
      rw [commutatorElement_def, ha_def]; group
    rw [e1, e2, hW t ht]; group
  rw [hsq a ha, hsq b hb] at h1
  have h3 : b = t := mul_left_cancel (h1.trans (faith_comm hT ht ha))
  have hz3' : z * z * z = 1 := by rw [← pow_three']; exact hz3
  have h4 : z * t * z⁻¹ = t := by
    calc z * t * z⁻¹ = z * b * z⁻¹ := by rw [h3]
      _ = (z * z * z) * t * (z * z * z)⁻¹ := by rw [hb_def, ha_def]; group
      _ = t := by rw [hz3']; group
  exact mul_inv_eq_iff_eq_mul.1 h4

private lemma faith_normal_centralizer {G : Type*} [Group G] {Y W : Subgroup G}
    (hYW : Y ≤ normalizer (W : Set G)) :
    ((centralizer (W : Set G)).subgroupOf Y).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf, mem_centralizer_iff] at hn ⊢
  intro w hw
  have hg : (g : G)⁻¹ * w * (g : G) ∈ W := by
    have := (mem_normalizer_iff.1 (hYW (inv_mem g.2)) w).1 hw
    simpa using this
  have h := hn _ hg
  show w * ((g : G) * (n : G) * (g : G)⁻¹) = (g : G) * (n : G) * (g : G)⁻¹ * w
  calc w * ((g : G) * (n : G) * (g : G)⁻¹)
      = (g : G) * (((g : G)⁻¹ * w * (g : G)) * (n : G)) * (g : G)⁻¹ := by group
    _ = (g : G) * ((n : G) * ((g : G)⁻¹ * w * (g : G))) * (g : G)⁻¹ := by rw [h]
    _ = (g : G) * (n : G) * (g : G)⁻¹ * w := by group

private lemma faith_z_centralizes {G : Type*} [Group G] [Finite G] {Y W : Subgroup G} {z : G}
    (hY : IsPGroup 3 Y) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    (hcen : ∀ w ∈ Y, w ∈ centralizer (Y : Set G) → w ^ 3 = 1 → w ∈ zpowers z)
    (hYW : Y ≤ normalizer (W : Set G))
    (hy : ∃ y ∈ Y, y ≠ 1 ∧ y ∈ centralizer (W : Set G)) : z ∈ centralizer (W : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hyY, hy1, hyW⟩ := hy
  have hN : ((centralizer (W : Set G)).subgroupOf Y).Normal := faith_normal_centralizer hYW
  have : Group.IsNilpotent Y := hY.isNilpotent
  have hNbot : (centralizer (W : Set G)).subgroupOf Y ≠ ⊥ := by
    intro h
    have hmem : (⟨y, hyY⟩ : Y) ∈ (centralizer (W : Set G)).subgroupOf Y := hyW
    rw [h, Subgroup.mem_bot] at hmem
    exact hy1 (congrArg Subtype.val hmem)
  obtain ⟨M, hMdef⟩ : ∃ M : Subgroup Y,
      M = (centralizer (W : Set G)).subgroupOf Y ⊓ center Y := ⟨_, rfl⟩
  have hM : M ≠ ⊥ := hMdef ▸ Group.IsNilpotent.inf_center_ne_bot_of_normal hNbot
  have hMp : IsPGroup 3 M := hY.to_subgroup M
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hMp
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hn
    exact hM hn
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hn]; exact dvd_pow_self 3 hn0)
  have hxM : (x : Y) ∈ (centralizer (W : Set G)).subgroupOf Y ⊓ center Y := hMdef ▸ x.2
  have hx3 : ((x : Y) : G) ^ 3 = 1 := by
    have h : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have := congrArg (fun m : M => ((m : Y) : G)) h
    simpa using this
  have hx1 : ((x : Y) : G) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext (Subtype.ext h)
    rw [this, orderOf_one] at hx
    norm_num at hx
  have hxN : ((x : Y) : G) ∈ centralizer (W : Set G) := mem_subgroupOf.1 hxM.1
  have hxC : ((x : Y) : G) ∈ centralizer (Y : Set G) := by
    rw [mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hxM.2 ⟨g, hg⟩)
  have hxz : ((x : Y) : G) ∈ zpowers z := hcen _ (x : Y).2 hxC hx3
  have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hxord : orderOf ((x : Y) : G) = 3 := orderOf_eq_prime hx3 hx1
  have heq : zpowers ((x : Y) : G) = zpowers z := by
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hxz)
    rw [Nat.card_zpowers, Nat.card_zpowers, hzord, hxord]
  have hzx : z ∈ zpowers ((x : Y) : G) := heq ▸ mem_zpowers z
  exact (zpowers_le.2 hxN) hzx

private lemma faith_exists_injective_gl {W : Type*} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hW2 : ∀ w : W, w * w = 1) :
    ∃ k : ℕ, Nat.card W = 2 ^ k ∧
      ∃ κ : MulAut W →* GL (Fin k) (ZMod 2), Function.Injective κ := by
  classical
  let _ : CommGroup W := { (inferInstance : Group W) with mul_comm := hcomm }
  let _ : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    exact hW2 (Additive.toMul x)
  have : Fintype (Additive W) := Fintype.ofFinite _
  have hcard : Nat.card W = 2 ^ Module.finrank (ZMod 2) (Additive W) := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at h
    exact h
  refine ⟨Module.finrank (ZMod 2) (Additive W), hcard, ?_⟩
  let b : Module.Basis (Fin (Module.finrank (ZMod 2) (Additive W))) (ZMod 2) (Additive W) :=
    Module.finBasisOfFinrankEq _ _ rfl
  let f : MulAut W →* Module.End (ZMod 2) (Additive W) :=
    { toFun := fun σ => (MulEquiv.toAdditive σ).toAddMonoidHom.toZModLinearMap 2
      map_one' := by ext x; rfl
      map_mul' := fun σ τ => by ext x; rfl }
  let β : MulAut W →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive W) :=
    (Units.map f).comp (toUnits : MulAut W ≃* (MulAut W)ˣ).toMonoidHom
  have hβ : Function.Injective β := by
    intro σ τ h
    have h' := congrArg (fun u : LinearMap.GeneralLinearGroup (ZMod 2) (Additive W) =>
      (u : Module.End (ZMod 2) (Additive W))) h
    ext x
    exact LinearMap.congr_fun h' (Additive.ofMul x)
  let γ := (Matrix.GeneralLinearGroup.toLin' b).symm
  exact ⟨γ.toMonoidHom.comp β, γ.injective.comp hβ⟩

private lemma faith_exists_centralizing {G : Type*} [Group G] [Finite G] {Y W : Subgroup G}
    (hY : IsPGroup 3 Y) (hY27 : 27 ≤ Nat.card Y) (hW : IsElemAbelian 2 W)
    (hW16 : Nat.card W ≤ 16) (hYW : Y ≤ normalizer (W : Set G)) :
    ∃ y ∈ Y, y ≠ 1 ∧ y ∈ centralizer (W : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk, κ, hκ⟩ := faith_exists_injective_gl (W := W)
    (fun a b => Subtype.ext (faith_comm hW a.2 b.2))
    (fun w => Subtype.ext (by simpa [sq] using hW.2 w w.2))
  have hconj : ∀ (y : Y) (w : W), (y : G) * w * (y : G)⁻¹ ∈ W := fun y w =>
    (mem_normalizer_iff.1 (hYW y.2) w).1 w.2
  let ρ : Y →* MulAut W :=
    { toFun := fun y =>
        { toFun := fun w => ⟨(y : G) * w * (y : G)⁻¹, hconj y w⟩
          invFun := fun w => ⟨(y : G)⁻¹ * w * (y : G), by simpa using hconj y⁻¹ w⟩
          left_inv := fun w => Subtype.ext (by simp [mul_assoc])
          right_inv := fun w => Subtype.ext (by simp [mul_assoc])
          map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
      map_one' := MulEquiv.ext fun w => Subtype.ext (by simp)
      map_mul' := fun a b => MulEquiv.ext fun w => Subtype.ext (by simp [mul_assoc]) }
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    by_contra hy1
    refine hcon y y.2 (fun h => hy1 (Subtype.ext h)) ?_
    rw [mem_centralizer_iff]
    intro w hw
    have h := congrArg (fun σ : MulAut W => ((σ ⟨w, hw⟩ : W) : G)) hy
    have h' : (y : G) * w * (y : G)⁻¹ = w := h
    exact (mul_inv_eq_iff_eq_mul.1 h').symm
  have hdvd : Nat.card Y ∣ Nat.card (GL (Fin k) (ZMod 2)) :=
    Subgroup.card_dvd_of_injective (κ.comp ρ) (hκ.comp hρ)
  have hk4 : k ≤ 4 := by
    by_contra h
    have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h27 : 27 ∣ Nat.card Y := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hY
    have hm3 : 3 ≤ m := by
      by_contra h
      have : 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hm]
    exact (Nat.pow_dvd_pow 3 hm3 : 3 ^ 3 ∣ 3 ^ m)
  rw [Matrix.card_GL_field, ZMod.card] at hdvd
  have h := h27.trans hdvd
  interval_cases k <;> simp [Fin.prod_univ_succ] at h

theorem commutes_of_card_commutator_le {G : Type*} [Group G] [Finite G] {Y T₁ V : Subgroup G}
    {z : G} (hY : IsPGroup 3 Y) (hY27 : 27 ≤ Nat.card Y) (hzY : z ∈ Y) (hz1 : z ≠ 1)
    (hz3 : z ^ 3 = 1) (hzc : z ∈ centralizer (Y : Set G))
    (hcen : ∀ w ∈ Y, w ∈ centralizer (Y : Set G) → w ^ 3 = 1 → w ∈ zpowers z)
    (hT : IsElemAbelian 2 T₁) (hYT : Y ≤ normalizer (T₁ : Set G)) (hTV : T₁ ≤ V)
    (hV : Nat.card ↥⁅V, zpowers z⁆ ≤ 16) : ∀ t ∈ T₁, z * t = t * z := by
  classical
  have hzN : z ∈ normalizer (T₁ : Set G) := hYT hzY
  have hWT : ⁅T₁, zpowers z⁆ ≤ T₁ := by
    refine commutator_le.2 fun a ha g hg => ?_
    have h1 : g * a⁻¹ * g⁻¹ ∈ T₁ :=
      (mem_normalizer_iff.1 ((zpowers_le.2 hzN) hg) a⁻¹).1 (inv_mem ha)
    have h2 : ⁅a, g⁆ = a * (g * a⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
    rw [h2]
    exact mul_mem ha h1
  have hWe : IsElemAbelian 2 ⁅T₁, zpowers z⁆ :=
    ⟨⟨⟨fun a b => Subtype.ext (faith_comm hT (hWT a.2) (hWT b.2))⟩⟩,
      fun x hx => hT.2 x (hWT hx)⟩
  have hW16 : Nat.card ↥⁅T₁, zpowers z⁆ ≤ 16 :=
    (card_le_of_le (commutator_mono hTV le_rfl)).trans hV
  have hWY : ∀ y ∈ Y, ∀ h ∈ ⁅T₁, zpowers z⁆, y * h * y⁻¹ ∈ ⁅T₁, zpowers z⁆ := by
    intro y hy h hh
    have hle : ⁅T₁, zpowers z⁆ ≤ (⁅T₁, zpowers z⁆).comap (MulAut.conj y).toMonoidHom := by
      refine commutator_le.2 fun a ha g hg => ?_
      have hgc : g ∈ centralizer (Y : Set G) := (zpowers_le.2 hzc) hg
      have hyg : y * g * y⁻¹ = g :=
        mul_inv_eq_iff_eq_mul.2 (mem_centralizer_iff.1 hgc y hy)
      have hya : y * a * y⁻¹ ∈ T₁ := (mem_normalizer_iff.1 (hYT hy) a).1 ha
      have h2 : y * ⁅a, g⁆ * y⁻¹ = ⁅y * a * y⁻¹, y * g * y⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [hyg] at h2
      show y * ⁅a, g⁆ * y⁻¹ ∈ (⁅T₁, zpowers z⁆ : Subgroup G)
      rw [h2]
      exact commutator_mem_commutator hya hg
    exact hle hh
  have hYW : Y ≤ normalizer ((⁅T₁, zpowers z⁆ : Subgroup G) : Set G) := fun y hy =>
    mem_normalizer_iff.2 fun h => ⟨hWY y hy h, fun hh => by
      have h3 := hWY y⁻¹ (inv_mem hy) _ hh
      have h4 : y⁻¹ * (y * h * y⁻¹) * y⁻¹⁻¹ = h := by group
      rwa [h4] at h3⟩
  have hy := faith_exists_centralizing hY hY27 hWe hW16 hYW
  have hzW := faith_z_centralizes hY hz1 hz3 hcen hYW hy
  intro t ht
  refine faith_commute_of_commutator hT hz3 hzN (fun s hs => ?_) ht
  exact (mem_centralizer_iff.1 hzW _ (commutator_mem_commutator hs (mem_zpowers z))).symm

end CFSG.LocalAnalysis.RankThreeTheoremC
