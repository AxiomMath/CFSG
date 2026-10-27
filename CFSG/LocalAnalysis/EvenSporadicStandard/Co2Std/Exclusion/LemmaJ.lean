module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.XConcrete
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.XBasic
public import CFSG.GroupTheory.SwappedFactorsOffenders

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem subtype_toXW_apply (W : Subgroup G) (n : ↥(normalizer (W : Set G))) (w : ↥W) :
    ((((((XW W).subtype) (toXW W n)) w : ↥W)) : G) = (n : G) * (w : G) * (n : G)⁻¹ := by
  rw [show ((XW W).subtype (toXW W n) : MulAut ↥W) = (toXW W n : MulAut ↥W) from rfl]
  exact coe_toXW_apply W n w

variable {z : G} {W₁ W₂ : Subgroup G}

private theorem conj_mul_self (hz2 : z * z = 1) :
    (MulAut.conj z : MulAut G) * MulAut.conj z = 1 := by
  rw [← map_mul, hz2, map_one]

private theorem map_conj_swap (hzw : ∀ w ∈ W₁, z * w * z⁻¹ ∈ W₂) (hz2 : z * z = 1)
    (hcard₁ : Nat.card W₁ = 2 ^ 10) (hcard₂ : Nat.card W₂ = 2 ^ 10) :
    W₁.map (MulAut.conj z).toMonoidHom = W₂ ∧ W₂.map (MulAut.conj z).toMonoidHom = W₁ := by
  have h₁ : W₁.map (MulAut.conj z).toMonoidHom = W₂ := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨w, hw, rfl⟩
      simpa [MulAut.conj_apply] using hzw w hw
    · rw [Subgroup.card_map_of_injective (MulAut.conj z).injective, hcard₁, hcard₂]
  have hinvol : ∀ u : G,
      (MulAut.conj z).toMonoidHom ((MulAut.conj z).toMonoidHom u) = u := by
    intro u
    show (MulAut.conj z) ((MulAut.conj z) u) = u
    have := congrArg (fun f : MulAut G => f u) (conj_mul_self hz2)
    simpa using this
  constructor
  · exact h₁
  · apply Subgroup.eq_of_le_of_card_ge
    · rintro x ⟨w, hw, rfl⟩
      have hw' : w ∈ W₁.map (MulAut.conj z).toMonoidHom := by rw [h₁]; exact hw
      obtain ⟨u, hu, rfl⟩ := hw'
      rw [hinvol u]
      exact hu
    · rw [Subgroup.card_map_of_injective (MulAut.conj z).injective, hcard₂, hcard₁]

private noncomputable def conjEquiv (hzw : ∀ w ∈ W₁, z * w * z⁻¹ ∈ W₂) (hz2 : z * z = 1)
    (hcard₁ : Nat.card W₁ = 2 ^ 10) (hcard₂ : Nat.card W₂ = 2 ^ 10) :
    ↥W₂ ≃* ↥W₁ :=
  (Subgroup.equivMapOfInjective W₂ (MulAut.conj z).toMonoidHom
    (show Function.Injective (MulAut.conj z).toMonoidHom from (MulAut.conj z).injective)).trans
    (MulEquiv.subgroupCongr (map_conj_swap hzw hz2 hcard₁ hcard₂).2)

private theorem conjEquiv_apply (hzw : ∀ w ∈ W₁, z * w * z⁻¹ ∈ W₂) (hz2 : z * z = 1)
    (hcard₁ : Nat.card W₁ = 2 ^ 10) (hcard₂ : Nat.card W₂ = 2 ^ 10) (w : ↥W₂) :
    (((conjEquiv hzw hz2 hcard₁ hcard₂) w : ↥W₁) : G) = z * (w : G) * z⁻¹ := by
  rw [conjEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    Subgroup.coe_equivMapOfInjective_apply]
  rfl

private theorem conjEquiv_symm_apply {hzw : ∀ w ∈ W₁, z * w * z⁻¹ ∈ W₂} {hz2 : z * z = 1}
    {hcard₁ : Nat.card W₁ = 2 ^ 10} {hcard₂ : Nat.card W₂ = 2 ^ 10} (x : ↥W₁) :
    (((conjEquiv hzw hz2 hcard₁ hcard₂).symm x : ↥W₂) : G) = z⁻¹ * (x : G) * z := by
  have h := conjEquiv_apply hzw hz2 hcard₁ hcard₂
    ((conjEquiv hzw hz2 hcard₁ hcard₂).symm x)
  simp only [MulEquiv.apply_symm_apply] at h
  rw [h]
  group

variable {Y Ws : Subgroup G} {Qs : Subgroup (MulAut ↥Ws)} {t : ↥Ws}

private theorem card_bound_of_module (ψ : ↥Y →* MulAut ↥Ws)
    (hψ : ∀ (y : ↥Y) (w : ↥Ws), ((ψ y) w : G) = (y : G) * (w : G) * (y : G)⁻¹)
    (hmod : ModuleFacts Qs t) (hrange : ψ.range ≤ Qs)
    (hY : IsElementaryAbelian 2 ↥Y)
    (hne : ¬ Y ≤ centralizer (Ws : Set G)) :
    (centralizer (Ws : Set G)).relIndex Y *
      Nat.card ↥(Ws ⊓ centralizer (Y : Set G)) < 2 ^ 10 := by
  classical
  let C : Subgroup G := centralizer (Ws : Set G)
  have hker : ψ.ker = C.subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hy w hw
      have h := congrArg (fun z : ↥Ws => (z : G))
        (congrArg (fun f : MulAut ↥Ws => f ⟨w, hw⟩) hy)
      have h' : (y : G) * w * (y : G)⁻¹ = w := by
        simpa [hψ y ⟨w, hw⟩] using h
      calc w * (y : G) = ((y : G) * w * (y : G)⁻¹) * (y : G) := by rw [h']
        _ = (y : G) * w := by group
    · intro hc
      ext w
      rw [hψ y w]
      show (y : G) * (w : G) * (y : G)⁻¹ = (w : G)
      rw [← hc w w.2]
      group
  have hcard_range : Nat.card ψ.range = C.relIndex Y := by
    rw [← Subgroup.index_ker ψ, hker]
    rfl
  let f : {a : ↥Ws // ∀ y' ∈ ψ.range, y' a = a} → ↥(Ws ⊓ centralizer (Y : Set G)) :=
    fun a => ⟨(a.1 : G), a.1.2, by
      change (a.1 : G) ∈ Subgroup.centralizer (Y : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hmem : ψ ⟨y, hy⟩ ∈ ψ.range := MonoidHom.mem_range.mpr ⟨⟨y, hy⟩, rfl⟩
      have hfix : ψ ⟨y, hy⟩ a.1 = a.1 := a.2 (ψ ⟨y, hy⟩) hmem
      have hval : (y : G) * (a.1 : G) * (y : G)⁻¹ = (a.1 : G) := by
        have := congrArg (fun z : ↥Ws => (z : G)) hfix
        rwa [hψ ⟨y, hy⟩ a.1] at this
      calc (y : G) * (a.1 : G) =
          ((y : G) * (a.1 : G) * (y : G)⁻¹) * (y : G) := by group
        _ = (a.1 : G) * (y : G) := by rw [hval]⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(Ws ⊓ centralizer (Y : Set G)) => (z : G)) hab
  have hf_surj : Function.Surjective f := by
    intro w
    refine ⟨⟨⟨(w.1 : G), w.2.1⟩, ?_⟩, ?_⟩
    · intro y' hy'
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hy'
      apply Subtype.ext
      rw [hψ y ⟨(w.1 : G), w.2.1⟩]
      have hc : (y : G) * (w.1 : G) = (w.1 : G) * (y : G) :=
        Subgroup.mem_centralizer_iff.mp w.2.2 (y : G) y.2
      rw [hc]
      group
    · apply Subtype.ext
      rfl
  have hfixEquiv : {a : ↥Ws // ∀ y' ∈ ψ.range, y' a = a} ≃
      ↥(Ws ⊓ centralizer (Y : Set G)) := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hne_range : ψ.range ≠ ⊥ := by
    intro hbot
    apply hne
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hmem : ψ ⟨y, hy⟩ ∈ ψ.range := MonoidHom.mem_range.mpr ⟨⟨y, hy⟩, rfl⟩
    rw [hbot] at hmem
    have hone : ψ ⟨y, hy⟩ = 1 := Subgroup.mem_bot.mp hmem
    have h := congrArg (fun z : ↥Ws => (z : G))
      (congrArg (fun g : MulAut ↥Ws => g ⟨w, hw⟩) hone)
    have h' : (y : G) * w * (y : G)⁻¹ = w := by
      simpa [hψ ⟨y, hy⟩ ⟨w, hw⟩] using h
    calc w * (y : G) = ((y : G) * w * (y : G)⁻¹) * (y : G) := by rw [h']
      _ = (y : G) * w := by group
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsElementaryAbelian 2 (⊤ : Subgroup ↥Y) :=
    hY.of_mulEquiv (Subgroup.topEquiv).symm
  have hrange_ea : IsElementaryAbelian 2 ψ.range := by
    rw [MonoidHom.range_eq_map]
    exact IsElementaryAbelian.map (p := 2) (A := (⊤ : Subgroup ↥Y)) ψ
  have hno := hmod.noOffenders ψ.range hrange hrange_ea hne_range
  rw [hcard_range, Nat.card_congr hfixEquiv] at hno
  exact hno

variable {L A T : Subgroup G} {z t : G} {W W₁ W₂ : Subgroup G}
  {Q : Subgroup ↥(XW W)} {Q₁ : Subgroup (MulAut ↥(W₁.subgroupOf W))}
  {t₁ : ↥(W₁.subgroupOf W)}

private theorem hoff₁ (h : WHyp G L A T z t W W₁ W₂)
    (hx : XHyp (XW W).subtype Q (W₁.subgroupOf W) (W₂.subgroupOf W)
      (toXW W ⟨z, h.z_mem_normalizer⟩) Q₁ t₁)
    {S Y : Subgroup G} (hYS : Y ≤ S) (hSN : S ≤ normalizer (W : Set G))
    (hgood : ∀ (s : G) (hs : s ∈ S),
      XGood (XW W).subtype Q (W₁.subgroupOf W) (W₂.subgroupOf W) (toXW W ⟨s, hSN hs⟩))
    (hY : IsElementaryAbelian 2 ↥Y)
    (hYnorm₁ : ∀ y ∈ Y, ∀ w ∈ W₁, y * w * y⁻¹ ∈ W₁)
    (hnotC : ¬ Y ≤ centralizer (W₁ : Set G)) :
    (centralizer (W₁ : Set G)).relIndex Y *
      Nat.card ↥(W₁ ⊓ centralizer (Y : Set G)) < 2 ^ 10 := by
  classical
  have hW₁le : W₁ ≤ W := by rw [← h.sup_eq]; exact le_sup_left
  have hW₂le : W₂ ≤ W := by rw [← h.sup_eq]; exact le_sup_right
  have hYN : Y ≤ normalizer (W₁ : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      exact hYnorm₁ y hy w hw
    · intro hw
      have h := hYnorm₁ y⁻¹ (Y.inv_mem hy) (y * w * y⁻¹) hw
      have h' : y⁻¹ * (y * w * y⁻¹) * (y⁻¹)⁻¹ = w := by group
      rwa [h'] at h
  let ψ : ↥Y →* MulAut ↥W₁ := W₁.normalizerMonoidHom.comp (Subgroup.inclusion hYN)
  have hψ : ∀ (y : ↥Y) (w : ↥W₁),
      ((ψ y) w : G) = (y : G) * (w : G) * (y : G)⁻¹ := by
    intro y w
    show ((W₁.normalizerMonoidHom (Subgroup.inclusion hYN y) w : ↥W₁) : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hfirst : ∀ y : ↥Y, ∃ q ∈ Q, ∀ v ∈ W₁.subgroupOf W,
      (XW W).subtype (toXW W ⟨(y : G), hSN (hYS y.2)⟩) v = (XW W).subtype q v := by
    intro y
    rcases hgood (y : G) (hYS y.2) with ⟨h1, _⟩ | ⟨hswap1, _⟩
    · exact h1
    · exfalso
      have hW₁ne : W₁ ≠ ⊥ := by
        intro hbot
        have hcard := h.w.card₁
        rw [hbot, Subgroup.card_bot] at hcard
        norm_num at hcard
      obtain ⟨w, hw, hw1⟩ := (Subgroup.bot_or_exists_ne_one W₁).resolve_left hW₁ne
      have hmem₁ : y * w * y⁻¹ ∈ W₁ := hYnorm₁ y y.2 w hw
      let v : ↥(W₁.subgroupOf W) := ⟨⟨w, hW₁le hw⟩, hw⟩
      have hmem₂' := hswap1 (v : ↥W) v.2
      have hmem₂ : y * w * y⁻¹ ∈ W₂ := by
        have := hmem₂'
        rw [Subgroup.mem_subgroupOf] at this
        simp only [Subgroup.coe_subtype] at this
        rw [coe_toXW_apply] at this
        simpa [v] using this
      have hbot : y * w * y⁻¹ = 1 := by
        have hmem : y * w * y⁻¹ ∈ W₁ ⊓ W₂ := ⟨hmem₁, hmem₂⟩
        rw [h.w.inf_eq_bot] at hmem
        exact Subgroup.mem_bot.mp hmem
      have hw' : w = 1 := by
        have h1 : y * w = y := by
          have := congrArg (fun x : G => x * (y : G)) hbot
          simpa [mul_assoc] using this
        have h1' : (y : G) * w = (y : G) * 1 := by simpa using h1
        exact mul_left_cancel h1'
      exact hw1 hw'
  let e₁ : ↥(W₁.subgroupOf W) ≃* ↥W₁ := Subgroup.subgroupOfEquivOfLe hW₁le
  let Q₁W : Subgroup (MulAut ↥W₁) := Q₁.map (MulAut.congr e₁).toMonoidHom
  have hmod : ModuleFacts Q₁W (e₁ t₁) := hx.module.map_mulEquiv e₁
  have hrange : ψ.range ≤ Q₁W := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨q, hq, hqval⟩ := hfirst y
    have heq : ψ y = MulAut.congr e₁ (hx.resEquiv ⟨q, hq⟩) := by
      ext w
      have hψy : ((ψ y) w : G) = (y : G) * (w : G) * (y : G)⁻¹ := hψ y w
      rw [hψy]
      have hqv := hqval (e₁.symm w) (e₁.symm w).2
      have hcoe : ((((XW W).subtype (toXW W ⟨(y : G), hSN (hYS y.2)⟩)) (e₁.symm w) :
          ↥W) : G) = (y : G) * (w : G) * (y : G)⁻¹ := by
        have hsub : ((XW W).subtype (toXW W ⟨(y : G), hSN (hYS y.2)⟩) : MulAut ↥W) =
            ((toXW W ⟨(y : G), hSN (hYS y.2)⟩ : ↥(XW W)) : MulAut ↥W) := rfl
        rw [hsub, coe_toXW_apply]
        simp [e₁, Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe]
      calc (y : G) * (w : G) * (y : G)⁻¹
          = ((((XW W).subtype (toXW W ⟨(y : G), hSN (hYS y.2)⟩)) (e₁.symm w) :
              ↥W) : G) := hcoe.symm
        _ = ((((XW W).subtype q) (e₁.symm w) : ↥W) : G) := by rw [hqv]
        _ = (((((hx.resEquiv ⟨q, hq⟩ : MulAut ↥(W₁.subgroupOf W)) (e₁.symm w)) :
              ↥(W₁.subgroupOf W)) : ↥W) : G) := by
              rw [hx.resEquiv_apply]
        _ = ((e₁ ((hx.resEquiv ⟨q, hq⟩ : MulAut ↥(W₁.subgroupOf W)) (e₁.symm w)) :
              ↥W₁) : G) := by
              simp [e₁, Subgroup.subgroupOfEquivOfLe_apply_coe]
        _ = (((MulAut.congr e₁ (hx.resEquiv ⟨q, hq⟩)) w : ↥W₁) : G) := by
              rfl
    rw [heq]
    exact Subgroup.mem_map_of_mem (MulAut.congr e₁).toMonoidHom (hx.resEquiv ⟨q, hq⟩).2
  exact card_bound_of_module ψ hψ hmod hrange hY hnotC

private theorem hoff₂ (h : WHyp G L A T z t W W₁ W₂)
    (hx : XHyp (XW W).subtype Q (W₁.subgroupOf W) (W₂.subgroupOf W)
      (toXW W ⟨z, h.z_mem_normalizer⟩) Q₁ t₁)
    {S Y : Subgroup G} (hYS : Y ≤ S) (hSN : S ≤ normalizer (W : Set G))
    (hgood : ∀ (s : G) (hs : s ∈ S),
      XGood (XW W).subtype Q (W₁.subgroupOf W) (W₂.subgroupOf W) (toXW W ⟨s, hSN hs⟩))
    (hY : IsElementaryAbelian 2 ↥Y)
    (hYnorm₁ : ∀ y ∈ Y, ∀ w ∈ W₁, y * w * y⁻¹ ∈ W₁)
    (hYnorm₂ : ∀ y ∈ Y, ∀ w ∈ W₂, y * w * y⁻¹ ∈ W₂)
    (hnotC : ¬ Y ≤ centralizer (W₂ : Set G)) :
    (centralizer (W₂ : Set G)).relIndex Y *
      Nat.card ↥(W₂ ⊓ centralizer (Y : Set G)) < 2 ^ 10 := by
  classical
  have hW₁le : W₁ ≤ W := by rw [← h.sup_eq]; exact le_sup_left
  have hW₂le : W₂ ≤ W := by rw [← h.sup_eq]; exact le_sup_right
  have hYN₂ : Y ≤ normalizer (W₂ : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      exact hYnorm₂ y hy w hw
    · intro hw
      have h := hYnorm₂ y⁻¹ (Y.inv_mem hy) (y * w * y⁻¹) hw
      have h' : y⁻¹ * (y * w * y⁻¹) * (y⁻¹)⁻¹ = w := by group
      rwa [h'] at h
  let ψ : ↥Y →* MulAut ↥W₂ := W₂.normalizerMonoidHom.comp (Subgroup.inclusion hYN₂)
  have hψ : ∀ (y : ↥Y) (w : ↥W₂),
      ((ψ y) w : G) = (y : G) * (w : G) * (y : G)⁻¹ := by
    intro y w
    show ((W₂.normalizerMonoidHom (Subgroup.inclusion hYN₂ y) w : ↥W₂) : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  let e₂ : ↥W₂ ≃* ↥W₁ := conjEquiv h.w.swap h.hyp.z_sq h.w.card₁ h.w.card₂
  have he₂ : ∀ w : ↥W₂, (e₂ w : G) = z * (w : G) * z⁻¹ :=
    fun w => conjEquiv_apply h.w.swap h.hyp.z_sq h.w.card₁ h.w.card₂ w
  have he₂symm : ∀ x : ↥W₁, (e₂.symm x : G) = z⁻¹ * (x : G) * z :=
    fun x => conjEquiv_symm_apply x
  have hfirst : ∀ y : ↥Y, ∃ q ∈ Q, ∀ v ∈ W₂.subgroupOf W,
      (XW W).subtype (toXW W ⟨(y : G), hSN (hYS y.2)⟩) v = (XW W).subtype q v := by
    intro y
    rcases hgood (y : G) (hYS y.2) with ⟨_, h2⟩ | ⟨_, hswap2⟩
    · exact h2
    · exfalso
      have hW₂ne : W₂ ≠ ⊥ := by
        intro hbot
        have hcard := h.w.card₂
        rw [hbot, Subgroup.card_bot] at hcard
        norm_num at hcard
      obtain ⟨w, hw, hw1⟩ := (Subgroup.bot_or_exists_ne_one W₂).resolve_left hW₂ne
      have hmem₂ : y * w * y⁻¹ ∈ W₂ := hYnorm₂ y y.2 w hw
      let v : ↥(W₂.subgroupOf W) := ⟨⟨w, hW₂le hw⟩, hw⟩
      have hmem₁' := hswap2 (v : ↥W) v.2
      have hmem₁ : y * w * y⁻¹ ∈ W₁ := by
        have := hmem₁'
        rw [Subgroup.mem_subgroupOf] at this
        simp only [Subgroup.coe_subtype] at this
        rw [coe_toXW_apply] at this
        simpa [v] using this
      have hbot : y * w * y⁻¹ = 1 := by
        have hmem : y * w * y⁻¹ ∈ W₂ ⊓ W₁ := ⟨hmem₂, hmem₁⟩
        rw [inf_comm, h.w.inf_eq_bot] at hmem
        exact Subgroup.mem_bot.mp hmem
      have hw' : w = 1 := by
        have h1 : (y : G) * w = (y : G) * 1 := by
          have h2 := congrArg (fun x : G => x * (y : G)) hbot
          simpa [mul_assoc] using h2
        exact mul_left_cancel h1
      exact hw1 hw'
  let e₁ : ↥(W₁.subgroupOf W) ≃* ↥W₁ := Subgroup.subgroupOfEquivOfLe hW₁le
  let Q₁W : Subgroup (MulAut ↥W₁) := Q₁.map (MulAut.congr e₁).toMonoidHom
  have hmod : ModuleFacts Q₁W (e₁ t₁) := hx.module.map_mulEquiv e₁
  let Q₂W : Subgroup (MulAut ↥W₂) := Q₁W.map (MulAut.congr e₂.symm).toMonoidHom
  have hmod₂ : ModuleFacts Q₂W (e₂.symm (e₁ t₁)) := hmod.map_mulEquiv e₂.symm
  have hrange : ψ.range ≤ Q₂W := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨q, hq, hqval⟩ := hfirst y
    have heq : ψ y = MulAut.congr e₂.symm (MulAut.congr e₁ (hx.resEquiv ⟨q, hq⟩)) := by
      ext w
      have hψy : ((ψ y) w : G) = (y : G) * (w : G) * (y : G)⁻¹ := hψ y w
      rw [hψy]
      let v : ↥(W₂.subgroupOf W) := ⟨⟨w, hW₂le w.2⟩, w.2⟩
      have hqv := hqval v v.2
      have hz1 : ((e₁.symm (e₂ w) : ↥(W₁.subgroupOf W)) : ↥W) =
          ((XW W).subtype (toXW W ⟨z, h.z_mem_normalizer⟩)) ⟨w, hW₂le w.2⟩ := by
        apply Subtype.ext
        have hsub : ((XW W).subtype (toXW W ⟨z, h.z_mem_normalizer⟩) : MulAut ↥W) =
            ((toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W) := rfl
        rw [Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe, he₂, hsub, coe_toXW_apply]
      have hX : ((((XW W).subtype (toXW W ⟨(y : G), hSN (hYS y.2)⟩)) (v : ↥W) :
          ↥W) : G) = (y : G) * (w : G) * (y : G)⁻¹ := by
        have hsub : ((XW W).subtype (toXW W ⟨(y : G), hSN (hYS y.2)⟩) : MulAut ↥W) =
            ((toXW W ⟨(y : G), hSN (hYS y.2)⟩ : ↥(XW W)) : MulAut ↥W) := rfl
        rw [hsub, coe_toXW_apply]
      have hqX : ((((XW W).subtype q) (v : ↥W) : ↥W) : G) =
          (y : G) * (w : G) * (y : G)⁻¹ := by
        rw [← hqv]
        exact hX
      have hcomm : ((XW W).subtype q) * ((XW W).subtype (toXW W ⟨z, h.z_mem_normalizer⟩)) =
          ((XW W).subtype (toXW W ⟨z, h.z_mem_normalizer⟩)) * ((XW W).subtype q) := by
        rw [← map_mul, ← map_mul, hx.mul_comm_of_mem hq]
      have happly : ((XW W).subtype q) (((XW W).subtype (toXW W ⟨z, h.z_mem_normalizer⟩))
            ⟨w, hW₂le w.2⟩) =
          ((XW W).subtype (toXW W ⟨z, h.z_mem_normalizer⟩)) (((XW W).subtype q)
            ⟨w, hW₂le w.2⟩) := by
        simpa [MulAut.mul_apply] using
          congrArg (fun f : MulAut ↥W => f ⟨w, hW₂le w.2⟩) hcomm
      have hRHS : (((MulAut.congr e₂.symm (MulAut.congr e₁ (hx.resEquiv ⟨q, hq⟩))) w :
          ↥W₂) : G) = (y : G) * (w : G) * (y : G)⁻¹ := by
        have hA : ((MulAut.congr e₂.symm (MulAut.congr e₁ (hx.resEquiv ⟨q, hq⟩))) w :
            ↥W₂) = e₂.symm ((MulAut.congr e₁ (hx.resEquiv ⟨q, hq⟩)) (e₂ w)) := rfl
        rw [hA, he₂symm]
        have hB : ((MulAut.congr e₁ (hx.resEquiv ⟨q, hq⟩)) (e₂ w) : ↥W₁) =
            e₁ (((hx.resEquiv ⟨q, hq⟩ : MulAut ↥(W₁.subgroupOf W))
              (e₁.symm (e₂ w)))) := rfl
        rw [hB, Subgroup.subgroupOfEquivOfLe_apply_coe]
        rw [hx.resEquiv_apply]
        rw [hz1]
        rw [happly]
        have hsubz : ((XW W).subtype (toXW W ⟨z, h.z_mem_normalizer⟩) : MulAut ↥W) =
            ((toXW W ⟨z, h.z_mem_normalizer⟩ : ↥(XW W)) : MulAut ↥W) := rfl
        rw [hsubz, coe_toXW_apply]
        rw [hqX]
        group
      exact hRHS.symm
    rw [heq]
    exact Subgroup.mem_map_of_mem (MulAut.congr e₂.symm).toMonoidHom
      (Subgroup.mem_map_of_mem (MulAut.congr e₁).toMonoidHom (hx.resEquiv ⟨q, hq⟩).2)
  exact card_bound_of_module ψ hψ hmod₂ hrange hY hnotC

theorem WHyp.normalizer_le_of_xGood (h : WHyp G L A T z t W W₁ W₂) {Q : Subgroup ↥(XW W)}
    {Q₁ : Subgroup (MulAut ↥(W₁.subgroupOf W))} {t₁ : ↥(W₁.subgroupOf W)}
    (hx : XHyp (XW W).subtype Q (W₁.subgroupOf W) (W₂.subgroupOf W)
      (toXW W ⟨z, h.z_mem_normalizer⟩) Q₁ t₁)
    {S : Subgroup G} (hS : IsPGroup 2 S) (hWS : W ≤ S) (hSN : S ≤ normalizer (W : Set G))
    (hgood : ∀ (s : G) (hs : s ∈ S),
      XGood (XW W).subtype Q (W₁.subgroupOf W) (W₂.subgroupOf W) (toXW W ⟨s, hSN hs⟩)) :
    normalizer (S : Set G) ≤ normalizer (W : Set G) := by
  intro g hg
  have hW₁le : W₁ ≤ W := by rw [← h.sup_eq]; exact le_sup_left
  have hW₂le : W₂ ≤ W := by rw [← h.sup_eq]; exact le_sup_right
  let Y : Subgroup G := W.map (MulAut.conj g).toMonoidHom
  have hYP : Y ≤ S := by
    rintro _ ⟨w, hw, rfl⟩
    have hmem : g * w * g⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hg w).mp (hWS hw)
    simpa [MulAut.conj_apply] using hmem
  haveI : IsMulCommutative ↥W := h.elemAb.toIsMulCommutative
  have hCP : S ⊓ centralizer (W : Set G) ≤ W := by
    have hP : IsPGroup 2 ↥(S ⊓ centralizer (W : Set G)) := hS.to_inf_left
    have hW_le : W ≤ S ⊓ centralizer (W : Set G) :=
      le_inf hWS (Subgroup.le_centralizer W)
    exact (h.eq_of_le_centralizer hP hW_le inf_le_right).le
  have hperm : ∀ x ∈ S,
      ((∀ w ∈ W₁, x * w * x⁻¹ ∈ W₁) ∧ (∀ w ∈ W₂, x * w * x⁻¹ ∈ W₂)) ∨
      ((∀ w ∈ W₁, x * w * x⁻¹ ∈ W₂) ∧ (∀ w ∈ W₂, x * w * x⁻¹ ∈ W₁)) := by
    intro x hxS
    let xX := toXW W ⟨x, hSN hxS⟩
    rcases hgood x hxS with ⟨⟨q₁, hq₁, hq₁val⟩, ⟨q₂, hq₂, hq₂val⟩⟩ | ⟨hswap₁, hswap₂⟩
    · left
      constructor
      · intro w hw
        let v : ↥(W₁.subgroupOf W) := ⟨⟨w, hW₁le hw⟩, hw⟩
        have hmemV : ((XW W).subtype xX) v ∈ W₁.subgroupOf W := by
          rw [hq₁val v v.2]
          exact hx.apply_mem₁ hq₁ v.2
        have hmemG : ((((XW W).subtype xX) v : ↥W) : G) ∈ W₁ :=
          Subgroup.mem_subgroupOf.mp hmemV
        have hval := subtype_toXW_apply W ⟨x, hSN hxS⟩ (v : ↥W)
        rwa [hval] at hmemG
      · intro w hw
        let v : ↥(W₂.subgroupOf W) := ⟨⟨w, hW₂le hw⟩, hw⟩
        have hmemV : ((XW W).subtype xX) v ∈ W₂.subgroupOf W := by
          rw [hq₂val v v.2]
          exact hx.apply_mem₂ hq₂ v.2
        have hmemG : ((((XW W).subtype xX) v : ↥W) : G) ∈ W₂ :=
          Subgroup.mem_subgroupOf.mp hmemV
        have hval := subtype_toXW_apply W ⟨x, hSN hxS⟩ (v : ↥W)
        rwa [hval] at hmemG
    · right
      constructor
      · intro w hw
        let v : ↥(W₁.subgroupOf W) := ⟨⟨w, hW₁le hw⟩, hw⟩
        have hmemV : ((XW W).subtype xX) v ∈ W₂.subgroupOf W := hswap₁ v v.2
        have hmemG : ((((XW W).subtype xX) v : ↥W) : G) ∈ W₂ :=
          Subgroup.mem_subgroupOf.mp hmemV
        have hval := subtype_toXW_apply W ⟨x, hSN hxS⟩ (v : ↥W)
        rwa [hval] at hmemG
      · intro w hw
        let v : ↥(W₂.subgroupOf W) := ⟨⟨w, hW₂le hw⟩, hw⟩
        have hmemV : ((XW W).subtype xX) v ∈ W₁.subgroupOf W := hswap₂ v v.2
        have hmemG : ((((XW W).subtype xX) v : ↥W) : G) ∈ W₁ :=
          Subgroup.mem_subgroupOf.mp hmemV
        have hval := subtype_toXW_apply W ⟨x, hSN hxS⟩ (v : ↥W)
        rwa [hval] at hmemG
  have hY : IsElementaryAbelian 2 ↥Y := by
    have hmap := h.elemAb.subgroup_map (MulAut.conj g).toMonoidHom
    simpa [Y] using hmap
  have hYcard : 2 ^ (2 * 10) ≤ Nat.card Y := by
    have hcardY : Nat.card Y = 2 ^ 20 := by
      rw [show Nat.card Y = Nat.card W from
        Subgroup.card_map_of_injective (MulAut.conj g).injective, h.e3.card]
    rw [hcardY]
  have hYeq : Y = W :=
    CFSG.GroupTheory.eq_of_isElementaryAbelian_of_noOffenders (n := 10) (by norm_num)
      (W := W) (W₁ := W₁) (W₂ := W₂) (P := S)
      h.elemAb h.sup_eq h.w.inf_eq_bot h.w.card₁ h.w.card₂ hWS hCP hperm
      (fun Y' hY'S hY'norm hY'e hY'notC =>
        hoff₁ h hx hY'S hSN hgood hY'e (fun y hy => (hY'norm y hy).1) hY'notC)
      (fun Y' hY'S hY'norm hY'e hY'notC =>
        hoff₂ h hx hY'S hSN hgood hY'e (fun y hy => (hY'norm y hy).1)
          (fun y hy => (hY'norm y hy).2) hY'notC)
      hYP hY hYcard
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  simpa [Y] using hYeq

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
