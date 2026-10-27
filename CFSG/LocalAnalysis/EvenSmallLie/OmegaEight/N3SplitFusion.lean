module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitExtremal

public section

namespace CFSG.EvenSmallLie.OmegaEight.N3Split

open Subgroup Matrix CFSG.EvenSmallLie.OmegaEight.Stage2

variable {G : Type*} [Group G]

theorem inf_centralizer_conj {T : Subgroup G} {x : G} (hx : x ∈ normalizer (T : Set G)) (t : G) :
    T ⊓ centralizer ({x * t * x⁻¹} : Set G) =
      (T ⊓ centralizer ({t} : Set G)).map (MulAut.conj x).toMonoidHom := by
  rw [centralizer_conj]
  ext y
  simp only [mem_inf, mem_map, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    MulAut.conj_apply]
  constructor
  · rintro ⟨hy, z, hz, rfl⟩
    refine ⟨z, ⟨?_, hz⟩, rfl⟩
    have := (mem_normalizer_iff.1 hx z).2 hy
    exact this
  · rintro ⟨z, ⟨hzT, hz⟩, rfl⟩
    exact ⟨(mem_normalizer_iff.1 hx z).1 hzT, z, hz, rfl⟩

theorem conj_mem_sup {W : Subgroup G} (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hWsq : ∀ a ∈ W, a * a = 1) {u : G} (huN : u ∈ normalizer (W : Set G)) (hu2 : u * u = 1)
    {w : G} (hw : w ∈ W) :
    w * u * w⁻¹ ∈ (W ⊓ centralizer ({u} : Set G)) ⊔ zpowers u := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hWsq w hw)
  set a := u⁻¹ * w * u with ha
  have haW : a ∈ W := by
    have := (mem_normalizer_iff.1 (inv_mem huN) w).1 hw
    simpa [ha] using this
  set c := a * w with hc
  have hcW : c ∈ W := W.mul_mem haW hw
  have hua : u * a * u⁻¹ = w := by rw [ha]; group
  have huw : u * w * u⁻¹ = a := by
    rw [ha, hui]
  have hcu : u * c * u⁻¹ = c := by
    calc u * c * u⁻¹ = (u * a * u⁻¹) * (u * w * u⁻¹) := by rw [hc]; group
      _ = w * a := by rw [hua, huw]
      _ = c := by rw [hc, hWc w hw a haW]
  have e : w * u * w⁻¹ = u * c := by
    rw [hc, ha, hwi]
    calc w * u * w = u * (u⁻¹ * w * u * w) := by group
      _ = u * (u⁻¹ * w * u * w) := rfl
  rw [e]
  have hcu' : c * u = u * c := by
    calc c * u = u * c * u⁻¹ * u := by rw [hcu]
      _ = u * c := by group
  exact mul_mem (mem_sup_right (mem_zpowers u))
    (mem_sup_left ⟨hcW, mem_centralizer_singleton_iff.2 hcu'⟩)

section Hyp

variable {M : Model} {t : G} {TH W : Subgroup G} {φ : W ≃* Multiplicative (Fin 12 → ZMod 2)}
  {a : G}

theorem eq_W_of_offender [Finite G] (h : Stage2Hyp M t TH W φ) {B : Subgroup G}
    (hBN : B ≤ NW W) (hsq : ∀ x ∈ B, x * x = 1) (hcard : Nat.card B = 2 ^ 12)
    {S' : Subgroup GL12} (hBS : rhoImg W φ B ≤ S')
    (hoff : ∀ A : Subgroup GL12, A ≤ S' → (∀ x ∈ A, x * x = 1) → A ≠ ⊥ →
      Nat.card A * Nat.card ↥(Set.univ ∩ fixV A) ≤ 2 ^ 11) : B = W := by
  have hB2 : IsPGroup 2 B := isPGroup_of_sq_eq_one hsq
  by_cases hbot : rhoImg W φ B = ⊥
  · have hBC : B ≤ centralizer (W : Set G) := by
      intro b hb
      have hρ : rhoG W φ b ∈ rhoImg W φ B := rhoG_mem_rhoImg hBN hb
      rw [hbot, mem_bot] at hρ
      exact mem_centralizer_of_rhoG_eq_one (hBN hb) hρ
    have hBW := h.sylow_W B hBC hB2
    exact Subgroup.eq_of_le_of_card_ge hBW (by rw [hcard, card_W φ])
  · exfalso
    have hc := card_eq_card_rhoImg_mul (φ := φ) hBN
    have hAW := inf_centralizer_le_W (W := W) hB2 h.sylow_W
    have hk := card_inf_centralizer_le (φ := φ) hBN hAW
      (fun x hx y hy => commute_of_sq_eq_one hsq hx hy) (Z := Set.univ) (fun _ _ => trivial)
    have hsq' : ∀ y ∈ rhoImg W φ B, y * y = 1 := by
      intro y hy
      obtain ⟨b, hb, rfl⟩ := (mem_rhoImg hBN).1 hy
      rw [← rhoG_mul (hBN hb) (hBN hb), hsq b hb, rhoG_one]
    have hle := hoff _ hBS hsq' hbot
    have := (Nat.mul_le_mul_left (Nat.card (rhoImg W φ B)) hk).trans hle
    rw [← hc, hcard] at this
    norm_num at this

theorem tbar_ne_one (hF : SplitFacts M) : M.tbar ≠ 1 := by
  intro e
  have h1 := hF.card_fixM_tbar
  rw [e, card_fixM_one] at h1
  norm_num at h1

theorem t_not_mem_W (h : Stage2Hyp M t TH W φ) (hF : SplitFacts M) : t ∉ W := fun ht =>
  tbar_ne_one hF (h.rho_t ▸ rhoG_W ht)

theorem card_E₁ [Finite G] (h : Stage2Hyp M t TH W φ) (hF : SplitFacts M) :
    Nat.card ((W ⊓ centralizer ({t} : Set G)) ⊔ zpowers t : Subgroup G) = 128 := by
  have h1 : t ∉ W ⊓ centralizer ({t} : Set G) := fun ht => t_not_mem_W h hF (mem_inf.1 ht).1
  have h2 : ∀ w ∈ W ⊓ centralizer ({t} : Set G), w * t = t * w :=
    fun w hw => mem_centralizer_singleton_iff.1 (mem_inf.1 hw).2
  rw [card_sup_zpowers h.t_mul_t h1 h2, card_inf_centralizer_W φ h.t_mem_NW, h.rho_t,
    hF.card_fixM_tbar]
  norm_num

theorem map_conj_map_conj_inv (X : Subgroup G) (x : G) :
    (X.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom = X := by
  rw [Subgroup.map_map]
  ext y
  simp [mul_assoc]

theorem mem_normalizer_sup [Finite G] {X : Subgroup G} {u w : G}
    (hX : ∀ y ∈ X, w * y * w⁻¹ ∈ X ⊔ zpowers u) (hu : w * u * w⁻¹ ∈ X ⊔ zpowers u) :
    w ∈ normalizer ((X ⊔ zpowers u : Subgroup G) : Set G) := by
  set F := X ⊔ zpowers u with hF
  have hle : F.map (MulAut.conj w).toMonoidHom ≤ F := by
    rw [hF, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hX y hy
    · rw [MonoidHom.map_zpowers, zpowers_le]
      exact hu
  have heq : F.map (MulAut.conj w).toMonoidHom = F :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj w).injective])
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : (MulAut.conj w).toMonoidHom y ∈ F.map (MulAut.conj w).toMonoidHom := mem_map_of_mem _ hy
    rw [heq] at this
    simpa using this
  · intro hy
    rw [← heq] at hy
    obtain ⟨z, hz, e⟩ := hy
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply] at e
    have : z = y := by
      have e' : w * z * w⁻¹ = w * y * w⁻¹ := e
      simpa using e'
    rw [← this]
    exact hz

theorem centralizer_map_conj (X : Subgroup G) (x : G) :
    centralizer ((X.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) =
      (centralizer (X : Set G)).map (MulAut.conj x).toMonoidHom := by
  ext y
  simp only [mem_map, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
  constructor
  · intro hy
    refine ⟨x⁻¹ * y * x, mem_centralizer_iff.2 fun z hz => ?_, by group⟩
    have := mem_centralizer_iff.1 hy (x * z * x⁻¹) ⟨z, hz, rfl⟩
    have e : x * (z * (x⁻¹ * y * x)) * x⁻¹ = x * ((x⁻¹ * y * x) * z) * x⁻¹ := by
      calc x * (z * (x⁻¹ * y * x)) * x⁻¹ = x * z * x⁻¹ * y := by group
        _ = y * (x * z * x⁻¹) := this
        _ = x * ((x⁻¹ * y * x) * z) * x⁻¹ := by group
    simpa using e
  · rintro ⟨c, hc, rfl⟩
    refine mem_centralizer_iff.2 ?_
    rintro _ ⟨z, hz, rfl⟩
    have := mem_centralizer_iff.1 hc z hz
    simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]
    calc x * z * x⁻¹ * (x * c * x⁻¹) = x * (z * c) * x⁻¹ := by group
      _ = x * (c * z) * x⁻¹ := by rw [this]
      _ = x * c * x⁻¹ * (x * z * x⁻¹) := by group

theorem rhoImg_inf_CC [Finite G] (h : Stage2Hyp M t TH W φ) (hF : SplitFacts M)
    {T : Subgroup G} (hTN : T ≤ NW W) (hT2 : IsPGroup 2 T) (hTHT : TH ≤ T) :
    rhoImg W φ T ⊓ M.CC = M.TC := by
  have hTCS : M.TC ≤ rhoImg W φ T := by
    rw [← rhoImg_TH h]
    intro y hy
    obtain ⟨c, hc, rfl⟩ := (mem_rhoImg h.TH_le_normalizer).1 hy
    exact (mem_rhoImg hTN).2 ⟨c, hTHT hc, rfl⟩
  exact hF.TC_max _ ((isPGroup_rhoImg hT2 hTN).to_le inf_le_left) (le_inf hTCS hF.TC_le_CC)
    inf_le_right

theorem mem_NW_of_fusion [Finite G] (h : Stage2Hyp M t TH W φ) (hF : SplitFacts M)
    (hX : SplitExtra t TH W a) {T : Subgroup G} (hTN : T ≤ NW W) (hT2 : IsPGroup 2 T)
    (hWT : W ≤ T) (hTHT : TH ≤ T) {x : G} (hxT : x ∈ normalizer (T : Set G))
    (hcs : Nat.card ↥(rhoImg W φ T ⊓
      centralizer ({rhoG W φ (x * t * x⁻¹)} : Set GL12)) = 2 ^ 8)
    (hfix : Nat.card (fixM (rhoG W φ (x * t * x⁻¹) : Mat12)) = 2 ^ 6)
    (hker : Nat.card (kerSet (rhoImg W φ T) (rhoG W φ (x * t * x⁻¹))) = 2) :
    x ∈ NW W := by
  set u := x * t * x⁻¹ with hu
  set S := rhoImg W φ T with hS
  have huT : u ∈ T := (mem_normalizer_iff.1 hxT t).1 (hTHT h.t_mem)
  have huN : u ∈ NW W := hTN huT
  have hu2 : u * u = 1 := h.conj_mul_self x
  have hρu1 : rhoG W φ u ≠ 1 := by
    intro e
    rw [e, card_fixM_one] at hfix
    norm_num at hfix
  have huW : u ∉ W := fun h' => hρu1 (rhoG_W h')
  set P := T ⊓ centralizer ({u} : Set G) with hP
  have hPeq : P = TH.map (MulAut.conj x).toMonoidHom := by
    rw [hP, hu, inf_centralizer_conj hxT, inf_centralizer_eq h hT2 hTHT]
  have hPN : P ≤ NW W := inf_le_left.trans hTN
  have hcardP : Nat.card P = 2 ^ 14 := by
    rw [hPeq, card_map_of_injective (MulAut.conj x).injective, card_TH h, hF.card_TC,
      hF.card_fixM_tbar]
    norm_num
  set A' := W ⊓ centralizer ({u} : Set G) with hA'
  have hA'P : A' ≤ P := fun w hw => ⟨hWT hw.1, hw.2⟩
  have hcardA' : Nat.card A' = 2 ^ 6 := by rw [hA', card_inf_centralizer_W φ huN, hfix]
  have hWcomm : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val (W_comm φ ⟨v, hv⟩ ⟨w, hw⟩)
  have hPW : P ⊓ centralizer (W : Set G) = A' := by
    refine le_antisymm (fun y hy => ⟨inf_centralizer_le_W hT2 h.sylow_W ⟨hy.1.1, hy.2⟩, hy.1.2⟩)
      (fun w hw => ⟨hA'P hw, mem_centralizer_iff.2 fun v hv => hWcomm v hv w hw.1⟩)
  have hρPle : rhoImg W φ P ≤ S ⊓ centralizer ({rhoG W φ u} : Set GL12) := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := (mem_rhoImg hPN).1 hy
    refine ⟨(mem_rhoImg hTN).2 ⟨c, hc.1, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
    have hcu : c * u = u * c := mem_centralizer_singleton_iff.1 hc.2
    rw [← rhoG_mul (hPN hc) huN, ← rhoG_mul huN (hPN hc), hcu]
  have hρP : rhoImg W φ P = S ⊓ centralizer ({rhoG W φ u} : Set GL12) := by
    refine Subgroup.eq_of_le_of_card_ge hρPle ?_
    have h1 := card_eq_card_rhoImg_mul (φ := φ) hPN
    rw [hPW, hcardP, hcardA'] at h1
    rw [hcs]
    omega
  set B := P ⊓ centralizer (A' : Set G) with hB
  have hBN : B ≤ NW W := inf_le_left.trans hPN
  have hρB : ∀ c : GL12, c ∈ rhoImg W φ B ↔ c ∈ kerSet S (rhoG W φ u) := by
    intro c
    constructor
    · intro hc
      obtain ⟨b, hb, rfl⟩ := (mem_rhoImg hBN).1 hc
      have hbS := hρPle ((mem_rhoImg hPN).2 ⟨b, hb.1, rfl⟩)
      refine ⟨hbS.1, mem_centralizer_singleton_iff.1 hbS.2, fun v hv => ?_⟩
      set w := φ.symm (Multiplicative.ofAdd v) with hw
      have hwv : Multiplicative.toAdd (φ w) = v := by simp [hw]
      have hwu : u * (w : G) * u⁻¹ = w :=
        (mem_fixM_rhoG_iff (φ := φ) huN w).1 (by rw [hwv]; exact hv)
      have hwA : (w : G) ∈ A' := ⟨w.2, mem_centralizer_singleton_iff.2 (by
        calc (w : G) * u = u * w * u⁻¹ * u := by rw [hwu]
          _ = u * w := by group)⟩
      have hbw : b * (w : G) * b⁻¹ = w := by
        rw [← mem_centralizer_iff.1 hb.2 w hwA, mul_inv_cancel_right]
      have := (mem_fixM_rhoG_iff (φ := φ) (hBN hb) w).2 hbw
      rw [hwv] at this
      exact this
    · rintro ⟨hcS, hcu, hcfix⟩
      have hcP : c ∈ rhoImg W φ P := by
        rw [hρP]
        exact ⟨hcS, mem_centralizer_singleton_iff.2 hcu⟩
      obtain ⟨b, hb, rfl⟩ := (mem_rhoImg hPN).1 hcP
      refine (mem_rhoImg hBN).2 ⟨b, ⟨hb, mem_centralizer_iff.2 fun w hw => ?_⟩, rfl⟩
      have hwu : u * w * u⁻¹ = w := by
        rw [← mem_centralizer_singleton_iff.1 hw.2, mul_inv_cancel_right]
      have hv := (mem_fixM_rhoG_iff (φ := φ) huN ⟨w, hw.1⟩).2 hwu
      have hbv := hcfix _ hv
      have := (mem_fixM_rhoG_iff (φ := φ) (hPN hb) ⟨w, hw.1⟩).1 hbv
      calc w * b = b * w * b⁻¹ * b := by rw [this]
        _ = b * w := by group
  have hcardρB : Nat.card (rhoImg W φ B) = 2 := by
    have e : Nat.card (rhoImg W φ B) = Nat.card (kerSet S (rhoG W φ u)) :=
      Nat.card_congr (Equiv.subtypeEquivRight hρB)
    rw [e]
    exact hker
  have hBW : B ⊓ centralizer (W : Set G) = A' := by
    refine le_antisymm (fun y hy => ?_) (fun w hw => ⟨⟨hA'P hw, mem_centralizer_iff.2
      fun v hv => hWcomm v hv.1 w hw.1⟩, mem_centralizer_iff.2 fun v hv => hWcomm v hv w hw.1⟩)
    rw [← hPW]
    exact ⟨hy.1.1, hy.2⟩
  have hcardB : Nat.card B = 128 := by
    rw [card_eq_card_rhoImg_mul (φ := φ) hBN, hcardρB, hBW, hcardA']
    norm_num
  set A := A'.map (MulAut.conj x⁻¹).toMonoidHom with hAdef
  have hTHeq : TH = P.map (MulAut.conj x⁻¹).toMonoidHom := by
    rw [hPeq, Subgroup.map_map]
    ext y
    simp [mul_assoc]
  have hATH : A ≤ TH := by
    rw [hTHeq]
    exact map_mono hA'P
  have hPA' : ∀ p ∈ P, ∀ w ∈ A', p * w * p⁻¹ ∈ A' := by
    intro p hp w hw
    refine ⟨(mem_normalizer_iff.1 (hTN hp.1) w).1 hw.1, mem_centralizer_singleton_iff.2 ?_⟩
    have hpu : p * u = u * p := mem_centralizer_singleton_iff.1 hp.2
    have hwu : w * u = u * w := mem_centralizer_singleton_iff.1 hw.2
    have hpu' : p⁻¹ * u = u * p⁻¹ := commute_inv_of_commute hpu
    calc p * w * p⁻¹ * u = p * w * (u * p⁻¹) := by rw [mul_assoc, hpu']
      _ = p * (w * u) * p⁻¹ := by group
      _ = p * (u * w) * p⁻¹ := by rw [hwu]
      _ = (p * u) * w * p⁻¹ := by group
      _ = u * (p * w * p⁻¹) := by rw [hpu]; group
  have hAn : ∀ y ∈ TH, ∀ z ∈ A, y * z * y⁻¹ ∈ A := by
    intro y hy z hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hyP : x * y * x⁻¹ ∈ P := by rw [hPeq]; exact ⟨y, hy, rfl⟩
    refine ⟨x * y * x⁻¹ * w * (x * y * x⁻¹)⁻¹, hPA' _ hyP w hw, ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv]
    group
  have hAsq : ∀ z ∈ A, z * z = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv]
    calc x⁻¹ * w * x * (x⁻¹ * w * x) = x⁻¹ * (w * w) * x := by group
      _ = 1 := by rw [W_mem_sq φ hw.1]; group
  have hcardA : Nat.card A = 64 := by
    rw [hAdef, card_map_of_injective (MulAut.conj x⁻¹).injective, hcardA']
    norm_num
  have htA : t ∉ A := by
    rintro ⟨w, hw, e⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
      inv_inv] at e
    apply huW
    have : u = w := by rw [hu, ← e]; group
    rw [this]
    exact hw.1
  have hcardC : Nat.card ↥(TH ⊓ centralizer (A : Set G)) = 128 := by
    rw [hTHeq, hAdef, centralizer_map_conj, ← Subgroup.map_inf_eq _ _ _
      (MulAut.conj x⁻¹).injective, card_map_of_injective (MulAut.conj x⁻¹).injective]
    exact hcardB
  have hAE := hX.nsc A hATH hAn hAsq hcardA htA hcardC
  set E₁ : Subgroup G := (W ⊓ centralizer ({t} : Set G)) ⊔ zpowers t with hE₁
  have hAt : A ⊔ zpowers t = E₁ := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hAE le_sup_right) ?_
    rw [card_E₁ h hF, card_sup_zpowers h.t_mul_t htA
      (fun z hz => mem_centralizer_singleton_iff.1 (h.TH_le (hATH hz))), hcardA]
  have hxE : E₁.map (MulAut.conj x).toMonoidHom = A' ⊔ zpowers u := by
    rw [← hAt, Subgroup.map_sup, hAdef, map_conj_map_conj_inv, MonoidHom.map_zpowers]
    rfl
  have hWN : ∀ w ∈ W, w ∈ normalizer ((A' ⊔ zpowers u : Subgroup G) : Set G) := by
    intro w hw
    refine mem_normalizer_sup (fun y hy => mem_sup_left ?_) ?_
    · rw [hWcomm w hw y hy.1, mul_inv_cancel_right]
      exact hy
    · exact conj_mem_sup hWcomm (fun z hz => W_mem_sq φ hz) huN hu2 hw
  set F := W.map (MulAut.conj x⁻¹).toMonoidHom with hFdef
  have hxiT : x⁻¹ ∈ normalizer (T : Set G) := inv_mem hxT
  have hFT : F ≤ T := by
    rintro _ ⟨w, hw, rfl⟩
    have := (mem_normalizer_iff.1 hxiT w).1 (hWT hw)
    simpa using this
  have hFE : ∀ y ∈ F, ∀ z ∈ E₁, y * z * y⁻¹ ∈ E₁ := by
    rintro _ ⟨w, hw, rfl⟩ z hz
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv]
    have hmem : ∀ y, y ∈ E₁ ↔ x * y * x⁻¹ ∈ A' ⊔ zpowers u := by
      intro y
      rw [← hxE]
      constructor
      · intro hy
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y', hy', e⟩
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply] at e
        have : y' = y := by simpa using e
        rw [← this]
        exact hy'
    rw [hmem] at hz ⊢
    have := (mem_normalizer_iff.1 (hWN w hw) _).1 hz
    have e : x * (x⁻¹ * w * x * z * (x⁻¹ * w * x)⁻¹) * x⁻¹ = w * (x * z * x⁻¹) * w⁻¹ := by group
    rw [e]
    exact this
  have hSC := rhoImg_inf_CC h hF hTN hT2 hTHT
  have hρF : rhoImg W φ F ≤ M.TC := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := (mem_rhoImg (hFT.trans hTN)).1 hc
    have hyN := hTN (hFT hy)
    have htE : t ∈ E₁ := mem_sup_right (mem_zpowers t)
    have hyt := hFE y hy t htE
    have hcomm : ∀ z ∈ W ⊓ centralizer ({t} : Set G), z * t = t * z :=
      fun z hz => mem_centralizer_singleton_iff.1 hz.2
    obtain ⟨z, hz, e | e⟩ := (mem_sup_zpowers_iff h.t_mul_t hcomm).1 hyt
    · exfalso
      have h1 : rhoG W φ (y * t * y⁻¹) = 1 := by rw [e]; exact rhoG_W hz.1
      rw [rhoG_mul (mul_mem hyN h.t_mem_NW) (inv_mem hyN), rhoG_mul hyN h.t_mem_NW,
        rhoG_inv hyN, h.rho_t] at h1
      apply tbar_ne_one hF
      calc M.tbar = (rhoG W φ y)⁻¹ * (rhoG W φ y * M.tbar * (rhoG W φ y)⁻¹) * rhoG W φ y := by
            group
        _ = 1 := by rw [h1]; group
    · have h1 : rhoG W φ (y * t * y⁻¹) = M.tbar := by
        rw [e, rhoG_mul (W_le_NW hz.1) h.t_mem_NW, rhoG_W hz.1, h.rho_t, one_mul]
      rw [rhoG_mul (mul_mem hyN h.t_mem_NW) (inv_mem hyN), rhoG_mul hyN h.t_mem_NW,
        rhoG_inv hyN, h.rho_t] at h1
      have hct : rhoG W φ y * M.tbar = M.tbar * rhoG W φ y := by
        calc rhoG W φ y * M.tbar = rhoG W φ y * M.tbar * (rhoG W φ y)⁻¹ * rhoG W φ y := by
              group
          _ = M.tbar * rhoG W φ y := by rw [h1]
      rw [← hSC]
      exact ⟨(mem_rhoImg hTN).2 ⟨y, hFT hy, rfl⟩, h.centralizer_le y hyN hct⟩
  have hFsq : ∀ z ∈ F, z * z = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv]
    calc x⁻¹ * w * x * (x⁻¹ * w * x) = x⁻¹ * (w * w) * x := by group
      _ = 1 := by rw [W_mem_sq φ hw]; group
  have hcardF : Nat.card F = 2 ^ 12 := by
    rw [hFdef, card_map_of_injective (MulAut.conj x⁻¹).injective, card_W φ]
  have hFW : F = W := eq_W_of_offender h (hFT.trans hTN) hFsq hcardF hρF hF.offender_TC
  rw [mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    have h1 : x * w * x⁻¹ ∈ F.map (MulAut.conj x).toMonoidHom := ⟨w, hFW ▸ hw, rfl⟩
    rw [hFdef, map_conj_map_conj_inv] at h1
    exact h1
  · intro hw
    have h1 : x⁻¹ * (x * w * x⁻¹) * x⁻¹⁻¹ ∈ F := ⟨x * w * x⁻¹, hw, rfl⟩
    rw [hFW] at h1
    have e : x⁻¹ * (x * w * x⁻¹) * x⁻¹⁻¹ = w := by group
    rw [e] at h1
    exact h1

end Hyp

end CFSG.EvenSmallLie.OmegaEight.N3Split
