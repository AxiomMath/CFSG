module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Transfer

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

open Subgroup Matrix

structure Model where
  tbar : GL12
  CC : Subgroup GL12
  TC : Subgroup GL12

variable {G : Type*} [Group G]

structure Stage2Hyp (M : Model) (t : G) (TH W : Subgroup G)
    (φ : W ≃* Multiplicative (Fin 12 → ZMod 2)) : Prop where
  orderOf_t : orderOf t = 2
  t_mem : t ∈ TH
  TH_le : TH ≤ centralizer ({t} : Set G)
  TH_pgroup : IsPGroup 2 TH
  TH_index : ¬ 2 ∣ (TH.subgroupOf (centralizer ({t} : Set G))).index
  TH_le_normalizer : TH ≤ normalizer (W : Set G)
  sylow_W : ∀ S : Subgroup G, S ≤ centralizer (W : Set G) → IsPGroup 2 S → S ≤ W
  rho_t : rhoG W φ t = M.tbar
  rho_TH : ∀ x ∈ TH, rhoG W φ x ∈ M.TC
  TC_le : ∀ y ∈ M.TC, ∃ x ∈ TH, rhoG W φ x = y
  CC_le : ∀ y ∈ M.CC, ∃ g ∈ normalizer (W : Set G), rhoG W φ g = y
  centralizer_le : ∀ g ∈ normalizer (W : Set G),
    rhoG W φ g * M.tbar = M.tbar * rhoG W φ g → rhoG W φ g ∈ M.CC

structure ModelFacts (M : Model) : Prop where
  card_fixM_tbar : Nat.card (fixM (M.tbar : Mat12)) ≤ 2 ^ 7
  exists_of_fixM_tbar : ∀ v : Vec12, (M.tbar : Mat12) *ᵥ v = v →
    ∃ x : Vec12, (M.tbar : Mat12) *ᵥ x + x = v
  offender_m2 : ∀ E : Subgroup GL12, E ≤ M.TC → (∀ x ∈ E, x * x = 1) → E ≠ ⊥ →
    Nat.card E * Nat.card ↥(fixM (M.tbar : Mat12) ∩ fixV E) ≤ 2 ^ 7

namespace Stage2Hyp

variable {M : Model} {t : G} {TH W : Subgroup G} {φ : W ≃* Multiplicative (Fin 12 → ZMod 2)}

theorem t_mem_NW (h : Stage2Hyp M t TH W φ) : t ∈ NW W := h.TH_le_normalizer h.t_mem

theorem t_mul_t (h : Stage2Hyp M t TH W φ) : t * t = 1 := by
  rw [← sq, ← h.orderOf_t, pow_orderOf_eq_one]

theorem t_inv (h : Stage2Hyp M t TH W φ) : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t

theorem card_fixM_le [Finite G] (h : Stage2Hyp M t TH W φ) (hM : ModelFacts M) {u g : G}
    (hu : u = g * t * g⁻¹) (hun : u ∈ NW W) : Nat.card (fixM (rhoG W φ u : Mat12)) ≤ 2 ^ 7 := by
  refine card_fixM_le_of_conj (t := t) ?_ hu hun
  have hoff := hM.offender_m2
  rw [← h.rho_t] at hoff
  exact card_le_of_le_centralizer h.TH_index h.TH_le h.TH_le_normalizer h.sylow_W h.rho_TH
    h.t_mem_NW hoff (h.rho_t ▸ hM.card_fixM_tbar)

theorem exists_conj_of_rhoG_eq [Finite G] (h : Stage2Hyp M t TH W φ) (hM : ModelFacts M)
    {T : Subgroup G} (hTN : T ≤ NW W) (hT2 : IsPGroup 2 T) (hWT : W ≤ T) (htT : t ∈ T) {u : G}
    (huT : u ∈ T) (hu2 : u * u = 1) (hρu : rhoG W φ u = M.tbar) : ∃ r ∈ W, u = r * t * r⁻¹ := by
  have hw : t⁻¹ * u ∈ W := by
    rw [← inf_centralizer_eq_W φ hT2 hWT h.sylow_W]
    refine ⟨T.mul_mem (T.inv_mem htT) huT, mem_centralizer_of_rhoG_eq_one (φ := φ)
      (hTN (T.mul_mem (T.inv_mem htT) huT)) ?_⟩
    rw [rhoG_mul (hTN (T.inv_mem htT)) (hTN huT), rhoG_inv (hTN htT), h.rho_t, hρu,
      inv_mul_cancel]
  set w : W := ⟨t⁻¹ * u, hw⟩ with hwdef
  have e1 : u = t * w := by rw [hwdef]; group
  have e2 : (w : G) * (w : G) = 1 := W_mem_sq φ hw
  have e3 : t * (w : G) * (t * w) = 1 := by rw [← e1]; exact hu2
  have htw : t * (w : G) * t⁻¹ = w :=
    calc t * (w : G) * t⁻¹ = t * w * t := by rw [h.t_inv]
      _ = t * w * t * (w * w) := by rw [e2, mul_one]
      _ = (t * w * (t * w)) * w := by group
      _ = w := by rw [e3, one_mul]
  have hfix : (M.tbar : Mat12) *ᵥ Multiplicative.toAdd (φ w) = Multiplicative.toAdd (φ w) := by
    have := (mem_fixM_rhoG_iff (φ := φ) h.t_mem_NW w).2 htw
    rw [h.rho_t] at this
    exact this
  obtain ⟨x, hx⟩ := hM.exists_of_fixM_tbar _ hfix
  set r : W := φ.symm (Multiplicative.ofAdd x) with hrdef
  have hrx : Multiplicative.toAdd (φ r) = x := by rw [hrdef, MulEquiv.apply_symm_apply]; rfl
  have hmem : t * (r : G) * t⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 h.t_mem_NW r).1 r.2
  set a : W := ⟨t * (r : G) * t⁻¹, hmem⟩ with hadef
  have hax : Multiplicative.toAdd (φ a) = (M.tbar : Mat12) *ᵥ x := by
    have := rhoG_mulVec (φ := φ) h.t_mem_NW r
    rw [h.rho_t, hrx] at this
    rw [hadef, ← this]
  have hneg : ∀ y : Vec12, -y = y := fun y => by
    ext i
    have : ∀ c : ZMod 2, -c = c := by decide
    exact this _
  have key : a * r⁻¹ = w := by
    apply φ.injective
    apply Multiplicative.toAdd.injective
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hax, hrx, hneg, hx]
  have key' : t * (r : G) * t⁻¹ * (r : G)⁻¹ = w := by
    have := congrArg Subtype.val key
    simpa [hadef] using this
  refine ⟨r, r.2, ?_⟩
  calc u = t * w := e1
    _ = t * (t * (r : G) * t⁻¹ * (r : G)⁻¹) := by rw [key']
    _ = (t * t) * r * t⁻¹ * (r : G)⁻¹ := by group
    _ = r * t * (r : G)⁻¹ := by rw [h.t_mul_t, one_mul, h.t_inv]

theorem conj_mul_self (h : Stage2Hyp M t TH W φ) (g : G) :
    g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
  calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
    _ = 1 := by rw [h.t_mul_t, mul_one, mul_inv_cancel]

theorem rhoG_conj_mul_self (h : Stage2Hyp M t TH W φ) {g : G} (hgN : g * t * g⁻¹ ∈ NW W) :
    rhoG W φ (g * t * g⁻¹) * rhoG W φ (g * t * g⁻¹) = 1 := by
  rw [← rhoG_mul hgN hgN, h.conj_mul_self, rhoG_one]

theorem isPGroup_W_sup (h : Stage2Hyp M t TH W φ) : IsPGroup 2 (W ⊔ TH : Subgroup G) :=
  IsPGroup.to_sup_of_normal_left' (isPGroup_of_sq_eq_one fun _ hx => W_mem_sq φ hx)
    h.TH_pgroup h.TH_le_normalizer

theorem exists_lift [Finite G] (h : Stage2Hyp M t TH W φ) {S : Subgroup GL12}
    (hSX : S ≤ Xof W φ) (hS2 : IsPGroup 2 S) (hTCS : M.TC ≤ S) :
    ∃ T : Subgroup G, W ⊔ TH ≤ T ∧ T ≤ NW W ∧ IsPGroup 2 T ∧ rhoImg W φ T = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := rhoPre W φ S with hK
  have hKN : K ≤ NW W := fun g hg => (mem_rhoPre.1 hg).1
  have hPK : W ⊔ TH ≤ K := by
    refine sup_le (fun w hw => mem_rhoPre.2 ⟨W_le_NW hw, ?_⟩)
      (fun x hx => mem_rhoPre.2 ⟨h.TH_le_normalizer hx, hTCS (h.rho_TH x hx)⟩)
    rw [rhoG_W (φ := φ) hw]
    exact one_mem S
  have hP' : IsPGroup 2 ((W ⊔ TH).subgroupOf K) :=
    h.isPGroup_W_sup.of_equiv (Subgroup.subgroupOfEquivOfLe hPK).symm
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  let f : K →* S := (rhoOn W φ hKN).codRestrict S fun k => by
    rw [rhoOn_apply]
    exact (mem_rhoPre.1 k.2).2
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨g, hg, rfl⟩ := mem_Xof.1 (hSX hy)
    exact ⟨⟨g, mem_rhoPre.2 ⟨hg, hy⟩⟩, Subtype.ext (rhoOn_apply hKN _)⟩
  have htop : ((Q.mapSurjective hf : Sylow 2 S) : Subgroup S) = ⊤ :=
    ((Q.mapSurjective hf).is_maximal' (hS2.of_equiv Subgroup.topEquiv.symm) le_top).symm
  refine ⟨(Q : Subgroup K).map K.subtype, fun g hg => ⟨⟨g, hPK hg⟩,
    hQ (Subgroup.mem_subgroupOf.2 hg), rfl⟩, ?_, Q.isPGroup'.map _, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact hKN k.2
  · have hTN : (Q : Subgroup K).map K.subtype ≤ NW W := by
      rintro _ ⟨k, -, rfl⟩
      exact hKN k.2
    ext y
    rw [mem_rhoImg hTN]
    constructor
    · rintro ⟨_, ⟨k, -, rfl⟩, rfl⟩
      exact (mem_rhoPre.1 k.2).2
    · intro hy
      have hmem : (⟨y, hy⟩ : S) ∈ ((Q.mapSurjective hf : Sylow 2 S) : Subgroup S) :=
        htop ▸ mem_top _
      rw [Sylow.coe_mapSurjective] at hmem
      obtain ⟨k, hk, e⟩ := hmem
      refine ⟨k, ⟨k, hk, rfl⟩, ?_⟩
      have e' := congrArg Subtype.val e
      rw [← rhoOn_apply hKN k]
      exact e'

theorem false_of_offender [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (h : Stage2Hyp M t TH W φ) (hM : ModelFacts M) {S Y : Subgroup GL12} (hSX : S ≤ Xof W φ)
    (hS2 : IsPGroup 2 S) (hTCS : M.TC ≤ S)
    (hSmax : ∀ Z : Subgroup GL12, Z ≤ Xof W φ → IsPGroup 2 Z → S ≤ Z → Z = S)
    (hoff : ∀ A : Subgroup GL12, A ≤ S → (∀ x ∈ A, x * x = 1) → A ≠ ⊥ →
      Nat.card A * Nat.card ↥(Set.univ ∩ fixV A) ≤ 2 ^ 11)
    (hYi : Y.relIndex S = 2) (hY : ∀ y ∈ Y, y * y = 1 → 2 ^ 8 ≤ Nat.card (fixM (y : Mat12))) :
    False := by
  obtain ⟨T, hPT, hTN, hT2, hTS⟩ := h.exists_lift hSX hS2 hTCS
  have hWT : W ≤ T := le_sup_left.trans hPT
  have hmax := isMaximal_of_offender h.sylow_W hTN hT2 hWT hTS hSmax hoff
  refine false_of_transfer hG hnab h.orderOf_t hT2 hmax inf_le_left
    (relIndex_inf_rhoPre hTN hTS hYi) fun g hg => ?_
  obtain ⟨hgN, hρ⟩ := mem_rhoPre.1 (Subgroup.mem_inf.1 hg).2
  have h1 := h.card_fixM_le hM rfl hgN
  have h3 := hY _ hρ (h.rhoG_conj_mul_self hgN)
  omega

theorem false_of_oneClass [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (h : Stage2Hyp M t TH W φ) (hM : ModelFacts M) {S Y : Subgroup GL12} (hSX : S ≤ Xof W φ)
    (hS2 : IsPGroup 2 S) (hTCS : M.TC ≤ S)
    (hcls : ∀ s ∈ S, s * s = 1 → Nat.card (fixM (s : Mat12)) ≤ 2 ^ 7 →
      ∃ y ∈ S, s = y * M.tbar * y⁻¹)
    (hYS : Y ≤ S) (hYi : Y.relIndex S = 2) (htY : M.tbar ∉ Y) : False := by
  obtain ⟨T, hPT, hTN, hT2, hTS⟩ := h.exists_lift hSX hS2 hTCS
  have hWT : W ≤ T := le_sup_left.trans hPT
  have hTHT : TH ≤ T := le_sup_right.trans hPT
  have htT : t ∈ T := hTHT h.t_mem
  have hcls' : ∀ g : G, g * t * g⁻¹ ∈ T →
      ∃ s ∈ S, rhoG W φ (g * t * g⁻¹) = s * M.tbar * s⁻¹ := by
    intro g hg
    have hgN := hTN hg
    exact hcls _ (hTS ▸ rhoG_mem_rhoImg hTN hg) (h.rhoG_conj_mul_self hgN)
      (h.card_fixM_le hM rfl hgN)
  have hconj : ∀ g : G, g * t * g⁻¹ ∈ T → ∃ y ∈ T, g * t * g⁻¹ = y * t * y⁻¹ := by
    intro g hg
    obtain ⟨s, hs, hρ⟩ := hcls' g hg
    obtain ⟨y₀, hy₀, rfl⟩ := (mem_rhoImg hTN).1 (hTS ▸ hs)
    have hu'T : y₀⁻¹ * (g * t * g⁻¹) * y₀ ∈ T :=
      T.mul_mem (T.mul_mem (T.inv_mem hy₀) hg) hy₀
    have hu'2 : y₀⁻¹ * (g * t * g⁻¹) * y₀ * (y₀⁻¹ * (g * t * g⁻¹) * y₀) = 1 := by
      calc y₀⁻¹ * (g * t * g⁻¹) * y₀ * (y₀⁻¹ * (g * t * g⁻¹) * y₀) =
          y₀⁻¹ * (g * t * g⁻¹ * (g * t * g⁻¹)) * y₀ := by group
        _ = 1 := by rw [h.conj_mul_self, mul_one, inv_mul_cancel]
    have hρu' : rhoG W φ (y₀⁻¹ * (g * t * g⁻¹) * y₀) = M.tbar := by
      rw [rhoG_mul (hTN (T.mul_mem (T.inv_mem hy₀) hg)) (hTN hy₀),
        rhoG_mul (hTN (T.inv_mem hy₀)) (hTN hg), rhoG_inv (hTN hy₀), hρ]
      group
    obtain ⟨r, hr, hu'r⟩ := h.exists_conj_of_rhoG_eq hM hTN hT2 hWT htT hu'T hu'2 hρu'
    refine ⟨y₀ * r, T.mul_mem hy₀ (hWT hr), ?_⟩
    calc g * t * g⁻¹ = y₀ * (y₀⁻¹ * (g * t * g⁻¹) * y₀) * y₀⁻¹ := by group
      _ = y₀ * (r * t * r⁻¹) * y₀⁻¹ := by rw [hu'r]
      _ = (y₀ * r) * t * (y₀ * r)⁻¹ := by group
  have hmax := isMaximal_of_conj h.t_mem h.TH_le h.TH_index hTHT hconj
  refine false_of_transfer hG hnab h.orderOf_t hT2 hmax inf_le_left
    (relIndex_inf_rhoPre hTN hTS hYi) fun g hg => ?_
  obtain ⟨hgT, hgY⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨-, hρY⟩ := mem_rhoPre.1 hgY
  obtain ⟨s, hs, hρ⟩ := hcls' g hgT
  have hYn : (Y.subgroupOf S).Normal := Subgroup.normal_of_index_eq_two hYi
  have hmem := hYn.conj_mem ⟨_, hYS hρY⟩ (Subgroup.mem_subgroupOf.2 hρY) ⟨s⁻¹, S.inv_mem hs⟩
  rw [Subgroup.mem_subgroupOf] at hmem
  apply htY
  have e : M.tbar = s⁻¹ * rhoG W φ (g * t * g⁻¹) * s⁻¹⁻¹ := by rw [hρ]; group
  rw [e]
  exact hmem

end Stage2Hyp

end CFSG.EvenSmallLie.OmegaEight.Stage2
