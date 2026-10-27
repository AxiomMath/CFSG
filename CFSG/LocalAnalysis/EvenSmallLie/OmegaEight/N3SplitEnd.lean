module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitFusion
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitConj
public import CFSG.Monster.B.Recog.GenericTransferExtremal

public section

namespace CFSG.EvenSmallLie.OmegaEight.N3Split

open Subgroup Matrix CFSG.EvenSmallLie.OmegaEight.Stage2

variable {G : Type*} [Group G]

theorem isMaximal_of_conj' [Finite G] {t : G} {TH T : Subgroup G} (htTH : t ∈ TH)
    (hTHc : TH ≤ centralizer ({t} : Set G))
    (hTHi : ¬ 2 ∣ (TH.subgroupOf (centralizer ({t} : Set G))).index) (hTH : TH ≤ T)
    (hconj : ∀ x ∈ normalizer (T : Set G), x * t * x⁻¹ ∈ T →
      ∃ y ∈ T, x * t * x⁻¹ = y * t * y⁻¹) :
    ∀ Q : Subgroup G, IsPGroup 2 Q → T ≤ Q → Q = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Q hQ hTQ
  by_contra hne
  obtain ⟨x, hxQ, hxT, hxN⟩ := exists_mem_normalizer_of_lt hQ hTQ (Ne.symm hne)
  have hxt : x * t * x⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hxN t).1 (hTH htTH)
  obtain ⟨y, hyT, hxy⟩ := hconj x hxN hxt
  have hz : y⁻¹ * x ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y⁻¹ * x * t = y⁻¹ * (x * t * x⁻¹) * x := by group
      _ = y⁻¹ * (y * t * y⁻¹) * x := by rw [hxy]
      _ = t * (y⁻¹ * x) := by group
  have hzQ : y⁻¹ * x ∈ Q := Q.mul_mem (Q.inv_mem (hTQ hyT)) hxQ
  have heq := eq_of_isPGroup_of_not_dvd hTHi (hQ.to_le inf_le_left)
    (le_inf (hTH.trans hTQ) hTHc) inf_le_right
  have hzTH : y⁻¹ * x ∈ TH := heq ▸ (⟨hzQ, hz⟩ : y⁻¹ * x ∈ Q ⊓ centralizer ({t} : Set G))
  apply hxT
  have : x = y * (y⁻¹ * x) := by group
  rw [this]
  exact T.mul_mem hyT (hTH hzTH)

theorem index_ne_two [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (K : Subgroup G) : K.index ≠ 2 := by
  intro hK
  have hn : K.Normal := Subgroup.normal_of_index_eq_two hK
  rcases hn.eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.index_bot] at hK
    obtain ⟨a, b, hab⟩ := hnab
    have : IsCyclic G := isCyclic_of_prime_card (p := 2) hK
    exact hab (IsCyclic.commGroup.mul_comm a b)
  · rw [h, Subgroup.index_top] at hK
    norm_num at hK

section Hyp

variable {M : Model} {t : G} {TH W : Subgroup G} {φ : W ≃* Multiplicative (Fin 12 → ZMod 2)}
  {a : G}

theorem exists_conj_of_rhoG_eq' [Finite G] (h : Stage2Hyp M t TH W φ)
    (hex : ∀ v : Vec12, (M.tbar : Mat12) *ᵥ v = v → ∃ x : Vec12, (M.tbar : Mat12) *ᵥ x + x = v)
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
  obtain ⟨x, hx⟩ := hex _ hfix
  set r : W := φ.symm (Multiplicative.ofAdd x) with hrdef
  have hrx : Multiplicative.toAdd (φ r) = x := by rw [hrdef, MulEquiv.apply_symm_apply]; rfl
  have hmem : t * (r : G) * t⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 h.t_mem_NW r).1 r.2
  set a' : W := ⟨t * (r : G) * t⁻¹, hmem⟩ with hadef
  have hax : Multiplicative.toAdd (φ a') = (M.tbar : Mat12) *ᵥ x := by
    have := rhoG_mulVec (φ := φ) h.t_mem_NW r
    rw [h.rho_t, hrx] at this
    rw [hadef, ← this]
  have hneg : ∀ y : Vec12, -y = y := fun y => by
    ext i
    have : ∀ c : ZMod 2, -c = c := by decide
    exact this _
  have key : a' * r⁻¹ = w := by
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

theorem exists_conj_of_rhoG_conj [Finite G] (h : Stage2Hyp M t TH W φ) (hF : SplitFacts M)
    {T : Subgroup G} (hTN : T ≤ NW W) (hT2 : IsPGroup 2 T) (hWT : W ≤ T) (hTHT : TH ≤ T)
    {u : G} (huT : u ∈ T) (hu2 : u * u = 1) {y : GL12} (hy : y ∈ rhoImg W φ T)
    (hρu : rhoG W φ u = y * M.tbar * y⁻¹) : ∃ z ∈ T, u = z * t * z⁻¹ := by
  obtain ⟨y₀, hy₀, rfl⟩ := (mem_rhoImg hTN).1 hy
  have htT : t ∈ T := hTHT h.t_mem
  have hu'T : y₀⁻¹ * u * y₀ ∈ T := T.mul_mem (T.mul_mem (T.inv_mem hy₀) huT) hy₀
  have hu'2 : y₀⁻¹ * u * y₀ * (y₀⁻¹ * u * y₀) = 1 := by
    calc y₀⁻¹ * u * y₀ * (y₀⁻¹ * u * y₀) = y₀⁻¹ * (u * u) * y₀ := by group
      _ = 1 := by rw [hu2]; group
  have hρu' : rhoG W φ (y₀⁻¹ * u * y₀) = M.tbar := by
    rw [rhoG_mul (hTN (T.mul_mem (T.inv_mem hy₀) huT)) (hTN hy₀),
      rhoG_mul (hTN (T.inv_mem hy₀)) (hTN huT), rhoG_inv (hTN hy₀), hρu]
    group
  obtain ⟨r, hr, hu'r⟩ := exists_conj_of_rhoG_eq' h hF.exists_of_fixM_tbar hTN hT2 hWT htT
    hu'T hu'2 hρu'
  refine ⟨y₀ * r, T.mul_mem hy₀ (hWT hr), ?_⟩
  calc u = y₀ * (y₀⁻¹ * u * y₀) * y₀⁻¹ := by group
    _ = y₀ * (r * t * r⁻¹) * y₀⁻¹ := by rw [hu'r]
    _ = (y₀ * r) * t * (y₀ * r)⁻¹ := by group

theorem extremal_of_normalizer [Finite G] (h : Stage2Hyp M t TH W φ) {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hTHT : TH ≤ T) {x : G} (hx : x ∈ normalizer (T : Set G)) :
    T ⊓ centralizer ({x * t * x⁻¹} : Set G) = TH.map (MulAut.conj x).toMonoidHom := by
  rw [inf_centralizer_conj hx, inf_centralizer_eq h hT2 hTHT]

theorem false_of_maximal_cand [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h : Stage2Hyp M t TH W φ) (hF : SplitFacts M)
    (hX : SplitExtra t TH W a) {T : Subgroup G} (hTN : T ≤ NW W) (hT2 : IsPGroup 2 T)
    (hWT : W ≤ T) (hTmax : ∀ Q : Subgroup G, IsPGroup 2 Q → T ≤ Q → Q = T)
    {Y : Subgroup GL12} (hYi : Y.relIndex (rhoImg W φ T) = 2)
    (hY : ∀ s ∈ Y, ¬ IsCand (rhoImg W φ T) s) : False := by
  let P : Sylow 2 G :=
    { toSubgroup := T, isPGroup' := hT2, is_maximal' := fun {Q} hQ hle => hTmax Q hQ hle }
  have hMidx : (T ⊓ rhoPre W φ Y).relIndex (P : Subgroup G) = 2 :=
    relIndex_inf_rhoPre hTN rfl hYi
  have ht2 : t ^ 2 = 1 := by rw [sq]; exact h.t_mul_t
  obtain ⟨g, hgM, hodd⟩ :=
    CFSG.Monster.B.Recog.exists_conj_mem_odd_relIndex_of_transfer P hMidx ht2
    (fun K hK => absurd hK (index_ne_two hG hnab K))
  have hgT : g * t * g⁻¹ ∈ T := (Subgroup.mem_inf.1 hgM).1
  obtain ⟨g', hu, hC⟩ := exists_extremal_of_odd h hT2 rfl hodd
  have hcand := isCand_of_extremal h hF hX hTN hT2 hWT hu hgT hC
  exact hY _ (mem_rhoPre.1 (Subgroup.mem_inf.1 hgM).2).2 hcand

theorem false_of_cand1 [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (h : Stage2Hyp M t TH W φ) (hF : SplitFacts M) (hX : SplitExtra t TH W a)
    {S Y : Subgroup GL12} (hSX : S ≤ Xof W φ) (hS2 : IsPGroup 2 S) (hTCS : M.TC ≤ S)
    (hcls : ∀ s ∈ S, IsCand S s → ∃ y ∈ S, s = y * M.tbar * y⁻¹)
    (hYi : Y.relIndex S = 2) (hY : ∀ s ∈ Y, ¬ IsCand S s) : False := by
  obtain ⟨T, hPT, hTN, hT2, hTS⟩ := h.exists_lift hSX hS2 hTCS
  have hWT : W ≤ T := le_sup_left.trans hPT
  have hTHT : TH ≤ T := le_sup_right.trans hPT
  have hmax : ∀ Q : Subgroup G, IsPGroup 2 Q → T ≤ Q → Q = T := by
    refine isMaximal_of_conj' h.t_mem h.TH_le h.TH_index hTHT fun x hx hxT => ?_
    have hcand := isCand_of_extremal h hF hX hTN hT2 hWT rfl hxT
      (extremal_of_normalizer h hT2 hTHT hx)
    rw [hTS] at hcand
    obtain ⟨y, hy, hyt⟩ := hcls _ (hTS ▸ rhoG_mem_rhoImg hTN hxT) hcand
    exact exists_conj_of_rhoG_conj h hF hTN hT2 hWT hTHT hxT (h.conj_mul_self x)
      (hTS ▸ hy) hyt
  subst hTS
  exact false_of_maximal_cand hG hnab h hF hX hTN hT2 hWT hmax hYi hY

theorem false_of_cand2 [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (h : Stage2Hyp M t TH W φ) (hF : SplitFacts M) (hX : SplitExtra t TH W a)
    {S Y : Subgroup GL12} {τ : GL12} (hSX : S ≤ Xof W φ) (hS2 : IsPGroup 2 S) (hTCS : M.TC ≤ S)
    (hcls : ∀ s ∈ S, IsCand S s → ∃ y ∈ S, s = y * M.tbar * y⁻¹ ∨ s = y * τ * y⁻¹)
    (hτcs : Nat.card ↥(S ⊓ centralizer ({τ} : Set GL12)) = 2 ^ 8)
    (hτfix : Nat.card (fixM (τ : Mat12)) = 2 ^ 6) (hτker : Nat.card (kerSet S τ) = 2)
    (hτX : ∀ x ∈ Xof W φ, x * M.tbar * x⁻¹ ≠ τ)
    (hYi : Y.relIndex S = 2) (hY : ∀ s ∈ Y, ¬ IsCand S s) : False := by
  obtain ⟨T, hPT, hTN, hT2, hTS⟩ := h.exists_lift hSX hS2 hTCS
  have hWT : W ≤ T := le_sup_left.trans hPT
  have hTHT : TH ≤ T := le_sup_right.trans hPT
  have hmax : ∀ Q : Subgroup G, IsPGroup 2 Q → T ≤ Q → Q = T := by
    refine isMaximal_of_conj' h.t_mem h.TH_le h.TH_index hTHT fun x hx hxT => ?_
    have hcand := isCand_of_extremal h hF hX hTN hT2 hWT rfl hxT
      (extremal_of_normalizer h hT2 hTHT hx)
    rw [hTS] at hcand
    obtain ⟨y, hy, hyt | hyτ⟩ := hcls _ (hTS ▸ rhoG_mem_rhoImg hTN hxT) hcand
    · exact exists_conj_of_rhoG_conj h hF hTN hT2 hWT hTHT hxT (h.conj_mul_self x)
        (hTS ▸ hy) hyt
    · exfalso
      have hyN : y ∈ normalizer (S : Set GL12) := le_normalizer hy
      have hcs : Nat.card ↥(rhoImg W φ T ⊓
          centralizer ({rhoG W φ (x * t * x⁻¹)} : Set GL12)) = 2 ^ 8 := by
        rw [hTS, hyτ, card_inf_centralizer_conj hyN, hτcs]
      have hfix : Nat.card (fixM (rhoG W φ (x * t * x⁻¹) : Mat12)) = 2 ^ 6 := by
        rw [hyτ, card_fixM_conj, hτfix]
      have hker : Nat.card (kerSet (rhoImg W φ T) (rhoG W φ (x * t * x⁻¹))) = 2 := by
        rw [hTS, hyτ, card_kerSet_conj hyN, hτker]
      have hxN := mem_NW_of_fusion h hF hX hTN hT2 hWT hTHT hx hcs hfix hker
      have hρ : rhoG W φ (x * t * x⁻¹) = rhoG W φ x * M.tbar * (rhoG W φ x)⁻¹ := by
        rw [rhoG_mul (mul_mem hxN h.t_mem_NW) (inv_mem hxN), rhoG_mul hxN h.t_mem_NW,
          rhoG_inv hxN, h.rho_t]
      apply hτX (y⁻¹ * rhoG W φ x)
        ((Xof W φ).mul_mem ((Xof W φ).inv_mem (hSX hy)) (rhoG_mem_Xof hxN))
      calc y⁻¹ * rhoG W φ x * M.tbar * (y⁻¹ * rhoG W φ x)⁻¹ =
          y⁻¹ * (rhoG W φ x * M.tbar * (rhoG W φ x)⁻¹) * y := by group
        _ = y⁻¹ * (y * τ * y⁻¹) * y := by rw [← hρ, hyτ]
        _ = τ := by group
  subst hTS
  exact false_of_maximal_cand hG hnab h hF hX hTN hT2 hWT hmax hYi hY

theorem false_of_offender_cand [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h : Stage2Hyp M t TH W φ) (hF : SplitFacts M)
    (hX : SplitExtra t TH W a) {S Y : Subgroup GL12} (hSX : S ≤ Xof W φ) (hS2 : IsPGroup 2 S)
    (hTCS : M.TC ≤ S) (hSmax : ∀ Z : Subgroup GL12, Z ≤ Xof W φ → IsPGroup 2 Z → S ≤ Z → Z = S)
    (hoff : ∀ A : Subgroup GL12, A ≤ S → (∀ x ∈ A, x * x = 1) → A ≠ ⊥ →
      Nat.card A * Nat.card ↥(Set.univ ∩ fixV A) ≤ 2 ^ 11)
    (hYi : Y.relIndex S = 2) (hY : ∀ s ∈ Y, ¬ IsCand S s) : False := by
  obtain ⟨T, hPT, hTN, hT2, hTS⟩ := h.exists_lift hSX hS2 hTCS
  have hWT : W ≤ T := le_sup_left.trans hPT
  have hmax := isMaximal_of_offender h.sylow_W hTN hT2 hWT hTS hSmax hoff
  subst hTS
  exact false_of_maximal_cand hG hnab h hF hX hTN hT2 hWT hmax hYi hY

theorem tbar_mem_TC (h : Stage2Hyp M t TH W φ) : M.tbar ∈ M.TC := h.rho_t ▸ h.rho_TH t h.t_mem

theorem tbar_sq [Finite G] (h : Stage2Hyp M t TH W φ) : M.tbar * M.tbar = 1 := by
  rw [← h.rho_t, ← rhoG_mul h.t_mem_NW h.t_mem_NW, h.t_mul_t, rhoG_one]

theorem TC_pgroup (hF : SplitFacts M) : IsPGroup 2 M.TC := IsPGroup.of_card hF.card_TC

theorem inf_centralizer_tbar (h : Stage2Hyp M t TH W φ) (hF : SplitFacts M)
    {S : Subgroup GL12} (hSX : S ≤ Xof W φ) (hS2 : IsPGroup 2 S) (hTCS : M.TC ≤ S) :
    S ⊓ centralizer ({M.tbar} : Set GL12) = M.TC := by
  have hTCc : M.TC ≤ centralizer ({M.tbar} : Set GL12) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := h.TC_le y hy
    rw [mem_centralizer_singleton_iff, ← h.rho_t,
      ← rhoG_mul (h.TH_le_normalizer hx) h.t_mem_NW, ← rhoG_mul h.t_mem_NW
        (h.TH_le_normalizer hx), mem_centralizer_singleton_iff.1 (h.TH_le hx)]
  have hle : S ⊓ centralizer ({M.tbar} : Set GL12) ≤ M.CC := fun y hy =>
    h.mem_CC_of_commute (hSX hy.1) (mem_centralizer_singleton_iff.1 hy.2)
  exact hF.TC_max _ (hS2.to_le inf_le_left) (le_inf hTCS hTCc) hle

theorem isMax_of_inv [Finite G] (h : Stage2Hyp M t TH W φ) (hF : SplitFacts M)
    {S : Subgroup GL12} (hSX : S ≤ Xof W φ) (hS2 : IsPGroup 2 S) (hTCS : M.TC ≤ S)
    (hcls : ∀ s ∈ S, s * s = 1 → Nat.card (fixM (s : Mat12)) = 2 ^ 6 →
      Nat.card ↥(S ⊓ centralizer ({s} : Set GL12)) = 2 ^ 8 →
      Nat.card (burnSet S s) = Nat.card (burnSet S M.tbar) → ∃ y ∈ S, s = y * M.tbar * y⁻¹) :
    ∀ Z : Subgroup GL12, Z ≤ Xof W φ → IsPGroup 2 Z → S ≤ Z → Z = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Z hZX hZ2 hSZ
  by_contra hne
  obtain ⟨m, hmZ, hmS, hmN⟩ := exists_mem_normalizer_of_lt hZ2 hSZ (Ne.symm hne)
  have hmX := hZX hmZ
  have htS : M.tbar ∈ S := hTCS (tbar_mem_TC h)
  have hsS : m * M.tbar * m⁻¹ ∈ S := (mem_normalizer_iff.1 hmN _).1 htS
  have hs2 : m * M.tbar * m⁻¹ * (m * M.tbar * m⁻¹) = 1 := by
    calc m * M.tbar * m⁻¹ * (m * M.tbar * m⁻¹) = m * (M.tbar * M.tbar) * m⁻¹ := by group
      _ = 1 := by rw [tbar_sq h, mul_one, mul_inv_cancel]
  have hSC := inf_centralizer_tbar h hF hSX hS2 hTCS
  have hcs : Nat.card ↥(S ⊓ centralizer ({m * M.tbar * m⁻¹} : Set GL12)) = 2 ^ 8 := by
    rw [card_inf_centralizer_conj hmN, hSC, hF.card_TC]
  have hfix : Nat.card (fixM ((m * M.tbar * m⁻¹ : GL12) : Mat12)) = 2 ^ 6 := by
    rw [card_fixM_conj, hF.card_fixM_tbar]
  obtain ⟨y, hyS, hy⟩ := hcls _ hsS hs2 hfix hcs (card_burnSet_conj hmN _)
  have hwX : y⁻¹ * m ∈ Xof W φ := (Xof W φ).mul_mem ((Xof W φ).inv_mem (hSX hyS)) hmX
  have hwt : y⁻¹ * m * M.tbar = M.tbar * (y⁻¹ * m) := by
    calc y⁻¹ * m * M.tbar = y⁻¹ * (m * M.tbar * m⁻¹) * m := by group
      _ = y⁻¹ * (y * M.tbar * y⁻¹) * m := by rw [hy]
      _ = M.tbar * (y⁻¹ * m) := by group
  have hwC := h.mem_CC_of_commute hwX hwt
  have hwZ : y⁻¹ * m ∈ Z := Z.mul_mem (Z.inv_mem (hSZ hyS)) hmZ
  have hwNS : y⁻¹ * m ∈ normalizer (S : Set GL12) :=
    (normalizer (S : Set GL12)).mul_mem ((normalizer (S : Set GL12)).inv_mem
      (le_normalizer hyS)) hmN
  have hTC : S ⊓ M.CC = M.TC :=
    hF.TC_max _ (hS2.to_le inf_le_left) (le_inf hTCS hF.TC_le_CC) inf_le_right
  have hwN : y⁻¹ * m ∈ normalizer (M.TC : Set GL12) := by
    rw [← hTC, mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxS, hxC⟩
      exact ⟨(mem_normalizer_iff.1 hwNS x).1 hxS,
        M.CC.mul_mem (M.CC.mul_mem hwC hxC) (M.CC.inv_mem hwC)⟩
    · rintro ⟨hxS, hxC⟩
      refine ⟨(mem_normalizer_iff.1 hwNS x).2 hxS, ?_⟩
      have e : x = (y⁻¹ * m)⁻¹ * ((y⁻¹ * m) * x * (y⁻¹ * m)⁻¹) * (y⁻¹ * m) := by group
      rw [e]
      exact M.CC.mul_mem (M.CC.mul_mem (M.CC.inv_mem hwC) hxC) hwC
  have h2 : IsPGroup 2 (M.TC ⊔ zpowers (y⁻¹ * m) : Subgroup GL12) :=
    IsPGroup.to_sup_of_normal_left' (TC_pgroup hF) (hZ2.to_le ((zpowers_le).2 hwZ))
      ((zpowers_le).2 hwN)
  have h3 := hF.TC_max _ h2 le_sup_left (sup_le hF.TC_le_CC ((zpowers_le).2 hwC))
  have hwT : y⁻¹ * m ∈ M.TC :=
    h3 ▸ (le_sup_right : zpowers (y⁻¹ * m) ≤ M.TC ⊔ zpowers (y⁻¹ * m)) (mem_zpowers _)
  apply hmS
  have e : m = y * (y⁻¹ * m) := by group
  rw [e]
  exact S.mul_mem hyS (hTCS hwT)

end Hyp

end CFSG.EvenSmallLie.OmegaEight.N3Split
