module

public import CFSG.Quasithin.H13.L32A755e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems143

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.Orbit
open scoped commutatorElement

namespace Ctx753

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K : Subgroup G}

attribute [local instance] commGroupOfFact

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V))))]

theorem tildeV_inf_fixV_F4 (C : Ctx753 T L V K) (hMod : StmtL32NModule_F4)
    (hVL : V ≤ ⁅V, l1 T L V⁆) :
    subM (fsuV1 T V) (conjClosure V (hz T V)) V ⊓ fixV (autIH (fsuV1 T V) V (hz T V) K) = ⊥ := by
  obtain ⟨hVe, hV8, hLTV, hV1, -⟩ := hMod G T L V C.hyp.hyp C.hyp.fsu
  have hUN := C.U_le_normalizer
  have hVU : V ≤ conjClosure V (hz T V) := le_conjClosure V (hz T V)
  rw [eq_bot_iff]
  rintro w ⟨hwV, hwK⟩
  by_contra hw1

  obtain ⟨a, haU, hae⟩ := exists_mk_of_mem_tilde w
  have haV : (a : G) ∈ V := by
    have h1 := (mem_subM_iff (V₁ := fsuV1 T V) (IH := conjClosure V (hz T V))).1 hwV
    rw [← hae] at h1
    exact (secMk_mem_tildeOf_iff (inf_le_left : fsuV1 T V ≤ V)).1 h1
  set v : G := (a : G) with hv
  have hw : w = modMk hUN v haU := Subtype.ext hae.symm

  have hL1H : l1 T L V ≤ hz T V := C.l1_le.trans C.le_hz
  have hfix : ∀ l ∈ l1 T L V, l * v * l⁻¹ * v⁻¹ ∈ fsuV1 T V := by
    intro l hl
    have hlH := hL1H hl
    have hmem : actH C.f918.H_le_normalizer_V₁ (le_normalizer_conjClosure V (hz T V)) ⟨l, hlH⟩ ∈
        autIH (fsuV1 T V) V (hz T V) K := by
      rw [autIH_eq_map C.f918 C.le_hz]
      exact ⟨⟨l, hlH⟩, Subgroup.mem_subgroupOf.mpr (C.l1_le hl), rfl⟩
    have h1 := hwK _ hmem
    rw [hw, actH_modMk C.f918.H_le_normalizer_V₁ hUN (le_normalizer_conjClosure V (hz T V))] at h1
    have h2 := congrArg Subtype.val h1
    change secMk _ _ ⟨l * v * l⁻¹, _⟩ = secMk _ _ ⟨v, _⟩ at h2
    have h3 := secMk_eq_secMk_iff.1 h2
    change (l * v * l⁻¹)⁻¹ * v ∈ fsuV1 T V at h3
    have h4 := (Subgroup.mem_normalizer_iff.mp (hUN (hVU haV)) _).mp h3
    have e : l * v * l⁻¹ * v⁻¹ = (v * ((l * v * l⁻¹)⁻¹ * v) * v⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ h4

  have hvV₁ : v ∉ fsuV1 T V := by
    intro h
    apply hw1
    rw [hw]
    apply Subtype.ext
    change secMk _ _ ⟨v, _⟩ = 1
    exact secMk_eq_one_iff.2 h

  set W : Subgroup G := Subgroup.closure {v} ⊔ fsuV1 T V with hW
  have hWV : W ≤ V := sup_le ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 haV))
    inf_le_left
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => by
    have := hVe.1
    exact setLike_mul_comm hx hy
  have hsq : ∀ x ∈ V, x * x = 1 := fun x hx => by
    have := hVe.2 x hx
    rwa [pow_two] at this

  have hWcard : Nat.card W ≤ 4 := by
    have h1 : Nat.card ↥(Subgroup.closure ({v} : Set G)) ≤ 2 := by
      rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hsq v haV)
    have hcv : Subgroup.closure ({v} : Set G) ≤ V :=
      (Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 haV)
    have h2 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.closure ({v} : Set G))
      (fsuV1 T V) fun x hx y hy => hcomm x (hcv hx) y ((inf_le_left : fsuV1 T V ≤ V) hy)).1
    rw [hV1] at h2
    have h3 : 0 < Nat.card ↥(Subgroup.closure ({v} : Set G) ⊓ fsuV1 T V) := Nat.card_pos
    nlinarith

  have hWinv : ∀ l ∈ l1 T L V, ∀ x ∈ W, l * x * l⁻¹ ∈ W := by
    intro l hl
    have hlH := hL1H hl
    have hle : W ≤ W.comap (MulAut.conj l).toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [Subgroup.closure_le]
        rintro _ rfl
        change l * v * l⁻¹ ∈ W
        have e : l * v * l⁻¹ = (l * v * l⁻¹ * v⁻¹) * v := by group
        rw [e]
        exact W.mul_mem (Subgroup.mem_sup_right (hfix l hl))
          (Subgroup.mem_sup_left (Subgroup.subset_closure rfl))
      · intro c hc
        change l * c * l⁻¹ ∈ W
        rw [← Subgroup.mem_centralizer_iff.mp hlH c hc, mul_inv_cancel_right]
        exact Subgroup.mem_sup_right hc
    exact fun x hx => hle hx

  have hvW : v ∈ W := Subgroup.mem_sup_left (Subgroup.subset_closure rfl)
  have hV₁W : fsuV1 T V ≤ W := le_sup_right
  have hW4 : Nat.card W = 4 := by
    refine le_antisymm hWcard ?_
    have hdvd : Nat.card (fsuV1 T V) ∣ Nat.card W := Subgroup.card_dvd_of_le hV₁W
    rw [hV1] at hdvd
    have hne : Nat.card W ≠ 2 := by
      intro h2
      have := Subgroup.eq_of_le_of_card_ge hV₁W (by rw [h2, hV1])
      exact hvV₁ (this ▸ hvW)
    obtain ⟨k, hk⟩ := hdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      have : 0 < Nat.card W := Nat.card_pos
      omega
    have hk1 : k ≠ 1 := fun h1 => hne (by rw [hk, h1])
    omega
  have hidx : (W.subgroupOf V).index = 2 := by
    have h1 := Subgroup.relIndex_mul_card W V
    rw [show W ⊓ V = W from inf_eq_left.2 hWV, hW4, hV8] at h1
    change (W.subgroupOf V).index * 4 = 8 at h1
    omega

  have hLV : l1 T L V ≤ Subgroup.normalizer (V : Set G) :=
    (oTwoUpper_le _).trans (inf_le_left.trans (le_sup_left.trans hLTV))
  have hcommW : ⁅V, l1 T L V⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro x hx l hl
    have hlx : l * x⁻¹ * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hl) x⁻¹).mp (V.inv_mem hx)
    have e : ⁅x, l⁆ = x * (l * x⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    by_cases hxW : x ∈ W
    · exact W.mul_mem hxW (hWinv l hl _ (W.inv_mem hxW))
    · have h2 : l * x⁻¹ * l⁻¹ ∉ W := by
        intro h
        apply hxW
        have h3 := hWinv l⁻¹ (Subgroup.inv_mem _ hl) _ h
        have e2 : l⁻¹ * (l * x⁻¹ * l⁻¹) * l⁻¹⁻¹ = x⁻¹ := by group
        rw [e2] at h3
        exact (Subgroup.inv_mem_iff _).1 h3
      have h4 := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x, hx⟩) (b := ⟨_, hlx⟩)).2
        ⟨fun h => absurd (Subgroup.mem_subgroupOf.1 h) hxW,
          fun h => absurd (Subgroup.mem_subgroupOf.1 h) h2⟩
      exact Subgroup.mem_subgroupOf.1 h4
  have hle : V ≤ W := hVL.trans hcommW
  have := Subgroup.card_le_of_le hle
  rw [hV8, hW4] at this
  omega

theorem mem_of_piBar_eq_F4 (C : Ctx753 T L V K) (hMod : StmtL32NModule_F4)
    (hVL : V ≤ ⁅V, l1 T L V⁆) {a b : G} (ha : a ∈ V) (hb : b ∈ V)
    (h : M755.piBar (fixV (autIH (fsuV1 T V) V (hz T V) K))
        (modMk C.U_le_normalizer a (le_conjClosure V (hz T V) ha)) =
      M755.piBar _ (modMk C.U_le_normalizer b (le_conjClosure V (hz T V) hb))) :
    a⁻¹ * b ∈ fsuV1 T V := by
  have hVU : V ≤ conjClosure V (hz T V) := le_conjClosure V (hz T V)
  have hab : a⁻¹ * b ∈ V := V.mul_mem (V.inv_mem ha) hb
  have h2 : M755.piBar (fixV (autIH (fsuV1 T V) V (hz T V) K))
      (modMk C.U_le_normalizer (a⁻¹ * b) (hVU hab)) = 1 := by
    rw [modMk_mul C.U_le_normalizer (hVU (V.inv_mem ha)) (hVU hb),
      modMk_inv C.U_le_normalizer (hVU ha), map_mul, map_inv, h, inv_mul_cancel]
  rw [M755.piBar_eq_one_iff] at h2
  have h3 : modMk C.U_le_normalizer (a⁻¹ * b) (hVU hab) ∈
      subM (fsuV1 T V) (conjClosure V (hz T V)) V :=
    (modMk_mem_subM_iff C.U_le_normalizer (inf_le_left : fsuV1 T V ≤ V) _).2 hab
  have h5 : modMk C.U_le_normalizer (a⁻¹ * b) (hVU hab) ∈
      (⊥ : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V)))) :=
    C.tildeV_inf_fixV_F4 hMod hVL ▸ ⟨h3, h2⟩
  rw [Subgroup.mem_bot] at h5
  exact (C.modMk_eq_one_iff' _).1 h5

theorem coord_V2_F4 (C : Ctx753 T L V K) (hMod : StmtL32NModule_F4) (hVL : V ≤ ⁅V, l1 T L V⁆)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ}
    (hT : ∀ i ∈ M755.innerS, g2QAct (ZMod 2) (sEltG i) ∈
      (autSec (autIH (fsuV1 T V) V (hz T V) T) ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K))).map
        (MulAut.congr e).toMonoidHom)
    {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂) {w : G} (hw : w ∈ V₂) (hw1 : w ∉ fsuV1 T V) :
    e (M755.piBar _ (modMk C.U_le_normalizer w (le_conjClosure V (hz T V) (hV₂.2.1 hw)))) =
      M755.ptQ 8 := by
  obtain ⟨hV₁V₂, hV₂V, hTV₂, hV₂4⟩ := hV₂
  obtain ⟨-, -, -, hV1, -⟩ := hMod G T L V C.hyp.hyp C.hyp.fsu
  have hVU : V ≤ conjClosure V (hz T V) := le_conjClosure V (hz T V)
  have hwV := hV₂V hw
  refine M755.eq_ptQ_eight (fun h1 => hw1 ?_) fun i hi => ?_
  · have h2 : e (M755.piBar _ (modMk C.U_le_normalizer w (hVU hwV))) =
        e (M755.piBar _ (modMk C.U_le_normalizer 1 (hVU (V.one_mem)))) := by
      rw [h1, modMk_one, map_one, map_one]
    have h3 := C.mem_of_piBar_eq_F4 hMod hVL hwV V.one_mem (e.injective h2)
    rw [mul_one] at h3
    exact (Subgroup.inv_mem_iff _).1 h3
  · obtain ⟨t, ht, htu⟩ := C.exists_t_of_mem_map (hT i hi)
    rw [htu]
    congr 2
    have htw : t * w * t⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp (hTV₂ ht) w).mp hw
    have htw1 : t * w * t⁻¹ ∉ fsuV1 T V := by
      intro h
      apply hw1
      have hc := Subgroup.mem_centralizer_iff.mp (C.T_le ht) _ h
      have e1 : w = t * w * t⁻¹ := by
        calc w = t⁻¹ * ((t * w * t⁻¹) * t) := by group
          _ = t⁻¹ * (t * (t * w * t⁻¹)) := by rw [hc]
          _ = t * w * t⁻¹ := by group
      rw [e1]
      exact h
    have hmem := inv_mul_mem_of_two hV₁V₂ (by rw [hV1, hV₂4]) hw htw hw1 htw1
    exact Subtype.ext (secMk_eq_secMk_iff.mpr hmem).symm

theorem coord_V_F4 (C : Ctx753 T L V K) (hMod : StmtL32NModule_F4) (hVL : V ≤ ⁅V, l1 T L V⁆)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ}
    (hT : ∀ i ∈ M755.innerS, g2QAct (ZMod 2) (sEltG i) ∈
      (autSec (autIH (fsuV1 T V) V (hz T V) T) ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K))).map
        (MulAut.congr e).toMonoidHom)
    {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂) {v : G} (hv : v ∈ V) (hv2 : v ∉ V₂) :
    e (M755.piBar _ (modMk C.U_le_normalizer v (le_conjClosure V (hz T V) hv))) = M755.ptQ 32 ∨
      e (M755.piBar _ (modMk C.U_le_normalizer v (le_conjClosure V (hz T V) hv))) =
        M755.ptQ 40 := by
  obtain ⟨hV₁V₂, hV₂V, hTV₂, hV₂4⟩ := hV₂
  obtain ⟨-, hV8, hLTV, hV1, -⟩ := hMod G T L V C.hyp.hyp C.hyp.fsu
  have hVU : V ≤ conjClosure V (hz T V) := le_conjClosure V (hz T V)
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hLTV

  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ V₂, w ∉ fsuV1 T V := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show V₂ ≤ fsuV1 T V from h)
    rw [hV1, hV₂4] at this
    omega
  have hw8 := C.coord_V2_F4 hMod hVL hT ⟨hV₁V₂, hV₂V, hTV₂, hV₂4⟩ hw hw1
  have hv1 : v ∉ fsuV1 T V := fun h => hv2 (hV₁V₂ h)
  refine M755.eq_of_mem_line0 (fun h1 => hv1 ?_) (fun h8 => hv2 ?_) fun i hi => ?_
  · have h2 : e (M755.piBar _ (modMk C.U_le_normalizer v (hVU hv))) =
        e (M755.piBar _ (modMk C.U_le_normalizer 1 (hVU (V.one_mem)))) := by
      rw [h1, modMk_one, map_one, map_one]
    have h3 := C.mem_of_piBar_eq_F4 hMod hVL hv V.one_mem (e.injective h2)
    rw [mul_one] at h3
    exact (Subgroup.inv_mem_iff _).1 h3
  · have h3 := C.mem_of_piBar_eq_F4 hMod hVL (hV₂V hw) hv (e.injective (h8.trans hw8.symm).symm)
    have e1 : v = w * (w⁻¹ * v) := by group
    rw [e1]
    exact V₂.mul_mem hw (hV₁V₂ h3)
  · obtain ⟨t, ht, htu⟩ := C.exists_t_of_mem_map (hT i hi)
    rw [htu]
    have htv : t * v * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hTV ht) v).mp hv
    have htv2 : t * v * t⁻¹ ∉ V₂ := by
      intro h
      apply hv2
      have := (Subgroup.mem_normalizer_iff.mp (hTV₂ (T.inv_mem ht)) _).mp h
      simpa [mul_assoc] using this
    have hmem := inv_mul_mem_of_two hV₂V (by rw [hV₂4, hV8]) hv htv hv2 htv2
    have e1 : t * v * t⁻¹ = v * (v⁻¹ * (t * v * t⁻¹)) := by group
    have hx : v⁻¹ * (t * v * t⁻¹) ∈ V := V.mul_mem (V.inv_mem hv) htv
    have hsplit : modMk C.U_le_normalizer (t * v * t⁻¹) (hVU htv) =
        modMk C.U_le_normalizer v (hVU hv) *
          modMk C.U_le_normalizer (v⁻¹ * (t * v * t⁻¹)) (hVU hx) := by
      rw [← modMk_mul C.U_le_normalizer (hVU hv) (hVU hx)]
      congr 1
    by_cases h1 : v⁻¹ * (t * v * t⁻¹) ∈ fsuV1 T V
    · left
      congr 2
      exact Subtype.ext (secMk_eq_secMk_iff.mpr h1).symm
    · right
      have h2 : e (M755.piBar _ (modMk C.U_le_normalizer (v⁻¹ * (t * v * t⁻¹)) (hVU hx))) =
          M755.ptQ 8 := by
        rw [← hw8]
        congr 2
        apply Subtype.ext
        apply secMk_eq_secMk_iff.mpr
        exact inv_mul_mem_of_two hV₁V₂ (by rw [hV1, hV₂4]) hmem hw h1 hw1
      change e (M755.piBar _ (modMk C.U_le_normalizer (t * v * t⁻¹) (hVU htv))) = _
      rw [hsplit, map_mul, map_mul, h2, mul_comm]

end Ctx753

end CFSG.Quasithin.H13.L32A
