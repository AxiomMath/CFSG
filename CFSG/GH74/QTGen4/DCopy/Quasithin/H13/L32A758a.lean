module

public import CFSG.Quasithin.H13.L32A758a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A756g

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.H13.Orbit
open scoped commutatorElement

namespace Ctx753

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K : Subgroup G}

attribute [local instance] commGroupOfFact

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V))))]

theorem caseI_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hG : M755.G2Facts) (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4)
    (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    (h13314 : A6.Stmt13_3_14_F4) (h1222 : Stmt12_2_2_F4) {γ γ' : F8.Geom T L (hz T V)}
    {g k : ↥((L ⊔ T) ⊔ hz T V)} (N : Not1471 T L V (hz T V) γ γ' g k) :
    C.ΦX E (conjSub ((k : G) * g) (conjClosure V (hz T V))) ≤ sSubG ∧
      (∃ e₀ ∈ [1, 2, 6], ∀ i, i ∈ idx (C.ΦX E (conjSub ((k : G) * g) (conjClosure V (hz T V))))
        ↔ i ∈ sE8.getD e₀ []) ∧
      (centralizerMod (conjSub ((k : G) * g) (fsuV1 T V)) (conjClosure V (hz T V))
        (conjSub ((k : G) * g) (conjClosure V (hz T V)))).relIndex (conjClosure V (hz T V)) =
      (conjSub ((k : G) * g) (conjClosure V (hz T V)) ⊓ pCoreOf 2 (hz T V)).relIndex
        (conjSub ((k : G) * g) (conjClosure V (hz T V))) := by
  set x := (k : G) * g with hx
  have hUαH := N.uα_le_hz C
  have hAS := C.ΦX_le_sSubG E (N.uα_le_T C)
  have hUαe : IsElemAbelian 2 (conjSub x (conjClosure V (hz T V))) :=
    F7.isElemAbelian_conjSub C.hF98.F911_3
  obtain ⟨hA2, hAc⟩ := C.ΦX_elem E hUαH hUαe
  have hA1 : C.ΦX E (conjSub x (conjClosure V (hz T V))) ≠ ⊥ := by
    intro hA
    have hcard := C.card_ΦX E hUαH
    rw [hA, Subgroup.card_bot] at hcard
    exact absurd hcard.symm (ne_of_gt (N.one_lt_relIndex C))
  set D := centralizerMod (conjSub x (fsuV1 T V)) (conjClosure V (hz T V))
    (conjSub x (conjClosure V (hz T V))) with hDdef
  have hDU : D ≤ conjClosure V (hz T V) := centralizerMod_le_left _ _ _
  have hcomm := C.comm_D_eq_bot_F4 E hG h13322 hMod hVL hV₂ h13314 h1222 N

  have hθD : C.θX e D ≤ fixV ((C.ΦX E (conjSub x (conjClosure V (hz T V)))).map
      (g2QAct (ZMod 2))) := by
    intro q hq
    obtain ⟨d, hd, rfl⟩ := (C.mem_θX e hDU).1 hq
    rintro _ ⟨γ₀, hγ₀, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (C.mem_ΦX E hUαH).1 hγ₀
    have h1 : ⁅d, a⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hd ha
      rw [hcomm, Subgroup.mem_bot] at this
      exact this
    rw [commutatorElement_def] at h1
    have h2 : a * d * a⁻¹ = d := by
      have e1 : a * d * a⁻¹ = (d * a * d⁻¹ * a⁻¹)⁻¹ * d := by group
      rw [e1, h1, inv_one, one_mul]
    change g2QAct (ZMod 2) (C.ΦG E a) (C.θG e d) = C.θG e d
    rw [← C.θG_conj E (hUαH ha) (hDU hd), h2]

  have hDle : D.relIndex (conjClosure V (hz T V)) ≤
      Nat.card (C.ΦX E (conjSub x (conjClosure V (hz T V)))) := by
    rw [C.card_ΦX E hUαH]
    exact N.relIndex_D_le C
  have hθidx : (C.θX e D).index ∣ D.relIndex (conjClosure V (hz T V)) :=
    Subgroup.index_map_dvd _ (C.θ_surjective e)
  have hpos : 0 < D.relIndex (conjClosure V (hz T V)) :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite
      (H := D.subgroupOf (conjClosure V (hz T V))))
  have hmul := (C.θX e D).card_mul_index
  rw [card_ModQ] at hmul
  have : Finite ModQ := Nat.finite_of_card_ne_zero (by rw [card_ModQ]; norm_num)
  have hcθ := Subgroup.card_le_of_le hθD
  have hθle := Nat.le_of_dvd hpos hθidx
  have hff : 64 ≤ (idx (C.ΦX E (conjSub x (conjClosure V (hz T V))))).card *
      Nat.card (fixV ((C.ΦX E (conjSub x (conjClosure V (hz T V)))).map (g2QAct (ZMod 2)))) := by
    rw [← card_eq_idx hAS]
    calc 64 = Nat.card (C.θX e D) * (C.θX e D).index := hmul.symm
      _ ≤ Nat.card (fixV ((C.ΦX E (conjSub x (conjClosure V (hz T V)))).map
            (g2QAct (ZMod 2)))) * D.relIndex (conjClosure V (hz T V)) :=
          Nat.mul_le_mul hcθ hθle
      _ ≤ _ := by rw [mul_comm]; exact Nat.mul_le_mul_right _ hDle
  obtain ⟨h8, hfix8⟩ := B42U33.offender_exact_sylow hAS hA1 hAc hA2 hff
  obtain ⟨e₀, he₀, hidx⟩ := idx_eq_sE8 hAS hA2 hAc (by omega)

  obtain ⟨v₃₂, hv₃₂, -, hθ₃₂⟩ := C.exists_V_θG_F4 E hMod hVL hV₂ (d := 32) (by simp)
  obtain ⟨v₄₀, hv₄₀, -, hθ₄₀⟩ := C.exists_V_θG_F4 E hMod hVL hV₂ (d := 40) (by simp)
  have hfixV : ∀ i ∈ sE8.getD e₀ [], M755.actC i 32 = 32 ∧ M755.actC i 40 = 40 := by
    intro i hi
    have hi64 := M755.sE8_lt e₀ he₀ i hi
    obtain ⟨a, ha, hae⟩ := (C.mem_ΦX E hUαH).1 (mem_idx.1 ((hidx i).2 hi)).2
    have hR := N.uα_le_R1 C ha
    have h32 : (32 : ℕ) ∈ M755.qCodes := by decide
    have h40 : (40 : ℕ) ∈ M755.qCodes := by decide
    have f1 := C.ΦG_fix_V E hR hv₃₂
    have f2 := C.ΦG_fix_V E hR hv₄₀
    rw [hθ₃₂, hae, M755.g2QAct_sEltG_code hi64 h32] at f1
    rw [hθ₄₀, hae, M755.g2QAct_sEltG_code hi64 h40] at f2
    exact ⟨M755.ptQ_inj (M755.actC_qCodes i hi64 _ h32) h32 f1,
      M755.ptQ_inj (M755.actC_qCodes i hi64 _ h40) h40 f2⟩
  have hcount : (o0Codes.filter fun c => !c.testBit 0 &&
      (sE8.getD e₀ []).all fun i => fixQB (sM i) c).length = 8 := by
    rw [← card_fixV_Q hAS _ (fun c => by
      rw [List.all_eq_true]
      exact forall_congr' fun i => imp_congr (hidx i).symm Iff.rfl)]
    exact hfix8
  have he : e₀ ∈ [1, 2, 6] := by
    rcases M755.ff_cases' e₀ he₀ hfixV hcount with h | h | h <;> simp [h]
  refine ⟨hAS, ⟨e₀, he, hidx⟩, le_antisymm (hDle.trans_eq (C.card_ΦX E hUαH)) ?_⟩

  rw [← C.card_ΦX E hUαH, card_eq_idx hAS, h8]
  have h1 : Nat.card (C.θX e D) ≤ 8 := hcθ.trans hfix8.le
  have h2 : 8 ≤ (C.θX e D).index := by
    by_contra hlt
    push Not at hlt
    have : Nat.card (C.θX e D) * (C.θX e D).index < 8 * 8 :=
      Nat.mul_lt_mul_of_le_of_lt h1 hlt (by omega)
    omega
  exact h2.trans hθle

theorem heq_of_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hG : M755.G2Facts) (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4)
    (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    (h13314 : A6.Stmt13_3_14_F4) (h1222 : Stmt12_2_2_F4) {γ γ' : F8.Geom T L (hz T V)}
    {g k : ↥((L ⊔ T) ⊔ hz T V)} (N : Not1471 T L V (hz T V) γ γ' g k) :
    mIdx (F8.Uγ V (hz T V) (g : G)) (F8.Dγ V (fsuV1 T V) (hz T V) (g : G)) =
      mIdx (conjClosure V (hz T V)) (F8.DH V (fsuV1 T V) (hz T V) (g : G)) := by
  obtain ⟨-, -, heq⟩ := C.caseI_F4 E hG h13322 hMod hVL hV₂ h13314 h1222 N
  have hF := C.hF98
  have hUp : IsPGroup 2 ↥(conjClosure V (hz T V)) := isPGroup_of_isElemAbelian hF.F911_3
  have hUγp : IsPGroup 2 ↥(F8.Uγ V (hz T V) (g : G)) := by
    rw [F8.Uγ]
    exact F7.isPGroup_conjSub hUp
  have hUk : conjSub (k : G) (conjClosure V (hz T V)) = conjClosure V (hz T V) :=
    conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V _ N.mem)
  rw [N.D_eq, ← hUk, relIndex_conjSub, hUk, ← N.Dγ_conj C, ← (Not1471.uα_eq' (g := g) (k := k)),
    relIndex_conjSub, HypF98.relIndex_eq_two_pow_mIdx hUp,
    HypF98.relIndex_eq_two_pow_mIdx hUγp] at heq
  exact (Nat.pow_right_injective (le_refl 2) heq).symm

theorem exists_A0_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hG : M755.G2Facts) (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4)
    (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    (h13314 : A6.Stmt13_3_14_F4) (h1222 : Stmt12_2_2_F4) {γ γ' : F8.Geom T L (hz T V)}
    {g k : ↥((L ⊔ T) ⊔ hz T V)} (N : Not1471 T L V (hz T V) γ γ' g k) :
    ∃ l ∈ L, l ∈ hz T V ∧ ∀ i,
      i ∈ idx (C.ΦX E (conjSub (l * ((k : G) * g)) (conjClosure V (hz T V)))) ↔
        i ∈ [0, 2, 4, 6, 8, 10, 12, 14] := by
  set x := (k : G) * g with hx
  obtain ⟨hAS, ⟨e₀, he₀, hidx⟩, -⟩ := C.caseI_F4 E hG h13322 hMod hVL hV₂ h13314 h1222 N
  have hcE : M755.centerE e₀ ∈ [8, 32, 40] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he₀
    rcases he₀ with rfl | rfl | rfl <;> decide
  have hcQ : M755.centerE e₀ ∈ M755.qCodes := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcE
    rcases hcE with h | h | h <;> rw [h] <;> decide
  obtain ⟨v, hv, hv1, hθv⟩ := C.exists_V_θG_F4 E hMod hVL hV₂ hcE
  obtain ⟨l₀, hl₀L, hl₀H, hl₀θ⟩ := C.exists_l_of_V_F4 E h13322 hMod hVL hV₂ hv hv1
  have N' := N.mul_left C.hF98 (inv_mem hl₀L) (inv_mem hl₀H)
  have hx' : ((⟨l₀⁻¹, Subgroup.mem_sup_left (Subgroup.mem_sup_left (inv_mem hl₀L))⟩ * k :
      ↥((L ⊔ T) ⊔ hz T V)) : G) * g = l₀⁻¹ * x := by
    rw [Subgroup.coe_mul, mul_assoc]
  obtain ⟨hAS', ⟨e₁, he₁, hidx'⟩, -⟩ := C.caseI_F4 E hG h13322 hMod hVL hV₂ h13314 h1222 N'
  rw [hx'] at hAS' hidx'
  refine ⟨l₀⁻¹, inv_mem hl₀L, inv_mem hl₀H, fun i => ?_⟩

  have hUαH := N.uα_le_hz C
  have hUαH' := N'.uα_le_hz C
  rw [hx'] at hUαH'
  have hl₀H' := inv_mem hl₀H
  have hcen := (M755.isCenterQ_iff hAS he₀ hidx hcQ).2 rfl
  have hcen' := M755.isCenterQ_conj (B := C.ΦX E (conjSub x (conjClosure V (hz T V))))
    (B' := C.ΦX E (conjSub (l₀⁻¹ * x) (conjClosure V (hz T V)))) (g := (C.ΦG E l₀)⁻¹)
    (fun b' hb' => by
      obtain ⟨u', hu', rfl⟩ := (C.mem_ΦX E hUαH').1 hb'
      rw [C.mem_ΦX E hUαH, inv_inv]
      have hu'' : l₀ * u' * l₀⁻¹ ∈ conjSub x (conjClosure V (hz T V)) := by
        rw [conjSub_mul] at hu'
        have h1 := mem_conjSub.1 hu'
        rwa [inv_inv] at h1
      refine ⟨_, hu'', ?_⟩
      rw [C.ΦG_mul E (mul_mem hl₀H (hUαH' hu')) (inv_mem hl₀H), C.ΦG_mul E hl₀H (hUαH' hu'),
        C.ΦG_inv E hl₀H])
    (fun b hb => by
      obtain ⟨u, hu, rfl⟩ := (C.mem_ΦX E hUαH).1 hb
      rw [C.mem_ΦX E hUαH']
      have hu'' : l₀⁻¹ * u * l₀⁻¹⁻¹ ∈ conjSub (l₀⁻¹ * x) (conjClosure V (hz T V)) := by
        rw [conjSub_mul]
        exact mul_mem_conjSub hu
      refine ⟨_, hu'', ?_⟩
      rw [C.ΦG_mul E (mul_mem hl₀H' (hUαH hu)) (inv_mem hl₀H'), C.ΦG_mul E hl₀H' (hUαH hu),
        C.ΦG_inv E hl₀H', C.ΦG_inv E hl₀H, inv_inv])
    hcen
  have hp : g2QAct (ZMod 2) (C.ΦG E l₀)⁻¹ (M755.ptQ (M755.centerE e₀)) = M755.ptQ 8 := by
    rw [← hθv, ← hl₀θ, map_inv, MulAut.inv_apply_self]
  rw [hp] at hcen'
  have h8q : (8 : ℕ) ∈ M755.qCodes := by decide
  have he₁2 : e₁ = 2 := by
    have h1 := (M755.isCenterQ_iff hAS' he₁ hidx' h8q).1 hcen'
    have key : ∀ e ∈ [1, 2, 6], 8 = M755.centerE e → e = 2 := by decide
    exact key e₁ he₁ h1
  rw [hidx' i, he₁2]
  exact M755.sE8_two i

end Ctx753

end CFSG.Quasithin.H13.L32A
