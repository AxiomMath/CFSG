module

public import CFSG.Quasithin.H13.U3S1343
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.InternalSec
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

variable {T L V : Subgroup G}

theorem s134_comm_reduced_F4 (h1332 : Stmt13_3_2_F4) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (S : A6.Setting134 G T L V)
    (hHM : ∃ H : Subgroup G, InH T H ∧ ¬ H ≤ normalizer (L : Set G)) :
    ⁅reducedAggregate (L ⊔ T), L⁆ = V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := reducedAggregate (L ⊔ T) with hWdef
  have hred : IsTwoReducedIn (L ⊔ T) W := isTwoReducedIn_reducedAggregate (L ⊔ T)
  have hKW : L ≤ normalizer (W : Set G) := le_sup_left.trans hred.2.1
  obtain ⟨hWc, hcase⟩ := s134_b51Part1 hC58 h317 h56 S hHM
  obtain ⟨h5, -⟩ := h1332 G T L S.h13 L S.h13.faithful
  have hcard : Nat.card (autOn L W) ≤ 6048 :=
    (card_autOn_le_card_quot hKW (s134_pCoreOf_le_centralizer S)).trans (card_le_of_qt13Five h5)
  obtain ⟨hn3, hn4⟩ := not_case1iii_iv (J := ffJ (autOn (L ⊔ T) W)) hcard
  have hmap := map_commV_autOn hKW
  have hVW : V ≤ W := S.irr.1
  rcases hcase.2 with h1i | h1ii | h1iii | h1iv
  · exact eq_of_irrPlus hKW h1i.1 hVW S.irr.2.2.1 S.irr.2.2.2.1 S.irr.2.1
  ·
    exfalso
    have h0 := fixV_inf_commV_eq_bot_of_case1ii h1ii
    have hzW : S.zV ∈ W := hVW S.zV_mem_V
    have hzWL : S.zV ∈ ⁅W, L⁆ := by
      have : V ≤ ⁅W, L⁆ := by
        calc V = ⁅V, L⁆ := S.irr.2.2.2.1.symm
          _ ≤ ⁅W, L⁆ := commutator_mono hVW le_rfl
      exact this S.zV_mem_V
    have hmem : (⟨S.zV, hzW⟩ : ↥W) ∈ fixV (autOn L W) ⊓ commV (autOn L W) := by
      refine mem_inf.mpr ⟨mem_fixV.2 fun σ hσ => ?_, ?_⟩
      · obtain ⟨⟨g, hgN⟩, hgL, rfl⟩ := Setup.mem_autOn_iff.1 hσ
        apply Subtype.ext
        rw [coe_conjAct_apply]
        exact S.conj_zV ⟨g, S.frame.L_le hgL⟩
      · have h1 : S.zV ∈ (commV (autOn L W)).map W.subtype := hmap ▸ hzWL
        obtain ⟨y, hy, hyv⟩ := h1
        have : y = ⟨S.zV, hzW⟩ := Subtype.ext hyv
        exact this ▸ hy
    rw [h0, mem_bot] at hmem
    exact S.zV_ne_one (congrArg Subtype.val hmem)
  · exact (hn3 h1iii).elim
  · exact (hn4 h1iv).elim

theorem s134_comm_VZ_le_F4 (h1332 : Stmt13_3_2_F4) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (S : A6.Setting134 G T L V)
    (hHM : ∃ H : Subgroup G, InH T H ∧ ¬ H ≤ normalizer (L : Set G)) :
    VZ T (L ⊔ T) ≤ quasithinOmegaOneCenter T ⊔ V ∧ ⁅VZ T (L ⊔ T), L ⊔ T⁆ ≤ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := quasithinOmegaOneCenter T with hZdef
  set W := VZ T (L ⊔ T) with hWdef
  have hInH : InH T (L ⊔ T) := ⟨le_sup_right, S.h13.faithful.1.2.2.2⟩
  have hredW : IsTwoReducedIn (L ⊔ T) W :=
    C1GN.isTwoReducedIn_VZ (s134_charTwo_of_inH S hInH) (s134_sylow_LT S)
  have hWR : W ≤ reducedAggregate (L ⊔ T) := A7.le_reducedAggregate_of_isTwoReducedIn hredW
  have hWL : ⁅W, L⁆ ≤ V := by
    rw [← s134_comm_reduced_F4 h1332 hC58 h317 h56 S hHM]
    exact commutator_mono hWR le_rfl
  have hZW : Z ≤ W := le_conjClosure _ _
  have hZc : ∀ z ∈ Z, ∀ t ∈ T, t * z * t⁻¹ = z := fun z hz t ht => by
    rw [mem_centralizer_iff.mp (s134_Z_le_center T hz).2 t ht, mul_inv_cancel_right]
  have hLTN : L ⊔ T ≤ normalizer (V : Set G) := sup_le S.frame.L_le S.frame.T_le

  have ha : ∀ x ∈ L ⊔ T, ∀ z ∈ Z, x * z * x⁻¹ * z⁻¹ ∈ V := by
    intro x hx z hz
    obtain ⟨l, hl, t, ht, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer S.T_le_NL hx
    have h1 : l * t * z * (l * t)⁻¹ * z⁻¹ = l * z * l⁻¹ * z⁻¹ := by
      calc l * t * z * (l * t)⁻¹ * z⁻¹ = l * (t * z * t⁻¹) * l⁻¹ * z⁻¹ := by group
        _ = l * z * l⁻¹ * z⁻¹ := by rw [hZc z hz t ht]
    rw [h1]
    have h2 : l * z * l⁻¹ * z⁻¹ = ⁅z, l⁆⁻¹ := by rw [commutatorElement_def]; group
    rw [h2]
    exact inv_mem (hWL (commutator_mem_commutator (hZW hz) hl))

  have hb : W ≤ Z ⊔ V := by
    refine conjClosure_le fun x hx z hz => ?_
    have e : x * z * x⁻¹ = (x * z * x⁻¹ * z⁻¹) * z := by group
    rw [e, sup_comm]
    exact mul_mem (mem_sup_left (ha x hx z hz)) (mem_sup_right hz)
  refine ⟨hb, ?_⟩

  have hZV : ∀ z ∈ Z, ∀ v ∈ V, z * v = v * z := fun z hz v hv =>
    (mem_centralizer_iff.mp (s134_Z_le_center T hz).2 v (S.V_le_T hv)).symm
  have hVZ : V ≤ normalizer (Z : Set G) := Vol2.Ch11.SecC.le_normalizer_of_commute hZV
  rw [commutator_le]
  intro w hw x hx
  obtain ⟨z, hz, v, hv, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hVZ (hb hw)
  have hxV : x * v⁻¹ * x⁻¹ ∈ V := (mem_normalizer_iff.mp (hLTN hx) v⁻¹).mp (inv_mem hv)
  have hzx : z * x * z⁻¹ * x⁻¹ ∈ V := by
    have : z * x * z⁻¹ * x⁻¹ = (x * z * x⁻¹ * z⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem (ha x hx z hz)
  have hcv : z * (v * (x * v⁻¹ * x⁻¹)) * z⁻¹ = v * (x * v⁻¹ * x⁻¹) := by
    rw [hZV z hz _ (mul_mem hv hxV), mul_inv_cancel_right]
  have e : ⁅z * v, x⁆ = z * (v * (x * v⁻¹ * x⁻¹)) * z⁻¹ * (z * x * z⁻¹ * x⁻¹) := by
    rw [commutatorElement_def]; group
  rw [e, hcv]
  exact mul_mem (mul_mem hv hxV) hzx

theorem s134_Z_eq_F4 (h1332 : Stmt13_3_2_F4) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (S : A6.Setting134 G T L V)
    (hHM : ∃ H : Subgroup G, InH T H ∧ ¬ H ≤ normalizer (L : Set G)) :
    quasithinOmegaOneCenter T =
      fsuV1 T V ⊔ quasithinOmegaOneCenter T ⊓ centralizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := quasithinOmegaOneCenter T with hZdef
  set W := VZ T (L ⊔ T) with hWdef
  obtain ⟨hb, hc⟩ := s134_comm_VZ_le_F4 h1332 hC58 h317 h56 S hHM
  have hInH : InH T (L ⊔ T) := ⟨le_sup_right, S.h13.faithful.1.2.2.2⟩
  have hredW : IsTwoReducedIn (L ⊔ T) W :=
    C1GN.isTwoReducedIn_VZ (s134_charTwo_of_inH S hInH) (s134_sylow_LT S)
  have hTZ : T ≤ centralizer (Z : Set G) := fun t ht => mem_centralizer_iff.mpr fun x hx =>
    (mem_centralizer_iff.mp (s134_Z_le_center T hx).2 t ht).symm
  have hdec := Vol2.Ch11.SecC.conjClosure_eq_commutator_sup
    (F7.isSylowTwoOf_odd_relIndex (s134_sylow_LT S)) hredW.2.2.1 hTZ
  refine le_antisymm (fun z hz => ?_) (sup_le inf_le_right inf_le_left)
  have hzW : z ∈ W := le_conjClosure _ _ hz
  have hWab := hredW.2.2.1
  have hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hWab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUW : ⁅W, L ⊔ T⁆ ≤ W :=
    le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjClosure _ _)
  have hBN : W ⊓ centralizer ((L ⊔ T : Subgroup G) : Set G) ≤
      normalizer ((⁅W, L ⊔ T⁆ : Subgroup G) : Set G) :=
    Vol2.Ch11.SecC.le_normalizer_of_commute fun a ha b hb => hcomm a (hUW ha) b hb.1
  have hdec' : W = ⁅W, L ⊔ T⁆ ⊔ W ⊓ centralizer ((L ⊔ T : Subgroup G) : Set G) := hdec
  have hz' : z ∈ ⁅W, L ⊔ T⁆ ⊔ W ⊓ centralizer ((L ⊔ T : Subgroup G) : Set G) := by
    rw [← hdec']; exact hzW
  obtain ⟨u, hu, c, hc', rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hBN hz'
  obtain ⟨hcW, hcC⟩ := mem_inf.mp hc'
  have hZV_T : Z ⊔ V ≤ T := sup_le (fun x hx => (s134_Z_le_center T hx).1) S.V_le_T
  have hcZ : c ∈ Z := by
    refine mem_quasithinOmegaOneCenter_iff.2 ⟨hZV_T (hb hcW), ?_, hWab.2 c hcW⟩
    exact centralizer_le (show (T : Set G) ⊆ ((L ⊔ T : Subgroup G) : Set G) from
      fun x hx => le_sup_right (a := L) hx) hcC
  have hcL : c ∈ centralizer (L : Set G) :=
    centralizer_le (show (L : Set G) ⊆ ((L ⊔ T : Subgroup G) : Set G) from
      fun x hx => le_sup_left (b := T) hx) hcC
  have huZ : u ∈ Z := by
    have : u = (u * c) * c⁻¹ := by group
    rw [this]
    exact mul_mem hz (inv_mem hcZ)
  exact mul_mem (mem_sup_left (mem_inf.mpr ⟨hc hu, huZ⟩))
    (mem_sup_right (mem_inf.mpr ⟨hcZ, hcL⟩))

theorem s134_card_Z_F4 (h1332 : Stmt13_3_2_F4) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (S : A6.Setting134 G T L V)
    (hHM : ∃ H : Subgroup G, InH T H ∧ ¬ H ≤ normalizer (L : Set G)) :
    Nat.card ↥(quasithinOmegaOneCenter T) =
      2 * Nat.card ↥(quasithinOmegaOneCenter T ⊓ centralizer (L : Set G)) := by
  set Z := quasithinOmegaOneCenter T with hZdef
  set ZL := Z ⊓ centralizer (L : Set G) with hZLdef
  have hZ := s134_Z_eq_F4 h1332 hC58 h317 h56 S hHM
  have hV1Z : fsuV1 T V ≤ Z := inf_le_right
  have hZLZ : ZL ≤ Z := inf_le_left

  have hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    mem_centralizer_iff.mp (s134_Z_le_center T hb).2 a (s134_Z_le_center T ha).1
  have : IsMulCommutative ↥Z := ⟨⟨fun a b => Subtype.ext (hZc a a.2 b b.2)⟩⟩
  have hN : (ZL.subgroupOf Z).Normal := normal_of_isMulCommutative _

  have h1 : ZL.relIndex Z = ZL.relIndex (fsuV1 T V) := by
    have e1 : (fsuV1 T V).subgroupOf Z ⊔ ZL.subgroupOf Z = ⊤ := by
      rw [← subgroupOf_sup hV1Z hZLZ, ← hZ, subgroupOf_self]
    have h2 := relIndex_sup_right ((fsuV1 T V).subgroupOf Z) (ZL.subgroupOf Z)
    rw [e1, relIndex_subgroupOf hV1Z] at h2
    rw [← h2, relIndex_top_right]
    rfl

  have hZV1 : V ⊓ centralizer (L : Set G) ≤ fsuV1 T V :=
    le_inf inf_le_left ((A6.Setting134.ZV_le_ZL S).trans inf_le_left)
  have h3 : ZL ⊓ fsuV1 T V = V ⊓ centralizer (L : Set G) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxZL, hxV1⟩ := mem_inf.1 hx
      exact mem_inf.2 ⟨(mem_inf.1 hxV1).1, (mem_inf.1 hxZL).2⟩
    · intro hx
      exact mem_inf.2 ⟨A6.Setting134.ZV_le_ZL S hx, hZV1 hx⟩
  have h4 : ZL.relIndex (fsuV1 T V) = 2 := by
    rw [← inf_relIndex_right, h3]
    have h5 := relIndex_mul_card (V ⊓ centralizer (L : Set G)) (fsuV1 T V)
    rw [inf_eq_left.2 hZV1, S.card_ZV, S.card_V1] at h5
    omega
  have h6 := relIndex_mul_card ZL Z
  rw [inf_eq_left.2 hZLZ, h1, h4] at h6
  exact h6.symm

theorem s134_L1_le_centralizer_Z_F4 (h1332 : Stmt13_3_2_F4) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (S : A6.Setting134 G T L V)
    (hHM : ∃ H : Subgroup G, InH T H ∧ ¬ H ≤ normalizer (L : Set G)) :
    L₁Of L (fsuV1 T V) ≤ centralizer (quasithinOmegaOneCenter T : Set G) := by
  intro x hx
  have hx' : x ∈ L ⊓ normalizer (fsuV1 T V : Set G) := oTwoRes_le _ hx
  obtain ⟨hxL, hxN⟩ := mem_inf.1 hx'
  have hxC := s134_centralizes_V1 S (S.frame.L_le hxL) hxN
  have hcomm : ∀ a ∈ fsuV1 T V, ∀ c ∈ quasithinOmegaOneCenter T ⊓ centralizer (L : Set G),
      a * c = c * a := by
    intro a ha c hc
    have haZ : a ∈ quasithinOmegaOneCenter T := (mem_inf.1 ha).2
    have hcZ : c ∈ quasithinOmegaOneCenter T := (mem_inf.1 hc).1
    exact mem_centralizer_iff.mp (s134_Z_le_center T hcZ).2 a (s134_Z_le_center T haZ).1
  rw [s134_Z_eq_F4 h1332 hC58 h317 h56 S hHM]
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨a, ha, c, hc, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer
    (Vol2.Ch11.SecC.le_normalizer_of_commute hcomm) hy
  have h1 : a * x = x * a := (mem_centralizer_iff.mp hxC) a ha
  have h2 : x * c = c * x := (mem_centralizer_iff.mp (mem_inf.1 hc).2) x hxL
  calc a * c * x = a * (x * c) := by rw [mul_assoc, h2]
    _ = x * (a * c) := by rw [← mul_assoc, h1, mul_assoc]

end CFSG.Quasithin.H13.U3
