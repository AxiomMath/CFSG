module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem20Four
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Basic
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.GH74.QTGen4.Leaves.Hyp6116Gen4

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

section Generic

variable {G : Type} [Group G]

theorem card_le_16 (hG : CFSG.GH74.Gen4 G) {E : Subgroup G} (hE : IsElemAbelian 2 E) :
    Nat.card E ≤ 16 := by
  have h := CFSG.GH74.SectionalTwoRankLE.card_le_of_elementary
    (show CFSG.GH74.SectionalTwoRankLE G 4 from hG) E hE
  norm_num at h
  exact h

theorem card_le_of_isElemAbelianMod [Finite G] (hG : CFSG.GH74.Gen4 G) {X Y : Subgroup G}
    (hYX : Y ≤ X) (hXY : IsElemAbelianMod X Y) : Nat.card X ≤ 16 * Nat.card Y := by
  have hN : (Y.subgroupOf X).Normal := by
    refine ⟨fun a ha b => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    have hc := (hXY b b.2 a a.2).1
    have e : ((b * a * b⁻¹ : X) : G) = ((b : G) * a * (b : G)⁻¹ * (a : G)⁻¹) * a := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e]
    exact Y.mul_mem hc ha
  have hQ : CFSG.GH74.Gen4 (↥X ⧸ Y.subgroupOf X) :=
    CFSG.GH74.Gen4.quotient _ (CFSG.GH74.Gen4.subgroup X hG)
  have hcomm : ∀ p q : ↥X ⧸ Y.subgroupOf X, p * q = q * p := by
    intro p q
    induction p using QuotientGroup.induction_on with
    | H a =>
      induction q using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have hc := (hXY ((b : G)⁻¹) (X.inv_mem b.2) ((a : G)⁻¹) (X.inv_mem a.2)).1
        have e : (((a * b)⁻¹ * (b * a) : X) : G) =
            (b : G)⁻¹ * (a : G)⁻¹ * ((b : G)⁻¹)⁻¹ * ((a : G)⁻¹)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
        rw [e]; exact hc
  have hsq : ∀ p : ↥X ⧸ Y.subgroupOf X, p ^ 2 = 1 := by
    intro p
    induction p using QuotientGroup.induction_on with
    | H a =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.coe_pow]
      exact (hXY a a.2 a a.2).2
  have hE : IsElemAbelian 2 (⊤ : Subgroup (↥X ⧸ Y.subgroupOf X)) :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm a b)⟩⟩, fun q _ => hsq q⟩
  have hc := card_le_16 hQ hE
  rw [Subgroup.card_top] at hc
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Y.subgroupOf X)
  have h2 : Nat.card (Y.subgroupOf X) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX).toEquiv
  rw [h1, h2]
  exact Nat.mul_le_mul_right _ hc

end Generic

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

theorem card_facts (hG : CFSG.GH74.Gen4 G) (h : Hyp611Nat G T M L V n) :
    n = 2 ∧ Nat.card V = 16 ∧ Nat.card (ch6ZS T L V) = 4 := by
  have hV := h.natural.card_eq
  have h16 := card_le_16 hG h.toHyp611.isElemAbelian
  have hn2 := h.two_le
  have hn : n = 2 := by
    rcases Nat.lt_or_ge n 3 with hlt | hge
    · omega
    · exfalso
      have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hge
      rw [hV] at h16
      nlinarith
  subst hn
  exact ⟨rfl, hV.trans (by norm_num), h.card_ZS.trans (by norm_num)⟩

theorem U_le_S (h : Hyp6116 G T M L V n) :
    conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ≤ ch6S T L V :=
  (conjClosure_mono le_rfl le_sup_left).trans
    ((h.conjClosure_le_pCoreOf h.isInHS_sup).trans (h.pCoreOf_le_S h.isInHS_sup))

theorem isElemAbelianMod_U (h : Hyp6116 G T M L V n) :
    IsElemAbelianMod (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)))
      (ch6ZS T L V) :=
  fun u hu w hw => h.isElemAbelianMod h.isInHS_sup u (conjClosure_mono le_rfl le_sup_left hu) w
    (conjClosure_mono le_rfl le_sup_left hw)

theorem mem_normalizer_of_conjSub_eq {b : G} (e : conjSub b V = V) :
    b ∈ Subgroup.normalizer (V : Set G) := by
  have e' : conjSubgroup V b⁻¹ = V := by
    show conjSub b⁻¹⁻¹ V = V
    rw [inv_inv]; exact e
  have := Subgroup.inv_mem _ (conjSubgroup_eq_iff_mem_normalizer.mp e')
  rwa [inv_inv] at this

theorem exists_noncomm (hG : CFSG.GH74.Gen4 G) (h : Hyp6116 G T M L V n)
    (hNV : Subgroup.normalizer (V : Set G) ≤ M) :
    ∃ x ∈ Subgroup.centralizer (ch6ZS T L V : Set G), ⁅V, conjSub x V⁆ ≠ ⊥ := by
  obtain ⟨-, hV16, -⟩ := card_facts hG h.toHyp611Nat
  by_contra hall
  push Not at hall
  apply h.not_le
  intro x hx
  apply hNV
  have hVab := h.toHyp611.isElemAbelian
  have hWab : IsElemAbelian 2 (conjSub x V) := hVab.map (MulAut.conj x).toMonoidHom
  have hcomm : ∀ a ∈ V, ∀ b ∈ conjSub x V, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hall x hx) ha) b hb).symm
  have h1 := card_le_16 hG (IsElemAbelian.sup_of_commute hVab hWab hcomm)
  have heq : V = V ⊔ conjSub x V := Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
  have hle : conjSub x V ≤ V :=
    calc conjSub x V ≤ V ⊔ conjSub x V := le_sup_right
      _ = V := heq.symm
  exact mem_normalizer_of_conjSub_eq
    (Subgroup.eq_of_le_of_card_ge hle (card_conjSub' x V).ge)

theorem false_of_noncomm (hG : CFSG.GH74.Gen4 G) (h : Hyp6116 G T M L V n) {x : G}
    (hx : x ∈ Subgroup.centralizer (ch6ZS T L V : Set G)) (hne : ⁅V, conjSub x V⁆ ≠ ⊥) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨rfl, hV16, hZ4⟩ := card_facts hG h.toHyp611Nat
  have hEM := isElemAbelianMod_U h
  have hUS := U_le_S h
  set Z := ch6ZS T L V with hZ
  set U := conjClosure V (Subgroup.centralizer (Z : Set G)) with hU
  set W := conjSub x V with hW
  have hVab : IsElemAbelian 2 V := h.toHyp611.isElemAbelian
  have hWab : IsElemAbelian 2 W := hVab.map (MulAut.conj x).toMonoidHom
  have hW16 : Nat.card W = 16 := (card_conjSub' x V).trans hV16
  have hUN : U ≤ Subgroup.normalizer (V : Set G) :=
    hUS.trans (inf_le_left.trans h.toHyp611.T_le_normalizer)
  have hWU : W ≤ U := Hyp6116.conjSub_le_conjClosure hx
  have hWS : W ≤ ch6S T L V := hWU.trans hUS
  have hWN : W ≤ Subgroup.normalizer (V : Set G) := hWU.trans hUN
  have hVU : V ≤ U := le_conjClosure V _
  have hZV : Z ≤ V := inf_le_left
  have hZW : Z ≤ W := by
    intro z hz
    refine Subgroup.mem_map.mpr ⟨z, hZV hz, ?_⟩
    have hc : z * x = x * z := Subgroup.mem_centralizer_iff.mp hx z hz
    show x * z * x⁻¹ = z
    rw [← hc]; group
  have hcZ : ⁅V, W⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro v hv w hw
    exact (hEM v (hVU hv) w (hWU hw)).1
  have hCWV : W ⊓ Subgroup.centralizer (V : Set G) ≤ V := by
    have hab : IsElemAbelian 2 (W ⊓ Subgroup.centralizer (V : Set G)) :=
      ⟨⟨⟨fun a b => Subtype.ext (B2F.isElemAbelian_comm hWab a.2.1 b.2.1)⟩⟩,
        fun y hy => hWab.2 y hy.1⟩
    have hsup := IsElemAbelian.sup_of_commute hVab hab (fun a ha b hb =>
      Subgroup.mem_centralizer_iff.mp hb.2 a ha)
    have h1 := card_le_16 hG hsup
    have heq : V = V ⊔ (W ⊓ Subgroup.centralizer (V : Set G)) :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
    calc W ⊓ Subgroup.centralizer (V : Set G) ≤ V ⊔ (W ⊓ Subgroup.centralizer (V : Set G)) :=
          le_sup_right
      _ = V := heq.symm
  obtain ⟨w0, hw0W, hw0V⟩ : ∃ w ∈ W, w ∉ Subgroup.centralizer (V : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact ((Subgroup.mem_centralizer_iff.mp (hcon w hw)) v hv).symm
  have hCV0 : V ⊓ Subgroup.centralizer ({w0} : Set G) = Z :=
    h.toHyp611Nat.centralizer_singleton_eq_ZS (hWS hw0W) hw0V
  have hVW : V ⊓ W = Z := by
    apply le_antisymm
    · intro y hy
      rw [← hCV0]
      exact ⟨hy.1, Subgroup.mem_centralizer_singleton_iff.mpr
        (B2F.isElemAbelian_comm hWab hy.2 hw0W)⟩
    · exact le_inf hZV hZW
  have hCW : W ⊓ Subgroup.centralizer (V : Set G) = Z := by
    apply le_antisymm
    · intro y hy
      rw [← hVW]
      exact ⟨hCWV hy, hy.1⟩
    · exact le_inf hZW (fun z hz => Subgroup.mem_centralizer_iff.mpr fun y hy =>
        B2F.isElemAbelian_comm hVab hy (hZV hz))
  have hidx : V.relIndex (W ⊔ V) = V.relIndex W := relIndex_sup_eq_relIndex_of_le_normalizer hWN
  have hrel : V.relIndex W = 4 := by
    have h1 := card_mul_relIndex_of_le (inf_le_right : V ⊓ W ≤ W)
    rw [Subgroup.inf_relIndex_right, hVW, hZ4, hW16] at h1
    omega
  have hsup64 : Nat.card ↥(W ⊔ V) = 64 := by
    have h1 := card_mul_relIndex_of_le (le_sup_right : V ≤ W ⊔ V)
    rw [hidx, hrel, hV16] at h1
    omega
  have hU64 : Nat.card U ≤ 64 := by
    have := card_le_of_isElemAbelianMod hG (hZV.trans hVU) hEM
    rw [hZ4] at this
    omega
  have hUeq : W ⊔ V = U := Subgroup.eq_of_le_of_card_ge (sup_le hWU hVU) (by omega)
  have hinv : ∀ y ∈ V ⊔ W, y ^ 2 = 1 → y ∈ V ∨ y ∈ W := by
    intro y hy hy2
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hWN] at hy
    obtain ⟨v, hv, w, hw, rfl⟩ := hy
    by_cases hwZ : w ∈ Z
    · exact Or.inl (V.mul_mem hv (hZV hwZ))
    by_cases hvZ : v ∈ Z
    · exact Or.inr (W.mul_mem (hZW hvZ) hw)
    exfalso
    have hwV : w ∉ Subgroup.centralizer (V : Set G) := fun hwc => hwZ (hCW ▸ ⟨hw, hwc⟩)
    have hCV : V ⊓ Subgroup.centralizer ({w} : Set G) = Z :=
      h.toHyp611Nat.centralizer_singleton_eq_ZS (hWS hw) hwV
    have hvw : v * w ≠ w * v := by
      intro e
      apply hvZ
      rw [← hCV]
      exact ⟨hv, Subgroup.mem_centralizer_singleton_iff.mpr e⟩
    have hc : w * v * w⁻¹ * v⁻¹ ∈ Z := by
      have := Subgroup.commutator_mem_commutator hw hv
      rw [Subgroup.commutator_comm] at this
      exact hcZ this
    have hcv : (w * v * w⁻¹ * v⁻¹) * v = v * (w * v * w⁻¹ * v⁻¹) :=
      B2F.isElemAbelian_comm hVab (hZV hc) hv
    have hv2 : v * v = 1 := by rw [← pow_two]; exact hVab.2 v hv
    have hw2 : w * w = 1 := by rw [← pow_two]; exact hWab.2 w hw
    apply hvw
    have hsq : (v * w) ^ 2 = w * v * w⁻¹ * v⁻¹ := by
      calc (v * w) ^ 2 = v * (w * v * w⁻¹ * v⁻¹ * v * w) * w := by rw [pow_two]; group
        _ = v * (v * (w * v * w⁻¹ * v⁻¹) * w) * w := by rw [hcv]
        _ = (v * v) * (w * v * w⁻¹ * v⁻¹) * (w * w) := by group
        _ = w * v * w⁻¹ * v⁻¹ := by rw [hv2, hw2]; group
    rw [hsq] at hy2
    calc v * w = (w * v * w⁻¹ * v⁻¹)⁻¹ * (w * v) := by group
      _ = w * v := by rw [hy2, inv_one, one_mul]
  have hleor : ∀ A : Subgroup G, A ≤ V ⊔ W → IsElemAbelian 2 A → A ≤ V ∨ A ≤ W := by
    intro A hA hAel
    by_contra hcon
    push Not at hcon
    obtain ⟨a, haA, haV⟩ := Set.not_subset.mp hcon.1
    obtain ⟨b, hbA, hbW⟩ := Set.not_subset.mp hcon.2
    have haW : a ∈ W := (hinv a (hA haA) (hAel.2 a haA)).resolve_left haV
    have hbV : b ∈ V := (hinv b (hA hbA) (hAel.2 b hbA)).resolve_right hbW
    rcases hinv (a * b) (hA (A.mul_mem haA hbA)) (hAel.2 _ (A.mul_mem haA hbA)) with hab | hab
    · apply haV
      have e : a = (a * b) * b⁻¹ := by group
      rw [e]
      exact V.mul_mem hab (V.inv_mem hbV)
    · apply hbW
      have e : b = a⁻¹ * (a * b) := by group
      rw [e]
      exact W.mul_mem (W.inv_mem haW) hab
  have horb : ∀ i ∈ Subgroup.centralizer (Z : Set G), conjSub i V = V ∨ conjSub i V = W := by
    intro i hi
    have hiU : conjSub i V ≤ V ⊔ W := by
      rw [sup_comm, hUeq]; exact Hyp6116.conjSub_le_conjClosure hi
    rcases hleor _ hiU (hVab.map (MulAut.conj i).toMonoidHom) with hle | hle
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge hle (card_conjSub' i V).ge)
    · exact Or.inr (Subgroup.eq_of_le_of_card_ge hle (by have := card_conjSub' i V; omega))
  have hWV : W ≠ V := by
    intro e
    apply hne
    rw [e]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun a ha =>
      Subgroup.mem_centralizer_iff.mpr fun b hb => B2F.isElemAbelian_comm hVab hb ha
  have hidx2 : ((Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (Z : Set G)).subgroupOf
      (Subgroup.centralizer (Z : Set G))).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨x, hx⟩, fun b => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    have hb : (b : G) ∈ Subgroup.centralizer (Z : Set G) := b.2
    have hbx : (b : G) * x ∈ Subgroup.centralizer (Z : Set G) := Subgroup.mul_mem _ hb hx
    have hmul : conjSub ((b : G) * x) V = conjSub (b : G) W := conjSub_mul _ _ _
    rcases horb b hb with hb1 | hb1
    · have hbN : (b : G) ∈ Subgroup.normalizer (V : Set G) := mem_normalizer_of_conjSub_eq hb1
      refine Or.inr ⟨⟨hbN, hb⟩, fun hbxN => ?_⟩
      have h1 : conjSub (b : G) W = V := by
        rw [← hmul]; exact conjSub_eq_of_mem_normalizer' hbxN.1
      have h2 := congrArg (conjSub (b : G)⁻¹) (h1.trans hb1.symm)
      rw [conjSub_conjSub_inv, conjSub_conjSub_inv] at h2
      exact hWV h2
    · have hbN : (b : G) ∉ Subgroup.normalizer (V : Set G) := fun hbn =>
        hWV (hb1.symm.trans (conjSub_eq_of_mem_normalizer' hbn))
      refine Or.inl ⟨⟨?_, hbx⟩, fun hbn => hbN hbn.1⟩
      rcases horb _ hbx with h3 | h3
      · exact mem_normalizer_of_conjSub_eq h3
      · exfalso
        have h4 : conjSub (b : G) W = conjSub (b : G) V := by rw [← hmul, h3, hb1]
        have h5 := congrArg (conjSub (b : G)⁻¹) h4
        rw [conjSub_conjSub_inv, conjSub_conjSub_inv] at h5
        exact hWV h5
  obtain ⟨hSI, -, hSidx⟩ := h.toHyp611Nat.isSylowIn_S
  have hSN : ch6S T L V ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (Z : Set G) :=
    le_inf (inf_le_left.trans h.toHyp611.T_le_normalizer) hSI
  apply hSidx
  have hm := Subgroup.relIndex_mul_relIndex (ch6S T L V)
    (Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (Z : Set G))
    (Subgroup.centralizer (Z : Set G)) hSN inf_le_right
  have h2 : (Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (Z : Set G)).relIndex
      (Subgroup.centralizer (Z : Set G)) = 2 := hidx2
  show 2 ∣ (ch6S T L V).relIndex (Subgroup.centralizer (Z : Set G))
  rw [← hm, h2]
  exact dvd_mul_left _ _

end CFSG.GH74.QTGen4.Leaves.Hyp6116Gen4

namespace CFSG.GH74.QTGen4.Leaves.Hyp6116Gen4

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Open

theorem hno_F4 (h432 : Stmt4_3_2_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (n : ℕ),
      Hyp6116 G T M L V n → False := by
  intro G _ _ T M L V n h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG : CFSG.GH74.Gen4 G := CFSG.GH74.QTGen4.Finite4.gen4 (G := G)
  have hNV : Subgroup.normalizer (V : Set G) ≤ M :=
    le_of_isUniqueM_of_le_twoLocal (h.toHyp611.isUniqueM_F4 h432) h.toHyp611.sup_le_normalizer
      ⟨V, h.toHyp611.ne_bot, B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian, rfl⟩
  obtain ⟨x, hx, hne⟩ := exists_noncomm hG h hNV
  exact false_of_noncomm hG h hx hne

end CFSG.GH74.QTGen4.Leaves.Hyp6116Gen4
