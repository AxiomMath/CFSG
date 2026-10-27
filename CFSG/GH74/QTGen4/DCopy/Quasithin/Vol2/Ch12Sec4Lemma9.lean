module

public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma9
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4Post
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4Pre

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem lemma12_4_9_of_F4
    (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (hpre : Pre1242_F4)
    (h12210 : Stmt12_2_10_F4) (h1247 : Lemma12_4_7_F4) (hB46 : B46OffenderCommEqFix) :
    Lemma12_4_9_F4 := by
  intro G _ _ T L V hcx hq g hAN hne hVA
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hcx.hyp
  obtain ⟨z, hz2, hzeq, hMz, hMV⟩ := post1244_core_F4 h331 h1222 hpre hcx hq
  obtain ⟨hc, hcases⟩ := modules_cases_of_hyp1223_F4 h1222 hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hcomm : ⁅V, L⁆ = V := hyp.irrPlus.2.2.2.1
  have hV1 : V ≠ ⊥ := hyp.irrPlus.2.1
  have hVLT : V ≤ L ⊔ T := hVT.trans le_sup_right
  have hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_isPrimeReduced_sup hyp.normalizes hVLT hred
  have hVp : IsPGroup 2 V := hyp.sylow.1.to_le hVT
  have hsq : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    have h1 := hred.isElementaryAbelian
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V.subgroupOf (L ⊔ T))
      (⟨v, hVLT hv⟩ : ↥(L ⊔ T)) (Subgroup.mem_subgroupOf.mpr hv)
    simpa using congrArg Subtype.val h2
  have hVel : IsElemAbelian 2 V := ⟨hc, hsq⟩
  have hab : V ≤ Subgroup.centralizer (V : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy =>
      congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : ↥V) ⟨x, hx⟩)
  have hnc : ¬ L ≤ Subgroup.centralizer (V : Set G) := by
    intro h
    apply hV1
    rw [← hcomm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mpr h)
  have hzZ : z ∈ V ⊓ Subgroup.centralizer (L : Set G) := hzeq ▸ Subgroup.mem_zpowers z
  have hZ2 : Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) = 2 := by
    rw [hzeq, Nat.card_zpowers, hz2]
  have hcommGr : commV (autOn L V) = ⊤ := commV_autOn_eq_top hLV hcomm
  have hfixGr : Nat.card (fixV (autOn L V)) = 2 := by
    rw [fixV_autOn_eq hLV, card_subgroupOf_eq_card_inf, hZ2]

  have hweak : ∀ h : G, z ∈ CFSG.conjugate V h → h ∈ Subgroup.normalizer (V : Set G) := by
    intro h hzh
    have h1 : (h⁻¹)⁻¹ * z * h⁻¹ ∈ V := by
      rw [inv_inv]
      exact mem_conjugate_iff_mul_mem.1 hzh
    obtain ⟨l, hl, hle⟩ := h1247 G T L V hcx hq z hzZ.1 h⁻¹ h1
    have hlz : l⁻¹ * z * l = z := by
      have h2 := Subgroup.mem_centralizer_iff.1 hzZ.2 l hl
      rw [mul_assoc, ← h2]
      group
    rw [hlz, inv_inv] at hle
    have hhz : h ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc h * z = h * z * h⁻¹ * h := by group
        _ = z * h := by rw [← hle]
    rw [← hMV, hMz]
    exact hhz

  have hAel : IsElemAbelian 2 (CFSG.conjugate V g) := E3.isElemAbelian_conjSubgroup hVel g
  have hBel : IsElemAbelian 2 (CFSG.conjugate V g⁻¹) := E3.isElemAbelian_conjSubgroup hVel g⁻¹
  have hAcard : Nat.card (CFSG.conjugate V g) = Nat.card V := card_conjugate_eq V g
  have hBcard : Nat.card (CFSG.conjugate V g⁻¹) = Nat.card V := card_conjugate_eq V g⁻¹
  have hBN : CFSG.conjugate V g⁻¹ ≤ Subgroup.normalizer (V : Set G) := by
    have h1 := conjugate_le_normalizer_conjugate hVA g⁻¹
    rwa [conjugate_conjugate_inv'] at h1
  have hVB : V ≤ Subgroup.normalizer (CFSG.conjugate V g⁻¹ : Set G) := by
    have h1 := conjugate_le_normalizer_conjugate hAN g⁻¹
    rwa [conjugate_conjugate_inv'] at h1
  have hneA : ¬ CFSG.conjugate V g ≤ Subgroup.centralizer (V : Set G) := fun h =>
    hne (Subgroup.commutator_eq_bot_iff_le_centralizer.2 h)
  have hneB : ¬ CFSG.conjugate V g⁻¹ ≤ Subgroup.centralizer (V : Set G) := by
    intro h
    have h1 := conjugate_le_centralizer_conjugate h g
    rw [conjugate_inv_conjugate'] at h1
    exact hneA (Subgroup.le_centralizer_iff.1 h1)

  have hcB1 : Nat.card ↥(CFSG.conjugate V g⁻¹ ⊓ Subgroup.centralizer (V : Set G)) =
      Nat.card ↥(V ⊓ Subgroup.centralizer (CFSG.conjugate V g : Set G)) := by
    rw [← card_conjugate_eq (V ⊓ Subgroup.centralizer (CFSG.conjugate V g : Set G)) g⁻¹,
      conjugate_inf_centralizer, conjugate_conjugate_inv']
  have hcB2 : Nat.card ↥(V ⊓ Subgroup.centralizer (CFSG.conjugate V g⁻¹ : Set G)) =
      Nat.card ↥(CFSG.conjugate V g ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [← card_conjugate_eq (CFSG.conjugate V g ⊓ Subgroup.centralizer (V : Set G)) g⁻¹,
      conjugate_inf_centralizer, conjugate_conjugate_inv']

  have hside : ∀ X : Subgroup G, IsElemAbelian 2 X → X ≤ Subgroup.normalizer (V : Set G) →
      ¬ X ≤ Subgroup.centralizer (V : Set G) → Nat.card X = Nat.card V →
      Nat.card ↥(X ⊓ Subgroup.centralizer (V : Set G)) ≤
        Nat.card ↥(V ⊓ Subgroup.centralizer (X : Set G)) → z ∈ ⁅V, X⁆ := by
    intro X hXel hXN hXne hXcard hXle
    have hXL : X ≤ Subgroup.normalizer (L : Set G) := hXN.trans hMV.symm.le
    rcases hq with h3' | hU
    ·
      obtain ⟨e⟩ := h3'
      have hs3 : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
        have := (isSimpleGroup_sl_zmod_two (m := 3) (by norm_num)).1
        exact e.isSimpleGroup
      have h168 := card_quot_of_sl_three ⟨e⟩
      obtain ⟨eA⟩ := nonempty_autOn_mulEquiv_quotient hLV hO2 hs3 hnc
      have hGrs : IsSimpleGroup (autOn L V) := eA.isSimpleGroup
      have hGr : Nat.card (autOn L V) = 168 := by rw [Nat.card_congr eA.toEquiv, h168]

      have hV16 : Nat.card V = 2 ^ 4 := by
        have hle := hcases.1 ⟨e⟩
        have hidx := four_lt_relIndex_of_simple hLV hcomm hnc hO2 hs3 (by rw [h168]; norm_num)
        have h1 := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (L : Set G)) V
        rw [inf_eq_left.2 (inf_le_left : V ⊓ Subgroup.centralizer (L : Set G) ≤ V), hZ2] at h1
        have h2 := E3.relIndex_eq_two_pow hVp (V ⊓ Subgroup.centralizer (L : Set G))
        rw [h2] at hidx h1
        have hm : 3 ≤ E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) := by
          by_contra hm
          push Not at hm
          interval_cases (E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G))) <;>
            norm_num at hidx
        have h8 : 8 ≤ 2 ^ E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) :=
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hm
        rw [show (2 : ℕ) ^ 4 = 16 by norm_num] at hle ⊢
        omega
      have hnat := binaryNaturalSL_of_card_sixteen
        (fun w : ↥V => Subtype.ext (by simpa using hsq w w.2)) hV16 hGrs hGr hcommGr hfixGr
      exact mem_commutator_of_l3 hsq hV16 hLV hnat hcommGr hzZ.1 hzZ.2 hXN hXL hXel hXne
    ·
      have hsU : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
        CFSG.Timmesfeld.isSimpleGroup_of_lieModel hU
      obtain ⟨eA⟩ := nonempty_autOn_mulEquiv_quotient hLV hO2 hsU hnc
      have hGrs : IsSimpleGroup (autOn L V) := eA.isSimpleGroup

      have hZL : autOn L V ⊓ Subgroup.centralizer (autOn L V : Set (MulAut ↥V)) = ⊥ := by
        have hnab : ¬ ∀ a b : autOn L V, a * b = b * a := by
          intro hall'
          obtain ⟨-, -, a, b, hab'⟩ := hyp.quasisimple
          apply hab'
          obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
          obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
          have h1 : a' * b' = b' * a' := eA.symm.injective (by
            rw [map_mul, map_mul]
            exact hall' _ _)
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h1]
        have hnorm : ((Subgroup.centralizer (autOn L V : Set (MulAut ↥V))).subgroupOf
            (autOn L V)).Normal := by
          refine ⟨fun n hn x => ?_⟩
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hn ⊢
          intro y hy
          have h1 := hn y hy
          have h2 := hn (x : MulAut ↥V) x.2
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          calc y * (↑x * ↑n * (↑x)⁻¹) = y * (↑n * ↑x * (↑x)⁻¹) := by rw [← h2]
            _ = y * n := by group
            _ = n * y := h1
            _ = ↑n * ↑x * (↑x)⁻¹ * y := by group
            _ = ↑x * ↑n * (↑x)⁻¹ * y := by rw [h2]
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Subgroup.centralizer
            (autOn L V : Set (MulAut ↥V))).subgroupOf (autOn L V)) with hb | ht
        · refine eq_bot_iff.2 fun y hy => ?_
          have h1 : (⟨y, hy.1⟩ : autOn L V) ∈ (Subgroup.centralizer
              (autOn L V : Set (MulAut ↥V))).subgroupOf (autOn L V) :=
            Subgroup.mem_subgroupOf.2 hy.2
          rw [hb, Subgroup.mem_bot] at h1
          exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)
        · exfalso
          apply hnab
          intro a b
          have h1 : a ∈ (Subgroup.centralizer (autOn L V : Set (MulAut ↥V))).subgroupOf
              (autOn L V) := ht ▸ Subgroup.mem_top a
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
          exact Subtype.ext (h1 b b.2).symm
      have hMC : autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V ⊓
          Subgroup.centralizer (autOn L V : Set (MulAut ↥V)) = ⊥ := by
        have h1 := (h12210 G T L V hyp).1
        exact h1.trans hZL
      have hnat : G2NaturalDerived (autOn L V) ⊤ (fixV (autOn L V)) 1 := by
        rw [fixV_autOn_eq hLV]
        exact hcases.2.1 hU
      have hzM : z ∈ Subgroup.centralizer
          ((Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) :
            Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro m hm
        have h1 : m ∈ Subgroup.centralizer ({z} : Set G) := by
          rw [← hMz]
          exact hm.1
        exact Subgroup.mem_centralizer_singleton_iff.1 h1
      exact mem_commutator_of_g2 hB46 hsq (le_inf Subgroup.le_normalizer hLV) inf_le_right
        inf_le_left hMC hcommGr hnat hzZ.1 hzM (le_inf hXL hXN) hXel hXne hXcard hXle

  have hgN : g ∈ Subgroup.normalizer (V : Set G) := by
    rcases le_total (Nat.card ↥(CFSG.conjugate V g ⊓ Subgroup.centralizer (V : Set G)))
        (Nat.card ↥(V ⊓ Subgroup.centralizer (CFSG.conjugate V g : Set G))) with hle | hle
    · have hz := hside _ hAel hAN hneA hAcard hle
      have h1 : ⁅V, CFSG.conjugate V g⁆ ≤ CFSG.conjugate V g := by
        rw [Subgroup.commutator_comm]
        exact commutator_le_of_le_normalizer hVA
      exact hweak g (h1 hz)
    · have hz := hside _ hBel hBN hneB hBcard (by rw [hcB1, hcB2]; exact hle)
      have h1 : ⁅V, CFSG.conjugate V g⁻¹⁆ ≤ CFSG.conjugate V g⁻¹ := by
        rw [Subgroup.commutator_comm]
        exact commutator_le_of_le_normalizer hVB
      simpa using inv_mem (hweak g⁻¹ (h1 hz))
  apply hne
  rw [conjugate_eq_of_mem_normalizer' hgN]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hab

end CFSG.Quasithin.H13
