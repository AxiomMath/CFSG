module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

private theorem oi_mem_centerOf_iff {G : Type} [Group G] {X : Subgroup G} {x : G} :
    x ∈ centerOf X ↔ x ∈ X ∧ ∀ y ∈ X, y * x = x * y := by
  simp only [centerOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]

private theorem oi_omega_le_centerOf {G : Type} [Group G] (Q : Subgroup G) :
    dsOmega1 (centerOf Q) ≤ centerOf Q := by
  unfold dsOmega1
  exact (Subgroup.closure_le _).2 fun _ hx => hx.1

private theorem oi_omega_le {G : Type} [Group G] (Q : Subgroup G) :
    dsOmega1 (centerOf Q) ≤ Q := fun _ hx =>
  (oi_mem_centerOf_iff.mp (oi_omega_le_centerOf Q hx)).1

private theorem oi_omega_comm {G : Type} [Group G] {Q : Subgroup G} {w q : G}
    (hw : w ∈ dsOmega1 (centerOf Q)) (hq : q ∈ Q) : w * q = q * w :=
  ((oi_mem_centerOf_iff.mp (oi_omega_le_centerOf Q hw)).2 q hq).symm

private theorem oi_isPGroup_zpowers {G : Type} [Group G] {x : G} (hx : x ^ 2 = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  have hdvd : orderOf x ∣ 2 ^ 1 := by
    rw [pow_one]
    exact orderOf_dvd_of_pow_eq_one hx
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])

private theorem oi_comm_of_elemAbelian {G : Type} [Group G] {X : Subgroup G}
    (hX : IsElemAbelian 2 X) {a b : G} (ha : a ∈ X) (hb : b ∈ X) : a * b = b * a :=
  congrArg Subtype.val (isMulCommutative_iff.mp hX.1 ⟨a, ha⟩ ⟨b, hb⟩)

private theorem oi_conj_mem {G : Type} [Group G] {H : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (hx : x ∈ H) : g * x * g⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.mp hg x).mp hx

private theorem oi_S_le_bigB {G : Type} [Group G] (L1 L2 S : Subgroup G) :
    S ≤ bigB L1 L2 S := by
  unfold bigB
  exact le_sup_right

private theorem oi_isElemAbelian_sup {G : Type} [Group G] {X Y : Subgroup G}
    (hX : IsElemAbelian 2 X) (hY : IsElemAbelian 2 Y) (hYN : Y ≤ Subgroup.normalizer (X : Set G))
    (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) : IsElemAbelian 2 (X ⊔ Y) := by
  have key : ∀ a ∈ X ⊔ Y, ∀ b ∈ X ⊔ Y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨x1, hx1, y1, hy1, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hYN).mp ha
    obtain ⟨x2, hx2, y2, hy2, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hYN).mp hb
    have c1 : Commute x1 x2 := oi_comm_of_elemAbelian hX hx1 hx2
    have c2 : Commute y1 y2 := oi_comm_of_elemAbelian hY hy1 hy2
    have c3 : Commute x1 y2 := hc x1 hx1 y2 hy2
    have c4 : Commute y1 x2 := (hc x2 hx2 y1 hy1).symm
    exact Commute.mul_right (Commute.mul_left c1 c4) (Commute.mul_left c3 c2)
  refine ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (key a a.2 b b.2), fun a ha => ?_⟩
  obtain ⟨x1, hx1, y1, hy1, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hYN).mp ha
  rw [Commute.mul_pow (hc x1 hx1 y1 hy1 : Commute x1 y1), hX.2 x1 hx1, hY.2 y1 hy1, one_mul]

private theorem oi_not_comm {G : Type} [Group G] [Finite G] {L1 L2 S X Y : Subgroup G}
    (hL : Hyp111 L1 L2 S)
    (hrank : ∀ E : Subgroup G, IsElemAbelian 2 E → Nat.card E ≤ 16)
    (hX : IsElemAbelian 2 X) (hY : IsElemAbelian 2 Y) (hXn : Nat.card X = 16)
    (hYn : Nat.card Y = 16) (hXS : X ≤ S) (hXL1 : L1 ≤ Subgroup.normalizer (X : Set G))
    (hXS' : S ≤ Subgroup.normalizer (X : Set G))
    (hYX : Y ≤ Subgroup.normalizer (X : Set G)) (hYL2 : L2 ≤ Subgroup.normalizer (Y : Set G))
    (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) : False := by
  have hXY : X = X ⊔ Y :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by
      rw [hXn]; exact hrank _ (oi_isElemAbelian_sup hX hY hYX hc))
  have hYX' : Y ≤ X := by
    rw [hXY]; exact le_sup_right
  have hYeq : Y = X := Subgroup.eq_of_le_of_card_ge hYX' (by omega)
  have hXle : X ≤ L1 ⊔ L2 ⊔ S := hXS.trans le_sup_right
  have hXp : IsPGroup 2 X := IsPGroup.of_card (n := 4) (by norm_num [hXn])
  have h2 : L2 ≤ Subgroup.normalizer (X : Set G) := by
    rw [← hYeq]; exact hYL2
  have hX0 : X = ⊥ := CFSG.GH74.QTGen4.DSGen4.coreFree hL hXp hXle hXL1 h2 hXS'
  rw [hX0, Subgroup.card_bot] at hXn
  norm_num at hXn

private theorem oi_half {G : Type} [Group G] [Finite4 G]
    [DSLeaf LeafDSANoField] [DSLeaf LeafZiStructure] [DSLeaf LeafZiChief] [DSLeaf LeafM3]
    [DSLeaf LeafM4] [DSLeaf LeafRankBounds] {L1 L2 S : Subgroup G} (h : DSAHyp L1 L2 S)
    (c1 : ⁅dsZi L1 S, L1⁆ ≠ ⊥) (c2 : ⁅dsZi L2 S, L2⁆ ≠ ⊥)
    (hab : (dsZi L1 S ⊓ dsQ L2 L1 S).relIndex (dsZi L1 S) ≤
      (dsZi L2 S ⊓ dsQ L1 L2 S).relIndex (dsZi L2 S)) :
    ¬ dsZi L1 S ≤ dsQ L2 L1 S ∧ ¬ dsZi L2 S ≤ dsQ L1 L2 S ∧ NatSec L1 ⊥ (dsZi L1 S) ∧
      NatSec L2 ⊥ (dsZi L2 S) ∧ dsZi L1 S ⊓ dsZi L2 S = dsZi L2 S ⊓ dsQ L1 L2 S ∧
      dsZi L1 S ⊓ dsZi L2 S = dsZi L1 S ⊓ dsQ L2 L1 S ∧
      Nat.card (dsZi L1 S ⊓ dsZi L2 S : Subgroup G) = 4 := by
  have hS := dsa_no_field h
  have hZS1 : ZSetting L1 L2 S := ⟨h.hyp, hS.2.2⟩
  have hZS2 : ZSetting L2 L1 S := hZS1.symm
  have hq1 : IsL2Quot 2 (oTwoQuot ↥L1) :=
    CFSG.GH74.QTGen4.U42.VertexGen4.isL2Quot_two_of_gen4 Finite4.gen4 h.hyp.hyp.h1 h.ns1
  have hq2 : IsL2Quot 2 (oTwoQuot ↥L2) :=
    CFSG.GH74.QTGen4.U42.VertexGen4.isL2Quot_two_of_gen4 Finite4.gen4 h.hyp.hyp.h2 h.ns2
  obtain ⟨-, -, -, eW1, -, hN1, -⟩ := zi_structure hZS1
  obtain ⟨-, -, -, eW2, -, hN2, -⟩ := zi_structure hZS2
  obtain ⟨A1, hW1, -, hf1⟩ := zi_chief hZS1 hq1 c1
  obtain ⟨A2, hW2, -, hf2⟩ := zi_chief hZS2 hq2 c2
  have hE1 : IsElemAbelian 2 (dsZi L1 S) := by rw [hW1]; exact eW1
  have hE2 : IsElemAbelian 2 (dsZi L2 S) := by rw [hW2]; exact eW2
  have hn1 : Nat.card (dsZi L1 S : Subgroup G) = 16 := by
    have := A1.card
    rwa [Subgroup.relIndex_bot_left] at this
  have hn2 : Nat.card (dsZi L2 S : Subgroup G) = 16 := by
    have := A2.card
    rwa [Subgroup.relIndex_bot_left] at this
  have hQ1S : dsQ L1 L2 S ≤ S :=
    (le_sup_right : dsQ L1 L2 S ≤ (S ⊓ L1) ⊔ dsQ L1 L2 S).trans_eq hS.1.symm
  have hQ2S : dsQ L2 L1 S ≤ S :=
    (le_sup_right : dsQ L2 L1 S ≤ (S ⊓ L2) ⊔ dsQ L2 L1 S).trans_eq hS.2.1.symm
  have hZ1Q1 : dsZi L1 S ≤ dsQ L1 L2 S := by
    rw [hW1]; exact oi_omega_le _
  have hZ2Q2 : dsZi L2 S ≤ dsQ L2 L1 S := by
    rw [hW2]; exact oi_omega_le _
  have hZ1S : dsZi L1 S ≤ S := hZ1Q1.trans hQ1S
  have hZ2S : dsZi L2 S ≤ S := hZ2Q2.trans hQ2S
  have hcZ1Q1 : ∀ e ∈ dsZi L1 S, ∀ q ∈ dsQ L1 L2 S, e * q = q * e := by
    intro e he q hq
    rw [hW1] at he
    exact oi_omega_comm he hq
  have hcZ2Q2 : ∀ e ∈ dsZi L2 S, ∀ q ∈ dsQ L2 L1 S, e * q = q * e := by
    intro e he q hq
    rw [hW2] at he
    exact oi_omega_comm he hq
  have hSP1 : S ≤ L1 ⊔ bigB L1 L2 S := (oi_S_le_bigB L1 L2 S).trans le_sup_right
  have hSP2 : S ≤ L2 ⊔ bigB L2 L1 S := (oi_S_le_bigB L2 L1 S).trans le_sup_right
  have hSN1 : S ≤ Subgroup.normalizer (dsZi L1 S : Set G) := hSP1.trans hN1
  have hSN2 : S ≤ Subgroup.normalizer (dsZi L2 S : Set G) := hSP2.trans hN2
  have hZ1N2 : dsZi L1 S ≤ Subgroup.normalizer (dsZi L2 S : Set G) := hZ1S.trans hSN2
  have hZ2N1 : dsZi L2 S ≤ Subgroup.normalizer (dsZi L1 S : Set G) := hZ2S.trans hSN1
  have hQ1N2 : dsQ L1 L2 S ≤ Subgroup.normalizer (dsZi L2 S : Set G) := hQ1S.trans hSN2
  have hnc : ¬ ∀ x ∈ dsZi L1 S, ∀ y ∈ dsZi L2 S, x * y = y * x := fun hc =>
    oi_not_comm h.hyp.hyp (fun E hE => (rank_bounds (G := G)).2 E hE) hE1 hE2 hn1 hn2 hZ1S
      (le_sup_left.trans hN1) hSN1 hZ2N1 (le_sup_left.trans hN2) hc
  have hI1 : ¬ dsZi L1 S ≤ dsQ L2 L1 S := fun hle => hnc fun x hx y hy =>
    (hcZ2Q2 y hy x (hle hx)).symm
  have hI2 : ¬ dsZi L2 S ≤ dsQ L1 L2 S := fun hle => hnc fun x hx y hy =>
    hcZ1Q1 x hx y (hle hy)
  have hbr12 : ∀ e ∈ dsZi L1 S, ∀ z ∈ dsZi L2 S, ⁅e, z⁆ ∈ dsZi L2 S := by
    intro e he z hz
    have h1 : e * z * e⁻¹ ∈ dsZi L2 S := oi_conj_mem (hZ1N2 he) hz
    rw [commutatorElement_def]
    exact (dsZi L2 S).mul_mem h1 ((dsZi L2 S).inv_mem hz)
  have hbr21 : ∀ z ∈ dsZi L2 S, ∀ e ∈ dsZi L1 S, ⁅z, e⁆ ∈ dsZi L1 S := by
    intro z hz e he
    have h1 : z * e * z⁻¹ ∈ dsZi L1 S := oi_conj_mem (hSN1 (hZ2S hz)) he
    rw [commutatorElement_def]
    exact (dsZi L1 S).mul_mem h1 ((dsZi L1 S).inv_mem he)
  have hcomm_Z1 : ∀ e ∈ dsZi L1 S, ∀ t ∈ S, ⁅e, t⁆ ∈ dsZi L1 S := by
    intro e he t ht
    have h1 : t * e⁻¹ * t⁻¹ ∈ dsZi L1 S := oi_conj_mem (hSN1 ht) ((dsZi L1 S).inv_mem he)
    have e1 : ⁅e, t⁆ = e * (t * e⁻¹ * t⁻¹) := by
      simp only [commutatorElement_def, mul_assoc]
    rw [e1]
    exact (dsZi L1 S).mul_mem he h1
  have hq1' : ⁅⁅dsZi L1 S, dsZi L2 S⁆, dsZi L2 S⁆ ≤ ⊥ := by
    have hle12 : ⁅dsZi L1 S, dsZi L2 S⁆ ≤ dsZi L2 S :=
      Subgroup.commutator_le.mpr fun e he z hz => hbr12 e he z hz
    exact Subgroup.commutator_le.mpr fun a ha b hb => Subgroup.mem_bot.mpr
      (commutatorElement_eq_one_iff_mul_comm.mpr (oi_comm_of_elemAbelian hE2 (hle12 ha) hb))
  have hnt1 : ¬ ⁅dsZi L1 S, dsZi L2 S⁆ ≤ ⊥ := fun hle => hnc fun x hx y hy =>
    commutatorElement_eq_one_iff_mul_comm.mp
      (Subgroup.mem_bot.mp (Subgroup.commutator_le.mp hle x hx y hy))
  have hf1' : ∀ x ∈ dsZi L2 S, (∀ e ∈ dsZi L1 S, ⁅x, e⁆ ∈ (⊥ : Subgroup G)) →
      x ∈ dsQ L1 L2 S := fun x hx hall =>
    hf1 x (hSP1 (hZ2S hx)) (oi_isPGroup_zpowers (hE2.2 x hx))
      (fun e he => Subgroup.mem_bot.mp (hall e he))
  have hYc1 : ∀ y ∈ dsZi L1 S ⊓ dsQ L2 L1 S, ∀ x ∈ dsZi L2 S, ⁅y, x⁆ ∈ (⊥ : Subgroup G) :=
    fun y hy x hx => Subgroup.mem_bot.mpr
      (commutatorElement_eq_one_iff_mul_comm.mpr ((hcZ2Q2 x hx y (Subgroup.mem_inf.mp hy).2).symm))
  have hX1 : dsZi L2 S ≤ (S ⊓ L1) ⊔ dsQ L1 L2 S := hZ2S.trans hS.1.le
  obtain ⟨hNat1, hS12', hrel1⟩ :=
    m4 (X := dsZi L2 S) (Y := dsZi L1 S ⊓ dsQ L2 L1 S) A1 h.hyp.hyp.h1.sylow hX1 hq1' hnt1 hf1'
      bot_le inf_le_left hYc1 hab
  have hS12 : dsZi L2 S ⊔ dsQ L1 L2 S = S := hS12'.trans hS.1.symm
  have hmemS : ∀ t ∈ S, ∃ z ∈ dsZi L2 S, ∃ q ∈ dsQ L1 L2 S, t = z * q := by
    intro t ht
    have ht' : t ∈ dsZi L2 S ⊔ dsQ L1 L2 S := by
      rw [hS12]; exact ht
    exact (F1.mem_sup_iff_exists_mul_of_normalizes hQ1N2).mp ht'
  have hcomm_key : ∀ e ∈ dsZi L1 S, ∀ t ∈ S, ⁅e, t⁆ ∈ dsZi L2 S := by
    intro e he t ht
    obtain ⟨z, hz, q, hq, rfl⟩ := hmemS t ht
    have hc : Commute e q := hcZ1Q1 e he q hq
    have hqe : q * e⁻¹ * q⁻¹ = e⁻¹ := by
      rw [← hc.inv_left.eq, mul_inv_cancel_right]
    have key : ⁅e, z * q⁆ = ⁅e, z⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc e * (z * q) * e⁻¹ * (z * q)⁻¹ = e * z * (q * e⁻¹ * q⁻¹) * z⁻¹ := by group
        _ = e * z * e⁻¹ * z⁻¹ := by rw [hqe]
    rw [key]
    exact hbr12 e he z hz
  have hcardQ2 : Nat.card (dsZi L1 S ⊓ dsQ L2 L1 S : Subgroup G) = 4 := by
    have hr := Subgroup.relIndex_mul_card (H := dsZi L1 S ⊓ dsQ L2 L1 S) (K := dsZi L1 S)
    have hself : (dsZi L1 S ⊓ dsQ L2 L1 S) ⊓ dsZi L1 S = dsZi L1 S ⊓ dsQ L2 L1 S :=
      inf_eq_left.mpr inf_le_left
    rw [hself, hrel1, hn1] at hr
    omega
  have hcomm_br : ⁅dsZi L1 S, S ⊓ L1⁆ ≤ dsZi L1 S ⊓ dsZi L2 S :=
    Subgroup.commutator_le.mpr fun e he t ht => Subgroup.mem_inf.mpr
      ⟨hcomm_Z1 e he t (Subgroup.mem_inf.mp ht).1, hcomm_key e he t (Subgroup.mem_inf.mp ht).1⟩
  have h4 : Nat.card (⁅dsZi L1 S, S ⊓ L1⁆ : Subgroup G) = 4 := by
    have := ((m3 A1 h.hyp.hyp.h1.sylow).1 hNat1).2.1
    rwa [sup_bot_eq, Subgroup.relIndex_bot_left] at this
  have hcardI : 4 ≤ Nat.card (dsZi L1 S ⊓ dsZi L2 S : Subgroup G) := by
    have := Subgroup.card_le_of_le hcomm_br
    omega
  have hI_le_Q2 : dsZi L1 S ⊓ dsZi L2 S ≤ dsZi L1 S ⊓ dsQ L2 L1 S :=
    inf_le_inf le_rfl hZ2Q2
  have hI_eq_Q2 : dsZi L1 S ⊓ dsZi L2 S = dsZi L1 S ⊓ dsQ L2 L1 S :=
    Subgroup.eq_of_le_of_card_ge hI_le_Q2 (by omega)
  have hcardI_eq : Nat.card (dsZi L1 S ⊓ dsZi L2 S : Subgroup G) = 4 := by
    rw [hI_eq_Q2]; exact hcardQ2
  have hI_le_Q1 : dsZi L1 S ⊓ dsZi L2 S ≤ dsZi L2 S ⊓ dsQ L1 L2 S :=
    le_inf inf_le_right (inf_le_left.trans hZ1Q1)
  have hcardQ1 : Nat.card (dsZi L2 S ⊓ dsQ L1 L2 S : Subgroup G) ≤ 4 := by
    have hr := Subgroup.relIndex_mul_card (H := dsZi L2 S ⊓ dsQ L1 L2 S) (K := dsZi L2 S)
    have hself : (dsZi L2 S ⊓ dsQ L1 L2 S) ⊓ dsZi L2 S = dsZi L2 S ⊓ dsQ L1 L2 S :=
      inf_eq_left.mpr inf_le_left
    rw [hself, hn2] at hr
    have h4le : 4 ≤ (dsZi L2 S ⊓ dsQ L1 L2 S).relIndex (dsZi L2 S) := by
      rw [hrel1] at hab
      exact hab
    by_contra hcon
    have hcon' : 5 ≤ Nat.card (dsZi L2 S ⊓ dsQ L1 L2 S : Subgroup G) := by omega
    have hmul := Nat.mul_le_mul h4le hcon'
    rw [hr] at hmul
    omega
  have hI_eq_Q1 : dsZi L1 S ⊓ dsZi L2 S = dsZi L2 S ⊓ dsQ L1 L2 S :=
    Subgroup.eq_of_le_of_card_ge hI_le_Q1 (by omega)
  have hcardQ1' : Nat.card (dsZi L2 S ⊓ dsQ L1 L2 S : Subgroup G) = 4 := by
    rw [← hI_eq_Q1]; exact hcardI_eq
  have hrel2 : (dsZi L2 S ⊓ dsQ L1 L2 S).relIndex (dsZi L2 S) = 4 := by
    have hr := Subgroup.relIndex_mul_card (H := dsZi L2 S ⊓ dsQ L1 L2 S) (K := dsZi L2 S)
    have hself : (dsZi L2 S ⊓ dsQ L1 L2 S) ⊓ dsZi L2 S = dsZi L2 S ⊓ dsQ L1 L2 S :=
      inf_eq_left.mpr inf_le_left
    rw [hself, hn2, hcardQ1'] at hr
    omega
  have hX2 : dsZi L1 S ≤ (S ⊓ L2) ⊔ dsQ L2 L1 S := hZ1S.trans hS.2.1.le
  have hle21 : ⁅dsZi L2 S, dsZi L1 S⁆ ≤ dsZi L1 S :=
    Subgroup.commutator_le.mpr fun z hz e he => hbr21 z hz e he
  have hq2' : ⁅⁅dsZi L2 S, dsZi L1 S⁆, dsZi L1 S⁆ ≤ ⊥ :=
    Subgroup.commutator_le.mpr fun a ha b hb => Subgroup.mem_bot.mpr
      (commutatorElement_eq_one_iff_mul_comm.mpr (oi_comm_of_elemAbelian hE1 (hle21 ha) hb))
  have hnt2 : ¬ ⁅dsZi L2 S, dsZi L1 S⁆ ≤ ⊥ := fun hle => hnc fun x hx y hy =>
    (commutatorElement_eq_one_iff_mul_comm.mp
      (Subgroup.mem_bot.mp (Subgroup.commutator_le.mp hle y hy x hx))).symm
  have hf2' : ∀ x ∈ dsZi L1 S, (∀ e ∈ dsZi L2 S, ⁅x, e⁆ ∈ (⊥ : Subgroup G)) →
      x ∈ dsQ L2 L1 S := fun x hx hall =>
    hf2 x (hSP2 (hZ1S hx)) (oi_isPGroup_zpowers (hE1.2 x hx))
      (fun e he => Subgroup.mem_bot.mp (hall e he))
  have hYc2 : ∀ y ∈ dsZi L2 S ⊓ dsQ L1 L2 S, ∀ x ∈ dsZi L1 S, ⁅y, x⁆ ∈ (⊥ : Subgroup G) :=
    fun y hy x hx => Subgroup.mem_bot.mpr
      (commutatorElement_eq_one_iff_mul_comm.mpr ((hcZ1Q1 x hx y (Subgroup.mem_inf.mp hy).2).symm))
  have hcard2 : (dsZi L2 S ⊓ dsQ L1 L2 S).relIndex (dsZi L2 S) ≤
      (dsZi L1 S ⊓ dsQ L2 L1 S).relIndex (dsZi L1 S) :=
    le_of_eq (hrel2.trans hrel1.symm)
  obtain ⟨hNat2, -, -⟩ :=
    m4 (X := dsZi L1 S) (Y := dsZi L2 S ⊓ dsQ L1 L2 S) A2 h.hyp.hyp.h2.sylow hX2 hq2' hnt2 hf2'
      bot_le inf_le_left hYc2 hcard2
  exact ⟨hI1, hI2, hNat1, hNat2, hI_eq_Q1, hI_eq_Q2, hcardI_eq⟩

theorem leafDSACaseIOffender [DSLeaf LeafDSANoField] [DSLeaf LeafZiStructure] [DSLeaf LeafZiChief] [DSLeaf LeafM3] [DSLeaf LeafM4] [DSLeaf LeafRankBounds] [DSLeaf LeafSylowS] : LeafDSACaseIOffender := by
  intro G _ _ L1 L2 S h c1 c2
  rcases le_total ((dsZi L1 S ⊓ dsQ L2 L1 S).relIndex (dsZi L1 S))
      ((dsZi L2 S ⊓ dsQ L1 L2 S).relIndex (dsZi L2 S)) with hab | hab
  · exact oi_half h c1 c2 hab
  · obtain ⟨j1, j2, j3, j4, j5, j6, j7⟩ := oi_half h.symm c2 c1 hab
    exact ⟨j2, j1, j4, j3, (inf_comm _ _).trans j6, (inf_comm _ _).trans j5,
      by rw [inf_comm]; exact j7⟩

end CFSG.GH74.QTGen4.DSGen4
