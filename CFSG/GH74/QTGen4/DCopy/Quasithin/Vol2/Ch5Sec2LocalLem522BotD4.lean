module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522BotList
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotD4L8
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotD4Q
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotW

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement

theorem stmt5_2_2_bot_D4_of_F4 (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    (hLie : Stmt5_2_L2Lie_F4) : Stmt5_2_2_bot_D4_F4 := by
  intro G _ _ T M L V H B D L₂ Dp n hyp hO hS3 h111 _ hL2 hQsp hO11
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  set S := sec52S M H with hSdef
  set Q := pCoreOf 2 L₂ with hQdef
  have hSY : IsSylowTwoOf S (Dp ⊔ S) := by
    have h1 := h111.h2.sylow
    rwa [inf_eq_left.mpr le_sup_right] at h1
  have hS12 : Nat.card ↥S = 2 ^ 12 := by
    rw [card_eq_two_mul_of_perm_three hSY hS3, hO11]
    norm_num
  have hQ9 : Nat.card ↥Q = 2 ^ 9 := by rw [hQsp.2.1]
  have hSL12 : Nat.card ↥(S ⊓ L₂) = 2 ^ 12 := by
    rw [card_inf_of_card_oTwoQuot h111.h1.sylow (j := 3) (m := 63) (by norm_num)
      (by rw [hL2.card (by norm_num)]; norm_num), hQ9]
    norm_num
  have hSL : S ≤ L₂ := le_of_card_le_card_inf (hS12.trans hSL12.symm).le
  have hSL' : IsSylowTwoOf S L₂ := by
    have h1 := h111.h1.sylow
    rwa [inf_eq_left.mpr hSL] at h1
  have hQS : Q ≤ S := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hSL'
  have hS2 : IsPGroup 2 ↥S := pCoreOf_isPGroup 2 _
  have hchar : CharTwo L₂ := by
    have hle : L₂ ≤ L₂ ⊔ S ⊔ borelOf (Dp ⊔ S) S := le_sup_left.trans le_sup_left
    refine CT.CharTwo.of_normal h111.h1.charTwo hle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr ?_)
    exact sup_le (sup_le Subgroup.le_normalizer h111.h1.normalizes) h111.h1.borel_le
  obtain ⟨z, hzQ, hz1, hzz, hzc, hcen, -, -⟩ := isSpecialPow_central_facts (by norm_num) hQsp
  have hLQ : L₂ ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 L₂
  have hzL : ∀ l ∈ L₂, l * z = z * l := by
    intro l hl
    have hlz : l * z * l⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hLQ hl) z).mp hzQ
    have hc : l * z * l⁻¹ = 1 ∨ l * z * l⁻¹ = z := by
      refine hcen _ hlz fun q hq => ?_
      have hq' : l⁻¹ * q * l⁻¹⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hLQ (L₂.inv_mem hl)) q).mp hq
      rw [inv_inv] at hq'
      have h1 := hzc _ hq'
      calc q * (l * z * l⁻¹) = l * ((l⁻¹ * q * l) * z) * l⁻¹ := by group
        _ = l * (z * (l⁻¹ * q * l)) * l⁻¹ := by rw [h1]
        _ = l * z * l⁻¹ * q := by group
    rcases hc with h0 | h0
    · exfalso
      apply hz1
      calc z = l⁻¹ * (l * z * l⁻¹) * l := by group
        _ = 1 := by rw [h0]; group
    · calc l * z = l * z * l⁻¹ * l := by group
        _ = z * l := by rw [h0]
  obtain ⟨hST, hTS, -, -, hSLeq, hSL₂eq, -, -⟩ := hyp.S_facts_F4 h510 h331 hR
  have hzT : ∀ t ∈ T, t * z = z * t := by
    intro t ht
    have hyS : t * z * t⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp (hTS ht) z).mp (hQS hzQ)
    have hyc : ∀ q ∈ Q, q * (t * z * t⁻¹) = (t * z * t⁻¹) * q := by
      intro q hq
      have hq' : t⁻¹ * q * t⁻¹⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp (hTS (T.inv_mem ht)) q).mp (hQS hq)
      rw [inv_inv] at hq'
      have h1 := hzL _ (hSL hq')
      calc q * (t * z * t⁻¹) = t * ((t⁻¹ * q * t) * z) * t⁻¹ := by group
        _ = t * (z * (t⁻¹ * q * t)) * t⁻¹ := by rw [h1]
        _ = t * z * t⁻¹ * q := by group
    have hyQ : t * z * t⁻¹ ∈ Q := hchar ⟨hSL hyS, Subgroup.mem_centralizer_iff.mpr hyc⟩
    rcases hcen _ hyQ hyc with h0 | h0
    · exfalso
      apply hz1
      calc z = t⁻¹ * (t * z * t⁻¹) * t := by group
        _ = 1 := by rw [h0]; group
    · calc t * z = t * z * t⁻¹ * t := by group
        _ = z * t := by rw [h0]
  have hzZ : Subgroup.zpowers z ≤ quasithinOmegaOneCenter T := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.subset_closure
    refine ⟨⟨hST (hQS hzQ), Subgroup.mem_centralizer_iff.mpr hzT⟩, ?_⟩
    rw [sq]
    exact hzz
  have hsylLT : IsSylowTwoOf T (L ⊔ T) := h.isSylowTwoOf le_sup_right
  have hV := hyp.ch5Module
  have hred := hV.isTwoReducedIn
  have hVO : V ≤ pCoreOf 2 (L ⊔ T) := le_pCoreOf_of_le_normalizer 2 hred.1 hred.2.1
    (fun v => ⟨1, Subtype.ext (by simpa [pow_one] using hred.2.2.1.2 v v.2)⟩)
  have hcharLT : CharTwo (L ⊔ T) := by
    refine charTwo_of_inH' h.qtke h.sylow ⟨le_sup_right, fun h0 => hV.2.2 ?_⟩
    have hV0 : V = ⊥ := le_bot_iff.mp (h0 ▸ hVO)
    rw [hV0, Subgroup.commutator_bot_left]
  obtain ⟨hXc, hXe⟩ := conjClosure_le_centerOf_pCoreOf_of_sylowIn le_sup_right hsylLT.2.1
    hsylLT.2.2 hcharLT hzZ
  set X := conjClosure (Subgroup.zpowers z) L with hXdef
  have hXX : X ≤ conjClosure (Subgroup.zpowers z) (L ⊔ T) := conjClosure_mono le_rfl le_sup_left
  have hXO : ∀ x ∈ X, ∀ o ∈ pCoreOf 2 (L ⊔ T), o * x = x * o := fun x hx o ho =>
    Subgroup.mem_centralizer_iff.mp (hXc (hXX hx)).2 o ho
  have hXc' : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hXe.1.is_comm.comm ⟨a, hXX ha⟩ ⟨b, hXX hb⟩)
  have hX2 : ∀ x ∈ X, x * x = 1 := fun x hx => by
    rw [← sq]
    exact hXe.2 x (hXX hx)
  have hLX : L ≤ Subgroup.normalizer (X : Set G) := le_normalizer_conjClosure _ L
  have hzX : z ∈ X := le_conjClosure _ L (Subgroup.mem_zpowers z)
  have hDpL : Dp ≤ L := hyp.Dp_le.trans (hyp.notation59.2.1.1.trans inf_le_left)
  have hXL : ⁅X, L⁆ ≠ ⊥ := by
    intro h0
    have hzLc : ∀ l ∈ L, l * z = z * l := by
      intro l hl
      have h1 := Subgroup.commutator_mem_commutator hzX hl
      rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    have hG₀ : Dp ⊔ (L₂ ⊔ S) ≤
        Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      refine sup_le (fun d hd => ?_) (sup_le (fun l hl => ?_) (fun s hs => ?_))
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hzLc d (hDpL hd)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hzL l hl
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hzL s (hSL hs)
    have hle : Subgroup.zpowers z ≤ pCoreOf 2 (Dp ⊔ (L₂ ⊔ S)) := by
      refine le_pCoreOf_of_le_normalizer 2 ?_
        (hG₀.trans (Subgroup.centralizer_le_normalizer _)) ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (hQS hzQ))
      · exact IsPGroup.of_card (n := 1) (by
          rw [Nat.card_zpowers, pow_one]
          exact orderOf_eq_prime (by rw [sq]; exact hzz) hz1)
    rw [hO] at hle
    exact hz1 ((Subgroup.mem_bot).mp (hle (Subgroup.mem_zpowers z)))
  have hn : Even n := by
    rcases hyp.n_cases with h2 | h4 | h8
    · exact ⟨1, by omega⟩
    · exact ⟨2, by omega⟩
    · exact ⟨4, by omega⟩
  have hE16 := h.sixteen_le_card_commutator_of hLX hXc' hX2 hXL hn
  have hEX : ⁅X, L⁆ ≤ X := Subgroup.le_normalizer_iff_commutator_le_left.mp hLX
  have hXLT : X ≤ pCoreOf 2 (L ⊔ T) := fun x hx => (hXc (hXX hx)).1
  have hOT : pCoreOf 2 (L ⊔ T) ≤ T := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hsylLT
  have hEL : ⁅X, L⁆ ≤ L := by
    have hXN : X ≤ Subgroup.normalizer (L : Set G) :=
      hXLT.trans ((pCoreOf_le 2 _).trans h.sup_le_normalizer)
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hXN
  have hES : ⁅X, L⁆ ≤ S := by
    intro x hx
    have hxTL : x ∈ T ⊓ L := ⟨hOT (hXLT (hEX hx)), hEL hx⟩
    rw [← hSLeq] at hxTL
    exact hxTL.1
  set N₂ := CFSG.Open.pCore 2 ↥L₂ with hN₂
  set π₂ : ↥L₂ →* oTwoQuot ↥L₂ := QuotientGroup.mk' N₂ with hπ₂
  have hker : ∀ y : ↥L₂, π₂ y = 1 ↔ (y : G) ∈ Q := by
    intro y
    rw [hπ₂, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hQdef, pCoreOf]
    exact (Subgroup.mem_map_iff_mem L₂.subtype_injective).symm
  have hkerS : π₂.ker ≤ S.subgroupOf L₂ := by
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    exact hQS ((hker y).mp hy)
  set Sb := (S.subgroupOf L₂).map π₂ with hSb
  have hSb2 : IsPGroup 2 ↥Sb :=
    (hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSL).symm).map π₂
  have hSbi : ¬ 2 ∣ Sb.index := by
    rw [hSb, Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective N₂) hkerS]
    exact hSL'.2.2
  have hSbmem : ∀ y : ↥L₂, y ∈ S.subgroupOf L₂ ↔ π₂ y ∈ Sb := by
    intro y
    rw [← Subgroup.mem_comap, hSb, Subgroup.comap_map_eq_self hkerS]
  obtain ⟨c, hcN, hc7, hc1, hcfix⟩ := exists_cartan_of_isL2Quot_three hL2 hSb2 hSbi
  obtain ⟨ℓ, hℓ⟩ := QuotientGroup.mk'_surjective N₂ c
  have hℓc : π₂ ℓ = c := hℓ
  set β := ℓ ^ 512 with hβdef
  have hN512 : Nat.card ↥N₂ = 512 := by
    have h1 : Nat.card ↥Q = Nat.card ↥N₂ := Subgroup.card_map_of_injective L₂.subtype_injective
    rw [← h1, hQ9]
    norm_num
  have hβ7 : β ^ 7 = 1 := by
    have hℓ7 : ℓ ^ 7 ∈ N₂ := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπ₂, map_pow, hℓc, hc7]
    have h1 : (⟨ℓ ^ 7, hℓ7⟩ : ↥N₂) ^ Nat.card ↥N₂ = 1 := pow_card_eq_one'
    rw [hN512] at h1
    have h2 : (ℓ ^ 7) ^ 512 = 1 := congrArg Subtype.val h1
    rw [hβdef, ← pow_mul, mul_comm, pow_mul, h2]
  have hβc : π₂ β = c := by
    rw [hβdef, map_pow, hℓc, show 512 = 7 * 73 + 1 by norm_num, pow_add, pow_mul, hc7, one_pow,
      one_mul, pow_one]
  set b : G := (β : G) with hbdef
  have hbL₂ : b ∈ L₂ := β.2
  have hb7 : b ^ 7 = 1 := by
    have := congrArg Subtype.val hβ7
    simpa [hbdef] using this
  have hbS : b ∈ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    by_cases hxL : x ∈ L₂
    · have h1 := hSbmem ⟨x, hxL⟩
      rw [Subgroup.mem_subgroupOf] at h1
      have h2 : b * x * b⁻¹ ∈ S ↔ π₂ (β * ⟨x, hxL⟩ * β⁻¹) ∈ Sb := by
        have h3 := hSbmem (β * ⟨x, hxL⟩ * β⁻¹)
        rw [Subgroup.mem_subgroupOf] at h3
        exact h3
      rw [h1, h2, map_mul, map_mul, map_inv, hβc]
      exact Subgroup.mem_normalizer_iff.mp hcN _
    · have hbx : b * x * b⁻¹ ∉ L₂ := fun hx' => hxL (by
        have := L₂.mul_mem (L₂.mul_mem (L₂.inv_mem hbL₂) hx') hbL₂
        simpa [mul_assoc] using this)
      exact ⟨fun hx => absurd (hSL hx) hxL, fun hx => absurd (hSL hx) hbx⟩
  have hbfix : ∀ s ∈ S, s * b = b * s → s ∈ Q := by
    intro s hs hsb
    have hy : π₂ ⟨s, hSL hs⟩ ∈ Sb := (hSbmem ⟨s, hSL hs⟩).mp hs
    have hyb : (⟨s, hSL hs⟩ : ↥L₂) * β = β * ⟨s, hSL hs⟩ := Subtype.ext hsb
    have h1 := congrArg π₂ hyb
    rw [map_mul, map_mul, hβc] at h1
    exact (hker _).mp (hcfix _ hy h1)
  have hbQ : ¬ Q ≤ Subgroup.centralizer ({b} : Set G) := by
    intro hle
    apply hc1
    rw [← hβc]
    refine (hker β).mpr (hchar ⟨hbL₂, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hq)
  obtain ⟨-, hbor, -⟩ := hLie G T M L H B D L₂ n hyp.toHyp5_1_8 hyp.notation59 hyp.choice
  have hTL₂ : T ⊓ L₂ = S := by rw [← hSL₂eq, inf_eq_left.mpr hSL]
  have hbM : b ∈ M := hbor ⟨hbL₂, by rw [hTL₂]; exact hbS⟩
  have hbL : b ∈ Subgroup.normalizer (L : Set G) := h.normal hbM
  have hbz : ∀ w ∈ Subgroup.zpowers z, b * w = w * b := by
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.zpow_right (hzL b hbL₂) k).eq
  have hOL : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
      (h.sup_le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)
  have hbX : X ≤ Subgroup.centralizer ({b} : Set G) := by
    refine conjClosure_le fun l hl w hw => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    set o := b * l * b⁻¹ * l⁻¹ with ho
    have hoO : o ∈ pCoreOf 2 (L ⊔ T) :=
      hOL (h.commutator_mem_of_pow_seven hyp.n_cases hbL hb7 hl)
    have hlw : l * w * l⁻¹ ∈ X := mem_conjClosure hl hw
    have h1 := hXO _ hlw o hoO
    have hbw := hbz w hw
    have e1 : b * (l * w * l⁻¹) * b⁻¹ = o * (l * w * l⁻¹) * o⁻¹ := by
      calc b * (l * w * l⁻¹) * b⁻¹ = (b * l * b⁻¹) * (b * w * b⁻¹) * (b * l * b⁻¹)⁻¹ := by group
        _ = (o * l) * w * (o * l)⁻¹ := by
            rw [show b * w * b⁻¹ = w by rw [hbw, mul_inv_cancel_right]]
            rw [ho]
            group
        _ = o * (l * w * l⁻¹) * o⁻¹ := by group
    have e2 : o * (l * w * l⁻¹) * o⁻¹ = l * w * l⁻¹ := by
      rw [h1, mul_inv_cancel_right]
    have e3 : b * (l * w * l⁻¹) * b⁻¹ = l * w * l⁻¹ := e1.trans e2
    calc l * w * l⁻¹ * b = b * (l * w * l⁻¹) * b⁻¹ * b := by rw [e3]
      _ = b * (l * w * l⁻¹) := by group
  have hEQ : ⁅X, L⁆ ≤ Q ⊓ Subgroup.centralizer ({b} : Set G) := by
    intro x hx
    have hxb : x ∈ Subgroup.centralizer ({b} : Set G) := hbX (hEX hx)
    exact ⟨hbfix x (hES hx) (Subgroup.mem_centralizer_singleton_iff.mp hxb), hxb⟩
  have h8 := card_inf_centralizer_le_eight hQsp (hLQ hbL₂) hb7 hbQ
  have := Subgroup.card_le_of_le hEQ
  omega

end CFSG.Quasithin.H13
