module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplitDecomp
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.Goldschmidt.Steps.Sec82Tools
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplit

open CFSG CFSG.LocalCores CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.Lemma213 (layerMul_injective conj_mem_layer)

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x : Y}

@[expose] def omega1 (p : ℕ) (W : Subgroup Y)
    (hW : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w) : Subgroup Y where
  carrier := {w | w ∈ W ∧ w ^ p = 1}
  mul_mem' := fun {a b} ha hb => ⟨W.mul_mem ha.1 hb.1, by
    have hab : Commute a b := hW a ha.1 b hb.1
    rw [hab.mul_pow, ha.2, hb.2, one_mul]⟩
  one_mem' := ⟨W.one_mem, one_pow p⟩
  inv_mem' := fun {a} ha => ⟨W.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem omega1_le {W : Subgroup Y} {hW : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w} :
    omega1 p W hW ≤ W := fun _ hw => hw.1

theorem isElemAbelian_omega1 {W : Subgroup Y} {hW : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w} :
    IsElemAbelian p (omega1 p W hW) :=
  (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_iff).2
    ⟨fun a ha b hb => hW a ha.1 b hb.1, fun a ha => ha.2⟩

theorem comm_comp (h : SplitCfg p P x) (C : ComponentIndex Y) :
    ∀ a ∈ P ⊓ C.1, ∀ b ∈ P ⊓ C.1, a * b = b * a := fun a ha b hb => by
  haveI := h.cyclic C
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥(P ⊓ C.1)) ⟨b, hb⟩)

@[expose] def omegaComp (h : SplitCfg p P x) (C : ComponentIndex Y) : Subgroup Y :=
  omega1 p (P ⊓ C.1) (comm_comp h C)

theorem omegaComp_le (h : SplitCfg p P x) (C : ComponentIndex Y) : omegaComp h C ≤ P ⊓ C.1 :=
  omega1_le

theorem mem_omegaComp {h : SplitCfg p P x} {C : ComponentIndex Y} {t : Y} :
    t ∈ omegaComp h C ↔ t ∈ P ⊓ C.1 ∧ t ^ p = 1 := Iff.rfl

theorem card_omegaComp (h : SplitCfg p P x) (C : ComponentIndex Y) :
    Nat.card (omegaComp h C) = p := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  apply le_antisymm
  · exact card_le_comp h C ((omegaComp_le h C).trans inf_le_right) isElemAbelian_omega1
  · obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(P ⊓ C.1)) p (dvd_inf_comp h C)
    have hord : orderOf (g : Y) = p := by rw [Subgroup.orderOf_coe]; exact hg
    have hgp : (g : Y) ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
    have hle : zpowers (g : Y) ≤ omegaComp h C :=
      zpowers_le.mpr (mem_omegaComp.mpr ⟨g.2, hgp⟩)
    have := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, hord] at this

theorem omegaComp_central (h : SplitCfg p P x) (C : ComponentIndex Y) {n q : Y}
    (hn : n ∈ omegaComp h C) (hq : q ∈ compKer P) : q * n = n * q := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : Fact (IsPGroup p ↥(compKer P)) := ⟨h.sylow.isPGroup.to_le compKer_le⟩
  have hNQ : omegaComp h C ≤ compKer P :=
    ((omegaComp_le h C).trans (inf_le_inf_left P (component_le_layer C.2))).trans
      layer_inf_le_compKer
  let N : Subgroup ↥(compKer P) := (omegaComp h C).subgroupOf (compKer P)
  haveI : N.Normal := ⟨fun n' hn' g => by
    have hn'' : (n' : Y) ∈ omegaComp h C := hn'
    refine Subgroup.mem_subgroupOf.mpr (mem_omegaComp.mpr ⟨⟨?_, ?_⟩, ?_⟩)
    · exact P.mul_mem (P.mul_mem (compKer_le g.2) (omegaComp_le h C hn'').1)
        (P.inv_mem (compKer_le g.2))
    · have hg := mem_normalizer_of_mem_compKer g.2 C
      exact (Subgroup.mem_normalizer_iff.mp hg _).mp (omegaComp_le h C hn'').2
    · show ((g : Y) * (n' : Y) * (g : Y)⁻¹) ^ p = 1
      rw [conj_pow, (mem_omegaComp.mp hn'').2, mul_one, mul_inv_cancel]⟩
  have hcard : Nat.card N = p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hNQ).toEquiv]
    exact card_omegaComp h C
  have hcen := normal_subgroup_card_eq_prime_le_center N hcard
  have hnN : (⟨n, hNQ hn⟩ : ↥(compKer P)) ∈ N := Subgroup.mem_subgroupOf.mpr hn
  have := Subgroup.mem_center_iff.mp (hcen hnN) ⟨q, hq⟩
  exact congrArg Subtype.val this

@[expose] def Vsub (p : ℕ) (P : Subgroup Y) : Subgroup Y where
  carrier := {a | a ∈ P ⊓ layer Y ∧ a ^ p = 1 ∧ ∀ q ∈ compKer P, q * a = a * q}
  mul_mem' := fun {a b} ha hb => by
    have hab : Commute a b := hb.2.2 a (layer_inf_le_compKer ha.1)
    refine ⟨mul_mem ha.1 hb.1, ?_, fun q hq => ?_⟩
    · rw [hab.mul_pow, ha.2.1, hb.2.1, one_mul]
    · rw [← mul_assoc, ha.2.2 q hq, mul_assoc, hb.2.2 q hq, ← mul_assoc]
  one_mem' := ⟨one_mem _, one_pow p, fun q _ => by simp⟩
  inv_mem' := fun {a} ha =>
    ⟨inv_mem ha.1, by rw [inv_pow, ha.2.1, inv_one],
      fun q hq => (Commute.inv_right (ha.2.2 q hq : Commute q a))⟩

theorem Vsub_le : Vsub p P ≤ P ⊓ layer Y := fun _ ha => ha.1

theorem isElemAbelian_Vsub : IsElemAbelian p (Vsub p P) :=
  (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_iff).2
    ⟨fun a ha b hb => hb.2.2 a (layer_inf_le_compKer ha.1), fun a ha => ha.2.1⟩

theorem conj_mem_Vsub {g v : Y} (hg : g ∈ P) (hv : v ∈ Vsub p P) : g * v * g⁻¹ ∈ Vsub p P := by
  refine ⟨⟨P.mul_mem (P.mul_mem hg hv.1.1) (P.inv_mem hg), ?_⟩, ?_, fun q hq => ?_⟩
  · exact conj_mem_layer g hv.1.2
  · rw [conj_pow, hv.2.1, mul_one, mul_inv_cancel]
  · have h1 := hv.2.2 (g⁻¹ * q * g) (by
      have := conj_mem_compKer (P.inv_mem hg) hq
      rwa [inv_inv] at this)
    calc q * (g * v * g⁻¹) = g * ((g⁻¹ * q * g) * v) * g⁻¹ := by group
      _ = g * (v * (g⁻¹ * q * g)) * g⁻¹ := by rw [h1]
      _ = g * v * g⁻¹ * q := by group

theorem card_Vsub (h : SplitCfg p P x) : p ^ p ≤ Nat.card (Vsub p P) := by
  have hcard : Nat.card (∀ C : ComponentIndex Y, ↥(omegaComp h C)) = p ^ p := by
    rw [Nat.card_pi]
    simp only [card_omegaComp h]
    rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, h.card_comp]
  let fam : (∀ C : ComponentIndex Y, ↥(omegaComp h C)) → ∀ C : ComponentIndex Y, ↥C.1 :=
    fun n C => ⟨(n C : Y), (omegaComp_le h C (n C).2).2⟩
  have hmem : ∀ n : (∀ C : ComponentIndex Y, ↥(omegaComp h C)), layerMul Y (fam n) ∈ Vsub p P := by
    intro n
    have hl : layerMul Y (fam n) ∈ layer Y := by rw [← layerMul_range]; exact ⟨fam n, rfl⟩
    have hP : layerMul Y (fam n) ∈ P :=
      layerMul_mem (fam n) fun C => (omegaComp_le h C (n C).2).1
    refine ⟨⟨hP, hl⟩, ?_, fun q hq => ?_⟩
    · have : (layerMul Y (fam n)) ^ p = layerMul Y ((fam n) ^ p) := (map_pow _ _ _).symm
      rw [this]
      have h1 : (fam n) ^ p = 1 := by
        funext C
        apply Subtype.ext
        exact (mem_omegaComp.mp (n C).2).2
      rw [h1, map_one]
    · have hc : layerMul Y (fam n) ∈ centralizer (compKer P : Set Y) :=
        layerMul_mem (H := centralizer (compKer P : Set Y)) (fam n) fun C =>
          mem_centralizer_iff.mpr fun q hq => omegaComp_central h C (n C).2 hq
      exact mem_centralizer_iff.mp hc q hq
  let Φ : (∀ C : ComponentIndex Y, ↥(omegaComp h C)) → ↥(Vsub p P) := fun n =>
    ⟨layerMul Y (fam n), hmem n⟩
  have hΦ : Function.Injective Φ := by
    intro n n' hnn
    have h1 : layerMul Y (fam n) = layerMul Y (fam n') := congrArg Subtype.val hnn
    have h2 := layerMul_injective h.centre h1
    funext C
    apply Subtype.ext
    have h3 := congrArg Subtype.val (congrFun h2 C)
    exact h3
  have := Nat.card_le_card_of_injective Φ hΦ
  rwa [hcard] at this

theorem W_eq_bot (h : SplitCfg p P x) {W : Subgroup Y} (hWQ : W ≤ compKer P)
    (hWx : ∀ w ∈ W, x * w * x⁻¹ ∈ W) (hWc : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w)
    (hWA : ∀ a ∈ P ⊓ layer Y, a ∈ W → a = 1) : W = ⊥ := by
  by_contra hne
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hp := h.prime
  have hWP : W ≤ P := hWQ.trans compKer_le
  obtain ⟨w0, hw0W, hw0p, hw01⟩ : ∃ w0 ∈ W, w0 ^ p = 1 ∧ w0 ≠ 1 := by
    haveI : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).2 hne
    have hWp : IsPGroup p ↥W := h.sylow.isPGroup.to_le hWP
    obtain ⟨m, hm, hmcard⟩ := hWp.nontrivial_iff_card.mp inferInstance
    have hdvd : p ∣ Nat.card ↥W := hmcard ▸ dvd_pow_self p hm.ne'
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥W) p hdvd
    have hord : orderOf (g : Y) = p := by rw [Subgroup.orderOf_coe]; exact hg
    refine ⟨g, g.2, by rw [← hord]; exact pow_orderOf_eq_one _, fun h1 => ?_⟩
    rw [h1, orderOf_one] at hord
    exact hp.one_lt.ne hord
  obtain ⟨V, hVdef⟩ : ∃ V, V = Vsub p P := ⟨_, rfl⟩
  have hVcard : p ^ p ≤ Nat.card V := hVdef ▸ card_Vsub h
  have hVA : V ≤ P ⊓ layer Y := hVdef ▸ Vsub_le
  have hVe : IsElemAbelian p V := hVdef ▸ isElemAbelian_Vsub
  have hVc : ∀ v ∈ V, ∀ q ∈ compKer P, q * v = v * q := fun v hv q hq => by
    rw [hVdef] at hv
    exact hv.2.2 q hq
  have hVx : ∀ v ∈ V, x * v * x⁻¹ ∈ V := fun v hv => by
    rw [hVdef] at hv ⊢
    exact conj_mem_Vsub h.x_mem hv
  let W1 : Subgroup Y := omega1 p W hWc
  have hW1e : IsElemAbelian p W1 := isElemAbelian_omega1
  have hW1x : ∀ w ∈ W1, x * w * x⁻¹ ∈ W1 := fun w hw =>
    ⟨hWx w hw.1, by rw [conj_pow, hw.2, mul_one, mul_inv_cancel]⟩
  have hW1card : p ≤ Nat.card W1 := by
    have hle : zpowers w0 ≤ W1 := zpowers_le.mpr ⟨hw0W, hw0p⟩
    have h1 := Subgroup.card_le_of_le hle
    have hord : orderOf w0 = p := orderOf_eq_prime hw0p hw01
    rwa [Nat.card_zpowers, hord] at h1
  have hVW1 : ∀ a ∈ V, ∀ b ∈ W1, a * b = b * a := fun a ha b hb =>
    (hVc a ha b (hWQ hb.1)).symm
  have hE : IsElemAbelian p (V ⊔ W1) := hVe.sup_of_commute hW1e hVW1
  have hEP : V ⊔ W1 ≤ P := sup_le (hVA.trans inf_le_left) (omega1_le.trans hWP)
  have hxE : x ∈ normalizer ((V ⊔ W1 : Subgroup Y) : Set Y) := by
    refine CFSG.Goldschmidt.Sec82.mem_normalizer_of_conj_mem fun e he => ?_
    have hle : V ⊔ W1 ≤ (V ⊔ W1).comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (fun v hv => ?_) (fun w hw => ?_)
      · exact mem_sup_left (hVx v hv)
      · exact mem_sup_right (hW1x w hw)
    exact hle he
  have hbound := h.rank_le _ hEP hE hxE
  have hinj : Function.Injective (fun vw : ↥V × ↥W1 =>
      (⟨(vw.1 : Y) * vw.2, mul_mem (mem_sup_left vw.1.2) (mem_sup_right vw.2.2)⟩ : ↥(V ⊔ W1))) := by
    rintro ⟨v, w⟩ ⟨v', w'⟩ hvw
    have h1 : (v : Y) * w = v' * w' := congrArg Subtype.val hvw
    have h2 : (v' : Y)⁻¹ * v = w' * (w : Y)⁻¹ := by
      calc (v' : Y)⁻¹ * v = (v' : Y)⁻¹ * (v * w) * (w : Y)⁻¹ := by group
        _ = (v' : Y)⁻¹ * (v' * w') * (w : Y)⁻¹ := by rw [h1]
        _ = w' * (w : Y)⁻¹ := by group
    have h3 : (v' : Y)⁻¹ * v = 1 :=
      hWA _ (hVA (V.mul_mem (V.inv_mem v'.2) v.2))
        (by rw [h2]; exact W.mul_mem (omega1_le w'.2) (W.inv_mem (omega1_le w.2)))
    have hv : (v' : Y) = v := inv_mul_eq_one.mp h3
    have hw : (w : Y) = w' := by
      rw [← hv] at h1
      exact mul_left_cancel h1
    have hv2 : v = v' := Subtype.ext hv.symm
    have hw2 : w = w' := Subtype.ext hw
    rw [hv2, hw2]
  have hcardE : Nat.card ↥V * Nat.card ↥W1 ≤ Nat.card ↥(V ⊔ W1) := by
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_prod] at this
  have h5 : p ^ p * p ≤ Nat.card ↥(V ⊔ W1) := (Nat.mul_le_mul hVcard hW1card).trans hcardE
  have h6 : 0 < p ^ p := pow_pos hp.pos p
  have h7 : p ^ p * 2 ≤ p ^ p * p := Nat.mul_le_mul_left (p ^ p) hp.two_le
  omega

theorem compKer_le_layer (hsplit : KFactSylowSplit) (h7131 : GL83.I_7_13_1)
    (h : SplitCfg p P x) : compKer P ≤ layer Y := by
  obtain ⟨W, hWQ, hWx, hWc, hWA, hdec⟩ := exists_complement hsplit h7131 h
  have hW : W = ⊥ := W_eq_bot h hWQ hWx hWc hWA
  intro q hq
  obtain ⟨a, ha, w, hw, rfl⟩ := hdec q hq
  rw [hW, Subgroup.mem_bot] at hw
  rw [hw, mul_one]
  exact ha.2

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplit
