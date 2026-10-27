module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma138
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1315b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1245b
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevToolsK
public import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
public import CFSG.LocalAnalysis.GL83PartI.I_22_6.Gen

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs27

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut)

section Basics

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem elem_mul_comm {B : Subgroup X} (hB : IsElemAbelian p B) {a b : X} (ha : a ∈ B)
    (hb : b ∈ B) : a * b = b * a := by
  have h := hB.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val h

theorem card_eq_pow_pRank (hp : p.Prime) {B : Subgroup X} (hB : IsElemAbelian p B) :
    Nat.card B = p ^ CFSG.Open.pRank p B := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup hB).exists_card_eq
  have h1 : k ≤ CFSG.Open.pRank p B := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB hk
  have h2 : CFSG.Open.pRank p B ≤ k :=
    CFSG.SectionRank.pRank_le hp.one_lt fun E hEB _ => hk ▸ Subgroup.card_le_of_le hEB
  rw [hk, le_antisymm h1 h2]

theorem le_centralizer_of_le {E U : Subgroup X} (hE : IsElemAbelian p E) (hUE : U ≤ E) :
    E ≤ Subgroup.centralizer (U : Set X) := by
  intro e he
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact elem_mul_comm hE (hUE hu) he

theorem three_le_pRank_of_scp (hp : p.Prime) {E A : Subgroup X} (hE : IsSCp p ⊤ E)
    (hA : IsSCp p ⊤ A) (hEA : E ≠ A) (hr : 2 ≤ CFSG.Open.pRank p (E ⊓ A)) :
    3 ≤ CFSG.Open.pRank p E := by
  have hI : IsElemAbelian p (E ⊓ A) := CFSG.Open.IsElemAbelian.mono hE.2.1 inf_le_left
  have hlt : E ⊓ A < E := by
    refine lt_of_le_of_ne inf_le_left fun h => hEA ?_
    have hEleA : E ≤ A := h ▸ inf_le_right
    exact (hE.2.2 A le_top hA.2.1 hEleA).symm
  have hcard : Nat.card (E ⊓ A : Subgroup X) < Nat.card E := Subgroup.card_lt_of_lt hlt
  rw [card_eq_pow_pRank hp hI, card_eq_pow_pRank hp hE.2.1] at hcard
  have := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hcard
  omega

theorem isKConnectedIn_self (hp : p.Prime) {E : Subgroup X} (hE : IsElemAbelian p E)
    (hE3 : 3 ≤ CFSG.Open.pRank p E) : IsKConnectedIn p 3 ⊤ E E := by
  have hc : p ^ 3 ≤ Nat.card E := by
    rw [card_eq_pow_pRank hp hE]
    exact Nat.pow_le_pow_right hp.pos hE3
  exact ⟨le_top, hE, hc, le_top, hE, hc, Or.inl (le_centralizer_of_le hE le_rfl)⟩

theorem isKConnectedIn_of_inter (hp : p.Prime) {E A : Subgroup X} (hE : IsElemAbelian p E)
    (hA : IsElemAbelian p A) (h3 : 3 ≤ CFSG.Open.pRank p (E ⊓ A)) : IsKConnectedIn p 3 ⊤ E A := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hI : IsElemAbelian p (E ⊓ A) := CFSG.Open.IsElemAbelian.mono hE inf_le_left
  have hIc : Nat.card (E ⊓ A : Subgroup X) = p ^ CFSG.Open.pRank p (E ⊓ A) := card_eq_pow_pRank hp hI
  obtain ⟨U₀, hU₀⟩ := Sylow.exists_subgroup_card_pow_prime p (G := ↥(E ⊓ A)) (n := 3)
    (by rw [hIc]; exact pow_dvd_pow p h3)
  set U : Subgroup X := U₀.map (E ⊓ A).subtype with hUdef
  have hUI : U ≤ E ⊓ A := Subgroup.map_subtype_le U₀
  have hUc : Nat.card U = p ^ 3 := by
    rw [hUdef, Subgroup.card_map_of_injective (E ⊓ A).subtype_injective, hU₀]
  have hUel : IsElemAbelian p U := CFSG.Open.IsElemAbelian.mono hI hUI
  have hEc : p ^ 3 ≤ Nat.card E := by
    calc p ^ 3 = Nat.card U := hUc.symm
      _ ≤ Nat.card E := Subgroup.card_le_of_le (hUI.trans inf_le_left)
  have hAc : p ^ 3 ≤ Nat.card A := by
    calc p ^ 3 = Nat.card U := hUc.symm
      _ ≤ Nat.card A := Subgroup.card_le_of_le (hUI.trans inf_le_right)
  refine ⟨le_top, hE, hEc, le_top, hA, hAc, Or.inr ⟨U, U, ⟨le_top, hUel, hUc⟩, ⟨le_top, hUel, hUc⟩,
    le_centralizer_of_le hE (hUI.trans inf_le_left), Relation.ReflTransGen.refl, ?_⟩⟩
  exact Subgroup.le_centralizer_iff.1 (le_centralizer_of_le hA (hUI.trans inf_le_right))

theorem normalizer_le_glbCore' {Q P : Subgroup X} (hQP : Q ≤ P) (hQ : 2 ≤ CFSG.Open.pRank p Q) :
    Subgroup.normalizer (Q : Set X) ≤ GLBCore p 2 P :=
  le_sSup ⟨Q, hQP, hQ, rfl⟩

theorem le_glbCore_of_inter {E A : Subgroup X} (hA : IsElemAbelian p A)
    (hr : 2 ≤ CFSG.Open.pRank p (E ⊓ A)) : A ≤ GLBCore p 2 E :=
  (le_centralizer_of_le hA inf_le_right).trans ((Subgroup.centralizer_le_normalizer _).trans
    (normalizer_le_glbCore' inf_le_left hr))

theorem kStar_le_glbCore {E A K : Subgroup X} (hA : IsElemAbelian p A)
    (hr : 2 ≤ CFSG.Open.pRank p (E ⊓ A)) (hK : K ≤ GLBCore p 2 E) :
    (⨆ g ∈ A, GLBConj g K) ≤ GLBCore p 2 E := by
  refine iSup₂_le fun g hg => ?_
  have hgΓ : g ∈ GLBCore p 2 E := le_glbCore_of_inter hA hr hg
  calc GLBConj g K ≤ GLBConj g (GLBCore p 2 E) := gLBConj_mono g hK
    _ = GLBCore p 2 E := gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hgΓ)

end Basics

section Family

variable {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem dvd_card_of_ne_bot {C : Subgroup X} (hC : IsElemAbelian p C) (hne : C ≠ ⊥) :
    p ∣ Nat.card C := by
  have hc := card_eq_pow_pRank (Fact.out : p.Prime) hC
  have h0 : CFSG.Open.pRank p C ≠ 0 := by
    intro h0
    apply hne
    rw [h0, pow_zero] at hc
    exact Subgroup.eq_bot_of_card_eq C hc
  rw [hc]
  exact dvd_pow_self p h0

open GL83.CompFam in
theorem le_glbCore_of_not_le_normalizer {E K : Subgroup X} (hE : IsElemAbelian p E)
    (hE3 : 3 ≤ CFSG.Open.pRank p E) (hKc : IsComponentOf K ⊤)
    (hC : E ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥) (hN : ¬ E ≤ Subgroup.normalizer (K : Set X)) :
    K ≤ GLBCore p 2 E := by
  have hp := (Fact.out : p.Prime)
  have hF := isFam_conjSet hE hKc
  have hK₀ := mem_conjSet_self E K
  have hCel : IsElemAbelian p (cen E K) := CFSG.Open.IsElemAbelian.mono hE inf_le_left
  have hCd : p ∣ Nat.card (cen E K) := dvd_card_of_ne_bot hCel hC
  have hAB : stab E K ≤ E := inf_le_left
  obtain ⟨i, hi⟩ := GL83.CompFam.exists_card_eq_pow (elem_mono hE hAB)
  obtain ⟨j, hj⟩ := GL83.CompFam.exists_card_eq_pow hE
  have hjr : j = CFSG.Open.pRank p E := by
    have h := card_eq_pow_pRank hp hE
    rw [hj] at h
    exact Nat.pow_right_injective hp.two_le h
  have hij : i < j := by
    have hle : i ≤ j := by
      have h := Subgroup.card_le_of_le hAB
      rw [hi, hj] at h
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h
    refine lt_of_le_of_ne hle fun h => hN ?_
    have hAeq : stab E K = E := Subgroup.eq_of_le_of_card_ge hAB (by rw [hi, hj, h])
    exact (le_of_eq hAeq.symm).trans inf_le_right
  have hnormΓ : normJoin hF K ≤ GLBCore p 2 E := by
    refine iSup₂_le fun M hM => ?_
    obtain ⟨b, hb, hbA, K', hK', hbA', rfl⟩ := hM
    exact hF.normSub_le_gamma hK₀ hCd hK' hb hbA'
  have hlay : GL83.CompFam.layer (conjSet E K) ≤ GLBCore p 2 E := by
    by_cases h2 : i + 2 ≤ j
    · refine (hF.layer_le_normJoin_two hK₀ ?_).trans hnormΓ
      rw [hi, hj]
      calc p ^ 2 * p ^ i = p ^ (2 + i) := (pow_add p 2 i).symm
        _ ≤ p ^ j := Nat.pow_le_pow_right hp.pos (by omega)
    · have hj' : j = i + 1 := by omega
      have hB1 : Nat.card E = p * Nat.card (stab E K) := by
        rw [hi, hj, hj', pow_succ']
      by_cases hAC : stab E K ≤ cen E K
      · have hCeq : cen E K = stab E K := le_antisymm (cen_le_stab E K) hAC
        have hCr : 2 ≤ CFSG.Open.pRank p (cen E K) := by
          have h := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hCel (k := i) (by rw [hCeq, hi])
          omega
        have h1 : GL83.CompFam.layer (conjSet E K) ≤ Subgroup.centralizer ((cen E K : Subgroup X) : Set X) :=
          Subgroup.le_centralizer_iff.1 (hF.cen_le_centralizer_of_le_layer hK₀ le_rfl)
        exact h1.trans ((Subgroup.centralizer_le_normalizer _).trans
          (normalizer_le_glbCore' inf_le_left hCr))
      · exact (hF.layer_le_normJoin_one hK₀ hB1 hAC).trans hnormΓ
  exact (le_layer hK₀).trans hlay

end Family

section Layer

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem le_glaLayer_top {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    K ≤ GLALayer (⊤ : Subgroup X) :=
  le_sSup hK

theorem inf_centralizer_ne_bot {E A K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hc : Subgroup.centralizer ((GLALayer (⊤ : Subgroup X) : Subgroup X) : Set X) ⊓ (E ⊓ A) ≠ ⊥) :
    E ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ := by
  obtain ⟨⟨c, hc1⟩, hcne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc
  refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨c, (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hc1).2).1,
    Subgroup.centralizer_le (le_glaLayer_top hK) (Subgroup.mem_inf.1 hc1).1⟩, ?_⟩
  intro h
  have hc1' : c = 1 := by simpa using congrArg Subtype.val h
  exact hcne (Subtype.ext hc1')

end Layer

section Core

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem one_le_pRank_of_ne_bot (hp : p.Prime) {C : Subgroup X} (hC : IsElemAbelian p C)
    (hne : C ≠ ⊥) : 1 ≤ CFSG.Open.pRank p C := by
  have hc := card_eq_pow_pRank hp hC
  by_contra h0
  apply hne
  rw [show CFSG.Open.pRank p C = 0 by omega, pow_zero] at hc
  exact Subgroup.eq_bot_of_card_eq C hc

theorem le_glbCore_of_cen {E K : Subgroup X}
    (h2 : 2 ≤ CFSG.Open.pRank p (E ⊓ Subgroup.centralizer (K : Set X))) : K ≤ GLBCore p 2 E :=
  (Subgroup.le_centralizer_iff.1 inf_le_right).trans ((Subgroup.centralizer_le_normalizer _).trans
    (normalizer_le_glbCore' inf_le_left h2))

end Core

section AbelianSylow

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem isElemAbelian_sup_of_commute {H₁ H₂ : Subgroup X} (h₁ : IsElemAbelian p H₁)
    (h₂ : IsElemAbelian p H₂) (hc : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x) :
    IsElemAbelian p (H₁ ⊔ H₂) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun z hz => ?_⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := (GL83.CompFam.mem_sup_of_commute hc).1 a.2
    obtain ⟨x', hx', y', hy', hxy'⟩ := (GL83.CompFam.mem_sup_of_commute hc).1 b.2
    show (a : X) * b = b * a
    rw [← hxy, ← hxy']
    have c1 : Commute x x' := elem_mul_comm h₁ hx hx'
    have c2 : Commute x y' := hc x hx y' hy'
    have c3 : Commute y x' := (hc x' hx' y hy).symm
    have c4 : Commute y y' := elem_mul_comm h₂ hy hy'
    exact ((c1.mul_right c2).mul_left (c3.mul_right c4)).eq
  · obtain ⟨x, hx, y, hy, rfl⟩ := (GL83.CompFam.mem_sup_of_commute hc).1 hz
    rw [(show Commute x y from hc x hx y hy).mul_pow, h₁.2 x hx, h₂.2 y hy, one_mul]

theorem isElemAbelian_zpowers' {k : X} (hk : k ^ p = 1) : IsElemAbelian p (Subgroup.zpowers k) := by
  refine ⟨inferInstance, fun x hx => ?_⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]

theorem inf_centralizer_self_eq_bot {K : Subgroup X} (hZ : Subgroup.center ↥K = ⊥) :
    K ⊓ Subgroup.centralizer (K : Set X) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.1 hx
  have h : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxC g g.2)
  rw [hZ, Subgroup.mem_bot] at h
  exact congrArg Subtype.val h

theorem innerAut_normal_local (Y : Type*) [Group Y] : (innerAut Y).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨y, rfl⟩ := hn
  refine ⟨g y, ?_⟩
  ext z
  simp [MulAut.conj_apply]

theorem exists_inner_of_not_dvd [Fact p.Prime] {K : Subgroup X}
    (hOut : ¬ p ∣ (innerAut ↥K).index) {e : X} (heN : e ∈ Subgroup.normalizer (K : Set X))
    (hep : e ^ p = 1) : ∃ k ∈ K, ∀ x ∈ K, e * x * e⁻¹ = k * x * k⁻¹ := by
  have hp := (Fact.out : p.Prime)
  haveI : (innerAut ↥K).Normal := innerAut_normal_local ↥K
  set σ : MulAut ↥K := K.normalizerMonoidHom ⟨e, heN⟩ with hσ
  have hσp : σ ^ p = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨e, heN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ p = 1 := Subtype.ext (by simpa using hep)
    rw [this, map_one]
  have hmk : (QuotientGroup.mk σ : MulAut ↥K ⧸ innerAut ↥K) = 1 := by
    have h1 : orderOf (QuotientGroup.mk σ : MulAut ↥K ⧸ innerAut ↥K) ∣ p := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← QuotientGroup.mk_pow, hσp, QuotientGroup.mk_one]
    have h2 : orderOf (QuotientGroup.mk σ : MulAut ↥K ⧸ innerAut ↥K) ∣ (innerAut ↥K).index :=
      orderOf_dvd_natCard _
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · exact orderOf_eq_one_iff.1 h
    · exact absurd (h ▸ h2) hOut
  have hσI : σ ∈ innerAut ↥K := (QuotientGroup.eq_one_iff σ).1 hmk
  obtain ⟨k, hk⟩ := hσI
  refine ⟨k, k.2, fun x hx => ?_⟩
  have h := congrArg (fun f : MulAut ↥K => ((f ⟨x, hx⟩ : ↥K) : X)) hk
  simp only [MulAut.conj_apply] at h
  rw [hσ] at h
  exact h.symm

theorem eq_inf_sup_inf_of_inner [Fact p.Prime] {E K : Subgroup X} (hE : IsSCp p ⊤ E)
    (hEN : E ≤ Subgroup.normalizer (K : Set X)) (hZ : K ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (hinner : ∀ e ∈ E, ∃ k ∈ K, ∀ x ∈ K, e * x * e⁻¹ = k * x * k⁻¹) :
    E = (E ⊓ K) ⊔ (E ⊓ Subgroup.centralizer (K : Set X)) := by
  refine le_antisymm (fun e he => ?_) (sup_le inf_le_left inf_le_left)
  obtain ⟨k, hkK, hk⟩ := hinner e he
  set c := k⁻¹ * e with hc
  have hcC : c ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := hk x hx
    calc x * c = k⁻¹ * (k * x * k⁻¹) * e := by rw [hc]; group
      _ = k⁻¹ * (e * x * e⁻¹) * e := by rw [h1]
      _ = c * x := by rw [hc]; group
  have hkE : ∀ e' ∈ E, e' * k = k * e' := by
    intro e' he'
    have hk' : e' * k * e'⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hEN he') k).1 hkK
    have hc' : e' * c * e'⁻¹ ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : e'⁻¹ * x * e' ∈ K := by
        have := (Subgroup.mem_normalizer_iff.1 (hEN (E.inv_mem he')) x).1 hx
        simpa using this
      have h2 := Subgroup.mem_centralizer_iff.1 hcC _ hx'
      calc x * (e' * c * e'⁻¹) = e' * ((e'⁻¹ * x * e') * c) * e'⁻¹ := by group
        _ = e' * (c * (e'⁻¹ * x * e')) * e'⁻¹ := by rw [h2]
        _ = e' * c * e'⁻¹ * x := by group
    have hee : e' * e * e'⁻¹ = e := by rw [elem_mul_comm hE.2.1 he' he]; group
    have heq : (e' * k * e'⁻¹) * (e' * c * e'⁻¹) = k * c := by
      calc (e' * k * e'⁻¹) * (e' * c * e'⁻¹) = e' * (k * c) * e'⁻¹ := by group
        _ = e' * e * e'⁻¹ := by rw [hc]; group
        _ = e := hee
        _ = k * c := by rw [hc]; group
    have hmem : k⁻¹ * (e' * k * e'⁻¹) ∈ K ⊓ Subgroup.centralizer (K : Set X) := by
      refine ⟨K.mul_mem (K.inv_mem hkK) hk', ?_⟩
      have e2 : k⁻¹ * (e' * k * e'⁻¹) = c * (e' * c * e'⁻¹)⁻¹ := by
        calc k⁻¹ * (e' * k * e'⁻¹) =
            k⁻¹ * ((e' * k * e'⁻¹) * (e' * c * e'⁻¹)) * (e' * c * e'⁻¹)⁻¹ := by group
          _ = k⁻¹ * (k * c) * (e' * c * e'⁻¹)⁻¹ := by rw [heq]
          _ = c * (e' * c * e'⁻¹)⁻¹ := by group
      rw [e2]
      exact Subgroup.mul_mem _ hcC (Subgroup.inv_mem _ hc')
    rw [hZ, Subgroup.mem_bot] at hmem
    have h3 : e' * k * e'⁻¹ = k := (inv_mul_eq_one.1 hmem).symm
    calc e' * k = e' * k * e'⁻¹ * e' := by group
      _ = k * e' := by rw [h3]
  have hkp : k ^ p = 1 := by
    have hcomm : Commute k c := Subgroup.mem_centralizer_iff.1 hcC k hkK
    have h1 : (k * c) ^ p = 1 := by rw [hc, mul_inv_cancel_left]; exact hE.2.1.2 e he
    rw [hcomm.mul_pow] at h1
    have hmem : k ^ p ∈ K ⊓ Subgroup.centralizer (K : Set X) := by
      refine ⟨K.pow_mem hkK p, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h1]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hcC p)
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  have hkEmem : k ∈ E := by
    have hel : IsElemAbelian p (E ⊔ Subgroup.zpowers k) := by
      refine isElemAbelian_sup_of_commute hE.2.1 (isElemAbelian_zpowers' hkp) fun x hx y hy => ?_
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact (Commute.zpow_right (show Commute x k from hkE x hx) n).eq
    have heq := hE.2.2 (E ⊔ Subgroup.zpowers k) le_top hel le_sup_left
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers k)
  have hcE : c ∈ E := E.mul_mem (E.inv_mem hkEmem) he
  have e3 : e = k * c := by rw [hc]; group
  rw [e3]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hkEmem, hkK⟩) (Subgroup.mem_sup_right ⟨hcE, hcC⟩)

theorem mem_of_pow_eq_one_of_maximal [Fact p.Prime] {C Q : Subgroup X} (hQ : IsPGroup p ↥Q)
    (hCQ : C ≤ Q) (hCc : Nat.card C = p) (hCel : IsElemAbelian p C)
    (hmax : ∀ F : Subgroup X, F ≤ Q → IsElemAbelian p F → C ≤ F → F = C) :
    ∀ x ∈ Q, x ^ p = 1 → x ∈ C := by
  have hp := (Fact.out : p.Prime)
  have hCne : C ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hCc
    exact hp.one_lt.ne hCc
  haveI : Nontrivial ↥Q := by
    obtain ⟨⟨c, hc⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hCne
    refine ⟨⟨⟨c, hCQ hc⟩, 1, fun h => hc1 (Subtype.ext ?_)⟩⟩
    simpa using congrArg Subtype.val h
  haveI := hQ.center_nontrivial
  have hZp : IsPGroup p ↥(Subgroup.center ↥Q) := hQ.to_subgroup _
  obtain ⟨n, hn⟩ := hZp.exists_card_eq
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Nat.card_eq_one_iff_unique] at hn
    obtain ⟨⟨a, b, hab⟩⟩ := (inferInstance : Nontrivial ↥(Subgroup.center ↥Q))
    exact hab (hn.1.elim a b)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥Q)) p
    (by rw [hn]; exact dvd_pow_self p hn0)
  set z0 : X := ((z : ↥Q) : X) with hz0
  have hz0p : z0 ^ p = 1 := by
    have : z ^ p = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    simpa [hz0] using congrArg (fun w : ↥(Subgroup.center ↥Q) => ((w : ↥Q) : X)) this
  have hz01 : z0 ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext (Subtype.ext h)
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hz0c : ∀ y ∈ Q, y * z0 = z0 * y := by
    intro y hy
    have := Subgroup.mem_center_iff.1 z.2 ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hz0Q : z0 ∈ Q := (z : ↥Q).2
  have hzC : z0 ∈ C := by
    have hel : IsElemAbelian p (C ⊔ Subgroup.zpowers z0) := by
      refine isElemAbelian_sup_of_commute hCel (isElemAbelian_zpowers' hz0p) fun x hx y hy => ?_
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact (Commute.zpow_right (show Commute x z0 from hz0c x (hCQ hx)) m).eq
    have heq := hmax _ (sup_le hCQ (Subgroup.zpowers_le.2 hz0Q)) hel le_sup_left
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z0)
  have hCz : C = Subgroup.zpowers z0 := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzC) ?_).symm
    rw [hCc, Nat.card_zpowers, orderOf_eq_prime hz0p hz01]
  intro x hxQ hxp
  have hel : IsElemAbelian p (C ⊔ Subgroup.zpowers x) := by
    refine isElemAbelian_sup_of_commute hCel (isElemAbelian_zpowers' hxp) fun c hc y hy => ?_
    rw [hCz] at hc
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    obtain ⟨m', rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.zpow_left (show Commute z0 x from (hz0c x hxQ).symm) m).zpow_right m').eq
  have heq := hmax _ (sup_le hCQ (Subgroup.zpowers_le.2 hxQ)) hel le_sup_left
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

theorem false_of_abelian_sylow [Fact p.Prime] (hO : GLAPPrimeCore p X = ⊥) {E A K : Subgroup X}
    (hKc : IsComponentOf K ⊤) (hE : IsSCp p ⊤ E) (hA : IsSCp p ⊤ A) (hEA : E ≠ A)
    (hEAp : IsPGroup p ↥(E ⊔ A)) (hN : E ≤ Subgroup.normalizer (K : Set X))
    (hC1 : CFSG.Open.pRank p (E ⊓ Subgroup.centralizer (K : Set X)) = 1)
    (hE3 : CFSG.Open.pRank p E = 3) (hOut : ¬ p ∣ (innerAut ↥K).index)
    (hab : ∀ P : Sylow p ↥K, IsMulCommutative ↥(P : Subgroup ↥K)) : False := by
  have hp := (Fact.out : p.Prime)
  have hZ : Subgroup.center ↥K = ⊥ := by
    have hnd : ¬ p ∣ Nat.card (Subgroup.center ↥K) := fun hd =>
      GL83.not_isMulCommutative_sylow_of_perfect hKc.2.2.1 hd default (hab default)
    have hsn : IsSubnormal ((Subgroup.center ↥K).map K.subtype) ⊤ := by
      refine IsSubnormal.step (M := K) (Subgroup.map_subtype_le _) ?_ hKc.2.1
      rw [show ((Subgroup.center ↥K).map K.subtype).subgroupOf K = Subgroup.center ↥K from
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective _]
      infer_instance
    have hcop : Nat.Coprime p (Nat.card ((Subgroup.center ↥K).map K.subtype)) := by
      rw [Subgroup.card_map_of_injective K.subtype_injective]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
    have h0 := GL83.CompFam.eq_bot_of_isSubnormal_of_coprime hp hO hsn hcop
    exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 h0
  have hKC := inf_centralizer_self_eq_bot hZ
  set C := E ⊓ Subgroup.centralizer (K : Set X) with hCdef
  have hEsplit := eq_inf_sup_inf_of_inner hE hN hKC fun e he =>
    exists_inner_of_not_dvd hOut (hN he) (hE.2.1.2 e he)
  have hEKel : IsElemAbelian p (E ⊓ K) := CFSG.Open.IsElemAbelian.mono hE.2.1 inf_le_left
  have hCel : IsElemAbelian p C := CFSG.Open.IsElemAbelian.mono hE.2.1 inf_le_left
  have hCc : Nat.card C = p := by rw [card_eq_pow_pRank hp hCel, hC1, pow_one]
  have hcommEKC : ∀ x ∈ E ⊓ K, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy).2 x (Subgroup.mem_inf.1 hx).2
  have hEKc : Nat.card (E ⊓ K : Subgroup X) = p ^ 2 := by
    have hd : (E ⊓ K) ⊓ C = ⊥ := le_bot_iff.1 (hKC ▸
      le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
    have h1 := GL83.CompFam.card_sup_of_commute_of_inf_eq_bot hcommEKC hd
    rw [← hEsplit, card_eq_pow_pRank hp hE.2.1, hE3, hCc] at h1
    have h2 : Nat.card (E ⊓ K : Subgroup X) * p = p ^ 2 * p := by rw [← h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hp.pos h2
  set Q := Subgroup.centralizer (K : Set X) ⊓ (E ⊔ A) with hQdef
  have hQp : IsPGroup p ↥Q := hEAp.to_le inf_le_right
  have hCQ : C ≤ Q := le_inf inf_le_right (inf_le_left.trans le_sup_left)
  have hmax : ∀ F : Subgroup X, F ≤ Q → IsElemAbelian p F → C ≤ F → F = C := by
    intro F hFQ hFel hCF
    have hFC : F ≤ Subgroup.centralizer (K : Set X) := hFQ.trans inf_le_left
    have hel : IsElemAbelian p ((E ⊓ K) ⊔ F) := isElemAbelian_sup_of_commute hEKel hFel
      fun x hx y hy => Subgroup.mem_centralizer_iff.1 (hFC hy) x (Subgroup.mem_inf.1 hx).2
    have hle : E ≤ (E ⊓ K) ⊔ F := hEsplit.le.trans (sup_le_sup_left hCF _)
    have heq := hE.2.2 _ le_top hel hle
    refine le_antisymm (fun x hx => ?_) hCF
    have hxE : x ∈ E := heq ▸ (Subgroup.mem_sup_right hx)
    exact ⟨hxE, hFC hx⟩
  have hQ1 := mem_of_pow_eq_one_of_maximal hQp hCQ hCc hCel hmax
  have hAN : A ≤ Subgroup.normalizer (K : Set X) := by
    intro a ha
    by_contra hna
    have hKa : GL83.CompFam.cj a K ≠ K := fun h => hna (GL83.CompFam.cj_eq_iff_mem_normalizer.1 h)
    have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
      (GL83.CompFam.isComponentOf_cj hKc a) hKc hKa
    have hKaC : GL83.CompFam.cj a K ≤ Subgroup.centralizer (K : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    have hmap : (E ⊓ K).map (MulAut.conj a).toMonoidHom ≤ C := by
      rintro _ ⟨y, hy, rfl⟩
      have hyE := (Subgroup.mem_inf.1 hy).1
      have hyK := (Subgroup.mem_inf.1 hy).2
      refine hQ1 _ ⟨hKaC (GL83.CompFam.mul_mem_cj hyK), ?_⟩ ?_
      · exact (E ⊔ A).mul_mem ((E ⊔ A).mul_mem (Subgroup.mem_sup_right ha)
          (Subgroup.mem_sup_left hyE)) ((E ⊔ A).inv_mem (Subgroup.mem_sup_right ha))
      · show ((MulAut.conj a) y) ^ p = 1
        rw [← map_pow, hEKel.2 y hy, map_one]
    have hcard := Subgroup.card_le_of_le hmap
    rw [Subgroup.card_map_of_injective (MulAut.conj a).injective, hEKc, hCc] at hcard
    have h2 := hp.two_le
    have : p * 2 ≤ p * p := Nat.mul_le_mul_left p h2
    nlinarith
  have hAsplit := eq_inf_sup_inf_of_inner hA hAN hKC fun e he =>
    exists_inner_of_not_dvd hOut (hAN he) (hA.2.1.2 e he)
  have hACC : A ⊓ Subgroup.centralizer (K : Set X) ≤ C := fun x hx =>
    hQ1 x ⟨(Subgroup.mem_inf.1 hx).2, Subgroup.mem_sup_right (Subgroup.mem_inf.1 hx).1⟩
      (hA.2.1.2 x (Subgroup.mem_inf.1 hx).1)
  have hcommK : ∀ x ∈ E ⊓ K, ∀ y ∈ A ⊓ K, x * y = y * x := by
    have hR : IsPGroup p ↥((K ⊓ (E ⊔ A)).subgroupOf K) :=
      (hEAp.to_le inf_le_right).comap_of_injective K.subtype K.subtype_injective
    obtain ⟨P, hRP⟩ := hR.exists_le_sylow
    intro x hx y hy
    have hx' : (⟨x, (Subgroup.mem_inf.1 hx).2⟩ : ↥K) ∈ (P : Subgroup ↥K) :=
      hRP (Subgroup.mem_subgroupOf.2 ⟨(Subgroup.mem_inf.1 hx).2,
        Subgroup.mem_sup_left (Subgroup.mem_inf.1 hx).1⟩)
    have hy' : (⟨y, (Subgroup.mem_inf.1 hy).2⟩ : ↥K) ∈ (P : Subgroup ↥K) :=
      hRP (Subgroup.mem_subgroupOf.2 ⟨(Subgroup.mem_inf.1 hy).2,
        Subgroup.mem_sup_right (Subgroup.mem_inf.1 hy).1⟩)
    have h := (hab P).is_comm.comm ⟨_, hx'⟩ ⟨_, hy'⟩
    exact congrArg (fun z : ↥(P : Subgroup ↥K) => ((z : ↥K) : X)) h
  have hT1 : IsElemAbelian p ((E ⊓ K) ⊔ (A ⊓ K)) :=
    isElemAbelian_sup_of_commute hEKel (CFSG.Open.IsElemAbelian.mono hA.2.1 inf_le_left) hcommK
  have hT : IsElemAbelian p (((E ⊓ K) ⊔ (A ⊓ K)) ⊔ C) := isElemAbelian_sup_of_commute hT1 hCel
    fun x hx y hy => Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy).2 x
      ((sup_le inf_le_right inf_le_right : (E ⊓ K) ⊔ (A ⊓ K) ≤ K) hx)
  have hET : E ≤ ((E ⊓ K) ⊔ (A ⊓ K)) ⊔ C := hEsplit.le.trans (sup_le_sup_right le_sup_left C)
  have hAT : A ≤ ((E ⊓ K) ⊔ (A ⊓ K)) ⊔ C :=
    hAsplit.le.trans (sup_le (le_sup_right.trans le_sup_left) (hACC.trans le_sup_right))
  have hTE := hE.2.2 _ le_top hT hET
  exact hEA (hA.2.2 E le_top hE.2.1 (hTE ▸ hAT))

end AbelianSylow

@[expose] def Input27_3Core : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    GLAPPrimeCore p X = ⊥ → ∀ K : Subgroup X, GLAPComponent p ⊤ K →
    CFSG.LocalAnalysis.GLTheoremA.IsKHat ↥K →
    ∀ E A : Subgroup X, IsSCp p ⊤ E → IsSCp p ⊤ A → E ≠ A → IsPGroup p ↥(E ⊔ A) →
      CFSG.Open.pRank p (E ⊓ A) = 2 →
      Subgroup.centralizer ((GLALayer (⊤ : Subgroup X) : Subgroup X) : Set X) ⊓ (E ⊓ A) ≠ ⊥ →
      ¬ K ≤ GLBCore p 2 E → E ≤ Subgroup.normalizer (K : Set X) →
      CFSG.Open.pRank p (E ⊓ Subgroup.centralizer (K : Set X)) = 1 →
      CFSG.Open.pRank p E ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) + 1 →
      (CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ 2 →
        5 ≤ p ∧ CFSG.Open.pRank p E = 3 ∧ CFSG.Open.pRank p A = 3 ∧
          (p ∣ (innerAut ↥K).index ∨ ∃ P : Sylow p ↥K, ¬ IsMulCommutative ↥(P : Subgroup ↥K))) →
      (∃ Es : Subgroup X, IsSCp p ⊤ Es ∧ 3 ≤ CFSG.Open.pRank p Es ∧
          IsKConnectedIn p 3 ⊤ E Es ∧ K ≤ GLBCore p 2 Es) ∨
      IsKConnectedIn p 3 ⊤ E A ∨
      (∃ y ∈ GLBCore p 2 E, GLBConj y E = A) ∨
      (CFSG.Open.pRank p E = 3 ∧ 3 < CFSG.Open.pRank p A) ∨
      (p = 3 ∧ CFSG.Open.pRank p E = 3) ∨
      (p = 3 ∧ Nat.card E = 3 ^ 4 ∧ Nat.card A = 3 ^ 3 ∧ IsLTwoTwentySeven ↥K) ∨
      CFSG.HardMathSupport.Solomon.LocalBalance.IsCompLocallyBalanced p 1 A K

@[expose] def Input27_4Core : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    GLAPPrimeCore p X = ⊥ → ∀ K : Subgroup X, GLAPComponent p ⊤ K →
    CFSG.LocalAnalysis.GLTheoremA.IsKHat ↥K →
    ∀ E A : Subgroup X, IsSCp p ⊤ E → IsSCp p ⊤ A → E ≠ A → IsPGroup p ↥(E ⊔ A) →
      2 ≤ CFSG.Open.pRank p (E ⊓ A) →
      Subgroup.centralizer ((GLALayer (⊤ : Subgroup X) : Subgroup X) : Set X) ⊓ (E ⊓ A) ≠ ⊥ →
      ¬ (⨆ g ∈ A, GLBConj g K) ≤ GLBCore p 2 E → ¬ K ≤ GLBCore p 2 E →
      E ≤ Subgroup.normalizer (K : Set X) →
      CFSG.Open.pRank p (E ⊓ Subgroup.centralizer (K : Set X)) = 1 →
      CFSG.Open.pRank p E ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) + 1 →
      (CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ 2 →
        5 ≤ p ∧ CFSG.Open.pRank p E = 3 ∧ CFSG.Open.pRank p A = 3 ∧
          (p ∣ (innerAut ↥K).index ∨ ∃ P : Sylow p ↥K, ¬ IsMulCommutative ↥(P : Subgroup ↥K))) →
      ((⨆ g ∈ A, GLBConj g K) ≤ GLBCore p 2 E) ∨
      (∃ n : ℕ, IsAltType n (CFSG.HardMathSupport.Solomon.LocalBalance.barOf p K) ∧ ¬ p ∣ n) ∨
      (∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
          GLAPComponent p (GLAPLayer p ((⨆ g ∈ A, GLBConj g K) ⊓ Subgroup.centralizer ({a} : Set X))) J →
          IsLocallyOTwoBalancedWrtP p 1 (CFSG.HardMathSupport.Solomon.LocalBalance.barOf p J) ∨
            (p = 3 ∧ IsLTwoTwentySeven (CFSG.HardMathSupport.Solomon.LocalBalance.barOf p J) ∧
              IsCompLocallyOTwoBalanced p 1 A J)) ∨
      (CFSG.Open.pRank p E = 3 ∧ 3 < CFSG.Open.pRank p A) ∨ (p = 3 ∧ CFSG.Open.pRank p E = 3) ∨
      (p = 3 ∧ Nat.card E = 3 ^ 4 ∧ Nat.card A = 3 ^ 3 ∧ IsLTwoTwentySeven ↥K)

theorem five_le_of_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : 5 ≤ p := by
  have h2 := hp.two_le
  by_contra h
  interval_cases p
  · exact hp2 rfl
  · exact hp3 rfl
  · exact absurd hp (by norm_num)

theorem input27_3_of_core (h : Input27_3Core) : Input27_3 := by
  intro p hp hp2 X _ _ hXK hO K hK hKh E A hE hA hEA hEAp hr hc
  haveI : Fact p.Prime := ⟨hp⟩
  have hKc : IsComponentOf K ⊤ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i116n_isComponentOf_of_glaPComponent hO hK
  have hE3 : 3 ≤ CFSG.Open.pRank p E := three_le_pRank_of_scp hp hE hA hEA hr
  have hA3 : 3 ≤ CFSG.Open.pRank p A :=
    three_le_pRank_of_scp hp hA hE hEA.symm (by rwa [inf_comm])
  by_cases hKΓ : K ≤ GLBCore p 2 E
  · exact Or.inl ⟨E, hE, hE3, isKConnectedIn_self hp hE.2.1 hE3, hKΓ⟩
  by_cases hr3 : 3 ≤ CFSG.Open.pRank p (E ⊓ A)
  · exact Or.inr (Or.inl (isKConnectedIn_of_inter hp hE.2.1 hA.2.1 hr3))
  have hr2 : CFSG.Open.pRank p (E ⊓ A) = 2 := by omega
  have hCne := inf_centralizer_ne_bot hKc hc
  have hN : E ≤ Subgroup.normalizer (K : Set X) := by
    by_contra hN
    exact hKΓ (le_glbCore_of_not_le_normalizer hE.2.1 hE3 hKc hCne hN)
  have hC1 : CFSG.Open.pRank p (E ⊓ Subgroup.centralizer (K : Set X)) = 1 := by
    have h1 := one_le_pRank_of_ne_bot hp (CFSG.Open.IsElemAbelian.mono hE.2.1 inf_le_left) hCne
    have h2 : CFSG.Open.pRank p (E ⊓ Subgroup.centralizer (K : Set X)) ≤ 1 := by
      by_contra h2
      exact hKΓ (le_glbCore_of_cen (by omega))
    omega
  have hAut : CFSG.Open.pRank p E ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) + 1 := by
    by_contra h'
    exact hKΓ (GL83.I_22_5_proved X p hp hO K hKc E hE.2.1 (by omega) 2 (by omega) (by omega))
  by_cases hA2 : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ 2
  · have hE3' : CFSG.Open.pRank p E = 3 := by omega
    by_cases hAgt : 3 < CFSG.Open.pRank p A
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hE3', hAgt⟩)))
    by_cases hp3 : p = 3
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp3, hE3'⟩))))
    have hOS : p ∣ (innerAut ↥K).index ∨
        ∃ P : Sylow p ↥K, ¬ IsMulCommutative ↥(P : Subgroup ↥K) := by
      by_contra hcon
      push Not at hcon
      exact false_of_abelian_sylow hO hKc hE hA hEA hEAp hN hC1 hE3' hcon.1 hcon.2
    exact h p hp hp2 X hXK hO K hK hKh E A hE hA hEA hEAp hr2 hc hKΓ hN hC1 hAut
      (fun _ => ⟨five_le_of_prime hp hp2 hp3, hE3', by omega, hOS⟩)
  · exact h p hp hp2 X hXK hO K hK hKh E A hE hA hEA hEAp hr2 hc hKΓ hN hC1 hAut
      (fun h' => absurd h' hA2)

theorem input27_4_of_core (h : Input27_4Core) : Prop115.Input27_4 := by
  intro p hp hp2 X _ _ hXK hO K hK hKh E A hE hA hEA hEAp hr hc
  haveI : Fact p.Prime := ⟨hp⟩
  have hKc : IsComponentOf K ⊤ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i116n_isComponentOf_of_glaPComponent hO hK
  have hE3 : 3 ≤ CFSG.Open.pRank p E := three_le_pRank_of_scp hp hE hA hEA hr
  have hA3 : 3 ≤ CFSG.Open.pRank p A :=
    three_le_pRank_of_scp hp hA hE hEA.symm (by rwa [inf_comm])
  by_cases hKs : (⨆ g ∈ A, GLBConj g K) ≤ GLBCore p 2 E
  · exact Or.inl hKs
  have hKΓ : ¬ K ≤ GLBCore p 2 E := fun hKΓ => hKs (kStar_le_glbCore hA.2.1 hr hKΓ)
  have hCne := inf_centralizer_ne_bot hKc hc
  have hN : E ≤ Subgroup.normalizer (K : Set X) := by
    by_contra hN
    exact hKΓ (le_glbCore_of_not_le_normalizer hE.2.1 hE3 hKc hCne hN)
  have hC1 : CFSG.Open.pRank p (E ⊓ Subgroup.centralizer (K : Set X)) = 1 := by
    have h1 := one_le_pRank_of_ne_bot hp (CFSG.Open.IsElemAbelian.mono hE.2.1 inf_le_left) hCne
    have h2 : CFSG.Open.pRank p (E ⊓ Subgroup.centralizer (K : Set X)) ≤ 1 := by
      by_contra h2
      exact hKΓ (le_glbCore_of_cen (by omega))
    omega
  have hAut : CFSG.Open.pRank p E ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) + 1 := by
    by_contra h'
    exact hKΓ (GL83.I_22_5_proved X p hp hO K hKc E hE.2.1 (by omega) 2 (by omega) (by omega))
  by_cases hA2 : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ 2
  · have hE3' : CFSG.Open.pRank p E = 3 := by omega
    by_cases hAgt : 3 < CFSG.Open.pRank p A
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hE3', hAgt⟩)))
    by_cases hp3 : p = 3
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp3, hE3'⟩))))
    have hOS : p ∣ (innerAut ↥K).index ∨
        ∃ P : Sylow p ↥K, ¬ IsMulCommutative ↥(P : Subgroup ↥K) := by
      by_contra hcon
      push Not at hcon
      exact false_of_abelian_sylow hO hKc hE hA hEA hEAp hN hC1 hE3' hcon.1 hcon.2
    exact h p hp hp2 X hXK hO K hK hKh E A hE hA hEA hEAp hr hc hKs hKΓ hN hC1 hAut
      (fun _ => ⟨five_le_of_prime hp hp2 hp3, hE3', by omega, hOS⟩)
  · exact h p hp hp2 X hXK hO K hK hKh E A hE hA hEA hEAp hr hc hKs hKΓ hN hC1 hAut
      (fun h' => absurd h' hA2)


theorem input27_3Core_of_input27_3 (h : Input27_3) : Input27_3Core := by
  intro p hp hp2 X _ _ hXK hO K hK hKh E A hE hA hEA hEAp hr hc _ _ _ _ _
  exact h p hp hp2 X hXK hO K hK hKh E A hE hA hEA hEAp hr.ge hc

theorem input27_4Core_of_input27_4 (h : Prop115.Input27_4) : Input27_4Core := by
  intro p hp hp2 X _ _ hXK hO K hK hKh E A hE hA hEA hEAp hr hc _ _ _ _ _ _
  exact h p hp hp2 X hXK hO K hK hKh E A hE hA hEA hEAp hr hc

section Gamma

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem le_normalizer_of_le {B U : Subgroup X} (hB : IsElemAbelian p B) (hUB : U ≤ B) :
    B ≤ Subgroup.normalizer (U : Set X) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e : b * h * b⁻¹ = h := by rw [elem_mul_comm hB hb (hUB hh)]; group
    rw [e]
    exact hh
  · intro hh
    have hB' : b * h * b⁻¹ ∈ B := hUB hh
    have e : h = b⁻¹ * (b * h * b⁻¹) * b := by group
    rw [e, elem_mul_comm hB (B.inv_mem hb) hB']
    have e2 : b * h * b⁻¹ * b⁻¹ * b = b * h * b⁻¹ := by group
    rw [e2]
    exact hh

theorem le_normalizer_iSup' {ι : Sort*} {H : Subgroup X} (K : ι → Subgroup X)
    (h : ∀ i, H ≤ Subgroup.normalizer (K i : Set X)) :
    H ≤ Subgroup.normalizer ((⨆ i, K i : Subgroup X) : Set X) := by
  have hA : ∀ g ∈ H, ∀ x ∈ (⨆ i, K i), g * x * g⁻¹ ∈ (⨆ i, K i) := by
    intro g hg x hx
    have hle : (⨆ i, K i) ≤ (⨆ i, K i).comap (MulAut.conj g).toMonoidHom := by
      refine iSup_le fun i y hy => ?_
      rw [Subgroup.mem_comap]
      exact Subgroup.mem_iSup_of_mem i ((Subgroup.mem_normalizer_iff.1 (h i hg) y).1 hy)
    exact hle hx
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hA g hg x hx, fun hx => ?_⟩
  have h1 := hA g⁻¹ (H.inv_mem hg) _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h1


theorem isElemAbelian_subgroupOf {B : Subgroup X} (hB : IsElemAbelian p B) (H : Subgroup X) :
    IsElemAbelian p (B.subgroupOf H) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
  · exact elem_mul_comm hB (Subgroup.mem_subgroupOf.1 a.2) (Subgroup.mem_subgroupOf.1 b.2)
  · have h := hB.2 _ (Subgroup.mem_subgroupOf.1 hx)
    simpa using h

theorem gammaTwoIn_le (B L : Subgroup X) : Lemma138.gammaTwoIn p B L ≤ L :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => inf_le_left

theorem le_normalizer_gammaTwoIn {B L : Subgroup X} (hB : IsElemAbelian p B)
    (hBN : B ≤ Subgroup.normalizer (L : Set X)) :
    B ≤ Subgroup.normalizer (Lemma138.gammaTwoIn p B L : Set X) := by
  unfold Lemma138.gammaTwoIn
  refine le_normalizer_iSup' _ fun U => le_normalizer_iSup' _ fun hU =>
    le_normalizer_iSup' _ fun _ => ?_
  exact (le_inf hBN ((le_normalizer_of_le hB hU).trans Subgroup.le_normalizer)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

theorem le_gammaTwoIn_sup_of_le_glbCore {B L : Subgroup X} (hB : IsElemAbelian p B)
    (hBN : B ≤ Subgroup.normalizer (L : Set X))
    (h : L.subgroupOf (L ⊔ B) ≤ GLBCore p 2 (B.subgroupOf (L ⊔ B))) :
    L ≤ Lemma138.gammaTwoIn p B L ⊔ B := by
  have hle : GLBCore p 2 (B.subgroupOf (L ⊔ B)) ≤
      (Lemma138.gammaTwoIn p B L ⊔ B).comap (L ⊔ B).subtype := by
    unfold GLBCore
    refine sSup_le ?_
    rintro N ⟨Q, hQB, hQr, rfl⟩ y hy
    rw [Subgroup.mem_comap]
    have hyLB : (y : X) ∈ ((L ⊔ B : Subgroup X) : Set X) := y.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L B hBN] at hyLB
    obtain ⟨l, hl, b, hb, hlb⟩ := Set.mem_mul.1 hyLB
    have hQ₀B : Q.map (L ⊔ B).subtype ≤ B := by
      rintro _ ⟨q, hq, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hQB hq)
    have hQ₀r : 2 ≤ CFSG.Open.pRank p (Q.map (L ⊔ B).subtype) := by
      rw [CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective p
        (L ⊔ B).subtype_injective]
      exact hQr
    have hyN : (y : X) ∈ Subgroup.normalizer ((Q.map (L ⊔ B).subtype : Subgroup X) : Set X) :=
      Subgroup.le_normalizer_map _ ⟨y, hy, rfl⟩
    have hbN := le_normalizer_of_le hB hQ₀B hb
    have hlN : l ∈ Subgroup.normalizer ((Q.map (L ⊔ B).subtype : Subgroup X) : Set X) := by
      have e : l = (y : X) * b⁻¹ := by rw [← hlb]; group
      rw [e]
      exact Subgroup.mul_mem _ hyN (Subgroup.inv_mem _ hbN)
    have hlG : l ∈ Lemma138.gammaTwoIn p B L := by
      unfold Lemma138.gammaTwoIn
      exact Subgroup.mem_iSup_of_mem (Q.map (L ⊔ B).subtype)
        (Subgroup.mem_iSup_of_mem hQ₀B (Subgroup.mem_iSup_of_mem hQ₀r ⟨hl, hlN⟩))
    show (y : X) ∈ Lemma138.gammaTwoIn p B L ⊔ B
    rw [← hlb]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlG) (Subgroup.mem_sup_right hb)
  intro x hx
  have hxY : x ∈ L ⊔ B := (le_sup_left : L ≤ L ⊔ B) hx
  exact hle (h (Subgroup.mem_subgroupOf.2 (show ((⟨x, hxY⟩ : ↥(L ⊔ B)) : X) ∈ L from hx)))

end Gamma


section I2711

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem normal_subgroupOf_sup {L B : Subgroup X} (hBN : B ≤ Subgroup.normalizer (L : Set X)) :
    (L.subgroupOf (L ⊔ B)).Normal := by
  have h := Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := B) (N := L) hBN
  rw [sup_comm] at h
  exact h

theorem eq_gammaTwoIn_of_input2319 (h2319 : Lemma1315b.Input23_19) (hp : p.Prime) (hp2 : p ≠ 2)
    {L B : Subgroup X} (hLK : CFSG.IsKGroup ↥L) (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hB : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (L : Set X))
    (hmax : ∀ A : Subgroup X, A ≤ B ⊔ L → IsElemAbelian p A → Nat.card A ≤ Nat.card B)
    (hB4 : 4 ≤ CFSG.Open.pRank p B)
    (htype : (∃ n : ℕ, IsAltType n (↥L ⧸ Subgroup.center ↥L)) ∨
      (∃ q : ℕ, q.Prime ∧ q ≠ p ∧ IsChevSimple q (↥L ⧸ Subgroup.center ↥L)) ∨
      (∀ A : Subgroup (MulAut ↥L), IsElemAbelian p A → CFSG.Open.pRank p A ≤ 2)) :
    L = Lemma138.gammaTwoIn p B L := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hBp : IsPGroup p ↥B := CFSG.Open.IsElemAbelian.isPGroup hB
  have hKY : CFSG.Open.IsKGroup ↥(L ⊔ B) :=
    CFSG.LocalAnalysis.GLTheoremA.chevTools_isKGroup_sup hp
      (CFSG.KCore.KGroupAllSimple.kGroupNonab hLK) hBN hBp
  have hB'el : IsElemAbelian p (B.subgroupOf (L ⊔ B)) := isElemAbelian_subgroupOf hB _
  have hrB' : CFSG.Open.pRank p (B.subgroupOf (L ⊔ B)) = CFSG.Open.pRank p B :=
    CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_subgroupOf p le_sup_right
  have hcardB : Nat.card B = p ^ CFSG.Open.pRank p B := card_eq_pow_pRank hp hB
  have hrk : CFSG.Open.pRank p (B.subgroupOf (L ⊔ B)) = CFSG.Open.pRank p (⊤ : Subgroup ↥(L ⊔ B)) := by
    refine le_antisymm (CFSG.SectionRank.pRank_mono hp.one_lt le_top) ?_
    rw [hrB']
    refine CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => ?_
    have h1 := hmax (E.map (L ⊔ B).subtype) ((Subgroup.map_subtype_le E).trans (le_of_eq (sup_comm L B)))
      (CFSG.SectionRank.isElemAbelian_map hE _)
    rw [Subgroup.card_map_of_injective (L ⊔ B).subtype_injective] at h1
    rw [← hcardB]
    exact h1
  have eL : ↥(L.subgroupOf (L ⊔ B)) ≃* ↥L := Subgroup.subgroupOfEquivOfLe le_sup_left
  have hL'q : CFSG.Open.IsQuasisimple ↥(L.subgroupOf (L ⊔ B)) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv eL hLq
  have hL'c : CFSG.Open.IsComponentOf (L.subgroupOf (L ⊔ B)) ⊤ :=
    ⟨le_top, isSubnormal_of_normal (normal_subgroupOf_sup hBN), hL'q⟩
  have htype' : (∃ n : ℕ, IsAltType n (↥(L.subgroupOf (L ⊔ B)) ⧸ Subgroup.center ↥(L.subgroupOf (L ⊔ B)))) ∨
      (∃ q : ℕ, q.Prime ∧ q ≠ p ∧
        IsChevSimple q (↥(L.subgroupOf (L ⊔ B)) ⧸ Subgroup.center ↥(L.subgroupOf (L ⊔ B)))) ∨
      (∀ A : Subgroup (MulAut ↥(L.subgroupOf (L ⊔ B))), IsElemAbelian p A →
        CFSG.Open.pRank p A ≤ 2) := by
    rcases htype with ⟨n, hn⟩ | ⟨q, hq, hqp, hch⟩ | hA
    · exact Or.inl ⟨n, Lemma1315b.isAltType_center_of_equiv eL hn⟩
    · exact Or.inr (Or.inl ⟨q, hq, hqp, Lemma1315b.isChevSimple_center_of_equiv eL hch⟩)
    · refine Or.inr (Or.inr fun A hA' => ?_)
      have h1 := hA (A.map (MulAut.congr eL).toMonoidHom) (CFSG.SectionRank.isElemAbelian_map hA' _)
      rwa [CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective p
        (MulAut.congr eL).injective] at h1
  have h23 := h2319 ↥(L ⊔ B) hKY p hp hp2 (B.subgroupOf (L ⊔ B)) hB'el (by rw [hrB']; exact hB4)
    hrk (L.subgroupOf (L ⊔ B)) hL'c htype'
  have hLΓB : L ≤ Lemma138.gammaTwoIn p B L ⊔ B := le_gammaTwoIn_sup_of_le_glbCore hB hBN h23
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.1 ⟨hLq.1⟩
  have hLΓ : L ≤ Lemma138.gammaTwoIn p B L :=
    CFSG.LocalAnalysis.GLTheoremA.chevTools_perfect_le_of_sup hp (le_normalizer_gammaTwoIn hB hBN)
      hBp hLΓB hperf
  exact le_antisymm hLΓ (gammaTwoIn_le B L)

@[expose] def InputI2711ChevPSpor : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 → ∀ (L B : Subgroup X),
    CFSG.IsKGroup ↥L → CFSG.Open.IsQuasisimple ↥L → IsElemAbelian p B →
    B ≤ Subgroup.normalizer (L : Set X) →
    (∀ A : Subgroup X, A ≤ B ⊔ L → IsElemAbelian p A → Nat.card A ≤ Nat.card B) →
    4 ≤ CFSG.Open.pRank p B →
    (¬ ∃ n : ℕ, IsAltType n (↥L ⧸ Subgroup.center ↥L)) →
    (¬ ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ IsChevSimple q (↥L ⧸ Subgroup.center ↥L)) →
    (∃ A : Subgroup (MulAut ↥L), IsElemAbelian p A ∧ 3 ≤ CFSG.Open.pRank p A) →
    CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (L : Set X)) ≤ 1 →
    ∀ J0 : Subgroup X,
      CFSG.Open.IsComponentOf J0 (⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
        L ⊓ Subgroup.normalizer (U : Set X)) →
      ((∃ k : ℕ, 5 ≤ k * p ∧ IsAltType (k * p) J0) ∨ (∃ k : ℕ, IsAltType (k * p + 2) J0) ∨
        (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ HasFixedPointFreeOrder ε n p ∧
          Nonempty (↥J0 ≃* ↥(⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ : Subgroup
            (GL (Fin n ⊕ Fin n) (ZMod 2))))) ∨
        (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) J0 ∧
          HasFixedPointFreeOrder ε n p)) →
      ¬ (p = 3 ∧ IsAltType 5 J0) →
      (∃ E : Subgroup X, E ≤ B ∧ B ⊓ Subgroup.centralizer (L : Set X) ≤ E ∧
        Nat.card B ≤ p ^ 2 * Nat.card E ∧
        GLAPLayer p (J0 ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥) →
      L = ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
        L ⊓ Subgroup.normalizer (U : Set X)

theorem inputI27111_of_inputs (h2319 : Lemma1315b.Input23_19) (hCS : InputI2711ChevPSpor) :
    Lemma138.InputI27111 := by
  intro X _ _ p hp hp2 L B hLK hLq hB hBN hmax hB4 J0 hJ0 hJt hJ5 hE
  change L = Lemma138.gammaTwoIn p B L
  by_cases hC : 2 ≤ CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (L : Set X))
  · refine le_antisymm (fun x hx => ?_) (gammaTwoIn_le B L)
    unfold Lemma138.gammaTwoIn
    refine Subgroup.mem_iSup_of_mem (B ⊓ Subgroup.centralizer (L : Set X))
      (Subgroup.mem_iSup_of_mem inf_le_left (Subgroup.mem_iSup_of_mem hC ⟨hx, ?_⟩))
    refine Subgroup.centralizer_le_normalizer
      ((B ⊓ Subgroup.centralizer (L : Set X) : Subgroup X) : Set X) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (Subgroup.mem_centralizer_iff.1 hc.2 x hx).symm
  by_cases hcov : (∃ n : ℕ, IsAltType n (↥L ⧸ Subgroup.center ↥L)) ∨
      (∃ q : ℕ, q.Prime ∧ q ≠ p ∧ IsChevSimple q (↥L ⧸ Subgroup.center ↥L)) ∨
      (∀ A : Subgroup (MulAut ↥L), IsElemAbelian p A → CFSG.Open.pRank p A ≤ 2)
  · exact eq_gammaTwoIn_of_input2319 h2319 hp hp2 hLK hLq hB hBN hmax hB4 hcov
  · have hnA : ¬ ∃ n : ℕ, IsAltType n (↥L ⧸ Subgroup.center ↥L) := fun h => hcov (Or.inl h)
    have hnC : ¬ ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ IsChevSimple q (↥L ⧸ Subgroup.center ↥L) :=
      fun h => hcov (Or.inr (Or.inl h))
    have hA : ∃ A : Subgroup (MulAut ↥L), IsElemAbelian p A ∧ 3 ≤ CFSG.Open.pRank p A := by
      by_contra h
      apply hcov
      refine Or.inr (Or.inr fun A hA => ?_)
      by_contra h3
      exact h ⟨A, hA, by omega⟩
    obtain ⟨E, hEB, hEi, hEl⟩ := hE
    have hJ0L : J0 ≤ L := hJ0.1.trans (gammaTwoIn_le B L)
    refine hCS X p hp hp2 L B hLK hLq hB hBN hmax hB4 hnA hnC hA (by omega) J0 hJ0 hJt hJ5
      ⟨E ⊔ (B ⊓ Subgroup.centralizer (L : Set X)), sup_le hEB inf_le_left, le_sup_right,
        hEi.trans (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le le_sup_left)), ?_⟩
    have heq : J0 ⊓ Subgroup.centralizer ((E ⊔ (B ⊓ Subgroup.centralizer (L : Set X)) :
        Subgroup X) : Set X) = J0 ⊓ Subgroup.centralizer (E : Set X) := by
      refine le_antisymm (inf_le_inf_left _ (Subgroup.centralizer_le (le_sup_left :
        E ≤ E ⊔ (B ⊓ Subgroup.centralizer (L : Set X))))) ?_
      intro x hx
      obtain ⟨hxJ, hxE⟩ := Subgroup.mem_inf.1 hx
      refine Subgroup.mem_inf.2 ⟨hxJ, ?_⟩
      have hle : E ⊔ (B ⊓ Subgroup.centralizer (L : Set X)) ≤
          Subgroup.centralizer ({x} : Set X) := by
        refine sup_le (fun e he => ?_) (fun c hc => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.1 hxE e he)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.1 hc.2 x (hJ0L hxJ)).symm
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have := hle hh
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this
    rw [heq]
    exact hEl

theorem inputI2711ChevPSpor_of_inputI27111 (h : Lemma138.InputI27111) : InputI2711ChevPSpor := by
  intro X _ _ p hp hp2 L B hLK hLq hB hBN hmax hB4 _ _ _ _ J0 hJ0 hJt hJ5 hE
  obtain ⟨E, hEB, -, hEi, hEl⟩ := hE
  exact h X p hp hp2 L B hLK hLq hB hBN hmax hB4 J0 hJ0 hJt hJ5 ⟨E, hEB, hEi, hEl⟩

end I2711


section I275

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem kStar_eq_of_le_normalizer {B K : Subgroup X} (hN : B ≤ Subgroup.normalizer (K : Set X)) :
    (⨆ b ∈ B, GLBConj b K) = K := by
  refine le_antisymm (iSup₂_le fun b hb => le_of_eq (gLBConj_eq_of_mem_normalizer (hN hb))) ?_
  have h1 := le_iSup₂ (f := fun b (_ : b ∈ B) => GLBConj b K) 1 B.one_mem
  rwa [gLBConj_one] at h1

open GL83.CompFam in
theorem kStar_le_iSup_centralizer [Fact p.Prime] {B K : Subgroup X} (hB : IsElemAbelian p B)
    (hBc : Nat.card B = p ^ 2) (hKc : IsComponentOf K ⊤) (hN : ¬ B ≤ Subgroup.normalizer (K : Set X)) :
    (⨆ b ∈ B, GLBConj b K) ≤
      ⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), Subgroup.centralizer ({b} : Set X) := by
  have hp := (Fact.out : p.Prime)
  have hF := isFam_conjSet hB hKc
  have hK₀ := mem_conjSet_self B K
  have h1 : (⨆ b ∈ B, GLBConj b K) ≤ GL83.CompFam.layer (conjSet B K) :=
    iSup₂_le fun b hb => le_layer ⟨b⁻¹, B.inv_mem hb, rfl⟩
  have hC : ∀ c ∈ B, c ≠ 1 → Subgroup.centralizer ({c} : Set X) ≤
      ⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), Subgroup.centralizer ({b} : Set X) :=
    fun c hc hc1 => le_iSup_of_le c (le_iSup_of_le hc (le_iSup_of_le hc1 le_rfl))
  have hnorm : normJoin hF K ≤
      ⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), Subgroup.centralizer ({b} : Set X) := by
    refine iSup₂_le fun M hM => ?_
    obtain ⟨b, hb, hbA, K', hK', hbA', rfl⟩ := hM
    have hb1 : b ≠ 1 := fun h => hbA (h ▸ (stab B K).one_mem)
    refine le_trans (fun z hz => ?_) (hC b hb hb1)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mem_normSub_comm _ (hF.elem.2 b hb) hz).symm
  have hAB : stab B K ≤ B := inf_le_left
  obtain ⟨i, hi⟩ := GL83.CompFam.exists_card_eq_pow (elem_mono hB hAB)
  have hi2 : i < 2 := by
    have hle : i ≤ 2 := by
      have h := Subgroup.card_le_of_le hAB
      rw [hi, hBc] at h
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h
    refine lt_of_le_of_ne hle fun h => hN ?_
    have hAeq : stab B K = B := Subgroup.eq_of_le_of_card_ge hAB (by rw [hi, hBc, h])
    exact (le_of_eq hAeq.symm).trans inf_le_right
  refine h1.trans ?_
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · refine (hF.layer_le_normJoin_two hK₀ ?_).trans hnorm
    rw [hi, hBc, pow_zero, mul_one]
  · have hB1 : Nat.card B = p * Nat.card (stab B K) := by rw [hi, hBc, pow_one, sq]
    by_cases hAC : stab B K ≤ cen B K
    · have hCc : Nat.card (cen B K) = p := by
        rw [le_antisymm (cen_le_stab B K) hAC, hi, pow_one]
      have hne : cen B K ≠ ⊥ := by
        intro h0
        rw [h0, Subgroup.card_bot] at hCc
        exact hp.one_lt.ne hCc
      obtain ⟨⟨c, hc⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
      have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
      exact (hF.layer_le_centralizer_cen hK₀ hc).trans (hC c (Subgroup.mem_inf.1 hc).1 hc1')
    · exact (hF.layer_le_normJoin_one hK₀ hB1 hAC).trans hnorm

@[expose] def Input27_5Core : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → GLAPPrimeCore 3 X = ⊥ →
    ∀ K : Subgroup X, CFSG.Open.IsComponentOf K ⊤ →
    ∀ B : Subgroup X, IsElemAbelian 3 B → Nat.card B = 9 →
      B ≤ Subgroup.normalizer (K : Set X) →
      (∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b = 1) →
    ∀ S : Subgroup X, IsPGroup 2 ↥S → B ≤ Subgroup.normalizer (S : Set X) →
      S ≤ Subgroup.normalizer (K : Set X) → ¬ K ≤ Subgroup.centralizer (S : Set X) →
      (∀ b ∈ B, b ≠ 1 →
        S ⊓ Subgroup.centralizer ({b} : Set X) ≤ pCoreOf 2 (Subgroup.centralizer ({b} : Set X))) →
      K ≤ (⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), Subgroup.centralizer ({b} : Set X)) ∨
      (∃ n : ℕ, IsAltType n ↥K) ∨
      (CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) = 2 ∧ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥K)) = 2 ∧
        9 ∣ Nat.card ↥K ∧ ¬ 81 ∣ Nat.card ↥K)

theorem input27_5_of_core (h : Input27_5Core) : Claims1245b.Input27_5 := by
  intro X _ _ hXK hO K hK B hB hB9 S hS hBS hSN hnc hcond
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hN : B ≤ Subgroup.normalizer (K : Set X)
  · have hKs : (⨆ b ∈ B, GLBConj b K) = K := kStar_eq_of_le_normalizer hN
    rw [hKs] at hSN hnc ⊢
    by_cases hC : ∃ c ∈ B, c ≠ 1 ∧ c ∈ Subgroup.centralizer (K : Set X)
    · obtain ⟨c, hcB, hc1, hcK⟩ := hC
      refine Or.inl (le_trans (fun x hx => ?_)
        (le_iSup_of_le c (le_iSup_of_le hcB (le_iSup_of_le hc1 le_rfl))))
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hcK x hx
    · have hC' : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b = 1 := by
        intro b hb hbK
        by_contra hb1
        exact hC ⟨b, hb, hb1, hbK⟩
      exact h X hXK hO K hK B hB hB9 hN hC' S hS hBS hSN hnc hcond
  · exact Or.inl (kStar_le_iSup_centralizer hB (by rw [hB9]; norm_num) hK hN)

theorem input27_5Core_of_input27_5 (h : Claims1245b.Input27_5) : Input27_5Core := by
  intro X _ _ hXK hO K hK B hB hB9 hN _ S hS hBS hSN hnc hcond
  have hKs := kStar_eq_of_le_normalizer hN
  have h1 := h X hXK hO K hK B hB hB9 S hS hBS (by rw [hKs]; exact hSN) (by rw [hKs]; exact hnc) hcond
  rwa [hKs] at h1

end I275

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs27
