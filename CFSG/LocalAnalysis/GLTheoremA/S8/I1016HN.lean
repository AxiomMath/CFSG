module

public import CFSG.LocalAnalysis.GLTheoremA.S8.I1016ON
public import CFSG.LocalAnalysis.GLTheoremA.S8.HNAlt12
public import CFSG.RankThree.PartOne.K133Spor.HNKlein
public import CFSG.RankThree.PartOne.K133Spor.HNClassB
public import CFSG.RankThree.PartOne.S11c.HNInvQ6
public import CFSG.Sporadic.HNOddCore.InvRow4b
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveLocal
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Lin
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Conj
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.Bridge.HSSurj
public import CFSG.LocalAnalysis.GLTheoremA.Sec5BTools
public import CFSG.LocalAnalysis.GLTheoremA.S8.I2014Core
public import CFSG.LocalAnalysis.GLTheoremA.S8.I1423HN
public import CFSG.LocalAnalysis.GLTheoremA.S8.I1016ONRow
public import CFSG.LocalAnalysis.GLTheoremA.S8.I1016CoRows
public import CFSG.Sporadic.HNOddCore.InvRow6
public import CFSG.Sporadic.HN.Local.Main
public import CFSG.RankThree.PartOne.K133Spor.HNLeaf6
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma83Inputs
public import CFSG.GH74.Generic.S45.LLinSel
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma89

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.HNRows


open CFSG.Open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA

@[expose] def omega1Z {X : Type*} [Group X] (V : Subgroup X) : Subgroup X where
  carrier := {w | w ∈ V ∧ w ^ 2 = 1 ∧ ∀ v ∈ V, w * v = v * w}
  mul_mem' := by
    rintro a b ⟨haV, ha2, hac⟩ ⟨hbV, hb2, hbc⟩
    refine ⟨V.mul_mem haV hbV, ?_, fun v hv => ?_⟩
    · have hab : a * b = b * a := hac b hbV
      calc (a * b) ^ 2 = a * (b * a) * b := by rw [sq]; simp only [mul_assoc]
        _ = a * (a * b) * b := by rw [hab]
        _ = a ^ 2 * b ^ 2 := by rw [sq, sq]; simp only [mul_assoc]
        _ = 1 := by rw [ha2, hb2, one_mul]
    · calc a * b * v = a * (b * v) := by group
        _ = a * (v * b) := by rw [hbc v hv]
        _ = (a * v) * b := by group
        _ = (v * a) * b := by rw [hac v hv]
        _ = v * (a * b) := by group
  one_mem' := ⟨V.one_mem, by simp, fun v _ => by simp⟩
  inv_mem' := by
    rintro a ⟨haV, ha2, hac⟩
    have hinv : a⁻¹ = a := by
      rw [inv_eq_iff_mul_eq_one, ← sq, ha2]
    refine ⟨V.inv_mem haV, by rw [hinv, ha2], fun v hv => ?_⟩
    rw [hinv]; exact hac v hv

theorem false_of_five_cube_core {Y : Type} [Group Y] [Finite Y] {a b : Y}
    (hHS : ∀ E : Subgroup (MulAut (NativeSporadic.Carrier .HS)),
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → Nat.card E = 125 → False)
    (hcore : ∀ D V' : Subgroup Y, (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) → (∀ d ∈ D, d ^ 5 = 1) →
      Nat.card D = 25 → (∀ x ∈ V', ∀ y ∈ V', x * y = y * x) → (∀ v ∈ V', v ^ 2 = 1) →
      Nat.card V' = 4 → (∀ d ∈ D, ∀ v ∈ V', d * v = v * d) → False)
    (hcls : ∀ x : Y, x ^ 2 = 1 → x ≠ 1 → (∃ g, g * a * g⁻¹ = x) ∨ ∃ g, g * b * g⁻¹ = x)
    (hcb : Nat.card (Subgroup.centralizer ({b} : Set Y)) = 3686400)
    (q : ↥(Subgroup.centralizer ({a} : Set Y)) →* MulAut (NativeSporadic.Carrier .HS))
    (hq : ∀ u, q u = 1 → (u : Y) = 1 ∨ (u : Y) = a)
    {E V : Subgroup Y} (hE : IsElemAbelian 5 E) (hEc : Nat.card E = 125)
    (hV : IsPGroup 2 V) (hV1 : V ≠ ⊥) (hEV : E ≤ Subgroup.normalizer (V : Set Y)) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := omega1Z V with hWdef
  have hWV : W ≤ V := fun w hw => hw.1
  have hW2 : IsPGroup 2 W := hV.to_le hWV
  have hW1 : W ≠ ⊥ := by
    haveI : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).2 hV1
    haveI := hV.center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center V)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hV) (z : V)
    have hzk : ((z : V) : Y) ^ 2 ^ k = 1 := by
      have := pow_orderOf_eq_one (z : V)
      rw [hk] at this
      exact congrArg Subtype.val this
    have hz1' : ((z : V) : Y) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
    obtain ⟨t, ht, hto⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.S8.L84.exists_orderOf_two_mem_zpowers hz1' hzk
    intro hbot
    have htW : t ∈ W := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
      refine ⟨V.zpow_mem (z : V).2 n, by rw [← hto]; exact pow_orderOf_eq_one _, fun v hv => ?_⟩
      have hzv : ((z : V) : Y) * v = v * ((z : V) : Y) :=
        congrArg Subtype.val ((Subgroup.mem_center_iff.1 z.2 ⟨v, hv⟩).symm)
      exact (Commute.zpow_left hzv n).eq
    rw [hbot, Subgroup.mem_bot] at htW
    rw [htW, orderOf_one] at hto
    norm_num at hto
  have hW5 : ¬ 5 ∣ Nat.card W := by
    obtain ⟨k, hk⟩ := hW2.exists_card_eq
    rw [hk]; intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).1
      (Nat.prime_five.dvd_of_dvd_pow h)
    omega
  have hEW : E ≤ Subgroup.normalizer (W : Set Y) := by
    intro e he
    refine mem_normalizer_of_conj_le fun w hw => ?_
    obtain ⟨hwV, hw2, hwc⟩ := hw
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hEV he) w).1 hwV, by rw [conj_pow, hw2]; group, ?_⟩
    intro v hv
    have hv' : e⁻¹ * v * e⁻¹⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hEV (E.inv_mem he)) v).1 hv
    have h := hwc _ hv'
    calc e * w * e⁻¹ * v = e * (w * (e⁻¹ * v * e⁻¹⁻¹)) * e⁻¹ := by group
      _ = e * ((e⁻¹ * v * e⁻¹⁻¹) * w) * e⁻¹ := by rw [h]
      _ = v * (e * w * e⁻¹) := by group
  have hE1 : E ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hEc; norm_num at hEc
  obtain ⟨B, hBi, x, hxW, hx1, hBx⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S8.L84.exists_hyperplane_fixed hE hE1 hW5 hW1 hEW
  set D : Subgroup Y := B.map E.subtype with hD
  have hDc : Nat.card D = 25 := by
    rw [hD, Subgroup.card_map_of_injective E.subtype_injective]
    have h := B.card_mul_index
    rw [hBi, hEc] at h
    omega
  have hDE : D ≤ E := Subgroup.map_subtype_le _
  have hDx : ∀ d ∈ D, d * x = x * d := by
    rintro _ ⟨b, hb, rfl⟩
    exact hBx b hb
  have hEcomm : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have huniq : ∀ y ∈ W, (∀ d ∈ D, d * y = y * d) → y = 1 ∨ y = x := by
    intro y hyW hDy
    by_contra hne
    push Not at hne
    obtain ⟨hy1, hyx⟩ := hne
    have hxy : x * y = y * x := hxW.2.2 y hyW.1
    have hy2 : y ^ 2 = 1 := hyW.2.1
    have hna : x ∉ Subgroup.zpowers y := by
      intro hx
      have hyo : orderOf y = 2 := orderOf_eq_prime hy2 hy1
      have hc : Nat.card (Subgroup.zpowers y) = 2 := by rw [Nat.card_zpowers, hyo]
      have h1 : (1 : Y) ∈ Subgroup.zpowers y := Subgroup.one_mem _
      have h2 : y ∈ Subgroup.zpowers y := Subgroup.mem_zpowers y
      have h3 := three_le_card h2 hx
        hy1 hx1 (fun h => hyx h.symm)
      rw [hc] at h3
      norm_num at h3
    obtain ⟨hV4e, hV4c⟩ := CFSG.LocalAnalysis.GLTheoremA.Prop53.isElemAbelian_card_sup_zpowers
      Nat.prime_two hxy hxW.2.1 hy2 hy1 hna
    refine hcore D (Subgroup.zpowers x ⊔ Subgroup.zpowers y)
      (fun u hu v hv => hEcomm u (hDE hu) v (hDE hv)) (fun d hd => hE.2 d (hDE hd)) hDc
      (fun u hu v hv => congrArg Subtype.val (hV4e.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩))
      (fun v hv => hV4e.2 v hv) (by rw [hV4c]; norm_num) (fun d hd v hv => ?_)
    have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer ({d} : Set Y) :=
      sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (hDx d hd).symm))
        (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (hDy d hd).symm))
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hv)).symm
  have hEx : ∀ e ∈ E, e * x * e⁻¹ = x := by
    intro e he
    have hy : e * x * e⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 (hEW he) x).1 hxW
    have hDy : ∀ d ∈ D, d * (e * x * e⁻¹) = (e * x * e⁻¹) * d := by
      intro d hd
      have hde : d * e = e * d := hEcomm d (hDE hd) e he
      have hdx : d * x * d⁻¹ = x := by rw [hDx d hd]; group
      have : d * (e * x * e⁻¹) * d⁻¹ = e * x * e⁻¹ := by
        calc d * (e * x * e⁻¹) * d⁻¹ = (d * e) * x * (d * e)⁻¹ := by group
          _ = (e * d) * x * (e * d)⁻¹ := by rw [hde]
          _ = e * (d * x * d⁻¹) * e⁻¹ := by group
          _ = e * x * e⁻¹ := by rw [hdx]
      calc d * (e * x * e⁻¹) = d * (e * x * e⁻¹) * d⁻¹ * d := by group
        _ = (e * x * e⁻¹) * d := by rw [this]
    rcases huniq _ hy hDy with h | h
    · exfalso
      apply hx1
      have : x = e⁻¹ * (e * x * e⁻¹) * e := by group
      rw [this, h]; group
    · exact h
  have hx2 : x ^ 2 = 1 := hxW.2.1
  have hx5 : ∀ e ∈ E, e = x → False := by
    intro e he hex
    have h5 := hE.2 e he
    rw [hex] at h5
    have : x ^ 5 = x := by
      calc x ^ 5 = x * (x ^ 2) ^ 2 := by group
        _ = x := by rw [hx2]; group
    exact hx1 (this ▸ h5)
  rcases hcls x hx2 hx1 with ⟨g, hg⟩ | ⟨g, hg⟩
  ·
    have hmem : ∀ e ∈ E, g⁻¹ * e * g ∈ Subgroup.centralizer ({a} : Set Y) := by
      intro e he
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxe := hEx e he
      have hxe' : e * x = x * e := by
        calc e * x = e * x * e⁻¹ * e := by group
          _ = x * e := by rw [hxe]
      rw [← hg] at hxe'
      calc g⁻¹ * e * g * a = g⁻¹ * (e * (g * a * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * a * g⁻¹) * e) * g := by rw [hxe']
        _ = a * (g⁻¹ * e * g) := by group
    let ι : ↥E →* ↥(Subgroup.centralizer ({a} : Set Y)) :=
      { toFun := fun e => ⟨g⁻¹ * e * g, hmem e e.2⟩
        map_one' := by ext; simp
        map_mul' := fun u v => by ext; simp only [Subgroup.coe_mul]; group }
    have hφ : Function.Injective (q.comp ι) := by
      rw [injective_iff_map_eq_one]
      intro e he
      rcases hq _ he with h | h
      · have h' : g⁻¹ * (e : Y) * g = 1 := h
        apply Subtype.ext
        have : (e : Y) = g * (g⁻¹ * e * g) * g⁻¹ := by group
        rw [this, h']; simp
      · exfalso
        have h' : g⁻¹ * (e : Y) * g = a := h
        apply hx5 e e.2
        rw [← hg, ← h']; group
    refine hHS (q.comp ι).range ?_ ?_
    · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hEcomm u u.2 v v.2)
    · rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, hEc]
  ·
    have hle : E ≤ Subgroup.centralizer ({x} : Set Y) := fun e he =>
      Subgroup.mem_centralizer_singleton_iff.2 (by
        calc e * x = e * x * e⁻¹ * e := by group
          _ = x * e := by rw [hEx e he])
    have hcx : Nat.card (Subgroup.centralizer ({x} : Set Y)) = 3686400 := by
      rw [← hg, centralizer_conj,
        Subgroup.card_map_of_injective (MulAut.conj g).injective, hcb]
    have := Subgroup.card_dvd_of_le hle
    rw [hEc, hcx] at this
    norm_num at this

theorem pow_le_of_dvd_card_HN {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5)
    (h : p ^ n ∣ 273030912000000) : p ^ n ≤ p := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simpa using hp.one_lt.le
    · simp
  exfalso
  have h2 : p ^ 2 ∣ 273030912000000 := (pow_dvd_pow p hn).trans h
  have h1 : p ∣ 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19 :=
    (dvd_pow_self p two_ne_zero).trans (by norm_num at h2 ⊢; exact h2)
  have key : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq h =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 h
  simp only [hp.dvd_mul] at h1
  rcases h1 with (((((h | h) | h) | h) | h) | h)
  · exact hp2 (key 2 (by norm_num) (hp.dvd_of_dvd_pow h))
  · exact hp3 (key 3 (by norm_num) (hp.dvd_of_dvd_pow h))
  · exact hp5 (key 5 (by norm_num) (hp.dvd_of_dvd_pow h))
  · rw [key 7 (by norm_num) h] at h2; norm_num at h2
  · rw [key 11 (by norm_num) h] at h2; norm_num at h2
  · rw [key 19 (by norm_num) h] at h2; norm_num at h2

theorem i1016_HN_core {Y : Type} [Group Y] [Finite Y] {a b : Y}
    (hHS : ∀ E : Subgroup (MulAut (NativeSporadic.Carrier .HS)),
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → Nat.card E = 125 → False)
    (hcore : ∀ D V' : Subgroup Y, (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) → (∀ d ∈ D, d ^ 5 = 1) →
      Nat.card D = 25 → (∀ x ∈ V', ∀ y ∈ V', x * y = y * x) → (∀ v ∈ V', v ^ 2 = 1) →
      Nat.card V' = 4 → (∀ d ∈ D, ∀ v ∈ V', d * v = v * d) → False)
    (hcls : ∀ x : Y, x ^ 2 = 1 → x ≠ 1 → (∃ g, g * a * g⁻¹ = x) ∨ ∃ g, g * b * g⁻¹ = x)
    (hca : Nat.card (Subgroup.centralizer ({a} : Set Y)) = 177408000)
    (hcb : Nat.card (Subgroup.centralizer ({b} : Set Y)) = 3686400)
    (q : ↥(Subgroup.centralizer ({a} : Set Y)) →* MulAut (NativeSporadic.Carrier .HS))
    (hq : ∀ u, q u = 1 → (u : Y) = 1 ∨ (u : Y) = a) (hY : Nat.card Y = 273030912000000)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E V : Subgroup Y} (hE : IsElemAbelian p E)
    (hV : IsPGroup 2 V) (hV1 : V ≠ ⊥) (hEV : E ≤ Subgroup.normalizer (V : Set Y))
    (h3 : p ^ 3 ≤ Nat.card E) : p = 3 ∧ Nat.card E ≤ 3 ^ 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hEp
  have hdvd : p ^ n ∣ 273030912000000 := hn ▸ hY ▸ Subgroup.card_subgroup_dvd_card E
  have hn3 : 3 ≤ n := by
    rw [hn] at h3
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h3
  by_cases hp3 : p = 3
  · subst hp3
    refine ⟨rfl, CFSG.LocalAnalysis.GLTheoremA.S8.L84.card_le_of_involution_centralizers (k := 2)
      Nat.prime_three (by norm_num) hE hV hV1 hEV fun t ht F hF hFp => ?_⟩
    have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; norm_num at ht
    have hCt : Nat.card (Subgroup.centralizer ({t} : Set Y)) ∣ 177408000 ∨
        Nat.card (Subgroup.centralizer ({t} : Set Y)) ∣ 3686400 := by
      rcases hcls t ht2 ht1 with ⟨g, hg⟩ | ⟨g, hg⟩
      · left
        rw [← hg, centralizer_conj,
          Subgroup.card_map_of_injective (MulAut.conj g).injective, hca]
      · right
        rw [← hg, centralizer_conj,
          Subgroup.card_map_of_injective (MulAut.conj g).injective, hcb]
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hFp
    have hFd := Subgroup.card_dvd_of_le hF
    rw [hm]
    have hm3 : m < 3 := by
      by_contra hm3
      push Not at hm3
      have h27 : 3 ^ 3 ∣ Nat.card (Subgroup.centralizer ({t} : Set Y)) :=
        (pow_dvd_pow 3 hm3).trans (hm ▸ hFd)
      rcases hCt with h | h
      · exact absurd (h27.trans h) (by norm_num)
      · exact absurd (h27.trans h) (by norm_num)
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exfalso
  by_cases hp5 : p = 5
  · subst hp5
    have h125 : 5 ^ 3 ∣ Nat.card E := hn ▸ pow_dvd_pow 5 hn3
    obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 5 h125
    refine false_of_five_cube_core hHS hcore hcls hcb q hq (E := P.map E.subtype) ?_ ?_ hV hV1 ?_
    · refine CFSG.LocalAnalysis.GLTheoremA.S8.L84.elemAbelian_of_le hE ?_
      rintro _ ⟨a', -, rfl⟩
      exact a'.2
    · rw [Subgroup.card_map_of_injective E.subtype_injective, hP]; norm_num
    · rintro _ ⟨a', -, rfl⟩
      exact hEV a'.2
  · have h1 := pow_le_of_dvd_card_HN hp hp2 hp3 hp5 hdvd
    have : p ^ 3 ≤ p ^ 1 := (Nat.pow_le_pow_right hp.pos hn3).trans (by rw [pow_one]; exact h1)
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 this
    omega

theorem q_of_iso {Y Q M : Type} [Group Y] [Group Q] [Group M] (e : Y ≃* Q) {a : Q}
    (q : ↥(Subgroup.centralizer ({a} : Set Q)) →* M)
    (hq : ∀ u, q u = 1 → (u : Q) = 1 ∨ (u : Q) = a) :
    ∃ q' : ↥(Subgroup.centralizer ({e.symm a} : Set Y)) →* M,
      ∀ u, q' u = 1 → (u : Y) = 1 ∨ (u : Y) = e.symm a := by
  have hmem : ∀ u : ↥(Subgroup.centralizer ({e.symm a} : Set Y)),
      e u ∈ Subgroup.centralizer ({a} : Set Q) := by
    intro u
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.1 u.2
    have := congrArg e h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  let φ : ↥(Subgroup.centralizer ({e.symm a} : Set Y)) →* ↥(Subgroup.centralizer ({a} : Set Q)) :=
    { toFun := fun u => ⟨e u, hmem u⟩
      map_one' := by ext; simp
      map_mul' := fun u v => by ext; simp }
  refine ⟨q.comp φ, fun u hu => ?_⟩
  rcases hq _ hu with h | h
  · left
    have h' : e u = 1 := h
    exact e.injective (h'.trans (map_one e).symm)
  · right
    have h' : e u = a := h
    calc (u : Y) = e.symm (e u) := (e.symm_apply_apply _).symm
      _ = e.symm a := by rw [h']

theorem isElementaryAbelian_of {X : Type*} [Group X] {p : ℕ} {D : Subgroup X}
    (hc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hp : ∀ d ∈ D, d ^ p = 1) :
    CFSG.IsElementaryAbelian p D where
  is_comm := ⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
    Subtype.ext (by simpa using hp g g.2)


theorem false_of_abelian_125_autHS (E : Subgroup (MulAut (NativeSporadic.Carrier .HS)))
    (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hc : Nat.card E = 125) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard : Nat.card (NativeSporadic.Carrier .HS) = 44352000 := CFSG.Sporadic.HS.card_HS
  have hfin : Finite (NativeSporadic.Carrier .HS) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : IsSimpleGroup (NativeSporadic.Carrier .HS) := CFSG.Sporadic.HS.isSimpleGroup_HS
  have hZ : Subgroup.center (NativeSporadic.Carrier .HS) = ⊥ :=
    CFSG.HardMathSupport.Dickson.I271.center_eq_bot_of_simple_nonab
      (exists_noncomm_of_simple (by rw [hcard]; norm_num))
  have hKc := CFSG.GH74.GLS.IVK.Proofs2.centralizer_inner_eq_bot_of_center_eq_bot hZ
  have hinj := CFSG.GH74.GLS.IVK.Proofs2.conj_injective_of_center_eq_bot hZ
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have eK : ↥(inner (NativeSporadic.Carrier .HS)) ≃* (TauCeti.CFSGIndex.sporadic .HS).Group :=
    (MonoidHom.ofInjective hinj).symm.trans b
  have hEp : IsPGroup 5 E := IsPGroup.of_card (n := 3) (by rw [hc]; norm_num)
  obtain ⟨R, hER⟩ := hEp.exists_le_sylow
  have h := CFSG.AGLEmbeddingD2.d2HeisLocalEqAt_hs (MulAut (NativeSporadic.Carrier .HS))
    (inner _) (inner_normal _) hKc ⟨eK⟩ 5 rfl R
  obtain ⟨-, hR125, -, hR5, -⟩ := h
  have hRE : E = (R : Subgroup (MulAut (NativeSporadic.Carrier .HS))) :=
    Subgroup.eq_of_le_of_card_ge hER (by rw [hR125, hc]; norm_num)
  have hinf : (R : Subgroup (MulAut (NativeSporadic.Carrier .HS))) ⊓ Subgroup.centralizer ((R : Subgroup (MulAut (NativeSporadic.Carrier .HS))) : Set _) =
      (R : Subgroup (MulAut (NativeSporadic.Carrier .HS))) := by
    refine inf_eq_left.2 fun a ha => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [← hRE] at ha hb
    exact hE b hb a ha
  rw [hinf, hR125] at hR5
  norm_num at hR5




set_option maxRecDepth 20000 in
theorem i1016_HN_native {Y : Type} [Group Y] [Finite Y] (ψ : Y ≃* NativeSporadic.HN)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E V : Subgroup Y} (hE : IsElemAbelian p E)
    (hV : IsPGroup 2 V) (hV1 : V ≠ ⊥) (hEV : E ≤ Subgroup.normalizer (V : Set Y))
    (h3 : p ^ 3 ≤ Nat.card E) : p = 3 ∧ Nat.card E ≤ 3 ^ 3 := by
  let e : Y ≃* CFSG.Sporadic.HNSchreier.JH := ψ.trans CFSG.Sporadic.HNSchreier.hnEquivJ
  set a' : Y := e.symm CFSG.Sporadic.HNSchreier.aJ with ha'
  obtain ⟨q, hq⟩ := CFSG.RankThree.PartOne.HNRed.exists_q6
  obtain ⟨q', hq'⟩ := @q_of_iso Y CFSG.Sporadic.HNSchreier.JH _ _ inferInstance _ e _ q hq
  have hca : Nat.card (Subgroup.centralizer ({a'} : Set Y)) = 177408000 :=
    (@CFSG.Sporadic.HN.Local.card_centralizer_equiv CFSG.Sporadic.HNSchreier.JH Y inferInstance _
      e.symm CFSG.Sporadic.HNSchreier.aJ).symm.trans CFSG.Sporadic.HNOddCore.card_CJ_t6
  have ha'2 : a' ^ 2 = 1 := by rw [ha', ← map_pow, CFSG.Sporadic.HNOddCore.aJ_sq, map_one]
  have ha'1 : a' ≠ 1 := fun h => CFSG.Sporadic.HNOddCore.aJ_ne_one
    (e.symm.injective (h.trans (map_one e.symm).symm))
  have hinv : ∀ x : Y, x ^ 2 = 1 → x ≠ 1 →
      IsConj CFSG.Sporadic.HN.Local.hnT2 (ψ x) ∨ IsConj CFSG.Sporadic.HN.Local.hnT4 (ψ x) :=
    fun x hx2 hx1 => CFSG.Sporadic.HN.Local.hn_involution_cover (ψ x)
      (by rw [← map_pow, hx2, map_one]) (fun h => hx1 (ψ.injective (h.trans (map_one ψ).symm)))
  set b : Y := ψ.symm CFSG.Sporadic.HN.Local.hnT4 with hb
  have hcb : Nat.card (Subgroup.centralizer ({b} : Set Y)) = 3686400 := by
    rw [@CFSG.Sporadic.HN.Local.card_centralizer_equiv Y NativeSporadic.HN _ Units.instGroup ψ b,
      hb, MulEquiv.apply_symm_apply]
    exact CFSG.Sporadic.HN.Local.hn_card_centralizer_t4
  have hψa : IsConj CFSG.Sporadic.HN.Local.hnT2 (ψ a') := by
    rcases hinv a' ha'2 ha'1 with h | h
    · exact h
    · exfalso
      have h' : IsConj (ψ b) (ψ a') := by rw [hb, MulEquiv.apply_symm_apply]; exact h
      obtain ⟨c, hc⟩ := isConj_iff.1 ((@CFSG.Sporadic.HN.Local.isConj_equiv_iff Y NativeSporadic.HN _ Units.instGroup ψ b a').1 h')
      have h1 : Nat.card (Subgroup.centralizer ({a'} : Set Y)) = 3686400 := by
        rw [← hc, centralizer_conj,
          Subgroup.card_map_of_injective (MulAut.conj c).injective, hcb]
      rw [hca] at h1
      norm_num at h1
  have hcls : ∀ x : Y, x ^ 2 = 1 → x ≠ 1 → (∃ g, g * a' * g⁻¹ = x) ∨ ∃ g, g * b * g⁻¹ = x := by
    intro x hx2 hx1
    rcases hinv x hx2 hx1 with h | h
    · left
      exact isConj_iff.1 ((@CFSG.Sporadic.HN.Local.isConj_equiv_iff Y NativeSporadic.HN _ Units.instGroup ψ a' x).1
        (hψa.symm.trans h))
    · right
      refine isConj_iff.1
        ((@CFSG.Sporadic.HN.Local.isConj_equiv_iff Y NativeSporadic.HN _ Units.instGroup ψ b x).1 ?_)
      rw [hb, MulEquiv.apply_symm_apply]
      exact h
  have hcore : ∀ D V' : Subgroup Y, (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) → (∀ d ∈ D, d ^ 5 = 1) →
      Nat.card D = 25 → (∀ x ∈ V', ∀ y ∈ V', x * y = y * x) → (∀ v ∈ V', v ^ 2 = 1) →
      Nat.card V' = 4 → (∀ d ∈ D, ∀ v ∈ V', d * v = v * d) → False :=
    fun D V' h1 h2 h3 h4 h5 h6 h7 =>
      CFSG.RankThree.PartOne.K133Spor.hnKleinPlaneFree Y ⟨ψ⟩ D V'
        (isElementaryAbelian_of h1 h2) h3 (isElementaryAbelian_of h4 h5) h6 h7
  have hY : Nat.card Y = 273030912000000 :=
    (Nat.card_congr ψ.toEquiv).trans CFSG.Sporadic.HNSchreier.card_HN
  exact i1016_HN_core false_of_abelian_125_autHS hcore hcls hca hcb q' hq' hY hp hp2 hE hV hV1
    hEV h3


theorem nonempty_pquot_equiv_HN_p {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X L : Subgroup G} (hL : GLAPComponent p X L)
    (hcat : catalogIs (PSimple p L) (S8.sporIs .HN)) :
    Nonempty (PQuot p L ≃* CFSG.Blueprint.NativeSporadic.HN) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rw [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  let eS : PSimple p L ≃* CFSG.Blueprint.NativeSporadic.Carrier .HN := e.trans b.symm
  have hq := S8.L84.cfsgQuasisimple_of_open (isQuasisimple_pQuot_of_glaPComponent hp hL)
  have h := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq
    (X := CFSG.Blueprint.NativeSporadic.Carrier .HN) eS
  have hM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (CFSG.Blueprint.NativeSporadic.Carrier .HN)) = 1 :=
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_HN
  rw [hM] at h
  have hZ : Subgroup.center (PQuot p L) = ⊥ := Subgroup.card_eq_one.mp (Nat.dvd_one.1 h)
  exact ⟨(((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
    e).trans b.symm⟩

theorem i1016HNAt_holds (G : Type) [Group G] [Finite G] : S8.L83.I1016HNAt G := by
  intro p hp hp2 X L E V hL hcat hEL hE hVL hV hVO hEV h3
  obtain ⟨Eb, Vb, hEb, hEbc, hVb, hVb1, hEbVb⟩ := S8.L84.pquot_facts hp hEL hE hVL hV hVO hEV
  obtain ⟨ψ⟩ := nonempty_pquot_equiv_HN_p hp hL hcat
  rw [← hEbc] at h3 ⊢
  exact i1016_HN_native ψ hp hp2 hEb hVb hVb1 hEbVb h3

end CFSG.LocalAnalysis.GLTheoremA.S8.HNRows
