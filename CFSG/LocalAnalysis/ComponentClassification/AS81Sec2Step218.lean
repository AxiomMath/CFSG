module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step218Mod
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step218Gold
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2OmegaPts
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Cz

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

namespace Sec2Q

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F T₀ Q : Subgroup G}
  {u y z : G}

open Sec2

omit [Finite G] in
theorem conj_eq_of_mem_zpowers' {w ζ : G} (hw : w ∈ centralizer ({z} : Set G))
    (hζ : ζ ∈ zpowers z) : w * ζ * w⁻¹ = ζ := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hζ
  have h1 : w * z * w⁻¹ = z := by
    have h2 : z * w = w * z := mem_centralizer_iff.mp hw z rfl
    rw [← h2, mul_inv_cancel_right]
  rw [← conj_zpow, h1]

theorem mem_normalizer_of_mem_normalizer_sec2Z
    (hQO : GoldschmidtQO) (h4 : AS76b.Asc75Theorem4)
    (h34 : AS76b.Asc08Lemma34) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h21 : Step21) (h24 : Step24)
    (h26 : Step26) (h26ii : Step26ii) (h27 : Step27) (h211 : Step211) (h212 : Step212)
    (hQ : Sec2Q G A R g E F T₀ Q u y z) {n : G}
    (hnZ : n ∈ normalizer (sec2Z A E F : Set G)) (hnz : n ∈ centralizer ({z} : Set G)) :
    n ∈ normalizer (Q : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hQ.data
  have hset := hd.setting
  have hSp : Special (sec2S A R E F) (sec2Z A E F) := special_of h24 hset
  obtain ⟨-, -, ⟨x, hx3, hxF4, hxcl, hxH, hxH', hθx⟩, -, -, -⟩ :=
    (h212 G A R g E F hset).2 T₀ hd.le hd.sylow
  obtain ⟨C, t, z₁, hD, hQeq, -, -⟩ :=
    exists_qsetting h21 h24 h26 h212 hQ hx3 hxF4 hxcl hxH hxH' hθx
  have htQ : t ∈ Q := hQeq ▸ hD.hS.t_mem_Qt hD.ht.normS hD.ht.sq
  have hgold := le_normalizer_sup_oddCoreIn_sec2Z hQO h24 h26 h26ii h212 hset hd.le hd.sylow
  have hOS := oddCoreIn_centralizer_Z_le_centralizer h4 h34 hE16 h24 h26 h27 hset hd.uy
  have hS2 : IsPGroup 2 (sec2S A R E F) := IsPGroup.of_card (n := 10) (by
    rw [C.card_S hSp]
    norm_num)
  have hCZS : ∀ c ∈ centralizer (sec2Z A E F : Set G), c ∈ normalizer (sec2S A R E F : Set G) := by
    intro c hc
    apply AS76b.mem_normalizer_of_map_conj_le
    rintro _ ⟨s, hs, rfl⟩
    show c * s * c⁻¹ ∈ sec2S A R E F
    have h1 : c * s * c⁻¹ ∈ sec2S A R E F ⊔ AS76b.oddCoreIn (centralizer (sec2Z A E F : Set G)) :=
      (mem_normalizer_iff.mp (hgold hc) s).mp (mem_sup_left hs)
    obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
    have hk' : (c * s * c⁻¹) ^ 2 ^ k = 1 := by
      rw [conj_pow, show s ^ 2 ^ k = 1 by simpa using congrArg Subtype.val hk, mul_one,
        mul_inv_cancel]
    exact mem_of_mem_sup_of_odd' hS2 (AS76b.odd_card_oddCoreIn _) hOS h1 hk'
  have hmem : ∀ w ∈ centralizer (sec2Z A E F : Set G), w ∈ centralizer ({z} : Set G) →
      w ∈ normalizer (Q : Set G) := fun w hwZ hwz =>
    mem_normalizer_of_mem_normalizer_sec2S h4 h34 hE16 h21 h24 h26 h211 h212 hQ hx3 hxF4 hxcl
      hxH hxH' hθx (hCZS w hwZ) hwz
  have hzZ : z ∈ sec2Z A E F := z_mem_Z h212 hQ
  have hz1 : z ≠ 1 := by
    intro h
    have := hQ.order
    rw [h, orderOf_one] at this
    omega
  obtain ⟨c, hcZ, hcz⟩ : ∃ c ∈ sec2Z A E F, c ∉ zpowers z := by
    by_contra hcon
    have hle : sec2Z A E F ≤ zpowers z := fun w hw => by_contra fun h => hcon ⟨w, hw, h⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [hSp.card, Nat.card_zpowers, hQ.order] at h1
    norm_num at h1
  have hc1 : c ≠ 1 := fun h => hcz (h ▸ one_mem _)
  have hcz' : z ≠ c := fun h => hcz (h ▸ mem_zpowers z)
  have hzz : z * z = 1 := hSp.elem z hzZ
  have hzc1 : z * c ≠ 1 := by
    intro h
    apply hcz
    have e : c = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [e]
    exact inv_mem (mem_zpowers z)
  have hzcz : z ≠ z * c := fun h => hc1 (left_eq_mul.mp h)
  have hzcc : c ≠ z * c := fun h => hz1 (right_eq_mul.mp h)
  have hfour : ∀ w ∈ sec2Z A E F, w = 1 ∨ w = z ∨ w = c ∨ w = z * c := fun w hw =>
    hSp.eq_of_four (one_mem _) hzZ hcZ (mul_mem hzZ hcZ) hw hz1.symm hc1.symm hzc1.symm hcz'
      hzcz hzcc
  have hcent : ∀ w : G, w * z * w⁻¹ = z → w * c * w⁻¹ = c →
      w ∈ centralizer (sec2Z A E F : Set G) := by
    intro w hwz' hwc
    refine mem_centralizer_iff.mpr fun v hv => ?_
    have h1 : w * v * w⁻¹ = v := by
      rcases hfour v hv with rfl | rfl | rfl | rfl
      · group
      · exact hwz'
      · exact hwc
      · calc w * (z * c) * w⁻¹ = (w * z * w⁻¹) * (w * c * w⁻¹) := by group
          _ = z * c := by rw [hwz', hwc]
    calc v * w = w * v * w⁻¹ * w := by rw [h1]
      _ = w * v := by group
  have hnz' : n * z * n⁻¹ = z := conj_eq_of_mem_zpowers' hnz (mem_zpowers z)
  have htz : t ∈ centralizer ({z} : Set G) := hQ.Q_le_centralizer htQ
  have htz' : t * z * t⁻¹ = z := conj_eq_of_mem_zpowers' htz (mem_zpowers z)
  have hz₁ : z = z₁ := by
    rcases hSp.eq_one_or_eq hD.hzZ ((hD.hz z hzZ).mp htz') with h | h
    · exact absurd h hz1
    · exact h
  have hnc : n * c * n⁻¹ ∈ sec2Z A E F := (mem_normalizer_iff.mp hnZ c).mp hcZ
  have hnc1 : n * c * n⁻¹ ≠ 1 := fun h => hc1 (by
    calc c = n⁻¹ * (n * c * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group)
  have hncz : n * c * n⁻¹ ≠ z := by
    intro h
    apply hcz'
    calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
      _ = n⁻¹ * (n * c * n⁻¹) * n := by rw [hnz', h]
      _ = c := by group
  rcases hfour _ hnc with h | h | h | h
  · exact absurd h hnc1
  · exact absurd h hncz
  · exact hmem n (hcent n hnz' h) hnz
  ·
    have htc : t * c * t⁻¹ = z * c := by
      have h1 : t * c * t⁻¹ ∈ sec2Z A E F := conj_mem_Z_of_normS hSp hD.ht.normS hcZ
      rcases hfour _ h1 with h' | h' | h' | h'
      · exact absurd (by
          calc c = t⁻¹ * (t * c * t⁻¹) * t := by group
            _ = 1 := by rw [h']; group) hc1
      · exact absurd (by
          calc c = t⁻¹ * (t * c * t⁻¹) * t := by group
            _ = t⁻¹ * (t * z * t⁻¹) * t := by rw [h', htz']
            _ = z := by group) (Ne.symm hcz')
      · exact absurd ((hD.hz c hcZ).mp h') (by rw [← hz₁]; exact hcz)
      · exact h'
    have hntc : (n * t) * c * (n * t)⁻¹ = c := by
      calc (n * t) * c * (n * t)⁻¹ = n * (t * c * t⁻¹) * n⁻¹ := by group
        _ = n * (z * c) * n⁻¹ := by rw [htc]
        _ = (n * z * n⁻¹) * (n * c * n⁻¹) := by group
        _ = z * (z * c) := by rw [hnz', h]
        _ = c := by rw [← mul_assoc, hzz, one_mul]
    have hntz : (n * t) * z * (n * t)⁻¹ = z := by
      calc (n * t) * z * (n * t)⁻¹ = n * (t * z * t⁻¹) * n⁻¹ := by group
        _ = z := by rw [htz', hnz']
    have h1 := hmem (n * t) (hcent (n * t) hntz hntc) (mul_mem hnz htz)
    have h2 := mul_mem h1 (inv_mem (le_normalizer htQ))
    simpa using h2

theorem eq_of_one_lt_pRank
    (hQO : GoldschmidtQO) (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h21 : Step21) (h24 : Step24)
    (h26 : Step26) (h26ii : Step26ii) (h27 : Step27) (h211 : Step211) (h212 : Step212)
    (h215 : Step215) (h216 : Step216) (hQ : Sec2Q G A R g E F T₀ Q u y z) {c : G}
    (hc : c ∈ centralizer ({z} : Set G)) (hr : 1 < Open.pRank 2 (Q ⊓ rightConjugate Q c)) :
    rightConjugate Q c = Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hQ.data
  have hset := hd.setting
  have hSp : Special (sec2S A R E F) (sec2Z A E F) := special_of h24 hset
  obtain ⟨ψ, ρ, hadd, hsurj, hker, hsq, hρψ, hrange, -⟩ := h216 G A R g E F T₀ Q u y z hQ
  have hzQ := hQ.z_mem_Q
  have hMN : sec2M Q (sec2T E T₀) ≤ normalizer (Q : Set G) := hQ.M_le_normalizer
  have hNz : normalizer (Q : Set G) ≤ centralizer ({z} : Set G) := hQ.normalizer_le_centralizer
  have hψ1 : ψ 1 = 0 := by
    have h := hadd 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at h
    exact add_eq_left.mp h.symm
  have hψinv : ∀ a ∈ Q, ψ a⁻¹ = ψ a := by
    intro a ha
    have h := hadd a ha a⁻¹ (Q.inv_mem ha)
    rw [mul_inv_cancel, hψ1] at h
    have h2 : ψ a + ψ a = 0 := by
      funext k
      exact CharTwo.add_self_eq_zero _
    exact add_left_cancel (h.symm.trans h2.symm)
  have hψeq : ∀ a ∈ Q, ∀ b ∈ Q, ψ a = ψ b → a⁻¹ * b ∈ zpowers z := by
    intro a ha b hb hab
    rw [← hker _ (Q.mul_mem (Q.inv_mem ha) hb), hadd _ (Q.inv_mem ha) _ hb, hψinv a ha, hab]
    funext k
    exact CharTwo.add_self_eq_zero _
  obtain ⟨-, -, -, hZ2, -, -⟩ := (h212 G A R g E F hset).2 T₀ hd.le hd.sylow
  obtain ⟨-, h215ii, -⟩ := h215 G A R g E F T₀ Q u y z hQ
  have hZV : sec2Z A E F ≤ E ⊓ A := by
    rw [hset.frame.sec2Z_eq]
    exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hZQ : sec2Z A E F ≤ Q := by
    intro w hw
    have h1 : w ∈ E ⊓ A ⊓ Q := by
      rw [h215ii]
      refine mem_inf.mpr ⟨?_, hZV hw⟩
      rw [← hZ2] at hw
      obtain ⟨x, hx, rfl⟩ := hw
      exact ⟨x, Subgroup.upperCentralSeries_mono _ (by norm_num) hx, rfl⟩
    exact h1.2
  have hzcard : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hQ.order]
  obtain ⟨Ee, hEle, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two
    (Q ⊓ rightConjugate Q c)
  obtain ⟨a, haE, haz⟩ : ∃ a ∈ Ee, a ∉ zpowers z := by
    by_contra hcon
    have hle : Ee ≤ zpowers z := fun w hw => by_contra fun h => hcon ⟨w, hw, h⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [hzcard, hEcard] at h1
    have h2 : 2 ^ 2 ≤ 2 ^ Open.pRank 2 (Q ⊓ rightConjugate Q c) :=
      Nat.pow_le_pow_right (by norm_num) hr
    omega
  have ha2 : a * a = 1 := by rw [← sq]; exact hEel.2 a haE
  have haQ : a ∈ Q := (mem_inf.mp (hEle haE)).1
  have haQc : c * a * c⁻¹ ∈ Q := (mem_rightConjugate_iff _ _ _).mp (mem_inf.mp (hEle haE)).2
  have hca2 : (c * a * c⁻¹) * (c * a * c⁻¹) = 1 := by
    calc (c * a * c⁻¹) * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  have hcaz : c * a * c⁻¹ ∉ zpowers z := by
    intro h
    apply haz
    have h1 := conj_eq_of_mem_zpowers' (inv_mem hc) h
    rw [show c⁻¹ * (c * a * c⁻¹) * c⁻¹⁻¹ = a by group] at h1
    rw [h1]
    exact h
  have hzZ : z ∈ sec2Z A E F := z_mem_Z h212 hQ
  obtain ⟨c₀, hc₀Z, hc₀z⟩ : ∃ c₀ ∈ sec2Z A E F, c₀ ∉ zpowers z := by
    by_contra hcon
    have hle : sec2Z A E F ≤ zpowers z := fun w hw => by_contra fun h => hcon ⟨w, hw, h⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [hSp.card, hzcard] at h1
    norm_num at h1
  have hc₀Q : c₀ ∈ Q := hZQ hc₀Z
  have hc₀2 : c₀ * c₀ = 1 := hSp.elem c₀ hc₀Z
  have htrans : ∀ b ∈ Q, b * b = 1 → b ∉ zpowers z →
      ∃ m ∈ sec2M Q (sec2T E T₀), (m * c₀ * m⁻¹)⁻¹ * b ∈ zpowers z := by
    intro b hb hb2 hbz
    have hv : ψ c₀ ≠ 0 := fun h => hc₀z ((hker c₀ hc₀Q).mp h)
    have hw : ψ b ≠ 0 := fun h => hbz ((hker b hb).mp h)
    have hq : qMinus (ψ c₀) = qMinus (ψ b) := by
      rw [(hsq c₀ hc₀Q).mpr hc₀2, (hsq b hb).mpr hb2]
    obtain ⟨ω, hω, hωv⟩ := Sec2Omega.exists_mem_timmesfeldOmega_apply_eq hv hw hq
    rw [← hrange] at hω
    obtain ⟨m, rfl⟩ := hω
    refine ⟨m, m.2, ?_⟩
    have hmc : (m : G) * c₀ * (m : G)⁻¹ ∈ Q := (mem_normalizer_iff.mp (hMN m.2) c₀).mp hc₀Q
    exact hψeq _ hmc _ hb (by rw [hρψ m c₀ hc₀Q, hωv])
  obtain ⟨m₁, hm₁, hζ₁⟩ := htrans a haQ ha2 haz
  obtain ⟨m₂, hm₂, hζ₂⟩ := htrans _ haQc hca2 hcaz
  have hm₁z : m₁ ∈ centralizer ({z} : Set G) := hNz (hMN hm₁)
  have hm₂z : m₂ ∈ centralizer ({z} : Set G) := hNz (hMN hm₂)
  set n := m₂⁻¹ * c * m₁ with hndef
  have hnz : n ∈ centralizer ({z} : Set G) := mul_mem (mul_mem (inv_mem hm₂z) hc) hm₁z
  set ζ₁ := (m₁ * c₀ * m₁⁻¹)⁻¹ * a with hζ₁def
  set ζ₂ := (m₂ * c₀ * m₂⁻¹)⁻¹ * (c * a * c⁻¹) with hζ₂def
  have hnc₀ : n * c₀ * n⁻¹ = c₀ * (ζ₂ * ζ₁⁻¹) := by
    have e1 : m₁ * c₀ * m₁⁻¹ = a * ζ₁⁻¹ := by rw [hζ₁def]; group
    have e2 : c * a * c⁻¹ = m₂ * c₀ * m₂⁻¹ * ζ₂ := by rw [hζ₂def]; group
    have c1 : c * ζ₁⁻¹ * c⁻¹ = ζ₁⁻¹ := conj_eq_of_mem_zpowers' hc (inv_mem hζ₁)
    have c2 : m₂⁻¹ * (ζ₂ * ζ₁⁻¹) * m₂⁻¹⁻¹ = ζ₂ * ζ₁⁻¹ :=
      conj_eq_of_mem_zpowers' (inv_mem hm₂z) (mul_mem hζ₂ (inv_mem hζ₁))
    calc n * c₀ * n⁻¹ = m₂⁻¹ * c * (m₁ * c₀ * m₁⁻¹) * c⁻¹ * m₂ := by rw [hndef]; group
      _ = m₂⁻¹ * ((c * a * c⁻¹) * (c * ζ₁⁻¹ * c⁻¹)) * m₂ := by rw [e1]; group
      _ = m₂⁻¹ * (m₂ * c₀ * m₂⁻¹ * ζ₂ * ζ₁⁻¹) * m₂ := by rw [e2, c1]
      _ = c₀ * (m₂⁻¹ * (ζ₂ * ζ₁⁻¹) * m₂⁻¹⁻¹) := by group
      _ = c₀ * (ζ₂ * ζ₁⁻¹) := by rw [c2]
  have hnz' : n * z * n⁻¹ = z := conj_eq_of_mem_zpowers' hnz (mem_zpowers z)
  have hnZ : n ∈ normalizer (sec2Z A E F : Set G) := by
    have hz1 : z ≠ 1 := by
      intro h
      have := hQ.order
      rw [h, orderOf_one] at this
      omega
    have hc₀1 : c₀ ≠ 1 := fun h => hc₀z (h ▸ one_mem _)
    have hzc₀ : z ≠ c₀ := fun h => hc₀z (h ▸ mem_zpowers z)
    have hzc1 : z * c₀ ≠ 1 := by
      intro h
      apply hc₀z
      rw [eq_inv_of_mul_eq_one_right h]
      exact inv_mem (mem_zpowers z)
    have hzcz : z ≠ z * c₀ := fun h => hc₀1 (left_eq_mul.mp h)
    have hzcc : c₀ ≠ z * c₀ := fun h => hz1 (right_eq_mul.mp h)
    have hnζ : ζ₂ * ζ₁⁻¹ ∈ sec2Z A E F := zpowers_le.mpr hzZ (mul_mem hζ₂ (inv_mem hζ₁))
    apply AS76b.mem_normalizer_of_map_conj_le
    rintro _ ⟨w, hw, rfl⟩
    show n * w * n⁻¹ ∈ sec2Z A E F
    rcases hSp.eq_of_four (one_mem _) hzZ hc₀Z (mul_mem hzZ hc₀Z) hw hz1.symm hc₀1.symm
      hzc1.symm hzc₀ hzcz hzcc with rfl | rfl | rfl | rfl
    · simp
    · rw [hnz']
      exact hzZ
    · rw [hnc₀]
      exact mul_mem hc₀Z hnζ
    · rw [show n * (z * c₀) * n⁻¹ = (n * z * n⁻¹) * (n * c₀ * n⁻¹) by group, hnz', hnc₀]
      exact mul_mem hzZ (mul_mem hc₀Z hnζ)
  have hnN := mem_normalizer_of_mem_normalizer_sec2Z hQO h4 h34 hE16 h21 h24 h26 h26ii h27 h211
    h212 hQ hnZ hnz
  have hcN : c ∈ normalizer (Q : Set G) := by
    have e : c = m₂ * n * m₁⁻¹ := by rw [hndef]; group
    rw [e]
    exact mul_mem (mul_mem (hMN hm₂) hnN) (inv_mem (hMN hm₁))
  exact (rightConjugate_eq_self_iff Q c).mpr hcN

end Sec2Q

theorem step218ii_of
    (hQO : GoldschmidtQO) (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h21 : Step21) (h24 : Step24)
    (h26 : Step26) (h26ii : Step26ii) (h27 : Step27) (h211 : Step211) (h212 : Step212)
    (h215 : Step215) (h216 : Step216) :
    ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F T₀ Q : Subgroup G)
      (u y z : G), Sec2Q G A R g E F T₀ Q u y z →
        ∀ c ∈ centralizer ({z} : Set G), 1 < Open.pRank 2 (Q ⊓ rightConjugate Q c) →
          rightConjugate Q c = Q := by
  intro G _ _ A R g E F T₀ Q u y z hQ c hc hr
  exact Sec2Q.eq_of_one_lt_pRank hQO h4 h34 hE16 h21 h24 h26 h26ii h27 h211 h212 h215 h216 hQ hc hr

end CFSG.ComponentClassification.AS81
