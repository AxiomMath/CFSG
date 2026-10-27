module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspL33Bridge
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesConfining

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.L33Insp

open CFSG.Open

def rawSub (l : List Nat) (hl : ∀ x ∈ l, x < 19683 ∧ ndet x = 1) (h1 : nid ∈ l)
    (hmul : ∀ x ∈ l, ∀ y ∈ l, nmul x y ∈ l) (hinv : ∀ x ∈ l, ∃ y ∈ l, nmul x y = nid) :
    Subgroup S3 where
  carrier := {x | rn x ∈ l}
  mul_mem' := by
    intro x y hx hy
    show rn (x * y) ∈ l
    rw [rn_mul]
    exact hmul _ hx _ hy
  one_mem' := by
    show rn 1 ∈ l
    rw [rn_one]
    exact h1
  inv_mem' := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hinv _ hx
    obtain ⟨hy1, hy2⟩ := hl y hy
    have hx1 : x * ofN y hy2 = 1 := by
      apply rn_inj
      rw [rn_mul, rn_ofN y hy1 hy2, hxy, rn_one]
    show rn x⁻¹ ∈ l
    rw [inv_eq_of_mul_eq_one_right hx1, rn_ofN y hy1 hy2]
    exact hy

theorem card_rawSub {l : List Nat} {hl : ∀ x ∈ l, x < 19683 ∧ ndet x = 1} {h1 : nid ∈ l}
    {hmul : ∀ x ∈ l, ∀ y ∈ l, nmul x y ∈ l} {hinv : ∀ x ∈ l, ∃ y ∈ l, nmul x y = nid}
    (hnd : l.Nodup) : Nat.card (rawSub l hl h1 hmul hinv) = l.length := by
  have e : rawSub l hl h1 hmul hinv ≃ {a // a ∈ l} :=
    { toFun := fun x => ⟨rn x.1, x.2⟩
      invFun := fun a => ⟨ofN a.1 (hl _ a.2).2, by
        show rn (ofN a.1 (hl _ a.2).2) ∈ l
        rw [rn_ofN _ (hl _ a.2).1]
        exact a.2⟩
      left_inv := fun x => Subtype.ext (rn_inj (rn_ofN _ (hl _ x.2).1 (hl _ x.2).2))
      right_inv := fun a => Subtype.ext (rn_ofN _ (hl _ a.2).1 (hl _ a.2).2) }
  rw [Nat.card_congr e, card_subtype_mem hnd]

theorem t16_facts : (∀ x ∈ t16p, x < 19683 ∧ ndet x = 1) ∧ nid ∈ t16p ∧
    (∀ x ∈ t16p, ∀ y ∈ t16p, nmul x y ∈ t16p) ∧ (∀ x ∈ t16p, ∃ y ∈ t16p, nmul x y = nid) ∧
    t16p.Nodup ∧ t16p.length = 16 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := t16_check
  exact ⟨fun x hx => ⟨h7 x hx, (h1 x hx).1⟩, h2, h3, h4, h5, h6⟩

def T16 : Subgroup S3 :=
  rawSub t16p t16_facts.1 t16_facts.2.1 t16_facts.2.2.1 t16_facts.2.2.2.1

theorem mem_T16 {x : S3} : x ∈ T16 ↔ rn x ∈ t16p := Iff.rfl

theorem card_T16 : Nat.card T16 = 16 := by
  rw [T16, card_rawSub t16_facts.2.2.2.2.1, t16_facts.2.2.2.2.2]

theorem T16_pgroup : IsPGroup 2 T16 := IsPGroup.of_card (n := 4) (by rw [card_T16]; norm_num)

def u0 : S3 := ofN nt0 (by decide)

theorem rn_u0 : rn u0 = nt0 := rn_ofN nt0 (by decide) (by decide)

theorem u0_sq : u0 * u0 = 1 := by
  apply rn_inj
  rw [rn_mul, rn_u0, rn_one]
  decide +kernel

theorem u0_ne_one : u0 ≠ 1 := by
  intro h
  have := congrArg rn h
  rw [rn_u0, rn_one] at this
  revert this
  decide +kernel

def Cs : Subgroup S3 := Subgroup.centralizer ({u0} : Set S3)

theorem mem_Cs {x : S3} : x ∈ Cs ↔ nmul (rn x) nt0 = nmul nt0 (rn x) := by
  unfold Cs
  rw [Subgroup.mem_centralizer_singleton_iff, ← rn_inj.eq_iff, rn_mul, rn_mul, rn_u0]

theorem T16_le_Cs : T16 ≤ Cs := by
  intro x hx
  rw [mem_Cs]
  exact (t16_check.1 _ hx).2

theorem card_dvd_sixteen {Q : Subgroup S3} (hQ : IsPGroup 2 Q) : Nat.card Q ∣ 16 := by
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hdvd : Nat.card Q ∣ 5616 := card_S3 ▸ Subgroup.card_subgroup_dvd_card Q
  rw [hn] at hdvd ⊢
  have hcop : Nat.Coprime (2 ^ n) 351 := Nat.Coprime.pow_left n (by norm_num)
  exact hcop.dvd_of_dvd_mul_right (by simpa using hdvd)

theorem pCoreOf_le_T16 {Y : Subgroup S3} (hCY : Cs ≤ Y) : pCoreOf 2 Y ≤ T16 := by
  have hT : T16 ≤ Y := T16_le_Cs.trans hCY
  obtain ⟨P, hTP, hP⟩ := exists_isSylowTwoOf_of_le hT T16_pgroup
  have hP16 : Nat.card P ∣ 16 := card_dvd_sixteen hP.isPGroup
  have hTP' : T16 = P := Subgroup.eq_of_le_of_card_ge hTP (by
    rw [card_T16]
    exact Nat.le_of_dvd (by norm_num) hP16)
  rw [hTP']
  exact hP.pCoreOf_le

theorem rn_sq (w : S3) : rn (w ^ 2) = nsq (rn w) := by
  rw [sq, rn_mul]
  rfl

theorem rn_pow16 (z : S3) : rn (z ^ 16) = npow16 (rn z) := by
  have h : z ^ 16 = (((z ^ 2) ^ 2) ^ 2) ^ 2 := by
    rw [← pow_mul, ← pow_mul, ← pow_mul]
  rw [h, rn_sq, rn_sq, rn_sq, rn_sq]
  rfl

theorem c48_mem {c : Nat} (hc : c ∈ c48p) : c < 19683 ∧ ∃ h : ndet c = 1, ofN c h ∈ Cs := by
  obtain ⟨h1, h2, h3⟩ := c48_check c hc
  exact ⟨h1, h2, by rw [mem_Cs, rn_ofN c h1 h2]; exact h3⟩

theorem main_t0 {Y : Subgroup S3} (hCY : Cs ≤ Y) (hY : CharTwo Y) : Y = Cs := by
  have hQT : pCoreOf 2 Y ≤ T16 := pCoreOf_le_T16 hCY
  have hnorm : Y ≤ Subgroup.normalizer ((pCoreOf 2 Y : Subgroup S3) : Set S3) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 Y
  have hcent : Y ⊓ Subgroup.centralizer ((pCoreOf 2 Y : Subgroup S3) : Set S3) ≤ pCoreOf 2 Y := hY
  generalize pCoreOf 2 Y = Q at hQT hnorm hcent
  have hconj : ∀ y ∈ Y, ∀ q ∈ Q, y * q * y⁻¹ ∈ Q := fun y hy q hq =>
    (Subgroup.mem_normalizer_iff.mp (hnorm hy) q).mp hq
  have hQ8 : ∀ x ∈ Q, rn x ∈ q8p := by
    intro x hxQ
    by_contra hxn
    obtain ⟨c, hc, y, hy, hcxy, hne⟩ := t16_not_q8 _ (hQT hxQ) hxn
    obtain ⟨hc1, hc2, hcC⟩ := c48_mem hc
    obtain ⟨hy1, hy2, hyC⟩ := c48_mem hy
    have hcx : ofN c hc2 * x = ofN y hy2 * ofN c hc2 := by
      apply rn_inj
      rw [rn_mul, rn_mul, rn_ofN c hc1 hc2, rn_ofN y hy1 hy2]
      exact hcxy
    have hyx : ofN y hy2 = ofN c hc2 * x * (ofN c hc2)⁻¹ := by
      rw [hcx]
      group
    have hyQ : ofN y hy2 ∈ Q := by
      rw [hyx]
      exact hconj _ (hCY hcC) x hxQ
    have hxyT : x * ofN y hy2 ∈ T16 := T16.mul_mem (hQT hxQ) (hQT hyQ)
    have h16 : (x * ofN y hy2) ^ 16 = 1 := by
      have h := pow_card_eq_one' (G := T16) (x := ⟨x * ofN y hy2, hxyT⟩)
      rw [card_T16] at h
      exact congrArg Subtype.val h
    apply hne
    have h := congrArg rn h16
    rwa [rn_pow16, rn_mul, rn_ofN y hy1 hy2, rn_one] at h
  have hq8 := q8_check
  by_cases hA : ∀ x ∈ Q, rn x = nid ∨ rn x = nt0
  ·
    exfalso
    have hq4T : q4p ∈ t16p := hq8.1 _ hq8.2.2.2.2.1
    obtain ⟨hq41, hq42⟩ := (t16_facts.1 _ hq4T)
    have hq4C : ofN q4p hq42 ∈ Cs := by
      rw [mem_Cs, rn_ofN _ hq41 hq42]
      exact (t16_check.1 _ hq4T).2
    have hcentm : ofN q4p hq42 ∈ Subgroup.centralizer (Q : Set S3) := by
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro z hz
      rcases hA z hz with h | h
      · have : z = 1 := rn_inj (by rw [h, rn_one])
        rw [this]
        simp
      · have : z = u0 := rn_inj (by rw [h, rn_u0])
        rw [this]
        exact ((Subgroup.mem_centralizer_singleton_iff.mp hq4C).symm)
    have hmem : ofN q4p hq42 ∈ Y ⊓ Subgroup.centralizer (Q : Set S3) := ⟨hCY hq4C, hcentm⟩
    have hq := hcent hmem
    have h := hA _ hq
    rw [rn_ofN _ hq41 hq42] at h
    rcases h with h | h
    · exact hq8.2.2.2.2.2.1 h
    · exact hq8.2.2.2.2.2.2 h
  ·
    push Not at hA
    obtain ⟨x, hxQ, hx1, hx2⟩ := hA
    have hsq : x * x = u0 := by
      apply rn_inj
      rw [rn_mul, rn_u0]
      exact hq8.2.2.2.1 _ (hQ8 x hxQ) hx1 hx2
    have hu0Q : u0 ∈ Q := hsq ▸ Q.mul_mem hxQ hxQ
    have hYC : Y ≤ Cs := by
      intro y hy
      have hw := hconj y hy u0 hu0Q
      have hw8 := hQ8 _ hw
      have hww : (y * u0 * y⁻¹) * (y * u0 * y⁻¹) = 1 := by
        calc (y * u0 * y⁻¹) * (y * u0 * y⁻¹) = y * (u0 * u0) * y⁻¹ := by group
          _ = 1 := by rw [u0_sq]; group
      have hw1 : y * u0 * y⁻¹ ≠ 1 := by
        intro h
        apply u0_ne_one
        calc u0 = y⁻¹ * (y * u0 * y⁻¹) * y := by group
          _ = 1 := by rw [h]; group
      have hwr : rn (y * u0 * y⁻¹) = nt0 := by
        by_contra hne
        have hne1 : rn (y * u0 * y⁻¹) ≠ nid := fun h => hw1 (rn_inj (by rw [h, rn_one]))
        have h2 := hq8.2.2.2.1 _ hw8 hne1 hne
        rw [← rn_mul, hww, rn_one] at h2
        revert h2
        decide +kernel
      have hweq : y * u0 * y⁻¹ = u0 := rn_inj (by rw [hwr, rn_u0])
      rw [Cs, Subgroup.mem_centralizer_singleton_iff]
      calc y * u0 = (y * u0 * y⁻¹) * y := by group
        _ = u0 * y := by rw [hweq]
    exact le_antisymm hYC hCY

theorem charTwo_map_mulEquiv {G G' : Type*} [Group G] [Group G'] {Y : Subgroup G} (e : G ≃* G')
    (hY : CharTwo Y) : CharTwo (Y.map e.toMonoidHom) :=
  charTwo_iff_internal.mpr
    (CFSG.RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_of_mulEquiv 2
      (Subgroup.equivMapOfInjective Y e.toMonoidHom e.injective) (charTwo_iff_internal.mp hY))

theorem exists_conj_u0 {t : S3} (ht2 : t * t = 1) (ht1 : t ≠ 1) : ∃ g : S3, g * u0 * g⁻¹ = t := by
  have hmem := rn_mem_nL t
  have hsq : nmul (rn t) (rn t) = nid := by rw [← rn_mul, ht2, rn_one]
  have hne : rn t ≠ nid := fun h => ht1 (rn_inj (by rw [h, rn_one]))
  rcases inv_check _ hmem hne hsq with h | ⟨e, he, h⟩
  · exact ⟨1, by rw [one_mul, inv_one, mul_one]; exact rn_inj (by rw [h, rn_u0])⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := invTable_check e he
    refine ⟨ofN e.2 h4, ?_⟩
    have hg : ofN e.2 h4 * u0 = t * ofN e.2 h4 := by
      apply rn_inj
      rw [rn_mul, rn_mul, rn_ofN _ h2 h4, rn_u0, ← h, h7]
    rw [mul_inv_eq_iff_eq_mul]
    exact hg

theorem main_inv {t : S3} (ht2 : t * t = 1) (ht1 : t ≠ 1) {Y : Subgroup S3}
    (hCY : Subgroup.centralizer ({t} : Set S3) ≤ Y) (hY : CharTwo Y) :
    Y = Subgroup.centralizer ({t} : Set S3) := by
  obtain ⟨g, hg⟩ := exists_conj_u0 ht2 ht1
  let e : S3 ≃* S3 := MulAut.conj g⁻¹
  have he : ∀ x, e x = g⁻¹ * x * g := fun x => by simp [e]
  have hY' : CharTwo (Y.map e.toMonoidHom) := charTwo_map_mulEquiv e hY
  have hC : Cs ≤ Y.map e.toMonoidHom := by
    intro c hc
    refine ⟨g * c * g⁻¹, hCY ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff, Cs, Subgroup.mem_centralizer_singleton_iff] at *
      rw [← hg]
      calc g * c * g⁻¹ * (g * u0 * g⁻¹) = g * (c * u0) * g⁻¹ := by group
        _ = g * (u0 * c) * g⁻¹ := by rw [hc]
        _ = g * u0 * g⁻¹ * (g * c * g⁻¹) := by group
    · show e (g * c * g⁻¹) = c
      rw [he]
      group
  have h0 := main_t0 hC hY'
  apply le_antisymm _ hCY
  intro y hy
  have hy' : e y ∈ Y.map e.toMonoidHom := ⟨y, hy, rfl⟩
  rw [h0, Cs, Subgroup.mem_centralizer_singleton_iff, he] at hy'
  rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
  calc y * (g * u0 * g⁻¹) = g * ((g⁻¹ * y * g) * u0) * g⁻¹ := by group
    _ = g * (u0 * (g⁻¹ * y * g)) * g⁻¹ := by rw [hy']
    _ = g * u0 * g⁻¹ * y := by group

end CFSG.QuasithinUnique.Vol2Native.L239.L33Insp
