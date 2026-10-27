module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltRank
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426SporKlein

variable {G : Type} [Group G]

section Klein

variable {t1 t2 : G} (h1 : t1 ^ 2 = 1) (h2 : t2 ^ 2 = 1) (hc : t1 * t2 = t2 * t1)

include h1 h2 hc in
theorem klein_mul_mem {a b : G} (ha : a = 1 ∨ a = t1 ∨ a = t2 ∨ a = t1 * t2)
    (hb : b = 1 ∨ b = t1 ∨ b = t2 ∨ b = t1 * t2) :
    a * b = 1 ∨ a * b = t1 ∨ a * b = t2 ∨ a * b = t1 * t2 := by
  have e1 : t1 * t1 = 1 := by rw [← sq]; exact h1
  have e2 : t2 * t2 = 1 := by rw [← sq]; exact h2
  have e3 : t1 * (t1 * t2) = t2 := by rw [← mul_assoc, e1, one_mul]
  have e4 : t2 * (t1 * t2) = t1 := by rw [← mul_assoc, ← hc, mul_assoc, e2, mul_one]
  have e5 : t1 * t2 * t1 = t2 := by rw [hc, mul_assoc, e1, mul_one]
  have e6 : t1 * t2 * t2 = t1 := by rw [mul_assoc, e2, mul_one]
  have e7 : t1 * t2 * (t1 * t2) = 1 := by rw [← mul_assoc, e5, e2]
  have e8 : t2 * t1 = t1 * t2 := hc.symm
  rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;> rw [ha, hb] <;>
    simp only [one_mul, mul_one, e1, e2, e3, e4, e5, e6, e7, e8, true_or, or_true]

@[expose] def kleinSub : Subgroup G where
  carrier := {a | a = 1 ∨ a = t1 ∨ a = t2 ∨ a = t1 * t2}
  one_mem' := Or.inl rfl
  mul_mem' ha hb := klein_mul_mem h1 h2 hc ha hb
  inv_mem' {a} ha := by
    have e1 : t1⁻¹ = t1 := inv_eq_of_mul_eq_one_left (by rw [← sq]; exact h1)
    have e2 : t2⁻¹ = t2 := inv_eq_of_mul_eq_one_left (by rw [← sq]; exact h2)
    rcases ha with ha | ha | ha | ha <;> rw [ha]
    · simp
    · exact Or.inr (Or.inl e1)
    · exact Or.inr (Or.inr (Or.inl e2))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [mul_inv_rev, e1, e2, hc]

theorem mem_kleinSub {a : G} :
    a ∈ kleinSub h1 h2 hc ↔ a = 1 ∨ a = t1 ∨ a = t2 ∨ a = t1 * t2 := Iff.rfl

theorem kleinSub_isElemAbelian : IsElemAbelian 2 (kleinSub h1 h2 hc) := by
  have hC : Commute t1 t2 := hc
  have hA : ∀ a ∈ kleinSub h1 h2 hc, Commute a t1 ∧ Commute a t2 := by
    intro a ha
    rcases ha with ha | ha | ha | ha <;> rw [ha]
    · exact ⟨Commute.one_left _, Commute.one_left _⟩
    · exact ⟨Commute.refl _, hC⟩
    · exact ⟨hC.symm, Commute.refl _⟩
    · exact ⟨(Commute.refl t1).mul_left hC.symm, hC.mul_left (Commute.refl t2)⟩
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩
  · obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    show a * b = b * a
    obtain ⟨ha1, ha2⟩ := hA a ha
    rcases hb with hb | hb | hb | hb <;> rw [hb]
    · exact (Commute.one_right a).eq
    · exact ha1.eq
    · exact ha2.eq
    · exact (ha1.mul_right ha2).eq
  · rcases ha with ha | ha | ha | ha <;> rw [ha]
    · exact one_pow 2
    · exact h1
    · exact h2
    · rw [hC.mul_pow, h1, h2, one_mul]

theorem card_kleinSub [DecidableEq G] (ht1 : t1 ≠ 1) (ht2 : t2 ≠ 1) (h12 : t1 ≠ t2) :
    Nat.card (kleinSub h1 h2 hc) = 4 := by
  have e1 : t1 * t1 = 1 := by rw [← sq]; exact h1
  have hs : ((kleinSub h1 h2 hc : Subgroup G) : Set G) = ({1, t1, t2, t1 * t2} : Finset G) := by
    ext a
    simp [mem_kleinSub, kleinSub]
  rw [← SetLike.coe_sort_coe, hs, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have n1 : t1 * t2 ≠ 1 := fun h => h12 (by
    have := congrArg (t1 * ·) h
    simpa [← mul_assoc, e1] using this.symm)
  have n2 : t1 * t2 ≠ t1 := fun h => ht2 (by
    have := congrArg (t1⁻¹ * ·) h
    simpa [← mul_assoc] using this)
  have n3 : t1 * t2 ≠ t2 := fun h => ht1 (by
    have := congrArg (· * t2⁻¹) h
    simpa [mul_assoc] using this)
  rw [Finset.card_insert_of_notMem (by simp [ht1.symm, ht2.symm, n1.symm]),
    Finset.card_insert_of_notMem (by simp [h12, n2.symm]),
    Finset.card_insert_of_notMem (by simp [n3.symm])]
  rfl

end Klein

structure KleinData (x y t1 t2 : G) : Prop where
  x3 : x ^ 3 = 1
  x1 : x ≠ 1
  y3 : y ^ 3 = 1
  y1 : y ≠ 1
  yx : y ≠ x
  yx2 : y ≠ x ^ 2
  xy : x * y = y * x
  t12 : t1 ^ 2 = 1
  t22 : t2 ^ 2 = 1
  t11 : t1 ≠ 1
  t21 : t2 ≠ 1
  t1t2 : t1 ≠ t2
  tc : t1 * t2 = t2 * t1
  xt1 : x * t1 = t1 * x
  xt2 : x * t2 = t2 * x
  yt1 : y * t1 * y⁻¹ = t2
  yt2 : y * t2 * y⁻¹ = t1 * t2

theorem mem_zpowers_of_pow_three {x g : G} (hx : x ^ 3 = 1) (hg : g ∈ Subgroup.zpowers x) :
    g = 1 ∨ g = x ∨ g = x ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have hk : x ^ k = x ^ (k % 3) :=
    zpow_eq_zpow_emod k (show x ^ (3 : ℤ) = 1 by exact_mod_cast hx)
  rw [hk]
  have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases this with h | h | h <;> rw [h]
  · exact Or.inl (zpow_zero x)
  · exact Or.inr (Or.inl (zpow_one x))
  · exact Or.inr (Or.inr (by exact_mod_cast zpow_natCast x 2))

variable {x y t1 t2 : G}

@[expose] def MapsInto (T : Subgroup G) (g : G) : Prop := ∀ t ∈ T, g * t * g⁻¹ ∈ T

theorem MapsInto.mul {T : Subgroup G} {g h : G} (hg : MapsInto T g) (hh : MapsInto T h) :
    MapsInto T (g * h) := fun t ht => by
  have := hg _ (hh t ht)
  simpa [mul_assoc] using this

theorem mem_normalizer_of_mapsInto {T : Subgroup G} {g : G} (hg : MapsInto T g)
    (hg' : MapsInto T g⁻¹) : g ∈ Subgroup.normalizer (T : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · exact hg t
  · intro ht
    have := hg' _ ht
    simpa [mul_assoc] using this

theorem mapsInto_inv_of_cube {T : Subgroup G} {g : G} (hg : MapsInto T g) (h3 : g ^ 3 = 1) :
    MapsInto T g⁻¹ := by
  have : g⁻¹ = g * g := inv_eq_of_mul_eq_one_left (by rw [← h3, pow_succ, sq])
  rw [this]
  exact hg.mul hg

theorem kleinData_spec [Finite G] (h : KleinData x y t1 t2) :
    Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) = 9 ∧
      (∀ d ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y, ∀ t ∈ kleinSub h.t12 h.t22 h.tc,
        d * t * d⁻¹ ∈ kleinSub h.t12 h.t22 h.tc) ∧
      (∀ t ∈ kleinSub h.t12 h.t22 h.tc, ∃ d ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y,
        ∃ s ∈ kleinSub h.t12 h.t22 h.tc, d * s * d⁻¹ * s⁻¹ = t) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T := kleinSub h.t12 h.t22 h.tc with hT
  have e1 : t1 * t1 = 1 := by rw [← sq]; exact h.t12
  have e2 : t2 * t2 = 1 := by rw [← sq]; exact h.t22
  have i1 : t1⁻¹ = t1 := inv_eq_of_mul_eq_one_left e1
  have i2 : t2⁻¹ = t2 := inv_eq_of_mul_eq_one_left e2
  have hxT : MapsInto T x := by
    intro t ht
    have hxt : x * t = t * x := by
      rcases ht with h0 | h0 | h0 | h0 <;> rw [h0]
      · simp
      · exact h.xt1
      · exact h.xt2
      · rw [← mul_assoc, h.xt1, mul_assoc, h.xt2, mul_assoc]
    rw [hxt, mul_inv_cancel_right]
    exact ht
  have hy12 : y * (t1 * t2) * y⁻¹ = t1 := by
    calc y * (t1 * t2) * y⁻¹ = (y * t1 * y⁻¹) * (y * t2 * y⁻¹) := by group
      _ = t2 * (t1 * t2) := by rw [h.yt1, h.yt2]
      _ = t1 := by rw [← mul_assoc, ← h.tc, mul_assoc, e2, mul_one]
  have hyT : MapsInto T y := by
    intro t ht
    rcases ht with h0 | h0 | h0 | h0 <;> rw [h0]
    · simp only [mul_one, mul_inv_cancel]; exact T.one_mem
    · rw [h.yt1]; exact Or.inr (Or.inr (Or.inl rfl))
    · rw [h.yt2]; exact Or.inr (Or.inr (Or.inr rfl))
    · rw [hy12]; exact Or.inr (Or.inl rfl)
  have hxN := mem_normalizer_of_mapsInto hxT (mapsInto_inv_of_cube hxT h.x3)
  have hyN := mem_normalizer_of_mapsInto hyT (mapsInto_inv_of_cube hyT h.y3)
  have hPN : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (T : Set G) :=
    sup_le (Subgroup.zpowers_le.2 hxN) (Subgroup.zpowers_le.2 hyN)
  refine ⟨?_, fun d hd t ht => (Subgroup.mem_normalizer_iff.1 (hPN hd) t).1 ht, ?_⟩
  ·
    have hyNx : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
      refine Subgroup.zpowers_le.2 ?_
      rw [Subgroup.mem_normalizer_iff]
      intro g
      have hc : ∀ g ∈ Subgroup.zpowers x, y * g * y⁻¹ = g := by
        intro g hg
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
        have hcm : Commute y x := h.xy.symm
        rw [(hcm.zpow_right k).eq, mul_inv_cancel_right]
      constructor
      · intro hg; rw [hc g hg]; exact hg
      · intro hg
        have hcm : Commute y⁻¹ x := (Commute.inv_left h.xy.symm)
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg
        have e : g = y⁻¹ * x ^ k * y := by rw [hk]; group
        rw [e, (hcm.zpow_right k).eq, inv_mul_cancel_right]
        exact Subgroup.zpow_mem_zpowers x k
    have hprod := card_sup_mul_card_inf_of_le_normalizer hyNx
    have hcx : Nat.card (Subgroup.zpowers x) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime h.x3 h.x1]
    have hcy : Nat.card (Subgroup.zpowers y) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime h.y3 h.y1]
    have hinf : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers y) = 1 := by
      have hd : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers y) ∣ 3 := by
        rw [← hcy]; exact Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
      · exact h1
      · exfalso
        have heq : Subgroup.zpowers x ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hcy])
        have hy' : y ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers y := by
          rw [heq]; exact Subgroup.mem_zpowers y
        have hy : y ∈ Subgroup.zpowers x := (Subgroup.mem_inf.1 hy').1
        rcases mem_zpowers_of_pow_three h.x3 hy with h' | h' | h'
        · exact h.y1 h'
        · exact h.yx h'
        · exact h.yx2 h'
    rw [hinf, mul_one, hcx, hcy] at hprod
    exact hprod
  ·
    have hyP : y ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    intro t ht
    rcases ht with h0 | h0 | h0 | h0 <;> rw [h0]
    · exact ⟨1, Subgroup.one_mem _, 1, T.one_mem, by simp⟩
    · refine ⟨y, hyP, t2, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
      rw [h.yt2, i2, mul_assoc, e2, mul_one]
    · refine ⟨y, hyP, t1 * t2, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
      rw [hy12, mul_inv_rev, i1, i2, ← mul_assoc, h.tc, mul_assoc, e1, mul_one]
    · refine ⟨y, hyP, t1, Or.inr (Or.inl rfl), ?_⟩
      rw [h.yt1, i1, h.tc]

theorem klein_of_sylow [Finite G] (hfac : (Nat.card G).factorization 3 = 2)
    (h : KleinData x y t1 t2) (D : Subgroup G) (hD : Nat.card D = 9) :
    ∃ T0 : Subgroup G, IsElemAbelian 2 T0 ∧ Nat.card T0 = 4 ∧
      (∀ d ∈ D, ∀ t ∈ T0, d * t * d⁻¹ ∈ T0) ∧
      (∀ t ∈ T0, ∃ d ∈ D, ∃ s ∈ T0, d * s * d⁻¹ * s⁻¹ = t) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hPc, hPn, hPcov⟩ := kleinData_spec h
  set P := Subgroup.zpowers x ⊔ Subgroup.zpowers y
  set T := kleinSub h.t12 h.t22 h.tc
  have h9 : (9 : ℕ) = 3 ^ (Nat.card G).factorization 3 := by rw [hfac]; norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (Sylow.ofCard P (hPc.trans h9))
    (Sylow.ofCard D (hD.trans h9))
  have hmemD : ∀ d ∈ D, ∃ p ∈ P, g * p * g⁻¹ = d := by
    intro d hd
    have hd' : d ∈ ((g • Sylow.ofCard P (hPc.trans h9) : Sylow 3 G) : Subgroup G) := by
      rw [hg]; exact hd
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hd'
    obtain ⟨p, hp, hpd⟩ := hd'
    exact ⟨p, hp, by rw [← hpd, MulAut.smul_def, MulAut.conj_apply]⟩
  have hPD : ∀ p ∈ P, g * p * g⁻¹ ∈ D := by
    intro p hp
    have : g * p * g⁻¹ ∈ ((g • Sylow.ofCard P (hPc.trans h9) : Sylow 3 G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨p, hp, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
    rwa [hg] at this
  set T0 : Subgroup G := T.map (MulAut.conj g).toMonoidHom with hT0
  have hT0mem : ∀ u, u ∈ T0 ↔ ∃ t ∈ T, g * t * g⁻¹ = u := by
    intro u
    rw [hT0, Subgroup.mem_map]
    simp [MulAut.conj_apply]
  refine ⟨T0, KD264Rank.isElemAbelian_map (MulAut.conj g).injective
    (kleinSub_isElemAbelian h.t12 h.t22 h.tc), ?_, ?_, ?_⟩
  · rw [hT0, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact card_kleinSub h.t12 h.t22 h.tc h.t11 h.t21 h.t1t2
  · intro d hd u hu
    obtain ⟨p, hp, rfl⟩ := hmemD d hd
    obtain ⟨t, ht, rfl⟩ := (hT0mem u).1 hu
    rw [hT0mem]
    exact ⟨p * t * p⁻¹, hPn p hp t ht, by group⟩
  · intro u hu
    obtain ⟨t, ht, rfl⟩ := (hT0mem u).1 hu
    obtain ⟨p, hp, s, hs, hps⟩ := hPcov t ht
    refine ⟨g * p * g⁻¹, hPD p hp, g * s * g⁻¹, (hT0mem _).2 ⟨s, hs, rfl⟩, ?_⟩
    rw [← hps]
    group

end CFSG.LocalAnalysis.GLTheoremA.KD1426SporKlein
