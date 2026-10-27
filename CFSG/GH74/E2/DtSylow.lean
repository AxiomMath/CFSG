module

public import CFSG.RankThree.Asc83Table.GL23
public import CFSG.Dihedral.DisconnectedInvolutionGraph.QuaternionCoordinateEquiv
public meta import Mathlib
public import Certificates.Certificate5009

public section

namespace CFSG.GH74.E2

open Subgroup

section Q8Facts

private theorem q8_center : ∀ x : QuaternionGroup 2,
    (∀ y, x * y = y * x) ↔ (x = 1 ∨ x = QuaternionGroup.a 2) := by decide

private theorem q8_sq : ∀ x : QuaternionGroup 2, x ≠ 1 → x ≠ QuaternionGroup.a 2 →
    x * x = QuaternionGroup.a 2 := by decide

private theorem q8_exists_out : ∀ w : QuaternionGroup 2, w ≠ 1 → w ≠ QuaternionGroup.a 2 →
    ∃ y, y ≠ 1 ∧ y ≠ QuaternionGroup.a 2 ∧ y ≠ w ∧ y ≠ w⁻¹ := by decide

private theorem q8_inv : ∀ w y : QuaternionGroup 2,
    (w = 1 ∨ w = QuaternionGroup.a 2 ∨ y = 1 ∨ y = QuaternionGroup.a 2 ∨ y = w ∨ y = w⁻¹) ∨
      y * w * y⁻¹ = w⁻¹ := by decide

private theorem q8_card_aut :
    Nat.card (MulAut (QuaternionGroup 2)) = 24 :=
  Certificates.certificate5009.1

private theorem q8_inner : ∀ σ : MulAut (QuaternionGroup 2),
    (∀ q, σ q * q = 1 ∨ σ q * q = QuaternionGroup.a 2) →
      ∃ q0, ∀ x, σ x = q0 * x * q0⁻¹ :=
  Certificates.certificate5009.2

end Q8Facts

private structure Q8Data {D : Type} [Group D] (Q : Subgroup D) (z : D) : Prop where
  card : Nat.card Q = 8
  zmem : z ∈ Q
  zne : z ≠ 1
  zsq : z * z = 1
  center : ∀ d ∈ Q, (∀ q ∈ Q, d * q = q * d) ↔ (d = 1 ∨ d = z)
  sq : ∀ x ∈ Q, x ≠ 1 → x ≠ z → x * x = z
  exists_out : ∀ w ∈ Q, w ≠ 1 → w ≠ z → ∃ y ∈ Q, y ≠ 1 ∧ y ≠ z ∧ y ≠ w ∧ y ≠ w⁻¹
  inv : ∀ w ∈ Q, ∀ y ∈ Q,
    (w = 1 ∨ w = z ∨ y = 1 ∨ y = z ∨ y = w ∨ y = w⁻¹) ∨ y * w * y⁻¹ = w⁻¹
  aut : Nat.card (MulAut ↥Q) = 24
  inner : ∀ σ : MulAut ↥Q,
    (∀ q : ↥Q, ((σ q * q : ↥Q) : D) = 1 ∨ ((σ q * q : ↥Q) : D) = z) →
      ∃ q0 : ↥Q, ∀ x : ↥Q, σ x = q0 * x * q0⁻¹

private theorem q8Data
    {D : Type} [Group D] (Q : Subgroup D) (e : ↥Q ≃* QuaternionGroup 2) :
    Q8Data Q ((e.symm (QuaternionGroup.a 2) : ↥Q) : D) := by
  have hne1 : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide
  have hsq1 : (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 := by decide
  have hez : ∀ x : ↥Q, e x = QuaternionGroup.a 2 ↔ x = e.symm (QuaternionGroup.a 2) := fun x =>
    (MulEquiv.eq_symm_apply e).symm
  have he1 : ∀ x : ↥Q, e x = 1 ↔ x = 1 := fun x => by
    rw [← map_one e]
    exact e.injective.eq_iff
  refine ⟨?_, (e.symm (QuaternionGroup.a 2)).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  · intro h
    have h1 : e.symm (QuaternionGroup.a 2) = 1 := Subtype.ext h
    apply hne1
    have := congrArg e h1
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  · have h1 : e.symm (QuaternionGroup.a 2) * e.symm (QuaternionGroup.a 2) = 1 := by
      apply e.injective
      rw [map_mul, MulEquiv.apply_symm_apply, map_one]
      exact hsq1
    exact congrArg Subtype.val h1
  · intro d hd
    constructor
    · intro hcomm
      have h1 : ∀ y : QuaternionGroup 2, e ⟨d, hd⟩ * y = y * e ⟨d, hd⟩ := by
        intro y
        have h2 := hcomm _ (e.symm y).2
        have h3 : (⟨d, hd⟩ : ↥Q) * e.symm y = e.symm y * ⟨d, hd⟩ := Subtype.ext h2
        have h4 := congrArg e h3
        rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h4
      rcases (q8_center _).1 h1 with h | h
      · exact Or.inl (congrArg Subtype.val ((he1 _).1 h))
      · exact Or.inr (congrArg Subtype.val ((hez _).1 h))
    · intro h q hq
      have hcq : ∀ y : QuaternionGroup 2, e ⟨d, hd⟩ * y = y * e ⟨d, hd⟩ := by
        intro y
        rcases h with h | h
        · have : (⟨d, hd⟩ : ↥Q) = 1 := Subtype.ext h
          rw [this, map_one, one_mul, mul_one]
        · have : (⟨d, hd⟩ : ↥Q) = e.symm (QuaternionGroup.a 2) := Subtype.ext h
          rw [this, MulEquiv.apply_symm_apply]
          exact (q8_center _).2 (Or.inr rfl) y
      have h1 := hcq (e ⟨q, hq⟩)
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (e.injective h1)
  · intro x hx h1 hz'
    have h1' : e ⟨x, hx⟩ ≠ 1 := fun h => h1 (congrArg Subtype.val ((he1 _).1 h))
    have h2' : e ⟨x, hx⟩ ≠ QuaternionGroup.a 2 := fun h => hz' (congrArg Subtype.val ((hez _).1 h))
    have h3 := q8_sq _ h1' h2'
    rw [← map_mul, hez] at h3
    exact congrArg Subtype.val h3
  · intro w hw hw1 hwz
    have h1' : e ⟨w, hw⟩ ≠ 1 := fun h => hw1 (congrArg Subtype.val ((he1 _).1 h))
    have h2' : e ⟨w, hw⟩ ≠ QuaternionGroup.a 2 := fun h => hwz (congrArg Subtype.val ((hez _).1 h))
    obtain ⟨Y, hY1, hYz, hYw, hYw'⟩ := q8_exists_out _ h1' h2'
    refine ⟨((e.symm Y : ↥Q) : D), (e.symm Y).2, ?_, ?_, ?_, ?_⟩
    · intro h
      apply hY1
      have : e.symm Y = 1 := Subtype.ext h
      rwa [MulEquiv.symm_apply_eq, map_one] at this
    · intro h
      apply hYz
      have : e.symm Y = e.symm (QuaternionGroup.a 2) := Subtype.ext h
      exact e.symm.injective this
    · intro h
      apply hYw
      have : e.symm Y = ⟨w, hw⟩ := Subtype.ext h
      rwa [MulEquiv.symm_apply_eq] at this
    · intro h
      apply hYw'
      have : e.symm Y = (⟨w, hw⟩ : ↥Q)⁻¹ := Subtype.ext h
      rwa [MulEquiv.symm_apply_eq, map_inv] at this
  · intro w hw y hy
    rcases q8_inv (e ⟨w, hw⟩) (e ⟨y, hy⟩) with h | h
    · left
      rcases h with h | h | h | h | h | h
      · exact Or.inl (congrArg Subtype.val ((he1 _).1 h))
      · exact Or.inr (Or.inl (congrArg Subtype.val ((hez _).1 h)))
      · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val ((he1 _).1 h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (congrArg Subtype.val ((hez _).1 h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (congrArg Subtype.val (e.injective h))))))
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
        have := e.injective (h.trans (map_inv e _).symm)
        exact congrArg Subtype.val this
    · right
      have h' : e (⟨y, hy⟩ * ⟨w, hw⟩ * (⟨y, hy⟩ : ↥Q)⁻¹) = e ((⟨w, hw⟩ : ↥Q)⁻¹) := by
        rw [map_mul, map_mul, map_inv, map_inv]
        exact h
      exact congrArg Subtype.val (e.injective h')
  · rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact q8_card_aut
  · intro σ hσ
    have h1 : ∀ q : QuaternionGroup 2, (MulAut.congr e σ) q * q = 1 ∨
        (MulAut.congr e σ) q * q = QuaternionGroup.a 2 := by
      intro q
      have hq : (MulAut.congr e σ) q = e (σ (e.symm q)) := rfl
      have key : e (σ (e.symm q) * e.symm q) = (MulAut.congr e σ) q * q := by
        rw [map_mul, hq, MulEquiv.apply_symm_apply]
      rcases hσ (e.symm q) with h | h
      · left
        have h' : σ (e.symm q) * e.symm q = 1 := Subtype.ext h
        rw [← key, h', map_one]
      · right
        have h' : σ (e.symm q) * e.symm q = e.symm (QuaternionGroup.a 2) := Subtype.ext h
        rw [← key, h', MulEquiv.apply_symm_apply]
    obtain ⟨q0, hq0⟩ := q8_inner _ h1
    refine ⟨e.symm q0, fun x => ?_⟩
    apply e.injective
    have h2 := hq0 (e x)
    have h3 : (MulAut.congr e σ) (e x) = e (σ x) := by
      change e (σ (e.symm (e x))) = e (σ x)
      rw [MulEquiv.symm_apply_apply]
    rw [h3] at h2
    rw [h2, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

section Q16

private theorem pow_mod_eight' {X : Type*} [Group X] {x : X} (hx : x ^ 8 = 1) (n : ℕ) :
    x ^ (n % 8) = x ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 8, pow_add, pow_mul, hx, one_pow, mul_one]

private noncomputable def coordHom8 {X : Type*} [Group X] (x : X) (hx : x ^ 8 = 1) :
    Multiplicative (ZMod 8) →* X where
  toFun k := x ^ (Multiplicative.toAdd k).val
  map_one' := by simp
  map_mul' a b := by
    change x ^ (Multiplicative.toAdd a + Multiplicative.toAdd b).val =
      x ^ (Multiplicative.toAdd a).val * x ^ (Multiplicative.toAdd b).val
    rw [ZMod.val_add, pow_mod_eight' hx, pow_add]

private theorem coordHom8_apply {X : Type*} [Group X] (x : X) (hx : x ^ 8 = 1) (k : ZMod 8) :
    coordHom8 x hx (Multiplicative.ofAdd k) = x ^ k.val := rfl

end Q16

section Structure

variable {D : Type} [Group D] [Finite D] {Q : Subgroup D} [Q.Normal] {z : D}

omit [Finite D] in
private theorem q8_card_D (hz : Q8Data Q z) (hC : ∀ d : D, (∀ q ∈ Q, d * q = q * d) → d ∈ Q)
    (h3 : 3 ∣ Nat.card D) : Nat.card D = 24 ∨ Nat.card D = 48 := by
  let ρ : D →* MulAut ↥Q := MulAut.conjNormal
  have hρ : ∀ (d : D) (q : ↥Q), ((ρ d q : ↥Q) : D) = d * q * d⁻¹ := fun d q =>
    MulAut.conjNormal_apply d q
  have hker : ∀ d : D, d ∈ ρ.ker ↔ (d = 1 ∨ d = z) := by
    intro d
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have hcomm : ∀ q ∈ Q, d * q = q * d := by
        intro q hq
        have h1 : d * q * d⁻¹ = q := by
          have := congrArg (fun f : MulAut ↥Q => ((f ⟨q, hq⟩ : ↥Q) : D)) h
          simpa [hρ] using this
        calc d * q = d * q * d⁻¹ * d := by group
          _ = q * d := by rw [h1]
      exact (hz.center d (hC d hcomm)).1 hcomm
    · intro h
      have hdQ : d ∈ Q := by
        rcases h with h | h
        · rw [h]; exact Q.one_mem
        · rw [h]; exact hz.zmem
      have hcomm := (hz.center d hdQ).2 h
      refine MulEquiv.ext fun q => Subtype.ext ?_
      rw [hρ, MulAut.one_apply]
      exact mul_inv_eq_iff_eq_mul.2 (hcomm q q.2)
  have hkerc : Nat.card ρ.ker = 2 := by
    rw [Nat.card_eq_two_iff' (⟨1, ρ.ker.one_mem⟩ : ρ.ker)]
    refine ⟨⟨z, (hker z).2 (Or.inr rfl)⟩, fun h => hz.zne (congrArg Subtype.val h), fun y hy => ?_⟩
    rcases (hker y.1).1 y.2 with h | h
    · exact absurd (Subtype.ext h) hy
    · exact Subtype.ext h
  have h1 := ρ.ker.card_mul_index
  rw [Subgroup.index_ker, hkerc] at h1
  have h2 : Nat.card ρ.range ∣ 24 := hz.aut ▸ Subgroup.card_subgroup_dvd_card ρ.range
  have h8 : 8 ∣ Nat.card D := hz.card ▸ Subgroup.card_subgroup_dvd_card Q
  have h24 : 24 ∣ Nat.card D :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 3) h8 h3
  obtain ⟨r, hr⟩ : ∃ r, r = Nat.card ρ.range := ⟨_, rfl⟩
  rw [← hr] at h1 h2
  have hr24 : r ≤ 24 := Nat.le_of_dvd (by norm_num) h2
  rw [← h1] at h24 ⊢
  interval_cases r <;> omega

private theorem q8_case48 (hz : Q8Data Q z) (hC : ∀ d : D, (∀ q ∈ Q, d * q = q * d) → d ∈ Q)
    {P : Subgroup D} (hQP : Q ≤ P) (hP : Nat.card P = 16) :
    Nonempty (↥P ≃* QuaternionGroup 4) ∨ Nonempty (↥P ≃* CFSG.Open.SemidihedralGroup 4) := by
  have hidx : (Q.subgroupOf P).index = 2 := by
    have h1 := (Q.subgroupOf P).card_mul_index
    have h2 : Nat.card (Q.subgroupOf P) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv
    rw [h2, hz.card, hP] at h1
    omega
  have hsqQ : ∀ s ∈ P, s * s ∈ Q := fun s hs =>
    Subgroup.mul_self_mem_of_index_two hidx (⟨s, hs⟩ : ↥P)
  have hex : ∃ s ∈ P, s ∉ Q := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (show P ≤ Q from hcon)
    rw [hP, hz.card] at h1
    omega
  have hZcomm : ∀ u : D, (u = 1 ∨ u = z) → ∀ q ∈ Q, u * q = q * u := by
    intro u hu q hq
    have huQ : u ∈ Q := by
      rcases hu with h | h
      · rw [h]; exact Q.one_mem
      · rw [h]; exact hz.zmem
    exact (hz.center u huQ).2 hu q hq
  have hZinv : ∀ u : D, (u = 1 ∨ u = z) → (u⁻¹ = 1 ∨ u⁻¹ = z) := by
    intro u hu
    rcases hu with h | h
    · left; rw [h, inv_one]
    · right; rw [h]; exact inv_eq_of_mul_eq_one_right hz.zsq
  have hZmul : ∀ u v : D, (u = 1 ∨ u = z) → (v = 1 ∨ v = z) → (u * v = 1 ∨ u * v = z) := by
    intro u v hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact Or.inl (mul_one 1)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl hz.zsq
  obtain ⟨s, hsP, hsQ, hs1, hsz⟩ : ∃ s ∈ P, s ∉ Q ∧ s * s ≠ 1 ∧ s * s ≠ z := by
    by_contra hcon
    have hall : ∀ s ∈ P, s ∉ Q → (s * s = 1 ∨ s * s = z) := by
      intro s hs hsQ
      by_contra hne
      push Not at hne
      exact hcon ⟨s, hs, hsQ, hne.1, hne.2⟩
    obtain ⟨s0, hs0, hs0Q⟩ := hex
    let σ : MulAut ↥Q := MulAut.conjNormal s0
    have hσ : ∀ q : ↥Q, ((σ q : ↥Q) : D) = s0 * q * s0⁻¹ := fun q =>
      MulAut.conjNormal_apply s0 q
    have hinner : ∀ q : ↥Q, ((σ q * q : ↥Q) : D) = 1 ∨ ((σ q * q : ↥Q) : D) = z := by
      intro q
      have hqP : (q : D) ∈ P := hQP q.2
      have hs0q : s0 * q ∉ Q := fun h => hs0Q (by
        have := Q.mul_mem h (Q.inv_mem q.2)
        simpa using this)
      have hA := hall (s0 * q) (P.mul_mem hs0 hqP) hs0q
      have hB := hall s0 hs0 hs0Q
      have hv := hZinv _ hB
      have hcv : (s0 * s0)⁻¹ * q = q * (s0 * s0)⁻¹ := hZcomm _ hv q q.2
      have e1 : ((σ q * q : ↥Q) : D) = (s0 * q * (s0 * q)) * (s0 * s0)⁻¹ := by
        rw [Subgroup.coe_mul, hσ]
        calc s0 * q * s0⁻¹ * q = s0 * q * s0 * ((s0 * s0)⁻¹ * q) := by group
          _ = s0 * q * s0 * (q * (s0 * s0)⁻¹) := by rw [hcv]
          _ = (s0 * q * (s0 * q)) * (s0 * s0)⁻¹ := by group
      rw [e1]
      exact hZmul _ _ hA hv
    obtain ⟨q0, hq0⟩ := hz.inner σ hinner
    have hcent : ∀ q ∈ Q, ((q0 : D)⁻¹ * s0) * q = q * ((q0 : D)⁻¹ * s0) := by
      intro q hq
      have h1 := congrArg Subtype.val (hq0 ⟨q, hq⟩)
      rw [hσ] at h1
      have h1' : s0 * q * s0⁻¹ = (q0 : D) * q * ((q0 : D)⁻¹) := by simpa using h1
      calc ((q0 : D)⁻¹ * s0) * q = (q0 : D)⁻¹ * (s0 * q * s0⁻¹) * s0 := by group
        _ = (q0 : D)⁻¹ * ((q0 : D) * q * ((q0 : D)⁻¹)) * s0 := by rw [h1']
        _ = q * ((q0 : D)⁻¹ * s0) := by group
    have hmem := hC _ hcent
    apply hs0Q
    have := Q.mul_mem q0.2 hmem
    simpa using this
  have hu : s * s ∈ Q := hsqQ s hsP
  have hu2 : (s * s) * (s * s) = z := hz.sq _ hu hs1 hsz
  have hs4 : s ^ 4 = z := by
    rw [← hu2]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hs8 : s ^ 8 = 1 := by
    calc s ^ 8 = s ^ 4 * s ^ 4 := by group
      _ = 1 := by rw [hs4]; exact hz.zsq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have horder : orderOf s = 8 := by
    have h1 : ¬ s ^ 2 ^ 2 = 1 := by
      intro h
      apply hz.zne
      rw [← hs4]
      simpa using h
    have h2 : s ^ 2 ^ (2 + 1) = 1 := by simpa using hs8
    simpa using orderOf_eq_prime_pow h1 h2
  have hsne : ∀ i : ℕ, 0 < i → i < 8 → s ^ i ≠ 1 := fun i hi0 hi8 h => by
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [horder] at h1
    have := Nat.le_of_dvd hi0 h1
    omega
  obtain ⟨y, hyQ, hy1, hyz, hyu, hyu'⟩ := hz.exists_out (s * s) hu hs1 hsz
  have hyy : y * y = z := hz.sq y hyQ hy1 hyz
  have hyuc : y * (s * s) * y⁻¹ = (s * s)⁻¹ := by
    rcases hz.inv (s * s) hu y hyQ with h | h
    · exfalso
      rcases h with h | h | h | h | h | h
      · exact hs1 h
      · exact hsz h
      · exact hy1 h
      · exact hyz h
      · exact hyu h
      · exact hyu' h
    · exact h
  have hyP : y ∈ P := hQP hyQ
  have hy_not : y ∉ Subgroup.zpowers s := by
    intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hcomm : y * s = s * y := by
      rw [← hk]
      exact ((Commute.refl s).zpow_left k).eq
    have hys : y * s * y⁻¹ = s := mul_inv_eq_iff_eq_mul.2 hcomm
    have h1 : y * (s * s) * y⁻¹ = s * s := by
      calc y * (s * s) * y⁻¹ = (y * s * y⁻¹) * (y * s * y⁻¹) := by group
        _ = s * s := by rw [hys]
    rw [h1] at hyuc
    have h2 : (s * s) * (s * s) = 1 := by
      calc (s * s) * (s * s) = (s * s) * (s * s)⁻¹ := by rw [← hyuc]
        _ = 1 := mul_inv_cancel _
    exact hz.zne (by rw [← hu2]; exact h2)
  have hle : Subgroup.zpowers s ≤ P := (Subgroup.zpowers_le).2 hsP
  have hidx2 : ((Subgroup.zpowers s).subgroupOf P).index = 2 := by
    have h1 := ((Subgroup.zpowers s).subgroupOf P).card_mul_index
    have h2 : Nat.card ((Subgroup.zpowers s).subgroupOf P) = Nat.card (Subgroup.zpowers s) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [h2, Nat.card_zpowers, horder, hP] at h1
    omega
  have hnorm : ((Subgroup.zpowers s).subgroupOf P).Normal := Subgroup.normal_of_index_eq_two hidx2
  have ht : y * s * y⁻¹ ∈ Subgroup.zpowers s := by
    have := hnorm.conj_mem ⟨s, hsP⟩ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers s)) ⟨y, hyP⟩
    exact Subgroup.mem_subgroupOf.1 this
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ht
  have htt : (y * s * y⁻¹) * (y * s * y⁻¹) = (s * s)⁻¹ := by
    calc (y * s * y⁻¹) * (y * s * y⁻¹) = y * (s * s) * y⁻¹ := by group
      _ = (s * s)⁻¹ := hyuc
  have h2k : s ^ (2 * k + 2) = 1 := by
    calc s ^ (2 * k + 2) = (s ^ k * s ^ k) * (s * s) := by
          rw [zpow_add, two_mul, zpow_add, zpow_two]
      _ = ((y * s * y⁻¹) * (y * s * y⁻¹)) * (s * s) := by rw [hk]
      _ = 1 := by rw [htt]; exact inv_mul_cancel _
  have h8k : (8 : ℤ) ∣ 2 * k + 2 := by
    have := orderOf_dvd_iff_zpow_eq_one.2 h2k
    rw [horder] at this
    exact_mod_cast this
  have hkmod : k % 8 = 3 ∨ k % 8 = 7 := by omega
  have hkpow : s ^ (k % 8) = s ^ k := by
    have := zpow_mod_orderOf s k
    rw [horder] at this
    simpa using this
  rcases hkmod with h3 | h7
  ·
    have ht3 : y * s * y⁻¹ = s ^ 3 := by
      rw [← hk, ← hkpow, h3]
      norm_num
    right
    have h2 : (y * s) ^ 2 = 1 := by
      have e : (y * s) ^ 2 = (y * s * y⁻¹) * (y * y) * s := by
        rw [pow_two]
        group
      rw [e, ht3, hyy, ← hs4]
      calc s ^ 3 * s ^ 4 * s = s ^ 8 := by group
        _ = 1 := hs8
    have hc : (y * s) * s * (y * s)⁻¹ = s ^ 3 := by
      rw [← ht3]
      group
    have hne : ∀ (i : Fin 8) (e : Fin 2), s ^ (i : ℕ) * (y * s) ^ (e : ℕ) = 1 → i = 0 ∧ e = 0 := by
      intro i e h
      have he2 := e.2
      have he : (e : ℕ) = 0 ∨ (e : ℕ) = 1 := by omega
      rcases he with he | he
      · rw [he, pow_zero, mul_one] at h
        have hi : (i : ℕ) = 0 := by
          by_contra hne'
          exact hsne i (Nat.pos_of_ne_zero hne') i.2 h
        exact ⟨Fin.ext hi, Fin.ext he⟩
      · exfalso
        rw [he, pow_one] at h
        apply hy_not
        have hyeq : y = (s ^ (i : ℕ))⁻¹ * s⁻¹ := by
          calc y = (s ^ (i : ℕ))⁻¹ * (s ^ (i : ℕ) * (y * s)) * s⁻¹ := by group
            _ = (s ^ (i : ℕ))⁻¹ * s⁻¹ := by rw [h]; group
        rw [hyeq]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers s _))
          (Subgroup.inv_mem _ (Subgroup.mem_zpowers s))
    exact CFSG.RankThree.Asc83Table.nonempty_mulEquiv_semidihedral (by simp [hP]) hsP
      (P.mul_mem hyP hsP) hs8 h2 hc hne
  ·
    have ht7 : y * s * y⁻¹ = s ^ 7 := by
      rw [← hk, ← hkpow, h7]
      norm_num
    left
    have hsinv : y * s * y⁻¹ = s⁻¹ := by
      rw [ht7]
      exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hs8)
    have hconj : ∀ n : ℕ, y * s ^ n * y⁻¹ = (s ^ n)⁻¹ := by
      intro n
      rw [← conj_pow, hsinv, inv_pow]
    have hS8 : (⟨s, hsP⟩ : ↥P) ^ 8 = 1 := Subtype.ext (by simpa using hs8)
    have hinj : Function.Injective (coordHom8 (⟨s, hsP⟩ : ↥P) hS8) := by
      rw [injective_iff_map_eq_one]
      intro k hk
      have hk' : (⟨s, hsP⟩ : ↥P) ^ (Multiplicative.toAdd k).val = 1 := hk
      have hk'' : s ^ (Multiplicative.toAdd k).val = 1 := by
        simpa using congrArg Subtype.val hk'
      have hlt := ZMod.val_lt (Multiplicative.toAdd k)
      have h0 : (Multiplicative.toAdd k).val = 0 := by
        by_contra hne'
        exact hsne _ (Nat.pos_of_ne_zero hne') hlt hk''
      exact toAdd_eq_zero.1 ((ZMod.val_eq_zero _).1 h0)
    have hrange : Nat.card (coordHom8 (⟨s, hsP⟩ : ↥P) hS8).range = 8 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
      simp
    have hindex : (coordHom8 (⟨s, hsP⟩ : ↥P) hS8).range.index = 2 := by
      have h1 := (coordHom8 (⟨s, hsP⟩ : ↥P) hS8).range.card_mul_index
      rw [hrange, hP] at h1
      omega
    have hout : (⟨y, hyP⟩ : ↥P) ∉ (coordHom8 (⟨s, hsP⟩ : ↥P) hS8).range := by
      rintro ⟨k, hk⟩
      apply hy_not
      have hk0 : (⟨s, hsP⟩ : ↥P) ^ (Multiplicative.toAdd k).val = ⟨y, hyP⟩ := hk
      have hk' : s ^ (Multiplicative.toAdd k).val = y := by
        simpa using congrArg Subtype.val hk0
      rw [← hk']
      exact Subgroup.npow_mem_zpowers s _
    have hsq : (⟨y, hyP⟩ : ↥P) ^ 2 =
        coordHom8 (⟨s, hsP⟩ : ↥P) hS8 (Multiplicative.ofAdd ((4 : ℕ) : ZMod 8)) := by
      apply Subtype.ext
      have h4 : ((4 : ℕ) : ZMod 8).val = 4 := by decide
      simp only [coordHom8_apply, h4, Subgroup.coe_pow]
      rw [hs4, pow_two, hyy]
    have hinvc : ∀ k : Multiplicative (ZMod 8), (⟨y, hyP⟩ : ↥P) *
        coordHom8 (⟨s, hsP⟩ : ↥P) hS8 k * (⟨y, hyP⟩ : ↥P)⁻¹ =
          (coordHom8 (⟨s, hsP⟩ : ↥P) hS8 k)⁻¹ := by
      intro k
      apply Subtype.ext
      exact hconj _
    exact ⟨(CFSG.DisconnectedInvolutionGraph.Helpers.quaternionCoordinateEquiv 4
      (coordHom8 (⟨s, hsP⟩ : ↥P) hS8) ⟨y, hyP⟩ hsq hinvc hinj hindex hout).symm⟩

end Structure

theorem sylow_two_of_Dt
    {D : Type} [Group D] [Finite D] (Q : Subgroup D) [Q.Normal]
    (hQ : Nonempty (↥Q ≃* QuaternionGroup 2)) (hC : ∀ d : D, (∀ q ∈ Q, d * q = q * d) → d ∈ Q)
    (h3 : 3 ∣ Nat.card D) (P : Sylow 2 D) :
    (Nat.card D = 24 ∧ (P : Subgroup D) = Q) ∨
    (Nat.card D = 48 ∧ Nonempty (↥(P : Subgroup D) ≃* QuaternionGroup 4)) ∨
    (Nat.card D = 48 ∧ Nonempty (↥(P : Subgroup D) ≃* CFSG.Open.SemidihedralGroup 4)) := by
  obtain ⟨e⟩ := hQ
  have hz := q8Data Q e
  have hQP : Q ≤ (P : Subgroup D) :=
    (IsPGroup.of_card (n := 3) (hz.card.trans (by norm_num))).le_sylow_of_normal P
  have hPcard : Nat.card (P : Subgroup D) = 2 ^ (Nat.card D).factorization 2 :=
    P.card_eq_multiplicity
  rcases q8_card_D hz hC h3 with h24 | h48
  · left
    refine ⟨h24, ?_⟩
    have hfac : (Nat.card D).factorization 2 = 3 := by
      rw [h24, show (24 : ℕ) = 2 ^ 3 * 3 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization Nat.prime_three]
      simp
    have hP8 : Nat.card (P : Subgroup D) = 8 := by
      rw [hPcard, hfac]
      norm_num
    exact (Subgroup.eq_of_le_of_card_ge hQP (by rw [hP8, hz.card])).symm
  · right
    have hfac : (Nat.card D).factorization 2 = 4 := by
      rw [h48, show (48 : ℕ) = 2 ^ 4 * 3 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization Nat.prime_three]
      simp
    have hP16 : Nat.card (P : Subgroup D) = 16 := by
      rw [hPcard, hfac]
      norm_num
    rcases q8_case48 hz hC hQP hP16 with h | h
    · exact Or.inl ⟨h48, h⟩
    · exact Or.inr ⟨h48, h⟩

end CFSG.GH74.E2
