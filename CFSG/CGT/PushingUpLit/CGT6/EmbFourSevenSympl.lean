module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open scoped commutatorElement

variable {A : Type*} [Group A]

theorem exists_two_le_card_eq_pow_of_not_isCyclic [Finite A] {p : ℕ} (hp : p.Prime)
    (hA : IsPGroup p A) (hnc : ¬ IsCyclic A) : ∃ j : ℕ, 2 ≤ j ∧ Nat.card A = p ^ j := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hA
  refine ⟨n, ?_, hn⟩
  by_contra h
  have hn1 : n = 0 ∨ n = 1 := by omega
  apply hnc
  rcases hn1 with rfl | rfl
  · have h1 : Nat.card A = 1 := by simpa using hn
    have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp h1).1
    infer_instance
  · exact isCyclic_of_prime_card (p := p) (by simpa using hn)

@[expose] def fixedSubgroup (σ : A ≃* A) : Subgroup A where
  carrier := {a | σ a = a}
  one_mem' := map_one σ
  mul_mem' := fun {a b} ha hb => by
    have ha' : σ a = a := ha
    have hb' : σ b = b := hb
    show σ (a * b) = a * b
    rw [map_mul, ha', hb']
  inv_mem' := fun {a} ha => by
    have ha' : σ a = a := ha
    show σ a⁻¹ = a⁻¹
    rw [map_inv, ha']

theorem mem_fixedSubgroup {σ : A ≃* A} {a : A} : a ∈ fixedSubgroup σ ↔ σ a = a := Iff.rfl

theorem card_fixedSubgroup (σ : A ≃* A) :
    Nat.card (fixedSubgroup σ) = Nat.card {a : A // σ a = a} :=
  rfl

theorem fixedSubgroup_ne_top {σ : A ≃* A} (hne : ∃ a, σ a ≠ a) : fixedSubgroup σ ≠ ⊤ := by
  obtain ⟨a, ha⟩ := hne
  intro h
  exact ha ((mem_fixedSubgroup).mp (h ▸ Subgroup.mem_top a))

theorem card_fixed_mul_le_of_isPGroup [Finite A] {p : ℕ} (hp : p.Prime) (hA : IsPGroup p A)
    (σ : A ≃* A) (hne : ∃ a, σ a ≠ a) : Nat.card {a : A // σ a = a} * p ≤ Nat.card A := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← card_fixedSubgroup]
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hA
  have hidx : (fixedSubgroup σ).index ∣ p ^ n := by
    rw [← hn]
    exact Subgroup.index_dvd_card _
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp hidx
  have hne1 : (fixedSubgroup σ).index ≠ 1 := fun h =>
    fixedSubgroup_ne_top hne (Subgroup.index_eq_one.mp h)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne1 (by simpa using hk')
  have hpidx : p ≤ (fixedSubgroup σ).index := by
    rw [hk']
    exact Nat.le_self_pow hk0 p
  calc Nat.card (fixedSubgroup σ) * p ≤ Nat.card (fixedSubgroup σ) * (fixedSubgroup σ).index :=
        Nat.mul_le_mul_left _ hpidx
    _ = Nat.card A := by rw [mul_comm]; exact (fixedSubgroup σ).index_mul_card

theorem card_fixed_mul_81_le_of_isPGroup [Finite A] (hA : IsPGroup 3 A) (σ : A ≃* A)
    (h5 : ∀ a, σ (σ (σ (σ (σ a)))) = a) (hne : ∃ a, σ a ≠ a) :
    Nat.card {a : A // σ a = a} * 81 ≤ Nat.card A := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h5p : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let g : MulAut A := σ
  have hg5 : g ^ 5 = 1 := by
    ext a
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply]
    exact h5 a
  have hcard : Nat.card (Subgroup.zpowers g) ∣ 5 ^ 1 := by
    rw [Nat.card_zpowers]
    simpa using orderOf_dvd_of_pow_eq_one hg5
  have hP5 : IsPGroup 5 (Subgroup.zpowers g) := IsPGroup.of_card_dvd_pow hcard
  have hmod := hP5.card_modEq_card_fixedPoints (α := A)
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers g) A) =
      Nat.card {a : A // σ a = a} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
    constructor
    · intro ha
      exact ha ⟨g, Subgroup.mem_zpowers g⟩
    · intro ha h
      have hg : g ∈ MulAction.stabilizer (MulAut A) a := ha
      have hle : Subgroup.zpowers g ≤ MulAction.stabilizer (MulAut A) a :=
        (Subgroup.zpowers_le).mpr hg
      exact hle h.2
  rw [hfix] at hmod
  have hC := hA.to_subgroup (fixedSubgroup σ)
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hA
  obtain ⟨c, hc⟩ := (IsPGroup.iff_card).mp hC
  have hlt : Nat.card (fixedSubgroup σ) < Nat.card A := by
    refine lt_of_le_of_ne (Subgroup.card_le_card_group _) fun heq => ?_
    exact fixedSubgroup_ne_top hne (Subgroup.eq_top_of_card_eq _ heq)
  rw [card_fixedSubgroup] at hc hlt
  rw [hm, hc] at hmod
  rw [hm, hc] at hlt ⊢
  have hcm : c < m := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  obtain ⟨d, rfl⟩ : ∃ d, m = c + d := ⟨m - c, by omega⟩
  have hd1 : 1 ≤ d := by omega
  have hd : 3 ^ d ≡ 1 [MOD 5] := by
    have h1 : 3 ^ c * 3 ^ d ≡ 3 ^ c * 1 [MOD 5] := by
      simpa [pow_add] using hmod
    exact Nat.ModEq.cancel_left_of_coprime (by
      have : Nat.Coprime 5 (3 ^ c) := Nat.Coprime.pow_right _ (by norm_num)
      exact this) h1
  have hd4 : 4 ≤ d := by
    by_contra h
    have : d = 1 ∨ d = 2 ∨ d = 3 := by omega
    rcases this with rfl | rfl | rfl <;> simp [Nat.ModEq] at hd
  calc 3 ^ c * 81 = 3 ^ c * 3 ^ 4 := by norm_num
    _ ≤ 3 ^ c * 3 ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hd4)
    _ = 3 ^ (c + d) := by rw [pow_add]

section Pairing

variable {B : Type*} [Group B]

theorem pairing_skew {c : A → A → B} (hc₁ : ∀ a a' b, c (a * a') b = c a b * c a' b)
    (hc₂ : ∀ a b b', c a (b * b') = c a b * c a b') (halt : ∀ a, c a a = 1) (a b : A) :
    c a b * c b a = 1 := by
  have h : c (a * b) (a * b) = (c a a * c a b) * (c b a * c b b) := by
    rw [hc₁, hc₂, hc₂]
  rw [halt, halt, halt] at h
  simpa using h.symm

theorem card_fixed_mul_sq_le_of_isPGroup [Finite A] {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5)
    (hA : IsPGroup p A) (hcomm : ∀ a b : A, a * b = b * a) (σ : A ≃* A)
    (h5 : ∀ a, σ (σ (σ (σ (σ a)))) = a) (hne : ∃ a, σ a ≠ a) (c : A → A → B)
    (hc₁ : ∀ a a' b, c (a * a') b = c a b * c a' b)
    (hc₂ : ∀ a b b', c a (b * b') = c a b * c a b') (halt : ∀ a, c a a = 1)
    (hnd : ∀ a, (∀ b, c a b = 1) → a = 1) (hinv : ∀ a b, c (σ a) (σ b) = c a b) :
    Nat.card {a : A // σ a = a} * p ^ 2 ≤ Nat.card A := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let _ : CommGroup A := { ‹Group A› with mul_comm := hcomm }
  let φ : A →* A := MonoidHom.mk' (fun a => a⁻¹ * σ a) (fun a b => by
    simp only [mul_inv, map_mul]
    exact mul_mul_mul_comm _ _ _ _)
  have hφ : ∀ a, φ a = a⁻¹ * σ a := fun a => rfl
  have hker : φ.ker = fixedSubgroup σ := by
    ext a
    simp only [MonoidHom.mem_ker, mem_fixedSubgroup, hφ]
    rw [inv_mul_eq_one, eq_comm]
  have hquot : Nat.card (A ⧸ fixedSubgroup σ) = Nat.card φ.range := by
    rw [← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hcardA : Nat.card A = Nat.card φ.range * Nat.card (fixedSubgroup σ) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (fixedSubgroup σ), hquot]
  obtain ⟨i, hi⟩ := (IsPGroup.iff_card).mp (hA.to_subgroup φ.range)
  have hDne : φ.range ≠ ⊥ := by
    obtain ⟨a, ha⟩ := hne
    intro h
    have : φ a ∈ φ.range := ⟨a, rfl⟩
    rw [h, Subgroup.mem_bot, hφ, inv_mul_eq_one, eq_comm] at this
    exact ha this
  have hi1 : 1 ≤ i := by
    by_contra h
    have h0 : i = 0 := by omega
    rw [h0, pow_zero] at hi
    exact hDne (Subgroup.eq_bot_of_card_eq _ hi)
  by_contra hcon
  have hCpos : 0 < Nat.card (fixedSubgroup σ) := Nat.card_pos
  have hlt : p ^ i < p ^ 2 := by
    have h1 : Nat.card A < Nat.card (fixedSubgroup σ) * p ^ 2 := not_le.mp hcon
    rw [hcardA, hi, mul_comm] at h1
    exact Nat.lt_of_mul_lt_mul_left h1
  have hi2 : i = 1 := by
    have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
    omega
  have hDcard : Nat.card φ.range = p := by rw [hi, hi2, pow_one]
  let N : A →* A := MonoidHom.mk'
    (fun a => a * σ a * σ (σ a) * σ (σ (σ a)) * σ (σ (σ (σ a)))) (fun a b => by
      simp only [map_mul]
      ac_rfl)
  have hNφ : ∀ a, N (φ a) = 1 := fun a => by
    show φ a * σ (φ a) * σ (σ (φ a)) * σ (σ (σ (φ a))) * σ (σ (σ (σ (φ a)))) = 1
    simp only [hφ, map_mul, map_inv, h5]
    group
  have hNfix : ∀ z, σ z = z → N z = z ^ 5 := fun z hz => by
    show z * σ z * σ (σ z) * σ (σ (σ z)) * σ (σ (σ (σ z))) = z ^ 5
    simp only [hz]
    rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_one]
  have hCD : fixedSubgroup σ ⊓ φ.range = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro z ⟨hzC, a, rfl⟩
    have hz5 : (φ a) ^ 5 = 1 := (hNfix _ hzC).symm.trans (hNφ a)
    obtain ⟨k, hk⟩ := hA (φ a)
    have hd1 : orderOf (φ a) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
    have hd2 : orderOf (φ a) ∣ 5 := orderOf_dvd_of_pow_eq_one hz5
    have hcop : Nat.Coprime (p ^ k) 5 :=
      Nat.Coprime.pow_left _ ((Nat.coprime_primes hp Nat.prime_five).mpr hp5)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  let f : φ.range →* A ⧸ fixedSubgroup σ :=
    (QuotientGroup.mk' (fixedSubgroup σ)).comp φ.range.subtype
  have hfinj : Function.Injective f := by
    intro d₁ d₂ h
    have h' : (d₁ : A)⁻¹ * (d₂ : A) ∈ fixedSubgroup σ := QuotientGroup.eq.mp h
    have h'' : (d₁ : A)⁻¹ * (d₂ : A) ∈ φ.range := mul_mem (inv_mem d₁.2) d₂.2
    have h3 : (d₁ : A)⁻¹ * (d₂ : A) ∈ fixedSubgroup σ ⊓ φ.range := ⟨h', h''⟩
    rw [hCD, Subgroup.mem_bot, inv_mul_eq_one] at h3
    exact Subtype.ext h3
  have hfbij : Function.Bijective f := hfinj.bijective_of_nat_card_le (le_of_eq hquot)
  have hsplit : ∀ a : A, ∃ d ∈ φ.range, ∃ u ∈ fixedSubgroup σ, a = d * u := fun a => by
    obtain ⟨d, hd⟩ := hfbij.2 (QuotientGroup.mk a)
    have : (d : A)⁻¹ * a ∈ fixedSubgroup σ := QuotientGroup.eq.mp hd
    exact ⟨d, d.2, _, this, by simp⟩
  obtain ⟨d₀, hd₀⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hDne
  obtain ⟨a₀, ha₀⟩ := d₀.2
  have : Fact (Nat.card φ.range).Prime := ⟨hDcard ▸ hp⟩
  have hgen : Subgroup.zpowers d₀ = ⊤ := zpowers_eq_top_of_prime_card hDcard hd₀
  let ψ : A →* B := MonoidHom.mk' (fun a => c a (d₀ : A)) (fun a a' => hc₁ a a' _)
  have hψC : ∀ u ∈ fixedSubgroup σ, ψ u = 1 := fun u hu => by
    let ρ : A →* B := MonoidHom.mk' (c u) (hc₂ u)
    have hσu : σ u = u := hu
    show c u (d₀ : A) = 1
    rw [← ha₀, hφ]
    have h1 : c u (a₀⁻¹ * σ a₀) = ρ a₀⁻¹ * ρ (σ a₀) := hc₂ u _ _
    have h2 : ρ (σ a₀) = ρ a₀ := by
      show c u (σ a₀) = c u a₀
      rw [← hinv u a₀, hσu]
    rw [h1, h2, map_inv, inv_mul_cancel]
  have hψD : ∀ e ∈ φ.range, ψ e = 1 := fun e he => by
    have hmem : (⟨e, he⟩ : φ.range) ∈ Subgroup.zpowers d₀ := by rw [hgen]; exact Subgroup.mem_top _
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have : e = (d₀ : A) ^ n := by
      have := congrArg Subtype.val hn.symm
      simpa using this
    rw [this, map_zpow]
    have : ψ (d₀ : A) = 1 := halt _
    rw [this, one_zpow]
  have hall : ∀ a, c a (d₀ : A) = 1 := fun a => by
    obtain ⟨d, hd, u, hu, rfl⟩ := hsplit a
    have : ψ (d * u) = 1 := by rw [map_mul, hψD d hd, hψC u hu, one_mul]
    exact this
  have hrad : ∀ b, c (d₀ : A) b = 1 := fun b => by
    have h1 := pairing_skew hc₁ hc₂ halt (d₀ : A) b
    rw [hall b, mul_one] at h1
    exact h1
  exact hd₀ (Subtype.ext (hnd _ hrad))

end Pairing

section CenterPairing

variable {Γ : Type*} [Group Γ]

theorem comm_mul_left_of_central (hc : ∀ g h : Γ, ⁅g, h⁆ ∈ Subgroup.center Γ) (g g' h : Γ) :
    ⁅g * g', h⁆ = ⁅g, h⁆ * ⁅g', h⁆ := by
  have h1 : ⁅g * g', h⁆ = g * ⁅g', h⁆ * g⁻¹ * ⁅g, h⁆ := by
    simp only [commutatorElement_def]
    group
  have h2 : g * ⁅g', h⁆ * g⁻¹ = ⁅g', h⁆ := by
    have := Subgroup.mem_center_iff.mp (hc g' h) g
    rw [this]
    group
  have h3 : ⁅g', h⁆ * ⁅g, h⁆ = ⁅g, h⁆ * ⁅g', h⁆ :=
    (Subgroup.mem_center_iff.mp (hc g' h) ⁅g, h⁆).symm
  rw [h1, h2, h3]

theorem comm_mul_right_of_central (hc : ∀ g h : Γ, ⁅g, h⁆ ∈ Subgroup.center Γ) (g h h' : Γ) :
    ⁅g, h * h'⁆ = ⁅g, h⁆ * ⁅g, h'⁆ := by
  have h1 : ⁅g, h * h'⁆ = ⁅g, h⁆ * (h * ⁅g, h'⁆ * h⁻¹) := by
    simp only [commutatorElement_def]
    group
  have h2 : h * ⁅g, h'⁆ * h⁻¹ = ⁅g, h'⁆ := by
    have := Subgroup.mem_center_iff.mp (hc g h') h
    rw [this]
    group
  rw [h1, h2]

theorem comm_mul_central_left {z : Γ} (hz : z ∈ Subgroup.center Γ) (g h : Γ) :
    ⁅g * z, h⁆ = ⁅g, h⁆ := by
  have hzh : z * h * z⁻¹ = h := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.mp hz h).symm
  calc ⁅g * z, h⁆ = g * (z * h * z⁻¹) * g⁻¹ * h⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅g, h⁆ := by rw [hzh]; rfl

theorem comm_mul_central_right {w : Γ} (hw : w ∈ Subgroup.center Γ) (g h : Γ) :
    ⁅g, h * w⁆ = ⁅g, h⁆ := by
  have hwg : w * g⁻¹ * w⁻¹ = g⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.mp hw g⁻¹).symm
  calc ⁅g, h * w⁆ = g * h * (w * g⁻¹ * w⁻¹) * h⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅g, h⁆ := by rw [hwg]; rfl

@[expose] def centerPair : Γ ⧸ Subgroup.center Γ → Γ ⧸ Subgroup.center Γ → Γ :=
  fun a b => Quotient.liftOn₂' a b (fun g h => ⁅g, h⁆) (by
    intro g₁ h₁ g₂ h₂ hg hh
    have hg' : g₁⁻¹ * g₂ ∈ Subgroup.center Γ := QuotientGroup.leftRel_apply.mp hg
    have hh' : h₁⁻¹ * h₂ ∈ Subgroup.center Γ := QuotientGroup.leftRel_apply.mp hh
    have e1 : g₂ = g₁ * (g₁⁻¹ * g₂) := by group
    have e2 : h₂ = h₁ * (h₁⁻¹ * h₂) := by group
    rw [e1, e2, comm_mul_central_left hg', comm_mul_central_right hh'])

theorem centerPair_mk (g h : Γ) :
    centerPair (QuotientGroup.mk g) (QuotientGroup.mk h) = ⁅g, h⁆ := rfl

theorem centerPair_mul_left (hc : ∀ g h : Γ, ⁅g, h⁆ ∈ Subgroup.center Γ)
    (a a' b : Γ ⧸ Subgroup.center Γ) :
    centerPair (a * a') b = centerPair a b * centerPair a' b := by
  induction a using QuotientGroup.induction_on
  induction a' using QuotientGroup.induction_on
  induction b using QuotientGroup.induction_on
  rw [← QuotientGroup.mk_mul, centerPair_mk, centerPair_mk, centerPair_mk]
  exact comm_mul_left_of_central hc _ _ _

theorem centerPair_mul_right (hc : ∀ g h : Γ, ⁅g, h⁆ ∈ Subgroup.center Γ)
    (a b b' : Γ ⧸ Subgroup.center Γ) :
    centerPair a (b * b') = centerPair a b * centerPair a b' := by
  induction a using QuotientGroup.induction_on
  induction b using QuotientGroup.induction_on
  induction b' using QuotientGroup.induction_on
  rw [← QuotientGroup.mk_mul, centerPair_mk, centerPair_mk, centerPair_mk]
  exact comm_mul_right_of_central hc _ _ _

theorem centerPair_self (a : Γ ⧸ Subgroup.center Γ) : centerPair a a = 1 := by
  induction a using QuotientGroup.induction_on
  rw [centerPair_mk]
  exact commutatorElement_self _

theorem centerPair_nondegenerate (a : Γ ⧸ Subgroup.center Γ)
    (h : ∀ b, centerPair a b = 1) : a = 1 := by
  induction a using QuotientGroup.induction_on with
  | H g =>
    refine (QuotientGroup.eq_one_iff g).mpr (Subgroup.mem_center_iff.mpr fun k => ?_)
    have := h (QuotientGroup.mk k)
    rw [centerPair_mk] at this
    exact (commutatorElement_eq_one_iff_mul_comm.mp this).symm

theorem centerQuot_comm (hc : ∀ g h : Γ, ⁅g, h⁆ ∈ Subgroup.center Γ)
    (a b : Γ ⧸ Subgroup.center Γ) : a * b = b * a := by
  induction a using QuotientGroup.induction_on with
  | H g =>
    induction b using QuotientGroup.induction_on with
    | H h =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      convert hc h⁻¹ g⁻¹ using 1
      simp only [commutatorElement_def]
      group

theorem center_quot_bounds [Finite Γ] {p : ℕ} (hp : p.Prime) (hP : IsPGroup p Γ)
    (hc : ∀ g h : Γ, ⁅g, h⁆ ∈ Subgroup.center Γ) (hnab : ¬ ∀ a b : Γ, a * b = b * a)
    (σ : (Γ ⧸ Subgroup.center Γ) ≃* (Γ ⧸ Subgroup.center Γ))
    (h5 : ∀ a, σ (σ (σ (σ (σ a)))) = a) (hne : ∃ a, σ a ≠ a)
    (hinv : ∀ a b, centerPair (σ a) (σ b) = centerPair a b) :
    (∃ j : ℕ, 2 ≤ j ∧ Nat.card (Γ ⧸ Subgroup.center Γ) = p ^ j) ∧
      Nat.card {a // σ a = a} * p ≤ Nat.card (Γ ⧸ Subgroup.center Γ) ∧
      (p ≠ 5 → Nat.card {a // σ a = a} * p ^ 2 ≤ Nat.card (Γ ⧸ Subgroup.center Γ)) ∧
      (p = 3 → Nat.card {a // σ a = a} * 81 ≤ Nat.card (Γ ⧸ Subgroup.center Γ)) := by
  have hA : IsPGroup p (Γ ⧸ Subgroup.center Γ) := hP.to_quotient _
  have hnc : ¬ IsCyclic (Γ ⧸ Subgroup.center Γ) := fun hcyc => by
    have h := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center Γ)) (by rw [QuotientGroup.ker_mk'])
    exact hnab fun a b => h.is_comm.comm a b
  refine ⟨exists_two_le_card_eq_pow_of_not_isCyclic hp hA hnc,
    card_fixed_mul_le_of_isPGroup hp hA σ hne, fun hp5 => ?_, fun h3 => ?_⟩
  · exact card_fixed_mul_sq_le_of_isPGroup hp hp5 hA (centerQuot_comm hc) σ h5 hne centerPair
      (centerPair_mul_left hc) (centerPair_mul_right hc) centerPair_self
      centerPair_nondegenerate hinv
  · subst h3
    exact card_fixed_mul_81_le_of_isPGroup hA σ h5 hne

end CenterPairing

end CFSG.CGT.PushingUpLit.CGT6
