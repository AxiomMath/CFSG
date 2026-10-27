module

public import CFSG.Holt.H78.AltModelAut

public section

namespace CFSG.HardMathSupport.RichardWeiss.Coordinator

open Equiv Equiv.Perm

section Uniqueness

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem eq_one_of_commute_alternatingGroup (h5 : 5 ≤ Fintype.card Ω) {σ : Perm Ω}
    (h : ∀ a ∈ alternatingGroup Ω, σ * a = a * σ) : σ = 1 := by
  by_contra hne
  have h5' : 5 ≤ Nat.card Ω := by rwa [Nat.card_eq_fintype_card]
  let N : Subgroup (Perm Ω) := Subgroup.centralizer (alternatingGroup Ω : Set (Perm Ω))
  have hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hn ⊢
    intro a ha
    have ha' : g⁻¹ * a * g ∈ alternatingGroup Ω := by
      have := (inferInstance : (alternatingGroup Ω).Normal).conj_mem a ha g⁻¹
      simpa using this
    have := hn _ ha'
    calc a * (g * n * g⁻¹) = g * ((g⁻¹ * a * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * a * g)) * g⁻¹ := by rw [this]
      _ = g * n * g⁻¹ * a := by group
  have hnt : Nontrivial N :=
    ⟨⟨⟨σ, fun a ha => (h a ha).symm⟩, 1, fun hh => hne (congrArg Subtype.val hh)⟩⟩
  have hle := Equiv.Perm.alternatingGroup_le_of_normal h5' hnt
  have hc : Subgroup.center ↥(alternatingGroup Ω) = ⊤ :=
    eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hle x.2)) g g.2)
  rw [alternatingGroup.center_eq_bot (by omega)] at hc
  have : Nontrivial ↥(alternatingGroup Ω) := alternatingGroup.nontrivial_of_three_le_card (by omega)
  exact (bot_ne_top : (⊥ : Subgroup ↥(alternatingGroup Ω)) ≠ ⊤) hc

end Uniqueness

section Action

variable {Q : Type*} [Group Q] {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] def ConjSpec {C : Subgroup Q} (φ : ↥C ≃* ↥(alternatingGroup Ω)) (u : Q) (σ : Perm Ω) : Prop :=
  ∀ c c' : ↥C, (c' : Q) = u * c * u⁻¹ →
    ((φ c' : ↥(alternatingGroup Ω)) : Perm Ω) = σ * ((φ c : ↥(alternatingGroup Ω)) : Perm Ω) * σ⁻¹

@[expose] noncomputable def conjOnSub (C : Subgroup Q) {u : Q} (hu : u ∈ Subgroup.normalizer (C : Set Q)) :
    ↥C ≃* ↥C :=
  ((MulAut.conj u).subgroupMap C).trans
    (MulEquiv.subgroupCongr (Subgroup.mem_normalizer_iff_map_conj_eq.mp hu))

theorem coe_conjOnSub (C : Subgroup Q) {u : Q} (hu : u ∈ Subgroup.normalizer (C : Set Q))
    (c : ↥C) : ((conjOnSub C hu c : ↥C) : Q) = u * c * u⁻¹ := rfl

theorem exists_perm_conj_of_mem_normalizer (h5 : 5 ≤ Fintype.card Ω) (h6 : Fintype.card Ω ≠ 6)
    {C : Subgroup Q} (φ : ↥C ≃* ↥(alternatingGroup Ω)) {u : Q}
    (hu : u ∈ Subgroup.normalizer (C : Set Q)) : ∃ σ : Perm Ω, ConjSpec φ u σ := by
  obtain ⟨σ, hσ⟩ := CFSG.Holt.H78.exists_perm_conj_eq_of_mulAut_alternatingGroup h5 h6
    (φ.symm.trans ((conjOnSub C hu).trans φ))
  refine ⟨σ, fun c c' hc' => ?_⟩
  have hc'' : c' = conjOnSub C hu c := Subtype.ext (by rw [coe_conjOnSub]; exact hc')
  have := hσ (φ c)
  simpa [hc''] using this

theorem eq_of_conjSpec (h5 : 5 ≤ Fintype.card Ω) {C : Subgroup Q}
    (φ : ↥C ≃* ↥(alternatingGroup Ω)) {u : Q} (hu : u ∈ Subgroup.normalizer (C : Set Q))
    {σ τ : Perm Ω} (hσ : ConjSpec φ u σ) (hτ : ConjSpec φ u τ) : σ = τ := by
  have h1 : σ⁻¹ * τ = 1 := by
    refine eq_one_of_commute_alternatingGroup h5 fun a ha => ?_
    set c : ↥C := φ.symm ⟨a, ha⟩ with hc
    have hcm : u * (c : Q) * u⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.1 hu c).1 c.2
    have hφc : ((φ c : ↥(alternatingGroup Ω)) : Perm Ω) = a := by simp [hc]
    have e1 := hσ c ⟨_, hcm⟩ rfl
    have e2 := hτ c ⟨_, hcm⟩ rfl
    rw [hφc] at e1 e2
    have h : σ * a * σ⁻¹ = τ * a * τ⁻¹ := e1.symm.trans e2
    calc σ⁻¹ * τ * a = σ⁻¹ * (τ * a * τ⁻¹) * τ := by group
      _ = σ⁻¹ * (σ * a * σ⁻¹) * τ := by rw [h]
      _ = a * (σ⁻¹ * τ) := by group
  exact inv_mul_eq_one.1 h1

theorem conjSpec_conj {C : Subgroup Q} (φ : ↥C ≃* ↥(alternatingGroup Ω)) {u v : Q}
    (hu : u ∈ Subgroup.normalizer (C : Set Q)) (hv : v ∈ Subgroup.normalizer (C : Set Q))
    {σ τ : Perm Ω} (hσ : ConjSpec φ u σ) (hτ : ConjSpec φ v τ) :
    ConjSpec φ (v * u * v⁻¹) (τ * σ * τ⁻¹) := by
  intro c c'' hc''
  have hv' : v⁻¹ ∈ Subgroup.normalizer (C : Set Q) := inv_mem hv
  have c1mem : v⁻¹ * (c : Q) * v ∈ C := by
    have := (Subgroup.mem_normalizer_iff.1 hv' c).1 c.2
    simpa using this
  set c₁ : ↥C := ⟨_, c1mem⟩ with hc₁
  have c2mem : u * (c₁ : Q) * u⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.1 hu c₁).1 c₁.2
  set c₂ : ↥C := ⟨_, c2mem⟩ with hc₂
  have e1 : (c : Q) = v * (c₁ : Q) * v⁻¹ := by simp [hc₁, mul_assoc]
  have e2 : (c'' : Q) = v * (c₂ : Q) * v⁻¹ := by
    rw [hc'']; simp [hc₁, hc₂, mul_assoc]
  have s1 := hτ c₁ c e1
  have s2 := hσ c₁ c₂ rfl
  have s3 := hτ c₂ c'' e2
  have h1 : ((φ c₁ : ↥(alternatingGroup Ω)) : Perm Ω) = τ⁻¹ * (φ c : Perm Ω) * τ := by
    rw [s1]; group
  rw [s3, s2, h1]
  group

theorem exists_action (h5 : 5 ≤ Fintype.card Ω) (h6 : Fintype.card Ω ≠ 6) {C : Subgroup Q}
    (φ : ↥C ≃* ↥(alternatingGroup Ω)) {H : Type*} [Group H] (ψ : H →* Q)
    (hψ : ∀ h, ψ h ∈ Subgroup.normalizer (C : Set Q)) :
    ∃ π : H →* Perm Ω, (∀ h, ConjSpec φ (ψ h) (π h)) ∧
      ∀ h, π h = 1 ↔ ψ h ∈ Subgroup.centralizer (C : Set Q) := by
  choose f hf using fun h => exists_perm_conj_of_mem_normalizer h5 h6 φ (hψ h)
  have hmul : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    refine eq_of_conjSpec h5 φ (hψ (a * b)) (hf (a * b)) ?_
    intro c c'' hc''
    have hc'mem : ψ b * (c : Q) * (ψ b)⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.1 (hψ b) c).1 c.2
    have h1 := hf b c ⟨_, hc'mem⟩ rfl
    have h2 := hf a ⟨_, hc'mem⟩ c'' (by rw [hc'', map_mul]; simp [mul_assoc])
    rw [h2, h1]
    simp [mul_assoc]
  refine ⟨MonoidHom.mk' f hmul, hf, fun h => ?_⟩
  show f h = 1 ↔ _
  constructor
  · intro h1
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hcm : ψ h * g * (ψ h)⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.1 (hψ h) g).1 hg
    have e := hf h ⟨g, hg⟩ ⟨_, hcm⟩ rfl
    rw [h1] at e
    have e' : (⟨_, hcm⟩ : ↥C) = ⟨g, hg⟩ := φ.injective (Subtype.ext (by simpa using e))
    have e'' := congrArg Subtype.val e'
    simp only at e''
    calc g * ψ h = (ψ h * g * (ψ h)⁻¹) * ψ h := by rw [e'']
      _ = ψ h * g := by group
  · intro hcent
    refine eq_of_conjSpec h5 φ (hψ h) (hf h) ?_
    intro c c' hc'
    have hc1 := Subgroup.mem_centralizer_iff.1 hcent c c.2
    have : (c' : Q) = c := by
      rw [hc', ← hc1]
      group
    have hcc : c' = c := Subtype.ext this
    rw [hcc]
    simp

theorem sign_eq_one_of_odd_orderOf {σ : Perm Ω} (h : Odd (orderOf σ)) : sign σ = 1 := by
  have hpow : sign σ ^ orderOf σ = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases Int.units_eq_one_or (sign σ) with h1 | h1
  · exact h1
  · rw [h1, h.neg_one_pow] at hpow
    exact absurd hpow (by decide)

theorem mem_alternatingGroup_of_isPGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H : Type*}
    [Group H] (hH : IsPGroup p H) (π : H →* Perm Ω) (h : H) : π h ∈ alternatingGroup Ω := by
  obtain ⟨k, hk⟩ := hH h
  have hord : orderOf (π h) ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
  have hodd : Odd (orderOf (π h)) := by
    have : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
    exact this.of_dvd_nat hord
  exact (mem_alternatingGroup).2 (sign_eq_one_of_odd_orderOf hodd)

end Action

section Bound

theorem not_sq_dvd_factorial_of_lt {p k : ℕ} (hp : p.Prime) (hk : k < 2 * p) :
    ¬ p ^ 2 ∣ k.factorial := by
  have := Fact.mk hp
  intro h
  have hk0 : k.factorial ≠ 0 := k.factorial_ne_zero
  have h2 : 2 ≤ padicValNat p k.factorial := (padicValNat_dvd_iff_le hk0).1 h
  have hp2 : 2 ≤ p := hp.two_le
  have hlt : k < p ^ 2 := by nlinarith
  have hlog : Nat.log p k < 2 := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp
    · exact Nat.log_lt_of_lt_pow hpos.ne' hlt
  rw [padicValNat_factorial hlog] at h2
  have : Finset.Ico 1 2 = {1} := by decide
  rw [this, Finset.sum_singleton, pow_one] at h2
  have : k / p < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  omega

theorem card_le_of_isPGroup_perm_lt {p k : ℕ} (hp : p.Prime) (hk : k < 2 * p)
    {P : Subgroup (Perm (Fin k))} (hP : IsPGroup p P) : Nat.card P ≤ p := by
  have := Fact.mk hp
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (G := P)).1 hP
  have hdvd : Nat.card P ∣ k.factorial := by
    have := Subgroup.card_subgroup_dvd_card P
    simpa [Nat.card_perm, Fintype.card_perm, Fintype.card_fin] using this
  rw [ha] at hdvd ⊢
  have ha1 : a ≤ 1 := by
    by_contra hc
    exact not_sq_dvd_factorial_of_lt hp hk ((pow_dvd_pow p (by omega)).trans hdvd)
  calc p ^ a ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos ha1
    _ = p := pow_one p

variable {K : Type*} [Group K]

theorem ker_comp_eq_of_isPGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H : Type*} [Group H]
    (hH : IsPGroup p H) {T : Type*} [Group T] (π : H →* T) (f : T →* K) (hf : IsPGroup 2 f.ker) :
    (f.comp π).ker = π.ker := by
  ext h
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
  constructor
  · intro hgh
    have hmem : π h ∈ f.ker := hgh
    obtain ⟨b, hb⟩ := hf ⟨_, hmem⟩
    obtain ⟨a, ha⟩ := hH h
    have hb' : (π h) ^ (2 ^ b) = 1 := congrArg (fun x : ↥f.ker => (x : T)) hb
    have ha' : (π h) ^ (p ^ a) = 1 := by rw [← map_pow, ha, map_one]
    have hcop : Nat.Coprime (2 ^ b) (p ^ a) :=
      ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)).pow b a
    have h1 : orderOf (π h) ∣ Nat.gcd (2 ^ b) (p ^ a) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hb') (orderOf_dvd_of_pow_eq_one ha')
    rw [hcop] at h1
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)
  · intro h1
    rw [h1, map_one]

theorem index_ker_le_of_perm {p k : ℕ} (hp : p.Prime) (hk : k < 2 * p) {H : Type*} [Group H]
    (hH : IsPGroup p H) (g : H →* Perm (Fin k)) : g.ker.index ≤ p := by
  have hrange : IsPGroup p g.range := hH.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  rw [Subgroup.index_ker]
  exact card_le_of_isPGroup_perm_lt hp hk hrange

theorem index_ker_le_of_two_kernel {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : k < 2 * p)
    {H : Type*} [Group H] (hH : IsPGroup p H) (π : H →* K) {T : Subgroup K}
    (hT : ∀ h, π h ∈ T) (f : ↥T →* Perm (Fin k)) (hf : IsPGroup 2 f.ker) :
    π.ker.index ≤ p := by
  have hker := ker_comp_eq_of_isPGroup hp hp2 hH (π.codRestrict T hT) f hf
  have hker' : (π.codRestrict T hT).ker = π.ker := MonoidHom.ker_codRestrict _ _ _
  rw [← hker', ← hker]
  exact index_ker_le_of_perm hp hk hH _

end Bound

end CFSG.HardMathSupport.RichardWeiss.Coordinator
