module

public import CFSG.GroupTheory.SteinbergCBHHBCoreInduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.FPFSCoprimeCore

public section

universe u v

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.HHChar

open Module Subgroup CFSG.GroupTheory.HallHigmanB CFSG.LocalAnalysis.RankThreeTheoremC.FPFS

section KLInduction

variable {K : Type v} [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

section Abelian

variable {V : Type*} [AddCommGroup V] [Module K V] {A : Subgroup (Module.End K V)ˣ}

omit [IsAlgClosed K] [CharP K ℓ] in
theorem exists_fixed_of_jointGen
    (hA : ∀ a b : A, Commute ((a : (Module.End K V)ˣ) : Module.End K V)
      ((b : (Module.End K V)ˣ) : Module.End K V))
    (x : (Module.End K V)ˣ) (hx : x ∈ normalizer (A : Set (Module.End K V)ˣ)) {p : ℕ}
    [hp : Fact p.Prime] (hxp : x ^ p = 1) {χ : A → K}
    (hper : Function.minimalPeriod (twistChar x hx) χ = p) {u : V} (hu : u ∈ jointGen A χ)
    (hu0 : u ≠ 0) : ∃ v : V, v ≠ 0 ∧ (x : Module.End K V) v = v := by
  classical
  set Φ := twistChar x hx with hΦ
  have hp0 : 0 < p := hp.out.pos
  have hmem : ∀ i : Fin p, ((x : Module.End K V) ^ (i : ℕ)) u ∈
      jointGen A (Φ^[(i : ℕ)] χ) := fun i => by
    have := apply_mem_jointGen_twist (x ^ (i : ℕ)) (pow_mem hx _) hu
    rwa [← iterate_twistChar, Units.val_pow_eq_pow_val] at this
  have hne : ∀ i : Fin p, ((x : Module.End K V) ^ (i : ℕ)) u ≠ 0 := fun i h => by
    apply hu0
    have hinj : Function.Injective ((x : Module.End K V) ^ (i : ℕ)) := by
      rw [← Units.val_pow_eq_pow_val]
      exact (Module.End.isUnit_iff _).1 (Units.isUnit _) |>.1
    exact hinj (by rw [h, map_zero])
  have hind : iSupIndep fun i : Fin p => jointGen A (Φ^[(i : ℕ)] χ) := by
    refine (iSupIndep_jointGen hA).comp fun i i' h => Fin.ext ?_
    have hi : (i : ℕ) < Function.minimalPeriod Φ χ := by rw [hper]; exact i.2
    have hi' : (i' : ℕ) < Function.minimalPeriod Φ χ := by rw [hper]; exact i'.2
    exact Function.iterate_injOn_Iio_minimalPeriod hi hi' h
  have hli := hind.linearIndependent _ hmem hne
  have hsum : ∑ i : Fin p, ((x : Module.End K V) ^ (i : ℕ)) u ≠ 0 := by
    intro h
    have := linearIndependent_iff'.1 hli Finset.univ (fun _ => 1) (by simpa using h)
      ⟨0, hp0⟩ (Finset.mem_univ _)
    exact one_ne_zero this
  refine ⟨∑ i : Fin p, ((x : Module.End K V) ^ (i : ℕ)) u, hsum, ?_⟩
  rw [Fin.sum_univ_eq_sum_range (fun i => ((x : Module.End K V) ^ i) u) p, map_sum]
  have h1 : ∀ i : ℕ, (x : Module.End K V) (((x : Module.End K V) ^ i) u) =
      ((x : Module.End K V) ^ (i + 1)) u := fun i => by
    rw [pow_succ', Module.End.mul_apply]
  simp only [h1]
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun i => ((x : Module.End K V) ^ i) u)]
  have h2 : ((x : Module.End K V) ^ (n + 1)) u = ((x : Module.End K V) ^ 0) u := by
    have : (x : Module.End K V) ^ (n + 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, hxp, Units.val_one]
    rw [this, pow_zero]
  rw [h2]

theorem exists_fixed_of_abelian_char [FiniteDimensional K V]
    (hA : ∀ a b : A, Commute ((a : (Module.End K V)ˣ) : Module.End K V)
      ((b : (Module.End K V)ˣ) : Module.End K V)) {p q : ℕ} [hp : Fact p.Prime] (hq : q.Prime)
    (hqℓ : q ≠ ℓ) (hAq : IsPGroup q A) (x : (Module.End K V)ˣ)
    (hx : x ∈ normalizer (A : Set (Module.End K V)ˣ)) (hxp : x ^ p = 1)
    (hz : ∃ a ∈ A, x * a ≠ a * x) : ∃ v : V, v ≠ 0 ∧ (x : Module.End K V) v = v := by
  classical
  set Φ := twistChar x hx with hΦ
  obtain ⟨χ, hχne, hχz⟩ : ∃ χ : A → K, jointGen A χ ≠ ⊥ ∧ Φ χ ≠ χ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, ha, hza⟩ := hz
    apply hza
    have hconj : ((x⁻¹ * a * x : (Module.End K V)ˣ) : Module.End K V) =
        (a : Module.End K V) := by
      have hle : ⨆ χ : A → K, jointGen A χ ≤ LinearMap.eqLocus
          ((x⁻¹ * a * x : (Module.End K V)ˣ) : Module.End K V) (a : Module.End K V) := by
        refine iSup_le fun χ => ?_
        by_cases hbot : jointGen A χ = ⊥
        · rw [hbot]
          exact bot_le
        intro v hv
        have hfix := hcon χ hbot
        have h1 := apply_eq_smul_of_mem_jointGen (p := ℓ) hq hqℓ hAq hv
          ⟨x⁻¹ * a * x, inv_mul_mul_mem_of_mem_normalizer hx ha⟩
        have h2 := apply_eq_smul_of_mem_jointGen (p := ℓ) hq hqℓ hAq hv ⟨a, ha⟩
        change ((x⁻¹ * a * x : (Module.End K V)ˣ) : Module.End K V) v =
          (a : Module.End K V) v
        rw [h1, h2]
        congr 1
        have h3 : twistChar x hx χ ⟨a, ha⟩ = χ ⟨a, ha⟩ := by
          rw [← hΦ, hfix]
        exact h3
      rw [iSup_jointGen_eq_top hA] at hle
      exact LinearMap.ext fun v => hle (Submodule.mem_top (x := v))
    have := Units.ext hconj
    calc x * a = x * (x⁻¹ * a * x) := by rw [this]
      _ = a * x := by group
  have hper : Function.minimalPeriod Φ χ = p := by
    have hdvd : Function.minimalPeriod Φ χ ∣ p :=
      Function.IsPeriodicPt.minimalPeriod_dvd (iterate_twistChar_of_pow_eq_one x hx hxp χ)
    rcases (Nat.dvd_prime hp.out).1 hdvd with h | h
    · exfalso
      apply hχz
      have h3 := Function.iterate_minimalPeriod (f := Φ) (x := χ)
      rwa [h, Function.iterate_one] at h3
    · exact h
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχne
  exact exists_fixed_of_jointGen hA x hx hxp hper hu hu0

end Abelian


section Core

def KLCore (K : Type v) [Field K] (p q N : ℕ) : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : Subgroup (Module.End K V)ˣ) [Finite Q], Nat.card Q = N → IsPGroup q Q →
    ∀ (x : (Module.End K V)ˣ), x ∈ normalizer (Q : Set (Module.End K V)ˣ) → x ^ p = 1 →
      (∃ a ∈ Q, x * a ≠ a * x) → ∃ v : V, v ≠ 0 ∧ (x : Module.End K V) v = v

end Core

section NonAbelian

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]

theorem klCore_nonabelian_char (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hqp : q ≠ p) (hpℓ : p ≠ ℓ)
    (hqℓ : q ≠ ℓ)
    {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : Subgroup (Module.End K V)ˣ} [Finite Q] (hQq : IsPGroup q Q)
    {x : (Module.End K V)ˣ} (hxQ : x ∈ normalizer (Q : Set (Module.End K V)ˣ))
    (hxp : x ^ p = 1) (hz : ∃ a ∈ Q, x * a ≠ a * x)
    (hmin : ∀ R : Subgroup (Module.End K V)ˣ, R ≤ Q → R ≠ Q →
      x ∈ normalizer (R : Set (Module.End K V)ˣ) → ∀ g ∈ R, x * g = g * x)
    (hnab : ¬ ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (IH : ∀ N' < Nat.card Q, KLCore.{u, v} K p q N') :
    ∃ v : V, v ≠ 0 ∧ (x : Module.End K V) v = v := by
  classical
  have hp0 : 0 < p := hp.out.pos
  have hℓprime : ℓ.Prime := Fact.out
  have hpK : NeZero (p : K) := ⟨by
    rw [Ne, CharP.cast_eq_zero_iff K ℓ]
    intro h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓprime hp.out).1 h).symm⟩
  have hmc := minimal_config (p := p) (q := q) hqp hQq hxQ (n := 1) le_rfl
    (by rwa [pow_one]) (by simpa using hz) (by simpa using hmin)
  simp only [Nat.sub_self, pow_zero, pow_one] at hmc
  obtain ⟨hO1, hO2, hO3⟩ := hmc
  set A : Subgroup (Module.End K V)ˣ := (center Q).map Q.subtype with hAdef
  have hAmem : ∀ a, a ∈ A ↔ a ∈ Q ∧ ∀ g ∈ Q, a * g = g * a := by
    intro a
    constructor
    · rintro ⟨a', ha', rfl⟩
      refine ⟨a'.2, fun g hg => ?_⟩
      have := congrArg Subtype.val ((mem_center_iff.1 ha') ⟨g, hg⟩)
      exact this.symm
    · rintro ⟨haQ, ha⟩
      exact ⟨⟨a, haQ⟩, mem_center_iff.2 fun g => Subtype.ext (ha g g.2).symm, rfl⟩
  have hAQ : A ≤ Q := fun a ha => ((hAmem a).1 ha).1
  have hAcomm : ∀ a b : A, Commute ((a : (Module.End K V)ˣ) : Module.End K V)
      ((b : (Module.End K V)ˣ) : Module.End K V) := fun a b =>
    congrArg Units.val (((hAmem a).1 a.2).2 b (hAQ b.2))
  have : Finite A := Finite.of_injective (Subgroup.inclusion hAQ)
    (Subgroup.inclusion_injective hAQ)
  have hAq : IsPGroup q A := hQq.to_le hAQ
  have hxA : x ∈ normalizer (A : Set (Module.End K V)ˣ) := by
    rw [mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      obtain ⟨haQ, hac⟩ := (hAmem a).1 ha
      refine (hAmem _).2 ⟨conj_mem_of_mem_normalizer hxQ haQ, fun g hg => ?_⟩
      have hg' : x⁻¹ * g * x ∈ Q := by
        have := conj_mem_of_mem_normalizer (inv_mem hxQ) hg
        rwa [inv_inv] at this
      have h1 := hac _ hg'
      calc x * a * x⁻¹ * g = x * (a * (x⁻¹ * g * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * g * x) * a) * x⁻¹ := by rw [h1]
        _ = g * (x * a * x⁻¹) := by group
    · intro ha
      obtain ⟨haQ, hac⟩ := (hAmem _).1 ha
      have haQ' : a ∈ Q := by
        have := conj_mem_of_mem_normalizer (inv_mem hxQ) haQ
        rwa [inv_inv, show x⁻¹ * (x * a * x⁻¹) * x = a by group] at this
      refine (hAmem a).2 ⟨haQ', fun g hg => ?_⟩
      have h1 := hac _ (conj_mem_of_mem_normalizer hxQ hg)
      calc a * g = x⁻¹ * ((x * a * x⁻¹) * (x * g * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * g * x⁻¹) * (x * a * x⁻¹)) * x := by rw [h1]
        _ = g * a := by group
  have hAne : A ≠ Q := fun h => hnab fun a ha b hb => by
    rw [← h] at ha
    exact ((hAmem a).1 ha).2 b hb
  have hzA : ∀ a ∈ A, x * a = a * x := hmin A hAQ hAne hxA
  have hcA : ∀ s ∈ Q, ∀ t ∈ Q, t * s * t⁻¹ * s⁻¹ ∈ A := fun s hs t ht =>
    (hAmem _).2 ⟨by
      exact mul_mem (mul_mem (mul_mem ht hs) (inv_mem ht)) (inv_mem hs),
      fun g hg => hO1 s hs t ht g hg⟩
  obtain ⟨μ, hμne, s₀, t₀, hs₀, ht₀, hμc⟩ : ∃ μ : A → K, jointGen A μ ≠ ⊥ ∧
      ∃ s t, ∃ (hs : s ∈ Q) (ht : t ∈ Q), μ ⟨t * s * t⁻¹ * s⁻¹, hcA s hs t ht⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hnab
    intro a ha b hb
    have hc1 : ((b * a * b⁻¹ * a⁻¹ : (Module.End K V)ˣ) : Module.End K V) = 1 := by
      have hle : ⨆ μ : A → K, jointGen A μ ≤ LinearMap.eqLocus
          ((b * a * b⁻¹ * a⁻¹ : (Module.End K V)ˣ) : Module.End K V) 1 := by
        refine iSup_le fun μ => ?_
        by_cases hbot : jointGen A μ = ⊥
        · rw [hbot]
          exact bot_le
        intro v hv
        rw [LinearMap.mem_eqLocus, Module.End.one_apply]
        have h1 := apply_eq_smul_of_mem_jointGen (p := ℓ) hq.out hqℓ hAq hv ⟨_, hcA a ha b hb⟩
        rw [hcon μ hbot a b ha hb, one_smul] at h1
        exact h1
      rw [iSup_jointGen_eq_top hAcomm] at hle
      exact LinearMap.ext fun v => hle Submodule.mem_top
    have h1 : b * a * b⁻¹ * a⁻¹ = 1 := Units.ext hc1
    calc a * b = (b * a * b⁻¹ * a⁻¹)⁻¹ * (b * a) := by group
      _ = b * a := by rw [h1, inv_one, one_mul]
  set Φ := twistChar x hxA with hΦdef
  have hΦμ : Φ μ = μ := by
    rw [hΦdef]
    funext a
    simp only [twistChar]
    congr 1
    apply Subtype.ext
    change x⁻¹ * a * x = a
    rw [mul_assoc, ← hzA a a.2, ← mul_assoc, inv_mul_cancel, one_mul]
  set U := jointGen A μ with hUdef
  have hUQ : ∀ g ∈ Q, ∀ v ∈ U, ((g : (Module.End K V)ˣ) : Module.End K V) v ∈ U := by
    intro g hg v hv
    rw [hUdef, jointGen, Submodule.mem_iInf] at hv ⊢
    intro a
    exact Module.End.mapsTo_maxGenEigenspace_of_comm
      (congrArg Units.val (((hAmem a).1 a.2).2 g hg)) (μ a) (hv a)
  have hUx : ∀ v ∈ U, (x : Module.End K V) v ∈ U := by
    intro v hv
    have := apply_mem_jointGen_twist x hxA hv
    rwa [← hΦdef, hΦμ] at this
  have hUxinv : ∀ v ∈ U, ((x⁻¹ : (Module.End K V)ˣ) : Module.End K V) v ∈ U := by
    have hpow : ∀ (k : ℕ), ∀ v ∈ U, ((x ^ k : (Module.End K V)ˣ) : Module.End K V) v ∈ U := by
      intro k
      induction k with
      | zero => intro v hv; simpa using hv
      | succ k ih =>
        intro v hv
        rw [pow_succ', Units.val_mul, Module.End.mul_apply]
        exact hUx _ (ih v hv)
    have hinv : x⁻¹ = x ^ (p - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hp0, hxp]
    intro v hv
    rw [hinv]
    exact hpow _ v hv
  have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hμne
  set ρ := restrictRep Q.subtype U (fun g v hv => hUQ g g.2 v hv) with hρdef
  set x' := restrictUnit x U hUx hUxinv with hx'def
  set θ := conjAut Q x hxQ with hθdef
  have hyθ : ∀ g, x' * ρ g * x'⁻¹ = ρ (θ g) := by
    intro g
    apply Units.ext
    refine LinearMap.ext fun w => Subtype.ext ?_
    change (x : Module.End K V) (((g : (Module.End K V)ˣ) : Module.End K V)
      (((x⁻¹ : (Module.End K V)ˣ) : Module.End K V) w)) =
        ((x * (g : (Module.End K V)ˣ) * x⁻¹ : (Module.End K V)ˣ) : Module.End K V) w
    rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
  have hx'P : x' ^ p = 1 := by
    apply Units.ext
    refine LinearMap.ext fun w => Subtype.ext ?_
    rw [restrictUnit_units_pow, hxp]
    rfl
  have hθfpf : ∀ g : Q, g⁻¹ * θ g ∈ center Q → g ∈ center Q := by
    intro g hg
    rw [mem_center_iff] at hg ⊢
    set g₀ : (Module.End K V)ˣ := (g : (Module.End K V)ˣ) with hg₀
    have h1 : ((θ g : Q) : (Module.End K V)ˣ) = x * g₀ * x⁻¹ := by
      rw [hθdef, conjAut_apply]
    have hfix : ∀ h ∈ Q, (x * g₀ * x⁻¹ * g₀⁻¹) * h = h * (x * g₀ * x⁻¹ * g₀⁻¹) := by
      intro h hh
      have hw := congrArg Subtype.val (hg ⟨h, hh⟩)
      have hwg := congrArg Subtype.val (hg g)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, h1] at hw hwg
      have hcw : x * g₀ * x⁻¹ * g₀⁻¹ = g₀⁻¹ * (x * g₀ * x⁻¹) := by
        calc x * g₀ * x⁻¹ * g₀⁻¹ = g₀ * (g₀⁻¹ * (x * g₀ * x⁻¹)) * g₀⁻¹ := by group
          _ = (g₀⁻¹ * (x * g₀ * x⁻¹)) * g₀ * g₀⁻¹ := by rw [hwg]
          _ = g₀⁻¹ * (x * g₀ * x⁻¹) := by group
      rw [hcw]
      exact hw.symm
    intro h
    exact Subtype.ext (hO3 g₀ g.2 hfix h h.2).symm
  have hsc : ∀ c ∈ center Q, ∃ ν : K,
      ((ρ c : (Module.End K U)ˣ) : Module.End K U) = ν • 1 := by
    intro c hc
    have hcA' : (c : (Module.End K V)ˣ) ∈ A := ⟨c, hc, rfl⟩
    refine ⟨μ ⟨c, hcA'⟩, LinearMap.ext fun w => Subtype.ext ?_⟩
    change (((c : Q) : (Module.End K V)ˣ) : Module.End K V) (w : V) = μ ⟨c, hcA'⟩ • (w : V)
    exact apply_eq_smul_of_mem_jointGen (p := ℓ) hq.out hqℓ hAq w.2 ⟨c, hcA'⟩
  have hcl : ∀ s t : Q, t * s * t⁻¹ * s⁻¹ ∈ center Q := by
    intro s t
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (hO1 s s.2 t t.2 g g.2).symm
  have hnab' : ∃ g : Q, g ∉ center Q := by
    by_contra hcon
    push Not at hcon
    apply hnab
    intro a ha b hb
    have := congrArg Subtype.val ((mem_center_iff.1 (hcon ⟨a, ha⟩)) ⟨b, hb⟩)
    exact this.symm
  have hinner : ∃ w : U, w ≠ 0 ∧ (x' : Module.End K U) w = w := by
    by_cases hfaith : Function.Injective ρ
    · exact extraspecial_core_coprime hp2 hq2 hQq ρ hfaith hsc hcl hnab' x' θ hyθ hx'P hθfpf
    · set Qb := ρ.range with hQbdef
      have hlt : Nat.card Qb < Nat.card Q := card_range_lt_of_not_injective ρ hfaith
      have : Finite Qb := Set.finite_range ρ |>.to_subtype
      have hQbq : IsPGroup q Qb := hQq.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
      have hx'Qb : x' ∈ normalizer (Qb : Set (Module.End K U)ˣ) := by
        rw [mem_normalizer_iff]
        intro h
        constructor
        · rintro ⟨g, rfl⟩
          exact ⟨θ g, (hyθ g).symm⟩
        · rintro ⟨g, hg⟩
          refine ⟨θ.symm g, ?_⟩
          have := hyθ (θ.symm g)
          rw [MulEquiv.apply_symm_apply] at this
          rw [← this] at hg
          calc ρ (θ.symm g) = x'⁻¹ * (x' * ρ (θ.symm g) * x'⁻¹) * x' := by group
            _ = x'⁻¹ * (x' * h * x'⁻¹) * x' := by rw [hg]
            _ = h := by group
      have hz' : ∃ a ∈ Qb, x' * a ≠ a * x' := by
        by_contra hcon
        push Not at hcon
        have hρθ : ∀ g : Q, ρ (θ g) = ρ g := by
          intro g
          rw [← hyθ, hcon _ ⟨g, rfl⟩, mul_inv_cancel_right]
        have hρθi : ∀ (i : ℕ) (g : Q), ρ ((θ ^ i) g) = ρ g := by
          intro i
          induction i with
          | zero => intro g; rfl
          | succ i ih => intro g; rw [pow_succ', MulAut.mul_apply, hρθ, ih]
        have hker : ∀ g (hg : g ∈ Q), ρ ⟨g, hg⟩ = 1 := by
          intro g hg
          have hle : closure {c | ∃ h ∈ Q, ∃ i : ℕ, c = h⁻¹ * (x ^ i * h * (x ^ i)⁻¹)} ≤
              ρ.ker.map Q.subtype := by
            rw [closure_le]
            rintro _ ⟨h, hh, i, rfl⟩
            have hzi : x ^ i * h * (x ^ i)⁻¹ ∈ Q := conj_mem_of_mem_normalizer
              (pow_mem hxQ _) hh
            refine ⟨⟨h, hh⟩⁻¹ * ⟨_, hzi⟩, ?_, rfl⟩
            rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
            have h1 : (⟨x ^ i * h * (x ^ i)⁻¹, hzi⟩ : Q) = (θ ^ i) ⟨h, hh⟩ := by
              apply Subtype.ext
              change x ^ i * h * (x ^ i)⁻¹ = (((θ ^ i) ⟨h, hh⟩ : Q) : (Module.End K V)ˣ)
              rw [hθdef, conjAut_pow_apply]
            rw [h1, hρθi]
          obtain ⟨g', hg', hgg'⟩ := hle (hO2 g hg)
          rw [SetLike.mem_coe, MonoidHom.mem_ker] at hg'
          rw [show (⟨g, hg⟩ : Q) = g' from Subtype.ext hgg'.symm]
          exact hg'
        apply hμc
        have hc := hker _ (mul_mem (mul_mem (mul_mem ht₀ hs₀) (inv_mem ht₀)) (inv_mem hs₀))
        obtain ⟨w, hw⟩ := exists_ne (0 : U)
        have h1 := congrArg (fun F : (Module.End K U)ˣ => (((F : Module.End K U) w : U) : V)) hc
        simp only [Units.val_one, Module.End.one_apply] at h1
        have h2 := apply_eq_smul_of_mem_jointGen (p := ℓ) hq.out hqℓ hAq w.2
          ⟨t₀ * s₀ * t₀⁻¹ * s₀⁻¹, hcA s₀ hs₀ t₀ ht₀⟩
        change ((t₀ * s₀ * t₀⁻¹ * s₀⁻¹ : (Module.End K V)ˣ) : Module.End K V) w = (w : V) at h1
        rw [h1] at h2
        have h3 : (μ ⟨_, hcA s₀ hs₀ t₀ ht₀⟩ - 1) • (w : V) = 0 := by
          rw [sub_smul, one_smul, ← h2, sub_self]
        have hw' : (w : V) ≠ 0 := fun h => hw (Subtype.ext h)
        exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hw')
      exact IH _ hlt U Qb rfl hQbq x' hx'Qb hx'P hz'
  obtain ⟨w, hw0, hw⟩ := hinner
  exact ⟨(w : V), fun h => hw0 (Subtype.ext h), congrArg Subtype.val hw⟩

end NonAbelian

section Induction

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]

theorem klCore_all_char (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hqp : q ≠ p) (hpℓ : p ≠ ℓ)
    (hqℓ : q ≠ ℓ) (N : ℕ) : KLCore.{u, v} K p q N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro V _ _ _ Q _ hcard hQq x hxQ hxp hz
  classical
  by_cases hred : ∃ R : Subgroup (Module.End K V)ˣ, R ≤ Q ∧ R ≠ Q ∧
      x ∈ normalizer (R : Set (Module.End K V)ˣ) ∧ ∃ a ∈ R, x * a ≠ a * x
  · obtain ⟨R, hRQ, hRne, hxR, hzR⟩ := hred
    have : Finite R := Finite.of_injective (Subgroup.inclusion hRQ)
      (Subgroup.inclusion_injective hRQ)
    have hlt : Nat.card R < N := hcard ▸ Subgroup.card_lt_of_lt (lt_of_le_of_ne hRQ hRne)
    exact ih _ hlt V R rfl (hQq.to_le hRQ) x hxR hxp hzR
  push Not at hred
  by_cases hab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a
  · exact exists_fixed_of_abelian_char (A := Q)
      (fun a b => congrArg Units.val (hab a a.2 b b.2)) hq.out hqℓ hQq x hxQ hxp hz
  · exact klCore_nonabelian_char hp2 hq2 hqp hpℓ hqℓ hQq hxQ hxp hz hred hab
      (fun N' hN' => ih N' (hcard ▸ hN'))

theorem kl_core_char (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hqp : q ≠ p) (hpℓ : p ≠ ℓ)
    (hqℓ : q ≠ ℓ) {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : Subgroup (Module.End K V)ˣ) [Finite Q] (hQ : IsPGroup q Q) (x : (Module.End K V)ˣ)
    (hxQ : x ∈ normalizer (Q : Set (Module.End K V)ˣ)) (hxp : x ^ p = 1)
    (hfix : ∀ v : V, (x : Module.End K V) v = v → v = 0) : ∀ a ∈ Q, x * a = a * x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hv0, hv⟩ := klCore_all_char hp2 hq2 hqp hpℓ hqℓ _ V Q rfl hQ x hxQ hxp hcon
  exact hv0 (hfix v hv)

end Induction

end KLInduction

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.HHChar
