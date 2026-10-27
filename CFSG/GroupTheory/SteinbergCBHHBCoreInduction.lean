module

public import CFSG.GroupTheory.SteinbergCBHHBExtraspecialModule
public import CFSG.GroupTheory.SteinbergCBHHBMinimalConfig

public noncomputable section

namespace CFSG.GroupTheory.HallHigmanB

open Module Subgroup

universe u v

variable {K : Type v} [Field K]

section Restrict

variable {V : Type u} [AddCommGroup V] [Module K V]

@[expose] def restrictUnit (y : (Module.End K V)ˣ) (U : Submodule K V)
    (hU : ∀ v ∈ U, (y : Module.End K V) v ∈ U)
    (hU' : ∀ v ∈ U, ((y⁻¹ : (Module.End K V)ˣ) : Module.End K V) v ∈ U) :
    (Module.End K U)ˣ where
  val := (y : Module.End K V).restrict hU
  inv := ((y⁻¹ : (Module.End K V)ˣ) : Module.End K V).restrict hU'
  val_inv := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    change (y : Module.End K V) (((y⁻¹ : (Module.End K V)ˣ) : Module.End K V) w) = w
    rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
  inv_val := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    change ((y⁻¹ : (Module.End K V)ˣ) : Module.End K V) ((y : Module.End K V) w) = w
    rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]

theorem restrictUnit_apply (y : (Module.End K V)ˣ) (U : Submodule K V)
    (hU : ∀ v ∈ U, (y : Module.End K V) v ∈ U)
    (hU' : ∀ v ∈ U, ((y⁻¹ : (Module.End K V)ˣ) : Module.End K V) v ∈ U) (w : U) :
    ((((restrictUnit y U hU hU' : (Module.End K U)ˣ) : Module.End K U) w : U) : V) =
      (y : Module.End K V) w :=
  rfl

theorem restrictUnit_pow_apply (y : (Module.End K V)ˣ) (U : Submodule K V)
    (hU : ∀ v ∈ U, (y : Module.End K V) v ∈ U)
    (hU' : ∀ v ∈ U, ((y⁻¹ : (Module.End K V)ˣ) : Module.End K V) v ∈ U) (n : ℕ) (w : U) :
    (((((restrictUnit y U hU hU' : (Module.End K U)ˣ) : Module.End K U) - 1) ^ n) w : V) =
      (((y : Module.End K V) - 1) ^ n) w := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    rfl

theorem restrictUnit_units_pow (y : (Module.End K V)ˣ) (U : Submodule K V)
    (hU : ∀ v ∈ U, (y : Module.End K V) v ∈ U)
    (hU' : ∀ v ∈ U, ((y⁻¹ : (Module.End K V)ˣ) : Module.End K V) v ∈ U) (n : ℕ) (w : U) :
    (((((restrictUnit y U hU hU') ^ n : (Module.End K U)ˣ) : Module.End K U) w : U) : V) =
      ((y ^ n : (Module.End K V)ˣ) : Module.End K V) w := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Units.val_mul, Module.End.mul_apply, pow_succ', Units.val_mul,
      Module.End.mul_apply, restrictUnit_apply, ih]

end Restrict

section Card

theorem card_range_lt_of_not_injective {G H : Type*} [Group G] [Group H] [Finite G]
    (f : G →* H) (hf : ¬ Function.Injective f) : Nat.card f.range < Nat.card G := by
  have hker : f.ker ≠ ⊥ := fun h => hf ((MonoidHom.ker_eq_bot_iff f).1 h)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have h2 : Nat.card (G ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have h3 : Nat.card f.ker ≠ 1 := fun h => hker ((Subgroup.card_eq_one).1 h)
  have h4 : 0 < Nat.card f.ker := Nat.card_pos
  have : Finite f.range := Set.finite_range f |>.to_subtype
  have h5 : 0 < Nat.card f.range := Nat.card_pos
  rw [h2] at h1
  rw [h1]
  calc Nat.card f.range = Nat.card f.range * 1 := (mul_one _).symm
    _ < Nat.card f.range * Nat.card f.ker := Nat.mul_lt_mul_of_pos_left (by omega) h5

end Card

section Conj

variable {Γ : Type*} [Group Γ]

@[expose] def conjAut (Q : Subgroup Γ) (y : Γ) (hy : y ∈ normalizer (Q : Set Γ)) : MulAut Q where
  toFun g := ⟨y * g * y⁻¹, conj_mem_of_mem_normalizer hy g.2⟩
  invFun g := ⟨y⁻¹ * g * y, by
    have := conj_mem_of_mem_normalizer (inv_mem hy) g.2
    rwa [inv_inv] at this⟩
  left_inv g := Subtype.ext (by simp [mul_assoc])
  right_inv g := Subtype.ext (by simp [mul_assoc])
  map_mul' g h := Subtype.ext (by
    change y * ((g : Γ) * h) * y⁻¹ = (y * g * y⁻¹) * (y * h * y⁻¹)
    group)

theorem conjAut_apply (Q : Subgroup Γ) (y : Γ) (hy : y ∈ normalizer (Q : Set Γ)) (g : Q) :
    ((conjAut Q y hy g : Q) : Γ) = y * g * y⁻¹ :=
  rfl

theorem conjAut_pow_apply (Q : Subgroup Γ) (y : Γ) (hy : y ∈ normalizer (Q : Set Γ)) (k : ℕ)
    (g : Q) : (((conjAut Q y hy ^ k) g : Q) : Γ) = y ^ k * g * (y ^ k)⁻¹ := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, conjAut_apply, ih, pow_succ']
    group

end Conj

section Core

variable (K) in
@[expose] def HHConclusion (p q : ℕ) {V : Type u} [AddCommGroup V] [Module K V]
    (Q : Subgroup (Module.End K V)ˣ) (x : (Module.End K V)ˣ) (n : ℕ) : Prop :=
  ((x : Module.End K V) - 1) ^ (p ^ n - 1) ≠ 0 ∨
    ∃ m k, 1 ≤ m ∧ m ≤ n ∧ 1 ≤ k ∧ p ^ m - 1 = q ^ k ∧ (∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a) ∧
      ((x : Module.End K V) - 1) ^ (p ^ (n - m) * (p ^ m - 1) - 1) ≠ 0

variable (K) in
@[expose] def HHCore (p q N : ℕ) : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : Subgroup (Module.End K V)ˣ) [Finite Q], Nat.card Q = N → IsPGroup q Q →
    ∀ (x : (Module.End K V)ˣ) (n : ℕ), 1 ≤ n → x ∈ normalizer (Q : Set (Module.End K V)ˣ) →
      x ^ (p ^ n) = 1 → (∃ a ∈ Q, x ^ (p ^ (n - 1)) * a ≠ a * x ^ (p ^ (n - 1))) →
      HHConclusion K p q Q x n

end Core

section NonAbelian

theorem exists_apply_ne_zero_of_ne_zero {W : Type*} [AddCommGroup W] [Module K W]
    {f : Module.End K W} (hf : f ≠ 0) : ∃ w, f w ≠ 0 := by
  by_contra h
  push Not at h
  exact hf (LinearMap.ext h)

variable [IsAlgClosed K] {p q : ℕ} [hp : Fact p.Prime] [CharP K p] [hq : Fact q.Prime]

theorem hhCore_nonabelian (hqp : q ≠ p) {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : Subgroup (Module.End K V)ˣ} [Finite Q] (hQq : IsPGroup q Q)
    {x : (Module.End K V)ˣ} {n : ℕ} (hn : 1 ≤ n)
    (hxQ : x ∈ normalizer (Q : Set (Module.End K V)ˣ)) (hxn : x ^ (p ^ n) = 1)
    (hz : ∃ a ∈ Q, x ^ (p ^ (n - 1)) * a ≠ a * x ^ (p ^ (n - 1)))
    (hmin : ∀ R : Subgroup (Module.End K V)ˣ, R ≤ Q → R ≠ Q →
      x ∈ normalizer (R : Set (Module.End K V)ˣ) →
      ∀ g ∈ R, x ^ (p ^ (n - 1)) * g = g * x ^ (p ^ (n - 1)))
    (hnab : ¬ ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (IH : ∀ N' < Nat.card Q, HHCore.{u} K p q N') :
    HHConclusion K p q Q x n := by
  classical
  set z := x ^ (p ^ (n - 1)) with hzdef
  obtain ⟨hO1, hO2, hO3⟩ := minimal_config hqp hQq hxQ hn hxn hz hmin
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
  have : Finite A := Finite.of_injective (Subgroup.inclusion hAQ) (Subgroup.inclusion_injective hAQ)
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
  have hzA : ∀ a ∈ A, z * a = a * z := hmin A hAQ hAne hxA
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
        have h1 := apply_eq_smul_of_mem_jointGen hq.out hqp hAq hv ⟨_, hcA a ha b hb⟩
        rw [hcon μ hbot a b ha hb, one_smul] at h1
        exact h1
      rw [iSup_jointGen_eq_top hAcomm] at hle
      exact LinearMap.ext fun v => hle Submodule.mem_top
    have h1 : b * a * b⁻¹ * a⁻¹ = 1 := Units.ext hc1
    calc a * b = (b * a * b⁻¹ * a⁻¹)⁻¹ * (b * a) := by group
      _ = b * a := by rw [h1, inv_one, one_mul]
  set Φ := twistChar x hxA with hΦdef
  have hΦz : Function.IsPeriodicPt Φ (p ^ (n - 1)) μ := by
    change Φ^[p ^ (n - 1)] μ = μ
    rw [hΦdef, iterate_twistChar]
    funext a
    simp only [twistChar]
    congr 1
    apply Subtype.ext
    change z⁻¹ * a * z = a
    rw [mul_assoc, ← hzA a a.2, ← mul_assoc, inv_mul_cancel, one_mul]
  obtain ⟨s, hsn, hper⟩ := (Nat.dvd_prime_pow hp.out).1 hΦz.minimalPeriod_dvd
  have hsn' : s ≤ n - 1 := hsn
  set m := n - s with hmdef
  have hm : 1 ≤ m := by omega
  set y := x ^ (p ^ s) with hydef
  have hyQ : y ∈ normalizer (Q : Set (Module.End K V)ˣ) := pow_mem hxQ _
  have hyfix : Φ^[p ^ s] μ = μ := by
    rw [← hper]
    exact Function.iterate_minimalPeriod
  have hpsm : p ^ s * p ^ m = p ^ n := by rw [← pow_add, hmdef]; congr 1; omega
  have hyP : y ^ (p ^ m) = 1 := by rw [hydef, ← pow_mul, hpsm, hxn]
  set U := jointGen A μ with hUdef
  have hUQ : ∀ g ∈ Q, ∀ v ∈ U, ((g : (Module.End K V)ˣ) : Module.End K V) v ∈ U := by
    intro g hg v hv
    rw [hUdef, jointGen, Submodule.mem_iInf] at hv ⊢
    intro a
    exact Module.End.mapsTo_maxGenEigenspace_of_comm
      (congrArg Units.val (((hAmem a).1 a.2).2 g hg)) (μ a) (hv a)
  have hUy : ∀ v ∈ U, (y : Module.End K V) v ∈ U := by
    intro v hv
    have := apply_mem_jointGen_twist (x ^ (p ^ s)) (pow_mem hxA _) hv
    rw [← iterate_twistChar x hxA (p ^ s) μ, ← hΦdef, hyfix] at this
    exact this
  have hUyinv : ∀ v ∈ U, ((y⁻¹ : (Module.End K V)ˣ) : Module.End K V) v ∈ U := by
    have hpow : ∀ (k : ℕ), ∀ v ∈ U, ((y ^ k : (Module.End K V)ˣ) : Module.End K V) v ∈ U := by
      intro k
      induction k with
      | zero => intro v hv; simpa using hv
      | succ k ih =>
        intro v hv
        rw [pow_succ', Units.val_mul, Module.End.mul_apply]
        exact hUy _ (ih v hv)
    have hinv : y⁻¹ = y ^ (p ^ m - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
        Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.out.pos), hyP]
    intro v hv
    rw [hinv]
    exact hpow _ v hv
  have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hμne
  set ρ := restrictRep Q.subtype U (fun g v hv => hUQ g g.2 v hv) with hρdef
  set y' := restrictUnit y U hUy hUyinv with hy'def
  set θ := conjAut Q y hyQ with hθdef
  have hyθ : ∀ g, y' * ρ g * y'⁻¹ = ρ (θ g) := by
    intro g
    apply Units.ext
    refine LinearMap.ext fun w => Subtype.ext ?_
    change (y : Module.End K V) (((g : (Module.End K V)ˣ) : Module.End K V)
      (((y⁻¹ : (Module.End K V)ˣ) : Module.End K V) w)) =
        ((y * (g : (Module.End K V)ˣ) * y⁻¹ : (Module.End K V)ˣ) : Module.End K V) w
    rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
  have hy'P : y' ^ (p ^ m) = 1 := by
    apply Units.ext
    refine LinearMap.ext fun w => Subtype.ext ?_
    rw [restrictUnit_units_pow, hyP]
    rfl
  have hzy : y ^ (p ^ (m - 1)) = z := by
    rw [hydef, hzdef, ← pow_mul, ← pow_add]
    congr 2
    omega
  have hθfpf : ∀ g : Q, g⁻¹ * (θ ^ (p ^ (m - 1))) g ∈ center Q → g ∈ center Q := by
    intro g hg
    rw [mem_center_iff] at hg ⊢
    set g₀ : (Module.End K V)ˣ := (g : (Module.End K V)ˣ) with hg₀
    have h1 : (((θ ^ (p ^ (m - 1))) g : Q) : (Module.End K V)ˣ) = z * g₀ * z⁻¹ := by
      rw [hθdef, conjAut_pow_apply, hzy]
    have hfix : ∀ h ∈ Q, (z * g₀ * z⁻¹ * g₀⁻¹) * h = h * (z * g₀ * z⁻¹ * g₀⁻¹) := by
      intro h hh
      have hw := congrArg Subtype.val (hg ⟨h, hh⟩)
      have hwg := congrArg Subtype.val (hg g)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, h1] at hw hwg
      have hcw : z * g₀ * z⁻¹ * g₀⁻¹ = g₀⁻¹ * (z * g₀ * z⁻¹) := by
        calc z * g₀ * z⁻¹ * g₀⁻¹ = g₀ * (g₀⁻¹ * (z * g₀ * z⁻¹)) * g₀⁻¹ := by group
          _ = (g₀⁻¹ * (z * g₀ * z⁻¹)) * g₀ * g₀⁻¹ := by rw [hwg]
          _ = g₀⁻¹ * (z * g₀ * z⁻¹) := by group
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
    exact apply_eq_smul_of_mem_jointGen hq.out hqp hAq w.2 ⟨c, hcA'⟩
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
  have hinner : (((y' : Module.End K U) - 1) ^ (p ^ m - 1) ≠ 0) ∨ ∃ m' k, 1 ≤ m' ∧ m' ≤ m ∧
      1 ≤ k ∧ p ^ m' - 1 = q ^ k ∧
        ((y' : Module.End K U) - 1) ^ (p ^ (m - m') * (p ^ m' - 1) - 1) ≠ 0 := by
    by_cases hfaith : Function.Injective ρ
    · rcases extraspecial_core hQq ρ hfaith hsc hcl hnab' y' θ hyθ hm hy'P hθfpf with
        h | ⟨k, hk, hkq, h⟩
      · exact Or.inl h
      · refine Or.inr ⟨m, k, hm, le_rfl, hk, hkq, ?_⟩
        rw [Nat.sub_self, pow_zero, one_mul, show p ^ m - 1 - 1 = p ^ m - 2 by omega]
        exact h
    · set Qb := ρ.range with hQbdef
      have hlt : Nat.card Qb < Nat.card Q := card_range_lt_of_not_injective ρ hfaith
      have : Finite Qb := Set.finite_range ρ |>.to_subtype
      have hQbq : IsPGroup q Qb := hQq.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
      have hy'Qb : y' ∈ normalizer (Qb : Set (Module.End K U)ˣ) := by
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
          calc ρ (θ.symm g) = y'⁻¹ * (y' * ρ (θ.symm g) * y'⁻¹) * y' := by group
            _ = y'⁻¹ * (y' * h * y'⁻¹) * y' := by rw [hg]
            _ = h := by group
      have hz' : ∃ a ∈ Qb, y' ^ (p ^ (m - 1)) * a ≠ a * y' ^ (p ^ (m - 1)) := by
        by_contra hcon
        push Not at hcon
        have hyθn : ∀ (k : ℕ) (g : Q), y' ^ k * ρ g * (y' ^ k)⁻¹ = ρ ((θ ^ k) g) := by
          intro k
          induction k with
          | zero => intro g; simp
          | succ k ih =>
            intro g
            rw [pow_succ' θ k, MulAut.mul_apply, ← hyθ, ← ih, pow_succ' y' k]
            group
        have hρθ : ∀ g : Q, ρ ((θ ^ (p ^ (m - 1))) g) = ρ g := by
          intro g
          rw [← hyθn, hcon _ ⟨g, rfl⟩, mul_inv_cancel_right]
        have hρθi : ∀ (i : ℕ) (g : Q), ρ (((θ ^ (p ^ (m - 1))) ^ i) g) = ρ g := by
          intro i
          induction i with
          | zero => intro g; rfl
          | succ i ih => intro g; rw [pow_succ', MulAut.mul_apply, hρθ, ih]
        have hker : ∀ g (hg : g ∈ Q), ρ ⟨g, hg⟩ = 1 := by
          intro g hg
          have hle : closure {c | ∃ h ∈ Q, ∃ i : ℕ, c = h⁻¹ * (z ^ i * h * (z ^ i)⁻¹)} ≤
              ρ.ker.map Q.subtype := by
            rw [closure_le]
            rintro _ ⟨h, hh, i, rfl⟩
            have hzi : z ^ i * h * (z ^ i)⁻¹ ∈ Q := conj_mem_of_mem_normalizer
              (pow_mem (pow_mem hxQ _) _) hh
            refine ⟨⟨h, hh⟩⁻¹ * ⟨_, hzi⟩, ?_, rfl⟩
            rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
            have h1 : (⟨z ^ i * h * (z ^ i)⁻¹, hzi⟩ : Q) =
                ((θ ^ (p ^ (m - 1))) ^ i) ⟨h, hh⟩ := by
              apply Subtype.ext
              change z ^ i * h * (z ^ i)⁻¹ =
                (((θ ^ (p ^ (m - 1))) ^ i) ⟨h, hh⟩ : (Module.End K V)ˣ)
              rw [show (θ ^ (p ^ (m - 1))) ^ i = θ ^ (p ^ (m - 1) * i) from (pow_mul θ _ _).symm,
                hθdef, conjAut_pow_apply, pow_mul, hzy]
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
        have h2 := apply_eq_smul_of_mem_jointGen hq.out hqp hAq w.2
          ⟨t₀ * s₀ * t₀⁻¹ * s₀⁻¹, hcA s₀ hs₀ t₀ ht₀⟩
        change ((t₀ * s₀ * t₀⁻¹ * s₀⁻¹ : (Module.End K V)ˣ) : Module.End K V) w = (w : V) at h1
        rw [h1] at h2
        have h3 : (μ ⟨_, hcA s₀ hs₀ t₀ ht₀⟩ - 1) • (w : V) = 0 := by
          rw [sub_smul, one_smul, ← h2, sub_self]
        have hw' : (w : V) ≠ 0 := fun h => hw (Subtype.ext h)
        exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hw')
      rcases IH _ hlt U Qb rfl hQbq y' m hm hy'Qb hy'P hz' with h | ⟨m', k, hm', hm'm, hk, hkq,
        -, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨m', k, hm', hm'm, hk, hkq, h⟩
  have hlift : ∀ j, ((y' : Module.End K U) - 1) ^ j ≠ 0 →
      ((x : Module.End K V) - 1) ^ (p ^ s * (j + 1) - 1) ≠ 0 := by
    intro j hj
    obtain ⟨w, hw⟩ := exists_apply_ne_zero_of_ne_zero hj
    have hw' : (((x : Module.End K V) ^ (p ^ s) - 1 : Module.End K V) ^ j) w ≠ 0 := by
      intro h0
      apply hw
      apply Subtype.ext
      rw [restrictUnit_pow_apply, hydef, Units.val_pow_eq_pow_val, h0]
      rfl
    exact sub_one_pow_ne_zero_of_jointGen (p := p) hAcomm x hxA hper w.2 hw'
  rcases hinner with h | ⟨m', k, hm', hm'm, hk, hkq, h⟩
  · left
    have := hlift _ h
    rwa [Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.out.pos), hpsm] at this
  · right
    refine ⟨m', k, hm', hm'm.trans (Nat.sub_le n s), hk, hkq,
      ⟨t₀, ht₀, s₀, hs₀, fun h => ?_⟩, ?_⟩
    · apply hμc
      have h1 : t₀ * s₀ * t₀⁻¹ * s₀⁻¹ = 1 := by
        rw [h]
        group
      obtain ⟨w, hwU, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμne
      have h2 := apply_eq_smul_of_mem_jointGen hq.out hqp hAq hwU ⟨_, hcA s₀ hs₀ t₀ ht₀⟩
      have hc1 : ((t₀ * s₀ * t₀⁻¹ * s₀⁻¹ : (Module.End K V)ˣ) : Module.End K V) w = w := by
        rw [h1]
        rfl
      change ((t₀ * s₀ * t₀⁻¹ * s₀⁻¹ : (Module.End K V)ˣ) : Module.End K V) w = _ at h2
      rw [hc1] at h2
      have h3 : (μ ⟨_, hcA s₀ hs₀ t₀ ht₀⟩ - 1) • w = 0 := by
        rw [sub_smul, one_smul, ← h2, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hw0)
    · have hpos : 1 ≤ p ^ (m - m') * (p ^ m' - 1) := by
        have h1 : 2 ≤ p ^ m' := le_trans hp.out.two_le (Nat.le_self_pow (by omega) p)
        have h2 : 1 ≤ p ^ (m - m') := Nat.one_le_pow _ _ hp.out.pos
        calc 1 = 1 * 1 := rfl
          _ ≤ p ^ (m - m') * (p ^ m' - 1) := Nat.mul_le_mul h2 (by omega)
      have := hlift _ h
      rwa [Nat.sub_add_cancel hpos, ← mul_assoc, ← pow_add,
        show s + (m - m') = n - m' by omega] at this

end NonAbelian

section Induction

variable [IsAlgClosed K] {p q : ℕ} [hp : Fact p.Prime] [CharP K p] [hq : Fact q.Prime]

theorem hhCore_all (hqp : q ≠ p) (N : ℕ) : HHCore.{u} K p q N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro V _ _ _ Q _ hcard hQq x n hn hxQ hxn hz
  classical
  by_cases hred : ∃ R : Subgroup (Module.End K V)ˣ, R ≤ Q ∧ R ≠ Q ∧
      x ∈ normalizer (R : Set (Module.End K V)ˣ) ∧
      ∃ a ∈ R, x ^ (p ^ (n - 1)) * a ≠ a * x ^ (p ^ (n - 1))
  · obtain ⟨R, hRQ, hRne, hxR, hzR⟩ := hred
    have : Finite R := Finite.of_injective (Subgroup.inclusion hRQ)
      (Subgroup.inclusion_injective hRQ)
    have hlt : Nat.card R < N := hcard ▸ Subgroup.card_lt_of_lt (lt_of_le_of_ne hRQ hRne)
    rcases ih _ hlt V R rfl (hQq.to_le hRQ) x n hn hxR hxn hzR with h |
      ⟨m, k, hm, hmn, hk, hkq, ⟨a, ha, b, hb, hab⟩, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨m, k, hm, hmn, hk, hkq, ⟨a, hRQ ha, b, hRQ hb, hab⟩, h⟩
  push Not at hred
  by_cases hab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a
  · left
    exact sub_one_pow_ne_zero_of_abelian (A := Q)
      (fun a b => congrArg Units.val (hab a a.2 b b.2)) hq.out hqp hQq x hxQ hn hxn hz
  · exact hhCore_nonabelian hqp hQq hn hxQ hxn hz hred hab fun N' hN' => ih N' (hcard ▸ hN')

theorem hh_core (hqp : q ≠ p) {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : Subgroup (Module.End K V)ˣ) [Finite Q] (hQq : IsPGroup q Q)
    (x : (Module.End K V)ˣ) {n : ℕ} (hn : 1 ≤ n)
    (hxQ : x ∈ normalizer (Q : Set (Module.End K V)ˣ)) (hxn : x ^ (p ^ n) = 1)
    (hz : ∃ a ∈ Q, x ^ (p ^ (n - 1)) * a ≠ a * x ^ (p ^ (n - 1))) :
    HHConclusion K p q Q x n :=
  hhCore_all hqp _ V Q rfl hQq x n hn hxQ hxn hz

end Induction

end CFSG.GroupTheory.HallHigmanB
