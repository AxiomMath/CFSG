module

public import CFSG.Goldschmidt.Steps.G37Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutOmega
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderCount

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ComponentClassification.AschbacherToolkit
open CFSG.ComponentClassification.AschbacherToolkit.Bender

variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
theorem apply_mem_sylowCenter {R : Subgroup Q} [Finite R] {β : MulAut Q}
    (hβR : ∀ r ∈ R, β r ∈ R) {z : Q} (hz : z ∈ sylowCenter R) : β z ∈ sylowCenter R := by
  have hβR' : R.map β.toMonoidHom = R :=
    Subgroup.eq_of_le_of_card_ge (fun _ ⟨r, hr, hrx⟩ => hrx ▸ hβR r hr)
      (card_map_of_injective (f := β.toMonoidHom) β.injective).ge
  obtain ⟨hzR, hzc⟩ := mem_sylowCenter.mp hz
  refine mem_sylowCenter.mpr ⟨hβR z hzR, fun t ht => ?_⟩
  have ht' : t ∈ R.map β.toMonoidHom := by rw [hβR']; exact ht
  obtain ⟨s, hs, rfl⟩ := ht'
  change β s * β z = β z * β s
  rw [← map_mul, ← map_mul, hzc s hs]

theorem card_le_mul_card_comap_fixing {q k : ℕ} (hB : fusionBenderBorel Q q k) (hq : 2 ≤ q)
    (R : Sylow 2 Q) {T : Type*} [Group T] [Finite T] (hT : IsPGroup 2 T) (σ : T →* MulAut Q)
    (hσR : ∀ t, ∀ r ∈ (R : Subgroup Q), σ t r ∈ (R : Subgroup Q)) :
    Nat.card T ≤ (q - 1) *
      Nat.card ((fixingSubgroup (MulAut Q) (sylowCenter (R : Subgroup Q) : Set Q)).comap σ) := by
  classical
  set Z := sylowCenter (R : Subgroup Q) with hZdef
  set F := (fixingSubgroup (MulAut Q) (Z : Set Q)).comap σ with hFdef
  have hmemF : ∀ t, t ∈ F ↔ ∀ z ∈ Z, σ t z = z := fun t => by
    rw [hFdef, mem_comap, mem_fixingSubgroup_iff]
    rfl
  obtain ⟨hSE, ⟨D, hDcyc, hDodd, -, hND⟩, -, -, -⟩ := hB R
  obtain ⟨-, hZ2, hZcard, -⟩ := benderBorel_sylowCenter hB R
  have hσS : ∀ t, σ t • R = R := fun t => Omega.smul_eq_of_mapsTo (hσR t)
  have hσZ : ∀ t, ∀ z ∈ Z, σ t z ∈ Z := fun t z hz => apply_mem_sylowCenter (hσR t) hz
  have hσN : ∀ t, ∀ n ∈ normalizer ((R : Subgroup Q) : Set Q),
      σ t n ∈ normalizer ((R : Subgroup Q) : Set Q) := fun t n hn => by
    have := Omega.mem_normalizer_smul (α := σ t) hn
    rwa [hσS t] at this
  have hZN : ∀ n ∈ normalizer ((R : Subgroup Q) : Set Q), ∀ z ∈ Z, n * z * n⁻¹ ∈ Z := by
    intro n hn z hz
    have h := conj_mem_sylowCenter (inv_mem hn) hz
    rwa [inv_inv] at h
  have hDN : D ≤ normalizer ((R : Subgroup Q) : Set Q) := hND ▸ le_sup_right
  have : IsCyclic D := hDcyc
  have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (IsCyclic.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hact : ∀ n ∈ normalizer ((R : Subgroup Q) : Set Q), ∃ d ∈ D,
      ∀ z ∈ Z, n * z * n⁻¹ = d * z * d⁻¹ := by
    intro n hn
    rw [← hND, sup_comm] at hn
    obtain ⟨d, hd, r, hr, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hDN hn
    refine ⟨d, hd, fun z hz => ?_⟩
    have hrz : r * z * r⁻¹ = z := by
      rw [(mem_sylowCenter.mp hz).2 r hr, mul_inv_cancel_right]
    calc d * r * z * (d * r)⁻¹ = d * (r * z * r⁻¹) * d⁻¹ := by group
      _ = d * z * d⁻¹ := by rw [hrz]
  have htrans : ∀ z₁ ∈ Z, z₁ ≠ 1 → ∀ z₂ ∈ Z, z₂ ≠ 1 → ∃ d ∈ D, d * z₁ * d⁻¹ = z₂ := by
    intro z₁ hz₁ h₁ z₂ hz₂ h₂
    obtain ⟨n, hn, hnz⟩ := normalizer_transitive_center hSE hZ2 hz₁ hz₂ h₁ h₂
    obtain ⟨d, hd, hdz⟩ := hact n⁻¹ (inv_mem hn)
    exact ⟨d, hd, by rw [← hdz z₁ hz₁, inv_inv]; exact hnz⟩
  obtain ⟨z₀, hz₀, hz₀1⟩ : ∃ z₀ ∈ Z, z₀ ≠ 1 := by
    have h1 : 1 < Nat.card Z := by rw [hZcard]; omega
    obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      ((Subgroup.one_lt_card_iff_ne_bot _).mp h1)
    exact ⟨z, hz, fun h => hz1 (Subtype.ext h)⟩
  have hreg : ∀ d ∈ D, ∀ d' ∈ D, d * z₀ * d⁻¹ = d' * z₀ * d'⁻¹ →
      ∀ z ∈ Z, d * z * d⁻¹ = d' * z * d'⁻¹ := by
    intro d hd d' hd' h z hz
    by_cases hz1 : z = 1
    · simp [hz1]
    obtain ⟨e, he, rfl⟩ := htrans z₀ hz₀ hz₀1 z hz hz1
    calc d * (e * z₀ * e⁻¹) * d⁻¹ = e * (d * z₀ * d⁻¹) * e⁻¹ := by
          rw [show d * (e * z₀ * e⁻¹) * d⁻¹ = (d * e) * z₀ * (d * e)⁻¹ by group,
            hDcomm d hd e he]
          group
      _ = e * (d' * z₀ * d'⁻¹) * e⁻¹ := by rw [h]
      _ = d' * (e * z₀ * e⁻¹) * d'⁻¹ := by
          rw [show e * (d' * z₀ * d'⁻¹) * e⁻¹ = (e * d') * z₀ * (e * d')⁻¹ by group,
            hDcomm e he d' hd']
          group
  have hpow : ∀ a ∈ normalizer ((R : Subgroup Q) : Set Q),
      ∀ b ∈ normalizer ((R : Subgroup Q) : Set Q), (∀ z ∈ Z, a * z * a⁻¹ = b * z * b⁻¹) →
        ∀ m : ℕ, ∀ z ∈ Z, a ^ m * z * (a ^ m)⁻¹ = b ^ m * z * (b ^ m)⁻¹ := by
    intro a ha b hb h m
    induction m with
    | zero => intro z hz; simp
    | succ m ih =>
      intro z hz
      have hbz : b ^ m * z * (b ^ m)⁻¹ ∈ Z := hZN (b ^ m) (pow_mem hb m) z hz
      calc a ^ (m + 1) * z * (a ^ (m + 1))⁻¹ = a * (a ^ m * z * (a ^ m)⁻¹) * a⁻¹ := by group
        _ = a * (b ^ m * z * (b ^ m)⁻¹) * a⁻¹ := by rw [ih z hz]
        _ = b * (b ^ m * z * (b ^ m)⁻¹) * b⁻¹ := h _ hbz
        _ = b ^ (m + 1) * z * (b ^ (m + 1))⁻¹ := by group
  obtain ⟨⟨d₀, hd₀D⟩, hgen⟩ := IsCyclic.exists_generator (α := D)
  have hpowD : ∀ d ∈ D, ∃ m : ℕ, d₀ ^ m = d := by
    intro d hd
    have h1 := hgen ⟨d, hd⟩
    rw [← mem_powers_iff_mem_zpowers] at h1
    obtain ⟨m, hm⟩ := h1
    exact ⟨m, congrArg Subtype.val hm⟩
  have hd₀N : d₀ ∈ normalizer ((R : Subgroup Q) : Set Q) := hDN hd₀D
  have hkey : ∀ t t' : T, (∀ z ∈ Z, σ t d₀ * z * (σ t d₀)⁻¹ = σ t' d₀ * z * (σ t' d₀)⁻¹) →
      t⁻¹ * t' ∈ F := by
    intro t t' h
    set γ := σ (t⁻¹ * t') with hγdef
    have hγ : γ = (σ t)⁻¹ * σ t' := by rw [hγdef, map_mul, map_inv]
    have hγd : ∀ z ∈ Z, γ d₀ * z * (γ d₀)⁻¹ = d₀ * z * d₀⁻¹ := by
      intro z hz
      apply (σ t).injective
      have h1 : σ t (γ d₀) = σ t' d₀ := by
        rw [hγ, MulAut.mul_apply, MulAut.apply_inv_self]
      rw [map_mul, map_mul, map_inv, h1, map_mul, map_mul, map_inv, h (σ t z) (hσZ t z hz)]
    have hγD : ∀ d ∈ D, ∀ z ∈ Z, γ d * z * (γ d)⁻¹ = d * z * d⁻¹ := by
      intro d hd z hz
      obtain ⟨m, rfl⟩ := hpowD d hd
      rw [map_pow]
      exact hpow (γ d₀) (hσN _ d₀ hd₀N) d₀ hd₀N hγd m z hz
    have hγz₀ : γ z₀ ∈ Z := hσZ _ z₀ hz₀
    have hγz₀1 : γ z₀ ≠ 1 := by
      intro h1
      apply hz₀1
      apply γ.injective
      rw [h1, map_one]
    obtain ⟨e, he, hez₀⟩ := htrans z₀ hz₀ hz₀1 (γ z₀) hγz₀ hγz₀1
    have hez : ∀ z ∈ Z, γ z = e * z * e⁻¹ := by
      intro z hz
      by_cases hz1 : z = 1
      · rw [hz1, map_one]
        group
      obtain ⟨d, hd, rfl⟩ := htrans z₀ hz₀ hz₀1 z hz hz1
      rw [map_mul, map_mul, map_inv, hγD d hd (γ z₀) hγz₀, ← hez₀,
        show d * (e * z₀ * e⁻¹) * d⁻¹ = (d * e) * z₀ * (d * e)⁻¹ by group, hDcomm d hd e he]
      group
    obtain ⟨n, hn⟩ := hT (t⁻¹ * t')
    have hγn : γ ^ 2 ^ n = 1 := by rw [hγdef, ← map_pow, hn, map_one]
    have hγm : ∀ m : ℕ, ∀ z ∈ Z, (γ ^ m) z = e ^ m * z * (e ^ m)⁻¹ := by
      intro m
      induction m with
      | zero => intro z hz; simp
      | succ m ih =>
        intro z hz
        rw [pow_succ', MulAut.mul_apply, ih z hz,
          hez _ (hZN (e ^ m) (pow_mem (hDN he) m) z hz)]
        group
    have heZ : ∀ z ∈ Z, e ^ 2 ^ n * z = z * e ^ 2 ^ n := by
      intro z hz
      have h1 := hγm (2 ^ n) z hz
      rw [hγn, MulAut.one_apply] at h1
      calc e ^ 2 ^ n * z = (e ^ 2 ^ n * z * (e ^ 2 ^ n)⁻¹) * e ^ 2 ^ n := by group
        _ = z * e ^ 2 ^ n := by rw [← h1]
    have hcop : Nat.Coprime (2 ^ n) (orderOf e) := by
      apply Nat.Coprime.pow_left
      rw [Nat.coprime_two_left]
      have h1 : orderOf e ∣ Nat.card D := by
        have := orderOf_dvd_natCard (⟨e, he⟩ : D)
        rwa [Subgroup.orderOf_mk] at this
      exact hDodd.of_dvd_nat h1
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [hmemF]
    intro z hz
    rw [hez z hz]
    have h2 : e * z = z * e := by
      rw [← hm]
      exact Commute.pow_left (heZ z hz) m
    rw [h2, mul_inv_cancel_right]
  have hΨZ : ∀ t : T, σ t d₀ * z₀ * (σ t d₀)⁻¹ ∈ Z := fun t => hZN _ (hσN t d₀ hd₀N) z₀ hz₀
  have hΨ1 : ∀ t : T, σ t d₀ * z₀ * (σ t d₀)⁻¹ ≠ 1 := fun t h => hz₀1 (by
    have h1 := congrArg (fun x => (σ t d₀)⁻¹ * x * σ t d₀) h
    simpa [mul_assoc] using h1)
  have hiff : ∀ t t' : T,
      σ t d₀ * z₀ * (σ t d₀)⁻¹ = σ t' d₀ * z₀ * (σ t' d₀)⁻¹ ↔ t⁻¹ * t' ∈ F := by
    intro t t'
    constructor
    · intro h
      apply hkey
      obtain ⟨a, ha, hac⟩ := hact _ (hσN t d₀ hd₀N)
      obtain ⟨b, hb, hbc⟩ := hact _ (hσN t' d₀ hd₀N)
      intro z hz
      rw [hac z hz, hbc z hz]
      exact hreg a ha b hb (by rw [← hac z₀ hz₀, ← hbc z₀ hz₀]; exact h) z hz
    · intro h
      rw [hmemF] at h
      set γ := σ (t⁻¹ * t') with hγdef
      have h1 : σ t' = σ t * γ := by rw [hγdef, ← map_mul, mul_inv_cancel_left]
      set w := (σ t)⁻¹ z₀ with hw
      have hwZ : w ∈ Z := by
        rw [hw, ← map_inv]
        exact hσZ t⁻¹ z₀ hz₀
      have hz₀w : z₀ = σ t w := by rw [hw, MulAut.apply_inv_self]
      have hγw : γ d₀ * w * (γ d₀)⁻¹ = d₀ * w * d₀⁻¹ := by
        have e1 := h (d₀ * w * d₀⁻¹) (hZN d₀ hd₀N w hwZ)
        rw [map_mul, map_mul, map_inv, h w hwZ] at e1
        exact e1
      have hL : σ t d₀ * z₀ * (σ t d₀)⁻¹ = σ t (d₀ * w * d₀⁻¹) := by
        rw [hz₀w, map_mul, map_mul, map_inv]
      have hR : σ t' d₀ * z₀ * (σ t' d₀)⁻¹ = σ t (γ d₀ * w * (γ d₀)⁻¹) := by
        rw [hz₀w, h1, MulAut.mul_apply, map_mul, map_mul, map_inv]
      rw [hL, hR, hγw]
  let Ψ : T ⧸ F → {z : Z // z ≠ 1} := Quotient.lift
    (fun t => ⟨⟨_, hΨZ t⟩, fun h => hΨ1 t (congrArg Subtype.val h)⟩)
    (fun a b hab => Subtype.ext (Subtype.ext ((hiff a b).mpr (QuotientGroup.leftRel_apply.mp hab))))
  have hΨinj : Function.Injective Ψ := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    apply QuotientGroup.eq.mpr
    apply (hiff a b).mp
    exact congrArg (fun u : {z : Z // z ≠ 1} => ((u.1 : Z) : Q)) hxy
  have h1 := Nat.card_le_card_of_injective Ψ hΨinj
  have h2 : Nat.card {z : Z // z ≠ 1} = q - 1 := by
    have : Fintype Z := Fintype.ofFinite _
    rw [← hZcard, Nat.card_eq_fintype_card (α := Z)]
    rw [← Set.card_ne_eq (1 : Z), ← Nat.card_eq_fintype_card]
    rfl
  calc Nat.card T = Nat.card (T ⧸ F) * Nat.card F := F.card_eq_card_quotient_mul_card_subgroup
    _ ≤ (q - 1) * Nat.card F := Nat.mul_le_mul_right _ (h1.trans h2.le)

end CFSG.ComponentClassification.GMS78
