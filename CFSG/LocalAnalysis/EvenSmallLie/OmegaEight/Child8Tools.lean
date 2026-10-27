module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.PGroupNormalizerExtension
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.EvenSmallLie.OmegaEight.Child8

open Subgroup

section Coord

variable {G A : Type*} [Group G] [AddZeroClass A] (ι : Multiplicative A →* G)

theorem conj_mem_range_of_mem_normalizer {n : G} (hn : n ∈ normalizer (Set.range ι))
    (v : Multiplicative A) : n * ι v * n⁻¹ ∈ Set.range ι :=
  (mem_set_normalizer_iff.1 hn (ι v)).1 ⟨v, rfl⟩

@[expose] noncomputable def coordConj (n : normalizer (Set.range ι)) (v : A) : A :=
  Multiplicative.toAdd
    (Classical.choose (conj_mem_range_of_mem_normalizer ι n.2 (Multiplicative.ofAdd v)))

theorem coordConj_spec (n : normalizer (Set.range ι)) (v : A) :
    ι (Multiplicative.ofAdd (coordConj ι n v)) = n * ι (Multiplicative.ofAdd v) * (n : G)⁻¹ :=
  Classical.choose_spec (conj_mem_range_of_mem_normalizer ι n.2 (Multiplicative.ofAdd v))

variable {ι}

theorem coordConj_add (hι : Function.Injective ι) (n : normalizer (Set.range ι)) (x y : A) :
    coordConj ι n (x + y) = coordConj ι n x + coordConj ι n y := by
  apply hι
  change ι (Multiplicative.ofAdd (coordConj ι n (x + y))) =
    ι (Multiplicative.ofAdd (coordConj ι n x) * Multiplicative.ofAdd (coordConj ι n y))
  rw [map_mul, coordConj_spec, coordConj_spec, coordConj_spec, ofAdd_add, map_mul]
  group

variable (ι)

@[expose, instance_reducible] noncomputable def coordAction (hι : Function.Injective ι) :
    MulAction (normalizer (Set.range ι)) A where
  smul := coordConj ι
  one_smul v := hι (by
    change ι (Multiplicative.ofAdd (coordConj ι 1 v)) = ι (Multiplicative.ofAdd v)
    rw [coordConj_spec]
    simp)
  mul_smul m n v := hι (by
    change ι (Multiplicative.ofAdd (coordConj ι (m * n) v)) =
      ι (Multiplicative.ofAdd (coordConj ι m (coordConj ι n v)))
    rw [coordConj_spec, coordConj_spec, coordConj_spec]
    simp only [coe_mul, mul_inv_rev]
    group)

end Coord

section Sylow

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_sylow_eq_of_normalizer_le {P H : Subgroup G} (hP : IsPGroup p P)
    (hmax : ∀ Q : Subgroup G, IsPGroup p Q → P ≤ Q → Q ≤ H → Q = P)
    (hN : normalizer (P : Set G) ≤ H) : ∃ S : Sylow p G, (S : Subgroup G) = P := by
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  refine ⟨S, ?_⟩
  by_contra hne
  obtain ⟨U, hPU, hU, hUS⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.pgroup_strict_normalizer_extension p P S
      S.isPGroup' (lt_of_le_of_ne hPS (Ne.symm hne))
  exact hPU.ne (hmax U hU hPU.le ((hUS.trans inf_le_right).trans hN)).symm

theorem eq_of_card_of_le {P H Q : Subgroup G} {a m : ℕ} (hP : Nat.card P = p ^ a)
    (hH : Nat.card H = p ^ a * m) (hm : ¬ p ∣ m) (hQ : IsPGroup p Q) (hPQ : P ≤ Q)
    (hQH : Q ≤ H) : Q = P := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hQ
  have hdvd : p ^ b ∣ p ^ a * m := hb ▸ hH ▸ card_dvd_of_le hQH
  have hcop : Nat.Coprime (p ^ b) m :=
    Nat.Coprime.pow_left b ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  have hdvd' : p ^ b ∣ p ^ a := hcop.dvd_of_dvd_mul_right hdvd
  refine (eq_of_le_of_card_ge hPQ ?_).symm
  rw [hb, hP]
  exact Nat.le_of_dvd (pow_pos hp.pos a) hdvd'

end Sylow

theorem conj_mem_of_two_mul_card_eq {G : Type*} [Group G] {N T : Subgroup G} [Finite T]
    (hNT : N ≤ T) (hcard : Nat.card T = 2 * Nat.card N) {t : G} (ht : t ∈ T) {n : G}
    (hn : n ∈ N) : t * n * t⁻¹ ∈ N := by
  have hpos : 0 < Nat.card N := by
    have := Nat.card_pos (α := T)
    omega
  have hrel : N.relIndex T = 2 := by
    have h := relIndex_mul_card N T
    rw [inf_of_le_left hNT, hcard] at h
    exact Nat.eq_of_mul_eq_mul_right hpos h
  have hnorm : (N.subgroupOf T).Normal := normal_of_index_eq_two hrel
  have h := hnorm.conj_mem ⟨n, hNT hn⟩ (by rwa [mem_subgroupOf]) ⟨t, ht⟩
  rwa [mem_subgroupOf] at h

section UCore

variable {G : Type*} [Group G]

theorem inf_centralizer_mul_eq {E : Subgroup G} (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    {c e : G} (he : e ∈ E) :
    E ⊓ centralizer ({c * e} : Set G) = E ⊓ centralizer ({c} : Set G) := by
  ext a
  simp only [mem_inf, mem_centralizer_singleton_iff]
  refine and_congr_right fun ha => ?_
  have h1 : c * e * a = c * a * e := by rw [mul_assoc, ← hE a ha e he, ← mul_assoc]
  rw [h1, ← mul_assoc]
  exact mul_left_inj e

theorem card_inf_centralizer_conj {E : Subgroup G} {d : G} (hd : d ∈ normalizer (E : Set G))
    (c : G) : Nat.card (E ⊓ centralizer ({d * c * d⁻¹} : Set G) : Subgroup G) =
      Nat.card (E ⊓ centralizer ({c} : Set G) : Subgroup G) := by
  have hmap : (E ⊓ centralizer ({c} : Set G)).map (MulAut.conj d).toMonoidHom =
      E ⊓ centralizer ({d * c * d⁻¹} : Set G) := by
    ext x
    rw [mem_map_equiv, mem_inf, mem_inf, mem_centralizer_singleton_iff,
      mem_centralizer_singleton_iff]
    have hsymm : (MulAut.conj d).symm x = d⁻¹ * x * d := by
      rw [MulAut.conj_symm_apply]
    rw [hsymm]
    have hEx : d⁻¹ * x * d ∈ E ↔ x ∈ E := by
      rw [mem_normalizer_iff.1 hd (d⁻¹ * x * d)]
      simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
    rw [hEx]
    refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
    · calc x * (d * c * d⁻¹) = d * (d⁻¹ * x * d * c) * d⁻¹ := by group
        _ = d * (c * (d⁻¹ * x * d)) * d⁻¹ := by rw [h]
        _ = d * c * d⁻¹ * x := by group
    · calc d⁻¹ * x * d * c = d⁻¹ * (x * (d * c * d⁻¹)) * d := by group
        _ = d⁻¹ * (d * c * d⁻¹ * x) * d := by rw [h]
        _ = c * (d⁻¹ * x * d) := by group
  rw [← hmap, card_map_of_injective (MulAut.conj d).injective]

theorem conj_pow_succ (d x : G) (k : ℕ) :
    d ^ (k + 1) * x * (d ^ (k + 1))⁻¹ = d * (d ^ k * x * (d ^ k)⁻¹) * d⁻¹ := by
  rw [pow_succ']
  group

theorem conj_eq_of_odd_of_zc {C E : Subgroup G} {s₁ s₂ x₀ d : G} {U : Set G}
    (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hs₁ : s₁ ∈ C) (hs₂ : s₂ ∈ C)
    (hz₁ : ∀ c ∈ C, s₁ * c * s₁⁻¹ * c⁻¹ ∈ E) (hz₂ : ∀ c ∈ C, s₂ * c * s₂⁻¹ * c⁻¹ ∈ E)
    (hzc : ∀ c ∈ C, (∀ c' ∈ C, c * c' * c⁻¹ * c'⁻¹ ∈ E) →
      c ∈ E ∨ s₁⁻¹ * c ∈ E ∨ s₂⁻¹ * c ∈ E ∨ (s₁ * s₂)⁻¹ * c ∈ E)
    (hs₁E : s₁ ∉ E) (hs₂E : s₂ ∉ E) (h12 : s₁⁻¹ * s₂ ∉ E)
    (hk₁ : Nat.card (E ⊓ centralizer ({s₁} : Set G) : Subgroup G) ≠
      Nat.card (E ⊓ centralizer ({s₁ * s₂} : Set G) : Subgroup G))
    (hk₂ : Nat.card (E ⊓ centralizer ({s₂} : Set G) : Subgroup G) ≠
      Nat.card (E ⊓ centralizer ({s₁ * s₂} : Set G) : Subgroup G))
    (hx₀ : ∃ e ∈ E, e * s₁ * e⁻¹ * s₁⁻¹ = x₀)
    (hU : ∀ e ∈ E, e * s₁ * e⁻¹ * s₁⁻¹ ∈ U →
      e * s₁ * e⁻¹ * s₁⁻¹ = 1 ∨ e * s₁ * e⁻¹ * s₁⁻¹ = x₀)
    (hx₀U : x₀ ∈ U) (hx₀1 : x₀ ≠ 1)
    (hdC : d ∈ normalizer (C : Set G)) (hdE : d ∈ normalizer (E : Set G))
    (hdU : ∀ u ∈ U, d * u * d⁻¹ ∈ U) {m : ℕ} (hm : Odd m) (hdm : d ^ m = 1) :
    d * x₀ * d⁻¹ = x₀ := by
  have hEd : ∀ e ∈ E, d * e * d⁻¹ ∈ E := fun e he => (mem_normalizer_iff.1 hdE e).1 he
  have hEd' : ∀ e, d * e * d⁻¹ ∈ E → e ∈ E := fun e he => (mem_normalizer_iff.1 hdE e).2 he
  have hCd : ∀ c ∈ C, d * c * d⁻¹ ∈ C := fun c hc => (mem_normalizer_iff.1 hdC c).1 hc
  have hCd' : ∀ c ∈ C, d⁻¹ * c * d ∈ C := fun c hc =>
    (mem_normalizer_iff.1 hdC (d⁻¹ * c * d)).2 (by simpa [mul_assoc] using hc)
  have hzcd : ∀ s ∈ C, (∀ c ∈ C, s * c * s⁻¹ * c⁻¹ ∈ E) →
      ∀ c ∈ C, d * s * d⁻¹ * c * (d * s * d⁻¹)⁻¹ * c⁻¹ ∈ E := by
    intro s _ hz c hc
    have h := hEd _ (hz _ (hCd' c hc))
    convert h using 1
    group
  have hκe : ∀ c e, e ∈ E → Nat.card (E ⊓ centralizer ({c * e} : Set G) : Subgroup G) =
      Nat.card (E ⊓ centralizer ({c} : Set G) : Subgroup G) := fun c e he => by
    rw [inf_centralizer_mul_eq hE he]
  have hcls : ∀ s ∈ C, (∀ c ∈ C, s * c * s⁻¹ * c⁻¹ ∈ E) → s ∉ E →
      Nat.card (E ⊓ centralizer ({s} : Set G) : Subgroup G) ≠
        Nat.card (E ⊓ centralizer ({s₁ * s₂} : Set G) : Subgroup G) →
      s₁⁻¹ * (d * s * d⁻¹) ∈ E ∨ s₂⁻¹ * (d * s * d⁻¹) ∈ E := by
    intro s hs hz hsE hκ
    rcases hzc _ (hCd s hs) (hzcd s hs hz) with h | h | h | h
    · exact absurd (hEd' s h) hsE
    · exact Or.inl h
    · exact Or.inr h
    · refine absurd ?_ hκ
      rw [← card_inf_centralizer_conj hdE s]
      have h' : d * s * d⁻¹ = s₁ * s₂ * ((s₁ * s₂)⁻¹ * (d * s * d⁻¹)) := by group
      rw [h', hκe _ _ h]
  have h1 := hcls s₁ hs₁ hz₁ hs₁E hk₁
  have h2 := hcls s₂ hs₂ hz₂ hs₂E hk₂
  have hfix : s₁⁻¹ * (d * s₁ * d⁻¹) ∈ E → d * x₀ * d⁻¹ = x₀ := by
    intro he₀
    obtain ⟨e, he, rfl⟩ := hx₀
    have he' : d * e * d⁻¹ ∈ E := hEd e he
    have key : d * (e * s₁ * e⁻¹ * s₁⁻¹) * d⁻¹ =
        d * e * d⁻¹ * s₁ * (d * e * d⁻¹)⁻¹ * s₁⁻¹ := by
      have hc := hE _ he₀ _ (inv_mem he')
      calc d * (e * s₁ * e⁻¹ * s₁⁻¹) * d⁻¹ =
            d * e * d⁻¹ * s₁ * ((s₁⁻¹ * (d * s₁ * d⁻¹)) * (d * e * d⁻¹)⁻¹) *
              (s₁⁻¹ * (d * s₁ * d⁻¹))⁻¹ * s₁⁻¹ := by group
        _ = d * e * d⁻¹ * s₁ * ((d * e * d⁻¹)⁻¹ * (s₁⁻¹ * (d * s₁ * d⁻¹))) *
              (s₁⁻¹ * (d * s₁ * d⁻¹))⁻¹ * s₁⁻¹ := by rw [hc]
        _ = d * e * d⁻¹ * s₁ * (d * e * d⁻¹)⁻¹ * s₁⁻¹ := by group
    have hmemU := hdU _ hx₀U
    rw [key] at hmemU
    rcases hU _ he' hmemU with h | h
    · rw [← key] at h
      exact absurd (by simpa using h) hx₀1
    · rw [key, h]
  rcases h1 with h1 | h1
  · exact hfix h1
  exfalso
  rcases h2 with h2 | h2
  · have step₁ : ∀ x, s₁⁻¹ * x ∈ E → s₂⁻¹ * (d * x * d⁻¹) ∈ E := by
      intro x hx
      have h' : s₂⁻¹ * (d * x * d⁻¹) = s₂⁻¹ * (d * s₁ * d⁻¹) * (d * (s₁⁻¹ * x) * d⁻¹) := by
        group
      rw [h']
      exact mul_mem h1 (hEd _ hx)
    have step₂ : ∀ x, s₂⁻¹ * x ∈ E → s₁⁻¹ * (d * x * d⁻¹) ∈ E := by
      intro x hx
      have h' : s₁⁻¹ * (d * x * d⁻¹) = s₁⁻¹ * (d * s₂ * d⁻¹) * (d * (s₂⁻¹ * x) * d⁻¹) := by
        group
      rw [h']
      exact mul_mem h2 (hEd _ hx)
    have hind : ∀ k : ℕ, s₁⁻¹ * (d ^ (2 * k) * s₁ * (d ^ (2 * k))⁻¹) ∈ E := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have h' := step₂ _ (step₁ _ ih)
        rwa [← conj_pow_succ, ← conj_pow_succ] at h'
    obtain ⟨k, rfl⟩ := hm
    have h' := step₁ _ (hind k)
    rw [← conj_pow_succ, hdm] at h'
    simp only [one_mul, inv_one, mul_one] at h'
    exact h12 (by simpa using inv_mem h')
  · apply h12
    have h' : (s₂⁻¹ * (d * s₂ * d⁻¹))⁻¹ * (s₂⁻¹ * (d * s₁ * d⁻¹)) ∈ E :=
      mul_mem (inv_mem h2) h1
    have h'' : d * (s₂⁻¹ * s₁) * d⁻¹ ∈ E := by
      convert h' using 1
      group
    simpa using inv_mem (hEd' _ h'')

theorem conj_pow_two_pow_ne {n x y₁ y₂ : G} (h1 : n * x * n⁻¹ = y₁) (h2 : n * y₁ * n⁻¹ = y₂)
    (h3 : n * y₂ * n⁻¹ = x) (hy₁ : y₁ ≠ x) (hy₂ : y₂ ≠ x) (a : ℕ) :
    n ^ 2 ^ a * x * (n ^ 2 ^ a)⁻¹ ≠ x := by
  have h3' : ∀ k : ℕ, n ^ (k + 3) * x * (n ^ (k + 3))⁻¹ = n ^ k * x * (n ^ k)⁻¹ := by
    intro k
    have : n ^ (k + 3) * x * (n ^ (k + 3))⁻¹ =
        n ^ k * (n * (n * (n * x * n⁻¹) * n⁻¹) * n⁻¹) * (n ^ k)⁻¹ := by
      rw [pow_add]
      group
    rw [this, h1, h2, h3]
  have hmod : ∀ q r : ℕ, n ^ (r + 3 * q) * x * (n ^ (r + 3 * q))⁻¹ = n ^ r * x * (n ^ r)⁻¹ := by
    intro q r
    induction q with
    | zero => simp
    | succ q ih => rw [show r + 3 * (q + 1) = r + 3 * q + 3 by ring, h3', ih]
  have h2a : 2 ^ a % 3 = 1 ∨ 2 ^ a % 3 = 2 := by
    induction a with
    | zero => left; rfl
    | succ a ih => rw [pow_succ]; omega
  rw [← Nat.mod_add_div (2 ^ a) 3, hmod]
  rcases h2a with h | h
  · rw [h, pow_one, h1]
    exact hy₁
  · rw [h, pow_two, show n * n * x * (n * n)⁻¹ = n * (n * x * n⁻¹) * n⁻¹ by group, h1, h2]
    exact hy₂

theorem exists_pow_two_pow_odd [Finite G] (n : G) :
    ∃ a m : ℕ, Odd m ∧ (n ^ 2 ^ a) ^ m = 1 := by
  obtain ⟨a, m, hm, h⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  exact ⟨a, m, hm, by rw [← pow_mul, ← h, pow_orderOf_eq_one]⟩

end UCore

section Transport

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conj_mem [Finite G] {S : Set G} {g : G}
    (h : ∀ x ∈ S, g * x * g⁻¹ ∈ S) : g ∈ normalizer S := by
  rw [mem_set_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  set f : S → S := fun y => ⟨g * y * g⁻¹, h y y.2⟩
  have hf : Function.Injective f := fun a b hab => by
    have h1 := congrArg Subtype.val hab
    simp only [f, mul_left_inj, mul_right_inj] at h1
    exact Subtype.ext h1
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hf) ⟨_, hx⟩
  have h1 := congrArg Subtype.val hy
  simp only [f, mul_left_inj, mul_right_inj] at h1
  exact h1 ▸ y.2

variable {X : Type*} [Group X] {ψ : X →* G}

theorem card_comap_of_le_range (hψ : Function.Injective ψ) {B : Subgroup G}
    (hB : B ≤ ψ.range) : Nat.card (B.comap ψ) = Nat.card B := by
  rw [← card_map_of_injective hψ, map_comap_eq_self hB]

theorem comap_le_of_le_map (hψ : Function.Injective ψ) {B : Subgroup G} {T : Subgroup X}
    (hB : B ≤ T.map ψ) : B.comap ψ ≤ T := by
  intro x hx
  obtain ⟨t, ht, htx⟩ := hB hx
  rwa [← hψ htx]

theorem mem_of_map_mem (hψ : Function.Injective ψ) {T : Subgroup X} {x : X}
    (hx : ψ x ∈ T.map ψ) : x ∈ T := by
  obtain ⟨t, ht, htx⟩ := hx
  rwa [← hψ htx]

theorem card_range_of_injective (hψ : Function.Injective ψ) : Nat.card ψ.range = Nat.card X :=
  (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm

end Transport

end CFSG.EvenSmallLie.OmegaEight.Child8
