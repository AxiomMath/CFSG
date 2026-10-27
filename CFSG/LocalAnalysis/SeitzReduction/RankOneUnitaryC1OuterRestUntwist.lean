module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterRestBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1OuterConf

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D V : Subgroup G} {k : ℕ}

theorem outerRestPt_pow_of_conj
    (hcf : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k) {x : G}
    (hx : x ∈ normalizer (szR (szT₁ L T) V t : Set G))
    (hxA : ∀ b ∈ szA₁ (szT₁ L T), x * b * x⁻¹ = b) :
    ∀ n : ℕ, outerRestPt t k (x ^ n) = outerRestPt t k x ^ n := by
  intro n
  induction n with
  | zero => rw [pow_zero, pow_zero, outerRestPt_of_comm (by rw [one_mul, mul_one])]
  | succ n ih =>
    rw [pow_succ', hcf.outerRestPt_mul_of_conj h hS2 hk hx (pow_mem hx n) hxA, ih, pow_succ]

section Untwist


theorem outerRest_exists_u3C1U_of_transitive (hcf : U3C1OuterConf G L f t T R₂ D V k)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hk : 2 ≤ k) {d : G} (hC : U3C1Cartan L T D d)
    (htr : ∀ b ∈ szA₁ (szT₁ L T), ∃ x ∈ normalizer (szR (szT₁ L T) V t : Set G) ⊓
      centralizer (szA₁ (szT₁ L T) : Set G), outerRestPt t k x = b) :
    ∀ b ∈ szA₁ (szT₁ L T), ∃ x ∈ u3C1U L T V t, outerRestPt t k x = b := by
  classical
  obtain ⟨E', _, _, _, σ, hEcard, hσ, hfix, u, v, hc, hA₁u, -, -⟩ :=
    h.exists_rootCoords_scalar_of_card_sylow hS2
  have : Fintype E' := Fintype.ofFinite E'
  obtain ⟨-, hA₁card, -, -, -, hsqA₁, -⟩ := h.facts_of_card_sylow hS2
  have hf1 : 1 ≤ f := by have := h.two_le; omega
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ : E', σ μ ≠ μ := by
    by_contra hall
    push Not at hall
    have h1 : Nat.card {x : E' // σ x = x} = Nat.card E' :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hall)
    rw [hfix, hEcard] at h1
    have h2 : 2 ^ f < (2 ^ f) ^ 2 := by
      have : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
      nlinarith
    omega
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    rw [hσ, hσ, ← pow_mul, ← sq]
    have h1 : x ^ Fintype.card E' = x := FiniteField.pow_card x
    rwa [← Nat.card_eq_fintype_card, hEcard] at h1
  set Y := normalizer (szR (szT₁ L T) V t : Set G) with hYdef
  set A₁ := szA₁ (szT₁ L T) with hA₁def
  set T₁ := szT₁ L T with hT₁def
  set X := Y ⊓ centralizer (A₁ : Set G) with hXdef
  have hXY : ∀ x ∈ X, x ∈ Y := fun x hx => (mem_inf.mp hx).1
  have hXT : ∀ x ∈ X, x ∈ normalizer (T₁ : Set G) := fun x hx =>
    (hcf.normalizer_szR_le h hS2 hk (hXY x hx)).2.2.1
  have hXA : ∀ x ∈ X, ∀ a ∈ A₁, x * a * x⁻¹ = a := fun x hx a ha => by
    rw [← mem_centralizer_iff.mp (mem_inf.mp hx).2 a ha, mul_inv_cancel_right]
  have hconjT : ∀ x ∈ X, ∀ y ∈ T₁, x * y * x⁻¹ ∈ T₁ := fun x hx y hy =>
    (mem_normalizer_iff.mp (hXT x hx) y).mp hy
  have hconjT' : ∀ x ∈ X, ∀ y ∈ T₁, x⁻¹ * y * x ∈ T₁ := fun x hx y hy =>
    (mem_normalizer_iff''.mp (hXT x hx) y).mp hy
  have hπmul : ∀ x ∈ X, ∀ x' ∈ X, outerRestPt t k (x * x') =
      outerRestPt t k x' * outerRestPt t k x := fun x hx x' hx' =>
    hcf.outerRestPt_mul_of_conj h hS2 hk (hXY x hx) (hXY x' hx') (hXA x hx)
  have hπmem : ∀ x ∈ X, outerRestPt t k x ∈ A₁ := fun x hx =>
    hcf.outerRestPt_mem h hS2 hk (hXY x hx)
  have hA₁comm : ∀ a ∈ A₁, ∀ b ∈ A₁, a * b = b * a := fun a ha b hb =>
    mem_centralizer_iff.mp (mem_szA₁.mp hb).2 a (szA₁_le _ ha)
  have hπinv : ∀ x ∈ X, outerRestPt t k x⁻¹ = (outerRestPt t k x)⁻¹ := by
    intro x hx
    have e := hπmul x hx x⁻¹ (inv_mem hx)
    rw [mul_inv_cancel, outerRestPt_of_comm (by rw [one_mul, mul_one])] at e
    exact (eq_inv_of_mul_eq_one_left e.symm)
  have hdich : ∀ x ∈ X, ∃ l : E', l * σ l = 1 ∧ ((∀ y ∈ T₁, u (x * y * x⁻¹) = l * u y) ∨
      (∀ y ∈ T₁, u (x * y * x⁻¹) = l * σ (u y))) := fun x hx =>
    hc.exists_norm_one hμ₀ (hXT x hx) fun y hy hu => hXA x hx y ((hA₁u y hy).mpr hu)
  have hne0 : ∀ l : E', l * σ l = 1 → l ≠ 0 := fun l hl h0 => by
    rw [h0, zero_mul] at hl; exact zero_ne_one hl
  obtain ⟨y₁, hy₁, hu₁⟩ := hc.u_surj 1
  obtain ⟨y₂, hy₂, hu₂⟩ := hc.u_surj μ₀
  have hnorm : ∀ x ∈ X, ∀ l : E', (∀ y ∈ T₁, u (x * y * x⁻¹) = l * u y) → l * σ l = 1 := by
    intro x hx l hl
    obtain ⟨l₀, hl₀, hl₀x | hl₀x⟩ := hdich x hx
    · have := (hl y₁ hy₁).symm.trans (hl₀x y₁ hy₁)
      rw [hu₁, mul_one, mul_one] at this
      rwa [this]
    · exfalso
      have h1 := (hl y₁ hy₁).symm.trans (hl₀x y₁ hy₁)
      rw [hu₁, map_one, mul_one, mul_one] at h1
      have h2 := (hl y₂ hy₂).symm.trans (hl₀x y₂ hy₂)
      rw [hu₂, ← h1] at h2
      exact hμ₀ (mul_left_cancel₀ (hne0 l (h1 ▸ hl₀)) h2).symm
  have hdD := hC.mem
  have hdL : d ∈ L := hC.le hdD
  have hdt : d * t = t * d := mem_centralizer_iff.mp h.mem d hdL
  have hdT : d ∈ normalizer (T₁ : Set G) := hC.le_normalizer hdD
  have hdY : d ∈ Y := mem_normalizer_szR_of hdT (hcf.D_le hdD) hdt
  have hdA : d ∈ normalizer (A₁ : Set G) := normalizer_le_normalizer_inf_centralizer _ hdT
  have hdX : ∀ x ∈ X, d⁻¹ * x * d ∈ X := by
    intro x hx
    refine mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hdY) (hXY x hx)) hdY,
      mem_centralizer_iff.mpr fun a ha => ?_⟩
    have ha' : d * a * d⁻¹ ∈ A₁ := (mem_normalizer_iff.mp hdA a).mp ha
    have h1 := hXA x hx _ ha'
    have h2 : (d * a * d⁻¹) * x = x * (d * a * d⁻¹) := by
      calc (d * a * d⁻¹) * x = (x * (d * a * d⁻¹) * x⁻¹) * x := by rw [h1]
        _ = x * (d * a * d⁻¹) := by group
    calc a * (d⁻¹ * x * d) = d⁻¹ * ((d * a * d⁻¹) * x) * d := by group
      _ = d⁻¹ * (x * (d * a * d⁻¹)) * d := by rw [h2]
      _ = (d⁻¹ * x * d) * a := by group
  have hπd1 : outerRestPt t k d = 1 := outerRestPt_of_comm hdt
  have hπd2 : outerRestPt t k d⁻¹ = 1 := outerRestPt_of_comm (Commute.inv_left hdt).eq
  have hπd : ∀ x ∈ X, outerRestPt t k (d⁻¹ * x * d) = d⁻¹ * outerRestPt t k x * d := by
    intro x hx
    rw [mul_assoc, hcf.outerRestPt_mul h hS2 hk (inv_mem hdY) (mul_mem (hXY x hx) hdY),
      hcf.outerRestPt_mul h hS2 hk (hXY x hx) hdY, hπd1, hπd2]
    group
  set P : G → Prop := fun b => ∃ x ∈ X, (∃ l : E', ∀ y ∈ T₁, u (x * y * x⁻¹) = l * u y) ∧
    outerRestPt t k x = b with hPdef
  have hP1 : P 1 := ⟨1, one_mem _, ⟨1, fun y _ => by simp⟩,
    outerRestPt_of_comm (by rw [one_mul, mul_one])⟩
  have hP2 : ∀ b b', P b → P b' → P (b' * b) := by
    rintro b b' ⟨x, hx, ⟨l, hl⟩, rfl⟩ ⟨x', hx', ⟨l', hl'⟩, rfl⟩
    refine ⟨x * x', mul_mem hx hx', ⟨l * l', fun y hy => ?_⟩, hπmul x hx x' hx'⟩
    rw [show x * x' * y * (x * x')⁻¹ = x * (x' * y * x'⁻¹) * x⁻¹ by group,
      hl _ (hconjT x' hx' y hy), hl' y hy, mul_assoc]
  have triv_iff : ∀ {z : G}, z ∈ normalizer (T₁ : Set G) →
      ((∀ y ∈ T₁, y⁻¹ * (z * y * z⁻¹) ∈ A₁) ↔ ∀ y ∈ T₁, u (z * y * z⁻¹) = u y) := by
    intro z hzT
    constructor
    · intro h' y hy
      have hzy : z * y * z⁻¹ ∈ T₁ := (mem_normalizer_iff.mp hzT y).mp hy
      have h1 := (hA₁u _ (mul_mem (inv_mem hy) hzy)).mp (h' y hy)
      rw [hc.u_mul_inv hy hzy] at h1
      exact sub_eq_zero.mp h1
    · intro h' y hy
      have hzy : z * y * z⁻¹ ∈ T₁ := (mem_normalizer_iff.mp hzT y).mp hy
      refine (hA₁u _ (mul_mem (inv_mem hy) hzy)).mpr ?_
      rw [hc.u_mul_inv hy hzy, h' y hy, sub_self]
  have hP4 : ∀ b, P b → P (d⁻¹ * b * d) := by
    rintro b ⟨x, hx, ⟨l, hl⟩, rfl⟩
    have hz : d⁻¹ * x * d ∈ X := hdX x hx
    refine ⟨d⁻¹ * x * d, hz, ?_, hπd x hx⟩
    obtain ⟨l', hl', hlz | hlz⟩ := hdich _ hz
    · exact ⟨l', hlz⟩
    refine ⟨1, ?_⟩
    have hz2 : ∀ y ∈ T₁, u ((d⁻¹ * x * d) ^ 2 * y * ((d⁻¹ * x * d) ^ 2)⁻¹) = u y := by
      intro y hy
      rw [show (d⁻¹ * x * d) ^ 2 * y * ((d⁻¹ * x * d) ^ 2)⁻¹ =
        (d⁻¹ * x * d) * ((d⁻¹ * x * d) * y * (d⁻¹ * x * d)⁻¹) * (d⁻¹ * x * d)⁻¹ by
          simp only [sq]; group,
        hlz _ (hconjT _ hz y hy), hlz y hy, map_mul, hσσ, ← mul_assoc, hl', one_mul]
    have hz2' := (triv_iff (pow_mem (hXT _ hz) 2)).mpr hz2
    have hx2' := U3C1.conj_triv hdT hdA hz2'
    rw [show d * (d⁻¹ * x * d) ^ 2 * d⁻¹ = x ^ 2 by simp only [sq]; group] at hx2'
    have hx2 := (triv_iff (pow_mem (hXT x hx) 2)).mp hx2'
    have hl2 : l * l = 1 := by
      have h1 := (U3RootCoords.u_conj_pow (hXT x hx) hl 2 y₁ hy₁).symm.trans (hx2 y₁ hy₁)
      rwa [hu₁, mul_one, sq] at h1
    have hl1 : l = 1 := by
      rcases mul_self_eq_one_iff.mp hl2 with h1 | h1
      · exact h1
      · rw [h1, CharTwo.neg_eq]
    have hxtriv := (triv_iff (hXT x hx)).mpr fun y hy => by rw [hl y hy, hl1, one_mul]
    have h3 := U3C1.conj_triv (inv_mem hdT) (inv_mem hdA) hxtriv
    simp only [inv_inv] at h3
    intro y hy
    rw [(triv_iff (hXT _ hz)).mp h3 y hy, one_mul]
  have hP4n : ∀ n : ℕ, ∀ b, P b → P ((d ^ n)⁻¹ * b * d ^ n) := by
    intro n
    induction n with
    | zero => intro b hb; simpa using hb
    | succ n ih =>
      intro b hb
      have h1 := hP4 _ (ih b hb)
      rwa [show d⁻¹ * ((d ^ n)⁻¹ * b * d ^ n) * d = (d ^ (n + 1))⁻¹ * b * d ^ (n + 1) by
        rw [pow_succ]; group] at h1
  have hP5 : ∀ x ∈ X, ∀ x' ∈ X,
      ¬ (∃ l : E', ∀ y ∈ T₁, u (x * y * x⁻¹) = l * u y) →
      ¬ (∃ l : E', ∀ y ∈ T₁, u (x' * y * x'⁻¹) = l * u y) →
      P (outerRestPt t k x * (outerRestPt t k x')⁻¹) := by
    intro x hx x' hx' hnx hnx'
    obtain ⟨l, hl, hlx | hlx⟩ := hdich x hx
    · exact absurd ⟨l, hlx⟩ hnx
    obtain ⟨l', hl', hlx' | hlx'⟩ := hdich x' hx'
    · exact absurd ⟨l', hlx'⟩ hnx'
    have hl'0 := hne0 l' hl'
    have hinv' : ∀ z ∈ T₁, u (x'⁻¹ * z * x') = (σ l')⁻¹ * σ (u z) := by
      intro z hz
      have h1 := hlx' _ (hconjT' x' hx' z hz)
      rw [show x' * (x'⁻¹ * z * x') * x'⁻¹ = z by group] at h1
      have h2 : σ (u z) = σ l' * u (x'⁻¹ * z * x') := by rw [h1, map_mul, hσσ]
      rw [h2, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero σ).mpr hl'0), one_mul]
    refine ⟨x'⁻¹ * x, mul_mem (inv_mem hx') hx, ⟨(σ l')⁻¹ * σ l, fun y hy => ?_⟩, ?_⟩
    · rw [show x'⁻¹ * x * y * (x'⁻¹ * x)⁻¹ = x'⁻¹ * (x * y * x⁻¹) * x' by group,
        hinv' _ (hconjT x hx y hy), hlx y hy, map_mul, hσσ, mul_assoc]
    · rw [hπmul _ (inv_mem hx') x hx, hπinv x' hx']
  have hPall : ∀ b ∈ A₁, P b := by
    by_contra hcon
    push Not at hcon
    obtain ⟨b₀, hb₀, hPb₀⟩ := hcon
    have hnot : ∀ b ∈ A₁, ¬ P b → ∃ x ∈ X,
        ¬ (∃ l : E', ∀ y ∈ T₁, u (x * y * x⁻¹) = l * u y) ∧ outerRestPt t k x = b := by
      intro b hb hPb
      obtain ⟨x, hx, hxb⟩ := htr b hb
      exact ⟨x, hx, fun hun => hPb ⟨x, hx, hun, hxb⟩, hxb⟩
    have h2 : 2 < Nat.card A₁ := by
      rw [hA₁card]
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
    obtain ⟨s, hs, s', hs', hs1, hs'1, hss'⟩ := exists_two_ne_one h2
    have hex : ∃ p ∈ A₁, p ≠ 1 ∧ P p := by
      by_cases h1 : P s
      · exact ⟨s, hs, hs1, h1⟩
      by_cases h3 : P s'
      · exact ⟨s', hs', hs'1, h3⟩
      obtain ⟨x, hx, hnx, hxs⟩ := hnot s hs h1
      obtain ⟨x', hx', hnx', hx's⟩ := hnot s' hs' h3
      refine ⟨s * s'⁻¹, mul_mem hs (inv_mem hs'), fun h4 => hss' (mul_inv_eq_one.mp h4), ?_⟩
      have := hP5 x hx x' hx' hnx hnx'
      rwa [hxs, hx's] at this
    obtain ⟨p, hp, hp1, hPp⟩ := hex
    apply hPb₀
    by_cases hb₀1 : b₀ = 1
    · rw [hb₀1]; exact hP1
    obtain ⟨n, hn⟩ := hC.trans p hp b₀ hb₀ hp1 hb₀1
    rw [← hn]
    exact hP4n n p hPp
  intro b hb
  obtain ⟨x, hx, ⟨l, hl⟩, hxb⟩ := hPall b hb
  have hlq : l ^ (2 ^ f + 1) = 1 := by
    have := hnorm x hx l hl
    rwa [hσ, ← pow_succ'] at this
  have hxq := U3RootCoords.u_conj_pow (hXT x hx) hl (2 ^ f + 1)
  have hxqX : x ^ (2 ^ f + 1) ∈ X := pow_mem hx _
  refine ⟨x ^ (2 ^ f + 1), ⟨hXY _ hxqX, (mem_inf.mp hxqX).2, hXT _ hxqX, fun y hy => ?_⟩, ?_⟩
  · have hz : x ^ (2 ^ f + 1) * y * (x ^ (2 ^ f + 1))⁻¹ ∈ T₁ :=
      (mem_normalizer_iff.mp (hXT _ hxqX) y).mp hy
    refine (hA₁u _ (mul_mem (inv_mem hy) hz)).mpr ?_
    rw [hc.u_mul_inv hy hz, hxq y hy, hlq, one_mul, sub_self]
  · rw [hcf.outerRestPt_pow_of_conj h hS2 hk (hXY x hx) (hXA x hx), hxb, pow_succ]
    have hb2 : b ^ 2 ^ f = 1 := by
      obtain ⟨m, hm⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
      rw [hm, pow_succ, pow_mul', hsqA₁ b hb, one_pow]
    rw [hb2, one_mul]

end Untwist

end U3C1OuterConf

end CFSG.SeitzReduction.RankOne
