module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB42Alg

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

theorem wl_cases {k : Type} [Field k] (hk : Nat.card k = 4) {m : k} (hm0 : m ≠ 0)
    (hm1 : m ≠ 1) (x : k) : x = 0 ∨ x = 1 ∨ x = m ∨ x = m + 1 := by
  have : CharP k 2 := charP_two_of_card_four_B42 hk
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hm := sq_add_self_add_one_eq_zero_B42 hk hm0 hm1
  by_cases h0 : x = 0
  · exact Or.inl h0
  by_cases h1 : x = 1
  · exact Or.inr (Or.inl h1)
  have hx := sq_add_self_add_one_eq_zero_B42 hk h0 h1
  have h : (x - m) * (x + m + 1) = 0 := by linear_combination hx - hm
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.1 h)))
  · exact Or.inr (Or.inr (Or.inr (by linear_combination h - (m + 1) * h2)))

theorem wl_comm_mul {k : Type} [Field k] (g h : ↥(unipAll k)) :
    g * h = h * g * uelt 0 0 (coordA g * coordB h - coordA h * coordB g) := by
  obtain ⟨a, b, c, rfl⟩ := exists_uelt g
  obtain ⟨a', b', c', rfl⟩ := exists_uelt h
  simp only [uelt_mul, coordA_uelt, coordB_uelt, uelt_inj]
  exact ⟨by ring, by ring, by ring⟩

theorem wl_frattini {k : Type} [Field k] (H : Subgroup ↥(unipAll k))
    (hH : ∀ a b : k, ∃ q ∈ H, coordA q = a ∧ coordB q = b) : ∀ x, x ∈ H := by
  have hZ : ∀ c : k, uelt 0 0 c ∈ H := by
    intro c
    obtain ⟨g, hg, hgA, hgB⟩ := hH c 0
    obtain ⟨h, hh, hhA, hhB⟩ := hH 0 1
    have e : (uelt 0 0 c : ↥(unipAll k)) = (h * g)⁻¹ * (g * h) := by
      rw [eq_inv_mul_iff_mul_eq, wl_comm_mul g h, hgA, hgB, hhA, hhB]
      congr 3
      ring
    rw [e]
    exact H.mul_mem (H.inv_mem (H.mul_mem hh hg)) (H.mul_mem hg hh)
  intro x
  obtain ⟨q, hq, hqA, hqB⟩ := hH (coordA x) (coordB x)
  have h0 : coordA (q⁻¹ * x) = 0 := by
    rw [coordA_mul, coordA_inv, hqA]
    ring
  have h1 : coordB (q⁻¹ * x) = 0 := by
    rw [coordB_mul, coordB_inv, hqB]
    ring
  have hz : q⁻¹ * x = uelt 0 0 (coordC (q⁻¹ * x)) := by
    have := uelt_coords (q⁻¹ * x)
    rw [h0, h1] at this
    exact this.symm
  have e : x = q * uelt 0 0 (coordC (q⁻¹ * x)) := by
    rw [← hz, mul_inv_cancel_left]
  rw [e]
  exact H.mul_mem hq (hZ _)

theorem wl_coordC_d_center {k : Type} [Field k] (d : ↥(unipAll k) →* ↥(unipAll k)) {μ : k}
    (hdA : ∀ g, coordA (d g) = μ * coordA g) (hdB : ∀ g, coordB (d g) = μ * coordB g)
    (c : k) : coordC (d (uelt 0 0 c)) = μ ^ 2 * c := by
  have e : (uelt c 0 0 : ↥(unipAll k)) * uelt 0 1 0 =
      uelt 0 1 0 * uelt c 0 0 * uelt 0 0 c := by
    simp only [uelt_mul, uelt_inj]
    exact ⟨by ring, by ring, by ring⟩
  have h := congrArg (fun g => coordC (d g)) e
  simp only [map_mul, coordC_mul, coordA_mul, hdA, hdB, coordA_uelt, coordB_uelt] at h
  linear_combination -h

theorem wl_K_mem {k : Type} [Field k] (d : ↥(unipAll k) →* ↥(unipAll k))
    (𝒜 : Subgroup (↥(unipAll k) × ↥(unipAll k)))
    (H2 : ∀ g ∈ 𝒜, (d g.1, g.2) ∈ 𝒜) :
    ∀ g ∈ 𝒜, (d g.1 * g.1⁻¹, (1 : ↥(unipAll k))) ∈ 𝒜 := by
  intro g hg
  have h := 𝒜.mul_mem (H2 g hg) (𝒜.inv_mem hg)
  have e : ((d g.1, g.2) * g⁻¹ : ↥(unipAll k) × ↥(unipAll k)) =
      (d g.1 * g.1⁻¹, (1 : ↥(unipAll k))) := by
    ext
    · simp
    · simp
  rwa [e] at h

theorem wl_cramer {k : Type} [Field k] (a b a₁ b₁ a₂ b₂ : k) (hD : a₁ * b₂ - a₂ * b₁ ≠ 0) :
    ∃ α β : k, α * a₁ + β * a₂ = a ∧ α * b₁ + β * b₂ = b := by
  refine ⟨(a * b₂ - a₂ * b) / (a₁ * b₂ - a₂ * b₁), (a₁ * b - a * b₁) / (a₁ * b₂ - a₂ * b₁),
    ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]
    ring
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]
    ring

theorem wl_caseA {k : Type} [Field k] (hk : Nat.card k = 4) {μ : k} (hμ0 : μ ≠ 0)
    (hμ1 : μ ≠ 1) (d : ↥(unipAll k) →* ↥(unipAll k))
    (hdA : ∀ g, coordA (d g) = μ * coordA g) (hdB : ∀ g, coordB (d g) = μ * coordB g)
    (𝒜 : Subgroup (↥(unipAll k) × ↥(unipAll k)))
    (H2 : ∀ g ∈ 𝒜, (d g.1, g.2) ∈ 𝒜)
    (hA : ∃ g ∈ 𝒜, ∃ h ∈ 𝒜, coordA g.1 * coordB h.1 ≠ coordA h.1 * coordB g.1) :
    ∀ u : ↥(unipAll k), (u, (1 : ↥(unipAll k))) ∈ 𝒜 := by
  have : CharP k 2 := charP_two_of_card_four_B42 hk
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hK := wl_K_mem d 𝒜 H2
  obtain ⟨m, hm⟩ : ∃ m : k, m = μ - 1 := ⟨_, rfl⟩
  have hm0 : m ≠ 0 := by
    rw [hm]
    exact sub_ne_zero.2 hμ1
  have hm1 : m ≠ 1 := by
    intro h
    apply hμ0
    linear_combination h - hm + h2
  obtain ⟨R, hR⟩ : ∃ R : k → k → Prop,
      ∀ a b, R a b ↔ ∃ g ∈ 𝒜, coordA g.1 = a ∧ coordB g.1 = b := ⟨_, fun _ _ => Iff.rfl⟩
  have R0 : R 0 0 := (hR _ _).2 ⟨1, 𝒜.one_mem, by simp, by simp⟩
  have Radd : ∀ a b a' b', R a b → R a' b' → R (a + a') (b + b') := by
    intro a b a' b' h h'
    obtain ⟨g, hg, rfl, rfl⟩ := (hR _ _).1 h
    obtain ⟨g', hg', rfl, rfl⟩ := (hR _ _).1 h'
    exact (hR _ _).2 ⟨g * g', 𝒜.mul_mem hg hg', by simp [coordA_mul], by simp [coordB_mul]⟩
  have Rm : ∀ a b, R a b → R (m * a) (m * b) := by
    intro a b h
    obtain ⟨g, hg, rfl, rfl⟩ := (hR _ _).1 h
    refine (hR _ _).2 ⟨(d g.1 * g.1⁻¹, 1), hK g hg, ?_, ?_⟩
    · show coordA (d g.1 * g.1⁻¹) = m * coordA g.1
      rw [coordA_mul, coordA_inv, hdA, hm]
      ring
    · show coordB (d g.1 * g.1⁻¹) = m * coordB g.1
      rw [coordB_mul, coordB_inv, hdB, hm]
      ring
  have Rsc : ∀ a b, R a b → ∀ c, R (c * a) (c * b) := by
    intro a b hab c
    rcases wl_cases hk hm0 hm1 c with rfl | rfl | rfl | rfl
    · simpa using R0
    · simpa using hab
    · exact Rm a b hab
    · have h := Radd _ _ _ _ (Rm a b hab) hab
      have e1 : (m + 1) * a = m * a + a := by ring
      have e2 : (m + 1) * b = m * b + b := by ring
      rw [e1, e2]
      exact h
  obtain ⟨g₁, hg₁, g₂, hg₂, hne⟩ := hA
  have hD : coordA g₁.1 * coordB g₂.1 - coordA g₂.1 * coordB g₁.1 ≠ 0 :=
    fun h => hne (by linear_combination h)
  have Rall : ∀ a b, R a b := by
    intro a b
    obtain ⟨α, β, e1, e2⟩ := wl_cramer a b (coordA g₁.1) (coordB g₁.1) (coordA g₂.1)
      (coordB g₂.1) hD
    have h3 := Radd _ _ _ _ (Rsc _ _ ((hR _ _).2 ⟨g₁, hg₁, rfl, rfl⟩) α)
      (Rsc _ _ ((hR _ _).2 ⟨g₂, hg₂, rfl, rfl⟩) β)
    rw [e1, e2] at h3
    exact h3
  let K₁ : Subgroup ↥(unipAll k) := 𝒜.comap (MonoidHom.inl _ _)
  have hK₁ : ∀ x, x ∈ K₁ ↔ (x, (1 : ↥(unipAll k))) ∈ 𝒜 := fun x => Iff.rfl
  refine fun u => (hK₁ u).1 (wl_frattini K₁ ?_ u)
  intro a b
  obtain ⟨g, hg, hgA, hgB⟩ := (hR _ _).1 (Rall (m⁻¹ * a) (m⁻¹ * b))
  have hmm : m * m⁻¹ = 1 := mul_inv_cancel₀ hm0
  refine ⟨d g.1 * g.1⁻¹, (hK₁ _).2 (hK g hg), ?_, ?_⟩
  · rw [coordA_mul, coordA_inv, hdA, hgA]
    linear_combination a * hmm - (m⁻¹ * a) * hm
  · rw [coordB_mul, coordB_inv, hdB, hgB]
    linear_combination b * hmm - (m⁻¹ * b) * hm

theorem wl_caseB {k : Type} [Field k] (hk : Nat.card k = 4) {μ : k}
    (hμ1 : μ ≠ 1) (d : ↥(unipAll k) →* ↥(unipAll k))
    (hdA : ∀ g, coordA (d g) = μ * coordA g) (hdB : ∀ g, coordB (d g) = μ * coordB g)
    (𝒜 : Subgroup (↥(unipAll k) × ↥(unipAll k))) (hcard : Nat.card ↥𝒜 = 64)
    (H1 : ∀ g ∈ 𝒜, ∀ h ∈ 𝒜, g.1 * h.2 = h.2 * g.1)
    (H2 : ∀ g ∈ 𝒜, (d g.1, g.2) ∈ 𝒜)
    (H3 : ∀ u : ↥(unipAll k), ∃ g ∈ 𝒜, ∃ h ∈ 𝒜, u = g.1 * h.2)
    (hB : ∀ g ∈ 𝒜, ∀ h ∈ 𝒜, coordA g.1 * coordB h.1 = coordA h.1 * coordB g.1) :
    ∀ g ∈ 𝒜, g.1 = 1 := by
  have : CharP k 2 := charP_two_of_card_four_B42 hk
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hfin : Finite k := Nat.finite_of_card_ne_zero (by omega)
  have hUcard : Nat.card ↥(unipAll k) = 64 := by
    rw [card_unipAll, hk]
    norm_num
  have hK := wl_K_mem d 𝒜 H2
  have hZ : ∀ g ∈ 𝒜, coordA g.1 = 0 ∧ coordB g.1 = 0 := by
    intro g hg
    refine coords_eq_zero_of_commute fun u => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := H3 u
    have h1 : g.1 * a.1 = a.1 * g.1 := (commute_unipAll_iff' _ _).2 (hB g hg a ha)
    rw [← mul_assoc, h1, mul_assoc, H1 g hg b hb, ← mul_assoc]
  have hQ : ∀ u : ↥(unipAll k), ∃ y ∈ 𝒜, y.2 = u := by
    have hall := wl_frattini (𝒜.map (MonoidHom.snd _ _)) (by
      intro a b
      obtain ⟨x, hx, y, hy, hxy⟩ := H3 (uelt a b 0)
      refine ⟨y.2, Subgroup.mem_map.2 ⟨y, hy, rfl⟩, ?_, ?_⟩
      · have := congrArg coordA hxy
        rw [coordA_uelt, coordA_mul, (hZ x hx).1, zero_add] at this
        exact this.symm
      · have := congrArg coordB hxy
        rw [coordB_uelt, coordB_mul, (hZ x hx).2, zero_add] at this
        exact this.symm)
    intro u
    obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.1 (hall u)
    exact ⟨y, hy, hyu⟩
  have hinj : ∀ g ∈ 𝒜, ∀ h ∈ 𝒜, g.2 = h.2 → g = h := by
    have hfinA : Finite ↥𝒜 := Nat.finite_of_card_ne_zero (by omega)
    have hfinU : Finite ↥(unipAll k) := Nat.finite_of_card_ne_zero (by omega)
    let f : ↥𝒜 → ↥(unipAll k) := fun g => g.1.2
    have hf : Function.Surjective f := by
      intro u
      obtain ⟨y, hy, rfl⟩ := hQ u
      exact ⟨⟨y, hy⟩, rfl⟩
    have hbij : Function.Bijective f := hf.bijective_of_nat_card_le (by rw [hcard, hUcard])
    intro g hg h hh hgh
    exact congrArg Subtype.val (hbij.1 (show f ⟨g, hg⟩ = f ⟨h, hh⟩ from hgh))
  have hK1 : ∀ g ∈ 𝒜, g.2 = 1 → g.1 = 1 := by
    intro g hg h2
    have := hinj g hg 1 𝒜.one_mem (by simpa using h2)
    simpa using congrArg Prod.fst this
  have hμ2 : μ ^ 2 ≠ 1 := by
    intro h
    apply hμ1
    have h3 : (μ - 1) ^ 2 = 0 := by linear_combination h + (1 - μ) * h2
    have h4 := pow_eq_zero_iff (two_ne_zero) |>.1 h3
    linear_combination h4
  intro g hg
  have hdg : d g.1 = g.1 := mul_inv_eq_one.1 (hK1 (d g.1 * g.1⁻¹, 1) (hK g hg) rfl)
  obtain ⟨hA0, hB0⟩ := hZ g hg
  have hgc : g.1 = uelt 0 0 (coordC g.1) := by
    have := uelt_coords g.1
    rw [hA0, hB0] at this
    exact this.symm
  have hc : coordC (d g.1) = μ ^ 2 * coordC g.1 := by
    have := wl_coordC_d_center d hdA hdB (coordC g.1)
    rwa [← hgc] at this
  have hc0 : coordC g.1 = 0 := by
    rw [hdg] at hc
    have h3 : (μ ^ 2 - 1) * coordC g.1 = 0 := by linear_combination -hc
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hμ2)
  rw [hgc, hc0, uelt_zero]

theorem weights_lemma {k : Type} [Field k] (hk : Nat.card k = 4) {μ : k} (hμ0 : μ ≠ 0)
    (hμ1 : μ ≠ 1) (d : ↥(unipAll k) →* ↥(unipAll k))
    (hdA : ∀ g, coordA (d g) = μ * coordA g) (hdB : ∀ g, coordB (d g) = μ * coordB g)
    (𝒜 : Subgroup (↥(unipAll k) × ↥(unipAll k))) (hcard : Nat.card ↥𝒜 = 64)
    (H1 : ∀ g ∈ 𝒜, ∀ h ∈ 𝒜, g.1 * h.2 = h.2 * g.1)
    (H2 : ∀ g ∈ 𝒜, (d g.1, g.2) ∈ 𝒜)
    (H3 : ∀ u : ↥(unipAll k), ∃ g ∈ 𝒜, ∃ h ∈ 𝒜, u = g.1 * h.2) :
    (∀ g : ↥(unipAll k) × ↥(unipAll k), g ∈ 𝒜 ↔ g.2 = 1) ∨
      (∀ g : ↥(unipAll k) × ↥(unipAll k), g ∈ 𝒜 ↔ g.1 = 1) := by
  have hfin : Finite k := Nat.finite_of_card_ne_zero (by omega)
  have hUcard : Nat.card ↥(unipAll k) = 64 := by
    rw [card_unipAll, hk]
    norm_num
  have hfinA : Finite ↥𝒜 := Nat.finite_of_card_ne_zero (by omega)
  by_cases hA : ∃ g ∈ 𝒜, ∃ h ∈ 𝒜, coordA g.1 * coordB h.1 ≠ coordA h.1 * coordB g.1
  · left
    have hu := wl_caseA hk hμ0 hμ1 d hdA hdB 𝒜 H2 hA
    let E₁ : Subgroup (↥(unipAll k) × ↥(unipAll k)) :=
      (⊤ : Subgroup ↥(unipAll k)).map (MonoidHom.inl _ _)
    have hE₁card : Nat.card E₁ = 64 := by
      rw [Subgroup.card_map_of_injective (fun x y h => congrArg Prod.fst h), Subgroup.card_top,
        hUcard]
    have hle : E₁ ≤ 𝒜 := by
      rintro _ ⟨u, -, rfl⟩
      exact hu u
    have heq : E₁ = 𝒜 := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hE₁card])
    intro g
    rw [← heq]
    constructor
    · rintro ⟨u, -, rfl⟩
      rfl
    · intro h
      exact ⟨g.1, trivial, Prod.ext rfl h.symm⟩
  · right
    push Not at hA
    have hone := wl_caseB hk hμ1 d hdA hdB 𝒜 hcard H1 H2 H3 hA
    let E₂ : Subgroup (↥(unipAll k) × ↥(unipAll k)) :=
      (⊤ : Subgroup ↥(unipAll k)).map (MonoidHom.inr _ _)
    have hE₂card : Nat.card E₂ = 64 := by
      rw [Subgroup.card_map_of_injective (fun x y h => congrArg Prod.snd h), Subgroup.card_top,
        hUcard]
    have hle : 𝒜 ≤ E₂ := fun g hg => ⟨g.2, trivial, Prod.ext (hone g hg).symm rfl⟩
    have heq : 𝒜 = E₂ := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hE₂card])
    intro g
    rw [heq]
    constructor
    · rintro ⟨u, -, rfl⟩
      rfl
    · intro h
      exact ⟨g.2, trivial, Prod.ext h.symm rfl⟩

end CFSG.OddStandard.Seitz77
