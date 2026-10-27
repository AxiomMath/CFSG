module

public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4SevenTwo

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

@[expose] def Thm49FailureExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (d : Data G), d.Hyp →
    (∀ g : G, g * d.t * g⁻¹ ≠ d.t * d.v) → False

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem Hyp.t_mul_v_mem_tG (hF : Thm49FailureExclusion)
    (hd : d.Hyp) : d.t * d.v ∈ d.tG := by
  by_contra h
  exact hF G d hd fun g hg => h ⟨g, hg⟩

omit [Finite G] in
@[expose] def Thm49Statement (d : Data G) : Prop :=
  d.tG ∩ centralizer ({d.t} : Set G) =
    {d.t} ∪ {s | ∃ l ∈ d.L, l * (d.t * d.z) * l⁻¹ = s} ∪
      {s | ∃ l ∈ d.L, l * (d.t * d.v) * l⁻¹ = s}

omit [Finite G] in
theorem t_mul_v_mem_tG_of_thm49Statement
    (h49 : d.Thm49Statement) : d.t * d.v ∈ d.tG := by
  have h : d.t * d.v ∈ d.tG ∩ centralizer ({d.t} : Set G) := by
    rw [h49]
    exact Or.inr ⟨1, one_mem _, by group⟩
  exact h.1

theorem Hyp.thm49
    (h49 : d.Thm49Statement) (hd : d.Hyp) :
    d.tG ∩ centralizer ({d.t} : Set G) =
        {d.t} ∪ {s | ∃ l ∈ d.L, l * (d.t * d.z) * l⁻¹ = s} ∪
          {s | ∃ l ∈ d.L, l * (d.t * d.v) * l⁻¹ = s} ∧
      d.tG ∩ centralizer ({d.t} : Set G) = {s | ∃ l ∈ d.L, s = d.t * l ∧ s * s = 1} := by
  have ht2 := hd.t_mul_self
  have htv := t_mul_v_mem_tG_of_thm49Statement h49
  have htz : d.t * d.z ∈ d.tG := hd.exists_conj_eq_t_mul_z
  have hconj : ∀ l ∈ d.L, ∀ x, x ∈ d.tG → x ∈ centralizer ({d.t} : Set G) →
      l * x * l⁻¹ ∈ d.tG ∩ centralizer ({d.t} : Set G) := by
    intro l hl x hx hxC
    obtain ⟨g, rfl⟩ := hx
    refine ⟨⟨l * g, by group⟩, ?_⟩
    exact mul_mem (mul_mem (hd.L_le hl) hxC) (inv_mem (hd.L_le hl))
  have htzC : d.t * d.z ∈ centralizer ({d.t} : Set G) :=
    mul_mem d.t_mem_centralizer (hd.L_le d.z_mem)
  have htvC : d.t * d.v ∈ centralizer ({d.t} : Set G) :=
    mul_mem d.t_mem_centralizer (hd.L_le d.v_mem)
  have h1 : d.tG ∩ centralizer ({d.t} : Set G) =
      {d.t} ∪ {s | ∃ l ∈ d.L, l * (d.t * d.z) * l⁻¹ = s} ∪
        {s | ∃ l ∈ d.L, l * (d.t * d.v) * l⁻¹ = s} := by
    ext s
    constructor
    · rintro ⟨⟨g, rfl⟩, hsC⟩
      rcases hd.conj_t_cases hsC with h | ⟨m, hm, h | h⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨m, hm, h.symm⟩)
      · exact Or.inr ⟨m, hm, h.symm⟩
    · rintro ((h | ⟨l, hl, rfl⟩) | ⟨l, hl, rfl⟩)
      · rw [Set.mem_singleton_iff.1 h]
        exact ⟨⟨1, by group⟩, d.t_mem_centralizer⟩
      · exact hconj l hl _ htz htzC
      · exact hconj l hl _ htv htvC
  refine ⟨h1, ?_⟩
  ext s
  constructor
  · rintro ⟨⟨g, rfl⟩, hsC⟩
    have hs2 : g * d.t * g⁻¹ * (g * d.t * g⁻¹) = 1 := by
      calc g * d.t * g⁻¹ * (g * d.t * g⁻¹) = g * (d.t * d.t) * g⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    rcases hd.involution_mem hsC (by rw [sq]; exact hs2) with h | h
    · exact absurd h (hd.conj_t_not_mem g)
    · exact ⟨_, h, by rw [← mul_assoc, ht2, one_mul], hs2⟩
  · rintro ⟨l, hl, rfl, hs2⟩
    rw [h1]
    have hl2 : l * l = 1 := by
      have hc := hd.L_comm_t hl
      calc l * l = d.t * l * (d.t * l) := by
            rw [← mul_assoc, mul_assoc d.t l d.t, hc, ← mul_assoc, ht2, one_mul]
        _ = 1 := hs2
    by_cases hl1 : l = 1
    · left
      left
      rw [hl1, mul_one]
      rfl
    · obtain ⟨m, hm, hx⟩ := involution_L_conj d hl (orderOf_eq_prime (by rw [sq]; exact hl2) hl1)
      have hmt := hd.L_comm_t hm
      have key : ∀ x : G, l = m * x * m⁻¹ → d.t * l = m * (d.t * x) * m⁻¹ := by
        intro x hx
        rw [hx]
        calc d.t * (m * x * m⁻¹) = (d.t * m) * x * m⁻¹ := by group
          _ = (m * d.t) * x * m⁻¹ := by rw [hmt]
          _ = m * (d.t * x) * m⁻¹ := by group
      rcases hx with hx | hx
      · exact Or.inl (Or.inr ⟨m, hm, (key _ hx).symm⟩)
      · exact Or.inr ⟨m, hm, (key _ hx).symm⟩

theorem Hyp.thm51
    (h49 : d.Thm49Statement) (hd : d.Hyp) {D : Subgroup G} (hD : D = d.A ∨ D = d.B) :
    d.tG ∩ D = (fun x => d.t * x) '' ((D ⊓ d.L : Subgroup G) : Set G) ∧
      normalizer (D : Set G) ≤ normalizer ((D ⊓ d.L : Subgroup G) : Set G) ∧
      ∀ s ∈ d.tG ∩ D, ∃ n ∈ normalizer (D : Set G), n * d.t * n⁻¹ = s := by
  obtain ⟨h1, h2, h3⟩ := hd.thm47_two hD
  have ht2 := hd.t_mul_self
  have hDC : D ≤ centralizer ({d.t} : Set G) := by
    rcases hD with rfl | rfl
    · exact hd.A_facts.2.1
    · exact hd.B_facts.2.1
  have hDa : CFSG.Open.IsElemAbelian 2 D := by
    rcases hD with rfl | rfl
    · exact hd.A_facts.2.2.1
    · exact hd.B_facts.2.2.1
  have htD : d.t ∈ D := by
    rcases hD with rfl | rfl <;> exact mem_sup_right (mem_zpowers _)
  refine ⟨?_, h3, h2⟩
  ext s
  constructor
  · intro hs
    exact ⟨d.t * s, h1 s hs, show d.t * (d.t * s) = s by rw [← mul_assoc, ht2, one_mul]⟩
  · rintro ⟨e, he, rfl⟩
    obtain ⟨heD, heL⟩ := mem_inf.1 he
    have hmem : d.t * e ∈ d.tG ∩ centralizer ({d.t} : Set G) := by
      rw [(hd.thm49 h49).2]
      refine ⟨e, heL, rfl, ?_⟩
      have hc := hd.L_comm_t heL
      calc d.t * e * (d.t * e) = d.t * (e * d.t) * e := by group
        _ = d.t * d.t * (e * e) := by rw [hc]; group
        _ = 1 := by rw [ht2, one_mul, ← sq]; exact hDa.2 e heD
    exact ⟨hmem.1, mul_mem htD heD⟩

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
