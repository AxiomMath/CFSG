module

public import CFSG.Sporadic.SuzRecog.TitsTwoType
public import Mathlib.Algebra.Group.Action.Sum

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Sporadic.SuzRecog.TitsTwo CFSG.Sporadic.Co1Patterson CFSG.Monster.B.Recog
  SimpleGraph

universe u v

@[expose] def AmalgamUniversal {Z : Type u} [Group Z] (Xp Xq Xe : Subgroup Z) (s : Z) : Prop :=
  ∃ (hq : s ∈ Xq) (he : s ∈ Xe), ∀ (G : Type v) [Group G] (φp : ↥Xp →* G) (φq : ↥Xq →* G)
    (φe : ↥Xe →* G),
    (∀ (x : Z) (hp : x ∈ Xp) (hq' : x ∈ Xq), φp ⟨x, hp⟩ = φq ⟨x, hq'⟩) →
    (∀ (x : Z) (hp : x ∈ Xp) (he' : x ∈ Xe), φp ⟨x, hp⟩ = φe ⟨x, he'⟩) →
    φq ⟨s, hq⟩ = φe ⟨s, he⟩ →
    ∃! Φ : Z →* G, (∀ x : ↥Xp, Φ x = φp x) ∧ (∀ x : ↥Xq, Φ x = φq x) ∧
      ∀ x : ↥Xe, Φ x = φe x

namespace AmalgamUniversal

variable {Z : Type u} [Group Z] {Xp Xq Xe : Subgroup Z} {s : Z}

theorem mem_q (h : AmalgamUniversal.{u, v} Xp Xq Xe s) : s ∈ Xq := h.fst

theorem mem_e (h : AmalgamUniversal.{u, v} Xp Xq Xe s) : s ∈ Xe := h.snd.fst

theorem existsUnique_hom (h : AmalgamUniversal.{u, v} Xp Xq Xe s) {G : Type v} [Group G]
    (φp : ↥Xp →* G) (φq : ↥Xq →* G) (φe : ↥Xe →* G)
    (hpq : ∀ (x : Z) (hp : x ∈ Xp) (hq' : x ∈ Xq), φp ⟨x, hp⟩ = φq ⟨x, hq'⟩)
    (hpe : ∀ (x : Z) (hp : x ∈ Xp) (he' : x ∈ Xe), φp ⟨x, hp⟩ = φe ⟨x, he'⟩)
    (hs : φq ⟨s, h.mem_q⟩ = φe ⟨s, h.mem_e⟩) :
    ∃! Φ : Z →* G, (∀ x : ↥Xp, Φ x = φp x) ∧ (∀ x : ↥Xq, Φ x = φq x) ∧
      ∀ x : ↥Xe, Φ x = φe x :=
  h.snd.snd G φp φq φe hpq hpe hs

theorem exists_hom (h : AmalgamUniversal.{u, v} Xp Xq Xe s) {G : Type v} [Group G]
    (φp : ↥Xp →* G) (φq : ↥Xq →* G) (φe : ↥Xe →* G)
    (hpq : ∀ (x : Z) (hp : x ∈ Xp) (hq' : x ∈ Xq), φp ⟨x, hp⟩ = φq ⟨x, hq'⟩)
    (hpe : ∀ (x : Z) (hp : x ∈ Xp) (he' : x ∈ Xe), φp ⟨x, hp⟩ = φe ⟨x, he'⟩)
    (hs : φq ⟨s, h.mem_q⟩ = φe ⟨s, h.mem_e⟩) :
    ∃ Φ : Z →* G, (∀ x : ↥Xp, Φ x = φp x) ∧ (∀ x : ↥Xq, Φ x = φq x) ∧
      ∀ x : ↥Xe, Φ x = φe x :=
  (h.existsUnique_hom φp φq φe hpq hpe hs).exists

end AmalgamUniversal

section Triangles

variable {Z : Type u} [Group Z] {Xp Xq : Subgroup Z} {s : Z}

@[expose] def amalgamTriangles (Xp Xq : Subgroup Z) (s : Z) :
    Set ((Z ⧸ Xp) ⊕ (Z ⧸ Xq)) → Prop := fun S =>
  ∃ (x y : Z ⧸ Xp) (π : Z ⧸ Xq), (cosetGraph₂ Xp Xq s).Adj (.inl x) (.inl y) ∧
    (cosetGraph₂ Xp Xq s).Adj (.inl x) (.inr π) ∧ (cosetGraph₂ Xp Xq s).Adj (.inl y) (.inr π) ∧
    S = {.inl x, .inl y, .inr π}

theorem amalgamTriangles_iff (S : Set ((Z ⧸ Xp) ⊕ (Z ⧸ Xq))) :
    amalgamTriangles Xp Xq s S ↔ ∃ (x y : Z ⧸ Xp) (π : Z ⧸ Xq), (cosetGraph Xp s).Adj x y ∧
      (∃ z : Z, x = (z : Z ⧸ Xp) ∧ π = (z : Z ⧸ Xq)) ∧
      (∃ z : Z, y = (z : Z ⧸ Xp) ∧ π = (z : Z ⧸ Xq)) ∧ S = {.inl x, .inl y, .inr π} := by
  simp only [amalgamTriangles, cosetGraph₂_adj_inl_inl, cosetGraph₂_adj_inl_inr]

theorem amalgamTriangles_smul (g : Z) (S : Set ((Z ⧸ Xp) ⊕ (Z ⧸ Xq)))
    (hS : amalgamTriangles Xp Xq s S) : amalgamTriangles Xp Xq s ((g • ·) '' S) := by
  obtain ⟨x, y, π, hxy, hxπ, hyπ, rfl⟩ := hS
  refine ⟨g • x, g • y, g • π, cosetGraph₂_adj_smul g hxy, cosetGraph₂_adj_smul g hxπ,
    cosetGraph₂_adj_smul g hyπ, ?_⟩
  simp only [Set.image_insert_eq, Set.image_singleton]
  rfl

end Triangles

section BaseEdge

variable {Z : Type u} [Group Z] {Xp Xq Xe : Subgroup Z} {s : Z}

private theorem smul_inl_one_eq_iff (g : Z) :
    g • (Sum.inl ((1 : Z) : Z ⧸ Xp) : (Z ⧸ Xp) ⊕ (Z ⧸ Xq)) = Sum.inl ((1 : Z) : Z ⧸ Xp) ↔
      g ∈ Xp := by
  change Sum.inl ((g * 1 : Z) : Z ⧸ Xp) = _ ↔ _
  rw [Sum.inl.injEq, QuotientGroup.eq]
  simp

private theorem smul_inr_one_eq_iff (g : Z) :
    g • (Sum.inr ((1 : Z) : Z ⧸ Xq) : (Z ⧸ Xp) ⊕ (Z ⧸ Xq)) = Sum.inr ((1 : Z) : Z ⧸ Xq) ↔
      g ∈ Xq := by
  change Sum.inr ((g * 1 : Z) : Z ⧸ Xq) = _ ↔ _
  rw [Sum.inr.injEq, QuotientGroup.eq]
  simp

private theorem smul_inl_s_eq_inl_s_iff (g : Z) :
    g • (Sum.inl ((s : Z) : Z ⧸ Xp) : (Z ⧸ Xp) ⊕ (Z ⧸ Xq)) = Sum.inl ((s : Z) : Z ⧸ Xp) ↔
      s⁻¹ * g * s ∈ Xp := by
  change Sum.inl ((g * s : Z) : Z ⧸ Xp) = _ ↔ _
  rw [Sum.inl.injEq, QuotientGroup.eq]
  have : (g * s)⁻¹ * s = (s⁻¹ * g * s)⁻¹ := by group
  rw [this, inv_mem_iff]

private theorem smul_inl_one_eq_inl_s_iff (g : Z) :
    g • (Sum.inl ((1 : Z) : Z ⧸ Xp) : (Z ⧸ Xp) ⊕ (Z ⧸ Xq)) = Sum.inl ((s : Z) : Z ⧸ Xp) ↔
      s⁻¹ * g ∈ Xp := by
  change Sum.inl ((g * 1 : Z) : Z ⧸ Xp) = _ ↔ _
  rw [Sum.inl.injEq, QuotientGroup.eq]
  have : (g * 1)⁻¹ * s = (s⁻¹ * g)⁻¹ := by group
  rw [this, inv_mem_iff]

private theorem smul_inl_s_eq_inl_one_iff (g : Z) :
    g • (Sum.inl ((s : Z) : Z ⧸ Xp) : (Z ⧸ Xp) ⊕ (Z ⧸ Xq)) = Sum.inl ((1 : Z) : Z ⧸ Xp) ↔
      g * s ∈ Xp := by
  change Sum.inl ((g * s : Z) : Z ⧸ Xp) = _ ↔ _
  rw [Sum.inl.injEq, QuotientGroup.eq, mul_one, inv_mem_iff]

private theorem swap_smul (hs₂ : s * s ∈ Xp) :
    s • (Sum.inl ((1 : Z) : Z ⧸ Xp) : (Z ⧸ Xp) ⊕ (Z ⧸ Xq)) = Sum.inl ((s : Z) : Z ⧸ Xp) ∧
      s • (Sum.inl ((s : Z) : Z ⧸ Xp) : (Z ⧸ Xp) ⊕ (Z ⧸ Xq)) =
        Sum.inl ((1 : Z) : Z ⧸ Xp) := by
  refine ⟨?_, (smul_inl_s_eq_inl_one_iff s).2 hs₂⟩
  change Sum.inl ((s * 1 : Z) : Z ⧸ Xp) = _
  rw [mul_one]

private theorem mem_e_iff_smul
    (he : ∀ g : Z, g ∈ Xe ↔ (g ∈ Xp ∧ s⁻¹ * g * s ∈ Xp) ∨ (s⁻¹ * g ∈ Xp ∧ g * s ∈ Xp))
    (g : Z) : g ∈ Xe ↔
      (g • (Sum.inl ((1 : Z) : Z ⧸ Xp) : (Z ⧸ Xp) ⊕ (Z ⧸ Xq)) = Sum.inl ((1 : Z) : Z ⧸ Xp) ∧
        g • (Sum.inl ((s : Z) : Z ⧸ Xp) : (Z ⧸ Xp) ⊕ (Z ⧸ Xq)) = Sum.inl ((s : Z) : Z ⧸ Xp)) ∨
      (g • (Sum.inl ((1 : Z) : Z ⧸ Xp) : (Z ⧸ Xp) ⊕ (Z ⧸ Xq)) = Sum.inl ((s : Z) : Z ⧸ Xp) ∧
        g • (Sum.inl ((s : Z) : Z ⧸ Xp) : (Z ⧸ Xp) ⊕ (Z ⧸ Xq)) = Sum.inl ((1 : Z) : Z ⧸ Xp)) := by
  rw [he g, smul_inl_one_eq_iff, smul_inl_s_eq_inl_s_iff, smul_inl_one_eq_inl_s_iff,
    smul_inl_s_eq_inl_one_iff]

private theorem exists_smul_of_adj_inl_one (hs : s ∉ Xp) (hs₂ : s * s ∈ Xp)
    (y : (Z ⧸ Xp) ⊕ (Z ⧸ Xq)) (hy : (cosetGraph₂ Xp Xq s).Adj (.inl ((1 : Z) : Z ⧸ Xp)) y) :
    (∃ g ∈ Xp, g • (Sum.inl ((s : Z) : Z ⧸ Xp) : (Z ⧸ Xp) ⊕ (Z ⧸ Xq)) = y) ∨
      ∃ g ∈ Xp, g • (Sum.inr ((1 : Z) : Z ⧸ Xq) : (Z ⧸ Xp) ⊕ (Z ⧸ Xq)) = y := by
  rcases y with y | y
  · obtain ⟨a, ha, rfl⟩ := (cosetGraph_adj_mk_iff hs hs₂).1 (cosetGraph₂_adj_inl_inl.1 hy)
    exact Or.inl ⟨a, ha, by simp⟩
  · obtain ⟨z, hz, rfl⟩ := cosetGraph₂_adj_inl_inr.1 hy
    rw [QuotientGroup.eq] at hz
    exact Or.inr ⟨z, by simpa using hz, by simp⟩

private theorem exists_smul_of_adj_inr_one (y : (Z ⧸ Xp) ⊕ (Z ⧸ Xq))
    (hy : (cosetGraph₂ Xp Xq s).Adj (.inr ((1 : Z) : Z ⧸ Xq)) y) :
    ∃ g ∈ Xq, g • (Sum.inl ((1 : Z) : Z ⧸ Xp) : (Z ⧸ Xp) ⊕ (Z ⧸ Xq)) = y := by
  rcases y with y | y
  · obtain ⟨z, rfl, hz⟩ := cosetGraph₂_adj_inr_inl.1 hy
    rw [QuotientGroup.eq] at hz
    exact ⟨z, by simpa using hz, by simp⟩
  · exact absurd hy cosetGraph₂_not_adj_inr_inr

end BaseEdge

section Connectivity

variable {Z : Type u} [Group Z] {Xp Xq Xe : Subgroup Z} {s : Z}

theorem cosetGraph₂_preconnected_of_points (h : (cosetGraph Xp s).Preconnected) :
    (cosetGraph₂ Xp Xq s).Preconnected := by
  have hpt : ∀ x y : Z ⧸ Xp,
      (cosetGraph₂ Xp Xq s).Reachable (.inl x) (.inl y) := fun x y => by
    obtain ⟨w⟩ := h x y
    exact ⟨w.map ⟨Sum.inl, fun h => cosetGraph₂_adj_inl_inl.2 h⟩⟩
  have hv : ∀ w : (Z ⧸ Xp) ⊕ (Z ⧸ Xq),
      (cosetGraph₂ Xp Xq s).Reachable (.inl ((1 : Z) : Z ⧸ Xp)) w := by
    rintro (w | w)
    · exact hpt _ _
    · obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective w
      exact (hpt _ ((z : Z) : Z ⧸ Xp)).trans (cosetGraph₂_adj_inl_inr.2 ⟨z, rfl, rfl⟩).reachable
  exact fun a b => (hv a).symm.trans (hv b)

end Connectivity

section FlagTransitive

variable {Z : Type u} [Group Z] {Xp Xq : Subgroup Z} {s : Z}

theorem flag_transitive_of_two_transitive (hs : s ∉ Xp)
    (h : ∀ w ∈ Xq, w ∉ Xp → ∃ l ∈ Xq, l ∈ Xp ∧ w⁻¹ * (l * s) ∈ Xp) :
    ∀ d ∈ Xp, ∀ x ∈ Xp, ∀ k ∈ Xq, d * k = s * x →
      ∃ e ∈ Xp, s⁻¹ * e * s ∈ Xp ∧ d⁻¹ * e ∈ Xq := by
  intro d hd x hx k hk hdk
  have hkp : k ∉ Xp := by
    intro hkp
    refine hs ?_
    have : s = d * k * x⁻¹ := by rw [hdk]; group
    rw [this]
    exact Xp.mul_mem (Xp.mul_mem hd hkp) (Xp.inv_mem hx)
  obtain ⟨l, hlq, hlp, hl⟩ := h k hk hkp
  refine ⟨d * l, Xp.mul_mem hd hlp, ?_, by simpa using hlq⟩
  have hd' : d = s * x * k⁻¹ := by rw [← hdk]; group
  have : s⁻¹ * (d * l) * s = x * (k⁻¹ * (l * s)) := by rw [hd']; group
  rw [this]
  exact Xp.mul_mem hx hl

end FlagTransitive

structure TitsInput {Z : Type u} [Group Z] (Xp Xq Xe : Subgroup Z) (s : Z) : Prop where
  not_mem_p : s ∉ Xp
  mul_self_mem_p : s * s ∈ Xp
  mem_q : s ∈ Xq
  mem_e_iff : ∀ g : Z, g ∈ Xe ↔ (g ∈ Xp ∧ s⁻¹ * g * s ∈ Xp) ∨ (s⁻¹ * g ∈ Xp ∧ g * s ∈ Xp)
  flag_transitive : ∀ d ∈ Xp, ∀ x ∈ Xp, ∀ k ∈ Xq, d * k = s * x →
    ∃ e ∈ Xp, s⁻¹ * e * s ∈ Xp ∧ d⁻¹ * e ∈ Xq
  preconnected : (cosetGraph₂ Xp Xq s).Preconnected
  triangulable : TriangulableBy (cosetGraph₂ Xp Xq s) (amalgamTriangles Xp Xq s)

namespace TitsInput

variable {Z : Type u} [Group Z] {Xp Xq Xe : Subgroup Z} {s : Z}

theorem mem_e (D : TitsInput Xp Xq Xe s) : s ∈ Xe :=
  (D.mem_e_iff s).2 (Or.inr ⟨by simpa using Xp.one_mem, D.mul_self_mem_p⟩)

theorem of_action {Ω : Type*} [MulAction Z Ω] {x₀ : Ω} (hXp : Xp = MulAction.stabilizer Z x₀)
    (hs : s • x₀ ≠ x₀) (hs₂ : s • s • x₀ = x₀) (hq : s ∈ Xq)
    (he : ∀ g : Z, g ∈ Xe ↔ (g • x₀ = x₀ ∧ g • s • x₀ = s • x₀) ∨
      (g • x₀ = s • x₀ ∧ g • s • x₀ = x₀))
    (h₂ : ∀ w ∈ Xq, w • x₀ ≠ x₀ → ∃ l ∈ Xq, l • x₀ = x₀ ∧ l • s • x₀ = w • x₀)
    (hconn : (cosetGraph₂ Xp Xq s).Preconnected)
    (htri : TriangulableBy (cosetGraph₂ Xp Xq s) (amalgamTriangles Xp Xq s)) :
    TitsInput Xp Xq Xe s := by
  have hmem : ∀ g : Z, g ∈ Xp ↔ g • x₀ = x₀ := fun g => by
    rw [hXp, MulAction.mem_stabilizer_iff]
  have hnot : s ∉ Xp := fun h => hs ((hmem s).1 h)
  refine ⟨hnot, (hmem _).2 (by rw [mul_smul]; exact hs₂), hq, fun g => ?_,
    flag_transitive_of_two_transitive hnot fun w hw hwp => ?_, hconn, htri⟩
  · rw [he g, hmem g, hmem (s⁻¹ * g * s), hmem (s⁻¹ * g), hmem (g * s)]
    simp only [mul_smul, inv_smul_eq_iff]
  · obtain ⟨l, hlq, hlx, hl⟩ := h₂ w hw (fun h => hwp ((hmem w).2 h))
    refine ⟨l, hlq, (hmem l).2 hlx, (hmem _).2 ?_⟩
    rw [mul_smul, mul_smul, inv_smul_eq_iff, hl]

theorem exists_mem_smul_flag (D : TitsInput Xp Xq Xe s) {a : Z ⧸ Xp} {b : Z ⧸ Xq}
    (h₁ : (cosetGraph₂ Xp Xq s).Adj (.inl ((1 : Z) : Z ⧸ Xp)) (.inl a))
    (h₂ : (cosetGraph₂ Xp Xq s).Adj (.inl ((1 : Z) : Z ⧸ Xp)) (.inr b))
    (h₃ : (cosetGraph₂ Xp Xq s).Adj (.inl a) (.inr b)) :
    ∃ g ∈ Xp, ((g * s : Z) : Z ⧸ Xp) = a ∧ ((g : Z) : Z ⧸ Xq) = b := by
  obtain ⟨a₀, ha₀, rfl⟩ := (cosetGraph_adj_mk_iff D.not_mem_p D.mul_self_mem_p).1
    (cosetGraph₂_adj_inl_inl.1 h₁)
  obtain ⟨z, hz, rfl⟩ := cosetGraph₂_adj_inl_inr.1 h₂
  obtain ⟨z', hz'a, hz'b⟩ := cosetGraph₂_adj_inl_inr.1 h₃
  rw [QuotientGroup.eq] at hz hz'a hz'b
  have hzp : z ∈ Xp := by simpa using hz
  have hd : a₀⁻¹ * z ∈ Xp := Xp.mul_mem (Xp.inv_mem ha₀) hzp
  obtain ⟨e, he, hse, hde⟩ := D.flag_transitive (a₀⁻¹ * z) hd _ hz'a (z⁻¹ * z') hz'b (by group)
  refine ⟨a₀ * e, Xp.mul_mem ha₀ he, ?_, ?_⟩
  · rw [QuotientGroup.eq]
    have : (a₀ * e * s)⁻¹ * (1 * a₀ * s) = (s⁻¹ * e * s)⁻¹ := by group
    rw [this]
    exact Xp.inv_mem hse
  · rw [QuotientGroup.eq]
    have : (a₀ * e)⁻¹ * z = ((a₀⁻¹ * z)⁻¹ * e)⁻¹ := by group
    rw [this]
    exact Xq.inv_mem hde

def titsDataTwo (D : TitsInput Xp Xq Xe s) :
    TitsDataTwo (cosetGraph₂ Xp Xq s) (amalgamTriangles Xp Xq s) Z Empty Unit where
  p := .inl ((1 : Z) : Z ⧸ Xp)
  p₁ := .inl ((s : Z) : Z ⧸ Xp)
  q := .inr ((1 : Z) : Z ⧸ Xq)
  u := fun j => j.elim
  Xp := Xp
  Xq := Xq
  Xe := Xe
  Xt := fun j => j.elim
  hadj := fun g _ _ h => cosetGraph₂_adj_smul g h
  hTinv := fun g S hS => amalgamTriangles_smul g S hS
  hconn := D.preconnected
  hΓ := D.triangulable
  hpp₁ := cosetGraph₂_adj_inl_inl.2
    ((cosetGraph_adj_mk_iff D.not_mem_p D.mul_self_mem_p).2 ⟨1, Xp.one_mem, by simp⟩)
  hpq := cosetGraph₂_adj_inl_inr.2 ⟨1, rfl, rfl⟩
  hsep := fun g h => by simp at h
  hlocp := exists_smul_of_adj_inl_one D.not_mem_p D.mul_self_mem_p
  hlocq := exists_smul_of_adj_inr_one
  hXp := fun g => (smul_inl_one_eq_iff g).symm
  hXq := fun g => (smul_inr_one_eq_iff g).symm
  hXe := mem_e_iff_smul D.mem_e_iff
  hXt := fun j => j.elim
  hτ := fun j => j.elim
  hρ := fun j => j.elim
  s := s
  hs := swap_smul D.mul_self_mem_p
  c := fun _ => 1
  c' := fun _ => 1
  hc := fun _ => Xp.one_mem
  hc' := fun _ => Xp.one_mem
  hcell := fun _ => by
    simp only [one_smul]
    change Sum.inr ((s * 1 : Z) : Z ⧸ Xq) = Sum.inr ((1 : Z) : Z ⧸ Xq)
    rw [Sum.inr.injEq, QuotientGroup.eq]
    simpa using D.mem_q
  htri := by
    intro y₁ y₂ h₁ h₂ h₃ hT
    obtain ⟨x, y, π, -, -, -, hS⟩ := hT
    have hπ : (Sum.inr π : (Z ⧸ Xp) ⊕ (Z ⧸ Xq)) ∈
        ({Sum.inl ((1 : Z) : Z ⧸ Xp), y₁, y₂} : Set ((Z ⧸ Xp) ⊕ (Z ⧸ Xq))) := by
      rw [hS]
      simp
    rcases y₁ with a | b <;> rcases y₂ with a' | b'
    · simp at hπ
    · obtain ⟨g, hg, hga, hgb⟩ := D.exists_mem_smul_flag h₁ h₃.symm h₂
      refine Or.inr (Or.inl ⟨(), g, hg, ?_, ?_⟩)
      · change Sum.inl ((g * s : Z) : Z ⧸ Xp) = _
        rw [hga]
      · simp only [one_smul]
        change Sum.inr ((g * 1 : Z) : Z ⧸ Xq) = _
        rw [mul_one, hgb]
    · obtain ⟨g, hg, hga, hgb⟩ := D.exists_mem_smul_flag h₃.symm h₁ h₂.symm
      refine Or.inr (Or.inr ⟨(), g, hg, ?_, ?_⟩)
      · simp only [one_smul]
        change Sum.inr ((g * 1 : Z) : Z ⧸ Xq) = _
        rw [mul_one, hgb]
      · change Sum.inl ((g * s : Z) : Z ⧸ Xp) = _
        rw [hga]
    · exact absurd h₂ cosetGraph₂_not_adj_inr_inr

end TitsInput

theorem amalgamUniversal_of_tits {Z : Type u} [Group Z] {Xp Xq Xe : Subgroup Z} {s : Z}
    (D : TitsInput Xp Xq Xe s) : AmalgamUniversal.{u, v} Xp Xq Xe s := by
  refine ⟨D.mem_q, D.mem_e, fun G _ φp φq φe hpq hpe hrel => ?_⟩
  obtain ⟨Φ, ⟨hΦp, hΦq, hΦe, -⟩, huniq⟩ := D.titsDataTwo.existsUnique_hom φp φq φe
    (fun j => isEmptyElim j) hpq hpe (fun j => isEmptyElim j) (fun j => isEmptyElim j)
    (fun _ => by
      show φq ⟨(1 : Z)⁻¹ * s * 1, _⟩ =
        (φp ⟨(1 : Z), Xp.one_mem⟩)⁻¹ * φe ⟨s, D.mem_e⟩ * φp ⟨(1 : Z), Xp.one_mem⟩
      have h₁ : (⟨(1 : Z)⁻¹ * s * 1, by simpa using D.mem_q⟩ : Xq) = ⟨s, D.mem_q⟩ :=
        Subtype.ext (by simp)
      have h₂ : (⟨(1 : Z), Xp.one_mem⟩ : Xp) = 1 := rfl
      rw [h₁, h₂, map_one, inv_one, one_mul, mul_one]
      exact hrel)
  exact ⟨Φ, ⟨hΦp, hΦq, hΦe⟩, fun Ψ hΨ => huniq Ψ ⟨hΨ.1, hΨ.2.1, hΨ.2.2, fun j => isEmptyElim j⟩⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
