module

public import CFSG.ClassicalInvolution.Asc77.AscC25V1
public import CFSG.ClassicalInvolution.Asc77.AscT7F2Out
public import CFSG.ClassicalInvolution.Asc77.AscT7U1
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

@[expose] def lam {G : Type} [Group G] (R R' : Subgroup G) (t' : G) : Subgroup G :=
  R ⊔ R' ⊔ Subgroup.zpowers t'

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ t' : G}

section Lam

variable (R R' t')

theorem mem_lam_iff (ht'2 : t' * t' = 1) (ht'R : conjSub t' R = R') (ht'R' : conjSub t' R' = R)
    {x : G} : x ∈ lam R R' t' ↔ x ∈ R ⊔ R' ∨ t' * x ∈ R ⊔ R' := by
  have hinv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht'2
  have hconj : ∀ y ∈ R ⊔ R', t' * y * t' ∈ R ⊔ R' := by
    intro y hy
    have h1 : conjSub t' (R ⊔ R') = R' ⊔ R := by
      rw [show conjSub t' (R ⊔ R') = conjSub t' R ⊔ conjSub t' R' from Subgroup.map_sup _ _ _,
        ht'R, ht'R']
    have h2 : t' * y * t'⁻¹ ∈ conjSub t' (R ⊔ R') := conj_mem_conjSub (n := t') hy
    rw [h1, sup_comm, hinv] at h2
    exact h2
  let T : Subgroup G :=
    { carrier := {x | x ∈ R ⊔ R' ∨ t' * x ∈ R ⊔ R'}
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl ((R ⊔ R').mul_mem hx hy)
        · right
          have : t' * (x * y) = (t' * x * t') * (t' * y) := by
            calc t' * (x * y) = t' * x * (t' * t') * y := by rw [ht'2]; group
              _ = _ := by group
          rw [this]
          exact (R ⊔ R').mul_mem (hconj x hx) hy
        · right
          have : t' * (x * y) = (t' * x) * y := by group
          rw [this]
          exact (R ⊔ R').mul_mem hx hy
        · left
          have : x * y = (t' * (t' * x) * t') * (t' * y) := by
            calc x * y = (t' * t') * x * ((t' * t') * y) := by rw [ht'2]; group
              _ = _ := by group
          rw [this]
          exact (R ⊔ R').mul_mem (hconj _ hx) hy
      one_mem' := Or.inl (R ⊔ R').one_mem
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl ((R ⊔ R').inv_mem hx)
        · right
          have h1 := hconj _ ((R ⊔ R').inv_mem hx)
          have h3 : (t' * x)⁻¹ = x⁻¹ * t' := by rw [mul_inv_rev, hinv]
          rw [h3] at h1
          have h2 : t' * x⁻¹ = t' * (x⁻¹ * t') * t' := by
            calc t' * x⁻¹ = t' * x⁻¹ * (t' * t') := by rw [ht'2, mul_one]
              _ = _ := by group
          rw [h2]
          exact h1 }
  have hP : R ⊔ R' ≤ T := fun y hy => Or.inl hy
  have ht'T : t' ∈ T := Or.inr (by rw [ht'2]; exact (R ⊔ R').one_mem)
  constructor
  · intro hx
    have hle : lam R R' t' ≤ T := sup_le hP (Subgroup.zpowers_le.mpr ht'T)
    exact hle hx
  · rintro (hx | hx)
    · exact Subgroup.mem_sup_left hx
    · have h1 : t' * x ∈ lam R R' t' := Subgroup.mem_sup_left hx
      have h2 : t' ∈ lam R R' t' := Subgroup.mem_sup_right (Subgroup.mem_zpowers t')
      have := (lam R R' t').mul_mem h2 h1
      rwa [← mul_assoc, ht'2, one_mul] at this

end Lam

section Main


variable (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')

include h

theorem lam_le_S : lam R R' t' ≤ (S : Subgroup G) :=
  sup_le (sup_le h.hRS h.hR'S) (Subgroup.zpowers_le.mpr h.ht'S)

theorem mem_lam_iff' {x : G} : x ∈ lam R R' t' ↔ x ∈ R ⊔ R' ∨ t' * x ∈ R ⊔ R' :=
  mem_lam_iff R R' t' h.ht'2 h.ht'R h.ht'R'

theorem not_mem_lam {a : G} (haS : a ∈ (S : Subgroup G)) (hF' : IsFAut R' a) :
    a ∉ lam R R' t' := by
  intro ha
  have haN : a ∈ T7F2.Nsub S R :=
    h.mem_N_of_conj_R' haS (mem_normalizer_iff_conjSub_eq.mp hF'.1)
  have hPN : R ⊔ R' ≤ T7F2.Nsub S R := sup_le h.R_le_N h.R'_le_N
  rcases (mem_lam_iff' h).mp ha with hP | hP
  · obtain ⟨r, hr, r', hr', hrr'⟩ := T7F2.Out.exists_mul_of_mem_sup_of_commute h.hcomm hP
    have hc : Commute r r' := h.hcomm r hr r' hr'
    have hcen : ∀ x ∈ R', r⁻¹ * x = x * r⁻¹ := fun x hx =>
      ((show Commute r x from h.hcomm r hr x hx).inv_left).eq
    have hF2 : IsFAut R' (a * r⁻¹) := T7U.isFAut_mul_of_centralizes hcen hF'
    have : a * r⁻¹ = r' := by
      rw [hrr', hc.eq]
      group
    rw [this] at hF2
    exact T7U.not_isFAut_of_mem h.hqR' h.hzR' hr' hF2
  · have h1 : t' ∈ T7F2.Nsub S R := by
      have h2 := (T7F2.Nsub S R).mul_mem (hPN hP) ((T7F2.Nsub S R).inv_mem haN)
      simpa using h2
    exact h.t'_not_mem_N h1

theorem false_of_cyc_fus [IsSimpleGroup G] {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1)
    (hF' : IsFAut R' a)
    (hcyc : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), ⁅x, y⁆ ∈ lam R R' t')
    (hfus : ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → a⁻¹ * (g⁻¹ * a * g) ∈ lam R R' t') :
    False := by
  classical
  have hle := lam_le_S h
  let N : Subgroup ↥(S : Subgroup G) := (lam R R' t').subgroupOf (S : Subgroup G)
  have hmem : ∀ s : ↥(S : Subgroup G), s ∈ N ↔ (s : G) ∈ lam R R' t' := fun s =>
    Subgroup.mem_subgroupOf
  have hnorm : N.Normal := by
    refine ⟨fun n hn s => ?_⟩
    rw [hmem] at hn ⊢
    have h1 := hcyc (s : G) s.2 (n : G) n.2
    have h2 : (s : G) * n * (s : G)⁻¹ = ⁅(s : G), (n : G)⁆ * (n : G) := by
      simp only [commutatorElement_def]; group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h2]
    exact (lam R R' t').mul_mem h1 hn
  have : N.Normal := hnorm
  have hab : ∀ x y : ↥(S : Subgroup G) ⧸ N, x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with | _ s₁ => ?_
    induction y using QuotientGroup.induction_on with | _ s₂ => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hmem]
    have h1 := hcyc ((s₂⁻¹ : ↥(S : Subgroup G)) : G) (s₂⁻¹).2 ((s₁⁻¹ : ↥(S : Subgroup G)) : G)
      (s₁⁻¹).2
    have h2 : ((s₁ * s₂)⁻¹ * (s₂ * s₁) : ↥(S : Subgroup G)) = (s₂⁻¹ * s₁⁻¹ * s₂ * s₁ : _) := by
      group
    rw [h2]
    simpa [commutatorElement_def, mul_assoc] using h1
  let _ : CommGroup (↥(S : Subgroup G) ⧸ N) :=
    { (inferInstance : Group (↥(S : Subgroup G) ⧸ N)) with mul_comm := hab }
  let ϕ : ↥(S : Subgroup G) →* ↥(S : Subgroup G) ⧸ N := QuotientGroup.mk' N
  obtain ⟨x, -, y, -, hxy⟩ := h.hqR.exists_not_commute
  refine C25V.false_of_transfer_fusion ⟨x, y, hxy⟩ S (S : Subgroup G) le_rfl ϕ a haS ha2 ?_ ?_
  · intro g hg
    have h1 : a⁻¹ * (g⁻¹ * a * g) ∈ lam R R' t' := hfus g hg
    have h2 := (lam R R' t').inv_mem h1
    show (QuotientGroup.mk ⟨g⁻¹ * a * g, hg⟩ : ↥(S : Subgroup G) ⧸ N) = QuotientGroup.mk ⟨a, haS⟩
    rw [QuotientGroup.eq, hmem]
    simpa [mul_assoc] using h2
  · intro hone
    have : (QuotientGroup.mk ⟨a, haS⟩ : ↥(S : Subgroup G) ⧸ N) = 1 := hone
    rw [QuotientGroup.eq_one_iff, hmem] at this
    exact not_mem_lam h haS hF' this

end Main

end CFSG.ClassicalInvolution.Asc77.C25V
