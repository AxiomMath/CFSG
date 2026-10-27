module

public import CFSG.ClassicalInvolution.Asc77.AscT7K5
public import CFSG.ClassicalInvolution.Asc77.AscT7K1

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance.Bootstrap

namespace T7K

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}

omit [Finite G] in
theorem mem_cases_of_commuting_involutions {U Z E : G} (hU : U * U = 1) (hZ : Z * Z = 1)
    (hE : E * E = 1) (cUZ : U * Z = Z * U) (cUE : U * E = E * U) (cZE : Z * E = E * Z) {x : G}
    (hx : x ∈ Subgroup.closure ({U * E, U, Z} : Set G)) :
    x = 1 ∨ x = Z ∨ x = U ∨ x = U * Z ∨ x = E ∨ x = Z * E ∨ x = U * E ∨ x = U * Z * E := by
  have hU' : ∀ y : G, U * (U * y) = y := fun y => by rw [← mul_assoc, hU, one_mul]
  have hZ' : ∀ y : G, Z * (Z * y) = y := fun y => by rw [← mul_assoc, hZ, one_mul]
  have hE' : ∀ y : G, E * (E * y) = y := fun y => by rw [← mul_assoc, hE, one_mul]
  have cUZ' : ∀ y : G, U * (Z * y) = Z * (U * y) := fun y => by
    rw [← mul_assoc, cUZ, mul_assoc]
  have cUE' : ∀ y : G, U * (E * y) = E * (U * y) := fun y => by
    rw [← mul_assoc, cUE, mul_assoc]
  have cZE' : ∀ y : G, Z * (E * y) = E * (Z * y) := fun y => by
    rw [← mul_assoc, cZE, mul_assoc]
  have iU : U⁻¹ = U := inv_eq_of_mul_eq_one_right hU
  have iZ : Z⁻¹ = Z := inv_eq_of_mul_eq_one_right hZ
  have iE : E⁻¹ = E := inv_eq_of_mul_eq_one_right hE
  induction hx using Subgroup.closure_induction with
  | mem x hx => rcases hx with rfl | rfl | rfl <;> simp
  | one => simp
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [mul_assoc, hU, hZ, hE, hZ', hE', cUZ, cUE, cZE, cUZ', cUE', cZE']
  | inv x _ hx =>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [mul_assoc, iU, iZ, iE, cUZ, cUE, cZE, cZE']

theorem B_le_W (hd : Hyp23bData Ω K K' W z u e g) :
    Subgroup.closure ({u * e, u, z} : Set G) ≤ W := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl | rfl)
  · exact W.mul_mem hd.huW (e_mem_inf hd).1
  · exact hd.huW
  · exact hd.hzW

variable [IsSimpleGroup G]

theorem exists_three_gens (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    ∃ x₁ x₂ x₃ : G, x₁ ∈ W ∧ x₂ ∈ W ∧ x₃ ∈ W ∧
      W ≤ Subgroup.closure ({x₁, x₂, x₃} : Set G) := by
  have hst := hs.stand
  have hctx : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst hd.hW
  obtain ⟨e', F, he, -, -, -, hab, hcomm, hac, -⟩ :=
    T7E.exists_frame4 hs hd.hW hd.hzW hd.hS4
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, r₁, r₂, r₃, t₁, t₂, t₃, s₁, s₂, s₃⟩ := F.exists_gens hctx
  have hgen : W ≤ Subgroup.closure ({x₁, x₂, x₃} : Set G) :=
    F.W_le_closure hctx he hab hcomm hac h₁ h₂ h₃ r₂ r₃ t₃
  exact ⟨x₁, x₂, x₃, (h₁ ▸ Subgroup.mem_zpowers x₁ : x₁ ∈ F.ρ.R ⊓ W).2,
    (h₂ ▸ Subgroup.mem_zpowers x₂ : x₂ ∈ F.ρ'.R ⊓ W).2,
    (h₃ ▸ Subgroup.mem_zpowers x₃ : x₃ ∈ F.ρ₃.R ⊓ W).2, hgen⟩

theorem mem_B_of_involution (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g)
    {w : G} (hw : w ∈ W) (hw2 : w * w = 1) : w ∈ Subgroup.closure ({u * e, u, z} : Set G) := by
  have hst := hs.stand
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, hgen⟩ := exists_three_gens hs hd
  have hB := B_isElemAbelian hs hd
  exact mem_of_involution_of_card_eq_eight
    (Thompson.commutes_of_mem_WSet hst.odd hst.five hst.hyp hd.hW) h₁ h₂ h₃ hgen (B_le_W hd)
    (fun s hs' => by simpa only [pow_two] using hB.2 s hs') (B_natCard hs hd) hw hw2

theorem mem_normalizer_B (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g)
    {n : G} (hn : n ∈ Subgroup.normalizer (W : Set G)) :
    n ∈ Subgroup.normalizer ((Subgroup.closure ({u * e, u, z} : Set G) : Subgroup G) : Set G) := by
  have hB := B_isElemAbelian hs hd
  have hBW := B_le_W hd
  have key : ∀ m ∈ Subgroup.normalizer (W : Set G), ∀ x ∈ Subgroup.closure ({u * e, u, z} : Set G),
      m * x * m⁻¹ ∈ Subgroup.closure ({u * e, u, z} : Set G) := by
    intro m hm x hx
    refine mem_B_of_involution hs hd ((Subgroup.mem_normalizer_iff.mp hm x).mp (hBW hx)) ?_
    have hx2 : x * x = 1 := by simpa only [pow_two] using hB.2 x hx
    calc m * x * m⁻¹ * (m * x * m⁻¹) = m * (x * x) * m⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key n hn x hx, fun hx => ?_⟩
  have := key n⁻¹ (Subgroup.inv_mem _ hn) _ hx
  simpa [mul_assoc] using this

end T7K

end CFSG.ClassicalInvolution.Asc77
