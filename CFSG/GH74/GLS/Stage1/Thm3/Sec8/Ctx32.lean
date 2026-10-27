module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx31
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx28
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx29

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem psi3 (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {g : G} (hg : g ∈ Wsub S U) :
    h⁻¹ * (h⁻¹ * (h⁻¹ * g * h) * h) * h = g := hs.cube_conj hg

theorem exists_invol_of_psi_inv (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hSne : S ≠ S1 S K₁)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1))
    (hψW₀ : ∀ v ∈ Wsub S U ⊓ S1 S K₁, h⁻¹ * v * h ∈ Wsub S U ⊓ S1 S K₁) :
    ∃ d ∈ S, d ∉ S1 S K₁ ∧ d * d = 1 := by
  have hk2 : 2 ≤ 1 + 1 := le_refl _
  obtain ⟨y₁, hy₁P, -, hy₁inv, -⟩ := hs.exists_y₁ hII hq hk
  have hrelW := hs.relIndex_W₀_W hII hq hSne hk
  have hAW₀ : Aof S K₁ W₂ h ≤ Wsub S U ⊓ S1 S K₁ :=
    le_inf (hs.A_le_W hII hq hrec hk2 hk) (hs.A_le_S1 hII hq hrec)
  obtain ⟨w, hwW, hwn⟩ := hs.exists_W_not_S1 hII hq hSne hy₁P hy₁inv
  have hwn₀ : w ∉ Wsub S U ⊓ S1 S K₁ := fun h' => hwn h'.2
  have hw1 : h⁻¹ * w * h ∈ Wsub S U := hs.W_conj_h hwW
  have hw2 : h⁻¹ * (h⁻¹ * w * h) * h ∈ Wsub S U := hs.W_conj_h hw1
  have hψ3 := hs.psi3 hwW
  have hψw₀ : h⁻¹ * w * h ∉ Wsub S U ⊓ S1 S K₁ := by
    intro h'
    have h2 := hψW₀ _ (hψW₀ _ h')
    rw [hψ3] at h2
    exact hwn₀ h2
  have hψ2w₀ : h⁻¹ * (h⁻¹ * w * h) * h ∉ Wsub S U ⊓ S1 S K₁ := by
    intro h'
    have h2 := hψW₀ _ h'
    rw [hψ3] at h2
    exact hwn₀ h2
  have hψw_inv : (h⁻¹ * w * h)⁻¹ ∉ Wsub S U ⊓ S1 S K₁ :=
    fun h' => hψw₀ (by simpa using inv_mem h')
  have hww : w * (h⁻¹ * w * h) ∈ Wsub S U ⊓ S1 S K₁ := by
    have := Basic.mul_inv_mem_of_relIndex_two hrelW hwW (inv_mem hw1) hwn₀ hψw_inv
    rwa [inv_inv] at this
  have hnW : (w * (h⁻¹ * w * h)) * (h⁻¹ * (h⁻¹ * w * h) * h) ∈ Wsub S U :=
    mul_mem (mul_mem hwW hw1) hw2
  have hn₀ : (w * (h⁻¹ * w * h)) * (h⁻¹ * (h⁻¹ * w * h) * h) ∉ Wsub S U ⊓ S1 S K₁ := by
    intro h'
    apply hψ2w₀
    have e : h⁻¹ * (h⁻¹ * w * h) * h = (w * (h⁻¹ * w * h))⁻¹ *
        ((w * (h⁻¹ * w * h)) * (h⁻¹ * (h⁻¹ * w * h) * h)) := by group
    rw [e]
    exact mul_mem (inv_mem hww) h'
  have hψn : h⁻¹ * ((w * (h⁻¹ * w * h)) * (h⁻¹ * (h⁻¹ * w * h) * h)) * h =
      ((h⁻¹ * w * h) * (h⁻¹ * (h⁻¹ * w * h) * h)) * w := by
    calc h⁻¹ * ((w * (h⁻¹ * w * h)) * (h⁻¹ * (h⁻¹ * w * h) * h)) * h
        = (h⁻¹ * w * h) * (h⁻¹ * (h⁻¹ * w * h) * h) *
            (h⁻¹ * (h⁻¹ * (h⁻¹ * w * h) * h) * h) := by group
      _ = ((h⁻¹ * w * h) * (h⁻¹ * (h⁻¹ * w * h) * h)) * w := by rw [hψ3]
  have hcomm := hs.W_comm_mem_A hII hq hrec hk (mul_mem hw1 hw2) hwW
  have hc : (h⁻¹ * ((w * (h⁻¹ * w * h)) * (h⁻¹ * (h⁻¹ * w * h) * h)) * h) *
      ((w * (h⁻¹ * w * h)) * (h⁻¹ * (h⁻¹ * w * h) * h))⁻¹ ∈ Aof S K₁ W₂ h := by
    rw [hψn]
    have e : (((h⁻¹ * w * h) * (h⁻¹ * (h⁻¹ * w * h) * h)) * w) *
        ((w * (h⁻¹ * w * h)) * (h⁻¹ * (h⁻¹ * w * h) * h))⁻¹ =
        ((h⁻¹ * w * h) * (h⁻¹ * (h⁻¹ * w * h) * h)) * w *
          ((h⁻¹ * w * h) * (h⁻¹ * (h⁻¹ * w * h) * h))⁻¹ * w⁻¹ := by group
    rw [e]
    exact hcomm
  obtain ⟨a, ha, hnaD⟩ := hs.exists_a_mem_D hII hq hrec hk2 hk hnW hc
  have hnaW := ((mem_Dsub_iff).1 hnaD).1
  have hna₀ : (w * (h⁻¹ * w * h)) * (h⁻¹ * (h⁻¹ * w * h) * h) * a ∉ Wsub S U ⊓ S1 S K₁ := by
    intro h'
    apply hn₀
    have e : (w * (h⁻¹ * w * h)) * (h⁻¹ * (h⁻¹ * w * h) * h) =
        ((w * (h⁻¹ * w * h)) * (h⁻¹ * (h⁻¹ * w * h) * h) * a) * a⁻¹ := by group
    rw [e]
    exact mul_mem h' (inv_mem (hAW₀ ha))
  exact ⟨_, hnaW.1, fun hd => hna₀ (Subgroup.mem_inf.2 ⟨hnaW, hd⟩),
    hs.D_sq hII hq hrec hk hnaD⟩

theorem exists_invol_outside_e1 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (he : (Pz S z).relIndex (S1 S K₁) = 2)
    (hSne : S ≠ S1 S K₁) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1)) :
    ∃ d ∈ S, d ∉ S1 S K₁ ∧ d * d = 1 := by
  have hk2 : 2 ≤ 1 + 1 := le_refl _
  obtain ⟨y₁, hy₁P, hy₁sq, hy₁inv, -⟩ := hs.exists_y₁ hII hq hk
  obtain ⟨y₂, hy₂P, hy₂sq, hy₂inv, -⟩ := hs.exists_y₂ hII hq hrec hk
  have hyW : y₁ * y₂ ∈ Wsub S U := hs.y_mem_W hII hq hy₁P hy₂P hy₁inv hy₂inv
  have hyV₁ := hs.y_inv_V₁ hII hy₂P hy₁inv
  have hyA : y₁ * y₂ ∉ Aof S K₁ W₂ h := hs.not_mem_A_of_inv hII hq hrec hyV₁
  have hy2 : (y₁ * y₂) * (y₁ * y₂) = 1 := hs.y_sq hII hy₁P hy₂P hy₁sq hy₂sq
  have hyS1 : y₁ * y₂ ∈ S1 S K₁ :=
    mul_mem (hs.P_le_S1 hII (Or.inl rfl) hy₁P) (hs.P_le_S1 hII (Or.inr rfl) hy₂P)
  have hrelA := hs.A_relIndex_W₀ hII hq hrec he hk2 hk hy₁P hy₁inv
  have hrelW := hs.relIndex_W₀_W hII hq hSne hk
  have hAW₀ : Aof S K₁ W₂ h ≤ Wsub S U ⊓ S1 S K₁ :=
    le_inf (hs.A_le_W hII hq hrec hk2 hk) (hs.A_le_S1 hII hq hrec)
  have hyW₀ : y₁ * y₂ ∈ Wsub S U ⊓ S1 S K₁ := Subgroup.mem_inf.2 ⟨hyW, hyS1⟩
  by_cases hψy : h⁻¹ * (y₁ * y₂) * h ∈ Wsub S U ⊓ S1 S K₁
  ·
    have hψW₀ : ∀ v ∈ Wsub S U ⊓ S1 S K₁, h⁻¹ * v * h ∈ Wsub S U ⊓ S1 S K₁ := by
      intro v hv
      by_cases hvA : v ∈ Aof S K₁ W₂ h
      · exact hAW₀ ((hs.A_conj hII hq hrec hk hvA).2)
      · have ha₀ : v * (y₁ * y₂)⁻¹ ∈ Aof S K₁ W₂ h :=
          Basic.mul_inv_mem_of_relIndex_two hrelA hv hyW₀ hvA hyA
        have ha₁ : h⁻¹ * (v * (y₁ * y₂)⁻¹) * h ∈ Aof S K₁ W₂ h :=
          (hs.A_conj hII hq hrec hk ha₀).2
        have e : h⁻¹ * v * h =
            (h⁻¹ * (v * (y₁ * y₂)⁻¹) * h) * (h⁻¹ * (y₁ * y₂) * h) := by group
        rw [e]
        exact mul_mem (hAW₀ ha₁) hψy
    exact hs.exists_invol_of_psi_inv hII hq hrec hSne hk hψW₀
  ·
    refine ⟨h⁻¹ * (y₁ * y₂) * h, (hs.W_conj_h hyW).1,
      fun hd => hψy (Subgroup.mem_inf.2 ⟨hs.W_conj_h hyW, hd⟩), ?_⟩
    calc h⁻¹ * (y₁ * y₂) * h * (h⁻¹ * (y₁ * y₂) * h) = h⁻¹ * ((y₁ * y₂) * (y₁ * y₂)) * h := by group
      _ = 1 := by rw [hy2]; group

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
