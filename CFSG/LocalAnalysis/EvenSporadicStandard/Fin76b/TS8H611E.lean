module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H611D
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma611E

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OHyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B : Subgroup G} {S : Subgroup G}
  (h : OHyp69 L z t T E B β S)

include h

@[expose] def OuterPairing (h : OHyp69 L z t T E B β S) {α : G} (hα : AlphaSpec S z t α) : Prop :=
  ∀ x ∈ E, ∀ y ∈ E, ∀ w w' : G, IsLift h hα α x w → IsLift h hα α y w' →
    w * w' * w⁻¹ * w'⁻¹ = iota α (x * y * x⁻¹ * y⁻¹) ∧
    w * (z * w' * z⁻¹) * w⁻¹ * (z * w' * z⁻¹)⁻¹ = 1

theorem lemma611Cl_of_pairing {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hM : OuterMFacts E S z t) (hp : OuterPairing h hα) :
    Lemma611Cl E B z t α (Fsub h hα) (Wsub h hα (zpowers α)) (Wsub h hα (zpowers (α * t))) := by
  obtain ⟨a, b, c, d, hE⟩ := hF.gen_four
  have hgen : ∀ g ∈ ({a, b, c, d} : Set G), g ∈ E := fun g hg =>
    hE ▸ Subgroup.subset_closure hg
  have ha : a ∈ E := hgen a (by simp)
  have hb : b ∈ E := hgen b (by simp)
  have hc : c ∈ E := hgen c (by simp)
  have hd : d ∈ E := hgen d (by simp)
  have hz₁ := h.zinv_alpha hα
  have hlift : ∀ w ∈ Wsub h hα (zpowers α), ∃ x ∈ E, IsLift h hα α x w := fun w hw =>
    h.exists_isLift_of_mem_Wsub hα hz₁ hE ha hb hc hd hw
  have hzz : ∀ w : G, z * (z * w * z⁻¹) * z⁻¹ = w := fun w => by
    calc z * (z * w * z⁻¹) * z⁻¹ = (z * z) * w * (z * z)⁻¹ := by group
      _ = w := by rw [h.z_sq]; group
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
  have hzαt : z * (α * t) * z⁻¹ = α := by
    calc z * (α * t) * z⁻¹ = (z * α * z⁻¹) * (z * t * z⁻¹) := by group
      _ = α * t * t := by rw [h.z_conj_alpha hα, h.z_conj_t]
      _ = α := by rw [mul_assoc, h.t_sq, mul_one]
  have hcomm1 : ∀ w₁ ∈ Wsub h hα (zpowers α), ∀ w₂ ∈ Wsub h hα (zpowers (α * t)),
      w₁ * w₂ = w₂ * w₁ := by
    intro w₁ hw₁ w₂ hw₂
    have hw₂' := h.conj_z_W2 hα hw₂
    obtain ⟨x, hx, hwx⟩ := hlift w₁ hw₁
    obtain ⟨y, hy, hwy⟩ := hlift _ hw₂'
    have h1 := (hp x hx y hy w₁ _ hwx hwy).2
    rw [hzz] at h1
    exact cmt_eq_one_iff.1 h1
  have hcomm1' : ∀ w ∈ Wsub h hα (zpowers α), ∀ w' ∈ Wsub h hα (zpowers α),
      w * w' * w⁻¹ * w'⁻¹ = 1 ∨ w * w' * w⁻¹ * w'⁻¹ = α := by
    intro w hw w' hw'
    obtain ⟨x, hx, hwx⟩ := hlift w hw
    obtain ⟨y, hy, hwy⟩ := hlift w' hw'
    rw [(hp x hx y hy w w' hwx hwy).1]
    exact iota_mem α _
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := h.exists_anticomm_E2
  have hct : x₀ * y₀ * x₀⁻¹ * y₀⁻¹ = t := by
    have h1 : x₀ * y₀ * x₀⁻¹ * y₀⁻¹ ≠ 1 := fun h1 => hxy₀ (cmt_eq_one_iff.1 h1)
    exact (h.oe.econfig.comm x₀ hx₀.1 y₀ hy₀.1).resolve_left h1
  obtain ⟨w₀, hw₀⟩ := h.exists_isLift hM hα hz₁ hE ha hb hc hd hx₀.1
  obtain ⟨w₀', hw₀'⟩ := h.exists_isLift hM hα hz₁ hE ha hb hc hd hy₀.1
  have hw₀W := h.isLift_mem_Wsub hα (A := zpowers α) (mem_zpowers α) hw₀
  have hw₀'W := h.isLift_mem_Wsub hα (A := zpowers α) (mem_zpowers α) hw₀'
  have hα₀ : w₀ * w₀' * w₀⁻¹ * w₀'⁻¹ = α := by
    rw [(hp x₀ hx₀.1 y₀ hy₀.1 w₀ w₀' hw₀ hw₀').1, hct, iota_of_ne h.t_ne]
  refine ⟨fun w hw => hw.1, fun w hw => hw.1, fun q hq w hw => h.Q_norm_Wsub hα hq hw,
    fun q hq w hw => h.Q_norm_Wsub hα hq hw,
    fun b hb w hw => h.W_norm_Wsub hα (h.B_le_W hb) hw,
    fun b hb w hw => h.W_norm_Wsub hα (h.B_le_W hb) hw,
    fun w hw => h.conj_z_W1 hα hw, fun w hw => h.conj_z_W2 hα hw, ?_,
    fun q hq => h.Qs_eq_W1_W2 hα hF hM hq, hcomm1, hcomm1', ⟨w₀, hw₀W, w₀', hw₀'W, hα₀⟩, ?_, ?_,
    ?_, ?_⟩
  · apply le_antisymm
    · exact fun q hq => h.W1_inf_W2 hα hq.1 hq.2
    · exact fun q hq => ⟨h.Zg_mem_Wsub hα _ hq, h.Zg_mem_Wsub hα _ hq⟩
  · intro w hw w' hw'
    have hu := h.conj_z_W2 hα hw
    have hu' := h.conj_z_W2 hα hw'
    have e : w * w' * w⁻¹ * w'⁻¹ =
        z * ((z * w * z⁻¹) * (z * w' * z⁻¹) * (z * w * z⁻¹)⁻¹ * (z * w' * z⁻¹)⁻¹) * z⁻¹ := by
      calc w * w' * w⁻¹ * w'⁻¹ = (z * z) * (w * w' * w⁻¹ * w'⁻¹) * (z * z)⁻¹ := by
            rw [h.z_sq]; group
        _ = _ := by group
    rw [e]
    rcases hcomm1' _ hu _ hu' with h1 | h1
    · left; rw [h1]; group
    · right; rw [h1, h.z_conj_alpha hα]
  · refine ⟨z * w₀ * z⁻¹, h.conj_z_W1 hα hw₀W, z * w₀' * z⁻¹, h.conj_z_W1 hα hw₀'W, ?_⟩
    have : (z * w₀ * z⁻¹) * (z * w₀' * z⁻¹) * (z * w₀ * z⁻¹)⁻¹ * (z * w₀' * z⁻¹)⁻¹ =
        z * (w₀ * w₀' * w₀⁻¹ * w₀'⁻¹) * z⁻¹ := by group
    rw [this, hα₀, h.z_conj_alpha hα]
  · intro w hw
    obtain ⟨x, hx, hwx⟩ := hlift w hw
    obtain ⟨a₁, ha₁, hxa, -⟩ := h.rel_d_t hα hx hwx
    have haE : a₁ ∈ E := by
      rcases ha₁ with rfl | rfl
      · exact one_mem _
      · exact h.t_mem_E
    have : w * (z * w * z⁻¹) = x * a₁⁻¹ := by rw [hxa]; group
    rw [this]
    exact mul_mem hx (inv_mem haE)
  · intro e he
    obtain ⟨w₀, hw₀e⟩ := h.exists_isLift hM hα hz₁ hE ha hb hc hd he
    obtain ⟨a₁, ha₁, hxa, -⟩ := h.rel_d_t hα he hw₀e
    have hw₀W := h.isLift_mem_Wsub hα (A := zpowers α) (mem_zpowers α) hw₀e
    rcases ha₁ with rfl | rfl
    · exact ⟨w₀, hw₀W, by rw [hxa, mul_one]⟩
    · have hwQ := hw₀e.1
      have hzwQ : z * w₀ * z⁻¹ ∈ Fsub h hα ⊓ centralizer ({α} : Set G) := h.z_norm_Qs hα hwQ
      have hαc : α * (z * w₀ * z⁻¹) = (z * w₀ * z⁻¹) * α :=
        (h.Zg_cent_Q hα (h.alpha_mem_Zg hα)).2 _ hzwQ
      refine ⟨w₀ * α, mul_mem hw₀W (h.Zg_mem_Wsub hα _ (h.alpha_mem_Zg hα)), ?_⟩
      calc e = w₀ * (z * w₀ * z⁻¹) * a₁ := hxa
        _ = w₀ * (z * w₀ * z⁻¹) * (α * (α * a₁)) := by
            rw [← mul_assoc α α a₁, hα.sq, one_mul]
        _ = w₀ * (α * (z * w₀ * z⁻¹)) * (α * a₁) := by
            calc w₀ * (z * w₀ * z⁻¹) * (α * (α * a₁))
                = w₀ * ((z * w₀ * z⁻¹) * α) * (α * a₁) := by group
              _ = w₀ * (α * (z * w₀ * z⁻¹)) * (α * a₁) := by rw [hαc]
        _ = w₀ * α * (z * (w₀ * α) * z⁻¹) := by
            calc w₀ * (α * (z * w₀ * z⁻¹)) * (α * a₁)
                = w₀ * α * ((z * w₀ * z⁻¹) * (α * a₁)) := by group
              _ = w₀ * α * ((z * w₀ * z⁻¹) * (z * α * z⁻¹)) := by rw [h.z_conj_alpha hα]
              _ = w₀ * α * (z * (w₀ * α) * z⁻¹) := by group

end OHyp69

end CFSG.EvenSporadicStandard.Fin76b
