module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma611D
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma611Table

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

@[expose] def Lemma610Cl {G : Type} [Group G] (E S B : Subgroup G) (z t α : G)
    (F : Subgroup G) : Prop :=
  S ⊔ E ≤ F ∧ F ≤ normalizer ((S ⊔ E : Subgroup G) : Set G) ∧
    (∀ g ∈ normalizer ((S ⊔ E : Subgroup G) : Set G), ∀ f ∈ F, g * f * g⁻¹ ∈ F) ∧
    Nat.card ↥F = 2048 ∧
    (∀ K : Subgroup G, K ≤ normalizer ((S ⊔ E : Subgroup G) : Set G) →
      (∀ g ∈ normalizer ((S ⊔ E : Subgroup G) : Set G), ∀ k ∈ K, g * k * g⁻¹ ∈ K) →
        IsPGroup 2 K → K ≤ F) ∧ (∀ b ∈ B, b ∈ F → b = 1) ∧
    (∀ m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G), ∃ f ∈ F, ∃ b ∈ B, m = f * b) ∧
    F ⊓ centralizer ({z} : Set G) = E ⊔ zpowers z ∧
    Nat.card ↥(F ⊓ centralizer ({α} : Set G)) = 1024 ∧
    (∀ g ∈ normalizer ((S ⊔ E : Subgroup G) : Set G), ∀ q ∈ F ⊓ centralizer ({α} : Set G),
      g * q * g⁻¹ ∈ F ⊓ centralizer ({α} : Set G)) ∧
    (∀ m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G), m * α = α * m →
      ∃ q ∈ F ⊓ centralizer ({α} : Set G), ∃ b ∈ B, m = q * b) ∧
    (∀ y : G, (y ∈ F ⊓ centralizer ({α} : Set G) ∧
      ∀ q ∈ F ⊓ centralizer ({α} : Set G), y * q = q * y) ↔
        (y = 1 ∨ y = t ∨ y = α ∨ y = α * t)) ∧
    (∀ q ∈ F ⊓ centralizer ({α} : Set G), ∀ q' ∈ F ⊓ centralizer ({α} : Set G),
      ∃ c, (c = 1 ∨ c = t ∨ c = α ∨ c = α * t) ∧ q * q' = c * (q' * q)) ∧
    (∀ q ∈ F ⊓ centralizer ({α} : Set G),
      q * q = 1 ∨ q * q = t ∨ q * q = α ∨ q * q = α * t)

@[expose] def Lemma611Cl {G : Type} [Group G] (E B : Subgroup G) (z t α : G)
    (F W₁ W₂ : Subgroup G) : Prop :=
  W₁ ≤ F ⊓ centralizer ({α} : Set G) ∧ W₂ ≤ F ⊓ centralizer ({α} : Set G) ∧
    (∀ q ∈ F ⊓ centralizer ({α} : Set G), ∀ w ∈ W₁, q * w * q⁻¹ ∈ W₁) ∧
    (∀ q ∈ F ⊓ centralizer ({α} : Set G), ∀ w ∈ W₂, q * w * q⁻¹ ∈ W₂) ∧
    (∀ b ∈ B, ∀ w ∈ W₁, b * w * b⁻¹ ∈ W₁) ∧ (∀ b ∈ B, ∀ w ∈ W₂, b * w * b⁻¹ ∈ W₂) ∧
    (∀ w ∈ W₁, z * w * z⁻¹ ∈ W₂) ∧ (∀ w ∈ W₂, z * w * z⁻¹ ∈ W₁) ∧
    W₁ ⊓ W₂ = zpowers α ⊔ zpowers t ∧
    (∀ q ∈ F ⊓ centralizer ({α} : Set G), ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, q = w₁ * w₂) ∧
    (∀ w₁ ∈ W₁, ∀ w₂ ∈ W₂, w₁ * w₂ = w₂ * w₁) ∧
    (∀ w ∈ W₁, ∀ w' ∈ W₁, w * w' * w⁻¹ * w'⁻¹ = 1 ∨ w * w' * w⁻¹ * w'⁻¹ = α) ∧
    (∃ w ∈ W₁, ∃ w' ∈ W₁, w * w' * w⁻¹ * w'⁻¹ = α) ∧
    (∀ w ∈ W₂, ∀ w' ∈ W₂, w * w' * w⁻¹ * w'⁻¹ = 1 ∨ w * w' * w⁻¹ * w'⁻¹ = α * t) ∧
    (∃ w ∈ W₂, ∃ w' ∈ W₂, w * w' * w⁻¹ * w'⁻¹ = α * t) ∧
    (∀ w ∈ W₁, w * (z * w * z⁻¹) ∈ E) ∧ (∀ e ∈ E, ∃ w ∈ W₁, e = w * (z * w * z⁻¹))

@[expose] def Lemma611Out {G : Type} [Group G] (E S B : Subgroup G) (z t : G) : Prop :=
  ∀ α : G, AlphaSpec S z t α → ∃ F W₁ W₂ : Subgroup G, Lemma610Cl E S B z t α F ∧
    Lemma611Cl E B z t α F W₁ W₂

namespace Hyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B : Subgroup G} {S : Subgroup G}
  (h : Hyp69 L z t T₀ E Q x β B S)

include h

theorem lemma611Cl_of_pairing {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hpair : ∀ x ∈ E, ∀ y ∈ E, ∀ w w', IsLift h hα α x w → IsLift h hα α y w' →
      w * w' * w⁻¹ * w'⁻¹ = iota α (x * y * x⁻¹ * y⁻¹) ∧
      w * (z * w' * z⁻¹) * w⁻¹ * (z * w' * z⁻¹)⁻¹ = 1) :
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
    have h1 := (hpair x hx y hy w₁ _ hwx hwy).2
    rw [hzz] at h1
    exact cmt_eq_one_iff.1 h1
  have hcomm1' : ∀ w ∈ Wsub h hα (zpowers α), ∀ w' ∈ Wsub h hα (zpowers α),
      w * w' * w⁻¹ * w'⁻¹ = 1 ∨ w * w' * w⁻¹ * w'⁻¹ = α := by
    intro w hw w' hw'
    obtain ⟨x, hx, hwx⟩ := hlift w hw
    obtain ⟨y, hy, hwy⟩ := hlift w' hw'
    rw [(hpair x hx y hy w w' hwx hwy).1]
    exact iota_mem α _
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := h.exists_anticomm_E2
  have hct : x₀ * y₀ * x₀⁻¹ * y₀⁻¹ = t := by
    have h1 : x₀ * y₀ * x₀⁻¹ * y₀⁻¹ ≠ 1 := fun h1 => hxy₀ (cmt_eq_one_iff.1 h1)
    exact (h.conf.econfig.comm x₀ hx₀.1 y₀ hy₀.1).resolve_left h1
  obtain ⟨w₀, hw₀⟩ := h.exists_isLift hα hz₁ hE ha hb hc hd hx₀.1
  obtain ⟨w₀', hw₀'⟩ := h.exists_isLift hα hz₁ hE ha hb hc hd hy₀.1
  have hw₀W := h.isLift_mem_Wsub hα (A := zpowers α) (mem_zpowers α) hw₀
  have hw₀'W := h.isLift_mem_Wsub hα (A := zpowers α) (mem_zpowers α) hw₀'
  have hα₀ : w₀ * w₀' * w₀⁻¹ * w₀'⁻¹ = α := by
    rw [(hpair x₀ hx₀.1 y₀ hy₀.1 w₀ w₀' hw₀ hw₀').1, hct, iota_of_ne h.t_ne]
  refine ⟨fun w hw => hw.1, fun w hw => hw.1, fun q hq w hw => h.Q_norm_Wsub hα hq hw,
    fun q hq w hw => h.Q_norm_Wsub hα hq hw,
    fun b hb w hw => h.W_norm_Wsub hα (h.B_le_W hb) hw,
    fun b hb w hw => h.W_norm_Wsub hα (h.B_le_W hb) hw,
    fun w hw => h.conj_z_W1 hα hw, fun w hw => h.conj_z_W2 hα hw, ?_,
    fun q hq => h.Qs_eq_W1_W2 hα hF hq, hcomm1, hcomm1', ⟨w₀, hw₀W, w₀', hw₀'W, hα₀⟩, ?_, ?_,
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
    obtain ⟨w₀, hw₀e⟩ := h.exists_isLift hα hz₁ hE ha hb hc hd he
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

theorem eps_eq_one {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hWr : ∃ hz : z ∈ centralizer ({β} : Set G),
      WreathAlt ↥(centralizer ({β} : Set G)) (QuotientGroup.mk ⟨z, hz⟩))
    (hBD : BetaData65 E β) (hh67 : ∀ g : G, g * z * g⁻¹ ∈ S → g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z * t)
    {ε : G} (hε : ε = 1 ∨ ε = t)
    (hpair : ∀ x ∈ E, ∀ y ∈ E, ∀ w w', IsLift h hα α x w → IsLift h hα α y w' →
      w * w' * w⁻¹ * w'⁻¹ = iota (α * ε) (x * y * x⁻¹ * y⁻¹) ∧
      w * (z * w' * z⁻¹) * w⁻¹ * (z * w' * z⁻¹)⁻¹ = iota ε (x * y * x⁻¹ * y⁻¹)) : ε = 1 := by
  rcases hε with hε | hε
  · exact hε
  exfalso
  subst hε
  obtain ⟨hz, hWreath⟩ := hWr
  have hB : β ∈ B := h.conf.beta_mem
  have hβ3 : orderOf β = 3 := h.conf.beta_order
  have hβt : β * ε = ε * β := mem_centralizer_singleton_iff.1 (h.conf.B_cent hB)
  obtain ⟨d₁, hd₁, d₂, hd₂, hne⟩ := exists_noncomm_inf_centralizer h.wf (h.conf.B_le hB) hβt hβ3
  have hfix : ∀ d ∈ E ⊓ centralizer ({β} : Set G), β * d * β⁻¹ = d := by
    intro d hd
    have hc : d * β = β * d := mem_centralizer_singleton_iff.1 hd.2
    calc β * d * β⁻¹ = d * β * β⁻¹ := by rw [← hc]
      _ = d := by group
  obtain ⟨g₁, hg₁, hg₁β⟩ := h.exists_fixed_lift hα hF hB hβ3 hd₁.1 (hfix d₁ hd₁)
  obtain ⟨g₂, hg₂, hg₂β⟩ := h.exists_fixed_lift hα hF hB hβ3 hd₂.1 (hfix d₂ hd₂)
  have hd12 : d₁ * d₂ * d₁⁻¹ * d₂⁻¹ = ε := by
    have h1 : d₁ * d₂ * d₁⁻¹ * d₂⁻¹ ≠ 1 := fun h1 => hne (cmt_eq_one_iff.1 h1)
    exact (h.conf.econfig.comm d₁ hd₁.1 d₂ hd₂.1).resolve_left h1
  have hti : ε⁻¹ = ε := inv_eq_of_mul_eq_one_right h.t_sq
  have hd21 : d₂ * d₁ * d₂⁻¹ * d₁⁻¹ = ε := by
    have : d₂ * d₁ * d₂⁻¹ * d₁⁻¹ = (d₁ * d₂ * d₁⁻¹ * d₂⁻¹)⁻¹ := by group
    rw [this, hd12, hti]
  have hzz : ∀ w : G, z * (z * w * z⁻¹) * z⁻¹ = w := fun w => by
    calc z * (z * w * z⁻¹) * z⁻¹ = (z * z) * w * (z * z)⁻¹ := by group
      _ = w := by rw [h.z_sq]; group
  have hzαt : z * (α * ε) * z⁻¹ = α := by
    calc z * (α * ε) * z⁻¹ = (z * α * z⁻¹) * (z * ε * z⁻¹) := by group
      _ = α * ε * ε := by rw [h.z_conj_alpha hα, h.z_conj_t]
      _ = α := by rw [mul_assoc, h.t_sq, mul_one]
  have P12 := hpair d₁ hd₁.1 d₂ hd₂.1 g₁ g₂ hg₁ hg₂
  have P21 := hpair d₂ hd₂.1 d₁ hd₁.1 g₂ g₁ hg₂ hg₁
  have P11 := hpair d₁ hd₁.1 d₁ hd₁.1 g₁ g₁ hg₁ hg₁
  have P22 := hpair d₂ hd₂.1 d₂ hd₂.1 g₂ g₂ hg₂ hg₂
  have e11 : d₁ * d₁ * d₁⁻¹ * d₁⁻¹ = 1 := by group
  have e22 : d₂ * d₂ * d₂⁻¹ * d₂⁻¹ = 1 := by group
  have T12 : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = α * ε := by
    have := P12.1
    rwa [hd12, iota_of_ne h.t_ne] at this
  have T34 : (z * g₁ * z⁻¹) * (z * g₂ * z⁻¹) * (z * g₁ * z⁻¹)⁻¹ * (z * g₂ * z⁻¹)⁻¹ = α := by
    have : (z * g₁ * z⁻¹) * (z * g₂ * z⁻¹) * (z * g₁ * z⁻¹)⁻¹ * (z * g₂ * z⁻¹)⁻¹ =
        z * (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) * z⁻¹ := by group
    rw [this, T12, hzαt]
  have T14 : g₁ * (z * g₂ * z⁻¹) * g₁⁻¹ * (z * g₂ * z⁻¹)⁻¹ = ε := by
    have := P12.2
    rwa [hd12, iota_of_ne h.t_ne] at this
  have T23 : g₂ * (z * g₁ * z⁻¹) * g₂⁻¹ * (z * g₁ * z⁻¹)⁻¹ = ε := by
    have := P21.2
    rwa [hd21, iota_of_ne h.t_ne] at this
  have T13 : g₁ * (z * g₁ * z⁻¹) = (z * g₁ * z⁻¹) * g₁ := by
    have := P11.2
    rw [e11, iota_one] at this
    exact cmt_eq_one_iff.1 this
  have T24 : g₂ * (z * g₂ * z⁻¹) = (z * g₂ * z⁻¹) * g₂ := by
    have := P22.2
    rw [e22, iota_one] at this
    exact cmt_eq_one_iff.1 this
  have hzβ : Commute z β := mem_centralizer_singleton_iff.1 hz
  have hzβ' : Commute z⁻¹ β := hzβ.inv_left
  have hg₁c : Commute g₁ β := hg₁β
  have hg₂c : Commute g₂ β := hg₂β
  have hh₁c : Commute (z * g₁ * z⁻¹) β := (hzβ.mul_left hg₁c).mul_left hzβ'
  have hh₂c : Commute (z * g₂ * z⁻¹) β := (hzβ.mul_left hg₂c).mul_left hzβ'
  have hαβ : Commute α β := (h.BS β hB α hα.mem).symm
  have htβ : Commute ε β := (mem_centralizer_singleton_iff.1 (h.conf.B_cent hB)).symm
  have hQg₁ := hg₁.1
  have hQg₂ := hg₂.1
  have hQh₁ := h.z_norm_Qs hα hQg₁
  have hQh₂ := h.z_norm_Qs hα hQg₂
  obtain ⟨z', hz'⟩ : ∃ z' : ↥(centralizer ({β} : Set G)), (z' : G) = z := ⟨⟨z, hz⟩, rfl⟩
  obtain ⟨α', hα'⟩ : ∃ α' : ↥(centralizer ({β} : Set G)), (α' : G) = α :=
    ⟨⟨α, mem_centralizer_singleton_iff.2 hαβ.eq⟩, rfl⟩
  obtain ⟨t', ht'⟩ : ∃ t' : ↥(centralizer ({β} : Set G)), (t' : G) = ε :=
    ⟨⟨ε, mem_centralizer_singleton_iff.2 htβ.eq⟩, rfl⟩
  obtain ⟨g₁', hg₁'⟩ : ∃ g₁' : ↥(centralizer ({β} : Set G)), (g₁' : G) = g₁ :=
    ⟨⟨g₁, mem_centralizer_singleton_iff.2 hg₁c.eq⟩, rfl⟩
  obtain ⟨g₂', hg₂'⟩ : ∃ g₂' : ↥(centralizer ({β} : Set G)), (g₂' : G) = g₂ :=
    ⟨⟨g₂, mem_centralizer_singleton_iff.2 hg₂c.eq⟩, rfl⟩
  obtain ⟨h₁', hh₁'⟩ : ∃ h₁' : ↥(centralizer ({β} : Set G)), (h₁' : G) = z * g₁ * z⁻¹ :=
    ⟨⟨z * g₁ * z⁻¹, mem_centralizer_singleton_iff.2 hh₁c.eq⟩, rfl⟩
  obtain ⟨h₂', hh₂'⟩ : ∃ h₂' : ↥(centralizer ({β} : Set G)), (h₂' : G) = z * g₂ * z⁻¹ :=
    ⟨⟨z * g₂ * z⁻¹, mem_centralizer_singleton_iff.2 hh₂c.eq⟩, rfl⟩
  have hzK : ∀ (a b : ↥(centralizer ({β} : Set G))), (a : G) = b → a = b := fun a b hab =>
    Subtype.ext hab
  refine no_table_in_wreath (K := ↥(centralizer ({β} : Set G))) (z := z') (α := α') (t := t')
    (g₁ := g₁') (g₂ := g₂') (h₁ := h₁') (h₂ := h₂') ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  ·
    have hz'eq : z' = ⟨z, hz⟩ := Subtype.ext hz'
    rw [hz'eq]
    exact hWreath
  · apply Subtype.ext; simpa [hz'] using h.z_sq
  · apply Subtype.ext; simpa [hα'] using hα.sq
  · apply Subtype.ext; simpa [ht'] using h.t_sq
  · intro e; exact hα.ne_one (by simpa [hα'] using congrArg Subtype.val e)
  · intro e; exact h.t_ne (by simpa [ht'] using congrArg Subtype.val e)
  · intro e; exact hα.ne_t (by rw [← hα', ← ht']; exact congrArg Subtype.val e)
  · apply Subtype.ext
    simpa [hα', ht'] using h.t_comm_S α hα.mem
  · apply Subtype.ext
    simpa [hz', hα', ht'] using h.z_conj_alpha hα
  · apply Subtype.ext
    simpa [hz', ht'] using h.z_conj_t
  · have hmem : t' ∈ (E ⊓ centralizer ({β} : Set G)).subgroupOf (centralizer ({β} : Set G)) := by
      rw [mem_subgroupOf, ht']
      exact ⟨h.t_mem_E, mem_centralizer_singleton_iff.2 htβ.eq⟩
    exact hBD.2 hmem
  · intro g hg
    have e1 := congrArg Subtype.val hg
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hz', hα'] at e1
    rcases hh67 (g : G) (by rw [e1]; exact hα.mem) with h1 | h1
    · exact hα.ne_z (by rw [← e1, h1])
    · exact hα.ne_zt (by rw [← e1, h1])
  ·
    have hQ2 : IsPGroup 2 (Fsub h hα) := h.F_pgroup hα
    have hQβ : IsPGroup 2 ((Fsub h hα ⊓ centralizer ({α} : Set G)).subgroupOf
        (centralizer ({β} : Set G))) := (hQ2.to_le inf_le_left).comap_subtype
    refine hQβ.to_le ?_
    rw [Subgroup.closure_le]
    intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rw [SetLike.mem_coe, mem_subgroupOf]
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hα']; exact (h.Zg_cent_Q hα (h.alpha_mem_Zg hα)).1
    · rw [ht']; exact (h.Zg_cent_Q hα (h.t_mem_Zg hα)).1
    · rw [hg₁']; exact hQg₁
    · rw [hg₂']; exact hQg₂
    · rw [hh₁']; exact hQh₁
    · rw [hh₂']; exact hQh₂
  · intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hα']
    rcases hc with rfl | rfl | rfl | rfl
    · rw [hg₁']; exact mem_centralizer_singleton_iff.1 hQg₁.2
    · rw [hg₂']; exact mem_centralizer_singleton_iff.1 hQg₂.2
    · rw [hh₁']; exact mem_centralizer_singleton_iff.1 hQh₁.2
    · rw [hh₂']; exact mem_centralizer_singleton_iff.1 hQh₂.2
  · intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    apply Subtype.ext
    simp only [Subgroup.coe_mul, ht']
    have hεZ := h.t_mem_Zg hα
    rcases hc with rfl | rfl | rfl | rfl
    · rw [hg₁']; exact ((h.Zg_cent_Q hα hεZ).2 g₁ hQg₁).symm
    · rw [hg₂']; exact ((h.Zg_cent_Q hα hεZ).2 g₂ hQg₂).symm
    · rw [hh₁']; exact ((h.Zg_cent_Q hα hεZ).2 _ hQh₁).symm
    · rw [hh₂']; exact ((h.Zg_cent_Q hα hεZ).2 _ hQh₂).symm
  · intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    have hcQ : (c : G) ∈ Fsub h hα ⊓ centralizer ({α} : Set G) := by
      rcases hc with rfl | rfl | rfl | rfl
      · rw [hg₁']; exact hQg₁
      · rw [hg₂']; exact hQg₂
      · rw [hh₁']; exact hQh₁
      · rw [hh₂']; exact hQh₂
    have key : c * c = 1 ∨ c * c = t' ∨ c * c = α' ∨ c * c = α' * t' := by
      rcases h.QF_sq hα hcQ with e | e | e | e
      · left; apply Subtype.ext; simpa using e
      · right; left; apply Subtype.ext; simpa [ht'] using e
      · right; right; left; apply Subtype.ext; simpa [hα'] using e
      · right; right; right; apply Subtype.ext; simpa [hα', ht'] using e
    rcases key with e | e | e | e
    · rw [e]; exact one_mem _
    · rw [e]; exact mem_sup_right (mem_zpowers _)
    · rw [e]; exact mem_sup_left (mem_zpowers _)
    · rw [e]; exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))
  · apply Subtype.ext
    simpa [hg₁', hg₂', hα', ht'] using T12
  · apply Subtype.ext
    simpa [hh₁', hh₂', hα'] using T34
  · apply Subtype.ext
    simpa [hg₁', hh₂', ht'] using T14
  · apply Subtype.ext
    simpa [hg₂', hh₁', ht'] using T23
  · apply Subtype.ext
    simpa [hg₁', hh₁'] using T13
  · apply Subtype.ext
    simpa [hg₂', hh₂'] using T24

theorem lemma610Cl {α : G} (hα : AlphaSpec S z t α) :
    Lemma610Cl E S B z t α (Fsub h hα) :=
  ⟨h.U_le_Fsub hα, h.Fsub_le_M hα, fun _ hg _ hf => h.Fsub_normal hα hg hf, h.card_Fsub hα,
    (by intro K hKM hKn hK2 k hk; exact h.normal_two_le_F hα hKM hKn hK2 hk),
    fun _ hb hbF => h.B_inf_F hα hb hbF, fun _ hm => h.M_eq_FB hα hm, h.CFz_eq hα,
    h.card_QF hα, fun _ hg _ hq => h.QF_normal hα hg hq,
    fun _ hm hmα => h.CMalpha_eq hα hm hmα, fun _ => h.center_QF hα,
    fun _ hq _ hq' => h.QF_comm hα hq hq', fun _ hq => h.QF_sq hα hq⟩

theorem lemma611 (hF : EFacts611 E t)
    (hWr : ∃ hz : z ∈ centralizer ({β} : Set G),
      WreathAlt ↥(centralizer ({β} : Set G)) (QuotientGroup.mk ⟨z, hz⟩))
    (hBD : BetaData65 E β) : Lemma611Out E S B z t := by
  intro α hα
  obtain ⟨ε, hε, hpair⟩ := h.pairing_structure hα hF
  have hε1 : ε = 1 := h.eps_eq_one hα hF hWr hBD h.h67 hε hpair
  subst hε1
  refine ⟨Fsub h hα, Wsub h hα (zpowers α), Wsub h hα (zpowers (α * t)), h.lemma610Cl hα,
    h.lemma611Cl_of_pairing hα hF ?_⟩
  intro x hx y hy w w' hw hw'
  obtain ⟨h1, h2⟩ := hpair x hx y hy w w' hw hw'
  rw [mul_one] at h1
  exact ⟨h1, by rw [h2, iota_one_left]⟩

end Hyp69

end CFSG.EvenSporadicStandard.Fin76b
