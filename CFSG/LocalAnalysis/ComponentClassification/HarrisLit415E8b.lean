module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415E8a
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415V

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd

namespace L415

theorem card_le_four {α : Type*} [DecidableEq α] (a b c d : α) :
    ({a, b, c, d} : Finset α).card ≤ 4 := by
  calc ({a, b, c, d} : Finset α).card ≤ ({b, c, d} : Finset α).card + 1 :=
        Finset.card_insert_le _ _
    _ ≤ (({c, d} : Finset α).card + 1) + 1 := by gcongr; exact Finset.card_insert_le _ _
    _ ≤ (2 + 1) + 1 := by gcongr; exact Finset.card_le_two

end L415

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ} {hs : Setting46e t L p f S w z V i j}
  {Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} {W : Subgroup X} {z₁ : X}

namespace Config415

variable (hc : Config415 hs Kb₁ Kb₂ W z₁)
include hc

theorem mem_X_cases {c : X} (hcX : c ∈ closure {t, w ^ (orderOf w / 2), z}) :
    c ∈ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊔ zpowers z ∨
      t * c ∈ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊔ zpowers z := by
  have hσ := hs.setup
  by_cases h1 : c ∈ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊔ zpowers z
  · exact Or.inl h1
  right
  have hle : zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊔ zpowers z ≤
      closure {t, w ^ (orderOf w / 2), z} := by
    rw [← hc.inf_X_centralizer]
    exact inf_le_left
  set H := (zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊔ zpowers z).subgroupOf
    (closure {t, w ^ (orderOf w / 2), z}) with hH
  have hH2 : H.index = 2 := by
    have h2 := H.index_mul_card
    have h3 : Nat.card H = 4 := by
      rw [hH, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, hc.card_beta_z]
    rw [h3, hσ.card_X] at h2
    omega
  have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have htH : (⟨t, htX⟩ : ↥(closure {t, w ^ (orderOf w / 2), z})) ∉ H := by
    intro h2
    have h3 : t ∈ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊔ zpowers z := h2
    rw [← hc.inf_X_centralizer] at h3
    exact hc.t_not_comm (mem_centralizer_singleton_iff.mp (mem_inf.mp h3).2)
  have hcH : (⟨c, hcX⟩ : ↥(closure {t, w ^ (orderOf w / 2), z})) ∉ H := h1
  have h4 := (Subgroup.mul_mem_iff_of_index_two hH2).mpr (iff_of_false htH hcH)
  exact h4

theorem eight_le_of_conj_mem (hKC : AutPSL2CentralizerInput) {s : Finset X}
    (hsW : ∀ g ∈ W, g * t * g⁻¹ ∈ s) : 8 ≤ s.card := by
  classical
  have hσ := hs.setup
  have h1 := L415.card_le_of_fiber (A := W) (K := centralizer {t}) (fun g => g * t * g⁻¹)
    (fun a _ a' _ h => by
      rw [mem_centralizer_singleton_iff]
      calc a⁻¹ * a' * t = a⁻¹ * (a' * t * a'⁻¹) * a' := by group
        _ = a⁻¹ * (a * t * a⁻¹) * a' := by rw [← h]
        _ = t * (a⁻¹ * a') := by group) s hsW
  rw [hσ.inf_W_t hKC hs.beta hc.isSylowOf_W hc.U_le] at h1
  have h2 := hc.card_le
  have h3 : 0 < Nat.card ↥(zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) := Nat.card_pos
  by_contra h4
  push Not at h4
  have h5 : Nat.card W ≤ Nat.card ↥(zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) * 7 :=
    h1.trans (Nat.mul_le_mul_left _ (by omega))
  omega

theorem nab_cen :
    (∃ a ∈ barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) W ⊓ Kb₁,
      ∃ b ∈ barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) W ⊓ Kb₁,
        a * b ≠ b * a) ∧
    (∀ c ∈ barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) W ⊓ Kb₁,
      (∀ d ∈ barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) W ⊓ Kb₁,
        c * d = d * c) →
        c = 1 ∨ c = QuotientGroup.mk ⟨z₁, hc.isSylowOf_W.le hc.z₁_mem⟩) := by
  have hσ := hs.setup
  have h45 := hs.lemma45
  obtain ⟨m, hm, ⟨eDs⟩⟩ := h45.dihedral_Dstar
  have hzc : ∀ d ∈ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j),
      z * d = d * z := by
    intro d hd
    have hz : z ∈ (S ⊓ L) ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X) := by
      rw [hσ.center_D]
      exact mem_zpowers z
    exact ((Subgroup.mem_centralizer_iff.mp (mem_inf.mp hz).2) d (mem_inf.mp hd).1).symm
  have hW₀z₂ : ∀ y ∈ W, y * z₁ = z₁ * y → y * (t * z₁ * t⁻¹) = (t * z₁ * t⁻¹) * y :=
    fun y hy hyz => mem_centralizer_singleton_iff.mp
      (hc.W₀_le_z₂ (mem_inf.mpr ⟨hy, mem_centralizer_singleton_iff.mpr hyz⟩))
  obtain ⟨h1, h2, -⟩ := L415.exists_B₀_of (hc.isSylowOf_W.le hc.t_mem_W)
    (by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]) hc.prod hc.isSylowOf_W
    hc.t_mem_W hc.z₁_mem hc.sq_z₁ hc.z₁_ne hc.z_eq hc.mk_z₁ hc.comm_iff hc.mul_t hW₀z₂
    hc.Dstar_le_W hc.isSylowOf_Dstar_bar hm eDs h45.z_mem hzc
  exact ⟨h1, h2⟩

theorem le_W₀_of_abelian {B : Subgroup X} (hBW : B ≤ W) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBn : ∀ g ∈ W, ∀ b ∈ B, g * b * g⁻¹ ∈ B) : B ≤ W ⊓ centralizer {z₁} := by
  set M := centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) with hMdef
  have hWM : W ≤ M := hc.isSylowOf_W.le
  have hE : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := by
    have := LocalCores.layer_characteristic (G := MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    infer_instance
  set Bb := barOf M B with hBb
  have hBbc : ∀ a ∈ Bb, ∀ b ∈ Bb, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBc x hx y hy)
  have hBbn : ∀ d ∈ barOf M W ⊓ Kb₁, ∀ b ∈ Bb, d * b * d⁻¹ ∈ Bb := by
    rintro _ hd _ ⟨y, hy, rfl⟩
    obtain ⟨g, hg, rfl⟩ := (mem_inf.mp hd).1
    exact ⟨g * y * g⁻¹, hBn g hg y hy, by simp only [map_mul, map_inv]⟩
  intro x hx
  have hxW := hBW hx
  have hxb : (QuotientGroup.mk ⟨x, hWM hxW⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈ Bb :=
    mk_mem_barOf (hWM hxW) hx
  have h1 := hc.prod.map_K₁_of_abelian hE hBbc hBbn hc.nab_cen.1 hxb
  exact mem_inf.mpr ⟨hxW, mem_centralizer_singleton_iff.mpr
    ((hc.comm_iff x hxW (hWM hxW)).mpr h1)⟩

theorem card_Y₃ :
    Nat.card ↥(zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) ⊔
      zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 8 ∧
    (∀ a ∈ zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) ⊔ zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j),
      ∀ b ∈ zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) ⊔
        zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j), a * b = b * a) ∧
    (∀ a ∈ zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) ⊔
        zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j), a * a = 1) := by
  have hσ := hs.setup
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβdef
  have hz₁2 : z₁ * z₁ = 1 := by rw [← sq]; exact hc.sq_z₁
  have hz₁1 : z₁ ≠ 1 := fun h1 => hc.z₁_ne (by rw [h1]; group)
  have hz₂2 : (t * z₁ * t⁻¹) * (t * z₁ * t⁻¹) = 1 := by
    rw [show t * z₁ * t⁻¹ * (t * z₁ * t⁻¹) = t * (z₁ * z₁) * t⁻¹ by group, hz₁2]
    group
  have hz₂1 : t * z₁ * t⁻¹ ≠ 1 := fun h1 => hz₁1 (by
    calc z₁ = t⁻¹ * (t * z₁ * t⁻¹) * t := by group
      _ = 1 := by rw [h1]; group)
  have hβ2 : β * β = 1 := by rw [← sq]; exact hσ.sq_eq_one_of_mem_X hs.beta.mem_X
  have hz₁W := hc.z₁_mem
  have hz₂W : t * z₁ * t⁻¹ ∈ W := mul_mem (mul_mem hc.t_mem_W hz₁W) (inv_mem hc.t_mem_W)
  obtain ⟨hB₁c, hB₁2⟩ := L415.elem_zpowers hz₁2
  have hz₂B₁ : t * z₁ * t⁻¹ ∉ zpowers z₁ := fun h1 => by
    rcases L415.mem_zpowers_two hz₁2 h1 with h2 | h2
    · exact hz₂1 h2
    · exact hc.z₁_ne h2.symm
  obtain ⟨hB₂c, hB₂2, hB₂⟩ := L415.elem_sup hB₁c hB₁2 hz₂2 hz₂B₁ (fun a ha => by
    rcases L415.mem_zpowers_two hz₁2 ha with rfl | rfl
    · simp
    · exact hc.z₁_comm_z₂)
  have hB₂W : zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) ≤ W :=
    sup_le (zpowers_le.mpr hz₁W) (zpowers_le.mpr hz₂W)
  obtain ⟨hB₃c, hB₃2, hB₃⟩ := L415.elem_sup hB₂c hB₂2 hβ2 hc.beta_not_mem (fun a ha =>
    hc.comm_beta (hB₂W ha))
  refine ⟨?_, hB₃c, hB₃2⟩
  rw [hB₃, hB₂, L415.card_zpowers_two hz₁2 hz₁1]

theorem inf_centralizer_Y₃ {𝒱 : Subgroup X} (h𝒱 : IsSylowOf 2 𝒱 ⊤) (hW𝒱 : W ≤ 𝒱) :
    𝒱 ⊓ centralizer ((zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) ⊔
      zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) : Subgroup X) : Set X) =
      W ⊓ centralizer {z₁} := by
  apply le_antisymm
  · intro x hx
    have hx𝒱 := (mem_inf.mp hx).1
    have hxc := Subgroup.mem_centralizer_iff.mp (mem_inf.mp hx).2
    have hxβ : x ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
      mem_centralizer_singleton_iff.mpr (hxc _ (mem_sup_right (mem_zpowers _))).symm
    have hxW : x ∈ W := by
      rw [← hc.inf_V_beta h𝒱 hW𝒱]
      exact mem_inf.mpr ⟨hx𝒱, hxβ⟩
    exact mem_inf.mpr ⟨hxW, mem_centralizer_singleton_iff.mpr
      (hxc _ (mem_sup_left (mem_sup_left (mem_zpowers _)))).symm⟩
  · intro x hx
    have hxW := (mem_inf.mp hx).1
    have hxz₁ := mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2
    have hxz₂ := mem_centralizer_singleton_iff.mp (hc.W₀_le_z₂ hx)
    have hxβ := hc.comm_beta hxW
    refine mem_inf.mpr ⟨hW𝒱 hxW, ?_⟩
    have hle : zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) ⊔
        zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≤ centralizer {x} :=
      sup_le (sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxz₁.symm))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxz₂.symm)))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxβ.symm))
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => mem_centralizer_singleton_iff.mp (hle hy)

end Config415

end CFSG.ComponentClassification.HarrisLit
