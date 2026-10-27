module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2Offender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3Pgl
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X3

section General

variable {p : ℕ} [hpf : Fact p.Prime]

@[expose] noncomputable def p2ToPGL (p : ℕ) [Fact p.Prime] :
    projectiveSL 2 (ZMod p) →* PGL2 (ZMod p) :=
  (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p)).comp
    (p2Equiv (ZMod p)).toMonoidHom

theorem p2ToPGL_injective : Function.Injective (p2ToPGL p) :=
  Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp (p2Equiv (ZMod p)).injective

theorem mem_pglS_iff {x : PGL2 (ZMod p)} : x ∈ pglS (ZMod p) ↔ ∃ s : projectiveSL 2 (ZMod p),
    p2ToPGL p s = x := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨s, rfl⟩ := (p2Equiv (ZMod p)).surjective y
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨p2Equiv (ZMod p) s, rfl⟩

theorem isElementaryAbelian_two_of {G : Type*} [Group G] {B : Subgroup G}
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ a ∈ B, a * a = 1) :
    CFSG.IsElementaryAbelian 2 B := CFSG.IsElementaryAbelian.two_of_forall_mul_self hBc hB2

theorem pgl2_general_offender_actor
    (hp5 : 5 ≤ p) {E : Type*} [AddCommGroup E]
    [Module (ZMod 2) E] [Module.Finite (ZMod 2) E] [Nontrivial E]
    (ρ : PGL2 (ZMod p) →* (E ≃ₗ[ZMod 2] E)) (hE : commSub ρ (pglS (ZMod p)) = ⊤)
    {B : Subgroup (PGL2 (ZMod p))} (hB1 : B ≠ ⊥) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hB2 : ∀ a ∈ B, a * a = 1)
    (hoff : Module.finrank (ZMod 2) E - Module.finrank (ZMod 2) (fixedSub ρ B) ≤
      Nat.log 2 (Nat.card B)) :
    (∀ s ∈ pglS (ZMod p), ρ s = 1 → s = 1) ∧ Module.finrank (ZMod 2) E ≤ 6 ∧
      (p = 5 ∨ p = 7) := by
  have hp2 : p ≠ 2 := by omega
  have hK : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  obtain ⟨-, hidx, -, -, hpair⟩ := projective_involution_pairing (ZMod p) hK
  have : CFSG.IsElementaryAbelian 2 B := isElementaryAbelian_two_of hBc hB2
  have h4 : Nat.card B ≤ 4 := card_le_four_of_elementaryAbelian hK B
  set ρ₀ := ρ.comp (p2ToPGL p) with hρ₀
  have hdisp : ∀ s : projectiveSL 2 (ZMod p), disp ρ₀ s = disp ρ (p2ToPGL p s) := fun s => rfl
  have hE₀ : commSub ρ₀ ⊤ = ⊤ := by
    rw [← hE]
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨s, -, e, rfl⟩
      exact Submodule.subset_span ⟨p2ToPGL p s, mem_pglS_iff.2 ⟨s, rfl⟩, e, rfl⟩
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨x, hx, e, rfl⟩
      obtain ⟨s, rfl⟩ := mem_pglS_iff.1 hx
      exact Submodule.subset_span ⟨s, trivial, e, rfl⟩
  have key : ∃ a : projectiveSL 2 (ZMod p), a ≠ 1 ∧ a * a = 1 ∧
      Module.finrank (ZMod 2) (LinearMap.range (disp ρ₀ a)) ≤ 2 := by
    by_cases hcase : ∃ a ∈ B, a ∈ pglS (ZMod p) ∧ a ≠ 1
    · obtain ⟨a, haB, haS, ha1⟩ := hcase
      obtain ⟨a₀, rfl⟩ := mem_pglS_iff.1 haS
      refine ⟨a₀, fun h => ha1 (by rw [h, map_one]), p2ToPGL_injective ?_, ?_⟩
      · rw [map_mul, map_one]
        exact hB2 _ haB
      · rw [hdisp]
        exact finrank_range_disp_le_of_offender ρ haB
          (hoff.trans ((Nat.log_mono_right h4).trans (by norm_num)))
    · push Not at hcase
      obtain ⟨t, htB, ht1⟩ : ∃ t ∈ B, t ≠ 1 := by
        obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
        exact ⟨t, t.2, fun h => ht (Subtype.ext h)⟩
      have ht2 : t * t = 1 := hB2 t htB
      have htS : t ∉ pglS (ZMod p) := fun h => ht1 (hcase t htB h)
      have hBsub : ∀ b ∈ B, b = 1 ∨ b = t := by
        intro b hb
        by_cases hb1 : b = 1
        · exact Or.inl hb1
        · right
          have hbS : b ∉ pglS (ZMod p) := fun h => hb1 (hcase b hb h)
          have hmem : b * t⁻¹ ∈ pglS (ZMod p) := by
            rw [Subgroup.mul_mem_iff_of_index_two hidx]
            simp [hbS, htS]
          have : b * t⁻¹ = 1 := hcase _ (B.mul_mem hb (B.inv_mem htB)) hmem
          exact mul_inv_eq_one.1 this
      have hcardB : Nat.card B ≤ 2 := by
        have hsub : (B : Set (PGL2 (ZMod p))) ⊆ {1, t} := fun b hb => by
          rcases hBsub b hb with h | h
          · exact Or.inl h
          · exact Or.inr h
        calc Nat.card B = Set.ncard (B : Set (PGL2 (ZMod p))) := (Nat.card_coe_set_eq _).symm
          _ ≤ Set.ncard ({1, t} : Set (PGL2 (ZMod p))) := Set.ncard_le_ncard hsub (Set.toFinite _)
          _ ≤ Set.ncard ({t} : Set (PGL2 (ZMod p))) + 1 := Set.ncard_insert_le _ _
          _ = 2 := by rw [Set.ncard_singleton]
      have hlog : Nat.log 2 (Nat.card B) ≤ 1 := (Nat.log_mono_right hcardB).trans (by norm_num)
      have hrt : Module.finrank (ZMod 2) (LinearMap.range (disp ρ t)) ≤ 1 :=
        finrank_range_disp_le_of_offender ρ htB (hoff.trans hlog)
      obtain ⟨s, hsS, hst, hcomm⟩ := hpair t ht2 ht1
      have hrt' : Module.finrank (ZMod 2) (LinearMap.range (disp ρ (s⁻¹ * t * s))) ≤ 1 := by
        have := finrank_range_disp_conj ρ t s⁻¹
        rw [inv_inv] at this
        rw [this]
        exact hrt
      have ht'S : s⁻¹ * t * s ∉ pglS (ZMod p) := by
        intro h
        apply htS
        have hs' : s⁻¹ ∈ pglS (ZMod p) := (pglS (ZMod p)).inv_mem hsS
        have : t = s * (s⁻¹ * t * s) * s⁻¹ := by group
        rw [this]
        exact (pglS (ZMod p)).mul_mem ((pglS (ZMod p)).mul_mem hsS h) hs'
      have hasS : t * (s⁻¹ * t * s) ∈ pglS (ZMod p) := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx]
        simp [htS, ht'S]
      obtain ⟨a₀, ha₀⟩ := mem_pglS_iff.1 hasS
      have ha1 : t * (s⁻¹ * t * s) ≠ 1 := by
        intro h
        apply hst
        have h1 : s⁻¹ * t * s = t⁻¹ := eq_inv_of_mul_eq_one_right h
        have h2 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
        rw [h1, h2]
      have ha2 : (t * (s⁻¹ * t * s)) * (t * (s⁻¹ * t * s)) = 1 := by
        have hc : t * (s⁻¹ * t * s) = (s⁻¹ * t * s) * t := hcomm.eq
        have hsq : (s⁻¹ * t * s) * (s⁻¹ * t * s) = 1 := by
          calc (s⁻¹ * t * s) * (s⁻¹ * t * s) = s⁻¹ * (t * t) * s := by group
            _ = 1 := by rw [ht2]; group
        calc (t * (s⁻¹ * t * s)) * (t * (s⁻¹ * t * s))
            = t * ((s⁻¹ * t * s) * t) * (s⁻¹ * t * s) := by group
          _ = t * (t * (s⁻¹ * t * s)) * (s⁻¹ * t * s) := by rw [← hc]
          _ = (t * t) * ((s⁻¹ * t * s) * (s⁻¹ * t * s)) := by group
          _ = 1 := by rw [hsq, ht2, mul_one]
      refine ⟨a₀, fun h => ha1 (by rw [← ha₀, h, map_one]), p2ToPGL_injective ?_, ?_⟩
      · rw [map_mul, map_one, ha₀]
        exact ha2
      · rw [hdisp, ha₀]
        exact (finrank_range_disp_mul_le ρ t _).trans (by omega)
  obtain ⟨a, ha1, ha2, hrk⟩ := key
  obtain ⟨hinj, hdim, hp⟩ := p2_actor_of_low_rank_involution hp5 ρ₀ hE₀ ha1 ha2 hrk
  refine ⟨fun s hs hρ => ?_, hdim, hp⟩
  obtain ⟨s₀, rfl⟩ := mem_pglS_iff.1 hs
  have : s₀ = 1 := hinj (by
    show ρ (p2ToPGL p s₀) = ρ (p2ToPGL p 1)
    rw [map_one, map_one]
    exact hρ)
  rw [this, map_one]

end General

end CFSG.QuasithinUnique.Setup.Family
