module

public import CFSG.Sporadic.Bridge.J2
public import CFSG.Sporadic.J2
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open TauCeti CFSG.Blueprint CFSG.Sporadic.Bridge

theorem nonempty_mulEquiv_J2_of_relators {G : Type} [Group G]
    (u v : G) (L : Subgroup G) (hL : L = Subgroup.closure ({u, v} : Set G))
    (h1 : u * v * u * v⁻¹ * u⁻¹ * v⁻¹ = 1)
    (h2 : u * v * v * u * v⁻¹ * v⁻¹ * v⁻¹ * v⁻¹ * v⁻¹ = 1)
    (w : G) (hw : w = u * v⁻¹ * u * v⁻¹ * v⁻¹ * v⁻¹ * u * u * u * v⁻¹)
    (h3 : w * w * w * (u * u * u * u * u * u * u) = 1) (hu : u ≠ 1) :
    Nonempty (↥L ≃* NativeSporadic.J2) := by
  subst hL
  set L : Subgroup G := Subgroup.closure ({u, v} : Set G)
  have hu' : u ∈ L := Subgroup.subset_closure (by simp)
  have hv' : v ∈ L := Subgroup.subset_closure (by simp)
  let img : ℕ → ↥L := fun i => if i = 0 then ⟨u, hu'⟩ else ⟨v, hv'⟩
  have himg0 : img 0 = ⟨u, hu'⟩ := by simp [img]
  have himg1 : img 1 = ⟨v, hv'⟩ := by simp [img]
  have hrel : ∀ w ∈ Sporadic.j2Presentation.relatorLetters, wordProd img w = 1 := by
    intro w hw
    rw [J2.relatorLetters_eq] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    apply Subtype.ext
    rw [coe_wordProd]
    rcases hw with rfl | rfl | rfl
    · simpa [wordProd, J2.r₁L, himg0, himg1, mul_assoc] using h1
    · simpa [wordProd, J2.r₂L, himg0, himg1, mul_assoc] using h2
    · subst hw
      simpa [wordProd, J2.r₃L, J2.wL, himg0, himg1, mul_assoc] using h3
  let φ : Sporadic.j2Presentation.Group →* ↥L := presHom Sporadic.j2Presentation img hrel
  have hφ0 : φ (presGen Sporadic.j2Presentation 0) = ⟨u, hu'⟩ := by
    rw [presHom_presGen Sporadic.j2Presentation img hrel (by rw [J2.generatorCount_eq]; norm_num),
      himg0]
  have hφ1 : φ (presGen Sporadic.j2Presentation 1) = ⟨v, hv'⟩ := by
    rw [presHom_presGen Sporadic.j2Presentation img hrel (by rw [J2.generatorCount_eq]; norm_num),
      himg1]
  have hsurj : Function.Surjective φ := by
    refine MonoidHom.range_eq_top.1 ?_
    rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := ({u, v} : Set G))]
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    rcases hx with hx | hx
    · exact ⟨presGen Sporadic.j2Presentation 0, by rw [hφ0]; exact (Subtype.ext hx).symm⟩
    · rw [Set.mem_singleton_iff] at hx
      exact ⟨presGen Sporadic.j2Presentation 1, by rw [hφ1]; exact (Subtype.ext hx).symm⟩
  obtain ⟨e⟩ : Nonempty (NativeSporadic.J2 ≃* Sporadic.j2Presentation.Group) :=
    J2.nonempty_mulEquiv
  haveI : IsSimpleGroup Sporadic.j2Presentation.Group :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 e.symm
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      have hmem : presGen Sporadic.j2Presentation 0 ∈ φ.ker := by rw [h]; exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker, hφ0] at hmem
      exact hu (congrArg Subtype.val hmem)
  exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm.trans e.symm⟩

theorem J2_facts_of_equiv {T : Type} [Group T]
    (e : T ≃* NativeSporadic.J2) :
    IsSimpleGroup T ∧ Nat.card T = 604800 ∧ ∃ a b : T, a * b ≠ b * a := by
  have hs : IsSimpleGroup T := @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 e
  have hc : Nat.card T = 604800 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J2.card_J2
  refine ⟨hs, hc, ?_⟩
  by_contra hab
  push_neg at hab
  haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  letI : CommGroup T := { ‹Group T› with mul_comm := fun a b => hab a b }
  have hp := IsSimpleGroup.prime_card (α := T)
  rw [hc] at hp
  exact absurd hp (by norm_num)

end CFSG.HardMathSupport.Dickson.I271.TabCo1
