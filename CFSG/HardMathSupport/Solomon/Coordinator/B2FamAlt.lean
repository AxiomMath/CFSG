module

public import CFSG.HardMathSupport.Solomon.Coordinator.B2FamAltCore
public import CFSG.HardMathSupport.Solomon.Coordinator.B2FamAltSix
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamAlt
public import CFSG.CharacterTheory.Burnside

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB Equiv Equiv.Perm

namespace B2FamAlt

theorem exists_perm_of_sq_eq_one {n : ℕ} (hn : 5 ≤ n) (α : MulAut (alternatingGroup (Fin n)))
    (hα : α ^ 2 = 1) :
    (∃ σ : Perm (Fin n), MulAut.conjNormal σ = α ∧ σ ^ 2 = 1) ∨
      Nat.card (fixSubgroup α) = 10 := by
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n (by omega)
  have key : (∃ σ : Perm (Fin n), MulAut.conjNormal σ = α) ∨ Nat.card (fixSubgroup α) = 10 := by
    by_cases h6 : n = 6
    · subst h6
      rcases alt6_involution_conj_or_card_ten (MulEquiv.refl _) hα with ⟨σ, hσ⟩ | h
      · refine Or.inl ⟨σ, ?_⟩
        rw [← hσ]
        exact MulEquiv.ext fun _ => rfl
      · exact Or.inr h
    · exact Or.inl
        ((CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn h6).2 α)
  rcases key with ⟨σ, hσ⟩ | h
  · refine Or.inl ⟨σ, hσ, hinj ?_⟩
    rw [map_pow, hσ, hα, map_one]
  · exact Or.inr h

theorem glaPLayer_eq_bot_of_isSolvable {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X : Subgroup G} [Group.IsSolvable X] : GLAPLayer p X = ⊥ := by
  refine eq_bot_iff.2 (sSup_le fun J hJ g hg => ?_)
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val (hom_eq_one_of_solvable hp hJ (MonoidHom.id X) g hg)

theorem coreA {n : ℕ} {σ : Perm (Fin n)} (hσ : σ ^ 2 = 1) :
    ∀ J : Subgroup (alternatingGroup (Fin n)),
      GLAPComponent 2 (fixSubgroup (MulAut.conjNormal σ : MulAut (alternatingGroup (Fin n)))) J →
      ∀ g ∈ J, ∀ o ∈ GLAPPrimeCoreOf 2
        (fixSubgroup (MulAut.conjNormal σ : MulAut (alternatingGroup (Fin n)))), o * g = g * o := by
  intro J hJ
  set ι : ↥(alternatingGroup (Fin n)) →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype with hι
  have hinj : Function.Injective ι := Subgroup.subtype_injective _
  have hX := fixSubgroup_conjNormal_map σ
  have hc : ∀ y ∈ fixSubgroup (MulAut.conjNormal σ : MulAut ↥(alternatingGroup (Fin n))) ⊓ ι.ker,
      ∀ x ∈ fixSubgroup (MulAut.conjNormal σ : MulAut ↥(alternatingGroup (Fin n))),
        x * y = y * x := by
    intro y hy x _
    have : y = 1 := hinj ((MonoidHom.mem_ker.1 hy.2).trans (map_one ι).symm)
    rw [this, mul_one, one_mul]
  have hJ' : GLAPComponent 2 (B3FamAlt.centAlt σ) (J.map ι) := by
    rw [← hX]
    exact glaPComponent_map_central Nat.prime_two ι hc hJ
  intro g hg o ho
  have hoO : (o : Perm (Fin n)) ∈ GLAPPrimeCoreOf 2 (B3FamAlt.centAlt σ) := by
    rw [← hX, ← CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective 2 ι
      hinj]
    exact ⟨o, ho, rfl⟩
  exact Subtype.ext (core hσ hJ' (g : Perm (Fin n)) ⟨g, hg, rfl⟩ _ hoO)

theorem commutator_layer_eq_bot_A {n : ℕ} (hn : 5 ≤ n)
    (α : MulAut (alternatingGroup (Fin n))) (hα : α ^ 2 = 1) :
    ⁅GLAPLayer 2 (fixSubgroup α), GLAPPrimeCoreOf 2 (fixSubgroup α)⁆ = ⊥ := by
  rcases exists_perm_of_sq_eq_one hn α hα with ⟨σ, rfl, hσ⟩ | h10
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.2
      (sSup_le fun J hJ g hg => Subgroup.mem_centralizer_iff.2 fun o ho =>
        coreA hσ J hJ g hg o ho)
  · have : Fintype (fixSubgroup α) := Fintype.ofFinite _
    have : Group.IsSolvable (fixSubgroup α) :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 1) (b := 1)
        Nat.prime_two Nat.prime_five (by norm_num)
        (by rw [← Nat.card_eq_fintype_card, h10]; norm_num)
    rw [glaPLayer_eq_bot_of_isSolvable Nat.prime_two, Subgroup.commutator_bot_left]

theorem commutator_eq_bot_of_mulEquiv {S T : Type} [Group S] [Group T] [Finite S] [Finite T]
    (e : S ≃* T) (β : MulAut S)
    (h : ⁅GLAPLayer 2 (fixSubgroup (MulAut.congr e β)),
      GLAPPrimeCoreOf 2 (fixSubgroup (MulAut.congr e β))⁆ = ⊥) :
    ⁅GLAPLayer 2 (fixSubgroup β), GLAPPrimeCoreOf 2 (fixSubgroup β)⁆ = ⊥ := by
  let π : S →* T := e.toMonoidHom
  have hπ : Function.Surjective π := e.surjective
  have hker : π.ker ≤ Subgroup.center S := by
    have : π.ker = ⊥ := (MonoidHom.ker_eq_bot_iff π).2 e.injective
    rw [this]; exact bot_le
  have hββ : ∀ k, π (β k) = MulAut.congr e β (π k) := fun k => by simp [π]
  have hLmap : (GLAPLayer 2 (fixSubgroup β)).map π ≤
      GLAPLayer 2 (fixSubgroup (MulAut.congr e β)) :=
    (map_glaPLayer_fixSubgroup_eq π hker β _ hββ hπ Nat.prime_two).le
  have hOmap := map_glaPPrimeCoreOf_fixSubgroup_le π hker β _ hββ hπ Nat.prime_two
  have hcm : (⁅GLAPLayer 2 (fixSubgroup β), GLAPPrimeCoreOf 2 (fixSubgroup β)⁆).map π = ⊥ := by
    rw [Subgroup.map_commutator]
    exact eq_bot_iff.2 (h ▸ Subgroup.commutator_mono hLmap hOmap)
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 hcm

theorem commutator_layer_eq_bot_two {n : ℕ} (hn : 5 ≤ n) {S : Type} [Group S] [Finite S]
    (e : S ≃* alternatingGroup (Fin n)) (β : MulAut S) (hβ : β ^ 2 = 1) :
    ⁅GLAPLayer 2 (fixSubgroup β), GLAPPrimeCoreOf 2 (fixSubgroup β)⁆ = ⊥ := by
  refine commutator_eq_bot_of_mulEquiv e β (commutator_layer_eq_bot_A hn _ ?_)
  show (MulAut.congr e : MulAut S →* MulAut (alternatingGroup (Fin n))) β ^ 2 = 1
  rw [← map_pow, hβ, map_one]

end B2FamAlt

end CFSG.HardMathSupport.Solomon.Coordinator
