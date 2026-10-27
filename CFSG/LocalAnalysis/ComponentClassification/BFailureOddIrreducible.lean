module

public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.ComponentClassification.BFailureOdd

open CFSG

variable {k P V : Type*} [Field k] [Group P] [AddCommGroup V] [Module k V]

@[expose] def sectionRepresentation (ρ : Representation k P V) (U W : Submodule k V)
    (hU : ∀ g : P, U ≤ U.comap (ρ g)) (hW : ∀ g : P, W ≤ W.comap (ρ g)) :
    Representation k P (W ⧸ U.comap W.subtype) :=
  (ρ.subrepresentation W hW).quotient (U.comap W.subtype) fun g _ hx => hU g hx

theorem eq_one_of_commute_of_isPerfect {M : Type*} [Monoid M] [Group.IsPerfect P]
    (f : P →* M) (hf : ∀ a b : P, f a * f b = f b * f a) (g : P) : f g = 1 := by
  have hle : commutator P ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have h1 : f (a * b * a⁻¹ * b⁻¹) = f b * (f a * f a⁻¹) * f b⁻¹ := by
      rw [map_mul, map_mul, map_mul, hf a b, mul_assoc (f b)]
    rw [MonoidHom.mem_ker, commutatorElement_def, h1, ← map_mul f a, mul_inv_cancel, map_one,
      mul_one, ← map_mul, mul_inv_cancel, map_one]
  exact hle (Group.IsPerfect.commutator_eq_top (G := P) ▸ Subgroup.mem_top g)

theorem commutatorSpan_invariant (ρ : Representation k P V) (X : Submodule k V) (h : P) :
    Submodule.span k {y | ∃ (g : P) (x : V), x ∈ X ∧ ρ g x - x = y} ≤
      (Submodule.span k {y | ∃ (g : P) (x : V), x ∈ X ∧ ρ g x - x = y}).comap (ρ h) := by
  rw [Submodule.span_le]
  rintro _ ⟨g, x, hx, rfl⟩
  have e : ρ h (ρ g x - x) = (ρ (h * g) x - x) - (ρ h x - x) := by
    rw [map_sub, map_mul, Module.End.mul_apply]
    abel
  rw [SetLike.mem_coe, Submodule.mem_comap, e]
  exact sub_mem (Submodule.subset_span ⟨h * g, x, hx, rfl⟩)
    (Submodule.subset_span ⟨h, x, hx, rfl⟩)

theorem perfect_linear_action_nontrivial_irreducible_section [Group.IsPerfect P]
    [FiniteDimensional k V] (ρ : Representation k P V) (hρ : ¬ ρ.IsTrivial) :
    let W : Submodule k V := Submodule.span k {y | ∃ (g : P) (v : V), ρ g v - v = y}
    ∃ hW : ∀ g : P, W ≤ W.comap (ρ g), W ≠ ⊥ ∧
      Submodule.span k {y | ∃ (g : P) (w : V), w ∈ W ∧ ρ g w - w = y} = W ∧
      ∃ (U : Submodule k V) (hU : ∀ g : P, U ≤ U.comap (ρ g)),
        U < W ∧ (sectionRepresentation ρ U W hU hW).IsIrreducible ∧
          ¬ (sectionRepresentation ρ U W hU hW).IsTrivial ∧
          2 ≤ Module.finrank k (W ⧸ U.comap W.subtype) ∧
          (CFSG.IsQuasisimple P →
            CFSG.IsQuasisimple (sectionRepresentation ρ U W hU hW).asGroupHom.range ∧
              (sectionRepresentation ρ U W hU hW).asGroupHom.ker ≤ Subgroup.center P) := by
  intro W
  have hWset : {y | ∃ (g : P) (v : V), ρ g v - v = y} =
      {y | ∃ (g : P) (x : V), x ∈ (⊤ : Submodule k V) ∧ ρ g x - x = y} := by
    ext y
    simp
  have hWinv : ∀ g : P, W ≤ W.comap (ρ g) := by
    intro g
    have := commutatorSpan_invariant ρ ⊤ g
    rwa [← hWset] at this
  have hWne : W ≠ ⊥ := by
    have hρ' : ∃ g : P, ∃ v : V, ρ g v ≠ v := by
      by_contra hcon
      exact hρ ⟨fun g => LinearMap.ext fun v => by_contra fun h => hcon ⟨g, v, h⟩⟩
    obtain ⟨g, v, hv⟩ := hρ'
    intro hbot
    have hmem : ρ g v - v ∈ W := Submodule.subset_span ⟨g, v, rfl⟩
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at hmem
    exact hv hmem
  set W₁ := Submodule.span k {y | ∃ (g : P) (w : V), w ∈ W ∧ ρ g w - w = y} with hW₁def
  have hW₁inv : ∀ g : P, W₁ ≤ W₁.comap (ρ g) := commutatorSpan_invariant ρ W
  have hW₁le : W₁ ≤ W := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, w, hw, rfl⟩
    exact sub_mem (hWinv g hw) hw
  have hWle : W ≤ W₁ := by
    let ρ₁ := ρ.quotient W₁ hW₁inv
    have hcomm : ∀ a b : P, ρ₁ a * ρ₁ b = ρ₁ b * ρ₁ a := by
      intro a b
      apply Submodule.linearMap_qext
      ext v
      change Submodule.Quotient.mk (ρ a (ρ b v)) = Submodule.Quotient.mk (ρ b (ρ a v))
      rw [Submodule.Quotient.eq]
      have e : ρ a (ρ b v) - ρ b (ρ a v) =
          (ρ a (ρ b v - v) - (ρ b v - v)) - (ρ b (ρ a v - v) - (ρ a v - v)) := by
        simp only [map_sub]
        abel
      rw [e]
      exact sub_mem (Submodule.subset_span ⟨a, _, Submodule.subset_span ⟨b, v, rfl⟩, rfl⟩)
        (Submodule.subset_span ⟨b, _, Submodule.subset_span ⟨a, v, rfl⟩, rfl⟩)
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, v, rfl⟩
    have h1 := LinearMap.congr_fun (eq_one_of_commute_of_isPerfect ρ₁ hcomm g)
      (Submodule.Quotient.mk v)
    change Submodule.Quotient.mk (ρ g v) = Submodule.Quotient.mk v at h1
    exact (Submodule.Quotient.eq W₁).1 h1
  have hW₁eq : W₁ = W := le_antisymm hW₁le hWle
  obtain ⟨U, ⟨hUinv, hUW⟩, hUmax⟩ := WellFounded.has_min wellFounded_gt
    {X : Submodule k V | (∀ g : P, X ≤ X.comap (ρ g)) ∧ X < W}
    ⟨⊥, fun _ => bot_le, bot_lt_iff_ne_bot.2 hWne⟩
  have hnontriv : Nontrivial (W ⧸ U.comap W.subtype) := by
    rw [← not_subsingleton_iff_nontrivial, Submodule.Quotient.subsingleton_iff,
      Submodule.comap_subtype_eq_top]
    exact not_le_of_gt hUW
  have hirr : (sectionRepresentation ρ U W hUinv hWinv).IsIrreducible := by
    refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := fun Y => ?_ }
    · intro h
      exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
    · let X : Submodule k V := (Y.toSubmodule.comap (U.comap W.subtype).mkQ).map W.subtype
      have hmemX : ∀ w : W, (w : V) ∈ X ↔ Submodule.Quotient.mk w ∈ Y.toSubmodule := by
        intro w
        constructor
        · rintro ⟨w', hw', hw'w⟩
          rw [← Subtype.ext hw'w]
          exact hw'
        · intro hw
          exact ⟨w, hw, rfl⟩
      have hXW : X ≤ W := Submodule.map_subtype_le _ _
      have hUX : U ≤ X := by
        intro u hu
        refine (hmemX ⟨u, hUW.le hu⟩).2 ?_
        have h0 : (Submodule.Quotient.mk (⟨u, hUW.le hu⟩ : W) : W ⧸ U.comap W.subtype) = 0 :=
          (Submodule.Quotient.mk_eq_zero _).2 hu
        rw [h0]
        exact Y.toSubmodule.zero_mem
      have hXinv : ∀ g : P, X ≤ X.comap (ρ g) := by
        intro g x hx
        obtain ⟨w, hw, rfl⟩ := hx
        exact (hmemX ⟨ρ g w, hWinv g w.2⟩).2 (Y.apply_mem_toSubmodule g hw)
      by_cases hXeq : X = W
      · right
        apply Subrepresentation.ext
        refine eq_top_iff.2 fun z _ => ?_
        obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
        refine (hmemX w).1 ?_
        rw [hXeq]
        exact w.2
      · left
        have hXU : X = U := by
          by_contra hne
          exact hUmax X ⟨hXinv, lt_of_le_of_ne hXW hXeq⟩ (lt_of_le_of_ne hUX (Ne.symm hne))
        apply Subrepresentation.ext
        refine eq_bot_iff.2 fun z hz => ?_
        obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
        rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
        have hwX := (hmemX w).2 hz
        rw [hXU] at hwX
        exact hwX
  have hnontrivU : ¬ (sectionRepresentation ρ U W hUinv hWinv).IsTrivial := by
    intro htriv
    apply not_le_of_gt hUW
    rw [← hW₁eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, w, hw, rfl⟩
    have h1 := LinearMap.congr_fun (htriv.out g)
      (Submodule.Quotient.mk (⟨w, hw⟩ : W) : W ⧸ U.comap W.subtype)
    change (Submodule.Quotient.mk (⟨ρ g w, hWinv g hw⟩ : W) : W ⧸ U.comap W.subtype) =
      Submodule.Quotient.mk (⟨w, hw⟩ : W) at h1
    exact (Submodule.Quotient.eq (U.comap W.subtype)).1 h1
  have hfin : 2 ≤ Module.finrank k (W ⧸ U.comap W.subtype) := by
    have hpos : 0 < Module.finrank k (W ⧸ U.comap W.subtype) :=
      Module.finrank_pos_iff.2 hnontriv
    by_contra hlt
    have h1 : Module.finrank k (W ⧸ U.comap W.subtype) = 1 := by omega
    apply hnontrivU
    refine ⟨fun g => eq_one_of_commute_of_isPerfect _ (fun a b => ?_) g⟩
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h1
      (sectionRepresentation ρ U W hUinv hWinv a)
    obtain ⟨d, hd, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h1
      (sectionRepresentation ρ U W hUinv hWinv b)
    rw [hc, hd]
    ext x
    simp [smul_smul, mul_comm]
  have hquasi : CFSG.IsQuasisimple P →
      CFSG.IsQuasisimple (sectionRepresentation ρ U W hUinv hWinv).asGroupHom.range ∧
        (sectionRepresentation ρ U W hUinv hWinv).asGroupHom.ker ≤ Subgroup.center P := by
    intro hP
    have htrivial_of : ∀ g, (sectionRepresentation ρ U W hUinv hWinv).asGroupHom g = 1 →
        sectionRepresentation ρ U W hUinv hWinv g = LinearMap.id := fun g hg => by
      have h := congrArg Units.val hg
      rw [Representation.asGroupHom_apply] at h
      exact h
    refine ⟨?_, ?_⟩
    · rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hP
        (sectionRepresentation ρ U W hUinv hWinv).asGroupHom with hbot | hq
      · exfalso
        apply hnontrivU
        refine ⟨fun g => htrivial_of g ?_⟩
        rw [MonoidHom.range_eq_bot_iff] at hbot
        rw [hbot]
        rfl
      · exact hq
    · rcases LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hP
        (MonoidHom.normal_ker (sectionRepresentation ρ U W hUinv hWinv).asGroupHom) with
        htop | hc
      · exfalso
        apply hnontrivU
        refine ⟨fun g => htrivial_of g ?_⟩
        have hg : g ∈ (sectionRepresentation ρ U W hUinv hWinv).asGroupHom.ker := by
          rw [htop]
          exact Subgroup.mem_top g
        exact hg
      · exact hc
  exact ⟨hWinv, hWne, hW₁eq, U, hUinv, hUW, hirr, hnontrivU, hfin, hquasi⟩

end CFSG.ComponentClassification.BFailureOdd
