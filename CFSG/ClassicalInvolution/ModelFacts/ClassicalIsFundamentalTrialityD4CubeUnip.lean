module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4Model

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Generic

theorem mem_sup₃_iff_of_commute {G : Type*} [Group G] {A B C : Subgroup G}
    (hab : ∀ a ∈ A, ∀ b ∈ B, Commute a b) (hac : ∀ a ∈ A, ∀ c ∈ C, Commute a c)
    (hbc : ∀ b ∈ B, ∀ c ∈ C, Commute b c) {g : G} :
    g ∈ A ⊔ B ⊔ C ↔ ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, g = a * b * c := by
  constructor
  · intro hg
    let S : Subgroup G :=
      { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, g = a * b * c}
        mul_mem' := by
          rintro _ _ ⟨a, ha, b, hb, c, hc, rfl⟩ ⟨a', ha', b', hb', c', hc', rfl⟩
          refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', c * c', mul_mem hc hc', ?_⟩
          have h1 : c * a' = a' * c := (hac a' ha' c hc).eq.symm
          have h2 : c * b' = b' * c := (hbc b' hb' c hc).eq.symm
          have h3 : b * a' = a' * b := (hab a' ha' b hb).eq.symm
          calc a * b * c * (a' * b' * c') = a * b * (c * a') * b' * c' := by group
            _ = a * b * (a' * c) * b' * c' := by rw [h1]
            _ = a * (b * a') * c * b' * c' := by group
            _ = a * (a' * b) * c * b' * c' := by rw [h3]
            _ = a * a' * b * (c * b') * c' := by group
            _ = a * a' * b * (b' * c) * c' := by rw [h2]
            _ = a * a' * (b * b') * (c * c') := by group
        one_mem' := ⟨1, one_mem _, 1, one_mem _, 1, one_mem _, by simp⟩
        inv_mem' := by
          rintro _ ⟨a, ha, b, hb, c, hc, rfl⟩
          refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, c⁻¹, inv_mem hc, ?_⟩
          have h1 : a⁻¹ * c⁻¹ = c⁻¹ * a⁻¹ := ((hac a ha c hc).inv_inv).eq
          have h2 : b⁻¹ * c⁻¹ = c⁻¹ * b⁻¹ := ((hbc b hb c hc).inv_inv).eq
          have h3 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := ((hab a ha b hb).inv_inv).eq
          calc (a * b * c)⁻¹ = c⁻¹ * b⁻¹ * a⁻¹ := by group
            _ = c⁻¹ * (b⁻¹ * a⁻¹) := by group
            _ = c⁻¹ * (a⁻¹ * b⁻¹) := by rw [h3]
            _ = (c⁻¹ * a⁻¹) * b⁻¹ := by group
            _ = (a⁻¹ * c⁻¹) * b⁻¹ := by rw [h1]
            _ = a⁻¹ * (c⁻¹ * b⁻¹) := by group
            _ = a⁻¹ * (b⁻¹ * c⁻¹) := by rw [h2]
            _ = a⁻¹ * b⁻¹ * c⁻¹ := by group }
    have hle : A ⊔ B ⊔ C ≤ S := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro y hy
        exact ⟨y, hy, 1, one_mem _, 1, one_mem _, by simp⟩
      · intro y hy
        exact ⟨1, one_mem _, y, hy, 1, one_mem _, by simp⟩
      · intro y hy
        exact ⟨1, one_mem _, 1, one_mem _, y, hy, by simp⟩
    exact hle hg
  · rintro ⟨a, ha, b, hb, c, hc, rfl⟩
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))) (Subgroup.mem_sup_right hc)

theorem mul_comm_rotate {G : Type*} [Group G] {x0 x1 x2 : G} (h01 : Commute x0 x1)
    (h02 : Commute x0 x2) : x1 * x2 * x0 = x0 * x1 * x2 :=
  calc x1 * x2 * x0 = x1 * (x2 * x0) := mul_assoc _ _ _
    _ = x1 * (x0 * x2) := by rw [h02.eq]
    _ = (x1 * x0) * x2 := (mul_assoc _ _ _).symm
    _ = (x0 * x1) * x2 := by rw [h01.eq]

end Generic

section Frobenius

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]

theorem exists_frobTwistGL_diagramMap_pinnedX (t : TwistTag) (e : ℕ) {γ : Fin t.tag.rank → ℤ}
    (hγ : IsRoot t.tag γ) :
    ∃ μ : kˣ, ∀ c : k, frobTwistGL t.tag k p e (diagramMap t k) (pinnedX t.tag k γ c) =
      pinnedX t.tag k (permLattice t.perm γ) ((μ : k) * c ^ (p ^ e)) := by
  obtain ⟨μ, hμ⟩ := wordWeylMatrix_mul_diagramMap_conj_pinnedX (k := k) t [] hγ
  rw [wordWeylMatrix_nil, ToralSign.wordElt_nil, thetaMap_one, one_mul] at hμ
  refine ⟨μ, fun c => ?_⟩
  rw [frobTwistGL_apply, entrywiseFrobGL_pinnedX, hμ, iterateFrobenius_def]

theorem exists_frobTwistGL_diagramMap_pinnedX_d4 (e : ℕ) {γ : Fin d4.rank → ℤ}
    (hγ : IsRoot d4 γ) :
    ∃ μ : kˣ, ∀ c : k, frobTwistGL d4 k p e (diagramMap TwistTag.D4 k) (pinnedX d4 k γ c) =
      pinnedX d4 k (rho γ) ((μ : k) * c ^ (p ^ e)) :=
  exists_frobTwistGL_diagramMap_pinnedX p TwistTag.D4 e hγ

end Frobenius

section Triple

variable {K : Type} [Field K]

theorem pinnedX_eq_coe_xPar_d4 {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (c : K) :
    pinnedX d4 K γ c = ((xPar (rootOperatorFamily d4) γ ((d4Sign γ : K) * c) :
      adjointGroup d4 K) : ModGL d4 K) := by
  rw [coe_xPar_d4 hγ, ← mul_assoc, d4Sign_mul_self, one_mul]

theorem commute_pinnedX_rho {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hne : rho α ≠ α)
    (c d : K) : Commute (pinnedX d4 K α c) (pinnedX d4 K (rho α) d) := by
  rw [pinnedX_eq_coe_xPar_d4 hα, pinnedX_eq_coe_xPar_d4 (isRoot_rho hα)]
  exact (commute_xPar_rho hα hne _ _).map (adjointGroup d4 K).subtype

theorem commute_pinnedX_rho_rho {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hne : rho α ≠ α)
    (c d : K) : Commute (pinnedX d4 K α c) (pinnedX d4 K (rho (rho α)) d) := by
  rw [pinnedX_eq_coe_xPar_d4 hα, pinnedX_eq_coe_xPar_d4 (isRoot_rho (isRoot_rho hα))]
  exact (commute_xPar_rho_rho hα hne _ _).map (adjointGroup d4 K).subtype

theorem pinnedX_rho_mul_inj {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hne : rho α ≠ α)
    {c d f c' d' f' : K}
    (h : pinnedX d4 K α c * pinnedX d4 K (rho α) d * pinnedX d4 K (rho (rho α)) f =
      pinnedX d4 K α c' * pinnedX d4 K (rho α) d' * pinnedX d4 K (rho (rho α)) f') :
    c = c' ∧ d = d' ∧ f = f' := by
  have h1 := isRoot_rho hα
  have h2 := isRoot_rho h1
  rw [pinnedX_eq_coe_xPar_d4 hα, pinnedX_eq_coe_xPar_d4 h1, pinnedX_eq_coe_xPar_d4 h2,
    pinnedX_eq_coe_xPar_d4 hα, pinnedX_eq_coe_xPar_d4 h1, pinnedX_eq_coe_xPar_d4 h2] at h
  have h' : (xPar (rootOperatorFamily d4) α ((d4Sign α : K) * c) *
      xPar (rootOperatorFamily d4) (rho α) ((d4Sign (rho α) : K) * d) *
      xPar (rootOperatorFamily d4) (rho (rho α)) ((d4Sign (rho (rho α)) : K) * f) :
        adjointGroup d4 K) =
      xPar (rootOperatorFamily d4) α ((d4Sign α : K) * c') *
      xPar (rootOperatorFamily d4) (rho α) ((d4Sign (rho α) : K) * d') *
      xPar (rootOperatorFamily d4) (rho (rho α)) ((d4Sign (rho (rho α)) : K) * f') :=
    Subtype.ext h
  obtain ⟨e1, e2, e3⟩ := xPar_rho_mul_inj hα hne h'
  exact ⟨mul_left_cancel₀ (d4Sign_ne_zero α) e1, mul_left_cancel₀ (d4Sign_ne_zero _) e2,
    mul_left_cancel₀ (d4Sign_ne_zero _) e3⟩

variable (K) in
@[expose] noncomputable def tripleGroup (β : Fin d4.rank → ℤ) : Subgroup (ModGL d4 K) :=
  rootSubgroup d4 K β ⊔ rootSubgroup d4 K (rho β) ⊔ rootSubgroup d4 K (rho (rho β))

theorem mem_tripleGroup_iff {β : Fin d4.rank → ℤ} (hβ : IsRoot d4 β) (hne : rho β ≠ β)
    {g : ModGL d4 K} :
    g ∈ tripleGroup K β ↔ ∃ c d f : K,
      g = pinnedX d4 K β c * pinnedX d4 K (rho β) d * pinnedX d4 K (rho (rho β)) f := by
  have hcomm : ∀ (γ δ : Fin d4.rank → ℤ),
      (∀ c d : K, Commute (pinnedX d4 K γ c) (pinnedX d4 K δ d)) →
      ∀ x ∈ rootSubgroup d4 K γ, ∀ y ∈ rootSubgroup d4 K δ, Commute x y := by
    intro γ δ h x hx y hy
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hy
    exact h c d
  have h1 := isRoot_rho hβ
  rw [tripleGroup, mem_sup₃_iff_of_commute
    (hcomm _ _ (commute_pinnedX_rho hβ hne)) (hcomm _ _ (commute_pinnedX_rho_rho hβ hne))
    (hcomm _ _ (commute_pinnedX_rho h1 (rho_rho_ne_rho hne)))]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, rfl⟩
    obtain ⟨a', rfl⟩ := mem_rootSubgroup.1 ha
    obtain ⟨b', rfl⟩ := mem_rootSubgroup.1 hb
    obtain ⟨c', rfl⟩ := mem_rootSubgroup.1 hc
    exact ⟨a', b', c', rfl⟩
  · rintro ⟨c, d, f, rfl⟩
    exact ⟨_, mem_rootSubgroup.2 ⟨c, rfl⟩, _, mem_rootSubgroup.2 ⟨d, rfl⟩, _,
      mem_rootSubgroup.2 ⟨f, rfl⟩, rfl⟩

end Triple

section Count

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]

theorem card_fixedPointsIn_tripleGroup_le {e : ℕ} (he : 1 ≤ e) {β : Fin d4.rank → ℤ}
    (hβ : IsRoot d4 β) (hne : rho β ≠ β) :
    Nat.card (fixedPointsIn (tripleGroup k β)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k))) ≤ (p ^ e) ^ 3 := by
  classical
  have h1 := isRoot_rho hβ
  have h2 := isRoot_rho h1
  obtain ⟨μ₀, hμ₀⟩ := exists_frobTwistGL_diagramMap_pinnedX_d4 (k := k) p e hβ
  obtain ⟨μ₁, hμ₁⟩ := exists_frobTwistGL_diagramMap_pinnedX_d4 (k := k) p e h1
  obtain ⟨μ₂, hμ₂⟩ := exists_frobTwistGL_diagramMap_pinnedX_d4 (k := k) p e h2
  have hρ3 : rho (rho (rho β)) = β := rho_rho_rho β
  set q := p ^ e with hq
  have hq2 : 2 ≤ q := by
    have := (Fact.out : p.Prime).two_le
    calc 2 ≤ p := this
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he
  set μ : kˣ := μ₂ * μ₁ ^ q * μ₀ ^ (q * q) with hμ
  have hμ0 : (μ : k) ≠ 0 := μ.ne_zero
  have hq3 : 2 ≤ q ^ 3 := le_trans hq2 (Nat.le_self_pow (by norm_num) q)
  let P : Polynomial k := Polynomial.C (μ : k) * Polynomial.X ^ (q ^ 3) - Polynomial.X
  have hdeg1 : (Polynomial.C (μ : k) * Polynomial.X ^ (q ^ 3)).natDegree = q ^ 3 :=
    Polynomial.natDegree_C_mul_X_pow _ _ hμ0
  have hlt : (Polynomial.X : Polynomial k).natDegree <
      (Polynomial.C (μ : k) * Polynomial.X ^ (q ^ 3)).natDegree := by
    rw [hdeg1, Polynomial.natDegree_X]
    omega
  have hPdeg : P.natDegree = q ^ 3 := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, hdeg1]
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hPdeg
    omega
  have hmem : ∀ g : fixedPointsIn (tripleGroup k β)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)), g.1 ∈ tripleGroup k β :=
    fun g => (mem_fixedPointsIn.1 g.2).1
  choose a b c hv using fun g : fixedPointsIn (tripleGroup k β)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)) =>
    (mem_tripleGroup_iff hβ hne).1 (hmem g)
  have hrel : ∀ g, b g = (μ₀ : k) * (a g) ^ q ∧ c g = (μ₁ : k) * (b g) ^ q ∧
      a g = (μ₂ : k) * (c g) ^ q := by
    intro g
    have hF := (mem_fixedPointsIn.1 g.2).2
    rw [hv g, map_mul, map_mul, hμ₀, hμ₁, hμ₂, hρ3] at hF
    have h01 := commute_pinnedX_rho (K := k) hβ hne
    have h02 := commute_pinnedX_rho_rho (K := k) hβ hne
    have hF' := (mul_comm_rotate (h01 _ _) (h02 _ _)).symm.trans hF
    obtain ⟨e1, e2, e3⟩ := pinnedX_rho_mul_inj hβ hne hF'
    exact ⟨e2.symm, e3.symm, e1.symm⟩
  have hroot : ∀ g, a g ∈ P.roots.toFinset := by
    intro g
    obtain ⟨r1, r2, r3⟩ := hrel g
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def]
    have hfin : a g = (μ : k) * (a g) ^ (q ^ 3) := by
      calc a g = (μ₂ : k) * (c g) ^ q := r3
        _ = (μ₂ : k) * ((μ₁ : k) * (b g) ^ q) ^ q := by rw [r2]
        _ = (μ₂ : k) * ((μ₁ : k) * ((μ₀ : k) * (a g) ^ q) ^ q) ^ q := by rw [r1]
        _ = (μ : k) * (a g) ^ (q ^ 3) := by
          simp only [hμ, Units.val_mul, Units.val_pow_eq_pow_val]
          have hp : ∀ x y : k, (x * y) ^ q = x ^ q * y ^ q := fun x y => mul_pow x y q
          rw [hp, hp, hp, ← pow_mul, ← pow_mul, ← pow_mul]
          ring_nf
    simp only [P, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [← hfin, sub_self]
  have hinj : Function.Injective fun g => (⟨a g, hroot g⟩ : P.roots.toFinset) := by
    intro g g' h
    have h1 : a g = a g' := congrArg Subtype.val h
    obtain ⟨r1, r2, -⟩ := hrel g
    obtain ⟨r1', r2', -⟩ := hrel g'
    have hb : b g = b g' := by rw [r1, r1', h1]
    have hc : c g = c g' := by rw [r2, r2', hb]
    exact Subtype.ext (by rw [hv g, hv g', h1, hb, hc])
  calc Nat.card (fixedPointsIn (tripleGroup k β)
        (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k))) ≤
        Nat.card P.roots.toFinset := Nat.card_le_card_of_injective _ hinj
    _ = P.roots.toFinset.card := Nat.card_eq_fintype_card.trans (Fintype.card_coe _)
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ = q ^ 3 := hPdeg

end Count

end CFSG.ClassicalInvolution.ModelFacts
