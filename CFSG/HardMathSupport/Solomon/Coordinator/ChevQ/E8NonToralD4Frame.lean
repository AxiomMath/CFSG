module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToralD4Triples
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoShadow
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.Lift
public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootGroup

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

set_option linter.unusedSectionVars false


section Weyl

variable {τ : Tag} {K : Type} [Field K] {ι : Type} {a : ι → Fin τ.rank → Kˣ}

theorem KernelPosStable.mul {w w' : WeylGroup τ} (hw : KernelPosStable a w)
    (hw' : KernelPosStable a w') : KernelPosStable a (w * w') := by
  intro γ hγ hpos
  obtain ⟨h1, h2⟩ := hw' γ hγ hpos
  rw [mul_smul]
  exact hw _ h1 h2

theorem KernelPosStable.inv {w : WeylGroup τ} (hw : KernelPosStable a w) :
    KernelPosStable a w⁻¹ := by
  set S : Set (Fin τ.rank → ℤ) := {γ | γ ∈ familyKernel a ∧ 0 < height γ} with hS
  have hfin : S.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  have hmaps : Set.MapsTo (fun γ => w • γ) S S := fun γ hγ => hw γ hγ.1 hγ.2
  have hbij := (hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 (MulAction.injective w).injOn
  intro γ hγ hpos
  obtain ⟨δ, hδ, hδγ⟩ := hbij.surjOn ⟨hγ, hpos⟩
  have e : w⁻¹ • γ = δ := by
    rw [← hδγ]
    exact inv_smul_smul w δ
  rw [e]
  exact hδ

theorem mul_mem_familyStabilizer {w w' : WeylGroup τ} (hw : w ∈ familyStabilizer a)
    (hw' : w' ∈ familyStabilizer a) : w * w' ∈ familyStabilizer a := fun i v => by
  rw [mul_smul, hw i, hw' i]

theorem image_smul_mul_eq {S : Set (Fin τ.rank → ℤ)} {u v : WeylGroup τ}
    (hu : (fun α => u • α) '' S = S) (hv : (fun α => v • α) '' S = S) :
    (fun α => (u * v) • α) '' S = S := by
  have e : (fun α : Fin τ.rank → ℤ => (u * v) • α) = (fun α => u • α) ∘ fun α => v • α :=
    funext fun α => mul_smul u v α
  rw [e, Set.image_comp, hv, hu]

theorem image_smul_inv_eq {S : Set (Fin τ.rank → ℤ)} {u : WeylGroup τ}
    (hu : (fun α => u • α) '' S = S) : (fun α => u⁻¹ • α) '' S = S := by
  conv_lhs => rw [← hu, Set.image_image]
  simp only [inv_smul_smul, Set.image_id']

theorem smul_mem_of_image_eq {S : Set (Fin τ.rank → ℤ)} {u : WeylGroup τ}
    (hu : (fun α => u • α) '' S = S) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ S) : u • γ ∈ S :=
  hu ▸ Set.mem_image_of_mem _ hγ

end Weyl

section Reflections

variable {τ : Tag} {L : Type} [Field L] {ι : Type}

theorem mem_familyStabilizer_of_mem_closure {a : ι → Fin τ.rank → Lˣ} {ρ : WeylGroup τ}
    (hρ : ρ ∈ Subgroup.closure (rootReflection '' familyKernel a)) : ρ ∈ familyStabilizer a := by
  intro i
  have hle : Subgroup.closure (rootReflection '' familyKernel a) ≤
      rootCharStabilizerSubgroup (a i) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨γ, hγ, rfl⟩
    exact reflection_mem_stab a hγ.1 hγ.2 i
  exact mem_rootCharStabilizerSubgroup.1 (hle hρ)

end Reflections

theorem e8D4OrthOrbit_conj {L : Type} [Field L] {a : Fin 2 → Fin Tag.E8.rank → Lˣ}
    {ω ρ : WeylGroup Tag.E8} (hρ : ρ ∈ familyStabilizer a) (h : E8D4OrthOrbit a ω) :
    E8D4OrthOrbit a (ρ * ω * ρ⁻¹) := by
  obtain ⟨hcard, hfix, htr, d, hd, h1, h2, h3⟩ := h
  have hK := image_familyKernel hρ
  have hKi := image_smul_inv_eq hK
  have hp : ∀ (n : ℕ) (v : Fin Tag.E8.rank → ℤ),
      (ρ * ω * ρ⁻¹) ^ n • (ρ • v) = ρ • (ω ^ n • v) := fun n v => by
    rw [conj_pow, mul_smul, mul_smul, inv_smul_smul]
  refine ⟨hcard, fun γ hγ => ?_, tripleRefl_transitive_conj (fun α => ⟨smul_mem_of_image_eq hKi,
    fun h' => by simpa using smul_mem_of_image_eq hK h'⟩) htr, ρ • d,
    smul_mem_of_image_eq hK hd, ?_⟩
  · have hγ' : ρ⁻¹ • γ ∈ familyKernel a := smul_mem_of_image_eq hKi hγ
    have eγ : γ = ρ • (ρ⁻¹ • γ) := (smul_inv_smul ρ γ).symm
    have e1 : (ρ * ω * ρ⁻¹) • γ = ρ • (ω • (ρ⁻¹ • γ)) := by
      have := hp 1 (ρ⁻¹ • γ)
      rwa [pow_one, pow_one, ← eγ] at this
    rcases hfix _ hγ' with hf | hf
    · left
      rw [e1, hf, smul_inv_smul]
    · right
      rw [e1, ← iform_smul ρ⁻¹, inv_smul_smul]
      exact hf
  · have e1 := hp 1 d
    have e2 := hp 2 d
    rw [pow_one, pow_one] at e1
    rw [e1, e2, iform_smul, iform_smul, iform_smul]
    exact ⟨h1, h2, h3⟩

section Monomial

variable {τ : Tag} {L : Type} [Field L] {ι : Type}

theorem exists_conj_torus_mul_canonicalRep {t : ModGL τ L} (ht : t ∈ torusGroup τ L)
    (ρ ω : WeylGroup τ) :
    ∃ t₁ ∈ torusGroup τ L, canonicalRep (coxeterSystem τ) L ρ *
        (t * canonicalRep (coxeterSystem τ) L ω) * (canonicalRep (coxeterSystem τ) L ρ)⁻¹ =
      t₁ * canonicalRep (coxeterSystem τ) L (ρ * ω * ρ⁻¹) := by
  obtain ⟨s, hs, hsinv⟩ :=
    E6ThreeInner.exists_torus_mul_canonicalRep_inv (one_mem (torusGroup τ L)) ρ
  obtain ⟨s₁, hs₁, h1⟩ :=
    E6ThreeInner.exists_torus_mul_canonicalRep_mul (one_mem (torusGroup τ L)) ht ρ ω
  obtain ⟨s₂, hs₂, h2⟩ := E6ThreeInner.exists_torus_mul_canonicalRep_mul hs₁ hs (ρ * ω) ρ⁻¹
  rw [one_mul] at hsinv h1
  exact ⟨s₂, hs₂, by rw [h1, hsinv, h2]⟩

theorem units_map_entrywiseHom_mem_torusGroup [IsAlgClosed L] (σ : L →+* L) {t : ModGL τ L}
    (ht : t ∈ torusGroup τ L) : Units.map (entrywiseHom σ) t ∈ torusGroup τ L := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have e : Units.map (entrywiseHom σ) (rootDiagUnit τ l) =
      rootDiagUnit τ fun i => Units.map σ.toMonoidHom (l i) := Units.ext (entrywise_rootDiag σ l)
  rw [e]
  exact rootDiagUnit_mem_torusGroup _

theorem commute_of_conj_entrywise_eq [IsAlgClosed L] (σ' : L →+* L) {t' t₁ : ModGL τ L}
    (ht' : t' ∈ torusGroup τ L) (ht₁ : t₁ ∈ torusGroup τ L) {σ ω : WeylGroup τ}
    (h : t' * canonicalRep (coxeterSystem τ) L σ *
        Units.map (entrywiseHom σ') (t₁ * canonicalRep (coxeterSystem τ) L ω) *
          (t' * canonicalRep (coxeterSystem τ) L σ)⁻¹ =
        t₁ * canonicalRep (coxeterSystem τ) L ω) :
    σ * ω = ω * σ := by
  rw [map_mul, W2.E8Lift.units_map_entrywiseHom_canonicalRep] at h
  have hΦt := units_map_entrywiseHom_mem_torusGroup σ' ht₁
  obtain ⟨s, hs, hsinv⟩ := E6ThreeInner.exists_torus_mul_canonicalRep_inv ht' σ
  obtain ⟨s₁, hs₁, h1⟩ := E6ThreeInner.exists_torus_mul_canonicalRep_mul ht' hΦt σ ω
  obtain ⟨s₂, hs₂, h2⟩ := E6ThreeInner.exists_torus_mul_canonicalRep_mul hs₁ hs (σ * ω) σ⁻¹
  rw [hsinv, h1, h2] at h
  have e := E6ThreeInner.eq_of_torus_mul_canonicalRep_eq hs₂ ht₁ h
  calc σ * ω = σ * ω * σ⁻¹ * σ := by group
    _ = ω * σ := by rw [e]

theorem exists_reframe_mul_canonicalRep [IsAlgClosed L] (a : ι → Fin τ.rank → Lˣ)
    (Fr : L →+* L) {m : ModGL τ L} {x ρ ρ₁ : WeylGroup τ} (hm : m ∈ familyGroup (K := L) a)
    (hρ : ρ ∈ Subgroup.closure (rootReflection '' familyKernel a))
    (hρ₁ : ρ₁ ∈ Subgroup.closure (rootReflection '' familyKernel a)) :
    ∃ m₁ ∈ familyGroup (K := L) a,
      canonicalRep (coxeterSystem τ) L ρ * (m * canonicalRep (coxeterSystem τ) L x) *
          (Units.map (entrywiseHom Fr) (canonicalRep (coxeterSystem τ) L ρ))⁻¹ =
        m₁ * canonicalRep (coxeterSystem τ) L (ρ₁ * (ρ * x * ρ⁻¹)) := by
  rw [W2.E8Lift.units_map_entrywiseHom_canonicalRep]
  have hnρ := canonicalRep_closure_mem_familyGroup a hρ
  have hnρ₁ := canonicalRep_closure_mem_familyGroup a hρ₁
  have hTM : torusGroup τ L ≤ familyGroup (K := L) a := le_sup_left
  obtain ⟨t₁, ht₁, h1⟩ := exists_conj_torus_mul_canonicalRep (one_mem (torusGroup τ L)) ρ x
  rw [one_mul] at h1
  obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (R := L) ρ₁ (ρ * x * ρ⁻¹)
  set nρ := canonicalRep (coxeterSystem τ) L ρ with hnρdef
  set nρ₁ := canonicalRep (coxeterSystem τ) L ρ₁ with hnρ₁def
  refine ⟨nρ * m * nρ⁻¹ * t₁ * nρ₁⁻¹ * k, ?_, ?_⟩
  · exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hnρ hm) (inv_mem hnρ)) (hTM ht₁))
      (inv_mem hnρ₁)) (hTM hk)
  · calc nρ * (m * canonicalRep (coxeterSystem τ) L x) * nρ⁻¹ =
          nρ * m * nρ⁻¹ * (nρ * canonicalRep (coxeterSystem τ) L x * nρ⁻¹) := by group
      _ = nρ * m * nρ⁻¹ * (t₁ * canonicalRep (coxeterSystem τ) L (ρ * x * ρ⁻¹)) := by rw [h1]
      _ = nρ * m * nρ⁻¹ * t₁ * nρ₁⁻¹ *
          (nρ₁ * canonicalRep (coxeterSystem τ) L (ρ * x * ρ⁻¹)) := by group
      _ = nρ * m * nρ⁻¹ * t₁ * nρ₁⁻¹ * k *
          canonicalRep (coxeterSystem τ) L (ρ₁ * (ρ * x * ρ⁻¹)) := by rw [hkk]; group

theorem frobTwistGL_mem_familyGroup_inf_centralizer [IsAlgClosed L] (p : ℕ) [Fact p.Prime]
    [CharP L p] (e : ℕ) (a : ι → Fin τ.rank → Lˣ) {m₁ z₁ : ModGL τ L} {x₁ : WeylGroup τ}
    (hm₁ : m₁ ∈ familyGroup (K := L) a)
    (hx₁ : (fun α => x₁ • α) '' familyKernel a = familyKernel a)
    (hz₁ : frobTwistGL τ L p e (m₁ * canonicalRep (coxeterSystem τ) L x₁) z₁ = z₁) :
    ∀ h ∈ familyGroup (K := L) a ⊓ Subgroup.centralizer {z₁},
      frobTwistGL τ L p e (m₁ * canonicalRep (coxeterSystem τ) L x₁) h ∈
        familyGroup (K := L) a ⊓ Subgroup.centralizer {z₁} := by
  intro h hh
  rw [Subgroup.mem_inf] at hh ⊢
  obtain ⟨hhM, hhC⟩ := hh
  refine ⟨?_, ?_⟩
  · rw [frobTwistGL_apply]
    have hF := entrywiseFrobGL_mem_familyGroup p a e hhM
    have hN : m₁ * canonicalRep (coxeterSystem τ) L x₁ ∈
        Subgroup.normalizer (familyGroup (K := L) a : Set (ModGL τ L)) :=
      mul_mem (Subgroup.le_normalizer hm₁) (canonicalRep_mem_normalizer_of_image hx₁)
    exact (Subgroup.mem_normalizer_iff.1 hN _).1 hF
  · rw [Subgroup.mem_centralizer_singleton_iff] at hhC ⊢
    rw [← hz₁, ← map_mul, ← map_mul, hhC]

end Monomial

theorem twisted_conj_fixed {G : Type*} [Group G] (Φ : G →* G) {ζ y n' n₀ X X' : G}
    (hζ : ζ⁻¹ * (y * n' * Φ ζ * (y * n')⁻¹) = n₀ * y⁻¹)
    (hX : n₀ * (n' * Φ X * n'⁻¹) * n₀⁻¹ = X') :
    y * n' * Φ (ζ * X * ζ⁻¹) * (y * n')⁻¹ = ζ * X' * ζ⁻¹ := by
  have hS : y * n' * Φ ζ * (y * n')⁻¹ = ζ * (n₀ * y⁻¹) := by
    rw [← hζ]
    group
  rw [← hX]
  calc y * n' * Φ (ζ * X * ζ⁻¹) * (y * n')⁻¹ =
        (y * n' * Φ ζ * (y * n')⁻¹) * (y * (n' * Φ X * n'⁻¹) * y⁻¹) *
          (y * n' * Φ ζ * (y * n')⁻¹)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
        group
    _ = ζ * (n₀ * (n' * Φ X * n'⁻¹) * n₀⁻¹) * ζ⁻¹ := by
        rw [hS]
        group

theorem exists_ne_zero_mul_pow_eq {L : Type} [Field L] [IsAlgClosed L] (μ : Lˣ) {q : ℕ}
    (hq : 2 ≤ q) : ∃ t : L, t ≠ 0 ∧ (μ : L) * t ^ q = t := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq ((μ⁻¹ : Lˣ) : L) (by omega : 0 < q - 1)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at ht
    exact (Units.ne_zero _) ht.symm
  refine ⟨t, ht0, ?_⟩
  have hq' : q = (q - 1) + 1 := by omega
  rw [hq', pow_succ, ht, ← mul_assoc, Units.mul_inv, one_mul]

theorem eq_iterateFrobenius {L : Type} [CommRing L] {p : ℕ} [ExpChar L p] {N e : ℕ}
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ N) (hN : N = p ^ e) : Fr = iterateFrobenius L p e :=
  RingHom.ext fun c => by rw [hFr, hN, iterateFrobenius_def]

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

end
