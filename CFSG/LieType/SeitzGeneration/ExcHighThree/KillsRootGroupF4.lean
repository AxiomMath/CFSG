module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootGroup

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Steinberg.Adjoint

section KillsRootF4


variable {τ : Tag}

@[expose] def KillsCycleShape (τ : Tag) : Prop :=
  ∀ {M : Type} [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (w : WeylGroup τ),
    (fun α => w • α) '' kernelRoots χ = kernelRoots χ →
    ∀ {α : Fin τ.rank → ℤ}, α ∈ kernelRoots χ →
    ∃ x ∈ Subgroup.closure (rootReflection '' kernelRoots χ), ∃ (n : ℕ) (hn : 0 < n),
      ∃ β : Fin n → Fin τ.rank → ℤ, β ⟨0, hn⟩ = α ∧ (∀ k, β k ∈ kernelRoots χ) ∧
        (∀ i j, i ≠ j → iform (β i) (β j) = 0 ∧ β i ≠ β j ∧ β i ≠ -β j ∧
          ∀ a b : ℕ, 0 < a → 0 < b → ¬ IsRoot τ (a • β i + b • β j)) ∧
        ∀ k : Fin n, (x * w) • β k = β ⟨((k : ℕ) + 1) % n, Nat.mod_lt _ hn⟩

theorem kill_cycle_periodic_of {L : Type} [Field L] {ι : Type} {τ : Tag} (hcyc : KillsCycleShape τ)
    (a : ι → Fin τ.rank → Lˣ) (w : WeylGroup τ)
    (hw : (fun α => w • α) '' familyKernel a = familyKernel a)
    {α : Fin τ.rank → ℤ} (hα : α ∈ familyKernel a) :
    ∃ x ∈ Subgroup.closure (rootReflection '' familyKernel a), ∃ (n : ℕ) (β : ℕ → Fin τ.rank → ℤ),
      0 < n ∧ (∀ k, β (k + n) = β k) ∧ (∀ k, β k ∈ familyKernel a) ∧
      (∀ k l, k < n → l < n → k ≠ l →
        iform (β k) (β l) = 0 ∧ β k ≠ β l ∧ ¬ IsRoot τ (β k + β l)) ∧
      ∀ k, (x * w) • β k = β (k + 1) := by
  have hw' : (fun α => w • α) '' kernelRoots (familyChar a) = kernelRoots (familyChar a) := by
    rw [kernelRoots_familyChar]
    exact hw
  have hα' : α ∈ kernelRoots (familyChar a) := by
    rw [kernelRoots_familyChar]
    exact hα
  obtain ⟨x, hx, n, hn, β, -, hβS, horth, hgβ⟩ := hcyc (familyChar a) w hw' hα'
  rw [kernelRoots_familyChar] at hx hβS
  refine ⟨x, hx, n, fun k => β ⟨k % n, Nat.mod_lt _ hn⟩, hn, ?_, ?_, ?_, ?_⟩
  · intro k
    show β ⟨(k + n) % n, Nat.mod_lt _ hn⟩ = β ⟨k % n, Nat.mod_lt _ hn⟩
    congr 1
    exact Fin.ext (Nat.add_mod_right k n)
  · intro k
    exact hβS _
  · intro k l hk hl hkl
    have hkl' : (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n) ≠ ⟨l % n, Nat.mod_lt _ hn⟩ := by
      intro h
      apply hkl
      have h' := congrArg Fin.val h
      simp only [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hl] at h'
      exact h'
    have h := horth ⟨k % n, Nat.mod_lt _ hn⟩ ⟨l % n, Nat.mod_lt _ hn⟩ hkl'
    refine ⟨h.1, h.2.1, ?_⟩
    have h11 := h.2.2.2 1 1 one_pos one_pos
    simpa using h11
  · intro k
    show (x * w) • β ⟨k % n, Nat.mod_lt _ hn⟩ = β ⟨(k + 1) % n, Nat.mod_lt _ hn⟩
    refine (hgβ ⟨k % n, Nat.mod_lt _ hn⟩).trans ?_
    congr 1
    exact Fin.ext (Nat.mod_add_mod k n 1)

theorem kill_core_of (hcyc : KillsCycleShape τ)
    (K : Type) [Field K] [Finite K] (A : Subgroup (adjointGroup τ K)) (D : LangPlaneData τ K A)
    (α : Fin τ.rank → ℤ) (hα : IsRoot τ α) (hk : D.Kills α) :
    ∃ uL : ModGL τ (AlgebraicClosure K), uL ∈ adjointGroup τ (AlgebraicClosure K) ∧ uL ≠ 1 ∧
      uL ^ ringChar K = 1 ∧ Units.map (entrywiseHom D.Fr) uL = uL ∧
      ∀ y ∈ A, uL * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((D.c * y * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((D.c * y * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) * uL := by
  classical
  obtain ⟨e, he, hcard⟩ := card_eq_pow_ringChar K
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  have hFrEq : D.Fr = iterateFrobenius (AlgebraicClosure K) (ringChar K) e :=
    RingHom.ext fun c => by rw [D.hFr c, iterateFrobenius_def, hcard]
  have hFrob : ∀ g : ModGL τ (AlgebraicClosure K),
      Units.map (entrywiseHom D.Fr) g = entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e g := by
    intro g
    rw [hFrEq]
  have hg0F : entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e D.g0 =
      D.g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w := by
    rw [← hFrob]
    exact D.hg0
  have hBF : ∀ z : ModGL τ K, entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e
      (baseChangeGL (algebraMap K (AlgebraicClosure K)) z) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) z := by
    intro z
    rw [← hFrob]
    exact CFSG.RankThree.PartOne.KE.baseChangeGL_frobenius_fixed D.Fr D.hFr z
  have hk' : ∀ y : A, ∃ a : Fin τ.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit τ a = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((D.c * (y : adjointGroup τ K) * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) * D.g0 ∧
        rootChar a α = 1 := fun y => hk y.1 y.2
  choose a ha using hk'
  have hconj : ∀ y : A, rootDiagUnit τ (a y) =
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w *
        entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e (rootDiagUnit τ (a y)) *
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w)⁻¹ := by
    intro y
    have hF : entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e (rootDiagUnit τ (a y)) =
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w)⁻¹ * rootDiagUnit τ (a y) *
          canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w := by
      rw [(ha y).1, map_mul, map_mul, map_inv, hg0F, hBF]
      group
    rw [hF]
    group
  have hrel : ∀ y : A, ∀ v, rootChar (a y) (D.w • v) = rootChar (a y) v ^ (ringChar K ^ e) :=
    fun y v => rootChar_frob_of_conj (a y) D.w (hconj y) v
  have hαS : α ∈ familyKernel a := ⟨hα, fun y => (ha y).2⟩
  have hSw : ∀ β ∈ familyKernel a, D.w • β ∈ familyKernel a ∧ D.w⁻¹ • β ∈ familyKernel a :=
    fun β hβ => family_w_stab a (fun i v => hrel i v) hβ
  have hwS : (fun β => D.w • β) '' familyKernel a = familyKernel a :=
    image_eq_of_mem_stab _ D.w (fun β hβ => (hSw β hβ).1) (fun β hβ => (hSw β hβ).2)
  obtain ⟨x, hx, n, β, hn, hper, hβS, horth, hgβ⟩ := kill_cycle_periodic_of hcyc a D.w hwS hαS
  have hxstab : ∀ i, x ∈ rootCharStabilizerSubgroup (a i) :=
    fun i => closure_refl_stab a (familyKernel a) (fun γ hγ => hγ) hx i
  have hxM : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) x ∈
      familyGroup (K := AlgebraicClosure K) a :=
    canonicalRep_closure_mem_familyGroup a hx
  have hxw_img : (fun γ => (x * D.w) • γ) '' familyKernel a = familyKernel a := by
    apply image_eq_of_mem_stab
    · intro γ hγ
      rw [mul_smul]
      exact stab_mem_familyKernel a hxstab (hSw γ hγ).1
    · intro γ hγ
      rw [mul_inv_rev, mul_smul]
      exact (hSw _ (stab_mem_familyKernel a (fun i => inv_mem (hxstab i)) hγ)).2
  have hQnorm : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) ∈
      Subgroup.normalizer (familyGroup (K := AlgebraicClosure K) a :
        Set (ModGL τ (AlgebraicClosure K))) :=
    canonicalRep_mem_normalizer_of_image hxw_img
  obtain ⟨k, hk, hkxw⟩ := canonicalRep_mul_mem (R := AlgebraicClosure K) x D.w
  have hQk : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) =
      k⁻¹ * (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) x *
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w) := by
    rw [hkxw]
    group
  have hm_mem : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w *
      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w))⁻¹ ∈
        familyGroup (K := AlgebraicClosure K) a := by
    have hm : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w *
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w))⁻¹ =
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) x)⁻¹ * k := by
      rw [hQk]
      group
    rw [hm]
    exact mul_mem (inv_mem hxM) (torus_le_familyGroup a hk)
  have hn_lang : D.g0⁻¹ * entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e D.g0 =
      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w *
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w))⁻¹) *
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) := by
    rw [hg0F]
    group
  have hLang := lang_familyGroup (ringChar K) a e he _ hQnorm
  obtain ⟨ζ, hζ, hζQ⟩ := exists_mem_lang_conj (entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e)
    hm_mem hn_lang hLang
  have hg1F : entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e (D.g0 * ζ) =
      (D.g0 * ζ) * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) := by
    rw [← hζQ, mul_inv_cancel_left]
  obtain ⟨v, hvM, hvF, hv1, hvp⟩ := exists_cycle_element (L := AlgebraicClosure K) (ringChar K) e he
    (x * D.w) n hn β hper (fun k => (hβS k).1) horth hgβ (familyKernel a) hβS
  have hvM' : v ∈ familyGroup (K := AlgebraicClosure K) a := rootSpan_le_familyGroup a hvM
  have hFvQ : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) *
      entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e v *
      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w))⁻¹ = v := by
    rw [frobTwistGL_apply] at hvF
    exact hvF
  have hFv : entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e v =
      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w))⁻¹ * v *
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) := by
    calc entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e v
        = (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w))⁻¹ *
            (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) *
              entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) e v *
              (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w))⁻¹) *
            canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (x * D.w) := by group
      _ = _ := by rw [hFvQ]
  have hζadj : ζ ∈ adjointGroup τ (AlgebraicClosure K) := familyGroup_le_adjoint a hζ
  have hvadj : v ∈ adjointGroup τ (AlgebraicClosure K) := familyGroup_le_adjoint a hvM'
  refine ⟨(D.g0 * ζ) * v * (D.g0 * ζ)⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_mem (mul_mem (mul_mem D.hg0C hζadj) hvadj) (inv_mem (mul_mem D.hg0C hζadj))
  · intro h
    apply hv1
    calc v = (D.g0 * ζ)⁻¹ * ((D.g0 * ζ) * v * (D.g0 * ζ)⁻¹) * (D.g0 * ζ) := by group
      _ = 1 := by rw [h]; group
  · rw [conj_pow, hvp]
    group
  · rw [hFrob, map_mul, map_mul, map_inv, hg1F, hFv]
    group
  · intro y hy
    obtain ⟨d, hd⟩ : ∃ d, rootDiagUnit τ (a ⟨y, hy⟩) = d := ⟨_, rfl⟩
    have hdy : d = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((D.c * y * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) * D.g0 := by
      rw [← hd]
      exact (ha ⟨y, hy⟩).1
    have hζd : ζ * d = d * ζ := by
      rw [← hd]
      exact familyGroup_comm a ⟨y, hy⟩ hζ
    have hvd : v * d = d * v := by
      rw [← hd]
      exact familyGroup_comm a ⟨y, hy⟩ hvM'
    have hbz : baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((D.c * y * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) =
        (D.g0 * ζ) * d * (D.g0 * ζ)⁻¹ := by
      have hζd' : ζ * d * ζ⁻¹ = d := by
        rw [hζd]
        group
      calc baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((D.c * y * D.c⁻¹ : adjointGroup τ K) : ModGL τ K)
          = D.g0 * (D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((D.c * y * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) * D.g0) * D.g0⁻¹ := by group
        _ = D.g0 * d * D.g0⁻¹ := by rw [← hdy]
        _ = (D.g0 * ζ) * d * (D.g0 * ζ)⁻¹ := by
          rw [show D.g0 * ζ * d * (D.g0 * ζ)⁻¹ = D.g0 * (ζ * d * ζ⁻¹) * D.g0⁻¹ by group, hζd']
    rw [hbz]
    calc ((D.g0 * ζ) * v * (D.g0 * ζ)⁻¹) * ((D.g0 * ζ) * d * (D.g0 * ζ)⁻¹)
        = (D.g0 * ζ) * (v * d) * (D.g0 * ζ)⁻¹ := by group
      _ = (D.g0 * ζ) * (d * v) * (D.g0 * ζ)⁻¹ := by rw [hvd]
      _ = ((D.g0 * ζ) * d * (D.g0 * ζ)⁻¹) * ((D.g0 * ζ) * v * (D.g0 * ζ)⁻¹) := by group

theorem langPlaneKillsRoot_F4_of_cycle (hcyc : KillsCycleShape Tag.F4) : LangPlaneKillsRoot Tag.F4 := by
  intro K _ _ A D α hα hk
  obtain ⟨uL, huLad, huL1, huLp, huLF, huLc⟩ := kill_core_of (τ := Tag.F4) hcyc K A D α hα hk
  have hbij : Function.Bijective D.Fr := by
    refine ⟨D.Fr.injective, fun c => ?_⟩
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.card_pos (α := K))
    exact ⟨z, by rw [D.hFr z, hz]⟩
  obtain ⟨u', hu'mem, hu'eq⟩ := Subgroup.mem_map.1
    (CFSG.RankThree.Chevalley.mem_map_adjointGroup_of_frobenius_fixed (τ := Tag.F4) (Or.inr rfl)
      D.Fr D.hFr hbij huLad huLF)
  exact finish_of_descent K A D.c u' hu'mem uL hu'eq huL1 huLp huLc

end KillsRootF4

end CFSG.LieType.SeitzGeneration.ExcHighThree
