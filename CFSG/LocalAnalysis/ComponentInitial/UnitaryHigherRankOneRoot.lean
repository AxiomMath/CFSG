module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankTwoLevi

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open Module Submodule
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K]

section Coords

@[expose] def rkVec (x y w : K) : HypIndex 1 1 → K :=
  Sum.elim (fun _ => x) (Sum.elim (fun _ => y) (fun _ => w))

omit [Field K] in
@[simp] theorem rkVec_inl (x y w : K) (i : Fin 1) : rkVec x y w (.inl i) = x := rfl
omit [Field K] in
@[simp] theorem rkVec_inr_inl (x y w : K) (i : Fin 1) : rkVec x y w (.inr (.inl i)) = y := rfl
omit [Field K] in
@[simp] theorem rkVec_inr_inr (x y w : K) (i : Fin 1) : rkVec x y w (.inr (.inr i)) = w := rfl

omit [Field K] in
theorem rkVec_eta (v : HypIndex 1 1 → K) :
    v = rkVec (v (.inl 0)) (v (.inr (.inl 0))) (v (.inr (.inr 0))) := by
  funext c
  rcases c with i | i | i <;> obtain rfl := Fin.fin_one_eq_zero i <;> rfl

omit [Field K] in
theorem rkVec_injective {x y w x' y' w' : K} (he : rkVec x y w = rkVec x' y' w') :
    x = x' ∧ y = y' ∧ w = w' :=
  ⟨congrFun he (.inl 0), congrFun he (.inr (.inl 0)), congrFun he (.inr (.inr 0))⟩

theorem rkVec_smul (c x y w : K) : c • rkVec x y w = rkVec (c * x) (c * y) (c * w) := by
  funext v
  rcases v with i | i | i <;> rfl

theorem rkVec_add (x y w x' y' w' : K) :
    rkVec x y w + rkVec x' y' w' = rkVec (x + x') (y + y') (w + w') := by
  funext v
  rcases v with i | i | i <;> rfl

theorem rkVec_zero : rkVec (0 : K) 0 0 = 0 := by
  funext v
  rcases v with i | i | i <;> rfl

theorem rkVec_eq_zero_iff {x y w : K} : rkVec x y w = 0 ↔ x = 0 ∧ y = 0 ∧ w = 0 := by
  constructor
  · intro h0
    rw [← rkVec_zero] at h0
    exact rkVec_injective h0
  · rintro ⟨rfl, rfl, rfl⟩
    exact rkVec_zero

theorem single_inl_eq_rkVec : (Pi.single (.inl 0) 1 : HypIndex 1 1 → K) = rkVec 1 0 0 := by
  funext v
  rcases v with i | i | i <;> obtain rfl := Fin.fin_one_eq_zero i <;> simp [rkVec]

theorem single_inr_inr_eq_rkVec :
    (Pi.single (.inr (.inr 0)) 1 : HypIndex 1 1 → K) = rkVec 0 0 1 := by
  funext v
  rcases v with i | i | i <;> obtain rfl := Fin.fin_one_eq_zero i <;> simp [rkVec]

theorem hypForm_rkVec (h : UnitaryFieldData p f K) (x y w x' y' w' : K) :
    hypForm h 1 1 (rkVec x y w) (rkVec x' y' w') =
      h.bar x * w' + h.bar y * y' + h.bar w * x' := by
  rw [hypForm_apply]
  simp [Fintype.sum_sum_type, rkVec]
  ring

theorem mulVec_rkVec (M : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (x y w : K) :
    M *ᵥ rkVec x y w = rkVec
      (M (.inl 0) (.inl 0) * x + M (.inl 0) (.inr (.inl 0)) * y + M (.inl 0) (.inr (.inr 0)) * w)
      (M (.inr (.inl 0)) (.inl 0) * x + M (.inr (.inl 0)) (.inr (.inl 0)) * y +
        M (.inr (.inl 0)) (.inr (.inr 0)) * w)
      (M (.inr (.inr 0)) (.inl 0) * x + M (.inr (.inr 0)) (.inr (.inl 0)) * y +
        M (.inr (.inr 0)) (.inr (.inr 0)) * w) := by
  funext v
  rcases v with i | i | i <;> obtain rfl := Fin.fin_one_eq_zero i <;>
    simp [mulVec, dotProduct, Fintype.sum_sum_type, rkVec, add_assoc]

theorem rkOneQ_mulVec (h : UnitaryFieldData p f K) (a b x y w : K) :
    rkOneQ h a b *ᵥ rkVec x y w = rkVec (x - h.bar a * y + b * w) (y + a * w) w := by
  rw [mulVec_rkVec]
  congr 1
  · simp [rkOneQ, heisenbergMatrix, hypIndexFin3]
    ring
  · simp [rkOneQ, heisenbergMatrix, hypIndexFin3]
  · simp [rkOneQ, heisenbergMatrix, hypIndexFin3]

theorem rkOneD_mulVec (h : UnitaryFieldData p f K) (s x y w : K) :
    rkOneD h s *ᵥ rkVec x y w = rkVec (s * x) (h.bar s / s * y) ((h.bar s)⁻¹ * w) := by
  funext c
  rw [rkOneD, mulVec_diagonal]
  rcases c with i | i | i <;> rfl

end Coords

section Points

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def infL : hypIsotropicLines h 1 1 :=
  ⟨infPt, span_single_mem_hypIsotropicLines (by simp)⟩

@[expose] noncomputable def zeroL : hypIsotropicLines h 1 1 :=
  ⟨zeroPt, span_single_mem_hypIsotropicLines (by simp)⟩

theorem coe_infL : (infL h : Submodule K (HypIndex 1 1 → K)) = K ∙ rkVec 1 0 0 := by
  rw [← single_inl_eq_rkVec]
  rfl

theorem coe_zeroL : (zeroL h : Submodule K (HypIndex 1 1 → K)) = K ∙ rkVec 0 0 1 := by
  rw [← single_inr_inr_eq_rkVec]
  rfl

theorem hypForm_rkVec_self_eq {a b : K} :
    hypForm h 1 1 (rkVec b a 1) (rkVec b a 1) = h.norm a + h.trace b := by
  rw [hypForm_rkVec, map_one, mul_one, one_mul, UnitaryFieldData.norm, UnitaryFieldData.trace]
  ring

theorem rkVec_ne_zero (a b : K) : rkVec b a (1 : K) ≠ 0 := fun h0 =>
  one_ne_zero (rkVec_eq_zero_iff.mp h0).2.2

@[expose] noncomputable def rkPtL {a b : K} (hab : h.norm a + h.trace b = 0) :
    hypIsotropicLines h 1 1 :=
  ⟨K ∙ rkVec b a 1, span_mem_hypIsotropicLines h (rkVec_ne_zero a b)
    (by rw [hypForm_rkVec_self_eq, hab])⟩

theorem coe_rkPtL {a b : K} (hab : h.norm a + h.trace b = 0) :
    (rkPtL h hab : Submodule K (HypIndex 1 1 → K)) = K ∙ rkVec b a 1 :=
  rfl

theorem rkPtL_zero : rkPtL h (norm_zero_add_trace (zero_mem h.traceZero)) = zeroL h :=
  Subtype.ext (by rw [coe_rkPtL, coe_zeroL])

variable {h}

theorem eq_of_span_rkVec_eq {a b a' b' : K} (he : K ∙ rkVec b a (1 : K) = K ∙ rkVec b' a' 1) :
    a = a' ∧ b = b' := by
  have hmem : rkVec b' a' (1 : K) ∈ K ∙ rkVec b a 1 := by
    rw [he]
    exact mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  rw [rkVec_smul] at hc
  obtain ⟨h1, h2, h3⟩ := rkVec_injective hc
  rw [mul_one] at h3
  rw [h3, one_mul] at h1 h2
  exact ⟨h2, h1⟩

theorem rkPtL_ne_infL {a b : K} (hab : h.norm a + h.trace b = 0) : rkPtL h hab ≠ infL h := by
  intro he
  have hmem : rkVec 1 0 (0 : K) ∈ K ∙ rkVec b a 1 := by
    rw [← coe_rkPtL h hab, he, coe_infL]
    exact mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  rw [rkVec_smul] at hc
  obtain ⟨h1, -, h3⟩ := rkVec_injective hc
  rw [mul_one] at h3
  rw [h3, zero_mul] at h1
  exact zero_ne_one h1

theorem zeroL_ne_infL : zeroL h ≠ infL h := by
  rw [← rkPtL_zero h]
  exact rkPtL_ne_infL _

theorem exists_rkPtL_eq (L : hypIsotropicLines h 1 1) (hL : L ≠ infL h) :
    ∃ (a b : K) (hab : h.norm a + h.trace b = 0), rkPtL h hab = L := by
  obtain ⟨v, hv0, hvv, hLv⟩ := exists_eq_span_of_mem_hypIsotropicLines h L.2
  rw [rkVec_eta v] at hv0 hvv hLv
  set x := v (.inl 0)
  set y := v (.inr (.inl 0))
  set w := v (.inr (.inr 0))
  rw [hypForm_rkVec] at hvv
  by_cases hw : w = 0
  · exfalso
    rw [hw] at hvv hv0 hLv
    have hy : y = 0 := by
      simp only [mul_zero, map_zero, zero_mul, zero_add, add_zero] at hvv
      rcases mul_eq_zero.mp hvv with h0 | h0
      · exact (UnitaryFieldData.bar_eq_zero_iff h).mp h0
      · exact h0
    rw [hy] at hv0 hLv
    have hx : x ≠ 0 := fun h0 => hv0 (by rw [h0, rkVec_zero])
    apply hL
    apply Subtype.ext
    rw [hLv, coe_infL, show rkVec x 0 (0 : K) = x • rkVec 1 0 0 by
      rw [rkVec_smul, mul_one, mul_zero], span_singleton_smul_eq (IsUnit.mk0 _ hx)]
  · have hvw : rkVec x y w = w • rkVec (x / w) (y / w) 1 := by
      rw [rkVec_smul, mul_div_cancel₀ _ hw, mul_div_cancel₀ _ hw, mul_one]
    have hL' : (L : Submodule K (HypIndex 1 1 → K)) = K ∙ rkVec (x / w) (y / w) 1 := by
      rw [hLv, hvw, span_singleton_smul_eq (IsUnit.mk0 _ hw)]
    have hab : h.norm (y / w) + h.trace (x / w) = 0 := by
      rw [← hypForm_rkVec_self_eq h]
      exact hypForm_self_of_span h L hL'
    exact ⟨y / w, x / w, hab, Subtype.ext hL'.symm⟩

end Points

section Unitriangular

variable (h : UnitaryFieldData p f K)

theorem rkOneQ_mul (a b c d : K) :
    rkOneQ h a b * rkOneQ h c d = rkOneQ h (a + c) (b + d - h.bar a * c) := by
  rw [rkOneQ, rkOneQ, rkOneQ, submatrix_mul_equiv, heisenbergMatrix_mul]

theorem rkOneQElt_mem {a b : K} (hab : h.norm a + h.trace b = 0) :
    rkOneQElt h a b hab ∈ hypUnitriangular h 1 1 := by
  refine mem_hypUnitriangular.mpr ⟨fun i j hij => ?_, fun i => ?_⟩
  · change rkOneQ h a b i j = 0
    rcases i with i | i | i <;> rcases j with j | j | j <;>
      obtain rfl := Fin.fin_one_eq_zero i <;> obtain rfl := Fin.fin_one_eq_zero j <;>
      simp [fullPos] at hij <;> simp [rkOneQ, heisenbergMatrix, hypIndexFin3]
  · change rkOneQ h a b i i = 1
    rcases i with i | i | i <;> obtain rfl := Fin.fin_one_eq_zero i <;>
      simp [rkOneQ, heisenbergMatrix, hypIndexFin3]

theorem exists_eq_rkOneQElt {g : hypSU h 1 1} (hg : g ∈ hypUnitriangular h 1 1) :
    ∃ (a b : K) (hab : h.norm a + h.trace b = 0), g = rkOneQElt h a b hab := by
  obtain ⟨hT, hD⟩ := mem_hypUnitriangular.mp hg
  set M := ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) with hM
  have hze : M (.inr (.inl 0)) (.inl 0) = 0 := hT (by simp [fullPos])
  have hfe : M (.inr (.inr 0)) (.inl 0) = 0 := hT (by simp [fullPos])
  have hfz : M (.inr (.inr 0)) (.inr (.inl 0)) = 0 := hT (by simp [fullPos])
  have hee : M (.inl 0) (.inl 0) = 1 := hD _
  have hzz : M (.inr (.inl 0)) (.inr (.inl 0)) = 1 := hD _
  have hff : M (.inr (.inr 0)) (.inr (.inr 0)) = 1 := hD _
  set x := M (.inl 0) (.inr (.inl 0))
  set b := M (.inl 0) (.inr (.inr 0))
  set a := M (.inr (.inl 0)) (.inr (.inr 0))
  have hMv : ∀ u v w : K, M *ᵥ rkVec u v w = rkVec (u + x * v + b * w) (v + a * w) w := by
    intro u v w
    rw [mulVec_rkVec, hee, hze, hfe, hzz, hfz, hff]
    congr 1 <;> ring
  have hiso : ∀ u v, hypForm h 1 1 (M *ᵥ u) (M *ᵥ v) = hypForm h 1 1 u v :=
    fun u v => hypForm_smul_smul h g u v
  have h1 := hiso (rkVec 0 1 0) (rkVec 0 0 1)
  rw [hMv, hMv, hypForm_rkVec, hypForm_rkVec] at h1
  simp only [mul_zero, add_zero, zero_add, mul_one, map_one, map_zero, zero_mul, one_mul] at h1
  have hx : x = -h.bar a := by
    have := congrArg h.bar h1
    rw [map_add, h.bar_bar, map_zero] at this
    linear_combination this
  have h2 := hiso (rkVec 0 0 1) (rkVec 0 0 1)
  rw [hMv, hypForm_rkVec, hypForm_rkVec] at h2
  simp only [mul_zero, add_zero, zero_add, mul_one, map_one, map_zero, one_mul] at h2
  have hab : h.norm a + h.trace b = 0 := by
    rw [UnitaryFieldData.norm, UnitaryFieldData.trace]
    linear_combination h2
  refine ⟨a, b, hab, Subtype.ext (Units.ext ?_)⟩
  change M = rkOneQ h a b
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    obtain rfl := Fin.fin_one_eq_zero i <;> obtain rfl := Fin.fin_one_eq_zero j <;>
    simp [rkOneQ, heisenbergMatrix, hypIndexFin3, hee, hze, hfe, hzz, hfz, hff, ← hx] <;> rfl

end Unitriangular

section UStar

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def rkOneUHom :
    hypUnitriangular h 1 1 →* Equiv.Perm (hypIsotropicLines h 1 1) :=
  (hypProjLineAction h 1 1).comp ((hypProj h 1 1).comp (hypUnitriangular h 1 1).subtype)

theorem rkOneU_eq {a b : K} (hab : h.norm a + h.trace b = 0) :
    rkOneU h a b hab = rkOneUHom h ⟨rkOneQElt h a b hab, rkOneQElt_mem h hab⟩ :=
  rfl

theorem gl_smul_span {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι K) (v : ι → K) :
    g • (K ∙ v) = K ∙ ((g : Matrix ι ι K) *ᵥ v) := by
  rw [gl_smul_eq_map, Submodule.map_span, Set.image_singleton]
  rfl

theorem rkOneU_zeroL {a b : K} (hab : h.norm a + h.trace b = 0) :
    rkOneU h a b hab (zeroL h) = rkPtL h hab := by
  apply Subtype.ext
  change ((rkOneQElt h a b hab : hypSU h 1 1) : GL (HypIndex 1 1) K) •
    (zeroL h : Submodule K (HypIndex 1 1 → K)) = _
  rw [coe_zeroL, gl_smul_span, coe_rkPtL]
  change K ∙ (rkOneQ h a b *ᵥ rkVec 0 0 1) = _
  rw [rkOneQ_mulVec]
  simp

theorem rkOneU_infL {a b : K} (hab : h.norm a + h.trace b = 0) :
    rkOneU h a b hab (infL h) = infL h := by
  apply Subtype.ext
  change ((rkOneQElt h a b hab : hypSU h 1 1) : GL (HypIndex 1 1) K) •
    (infL h : Submodule K (HypIndex 1 1 → K)) = _
  rw [coe_infL, gl_smul_span]
  change K ∙ (rkOneQ h a b *ᵥ rkVec 1 0 0) = _
  rw [rkOneQ_mulVec]
  simp

variable {h} in
theorem rkOneU_injective {a b a' b' : K} {hab : h.norm a + h.trace b = 0}
    {hab' : h.norm a' + h.trace b' = 0} (he : rkOneU h a b hab = rkOneU h a' b' hab') :
    a = a' ∧ b = b' := by
  have h1 := congrArg (fun x : Equiv.Perm (hypIsotropicLines h 1 1) =>
    ((x (zeroL h) : hypIsotropicLines h 1 1) : Submodule K (HypIndex 1 1 → K))) he
  simp only [rkOneU_zeroL, coe_rkPtL] at h1
  exact eq_of_span_rkVec_eq h1

theorem rkOneUHom_injective : Function.Injective (rkOneUHom h) := by
  intro g g' hgg'
  obtain ⟨a, b, hab, hg⟩ := exists_eq_rkOneQElt h g.2
  obtain ⟨a', b', hab', hg'⟩ := exists_eq_rkOneQElt h g'.2
  have he : rkOneU h a b hab = rkOneU h a' b' hab' := by
    rw [rkOneU_eq, rkOneU_eq]
    have e1 : (⟨rkOneQElt h a b hab, rkOneQElt_mem h hab⟩ : hypUnitriangular h 1 1) = g :=
      Subtype.ext hg.symm
    have e2 : (⟨rkOneQElt h a' b' hab', rkOneQElt_mem h hab'⟩ : hypUnitriangular h 1 1) = g' :=
      Subtype.ext hg'.symm
    rw [e1, e2]
    exact hgg'
  obtain ⟨rfl, rfl⟩ := rkOneU_injective he
  exact Subtype.ext (hg.trans hg'.symm)

theorem range_rkOneUHom : (rkOneUHom h).range = rkOneUStar h := by
  rw [rkOneUHom, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype]
  rfl

@[expose] noncomputable def rkOneUIso : hypUnitriangular h 1 1 ≃* rkOneUStar h :=
  (MonoidHom.ofInjective (rkOneUHom_injective h)).trans
    (MulEquiv.subgroupCongr (range_rkOneUHom h))

theorem coe_rkOneUIso (g : hypUnitriangular h 1 1) :
    ((rkOneUIso h g : rkOneUStar h) : Equiv.Perm (hypIsotropicLines h 1 1)) = rkOneUHom h g :=
  rfl

theorem rkOneU_mem {a b : K} (hab : h.norm a + h.trace b = 0) :
    rkOneU h a b hab ∈ rkOneUStar h :=
  (rkOneUIso h ⟨rkOneQElt h a b hab, rkOneQElt_mem h hab⟩).2

theorem rkOneUIso_rkOneQElt {a b : K} (hab : h.norm a + h.trace b = 0) :
    rkOneUIso h ⟨rkOneQElt h a b hab, rkOneQElt_mem h hab⟩ = ⟨rkOneU h a b hab, rkOneU_mem h hab⟩ :=
  rfl

theorem mem_rkOneUStar {x : Equiv.Perm (hypIsotropicLines h 1 1)} :
    x ∈ rkOneUStar h ↔ ∃ (a b : K) (hab : h.norm a + h.trace b = 0), rkOneU h a b hab = x := by
  constructor
  · intro hx
    rw [← range_rkOneUHom] at hx
    obtain ⟨g, rfl⟩ := hx
    obtain ⟨a, b, hab, hg⟩ := exists_eq_rkOneQElt h g.2
    exact ⟨a, b, hab, by rw [rkOneU_eq]; congr 1; exact Subtype.ext hg.symm⟩
  · rintro ⟨a, b, hab, rfl⟩
    exact rkOneU_mem h hab

theorem rkOneQElt_mul {a b c d : K} (hab : h.norm a + h.trace b = 0)
    (hcd : h.norm c + h.trace d = 0) :
    rkOneQElt h a b hab * rkOneQElt h c d hcd = rkOneQElt h (a + c) (b + d - h.bar a * c)
      ((unitary_heisenberg_identities h).2.1 a b c d hab hcd).2 :=
  Subtype.ext (Units.ext (rkOneQ_mul h a b c d))

theorem rkOneU_mul {a b c d : K} (hab : h.norm a + h.trace b = 0)
    (hcd : h.norm c + h.trace d = 0) :
    rkOneU h a b hab * rkOneU h c d hcd = rkOneU h (a + c) (b + d - h.bar a * c)
      ((unitary_heisenberg_identities h).2.1 a b c d hab hcd).2 := by
  rw [rkOneU, rkOneU, rkOneU, ← map_mul, ← map_mul, rkOneQElt_mul]

end UStar

section Algebra

variable (h : UnitaryFieldData p f K)

theorem exists_norm_add_trace_eq_zero (a : K) : ∃ b : K, h.norm a + h.trace b = 0 := by
  obtain ⟨b, hb⟩ := h.traceLin_surjective ⟨-h.norm a, neg_mem (h.norm_mem_fixedField a)⟩
  have hb' : h.trace b = -h.norm a := by simpa using congrArg Subtype.val hb
  exact ⟨b, by rw [hb', add_neg_cancel]⟩

theorem coe_rkOneQElt {a b : K} (hab : h.norm a + h.trace b = 0) :
    (((rkOneQElt h a b hab : hypSU h 1 1) : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K) = rkOneQ h a b :=
  rfl

theorem rkOneQ_zf (a b : K) : rkOneQ h a b (.inr (.inl 0)) (.inr (.inr 0)) = a := by
  simp [rkOneQ, heisenbergMatrix, hypIndexFin3]

theorem rkOneQ_ef (a b : K) : rkOneQ h a b (.inl 0) (.inr (.inr 0)) = b := by
  simp [rkOneQ, heisenbergMatrix, hypIndexFin3]

theorem trace_sub (x y : K) : h.trace (x - y) = h.trace x - h.trace y := by
  simp only [UnitaryFieldData.trace, map_sub]
  ring

theorem card_rkOneUStar : Nat.card (rkOneUStar h) = (p ^ f) ^ 3 := by
  choose b₀ hb₀ using exists_norm_add_trace_eq_zero h
  have hmem : ∀ g : hypUnitriangular h 1 1,
      ((g : hypSU h 1 1) : GL (HypIndex 1 1) K) (.inl 0) (.inr (.inr 0)) -
        b₀ (((g : hypSU h 1 1) : GL (HypIndex 1 1) K) (.inr (.inl 0)) (.inr (.inr 0))) ∈
          h.traceZero := fun g => by
    obtain ⟨a, b, hab, hg⟩ := exists_eq_rkOneQElt h g.2
    rw [hg, coe_rkOneQElt, rkOneQ_zf, rkOneQ_ef, UnitaryFieldData.mem_traceZero, trace_sub]
    linear_combination hab - hb₀ a
  have hpar : ∀ (a : K) (t : h.traceZero), h.norm a + h.trace (b₀ a + t) = 0 := fun a t => by
    have ht := (UnitaryFieldData.mem_traceZero h).mp t.2
    have h0 := hb₀ a
    simp only [UnitaryFieldData.trace, map_add] at ht h0 ⊢
    linear_combination h0 + ht
  let e : hypUnitriangular h 1 1 ≃ K × h.traceZero :=
    { toFun := fun g => ⟨((g : hypSU h 1 1) : GL (HypIndex 1 1) K) (.inr (.inl 0)) (.inr (.inr 0)),
        ⟨_, hmem g⟩⟩
      invFun := fun x => ⟨rkOneQElt h x.1 (b₀ x.1 + x.2) (hpar x.1 x.2), rkOneQElt_mem h _⟩
      left_inv := fun g => by
        obtain ⟨a, b, hab, hg⟩ := exists_eq_rkOneQElt h g.2
        apply Subtype.ext
        simp only [hg, coe_rkOneQElt, rkOneQ_zf, rkOneQ_ef, add_sub_cancel]
      right_inv := fun x => by
        ext
        · exact rkOneQ_zf h _ _
        · change rkOneQ h x.1 (b₀ x.1 + x.2) (.inl 0) (.inr (.inr 0)) -
            b₀ (rkOneQ h x.1 (b₀ x.1 + x.2) (.inr (.inl 0)) (.inr (.inr 0))) = x.2
          rw [rkOneQ_zf, rkOneQ_ef, add_sub_cancel_left] }
  have := h.finite
  rw [← Nat.card_congr (rkOneUIso h).toEquiv, Nat.card_congr e, Nat.card_prod,
    UnitaryFieldData.card_traceZero, UnitaryFieldData.card_eq_sq h]
  ring

@[expose] noncomputable def uAHom : hypUnitriangular h 1 1 →* Multiplicative K where
  toFun g := Multiplicative.ofAdd
    (((g : hypSU h 1 1) : GL (HypIndex 1 1) K) (.inr (.inl 0)) (.inr (.inr 0)))
  map_one' := by simp
  map_mul' g g' := by
    obtain ⟨a, b, hab, hg⟩ := exists_eq_rkOneQElt h g.2
    obtain ⟨c, d, hcd, hg'⟩ := exists_eq_rkOneQElt h g'.2
    have hgg' : ((g * g' : hypUnitriangular h 1 1) : hypSU h 1 1) =
        rkOneQElt h (a + c) (b + d - h.bar a * c)
          ((unitary_heisenberg_identities h).2.1 a b c d hab hcd).2 := by
      rw [Subgroup.coe_mul, hg, hg', rkOneQElt_mul]
    simp only [hgg', hg, hg', coe_rkOneQElt, rkOneQ_zf]
    rfl

@[expose] noncomputable def rkOneAHom : rkOneUStar h →* Multiplicative K :=
  (uAHom h).comp (rkOneUIso h).symm.toMonoidHom

theorem rkOneAHom_rkOneU {a b : K} (hab : h.norm a + h.trace b = 0) :
    rkOneAHom h ⟨rkOneU h a b hab, rkOneU_mem h hab⟩ = Multiplicative.ofAdd a := by
  have he : (rkOneUIso h).symm ⟨rkOneU h a b hab, rkOneU_mem h hab⟩ =
      ⟨rkOneQElt h a b hab, rkOneQElt_mem h hab⟩ :=
    (rkOneUIso h).symm_apply_eq.mpr (rkOneUIso_rkOneQElt h hab).symm
  change uAHom h ((rkOneUIso h).symm ⟨rkOneU h a b hab, rkOneU_mem h hab⟩) = _
  rw [he]
  change Multiplicative.ofAdd (rkOneQ h a b (.inr (.inl 0)) (.inr (.inr 0))) = _
  rw [rkOneQ_zf]

theorem rkOneU_congr {a b a' b' : K} (hab : h.norm a + h.trace b = 0) (ha : a = a')
    (hb : b = b') : rkOneU h a b hab = rkOneU h a' b' (ha ▸ hb ▸ hab) := by
  subst ha hb
  rfl

theorem rkOneU_zero_zero : rkOneU h 0 0 (norm_zero_add_trace (zero_mem h.traceZero)) = 1 := by
  rw [rkOneU]
  convert map_one (hypProjLineAction h 1 1) using 2
  convert map_one (hypProj h 1 1)
  exact Subtype.ext (Units.ext (by
    rw [coe_rkOneQElt, rkOneQ, heisenbergMatrix_zero_zero]
    exact submatrix_one_equiv _))

theorem mem_rkOneC {x : Equiv.Perm (hypIsotropicLines h 1 1)} :
    x ∈ rkOneC h ↔ ∃ (t : K) (ht : t ∈ h.traceZero), rkOneU h 0 t (norm_zero_add_trace ht) = x :=
  ⟨fun ⟨t, ht⟩ => ⟨t.toAdd, t.toAdd.2, ht⟩, fun ⟨t, ht, hx⟩ => ⟨Multiplicative.ofAdd ⟨t, ht⟩, hx⟩⟩

theorem commutator_param_mem (a c : K) : h.norm 0 + h.trace (h.bar c * a - h.bar a * c) = 0 := by
  simp only [UnitaryFieldData.norm, UnitaryFieldData.trace, map_zero, mul_zero, zero_add,
    map_sub, map_mul, h.bar_bar]
  ring

theorem rkOneU_commutator {a b c d : K} (hab : h.norm a + h.trace b = 0)
    (hcd : h.norm c + h.trace d = 0) :
    rkOneU h a b hab * rkOneU h c d hcd * (rkOneU h a b hab)⁻¹ * (rkOneU h c d hcd)⁻¹ =
      rkOneU h 0 (h.bar c * a - h.bar a * c) (commutator_param_mem h a c) := by
  rw [rkOneU, rkOneU, rkOneU, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_inv,
    ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  congr 2
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Matrix.coe_units_inv,
    coe_rkOneQElt]
  rw [rkOneQ, rkOneQ, rkOneQ, inv_submatrix_equiv, inv_submatrix_equiv, submatrix_mul_equiv,
    submatrix_mul_equiv, submatrix_mul_equiv, (unitary_heisenberg_commutator h).1 a b c d hab hcd]

end Algebra

section Center

variable (h : UnitaryFieldData p f K)

theorem mem_traceZero_of_norm_zero {b : K} (hb : h.norm 0 + h.trace b = 0) : b ∈ h.traceZero := by
  rw [UnitaryFieldData.norm, zero_mul, zero_add] at hb
  exact (UnitaryFieldData.mem_traceZero h).mpr hb

theorem rkOneC_le : rkOneC h ≤ rkOneUStar h := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := (mem_rkOneC h).mp hx
  exact rkOneU_mem h _

theorem rkOneC_eq_center :
    rkOneC h = (Subgroup.center (rkOneUStar h)).map (rkOneUStar h).subtype := by
  ext x
  rw [mem_rkOneC, Subgroup.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨_, rkOneU_mem h _⟩, Subgroup.mem_center_iff.mpr fun y => ?_, rfl⟩
    obtain ⟨c, d, hcd, hy⟩ := (mem_rkOneUStar h).mp y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hy, rkOneU_mul, rkOneU_mul]
    exact rkOneU_congr h _ (by ring) (by rw [map_zero]; ring)
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, b, hab, hy'⟩ := (mem_rkOneUStar h).mp y.2
    by_cases ha : a = 0
    · subst ha
      exact ⟨b, mem_traceZero_of_norm_zero h hab, hy'⟩
    · exfalso
      obtain ⟨r, hr⟩ := h.exists_bar_ne
      obtain ⟨d, hd⟩ := exists_norm_add_trace_eq_zero h (a * r)
      have hc := Subgroup.mem_center_iff.mp hy ⟨rkOneU h (a * r) d hd, rkOneU_mem h hd⟩
      have hc' : (y : Equiv.Perm (hypIsotropicLines h 1 1)) * rkOneU h (a * r) d hd *
          (y : Equiv.Perm (hypIsotropicLines h 1 1))⁻¹ * (rkOneU h (a * r) d hd)⁻¹ = 1 := by
        have := congrArg Subtype.val hc
        simp only [Subgroup.coe_mul] at this
        rw [← this, mul_inv_cancel_right, mul_inv_cancel]
      rw [← hy', rkOneU_commutator, ← rkOneU_zero_zero h] at hc'
      have h1 := (rkOneU_injective hc').2
      rw [map_mul] at h1
      have h2 : h.norm a * (h.bar r - r) = 0 := by
        rw [UnitaryFieldData.norm]
        linear_combination h1
      rcases mul_eq_zero.mp h2 with h3 | h3
      · rw [UnitaryFieldData.norm] at h3
        exact ha ((mul_eq_zero.mp h3).elim id fun h4 =>
          (UnitaryFieldData.bar_eq_zero_iff h).mp h4)
      · exact hr (sub_eq_zero.mp h3)

theorem rkOneC_eq_commutator : rkOneC h = ⁅rkOneUStar h, rkOneUStar h⁆ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := (mem_rkOneC h).mp hx
    have ht' : t ∈ h.barSub.range := by rw [h.range_barSub]; exact ht
    obtain ⟨r, hr⟩ := ht'
    rw [UnitaryFieldData.barSub_apply] at hr
    obtain ⟨b, hb⟩ := exists_norm_add_trace_eq_zero h 1
    obtain ⟨d, hd⟩ := exists_norm_add_trace_eq_zero h r
    have hcomm := rkOneU_commutator h hb hd
    have hpar : h.bar r * 1 - h.bar 1 * r = t := by rw [map_one, mul_one, one_mul, hr]
    rw [rkOneU_congr h (commutator_param_mem h 1 r) rfl hpar] at hcomm
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (rkOneU_mem h hb) (rkOneU_mem h hd)
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨a, b, hab, rfl⟩ := (mem_rkOneUStar h).mp hx
    obtain ⟨c, d, hcd, rfl⟩ := (mem_rkOneUStar h).mp hy
    change rkOneU h a b hab * rkOneU h c d hcd * (rkOneU h a b hab)⁻¹ *
      (rkOneU h c d hcd)⁻¹ ∈ rkOneC h
    rw [rkOneU_commutator]
    exact (mem_rkOneC h).mpr ⟨_, mem_traceZero_of_norm_zero h (commutator_param_mem h a c), rfl⟩

theorem ker_rkOneAHom : (rkOneAHom h).ker = (rkOneC h).subgroupOf (rkOneUStar h) := by
  ext ⟨x, hx⟩
  obtain ⟨a, b, hab, rfl⟩ := (mem_rkOneUStar h).mp hx
  rw [MonoidHom.mem_ker, rkOneAHom_rkOneU, Subgroup.mem_subgroupOf, mem_rkOneC]
  constructor
  · intro ha
    have ha0 : a = 0 := by simpa using ha
    subst ha0
    exact ⟨b, mem_traceZero_of_norm_zero h hab, rfl⟩
  · rintro ⟨t, ht, he⟩
    rw [(rkOneU_injective he).1.symm]
    rfl

theorem rkOneAHom_surjective : Function.Surjective (rkOneAHom h) := fun m => by
  obtain ⟨b, hb⟩ := exists_norm_add_trace_eq_zero h (Multiplicative.toAdd m)
  exact ⟨⟨_, rkOneU_mem h hb⟩, by rw [rkOneAHom_rkOneU]; rfl⟩

end Center

section Stabilizers

variable (h : UnitaryFieldData p f K)

theorem rkOneD_mul_rkOneQ {s : K} (hs : s ≠ 0) (a b : K) :
    rkOneD h s * rkOneQ h a b =
      rkOneQ h (h.bar s ^ 2 / s * a) (s * h.bar s * b) * rkOneD h s := by
  have hbs : h.bar s ≠ 0 := (map_ne_zero h.bar).mpr hs
  refine ext_iff_mulVec.mpr fun v => ?_
  rw [rkVec_eta v, ← mulVec_mulVec, ← mulVec_mulVec, rkOneQ_mulVec, rkOneD_mulVec,
    rkOneD_mulVec, rkOneQ_mulVec]
  simp only [map_mul, map_div₀, map_pow, h.bar_bar]
  congr 1 <;> field_simp

theorem rkOneT_param {s : K} (hs : s ≠ 0) {a b : K} (hab : h.norm a + h.trace b = 0) :
    h.norm (h.bar s ^ 2 / s * a) + h.trace (s * h.bar s * b) = 0 := by
  have hbs : h.bar s ≠ 0 := (map_ne_zero h.bar).mpr hs
  have he : h.norm (h.bar s ^ 2 / s * a) + h.trace (s * h.bar s * b) =
      s * h.bar s * (h.norm a + h.trace b) := by
    simp only [UnitaryFieldData.norm, UnitaryFieldData.trace, map_mul, map_div₀, map_pow,
      h.bar_bar]
    field_simp
  rw [he, hab, mul_zero]

theorem rkOneTElt_conj (s : Kˣ) {a b : K} (hab : h.norm a + h.trace b = 0) :
    rkOneTElt h s * rkOneU h a b hab * (rkOneTElt h s)⁻¹ =
      rkOneU h (h.bar s ^ 2 / s * a) (s * h.bar s * b) (rkOneT_param h s.ne_zero hab) := by
  rw [rkOneTElt, rkOneU, rkOneU, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul,
    ← map_mul]
  congr 2
  rw [mul_inv_eq_iff_eq_mul]
  exact Subtype.ext (Units.ext (rkOneD_mul_rkOneQ h s.ne_zero a b))

theorem rkOneTElt_infL (s : Kˣ) : rkOneTElt h s (infL h) = infL h := by
  apply Subtype.ext
  change ((rkOneDHomSU h s : hypSU h 1 1) : GL (HypIndex 1 1) K) •
    (infL h : Submodule K (HypIndex 1 1 → K)) = _
  rw [coe_infL, gl_smul_span]
  change K ∙ (rkOneD h s *ᵥ rkVec 1 0 0) = _
  rw [rkOneD_mulVec, mul_one, mul_zero, mul_zero,
    show rkVec (s : K) 0 0 = (s : K) • rkVec 1 0 0 by rw [rkVec_smul, mul_one, mul_zero],
    span_singleton_smul_eq (IsUnit.mk0 _ s.ne_zero)]

theorem rkOneTElt_zeroL (s : Kˣ) : rkOneTElt h s (zeroL h) = zeroL h := by
  have hbs : h.bar (s : K) ≠ 0 := (map_ne_zero h.bar).mpr s.ne_zero
  apply Subtype.ext
  change ((rkOneDHomSU h s : hypSU h 1 1) : GL (HypIndex 1 1) K) •
    (zeroL h : Submodule K (HypIndex 1 1 → K)) = _
  rw [coe_zeroL, gl_smul_span]
  change K ∙ (rkOneD h s *ᵥ rkVec 0 0 1) = _
  rw [rkOneD_mulVec, mul_one, mul_zero, mul_zero,
    show rkVec 0 0 (h.bar (s : K))⁻¹ = (h.bar (s : K))⁻¹ • rkVec 0 0 1 by
      rw [rkVec_smul, mul_one, mul_zero],
    span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero hbs))]

theorem mem_rkOneT {x : Equiv.Perm (hypIsotropicLines h 1 1)} :
    x ∈ rkOneT h ↔ ∃ s : Kˣ, rkOneTElt h s = x :=
  ⟨fun ⟨s, hs⟩ => ⟨s, hs⟩, fun ⟨s, hs⟩ => ⟨s, hs⟩⟩

theorem rkOneT_le_rkOneG : rkOneT h ≤ rkOneG h := by
  rintro _ ⟨s, rfl⟩
  exact ⟨hypProj h 1 1 (rkOneDHomSU h s), rfl⟩

theorem rkOneUStar_le_rkOneG : rkOneUStar h ≤ rkOneG h := by
  rintro _ ⟨x, -, rfl⟩
  exact ⟨x, rfl⟩

@[expose] noncomputable def rkOneGInf : Subgroup (Equiv.Perm (hypIsotropicLines h 1 1)) :=
  rkOneG h ⊓ MulAction.stabilizer (Equiv.Perm (hypIsotropicLines h 1 1)) (infL h)

@[expose] noncomputable def rkOneGZero : Subgroup (Equiv.Perm (hypIsotropicLines h 1 1)) :=
  rkOneG h ⊓ MulAction.stabilizer (Equiv.Perm (hypIsotropicLines h 1 1)) (zeroL h)

theorem mem_rkOneGInf {x : Equiv.Perm (hypIsotropicLines h 1 1)} :
    x ∈ rkOneGInf h ↔ x ∈ rkOneG h ∧ x (infL h) = infL h :=
  Iff.rfl

theorem mem_rkOneGZero {x : Equiv.Perm (hypIsotropicLines h 1 1)} :
    x ∈ rkOneGZero h ↔ x ∈ rkOneG h ∧ x (zeroL h) = zeroL h :=
  Iff.rfl

theorem rkOneUStar_fix {x : Equiv.Perm (hypIsotropicLines h 1 1)} (hx : x ∈ rkOneUStar h) :
    x (infL h) = infL h := by
  obtain ⟨a, b, hab, rfl⟩ := (mem_rkOneUStar h).mp hx
  exact rkOneU_infL h hab

theorem mem_hypUnitriangular_of_fix {g : hypSU h 1 1}
    (hg : ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ rkVec 1 0 0 =
      rkVec 1 0 0) : g ∈ hypUnitriangular h 1 1 := by
  set M := ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) with hM
  have hcol := hg
  rw [mulVec_rkVec] at hcol
  simp only [mul_one, mul_zero, add_zero] at hcol
  obtain ⟨hee, hze, hfe⟩ := rkVec_injective hcol
  have hiso : ∀ u v, hypForm h 1 1 (M *ᵥ u) (M *ᵥ v) = hypForm h 1 1 u v :=
    fun u v => hypForm_smul_smul h g u v
  have h1 := hiso (rkVec 1 0 0) (rkVec 0 0 1)
  rw [hg, mulVec_rkVec, hypForm_rkVec, hypForm_rkVec] at h1
  simp only [mul_zero, add_zero, zero_add, mul_one, map_one, map_zero, one_mul, zero_mul] at h1
  have h2 := hiso (rkVec 1 0 0) (rkVec 0 1 0)
  rw [hg, mulVec_rkVec, hypForm_rkVec, hypForm_rkVec] at h2
  simp only [mul_zero, add_zero, zero_add, mul_one, map_one, map_zero, one_mul, zero_mul] at h2
  have hdet := (mem_hypSU.mp g.2).2
  rw [← hM, ← det_submatrix_equiv_self hypIndexFin3.symm M, det_fin_three] at hdet
  have e0 : hypIndexFin3.symm 0 = (.inl 0 : HypIndex 1 1) := rfl
  have e1 : hypIndexFin3.symm 1 = (.inr (.inl 0) : HypIndex 1 1) := rfl
  have e2 : hypIndexFin3.symm 2 = (.inr (.inr 0) : HypIndex 1 1) := rfl
  simp only [submatrix_apply, e0, e1, e2, hee, hze, hfe, h1, h2] at hdet
  have hzz : M (.inr (.inl 0)) (.inr (.inl 0)) = 1 := by linear_combination hdet
  refine mem_hypUnitriangular.mpr ⟨fun i j hij => ?_, fun i => ?_⟩
  · rcases i with i | i | i <;> rcases j with j | j | j <;>
      obtain rfl := Fin.fin_one_eq_zero i <;> obtain rfl := Fin.fin_one_eq_zero j <;>
      simp [fullPos] at hij
    · exact hze
    · exact hfe
    · exact h2
  · rcases i with i | i | i <;> obtain rfl := Fin.fin_one_eq_zero i
    · exact hee
    · exact hzz
    · exact h1

theorem mem_rkOneGInf_iff {x : Equiv.Perm (hypIsotropicLines h 1 1)} :
    x ∈ rkOneGInf h ↔ ∃ u ∈ rkOneUStar h, ∃ t ∈ rkOneT h, x = u * t := by
  constructor
  · rintro ⟨⟨y, rfl⟩, hx⟩
    obtain ⟨g, rfl⟩ := hypProj_surjective h 1 1 y
    have hx' := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hx)
    change ((g : GL (HypIndex 1 1) K)) • (infL h : Submodule K (HypIndex 1 1 → K)) =
      (infL h : Submodule K (HypIndex 1 1 → K)) at hx'
    rw [coe_infL, gl_smul_span] at hx'
    have hge : ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
        rkVec 1 0 0 ∈ K ∙ rkVec 1 0 (0 : K) := by
      rw [← hx']
      exact mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hge
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      have h1 := congrArg (fun v => (((g⁻¹ : hypSU h 1 1) : GL (HypIndex 1 1) K) :
        Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ v) hc
      simp only [mulVec_zero, mulVec_mulVec] at h1
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one,
        one_mulVec] at h1
      exact one_ne_zero (rkVec_eq_zero_iff.mp h1.symm).1
    set su := Units.mk0 c hc0 with hsu
    set g' := g * (rkOneDHomSU h su)⁻¹ with hg'
    have hfix : ((g' : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
        rkVec 1 0 0 = rkVec 1 0 0 := by
      have hd : ((rkOneDHomSU h su⁻¹ : hypSU h 1 1) : GL (HypIndex 1 1) K) *ᵥ
          (rkVec 1 0 0 : HypIndex 1 1 → K) = c⁻¹ • rkVec 1 0 0 := by
        change rkOneD h (su⁻¹ : Kˣ) *ᵥ rkVec 1 0 0 = _
        rw [rkOneD_mulVec, rkVec_smul]
        simp [hsu]
      rw [hg', ← map_inv, Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, hd, mulVec_smul, ← hc,
        smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hU := mem_hypUnitriangular_of_fix h hfix
    refine ⟨rkOneUHom h ⟨g', hU⟩, ?_, rkOneTElt h su, ⟨su, rfl⟩, ?_⟩
    · rw [← range_rkOneUHom]
      exact ⟨_, rfl⟩
    · change hypProjLineAction h 1 1 (hypProj h 1 1 g) =
        hypProjLineAction h 1 1 (hypProj h 1 1 g') *
          hypProjLineAction h 1 1 (hypProj h 1 1 (rkOneDHomSU h su))
      rw [← map_mul, ← map_mul, hg', inv_mul_cancel_right]
  · rintro ⟨u, hu, t, ht, rfl⟩
    refine ⟨mul_mem (rkOneUStar_le_rkOneG h hu) (rkOneT_le_rkOneG h ht), ?_⟩
    obtain ⟨s, rfl⟩ := (mem_rkOneT h).mp ht
    show u * rkOneTElt h s ∈ MulAction.stabilizer (Equiv.Perm (hypIsotropicLines h 1 1)) (infL h)
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, Equiv.Perm.mul_apply, rkOneTElt_infL,
      rkOneUStar_fix h hu]

theorem rkOneGInf_inf_rkOneGZero : rkOneGInf h ⊓ rkOneGZero h = rkOneT h := by
  apply le_antisymm
  · rintro x ⟨hx, -, hx0⟩
    obtain ⟨u, hu, t, ht, rfl⟩ := (mem_rkOneGInf_iff h).mp hx
    obtain ⟨s, rfl⟩ := (mem_rkOneT h).mp ht
    obtain ⟨a, b, hab, rfl⟩ := (mem_rkOneUStar h).mp hu
    have h0 := MulAction.mem_stabilizer_iff.mp hx0
    rw [Equiv.Perm.smul_def, Equiv.Perm.mul_apply, rkOneTElt_zeroL, rkOneU_zeroL,
      ← rkPtL_zero h] at h0
    obtain ⟨rfl, rfl⟩ := eq_of_span_rkVec_eq (congrArg Subtype.val h0)
    rw [rkOneU_zero_zero, one_mul]
    exact ⟨s, rfl⟩
  · intro x hx
    obtain ⟨s, rfl⟩ := (mem_rkOneT h).mp hx
    exact ⟨⟨rkOneT_le_rkOneG h hx, rkOneTElt_infL h s⟩,
      ⟨rkOneT_le_rkOneG h hx, rkOneTElt_zeroL h s⟩⟩

end Stabilizers

section Sylow

variable (h : UnitaryFieldData p f K)

theorem rkOneUStar_le_rkOneGInf : rkOneUStar h ≤ rkOneGInf h := fun _ hx =>
  ⟨rkOneUStar_le_rkOneG h hx, MulAction.mem_stabilizer_iff.mpr (rkOneUStar_fix h hx)⟩

theorem rkOneT_le_rkOneGInf : rkOneT h ≤ rkOneGInf h := fun x hx =>
  (rkOneGInf_inf_rkOneGZero h ▸ hx : x ∈ rkOneGInf h ⊓ rkOneGZero h).1

theorem rkOneUStar_normal : ((rkOneUStar h).subgroupOf (rkOneGInf h)).Normal := by
  refine ⟨fun n hn x => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨u, hu, t, ht, hx⟩ := (mem_rkOneGInf_iff h).mp x.2
  obtain ⟨s, rfl⟩ := (mem_rkOneT h).mp ht
  obtain ⟨c, d, hcd, hn'⟩ := (mem_rkOneUStar h).mp hn
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx, ← hn']
  have he : u * rkOneTElt h s * rkOneU h c d hcd * (u * rkOneTElt h s)⁻¹ =
      u * (rkOneTElt h s * rkOneU h c d hcd * (rkOneTElt h s)⁻¹) * u⁻¹ := by group
  rw [he, rkOneTElt_conj]
  exact mul_mem (mul_mem hu (rkOneU_mem h _)) (inv_mem hu)

theorem finite_hypIsotropicLines_one : Finite (hypIsotropicLines h 1 1) := by
  have := h.finite
  have : Finite (Submodule K (HypIndex 1 1 → K)) := Finite.of_injective _ SetLike.coe_injective
  exact Subtype.finite

theorem rkOneTElt_inv (s : Kˣ) : rkOneTElt h s⁻¹ = (rkOneTElt h s)⁻¹ := by
  simp only [rkOneTElt, map_inv]

theorem exists_rkOneT_mul_rkOneUStar {x : Equiv.Perm (hypIsotropicLines h 1 1)}
    (hx : x ∈ rkOneGInf h) : ∃ t ∈ rkOneT h, ∃ u ∈ rkOneUStar h, x = t * u := by
  obtain ⟨u, hu, t, ht, hx⟩ := (mem_rkOneGInf_iff h).mp hx
  obtain ⟨s, rfl⟩ := (mem_rkOneT h).mp ht
  obtain ⟨a, b, hab, rfl⟩ := (mem_rkOneUStar h).mp hu
  have hz : (rkOneTElt h s)⁻¹ * rkOneU h a b hab * rkOneTElt h s ∈ rkOneUStar h := by
    have := rkOneTElt_conj h s⁻¹ hab
    rw [rkOneTElt_inv, inv_inv] at this
    rw [this]
    exact rkOneU_mem h _
  refine ⟨rkOneTElt h s, ht, _, hz, ?_⟩
  rw [hx]
  group

theorem rkOneT_inf_rkOneUStar {x : Equiv.Perm (hypIsotropicLines h 1 1)} (hT : x ∈ rkOneT h)
    (hU : x ∈ rkOneUStar h) : x = 1 := by
  obtain ⟨s, rfl⟩ := (mem_rkOneT h).mp hT
  obtain ⟨a, b, hab, he⟩ := (mem_rkOneUStar h).mp hU
  have h0 := rkOneTElt_zeroL h s
  rw [← he, rkOneU_zeroL, ← rkPtL_zero h] at h0
  rw [← he]
  obtain ⟨rfl, rfl⟩ := eq_of_span_rkVec_eq (congrArg Subtype.val h0)
  exact rkOneU_zero_zero h

theorem rkOneUStar_index_eq :
    ((rkOneUStar h).subgroupOf (rkOneGInf h)).index = Nat.card (rkOneT h) := by
  have := finite_hypIsotropicLines_one h
  let F : rkOneT h × rkOneUStar h → rkOneGInf h := fun x =>
    ⟨(x.1 : Equiv.Perm (hypIsotropicLines h 1 1)) * x.2,
      mul_mem (rkOneT_le_rkOneGInf h x.1.2) (rkOneUStar_le_rkOneGInf h x.2.2)⟩
  have hF : Function.Bijective F := by
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · have he : ((y.1 : Equiv.Perm (hypIsotropicLines h 1 1)))⁻¹ * x.1 =
          y.2 * (x.2 : Equiv.Perm (hypIsotropicLines h 1 1))⁻¹ := by
        have := congrArg Subtype.val hxy
        change (x.1 : Equiv.Perm (hypIsotropicLines h 1 1)) * x.2 = y.1 * y.2 at this
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← this, mul_inv_cancel_right]
      have h1 := rkOneT_inf_rkOneUStar h (mul_mem (inv_mem y.1.2) x.1.2)
        (he ▸ mul_mem y.2.2 (inv_mem x.2.2))
      have h2 : (x.1 : Equiv.Perm (hypIsotropicLines h 1 1)) = y.1 :=
        (inv_mul_eq_one.mp h1).symm
      have h3 : (x.2 : Equiv.Perm (hypIsotropicLines h 1 1)) = y.2 := by
        rw [h1] at he
        exact (mul_inv_eq_one.mp he.symm).symm
      exact Prod.ext (Subtype.ext h2) (Subtype.ext h3)
    · obtain ⟨t, ht, u, hu, hz⟩ := exists_rkOneT_mul_rkOneUStar h z.2
      exact ⟨(⟨t, ht⟩, ⟨u, hu⟩), Subtype.ext hz.symm⟩
  have hcard := Nat.card_congr (Equiv.ofBijective F hF)
  rw [Nat.card_prod] at hcard
  have hmul := Subgroup.card_mul_index ((rkOneUStar h).subgroupOf (rkOneGInf h))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rkOneUStar_le_rkOneGInf h)).toEquiv,
    ← hcard, mul_comm (Nat.card (rkOneT h))] at hmul
  have hpos : 0 < Nat.card (rkOneUStar h) := by
    rw [card_rkOneUStar]
    exact pow_pos (pow_pos h.prime.pos f) 3
  exact Nat.eq_of_mul_eq_mul_left hpos hmul

theorem not_dvd_index_rkOneUStar :
    ¬ p ∣ ((rkOneUStar h).subgroupOf (rkOneGInf h)).index := by
  have := h.finite
  have h2 : Nat.card (rkOneT h) ∣ Nat.card Kˣ := Subgroup.card_range_dvd _
  rw [Nat.card_units, UnitaryFieldData.card_eq_sq h] at h2
  intro hp
  have h3 : p ∣ (p ^ f) ^ 2 - 1 := ((rkOneUStar_index_eq h) ▸ hp).trans h2
  have h4 : p ∣ (p ^ f) ^ 2 := dvd_pow (dvd_pow_self p (by have := h.one_le; omega)) two_ne_zero
  have h5 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos h.prime.pos f)
  have h6 := Nat.dvd_sub h4 h3
  rw [Nat.sub_sub_self h5] at h6
  exact h.prime.one_lt.ne' (Nat.dvd_one.mp h6)

theorem rkOneUStar_eq_sylow (P : Sylow p (rkOneGInf h)) :
    (P : Subgroup (rkOneGInf h)) = (rkOneUStar h).subgroupOf (rkOneGInf h) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := finite_hypIsotropicLines_one h
  have hcardN : Nat.card ((rkOneUStar h).subgroupOf (rkOneGInf h)) = p ^ (3 * f) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rkOneUStar_le_rkOneGInf h)).toEquiv,
      card_rkOneUStar, ← pow_mul, mul_comm]
  have hpg : IsPGroup p ((rkOneUStar h).subgroupOf (rkOneGInf h)) := IsPGroup.of_card hcardN
  have hP₀ := IsPGroup.toSylow_coe hpg (not_dvd_index_rkOneUStar h)
  have : Unique (Sylow p (rkOneGInf h)) :=
    Sylow.unique_of_normal (hpg.toSylow (not_dvd_index_rkOneUStar h))
      (by rw [hP₀]; exact rkOneUStar_normal h)
  rw [Subsingleton.elim P (hpg.toSylow (not_dvd_index_rkOneUStar h)), hP₀]

@[expose] noncomputable def rkOneWMat : Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
  (!![0, 0, 1; 0, -1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) K).submatrix hypIndexFin3 hypIndexFin3

theorem rkOneWMat_mulVec (x y w : K) : rkOneWMat *ᵥ rkVec x y w = rkVec w (-y) x := by
  rw [mulVec_rkVec]
  simp [rkOneWMat, hypIndexFin3]

theorem rkOneWMat_gram :
    ((rkOneWMat (K := K)).map h.bar)ᵀ * hypGram 1 1 K * rkOneWMat = hypGram 1 1 K := by
  refine (gramForm_isometry_iff h _ _).mp fun x y => ?_
  change hypForm h 1 1 _ _ = hypForm h 1 1 _ _
  rw [rkVec_eta x, rkVec_eta y, rkOneWMat_mulVec, rkOneWMat_mulVec, hypForm_rkVec, hypForm_rkVec,
    map_neg]
  ring

theorem det_rkOneWMat : (rkOneWMat (K := K)).det = 1 := by
  rw [rkOneWMat, det_submatrix_equiv_self, det_fin_three]
  simp

@[expose] noncomputable def rkOneW : hypSU h 1 1 :=
  mkHypSU h rkOneWMat (rkOneWMat_gram h) det_rkOneWMat

theorem rkOneW_infL : hypProjLineAction h 1 1 (hypProj h 1 1 (rkOneW h)) (infL h) = zeroL h := by
  apply Subtype.ext
  change ((rkOneW h : hypSU h 1 1) : GL (HypIndex 1 1) K) •
    (infL h : Submodule K (HypIndex 1 1 → K)) = _
  rw [coe_infL, gl_smul_span, coe_zeroL]
  change K ∙ (rkOneWMat *ᵥ rkVec 1 0 0) = _
  rw [rkOneWMat_mulVec, neg_zero]

theorem rkOneG_two_transitive (L₁ L₂ M₁ M₂ : hypIsotropicLines h 1 1) (hL : L₁ ≠ L₂)
    (hM : M₁ ≠ M₂) : ∃ g ∈ rkOneG h, g L₁ = M₁ ∧ g L₂ = M₂ := by
  have hpair : ∀ L₁ L₂ : hypIsotropicLines h 1 1, L₁ ≠ L₂ →
      ∃ g ∈ rkOneG h, g (infL h) = L₁ ∧ g (zeroL h) = L₂ := by
    intro L₁ L₂ hne
    obtain ⟨g₁, hg₁, hg₁L⟩ : ∃ g ∈ rkOneG h, g (infL h) = L₁ := by
      by_cases hL : L₁ = infL h
      · exact ⟨1, one_mem _, by rw [hL]; rfl⟩
      · obtain ⟨a, b, hab, hL'⟩ := exists_rkPtL_eq L₁ hL
        refine ⟨rkOneU h a b hab * hypProjLineAction h 1 1 (hypProj h 1 1 (rkOneW h)),
          mul_mem (rkOneUStar_le_rkOneG h (rkOneU_mem h hab)) ⟨_, rfl⟩, ?_⟩
        rw [Equiv.Perm.mul_apply, rkOneW_infL, rkOneU_zeroL, hL']
    have hL₂ : g₁⁻¹ L₂ ≠ infL h := fun he => hne (hg₁L.symm.trans (by
      rw [← he, Equiv.Perm.coe_inv, Equiv.apply_symm_apply]))
    obtain ⟨a, b, hab, hL₂'⟩ := exists_rkPtL_eq (g₁⁻¹ L₂) hL₂
    refine ⟨g₁ * rkOneU h a b hab, mul_mem hg₁ (rkOneUStar_le_rkOneG h (rkOneU_mem h hab)), ?_,
      ?_⟩
    · rw [Equiv.Perm.mul_apply, rkOneU_infL, hg₁L]
    · rw [Equiv.Perm.mul_apply, rkOneU_zeroL, hL₂', Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
  obtain ⟨g, hg, hg1, hg2⟩ := hpair L₁ L₂ hL
  obtain ⟨g', hg', hg'1, hg'2⟩ := hpair M₁ M₂ hM
  refine ⟨g' * g⁻¹, mul_mem hg' (inv_mem hg), ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, ← hg1, Equiv.Perm.coe_inv, Equiv.symm_apply_apply, hg'1]
  · rw [Equiv.Perm.mul_apply, ← hg2, Equiv.Perm.coe_inv, Equiv.symm_apply_apply, hg'2]

end Sylow

theorem unitary_rank_one_root_structure (h : UnitaryFieldData p f K) :
    (∀ x, x ∈ rkOneUStar h ↔
      ∃ (a b : K) (hab : h.norm a + h.trace b = 0), rkOneU h a b hab = x) ∧
    (∀ (a b a' b' : K) (hab : h.norm a + h.trace b = 0) (hab' : h.norm a' + h.trace b' = 0),
      rkOneU h a b hab = rkOneU h a' b' hab' → a = a' ∧ b = b') ∧
    Nat.card (rkOneUStar h) = (p ^ f) ^ 3 ∧
    rkOneC h = (Subgroup.center (rkOneUStar h)).map (rkOneUStar h).subtype ∧
    rkOneC h = ⁅rkOneUStar h, rkOneUStar h⁆ ∧
    (∃ φ : rkOneUStar h →* Multiplicative K,
      (∀ (a b : K) (hab : h.norm a + h.trace b = 0),
        φ ⟨rkOneU h a b hab, rkOneU_mem h hab⟩ = Multiplicative.ofAdd a) ∧
      Function.Surjective φ ∧ φ.ker = (rkOneC h).subgroupOf (rkOneUStar h)) ∧
    (∀ L : hypIsotropicLines h 1 1, L ≠ infL h →
      ∃! ab : K × K, h.norm ab.1 + h.trace ab.2 = 0 ∧
        (L : Submodule K (HypIndex 1 1 → K)) = K ∙ rkVec ab.2 ab.1 1) ∧
    (∀ (a b : K) (hab : h.norm a + h.trace b = 0),
      (rkOneU h a b hab (zeroL h) : Submodule K (HypIndex 1 1 → K)) = K ∙ rkVec b a 1) ∧
    (∀ x ∈ rkOneUStar h, x (infL h) = infL h) ∧
    (∀ L : hypIsotropicLines h 1 1, L ≠ infL h →
      ∃! x : Equiv.Perm (hypIsotropicLines h 1 1), x ∈ rkOneUStar h ∧ x (zeroL h) = L) ∧
    (∀ x, x ∈ rkOneGInf h ↔ ∃ u ∈ rkOneUStar h, ∃ t ∈ rkOneT h, x = u * t) ∧
    rkOneGInf h ⊓ rkOneGZero h = rkOneT h ∧
    rkOneUStar h ≤ rkOneGInf h ∧
    (∀ P : Sylow p (rkOneGInf h),
      (P : Subgroup (rkOneGInf h)) = (rkOneUStar h).subgroupOf (rkOneGInf h)) ∧
    (∀ L₁ L₂ M₁ M₂ : hypIsotropicLines h 1 1, L₁ ≠ L₂ → M₁ ≠ M₂ →
      ∃ g ∈ rkOneG h, g L₁ = M₁ ∧ g L₂ = M₂) := by
  refine ⟨fun x => mem_rkOneUStar h, fun a b a' b' hab hab' he => rkOneU_injective he,
    card_rkOneUStar h, rkOneC_eq_center h, rkOneC_eq_commutator h,
    ⟨rkOneAHom h, fun a b hab => rkOneAHom_rkOneU h hab, rkOneAHom_surjective h,
      ker_rkOneAHom h⟩, fun L hL => ?_, fun a b hab => by rw [rkOneU_zeroL, coe_rkPtL],
    fun x hx => rkOneUStar_fix h hx, fun L hL => ?_, fun x => mem_rkOneGInf_iff h,
    rkOneGInf_inf_rkOneGZero h, rkOneUStar_le_rkOneGInf h, rkOneUStar_eq_sylow h,
    fun L₁ L₂ M₁ M₂ hL hM => rkOneG_two_transitive h L₁ L₂ M₁ M₂ hL hM⟩
  · obtain ⟨a, b, hab, rfl⟩ := exists_rkPtL_eq L hL
    refine ⟨(a, b), ⟨hab, rfl⟩, fun ab hab' => ?_⟩
    obtain ⟨h1, h2⟩ := eq_of_span_rkVec_eq hab'.2
    exact Prod.ext h1.symm h2.symm
  · obtain ⟨a, b, hab, rfl⟩ := exists_rkPtL_eq L hL
    refine ⟨rkOneU h a b hab, ⟨rkOneU_mem h hab, rkOneU_zeroL h hab⟩, fun y ⟨hy, hy0⟩ => ?_⟩
    obtain ⟨a', b', hab', rfl⟩ := (mem_rkOneUStar h).mp hy
    rw [rkOneU_zeroL] at hy0
    obtain ⟨rfl, rfl⟩ := eq_of_span_rkVec_eq (congrArg Subtype.val hy0)
    rfl

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
