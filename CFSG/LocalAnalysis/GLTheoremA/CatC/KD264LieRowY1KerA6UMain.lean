module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6UKern
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4UKern

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.KD264LieA4

variable {p f : ℕ} {K : Type} [Field K]

theorem Fdiag_le_Dfull (K : Type) [Field K] : Fdiag K ≤ Dfull K := by
  rintro x ⟨⟨⟨a, c⟩, hac⟩, rfl⟩
  have ha : a ∈ mu3U K := (Subgroup.mem_prod.mp hac).1
  have hc : c ∈ mu3U K := (Subgroup.mem_prod.mp hac).2
  refine ⟨![⟨a, ha⟩, ⟨a, ha⟩, ⟨c, hc⟩], ?_⟩
  have hv : Dhom K ![⟨a, ha⟩, ⟨a, ha⟩, ⟨c, hc⟩] = ![a, a, c] := by
    funext k
    fin_cases k <;> rfl
  change diagGen (Dhom K ![⟨a, ha⟩, ⟨a, ha⟩, ⟨c, hc⟩]) = diagU a c
  rw [hv, diagU_eq_diagGen]

theorem Fdiag_card (K : Type) [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    Nat.card (Fdiag K) = 9 := by
  have hinj : Function.Injective (diagUHom.comp (Subgroup.prod (mu3U K) (mu3U K)).subtype :
      (Subgroup.prod (mu3U K) (mu3U K)) →* GL (Fin 6) K) :=
    diagUHom_injective.comp Subtype.val_injective
  unfold Fdiag
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, card_mu3 K hζ]

theorem diagU_mem_Fdiag (K : Type) [Field K] {a c : Kˣ} (ha : a ∈ mu3U K) (hc : c ∈ mu3U K) :
    diagU a c ∈ Fdiag K :=
  ⟨⟨(a, c), Subgroup.mem_prod.mpr ⟨ha, hc⟩⟩, rfl⟩

theorem diagU_one_one : diagU (K := K) 1 1 = 1 := by
  apply Units.ext
  rw [diagU_val, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]

theorem Fdiag_scalar_one {x : GL (Fin 6) K} (hx : x ∈ Fdiag K) {c : K}
    (hxc : (x : Matrix (Fin 6) (Fin 6) K) = Matrix.scalar (Fin 6) c) : x = 1 := by
  obtain ⟨⟨⟨a, c'⟩, hac⟩, rfl⟩ := hx
  have ha : a ∈ mu3U K := (Subgroup.mem_prod.mp hac).1
  have hc' : c' ∈ mu3U K := (Subgroup.mem_prod.mp hac).2
  have ha3 : ((a : Kˣ) : K) ^ 3 = 1 := by
    have := (mem_rootsOfUnity 3 _).mp ha
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  have e0 := congrFun (congrFun hxc 0) 0
  have e3 := congrFun (congrFun hxc 3) 3
  have e2 := congrFun (congrFun hxc 2) 2
  change ((diagU a c' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) 0 0 = _ at e0
  change ((diagU a c' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) 3 3 = _ at e3
  change ((diagU a c' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) 2 2 = _ at e2
  rw [diagU_val] at e0 e3 e2
  simp [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at e0 e3 e2
  have hinv : ((a : Kˣ) : K)⁻¹ = ((a : Kˣ) : K) := by rw [e3, e0]
  have hcaa : ((a : Kˣ) : K) * ((a : Kˣ) : K) = 1 := by
    calc ((a : Kˣ) : K) * ((a : Kˣ) : K) = ((a : Kˣ) : K) * ((a : Kˣ) : K)⁻¹ := by rw [hinv]
      _ = 1 := mul_inv_cancel₀ (Units.ne_zero a)
  have ha1 : ((a : Kˣ) : K) = 1 := by
    have h3 : ((a : Kˣ) : K) ^ 3 = ((a : Kˣ) : K) := by
      rw [show ((a : Kˣ) : K) ^ 3 = ((a : Kˣ) : K) * (((a : Kˣ) : K) * ((a : Kˣ) : K)) by ring, hcaa,
        mul_one]
    rw [← h3, ha3]
  have hc1 : ((c' : Kˣ) : K) = 1 := by
    rw [e2]
    exact (e0.symm.trans ha1)
  have ha' : a = 1 := Units.ext ha1
  have hc'' : c' = 1 := Units.ext hc1
  subst ha' hc''
  exact diagU_one_one

theorem Fdiag_cube {f : GL (Fin 6) K} (hf : f ∈ Fdiag K) : f ^ 3 = 1 := by
  obtain ⟨⟨⟨a, c⟩, hac⟩, rfl⟩ := hf
  have ha : a ∈ mu3U K := (Subgroup.mem_prod.mp hac).1
  have hc : c ∈ mu3U K := (Subgroup.mem_prod.mp hac).2
  have ha3 : ((a : Kˣ) : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 _).mp ha, Units.val_one]
  have hc3 : ((c : Kˣ) : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 _).mp hc, Units.val_one]
  show diagUHom (a, c) ^ 3 = 1
  change diagU a c ^ 3 = 1
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, diagU_val, Matrix.diagonal_pow, Units.val_one, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [ha3, hc3]

theorem piJ_PsiJ_injective (h : UnitaryFieldData p f K) :
    Function.Injective ((piJ h).comp (PsiJ h)) := by
  rw [injective_iff_map_eq_one]
  intro X hX
  rw [MonoidHom.comp_apply] at hX
  obtain ⟨c, hc⟩ := (piJ_eq_one_iff h (PsiJ h X)).mp hX
  rw [PsiJ_coe] at hc
  have hc1 := Psi_scalar_one h X hc
  rw [hc1] at hc
  apply Psi_injective h
  rw [map_one]
  apply Units.ext
  rw [hc, Units.val_one]
  ext i j
  simp [Matrix.scalar_apply, Matrix.one_apply]

theorem Psi_comm_Fdiag (h : UnitaryFieldData p f K) (hbar : ∀ x : K, x ^ 3 = 1 → h.bar x = x)
    (X : Matrix.SpecialLinearGroup (Fin 2) K) {f : GL (Fin 6) K} (hf : f ∈ Fdiag K) :
    Psi h X * f = f * Psi h X := by
  obtain ⟨⟨⟨a, c⟩, hac⟩, rfl⟩ := hf
  have ha : a ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp (Subgroup.mem_prod.mp hac).1
  have hc : c ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp (Subgroup.mem_prod.mp hac).2
  exact Psi_comm_diagU h hbar X ha hc

theorem kerConcl_Dfull [Finite K] (h : UnitaryFieldData p f K)
    (hbar : ∀ x : K, x ^ 3 = 1 → h.bar x = x) {ζu : Kˣ} (hζ : IsPrimitiveRoot (ζu : K) 3)
    (hK4 : 4 ≤ Nat.card K) :
    KerConcl (((Dfull K).subgroupOf (gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K))).map (piJ h)) := by
  have hFle : Fdiag K ≤ gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K) :=
    (Fdiag_le_Dfull K).trans (Dfull_le h hbar)
  have hFE : ((Fdiag K).subgroupOf (gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K))).map (piJ h) ≤
      (((Dfull K).subgroupOf (gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K)))).map (piJ h) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono _ (Fdiag_le_Dfull K))
  have hinj : ∀ x ∈ (Fdiag K).subgroupOf (gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K)),
      piJ h x = 1 → x = 1 := by
    intro x hx hx1
    obtain ⟨c, hc⟩ := (piJ_eq_one_iff h x).mp hx1
    exact Subtype.ext (Fdiag_scalar_one (Subgroup.mem_subgroupOf.mp hx) hc)
  have hcard : Nat.card (((Fdiag K).subgroupOf (gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K))).map
      (piJ h)) = 9 := by
    rw [card_map_eq_of_injOn (piJ h) _ hinj]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFle).toEquiv]
    exact Fdiag_card K hζ
  have hζμ : ζu ∈ mu3U K := by
    rw [mem_rootsOfUnity]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hζ.pow_eq_one)
  have h1μ : (1 : Kˣ) ∈ mu3U K := one_mem _
  have hd1 : diagU ζu 1 ∈ Fdiag K := diagU_mem_Fdiag K hζμ h1μ
  have hd2 : diagU 1 ζu ∈ Fdiag K := diagU_mem_Fdiag K h1μ hζμ
  have hnorm : ∀ c ∈ Subgroup.centralizer
      (((Fdiag K).subgroupOf (gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K))).map (piJ h) :
        Set (PSUJ h)),
      ∀ n ∈ ((piJ h).comp (PsiJ h)).range, c * n * c⁻¹ ∈ ((piJ h).comp (PsiJ h)).range := by
    intro c hc n hn
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    have hcomm : ∀ f ∈ (Fdiag K).subgroupOf (gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K)),
        x * f = f * x := by
      intro f hf
      have hf3 : f ^ 3 = 1 := Subtype.ext (Fdiag_cube (Subgroup.mem_subgroupOf.mp hf))
      have hcf : piJ h f * piJ h x = piJ h x * piJ h f :=
        (Subgroup.mem_centralizer_iff.mp hc) (piJ h f) (Subgroup.mem_map.mpr ⟨f, hf, rfl⟩)
      exact comm_of_lift h hbar x f hf3 hcf.symm
    have h1 : (x : GL (Fin 6) K) * diagU ζu 1 = diagU ζu 1 * x :=
      congrArg Subtype.val (hcomm ⟨diagU ζu 1, hFle hd1⟩ (Subgroup.mem_subgroupOf.mpr hd1))
    have h2 : (x : GL (Fin 6) K) * diagU 1 ζu = diagU 1 ζu * x :=
      congrArg Subtype.val (hcomm ⟨diagU 1 ζu, hFle hd2⟩ (Subgroup.mem_subgroupOf.mpr hd2))
    obtain ⟨P, hxP, hz02, hz12, hz20, hz21⟩ := centralizer_block h hζ x.2 h1 h2
    obtain ⟨X, rfl⟩ := hn
    obtain ⟨X', hX'⟩ := Psi_normal h P hz02 hz12 hz20 hz21 X
    refine ⟨X', ?_⟩
    have hx' : x * PsiJ h X = PsiJ h X' * x := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, PsiJ_coe, PsiJ_coe, hxP]
      exact hX'
    have hfin : x * PsiJ h X * x⁻¹ = PsiJ h X' := by
      rw [hx', mul_assoc, mul_inv_cancel, mul_one]
    show piJ h (PsiJ h X') = piJ h x * piJ h (PsiJ h X) * (piJ h x)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, hfin]
  have hHC : ((piJ h).comp (PsiJ h)).range ≤ Subgroup.centralizer
      ((((Fdiag K).subgroupOf (gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K))).map (piJ h) :
        Subgroup (PSUJ h)) : Set (PSUJ h)) := by
    intro y hy
    obtain ⟨X, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.mp hf
    show piJ h f' * piJ h (PsiJ h X) = piJ h (PsiJ h X) * piJ h f'
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, PsiJ_coe]
    exact (Psi_comm_Fdiag h hbar X (Subgroup.mem_subgroupOf.mp hf')).symm
  have hNorm : (((piJ h).comp (PsiJ h)).range.subgroupOf (Subgroup.centralizer
      ((((Fdiag K).subgroupOf (gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K))).map (piJ h) :
        Subgroup (PSUJ h)) : Set (PSUJ h)))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hnorm (g : PSUJ h) g.2 (n : PSUJ h) hn
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact this
  have eq := MonoidHom.ofInjective (piJ_PsiJ_injective h)
  refine ⟨((Fdiag K).subgroupOf (gramSU h (hypJ : Matrix (Fin 6) (Fin 6) K))).map (piJ h), hFE,
    hcard, ((piJ h).comp (PsiJ h)).range, hHC, ?_, ?_, ?_⟩
  · exact CFSG.Open.IsSubnormal.step hHC hNorm (CFSG.Open.IsSubnormal.refl _)
  · exact isQuasisimple_equiv eq (isQuasisimple_SL2_field K hK4)
  · rw [← card_quotient_center_equiv eq]
    exact three_dvd_card_PSL2 hζ

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
