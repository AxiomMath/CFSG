module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E1Base

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.E1

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {τ : Tag} {K : Type} [Field K]

theorem rootChar_single' (b : Fin τ.rank → Kˣ) (i : Fin τ.rank) :
    rootChar b (Pi.single i 1) = b i := by
  rw [rootChar, Finset.prod_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, zpow_zero])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, zpow_one]

theorem reflect_single_of_cartan {i j : Fin τ.rank} (hij : τ.cartan i j = -1) :
    reflect τ i (Pi.single j 1) = Pi.single j 1 + Pi.single i 1 := by
  rw [reflect, Finset.sum_eq_single j (fun k _ hk => by rw [Pi.single_eq_of_ne hk, mul_zero])
    (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, mul_one, hij, neg_one_smul,
    sub_neg_eq_add]

theorem exists_rootChar_eq_one_of_cartan {i j : Fin τ.rank} (hij : τ.cartan i j = -1)
    (b : Fin τ.rank → Kˣ) (hb : ∀ k, b k = 1 ∨ b k = -1) :
    ∃ β, IsRoot τ β ∧ rootChar b β = 1 := by
  rcases hb i with hi | hi
  · exact ⟨_, .basis i, by rw [rootChar_single', hi]⟩
  rcases hb j with hj | hj
  · exact ⟨_, .basis j, by rw [rootChar_single', hj]⟩
  refine ⟨_, (IsRoot.basis j).reflect i, ?_⟩
  rw [reflect_single_of_cartan hij, rootChar_add, rootChar_single', rootChar_single', hi, hj]
  simp

theorem exists_rootChar_eq_one (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8)
    (b : Fin τ.rank → Kˣ) (hb : ∀ k, b k = 1 ∨ b k = -1) :
    ∃ β, IsRoot τ β ∧ rootChar b β = 1 := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact exists_rootChar_eq_one_of_cartan (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩)
      (by decide) b hb
  · exact exists_rootChar_eq_one_of_cartan (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩)
      (by decide) b hb
  · exact exists_rootChar_eq_one_of_cartan (i := ⟨0, by decide⟩) (j := ⟨2, by decide⟩)
      (by decide) b hb
  · exact exists_rootChar_eq_one_of_cartan (i := ⟨0, by decide⟩) (j := ⟨2, by decide⟩)
      (by decide) b hb

theorem range_rootSL2_le_toralCentralizer
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) {b : Fin τ.rank → Kˣ}
    (hb1 : rootChar b β = 1) : (rootSL2 τ K β).range ≤ toralCentralizer τ K b := by
  have hk : β ∈ rootCharKernel b := ⟨hβ, hb1⟩
  have hk' : -β ∈ rootCharKernel b := by
    refine ⟨CFSG.LieType.Chevalley.IsRoot.neg hβ, ?_⟩
    rw [show -β = (-1 : ℤ) • β by simp, rootChar_zsmul, hb1, one_zpow]
  rw [ExcSelector.range_rootSL2_eq hβ]
  refine le_trans ?_ (rootSpan_rootCharKernel_le_toralCentralizer b)
  exact sup_le (le_iSup₂ (f := fun γ (_ : γ ∈ rootCharKernel b) => rootSubgroup τ K γ) β hk)
    (le_iSup₂ (f := fun γ (_ : γ ∈ rootCharKernel b) => rootSubgroup τ K γ) (-β) hk')

variable [Finite K]

theorem not_isPGroup_inner_diagonal
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8)
    (hK : Odd (Nat.card K)) {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K}
    {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) =
      (g : ModGL τ K) * rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹)
    (hα : α ^ 2 = 1) :
    ¬ IsPGroup 2 (↥(fixedSubgroup α) ⧸ pPrimeCore 2 ↥(fixedSubgroup α)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set Lc := AlgebraicClosure K
  set ι := algebraMap K Lc with hι
  set p := ringChar K with hp_def
  have hpK : CharP K p := ringChar.charP K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP Lc p := charP_of_injective_algebraMap (algebraMap K Lc).injective p
  have hK2 : ringChar K ≠ 2 := by
    intro h2
    have h2' : p = 2 := h2
    rw [Nat.card_eq_fintype_card, hcard, h2'] at hK
    exact Nat.not_even_iff_odd.2 hK ((Nat.even_pow' n.ne_zero).2 even_two)
  set Fr := iterateFrobenius Lc p n with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFr_def, iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  have hFrι : ∀ c : K, Fr (ι c) = ι c := fun c => by
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  set b : Fin τ.rank → Lcˣ := fun i => Units.map ι.toMonoidHom (a i) with hb_def
  set x := baseChangeGL ι (g : ModGL τ K) * rootDiagUnit τ b with hx_def
  obtain ⟨hinj, hHG, hfaith, -⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness τ K hK Lc ι
  have hgG : baseChangeGL ι (g : ModGL τ K) ∈ adjointGroup τ Lc := hHG ⟨g, g.2, rfl⟩
  have hxG : x ∈ adjointGroup τ Lc :=
    mul_mem hgG (exceptional_Lang_adjoint_diagonal_lift τ Lc b).1
  have hdb : baseChangeGL ι (rootDiagUnit τ a) = rootDiagUnit τ b := baseChangeGL_rootDiagUnit ι a
  have hxconj : ∀ h : adjointGroup τ K,
      x * baseChangeGL ι (h : ModGL τ K) * x⁻¹ = baseChangeGL ι (α h : ModGL τ K) := by
    intro h
    rw [hαg h, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hdb, hx_def]
    group
  obtain ⟨-, hHR, -, -⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group τ K hK Lc Fr hFr
  have hgR := hHR ⟨g, g.2, rfl⟩
  have hFd : Units.map (entrywiseHom Fr) (rootDiagUnit τ b) = rootDiagUnit τ b := by
    refine Units.ext ?_
    change entrywise Fr (rootDiag b) = rootDiag b
    rw [entrywise_rootDiag]
    congr 1
    funext i
    ext
    exact hFrι _
  have hxR : x ∈ adjointGroup τ Lc ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    refine Subgroup.mem_inf.2 ⟨hxG, ?_⟩
    change Units.map (entrywiseHom Fr) x = x
    rw [hx_def, map_mul, hFd]
    congr 1
    exact (Subgroup.mem_inf.1 hgR).2
  have hα2 : ∀ h, α (α h) = h := fun h => by
    have := congrArg (fun φ : MulAut (adjointGroup τ K) => φ h) hα
    simpa [sq] using this
  have hx2 : x ^ 2 = 1 := by
    refine hfaith _ (pow_mem hxG 2) fun y hy => ?_
    obtain ⟨h, hh, rfl⟩ := hy
    have h1 := hxconj ⟨h, hh⟩
    have h2 := hxconj (α ⟨h, hh⟩)
    rw [hα2] at h2
    change x * baseChangeGL ι h * x⁻¹ = _ at h1
    change _ = baseChangeGL ι h at h2
    rw [sq]
    calc x * x * baseChangeGL ι h =
        (x * (x * baseChangeGL ι h * x⁻¹) * x⁻¹) * (x * x) := by group
      _ = baseChangeGL ι h * (x * x) := by rw [h1, h2]
  obtain ⟨h, -, a', ha', -, -, hCh, -⟩ :=
    G2_F4_E6_E8_rational_inner_diagonal_involution_fixed_p_components τ K Lc hτ hK Fr hFr hxR
      hx2
  set H := (adjointGroup τ K).map (baseChangeGL ι) with hH
  let φ : adjointGroup τ K →* ModGL τ Lc := (baseChangeGL ι).comp (adjointGroup τ K).subtype
  have hφ : Function.Injective φ := hinj.comp Subtype.val_injective
  have hmap : (fixedSubgroup α).map φ = H ⊓ Subgroup.centralizer {x} := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨⟨c, c.2, rfl⟩, ?_⟩
      have h1 := hxconj c
      have hc' : α c = c := hc
      rw [hc'] at h1
      change baseChangeGL ι (c : ModGL τ K) * x = x * baseChangeGL ι (c : ModGL τ K)
      calc baseChangeGL ι (c : ModGL τ K) * x =
          (x * baseChangeGL ι (c : ModGL τ K) * x⁻¹) * x := by rw [h1]
        _ = x * baseChangeGL ι (c : ModGL τ K) := by group
    · rintro ⟨⟨c, hc, rfl⟩, hcx⟩
      refine ⟨⟨c, hc⟩, ?_, rfl⟩
      have h1 := hxconj ⟨c, hc⟩
      have h2 : x * baseChangeGL ι c * x⁻¹ = baseChangeGL ι c := by
        rw [← hcx]
        group
      rw [h2] at h1
      exact Subtype.ext (hinj h1.symm)
  set b' : Fin τ.rank → Kˣ := fun i => if a' i = 1 then 1 else -1 with hb'_def
  have hb' : ∀ i, b' i = 1 ∨ b' i = -1 := fun i => by
    by_cases h1 : a' i = 1 <;> simp [hb'_def, h1]
  have hab : (fun i => Units.map (algebraMap K Lc).toMonoidHom (b' i)) = a' := by
    funext i
    by_cases h1 : a' i = 1
    · simp [hb'_def, h1]
    · have h2 : a' i = -1 := (ha' i).resolve_left h1
      rw [h2]
      simp only [hb'_def, h1, ↓reduceIte]
      exact Units.ext (by simp)
  have hXK := map_baseChangeGL_toralCentralizer (algebraMap K Lc) b'
  rw [hab] at hXK
  have hE : (fixedSubgroup α).map ((MulAut.conj h).toMonoidHom.comp φ) =
      (toralCentralizer τ K b').map (baseChangeGL ι) := by
    rw [← Subgroup.map_map, hmap, hCh, hXK]
  obtain ⟨β, hβ, hβ1⟩ := exists_rootChar_eq_one hτ b' hb'
  have : Finite (ModGL τ K) := finite_modGL
  refine not_isPGroup_of_sl2_map ((MulAut.conj h).toMonoidHom.comp φ)
    ((MulAut.conj h).injective.comp hφ) hK2 ((baseChangeGL ι).comp (rootSL2 τ K β))
    ((baseChangeGL_injective ι).comp (ExcSelector.rootSL2_injective_of_ne_two hK2 β)) ?_
  rw [hE, MonoidHom.range_comp]
  exact map_mono (range_rootSL2_le_toralCentralizer hβ hβ1)

end CFSG.ComponentClassification.HarrisLit.L33.E1
