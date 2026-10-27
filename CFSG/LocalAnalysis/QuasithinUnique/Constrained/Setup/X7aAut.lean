module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aGroup
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Unitri

variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem exists_up3_of_mem_unitriangular {A : SL(3, F)} (hA : A ∈ unitriangular 3 F) :
    ∃ x y z : F, A = up3 x y z := by
  obtain ⟨hlow, hdiag⟩ := mem_unitriangular.mp hA
  refine ⟨A 1 2, A 0 2, A 0 1, ?_⟩
  apply Subtype.ext
  ext i j
  have h10 := hlow 1 0 (by decide)
  have h20 := hlow 2 0 (by decide)
  have h21 := hlow 2 1 (by decide)
  have h00 := hdiag 0
  have h11 := hdiag 1
  have h22 := hdiag 2
  fin_cases i <;> fin_cases j <;> simp [up3_coe, upMat, h10, h20, h21, h00, h11, h22]

theorem card_le_of_pairwise [Finite F] {ι : Type*} [Finite ι] (a : ι → SL(3, F)) (hinj : Function.Injective a)
    (hU : ∀ i, a i ∈ unitriangular 3 F) (hsq : ∀ i, a i * a i = 1)
    (hcomm : ∀ i j, a i * a j = a j * a i) : Nat.card ι ≤ Nat.card F ^ 2 := by
  choose x y z hxyz using fun i => exists_up3_of_mem_unitriangular (hU i)
  have hsq' : ∀ i, z i * x i = 0 := by
    intro i
    have h := hsq i
    rw [hxyz i, up3_mul, ← up3_zero] at h
    have := (up3_inj h).2.1
    have h2 : y i + y i = 0 := CharTwo.add_self_eq_zero (y i)
    linear_combination this - h2
  have hcomm' : ∀ i j, z i * x j = z j * x i := by
    intro i j
    have h := hcomm i j
    rw [hxyz i, hxyz j, up3_mul, up3_mul] at h
    have := (up3_inj h).2.1
    linear_combination this
  have hdich : (∀ i, z i = 0) ∨ ∀ i, x i = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hcon
    have hxi : x i = 0 := by
      have := hsq' i
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hi
      · exact h
    have hzj : z j = 0 := by
      have := hsq' j
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hj
    have := hcomm' i j
    rw [hxi, hzj] at this
    simp at this
    rcases this with h | h
    · exact hi h
    · exact hj h
  rcases hdich with hz | hx
  · have hinj' : Function.Injective fun i => (x i, y i) := by
      intro i j h
      simp only [Prod.mk.injEq] at h
      apply hinj
      rw [hxyz i, hxyz j, h.1, h.2, hz i, hz j]
    calc Nat.card ι ≤ Nat.card (F × F) := Nat.card_le_card_of_injective _ hinj'
      _ = Nat.card F ^ 2 := by rw [Nat.card_prod, sq]
  · have hinj' : Function.Injective fun i => (z i, y i) := by
      intro i j h
      simp only [Prod.mk.injEq] at h
      apply hinj
      rw [hxyz i, hxyz j, h.1, h.2, hx i, hx j]
    calc Nat.card ι ≤ Nat.card (F × F) := Nat.card_le_card_of_injective _ hinj'
      _ = Nat.card F ^ 2 := by rw [Nat.card_prod, sq]

end Unitri

section Proj

variable {F : Type*} [Field F] [CharP F 2] [Finite F]

theorem card_le_of_elementary_abelian_projectiveSL (B : Subgroup (projectiveSL 3 F))
    (hB2 : ∀ b ∈ B, b * b = 1) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    Nat.card B ≤ Nat.card F ^ 2 := by
  classical
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
  have hBp : IsPGroup 2 B := by
    intro b
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa [pow_two] using hB2 b b.2
  obtain ⟨Q, hBQ⟩ := hBp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (projectiveSL 3 F) Q S
  have hmem : ∀ b : B, g * (b : projectiveSL 3 F) * g⁻¹ ∈ projUnitriangular 3 F := by
    intro b
    have h1 : (b : projectiveSL 3 F) ∈ ((Q : Subgroup (projectiveSL 3 F)) : Set _) := hBQ b.2
    have h2 : MulAut.conj g (b : projectiveSL 3 F) ∈
        ((g • Q : Sylow 2 (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
      rw [Sylow.coe_smul]
      exact Set.smul_mem_smul_set h1
    rw [hg] at h2
    have h3 : MulAut.conj g (b : projectiveSL 3 F) ∈ (S : Subgroup (projectiveSL 3 F)) := h2
    rw [hS] at h3
    rwa [MulAut.conj_apply] at h3
  choose a ha hπ using fun b : B => Subgroup.mem_map.mp (hmem b)
  have hker : ∀ x : SL(3, F), x ∈ unitriangular 3 F → proj 3 F x = 1 → x = 1 := by
    intro x hx h1
    have h2 : x ∈ unitriangular 3 F ⊓ scalars 3 F := ⟨hx, proj_eq_one_iff.mp h1⟩
    rw [unitriangular_inf_scalars] at h2
    exact Subgroup.mem_bot.mp h2
  refine card_le_of_pairwise a ?_ ha ?_ ?_
  · intro b b' h
    have h1 : g * (b : projectiveSL 3 F) * g⁻¹ = g * (b' : projectiveSL 3 F) * g⁻¹ := by
      rw [← hπ b, ← hπ b', h]
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  · intro b
    refine hker _ ((unitriangular 3 F).mul_mem (ha b) (ha b)) ?_
    rw [map_mul, hπ b]
    calc g * (b : projectiveSL 3 F) * g⁻¹ * (g * (b : projectiveSL 3 F) * g⁻¹)
        = g * ((b : projectiveSL 3 F) * b) * g⁻¹ := by group
      _ = 1 := by rw [hB2 b b.2]; group
  · intro b b'
    have hx : (a b * a b')⁻¹ * (a b' * a b) = 1 := by
      refine hker _ ((unitriangular 3 F).mul_mem ((unitriangular 3 F).inv_mem
        ((unitriangular 3 F).mul_mem (ha b) (ha b'))) ((unitriangular 3 F).mul_mem (ha b')
        (ha b))) ?_
      rw [map_mul, map_inv, map_mul, map_mul, hπ b, hπ b']
      have hc := hBc b b.2 b' b'.2
      calc (g * (b : projectiveSL 3 F) * g⁻¹ * (g * (b' : projectiveSL 3 F) * g⁻¹))⁻¹ *
            (g * (b' : projectiveSL 3 F) * g⁻¹ * (g * (b : projectiveSL 3 F) * g⁻¹))
          = (g * ((b : projectiveSL 3 F) * b') * g⁻¹)⁻¹ *
            (g * ((b' : projectiveSL 3 F) * b) * g⁻¹) := by group
        _ = 1 := by rw [hc]; group
    exact inv_mul_eq_one.mp hx

end Proj

section AutChain

variable {F : Type*} [Field F] [CharP F 2] [Finite F]

omit [CharP F 2] in
theorem center_projectiveSL_three_eq_bot' : Subgroup.center (projectiveSL 3 F) = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  obtain ⟨g, rfl⟩ := proj_surjective 3 F z
  have hconj : conjAut 3 F (Matrix.SpecialLinearGroup.toGL g) = 1 := by
    rw [conjAut_toGL]
    ext x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← Subgroup.mem_center_iff.1 hz x, mul_inv_cancel_right]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (K := F) (n := 3) le_rfl
    (Matrix.SpecialLinearGroup.toGL g) 1 (by rw [map_one, mul_one]; exact hconj)
  have hmat := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) hc
  simp only [GeneralLinearGroup.coe_scalar] at hmat
  have hdet : c ^ 3 = 1 := by
    apply Units.ext
    have h1 := congrArg Matrix.det hmat
    rw [Matrix.scalar_apply, Matrix.det_diagonal] at h1
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    rw [Units.val_pow_eq_pow_val, h1]
    exact g.2
  exact Subgroup.mem_bot.2 (proj_eq_one_iff.2 ⟨c, hdet, hmat.symm⟩)

omit [CharP F 2] in
theorem conj_injective_projectiveSL :
    Function.Injective (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) := by
  intro g h hgh
  have hmem : g⁻¹ * h ∈ Subgroup.center (projectiveSL 3 F) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz := congrArg (fun φ : MulAut (projectiveSL 3 F) => φ z) hgh
    simp only [MulAut.conj_apply] at hz
    calc z * (g⁻¹ * h) = g⁻¹ * (g * z * g⁻¹) * h := by group
      _ = g⁻¹ * (h * z * h⁻¹) * h := by rw [hz]
      _ = g⁻¹ * h * z := by group
  rw [center_projectiveSL_three_eq_bot', Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.mp hmem

theorem mem_inner_of_sq_conjAut {A : GL (Fin 3) F}
    (h : conjAut 3 F A * conjAut 3 F A = 1) :
    conjAut 3 F A ∈ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range := by
  have := Fintype.ofFinite F
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (K := F) (n := 3) le_rfl (A * A) 1
    (by rw [map_one, mul_one, map_mul]; exact h)
  obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) (c : F)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact c.ne_zero (by rw [hμ]; simp)
  let m : Fˣ := Units.mk0 μ hμ0
  have hcm : c = m * m := Units.ext (by simp [m, hμ])
  have hcen : ∀ B : GL (Fin 3) F, B * GeneralLinearGroup.scalar (Fin 3) m⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) m⁻¹ * B := by
    intro B
    have hz : GeneralLinearGroup.scalar (Fin 3) m⁻¹ ∈ Subgroup.center (GL (Fin 3) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨m⁻¹, rfl⟩
    exact Subgroup.mem_center_iff.mp hz B
  set A' : GL (Fin 3) F := GeneralLinearGroup.scalar (Fin 3) m⁻¹ * A with hA'
  have hA'A' : A' * A' = 1 := by
    have h1 : A' * A' = GeneralLinearGroup.scalar (Fin 3) m⁻¹ *
        GeneralLinearGroup.scalar (Fin 3) m⁻¹ * (A * A) := by
      rw [hA']
      calc GeneralLinearGroup.scalar (Fin 3) m⁻¹ * A *
            (GeneralLinearGroup.scalar (Fin 3) m⁻¹ * A)
          = GeneralLinearGroup.scalar (Fin 3) m⁻¹ *
            (A * GeneralLinearGroup.scalar (Fin 3) m⁻¹) * A := by group
        _ = _ := by rw [hcen A]; group
    rw [h1, ← hc, ← map_mul, ← map_mul, hcm]
    have : m⁻¹ * m⁻¹ * (m * m) = 1 := by group
    rw [this, map_one]
  have hdet2 : ((A'.det : Fˣ) : F) ^ 2 = 1 := by
    have := congrArg (fun B : GL (Fin 3) F => ((Matrix.GeneralLinearGroup.det B : Fˣ) : F)) hA'A'
    simp only [map_mul, Units.val_mul, map_one, Units.val_one] at this
    rw [sq]
    exact this
  have hdet1 : ((A'.det : Fˣ) : F) = 1 := by
    have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
    have h3 : (((A'.det : Fˣ) : F) - 1) ^ 2 = 0 := by
      linear_combination hdet2 + (1 - ((A'.det : Fˣ) : F)) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h3)
  let g : SL(3, F) := ⟨(A' : Matrix (Fin 3) (Fin 3) F), by
    have := hdet1
    simpa [Matrix.GeneralLinearGroup.det] using this⟩
  have hgA' : Matrix.SpecialLinearGroup.toGL g = A' := by
    apply Units.ext
    rfl
  have hAA' : A = GeneralLinearGroup.scalar (Fin 3) m * A' := by
    rw [hA', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hconjA : conjAut 3 F A = conjAut 3 F A' := by
    conv_lhs => rw [hAA']
    rw [map_mul, conjAut_scalar, one_mul]
  exact ⟨proj 3 F g, by rw [← conjAut_toGL, hgA', hconjA]⟩

theorem elementary_automorphism_rank_bound {f : ℕ} (_hf : 2 ≤ f) (hF : Nat.card F = 2 ^ f)
    (A : Subgroup (MulAut (projectiveSL 3 F))) [CFSG.IsElementaryAbelian 2 A] :
    Nat.card ↥(A ⊓ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range) ≤
        2 ^ (2 * f) ∧
      (A ⊓ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range).relIndex A ≤ 4 ∧
      Nat.card A ≤ 2 ^ (2 * f + 2) ∧
      (A ⊓ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range = ⊥ →
        Nat.card A ≤ 4) := by
  classical
  obtain ⟨hID, -, hDnorm, -, -, hEcyc, -, hRE, -, -⟩ := standard_outer_quotients (K := F) (n := 3)
  have hR : standardAutGroup 3 F = ⊤ := (automorphism_generation (K := F) le_rfl).1
  set I := (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range with hI
  set D := linearAutGroup 3 F with hD
  set E := semilinearAutGroup 3 F with hE
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((inferInstance : IsMulCommutative A).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hDE : D ≤ E := linearAutGroup_le_semilinearAutGroup
  have hAD : A ⊓ D = A ⊓ I := by
    refine le_antisymm ?_ (inf_le_inf_left _ hID)
    rintro a ⟨haA, haD⟩
    obtain ⟨B, rfl⟩ := mem_linearAutGroup_iff.mp haD
    exact ⟨haA, mem_inner_of_sq_conjAut (hA2 _ haA)⟩
  set A0 := A ⊓ I with hA0
  have hA0card : Nat.card A0 ≤ 2 ^ (2 * f) := by
    let B : Subgroup (projectiveSL 3 F) :=
      A0.comap (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F))
    have hBcard : Nat.card B = Nat.card A0 := by
      refine Nat.card_congr (Equiv.ofBijective
        (fun b : B => (⟨MulAut.conj (b : projectiveSL 3 F), b.2⟩ : A0)) ⟨?_, ?_⟩)
      · intro b b' h
        exact Subtype.ext (conj_injective_projectiveSL (congrArg Subtype.val h))
      · rintro ⟨a, haA, ⟨x, rfl⟩⟩
        exact ⟨⟨x, haA, x, rfl⟩, rfl⟩
    have hB2 : ∀ b ∈ B, b * b = 1 := by
      intro b hb
      have h1 : MulAut.conj (b * b) = (1 : MulAut (projectiveSL 3 F)) := by
        rw [map_mul]
        exact hA2 _ (Subgroup.mem_comap.mp hb).1
      exact conj_injective_projectiveSL (h1.trans (map_one _).symm)
    have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
      intro a ha b hb
      apply conj_injective_projectiveSL
      rw [map_mul, map_mul]
      exact hAc _ (Subgroup.mem_comap.mp ha).1 _ (Subgroup.mem_comap.mp hb).1
    have h1 := card_le_of_elementary_abelian_projectiveSL B hB2 hBc
    rw [hBcard, hF, ← pow_mul, mul_comm] at h1
    exact h1
  have hfinP : Finite (projectiveSL 3 F) := inferInstance
  have hEi : E.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hRE' : E.index ≤ 2 := by
    rw [hR] at hRE
    have h1 : E.relIndex ⊤ ≤ 2 := hRE
    rwa [Subgroup.relIndex_top_right] at h1
  have hAE : (A ⊓ E).relIndex A ≤ 2 := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    calc E.relIndex A ≤ E.relIndex ⊤ := Subgroup.relIndex_le_of_le_right le_top
          (by rw [Subgroup.relIndex_top_right]; exact hEi)
      _ = E.index := Subgroup.relIndex_top_right E
      _ ≤ 2 := hRE'
  have hA0E : A0.relIndex (A ⊓ E) ≤ 2 := by
    have hDn : (D.subgroupOf E).Normal := by
      rw [hR] at hDnorm
      rw [Subgroup.normal_subgroupOf_iff hDE]
      intro h k hh _
      exact ((Subgroup.normal_subgroupOf_iff le_top).mp hDnorm) h k hh (Subgroup.mem_top k)
    let θ : ↥(A ⊓ E) →* ↥E ⧸ D.subgroupOf E :=
      (QuotientGroup.mk' (D.subgroupOf E)).comp (Subgroup.inclusion inf_le_right)
    have hker : θ.ker = A0.subgroupOf (A ⊓ E) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      show (QuotientGroup.mk (Subgroup.inclusion inf_le_right x) : ↥E ⧸ D.subgroupOf E) = 1 ↔ _
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        have : (x : MulAut (projectiveSL 3 F)) ∈ A ⊓ D := ⟨x.2.1, hx⟩
        rwa [hAD] at this
      · intro hx
        have : (x : MulAut (projectiveSL 3 F)) ∈ A ⊓ D := by rwa [hAD]
        exact this.2
    have hcyc : IsCyclic (↥E ⧸ D.subgroupOf E) := by
      obtain ⟨g, hgE, hg⟩ := hEcyc
      refine ⟨⟨(QuotientGroup.mk (⟨g, hgE⟩ : ↥E) : ↥E ⧸ D.subgroupOf E), fun q => ?_⟩⟩
      induction q using QuotientGroup.induction_on with
      | _ x =>
        obtain ⟨k, hk⟩ := hg x x.2
        refine ⟨-k, ?_⟩
        show (QuotientGroup.mk (⟨g, hgE⟩ : ↥E) : ↥E ⧸ D.subgroupOf E) ^ (-k) =
          (QuotientGroup.mk x : ↥E ⧸ D.subgroupOf E)
        rw [← QuotientGroup.mk_zpow]
        apply QuotientGroup.eq.mpr
        rw [Subgroup.mem_subgroupOf]
        simpa [_root_.zpow_neg] using hk
    have hfinq : Finite (↥E ⧸ D.subgroupOf E) := inferInstance
    have hsq : ∀ y : ↥E ⧸ D.subgroupOf E, y ∈ θ.range → y ^ 2 = 1 := by
      rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
        exact hA2 (x : MulAut (projectiveSL 3 F)) x.2.1)
      rw [this, map_one]
    have hcard2 : Nat.card θ.range ≤ 2 := by
      have := Fintype.ofFinite (↥E ⧸ D.subgroupOf E)
      classical
      calc Nat.card θ.range
          ≤ Nat.card {y : ↥E ⧸ D.subgroupOf E // y ^ 2 = 1} :=
            Nat.card_le_card_of_injective (fun y => ⟨y.1, hsq y.1 y.2⟩)
              (fun a b h => Subtype.ext (by
                have := congrArg Subtype.val h
                simpa using this))
        _ ≤ 2 := by
          have h1 := IsCyclic.card_pow_eq_one_le (α := ↥E ⧸ D.subgroupOf E) (n := 2) (by norm_num)
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
          exact h1
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
    exact hcard2
  have hA0AE : A0 ≤ A ⊓ E := inf_le_inf_left _ (hID.trans hDE)
  have hidx : A0.relIndex A ≤ 4 := by
    have := Subgroup.relIndex_mul_relIndex A0 (A ⊓ E) A hA0AE inf_le_left
    rw [← this]
    calc A0.relIndex (A ⊓ E) * (A ⊓ E).relIndex A ≤ 2 * 2 := Nat.mul_le_mul hA0E hAE
      _ = 4 := by norm_num
  have hAcard : Nat.card A = A0.relIndex A * Nat.card A0 := by
    have := Subgroup.relIndex_mul_card (H := A0) (K := A)
    rw [inf_of_le_left inf_le_left] at this
    exact this.symm
  refine ⟨hA0card, hidx, ?_, fun h0 => ?_⟩
  · rw [hAcard, pow_add]
    calc A0.relIndex A * Nat.card A0 ≤ 4 * 2 ^ (2 * f) := Nat.mul_le_mul hidx hA0card
      _ = 2 ^ (2 * f) * 2 ^ 2 := by ring
  · have hcard1 : Nat.card A0 = 1 := by
      rw [h0]
      simp
    rw [hAcard, hcard1, mul_one]
    exact hidx.trans le_rfl

end AutChain

end CFSG.QuasithinUnique.Setup.X7a
