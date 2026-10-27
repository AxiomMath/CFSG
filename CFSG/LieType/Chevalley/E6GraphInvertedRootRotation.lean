module

public import CFSG.LieType.Chevalley.LangRootRankOneTorus
public import CFSG.LieType.Chevalley.ExactNormalFormE

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K]

theorem diagramMap_conj_pinnedX
    (t : TwistTag) {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α) :
    ∃ ε : K, ε * ε = 1 ∧ ∀ c : K, diagramMap t K * pinnedX t.tag K α c * (diagramMap t K)⁻¹ =
      pinnedX t.tag K (permLattice t.perm α) (ε * c) := by
  obtain ⟨w, i, rfl⟩ := isRoot_iff_exists_smul_single.1 hα
  obtain ⟨ε₁, h₁, hX⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w (isRoot_single t.tag i)
  obtain ⟨ε₂, h₂, hY⟩ :=
    exists_canonicalRep_mul_pinnedX_mul_inv K (weylTwist t w) (isRoot_single t.tag (t.perm i))
  refine ⟨ε₂ * ε₁, by linear_combination (ε₂ * ε₂) * h₁ + h₂, fun c => ?_⟩
  have e1 : pinnedX t.tag K (w • Pi.single i 1) c = canonicalRep (coxeterSystem t.tag) K w *
      xUnit t.tag K i (ε₁ * c) * (canonicalRep (coxeterSystem t.tag) K w)⁻¹ := by
    rw [← pinnedX_single, hX, ← mul_assoc, h₁, one_mul]
  have hconj : ∀ g : ModGL t.tag K,
      diagramMap t K * g * (diagramMap t K)⁻¹ = twistHom t K (RingHom.id K) g := fun g => by
    rw [← conj_diagramMap_eq_twistHom]
    rfl
  rw [e1, hconj, map_mul, map_mul, map_inv, twistHom_canonicalRep, twistHom_xUnit,
    RingHom.id_apply, ← pinnedX_single, hY, ← weylTwist_smul_permLattice, permLattice_single,
    mul_assoc]

theorem monomial_conj_pinnedX
    {τ : Tag} {n : ModGL τ K} (hn : n ∈ monomialSubgroup τ K)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ μ : Kˣ, ∀ c : K, n * pinnedX τ K γ c * n⁻¹ =
      pinnedX τ K (weylQuotientHom τ K ⟨n, hn⟩ • γ) (μ * c) := by
  obtain ⟨w, h, hh, rfl⟩ := monomialSubgroup_le_torusWeylCosets hn
  have hπ : weylQuotientHom τ K ⟨h * canonicalRep (coxeterSystem τ) K w, hn⟩ = w :=
    weylQuotientHom_eq (by
      simpa using (mapsRootLines_of_mem_torusGroup hh).mul (mapsRootLines_canonicalRep w))
  rw [hπ]
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  obtain ⟨ε, hε, hX⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hγ
  refine ⟨rootChar a (w • γ) * Units.mkOfMulEqOne ε ε hε, fun c => ?_⟩
  calc rootDiagUnit τ a * canonicalRep (coxeterSystem τ) K w * pinnedX τ K γ c *
        (rootDiagUnit τ a * canonicalRep (coxeterSystem τ) K w)⁻¹ =
      rootDiagUnit τ a * (canonicalRep (coxeterSystem τ) K w * pinnedX τ K γ c *
        (canonicalRep (coxeterSystem τ) K w)⁻¹) * (rootDiagUnit τ a)⁻¹ := by group
    _ = pinnedX τ K (w • γ) ((rootChar a (w • γ) : K) * (ε * c)) := by
        rw [hX, rootDiagUnit_conj_pinnedX a (IsRoot.smul hγ w)]
    _ = _ := by
        rw [Units.val_mul, Units.val_mkOfMulEqOne, mul_assoc]

theorem rootSL2_uSL_eq
    {τ : Tag} (β : Fin τ.rank → ℤ) (z : K) :
    rootSL2 τ K β (uSL z) = pinnedX τ K β ((pinnedData τ β).2.2 • z) := by
  have e : (pinnedData τ β).2.2 • ((pinnedData τ β).2.2 • z) = z := by
    rcases pinnedSign_eq τ β with h | h <;> rw [h] <;> simp
  rw [rootSL2_apply, simpleRootSL2_uSL, pinnedX, e]

theorem exists_rootSL2_vSL_eq
    {τ : Tag} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ ε : K, ε * ε = 1 ∧ ∀ z : K, rootSL2 τ K β (vSL z) = pinnedX τ K (-β) (ε * z) := by
  obtain ⟨ε, hε, h⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K (pinnedWord τ β)
    (isRoot_neg_single τ (pinnedData τ β).1)
  refine ⟨ε, hε, fun z => ?_⟩
  rw [rootSL2_apply, simpleRootSL2_vSL, ← pinnedX_neg_single, pinnedWeyl_eq_list_prod, h,
    smul_neg, wordProd_pinnedWord_smul hβ]

theorem nSL_mul_uSL (c : Kˣ) (z : K) :
    nSL c * uSL z = vSL (-(((c⁻¹ : Kˣ) : K) ^ 2) * z) * nSL c := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [nSL, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp

theorem nSL_mul_vSL (c : Kˣ) (z : K) : nSL c * vSL z = uSL (-((c : K) ^ 2) * z) * nSL c := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [nSL, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp

@[expose] def qSL (c ζ : Kˣ) (h2 : (2 : K) ≠ 0) : SL2 K :=
  ⟨!![1, -((c : K) / (2 * ζ)); (ζ : K) / c, 1 / 2], by
    rw [Matrix.det_fin_two_of]
    field_simp
    ring⟩

theorem nSL_mul_qSL (c ζ : Kˣ) (h2 : (2 : K) ≠ 0) (hζ : (ζ : K) ^ 2 = -1) :
    nSL c * qSL c ζ h2 = qSL c ζ h2 * HSL ζ := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [nSL, qSL, HSL, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals try field_simp
  all_goals first
    | exact hζ
    | exact hζ.symm


theorem E6_graph_inverted_root_SL2_rotation
    (k : Type) [Field k] [IsAlgClosed k]
    (hk : ringChar k ≠ 2) {n : ModGL TwistTag.E6.tag k}
    (hn : n ∈ monomialSubgroup TwistTag.E6.tag k) (hnP : (n * diagramMap TwistTag.E6 k) ^ 2 = 1)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β)
    (hωβ : weylQuotientHom TwistTag.E6.tag k ⟨n, hn⟩ • permLattice TwistTag.E6.perm β = -β) :
    ∃ y ∈ rootRankOneGroup TwistTag.E6.tag k β, ∃ n₁ : ModGL TwistTag.E6.tag k,
      ∃ hn₁ : n₁ ∈ monomialSubgroup TwistTag.E6.tag k,
        y * (n * diagramMap TwistTag.E6 k) * y⁻¹ = n₁ * diagramMap TwistTag.E6 k ∧
        weylQuotientHom TwistTag.E6.tag k ⟨n₁, hn₁⟩ =
          rootReflection β * weylQuotientHom TwistTag.E6.tag k ⟨n, hn⟩ := by
  set P := diagramMap TwistTag.E6 k with hP
  set A := n * P with hAdef
  set w := weylQuotientHom TwistTag.E6.tag k ⟨n, hn⟩ with hw
  set ι := rootSL2 TwistTag.E6.tag k β with hι
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have hinj : Function.Injective ι := fun B B' h =>
    simpleRootSL2_injective hk _ (by simpa [hι, rootSL2_apply] using h)
  have hA : ∀ γ, IsRoot TwistTag.E6.tag γ → ∃ μ : kˣ, ∀ c : k,
      A * pinnedX TwistTag.E6.tag k γ c * A⁻¹ =
        pinnedX TwistTag.E6.tag k (w • permLattice TwistTag.E6.perm γ) (μ * c) := by
    intro γ hγ
    obtain ⟨ε, hε, hPγ⟩ := diagramMap_conj_pinnedX (K := k) TwistTag.E6 hγ
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn (hγ.permLattice TwistTag.E6.cartan_perm)
    refine ⟨μ * Units.mkOfMulEqOne ε ε hε, fun c => ?_⟩
    calc A * pinnedX TwistTag.E6.tag k γ c * A⁻¹ =
          n * (P * pinnedX TwistTag.E6.tag k γ c * P⁻¹) * n⁻¹ := by
          rw [hAdef]
          group
      _ = _ := by
          rw [hPγ, hμ, Units.val_mul, Units.val_mkOfMulEqOne, mul_assoc]
  set s₀ : kˣ := if (pinnedData TwistTag.E6.tag β).2.2 = 1 then 1 else -1 with hs₀
  have hs₀z : ∀ z : k, (pinnedData TwistTag.E6.tag β).2.2 • z = (s₀ : k) * z := by
    intro z
    rcases pinnedSign_eq TwistTag.E6.tag β with h | h <;> simp [hs₀, h]
  have hs₀sq : s₀ * s₀ = 1 := by
    rcases pinnedSign_eq TwistTag.E6.tag β with h | h <;> simp [hs₀, h]
  have hu : ∀ z, ι (uSL z) = pinnedX TwistTag.E6.tag k β ((s₀ : k) * z) := fun z => by
    rw [hι, rootSL2_uSL_eq, hs₀z]
  obtain ⟨ε₁, hε₁, hl⟩ := exists_rootSL2_vSL_eq (K := k) hβ
  set s₁ : kˣ := Units.mkOfMulEqOne ε₁ ε₁ hε₁ with hs₁
  have hs₁sq : s₁ * s₁ = 1 := Units.ext (by simpa [hs₁] using hε₁)
  have hl' : ∀ z, ι (vSL z) = pinnedX TwistTag.E6.tag k (-β) ((s₁ : k) * z) := hl
  have hωneg : w • permLattice TwistTag.E6.perm (-β) = β := by
    rw [permLattice_neg, smul_neg, hωβ, neg_neg]
  obtain ⟨μ₁, hμ₁⟩ := hA β hβ
  obtain ⟨μ₂, hμ₂⟩ := hA (-β) (IsRoot.neg hβ)
  set a : kˣ := s₁ * μ₁ * s₀ with ha
  set b : kˣ := s₀ * μ₂ * s₁ with hb
  have hAu : ∀ z, A * ι (uSL z) * A⁻¹ = ι (vSL ((a : k) * z)) := fun z => by
    rw [hu, hμ₁, hωβ, hl', ha]
    congr 1
    calc (μ₁ : k) * ((s₀ : k) * z) = ((s₁ * s₁ : kˣ) : k) * (μ₁ * (s₀ * z)) := by
          rw [hs₁sq, Units.val_one, one_mul]
      _ = _ := by push_cast; ring
  have hAl : ∀ z, A * ι (vSL z) * A⁻¹ = ι (uSL ((b : k) * z)) := fun z => by
    rw [hl', hμ₂, hωneg, hu, hb]
    congr 1
    calc (μ₂ : k) * ((s₁ : k) * z) = ((s₀ * s₀ : kˣ) : k) * (μ₂ * (s₁ * z)) := by
          rw [hs₀sq, Units.val_one, one_mul]
      _ = _ := by push_cast; ring
  have hAA : A * A = 1 := by rw [← sq]; exact hnP
  have hAinv : A⁻¹ = A := inv_eq_of_mul_eq_one_right hAA
  have hba : b * a = 1 := by
    have h1 : ι (uSL 1) = ι (uSL ((b : k) * (a : k))) := by
      calc ι (uSL 1) = A * (A * ι (uSL 1) * A⁻¹) * A⁻¹ := by
            rw [hAinv]
            calc ι (uSL 1) = (A * A) * ι (uSL 1) * (A * A) := by rw [hAA, one_mul, mul_one]
              _ = _ := by group
        _ = ι (uSL ((b : k) * (a : k))) := by rw [hAu, mul_one, hAl]
    have h2' := congrArg (fun M : SL2 k => (M : Matrix (Fin 2) (Fin 2) k) 0 1) (hinj h1)
    simp only [uSL] at h2'
    exact Units.ext (by
      rw [Units.val_mul, Units.val_one]
      simpa using h2'.symm)
  obtain ⟨c₀, hc₀⟩ := IsAlgClosed.exists_pow_nat_eq (-((a⁻¹ : kˣ) : k)) (n := 2) (by norm_num)
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, neg_eq_zero] at hc₀
    exact (a⁻¹).ne_zero hc₀
  set c : kˣ := Units.mk0 c₀ hc₀0 with hc
  set r := rootWeylSL2 TwistTag.E6.tag k β c with hr
  have hru : ∀ z, r * ι (uSL z) * r⁻¹ = ι (vSL ((a : k) * z)) := fun z => by
    rw [hr, rootWeylSL2, ← map_inv, ← map_mul, ← map_mul, nSL_mul_uSL, mul_inv_cancel_right]
    congr 2
    have e : ((c⁻¹ : kˣ) : k) ^ 2 = ((a : kˣ) : k) * -1 := by
      rw [Units.val_inv_eq_inv_val, inv_pow, hc, Units.val_mk0, hc₀, Units.val_inv_eq_inv_val,
        inv_neg, inv_inv, mul_neg_one]
    rw [e]
    ring
  have hrl : ∀ z, r * ι (vSL z) * r⁻¹ = ι (uSL ((b : k) * z)) := fun z => by
    rw [hr, rootWeylSL2, ← map_inv, ← map_mul, ← map_mul, nSL_mul_vSL, mul_inv_cancel_right]
    congr 2
    have hb' : (b : k) = ((a⁻¹ : kˣ) : k) := by
      rw [eq_inv_of_mul_eq_one_left hba]
    rw [hc, Units.val_mk0, hc₀, hb']
    ring
  set η := r⁻¹ * A with hη
  have hηu : ∀ z, η * ι (uSL z) * η⁻¹ = ι (uSL z) := fun z => by
    have e := hru z
    calc η * ι (uSL z) * η⁻¹ = r⁻¹ * (A * ι (uSL z) * A⁻¹) * r := by rw [hη]; group
      _ = r⁻¹ * (r * ι (uSL z) * r⁻¹) * r := by rw [hAu, e]
      _ = ι (uSL z) := by group
  have hηl : ∀ z, η * ι (vSL z) * η⁻¹ = ι (vSL z) := fun z => by
    have e := hrl z
    calc η * ι (vSL z) * η⁻¹ = r⁻¹ * (A * ι (vSL z) * A⁻¹) * r := by rw [hη]; group
      _ = r⁻¹ * (r * ι (vSL z) * r⁻¹) * r := by rw [hAl, e]
      _ = ι (vSL z) := by group
  have hηall : ∀ B : SL2 k, η * ι B * η⁻¹ = ι B := by
    have heq : (MulAut.conj η).toMonoidHom.comp ι = ι :=
      MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
        rcases hg with ⟨z, rfl⟩ | ⟨z, rfl⟩
        · exact hηu z
        · exact hηl z
    intro B
    exact congrArg (fun f : SL2 k →* ModGL TwistTag.E6.tag k => f B) heq
  obtain ⟨ζ₀, hζ₀⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : k) (n := 2) (by norm_num)
  have hζ₀0 : ζ₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, neg_eq_zero] at hζ₀
    exact one_ne_zero hζ₀
  set ζ : kˣ := Units.mk0 ζ₀ hζ₀0 with hζ
  have hζsq : (ζ : k) ^ 2 = -1 := by rw [hζ, Units.val_mk0, hζ₀]
  set Q := qSL c ζ h2 with hQ
  set y := ι Q⁻¹ with hy
  have hyr : y * r * y⁻¹ = rootTorusSL2 TwistTag.E6.tag k β ζ := by
    have e : Q⁻¹ * nSL c * Q = HSL ζ := by
      rw [mul_assoc, hQ, nSL_mul_qSL c ζ h2 hζsq, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hy, hr, rootWeylSL2, ← map_inv, inv_inv, ← map_mul, ← map_mul, e, rootTorusSL2]
  have hyη : y * η * y⁻¹ = η := by
    have e := hηall Q⁻¹
    rw [← hy] at e
    calc y * η * y⁻¹ = y * (η * y⁻¹ * η⁻¹) * η := by group
      _ = y * (η * y * η⁻¹)⁻¹ * η := by group
      _ = η := by rw [e]; group
  obtain ⟨-, hdH, hrN, -⟩ := exceptional_Lang_root_rank_one_torus_transport TwistTag.E6.tag k hβ
  obtain ⟨hrM, hrπ⟩ := hrN c
  have hdM : rootTorusSL2 TwistTag.E6.tag k β ζ ∈ monomialSubgroup TwistTag.E6.tag k :=
    Subgroup.mem_sup_left (hdH ζ)
  set n₁ := rootTorusSL2 TwistTag.E6.tag k β ζ * r⁻¹ * n with hn₁def
  have hn₁ : n₁ ∈ monomialSubgroup TwistTag.E6.tag k := mul_mem (mul_mem hdM (inv_mem hrM)) hn
  refine ⟨y, ⟨Q⁻¹, rfl⟩, n₁, hn₁, ?_, ?_⟩
  · calc y * (n * P) * y⁻¹ = y * (r * η) * y⁻¹ := by rw [hη, ← hAdef]; group
      _ = (y * r * y⁻¹) * (y * η * y⁻¹) := by group
      _ = rootTorusSL2 TwistTag.E6.tag k β ζ * (r⁻¹ * (n * P)) := by rw [hyr, hyη, hη]
      _ = n₁ * P := by rw [hn₁def]; group
  · have hsplit : (⟨n₁, hn₁⟩ : monomialSubgroup TwistTag.E6.tag k) =
        ⟨_, hdM⟩ * (⟨r, hrM⟩ : monomialSubgroup TwistTag.E6.tag k)⁻¹ * ⟨n, hn⟩ := rfl
    have hdπ : weylQuotientHom TwistTag.E6.tag k ⟨_, hdM⟩ = 1 :=
      weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup (hdH ζ))
    rw [hsplit, map_mul, map_mul, map_inv, hdπ, hrπ, one_mul, rootReflection_inv hβ]

end CFSG.LieType.Chevalley
