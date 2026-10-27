module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCasesScal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsDim
import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryField
import CFSG.CGT.T75P.SylowSplit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt

section ProjAlg

variable {K : Type*} [Field K] {A : Type*} [CommGroup A] [Finite A] {p : ℕ}
variable {V : Type*} [AddCommGroup V] [Module K V] (ρ : Representation K A V)
variable (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hpK : (p : K) ≠ 0)

include hp hA hpK

theorem projI_projI_eq_inter [DecidableEq (Hyperplane A p)] (I J : Finset (Hyperplane A p))
    (v : V) : projI ρ I (projI ρ J v) = projI ρ (I ∩ J) v := by
  have h : ∀ H' ∈ J, projI ρ I (ρ.asAlgebraHom (eps K A p (some H')) v) =
      if H' ∈ I then ρ.asAlgebraHom (eps K A p (some H')) v else 0 := by
    intro H' _
    split_ifs with hH'
    · exact projI_apply_of_mem ρ hp hA hpK hH' ⟨v, rfl⟩
    · refine projI_apply_of_not_mem ρ hp hA hpK (fun H hH h => hH' ?_) ⟨v, rfl⟩
      rw [Option.some.inj h]
      exact hH
  rw [projI_apply ρ J v, map_sum, Finset.sum_congr rfl h, ← Finset.sum_filter,
    Finset.filter_mem_eq_inter, Finset.inter_comm, projI_apply]

theorem projI_projI_of_disjoint [DecidableEq (Hyperplane A p)] {I J : Finset (Hyperplane A p)}
    (h : Disjoint I J) (v : V) : projI ρ I (projI ρ J v) = 0 := by
  rw [projI_projI_eq_inter ρ hp hA hpK, Finset.disjoint_iff_inter_eq_empty.mp h, projI_apply,
    Finset.sum_empty]

theorem range_projI_le_ker_projI [DecidableEq (Hyperplane A p)] {I J : Finset (Hyperplane A p)}
    (h : Disjoint I J) : LinearMap.range (projI ρ J) ≤ LinearMap.ker (projI ρ I) := by
  rintro _ ⟨v, rfl⟩
  exact projI_projI_of_disjoint ρ hp hA hpK h v

theorem sum_finrank_le_finrank_ker_projI [FiniteDimensional K V] [DecidableEq (Hyperplane A p)]
    {I J : Finset (Hyperplane A p)} (h : Disjoint I J) :
    ∑ H ∈ J, Module.finrank K (weightSpace ρ H.1) ≤
      Module.finrank K (LinearMap.ker (projI ρ I)) := by
  rw [← finrank_range_projI ρ hp hA hpK J]
  exact Submodule.finrank_mono (range_projI_le_ker_projI ρ hp hA hpK h)

theorem sum_finrank_le_finrank [FiniteDimensional K V] (J : Finset (Hyperplane A p)) :
    ∑ H ∈ J, Module.finrank K (weightSpace ρ H.1) ≤ Module.finrank K V := by
  rw [← finrank_range_projI ρ hp hA hpK J]
  exact Submodule.finrank_le _

theorem finrank_eq_fixedSpace_add_sum_support [FiniteDimensional K V]
    (T : Finset (Hyperplane A p)) (hT : ∀ H : Hyperplane A p, H ∈ T ↔ weightSpace ρ H.1 ≠ ⊥) :
    Module.finrank K V = Module.finrank K (fixedSpace ρ ⊤) +
      ∑ H ∈ T, Module.finrank K (weightSpace ρ H.1) := by
  classical
  haveI : Fintype (Hyperplane A p) := Fintype.ofFinite _
  rw [finrank_eq_fixedSpace_add_sum ρ hp hA hpK]
  congr 1
  refine (Finset.sum_subset (Finset.subset_univ T) fun H _ hH => ?_).symm
  have hbot : weightSpace ρ H.1 = ⊥ := by
    by_contra h
    exact hH ((hT H).mpr h)
  rw [hbot, finrank_bot]

end ProjAlg

section Orth

variable {K : Type*} [Field K] {A : Type*} [CommGroup A] [Finite A] {p : ℕ}
variable {V : Type*} [AddCommGroup V] [Module K V] {σ : K →+* K}
variable (β : V →ₗ[K] V →ₛₗ[σ] K) (ρ : Representation K A V) (hρ : IsIsomRep β ρ)
variable (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hpK : (p : K) ≠ 0)

include hρ in
theorem orth_ker_range_projI (I : Finset (Hyperplane A p)) :
    ∀ u ∈ LinearMap.ker (projI ρ I), ∀ w ∈ LinearMap.range (projI ρ I), β u w = 0 ∧ β w u = 0 := by
  rintro u hu _ ⟨v, rfl⟩
  rw [LinearMap.mem_ker] at hu
  refine ⟨?_, ?_⟩
  · rw [← projI_left ρ β hρ I u v, hu, map_zero, LinearMap.zero_apply]
  · rw [projI_left ρ β hρ I v u, hu, map_zero]

include hρ hp hA hpK in
theorem nondeg_ker_projI (hβ : β.SeparatingLeft) (I : Finset (Hyperplane A p)) :
    ∀ u ∈ LinearMap.ker (projI ρ I), (∀ u' ∈ LinearMap.ker (projI ρ I), β u u' = 0) → u = 0 := by
  intro u hu h
  refine hβ u fun v => ?_
  have hv : v = (v - projI ρ I v) + projI ρ I v := by abel
  have h1 : v - projI ρ I v ∈ LinearMap.ker (projI ρ I) := by
    rw [LinearMap.mem_ker, map_sub, projI_projI ρ hp hA hpK, sub_self]
  rw [hv, map_add, h _ h1, (orth_ker_range_projI β ρ hρ I u hu _ ⟨v, rfl⟩).1, add_zero]

end Orth

section Engine

open scoped IsMulCommutative

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {τ : K →+* K}
variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
variable {H : Subgroup (GL ι K)} {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K}

theorem det_matrix_eq_det_glEquiv (g : GL ι K) :
    (g : Matrix ι ι K).det = (LinearEquiv.det (glEquiv g) : K) := by
  rw [LinearEquiv.coe_det, ← LinearMap.det_toLin']
  congr 1

theorem scalarGL_injective [Nonempty ι] :
    Function.Injective (Matrix.GeneralLinearGroup.scalar ι : Kˣ →* GL ι K) := by
  intro c d h
  have h1 := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) h
  simp only [Matrix.GeneralLinearGroup.coe_scalar] at h1
  exact Units.ext (Matrix.scalar_inj.mp h1)

theorem pow_eq_one_of_scalarGL [Nonempty ι] {c : Kˣ} {n : ℕ}
    (h : Matrix.GeneralLinearGroup.scalar ι c ^ n = 1) : c ^ n = 1 := by
  apply scalarGL_injective (ι := ι)
  rw [map_pow, h, map_one]

theorem scalar_mem_isomGL_of_mul (c : Kˣ) (hc : (c : K) * τ c = 1) :
    Matrix.GeneralLinearGroup.scalar ι c ∈ isomGL β := by
  rw [mem_isomGL]
  intro x y
  rw [← glEquiv_apply, ← glEquiv_apply, glEquiv_scalar_apply, glEquiv_scalar_apply]
  simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc]
  rw [mul_comm (τ _), hc, one_mul]

theorem semiMap_smul_of_pow_eq_one (hp : p.Prime) {A : GL ι K} {σ : K ≃+* K} (hσ : orderOf σ = p)
    {c : K} (hc : c ^ p = 1) (v : ι → K) :
    ModelGen.semiMap A σ (c • v) = c • ModelGen.semiMap A σ v := by
  rw [ModelGen.semiMap_smul, CFSG.StandardType.TableBUF.ringEquiv_apply_eq_of_pow_eq_one hp
    (by rw [← hσ]; exact pow_orderOf_eq_one σ) hc]

theorem exists_engine_lu (hp : p.Prime) [hSn : S.Normal] (hB : IsElemAbelian p B)
    (hrank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hZ : Subgroup.center ↥S = ⊥) (h4 : p ^ 4 ≤ Nat.card B) [Finite K] (h2 : (2 : K) ≠ 0)
    (hpK : (p : K) ≠ 0) (Dat : ClsInner p S B H β) (hHβ : H ≤ isomGL β)
    (hdetH : ∀ g ∈ isomGL β, (g : Matrix ι ι K).det = 1 → g ∈ H)
    (hG6 : ∀ g ∈ isomGL β, g ^ p = 1 → ∃ c : Kˣ, c ^ p = 1 ∧
      Matrix.GeneralLinearGroup.scalar ι c ∈ isomGL β ∧
      Matrix.GeneralLinearGroup.scalar ι c * g ∈ H) :
    ∃ Aε : Subgroup (GL ι K), IsElemAbelian p Aε ∧ liftGroup Dat ≤ Aε ∧ Aε ≤ isomGL β ∧
      Aε ≤ centGL (fieldSet Dat) ∧
      (∀ A' : Subgroup (GL ι K), Aε ≤ A' → IsElemAbelian p A' → A' ≤ isomGL β →
        A' ≤ centGL (fieldSet Dat) → A' ≤ Aε) ∧
      Aε ⊓ H = liftGroup Dat ∧
      (∀ c : Kˣ, c ^ p = 1 → Matrix.GeneralLinearGroup.scalar ι c ∈ isomGL β →
        Matrix.GeneralLinearGroup.scalar ι c ∈ Aε) ∧
      ∀ g ∈ Aε, ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ Aε ∧
        Matrix.GeneralLinearGroup.scalar ι c * g ∈ liftGroup Dat := by
  classical
  obtain ⟨Aε, hle, hAε, hAεβ, hAε𝒮, hmax⟩ := exists_maximal_engine Dat hHβ
  haveI : IsMulCommutative ↥Aε := hAε.1
  have hA : ∀ a : ↥Aε, a ^ p = 1 := fun a => Subtype.ext (by simpa using hAε.2 a a.2)
  have hρ : IsIsomRep β (glRep Aε) := isIsomRep_glRep hAεβ
  have hmaxE : IsMaxElem β (glRep Aε) p (fieldSet Dat) :=
    isMaxElem_of_maximal β (fieldSet Dat) Aε hAε hAεβ hAε𝒮 hmax
  have hinvβ : ∀ I : Finset (Hyperplane ↥Aε p),
      glEquiv.symm (invol (glRep Aε) hp hA hpK I) ∈ isomGL β := by
    intro I
    rw [mem_isomGL]
    intro x y
    rw [← glEquiv_apply, ← glEquiv_apply, MulEquiv.apply_symm_apply]
    exact invol_isometry (glRep Aε) hp hA hpK β hρ I x y
  have hmem : ∀ {Ha Hb : Hyperplane ↥Aε p}, Ha ≠ Hb →
      Even (Module.finrank K (weightSpace (glRep Aε) Ha.1) +
        Module.finrank K (weightSpace (glRep Aε) Hb.1)) →
      glEquiv.symm (invol (glRep Aε) hp hA hpK {Ha, Hb}) ∈ H := by
    intro Ha Hb hab he
    refine hdetH _ (hinvβ _) ?_
    rw [det_matrix_eq_det_glEquiv, MulEquiv.apply_symm_apply, LinearEquiv.coe_det,
      det_invol_pair (glRep Aε) hp hA hpK hab, he.neg_one_pow]
  have hmem' : ∀ {Ha Hb : Hyperplane ↥Aε p}, Ha ≠ Hb →
      Even (Module.finrank K (weightSpace (glRep Aε) Ha.1) +
        Module.finrank K (weightSpace (glRep Aε) Hb.1)) →
      glEquiv.symm (invol (glRep Aε) hp hA hpK {Hb, Ha}) ∈ H := by
    intro Ha Hb hab he
    rw [Finset.pair_comm]
    exact hmem hab he
  have hInv : ∀ H₁ H₂ H₃ : Hyperplane ↥Aε p, H₁ ≠ H₂ → H₁ ≠ H₃ → H₂ ≠ H₃ →
      weightSpace (glRep Aε) H₁.1 ≠ ⊥ → weightSpace (glRep Aε) H₂.1 ≠ ⊥ →
      weightSpace (glRep Aε) H₃.1 ≠ ⊥ →
      glEquiv.symm (invol (glRep Aε) hp hA hpK {H₁, H₂}) ∈ H ∨
        glEquiv.symm (invol (glRep Aε) hp hA hpK {H₁, H₃}) ∈ H ∨
        glEquiv.symm (invol (glRep Aε) hp hA hpK {H₂, H₃}) ∈ H := by
    intro H₁ H₂ H₃ h12 h13 h23 _ _ _
    have hcard : ({H₁, H₂, H₃} : Finset (Hyperplane ↥Aε p)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]
    obtain ⟨Ha, hHa, Hb, hHb, hab, he⟩ :=
      exists_pair_even_finrank (glRep Aε) {H₁, H₂, H₃} hcard.ge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hHa hHb
    rcases hHa with rfl | rfl | rfl <;> rcases hHb with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hab
      | exact Or.inl (hmem hab he)
      | exact Or.inr (Or.inl (hmem hab he))
      | exact Or.inr (Or.inr (hmem hab he))
      | exact Or.inl (hmem' hab he)
      | exact Or.inr (Or.inl (hmem' hab he))
      | exact Or.inr (Or.inr (hmem' hab he))
  have hcap := inf_eq_liftGroup hp hB hrank hBC hcore hZ h4 h2 hpK Dat hHβ hle hAε hAεβ hAε𝒮
    hmax hA hInv
  have hscalMax : ∀ c : Kˣ, c ^ p = 1 → Matrix.GeneralLinearGroup.scalar ι c ∈ isomGL β →
      Matrix.GeneralLinearGroup.scalar ι c ∈ Aε := by
    intro c hcp hcβ
    have hcp' : (c : K) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hcp, Units.val_one]
    obtain ⟨a, ha⟩ := hmaxE (glEquiv (Matrix.GeneralLinearGroup.scalar ι c))
      (fun x y => by
        have := (mem_isomGL.mp hcβ) x y
        rwa [← glEquiv_apply, ← glEquiv_apply] at this)
      (fun a v => by rw [glEquiv_scalar_apply, glEquiv_scalar_apply, map_smul])
      (by
        rintro s ⟨hF, rfl⟩ v
        simp only [LinearMap.toAddMonoidHom_coe, glEquiv_scalar_apply]
        exact (semiMap_smul_of_pow_eq_one hp hF.2.2.2.2.1.1 hcp' v).symm)
      (fun v => by
        rw [← map_pow, ← map_pow, hcp, map_one, map_one]
        rfl)
    have hae : (a : GL ι K) = Matrix.GeneralLinearGroup.scalar ι c := by
      apply glEquiv.injective
      refine LinearEquiv.ext fun v => ?_
      rw [← glRep_apply_eq_glEquiv]
      exact ha v
    rw [← hae]
    exact a.2
  refine ⟨Aε, hAε, hle, hAεβ, hAε𝒮, hmax, hcap, hscalMax, fun g hg => ?_⟩
  obtain ⟨c, hcp, hcβ, hcH⟩ := hG6 g (hAεβ hg) (hAε.2 g hg)
  have hcA := hscalMax c hcp hcβ
  refine ⟨c, hcA, ?_⟩
  rw [← hcap]
  exact ⟨Aε.mul_mem hcA hg, hcH⟩

theorem card_engine_eq [Nonempty ι] [Finite K] (hp : p.Prime) {Aε L : Subgroup (GL ι K)}
    (hAε : IsElemAbelian p Aε) (hle : L ≤ Aε) (hAεβ : Aε ≤ isomGL β)
    (hLscal : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ L → c = 1)
    (hscalMax : ∀ c : Kˣ, c ^ p = 1 → Matrix.GeneralLinearGroup.scalar ι c ∈ isomGL β →
      Matrix.GeneralLinearGroup.scalar ι c ∈ Aε)
    (hdec : ∀ g ∈ Aε, ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ Aε ∧
      Matrix.GeneralLinearGroup.scalar ι c * g ∈ L) :
    ((¬ ∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧ Matrix.GeneralLinearGroup.scalar ι c ∈ isomGL β) →
      Aε = L) ∧
    ((∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧ Matrix.GeneralLinearGroup.scalar ι c ∈ isomGL β) →
      Nat.card Aε = p * Nat.card L) := by
  have hpow : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ Aε → c ^ p = 1 := fun c hc =>
    pow_eq_one_of_scalarGL (hAε.2 _ hc)
  refine ⟨fun hns => le_antisymm (fun g hg => ?_) hle, fun ⟨c₀, hc₀1, hc₀p, hc₀β⟩ => ?_⟩
  · obtain ⟨c, hcA, hcL⟩ := hdec g hg
    have hc1 : c = 1 := by
      by_contra hc1
      exact hns ⟨c, hc1, hpow c hcA, hAεβ hcA⟩
    rw [hc1, map_one, one_mul] at hcL
    exact hcL
  · set A₀ : Subgroup (GL ι K) := Aε ⊓ StatedScalars ι K with hA₀
    have hA₀scal : ∀ g ∈ A₀, ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c = g := by
      rintro g ⟨-, c, hc⟩
      exact ⟨c, hc⟩
    have hsup : Aε = L ⊔ A₀ := by
      apply le_antisymm
      · intro g hg
        obtain ⟨c, hcA, hcL⟩ := hdec g hg
        have h1 : g = (Matrix.GeneralLinearGroup.scalar ι c)⁻¹ *
            (Matrix.GeneralLinearGroup.scalar ι c * g) := by group
        rw [h1, sup_comm]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (A₀.inv_mem ⟨hcA, c, rfl⟩))
          (Subgroup.mem_sup_right hcL)
      · exact sup_le hle inf_le_left
    have hinf : L ⊓ A₀ = ⊥ := by
      rw [eq_bot_iff]
      rintro g ⟨hgL, hgA₀⟩
      obtain ⟨c, rfl⟩ := hA₀scal g hgA₀
      rw [Subgroup.mem_bot, hLscal c hgL, map_one]
    have hcomm : ∀ g ∈ L, ∀ g₀ ∈ A₀, g * g₀ = g₀ * g := by
      intro g _ g₀ hg₀
      obtain ⟨c, rfl⟩ := hA₀scal g₀ hg₀
      exact (scalarGL_mul_comm c g).symm
    have hcardA₀ : Nat.card A₀ = p := by
      apply le_antisymm
      · have hle₀ : A₀ ≤ (rootsOfUnity p K).map (Matrix.GeneralLinearGroup.scalar ι) := by
          intro g hg
          obtain ⟨c, rfl⟩ := hA₀scal g hg
          exact ⟨c, (mem_rootsOfUnity p c).mpr (hpow c hg.1), rfl⟩
        calc Nat.card A₀ ≤ Nat.card ((rootsOfUnity p K).map
              (Matrix.GeneralLinearGroup.scalar ι)) := Subgroup.card_le_of_le hle₀
          _ = Nat.card (rootsOfUnity p K) :=
            Subgroup.card_map_of_injective scalarGL_injective
          _ ≤ p := by
            haveI : NeZero p := ⟨hp.ne_zero⟩
            exact card_rootsOfUnity K p
      · have hz : Subgroup.zpowers (Matrix.GeneralLinearGroup.scalar ι c₀) ≤ A₀ :=
          Subgroup.zpowers_le.mpr ⟨hscalMax c₀ hc₀p hc₀β, c₀, rfl⟩
        have hord : orderOf (Matrix.GeneralLinearGroup.scalar ι c₀) = p := by
          haveI : Fact p.Prime := ⟨hp⟩
          refine orderOf_eq_prime (by rw [← map_pow, hc₀p, map_one]) fun h => hc₀1 ?_
          apply scalarGL_injective (ι := ι)
          rw [h, map_one]
        calc p = Nat.card (Subgroup.zpowers (Matrix.GeneralLinearGroup.scalar ι c₀)) := by
              rw [Nat.card_zpowers, hord]
          _ ≤ Nat.card A₀ := Subgroup.card_le_of_le hz
    rw [hsup, CFSG.CGT.T75P.card_sup_of_commute hcomm hinf, hcardA₀, mul_comm]

theorem exists_scalar_of_smul_on [Finite K] (hp : p.Prime) (hβ : β = 0 ∨ β.SeparatingLeft)
    {Aε : Subgroup (GL ι K)} [IsMulCommutative Aε] (hA : ∀ a : ↥Aε, a ^ p = 1)
    (hpK : (p : K) ≠ 0) (hAεβ : Aε ≤ isomGL β)
    (hscalMax : ∀ c : Kˣ, c ^ p = 1 → Matrix.GeneralLinearGroup.scalar ι c ∈ isomGL β →
      Matrix.GeneralLinearGroup.scalar ι c ∈ Aε)
    (I : Finset (Hyperplane ↥Aε p)) (hU0 : wtU Aε I ≠ ⊥) :
    ∀ y ∈ Aε, ∀ c : K, (∀ u ∈ wtU Aε I, glEquiv y u = c • u) →
      ∃ c' : Kˣ, (c' : K) = c ∧ Matrix.GeneralLinearGroup.scalar ι c' ∈ Aε := by
  intro y hy c hc
  obtain ⟨u₀, hu₀, hu₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 : glEquiv y u₀ = 0 := by rw [hc u₀ hu₀, zero_smul]
    exact hu₀0 ((LinearEquiv.map_eq_zero_iff _).mp h1)
  have hpow : ∀ n : ℕ, ∀ u ∈ wtU Aε I, glEquiv (y ^ n) u = c ^ n • u := by
    intro n
    induction n with
    | zero => intro u _; simp
    | succ n ih =>
      intro u hu
      rw [pow_succ, map_mul, LinearEquiv.mul_apply, hc u hu, map_smul, ih u hu, smul_smul,
        pow_succ']
  have hcp : c ^ p = 1 := by
    have h1 := hpow p u₀ hu₀
    have hyp : y ^ p = 1 := congrArg Subtype.val (hA ⟨y, hy⟩)
    rw [hyp, map_one] at h1
    have h1' : (c ^ p - 1) • u₀ = 0 := by
      rw [sub_smul, ← h1, one_smul]
      exact sub_self _
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1').resolve_right hu₀0)
  set c' : Kˣ := Units.mk0 c hc0 with hc'
  have hc'p : c' ^ p = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hcp,
    Units.val_one])
  refine ⟨c', rfl, hscalMax c' hc'p ?_⟩
  rcases hβ with rfl | hβ
  · rw [isomGL_zero]
    exact Subgroup.mem_top _
  ·
    apply scalar_mem_isomGL_of_mul
    have hρ : IsIsomRep β (glRep Aε) := isIsomRep_glRep hAεβ
    obtain ⟨u', hu', hβu⟩ : ∃ u' ∈ wtU Aε I, β u₀ u' ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu₀0 (nondeg_ker_projI β (glRep Aε) hρ hp hA hpK hβ I u₀ hu₀ hcon)
    have h1 := (mem_isomGL.mp (hAεβ hy)) u₀ u'
    rw [← glEquiv_apply, ← glEquiv_apply, hc u₀ hu₀, hc u' hu'] at h1
    simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc] at h1
    have h1' : (c * τ c - 1) * β u₀ u' = 0 := by
      rw [sub_mul, one_mul, mul_comm c (τ c), h1, sub_self]
    have := sub_eq_zero.mp ((mul_eq_zero.mp h1').resolve_right hβu)
    simpa [hc'] using this

theorem two_le_finrank_weightSpace_of_not_scalar [Finite K] (hp : p.Prime)
    (hβ : β = 0 ∨ β.SeparatingLeft)
    {Aε : Subgroup (GL ι K)} [IsMulCommutative Aε] (hA : ∀ a : ↥Aε, a ^ p = 1)
    (hpK : (p : K) ≠ 0) (hAεβ : Aε ≤ isomGL β)
    (hns : ¬ ∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧ Matrix.GeneralLinearGroup.scalar ι c ∈ isomGL β)
    {H' : Hyperplane ↥Aε p} (hH' : weightSpace (glRep Aε) H'.1 ≠ ⊥) :
    2 ≤ Module.finrank K (weightSpace (glRep Aε) H'.1) := by
  have hpos : 0 < Module.finrank K (weightSpace (glRep Aε) H'.1) :=
    Nat.pos_of_ne_zero fun h => hH' (Submodule.finrank_eq_zero.mp h)
  by_contra hlt
  have h1 : Module.finrank K (weightSpace (glRep Aε) H'.1) = 1 := by omega
  obtain ⟨x, hx⟩ := exists_not_mem_hyperplane hp H'
  obtain ⟨c, hcp, hc1, hcx⟩ := exists_smul_of_finrank_eq_one (glRep Aε) hp hA hpK h1 hx
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hcp
    exact zero_ne_one hcp
  apply hns
  refine ⟨Units.mk0 c hc0, fun h => hc1 (by simpa using congrArg Units.val h),
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hcp, Units.val_one]), ?_⟩
  rcases hβ with rfl | hβ
  · rw [isomGL_zero]
    exact Subgroup.mem_top _
  · exact scalar_mem_isomGL_of_mul _ (mul_map_eq_one_of_finrank_eq_one β (glRep Aε) hp hA hpK
      (isIsomRep_glRep hAεβ) hβ hH' hcx)

theorem card_eq_lu [Finite K] (hp : p.Prime) [hSn : S.Normal] (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (Dat : ClsInner p S B H β) :
    (innerPart S B = B ∧ Nat.card B = p * Nat.card ↥(liftGroup Dat)) ∨
      (FieldElt p S B Dat.φ β Dat.θ Dat.b Dat.A Dat.σ ∧
        Nat.card B = p * Nat.card ↥(liftGroup Dat) * p) := by
  have hBC' : Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) = p := by
    rw [← ModelGen.inf_centMod_eq_inf_centralizer hSn hcore]
    exact hBC
  have hθcard := ModelGen.card_range_mul_card_inf Dat.θ Dat.θ_eq_one
  have hcardL : Nat.card ↥(liftGroup Dat) = Nat.card Dat.θ.range :=
    Subgroup.card_map_of_injective H.subtype_injective
  rcases Dat.split with hBB | hF
  · left
    refine ⟨hBB, ?_⟩
    have h1 : innerPart S B ⊓ Subgroup.centralizer (S : Set Ω) =
        B ⊓ Subgroup.centralizer (S : Set Ω) := by
      rw [inf_assoc, inf_eq_right.mpr (le_sup_right : Subgroup.centralizer (S : Set Ω) ≤
        S ⊔ Subgroup.centralizer (S : Set Ω))]
    rw [h1, hBC'] at hθcard
    have hB1 : Nat.card ↥(innerPart S B) = Nat.card B := by rw [hBB]
    rw [← hB1, ← hθcard, hcardL, mul_comm]
  · right
    refine ⟨hF, ?_⟩
    obtain ⟨hbB, hbN, hBb, hbout, -, -, -⟩ := hF
    have h := card_eq_of_inner_split hB hBC' hbB hBb hbout hθcard
    have hb1 : Dat.b ≠ 1 := fun h1 => hbN (h1 ▸ Subgroup.one_mem _)
    haveI : Fact p.Prime := ⟨hp⟩
    have hord : orderOf Dat.b = p := orderOf_eq_prime (hB.2 _ hbB) hb1
    rw [h, Nat.card_zpowers, hord, hcardL]

end Engine

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
