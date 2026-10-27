module

public import CFSG.LieType.SeitzGeneration.OuterLinearField
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnPlane
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364
public import CFSG.LieType.SeitzGeneration.HyperIrrGroup
public import CFSG.LieType.SeitzGeneration.OuterSUField

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2

open Matrix CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartOne CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
open CFSG.RankThree.PartOne.CTP (slSub mem_slSub)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

section Restrict

variable {G H : Type*} [Group G] [Group H]

noncomputable def resFun (j : H →* G) (b : MulAut G) (hb : ∀ h : H, ∃ h' : H, b (j h) = j h')
    (h : H) : H :=
  Classical.choose (hb h)

theorem map_resFun (j : H →* G) (b : MulAut G) (hb : ∀ h : H, ∃ h' : H, b (j h) = j h')
    (h : H) : j (resFun j b hb h) = b (j h) :=
  (Classical.choose_spec (hb h)).symm

noncomputable def resAutFun (j : H →* G) (hj : Function.Injective j) (B : Subgroup (MulAut G))
    (hB : ∀ b ∈ B, ∀ h : H, ∃ h' : H, b (j h) = j h') (b : B) : MulAut H where
  toFun := resFun j b (hB b b.2)
  invFun := resFun j (b⁻¹ : B) (hB _ (b⁻¹ : B).2)
  left_inv h := hj (by
    rw [map_resFun, map_resFun, Subgroup.coe_inv, MulAut.inv_apply_self])
  right_inv h := hj (by
    rw [map_resFun, map_resFun, Subgroup.coe_inv, MulAut.apply_inv_self])
  map_mul' h₁ h₂ := hj (by simp only [map_mul, map_resFun])

theorem map_resAutFun (j : H →* G) (hj : Function.Injective j) (B : Subgroup (MulAut G))
    (hB : ∀ b ∈ B, ∀ h : H, ∃ h' : H, b (j h) = j h') (b : B) (h : H) :
    j (resAutFun j hj B hB b h) = (b : MulAut G) (j h) :=
  map_resFun j b (hB b b.2) h

noncomputable def resAut (j : H →* G) (hj : Function.Injective j) (B : Subgroup (MulAut G))
    (hB : ∀ b ∈ B, ∀ h : H, ∃ h' : H, b (j h) = j h') : B →* MulAut H :=
  MonoidHom.mk' (resAutFun j hj B hB) fun b₁ b₂ => MulEquiv.ext fun h => hj (by
    simp only [MulAut.mul_apply, map_resAutFun, Subgroup.coe_mul])

theorem map_resAut (j : H →* G) (hj : Function.Injective j) (B : Subgroup (MulAut G))
    (hB : ∀ b ∈ B, ∀ h : H, ∃ h' : H, b (j h) = j h') (b : B) (h : H) :
    j (resAut j hj B hB b h) = (b : MulAut G) (j h) :=
  map_resAutFun j hj B hB b h

end Restrict

section Hyper

variable {X : Type*} [Group X]

theorem relIndex_closure_pair_of_indep [Finite X] {p : ℕ} (hp : p.Prime) {E : Subgroup X}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3) {a b : X} (ha : a ∈ E) (hb : b ∈ E)
    (ha1 : a ≠ 1) (hba : b ∉ Subgroup.zpowers a) :
    Nat.card (Subgroup.closure ({a, b} : Set X)) = p ^ 2 ∧
      (Subgroup.closure ({a, b} : Set X)).relIndex E = p := by
  have : Fact p.Prime := ⟨hp⟩
  set P := Subgroup.closure ({a, b} : Set X) with hPdef
  have hPE : P ≤ E := closure_pair_le ha hb
  have hle : Subgroup.zpowers a ≤ P := Subgroup.zpowers_le.2 (mem_closure_pair_left a b)
  have hne : Subgroup.zpowers a ≠ P := fun h => hba (h ▸ mem_closure_pair_right a b)
  have hz : Nat.card (Subgroup.zpowers a) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hE.2 a ha) ha1]
  have hab : Commute a b := congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h2 : Nat.card P ≤ p ^ 2 := card_closure_pair_le hp.pos hab (hE.2 a ha) (hE.2 b hb)
  have h3 : p < Nat.card P := by
    have hd : p ∣ Nat.card P := hz ▸ Subgroup.card_dvd_of_le hle
    have hne' : Nat.card P ≠ p := fun h => hne (Subgroup.eq_of_le_of_card_ge hle (by rw [h, hz]))
    exact lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hd) (Ne.symm hne')
  obtain ⟨i, hi3, hPi⟩ := (Nat.dvd_prime_pow hp).1 (hc ▸ Subgroup.card_dvd_of_le hPE)
  have hcP : Nat.card P = p ^ 2 := by
    rw [hPi] at h2 h3 ⊢
    have h23 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    interval_cases i
    · rw [pow_zero] at h3
      exact absurd h3 (by have := hp.two_le; omega)
    · rw [pow_one] at h3
      exact absurd h3 (lt_irrefl p)
    · rfl
    · omega
  refine ⟨hcP, ?_⟩
  have h := Subgroup.relIndex_mul_card P E
  rw [inf_eq_left.2 hPE, hcP, hc] at h
  have h' : p ^ 2 * P.relIndex E = p ^ 2 * p := by
    rw [← pow_succ, mul_comm]
    exact h
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) h'

theorem card_inf_eq_sq_of_decomp [Finite X] {p : ℕ} (hp : p.Prime) {E D : Subgroup X}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3) {φ : X} (hφE : φ ∈ E) (hφD : φ ∉ D)
    (hdec : ∀ x ∈ E, ∃ j : ℤ, x * (φ ^ j)⁻¹ ∈ D) : Nat.card (E ⊓ D : Subgroup X) = p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set B : Subgroup X := E ⊓ D with hB
  have hφ1 : φ ≠ 1 := fun h => hφD (h ▸ one_mem _)
  have hord : orderOf φ = p := orderOf_eq_prime (hE.2 _ hφE) hφ1
  let ψ : B × Subgroup.zpowers φ → E := fun bz =>
    ⟨(bz.1 : X) * bz.2, E.mul_mem bz.1.2.1 (Subgroup.zpowers_le.2 hφE bz.2.2)⟩
  have hsurj : Function.Surjective ψ := by
    rintro ⟨x₀, hx₀⟩
    obtain ⟨j, hj⟩ := hdec x₀ hx₀
    refine ⟨(⟨x₀ * (φ ^ j)⁻¹, E.mul_mem hx₀ (E.inv_mem (E.zpow_mem hφE j)), hj⟩,
      ⟨φ ^ j, Subgroup.zpow_mem_zpowers _ j⟩), ?_⟩
    apply Subtype.ext
    show x₀ * (φ ^ j)⁻¹ * φ ^ j = x₀
    group
  have h1 := Nat.card_le_card_of_surjective ψ hsurj
  rw [Nat.card_prod, Nat.card_zpowers, hord, hc] at h1
  have hBE : B ≤ E := inf_le_left
  obtain ⟨i, hi3, hBi⟩ := (Nat.dvd_prime_pow hp).1 (hc ▸ Subgroup.card_dvd_of_le hBE)
  have hBne : Nat.card B ≠ p ^ 3 := by
    intro h3
    have hBeq : B = E := Subgroup.eq_of_le_of_card_ge hBE (by rw [hc, h3])
    exact hφD (hBeq ▸ hφE : φ ∈ B).2
  rw [hBi] at h1 hBne ⊢
  have hp1 := hp.one_lt
  have h12 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp1 (by norm_num)
  interval_cases i
  · rw [pow_zero] at h1
    nlinarith
  · rw [pow_one] at h1
    nlinarith
  · rfl
  · exact absurd rfl hBne

theorem seitzHyperGamma_map_congr_le {p : ℕ} (e : MulAut X) (E : Subgroup (MulAut X)) :
    seitzHyperGamma p (E.map (MulAut.congr e).toMonoidHom) ≤
      (seitzHyperGamma p E).map e.toMonoidHom := by
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  refine iSup₂_le fun F' hF' => ?_
  obtain ⟨hF'E, hF'p⟩ := hF'
  set F := F'.comap (MulAut.congr e).toMonoidHom with hF
  have hFE : F ≤ E := by
    intro a ha
    obtain ⟨a', ha', hfa⟩ := hF'E ha
    rw [← hinj hfa]
    exact ha'
  have hmap : F.map (MulAut.congr e).toMonoidHom = F' := by
    rw [hF, Subgroup.map_comap_eq, inf_of_le_right (hF'E.trans (Subgroup.map_le_range _ E))]
  have hFp : F.relIndex E = p := by
    rw [← Subgroup.relIndex_map_map_of_injective F E hinj, hmap]
    exact hF'p
  intro y hy
  refine ⟨e⁻¹ y, ?_, by simp⟩
  refine (le_iSup₂_of_le F ⟨hFE, hFp⟩ le_rfl : fixedPoints F ≤ seitzHyperGamma p E) ?_
  rw [mem_fixedPoints]
  intro a ha
  have h1 := (mem_fixedPoints.1 hy) ((MulAut.congr e).toMonoidHom a)
    (hmap ▸ Subgroup.mem_map_of_mem _ ha)
  have h2 : e (a (e⁻¹ y)) = y := by simpa [MulAut.congr_apply] using h1
  have h3 := congrArg (e⁻¹ : MulAut X) h2
  rwa [MulAut.inv_apply_self] at h3

theorem mem_seitzHyperGamma_of_map_congr {p : ℕ} {e : MulAut X} {E : Subgroup (MulAut X)}
    {y : X} (hy : y ∈ seitzHyperGamma p (E.map (MulAut.congr e).toMonoidHom)) :
    e⁻¹ y ∈ seitzHyperGamma p E := by
  obtain ⟨z, hz, rfl⟩ := seitzHyperGamma_map_congr_le e E hy
  show e⁻¹ (e z) ∈ seitzHyperGamma p E
  rw [MulAut.inv_apply_self]
  exact hz

end Hyper

section Plane

theorem planeGen_projectiveSL_kfact (hS : KFactSeitzRankTwo) {m : ℕ} (hm : 2 ≤ m)
    {k : Type} [Field k] [Finite k] {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 0 < e)
    (hkc : Nat.card k = ℓ ^ e) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hdup : ¬ (ℓ ^ e = 2 ∧ (m = 2 ∨ m = 3)))
    (hexc : ¬ (p = 3 ∧ ℓ = 2 ∧ e = 2 ∧ m = 2))
    {E : Subgroup (MulAut (projectiveSL (m + 1) k))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) : PlaneGen E := by
  have hv : (TauCeti.LieTypeIndex.A m ⟨ℓ, e, hℓ, he⟩).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨⟨by omega, fun h => by omega⟩, ?_⟩
    simp only [TauCeti.PrimePower.card_def]
    rintro (⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h⟩)
    · omega
    · exact hdup ⟨h, Or.inl (by omega)⟩
    · exact hdup ⟨h, Or.inr (by omega)⟩
  set d₀ : TauCeti.ValidLieTypeIndex := ⟨.A m ⟨ℓ, e, hℓ, he⟩, hv⟩ with hd₀
  let ε := catEquivProjectiveSL hℓ he hkc hv
  have hpd : p ≠ d₀.1.characteristic := by simpa [hd₀] using hpℓ
  have hex : ¬ IsD2SeitzException p d₀.1 := by
    rintro (⟨hp3, ⟨q, hq1, hq2, hd⟩ | ⟨q, hq1, hq2, hd⟩ | ⟨q, hq1, hq2, hd⟩ |
        ⟨q, hq1, hq2, hd | hd⟩ | hd⟩ | ⟨h5, hd | hd⟩)
    · have := (TauCeti.LieTypeIndex.A.inj hd).1
      omega
    · obtain ⟨hm2, hq⟩ := TauCeti.LieTypeIndex.A.inj hd
      have h1 : ℓ = 2 := by
        have := congrArg TauCeti.PrimePower.p hq
        simpa [hq1] using this
      have h2 : e = 2 := by
        have := congrArg TauCeti.PrimePower.exponent hq
        simpa [hq2] using this
      exact hexc ⟨hp3, h1, h2, by omega⟩
    all_goals cases hd
  have h := hS d₀ p hp hp2 hpd hex (E.map (MulAut.congr ε.symm).toMonoidHom)
    (isElemAbelian_map_congr ε.symm hE) (by rw [card_map_congr]; exact hc)
  exact planeGen_of_outer_model ε.symm h

end Plane

section Subfield

variable {n : ℕ} {K : Type} [Field K]

theorem exists_map_eq_smul_of_commute [Finite K] (hn : 3 ≤ n) {σ : K ≃+* K} {z : GL (Fin n) K}
    (hcomm : fieldAut n K σ * conjAut n K z = conjAut n K z * fieldAut n K σ) :
    ∃ u : Kˣ, (z : Matrix (Fin n) (Fin n) K).map σ = (u : K) • (z : Matrix (Fin n) (Fin n) K) := by
  have hσz : conjAut n K (GeneralLinearGroup.map (σ : K →+* K) z) = conjAut n K z := by
    rw [← (standard_automorphism_transport (K := K) (n := n)).2.2.1 σ z, hcomm,
      mul_inv_cancel_right]
  obtain ⟨u, hu⟩ : ∃ u : Kˣ, GeneralLinearGroup.scalar (Fin n) u =
      GeneralLinearGroup.map (σ : K →+* K) z * z⁻¹ :=
    (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn _).mp
      (by rw [map_mul, map_inv, hσz, mul_inv_cancel])
  refine ⟨u, ?_⟩
  have h1 : GeneralLinearGroup.map (σ : K →+* K) z = GeneralLinearGroup.scalar (Fin n) u * z := by
    rw [hu, inv_mul_cancel_right]
  have h2 := congrArg (fun B : GL (Fin n) K => (B : Matrix (Fin n) (Fin n) K)) h1
  simp only [Units.val_mul, scalarGL_coe_eq_smul] at h2
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  simpa [GeneralLinearGroup.map_apply, Matrix.smul_apply] using h3

theorem slConjugation_mem_of_semi {k : Subfield K} {σ : K ≃+* K} (hk : ∀ x, x ∈ k ↔ σ x = x)
    {z : GL (Fin n) K} {u : K} (hu : u ≠ 0)
    (hz : (z : Matrix (Fin n) (Fin n) K).map σ = u • (z : Matrix (Fin n) (Fin n) K))
    {g : SpecialLinearGroup (Fin n) K} (hg : ∀ i j, (g : Matrix (Fin n) (Fin n) K) i j ∈ k) :
    ∀ i j, ((slConjugation n K z g : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) i j ∈ k := by
  have hZZi : (z : Matrix (Fin n) (Fin n) K) * ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hZiZ : ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (z : Matrix (Fin n) (Fin n) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hgσ : (g : Matrix (Fin n) (Fin n) K).map σ = g := by
    ext i j
    exact (hk _).1 (hg i j)
  have hZiσ : ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ =
      u⁻¹ • ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have h1 : (z : Matrix (Fin n) (Fin n) K).map σ *
        ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ = 1 := by
      rw [← Matrix.map_mul, hZZi]
      exact Matrix.map_one σ (map_zero σ) (map_one σ)
    rw [hz, Matrix.smul_mul] at h1
    calc ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ
        = u⁻¹ • (((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (u • ((z : Matrix (Fin n) (Fin n) K) *
            ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ))) := by
          rw [Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hu, one_smul, ← Matrix.mul_assoc, hZiZ,
            Matrix.one_mul]
      _ = u⁻¹ • ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [h1, Matrix.mul_one]
  have hmap : ((slConjugation n K z g : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K).map σ = slConjugation n K z g := by
    rw [coe_slConjugation, Matrix.map_mul, Matrix.map_mul, hz, hgσ, hZiσ, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hu, one_smul]
  intro i j
  exact (hk _).2 (congrFun (congrFun hmap i) j)

variable [Finite K]

theorem exists_zpow_mul_mem_linearAutGroup {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hn : 3 ≤ n) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2) {σ : K ≃+* K}
    (hσ : orderOf σ = p) {E : Subgroup (MulAut (projectiveSL n K))} (hE : IsElemAbelian p E)
    {x₀ : MulAut (projectiveSL n K)} (hx₀ : x₀ ∈ E) :
    ∃ j : ℤ, x₀ * ((fieldAut n K σ) ^ j)⁻¹ ∈ linearAutGroup n K := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hx₀S : x₀ ∈ semilinearAutGroup n K :=
    CFSG.RankThree.PartOne.KCLinCommOdd.mem_semilinearAutGroup_of_pow_eq_one hn hp2 hp (j := 1)
      (by simpa using hE.2 x₀ hx₀)
  obtain ⟨A, τ, hx₀A⟩ := mem_semilinearAutGroup_iff.mp hx₀S
  have hτp : τ ^ p = 1 := by
    have h1 : x₀ ^ p = 1 := hE.2 x₀ hx₀
    rw [hx₀A, CFSG.RankThree.LinearDescent.conjAut_mul_fieldAut_pow] at h1
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ h1).1
  obtain ⟨F₀, -, -, htop, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hℓ hf hK
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨F₀, htop⟩
  have hfinAut : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hτ : τ ∈ Subgroup.zpowers σ := mem_zpowers_of_pow_eq_one_of_isCyclic hp hσ hτp
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hτ
  refine ⟨j, ?_⟩
  have h3 : x₀ * ((fieldAut n K σ) ^ j)⁻¹ = conjAut n K A := by
    rw [hx₀A, ← hj, map_zpow]
    group
  rw [h3]
  exact conjAut_mem_linearAutGroup A

theorem card_inf_linearAutGroup {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hn : 3 ≤ n)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2) {σ : K ≃+* K} (hσ : orderOf σ = p)
    (hσout : fieldAut n K σ ∉ linearAutGroup n K) {E : Subgroup (MulAut (projectiveSL n K))}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3) (hσE : fieldAut n K σ ∈ E) :
    Nat.card (E ⊓ linearAutGroup n K : Subgroup (MulAut (projectiveSL n K))) = p ^ 2 := by
  have : Finite (MulAut (projectiveSL n K)) := MulEquiv.finite_left
  exact card_inf_eq_sq_of_decomp hp hE hc hσE hσout
    (fun x₀ hx₀ => exists_zpow_mul_mem_linearAutGroup hℓ hf hn hK hp hp2 hσ hE hx₀)

theorem range_le_seitzHyperGamma (hS : KFactSeitzRankTwo) {m : ℕ} (hm : 2 ≤ m) {ℓ f p : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) (hpq : p ∣ Nat.card K - 1) {σ : K ≃+* K} (hσ : orderOf σ = p)
    (hσout : ∀ B : GL (Fin (m + 1)) K, fieldAut (m + 1) K σ ≠ conjAut (m + 1) K B)
    (hexc : ¬ (p = 3 ∧ m = 2 ∧ Nat.card (semilinearFixedSubfield σ) = 4))
    {E : Subgroup (MulAut (projectiveSL (m + 1) K))} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3) (hσE : fieldAut (m + 1) K σ ∈ E) :
    (linearSubfieldInclusion (m + 1) (semilinearFixedSubfield σ)).range ≤ seitzHyperGamma p E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hn : 3 ≤ m + 1 := by omega
  have : Finite (MulAut (projectiveSL (m + 1) K)) := MulEquiv.finite_left
  set k : Subfield K := semilinearFixedSubfield σ with hkdef
  have hk : ∀ y, y ∈ k ↔ σ y = y := fun y => Iff.rfl
  set j := linearSubfieldInclusion (m + 1) k with hjdef
  have hj : Function.Injective j := linearSubfieldInclusion_injective (by omega) k
  set D := linearAutGroup (m + 1) K with hDdef
  have hσD : fieldAut (m + 1) K σ ∉ D := by
    intro h
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 h
    exact hσout A hA.symm
  set B : Subgroup (MulAut (projectiveSL (m + 1) K)) := E ⊓ D with hBdef
  have hBc : Nat.card B = p ^ 2 :=
    card_inf_linearAutGroup hℓ hf hn hK hp hp2 hσ hσD hE hcard hσE
  have hBa : IsElemAbelian p B := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hE.2 x hx.1⟩
    have h := congrArg Subtype.val (hE.1.is_comm.comm (⟨a, a.2.1⟩ : E) ⟨b, b.2.1⟩)
    exact h
  obtain ⟨hpf, hkc⟩ : p ∣ f ∧ Nat.card k = ℓ ^ (f / p) := card_semilinearFixedSubfield hℓ hf hK hσ
  have he : 0 < f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hKk : Nat.card K = Nat.card k ^ p := by
    rw [hK, hkc, ← pow_mul, Nat.div_mul_cancel hpf]
  have hk1 : 1 < Nat.card k := Finite.one_lt_card
  have hpk : p ∣ Nat.card k - 1 := by
    have h1 : ((Nat.card K : ℕ) : ZMod p) = 1 := by
      have hK1 : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
      have := (ZMod.natCast_eq_zero_iff _ p).2 hpq
      rw [Nat.cast_sub hK1, Nat.cast_one, sub_eq_zero] at this
      exact this
    rw [hKk, Nat.cast_pow, ZMod.pow_card] at h1
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hk1.le, Nat.cast_one, h1, sub_self]
  have hk4 : 4 ≤ Nat.card k := by
    have h1 : p ≤ Nat.card k - 1 := Nat.le_of_dvd (by omega) hpk
    have := hp.two_le
    have hp3 : 3 ≤ p := by omega
    omega
  have hBcomm : ∀ b ∈ B, fieldAut (m + 1) K σ * b = b * fieldAut (m + 1) K σ := fun b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hσE⟩ ⟨b, hb.1⟩)
  have hBL : ∀ b ∈ B, ∀ h : projectiveSL (m + 1) k, ∃ h' : projectiveSL (m + 1) k,
      b (j h) = j h' := by
    intro b hb h
    obtain ⟨z, rfl⟩ := mem_linearAutGroup_iff.1 hb.2
    obtain ⟨u, hu⟩ := exists_map_eq_smul_of_commute hn (hBcomm _ hb)
    obtain ⟨g, rfl⟩ := proj_surjective (m + 1) k h
    have hg : ∀ i i', ((SpecialLinearGroup.map k.subtype g : SpecialLinearGroup (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) i i' ∈ k := fun i i' =>
      ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i i').2
    have hmem : conjAut (m + 1) K z (j (proj (m + 1) k g)) ∈ j.range := by
      rw [hjdef, linearSubfieldInclusion_proj, conjAut_proj]
      exact mem_range_linearSubfieldInclusion.2
        ⟨_, slConjugation_mem_of_semi hk u.ne_zero hu hg, rfl⟩
    obtain ⟨h', hh'⟩ := hmem
    exact ⟨h', hh'.symm⟩
  have hσL : ∀ h : projectiveSL (m + 1) k, fieldAut (m + 1) K σ (j h) = j h := fun h =>
    fieldAut_linearSubfieldInclusion (fun c hc => (hk c).1 hc) h
  have hhyp : ∀ b ∈ B, b ≠ 1 → fixedPoints (Subgroup.closure
      ({b, fieldAut (m + 1) K σ} : Set (MulAut (projectiveSL (m + 1) K)))) ≤
        seitzHyperGamma p E := by
    intro b hb hb1
    have hσb : fieldAut (m + 1) K σ ∉ Subgroup.zpowers b := fun h =>
      hσD ((Subgroup.zpowers_le.2 hb.2) h)
    exact CFSG.RankThree.PartTwo.Sec4.Res6L364.fixedPoints_le_seitzHyperGamma
      (closure_pair_le hb.1 hσE)
      (relIndex_closure_pair_of_indep hp hE hcard hb.1 hσE hb1 hσb).2
  have hfixL : ∀ b ∈ B, b ≠ 1 → ∀ h : projectiveSL (m + 1) k, b (j h) = j h →
      j h ∈ seitzHyperGamma p E := by
    intro b hb hb1 h hbh
    refine hhyp b hb hb1 (CFSG.RankThree.PartTwo.Sec4.Res6L364.mem_fixedPoints_closure ?_)
    rintro φ (rfl | rfl)
    · exact hbh
    · exact hσL h
  by_cases htriv : ∃ b ∈ B, b ≠ 1 ∧ ∀ h : projectiveSL (m + 1) k, b (j h) = j h
  · obtain ⟨b, hb, hb1, hbh⟩ := htriv
    rintro _ ⟨h, rfl⟩
    exact hfixL b hb hb1 h (hbh h)
  · push Not at htriv
    set ρ := resAut j hj B hBL with hρ
    have hρinj : Function.Injective ρ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro b hb
      rw [MonoidHom.mem_ker] at hb
      rw [Subgroup.mem_bot]
      by_contra hb1
      obtain ⟨h, hh⟩ := htriv b b.2 (fun h => hb1 (Subtype.ext h))
      apply hh
      have h1 := map_resAut j hj B hBL b h
      rw [← hρ, hb] at h1
      exact h1.symm
    set E₁ : Subgroup (MulAut (projectiveSL (m + 1) k)) := ρ.range with hE₁
    have hE₁a : IsElemAbelian p E₁ := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
      · obtain ⟨_, ⟨a', rfl⟩⟩ := a
        obtain ⟨_, ⟨b', rfl⟩⟩ := b
        apply Subtype.ext
        show ρ a' * ρ b' = ρ b' * ρ a'
        rw [← map_mul, ← map_mul]
        congr 1
        exact hBa.1.is_comm.comm a' b'
      · rintro _ ⟨b', rfl⟩
        rw [← map_pow]
        have : b' ^ p = 1 := Subtype.ext (hBa.2 _ b'.2)
        rw [this, map_one]
    have hE₁c : Nat.card E₁ = p ^ 2 := by
      rw [hE₁, ← hBc]
      exact Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv.symm
    have hdup : ¬ (ℓ ^ (f / p) = 2 ∧ (m = 2 ∨ m = 3)) := by
      rintro ⟨h2, -⟩
      rw [← hkc] at h2
      omega
    have hexc' : ¬ (p = 3 ∧ ℓ = 2 ∧ f / p = 2 ∧ m = 2) := by
      rintro ⟨hp3, hℓ2, he2, hm2⟩
      apply hexc
      refine ⟨hp3, hm2, ?_⟩
      rw [hkc, hℓ2, he2]
      norm_num
    have hpl : PlaneGen E₁ :=
      planeGen_projectiveSL_kfact hS hm hℓ he hkc hp hp2 hpℓ hdup hexc' hE₁a hE₁c
    have hL : j.range = (planeClosure E₁).map j := by
      rw [show planeClosure E₁ = ⊤ from hpl, ← MonoidHom.range_eq_map]
    rw [hL, planeClosure, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨h, ⟨e₁, he₁, he₁1, he₁h⟩, rfl⟩
    obtain ⟨b, rfl⟩ := he₁
    have hb1 : (b : MulAut (projectiveSL (m + 1) K)) ≠ 1 := by
      intro h1
      apply he₁1
      have : b = 1 := Subtype.ext h1
      rw [this, map_one]
    refine hfixL b b.2 hb1 h ?_
    rw [← map_resAut j hj B hBL b h]
    exact congrArg j he₁h

end Subfield

section Main

variable {K : Type} [Field K] [Finite K]

theorem seitzHyperGamma_eq_top_sixtyFour (hK : Nat.card K = 64)
    {E : Subgroup (MulAut (projectiveSL 3 K))} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 3) : seitzHyperGamma 3 E = ⊤ := by
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (GaloisField 2 6) := Fintype.ofFinite (GaloisField 2 6)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 6) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 6 (by norm_num)]
    norm_num
  let e : K ≃+* GaloisField 2 6 := FiniteField.ringEquivOfCardEq hcard
  let φ : projectiveSL 3 K ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 6) :=
    (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr e).trans
      (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 6)).symm
  exact CFSG.RankThree.PartTwo.Sec4.seitzL3SixtyFour_holds (projectiveSL 3 K) ⟨φ⟩ E hE
    (by rw [hc]; norm_num)

theorem seitzHyperGamma_eq_top_of_not_le_linearAut
    (hS : KFactSeitzRankTwo) {m : ℕ} (hm : 2 ≤ m) {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hpq : p ∣ Nat.card K - 1) {E : Subgroup (MulAut (projectiveSL (m + 1) K))}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3)
    (hout : ¬ E ≤ linearAutGroup (m + 1) K) : seitzHyperGamma p E = ⊤ := by
  classical
  by_cases h64 : p = 3 ∧ m = 2 ∧ Nat.card K = 64
  · obtain ⟨rfl, rfl, hK64⟩ := h64
    exact seitzHyperGamma_eq_top_sixtyFour hK64 hE hc
  have hn : 3 ≤ m + 1 := by omega
  have hn0 : 0 < m + 1 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (MulAut (projectiveSL (m + 1) K)) := MulEquiv.finite_left
  obtain ⟨a0, ha0E, ha0D⟩ : ∃ a0 ∈ E, a0 ∉ linearAutGroup (m + 1) K := by
    by_contra hcon
    push Not at hcon
    exact hout hcon
  have ha01 : a0 ≠ 1 := fun h => ha0D (h ▸ one_mem _)
  have hord : orderOf a0 = p := orderOf_eq_prime (hE.2 a0 ha0E) ha01
  obtain ⟨b0, hb0E, hb0⟩ : ∃ b0 ∈ E, b0 ∉ Subgroup.zpowers a0 := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Subgroup.zpowers a0 := hcon
    have hfin : Finite (Subgroup.zpowers a0) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord]; exact hp.ne_zero)
    have h1 := Subgroup.card_le_of_le hle
    rw [hc, Nat.card_zpowers, hord] at h1
    have h2 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    rw [pow_one] at h2
    omega
  set P := Subgroup.closure ({a0, b0} : Set (MulAut (projectiveSL (m + 1) K))) with hPdef
  have hPE : P ≤ E := closure_pair_le ha0E hb0E
  have hPa : IsElemAbelian p P := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hE.2 x (hPE hx)⟩
    have h := congrArg Subtype.val (hE.1.is_comm.comm (⟨a, hPE a.2⟩ : E) ⟨b, hPE b.2⟩)
    exact h
  have hPc : Nat.card P = p ^ 2 :=
    (relIndex_closure_pair_of_indep hp hE hc ha0E hb0E ha01 hb0).1
  have hPout : ¬ P ≤ linearAutGroup (m + 1) K := fun h => ha0D (h (mem_closure_pair_left _ _))
  obtain ⟨h, σ, x, c, hσ, hKk, hσout, hσE, hxE, hxσ, hxns, hxp, hcσ⟩ :=
    exists_field_normal_form hℓ hf hn hK hp hp2 hpℓ hPa hPc hPout
  set E' := E.map (MulAut.congr h⁻¹).toMonoidHom with hE'def
  have hσE' : fieldAut (m + 1) K σ ∈ E' := Subgroup.map_mono hPE hσE
  have hxE' : conjAut (m + 1) K x ∈ E' := Subgroup.map_mono hPE hxE
  have hE'a : IsElemAbelian p E' := isElemAbelian_map_congr h⁻¹ hE
  have hE'c : Nat.card E' = p ^ 3 := (card_map_congr h⁻¹ E).trans hc
  set k : Subfield K := semilinearFixedSubfield σ with hkdef
  have hk : ∀ y, y ∈ k ↔ σ y = y := fun y => Iff.rfl
  have hc0 : c ≠ 0 :=
    ne_zero_of_gl_coe_eq_smul hn0 (G := x ^ p) (a := c) (by
      rw [Units.val_pow_eq_pow_val]
      exact hxp)
  obtain ⟨μ, hμ⟩ := CFSG.ABGLocalTools.exists_prod_pow_eq σ (c := c⁻¹) (by rw [map_inv₀, hcσ])
  rw [hσ] at hμ
  have hμ0 : μ ≠ 0 := by
    intro h0
    have h1 : ∏ i ∈ Finset.range p, (σ ^ i) μ = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr hp.pos) (by simp [h0])
    rw [hμ] at h1
    exact inv_ne_zero hc0 h1
  obtain ⟨M₀, hdet, hM₀⟩ := exists_fixed_matrix_smul hp hℓ hf hK σ hσ hxσ hxp
    (by rw [hμ]; exact inv_mul_cancel₀ hc0)
  let M : GL (Fin (m + 1)) K := Matrix.nonsingInvUnit M₀ hdet
  let G : GL (Fin (m + 1)) K := GeneralLinearGroup.scalar (Fin (m + 1)) (Units.mk0 μ hμ0) * x
  have hGcoe : (G : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      μ • (x : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
    rw [Units.val_mul, scalarGL_coe_eq_smul, Matrix.smul_mul, Matrix.one_mul]
    rfl
  have hGE : conjAut (m + 1) K G ∈ E' := by
    rw [map_mul, conjAut_scalar, one_mul]
    exact hxE'
  have hGns : ∀ a : K, (G : Matrix (Fin (m + 1)) (Fin (m + 1)) K) ≠ a • 1 := by
    intro a ha
    apply hxns (μ⁻¹ * a)
    rw [hGcoe] at ha
    have h1 := congrArg (fun Z => μ⁻¹ • Z) ha
    simpa [smul_smul, hμ0] using h1
  have hGM : (G : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      (M : Matrix (Fin (m + 1)) (Fin (m + 1)) K).map σ = M := by
    rw [hGcoe]
    exact hM₀
  have hGM' : G * GeneralLinearGroup.map (σ : K →+* K) M = M := Units.ext (by simpa using hGM)
  set E'' := E'.map (MulAut.congr (conjAut (m + 1) K M)⁻¹).toMonoidHom with hE''def
  have hσE'' : fieldAut (m + 1) K σ ∈ E'' := by
    refine ⟨conjAut (m + 1) K G * fieldAut (m + 1) K σ, E'.mul_mem hGE hσE', ?_⟩
    have htr := (standard_automorphism_transport (K := K) (n := m + 1)).2.2.1 σ M
    have hfc : fieldAut (m + 1) K σ * conjAut (m + 1) K M =
        conjAut (m + 1) K (GeneralLinearGroup.map (σ : K →+* K) M) * fieldAut (m + 1) K σ := by
      rw [← htr]
      group
    show (conjAut (m + 1) K M)⁻¹ * (conjAut (m + 1) K G * fieldAut (m + 1) K σ) *
      (conjAut (m + 1) K M)⁻¹⁻¹ = fieldAut (m + 1) K σ
    calc (conjAut (m + 1) K M)⁻¹ * (conjAut (m + 1) K G * fieldAut (m + 1) K σ) *
          (conjAut (m + 1) K M)⁻¹⁻¹
        = (conjAut (m + 1) K M)⁻¹ * conjAut (m + 1) K G *
            (fieldAut (m + 1) K σ * conjAut (m + 1) K M) := by group
      _ = (conjAut (m + 1) K M)⁻¹ * conjAut (m + 1) K G *
            (conjAut (m + 1) K (GeneralLinearGroup.map (σ : K →+* K) M) *
              fieldAut (m + 1) K σ) := by rw [hfc]
      _ = conjAut (m + 1) K (M⁻¹ * (G * GeneralLinearGroup.map (σ : K →+* K) M)) *
            fieldAut (m + 1) K σ := by
          simp only [map_mul, map_inv]
          group
      _ = fieldAut (m + 1) K σ := by rw [hGM', inv_mul_cancel, map_one, one_mul]
  have hE''a : IsElemAbelian p E'' := isElemAbelian_map_congr _ hE'a
  have hE''c : Nat.card E'' = p ^ 3 := (card_map_congr _ E').trans hE'c
  have hexc : ¬ (p = 3 ∧ m = 2 ∧ Nat.card k = 4) := by
    rintro ⟨hp3, hm2, hk4⟩
    apply h64
    refine ⟨hp3, hm2, ?_⟩
    rw [hKk, hk4, hp3]
    norm_num
  have h1 := range_le_seitzHyperGamma hS hm hℓ hf hK hp hp2 hpℓ hpq hσ hσout hexc hE'a hE'c hσE'
  have h2 := range_le_seitzHyperGamma hS hm hℓ hf hK hp hp2 hpℓ hpq hσ hσout hexc hE''a hE''c
    hσE''
  have hsub : ∀ g ∈ slSub (m + 1) k, proj (m + 1) K g ∈ seitzHyperGamma p E' := fun g hg =>
    h1 (mem_range_linearSubfieldInclusion.2 ⟨g, mem_slSub.1 hg, rfl⟩)
  have hsubM : ∀ g ∈ slSub (m + 1) k,
      proj (m + 1) K (slConjugation (m + 1) K M g) ∈ seitzHyperGamma p E' := by
    intro g hg
    have h3 : proj (m + 1) K g ∈ seitzHyperGamma p E'' :=
      h2 (mem_range_linearSubfieldInclusion.2 ⟨g, mem_slSub.1 hg, rfl⟩)
    have h4 := mem_seitzHyperGamma_of_map_congr h3
    rw [inv_inv, conjAut_proj] at h4
    exact h4
  have hpair := pairSL_closure hp hp2 hKk hn M (slConjugation_map_ne_of_unit σ hk G hGns M hGM)
  have hE'top : seitzHyperGamma p E' = ⊤ := by
    have hle : Subgroup.closure ((slSub (m + 1) k : Set (SpecialLinearGroup (Fin (m + 1)) K)) ∪
        ((slSub (m + 1) k).map (slConjugation (m + 1) K M).toMonoidHom :
          Set (SpecialLinearGroup (Fin (m + 1)) K))) ≤
        (seitzHyperGamma p E').comap (proj (m + 1) K) := by
      rw [Subgroup.closure_le]
      rintro y (hy | ⟨g, hg, rfl⟩)
      · exact hsub y hy
      · exact hsubM g hg
    rw [hpair, top_le_iff] at hle
    rw [eq_top_iff]
    intro y _
    obtain ⟨g, rfl⟩ := proj_surjective (m + 1) K y
    have hg : g ∈ (seitzHyperGamma p E').comap (proj (m + 1) K) := hle ▸ Subgroup.mem_top g
    exact hg
  exact CFSG.RankThree.PartTwo.Sec4.Res6L364.seitzHyperGamma_eq_top_of_map h⁻¹
    (MulAut.congr h⁻¹).toMonoidHom (fun a y => by simp [MulAut.congr_apply])
    (MulAut.congr h⁻¹).injective hE'top

end Main

section Unitary

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.CTP CFSG.RankThree.Classical
  CFSG.LieType.Chevalley

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem exists_zpow_mul_mem_primeFormD (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime) {σ : K ≃+* K} (hσ : orderOf σ = p)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} (hE : IsElemAbelian p E)
    {x₀ : MulAut (primeFormP h (idGram K n))} (hx₀ : x₀ ∈ E) :
    ∃ j : ℤ, x₀ * ((primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) ^ j)⁻¹ ∈
      primeFormD h (idGram K n) := by
  have hfin : Finite K := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hισ : primeFormFieldFactor h hC hn hne (primeFormFieldHom h hC σ) = σ := by
    have := primeFormFieldFactor_apply h hC hn hne 1 σ
    rwa [map_one, one_mul] at this
  have hτp : (primeFormFieldFactor h hC hn hne x₀) ^ p = 1 := by
    rw [← map_pow, hE.2 x₀ hx₀, map_one]
  have hcyc : IsCyclic (K ≃+* K) :=
    isCyclic_ringEquiv_of_card h.prime (by have := h.one_le; omega) h.card
  have hfinAut : Finite (K ≃+* K) := Finite.of_injective _ DFunLike.coe_injective
  have hτ : primeFormFieldFactor h hC hn hne x₀ ∈ Subgroup.zpowers σ :=
    OuterSUField.mem_zpowers_of_pow_eq_one hp hσ hτp
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hτ
  refine ⟨j, ?_⟩
  rw [← ker_primeFormFieldFactor h hC hn hne, MonoidHom.mem_ker, map_mul, map_inv, map_zpow,
    hισ, hj, mul_inv_cancel]

theorem exists_glAut_eq_mul_scalar (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) {σ : K ≃+* K}
    {z : primeFormUnitary h (idGram K n)}
    (hcomm : primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ * primeFormConjHom h _ z =
      primeFormConjHom h _ z * primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) :
    ∃ c : Kˣ, glAut σ (z : GL (Fin n) K) =
      (z : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) c := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have h1 := primeFormField_conj_eq h hC σ z
  rw [hcomm, mul_inv_cancel_right] at h1
  have h2 : primeFormPsi h hC ⟨z⁻¹ * primeFormFieldU h hC σ z, RingEquiv.refl K⟩ = 1 := by
    rw [primeFormPsi_apply, show primeFormFieldHom h hC (RingEquiv.refl K) = 1 from map_one _,
      mul_one, map_mul, map_inv, ← h1, inv_mul_cancel]
  obtain ⟨-, c, -, hc⟩ := (primeFormPsi_eq_one_iff h hC hn _).1 h2
  refine ⟨c, ?_⟩
  have hc' : (z : GL (Fin n) K)⁻¹ * glAut σ (z : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) c := hc
  rw [← hc']
  group

theorem glAut_conj_eq_of_semi (σ : K ≃+* K) {z g : GL (Fin n) K} {c : Kˣ}
    (hz : glAut σ z = z * GeneralLinearGroup.scalar (Fin n) c) (hg : glAut σ g = g) :
    glAut σ (z * g * z⁻¹) = z * g * z⁻¹ := by
  have hsg : GeneralLinearGroup.scalar (Fin n) c * g = g * GeneralLinearGroup.scalar (Fin n) c :=
    (commute_scalarGL c g).eq
  rw [map_mul, map_mul, map_inv, hz, hg]
  calc z * GeneralLinearGroup.scalar (Fin n) c * g * (z * GeneralLinearGroup.scalar (Fin n) c)⁻¹
      = z * (GeneralLinearGroup.scalar (Fin n) c * g) * (GeneralLinearGroup.scalar (Fin n) c)⁻¹ *
          z⁻¹ := by group
    _ = z * (g * GeneralLinearGroup.scalar (Fin n) c) * (GeneralLinearGroup.scalar (Fin n) c)⁻¹ *
          z⁻¹ := by rw [hsg]
    _ = z * g * z⁻¹ := by group

theorem conjHom_subfieldPSU_mem (h : UnitaryFieldData ℓ f K) {σ : K ≃+* K} {e : ℕ}
    (h₀ : UnitaryFieldData ℓ e (fixSubfield σ))
    (hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c) {z : primeFormUnitary h (idGram K n)}
    {c : Kˣ}
    (hz : glAut σ (z : GL (Fin n) K) = (z : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) c)
    (x : primeFormP h₀ (idGram (fixSubfield σ) n)) :
    ∃ x' : primeFormP h₀ (idGram (fixSubfield σ) n),
      primeFormConjHom h _ z (subfieldPSU h h₀ hbar n x) = subfieldPSU h h₀ hbar n x' := by
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective _ x
  have hgσ : glAut σ ((subfieldSU h h₀ hbar n g₀ : gramSU h _) : GL (Fin n) K) =
      ((subfieldSU h h₀ hbar n g₀ : gramSU h _) : GL (Fin n) K) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact (((g₀ : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)) i j).2
  have hfix := glAut_conj_eq_of_semi σ hz hgσ
  obtain ⟨g₁, hg₁⟩ := exists_subfieldGL_eq_of_fixed (n := n) hfix
  have hmem : subfieldGL (fixSubfield σ) n g₁ ∈ gramSU h ((1 : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) := by
    rw [hg₁]
    exact conj_mem_gramSU h _ z.2 (subfieldSU h h₀ hbar n g₀).2
  have hg₁SU := mem_gramSU_of_subfieldGL h n h₀ hbar hmem
  refine ⟨QuotientGroup.mk' _ ⟨g₁, hg₁SU⟩, ?_⟩
  change primeFormConjHom h _ z ((subfieldSU h h₀ hbar n g₀ : gramSU h _) : primeFormP h _) =
    ((subfieldSU h h₀ hbar n ⟨g₁, hg₁SU⟩ : gramSU h _) : primeFormP h _)
  rw [primeFormConjHom_mk]
  congr 1
  exact Subtype.ext hg₁.symm

theorem planeGen_primeFormP_kfact (hS : KFactSeitzRankTwo) {m e : ℕ} {k : Type} [Field k]
    (h₀ : UnitaryFieldData ℓ e k) (hm : 2 ≤ m) (hq : ℓ ^ e ≠ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) {E : Subgroup (MulAut (primeFormP h₀ (idGram k (m + 1))))}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2) : PlaneGen E := by
  have hfin : Finite k := h₀.finite
  have hℓ := h₀.prime
  have he : 0 < e := h₀.one_le
  have h2le : 2 ≤ ℓ ^ e := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ e := Nat.pow_le_pow_right hℓ.pos he
  have hv : (TauCeti.LieTypeIndex.twistedA m ⟨ℓ, e, hℓ, he⟩).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨⟨hm, fun _ => ?_⟩, not_false⟩
    rw [TauCeti.PrimePower.card_def]
    show 3 ≤ ℓ ^ e
    omega
  obtain ⟨-, K', _, _, hK', ⟨e₁⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m ⟨ℓ, e, hℓ, he⟩ hv (MulEquiv.refl _)
  have : Fintype k := Fintype.ofFinite k
  have : Fintype K' := Fintype.ofFinite K'
  have hcard : Fintype.card k = Fintype.card K' := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h₀.card, hK', ← pow_mul,
      mul_comm]
  let eK : k ≃+* K' := FiniteField.ringEquivOfCardEq hcard
  have hne : ¬(m + 1 = 3 ∧ ℓ ^ e = 2) := fun h' => hq h'.2
  let e₄ : primeFormP h₀ (idGram k (m + 1)) ≃* StatedProj (StatedSU (m + 1) (ℓ ^ e) k) :=
    (Classical.choice (unitary_prime_form_full_semilinear_realization h₀
      (isPrimeFormGram_idGram (K := k) (n := m + 1)) (by omega) hne).1).trans
      (unitaryPSUEquiv h₀ (by omega))
  let ε : Cat ⟨.twistedA m ⟨ℓ, e, hℓ, he⟩, hv⟩ ≃* primeFormP h₀ (idGram k (m + 1)) :=
    e₁.trans ((CFSG.Open.StatedSUFieldChange.statedProjSUEquiv eK (m + 1) (ℓ ^ e)).symm.trans
      e₄.symm)
  have hpd : p ≠ (TauCeti.LieTypeIndex.twistedA m ⟨ℓ, e, hℓ, he⟩).characteristic := by
    simpa using hpℓ
  have hex : ¬ IsD2SeitzException p (TauCeti.LieTypeIndex.twistedA m ⟨ℓ, e, hℓ, he⟩) := by
    rintro (⟨hp3, ⟨q, hq1, hq2, hd⟩ | ⟨q, hq1, hq2, hd⟩ | ⟨q, hq1, hq2, hd⟩ |
        ⟨q, hq1, hq2, hd | hd⟩ | hd⟩ | ⟨h5, hd | hd⟩)
    · cases hd
    · cases hd
    · obtain ⟨-, hqq⟩ := TauCeti.LieTypeIndex.twistedA.inj hd
      apply hq
      have h1 : ℓ = 2 := by
        have := congrArg TauCeti.PrimePower.p hqq
        simpa [hq1] using this
      have h2 : e = 1 := by
        have := congrArg TauCeti.PrimePower.exponent hqq
        simpa [hq2] using this
      rw [h1, h2]
      norm_num
    all_goals cases hd
  have h1 := hS ⟨.twistedA m ⟨ℓ, e, hℓ, he⟩, hv⟩ p hp hp2 hpd hex
    (E.map (MulAut.congr ε.symm).toMonoidHom) (isElemAbelian_map_congr ε.symm hE)
    (by rw [card_map_congr]; exact hc)
  exact planeGen_of_outer_model ε.symm h1

theorem range_subfieldPSU_le_seitzHyperGamma (hS : KFactSeitzRankTwo)
    (h : UnitaryFieldData ℓ f K) {m : ℕ} (hm : 2 ≤ m) (hne : ¬(m + 1 = 3 ∧ ℓ ^ f = 2)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) {σ : K ≃+* K} (hσ : orderOf σ = p)
    (hq₀ : ℓ ^ (f / p) ≠ 2) {E : Subgroup (MulAut (primeFormP h (idGram K (m + 1))))}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    (hσE : primeFormFieldHom h (isPrimeFormGram_one (n := m + 1)) σ ∈ E) :
    (subfieldPSU h (fixSubfield_unitaryFieldData h hp hp2 hσ)
      (fixSubfield_unitaryFieldData_bar h hp hp2 hσ) (m + 1)).range ≤ seitzHyperGamma p E := by
  classical
  have hfin : Finite K := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have hn : 3 ≤ m + 1 := by omega
  have : Finite (MulAut (primeFormP h (idGram K (m + 1)))) := MulEquiv.finite_left
  have hC : IsPrimeFormGram (1 : GL (Fin (m + 1)) K) := isPrimeFormGram_one
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  set hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ with hhbar
  set j := subfieldPSU h h₀ hbar (m + 1) with hjdef
  have hj : Function.Injective j := subfieldPSU_injective h h₀ hbar (m + 1) (by omega)
  set fσ := primeFormFieldHom h hC σ with hfσ
  have hισ : primeFormFieldFactor h hC hn hne fσ = σ := by
    have := primeFormFieldFactor_apply h hC hn hne 1 σ
    rwa [map_one, one_mul] at this
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  have hσD : fσ ∉ primeFormD h (idGram K (m + 1)) := by
    rw [← ker_primeFormFieldFactor h hC hn hne, MonoidHom.mem_ker, hισ]
    exact hσ1
  set B : Subgroup (MulAut (primeFormP h (idGram K (m + 1)))) :=
    E ⊓ primeFormD h (idGram K (m + 1)) with hBdef
  have hBc : Nat.card B = p ^ 2 := card_inf_eq_sq_of_decomp hp hE hcard hσE hσD
    (fun x hx => exists_zpow_mul_mem_primeFormD h hn hne hp hσ hE hx)
  have hBa : IsElemAbelian p B := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hE.2 x hx.1⟩
    have h' := congrArg Subtype.val (hE.1.is_comm.comm (⟨a, a.2.1⟩ : E) ⟨b, b.2.1⟩)
    exact h'
  have hBcomm : ∀ b ∈ B, fσ * b = b * fσ := fun b hb => by
    have h' := congrArg Subtype.val (hE.1.is_comm.comm (⟨_, hσE⟩ : E) ⟨b, hb.1⟩)
    exact h'
  have hBL : ∀ b ∈ B, ∀ x : primeFormP h₀ (idGram (fixSubfield σ) (m + 1)),
      ∃ x' : primeFormP h₀ (idGram (fixSubfield σ) (m + 1)), b (j x) = j x' := by
    intro b hb x
    obtain ⟨z, rfl⟩ := hb.2
    obtain ⟨c, hc⟩ := exists_glAut_eq_mul_scalar h hn (hBcomm _ hb)
    exact conjHom_subfieldPSU_mem h h₀ hbar hc x
  have hσL : ∀ x, fσ (j x) = j x := fun x => range_subfieldPSU_le h (m + 1) h₀ hbar ⟨x, rfl⟩
  have hhyp : ∀ b ∈ B, b ≠ 1 → fixedPoints (Subgroup.closure
      ({b, fσ} : Set (MulAut (primeFormP h (idGram K (m + 1)))))) ≤ seitzHyperGamma p E := by
    intro b hb hb1
    have hσb : fσ ∉ Subgroup.zpowers b := fun h' => hσD ((Subgroup.zpowers_le.2 hb.2) h')
    exact CFSG.RankThree.PartTwo.Sec4.Res6L364.fixedPoints_le_seitzHyperGamma
      (closure_pair_le hb.1 hσE)
      (relIndex_closure_pair_of_indep hp hE hcard hb.1 hσE hb1 hσb).2
  have hfixL : ∀ b ∈ B, b ≠ 1 → ∀ x, b (j x) = j x → j x ∈ seitzHyperGamma p E := by
    intro b hb hb1 x hbx
    refine hhyp b hb hb1 (CFSG.RankThree.PartTwo.Sec4.Res6L364.mem_fixedPoints_closure ?_)
    rintro φ (rfl | rfl)
    · exact hbx
    · exact hσL x
  set ρ := resAut j hj B hBL with hρ
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    rw [Subgroup.mem_bot]
    have hβ : ∀ y ∈ j.range, (b : MulAut (primeFormP h (idGram K (m + 1)))) y = y := by
      rintro _ ⟨x, rfl⟩
      have h1 := map_resAut j hj B hBL b x
      rw [← hρ, hb] at h1
      exact h1.symm
    obtain ⟨τ, -, hτ⟩ := eq_primeFormFieldHom_of_fix h (m + 1) h₀ hbar hn hne
      (fun h' => hq₀ h'.2) (b : MulAut (primeFormP h (idGram K (m + 1)))) hβ
    have hιb : primeFormFieldFactor h hC hn hne b = 1 := by
      rw [← MonoidHom.mem_ker, ker_primeFormFieldFactor]
      exact b.2.2
    have hτ1 : τ = 1 := by
      have e1 := primeFormFieldFactor_apply h hC hn hne 1 τ
      rw [map_one, one_mul] at e1
      rw [← e1, ← hτ]
      exact hιb
    apply Subtype.ext
    rw [hτ, hτ1, map_one]
    rfl
  set E₁ : Subgroup (MulAut (primeFormP h₀ (idGram (fixSubfield σ) (m + 1)))) := ρ.range with hE₁
  have hE₁a : IsElemAbelian p E₁ := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨a', rfl⟩⟩ := a
      obtain ⟨_, ⟨b', rfl⟩⟩ := b
      apply Subtype.ext
      show ρ a' * ρ b' = ρ b' * ρ a'
      rw [← map_mul, ← map_mul]
      congr 1
      exact hBa.1.is_comm.comm a' b'
    · rintro _ ⟨b', rfl⟩
      rw [← map_pow]
      have : b' ^ p = 1 := Subtype.ext (hBa.2 _ b'.2)
      rw [this, map_one]
  have hE₁c : Nat.card E₁ = p ^ 2 := by
    rw [hE₁, ← hBc]
    exact Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv.symm
  have hpl : PlaneGen E₁ := planeGen_primeFormP_kfact hS h₀ hm hq₀ hp hp2 hpℓ hE₁a hE₁c
  have hL : j.range = (planeClosure E₁).map j := by
    rw [show planeClosure E₁ = ⊤ from hpl, ← MonoidHom.range_eq_map]
  rw [hL, planeClosure, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨x, ⟨e₁, he₁, he₁1, he₁x⟩, rfl⟩
  obtain ⟨b, rfl⟩ := he₁
  have hb1 : (b : MulAut (primeFormP h (idGram K (m + 1)))) ≠ 1 := by
    intro h1
    apply he₁1
    have : b = 1 := Subtype.ext h1
    rw [this, map_one]
  refine hfixL b b.2 hb1 x ?_
  rw [← map_resAut j hj B hBL b x]
  exact congrArg j he₁x

theorem seitzHyperGamma_eq_top_of_not_le_primeFormD
    (hS : KFactSeitzRankTwo) (h : UnitaryFieldData ℓ f K) {m : ℕ} (hm : 2 ≤ m)
    (hne : ¬(m + 1 = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hpq : p ∣ ℓ ^ f + 1) (h8 : ¬ (p = 3 ∧ ℓ ^ f = 8))
    {E : Subgroup (MulAut (primeFormP h (idGram K (m + 1))))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 3) (hout : ¬ E ≤ primeFormD h (idGram K (m + 1))) :
    seitzHyperGamma p E = ⊤ := by
  classical
  have hfin : Finite K := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have hn : 3 ≤ m + 1 := by omega
  have : Finite (MulAut (primeFormP h (idGram K (m + 1)))) := MulEquiv.finite_left
  have hC : IsPrimeFormGram (1 : GL (Fin (m + 1)) K) := isPrimeFormGram_one
  obtain ⟨a, haE, haD⟩ : ∃ a ∈ E, a ∉ primeFormD h (idGram K (m + 1)) := by
    by_contra hcon
    push Not at hcon
    exact hout fun a ha => hcon a ha
  have haι : primeFormFieldFactor h hC hn hne a ≠ 1 := fun h1 => haD (by
    rw [← ker_primeFormFieldFactor h hC hn hne]
    exact h1)
  have ha1 : a ≠ 1 := fun h1 => haι (by rw [h1, map_one])
  have haord : orderOf a = p := orderOf_eq_prime (hE.2 a haE) ha1
  set σ := primeFormFieldFactor h hC hn hne a with hσdef
  have hσp : σ ^ p = 1 := by rw [hσdef, ← map_pow, hE.2 a haE, map_one]
  have hσord : orderOf σ = p := orderOf_eq_prime hσp haι
  have hpf : p ∣ f := (dvd_and_card_fixSubfield_unitary h hp hp2 hσord).1
  have hq₀ : ℓ ^ (f / p) ≠ 2 := by
    intro h2
    obtain ⟨hℓ2, hf1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 h2
    have hfp : f = p := by
      have := Nat.div_mul_cancel hpf
      rw [hf1, one_mul] at this
      exact this.symm
    rw [hℓ2, hfp] at hpq h8
    have h3 : p ∣ 3 := by
      have h1 : ((2 ^ p + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 hpq
      push_cast at h1
      rw [ZMod.pow_card] at h1
      have h4 : ((3 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination h1
      exact (ZMod.natCast_eq_zero_iff _ p).1 h4
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
    exact h8 ⟨hp3, by rw [hp3]; norm_num⟩
  have hq₀' : ¬(m + 1 = 3 ∧ ℓ ^ (f / p) = 2) := fun h' => hq₀ h'.2
  set κ := primeFormConjHom h (idGram K (m + 1)) with hκ
  set fσ := primeFormFieldHom h hC σ with hfσ
  have hισ : primeFormFieldFactor h hC hn hne fσ = σ := by
    have := primeFormFieldFactor_apply h hC hn hne 1 σ
    rwa [map_one, one_mul] at this
  have hσ1 : σ ≠ 1 := haι
  have hσD : fσ ∉ primeFormD h (idGram K (m + 1)) := by
    rw [← ker_primeFormFieldFactor h hC hn hne, MonoidHom.mem_ker, hισ]
    exact hσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hne hp hp2 hpℓ a
      haord σ rfl hσord
  set E' := E.map (MulAut.congr (κ M)⁻¹).toMonoidHom with hE'def
  have hσE' : fσ ∈ E' := by
    refine ⟨a, haE, ?_⟩
    change (κ M)⁻¹ * a * ((κ M)⁻¹)⁻¹ = fσ
    rw [inv_inv]
    exact hM
  have hE'a : IsElemAbelian p E' := isElemAbelian_map_congr _ hE
  have hE'c : Nat.card E' = p ^ 3 := (card_map_congr _ E).trans hc
  have hBc := card_inf_eq_sq_of_decomp hp hE'a hE'c hσE' hσD
    (fun x hx => exists_zpow_mul_mem_primeFormD h hn hne hp hσord hE'a hx)
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ E' ⊓ primeFormD h (idGram K (m + 1)), b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : E' ⊓ primeFormD h (idGram K (m + 1)) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [hbot, Subgroup.card_bot] at hBc
    have := Nat.one_lt_pow (by norm_num : 2 ≠ 0) hp.one_lt
    omega
  have hιb : primeFormFieldFactor h hC hn hne b = 1 := by
    rw [← MonoidHom.mem_ker, ker_primeFormFieldFactor]
    exact hbB.2
  have hbσE : b * fσ ∈ E' := E'.mul_mem hbB.1 hσE'
  have hbσι : primeFormFieldFactor h hC hn hne (b * fσ) = σ := by
    rw [map_mul, hιb, one_mul, hισ]
  have hbσ1 : b * fσ ≠ 1 := fun h1 => hσ1 (by rw [← hbσι, h1, map_one])
  have hbσord : orderOf (b * fσ) = p := orderOf_eq_prime (hE'a.2 _ hbσE) hbσ1
  obtain ⟨-, -, -, -, -, M', hM'⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hne hp hp2 hpℓ
      (b * fσ) hbσord σ hbσι hσord
  set E'' := E'.map (MulAut.congr (κ M')⁻¹).toMonoidHom with hE''def
  have hσE'' : fσ ∈ E'' := by
    refine ⟨b * fσ, hbσE, ?_⟩
    change (κ M')⁻¹ * (b * fσ) * ((κ M')⁻¹)⁻¹ = fσ
    rw [inv_inv]
    exact hM'
  have hE''a : IsElemAbelian p E'' := isElemAbelian_map_congr _ hE'a
  have hE''c : Nat.card E'' = p ^ 3 := (card_map_congr _ E').trans hE'c
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσord with hh₀
  set hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσord with hhbar
  have hfeq : f = p * (f / p) := (Nat.mul_div_cancel' hpf).symm
  set Q := QuotientGroup.mk' (normOneScalars h
    (gramSU h ((1 : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) (m + 1)) with hQ
  have hFmk : (subfieldPSU h h₀ hbar (m + 1)).range = (suSub h h₀ hbar (m + 1)).map Q :=
    range_subfieldPSU_eq_map h h₀ hbar (m + 1)
  have hfixF : ∀ x ∈ (subfieldPSU h h₀ hbar (m + 1)).range, fσ x = x := fun x hx =>
    range_subfieldPSU_le h (m + 1) h₀ hbar hx
  have hQmem : ∀ g ∈ suSub h h₀ hbar (m + 1), Q g ∈ (subfieldPSU h h₀ hbar (m + 1)).range :=
    fun g hg => by
      rw [hFmk]
      exact ⟨g, hg, rfl⟩
  have h1 := range_subfieldPSU_le_seitzHyperGamma hS h hm hne hp hp2 hpℓ hσord hq₀ hE'a hE'c
    hσE'
  have h2 := range_subfieldPSU_le_seitzHyperGamma hS h hm hne hp hp2 hpℓ hσord hq₀ hE''a hE''c
    hσE''
  have hconj' : (b * fσ) * κ M' = κ M' * fσ := by
    calc (b * fσ) * κ M' = κ M' * ((κ M')⁻¹ * (b * fσ) * κ M') := by group
      _ = κ M' * fσ := by rw [hM']
  have hne' : (suSub h h₀ hbar (m + 1)).map (primeFormConjSU h _ M').toMonoidHom ≠
      suSub h h₀ hbar (m + 1) := by
    intro heq
    have hFmap : ((subfieldPSU h h₀ hbar (m + 1)).range).map (κ M').toMonoidHom =
        (subfieldPSU h h₀ hbar (m + 1)).range := by
      rw [hFmk, map_primeFormConjHom_map_mk h h₀ hbar (m + 1) M', heq]
    have hfix' : ∀ x ∈ (subfieldPSU h h₀ hbar (m + 1)).range, (b * fσ) x = x := by
      intro x hx
      have hx' : x ∈ ((subfieldPSU h h₀ hbar (m + 1)).range).map (κ M').toMonoidHom := by
        rw [hFmap]
        exact hx
      obtain ⟨y, hy, rfl⟩ := hx'
      change (b * fσ) (κ M' y) = κ M' y
      rw [show (b * fσ) (κ M' y) = (b * fσ * κ M') y from rfl, hconj', MulAut.mul_apply,
        hfixF y hy]
    have hβ : ∀ x ∈ (subfieldPSU h h₀ hbar (m + 1)).range, b x = x := by
      intro x hx
      have h3 : (b * fσ) x = b (fσ x) := rfl
      rw [hfixF x hx] at h3
      rw [← h3]
      exact hfix' x hx
    obtain ⟨τ, -, hτ⟩ := eq_primeFormFieldHom_of_fix h (m + 1) h₀ hbar hn hne hq₀' b hβ
    have hτ1 : τ = 1 := by
      have e1 := primeFormFieldFactor_apply h hC hn hne 1 τ
      rw [map_one, one_mul] at e1
      rw [← e1, ← hτ]
      exact hιb
    apply hb1
    rw [hτ, hτ1, map_one]
  have hgen := subfieldPairSUOdd_of_ne_two ℓ f (f / p) K h (fixSubfield σ) h₀ hbar p hp hp2 hfeq
    hq₀ (m + 1) hn M' hne'
  have hcomap : (seitzHyperGamma p E').comap Q = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro g (hg | ⟨g, hg, rfl⟩)
    · exact h1 (hQmem g hg)
    · have h3 := mem_seitzHyperGamma_of_map_congr (h2 (hQmem g hg))
      rw [inv_inv] at h3
      have hQg : Q ((primeFormConjSU h _ M').toMonoidHom g) = κ M' (Q g) :=
        (primeFormConjHom_mk h _ M' g).symm
      show Q ((primeFormConjSU h _ M').toMonoidHom g) ∈ seitzHyperGamma p E'
      rw [hQg]
      exact h3
  have hE'top : seitzHyperGamma p E' = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ z
    have hg : g ∈ (seitzHyperGamma p E').comap Q := by
      rw [hcomap]
      exact Subgroup.mem_top g
    exact hg
  exact CFSG.RankThree.PartTwo.Sec4.Res6L364.seitzHyperGamma_eq_top_of_map (κ M)⁻¹
    (MulAut.congr (κ M)⁻¹).toMonoidHom (fun a y => by simp [MulAut.congr_apply])
    (MulAut.congr (κ M)⁻¹).injective hE'top

end Unitary

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2
