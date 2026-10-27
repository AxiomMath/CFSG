module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SmallPSp45
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpOrbit83
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpOrbit83Check

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

section Family

open scoped Classical

variable {P : Type*} [AddCommGroup P] {p : ℕ} [Fact p.Prime] {S : Type*} [Group S] [Finite S]
  {ι : Type} [Fintype ι]

omit [Finite S] in
theorem exists_functional (ψ : Multiplicative P →* S) {D₀ : Subgroup S}
    (hrel : D₀.relIndex ψ.range = p) :
    ∃ l : P →+ ZMod p, l ≠ 0 ∧ ∀ z : P, l z = 0 ↔ ψ (Multiplicative.ofAdd z) ∈ D₀ := by
  have hDidx : (D₀.comap ψ).index = p := by
    rw [Subgroup.index_comap]
    exact hrel
  have hDaidx : (AddSubgroup.toSubgroup.symm (D₀.comap ψ)).index = p := by
    rw [← AddSubgroup.index_toSubgroup, OrderIso.apply_symm_apply]
    exact hDidx
  obtain ⟨l, hl⟩ := exists_hom_of_index_eq_prime _ hDaidx
  have hlD : ∀ z : P, l z = 0 ↔ ψ (Multiplicative.ofAdd z) ∈ D₀ := fun z =>
    (hl z).trans (mem_toSubgroup_symm _ z)
  refine ⟨l, ?_, hlD⟩
  intro h0
  have htop : AddSubgroup.toSubgroup.symm (D₀.comap ψ) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    exact (hl z).1 (by rw [h0]; rfl)
  rw [htop, AddSubgroup.index_top] at hDaidx
  exact (Fact.out : p.Prime).one_lt.ne hDaidx

theorem horb_of_family_l (ψ : Multiplicative P →* S) (t : ι → S) (τ : ι → P →+ P)
    (ht : ∀ i x, t i * ψ x * (t i)⁻¹ = ψ (Multiplicative.ofAdd (τ i (Multiplicative.toAdd x))))
    {T₀ : Subgroup S} (hT : ∀ i, t i ∈ T₀) {D₀ : Subgroup S} (l : P →+ ZMod p)
    (hlD : ∀ z : P, l z = 0 ↔ ψ (Multiplicative.ofAdd z) ∈ D₀) {m : ℕ}
    (hm : m ≤ ((Finset.univ : Finset ι).image fun i => (l.comp (τ i)).ker).card) :
    m ≤ (T₀ ⊓ Subgroup.normalizer (D₀ : Set S)).relIndex T₀ := by
  have hker : ∀ i, (l.comp (τ i)).ker =
      AddSubgroup.toSubgroup.symm ((conjSub (t i)⁻¹ D₀).comap ψ) := by
    intro i
    ext z
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, hlD, mem_toSubgroup_symm,
      Subgroup.mem_comap, mem_conjSub, inv_inv, ht i (Multiplicative.ofAdd z), toAdd_ofAdd]
  let s : Finset S := Finset.univ.image fun i : ι => (t i)⁻¹
  have hs : ∀ y ∈ s, y ∈ T₀ := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
    exact T₀.inv_mem (hT i)
  have h1 := card_image_conj_le_relIndex T₀ D₀ s hs
  let G : Subgroup S → AddSubgroup P := fun C => AddSubgroup.toSubgroup.symm (C.comap ψ)
  have hcomp : (Finset.univ.image fun i => (l.comp (τ i)).ker) =
      (s.image fun y => conjSub y D₀).image G := by
    simp only [s, Finset.image_image]
    congr 1
    funext i
    exact hker i
  have h2 : (Finset.univ.image fun i => (l.comp (τ i)).ker).card ≤
      (s.image fun y => conjSub y D₀).card := by
    rw [hcomp]
    exact Finset.card_image_le
  exact hm.trans (h2.trans h1)

end Family

section Group

open Matrix CFSG.Assembly.LowTwoRank CFSG.LargeExtraspecial.A2Mod.FrC
open CFSG.LieType.Universal.Symplectic

variable {K : Type} [Field K] (φ : ZMod 3 →+* K)

@[expose] def symM8 (x : X3) : Matrix (Fin 4) (Fin 4) K := (symMat x).map φ

theorem symM_transpose8 (x : X3) : (symM8 φ x)ᵀ = symM8 φ x := by
  rw [symM8, ← Matrix.transpose_map, symMat_transpose]

theorem symM_add8 (x y : X3) : symM8 φ (x + y) = symM8 φ x + symM8 φ y := by
  ext i j
  simp [symM8, symMat_add]

theorem symM_zero8 : symM8 φ 0 = 0 := by
  ext i j; simp [symM8, symMat]

@[expose] noncomputable def psi08 : Multiplicative X3 →* StatedSp 4 K where
  toFun x := lower (symM8 φ (Multiplicative.toAdd x)) (symM_transpose8 φ _)
  map_one' := ext_mat (by
    rw [toAdd_one, mat_lower, symM_zero8, fromBlocks_one]
    rfl)
  map_mul' x y := ext_mat (by
    rw [toAdd_mul, map_mul, mat_lower, mat_lower, mat_lower, symM_add8, fromBlocks_multiply]
    simp [add_comm])

@[expose] noncomputable def psi8 : Multiplicative X3 →* StatedProj (StatedSp 4 K) :=
  (QuotientGroup.mk' _).comp (psi08 φ)

theorem symM_tau8 (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) (x : X3) :
    symM8 φ (tauL M x) = (M.map φ)ᵀ * symM8 φ x * M.map φ := by
  rw [symM8, symMat_tauL, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, symM8]

theorem det_map_ne (hφ : Function.Injective φ) {M : Matrix (Fin 4) (Fin 4) (ZMod 3)}
    (hM : M.det ≠ 0) : (M.map φ).det ≠ 0 := by
  have h : φ M.det = (M.map φ).det := RingHom.map_det φ M
  intro h0
  apply hM
  apply hφ
  rw [h, h0, map_zero]

@[expose] noncomputable def Mgl8 (hφ : Function.Injective φ) (M : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hM : M.det ≠ 0) : GL (Fin 4) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (M.map φ) (det_map_ne φ hφ hM)

theorem levGL_conj_psi08 (hφ : Function.Injective φ) (M : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hM : M.det ≠ 0) (x : Multiplicative X3) :
    levGL ((Mgl8 φ hφ M hM)⁻¹) * psi08 φ x * (levGL ((Mgl8 φ hφ M hM)⁻¹))⁻¹ =
      psi08 φ (Multiplicative.ofAdd (tauL M (Multiplicative.toAdd x))) := by
  refine levGL_conj_lower ((Mgl8 φ hφ M hM)⁻¹) (symM_transpose8 φ _) (symM_transpose8 φ _) ?_
  rw [toAdd_ofAdd, inv_inv, symM_tau8]
  rfl

@[expose] noncomputable def tEl8 (hφ : Function.Injective φ) (M : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hM : M.det ≠ 0) : StatedProj (StatedSp 4 K) :=
  QuotientGroup.mk' _ (levGL ((Mgl8 φ hφ M hM)⁻¹))

theorem tEl_conj8 (hφ : Function.Injective φ) (M : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hM : M.det ≠ 0) (x : Multiplicative X3) :
    tEl8 φ hφ M hM * psi8 φ x * (tEl8 φ hφ M hM)⁻¹ =
      psi8 φ (Multiplicative.ofAdd (tauL M (Multiplicative.toAdd x))) := by
  have := congrArg (QuotientGroup.mk' ((StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf
    (StatedSp 4 K))) (levGL_conj_psi08 φ hφ M hM x)
  simpa [tEl8, psi8, map_mul, map_inv] using this

theorem psi_ne_one8 : psi8 φ (Multiplicative.ofAdd (Pi.single 0 1 : X3)) ≠ 1 := by
  intro h
  rw [psi8, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  have hs : ((Matrix.GeneralLinearGroup.scalar (Fin 4 ⊕ Fin 4) c : GL (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
      (c : K) • (1 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) := by
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.one_apply]
  have h1 : SpExtras.mat 4 K (psi08 φ (Multiplicative.ofAdd (Pi.single 0 1 : X3))) =
      (c : K) • 1 := by
    rw [SpExtras.mat_apply, ← hs, hc]
  have e := congrFun (congrFun h1 (Sum.inr 0)) (Sum.inl 0)
  simp [psi08, symM8, symMat, cidx] at e

theorem pow_three_eq_one (x : Multiplicative X3) : x ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  ext k
  simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
  generalize Multiplicative.toAdd x k = a
  have : ((3 : ℕ) : ZMod 3) = 0 := by decide
  rw [this, zero_mul]

theorem orderOf_two_zmod_three_eq_two : orderOf (2 : ZMod 3) = 2 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m
  decide

variable {W : Type} [CommGroup W] [Finite W]

set_option maxHeartbeats 800000 in
theorem horb83 [CharP K 3] [Finite K] (hφ : Function.Injective φ)
    (D₀ : Subgroup (StatedProj (StatedSp 4 K))) (hrel : D₀.relIndex (psi8 φ).range = 3) :
    29 ≤ (Subgroup.normalizer ((psi8 φ).range : Set (StatedProj (StatedSp 4 K))) ⊓
      Subgroup.normalizer (D₀ : Set (StatedProj (StatedSp 4 K)))).relIndex
        (Subgroup.normalizer ((psi8 φ).range : Set (StatedProj (StatedSp 4 K)))) := by
  have : Finite (StatedProj (StatedSp 4 K)) := inferInstance
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨l, hl0, hlD⟩ := exists_functional (psi8 φ) (p := 3) hrel
  obtain ⟨C, hC, hcard⟩ := kernels_ge Afam pair_distinct form_ne_zero l hl0
  have hdet : ∀ i, (Afam i * C).det ≠ 0 := fun i => by
    rw [Matrix.det_mul]
    exact mul_ne_zero (Afam_det i) hC
  have hT : ∀ i, tEl8 φ hφ (Afam i * C) (hdet i) ∈
      Subgroup.normalizer ((psi8 φ).range : Set (StatedProj (StatedSp 4 K))) := by
    intro i
    refine mem_normalizer_of_forall_conj_mem fun y hy => ?_
    obtain ⟨x, rfl⟩ := hy
    rw [tEl_conj8]
    exact ⟨_, rfl⟩
  exact horb_of_family_l (P := X3) (p := 3) (ι := Fin 29) (psi8 φ)
    (fun i => tEl8 φ hφ (Afam i * C) (hdet i)) (fun i => (tauL (Afam i * C)).toAddMonoidHom)
    (fun i x => tEl_conj8 φ hφ (Afam i * C) (hdet i) x) hT l hlD hcard

theorem two_pow_le_card_of_psp83 (hW : ∀ w : W, w * w = 1) [CharP K 3] [Finite K]
    {L : Subgroup (MulAut W)} (θ : ↥L ≃* StatedProj (StatedSp 4 K)) : 2 ^ 58 ≤ Nat.card W := by
  let φ : ZMod 3 →+* K := ZMod.castHom (dvd_refl 3) K
  have hφ : Function.Injective φ := φ.injective
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hker : (θ.toMonoidHom).ker = ⊥ := by
    rw [MonoidHom.ker_eq_bot_iff]
    exact θ.injective
  have hUc : ∀ a ∈ (psi8 φ).range, ∀ b ∈ (psi8 φ).range, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hUp : ∀ a ∈ (psi8 φ).range, a ^ 3 = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow, pow_three_eq_one x, map_one]
  have hU : (psi8 φ).range ≠ ⊥ := fun h =>
    psi_ne_one8 φ (by rw [← Subgroup.mem_bot, ← h]; exact ⟨_, rfl⟩)
  have key := two_pow_le_card_of_lift_orbit (p := 3) hW (by norm_num) θ.toMonoidHom θ.surjective
    (by rw [hker]; exact bot_le) (by rw [hker, Subgroup.card_bot]; norm_num) hUc hUp hU le_rfl
    (m := 29) (fun D₀ _ hrel => horb83 φ hφ D₀ hrel)
  rw [orderOf_two_zmod_three_eq_two] at key
  simpa using key

end Group

open CFSG.Quasithin TauCeti CFSG.HardMathSupport.Cooperstein.Coordinator

theorem noIrrFFOffender_smallPSp83 {q : PrimePower} (hv : (LieTypeIndex.C 4 q).Valid)
    (h3 : q.card = 3) : NoIrrFFOffender (CFSGIndex.lie ⟨.C 4 q, hv⟩).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hp : q.p.Prime := q.prime_p
  have hcard : q.card = q.p ^ q.exponent := PrimePower.card_def q
  have hp3 : q.p = 3 := by
    have h1 : q.p ∣ 3 := by
      rw [← h3, hcard]; exact dvd_pow_self _ q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h1
  have he1 : q.exponent = 1 := by
    have h1 : 3 ^ q.exponent = 3 ^ 1 := by rw [← hp3, ← hcard, h3, hp3]; rfl
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  have hp2 : q.p ≠ 2 := by rw [hp3]; norm_num
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  obtain ⟨hcenter, K, _, _, hK, ⟨θ⟩⟩ :=
    exists_psp_model_of_lie_C hq.1 (FFToolkit.odd_card_center_of_isIrrOn hW hirr) hv e
  have : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = q.p ^ q.exponent := by
    rw [← Nat.card_eq_fintype_card]; exact hK
  have : CharP K q.p := charP_of_card_eq_prime_pow hKcard
  have : CharP K 3 := by rwa [← hp3]
  have hdim := two_pow_le_card_of_psp83 hW θ
  have hord := card_sup_le_of_pspn hW hp2 hK (by norm_num) hirr hcenter θ hEN hel
  rw [hp3, he1] at hord
  norm_num at hord
  by_contra hcon
  push Not at hcon
  have hU1 := FFToolkit.card_le_card_sup_of_offender hW hq hirr hEN hE hel hcon
  norm_num at hdim
  omega

theorem smallPSp83 : SmallPSp83 := by
  intro d q hq hd
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_smallPSp83 hv hq)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
