module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODUnitaryMono
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291LinUniFam
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt ODFamily odC odC_injective
  odC_of_mem od_card_torus od_torus_pow l212in_descend l212in_descend_injective)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291LinUni
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry (Uid)
open CFSG.LocalAnalysis.RankFourTheoremC (l212in_suPhi)
open CFSG.LocalAnalysis.RankFourTheoremC (odFamily_unitary_of_inputs odUZ mem_odUZ
  od_unitary_nonpower l212in_suConj l212in_suConj_coe l212in_suPhi_mk l212in_scalar_comm
  exists_cover_unitary i294ODUnitaryTorus_holds i294ODUnitaryMonomial_holds l212in_detU)

theorem kd291_aux_G_keyP {p : ℕ} (hp : p.Prime) (s r : ℤ) (hs : ¬ (p : ℤ) ∣ s) :
    ∃ j : ℕ, (p : ℤ) ∣ r - s * (j : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hs0 : (s : ZMod p) ≠ 0 := fun h => hs ((ZMod.intCast_zmod_eq_zero_iff_dvd s p).1 h)
  have hinv : (s : ZMod p) * (s : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hs0
  refine ⟨((r : ZMod p) * (s : ZMod p)⁻¹).val, ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
  have hj : (((r : ZMod p) * (s : ZMod p)⁻¹).val : ZMod p) = (r : ZMod p) * (s : ZMod p)⁻¹ :=
    ZMod.natCast_zmod_val _
  rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, hj]
  linear_combination (-(r : ZMod p)) * hinv

theorem kd291_cyclic_gen {p : ℕ} (hp : p.Prime) {C : Type} [CommGroup C] (hcyc : IsCyclic C)
    {d : C} (hd : ∀ c : C, d ≠ c ^ p) (c : C) : ∃ (j : ℕ) (u : C), c = d ^ j * u ^ p := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := C)
  obtain ⟨s, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hγ d)
  obtain ⟨r, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hγ c)
  have hs : ¬ (p : ℤ) ∣ s := by
    rintro ⟨t, rfl⟩
    apply hd (γ ^ t)
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  obtain ⟨j, hj⟩ := kd291_aux_G_keyP hp s r hs
  obtain ⟨w, hw⟩ := hj
  refine ⟨j, γ ^ w, ?_⟩
  rw [← zpow_natCast (γ ^ s) j, ← zpow_mul, ← zpow_natCast (γ ^ w) p, ← zpow_mul, ← zpow_add]
  congr 1
  linear_combination hw

theorem kd291_lu_false_abs {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Y : Type} [Group Y]
    [Finite Y] (L : Subgroup Y) [L.Normal]
    [Group.IsPerfect ↥L] (hcen : centralizer (L : Set Y) = ⊥)
    (hperf : ∀ (N : Subgroup Y) [N.Normal], IsPGroup p (Y ⧸ N) → N = ⊤)
    (hY3 : Open.pRank p (⊤ : Subgroup Y) ≤ 3) {x : Y} (hx : orderOf x = p)
    (hx2 : Open.pRank p (centralizer ({x} : Set Y)) ≤ 2)
    {S₀ P G C : Type} [Group S₀] [Group P] [Group G] [CommGroup C]
    (hS₀ : Group.IsPerfect S₀) (π : S₀ →* P) (c : G → (S₀ →* S₀)) (Φ : G →* MulAut P)
    (det : G →* C) (Z : Subgroup G) (hF : ODFamily p p Φ det Z)
    (e : ↥L ⧸ center ↥L ≃* P) (φ : S₀ →* ↥L) (hφπ : ∀ s, e (QuotientGroup.mk (φ s)) = π s)
    (hc : ∀ B s, π (c B s) = Φ B (π s)) (hcZ : ∀ w ∈ Z, ∀ B : G, c (w * B) = c B)
    (htorus : ∀ B : G, B ^ p = 1 → ∃ f : (Fin 3 → Multiplicative (ZMod p)) →* S₀,
      Function.Injective (π.comp f) ∧ ∀ a, c B (f a) = f a)
    (htorus4 : ∃ f : (Fin 4 → Multiplicative (ZMod p)) →* G,
      Function.Injective (fun a => Φ (f a))) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxp : x ^ p = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  set ψ : Y →* MulAut P := (l212in_descend e).comp (odC L) with hψ
  haveI : Φ.range.Normal :=
    ⟨fun a ha g => by
      have h := hF.comm_mem g a
      have h2 : g * a * g⁻¹ = (g * a * g⁻¹ * a⁻¹) * a := by group
      rw [h2]
      exact mul_mem h ha⟩
  have hψinj : Function.Injective ψ :=
    (l212in_descend_injective e).comp (odC_injective hcen)
  obtain ⟨B, hB⟩ : ψ x ∈ Φ.range :=
    map_mem_of_pow_eq_one Φ.range hF.comm_mem hperf ψ hxp
  have hlift : ∀ s, odC L x (φ s) = φ (c B s) := by
    intro s
    refine CFSG.LocalAnalysis.RankFourTheoremC.l212in_alpha_phi e π φ hφπ (odC L x) (c B)
      (fun t => ?_) s
    rw [hc, hB]
    rfl
  have hBZ : B ^ p ∈ Z := by
    refine (hF.ker_eq (B ^ p)).1 ?_
    rw [map_pow, hB, ← map_pow, hxp, map_one]
  have hnp : ∀ w ∈ Z, w ^ p ≠ B ^ p := by
    intro w hw hwp
    have hw' : w⁻¹ ∈ Z := Z.inv_mem hw
    have hBp : (w⁻¹ * B) ^ p = 1 := by
      have hc1 : Commute w⁻¹ B := hF.central w⁻¹ hw' B
      rw [hc1.mul_pow, inv_pow, hwp, inv_mul_cancel]
    obtain ⟨f, hfi, hfix⟩ := htorus (w⁻¹ * B) hBp
    rw [hcZ w⁻¹ hw' B] at hfix
    have hinj : Function.Injective (φ.comp f) := by
      intro a b hab
      apply hfi
      change π (f a) = π (f b)
      rw [← hφπ, ← hφπ]
      exact congrArg (fun l : ↥L => e (QuotientGroup.mk l)) hab
    have h3 := CFSG.LocalAnalysis.RankFourTheoremC.od_three_le_pRank_of_torus (L := L) (x := x)
      (φ.comp f) hinj (fun a => by
        change odC L x (φ (f a)) = φ (f a)
        rw [hlift, hfix])
    omega
  have hdet : ∀ k : C, det B ≠ k ^ p := hF.det_nonpower rfl B hBZ hnp
  have hall : ∀ g : G, Φ g ∈ ψ.range := by
    intro g
    obtain ⟨j, u, hj⟩ := kd291_cyclic_gen hp hF.cyclic (d := det B) hdet (det g)
    have hdet' : det (g * (B ^ j)⁻¹) = u ^ p := by
      rw [map_mul, map_inv, map_pow, hj, mul_right_comm, mul_inv_cancel, one_mul]
    obtain ⟨p₀, hp₀⟩ := MonoidHom.mem_range.1 (hF.inner_of_det (g * (B ^ j)⁻¹) ⟨u, hdet'⟩)
    obtain ⟨ℓq, rfl⟩ := e.surjective p₀
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective ℓq
    have hψℓ : ψ (ℓ : Y) = MulAut.conj (e (QuotientGroup.mk ℓ)) := by
      show l212in_descend e (odC L (ℓ : Y)) = _
      rw [odC_of_mem ℓ.2]
      exact CFSG.LocalAnalysis.RankFourTheoremC.l212in_descend_conj e ℓ
    have hΦg' : Φ (g * (B ^ j)⁻¹) = ψ (ℓ : Y) := by
      rw [hψℓ, hp₀]
    refine MonoidHom.mem_range.2 ⟨(ℓ : Y) * x ^ j, ?_⟩
    rw [map_mul, map_pow, ← hΦg', ← hB, ← map_pow, ← map_mul]
    congr 1
    group
  obtain ⟨f4, hf4⟩ := htorus4
  let g4 : (Fin 4 → Multiplicative (ZMod p)) →* MulAut P := Φ.comp f4
  let g4' : (Fin 4 → Multiplicative (ZMod p)) →* ψ.range :=
    g4.codRestrict ψ.range (fun a => hall (f4 a))
  have hg4' : Function.Injective g4' := by
    intro a b hab
    apply hf4
    exact congrArg Subtype.val hab
  let iso : Y ≃* ψ.range := MonoidHom.ofInjective hψinj
  let f' : (Fin 4 → Multiplicative (ZMod p)) →* Y := iso.symm.toMonoidHom.comp g4'
  have hf' : Function.Injective f' := iso.symm.injective.comp hg4'
  have hA : Nat.card (Fin 4 → Multiplicative (ZMod p)) = p ^ 4 := od_card_torus 4
  have h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) :=
    CFSG.SectionRank.le_pRank_of_injective (p := p) hp.one_lt (fun a b => mul_comm a b)
      (fun a => od_torus_pow a) hA f' hf' le_top
  omega

theorem kd291_aux_T4L_exists_chi {p : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K]
    (hpK : p ∣ Nat.card K - 1) :
    ∃ χ : Multiplicative (ZMod p) →* Kˣ, Function.Injective χ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_units])
  have hprimU : IsPrimitiveRoot ζ p := by
    rw [← hζ]
    exact IsPrimitiveRoot.orderOf ζ
  exact ⟨(Subgroup.zpowers ζ).subtype.comp
    (AddEquiv.toMultiplicativeLeft hprimU.zmodEquivZPowers).toMonoidHom,
    Subtype.val_injective.comp (AddEquiv.toMultiplicativeLeft hprimU.zmodEquivZPowers).injective⟩

@[expose] noncomputable def kd291_aux_T4L_diag (p : ℕ) (K : Type) [Field K] :
    (Fin p → Kˣ) →* GL (Fin p) K :=
  (Units.map (Matrix.diagonalRingHom (Fin p) K).toMonoidHom).comp
    (MulEquiv.piUnits.symm : (Fin p → Kˣ) ≃* (Fin p → K)ˣ).toMonoidHom

theorem kd291_aux_T4L_diag_val (p : ℕ) (K : Type) [Field K] (t : Fin p → Kˣ) :
    ((kd291_aux_T4L_diag p K t : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
      Matrix.diagonal (fun i => ((t i : Kˣ) : K)) := rfl

@[expose] noncomputable def kd291_aux_T4L_ext (p : ℕ) :
    (Fin 4 → Multiplicative (ZMod p)) →* (Fin p → Multiplicative (ZMod p)) where
  toFun a i := if h : i.val < 4 then a ⟨i.val, h⟩ else 1
  map_one' := by
    funext i
    by_cases h : i.val < 4 <;> simp [h]
  map_mul' a b := by
    funext i
    by_cases h : i.val < 4 <;> simp [h]

theorem kd291_aux_T4L_ext_apply {p : ℕ} (a : Fin 4 → Multiplicative (ZMod p)) (i : Fin p)
    (j : Fin 4) (hij : i.val = j.val) : kd291_aux_T4L_ext p a i = a j := by
  have hi : i.val < 4 := by have := j.isLt; omega
  show (if h : i.val < 4 then a ⟨i.val, h⟩ else 1) = a j
  rw [dif_pos hi]
  exact congrArg a (Fin.ext hij)

theorem kd291_aux_T4L_ext_ge {p : ℕ} (a : Fin 4 → Multiplicative (ZMod p)) (i : Fin p)
    (hi : ¬ i.val < 4) : kd291_aux_T4L_ext p a i = 1 := by
  show (if h : i.val < 4 then a ⟨i.val, h⟩ else 1) = 1
  rw [dif_neg hi]

@[expose] noncomputable def kd291_aux_T4L_f (p : ℕ) (K : Type) [Field K]
    (χ : Multiplicative (ZMod p) →* Kˣ) :
    (Fin 4 → Multiplicative (ZMod p)) →* GL (Fin p) K :=
  (kd291_aux_T4L_diag p K).comp
    ((MonoidHom.piMap (fun _ : Fin p => χ)).comp (kd291_aux_T4L_ext p))

theorem kd291_aux_T4L_f_apply (p : ℕ) (K : Type) [Field K] (χ : Multiplicative (ZMod p) →* Kˣ)
    (a : Fin 4 → Multiplicative (ZMod p)) (i : Fin p) :
    ((kd291_aux_T4L_f p K χ a : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) i i =
      ((χ (kd291_aux_T4L_ext p a i) : Kˣ) : K) := by
  simp only [kd291_aux_T4L_f, MonoidHom.comp_apply, kd291_aux_T4L_diag_val,
    Matrix.diagonal_apply_eq]
  rfl

theorem kd291_linear_torus4 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {K : Type} [Field K]
    [Finite K] (hpK : p ∣ Nat.card K - 1) :
    ∃ f : (Fin 4 → Multiplicative (ZMod p)) →* GL (Fin p) K,
      Function.Injective (fun a =>
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut p K (f a)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨χ, hχ⟩ := kd291_aux_T4L_exists_chi hp hpK
  refine ⟨kd291_aux_T4L_f p K χ, ?_⟩
  have hinj : Function.Injective
      ((CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut p K).comp
        (kd291_aux_T4L_f p K χ)) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have ha' : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut p K
        (kd291_aux_T4L_f p K χ a) = 1 := ha
    obtain ⟨c, hc⟩ :=
      (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (n := p) (K := K) (by omega)
        (kd291_aux_T4L_f p K χ a)).1 ha'
    have hdiag : ∀ i : Fin p, ((c : Kˣ) : K) = ((χ (kd291_aux_T4L_ext p a i) : Kˣ) : K) := by
      intro i
      have h2 := congrArg (fun B : GL (Fin p) K => (B : Matrix (Fin p) (Fin p) K) i i) hc
      simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq] at h2
      rw [kd291_aux_T4L_f_apply] at h2
      exact h2
    have h4 : 4 < p := by omega
    have hc1 : ((c : Kˣ) : K) = 1 := by
      have h := hdiag ⟨4, h4⟩
      rw [kd291_aux_T4L_ext_ge a ⟨4, h4⟩ (by simp), map_one, Units.val_one] at h
      exact h
    have hj : ∀ j : Fin 4, a j = 1 := by
      intro j
      have hjp : j.val < p := by have := j.isLt; omega
      have h := hdiag ⟨j.val, hjp⟩
      rw [hc1, kd291_aux_T4L_ext_apply a ⟨j.val, hjp⟩ j rfl] at h
      have h' : χ (a j) = 1 := Units.ext (by rw [Units.val_one]; exact h.symm)
      exact hχ (h'.trans (map_one χ).symm)
    exact funext hj
  exact hinj

section KD291T4UAux

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.ComponentClassification.CatalogueBUnitaryIsometry

theorem kd291_aux_T4U_chi {p : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K]
    (hpK : p ∣ Nat.card K - 1) :
    ∃ χ : Multiplicative (ZMod p) →* Kˣ, Function.Injective χ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_units])
  have hprimU : IsPrimitiveRoot ζ p := by
    rw [← hζ]
    exact IsPrimitiveRoot.orderOf ζ
  exact ⟨(Subgroup.zpowers ζ).subtype.comp
    (AddEquiv.toMultiplicativeLeft hprimU.zmodEquivZPowers).toMonoidHom,
    Subtype.val_injective.comp (AddEquiv.toMultiplicativeLeft hprimU.zmodEquivZPowers).injective⟩

theorem kd291_aux_T4U_powp {p : ℕ} (a : Multiplicative (ZMod p)) : a ^ p = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

@[expose] noncomputable def kd291_aux_T4U_diag {p : ℕ} {K : Type} [Field K]
    (χ : Multiplicative (ZMod p) →* Kˣ) (a : Fin 4 → Multiplicative (ZMod p)) : Fin p → Kˣ :=
  fun i => if h : i.val < 4 then χ (a ⟨i.val, h⟩) else 1

theorem kd291_aux_T4U_diag_one {p : ℕ} {K : Type} [Field K]
    (χ : Multiplicative (ZMod p) →* Kˣ) :
    kd291_aux_T4U_diag (K := K) χ 1 = 1 := by
  funext i
  simp only [kd291_aux_T4U_diag, Pi.one_apply]
  split_ifs <;> simp

theorem kd291_aux_T4U_diag_mul {p : ℕ} {K : Type} [Field K]
    (χ : Multiplicative (ZMod p) →* Kˣ) (a b : Fin 4 → Multiplicative (ZMod p)) :
    kd291_aux_T4U_diag χ (a * b) = kd291_aux_T4U_diag χ a * kd291_aux_T4U_diag χ b := by
  funext i
  simp only [kd291_aux_T4U_diag, Pi.mul_apply]
  split_ifs <;> simp [map_mul]

@[expose] noncomputable def kd291_aux_T4U_gl {p : ℕ} {K : Type} [Field K] (d : Fin p → Kˣ) :
    Matrix.GeneralLinearGroup (Fin p) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal fun i => (d i : K)) (by
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => (d i).ne_zero)

theorem kd291_aux_T4U_gl_coe {p : ℕ} {K : Type} [Field K] (d : Fin p → Kˣ) :
    ((kd291_aux_T4U_gl d : Matrix.GeneralLinearGroup (Fin p) K) : Matrix (Fin p) (Fin p) K) =
      diagonal fun i => (d i : K) :=
  rfl

theorem kd291_aux_T4U_gl_mul {p : ℕ} {K : Type} [Field K] (d d' : Fin p → Kˣ) :
    kd291_aux_T4U_gl (d * d') = kd291_aux_T4U_gl d * kd291_aux_T4U_gl d' := by
  apply Units.ext
  simp only [kd291_aux_T4U_gl_coe, Units.val_mul, diagonal_mul_diagonal]
  congr 1

theorem kd291_aux_T4U_gl_one {p : ℕ} {K : Type} [Field K] :
    kd291_aux_T4U_gl (1 : Fin p → Kˣ) = 1 := by
  apply Units.ext
  simp [kd291_aux_T4U_gl_coe]

@[expose] noncomputable def kd291_aux_T4U_hom {p : ℕ} {K : Type} [Field K]
    (χ : Multiplicative (ZMod p) →* Kˣ) :
    (Fin 4 → Multiplicative (ZMod p)) →* Matrix.GeneralLinearGroup (Fin p) K where
  toFun a := kd291_aux_T4U_gl (kd291_aux_T4U_diag χ a)
  map_one' := by
    show kd291_aux_T4U_gl (kd291_aux_T4U_diag χ 1) = 1
    rw [kd291_aux_T4U_diag_one, kd291_aux_T4U_gl_one]
  map_mul' a b := by
    show kd291_aux_T4U_gl (kd291_aux_T4U_diag χ (a * b)) =
      kd291_aux_T4U_gl (kd291_aux_T4U_diag χ a) * kd291_aux_T4U_gl (kd291_aux_T4U_diag χ b)
    rw [kd291_aux_T4U_diag_mul, kd291_aux_T4U_gl_mul]

theorem kd291_aux_T4U_conjTr_diag {p : ℕ} {K : Type} [Field K] (σ : K ≃+* K)
    (t : Fin p → K) :
    conjTr σ (diagonal t) = diagonal fun i => σ (t i) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [conjTr]
  · simp [conjTr, h, Ne.symm h]

theorem kd291_aux_T4U_mem {p r f : ℕ} [Fact r.Prime] {K : Type} [Field K] [Finite K]
    [CharP K r] (χ : Multiplicative (ZMod p) →* Kˣ) (hχ : ∀ a, χ a ^ (r ^ f + 1) = 1)
    (a : Fin 4 → Multiplicative (ZMod p)) :
    kd291_aux_T4U_gl (kd291_aux_T4U_diag χ a) ∈ Uid (unitaryInvolution K r f) p := by
  have hi : ∀ i, kd291_aux_T4U_diag χ a i ^ (r ^ f + 1) = 1 := by
    intro i
    simp only [kd291_aux_T4U_diag]
    split_ifs
    · exact hχ _
    · simp
  rw [mem_Uid_iff, kd291_aux_T4U_gl_coe, kd291_aux_T4U_conjTr_diag, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext i
  rw [unitaryInvolution_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, hi i, Units.val_one]

theorem kd291_aux_T4U_eq_one {p : ℕ} (hp5 : 5 ≤ p) {K : Type} [Field K]
    (χ : Multiplicative (ZMod p) →* Kˣ) (hχi : Function.Injective χ)
    (a : Fin 4 → Multiplicative (ZMod p)) (c : Kˣ)
    (hc : Matrix.GeneralLinearGroup.scalar (Fin p) c =
      kd291_aux_T4U_gl (kd291_aux_T4U_diag χ a)) :
    a = 1 := by
  have hent : ∀ i : Fin p, (c : K) = ((kd291_aux_T4U_diag χ a i : Kˣ) : K) := by
    intro i
    have h := congrArg (fun g : Matrix.GeneralLinearGroup (Fin p) K =>
      (g : Matrix (Fin p) (Fin p) K) i i) hc
    simpa [kd291_aux_T4U_gl_coe, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
      using h
  have h4 : (c : K) = 1 := by
    have h := hent ⟨4, by omega⟩
    simpa [kd291_aux_T4U_diag] using h
  funext j
  have hd : kd291_aux_T4U_diag χ a ⟨j.val, by have := j.isLt; omega⟩ = χ (a j) := by
    simp [kd291_aux_T4U_diag]
  have hχ1 : χ (a j) = 1 := by
    apply Units.ext
    have h := hent ⟨j.val, by have := j.isLt; omega⟩
    rw [hd, h4] at h
    rw [Units.val_one]
    exact h.symm
  have hfin : a j = 1 := hχi (by rw [hχ1, map_one])
  exact hfin

theorem kd291_aux_T4U_dvd {p r f : ℕ} [Fact r.Prime] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (r ^ f) ^ 2) (hpq : p ∣ r ^ f + 1) : p ∣ Nat.card K - 1 := by
  have hq1 : 1 ≤ r ^ f := Nat.one_le_pow _ _ (Fact.out : r.Prime).pos
  rw [hK, CFSG.LocalAnalysis.RankFourTheoremC.od_sq_sub_one _ hq1]
  exact Dvd.dvd.mul_right hpq _

theorem kd291_aux_T4U_ker {p r f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) [Fact r.Prime] {K : Type}
    [Field K] [Finite K] [CharP K r]
    (hK : Nat.card K = (r ^ f) ^ 2) (hpq : p ∣ r ^ f + 1) (B : Uid (unitaryInvolution K r f) p) :
    l212in_suPhi hK B = 1 ↔ B ∈ CFSG.LocalAnalysis.RankFourTheoremC.odUZ K p r f :=
  (CFSG.LocalAnalysis.RankFourTheoremC.odFamily_unitary_of_inputs (n := p) (p := p)
    CFSG.LocalAnalysis.RankFourTheoremC.i294ODUnitaryTorus_holds
    CFSG.LocalAnalysis.RankFourTheoremC.i294ODUnitaryMonomial_holds
    hp hp5 (dvd_refl p) hp.pos hK hpq).ker_eq B

end KD291T4UAux

theorem kd291_unitary_torus4 {p r f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) [Fact r.Prime] {K : Type}
    [Field K] [Finite K] [CharP K r]
    (hK : Nat.card K = (r ^ f) ^ 2) (hpq : p ∣ r ^ f + 1) :
    ∃ F : (Fin 4 → Multiplicative (ZMod p)) →* Uid (unitaryInvolution K r f) p,
      Function.Injective (fun a => l212in_suPhi hK (F a)) := by
  obtain ⟨χ, hχi⟩ := kd291_aux_T4U_chi hp (kd291_aux_T4U_dvd hK hpq)
  have hχq : ∀ a : Multiplicative (ZMod p), χ a ^ (r ^ f + 1) = 1 := by
    intro a
    have hpa : χ a ^ p = 1 := by
      rw [← map_pow, kd291_aux_T4U_powp, map_one]
    obtain ⟨k, hk⟩ := hpq
    rw [hk, pow_mul, hpa, one_pow]
  let G0 := kd291_aux_T4U_hom (K := K) χ
  let F : (Fin 4 → Multiplicative (ZMod p)) →* Uid (unitaryInvolution K r f) p :=
    { toFun := fun a => ⟨G0 a, kd291_aux_T4U_mem (r := r) (f := f) χ hχq a⟩
      map_one' := Subtype.ext (map_one G0)
      map_mul' := fun a b => Subtype.ext (map_mul G0 a b) }
  refine ⟨F, ?_⟩
  refine (injective_iff_map_eq_one ((l212in_suPhi hK).comp F)).2 ?_
  intro a ha
  obtain ⟨c, hc⟩ := CFSG.LocalAnalysis.RankFourTheoremC.mem_odUZ.1
    ((kd291_aux_T4U_ker hp hp5 hK hpq (F a)).1 ha)
  exact kd291_aux_T4U_eq_one hp5 χ hχi a c hc

section KdIL
open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.LocalAnalysis.RankFourTheoremC (odFamily_linear l212in_projectiveSLEquivStated
  exists_cover_linear)

theorem kd291_lu_false_linear {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y]
    [Finite Y] (L : Subgroup Y) [L.Normal] (hq : CFSG.Open.IsQuasisimple ↥L)
    (hZp : IsPGroup p (center ↥L)) (hcen : centralizer (L : Set Y) = ⊥)
    (hperf : ∀ (N : Subgroup Y) [N.Normal], IsPGroup p (Y ⧸ N) → N = ⊤)
    (hY3 : Open.pRank p (⊤ : Subgroup Y) ≤ 3) {x : Y} (hx : orderOf x = p)
    (hx2 : Open.pRank p (centralizer ({x} : Set Y)) ≤ 2) {n : ℕ} {K : Type} [Field K] [Finite K]
    (hpn : p ∣ n) (hpK : p ∣ Nat.card K - 1)
    (e : ↥L ⧸ center ↥L ≃* StatedProj (StatedSL n K)) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · haveI := hq.2
      haveI : Subsingleton (StatedProj (StatedSL 0 K)) := inferInstance
      exact absurd e.injective.subsingleton (not_subsingleton _)
    · exact h
  have hn5 : 5 ≤ n := hp5.trans (Nat.le_of_dvd hn0 hpn)
  let e' : ↥L ⧸ center ↥L ≃* projectiveSL n K :=
    e.trans (l212in_projectiveSLEquivStated n K).symm
  obtain ⟨φ, hφ, hφπ⟩ := exists_cover_linear hp hp5 hGA hq hZp (by omega) e'
  have hF := odFamily_linear hp hp5 hpn hn0 hpK
  have hperfSL : Group.IsPerfect (SpecialLinearGroup (Fin n) K) :=
    LinearGroups.special_linear_isPerfect (by omega) (Or.inl (by omega))
  have hcZ : ∀ w ∈ (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range,
      ∀ B : GL (Fin n) K, (slConjugation n K (w * B)).toMonoidHom
        = (slConjugation n K B).toMonoidHom := by
    rintro w ⟨u, rfl⟩ B
    refine MonoidHom.ext fun g => ?_
    show slConjugation n K (GeneralLinearGroup.scalar (Fin n) u * B) g = slConjugation n K B g
    rw [map_mul, CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_scalar,
      one_mul]
  have hnp : n = p := by
    refine n_eq_p_of_cover (p := p) hp5 hpn hn0 L hperf hx hx2 hperfSL (proj n K)
      (fun B => (slConjugation n K B).toMonoidHom) (conjAut n K)
      (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range hF.central hF.comm_mem
      (fun B h => (hF.ker_eq B).1 h) e' φ hφπ (fun B s => (conjAut_proj B s).symm)
      hcZ (fun B hB => linear_torus hp hn5 hpK B hB)
      (fun hn B hBZ hnp => linear_mono hp hpK hn B hBZ hnp)
  subst n
  haveI : Group.IsPerfect ↥L := ⟨hq.1⟩
  exact kd291_lu_false_abs hp hp5 L hcen hperf hY3 hx hx2 hperfSL (proj p K)
    (fun B => (slConjugation p K B).toMonoidHom) (conjAut p K) GeneralLinearGroup.det
    (GeneralLinearGroup.scalar (Fin p) : Kˣ →* GL (Fin p) K).range hF e' φ hφπ
    (fun B s => (conjAut_proj B s).symm) hcZ (fun B hB => linear_torus hp hn5 hpK B hB)
    (kd291_linear_torus4 hp hp5 hpK)

end KdIL

theorem kd291_lu_false_unitary {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y]
    [Finite Y] (L : Subgroup Y) [L.Normal] (hq : CFSG.Open.IsQuasisimple ↥L)
    (hZp : IsPGroup p (center ↥L)) (hcen : centralizer (L : Set Y) = ⊥)
    (hperf : ∀ (N : Subgroup Y) [N.Normal], IsPGroup p (Y ⧸ N) → N = ⊤)
    (hY3 : Open.pRank p (⊤ : Subgroup Y) ≤ 3) {x : Y} (hx : orderOf x = p)
    (hx2 : Open.pRank p (centralizer ({x} : Set Y)) ≤ 2) {n r f : ℕ} [Fact r.Prime] {K : Type}
    [Field K] [Finite K] [CharP K r] (hpn : p ∣ n) (hK : Nat.card K = (r ^ f) ^ 2)
    (hpq : p ∣ r ^ f + 1) (e : ↥L ⧸ center ↥L ≃* StatedProj (StatedSU n (r ^ f) K)) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · haveI := hq.2
      haveI : Subsingleton (StatedProj (StatedSU 0 (r ^ f) K)) := inferInstance
      exact absurd e.injective.subsingleton (not_subsingleton _)
    · exact h
  have hn5 : 5 ≤ n := hp5.trans (Nat.le_of_dvd hn0 hpn)
  have hp2 : p ≠ 2 := by omega
  obtain ⟨φ, -, hφπ⟩ := exists_cover_unitary hp hp5 hGA hq hZp hn5 hK e
  have hF := odFamily_unitary_of_inputs i294ODUnitaryTorus_holds i294ODUnitaryMonomial_holds hp
    hp5 hpn hn0 hK hpq
  have hperfSU : Group.IsPerfect (StatedSU n (r ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK (by omega) (by
      intro h
      simp only [Prod.mk.injEq] at h
      omega)
  haveI : Group.IsPerfect ↥L := ⟨hq.1⟩
  have hcZ : ∀ w ∈ odUZ K n r f, ∀ B : Uid (unitaryInvolution K r f) n,
      (l212in_suConj hK (w * B)).toMonoidHom = (l212in_suConj hK B).toMonoidHom := by
    intro w hw B
    obtain ⟨u, hu⟩ := mem_odUZ.1 hw
    refine MonoidHom.ext fun g => Subtype.ext ?_
    show ((l212in_suConj hK (w * B) g : StatedSU n (r ^ f) K) : GL (Fin n) K) =
      ((l212in_suConj hK B g : StatedSU n (r ^ f) K) : GL (Fin n) K)
    rw [l212in_suConj_coe, l212in_suConj_coe, Subgroup.coe_mul, _root_.mul_inv_rev, ← hu]
    have hc := l212in_scalar_comm ((B : GL (Fin n) K) * (g : GL (Fin n) K) *
      (B : GL (Fin n) K)⁻¹) u
    calc Matrix.GeneralLinearGroup.scalar (Fin n) u * (B : GL (Fin n) K) * (g : GL (Fin n) K) *
          ((B : GL (Fin n) K)⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin n) u)⁻¹)
        = Matrix.GeneralLinearGroup.scalar (Fin n) u * ((B : GL (Fin n) K) * (g : GL (Fin n) K) *
            (B : GL (Fin n) K)⁻¹) * (Matrix.GeneralLinearGroup.scalar (Fin n) u)⁻¹ := by group
      _ = (B : GL (Fin n) K) * (g : GL (Fin n) K) * (B : GL (Fin n) K)⁻¹ := by
        rw [← hc, _root_.mul_inv_cancel_right]
  have htorus : ∀ B : Uid (unitaryInvolution K r f) n, B ^ p = 1 →
      ∃ F : (Fin 3 → Multiplicative (ZMod p)) →* StatedSU n (r ^ f) K,
        Function.Injective ((QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf
          (StatedSU n (r ^ f) K))).comp F) ∧ ∀ a, (l212in_suConj hK B).toMonoidHom (F a) = F a := by
    intro B hB
    have hBp : (B : GL (Fin n) K) ^ p = 1 := by
      have h1 := congrArg Subtype.val hB
      simpa using h1
    obtain ⟨F, hFi, hFc, hFs⟩ := i294ODUnitaryTorus_holds hp hn5 hK hpq (B : GL (Fin n) K) B.2
      hBp
    refine ⟨F, ?_, fun a => ?_⟩
    · rw [injective_iff_map_eq_one]
      intro y hy
      have h1 : F y ∈ (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf
          (StatedSU n (r ^ f) K))).ker := hy
      rw [QuotientGroup.ker_mk'] at h1
      exact (injective_iff_map_eq_one F).1 hFi y (hFs y (Subgroup.mem_subgroupOf.1 h1))
    · apply Subtype.ext
      show ((l212in_suConj hK B (F a) : StatedSU n (r ^ f) K) : GL (Fin n) K) =
        (F a : GL (Fin n) K)
      rw [l212in_suConj_coe, hFc a, _root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one]
  have hnp : n = p := by
    refine n_eq_p_of_cover hp5 hpn hn0 L hperf hx hx2 hperfSU
      (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (r ^ f) K)))
      (fun B => (l212in_suConj hK B).toMonoidHom) (l212in_suPhi hK) (odUZ K n r f) hF.central
      hF.comm_mem (fun B h => (hF.ker_eq B).1 h) e φ hφπ
      (fun B s => (l212in_suPhi_mk hK B s).symm) hcZ htorus (fun hn B hBZ hBnp => ?_)
    obtain ⟨c, hBp, hnpow⟩ := od_unitary_nonpower hn0 hp hp2 hK hpq hBZ hBnp
    obtain ⟨T, hTe, hTcard, hTnorm⟩ := i294ODUnitaryMonomial_holds hp hp2 hK hpq hn
      (B : GL (Fin n) K) B.2 c hBp hnpow
    refine ⟨T, hTe, hTcard, fun g hg => ?_⟩
    obtain ⟨g', hg', hgg'⟩ := hTnorm g hg
    have h : l212in_suConj hK B g = g' := Subtype.ext (by rw [l212in_suConj_coe]; exact hgg')
    show l212in_suConj hK B g ∈ T
    rw [h]
    exact hg'
  subst n
  exact kd291_lu_false_abs hp hp5 L hcen hperf hY3 hx hx2 hperfSU
    (QuotientGroup.mk' ((StatedScalars (Fin p) K).subgroupOf (StatedSU p (r ^ f) K)))
    (fun B => (l212in_suConj hK B).toMonoidHom) (l212in_suPhi hK) l212in_detU (odUZ K p r f) hF e φ
    hφπ (fun B s => (l212in_suPhi_mk hK B s).symm) hcZ htorus (kd291_unitary_torus4 hp hp5 hK hpq)

theorem kd291_not_lu {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y]
    [Finite Y] (L : Subgroup Y) [L.Normal] (hq : CFSG.Open.IsQuasisimple ↥L)
    (hZp : IsPGroup p (center ↥L)) (hcen : centralizer (L : Set Y) = ⊥)
    (hperf : ∀ (N : Subgroup Y) [N.Normal], IsPGroup p (Y ⧸ N) → N = ⊤)
    (hY3 : Open.pRank p (⊤ : Subgroup Y) ≤ 3) {x : Y} (hx : orderOf x = p)
    (hx2 : Open.pRank p (centralizer ({x} : Set Y)) ≤ 2) :
    ¬ IsLinearOrUnitaryAt p (↥L ⧸ center ↥L) := by
  intro hlu
  haveI : Fact p.Prime := ⟨hp⟩
  rcases hlu with ⟨n, K, _, _, hpn, hpK, ⟨e⟩⟩ | ⟨n, q, K, _, _, hKq, hpn, hpq, ⟨e⟩⟩
  · exact kd291_lu_false_linear hp hp5 hGA L hq hZp hcen hperf hY3 hx hx2 hpn hpK e
  · obtain ⟨r, m, hr, hchar, -, hKr⟩ :=
      CFSG.LocalAnalysis.RankFourTheoremC.exists_char_pow_card K
    haveI : Fact r.Prime := ⟨hr⟩
    obtain ⟨f, -, hqf⟩ : ∃ f ≤ m, q = r ^ f := by
      refine (Nat.dvd_prime_pow hr).1 ?_
      rw [← hKr, hKq]
      exact dvd_pow_self q two_ne_zero
    subst hqf
    exact kd291_lu_false_unitary hp hp5 hGA L hq hZp hcen hperf hY3 hx hx2 hpn hKq hpq e

theorem kd291_aux_NLI_isLU_equiv {p : ℕ} {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : IsLinearOrUnitaryAt p X) : IsLinearOrUnitaryAt p X' := by
  rcases h with ⟨n, K, hF, hFin, hn, hK, ⟨f⟩⟩ | ⟨n, q, K, hF, hFin, hq, hn, hq1, ⟨f⟩⟩
  · exact Or.inl ⟨n, K, hF, hFin, hn, hK, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨n, q, K, hF, hFin, hq, hn, hq1, ⟨e.symm.trans f⟩⟩

theorem kd291_not_lu_of_center_bot {p : ℕ} {Y : Type} [Group Y] (L : Subgroup Y)
    (hZ : center ↥L = ⊥) (h : ¬ IsLinearOrUnitaryAt p (↥L ⧸ center ↥L)) :
    ¬ IsLinearOrUnitaryAt p ↥L := fun hlu =>
  h (kd291_aux_NLI_isLU_equiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm hlu)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
