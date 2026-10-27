module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3H
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Cover82A
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Prod

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.HarrisLit.C3 InvClassL HBlocks
  CFSG.ComponentClassification.CatalogueBProjectiveInvolution
  CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open scoped MatrixGroups commutatorElement

namespace ProdL4U4

theorem comm_of_mk_mem_perfect {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hN : N ≤ center G) {k : G} {J' : Subgroup (G ⧸ N)}
    (hJ' : J' ≤ centralizer ({(k : G ⧸ N)} : Set (G ⧸ N))) (hJp : ⁅J', J'⁆ = J') {X : G}
    (hX : (X : G ⧸ N) ∈ J') : X * k = k * X := by
  have key : ⁅centralizer ({(k : G ⧸ N)} : Set (G ⧸ N)),
      centralizer ({(k : G ⧸ N)} : Set (G ⧸ N))⁆ ≤
      (centralizer ({k} : Set G)).map (QuotientGroup.mk' N) := by
    rw [commutator_le]
    intro u hu v hv
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective v
    have hA : A * k * A⁻¹ * k⁻¹ ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
        mem_centralizer_singleton_iff.mp hu]
      group
    have hB : B * k * B⁻¹ * k⁻¹ ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
        mem_centralizer_singleton_iff.mp hv]
      group
    exact ⟨⁅A, B⁆, mem_centralizer_singleton_iff.mpr (commutator_comm_of_comm_mod hN hA hB),
      map_commutatorElement (QuotientGroup.mk' N) A B⟩
  have hX' : (X : G ⧸ N) ∈ (centralizer ({k} : Set G)).map (QuotientGroup.mk' N) := by
    rw [← hJp] at hX
    exact key (commutator_mono hJ' hJ' hX)
  obtain ⟨Y, hY, hYX⟩ := hX'
  have hYX2 : (Y : G ⧸ N) = (X : G ⧸ N) := hYX
  have hc := mem_center_iff.mp (hN (QuotientGroup.eq.mp hYX2)) k
  have hYk : Y * k = k * Y := mem_centralizer_singleton_iff.mp hY
  calc X * k = Y * ((Y⁻¹ * X) * k) := by group
    _ = Y * (k * (Y⁻¹ * X)) := by rw [hc]
    _ = (Y * k) * (Y⁻¹ * X) := by group
    _ = k * X := by rw [hYk]; group

theorem five_le_pow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq3 : ¬ (p = 3 ∧ f = 1)) : 5 ≤ p ^ f := by
  have h3 : 3 ≤ p ^ f := Cover82.three_le_pow hp hp2 hf
  obtain ⟨k, hk⟩ : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  by_contra hlt
  have heq : p ^ f = 3 := by omega
  apply hq3
  have hpd : p ∣ 3 := by
    rw [← heq]
    exact dvd_pow_self p (by omega)
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpd
  subst hp3
  exact ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3)
    (show 3 ^ f = 3 ^ 1 by rw [heq, pow_one])⟩

theorem exists_of_isSubnormal_sl2_card {Y : Type} [Group Y] [Finite Y] {u : Y} (hu : u * u = 1)
    (hu1 : u ≠ 1) {N : Subgroup Y} (hNC : N ≤ centralizer ({u} : Set Y))
    (hNsn : (N.subgroupOf (centralizer ({u} : Set Y))).IsSubnormal) (huN : u ∈ N)
    {F : Type} [Field F] [Finite F] (hF2 : ringChar F ≠ 2) (hF4 : 4 ≤ Nat.card F)
    (eN : ↥N ≃* SL(2, F)) :
    IsPComponent 2 (N.subgroupOf (centralizer ({u} : Set Y))) ∧
      ∃ p' n : ℕ, ∃ _ : Fact p'.Prime, p' ≠ 2 ∧ 0 < n ∧
        Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, GaloisField p' n)) ∧ p' ^ n = Nat.card F := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
  have hNO : pPrimeCore 2 ↥N = ⊥ := by
    have h1 := pPrimeCore_map_iso 2 eN
    rw [CatFactsSp4.pPrimeCore_SL2 h2 hF4] at h1
    exact (map_eq_bot_iff_of_injective _ eN.injective).mp h1
  obtain ⟨p', n, hp', hp'2, hn, ⟨eK⟩, hpn⟩ := CatFactsSp4.exists_sl2_galoisField_card hF2
  refine ⟨?_, p', n, hp', hp'2, hn, ⟨(QuotientGroup.quotientMulEquivOfEq hNO).trans
    (QuotientGroup.quotientBot.trans (eN.trans eK))⟩, hpn⟩
  have hq : IsQuasisimple ↥(N.subgroupOf (centralizer ({u} : Set Y))) :=
    (isQuasisimple_congr ((subgroupOfEquivOfLe hNC).trans eN)).mpr
      (CatFactsSp4.isQuasisimple_SL2' hF4)
  refine isPComponent_of_isComponent_of_not_le 2 ⟨hq, hNsn⟩ fun hle => hu1 ?_
  have h3 : (⟨u, hNC huN⟩ : ↥(centralizer ({u} : Set Y))) ∈
      pPrimeCore 2 ↥(centralizer ({u} : Set Y)) := hle (mem_subgroupOf.mpr huN)
  exact congrArg Subtype.val (Cover82.eq_one_of_mem_pPrimeCore h3 (Subtype.ext hu))

end ProdL4U4

theorem cfL4U4Prod_L4 {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hq3 : ¬ (p = 3 ∧ f = 1)) (hL : Blueprint.LieModel Y .PSL 4 p f)
    (hq : p ^ f % 4 = 3) {t w : Y} (ht : orderOf t = 2) (hw : orderOf w = 2) (hwt : w ≠ t)
    {M : Subgroup Y} (hMt : M ≤ centralizer ({t} : Set Y))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set Y))))
    (hMLie : Blueprint.LieModel (↥M ⧸ pPrimeCore 2 ↥M) .PSL 2 p (2 * f)) (hwM : w ∈ M) :
    ∃ N : Subgroup Y, N ≤ centralizer ({t * w} : Set Y) ∧
      IsPComponent 2 (N.subgroupOf (centralizer ({t * w} : Set Y))) ∧ t * w ∈ N ∧
      ∃ p' n : ℕ, ∃ _ : Fact p'.Prime, p' ≠ 2 ∧ 0 < n ∧
        Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, GaloisField p' n)) ∧ p' ^ n = p ^ f := by
  classical
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hL
  let : Fintype F := Fintype.ofFinite F
  have hFq : Fintype.card F = p ^ f := by rw [Fintype.card_eq_nat_card, hF]
  have hF4 : Fintype.card F % 4 = 3 := by rw [hFq]; exact hq
  have hqodd : Odd (Fintype.card F) := by rw [hFq]; exact (hp.odd_of_ne_two hp2).pow
  have hK2 : ringChar F ≠ 2 := LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hF
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hw2 : w * w = 1 := by rw [← pow_two, ← hw, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hw
    omega
  have htw : t * w = w * t := (mem_centralizer_singleton_iff.mp (hMt hwM)).symm
  have htw1 : t * w ≠ 1 := by
    intro h1
    apply hwt
    rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right ht2]
  have htw2 : t * w * (t * w) = 1 := by
    calc t * w * (t * w) = t * (w * t) * w := by group
      _ = t * (t * w) * w := by rw [← htw]
      _ = (t * t) * (w * w) := by group
      _ = 1 := by rw [ht2, hw2, one_mul]
  obtain ⟨-, ⟨s, hs, hs2, hsq, -, hsM⟩, -⟩ := Cover82.jdata hp hp2 hf (Or.inl hMLie)
  have := Fact.mk hs
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) s hsM
  have hMp : ⁅M, M⁆ = M := commutator_eq_self_of_isPComponent hMt hM
  have hu1 : e t ≠ 1 := by rw [Ne, MulEquiv.map_eq_one_iff]; exact ht1
  have hu2 : e t ^ 2 = 1 := by rw [← map_pow, sq, ht2, map_one]
  have hv' : orderOf (e (v : Y)) = s := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hv]
  have huv : e t * e (v : Y) = e (v : Y) * e t := by
    rw [← map_mul, ← map_mul, (mem_centralizer_singleton_iff.mp (hMt v.2)).symm]
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e t)
  have hkk := sq_eq_neg_one_of_comm_orderOf hqodd hu1 hu2 hs hs2 (by rw [hFq]; exact hsq) hv'
    huv k hk
  have hJ'k : M.map e.toMonoidHom ≤
      centralizer {(QuotientGroup.mk k : StatedProj (StatedSL 4 F))} := by
    rintro _ ⟨m, hm, rfl⟩
    rw [mem_centralizer_singleton_iff, hk]
    change e m * e t = e t * e m
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp (hMt hm)]
  have hJ'p : ⁅M.map e.toMonoidHom, M.map e.toMonoidHom⁆ = M.map e.toMonoidHom := by
    rw [← map_commutator, hMp]
  have hw'J : e w ∈ M.map e.toMonoidHom := mem_map_of_mem _ hwM
  have hw'2 : e w * e w = 1 := by rw [← map_mul, hw2, map_one]
  have hw'1 : e w ≠ 1 := by rw [Ne, MulEquiv.map_eq_one_iff]; exact hw1
  obtain ⟨X, hXw, hXX⟩ :=
    exists_lift_sq_eq_neg_one_of_perfect hF4 k hkk hJ'k hJ'p hw'J hw'2 hw'1
  have hNc : (StatedScalars (Fin 4) F).subgroupOf (StatedSL 4 F) ≤ center ↥(StatedSL 4 F) := by
    intro z hz
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    have hz' : (z : GL (Fin 4) F) ∈ center (GL (Fin 4) F) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact hz
    exact mem_center_iff.mp hz' g
  have hXk : X * k = k * X :=
    ProdL4U4.comm_of_mk_mem_perfect hNc hJ'k hJ'p (by rw [hXw]; exact hw'J)
  set Km := ((k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hKm
  set Xm := ((X : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hXm
  have hXk' : Xm * Km = Km * Xm := by
    have h1 := congrArg (fun A : ↥(StatedSL 4 F) => ((A : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F)) hXk
    simpa using h1
  have hdet : (Km * Xm).det = 1 := by
    rw [det_mul, det_eq_one_of_mem_statedSL k.2, det_eq_one_of_mem_statedSL X.2, mul_one]
  set T : SpecialLinearGroup (Fin 4) F := ⟨Km * Xm, hdet⟩ with hT
  have hTT : (T : Matrix (Fin 4) (Fin 4) F) * T = (1 : F) • 1 := by
    rw [one_smul]
    change Km * Xm * (Km * Xm) = 1
    calc Km * Xm * (Km * Xm) = Km * (Xm * Km) * Xm := by simp only [Matrix.mul_assoc]
      _ = Km * (Km * Xm) * Xm := by rw [hXk']
      _ = Km * Km * (Xm * Xm) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hkk, hXX, neg_mul_neg, Matrix.one_mul]
  set θ₀ : SpecialLinearGroup (Fin 4) F →* StatedProj (StatedSL 4 F) :=
    (QuotientGroup.mk' ((StatedScalars (Fin 4) F).subgroupOf (StatedSL 4 F))).comp
      (specialLinearGroupEquivStatedSL 4 F).toMonoidHom with hθ₀
  set θ : SpecialLinearGroup (Fin 4) F →* ↥(⊤ : Subgroup Y) :=
    (Subgroup.topEquiv.symm.toMonoidHom).comp (e.symm.toMonoidHom.comp θ₀) with hθ
  have hθs : Function.Surjective θ :=
    Subgroup.topEquiv.symm.surjective.comp (e.symm.surjective.comp
      ((QuotientGroup.mk'_surjective _).comp (specialLinearGroupEquivStatedSL 4 F).surjective))
  have hθθ₀ : ∀ s, θ s = 1 ↔ θ₀ s = 1 := by
    intro s
    change Subgroup.topEquiv.symm (e.symm (θ₀ s)) = 1 ↔ θ₀ s = 1
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
  have hθ₀c : ∀ s, θ₀ s = 1 ↔ s ∈ center (SpecialLinearGroup (Fin 4) F) := by
    intro s
    change QuotientGroup.mk' _ (specialLinearGroupEquivStatedSL 4 F s) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← map_center_eq_statedScalars 4 F,
      mem_map]
    constructor
    · rintro ⟨s', hs', hss'⟩
      rwa [(specialLinearGroupEquivStatedSL 4 F).injective hss'] at hs'
    · intro hs
      exact ⟨s, hs, rfl⟩
  have hθk : θ.ker ≤ scalars 4 F := by
    intro s hs
    rw [scalars_eq_center]
    exact (hθ₀c s).mp ((hθθ₀ s).mp (MonoidHom.mem_ker.mp hs))
  have hneg : (negOne4 : SpecialLinearGroup (Fin 4) F) ∈ center (SpecialLinearGroup (Fin 4) F) := by
    rw [← scalars_eq_center, mem_scalars]
    refine ⟨-1, by norm_num, ?_⟩
    change (-1 : Matrix (Fin 4) (Fin 4) F) = scalar (Fin 4) ((-1 : Fˣ) : F)
    rw [Units.val_neg, Units.val_one, map_neg, map_one]
  have hθ1 : θ negOne4 = 1 := (hθθ₀ _).mpr ((hθ₀c _).mpr hneg)
  have hιT : specialLinearGroupEquivStatedSL 4 F T = k * X := by
    apply Subtype.ext
    apply Units.ext
    rw [specialLinearGroupEquivStatedSL_coe, Subgroup.coe_mul, Units.val_mul]
  have hθT : ((θ T : ↥(⊤ : Subgroup Y)) : Y) = t * w := by
    change ((Subgroup.topEquiv.symm (e.symm (QuotientGroup.mk
      (specialLinearGroupEquivStatedSL 4 F T))) : ↥(⊤ : Subgroup Y)) : Y) = t * w
    rw [hιT, QuotientGroup.mk_mul, hk, hXw, ← map_mul, MulEquiv.symm_apply_apply]
    rfl
  have hns : ∀ a : F, (T : Matrix (Fin 4) (Fin 4) F) ≠ a • 1 := by
    intro a ha
    have ha4 : a ^ 4 = 1 := by
      have h1 := T.2
      rw [ha, det_smul, det_one, mul_one, Fintype.card_fin] at h1
      exact h1
    have ha0 : a ≠ 0 := by
      rintro rfl
      norm_num at ha4
    have hTs : T ∈ center (SpecialLinearGroup (Fin 4) F) := by
      rw [← scalars_eq_center, mem_scalars]
      refine ⟨Units.mk0 a ha0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, ha4,
        Units.val_one]), ?_⟩
      rw [ha, Units.val_mk0, scalar_apply, smul_one_eq_diagonal]
    have h1 : θ T = 1 := (hθθ₀ _).mpr ((hθ₀c _).mpr hTs)
    apply htw1
    rw [← hθT, h1]
    rfl
  obtain ⟨l, hl0, hl1, -, P, hP⟩ | ⟨l, hl0, hl1, hdet', -⟩ | ⟨hsq1, -⟩ :=
    classify_inv hK2 hTT one_ne_zero hns
  · have hl : l = 1 ∨ l = -1 := by
      have : l * l = 1 := by rw [← sq, ← hl1]
      exact mul_self_eq_one_iff.mp this
    have htP : (T : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) =
        (P : Matrix (Fin 4) (Fin 4) F) * X1 l := by
      rw [X1_eq_smul l, Matrix.mul_smul, ← hP, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hl0,
        one_smul]
    set θ' := θ.comp (CatalogueBHigherLinearAction.slConjugation 4 F P).toMonoidHom with hθ'
    set t₀ := CatalogueBHigherLinearAction.slConjugation 4 F P⁻¹ T with ht₀
    have ht₀X : (t₀ : Matrix (Fin 4) (Fin 4) F) = X1 l := by
      rw [ht₀, coe_slConjugation, inv_inv, Matrix.mul_assoc, htP, ← Matrix.mul_assoc,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    have hθ't : θ' t₀ = θ T := by
      rw [hθ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ht₀, ← MulAut.mul_apply,
        ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    have hθ's : Function.Surjective θ' := hθs.comp (MulEquiv.surjective _)
    have hθ'k : θ'.ker ≤ scalars 4 F := fun s hs =>
      mem_scalars_of_slConjugation_mem (hθk hs)
    have hθ'1 : θ' negOne4 = 1 := by
      rw [hθ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, slConjugation_mem_center hneg,
        hθ1]
    obtain ⟨X₁, X₂, -, h₁, -, hs₁, -, -, hi, ⟨F', _, _, hF'c, ⟨eN⟩⟩, -⟩ :=
      x_alternative hK2 hθ's hθ'k hθ'1 hl ht₀X
    rw [hθ't, hθT, top_inf_eq] at h₁ hs₁
    rw [hθ't, hθT] at hi
    have htwX : t * w ∈ X₁ := by
      have h1 : t * w ∈ X₁ ⊓ X₂ := by
        rw [hi]
        exact mem_zpowers _
      exact (mem_inf.mp h1).1
    have hF'n : Nat.card F' = p ^ f := by rw [Nat.card_eq_fintype_card, hF'c, hF]
    obtain ⟨hpc, p', n, hp', hp'2, hn, he, hpn⟩ := ProdL4U4.exists_of_isSubnormal_sl2_card htw2
      htw1 h₁ hs₁ htwX (LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hF'n)
      (by rw [hF'n]; exact (ProdL4U4.five_le_pow hp hp2 hf hq3).trans' (by norm_num)) eN
    exact ⟨X₁, h₁, hpc, htwX, p', n, hp', hp'2, hn, he, hpn.trans hF'n⟩
  · exfalso
    have hdet1 : (l⁻¹ • (T : Matrix (Fin 4) (Fin 4) F)).det = 1 := by
      rw [Matrix.det_smul, T.2, mul_one, Fintype.card_fin, inv_pow,
        show l ^ 4 = (l ^ 2) ^ 2 by ring, ← hl1, one_pow, inv_one]
    rw [hdet1] at hdet'
    apply Ring.two_ne_zero hK2
    linear_combination hdet'
  · exact absurd ⟨1, (one_mul 1).symm⟩ hsq1

end CFSG.ComponentClassification.CatFactsL4U4
