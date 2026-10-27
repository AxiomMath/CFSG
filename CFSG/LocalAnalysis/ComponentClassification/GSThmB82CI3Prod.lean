module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4ProdL4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3Raw
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CI3Sub
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7TransL

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.HarrisLit.C3 InvClassL HBlocks
  CFSG.ComponentClassification.CatalogueBProjectiveInvolution
  CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open scoped MatrixGroups commutatorElement

theorem cfL43Prod {Y : Type} [Group Y] [Finite Y] (hL : Blueprint.LieModel Y .PSL 4 3 1)
    {t w : Y} (ht : orderOf t = 2) (hw : orderOf w = 2) (hwt : w ≠ t)
    {M : Subgroup Y} (hMt : M ≤ centralizer ({t} : Set Y))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set Y))))
    (hMty : IsSec8JType (↥M ⧸ pPrimeCore 2 ↥M) 3 1) (hwM : w ∈ M) :
    ∃ N : Subgroup Y, N ≤ centralizer ({t * w} : Set Y) ∧
      (N.subgroupOf (centralizer ({t * w} : Set Y))).IsSubnormal ∧ t * w ∈ N ∧
      Nonempty (↥N ≃* SL(2, ZMod 3)) := by
  classical
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hL
  let : Fintype F := Fintype.ofFinite F
  have hFq : Fintype.card F = 3 ^ 1 := by rw [Fintype.card_eq_nat_card, hF]
  have hF4 : Fintype.card F % 4 = 3 := by rw [hFq]; norm_num
  have hqodd : Odd (Fintype.card F) := by rw [hFq]; decide
  have hK2 : ringChar F ≠ 2 :=
    LieType.Steinberg.ringChar_ne_two_of_card_eq_pow Nat.prime_three (by norm_num) hF
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
  obtain ⟨-, ⟨s, hs, hs2, hsq, -, hsM⟩, -⟩ :=
    Cover82.jdata Nat.prime_three (by norm_num) le_rfl hMty
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
  have hneg : (negOne4 : SpecialLinearGroup (Fin 4) F) ∈
      center (SpecialLinearGroup (Fin 4) F) := by
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
    have hF'3 : Fintype.card F' = 3 := by rw [hF'c, hF, pow_one]
    exact ⟨X₁, h₁, hs₁, htwX, ⟨eN.trans (ClassicalModels.specialLinearFieldEquiv
      (ZMod.ringEquivOfPrime F' Nat.prime_three hF'3).symm (Fin 2))⟩⟩
  · exfalso
    have hdet1 : (l⁻¹ • (T : Matrix (Fin 4) (Fin 4) F)).det = 1 := by
      rw [Matrix.det_smul, T.2, mul_one, Fintype.card_fin, inv_pow,
        show l ^ 4 = (l ^ 2) ^ 2 by ring, ← hl1, one_pow, inv_one]
    rw [hdet1] at hdet'
    apply Ring.two_ne_zero hK2
    linear_combination hdet'
  · exact absurd ⟨1, (one_mul 1).symm⟩ hsq1

end CFSG.ComponentClassification.CatFactsL4U4

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped MatrixGroups

namespace Seven

variable {H : Type} [Group H] [Finite H]

theorem exists_lift_of_isSubnormal {u : H} (hu : u * u = 1)
    {Nb : Subgroup (H ⧸ pPrimeCore 2 H)}
    (hNb : Nb ≤ centralizer ({QuotientGroup.mk' (pPrimeCore 2 H) u} : Set (H ⧸ pPrimeCore 2 H)))
    (hNbs : (Nb.subgroupOf (centralizer ({QuotientGroup.mk' (pPrimeCore 2 H) u} :
      Set (H ⧸ pPrimeCore 2 H)))).IsSubnormal)
    (huNb : QuotientGroup.mk' (pPrimeCore 2 H) u ∈ Nb) (eNb : ↥Nb ≃* SL(2, ZMod 3)) :
    ∃ N : Subgroup H, N ≤ centralizer ({u} : Set H) ∧
      (N.subgroupOf (centralizer ({u} : Set H))).IsSubnormal ∧ u ∈ N ∧
      Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, ZMod 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 H) with hπ
  have hcen : (centralizer ({u} : Set H)).map π =
      centralizer ({π u} : Set (H ⧸ pPrimeCore 2 H)) :=
    (OddQuot.centralizer_singleton_map_eq (H := H) hu).symm
  set N := Nb.comap π ⊓ centralizer ({u} : Set H) with hN
  have hNC : N ≤ centralizer ({u} : Set H) := inf_le_right
  have huC : u ∈ centralizer ({u} : Set H) := mem_centralizer_singleton_iff.mpr rfl
  have hNmap : N.map π = Nb := by
    refine le_antisymm ((map_mono inf_le_left).trans (map_comap_le _ _)) fun x hx => ?_
    have hx' : x ∈ (centralizer ({u} : Set H)).map π := by
      rw [hcen]
      exact hNb hx
    obtain ⟨c, hc, rfl⟩ := hx'
    exact mem_map_of_mem _ (mem_inf.mpr ⟨mem_comap.mpr hx, hc⟩)
  set ψ : ↥(centralizer ({u} : Set H)) →* ↥(centralizer ({π u} : Set (H ⧸ pPrimeCore 2 H))) :=
    (π.comp (centralizer ({u} : Set H)).subtype).codRestrict _ (fun c => by
      rw [← hcen]
      exact mem_map_of_mem _ c.2) with hψ
  have hcomap : N.subgroupOf (centralizer ({u} : Set H)) =
      (Nb.subgroupOf (centralizer ({π u} : Set (H ⧸ pPrimeCore 2 H)))).comap ψ := by
    ext c
    simp only [mem_subgroupOf, mem_comap, hN, mem_inf, mem_comap]
    exact ⟨fun h => h.1, fun h => ⟨h, c.2⟩⟩
  refine ⟨N, hNC, ?_, mem_inf.mpr ⟨mem_comap.mpr huNb, huC⟩, ?_⟩
  · rw [hcomap]
    exact hNbs.comap ψ
  · obtain ⟨e₁⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv π OddQuot.not_two_dvd_card_ker N
    obtain ⟨e₂⟩ := HarrisLit.T1.P54.F3.nonempty_quot_equiv_of_equiv_sl2Three eNb
    exact ⟨e₁.trans ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (MulEquiv.subgroupCongr hNmap)).trans e₂)⟩

variable {X : Type} [Group X] [Finite X]

theorem exists_sl23_of_l43 {L J₀ Y : Subgroup X}
    (hLie : Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSL 4 3 1)
    {t w : X} (htL : t ∈ L) (ht : t * t = 1) (ht1 : t ≠ 1) (hw : w * w = 1) (hw1 : w ≠ 1)
    (htw : t * w = w * t) (hwt : w ≠ t) (hJ0L : J₀ ≤ L) (hJ0t : J₀ ≤ centralizer ({t} : Set X))
    (hYt : L ⊓ centralizer ({t} : Set X) ≤ Y) (hJ0pc : IsPComponent 2 (J₀.subgroupOf Y))
    (hJ0ty : IsSec8JType (↥J₀ ⧸ pPrimeCore 2 ↥J₀) 3 1) (hwJ0 : w ∈ J₀) :
    ∃ N : Subgroup X, N ≤ L ⊓ centralizer ({t * w} : Set X) ∧
      (N.subgroupOf (L ⊓ centralizer ({t * w} : Set X))).IsSubnormal ∧ t * w ∈ N ∧
      Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, ZMod 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hπ
  set t' : ↥L := ⟨t, htL⟩ with ht'
  set w' : ↥L := ⟨w, hJ0L hwJ0⟩ with hw'
  have ht'2 : t' * t' = 1 := Subtype.ext ht
  have hw'2 : w' * w' = 1 := Subtype.ext hw
  have ht'1 : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have hw'1 : w' ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
  have htw' : t' * w' = w' * t' := Subtype.ext htw
  have hJ0Lt : J₀ ≤ L ⊓ centralizer ({t} : Set X) := le_inf hJ0L hJ0t
  have hpc1 : IsPComponent 2 (J₀.subgroupOf (L ⊓ centralizer ({t} : Set X))) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_le hJ0Lt hYt hJ0pc
  have hpc2 : IsPComponent 2 ((J₀.subgroupOf L).subgroupOf (centralizer ({t'} : Set ↥L))) := by
    rw [← inf_centralizer_subgroupOf htL]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two).mpr hpc1
  have hMt : J₀.subgroupOf L ≤ centralizer ({t'} : Set ↥L) := by
    rw [← inf_centralizer_subgroupOf htL]
    intro v hv
    exact mem_subgroupOf.mpr (hJ0Lt (mem_subgroupOf.mp hv))
  obtain ⟨hMbt, hMbpc⟩ := isPComponent_centralizer_map ht'2 hMt hpc2
  have hMbty : IsSec8JType (↥((J₀.subgroupOf L).map π) ⧸
      pPrimeCore 2 ↥((J₀.subgroupOf L).map π)) 3 1 := by
    obtain ⟨e₁⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv π OddQuot.not_two_dvd_card_ker
      (J₀.subgroupOf L)
    let e₂ := UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe hJ0L)
    exact CatFactsL4U4.Cover82.isSec8JType_of_mulEquiv (e₁.symm.trans e₂).symm hJ0ty
  have hne : π w' ≠ π t' := by
    intro h
    have hinj := OddQuot.injOn_of_isPGroup (H := ↥L) (isPGroup_closure_pair hw'2 ht'2 htw'.symm)
    have := hinj (subset_closure (by simp)) (subset_closure (by simp)) h
    exact hwt (congrArg Subtype.val this)
  obtain ⟨Nb, hNbt, hNbs, htwNb, ⟨eNb⟩⟩ := CatFactsL4U4.cfL43Prod hLie
    (orderOf_mk_eq_two ht'2 ht'1) (orderOf_mk_eq_two hw'2 hw'1) hne hMbt hMbpc hMbty
    (mem_map_of_mem _ (mem_subgroupOf.mpr hwJ0))
  have htw'2 : t' * w' * (t' * w') = 1 := by
    rw [show t' * w' * (t' * w') = t' * (w' * t') * w' by group, ← htw',
      show t' * (t' * w') * w' = (t' * t') * (w' * w') by group, ht'2, hw'2, one_mul]
  have hπtw : π t' * π w' = π (t' * w') := (map_mul π t' w').symm
  rw [hπtw] at hNbt hNbs htwNb
  obtain ⟨N₁, hN₁C, hN₁s, htwN₁, ⟨eN₁⟩⟩ := exists_lift_of_isSubnormal htw'2 hNbt hNbs htwNb eNb
  set N := N₁.map L.subtype with hNdef
  have htwL : t * w ∈ L := mul_mem htL (hJ0L hwJ0)
  have hcenL : (L ⊓ centralizer ({t * w} : Set X)).subgroupOf L =
      centralizer ({t' * w'} : Set ↥L) := inf_centralizer_subgroupOf htwL
  have hCmap : (centralizer ({t' * w'} : Set ↥L)).map L.subtype =
      L ⊓ centralizer ({t * w} : Set X) := by
    rw [← hcenL, map_subgroupOf_eq_of_le inf_le_left]
  have hNX : N ≤ L ⊓ centralizer ({t * w} : Set X) := by
    rw [← hCmap]
    exact map_mono hN₁C
  refine ⟨N, hNX, ?_, ⟨t' * w', htwN₁, rfl⟩, ?_⟩
  · have h1 := Eight2.Three.open_map L.subtype (Eight2.Three.open_of_isSubnormal hN₁C hN₁s)
    rw [hCmap] at h1
    exact Eight2.Three.isSubnormal_of_open h1
  · let e₀ : ↥N ≃* ↥N₁ := (N₁.equivMapOfInjective L.subtype L.subtype_injective).symm
    exact ⟨(UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e₀).trans eN₁⟩

end Seven

end CFSG.ComponentClassification.GSThmB
