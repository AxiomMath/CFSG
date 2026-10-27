module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinAbs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MICore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSimple
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB1
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangChev
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Final
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeAFinal
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24LeafShape
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3All
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Easy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporCheck
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporCo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporFi23
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporFiveB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHN3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHe3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporJ3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporLy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRu3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporSuz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporTh
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1ThreeTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZCo1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZMathHS1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZSpor
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K14ChevFacts
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporFi24
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporHe7
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriLHolds
public import Certificates.Data.TabCo1ThreeE
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcomp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.StandardType.RecipeExcLang
open scoped commutatorElement

@[expose] def l154ExcUntw : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .E6 q => q.p = 2 | .E7 q => q.p = 2 | .E8 q => q.p = 2 | .F4 q => q.p = 2 | .G2 q => q.p = 2
    | _ => False

theorem excUntw_exists_frob_pow {K : Type} [Field K] {ℓ f p : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    ∃ (e k : ℕ) (T : K ≃+* K), e * p = f ∧ 1 ≤ e ∧ (∀ c, T c = c ^ (ℓ ^ e)) ∧ σ ^ k = T ∧
      Nat.Coprime k p := by
  classical
  obtain ⟨φ, hφ, hφord, hφtop, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ hf hK
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨φ, hφtop⟩
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hpf : p ∣ f := by
    rw [← hσ, ← hcardAut]
    exact orderOf_dvd_natCard σ
  obtain ⟨e, he⟩ := hpf
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, mul_zero] at he
      omega
    · exact h
  have hep : e * p = f := by rw [he, mul_comm]
  set T := φ ^ e with hTdef
  have hφpow : ∀ (n : ℕ) (c : K), (φ ^ n) c = c ^ (ℓ ^ n) := by
    intro n
    induction n with
    | zero => intro c; simp
    | succ n ih =>
      intro c
      rw [pow_succ, RingAut.mul_apply, ih, hφ, ← pow_mul, pow_succ' ℓ n]
  have hT : ∀ c, T c = c ^ (ℓ ^ e) := hφpow e
  have hg : Nat.gcd f e = e := by
    rw [← hep]
    exact Nat.gcd_eq_right (Dvd.intro p rfl)
  have hTord : orderOf T = p := by
    rw [hTdef, orderOf_pow' φ (by omega), hφord, hg, ← hep]
    exact Nat.mul_div_cancel_left p (by omega)
  have hzz : Subgroup.zpowers T = Subgroup.zpowers σ :=
    (IsCyclic.subgroup_eq_iff_card_eq).2 (by rw [Nat.card_zpowers, Nat.card_zpowers, hTord, hσ])
  obtain ⟨k, hk⟩ : ∃ k : ℕ, σ ^ k = T := by
    have h : T ∈ Subgroup.zpowers σ := hzz ▸ Subgroup.mem_zpowers T
    rw [← mem_powers_iff_mem_zpowers] at h
    exact h
  refine ⟨e, k, T, hep, he1, hT, hk, ?_⟩
  refine ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hdvd => ?_).symm
  have h1 : σ ^ k = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hσ]; exact hdvd)
  rw [hk] at h1
  rw [h1, orderOf_one] at hTord
  exact hp.one_lt.ne hTord

theorem excUntw_induces_trans {L R R' : Type} [Group L] [Group R] [Group R']
    {rel : L → L → Prop} (θ : L ⧸ Subgroup.center L ≃* R) (e : R ≃* R') {φ : MulAut R}
    (h : LargeEvenInduces θ rel φ) : LargeEvenInduces (θ.trans e) rel (MulAut.congr e φ) := by
  intro l l' hl
  have h1 := h l l' hl
  simp only [MulEquiv.trans_apply, MulAut.congr_apply, MulEquiv.symm_apply_apply, h1]

theorem excUntw_induces_conj {L R : Type} [Group L] [Group R] {rel : L → L → Prop}
    (θ : L ⧸ Subgroup.center L ≃* R) (ι : MulAut R) {φ : MulAut R}
    (h : LargeEvenInduces θ rel φ) : LargeEvenInduces (θ.trans ι) rel (ι * φ * ι⁻¹) := by
  intro l l' hl
  have h1 := h l l' hl
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  change ι (φ (ι⁻¹ (ι (θ (QuotientGroup.mk l))))) = _
  rw [show ι⁻¹ (ι (θ (QuotientGroup.mk l))) = θ (QuotientGroup.mk l) from
    MulEquiv.symm_apply_apply _ _, h1]

theorem excUntw_indAut_pow {p : ℕ} {Ω : Type} [Group Ω] {S : Subgroup Ω} {y : Ω}
    (hy : y ∈ Subgroup.normalizer (S : Set Ω)) (k : ℕ)
    (hk : y ^ k ∈ Subgroup.normalizer (S : Set Ω)) :
    MI.indAut p S (y ^ k) hk = MI.indAut p S y hy ^ k := by
  unfold MI.indAut
  rw [← map_pow]
  congr 1
  exact Subtype.ext (by simp [inv_pow])

theorem excUntw_induces_pow {p : ℕ} {Ω : Type} [Group Ω] {S : Subgroup Ω} {y : Ω}
    (hy : y ∈ Subgroup.normalizer (S : Set Ω)) {R : Type} [Group R]
    (θ : PSimple p S ≃* R) {φ : MulAut R} (h : LargeEvenInduces θ (indRel p S y) φ) (k : ℕ) :
    LargeEvenInduces θ (indRel p S (y ^ k)) (φ ^ k) := by
  have hk : y ^ k ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.pow_mem _ hy k
  rw [MI.induces_indRel_iff hk θ, (MI.induces_indRel_iff hy θ).1 h, excUntw_indAut_pow hy k hk,
    map_pow]

theorem excUntw_induces_commute {p : ℕ} {Ω : Type} [Group Ω] {S : Subgroup Ω} {x y : Ω}
    (hx : x ∈ Subgroup.normalizer (S : Set Ω)) (hy : y ∈ Subgroup.normalizer (S : Set Ω))
    (hxy : x * y = y * x) {R : Type} [Group R] (θ : PSimple p S ≃* R) {φx φy : MulAut R}
    (hix : LargeEvenInduces θ (indRel p S x) φx) (hiy : LargeEvenInduces θ (indRel p S y) φy) :
    φx * φy = φy * φx := by
  rw [(MI.induces_indRel_iff hx θ).1 hix, (MI.induces_indRel_iff hy θ).1 hiy, ← map_mul, ← map_mul]
  congr 1
  unfold MI.indAut
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext
    (show x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ from (Commute.inv_inv (show Commute x y from hxy)).eq)

theorem excUntw_induces_pow_eq_one {p : ℕ} {Ω : Type} [Group Ω] {S : Subgroup Ω} {x : Ω}
    (hx : x ∈ Subgroup.normalizer (S : Set Ω)) (hxp : x ^ p = 1) {R : Type} [Group R]
    (θ : PSimple p S ≃* R) {φ : MulAut R} (h : LargeEvenInduces θ (indRel p S x) φ) :
    φ ^ p = 1 := by
  rw [(MI.induces_indRel_iff hx θ).1 h, ← map_pow, l154_indAut_pow_eq_one hx hxp, map_one]

theorem excUntw_chev_transport {τ : Tag} {K : Type} [Field K] {Q : LargeEvenRawCont}
    (h : Q (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))
      (LargeEvenChevIDImage τ.cartan K _) (LargeEvenChevFieldImage τ.cartan K _)) :
    Q (LargeEvenCenterQuot (adjointGroup τ K)) (markIDImage (IsRoot τ) K (adjointGroup τ K))
      (RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K)) := by
  have h1 : ∀ H : Subgroup (LargeEvenChevGL τ.cartan K),
      H = MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false →
      Q (LargeEvenCenterQuot H) (LargeEvenChevIDImage τ.cartan K H)
        (LargeEvenChevFieldImage τ.cartan K H) →
      Q (LargeEvenCenterQuot (MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false))
        (markIDImage (LargeEvenIsRoot τ.cartan) K
          (MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false))
        (RecipeFieldExcInn.markFieldImage (LargeEvenIsRoot τ.cartan) K
          (MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false)) := by
    intro H hH hQ
    subst hH
    rw [largeEvenChevIDImage_eq] at hQ
    exact hQ
  have h2 := h1 _ (largeEvenChevH_eq τ.cartan K false) h
  have h3 : ∀ S : (Fin τ.rank → ℤ) → Prop, LargeEvenIsRoot τ.cartan = S →
      Q (LargeEvenCenterQuot (MarkChev.chevH τ.cartan S K false))
        (markIDImage S K (MarkChev.chevH τ.cartan S K false))
        (RecipeFieldExcInn.markFieldImage S K (MarkChev.chevH τ.cartan S K false)) := by
    intro S hS
    subst hS
    exact h2
  suffices key : ∀ A : Subgroup (ModGL τ K), A = MarkChev.chevH τ.cartan (IsRoot τ) K false →
      Q (LargeEvenCenterQuot A) (markIDImage (IsRoot τ) K A)
        (RecipeFieldExcInn.markFieldImage (IsRoot τ) K A) from
    key _ (chevH_false_eq_adjointGroup K τ).symm
  intro A hA
  subst hA
  exact h3 _ (largeEvenIsRoot_eq_isRoot τ)

theorem excUntw_raw_of_label {lab : GLALabel}
    (htag : lab.tag = .G2 ∨ lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
    {Q : LargeEvenRawCont} (h : CFSG.Assembly.LargeEvenRawDatum lab Q) :
    ∃ (τ : Tag) (K : Type) (_ : Field K) (_ : Finite K),
      (τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) ∧ Nat.card K = 2 ^ lab.n ∧
      Q (LargeEvenCenterQuot (adjointGroup τ K)) (markIDImage (IsRoot τ) K (adjointGroup τ K))
        (RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K)) := by
  obtain ⟨t, l, n⟩ := lab
  rcases htag with ht | ht | ht | ht | ht <;> dsimp only at ht <;> subst ht
  · obtain ⟨K, instF, instFin, hK, hQ⟩ := h
    exact ⟨.G2, K, instF, instFin, Or.inl rfl, hK, excUntw_chev_transport hQ⟩
  · obtain ⟨K, instF, instFin, hK, hQ⟩ := h
    exact ⟨.F4, K, instF, instFin, Or.inr (Or.inl rfl), hK, excUntw_chev_transport hQ⟩
  · obtain ⟨K, instF, instFin, hK, hQ⟩ := h
    exact ⟨.E6, K, instF, instFin, Or.inr (Or.inr (Or.inl rfl)), hK, excUntw_chev_transport hQ⟩
  · obtain ⟨K, instF, instFin, hK, hQ⟩ := h
    exact ⟨.E7, K, instF, instFin, Or.inr (Or.inr (Or.inr (Or.inl rfl))), hK,
      excUntw_chev_transport hQ⟩
  · obtain ⟨K, instF, instFin, hK, hQ⟩ := h
    exact ⟨.E8, K, instF, instFin, Or.inr (Or.inr (Or.inr (Or.inr rfl))), hK,
      excUntw_chev_transport hQ⟩

theorem excUntw_tag_of_markTag {lab : GLALabel} {t : StatedLieTag}
    (ht : t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) (h : markTag lab = t) :
    lab.tag = .G2 ∨ lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 := by
  obtain ⟨tg, r, n⟩ := lab
  unfold CFSG.StandardType.markTag at h
  cases tg <;> simp only at h ⊢ <;> (try split_ifs at h) <;> subst h <;> simp at ht ⊢

section Model

theorem excUntw_eq_one_of_inndiagConj {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK4 : 4 ≤ Nat.card K) {z : inndiagGroup τ K} (hz : inndiagConj τ K z = 1) : z = 1 := by
  refine Subtype.ext (eq_one_of_commute_adjointGroup hK4 z.2 fun c hc => ?_)
  have h := congrArg (fun φ : MulAut ↥(adjointGroup τ K) =>
    ((φ ⟨c, hc⟩ : adjointGroup τ K) : ModGL τ K)) hz
  simp only [coe_inndiagConj, MulAut.one_apply] at h
  calc (z : ModGL τ K) * c = ((z : ModGL τ K) * c * (z : ModGL τ K)⁻¹) * z := by group
    _ = c * z := by rw [h]

theorem excUntw_entrywise_mul_conj {τ : Tag} {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (w : inndiagGroup τ K) :
    entrywiseAdjointAut τ σ * inndiagConj τ K w =
      inndiagConj τ K (inndiagFieldAut τ K σ w) * entrywiseAdjointAut τ σ := by
  refine MulEquiv.ext fun c => Subtype.ext ?_
  simp only [MulAut.mul_apply, coe_entrywiseAdjointAut, coe_inndiagConj, coe_inndiagFieldAut,
    map_mul, map_inv]

theorem excUntw_fix_of_commute {τ : Tag} {K : Type} [Field K] [Finite K] (hK4 : 4 ≤ Nat.card K)
    (σ : K ≃+* K) (w : inndiagGroup τ K)
    (hc : inndiagConj τ K w * entrywiseAdjointAut τ σ =
      entrywiseAdjointAut τ σ * inndiagConj τ K w) : inndiagFieldAut τ K σ w = w := by
  have h1 := excUntw_entrywise_mul_conj (τ := τ) σ w
  have h2 : inndiagConj τ K (inndiagFieldAut τ K σ w) = inndiagConj τ K w := by
    refine mul_right_cancel (b := entrywiseAdjointAut τ σ) ?_
    rw [← h1, ← hc]
  have h3 : inndiagConj τ K (w⁻¹ * inndiagFieldAut τ K σ w) = 1 := by
    rw [map_mul, map_inv, h2, inv_mul_cancel]
  exact (inv_mul_eq_one.1 (excUntw_eq_one_of_inndiagConj hK4 h3)).symm

theorem excUntw_pow_eq_one_of_induces {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK4 : 4 ≤ Nat.card K) {p : ℕ} {Ω : Type} [Group Ω] {S : Subgroup Ω} {x : Ω}
    (hx : x ∈ Subgroup.normalizer (S : Set Ω)) (hxp : x ^ p = 1)
    (θ : PSimple p S ≃* ↥(adjointGroup τ K)) {w : inndiagGroup τ K}
    (h : LargeEvenInduces θ (indRel p S x) (inndiagConj τ K w)) : w ^ p = 1 :=
  excUntw_eq_one_of_inndiagConj hK4 (by rw [map_pow]; exact excUntw_induces_pow_eq_one hx hxp θ h)

theorem excUntw_data_of_induces {τ : Tag} {K : Type} [Field K] [Finite K] {n p : ℕ} (hp : p.Prime)
    (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {Ω : Type} [Group Ω] {S : Subgroup Ω} {x y : Ω}
    (hxN : x ∈ Subgroup.normalizer (S : Set Ω)) (hyN : y ∈ Subgroup.normalizer (S : Set Ω))
    (hxp : x ^ p = 1) (hxy : x * y = y * x) (θ : PSimple p S ≃* ↥(adjointGroup τ K))
    (w : inndiagGroup τ K) (σ : K ≃+* K) (hσ : orderOf σ = p)
    (hix : LargeEvenInduces θ (indRel p S x) (inndiagConj τ K w))
    (hiy : LargeEvenInduces θ (indRel p S y) (entrywiseAdjointAut τ σ)) :
    ∃ (e k : ℕ) (φx φy : MulAut ↥(adjointGroup τ K)) (h : ModGL τ K) (T : K →+* K),
      1 ≤ e ∧ Nat.card K = 2 ^ (e * p) ∧ (∀ c, T c = c ^ (2 ^ e)) ∧
      h ∈ inndiagGroup τ K ∧ h ^ p = 1 ∧ Units.map (entrywiseHom T) h = h ∧
      baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈ adjointGroup τ (AlgebraicClosure K) ∧
      Nat.Coprime k p ∧ (∀ c, (φx c : ModGL τ K) = h * c * h⁻¹) ∧
      (∀ c, (φy c : ModGL τ K) = Units.map (entrywiseHom T) c) ∧
      LargeEvenInduces θ (indRel p S x) φx ∧ LargeEvenInduces θ (indRel p S (y ^ k)) φy := by
  obtain ⟨e, k, T, hep, he1, hT, hk, hcop⟩ := excUntw_exists_frob_pow Nat.prime_two hn hK hp σ hσ
  have hK4 : 4 ≤ Nat.card K := by
    have h2 : 2 ≤ n := by
      have := Nat.mul_le_mul he1 hp.two_le
      omega
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
  have hiy' : LargeEvenInduces θ (indRel p S (y ^ k)) (entrywiseAdjointAut τ T) := by
    rw [← hk, entrywiseAdjointAut_pow]
    exact excUntw_induces_pow hyN θ hiy k
  have hyk : y ^ k ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.pow_mem _ hyN k
  have hcomm := excUntw_induces_commute hxN hyk
    (Commute.pow_right (show Commute x y from hxy) k).eq θ hix hiy'
  have hfix := excUntw_fix_of_commute hK4 T w hcomm
  have hwp := excUntw_pow_eq_one_of_induces hK4 hxN hxp θ hix
  refine ⟨e, k, inndiagConj τ K w, entrywiseAdjointAut τ T, (w : ModGL τ K), T.toRingHom, he1,
    by rw [hK, hep], hT, w.2, ?_, ?_, baseChangeGL_mem_adjointGroup_of_mem_inndiag _ w.2, hcop,
    fun c => coe_inndiagConj w c, fun c => coe_entrywiseAdjointAut τ T c, hix, hiy'⟩
  · rw [← Subgroup.coe_pow, hwp]
    rfl
  · have h1 := congrArg Subtype.val hfix
    rwa [coe_inndiagFieldAut] at h1

theorem excUntw_normalize {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ} (hr : 0 < τ.rank)
    {Ω : Type} [Group Ω] {S : Subgroup Ω} {x y : Ω}
    (θ₀ : PSimple p S ≃* LargeEvenCenterQuot (adjointGroup τ K))
    {φx f u : MulAut (LargeEvenCenterQuot (adjointGroup τ K))}
    (hφx : φx ∈ markIDImage (IsRoot τ) K (adjointGroup τ K))
    (hf : f ∈ RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K))
    (hu : u ∈ markIDImage (IsRoot τ) K (adjointGroup τ K)) (hord : orderOf f = p)
    (hix : LargeEvenInduces θ₀ (indRel p S x) φx)
    (hiy : LargeEvenInduces θ₀ (indRel p S y) (u * f * u⁻¹)) :
    ∃ (θ : PSimple p S ≃* ↥(adjointGroup τ K)) (w : inndiagGroup τ K) (σ : K ≃+* K),
      orderOf σ = p ∧ LargeEvenInduces θ (indRel p S x) (inndiagConj τ K w) ∧
      LargeEvenInduces θ (indRel p S y) (entrywiseAdjointAut τ σ) := by
  obtain ⟨wx, hwx⟩ := exists_inndiagConj_of_mem_markID hφx
  obtain ⟨w, hw⟩ := exists_inndiagConj_of_mem_markID hu
  obtain ⟨σ, hσ⟩ := autEquiv_eq_entrywise_of_mem_markField hf
  have hσp : orderOf σ = p := by
    rw [← CFSG.RankThree.Chevalley.SteinbergBT.orderOf_entrywiseAdjointAut hr σ, ← hσ,
      MulEquiv.orderOf_eq, hord]
  have h1x := excUntw_induces_trans θ₀ (centerQuotEquivOfBot center_adjointGroup_eq_bot) hix
  have h1y := excUntw_induces_trans θ₀ (centerQuotEquivOfBot center_adjointGroup_eq_bot) hiy
  change LargeEvenInduces _ _ (autEquiv τ K φx) at h1x
  change LargeEvenInduces _ _ (autEquiv τ K (u * f * u⁻¹)) at h1y
  have ey : autEquiv τ K (u * f * u⁻¹) =
      inndiagConj τ K w * entrywiseAdjointAut τ σ * (inndiagConj τ K w)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hw, hσ]
  rw [hwx] at h1x
  rw [ey] at h1y
  have h2x := excUntw_induces_conj _ (inndiagConj τ K w)⁻¹ h1x
  have h2y := excUntw_induces_conj _ (inndiagConj τ K w)⁻¹ h1y
  have e2x : (inndiagConj τ K w)⁻¹ * inndiagConj τ K wx * ((inndiagConj τ K w)⁻¹)⁻¹ =
      inndiagConj τ K (w⁻¹ * wx * w) := by
    rw [map_mul, map_mul, map_inv, inv_inv]
  have e2y : (inndiagConj τ K w)⁻¹ * (inndiagConj τ K w * entrywiseAdjointAut τ σ *
      (inndiagConj τ K w)⁻¹) * ((inndiagConj τ K w)⁻¹)⁻¹ = entrywiseAdjointAut τ σ := by
    group
  rw [e2x] at h2x
  rw [e2y] at h2y
  exact ⟨_, w⁻¹ * wx * w, σ, hσp, h2x, h2y⟩

end Model

section LieModel

theorem excUntw_exists_lieModel {X : Type} [Group X] (hQ : catalogIs X l154ExcUntw) :
    ∃ (t : StatedLieTag) (f : ℕ), (t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) ∧
      CFSG.Blueprint.LieModel X t 0 2 f := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hQ
  cases i with
  | cyclic p hp => simp [l154ExcUntw, onLie] at hi
  | alternating n hn => simp [l154ExcUntw, onLie] at hi
  | sporadic s => simp [l154ExcUntw, onLie] at hi
  | lie d =>
    obtain ⟨t, hv⟩ := d
    cases t with
    | G2 q =>
      have hp : q.p = 2 := by simpa [l154ExcUntw, onLie] using hi
      exact ⟨.G2, q.exponent, Or.inl rfl,
        hp ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_G2 q hv e⟩
    | F4 q =>
      have hp : q.p = 2 := by simpa [l154ExcUntw, onLie] using hi
      exact ⟨.F4, q.exponent, Or.inr (Or.inl rfl),
        hp ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_F4 q hv e⟩
    | E6 q =>
      have hp : q.p = 2 := by simpa [l154ExcUntw, onLie] using hi
      exact ⟨.E6, q.exponent, Or.inr (Or.inr (Or.inl rfl)),
        hp ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_E6 q hv e⟩
    | E7 q =>
      have hp : q.p = 2 := by simpa [l154ExcUntw, onLie] using hi
      exact ⟨.E7, q.exponent, Or.inr (Or.inr (Or.inr (Or.inl rfl))),
        hp ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_E7 q hv e⟩
    | E8 q =>
      have hp : q.p = 2 := by simpa [l154ExcUntw, onLie] using hi
      exact ⟨.E8, q.exponent, Or.inr (Or.inr (Or.inr (Or.inr rfl))),
        hp ▸ CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_E8 q hv e⟩
    | _ => simp [l154ExcUntw, onLie] at hi

end LieModel

section LabelR

theorem excUntw_tag_of_hasLabel (hR : GGLabelRigidInput) {X : Type} [Group X] (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) (hQ : catalogIs X l154ExcUntw) {labK : GLALabel}
    (hK : Y10F.HasLabel X (· = labK)) :
    labK.tag = .G2 ∨ labK.tag = .F4 ∨ labK.tag = .E6 ∨ labK.tag = .E7 ∨ labK.tag = .E8 := by
  have hcen : Subgroup.center X = ⊥ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.center_eq_bot_of_isSimpleGroup_of_noncomm hs hnab
  have hperf : commutator X = ⊤ := (K144I.openQuasisimple_of_simple hs hnab).1
  obtain ⟨i, hi, ⟨e⟩⟩ := hQ
  obtain ⟨t, f, ht, hm⟩ := excUntw_exists_lieModel
    ⟨i, hi, ⟨(CanonInn.quotCenterEquivOfBot hcen).trans e⟩⟩
  have hmark := Canonical.largeEvenMarking_of_lieModel_centerQuot hperf hm
  obtain ⟨lab, ⟨hlt, -, -, -⟩, hlab⟩ := K144I.exists_label_of_hasLabel hmark
  have hE := excUntw_tag_of_markTag ht hlt
  obtain ⟨hlam, -, hGlab⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hlab
  obtain ⟨hlamK, -, hGlabK⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hK
  have hE' : K1419E.ExcGLATag lab := by
    rcases hE with h | h | h | h | h <;> simp [K1419E.ExcGLATag, h]
  have heq := K1419E.eq_of_ggLabelIso_exc
    (hR lab labK (X ⧸ Subgroup.center X) hlam hlamK hGlab hGlabK) hE'
  rw [heq]
  exact hE

end LabelR

section LabelRG

theorem excUntw_tag_of_marking {p : ℕ} {Ω : Type} [Group Ω] {S : Subgroup Ω} {lab : GLALabel}
    (hlab : Y10F.HasLabel (PQuot p S) (· = lab)) (hQ : catalogIs (PSimple p S) l154ExcUntw) :
    lab.tag = .G2 ∨ lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 := by
  obtain ⟨hperf, hsimple⟩ := Y10F.hasLabel_isQuasisimple hlab
  haveI : IsSimpleGroup (PSimple p S) := hsimple
  exact excUntw_tag_of_hasLabel ggLabelRigidInput_holds this
    (exists_mul_ne_mul_centerQuot_of_perfect hperf inferInstance) hQ
    (Y10F.hasLabel_centerQuot hlab)

end LabelRG

section LabelU

theorem excUntw_raw_marking {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {x y : Ω}
    (hQ : catalogIs (PSimple p S) l154ExcUntw) (hInn : InnDiagOn p (Subgroup.zpowers x) S)
    (hF : FieldOn p y S) :
    ∃ (τ : Tag) (K : Type) (_ : Field K) (_ : Finite K) (n : ℕ)
      (θ : PSimple p S ≃* LargeEvenCenterQuot (adjointGroup τ K))
      (φx f u : MulAut (LargeEvenCenterQuot (adjointGroup τ K))),
      (τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) ∧ Nat.card K = 2 ^ n ∧ 1 ≤ n ∧
      commutator (PQuot p S) = ⊤ ∧ φx ∈ markIDImage (IsRoot τ) K (adjointGroup τ K) ∧
      f ∈ RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K) ∧
      u ∈ markIDImage (IsRoot τ) K (adjointGroup τ K) ∧ orderOf f = p ∧
      LargeEvenInduces θ (indRel p S x) φx ∧ LargeEvenInduces θ (indRel p S y) (u * f * u⁻¹) := by
  have hdiag : CFSG.Assembly.LargeEvenMarking (PQuot p S)
      fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ (indRel p S x) φ :=
    Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh x (Subgroup.mem_zpowers x)) hInn.2
  obtain ⟨hperf, lab, hΛ, hraw⟩ := MI.marking_transport (indRel p S x) hdiag hF.2
  have hlab : Y10F.HasLabel (PQuot p S) (fun l : GLALabel => l = lab) :=
    ⟨hperf, lab, hΛ, Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨τ, K, instF, instFin, hτ, hK, hQ'⟩ :=
    excUntw_raw_of_label (excUntw_tag_of_marking hlab hQ) hraw
  obtain ⟨-, -, θ, ⟨-, f, hf, u, hu, hord, hiy⟩, φ, hφ, hix⟩ := hQ'
  exact ⟨τ, K, instF, instFin, lab.n, θ, φ, f, u, hτ, hK, hΛ.1, hperf, hφ, hf, hu, hord, hix, hiy⟩

theorem excUntw_marking_data {p : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2) {Ω : Type} [Group Ω]
    [Finite Ω] {S : Subgroup Ω} {x y : Ω} (hQ : catalogIs (PSimple p S) l154ExcUntw)
    (hxp : x ^ p = 1) (_hyp : y ^ p = 1) (hxy : x * y = y * x)
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) (hF : FieldOn p y S) :
    ∃ (τ : Tag) (K : Type) (_ : Field K) (_ : Finite K) (e k : ℕ)
      (θ : PSimple p S ≃* ↥(adjointGroup τ K)) (φx φy : MulAut ↥(adjointGroup τ K))
      (h : ModGL τ K) (T : K →+* K),
      (τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) ∧ CharP K 2 ∧ 1 ≤ e ∧
      Nat.card K = 2 ^ (e * p) ∧ (∀ c, T c = c ^ (2 ^ e)) ∧
      commutator ↥(adjointGroup τ K) = ⊤ ∧
      h ∈ CFSG.StandardType.RecipeExcLang.inndiagGroup τ K ∧ h ^ p = 1 ∧
      Units.map (entrywiseHom T) h = h ∧
      baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈ adjointGroup τ (AlgebraicClosure K) ∧
      Nat.Coprime k p ∧
      (∀ c, (φx c : ModGL τ K) = h * c * h⁻¹) ∧
      (∀ c, (φy c : ModGL τ K) = Units.map (entrywiseHom T) c) ∧
      LargeEvenInduces θ (indRel p S x) φx ∧ LargeEvenInduces θ (indRel p S (y ^ k)) φy := by
  obtain ⟨τ, K, instF, instFin, n, θ₀, φx₀, f, u, hτ, hK, hn, hperf, hφx, hf, hu, hord, hix, hiy⟩ :=
    excUntw_raw_marking hQ hInn hF
  have hr : 0 < τ.rank := by rcases hτ with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨θ, w, σ, hσ, hwx, hσy⟩ := excUntw_normalize hr θ₀ hφx hf hu hord hix hiy
  obtain ⟨e, k, φx, φy, h, T, he, hKe, hT, hh, hhp, hfix, hbc, hk, hφx', hφy, hindx, hindy⟩ :=
    excUntw_data_of_induces hp hn hK (hInn.1 (Subgroup.mem_zpowers x)) hF.1 hxp hxy θ w σ hσ hwx hσy
  haveI : Group.IsPerfect (PQuot p S) := ⟨hperf⟩
  haveI : Group.IsPerfect (PSimple p S) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center (PQuot p S)))
      (QuotientGroup.mk'_surjective _)
  haveI : Group.IsPerfect ↥(adjointGroup τ K) :=
    Group.IsPerfect.ofSurjective (f := θ.toMonoidHom) θ.surjective
  exact ⟨τ, K, instF, instFin, e, k, θ, φx, φy, h, T, hτ, charP_two_of_card hK, he, hKe, hT,
    Group.IsPerfect.commutator_eq_top, hh, hhp, hfix, hbc, hk, hφx', hφy, hindx, hindy⟩

end LabelU

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
