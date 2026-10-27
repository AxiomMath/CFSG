module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieNonUnitaryLin
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.PSL2Table CFSG.AGLEmbedding
open scoped MatrixGroups

section Model

variable {F : Type} [Field F]

@[expose] def diagPSL : Fˣ →* PSL(2, F) where
  toFun a := mk (diag a)
  map_one' := by rw [diag_one, map_one]
  map_mul' a b := by rw [diag_mul, map_mul]

theorem borel_eq_sup (hF : ringChar F ≠ 2) : borel F = unipotent F ⊔ (diagPSL (F := F)).range := by
  apply le_antisymm
  · rintro g ⟨A, hA, rfl⟩
    have hdet := det_entries A
    have h10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hA
    rw [h10, mul_zero, sub_zero] at hdet
    have h0 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    let a : Fˣ := Units.mk0 _ h0
    have hA' : A = unip ((A : Matrix (Fin 2) (Fin 2) F) 0 1 * (A : Matrix (Fin 2) (Fin 2) F) 0 0) *
        diag a := by
      apply SL_ext
      · simp [mul_apply_SL, a]
      · simp [mul_apply_SL, a]
        field_simp
      · simp [mul_apply_SL, h10, a]
      · simp [mul_apply_SL, a]
        exact eq_inv_of_mul_eq_one_right hdet
    rw [hA', map_mul]
    exact Subgroup.mul_mem_sup (mk_unip_mem_unipotent _) ⟨a, rfl⟩
  · refine sup_le ?_ ?_
    · rintro g ⟨A, hA, rfl⟩
      exact ⟨A, (mem_borelSL_iff A).2 hA.1, rfl⟩
    · rintro g ⟨a, rfl⟩
      exact ⟨diag a, (mem_borelSL_iff _).2 (by simp), rfl⟩

end Model

section Normalizer

theorem normalizer_map_conj {G : Type*} [Group G] (g : G) (S : Subgroup G) :
    Subgroup.normalizer ((S.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.normalizer (S : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have := h (g * y * g⁻¹)
    simp only [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at this
    simpa [mul_assoc] using this
  · intro h y
    simp only [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mul_assoc]
    have := h (g⁻¹ * y * g)
    simpa [mul_assoc] using this

theorem psl2GF_normalizer_eq_sup_cyclic {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (T : Sylow p (PSL2GF p n)) :
    ∃ J : Subgroup (PSL2GF p n), IsCyclic J ∧
      Subgroup.normalizer ((T : Subgroup (PSL2GF p n)) : Set (PSL2GF p n)) =
        (T : Subgroup (PSL2GF p n)) ⊔ J := by
  have hF : ringChar (GaloisField p n) ≠ 2 := by rw [ringChar.eq (GaloisField p n) p]; exact hp2
  obtain ⟨U, hU⟩ := exists_sylow_eq_unipotent_psl2GF hp2 hn
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL2GF p n) U T
  have hT : (T : Subgroup (PSL2GF p n)) =
      (unipotent (GaloisField p n)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hU]
    rfl
  refine ⟨(diagPSL (F := GaloisField p n)).range.map (MulAut.conj g).toMonoidHom, ?_, ?_⟩
  · haveI : IsCyclic (diagPSL (F := GaloisField p n)).range :=
      isCyclic_of_surjective (diagPSL (F := GaloisField p n)).rangeRestrict
        (diagPSL (F := GaloisField p n)).rangeRestrict_surjective
    exact isCyclic_of_surjective
      (((MulAut.conj g).toMonoidHom.subgroupMap (diagPSL (F := GaloisField p n)).range))
      (MonoidHom.subgroupMap_surjective _ _)
  · rw [hT, normalizer_map_conj, normalizer_unipotent_eq_borel hF, borel_eq_sup hF,
      Subgroup.map_sup]

end Normalizer

section Transport

theorem normalizer_map_equiv {A B : Type*} [Group A] [Group B] (f : A ≃* B) (S : Subgroup A) :
    Subgroup.normalizer ((S.map f.toMonoidHom : Subgroup B) : Set B) =
      (Subgroup.normalizer (S : Set A)).map f.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h a
    have := h (f a)
    simp only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, map_mul, map_inv] at this
    exact this
  · intro h b
    simp only [Subgroup.mem_map_equiv, map_mul, map_inv]
    exact h _

theorem normalizer_eq_sup_cyclic_of_equiv {K : Type} [Group K] [Finite K] {p n : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hn : 1 ≤ n) (e : K ≃* PSL2GF p n) (T : Sylow p K) :
    ∃ J : Subgroup K, IsCyclic J ∧
      Subgroup.normalizer ((T : Subgroup K) : Set K) = (T : Subgroup K) ⊔ J := by
  have hfs : Function.Surjective (e : K →* PSL2GF p n) := e.surjective
  let T'' : Sylow p (PSL2GF p n) := T.mapSurjective hfs
  have hT'' : (T'' : Subgroup (PSL2GF p n)) = (T : Subgroup K).map e.toMonoidHom :=
    Sylow.coe_mapSurjective hfs T
  obtain ⟨J'', hJc, hJ⟩ := psl2GF_normalizer_eq_sup_cyclic hp2 hn T''
  refine ⟨J''.map e.symm.toMonoidHom, ?_, ?_⟩
  · exact isCyclic_of_surjective (e.symm.toMonoidHom.subgroupMap J'')
      (MonoidHom.subgroupMap_surjective _ _)
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [← normalizer_map_equiv, ← hT'', hJ, Subgroup.map_sup, hT'', Subgroup.map_map]
    have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by
      ext x; simp
    rw [this, Subgroup.map_id]

end Transport

section Row

variable {X : Type} [Group X] [Finite X]

theorem sylow_le_of_index {K : Subgroup X} [K.Normal] (P : Sylow 3 X) (hidx : ¬ 3 ∣ K.index) :
    (P : Subgroup X) ≤ K := by
  have hp : IsPGroup 3 ((P : Subgroup X).map (QuotientGroup.mk' K)) :=
    P.isPGroup'.map (QuotientGroup.mk' K)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hp
  have hdvd : Nat.card ((P : Subgroup X).map (QuotientGroup.mk' K)) ∣ K.index :=
    Subgroup.card_subgroup_dvd_card _
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra h
    exact hidx ((dvd_pow_self 3 h).trans hdvd)
  rw [hk0, pow_zero] at hk
  have hbot := Subgroup.card_eq_one.1 hk
  intro x hx
  have : QuotientGroup.mk' K x ∈ ((P : Subgroup X).map (QuotientGroup.mk' K)) :=
    Subgroup.mem_map_of_mem _ hx
  rw [hbot, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff x).1 this

theorem isElemAbelian_of_subgroupOf {p : ℕ} {K S : Subgroup X} (hS : S ≤ K)
    (h : CFSG.Open.IsElemAbelian p (S.subgroupOf K)) : CFSG.Open.IsElemAbelian p S := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · have := h.1.is_comm.comm (⟨⟨a, hS a.2⟩, Subgroup.mem_subgroupOf.2 a.2⟩ : S.subgroupOf K)
      (⟨⟨b, hS b.2⟩, Subgroup.mem_subgroupOf.2 b.2⟩ : S.subgroupOf K)
    exact Subtype.ext (congrArg (fun z : ↥(S.subgroupOf K) => ((z : K) : X)) this)
  · have := h.2 ⟨x, hS hx⟩ (Subgroup.mem_subgroupOf.2 hx)
    exact congrArg (fun z : K => (z : X)) this

end Row

section Gamma

variable {X : Type} [Group X] [Finite X] {K : Subgroup X}

open CFSG.AGLEmbedding KFactProofs.GLBCoreNormalizer in
theorem gammaCore_eq_map_normalizer {P : Subgroup X} (hPK : P ≤ K) {T : Subgroup ↥K}
    (hT : T.map K.subtype = P) (hdvd : 3 ∣ Nat.card T)
    (hti : ∀ t ∈ T, t ≠ 1 → ∀ g : ↥K, g * t * g⁻¹ ∈ T →
      g ∈ Subgroup.normalizer (T : Set ↥K)) :
    gammaCore 3 1 K P = (Subgroup.normalizer (T : Set ↥K)).map K.subtype := by
  apply le_antisymm
  · unfold gammaCore
    rw [Subgroup.closure_le]
    rintro x ⟨hxK, R, hRP, hR, hxR⟩
    have hR0 : R ≠ ⊥ := ne_bot_of_one_le_pRank' (by norm_num) hR
    obtain ⟨r, hr⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hR0
    have hrP : (r : X) ∈ P := hRP r.2
    rw [← hT] at hrP
    obtain ⟨t, htT, htr⟩ := hrP
    have hxr : x * (r : X) * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 hxR r).1 r.2
    have hxr' : x * (r : X) * x⁻¹ ∈ P := hRP hxr
    rw [← hT] at hxr'
    obtain ⟨t2, ht2T, ht2⟩ := hxr'
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    refine hti t htT ?_ ⟨x, hxK⟩ ?_
    · intro h1
      apply hr
      apply Subtype.ext
      rw [← htr, h1]
      simp
    · have : (⟨x, hxK⟩ : ↥K) * t * (⟨x, hxK⟩ : ↥K)⁻¹ = t2 := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [show ((t : ↥K) : X) = r from htr]
        exact ht2.symm
      rw [this]
      exact ht2T
  · rintro x ⟨n, hn, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨n.2, P, le_rfl, ?_, ?_⟩
    · apply one_le_pRank_of_dvd (by norm_num)
      rw [← hT, Subgroup.card_map_of_injective K.subtype_injective]
      exact hdvd
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have hyK : y ∈ K := hPK hy
        rw [← hT] at hy ⊢
        obtain ⟨t, htT, rfl⟩ := hy
        refine ⟨n * t * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn t).1 htT, ?_⟩
        simp
      · intro hy
        rw [← hT] at hy ⊢
        obtain ⟨t, htT, ht⟩ := hy
        refine ⟨n⁻¹ * t * n, ?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.1 hn _).2 (by simpa [mul_assoc] using htT)
        · have ht' : ((t : ↥K) : X) = (n : X) * y * (n : X)⁻¹ := ht
          show ((n⁻¹ * t * n : ↥K) : X) = y
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ht']
          group

end Gamma

section Helpers2

variable {X : Type} [Group X] [Finite X] {K : Subgroup X}

theorem map_normalizer_eq_inf {P : Subgroup X} {T : Subgroup ↥K} (hT : T.map K.subtype = P) :
    (Subgroup.normalizer (T : Set ↥K)).map K.subtype = K ⊓ Subgroup.normalizer (P : Set X) := by
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨n.2, ?_⟩
    refine Subgroup.mem_normalizer_iff.2 ?_
    intro y
    constructor
    · intro hy
      rw [← hT] at hy ⊢
      obtain ⟨t, htT, rfl⟩ := hy
      exact ⟨n * t * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn t).1 htT, by simp⟩
    · intro hy
      rw [← hT] at hy ⊢
      obtain ⟨t, htT, ht⟩ := hy
      refine ⟨n⁻¹ * t * n, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 hn _).2 (by simpa [mul_assoc] using htT)
      · have ht' : ((t : ↥K) : X) = (n : X) * y * (n : X)⁻¹ := ht
        show ((n⁻¹ * t * n : ↥K) : X) = y
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ht']
        group
  · rintro ⟨hxK, hxN⟩
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    refine Subgroup.mem_normalizer_iff.2 ?_
    intro t
    have hiff := Subgroup.mem_normalizer_iff.1 hxN (t : X)
    have e1 : ((t : ↥K) : X) ∈ P ↔ t ∈ T := by
      rw [← hT]
      exact ⟨fun ⟨t', ht', h⟩ => by rw [← Subtype.ext h]; exact ht', fun h => ⟨t, h, rfl⟩⟩
    have e2 : (x * ((t : ↥K) : X) * x⁻¹) ∈ P ↔ (⟨x, hxK⟩ * t * ⟨x, hxK⟩⁻¹ : ↥K) ∈ T := by
      rw [← hT]
      constructor
      · rintro ⟨t', ht', h⟩
        have : t' = ⟨x, hxK⟩ * t * ⟨x, hxK⟩⁻¹ := Subtype.ext (by simpa using h)
        rw [← this]; exact ht'
      · intro h; exact ⟨_, h, by simp⟩
    rw [← e1, ← e2]
    exact hiff

theorem isElemAbelian_of_map_injective {p : ℕ} {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) {S : Subgroup A}
    (h : CFSG.Open.IsElemAbelian p (S.map f)) : CFSG.Open.IsElemAbelian p S := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · have := h.1.is_comm.comm (⟨f a, a, a.2, rfl⟩ : S.map f) (⟨f b, b, b.2, rfl⟩ : S.map f)
    apply Subtype.ext
    apply hf
    simpa using congrArg Subtype.val this
  · have := h.2 (f x) ⟨x, hx, rfl⟩
    apply hf
    simpa [← map_pow] using this

end Helpers2

section Assembly

open CFSG.RankThree.PartOne.Census3 TauCeti
open CFSG.AGLEmbedding.KFactProofs.NonUnitary

theorem gls3ConclusionPlus_A1_of_index {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal]
    (q : PrimePower) (hq : q.p = 3) (d : ValidLieTypeIndex) (hd : d.1 = .A 1 q)
    (e₀ : ↥K ≃* (CFSGIndex.lie d).Group) (hidx : ¬ 3 ∣ K.index) (P : Sylow 3 X) :
    Gls3ConclusionPlus X K (P : Subgroup X) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨d0, hv⟩ := d
  simp only at hd
  subst hd
  have hqcard : q.card = 3 ^ q.exponent := by rw [PrimePower.card_def, hq]
  have hn2 : 2 ≤ q.exponent := by
    by_contra h
    have h1 : q.exponent ≤ 1 := by omega
    have hv1 := ((LieTypeIndex.valid_iff _).1 hv).1
    have h4 : 4 ≤ q.card := (((LieTypeIndex.inStandardRange_iff _).1 hv1).2 rfl)
    rw [hqcard] at h4
    have : 3 ^ q.exponent ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
    omega
  have hd' : IsLinTwoIndex 3 q.exponent ⟨.A 1 q, hv⟩ := ⟨q, rfl, hq, rfl⟩
  obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd'
  let e : ↥K ≃* PSL2GF 3 q.exponent := e₀.trans e₂
  have hPK : (P : Subgroup X) ≤ K := sylow_le_of_index P hidx
  have hPinf : (P : Subgroup X) ⊓ K = P := inf_eq_left.2 hPK
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal (G := X) (p := 3) P (N := K)
  have hTmap : (T : Subgroup ↥K).map K.subtype = P := by
    rw [hT, Subgroup.map_subgroupOf_eq_of_le inf_le_right, hPinf]
  have D := smallRankOneData_of_isLinTwo hp2 hn2 hd' ⟨e₀⟩ T
  obtain ⟨J, hJc, hNJ⟩ := normalizer_eq_sup_cyclic_of_equiv hp2 (by omega) e T
  have hcardT : Nat.card (T : Subgroup ↥K) = 3 ^ q.exponent := by
    have hfs : Function.Surjective (e : ↥K →* PSL2GF 3 q.exponent) := e.surjective
    have := (psl2GF_sylow 3 q.exponent (by omega) (T.mapSurjective hfs)).2
    rw [Sylow.coe_mapSurjective hfs T, Subgroup.card_map_of_injective e.injective] at this
    exact this
  have hΓ : gammaCore 3 1 K (P : Subgroup X) =
      (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)).map K.subtype :=
    gammaCore_eq_map_normalizer hPK hTmap (by rw [hcardT]; exact dvd_pow_self 3 (by omega)) D.ti
  have hΓ' : gammaCore 3 1 K ((P : Subgroup X) ⊓ K) =
      (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)).map K.subtype := by rw [hPinf]; exact hΓ
  have hN : IsCoatom (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) := D.maximal
  refine ⟨?_, ?_, Or.inl ⟨q, hq, ⟨hv, ⟨e₀⟩⟩, hidx, ?_, ?_, ?_, ?_⟩⟩
  · rw [hΓ']
    refine lt_of_le_of_ne (Subgroup.map_subtype_le _) fun h => ?_
    have h' : (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)).map K.subtype =
        (⊤ : Subgroup ↥K).map K.subtype := by
      rw [h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hN.1 (Subgroup.map_injective K.subtype_injective h')
  · intro H hlt hHK
    rw [hΓ'] at hlt
    have hle : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ H.subgroupOf K :=
      Subgroup.map_le_iff_le_comap.1 hlt.le
    have hne : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≠ H.subgroupOf K := by
      intro h
      apply hlt.ne
      rw [h, Subgroup.map_subgroupOf_eq_of_le hHK]
    have htop := hN.2 _ (lt_of_le_of_ne hle hne)
    refine le_antisymm hHK fun x hx => ?_
    have : (⟨x, hx⟩ : ↥K) ∈ H.subgroupOf K := by rw [htop]; exact Subgroup.mem_top _
    exact this
  · rw [hΓ', hPinf, map_normalizer_eq_inf hTmap]
  · refine ⟨J.map K.subtype, ?_, ?_⟩
    · exact isCyclic_of_surjective (K.subtype.subgroupMap J) (MonoidHom.subgroupMap_surjective _ _)
    · rw [hΓ', hNJ, Subgroup.map_sup, hTmap, hPinf]
  · rw [hPinf]
    have hS : (P : Subgroup X) ≤ K := hPK
    refine isElemAbelian_of_subgroupOf hS ?_
    have hP' : (P : Subgroup X).subgroupOf K = T := by
      rw [← hTmap]
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective T
    rw [hP']
    have hfs : Function.Surjective (e : ↥K →* PSL2GF 3 q.exponent) := e.surjective
    have h1 := (psl2GF_sylow 3 q.exponent (by omega) (T.mapSurjective hfs)).1
    rw [Sylow.coe_mapSurjective hfs T] at h1
    exact isElemAbelian_of_map_injective (e : ↥K →* PSL2GF 3 q.exponent) e.injective h1
  · rw [hPinf, ← hTmap, Subgroup.card_map_of_injective K.subtype_injective, hcardT, hqcard]

end Assembly

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
