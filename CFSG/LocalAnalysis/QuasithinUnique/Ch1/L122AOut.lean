module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122ACore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare
public import CFSG.RankThree.SteinbergR3ESuzukiFieldSplitting
public import CFSG.Walter.J1Props.Aut
public import CFSG.Walter.Models
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.QuasithinUnique.Vol2Native.L122A

section Split

variable {A : Type*} [Group A]

theorem lift_of_split {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {I M F : Subgroup A} [I.Normal]
    [M.Normal] (hIM : I ≤ M) (hfac : ∀ x : A, ∃ m ∈ M, ∃ f ∈ F, x = m * f)
    (hMF : ∀ y : A, y ∈ M → y ∈ F → y = 1)
    (hcos : ∀ m ∈ M, ∀ m' ∈ M, m ∈ I ∨ m' ∈ I ∨ m⁻¹ * m' ∈ I) {x : A} (hx : x ^ p ∈ I) :
    ∃ ν ∈ I, (ν * x) ^ p = 1 := by
  obtain ⟨m, hm, f, hf, rfl⟩ := hfac x
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨j, hj⟩ := hodd
  have hfp : f ^ p = 1 := by
    apply hMF _ _ (F.pow_mem hf p)
    have h1 : (QuotientGroup.mk' M (m * f)) ^ p = 1 := by
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hIM hx
    have h2 : QuotientGroup.mk' M (m * f) = QuotientGroup.mk' M f := by
      have hm1 : QuotientGroup.mk' M m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
      rw [map_mul, hm1, one_mul]
    rw [h2, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hmI : m ∈ I := by
    by_contra hmI
    have hcomm : f * m * f⁻¹ * m⁻¹ ∈ I := by
      have hm' : f * m * f⁻¹ ∈ M := (Subgroup.Normal.conj_mem inferInstance m hm f)
      have hm'I : f * m * f⁻¹ ∉ I := by
        intro h
        apply hmI
        have := Subgroup.Normal.conj_mem inferInstance _ h f⁻¹
        simpa [mul_assoc] using this
      rcases hcos m hm _ hm' with h | h | h
      · exact absurd h hmI
      · exact absurd h hm'I
      · have := Subgroup.Normal.conj_mem inferInstance _ h m
        have e : m * (m⁻¹ * (f * m * f⁻¹)) * m⁻¹ = f * m * f⁻¹ * m⁻¹ := by group
        rwa [e] at this
    have hsq : m * m ∈ I := by
      rcases hcos m⁻¹ (M.inv_mem hm) m hm with h | h | h
      · exact absurd (by simpa using I.inv_mem h) hmI
      · exact absurd h hmI
      · simpa using h
    set q := QuotientGroup.mk' I with hq
    have hqm2 : q m * q m = 1 := by
      rw [← map_mul, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hsq
    have hqc : Commute (q m) (q f) := by
      have h0 : q (f * m * f⁻¹ * m⁻¹) = 1 := by
        rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hcomm
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h0
      have h3 : q f * q m * (q f)⁻¹ = q m := mul_inv_eq_one.mp h0
      exact (mul_inv_eq_iff_eq_mul.mp h3).symm
    have hqx : (q (m * f)) ^ p = 1 := by
      rw [← map_pow, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hx
    have hqf : (q f) ^ p = 1 := by rw [← map_pow, hfp, map_one]
    rw [map_mul, hqc.mul_pow, hqf, mul_one, hj] at hqx
    have hpow : (q m) ^ (2 * j + 1) = q m := by
      rw [pow_succ, pow_mul, sq, hqm2, one_pow, one_mul]
    rw [hpow] at hqx
    apply hmI
    rw [hq, QuotientGroup.mk'_apply] at hqx
    exact (QuotientGroup.eq_one_iff m).mp hqx
  refine ⟨m⁻¹, I.inv_mem hmI, ?_⟩
  rw [← mul_assoc, inv_mul_cancel, one_mul]
  exact hfp

end Split

section J1

open CFSG.Walter CFSG.Walter.J1Props CFSG.Open CFSG.Blueprint

theorem outPLifts_carrierJ1
    {K : Type} [Group K] (e : K ≃* NativeSporadic.Carrier .J1) (p : ℕ) :
    OutPLifts p K := by
  intro ξ _
  let ε : K ≃* walterJ1 := e.trans walterJ1EquivNative.symm
  obtain ⟨g, hg⟩ := J3_aut (ε.symm.trans (ξ.trans ε))
  have hξ : ξ = MulAut.conj (ε.symm g) := by
    apply MulEquiv.ext
    intro x
    apply ε.injective
    have h1 := congrArg (fun f : MulAut walterJ1 => f (ε x)) hg
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
    rw [h1]
    simp
  refine ⟨(ε.symm g)⁻¹, ?_⟩
  rw [hξ, ← map_mul, inv_mul_cancel, map_one, one_pow]

end J1

section Suzuki

open CFSG.Blueprint CFSG.RankThree.Automorphisms CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)

theorem outPLifts_suzuki (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    OutPLifts p (suzukiGroup a K) := by
  obtain ⟨-, ⟨e, he⟩, -, hinf, -⟩ := Suzuki_full_field_automorphism_splitting a ha K hK
  intro ξ ⟨k, hk⟩
  have hxI : ξ ^ p ∈ inner (suzukiGroup a K) := ⟨k, hk.symm⟩
  obtain ⟨ν, hν, hνp⟩ := lift_of_split hp hp2 (I := inner (suzukiGroup a K))
    (M := inner (suzukiGroup a K)) (F := (szFieldAut a K).range) le_rfl
    (fun x => by
      obtain ⟨⟨g, σ⟩, hx⟩ := e.surjective x
      exact ⟨MulAut.conj g, ⟨g, rfl⟩, szFieldAut a K σ, ⟨σ, rfl⟩, by rw [← hx, he]⟩)
    (fun y hyM hyF => by
      have : y ∈ (szFieldAut a K).range ⊓ inner (suzukiGroup a K) := ⟨hyF, hyM⟩
      rw [hinf] at this
      exact Subgroup.mem_bot.mp this)
    (fun m hm _ _ => Or.inl hm) hxI
  obtain ⟨k', hk'⟩ := hν
  exact ⟨k', by rw [hk']; exact hνp⟩

end Suzuki

section PSL2

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification

variable (K : Type) [Field K] [Finite K]

theorem isSquare_mul_of_not_isSquare {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (hna : ¬ IsSquare a)
    (hnb : ¬ IsSquare b) : IsSquare (a * b) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h1 : quadraticChar K a = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hna
  have h2 : quadraticChar K b = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hnb
  have h3 : quadraticChar K (a * b) = 1 := by
    rw [map_mul, h1, h2]
    norm_num
  exact (quadraticChar_one_iff_isSquare (mul_ne_zero ha hb)).mp h3

theorem psl_range_cosets (m m' : PGammaL2 K) (hm : m ∈ pGammaL2PGLRange K)
    (hm' : m' ∈ pGammaL2PGLRange K) :
    m ∈ pGammaL2PSLRange K ∨ m' ∈ pGammaL2PSLRange K ∨ m⁻¹ * m' ∈ pGammaL2PSLRange K := by
  obtain ⟨g, rfl⟩ := hm
  obtain ⟨g', rfl⟩ := hm'
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  obtain ⟨A', rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g'
  have key : ∀ B : GL (Fin 2) K,
      SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk B) ∈ pGammaL2PSLRange K ↔
        IsSquare (B.det : K) := by
    intro B
    rw [mem_pGammaL2PSLRange_iff]
    constructor
    · rintro ⟨y, hy⟩
      exact (pgl2_mk_mem_psl2_range_iff_det_isSquare B).mp ⟨y, SemidirectProduct.inl_injective hy⟩
    · intro h
      obtain ⟨y, hy⟩ := (pgl2_mk_mem_psl2_range_iff_det_isSquare B).mpr h
      exact ⟨y, congrArg SemidirectProduct.inl hy⟩
  by_cases h1 : IsSquare (A.det : K)
  · exact Or.inl ((key A).mpr h1)
  by_cases h2 : IsSquare (A'.det : K)
  · exact Or.inr (Or.inl ((key A').mpr h2))
  refine Or.inr (Or.inr ?_)
  rw [← map_inv, ← map_mul, ← map_inv, ← map_mul, key]
  have h3 := isSquare_mul_of_not_isSquare K (Units.ne_zero A.det) (Units.ne_zero A'.det) h1 h2
  obtain ⟨r, hr⟩ := h3
  have hd : ((A⁻¹ * A').det : K) = (A.det : K)⁻¹ * (A'.det : K) := by
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [hd]
  refine ⟨(A.det : K)⁻¹ * r, ?_⟩
  have hne : (A.det : K) ≠ 0 := Units.ne_zero A.det
  field_simp
  linear_combination hr

theorem outPLifts_psl2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : OutPLifts p (PSL2 K) := by
  have hI : (pGammaL2PSLRange K).Normal := by
    rw [← semilinearToOuter_ker K]
    infer_instance
  have hIM : pGammaL2PSLRange K ≤ pGammaL2PGLRange K := by
    intro x hx
    obtain ⟨y, rfl⟩ := (mem_pGammaL2PSLRange_iff K x).mp hx
    exact ⟨_, rfl⟩
  intro ξ ⟨k, hk⟩
  obtain ⟨x, rfl⟩ := semilinearAction_surjective K ξ
  have hxI : x ^ p ∈ pGammaL2PSLRange K := by
    rw [← semilinearToOuter_ker K, MonoidHom.mem_ker]
    change (QuotientGroup.mk (semilinearAction K (x ^ p)) : OuterAutomorphisms.Outer (PSL2 K)) = 1
    rw [map_pow, hk]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨k, rfl⟩
  obtain ⟨ν, hνI, hν⟩ := lift_of_split hp hp2 (I := pGammaL2PSLRange K)
    (M := pGammaL2PGLRange K) (F := (SemidirectProduct.inr : (K ≃+* K) →* PGammaL2 K).range)
    hIM
    (fun x => ⟨SemidirectProduct.inl x.left, ⟨x.left, rfl⟩, SemidirectProduct.inr x.right,
      ⟨x.right, rfl⟩, (SemidirectProduct.inl_left_mul_inr_right x).symm⟩)
    (fun y hyM hyF => by
      obtain ⟨g, rfl⟩ := hyM
      obtain ⟨σ, hσ⟩ := hyF
      have h1 := congrArg SemidirectProduct.rightHom hσ
      rw [SemidirectProduct.rightHom_inr, SemidirectProduct.rightHom_inl] at h1
      rw [← hσ, h1, map_one])
    (fun m hm m' hm' => psl_range_cosets K m m' hm hm') hxI
  have hνin : semilinearAction K ν ∈ OuterAutomorphisms.inner (PSL2 K) := by
    have : ν ∈ (semilinearToOuter K).ker := by rwa [semilinearToOuter_ker K]
    exact (QuotientGroup.eq_one_iff _).mp this
  obtain ⟨k', hk'⟩ := hνin
  refine ⟨k', ?_⟩
  rw [hk', ← map_mul, ← map_pow, hν, map_one]

end PSL2

section Types

open CFSG.Quasithin CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem outPLifts_of_psl2_model {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (K : Type) [Field K] [Finite K] (e : X ≃* StatedProj (StatedSL 2 K)) : OutPLifts p X :=
  (outPLifts_psl2 K hp hp2).of_mulEquiv
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).symm

theorem outPLifts_of_a38Types
    {X : Type} [Group X] (hX : A38Types X) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : OutPLifts p X := by
  rcases hX with ⟨n, hn⟩ | ⟨n, hn⟩ | hJ | ⟨q, hq, hq3, hn⟩
  · obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hn
    exact outPLifts_of_psl2_model hp hp2 K e
  · obtain ⟨-, a, ha, K, _, _, hna, hK, ⟨e⟩⟩ := hn
    exact (outPLifts_suzuki a ha K (by rw [← hna]; exact hK) hp hp2).of_mulEquiv e.symm
  · obtain ⟨e⟩ := hJ
    exact outPLifts_carrierJ1 e p
  · obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hn
    exact outPLifts_of_psl2_model hp hp2 K e

end Types

end CFSG.QuasithinUnique.Vol2Native.L122A
