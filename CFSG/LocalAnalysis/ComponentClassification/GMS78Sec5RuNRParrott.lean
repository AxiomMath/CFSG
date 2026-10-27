module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNRParrottCore
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSModelFast
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuJTrans
public import Certificates.Certificate15117
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSModel

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS CFSG.GMS78RuSP RuSModel

namespace RuNR

theorem mem_allPt {p : Pt} : p ∈ allPt ↔ p.1 < 256 := by
  obtain ⟨c, t, d⟩ := p
  simp [allPt, all8]

theorem pMul_eq {p q : Pt} (hp : p.1 < 256) (hq : q.1 < 256) : pMul p q = sMul true p q :=
  sMulF_eq true hp hq

theorem pMul_lt {p q : Pt} (hp : p.1 < 256) (hq : q.1 < 256) : (pMul p q).1 < 256 := by
  rw [pMul_eq hp hq]
  exact sMul_fst_lt true hp q

theorem mem_xPts {p : Pt} :
    p ∈ xPts ↔ p.1 < 256 ∧ p.2.2 = 0 ∧ sMask p.1 ∈ ([0, 1, 2, 3] : List ℕ) := by
  obtain ⟨c, t, d⟩ := p
  constructor
  · intro h
    simp only [xPts, List.mem_flatMap, List.mem_map] at h
    obtain ⟨m, hm, t', -, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have hm4 : m < 256 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      omega
    exact ⟨cOf_lt m, rfl, by rw [sMask_cOf hm4]; exact hm⟩
  · rintro ⟨hc, hd, hm⟩
    simp only at hc hd hm
    simp only [xPts, List.mem_flatMap, List.mem_map]
    exact ⟨sMask c, hm, t, RuQCode.mem_all8 t, by rw [cOf_sMask hc, hd]⟩

theorem inJ_iff {p : Pt} : inJ p = true ↔
    ∀ x ∈ xPts, pMul p x = pMul x p ∨ pMul p x = pMul fPt (pMul x p) := by
  simp [inJ]

theorem inCX_iff {p : Pt} : inCX p = true ↔ ∀ x ∈ xPts, pMul p x = pMul x p := by
  simp [inCX]

theorem mem_jPts {p : Pt} : p ∈ jPts ↔ p.1 < 256 ∧ inJ p = true := by
  simp [jPts, mem_allPt]

theorem cmt_iff {q p : Pt} : cmt q p = true ↔ pMul p q = pMul q p := by
  simp [cmt]

theorem decPt_encPt {p : Pt} (hp : p.1 < 256) : decPt (encPt p) = p := by
  obtain ⟨c, t, d⟩ := p
  have ht := t.isLt
  have hd := d.isLt
  simp only [decPt, encPt, Prod.mk.injEq]
  refine ⟨by omega, ?_, ?_⟩ <;> ext <;> simp [fin8Of] <;> omega

theorem encPt_lt {p : Pt} (hp : p.1 < 256) : encPt p < 16384 := by
  have ht := p.2.1.isLt
  have hd := p.2.2.isLt
  simp only [encPt]
  omega

theorem jMem_eq {p : Pt} (hp : p.1 < 256) : jMem p = inJ p := by
  have hi := encPt_lt hp
  simp only [jMem, jArr, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, hi,
    ite_true, Option.map_some, Option.getD_some, decPt_encPt hp]

theorem cntC_eq (q : Pt) : cntC q = (allPt.filter (cmt q)).length :=
  List.countP_eq_length_filter

theorem evenD_dMul :
    ∀ d e : Fin 8, evenD d = false → evenD (dMul d e) = false → evenD e = true := by
  decide

section Cert


theorem checkA_spec : inJ aPt = true ∧ inCX aPt = false ∧ sqPt aPt = onePt := by
  have h := (Certificates.certificate15117).1
  simp only [checkA, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem checkCa_spec : cntC aPt = 1024 := by
  have h := (Certificates.certificate15117).2.1
  rw [checkCa, beq_iff_eq] at h
  exact h

theorem checkCx_spec : ∀ x ∈ jPts, inCX x = false → sqPt x = onePt →
    jPts.countP (cmt x) ≤ 128 := by
  have h := (Certificates.certificate15117).2.2.1
  simp only [checkCx, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  intro x hx hcx hsq
  rcases h x hx with (h1 | h1) | h1
  · rw [hcx] at h1
    exact absurd h1 Bool.false_ne_true
  · exact absurd hsq h1
  · exact h1

theorem checkF1_spec : ∀ y ∈ allPt, cmt aPt y = true → jMem (sqPt y) = true → jMem y = false →
    evenD y.2.2 = false → ∃ j ∈ jPts, cmt aPt j = true ∧ sqPt (pMul y j) = onePt := by
  have h := (Certificates.certificate15117).2.2.2.1
  simp only [checkF1, List.all_eq_true, List.any_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, beq_iff_eq] at h
  intro y hy h1 h2 h3 h4
  rcases h y hy with (((h5 | h5) | h5) | h5) | h5
  · rw [h1] at h5
    exact absurd h5 (by decide)
  · rw [h2] at h5
    exact absurd h5 (by decide)
  · rw [h3] at h5
    exact absurd h5 (by decide)
  · rw [h4] at h5
    exact absurd h5 (by decide)
  · exact h5

theorem checkF3_spec : inJ cPt = true ∧ inCX cPt = false ∧ ∀ k ∈ jPts, inCX k = true →
    sqPt (pMul k cPt) = onePt → ∃ u ∈ allPt, cmt (pMul k cPt) u = true ∧
      jMem (sqPt u) = true ∧ jMem u = false ∧ evenD u.2.2 = false ∧
        ∀ j ∈ jPts, cmt (pMul k cPt) j = true → sqPt (pMul u j) ≠ onePt := by
  have h := (Certificates.certificate15117).2.2.2.2.1
  simp only [checkF3, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_filter,
    List.any_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun k hk hkx hsq => ?_⟩
  rcases h3 k ⟨hk, hkx⟩ with h4 | ⟨u, hu, ⟨⟨⟨⟨h5, h6⟩, h7⟩, h8⟩, h9⟩⟩
  · exact absurd hsq h4
  · refine ⟨u, hu, h5, h6, h7, h8, fun j hj hjc => ?_⟩
    rcases h9 j hj with h10 | h10
    · rw [hjc] at h10
      exact absurd h10 (by decide)
    · exact h10

theorem checkJd_spec : ∀ d ∈ ([0, 1, 4, 5] : List (Fin 8)), ∃ j ∈ jPts, j.2.2 = d := by
  have h := (Certificates.certificate15117).2.2.2.2.2
  simpa [checkJd] using h

end Cert

theorem allPt_nodup : allPt.Nodup := by
  have h8 : all8.Nodup := List.nodup_finRange 8
  refine List.nodup_flatMap.2 ⟨fun c _ => List.nodup_flatMap.2 ⟨fun t _ => ?_, ?_⟩, ?_⟩
  · exact h8.map fun d d' h => by simpa using h
  · refine h8.imp fun {t t'} htt' => ?_
    simp only [Function.onFun, List.disjoint_left, List.mem_map]
    rintro _ ⟨d, -, rfl⟩ ⟨d', -, he⟩
    simp only [Prod.mk.injEq] at he
    exact htt' he.2.1.symm
  · refine List.nodup_range.imp fun {c c'} hcc' => ?_
    simp only [Function.onFun, List.disjoint_left, List.mem_flatMap, List.mem_map]
    rintro _ ⟨t, -, d, -, rfl⟩ ⟨t', -, d', -, he⟩
    simp only [Prod.mk.injEq] at he
    exact hcc' he.1.symm

theorem jPts_nodup : jPts.Nodup := allPt_nodup.filter _

theorem sMul_snd_snd (ε : Bool) (p q : Pt) : (sMul ε p q).2.2 = dMul p.2.2 q.2.2 := rfl

theorem onePt_mul : sMul true onePt onePt = onePt := by decide

theorem dCode_zero : dCode 0 = linId := rfl

theorem dCode_fix_one : ∀ d : Fin 8, linApply (dCode d) 1 = 1 := by decide

end RuNR

namespace RuNR

variable {G : Type} [Group G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8} {Φ : Pt → G}

section Dictionary

variable (hΦ : Sec3.SzR.SModel L T R μ ν true Φ)
include hΦ

theorem Φ_mul {p q : Pt} (hp : p.1 < 256) (hq : q.1 < 256) : Φ (pMul p q) = Φ p * Φ q := by
  rw [pMul_eq hp hq]
  exact hΦ.mul p q

theorem Φ_one : Φ onePt = 1 := by
  have h := hΦ.mul onePt onePt
  rw [onePt_mul] at h
  exact mul_eq_left.mp h.symm

theorem Φ_inj {p q : Pt} (hp : p.1 < 256) (hq : q.1 < 256) (h : Φ p = Φ q) : p = q :=
  hΦ.inj p q hp hq h

theorem Φ_eq_one_iff {p : Pt} (hp : p.1 < 256) : Φ p = 1 ↔ p = onePt :=
  ⟨fun h => Φ_inj hΦ hp (by decide) (h.trans (Φ_one hΦ).symm), by rintro rfl; exact Φ_one hΦ⟩

theorem Φ_mul_comm_iff {p q : Pt} (hp : p.1 < 256) (hq : q.1 < 256) :
    Φ p * Φ q = Φ q * Φ p ↔ pMul p q = pMul q p := by
  rw [← Φ_mul hΦ hp hq, ← Φ_mul hΦ hq hp]
  exact ⟨Φ_inj hΦ (pMul_lt hp hq) (pMul_lt hq hp), congrArg Φ⟩

theorem Φ_sq {p : Pt} (hp : p.1 < 256) : Φ p ^ 2 = Φ (sqPt p) := by
  rw [pow_two, sqPt, Φ_mul hΦ hp hp]

theorem Φ_sq_eq_one_iff {p : Pt} (hp : p.1 < 256) : Φ p ^ 2 = 1 ↔ sqPt p = onePt := by
  rw [Φ_sq hΦ hp]
  exact Φ_eq_one_iff hΦ (pMul_lt hp hp)

end Dictionary

omit [Group G] in
theorem linApply_linId' : ∀ t : Fin 8, linApply linId t = t := by decide

theorem pp_one : (0 :: RuQCode.ppOf 1) = ([0, 1, 2, 3] : List ℕ) := rfl

theorem comm_eq_one_iff' {v x : G} : v * x * v⁻¹ * x⁻¹ = 1 ↔ v * x = x * v := by
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

theorem comm_eq_iff' {v x z : G} : v * x * v⁻¹ * x⁻¹ = z ↔ v * x = z * (x * v) := by
  rw [mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul, mul_assoc]

section Coords

variable (hM : Sec3.SzR.MaskCoords L T R μ ν) (hΦ : Sec3.SzR.SModel L T R μ ν true Φ)
include hM hΦ

theorem Φ_mem_R_iff {p : Pt} : Φ p ∈ R ↔ p.2.2 = 0 := by
  constructor
  · intro h
    have h1 : ∀ b ∈ gmsA L T, ν (Φ p * b * (Φ p)⁻¹) = linApply linId (ν b) := fun b hb => by
      rw [hM.central _ h b hb, mul_inv_cancel_right, linApply_linId']
    exact dCode_injective _ _ ((hM.code_unique (hΦ.code p) h1).trans dCode_zero.symm)
  · intro h
    obtain ⟨c, t, d⟩ := p
    simp only at h
    subst h
    exact hΦ.mem_R c t

omit hΦ in
theorem code_of_mem_R {x : G} (hx : x ∈ R) :
    ∀ b ∈ gmsA L T, ν (x * b * x⁻¹) = linApply (dCode 0) (ν b) := fun b hb => by
  rw [hM.central _ hx b hb, mul_inv_cancel_right, dCode_zero, linApply_linId']

theorem exists_Φ_of_mem_R {x : G} (hx : x ∈ R) : ∃ p : Pt, p.1 < 256 ∧ p.2.2 = 0 ∧ Φ p = x :=
  hΦ.surj x (le_normalizer hx) 0 (code_of_mem_R hM hx)

omit hM in
theorem ν_Φ_fPt : ν (Φ fPt) = 1 := hΦ.ν_eq 1

theorem Φ_fPt_ne_one : Φ fPt ≠ 1 := fun h => by
  have h1 := ν_Φ_fPt hΦ
  rw [h, hM.ν_one] at h1
  exact absurd h1 (by decide)

theorem Φ_conj_fPt (p : Pt) : Φ p * Φ fPt * (Φ p)⁻¹ = Φ fPt := by
  have hfA : Φ fPt ∈ gmsA L T := hΦ.mem_A 1
  refine hM.eq_of_ν_eq (hM.normA _ (hΦ.mem p) _ hfA) hfA ?_
  rw [hΦ.code p _ hfA, ν_Φ_fPt hΦ, dCode_fix_one]

theorem Φ_mem_X_iff {X : Subgroup G}
    (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν (Φ fPt))) {p : Pt} (hp : p.1 < 256) :
    Φ p ∈ X ↔ p ∈ xPts := by
  rw [hX, Φ_mem_R_iff hM hΦ, mem_xPts, ν_Φ_fPt hΦ, pp_one]
  obtain ⟨c, t, d⟩ := p
  simp only at hp ⊢
  constructor
  · rintro ⟨rfl, hm⟩
    rw [hΦ.μ_eq] at hm
    exact ⟨hp, rfl, hm⟩
  · rintro ⟨-, rfl, hm⟩
    exact ⟨rfl, by rw [hΦ.μ_eq]; exact hm⟩

theorem exists_Φ_of_mem_X {X : Subgroup G}
    (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν (Φ fPt))) {x : G} (hx : x ∈ X) :
    ∃ q ∈ xPts, Φ q = x := by
  obtain ⟨p, hp, -, rfl⟩ := exists_Φ_of_mem_R hM hΦ ((hX x).mp hx).1
  exact ⟨p, (Φ_mem_X_iff hM hΦ hX hp).mp hx, rfl⟩

theorem Φ_mem_J_iff {S X J : Subgroup G} (hS : ∀ g, g ∈ S ↔ ∃ p : Pt, p.1 < 256 ∧ Φ p = g)
    (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν (Φ fPt)))
    (hJ : ∀ v, v ∈ J ↔ v ∈ S ∧ ∀ x ∈ X, v * x * v⁻¹ * x⁻¹ = 1 ∨ v * x * v⁻¹ * x⁻¹ = Φ fPt)
    {p : Pt} (hp : p.1 < 256) : Φ p ∈ J ↔ inJ p = true := by
  have hf : fPt.1 < 256 := by decide
  rw [hJ, inJ_iff]
  constructor
  · rintro ⟨-, h⟩ x hx
    have hx256 := (mem_xPts.mp hx).1
    rcases h (Φ x) ((Φ_mem_X_iff hM hΦ hX hx256).mpr hx) with h1 | h1
    · left
      rw [comm_eq_one_iff'] at h1
      exact (Φ_mul_comm_iff hΦ hp hx256).mp h1
    · right
      rw [comm_eq_iff', ← Φ_mul hΦ hp hx256, ← Φ_mul hΦ hx256 hp,
        ← Φ_mul hΦ hf (pMul_lt hx256 hp)] at h1
      exact Φ_inj hΦ (pMul_lt hp hx256) (pMul_lt hf (pMul_lt hx256 hp)) h1
  · intro h
    refine ⟨(hS _).mpr ⟨p, hp, rfl⟩, fun x hx => ?_⟩
    obtain ⟨q, hq, rfl⟩ := exists_Φ_of_mem_X hM hΦ hX hx
    have hq256 := (mem_xPts.mp hq).1
    rcases h q hq with h1 | h1
    · left
      rw [comm_eq_one_iff']
      exact (Φ_mul_comm_iff hΦ hp hq256).mpr h1
    · right
      rw [comm_eq_iff', ← Φ_mul hΦ hp hq256, ← Φ_mul hΦ hq256 hp,
        ← Φ_mul hΦ hf (pMul_lt hq256 hp), h1]

theorem Φ_mem_centralizer_X_iff {X : Subgroup G}
    (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν (Φ fPt))) {p : Pt} (hp : p.1 < 256) :
    Φ p ∈ centralizer (X : Set G) ↔ inCX p = true := by
  rw [mem_centralizer_iff, inCX_iff]
  constructor
  · intro h x hx
    have hx256 := (mem_xPts.mp hx).1
    exact ((Φ_mul_comm_iff hΦ hx256 hp).mp (h _ ((Φ_mem_X_iff hM hΦ hX hx256).mpr hx))).symm
  · intro h x hx
    obtain ⟨q, hq, rfl⟩ := exists_Φ_of_mem_X hM hΦ hX hx
    exact (Φ_mul_comm_iff hΦ (mem_xPts.mp hq).1 hp).mpr (h q hq).symm

end Coords

section Count

variable (hΦ : Sec3.SzR.SModel L T R μ ν true Φ)
include hΦ

theorem card_inf_centralizer_eq {S : Subgroup G}
    (hS : ∀ g, g ∈ S ↔ ∃ p : Pt, p.1 < 256 ∧ Φ p = g) {q : Pt} (hq : q.1 < 256) :
    Nat.card ↥(S ⊓ centralizer ({Φ q} : Set G)) = cntC q := by
  have hset : ((S ⊓ centralizer ({Φ q} : Set G) : Subgroup G) : Set G) =
      Φ '' (((allPt.filter (cmt q)).toFinset : Finset Pt) : Set Pt) := by
    ext x
    simp only [SetLike.mem_coe, mem_inf, mem_centralizer_singleton_iff, Set.mem_image,
      List.mem_toFinset, List.mem_filter, mem_allPt, cmt_iff]
    constructor
    · rintro ⟨hxS, hxc⟩
      obtain ⟨p, hp, rfl⟩ := (hS x).mp hxS
      exact ⟨p, ⟨hp, (Φ_mul_comm_iff hΦ hp hq).mp hxc⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hc⟩, rfl⟩
      exact ⟨(hS _).mpr ⟨p, hp, rfl⟩, (Φ_mul_comm_iff hΦ hp hq).mpr hc⟩
  have hinj : Set.InjOn Φ (((allPt.filter (cmt q)).toFinset : Finset Pt) : Set Pt) := by
    intro p hp p' hp' h
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, mem_allPt] at hp hp'
    exact Φ_inj hΦ hp.1 hp'.1 h
  change Nat.card ((S ⊓ centralizer ({Φ q} : Set G) : Subgroup G) : Set G) = _
  rw [Nat.card_coe_set_eq, hset, hinj.ncard_image, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (allPt_nodup.filter _), cntC_eq]

theorem card_inf_centralizer_eq_J {J : Subgroup G}
    (hJ : ∀ p : Pt, p.1 < 256 → (Φ p ∈ J ↔ inJ p = true))
    (hJS : ∀ g ∈ J, ∃ p : Pt, p.1 < 256 ∧ Φ p = g) {q : Pt} (hq : q.1 < 256) :
    Nat.card ↥(J ⊓ centralizer ({Φ q} : Set G)) = jPts.countP (cmt q) := by
  have hset : ((J ⊓ centralizer ({Φ q} : Set G) : Subgroup G) : Set G) =
      Φ '' (((jPts.filter (cmt q)).toFinset : Finset Pt) : Set Pt) := by
    ext x
    simp only [SetLike.mem_coe, mem_inf, mem_centralizer_singleton_iff, Set.mem_image,
      List.mem_toFinset, List.mem_filter, mem_jPts, cmt_iff]
    constructor
    · rintro ⟨hxJ, hxc⟩
      obtain ⟨p, hp, rfl⟩ := hJS x hxJ
      exact ⟨p, ⟨⟨hp, (hJ p hp).mp hxJ⟩, (Φ_mul_comm_iff hΦ hp hq).mp hxc⟩, rfl⟩
    · rintro ⟨p, ⟨⟨hp, hpJ⟩, hc⟩, rfl⟩
      exact ⟨(hJ p hp).mpr hpJ, (Φ_mul_comm_iff hΦ hp hq).mpr hc⟩
  have hinj : Set.InjOn Φ (((jPts.filter (cmt q)).toFinset : Finset Pt) : Set Pt) := by
    intro p hp p' hp' h
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, mem_jPts] at hp hp'
    exact Φ_inj hΦ hp.1.1 hp'.1.1 h
  change Nat.card ((J ⊓ centralizer ({Φ q} : Set G) : Subgroup G) : Set G) = _
  rw [Nat.card_coe_set_eq, hset, hinj.ncard_image, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (jPts_nodup.filter _), List.countP_eq_length_filter]

theorem card_S {S : Subgroup G} (hS : ∀ g, g ∈ S ↔ ∃ p : Pt, p.1 < 256 ∧ Φ p = g) :
    Nat.card S = 2 ^ 14 := by
  let e : Fin 256 × Fin 8 × Fin 8 → S := fun p =>
    ⟨Φ (p.1.val, p.2.1, p.2.2), (hS _).mpr ⟨(p.1.val, p.2.1, p.2.2), p.1.isLt, rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨c, t, d⟩ ⟨c', t', d'⟩ h
      have h1 := Φ_inj hΦ c.isLt c'.isLt (congrArg Subtype.val h)
      simp only [Prod.mk.injEq] at h1
      obtain ⟨h2, rfl, rfl⟩ := h1
      rw [Fin.ext h2]
    · rintro ⟨g, hg⟩
      obtain ⟨⟨c, t, d⟩, hc, rfl⟩ := (hS g).mp hg
      exact ⟨(⟨c, hc⟩, t, d), rfl⟩
  rw [← Nat.card_eq_of_bijective e he, Nat.card_prod, Nat.card_prod, Nat.card_fin, Nat.card_fin]
  norm_num

end Count

@[expose] def wR : List Lin8 :=
  [(1, 4, 6), (1, 5, 7), (1, 5, 3), (1, 5, 3), (1, 5, 6), (1, 4, 7), (1, 4, 2), (1, 4, 2)]

@[expose] def wM : List ℕ := [20, 31, 25, 12, 55, 63, 76, 4]

omit [Group G] in
theorem wR_spec : ∀ i : Fin 8, wR.getD i linId ∈ glList ∧ linApply (wR.getD i linId) 1 = 1 := by
  decide +kernel

omit [Group G] in
theorem wM_spec : ∀ i : Fin 8, wM.getD i 0 < 256 ∧
    maskApply (adMat (wR.getD i linId)) (wM.getD i 0) ^^^ wM.getD i 0 = sBasis.getD i 0 := by
  decide +kernel

theorem mem_map_ker {H : Subgroup G} {A : Type*} [Group A] {χ : H →* A} {x : G} :
    x ∈ (χ.ker).map H.subtype ↔ ∃ hx : x ∈ H, χ ⟨x, hx⟩ = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem R_le_ker [Finite G] (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168) {f : G} (hfA : f ∈ gmsA L T)
    (hν : ν f = 1) {A : Type*} [CommGroup A] (χ : centralizer ({f} : Set G) →* A)
    (hχA : gmsA L T ≤ (χ.ker).map (centralizer ({f} : Set G)).subtype) :
    R ≤ (χ.ker).map (centralizer ({f} : Set G)).subtype := by
  set K := (χ.ker).map (centralizer ({f} : Set G)).subtype with hK
  have hRf : ∀ x ∈ R, x ∈ centralizer ({f} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hM.central x hx f hfA)
  have hκ : ∀ i : ℕ, ∃ k ∈ R, k ∈ K ∧ (i < 8 → μ k = sBasis.getD i 0) := by
    intro i
    by_cases hi : i < 8
    · obtain ⟨hr, hr1⟩ := wR_spec ⟨i, hi⟩
      obtain ⟨hm, hmb⟩ := wM_spec ⟨i, hi⟩
      obtain ⟨g, hgN, hgA, hgR⟩ := hM.exists_code_eq hNC hidx hr
      obtain ⟨x, hxR, hxμ⟩ := hM.surj _ hm
      have hgf : g ∈ centralizer ({f} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        have h1 := hM.eq_of_ν_eq (hM.normA g hgN f hfA) hfA (by
          rw [hgA f hfA, hν]
          exact hr1)
        calc g * f = g * f * g⁻¹ * g := by group
          _ = f * g := by rw [h1]
      have hgxR : g * x * g⁻¹ ∈ R := (mem_normalizer_iff.mp hgN x).mp hxR
      refine ⟨g * x * g⁻¹ * x⁻¹, mul_mem hgxR (inv_mem hxR), ?_, fun _ => ?_⟩
      · refine mem_map_ker.mpr ⟨mul_mem (mul_mem (mul_mem hgf (hRf x hxR)) (inv_mem hgf))
          (inv_mem (hRf x hxR)), ?_⟩
        have he : (⟨g * x * g⁻¹ * x⁻¹, mul_mem (mul_mem (mul_mem hgf (hRf x hxR)) (inv_mem hgf))
            (inv_mem (hRf x hxR))⟩ : centralizer ({f} : Set G)) =
            ⟨g, hgf⟩ * ⟨x, hRf x hxR⟩ * ⟨g, hgf⟩⁻¹ * ⟨x, hRf x hxR⟩⁻¹ := rfl
        rw [he, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (χ ⟨g, hgf⟩)]
        group
      · rw [hM.mul _ hgxR _ (inv_mem hxR), hM.μ_inv hxR, hgR x hxR, hxμ]
        simpa using hmb
    · exact ⟨1, one_mem _, one_mem _, fun h => absurd h hi⟩
  choose κ hκR hκK hκμ using hκ
  intro r hr
  set c := cOf (μ r)
  have h1 : secN κ c 8 ∈ R := Sec3.SzR.MaskCoords.secN_mem hκR c 8
  have h2 : secN κ c 8 ∈ K := Sec3.SzR.MaskCoords.secN_mem (R := K) hκK c 8
  have h3 : μ (secN κ c 8) = μ r := by
    rw [hM.μ_secN hκR (fun j hj => hκμ j hj) c le_rfl]
    exact sMask_cOf (hM.lt r hr)
  have h4 : (secN κ c 8)⁻¹ * r ∈ gmsA L T := by
    rw [← hM.ker _ (mul_mem (inv_mem h1) hr), hM.mul _ (inv_mem h1) _ hr, hM.μ_inv h1, h3,
      Nat.xor_self]
  have h5 := mul_mem h2 (hχA h4)
  rwa [mul_inv_cancel_left] at h5

omit [Group G] in
theorem evenD_mem : ∀ d : Fin 8, evenD d = true → d ∈ ([0, 1, 4, 5] : List (Fin 8)) := by
  decide

theorem Φ_mul_inv_mem_R (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hΦ : Sec3.SzR.SModel L T R μ ν true Φ)
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R) {p q : Pt}
    (hd : p.2.2 = q.2.2) : Φ p * (Φ q)⁻¹ ∈ R := by
  refine hM.mem_of_code_eq_linId hNC (mul_mem (hΦ.mem p) (inv_mem (hΦ.mem q))) fun b hb => ?_
  have hb' := hM.inv_conj_mem (hΦ.mem q) hb
  have h1 := hΦ.code q _ hb'
  rw [show Φ q * ((Φ q)⁻¹ * b * Φ q) * (Φ q)⁻¹ = b by group] at h1
  rw [show Φ p * (Φ q)⁻¹ * b * (Φ p * (Φ q)⁻¹)⁻¹ = Φ p * ((Φ q)⁻¹ * b * Φ q) * (Φ p)⁻¹ by group,
    hΦ.code p _ hb', hd, ← h1, linApply_linId']

theorem Φ_mem_iff_evenD (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hΦ : Sec3.SzR.SModel L T R μ ν true Φ)
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R) {S X J K : Subgroup G}
    (hS : ∀ g, g ∈ S ↔ ∃ p : Pt, p.1 < 256 ∧ Φ p = g)
    (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν (Φ fPt)))
    (hJ : ∀ v, v ∈ J ↔ v ∈ S ∧ ∀ x ∈ X, v * x * v⁻¹ * x⁻¹ = 1 ∨ v * x * v⁻¹ * x⁻¹ = Φ fPt)
    (hRK : R ≤ K) (hJK : J ≤ K) (hSK : ¬ S ≤ K) {p : Pt} (hp : p.1 < 256) :
    Φ p ∈ K ↔ evenD p.2.2 = true := by
  have heven : ∀ q : Pt, q.1 < 256 → evenD q.2.2 = true → Φ q ∈ K := by
    intro q hq he
    obtain ⟨j, hj, hjd⟩ := checkJd_spec q.2.2 (evenD_mem _ he)
    have hjJ : Φ j ∈ J := (Φ_mem_J_iff hM hΦ hS hX hJ (mem_jPts.mp hj).1).mpr (mem_jPts.mp hj).2
    have h1 := Φ_mul_inv_mem_R hM hΦ hNC (p := q) (q := j) hjd.symm
    have h2 := mul_mem (hRK h1) (hJK hjJ)
    rwa [inv_mul_cancel_right] at h2
  refine ⟨fun hpK => ?_, heven p hp⟩
  by_contra hodd
  rw [Bool.not_eq_true] at hodd
  apply hSK
  intro s hs
  obtain ⟨p', hp', rfl⟩ := (hS s).mp hs
  by_cases he : evenD p'.2.2 = true
  · exact heven p' hp' he
  rw [Bool.not_eq_true] at he
  obtain ⟨q, hq, hqe⟩ := (hS _).mp (mul_mem (inv_mem ((hS _).mpr ⟨p, hp, rfl⟩)) hs)
  have h1 : Φ (pMul p q) = Φ p' := by rw [Φ_mul hΦ hp hq, hqe, mul_inv_cancel_left]
  have h2 := Φ_inj hΦ (pMul_lt hp hq) hp' h1
  have h3 : dMul p.2.2 q.2.2 = p'.2.2 := by
    rw [← h2, pMul_eq hp hq, sMul_snd_snd]
  have h4 := evenD_dMul p.2.2 q.2.2 hodd (h3 ▸ he)
  have h5 := mul_mem hpK (heven q hq h4)
  rwa [hqe, mul_inv_cancel_left] at h5

end RuNR

namespace RuNR

variable {G : Type} [Group G]

theorem conj_mem_map_ker_iff {H : Subgroup G} {A : Type*} [CommGroup A] (χ : H →* A) {h : G}
    (hh : h ∈ H) (y : G) : h * y * h⁻¹ ∈ (χ.ker).map H.subtype ↔ y ∈ (χ.ker).map H.subtype := by
  rw [mem_map_ker, mem_map_ker]
  constructor
  · rintro ⟨hy, h1⟩
    have hyH : y ∈ H := by
      have := H.mul_mem (H.mul_mem (H.inv_mem hh) hy) hh
      rwa [show h⁻¹ * (h * y * h⁻¹) * h = y by group] at this
    refine ⟨hyH, ?_⟩
    have he : (⟨h * y * h⁻¹, hy⟩ : H) = ⟨h, hh⟩ * ⟨y, hyH⟩ * ⟨h, hh⟩⁻¹ := rfl
    rw [he, map_mul, map_mul, map_inv, mul_comm (χ ⟨h, hh⟩), mul_inv_cancel_right] at h1
    exact h1
  · rintro ⟨hy, h1⟩
    refine ⟨H.mul_mem (H.mul_mem hh hy) (H.inv_mem hh), ?_⟩
    have he : (⟨h * y * h⁻¹, H.mul_mem (H.mul_mem hh hy) (H.inv_mem hh)⟩ : H) =
      ⟨h, hh⟩ * ⟨y, hy⟩ * ⟨h, hh⟩⁻¹ := rfl
    rw [he, map_mul, map_mul, map_inv, mul_comm (χ ⟨h, hh⟩), mul_inv_cancel_right, h1]

theorem conj_mem_of_ker_eq {H J : Subgroup G} {A : Type*} [Group A] {σ : H →* A}
    (hσ : σ.ker = J.subgroupOf H) (hJH : J ≤ H) {h : G} (hh : h ∈ H) {j : G} (hj : j ∈ J) :
    h * j * h⁻¹ ∈ J := by
  have hjH := hJH hj
  have h1 : (⟨j, hjH⟩ : H) ∈ σ.ker := by
    rw [hσ]
    exact mem_subgroupOf.mpr hj
  have h2 : (⟨h, hh⟩ * ⟨j, hjH⟩ * ⟨h, hh⟩⁻¹ : H) ∈ σ.ker := by
    rw [MonoidHom.mem_ker] at h1 ⊢
    rw [map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel]
  rw [hσ] at h2
  exact mem_subgroupOf.mp h2

theorem conj_mem_centralizer_of_mem_normalizer {X : Subgroup G} {k c : G}
    (hk : k ∈ normalizer (X : Set G)) (hc : c ∈ centralizer (X : Set G)) :
    k * c * k⁻¹ ∈ centralizer (X : Set G) := by
  rw [mem_centralizer_iff] at hc ⊢
  intro x hx
  have hx' : k⁻¹ * x * k ∈ X := by
    have := (mem_normalizer_iff.mp (inv_mem hk) x).mp hx
    simpa using this
  have h1 := hc _ hx'
  calc x * (k * c * k⁻¹) = k * ((k⁻¹ * x * k) * c) * k⁻¹ := by group
    _ = k * (c * (k⁻¹ * x * k)) * k⁻¹ := by rw [h1]
    _ = k * c * k⁻¹ * x := by group

theorem factorization_two (n : ℕ) (hn : ¬ 2 ∣ n) (k : ℕ) : (2 ^ k * n).factorization 2 = k := by
  have hn0 : n ≠ 0 := fun h => hn (h ▸ dvd_zero 2)
  rw [Nat.factorization_mul (by positivity) hn0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hn, add_zero]

end RuNR

namespace RuNR

variable {G : Type} [Group G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8}
  {Φ : ℕ × Fin 8 × Fin 8 → G}

abbrev fPt' : ℕ × Fin 8 × Fin 8 := (0, 1, 0)

omit [Group G] in
theorem fix_dCode : ∀ t : Fin 8, (∀ d : Fin 8, linApply (dCode d) t = t) → t = 0 ∨ t = 1 := by
  decide

theorem isSylowOf_image [Finite G] (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168)
    (hΦ : Sec3.SzR.SModel L T R μ ν true Φ) {S : Subgroup G}
    (hS : ∀ g, g ∈ S ↔ ∃ p : ℕ × Fin 8 × Fin 8, p.1 < 256 ∧ Φ p = g) :
    IsSylowOf 2 S (normalizer (R : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSN' : S ≤ normalizer (R : Set G) := fun s hs => by
    obtain ⟨p, -, rfl⟩ := (hS s).mp hs
    exact hΦ.mem p
  have hcardN : Nat.card (normalizer (R : Set G)) = 2 ^ 14 * 21 := by
    have h := Subgroup.relIndex_mul_card R (normalizer (R : Set G))
    rw [hidx, inf_eq_left.mpr le_normalizer, hM.card_R] at h
    omega
  exact isSylowOf_of_card hSN' (by rw [card_S hΦ hS, hcardN, factorization_two 21 (by norm_num)])

end RuNR

namespace Sec3.SzR.MaskCoords

variable {G : Type} [Group G] [Finite G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8}
  (hM : MaskCoords L T R μ ν)
include hM

theorem exists_perm_five_of_plane (hRp : IsPGroup 2 R)
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168)
    (hNA : normalizer (gmsA L T : Set G) = normalizer (R : Set G))
    (h216 : ∀ F₁ : Subgroup G, F₁ ≤ gmsA L T → Nat.card F₁ = 4 →
      normalizer (F₁ : Set G) ≤ normalizer (R : Set G))
    {S : Subgroup G} (hSN : IsSylowOf 2 S (normalizer (R : Set G))) (hRS : R ≤ S) {f : G}
    (hfA : f ∈ gmsA L T) (hf1 : f ≠ 1) (hfS : ∀ s ∈ S, s * f * s⁻¹ = f)
    (h210 : ∀ g ∈ S, g ∉ R → g ^ 2 ∈ R → ∃ y ∈ S, y ^ 2 = 1 ∧ g⁻¹ * y ∈ R)
    {X : Subgroup G} (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f))
    {J : Subgroup G} (hJ : ∀ v, v ∈ J ↔ v ∈ S ∧ ∀ x ∈ X,
      v * x * v⁻¹ * x⁻¹ = 1 ∨ v * x * v⁻¹ * x⁻¹ = f)
    (hXH : centralizer ({f} : Set G) ≤ normalizer (X : Set G))
    (hnot : ¬ centralizer ({f} : Set G) ≤ normalizer (gmsA L T : Set G)) :
    ∃ σ : centralizer ({f} : Set G) →* Equiv.Perm (Fin 5), Function.Surjective σ ∧
      σ.ker = J.subgroupOf (centralizer ({f} : Set G)) := by
  classical
  have hXel := hM.isElemAbelian_plane hX
  have hcardX := hM.card_plane hX hfA hf1
  have hfX : f ∈ X := hM.gmsA_le_plane hX hfA
  have hof : orderOf f = 2 := orderOf_eq_prime (hXel.2 f hfX) hf1
  have hZ : ∀ x : G, x ∈ zpowers f ↔ x = 1 ∨ x = f := by
    intro x
    rw [mem_zpowers_iff_mem_range_orderOf, hof]
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      rw [Finset.mem_range] at ha
      interval_cases a
      · exact Or.inl (pow_zero f)
      · exact Or.inr (pow_one f)
    · rintro (h | h)
      · exact Finset.mem_image.2 ⟨0, by simp, by rw [h, pow_zero]⟩
      · exact Finset.mem_image.2 ⟨1, by simp, by rw [h, pow_one]⟩
  have hcardZ : Nat.card (zpowers f) = 2 := by rw [Nat.card_zpowers, hof]
  have hHZ : ∀ h ∈ centralizer ({f} : Set G), ∀ z ∈ zpowers f, h * z * h⁻¹ = z := by
    intro h hh z hz
    rcases (hZ z).1 hz with rfl | rfl
    · group
    · rw [mem_centralizer_singleton_iff.1 hh]
      group
  have hHX : ∀ h ∈ centralizer ({f} : Set G), ∀ x ∈ X, h * x * h⁻¹ ∈ X :=
    fun h hh x hx => (mem_normalizer_iff.1 (hXH hh) x).1 hx
  have hJ' : ∀ h, h ∈ J ↔ h ∈ centralizer ({f} : Set G) ∧
      ∀ x ∈ X, h * x * h⁻¹ * x⁻¹ ∈ zpowers f := by
    intro h
    rw [hM.mem_J_iff_of_mem_centralizer hNC hidx hNA hRp hSN hRS hfA hf1 hfS hX hJ h]
    simp only [hZ]
  have hidx120 := hM.relIndex_J_eq hRp hNC hidx h216 hSN hRS hfA hf1 hfS h210 hX hJ hXH hnot
  have htr : ∀ x ∈ X, x ∉ zpowers f → ∀ x' ∈ X, x' ∉ zpowers f →
      ∃ h ∈ centralizer ({f} : Set G), h * x * h⁻¹ * x'⁻¹ ∈ zpowers f := by
    intro x hx hxZ x' hx' hx'Z
    have hne : ∀ y, y ∉ zpowers f → y ≠ 1 ∧ y ≠ f := fun y hy =>
      ⟨fun h => hy ((hZ y).2 (Or.inl h)), fun h => hy ((hZ y).2 (Or.inr h))⟩
    obtain ⟨hx1, hxf⟩ := hne x hxZ
    obtain ⟨hx'1, hx'f⟩ := hne x' hx'Z
    obtain ⟨h, hh, hhx⟩ :=
      hM.exists_conj_eq_of_mem_plane hNC hidx hfA hf1 hX hXH hnot hx hx1 hxf hx' hx'1 hx'f
    refine ⟨h, hh, ?_⟩
    rw [hhx, mul_inv_cancel]
    exact one_mem _
  exact (RuGamma.dempwolff218 hXel hcardX (zpowers_le.2 hfX) hcardZ hHZ hHX hJ' hidx120 htr).1

theorem false_of_sModel_true (hRp : IsPGroup 2 R)
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168)
    (hNA : normalizer (gmsA L T : Set G) = normalizer (R : Set G))
    (h216 : ∀ F₁ : Subgroup G, F₁ ≤ gmsA L T → Nat.card F₁ = 4 →
      normalizer (F₁ : Set G) ≤ normalizer (R : Set G))
    {Φ : ℕ × Fin 8 × Fin 8 → G} (hΦ : SModel L T R μ ν true Φ) {S : Subgroup G}
    (hS : ∀ g, g ∈ S ↔ ∃ p : ℕ × Fin 8 × Fin 8, p.1 < 256 ∧ Φ p = g) {X : Subgroup G}
    (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν (Φ (0, 1, 0)))) {J : Subgroup G}
    (hJ : ∀ v, v ∈ J ↔ v ∈ S ∧ ∀ x ∈ X,
      v * x * v⁻¹ * x⁻¹ = 1 ∨ v * x * v⁻¹ * x⁻¹ = Φ (0, 1, 0))
    (hXH : centralizer ({Φ (0, 1, 0)} : Set G) ≤ normalizer (X : Set G))
    (hnot : ¬ centralizer ({Φ (0, 1, 0)} : Set G) ≤ normalizer (gmsA L T : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfdef : (0, 1, 0) = fPt := rfl
  rw [hfdef] at hX hJ hXH hnot
  set f := Φ fPt with hf
  have hfA : f ∈ gmsA L T := hΦ.mem_A 1
  have hf1 : f ≠ 1 := RuNR.Φ_fPt_ne_one hM hΦ
  have hfS : ∀ s ∈ S, s * f * s⁻¹ = f := fun s hs => by
    obtain ⟨p, -, rfl⟩ := (hS s).mp hs
    exact RuNR.Φ_conj_fPt hM hΦ p
  have hSN' : S ≤ normalizer (R : Set G) := fun s hs => by
    obtain ⟨p, -, rfl⟩ := (hS s).mp hs
    exact hΦ.mem p
  have hRS : R ≤ S := fun r hr => by
    obtain ⟨p, hp, -, rfl⟩ := RuNR.exists_Φ_of_mem_R hM hΦ hr
    exact (hS _).mpr ⟨p, hp, rfl⟩
  have hcardS : Nat.card S = 2 ^ 14 := RuNR.card_S hΦ hS
  have hS2 : IsPGroup 2 S := IsPGroup.of_card hcardS
  have hcardN : Nat.card (normalizer (R : Set G)) = 2 ^ 14 * 21 := by
    have h := Subgroup.relIndex_mul_card R (normalizer (R : Set G))
    rw [hidx, inf_eq_left.mpr le_normalizer, hM.card_R] at h
    omega
  have hSN : IsSylowOf 2 S (normalizer (R : Set G)) :=
    isSylowOf_of_card hSN' (by rw [hcardS, hcardN, RuNR.factorization_two 21 (by norm_num)])
  have h210 := hM.exists_sq_eq_one_inv_mul_mem_of_le hNC hidx hSN' hRS
  obtain ⟨hcardJ, hXJ, hJS, -⟩ := hM.J_props hRp hNC hidx hSN hRS hfA hf1 hfS h210 hX hJ
  set H := centralizer ({f} : Set G) with hH
  obtain ⟨σ, hσs, hσk⟩ :=
    hM.exists_perm_five_of_plane hRp hNC hidx hNA h216 hSN hRS hfA hf1 hfS h210 hX hJ hXH hnot
  set χ : H →* ℤˣ := Equiv.Perm.sign.comp σ with hχ
  set K := (χ.ker).map H.subtype with hK
  have hSH : S ≤ H := fun s hs => mem_centralizer_singleton_iff.mpr (by
    calc s * f = s * f * s⁻¹ * s := by group
      _ = f * s := by rw [hfS s hs])
  have hJH : J ≤ H := hJS.trans hSH
  have hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J := fun h hh j hj =>
    RuNR.conj_mem_of_ker_eq hσk hJH hh hj
  have hJK : J ≤ K := by
    intro j hj
    refine RuNR.mem_map_ker.mpr ⟨hJH hj, ?_⟩
    have h1 : (⟨j, hJH hj⟩ : H) ∈ σ.ker := by
      rw [hσk]
      exact mem_subgroupOf.mpr hj
    rw [MonoidHom.mem_ker] at h1
    show Equiv.Perm.sign (σ ⟨j, hJH hj⟩) = 1
    rw [h1, map_one]
  have hAK : gmsA L T ≤ K := (hM.gmsA_le_plane hX).trans (hXJ.trans hJK)
  have hRK : R ≤ K := RuNR.R_le_ker hM hNC hidx hfA (RuNR.ν_Φ_fPt hΦ) χ hAK
  have hidx120 := hM.relIndex_J_eq hRp hNC hidx h216 hSN hRS hfA hf1 hfS h210 hX hJ hXH hnot
  have hcardH : Nat.card H = 2 ^ 14 * 15 := by
    have h := Subgroup.relIndex_mul_card J H
    rw [hidx120, inf_eq_left.mpr hJH, hcardJ] at h
    omega
  have hχs : Function.Surjective χ := (Equiv.Perm.sign_surjective (α := Fin 5)).comp hσs
  have hkerχ : Nat.card χ.ker * 2 = Nat.card H := by
    have h1 := χ.ker.card_mul_index
    have h2 : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hχs, Subgroup.card_top, h2] at h1
    exact h1
  have hSK : ¬ S ≤ K := by
    intro hle
    have h1 : S.subgroupOf H ≤ χ.ker := fun s hs => by
      obtain ⟨hx, hχx⟩ := RuNR.mem_map_ker.mp (hle (mem_subgroupOf.mp hs))
      exact hχx
    have h2 := Subgroup.card_dvd_of_le h1
    rw [Nat.card_congr (subgroupOfEquivOfLe hSH).toEquiv, hcardS] at h2
    have h3 : Nat.card χ.ker = 2 ^ 13 * 15 := by omega
    rw [h3] at h2
    norm_num at h2
  have hpar : ∀ p : ℕ × Fin 8 × Fin 8, p.1 < 256 → (Φ p ∈ K ↔ evenD p.2.2 = true) :=
    fun p hp => RuNR.Φ_mem_iff_evenD hM hΦ hNC hS hX hJ hRK hJK hSK hp
  have hodd : ∀ h ∈ H, ∀ y : G, h * y * h⁻¹ ∉ K ↔ y ∉ K := fun h hh y =>
    not_congr (RuNR.conj_mem_map_ker_iff χ hh y)
  have hJiff : ∀ p : ℕ × Fin 8 × Fin 8, p.1 < 256 → (Φ p ∈ J ↔ inJ p = true) :=
    fun p hp => RuNR.Φ_mem_J_iff hM hΦ hS hX hJ hp
  have hXiff : ∀ p : ℕ × Fin 8 × Fin 8, p.1 < 256 →
      (Φ p ∈ centralizer (X : Set G) ↔ inCX p = true) :=
    fun p hp => RuNR.Φ_mem_centralizer_X_iff hM hΦ hX hp
  obtain ⟨hAJ, hAX, hAsq⟩ := RuNR.checkA_spec
  have hA256 : aPt.1 < 256 := by decide
  have haJ : Φ aPt ∈ J := (hJiff aPt hA256).mpr hAJ
  have haX : Φ aPt ∉ centralizer (X : Set G) := fun h => by
    rw [hXiff aPt hA256, hAX] at h
    exact absurd h (by decide)
  have ha2 : Φ aPt ^ 2 = 1 := (RuNR.Φ_sq_eq_one_iff hΦ hA256).mpr hAsq
  have hSyl : IsSylowOf 2 S H :=
    isSylowOf_of_card hSH (by rw [hcardS, hcardH, RuNR.factorization_two 15 (by norm_num)])
  have hCa : Nat.card ↥(S ⊓ centralizer ({Φ aPt} : Set G)) = 1024 := by
    rw [RuNR.card_inf_centralizer_eq hΦ hS hA256, RuNR.checkCa_spec]
  have hJS8 : J.relIndex S = 8 := by
    have h := Subgroup.relIndex_mul_card J S
    rw [inf_eq_left.mpr hJS, hcardJ, hcardS] at h
    omega
  have hbound : ∀ x ∈ J, x ∉ centralizer (X : Set G) → x ^ 2 = 1 →
      Nat.card ↥(S ⊓ centralizer ({x} : Set G)) ≤ 1024 := by
    intro x hxJ hxX hx2
    obtain ⟨q, hq, rfl⟩ := (hS _).mp (hJS hxJ)
    have hqJ := (hJiff q hq).mp hxJ
    have hqX : inCX q = false := by
      by_contra h
      rw [Bool.not_eq_false] at h
      exact hxX ((hXiff q hq).mpr h)
    have hq2 := (RuNR.Φ_sq_eq_one_iff hΦ hq).mp hx2
    have h128 := RuNR.checkCx_spec q (RuNR.mem_jPts.mpr ⟨hq, hqJ⟩) hqX hq2
    have hJx : Nat.card ↥(J ⊓ centralizer ({Φ q} : Set G)) ≤ 128 := by
      rw [RuNR.card_inf_centralizer_eq_J hΦ hJiff (fun g hg => (hS g).mp (hJS hg)) hq]
      exact h128
    have h1 := Subgroup.relIndex_mul_card J (S ⊓ centralizer ({Φ q} : Set G))
    rw [← inf_assoc, inf_eq_left.mpr hJS] at h1
    have h3 : J.relIndex (S ⊓ centralizer ({Φ q} : Set G)) ≤ 8 :=
      hJS8 ▸ Subgroup.relIndex_le_of_le_right inf_le_left (by rw [hJS8]; norm_num)
    rw [← h1]
    calc J.relIndex (S ⊓ centralizer ({Φ q} : Set G)) *
          Nat.card ↥(J ⊓ centralizer ({Φ q} : Set G)) ≤ 8 * 128 := Nat.mul_le_mul h3 hJx
      _ = 1024 := by norm_num
  have hmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ H ⊓ centralizer ({Φ aPt} : Set G) →
      S ⊓ centralizer ({Φ aPt} : Set G) ≤ P → P = S ⊓ centralizer ({Φ aPt} : Set G) := by
    intro P hP hPle hle
    obtain ⟨P', hP', hPP'⟩ := RuNR.exists_isSylowOf_ge_of_le (hPle.trans inf_le_left) hP
    obtain ⟨k, hkH, hk⟩ := hSyl.exists_mem_conj hP'
    have ha'J : k⁻¹ * Φ aPt * k ∈ J := by
      have := hJn k⁻¹ (H.inv_mem hkH) _ haJ
      rwa [inv_inv] at this
    have ha'X : k⁻¹ * Φ aPt * k ∉ centralizer (X : Set G) := fun h => by
      apply haX
      have := RuNR.conj_mem_centralizer_of_mem_normalizer (hXH hkH) h
      rwa [show k * (k⁻¹ * Φ aPt * k) * k⁻¹ = Φ aPt by group] at this
    have ha'2 : (k⁻¹ * Φ aPt * k) ^ 2 = 1 := by
      rw [show (k⁻¹ * Φ aPt * k) ^ 2 = k⁻¹ * Φ aPt ^ 2 * k by rw [pow_two, pow_two]; group, ha2]
      group
    have hinj : Nat.card P ≤ Nat.card ↥(S ⊓ centralizer ({k⁻¹ * Φ aPt * k} : Set G)) := by
      have hmem : ∀ x : P, k⁻¹ * (x : G) * k ∈ S ⊓ centralizer ({k⁻¹ * Φ aPt * k} : Set G) := by
        intro x
        refine mem_inf.mpr ⟨(hk x).mp (hPP' x.2), ?_⟩
        have := RuNR.mem_centralizer_conj (h := k⁻¹) (mem_inf.mp (hPle x.2)).2
        simpa using this
      refine Nat.card_le_card_of_injective (fun x : P => (⟨k⁻¹ * x * k, hmem x⟩ :
            ↥(S ⊓ centralizer ({k⁻¹ * Φ aPt * k} : Set G)))) ?_
      intro x y hxy
      have h1 : k⁻¹ * (x : G) * k = k⁻¹ * y * k := congrArg Subtype.val hxy
      exact Subtype.ext (by simpa using h1)
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    calc Nat.card P ≤ Nat.card ↥(S ⊓ centralizer ({k⁻¹ * Φ aPt * k} : Set G)) := hinj
      _ ≤ 1024 := hbound _ ha'J ha'X ha'2
      _ = Nat.card ↥(S ⊓ centralizer ({Φ aPt} : Set G)) := hCa.symm
  have hF1 : ∀ y ∈ S ⊓ centralizer ({Φ aPt} : Set G), y ^ 2 ∈ J → y ∉ J → y ∉ K →
      ∃ j ∈ J ⊓ centralizer ({Φ aPt} : Set G), (y * j) ^ 2 = 1 := by
    intro y hy hy2 hyJ hyK
    obtain ⟨hyS, hyc⟩ := mem_inf.mp hy
    obtain ⟨p, hp, rfl⟩ := (hS _).mp hyS
    have h1 : cmt aPt p = true := RuNR.cmt_iff.mpr
      ((RuNR.Φ_mul_comm_iff hΦ hp hA256).mp (mem_centralizer_singleton_iff.mp hyc))
    have hp2 : (sqPt p).1 < 256 := RuNR.pMul_lt hp hp
    have h2 : jMem (sqPt p) = true := by
      rw [RuNR.jMem_eq hp2]
      rw [RuNR.Φ_sq hΦ hp] at hy2
      exact (hJiff _ hp2).mp hy2
    have h3 : jMem p = false := by
      rw [RuNR.jMem_eq hp]
      by_contra h
      rw [Bool.not_eq_false] at h
      exact hyJ ((hJiff p hp).mpr h)
    have h4 : evenD p.2.2 = false := by
      by_contra h
      rw [Bool.not_eq_false] at h
      exact hyK ((hpar p hp).mpr h)
    obtain ⟨j, hj, hjc, hjsq⟩ := RuNR.checkF1_spec p (RuNR.mem_allPt.mpr hp) h1 h2 h3 h4
    obtain ⟨hj256, hjJ⟩ := RuNR.mem_jPts.mp hj
    refine ⟨Φ j, mem_inf.mpr ⟨(hJiff j hj256).mpr hjJ, mem_centralizer_singleton_iff.mpr
      ((RuNR.Φ_mul_comm_iff hΦ hj256 hA256).mpr (RuNR.cmt_iff.mp hjc))⟩, ?_⟩
    rw [← RuNR.Φ_mul hΦ hp hj256, RuNR.Φ_sq_eq_one_iff hΦ (RuNR.pMul_lt hp hj256)]
    exact hjsq
  obtain ⟨hCJ, hCX, hF3⟩ := RuNR.checkF3_spec
  have hC256 : cPt.1 < 256 := by decide
  have hcJ : Φ cPt ∈ J := (hJiff cPt hC256).mpr hCJ
  have hcX : Φ cPt ∉ centralizer (X : Set G) := fun h => by
    rw [hXiff cPt hC256, hCX] at h
    exact absurd h (by decide)
  obtain ⟨h, hh, hhk⟩ := hM.exists_conj_mem_centralizer_plane hRp hNC hidx hNA h216 hSN hRS hfA
    hf1 hfS h210 hX hJ hXH hnot haJ hcJ haX hcX
  obtain ⟨hkJ, hkX⟩ := mem_inf.mp hhk
  obtain ⟨q, hq, hqe⟩ := (hS _).mp (hJS hkJ)
  have hqJ : inJ q = true := (hJiff q hq).mp (hqe ▸ hkJ)
  have hqX : inCX q = true := (hXiff q hq).mp (hqe ▸ hkX)
  have hqc := RuNR.pMul_lt hq hC256
  have hc_eq : h * Φ aPt * h⁻¹ = Φ (pMul q cPt) := by
    rw [RuNR.Φ_mul hΦ hq hC256, hqe]
    group
  have hc2 : sqPt (pMul q cPt) = onePt := by
    rw [← RuNR.Φ_sq_eq_one_iff hΦ hqc, ← hc_eq,
      show (h * Φ aPt * h⁻¹) ^ 2 = h * Φ aPt ^ 2 * h⁻¹ by rw [pow_two, pow_two]; group, ha2]
    group
  obtain ⟨u, hu, huc, hu2, huJ, hue, hu3⟩ :=
    hF3 q (RuNR.mem_jPts.mpr ⟨hq, hqJ⟩) hqX hc2
  have hu256 := RuNR.mem_allPt.mp hu
  have hu2' : (sqPt u).1 < 256 := RuNR.pMul_lt hu256 hu256
  refine RuNR.false_of_transport (fun y => y ∉ K) hJn hodd hSH hS2 hmax hF1 hh (u := Φ u)
    (mem_inf.mpr ⟨(hS _).mpr ⟨u, hu256, rfl⟩, ?_⟩) ?_ ?_ ?_ ?_
  · rw [hc_eq, mem_centralizer_singleton_iff]
    exact (RuNR.Φ_mul_comm_iff hΦ hu256 hqc).mpr (RuNR.cmt_iff.mp huc)
  · rw [RuNR.Φ_sq hΦ hu256]
    rw [RuNR.jMem_eq hu2'] at hu2
    exact (hJiff _ hu2').mpr hu2
  · intro huJ'
    rw [RuNR.jMem_eq hu256, (hJiff u hu256).mp huJ'] at huJ
    exact absurd huJ (by decide)
  · intro huK
    rw [(hpar u hu256).mp huK] at hue
    exact absurd hue (by decide)
  · intro j hj
    obtain ⟨hjJ', hjc⟩ := mem_inf.mp hj
    obtain ⟨j', hj', rfl⟩ := (hS _).mp (hJS hjJ')
    have h1 : cmt (pMul q cPt) j' = true := by
      rw [hc_eq, mem_centralizer_singleton_iff] at hjc
      exact RuNR.cmt_iff.mpr ((RuNR.Φ_mul_comm_iff hΦ hj' hqc).mp hjc)
    have h2 := hu3 j' (RuNR.mem_jPts.mpr ⟨hj', (hJiff j' hj').mp hjJ'⟩) h1
    rw [← RuNR.Φ_mul hΦ hu256 hj', ne_eq, RuNR.Φ_sq_eq_one_iff hΦ (RuNR.pMul_lt hu256 hj')]
    exact h2

omit [Finite G] in
theorem mem_plane_conj_iff {n : G} (hnN : n ∈ normalizer (R : Set G)) {f : G}
    (hfA : f ∈ gmsA L T) {X X' : Subgroup G}
    (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f))
    (hX' : ∀ x, x ∈ X' ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν (n⁻¹ * f * n))) (x : G) :
    x ∈ X' ↔ n * x * n⁻¹ ∈ X := by
  obtain ⟨r, hr, hrA, hrR⟩ := hM.act n hnN
  obtain ⟨r', hr', hr'A, hr'R⟩ := hM.act n⁻¹ (inv_mem hnN)
  have hplane : ∀ {s : Lin8}, s ∈ glList → ∀ {t : Fin 8} {m : ℕ}, m ∈ 0 :: RuQCode.ppOf t →
      maskApply (adMat s) m ∈ 0 :: RuQCode.ppOf (linApply s t) := by
    intro s hs t m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · rw [RuQCode.maskApply_zero]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (RuQCode.ppOf_equiv hs hm)
  have hfA' : n⁻¹ * f * n ∈ gmsA L T := hM.inv_conj_mem hnN hfA
  rw [hX', hX]
  constructor
  · rintro ⟨hxR, hxm⟩
    refine ⟨(mem_normalizer_iff.mp hnN x).mp hxR, ?_⟩
    have h1 := hplane hr hxm
    rw [← hrR x hxR, ← hrA _ hfA', show n * (n⁻¹ * f * n) * n⁻¹ = f by group] at h1
    exact h1
  · rintro ⟨hyR, hym⟩
    have hxR : x ∈ R := by
      have := (mem_normalizer_iff.mp (inv_mem hnN) _).mp hyR
      rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at this
    refine ⟨hxR, ?_⟩
    have h1 := hplane hr' hym
    rw [← hr'R _ hyR, ← hr'A f hfA, show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group,
      inv_inv] at h1
    exact h1

theorem exists_sModel_false (hRp : IsPGroup 2 R)
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168)
    (hNA : normalizer (gmsA L T : Set G) = normalizer (R : Set G))
    (h216 : ∀ F₁ : Subgroup G, F₁ ≤ gmsA L T → Nat.card F₁ = 4 →
      normalizer (F₁ : Set G) ≤ normalizer (R : Set G))
    {S : Subgroup G} (hSN : IsSylowOf 2 S (normalizer (R : Set G))) {f : G}
    (hfA : f ∈ gmsA L T) (hf1 : f ≠ 1) (hfS : ∀ s ∈ S, s * f * s⁻¹ = f) {X : Subgroup G}
    (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f))
    (hXH : centralizer ({f} : Set G) ≤ normalizer (X : Set G))
    (hnot : ¬ centralizer ({f} : Set G) ≤ normalizer (gmsA L T : Set G)) :
    ∃ Φ : ℕ × Fin 8 × Fin 8 → G, SModel L T R μ ν false Φ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ε, Φ, hΦ⟩ := hM.exists_sModel hNC hidx
  cases ε
  · exact ⟨Φ, hΦ⟩
  exfalso
  obtain ⟨S', hS'⟩ : ∃ S' : Subgroup G,
      ∀ g, g ∈ S' ↔ ∃ p : ℕ × Fin 8 × Fin 8, p.1 < 256 ∧ Φ p = g := by
    have hmul : ∀ a b : G, (∃ p : ℕ × Fin 8 × Fin 8, p.1 < 256 ∧ Φ p = a) →
        (∃ p : ℕ × Fin 8 × Fin 8, p.1 < 256 ∧ Φ p = b) →
          ∃ p : ℕ × Fin 8 × Fin 8, p.1 < 256 ∧ Φ p = a * b := by
      rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
      exact ⟨pMul p q, RuNR.pMul_lt hp hq, RuNR.Φ_mul hΦ hp hq⟩
    have hone : ∃ p : ℕ × Fin 8 × Fin 8, p.1 < 256 ∧ Φ p = 1 :=
      ⟨onePt, by decide, RuNR.Φ_one hΦ⟩
    have hpow : ∀ a : G, (∃ p : ℕ × Fin 8 × Fin 8, p.1 < 256 ∧ Φ p = a) → ∀ k : ℕ,
        ∃ p : ℕ × Fin 8 × Fin 8, p.1 < 256 ∧ Φ p = a ^ k := by
      intro a ha k
      induction k with
      | zero => simpa using hone
      | succ k ih => rw [pow_succ]; exact hmul _ _ ih ha
    refine ⟨{ carrier := {g | ∃ p : ℕ × Fin 8 × Fin 8, p.1 < 256 ∧ Φ p = g}
              mul_mem' := fun ha hb => hmul _ _ ha hb
              one_mem' := hone
              inv_mem' := fun {a} ha => ?_ }, fun g => Iff.rfl⟩
    have h1 : a⁻¹ = a ^ (Nat.card G - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
        Nat.sub_one_add_one_eq_of_pos Nat.card_pos, pow_card_eq_one']
    rw [h1]
    exact hpow a ha _
  have hSN' := RuNR.isSylowOf_image hM hidx hΦ hS'
  obtain ⟨n, hnN, hn⟩ := hSN'.exists_mem_conj hSN
  have hfA' : n⁻¹ * f * n ∈ gmsA L T := hM.inv_conj_mem hnN hfA
  have hf' : n⁻¹ * f * n = Φ RuNR.fPt' := by
    have hcen : ∀ p : ℕ × Fin 8 × Fin 8, p.1 < 256 →
        Φ p * (n⁻¹ * f * n) * (Φ p)⁻¹ = n⁻¹ * f * n := by
      intro p hp
      have h1 : n * Φ p * n⁻¹ ∈ S := (hn _).mpr (by
        rw [show n⁻¹ * (n * Φ p * n⁻¹) * n = Φ p by group]
        exact (hS' _).mpr ⟨p, hp, rfl⟩)
      have h2 := hfS _ h1
      calc Φ p * (n⁻¹ * f * n) * (Φ p)⁻¹
          = n⁻¹ * ((n * Φ p * n⁻¹) * f * (n * Φ p * n⁻¹)⁻¹) * n := by group
        _ = n⁻¹ * f * n := by rw [h2]
    have hν : ∀ d : Fin 8, linApply (dCode d) (ν (n⁻¹ * f * n)) = ν (n⁻¹ * f * n) := by
      intro d
      have h1 := hΦ.code (0, 0, d) _ hfA'
      rw [hcen (0, 0, d) (by simp)] at h1
      exact h1.symm
    refine hM.eq_of_ν_eq hfA' (hΦ.mem_A 1) ?_
    rcases RuNR.fix_dCode _ hν with h0 | h1
    · exfalso
      apply hf1
      have h2 := hM.ν_inj _ hfA' h0
      calc f = n * (n⁻¹ * f * n) * n⁻¹ := by group
        _ = 1 := by rw [h2]; group
    · rw [h1, hΦ.ν_eq 1]
  obtain ⟨X', hX'⟩ := hM.exists_plane (Φ RuNR.fPt')
  have hX'' : ∀ x, x ∈ X' ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν (n⁻¹ * f * n)) := by
    rw [hf']
    exact hX'
  have hconjX : ∀ x, x ∈ X' ↔ n * x * n⁻¹ ∈ X := hM.mem_plane_conj_iff hnN hfA hX hX''
  have hcentf : ∀ g : G, g ∈ centralizer ({Φ RuNR.fPt'} : Set G) →
      n * g * n⁻¹ ∈ centralizer ({f} : Set G) := by
    intro g hg
    rw [← hf', mem_centralizer_singleton_iff] at hg
    rw [mem_centralizer_singleton_iff]
    calc n * g * n⁻¹ * f = n * (g * (n⁻¹ * f * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * f * n) * g) * n⁻¹ := by rw [hg]
      _ = f * (n * g * n⁻¹) := by group
  have hXH' : centralizer ({Φ RuNR.fPt'} : Set G) ≤ normalizer (X' : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    rw [hconjX, hconjX, show n * (g * x * g⁻¹) * n⁻¹ =
      (n * g * n⁻¹) * (n * x * n⁻¹) * (n * g * n⁻¹)⁻¹ by group]
    exact mem_normalizer_iff.mp (hXH (hcentf g hg)) _
  have hnot' : ¬ centralizer ({Φ RuNR.fPt'} : Set G) ≤ normalizer (gmsA L T : Set G) := by
    intro hle
    apply hnot
    intro g hg
    have h1 : n⁻¹ * g * n ∈ centralizer ({Φ RuNR.fPt'} : Set G) := by
      rw [← hf', mem_centralizer_singleton_iff]
      rw [mem_centralizer_singleton_iff] at hg
      calc n⁻¹ * g * n * (n⁻¹ * f * n) = n⁻¹ * (g * f) * n := by group
        _ = n⁻¹ * (f * g) * n := by rw [hg]
        _ = n⁻¹ * f * n * (n⁻¹ * g * n) := by group
    have hnA : n ∈ normalizer (gmsA L T : Set G) := hNA ▸ hnN
    have h2 := mul_mem (mul_mem hnA (hle h1)) (inv_mem hnA)
    rwa [show n * (n⁻¹ * g * n) * n⁻¹ = g by group] at h2
  have hfA' : Φ RuNR.fPt' ∈ gmsA L T := hΦ.mem_A 1
  have hf2 : Φ RuNR.fPt' * Φ RuNR.fPt' = 1 := by
    have h1 := (hM.sq_eq_one_iff (hM.le hfA')).mpr (by rw [(hM.ker _ (hM.le hfA')).mpr hfA']; rfl)
    rwa [pow_two] at h1
  have hfS' : ∀ s ∈ S', s * Φ RuNR.fPt' * s⁻¹ = Φ RuNR.fPt' := fun s hs => by
    obtain ⟨p, -, rfl⟩ := (hS' s).mp hs
    exact RuNR.Φ_conj_fPt hM hΦ p
  have hSX' : S' ≤ normalizer (X' : Set G) := fun s hs => by
    obtain ⟨p, -, rfl⟩ := (hS' s).mp hs
    exact hM.mem_normalizer_plane hX' (hΦ.mem p) (RuNR.Φ_conj_fPt hM hΦ p) hfA'
  obtain ⟨J', hJ'⟩ := exists_J hf2 hfS' hSX'
  exact hM.false_of_sModel_true hRp hNC hidx hNA h216 hΦ hS' hX' hJ' hXH' hnot'

end Sec3.SzR.MaskCoords

end CFSG.ComponentClassification.GMS78
