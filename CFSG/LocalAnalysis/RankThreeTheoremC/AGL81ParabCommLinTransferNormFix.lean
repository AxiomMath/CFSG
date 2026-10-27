module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferAut
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferLevi
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferDet
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferS3
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferCrt
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGeneric

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial LinearFlag Matrix
  CFSG.AGLEmbedding.LeviBlock
open scoped commutatorElement

theorem odd_card_units (K : Type) [Field K] [Finite K] [CharP K 2] : Odd (Nat.card Kˣ) := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hcard⟩ := FiniteField.card K 2
  rw [Nat.card_units, Nat.card_eq_fintype_card, hcard]
  exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' f.ne_zero).mpr even_two) odd_one

theorem pow_card_units_eq_one_of_mem_scalars {K : Type} [Field K] [Finite K] {n : ℕ}
    {g : SpecialLinearGroup (Fin n) K} (hg : g ∈ scalars n K) : g ^ Nat.card Kˣ = 1 := by
  obtain ⟨c, -, hc⟩ := hg
  have h : ((g ^ Nat.card Kˣ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    have h1 := Matrix.SpecialLinearGroup.coe_pow g (Nat.card Kˣ)
    rw [h1, hc, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one, map_one]
  exact Subtype.ext h

theorem commute_of_lt_two {K : Type} [Field K] {m : ℕ} (hm : m < 2) (g h : GL (Fin m) K) :
    g * h = h * g := by
  rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
  · exact Subsingleton.elim _ _
  · apply Units.ext
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi hj
    simp [Matrix.mul_apply, mul_comm]

theorem three_le_of_two_le_linBlockLen {n : ℕ} {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n)
    (hne : I.Nonempty) {a : Fin n} (ha : 2 ≤ linBlockLen n I a) : 3 ≤ n := by
  have hstart : (a : ℕ) = 0 ∨ (a : ℕ) ∈ I := by
    by_contra h
    have := linBlockLen_of_not_start h
    omega
  obtain ⟨h1, h2, h3, h4⟩ := linBlockLen_spec hstart
  obtain ⟨i, hi⟩ := hne
  obtain ⟨hi1, hin⟩ := hI i hi
  have h5 := h4 i hi
  omega

variable {A : Type} [Group A] [Finite A] {Y P : Subgroup A} {n : ℕ} {K : Type} [Field K]
  [Finite K] [CharP K 2] {I : Set ℕ} (C : LinCover Y P n K I)

theorem LinCover.toP_mem_pCore_of_mem_ker (hPY : P ≤ Y) (hn : 1 ≤ n)
    {u : ↥(flagStabilizer n K I)} (hu : u ∈ (linLeviHom K n I).ker) :
    C.toP u ∈ CFSG.pCore 2 ↥P := by
  have hs := C.toP_surjective hPY
  have hmap : ((linLeviHom K n I).ker.map C.toP) ≤ CFSG.pCore 2 ↥P := by
    have hnorm : ((linLeviHom K n I).ker.map C.toP).Normal := (MonoidHom.normal_ker _).map _ hs
    have hp : IsPGroup 2 ((linLeviHom K n I).ker.map C.toP) :=
      (isPGroup_ker_linLeviHom hn).map _
    exact le_sSup ⟨hnorm, hp⟩
  exact hmap (Subgroup.mem_map_of_mem _ hu)

include C in
theorem LinCover.exists_block (hPY : P ≤ Y) (hn : 1 ≤ n)
    (hna : ∃ x ∈ P, ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 P) :
    ∃ a : Fin n, 2 ≤ linBlockLen n I a := by
  by_contra hno
  push Not at hno
  obtain ⟨x, hx, y, hy, hxy⟩ := hna
  apply hxy
  obtain ⟨x', hx'⟩ := C.toP_surjective hPY ⟨x, hx⟩
  obtain ⟨y', hy'⟩ := C.toP_surjective hPY ⟨y, hy⟩
  have hU : ⁅x', y'⁆ ∈ (linLeviHom K n I).ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    funext a
    exact commute_of_lt_two (hno a) _ _
  have h3 := C.toP_mem_pCore_of_mem_ker hPY hn hU
  rw [map_commutatorElement, hx', hy'] at h3
  exact ⟨_, h3, rfl⟩

theorem LinCover.proj_mem_projUni (q : ↥(flagStabilizer n K I))
    (hq : C.toP q ∈ CFSG.pCore 2 ↥P) :
    proj n K (q : SpecialLinearGroup (Fin n) K) ∈ projUni K n I := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkerσ : ∀ z : ↥(flagStabilizer n K I), C.toP z = 1 →
      (z : SpecialLinearGroup (Fin n) K) ∈ scalars n K := by
    intro z hz
    rw [scalars_eq_center]
    apply C.ker_le_center
    rw [MonoidHom.mem_ker]
    have h1 : ((C.σ (z : SpecialLinearGroup (Fin n) K) : ↥Y) : A) = 1 :=
      congrArg (fun w : ↥P => (w : A)) hz
    exact Subtype.ext h1
  have hker : C.toP.ker ≤ Subgroup.center ↥(flagStabilizer n K I) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hc := Subgroup.mem_center_iff.mp (by
      rw [← scalars_eq_center]
      exact hkerσ z hz) g.1
    exact Subtype.ext hc
  obtain ⟨s, hs, z, hz, hsz⟩ := exists_mul_of_comap_isPGroup C.toP hker (odd_card_units K)
    (fun z hz => by
      have h := pow_card_units_eq_one_of_mem_scalars (hkerσ z hz)
      exact Subtype.ext (by simpa [Subgroup.coe_pow] using h))
    (CFSG.pCore_isPGroup (p := 2) (G := ↥P)) hq
  have hsU : s ∈ (linLeviHom K n I).ker :=
    le_ker_linLeviHom_of_normal_isPGroup (CFSG.pCore 2 ↥(flagStabilizer n K I))
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(flagStabilizer n K I))) hs
  rw [hsz, Subgroup.coe_mul, map_mul, proj_eq_one_iff.mpr (hkerσ z hz), mul_one]
  exact ⟨(s : SpecialLinearGroup (Fin n) K), ⟨s, hsU, rfl⟩, rfl⟩

theorem LinCover.toHat_mem_wSup (hPY : P ≤ Y) (hn : 1 ≤ n) (a : Fin n)
    (ha : 2 ≤ linBlockLen n I a) (x : ↥(flagStabilizer n K I))
    (hx : ∀ c : Fin n, c ≠ a → linLeviHom K n I x c = 1) :
    C.toHat x ∈ wSup (↥P ⧸ CFSG.pCore 2 ↥P) := by
  classical
  let D : Subgroup ↥(flagStabilizer n K I) :=
    ⨅ c : {c : Fin n // c ≠ a}, (linBlockHom K n I c.1).ker
  have hDmem : ∀ y : ↥(flagStabilizer n K I), y ∈ D ↔
      ∀ c : Fin n, c ≠ a → linBlockHom K n I c y = 1 := by
    intro y
    simp only [D, Subgroup.mem_iInf, MonoidHom.mem_ker, Subtype.forall]
  haveI hDn : D.Normal := Subgroup.normal_iInf_normal fun c => MonoidHom.normal_ker _
  have hxD : x ∈ D := (hDmem x).mpr fun c hc => hx c hc
  have hdet : ∀ y : ↥D, linBlockHom K n I a (y : ↥(flagStabilizer n K I)) ∈
      linBlockSL K n I a := by
    intro y
    rw [linBlockSL, Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    exact det_linBlockHom_eq_one a y fun c hc => by
      exact (hDmem y).mp y.2 c hc
  let ℓ : ↥D →* ↥(linBlockSL K n I a) :=
    ((linBlockHom K n I a).comp D.subtype).codRestrict _ hdet
  have hℓs : Function.Surjective ℓ := by
    rintro ⟨s, hs⟩
    have hmem : (Pi.mulSingle a s : ∀ c : Fin n, GL (Fin (linBlockLen n I c)) K) ∈
        (linLeviHom K n I).range := by
      refine pi_le_range_linLeviHom ((Subgroup.mem_pi _).mpr fun c _ => ?_)
      by_cases hc : c = a
      · subst hc
        simpa using hs
      · rw [Pi.mulSingle_eq_of_ne hc]
        exact one_mem _
    obtain ⟨y, hy⟩ := hmem
    have hyD : y ∈ D := (hDmem y).mpr fun c hc => by
      have h := congrFun hy c
      rw [Pi.mulSingle_eq_of_ne hc] at h
      exact h
    refine ⟨⟨y, hyD⟩, Subtype.ext ?_⟩
    have h := congrFun hy a
    rw [Pi.mulSingle_eq_same] at h
    exact h
  let φ : ↥D →* ↥P ⧸ CFSG.pCore 2 ↥P := C.toHat.comp D.subtype
  have hker : ℓ.ker ≤ φ.ker := by
    intro y hy
    have h1 : linBlockHom K n I a (y : ↥(flagStabilizer n K I)) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
    have hyU : (y : ↥(flagStabilizer n K I)) ∈ (linLeviHom K n I).ker := by
      rw [MonoidHom.mem_ker]
      funext c
      by_cases hc : c = a
      · subst hc
        exact h1
      · exact (hDmem y).mp y.2 c hc
    rw [MonoidHom.mem_ker]
    show C.toHat y = 1
    rw [LinCover.toHat, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact C.toP_mem_pCore_of_mem_ker hPY hn hyU
  have hrange : φ.range = D.map C.toHat := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hnormal : φ.range.Normal := by
    rw [hrange]
    exact hDn.map _ (C.toHat_surjective hPY)
  have hS := isQuasisimple_or_perm_three (K := K) ha
    (slEquivToGLRange (K := K) (linBlockLen n I a))
  have hle := range_le_wSup (CFSG.AGLEmbedding.pCore_quotient_pCore_eq_bot' (X := ↥P) 2) ℓ hℓs φ
    hker hnormal hS
  exact hle ⟨⟨x, hxD⟩, rfl⟩

theorem LinCover.normFix_autHom (hPY : P ≤ Y) (hn : 1 ≤ n)
    (b : ↥(Subgroup.normalizer (Y : Set A))) (hbP : (b : A) ∈ Subgroup.normalizer (P : Set A))
    (hW : WCent P (b : A)) : NormFix I (C.autHom b) := by
  refine ⟨C.map_projFlag b hbP, fun a ha x hx => ?_⟩
  have hmem := C.toHat_mem_wSup hPY hn a ha x hx
  have hc : (b : A) * ((C.toP x : ↥P) : A) * (b : A)⁻¹ * ((C.toP x : ↥P) : A)⁻¹ ∈
      pCoreOf 2 P := hW _ (C.toP x).2 hmem
  obtain ⟨c₀, hc₀, hc₀eq⟩ := hc
  obtain ⟨q, hq⟩ := C.toP_surjective hPY c₀
  have hσq : C.σ (q : SpecialLinearGroup (Fin n) K) =
      Y.normalizerMonoidHom b (C.σ (x : SpecialLinearGroup (Fin n) K)) *
        (C.σ (x : SpecialLinearGroup (Fin n) K))⁻¹ := by
    apply Subtype.ext
    have h1 : ((C.σ (q : SpecialLinearGroup (Fin n) K) : ↥Y) : A) = (c₀ : A) := by
      rw [← hq]
      rfl
    rw [h1, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact hc₀eq
  have hprojq : proj n K (q : SpecialLinearGroup (Fin n) K) =
      C.autHom b (proj n K (x : SpecialLinearGroup (Fin n) K)) *
        (proj n K (x : SpecialLinearGroup (Fin n) K))⁻¹ := by
    rw [← C.compat (q : SpecialLinearGroup (Fin n) K), hσq, C.autHom_apply_proj,
      ← C.compat (x : SpecialLinearGroup (Fin n) K), QuotientGroup.mk_mul, map_mul,
      QuotientGroup.mk_inv, map_inv]
  rw [← hprojq]
  exact C.proj_mem_projUni q (hq ▸ hc₀)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin
