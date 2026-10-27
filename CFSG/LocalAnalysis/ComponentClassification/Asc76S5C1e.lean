module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5C1a

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3
open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Overlap

variable {A R T : Subgroup G} {g : G}

theorem conj (h : Overlap A R g T) {k : G} (hk : k ∈ normalizer (A : Set G)) :
    Overlap A (AschbacherTightEmbedding.rightConjugate R k) (g * k)
      (AschbacherTightEmbedding.rightConjugate T k) := by
  have hNk : AschbacherTightEmbedding.rightConjugate (normalizer (A : Set G)) k =
      normalizer (A : Set G) := (rightConjugate_eq_self_iff _ k).mpr (Subgroup.le_normalizer hk)
  refine ⟨h.standard, fun hgk => h.not_mem ?_, ?_, ?_, ?_, ?_⟩
  · have : g = g * k * k⁻¹ := by group
    rw [this]
    exact mul_mem hgk (inv_mem hk)
  · have h1 := isSylowOf_rightConjugate h.sylow k
    rwa [AschbacherTheorem3.rightConjugate_inf, rightConjugate_mul, hNk] at h1
  · exact fun hb => h.ne_bot ((rightConjugate_eq_bot_iff).mp hb)
  · have h1 := isSylowOf_rightConjugate h.sylowR k
    have hK : AschbacherTightEmbedding.rightConjugate (centralizer (A : Set G)) k =
        centralizer (A : Set G) := (rightConjugate_eq_self_iff _ k).mpr
          (by rw [normalizer_centralizer_eq h.standard]; exact hk)
    rwa [hK] at h1
  · rw [← AschbacherTheorem3.rightConjugate_normalizer]
    exact rightConjugate_le_rightConjugate h.normalizesR k

theorem le_normalizer_inf_centralizer (h : Overlap A R g T)
    (hnot : ¬ IsSylowOf 2 T (AschbacherTightEmbedding.rightConjugate (centralizer (A : Set G)) g))
    (H : ∀ (x : G) (V : Subgroup G), Overlap A R x V →
      IsSylowOf 2 V (AschbacherTightEmbedding.rightConjugate (centralizer (A : Set G)) x) ∨
        R ⊓ centralizer (V : Set G) = R ⊓ centralizer (T : Set G)) :
    normalizer (R : Set G) ≤ normalizer ((R ⊓ centralizer (T : Set G) : Subgroup G) : Set G) := by
  intro n hn
  have hReven : Even (Nat.card R) :=
    even_iff_two_dvd.mpr (two_dvd_card_of_isSylowOf h.sylowR h.tight.1)
  have hnK : n ∈ normalizer (centralizer (A : Set G) : Set G) :=
    normalizer_le_normalizer_of_tightlyEmbedded h.tight h.sylowR.le hReven hn
  have hnA : n ∈ normalizer (A : Set G) := by rwa [normalizer_centralizer_eq h.standard] at hnK
  have hRn : AschbacherTightEmbedding.rightConjugate R n = R :=
    (rightConjugate_eq_self_iff R n).mpr hn
  have h' := h.conj hnA
  rw [hRn] at h'
  rcases H _ _ h' with hs | heq
  · exfalso
    apply hnot
    have := isSylowOf_rightConjugate hs n⁻¹
    simpa only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one, mul_inv_cancel_right]
      using this
  · have hc : AschbacherTightEmbedding.rightConjugate (R ⊓ centralizer (T : Set G)) n =
        R ⊓ centralizer (AschbacherTightEmbedding.rightConjugate T n : Set G) := by
      rw [AschbacherTheorem3.rightConjugate_inf, hRn,
        AschbacherTheorem3.rightConjugate_centralizer]
    rw [← hc] at heq
    exact (rightConjugate_eq_self_iff _ n).mp heq

end Overlap

theorem mem_normalizer_sup {X Y : Subgroup G} {a : G} (hX : a ∈ normalizer (X : Set G))
    (hY : a ∈ normalizer (Y : Set G)) : a ∈ normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  refine mem_normalizer_of_map_conj_le ?_
  rw [Subgroup.map_sup]
  refine sup_le_sup ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp hX x).mp hx
  · rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hY y).mp hy

omit [Finite G] in
theorem sq_eq_one_of_pow_two_pow_eq_one {H : Type*} [Group H]
    (hC : ∀ t x : H, orderOf t = 2 → x ∈ centralizer ({t} : Set H) → x ^ 2 = 1) {x : H} {m : ℕ}
    (hx : x ^ 2 ^ m = 1) : x ^ 2 = 1 := by
  obtain ⟨j, -, hjx⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx)
  rcases j with _ | j
  · rw [pow_zero, orderOf_eq_one_iff] at hjx
    rw [hjx, one_pow]
  · refine hC (x ^ 2 ^ j) x ?_ ?_
    · rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
        (by rw [hjx]; exact pow_dvd_pow 2 (Nat.le_succ j)), hjx, pow_succ,
        Nat.mul_div_cancel_left _ (by positivity)]
    · rw [mem_centralizer_singleton_iff]
      exact ((Commute.refl x).pow_right _).eq

theorem sq_eq_one_sl2 {n : ℕ} {b : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)} {m : ℕ}
    (hb : b ^ 2 ^ m = 1) : b ^ 2 = 1 := by
  set e := CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 n)
  have hz : (e.symm b) ^ 2 ^ m = 1 := by rw [← map_pow, hb, map_one]
  have h2 := sq_eq_one_of_pow_two_pow_eq_one
    (fun t x ht hx => CFSG.Walter.psl2_sq_eq_one_of_mem_centralizer_of_charTwo ht hx) hz
  have h3 : e ((e.symm b) ^ 2) = 1 := by rw [h2, map_one]
  rwa [map_pow, MulEquiv.apply_symm_apply] at h3

theorem sq_eq_one_of_caseL2 {K R T : Subgroup G} (hR : IsSylowOf 2 R K) {n : ℕ}
    (φ : oUpperTwoPrime (K ⊔ T) →* Multiplicative (Fin n → ZMod 2) ×
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (hker : φ.ker = (oddCoreIn K).subgroupOf (oUpperTwoPrime (K ⊔ T))) :
    ∀ r ∈ R, r ^ 2 = 1 := by
  intro r hr
  obtain ⟨m, hm⟩ := hR.isPGroup ⟨r, hr⟩
  have hm' : r ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hrY : r ∈ oUpperTwoPrime (K ⊔ T) := mem_oUpperTwoPrime (mem_sup_left (hR.le hr)) hm'
  have hy : φ ⟨r, hrY⟩ ^ 2 ^ m = 1 := by
    rw [← map_pow]
    have : (⟨r, hrY⟩ : oUpperTwoPrime (K ⊔ T)) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hm')
    rw [this, map_one]
  have hy2 : φ ⟨r, hrY⟩ ^ 2 = 1 := by
    ext1
    · exact sq_eq_one_multiplicative _
    · show (φ ⟨r, hrY⟩).2 ^ 2 = 1
      exact sq_eq_one_sl2 (congrArg Prod.snd hy)
  have hr2 : (⟨r, hrY⟩ : oUpperTwoPrime (K ⊔ T)) ^ 2 ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hy2
  rw [hker, mem_subgroupOf] at hr2
  have h1 : r ^ 2 ∈ oddCoreIn K ⊓ R := ⟨by simpa using hr2, R.pow_mem hr 2⟩
  rwa [oddCoreIn_inf_eq_bot hR.isPGroup, mem_bot] at h1

end CFSG.ComponentClassification.Asc76.Sec5
