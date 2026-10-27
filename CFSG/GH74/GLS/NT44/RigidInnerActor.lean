module

public import CFSG.GH74.GLS.NT44.RigidActorClasses
import CFSG.GH74.GLS.NT44.ActualCover
import CFSG.GH74.GLS.NT44.AutProjection
import CFSG.GH74.GLS.NT44.RigidFamily
import CFSG.GH74.GLS.NT44.UnitaryCenter
import CFSG.GH74.GLS.Stage1.Thm4.P92Basic
public import CFSG.GH74.GLS.NT44.ActualCoverModel

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open CFSG
open CFSG.GH74.GLS
open CFSG.GH74.GLS.Stage1.Thm4
open CFSG.GH74.GLS.Stage1.Thm3.Sec4
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.PerfectAutomorphisms

section Action

variable {G : Type} [Group G]

theorem mapQuotient_normalizerMonoidHom_congr {K : Subgroup G} {s t : G} (h : s = t)
    (hs : s ∈ Subgroup.normalizer (K : Set G)) (ht : t ∈ Subgroup.normalizer (K : Set G)) :
    MulAut.mapQuotient (pPrimeCore 2 ↥K) (K.normalizerMonoidHom ⟨s, hs⟩) =
      MulAut.mapQuotient (pPrimeCore 2 ↥K) (K.normalizerMonoidHom ⟨t, ht⟩) := by
  subst h
  rfl

theorem mapQuotient_normalizerMonoidHom_mul {K : Subgroup G} {s t : G}
    (hs : s ∈ Subgroup.normalizer (K : Set G)) (ht : t ∈ Subgroup.normalizer (K : Set G)) :
    MulAut.mapQuotient (pPrimeCore 2 ↥K) (K.normalizerMonoidHom ⟨s * t, mul_mem hs ht⟩) =
      MulAut.mapQuotient (pPrimeCore 2 ↥K) (K.normalizerMonoidHom ⟨s, hs⟩) *
        MulAut.mapQuotient (pPrimeCore 2 ↥K) (K.normalizerMonoidHom ⟨t, ht⟩) := by
  rw [show (⟨s * t, mul_mem hs ht⟩ : ↥(Subgroup.normalizer (K : Set G))) =
      ⟨s, hs⟩ * ⟨t, ht⟩ from rfl, map_mul, map_mul]

theorem conj_mem_normalizer_cmap {K : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (K : Set G)) (c : G) :
    c * t * c⁻¹ ∈ Subgroup.normalizer ((cmap c K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at ht ⊢
  intro y
  have h1 := ht (c⁻¹ * y * c)
  rw [mem_cmap, mem_cmap]
  rw [show c⁻¹ * (c * t * c⁻¹ * y * (c * t * c⁻¹)⁻¹) * c = t * (c⁻¹ * y * c) * t⁻¹ by group]
  exact h1

theorem conj_not_mem_centralizerSection_cmap {K : Subgroup G} {t : G}
    (ht : t ∉ centralizerSection K (pPrimeCoreOf 2 K)) (c : G) :
    c * t * c⁻¹ ∉ centralizerSection (cmap c K) (pPrimeCoreOf 2 (cmap c K)) := by
  intro h
  have h' := cmap_mem_centralizerSection h c⁻¹
  rw [pPrimeCoreOf_cmap, cmap_inv_cancel, cmap_inv_cancel,
    show c⁻¹ * (c * t * c⁻¹) * c⁻¹⁻¹ = t by group] at h'
  exact ht h'

theorem mapQuotient_mem_range_conj_cmap {K K' : Subgroup G} {c t : G} (hK' : cmap c K = K')
    (ht : t ∈ Subgroup.normalizer (K : Set G))
    (ht' : c * t * c⁻¹ ∈ Subgroup.normalizer (K' : Set G))
    (h : MulAut.mapQuotient (pPrimeCore 2 ↥K) (K.normalizerMonoidHom ⟨t, ht⟩) ∈
      (MulAut.conj : kBar K →* MulAut (kBar K)).range) :
    MulAut.mapQuotient (pPrimeCore 2 ↥K') (K'.normalizerMonoidHom ⟨c * t * c⁻¹, ht'⟩) ∈
      (MulAut.conj : kBar K' →* MulAut (kBar K')).range := by
  subst hK'
  obtain ⟨q, hq⟩ := h
  let e : ↥K ≃* ↥(cmap c K) := (MulAut.conj c).subgroupMap K
  let ψ : kBar K ≃* kBar (cmap c K) :=
    QuotientGroup.congr (pPrimeCore 2 ↥K) (pPrimeCore 2 ↥(cmap c K)) e
      (CFSG.pPrimeCore_map_iso 2 e)
  have hψmk : ∀ k : ↥K, ψ (QuotientGroup.mk k) = QuotientGroup.mk (e k) :=
    fun k => QuotientGroup.congr_mk _ _ _ _ k
  have hcongr : ∀ y : kBar K,
      MulAut.congr ψ (MulAut.mapQuotient (pPrimeCore 2 ↥K) (K.normalizerMonoidHom ⟨t, ht⟩))
        (ψ y) =
      ψ (MulAut.mapQuotient (pPrimeCore 2 ↥K) (K.normalizerMonoidHom ⟨t, ht⟩) y) := by
    intro y
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hkey : MulAut.mapQuotient (pPrimeCore 2 ↥(cmap c K))
        ((cmap c K).normalizerMonoidHom ⟨c * t * c⁻¹, ht'⟩) =
      MulAut.congr ψ (MulAut.mapQuotient (pPrimeCore 2 ↥K)
        (K.normalizerMonoidHom ⟨t, ht⟩)) := by
    ext x
    obtain ⟨y, rfl⟩ := ψ.surjective x
    induction y using QuotientGroup.induction_on with
    | H k =>
      rw [hcongr, MulAut.mapQuotient_mk, hψmk (K.normalizerMonoidHom ⟨t, ht⟩ k),
        hψmk k, MulAut.mapQuotient_mk]
      have hek : ∀ x : ↥K, ((e x : ↥(cmap c K)) : G) = c * (x : G) * c⁻¹ := fun x => rfl
      have hEl : ((cmap c K).normalizerMonoidHom ⟨c * t * c⁻¹, ht'⟩) (e k) =
          e (K.normalizerMonoidHom ⟨t, ht⟩ k) := by
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hek, hek,
          Subgroup.normalizerMonoidHom_apply_apply_coe]
        group
      rw [hEl]
  refine ⟨ψ q, ?_⟩
  rw [hkey, ← hq]
  ext x
  obtain ⟨y, rfl⟩ := ψ.surjective x
  simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, map_mul, map_inv]

end Action

section Classes

theorem isConj_congr_centerQuotientHom {K : Type} [Group K]
    (b b' : (K ⧸ Subgroup.center K) ≃* S) (γ : MulAut K) :
    IsConj (MulAut.congr b' (centerQuotientHom K γ)) (MulAut.congr b (centerQuotientHom K γ)) := by
  refine isConj_iff.mpr ⟨b'.symm.trans b, ?_⟩
  ext x
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_trans_apply, MulEquiv.symm_symm, MulEquiv.symm_apply_apply]

theorem not_isConj_r₄_mul_of_isConj_r₄ {β₁ β₂ : MulAut S}
    (h₁ : IsConj β₁ (conjAutS r₄R)) (h₂ : IsConj β₂ (conjAutS r₄R)) :
    ¬ IsConj (β₁ * β₂) (conjAutS r₄R) := by
  obtain ⟨ρ₁, rfl⟩ := conjAutS_surjective β₁
  obtain ⟨ρ₂, rfl⟩ := conjAutS_surjective β₂
  have key : ∀ {a b : R}, IsConj (conjAutS a) (conjAutS b) → IsConj a b := by
    intro a b h
    rw [isConj_iff] at h ⊢
    obtain ⟨d, hd⟩ := h
    obtain ⟨c, rfl⟩ := conjAutS_surjective d
    refine ⟨c, ?_⟩
    apply conjAutS_injective
    rw [← hd]
    simp only [map_mul, map_inv]
  have hρ₁ : IsConj ρ₁ r₄R := key h₁
  have hρ₂ : IsConj ρ₂ r₄R := key h₂
  intro h
  have hρ₁₂ : IsConj (ρ₁ * ρ₂) r₄R := by
    apply key
    rwa [← map_mul] at h
  have hs₁ : (ρ₁ : Equiv.Perm (Fin 42)) * r₄⁻¹ ∈ S :=
    CFSG.ComponentClassification.GrSLit.mul_inv_mem_S_of_isConj₄ hρ₁
  have hs₂ : (ρ₂ : Equiv.Perm (Fin 42)) * r₄⁻¹ ∈ S :=
    CFSG.ComponentClassification.GrSLit.mul_inv_mem_S_of_isConj₄ hρ₂
  have hs₃ : ((ρ₁ * ρ₂ : R) : Equiv.Perm (Fin 42)) * r₄⁻¹ ∈ S :=
    CFSG.ComponentClassification.GrSLit.mul_inv_mem_S_of_isConj₄ hρ₁₂
  apply not_mem_S_r₄
  have hr : r₄ = ((ρ₁ : Equiv.Perm (Fin 42)) * r₄⁻¹)⁻¹ *
      (((ρ₁ * ρ₂ : R) : Equiv.Perm (Fin 42)) * r₄⁻¹) *
      ((ρ₂ : Equiv.Perm (Fin 42)) * r₄⁻¹)⁻¹ := by
    rw [Subgroup.coe_mul]
    group
  rw [hr]
  exact mul_mem (mul_mem (inv_mem hs₁) hs₃) (inv_mem hs₂)

end Classes

section Unitary

theorem inverts_center_kBar_of_projective_unitary
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ]
    (hL34 : IsL34Quotient fullQ) (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x : G} {J : Subgroup G} (hJ : J ∈ RigidSet fullQ x)
    (α : MulAut (kBar J)) (b : (kBar J ⧸ Subgroup.center (kBar J)) ≃* S)
    (hunit : IsConj (MulAut.congr b (centerQuotientHom (kBar J) α)) (conjAutS r₄R)) :
    ∀ z ∈ Subgroup.center (kBar J), α z = z⁻¹ := by
  classical
  obtain ⟨eI⟩ := hJ.2
  have hfin : Finite fullQ := Finite.of_equiv (kBar J) eI.toEquiv
  have hq : CFSG.IsQuasisimple fullQ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eI
      (TwoThin.isQuasisimple_hat (P92.rig_pcomp hJ))
  obtain ⟨b₀, lam, e, -, -, -, -, hqe, -, -, -, -⟩ :=
    actualCoverOfL34 fullQ hq hL34 h16
  let b₁ : (kBar J ⧸ Subgroup.center (kBar J)) ≃* S :=
    (QuotientGroup.congr (Subgroup.center (kBar J)) (Subgroup.center fullQ) eI
      (Subgroup.map_center_eq eI)).trans b₀
  let eF : FullTwoCover ≃* kBar J := e.trans eI.symm
  let α' : MulAut FullTwoCover := MulAut.congr eF.symm α
  let β₁ : MulAut S := MulAut.congr b₁ (centerQuotientHom (kBar J) α)
  have hunit₁ : IsConj β₁ (conjAutS r₄R) :=
    (isConj_congr_centerQuotientHom b b₁ α).trans hunit
  have hb₁ : ∀ u : FullTwoCover,
      b₁ (QuotientGroup.mk' (Subgroup.center (kBar J)) (eF u)) = fullTwoCoverToS u := by
    intro u
    have h1 : eF u = eI.symm (e u) := by
      rw [show eF = e.trans eI.symm from rfl, MulEquiv.trans_apply]
    have h2 : eI (eF u) = e u := by rw [h1, MulEquiv.apply_symm_apply]
    calc b₁ (QuotientGroup.mk' (Subgroup.center (kBar J)) (eF u))
        = b₀ (QuotientGroup.mk' (Subgroup.center fullQ) (eI (eF u))) := by
          rw [show b₁ = (QuotientGroup.congr (Subgroup.center (kBar J))
              (Subgroup.center fullQ) eI (Subgroup.map_center_eq eI)).trans b₀ from rfl,
            MulEquiv.trans_apply, QuotientGroup.congr_mk']
      _ = b₀ (QuotientGroup.mk' (Subgroup.center fullQ) (e u)) := by rw [h2]
      _ = fullTwoCoverToS u := by
          exact DFunLike.congr_fun hqe u
  have hα'u : ∀ u : FullTwoCover, α' u = eF.symm (α (eF u)) := by
    intro u
    rw [show α' = MulAut.congr eF.symm α from rfl, MulAut.congr_apply,
      MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_symm]
  have hcomm : ∀ u : FullTwoCover, fullTwoCoverToS (α' u) = β₁ (fullTwoCoverToS u) := by
    intro u
    have hα'e : eF (α' u) = α (eF u) := by
      rw [hα'u, MulEquiv.apply_symm_apply]
    calc fullTwoCoverToS (α' u)
        = b₁ (QuotientGroup.mk' (Subgroup.center (kBar J)) (eF (α' u))) :=
            (hb₁ (α' u)).symm
      _ = b₁ (QuotientGroup.mk' (Subgroup.center (kBar J)) (α (eF u))) := by rw [hα'e]
      _ = β₁ (b₁ (QuotientGroup.mk' (Subgroup.center (kBar J)) (eF u))) :=
            congr_centerQuotientHom_comp_apply b₁ α (eF u)
      _ = β₁ (fullTwoCoverToS u) := by rw [hb₁ u]
  obtain ⟨Φ, hΦ, -, huniq, -, -, -⟩ := autProjection
  have hΦα' : Φ α' = β₁ := by
    rw [huniq β₁ α' hcomm, MulEquiv.apply_symm_apply]
  have hunit₁' : IsConj (Φ α') (conjAutS r₄R) := by rw [hΦα']; exact hunit₁
  have hinvFull : ∀ z ∈ Subgroup.center FullTwoCover, α' z = z⁻¹ :=
    inverts_center_of_projective_unitary Φ hΦ hunit₁'
  intro z hz
  have hz' : eF.symm z ∈ Subgroup.center FullTwoCover := by
    have hmem : z ∈ (Subgroup.center FullTwoCover).map (eF : FullTwoCover →* kBar J) := by
      rw [Subgroup.map_center_eq eF]
      exact hz
    obtain ⟨w, hw, hwz⟩ := hmem
    have hwz' : eF w = z := hwz
    rw [← hwz', MulEquiv.symm_apply_apply]
    exact hw
  have hα'z : α' (eF.symm z) = eF.symm (α z) := by
    rw [hα'u, MulEquiv.apply_symm_apply]
  refine eF.symm.injective ?_
  rw [map_inv, ← hα'z]
  exact hinvFull (eF.symm z) hz'

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_isSylowOf_centralizer_mem_of_orderOf_eq_two {x v : G} (hv2 : orderOf v = 2)
    (hvx : v * x = x * v) :
    ∃ S₀ : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 2 S₀ (Subgroup.centralizer ({x} : Set G)) ∧ v ∈ S₀ := by
  have : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have hvC : v ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hvx
  have hP : IsPGroup 2 ↥(Subgroup.zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv2, pow_one])
  obtain ⟨Q, hQ⟩ :=
    (hP.comap_subtype (K := Subgroup.centralizer ({x} : Set G))).exists_le_sylow
  have hmem : (⟨v, hvC⟩ : ↥(Subgroup.centralizer ({x} : Set G))) ∈
      (Subgroup.zpowers v).comap (Subgroup.centralizer ({x} : Set G)).subtype :=
    Subgroup.mem_comap.mpr (Subgroup.mem_zpowers v)
  refine ⟨(Q : Subgroup ↥(Subgroup.centralizer ({x} : Set G))).map
    (Subgroup.centralizer ({x} : Set G)).subtype, ⟨Q, rfl⟩, ?_⟩
  exact Subgroup.mem_map_of_mem (Subgroup.centralizer ({x} : Set G)).subtype (hQ hmem)

omit [Finite G] in
theorem conj_eq_inv_of_mem_inf_zStar {J S₀ : Subgroup G} {v : G}
    (eZ : ↥(S₀ ⊓ zStar J) ≃* Subgroup.center (kBar J))
    (heZ : ∀ w : ↥(S₀ ⊓ zStar J),
      (eZ w : kBar J) = CFSG.GH74.GLS.Stage1.Thm2.Recip.hatMk J ⟨(w : G), w.2.2.1⟩)
    (hvS : v ∈ S₀) (hvJ : v ∈ Subgroup.normalizer (J : Set G))
    (hinv : ∀ z ∈ Subgroup.center (kBar J),
      MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨v, hvJ⟩) z = z⁻¹) :
    ∀ w ∈ S₀ ⊓ zStar J, v * w * v⁻¹ = w⁻¹ := by
  intro w hw
  have hwJ : w ∈ J := hw.2.1
  have hvwS : v * w * v⁻¹ ∈ S₀ := S₀.mul_mem (S₀.mul_mem hvS hw.1) (S₀.inv_mem hvS)
  have hvwJ : v * w * v⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hvJ w).1 hwJ
  have hvwZ : v * w * v⁻¹ ∈ zStar J :=
    CFSG.GH74.GLS.Stage1.Thm4.Alt51.zStar_conj hvJ hw.2
  let w' : ↥(S₀ ⊓ zStar J) := ⟨v * w * v⁻¹, ⟨hvwS, hvwZ⟩⟩
  have hsub : (⟨v * w * v⁻¹, hvwJ⟩ : ↥J) =
      J.normalizerMonoidHom ⟨v, hvJ⟩ ⟨w, hwJ⟩ := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hsub' : (⟨(w' : G), w'.2.2.1⟩ : ↥J) = ⟨v * w * v⁻¹, hvwJ⟩ := by
    apply Subtype.ext
    rfl
  have hsub'' : (⟨(w' : G), w'.2.2.1⟩ : ↥J) =
      J.normalizerMonoidHom ⟨v, hvJ⟩ ⟨w, hwJ⟩ := hsub'.trans hsub
  have hmap0 : MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨v, hvJ⟩)
        (CFSG.GH74.GLS.Stage1.Thm2.Recip.hatMk J ⟨w, hwJ⟩) =
      CFSG.GH74.GLS.Stage1.Thm2.Recip.hatMk J
        (J.normalizerMonoidHom ⟨v, hvJ⟩ ⟨w, hwJ⟩) := by
    change MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨v, hvJ⟩)
        ((⟨w, hwJ⟩ : ↥J) : kBar J) =
      ((J.normalizerMonoidHom ⟨v, hvJ⟩ ⟨w, hwJ⟩ : ↥J) : kBar J)
    exact MulAut.mapQuotient_mk (N := pPrimeCore 2 ↥J) _ _
  have hmap : (eZ w' : kBar J) =
      MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨v, hvJ⟩)
        (CFSG.GH74.GLS.Stage1.Thm2.Recip.hatMk J ⟨w, hwJ⟩) := by
    have hz : (eZ w' : kBar J) = CFSG.GH74.GLS.Stage1.Thm2.Recip.hatMk J
        (J.normalizerMonoidHom ⟨v, hvJ⟩ ⟨w, hwJ⟩) := by
      rw [heZ w']
      exact congrArg (QuotientGroup.mk' (pPrimeCore 2 ↥J)) hsub''
    exact hz.trans hmap0.symm
  have hmap' : MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨v, hvJ⟩)
        (CFSG.GH74.GLS.Stage1.Thm2.Recip.hatMk J ⟨w, hwJ⟩) =
      (eZ ⟨w, hw⟩ : kBar J)⁻¹ := by
    rw [← heZ ⟨w, hw⟩]
    exact hinv (eZ ⟨w, hw⟩) (eZ ⟨w, hw⟩).2
  have hwinv : w' = (⟨w, hw⟩ : ↥(S₀ ⊓ zStar J))⁻¹ := by
    apply eZ.injective
    apply Subtype.ext
    rw [map_inv]
    exact hmap.trans hmap'
  have hcoe := congrArg (fun y : ↥(S₀ ⊓ zStar J) => (y : G)) hwinv
  simpa [w'] using hcoe

omit [Finite G] in
theorem exists_pair_of_mulEquiv_zmod_four {W : Subgroup G}
    (e : ↥W ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :
    ∃ ζ₁ ∈ W, ∃ ζ₂ ∈ W, ζ₁ * ζ₂ = ζ₂ * ζ₁ ∧ ζ₁ ^ 4 = 1 ∧ ζ₂ ^ 4 = 1 ∧ ζ₁ ^ 2 ≠ 1 ∧
      ζ₂ ^ 2 ≠ 1 ∧ ζ₁ ^ 2 * ζ₂ ^ 2 ≠ 1 := by
  let x₁ : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) := (Multiplicative.ofAdd 1, 1)
  let x₂ : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) := (1, Multiplicative.ofAdd 1)
  let w₁ : ↥W := e.symm x₁
  let w₂ : ↥W := e.symm x₂
  have e₁ : e w₁ = x₁ := e.apply_symm_apply x₁
  have e₂ : e w₂ = x₂ := e.apply_symm_apply x₂
  have hx1 : x₁ ^ 4 = 1 := by decide
  have hx2 : x₂ ^ 4 = 1 := by decide
  have hx1sq : x₁ ^ 2 ≠ 1 := by decide
  have hx2sq : x₂ ^ 2 ≠ 1 := by decide
  have hx12sq : x₁ ^ 2 * x₂ ^ 2 ≠ 1 := by decide
  have h12 : w₁ * w₂ = w₂ * w₁ := by
    apply e.injective
    rw [map_mul, map_mul, e₁, e₂]
    exact mul_comm x₁ x₂
  have h14 : w₁ ^ 4 = 1 := by
    apply e.injective
    rw [map_pow, e₁, e.map_one]
    exact hx1
  have h24 : w₂ ^ 4 = 1 := by
    apply e.injective
    rw [map_pow, e₂, e.map_one]
    exact hx2
  refine ⟨(w₁ : G), w₁.2, (w₂ : G), w₂.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [← Subgroup.coe_mul, h12]
  · simp only [← Subgroup.coe_pow, h14, Subgroup.coe_one]
  · simp only [← Subgroup.coe_pow, h24, Subgroup.coe_one]
  · intro h
    have hw : w₁ ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, h, Subgroup.coe_one]
    have hx : x₁ ^ 2 = 1 := by
      have := congrArg e hw
      rwa [map_pow, e₁, e.map_one] at this
    exact hx1sq hx
  · intro h
    have hw : w₂ ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, h, Subgroup.coe_one]
    have hx : x₂ ^ 2 = 1 := by
      have := congrArg e hw
      rwa [map_pow, e₂, e.map_one] at this
    exact hx2sq hx
  · intro h
    have hw : w₁ ^ 2 * w₂ ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, h, Subgroup.coe_one]
    have hx : x₁ ^ 2 * x₂ ^ 2 = 1 := by
      have := congrArg e hw
      rwa [map_mul, map_pow, map_pow, e₁, e₂, e.map_one] at this
    exact hx12sq hx

omit [Finite G] in
theorem sq_mem_comm_isConj_of_inverts {W : Subgroup G} {v ζ : G}
    (hvW : ∀ w ∈ W, v * w * v⁻¹ = w⁻¹) (hζ : ζ ∈ W) (h4 : ζ ^ 4 = 1) (h2 : ζ ^ 2 ≠ 1) :
    ζ ^ 2 ∈ W ∧ orderOf (ζ ^ 2) = 2 ∧ ζ ^ 2 * v = v * ζ ^ 2 ∧ IsConj v (ζ ^ 2 * v) := by
  have : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have hζ2W : ζ ^ 2 ∈ W := W.pow_mem hζ 2
  have hsq : (ζ ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, show 2 * 2 = 4 by norm_num, h4]
  have hsq' : ζ ^ 2 * ζ ^ 2 = 1 := by simpa [pow_two] using hsq
  have hinv2 : (ζ ^ 2)⁻¹ = ζ ^ 2 := inv_eq_of_mul_eq_one_right hsq'
  have hcomm : ζ ^ 2 * v = v * ζ ^ 2 := by
    have h := hvW (ζ ^ 2) hζ2W
    rw [hinv2] at h
    have h' : v * ζ ^ 2 = ζ ^ 2 * v := by
      calc v * ζ ^ 2 = (v * ζ ^ 2 * v⁻¹) * v := by group
        _ = ζ ^ 2 * v := by rw [h]
    exact h'.symm
  have hconj : IsConj v (ζ ^ 2 * v) := by
    refine isConj_iff.mpr ⟨ζ, ?_⟩
    have hζinv : v * ζ⁻¹ * v⁻¹ = ζ := by
      have := hvW ζ⁻¹ (W.inv_mem hζ)
      simpa using this
    have h3 : v * ζ⁻¹ = ζ * v := by
      calc v * ζ⁻¹ = (v * ζ⁻¹ * v⁻¹) * v := by group
        _ = ζ * v := by rw [hζinv]
    calc ζ * v * ζ⁻¹ = ζ * (v * ζ⁻¹) := by group
      _ = ζ * (ζ * v) := by rw [h3]
      _ = ζ ^ 2 * v := by rw [pow_two, mul_assoc]
  exact ⟨hζ2W, orderOf_eq_prime hsq h2, hcomm, hconj⟩

omit [Finite G] in
theorem not_mem_centralizerSection_of_odd_card {x v u : G} {J L : Subgroup G}
    (hJ : IsPCompIn 2 (Subgroup.centralizer ({x} : Set G)) J)
    (huZ : u ∈ zStar J) (huv : u * v = v * u) (hu2 : orderOf u = 2)
    (hodd : Odd (Nat.card ↥(CxK x J ⊓ CxK v L))) :
    u ∉ centralizerSection L (pPrimeCoreOf 2 L) := by
  intro h
  have huJ : u ∈ CxK x J := ⟨hJ.1 huZ.1, huZ.2⟩
  have huL : u ∈ CxK v L := ⟨Subgroup.mem_centralizer_singleton_iff.mpr huv, h⟩
  have hu : u ∈ CxK x J ⊓ CxK v L := ⟨huJ, huL⟩
  have hdvd : orderOf u ∣ Nat.card ↥(CxK x J ⊓ CxK v L) :=
    Subgroup.orderOf_dvd_natCard (CxK x J ⊓ CxK v L) hu
  rw [hu2] at hdvd
  exact hodd.not_two_dvd_nat hdvd

theorem conj_mem_kz_of_mem_kz {fullQ : Type} [Group fullQ] {x : G} (hxP : x ∈ Kz fullQ x)
    (g : G) : g * x * g⁻¹ ∈ Kz fullQ (g * x * g⁻¹) := by
  rw [kz_conj (Q := fullQ) (z := x) g]
  have hmem : (MulAut.conj g) x ∈ (Kz fullQ x).map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (K := Kz fullQ x) hxP
  rw [MulAut.conj_apply] at hmem
  exact hmem

theorem card_rigidSet_conj {fullQ : Type} [Group fullQ] (x g : G) :
    Nat.card ↥(RigidSet fullQ (g * x * g⁻¹)) = Nat.card ↥(RigidSet fullQ x) := by
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  exact ncard_rigidSet_conj (Q := fullQ) (z := x) g

end Unitary

theorem inner_actor_conj_mul_of_not_isConj_r₄
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (hL34 : IsL34Quotient fullQ) (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (hx2 : orderOf x = 2) (hv2 : orderOf v = 2) (hxv : IsConj x v) (hvx : v * x = x * v)
    (hJ : J ∈ RigidSet fullQ x) (hvN : v ∈ Subgroup.normalizer (J : Set G))
    (hvact : v ∉ centralizerSection J (pPrimeCoreOf 2 J)) (hxP : x ∈ Kz fullQ x)
    (hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(RigidSet fullQ s) ≤ Nat.card ↥(RigidSet fullQ x))
    (hr : 1 < Nat.card ↥(RigidSet fullQ x))
    {g : G} (hg : g * x * g⁻¹ = v) {L : Subgroup G} (hLJ : cmap g J = L)
    {u : G} (huZ : u ∈ zStar J) (hu2 : orderOf u = 2) (huv : u * v = v * u)
    (hconj : IsConj v (u * v)) (huL : u ∈ Subgroup.normalizer (L : Set G))
    (b₀ : (kBar L ⧸ Subgroup.center (kBar L)) ≃* S)
    (hnu : ¬ IsConj (MulAut.congr b₀ (centerQuotientHom (kBar L)
      (MulAut.mapQuotient (pPrimeCore 2 ↥L) (L.normalizerMonoidHom ⟨u, huL⟩))))
      (conjAutS r₄R)) :
    ∃ htN : g⁻¹ * (u * v) * g⁻¹⁻¹ ∈ Subgroup.normalizer (J : Set G),
      orderOf (g⁻¹ * (u * v) * g⁻¹⁻¹) = 2 ∧ IsConj x (g⁻¹ * (u * v) * g⁻¹⁻¹) ∧
      g⁻¹ * (u * v) * g⁻¹⁻¹ * x = x * (g⁻¹ * (u * v) * g⁻¹⁻¹) ∧
      g⁻¹ * (u * v) * g⁻¹⁻¹ ∉ centralizerSection J (pPrimeCoreOf 2 J) ∧
      MulAut.mapQuotient (pPrimeCore 2 ↥J)
          (J.normalizerMonoidHom ⟨g⁻¹ * (u * v) * g⁻¹⁻¹, htN⟩) ∈
        (MulAut.conj : kBar J →* MulAut (kBar J)).range := by
  classical
  have hL : L ∈ RigidSet fullQ v := by
    have h := isRigidOfType_conj hJ g
    rw [hg, hLJ] at h
    exact h
  have hLc : IsPCompIn 2 (Subgroup.centralizer ({v} : Set G)) L := P92.rig_pcomp hL
  have hvL : v ∈ CxK v L := mem_cxK_self_of_isPCompIn hLc
  have hvLN : v ∈ Subgroup.normalizer (L : Set G) := hvL.2.1
  have hact_v : MulAut.mapQuotient (pPrimeCore 2 ↥L) (L.normalizerMonoidHom ⟨v, hvLN⟩) = 1 :=
    (mapQuotient_normalizerMonoidHom_eq_one_iff hvLN).mpr hvL.2
  have huvLN : u * v ∈ Subgroup.normalizer (L : Set G) := mul_mem huL hvLN
  have hact_uv :
      MulAut.mapQuotient (pPrimeCore 2 ↥L) (L.normalizerMonoidHom ⟨u * v, huvLN⟩) =
        MulAut.mapQuotient (pPrimeCore 2 ↥L) (L.normalizerMonoidHom ⟨u, huL⟩) := by
    rw [mapQuotient_normalizerMonoidHom_mul huL hvLN, hact_v, mul_one]
  have hodd := odd_card_cxK_inf_cxK_of_rigid_actor hnonab hKproper hL34 h16 hx2 hv2 hxv hvx
    hJ hvN hvact hxP hmax J hJ L hL
  have huL' : u ∉ centralizerSection L (pPrimeCoreOf 2 L) :=
    not_mem_centralizerSection_of_odd_card (P92.rig_pcomp hJ) huZ huv hu2 hodd
  have huv_act : u * v ∉ centralizerSection L (pPrimeCoreOf 2 L) := by
    intro h
    apply huL'
    apply (mapQuotient_normalizerMonoidHom_eq_one_iff huL).mp
    rw [← hact_uv]
    exact (mapQuotient_normalizerMonoidHom_eq_one_iff huvLN).mpr h
  have huv2 : orderOf (u * v) = 2 := (orderOf_eq_of_isConj hconj).symm.trans hv2
  have hvuv : u * v * v = v * (u * v) :=
    calc u * v * v = v * u * v := by rw [huv]
      _ = v * (u * v) := mul_assoc v u v
  have hvP : v ∈ Kz fullQ v := by
    have h := conj_mem_kz_of_mem_kz hxP g
    rwa [hg] at h
  have hcard : Nat.card ↥(RigidSet fullQ v) = Nat.card ↥(RigidSet fullQ x) := by
    rw [← hg]
    exact card_rigidSet_conj x g
  have hmax' : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(RigidSet fullQ s) ≤ Nat.card ↥(RigidSet fullQ v) := by
    intro s hs
    rw [hcard]
    exact hmax s hs
  have hr' : 1 < Nat.card ↥(RigidSet fullQ v) := by
    rw [hcard]
    exact hr
  obtain ⟨hnorm', hcls'⟩ := inner_or_projective_unitary_of_rigid_actor_of_one_lt_card hnonab
    hKproper hL34 h16 hv2 huv2 hconj hvuv hL huvLN huv_act hvP hmax' hr'
  obtain ⟨b', -, -, -, hin | hun⟩ := hcls' L hL
  swap
  · exfalso
    apply hnu
    have h1 :
        MulAut.mapQuotient (pPrimeCore 2 ↥L) (L.normalizerMonoidHom ⟨u * v, hnorm' L hL⟩) =
          MulAut.mapQuotient (pPrimeCore 2 ↥L) (L.normalizerMonoidHom ⟨u, huL⟩) := hact_uv
    rw [h1] at hun
    exact (isConj_congr_centerQuotientHom b' b₀ _).trans hun
  have hJL : cmap g⁻¹ L = J := by
    rw [← hLJ]
    exact cmap_inv_cancel g J
  have ht₁N : g⁻¹ * (u * v) * g⁻¹⁻¹ ∈ Subgroup.normalizer (J : Set G) := by
    have h := conj_mem_normalizer_cmap huvLN g⁻¹
    rwa [hJL] at h
  have hx : g⁻¹ * v * g⁻¹⁻¹ = x := by
    rw [← hg]
    group
  refine ⟨ht₁N, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← orderOf_eq_of_isConj (isConj_iff.mpr ⟨g⁻¹, rfl⟩)]
    exact huv2
  · exact (hxv.trans hconj).trans (isConj_iff.mpr ⟨g⁻¹, rfl⟩)
  · rw [← hx]
    calc g⁻¹ * (u * v) * g⁻¹⁻¹ * (g⁻¹ * v * g⁻¹⁻¹) = g⁻¹ * (u * v * v) * g⁻¹⁻¹ := by group
      _ = g⁻¹ * (v * (u * v)) * g⁻¹⁻¹ := by rw [hvuv]
      _ = g⁻¹ * v * g⁻¹⁻¹ * (g⁻¹ * (u * v) * g⁻¹⁻¹) := by group
  · have h := conj_not_mem_centralizerSection_cmap huv_act g⁻¹
    rwa [hJL] at h
  · exact mapQuotient_mem_range_conj_cmap hJL huvLN ht₁N hin

theorem exists_nonunitary_sq_of_projective_unitary :
∀
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hnonab : ∃ a b : G, a * b ≠ b * a)
    (_hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (_hL34 : CFSG.GH74.GLS.IsL34Quotient fullQ)
    (_h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (_hx2 : orderOf x = 2) (_hv2 : orderOf v = 2)
    (_hxv : IsConj x v) (_hvx : v * x = x * v)
    (_hJ : J ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    (_hvN : v ∈ Subgroup.normalizer (J : Set G))
    (_hvact : v ∉ CFSG.GH74.GLS.centralizerSection J
      (CFSG.GH74.GLS.pPrimeCoreOf 2 J))
    (_hxP : x ∈ CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x)
    (_hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ s) ≤
        Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x))
    (S₀ : Subgroup G)
    (_hS₀ : CFSG.ABGLocalTools.IsSylowOf 2 S₀ (Subgroup.centralizer ({x} : Set G)))
    (_hvS₀ : v ∈ S₀) {g : G} (_hg : g * x * g⁻¹ = v)
    (b : (kBar J ⧸ Subgroup.center (kBar J)) ≃* S)
    (_hunit : IsConj (MulAut.congr b (centerQuotientHom (kBar J)
      (MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨v, _hvN⟩))))
      (conjAutS r₄R)),
  ∃ u ∈ S₀ ⊓ zStar J, orderOf u = 2 ∧ u * v = v * u ∧ IsConj v (u * v) ∧
    ∃ (hn : u ∈ Subgroup.normalizer ((cmap g J : Subgroup G) : Set G))
      (b₀ : (kBar (cmap g J) ⧸ Subgroup.center (kBar (cmap g J))) ≃* S),
      ¬ IsConj (MulAut.congr b₀ (centerQuotientHom (kBar (cmap g J))
        (MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥(cmap g J))
          ((cmap g J).normalizerMonoidHom ⟨u, hn⟩)))) (conjAutS r₄R) := by
  intro G instG instFinite instSimple
    hnonab hKproper fullQ instFullQ hL34 h16 x v J hx2 hv2 hxv hvx
    hJ hvN hvact hxP hmax S₀ hS₀ hvS₀ g hg b hunit
  classical
  have hinvZ := inverts_center_kBar_of_projective_unitary hL34 h16 hJ _ b hunit
  obtain ⟨eZ, e4, heZ⟩ := exists_rigid_center_sylow_equiv_of_center_card_sixteen hJ hS₀ hL34 h16
  have hvW : ∀ w ∈ S₀ ⊓ zStar J, v * w * v⁻¹ = w⁻¹ :=
    conj_eq_inv_of_mem_inf_zStar eZ heZ hvS₀ hvN hinvZ
  obtain ⟨ζ₁, hζ₁, ζ₂, hζ₂, h12, h14, h24, h1sq, h2sq, h12sq⟩ :=
    exists_pair_of_mulEquiv_zmod_four (eZ.trans e4)
  have hζ₃ : ζ₁ * ζ₂ ∈ S₀ ⊓ zStar J := mul_mem hζ₁ hζ₂
  have hsq₃ : (ζ₁ * ζ₂) ^ 2 = ζ₁ ^ 2 * ζ₂ ^ 2 := (Commute.mul_pow h12 2)
  have h34 : (ζ₁ * ζ₂) ^ 4 = 1 := by
    rw [Commute.mul_pow h12, h14, h24, one_mul]
  have h3sq : (ζ₁ * ζ₂) ^ 2 ≠ 1 := by
    rw [hsq₃]
    exact h12sq
  obtain ⟨hu₁W, hu₁2, hu₁v, hu₁c⟩ := sq_mem_comm_isConj_of_inverts hvW hζ₁ h14 h1sq
  obtain ⟨hu₂W, hu₂2, hu₂v, hu₂c⟩ := sq_mem_comm_isConj_of_inverts hvW hζ₂ h24 h2sq
  obtain ⟨hu₃W, hu₃2, hu₃v, hu₃c⟩ := sq_mem_comm_isConj_of_inverts hvW hζ₃ h34 h3sq
  have hL : cmap g J ∈ RigidSet fullQ v := by
    have h := isRigidOfType_conj hJ g
    rw [hg] at h
    exact h
  have hnormW : ∀ u ∈ S₀ ⊓ zStar J, orderOf u = 2 → u * v = v * u →
      u ∈ Subgroup.normalizer ((cmap g J : Subgroup G) : Set G) := fun u huW hu2 huv =>
    normalizes_rigid_family_of_centralizing_involution hnonab hKproper hL34 h16 hx2 hv2 hxv
      hvx hJ hvN hvact hxP hmax S₀ hS₀ hvS₀ J hJ u hu2 huW.1
      (Subgroup.mem_centralizer_singleton_iff.mpr huv) huW.2.2 (cmap g J) hL
  have hn₁ := hnormW _ hu₁W hu₁2 hu₁v
  have hn₂ := hnormW _ hu₂W hu₂2 hu₂v
  have hn₃ := hnormW _ hu₃W hu₃2 hu₃v
  obtain ⟨b₀⟩ := nonempty_centerQuotient_equiv_of_mem_rigidSet hL34 h16 hL
  by_cases hU₁ : IsConj (MulAut.congr b₀ (centerQuotientHom (kBar (cmap g J))
      (MulAut.mapQuotient (pPrimeCore 2 ↥(cmap g J))
        ((cmap g J).normalizerMonoidHom ⟨ζ₁ ^ 2, hn₁⟩)))) (conjAutS r₄R)
  · by_cases hU₂ : IsConj (MulAut.congr b₀ (centerQuotientHom (kBar (cmap g J))
        (MulAut.mapQuotient (pPrimeCore 2 ↥(cmap g J))
          ((cmap g J).normalizerMonoidHom ⟨ζ₂ ^ 2, hn₂⟩)))) (conjAutS r₄R)
    · have hU₃ : ¬ IsConj (MulAut.congr b₀ (centerQuotientHom (kBar (cmap g J))
          (MulAut.mapQuotient (pPrimeCore 2 ↥(cmap g J))
            ((cmap g J).normalizerMonoidHom ⟨(ζ₁ * ζ₂) ^ 2, hn₃⟩)))) (conjAutS r₄R) := by
        rw [mapQuotient_normalizerMonoidHom_congr hsq₃ hn₃ (mul_mem hn₁ hn₂),
          mapQuotient_normalizerMonoidHom_mul hn₁ hn₂, map_mul, map_mul]
        exact not_isConj_r₄_mul_of_isConj_r₄ hU₁ hU₂
      exact ⟨_, hu₃W, hu₃2, hu₃v, hu₃c, hn₃, b₀, hU₃⟩
    · exact ⟨_, hu₂W, hu₂2, hu₂v, hu₂c, hn₂, b₀, hU₂⟩
  · exact ⟨_, hu₁W, hu₁2, hu₁v, hu₁c, hn₁, b₀, hU₁⟩

theorem exists_inner_rigid_actor_of_one_lt_card :
∀
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hnonab : ∃ a b : G, a * b ≠ b * a)
    (_hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (_hL34 : CFSG.GH74.GLS.IsL34Quotient fullQ)
    (_h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (_hx2 : orderOf x = 2) (_hv2 : orderOf v = 2)
    (_hxv : IsConj x v) (_hvx : v * x = x * v)
    (_hJ : J ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    (_hvN : v ∈ Subgroup.normalizer (J : Set G))
    (_hvact : v ∉ CFSG.GH74.GLS.centralizerSection J
      (CFSG.GH74.GLS.pPrimeCoreOf 2 J))
    (_hxP : x ∈ CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x)
    (_hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ s) ≤
        Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x))
    (_hr : 1 < Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)),
  ∃ (t : G) (htN : t ∈ Subgroup.normalizer (J : Set G)),
    orderOf t = 2 ∧ IsConj x t ∧ t * x = x * t ∧
      t ∉ CFSG.GH74.GLS.centralizerSection J (CFSG.GH74.GLS.pPrimeCoreOf 2 J) ∧
      MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨t, htN⟩) ∈
        (MulAut.conj : CFSG.GH74.GLS.kBar J →* MulAut (CFSG.GH74.GLS.kBar J)).range := by
  intro G instG instFinite instSimple
    hnonab hKproper fullQ instFullQ hL34 h16 x v J hx2 hv2 hxv hvx
    hJ hvN hvact hxP hmax hr
  classical
  obtain ⟨hnorm, hcls⟩ := inner_or_projective_unitary_of_rigid_actor_of_one_lt_card hnonab
    hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN hvact hxP hmax hr
  obtain ⟨b, -, -, -, hin | hunit⟩ := hcls J hJ
  · exact ⟨v, hvN, hv2, hxv, hvx, hvact, hin⟩
  obtain ⟨S₀, hS₀, hvS₀⟩ := exists_isSylowOf_centralizer_mem_of_orderOf_eq_two hv2 hvx
  obtain ⟨g, hg⟩ := isConj_iff.mp hxv
  obtain ⟨u, huW, hu2, huv, huc, hn, b₀, hU⟩ := exists_nonunitary_sq_of_projective_unitary
    hnonab hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN hvact hxP hmax S₀ hS₀ hvS₀ hg b hunit
  exact ⟨_, inner_actor_conj_mul_of_not_isConj_r₄ hnonab hKproper hL34 h16 hx2 hv2 hxv hvx hJ
    hvN hvact hxP hmax hr hg rfl huW.2 hu2 huv huc hn b₀ hU⟩


section Pair

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_isSylowOf_centralizer_le_of_isPGroup {x : G} {P : Subgroup G}
    (hP : IsPGroup 2 ↥P) (hPC : P ≤ Subgroup.centralizer ({x} : Set G)) :
    ∃ S₀ : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 2 S₀ (Subgroup.centralizer ({x} : Set G)) ∧ P ≤ S₀ := by
  have : Fact (Nat.Prime 2) := Nat.fact_prime_two
  obtain ⟨Q, hQ⟩ :=
    (hP.comap_subtype (K := Subgroup.centralizer ({x} : Set G))).exists_le_sylow
  refine ⟨(Q : Subgroup ↥(Subgroup.centralizer ({x} : Set G))).map
    (Subgroup.centralizer ({x} : Set G)).subtype, ⟨Q, rfl⟩, ?_⟩
  intro p hp
  have hmem : (⟨p, hPC hp⟩ : ↥(Subgroup.centralizer ({x} : Set G))) ∈
      (Q : Subgroup ↥(Subgroup.centralizer ({x} : Set G))) := by
    apply hQ
    rw [Subgroup.comap_subtype]
    exact hp
  exact Subgroup.mem_map_of_mem (Subgroup.centralizer ({x} : Set G)).subtype hmem

omit [Finite G] in
theorem isPGroup_zpowers_sup_zpowers {v y : G} (hv : v ^ 2 = 1) (hy : y ^ 4 = 1)
    (hvy : v * y = y * v) : IsPGroup 2 ↥(Subgroup.zpowers v ⊔ Subgroup.zpowers y) := by
  have hzv : IsPGroup 2 ↥(Subgroup.zpowers v) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      simpa [Nat.card_zpowers] using orderOf_dvd_of_pow_eq_one hv)
  have hzy : IsPGroup 2 ↥(Subgroup.zpowers y) :=
    IsPGroup.of_card_dvd_pow (n := 2) (by
      simpa [Nat.card_zpowers] using orderOf_dvd_of_pow_eq_one hy)
  have hnorm : Subgroup.zpowers v ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro p hp k hk
    rcases (Subgroup.mem_zpowers_iff).mp hp with ⟨m, rfl⟩
    rcases (Subgroup.mem_zpowers_iff).mp hk with ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    have hcomm : Commute (v ^ m) (y ^ n) := ((commute_iff_eq v y).mpr hvy).zpow_zpow m n
    rw [show v ^ m * y ^ n * (v ^ m)⁻¹ = y ^ n by
      rw [hcomm.eq]
      group]
  exact IsPGroup.to_sup_of_normal_right' hzv hzy hnorm

omit [Finite G] in
theorem commute_of_mem_inf_zStar {J S₀ : Subgroup G}
    (eZ : ↥(S₀ ⊓ zStar J) ≃* Subgroup.center (kBar J)) {a b : G}
    (ha : a ∈ S₀ ⊓ zStar J) (hb : b ∈ S₀ ⊓ zStar J) : a * b = b * a := by
  have hub : ∀ x y : ↥(Subgroup.center (kBar J)), x * y = y * x := by
    intro x y
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp x.2 (y : kBar J)).symm
  have key : (⟨a, ha⟩ : ↥(S₀ ⊓ zStar J)) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
    apply eZ.injective
    simp only [map_mul]
    exact hub _ _
  exact congrArg Subtype.val key

open scoped commutatorElement in
theorem commute_of_mem_isPCompIn_of_ne {x : G} {J K : Subgroup G}
    (hJ : IsPCompIn 2 (Subgroup.centralizer ({x} : Set G)) J)
    (hK : IsPCompIn 2 (Subgroup.centralizer ({x} : Set G)) K) (hne : J ≠ K)
    {P : Subgroup G} (hP : IsPGroup 2 ↥P) {a b : G} (ha : a ∈ P ⊓ J) (hb : b ∈ P ⊓ K) :
    a * b = b * a := by
  have : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have haJ : a ∈ J := ha.2
  have hbK : b ∈ K := hb.2
  have hmem : ⁅b, a⁆ ∈ pPrimeCoreOf 2 K := by
    have h := CFSG.GH74.GLS.Stage1.Thm2.Recip.le_cSec_of_ne hJ hK hne haJ
    exact h.2.2 b hbK
  have hmemP : ⁅b, a⁆ ∈ P :=
    Subgroup.commutator_le_self P (Subgroup.commutator_mem_commutator hb.1 ha.1)
  have hcop : ¬ 2 ∣ Nat.card (pPrimeCoreOf 2 K) := by
    show ¬ 2 ∣ Nat.card ((pPrimeCore 2 ↥K).map K.subtype)
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact (Nat.prime_two.coprime_iff_not_dvd).mp (pPrimeCore_coprime_card (p := 2) (G := ↥K))
  have hnotdvd : ¬ 2 ∣ orderOf ⁅b, a⁆ := fun hd =>
    hcop (hd.trans (Subgroup.orderOf_dvd_natCard (pPrimeCoreOf 2 K) hmem))
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hdvd : orderOf ⁅b, a⁆ ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.orderOf_dvd_natCard P hmemP
  have h1 : ⁅b, a⁆ = 1 :=
    orderOf_eq_one_iff.mp ((Nat.prime_two.coprime_pow_of_not_dvd hnotdvd).eq_one_of_dvd hdvd)
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

end Pair

theorem inner_actor_conj_mul_pair_of_not_isConj_r₄
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (hL34 : IsL34Quotient fullQ) (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (hx2 : orderOf x = 2) (hv2 : orderOf v = 2) (hxv : IsConj x v) (hvx : v * x = x * v)
    (hJ : J ∈ RigidSet fullQ x) (hvN : v ∈ Subgroup.normalizer (J : Set G))
    (hvact : v ∉ centralizerSection J (pPrimeCoreOf 2 J)) (hxP : x ∈ Kz fullQ x)
    (hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(RigidSet fullQ s) ≤ Nat.card ↥(RigidSet fullQ x))
    (hr : 1 < Nat.card ↥(RigidSet fullQ x))
    {g : G} (hg : g * x * g⁻¹ = v)
    {u : G} (huZ : u ∈ zStar J) (hu2 : orderOf u = 2) (huv : u * v = v * u)
    (hconj : IsConj v (u * v))
    (huL : u ∈ Subgroup.normalizer ((cmap g J : Subgroup G) : Set G))
    (b₀ : (kBar (cmap g J) ⧸ Subgroup.center (kBar (cmap g J))) ≃* S)
    (hnu : ¬ IsConj (MulAut.congr b₀ (centerQuotientHom (kBar (cmap g J))
      (MulAut.mapQuotient (pPrimeCore 2 ↥(cmap g J))
        ((cmap g J).normalizerMonoidHom ⟨u, huL⟩)))) (conjAutS r₄R))
    {K' : Subgroup G} {c : G} (hcu : c * u = u * c)
    (hcv : c * v = v * c) (hswap : cmap c (cmap g J) = cmap g K') :
    ∃ htN : g⁻¹ * (u * v) * g⁻¹⁻¹ ∈ Subgroup.normalizer (K' : Set G),
      g⁻¹ * (u * v) * g⁻¹⁻¹ ∉ centralizerSection K' (pPrimeCoreOf 2 K') ∧
      MulAut.mapQuotient (pPrimeCore 2 ↥K')
          (K'.normalizerMonoidHom ⟨g⁻¹ * (u * v) * g⁻¹⁻¹, htN⟩) ∈
        (MulAut.conj : kBar K' →* MulAut (kBar K')).range := by
  classical
  obtain ⟨htJ, -, -, -, htact, htin⟩ :=
    inner_actor_conj_mul_of_not_isConj_r₄ hnonab hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN
      hvact hxP hmax hr hg rfl huZ hu2 huv hconj huL b₀ hnu
  let c' : G := g⁻¹ * c * g
  have hcmap : cmap c' J = K' := by
    have h1 : cmap c' J = cmap g⁻¹ (cmap c (cmap g J)) := by
      rw [← cmap_cmap, ← cmap_cmap]
    rw [h1, hswap, cmap_inv_cancel]
  have hmem : c * (u * v) = (u * v) * c := by
    rw [← mul_assoc, hcu, mul_assoc, hcv, ← mul_assoc]
  have hct : c' * (g⁻¹ * (u * v) * g⁻¹⁻¹) * c'⁻¹ = g⁻¹ * (u * v) * g⁻¹⁻¹ := by
    have h1 : c' * (g⁻¹ * (u * v) * g⁻¹⁻¹) * c'⁻¹ =
        g⁻¹ * (c * (u * v) * c⁻¹) * g := by
      simp only [c']
      group
    rw [h1, hmem]
    group
  have hnorm' : c' * (g⁻¹ * (u * v) * g⁻¹⁻¹) * c'⁻¹ ∈
      Subgroup.normalizer (K' : Set G) := by
    have h := conj_mem_normalizer_cmap htJ c'
    rwa [hcmap] at h
  have hact' : c' * (g⁻¹ * (u * v) * g⁻¹⁻¹) * c'⁻¹ ∉
      centralizerSection K' (pPrimeCoreOf 2 K') := by
    have h := conj_not_mem_centralizerSection_cmap htact c'
    rwa [hcmap] at h
  have hin' : MulAut.mapQuotient (pPrimeCore 2 ↥K')
      (K'.normalizerMonoidHom ⟨c' * (g⁻¹ * (u * v) * g⁻¹⁻¹) * c'⁻¹, hnorm'⟩) ∈
      (MulAut.conj : kBar K' →* MulAut (kBar K')).range :=
    mapQuotient_mem_range_conj_cmap hcmap htJ hnorm' htin
  have htN : g⁻¹ * (u * v) * g⁻¹⁻¹ ∈ Subgroup.normalizer (K' : Set G) := by
    rw [← hct]
    exact hnorm'
  refine ⟨htN, ?_, ?_⟩
  · rw [← hct]
    exact hact'
  · have h := mapQuotient_normalizerMonoidHom_congr hct hnorm' htN
    rw [← h]
    exact hin'

theorem exists_inner_rigid_actor_pair_of_one_lt_card :
∀
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hnonab : ∃ a b : G, a * b ≠ b * a)
    (_hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (_hL34 : CFSG.GH74.GLS.IsL34Quotient fullQ)
    (_h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (_hx2 : orderOf x = 2) (_hv2 : orderOf v = 2)
    (_hxv : IsConj x v) (_hvx : v * x = x * v)
    (_hJ : J ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    (_hvN : v ∈ Subgroup.normalizer (J : Set G))
    (_hvact : v ∉ CFSG.GH74.GLS.centralizerSection J
      (CFSG.GH74.GLS.pPrimeCoreOf 2 J))
    (_hxP : x ∈ CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x)
    (_hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ s) ≤
        Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x))
    (_hr : 1 < Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x))
    {K : Subgroup G} (_hK : K ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    {g y : G} (_hg : g * x * g⁻¹ = v) (_hyZ : y ∈ CFSG.GH74.GLS.zStar J) (_hy4 : y ^ 4 = 1)
    (_hyv : y * v = v * y) (_hswap : cmap y (cmap g J) = cmap g K),
  ∃ (t : G) (htJ : t ∈ Subgroup.normalizer (J : Set G))
    (htK : t ∈ Subgroup.normalizer (K : Set G)),
    orderOf t = 2 ∧ IsConj x t ∧ t * x = x * t ∧
      t ∉ CFSG.GH74.GLS.centralizerSection J (CFSG.GH74.GLS.pPrimeCoreOf 2 J) ∧
      MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨t, htJ⟩) ∈
        (MulAut.conj : CFSG.GH74.GLS.kBar J →* MulAut (CFSG.GH74.GLS.kBar J)).range ∧
      t ∉ CFSG.GH74.GLS.centralizerSection K (CFSG.GH74.GLS.pPrimeCoreOf 2 K) ∧
      MulAut.mapQuotient (CFSG.pPrimeCore 2 ↥K) (K.normalizerMonoidHom ⟨t, htK⟩) ∈
        (MulAut.conj : CFSG.GH74.GLS.kBar K →* MulAut (CFSG.GH74.GLS.kBar K)).range := by
  intro G instG instFinite instSimple
    hnonab hKproper fullQ instFullQ hL34 h16 x v J hx2 hv2 hxv hvx
    hJ hvN hvact hxP hmax hr K hK g y hg hyZ hy4 hyv hswap
  classical
  obtain ⟨hnorm, hcls⟩ := inner_or_projective_unitary_of_rigid_actor_of_one_lt_card hnonab
    hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN hvact hxP hmax hr
  by_cases hJK : J = K
  ·
    subst hJK
    obtain ⟨t, htN, ht2, htconj, httx, htact, htin⟩ :=
      exists_inner_rigid_actor_of_one_lt_card hnonab hKproper hL34 h16 hx2 hv2 hxv hvx
        hJ hvN hvact hxP hmax hr
    exact ⟨t, htN, htN, ht2, htconj, httx, htact, htin, htact, htin⟩
  have hv2' : v ^ 2 = 1 := by
    rw [← hv2]
    exact pow_orderOf_eq_one v
  have hvC : v ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hvx
  have hyC : y ∈ Subgroup.centralizer ({x} : Set G) := (P92.rig_pcomp hJ).1 hyZ.1
  have hPC : Subgroup.zpowers v ⊔ Subgroup.zpowers y ≤
      Subgroup.centralizer ({x} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hvC) (Subgroup.zpowers_le.mpr hyC)
  obtain ⟨S₀, hS₀, hle⟩ := exists_isSylowOf_centralizer_le_of_isPGroup
    (isPGroup_zpowers_sup_zpowers hv2' hy4 hyv.symm) hPC
  have hvS₀ : v ∈ S₀ := hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers v))
  have hyS₀ : y ∈ S₀ := hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have hyW : y ∈ S₀ ⊓ zStar J := ⟨hyS₀, hyZ⟩
  have hyJ : y ∈ S₀ ⊓ J := ⟨hyS₀, hyZ.1⟩
  obtain ⟨bJ, hmJ, -, -, hinJ | hunitJ⟩ := hcls J hJ
  · obtain ⟨bK, hmK, -, -, hinK | hunitK⟩ := hcls K hK
    ·
      have hvactK : v ∉ centralizerSection K (pPrimeCoreOf 2 K) := fun h =>
        hmK ((mapQuotient_normalizerMonoidHom_eq_one_iff (hnorm K hK)).mpr h)
      exact ⟨v, hnorm J hJ, hnorm K hK, hv2, hxv, hvx, hvact, hinJ, hvactK, hinK⟩
    ·
      have hvactK : v ∉ centralizerSection K (pPrimeCoreOf 2 K) := fun h =>
        hmK ((mapQuotient_normalizerMonoidHom_eq_one_iff (hnorm K hK)).mpr h)
      obtain ⟨u, huW, hu2, huv, huc, hn, b₀, hnu⟩ :=
        exists_nonunitary_sq_of_projective_unitary hnonab hKproper hL34 h16 hx2 hv2 hxv hvx
          hK (hnorm K hK) hvactK hxP hmax S₀ hS₀ hvS₀ hg bK hunitK
      have huK : u ∈ S₀ ⊓ K := ⟨huW.1, huW.2.1⟩
      have huy : y * u = u * y :=
        (commute_of_mem_isPCompIn_of_ne (P92.rig_pcomp hK) (P92.rig_pcomp hJ) (Ne.symm hJK)
          hS₀.isPGroup huK hyJ).symm
      have hu_inv : u⁻¹ = u := by
        apply inv_eq_of_mul_eq_one_right
        rw [← pow_two, ← hu2, pow_orderOf_eq_one]
      have hv_inv : v⁻¹ = v := by
        apply inv_eq_of_mul_eq_one_right
        rw [← pow_two, ← hv2, pow_orderOf_eq_one]
      have hcu : y⁻¹ * u = u * y⁻¹ := by
        have h := congrArg Inv.inv huy
        simpa only [mul_inv_rev, hu_inv] using h.symm
      have hcv : y⁻¹ * v = v * y⁻¹ := by
        have h := congrArg Inv.inv hyv
        simpa only [mul_inv_rev, hv_inv] using h.symm
      have hswap' : cmap y⁻¹ (cmap g K) = cmap g J := by
        rw [← hswap]
        exact cmap_inv_cancel y (cmap g J)
      obtain ⟨htK, ht2, htconj, httx, htactK, htinK⟩ :=
        inner_actor_conj_mul_of_not_isConj_r₄ hnonab hKproper hL34 h16 hx2 hv2 hxv hvx
          hK (hnorm K hK) hvactK hxP hmax hr hg rfl huW.2 hu2 huv huc hn b₀ hnu
      obtain ⟨htJ, htactJ, htinJ⟩ :=
        inner_actor_conj_mul_pair_of_not_isConj_r₄ hnonab hKproper hL34 h16 hx2 hv2 hxv hvx
          hK (hnorm K hK) hvactK hxP hmax hr hg huW.2 hu2 huv huc hn b₀ hnu hcu hcv hswap'
      exact ⟨g⁻¹ * (u * v) * g⁻¹⁻¹, htJ, htK, ht2, htconj, httx, htactJ, htinJ, htactK, htinK⟩
  ·
    obtain ⟨u, huW, hu2, huv, huc, hn, b₀, hnu⟩ :=
      exists_nonunitary_sq_of_projective_unitary hnonab hKproper hL34 h16 hx2 hv2 hxv hvx
        hJ hvN hvact hxP hmax S₀ hS₀ hvS₀ hg bJ hunitJ
    obtain ⟨eZ, -, -⟩ := exists_rigid_center_sylow_equiv_of_center_card_sixteen hJ hS₀ hL34 h16
    have hcu : y * u = u * y := commute_of_mem_inf_zStar eZ hyW huW
    obtain ⟨htJ, ht2, htconj, httx, htactJ, htinJ⟩ :=
      inner_actor_conj_mul_of_not_isConj_r₄ hnonab hKproper hL34 h16 hx2 hv2 hxv hvx
        hJ hvN hvact hxP hmax hr hg rfl huW.2 hu2 huv huc hn b₀ hnu
    obtain ⟨htK, htactK, htinK⟩ :=
      inner_actor_conj_mul_pair_of_not_isConj_r₄ hnonab hKproper hL34 h16 hx2 hv2 hxv hvx
        hJ hvN hvact hxP hmax hr hg huW.2 hu2 huv huc hn b₀ hnu hcu hyv hswap
    exact ⟨g⁻¹ * (u * v) * g⁻¹⁻¹, htJ, htK, ht2, htconj, httx, htactJ, htinJ, htactK, htinK⟩

end CFSG.GH74.GLS.NT44


end
