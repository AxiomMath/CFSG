module

public import CFSG.GroupTheory.SylowAutTrivialPerfect
import CFSG.ClassicalInvolution.Omega
import CFSG.Foundations.QuasisimpleMulEquiv
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.QuasithinUnique.Bridge

open Subgroup CFSG.RankThree.PartOne

private theorem open_isQuasisimple_of_isQuasisimple_strc {Q : Type*} [Group Q]
    (h : CFSG.IsQuasisimple Q) : CFSG.Open.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

private theorem map_conj_eq_self_of_mem_strc {X : Type} [Group X] [Finite X] {K D : Subgroup X}
    (hKq : CFSG.IsQuasisimple ↥K) (hKs : K.IsSubnormal)
    (hR : SylowAutTrivial (↥K ⧸ Subgroup.center ↥K)) (P : Sylow 2 ↥K)
    (hDP : D ≤ centralizer (((P : Subgroup ↥K).map K.subtype : Subgroup X) : Set X))
    {d : X} (hd : d ∈ D) : K.map (MulAut.conj d).toMonoidHom = K := by
  by_contra hne
  let K' : Subgroup X := K.map (MulAut.conj d).toMonoidHom
  have hK's : K'.IsSubnormal :=
    Subgroup.IsSubnormal.map (f := (MulAut.conj d).toMonoidHom) (MulAut.conj d).surjective hKs
  have hK'q : CFSG.IsQuasisimple ↥K' :=
    CFSG.IsQuasisimple.of_mulEquiv
      (K.equivMapOfInjective (MulAut.conj d).toMonoidHom (MulAut.conj d).injective).symm hKq
  have hcomm : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x :=
    CFSG.ClassicalInvolution.commute_of_isSubnormal_of_isQuasisimple
      (CFSG.Open.IsSubnormal.of_mathlib hKs)
      (CFSG.Open.IsSubnormal.of_mathlib hK's)
      (open_isQuasisimple_of_isQuasisimple_strc hKq)
      (open_isQuasisimple_of_isQuasisimple_strc hK'q) (Ne.symm hne)
  have hP'le : (P : Subgroup ↥K).map K.subtype ≤ K' := by
    intro p hp
    obtain ⟨q, hqP, hq⟩ := Subgroup.mem_map.mp hp
    have hqK : p ∈ K := hq ▸ q.2
    have hpd : p * d = d * p := (Subgroup.mem_centralizer_iff.mp (hDP hd)) p hp
    refine Subgroup.mem_map.mpr ⟨p, hqK, ?_⟩
    show d * p * d⁻¹ = p
    rw [← hpd]
    group
  have hcenter : (P : Subgroup ↥K) ≤ Subgroup.center ↥K := by
    intro p hp
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hp' : (p : X) ∈ (P : Subgroup ↥K).map K.subtype :=
      Subgroup.mem_map.mpr ⟨p, hp, rfl⟩
    exact hcomm (y : X) y.2 (p : X) (hP'le hp')
  have hdvd : 2 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) :=
    even_iff_two_dvd.mp (hR.even_card hKq.2.2)
  have hQbot : (P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center ↥K)) :
      Subgroup (↥K ⧸ Subgroup.center ↥K)) = ⊥ := by
    rw [Sylow.coe_mapSurjective, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hcenter
  exact (P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center ↥K))).ne_bot_of_dvd_card
    hdvd hQbot

theorem SylowAutTrivial.le_centralizer {X : Type} [Group X] [Finite X] {K D : Subgroup X}
    (hKq : CFSG.IsQuasisimple ↥K) (hKs : K.IsSubnormal)
    (hR : SylowAutTrivial (↥K ⧸ center ↥K)) (P : Sylow 2 ↥K) (hD : oResidualTwo ↥D = ⊤)
    (hDP : D ≤ centralizer (((P : Subgroup ↥K).map K.subtype : Subgroup X) : Set X)) :
    D ≤ centralizer (K : Set X) := by
  have hnorm : D ≤ Subgroup.normalizer (K : Set X) := fun d hd =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (map_conj_eq_self_of_mem_strc hKq hKs hR P hDP hd)
  let ψ : ↥D →* Subgroup.normalizer (K : Set X) := Subgroup.inclusion hnorm
  let φ : ↥D →* MulAut ↥K := (Subgroup.normalizerMonoidHom K).comp ψ
  have hφ : ∀ e : ↥D, ∀ x ∈ (P : Subgroup ↥K), φ e x = x := by
    intro e x hx
    apply Subtype.ext
    have hx' : (x : X) ∈ (P : Subgroup ↥K).map K.subtype := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hxe : (x : X) * (e : X) = (e : X) * (x : X) :=
      (Subgroup.mem_centralizer_iff.mp (hDP e.2)) (x : X) hx'
    have hv : ((φ e) x : X) = (e : X) * (x : X) * (e : X)⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe K (Subgroup.inclusion hnorm e) x
    rw [hv, ← hxe]
    group
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 : φ ⟨d, hd⟩ = 1 :=
    SylowAutTrivial.eq_one_of_isPerfect hKq.1 hR hD φ P hφ ⟨d, hd⟩
  have h2 : ((φ ⟨d, hd⟩) ⟨k, hk⟩ : X) = k := by
    rw [h1]
    rfl
  have h3 : d * k * d⁻¹ = k := by
    have hv : ((φ ⟨d, hd⟩) ⟨k, hk⟩ : X) = d * k * d⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe K (Subgroup.inclusion hnorm ⟨d, hd⟩) ⟨k, hk⟩
    rw [hv] at h2
    exact h2
  have h4 : d * k = k * d := by
    calc d * k = d * k * d⁻¹ * d := by group
      _ = k * d := by rw [h3]
  exact h4.symm

end CFSG.QuasithinUnique.Bridge
