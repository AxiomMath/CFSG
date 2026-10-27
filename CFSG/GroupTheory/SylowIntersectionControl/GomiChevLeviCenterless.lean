module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs
import CFSG.GroupTheory.SubgroupOfQuotientMapCentral
import CFSG.GroupTheory.SubgroupOfQuotientMapConj
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAtomQuotientMap
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevCentralQuotient
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevTransport
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChevMap
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevTrichotomyLocal
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedCoprimeMap
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedEmbedded

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G Γ : Type} [Group G] [Group Γ] {L : Subgroup G}
  {ψ : ↥(normalizer (L : Set G)) →* Γ}

private def GomiChevLeviCenterless : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L U H : Subgroup G), IsGomiChevTwo ↥L →
    center ↥L = ⊥ → IsSylowOf 2 U L → IsPGroup 2 H → H ≤ normalizer (L : Set G) →
    H ≤ normalizer (U : Set G) →
    L ⊓ normalizer (U : Set G) < L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) →
    L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) < L →
    pCoreOf 2 (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) = H ⊓ L →
    IsPIsolatedOver 2 (L ⊓ normalizer (H : Set G)) (H ⊓ L) →
    IsGomiAtom L U (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) ∨
      ∀ A : Subgroup G, IsGomiAtom L U A →
        A ≤ L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) →
        ∃ h ∈ H, A.map (MulAut.conj h).toMonoidHom ≠ A

private abbrev gomiMap (ψ : ↥(normalizer (L : Set G)) →* Γ) (K : Subgroup G) : Subgroup Γ :=
  (K.subgroupOf (normalizer (L : Set G))).map ψ

private lemma inf_centralizer_subgroupOf_eq_center (L : Subgroup G) :
    (L ⊓ centralizer (L : Set G)).subgroupOf L = center ↥L := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨-, hx⟩ g
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx) g g.2)
  · intro hx
    refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    exact congrArg Subtype.val (hx ⟨g, hg⟩)

private lemma natCard_inf_centralizer_eq_card_center (L : Subgroup G) :
    Nat.card ↥(L ⊓ centralizer (L : Set G)) = Nat.card (center ↥L) := by
  rw [← inf_centralizer_subgroupOf_eq_center L]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm

private lemma inf_centralizer_le_inf_normalizer {L : Subgroup G} {S : Subgroup G} (hSL : S ≤ L) :
    L ⊓ centralizer (L : Set G) ≤ L ⊓ normalizer (S : Set G) :=
  le_inf inf_le_left (inf_le_right.trans
    ((Subgroup.centralizer_le (fun _ hx => hSL hx)).trans
      (Subgroup.centralizer_le_normalizer (S : Set G))))

private lemma inf_centralizer_le_centralizer {L : Subgroup G} {S : Subgroup G} (hSL : S ≤ L) :
    L ⊓ centralizer (L : Set G) ≤ centralizer (S : Set G) :=
  inf_le_right.trans (Subgroup.centralizer_le (fun _ hx => hSL hx))

private lemma coprime_card_inf_centralizer [Finite G] {L : Subgroup G}
    (hL : IsGomiChevTwo ↥L) :
    Nat.Coprime (Nat.card ↥(L ⊓ centralizer (L : Set G))) 2 := by
  rw [natCard_inf_centralizer_eq_card_center L]
  exact hL.coprime_card_center

theorem IsGomiChevTwo.not_two_dvd_relIndex_inf_centralizer [Finite G] (hL : IsGomiChevTwo ↥L)
    (S : Subgroup G) : ¬ 2 ∣ S.relIndex (L ⊓ centralizer (L : Set G)) := by
  intro h
  have hdvd : 2 ∣ Nat.card (center ↥L) := by
    rw [← natCard_inf_centralizer_eq_card_center L]
    exact h.trans (Subgroup.relIndex_dvd_card S (L ⊓ centralizer (L : Set G)))
  exact (Nat.prime_two.coprime_iff_not_dvd.mp hL.coprime_card_center.symm) hdvd

theorem IsGomiChevTwo.map_subgroupOf_normalizer [Finite G]
    (hker : ψ.ker = (L ⊓ centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)))
    (hL : IsGomiChevTwo ↥L) :
    IsGomiChevTwo ↥((L.subgroupOf (normalizer (L : Set G))).map ψ) ∧
      center ↥((L.subgroupOf (normalizer (L : Set G))).map ψ) = ⊥ := by
  let f : ↥L →* Γ := ψ.comp (Subgroup.inclusion le_normalizer)
  have hrange : f.range = (L.subgroupOf (normalizer (L : Set G))).map ψ := by
    change (ψ.comp (Subgroup.inclusion le_normalizer)).range =
      (L.subgroupOf (normalizer (L : Set G))).map ψ
    rw [MonoidHom.range_comp, Subgroup.inclusion_range le_normalizer]
  have hker' : f.ker = center ↥L := by
    have h1 : f.ker = (L ⊓ centralizer (L : Set G)).subgroupOf L := by
      ext k
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      change ψ (Subgroup.inclusion le_normalizer k) = 1 ↔
        (k : G) ∈ L ⊓ centralizer (L : Set G)
      rw [← MonoidHom.mem_ker (f := ψ), hker, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
    rw [h1, inf_centralizer_subgroupOf_eq_center L]
  let e : ↥((L.subgroupOf (normalizer (L : Set G))).map ψ) ≃* ↥L ⧸ center ↥L :=
    (MulEquiv.subgroupCongr hrange.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hker'))
  have hZq : center (↥L ⧸ center ↥L) = ⊥ := by
    have : Group.IsPerfect ↥L := hL.1.1
    exact Group.IsPerfect.center_quotient_center_eq_bot ↥L
  refine ⟨?_, ?_⟩
  · exact IsGomiChevTwo.of_mulEquiv e.symm (IsGomiChevTwo.quotient_center hL)
  · rw [← Subgroup.map_center_eq e.symm, hZq, Subgroup.map_bot]

private lemma coprime_card_ker_subgroupOf_normalizer [Finite G]
    (hker : ψ.ker = (L ⊓ centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)))
    (hL : IsGomiChevTwo ↥L) : Nat.Coprime (Nat.card ψ.ker) 2 := by
  have hcard : Nat.card ψ.ker = Nat.card (center ↥L) := by
    rw [hker]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans le_normalizer)).toEquiv,
      natCard_inf_centralizer_eq_card_center L]
  rw [hcard]
  exact hL.coprime_card_center

private lemma subgroupOf_inf_ker_le_centralizer {H : Subgroup G}
    (hker : ψ.ker = (L ⊓ centralizer (L : Set G)).subgroupOf (normalizer (L : Set G))) :
    ((L ⊓ normalizer (H : Set G)).subgroupOf (normalizer (L : Set G))) ⊓ ψ.ker ≤
      centralizer (((L ⊓ normalizer (H : Set G)).subgroupOf (normalizer (L : Set G)) :
        Subgroup ↥(normalizer (L : Set G))) : Set ↥(normalizer (L : Set G))) := by
  intro y hy
  obtain ⟨hyK, hyker⟩ := Subgroup.mem_inf.mp hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  apply Subtype.ext
  have hyZ : (y : G) ∈ L ⊓ centralizer (L : Set G) := by
    rw [hker] at hyker
    exact Subgroup.mem_subgroupOf.mp hyker
  have hzL : (z : G) ∈ L := (Subgroup.mem_subgroupOf.mp hz).1
  exact Subgroup.mem_centralizer_iff.mp hyZ.2 (z : G) hzL

theorem IsPIsolatedOver.map_subgroupOf_normalizer [Finite G] [Finite Γ] {H : Subgroup G}
    (hker : ψ.ker = (L ⊓ centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)))
    (hL : IsGomiChevTwo ↥L) (hH : IsPGroup 2 H) (hHL : H ≤ normalizer (L : Set G))
    (hiso : IsPIsolatedOver 2 (L ⊓ normalizer (H : Set G)) (H ⊓ L)) :
    IsPIsolatedOver 2
      (((L ⊓ normalizer (H : Set G)).subgroupOf (normalizer (L : Set G))).map ψ)
      (((H ⊓ L).subgroupOf (normalizer (L : Set G))).map ψ) := by
  let X : Subgroup G := normalizer (L : Set G)
  have hKX : L ⊓ normalizer (H : Set G) ≤ X := inf_le_left.trans le_normalizer
  have hHX : H ⊓ L ≤ X := inf_le_left.trans hHL
  have hisoX : IsPIsolatedOver 2 ((L ⊓ normalizer (H : Set G)).subgroupOf X)
      ((H ⊓ L).subgroupOf X) :=
    (isPIsolatedOver_subgroupOf_iff hHX hKX).2 hiso
  have hH2 : IsPGroup 2 ((H ⊓ L).subgroupOf X) :=
    hH.to_inf_left.of_equiv (Subgroup.subgroupOfEquivOfLe hHX).symm
  have hKNG : L ⊓ normalizer (H : Set G) ≤ normalizer (H ⊓ L : Subgroup G) := by
    rw [inf_comm (H : Subgroup G) L]
    exact (le_inf (inf_le_left.trans le_normalizer) inf_le_right).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hKN : ((L ⊓ normalizer (H : Set G)).subgroupOf X) ≤
      normalizer (((H ⊓ L).subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hHX]
    exact Subgroup.subgroupOf_mono X hKNG
  have hHK : H ⊓ L ≤ L ⊓ normalizer (H : Set G) :=
    le_inf inf_le_right (inf_le_left.trans Subgroup.le_normalizer)
  have hpG : 2 ∣ (H ⊓ L).relIndex (L ⊓ normalizer (H : Set G)) :=
    IsPIsolatedOver.dvd_relIndex hiso hH.to_inf_left hHK hKNG
  have hp : 2 ∣ ((H ⊓ L).subgroupOf X).relIndex ((L ⊓ normalizer (H : Set G)).subgroupOf X) :=
    (Subgroup.relIndex_subgroupOf hKX).symm ▸ hpG
  have hY : (((L ⊓ normalizer (H : Set G)).subgroupOf X).subgroupOf
      ((L ⊓ normalizer (H : Set G)).subgroupOf X)).IsSubnormal := by
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.IsSubnormal.top
  have hkerC := coprime_card_ker_subgroupOf_normalizer hker hL
  have hcent := subgroupOf_inf_ker_le_centralizer (H := H) hker
  have hHY : ((H ⊓ L).subgroupOf X) ≤ ((L ⊓ normalizer (H : Set G)).subgroupOf X) :=
    Subgroup.subgroupOf_mono X hHK
  exact IsPIsolatedOver.map_of_coprime_ker (φ := ψ) hkerC hisoX hH2 hKN hHY le_rfl hY hp hcent

private lemma gomiChev_inf_normalizer_map [Finite G] {S : Subgroup G}
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (L ⊓ centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)))
    (hL : IsGomiChevTwo ↥L) (hS : IsPGroup 2 S) (hSX : S ≤ normalizer (L : Set G)) :
    (L.subgroupOf (normalizer (L : Set G))).map ψ ⊓
        normalizer (((S.subgroupOf (normalizer (L : Set G))).map ψ : Subgroup Γ) : Set Γ) =
      ((L ⊓ normalizer (S : Set G)).subgroupOf (normalizer (L : Set G))).map ψ :=
  inf_normalizer_map_subgroupOf (D := L ⊓ centralizer (L : Set G)) (L := L) (S := S) hψ hker
    (inf_le_left.trans le_normalizer) le_normalizer inf_le_left hSX hS
    (IsGomiChevTwo.not_two_dvd_relIndex_inf_centralizer (L := L) hL S)

private lemma map_subgroupOf_le_normalizer_map {R S : Subgroup G}
    (hRX : R ≤ normalizer (L : Set G)) (hSR : S ≤ normalizer (R : Set G)) :
    (S.subgroupOf (normalizer (L : Set G))).map ψ ≤
      normalizer (((R.subgroupOf (normalizer (L : Set G))).map ψ : Subgroup Γ) : Set Γ) := by
  refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map ψ)
  rw [← Subgroup.subgroupOf_normalizer_eq hRX]
  exact Subgroup.subgroupOf_mono _ hSR

private lemma gomiChev_pCore_map [Finite G] {H : Subgroup G}
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (L ⊓ centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)))
    (hL : IsGomiChevTwo ↥L)
    (hcore : pCoreOf 2 (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) = H ⊓ L) :
    pCoreOf 2 (((L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)).subgroupOf
        (normalizer (L : Set G))).map ψ) =
      ((H ⊓ L).subgroupOf (normalizer (L : Set G))).map ψ := by
  rw [pCoreOf_map_subgroupOf_of_le_centralizer (D := L ⊓ centralizer (L : Set G))
    (K := L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) hψ hker
    (inf_le_left.trans le_normalizer) (inf_le_left.trans le_normalizer)
    (inf_centralizer_le_centralizer inf_le_left) (coprime_card_inf_centralizer hL), hcore]

private lemma gomiChevAtom_map [Finite G] {U A : Subgroup G}
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (L ⊓ centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)))
    (hL : IsGomiChevTwo ↥L) (hU : IsPGroup 2 U) (hUX : U ≤ normalizer (L : Set G))
    (hAX : A ≤ normalizer (L : Set G))
    (hDB : L ⊓ centralizer (L : Set G) ≤ L ⊓ normalizer (U : Set G))
    (hDA : L ⊓ centralizer (L : Set G) ≤ A) :
    IsGomiAtom ((L.subgroupOf (normalizer (L : Set G))).map ψ)
        ((U.subgroupOf (normalizer (L : Set G))).map ψ)
        ((A.subgroupOf (normalizer (L : Set G))).map ψ) ↔ IsGomiAtom L U A :=
  isGomiAtom_map_subgroupOf_iff (D := L ⊓ centralizer (L : Set G)) hker le_normalizer hAX hDB hDA
    (gomiChev_inf_normalizer_map hψ hker hL hU hUX)

private lemma gomiChevLevi_atom_lift [Finite G] {U P : Subgroup G}
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (L ⊓ centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)))
    (hL : IsGomiChevTwo ↥L) (hU : IsPGroup 2 U) (hUX : U ≤ normalizer (L : Set G))
    (hPX : P ≤ normalizer (L : Set G))
    (hDB : L ⊓ centralizer (L : Set G) ≤ L ⊓ normalizer (U : Set G))
    (hDP : L ⊓ centralizer (L : Set G) ≤ P)
    (hkey : IsGomiAtom ((L.subgroupOf (normalizer (L : Set G))).map ψ)
        ((U.subgroupOf (normalizer (L : Set G))).map ψ)
        ((P.subgroupOf (normalizer (L : Set G))).map ψ)) : IsGomiAtom L U P :=
  (gomiChevAtom_map hψ hker hL hU hUX hPX hDB hDP).1 hkey

private lemma gomiChevLevi_forall_lift [Finite G] {U H P : Subgroup G}
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (L ⊓ centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)))
    (hL : IsGomiChevTwo ↥L) (hU : IsPGroup 2 U) (hUX : U ≤ normalizer (L : Set G))
    (hPX : P ≤ normalizer (L : Set G))
    (hDB : L ⊓ centralizer (L : Set G) ≤ L ⊓ normalizer (U : Set G))
    (hkey : ∀ A : Subgroup Γ, IsGomiAtom ((L.subgroupOf (normalizer (L : Set G))).map ψ)
        ((U.subgroupOf (normalizer (L : Set G))).map ψ) A →
        A ≤ (P.subgroupOf (normalizer (L : Set G))).map ψ →
        ∃ k ∈ (H.subgroupOf (normalizer (L : Set G))).map ψ,
          A.map (MulAut.conj k).toMonoidHom ≠ A) :
    ∀ A : Subgroup G, IsGomiAtom L U A → A ≤ P →
      ∃ h ∈ H, A.map (MulAut.conj h).toMonoidHom ≠ A := by
  intro A hA hAP
  have hDA : L ⊓ centralizer (L : Set G) ≤ A := hDB.trans hA.1.le
  have hAX : A ≤ normalizer (L : Set G) := hAP.trans hPX
  have hAbar := (gomiChevAtom_map hψ hker hL hU hUX hAX hDB hDA).2 hA
  have hAle : (A.subgroupOf (normalizer (L : Set G))).map ψ ≤
      (P.subgroupOf (normalizer (L : Set G))).map ψ :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono (normalizer (L : Set G)) hAP)
  obtain ⟨k, hkH, hkne⟩ := hkey _ hAbar hAle
  obtain ⟨x, hxH, rfl⟩ := Subgroup.mem_map.mp hkH
  refine ⟨(x : G), Subgroup.mem_subgroupOf.mp hxH, fun hAx => hkne ?_⟩
  have h := map_subgroupOf_map_conj (ψ := ψ) x A
  rw [hAx] at h
  exact h.symm

private lemma gomiChevLevi_hcore_map [Finite G] {H : Subgroup G}
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (L ⊓ centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)))
    (hL : IsGomiChevTwo ↥L) (hH : IsPGroup 2 H)
    (hcore : pCoreOf 2 (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) = H ⊓ L) :
    pCoreOf 2 (gomiMap ψ L ⊓ normalizer ((gomiMap ψ H ⊓ gomiMap ψ L : Subgroup Γ) : Set Γ)) =
      gomiMap ψ H ⊓ gomiMap ψ L := by
  have hHinfL : gomiMap ψ H ⊓ gomiMap ψ L =
      ((H ⊓ L : Subgroup G).subgroupOf (normalizer (L : Set G))).map ψ :=
    (map_subgroupOf_inf (K := H) (K' := L) hker inf_le_left).symm
  rw [hHinfL, gomiChev_inf_normalizer_map (ψ := ψ) hψ hker hL hH.to_inf_left
    (inf_le_right.trans le_normalizer)]
  exact gomiChev_pCore_map (ψ := ψ) hψ hker hL hcore

private lemma gomiChevLevi_hBP_map [Finite G] {H U : Subgroup G}
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (L ⊓ centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)))
    (hL : IsGomiChevTwo ↥L) (hU : IsPGroup 2 U) (hUL : U ≤ L) (hH : IsPGroup 2 H)
    (hBP : L ⊓ normalizer (U : Set G) < L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) :
    gomiMap ψ L ⊓ normalizer ((gomiMap ψ U : Subgroup Γ) : Set Γ) <
      gomiMap ψ L ⊓ normalizer ((gomiMap ψ H ⊓ gomiMap ψ L : Subgroup Γ) : Set Γ) := by
  have hBbar := gomiChev_inf_normalizer_map (ψ := ψ) hψ hker hL hU (hUL.trans le_normalizer)
  have hHinfL : gomiMap ψ H ⊓ gomiMap ψ L =
      ((H ⊓ L : Subgroup G).subgroupOf (normalizer (L : Set G))).map ψ :=
    (map_subgroupOf_inf (K := H) (K' := L) hker inf_le_left).symm
  have hPbar := gomiChev_inf_normalizer_map (ψ := ψ) hψ hker hL hH.to_inf_left
    (inf_le_right.trans le_normalizer)
  rw [hBbar, hHinfL, hPbar]
  exact (map_subgroupOf_lt_map_subgroupOf_iff (D := L ⊓ centralizer (L : Set G))
    (K := L ⊓ normalizer (U : Set G))
    (K' := L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) hker
    (inf_le_left.trans le_normalizer) (inf_le_left.trans le_normalizer)
    (inf_centralizer_le_inf_normalizer hUL)
    (inf_centralizer_le_inf_normalizer inf_le_right)).2 hBP

private lemma gomiChevLevi_hPL_map [Finite G] {H : Subgroup G}
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (L ⊓ centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)))
    (hL : IsGomiChevTwo ↥L) (hH : IsPGroup 2 H)
    (hPL : L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) < L) :
    gomiMap ψ L ⊓ normalizer ((gomiMap ψ H ⊓ gomiMap ψ L : Subgroup Γ) : Set Γ) < gomiMap ψ L := by
  have hHinfL : gomiMap ψ H ⊓ gomiMap ψ L =
      ((H ⊓ L : Subgroup G).subgroupOf (normalizer (L : Set G))).map ψ :=
    (map_subgroupOf_inf (K := H) (K' := L) hker inf_le_left).symm
  have hPbar := gomiChev_inf_normalizer_map (ψ := ψ) hψ hker hL hH.to_inf_left
    (inf_le_right.trans le_normalizer)
  rw [hHinfL, hPbar]
  exact (map_subgroupOf_lt_map_subgroupOf_iff (D := L ⊓ centralizer (L : Set G))
    (K := L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) (K' := L) hker
    (inf_le_left.trans le_normalizer) le_normalizer
    (inf_centralizer_le_inf_normalizer inf_le_right) inf_le_left).2 hPL

private lemma gomiChevLevi_hiso_map [Finite G] [Finite Γ] {H : Subgroup G}
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (L ⊓ centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)))
    (hL : IsGomiChevTwo ↥L) (hH : IsPGroup 2 H) (hHL : H ≤ normalizer (L : Set G))
    (hiso : IsPIsolatedOver 2 (L ⊓ normalizer (H : Set G)) (H ⊓ L)) :
    IsPIsolatedOver 2 (gomiMap ψ L ⊓ normalizer ((gomiMap ψ H : Subgroup Γ) : Set Γ))
      (gomiMap ψ H ⊓ gomiMap ψ L) := by
  have hHbarN := gomiChev_inf_normalizer_map (ψ := ψ) hψ hker hL hH hHL
  have hHinfL : gomiMap ψ H ⊓ gomiMap ψ L =
      ((H ⊓ L : Subgroup G).subgroupOf (normalizer (L : Set G))).map ψ :=
    (map_subgroupOf_inf (K := H) (K' := L) hker inf_le_left).symm
  rw [hHbarN, hHinfL]
  exact IsPIsolatedOver.map_subgroupOf_normalizer (ψ := ψ) hker hL hH hHL hiso

private lemma gomiChevLevi_instance (h : GomiChevLeviCenterless)
    {L U H : Subgroup G} [Finite G] (hL : IsGomiChevTwo ↥L)
    (hU : IsSylowOf 2 U L) (hH : IsPGroup 2 H)
    (hHL : H ≤ normalizer (L : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hBP : L ⊓ normalizer (U : Set G) < L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G))
    (hPL : L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) < L)
    (hcore : pCoreOf 2 (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) = H ⊓ L)
    (hiso : IsPIsolatedOver 2 (L ⊓ normalizer (H : Set G)) (H ⊓ L)) :
    IsGomiAtom L U (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) ∨
      ∀ A : Subgroup G, IsGomiAtom L U A →
        A ≤ L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) →
        ∃ h ∈ H, A.map (MulAut.conj h).toMonoidHom ≠ A := by
  let X : Subgroup G := normalizer (L : Set G)
  let Z : Subgroup G := L ⊓ centralizer (L : Set G)
  let Γq := ↥X ⧸ (L.subgroupOf X ⊓ ((centralizer (L : Set G)).subgroupOf X))
  let ψq : ↥X →* Γq := QuotientGroup.mk' _
  have hψq : Function.Surjective ψq :=
    QuotientGroup.mk'_surjective (L.subgroupOf X ⊓ ((centralizer (L : Set G)).subgroupOf X))
  have hker : ψq.ker = Z.subgroupOf X := by
    rw [QuotientGroup.ker_mk']
    exact (Subgroup.comap_inf L (centralizer (L : Set G)) X.subtype).symm
  have hLX : L ≤ X := le_normalizer
  have hUX : U ≤ X := hU.le.trans le_normalizer
  have hPX : L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) ≤ X := inf_le_left.trans hLX
  have hZL : Z ≤ L := inf_le_left
  have hLB : Z ≤ L ⊓ normalizer (U : Set G) := inf_centralizer_le_inf_normalizer hU.le
  have hZP : Z ≤ L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) :=
    inf_centralizer_le_inf_normalizer inf_le_right
  obtain ⟨hLb, hZb⟩ := IsGomiChevTwo.map_subgroupOf_normalizer (ψ := ψq) hker hL
  have hSylow : IsSylowOf 2 ((U.subgroupOf X).map ψq) ((L.subgroupOf X).map ψq) :=
    isSylowOf_map_subgroupOf hLX hU
  have hHbar : IsPGroup 2 ((H.subgroupOf X).map ψq) :=
    IsPGroup.map (hH.of_equiv (Subgroup.subgroupOfEquivOfLe hHL).symm) ψq
  have hHnormL := map_subgroupOf_le_normalizer_map (ψ := ψq) (R := L) (S := H) hLX hHL
  have hHnormU := map_subgroupOf_le_normalizer_map (ψ := ψq) (R := U) (S := H) hUX hHU
  have hPbar := gomiChev_inf_normalizer_map (ψ := ψq) hψq hker hL hH.to_inf_left
    (inf_le_right.trans hLX)
  have hHinfLbar : (H.subgroupOf X).map ψq ⊓ (L.subgroupOf X).map ψq =
      ((H ⊓ L : Subgroup G).subgroupOf X).map ψq :=
    (map_subgroupOf_inf (K := H) (K' := L) hker hZL).symm
  have hcore' := gomiChevLevi_hcore_map (L := L) (ψ := ψq) hψq hker hL hH hcore
  have hBP' := gomiChevLevi_hBP_map (L := L) (ψ := ψq) hψq hker hL hU.isPGroup hU.le hH hBP
  have hPL' := gomiChevLevi_hPL_map (L := L) (ψ := ψq) hψq hker hL hH hPL
  have hiso' := gomiChevLevi_hiso_map (L := L) (ψ := ψq) hψq hker hL hH hHL hiso
  have key := h Γq ((L.subgroupOf X).map ψq) ((U.subgroupOf X).map ψq) ((H.subgroupOf X).map ψq)
    hLb hZb hSylow hHbar hHnormL hHnormU hBP' hPL' hcore' hiso'
  rw [hHinfLbar, hPbar] at key
  rcases key with hkey | hkey
  · exact Or.inl (gomiChevLevi_atom_lift (ψ := ψq) hψq hker hL hU.isPGroup hUX hPX hLB hZP hkey)
  · exact Or.inr (gomiChevLevi_forall_lift (ψ := ψq) hψq hker hL hU.isPGroup hUX hPX hLB hkey)

private lemma gomiChevLevi_of_centerless (h : GomiChevLeviCenterless) : GomiChevLevi :=
  fun _ _ _ _ _ _ hL hU hH hHL hHU hBP hPL hcore hiso =>
    gomiChevLevi_instance h hL hU hH hHL hHU hBP hPL hcore hiso

theorem gomiChevLevi_of_center_eq_bot
    (h : ∀ (G : Type) [Group G] [Finite G] (L U H : Subgroup G), IsGomiChevTwo ↥L →
      center ↥L = ⊥ → IsSylowOf 2 U L → IsPGroup 2 H → H ≤ normalizer (L : Set G) →
      H ≤ normalizer (U : Set G) →
      L ⊓ normalizer (U : Set G) < L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) →
      L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) < L →
      pCoreOf 2 (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) = H ⊓ L →
      IsPIsolatedOver 2 (L ⊓ normalizer (H : Set G)) (H ⊓ L) →
      IsGomiAtom L U (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) ∨
        ∀ A : Subgroup G, IsGomiAtom L U A →
          A ≤ L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) →
          ∃ h ∈ H, A.map (MulAut.conj h).toMonoidHom ≠ A) :
    GomiChevLevi :=
  gomiChevLevi_of_centerless h

end CFSG.GroupTheory
