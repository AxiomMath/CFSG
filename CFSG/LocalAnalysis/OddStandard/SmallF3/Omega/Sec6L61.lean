module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6ShapesDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Helpers
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PocketLemmas
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ChainDiag
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem mem_normalizer_of_conjugate_eq {L : Subgroup G} {s : G}
    (h : CFSG.conjugate L s = L) : s ∈ normalizer (L : Set G) := by
  have h2 : s⁻¹ ∈ normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact h
  simpa using (Subgroup.inv_mem (normalizer (L : Set G)) h2)

private theorem inF_of_ctrQ_dvd_of_inFStar [Finite G] {K : Subgroup G} (hK : InFStar K)
    (hq : IsQuasisimple K) (hdvd : 25920 ∣ ctrQ K) : InF K := by
  rcases ctrQ_cases_of_inFStar hK with
    ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ |
      ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩
  · exact ⟨hq, Or.inl (Or.inl h)⟩
  · exact ⟨hq, Or.inl (Or.inr (Or.inl h))⟩
  · rcases h with h | h
    · exact ⟨hq, Or.inl (Or.inr (Or.inr (Or.inl h)))⟩
    · exact ⟨hq, Or.inr h⟩
  · exact ⟨hq, Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
  · exact ⟨hq, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))⟩
  · exact ⟨hq, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))⟩
  · rw [hc] at hdvd
    exact absurd hdvd (by decide +kernel)
  · rw [hc] at hdvd
    exact absurd hdvd (by decide +kernel)
  · rw [hc] at hdvd
    exact absurd hdvd (by decide +kernel)
  · rw [hc] at hdvd
    exact absurd hdvd (by decide +kernel)

theorem asc82Lemma61_of (hsh : Asc82Shapes) (h36 : Asc82Lemma36) (h37 : Asc82Lemma37)
    (hP : Asc82Tab6P) (hM : Asc82Tab6M) (hF : Asc82AutFacts) : Asc82Lemma61 := by
  intro G _ _ t L hS hL6 x hx2 hxt hX5
  let X : Subgroup G := layerCent L x
  have hLP : IsOm6P L := ⟨hS.component.isQuasisimple, hL6⟩
  have hnorm : ∀ c ∈ centralizer ({t} : Set G), CFSG.conjugate L c = L :=
    conjugate_eq_self_of_lemma36 h36 hS
  have hxN : x ∈ normalizer (L : Set G) := mem_normalizer_of_conjugate_eq (hnorm x hxt)
  have hXL : IsComponentIn X (L ⊓ centralizer ({x} : Set G)) :=
    isComponentIn_layerCent (L := L) (s := x) (Or.inl hX5)
  have hXc : IsComponentIn X (centralizer ({t, x} : Set G)) := by
    rw [centralizer_pair_eq_inf t x]
    exact IsComponentIn.of_normal_inf_centralizer hS.component.le hnorm hXL
  have hcomm : t * x = x * t := (Subgroup.mem_centralizer_singleton_iff.mp hxt).symm
  have htCx : t ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hXF : InF X := ⟨hXc.isQuasisimple, Or.inl (Or.inl hX5)⟩
  have hXstar : InFStar X := inFStar_of_inF hXF
  obtain ⟨K, hK, hXle⟩ := hS.lBalance t x hS.involution hx2 hcomm X hXc
  have hKstar : InFStar K := hS.a2 t x hS.involution hx2 hcomm X K hXc hK hXle hXstar
  have hmain : ∃ I : Subgroup G, IsComponentIn I (centralizer ({x} : Set G)) ∧ X ≤ I ∧ InF I := by
    have hK' : IsComponentIn (CFSG.conjugate K t) (centralizer ({x} : Set G)) := hK.conjugate htCx
    have hK'F : InFStar (CFSG.conjugate K t) := hKstar.conjugate t
    by_cases hKeq : CFSG.conjugate K t = K
    · have hXK : X ≤ K := by
        have h := hXle
        rw [hKeq, sup_idem] at h
        exact h
      exact ⟨K, hK, hXK, inF_of_le_of_inFStar hXK hXF hKstar⟩
    · have hne : CFSG.conjugate K t ≠ K := hKeq
      have hcommKK' : ∀ a ∈ K, ∀ b ∈ CFSG.conjugate K t, a * b = b * a :=
        hK.commute_of_ne hK' (Ne.symm hne)
      rcases ctrQ_dvd_of_le_sup_of_commute hXc.isQuasisimple hcommKK' hXle with hXK' | ⟨hdvd, _⟩
      · exact ⟨CFSG.conjugate K t, hK', hXK', inF_of_le_of_inFStar hXK' hXF hK'F⟩
      · exfalso
        have hXq : ctrQ X = 25920 := ctrQ_of_psp4 hXc.isQuasisimple hX5
        have hKF : InF K := inF_of_ctrQ_dvd_of_inFStar hKstar hK.isQuasisimple (by
          rw [← hXq]; exact hdvd)
        exact hne ((h36 G t L hS x K hx2 hK (Or.inl hKF)).2 (CFSG.conjugate K t) hK' hK'F)
  obtain ⟨I, hI, hXI, hIF⟩ := hmain
  have hshI := hsh G x I (sec3SettingLB_of_component hS hx2 hI hIF)
  rcases hshI with hI5 | hI6p | hI6m
  · exact ⟨I, hI, hXI, Or.inl hI5⟩
  · exact ⟨I, hI, hXI, Or.inr hI6p⟩
  · exfalso
    have hα : ∃ α : ℤˣ, InducesTypeSome L x 6 1 1 α :=
      (hP.layer_om5_iff G L hLP x hx2 hxN).mp hX5
    obtain ⟨⟨z, hzX, hz4plus⟩, u, huX, hu2, hutype⟩ := hF.omega5_sub G L hLP x hx2 hxN hα
    have hIM : IsOm6M I := ⟨hI.isQuasisimple, hI6m⟩
    have hz2 : orderOf z = 2 := hz4plus.1
    have hzI : z ∈ I := hXI hzX
    have huI : u ∈ I := hXI huX
    have hconj : u ∈ conjClassIn I z := hM.inv_one_class G I hIM z u hzI huI hz2 hu2
    obtain ⟨h, _, hhu⟩ := hconj
    have hg : (h⁻¹)⁻¹ * z * h⁻¹ = u := by
      rw [inv_inv]
      exact hhu.symm
    have hlayerL : layerCent L x ≤ L :=
      (Subgroup.map_subtype_le (CFSG.layer ↥(L ⊓ centralizer ({x} : Set G)))).trans inf_le_left
    have huL : u ∈ L := hlayerL huX
    have huCt : u ∈ centralizer ({t} : Set G) := hS.component.le huL
    have hmem : (h⁻¹)⁻¹ * z * h⁻¹ ∈ centralizer ({t} : Set G) := hg ▸ huCt
    have hlayer_bot : CFSG.inSubgroup CFSG.layer
        (L ⊓ centralizer ({(h⁻¹)⁻¹ * z * h⁻¹} : Set G)) = ⊥ :=
      h37 G t L hS z h⁻¹ hz4plus hmem
    have hlayerU : layerCent L u = ⊥ := by
      unfold layerCent
      rw [← hg]
      exact hlayer_bot
    have huN : u ∈ normalizer (L : Set G) := Subgroup.le_normalizer huL
    have hL29bot : IsL29 (layerCent L u) := hP.layer_i2 G L hLP u hu2 huN hutype
    have hbot : IsL29 (⊥ : Subgroup G) := hlayerU ▸ hL29bot
    unfold IsL29 at hbot
    have hmodel := hbot.statedClassicalModel_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)
    have h360 : Nat.card (↥(⊥ : Subgroup G) ⧸ oddCore ↥(⊥ : Subgroup G)) = 360 := by
      rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two
        (show (3 : ℕ) ≠ 2 by norm_num) hmodel).1 rfl]
      decide +kernel
    haveI : Subsingleton ↥(⊥ : Subgroup G) :=
      ⟨fun a b => Subtype.ext (by rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
    have h1 : Nat.card (↥(⊥ : Subgroup G) ⧸ oddCore ↥(⊥ : Subgroup G)) ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr inferInstance
    omega

end CFSG.OddStandard.SmallF3.Omega
