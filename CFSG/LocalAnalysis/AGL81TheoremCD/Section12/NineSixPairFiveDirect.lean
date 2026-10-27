module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6KProd
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.RankThree.PartOne.S11c.OuterInner
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N5GammaGroup
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Two
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenTwoOneHolds
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComm

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

private lemma inf_eq_bot_of_commute_of_faithful {X : Type} [Group X]
    {L I E : Subgroup X} (hc : ∀ a ∈ L, ∀ b ∈ I, a * b = b * a)
    (hfaith : ∀ e ∈ E, e ≠ 1 → ¬ I ≤ Subgroup.centralizer ({e} : Set X)) :
    E ⊓ L = ⊥ := by
  rw [eq_bot_iff]
  rintro e ⟨heE, heL⟩
  rw [Subgroup.mem_bot]
  by_contra he1
  exact hfaith e heE he1 fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hc e heL y hy).symm

private lemma false_of_isElemAbelian_card_pow_four {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hrank : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3) {B : Subgroup X}
    (hB : CFSG.Open.IsElemAbelian p B) (hcard : Nat.card B = p ^ 4) : False := by
  have h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) :=
    CFSG.SectionRank.le_pRank hp.one_lt (E := B) le_top hB (k := 4) hcard
  omega

private lemma pow_inv_mul_of_inner {X : Type} [Group X] {L I : Subgroup X} {p : ℕ} {e k : X}
    (hkL : k ∈ L) (hkp : k ^ p = 1) (hep : e ^ p = 1)
    (hconj : ∀ y ∈ L, e * y * e⁻¹ = k * y * k⁻¹) (heU : e ∉ L ⊔ I) :
    (k⁻¹ * e) ^ p = 1 ∧ k⁻¹ * e ≠ 1 ∧ (∀ y ∈ L, (k⁻¹ * e) * y * (k⁻¹ * e)⁻¹ = y) ∧
      k⁻¹ * e ∉ L ⊔ I := by
  have hek : e * k = k * e := by
    have h : e * k * e⁻¹ = k := by
      have := hconj k hkL
      rwa [show k * k * k⁻¹ = k from by group] at this
    calc e * k = (e * k * e⁻¹) * e := by group
      _ = k * e := by rw [h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hcomm : Commute k e := hek.symm
    rw [hcomm.inv_left.mul_pow, inv_pow, hkp, hep, inv_one, one_mul]
  · intro hf
    apply heU
    have hek' : e = k := by
      have := congrArg (fun x => k * x) hf
      simpa [mul_assoc] using this
    rw [hek']
    exact Subgroup.mem_sup_left hkL
  · intro y hy
    have h := hconj y hy
    calc (k⁻¹ * e) * y * (k⁻¹ * e)⁻¹
        = k⁻¹ * (e * y * e⁻¹) * k := by group
      _ = k⁻¹ * (k * y * k⁻¹) * k := by rw [h]
      _ = y := by group
  · intro hf
    apply heU
    have he : e = k * (k⁻¹ * e) := by group
    rw [he]
    exact mul_mem (Subgroup.mem_sup_left hkL) hf

private lemma false_of_le_sup {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {L I E : Subgroup X}
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3)
    (hc : ∀ a ∈ L, ∀ b ∈ I, a * b = b * a) (hdirect : L ⊓ I = ⊥)
    (hEsup : E ≤ L ⊔ I) (hE : CFSG.Open.IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hfaith : ∀ e ∈ E, e ≠ 1 → ¬ I ≤ Subgroup.centralizer ({e} : Set X))
    (hL2 : 2 ≤ CFSG.Open.pRank p L) : False := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨AL, hALleL, hALel, hALcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := p) (k := 2) hL2
  have hEinfL : E ⊓ L = ⊥ := inf_eq_bot_of_commute_of_faithful hc hfaith
  let φ : ↥E →* ↥I :=
    (KProd.projB L I hc hdirect).comp (Subgroup.inclusion hEsup)
  have hφker : MonoidHom.ker φ = ⊥ := by
    rw [eq_bot_iff]
    rintro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    have hx' : (KProd.projB L I hc hdirect) (Subgroup.inclusion hEsup x) = 1 := hx
    have hxL : (x : X) ∈ L := by
      have h := (KProd.projB_eq_one_iff L I hc hdirect
        (Subgroup.inclusion hEsup x)).mp hx'
      simpa using h
    exact Subtype.ext (Subgroup.mem_bot.mp (by
      have hmem : (x : X) ∈ E ⊓ L := ⟨x.2, hxL⟩
      rwa [hEinfL] at hmem))
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hφker
  have hEtop : CFSG.Open.IsElemAbelian p (⊤ : Subgroup ↥E) := by
    have h := CFSG.Open.IsElemAbelian.comap hE (f := E.subtype) E.subtype_injective
    have htop : E.comap E.subtype = (⊤ : Subgroup ↥E) := by ext x; simp
    rwa [htop] at h
  let Fsub : Subgroup ↥I := (⊤ : Subgroup ↥E).map φ
  have hFsubel : CFSG.Open.IsElemAbelian p Fsub := hEtop.map φ
  let F : Subgroup X := Fsub.map I.subtype
  have hFel : CFSG.Open.IsElemAbelian p F := hFsubel.map I.subtype
  have hFI : F ≤ I := Subgroup.map_subtype_le Fsub
  have hFcardE : Nat.card F = Nat.card E := by
    have h1 : Nat.card F = Nat.card Fsub := by
      have := Subgroup.card_map_of_injective (K := Fsub) (f := I.subtype) I.subtype_injective
      simpa [F] using this
    have h2 : Nat.card Fsub = Nat.card ↥E := by
      have := Subgroup.card_map_of_injective (K := (⊤ : Subgroup ↥E)) (f := φ) hφinj
      simpa [Fsub, Subgroup.card_top] using this
    rw [h1, h2]
  have hFcard : Nat.card F = p ^ 2 := by
    rw [hFcardE, hEcard]
  have hcommALF : ∀ a ∈ AL, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    hc a (hALleL ha) b (hFI hb)
  have hALinfF : AL ⊓ F = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxAL, hxF⟩
    rw [Subgroup.mem_bot]
    have hmem : x ∈ L ⊓ I := ⟨hALleL hxAL, hFI hxF⟩
    rw [hdirect] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hsupel : CFSG.Open.IsElemAbelian p (AL ⊔ F) := hALel.sup_of_commute hFel hcommALF
  have hsupcard : Nat.card ↥(AL ⊔ F) = Nat.card AL * Nat.card F :=
    (Nat.card_congr (KProd.prodEquivSup AL F hcommALF hALinfF).toEquiv).symm.trans
      (Nat.card_prod _ _)
  have hcardp4 : Nat.card ↥(AL ⊔ F) = p ^ 4 := by
    rw [hsupcard, hALcard, hFcard]
    ring
  exact false_of_isElemAbelian_card_pow_four hp hrank hsupel hcardp4

private lemma false_of_not_le_sup {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {L I E : Subgroup X}
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3)
    (hc : ∀ a ∈ L, ∀ b ∈ I, a * b = b * a) (hdirect : L ⊓ I = ⊥)
    (hpI : p ∣ Nat.card I) (hE : CFSG.Open.IsElemAbelian p E)
    (hEI : E ≤ Subgroup.normalizer (I : Set X))
    (hinner : ∀ e ∈ E, ∃ k ∈ L, k ^ p = 1 ∧ ∀ y ∈ L, e * y * e⁻¹ = k * y * k⁻¹)
    (hEnot : ¬ E ≤ L ⊔ I) (hL2 : 2 ≤ CFSG.Open.pRank p L) : False := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨AL, hALleL, hALel, hALcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := p) (k := 2) hL2
  have hEnot' : ¬ (E : Set X) ⊆ ((L ⊔ I : Subgroup X) : Set X) :=
    fun h => hEnot (SetLike.coe_subset_coe.mp h)
  obtain ⟨e, heE, heU⟩ := Set.not_subset.mp hEnot'
  obtain ⟨k, hkL, hkp, hconj⟩ := hinner e heE
  have hep : e ^ p = 1 := hE.2 e heE
  obtain ⟨hfp, hf1, hfL, hfU⟩ :=
    pow_inv_mul_of_inner (I := I) hkL hkp hep hconj (by simpa using heU)
  set f : X := k⁻¹ * e with hfdef
  have hford : orderOf f = p := orderOf_eq_prime hfp hf1
  obtain ⟨c, hcI, hcord, hccent⟩ :=
    CFSG.Quasithin.exists_orderOf_eq_of_isPGroup_normalizer (p := p)
      (P := E) (H := I) hE.isPGroup hEI hpI
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hcord
    exact hp.one_lt.ne' hcord.symm
  have hce : e * c = c * e := (Subgroup.mem_centralizer_iff.mp hccent) e heE
  have hck : k * c = c * k := hc k hkL c hcI
  have hcf : Commute c f := by
    rw [hfdef]
    exact (Commute.inv_right (show Commute c k from hck.symm)).mul_right
      (show Commute c e from hce.symm)
  have hcnotinAL : c ∉ AL := by
    intro hcAL
    have hmem : c ∈ L ⊓ I := ⟨hALleL hcAL, hcI⟩
    rw [hdirect] at hmem
    exact hc1 (Subgroup.mem_bot.mp hmem)
  have hALc : ∀ a ∈ AL, Commute a c := fun a ha => hc a (hALleL ha) c hcI
  obtain ⟨hB1el, hB1card⟩ :=
    CFSG.Quasithin.exists_elemAbelian_sup_zpowers (p := p) hALel hcord hALc hcnotinAL
  have hB1leU : AL ⊔ Subgroup.zpowers c ≤ L ⊔ I :=
    sup_le (hALleL.trans le_sup_left) (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right hcI))
  have hfB1 : f ∉ AL ⊔ Subgroup.zpowers c := fun h => hfU (hB1leU h)
  have hALcent : AL ≤ Subgroup.centralizer ({f} : Set X) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [hfdef] at hfL ⊢
    have h := hfL a (hALleL ha)
    have hfa : (k⁻¹ * e) * a = a * (k⁻¹ * e) := by
      calc (k⁻¹ * e) * a = ((k⁻¹ * e) * a * (k⁻¹ * e)⁻¹) * (k⁻¹ * e) := by group
        _ = a * (k⁻¹ * e) := by rw [h]
    exact hfa.symm
  have hzpcent : Subgroup.zpowers c ≤ Subgroup.centralizer ({f} : Set X) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hcf
  have hB1cent : AL ⊔ Subgroup.zpowers c ≤ Subgroup.centralizer ({f} : Set X) :=
    sup_le hALcent hzpcent
  have hcommB1f : ∀ b ∈ AL ⊔ Subgroup.zpowers c, Commute b f := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mp (hB1cent hb)
  obtain ⟨hB2el, hB2card⟩ :=
    CFSG.Quasithin.exists_elemAbelian_sup_zpowers (p := p) hB1el hford hcommB1f hfB1
  have hcardp4 : Nat.card ↥((AL ⊔ Subgroup.zpowers c) ⊔ Subgroup.zpowers f) = p ^ 4 := by
    rw [hB2card, hB1card, hALcard]
    ring
  exact false_of_isElemAbelian_card_pow_four hp hrank hB2el hcardp4

theorem pRank_add_one_le_of_ne_prime {X : Type} [Group X] [Finite X] (hK : CFSG.Open.IsKGroup X)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hO : CFSG.pPrimeCore p X = ⊥) {L I : Subgroup X}
    (hL : CFSG.IsComponent L) (hI : CFSG.IsComponent I) (hLI : L ≠ I) :
    CFSG.Open.pRank p I + 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨A, hAI, hA, hAc⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
      (p := p) (k := CFSG.Open.pRank p I) le_rfl
  have hIL : I ≤ Subgroup.centralizer (L : Set X) := by
    rcases CFSG.LocalCores.distinct_components_commute hI hL with hEq | hcomm
    · exact absurd hEq.symm hLI
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  obtain ⟨e, he, hord, c, hc, hnc⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.kFactOmegaNotCentral_holds X hK L hL p hp hp2
      (CFSG.LocalAnalysis.RankThreeTheoremC.thc_dvd_card hp hO hL)
  have h :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.add_one_le_pRank_of_le_centralizer hp hA hAc
      (hAI.trans hIL) he hord ⟨c, hc, hnc⟩
  rwa [CFSG.SectionRank.pRank_coe_eq_openPRank p (⊤ : Subgroup X)] at h

theorem false_of_inner_direct_of_prime {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3)
    {L I E : Subgroup X} (hL : CFSG.IsComponent L) (hI : CFSG.IsComponent I) (hLI : L ≠ I)
    (hdirect : L ⊓ I = ⊥) (hpI : p ∣ Nat.card I) (hL2 : 2 ≤ CFSG.Open.pRank p L)
    (hE : CFSG.Open.IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hEI : E ≤ Subgroup.normalizer (I : Set X))
    (hfaithI : ∀ e ∈ E, e ≠ 1 → ¬ I ≤ Subgroup.centralizer ({e} : Set X))
    (hinner : ∀ e ∈ E, ∃ k ∈ L, k ^ p = 1 ∧ ∀ y ∈ L, e * y * e⁻¹ = k * y * k⁻¹) : False := by
  have hc : ∀ a ∈ L, ∀ b ∈ I, a * b = b * a := by
    have hbot : ⁅L, I⁆ = ⊥ := by
      rcases CFSG.LocalCores.distinct_components_commute hL hI with h | h
      · exact absurd h hLI
      · exact h
    have hle : L ≤ Subgroup.centralizer (I : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm
  by_cases hcase : E ≤ L ⊔ I
  · exact false_of_le_sup hp hrank hc hdirect hcase hE hEcard hfaithI hL2
  · exact false_of_not_le_sup hp hrank hc hdirect hpI hE hEI hinner hcase hL2

private lemma inf_eq_bot_of_ne_of_center_eq_bot {X : Type} [Group X] [Finite X]
    {C C' : Subgroup X} (hC : CFSG.IsComponent C) (hC' : CFSG.IsComponent C') (hCC' : C ≠ C')
    (hZ : Subgroup.center ↥C = ⊥) : C ⊓ C' = ⊥ := by
  have hbot : ⁅C, C'⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hC hC').resolve_left hCC'
  have hcentC : C' ≤ Subgroup.centralizer (C : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rwa [Subgroup.commutator_comm] at hbot)
  rw [eq_bot_iff]
  rintro x ⟨hxC, hxC'⟩
  have hx : (⟨x, hxC⟩ : ↥C) ∈ Subgroup.center ↥C := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcentC hxC') (g : X) g.2)
  rw [hZ, Subgroup.mem_bot] at hx
  simpa using congrArg Subtype.val hx

private lemma exists_conj_of_inner_action {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {C E : Subgroup X} (hE : CFSG.Open.IsElemAbelian p E)
    (hEC : E ≤ Subgroup.normalizer (C : Set X)) (hZ : Subgroup.center ↥C = ⊥)
    (hout : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥C)) :
    ∀ e ∈ E, ∃ k ∈ C, k ^ p = 1 ∧ ∀ y ∈ C, e * y * e⁻¹ = k * y * k⁻¹ := by
  let ρ : ↥E →* MulAut ↥C := C.normalizerMonoidHom.comp (Subgroup.inclusion hEC)
  have hρ_apply : ∀ (e : ↥E) (y : ↥C),
      ((ρ e y : ↥C) : X) = (e : X) * (y : X) * (e : X)⁻¹ := fun e y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe C ⟨(e : X), hEC e.2⟩ y
  have hρp : ∀ e : ↥E, (ρ e) ^ p = 1 := by
    intro e
    rw [← map_pow, show e ^ p = 1 from Subtype.ext (hE.2 (e : X) e.2), map_one]
  intro e he
  obtain ⟨b, hb⟩ :=
    CFSG.RankThree.PartOne.exists_inner_of_pow_eq_one_of_not_dvd_card_outer hp hout
      (ρ ⟨e, he⟩) (hρp ⟨e, he⟩)
  refine ⟨(b : X), b.2, ?_, ?_⟩
  · have hconj : MulAut.conj (b ^ p) = 1 := by
      rw [map_pow, hb]
      exact hρp ⟨e, he⟩
    have hbcenter : b ^ p ∈ Subgroup.center ↥C := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : (MulAut.conj (b ^ p)) g = g := by
        rw [hconj]
        rfl
      rw [MulAut.conj_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    have hbp : b ^ p = 1 := by
      have h := hbcenter
      rw [hZ, Subgroup.mem_bot] at h
      exact h
    simpa using congrArg (fun z : ↥C => (z : X)) hbp
  · intro y hy
    have h1 : ρ ⟨e, he⟩ ⟨y, hy⟩ = b * ⟨y, hy⟩ * b⁻¹ := by
      rw [← hb]
      rfl
    have h2 : ((ρ ⟨e, he⟩ ⟨y, hy⟩ : ↥C) : X) = (b : X) * y * (b : X)⁻¹ := by
      rw [h1]
      simp
    rw [hρ_apply ⟨e, he⟩ ⟨y, hy⟩] at h2
    exact h2

theorem false_of_pair_of_not_dvd_card_outer {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hrank : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3)
    {C C' E : Subgroup X} (hC : CFSG.IsComponent C) (hC' : CFSG.IsComponent C') (hCC' : C ≠ C')
    (hZ : Subgroup.center ↥C = ⊥) (hpC' : p ∣ Nat.card C')
    (hE : CFSG.Open.IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hEC : E ≤ Subgroup.normalizer (C : Set X))
    (hEC' : E ≤ Subgroup.normalizer (C' : Set X))
    (hfaithC : ∀ e ∈ E, e ≠ 1 → ¬ C ≤ Subgroup.centralizer ({e} : Set X))
    (hfaithC' : ∀ e ∈ E, e ≠ 1 → ¬ C' ≤ Subgroup.centralizer ({e} : Set X))
    (hout : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥C)) :
    False := by
  have hdisj : C ⊓ C' = ⊥ := inf_eq_bot_of_ne_of_center_eq_bot hC hC' hCC' hZ
  have hinner := exists_conj_of_inner_action hp hE hEC hZ hout
  have hZ' : ∀ k ∈ C, (∀ l ∈ C, k * l = l * k) → k = 1 := by
    intro k hk hkl
    have hmem : (⟨k, hk⟩ : ↥C) ∈ Subgroup.center ↥C := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (hkl (l : X) l.2).symm
    rw [hZ, Subgroup.mem_bot] at hmem
    simpa using congrArg Subtype.val hmem
  have hfaith' : ∀ b ∈ E, b ≠ 1 → ¬ ∀ k ∈ C, b * k = k * b := by
    intro b hb hb1 hcentb
    exact hfaithC b hb hb1 fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcentb k hk).symm
  have hinner' : ∀ b ∈ E, ∃ k ∈ C, ∀ l ∈ C, b * l * b⁻¹ = k * l * k⁻¹ := by
    intro b hb
    obtain ⟨k, hkC, -, hconj⟩ := hinner b hb
    exact ⟨k, hkC, hconj⟩
  have hL2 : 2 ≤ CFSG.Open.pRank p C :=
    CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.n5_two_le_pRank_of_inner hp hE hEc
      hZ' hfaith' hinner'
  exact false_of_inner_direct_of_prime hp hrank hC hC' hCC' hdisj hpC' hL2 hE hEc hEC'
    hfaithC' hinner

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
