module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.RowData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Lemma36
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Setup
import CFSG.GroupTheory.OddOverlap
public import CFSG.LocalAnalysis.ComponentClassification.TBLitComponents
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35HLambda
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.I32Final

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.QuasithinUnique.Id2519 CFSG.QuasithinUnique.I32
  CFSG.EvenSporadicStandard.Solomon78
open scoped Pointwise

variable {H : Type} [Group H]

theorem SolStd.centralizer_le_normalizer [Finite H] {L : Subgroup H} (h : SolStd L) {t : H}
    (ht : t ∈ centralizer (L : Set H)) (ht2 : orderOf t = 2) :
    centralizer ({t} : Set H) ≤ normalizer (L : Set H) :=
  fun _ hy => CFSG.StandardSubgroupAPI.mem_of_odd_inf_map_conj_of_commute h.1.2 ht ht2
    (mem_centralizer_singleton_iff.1 hy)

theorem cyclic_sylow_all_of_exists [Finite H] {L : Subgroup H}
    (h : ∃ S : Sylow 2 (centralizer (L : Set H)), IsCyclic ↥S) :
    ∀ P : Sylow 2 (centralizer (L : Set H)), IsCyclic ↥P := by
  obtain ⟨S, hS⟩ := h
  intro P
  exact (MulEquiv.isCyclic (Sylow.equiv P S)).mpr hS

theorem FStarSimple.center_eq_bot [Finite H] {N : Subgroup H} (h : FStarSimple N) :
    center H = ⊥ := by
  have hNs := h.isSimpleGroup
  have hz : ∀ z ∈ center H, z = 1 := by
    intro z hz
    have hzN : z ∈ N := h.centralizer_le (mem_centralizer_iff.2 fun n _ =>
      mem_center_iff.1 hz n)
    have hzc : (⟨z, hzN⟩ : ↥N) ∈ center ↥N := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_center_iff.1 hz g)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥N) with h1 | h1
    · rw [h1, mem_bot] at hzc
      exact congrArg Subtype.val hzc
    · exfalso
      obtain ⟨a, b, hab⟩ := h.nonabelian
      exact hab (mem_center_iff.1 (h1 ▸ mem_top b) a)
  ext z
  rw [mem_bot]
  exact ⟨hz z, fun hz1 => hz1 ▸ one_mem _⟩

variable [Finite H]

theorem layer_dichotomy_of_quasisimple_Q
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hZ : center H = ⊥) {t u : H}
    (htH : t ∈ centralizer ({u} : Set H)) (ht2 : orderOf t = 2) (hu2 : orderOf u = 2)
    {B : Subgroup H} (hBu : B ≤ centralizer ({u} : Set H)) (hBt : B ≤ centralizer ({t} : Set H))
    (hq : CFSG.IsQuasisimple ↥B)
    (hn : (B.subgroupOf (centralizer ({u} : Set H) ⊓ centralizer ({t} : Set H))).Normal) :
    (IsTwoComponentIn (⨆ g ∈ oddLayer (centralizer ({u} : Set H)), CFSG.conjugate B g)
        (centralizer ({u} : Set H)) ∧
      t ∈ normalizer ((⨆ g ∈ oddLayer (centralizer ({u} : Set H)),
        CFSG.conjugate B g : Subgroup H) : Set H)) ∨
    ∃ J : Subgroup H, IsTwoComponentIn J (centralizer ({u} : Set H)) ∧
      J ≠ CFSG.conjugate J t ∧
      (⨆ g ∈ oddLayer (centralizer ({u} : Set H)), CFSG.conjugate B g) =
        J ⊔ CFSG.conjugate J t ∧ OddTwoIso J B := by
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    exact absurd hu2 (by decide)
  have hucen : u ∉ center H := by
    intro hz
    rw [hZ, mem_bot] at hz
    exact hu1 hz
  have hK : CFSG.SectionRank.IsKGroupCat ↥(centralizer ({u} : Set H)) :=
    CFSG.ComponentClassification.TBLit.isKGroupCat_centralizer hkp hucen
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    exact absurd ht2 (by decide)
  have ht2' : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  exact lemmaI32 H _ hK t htH ht1 ht2' B
    (isTwoComponentIn_of_quasisimple_normal (le_inf hBu hBt) hq hn)

theorem componentProduct_eq_of_pumpUp_Q {L K : Subgroup H} {t u : H} {b n : ℕ}
    (hbn : b < n) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hZ : center H = ⊥)
    (hB : BTheoremAt u) (hCt : centralizer ({t} : Set H) ≤ normalizer (L : Set H))
    (ht : t ∈ centralizer (L : Set H)) (ht2 : orderOf t = 2)
    (hu : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L) (huK : u ∈ K)
    (hKq : CFSG.IsQuasisimple ↥K) (hKu : K ≤ centralizer ({u} : Set H))
    (hKn : (K.subgroupOf (centralizer ({u} : Set H) ⊓ centralizer ({t} : Set H))).Normal)
    (hO : PumpUpOdd K t u)
    (hΛs : Group.IsSolvable ↥(normalizer (L : Set H) ⊓ centralizer (K : Set H)))
    (hΛr : ∀ E : Subgroup H, E ≤ normalizer (L : Set H) ⊓ centralizer (K : Set H) →
      (∀ x ∈ E, x * x = 1) → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → Nat.card E ≤ b)
    (hrank : InvolutionFixesElem ↥K n) :
    K = componentProduct K u := by
  classical
  set X : Subgroup H := centralizer ({u} : Set H) with hX
  have ht2' : t * t = 1 := by
    rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.1 ht2.dvd
  have htK : t ∈ centralizer (K : Set H) :=
    mem_centralizer_iff.2 fun k hk => mem_centralizer_iff.1 ht k (hKL hk)
  have htH : t ∈ X := mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht u hu).symm
  have hBt : K ≤ centralizer ({t} : Set H) := fun k hk =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht k (hKL hk))
  have hKM : IsCompIn K X := by
    rcases layer_dichotomy_of_quasisimple_Q hkp hZ htH ht2 hu2 (B := K) hKu hBt hKq hKn with
      ⟨hA, -⟩ | ⟨J, hJ, hJne, hJeq, -⟩
    · set M : Subgroup H := ⨆ g ∈ oddLayer X, CFSG.conjugate K g with hMdef
      have hMcomp : IsCompIn M X := hB M hA
      have hKleM : K ≤ M :=
        le_iSup₂_of_le (f := fun g (_ : g ∈ oddLayer X) => CFSG.conjugate K g) 1 (one_mem _)
          (by rw [conjugate_one])
      by_cases hMK : M = K
      · rw [hMK] at hMcomp
        exact hMcomp
      · exfalso
        have hodd := hO M hMcomp (le_sup_of_le_left hKleM) hMK
        exact not_odd_card_center_of_mem (hKleM huK) hu2
          (fun x hx => mem_centralizer_singleton_iff.1 (hMcomp.1 hx)) hodd
    · exfalso
      have hJcomp : IsCompIn J X := hB J hJ
      have htinvH : t⁻¹ ∈ X := X.inv_mem htH
      have hJ'comp : IsCompIn (CFSG.conjugate J t) X := hJcomp.map_conj htinvH
      have hcomm : ∀ a ∈ J, ∀ b ∈ CFSG.conjugate J t, a * b = b * a :=
        hJcomp.commute_of_ne hJ'comp hJne
      have hKJ : K ≤ J ⊔ CFSG.conjugate J t := by
        rw [← hJeq]
        exact le_iSup₂_of_le (f := fun g (_ : g ∈ oddLayer X) => CFSG.conjugate K g) 1 (one_mem _)
          (by rw [conjugate_one])
      have hJK : J ≠ K := by
        intro hJK
        apply hJne
        rw [hJK, conjugate_eq_of_mem_centralizer htK]
      have hodd := hO J hJcomp hKJ hJK
      have hJnorm : J ≤ normalizer (CFSG.conjugate J t : Set H) := fun a ha =>
        Subgroup.centralizer_le_normalizer (CFSG.conjugate J t : Set H)
          (mem_centralizer_iff.2 fun b hb => (hcomm a ha b hb).symm)
      have hu' : u ∈ (J : Set H) * (CFSG.conjugate J t : Set H) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right J (CFSG.conjugate J t) hJnorm]
        exact hKJ huK
      obtain ⟨a, ha, b, hb, hab0⟩ := hu'
      have hab : a * b = u := hab0
      have hJH : J ≤ X := hJcomp.1
      have hJ'X : CFSG.conjugate J t ≤ X := hJ'comp.1
      have hacent : ∀ x ∈ J, x * a = a * x := by
        intro x hx
        have h1 : x * u = u * x := mem_centralizer_singleton_iff.1 (hJH hx)
        rw [← hab] at h1
        have h2 : x * a * b = a * x * b := by
          calc x * a * b = x * (a * b) := by group
            _ = (a * b) * x := h1
            _ = a * (b * x) := by group
            _ = a * (x * b) := by rw [← hcomm x hx b hb]
            _ = a * x * b := by group
        exact mul_right_cancel h2
      have hbcent : ∀ x ∈ CFSG.conjugate J t, x * b = b * x := by
        intro x hx
        have h1 : x * u = u * x := mem_centralizer_singleton_iff.1 (hJ'X hx)
        rw [← hab] at h1
        have h2 : a * x * b = a * b * x := by
          calc a * x * b = x * a * b := by rw [hcomm a ha x hx]
            _ = x * (a * b) := by group
            _ = (a * b) * x := h1
            _ = a * b * x := rfl
        have h3 : x * b = b * x := by
          have := mul_left_cancel (a := a) (by simpa [mul_assoc] using h2)
          exact this
        exact h3
      have hoa : Odd (orderOf a) := odd_orderOf_of_mem_center hodd ha hacent
      have hob : Odd (orderOf b) := by
        obtain ⟨b', hb', hbb'⟩ := hb
        have hb'cent : ∀ x ∈ J, x * b' = b' * x := by
          intro x hx
          have hbb'' : t⁻¹ * b' * t = b := by simpa using hbb'
          have hy : t⁻¹ * x * t ∈ CFSG.conjugate J t :=
            ⟨x, hx, by simp⟩
          have h1 := hbcent _ hy
          rw [← hbb''] at h1
          have h2 : t⁻¹ * (x * b') * t = t⁻¹ * (b' * x) * t := by
            calc t⁻¹ * (x * b') * t = (t⁻¹ * x * t) * (t⁻¹ * b' * t) := by group
              _ = (t⁻¹ * b' * t) * (t⁻¹ * x * t) := h1
              _ = t⁻¹ * (b' * x) * t := by group
          exact mul_left_cancel (mul_right_cancel h2)
        have hob' : Odd (orderOf b') := odd_orderOf_of_mem_center hodd hb' hb'cent
        have hbb'' : t⁻¹ * b' * t = b := by simpa using hbb'
        have : orderOf b = orderOf b' := by
          rw [← hbb'']
          have h3 := (MulAut.conj t⁻¹).orderOf_eq b'
          simpa [MulAut.conj_apply] using h3
        rw [this]
        exact hob'
      have hcomm' : Commute a b := hcomm a ha b hb
      have hdvd : orderOf (a * b) ∣ (orderOf a).lcm (orderOf b) := hcomm'.orderOf_mul_dvd_lcm
      rw [hab, hu2] at hdvd
      have hodd2 : Odd ((orderOf a).lcm (orderOf b)) :=
        Odd.of_dvd_nat (hoa.mul hob) (Nat.lcm_dvd_mul _ _)
      exact (Nat.not_even_iff_odd.2 hodd2) (even_iff_two_dvd.2 hdvd)
  have hn : (K.subgroupOf X).Normal :=
    normal_of_component hbn hKM htH htK ht2' hCt hΛs hΛr hrank
  apply le_antisymm
  · exact le_sSup ⟨hKM.1, hn, ⟨MulEquiv.refl _⟩⟩
  · refine sSup_le ?_
    rintro N ⟨hNH, hNn, ⟨e⟩⟩
    by_cases hNK : N = K
    · exact hNK.le
    · exfalso
      have hNq : CFSG.IsQuasisimple ↥N := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hKq
      have hNcomp : IsCompIn N X := isCompIn_of_normal hNH hNq hNn
      have hcentK : N ≤ centralizer (K : Set H) := fun a ha =>
        mem_centralizer_iff.2 fun b hb => (hNcomp.commute_of_ne hKM hNK a ha b hb).symm
      have htN : t ∈ normalizer (N : Set H) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).1 hNn htH
      exact false_of_second_copy hbn ht2' hCt hKq hΛs hΛr hrank hcentK e htN

theorem componentProduct_eq_of_lemma36Data {s : TauCeti.SporadicName} {Q : PairClass} {m n : ℕ}
    (hd : Lemma36DataQ s Q m n) {N L K : Subgroup H} {t u : H} (hN : FStarSimple N)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hL : OddCover s L) (hQ : Q H L K u)
    (hstd : SolStd L) (hcyc : ∃ S : Sylow 2 (centralizer (L : Set H)), IsCyclic ↥S)
    (ht : t ∈ centralizer (L : Set H)) (ht2 : orderOf t = 2) (hB : BTheoremAt u)
    (hO : PumpUpOdd K t u) : K = componentProduct K u := by
  obtain ⟨hu2, huK, hKX, hchar, hKq, hAs, hA, hrank⟩ := hd.data H L K u hL hQ
  have hKL : K ≤ L := fun k hk => (hKX hk).1
  have hcycall := cyclic_sylow_all_of_exists hcyc
  have hCt := hstd.centralizer_le_normalizer ht ht2
  exact componentProduct_eq_of_pumpUp_Q hd.bound hkp hN.center_eq_bot hB hCt ht ht2 (hKL huK) hu2
    hKL huK hKq (fun k hk => (hKX hk).2) (normal_subgroupOf_of_characteristic ht hCt hKX hchar) hO
    (lam_isSolvable hcycall hAs)
    (fun E hE h2 _ => lam_elemAbelian_card_le_pow hcycall hA hE h2) hrank

end CFSG.EvenSporadicStandard.Induction
