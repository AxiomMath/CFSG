module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Lemma36Q
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.RowDataB
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.EmbedLam
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Second
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Transfer36

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.QuasithinUnique.Id2519 CFSG.QuasithinUnique.I32
  CFSG.EvenSporadicStandard.Solomon78
open scoped Pointwise

variable {H : Type} [Group H]

@[expose] def NoOtherComponent (K : Subgroup H) (t u : H) : Prop :=
  ∀ M : Subgroup H, IsCompIn M (centralizer ({u} : Set H)) → K ≤ M ⊔ CFSG.conjugate M t →
    M ≠ K → False

theorem false_of_mem_sup_conj [Finite H] {X J : Subgroup H} {t u : H} (hJ : IsCompIn J X)
    (htX : t ∈ X) (hJne : J ≠ CFSG.conjugate J t)
    (hodd : Odd (Nat.card (center ↥J))) (hu2 : orderOf u = 2)
    (hXu : ∀ x ∈ X, x * u = u * x) (huJ : u ∈ J ⊔ CFSG.conjugate J t) : False := by
  have htinvH : t⁻¹ ∈ X := X.inv_mem htX
  have hJ'comp : IsCompIn (CFSG.conjugate J t) X := hJ.map_conj htinvH
  have hcomm : ∀ a ∈ J, ∀ b ∈ CFSG.conjugate J t, a * b = b * a :=
    hJ.commute_of_ne hJ'comp hJne
  have hJnorm : J ≤ normalizer (CFSG.conjugate J t : Set H) := fun a ha =>
    Subgroup.centralizer_le_normalizer (CFSG.conjugate J t : Set H)
      (mem_centralizer_iff.2 fun b hb => (hcomm a ha b hb).symm)
  have hu' : u ∈ (J : Set H) * (CFSG.conjugate J t : Set H) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right J (CFSG.conjugate J t) hJnorm]
    exact huJ
  obtain ⟨a, ha, b, hb, hab0⟩ := hu'
  have hab : a * b = u := hab0
  have hJH : J ≤ X := hJ.1
  have hJ'X : CFSG.conjugate J t ≤ X := hJ'comp.1
  have hacent : ∀ x ∈ J, x * a = a * x := by
    intro x hx
    have h1 : x * u = u * x := hXu x (hJH hx)
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
    have h1 : x * u = u * x := hXu x (hJ'X hx)
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

theorem noOtherComponent_of_pumpUpOdd [Finite H] {K : Subgroup H} {t u : H} (hu2 : orderOf u = 2)
    (huK : u ∈ K) (htH : t ∈ centralizer ({u} : Set H)) (hO : PumpUpOdd K t u) :
    NoOtherComponent K t u := by
  intro M hM hKM hMK
  have hodd := hO M hM hKM hMK
  by_cases hMt : M = CFSG.conjugate M t
  · have hKM' : K ≤ M := by
      have : M ⊔ CFSG.conjugate M t = M := by rw [← hMt, sup_idem]
      rwa [this] at hKM
    exact not_odd_card_center_of_mem (hKM' huK) hu2
      (fun x hx => mem_centralizer_singleton_iff.1 (hM.1 hx)) hodd
  · exact false_of_mem_sup_conj hM htH hMt hodd hu2
      (fun x hx => mem_centralizer_singleton_iff.1 hx) (hKM huK)

theorem noOtherComponent_of_transfer [Finite H] {S : List TauCeti.SporadicName} {K : Subgroup H}
    {t u : H} (hu2 : orderOf u = 2) (hout : OutTwoCovers S)
    (hcomm : u ∈ ⁅centralizer ({u} : Set H), centralizer ({u} : Set H)⁆)
    (htypeL : ∀ M : Subgroup H, IsCompIn M (centralizer ({u} : Set H)) →
      K ≤ M ⊔ CFSG.conjugate M t → M ≠ K → ∃ s' ∈ S, OddCover s' M)
    (hC2 : ∀ M : Subgroup H, IsCompIn M (centralizer ({u} : Set H)) →
      (∃ s' ∈ S, OddCover s' M) → ∀ Q : Sylow 2 (centralizer (M : Set H)), Nat.card Q = 2) :
    NoOtherComponent K t u := by
  intro M hM hKM hMK
  obtain ⟨s', hs', hcov⟩ := htypeL M hM hKM hMK
  exact false_of_typeL_component hu2 hM hcov.odd_center (hout s' hs' H M hcov)
    (hC2 M hM ⟨s', hs', hcov⟩) hcomm

variable [Finite H]

theorem componentProduct_eq_of_noOther {L K : Subgroup H} {t u : H}
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hZ : center H = ⊥)
    (hB : BTheoremAt u) (hCt : centralizer ({t} : Set H) ≤ normalizer (L : Set H))
    (ht : t ∈ centralizer (L : Set H)) (ht2 : orderOf t = 2) (hu : u ∈ L) (hu2 : orderOf u = 2)
    (hKL : K ≤ L) (hKq : CFSG.IsQuasisimple ↥K) (hKu : K ≤ centralizer ({u} : Set H))
    (hKn : (K.subgroupOf (centralizer ({u} : Set H) ⊓ centralizer ({t} : Set H))).Normal)
    (hΛs : Group.IsSolvable ↥(lam L K)) (hemb : NoFixedEmbeds ↥K ↥(lam L K))
    (hex : NoOtherComponent K t u) : K = componentProduct K u := by
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
      · exact (hex M hMcomp (le_sup_of_le_left hKleM) hMK).elim
    · exfalso
      have hJcomp : IsCompIn J X := hB J hJ
      have hKJ : K ≤ J ⊔ CFSG.conjugate J t := by
        rw [← hJeq]
        exact le_iSup₂_of_le (f := fun g (_ : g ∈ oddLayer X) => CFSG.conjugate K g) 1 (one_mem _)
          (by rw [conjugate_one])
      have hJK : J ≠ K := by
        intro hJK
        apply hJne
        rw [hJK, conjugate_eq_of_mem_centralizer htK]
      exact hex J hJcomp hKJ hJK
  have hn : (K.subgroupOf X).Normal :=
    normal_of_component_emb hKM htH htK ht2' hCt hΛs hemb
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
      exact false_of_second_copy_emb ht2' hCt htK hKq hΛs hemb hcentK e htN

theorem componentProduct_eq_of_localData {m e : ℕ} (hm : m ≤ 2) {s : TauCeti.SporadicName}
    {N L K : Subgroup H} {t u : H} (hN : FStarSimple N)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hL : OddCover s L)
    (hstd : SolStd L) (hcyc : ∃ S : Sylow 2 (centralizer (L : Set H)), IsCyclic ↥S)
    (ht : t ∈ centralizer (L : Set H)) (ht2 : orderOf t = 2) (hB : BTheoremAt u)
    (hu2 : orderOf u = 2) (huL : u ∈ L) (hKX : K ≤ L ⊓ centralizer ({u} : Set H))
    (hchar : (K.subgroupOf (L ⊓ centralizer ({u} : Set H))).Characteristic)
    (hKq : CFSG.IsQuasisimple ↥K) (hAs : Group.IsSolvable ↥(autCentralizer L K))
    (hA : twoAdic (autCentralizer L K) ≤ m) (he : ElemBound e (autCentralizer L K))
    (hin : ∀ α ∈ autCentralizer L K, ∃ g : ↥L, α = MulAut.conj g)
    (hfix : InvolutionFixesNotLam ↥K (2 * e)) (hex : NoOtherComponent K t u) :
    K = componentProduct K u := by
  have hKL : K ≤ L := fun k hk => (hKX hk).1
  have hcycall := cyclic_sylow_all_of_exists hcyc
  have hCt := hstd.centralizer_le_normalizer ht ht2
  have hlam := lamLike_lam_elem hm hcycall hAs hA he hin hKL hL.odd_center
  exact componentProduct_eq_of_noOther hkp hN.center_eq_bot hB hCt ht ht2 huL hu2 hKL hKq
    (fun k hk => (hKX hk).2) (normal_subgroupOf_of_characteristic ht hCt hKX hchar) hlam.1
    (NoFixedEmbeds.of_lamLike hfix hlam) hex

theorem componentProduct_eq_of_lemma36e {S : List TauCeti.SporadicName} {s : TauCeti.SporadicName}
    {Q : PairClass} {m e : ℕ} (hd : Lemma36eDataQ s Q m e) (hout : OutTwoCovers S)
    {N L K : Subgroup H} {t u : H} (hN : FStarSimple N)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hL : OddCover s L) (hQ : Q H L K u)
    (hstd : SolStd L) (hcyc : ∃ S : Sylow 2 (centralizer (L : Set H)), IsCyclic ↥S)
    (ht : t ∈ centralizer (L : Set H)) (ht2 : orderOf t = 2) (hB : BTheoremAt u)
    (htypeL : ∀ M : Subgroup H, IsCompIn M (centralizer ({u} : Set H)) →
      K ≤ M ⊔ CFSG.conjugate M t → M ≠ K → ∃ s' ∈ S, OddCover s' M)
    (hC2 : u ∉ K → ∀ M : Subgroup H, IsCompIn M (centralizer ({u} : Set H)) →
      (∃ s' ∈ S, OddCover s' M) → ∀ Q : Sylow 2 (centralizer (M : Set H)), Nat.card Q = 2) :
    K = componentProduct K u := by
  obtain ⟨hu2, huL, hKX, hchar, hKq, hAs, hA, he, hin, hfix, hcase⟩ := hd.data H L K u hL hQ
  have htH : t ∈ centralizer ({u} : Set H) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht u huL).symm
  have hex : NoOtherComponent K t u := by
    by_cases huK : u ∈ K
    · refine noOtherComponent_of_pumpUpOdd hu2 huK htH fun M hM hKM hMK => ?_
      obtain ⟨s', -, hcov⟩ := htypeL M hM hKM hMK
      exact hcov.odd_center
    · refine noOtherComponent_of_transfer hu2 hout ?_ htypeL (hC2 huK)
      exact (Subgroup.commutator_mono inf_le_right inf_le_right) (hcase.resolve_left huK)
  exact componentProduct_eq_of_localData hd.m_le hN hkp hL hstd hcyc ht ht2 hB hu2 huL hKX hchar
    hKq hAs hA he hin hfix hex

end CFSG.EvenSporadicStandard.Induction
