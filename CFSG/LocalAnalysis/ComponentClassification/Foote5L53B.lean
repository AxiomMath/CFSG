module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53A
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L51A
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Tools2

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

@[expose] def Good53 (S L Q : Subgroup G) (w : G) : Prop :=
  ∃ g ∈ normalizer ((S ⊓ L : Subgroup G) : Set G), g⁻¹ * w * g ∈ Q ∧
    ∀ s ∈ S, s * (g⁻¹ * w * g) = g⁻¹ * w * g * s

omit [Finite G] in
theorem good53_of_conj {S L Q : Subgroup G} {w x : G}
    (hx : x ∈ normalizer ((S ⊓ L : Subgroup G) : Set G)) (hg : Good53 S L Q (x⁻¹ * w * x)) :
    Good53 S L Q w := by
  obtain ⟨g, hg, hgQ, hgZ⟩ := hg
  refine ⟨x * g, mul_mem hx hg, ?_, fun s hs => ?_⟩
  · rw [show (x * g)⁻¹ * w * (x * g) = g⁻¹ * (x⁻¹ * w * x) * g by group]
    exact hgQ
  · rw [show (x * g)⁻¹ * w * (x * g) = g⁻¹ * (x⁻¹ * w * x) * g by group]
    exact hgZ s hs

omit [Finite G] in
theorem mem_normalizer_of_le_centralizer {P : Subgroup G} {w : G}
    (hP : P ≤ centralizer ({w} : Set G)) : w ∈ normalizer (P : Set G) :=
  mem_normalizer_iff.mpr fun y => ⟨fun hy => by
    rw [(mem_centralizer_singleton_iff.mp (hP hy)).symm, mul_inv_cancel_right]; exact hy,
    fun hy => by
      have h1 := mem_centralizer_singleton_iff.mp (hP hy)
      have h2 : y = w * y * w⁻¹ := by
        calc y = w⁻¹ * (w * y * w⁻¹) * w := by group
          _ = w⁻¹ * (w * (w * y * w⁻¹) * w⁻¹) * w := by rw [← h1, mul_inv_cancel_right]
          _ = w * y * w⁻¹ := by group
      rw [h2]
      exact hy⟩

theorem exists_conj_isSylowOf_centralizer_of_sylow_normalizer
    {L Q S : Subgroup G} (hS : IsSylowOf 2 S (normalizer (L : Set G)))
    (hQ : Q = S ⊓ coreActionKernel L)
    (hcomm : ∀ r ∈ S ⊓ L, ∀ q ∈ Q, r * q = q * r) {w : G} (hwQ : w ∈ Q) :
    ∃ x ∈ normalizer (L : Set G), x ∈ normalizer ((S ⊓ L : Subgroup G) : Set G) ∧
      x⁻¹ * w * x ∈ Q ∧ IsSylowOf 2 (S ⊓ centralizer ({x⁻¹ * w * x} : Set G))
        (centralizer ({x⁻¹ * w * x} : Set G) ⊓ normalizer (L : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQS : Q ≤ S := (le_of_eq hQ).trans inf_le_left
  have hQle : Q ≤ coreActionKernel L := (le_of_eq hQ).trans inf_le_right
  have hQsyl : IsPGroup 2 Q := hQ.symm ▸ hS.isPGroup.to_le inf_le_left
  set K := centralizer ({w} : Set G) ⊓ normalizer (L : Set G) with hK
  have hRK : S ⊓ L ≤ K := le_inf (fun r hr =>
    mem_centralizer_singleton_iff.mpr (hcomm r hr w hwQ)) (inf_le_left.trans hS.le)
  obtain ⟨S₀, hS₀, hRS₀⟩ := exists_isSylowOf_ge_of_le hRK (hS.isPGroup.to_le inf_le_left)
  have hwK : w ∈ K := ⟨mem_centralizer_singleton_iff.mpr rfl, hS.le (hQS hwQ)⟩
  have hwS₀ : w ∈ S₀ := by
    have hw2 : IsPGroup 2 (zpowers w) := hQsyl.to_le (zpowers_le.mpr hwQ)
    have hwN : zpowers w ≤ normalizer (S₀ : Set G) :=
      zpowers_le.mpr (mem_normalizer_of_le_centralizer (hS₀.le.trans inf_le_left))
    have heq := hS₀.eq_of_le le_sup_left (sup_le hS₀.le (zpowers_le.mpr hwK))
      (hS₀.isPGroup.to_sup_of_normal_left' hw2 hwN)
    exact heq ▸ mem_sup_right (mem_zpowers w)
  obtain ⟨x, hxN, hx⟩ :=
    exists_conj_le_of_isSylowOf hS (hS₀.le.trans inf_le_right) hS₀.isPGroup
  have hxR : x ∈ normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    refine mem_normalizer_of_conjugate_eq (eq_of_le_of_card_ge (conjugate_le_of_forall
      fun r hr => mem_inf.mpr ⟨hx r (hRS₀ hr), ?_⟩) (card_conjugate_eq_card _ x).ge)
    exact conj_mem_of_mem_normalizer hxN (mem_inf.mp hr).2
  have hw'Q : x⁻¹ * w * x ∈ Q := by
    rw [hQ]
    refine mem_inf.mpr ⟨hx w hwS₀, ?_⟩
    have h1 := FooteLit.conj_mem_coreActionKernel (inv_mem hxN) (hQle hwQ)
    rwa [inv_inv] at h1
  refine ⟨x, hxN, hxR, hw'Q, ?_⟩
  have hsub : S ⊓ centralizer ({x⁻¹ * w * x} : Set G) ≤
      centralizer ({x⁻¹ * w * x} : Set G) ⊓ normalizer (L : Set G) :=
    le_inf inf_le_right (inf_le_left.trans hS.le)
  refine isSylowOf_of_twoPart_le (hS.isPGroup.to_le inf_le_left) hsub ?_
  obtain ⟨P', hP'⟩ := exists_isSylowOf 2
    (centralizer ({x⁻¹ * w * x} : Set G) ⊓ normalizer (L : Set G))
  rw [twoPart, ← hP'.card_eq]
  have h1 : conjugate P' x⁻¹ ≤ K := by
    refine conjugate_le_of_forall fun p hp => ?_
    rw [inv_inv]
    have hp' := hP'.le hp
    refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_,
      mul_mem (mul_mem hxN (mem_inf.mp hp').2) (inv_mem hxN)⟩
    have h2 := mem_centralizer_singleton_iff.mp (mem_inf.mp hp').1
    calc x * p * x⁻¹ * w = x * (p * (x⁻¹ * w * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * w * x) * p) * x⁻¹ := by rw [h2]
      _ = w * (x * p * x⁻¹) := by group
  have h2 : Nat.card P' ≤ Nat.card S₀ := by
    rw [← card_conjugate_eq_card P' x⁻¹, hS₀.card_eq]
    exact card_le_twoPart (hP'.isPGroup.map _) h1
  have h3 : conjugate S₀ x ≤ S ⊓ centralizer ({x⁻¹ * w * x} : Set G) := by
    refine conjugate_le_of_forall fun a ha => mem_inf.mpr ⟨hx a ha, ?_⟩
    have h4 := mem_centralizer_singleton_iff.mp (mem_inf.mp (hS₀.le ha)).1
    refine mem_centralizer_singleton_iff.mpr ?_
    calc x⁻¹ * a * x * (x⁻¹ * w * x) = x⁻¹ * (a * w) * x := by group
      _ = x⁻¹ * (w * a) * x := by rw [h4]
      _ = x⁻¹ * w * x * (x⁻¹ * a * x) := by group
  calc Nat.card P' ≤ Nat.card S₀ := h2
    _ = Nat.card (conjugate S₀ x) := (card_conjugate_eq_card _ _).symm
    _ ≤ _ := card_le_of_le h3

theorem isSylowOf_centralizer_of_not_good_generic
    {L P S K : Subgroup G} {w z : G}
    (hS2 : IsPGroup 2 S)
    (hPS : P ≤ S)
    (hPN : S ≤ normalizer (P : Set G))
    (hRNorm : S ≤ normalizer ((S ⊓ L : Subgroup G) : Set G))
    (hwP : w ∈ P)
    (hw2 : orderOf w = 2)
    (hzP : z ∈ P)
    (hz2 : orderOf z = 2)
    (hzS : ∀ s ∈ S, s * z = z * s)
    (hrank : CFSG.Open.pRank 2 P ≤ 2)
    (hCZ : centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (hCW : centralizer ({w} : Set G) ≤ normalizer (K : Set G))
    (hzK : z ∈ coreActionKernel K)
    (hroot : (S ⊓ centralizer ({w} : Set G)) ⊓ K = S ⊓ L)
    (hkernel : (S ⊓ centralizer ({w} : Set G)) ⊓ coreActionKernel K ≤ P)
    (hS0 : IsSylowOf 2 (S ⊓ centralizer ({w} : Set G))
      (centralizer ({w} : Set G) ⊓ normalizer (L : Set G)))
    (hng : ¬ Good53 S L P w) :
    IsSylowOf 2 (S ⊓ centralizer ({w} : Set G)) (centralizer ({w} : Set G)) ∧
      ∃ n ∈ S, n * w * n⁻¹ = w * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hw22 : w * w = 1 := by rw [← sq, ← hw2, pow_orderOf_eq_one]
  have hw1 : w ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hw2; omega
  have hz22 : z * z = 1 := by rw [← sq, ← hz2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hz2; omega
  have hwZ : ¬ ∀ s ∈ S, s * w = w * s := fun hZ =>
    hng ⟨1, one_mem _, by simpa using hwP, by simpa using hZ⟩
  have hwz : w ≠ z := fun h1 => hwZ (h1 ▸ hzS)
  have hwS0 : w ∈ S ⊓ centralizer ({w} : Set G) :=
    mem_inf.mpr ⟨hPS hwP, mem_centralizer_singleton_iff.mpr rfl⟩
  have hzS0 : z ∈ S ⊓ centralizer ({w} : Set G) :=
    mem_inf.mpr ⟨hPS hzP, mem_centralizer_singleton_iff.mpr (hzS w (hPS hwP)).symm⟩
  have hn : ∃ n ∈ S, n * w * n⁻¹ = w * z := by
    have hlt : S ⊓ centralizer ({w} : Set G) < S := lt_of_le_of_ne inf_le_left fun h1 =>
      hwZ fun s hs => mem_centralizer_singleton_iff.mp (mem_inf.mp (h1.symm ▸ hs :
        s ∈ S ⊓ centralizer ({w} : Set G))).2
    obtain ⟨n, hnS, hnS0, hnN⟩ := exists_mem_normalizer_not_mem_of_lt hS2 hlt
    have h1 : n * w * n⁻¹ ∈ S ⊓ centralizer ({w} : Set G) :=
      (mem_normalizer_iff.mp hnN w).mp hwS0
    have h2 : n * w * n⁻¹ * (n * w * n⁻¹) = 1 := by
      rw [show n * w * n⁻¹ * (n * w * n⁻¹) = n * (w * w) * n⁻¹ by group, hw22]; group
    have huP : n * w * n⁻¹ ∈ P := (mem_normalizer_iff.mp (hPN hnS) w).mp hwP
    have hcuw : n * w * n⁻¹ * w = w * (n * w * n⁻¹) :=
      mem_centralizer_singleton_iff.mp (mem_inf.mp h1).2
    have hcuz : n * w * n⁻¹ * z = z * (n * w * n⁻¹) :=
      hzS (n * w * n⁻¹) (mem_inf.mp h1).1
    have hcwz : w * z = z * w := hzS w (hPS hwP)
    rcases mem_four_of_pRank_le_two hrank hwP hzP huP hw22 hz22 h2 hw1 hz1 hwz hcwz
      hcuw hcuz with h3 | h3 | h3 | h3
    · exact absurd (by rw [show w = n⁻¹ * (n * w * n⁻¹) * n by group, h3]; group) hw1
    · exact absurd (mem_inf.mpr ⟨hnS, mem_centralizer_singleton_iff.mpr (by
        calc n * w = n * w * n⁻¹ * n := by group
          _ = w * n := by rw [h3])⟩) hnS0
    · exact absurd (by
        calc w = n⁻¹ * (n * w * n⁻¹) * n := by group
          _ = n⁻¹ * z * n := by rw [h3]
          _ = z := by rw [mul_assoc, ← hzS n hnS, ← mul_assoc, inv_mul_cancel, one_mul]) hwz
    · exact ⟨n, hnS, h3⟩
  refine ⟨?_, hn⟩
  by_contra hnot
  obtain ⟨S₁, hS₁, hS0S₁⟩ := exists_isSylowOf_ge_of_le (inf_le_right :
    S ⊓ centralizer ({w} : Set G) ≤ centralizer ({w} : Set G)) (hS2.to_le inf_le_left)
  have hlt : S ⊓ centralizer ({w} : Set G) < S₁ :=
    lt_of_le_of_ne hS0S₁ fun h1 => hnot (h1 ▸ hS₁)
  obtain ⟨s, hsS₁, hsS0, hsN⟩ := exists_mem_normalizer_not_mem_of_lt hS₁.isPGroup hlt
  have hsw : s ∈ centralizer ({w} : Set G) := hS₁.le hsS₁
  have hsz : ¬ s * z = z * s := by
    intro hsz
    have hsK : s ∈ centralizer ({w} : Set G) ⊓ normalizer (L : Set G) :=
      mem_inf.mpr ⟨hsw, hCZ (mem_centralizer_singleton_iff.mpr hsz)⟩
    have hs2 : IsPGroup 2 (zpowers s) := hS₁.isPGroup.to_le (zpowers_le.mpr hsS₁)
    have hp := (hS2.to_le inf_le_left).to_sup_of_normal_left' hs2 (zpowers_le.mpr hsN)
    have heq := hS0.eq_of_le le_sup_left (sup_le hS0.le (zpowers_le.mpr hsK)) hp
    exact hsS0 (heq ▸ mem_sup_right (mem_zpowers s))
  have hzs : s * z * s⁻¹ ∈ S ⊓ centralizer ({w} : Set G) :=
    (mem_normalizer_iff.mp hsN z).mp hzS0
  have hzsK : s * z * s⁻¹ ∈ coreActionKernel K :=
    FooteLit.conj_mem_coreActionKernel (hCW hsw) hzK
  have hzsP : s * z * s⁻¹ ∈ P := hkernel (mem_inf.mpr ⟨hzs, hzsK⟩)
  have hzs2 : s * z * s⁻¹ * (s * z * s⁻¹) = 1 := by
    rw [show s * z * s⁻¹ * (s * z * s⁻¹) = s * (z * z) * s⁻¹ by group, hz22]; group
  have hsR : s ∈ normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    rw [← hroot]
    exact FooteLit.mem_normalizer_inf' hsN (hCW hsw)
  have hgood : ∀ g ∈ normalizer ((S ⊓ L : Subgroup G) : Set G), g⁻¹ * w * g = z →
      Good53 S L P w := fun g hg hgz =>
    ⟨g, hg, by rw [hgz]; exact hzP, by rw [hgz]; exact hzS⟩
  have hcwz : w * z = z * w := hzS w (hPS hwP)
  have hcuw : s * z * s⁻¹ * w = w * (s * z * s⁻¹) :=
    mem_centralizer_singleton_iff.mp (mem_inf.mp hzs).2
  have hcuz : s * z * s⁻¹ * z = z * (s * z * s⁻¹) :=
    hzS (s * z * s⁻¹) (mem_inf.mp hzs).1
  rcases mem_four_of_pRank_le_two hrank hwP hzP hzsP hw22 hz22 hzs2 hw1 hz1 hwz hcwz
    hcuw hcuz with h3 | h3 | h3 | h3
  · have hz1' : z = 1 := by
      calc z = s⁻¹ * (s * z * s⁻¹) * s := by group
        _ = 1 := by rw [h3]; group
    rw [hz1', orderOf_one] at hz2
    omega
  · exact hng (hgood s hsR (by rw [← h3]; group))
  · exact hsz (by
      calc s * z = s * z * s⁻¹ * s := by group
        _ = z * s := by rw [h3])
  · obtain ⟨n, hnS, hnw⟩ := hn
    refine hng (hgood (n⁻¹ * s) (mul_mem (inv_mem (hRNorm hnS)) hsR) ?_)
    calc (n⁻¹ * s)⁻¹ * w * (n⁻¹ * s) = s⁻¹ * (n * w * n⁻¹) * s := by group
      _ = z := by rw [hnw, ← h3]; group

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem open_pRank_Q : CFSG.Open.pRank 2 Q = 2 := by
  have h1 := h.pRank_Q
  rwa [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h1

theorem mem_W {w u : G} (hwQ : w ∈ Q) (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwz : w ≠ z)
    (huQ : u ∈ Q) (hu2 : u * u = 1) (huw : u * w = w * u) :
    u = 1 ∨ u = w ∨ u = z ∨ u = w * z := by
  have hz2 : z * z = 1 := by rw [← sq, ← h.z2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun h1 => by
    have h2 := h.z2
    rw [h1, orderOf_one] at h2
    omega
  exact mem_four_of_pRank_le_two h.open_pRank_Q.le hwQ h.zQ huQ hw2 hz2 hu2 hw1 hz1 hwz
    (h.zS w (h.QS hwQ)) huw (h.zS u (h.QS huQ))

theorem inf_footeFixed_eq {w : G} (hwQ : w ∈ Q) (hw2 : orderOf w = 2) :
    S ⊓ centralizer ({w} : Set G) ⊓ footeFixed L w = S ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hfix, hLb, -, -, -, -⟩ := h.footeF_data hwQ hw2
  have hLb' : IsTwoComponentAt w (footeFixed L w) := hfix ▸ hLb
  obtain ⟨φ, -, -⟩ := exists_quotient_mulEquiv_footeFixed h.zL hw2 (h.Q_le hwQ) hLb'
  have hRle : S ⊓ L ≤ S ⊓ centralizer ({w} : Set G) ⊓ footeFixed L w := by
    refine le_inf (le_inf inf_le_left fun r hr => ?_) (h.R_le_footeFixed hwQ)
    exact mem_centralizer_singleton_iff.mpr (h.commute_Q_R hwQ hr).symm
  refine (eq_of_le_of_card_ge hRle ?_).symm
  rw [h.R_sylow.card_eq, ← twoPart, twoPart_eq_of_quotient_equiv φ]
  exact card_le_twoPart (h.isPGroup_S.to_le (inf_le_left.trans inf_le_left)) inf_le_right

theorem exists_conj_isSylowOf_centralizer {w : G} (hwQ : w ∈ Q) :
    ∃ x ∈ normalizer (L : Set G), x ∈ normalizer ((S ⊓ L : Subgroup G) : Set G) ∧
      x⁻¹ * w * x ∈ Q ∧ IsSylowOf 2 (S ⊓ centralizer ({x⁻¹ * w * x} : Set G))
        (centralizer ({x⁻¹ * w * x} : Set G) ⊓ normalizer (L : Set G)) :=
  exists_conj_isSylowOf_centralizer_of_sylow_normalizer h.sylS h.inf_coreActionKernel.symm
    (fun _ hr _ hq => (h.commute_Q_R hq hr).symm) hwQ

theorem mem_Q_of_mem_coreActionKernel_footeFixed {w x : G} (hwQ : w ∈ Q) (hw2 : orderOf w = 2)
    (hxS : x ∈ S) (hxw : x ∈ centralizer ({w} : Set G))
    (hxC : x ∈ coreActionKernel (footeFixed L w)) : x ∈ Q := by
  obtain ⟨hfix, hLb, hLbF, -, -, -⟩ := h.footeF_data hwQ hw2
  have hLb' : IsTwoComponentAt w (footeFixed L w) := hfix ▸ hLb
  have hxNb : x ∈ normalizer (footeFixed L w : Set G) := by
    rw [hfix]
    exact le_normalizer_of_mem_footeFamilyOf h.sec4.huniq hLb hLbF hxw
  rw [← h.inf_coreActionKernel]
  exact mem_inf.mpr ⟨hxS, (Foote47.mem_coreActionKernel_iff_of_footeFixed h.zL hw2 (h.Q_le hwQ)
    hLb' (h.S_le hxS) hxNb hxw).mpr hxC⟩

theorem isSylowOf_centralizer_of_not_good {w : G} (hwQ : w ∈ Q) (hw2 : orderOf w = 2)
    (hng : ¬ Good53 S L Q w)
    (hS₀ : IsSylowOf 2 (S ⊓ centralizer ({w} : Set G))
      (centralizer ({w} : Set G) ⊓ normalizer (L : Set G))) :
    IsSylowOf 2 (S ⊓ centralizer ({w} : Set G)) (centralizer ({w} : Set G)) ∧
      ∃ n ∈ S, n * w * n⁻¹ = w * z := by
  obtain ⟨hfix, hLb, hLbF, -, -, -⟩ := h.footeF_data hwQ hw2
  have hLb' : IsTwoComponentAt w (footeFixed L w) := hfix ▸ hLb
  have hCW : centralizer ({w} : Set G) ≤ normalizer (footeFixed L w : Set G) := by
    rw [hfix]
    exact le_normalizer_of_mem_footeFamilyOf h.sec4.huniq hLb hLbF
  have hzK : z ∈ coreActionKernel (footeFixed L w) :=
    mem_coreActionKernel_footeFixed (h.zS w (h.QS hwQ)) (h.Q_le h.zQ) hLb'
  exact isSylowOf_centralizer_of_not_good_generic h.isPGroup_S h.QS h.S_le_normalizer_Q
    h.S_le_normalizer_R hwQ hw2 h.zQ h.z2 h.zS h.open_pRank_Q.le
    h.centralizer_le_normalizer hCW hzK (h.inf_footeFixed_eq hwQ hw2)
    (by
      intro x hx
      obtain ⟨⟨hxS, hxC⟩, hxK⟩ := mem_inf.mp hx
      exact h.mem_Q_of_mem_coreActionKernel_footeFixed hwQ hw2 hxS hxC hxK)
    hS₀ hng

end Sec5

end CFSG.ComponentClassification.Foote5
