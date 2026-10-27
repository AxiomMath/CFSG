module

public import CFSG.LocalAnalysis.GL83PartI.I_24_3.CyclicPCore
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.Engine
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.Lift
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.Plane
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.Inner
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.Omega
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.CoverTransfer
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.ListDefs
public import CFSG.LieType.SeitzGeneration.Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointTypes

public section

namespace GL83.I243

open CFSG CFSG.Open CFSG.PreuniquenessRankFour.Helpers Subgroup

structure Cfg (p : ℕ) {X : Type} [Group X] [Finite X] (R : Sylow p X) (B K : Subgroup X)
    (z : X) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  comp : IsComponentOf K ⊤
  not_le : ¬ K ≤ GLBWeakCore p (R : Subgroup X)
  le_R : B ≤ (R : Subgroup X)
  elem : IsElemAbelian p B
  card_eq : Nat.card B = p ^ Open.pRank p (R : Subgroup X)
  rank3 : 3 ≤ Open.pRank p (R : Subgroup X)
  normalizes : B ≤ Subgroup.normalizer (K : Set X)
  mem_B : z ∈ B
  mem_K : z ∈ K
  central : z ∈ Subgroup.centralizer (K : Set X)
  order : orderOf z = p
  cen_le : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b ∈ Subgroup.zpowers z
  omega : ∀ c ∈ K, c ∈ Subgroup.centralizer (K : Set X) → c ^ p = 1 → c ∈ Subgroup.zpowers z

section Cfg

variable {X : Type} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {B K : Subgroup X} {z : X}

theorem Cfg.three_le_card (h : Cfg p R B K z) : p ^ 3 ≤ Nat.card B := by
  rw [h.card_eq]
  exact Nat.pow_le_pow_right h.prime.pos h.rank3

theorem Cfg.three_le_pRank (h : Cfg p R B K z) : 3 ≤ Open.pRank p B :=
  (pRank_eq_of_max h.prime R h.le_R h.elem h.card_eq).symm ▸ h.rank3

theorem Cfg.core_le (h : Cfg p R B K z) : GLBCore p 2 B ≤ GLBWeakCore p (R : Subgroup X) := by
  rw [← weakCore_eq_fullCore_of_commutative p h.prime B h.elem.1 h.three_le_pRank]
  exact weakCore_mono p h.prime h.le_R

theorem Cfg.false_of_core (h : Cfg p R B K z) (hK : K ≤ GLBCore p 2 B) : False :=
  h.not_le (hK.trans h.core_le)

def Cfg.gens (B K : Subgroup X) (z : X) : Set ↥K :=
  {k : ↥K | ∃ f ∈ B, f ∉ Subgroup.zpowers z ∧
    f * (k : X) * f⁻¹ * (k : X)⁻¹ ∈ Subgroup.centralizer (K : Set X)}

theorem Cfg.false_of_closure (h : Cfg p R B K z) (hgen : Subgroup.closure (Cfg.gens B K z) = ⊤) :
    False :=
  h.false_of_core (le_core_of_closure h.prime h.ne_two h.comp.2.2.1 h.elem h.normalizes
    h.mem_B h.mem_K h.central h.order h.omega hgen)

theorem Cfg.closure_gens_eq_top (h : Cfg p R B K z) {E : Subgroup (MulAut ↥K)}
    (hEB : ∀ ε ∈ E, ∃ f ∈ B, ∀ y : ↥K, ((ε y : ↥K) : X) = f * (y : X) * f⁻¹)
    (hcl : Subgroup.closure
      {k : ↥K | ∃ ε ∈ E, ε ≠ 1 ∧ ε k * k⁻¹ ∈ Subgroup.center ↥K} = ⊤) :
    Subgroup.closure (Cfg.gens B K z) = ⊤ := by
  rw [eq_top_iff, ← hcl]
  refine Subgroup.closure_mono ?_
  rintro k ⟨ε, hε, hε1, hk⟩
  obtain ⟨f, hfB, hf⟩ := hEB ε hε
  refine ⟨f, hfB, ?_, ?_⟩
  · intro hfz
    apply hε1
    have hfc : f ∈ Subgroup.centralizer (K : Set X) :=
      (Subgroup.zpowers_le.mpr h.central) hfz
    ext y
    rw [hf y, MulAut.one_apply]
    have := Subgroup.mem_centralizer_iff.mp hfc (y : X) y.2
    rw [← this, mul_inv_cancel_right]
  · have hc := Subgroup.mem_center_iff.mp hk
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    have h1 := congrArg (fun a : ↥K => (a : X)) (hc ⟨y, hy⟩)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hf] at h1
    exact h1

end Cfg

@[expose] def ThreeCoverWeakCore (i : TauCeti.CFSGIndex) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → Subgroup.center K ≠ ⊥ →
    IsPGroup 3 (Subgroup.center K) → IsCyclic (Subgroup.center K) →
    Nonempty (K ⧸ Subgroup.center K ≃* i.Group) →
    ∀ T : Sylow 3 K, GLBWeakCore 3 (T : Subgroup K) = ⊤

@[expose] def ThreeCoverTable : Prop :=
  ∀ i : TauCeti.CFSGIndex, IsThreeCoverIndex i → ThreeCoverWeakCore i

@[expose] def SmallThreeFacts : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → ∀ i : TauCeti.CFSGIndex,
    IsThreeSmallIndex i → Nonempty (K ⧸ Subgroup.center K ≃* i.Group) →
    CFSG.AGLEmbedding.KOutTwoGroup K ∧ 3 ^ 2 ∣ Nat.card (K ⧸ Subgroup.center K) ∧
      ¬ 3 ^ 3 ∣ Nat.card (K ⧸ Subgroup.center K)

@[expose] def LFourFacts : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d.1 = .A 2 q) →
    ∀ [Finite (TauCeti.CFSGIndex.lie d).Group],
    (3 ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group ∧
      ¬ 3 ^ 3 ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group) ∧
    Open.pRank 3 (⊤ : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)) ≤ 2 ∧
    (∀ E : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group), IsElemAbelian 3 E →
      Nat.card E = 3 ^ 2 →
      ¬ E ≤ (MulAut.conj : (TauCeti.CFSGIndex.lie d).Group →* MulAut _).range →
      Subgroup.closure {k : (TauCeti.CFSGIndex.lie d).Group | ∃ e ∈ E, e ≠ 1 ∧ e k = k} = ⊤)

section Cases

variable {X : Type} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {B K : Subgroup X} {z : X}

theorem Cfg.false_of_lie (h : Cfg p R B K z)
    (hS : CFSG.LieType.SeitzGeneration.SeitzPlanes fun d p _ => IsPCoverLieIndex p d.1)
    {d : TauCeti.ValidLieTypeIndex} (hchar : p ≠ d.1.characteristic)
    (hnex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1) (hsc : IsPCoverLieIndex p d.1)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) : False := by
  have hperf : Group.IsPerfect ↥K := ⟨h.comp.2.2.1⟩
  obtain ⟨E, hEel, hEcard, hEB⟩ := exists_plane_image h.prime h.normalizes h.elem
    h.mem_B h.order h.cen_le h.three_le_card
  have hcl := closure_fix_lift hperf e (fun _ => True)
    (fun E' hE' hc _ => hS d p h.prime h.ne_two hchar hnex E' hE' hc hsc) E hEel hEcard trivial
  exact h.false_of_closure (h.closure_gens_eq_top hEB hcl)

end Cases

theorem mem_of_pow_mem_of_pow_eq_one {G : Type*} [Group G] {H : Subgroup G} {x : G} {m n : ℕ}
    (hmn : Nat.Coprime m n) (hm : x ^ m ∈ H) (hn : x ^ n = 1) : x ∈ H := by
  rcases Nat.lt_or_ge 1 n with hn1 | hn1
  · obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hmn hn1
    have h := Nat.div_add_mod (m * u) n
    rw [hu] at h
    have hx : x = (x ^ m) ^ u := by
      rw [← pow_mul, ← h, pow_add, pow_mul, hn, one_pow, one_mul, pow_one]
    rw [hx]
    exact H.pow_mem hm u
  · interval_cases n
    · rw [Nat.coprime_zero_right] at hmn
      subst hmn
      simpa using hm
    · simp at hn
      rw [hn]
      exact H.one_mem

theorem inner_of_kOutTwoGroup {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K B : Subgroup X}
    (hBel : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hOut : CFSG.AGLEmbedding.KOutTwoGroup ↥K) :
    ∀ b ∈ B, ∃ k ∈ K, ∀ y ∈ K, b * y * b⁻¹ = k * y * k⁻¹ := by
  intro b hb
  let φ : MulAut ↥K := K.normalizerMonoidHom ⟨b, hBN hb⟩
  have hφ : ∀ y : ↥K, ((φ y : ↥K) : X) = b * (y : X) * b⁻¹ := fun y => rfl
  obtain ⟨k₁, hk₁⟩ := hOut φ
  have hφp : φ ^ p = 1 := by
    have h1 : (⟨b, hBN hb⟩ : Subgroup.normalizer (K : Set X)) ^ p = 1 :=
      Subtype.ext (by simpa using hBel.2 b hb)
    show (K.normalizerMonoidHom ⟨b, hBN hb⟩) ^ p = 1
    rw [← map_pow, h1, map_one]
  have hcop : Nat.Coprime (2 ^ k₁) p :=
    Nat.Coprime.pow_left k₁ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have hmem := mem_of_pow_mem_of_pow_eq_one (H := (MulAut.conj : ↥K →* MulAut ↥K).range) hcop hk₁
    hφp
  obtain ⟨k, hk⟩ := hmem
  refine ⟨(k : X), k.2, fun y hy => ?_⟩
  have := congrArg (fun a : MulAut ↥K => ((a ⟨y, hy⟩ : ↥K) : X)) hk
  simpa [hφ, MulAut.conj_apply] using this.symm

theorem not_pow_four_dvd_card {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hZ : p ∣ Nat.card (Subgroup.center K)) (hZ9 : ¬ p ^ 2 ∣ Nat.card (Subgroup.center K))
    (h9 : p ^ 2 ∣ Nat.card (K ⧸ Subgroup.center K))
    (h27 : ¬ p ^ 3 ∣ Nat.card (K ⧸ Subgroup.center K)) : ¬ p ^ 4 ∣ Nat.card K := by
  obtain ⟨a, ha⟩ := h9
  obtain ⟨b, hb⟩ := hZ
  have hpa : ¬ p ∣ a := by
    intro hpa
    apply h27
    rw [ha]
    obtain ⟨c, rfl⟩ := hpa
    exact ⟨c, by ring⟩
  have hpb : ¬ p ∣ b := by
    intro hpb
    apply hZ9
    rw [hb]
    obtain ⟨c, rfl⟩ := hpb
    exact ⟨c, by ring⟩
  have hK : Nat.card K = p ^ 3 * (a * b) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K), ha, hb]
    ring
  intro h4
  rw [hK, show p ^ 4 = p ^ 3 * p by ring] at h4
  have := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos 3) h4
  rcases (Nat.Prime.dvd_mul hp).mp this with h | h
  · exact hpa h
  · exact hpb h

section Cases2

variable {X : Type} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {B K : Subgroup X} {z : X}

theorem Cfg.false_of_cover {R : Sylow 3 X} (h : Cfg 3 R B K z) {i : TauCeti.CFSGIndex}
    (hi : ThreeCoverWeakCore i) (e : ↥K ⧸ Subgroup.center ↥K ≃* i.Group)
    (hO : CFSG.pCore 3 ↥K ≠ ⊥) : False := by
  have hcyc := isCyclic_pCore_of_omega h.prime h.comp.2.2 h.order h.omega
  exact h.not_le (le_weakCore_of_cover R h.comp hO hcyc
    (fun K' _ _ hq' hZ' hZp' hZc' ⟨e'⟩ T => hi K' hq' hZ' hZp' hZc' ⟨e'.trans e⟩ T))

theorem Cfg.false_of_small (h : Cfg p R B K z) (hOut : CFSG.AGLEmbedding.KOutTwoGroup ↥K)
    (h9 : p ^ 2 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K))
    (h27 : ¬ p ^ 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K))
    (hZ : p ∣ Nat.card (Subgroup.center ↥K)) (hZ9 : ¬ p ^ 2 ∣ Nat.card (Subgroup.center ↥K)) :
    False :=
  false_of_inner h.prime h.ne_two R h.comp h.not_le h.le_R h.elem h.three_le_card h.normalizes
    h.mem_B h.mem_K h.central h.order h.cen_le
    (inner_of_kOutTwoGroup h.prime h.ne_two h.elem h.normalizes hOut)
    (not_pow_four_dvd_card h.prime hZ hZ9 h9 h27)

end Cases2

section Cases3

variable {X : Type} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {B K : Subgroup X} {z : X}

theorem Cfg.false_of_lfour {R : Sylow 3 X} (h : Cfg 3 R B K z) {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d.1 = .A 2 q)
    (hF : LFourFacts) (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hZ : 3 ∣ Nat.card (Subgroup.center ↥K)) (hZ9 : ¬ 3 ^ 2 ∣ Nat.card (Subgroup.center ↥K)) :
    False := by
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv _ e.toEquiv
  obtain ⟨⟨h9, h27⟩, hrk, hgen⟩ := hF d hd
  have hperf : Group.IsPerfect ↥K := ⟨h.comp.2.2.1⟩
  haveI : Group.IsPerfect ↥K := hperf
  have hcardL : Nat.card (↥K ⧸ Subgroup.center ↥K) = Nat.card (TauCeti.CFSGIndex.lie d).Group :=
    Nat.card_congr e.toEquiv
  have hρ : Function.Injective ((MulAut.congr e).toMonoidHom.comp
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K)) :=
    (MulAut.congr e).injective.comp
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective _)
  have hB27 : Nat.card B = 3 ^ 3 := by
    have hlt : ¬ 3 ^ 4 ≤ Nat.card B := by
      intro h4
      obtain ⟨E', hE'el, hE'card, -⟩ := exists_elemAbelian_image h.prime h.normalizes h.elem
        h.mem_B h.order h.cen_le (n := 3) h4
      have hel := hE'el.map ((MulAut.congr e).toMonoidHom.comp
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K))
      have hc : Nat.card (E'.map ((MulAut.congr e).toMonoidHom.comp
          (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K))) = 3 ^ 3 := by
        rw [Subgroup.card_map_of_injective hρ, hE'card]
      have := CFSG.SectionRank.le_pRank (by norm_num) le_top hel hc
      omega
    have hr : Open.pRank 3 (R : Subgroup X) < 4 := by
      by_contra hge
      push Not at hge
      exact hlt (h.card_eq ▸ Nat.pow_le_pow_right (by norm_num) hge)
    rw [h.card_eq]
    congr 1
    have := h.rank3
    omega
  obtain ⟨E, hEel, hEcard, hEB, hBE⟩ := exists_plane_image_eq h.prime h.normalizes
    h.elem h.mem_B h.order h.cen_le hB27 h.central
  by_cases hinn : ∀ b ∈ B, ∃ k ∈ K, ∀ y ∈ K, b * y * b⁻¹ = k * y * k⁻¹
  · exact false_of_inner h.prime h.ne_two R h.comp h.not_le h.le_R h.elem
      (by rw [hB27]) h.normalizes h.mem_B h.mem_K h.central h.order h.cen_le hinn
      (not_pow_four_dvd_card h.prime hZ hZ9 (hcardL ▸ h9) (hcardL ▸ h27))
  · push Not at hinn
    obtain ⟨b, hbB, hb⟩ := hinn
    have hnotle : ¬ E ≤ (MulAut.conj : ↥K →* MulAut ↥K).range := by
      intro hle
      obtain ⟨ε, hεE, hεb⟩ := hBE b hbB
      obtain ⟨k, hk⟩ := hle hεE
      obtain ⟨y, hy, hne⟩ := hb k k.2
      apply hne
      have h1 := hεb ⟨y, hy⟩
      have h2 := congrArg (fun a : MulAut ↥K => ((a ⟨y, hy⟩ : ↥K) : X)) hk
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h2
      rw [← h1, ← h2]
    have hQ := not_le_range_conj_map hperf e hnotle
    have hcl := closure_fix_lift hperf e
      (fun E' => ¬ E' ≤ (MulAut.conj : (TauCeti.CFSGIndex.lie d).Group →* MulAut _).range)
      (fun E' hE' hc hQ' => hgen E' hE' hc hQ') E hEel hEcard hQ
    exact h.false_of_closure (h.closure_gens_eq_top hEB hcl)

end Cases3

theorem gl83ComponentPCoreTrivial_of_seitzCover
    (hS : CFSG.LieType.SeitzGeneration.SeitzPlanes fun d p _ => IsPCoverLieIndex p d.1)
    (hList : PCoverList) (hCover : ThreeCoverTable)
    (hSmall : SmallThreeFacts) (hL4 : LFourFacts) :
    CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial := by
  intro X _ _ hX p R K hp hp2 hrank hK hKR
  by_contra hO
  have hq : Open.IsQuasisimple ↥K := hK.2.2
  have hZ : p ∣ Nat.card (Subgroup.center ↥K) :=
    dvd_card_center_of_pCore_ne_bot hp hq hO
  obtain ⟨B, hBR, hBel, hBcard⟩ := pRank_attained p hp (R : Subgroup X)
  have hBN := normalizes_of_not_le_weakCore hp hp2 R hBR hBel hBcard hrank hK hZ hKR
  obtain ⟨z, hzB, hzK, hzc, hzp⟩ := exists_mem_center_of_normalizes hp hBel
    (sc_of_maximal hp R hBel hBcard) hBN hZ
  have hB3 : 3 ≤ Open.pRank p B := (pRank_eq_of_max hp R hBR hBel hBcard).symm ▸ hrank
  have hCB := inf_centralizer_le_zpowers hp R hKR hBR hBel hB3 hzB hzc hzp
  obtain ⟨i, ⟨e⟩⟩ := hX.isCatalogGroup_center_quotient hK
  have hcase := hList ↥K hq p hp hp2 hZ i ⟨e⟩
  have hΩ := omega_le_zpowers_of_not_le_weakCore hp R hK hKR hBR hBel hBcard hrank hBN hzB hzK hzc hzp hCB
  have hcfg : Cfg p R B K z :=
    ⟨hp, hp2, hK, hKR, hBR, hBel, hBcard, hrank, hBN, hzB, hzK, hzc, hzp, hCB, hΩ⟩
  rcases hcase with ⟨d, rfl, hchar, hnex, hsc⟩ | ⟨rfl, hB | ⟨hsm | hl4, h9⟩⟩
  · exact hcfg.false_of_lie hS hchar hnex hsc e
  · exact hcfg.false_of_cover (hCover _ hB) e hO
  · obtain ⟨hOut, h9', h27'⟩ := hSmall ↥K hq i hsm ⟨e⟩
    exact hcfg.false_of_small hOut h9' h27' hZ h9
  · obtain ⟨d, rfl, hd⟩ := hl4
    exact hcfg.false_of_lfour hd hL4 e hZ h9

theorem gl83ComponentPCoreTrivial_of_seitz
    (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) (hList : PCoverList) (hCover : ThreeCoverTable)
    (hSmall : SmallThreeFacts) (hL4 : LFourFacts) :
    CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial :=
  gl83ComponentPCoreTrivial_of_seitzCover
    (CFSG.LieType.SeitzGeneration.SeitzPlanes.mono (fun _ _ _ _ => trivial)
      (CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_iff.mp hS))
    hList hCover hSmall hL4

end GL83.I243
