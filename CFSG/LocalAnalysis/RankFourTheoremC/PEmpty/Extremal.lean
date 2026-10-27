module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fusion
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614ExtDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614L615
import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Plane

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (IsTwoInvariantIn IsMaxTwoInvariantIn Prop614Pair
  Prop614Better Prop614Extremal SmallRankPlane exists_isMaxTwoInvariantIn_of_le
  exists_prop614Extremal pCoreOf_le_of_isMaxTwoInvariantIn)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}

@[expose] def NormalizerRank (p : ℕ) (P : Sylow p G) (M B : Subgroup G) : Prop :=
  ∀ T : Subgroup G, IsMaxTwoInvariantIn B M T →
    Open.pRank p (P : Subgroup G) ≤ Open.pRank p (M ⊓ normalizer (T : Set G))

@[expose] def IsFInvariantIn (f : ℕ) (B X F : Subgroup G) : Prop :=
  F ≤ X ∧ IsPGroup f F ∧ B ≤ normalizer (F : Set G)

@[expose] def IsMaxFInvariantIn (f : ℕ) (B X F : Subgroup G) : Prop :=
  IsFInvariantIn f B X F ∧ ∀ F' : Subgroup G, IsFInvariantIn f B X F' → F ≤ F' → F' = F

theorem isMaxFInvariantIn_two_iff {B X F : Subgroup G} :
    IsMaxFInvariantIn 2 B X F ↔ IsMaxTwoInvariantIn B X F := Iff.rfl

theorem fusionIsSylowIn_of_isMax (hS : Situation G p P M) (hx : Point P M x) (hz : Central P z)
    (hcon : HasPrimeConstraint (G := M) p) {f : ℕ} (hf : f.Prime) (hfp : f ≠ p)
    {F : Subgroup G} (hF : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) M F) :
    fusionIsSylowIn f F (GLBPrimeCore p M) := by
  have hprime := hS.prime
  haveI : Fact f.Prime := ⟨hf⟩
  set B : Subgroup G := zpowers x ⊔ zpowers z
  set D : Subgroup G := GLBPrimeCore p M
  have hpl : SmallRankPlane p (P : Subgroup G) x z := plane_of_central hS hx hz
  have hB3 : IsPGroup p B := IsPGroup.of_card (n := 2) hpl.card_eq
  have hBM : B ≤ M := (sup_le (zpowers_le.mpr hx.mem) (zpowers_le.mpr hz.mem)).trans hS.sylow_le
  obtain ⟨⟨hFM, hF2, hBF⟩, hmax⟩ := hF
  have hF3 : Nat.Coprime p (Nat.card F) := by
    obtain ⟨k, hk⟩ := hF2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hprime hf).mpr hfp.symm)
  have hFD : F ≤ D :=
    CFSG.AGLEmbedding.signalizer_le_glbPrimeCore_of_contains hprime hS.ne_two hcon hB3 hBM
      (fun y _ hyB hord => hpl.mem_of_mem_centralizer y hyB (by
        rw [← hord]
        exact pow_orderOf_eq_one y)) hFM hF3 hBF
  have hD3 : ¬ p ∣ Nat.card D := (Nat.Prime.coprime_iff_not_dvd hprime).mp
    (CFSG.AGLEmbedding.glbPrimeCore_coprime p M)
  have hBD : B ≤ normalizer (D : Set G) :=
    hBM.trans (CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p M)
  obtain ⟨R, hRsyl, hFR, hBR⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    hprime hf hB3 hD3 hBD hFD hF2 hBF
  have hRF : R = F :=
    hmax R ⟨hRsyl.1.trans (CFSG.AGLEmbedding.glbPrimeCore_le p M), hRsyl.2.1, hBR⟩ hFR
  rwa [← hRF]

theorem exists_conj_le_normalizer_of_isMaxF (hS : Situation G p P M) (hx : Point P M x)
    (hz : Central P z) (hcon : HasPrimeConstraint (G := M) p) {f : ℕ} (hf : f.Prime)
    (hfp : f ≠ p) {F : Subgroup G} (hF : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) M F) :
    ∃ g : G, g ∈ M ∧
      (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ normalizer (F : Set G) := by
  have hprime := hS.prime
  haveI : Fact f.Prime := ⟨hf⟩
  set D : Subgroup G := GLBPrimeCore p M
  have hFD := fusionIsSylowIn_of_isMax hS hx hz hcon hf hfp hF
  have hD3 : ¬ p ∣ Nat.card D := (Nat.Prime.coprime_iff_not_dvd hprime).mp
    (CFSG.AGLEmbedding.glbPrimeCore_coprime p M)
  have hPD : (P : Subgroup G) ≤ normalizer (D : Set G) :=
    hS.sylow_le.trans (CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p M)
  have hbotf : IsPGroup f (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  have hbotp : IsPGroup p (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  have hPbot : (P : Subgroup G) ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  obtain ⟨S, hSsyl, -, hPS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    hprime hf P.isPGroup' hD3 hPD bot_le hbotf hPbot
  obtain ⟨c, hc, hFc⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows
    hprime hf hbotp hD3 bot_le hSsyl hFD bot_le bot_le
  refine ⟨c, CFSG.AGLEmbedding.glbPrimeCore_le p M (mem_inf.mp hc).1, ?_⟩
  rw [hFc, ← Subgroup.map_equiv_normalizer_eq]
  exact map_mono hPS

theorem exists_conj_le_normalizer_of_isMax (hS : Situation G p P M) (hx : Point P M x)
    (hz : Central P z) (hcon : HasPrimeConstraint (G := M) p) {T : Subgroup G}
    (hT : IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) M T) :
    ∃ g : G, g ∈ M ∧
      (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ normalizer (T : Set G) :=
  exists_conj_le_normalizer_of_isMaxF hS hx hz hcon Nat.prime_two (Ne.symm hS.ne_two) hT

theorem normalizerRank_of_constrained (hS : Situation G p P M) (hx : Point P M x)
    (hz : Central P z) (hcon : HasPrimeConstraint (G := M) p) :
    NormalizerRank p P M (zpowers x ⊔ zpowers z) := by
  intro T hT
  obtain ⟨g, hgM, hPg⟩ := exists_conj_le_normalizer_of_isMax hS hx hz hcon hT
  have hle : (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ M ⊓ normalizer (T : Set G) := by
    refine le_inf ?_ hPg
    rintro _ ⟨a, ha, rfl⟩
    exact M.mul_mem (M.mul_mem hgM (hS.sylow_le ha)) (M.inv_mem hgM)
  calc Open.pRank p (P : Subgroup G)
      = Open.pRank p ((P : Subgroup G).map (MulAut.conj g).toMonoidHom) :=
        (pRank_map_automorphism p hS.prime.one_lt _ _).symm
    _ ≤ Open.pRank p (M ⊓ normalizer (T : Set G)) :=
        CFSG.SectionRank.pRank_mono hS.prime.one_lt hle

private theorem exists_mem_normalizer_not_mem {q : ℕ} [Fact q.Prime] {Q R : Subgroup G}
    (hR : IsPGroup q R) (hQR : Q < R) : ∃ y ∈ R, y ∈ normalizer (Q : Set G) ∧ y ∉ Q := by
  have : Group.IsNilpotent R := hR.isNilpotent
  have hlt : Q.subgroupOf R < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hQR.ne ?_
    exact le_antisymm hQR.le (Subgroup.subgroupOf_eq_top.mp h)
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := R) _ hlt
  obtain ⟨y, hyN, hyQ⟩ := IsConcreteLE.exists_of_lt hgrow
  rw [← Subgroup.subgroupOf_normalizer_eq hQR.le, Subgroup.mem_subgroupOf] at hyN
  exact ⟨y, y.2, hyN, fun h => hyQ (Subgroup.mem_subgroupOf.mpr h)⟩

private theorem lt_inf_normalizer {q : ℕ} [Fact q.Prime] {S T : Subgroup G} (hT : IsPGroup q T)
    (hST : S < T) : S < T ⊓ normalizer (S : Set G) := by
  obtain ⟨y, hyT, hyN, hyS⟩ := exists_mem_normalizer_not_mem hT hST
  refine lt_of_le_of_ne (le_inf hST.le le_normalizer) fun h => hyS ?_
  rw [h]
  exact mem_inf.mpr ⟨hyT, hyN⟩

omit [Finite G] in
private theorem normalizer_le_normalizer_of_characteristic {S S₀ : Subgroup G} (h1 : S₀ ≤ S)
    (h3 : (S₀.subgroupOf S).Characteristic) :
    normalizer (S : Set G) ≤ normalizer (S₀ : Set G) := by
  have key : ∀ g ∈ normalizer (S : Set G), ∀ c ∈ S₀, g * c * g⁻¹ ∈ S₀ := by
    intro g hg c hc
    let φ : S ≃* S :=
      { toFun := fun s => ⟨g * s * g⁻¹, (mem_normalizer_iff.mp hg s).mp s.2⟩
        invFun := fun s => ⟨g⁻¹ * s * g, (mem_normalizer_iff''.mp hg s).mp s.2⟩
        left_inv := fun s => Subtype.ext (by simp [mul_assoc])
        right_inv := fun s => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun s t => Subtype.ext (by simp [mul_assoc]) }
    have hc' : (⟨c, h1 hc⟩ : S) ∈ S₀.subgroupOf S := hc
    exact characteristic_iff_map_le.mp h3 φ (mem_map_of_mem φ.toMonoidHom hc')
  intro g hg
  refine mem_normalizer_iff.mpr fun c => ⟨key g hg c, fun hc => ?_⟩
  simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hc

omit [Finite G] in
private theorem le_normalizer_inf_normalizer {B S T : Subgroup G}
    (hBT : B ≤ normalizer (T : Set G)) (hBS : B ≤ normalizer (S : Set G)) :
    B ≤ normalizer ((T ⊓ normalizer (S : Set G) : Subgroup G) : Set G) :=
  (le_inf hBT (hBS.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf

private theorem false_of_card_lt {M B H S H₁ R : Subgroup G} (h : Prop614Extremal M B H S)
    (hH₁ : IsTwoLocal H₁) (hBH₁ : B ≤ H₁) (hH₁M : ¬ H₁ ≤ M)
    (hR : IsTwoInvariantIn B (H₁ ⊓ M) R) (hcard : Nat.card S < Nat.card R) : False := by
  obtain ⟨S₁, hRS₁, hS₁⟩ := exists_isMaxTwoInvariantIn_of_le hR
  have hlt : Nat.card S < Nat.card S₁ := hcard.trans_le (Subgroup.card_le_of_le hRS₁)
  have hS₁1 : S₁ ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hlt
    have : 0 < Nat.card S := Nat.card_pos
    omega
  exact h.max H₁ S₁ ⟨hH₁, hBH₁, hH₁M, hS₁, hS₁1⟩ (Or.inl hlt)

theorem isMax_top_of_isMax (hS : Situation G p P M)
    (hnr : NormalizerRank p P M (zpowers x ⊔ zpowers z)) {T : Subgroup G}
    (hT : IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) M T) (hT1 : T ≠ ⊥) :
    IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) ⊤ T := by
  set B : Subgroup G := zpowers x ⊔ zpowers z
  have hT2 : IsPGroup 2 T := hT.1.2.1
  have hBT : B ≤ normalizer (T : Set G) := hT.1.2.2
  refine ⟨⟨le_top, hT2, hBT⟩, fun R hR hTR => ?_⟩
  obtain ⟨-, hR2, hBR⟩ := hR
  by_contra hne
  have hlt : T < R := lt_of_le_of_ne hTR (Ne.symm hne)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyR, hyN, hyT⟩ := exists_mem_normalizer_not_mem hR2 hlt
  set L : Subgroup G := normalizer (T : Set G)
  have hL : IsTwoLocal L := ⟨T, hT1, hT2, rfl⟩
  have hrank : 3 ≤ Open.pRank p (L ⊓ M) := by
    have h1 : Open.pRank p (P : Subgroup G) ≤ Open.pRank p (M ⊓ L) := hnr T hT
    rw [inf_comm] at h1
    have := hS.four_le_pRank
    omega
  have hLM : L ≤ M :=
    hS.toGlobal.d1 p hS.loc.beta P M hS.loc.maxLocal hS.loc.core L hL hrank
  have hBL : B ≤ normalizer (L : Set G) := hBT.trans le_normalizer
  have hR₁ : IsTwoInvariantIn B M (R ⊓ L) :=
    ⟨inf_le_right.trans hLM, hR2.to_le inf_le_left,
      (le_inf hBR hBL).trans inf_normalizer_le_normalizer_inf⟩
  have hR₁T := hT.2 (R ⊓ L) hR₁ (le_inf hTR le_normalizer)
  exact hyT (hR₁T ▸ mem_inf.mpr ⟨hyR, hyN⟩)

theorem isMax_self (hS : Situation G p P M)
    (hnr : NormalizerRank p P M (zpowers x ⊔ zpowers z)) {H S : Subgroup G}
    (h : Prop614Extremal M (zpowers x ⊔ zpowers z) H S) :
    IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) H S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hSHM, hS2, hBS⟩, hSmax⟩ := h.pair.isMax
  refine ⟨⟨hSHM.trans inf_le_left, hS2, hBS⟩, fun R hR hSR => ?_⟩
  by_contra hRS
  have hSltR : S < R := lt_of_le_of_ne hSR (Ne.symm hRS)
  obtain ⟨T, hST, hT⟩ := exists_isMaxTwoInvariantIn_of_le
    (⟨hSHM.trans inf_le_right, hS2, hBS⟩ : IsTwoInvariantIn (zpowers x ⊔ zpowers z) M S)
  have hT1 : T ≠ ⊥ := fun hT1 => h.pair.ne_bot (le_bot_iff.mp (hT1 ▸ hST))
  have hTG := isMax_top_of_isMax hS hnr hT hT1
  have hSltT : S < T := by
    refine lt_of_le_of_ne hST fun hST' => hRS ?_
    exact (hTG.2 R ⟨le_top, hR.2.1, hR.2.2⟩ (hST'.symm.le.trans hSR)).trans hST'.symm
  by_cases hH₁M : normalizer (S : Set G) ≤ M
  ·
    have hSltR₁ := lt_inf_normalizer hR.2.1 hSltR
    exact hSltR₁.ne (hSmax _ ⟨le_inf (inf_le_left.trans hR.1) (inf_le_right.trans hH₁M),
      hR.2.1.to_le inf_le_left, le_normalizer_inf_normalizer hR.2.2 hBS⟩ hSltR₁.le).symm
  ·
    exact false_of_card_lt h ⟨S, h.pair.ne_bot, hS2, rfl⟩ hBS hH₁M
      ⟨le_inf inf_le_right (inf_le_left.trans hT.1.1), hT.1.2.1.to_le inf_le_left,
        le_normalizer_inf_normalizer hT.1.2.2 hBS⟩
      (Subgroup.card_lt_of_lt (lt_inf_normalizer hT.1.2.1 hSltT))

theorem normalizer_le_of_characteristic (hS : Situation G p P M)
    (hnr : NormalizerRank p P M (zpowers x ⊔ zpowers z)) {H S : Subgroup G}
    (h : Prop614Extremal M (zpowers x ⊔ zpowers z) H S) {S₀ : Subgroup G} (h1 : S₀ ≤ S)
    (h2 : S₀ ≠ ⊥) (h3 : (S₀.subgroupOf S).Characteristic) :
    normalizer (S₀ : Set G) ≤ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hSHM, hS2, hBS⟩, -⟩ := h.pair.isMax
  have hNN := normalizer_le_normalizer_of_characteristic h1 h3
  have hH₁ : IsTwoLocal (normalizer (S₀ : Set G)) := ⟨S₀, h2, hS2.to_le h1, rfl⟩
  obtain ⟨T, hST, hT⟩ := exists_isMaxTwoInvariantIn_of_le
    (⟨hSHM.trans inf_le_right, hS2, hBS⟩ : IsTwoInvariantIn (zpowers x ⊔ zpowers z) M S)
  rcases hST.eq_or_lt with rfl | hSltT
  ·
    have hrank : 3 ≤ Open.pRank p (normalizer (S₀ : Set G) ⊓ M) := by
      have h1 := hnr S hT
      have h2 : M ⊓ normalizer (S : Set G) ≤ normalizer (S₀ : Set G) ⊓ M :=
        fun g hg => ⟨hNN hg.2, hg.1⟩
      have h3 := CFSG.SectionRank.pRank_mono hS.prime.one_lt h2
      have := hS.four_le_pRank
      omega
    exact hS.toGlobal.d1 p hS.loc.beta P M hS.loc.maxLocal hS.loc.core _ hH₁ hrank
  ·
    by_contra hH₁M
    exact false_of_card_lt h hH₁ (hBS.trans hNN) hH₁M
      ⟨le_inf inf_le_right (inf_le_left.trans hT.1.1), hT.1.2.1.to_le inf_le_left,
        le_normalizer_inf_normalizer hT.1.2.2 (hBS.trans hNN)⟩
      (Subgroup.card_lt_of_lt ((lt_inf_normalizer hT.1.2.1 hSltT).trans_le
        (inf_le_inf_left T hNN)))

theorem pRank_le_two (hS : Situation G p P M) (hx : Point P M x) (hz : Central P z)
    {H S : Subgroup G} (h : Prop614Pair M (zpowers x ⊔ zpowers z) H S) : Open.pRank p H ≤ 2 := by
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hpl := plane_of_central hS hx hz
  have hB3 : IsPGroup p ↥(zpowers x ⊔ zpowers z) := IsPGroup.of_card (n := 2) hpl.card_eq
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) := hpl.isIsolatedPlane.1
  have hB3' : IsPGroup p ↥((zpowers x ⊔ zpowers z).subgroupOf H) :=
    hB3.of_equiv (subgroupOfEquivOfLe h.le).symm
  obtain ⟨Q', hQ'⟩ := hB3'.exists_le_sylow
  set Q : Subgroup G := (Q' : Subgroup H).map H.subtype with hQ
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf p Q H := ⟨Q', rfl⟩
  have hBQ : zpowers x ⊔ zpowers z ≤ Q := by
    intro b hb
    have hbH : (⟨b, h.le hb⟩ : H) ∈ (zpowers x ⊔ zpowers z).subgroupOf H := hb
    exact ⟨⟨b, h.le hb⟩, hQ' hbH, rfl⟩
  have hQM : Q ≤ M :=
    le_of_plane_le hS hBP (centralizer_plane_le hS hz) hQsyl.isPGroup hBQ
  by_contra hbig
  push Not at hbig
  have hQrank : 3 ≤ Open.pRank p (H ⊓ M) := by
    have := pRank_eq_of_isSylowOf hprime hQsyl
    have h2 := CFSG.SectionRank.pRank_mono hprime.one_lt (le_inf hQsyl.le hQM)
    omega
  exact h.not_le (hS.toGlobal.d1 p hS.loc.beta P M hS.loc.maxLocal hS.loc.core H h.isTwoLocal
    hQrank)

structure Optimal {G : Type} [Group G] [Finite G] (p : ℕ) (M : Subgroup G) (x z : G)
    (H S : Subgroup G) : Prop where
  ext : Prop614Extremal M (zpowers x ⊔ zpowers z) H S
  eq_normalizer : H = normalizer (pCoreOf 2 H : Set G)
  maxInv : IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) H S
  core_le : pCoreOf 2 H ≤ S
  norm_le : ∀ S₀ : Subgroup G, pCoreOf 2 H < S₀ → S₀ ≤ S →
    S ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (S₀ : Set G) → normalizer (S₀ : Set G) ≤ M
  char_le : ∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → (S₀.subgroupOf S).Characteristic →
    normalizer (S₀ : Set G) ≤ M
  pRank_le : Open.pRank p H ≤ 2
  sylow_le : ∀ Q : Subgroup G, IsPGroup p Q → Q ≤ H → zpowers x ⊔ zpowers z ≤ Q → Q ≤ M

theorem exists_optimal (hS : Situation G p P M) (hx : Point P M x) (hz : Central P z)
    (hnr : NormalizerRank p P M (zpowers x ⊔ zpowers z))
    (hex : ∃ H S : Subgroup G, Prop614Pair M (zpowers x ⊔ zpowers z) H S) :
    ∃ H S : Subgroup G, Optimal p M x z H S := by
  obtain ⟨H, S, hext⟩ := exists_prop614Extremal hex
  have hmax := isMax_self hS hnr hext
  have hpl := plane_of_central hS hx hz
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) := hpl.isIsolatedPlane.1
  exact ⟨H, S, ⟨hext, hext.eq_normalizer_pCoreOf, hmax,
    pCoreOf_le_of_isMaxTwoInvariantIn hext.pair.le hmax,
    fun _ h1 h2 h3 => hext.normalizer_le_of_pCoreOf_lt h1 h2 h3,
    fun _ h1 h2 h3 => normalizer_le_of_characteristic hS hnr hext h1 h2 h3,
    pRank_le_two hS hx hz hext.pair,
    fun Q hQ _ hBQ => le_of_plane_le hS hBP (centralizer_plane_le hS hz) hQ hBQ⟩⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
