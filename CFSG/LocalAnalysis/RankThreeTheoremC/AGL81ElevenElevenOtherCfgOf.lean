module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenFiveAtOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenCfgOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111AltSixIrred
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111WeakCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenThreeCfg

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

@[expose] def NormIrredFrattini {M : Type*} [Group M] (S : Subgroup M) : Prop :=
  ∀ V : Subgroup M, V ≤ S → ¬ V ≤ (frattini ↥S).map S.subtype →
    Subgroup.normalizer (S : Set M) ≤ Subgroup.normalizer (V : Set M) → V = S

@[expose] def IsNineFourIndex (p : ℕ) : TauCeti.CFSGIndex → Prop
  | .cyclic _ _ => False
  | .alternating n _ => (p = 3 ∧ n = 6) ∨ (p = 5 ∧ n = 10)
  | .lie d =>
      (∃ q : TauCeti.PrimePower, q.p = p ∧ 2 ≤ q.exponent ∧ d.1 = .A 1 q) ∨
      (∃ q : TauCeti.PrimePower, q.p = p ∧ d.1 = .twistedA 2 q) ∨
      (p = 3 ∧ ∃ m : ℕ, d.1 = .reeG2 m) ∨
      (p = 3 ∧ ((∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .A 1 q) ∨
        (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d.1 = .A 2 q))) ∨
      (p = 5 ∧ (d.1 = .suzuki 2 ∨ d.1 = .tits))
  | .sporadic s => (p = 3 ∧ s = .M11) ∨ (p = 5 ∧ s = .McL) ∨ (p = 11 ∧ s = .J4)

@[expose] def NineFourListGroup (p : ℕ) (Y : Type*) [Group Y] : Prop :=
  IsSimpleGroup Y ∧ ∃ i : TauCeti.CFSGIndex, IsNineFourIndex p i ∧ Nonempty (Y ≃* i.Group)

@[expose] def KFactNineFourSylowIrred : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Z : Type) [Group Z] [Finite Z] (Y : Subgroup Z),
    NineFourListGroup p ↥Y → Open.pRank p Y = 2 →
    ∀ S : Sylow p ↥Y, NormIrredFrattini (S : Subgroup ↥Y)

variable (G) in
@[expose] def AGL81NineFourCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ¬ HasPrimeConstraint (G := H) p → 2 ≤ Open.pRank p K →
    Open.pRank p (d1PlusCore p H K) = 1 → NineFourListGroup p ↥K

variable (G) in
@[expose] def AGL81ElevenSevenFourL34 : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    p ∈ rankThreeSigmaA G → AGL81CfgData p P M H Q K → ¬ HasPrimeConstraint (G := H) p →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → (L.subgroupOf M).Normal →
    ¬ AGL81ElevenFiveOne p H K L → p = 3 → IsLinThreeFour K →
      ∀ b ∈ d1LiftX p H Q K, ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)

variable (G) in
@[expose] def AGL81TenFourteenThreeCfgGen : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    p ∣ Nat.card L → ∀ a : G, a ∈ M → orderOf a = p →
    ¬ Subgroup.centralizer ({a} : Set G) ≤ M →
    (∃ U : Subgroup G, U ≤ Subgroup.centralizer ({a} : Set G) ∧ IsAGLQ p M U) →
    ¬ ⁅Subgroup.zpowers a, L⁆ ≤ pCoreOf 2 L

variable (G) in
@[expose] def AGL81ElevenElevenParabolicGen : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → NineFourListGroup p ↥K → 2 ≤ Open.pRank p K →
    ¬ HasPrimeConstraint (G := H) p →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → (L.subgroupOf M).Normal →
    (∀ b ∈ d1LiftX p H Q K, ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)) →
    H ⊓ Subgroup.normalizer (d1LiftX p H Q K : Set G) ≤ M →
    (∀ V : Subgroup G, V ≤ d1LiftX p H Q K →
      ¬ V ≤ (frattini ↥(d1LiftX p H Q K)).map (d1LiftX p H Q K).subtype →
      H ⊓ Subgroup.normalizer (d1LiftX p H Q K : Set G) ≤ Subgroup.normalizer (V : Set G) →
      V = d1LiftX p H Q K) →
    ¬ 2 ∣ (jZero H L ⊔ pCoreOf 2 (H ⊓ L)).relIndex L →
    ⁅d1LiftX p H Q K, L⁆ ≤ pCoreOf 2 L

variable (G) in
@[expose] def AGL81ElevenElevenRankTwoCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    p ∈ rankThreeSigmaA G → AGL81CfgData p P M H Q K → ¬ HasPrimeConstraint (G := H) p →
    2 ≤ Open.pRank p K →
    ¬ (p = 3 ∧ IsAltTwoP 3 K) →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → (L.subgroupOf M).Normal →
    ¬ AGL81ElevenFiveOne p H K L →
      IsAGLQ p M (d1LiftX p H Q K) ∧ ⁅d1LiftX p H Q K, L⁆ ≤ pCoreOf 2 L

variable (G) in
@[expose] def AGL81ElevenElevenRankOneCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ¬ HasPrimeConstraint (G := H) p →
    Open.pRank p K ≤ 1 → 3 ≤ Open.pRank p H → ¬ (p = 3 ∧ IsAltTwoP 3 K) →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → (L.subgroupOf M).Normal →
    ¬ AGL81ElevenFiveOne p H K L →
      ∃ A : Subgroup G, A ≤ H ∧ IsAGLQ p M A ∧
        (∃ S : Sylow p K, (S : Subgroup K).map K.subtype =
          (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K) ∧
        ⁅A, L⁆ ≤ pCoreOf 2 L

theorem AGL81CfgData.sylowK_d1LiftX {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81CfgData p P M H Q K) :
    ∃ S : Sylow p K, (S : Subgroup K).map K.subtype =
      ((d1LiftX p H Q K).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K := by
  obtain ⟨S, hS'⟩ := hd.sylowK
  refine ⟨S, ?_⟩
  rw [map_d1LiftX, inf_assoc, inf_idem]
  exact hS'

theorem agl81ElevenElevenOtherCfg_of (h2 : AGL81ElevenElevenRankTwoCfg G)
    (h1 : AGL81ElevenElevenRankOneCfg G) : AGL81ElevenElevenOtherCfg G := by
  intro hS p P M H Q K hσ hd hnc hrk hA6 L hL hLn hno
  by_cases hK : 2 ≤ Open.pRank p K
  · obtain ⟨hQ, hAL⟩ := h2 hS p P M H Q K hσ hd hnc hK hA6 L hL hLn hno
    exact ⟨d1LiftX p H Q K, (d1LiftX_le p H Q K).trans hd.le_H, hQ, hd.sylowK_d1LiftX, hAL,
      fun _ => rfl⟩
  · push Not at hK
    obtain ⟨A, hAH, hAQ, hsyl, hAL⟩ := h1 hS p P M H Q K hd hnc (by omega) (hrk (by omega)) hA6
      L hL hLn hno
    exact ⟨A, hAH, hAQ, hsyl, hAL, fun h => absurd h (by omega)⟩

namespace OtherCfg

theorem mem_frattini_iff_of_equiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q) (x : P) :
    e x ∈ frattini Q ↔ x ∈ frattini P := by
  constructor
  · intro h
    have h1 := frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom)
      e.symm.surjective h
    simpa using h1
  · intro h
    exact frattini_le_comap_frattini_of_surjective (φ := e.toMonoidHom) e.surjective h

theorem eq_of_le_of_normIrredFrattini {X Y : Type*} [Group X] [Finite X] [Group Y] {p : ℕ}
    [Fact p.Prime] (f : X →* Y) (hf : Function.Surjective f) (hker : p.Coprime (Nat.card f.ker))
    {K : Subgroup Y} {S : Subgroup K} (hS : NormIrredFrattini S) {A V : Subgroup X}
    (hA : IsPGroup p A) (hSA : S.map K.subtype = A.map f) (hVA : V ≤ A)
    (hV1 : ¬ V ≤ (frattini ↥A).map A.subtype)
    (hVn : Subgroup.normalizer (A : Set X) ≤ Subgroup.normalizer (V : Set X)) : V = A := by
  have hAker : A ⊓ f.ker = ⊥ := AltSixIrred.inf_eq_bot_of_isPGroup_of_coprime hA hker
  have hinj : ∀ a ∈ A, f a = 1 → a = 1 := fun a ha h1 => by
    have hmem : a ∈ A ⊓ f.ker := ⟨ha, h1⟩
    rwa [hAker, Subgroup.mem_bot] at hmem
  have hfK : V.map f ≤ K := by
    refine (Subgroup.map_mono hVA).trans ?_
    rw [← hSA]
    exact Subgroup.map_subtype_le _
  set W : Subgroup K := (V.map f).subgroupOf K with hW
  have hWS : W ≤ S := by
    intro x hx
    have hx1 : (x : Y) ∈ S.map K.subtype := by
      rw [hSA]
      exact Subgroup.map_mono hVA hx
    obtain ⟨s, hs, hsx⟩ := hx1
    rwa [← Subtype.ext hsx]
  have hmemS : ∀ a : A, ∃ s : S, ((s : K) : Y) = f a := by
    intro a
    have h : f a ∈ S.map K.subtype := by
      rw [hSA]
      exact ⟨a, a.2, rfl⟩
    obtain ⟨s, hs, hsa⟩ := h
    exact ⟨⟨s, hs⟩, hsa⟩
  choose gfun hgfun using hmemS
  have hgext : ∀ (s s' : S), ((s : K) : Y) = ((s' : K) : Y) → s = s' := fun s s' h =>
    Subtype.ext (K.subtype_injective h)
  let g : A →* S :=
    { toFun := gfun
      map_one' := hgext _ _ (by rw [hgfun]; simp)
      map_mul' := fun a b => hgext _ _ (by
        rw [hgfun]
        simp only [Subgroup.coe_mul, hgfun, map_mul]) }
  have hg : ∀ a : A, ((g a : K) : Y) = f a := hgfun
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : f a = 1 := by rw [← hg, ha]; rfl
    exact Subtype.ext (hinj a a.2 h1)
  have hgsurj : Function.Surjective g := by
    intro s
    have h : ((s : K) : Y) ∈ A.map f := by
      rw [← hSA]
      exact ⟨s, s.2, rfl⟩
    obtain ⟨a, ha, hfa⟩ := h
    exact ⟨⟨a, ha⟩, hgext _ _ (by rw [hg]; exact hfa)⟩
  let e : A ≃* S := MulEquiv.ofBijective g ⟨hginj, hgsurj⟩
  have hW1 : ¬ W ≤ (frattini ↥S).map S.subtype := by
    intro hWΦ
    apply hV1
    intro v hv
    have hvA : v ∈ A := hVA hv
    have hk : (⟨f v, hfK ⟨v, hv, rfl⟩⟩ : K) ∈ W := ⟨v, hv, rfl⟩
    obtain ⟨s, hsΦ, hsk⟩ := hWΦ hk
    have hs : s = g ⟨v, hvA⟩ := hgext _ _ (by
      rw [hg]
      exact congrArg (fun k : K => (k : Y)) hsk)
    have hmem : (⟨v, hvA⟩ : A) ∈ frattini ↥A := by
      rw [← mem_frattini_iff_of_equiv e ⟨v, hvA⟩]
      exact hs ▸ hsΦ
    exact ⟨⟨v, hvA⟩, hmem, rfl⟩
  have hSsub : (S.map K.subtype).subgroupOf K = S :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hWn : Subgroup.normalizer (S : Set K) ≤ Subgroup.normalizer (W : Set K) := by
    intro k hk
    have hk0 : k ∈ (Subgroup.normalizer ((S.map K.subtype : Subgroup Y) : Set Y)).subgroupOf K := by
      rw [Subgroup.subgroupOf_normalizer_eq (Subgroup.map_subtype_le _), hSsub]
      exact hk
    rw [hSA] at hk0
    obtain ⟨n, hn, hnk⟩ := AltSixIrred.normalizer_map_le_map_normalizer f hf hker hA hk0
    have hn2 : f n ∈ Subgroup.normalizer ((V.map f : Subgroup Y) : Set Y) :=
      Subgroup.le_normalizer_map f ⟨n, hVn hn, rfl⟩
    rw [hnk] at hn2
    have hk2 : k ∈ (Subgroup.normalizer ((V.map f : Subgroup Y) : Set Y)).subgroupOf K := hn2
    rwa [Subgroup.subgroupOf_normalizer_eq hfK] at hk2
  have hWeq : W = S := hS W hWS hW1 hWn
  have hVf : V.map f = A.map f := by
    rw [← hSA, ← hWeq, hW, Subgroup.map_subgroupOf_eq_of_le hfK]
  refine le_antisymm hVA fun a ha => ?_
  obtain ⟨v, hv, hva⟩ : f a ∈ V.map f := by
    rw [hVf]
    exact ⟨a, ha, rfl⟩
  have hva' : v = a := inv_mul_eq_one.mp (hinj _ (A.mul_mem (A.inv_mem (hVA hv)) ha)
    (by rw [map_mul, map_inv, hva, inv_mul_cancel]))
  rwa [← hva']

end OtherCfg

theorem eq_of_le_of_normIrredFrattini_H {p : ℕ} [Fact p.Prime] {H A V : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (S : Sylow p K)
    (hS : NormIrredFrattini (S : Subgroup K)) (hAH : A ≤ H) (hA3 : IsPGroup p A)
    (hAsyl : (S : Subgroup K).map K.subtype =
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
    (hVA : V ≤ A) (hV1 : ¬ V ≤ (frattini ↥A).map A.subtype)
    (hVn : H ⊓ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (V : Set G)) : V = A := by
  have hVH : V ≤ H := hVA.trans hAH
  have hVn' : Subgroup.normalizer ((A.subgroupOf H : Subgroup H) : Set H) ≤
      Subgroup.normalizer ((V.subgroupOf H : Subgroup H) : Set H) := by
    intro n hn
    have h1 : n ∈ (Subgroup.normalizer (A : Set G)).subgroupOf H := by
      rw [Subgroup.subgroupOf_normalizer_eq hAH]
      exact hn
    have h2 : n ∈ (Subgroup.normalizer (V : Set G)).subgroupOf H := hVn ⟨n.2, h1⟩
    rwa [Subgroup.subgroupOf_normalizer_eq hVH] at h2
  have hV1' : ¬ V.subgroupOf H ≤ (frattini ↥(A.subgroupOf H)).map (A.subgroupOf H).subtype := by
    intro hΦ
    apply hV1
    intro v hv
    have hvH : v ∈ H := hVH hv
    have hv' : (⟨v, hvH⟩ : H) ∈ V.subgroupOf H := hv
    obtain ⟨s, hsΦ, hsv⟩ := hΦ hv'
    have hes : (Subgroup.subgroupOfEquivOfLe hAH) s = ⟨v, hVA hv⟩ :=
      Subtype.ext (congrArg (fun h : H => (h : G)) hsv)
    have hmem : (⟨v, hVA hv⟩ : A) ∈ frattini ↥A := by
      rw [← hes]
      exact (OtherCfg.mem_frattini_iff_of_equiv (Subgroup.subgroupOfEquivOfLe hAH) s).mpr hsΦ
    exact ⟨⟨v, hVA hv⟩, hmem, rfl⟩
  have hker : Nat.Coprime p
      (Nat.card (QuotientGroup.mk' (primeComplementCore (G := H) p)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact primeComplementCore_coprime p
  have hVA' := OtherCfg.eq_of_le_of_normIrredFrattini
    (QuotientGroup.mk' (primeComplementCore (G := H) p)) (QuotientGroup.mk'_surjective _) hker hS
    hA3.comap_subtype hAsyl (fun x hx => hVA hx : V.subgroupOf H ≤ A.subgroupOf H) hV1' hVn'
  have := Subgroup.subgroupOf_inj.mp hVA'
  rwa [inf_of_le_left hVH, inf_of_le_left hAH] at this

namespace OtherCfg

theorem exists_centralizing_of_dvd {p : ℕ} [Fact p.Prime] {A V : Subgroup G} (hA : IsPGroup p A)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hp : p ∣ Nat.card V) :
    ∃ y ∈ V, orderOf y = p ∧ ∀ a ∈ A, a * y = y * a := by
  have hpp : p.Prime := Fact.out
  set W := A ⊔ V with hW
  have hWV : W ≤ Subgroup.normalizer (V : Set G) := sup_le hAV Subgroup.le_normalizer
  obtain ⟨P, hP⟩ := (hA.comap_subtype (K := W)).exists_le_sylow
  set P' : Subgroup G := (P : Subgroup W).map W.subtype with hP'
  have hP'W : P' ≤ W := Subgroup.map_subtype_le _
  have hAP' : A ≤ P' := fun a ha => ⟨⟨a, (le_sup_left : A ≤ W) ha⟩, hP ha, rfl⟩
  have hP'3 : IsPGroup p P' := P.isPGroup'.map _
  have hP'V : P' ≤ Subgroup.normalizer (V : Set G) := hP'W.trans hWV
  have hne : P' ⊓ V ≠ ⊥ := by
    intro hb
    have hprod := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer V P' hP'V
      (by rw [disjoint_iff, inf_comm]; exact hb)
    have hle : P' ⊔ V ≤ W := sup_le hP'W le_sup_right
    have hri : P'.relIndex (P' ⊔ V) = Nat.card V := by
      have h1 := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) P' (P' ⊔ V) bot_le le_sup_left
      rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at h1
      have hpos : 0 < Nat.card P' := Nat.card_pos
      refine Nat.eq_of_mul_eq_mul_left hpos ?_
      rw [h1, sup_comm, hprod, mul_comm]
    have hdvd : P'.relIndex (P' ⊔ V) ∣ P'.relIndex W :=
      Dvd.intro _ (Subgroup.relIndex_mul_relIndex P' (P' ⊔ V) W le_sup_left hle)
    have hPi : P'.relIndex W = (P : Subgroup W).index := by
      show (P'.comap W.subtype).index = _
      rw [hP', Subgroup.comap_map_eq_self_of_injective W.subtype_injective]
    exact P.not_dvd_index (hPi ▸ (hri ▸ hp).trans hdvd)
  haveI : Group.IsNilpotent P' := hP'3.isNilpotent
  set N : Subgroup P' := (P' ⊓ V).subgroupOf P' with hN
  haveI hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hnV : (n : G) ∈ V := hn.2
    refine ⟨P'.mul_mem (P'.mul_mem g.2 n.2) (P'.inv_mem g.2), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hP'V g.2) n).mp hnV
  have hN1 : N ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.1⟩ : P') ∈ N := hx
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
  obtain ⟨⟨z, hzN, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hN1)
  set y₀ : G := ((z : P') : G) with hy₀
  have hy₀V : y₀ ∈ V := hzN.2
  have hy₀1 : y₀ ≠ 1 := by
    intro h
    exact hz1 (Subtype.ext (Subtype.ext h))
  have hy₀c : ∀ a ∈ A, a * y₀ = y₀ * a := by
    intro a ha
    have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hzZ ⟨a, hAP' ha⟩)
    simp only [Subgroup.coe_mul] at this
    exact this
  obtain ⟨n, hn⟩ := hP'3 (z : P')
  have hord : orderOf y₀ ∣ p ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hn
    simpa using this
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hpp).mp hord
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hy₀1 (orderOf_eq_one_iff.mp (by simpa using hk))
  refine ⟨y₀ ^ (p ^ (k - 1)), V.pow_mem hy₀V _, ?_, fun a ha => ?_⟩
  · rw [orderOf_pow' _ (pow_ne_zero _ hpp.ne_zero), hk,
      Nat.gcd_eq_right (pow_dvd_pow p (Nat.sub_le k 1)), Nat.pow_div (Nat.sub_le k 1) hpp.pos,
      show k - (k - 1) = 1 by omega, pow_one]
  · exact (Commute.pow_right (hy₀c a ha) _).eq

theorem isElemAbelian_sup_zpowers_gen {q : ℕ} (hq : q.Prime) {E : Subgroup G}
    (hE : IsElemAbelian q E) {z : G} (hzq : z ^ q = 1) (hzE : z ∉ E)
    (hz : ∀ e ∈ E, e * z = z * e) :
    IsElemAbelian q (E ⊔ Subgroup.zpowers z) ∧
      Nat.card (E ⊔ Subgroup.zpowers z : Subgroup G) = Nat.card E * q := by
  have : Fact q.Prime := ⟨hq⟩
  have hz1 : z ≠ 1 := fun h => hzE (h ▸ E.one_mem)
  have hord : orderOf z = q := orderOf_eq_prime hzq hz1
  have hcardz : Nat.card (Subgroup.zpowers z) = q := by rw [Nat.card_zpowers, hord]
  have hnorm : Subgroup.zpowers z ≤ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer (E : Set G) (Subgroup.mem_centralizer_iff.mpr hz)
  have hdisj : Disjoint E (Subgroup.zpowers z) := by
    rw [Subgroup.disjoint_def]
    intro x hxE hxz
    have : Fact (Nat.card (Subgroup.zpowers z)).Prime := ⟨by rw [hcardz]; exact hq⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (E.subgroupOf (Subgroup.zpowers z)) with h | h
    · have hx : (⟨x, hxz⟩ : Subgroup.zpowers z) ∈ E.subgroupOf (Subgroup.zpowers z) := hxE
      rw [h] at hx
      exact congrArg Subtype.val (Subgroup.mem_bot.1 hx)
    · exfalso
      have hf : (⟨z, Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z) ∈
          E.subgroupOf (Subgroup.zpowers z) := by
        rw [h]
        trivial
      exact hzE hf
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E
    (Subgroup.zpowers z) hnorm hdisj
  have hEab := hE.1
  have hdec : ∀ x ∈ E ⊔ Subgroup.zpowers z, ∃ e ∈ E, ∃ k : ℤ, x = e * z ^ k := by
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left E _ hnorm] at hx
    obtain ⟨e, he, y, hy, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨e, he, k, rfl⟩
  have hcomm : ∀ e ∈ E, ∀ k : ℤ, Commute e (z ^ k) := fun e he k =>
    Commute.zpow_right (hz e he) k
  refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, by rw [hcard, hcardz]⟩
  · obtain ⟨e₁, he₁, k₁, h₁⟩ := hdec x x.2
    obtain ⟨e₂, he₂, k₂, h₂⟩ := hdec y y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [h₁, h₂]
    have h12 : e₁ * e₂ = e₂ * e₁ :=
      congrArg Subtype.val (isMulCommutative_iff.mp hEab (⟨e₁, he₁⟩ : E) ⟨e₂, he₂⟩)
    calc e₁ * z ^ k₁ * (e₂ * z ^ k₂) = e₁ * (z ^ k₁ * e₂) * z ^ k₂ := by group
      _ = e₁ * (e₂ * z ^ k₁) * z ^ k₂ := by rw [(hcomm e₂ he₂ k₁).eq]
      _ = (e₁ * e₂) * (z ^ k₁ * z ^ k₂) := by group
      _ = (e₂ * e₁) * (z ^ k₂ * z ^ k₁) := by rw [h12, ← zpow_add, ← zpow_add, add_comm]
      _ = e₂ * (e₁ * z ^ k₂) * z ^ k₁ := by group
      _ = e₂ * (z ^ k₂ * e₁) * z ^ k₁ := by rw [(hcomm e₁ he₁ k₂).eq]
      _ = e₂ * z ^ k₂ * (e₁ * z ^ k₁) := by group
  · obtain ⟨e, he, k, rfl⟩ := hdec x hx
    rw [(hcomm e he k).mul_pow, hE.2 e he, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hzq, one_zpow]

theorem pRank_eq_of_sylow_equiv {p : ℕ} [Fact p.Prime] {Z : Type} [Group Z] [Finite Z]
    {K : Subgroup Z} {A : Subgroup G} (S : Sylow p K) (e : ↥A ≃* ↥(S : Subgroup K)) :
    Open.pRank p A = Open.pRank p K := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  calc Open.pRank p A = Open.pRank p (⊤ : Subgroup ↥A) :=
        CFSG.SectionRank.pRank_eq_pRank_top_subgroup A
    _ = Open.pRank p (⊤ : Subgroup ↥(S : Subgroup K)) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 e
    _ = Open.pRank p (S : Subgroup K) := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup _).symm
    _ = Open.pRank p (⊤ : Subgroup K) := (CFSG.SectionRank.pRank_sylow S).1
    _ = Open.pRank p K := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup K).symm

theorem d1LiftX_facts_gen {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81CfgData p P M H Q K)
    (hZ : ∀ k : K, (∀ k' : K, k * k' = k' * k) → k = 1) :
    d1LiftX p H Q K ⊓ d1PlusCore p H K = ⊥ ∧ ∃ S : Sylow p K,
      (S : Subgroup K).map K.subtype =
        ((d1LiftX p H Q K).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ∧
      Nonempty (↥(d1LiftX p H Q K) ≃* ↥(S : Subgroup K)) := by
  set O := primeComplementCore (G := H) p with hOdef
  set π := QuotientGroup.mk' O with hπ
  set A := d1LiftX p H Q K with hA
  have hAR : A ≤ Q := d1LiftX_le p H Q K
  have hAH : A ≤ H := hAR.trans hd.le_H
  set A' := A.subgroupOf H with hA'
  have hA'p : IsPGroup p A' := (hd.base.2.1.to_le hAR).comap_subtype
  have hAO : A' ⊓ O = ⊥ := by
    obtain ⟨n, hn⟩ := hA'p.exists_card_eq
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hn]
    exact (primeComplementCore_coprime (G := H) p).pow_left n
  have hinj : ∀ a ∈ A', π a = 1 → a = 1 := fun a ha h1 => by
    have hO : a ∈ O := (QuotientGroup.eq_one_iff a).mp h1
    have : a ∈ A' ⊓ O := ⟨ha, hO⟩
    rwa [hAO, Subgroup.mem_bot] at this
  refine ⟨?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨⟨a, ⟨haR, haK⟩, rfl⟩, ⟨b, hbC, hba⟩⟩
    have hab : b = a := Subtype.ext hba
    subst hab
    have hz : π b = 1 := by
      have := hZ ⟨π b, haK⟩ fun k' =>
        Subtype.ext ((Subgroup.mem_centralizer_iff.mp hbC) k' k'.2).symm
      exact congrArg Subtype.val this
    have hbA : b ∈ A' := by
      show (b : G) ∈ A
      exact ⟨b, ⟨haR, haK⟩, rfl⟩
    rw [Subgroup.mem_bot, hinj b hbA hz]
    rfl
  · obtain ⟨S, hS⟩ := hd.sylowK
    have hmap : A'.map π = (S : Subgroup K).map K.subtype := by
      rw [hS, hA', hA, map_d1LiftX]
    set φ : A' →* H ⧸ O := π.comp A'.subtype with hφ
    have hφinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro a ha
      exact Subtype.ext (hinj a a.2 ha)
    have hφr : φ.range = (S : Subgroup K).map K.subtype := by
      rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype, hmap]
    let f : A ≃* S :=
      ((Subgroup.subgroupOfEquivOfLe hAH).symm.trans (MonoidHom.ofInjective hφinj)).trans
        ((MulEquiv.subgroupCongr hφr).trans
          (Subgroup.equivMapOfInjective (S : Subgroup K) K.subtype K.subtype_injective).symm)
    exact ⟨S, hmap.symm, ⟨f⟩⟩

end OtherCfg

theorem agl81ElevenElevenRankTwoCfg_of (h7 : AGL81ElevenSevenCfg G)
    (h7L : AGL81ElevenSevenFourL34 G) (hX : AGL81NineThreeXCfg G) (h94 : AGL81NineFourCfg G)
    (hKI : KFactNineFourSylowIrred) (hCGT : AschbacherLocalCGTBlock) (hD2 : NoXBlockFor G)
    (h1033 : AGL81TenThreeThreeCfg G) (hN1 : TenThreeThree.AGL81ElevenThreeInspectionCfg G)
    (h1031 : AGL81TenThreeOneAt G) (h10C : AGL81TenOneCZero G) (h91 : AGL81TenNineOneCfg G)
    (hPar : AGL81ElevenElevenParabolicGen G) (h1014 : AGL81TenFourteenThreeCfgGen G) :
    AGL81ElevenElevenRankTwoCfg G := by
  intro hS p P M H Q K hσ hd hnc hrk hA6 L hL hLn hno
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hp : p.Prime := hesc.prime
  have hp2 : p ≠ 2 := hesc.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hcore : GLBWeakCore p (P : Subgroup G) ≤ M := hesc.weakCore_le
  set X := d1PlusCore p H K with hXdef
  set A := d1LiftX p H Q K with hAdef
  have hAQ : A ≤ Q := d1LiftX_le p H Q K
  have hAH : A ≤ H := hAQ.trans hd.le_H
  have hAM : A ≤ M := hAQ.trans hd.base.1
  have hA3 : IsPGroup p A := hd.base.2.1.to_le hAQ
  have hXM : X ≤ M := hX hS p P M H Q K hd
  have hXH : X ≤ H := Subgroup.map_subtype_le _
  have hMn : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.le).mp hLn
  obtain ⟨-, hXr, hJ0, hAJ⟩ := h7 hS p P M H Q K hσ hd hnc L hL hLn hno
  have hAJ' : ∀ b ∈ A, ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L) := by
    rcases hJ0 with hJX | ⟨hp3, hL34⟩
    · exact hAJ hJX
    · exact h7L hS p P M H Q K hσ hd hnc L hL hLn hno hp3 hL34
  have hlist : NineFourListGroup p ↥K := h94 hS p P M H Q K hd hnc hrk hXr
  have hZ : ∀ k : K, (∀ k' : K, k * k' = k' * k) → k = 1 := by
    intro k hk
    by_contra hk1
    have hcen : Subgroup.center ↥K = ⊤ := by
      haveI := hlist.1
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
      · exfalso
        apply hk1
        have : k ∈ Subgroup.center ↥K := Subgroup.mem_center_iff.mpr fun g => (hk g).symm
        rw [h] at this
        exact Subgroup.mem_bot.mp this
      · exact h
    letI : CommGroup ↥K :=
      { (inferInstance : Group ↥K) with
        mul_comm := fun a b => by
          have := Subgroup.mem_center_iff.mp (hcen ▸ Subgroup.mem_top a) b
          exact this.symm }
    haveI := hlist.1
    have hprime := IsSimpleGroup.prime_card (α := ↥K)
    obtain ⟨E, hEK, hE, hEc⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank hp hrk
    have hdvd : p ^ 2 ∣ Nat.card K := hEc ▸ Subgroup.card_dvd_of_le hEK
    have h1 : p ∣ Nat.card K := (dvd_pow_self p two_ne_zero).trans hdvd
    rcases (Nat.Prime.eq_one_or_self_of_dvd hprime p h1) with h | h
    · exact hp.ne_one h
    · rw [← h] at hdvd
      have := Nat.le_of_dvd hp.pos hdvd
      nlinarith [hp.two_le]
  obtain ⟨hAX, S, hSA, ⟨e⟩⟩ := OtherCfg.d1LiftX_facts_gen hd hZ
  have hrkA : Open.pRank p A = Open.pRank p K := OtherCfg.pRank_eq_of_sylow_equiv S e
  have hA2 : 2 ≤ Open.pRank p A := hrkA ▸ hrk
  have h3X : p ∣ Nat.card X := by
    obtain ⟨E₀, hE₀X, -, hE₀c⟩ := pRank_attained p hp X
    rw [hXr, pow_one] at hE₀c
    exact hE₀c ▸ Subgroup.card_dvd_of_le hE₀X
  have hAXn : A ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_d1PlusCore_of_map_le hAH (by rw [hAdef, map_d1LiftX]; exact inf_le_right)
  obtain ⟨z, hzX, hz3, hzc⟩ := OtherCfg.exists_centralizing_of_dvd hA3 hAXn h3X
  have hzA : z ∉ A := fun hzA => by
    have : z ∈ A ⊓ X := ⟨hzA, hzX⟩
    rw [hAX, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hz3
    exact hp.ne_one hz3.symm
  have hzM : z ∈ M := hXM hzX
  have hzH : z ∈ H := hXH hzX
  have hz3' : z ^ p = 1 := hz3 ▸ pow_orderOf_eq_one z
  have hrkA2 : Open.pRank p A ≤ 2 := by
    obtain ⟨E₀, hE₀A, hE₀, hE₀c⟩ := pRank_attained p hp A
    have hzE₀ : z ∉ E₀ := fun h => hzA (hE₀A h)
    obtain ⟨hEz, hEzc⟩ := OtherCfg.isElemAbelian_sup_zpowers_gen hp hE₀ hz3' hzE₀
      (fun e he => hzc e (hE₀A he))
    have hle : E₀ ⊔ Subgroup.zpowers z ≤ H ⊓ M :=
      sup_le (le_inf (hE₀A.trans hAH) (hE₀A.trans hAM))
        ((Subgroup.zpowers_le).mpr ⟨hzH, hzM⟩)
    have h3 := CFSG.SectionRank.le_pRank hp.one_lt hle hEz
      (k := Open.pRank p A + 1) (by rw [hEzc, hE₀c, pow_succ])
    have h4 := pRank_inf_le_three_of_setting hS hp hp2 hd.maxH.1 M
    omega
  have hrkK : Open.pRank p K = 2 := by omega
  have hirr0 : NormIrredFrattini (S : Subgroup ↥K) :=
    hKI p hp hp2 (H ⧸ primeComplementCore (G := H) p) K hlist hrkK S
  have hirr : ∀ V : Subgroup G, V ≤ A → ¬ V ≤ (frattini ↥A).map A.subtype →
      H ⊓ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (V : Set G) → V = A :=
    fun V hVA hV hVn => eq_of_le_of_normIrredFrattini_H S hirr0 hAH hA3 hSA hVA hV hVn
  have hNA : Subgroup.normalizer (A : Set G) ≤ M :=
    normalizer_le_of_central hcore hAM hA3 hA2 hzM hz3 hzA fun a ha => (hzc a ha).symm
  have hAL : ⁅A, L⁆ ≤ pCoreOf 2 L := by
    rcases h1033 hS p P M H Q K hd L hL hLn A (le_inf hAH hAM) hA3 hAJ' with hc | hodd
    · rw [Subgroup.commutator_le]
      intro a ha l hl
      rw [commutatorElement_def]
      refine inf_pCoreOf_le hL.le ⟨?_, hc a ha l hl⟩
      have hal : a * l * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hMn (hAM ha)) l).mp hl
      exact L.mul_mem hal (L.inv_mem hl)
    · exact hPar hS p P M H Q K hd hlist hrk hnc L hL hLn hAJ' (inf_le_right.trans hNA) hirr hodd
  have hpL : p ∣ Nat.card L := by
    have hQS : Q ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      hd.le_H.trans (localGroup_le_normalizer_pCoreOf 2 H)
    obtain ⟨R, hSR, hR⟩ := TwoRest3A6.exists_isMaxInvariantTwoIn_ge
      (hd.b3 _ (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
        (RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H) hQS)
      (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H) hQS
    have hR1 : R ≠ ⊥ := fun h0 => pCoreOf_two_ne_bot hd.maxH.1 (le_bot_iff.mp (h0 ▸ hSR))
    have hpJ : p ∣ Nat.card (jOne H L) := by
      by_cases hp3 : p = 3
      · subst hp3
        obtain ⟨I₀, hI₀⟩ := h10C hS 3 P M H Q K hd L hL (h91 hS 3 P M H Q K hd L hL)
        exact (h1031 hS 3 P M H Q K hd L hL I₀ hI₀).trans
          (Subgroup.card_dvd_of_le (IsCZeroMember.oUpperTwo_le_jOne hI₀))
      · exact hd.prime_dvd_card_jOne_of_ne_three hS hCGT hD2 h1033 hN1 hp3 hXM hL hLn hR hR1
    exact hpJ.trans (Subgroup.card_dvd_of_le
      ((jOne_le_jZero H L).trans ((jZero_le H L).trans inf_le_right)))
  obtain ⟨E, hEA, hEe, hEc⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank hp hA2
  have hzE : z ∉ E := fun h => hzA (hEA h)
  obtain ⟨hEz, hEzc⟩ := OtherCfg.isElemAbelian_sup_zpowers_gen hp hEe hz3' hzE
    (fun e he => hzc e (hEA he))
  have hEQ : IsAGLQ p M (E ⊔ Subgroup.zpowers z) :=
    ⟨sup_le (hEA.trans hAM) ((Subgroup.zpowers_le).mpr hzM),
      CFSG.Open.IsElemAbelian.isPGroup hEz,
      Or.inl (by
        rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
        exact CFSG.SectionRank.le_pRank hp.one_lt le_rfl hEz (by rw [hEzc, hEc]; ring))⟩
  have hcent : ∀ a ∈ E, a ≠ 1 → Subgroup.centralizer ({a} : Set G) ≤ M := by
    intro a ha ha1
    by_contra hCM
    have ha3 : orderOf a = p := orderOf_eq_prime (hEe.2 a ha) ha1
    refine h1014 hS p P M H Q K hd L hL hpL a (hAM (hEA ha)) ha3 hCM ⟨E ⊔ Subgroup.zpowers z, ?_, hEQ⟩
      ((Subgroup.commutator_mono ((Subgroup.zpowers_le).mpr (hEA ha)) le_rfl).trans hAL)
    refine sup_le (fun b hb => Subgroup.mem_centralizer_iff.mpr ?_) ?_
    · rintro x rfl
      exact congrArg Subtype.val (isMulCommutative_iff.mp hEe.1 ⟨x, ha⟩ ⟨b, hb⟩)
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      rintro x rfl
      exact hzc x (hEA ha)
  exact ⟨isAGLQ_of_centralizers hcore hAM hA3 hEA hEe hEc hz3 hzE
    (fun e he => (hzc e (hEA he)).symm) hcent, hAL⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
