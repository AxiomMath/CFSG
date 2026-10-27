module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeKPart
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeAltSix
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeSymThree
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNormalizesNoSU
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LnTwoCentralizerLift
import CFSG.LocalAnalysis.AGLEmbedding.SUPairModel
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.Quasithin Subgroup
open CFSG.ComponentClassification.AS76b (oUpperTwo)

open scoped commutatorElement

namespace TwelveNotLe

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_pCoreOf_of_not_mem_normalizer_of_coprime {M L : Subgroup G}
    (hL : IsTwoPrimeComponent M L) {y : G} (hyM : y ∈ M)
    (hyL : y ∉ Subgroup.normalizer (L : Set G)) {x : G} (hxL : x ∈ L) {k : ℕ}
    (hxk : x ^ 3 ^ k = 1) (hcop : Nat.Coprime 3 (orderOf (x⁻¹ * (y * x * y⁻¹)))) :
    ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  set L' := L.map (MulAut.conj y).toMonoidHom with hL'def
  have hne : L ≠ L' := fun h => hyL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hL' : IsTwoPrimeComponent M L' := hL.map_conj hyM
  have hc1 := hL.commutator_le hL' hne
  have hc2 := hL'.commutator_le hL hne.symm
  have hjL' : y * x * y⁻¹ ∈ L' := ⟨x, hxL, by simp [MulAut.conj_apply]⟩
  set n := orderOf (x⁻¹ * (y * x * y⁻¹)) with hn
  have hcn : (x⁻¹ * (y * x * y⁻¹)) ^ n = 1 := pow_orderOf_eq_one _
  have hn' : Nat.Coprime (3 ^ k) n := Nat.Coprime.pow_left k hcop
  set q := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hq
  have hq1 : ∀ z : M, (z : G) ∈ pCoreOf 2 M → q z = 1 := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hz
    have : w = z := Subtype.ext hwz
    exact (QuotientGroup.eq_one_iff z).mpr (this ▸ hw)
  have hq1' : ∀ z : M, q z = 1 → (z : G) ∈ pCoreOf 2 M := fun z hz =>
    ⟨z, (QuotientGroup.eq_one_iff z).mp hz, rfl⟩
  have hxM : x ∈ M := hL.le hxL
  have hjM : y * x * y⁻¹ ∈ M := hL'.le hjL'
  set x' : M := ⟨x, hxM⟩
  set j' : M := ⟨y * x * y⁻¹, hjM⟩
  have hxj : q x' * q j' = q j' * q x' := by
    have h := hq1 ⁅x', j'⁆ (hc1 (Subgroup.commutator_mem_commutator hxL hjL'))
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  have hx3 : q x' ^ 3 ^ k = 1 := by
    rw [← map_pow, show x' ^ 3 ^ k = 1 from Subtype.ext hxk, map_one]
  have hj3 : q j' ^ 3 ^ k = 1 := by
    rw [← map_pow, show j' ^ 3 ^ k = 1 from Subtype.ext (by simp [j', conj_pow, hxk]), map_one]
  have hc3 : ((q x')⁻¹ * q j') ^ 3 ^ k = 1 := by
    rw [(Commute.inv_left (Commute.symm hxj).symm).mul_pow, inv_pow, hx3, hj3, inv_one, one_mul]
  have hcn' : ((q x')⁻¹ * q j') ^ n = 1 := by
    rw [← map_inv, ← map_mul, ← map_pow,
      show (x'⁻¹ * j') ^ n = 1 from Subtype.ext (by simpa using hcn), map_one]
  have hc1' : (q x')⁻¹ * q j' = 1 := by
    have h := (pow_gcd_eq_one (a := (q x')⁻¹ * q j')).mpr ⟨hc3, hcn'⟩
    rwa [Nat.Coprime.gcd_eq_one hn', pow_one] at h
  have hxj' : q x' = q j' := inv_mul_eq_one.mp hc1'
  intro l hl
  have hlM : l ∈ M := hL.le hl
  set l' : M := ⟨l, hlM⟩
  have hjl := hq1 ⁅j', l'⁆ (hc2 (Subgroup.commutator_mem_commutator hjL' hl))
  rw [map_commutatorElement, ← hxj', ← map_commutatorElement] at hjl
  have hxl : x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 M := hq1' _ hjl
  rw [← hL.inf_twoCore]
  exact ⟨L.mul_mem (L.mul_mem (L.mul_mem hxL hl) (L.inv_mem hxL)) (L.inv_mem hl), hxl⟩

variable {P : Sylow 3 G} {M H Q : Subgroup G}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem mem_normalizer_of_xPart (hA6 : IsAltTwoP 3 K) {L : Subgroup G}
    (hL : IsTwoPrimeComponent M L) {I₁ : Subgroup G} (hI₁ : I₁ ∈ cZero (H ⊓ L))
    (hX : oUpperTwo I₁ ≤ d1PlusCore 3 H K) (h3 : 3 ∣ Nat.card (oUpperTwo I₁)) {t : G}
    (htM : t ∈ M) (htK : t ∈ hyp111Pre 3 H K) : t ∈ Subgroup.normalizer (L : Set G) := by
  by_contra hnL
  have hI₁' : IsCZeroMember (H ⊓ L) I₁ := hI₁
  have hI₁L : I₁ ≤ L := hI₁'.le.trans inf_le_right
  refine TwelveNoSU.false_of_forall_commutator_mem hI₁ h3 fun x hx ⟨k, hk⟩ => ?_
  have hc : Nat.Coprime 3 (orderOf (x⁻¹ * t * x⁻¹⁻¹ * t⁻¹)) :=
    coprime_orderOf_commutator_of_mem htK (inv_mem (hX hx))
  have he : x⁻¹ * (t * x * t⁻¹) = x⁻¹ * t * x⁻¹⁻¹ * t⁻¹ := by group
  exact commutator_mem_pCoreOf_of_not_mem_normalizer_of_coprime hL htM hnL
    (hI₁L (CFSG.AGLEmbedding.oUpperTwo_le_self I₁ hx)) hk (he ▸ hc)

theorem exists_central_cover {A : Type} [Group A] [Finite A] {Y P : Subgroup A} (hPY : P ≤ Y)
    (hZP : ∀ z ∈ Subgroup.center ↥Y, (z : A) ∈ P) (hZc : Nat.card (Subgroup.center ↥Y) = 3)
    (hS4 : Nonempty (↥((P.subgroupOf Y).map (QuotientGroup.mk' (Subgroup.center ↥Y))) ≃*
      Equiv.Perm (Fin 4))) :
    ∃ f : ↥P →* Equiv.Perm (Fin 4), Function.Surjective f ∧
      f.ker ≤ Subgroup.center ↥P ∧ Nat.card f.ker = 3 := by
  obtain ⟨e4⟩ := hS4
  set Z := Subgroup.center ↥Y
  set π : ↥Y →* ↥Y ⧸ Z := QuotientGroup.mk' Z
  set R := (P.subgroupOf Y).map π
  let f₀ : ↥P →* ↥R := (π.comp (Subgroup.inclusion hPY)).codRestrict R (fun x =>
    ⟨⟨(x : A), hPY x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩)
  have hf₀ : Function.Surjective f₀ := by
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    exact ⟨⟨(y : A), Subgroup.mem_subgroupOf.mp hy⟩, Subtype.ext rfl⟩
  let f : ↥P →* Equiv.Perm (Fin 4) := e4.toMonoidHom.comp f₀
  have hker : ∀ x : ↥P, x ∈ f.ker ↔ Subgroup.inclusion hPY x ∈ Z := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1
      have h2 : f₀ x = 1 := (map_eq_one_iff _ e4.injective).mp h1
      have h3 : π (Subgroup.inclusion hPY x) = 1 := congrArg Subtype.val h2
      exact (QuotientGroup.eq_one_iff _).mp h3
    · intro h1
      have h3 : π (Subgroup.inclusion hPY x) = 1 := (QuotientGroup.eq_one_iff _).mpr h1
      have h2 : f₀ x = 1 := Subtype.ext h3
      change e4 (f₀ x) = 1
      rw [h2, map_one]
  refine ⟨f, e4.surjective.comp hf₀, fun x hx => ?_, ?_⟩
  · have hxZ := (hker x).mp hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h := (Subgroup.mem_center_iff.mp hxZ) (Subgroup.inclusion hPY g)
    simpa using congrArg Subtype.val h
  · have hbij : Function.Bijective (fun x : ↥f.ker => (⟨Subgroup.inclusion hPY x.1,
        (hker x.1).mp x.2⟩ : ↥Z)) := by
      refine ⟨fun a b h => ?_, fun z => ?_⟩
      · apply Subtype.ext
        apply Subtype.ext
        have := congrArg (fun w : ↥Z => ((w : ↥Y) : A)) h
        exact this
      · refine ⟨⟨⟨(z : A), hZP z z.2⟩, (hker _).mpr ?_⟩, ?_⟩
        · have : Subgroup.inclusion hPY ⟨(z : A), hZP z z.2⟩ = (z : ↥Y) := Subtype.ext rfl
          rw [this]
          exact z.2
        · apply Subtype.ext
          apply Subtype.ext
          rfl
    rw [Nat.card_congr (Equiv.ofBijective _ hbij), hZc]

theorem nineThree_parabolic_or_unique (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hNX : CFSG.AGLEmbeddingD2.NoXBlockFor G) (h98 : AGL81NineEightFour G)
    (hA7 : AGL81TenNineOneCfg G)
    (hZ : AGL81TenOneSixCenterCfg G) (hS : Setting G) (hd : AGL81CfgData 3 P M H Q K)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    (IsClassicalTwoOrG2 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∧
      IsParabolicTwo (barM M L) (barM M (H ⊓ L))) ∨
    ((∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 6) ∧
        Nonempty (↥(barM M (H ⊓ L)) ≃* Equiv.Perm (Fin n))) ∨
      (∃ n : ℕ, Nonempty (↥(barM M (H ⊓ L)) ⧸ CFSG.pCore 2 ↥(barM M (H ⊓ L)) ≃*
        Equiv.Perm (Fin n))) ∨
      (∃ r s : ℕ, 5 ≤ s ∧ Nonempty (↥(barM M (H ⊓ L)) ⧸ CFSG.pCore 2 ↥(barM M (H ⊓ L)) ≃*
        Equiv.Perm (Fin r) × Equiv.Perm (Fin s))) ∨
      (∃ (k : ℕ) (d : TauCeti.ValidLieTypeIndex), 3 ≤ k ∧
        (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B k q) ∧
        Nonempty (↥(barM M (H ⊓ L)) ⧸ CFSG.pCore 2 ↥(barM M (H ⊓ L)) ≃*
          (TauCeti.CFSGIndex.lie d).Group)) ∨
      (∃ f : ↥(barM M (H ⊓ L)) →* Equiv.Perm (Fin 4), Function.Surjective f ∧
        f.ker ≤ Subgroup.center ↥(barM M (H ⊓ L)) ∧ Nat.card f.ker = 3)) := by
  have hT := hd.toTwoLocalPhaseThree' hS h98
  have hK : Open.IsKGroup ↥M := (hT.toTwoLocalPair.isKGroup_of_isKProper hS.kProper).1
  have hA : Asc81bHyp M (pCoreOf 2 H) := hT.asc81bHyp
  have hNH : normalizer (pCoreOf 2 H : Set G) = H := hT.toTwoLocalPair.normalizer_twoCore_H
  have hNS : normalizer (pCoreOf 2 H : Set G) ⊓ L = H ⊓ L := by rw [hNH]
  have hX : ¬ InClassXBlock L := (hT.nineThree_not_one hK h85 hNX hL).1
  have trq : ∀ {T : Type} [Group T], Nonempty (↥(barM M (normalizer (pCoreOf 2 H : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM M (normalizer (pCoreOf 2 H : Set G) ⊓ L)) ≃* T) →
      Nonempty (↥(barM M (H ⊓ L)) ⧸ CFSG.pCore 2 ↥(barM M (H ⊓ L)) ≃* T) := by
    rintro T _ ⟨e⟩
    obtain ⟨e'⟩ := nonempty_quotient_pCore_mulEquiv
      (MulEquiv.subgroupCongr (congrArg (barM M) hNS.symm))
    exact ⟨e'.trans e⟩
  rcases hT.nineThree hK h93 hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · left
    refine ⟨h2.1, ?_⟩
    have := h2.2.1
    rwa [hNS] at this
  · right
    have hSy := hT.not_isSylowTwoOf_inf hK h85 hNX hL
    rcases citedBlockTransvectionPL_of_type
        CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds G M
        (pCoreOf 2 H) L hK hA hL hX hSy h3 with ⟨k, d, hk, hq, hP⟩ | ⟨n, -, hP⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, d, hk, hq, trq hP⟩)))
    · exact Or.inr (Or.inl ⟨n, trq hP⟩)
  · right
    have hZP := hZ hS 3 P M H Q K hd L hL h4
    obtain ⟨-, hZc, -, -, hS4⟩ := h4
    rw [hNS] at hS4
    have hPY : barM M (H ⊓ L) ≤ barM M L := map_mono fun x hx => by
      rw [mem_subgroupOf] at hx ⊢
      exact hx.2
    exact Or.inr (Or.inr (Or.inr (Or.inr (exists_central_cover hPY hZP hZc hS4))))
  · exact ((hA7 hS 3 P M H Q K hd L hL).false h5.2.1.some).elim
  · right
    obtain ⟨-, n, -, hP⟩ := h6
    exact Or.inr (Or.inl ⟨n, trq hP⟩)
  · right
    obtain ⟨-, n, -, hP⟩ := h7
    exact Or.inr (Or.inl ⟨n, trq hP⟩)
  · right
    obtain ⟨-, N, r, hN, hr, h0, h2', h4', -, φ, -, -⟩ := h8
    have hs : 5 ≤ N - 2 * r := by
      obtain ⟨a, ha⟩ := hN
      omega
    have hφ : Nonempty (↥(barM M (normalizer (pCoreOf 2 H : Set G) ⊓ L)) ⧸
        CFSG.pCore 2 ↥(barM M (normalizer (pCoreOf 2 H : Set G) ⊓ L)) ≃*
          Equiv.Perm (Fin r) × Equiv.Perm (Fin (N - 2 * r))) := ⟨φ⟩
    exact Or.inr (Or.inr (Or.inl ⟨r, N - 2 * r, hs, trq hφ⟩))

theorem agl81TwelveCaseNotLe_of_kfacts (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hNX : CFSG.AGLEmbeddingD2.NoXBlockFor G) (h98 : AGL81NineEightFour G)
    (hA7 : AGL81TenNineOneCfg G) (hZ : AGL81TenOneSixCenterCfg G)
    (h1031 : AGL81TenThreeOneAt G) (h1013 : AGL81TenThirteenAt G)
    (hAS : KFactTwelveNotLeAltSix) (hGr : KFactTwelveNotLeGraph)
    (hSU : KFactTwelveNotLeSymThreeUnique) (hLn : KFactLnTwoCentralizer G)
    (h42 : AGL81TenFourteenThreeAt G) (hn : AGL81TwelveNormalizes G)
    (h431 : AGL81TenFourteenTwoThree G) : AGL81TwelveCaseNotLe G := by
  intro hS P M H Q K b L h3σ hc hJ
  have hc' : TwelveCase P M H Q K b L := hc
  obtain ⟨hd, hA6, -, -, hb, hL, I₀, hI₀, hI₀K⟩ := hc
  have hb' : TwelveB M H Q K b := hb
  obtain ⟨hbHM, hbX, hob, hCb, hQb⟩ := hb
  have hbL : b ∈ normalizer (L : Set G) := hn hS P M H Q K b L hc' (mem_zpowers b)
  have h3 : ∀ I ∈ cZero (H ⊓ L), 3 ∣ Nat.card (oUpperTwo I) := fun I hI =>
    h1031 hS 3 P M H Q K hd L hL I hI
  haveI := normal_of_cfg hd hA6
  have hZK := center_eq_bot_of_isAltTwoP hA6
  obtain ⟨S, hSK⟩ := hd.sylowK
  have hLM : L ≤ M := hL.le
  have hDM : H ⊓ L ≤ M := inf_le_right.trans hLM
  have hI₀' : IsCZeroMember (H ⊓ L) I₀ := hI₀
  obtain ⟨I₁, hI₁, hI₁X⟩ :=
    exists_xPart_of_not_le hAS h1013 h3σ hS hd hA6 S hSK hbHM.1 hbX hL hbL h3 hJ
  have hI₁' : IsCZeroMember (H ⊓ L) I₁ := hI₁
  obtain ⟨t, htM, htK, ⟨k, htk⟩, hmove⟩ := exists_two_element_moving hAS hd hA6 S hSK hb'
  have htK' : (t : G) ∈ hyp111Pre 3 H K := ⟨t, htK, rfl⟩
  have htL : (t : G) ∈ normalizer (L : Set G) :=
    mem_normalizer_of_xPart hA6 hL.toIsTwoPrimeComponent hI₁ hI₁X (h3 I₁ hI₁) htM htK'
  have htD : (t : G) ∈ normalizer ((H ⊓ L : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    have h1 := mem_normalizer_iff.mp (le_normalizer t.2 : (t : G) ∈ normalizer (H : Set G)) x
    have h2 := mem_normalizer_iff.mp htL x
    exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩
  obtain ⟨hO2, ⟨e⟩, hIE, hI3⟩ := kPart_shape hAS hd hA6 S hSK hLM hI₀ hI₀K (h3 I₀ hI₀)
  set I₀t := I₀.map (MulAut.conj (t : G)).toMonoidHom with hI₀t
  have hI₀t' : IsCZeroMember (H ⊓ L) I₀t := hI₀'.map_conj htD
  have hI₀tK : oUpperTwo I₀t ≤ hyp111Pre 3 H K := oUpperTwo_map_conj_le hI₀K t.2
  obtain ⟨hO2t, ⟨et⟩, -, -⟩ := kPart_shape hAS hd hA6 S hSK hLM hI₀t' hI₀tK (h3 I₀t hI₀t')
  set Pb := barM M (H ⊓ L) with hPb
  set tb := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(t : G), htM⟩ with htb
  have hJt : (barM M I₀).map (MulAut.conj tb).toMonoidHom = barM M I₀t :=
    (barM_map_conj htM I₀).symm
  have hJsn := isSubnormal_hatOf hDM hI₀'.subnormal
  have hJtsn := isSubnormal_hatOf hDM hI₀t'.subnormal
  have hJe : Nonempty (↥(hatOf Pb (barM M I₀)) ≃* Equiv.Perm (Fin 3)) := by
    obtain ⟨f⟩ := nonempty_hatOf_mulEquiv hDM hI₀'.le
      (inf_pCoreOf_eq_of_isSubnormal hI₀'.subnormal)
    exact ⟨f.trans e⟩
  have hJte : Nonempty (↥(hatOf Pb (barM M I₀t)) ≃* Equiv.Perm (Fin 3)) := by
    obtain ⟨f⟩ := nonempty_hatOf_mulEquiv hDM hI₀t'.le
      (inf_pCoreOf_eq_of_isSubnormal hI₀t'.subnormal)
    exact ⟨f.trans et⟩
  have hne : hatOf Pb (barM M I₀t) ≠ hatOf Pb (barM M I₀) := by
    intro h
    have hle := le_sup_pCoreOf_of_hatOf_eq hDM hI₀t'.le hI₀'.le h
    rw [← hO2, sup_eq_left.mpr (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 I₀)] at hle
    have heq : I₀t = I₀ := eq_of_le_of_card_ge hle (by
      rw [hI₀t, card_map_of_injective (MulAut.conj (t : G)).injective])
    have hO : (oUpperTwo I₀).map (MulAut.conj (t : G)).toMonoidHom = oUpperTwo I₀ := by
      rw [CFSG.AGLEmbedding.SUPair.map_oUpperTwo, ← hI₀t, heq]
    apply hmove _ hIE hI3
    rw [mem_normalizer_iff_map_conj_eq]
    calc (((oUpperTwo I₀).subgroupOf H).map
          (QuotientGroup.mk' (primeComplementCore (G := H) 3))).map
          (MulAut.conj (QuotientGroup.mk' (primeComplementCore (G := H) 3) t))
        = ((((oUpperTwo I₀).subgroupOf H).map (MulAut.conj t).toMonoidHom).map
            (QuotientGroup.mk' (primeComplementCore (G := H) 3))) := by
          rw [Subgroup.map_map, Subgroup.map_map]
          congr 1
      _ = ((((oUpperTwo I₀).map (MulAut.conj (t : G)).toMonoidHom).subgroupOf H).map
            (QuotientGroup.mk' (primeComplementCore (G := H) 3))) := by
          rw [subgroupOf_map_conj t.2]
      _ = ((oUpperTwo I₀).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) :=
          by rw [hO]
  rcases nineThree_parabolic_or_unique h85 h93 hNX h98 hA7 hZ hS hd hL with ⟨hcl, hpar⟩ | hshape
  ·
    have hqs : CFSG.Open.IsQuasisimple ↥(barM M L) := hL.component.2.2
    have hOL : pCoreOf 2 (barM M L) = ⊥ :=
      TenThreeThree.pCoreOf_barM_eq_bot hL.toIsTwoPrimeComponent
    obtain ⟨hLr, hMr⟩ := twelve_ranks hS hd hLM
    have hrk : Open.pRank 3 (barM M L) ≤ 3 := by
      rw [pRank_barM_eq Nat.prime_three (by norm_num) M L hLM]
      omega
    have htY : tb ∈ normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      LnTwoLift.mem_normalizer_barM htM htL
    have htP : tb ∈ normalizer (Pb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      LnTwoLift.mem_normalizer_barM htM htD
    have ht2 : ∃ k : ℕ, tb ^ 2 ^ k = 1 := ⟨k, by
      rw [htb, ← map_pow, show (⟨(t : G), htM⟩ : ↥M) ^ 2 ^ k = 1 from
        Subtype.ext (by simpa using congrArg Subtype.val htk), map_one]⟩
    have hne' : hatOf Pb ((barM M I₀).map (MulAut.conj tb).toMonoidHom) ≠ hatOf Pb (barM M I₀) := by
      rw [hJt]
      exact hne
    have hJ1sn := isSubnormal_hatOf hDM hI₁'.subnormal
    obtain ⟨f₁⟩ := nonempty_hatOf_mulEquiv hDM hI₁'.le
      (inf_pCoreOf_eq_of_isSubnormal hI₁'.subnormal)
    have hJ1shape : IsSymThreeOrSUThreeTwo ↥(hatOf Pb (barM M I₁)) ∨
        Open.IsQuasisimple ↥(hatOf Pb (barM M I₁)) := by
      rcases hI₁'.shape with ha | ⟨-, hb₁⟩
      · right
        exact CFSG.Open.IsQuasisimple.of_mulEquiv
          (f₁.trans (Subgroup.topEquiv.symm.trans
            (MulEquiv.subgroupCongr (LnTwoLift.barM_self_eq_top' I₁).symm))) ha.component.2.2
      · exact Or.inl (IsSymThreeOrSUThreeTwo.of_mulEquiv f₁.symm hb₁)
    have hdist : ∀ {I : Subgroup G}, IsCZeroMember (H ⊓ L) I → oUpperTwo I ≤ hyp111Pre 3 H K →
        pCoreOf 2 I = pCoreOf 2 (H ⊓ L) → hatOf Pb (barM M I₁) ≠ hatOf Pb (barM M I) := by
      intro I hI hIK hOI h
      have hle := le_sup_pCoreOf_of_hatOf_eq hDM hI₁'.le hI.le h
      rw [← hOI, sup_eq_left.mpr (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 I)] at hle
      have hle2 : oUpperTwo I₁ ≤ oUpperTwo I :=
        closure_mono fun x hx => ⟨hle hx.1, hx.2⟩
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (h3 I₁ hI₁)
      have hcx := coprime_orderOf_of_mem_hyp111Pre_d1PlusCore hZK (hIK (hle2 x.2)) (hI₁X x.2)
      rw [Subgroup.orderOf_coe, hx] at hcx
      norm_num at hcx
    have hne1 := hdist hI₀' hI₀K hO2
    have hne2 : hatOf Pb (barM M I₁) ≠ hatOf Pb ((barM M I₀).map (MulAut.conj tb).toMonoidHom) := by
      rw [hJt]
      exact hdist hI₀t' hI₀tK hO2t
    obtain ⟨r, hr, hlie⟩ := hGr (↥M ⧸ CFSG.pCore 2 ↥M) (barM M L) Pb (barM M I₀) (barM M I₁) tb
      hqs hOL hcl hpar hrk (barM_mono hI₀'.le) hJsn hJe htY htP ht2 hne'
      (barM_mono hI₁'.le) hJ1sn hJ1shape hne1 hne2
    obtain ⟨I, hI, h3I⟩ := hLn M L b r hL.toIsTwoPrimeComponent hr hlie hbHM.2
      (hn hS P M H Q K b L hc') hob (h42 hS P M H Q K b L hc')
    obtain ⟨H₁, R₁, hesc⟩ := hd.escape
    exact h431 hS P M H₁ R₁ hesc b hbHM.2 hob hCb ⟨Q, hQb, hd.base⟩ I hI h3I
  ·
    exact hne (hSU ↥Pb hshape _ _ hJtsn hJsn hJte hJe)

end TwelveNotLe

variable {G : Type} [Group G] [Finite G]
  in
theorem agl81ElevenTwelveOne_of_cartan_kfacts (h9 : AGL81NineCompetitorQ G)
    (h1014 : AGL81TenFourteenThreeCfg G) (h1031 : AGL81TenThreeOneAt G)
    (h431 : AGL81TenFourteenTwoThree G) (h1013 : AGL81TenThirteenAt G)
    (h85 : Asc81bEightFive) (h93 : Asc81bNineThree) (hNX : CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (h98 : AGL81NineEightFour G) (hA7 : AGL81TenNineOneCfg G) (hZ : AGL81TenOneSixCenterCfg G)
    (hC : AGL81TenThreeThreeCasesNCfg G) (hKL : KFactTwelveRanksLe)
    (hLn : KFactLnTwoCentralizer G) (hKC : TwelveLe.KFactTwelveLeCartan)
    (hKE : TwelveLe.KFactTwelveLeE27) (hGr : TwelveNotLe.KFactTwelveNotLeGraph) :
    AGL81ElevenTwelveOne G :=
  have h42 := agl81TenFourteenThreeAt_of h1014 h1031
  have hn := agl81TwelveNormalizes_of_tenThreeOne h1031
  agl81ElevenTwelveOne_of (agl81TwelveSetup_of h9) h42
    (TwelveNotLe.agl81TwelveCaseNotLe_of_kfacts h85 h93 hNX h98 hA7 hZ h1031 h1013
      TwelveNotLe.kFactTwelveNotLeAltSix_holds hGr TwelveNotLe.kFactTwelveNotLeSymThreeUnique_holds
      hLn h42 hn h431)
    (TwelveLe.agl81TwelveCaseLe_of_cartan hC hn h431 hKL hKC hKE)

end CFSG.LocalAnalysis.RankThreeTheoremC
