module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairTRFrontier
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.StrongThreeAutomizer
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairOddIndex
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFour
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive
import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairSepAssembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.RankThreeTheoremC

@[expose] def KFactParabolicE9NotTransitive : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (Lb P E N : Subgroup Q), CFSG.Open.IsQuasisimple ↥Lb →
    IsClassicalTwoOrG2 (↥Lb ⧸ Subgroup.center ↥Lb) → IsParabolicTwo Lb P →
    ¬ IsSylowTwoOf (pCoreOf 2 P) Lb →
    (∀ J : Subgroup Q, J ≤ P → ⁅J, J⁆ = J → ¬ 3 ∣ Nat.card J) →
    E ≤ P → IsElemAbelian 3 E → Nat.card E = 9 → ¬ 3 ∣ E.relIndex P →
    N ≤ Subgroup.normalizer (Lb : Set Q) → N ≤ Subgroup.normalizer (E : Set Q) →
    N ≤ Subgroup.normalizer (P : Set Q) → ¬ TransitiveOnNonidentity N E

theorem irreducibleOn_of_transitiveOnNonidentity {X : Type*} [Group X] {N R : Subgroup X}
    (htr : TransitiveOnNonidentity N R) : IrreducibleOn N R := by
  intro W hWR hNW
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨⟨w, hwW⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  refine le_antisymm hWR fun y hy => ?_
  by_cases hy1 : y = 1
  · rw [hy1]; exact W.one_mem
  obtain ⟨n, hn, hny⟩ := htr w (hWR hwW) y hy hw1' hy1
  rw [← hny]
  exact (Subgroup.mem_normalizer_iff.mp (hNW hn) w).mp hwW

variable {G : Type} [Group G] [Finite G]

theorem PairStrongCtx.transitive_of_oddIndex (hK : KFactStrongThreeAutomizer)
    {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R)
    (hodd : ¬ PairEvenIndex M H) :
    IsElemAbelian 3 R ∧ Nat.card R = 9 ∧
      TransitiveOnNonidentity (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) R :=
  transitive_of_oddIndex_of_pair hK hctx.pair hctx.esc hctx.strong hodd

omit [Finite G] in
theorem transitive_barM {M H R : Subgroup G}
    (htr : TransitiveOnNonidentity (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) R) :
    TransitiveOnNonidentity (barM M (H ⊓ M ⊓ Subgroup.normalizer (R : Set G))) (barM M R) := by
  intro x hx y hy hx1 hy1
  obtain ⟨r₁, hr₁R, rfl⟩ := mem_barM_iff.mp hx
  obtain ⟨r₂, hr₂R, rfl⟩ := mem_barM_iff.mp hy
  have hr₁1 : (r₁ : G) ≠ 1 := fun h1 => hx1 (by
    have : r₁ = 1 := Subtype.ext h1
    rw [this, map_one])
  have hr₂1 : (r₂ : G) ≠ 1 := fun h1 => hy1 (by
    have : r₂ = 1 := Subtype.ext h1
    rw [this, map_one])
  obtain ⟨n, hn, hnr⟩ := htr _ hr₁R _ hr₂R hr₁1 hr₂1
  have hnM : n ∈ M := hn.1.2
  refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨n, hnM⟩,
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hn), ?_⟩
  have e : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨n, hnM⟩ * QuotientGroup.mk' (CFSG.pCore 2 ↥M) r₁ *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨n, hnM⟩)⁻¹ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨n * r₁ * n⁻¹, M.mul_mem (M.mul_mem hnM r₁.2)
        (M.inv_mem hnM)⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e]
  have : (⟨n * r₁ * n⁻¹, M.mul_mem (M.mul_mem hnM r₁.2) (M.inv_mem hnM)⟩ : ↥M) = r₂ :=
    Subtype.ext hnr
  rw [this]

theorem exists_conj_mem_of_sylow {X R : Subgroup G} (hR : IsPGroup 3 R)
    (hidx : ¬ 3 ∣ R.relIndex X) {z : G} (hzX : z ∈ X) (hz : IsPGroup 3 (Subgroup.zpowers z)) :
    ∃ h ∈ X, h⁻¹ * z * h ∈ R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR'p : IsPGroup 3 (R.subgroupOf X) := hR.comap_of_injective X.subtype X.subtype_injective
  set S₀ : Sylow 3 ↥X := hR'p.toSylow hidx
  have hz' : IsPGroup 3 (Subgroup.zpowers (⟨z, hzX⟩ : ↥X)) := by
    refine (hz.comap_of_injective X.subtype X.subtype_injective).to_le ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_comap.mpr (Subgroup.mem_zpowers z)
  obtain ⟨Q, hQ⟩ := hz'.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥X S₀ Q
  have hzQ : (⟨z, hzX⟩ : ↥X) ∈ (Q : Subgroup ↥X) := hQ (Subgroup.mem_zpowers _)
  rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hzQ
  refine ⟨(h : G), h.2, ?_⟩
  have hmem : h⁻¹ * ⟨z, hzX⟩ * h ∈ R.subgroupOf X := by
    have := (IsPGroup.mem_toSylow hR'p hidx).mp hzQ
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have := Subgroup.mem_subgroupOf.mp hmem
  simpa using this

omit [Finite G] in
theorem barM_normalizer_inf_eq {M S L : Subgroup G} (hQS : pCoreOf 2 M ≤ S) :
    barM M (Subgroup.normalizer (S : Set G) ⊓ L) =
      barM M (Subgroup.normalizer (S : Set G)) ⊓ barM M L := by
  refine le_antisymm (le_inf (barM_mono inf_le_left) (barM_mono inf_le_right)) ?_
  rintro x ⟨hxN, hxL⟩
  obtain ⟨n, hnN, rfl⟩ := mem_barM_iff.mp hxN
  obtain ⟨l, hlL, hl⟩ := mem_barM_iff.mp hxL
  have hker : n⁻¹ * l ∈ CFSG.pCore 2 ↥M := by
    rw [← QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥M), QuotientGroup.mk_mul,
      QuotientGroup.mk_inv]
    change (QuotientGroup.mk' (CFSG.pCore 2 ↥M) n)⁻¹ * QuotientGroup.mk' (CFSG.pCore 2 ↥M) l = 1
    rw [hl, inv_mul_cancel]
  have hkS : ((n⁻¹ * l : ↥M) : G) ∈ S := hQS (by
    unfold pCoreOf
    exact Subgroup.mem_map_of_mem M.subtype hker)
  have hlN : (l : G) ∈ Subgroup.normalizer (S : Set G) := by
    have e : (l : G) = (n : G) * ((n⁻¹ * l : ↥M) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem _ hnN (Subgroup.le_normalizer hkS)
  rw [← hl]
  exact mem_barM_iff.mpr ⟨l, ⟨hlN, hlL⟩, rfl⟩

omit [Finite G] in
theorem barM_normalizer_le_normalizer_of_oneImage {M H L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L) :
    barM M (Subgroup.normalizer (pCoreOf 2 H : Set G)) ≤
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  intro x hx
  obtain ⟨k, hkN, rfl⟩ := mem_barM_iff.mp hx
  have hw := hL.map_conj k.2 hkN
  have he := hk1 _ hw
  rw [barM_map_conj k.2] at he
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr he

theorem PairStrongCtx.not_three_dvd_relIndex_inf {P : Sylow 3 G} {M A H R : Subgroup G}
    (hctx : PairStrongCtx P M A H R) : ¬ 3 ∣ R.relIndex (H ⊓ M) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpr := hctx.pair
  obtain ⟨T, hT⟩ := hctx.esc.isSylow
  have hRT : R.subgroupOf H = (T : Subgroup ↥H) := by
    rw [← hT]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hmul : R.relIndex (H ⊓ M) * (H ⊓ M).relIndex H = R.relIndex H :=
    Subgroup.relIndex_mul_relIndex R (H ⊓ M) H (le_inf hpr.le_H hpr.le_M) inf_le_left
  intro hd
  apply T.not_dvd_index
  have e : R.relIndex H = (T : Subgroup ↥H).index := by
    rw [Subgroup.relIndex, hRT]
  rw [← e, ← hmul]
  exact hd.mul_right _

theorem exists_threeElement_of_barM {M X : Subgroup G} {y₀ : ↥M} (hy₀ : (y₀ : G) ∈ X)
    (hy3 : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) y₀) ^ 3 = 1)
    (hy1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) y₀ ≠ 1) :
    ∃ z : ↥M, (z : G) ∈ X ∧ IsPGroup 3 (Subgroup.zpowers (z : G)) ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) z ≠ 1 := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have ho : orderOf y₀ ≠ 0 := (orderOf_pos y₀).ne'
  obtain ⟨e, m, hm3, hom⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho 3 (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hom
    exact ho hom
  refine ⟨y₀ ^ m, X.pow_mem hy₀ m, ?_, ?_⟩
  · have hord : orderOf ((y₀ : G) ^ m) = 3 ^ e := by
      rw [orderOf_pow' _ hm0, Subgroup.orderOf_coe, hom]
      have : Nat.gcd (3 ^ e * m) m = m := Nat.gcd_eq_right (Dvd.intro_left _ rfl)
      rw [this, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
    refine IsPGroup.of_card (n := e) ?_
    rw [Nat.card_zpowers]
    push_cast
    exact hord
  · rw [map_pow]
    intro h
    have hord : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) y₀) = 3 :=
      orderOf_eq_prime hy3 hy1
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hdvd
    exact hm3 hdvd

theorem PairStrongCtx.barM_le_of_oneImage {P : Sylow 3 G} {M A H R : Subgroup G}
    (hctx : PairStrongCtx P M A H R) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (hy : ∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L), y ^ 3 = 1 ∧ y ≠ 1)
    (hirr : IrreducibleOn (barM M (H ⊓ M ⊓ Subgroup.normalizer (R : Set G))) (barM M R)) :
    barM M R ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) := by
  have hpr := hctx.pair
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Kb := barM M (Subgroup.normalizer (S : Set G)) with hKb
  set Pb := barM M (Subgroup.normalizer (S : Set G) ⊓ L) with hPbdef
  have hPb : Pb = Kb ⊓ barM M L := barM_normalizer_inf_eq hpr.twoCore_M_le
  have hKP : Kb ≤ Subgroup.normalizer (Pb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro k hk
    have h1 := barM_normalizer_le_normalizer_of_oneImage hL hk1 hk
    rw [Subgroup.mem_normalizer_iff] at h1 ⊢
    intro x
    rw [hPb]
    constructor
    · rintro ⟨hxK, hxL⟩
      exact ⟨Kb.mul_mem (Kb.mul_mem hk hxK) (Kb.inv_mem hk), (h1 x).mp hxL⟩
    · rintro ⟨hxK, hxL⟩
      refine ⟨?_, (h1 x).mpr hxL⟩
      have e : x = k⁻¹ * (k * x * k⁻¹) * k := by group
      rw [e]
      exact Kb.mul_mem (Kb.mul_mem (Kb.inv_mem hk) hxK) hk
  have hHMK : ∀ n : ↥M, (n : G) ∈ H → mk n ∈ Kb := fun n hn =>
    mem_barM_iff.mpr ⟨n, by rw [hpr.normalizer_twoCore_H]; exact hn, rfl⟩
  obtain ⟨y, hyP, hy3, hy1⟩ := hy
  obtain ⟨y₀, hy₀, rfl⟩ := mem_barM_iff.mp hyP
  obtain ⟨z, hzX, hz3, hz1⟩ := exists_threeElement_of_barM hy₀ hy3 hy1
  have hzHM : (z : G) ∈ H ⊓ M := ⟨by rw [← hpr.normalizer_twoCore_H]; exact hzX.1, z.2⟩
  obtain ⟨h, hhHM, hhz⟩ := exists_conj_mem_of_sylow hpr.isPGroup_R
    hctx.not_three_dvd_relIndex_inf hzHM hz3
  set w : ↥M := ⟨h⁻¹ * z * h, M.mul_mem (M.mul_mem (M.inv_mem hhHM.2) z.2) hhHM.2⟩ with hw
  have hwR : mk w ∈ barM M R := mem_barM_iff.mpr ⟨w, hhz, rfl⟩
  have hwP : mk w ∈ Pb := by
    have hzP : mk z ∈ Pb := mem_barM_iff.mpr ⟨z, hzX, rfl⟩
    have hhK : mk ⟨h, hhHM.2⟩ ∈ Kb := hHMK _ hhHM.1
    have := (Subgroup.mem_normalizer_iff.mp (hKP (Kb.inv_mem hhK)) _).mp hzP
    have e : mk w = (mk ⟨h, hhHM.2⟩)⁻¹ * mk z * ((mk ⟨h, hhHM.2⟩)⁻¹)⁻¹ := by
      rw [inv_inv, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact this
  have hw1 : mk w ≠ 1 := by
    intro h1
    apply hz1
    have e : mk z = mk ⟨h, hhHM.2⟩ * mk w * (mk ⟨h, hhHM.2⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [hw, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e, h1, mul_one, mul_inv_cancel]
  have hinv : barM M (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) ≤
      Subgroup.normalizer ((barM M R ⊓ Pb : Subgroup _) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro n hn
    obtain ⟨n₀, hn₀, rfl⟩ := mem_barM_iff.mp hn
    have hnR : mk n₀ ∈ Subgroup.normalizer (barM M R : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      have hmap : R.map (MulAut.conj (n₀ : G)).toMonoidHom = R :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hn₀.2
      have := barM_map_conj n₀.2 R
      rw [hmap] at this
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr this.symm
    have hnP := hKP (hHMK n₀ hn₀.1.1)
    rw [Subgroup.mem_normalizer_iff] at hnR hnP ⊢
    intro x
    exact ⟨fun hx => ⟨(hnR x).mp hx.1, (hnP x).mp hx.2⟩,
      fun hx => ⟨(hnR x).mpr hx.1, (hnP x).mpr hx.2⟩⟩
  rcases hirr _ inf_le_left hinv with hbot | htop
  · exfalso
    have hmem : mk w ∈ (barM M R ⊓ Pb : Subgroup _) := ⟨hwR, hwP⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hw1 hmem
  · intro x hx
    have : x ∈ (barM M R ⊓ Pb : Subgroup _) := by rw [htop]; exact hx
    exact this.2

@[expose] def OddTwoImageKill : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M A H R : Subgroup G),
    PairStrongCtx P M A H R → IsElemAbelian 3 R → Nat.card R = 9 →
    TransitiveOnNonidentity (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) R →
    ∀ L₁ L₂ : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L₁ → IsWeakSBlock M (pCoreOf 2 H) L₂ →
    barM M L₁ ≠ barM M L₂ →
    (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L₁ ∨ barM M L' = barM M L₂) →
    (∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₁), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M))) →
    (∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₂), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M))) → False

@[expose] def OddOneImageKill : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M A H R : Subgroup G),
    PairStrongCtx P M A H R → ¬ PairEvenIndex M H → IsElemAbelian 3 R → Nat.card R = 9 →
    TransitiveOnNonidentity (barM M (H ⊓ M ⊓ Subgroup.normalizer (R : Set G))) (barM M R) →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L) →
    barM M R ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) → False


theorem pairOddIndexResidue_of (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hK : KFactStrongThreeAutomizer)
    (hcen : PairBlockCentreThree) (hO3 : OddTwoImageKill) (hO5 : OddOneImageKill) :
    PairOddIndexResidue := by
  intro G _ _ P M A H R hctx hodd
  have hpr := hctx.pair
  have hLF := CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
  have h84 : Asc81bEightFour := asc81bEightFour_of_factorization hLF
  have h85 : Asc81bEightFive := asc81bEightFive_of_factorization hLF
  have h86 : Asc81bEightSix :=
    asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved
  set S := pCoreOf 2 H
  have hX : NoXBlockFor G := hD2.noXBlockFor hctx.glob.toD1Global
  have hH := hctx.esc.pRank_H
  have hthree : ∀ L : Subgroup G, IsWeakSBlock M S L → BlockHasThree M S L := fun L hL =>
    hpr.blockHasThree h85 h86 h93 hX kFactParabolicThree
      (citedBlockThreeTransvection_of_inverted hΛ) (kFactBlockThreeAltSeven_of_inverted hΛ) hL
  have hy : ∀ L : Subgroup G, IsWeakSBlock M S L →
      ∃ y ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L), y ^ 3 = 1 ∧
        y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun L hL => by
    by_cases hZ : 3 ∣ Nat.card (barM M L ⊓
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)
    · exact hcen G P M A H R hctx L hL hZ
    · exact exists_order_three_noncentral hL.le (hthree L hL) hZ
  obtain ⟨hRel, hR9, htr⟩ := hctx.transitive_of_oddIndex hK hodd
  have htrb := transitive_barM htr
  obtain ⟨L₁, hL₁⟩ := hpr.exists_weakSBlock h84 hX
  by_cases hk1 : ∀ L' : Subgroup G, IsWeakSBlock M S L' → barM M L' = barM M L₁
  ·
    obtain ⟨y, hyP, hy3, hyC⟩ := hy L₁ hL₁
    have hy1 : y ≠ 1 := fun h1 => hyC (h1 ▸ Subgroup.one_mem _)
    have hle := hctx.barM_le_of_oneImage hL₁ hk1 ⟨y, hyP, hy3, hy1⟩
      (irreducibleOn_of_transitiveOnNonidentity htrb)
    exact hO5 G P M A H R hctx hodd hRel hR9 htrb L₁ hL₁ hk1 hle
  ·
    simp only [not_forall] at hk1
    obtain ⟨L₂, hL₂, hne⟩ := hk1
    have hk2 : ∀ L' : Subgroup G, IsWeakSBlock M S L' →
        barM M L' = barM M L₁ ∨ barM M L' = barM M L₂ := by
      intro L' hL'
      by_contra hcon
      simp only [not_or] at hcon
      refine hpr.false_of_three_weakSBlock_images hH hthree ![L₁, L₂, L'] (fun i => ?_) ?_
      · fin_cases i
        · exact hL₁
        · exact hL₂
        · exact hL'
      · have h12 : barM M L₁ ≠ barM M L₂ := fun he => hne he.symm
        have h13 : barM M L₁ ≠ barM M L' := fun he => hcon.1 he.symm
        have h23 : barM M L₂ ≠ barM M L' := fun he => hcon.2 he.symm
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp at hij ⊢
        all_goals first
          | exact absurd hij h12 | exact absurd hij.symm h12 | exact absurd hij h13
          | exact absurd hij.symm h13 | exact absurd hij h23 | exact absurd hij.symm h23
    exact hO3 G P M A H R hctx hRel hR9 htr L₁ L₂ hL₁ hL₂ (fun he => hne he.symm) hk2
      (hy L₁ hL₁) (hy L₂ hL₂)

end CFSG.AGLEmbeddingD2.McLaughlin
