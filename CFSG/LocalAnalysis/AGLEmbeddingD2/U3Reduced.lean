module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Assembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.TheoremZ
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.LocalAnalysis.AGLEmbedding.PairPrimeCoreCommutator
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeOut
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactUnitaryThreeSylow
import CFSG.LocalAnalysis.AGLEmbeddingD2.L2Data
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorel

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

theorem card_inf_centralizer_eq_prime {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {R : Subgroup G} (hR : Nat.card R = p ^ 3)
    (hcomm : ⁅R, R⁆ = R ⊓ Subgroup.centralizer (R : Set G)) :
    Nat.card (R ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) = p := by
  have hp : p.Prime := Fact.out
  have hZ : (Subgroup.center R).map R.subtype = R ⊓ Subgroup.centralizer (R : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_center_iff, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, fun g hg => by simpa using congrArg Subtype.val (hy ⟨g, hg⟩)⟩
    · rintro ⟨hx, hc⟩
      exact ⟨⟨x, hx⟩, fun g => Subtype.ext (hc g g.2), rfl⟩
  have : Finite R := Nat.finite_of_card_ne_zero (hR ▸ pow_ne_zero 3 hp.ne_zero)
  rw [← hZ, Subgroup.card_map_of_injective R.subtype_injective]
  have hnc : ¬ IsMulCommutative R := by
    intro hc
    have hRC : R ≤ Subgroup.centralizer (R : Set G) := fun a ha => by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val (hc.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
    rw [inf_eq_left.mpr hRC, Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hRC] at hcomm
    rw [← hcomm, Subgroup.card_bot] at hR
    have := Nat.one_lt_pow (by norm_num : 3 ≠ 0) hp.one_lt
    omega
  obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow hR (by norm_num)
  have hk3 : k ≤ 3 := by
    have := Subgroup.card_subgroup_dvd_card (Subgroup.center R)
    rw [hk, hR] at this
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp this
  interval_cases k
  · simpa using hk
  · exfalso
    have hidx : (Subgroup.center R).index = p := by
      have := Subgroup.card_mul_index (Subgroup.center R)
      rw [hk, hR] at this
      apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2)
      rw [this]
      ring
    have : IsCyclic (R ⧸ Subgroup.center R) := by
      have : Fact (Nat.card (R ⧸ Subgroup.center R)).Prime := ⟨by
        rw [← Subgroup.index, hidx]; exact hp⟩
      exact isCyclic_of_prime_card rfl
    exact hnc (isMulCommutative_of_isCyclic_quotient_center_self R)
  · exfalso
    have htop : Subgroup.center R = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, hk, hR]
    exact hnc (Subgroup.center_eq_top_iff.mp htop)

theorem isUnitaryIndex_of_twistedA {p : ℕ} {d : TauCeti.ValidLieTypeIndex}
    {q : TauCeti.PrimePower} (hq : q.p = p) (hq1 : q.exponent = 1) (hd : d.1 = .twistedA 2 q) :
    IsUnitaryIndex p d ∧ d.1.fieldExponent = 1 :=
  ⟨⟨q, hq, hd⟩, by rw [hd]; simpa using hq1⟩

theorem isUnitaryIndex_of_case {p : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hp : p = d.1.characteristic)
    (hd : ∃ q : TauCeti.PrimePower, q.exponent = 1 ∧ d.1 = .twistedA 2 q) :
    IsUnitaryIndex p d ∧ d.1.fieldExponent = 1 := by
  obtain ⟨q, hq1, hdq⟩ := hd
  exact isUnitaryIndex_of_twistedA (by rw [hp, hdq]; simp) hq1 hdq

private theorem exists_of_isUnitaryIndex {p : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hd : IsUnitaryIndex p d) (hn : d.1.fieldExponent = 1) :
    ∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ d.1 = .twistedA 2 q := by
  obtain ⟨q, hq, hdq, hfe, -⟩ := hd.exists_eq
  exact ⟨q, hq, hfe ▸ hn, hdq⟩

structure UnitaryBorelKFacts : Prop where
  sylowStructure : KFactUnitarySylowStructure
  unipotentCentralizer : KFactUnitaryUnipotentCentralizer
  borelMaximal : KFactUnitaryBorelMaximal
  sylowNormalizerSolvable : KFactUnitarySylowNormalizerSolvable

section Reduced

variable {X : Type} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {A X₀ K : Subgroup X}

namespace D2AlmostSimple

theorem sylow_le_of_u3 [Fact p.Prime] (h : D2AlmostSimple p X R A X₀ K)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) (hn : d.1.fieldExponent = 1)
    (e : K ≃* CatGroup d) : (R : Subgroup X) ≤ K :=
  h.sylow_le_of_not_dvd_card_outer
    (kFactUnitaryThreeOut K d ⟨e⟩ p h.prime h.ne_two (exists_of_isUnitaryIndex hd hn))

theorem card_sylow_of_u3 [Fact p.Prime] (h : D2AlmostSimple p X R A X₀ K)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) (hn : d.1.fieldExponent = 1)
    (e : K ≃* CatGroup d) : Nat.card (R : Subgroup X) = p ^ 3 := by
  have hRK := h.sylow_le_of_u3 hd hn e
  have h3 := kFactUnitaryThreeSylow K d ⟨e⟩ p h.prime h.ne_two
    (exists_of_isUnitaryIndex hd hn) (R.subtype hRK)
  rwa [Sylow.coe_subtype, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv] at h3

theorem centralizer_le_of_u3 [Fact p.Prime] (hKU5 : KFactUnitaryUnipotentCentralizer)
    (h : D2AlmostSimple p X R A X₀ K) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsUnitaryIndex p d) (hn : d.1.fieldExponent = 1) (e : K ≃* CatGroup d) :
    Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ R := by
  have hRK := h.sylow_le_of_u3 hd hn e
  have := h.normal
  intro y hy
  set α : MulAut K := MulAut.conjNormal y
  have hfix : ∀ z ∈ (R.subtype hRK : Subgroup K), α z = z := by
    intro z hz
    refine Subtype.ext ?_
    rw [MulAut.conjNormal_apply]
    exact mul_inv_eq_of_eq_mul (Subgroup.mem_centralizer_iff.mp hy _ hz).symm
  obtain ⟨u, hu, hαu⟩ := hKU5 K p d hd ⟨e⟩ (R.subtype hRK) α hfix
  have hcent : (u : X)⁻¹ * y ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h' := congrArg Subtype.val (DFunLike.congr_fun hαu ⟨k, hk⟩)
    simp only [α, MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h'
    calc k * ((u : X)⁻¹ * y) = (u : X)⁻¹ * ((u : X) * k * (u : X)⁻¹) * y := by group
      _ = (u : X)⁻¹ * (y * k * y⁻¹) * y := by rw [← h']
      _ = (u : X)⁻¹ * y * k := by group
  rw [h.centralizer_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at hcent
  have hu' : (u : X) ∈ (R : Subgroup X) := hu
  exact hcent ▸ hu'

theorem normalizer_eq_of_u3 [Fact p.Prime] (hKU6 : KFactUnitaryBorelMaximal)
    (h : D2AlmostSimple p X R A X₀ K) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsUnitaryIndex p d) (hn : d.1.fieldExponent = 1) (e : K ≃* CatGroup d) :
    Subgroup.normalizer ((R : Subgroup X) : Set X) = X₀ := by
  have hRK := h.sylow_le_of_u3 hd hn e
  have := h.normal
  have hN : Subgroup.normalizer ((R : Subgroup X) : Set X) ≤ X₀ :=
    h.normalizer_le_of_rank _ h.sylow_le R.isPGroup' h.pRank_eq.ge
  have hNK : Subgroup.normalizer (((R.subtype hRK : Subgroup K)) : Set K) ≤ X₀.subgroupOf K := by
    intro k hk
    rw [Sylow.coe_subtype, ← Subgroup.subgroupOf_normalizer_eq hRK] at hk
    exact Subgroup.mem_subgroupOf.mpr (hN (Subgroup.mem_subgroupOf.mp hk))
  have heq : X₀.subgroupOf K = Subgroup.normalizer (((R.subtype hRK : Subgroup K)) : Set K) :=
    ((hKU6 K p d hd ⟨e⟩ (R.subtype hRK)).le_iff.mp hNK).resolve_left fun hK =>
      h.not_le (Subgroup.subgroupOf_eq_top.mp hK)
  have hX₀K : X₀ ⊓ K ≤ Subgroup.normalizer (((R : Subgroup X) ⊓ K : Subgroup X) : Set X) := by
    rintro y ⟨hy₀, hyK⟩
    have hy : (⟨y, hyK⟩ : K) ∈ Subgroup.normalizer (((R.subtype hRK : Subgroup K)) : Set K) :=
      heq ▸ Subgroup.mem_subgroupOf.mpr hy₀
    rw [Sylow.coe_subtype, ← Subgroup.subgroupOf_normalizer_eq hRK] at hy
    rw [inf_eq_left.mpr hRK]
    exact Subgroup.mem_subgroupOf.mp hy
  have hle := le_normalizer_sylow_inf K R (by rw [inf_eq_left.mpr hRK]; exact h.sylow_le) hX₀K
  rw [inf_eq_left.mpr hRK] at hle
  exact le_antisymm hN hle

theorem commutator_eq_of_u3 [Fact p.Prime] (hKU2 : KFactUnitarySylowStructure)
    (h : D2AlmostSimple p X R A X₀ K) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsUnitaryIndex p d) (hn : d.1.fieldExponent = 1) (e : K ≃* CatGroup d) :
    ⁅(R : Subgroup X), (R : Subgroup X)⁆ =
        (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) ∧
      ∀ r ∈ (R : Subgroup X), r ^ p = 1 := by
  have hRK := h.sylow_le_of_u3 hd hn e
  have := h.normal
  obtain ⟨-, hTcomm, hTpow, -⟩ := hKU2 K p d h.ne_two hd ⟨e⟩ (R.subtype hRK)
  have hTK : (R.subtype hRK : Subgroup K).map K.subtype = R :=
    Subgroup.map_subgroupOf_eq_of_le hRK
  refine ⟨?_, fun r hr => ?_⟩
  · rw [← hTK, ← Subgroup.map_commutator, hTcomm]
    ext y
    constructor
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      refine ⟨Subgroup.mem_map_of_mem K.subtype hk1, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hk2 u hu)
    · rintro ⟨hy1, hy2⟩
      obtain ⟨k, hk, rfl⟩ := hy1
      refine ⟨k, ⟨hk, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hy2 u (Subgroup.mem_map_of_mem _ hu))
  · have := hTpow ⟨r, hRK hr⟩ hr
    simpa using congrArg Subtype.val this

theorem card_center_of_u3 [Fact p.Prime] (hKU2 : KFactUnitarySylowStructure)
    (h : D2AlmostSimple p X R A X₀ K) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsUnitaryIndex p d) (hn : d.1.fieldExponent = 1) (e : K ≃* CatGroup d) :
    Nat.card ((R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) :
      Subgroup X) = p :=
  card_inf_centralizer_eq_prime (h.card_sylow_of_u3 hd hn e)
    (h.commutator_eq_of_u3 hKU2 hd hn e).1

theorem dichotomy_of_u3 [Fact p.Prime] (hKU2 : KFactUnitarySylowStructure)
    (hKU5 : KFactUnitaryUnipotentCentralizer) (hKU6 : KFactUnitaryBorelMaximal)
    (h : D2AlmostSimple p X R A X₀ K) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsUnitaryIndex p d) (hn : d.1.fieldExponent = 1) (e : K ≃* CatGroup d)
    {W : Subgroup X} (hWX₀ : W ≤ X₀) (hX₀W : X₀ ≤ Subgroup.normalizer (W : Set X)) :
    W = ⊥ ∨ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ W := by
  have hp : p.Prime := Fact.out
  have hCU := h.centralizer_le_of_u3 hKU5 hd hn e
  have hX₀R : X₀ ≤ Subgroup.normalizer ((R : Subgroup X) : Set X) :=
    (h.normalizer_eq_of_u3 hKU6 hd hn e).ge
  obtain ⟨hcomm, hpow⟩ := h.commutator_eq_of_u3 hKU2 hd hn e
  have hZcard := h.card_center_of_u3 hKU2 hd hn e
  have hRX₀ : (R : Subgroup X) ≤ X₀ := h.sylow_le
  rcases (W ⊓ R).bot_or_nontrivial with hWU | hWU
  · left
    rw [eq_bot_iff]
    intro w hw
    have hwC : w ∈ Subgroup.centralizer ((R : Subgroup X) : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hcW : w * z * w⁻¹ * z⁻¹ ∈ W := by
        have h' := (Subgroup.mem_normalizer_iff.mp (hX₀W (hRX₀ hz)) w⁻¹).mp (W.inv_mem hw)
        simpa only [mul_assoc] using W.mul_mem hw h'
      have hcomm' : w * z * w⁻¹ * z⁻¹ ∈ W ⊓ (R : Subgroup X) := ⟨hcW,
        (R : Subgroup X).mul_mem ((Subgroup.mem_normalizer_iff.mp (hX₀R (hWX₀ hw)) z).mp hz)
          ((R : Subgroup X).inv_mem hz)⟩
      rw [hWU, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hcomm'
      exact hcomm'.symm
    have hwWU : w ∈ W ⊓ (R : Subgroup X) := ⟨hw, hCU hwC⟩
    rwa [hWU] at hwWU
  · right
    have : Group.IsNilpotent (R : Subgroup X) := R.isPGroup'.isNilpotent
    have hNn : ((W ⊓ (R : Subgroup X)).subgroupOf (R : Subgroup X)).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr ?_
      exact (le_inf (hRX₀.trans hX₀W) Subgroup.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hne : (W ⊓ (R : Subgroup X)).subgroupOf (R : Subgroup X) ≠ ⊥ := by
      intro hbot
      obtain ⟨x, hx, hx1⟩ := (Subgroup.nontrivial_iff_exists_ne_one _).mp hWU
      have : (⟨x, hx.2⟩ : (R : Subgroup X)) ∈
          (W ⊓ (R : Subgroup X)).subgroupOf (R : Subgroup X) := Subgroup.mem_subgroupOf.mpr hx
      rw [hbot, Subgroup.mem_bot] at this
      exact hx1 (congrArg Subtype.val this)
    obtain ⟨⟨g, hgW, hgZ⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
    have hg1' : (g : X) ≠ 1 := fun h' => hg1 (Subtype.ext (Subtype.ext h'))
    have hgZ' : (g : X) ∈ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) :=
      ⟨g.2, Subgroup.mem_centralizer_iff.mpr fun u hu =>
        congrArg Subtype.val ((Subgroup.mem_center_iff.mp hgZ) ⟨u, hu⟩)⟩
    have hgW' : (g : X) ∈ W := (Subgroup.mem_subgroupOf.mp hgW).1
    have hord : orderOf (g : X) = p := orderOf_eq_prime (hpow _ g.2) hg1'
    have hzp : Subgroup.zpowers (g : X) =
        (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) := by
      refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hgZ') ?_
      rw [hZcard, Nat.card_zpowers, hord]
    rw [← hzp]
    exact (Subgroup.zpowers_le).mpr hgW'

theorem le_of_isPGroup_of_normal (h : D2AlmostSimple p X R A X₀ K) {W : Subgroup X}
    (hX₀W : X₀ ≤ Subgroup.normalizer (W : Set X)) (hWp : IsPGroup p W) : W ≤ R := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hsup : IsPGroup p (W ⊔ (R : Subgroup X) : Subgroup X) :=
    hWp.to_sup_of_normal_left' R.isPGroup' (h.sylow_le.trans hX₀W)
  exact (R.is_maximal' hsup le_sup_right) ▸ le_sup_left

theorem isSolvable_of_u3 [Fact p.Prime] (hKU6 : KFactUnitaryBorelMaximal)
    (hKU8 : KFactUnitarySylowNormalizerSolvable) (h : D2AlmostSimple p X R A X₀ K)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) (hn : d.1.fieldExponent = 1)
    (e : K ≃* CatGroup d) : Group.IsSolvable X₀ := by
  have hRK := h.sylow_le_of_u3 hd hn e
  have := h.normal
  have hX₀R : X₀ ≤ Subgroup.normalizer ((R : Subgroup X) : Set X) :=
    (h.normalizer_eq_of_u3 hKU6 hd hn e).ge
  have hinj : Function.Injective (MulAut.conjNormal (H := K) : X →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_conjNormal_eq_centralizer, h.centralizer_eq_bot]
  have hA : ∀ α ∈ X₀.map (MulAut.conjNormal (H := K) : X →* MulAut K),
      (R.subtype hRK : Subgroup K).map (α : K ≃* K).toMonoidHom = R.subtype hRK := by
    rintro _ ⟨y, hy, rfl⟩
    refine Subgroup.eq_of_le_of_card_ge (fun z hz => ?_) (by
      rw [Subgroup.card_map_of_injective
        (f := ((MulAut.conjNormal y : K ≃* K)).toMonoidHom) (MulAut.conjNormal y).injective])
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    change ((MulAut.conjNormal y x : K) : X) ∈ (R : Subgroup X)
    rw [MulAut.conjNormal_apply]
    exact (Subgroup.mem_normalizer_iff.mp (hX₀R hy) _).mp hx
  have := hKU8 K p d hd ⟨e⟩ (R.subtype hRK) _ hA
  exact Group.isSolvable_of_isSolvable_injective
    (f := (X₀.equivMapOfInjective _ hinj).toMonoidHom) (X₀.equivMapOfInjective _ hinj).injective

theorem primeComplementCore_eq_bot_of_u3 [Fact p.Prime] (hKU2 : KFactUnitarySylowStructure)
    (hKU5 : KFactUnitaryUnipotentCentralizer) (hKU6 : KFactUnitaryBorelMaximal)
    (h : D2AlmostSimple p X R A X₀ K) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsUnitaryIndex p d) (hn : d.1.fieldExponent = 1) (e : K ≃* CatGroup d) :
    primeComplementCore (G := X₀) p = ⊥ := by
  have hZcard := h.card_center_of_u3 hKU2 hd hn e
  refine primeComplementCore_eq_bot_of_dichotomy
    (Z := (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X))
    (fun W hW hWn => h.dichotomy_of_u3 hKU2 hKU5 hKU6 hd hn e hW hWn)
    (R.isPGroup'.to_inf_left) ?_
  intro hbot
  rw [hbot, Subgroup.card_bot] at hZcard
  exact h.prime.one_lt.ne hZcard

theorem borel_of_u3 [Fact p.Prime] (hKU : UnitaryBorelKFacts) (h : D2AlmostSimple p X R A X₀ K)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) (hn : d.1.fieldExponent = 1)
    (e : K ≃* CatGroup d) :
    Subgroup.normalizer ((R : Subgroup X) : Set X) = X₀ ∧
      Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ R ∧
      Nat.card ((R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) :
        Subgroup X) = p ∧
      ⁅(R : Subgroup X), (R : Subgroup X)⁆ =
        (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) ∧
      (∀ r ∈ (R : Subgroup X), r ^ p = 1) ∧
      (∀ W : Subgroup X, W ≤ X₀ → X₀ ≤ Subgroup.normalizer (W : Set X) →
        W = ⊥ ∨ (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ W) ∧
      (∀ W : Subgroup X, X₀ ≤ Subgroup.normalizer (W : Set X) → IsPGroup p W → W ≤ R) ∧
      Group.IsSolvable X₀ ∧ primeComplementCore (G := X₀) p = ⊥ :=
  ⟨h.normalizer_eq_of_u3 hKU.borelMaximal hd hn e,
    h.centralizer_le_of_u3 hKU.unipotentCentralizer hd hn e,
    h.card_center_of_u3 hKU.sylowStructure hd hn e,
    (h.commutator_eq_of_u3 hKU.sylowStructure hd hn e).1,
    (h.commutator_eq_of_u3 hKU.sylowStructure hd hn e).2,
    fun _ hW hWn => h.dichotomy_of_u3 hKU.sylowStructure hKU.unipotentCentralizer
      hKU.borelMaximal hd hn e hW hWn,
    fun _ hWn hWp => h.le_of_isPGroup_of_normal hWn hWp,
    h.isSolvable_of_u3 hKU.borelMaximal hKU.sylowNormalizerSolvable hd hn e,
    h.primeComplementCore_eq_bot_of_u3 hKU.sylowStructure hKU.unipotentCentralizer
      hKU.borelMaximal hd hn e⟩

end D2AlmostSimple

end Reduced

section Pair

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R : Subgroup G}

theorem AGLPair.ne_bot_R (h : AGLPair p M H R) : R ≠ ⊥ := by
  intro hR
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨T, hT⟩ := h.isSylow
  have hT1 : (T : Subgroup H) = ⊥ := by
    rw [hR] at hT
    exact (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp hT
  have hcop : p.Coprime (Nat.card H) := by
    have := T.not_dvd_index
    rwa [hT1, Subgroup.index_bot, ← Nat.Prime.coprime_iff_not_dvd h.prime] at this
  exact h.not_le ((le_glbPrimeCore le_rfl Subgroup.le_normalizer hcop).trans h.primeCore_le)

theorem AGLJConfig.of_pair (h : AGLPair p M H R)
    (hRQ : ((R ⊔ pCoreOf 2 M).subgroupOf M).Normal)
    (hC : (H ⊓ M) ⊓ Subgroup.centralizer (R : Set G) ≤ R ⊔ GLBPrimeCore p H) :
    AGLJConfig p M H R R where
  pair := h
  le_R := le_rfl
  ne_bot := h.ne_bot_R
  normal_sup := hRQ
  commutator_le := h.commutator_primeCore_le_twoCore le_rfl hRQ
  centralizer_le := hC

end Pair

section Escape

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M A H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D2Escape.card_eq_of_u3 [Fact p.Prime] (h : D2Escape p P M A H R)
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) (hn : d.1.fieldExponent = 1)
    (e : K ≃* CatGroup d) : Nat.card R = p ^ 3 := by
  rw [← h.card_map_eq le_rfl, ← hRbar]
  exact hK.card_sylow_of_u3 hd hn e

theorem D2Escape.toPair_of_u3 [Fact p.Prime] (hKU : UnitaryBorelKFacts)
    (h : D2Escape p P M A H R) (hglob : AGLGlobal G)
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) (hn : d.1.fieldExponent = 1)
    (e : K ≃* CatGroup d) : AGLPair p M H R :=
  h.toPair hglob (h.twoCore_inf_eq_of_primeCore_inf_eq
    (h.primeCore_inf_eq_iff.mpr (hK.primeComplementCore_eq_bot_of_u3 hKU.sylowStructure
      hKU.unipotentCentralizer hKU.borelMaximal hd hn e)))

theorem inf_centralizer_le_of_u3 [Fact p.Prime] (hKU5 : KFactUnitaryUnipotentCentralizer)
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) (hn : d.1.fieldExponent = 1)
    (e : K ≃* CatGroup d) :
    (H ⊓ M) ⊓ Subgroup.centralizer (R : Set G) ≤ R ⊔ GLBPrimeCore p H := by
  have hCX : Subgroup.centralizer (((R.subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) :
          Subgroup (H ⧸ primeComplementCore (G := H) p)) :
          Set (H ⧸ primeComplementCore (G := H) p)) ≤
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
    rw [← hRbar]
    exact hK.centralizer_le_of_u3 hKU5 hd hn e
  rintro y ⟨hyHM, hyC⟩
  refine centralizer_le_of_map (inf_le_right.trans hCX) y hyHM fun x hx => ?_
  have hc := Subgroup.mem_centralizer_iff.mp hyC x hx
  rw [← hc, show x * y * y⁻¹ * x⁻¹ = 1 by group]
  exact one_mem _

theorem D2Escape.aglJConfig_of_u3 [Fact p.Prime] (hKU : UnitaryBorelKFacts)
    (h : D2Escape p P M A H R) (hglob : AGLGlobal G)
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) (hn : d.1.fieldExponent = 1)
    (e : K ≃* CatGroup d) (hRQ : ((R ⊔ pCoreOf 2 M).subgroupOf M).Normal) :
    AGLJConfig p M H R R :=
  AGLJConfig.of_pair (h.toPair_of_u3 hKU hglob hK hd hn e) hRQ
    (inf_centralizer_le_of_u3 hKU.unipotentCentralizer hRbar hK hd hn e)

end Escape

end CFSG.AGLEmbeddingD2
