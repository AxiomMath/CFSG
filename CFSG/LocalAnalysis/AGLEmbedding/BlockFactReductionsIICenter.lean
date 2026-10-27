module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZComp
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeBlocksAux
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.GH74.Generic.GKFCover
public import CFSG.Alternating.Multipliers.Main
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.Adapters.LinearCatalogStated

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)

section Multiplier

theorem isCyclic_of_le_range_of_isPGroup {a b c d : ℕ} {H : Type*} [Group H]
    (ψ : (Multiplicative (ZMod a) × Multiplicative (ZMod b)) ×
      (Multiplicative (ZMod c) × Multiplicative (ZMod d)) →* H)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hN : ¬ ℓ ∣ b * (c * d)) {P : Subgroup H} (hPψ : P ≤ ψ.range)
    (hP : IsPGroup ℓ P) : IsCyclic P := by
  set ι := (MonoidHom.inl (Multiplicative (ZMod a) × Multiplicative (ZMod b))
    (Multiplicative (ZMod c) × Multiplicative (ZMod d))).comp
    (MonoidHom.inl (Multiplicative (ZMod a)) (Multiplicative (ZMod b))) with hι
  have hC : IsCyclic (ψ.comp ι).range :=
    isCyclic_of_surjective (ψ.comp ι).rangeRestrict (ψ.comp ι).rangeRestrict_surjective
  refine Subgroup.isCyclic_of_le (H' := (ψ.comp ι).range) ?_
  intro x hx
  obtain ⟨m, rfl⟩ := hPψ hx
  have hcard : ∀ k : ℕ, ∀ y : Multiplicative (ZMod k), y ^ k = 1 := by
    intro k y
    have := pow_card_eq_one' (G := Multiplicative (ZMod k)) (x := y)
    rwa [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at this
  have hmN : m ^ (b * (c * d)) = ι (m.1.1 ^ (b * (c * d))) := by
    have h2 : m.1.2 ^ (b * (c * d)) = 1 := by rw [pow_mul, hcard b, one_pow]
    have h3 : m.2.1 ^ (b * (c * d)) = 1 := by
      rw [show b * (c * d) = c * (b * d) by ring, pow_mul, hcard c, one_pow]
    have h4 : m.2.2 ^ (b * (c * d)) = 1 := by
      rw [show b * (c * d) = d * (b * c) by ring, pow_mul, hcard d, one_pow]
    ext <;> simp [hι, h2, h3, h4]
  obtain ⟨k, hk⟩ := hP ⟨ψ m, hx⟩
  have hk' : (ψ m) ^ ℓ ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : (b * (c * d)).Coprime (orderOf (ψ m)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk')
      (Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hN).symm)
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hj, ← map_pow, hmN]
  exact Subgroup.pow_mem _ (MonoidHom.mem_range.mpr ⟨m.1.1 ^ (b * (c * d)), rfl⟩) j

theorem isCyclic_of_le_center_of_lieModel
    (hGA : CFSG.Open.GriessAllModelsStatement) {A X : Type}
    [Group A] [Group.IsPerfect A] [Group X] (e : A ⧸ Subgroup.center A ≃* X)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (hm : CFSG.Models.LieModel X t n p f) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hN : ¬ ℓ ∣ (genericOrders t n p f).2 *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2))
    {P : Subgroup A} (hPZ : P ≤ Subgroup.center A) (hP : IsPGroup ℓ P) : IsCyclic P := by
  set q := CFSG.GH74.Generic.centralQuotientMap e
  have hqs := CFSG.GH74.Generic.centralQuotientMap_surjective e
  have hker := CFSG.GH74.Generic.centralQuotientMap_ker e
  obtain ⟨-, ⟨g⟩⟩ := hGA X t n p f hm
  have hψ₀ := CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q hqs hker.le
  let ψ := q.ker.subtype.comp
    ((CFSG.RankThree.PerfectCover.hopfMultiplierToKer q hqs hker.le).comp
      ((CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).toMonoidHom.comp
        g.symm.toMonoidHom))
  refine isCyclic_of_le_range_of_isPGroup ψ hℓ hN ?_ hP
  intro x hx
  have hxk : x ∈ q.ker := hker ▸ hPZ hx
  obtain ⟨m, hm⟩ := hψ₀ ⟨x, hxk⟩
  refine ⟨g ((CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).symm m), ?_⟩
  simp [ψ, hm]

theorem exceptionalOrders_mul_dvd_sixteen_of_two (t : CFSG.Assembly.LowTwoRank.StatedLieTag)
    (n f : ℕ) : (exceptionalOrders t n 2 f).1 * (exceptionalOrders t n 2 f).2 ∣ 16 := by
  unfold exceptionalOrders
  split <;> first | omega | norm_num

theorem genericOrders_snd_eq_one_of_two (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n f : ℕ)
    (hf : 1 ≤ f) : (genericOrders t n 2 f).2 = 1 := by
  have hq : Even (2 ^ f) := (Nat.even_pow' (by omega)).mpr even_two
  cases t <;> simp [genericOrders, hq]

theorem not_dvd_multiplierOrders_of_two (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n f : ℕ)
    (hf : 1 ≤ f) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) :
    ¬ ℓ ∣ (genericOrders t n 2 f).2 *
      ((exceptionalOrders t n 2 f).1 * (exceptionalOrders t n 2 f).2) := by
  rw [genericOrders_snd_eq_one_of_two t n f hf, one_mul]
  intro h
  have h16 : ℓ ∣ 2 ^ 4 := h.trans (exceptionalOrders_mul_dvd_sixteen_of_two t n f)
  exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hℓ.dvd_of_dvd_pow h16))

theorem isCyclic_of_le_center_of_alternating {A : Type} [Group A]
    [Finite A] [Group.IsPerfect A] {m : ℕ} (hm : 5 ≤ m)
    (e : A ⧸ Subgroup.center A ≃* alternatingGroup (Fin m)) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    {P : Subgroup A} (hPZ : P ≤ Subgroup.center A) (hP : IsPGroup ℓ P) : IsCyclic P := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hdvd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier inferInstance
    (CFSG.GH74.Generic.centralQuotientMap e) (CFSG.GH74.Generic.centralQuotientMap_surjective e)
    (CFSG.GH74.Generic.centralQuotientMap_ker e).le
  rw [CFSG.GH74.Generic.centralQuotientMap_ker e,
    (CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput m hm).2] at hdvd
  have h6 : Nat.card (Subgroup.center A) ∣ 6 := by
    split_ifs at hdvd
    · exact hdvd
    · exact hdvd.trans (by norm_num)
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hPc : ℓ ^ k ∣ 2 * 3 := hk ▸ (Subgroup.card_dvd_of_le hPZ).trans h6
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have hℓ2' : ℓ ^ 2 ∣ 2 * 3 := (pow_dvd_pow ℓ (by omega)).trans hPc
    have h3 : ℓ ∣ 3 := by
      rcases (Nat.Prime.dvd_mul hℓ).mp (dvd_trans (dvd_pow_self ℓ two_ne_zero) hℓ2') with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h) hℓ2
      · exact h
    have hℓ3 : ℓ = 3 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp h3
    subst hℓ3
    norm_num at hℓ2'
  interval_cases k
  · have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
    exact isCyclic_of_subsingleton
  · exact isCyclic_of_prime_card (by simpa using hk)

open TauCeti in
theorem statedClassicalModel_of_typeA {K : Type} [Group K] {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.A r q).Valid) (e : K ≃* ValidLieTypeIndex.Group ⟨.A r q, hv⟩) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSL (r + 1) q.p q.exponent :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e

end Multiplier

@[expose] def KFactCenterOddCyclic : Prop :=
  ∀ (A : Type) [Group A] [Finite A], CFSG.Open.IsQuasisimple A →
    (IsClassicalTwoOrG2 (A ⧸ Subgroup.center A) ∨
      ∃ m : ℕ, Nonempty (A ⧸ Subgroup.center A ≃* alternatingGroup (Fin m))) →
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ∀ P : Subgroup A, P ≤ Subgroup.center A → IsPGroup ℓ P →
      IsCyclic P

open TauCeti in
theorem kFactCenterOddCyclic_of_griess
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    KFactCenterOddCyclic := by
  intro A _ _ hq hA ℓ hℓ hℓ2 P hPZ hP
  have : Group.IsPerfect A := Group.isPerfect_def.mpr hq.1
  have : Nontrivial (A ⧸ Subgroup.center A) := hq.2.toNontrivial
  rcases hA with ((⟨⟨d, hv⟩, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨⟨d, hv⟩, hd, ⟨e⟩⟩) | ⟨m, hm⟩)
  · have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
    have key : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n f : ℕ}, 1 ≤ f →
        CFSG.Models.LieModel (CFSGIndex.lie ⟨d, hv⟩).Group t n 2 f → IsCyclic P :=
      fun hf hm => isCyclic_of_le_center_of_lieModel hGA e hm hℓ
        (not_dvd_multiplierOrders_of_two _ _ _ hf hℓ hℓ2) hPZ hP
    cases d
    case A r q =>
      have hc := statedClassicalModel_of_typeA hv (MulEquiv.refl _)
      have hm : CFSG.Models.LieModel _ _ _ _ _ := ⟨hc.1, Or.inl hc⟩
      rw [show q.p = 2 from hd] at hm
      exact key q.exponent_pos hm
    case twistedA r q =>
      have hc :=
        CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _)
      have hm : CFSG.Models.LieModel _ _ _ _ _ := ⟨hc.1, Or.inl hc⟩
      rw [show q.p = 2 from hd] at hm
      exact key q.exponent_pos hm
    case B r q =>
      rcases (show r = 2 ∨ 3 ≤ r by have : 2 ≤ r := hrange.1; omega) with rfl | hr3
      · have hc :=
          CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv (MulEquiv.refl _)
        have hm : CFSG.Models.LieModel _ _ _ _ _ := ⟨hc.1, Or.inl hc⟩
        rw [show q.p = 2 from hd] at hm
        exact key q.exponent_pos hm
      · have hc :=
          CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd hr3
            (MulEquiv.refl _)
        have hm : CFSG.Models.LieModel _ _ _ _ _ := ⟨hc.1, Or.inl hc⟩
        rw [show q.p = 2 from hd] at hm
        exact key q.exponent_pos hm
    case D r q =>
      have hc :=
        CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv (MulEquiv.refl _)
      have hm : CFSG.Models.LieModel _ _ _ _ _ := ⟨hc.1, Or.inl hc⟩
      rw [show q.p = 2 from hd] at hm
      exact key q.exponent_pos hm
    case twistedD r q =>
      have hc :=
        CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv
          (MulEquiv.refl _)
      have hm : CFSG.Models.LieModel _ _ _ _ _ := ⟨hc.1, Or.inl hc⟩
      rw [show q.p = 2 from hd] at hm
      exact key q.exponent_pos hm
    case G2 q =>
      have h3q : 3 ≤ q.p ^ q.exponent := by simpa only [PrimePower.card_def] using hrange
      have hm : CFSG.Models.LieModel (CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2 0 q.p q.exponent :=
        ⟨⟨q.prime_p, q.exponent_pos, rfl, h3q⟩,
          Or.inr ⟨rfl, ⟨.G2 q, hv⟩, ⟨rfl, rfl⟩, ⟨MulEquiv.refl _⟩⟩⟩
      rw [show q.p = 2 from hd] at hm
      exact key q.exponent_pos hm
    all_goals exact absurd hd (by simp [IsClassicalOrG2Index])
  · exact isCyclic_of_le_center_of_alternating (by omega) e hℓ hℓ2 hPZ hP
  · rcases hd with ⟨q, hq7, rfl⟩ | ⟨q, hq3, rfl⟩
    · have hq' : q.p = 7 ∧ q.exponent = 1 := by
        rw [PrimePower.card_def] at hq7
        exact (by norm_num : Nat.Prime 7).pow_eq_iff.mp hq7
      have hc := statedClassicalModel_of_typeA hv (MulEquiv.refl _)
      have hm : CFSG.Models.LieModel _ _ _ _ _ := ⟨hc.1, Or.inl hc⟩
      rw [hq'.1, hq'.2] at hm
      refine isCyclic_of_le_center_of_lieModel hGA e hm hℓ ?_ hPZ hP
      simp [genericOrders, exceptionalOrders, hℓ.ne_one]
    · have hq' : q.p = 3 ∧ q.exponent = 1 := by
        rw [PrimePower.card_def] at hq3
        exact Nat.prime_three.pow_eq_iff.mp hq3
      have hc :=
        CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv (MulEquiv.refl _)
      have hm : CFSG.Models.LieModel _ _ _ _ _ := ⟨hc.1, Or.inl hc⟩
      rw [hq'.1, hq'.2] at hm
      refine isCyclic_of_le_center_of_lieModel hGA e hm hℓ ?_ hPZ hP
      simp [genericOrders, exceptionalOrders, hℓ.ne_one]
  · obtain ⟨e⟩ := hm
    exact isCyclic_of_le_center_of_alternating
      (five_le_of_isPerfect_mulEquiv_alternatingGroup e) e hℓ hℓ2 hPZ hP

theorem kFactBlockCenterCyclic_of_oddCyclic (h93 : Asc81bNineThree)
    (h : KFactCenterOddCyclic) : KFactBlockCenterCyclic := by
  intro G _ _ M S L hK hA hL hX hS p hp hp2 A hAL hAC hAp
  have hq := hL.component.2.2
  have hperf : Group.IsPerfect (barM M L) := ⟨hq.1⟩
  have : Nontrivial (barM M L ⧸ Subgroup.center (barM M L)) := hq.2.toNontrivial
  have : Nontrivial (barM M L) :=
    (QuotientGroup.mk'_surjective (Subgroup.center (barM M L))).nontrivial
  have hnab : ∃ a b : ↥(barM M L), a * b ≠ b * a := by
    by_contra hcon
    have : IsMulCommutative (barM M L) :=
      ⟨⟨fun a b => of_not_not fun h => hcon ⟨a, b, h⟩⟩⟩
    exact Group.IsPerfect.not_isMulCommutative (barM M L) this
  have hA'Z : A.subgroupOf (barM M L) ≤ Subgroup.center (barM M L) := by
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro b
    exact Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (hAC (Subgroup.mem_subgroupOf.mp ha)) b b.2)
  have hA'p : IsPGroup p (A.subgroupOf (barM M L)) := hAp.comap_subtype
  suffices hc : IsCyclic (A.subgroupOf (barM M L)) from
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hAL).toMonoidHom (MulEquiv.surjective _)
  have hbot : Subgroup.center (barM M L) = ⊥ → IsCyclic (A.subgroupOf (barM M L)) := by
    intro hZ
    rw [hZ, le_bot_iff] at hA'Z
    rw [hA'Z]
    exact isCyclic_of_subsingleton
  rcases h93 G M S L hK hA hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · exact h _ hq (Or.inl h2.1) p hp hp2 _ hA'Z hA'p
  · exact hbot (center_eq_bot_of_isOrthogonalTwo hperf hnab h3.2.1)
  · have hdvd : Nat.card (A.subgroupOf (barM M L)) ∣ 3 :=
      h4.2.1 ▸ Subgroup.card_dvd_of_le hA'Z
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · have : Subsingleton (A.subgroupOf (barM M L)) := (Nat.card_eq_one_iff_unique.mp h1).1
      exact isCyclic_of_subsingleton
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact isCyclic_of_prime_card h3
  · obtain ⟨φ⟩ := h5.2.1
    exact hbot (center_eq_bot_of_mulEquiv_alternating hnab φ)
  · obtain ⟨-, n, hn, -⟩ := h6
    exact h _ hq (Or.inr ⟨2 * n, hn⟩) p hp hp2 _ hA'Z hA'p
  · obtain ⟨-, n, ⟨φ⟩, -⟩ := h7
    exact hbot (center_eq_bot_of_mulEquiv_alternating hnab φ)
  · obtain ⟨-, N, r, -, -, -, -, -, ⟨φ⟩, -⟩ := h8
    exact hbot (center_eq_bot_of_mulEquiv_alternating hnab φ)

theorem kFactBlockCenterCyclic_of_griess
    (h93 : Asc81bNineThree)
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    KFactBlockCenterCyclic :=
  kFactBlockCenterCyclic_of_oddCyclic h93 (kFactCenterOddCyclic_of_griess hGA)

end CFSG.AGLEmbedding
