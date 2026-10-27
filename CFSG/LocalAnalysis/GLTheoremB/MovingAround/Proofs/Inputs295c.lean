module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs295b
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankOne
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62AutElemRank
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaEightMinusElemRank
public import Certificates.Certificate29530
import CFSG.Assembly.ComponentFreeOddCores
import CFSG.CGT.PushingUpLit.BHS5.FiveSixGrp

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295c

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.HardMathSupport.Dickson.Bal207.D42Tri

theorem genOf_k2_eq :
    genOf 360 (k2Tbls ()) = CFSG.Sporadic.Schreier.centralizerIn
      CFSG.EvenSmallLie.OmegaEight.omegaT t2Perm := by
  obtain ⟨hK, hKcard⟩ := k2_spec
  exact Subgroup.eq_of_le_of_card_ge hK (by rw [card_centralizer_t2, hKcard])

theorem d42T2NoNine_holds :
    Inputs295.D42T2NoNine := by
  intro g hg h9
  rw [← genOf_k2_eq] at hg
  exact Certificates.certificate29530 g hg h9

section Facts

open CFSG.HardMathSupport.Solomon.Coordinator (IsChevOfChar fixSubgroup)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
  (isPSolvable_of_mulEquiv)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
  (isPSolvable_of_le isPSolvable_of_normal)

@[expose] def OuterExcl295 {K : Type} [Group K] [Finite K] (α : MulAut K) : Prop :=
  (∃ P : Subgroup K, P ≤ fixSubgroup α ∧ IsPGroup 3 ↥P ∧ 3 ^ 4 ≤ Nat.card P) ∨
    3 ≤ CFSG.Open.pRank 3 (fixSubgroup α) ∨ ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixSubgroup α)

@[expose] def Outer295At (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → CFSG.Open.IsKGroup K →
    ¬ IsChevOfChar 3 K → 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) →
    ∀ α : MulAut K, α ^ 3 = 1 → α ∉ (MulAut.conj : K →* MulAut K).range → OuterExcl295 α

@[expose] def Inner295At (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → CFSG.Open.IsKGroup K →
    ¬ IsChevOfChar 3 K → 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) →
    ∀ x : K, orderOf x = 3 → Inputs295.Excl295At x

theorem false_of_excl295At {X : Type} [Group X] [Finite X] {x : X} (h : Inputs295.Excl295At x)
    (hC4 : ∀ S : Subgroup X, S ≤ Subgroup.centralizer ({x} : Set X) → IsPGroup 3 ↥S →
      Nat.card S ≤ 3 ^ 4)
    (hrk3 : CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set X)) = 3)
    (hsolv : CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.centralizer ({x} : Set X))) : False := by
  rcases h with ⟨P, hP, hPp, hPc⟩ | hr | hs
  · exact absurd (hPc.trans (hC4 P hP hPp)) (by norm_num)
  · omega
  · exact hs hsolv

theorem fixSubgroup_conjNormal {X : Type} [Group X] {L : Subgroup X} [L.Normal] (x : X) :
    fixSubgroup (MulAut.conjNormal x : MulAut ↥L) =
      (L ⊓ Subgroup.centralizer ({x} : Set X)).subgroupOf L := by
  ext s
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, Subgroup.mem_subgroupOf,
    Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hs
    refine ⟨s.2, ?_⟩
    have h1 := congrArg Subtype.val hs
    simp only [MulAut.conjNormal_apply] at h1
    calc (s : X) * x = x * s * x⁻¹ * x := by rw [h1]
      _ = x * s := by group
  · rintro ⟨-, hs⟩
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply]
    rw [← hs]
    group

theorem isElemAbelian_zpowers {X : Type} [Group X] {x : X} (hx3 : x ^ 3 = 1) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers x) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun z hz => ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]

theorem commute_of_le_centralizer {X : Type} [Group X] {x : X} {Q : Subgroup X}
    (hQ : Q ≤ Subgroup.centralizer ({x} : Set X)) :
    ∀ a ∈ Q, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
  intro a ha b hb
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  exact Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 (hQ ha)) i

theorem exists_pGroup_sup_zpowers {X : Type} [Group X] [Finite X] {x : X} (hx3 : x ^ 3 = 1)
    {Q : Subgroup X} (hQ : Q ≤ Subgroup.centralizer ({x} : Set X)) (hQp : IsPGroup 3 ↥Q)
    (hxQ : x ∉ Q) {k : ℕ} (hk : Nat.card Q = 3 ^ k) :
    Q ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({x} : Set X) ∧
      IsPGroup 3 ↥(Q ⊔ Subgroup.zpowers x) ∧ 3 ^ (k + 1) ≤ Nat.card ↥(Q ⊔ Subgroup.zpowers x) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxC : x ∈ Subgroup.centralizer ({x} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxp : IsPGroup 3 ↥(Subgroup.zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h ▸ Q.one_mem) hxQ
    · exact h)
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (Q : Set X) :=
    (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun q hq =>
      Subgroup.mem_centralizer_singleton_iff.1 (hQ hq))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hp : IsPGroup 3 ↥(Q ⊔ Subgroup.zpowers x) := IsPGroup.to_sup_of_normal_left' hQp hxp hnorm
  refine ⟨sup_le hQ (by rw [Subgroup.zpowers_le]; exact hxC), hp, ?_⟩
  obtain ⟨m, hm⟩ := hp.exists_card_eq
  have hlt : Nat.card Q < Nat.card ↥(Q ⊔ Subgroup.zpowers x) := by
    refine Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_left fun heq => hxQ ?_)
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  rw [hk, hm] at hlt
  rw [hm]
  exact Nat.pow_le_pow_right (by norm_num) ((Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt)

theorem false_of_outerExcl295 {X : Type} [Group X] [Finite X] {L : Subgroup X} [L.Normal] {x : X}
    (hxL : x ∉ L) (hx3 : x ^ 3 = 1) (h : OuterExcl295 (MulAut.conjNormal x : MulAut ↥L))
    (hC4 : ∀ S : Subgroup X, S ≤ Subgroup.centralizer ({x} : Set X) → IsPGroup 3 ↥S →
      Nat.card S ≤ 3 ^ 4)
    (hrk3 : CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set X)) = 3)
    (hsolv : CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.centralizer ({x} : Set X))) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold OuterExcl295 at h
  rw [fixSubgroup_conjNormal] at h
  have himg : ∀ P : Subgroup ↥L,
      P ≤ (L ⊓ Subgroup.centralizer ({x} : Set X)).subgroupOf L →
        P.map L.subtype ≤ L ⊓ Subgroup.centralizer ({x} : Set X) := by
    intro P hP z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
    exact Subgroup.mem_subgroupOf.1 (hP hy)
  have hxP : ∀ P : Subgroup ↥L, x ∉ P.map L.subtype := by
    intro P hx
    obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 hx
    exact hxL (hy ▸ y.2)
  rcases h with ⟨P, hP, hPp, hPc⟩ | hr | hs
  ·
    obtain ⟨k, hk⟩ := (hPp.map L.subtype).exists_card_eq
    have hk' : Nat.card P = 3 ^ k := by
      rw [← hk, Subgroup.card_map_of_injective L.subtype_injective]
    have hk4 : 4 ≤ k := by
      rw [hk'] at hPc
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hPc
    obtain ⟨hQC, hQp, hQc⟩ := exists_pGroup_sup_zpowers hx3 ((himg P hP).trans inf_le_right)
      (hPp.map L.subtype) (hxP P) hk
    have h1 := hC4 _ hQC hQp
    have h2 : 3 ^ 5 ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact absurd (h2.trans (hQc.trans h1)) (by norm_num)
  ·
    obtain ⟨E, hEC, hEa, hEc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
      ((L ⊓ Subgroup.centralizer ({x} : Set X)).subgroupOf L)
    set k := CFSG.Open.pRank 3 ((L ⊓ Subgroup.centralizer ({x} : Set X)).subgroupOf L)
    have hE'a : CFSG.Open.IsElemAbelian 3 (E.map L.subtype) :=
      CFSG.SectionRank.isElemAbelian_map hEa _
    have hE'C : E.map L.subtype ≤ Subgroup.centralizer ({x} : Set X) :=
      (himg E hEC).trans inf_le_right
    have hE'c : Nat.card (E.map L.subtype) = 3 ^ k := by
      rw [Subgroup.card_map_of_injective L.subtype_injective, hEc]
    have hE'p : IsPGroup 3 ↥(E.map L.subtype) := fun g =>
      ⟨1, Subtype.ext (by simpa using hE'a.2 g g.2)⟩
    obtain ⟨hAC, -, hAc⟩ := exists_pGroup_sup_zpowers hx3 hE'C hE'p (hxP E) hE'c
    have hA : CFSG.Open.IsElemAbelian 3 (E.map L.subtype ⊔ Subgroup.zpowers x) :=
      CFSG.Open.IsElemAbelian.sup_of_commute hE'a (isElemAbelian_zpowers hx3)
        (commute_of_le_centralizer hE'C)
    have hAp : IsPGroup 3 ↥(E.map L.subtype ⊔ Subgroup.zpowers x) := fun g =>
      ⟨1, Subtype.ext (by simpa using hA.2 g g.2)⟩
    obtain ⟨m, hm⟩ := hAp.exists_card_eq
    have hkm : k + 1 ≤ m := by
      rw [hm] at hAc
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hAc
    have := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hAC hA hm
    omega
  ·
    exact hs (isPSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
      (isPSolvable_of_le hsolv inf_le_right))

theorem lieIndexChar_eq_characteristic (d : TauCeti.LieTypeIndex) :
    CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar d = d.characteristic := by
  cases d <;> simp [CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar]

theorem characteristic_ne_three {Q : Type} [Group Q] {d : TauCeti.ValidLieTypeIndex}
    (e : Q ≃* (TauCeti.CFSGIndex.lie d).Group) (h : ¬ IsChevOfChar 3 Q) :
    d.1.characteristic ≠ 3 := by
  intro h3
  refine h
    ⟨d, CFSG.HardMathSupport.Solomon.Coordinator.YS08.isChevIndexOfChar_of_lieIndexChar_eq ?_, ⟨e⟩⟩
  rw [lieIndexChar_eq_characteristic]
  exact h3

theorem false_of_at {X : Type} [Group X] [Finite X] {L : Subgroup X} (hLn : L.Normal)
    (hq : CFSG.Open.IsQuasisimple ↥L) (hK : CFSG.Open.IsKGroup ↥L)
    (hC : ∀ g : X, (∀ l ∈ L, g * l = l * g) → g = 1) {d : TauCeti.ValidLieTypeIndex}
    (he : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hchev : ¬ IsChevOfChar 3 (↥L ⧸ Subgroup.center ↥L))
    (hrk : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) {x : X} (hx : orderOf x = 3)
    (hC4 : ∀ S : Subgroup X, S ≤ Subgroup.centralizer ({x} : Set X) → IsPGroup 3 ↥S →
      Nat.card S ≤ 3 ^ 4)
    (hrk3 : CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set X)) = 3)
    (hsolv : CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.centralizer ({x} : Set X)))
    (hO : Outer295At d) (hI : Inner295At d) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hLn
  have hZ : Subgroup.center ↥L = ⊥ := Inputs295.center_eq_bot_of_cent hC
  obtain ⟨e⟩ := he
  let eQ : ↥L ≃* (↥L ⧸ Subgroup.center ↥L) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2
  haveI hs : IsSimpleGroup ↥L := eQ.isSimpleGroup
  have hnab : ∃ a b : ↥L, a * b ≠ b * a :=
    CFSG.CGT.PushingUpLit.BHS5.exists_noncomm_of_isQuasisimple hq
  have hchevL : ¬ IsChevOfChar 3 ↥L := fun ⟨d', hd', ⟨f⟩⟩ => hchev ⟨d', hd', ⟨eQ.symm.trans f⟩⟩
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hinj : Function.Injective (MulAut.conjNormal : X →* MulAut ↥L) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [Subgroup.mem_bot]
    refine hC g fun l hl => ?_
    have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨l, hl⟩ : ↥L) : X)) hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc g * l = g * l * g⁻¹ * g := by group
      _ = l * g := by rw [h1]
  have hrkA : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥L)) :=
    hrk.trans (CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) _ hinj)
  by_cases hxL : x ∈ L
  · have hxo : orderOf (⟨x, hxL⟩ : ↥L) = 3 := by
      rw [← hx, ← Subgroup.orderOf_coe]
    exact false_of_excl295At (Inputs295.Excl295At.of_subgroup hxL
      (hI ↥L hs hnab ⟨eQ.trans e⟩ hK hchevL hrkA ⟨x, hxL⟩ hxo)) hC4 hrk3 hsolv
  · have hα3 : (MulAut.conjNormal x : MulAut ↥L) ^ 3 = 1 := by
      rw [← map_pow, hx3, map_one]
    have hout : (MulAut.conjNormal x : MulAut ↥L) ∉ (MulAut.conj : ↥L →* MulAut ↥L).range := by
      rintro ⟨l, hl⟩
      apply hxL
      have hc : ∀ m ∈ L, ((l : X)⁻¹ * x) * m = m * ((l : X)⁻¹ * x) := by
        intro m hm
        have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨m, hm⟩ : ↥L) : X)) hl
        simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
          Subgroup.coe_inv] at h1
        calc (l : X)⁻¹ * x * m = (l : X)⁻¹ * (x * m * x⁻¹) * x := by group
          _ = (l : X)⁻¹ * ((l : X) * m * (l : X)⁻¹) * x := by rw [h1]
          _ = m * ((l : X)⁻¹ * x) := by group
      have h1 := hC _ hc
      rw [inv_mul_eq_one] at h1
      rw [← h1]
      exact l.2
    exact false_of_outerExcl295 hxL hx3
      (hO ↥L hs hnab ⟨eQ.trans e⟩ hK hchevL hrkA _ hα3 hout) hC4 hrk3 hsolv

theorem input29_5'LieTwo_of_at
    (h : ∀ d : TauCeti.ValidLieTypeIndex,
      Inputs295.IsClassicalTwoIndex (TauCeti.CFSGIndex.lie d) →
      ¬ CFSG.LocalAnalysis.GLTheoremA.S9.isD4two (TauCeti.CFSGIndex.lie d) →
        Outer295At d ∧ Inner295At d) :
    Inputs295.Input29_5'LieTwo := by
  intro X _ _ L hLn hq hK hC d he h2 h42 hchev hrk x hx hC4 hrk3 hsolv
  obtain ⟨hO, hI⟩ := h d h2 h42
  exact false_of_at hLn hq hK hC he hchev hrk hx hC4 hrk3 hsolv hO hI

theorem input29_5'LieOther_of_at
    (h : ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic ≠ 3 →
      ¬ Inputs295.IsClassicalTwoIndex (TauCeti.CFSGIndex.lie d) →
        Outer295At d ∧ Inner295At d) :
    Inputs295.Input29_5'LieOther := by
  intro X _ _ L hLn hq hK hC d he h2 hchev hrk x hx hC4 hrk3 hsolv
  obtain ⟨e⟩ := he
  obtain ⟨hO, hI⟩ := h d (characteristic_ne_three e hchev) h2
  exact false_of_at hLn hq hK hC ⟨e⟩ hchev hrk hx hC4 hrk3 hsolv hO hI

theorem at_of_pRank_mulAut_le {d : TauCeti.ValidLieTypeIndex}
    (h : ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 3) :
    Outer295At d ∧ Inner295At d :=
  ⟨fun K _ _ hs hnab he _ _ h4 => absurd (h K hs hnab he) (by omega),
    fun K _ _ hs hnab he _ _ h4 => absurd (h K hs hnab he) (by omega)⟩

theorem pRank_le_two_of_noE27 {G : Type} [Group G] [Finite G]
    (h : ∀ E : Subgroup G, CFSG.Open.IsElemAbelian 3 E → Nat.card E ≠ 27) :
    CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.SectionRank.pRank_le (p := 3) (by norm_num) fun E _ hE => ?_
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  rw [hk]
  by_contra hlt
  have hk3 : 3 ≤ k := by
    by_contra h'
    exact hlt (Nat.pow_le_pow_right (by norm_num) (by omega))
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) 3 (n := 3)
    (by rw [hk]; exact pow_dvd_pow 3 hk3)
  refine h (F.map E.subtype) (hE.mono (Subgroup.map_subtype_le F)) ?_
  rw [Subgroup.card_map_of_injective E.subtype_injective, hF]
  norm_num

end Facts

section Vacuous

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem at_of_rankOne {d : TauCeti.ValidLieTypeIndex} (hch : d.1.characteristic ≠ 3)
    (hd : IsRankOneIndex d.1) : Outer295At d ∧ Inner295At d :=
  at_of_pRank_mulAut_le fun K _ _ hs hnab he =>
    (rankOneAut_holds d hch hd K hs hnab he).trans (by norm_num)

theorem at_of_linThree {d : TauCeti.ValidLieTypeIndex}
    (hd : CFSG.LocalAnalysis.RankThreeTheoremC.IsLinThreeCover3 d) :
    Outer295At d ∧ Inner295At d := by
  refine at_of_pRank_mulAut_le fun K _ _ _ _ ⟨e⟩ => ?_
  obtain ⟨dd, hv⟩ := d
  rcases hd with ⟨q, hq, h3⟩ | ⟨q, hq, h3⟩
  · change dd = .A 2 q at hq
    subst hq
    refine pRank_mulAut_le_of_model
      (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e) (Or.inl rfl)
      (by norm_num) Nat.prime_three (by norm_num) ?_
    show 3 ∣ Nat.gcd (2 + 1) (q.p ^ q.exponent - 1)
    exact Nat.dvd_gcd (dvd_refl 3) (by rwa [← TauCeti.PrimePower.card_def])
  · change dd = .twistedA 2 q at hq
    subst hq
    refine pRank_mulAut_le_of_model
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e) (Or.inr rfl)
      (by norm_num) Nat.prime_three (by norm_num) ?_
    show 3 ∣ Nat.gcd (2 + 1) (q.p ^ q.exponent + 1)
    exact Nat.dvd_gcd (dvd_refl 3) (by rwa [← TauCeti.PrimePower.card_def])

theorem pRank_mulAut_le_three_of_chain {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a)
    (hE : ∀ E : Subgroup K, CFSG.Open.IsElemAbelian 3 E → Nat.card E ≠ 27)
    (hc : CFSG.RankThree.PartOne.OutStructure.OutPChain 3 K) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 3 := by
  have h1 := pRank_mulAut_le_of_outPChain Nat.prime_three
    (GL83.I713.center_eq_bot_of_simple hnab) hc
  have h2 := pRank_le_two_of_noE27 hE
  omega

theorem at_of_suzuki (m : ℕ)
    (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) :
    Outer295At ⟨.suzuki m, hv⟩ ∧ Inner295At ⟨.suzuki m, hv⟩ := by
  refine at_of_pRank_mulAut_le fun K _ _ _ _ ⟨e⟩ => ?_
  refine CFSG.SectionRank.pRank_le (p := 3) (by norm_num) fun E _ hE => ?_
  have hdvd := CFSG.RankThree.PartTwo.KFacts.KP7.card_dvd_three_of_pow_three
    (CFSG.HardMathSupport.Cooperstein.Coordinator.suzukiModel_of_lie hv e) hE.2
  exact (Nat.le_of_dvd (by norm_num) hdvd).trans (by norm_num)

@[expose] def IsBig295Index (d : TauCeti.LieTypeIndex) : Prop :=
  IsRankThreeIndex d ∨ IsRankFourIndex d ∨
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.I294CrossIsExcBig d

theorem inner295At_D4 (hD4 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.InputD4)
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid) :
    Inner295At ⟨.D 4 q, hv⟩ := by
  intro K _ _ hs hnab ⟨e⟩ hK hchev _ x hx
  haveI := hs
  have hch : q.p ≠ 3 := by
    have := characteristic_ne_three e hchev
    simpa using this
  have hZ : Subgroup.center K = ⊥ := GL83.I713.center_eq_bot_of_simple hnab
  let eQ : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hType : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.IsD4Type K :=
    ⟨q.p, q.exponent, hch, CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eQ
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 q hv e)⟩
  have hqO : CFSG.Open.IsQuasisimple K :=
    ⟨CFSG.Assembly.Dichotomy.commutator_eq_top_of_isSimpleGroup hnab, eQ.symm.isSimpleGroup⟩
  have hq' : CFSG.IsQuasisimple K := ⟨⟨hqO.1⟩, hqO.2,
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hqO⟩
  have hK' : CFSG.IsKGroup K := CFSG.KCore.KGroupNonab.kGroupAllSimple
    CFSG.Assembly.inCatalog_isoInvariant CFSG.Assembly.inCatalog_containsAbelianSimple hK
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; norm_num at hx
  exact Or.inr (Or.inl ((hD4 K hq' hK' hType).2 x hx3 hx1))

theorem at_of_sp62 {d : TauCeti.ValidLieTypeIndex}
    (hd : CFSG.AGLEmbedding.IsSpSixTwoIndex d) : Outer295At d ∧ Inner295At d :=
  at_of_pRank_mulAut_le fun K _ _ _ _ he => CFSG.AGLEmbedding.kFactSp62AutElemRank K d hd he

theorem at_of_omegaMinusTwo {d : TauCeti.ValidLieTypeIndex}
    (hd : CFSG.AGLEmbedding.IsOmegaMinusTwoIndex 4 d) : Outer295At d ∧ Inner295At d :=
  at_of_pRank_mulAut_le fun K _ _ _ _ he => CFSG.SectionRank.pRank_le (p := 3) (by norm_num)
    fun E _ hE => CFSG.AGLEmbedding.kFactOmegaEightMinusAutElemRank K d hd he E hE

theorem p_ne_three_of_card_two {q : TauCeti.PrimePower} (h : q.card = 2) : q.p ≠ 3 := by
  intro h3
  have h1 : 3 ∣ q.p ^ q.exponent := by
    rw [h3]
    exact dvd_pow_self 3 q.exponent_pos.ne'
  rw [← TauCeti.PrimePower.card_def, h] at h1
  norm_num at h1

theorem characteristic_ne_three_of_classicalTwo {d : TauCeti.ValidLieTypeIndex}
    (h : Inputs295.IsClassicalTwoIndex (TauCeti.CFSGIndex.lie d)) :
    d.1.characteristic ≠ 3 := by
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | A r q => simpa using p_ne_three_of_card_two h
  | twistedA r q => simpa using p_ne_three_of_card_two h
  | B r q => simpa using p_ne_three_of_card_two h
  | D r q => simpa using p_ne_three_of_card_two h
  | twistedD r q => simpa using p_ne_three_of_card_two h
  | _ => exact h.elim

@[expose] def Lie295TwoRest : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, Inputs295.IsClassicalTwoIndex (TauCeti.CFSGIndex.lie d) →
    ¬ CFSG.LocalAnalysis.GLTheoremA.S9.isD4two (TauCeti.CFSGIndex.lie d) → IsBig295Index d.1 →
    ¬ CFSG.AGLEmbedding.IsSpSixTwoIndex d → ¬ CFSG.AGLEmbedding.IsOmegaMinusTwoIndex 4 d →
      Outer295At d ∧ Inner295At d

@[expose] def Lie295OtherOuter : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic ≠ 3 →
    ¬ Inputs295.IsClassicalTwoIndex (TauCeti.CFSGIndex.lie d) → IsBig295Index d.1 →
      Outer295At d

@[expose] def Lie295OtherInner : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic ≠ 3 →
    ¬ Inputs295.IsClassicalTwoIndex (TauCeti.CFSGIndex.lie d) → IsBig295Index d.1 →
      (∀ q : TauCeti.PrimePower, d.1 ≠ .D 4 q) → Inner295At d

end Vacuous

section VacuousCert

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem at_of_tits (hv : TauCeti.LieTypeIndex.tits.Valid) :
    Outer295At ⟨.tits, hv⟩ ∧ Inner295At ⟨.tits, hv⟩ := by
  refine at_of_pRank_mulAut_le fun K _ _ hs hnab ⟨e⟩ => ?_
  have hO : ¬ 3 ∣ Nat.card (Outer K) := by
    obtain ⟨f⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv K 2 1
      (CFSG.HardMathSupport.Cooperstein.Coordinator.reeTitsModel_tits_of_lie hv e)
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence f).toEquiv,
      CFSG.Sporadic.Schreier.Tits.card_outer_titsD]
    decide
  have h1 := GL83.I713.pRank_mulAut_le Nat.prime_three (GL83.I713.center_eq_bot_of_simple hnab)
  have h2 := GL83.I713.pRank_top_eq_zero_of_not_dvd Nat.prime_three hO
  have h3 : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 2 := pRank_le_two_of_noE27 fun E hE h27 =>
    CFSG.HardMathSupport.Timmesfeld.CrossChar.no_elemAbelian27_cat_tits hv
      (E := E.map e.toMonoidHom) (CFSG.SectionRank.isElemAbelian_map hE _)
      (by rw [Subgroup.card_map_of_injective e.injective, h27])
  omega

theorem outPChain_of_rankTwo (d : TauCeti.ValidLieTypeIndex) (hd : IsRankTwoIndex d.1)
    {K : Type} [Group K] [Finite K] (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    CFSG.RankThree.PartOne.OutStructure.OutPChain 3 K := by
  obtain ⟨dd, hv⟩ := d
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  cases dd with
  | A r q =>
    obtain ⟨-, hq⟩ := hd
    refine outPChain_of_lieModel Nat.prime_three (by norm_num)
      (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
        CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e⟩) ?_
    intro _ h3
    have h3' : 3 ∣ q.card - 1 := by
      rw [TauCeti.PrimePower.card_def]
      exact h3.trans (Nat.gcd_dvd_right _ _)
    omega
  | twistedA r q =>
    obtain ⟨-, hq⟩ := hd
    refine outPChain_of_lieModel Nat.prime_three (by norm_num)
      (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
        CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e⟩) ?_
    intro h3
    have h3' : 3 ∣ q.card + 1 := by
      rw [TauCeti.PrimePower.card_def]
      exact h3.trans (Nat.gcd_dvd_right _ _)
    omega
  | B r q =>
    change r = 2 at hd
    subst hd
    exact outPChain_of_lieModel Nat.prime_three (by norm_num)
      (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
        CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e⟩) trivial
  | G2 q =>
    have h3q : 3 ≤ q.p ^ q.exponent := by simpa only [TauCeti.PrimePower.card_def] using hrange
    exact outPChain_of_lieModel Nat.prime_three (by norm_num)
      (blueprintLieModel_of_models (t := .G2) (n := 0) (p := q.p) (f := q.exponent)
        ⟨⟨q.prime_p, q.exponent_pos, rfl, h3q⟩, Or.inr ⟨rfl, ⟨.G2 q, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩⟩)
      trivial
  | trialityD4 q =>
    exact outPChain_of_lieModel Nat.prime_three (by norm_num)
      (blueprintLieModel_of_models (t := .trialityD4) (n := 0) (p := q.p) (f := q.exponent)
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, Or.inr ⟨rfl, ⟨.trialityD4 q, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩⟩)
      trivial
  | reeF4 m =>
    have hm1 : 1 ≤ m := hrange
    exact outPChain_of_lieModel Nat.prime_three (by norm_num)
      (blueprintLieModel_of_models (t := .twistedF4) (n := 0) (p := 2) (f := 2 * m + 1)
        ⟨⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩,
          Or.inr ⟨rfl, ⟨.reeF4 m, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩⟩)
      trivial
  | _ => exact hd.elim

theorem at_of_rankTwo (d : TauCeti.ValidLieTypeIndex) (hch : d.1.characteristic ≠ 3)
    (hd : IsRankTwoIndex d.1) : Outer295At d ∧ Inner295At d :=
  at_of_pRank_mulAut_le fun K _ _ _ hnab ⟨e⟩ =>
    pRank_mulAut_le_three_of_chain hnab (noE27Index_of_isRankTwoIndex d hch hd K ⟨e⟩)
      (outPChain_of_rankTwo d hd e)

theorem at_of_not_big (d : TauCeti.ValidLieTypeIndex) (hch : d.1.characteristic ≠ 3)
    (hb : ¬ IsBig295Index d.1) : Outer295At d ∧ Inner295At d := by
  by_cases hL3 : CFSG.LocalAnalysis.RankThreeTheoremC.IsLinThreeCover3 d
  · exact at_of_linThree hL3
  have hopen : IsOpenIndex d.1 → Outer295At d ∧ Inner295At d := fun ho => by
    rcases isOpenIndex_cases d hch hL3 ho with h1 | h2 | h3 | h4
    · exact at_of_rankOne hch h1
    · exact at_of_rankTwo d hch h2
    · exact absurd (Or.inl h3) hb
    · exact absurd (Or.inr (Or.inl h4)) hb
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | A r q => exact hopen trivial
  | twistedA r q => exact hopen trivial
  | B r q => exact hopen trivial
  | C r q => exact hopen trivial
  | D r q => exact hopen trivial
  | twistedD r q => exact hopen trivial
  | G2 q => exact hopen trivial
  | trialityD4 q => exact hopen trivial
  | reeF4 m => exact hopen trivial
  | E6 q => exact absurd (Or.inr (Or.inr trivial)) hb
  | E7 q => exact absurd (Or.inr (Or.inr trivial)) hb
  | E8 q => exact absurd (Or.inr (Or.inr trivial)) hb
  | F4 q => exact absurd (Or.inr (Or.inr trivial)) hb
  | twistedE6 q => exact absurd (Or.inr (Or.inr trivial)) hb
  | suzuki m => exact at_of_suzuki m hv
  | reeG2 m => exact absurd (TauCeti.LieTypeIndex.characteristic_reeG2 m) hch
  | tits => exact at_of_tits hv

theorem input29_5'LieTwo_of_rest (h : Lie295TwoRest) :
    Inputs295.Input29_5'LieTwo :=
  input29_5'LieTwo_of_at fun d h2 h42 => by
    by_cases hb : IsBig295Index d.1
    · by_cases hs : CFSG.AGLEmbedding.IsSpSixTwoIndex d
      · exact at_of_sp62 hs
      by_cases ho : CFSG.AGLEmbedding.IsOmegaMinusTwoIndex 4 d
      · exact at_of_omegaMinusTwo ho
      exact h d h2 h42 hb hs ho
    · exact at_of_not_big d (characteristic_ne_three_of_classicalTwo h2) hb

theorem input29_5'LieOther_of_rest
    (hD4 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.InputD4)
    (hO : Lie295OtherOuter) (hI : Lie295OtherInner) : Inputs295.Input29_5'LieOther :=
  input29_5'LieOther_of_at fun d hch h2 => by
    by_cases hb : IsBig295Index d.1
    · refine ⟨hO d hch h2 hb, ?_⟩
      by_cases hD : ∃ q : TauCeti.PrimePower, d.1 = .D 4 q
      · obtain ⟨q, hq⟩ := hD
        obtain ⟨dd, hv⟩ := d
        change dd = .D 4 q at hq
        subst hq
        exact inner295At_D4 hD4 q hv
      · push Not at hD
        exact hI d hch h2 hb hD
    · exact at_of_not_big d hch hb

theorem input29_5'LieRest_of_rest
    (hD4 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.InputD4)
    (hT : Lie295TwoRest) (hO : Lie295OtherOuter) (hI : Lie295OtherInner) :
    Inputs295.Input29_5'LieRest :=
  ⟨Inputs295.input29_5'LieNotD42_of_split (input29_5'LieTwo_of_rest hT)
    (input29_5'LieOther_of_rest hD4 hO hI), d42T2NoNine_holds⟩

end VacuousCert

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295c
