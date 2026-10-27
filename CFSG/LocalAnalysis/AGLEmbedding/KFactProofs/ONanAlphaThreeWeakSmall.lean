module

public import CFSG.LocalAnalysis.AGLEmbedding.SporadicAlphaData
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
import CFSG.LocalAnalysis.AGLEmbedding.CoverAbelianSylow
import CFSG.LocalAnalysis.AGLEmbedding.CoverAbelianSylowAux
import CFSG.LocalAnalysis.AGLEmbedding.CoverRankLift
import CFSG.LocalAnalysis.AGLEmbedding.SporadicAlpha
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowONan
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverRankFiveCensus
import CFSG.Sporadic.Bridge.ONSurj
import CFSG.Sporadic.Bridge.M22
import CFSG.Alternating.Multipliers.Main

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeWeak

open CFSG.Open CFSG.Blueprint CFSG.AGLEmbedding.KFactProofs.CoverFive
open CFSG.RankThree.PartTwo.Sec4.Census (SporadicMultipliers)

theorem sylow_card_dvd_27 {K : Type} [Group K] [Finite K] (T : Sylow 3 K) {m : ℕ}
    (hK : Nat.card K = 27 * m) (hm : ¬ 3 ∣ m) : Nat.card (T : Subgroup K) ∣ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
  have hdvd : Nat.card (T : Subgroup K) ∣ 27 * m := hK ▸ Subgroup.card_subgroup_dvd_card _
  rw [hk] at hdvd ⊢
  have hcop : Nat.Coprime (3 ^ k) m :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm)
  exact hcop.dvd_of_dvd_mul_right hdvd

theorem isCyclic_of_card_le_three {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 3) :
    IsCyclic G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  interval_cases hc : Nat.card G
  · obtain ⟨hs, -⟩ := Nat.card_eq_one_iff_unique.mp hc
    exact isCyclic_of_subsingleton
  · exact isCyclic_of_prime_card (p := 2) hc
  · exact isCyclic_of_prime_card (p := 3) hc

theorem not_commutative_sylow {K : Type} [Group K] [Finite K] [Group.IsPerfect K] {p : ℕ}
    [Fact p.Prime] (T : Sylow p K) {z : K} (hz : z ∈ Subgroup.center K) (hzo : orderOf z = p) :
    ¬ ∀ a ∈ (T : Subgroup K), ∀ b ∈ (T : Subgroup K), a * b = b * a := by
  intro hc
  have hz1 := center_le_commutator_of_isPerfect T hz
    ⟨1, by rw [pow_one, ← hzo]; exact pow_orderOf_eq_one z⟩
  have hbot : ⁅(T : Subgroup K), (T : Subgroup K)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hc b hb a ha
  rw [hbot, Subgroup.mem_bot] at hz1
  rw [hz1, orderOf_one] at hzo
  exact (Fact.out : p.Prime).one_lt.ne hzo

theorem exists_central_of_order_prime {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hZ : Subgroup.center K ≠ ⊥) (hZp : IsPGroup p (Subgroup.center K)) :
    ∃ z ∈ Subgroup.center K, orderOf z = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) p
    (dvd_card_center_of_isPGroup hp hZ hZp)
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

@[expose] def SylowHyp (K : Type) [Group K] (T : Sylow 3 K) : Prop :=
  (∃ A : Subgroup K, A ≤ (T : Subgroup K) ⊓ Subgroup.centralizer (T : Set K) ∧
      IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 2) ∨
    (∃ A : Subgroup K, A ≤ (T : Subgroup K) ∧
      (T : Subgroup K) ≤ Subgroup.normalizer (A : Set K) ∧ IsElemAbelian 3 A ∧
      3 ^ (3 + 1) ≤ Nat.card A)

theorem false_of_sylow_card_dvd_27 {K : Type} [Group K] [Finite K] [Group.IsPerfect K]
    (T : Sylow 3 K) (h27 : Nat.card (T : Subgroup K) ∣ 27) {z : K}
    (hz : z ∈ Subgroup.center K) (hzo : orderOf z = 3) (hT : SylowHyp K T) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnc := not_commutative_sylow T hz hzo
  have hle27 : Nat.card (T : Subgroup K) ≤ 27 := Nat.le_of_dvd (by norm_num) h27
  rcases hT with ⟨A, hA, -, hAcard⟩ | ⟨A, hAT, -, -, hAcard⟩
  ·
    have hAT : A ≤ (T : Subgroup K) := hA.trans inf_le_left
    have hAZ : A.subgroupOf (T : Subgroup K) ≤ Subgroup.center (T : Subgroup K) := by
      intro a ha
      rw [Subgroup.mem_center_iff]
      intro b
      have h1 := Subgroup.mem_centralizer_iff.mp (hA ha).2 b b.2
      exact Subtype.ext h1
    have h9 : 9 ≤ Nat.card (Subgroup.center (T : Subgroup K)) := by
      have h1 : Nat.card (A.subgroupOf (T : Subgroup K)) = Nat.card A :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv
      have h2 := Subgroup.card_le_of_le hAZ
      omega
    have hidx := Subgroup.card_mul_index (Subgroup.center (T : Subgroup K))
    have hi3 : (Subgroup.center (T : Subgroup K)).index ≤ 3 := by
      have : 9 * (Subgroup.center (T : Subgroup K)).index ≤
          Nat.card (Subgroup.center (T : Subgroup K)) *
            (Subgroup.center (T : Subgroup K)).index := Nat.mul_le_mul_right _ h9
      omega
    have : IsCyclic ((T : Subgroup K) ⧸ Subgroup.center (T : Subgroup K)) :=
      isCyclic_of_card_le_three (by rw [← Subgroup.index_eq_card]; exact hi3)
    have hcomm := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center (T : Subgroup K))) (QuotientGroup.ker_mk' _).le
    exact hnc fun a ha b hb => congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · have h1 : Nat.card A ∣ Nat.card (T : Subgroup K) := Subgroup.card_dvd_of_le hAT
    have h2 : Nat.card A ≤ 27 := (Nat.le_of_dvd Nat.card_pos h1).trans hle27
    norm_num at hAcard
    omega

theorem card_center_eq_three {K : Type} [Group K] [Finite K] (hZ : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup 3 (Subgroup.center K)) (hdvd : Nat.card (Subgroup.center K) ∣ 12) :
    Nat.card (Subgroup.center K) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj⟩ := hZp.exists_card_eq
  have h3 := dvd_card_center_of_isPGroup Nat.prime_three hZ hZp
  rw [hj] at hdvd h3 ⊢
  rcases j with _ | _ | j
  · norm_num at h3
  · norm_num
  · exfalso
    have h9 : 9 ∣ 3 ^ (j + 1 + 1) := by
      rw [show 3 ^ (j + 1 + 1) = 3 ^ j * 9 by ring]
      exact dvd_mul_left 9 _
    have := h9.trans hdvd
    omega

theorem false_of_cover_order {K X : Type} [Group K] [Finite K] [Group X] [Group.IsPerfect K]
    (hZ : Subgroup.center K ≠ ⊥) (hZp : IsPGroup 3 (Subgroup.center K))
    (e : K ⧸ Subgroup.center K ≃* X) {N m : ℕ} (hX : Nat.card X = N)
    (hdvd : Nat.card (Subgroup.center K) ∣ 12) (hN : 3 * N = 27 * m) (hm : ¬ 3 ∣ m)
    (T : Sylow 3 K) (hT : SylowHyp K T) : False := by
  have hc3 := card_center_eq_three hZ hZp hdvd
  have hK : Nat.card K = 27 * m := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K),
      Nat.card_congr e.toEquiv, hX, hc3]
    omega
  obtain ⟨z, hzZ, hzo⟩ := exists_central_of_order_prime Nat.prime_three hZ hZp
  exact false_of_sylow_card_dvd_27 T (sylow_card_dvd_27 T hK hm) hzZ hzo hT

theorem card_alternatingGroup_fin (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp

theorem false_alt_hyp {K : Type} [Group K] [Finite K]
    (hq : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup 3 (Subgroup.center K)) {n : ℕ} (hn : 5 ≤ n) (h67 : n = 6 ∨ n = 7)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) (T : Sylow 3 K)
    (hT : SylowHyp K T) : False := by
  have : Group.IsPerfect K := hq.1
  have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq e
  rw [(CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput n hn).2] at hdvd
  have hdvd6 : Nat.card (Subgroup.center K) ∣ 6 := by simpa [h67] using hdvd
  have hdvd12 : Nat.card (Subgroup.center K) ∣ 12 := hdvd6.trans (by norm_num)
  rcases h67 with rfl | rfl
  · have h6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [card_alternatingGroup_fin 6 (by norm_num)]
      rfl
    exact false_of_cover_order hZ hZp e h6 hdvd12 (m := 40) (by norm_num) (by norm_num) T hT
  · have h7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [card_alternatingGroup_fin 7 (by norm_num)]
      rfl
    exact false_of_cover_order hZ hZp e h7 hdvd12 (m := 280) (by norm_num) (by norm_num) T hT

theorem false_M22_hyp (hSpor : SporadicMultipliers) {K : Type}
    [Group K] [Finite K] (hq : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup 3 (Subgroup.center K))
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .M22).Group) (T : Sylow 3 K)
    (hT : SylowHyp K T) : False := by
  have : Group.IsPerfect K := hq.1
  have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq e
  rw [hSpor.1 .M22] at hdvd
  have hdvd12 : Nat.card (Subgroup.center K) ∣ 12 := hdvd
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have hcard : Nat.card (K ⧸ Subgroup.center K) = 443520 := by
    rw [Nat.card_congr (e.trans b.symm).toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M22
  exact false_of_cover_order hZ hZp (MulEquiv.refl _) hcard hdvd12 (m := 49280) (by norm_num)
    (by norm_num) T hT

theorem centralizer_le_center_of_abelianSylowDatum {K X : Type} [Group K] [Finite K] [Group X]
    (π : K →* X) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center K)
    [Group.IsPerfect K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hZ1 : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup p (Subgroup.center K)) (hZc : IsCyclic (Subgroup.center K))
    (hD : AbelianSylowDatum X p) (T : Sylow p K) :
    ∀ x ∈ (T : Subgroup K), (∀ y ∈ (T : Subgroup K), x * y = y * x) →
      x ∈ Subgroup.center K := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite X := Finite.of_surjective π hπ
  obtain ⟨D, hn, hF, hN, hidx⟩ := hD
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card (D.card_span hp)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q (T.mapSurjective hπ)
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  set D' := D.map (MulAut.conj g).toMonoidHom hinj with hD'
  have hspan : D'.span ≤ (T : Subgroup K).map π := by
    have h2 := congrArg (fun S : Sylow p X => (S : Subgroup X)) hg
    simp only [Sylow.coe_mapSurjective] at h2
    rw [hD', ModuleSpec.map_span, ← h2, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact Subgroup.map_mono hQ
  have hle : D'.span.comap π ≤ (T : Subgroup K) := by
    calc D'.span.comap π ≤ ((T : Subgroup K).map π).comap π := Subgroup.comap_mono hspan
      _ = (T : Subgroup K) ⊔ π.ker := Subgroup.comap_map_eq _ _
      _ = (T : Subgroup K) := by rw [hker, sup_eq_left]; exact IsPGroup.le_sylow_of_normal hZp T
  have hidx' : ¬ p ∣ (D'.span.comap π).index := by
    rwa [Subgroup.index_comap_of_surjective _ hπ, hD', ModuleSpec.map_span,
      Subgroup.index_map_of_bijective (MulAut.conj g).bijective]
  have heq : D'.span.comap π = (T : Subgroup K) :=
    (((T.isPGroup'.to_le hle).toSylow hidx').3 T.isPGroup' hle).symm
  have hN' : D'.Nondeg := hN
  rcases D'.commute_or_mem_center_of_nondeg π hp hp2 hπ hker hZp hZc hN' with hcomm | hcent
  · exfalso
    obtain ⟨z, hz, hzo⟩ := exists_central_of_order_prime hp hZ1 hZp
    exact not_commutative_sylow T hz hzo (by rw [← heq]; exact hcomm)
  · rw [heq] at hcent
    exact hcent

theorem card_le_three_of_le_center {K : Type} [Group K] [Finite K]
    (hZc : IsCyclic (Subgroup.center K)) {A : Subgroup K} (hA : A ≤ Subgroup.center K)
    (hA3 : ∀ x ∈ A, x ^ 3 = 1) : Nat.card A ≤ 3 := by
  classical
  have : Fintype (Subgroup.center K) := Fintype.ofFinite _
  have h := IsCyclic.card_pow_eq_one_le (α := Subgroup.center K) (n := 3) (by norm_num)
  refine le_trans (Nat.card_le_card_of_injective
    (fun a : A => (⟨⟨a.1, hA a.2⟩, Subtype.ext (hA3 a.1 a.2)⟩ :
      {x : Subgroup.center K // x ^ 3 = 1})) ?_) ?_
  · intro a b hab
    exact Subtype.ext (congrArg (fun x : {x : Subgroup.center K // x ^ 3 = 1} => (x.1 : K)) hab)
  · rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact h

theorem false_ON_hyp
    {K : Type} [Group K]
    [Finite K] (hq : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZc : IsCyclic (Subgroup.center K))
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .ONan).Group) (T : Sylow 3 K)
    (hT : SylowHyp K T) : False := by
  have hperf : Group.IsPerfect K := hq.1
  obtain ⟨b⟩ : Nonempty (NativeSporadic.Carrier .ONan ≃*
      (TauCeti.CFSGIndex.sporadic .ONan).Group) := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have h1 : AbelianSylowDatum (NativeSporadic.Carrier .ONan) 3 := abelianSylowDatum_ON_three
  have hS : AbelianSylowDatum (K ⧸ Subgroup.center K) 3 :=
    AbelianSylowDatum.of_mulEquiv (b.trans e.symm) h1
  let π : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Subgroup.center K := QuotientGroup.ker_mk' _
  have hcen := centralizer_le_center_of_abelianSylowDatum π hπ hker Nat.prime_three
    (by norm_num) hZ hZp hZc hS T
  have hrk := (coverAbelianSylowLemma K (K ⧸ Subgroup.center K) π hπ hker hperf 3
    Nat.prime_three (by norm_num) hZ hZp hZc hS T).2
  rcases hT with ⟨A, hA, hAel, hAcard⟩ | ⟨A, hAT, -, hAel, hAcard⟩
  · have hAZ : A ≤ Subgroup.center K := fun a ha =>
      hcen a (hA ha).1 fun y hy => (Subgroup.mem_centralizer_iff.mp (hA ha).2 y hy).symm
    have := card_le_three_of_le_center hZc hAZ hAel.2
    norm_num at hAcard
    omega
  · have := le_pRank_of_pow_le_card Nat.prime_three hAT hAel hAcard
    omega

end CFSG.AGLEmbedding.KFactProofs.ThreeWeak
