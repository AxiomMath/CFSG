module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618CaseDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618Main
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618Point
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618Two
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618OneCase
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Good
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem layer618_isSimpleGroup_quotient {M : Type*} [Group M] {S : Subgroup M}
    [S.Normal] (hS : S ≠ ⊤) (hmax : ∀ T : Subgroup M, T.Normal → S ≤ T → T = S ∨ T = ⊤) :
    IsSimpleGroup (M ⧸ S) := by
  have : Nontrivial (M ⧸ S) := by
    obtain ⟨g, -, hg⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hS)
    exact ⟨⟨QuotientGroup.mk g, 1, fun h => hg ((QuotientGroup.eq_one_iff g).1 h)⟩⟩
  refine { eq_bot_or_eq_top_of_normal := fun T hT => ?_ }
  have hle : S ≤ T.comap (QuotientGroup.mk' S) := fun x hx => by
    simp [(QuotientGroup.eq_one_iff x).2 hx]
  rcases hmax _ (hT.comap _) hle with h | h
  · refine Or.inl (eq_bot_iff.2 fun t ht => ?_)
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
    have : g ∈ T.comap (QuotientGroup.mk' S) := ht
    rw [h] at this
    exact (Subgroup.mem_bot).2 ((QuotientGroup.eq_one_iff g).2 this)
  · refine Or.inr (eq_top_iff.2 fun t _ => ?_)
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
    have : g ∈ T.comap (QuotientGroup.mk' S) := by rw [h]; exact mem_top g
    exact this

omit [Finite G] in
private theorem layer618_isSimpleGroup_of_maximal {K Q : Subgroup G} (hQK : Q ≤ K)
    [(Q.subgroupOf K).Normal] (hlt : Q < K)
    (hmax : ∀ N : Subgroup G, N ≤ K → (N.subgroupOf K).Normal → Q ≤ N → N = Q ∨ N = K) :
    IsSimpleGroup (↥K ⧸ Q.subgroupOf K) := by
  refine layer618_isSimpleGroup_quotient (S := Q.subgroupOf K) ?_ ?_
  · intro htop
    exact absurd (Subgroup.subgroupOf_eq_top.1 htop) (not_le_of_gt hlt)
  · intro T hT hST
    have hNT : (T.map K.subtype).subgroupOf K = T :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective T
    have hQN : Q ≤ T.map K.subtype := fun q hq =>
      Subgroup.mem_map.2 ⟨⟨q, hQK hq⟩, hST (Subgroup.mem_subgroupOf.2 hq), rfl⟩
    have hTn : ((T.map K.subtype).subgroupOf K).Normal := by rw [hNT]; exact hT
    rcases hmax _ (Subgroup.map_subtype_le T) hTn hQN with h | h
    · exact Or.inl (by rw [← hNT, h])
    · exact Or.inr (by rw [← hNT, h]; exact Subgroup.subgroupOf_self K)

omit [Finite G] in
private theorem layer618_quotient_nonabelian {K Q : Subgroup G} [(Q.subgroupOf K).Normal]
    (hperf : ⁅K, K⁆ = K) (hlt : Q < K) :
    ∃ a b : ↥K ⧸ Q.subgroupOf K, a * b ≠ b * a := by
  by_contra hne
  have hcomm : ∀ a b : ↥K ⧸ Q.subgroupOf K, a * b = b * a := fun a b => by
    by_contra h
    exact hne ⟨a, b, h⟩
  refine absurd ?_ (not_le_of_gt hlt)
  calc K = ⁅K, K⁆ := hperf.symm
    _ ≤ Q := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      let a : ↥K := ⟨g₁, hg₁⟩
      let b : ↥K := ⟨g₂, hg₂⟩
      have h1 : (QuotientGroup.mk' (Q.subgroupOf K)) ⁅a, b⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ _)
      exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)

omit [Finite G] in
private theorem layer618_three_dvd_card {K O : Subgroup G} [((K ⊓ O).subgroupOf K).Normal] {z : G}
    (hzK : z ∈ K) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (hO : Nat.Coprime 3 (Nat.card O)) :
    3 ∣ Nat.card (↥K ⧸ (K ⊓ O).subgroupOf K) := by
  have hzO : z ∉ O := by
    intro hzO
    have h1 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    have h2 : orderOf z ≠ 1 := fun h => hz1 (orderOf_eq_one_iff.1 h)
    have h3 : orderOf z = 3 := ((Nat.dvd_prime Nat.prime_three).1 h1).resolve_left h2
    have h4 : orderOf z ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hzO
    rw [h3] at h4
    exact absurd (Nat.Coprime.eq_one_of_dvd hO h4) (by norm_num)
  set r : ↥K ⧸ (K ⊓ O).subgroupOf K := QuotientGroup.mk ⟨z, hzK⟩ with hr
  have hr3 : r ^ 3 = 1 := by
    rw [hr, ← QuotientGroup.mk_pow]
    have : (⟨z, hzK⟩ : ↥K) ^ 3 = 1 := Subtype.ext hz3
    rw [this]
    rfl
  have hr1 : r ≠ 1 := by
    intro h
    exact hzO (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h)).2
  have h1 : orderOf r ∣ 3 := orderOf_dvd_of_pow_eq_one hr3
  have h2 : orderOf r ≠ 1 := fun h => hr1 (orderOf_eq_one_iff.1 h)
  have h3 : orderOf r = 3 := ((Nat.dvd_prime Nat.prime_three).1 h1).resolve_left h2
  rw [← h3]
  exact _root_.orderOf_dvd_natCard r

private theorem layer618_cover {K O : Subgroup G} {b : G} (hb3 : b ^ 3 = 1)
    (hbK : b ∈ normalizer (K : Set G)) (hbO : b ∈ normalizer (O : Set G))
    (hO : Nat.Coprime 3 (Nat.card O)) (hcomm : ⁅zpowers b, K⁆ ≤ O) :
    ∀ k ∈ K, ∃ q ∈ K ⊓ O, q * k ∈ centralizer ({b} : Set G) := by
  intro k hk
  have hc : b * k * b⁻¹ * k⁻¹ ∈ K ⊓ O :=
    ⟨K.mul_mem ((mem_normalizer_iff.1 hbK k).1 hk) (K.inv_mem hk),
      hcomm (Subgroup.commutator_mem_commutator (mem_zpowers b) hk)⟩
  have hQ : Nat.Coprime 3 (Nat.card ↥(K ⊓ O)) :=
    hO.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
  exact exists_mul_mem_centralizer_of_coprime hb3
    (Subgroup.inf_normalizer_le_normalizer_inf ⟨hbK, hbO⟩) hQ hc

private def layer618In (K C : Subgroup G) : ↥((K ⊓ C).subgroupOf C) →* ↥K where
  toFun d := ⟨(d.1 : G), (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 d.2)).1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private def layer618F (K Q C : Subgroup G) [(Q.subgroupOf K).Normal] :
    ↥((K ⊓ C).subgroupOf C) →* ↥K ⧸ Q.subgroupOf K :=
  (QuotientGroup.mk' (Q.subgroupOf K)).comp (layer618In K C)

omit [Finite G] in
private theorem layer618F_surjective {K Q C : Subgroup G} [(Q.subgroupOf K).Normal] (hQK : Q ≤ K)
    (hcov : ∀ k ∈ K, ∃ q ∈ Q, q * k ∈ C) : Function.Surjective (layer618F K Q C) := by
  intro r
  obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective r
  obtain ⟨q, hq, hqk⟩ := hcov k hk
  have hqK : q ∈ K := hQK hq
  refine ⟨⟨⟨q * k, hqk⟩, Subgroup.mem_subgroupOf.2 ⟨K.mul_mem hqK hk, hqk⟩⟩, ?_⟩
  have hq1 : ((⟨q, hqK⟩ : ↥K) : ↥K ⧸ Q.subgroupOf K) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hq)
  show ((⟨q, hqK⟩ * ⟨k, hk⟩ : ↥K) : ↥K ⧸ Q.subgroupOf K) = _
  rw [QuotientGroup.mk_mul, hq1, one_mul]

omit [Finite G] in
private theorem layer618_kbar {K Q C : Subgroup G} [(Q.subgroupOf K).Normal]
    {L : Subgroup ↥C} (hLD : L ≤ (K ⊓ C).subgroupOf C) (e : ↥L ≃* PSL(3, ZMod 2))
    (hbij : Function.Bijective ((layer618F K Q C).comp (Subgroup.inclusion hLD))) :
    ∃ f : ↥K →* PSL(3, ZMod 2), Function.Surjective f ∧ ∀ k : ↥K, f k = 1 ↔ (k : G) ∈ Q := by
  let ψ : (↥K ⧸ Q.subgroupOf K) ≃* PSL(3, ZMod 2) :=
    (MulEquiv.ofBijective _ hbij).symm.trans e
  refine ⟨ψ.toMonoidHom.comp (QuotientGroup.mk' (Q.subgroupOf K)), ?_, fun k => ?_⟩
  · exact ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  · show ψ (QuotientGroup.mk' (Q.subgroupOf K) k) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]

omit [Finite G] in
private theorem layer618_decomp {K Q C : Subgroup G} [(Q.subgroupOf K).Normal]
    {L : Subgroup ↥C} (hLD : L ≤ (K ⊓ C).subgroupOf C) (e : ↥L ≃* PSL(3, ZMod 2))
    (hbij : Function.Bijective ((layer618F K Q C).comp (Subgroup.inclusion hLD))) :
    ∃ L' : Subgroup G, L' ≤ K ∧ L' ≤ C ∧ Nonempty (↥L' ≃* PSL(3, ZMod 2)) ∧
      ∀ k ∈ K, ∃ l ∈ L', ∃ o ∈ Q, k = l * o := by
  refine ⟨L.map C.subtype, ?_, ?_,
    ⟨(Subgroup.equivMapOfInjective L C.subtype C.subtype_injective).symm.trans e⟩, ?_⟩
  · rintro _ ⟨l, hl, rfl⟩
    exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 (hLD hl))).1
  · rintro _ ⟨l, hl, rfl⟩
    exact l.2
  · intro k hk
    obtain ⟨l, hl⟩ := hbij.2 (QuotientGroup.mk ⟨k, hk⟩)
    refine ⟨((l : ↥C) : G), ⟨(l : ↥C), l.2, rfl⟩, ((l : ↥C) : G)⁻¹ * k, ?_, by group⟩
    exact Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hl)

omit [Finite G] in
private theorem layer618_fixed_point_free {K O C : Subgroup G} {b : G}
    (hKO : K ≤ normalizer (O : Set G)) (hO : Nat.Coprime 3 (Nat.card O))
    (hbC : ∀ o : G, b * o = o * b → o ∈ C) {L : Subgroup ↥C}
    (hLD : L ≤ (K ⊓ C).subgroupOf C)
    (hQ0 : ∀ Q : Subgroup ↥C, Nat.Coprime 3 (Nat.card Q) →
      (∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q) → Q = ⊥) :
    ∀ o ∈ O, b * o = o * b → o = 1 := by
  intro o hoO hbo
  have hoC : o ∈ C := hbC o hbo
  have hcop : Nat.Coprime 3 (Nat.card ↥((O ⊓ C).subgroupOf C)) := by
    refine hO.coprime_dvd_right ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : O ⊓ C ≤ C)).toEquiv]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hnorm : ∀ l ∈ L, ∀ q ∈ (O ⊓ C).subgroupOf C, l * q * l⁻¹ ∈ (O ⊓ C).subgroupOf C := by
    intro l hl q hq
    have hlK : ((l : ↥C) : G) ∈ K := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 (hLD hl))).1
    have hqO : ((q : ↥C) : G) ∈ O := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hq)).1
    exact Subgroup.mem_subgroupOf.2 ⟨(mem_normalizer_iff.1 (hKO hlK) _).1 hqO,
      C.mul_mem (C.mul_mem l.2 q.2) (C.inv_mem l.2)⟩
  have hbot := hQ0 _ hcop hnorm
  have hmem : (⟨o, hoC⟩ : ↥C) ∈ (O ⊓ C).subgroupOf C := Subgroup.mem_subgroupOf.2 ⟨hoO, hoC⟩
  rw [hbot] at hmem
  exact congrArg Subtype.val (Subgroup.mem_bot.1 hmem)

theorem exists_prop614Layer (hS : Setting G) (h627 : GL83SmallRankProp627 G)
    {P : Sylow 3 G} {M : Subgroup G}
    (hsit : SmallRankSituation G 3 P M) (hsolv : Group.IsSolvable M) {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {H K : Subgroup G}
    (hB : zpowers x ⊔ zpowers z ≤ H) (hK : Prop614Component M H K x z) :
    ∃ b : G, Prop614Layer P M H K x z b := by
  obtain ⟨b, hbB, hbZ, hcomm⟩ := hK.centralizes
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hHO, hOcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 3 H
  have hbH : b ∈ H := hB hbB
  have hKO : K ≤ normalizer (rankThreePrimeCore 3 H : Set G) := hK.le.trans hHO
  have hb : SmallRankPoint P M b := smallRankPoint_of_mem_plane hS hsit hx hz hbB hbZ
  obtain ⟨T, hT⟩ := exists_smallRankSylowTwo hS hsit.mem_sigmaA hsit.isCoreMaxLocal
  have hcov := layer618_cover hb.pow_eq_one (hK.normal hbH) (hHO hbH) hOcop hcomm
  have hQn : ((K ⊓ rankThreePrimeCore 3 H).subgroupOf K).Normal := by
    rw [Subgroup.inf_subgroupOf_left]
    exact Subgroup.normal_subgroupOf_of_le_normalizer hKO
  rcases (h627 3 P M hsit).2 b hb T hT with hone | htwo
  swap
  · exact (false_of_caseTwo hsolv htwo inf_le_left hQn hK.perfect hK.lt hK.maximal hcov).elim
  have hR : IsSimpleGroup (↥K ⧸ (K ⊓ rankThreePrimeCore 3 H).subgroupOf K) :=
    layer618_isSimpleGroup_of_maximal inf_le_left hK.lt hK.maximal
  obtain ⟨L, hLD, ⟨e⟩, hbij, hQ0⟩ := exists_layer_of_caseOne hone.2
    (D := (K ⊓ centralizer ({b} : Set G)).subgroupOf (centralizer ({b} : Set G)))
    (layer618_quotient_nonabelian hK.perfect hK.lt)
    (layer618_three_dvd_card (hK.mem (mem_zpowers z)) hz.pow_eq_one hz.ne_one hOcop)
    (layer618F K (K ⊓ rankThreePrimeCore 3 H) (centralizer ({b} : Set G)))
    (layer618F_surjective inf_le_left hcov)
  obtain ⟨f₀, hf₀s, hf₀k⟩ := layer618_kbar hLD e hbij
  obtain ⟨L', hL'K, hL'C, he', hdec⟩ := layer618_decomp hLD e hbij
  refine ⟨b, hbB, hbZ, hcomm, ⟨T, hT, hone⟩,
    ⟨f₀, hf₀s, fun k => (hf₀k k).trans ⟨fun h => h.2, fun h => ⟨k.2, h⟩⟩⟩,
    ⟨L', hL'K, hL'C, he', fun k hk => ?_⟩,
    layer618_fixed_point_free hKO hOcop (fun o ho => ?_) hLD hQ0⟩
  · obtain ⟨l, hl, o, ho, rfl⟩ := hdec k hk
    exact ⟨l, hl, o, ho.2, rfl⟩
  · exact Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact ho

theorem prop614Core18_of_core19 (hS : Setting G) (h627 : GL83SmallRankProp627 G)
    (h : GL83SmallRankProp614Core19 G) :
    GL83SmallRankProp614Core18 G := by
  intro P M hsit hsolv he x z hx hz H S hext h0 h1 h2 h3 h4 h5 h6 hKex
  obtain ⟨K, hK⟩ := hKex
  obtain ⟨b, hb⟩ := exists_prop614Layer hS h627 hsit hsolv hx hz hext.pair.le hK
  exact h P M hsit hsolv he x z hx hz H S hext h0 h1 h2 h3 h4 h5 h6 ⟨K, b, hK, hb⟩

theorem prop614_of_core19 (hS : Setting G) (hU0 : FullCoreLocal G) (hD2 : TheoremD2 G)
    (hK : KFactBlockFactorThreePrime) (hKF1 : KFactSylowNormalizerIrreducible)
    (hKF2 : KFactOutThreePrimeSimple) (h627 : GL83SmallRankProp627 G)
    (h632 : GL83SmallRankProp632 G) (h : GL83SmallRankProp614Core19 G) :
    GL83SmallRankProp614 G :=
  prop614_of_core18 hS hU0 hD2 hK hKF1 hKF2 h627 h632 (prop614Core18_of_core19 hS h627 h)

end CFSG.LocalAnalysis.RankThreeTheoremC
