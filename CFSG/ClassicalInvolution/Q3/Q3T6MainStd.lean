module

public import CFSG.ClassicalInvolution.Q3.Q3T6MainEnd
public import CFSG.ClassicalInvolution.Q3.Q3T6MainSylow
public import CFSG.ClassicalInvolution.Q3.Q3T6FaVoc

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Disc3
open scoped MatrixGroups commutatorElement

section Twin

variable {G : Type} [Group G] [Finite G] {t : MemberType} {Ω : Set (Subgroup G)}

theorem comm_le_oddCore_of_twin_u (hΩ : HypOmegaModU t Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z)
    (hzJ : IsUniqueInvolution J z) : ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzK.sq) hzK.ne_one
  have hdvd : 2 ∣ Nat.card ↥(K ⊓ J) := by
    have := Subgroup.orderOf_dvd_natCard (K ⊓ J) (x := z) ⟨hzK.mem, hzJ.mem⟩
    rwa [hz2] at this
  have hN : Nat.card ↥(K ⊓ J) ≠ 0 := Nat.card_pos.ne'
  have h1 := one_le_padicValNat_of_dvd hN hdvd
  obtain ⟨h2, h3⟩ := hΩ.omega4 K hK J hJ hKJ
  exact h3 (le_antisymm h2 h1)

theorem le_normalizer_of_twin_u (hΩ : HypOmegaModU t Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z)
    (hzJ : IsUniqueInvolution J z) : K ≤ Subgroup.normalizer (J : Set G) := by
  have hc := comm_le_oddCore_of_twin_u hΩ hK hJ hKJ hzK hzJ
  have key : ∀ k ∈ K, ∀ j ∈ J, k * j * k⁻¹ ∈ J := by
    intro k hk j hj
    have h1 : ⁅k, j⁆ ∈ oddCoreOf J := (hc (Subgroup.commutator_mem_commutator hk hj)).2
    have h2 : ⁅k, j⁆ ∈ J := oddCoreOf_le_self J h1
    have e : k * j * k⁻¹ = ⁅k, j⁆ * j := by rw [commutatorElement_def]; group
    rw [e]
    exact J.mul_mem h2 hj
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key k hk h hh, fun hh => ?_⟩
  have := key k⁻¹ (K.inv_mem hk) _ hh
  have e : k⁻¹ * (k * h * k⁻¹) * k⁻¹⁻¹ = h := by group
  rwa [e] at this

end Twin

section Std


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {S : Sylow 2 G} {R : Subgroup G} {z : G}

theorem natCard_rSet_of_classical
    (hcl : ∀ J ∈ Ω, ∃ w : G, IsClassicalMemberU (.sl2 3 1) J w) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : Nat.card R = 8 := by
  obtain ⟨J, hJ, P, rfl⟩ := hR
  obtain ⟨w, hw⟩ := hcl J hJ
  obtain ⟨e⟩ := quaternion_sylow_of_isClassicalMember3 (hw.toQ3 (by norm_num)) P
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), Nat.card_congr e.toEquiv,
    Nat.card_eq_fintype_card, QuaternionGroup.card]

namespace Std6Three

variable (hstd : Std6Three Ω K S R z)
include hstd

theorem eq_conjClass : Ω = CoreAssembly.conjClass K := eq_conjClass3 hstd.stand

theorem member : IsClassicalMemberU (.sl2 3 1) K z := by
  obtain ⟨z', hz'⟩ := hstd.stand.hyp.classical K hstd.stand.mem
  obtain rfl : z' = z := (hstd.hz.unique z' hz'.mem hz'.mul_self).resolve_left hz'.ne_one
  exact hz'

theorem normEq : Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G) := by
  have hs := hstd.stand
  have hz := hstd.hz
  apply le_antisymm
  · intro n hn
    have hmem : n * z * n⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hn z).mp hz.mem
    have h2 : n * z * n⁻¹ * (n * z * n⁻¹) = 1 := by
      calc n * z * n⁻¹ * (n * z * n⁻¹) = n * (z * z) * n⁻¹ := by group
        _ = 1 := by rw [hz.sq]; group
    have h1 : n * z * n⁻¹ ≠ 1 := fun h => hz.ne_one (by
      calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group)
    have h := (hz.unique _ hmem h2).resolve_left h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [h]
  · intro c hc
    have hcz : c * z * c⁻¹ = z := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hc]
      group
    have hKc : conjSub c K ∈ Ω := hs.hyp.conjInvariant c K hs.mem
    have hzc : IsUniqueInvolution (conjSub c K) z := hcz ▸ hz.conj c
    by_contra hnot
    have hne : conjSub c K ≠ K := fun h => hnot (mem_normalizer_iff_conjSub_eq.mpr h)
    have hle := le_normalizer_of_twin_u hs.hyp hKc hs.mem hne hzc hz
    obtain ⟨R', hR', hR'J, -⟩ := exists_mem_RSet_ge hKc (isPGroup_two_bot (G := G)) bot_le
    exact hstd.edgeless K hs.mem _ hKc
      (Or.inl ⟨hKc, hne, R', hR', hR'J.1, fun x hx => hle (hR'J.1 hx)⟩)

theorem not_dConnected [IsSimpleGroup G] : ¬ DConnected (CoreAssembly.conjClass K) := by
  have hz := hstd.hz
  have hedge : DEdgeless (CoreAssembly.conjClass K) := hstd.eq_conjClass ▸ hstd.edgeless
  intro hc
  have hall : ∀ J ∈ CoreAssembly.conjClass K, J = K := by
    intro J hJ
    rcases Relation.ReflTransGen.cases_head (hc K (CoreAssembly.mem_conjClass_self K) J hJ) with
      h1 | ⟨c, ⟨hc1, hc2⟩, -⟩
    · exact h1.symm
    · exact absurd hc2 (hedge K (CoreAssembly.mem_conjClass_self K) c hc1)
  have hKtop : K = ⊤ := by
    have hgen := gen_conjClass K hz.mem hz.ne_one
    exact eq_top_iff.mpr (hgen ▸ iSup₂_le fun J hJ => (hall J hJ).le)
  have hzc : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [← hstd.normEq, hKtop, Subgroup.mem_normalizer_iff]
      intro k
      simp
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  have htop : Subgroup.center G = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h1 | h1
    · rw [h1, Subgroup.mem_bot] at hzc
      exact absurd hzc hz.ne_one
    · exact h1
  obtain ⟨x, -, y, -, hxy⟩ := exists_noncomm_of_sl2 hstd.member
  have hx : x ∈ Subgroup.center G := htop ▸ Subgroup.mem_top x
  exact hxy (Subgroup.mem_center_iff.mp hx y).symm

theorem tight [IsSimpleGroup G] : TightStd3 K z where
  nonabelian := by
    obtain ⟨x, -, y, -, hxy⟩ := exists_noncomm_of_sl2 hstd.member
    exact ⟨x, y, hxy⟩
  below := hstd.stand.below
  member := hstd.member
  hyp := hstd.eq_conjClass ▸ hstd.stand.hyp
  rank := hstd.rank
  notFourGenerated := fun h4 => hstd.cex (Or.inr h4)
  dDisconnected := hstd.not_dConnected
  normEq := hstd.normEq
  edgeless := hstd.eq_conjClass ▸ hstd.edgeless

theorem isSylow2In_R : IsSylow2In R K := by
  obtain ⟨J, hJ, P, hRJ⟩ := hstd.hR
  by_cases hJK : J = K
  · subst hJK
    rw [hRJ]
    exact isSylow2In_map_sylow J P
  · exfalso
    obtain ⟨h2, -⟩ := hstd.stand.hyp.omega4 K hstd.stand.mem J hJ (Ne.symm hJK)
    have hRKJ : R ≤ K ⊓ J := le_inf hstd.hRK (hRJ ▸ Subgroup.map_subtype_le _)
    have h8 : Nat.card R = 8 :=
      natCard_rSet_of_classical (fun J hJ => hstd.stand.hyp.classical J hJ) hstd.hR
    have hdvd : 2 ^ 3 ∣ Nat.card ↥(K ⊓ J) := by
      have := Subgroup.card_dvd_of_le hRKJ
      rwa [h8] at this
    have h3 : 3 ≤ padicValNat 2 (Nat.card ↥(K ⊓ J)) :=
      (padicValNat_dvd_iff_le Nat.card_pos.ne').mp hdvd
    omega

theorem exists_sylow_le :
    ∃ Q₀ : Sylow 2 K, (Q₀ : Subgroup K).map K.subtype ≤ (S : Subgroup G) := by
  have hRK := hstd.isSylow2In_R
  obtain ⟨Q, hQ⟩ := (hRK.2.1.comap_subtype : IsPGroup 2 (R.subgroupOf K)).exists_le_sylow
  have heq : (Q : Subgroup K).map K.subtype = R :=
    hRK.2.2 _ (Subgroup.map_subtype_le _) (Q.isPGroup'.map _)
      (by rw [← Subgroup.map_subgroupOf_eq_of_le hRK.1]; exact Subgroup.map_mono hQ)
  exact ⟨Q, heq ▸ hstd.hRS⟩

end Std6Three

namespace TightStd3

variable {K : Subgroup G} {z : G} (ht : TightStd3 K z)
include ht

theorem uniqueInvolutionNormal : UniqueInvolutionNormal K z := by
  let Q : Sylow 2 K := Classical.choice Sylow.nonempty
  exact uniqueInvolutionNormal_of_quaternion_sylow ht.member.orderOf_eq_two ht.member.mem
    ht.le_centralizer
    ((Subgroup.normal_subgroupOf_iff_le_normalizer ht.le_centralizer).mpr
      ht.centralizer_le_normalizer) Q
    (quaternion_sylow_of_isClassicalMember3' (ht.member.toQ3 (by norm_num)) Q)

theorem mem_of_isSylow2Of {P : Subgroup G} (hP : IsSylow2Of P K) : z ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := ht.uniqueInvolutionNormal
  have h2K : 2 ∣ Nat.card K := by
    have h := Subgroup.orderOf_dvd_natCard K hU.2.1
    rwa [hU.1] at h
  have hPcard := hP.card_eq
  have h2P : 2 ∣ Nat.card P := by
    rw [hPcard]
    have hpos : 0 < (Nat.card K).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2K
    exact dvd_pow_self 2 hpos.ne'
  obtain ⟨⟨x, hxP⟩, hx2⟩ := exists_prime_orderOf_dvd_card' 2 h2P
  have hx2' : orderOf x = 2 := by rw [← Subgroup.orderOf_mk x hxP]; exact hx2
  rw [← hU.2.2.1 x (hP.1 hxP) hx2']
  exact hxP

theorem isUniqueInvolution_of_mem_rSet_of_le {R : Subgroup G}
    (hR : R ∈ RSet (CoreAssembly.conjClass K)) (hRK : R ≤ K) : IsUniqueInvolution R z := by
  have hI := ht.isUniqueInvolution
  have h2R : 2 ∣ Nat.card R := by rw [ht.natCard_rSet hR]; norm_num
  obtain ⟨⟨u, hu⟩, hu2⟩ := exists_prime_orderOf_dvd_card' 2 h2R
  have hu' : orderOf u = 2 := by rw [← Subgroup.orderOf_mk u hu]; exact hu2
  have huz : u = z := ht.uniqueInvolutionNormal.2.2.1 _ (hRK hu) hu'
  exact ⟨huz ▸ hu, hI.ne_one, hI.sq, fun y hy hy2 => hI.unique y (hRK hy) hy2⟩

theorem mem_omegaNbr_of_commuting_sylow {g : G} (hg : g ∉ Subgroup.normalizer (K : Set G))
    {P₁ P₂ : Subgroup G} (hP₁ : IsSylow2Of P₁ K) (hP₂ : IsSylow2Of P₂ (conjSubgroup g K))
    (hcomm : ∀ x ∈ P₁, ∀ y ∈ P₂, x * y = y * x) :
    conjSubgroup g K ∈ Asc77.omegaNbr (CoreAssembly.conjClass K) K := by
  have hzP₁ := ht.mem_of_isSylow2Of hP₁
  obtain ⟨T, hT⟩ := hP₂.exists_sylow
  refine ⟨⟨g, rfl⟩, fun h => hg (conjSubgroup_eq_self_iff.mp h), P₂,
    ⟨conjSubgroup g K, ⟨g, rfl⟩, T, hT.symm⟩, hP₂.1, ?_⟩
  intro y hy
  rw [ht.normEq, Subgroup.mem_centralizer_singleton_iff]
  exact (hcomm z hzP₁ y hy).symm

theorem conjSubgroup_sylow_eq (Q : Sylow 2 K) {S : Subgroup G} (hS : IsPGroup 2 S)
    (hQS : (Q : Subgroup K).map K.subtype ≤ S) {g : G}
    (hgS : conjSubgroup g ((Q : Subgroup K).map K.subtype) ≤ S) :
    conjSubgroup g ((Q : Subgroup K).map K.subtype) = (Q : Subgroup K).map K.subtype := by
  have hU := ht.uniqueInvolutionNormal
  have hQq := quaternion_sylow_of_isClassicalMember3' (ht.member.toQ3 (by norm_num)) Q
  have hzQ : z ∈ (Q : Subgroup K).map K.subtype :=
    ht.mem_of_isSylow2Of (isSylow2Of_map_subtype Q)
  by_contra hne
  have h1 : conjSubgroup 1 ((Q : Subgroup K).map K.subtype) ≤ S := by
    rw [conjSubgroup_one]
    exact hQS
  have hne' : conjSubgroup 1 ((Q : Subgroup K).map K.subtype) ≠
      conjSubgroup g ((Q : Subgroup K).map K.subtype) := by
    rw [conjSubgroup_one]
    exact fun h => hne h.symm
  obtain ⟨hbot, hcomm⟩ := quaternion_conjugates_commute Q hQq hzQ hU.1 hU.2.2.2.1 hU.2.2.2.2 hS
    hQS h1 hgS hne'
  rw [conjSubgroup_one] at hbot hcomm
  by_cases hg : g ∈ Subgroup.normalizer (K : Set G)
  · have hgz : g ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [← ht.normEq]
      exact hg
    have hz' : z ∈ conjSubgroup g ((Q : Subgroup K).map K.subtype) := by
      have h := mem_conjSubgroup_of_mem (g := g) hzQ
      rwa [show g * z * g⁻¹ = z by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hgz]; group] at h
    have hz1 : z ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_inf.mpr ⟨hzQ, hz'⟩
    rw [Subgroup.mem_bot] at hz1
    have h2 := hU.1
    rw [hz1] at h2
    simp at h2
  · exact absurd (Or.inl (ht.mem_omegaNbr_of_commuting_sylow hg (isSylow2Of_map_subtype Q)
      ((isSylow2Of_map_subtype Q).conj g) hcomm))
      (ht.edgeless K (CoreAssembly.mem_conjClass_self K) _ ⟨g, rfl⟩)

end TightStd3

namespace Std6Three

variable (hstd : Std6Three Ω K S R z)
include hstd

theorem le_centralizer [IsSimpleGroup G] :
    (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
  have ht := hstd.tight
  obtain ⟨Q₀, hQS⟩ := hstd.exists_sylow_le
  have hzR : IsUniqueInvolution ((Q₀ : Subgroup K).map K.subtype) z :=
    ht.isUniqueInvolution_of_mem_rSet_of_le
      (hstd.eq_conjClass ▸ ⟨K, hstd.stand.mem, Q₀, rfl⟩) (Subgroup.map_subtype_le _)
  have hSN : (S : Subgroup G) ≤
      Subgroup.normalizer (((Q₀ : Subgroup K).map K.subtype : Subgroup G) : Set G) := by
    intro s hs
    have hle : conjSubgroup s ((Q₀ : Subgroup K).map K.subtype) ≤ (S : Subgroup G) := by
      intro x hx
      have hx' := mem_conjSubgroup_iff.mp hx
      have e : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs (hQS hx')) (Subgroup.inv_mem _ hs)
    exact conjSubgroup_eq_self_iff.mp (ht.conjSubgroup_sylow_eq Q₀ S.isPGroup' hQS hle)
  intro s hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := hzR.conj_eq (conjSub_eq_of_mem_normalizer (hSN hs))
  calc s * z = s * z * s⁻¹ * s := by group
    _ = z * s := by rw [h1]

end Std6Three

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6
