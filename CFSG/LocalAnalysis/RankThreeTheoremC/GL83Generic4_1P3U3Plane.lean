module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3L45
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem u3plane_card_center {T : Type*} [Group T] [Finite T] (hc : Nat.card T = 3 ^ 3)
    (hnc : ¬ IsMulCommutative T) : Nat.card (center T) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTp : IsPGroup 3 T := IsPGroup.of_card hc
  have hnt : Nontrivial T := by
    rw [← Finite.one_lt_card_iff_nontrivial, hc]
    norm_num
  have hZnt : Nontrivial (center T) := hTp.center_nontrivial
  have h1 : 1 < Nat.card (center T) := Finite.one_lt_card_iff_nontrivial.mpr hZnt
  have hdvd : Nat.card (center T) ∣ 3 ^ 3 := hc ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases i
  · rw [hci] at h1
    omega
  · simpa using hci
  · exfalso
    have hq : Nat.card (T ⧸ center T) = 3 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center T)
      rw [hc, hci] at h
      omega
    have : IsCyclic (T ⧸ center T) := isCyclic_of_prime_card hq
    exact hnc (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (center T)) (by rw [QuotientGroup.ker_mk']))
  · exfalso
    have htop : center T = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hci, hc])
    exact hnc ⟨⟨fun a b => (mem_center_iff.mp (htop ▸ mem_top a) b).symm⟩⟩

theorem u3plane_facts {P : Sylow 3 G} {M : Subgroup G} {x : G} {J : Subgroup G}
    (hgen : IsGenericPoint 3 P M x) (hR1 : U3Prop34 3 P J x) (hxJ : x ∉ J) :
    IsElemAbelian 3 (u3VPlane (P : Subgroup G) J x) ∧
      Nat.card (u3VPlane (P : Subgroup G) J x) = 3 ^ 2 ∧
      u3VPlane (P : Subgroup G) J x ≤ (P : Subgroup G) ∧ x ∈ u3VPlane (P : Subgroup G) J x ∧
      u3VPlane (P : Subgroup G) J x ⊓ J ≠ ⊥ ∧
      ∀ u ∈ u3VPlane (P : Subgroup G) J x ⊓ J, ∀ t ∈ (P : Subgroup G) ⊓ J, u * t = t * u := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hxP, ⟨-, hx1, hx3, -, -⟩, -, -⟩ := hgen
  obtain ⟨hPC, hcard, hexp, hnc, -, -⟩ := hR1
  set T : Subgroup G := (P : Subgroup G) ⊓ J with hT
  have hTP : T ≤ (P : Subgroup G) := inf_le_left
  have hcZ : Nat.card (center ↥T) = 3 := u3plane_card_center hcard hnc
  set A : Subgroup G := (center ↥T).map T.subtype with hA
  have hAcard : Nat.card A = 3 := by
    rw [hA, Subgroup.card_map_of_injective T.subtype_injective, hcZ]
  have hAmem : ∀ a ∈ A, ∃ a' : ↥T, a' ∈ center ↥T ∧ (a' : G) = a := fun a ⟨a', ha', h⟩ =>
    ⟨a', ha', h⟩
  have hAT : ∀ a ∈ A, a ∈ T := fun a ha => by
    obtain ⟨a', -, rfl⟩ := hAmem a ha
    exact a'.2
  have hAc : ∀ a ∈ A, ∀ t ∈ T, a * t = t * a := fun a ha t ht => by
    obtain ⟨a', ha'c, rfl⟩ := hAmem a ha
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp ha'c ⟨t, ht⟩).symm)
  have hAx : ∀ a ∈ A, a * x = x * a := fun a ha =>
    mem_centralizer_singleton_iff.mp (hPC (hTP (hAT a ha)))
  have hxA : x ∉ A := fun h => hxJ (hAT x h).2
  have hAel : IsElemAbelian 3 A := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => hexp a (hAT a ha)⟩
    apply Subtype.ext
    exact hAc a a.2 b (hAT b b.2)
  have hAcent : A ≤ centralizer ((zpowers x : Subgroup G) : Set G) := fun a ha => by
    rw [p34_centralizer_zpowers x]
    exact mem_centralizer_singleton_iff.mpr (hAx a ha)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hUdef : u3VPlane (P : Subgroup G) J x = A ⊔ zpowers x := rfl
  rw [hUdef]
  refine ⟨CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3 hAel
      (CFSG.AGLEmbedding.isElemAbelian_zpowers hx3) hAcent, ?_,
    sup_le (fun a ha => hTP (hAT a ha)) (zpowers_le.mpr hxP), mem_sup_right (mem_zpowers x), ?_, ?_⟩
  · rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three A hx3 hxA hAx, hAcard]
    norm_num
  · intro h
    have hAle : A ≤ (A ⊔ zpowers x) ⊓ J := le_inf le_sup_left fun a ha => (hAT a ha).2
    rw [h] at hAle
    have := Subgroup.card_le_of_le hAle
    rw [hAcard, Subgroup.card_bot] at this
    omega
  · intro u hu t ht
    have hAN : A ≤ normalizer ((zpowers x : Subgroup G) : Set G) := fun a ha =>
      Subgroup.centralizer_le_normalizer ((zpowers x : Subgroup G) : Set G) (hAcent ha)
    have hu' : u ∈ ((A ⊔ zpowers x : Subgroup G) : Set G) := hu.1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A (zpowers x) hAN] at hu'
    obtain ⟨a, ha, v, hv, hav⟩ := hu'
    have hvJ : v ∈ J := by
      have : v = a⁻¹ * u := by rw [← hav]; group
      rw [this]
      exact J.mul_mem (J.inv_mem (hAT a ha).2) hu.2
    have hv1 : v = 1 := by
      by_contra hv1
      have hzv := p34_zpowers_eq_of_mem hxo hv hv1
      exact hxJ (zpowers_le.mpr hvJ (by rw [hzv]; exact mem_zpowers x))
    have hau : a = u := by simpa [hv1] using hav
    rw [← hau]
    exact hAc a ha t ht

theorem u3_exists_maximal_not_le (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK2 : KFactU3TwoSignalizer) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsU3Normal M x J) (hxJ : x ∉ J) (hR1 : U3Prop34 3 P J x) :
    ∃ S₁ : Subgroup G, rankTwoMaximalInvariantTwoSubgroup (u3VPlane (P : Subgroup G) J x) S₁ ∧
      ¬ S₁ ≤ M := by
  obtain ⟨hU, hUc, hUP, hxU, hUJ, hUZ⟩ := u3plane_facts hgen hR1 hxJ
  exact u3_exists_maximal_not_le_of_plane hS hU0 hK2 hp hM hgen hJ hxJ hU hUc hUP hxU hUJ hUZ

end CFSG.LocalAnalysis.RankThreeTheoremC
