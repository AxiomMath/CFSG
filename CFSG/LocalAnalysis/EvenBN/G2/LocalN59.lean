module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalNDefs
public import CFSG.LocalAnalysis.EvenBN.G2.LocalQ55
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialSmall
import CFSG.CGT.PushingUpLit.CGT6K1.Closed

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure (BarM barMap barSub)
open CFSG.LocalAnalysis.EvenBN.Common.RankOneLayerRadical (commutatorWith RankOneData
  mem_sup_zpowers_iff_of_involution centralizer_barMap_eq)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer (ExactClosure)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement Pointwise MatrixGroups


namespace N59

section Abstract

variable {G : Type} [Group G]

theorem normalizer_ne_top_of_isPGroup_two [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {X : Subgroup G} (hX : IsPGroup 2 X) (hX1 : X ≠ ⊥) :
    normalizer (X : Set G) ≠ ⊤ := by
  intro htop
  have hN : X.Normal := normalizer_eq_top_iff.1 htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal X with hb | ht
  · exact hX1 hb
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hG : IsPGroup 2 G := fun g => by
      have hg : g ∈ X := ht ▸ Subgroup.mem_top g
      obtain ⟨k, hk⟩ := hX ⟨g, hg⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    obtain ⟨a, b, hab⟩ := hnab
    have : Nontrivial G := ⟨⟨a, b, fun h => hab (h ▸ rfl)⟩⟩
    have hc : center G ≠ ⊥ := by
      intro hb
      obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := (IsPGroup.center_nontrivial hG).exists_pair_ne
      rw [hb, Subgroup.mem_bot] at hx hy
      exact hxy (Subtype.ext (hx.trans hy.symm))
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hb | ht'
    · exact hc hb
    · exact hab (Subgroup.mem_center_iff.1 (ht' ▸ Subgroup.mem_top a : a ∈ center G) b).symm

theorem isSylowOf_zpowers_sup_of_odd [Finite G] {τ : G} {H : Subgroup G} (hτ : orderOf τ = 2)
    (hcomm : ∀ h ∈ H, h * τ = τ * h) (hH : Odd (Nat.card H)) :
    IsSylowOf 2 (zpowers τ) (zpowers τ ⊔ H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : Nat.card (zpowers τ) = 2 := by rw [Nat.card_zpowers, hτ]
  have hτH : zpowers τ ≤ normalizer (H : Set G) := by
    rw [zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 hcomm)
  have hinf : Nat.card (H ⊓ zpowers τ : Subgroup G) = 1 := by
    have h1 : Nat.card (H ⊓ zpowers τ : Subgroup G) ∣ 2 := hP ▸ Subgroup.card_dvd_of_le inf_le_right
    have h2 : Nat.card (H ⊓ zpowers τ : Subgroup G) ∣ Nat.card H :=
      Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h3 | h3
    · exact h3
    · rw [h3] at h2
      exact absurd (even_iff_two_dvd.2 h2) (Nat.not_even_iff_odd.2 hH)
  have hcard := Common.card_sup_mul_card_inf_eq (A := H) (B := zpowers τ) hτH
  rw [hinf, mul_one, hP, mul_comm] at hcard
  rw [ABGLocalTools.isSylowOf_iff]
  refine ⟨le_sup_left, ?_, ?_⟩
  · exact IsPGroup.iff_card.2 ⟨1, by rw [hP]; norm_num⟩
  · have h1 := Subgroup.relIndex_mul_card (zpowers τ) (zpowers τ ⊔ H)
    rw [inf_eq_left.2 le_sup_left, hP, sup_comm, hcard] at h1
    have h2 : (zpowers τ).relIndex (H ⊔ zpowers τ) = Nat.card H := by omega
    rw [sup_comm, h2]
    intro hd
    exact (Nat.not_even_iff_odd.2 hH) (even_iff_two_dvd.2 hd)

theorem not_subset_mul_of_card_lt [Finite G] {P X S : Subgroup G}
    (h : Nat.card X * Nat.card S < Nat.card P * Nat.card (X ⊓ S : Subgroup G)) :
    ¬ ((P : Set G) ⊆ (X : Set G) * (S : Set G)) := by
  intro hsub
  have h1 : Nat.card P ≤ ((X : Set G) * (S : Set G)).ncard := by
    have : Nat.card P = (P : Set G).ncard := Nat.card_coe_set_eq (P : Set G)
    rw [this]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := ncard_mul_set_mul_card_inf X S
  have h3 : Nat.card P * Nat.card (X ⊓ S : Subgroup G) ≤
      ((X : Set G) * (S : Set G)).ncard * Nat.card (X ⊓ S : Subgroup G) :=
    Nat.mul_le_mul_right _ h1
  omega

theorem le_of_forall_fixed_of_commutator_mem [Finite G] {J P X N : Subgroup G} (hXP : X ≤ P)
    (hPab : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ X) (hJP : J ≤ normalizer (P : Set G))
    (hJX : J ≤ normalizer (X : Set G)) (hsolv : Group.IsSolvable P)
    (hcop : (Nat.card J).Coprime (Nat.card P)) (hfix : ∀ c ∈ P ⊓ centralizer (J : Set G), c ∈ X)
    (hXN : X ≤ N) (hcomm : ∀ j ∈ J, ∀ p ∈ P, ⁅j, p⁆ ∈ N) : P ≤ N := by
  have h1 := le_commutator_sup_of_forall_fixed hXP hPab hJP hJX hsolv hcop hfix
  exact h1.trans (sup_le (commutator_le.2 hcomm) hXN)

theorem centralizer_barMap_eq_barSub_of_factor {X C₇ C₀ : Subgroup G} {t : G}
    (ht : t ∈ normalizer (X : Set G)) (htX : t ∉ X) (ht2 : t * t = 1)
    (hC₇ : X ⊔ zpowers t = C₇) (hNX : normalizer (C₇ : Set G) ≤ normalizer (X : Set G))
    (hfac : ∀ m ∈ normalizer (C₇ : Set G), ∃ x ∈ X, ∃ c ∈ C₀, m = x * c)
    (hC₀ : C₀ ≤ normalizer (C₇ : Set G)) :
    centralizer ({barMap X ⟨t, ht⟩} : Set (BarM X)) = barSub X (normalizer (C₇ : Set G)) ∧
      barSub X (normalizer (C₇ : Set G)) = barSub X C₀ := by
  refine ⟨hC₇ ▸ centralizer_barMap_eq ht htX ht2, ?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨x, hx, c, hc, hmc⟩ := hfac m (mem_subgroupOf.1 hm)
    have hcN : c ∈ normalizer (X : Set G) := hNX (hC₀ hc)
    refine Subgroup.mem_map.2 ⟨⟨c, hcN⟩, mem_subgroupOf.2 hc, ?_⟩
    refine (CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.barMap_eq_iff.2 ?_).symm
    change (m : G)⁻¹ * c ∈ X
    rw [hmc, mul_inv_rev]
    have := (mem_normalizer_iff.1 (inv_mem hcN) x⁻¹).1 (inv_mem hx)
    simpa using this
  · intro hy
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hy
    exact Subgroup.mem_map.2 ⟨m, mem_subgroupOf.2 (hC₀ (mem_subgroupOf.1 hm)), rfl⟩

open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure in
theorem nonempty_mulEquiv_barSub {X A K : Subgroup G} (hA : A ≤ normalizer (X : Set G))
    (hAK : A ≤ K) (hK : ∀ k ∈ K, ∃ x ∈ X, ∃ a ∈ A, k = x * a) (hinf : A ⊓ X = ⊥) :
    Nonempty (A ≃* barSub X K) := by
  let ψ : A →* BarM X := (barMap X).comp (Subgroup.inclusion hA)
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (a : G) ∈ X := barMap_eq_one_iff.1 ha
    have h2 : (a : G) ∈ A ⊓ X := ⟨a.2, h1⟩
    rw [hinf] at h2
    exact Subtype.ext (Subgroup.mem_bot.1 h2)
  have hrange : ψ.range = barSub X K := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact Subgroup.mem_map.2 ⟨⟨a, hA a.2⟩, mem_subgroupOf.2 (hAK a.2), rfl⟩
    · intro hy
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hy
      obtain ⟨x, hx, a, ha, hma⟩ := hK m (mem_subgroupOf.1 hm)
      refine ⟨⟨a, ha⟩, ?_⟩
      change barMap X ⟨a, hA ha⟩ = barMap X m
      refine barMap_eq_iff.2 ?_
      change a⁻¹ * (m : G) ∈ X
      rw [hma]
      have := (mem_normalizer_iff.1 (inv_mem (hA ha)) x).1 hx
      simpa [mul_assoc] using this
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure in
theorem normal_barSub_subgroupOf_barSub {X K C₀ : Subgroup G} (hKC : K ≤ C₀)
    (hC₀K : ∀ c ∈ C₀, ∀ k ∈ K, c * k * c⁻¹ ∈ K) :
    ((barSub X K).subgroupOf (barSub X C₀)).Normal := by
  have hle : barSub X K ≤ barSub X C₀ :=
    Subgroup.map_mono fun x hx => mem_subgroupOf.2 (hKC (mem_subgroupOf.1 hx))
  refine (Subgroup.normal_subgroupOf_iff hle).2 fun h k hh hk => ?_
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hh
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hk
  refine Subgroup.mem_map.2 ⟨c * a * c⁻¹,
    mem_subgroupOf.2 (hC₀K _ (mem_subgroupOf.1 hc) _ (mem_subgroupOf.1 ha)), ?_⟩
  simp only [map_mul, map_inv]

open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure in
theorem zpowers_sup_barSub_le_centralizer {X CU J : Subgroup G} {t : G}
    (ht : t ∈ normalizer (X : Set G)) (htJ : ∀ j ∈ J, j * t = t * j)
    (htCU : ∀ y ∈ CU, y * t = t * y) (hJCU : ∀ j ∈ J, ∀ y ∈ CU, (y * j)⁻¹ * (j * y) ∈ X) :
    zpowers (barMap X ⟨t, ht⟩) ⊔ barSub X J ≤
      centralizer ({barMap X ⟨t, ht⟩} : Set (BarM X)) ⊓
        centralizer (barSub X CU : Set (BarM X)) := by
  refine sup_le ?_ ?_
  · rw [zpowers_le]
    refine ⟨mem_centralizer_singleton_iff.2 rfl, mem_centralizer_iff.2 fun h hh => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hh
    rw [← map_mul, ← map_mul]
    refine barMap_eq_iff.2 ?_
    change ((y : G) * t)⁻¹ * (t * (y : G)) ∈ X
    rw [htCU _ (mem_subgroupOf.1 hy), inv_mul_cancel]
    exact one_mem _
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hg
    have hj' : (j : G) ∈ J := mem_subgroupOf.1 hj
    refine ⟨mem_centralizer_singleton_iff.2 ?_, mem_centralizer_iff.2 fun h hh => ?_⟩
    · rw [← map_mul, ← map_mul]
      refine barMap_eq_iff.2 ?_
      change ((j : G) * t)⁻¹ * (t * (j : G)) ∈ X
      rw [htJ _ hj', inv_mul_cancel]
      exact one_mem _
    · obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hh
      rw [← map_mul, ← map_mul]
      exact barMap_eq_iff.2 (hJCU _ hj' _ (mem_subgroupOf.1 hy))

open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure in
theorem barMap_mem_zpowers_sup {X J : Subgroup G} {t : G} (ht : t ∈ normalizer (X : Set G))
    {c : G} (hc : c ∈ normalizer (X : Set G)) {δ j : G} {k : ℤ} (hδ : δ ∈ X) (hj : j ∈ J)
    (hjN : j ∈ normalizer (X : Set G)) (e : c = δ * j * t ^ k) :
    barMap X ⟨c, hc⟩ ∈ zpowers (barMap X ⟨t, ht⟩) ⊔ barSub X J := by
  have hδN : δ ∈ normalizer (X : Set G) := le_normalizer hδ
  have e1 : (⟨c, hc⟩ : normalizer (X : Set G)) = ⟨δ, hδN⟩ * ⟨j, hjN⟩ * (⟨t, ht⟩ ^ k) :=
    Subtype.ext (by simp [e])
  have hδ1 : barMap X ⟨δ, hδN⟩ = 1 := barMap_eq_one_iff.2 hδ
  rw [e1, map_mul, map_mul, map_zpow, hδ1, one_mul]
  exact mul_mem (mem_sup_right (Subgroup.mem_map.2 ⟨⟨j, hjN⟩, mem_subgroupOf.2 hj, rfl⟩))
    (mem_sup_left (zpow_mem_zpowers _ _))

open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure in
theorem odd_card_barSub {X J J' : Subgroup G} (hJ : J ≤ normalizer (X : Set G)) (hJJ' : J ≤ J')
    (hodd : Odd (Nat.card J')) : Odd (Nat.card (barSub X J)) := by
  have h1 : Nat.card (barSub X J) ∣ Nat.card (J.subgroupOf (normalizer (X : Set G))) :=
    Subgroup.card_map_dvd _ _
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ).toEquiv] at h1
  exact hodd.of_dvd_nat (h1.trans (Subgroup.card_dvd_of_le hJJ'))

open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure in
theorem exists_barMap_eq_of_factor {X N C₀ : Subgroup G} (hC₀ : C₀ ≤ normalizer (X : Set G))
    (hfac : ∀ m ∈ N, ∃ x ∈ X, ∃ c ∈ C₀, m = x * c) :
    ∀ m : ↥(normalizer (X : Set G)), (m : G) ∈ N →
      ∃ c : ↥(normalizer (X : Set G)), (c : G) ∈ C₀ ∧ barMap X c = barMap X m := by
  intro m hm
  obtain ⟨x, hx, c, hc, hmc⟩ := hfac m hm
  refine ⟨⟨c, hC₀ hc⟩, hc, barMap_eq_iff.2 ?_⟩
  change c⁻¹ * (m : G) ∈ X
  rw [hmc]
  have := (mem_normalizer_iff.1 (inv_mem (hC₀ hc)) x).1 hx
  simpa [mul_assoc] using this

open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure in
theorem orderOf_barMap_involution {X : Subgroup G} {t : G} (ht : t ∈ normalizer (X : Set G))
    (htX : t ∉ X) (ht2 : t * t = 1) : orderOf (barMap X ⟨t, ht⟩) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [sq, ← map_mul]
    have : (⟨t, ht⟩ * ⟨t, ht⟩ : normalizer (X : Set G)) = 1 := Subtype.ext ht2
    rw [this, map_one]
  · intro h1
    exact htX (barMap_eq_one_iff.1 h1)

theorem sup_inf_centralizer_le_of_coprime [Finite G] {A S F F₅ : Subgroup G}
    (hSF₅ : S ≤ normalizer (F₅ : Set G)) (hinf : S ⊓ F₅ = F) (hFS : F ≤ S) (hFF₅ : F ≤ F₅)
    (hSF : S ≤ normalizer (F : Set G)) (hAS : A ≤ normalizer (S : Set G))
    (hAF : A ≤ normalizer (F : Set G)) (hAF₅ : A ≤ normalizer (F₅ : Set G))
    (hsolv : Group.IsSolvable S) (hcop : (Nat.card A).Coprime (Nat.card S))
    (hCS : S ⊓ centralizer (A : Set G) ≤ F) :
    (S ⊔ F₅) ⊓ centralizer (A : Set G) ≤ F₅ := by
  intro c hc
  obtain ⟨hcSF, hcA⟩ := Subgroup.mem_inf.1 hc
  rw [sup_comm] at hcSF
  obtain ⟨f, hf, s, hs, rfl⟩ := Common.exists_mul_of_le_normalizer hSF₅ c hcSF
  have hfix : ∀ j ∈ A, s⁻¹ * (j * s * j⁻¹) ∈ F := by
    intro j hj
    have hjc : j * (f * s) * j⁻¹ = f * s := by
      have := mem_centralizer_iff.1 hcA j hj
      rw [this, mul_inv_cancel_right]
    have hs' : j * s * j⁻¹ ∈ S := (mem_normalizer_iff.1 (hAS hj) s).1 hs
    have hf' : j * f * j⁻¹ ∈ F₅ := (mem_normalizer_iff.1 (hAF₅ hj) f).1 hf
    have e1 : f⁻¹ * (j * f * j⁻¹) = s * (j * s * j⁻¹)⁻¹ := by
      have : (j * f * j⁻¹) * (j * s * j⁻¹) = f * s := by
        rw [← hjc]; group
      calc f⁻¹ * (j * f * j⁻¹) = f⁻¹ * ((j * f * j⁻¹) * (j * s * j⁻¹)) * (j * s * j⁻¹)⁻¹ := by
            group
        _ = s * (j * s * j⁻¹)⁻¹ := by rw [this]; group
    have hu : s * (j * s * j⁻¹)⁻¹ ∈ F := by
      have h1 : s * (j * s * j⁻¹)⁻¹ ∈ S := mul_mem hs (inv_mem hs')
      have h2 : s * (j * s * j⁻¹)⁻¹ ∈ F₅ := by
        rw [← e1]
        exact mul_mem (inv_mem hf) hf'
      rw [← hinf]
      exact ⟨h1, h2⟩
    have := (mem_normalizer_iff.1 (inv_mem (hSF hs)) _).1 (inv_mem hu)
    simpa [mul_assoc] using this
  obtain ⟨c', hc', n, hn, hsn⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime hFS hSF hAS hAF
    hsolv hcop hs hfix
  have hsF : s ∈ F := by
    rw [hsn]
    exact mul_mem (hCS hc') hn
  exact mul_mem hf (hFF₅ hsF)

theorem conj_mem_normalClosureInNormalizer {X Y : Subgroup G}
    (hY : Y ≤ normalizer (X : Set G)) {g n : G} (hg : g ∈ normalizer (X : Set G))
    (hn : n ∈ Common.RankOneLayerRadical.normalClosureInNormalizer X Y) :
    g * n * g⁻¹ ∈ Common.RankOneLayerRadical.normalClosureInNormalizer X Y := by
  have hN := Common.RankOneLayerRadical.normal_subgroupOf_normalClosureInNormalizer hY
  have hnX : n ∈ normalizer (X : Set G) :=
    Common.RankOneLayerRadical.normalClosureInNormalizer_le_normalizer hY hn
  exact hN.conj_mem ⟨n, hnX⟩ (mem_subgroupOf.2 hn) ⟨g, hg⟩

open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure in
theorem mul_self_eq_one_of_mem_barSub {X P : Subgroup G} (hsq : ∀ p ∈ P, p * p ∈ X) :
    ∀ v ∈ barSub X P, v * v = 1 := by
  intro v hv
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hv
  rw [← map_mul]
  exact barMap_eq_one_iff.2 (hsq _ (mem_subgroupOf.1 hp))

open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure in
theorem subset_mul_of_commutatorWith_eq_bot {X P C₇ C₀ S : Subgroup G} {t : G}
    (ht : t ∈ normalizer (X : Set G)) (hXP : X ≤ P) (hPN : P ≤ normalizer (X : Set G))
    (hXC : X ≤ normalizer (C₇ : Set G))
    (hcent : centralizer ({barMap X ⟨t, ht⟩} : Set (BarM X)) = barSub X (normalizer (C₇ : Set G)))
    (hfac : ∀ m ∈ normalizer (C₇ : Set G), ∃ x ∈ X, ∃ c ∈ C₀, m = x * c)
    (hC₀S : ∀ c ∈ C₀, c ∈ P → c ∈ S)
    (h0 : Common.RankOneLayerRadical.commutatorWith (barSub X P) (barMap X ⟨t, ht⟩) = ⊥) :
    (P : Set G) ⊆ (X : Set G) * (S : Set G) := by
  intro p hp
  set v : BarM X := barMap X ⟨p, hPN hp⟩ with hv
  have hvP : v ∈ barSub X P := Subgroup.mem_map.2 ⟨⟨p, hPN hp⟩, mem_subgroupOf.2 hp, rfl⟩
  have h1 : v⁻¹ * ((barMap X ⟨t, ht⟩)⁻¹ * v * barMap X ⟨t, ht⟩) ∈
      Common.RankOneLayerRadical.commutatorWith (barSub X P) (barMap X ⟨t, ht⟩) :=
    Subgroup.subset_closure ⟨v, hvP, rfl⟩
  rw [h0, Subgroup.mem_bot, inv_mul_eq_one] at h1
  have h2 : v ∈ centralizer ({barMap X ⟨t, ht⟩} : Set (BarM X)) := by
    rw [mem_centralizer_singleton_iff]
    have := congrArg (fun y => barMap X ⟨t, ht⟩ * y) h1
    exact Eq.symm (by simpa [mul_assoc] using this)
  rw [hcent] at h2
  have hpN : p ∈ normalizer (C₇ : Set G) := (mem_barSub_iff hXC ⟨p, hPN hp⟩).1 h2
  obtain ⟨x, hx, c, hc, hpc⟩ := hfac p hpN
  have hcP : c ∈ P := by
    have := mul_mem (inv_mem (hXP hx)) hp
    rwa [hpc, inv_mul_cancel_left] at this
  exact Set.mem_mul.2 ⟨x, hx, c, hC₀S c hc hcP, hpc.symm⟩

open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure in
theorem commutatorWith_barSub_le {X P K : Subgroup G} {t : G} (ht : t ∈ normalizer (X : Set G))
    (hK : K ≤ normalizer (X : Set G))
    (hgen : ∀ p ∈ P, ∃ k ∈ K, ∃ x ∈ X, p⁻¹ * t⁻¹ * p * t = k * x) :
    Common.RankOneLayerRadical.commutatorWith (barSub X P) (barMap X ⟨t, ht⟩) ≤ barSub X K := by
  rw [Common.RankOneLayerRadical.commutatorWith, Subgroup.closure_le]
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hv
  obtain ⟨k, hk, x, hx, e⟩ := hgen p (mem_subgroupOf.1 hp)
  have e1 : (barMap X p)⁻¹ * ((barMap X ⟨t, ht⟩)⁻¹ * barMap X p * barMap X ⟨t, ht⟩) =
      barMap X (p⁻¹ * (⟨t, ht⟩⁻¹ * p * ⟨t, ht⟩)) := by simp [map_mul, map_inv]
  rw [SetLike.mem_coe, e1]
  refine Subgroup.mem_map.2 ⟨⟨k, hK hk⟩, mem_subgroupOf.2 hk, barMap_eq_iff.2 ?_⟩
  change k⁻¹ * ((p : G)⁻¹ * (t⁻¹ * (p : G) * t)) ∈ X
  have : (p : G)⁻¹ * (t⁻¹ * (p : G) * t) = k * x := by rw [← e]; group
  rw [this, inv_mul_cancel_left]
  exact hx

end Abstract

end N59

open N59

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]


private theorem t_mem_centralizer_inf_normalizer_U (h : Setup G L f t) (d : G2Data L K) :
    t ∈ centralizer ({t} : Set G) ⊓ normalizer (d.U : Set G) := by
  refine ⟨mem_centralizer_singleton_iff.2 rfl, Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.2 fun u hu => ?_)⟩
  exact mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hu))

private theorem yamada_5_59_N₁_normalizer_factor (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (∀ m ∈ normalizer (yamadaC₇ d t : Set G), ∃ x ∈ yamadaD₇ d t,
        ∃ c ∈ centralizer ({t} : Set G) ⊓ normalizer (d.U : Set G), m = x * c) ∧
      centralizer ({t} : Set G) ⊓ normalizer (d.U : Set G) ≤ normalizer (yamadaC₇ d t : Set G) := by
  have hD := hQ.doubling
  obtain ⟨-, -, hsup, htN, -⟩ := h.yamada_5_51 hW d hK hQ
  have h553 := (h.yamada_5_55_3 hW d hK hQ).1.1
  obtain ⟨-, hset19, -⟩ := (h.yamada_5_19 d hK hD).1
  have hset53 := (h.yamada_5_3_1 d hK).2.2.1
  have hC₁C₇ := h.yamadaC₁_le_yamadaCstar d hK hD
  refine ⟨fun m hm => ?_, fun c hc => ?_⟩
  · have hm1 : m ∈ ((normalizer (yamadaC₁ d t : Set G) : Subgroup G) : Set G) := by
      rw [← h553]; exact hm
    rw [hset19] at hm1
    obtain ⟨a, ha, n, hn, rfl⟩ := Set.mem_mul.1 hm1
    have hn' : n ∈ ((normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) : Subgroup G) : Set G) :=
      hn
    rw [hset53] at hn'
    obtain ⟨c₁, hc₁, c, hc, rfl⟩ := Set.mem_mul.1 hn'
    have hac : a * c₁ ∈ yamadaD₇ d t ⊔ zpowers t := by
      rw [hsup]
      exact mul_mem ha (hC₁C₇ hc₁)
    rcases (mem_sup_zpowers_iff_of_involution h.t_mul_t htN).1 hac with hx | ⟨x, hx, e⟩
    · exact ⟨a * c₁, hx, c, hc, by group⟩
    · refine ⟨x, hx, t * c, ?_, ?_⟩
      · exact mul_mem (t_mem_centralizer_inf_normalizer_U h d) hc
      · rw [← mul_assoc, ← mul_assoc, e]
  · rw [h553]
    exact le_normalizer_yamadaC₁ d t (h.centralizer_inf_normalizer_U_le d hc)

private theorem t_mem_centralizer_inf_normalizer_Y (h : Setup G L f t) (d : G2Data L K) :
    t ∈ centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G) := by
  refine ⟨mem_centralizer_singleton_iff.2 rfl, Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.2 fun u hu => ?_)⟩
  exact mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hu))

private theorem yamada_5_59_N₂_normalizer_factor (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (∀ m ∈ normalizer (yamadaL₆ d t : Set G), ∃ x ∈ yamadaM₆ d t,
        ∃ c ∈ centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G), m = x * c) ∧
      centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G) ≤ normalizer (yamadaL₆ d t : Set G) := by
  have hD := hQ.doubling
  obtain ⟨hsup, htN, -⟩ := (h.yamada_5_44_1 hW d hK hQ).1
  have h553 := (h.yamada_5_55_3 hW d hK hQ).2.1
  obtain ⟨-, hset539, -⟩ := (h.yamada_5_39_1 hW d hK hQ).1
  have hL₃L₆ : yamadaL₃ d t ≤ yamadaL₆ d t :=
    ((h.yamada_5_39_1 hW d hK hQ).2).ge.trans inf_le_left
  obtain ⟨-, -, hset523, -, hL₂L₃⟩ := h.yamada_5_23_1 hW d hK hD
  have hL₂L₃' : yamadaL₂ d t ≤ yamadaL₃ d t := hL₂L₃.ge.trans inf_le_left
  have hset55 := (h.yamada_5_5_1 d hK).2.2.1
  refine ⟨fun m hm => ?_, fun c hc => ?_⟩
  · have hm1 : m ∈ ((normalizer (yamadaL₂ d t : Set G) : Subgroup G) : Set G) := by
      rw [← h553]; exact hm
    rw [hset539] at hm1
    obtain ⟨a, ha, n, hn, rfl⟩ := Set.mem_mul.1 hm1
    rw [hset523] at hn
    obtain ⟨l₃, hl₃, n', hn', rfl⟩ := Set.mem_mul.1 hn
    rw [hset55] at hn'
    obtain ⟨l₂, hl₂, c, hc, rfl⟩ := Set.mem_mul.1 hn'
    have hac : a * l₃ * l₂ ∈ yamadaM₆ d t ⊔ zpowers t := by
      rw [hsup]
      exact mul_mem (mul_mem ha (hL₃L₆ hl₃)) (hL₃L₆ (hL₂L₃' hl₂))
    rcases (mem_sup_zpowers_iff_of_involution h.t_mul_t htN).1 hac with hx | ⟨x, hx, e⟩
    · exact ⟨a * l₃ * l₂, hx, c, hc, by group⟩
    · refine ⟨x, hx, t * c, ?_, ?_⟩
      · exact mul_mem (t_mem_centralizer_inf_normalizer_Y h d) hc
      · rw [← mul_assoc, ← mul_assoc, e]
        group
  · rw [h553]
    exact le_normalizer_yamadaL₂ d t (h.centralizer_inf_normalizer_Y_le d hc)

private theorem t_mem_normalizer_S (h : Setup G L f t) (d : G2Data L K) :
    t ∈ normalizer (d.S : Set G) :=
  Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.2 fun s hs => mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs))

private theorem yamadaP_inf_centralizer_eq (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaP d t ⊓ centralizer ({t} : Set G) = d.S := by
  have hSP : d.S ≤ yamadaP d t := by
    obtain ⟨-, -, -, -, hS₆P, -, -⟩ := h.yamadaP_facts hW d hK hQ
    exact (S_le_yamadaS₆ d t).trans hS₆P
  obtain ⟨-, hPR₈, -, -, -, -, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨⟨-, -, htP⟩, -⟩ := h.yamada_5_51 hW d hK hQ
  refine le_antisymm (fun x hx => ?_) (le_inf hSP (h.S_le_centralizer d))
  obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxR : x ∈ yamadaR d t := by
    rw [← (h.yamada_5_49_1 hW d hK hQ).2.2]
    exact Subgroup.mem_inf.2 ⟨hPR₈ hxP, hxC⟩
  rw [yamadaR, h.centralizer_L_inf] at hxR
  rcases (mem_sup_zpowers_iff_of_involution h.t_mul_t (t_mem_normalizer_S h d)).1 hxR with
      hs | ⟨s, hs, e⟩
  · exact hs
  · exfalso
    apply htP
    have := mul_mem (inv_mem (hSP hs)) hxP
    rwa [e, inv_mul_cancel_left] at this

private theorem yamadaD₇_inf_centralizer_eq (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaD₇ d t ⊓ centralizer ({t} : Set G) = d.D := by
  have hD := hQ.doubling
  obtain ⟨-, -, -, -, -, hFD, -, hDS, -, hSL⟩ := d.inclusions
  refine le_antisymm (fun x hx => ?_) (le_inf (h.D_le_yamadaD₇ hW d hK hQ)
    ((hDS.trans hSL).trans h.L_le_centralizer))
  obtain ⟨hxD, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxS : x ∈ d.S := by
    rw [← h.yamadaP_inf_centralizer_eq hW d hK hQ]
    exact Subgroup.mem_inf.2 ⟨yamadaD₇_le_yamadaP d t hxD, hxC⟩
  exact h.S_inf_yamadaCstar_le_D hW d hK hD (Subgroup.mem_inf.2 ⟨hxS, yamadaD₇_le_yamadaC₇ d t hxD⟩)

private theorem yamadaM₆_inf_centralizer_eq (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₆ d t ⊓ centralizer ({t} : Set G) = d.M := by
  obtain ⟨-, -, -, -, -, hFD, -, hDS, hMS, hSL⟩ := d.inclusions
  refine le_antisymm (fun x hx => ?_) (le_inf (h.M_le_yamadaM₆ hW d hK hQ)
    ((hMS.trans hSL).trans h.L_le_centralizer))
  obtain ⟨hxM, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxS : x ∈ d.S := by
    rw [← h.yamadaP_inf_centralizer_eq hW d hK hQ]
    exact Subgroup.mem_inf.2 ⟨h.yamadaM₆_le_yamadaP hW d hK hQ hxM, hxC⟩
  rw [← h.yamadaL₆_inf_S hW d hK hQ]
  exact Subgroup.mem_inf.2 ⟨h.yamadaM₆_le_yamadaL₆ hW d hK hQ hxM, hxS⟩

omit [Finite G] in
private theorem D_inf_leviA (d : G2Data L K) : d.D ⊓ d.leviA = ⊥ := by
  obtain ⟨-, -, -, -, -, -, hinf, -⟩ := even_G2_highest_long_root_centralizer K
  rw [G2Data.D, G2Data.leviA, ← d.image_inf, hinf, d.image_bot]

omit [Finite G] in
private theorem M_inf_leviB (d : G2Data L K) : d.M ⊓ d.leviB = ⊥ := by
  rw [G2Data.M, G2Data.leviB, ← d.image_inf, Model.M_inf_leviB, d.image_bot]

private theorem act_D_leviA_iff (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) {x : G} (hx : x ∈ normalizer (L : Set G)) :
    (∀ y ∈ d.D ⊔ d.leviA, y⁻¹ * (x * y * x⁻¹) ∈ d.D) ↔
      x ∈ (d.D ⊔ d.J₃) ⊔ centralizer (L : Set G) := by
  have himg1 : d.image (Model.D K ⊔ Model.leviA K) = d.D ⊔ d.leviA :=
    d.image_sup Model.D_le_adjointGroup (Model.leviA_le_adjointGroup K)
  have himg2 : d.image (Model.D K ⊔ Model.J₃ K) = d.D ⊔ d.J₃ :=
    d.image_sup Model.D_le_adjointGroup (Model.torusFix_le_adjointGroup K g2r)
  have := d.act_sectionCentralizer_eq le_sup_left (Model.yamada_3_23_3 hK h.two_le).2.1 hx
  rw [himg1, himg2] at this
  exact this

private theorem act_M_leviB_iff (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) {x : G} (hx : x ∈ normalizer (L : Set G)) :
    (∀ y ∈ d.M ⊔ d.leviB, y⁻¹ * (x * y * x⁻¹) ∈ d.M) ↔
      x ∈ (d.M ⊔ d.J₄) ⊔ centralizer (L : Set G) := by
  have himg1 : d.image (Model.M K ⊔ Model.leviB K) = d.M ⊔ d.leviB :=
    d.image_sup Model.M_le_adjointGroup (Model.leviB_le_adjointGroup K)
  have himg2 : d.image (Model.M K ⊔ Model.J₄ K) = d.M ⊔ d.J₄ :=
    d.image_sup Model.M_le_adjointGroup (Model.torusFix_le_adjointGroup K g2a)
  have := d.act_sectionCentralizer_eq le_sup_left (Model.yamada_3_23_3 hK h.two_le).2.2.2 hx
  rw [himg1, himg2] at this
  exact this

private theorem yamadaK₁_le_inf (d : G2Data L K) : yamadaK₁ d ≤ L ⊓ normalizer (d.U : Set G) :=
  commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

private theorem yamadaK₂_le_inf (d : G2Data L K) : yamadaK₂ d ≤ L ⊓ normalizer (d.Y : Set G) :=
  commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

private theorem yamadaK₁_le_normalizer_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaK₁ d ≤ normalizer (yamadaD₇ d t : Set G) :=
  (yamadaK₁_le_inf d).trans (h.normalizer_L_le_yamadaD₇_M₆ hW d hK hQ).1

private theorem yamadaK₂_le_normalizer_yamadaM₆ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaK₂ d ≤ normalizer (yamadaM₆ d t : Set G) :=
  (yamadaK₂_le_inf d).trans (h.normalizer_L_le_yamadaD₇_M₆ hW d hK hQ).2

private theorem normalizer_yamadaD₇_ne_top (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    normalizer (yamadaD₇ d t : Set G) ≠ ⊤ := by
  have := h.simple
  obtain ⟨⟨hD₇R, -⟩, -⟩ := h.yamada_5_56 hW d hK hQ
  refine normalizer_ne_top_of_isPGroup_two h.nonab
    ((Q52.isPGroup_yamadaR₈ d t).to_le hD₇R) fun hb => ?_
  have h1 := h.card_yamadaD₇ hW d hK hQ
  rw [hb, Subgroup.card_bot] at h1
  have : 1 < Nat.card K ^ 10 := Nat.one_lt_pow (by norm_num) hQ.one_lt
  omega

private theorem normalizer_yamadaM₆_ne_top (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    normalizer (yamadaM₆ d t : Set G) ≠ ⊤ := by
  have := h.simple
  obtain ⟨-, ⟨hM₆R, -⟩⟩ := h.yamada_5_56 hW d hK hQ
  refine normalizer_ne_top_of_isPGroup_two h.nonab
    ((Q52.isPGroup_yamadaR₈ d t).to_le hM₆R) fun hb => ?_
  have h1 := Q44.card_M₆ hW h d hK hQ
  rw [hb, Subgroup.card_bot] at h1
  have : 1 < Nat.card K ^ 10 := Nat.one_lt_pow (by norm_num) hQ.one_lt
  omega

private theorem yamada_5_59_N₁_kernel (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {c : G}
    (hcN : c ∈ normalizer (yamadaD₇ d t : Set G))
    (hc : c ∈ centralizer ({t} : Set G) ⊓ normalizer (d.U : Set G))
    (hy : ∀ y ∈ yamadaK₁ d, (y * c)⁻¹ * (c * y) ∈ yamadaD₇ d t) :
    ∃ δ ∈ yamadaD₇ d t, ∃ j ∈ d.J₃, ∃ k : ℤ, c = δ * j * t ^ k := by
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  have hct : c ∈ centralizer ({t} : Set G) := hc.1
  have hcL : c ∈ normalizer (L : Set G) := h.centralizer_le_normalizer hct
  have hact : ∀ y ∈ d.D ⊔ d.leviA, y⁻¹ * (c * y * c⁻¹) ∈ d.D := by
    intro y hy'
    have hyK : y ∈ yamadaK₁ d := by rw [yamadaK₁_eq d hK4]; exact hy'
    have h1 := hy y hyK
    have h3 : y⁻¹ * (c * y * c⁻¹) ∈ yamadaD₇ d t := by
      have h2 : y⁻¹ * (c * y * c⁻¹) = c * ((y * c)⁻¹ * (c * y)) * c⁻¹ := by group
      rw [h2]
      exact (mem_normalizer_iff.1 hcN _).1 h1
    have hyL : y ∈ L := sup_le (d.image_le _) (d.image_le _) hy'
    have h4 : y⁻¹ * (c * y * c⁻¹) ∈ L :=
      mul_mem (inv_mem hyL) ((mem_normalizer_iff.1 hcL y).1 hyL)
    rw [← h.yamadaD₇_inf_centralizer_eq hW d hK hQ]
    exact ⟨h3, h.L_le_centralizer h4⟩
  have hmem := (h.act_D_leviA_iff d hK hcL).1 hact
  have hZN : centralizer (L : Set G) ≤ normalizer ((d.D ⊔ d.J₃ : Subgroup G) : Set G) :=
    (Subgroup.centralizer_le (sup_le (d.image_le _) (d.image_le _) :
      (d.D ⊔ d.J₃ : Subgroup G) ≤ L)).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨a, ha, z, hz, rfl⟩ := Common.exists_mul_of_le_normalizer hZN c hmem
  have hJ₃D : d.J₃ ≤ normalizer (d.D : Set G) :=
    ((le_sup_right : d.J₃ ≤ d.leviA ⊔ d.J₃).trans
      (le_sup_right : _ ≤ d.D ⊔ (d.leviA ⊔ d.J₃))).trans
      ((d.yamada_3_13_2_G).2.1.symm.le.trans inf_le_right)
  obtain ⟨δ, hδ, j, hj, rfl⟩ := Common.exists_mul_of_le_normalizer hJ₃D a ha
  have haL : δ * j ∈ L := mul_mem (d.image_le _ hδ) (d.image_le _ hj)
  have hzC : z ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
    refine ⟨hz, ?_⟩
    have := mul_mem (inv_mem (h.L_le_centralizer haL)) hct
    rwa [inv_mul_cancel_left] at this
  rw [h.centralizer_L_inf] at hzC
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hzC
  exact ⟨δ, h.D_le_yamadaD₇ hW d hK hQ hδ, j, hj, k, rfl⟩

private theorem nonempty_mulEquiv_yamadaBarK₁ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    Nonempty (↥(yamadaBarK₁ d t) ≃* SL(2, K)) := by
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨⟨e⟩, -⟩ := d.yamada_3_11_G
  have hA := h.leviA_le_normalizer_yamadaD₇ hW d hK hQ
  have hAD : d.leviA ≤ normalizer (d.D : Set G) :=
    le_sup_right.trans (h.D_sup_leviA_le_normalizer_D d)
  obtain ⟨bar⟩ := nonempty_mulEquiv_barSub (X := yamadaD₇ d t) (A := d.leviA) (K := yamadaK₁ d) hA
    (by rw [yamadaK₁_eq d hK4]; exact le_sup_right)
    (fun k hk => by
      rw [yamadaK₁_eq d hK4] at hk
      obtain ⟨δ, hδ, a, ha, rfl⟩ := Common.exists_mul_of_le_normalizer hAD k hk
      exact ⟨δ, h.D_le_yamadaD₇ hW d hK hQ hδ, a, ha, rfl⟩)
    (eq_bot_iff.2 fun x hx => by
      obtain ⟨hxA, hxD₇⟩ := Subgroup.mem_inf.1 hx
      have hxD : x ∈ d.D := by
        rw [← h.yamadaD₇_inf_centralizer_eq hW d hK hQ]
        exact ⟨hxD₇, h.L_le_centralizer (d.image_le _ hxA)⟩
      rw [← D_inf_leviA d]
      exact ⟨hxD, hxA⟩)
  exact ⟨(e.trans bar).symm⟩

private theorem rootGroup_r_le_leviA (d : G2Data L K) : d.rootGroup g2r ≤ d.leviA := fun g hg =>
  (d.yamada_3_11_G.2.2.1 g).2 (Or.inl ⟨g, hg, 1, one_mem _, (mul_one g).symm⟩)

private theorem J₁_le_leviA (d : G2Data L K) : d.J₁ ≤ d.leviA := fun g hg =>
  (d.yamada_3_11_G.2.2.1 g).2 (Or.inl ⟨1, one_mem _, g, hg, (one_mul g).symm⟩)

private theorem rootGroup_a_le_leviB (d : G2Data L K) : d.rootGroup g2a ≤ d.leviB := fun g hg =>
  (d.yamada_3_11_G.2.2.2 g).2 (Or.inl ⟨g, hg, 1, one_mem _, (mul_one g).symm⟩)

private theorem J₂_le_leviB (d : G2Data L K) : d.J₂ ≤ d.leviB := fun g hg =>
  (d.yamada_3_11_G.2.2.2 g).2 (Or.inl ⟨1, one_mem _, g, hg, (one_mul g).symm⟩)

private theorem S_le_yamadaK₁ (d : G2Data L K) (hK4 : 4 ≤ Nat.card K) : d.S ≤ yamadaK₁ d := by
  obtain ⟨-, -, -, -, -, hFD, -, -, -, -⟩ := d.inclusions
  obtain ⟨-, -, -, -, -, hM, -, -, hS⟩ := d.yamada_defs
  rw [yamadaK₁_eq d hK4, ← hS, ← hM]
  exact sup_le le_sup_left (sup_le ((rootGroup_r_le_leviA d).trans le_sup_right)
    (hFD.trans le_sup_left))

private theorem S_le_yamadaK₂ (d : G2Data L K) (hK4 : 4 ≤ Nat.card K) : d.S ≤ yamadaK₂ d := by
  obtain ⟨-, -, -, -, -, -, hFM, -, -, -⟩ := d.inclusions
  obtain ⟨-, -, -, -, hD, -, -, -, hS⟩ := d.yamada_defs
  rw [yamadaK₂_eq d hK4, ← hS, ← hD]
  exact sup_le (sup_le ((rootGroup_a_le_leviB d).trans le_sup_right) (hFM.trans le_sup_left))
    le_sup_left

private theorem J₁_le_yamadaK₁ (d : G2Data L K) (hK4 : 4 ≤ Nat.card K) : d.J₁ ≤ yamadaK₁ d := by
  rw [yamadaK₁_eq d hK4]
  exact (J₁_le_leviA d).trans le_sup_right

private theorem J₂_le_yamadaK₂ (d : G2Data L K) (hK4 : 4 ≤ Nat.card K) : d.J₂ ≤ yamadaK₂ d := by
  rw [yamadaK₂_eq d hK4]
  exact (J₂_le_leviB d).trans le_sup_right

private theorem yamadaS₅_inf_centralizer_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {A : Subgroup G}
    (hAJ : A ≤ d.J) (hAF : d.S ⊓ centralizer (A : Set G) ≤ d.F) :
    yamadaS₅ d t ⊓ centralizer (A : Set G) ≤ yamadaF₅ d t := by
  obtain ⟨⟨hS₅, -, -⟩, ⟨hSF, -, -⟩⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨-, -, -, -, -, hFD, -, hDS, -, -⟩ := d.inclusions
  have hJS : d.J ≤ normalizer (d.S : Set G) :=
    (h.J_le_centralizer_inf_normalizer_S d).trans inf_le_right
  have hsolv : Group.IsSolvable d.S := by
    have := d.isSylowOf_S.isPGroup.isNilpotent
    infer_instance
  have hcop : (Nat.card A).Coprime (Nat.card d.S) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hAJ)
      (coprime_card_J d d.isSylowOf_S.isPGroup)
  rw [hS₅]
  exact sup_inf_centralizer_le_of_coprime (h.q49_S_le_normalizer_yamadaF₅ hW d hK hQ) hSF
    (hFD.trans hDS) (Q44.F_le_F₅ d t) d.S_le_normalizers.2.2.2.2.1 (hAJ.trans hJS)
    (hAJ.trans (JWeight.J_le_normalizer_F hW h d hK hQ))
    (hAJ.trans (JWeight.J_le_normalizer_F₅ hW h d hK hQ))
    hsolv hcop hAF

private theorem yamada_5_59_N₂_kernel (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {c : G}
    (hcN : c ∈ normalizer (yamadaM₆ d t : Set G))
    (hc : c ∈ centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G))
    (hy : ∀ y ∈ yamadaK₂ d, (y * c)⁻¹ * (c * y) ∈ yamadaM₆ d t) :
    ∃ μ ∈ yamadaM₆ d t, ∃ j ∈ d.J₄, ∃ k : ℤ, c = μ * j * t ^ k := by
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  have hct : c ∈ centralizer ({t} : Set G) := hc.1
  have hcL : c ∈ normalizer (L : Set G) := h.centralizer_le_normalizer hct
  have hact : ∀ y ∈ d.M ⊔ d.leviB, y⁻¹ * (c * y * c⁻¹) ∈ d.M := by
    intro y hy'
    have hyK : y ∈ yamadaK₂ d := by rw [yamadaK₂_eq d hK4]; exact hy'
    have h1 := hy y hyK
    have h3 : y⁻¹ * (c * y * c⁻¹) ∈ yamadaM₆ d t := by
      have h2 : y⁻¹ * (c * y * c⁻¹) = c * ((y * c)⁻¹ * (c * y)) * c⁻¹ := by group
      rw [h2]
      exact (mem_normalizer_iff.1 hcN _).1 h1
    have hyL : y ∈ L := sup_le (d.image_le _) (d.image_le _) hy'
    have h4 : y⁻¹ * (c * y * c⁻¹) ∈ L :=
      mul_mem (inv_mem hyL) ((mem_normalizer_iff.1 hcL y).1 hyL)
    rw [← h.yamadaM₆_inf_centralizer_eq hW d hK hQ]
    exact ⟨h3, h.L_le_centralizer h4⟩
  have hmem := (h.act_M_leviB_iff d hK hcL).1 hact
  have hZN : centralizer (L : Set G) ≤ normalizer ((d.M ⊔ d.J₄ : Subgroup G) : Set G) :=
    (Subgroup.centralizer_le (sup_le (d.image_le _) (d.image_le _) :
      (d.M ⊔ d.J₄ : Subgroup G) ≤ L)).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨a, ha, z, hz, rfl⟩ := Common.exists_mul_of_le_normalizer hZN c hmem
  have hJ₄M : d.J₄ ≤ normalizer (d.M : Set G) :=
    ((le_sup_right : d.J₄ ≤ d.leviB ⊔ d.J₄).trans
      (le_sup_right : _ ≤ d.M ⊔ (d.leviB ⊔ d.J₄))).trans
      ((d.yamada_3_13_3_G).2.2.1.symm.le.trans inf_le_right)
  obtain ⟨μ, hμ, j, hj, rfl⟩ := Common.exists_mul_of_le_normalizer hJ₄M a ha
  have haL : μ * j ∈ L := mul_mem (d.image_le _ hμ) (d.image_le _ hj)
  have hzC : z ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
    refine ⟨hz, ?_⟩
    have := mul_mem (inv_mem (h.L_le_centralizer haL)) hct
    rwa [inv_mul_cancel_left] at this
  rw [h.centralizer_L_inf] at hzC
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hzC
  exact ⟨μ, h.M_le_yamadaM₆ hW d hK hQ hμ, j, hj, k, rfl⟩

private theorem nonempty_mulEquiv_yamadaBarK₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    Nonempty (↥(yamadaBarK₂ d t) ≃* SL(2, K)) := by
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨-, ⟨e⟩, -⟩ := d.yamada_3_11_G
  have hB := h.leviB_le_normalizer_yamadaM₆ hW d hK hQ
  have hBM : d.leviB ≤ normalizer (d.M : Set G) :=
    ((le_sup_left : d.leviB ≤ d.leviB ⊔ d.J₄).trans
      (le_sup_right : _ ≤ d.M ⊔ (d.leviB ⊔ d.J₄))).trans
      ((d.yamada_3_13_3_G).2.2.1.symm.le.trans inf_le_right)
  obtain ⟨bar⟩ := nonempty_mulEquiv_barSub (X := yamadaM₆ d t) (A := d.leviB) (K := yamadaK₂ d) hB
    (by rw [yamadaK₂_eq d hK4]; exact le_sup_right)
    (fun k hk => by
      rw [yamadaK₂_eq d hK4] at hk
      obtain ⟨μ, hμ, a, ha, rfl⟩ := Common.exists_mul_of_le_normalizer hBM k hk
      exact ⟨μ, h.M_le_yamadaM₆ hW d hK hQ hμ, a, ha, rfl⟩)
    (eq_bot_iff.2 fun x hx => by
      obtain ⟨hxB, hxM₆⟩ := Subgroup.mem_inf.1 hx
      have hxM : x ∈ d.M := by
        rw [← h.yamadaM₆_inf_centralizer_eq hW d hK hQ]
        exact ⟨hxM₆, h.L_le_centralizer (d.image_le _ hxB)⟩
      rw [← M_inf_leviB d]
      exact ⟨hxM, hxB⟩)
  exact ⟨(e.trans bar).symm⟩


theorem yamada_5_59_N₁_centralizer (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    t ∈ normalizer (yamadaD₇ d t : Set G) ∧ t ∉ yamadaD₇ d t ∧
      normalizer (yamadaD₇ d t : Set G) ≠ ⊤ ∧
      yamadaK₁ d ≤ normalizer (yamadaD₇ d t : Set G) ∧
      (centralizer ({yamadaT₁ d t} : Set (BarM (yamadaD₇ d t))) =
          barSub (yamadaD₇ d t) (normalizer (yamadaC₇ d t : Set G)) ∧
        barSub (yamadaD₇ d t) (normalizer (yamadaC₇ d t : Set G)) =
          barSub (yamadaD₇ d t) (centralizer ({t} : Set G) ⊓ normalizer (d.U : Set G))) ∧
      yamadaD₇ d t ⊓ centralizer ({t} : Set G) = d.D ∧
      (yamadaBarK₁ d t ≤ centralizer ({yamadaT₁ d t} : Set (BarM (yamadaD₇ d t))) ∧
        ((yamadaBarK₁ d t).subgroupOf
          (centralizer ({yamadaT₁ d t} : Set (BarM (yamadaD₇ d t))))).Normal ∧
        Nonempty (↥(yamadaBarK₁ d t) ≃* SL(2, K))) ∧
      (centralizer ({yamadaT₁ d t} : Set (BarM (yamadaD₇ d t))) ⊓
          centralizer (yamadaBarK₁ d t : Set (BarM (yamadaD₇ d t))) =
        zpowers (yamadaT₁ d t) ⊔ barSub (yamadaD₇ d t) d.J₃ ∧
      IsSylowOf 2 (zpowers (yamadaT₁ d t))
        (centralizer (yamadaBarK₁ d t : Set (BarM (yamadaD₇ d t))) ⊓
          centralizer ({yamadaT₁ d t} : Set (BarM (yamadaD₇ d t))))) := by
  classical
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨-, -, hsup, htN, htD⟩ := h.yamada_5_51 hW d hK hQ
  have hT := yamadaT₁_eq d htN
  have hKN := yamadaK₁_le_normalizer_yamadaD₇ hW h d hK hQ
  obtain ⟨hfac, hC₀⟩ := h.yamada_5_59_N₁_normalizer_factor hW d hK hQ
  have h553 := (h.yamada_5_55_3 hW d hK hQ).1
  have hNX : normalizer (yamadaC₇ d t : Set G) ≤ normalizer (yamadaD₇ d t : Set G) :=
    h553.1.le.trans h553.2
  have hcent := centralizer_barMap_eq_barSub_of_factor htN htD h.t_mul_t hsup hNX hfac hC₀
  have hKC : yamadaK₁ d ≤ centralizer ({t} : Set G) ⊓ normalizer (d.U : Set G) :=
    (yamadaK₁_le_inf d).trans (inf_le_inf_right _ h.L_le_centralizer)
  have hC₀N : centralizer ({t} : Set G) ⊓ normalizer (d.U : Set G) ≤
      normalizer (yamadaD₇ d t : Set G) := hC₀.trans hNX
  have hJ₃N : d.J₃ ≤ normalizer (yamadaD₇ d t : Set G) :=
    (J₃_le_J d).trans (h.J_le_normalizer_yamadaD₇ hW d hK hQ)
  have hZle : zpowers (barMap (yamadaD₇ d t) ⟨t, htN⟩) ⊔ barSub (yamadaD₇ d t) d.J₃ ≤
      centralizer ({barMap (yamadaD₇ d t) ⟨t, htN⟩} : Set (BarM (yamadaD₇ d t))) ⊓
        centralizer (barSub (yamadaD₇ d t) (yamadaK₁ d) : Set (BarM (yamadaD₇ d t))) := by
    refine zpowers_sup_barSub_le_centralizer htN
      (fun j hj => mem_centralizer_singleton_iff.1
        (h.L_le_centralizer (d.image_le _ hj)))
      (fun y hy => mem_centralizer_singleton_iff.1
        (h.L_le_centralizer ((yamadaK₁_le_inf d hy).1))) fun j hj y hy => ?_
    have hjL : j ∈ L := d.image_le _ hj
    have hyK : y ∈ d.D ⊔ d.leviA := by rw [← yamadaK₁_eq d hK4]; exact hy
    have hmemj : j ∈ (d.D ⊔ d.J₃) ⊔ centralizer (L : Set G) := mem_sup_left (mem_sup_right hj)
    have hact := (h.act_D_leviA_iff d hK (le_normalizer hjL)).2 hmemj y hyK
    have e : (y * j)⁻¹ * (j * y) = j⁻¹ * (y⁻¹ * (j * y * j⁻¹)) * j := by group
    rw [e]
    have := (mem_normalizer_iff.1 (inv_mem (hJ₃N hj)) _).1 (h.D_le_yamadaD₇ hW d hK hQ hact)
    simpa using this
  have hZ : centralizer ({barMap (yamadaD₇ d t) ⟨t, htN⟩} : Set (BarM (yamadaD₇ d t))) ⊓
      centralizer (yamadaBarK₁ d t : Set (BarM (yamadaD₇ d t))) =
      zpowers (barMap (yamadaD₇ d t) ⟨t, htN⟩) ⊔ barSub (yamadaD₇ d t) d.J₃ :=
    CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.centralizer_eq_of htN hcent.1
      (exists_barMap_eq_of_factor hC₀N hfac) (fun c hc hy => by
        obtain ⟨δ, hδ, j, hj, k, e⟩ := h.yamada_5_59_N₁_kernel hW d hK hQ c.2 hc
          (fun y hy' => hy ⟨y, hKN hy'⟩ hy')
        exact barMap_mem_zpowers_sup htN c.2 hδ hj (hJ₃N hj) e) hZle
  rw [hT]
  refine ⟨htN, htD, normalizer_yamadaD₇_ne_top hW h d hK hQ, hKN, hcent,
    h.yamadaD₇_inf_centralizer_eq hW d hK hQ, ⟨?_, ?_, nonempty_mulEquiv_yamadaBarK₁ hW h d hK hQ⟩,
    hZ, ?_⟩
  · rw [hcent.1, hcent.2]
    exact Subgroup.map_mono fun x hx => mem_subgroupOf.2 (hKC (mem_subgroupOf.1 hx))
  · rw [hcent.1, hcent.2]
    refine normal_barSub_subgroupOf_barSub hKC fun c hc k hk => ?_
    have hcL : c ∈ normalizer (L : Set G) := h.centralizer_le_normalizer hc.1
    have hcA : c ∈ normalizer ((L ⊓ normalizer (d.U : Set G) : Subgroup G) : Set G) :=
      Common.mem_normalizer_inf hcL (Subgroup.le_normalizer hc.2)
    exact (mem_normalizer_iff.1 (mem_normalizer_commutator hcA hcA) k).1 hk
  · rw [inf_comm, hZ]
    refine isSylowOf_zpowers_sup_of_odd (orderOf_barMap_involution htN htD h.t_mul_t)
      (fun g hg => ?_) (odd_card_barSub hJ₃N (J₃_le_J d) (odd_card_J d))
    have hg' := (hZle (mem_sup_right hg)).1
    exact mem_centralizer_singleton_iff.1 hg'

theorem yamada_5_59_N₁_P (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (yamadaD₇ d t ≤ yamadaP d t ∧ yamadaP d t ≤ normalizer (yamadaD₇ d t : Set G) ∧
      IsPGroup 2 (yamadaP d t)) ∧
      yamadaP d t ≤ yamadaN₁ d t ∧ t ∈ normalizer (yamadaP d t : Set G) ∧
      (∀ v ∈ yamadaBarP₁ d t, v * v = 1) ∧ Nat.card (yamadaBarP₁ d t) = (2 ^ f) ^ 2 ∧
      (commutatorWith (yamadaBarP₁ d t) (yamadaT₁ d t) ≠ ⊥ ∧
        commutatorWith (yamadaBarP₁ d t) (yamadaT₁ d t) ≤ yamadaBarK₁ d t) := by
  classical
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨-, hPR₈, -, -, -, -, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨⟨-, hR₈D⟩, -⟩ := h.yamada_5_56 hW d hK hQ
  obtain ⟨⟨-, htNP, -⟩, -, ⟨-, htN, -⟩⟩ := h.yamada_5_51 hW d hK hQ
  have hDP := yamadaD₇_le_yamadaP d t
  have hPN : yamadaP d t ≤ normalizer (yamadaD₇ d t : Set G) := hPR₈.trans hR₈D
  have hP2 : IsPGroup 2 (yamadaP d t) := (Q52.isPGroup_yamadaR₈ d t).to_le hPR₈
  have hKN := yamadaK₁_le_normalizer_yamadaD₇ hW h d hK hQ
  obtain ⟨-, hF₅D₇, -, -, -, -, helem⟩ := h.yamada_5_57_2 hW d hK hQ
  have hsq : ∀ p ∈ yamadaP d t, p * p ∈ yamadaD₇ d t := fun p hp => hF₅D₇ (helem p hp p hp).1
  have hab : ∀ x ∈ yamadaP d t, ∀ y ∈ yamadaP d t, ⁅x, y⁆ ∈ yamadaD₇ d t := fun x hx y hy =>
    hF₅D₇ (helem x hx y hy).2
  have hJ₁J : d.J₁ ≤ d.J := d.image_mono inf_le_left
  obtain ⟨hUY, hYX, -, hXF, -, -, -, -, -, -⟩ := d.inclusions
  have hPN₁ : yamadaP d t ≤ yamadaN₁ d t := by
    refine le_of_forall_fixed_of_commutator_mem (J := d.J₁) hDP hab
      (hJ₁J.trans (h.J_le_normalizer_yamadaP hW d hK hQ))
      (hJ₁J.trans (h.J_le_normalizer_yamadaD₇ hW d hK hQ))
      (by have := hP2.isNilpotent; infer_instance)
      (Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hJ₁J) (coprime_card_J d hP2))
      (fun c hc => ?_) (yamadaD₇_le_yamadaN₁ d t) (fun j hj p hp => ?_)
    · rcases hQ.branch with h8 | ⟨hK4', -⟩
      swap
      ·
        have hJ₁₄ : d.J₄ = d.J₁ := (d.yamada_3_9_4_four_G hK4').1.symm
        obtain ⟨hcP, hcC⟩ := Subgroup.mem_inf.1 hc
        have hc' : c ∈ ((yamadaM₆ d t : Set G) * (yamadaD₇ d t : Set G)) := by
          rw [← h.yamadaP_eq_mul hW d hK hQ]
          exact hcP
        obtain ⟨m, hm, e, he, rfl⟩ := Set.mem_mul.1 hc'
        refine mul_mem (h.yamadaF₅_le_yamadaD₇ hW d hK hQ
          (h.mem_yamadaF₅_of_fixed_J₄_yamadaM₆ hW d hK hQ m hm fun j hj => ?_)) he
        have hjJ : j ∈ d.J := J₄_le_J d hj
        have hJD := h.J_le_normalizer_yamadaD₇ hW d hK hQ hjJ
        have hJM := h.J_le_normalizer_yamadaM₆ hW d hK hQ hjJ
        have hmN : m ∈ normalizer (yamadaD₇ d t : Set G) :=
          hPN (h.yamadaM₆_le_yamadaP hW d hK hQ hm)
        have hjc : j * (m * e) * j⁻¹ = m * e := by
          rw [mem_centralizer_iff.1 hcC j (hJ₁₄ ▸ (show j ∈ d.J₄ from hj)), mul_inv_cancel_right]
        have h1 : j * m * j⁻¹ = m * e * (j * e * j⁻¹)⁻¹ := by
          refine eq_mul_inv_iff_mul_eq.2 ?_
          calc j * m * j⁻¹ * (j * e * j⁻¹) = j * (m * e) * j⁻¹ := by group
            _ = m * e := hjc
        have hD₇ : ⁅j, m⁆ ∈ yamadaD₇ d t := by
          rw [commutatorElement_def, h1,
            show m * e * (j * e * j⁻¹)⁻¹ * m⁻¹ = m * (e * (j * e * j⁻¹)⁻¹) * m⁻¹ by group]
          exact (mem_normalizer_iff.1 hmN _).1
            (mul_mem he (inv_mem ((mem_normalizer_iff.1 hJD e).1 he)))
        have hM₆ : ⁅j, m⁆ ∈ yamadaM₆ d t := by
          rw [commutatorElement_def]
          exact mul_mem ((mem_normalizer_iff.1 hJM m).1 hm) (inv_mem hm)
        rw [← h.yamadaM₆_inf_yamadaD₇ hW d hK hQ]
        exact Subgroup.mem_inf.2 ⟨hM₆, hD₇⟩
      have hAF : d.S ⊓ centralizer (d.J₁ : Set G) ≤ d.F := by
        rw [d.S_inf_centralizer_J₁ h8]
        exact hUY.trans (hYX.trans hXF)
      exact hF₅D₇ (yamadaS₅_inf_centralizer_le hW h d hK hQ hJ₁J hAF
        ⟨Q52.yamadaP_inf_centralizer_le hW h d hK hQ hJ₁J hAF hc, hc.2⟩)
    · have hjN₁ : j ∈ yamadaN₁ d t := yamadaK₁_le_yamadaN₁ d t (J₁_le_yamadaK₁ d hK4 hj)
      have e : ⁅j, p⁆ = j * (p * j⁻¹ * p⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem hjN₁ (conj_mem_normalClosureInNormalizer hKN (hPN hp) (inv_mem hjN₁))
  obtain ⟨-, -, -, -, ⟨hcent, -⟩, -⟩ := h.yamada_5_59_N₁_centralizer hW d hK hQ
  obtain ⟨hfac, -⟩ := h.yamada_5_59_N₁_normalizer_factor hW d hK hQ
  have hT := yamadaT₁_eq d htN
  rw [hT] at hcent
  refine ⟨⟨hDP, hPN, hP2⟩, hPN₁, htNP, mul_self_eq_one_of_mem_barSub hsq, ?_, ?_, ?_⟩
  ·
    have h1 := CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.card_barSub hDP hPN
    rw [h.card_yamadaP hW d hK hQ, h.card_yamadaD₇ hW d hK hQ] at h1
    have hq : 0 < Nat.card K ^ 10 := pow_pos Nat.card_pos 10
    have h2 : Nat.card (yamadaBarP₁ d t) = Nat.card K ^ 2 :=
      Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)
    rw [h2, hK]
  ·
    intro h0
    rw [hT] at h0
    refine not_subset_mul_of_card_lt (P := yamadaP d t) (X := yamadaD₇ d t) (S := d.S) ?_
      (subset_mul_of_commutatorWith_eq_bot htN hDP hPN
        ((yamadaD₇_le_yamadaC₇ d t).trans Subgroup.le_normalizer) hcent hfac
        (fun c hc hcP => (h.yamadaP_inf_centralizer_eq hW d hK hQ).le ⟨hcP, hc.1⟩) h0)
    obtain ⟨-, -, -, -, -, hFD, -, hDS, -, -⟩ := d.inclusions
    have hDle : d.D ≤ yamadaD₇ d t ⊓ d.S := le_inf (h.D_le_yamadaD₇ hW d hK hQ) hDS
    have c1 := Subgroup.card_le_of_le hDle
    rw [d.cards.2.2.2.2.2.1] at c1
    rw [h.card_yamadaD₇ hW d hK hQ, d.cards.2.2.2.2.2.2.2, h.card_yamadaP hW d hK hQ]
    have hq : 1 < Nat.card K := hQ.one_lt
    calc Nat.card K ^ 10 * Nat.card K ^ 6 = Nat.card K ^ 16 := by ring
      _ < Nat.card K ^ 12 * Nat.card K ^ 5 := by
        rw [← pow_add]
        exact Nat.pow_lt_pow_right hq (by norm_num)
      _ ≤ Nat.card K ^ 12 * Nat.card (yamadaD₇ d t ⊓ d.S : Subgroup G) :=
        Nat.mul_le_mul_left _ c1
  ·
    rw [hT]
    refine commutatorWith_barSub_le htN hKN fun p hp => ?_
    have hSN := h.S_le_normalizer_yamadaD₇ hW d hK hQ
    obtain ⟨⟨hS₅, -, -⟩, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
    have hpR : p⁻¹ ∈ normalizer (yamadaR₅ d t : Set G) := yamadaR₈_le d t (hPR₈ (inv_mem hp))
    have hκ := inv_mem (h.q49_crossed_mem_yamadaS₅ hW d hK hQ hpR)
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
    have e : p⁻¹ * t⁻¹ * p * t = (t * p⁻¹ * t * p⁻¹⁻¹)⁻¹ := by
      simp only [mul_inv_rev, inv_inv, htinv, mul_assoc]
    rw [hS₅, sup_comm] at hκ
    obtain ⟨f₀, hf₀, s, hs, hfs⟩ := Common.exists_mul_of_le_normalizer
      (h.q49_S_le_normalizer_yamadaF₅ hW d hK hQ) _ hκ
    refine ⟨s, S_le_yamadaK₁ d hK4 hs, s⁻¹ * f₀ * s, ?_, ?_⟩
    · have := (mem_normalizer_iff.1 (inv_mem (hSN hs)) f₀).1 (hF₅D₇ hf₀)
      simpa using this
    · rw [e, hfs]
      group

theorem yamada_5_59_N₁_data (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∃ α : ↥(yamadaBarK₁ d t) ≃* SL(2, K),
      RankOneData (yamadaBarK₁ d t) α (yamadaT₁ d t) (yamadaBarP₁ d t) f := by
  classical
  obtain ⟨htN, htD, hNtop, hKN, ⟨hcent, hNC⟩, hDC, ⟨hKt, hKn, ⟨α₀⟩⟩, hCK, hsyl⟩ :=
    h.yamada_5_59_N₁_centralizer hW d hK hQ
  obtain ⟨⟨hDP, hPN, hP2⟩, hPN₁, htP, hsq, hcard, hcomm_ne, hcomm_le⟩ :=
    h.yamada_5_59_N₁_P hW d hK hQ
  have hbarN : yamadaBarN₁ d t = normalClosure (yamadaBarK₁ d t : Set (BarM (yamadaD₇ d t))) :=
    barSub_yamadaN₁ d t hKN
  have hkgroup : CFSG.SectionRank.IsKGroupCat (BarM (yamadaD₇ d t)) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isKGroupCat_of_section_of_kProper h.kproper hNtop
      ((yamadaD₇ d t).subgroupOf (normalizer (yamadaD₇ d t : Set G)))
  have hτ : orderOf (yamadaT₁ d t) = 2 := by
    rw [yamadaT₁_eq d htN]
    have ht2 : t * t = 1 := by rw [← sq, ← h.ht, pow_orderOf_eq_one]
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, ← map_mul]
      have : (⟨t, htN⟩ * ⟨t, htN⟩ : normalizer (yamadaD₇ d t : Set G)) = 1 := Subtype.ext ht2
      rw [this, map_one]
    · intro h1
      exact htD
        ((CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.barMap_eq_one_iff).1 h1)
  have hτV : yamadaT₁ d t ∈ normalizer (yamadaBarP₁ d t : Set (BarM (yamadaD₇ d t))) := by
    rw [yamadaT₁_eq d htN, mem_normalizer_iff]
    intro y
    obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective ((yamadaD₇ d t).subgroupOf
      (normalizer (yamadaD₇ d t : Set G))) y
    have hy : y = barMap (yamadaD₇ d t) m := hm.symm
    have e : barMap (yamadaD₇ d t) ⟨t, htN⟩ * y * (barMap (yamadaD₇ d t) ⟨t, htN⟩)⁻¹ =
        barMap (yamadaD₇ d t) (⟨t, htN⟩ * m * ⟨t, htN⟩⁻¹) := by
      rw [hy, map_mul, map_mul, map_inv]
    rw [e, hy]
    change barMap (yamadaD₇ d t) m ∈ barSub (yamadaD₇ d t) (yamadaP d t) ↔
      barMap (yamadaD₇ d t) (⟨t, htN⟩ * m * ⟨t, htN⟩⁻¹) ∈ barSub (yamadaD₇ d t) (yamadaP d t)
    rw [CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.mem_barSub_iff hDP,
      CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.mem_barSub_iff hDP]
    exact mem_normalizer_iff.1 htP (m : G)
  refine ⟨α₀, ?_⟩
  exact
    { kGroup := hkgroup
      two_le := h.two_le
      card_k := hK
      orderOf_tau := hτ
      le_centralizer := hKt
      normal_in_centralizer := hKn
      sylow := hsyl
      sq_eq_one := hsq
      card_V := hcard
      le_normalClosure := by
        rw [← hbarN]
        exact Subgroup.map_mono fun x hx => mem_subgroupOf.2 (hPN₁ (mem_subgroupOf.1 hx))
      tau_mem_normalizer := hτV
      commutatorWith_ne_bot := hcomm_ne
      commutatorWith_le := hcomm_le }

theorem yamada_5_59_N₁ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    IsSylowOf 2 (yamadaP d t) (yamadaN₁ d t) ∧
      yamadaBarN₁ d t = normalClosure (yamadaBarK₁ d t : Set (BarM (yamadaD₇ d t))) ∧
      ∃ α : ↥(yamadaBarK₁ d t) ≃* SL(2, K),
        ExactClosure (yamadaBarK₁ d t) α (yamadaT₁ d t) (yamadaBarP₁ d t) f := by
  classical
  obtain ⟨htN, htD, hNtop, hKN, hc2, hDC, hK3, hCK, hsyl⟩ :=
    h.yamada_5_59_N₁_centralizer hW d hK hQ
  obtain ⟨⟨hDP, hPN, hP2⟩, hPN₁, -⟩ := h.yamada_5_59_N₁_P hW d hK hQ
  obtain ⟨α₀, hdata⟩ := h.yamada_5_59_N₁_data hW d hK hQ
  have hex := hdata.exactClosure CFSG.CGT.PushingUpLit.CGT6K1.catSelector_holds
    CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer.smallSurvivorsNoElementary
  refine ⟨?_, barSub_yamadaN₁ d t hKN, α₀, hex⟩
  exact CFSG.LocalAnalysis.EvenBN.Common.RankOneLayerRadical.isSylowOf_normalClosureInNormalizer
    (hP2.to_le hDP) hDP hPN hKN hex.2.2.2.1

theorem yamada_5_59_N₂_centralizer (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    t ∈ normalizer (yamadaM₆ d t : Set G) ∧ t ∉ yamadaM₆ d t ∧
      normalizer (yamadaM₆ d t : Set G) ≠ ⊤ ∧
      yamadaK₂ d ≤ normalizer (yamadaM₆ d t : Set G) ∧
      (centralizer ({yamadaT₂ d t} : Set (BarM (yamadaM₆ d t))) =
          barSub (yamadaM₆ d t) (normalizer (yamadaL₆ d t : Set G)) ∧
        barSub (yamadaM₆ d t) (normalizer (yamadaL₆ d t : Set G)) =
          barSub (yamadaM₆ d t) (centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G))) ∧
      yamadaM₆ d t ⊓ centralizer ({t} : Set G) = d.M ∧
      (yamadaBarK₂ d t ≤ centralizer ({yamadaT₂ d t} : Set (BarM (yamadaM₆ d t))) ∧
        ((yamadaBarK₂ d t).subgroupOf
          (centralizer ({yamadaT₂ d t} : Set (BarM (yamadaM₆ d t))))).Normal ∧
        Nonempty (↥(yamadaBarK₂ d t) ≃* SL(2, K))) ∧
      (centralizer ({yamadaT₂ d t} : Set (BarM (yamadaM₆ d t))) ⊓
          centralizer (yamadaBarK₂ d t : Set (BarM (yamadaM₆ d t))) =
        zpowers (yamadaT₂ d t) ⊔ barSub (yamadaM₆ d t) d.J₄ ∧
      IsSylowOf 2 (zpowers (yamadaT₂ d t))
        (centralizer (yamadaBarK₂ d t : Set (BarM (yamadaM₆ d t))) ⊓
          centralizer ({yamadaT₂ d t} : Set (BarM (yamadaM₆ d t))))) := by
  classical
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨hsup, htN, htD⟩ := (h.yamada_5_44_1 hW d hK hQ).1
  have hT := yamadaT₂_eq d htN
  have hKN := yamadaK₂_le_normalizer_yamadaM₆ hW h d hK hQ
  obtain ⟨hfac, hC₀⟩ := h.yamada_5_59_N₂_normalizer_factor hW d hK hQ
  have h553 := (h.yamada_5_55_3 hW d hK hQ).2
  have hNX : normalizer (yamadaL₆ d t : Set G) ≤ normalizer (yamadaM₆ d t : Set G) :=
    h553.1.le.trans h553.2
  have hcent := centralizer_barMap_eq_barSub_of_factor htN htD h.t_mul_t hsup hNX hfac hC₀
  have hKC : yamadaK₂ d ≤ centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G) :=
    (yamadaK₂_le_inf d).trans (inf_le_inf_right _ h.L_le_centralizer)
  have hC₀N : centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G) ≤
      normalizer (yamadaM₆ d t : Set G) := hC₀.trans hNX
  have hJ₄N : d.J₄ ≤ normalizer (yamadaM₆ d t : Set G) :=
    (J₄_le_J d).trans (h.J_le_normalizer_yamadaM₆ hW d hK hQ)
  have hZle : zpowers (barMap (yamadaM₆ d t) ⟨t, htN⟩) ⊔ barSub (yamadaM₆ d t) d.J₄ ≤
      centralizer ({barMap (yamadaM₆ d t) ⟨t, htN⟩} : Set (BarM (yamadaM₆ d t))) ⊓
        centralizer (barSub (yamadaM₆ d t) (yamadaK₂ d) : Set (BarM (yamadaM₆ d t))) := by
    refine zpowers_sup_barSub_le_centralizer htN
      (fun j hj => mem_centralizer_singleton_iff.1
        (h.L_le_centralizer (d.image_le _ hj)))
      (fun y hy => mem_centralizer_singleton_iff.1
        (h.L_le_centralizer ((yamadaK₂_le_inf d hy).1))) fun j hj y hy => ?_
    have hjL : j ∈ L := d.image_le _ hj
    have hyK : y ∈ d.M ⊔ d.leviB := by rw [← yamadaK₂_eq d hK4]; exact hy
    have hmemj : j ∈ (d.M ⊔ d.J₄) ⊔ centralizer (L : Set G) := mem_sup_left (mem_sup_right hj)
    have hact := (h.act_M_leviB_iff d hK (le_normalizer hjL)).2 hmemj y hyK
    have e : (y * j)⁻¹ * (j * y) = j⁻¹ * (y⁻¹ * (j * y * j⁻¹)) * j := by group
    rw [e]
    have := (mem_normalizer_iff.1 (inv_mem (hJ₄N hj)) _).1 (h.M_le_yamadaM₆ hW d hK hQ hact)
    simpa using this
  have hZ : centralizer ({barMap (yamadaM₆ d t) ⟨t, htN⟩} : Set (BarM (yamadaM₆ d t))) ⊓
      centralizer (yamadaBarK₂ d t : Set (BarM (yamadaM₆ d t))) =
      zpowers (barMap (yamadaM₆ d t) ⟨t, htN⟩) ⊔ barSub (yamadaM₆ d t) d.J₄ :=
    CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.centralizer_eq_of htN hcent.1
      (exists_barMap_eq_of_factor hC₀N hfac) (fun c hc hy => by
        obtain ⟨μ, hμ, j, hj, k, e⟩ := h.yamada_5_59_N₂_kernel hW d hK hQ c.2 hc
          (fun y hy' => hy ⟨y, hKN hy'⟩ hy')
        exact barMap_mem_zpowers_sup htN c.2 hμ hj (hJ₄N hj) e) hZle
  rw [hT]
  refine ⟨htN, htD, normalizer_yamadaM₆_ne_top hW h d hK hQ, hKN, hcent,
    h.yamadaM₆_inf_centralizer_eq hW d hK hQ, ⟨?_, ?_, nonempty_mulEquiv_yamadaBarK₂ hW h d hK hQ⟩,
    hZ, ?_⟩
  · rw [hcent.1, hcent.2]
    exact Subgroup.map_mono fun x hx => mem_subgroupOf.2 (hKC (mem_subgroupOf.1 hx))
  · rw [hcent.1, hcent.2]
    refine normal_barSub_subgroupOf_barSub hKC fun c hc k hk => ?_
    have hcL : c ∈ normalizer (L : Set G) := h.centralizer_le_normalizer hc.1
    have hcA : c ∈ normalizer ((L ⊓ normalizer (d.Y : Set G) : Subgroup G) : Set G) :=
      Common.mem_normalizer_inf hcL (Subgroup.le_normalizer hc.2)
    exact (mem_normalizer_iff.1 (mem_normalizer_commutator hcA hcA) k).1 hk
  · rw [inf_comm, hZ]
    refine isSylowOf_zpowers_sup_of_odd (orderOf_barMap_involution htN htD h.t_mul_t)
      (fun g hg => ?_) (odd_card_barSub hJ₄N (J₄_le_J d) (odd_card_J d))
    have hg' := (hZle (mem_sup_right hg)).1
    exact mem_centralizer_singleton_iff.1 hg'

theorem yamada_5_59_N₂_P (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (yamadaM₆ d t ≤ yamadaP d t ∧ yamadaP d t ≤ normalizer (yamadaM₆ d t : Set G) ∧
      IsPGroup 2 (yamadaP d t)) ∧
      yamadaP d t ≤ yamadaN₂ d t ∧ t ∈ normalizer (yamadaP d t : Set G) ∧
      (∀ v ∈ yamadaBarP₂ d t, v * v = 1) ∧ Nat.card (yamadaBarP₂ d t) = (2 ^ f) ^ 2 ∧
      (commutatorWith (yamadaBarP₂ d t) (yamadaT₂ d t) ≠ ⊥ ∧
        commutatorWith (yamadaBarP₂ d t) (yamadaT₂ d t) ≤ yamadaBarK₂ d t) := by
  classical
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨-, hPR₈, -, -, -, -, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨-, ⟨-, hR₈M⟩⟩ := h.yamada_5_56 hW d hK hQ
  obtain ⟨⟨-, htNP, -⟩, -, -⟩ := h.yamada_5_51 hW d hK hQ
  obtain ⟨-, htN, -⟩ := (h.yamada_5_44_1 hW d hK hQ).1
  have hMP := h.yamadaM₆_le_yamadaP hW d hK hQ
  have hPN : yamadaP d t ≤ normalizer (yamadaM₆ d t : Set G) := hPR₈.trans hR₈M
  have hP2 : IsPGroup 2 (yamadaP d t) := (Q52.isPGroup_yamadaR₈ d t).to_le hPR₈
  have hKN := yamadaK₂_le_normalizer_yamadaM₆ hW h d hK hQ
  obtain ⟨hF₅M₆, -, -, -, -, -, helem⟩ := h.yamada_5_57_2 hW d hK hQ
  have hsq : ∀ p ∈ yamadaP d t, p * p ∈ yamadaM₆ d t := fun p hp => hF₅M₆ (helem p hp p hp).1
  have hab : ∀ x ∈ yamadaP d t, ∀ y ∈ yamadaP d t, ⁅x, y⁆ ∈ yamadaM₆ d t := fun x hx y hy =>
    hF₅M₆ (helem x hx y hy).2
  have hJ₂J : d.J₂ ≤ d.J := d.image_mono inf_le_left
  obtain ⟨-, -, -, -, hWF, -, -, -, -, -⟩ := d.inclusions
  obtain ⟨-, -, hv, -, -, -, -, -, -⟩ := d.yamada_defs
  have hAF : d.S ⊓ centralizer (d.J₂ : Set G) ≤ d.F := by
    rw [(h.J₂_facts d hK).2.2.1]
    exact (le_sup_left.trans hv.le).trans hWF
  have hPN₂ : yamadaP d t ≤ yamadaN₂ d t := by
    refine le_of_forall_fixed_of_commutator_mem (J := d.J₂) hMP hab
      (hJ₂J.trans (h.J_le_normalizer_yamadaP hW d hK hQ))
      (hJ₂J.trans (h.J_le_normalizer_yamadaM₆ hW d hK hQ))
      (by have := hP2.isNilpotent; infer_instance)
      (Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hJ₂J) (coprime_card_J d hP2))
      (fun c hc => ?_) (yamadaM₆_le_yamadaN₂ d t) (fun j hj p hp => ?_)
    · exact hF₅M₆ (yamadaS₅_inf_centralizer_le hW h d hK hQ hJ₂J hAF
        ⟨Q52.yamadaP_inf_centralizer_le hW h d hK hQ hJ₂J hAF hc, hc.2⟩)
    · have hjN₂ : j ∈ yamadaN₂ d t := yamadaK₂_le_yamadaN₂ d t (J₂_le_yamadaK₂ d hK4 hj)
      have e : ⁅j, p⁆ = j * (p * j⁻¹ * p⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem hjN₂ (conj_mem_normalClosureInNormalizer hKN (hPN hp) (inv_mem hjN₂))
  obtain ⟨-, -, -, -, ⟨hcent, -⟩, -⟩ := h.yamada_5_59_N₂_centralizer hW d hK hQ
  obtain ⟨hfac, -⟩ := h.yamada_5_59_N₂_normalizer_factor hW d hK hQ
  have hT := yamadaT₂_eq d htN
  rw [hT] at hcent
  refine ⟨⟨hMP, hPN, hP2⟩, hPN₂, htNP, mul_self_eq_one_of_mem_barSub hsq, ?_, ?_, ?_⟩
  ·
    have h1 := CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.card_barSub hMP hPN
    rw [h.card_yamadaP hW d hK hQ, Q44.card_M₆ hW h d hK hQ] at h1
    have hq : 0 < Nat.card K ^ 10 := pow_pos Nat.card_pos 10
    have h2 : Nat.card (yamadaBarP₂ d t) = Nat.card K ^ 2 :=
      Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)
    rw [h2, hK]
  ·
    intro h0
    rw [hT] at h0
    refine not_subset_mul_of_card_lt (P := yamadaP d t) (X := yamadaM₆ d t) (S := d.S) ?_
      (subset_mul_of_commutatorWith_eq_bot htN hMP hPN
        ((h.yamadaM₆_le_yamadaL₆ hW d hK hQ).trans Subgroup.le_normalizer) hcent hfac
        (fun c hc hcP => (h.yamadaP_inf_centralizer_eq hW d hK hQ).le ⟨hcP, hc.1⟩) h0)
    obtain ⟨-, -, -, -, -, -, -, -, hMS, -⟩ := d.inclusions
    have hMle : d.M ≤ yamadaM₆ d t ⊓ d.S := le_inf (h.M_le_yamadaM₆ hW d hK hQ) hMS
    have c1 := Subgroup.card_le_of_le hMle
    rw [d.cards.2.2.2.2.2.2.1] at c1
    rw [Q44.card_M₆ hW h d hK hQ, d.cards.2.2.2.2.2.2.2, h.card_yamadaP hW d hK hQ]
    have hq : 1 < Nat.card K := hQ.one_lt
    calc Nat.card K ^ 10 * Nat.card K ^ 6 = Nat.card K ^ 16 := by ring
      _ < Nat.card K ^ 12 * Nat.card K ^ 5 := by
        rw [← pow_add]
        exact Nat.pow_lt_pow_right hq (by norm_num)
      _ ≤ Nat.card K ^ 12 * Nat.card (yamadaM₆ d t ⊓ d.S : Subgroup G) :=
        Nat.mul_le_mul_left _ c1
  ·
    rw [hT]
    refine commutatorWith_barSub_le htN hKN fun p hp => ?_
    have hSN := h.S_le_normalizer_yamadaM₆ hW d hK hQ
    obtain ⟨⟨hS₅, -, -⟩, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
    have hpR : p⁻¹ ∈ normalizer (yamadaR₅ d t : Set G) := yamadaR₈_le d t (hPR₈ (inv_mem hp))
    have hκ := inv_mem (h.q49_crossed_mem_yamadaS₅ hW d hK hQ hpR)
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
    have e : p⁻¹ * t⁻¹ * p * t = (t * p⁻¹ * t * p⁻¹⁻¹)⁻¹ := by
      simp only [mul_inv_rev, inv_inv, htinv, mul_assoc]
    rw [hS₅, sup_comm] at hκ
    obtain ⟨f₀, hf₀, s, hs, hfs⟩ := Common.exists_mul_of_le_normalizer
      (h.q49_S_le_normalizer_yamadaF₅ hW d hK hQ) _ hκ
    refine ⟨s, S_le_yamadaK₂ d hK4 hs, s⁻¹ * f₀ * s, ?_, ?_⟩
    · have := (mem_normalizer_iff.1 (inv_mem (hSN hs)) f₀).1 (hF₅M₆ hf₀)
      simpa using this
    · rw [e, hfs]
      group

theorem yamada_5_59_N₂_data (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∃ α : ↥(yamadaBarK₂ d t) ≃* SL(2, K),
      RankOneData (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f := by
  classical
  obtain ⟨htN, htD, hNtop, hKN, ⟨hcent, hNC⟩, hDC, ⟨hKt, hKn, ⟨α₀⟩⟩, hCK, hsyl⟩ :=
    h.yamada_5_59_N₂_centralizer hW d hK hQ
  obtain ⟨⟨hDP, hPN, hP2⟩, hPN₁, htP, hsq, hcard, hcomm_ne, hcomm_le⟩ :=
    h.yamada_5_59_N₂_P hW d hK hQ
  have hbarN : yamadaBarN₂ d t = normalClosure (yamadaBarK₂ d t : Set (BarM (yamadaM₆ d t))) :=
    barSub_yamadaN₂ d t hKN
  have hkgroup : CFSG.SectionRank.IsKGroupCat (BarM (yamadaM₆ d t)) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isKGroupCat_of_section_of_kProper h.kproper hNtop
      ((yamadaM₆ d t).subgroupOf (normalizer (yamadaM₆ d t : Set G)))
  have hτ : orderOf (yamadaT₂ d t) = 2 := by
    rw [yamadaT₂_eq d htN]
    have ht2 : t * t = 1 := by rw [← sq, ← h.ht, pow_orderOf_eq_one]
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, ← map_mul]
      have : (⟨t, htN⟩ * ⟨t, htN⟩ : normalizer (yamadaM₆ d t : Set G)) = 1 := Subtype.ext ht2
      rw [this, map_one]
    · intro h1
      exact htD
        ((CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.barMap_eq_one_iff).1 h1)
  have hτV : yamadaT₂ d t ∈ normalizer (yamadaBarP₂ d t : Set (BarM (yamadaM₆ d t))) := by
    rw [yamadaT₂_eq d htN, mem_normalizer_iff]
    intro y
    obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective ((yamadaM₆ d t).subgroupOf
      (normalizer (yamadaM₆ d t : Set G))) y
    have hy : y = barMap (yamadaM₆ d t) m := hm.symm
    have e : barMap (yamadaM₆ d t) ⟨t, htN⟩ * y * (barMap (yamadaM₆ d t) ⟨t, htN⟩)⁻¹ =
        barMap (yamadaM₆ d t) (⟨t, htN⟩ * m * ⟨t, htN⟩⁻¹) := by
      rw [hy, map_mul, map_mul, map_inv]
    rw [e, hy]
    change barMap (yamadaM₆ d t) m ∈ barSub (yamadaM₆ d t) (yamadaP d t) ↔
      barMap (yamadaM₆ d t) (⟨t, htN⟩ * m * ⟨t, htN⟩⁻¹) ∈ barSub (yamadaM₆ d t) (yamadaP d t)
    rw [CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.mem_barSub_iff hDP,
      CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.mem_barSub_iff hDP]
    exact mem_normalizer_iff.1 htP (m : G)
  refine ⟨α₀, ?_⟩
  exact
    { kGroup := hkgroup
      two_le := h.two_le
      card_k := hK
      orderOf_tau := hτ
      le_centralizer := hKt
      normal_in_centralizer := hKn
      sylow := hsyl
      sq_eq_one := hsq
      card_V := hcard
      le_normalClosure := by
        rw [← hbarN]
        exact Subgroup.map_mono fun x hx => mem_subgroupOf.2 (hPN₁ (mem_subgroupOf.1 hx))
      tau_mem_normalizer := hτV
      commutatorWith_ne_bot := hcomm_ne
      commutatorWith_le := hcomm_le }

theorem yamada_5_59_N₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    IsSylowOf 2 (yamadaP d t) (yamadaN₂ d t) ∧
      yamadaBarN₂ d t = normalClosure (yamadaBarK₂ d t : Set (BarM (yamadaM₆ d t))) ∧
      ∃ α : ↥(yamadaBarK₂ d t) ≃* SL(2, K),
        ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f := by
  classical
  obtain ⟨htN, htD, hNtop, hKN, hc2, hDC, hK3, hCK, hsyl⟩ :=
    h.yamada_5_59_N₂_centralizer hW d hK hQ
  obtain ⟨⟨hDP, hPN, hP2⟩, hPN₁, -⟩ := h.yamada_5_59_N₂_P hW d hK hQ
  obtain ⟨α₀, hdata⟩ := h.yamada_5_59_N₂_data hW d hK hQ
  have hex := hdata.exactClosure CFSG.CGT.PushingUpLit.CGT6K1.catSelector_holds
    CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer.smallSurvivorsNoElementary
  refine ⟨?_, barSub_yamadaN₂ d t hKN, α₀, hex⟩
  exact CFSG.LocalAnalysis.EvenBN.Common.RankOneLayerRadical.isSylowOf_normalClosureInNormalizer
    (hP2.to_le hDP) hDP hPN hKN hex.2.2.2.1

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
