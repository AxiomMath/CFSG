module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.SectionRank

open Subgroup CFSG.LocalCores

variable {G : Type*} [Group G] [Finite G]

theorem exists_pow_layerMul_eq_one {p : ℕ} (hp : p.Prime) (x : ∀ K : ComponentIndex G, K.1)
    (hx : ∀ K, p ∣ Nat.card K.1 → x K = 1) : ∃ n, ¬ p ∣ n ∧ layerMul G x ^ n = 1 := by
  classical
  refine ⟨∏ K ∈ Finset.univ.filter (fun K : ComponentIndex G => ¬ p ∣ Nat.card K.1),
    Nat.card K.1, ?_, ?_⟩
  · rw [hp.prime.dvd_finsetProd_iff]
    rintro ⟨K, hK, hdvd⟩
    exact (Finset.mem_filter.mp hK).2 hdvd
  · rw [← map_pow]
    convert map_one (layerMul G)
    funext K
    rw [Pi.pow_apply, Pi.one_apply]
    by_cases hK : p ∣ Nat.card K.1
    · rw [hx K hK, one_pow]
    · have hmem : K ∈ Finset.univ.filter (fun K : ComponentIndex G => ¬ p ∣ Nat.card K.1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ K, hK⟩
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun K : ComponentIndex G => Nat.card K.1) hmem
      rw [hc, pow_mul, pow_card_eq_one', one_pow]

theorem three_le_pRank_of_components {p : ℕ} [hp : Fact p.Prime] {L₁ L₂ : Subgroup G}
    (h₁ : IsComponent L₁) (h₂ : IsComponent L₂) (hne : L₁ ≠ L₂) {z x₁ x₂ : G}
    (hz : z ∈ center G) (hzp : orderOf z = p) (hx₁ : x₁ ∈ L₁) (hx₂ : x₂ ∈ L₂)
    (hx₁p : orderOf x₁ = p) (hx₂p : orderOf x₂ = p) (hx₁c : ¬ ∀ k ∈ L₁, Commute k x₁)
    (hx₂c : ¬ ∀ k ∈ L₂, Commute k x₂) : 3 ≤ Open.pRank p (⊤ : Subgroup G) := by
  have h12 : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b := by
    rcases distinct_components_commute h₁ h₂ with h | h
    · exact absurd h hne
    · exact fun a ha b hb =>
        (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h ha) b hb).symm
  have hzc : ∀ (g : G) (m : ℤ), Commute (z ^ m) g := fun g m =>
    (show Commute z g from (mem_center_iff.mp hz g).symm).zpow_left m
  have hcomm₀ : ∀ a b : zpowers z, a * b = b * a := by
    rintro ⟨_, m, rfl⟩ ⟨_, n, rfl⟩
    exact Subtype.ext (zpow_mul_comm z m n)
  have hpow₀ : ∀ a : zpowers z, a ^ p = 1 := by
    rintro ⟨_, m, rfl⟩
    refine Subtype.ext ?_
    change (z ^ m) ^ p = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hzp,
      pow_orderOf_eq_one, one_zpow]
  have hcard₀ : Nat.card (zpowers z) = p ^ 1 := by rw [Nat.card_zpowers, hzp, pow_one]
  have hx₁1 : x₁ ∉ (zpowers z).subtype.range := by
    rw [range_subtype]
    rintro ⟨m, rfl⟩
    exact hx₁c fun k _ => (hzc k m).symm
  obtain ⟨F₁, hF₁, hcomm₁, hpow₁, hcard₁, hrange₁⟩ := exists_extend hcomm₀ hpow₀ hcard₀
    (zpowers z).subtype (subtype_injective _) (hx₁p ▸ pow_orderOf_eq_one x₁) hx₁1
    (fun ⟨_, m, hm⟩ => hm ▸ hzc x₁ m)
  have hrange : ∀ a, Commute (F₁ a) x₂ ∧ ∀ k ∈ L₂, Commute k (F₁ a) := by
    intro a
    obtain ⟨⟨_, m, rfl⟩, n, hn⟩ := hrange₁ a
    rw [hn]
    exact ⟨(hzc x₂ m).mul_left ((h12 x₁ hx₁ x₂ hx₂).pow_left n),
      fun k hk => ((hzc k m).symm).mul_right ((h12 x₁ hx₁ k hk).symm.pow_right n)⟩
  have hx₂1 : x₂ ∉ F₁.range := by
    rintro ⟨a, rfl⟩
    exact hx₂c (hrange a).2
  obtain ⟨F₂, hF₂, hcomm₂, hpow₂, hcard₂, -⟩ := exists_extend hcomm₁ hpow₁ hcard₁ F₁ hF₁
    (hx₂p ▸ pow_orderOf_eq_one x₂) hx₂1 fun a => (hrange a).1
  exact le_pRank_of_injective hp.out.one_lt hcomm₂ hpow₂ hcard₂ F₂ hF₂ le_top

theorem central_product_quotient_criterion (hE : layer G = ⊤) (hG : IsStronglyQuasithin G)
    (helt : ∀ L : Subgroup G, IsComponent L → ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card L →
      ∃ x : L, orderOf x = p ∧ x ∉ center L)
    (hquot : ∀ L : Subgroup G, IsComponent L → ∀ (A : Subgroup L) [A.Normal], A ≤ center L →
      IsStronglyQuasithin (L ⧸ A))
    (N : Subgroup G) [N.Normal] (hN : N ≤ center G) : IsStronglyQuasithin (G ⧸ N) := by
  rw [isStronglyQuasithin_iff]
  intro p hp hp2
  have : Fact p.Prime := ⟨hp⟩
  have hp1 := hp.one_lt
  have hG2 := (isStronglyQuasithin_iff.mp hG) p hp hp2
  by_cases hpN : p ∣ Nat.card N
  swap
  · rw [pRank_quotient_eq N hpN]
    exact hG2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := N) p hpN
  have hzc : (z : G) ∈ center G := hN z.2
  have hzp : orderOf (z : G) = p := by rw [orderOf_coe, hz]
  have hnc : ∀ (L : Subgroup G) (x : L), x ∉ center L → ¬ ∀ k ∈ L, Commute k (x : G) :=
    fun L x hx h => hx (mem_center_iff.mpr fun g => Subtype.ext (h g g.2))
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ComponentIndex G, p ∣ Nat.card L₀.1 := by
    by_contra hnone
    push Not at hnone
    obtain ⟨y, hy⟩ := exists_layerMul_eq (hE ▸ mem_top (z : G) : (z : G) ∈ layer G)
    obtain ⟨n, hpn, hn⟩ := exists_pow_layerMul_eq_one hp y fun K hK => absurd hK (hnone K)
    rw [hy] at hn
    exact hpn (hzp ▸ orderOf_dvd_of_pow_eq_one hn)
  have huniq : ∀ L : ComponentIndex G, p ∣ Nat.card L.1 → L = L₀ := by
    intro L hL
    by_contra hne
    obtain ⟨x₀, hx₀p, hx₀c⟩ := helt L₀.1 L₀.2 p hp hp2 hL₀
    obtain ⟨x, hxp, hxc⟩ := helt L.1 L.2 p hp hp2 hL
    have h3 := three_le_pRank_of_components L₀.2 L.2 (fun h => hne (Subtype.ext h).symm) hzc hzp
      x₀.2 x.2 (by rw [orderOf_coe, hx₀p]) (by rw [orderOf_coe, hxp]) (hnc _ _ hx₀c)
      (hnc _ _ hxc)
    omega
  let f : L₀.1 →* G ⧸ N := (QuotientGroup.mk' N).comp L₀.1.subtype
  have hT : ∀ g : G ⧸ N, g ^ p = 1 → g ∈ f.range := by
    intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N g
    obtain ⟨y, rfl⟩ := exists_layerMul_eq (hE ▸ mem_top x : x ∈ layer G)
    have hL₀M : ∀ l ∈ L₀.1, l ∈ f.range.comap (QuotientGroup.mk' N) := fun l hl =>
      ⟨⟨l, hl⟩, rfl⟩
    have hdecomp := layerMul_eq_mul_update y L₀
    have hu := commute_layerMul_update y L₀ (y L₀).2
    obtain ⟨n, hpn, hun⟩ := exists_pow_layerMul_eq_one hp (Function.update y L₀ 1)
      fun K hK => by
        obtain rfl := huniq K hK
        exact Function.update_self _ _ _
    have hxp : layerMul G y ^ p ∈ f.range.comap (QuotientGroup.mk' N) := by
      rw [mem_comap, map_pow, hg]
      exact one_mem _
    have hup : layerMul G (Function.update y L₀ 1) ^ p ∈
        f.range.comap (QuotientGroup.mk' N) := by
      have h : layerMul G (Function.update y L₀ 1) ^ p =
          ((y L₀ : G) ^ p)⁻¹ * layerMul G y ^ p := by
        rw [hdecomp, hu.mul_pow, inv_mul_cancel_left]
      rw [h]
      exact mul_mem (inv_mem (hL₀M _ (pow_mem (y L₀).2 p))) hxp
    have hcop : p.Coprime (orderOf (layerMul G (Function.update y L₀ 1))) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hun)
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    have hu' : layerMul G (Function.update y L₀ 1) ∈ f.range.comap (QuotientGroup.mk' N) := by
      rw [← hm]
      exact pow_mem hup m
    have hy : layerMul G y ∈ f.range.comap (QuotientGroup.mk' N) := by
      rw [hdecomp]
      exact mul_mem (hL₀M _ (y L₀).2) hu'
    exact hy
  obtain ⟨E, -, hEa, hEcard⟩ := exists_pRank hp1 (⊤ : Subgroup (G ⧸ N))
  have hker : f.ker ≤ center L₀.1 := fun l hl => by
    have hlN : (l : G) ∈ N := (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hl)
    exact mem_center_iff.mpr fun k => Subtype.ext (mem_center_iff.mp (hN hlN) k)
  have h2 := (isStronglyQuasithin_iff.mp (hquot L₀.1 L₀.2 f.ker hker)) p hp hp2
  calc Open.pRank p (⊤ : Subgroup (G ⧸ N)) ≤ Open.pRank p f.range :=
        le_pRank hp1 (fun g hg => hT g (hEa.2 g hg)) hEa hEcard
    _ = Open.pRank p (⊤ : Subgroup f.range) := pRank_eq_pRank_top_subgroup _
    _ = Open.pRank p (⊤ : Subgroup (L₀.1 ⧸ f.ker)) :=
        (pRank_top_eq_of_mulEquiv hp1 (QuotientGroup.quotientKerEquivRange f)).symm
    _ ≤ 2 := h2

end CFSG.SectionRank
