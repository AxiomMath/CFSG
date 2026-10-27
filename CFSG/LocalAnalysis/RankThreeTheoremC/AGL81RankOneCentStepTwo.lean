module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentTenFourteen
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentStepZero
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentSylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

section Generic

variable {p : ℕ} [Fact p.Prime] {C : Subgroup G}
  {K : Subgroup (C ⧸ primeComplementCore (G := C) p)}

theorem eq_one_of_mem_inf (hZ : Subgroup.center ↥K = ⊥) {x : G} (hxK : x ∈ hyp111Pre p C K)
    (hxX : x ∈ d1PlusCore p C K) {n : ℕ} (hxp : x ^ (p ^ n) = 1) : x = 1 := by
  obtain ⟨x', hx'K, rfl⟩ := hxK
  obtain ⟨x'', hx''C, hx''⟩ := hxX
  have hx : x'' = x' := Subtype.ext hx''
  subst hx
  set k : K := ⟨QuotientGroup.mk' (primeComplementCore (G := C) p) x'', hx'K⟩
  have hk : k ∈ Subgroup.center ↥K := by
    refine Subgroup.mem_center_iff.mpr fun k' => ?_
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx''C k'.1 k'.2)
  rw [hZ] at hk
  have hcore : x'' ∈ primeComplementCore (G := C) p := by
    have : QuotientGroup.mk' (primeComplementCore (G := C) p) x'' = 1 :=
      congrArg Subtype.val (Subgroup.mem_bot.mp hk)
    exact (QuotientGroup.eq_one_iff x'').mp this
  have hxp' : x'' ^ (p ^ n) = 1 := Subtype.ext (by simpa using hxp)
  rw [eq_one_of_mem_core hcore hxp']
  rfl

theorem not_mem_hyp111Pre (hZ : Subgroup.center ↥K = ⊥) {b : G} (hbX : b ∈ d1PlusCore p C K)
    (hbo : orderOf b = p) : b ∉ hyp111Pre p C K := by
  intro hbK
  have hb1 := eq_one_of_mem_inf hZ hbK hbX (n := 1) (by rw [pow_one, ← hbo, pow_orderOf_eq_one])
  rw [hb1, orderOf_one] at hbo
  exact (Fact.out : p.Prime).one_lt.ne hbo

theorem le_normalizer_hyp111Pre (hK : K.Normal) :
    C ≤ Subgroup.normalizer (hyp111Pre p C K : Set G) := by
  have hN : (K.comap (QuotientGroup.mk' (primeComplementCore (G := C) p))).Normal := hK.comap _
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp ?_
  have e : (hyp111Pre p C K).subgroupOf C =
      K.comap (QuotientGroup.mk' (primeComplementCore (G := C) p)) :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  change ((hyp111Pre p C K).subgroupOf C).Normal
  rw [e]
  exact hN

theorem commute_of_mem_inf (hK : K.Normal) (hZ : Subgroup.center ↥K = ⊥) {B : Subgroup G}
    (hBC : B ≤ C) (hB : IsPGroup p B) {u v : G} (huB : u ∈ B) (hvB : v ∈ B)
    (huK : u ∈ hyp111Pre p C K) (hvX : v ∈ d1PlusCore p C K) : u * v = v * u := by
  have hKn := le_normalizer_hyp111Pre hK
  have hXn := le_normalizer_d1PlusCore hK
  have hcK : u * v * u⁻¹ * v⁻¹ ∈ hyp111Pre p C K := by
    have h := (Subgroup.mem_normalizer_iff.mp (hKn (hBC hvB)) u⁻¹).mp
      ((hyp111Pre p C K).inv_mem huK)
    have := (hyp111Pre p C K).mul_mem huK h
    simpa [mul_assoc] using this
  have hcX : u * v * u⁻¹ * v⁻¹ ∈ d1PlusCore p C K := by
    have h := (Subgroup.mem_normalizer_iff.mp (hXn (hBC huB)) v).mp hvX
    have := (d1PlusCore p C K).mul_mem h ((d1PlusCore p C K).inv_mem hvX)
    simpa [mul_assoc] using this
  have hcB : u * v * u⁻¹ * v⁻¹ ∈ B :=
    B.mul_mem (B.mul_mem (B.mul_mem huB hvB) (B.inv_mem huB)) (B.inv_mem hvB)
  obtain ⟨n, hn⟩ := hB ⟨_, hcB⟩
  have hn' : (u * v * u⁻¹ * v⁻¹) ^ (p ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have h1 := eq_one_of_mem_inf hZ hcK hcX hn'
  calc u * v = (u * v * u⁻¹ * v⁻¹) * (v * u) := by group
    _ = v * u := by rw [h1, one_mul]

theorem pRank_add_one_le (hZ : Subgroup.center ↥K = ⊥) {b : G} (hbC : b ∈ C)
    (hb : ∀ c ∈ C, b * c = c * b) (hbo : orderOf b = p) :
    Open.pRank p (⊤ : Subgroup ↥K) + 1 ≤ Open.pRank p C := by
  have hp : p.Prime := Fact.out
  have hbX : b ∈ d1PlusCore p C K := mem_d1PlusCore_of_central hbC hb K
  have hbK := not_mem_hyp111Pre hZ hbX hbo
  have hKC : hyp111Pre p C K ≤ C := Subgroup.map_subtype_le _
  have h := CFSG.LocalAnalysis.RankThreeTheoremC.pRank_inf_succ_le_of_central hp hbC hbo hbK
    (Subgroup.mem_centralizer_iff.mpr fun k hk => (hb k (hKC hk)).symm)
  rw [inf_eq_right.mpr hKC] at h
  have hcop : p.Coprime (Nat.card (primeComplementCore (G := C) p)) :=
    primeComplementCore_coprime (G := C) p
  have hmap := pRank_map_mk_eq_pRank_map_subtype hp (primeComplementCore (G := C) p) hcop
    (K.comap (QuotientGroup.mk' (primeComplementCore (G := C) p)))
  rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hmap
  have htop := CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) K
  change Open.pRank p K = Open.pRank p (hyp111Pre p C K) at hmap
  omega

end Generic

theorem stepThreeGroup_kbar
    {p : ℕ} (hp : p = 3 ∨ p = 5) {M : Subgroup G} {b : G} (hbo : orderOf b = p)
    (hT : TenFourteenCentAt p M (Subgroup.centralizer ({b} : Set G)))
    (hne : d1KBar p M (Subgroup.centralizer ({b} : Set G)) ≠ ⊥)
    (hC3 : Open.pRank p (Subgroup.centralizer ({b} : Set G)) ≤ 3) :
    StepThreeGroup p ↥(d1KBar p M (Subgroup.centralizer ({b} : Set G))) := by
  haveI : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> norm_num⟩
  have hbC : b ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hb : ∀ c ∈ Subgroup.centralizer ({b} : Set G), b * c = c * b := fun c hc =>
    (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
  have h := pRank_add_one_le (hT.center hne) hbC hb hbo
  exact stepThreeGroup_of_tenFourteenOne hp (hT.list hne) (by omega)

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
