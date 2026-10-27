module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.NormalRankTwo

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

omit [Finite G] in
theorem isElemAbelian_sup_zpowers_of_mem_centralizer {V : Subgroup G} (hV : IsElemAbelian p V)
    {x : G} (hxV : x ∈ Subgroup.centralizer (V : Set G)) (hxp : x ^ p = 1) :
    IsElemAbelian p (V ⊔ Subgroup.zpowers x) := by
  have hXV : Subgroup.zpowers x ≤ Subgroup.centralizer (V : Set G) := Subgroup.zpowers_le.mpr hxV
  have hVX : V ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
    Subgroup.le_centralizer_iff.mp hXV
  have hVV : V ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hV.1
  have hXX : Subgroup.zpowers x ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  refine ⟨Subgroup.le_centralizer_iff_isMulCommutative.mp
    (sup_le (Subgroup.le_centralizer_iff.mp (sup_le hVV hXV))
      (Subgroup.le_centralizer_iff.mp (sup_le hVX hXX))), fun y hy => ?_⟩
  have hy' : y ∈ (V : Set G) * (Subgroup.zpowers x : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right V _
      (hVX.trans (Subgroup.centralizer_le_normalizer _))]
    exact hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hcomm : Commute a (x ^ k) := (Subgroup.mem_centralizer_iff.mp (hVX ha) _ hb).symm
  rw [hcomm.mul_pow, hV.2 a ha, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hxp, one_zpow]

theorem mem_of_pow_eq_one_of_mem_inf_centralizer (hp : p.Prime) {P V : Subgroup G}
    (hV : IsElemAbelian p V) (hVcard : Nat.card V = p ^ 2) (hVP : V ≤ P)
    (hC : Open.pRank p (P ⊓ Subgroup.centralizer (V : Set G)) ≤ 2) {x : G}
    (hx : x ∈ P ⊓ Subgroup.centralizer (V : Set G)) (hxp : x ^ p = 1) : x ∈ V := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hxV
  have hE := isElemAbelian_sup_zpowers_of_mem_centralizer hV hx.2 hxp
  have hEle : V ⊔ Subgroup.zpowers x ≤ P ⊓ Subgroup.centralizer (V : Set G) :=
    sup_le (le_inf hVP (Subgroup.le_centralizer_iff_isMulCommutative.mpr hV.1))
      (Subgroup.zpowers_le.mpr hx)
  have hlt : V < V ⊔ Subgroup.zpowers x := lt_of_le_of_ne le_sup_left fun h =>
    hxV (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (fun y : (V ⊔ Subgroup.zpowers x : Subgroup G) =>
    ⟨1, Subtype.ext (by simpa using hE.2 y y.2)⟩)
  have hcard := Subgroup.card_lt_of_lt hlt
  rw [hVcard, hn, pow_lt_pow_iff_right₀ hp.one_lt] at hcard
  have hrank : n ≤ Open.pRank p (P ⊓ Subgroup.centralizer (V : Set G)) :=
    le_csSup (pRank_bddAbove p hp _) ⟨_, hEle, hE, hn⟩
  omega

theorem mem_of_mem_center_of_pRank_centralizer_le_two (hp : p.Prime) {P V : Subgroup G}
    (hV : IsElemAbelian p V) (hVcard : Nat.card V = p ^ 2) (hVP : V ≤ P)
    (hC : Open.pRank p (P ⊓ Subgroup.centralizer (V : Set G)) ≤ 2)
    {z : G} (hz : z ∈ P) (hzc : z ∈ Subgroup.centralizer (P : Set G)) (hzp : orderOf z = p) :
    z ∈ V :=
  mem_of_pow_eq_one_of_mem_inf_centralizer hp hV hVcard hVP hC
    ⟨hz, Subgroup.centralizer_le hVP hzc⟩ (hzp ▸ pow_orderOf_eq_one z)

theorem isCyclic_center_of_pRank_centralizer_le_two (hp : p.Prime) (hodd : p ≠ 2)
    {P V : Subgroup G} (hP : IsPGroup p P) (hrank : 3 ≤ Open.pRank p P)
    (hV : IsElemAbelian p V) (hVcard : Nat.card V = p ^ 2) (hVP : V ≤ P)
    (hC : Open.pRank p (P ⊓ Subgroup.centralizer (V : Set G)) ≤ 2) :
    IsCyclic (Subgroup.center P) := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hcyc
  obtain ⟨W, -, hW, hWcard⟩ := odd_pGroup_noncyclic_has_normal_elementary_rank_two p hodd _ rfl
    (hP.to_subgroup (Subgroup.center P)) hcyc
  have hWV : (W.map (Subgroup.center P).subtype).map P.subtype ≤ V := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine mem_of_pow_eq_one_of_mem_inf_centralizer hp hV hVcard hVP hC
      ⟨(w : P).2, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩ ?_
    · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2 ⟨v, hVP hv⟩)
    · simpa using congrArg (fun y : Subgroup.center P => ((y : P) : G)) (hW.2 w hw)
  have hWeq := Subgroup.eq_of_le_of_card_ge hWV (by
    rw [hVcard, Subgroup.card_map_of_injective P.subtype_injective,
      Subgroup.card_map_of_injective (Subgroup.center P).subtype_injective, hWcard])
  have hPC : P ≤ P ⊓ Subgroup.centralizer (V : Set G) := by
    refine le_inf le_rfl fun g hg => Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    rw [← hWeq] at hv
    obtain ⟨_, ⟨w, -, rfl⟩, rfl⟩ := hv
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2 ⟨g, hg⟩)).symm
  have := pRank_mono p hp hPC
  omega

end CFSG.AGLEmbedding
