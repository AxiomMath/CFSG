module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem isCyclic_of_le_centralizer {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {R L Q E : Subgroup G}
    (hZ : ∀ l ∈ L, (∀ h ∈ L, h * l = l * h) → l = 1) (hR3 : CFSG.Open.pRank p R ≤ 3)
    (hQR : Q ≤ R) (hQL : Q ≤ centralizer (L : Set G)) (hQp : IsPGroup p Q) (hEL : E ≤ L)
    (hER : E ≤ R) (hE : IsElemAbelian p E) {k : ℕ} (hk : 2 ≤ k) (hEc : Nat.card E = p ^ k) :
    IsCyclic Q := by
  have hprime : p.Prime := Fact.out
  by_contra hnc
  obtain ⟨B, hB, hBc⟩ := CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two
    (hprime.odd_of_ne_two hp2) hQp hnc
  have hB' : IsElemAbelian p (B.map Q.subtype) := elementary_map_injective p B Q.subtype
    Q.subtype_injective ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p B).1 hB)
  have hBc' : Nat.card (B.map Q.subtype) = p ^ 2 := by
    rw [card_map_of_injective Q.subtype_injective, hBc]
  have hBQ : B.map Q.subtype ≤ Q := map_subtype_le B
  have := add_le_pRank_of_commute (P := R) hB' hE hBc' hEc
    (fun a ha b hb => (mem_centralizer_iff.mp (hQL (hBQ ha)) b (hEL hb)).symm)
    (Subgroup.disjoint_def.mpr fun {y} hyB hyE =>
      hZ y (hEL hyE) fun h hh => mem_centralizer_iff.mp (hQL (hBQ hyB)) h hh)
    (hBQ.trans hQR) hER
  omega

theorem exists_eq_mul_inf_of_isSylowOf_mulEquiv_psl {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {P C L : Subgroup G} (hsyl : CFSG.ABGLocalTools.IsSylowOf p P C) (hLC : L ≤ C)
    (hCL : C ≤ normalizer (L : Set G)) (e : L ≃* PSL(2, GaloisField p 2)) :
    ∀ g ∈ P, ∃ a ∈ P ⊓ L, ∃ k ∈ P ⊓ centralizer (L : Set G), g = a * k := by
  have hprime : p.Prime := Fact.out
  have hPp : IsPGroup p P := hsyl.isPGroup
  have hKcard : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
  have hAsyl : CFSG.ABGLocalTools.IsSylowOf p (P ⊓ L) L := hsyl.inf_of_le_normalizer hLC hCL
  have hZ : ∀ l ∈ L, (∀ h ∈ L, h * l = l * h) → l = 1 := fun l hl hc =>
    eq_one_of_commute_of_mulEquiv_psl_two e hl hc
  have hPN : P ≤ normalizer (L : Set G) := hsyl.le.trans hCL
  let φ : P →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hPN)
  let H : Subgroup G := ((φ.range).comap (MulAut.conj : L →* MulAut L)).map L.subtype
  have hHL : H ≤ L := map_subtype_le _
  have hHiff : ∀ (l : G) (hl : l ∈ L),
      l ∈ H ↔ ∃ g ∈ P, ∀ h ∈ L, g * h * g⁻¹ = l * h * l⁻¹ := by
    intro l hl
    constructor
    · rintro ⟨l', ⟨g, hg⟩, rfl⟩
      refine ⟨g, g.2, fun h hh => ?_⟩
      have := congrArg (fun f : MulAut L => ((f ⟨h, hh⟩ : L) : G)) hg
      simpa [φ] using this
    · rintro ⟨g, hg, hgl⟩
      refine ⟨⟨l, hl⟩, ⟨⟨g, hg⟩, ?_⟩, rfl⟩
      ext h
      exact hgl h h.2
  have hAH : P ⊓ L ≤ H := fun a ha => (hHiff a ha.2).2 ⟨a, ha.1, fun h hh => rfl⟩
  have hHp : IsPGroup p H := by
    rintro ⟨y, l', ⟨g', hg'⟩, rfl⟩
    obtain ⟨k, hk⟩ := hPp g'
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (MulAut.conj (l' ^ (p ^ k)) : MulAut L) = 1 := by
      rw [map_pow, ← hg', ← map_pow, hk, map_one]
    apply hZ _ (l' ^ (p ^ k)).2
    intro h hh
    have := congrArg (fun f : MulAut L => ((f ⟨h, hh⟩ : L) : G)) h1
    simp only [MulAut.conj_apply, MulAut.one_apply, Subgroup.coe_mul, InvMemClass.coe_inv] at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  have hHA : H = P ⊓ L := hAsyl.eq_of_le hAH hHL hHp
  intro g hg
  obtain ⟨j, hj⟩ := hPp ⟨g, hg⟩
  obtain ⟨l, hl, hconj⟩ := exists_mem_conj_eq_of_pow_eq_one hprime hp5 hKcard e (hPN hg)
    (congrArg Subtype.val hj : g ^ (p ^ j) = 1)
  have hlA : l ∈ P ⊓ L := hHA ▸ (hHiff l hl).2 ⟨g, hg, hconj⟩
  refine ⟨l, hlA, l⁻¹ * g, ⟨P.mul_mem (P.inv_mem hlA.1) hg, mem_centralizer_iff.mpr
    fun h hh => ?_⟩, by group⟩
  have := hconj h hh
  calc h * (l⁻¹ * g) = l⁻¹ * (l * h * l⁻¹) * g := by group
    _ = l⁻¹ * (g * h * g⁻¹) * g := by rw [this]
    _ = l⁻¹ * g * h := by group

theorem isMulCommutative_of_isSylowOf_mulEquiv_psl {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {P C L : Subgroup G} {x : G} (hsyl : CFSG.ABGLocalTools.IsSylowOf p P C) (hLC : L ≤ C)
    (hCL : C ≤ normalizer (L : Set G)) (hxP : x ∈ P) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hxC : ∀ c ∈ C, c * x = x * c) (hP3 : CFSG.Open.pRank p P ≤ 3) {m : ℕ} (hm : 2 ≤ m)
    (e : L ≃* PSL(2, GaloisField p m)) : IsMulCommutative P := by
  obtain ⟨rfl, hrank2⟩ := eq_two_of_isSylowOf_mulEquiv_psl hsyl hLC hCL hxP hx1 hxp hxC hP3 hm e
  have hKcard : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
  have hZ : ∀ l ∈ L, (∀ h ∈ L, h * l = l * h) → l = 1 := fun l hl hc =>
    eq_one_of_commute_of_mulEquiv_psl_two e hl hc
  have hPp : IsPGroup p P := hsyl.isPGroup
  have hAcomm : IsMulCommutative (P ⊓ L : Subgroup G) :=
    isMulCommutative_of_isPGroup_of_mulEquiv_psl_two hKcard e inf_le_right hPp.to_inf_left
  obtain ⟨E, hEA, hE, hEc⟩ := pRank_attained p (P ⊓ L) (by omega)
  rw [hrank2] at hEc
  have hKcyc : IsCyclic ↥(P ⊓ centralizer (L : Set G)) :=
    isCyclic_of_le_centralizer (by omega) hZ hP3 inf_le_left inf_le_right hPp.to_inf_left
      (hEA.trans inf_le_right) (hEA.trans inf_le_left) hE le_rfl hEc
  have hKcomm : IsMulCommutative (P ⊓ centralizer (L : Set G) : Subgroup G) := inferInstance
  have hdec := exists_eq_mul_inf_of_isSylowOf_mulEquiv_psl hp5 hsyl hLC hCL e
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨a₁, ha₁, k₁, hk₁, h₁⟩ := hdec a a.2
  obtain ⟨a₂, ha₂, k₂, hk₂, h₂⟩ := hdec b b.2
  have hkk : k₁ * k₂ = k₂ * k₁ :=
    congrArg Subtype.val (hKcomm.is_comm.comm (⟨k₁, hk₁⟩ : ↥(P ⊓ centralizer (L : Set G)))
      ⟨k₂, hk₂⟩)
  have haa : a₁ * a₂ = a₂ * a₁ :=
    congrArg Subtype.val (hAcomm.is_comm.comm (⟨a₁, ha₁⟩ : ↥(P ⊓ L)) ⟨a₂, ha₂⟩)
  have c1 : k₁ * a₂ = a₂ * k₁ := (mem_centralizer_iff.mp hk₁.2 a₂ ha₂.2).symm
  have c2 : k₂ * a₁ = a₁ * k₂ := (mem_centralizer_iff.mp hk₂.2 a₁ ha₁.2).symm
  apply Subtype.ext
  show (a : G) * b = b * a
  rw [h₁, h₂]
  calc a₁ * k₁ * (a₂ * k₂) = a₁ * (k₁ * a₂) * k₂ := by group
    _ = a₁ * (a₂ * k₁) * k₂ := by rw [c1]
    _ = a₁ * a₂ * (k₁ * k₂) := by group
    _ = a₂ * a₁ * (k₂ * k₁) := by rw [haa, hkk]
    _ = a₂ * (a₁ * k₂) * k₁ := by group
    _ = a₂ * (k₂ * a₁) * k₁ := by rw [c2]
    _ = a₂ * k₂ * (a₁ * k₁) := by group

end CFSG.LocalAnalysis.RankThreeTheoremC
