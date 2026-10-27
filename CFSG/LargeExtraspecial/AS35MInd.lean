module

public import CFSG.LargeExtraspecial.AS35MQuotSet
public import CFSG.LargeExtraspecial.AS35DSixOne

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CQuotE

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

section Ind

variable {E : Set G} {x : G} (hE : S.DescentSet E x) (hx3 : orderOf x = 3)
  (hfix : fixSpace (S.rhoL hE.x_mem_M) ≠ ⊥) (hcent : S.QuotCentHypE E)
  (hO2 : S.QuotOTwoHypE E)

theorem quotE_weak (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    (g₁ : GQ E) (hg : g₁ * (S.quotE hE hx3 hfix hcent hO2).z * g₁⁻¹ ∈
      (S.quotE hE hx3 hfix hcent hO2).QG) :
    g₁ * (S.quotE hE hx3 hfix hcent hO2).z * g₁⁻¹ = (S.quotE hE hx3 hfix hcent hO2).z := by
  rw [quotE_QG, quotE_z] at hg
  rw [quotE_z]
  obtain ⟨c, rfl⟩ := mkQ_surjective E g₁
  obtain ⟨d, hdQ, hd⟩ := (S.mem_QQE).mp hg
  have hconj : mkQ E c * S.zQuotE hE * (mkQ E c)⁻¹ = mkQ E (c * S.zCxE hE * c⁻¹) := by
    rw [zQuotE, map_mul, map_mul, map_inv]
  rw [hconj] at hd ⊢
  have hcz2 : (c * S.zCxE hE * c⁻¹) ^ (2 ^ 2) = 1 := by
    rw [conj_pow, show (2 : ℕ) ^ 2 = 2 * 2 from rfl, pow_mul, S.zCxE_sq, one_pow, mul_one,
      mul_inv_cancel]
  have h1 := eq_of_mkQ_eq (S.pow_four_of_coe_mem_QG_E hdQ) hcz2 hd
  have h2 : (c : G) * S.z * (c : G)⁻¹ ∈ S.QG := by
    have := congrArg (fun w : Cx E => (w : G)) h1
    simp only [coe_mul, coe_inv] at this
    rw [show (c : G) * S.z * (c : G)⁻¹ = ((c : G) * ((S.zCxE hE : Cx E) : G) * (c : G)⁻¹) from
      rfl, ← this]
    exact hdQ
  have h3 := hW c h2
  rw [zQuotE]
  congr 1
  exact Subtype.ext (by simpa [zCxE] using h3)

theorem quotE_zInOTwo (hO : ∀ t ∈ S.QG, orderOf t = 2 → S.ZInOTwo t)
    (t₁ : GQ E) (ht : t₁ ∈ (S.quotE hE hx3 hfix hcent hO2).QG) (ht2 : orderOf t₁ = 2) :
    (S.quotE hE hx3 hfix hcent hO2).ZInOTwo t₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [quotE_QG] at ht
  obtain ⟨d, hdQ, rfl⟩ := (S.mem_QQE).mp ht
  have hd2 : d ^ 2 = 1 := by
    have h1 : mkQ E (d ^ 2) = mkQ E 1 := by
      rw [map_pow, map_one, ← ht2, pow_orderOf_eq_one]
    refine eq_of_mkQ_eq (m := 1) ?_ (by rw [one_pow]) h1
    rw [pow_one, ← pow_mul]
    exact S.pow_four_of_coe_mem_QG_E hdQ
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hdo : orderOf (d : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hd2 hd1
  have hzd := hO d hdQ hdo
  set P : Subgroup (GQ E) := ((oTwoCent (d : G)).comap (Cx E).subtype).map (mkQ E) with hP
  refine (S.quotE hE hx3 hfix hcent hO2).zInOTwo_of_le (P := P) ?_ ?_ ?_ ?_
  · rintro _ ⟨c, hc, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (oTwoCent_le_centralizer _ hc))
  · intro g₁ hg₁ p hp
    obtain ⟨c', rfl⟩ := mkQ_surjective E g₁
    obtain ⟨c, hc, rfl⟩ := hp
    rw [mem_centralizer_singleton_iff] at hg₁
    have h1 := commute_of_mkQ_commute (m := 1) (by rw [pow_one]; exact hd2) hg₁
    have h2 : (c' : G) ∈ centralizer ({(d : G)} : Set G) :=
      mem_centralizer_singleton_iff.mpr (congrArg (fun w : Cx E => (w : G)) h1)
    refine ⟨c' * c * c'⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    change ((c' * c * c'⁻¹ : Cx E) : G) ∈ oTwoCent (d : G)
    rw [coe_mul, coe_mul, coe_inv]
    exact conj_mem_oTwoCent h2 hc
  · exact ((isPGroup_oTwoCent (d : G)).comap_of_injective (Cx E).subtype
      (Cx E).subtype_injective).map _
  · exact ⟨S.zCxE hE, hzd, rfl⟩

theorem quotE_not_mem_center (hnc : ∃ c ∈ centralizer E, c ∉ S.M) :
    (S.quotE hE hx3 hfix hcent hO2).z ∉ center (GQ E) := by
  obtain ⟨c, hcE, hcM⟩ := hnc
  intro hz
  rw [quotE_z] at hz
  apply hcM
  refine (S.mkQ_mem_MQE_iff hE ⟨c, hcE⟩).mp ?_
  rw [mem_centralizer_singleton_iff]
  exact (mem_center_iff.mp hz (mkQ E ⟨c, hcE⟩))

theorem quotE_aschTwo (ih : S14.AschbacherBelow (Nat.card G))
    (hw : 2 ≤ (S.quotE hE hx3 hfix hcent hO2).width)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    (hO : ∀ t ∈ S.QG, orderOf t = 2 → S.ZInOTwo t)
    (hnc : ∃ c ∈ centralizer E, c ∉ S.M) :
    (S.quotE hE hx3 hfix hcent hO2).AschTwo := by
  rcases ih (GQ E) (card_GQ_lt hE.mem hE.x_mem hx3) (S.quotE hE hx3 hfix hcent hO2) hw with
    h1 | h2 | ⟨t, htQ, ht2, ht⟩ | ⟨g, hgQ, hgne⟩
  · exact absurd h1 (S.quotE_not_mem_center hE hx3 hfix hcent hO2 hnc)
  · exact h2
  · exact absurd (S.quotE_zInOTwo hE hx3 hfix hcent hO2 hO t htQ ht2) ht
  · exact absurd (S.quotE_weak hE hx3 hfix hcent hO2 hW g hgQ) hgne

end Ind

section Gen

variable {E : Set G} {x : G} (hE : S.DescentSet E x) (hx3 : orderOf x = 3)
  (hfix : fixSpace (S.rhoL hE.x_mem_M) ≠ ⊥) (hcent : S.QuotCentHypE E)
  (hO2 : S.QuotOTwoHypE E)

omit [Finite G] in
@[expose] def XCxE : Subgroup (Cx E) :=
  closure {w | ∃ c : Cx E, c * S.zCxE hE * c⁻¹ = w}

theorem map_XCxE : (S.XCxE hE).map (mkQ E) = (S.quotE hE hx3 hfix hcent hO2).zGen := by
  rw [XCxE, MonoidHom.map_closure, zGen, quotE_z]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    refine isConj_iff.mpr ⟨mkQ E c, ?_⟩
    rw [zQuotE, map_mul, map_mul, map_inv]
  · intro hg
    obtain ⟨a, rfl⟩ := isConj_iff.mp hg
    obtain ⟨c, rfl⟩ := mkQ_surjective E a
    exact ⟨c * S.zCxE hE * c⁻¹, ⟨c, rfl⟩, by rw [zQuotE, map_mul, map_mul, map_inv]⟩

theorem eq_bot_of_normal_two_XCxE (hA2 : (S.quotE hE hx3 hfix hcent hO2).AschTwo)
    {N : Subgroup (Cx E)} (hNX : N ≤ S.XCxE hE)
    (hNn : ∀ a ∈ S.XCxE hE, ∀ n ∈ N, a * n * a⁻¹ ∈ N) (hN2 : IsPGroup 2 N) : N = ⊥ := by
  set T := S.quotE hE hx3 hfix hcent hO2 with hT
  have hmap := S.map_XCxE hE hx3 hfix hcent hO2
  have hNL : N.map (mkQ E) ≤ T.zGen := hmap ▸ map_mono hNX
  have := hA2.1
  have hKn : ((N.map (mkQ E)).subgroupOf T.zGen).Normal := ⟨fun k hk l => by
    rw [mem_subgroupOf] at hk ⊢
    obtain ⟨n, hn, hnk⟩ := hk
    obtain ⟨a, ha, hal⟩ : (l : GQ E) ∈ (S.XCxE hE).map (mkQ E) := by rw [hmap]; exact l.2
    refine ⟨a * n * a⁻¹, hNn a ha n hn, ?_⟩
    simp only [coe_mul, coe_inv, map_mul, map_inv, hal, hnk]⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.map (mkQ E)).subgroupOf T.zGen) with h | h
  · rw [eq_bot_iff]
    intro n hn
    have h1 : mkQ E n = 1 := by
      have h2 : (⟨mkQ E n, hNL ⟨n, hn, rfl⟩⟩ : T.zGen) ∈
          (N.map (mkQ E)).subgroupOf T.zGen := by
        rw [mem_subgroupOf]
        exact ⟨n, hn, rfl⟩
      rw [h, mem_bot] at h2
      exact congrArg Subtype.val h2
    obtain ⟨k, hk⟩ := hN2 ⟨n, hn⟩
    have hk' : n ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    rw [← map_one (mkQ E)] at h1
    exact (mem_bot).mpr (eq_of_mkQ_eq hk' (by rw [one_pow]) h1)
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hL2 : IsPGroup 2 T.zGen := by
      intro l
      have hl : l ∈ (N.map (mkQ E)).subgroupOf T.zGen := by rw [h]; exact mem_top l
      rw [mem_subgroupOf] at hl
      obtain ⟨k, hk⟩ := ((hN2.map (mkQ E)) ⟨l, hl⟩)
      have hk' := congrArg Subtype.val hk
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hk'
      exact ⟨k, Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hk')⟩
    have hsolv : Group.IsSolvable T.zGen := by
      have := hL2.isNilpotent
      infer_instance
    have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr hsolv
    have hz : T.z ∈ centralizer (T.zGen : Set (GQ E)) := by
      rw [mem_centralizer_iff]
      intro l hl
      exact congrArg Subtype.val (hcomm ⟨l, hl⟩ ⟨T.z, T.z_mem_zGen⟩)
    rw [hA2.2.1, mem_bot] at hz
    exact T.z_ne_one hz

end Gen

end Setting

end CFSG.LargeExtraspecial
