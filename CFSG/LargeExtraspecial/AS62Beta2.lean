module

public import CFSG.LargeExtraspecial.AS62Beta1
public import CFSG.LargeExtraspecial.AS62O4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Asc77 CFSG.RankThree.OrthogonalInvolutions

namespace AS62

variable {G : Type} [Group G]

omit [Group G] in
private theorem ncard_le_four (a b c d : G) : ({a, b, c, d} : Set G).ncard ≤ 4 := by
  have h1 := Set.ncard_insert_le a ({b, c, d} : Set G)
  have h2 := Set.ncard_insert_le b ({c, d} : Set G)
  have h3 := Set.ncard_insert_le c ({d} : Set G)
  rw [Set.ncard_singleton] at h3
  omega

private theorem mul_comm_iff_commutator_eq_one {a b : G} :
    a * b = b * a ↔ a * b * a⁻¹ * b⁻¹ = 1 := by
  constructor
  · intro h
    rw [h]
    group
  · intro h
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h, one_mul]

private theorem conj_eq_of_commutator_eq {a b v : G} (h : a * b * a⁻¹ * b⁻¹ = v) :
    a * b * a⁻¹ = v * b := by
  rw [← h]
  group

theorem card_le_four_of_le_sup {H K : Subgroup G} {a v : G} (haa : a * a = 1)
    (ha : ∀ k ∈ K, a * k * a⁻¹ ∈ K) (hHK : H ≤ K ⊔ zpowers a)
    (hHv : ∀ y ∈ H, y ∈ K → y = 1 ∨ y = v) : Nat.card H ≤ 4 := by
  have hcard : Nat.card H = (H : Set G).ncard := Nat.card_coe_set_eq (H : Set G)
  by_cases hsub : ∀ y ∈ H, y ∈ K
  · have h' : (H : Set G) ⊆ {1, v, 1, v} := by
      intro y hy
      rcases hHv y hy (hsub y hy) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    rw [hcard]
    exact (Set.ncard_le_ncard h' (Set.toFinite _)).trans (ncard_le_four _ _ _ _)
  · push Not at hsub
    obtain ⟨y₀, hy₀H, hy₀K⟩ := hsub
    have hy₀a : y₀ * a ∈ K :=
      ((S8.mem_sup_zpowers_iff haa ha).mp (hHK hy₀H)).resolve_left hy₀K
    have h' : (H : Set G) ⊆ {1, v, y₀, y₀ * v} := by
      intro y hy
      by_cases hyK : y ∈ K
      · rcases hHv y hy hyK with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · have hya : y * a ∈ K := ((S8.mem_sup_zpowers_iff haa ha).mp (hHK hy)).resolve_left hyK
        have hk : y₀⁻¹ * y ∈ K := by
          have := ha _ (mul_mem (inv_mem hy₀a) hya)
          rwa [show a * ((y₀ * a)⁻¹ * (y * a)) * a⁻¹ = y₀⁻¹ * y by group] at this
        have hy' : y = y₀ * (y₀⁻¹ * y) := by group
        rcases hHv _ (mul_mem (inv_mem hy₀H) hy) hk with h | h
        · rw [h, mul_one] at hy'
          exact Or.inr (Or.inr (Or.inl hy'))
        · rw [h] at hy'
          exact Or.inr (Or.inr (Or.inr hy'))
    rw [hcard]
    exact (Set.ncard_le_ncard h' (Set.toFinite _)).trans (ncard_le_four _ _ _ _)

end AS62

namespace Setting

variable {G : Type} [Group G] [Finite G]

namespace SixThreeCtx

variable {S : Setting G} (c : SixThreeCtx S)

theorem mem_four_of_commute (hw : S.width = 2) (hS : IsSThreeAt S.z c.N) {m : G}
    (hmz : m * S.z = S.z * m) (hmu : m * c.u = c.u * m) {r₀ : G} (hr₀ : r₀ ∈ c.Rt)
    (hmr₀ : m * r₀ ≠ r₀ * m) {r : G} (hr : r ∈ c.Rt) (hmr : m * r = r * m) :
    r = 1 ∨ r = S.z ∨ r = c.u ∨ r = c.u * S.z := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  by_contra! hne
  obtain ⟨hr1, hrz, hru, hruz⟩ := hne
  apply hmr₀
  set σ := S.rhoL (c.t_mem_M_of_sThree hS) with hσ
  have hU2 : finrank (ZMod 2) (commSpace σ) = 2 := (c.sThree_typeA hS).1
  have huR := c.u_mem_Rt
  rw [c.Rt_eq_clPre hw hS] at hr₀ hr huR
  obtain ⟨hr₀Q, hr₀U⟩ := S.mem_clPre.mp hr₀
  obtain ⟨hrQ, hrU⟩ := S.mem_clPre.mp hr
  obtain ⟨-, huU⟩ := S.mem_clPre.mp huR
  have ha0 : S.cl c.u ≠ 0 := by
    rw [ne_eq, S.cl_eq_zero_iff c.huQ]
    rintro (h | h)
    · exact c.hu1 h
    · exact c.huz h
  have hb0 : S.cl r ≠ 0 := by
    rw [ne_eq, S.cl_eq_zero_iff hrQ]
    rintro (h | h)
    · exact hr1 h
    · exact hrz h
  have hab : S.cl c.u ≠ S.cl r := by
    rw [ne_eq, S.cl_eq_cl_iff c.huQ hrQ]
    rintro (h | h)
    · exact hru h
    · exact hruz h
  have e1 : S.cl c.u + S.cl r ≠ 0 := fun h => hab (by
    rw [add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self] at h
    exact h)
  have e2 : S.cl c.u + S.cl r ≠ S.cl c.u := fun h => hb0 (by simpa using h)
  have e3 : S.cl c.u + S.cl r ≠ S.cl r := fun h => ha0 (by simpa using h)
  have hsub : ({0, S.cl c.u, S.cl r, S.cl c.u + S.cl r} : Set S.Qt) ⊆ commSpace σ := by
    rintro v (rfl | rfl | rfl | rfl)
    · exact (commSpace σ).zero_mem
    · exact huU
    · exact hrU
    · exact (commSpace σ).add_mem huU hrU
  have h4 : ({0, S.cl c.u, S.cl r, S.cl c.u + S.cl r} : Set S.Qt).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨Ne.symm ha0, Ne.symm hb0, Ne.symm e1⟩),
      Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hab, Ne.symm e2⟩),
      Set.ncard_pair (Ne.symm e3)]
  have hcard : (commSpace σ : Set S.Qt).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card (commSpace σ) = 4
    rw [S.card_submodule, hU2]
    norm_num
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, h4]) (Set.toFinite _)
  have hmem : S.cl r₀ ∈ ({0, S.cl c.u, S.cl r, S.cl c.u + S.cl r} : Set S.Qt) := by
    rw [heq]
    exact hr₀U
  have key : ∀ a ∈ S.QG, Commute m a → S.cl a = S.cl r₀ → m * r₀ = r₀ * m := by
    intro a haQ ha hcl
    rcases (S.cl_eq_cl_iff haQ hr₀Q).mp hcl with h | h
    · rw [h]
      exact ha
    · rw [h]
      exact ha.mul_right hmz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h | h
  · exact key 1 (one_mem _) (Commute.one_right m) (S.cl_one.trans h.symm)
  · exact key c.u c.huQ hmu h.symm
  · exact key r hrQ hmr h.symm
  · exact key (c.u * r) (mul_mem c.huQ hrQ) (Commute.mul_right hmu hmr)
      ((S.cl_mul c.huQ hrQ).trans h.symm)

theorem mem_QG_or_of_centralizes (hw : S.width = 2) (hS : IsSThreeAt S.z c.N) {m : G}
    (hmM : m ∈ S.M) (hm : ∀ r ∈ c.Rt, m * r = r * m) : m ∈ S.QG ∨ c.t * m ∈ S.QG := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  set htM := c.t_mem_M_of_sThree hS
  obtain ⟨hU2, hUs, -, -⟩ := c.sThree_typeA hS
  have hV : finrank (ZMod 2) S.Qt = 4 := by rw [S.finrank_Qt_eq_two_mul_width, hw]
  have hfix : ∀ v ∈ commSpace (S.rhoL htM), S.rhoL hmM v = v := by
    intro v hv
    obtain ⟨r, hrQ, rfl⟩ := S.exists_cl v
    have hr : r ∈ c.Rt := by
      rw [c.Rt_eq_clPre hw hS]
      exact S.mem_clPre.mpr ⟨hrQ, hv⟩
    rw [S.rhoL_cl hmM hrQ, hm r hr, mul_inv_cancel_right]
  by_cases hm1 : S.rhoL hmM = 1
  · exact Or.inl ((S.ρ_eq_one_iff ⟨m, hmM⟩).mp (Subtype.ext hm1))
  · right
    have heq := AS62.eq_of_fix_tsPlane hV S.q_nondegenerate hU2 hUs (S.rhoL_mem hmM)
      (S.rhoL_mem htM) hm1 (S.rhoL_ne_one htM c.t_not_mem_QG) hfix fun v hv =>
        mem_fixSpace.mp (commSpace_le_fixSpace (S.rhoL_mul_self htM c.t_mul_self) hv)
    have hρ : S.ρ ⟨m, hmM⟩ = S.ρ ⟨c.t, htM⟩ := Subtype.ext heq
    have htmM : c.t * m ∈ S.M := mul_mem htM hmM
    refine (S.ρ_eq_one_iff ⟨c.t * m, htmM⟩).mp ?_
    rw [show (⟨c.t * m, htmM⟩ : S.M) = ⟨c.t, htM⟩ * ⟨m, hmM⟩ from rfl, map_mul, hρ, ← map_mul,
      show (⟨c.t, htM⟩ * ⟨c.t, htM⟩ : S.M) = 1 from Subtype.ext c.t_mul_self, map_one]

theorem exists_not_commute_Pt (hw : S.width = 2) (hS : IsSThreeAt S.z c.N)
    (hQQ : ∀ w ∈ S.QG ⊓ S.Qa c.g, w = 1 ∨ w = c.u) :
    ∃ p ∈ c.Pt, ∃ r ∈ c.Rt, p * r ≠ r * p := by
  by_contra! h
  have hPQ : ∀ y ∈ c.Pt, y ∈ S.QG → y = 1 ∨ y = c.u := fun y hy hyQ =>
    hQQ y (mem_inf.mpr ⟨hyQ, (mem_inf.mp hy).1⟩)
  have htt : ∀ p : G, p = c.t * (c.t * p) := fun p => by
    rw [← mul_assoc, c.t_mul_self, one_mul]
  have hsub : (c.Pt : Set G) ⊆ {1, c.u, c.t, c.t * c.u} := by
    intro p hp
    rcases c.mem_QG_or_of_centralizes hw hS (mem_inf.mp hp).2 (h p hp) with hq | hq
    · rcases hPQ p hp hq with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
    · rcases hPQ _ (mul_mem (c.t_mem_Pt hS) hp) hq with h1 | h1
      · refine Or.inr (Or.inr (Or.inl ?_))
        rw [htt p, h1, mul_one]
      · refine Or.inr (Or.inr (Or.inr (?_ : p = c.t * c.u)))
        rw [htt p, h1]
  have h8 : (c.Pt : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact c.card_Pt hw hS
  have := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (AS62.ncard_le_four _ _ _ _)
  omega

theorem exists_mul_eq_of_mem (hw : S.width = 2) (hS : IsSThreeAt S.z c.N)
    (hQQ : ∀ w ∈ S.QG ⊓ S.Qa c.g, w = 1 ∨ w = c.u) {k : G} (hkN : k ∈ c.N) (hkM : k ∉ S.M)
    (hR : S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G) = c.Rt)
    (hPt : S.Qa k ⊓ S.M ≤ centralizer ({c.t} : Set G))
    (hQQ' : ∀ w ∈ S.QG ⊓ S.Qa k, w = 1 ∨ w = c.u) {y : G} (hy : y ∈ S.Qa k ⊓ S.M) :
    ∃ p ∈ c.Pt, ∃ r ∈ c.Rt, y = p * r := by
  have hyM := (mem_inf.mp hy).2
  have hyt : y * c.t = c.t * y := mem_centralizer_singleton_iff.mp (hPt hy)
  have hyz : y * S.z = S.z * y := S.mem_M_iff.mp hyM
  have hyu : y * c.u = c.u * y :=
    (c.withG k hkN hkM).commute_of_mem_Pt hw hS hy (c.withG k hkN hkM).u_mem_Pt
  have hyR : ∀ r ∈ c.Rt, y * r * y⁻¹ * r⁻¹ = 1 ∨ y * r * y⁻¹ * r⁻¹ = c.u := by
    intro r hr
    have hr' : r ∈ (c.withG k hkN hkM).Rt := by
      change r ∈ S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G)
      rw [hR]
      exact hr
    exact hQQ' _ ((c.withG k hkN hkM).commutator_mem_inf_Qa hy hr')
  have hfin : ∀ p₁ ∈ c.Pt, (∀ r ∈ c.Rt, p₁⁻¹ * y * r = r * (p₁⁻¹ * y)) →
      ∃ p ∈ c.Pt, ∃ r ∈ c.Rt, y = p * r := by
    intro p₁ hp₁ hm
    have hp₁t : p₁ * c.t = c.t * p₁ :=
      mem_centralizer_singleton_iff.mp (c.Pt_le_centralizer hp₁)
    have hmM : p₁⁻¹ * y ∈ S.M := mul_mem (inv_mem (mem_inf.mp hp₁).2) hyM
    have hmt : Commute (p₁⁻¹ * y) c.t := (Commute.inv_left hp₁t).mul_left hyt
    rcases c.mem_QG_or_of_centralizes hw hS hmM hm with hq | hq
    · exact ⟨p₁, hp₁, p₁⁻¹ * y, mem_inf.mpr ⟨hq, mem_centralizer_singleton_iff.mpr hmt⟩,
        (mul_inv_cancel_left p₁ y).symm⟩
    · refine ⟨p₁ * c.t, mul_mem hp₁ (c.t_mem_Pt hS), c.t * (p₁⁻¹ * y),
        mem_inf.mpr ⟨hq, mem_centralizer_singleton_iff.mpr ((Commute.refl c.t).mul_left hmt)⟩, ?_⟩
      rw [mul_assoc, ← mul_assoc c.t c.t, c.t_mul_self, one_mul, mul_inv_cancel_left]
  by_cases hyR' : ∀ r ∈ c.Rt, y * r = r * y
  · refine hfin 1 (one_mem _) fun r hr => ?_
    rw [inv_one, one_mul]
    exact hyR' r hr
  · push Not at hyR'
    obtain ⟨r₁, hr₁, hyr₁⟩ := hyR'
    obtain ⟨p₀, hp₀, r₀, hr₀, hp₀r₀⟩ := c.exists_not_commute_Pt hw hS hQQ
    have hp₀z : p₀ * S.z = S.z * p₀ := S.mem_M_iff.mp (mem_inf.mp hp₀).2
    have hp₀u : p₀ * c.u = c.u * p₀ := c.commute_of_mem_Pt hw hS hp₀ c.u_mem_Pt
    refine hfin p₀ hp₀ fun r hr => ?_
    have hact : y * r * y⁻¹ = p₀ * r * p₀⁻¹ := by
      by_cases hyr : y * r = r * y
      · have hp₀r : p₀ * r = r * p₀ := by
          rcases c.mem_four_of_commute hw hS hyz hyu hr₁ hyr₁ hr hyr with h | h | h | h <;>
            rw [h]
          · rw [mul_one, one_mul]
          · exact hp₀z
          · exact hp₀u
          · exact Commute.mul_right hp₀u hp₀z
        rw [hyr, hp₀r, mul_inv_cancel_right, mul_inv_cancel_right]
      · have hp₀r : p₀ * r ≠ r * p₀ := by
          intro hp₀r
          apply hyr
          rcases c.mem_four_of_commute hw hS hp₀z hp₀u hr₀ hp₀r₀ hr hp₀r with h | h | h | h <;>
            rw [h]
          · rw [mul_one, one_mul]
          · exact hyz
          · exact hyu
          · exact Commute.mul_right hyu hyz
        have h1 := (hyR r hr).resolve_left fun h =>
          hyr (AS62.mul_comm_iff_commutator_eq_one.mpr h)
        have h2 := (hQQ _ (c.commutator_mem_inf_Qa hp₀ hr)).resolve_left fun h =>
          hp₀r (AS62.mul_comm_iff_commutator_eq_one.mpr h)
        rw [AS62.conj_eq_of_commutator_eq h1, AS62.conj_eq_of_commutator_eq h2]
    calc p₀⁻¹ * y * r = p₀⁻¹ * (y * r * y⁻¹) * y := by group
      _ = p₀⁻¹ * (p₀ * r * p₀⁻¹) * y := by rw [hact]
      _ = r * (p₀⁻¹ * y) := by group

theorem mem_sup_or_mem_sup (hw : S.width = 2) (hS : IsSThreeAt S.z c.N)
    (hQQ : ∀ w ∈ S.QG ⊓ S.Qa c.g, w = 1 ∨ w = c.u) {k : G} (hkN : k ∈ c.N) (hkM : k ∉ S.M)
    (hR : S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G) = c.Rt)
    (hPt : S.Qa k ⊓ S.M ≤ centralizer ({c.t} : Set G))
    (hQQ' : ∀ w ∈ S.QG ⊓ S.Qa k, w = 1 ∨ w = c.u) {y : G} (hy : y ∈ S.Qa k ⊓ S.M) :
    y ∈ c.Rt ⊔ zpowers c.t ∨ y ∈ c.Pt ⊔ zpowers S.z := by
  obtain ⟨p, hp, r, hr, rfl⟩ := c.exists_mul_eq_of_mem hw hS hQQ hkN hkM hR hPt hQQ' hy
  have hyy := (c.withG k hkN hkM).mul_self_of_mem_Pt hw hS hy
  have hpp := c.mul_self_of_mem_Pt hw hS hp
  have hrr := c.mul_self_of_mem_Rt hw hS hr
  have hpr : p * r = r * p := by
    have h1 : p * r = (p * r)⁻¹ := eq_inv_of_mul_eq_one_left hyy
    rwa [mul_inv_rev, inv_eq_of_mul_eq_one_right hrr, inv_eq_of_mul_eq_one_right hpp] at h1
  by_cases hpR : ∀ r' ∈ c.Rt, p * r' = r' * p
  · left
    have hpt : p * c.t = c.t * p := mem_centralizer_singleton_iff.mp (c.Pt_le_centralizer hp)
    rcases c.mem_QG_or_of_centralizes hw hS (mem_inf.mp hp).2 hpR with hq | hq
    · exact mem_sup_left (mul_mem (mem_inf.mpr ⟨hq, mem_centralizer_singleton_iff.mpr hpt⟩) hr)
    · have htp : c.t * p ∈ c.Rt := mem_inf.mpr ⟨hq, mem_centralizer_singleton_iff.mpr
        ((Commute.refl c.t).mul_left hpt)⟩
      have h1 := mul_mem (mem_sup_right (mem_zpowers c.t) : c.t ∈ c.Rt ⊔ zpowers c.t)
        (mem_sup_left (mul_mem htp hr) : c.t * p * r ∈ c.Rt ⊔ zpowers c.t)
      rwa [← mul_assoc, ← mul_assoc, c.t_mul_self, one_mul] at h1
  · right
    push Not at hpR
    obtain ⟨r₀, hr₀, hpr₀⟩ := hpR
    have hpz : p * S.z = S.z * p := S.mem_M_iff.mp (mem_inf.mp hp).2
    have hpu : p * c.u = c.u * p := c.commute_of_mem_Pt hw hS hp c.u_mem_Pt
    rcases c.mem_four_of_commute hw hS hpz hpu hr₀ hpr₀ hr hpr with h | h | h | h <;> rw [h]
    · rw [mul_one]
      exact mem_sup_left hp
    · exact mul_mem (mem_sup_left hp) (mem_sup_right (mem_zpowers _))
    · exact mem_sup_left (mul_mem hp c.u_mem_Pt)
    · rw [← mul_assoc]
      exact mul_mem (mem_sup_left (mul_mem hp c.u_mem_Pt)) (mem_sup_right (mem_zpowers _))

theorem false_of_inf_le_two (hw : S.width = 2) (hS : IsSThreeAt S.z c.N)
    (hQQ : ∀ w ∈ S.QG ⊓ S.Qa c.g, w = 1 ∨ w = c.u) : False := by
  obtain ⟨k, hkN, hkM, hR, hPt, hQQ', hQQ''⟩ := c.exists_third_conj hw hS hQQ
  have h8 : Nat.card ↥(S.Qa k ⊓ S.M) = 8 := (c.withG k hkN hkM).card_Pt hw hS
  have hsub : ((S.Qa k ⊓ S.M : Subgroup G) : Set G) ⊆
      ((c.Rt ⊔ zpowers c.t : Subgroup G) : Set G) ∪
        ((c.Pt ⊔ zpowers S.z : Subgroup G) : Set G) :=
    fun y hy => c.mem_sup_or_mem_sup hw hS hQQ hkN hkM hR hPt hQQ' hy
  rcases SubgroupClass.subset_union.mp hsub with hle | hle
  ·
    have htn : ∀ r ∈ c.Rt, c.t * r * c.t⁻¹ ∈ c.Rt := fun r hr => by
      rw [← mem_centralizer_singleton_iff.mp (mem_inf.mp hr).2, mul_inv_cancel_right]
      exact hr
    have := AS62.card_le_four_of_le_sup c.t_mul_self htn hle fun y hy hyR =>
      hQQ' y (mem_inf.mpr ⟨(mem_inf.mp hyR).1, (mem_inf.mp hy).1⟩)
    omega
  ·
    have hzn : ∀ p ∈ c.Pt, S.z * p * S.z⁻¹ ∈ c.Pt := fun p hp => by
      rw [← S.mem_M_iff.mp (mem_inf.mp hp).2, mul_inv_cancel_right]
      exact hp
    have := AS62.card_le_four_of_le_sup S.z_mul_z hzn hle fun y hy hyP =>
      hQQ'' y (mem_inf.mpr ⟨(mem_inf.mp hyP).1, (mem_inf.mp hy).1⟩)
    omega

end SixThreeCtx

end Setting

end CFSG.LargeExtraspecial
