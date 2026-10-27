module

public import CFSG.LargeExtraspecial.AS35DSixThreeD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Asc77 CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G]

namespace SixThreeCtx

variable {S : Setting G} (c : SixThreeCtx S)

abbrev Rt : Subgroup G := S.QG ⊓ centralizer ({c.t} : Set G)

noncomputable abbrev Pt : Subgroup G := S.Qa c.g ⊓ S.M

abbrev withG (k : G) (hkN : k ∈ c.N) (hkM : k ∉ S.M) : SixThreeCtx S :=
  { c with g := k, hgN := hkN, hgM := hkM }

theorem fixSpace_eq_commSpace_of_width_two (hw : S.width = 2) (hS : IsSThreeAt S.z c.N) :
    fixSpace (S.rhoL (c.t_mem_M_of_sThree hS)) =
      commSpace (S.rhoL (c.t_mem_M_of_sThree hS)) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  set htM := c.t_mem_M_of_sThree hS
  have h2 := (c.sThree_typeA hS).1
  have h3 := finrank_commSpace_add_finrank_fixSpace (S.rhoL htM)
  rw [S.finrank_Qt_eq_two_mul_width, hw] at h3
  exact (Submodule.eq_of_le_of_finrank_eq
    (commSpace_le_fixSpace (S.rhoL_mul_self htM c.t_mul_self)) (by omega)).symm

theorem Rt_eq_clPre (hw : S.width = 2) (hS : IsSThreeAt S.z c.N) :
    c.Rt = S.clPre (commSpace (S.rhoL (c.t_mem_M_of_sThree hS))) := by
  rw [← c.fixSpace_eq_commSpace_of_width_two hw hS]
  exact (c.sThree_typeA hS).2.2.1

theorem card_Rt (hw : S.width = 2) (hS : IsSThreeAt S.z c.N) : Nat.card c.Rt = 8 := by
  have hk := c.card_QG_eq_four_mul hS
  rw [S.card_QG_eq_card_Q, S.card_Q_eq, hw,
    show (2 : ℕ) ^ (1 + 2 * 2) = 2 ^ 2 * 8 by norm_num] at hk
  exact (Nat.eq_of_mul_eq_mul_left (by norm_num) hk).symm

theorem mul_self_of_mem_Rt (hw : S.width = 2) (hS : IsSThreeAt S.z c.N) {r : G}
    (hr : r ∈ c.Rt) : r * r = 1 := by
  rw [c.Rt_eq_clPre hw hS] at hr
  obtain ⟨hrQ, hrU⟩ := S.mem_clPre.mp hr
  rw [← pow_two, ← S.q_cl_eq_zero_iff hrQ]
  exact (c.sThree_typeA hS).2.1 _ hrU

theorem commute_of_mem_Rt (hw : S.width = 2) (hS : IsSThreeAt S.z c.N) {r r' : G}
    (hr : r ∈ c.Rt) (hr' : r' ∈ c.Rt) : r * r' = r' * r := by
  set htM := c.t_mem_M_of_sThree hS
  rw [c.Rt_eq_clPre hw hS] at hr hr'
  obtain ⟨hrQ, hrU⟩ := S.mem_clPre.mp hr
  obtain ⟨hr'Q, hr'U⟩ := S.mem_clPre.mp hr'
  rw [← S.polar_cl_eq_zero_iff hrQ hr'Q]
  exact polar_commSpace_eq_zero (S.rhoL_mem htM) (S.rhoL_mul_self htM c.t_mul_self) hrU hr'U

omit [Finite G] in
theorem u_mem_Rt : c.u ∈ c.Rt :=
  mem_inf.mpr ⟨c.huQ, mem_centralizer_singleton_iff.mpr c.commute_u_t⟩

theorem Pt_eq_map {h : G} (hhz : h * S.z * h⁻¹ = c.t) (hht : h * c.t * h⁻¹ = S.z) :
    c.Pt = c.Rt.map (MulAut.conj h).toMonoidHom := by
  have hQah : S.Qa h = S.Qa c.g := S.Qa_eq_of_conj_eq (by rw [hhz])
  ext y
  constructor
  · intro hy
    obtain ⟨hyQa, hyM⟩ := mem_inf.mp hy
    rw [← hQah, S.Qa_eq_map] at hyQa
    obtain ⟨x, hxQ, rfl⟩ := hyQa
    refine ⟨x, mem_inf.mpr ⟨hxQ, mem_centralizer_singleton_iff.mpr ?_⟩, rfl⟩
    have h1 := S.mem_M_iff.mp hyM
    change h * x * h⁻¹ * S.z = S.z * (h * x * h⁻¹) at h1
    have ht' : c.t = h⁻¹ * S.z * h := by
      rw [← hht]
      exact (show ∀ a : G, a = h⁻¹ * (h * a * h⁻¹) * h from fun a => by group) c.t
    calc x * c.t = h⁻¹ * ((h * x * h⁻¹) * S.z) * h := by rw [ht']; group
      _ = h⁻¹ * (S.z * (h * x * h⁻¹)) * h := by rw [h1]
      _ = c.t * x := by rw [ht']; group
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxQ, hxt⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [← hQah, S.Qa_eq_map]
      exact ⟨x, hxQ, rfl⟩
    · rw [S.mem_M_iff]
      change h * x * h⁻¹ * S.z = S.z * (h * x * h⁻¹)
      have hxt' := mem_centralizer_singleton_iff.mp hxt
      calc h * x * h⁻¹ * S.z = h * (x * c.t) * h⁻¹ := by rw [← hht]; group
        _ = h * (c.t * x) * h⁻¹ := by rw [hxt']
        _ = S.z * (h * x * h⁻¹) := by rw [← hht]; group

theorem card_Pt (hw : S.width = 2) (hS : IsSThreeAt S.z c.N) : Nat.card c.Pt = 8 := by
  obtain ⟨h, -, hhz, hht⟩ := c.exists_swap hS
  rw [c.Pt_eq_map hhz hht, card_map_of_injective (MulAut.conj h).injective, c.card_Rt hw hS]

theorem mul_self_of_mem_Pt (hw : S.width = 2) (hS : IsSThreeAt S.z c.N) {p : G}
    (hp : p ∈ c.Pt) : p * p = 1 := by
  obtain ⟨h, -, hhz, hht⟩ := c.exists_swap hS
  rw [c.Pt_eq_map hhz hht] at hp
  obtain ⟨r, hr, rfl⟩ := hp
  change h * r * h⁻¹ * (h * r * h⁻¹) = 1
  rw [show h * r * h⁻¹ * (h * r * h⁻¹) = h * (r * r) * h⁻¹ by group,
    c.mul_self_of_mem_Rt hw hS hr]
  group

theorem commute_of_mem_Pt (hw : S.width = 2) (hS : IsSThreeAt S.z c.N) {p p' : G}
    (hp : p ∈ c.Pt) (hp' : p' ∈ c.Pt) : p * p' = p' * p := by
  obtain ⟨h, -, hhz, hht⟩ := c.exists_swap hS
  rw [c.Pt_eq_map hhz hht] at hp hp'
  obtain ⟨r, hr, rfl⟩ := hp
  obtain ⟨r', hr', rfl⟩ := hp'
  change h * r * h⁻¹ * (h * r' * h⁻¹) = h * r' * h⁻¹ * (h * r * h⁻¹)
  rw [show h * r * h⁻¹ * (h * r' * h⁻¹) = h * (r * r') * h⁻¹ by group,
    show h * r' * h⁻¹ * (h * r * h⁻¹) = h * (r' * r) * h⁻¹ by group,
    c.commute_of_mem_Rt hw hS hr hr']

omit [Finite G] in
theorem t_mem_Pt (hS : IsSThreeAt S.z c.N) : c.t ∈ c.Pt :=
  mem_inf.mpr ⟨(S.conjBy c.g).z_mem_QG, c.t_mem_M_of_sThree hS⟩

omit [Finite G] in
theorem u_mem_Pt : c.u ∈ c.Pt := mem_inf.mpr ⟨c.u_mem_Qa, S.QG_le_M c.huQ⟩

omit [Finite G] in
theorem Pt_le_centralizer : c.Pt ≤ centralizer ({c.t} : Set G) :=
  fun _ hp => (S.conjBy c.g).QG_le_M (mem_inf.mp hp).1

omit [Finite G] in
theorem commutator_mem_inf_Qa {p r : G} (hp : p ∈ c.Pt) (hr : r ∈ c.Rt) :
    p * r * p⁻¹ * r⁻¹ ∈ S.QG ⊓ S.Qa c.g := by
  obtain ⟨hpQa, hpM⟩ := mem_inf.mp hp
  obtain ⟨hrQ, hrt⟩ := mem_inf.mp hr
  have hrT : r ∈ (S.conjBy c.g).M := hrt
  refine mem_inf.mpr ⟨mul_mem (S.conj_mem_QG hpM hrQ) (inv_mem hrQ), ?_⟩
  rw [show p * r * p⁻¹ * r⁻¹ = p * (r * p⁻¹ * r⁻¹) by group]
  exact mul_mem hpQa ((S.conjBy c.g).conj_mem_QG hrT (inv_mem hpQa))

omit [Finite G] in
theorem eq_t_of_conj_mem_Qa {k : G} (hk : k * S.z * k⁻¹ ∈ S.Qa c.g) :
    k * S.z * k⁻¹ = c.t := by
  rw [S.Qa_eq_map] at hk
  obtain ⟨q, hq, hqk⟩ := hk
  change c.g * q * c.g⁻¹ = k * S.z * k⁻¹ at hqk
  have hq' : q = (c.g⁻¹ * k) * S.z * (c.g⁻¹ * k)⁻¹ := by
    calc q = c.g⁻¹ * (c.g * q * c.g⁻¹) * c.g := by group
      _ = (c.g⁻¹ * k) * S.z * (c.g⁻¹ * k)⁻¹ := by rw [hqk]; group
  have h1 := c.hW (c.g⁻¹ * k) (hq' ▸ hq)
  rw [← hqk, hq'.trans h1]

omit [Finite G] in
theorem eq_one_or_eq_u_of_conj {m w : G} (hmN : m ∈ c.N)
    (h : m * w * m⁻¹ = 1 ∨ m * w * m⁻¹ = c.u) : w = 1 ∨ w = c.u := by
  have hw : w = m⁻¹ * (m * w * m⁻¹) * m := by group
  rcases h with h | h <;> rw [h] at hw
  · left
    rw [hw]
    group
  · right
    rw [hw, mul_assoc, ← c.commute_u hmN, inv_mul_cancel_left]

omit [Finite G] in
theorem exists_transposition (hS : IsSThreeAt S.z c.N) {a b : G} (ha : a ∈ S.zConj c.N)
    (hb : b ∈ S.zConj c.N) :
    ∃ k ∈ c.N, k * a * k⁻¹ = b ∧ k * b * k⁻¹ = a ∧
      ∀ y ∈ S.zConj c.N, y ≠ a → y ≠ b → k * y * k⁻¹ = y := by
  classical
  obtain ⟨-, -, -, hsurj⟩ := hS
  obtain ⟨k, hk⟩ := hsurj (Equiv.swap ⟨a, ha⟩ ⟨b, hb⟩)
  have key : ∀ y : S.zConj c.N,
      (k : G) * y * (k : G)⁻¹ = ((Equiv.swap ⟨a, ha⟩ ⟨b, hb⟩ y : S.zConj c.N) : G) :=
    fun y => by rw [← hk]; rfl
  refine ⟨k, k.2, ?_, ?_, fun y hy hya hyb => ?_⟩
  · have := key ⟨a, ha⟩
    rw [Equiv.swap_apply_left] at this
    exact this
  · have := key ⟨b, hb⟩
    rw [Equiv.swap_apply_right] at this
    exact this
  · have := key ⟨y, hy⟩
    rw [Equiv.swap_apply_of_ne_of_ne (fun h => hya (congrArg Subtype.val h))
      (fun h => hyb (congrArg Subtype.val h))] at this
    exact this

omit [Finite G] in
theorem exists_third_point (hS : IsSThreeAt S.z c.N) :
    ∃ x ∈ S.zConj c.N, x ≠ S.z ∧ x ≠ c.t ∧ ∀ y ∈ S.zConj c.N, y = S.z ∨ y = c.t ∨ y = x := by
  have hsub : ({S.z, c.t} : Set G) ⊆ S.zConj c.N := by
    rintro y (rfl | rfl)
    · exact self_mem_conjIn _ _
    · exact c.t_mem_zConj
  have h1 : (S.zConj c.N \ {S.z, c.t}).ncard = 1 := by
    rw [Set.ncard_sdiff hsub, hS.1, Set.ncard_pair (Ne.symm c.t_ne_z)]
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp h1
  have hxmem : x ∈ S.zConj c.N \ {S.z, c.t} := by
    rw [hx]
    exact Set.mem_singleton x
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hxmem
  refine ⟨x, hxmem.1, hxmem.2.1, hxmem.2.2, fun y hy => ?_⟩
  by_contra! hne
  have hy' : y ∈ S.zConj c.N \ {S.z, c.t} := by
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hy, hne.1, hne.2.1⟩
  rw [hx] at hy'
  exact hne.2.2 hy'

omit [Finite G] in
theorem commute_t_mul_third (hS : IsSThreeAt S.z c.N) {x : G} (hxΩ : x ∈ S.zConj c.N)
    (hxz : x ≠ S.z) (hxt : x ≠ c.t) (hΩ : ∀ y ∈ S.zConj c.N, y = S.z ∨ y = c.t ∨ y = x)
    {k : G} (hk : k ∈ c.P) : k * (c.t * x) = c.t * x * k := by
  have hkN := c.hPN hk
  have hkQ := (mem_inf.mp hk).1
  have hkz' : k⁻¹ * S.z * k = S.z := by rw [S.z_comm_QG (inv_mem hkQ)]; group
  have hmap : ∀ y ∈ S.zConj c.N, y ≠ S.z → k * y * k⁻¹ = c.t ∨ k * y * k⁻¹ = x := by
    intro y hy hyz
    rcases hΩ _ (conj_mem_conjIn_of_mem hkN hy) with h | h | h
    · exfalso
      apply hyz
      calc y = k⁻¹ * (k * y * k⁻¹) * k := by group
        _ = S.z := by rw [h, hkz']
    · exact Or.inl h
    · exact Or.inr h
  have hinj : k * c.t * k⁻¹ ≠ k * x * k⁻¹ := fun h =>
    hxt (mul_left_cancel (mul_right_cancel h)).symm
  have htx : c.t * x = x * c.t := hS.2.1 _ c.t_mem_zConj _ hxΩ
  have e : ∀ a b : G, k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := fun a b => by group
  have hconj : k * (c.t * x) * k⁻¹ = c.t * x := by
    rw [e]
    rcases hmap _ c.t_mem_zConj c.t_ne_z with h1 | h1 <;>
      rcases hmap _ hxΩ hxz with h2 | h2
    · exact absurd (h1.trans h2.symm) hinj
    · rw [h1, h2]
    · rw [h1, h2, htx]
    · exact absurd (h1.trans h2.symm) hinj
  calc k * (c.t * x) = k * (c.t * x) * k⁻¹ * k := (inv_mul_cancel_right _ _).symm
    _ = c.t * x * k := by rw [hconj]

theorem t_mul_third_eq (hS : IsSThreeAt S.z c.N) {x : G} (hxΩ : x ∈ S.zConj c.N)
    (hxz : x ≠ S.z) (hxt : x ≠ c.t) (hΩ : ∀ y ∈ S.zConj c.N, y = S.z ∨ y = c.t ∨ y = x) :
    c.t * x = S.z ∨ c.t * x = c.u * S.z := by
  have htx : c.t * x = x * c.t := hS.2.1 _ c.t_mem_zConj _ hxΩ
  have hxx : x * x = 1 := by
    obtain ⟨k, -, rfl⟩ := hxΩ
    rw [show k * S.z * k⁻¹ * (k * S.z * k⁻¹) = k * (S.z * S.z) * k⁻¹ by group, S.z_mul_z]
    group
  have hd2 : (c.t * x) ^ 2 = 1 := by
    rw [pow_two]
    calc c.t * x * (c.t * x) = c.t * (x * c.t) * x := by simp only [mul_assoc]
      _ = c.t * c.t * (x * x) := by rw [← htx]; simp only [mul_assoc]
      _ = 1 := by rw [c.t_mul_self, hxx, one_mul]
  have hcomm : ∀ f ∈ c.P, f * (c.t * x) = c.t * x * f := fun f hf =>
    c.commute_t_mul_third hS hxΩ hxz hxt hΩ hf
  have hdQ : c.t * x ∈ S.QG := S.mem_QG_of_sq_eq_one_of_commute inf_le_left
    (S.relIndex_centralizer_eq_two c.huQ c.hu1 c.huz) hd2 fun f hf => (hcomm f hf).symm
  have hd : c.t * x ∈ S.QG ⊓ centralizer ((S.QG ⊓ centralizer ({c.u} : Set G) :
      Subgroup G) : Set G) :=
    mem_inf.mpr ⟨hdQ, mem_centralizer_iff.mpr hcomm⟩
  have hxeq : x = c.t * (c.t * x) := by rw [← mul_assoc, c.t_mul_self, one_mul]
  rcases (S.mem_centralizer_centralizer_iff c.huQ).mp hd with h | h | h | h
  · exfalso
    apply hxt
    rw [hxeq, h, mul_one]
  · exact Or.inl h
  · exfalso
    apply hxt
    have hxQa : x ∈ S.Qa c.g := by
      rw [hxeq, h]
      exact mul_mem (S.conj_z_mem_Qa c.g) c.u_mem_Qa
    obtain ⟨k, -, rfl⟩ := hxΩ
    exact c.eq_t_of_conj_mem_Qa hxQa
  · exact Or.inr h

theorem exists_third_conj (hw : S.width = 2) (hS : IsSThreeAt S.z c.N)
    (hQQ : ∀ w ∈ S.QG ⊓ S.Qa c.g, w = 1 ∨ w = c.u) :
    ∃ k ∈ c.N, k ∉ S.M ∧ S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G) = c.Rt ∧
      S.Qa k ⊓ S.M ≤ centralizer ({c.t} : Set G) ∧
      (∀ w ∈ S.QG ⊓ S.Qa k, w = 1 ∨ w = c.u) ∧
      (∀ w ∈ S.Qa c.g ⊓ S.Qa k, w = 1 ∨ w = c.u) := by
  have inv_conj : ∀ a b d : G, a * b * a⁻¹ = d → a⁻¹ * d * a = b := fun a b d h => by
    rw [← h]
    group
  obtain ⟨x, hxΩ, hxz, hxt, hΩ⟩ := c.exists_third_point hS
  have hzΩ : S.z ∈ S.zConj c.N := self_mem_conjIn _ _
  have htΩ : c.t ∈ S.zConj c.N := c.t_mem_zConj
  obtain ⟨k, hkN, hkz, -, -⟩ := c.exists_transposition hS hzΩ hxΩ
  obtain ⟨s, hsN, hst, -, hsfix⟩ := c.exists_transposition hS htΩ hxΩ
  obtain ⟨h, hhN, hhz, -, hhfix⟩ := c.exists_transposition hS hzΩ htΩ
  have hsz := inv_conj s S.z S.z (hsfix _ hzΩ (Ne.symm c.t_ne_z) (Ne.symm hxz))
  have hhx := inv_conj h x x (hhfix _ hxΩ hxz hxt)
  have hst' := inv_conj s c.t x hst
  have hhz' := inv_conj h S.z c.t hhz
  have hkM : k ∉ S.M := by
    intro hkM
    apply hxz
    rw [← hkz, S.mem_M_iff.mp hkM, mul_inv_cancel_right]
  have hd := c.t_mul_third_eq hS hxΩ hxz hxt hΩ
  have hxeq : x = c.t * (c.t * x) := by rw [← mul_assoc, c.t_mul_self, one_mul]
  have hR : S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G) = c.Rt := by
    have hle : c.Rt ≤ S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G) := by
      intro y hy
      obtain ⟨hyQ, hyt⟩ := mem_inf.mp hy
      have hyt' : Commute y c.t := mem_centralizer_singleton_iff.mp hyt
      have hyu : Commute y c.u :=
        mem_centralizer_singleton_iff.mp (mem_inf.mp (c.cqt_le hy)).2
      have hyd : Commute y (c.t * x) := by
        rcases hd with h' | h' <;> rw [h']
        · exact S.z_comm_QG hyQ
        · exact hyu.mul_right (S.z_comm_QG hyQ)
      refine mem_inf.mpr ⟨hyQ, mem_centralizer_singleton_iff.mpr ?_⟩
      rw [hkz, hxeq]
      exact hyt'.mul_right hyd
    have h1 : Nat.card ↥(S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G)) = 8 :=
      (c.withG k hkN hkM).card_Rt hw hS
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [h1, c.card_Rt hw hS]
  have hPt : S.Qa k ⊓ S.M ≤ centralizer ({c.t} : Set G) := by
    intro y hy
    have h1 : y ∈ centralizer ({k * S.z * k⁻¹} : Set G) :=
      (c.withG k hkN hkM).Pt_le_centralizer hy
    rw [hkz] at h1
    have hyx : Commute y x := mem_centralizer_singleton_iff.mp h1
    have hyz : Commute y S.z := S.mem_M_iff.mp (mem_inf.mp hy).2
    have hyu : Commute y c.u :=
      (c.withG k hkN hkM).commute_of_mem_Pt hw hS hy (c.withG k hkN hkM).u_mem_Pt
    have hyd : Commute y (c.t * x) := by
      rcases hd with h' | h' <;> rw [h']
      · exact hyz
      · exact hyu.mul_right hyz
    have h2 := hyd.mul_right hyx.inv_right
    rw [mul_inv_cancel_right] at h2
    exact mem_centralizer_singleton_iff.mpr h2
  have e2 : ∀ a b : G, a * b * S.z * (a * b)⁻¹ = a * (b * S.z * b⁻¹) * a⁻¹ := fun a b => by
    group
  have hQQ' : ∀ w ∈ S.QG ⊓ S.Qa k, w = 1 ∨ w = c.u := by
    intro w hw
    obtain ⟨hwQ, hwk⟩ := mem_inf.mp hw
    have hsM : s⁻¹ ∈ S.M := S.mem_M_iff.mpr (by
      calc s⁻¹ * S.z = s⁻¹ * S.z * s * s⁻¹ := by group
        _ = S.z * s⁻¹ := by rw [hsz])
    have hQs : S.Qa (s⁻¹ * k) = S.Qa c.g := by
      refine S.Qa_eq_of_conj_eq ?_
      rw [e2, hkz, inv_inv]
      exact hst'
    have h1 : s⁻¹ * w * s⁻¹⁻¹ ∈ S.Qa c.g := hQs ▸ S.conj_mem_Qa_mul (h := s⁻¹) hwk
    have h2 : s⁻¹ * w * s⁻¹⁻¹ ∈ S.QG := S.conj_mem_QG hsM hwQ
    exact c.eq_one_or_eq_u_of_conj (inv_mem hsN) (hQQ _ (mem_inf.mpr ⟨h2, h1⟩))
  have hQQ'' : ∀ w ∈ S.Qa c.g ⊓ S.Qa k, w = 1 ∨ w = c.u := by
    intro w hw
    obtain ⟨hwg, hwk⟩ := mem_inf.mp hw
    have hmN : s⁻¹ * h⁻¹ ∈ c.N := mul_mem (inv_mem hsN) (inv_mem hhN)
    have e : ∀ a : G, (s⁻¹ * h⁻¹) * a * (s⁻¹ * h⁻¹)⁻¹ = s⁻¹ * (h⁻¹ * a * h) * s := fun a => by
      group
    have hmt : (s⁻¹ * h⁻¹) * c.t * (s⁻¹ * h⁻¹)⁻¹ = S.z := by rw [e, hhz', hsz]
    have hmx : (s⁻¹ * h⁻¹) * x * (s⁻¹ * h⁻¹)⁻¹ = c.t := by rw [e, hhx, hst']
    have hQ1 : S.Qa ((s⁻¹ * h⁻¹) * c.g) = S.QG := by
      rw [← S.Qa_one]
      refine S.Qa_eq_of_conj_eq ?_
      rw [e2]
      exact hmt.trans (by group)
    have hQ2 : S.Qa ((s⁻¹ * h⁻¹) * k) = S.Qa c.g := by
      refine S.Qa_eq_of_conj_eq ?_
      rw [e2, hkz]
      exact hmx
    have h1 : (s⁻¹ * h⁻¹) * w * (s⁻¹ * h⁻¹)⁻¹ ∈ S.QG :=
      hQ1 ▸ S.conj_mem_Qa_mul (h := s⁻¹ * h⁻¹) hwg
    have h2 : (s⁻¹ * h⁻¹) * w * (s⁻¹ * h⁻¹)⁻¹ ∈ S.Qa c.g :=
      hQ2 ▸ S.conj_mem_Qa_mul (h := s⁻¹ * h⁻¹) hwk
    exact c.eq_one_or_eq_u_of_conj hmN (hQQ _ (mem_inf.mpr ⟨h1, h2⟩))
  exact ⟨k, hkN, hkM, hR, hPt, hQQ', hQQ''⟩

end SixThreeCtx

end Setting

end CFSG.LargeExtraspecial
