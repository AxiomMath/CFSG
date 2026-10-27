module

public import CFSG.LargeExtraspecial.AS35DSixThreeD
public import CFSG.LargeExtraspecial.AS35DThreeSeven

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Asc77 CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem Qa_not_le_M (S : Setting G) {g : G} (hgM : g ∉ S.M) : ¬ S.Qa g ≤ S.M := by
  intro hM
  apply hgM
  have hc : ∀ q ∈ S.QG, q * (g⁻¹ * S.z * g) = (g⁻¹ * S.z * g) * q := by
    intro q hq
    have h1 : g * q * g⁻¹ ∈ S.M := hM (by rw [S.Qa_eq_map]; exact ⟨q, hq, rfl⟩)
    have h2 := S.mem_M_iff.mp h1
    calc q * (g⁻¹ * S.z * g) = g⁻¹ * ((g * q * g⁻¹) * S.z) * g := by group
      _ = g⁻¹ * (S.z * (g * q * g⁻¹)) * g := by rw [h2]
      _ = (g⁻¹ * S.z * g) * q := by group
  have h1 : g⁻¹ * S.z * g ≠ 1 := by
    intro h
    apply S.z_ne_one
    calc S.z = g * (g⁻¹ * S.z * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have h3 := S.eq_z_of_commute_QG hc h1
  rw [S.mem_M_iff]
  calc g * S.z = g * (g⁻¹ * S.z * g) := by rw [h3]
    _ = S.z * g := by group

namespace SixThreeCtx

variable {S : Setting G} (c : SixThreeCtx S)

theorem false_of_inf_le (hn3 : 3 ≤ S.width) (hS : IsSThreeAt S.z c.N)
    (hQQ : ∀ w ∈ S.QG ⊓ S.Qa c.g, w = 1 ∨ w = c.u) : False := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  set htM := c.t_mem_M_of_sThree hS
  obtain ⟨hU2, hUs, hCfix, hZ⟩ := c.sThree_typeA hS
  set σ := S.rhoL htM with hσ
  set T := S.conjBy c.g with hT
  have hσ2 := S.rhoL_mul_self htM c.t_mul_self
  have huZ := c.inf_Qa_le_center (mem_inf.mpr ⟨c.huQ, c.u_mem_Qa⟩)
  rw [hZ] at huZ
  have hcuU : S.cl c.u ∈ commSpace σ := (S.mem_clPre.mp huZ).2
  have hcu0 : S.cl c.u ≠ 0 := by
    rw [ne_eq, S.cl_eq_zero_iff c.huQ]
    rintro (h | h)
    · exact c.hu1 h
    · exact c.huz h
  set Y := S.Qa c.g ⊓ S.M with hY
  have hYc : ∀ w (hw : w ∈ Y), ∀ v, (∀ x ∈ commSpace σ, QuadraticMap.polar S.q x v = 0) →
      S.rhoL (mem_inf.mp hw).2 v - v ∈ Submodule.span (ZMod 2) {S.cl c.u} := by
    intro w hw v hv
    obtain ⟨hwQa, hwM⟩ := mem_inf.mp hw
    obtain ⟨y, hyQ, rfl⟩ := S.exists_cl v
    have hyC : y ∈ S.QG ⊓ centralizer ({c.t} : Set G) := by
      rw [hCfix]
      refine S.mem_clPre.mpr ⟨hyQ, ?_⟩
      rw [fixSpace_eq_orthogonal_commSpace S.q_nondegenerate (S.rhoL_mem htM) hσ2,
        LinearMap.BilinForm.mem_orthogonal_iff]
      intro x hx
      change S.q.polarBilin x (S.cl y) = 0
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hv x hx
    have hyT : y ∈ T.M := (mem_inf.mp hyC).2
    have hcomm : w * y * w⁻¹ * y⁻¹ ∈ S.QG ⊓ S.Qa c.g := by
      refine mem_inf.mpr ⟨mul_mem (S.conj_mem_QG hwM hyQ) (inv_mem hyQ), ?_⟩
      rw [show w * y * w⁻¹ * y⁻¹ = w * (y * w⁻¹ * y⁻¹) by group]
      exact mul_mem hwQa (T.conj_mem_QG hyT (inv_mem hwQa))
    have hcl : S.rhoL hwM (S.cl y) - S.cl y = S.cl (w * y * w⁻¹ * y⁻¹) := by
      rw [S.rhoL_cl hwM hyQ, S.cl_mul (S.conj_mem_QG hwM hyQ) (inv_mem hyQ), S.cl_inv hyQ,
        sub_eq_add_vec (ZMod 2)]
    rw [hcl]
    rcases hQQ _ hcomm with h | h
    · rw [h, S.cl_one]
      exact Submodule.zero_mem _
    · rw [h]
      exact Submodule.mem_span_singleton_self _
  have hYab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
    intro a ha b hb
    have hcommρ := S.commute_of_sub_mem_span hU2 hUs hcuU hcu0 (S.rhoL_mem (mem_inf.mp ha).2)
      (S.rhoL_mem (mem_inf.mp hb).2) (hYc a ha) (hYc b hb)
    have haM := (mem_inf.mp ha).2
    have hbM := (mem_inf.mp hb).2
    have hρ : S.ρ (⟨a, haM⟩ * ⟨b, hbM⟩ * (⟨a, haM⟩ : S.M)⁻¹ * (⟨b, hbM⟩ : S.M)⁻¹) = 1 := by
      have h1 : S.ρ ⟨a, haM⟩ * S.ρ ⟨b, hbM⟩ = S.ρ ⟨b, hbM⟩ * S.ρ ⟨a, haM⟩ :=
        Subtype.ext hcommρ
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    have hQ : a * b * a⁻¹ * b⁻¹ ∈ S.QG := (S.ρ_eq_one_iff _).mp hρ
    have hQa : a * b * a⁻¹ * b⁻¹ ∈ S.Qa c.g :=
      mul_mem (mul_mem (mul_mem (mem_inf.mp ha).1 (mem_inf.mp hb).1)
        (inv_mem (mem_inf.mp ha).1)) (inv_mem (mem_inf.mp hb).1)
    have hone : a * b * a⁻¹ * b⁻¹ = 1 := by
      rcases hQQ _ (mem_inf.mpr ⟨hQ, hQa⟩) with h | h
      · exact h
      · exfalso
        rcases T.commutator_eq_one_or_z (mem_inf.mp ha).1 (mem_inf.mp hb).1 with h' | h'
        · exact c.hu1 (h ▸ h')
        · apply c.t_not_mem_QG
          change T.z ∈ S.QG
          rw [← h', h]
          exact c.huQ
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [hone, one_mul]
  obtain ⟨h, hhN, hhz, hht⟩ := c.exists_swap hS
  have hQah : S.Qa h = S.Qa c.g := S.Qa_eq_of_conj_eq (by rw [hhz])
  have hYmap : (S.QG ⊓ centralizer ({c.t} : Set G)).map (MulAut.conj h).toMonoidHom = Y := by
    ext y
    constructor
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
    · intro hy
      obtain ⟨hyQa, hyM⟩ := mem_inf.mp hy
      rw [← hQah, S.Qa_eq_map] at hyQa
      obtain ⟨x, hxQ, rfl⟩ := hyQa
      refine ⟨x, mem_inf.mpr ⟨hxQ, mem_centralizer_singleton_iff.mpr ?_⟩, rfl⟩
      have h1 := S.mem_M_iff.mp hyM
      change h * x * h⁻¹ * S.z = S.z * (h * x * h⁻¹) at h1
      have key : ∀ a : G, a = h⁻¹ * (h * a * h⁻¹) * h := fun a => by group
      have ht' : c.t = h⁻¹ * S.z * h := by rw [← hht]; exact key c.t
      calc x * c.t = h⁻¹ * ((h * x * h⁻¹) * S.z) * h := by rw [ht']; group
        _ = h⁻¹ * (S.z * (h * x * h⁻¹)) * h := by rw [h1]
        _ = c.t * x := by rw [ht']; group
  have hcardY : Nat.card Y = Nat.card ↥(S.QG ⊓ centralizer ({c.t} : Set G)) := by
    rw [← hYmap, card_map_of_injective (MulAut.conj h).injective]
  have hk := c.card_QG_eq_four_mul hS
  rw [S.card_QG_eq_card_Q, S.card_Q_eq] at hk
  have hYle := T.card_le_of_commute (A := Y) inf_le_left hYab
  rw [hT, S.width_conjBy, hcardY] at hYle
  have h1 : 2 ^ (1 + 2 * S.width) ≤ 2 ^ 2 * 2 ^ (S.width + 1) := by
    rw [hk]
    exact Nat.mul_le_mul_left _ hYle
  rw [← pow_add] at h1
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
  omega

theorem inf_Qa_le_clPre (hS : IsSThreeAt S.z c.N) :
    S.QG ⊓ S.Qa c.g ≤ S.clPre (commSpace (S.rhoL (c.t_mem_M_of_sThree hS))) := by
  intro y hy
  have := c.inf_Qa_le_center hy
  rwa [(c.sThree_typeA hS).2.2.2] at this

theorem clPre_commSpace_eq (hS : IsSThreeAt S.z c.N) {w : G} (hw : w ∈ S.QG ⊓ S.Qa c.g)
    (hw1 : w ≠ 1) (hwu : w ≠ c.u) :
    S.clPre (commSpace (S.rhoL (c.t_mem_M_of_sThree hS))) =
      zpowers S.z ⊔ (S.QG ⊓ S.Qa c.g) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  set htM := c.t_mem_M_of_sThree hS
  have hU2 := (c.sThree_typeA hS).1
  have hle := c.inf_Qa_le_clPre hS
  set σ := S.rhoL htM with hσ
  set W := S.clSub (S.QG ⊓ S.Qa c.g) with hW
  have hWU : W ≤ commSpace σ := by
    intro v hv
    obtain ⟨y, hy, -, rfl⟩ := S.mem_clSub_iff.mp hv
    exact (S.mem_clPre.mp (hle hy)).2
  have hzQa : S.z ∉ S.Qa c.g := S.z_not_mem_Qa c.hW c.t_ne_z
  have huQQ : c.u ∈ S.QG ⊓ S.Qa c.g := mem_inf.mpr ⟨c.huQ, c.u_mem_Qa⟩
  obtain ⟨hwQ, hwQa⟩ := mem_inf.mp hw
  have ha0 : S.cl c.u ≠ 0 := by
    rw [ne_eq, S.cl_eq_zero_iff c.huQ]
    rintro (h | h)
    · exact c.hu1 h
    · exact c.huz h
  have hb0 : S.cl w ≠ 0 := by
    rw [ne_eq, S.cl_eq_zero_iff hwQ]
    rintro (h | h)
    · exact hw1 h
    · exact hzQa (h ▸ hwQa)
  have hab : S.cl c.u ≠ S.cl w := by
    rw [ne_eq, S.cl_eq_cl_iff c.huQ hwQ]
    rintro (h | h)
    · exact hwu h
    · apply hzQa
      have : S.z = c.u⁻¹ * w := by rw [h]; group
      rw [this]
      exact mul_mem (inv_mem c.u_mem_Qa) hwQa
  have e1 : S.cl c.u + S.cl w ≠ 0 := fun h => hab (by
    rw [add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self] at h
    exact h)
  have e2 : S.cl c.u + S.cl w ≠ S.cl c.u := fun h => hb0 (by simpa using h)
  have e3 : S.cl c.u + S.cl w ≠ S.cl w := fun h => ha0 (by simpa using h)
  have hsub : ({0, S.cl c.u, S.cl w, S.cl c.u + S.cl w} : Set S.Qt) ⊆ W := by
    rintro v (rfl | rfl | rfl | rfl)
    · exact W.zero_mem
    · exact S.cl_mem_clSub huQQ c.huQ
    · exact S.cl_mem_clSub hw hwQ
    · exact W.add_mem (S.cl_mem_clSub huQQ c.huQ) (S.cl_mem_clSub hw hwQ)
  have h4 : ({0, S.cl c.u, S.cl w, S.cl c.u + S.cl w} : Set S.Qt).ncard = 4 := by
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
  have hWeq : W = commSpace σ := by
    refine SetLike.coe_set_eq.mp (Set.eq_of_subset_of_ncard_le
      (SetLike.coe_subset_coe.mpr hWU) ?_ (Set.toFinite _))
    rw [hcard, ← h4]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  refine le_antisymm (fun x hx => ?_) (sup_le ?_ hle)
  · obtain ⟨hxQ, hxU⟩ := S.mem_clPre.mp hx
    rw [← hWeq] at hxU
    obtain ⟨y, hy, hyQ, hyx⟩ := S.mem_clSub_iff.mp hxU
    rcases (S.cl_eq_cl_iff hyQ hxQ).mp hyx with rfl | rfl
    · exact mem_sup_right hy
    · exact mul_mem (mem_sup_right hy) (mem_sup_left (mem_zpowers _))
  · rw [zpowers_le]
    exact S.z_mem_clPre _

noncomputable abbrev Ut (hS : IsSThreeAt S.z c.N) : Subgroup G :=
  zpowers c.t ⊔ S.clPre (commSpace (S.rhoL (c.t_mem_M_of_sThree hS)))

theorem t_mem_normalizer_clPre (hS : IsSThreeAt S.z c.N) :
    c.t ∈ normalizer (S.clPre (commSpace (S.rhoL (c.t_mem_M_of_sThree hS))) : Set G) := by
  set htM := c.t_mem_M_of_sThree hS
  have key : ∀ a b : G, a * a = 1 → a * (a * b * a⁻¹) * a⁻¹ = b := fun a b ha => by
    rw [show a * (a * b * a⁻¹) * a⁻¹ = (a * a) * b * (a * a)⁻¹ by group, ha]
    group
  have hfwd : ∀ y ∈ S.clPre (commSpace (S.rhoL htM)),
      c.t * y * c.t⁻¹ ∈ S.clPre (commSpace (S.rhoL htM)) := by
    intro y hy
    obtain ⟨hyQ, hyU⟩ := S.mem_clPre.mp hy
    rw [S.conj_eq_inv_of_cl_mem_commSpace htM c.t_mul_self hyQ hyU]
    exact inv_mem hy
  refine mem_normalizer_iff.mpr fun y => ⟨hfwd y, fun hy => ?_⟩
  have := hfwd _ hy
  rwa [key _ _ c.t_mul_self] at this

theorem conj_mem_Ut_of_mem_QG (hS : IsSThreeAt S.z c.N) {q : G} (hq : q ∈ S.QG) {y : G}
    (hy : y ∈ c.Ut hS) : q * y * q⁻¹ ∈ c.Ut hS := by
  set htM := c.t_mem_M_of_sThree hS
  have e1 : ∀ a b : G, a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := fun a b => by group
  have e2 : ∀ a b : G, a * b * a⁻¹ = (a * b * a⁻¹ * b⁻¹) * b := fun a b => by group
  suffices h : c.Ut hS ≤ (c.Ut hS).comap (MulAut.conj q).toMonoidHom from h hy
  refine sup_le ?_ ?_
  · rw [zpowers_le, mem_comap]
    change q * c.t * q⁻¹ ∈ c.Ut hS
    have h1 : c.t * q⁻¹ * c.t⁻¹ ∈ S.QG := S.conj_mem_QG htM (inv_mem hq)
    have hc : q * c.t * q⁻¹ * c.t⁻¹ ∈ S.clPre (commSpace (S.rhoL htM)) := by
      refine S.mem_clPre.mpr ⟨by rw [e1]; exact mul_mem hq h1, ?_⟩
      rw [e1, S.cl_mul hq h1, ← S.rhoL_cl htM (inv_mem hq), S.cl_inv hq]
      exact mem_commSpace.mpr ⟨S.cl q, by rw [sub_eq_add_vec (ZMod 2), add_comm]⟩
    rw [e2]
    exact mul_mem (mem_sup_right hc) (mem_sup_left (mem_zpowers _))
  · intro x hx
    rw [mem_comap]
    change q * x * q⁻¹ ∈ c.Ut hS
    have hxQ := (S.mem_clPre.mp hx).1
    rw [e2]
    refine mem_sup_right (mul_mem ?_ hx)
    rcases S.commutator_eq_one_or_z hq hxQ with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact S.z_mem_clPre _

theorem conj_mem_Ut_of_swap (hS : IsSThreeAt S.z c.N)
    (hZ : S.clPre (commSpace (S.rhoL (c.t_mem_M_of_sThree hS))) =
      zpowers S.z ⊔ (S.QG ⊓ S.Qa c.g))
    {k : G} (hkz : k * S.z * k⁻¹ = c.t) (hkt : k * c.t * k⁻¹ = S.z) {y : G}
    (hy : y ∈ c.Ut hS) : k * y * k⁻¹ ∈ c.Ut hS := by
  have hQk : S.Qa k = S.Qa c.g := S.Qa_eq_of_conj_eq (by rw [hkz])
  have hQkk : S.Qa (k * k) = S.QG := by
    rw [← S.Qa_one]
    apply S.Qa_eq_of_conj_eq
    rw [show k * k * S.z * (k * k)⁻¹ = k * (k * S.z * k⁻¹) * k⁻¹ by group, hkz, hkt]
    group
  have hQQ : ∀ x ∈ S.QG ⊓ S.Qa c.g, k * x * k⁻¹ ∈ S.QG ⊓ S.Qa c.g := by
    intro x hx
    obtain ⟨hxQ, hxQa⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [← hQk, S.Qa_eq_map] at hxQa
      obtain ⟨x', hx'Q, rfl⟩ := hxQa
      rw [← hQkk, S.Qa_eq_map]
      refine ⟨x', hx'Q, ?_⟩
      change k * k * x' * (k * k)⁻¹ = k * (k * x' * k⁻¹) * k⁻¹
      group
    · rw [← hQk, S.Qa_eq_map]
      exact ⟨x, hxQ, rfl⟩
  suffices h : c.Ut hS ≤ (c.Ut hS).comap (MulAut.conj k).toMonoidHom from h hy
  refine sup_le ?_ ?_
  · rw [zpowers_le, mem_comap]
    change k * c.t * k⁻¹ ∈ c.Ut hS
    rw [hkt]
    exact mem_sup_right (S.z_mem_clPre _)
  · rw [hZ]
    refine sup_le ?_ ?_
    · rw [zpowers_le, mem_comap]
      change k * S.z * k⁻¹ ∈ c.Ut hS
      rw [hkz]
      exact mem_sup_left (mem_zpowers _)
    · intro x hx
      rw [mem_comap]
      change k * x * k⁻¹ ∈ c.Ut hS
      have : k * x * k⁻¹ ∈ S.clPre (commSpace (S.rhoL (c.t_mem_M_of_sThree hS))) := by
        rw [hZ]
        exact mem_sup_right (hQQ x hx)
      exact mem_sup_right this

theorem isHSet_of_not_inf_le (hS : IsSThreeAt S.z c.N) {w : G} (hw : w ∈ S.QG ⊓ S.Qa c.g)
    (hw1 : w ≠ 1) (hwu : w ≠ c.u) : S.IsHSet (S.QG ⊔ S.Qa c.g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := c.clPre_commSpace_eq hS hw hw1 hwu
  set T := S.conjBy c.g with hT
  obtain ⟨h, -, hhz, hht⟩ := c.exists_swap hS
  have hQah : S.Qa h = S.Qa c.g := S.Qa_eq_of_conj_eq (by rw [hhz])
  have key : ∀ a b : G, a⁻¹ * (a * b * a⁻¹) * a⁻¹⁻¹ = b := fun a b => by group
  have hQn : S.QG ≤ normalizer (c.Ut hS : Set G) := fun q hq => mem_normalizer_iff.mpr fun y =>
    ⟨c.conj_mem_Ut_of_mem_QG hS hq, fun hy => by
      have := c.conj_mem_Ut_of_mem_QG hS (inv_mem hq) hy
      rwa [key] at this⟩
  have hhn : h ∈ normalizer (c.Ut hS : Set G) := mem_normalizer_iff.mpr fun y =>
    ⟨c.conj_mem_Ut_of_swap hS hZ hhz hht, fun hy => by
      have := c.conj_mem_Ut_of_swap hS hZ (k := h⁻¹) (by rw [← hht]; exact key h c.t)
        (by rw [← hhz]; exact key h S.z) hy
      rwa [key] at this⟩
  have hQgn : S.Qa c.g ≤ normalizer (c.Ut hS : Set G) := by
    rw [← hQah, S.Qa_eq_map]
    rintro _ ⟨q, hq, rfl⟩
    exact mul_mem (mul_mem hhn (hQn hq)) (inv_mem hhn)
  refine ⟨le_sup_left, pCore_ne_bot_of (X := c.Ut hS) ?_ ?_ ?_ ?_,
    fun hle => S.Qa_not_le_M c.hgM (le_sup_right.trans hle)⟩
  · exact sup_le (zpowers_le.mpr (mem_sup_right T.z_mem_QG))
      ((S.clPre_le_QG _).trans le_sup_left)
  · intro x hx y hy
    exact (mem_normalizer_iff.mp ((sup_le hQn hQgn) hx) y).mp hy
  · refine IsPGroup.to_sup_of_normal_right' (T.isPGroup_QG.to_le (zpowers_le.mpr T.z_mem_QG))
      (S.isPGroup_QG.to_le (S.clPre_le_QG _)) ?_
    rw [zpowers_le]
    exact c.t_mem_normalizer_clPre hS
  · intro h0
    have : S.z ∈ c.Ut hS := mem_sup_right (S.z_mem_clPre _)
    rw [h0, mem_bot] at this
    exact S.z_ne_one this

end SixThreeCtx

end Setting

namespace S14

theorem sixThreeStmt_of (h22 : AschbacherTwoTwoStmt) :
    ∀ (G : Type) [Group G] [Finite G] (S : Setting G), 3 ≤ S.width →
      (∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) →
      (∀ t ∈ S.QG, orderOf t = 2 → S.ZInOTwo t) →
      (∃ g : G, g ∉ S.M ∧ S.QG ⊓ S.Qa g ≠ ⊥) →
        ∃ H : Subgroup G, S.IsHSet H := by
  intro G _ _ S hn hW hO ⟨g₀, hg₀M, hg₀⟩
  obtain ⟨c⟩ := S.exists_sixThreeCtx (by omega) hW hO hg₀M hg₀
  rcases c.twoTwo h22 with hS | hA
  · by_cases hQQ : ∀ w ∈ S.QG ⊓ S.Qa c.g, w = 1 ∨ w = c.u
    · exact (c.false_of_inf_le hn hS hQQ).elim
    · push Not at hQQ
      obtain ⟨w, hw, hw1, hwu⟩ := hQQ
      exact ⟨_, c.isHSet_of_not_inf_le hS hw hw1 hwu⟩
  · exact (c.false_of_aFive hA).elim

end S14

end CFSG.LargeExtraspecial
