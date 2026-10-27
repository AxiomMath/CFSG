module

public import CFSG.GH74.Uniqueness.Section17Final
public import CFSG.GH74.Uniqueness.Section128Index

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

section MZero

theorem LData.mo_sq {c : Ctx12 Z M} {n i : ℕ} (h : LData c n i) :
    ∀ x ∈ zHull Z M, x * x = 1 := by
  intro x hx
  have := h.m_abelian.2 x hx
  rwa [pow_two] at this

theorem ZDSetup.centralizer_zHull_le (S : ZDSetup X Z M) (c : Ctx12 Z M) :
    centralizer (zHull Z M : Set X) ≤ M := by
  intro g hg
  have hz : c.z ∈ zHull Z M := subset_closure ⟨c.hz, c.hzM⟩
  apply S.prodDisc.centralizer_le_of_mem c.hz c.hzM
  rw [mem_centralizer_singleton_iff]
  exact (mem_centralizer_iff.mp hg c.z hz).symm

end MZero

section KReg

variable {c : Ctx12 Z M} {n : ℕ}

theorem LData.K_trans
    (hZ : IsInvariantInvolutionSet Z) (h : LData c n 1) :
    ∀ a ∈ zHull Z M, a ≠ 1 → ∀ b ∈ zHull Z M, b ≠ 1 → ∃ k ∈ c.D ⊓ c.L, k * a * k⁻¹ = b := by
  obtain ⟨Q, hQ⟩ := h.borel
  have hc := h.benderCore hZ hQ
  have hR := h.map_subtype_rootCenter hZ hQ
  have hK := h.map_subtype_commutator_cartan hZ hQ
  intro a ha ha1 b hb hb1
  rw [← hR] at ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  have ha1' : a' ≠ 1 := fun h1 => ha1 (by rw [h1]; rfl)
  have hb1' : b' ≠ 1 := fun h1 => hb1 (by rw [h1]; rfl)
  obtain ⟨d, ⟨hd, hdd⟩, -⟩ := hc.existsUnique_commutator_conj ha' ha1' hb' hb1'
  refine ⟨((d⁻¹ : c.L) : X), ?_, ?_⟩
  · rw [← h.k_eq', ← hK]
    exact ⟨d⁻¹, inv_mem hd, rfl⟩
  · rw [hdd]
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]

theorem LData.K_fpf
    (hZ : IsInvariantInvolutionSet Z) (h : LData c n 1) :
    ∀ k ∈ c.D ⊓ c.L, k ≠ 1 → ∀ x ∈ zHull Z M, k * x = x * k → x = 1 := by
  obtain ⟨Q, hQ⟩ := h.borel
  have hc := h.benderCore hZ hQ
  have hR := h.map_subtype_rootCenter hZ hQ
  have hK := h.map_subtype_commutator_cartan hZ hQ
  intro k hk hk1 x hx hkx
  by_contra hx1
  rw [← h.k_eq', ← hK] at hk
  obtain ⟨d, hd, rfl⟩ := hk
  rw [← hR] at hx
  obtain ⟨x', hx', rfl⟩ := hx
  have hx1' : x' ≠ 1 := fun h1 => hx1 (by rw [h1]; rfl)
  obtain ⟨d₀, -, huniq⟩ := hc.existsUnique_commutator_conj hx' hx1' hx' hx1'
  have hcomm : d * x' = x' * d := Subtype.ext hkx
  have h1 : d = d₀ := huniq d ⟨hd, by rw [mul_assoc, ← hcomm, inv_mul_cancel_left]⟩
  have h2 : (1 : c.L) = d₀ := huniq 1 ⟨one_mem _, by simp⟩
  apply hk1
  change ((d : c.L) : X) = 1
  rw [h1, ← h2]
  rfl

end KReg

section LJ

variable {c : Ctx12 Z M} {n i : ℕ}

theorem LData.L_inf_J (h : LData c n i) : c.L ⊓ centralizer (c.L : Set X) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxL, hxC⟩ := mem_inf.mp hx
  have hc : (⟨x, hxL⟩ : c.L) ∈ center ↥c.L := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.mp hxC g g.2)
  rw [h.center_eq_bot, mem_bot] at hc
  exact mem_bot.mpr (congrArg Subtype.val hc)

theorem LData.D_le_N (h : LData c n i) : c.D ≤ normalizer (c.L : Set X) := by
  intro d hd
  have : d ∈ ((normalizer (c.L : Set X) : Subgroup X) : Set X) := by
    rw [h.normalizer_eq]
    exact ⟨1, one_mem _, d, hd, one_mul d⟩
  exact this

theorem LData.N_eq (h : LData c n i) :
    ∀ g ∈ normalizer (c.L : Set X), ∃ l ∈ c.L, ∃ d ∈ c.D, g = l * d := by
  intro g hg
  have : g ∈ ((normalizer (c.L : Set X) : Subgroup X) : Set X) := hg
  rw [h.normalizer_eq] at this
  obtain ⟨l, hl, d, hd, hld⟩ := this
  exact ⟨l, hl, d, hd, hld.symm⟩

theorem LData.map_sylow_eq_zHull
    (hZ : IsInvariantInvolutionSet Z) {c : Ctx12 Z M} {n : ℕ}
    (h : LData c n 1) {Q : Sylow 2 c.L}
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    (Q : Subgroup c.L).map c.L.subtype = zHull Z M := by
  have hc := h.benderCore hZ hQ
  have hRQ : Bender.rootCenter (Q : Subgroup c.L) = (Q : Subgroup c.L) := by
    refine eq_of_le_of_card_ge (Bender.rootCenter_le _) ?_
    rw [hc.card_eq, hc.card_center, pow_one]
  rw [← hRQ]
  exact h.map_subtype_rootCenter hZ hQ

theorem LData.NM_eq
    (hZ : IsInvariantInvolutionSet Z) {c : Ctx12 Z M} {n : ℕ} (h : LData c n 1) :
    ∀ g ∈ M, g ∈ normalizer (c.L : Set X) → ∃ m ∈ zHull Z M, ∃ d ∈ c.D, g = m * d := by
  intro g hgM hgN
  obtain ⟨Q, hQ⟩ := h.borel
  have hmem : g ∈ ((M ⊓ normalizer (c.L : Set X) : Subgroup X) : Set X) := mem_inf.mpr ⟨hgM, hgN⟩
  rw [h.nM_eq_sylow hQ, h.map_sylow_eq_zHull hZ hQ] at hmem
  obtain ⟨m, hm, d, hd, hmd⟩ := hmem
  exact ⟨m, hm, d, hd, hmd.symm⟩

end LJ

section Prop131

variable {c : Ctx12 Z M} {n i : ℕ}

omit [Finite X] in
theorem conj_mem_cenHull (hZ : IsInvariantInvolutionSet Z) {u x : X} (g : X)
    (hx : x ∈ cenHull Z u) : g * x * g⁻¹ ∈ cenHull Z (g * u * g⁻¹) := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    refine subset_closure ⟨?_, ?_⟩
    · have := hZ.2 y hy.1 g⁻¹
      rwa [inv_inv] at this
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      have hyu : y * u = u * y := mem_centralizer_singleton_iff.mp hy.2
      calc g * y * g⁻¹ * (g * u * g⁻¹) = g * (y * u) * g⁻¹ := by group
        _ = g * (u * y) * g⁻¹ := by rw [hyu]
        _ = g * u * g⁻¹ * (g * y * g⁻¹) := by group
  | one => simp
  | mul a b _ _ ha hb =>
    have := mul_mem ha hb
    convert this using 1
    group
  | inv a _ ha =>
    have := inv_mem ha
    convert this using 1
    group

theorem ZDSetup.exists_inv_J (h131 : Prop131Stmt Z M) (h : LData c n i) :
    ∃ u ∈ c.D, orderOf u = 2 ∧ u ∈ centralizer (c.L : Set X) := by
  obtain ⟨u, hu, hu2⟩ := Simple.exists_mem_orderOf_eq_two_of_even_card c.hD
  refine ⟨u, hu, hu2, ?_⟩
  have hLu := h131 c n i h u hu hu2
  rw [mem_centralizer_iff]
  intro l hl
  rw [← hLu] at hl
  exact mem_centralizer_singleton_iff.mp (Cor713.zHull_le _ hl)

theorem ZDSetup.inv_conj_normalizer (S : ZDSetup X Z M) (h131 : Prop131Stmt Z M)
    (h : LData c n i) {u : X} (hu : u ∈ c.D) (hu2 : orderOf u = 2) {g : X}
    (hg : g * u * g⁻¹ ∈ c.D) : g ∈ normalizer (c.L : Set X) := by
  have hLu := h131 c n i h u hu hu2
  have hu2' : orderOf (g * u * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hu2
  have hLv := h131 c n i h _ hg hu2'
  rw [mem_normalizer_iff]
  intro l
  constructor
  · intro hl
    rw [← hLu] at hl
    have := conj_mem_cenHull S.invariant g hl
    rwa [hLv] at this
  · intro hl
    rw [← hLv] at hl
    have := conj_mem_cenHull S.invariant g⁻¹ hl
    have e1 : g⁻¹ * (g * l * g⁻¹) * g⁻¹⁻¹ = l := by group
    have e2 : g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u := by group
    rw [e1, e2, hLu] at this
    exact this

theorem ZDSetup.ncard_omega_15
    (S : ZDSetup X Z M) (h12 : Sec12Results Z M)
    (h131 : Prop131Stmt Z M) (h : LData c n 1) :
    (omega M).ncard = (2 ^ n) ^ 3 + 1 ∧ Nat.card M = 2 ^ (3 * n) * Nat.card c.D := by
  have hΩ : (omega M).ncard = (2 ^ n) ^ 3 + 1 := by
    rcases h12.l1210 c n 1 h with ⟨-, hΩ, -⟩ | ⟨h2, -⟩ | ⟨-, -, hall, -⟩
    · exact hΩ
    · exact absurd h2 (by norm_num)
    · exfalso
      obtain ⟨u, hu, hu2, -⟩ := ZDSetup.exists_inv_J h131 h
      exact (hall u hu hu2).1.ne' (h131 c n 1 h u hu hu2)
  refine ⟨hΩ, ?_⟩
  have h1 := S.ncard_omega_sub_one_mul_card c.htM
  rw [hΩ, Nat.add_sub_cancel, ← pow_mul, mul_comm n 3] at h1
  exact h1.symm

end Prop131

section OTwo

omit [Finite X] in
theorem oTwoIn_isPGroup (H : Subgroup X) : IsPGroup 2 (oTwoIn H) :=
  (pCore_isPGroup (p := 2) (G := ↥H)).map H.subtype

omit [Finite X] in
theorem le_oTwoIn {H N : Subgroup X} (hNH : N ≤ H)
    (hn : ∀ g ∈ H, ∀ x ∈ N, g * x * g⁻¹ ∈ N) (hp : IsPGroup 2 N) : N ≤ oTwoIn H := by
  have hnorm : (N.subgroupOf H).Normal :=
    ⟨fun x hx g => mem_subgroupOf.mpr (hn g g.2 x (mem_subgroupOf.mp hx))⟩
  have hp' : IsPGroup 2 (N.subgroupOf H) := hp.comap_subtype
  have hle : N.subgroupOf H ≤ pCore 2 ↥H := le_sSup ⟨hnorm, hp'⟩
  intro x hx
  exact ⟨⟨x, hNH hx⟩, hle (mem_subgroupOf.mpr hx), rfl⟩

theorem ZDSetup.oTwoIn_comm
    (S : ZDSetup X Z M) {c : Ctx12 Z M} {n i : ℕ} (h : LData c n i) :
    ∀ v ∈ oTwoIn M, ∀ x ∈ zHull Z M, v * x = x * v := by
  intro v hv x hx
  by_cases hx1 : x = 1
  · rw [hx1, mul_one, one_mul]
  have hxZ : x ∈ Z := by
    have : x ∈ zM Z M := by
      rw [h.zM_eq]
      exact ⟨hx, hx1⟩
    exact this.1
  have hxM : x ∈ M := Cor713.zHull_le M hx
  obtain ⟨-, T, hxT, hTx⟩ := S.theorem1_unconditional.2.2.2 x hxZ
  have hTM : (T : Subgroup X) ≤ M := fun s hs =>
    S.prodDisc.centralizer_le_of_mem hxZ hxM (mem_centralizer_singleton_iff.mpr (hTx s hs))
  have hVn : (T : Subgroup X) ≤ normalizer (oTwoIn M : Set X) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact oTwoIn_conj_mem M (hTM hs) hy
    · intro hy
      have := oTwoIn_conj_mem M (M.inv_mem (hTM hs)) hy
      have e : s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ = y := by group
      rwa [e] at this
  have hsup : IsPGroup 2 ↥(oTwoIn M ⊔ (T : Subgroup X)) :=
    IsPGroup.to_sup_of_normal_left' (oTwoIn_isPGroup M) T.isPGroup' hVn
  have hVT : oTwoIn M ≤ (T : Subgroup X) := by
    have := T.is_maximal' hsup le_sup_right
    rw [← this]
    exact le_sup_left
  exact hTx v (hVT hv)

end OTwo

section Four

theorem ZDSetup.closure_odd_M
    (S : ZDSetup X Z M) :
    closure {y : X | y ∈ M ∧ Odd (orderOf y)} = M := by
  rw [S.closure_odd_eq_iff]
  have hsimp : IsSimpleGroup X := S.theorem1_unconditional.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (closure {y : X | Odd (orderOf y)}) with
    hbot | htop
  · exfalso
    obtain ⟨t, ht, htM⟩ := S.exists_mem_not_mem
    obtain ⟨z, hz, hzM⟩ := S.exists_mem_inter
    have hnc : ¬ ∀ a b : X, a * b = b * a := by
      intro hall
      apply htM
      refine (S.prodDisc.2.2.1 z hz hzM t).mp ?_
      rw [hall t⁻¹ z, mul_assoc, inv_mul_cancel, mul_one]
      exact hzM
    obtain ⟨x, hxodd, hx1⟩ := exists_odd_ne_one_of_simple hnc
    have hxmem : x ∈ closure {y : X | Odd (orderOf y)} := subset_closure hxodd
    rw [hbot] at hxmem
    exact hx1 (mem_bot.mp hxmem)
  · exact htop

theorem ZDSetup.conj_D_15 (S : ZDSetup X Z M) (h12 : Sec12Results Z M) {c : Ctx12 Z M}
    {n i : ℕ} (h : LData c n i) :
    ∀ s ∈ M, orderOf s = 2 → s ∉ zHull Z M → ∃ m ∈ M, m⁻¹ * s * m ∈ c.D := by
  intro s hsM hs2 hsMo
  obtain ⟨ha, -, hb⟩ := h12.l1211 c n i h
  have hsZ : s ∉ Z := by
    intro hsZ
    have : s ∈ zM Z M := ⟨hsZ, hsM⟩
    rw [h.zM_eq] at this
    exact hsMo this.1
  have hnc : ¬ IsCentralInvolution s := fun hc => hsZ ((ha s hs2).mp hc)
  obtain ⟨u, hu, -, hsu⟩ := hb s hs2 hnc
  obtain ⟨g, hg⟩ := isConj_iff.mp hsu
  have hp : IsPGroup 2 (zpowers s) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hs2, pow_one]
  have hgs : g⁻¹⁻¹ * s * g⁻¹ ∈ M := by
    rw [inv_inv, hg]
    exact (mem_inf.mp hu).1
  obtain ⟨m, hm, hms⟩ := S.exists_mem_conj_of_isPGroup hsM hp hgs
  refine ⟨m, hm, ?_⟩
  rw [hms, inv_inv, hg]
  exact hu

end Four

end CFSG.GH74.Uniqueness
