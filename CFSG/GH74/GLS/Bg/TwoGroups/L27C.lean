module

public import CFSG.GH74.GLS.Bg.TwoGroups.L27B
public import CFSG.GH74.GLS.Bg.TwoGroups.L26B
public import CFSG.GH74.GLS.Bg.TwoGroups.L26K2
public import CFSG.GH74.GLS.Bg.TwoGroups.L26K3
public import CFSG.GH74.GLS.Bg.TwoGroups.L26S

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L27

open L26

variable {T : Type} [Group T] {t : T} {α : MulAut T}

theorem commAut_normal (α : MulAut T) : (commAut α).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    have h1 : (y * g⁻¹)⁻¹ * α (y * g⁻¹) ∈ commAut α := Subgroup.subset_closure ⟨_, rfl⟩
    have h2 : (g⁻¹)⁻¹ * α g⁻¹ ∈ commAut α := Subgroup.subset_closure ⟨_, rfl⟩
    have h3 := mul_mem h1 (inv_mem h2)
    have e : (y * g⁻¹)⁻¹ * α (y * g⁻¹) * ((g⁻¹)⁻¹ * α g⁻¹)⁻¹ = g * (y⁻¹ * α y) * g⁻¹ := by
      simp only [map_mul, map_inv]
      group
    rw [e] at h3
    exact h3
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact inv_mem hx

variable [Finite T]

theorem commAut_sup (h : Hyp7 T t α) : commAut α ⊔ Subgroup.zpowers t = ⊤ := by
  obtain ⟨E, cfg⟩ := exists_E h
  rw [eq_top_iff]
  intro g _
  have hg : g⁻¹ * α g ∈ commAut α := Subgroup.subset_closure ⟨g, rfl⟩
  obtain ⟨s, hs, hαs⟩ := exists_fixed_coset3 h.p2 α 1 (by rw [pow_one]; exact h.a3) (commAut α)
    (commAut_invariant α) g hg
  have hsmem : s ∈ Subgroup.zpowers t := by
    rcases cfg.fixed s hαs with h1 | h1
    · rw [h1]
      exact one_mem _
    · rw [h1]
      exact Subgroup.mem_zpowers t
  have : g = s * (g⁻¹ * s)⁻¹ := by group
  rw [this]
  exact mul_mem (Subgroup.mem_sup_right hsmem) (inv_mem (Subgroup.mem_sup_left hs))

theorem commAut_inf (h : Hyp7 T t α) : commAut α ⊓ Subgroup.zpowers t = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxQ, hxz⟩ := Subgroup.mem_inf.mp hx
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.t2) h.t1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxz
  have hmod : t ^ (k % 2) = t ^ k := by
    have := zpow_mod_orderOf t k
    rw [hord] at this
    simpa using this
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [h0, zpow_zero, hk] at hmod
    rw [← hmod]
    exact one_mem _
  · exfalso
    rw [h1, zpow_one, hk] at hmod
    rw [← hmod] at hxQ
    exact key7' h hxQ

theorem inY_commAut (h : Hyp7 T t α) : InY ↥(commAut α) := by
  classical
  obtain ⟨E, cfg⟩ := exists_E h
  have hnot : t ∉ commAut α := key7' h
  have hQn : (commAut α).Normal := commAut_normal α
  set Q := commAut α with hQ
  have hEQ : ∀ e ∈ E, e ∈ Q := by
    let φ : ↥E → ↥E := fun c => ⟨c⁻¹ * α c, mul_mem (inv_mem c.2) (cfg.Einv c c.2)⟩
    have hφ : Function.Injective φ := by
      intro c d hcd
      have h1 : (c : T)⁻¹ * α c = (d : T)⁻¹ * α d := congrArg Subtype.val hcd
      have e1 : α (c : T) = c * ((d : T)⁻¹ * α d) := by
        rw [← h1]
        group
      have hw : α ((c : T) * (d : T)⁻¹) = (c : T) * (d : T)⁻¹ := by
        rw [map_mul, map_inv, e1]
        group
      have hwE : (c : T) * (d : T)⁻¹ ∈ E := mul_mem c.2 (inv_mem d.2)
      exact Subtype.ext (mul_inv_eq_one.mp (cfg.Efpf _ hwE hw))
    intro e he
    obtain ⟨c, hc⟩ := Finite.surjective_of_injective hφ ⟨e, he⟩
    have h1 : (c : T)⁻¹ * α c = e := congrArg Subtype.val hc
    rw [← h1]
    exact Subgroup.subset_closure ⟨c, rfl⟩
  have hQC : ∀ q ∈ Q, t * q = q * t → q ∈ E := by
    intro q hq hqt
    rcases cfg.CE q hqt with h1 | ⟨e, he, rfl⟩
    · exact h1
    · exfalso
      apply hnot
      have : t = (t * e) * e⁻¹ := by group
      rw [this]
      exact mul_mem hq (inv_mem (hEQ e he))
  have _ := hQn
  let τ : MulAut ↥Q := MulAut.conjNormal t
  let αQ : MulAut ↥Q := L23.xRes α Q (commAut_invariant α)
  have hτ : ∀ q : ↥Q, τ q = q ↔ t * (q : T) = (q : T) * t := by
    intro q
    constructor
    · intro hq
      have := congrArg Subtype.val hq
      rw [MulAut.conjNormal_apply] at this
      calc t * (q : T) = (t * (q : T) * t⁻¹) * t := by group
        _ = (q : T) * t := by rw [this]
    · intro hq
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      calc t * (q : T) * t⁻¹ = (q : T) * t * t⁻¹ := by rw [hq]
        _ = q := by group
  have hmemE : ∀ q : ↥Q, q ∈ fixSub τ ↔ (q : T) ∈ E := by
    intro q
    constructor
    · intro hq
      exact hQC q q.2 ((hτ q).mp hq)
    · intro hq
      exact (hτ q).mpr (cfg.EC _ hq)
  have hEcard : Nat.card (fixSub τ) = 4 := by
    rw [← cfg.Ecard]
    exact Nat.card_congr
      { toFun := fun q => ⟨(q : ↥Q), (hmemE q.1).mp q.2⟩
        invFun := fun e => ⟨⟨e, hEQ e e.2⟩, (hmemE ⟨e, hEQ e e.2⟩).mpr e.2⟩
        left_inv := fun q => rfl
        right_inv := fun e => rfl }
  have hαQ3 : αQ ^ 3 = 1 := by
    refine MulEquiv.ext fun q => ?_
    apply Subtype.ext
    rw [L23.xRes_pow, h.a3]
    rfl
  have hcomm : αQ * τ = τ * αQ := by
    refine MulEquiv.ext fun q => ?_
    apply Subtype.ext
    show α (t * (q : T) * t⁻¹) = t * α (q : T) * t⁻¹
    rw [map_mul, map_mul, map_inv, h.αt]
  have cfgQ : Cfg ↥Q αQ τ (fixSub τ) :=
    { p2 := h.p2.to_subgroup Q
      a3 := hαQ3
      t2 := by rw [← map_mul, h.t2, map_one]
      comm := hcomm
      hE := fun g => Iff.rfl
      E2 := fun e he => Subtype.ext (cfg.E2 _ ((hmemE e).mp he))
      Ec := fun a ha b hb => Subtype.ext (cfg.Ec _ ((hmemE a).mp ha) _ ((hmemE b).mp hb))
      Ecard := hEcard
      Efpf := fun e he hfix => Subtype.ext
        (cfg.Efpf _ ((hmemE e).mp he) (congrArg Subtype.val hfix)) }
  exact Cfg.main SylSL3_4 SylSU3_4 sfacts_SylSL3_4 sfacts_SylSU3_4 k2_card h64_prop k3_prop
    (Nat.card ↥Q) ↥Q rfl αQ τ (fixSub τ) cfgQ

end L27

theorem iv2_2_7 : IV2_2_7 := by
  intro T _ _ hp t ht hCiso α hα1 hαo hαt
  obtain ⟨e⟩ := hCiso
  obtain ⟨n, hn⟩ := hαo
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, pow_two] at this
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht
    omega
  have hCcard : Nat.card (Subgroup.centralizer ({t} : Set T)) = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hCab : ∀ a b : T, t * a = a * t → t * b = b * t → a * b = b * a := by
    intro a b ha hb
    have ha' : a ∈ Subgroup.centralizer ({t} : Set T) := L27.mem_cent.mpr ha
    have hb' : b ∈ Subgroup.centralizer ({t} : Set T) := L27.mem_cent.mpr hb
    have h1 : e (⟨a, ha'⟩ * ⟨b, hb'⟩) = e (⟨b, hb'⟩ * ⟨a, ha'⟩) := by
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val (e.injective h1)
  have hC2 : ∀ c : T, t * c = c * t → c * c = 1 := by
    intro c hc
    have hc' : c ∈ Subgroup.centralizer ({t} : Set T) := L27.mem_cent.mpr hc
    have h1 : (⟨c, hc'⟩ : ↥(Subgroup.centralizer ({t} : Set T))) * ⟨c, hc'⟩ = 1 := by
      apply e.injective
      rw [map_mul, map_one]
      exact (by decide : ∀ x : E2 3, x * x = 1) _
    exact congrArg Subtype.val h1
  have hα3n : α ^ (3 ^ n) = 1 := by
    rw [← hn]
    exact pow_orderOf_eq_one α
  have hα3 : α ^ 3 = 1 :=
    L27.alpha_cube hp t ht2 (le_of_eq hCcard) α n hα3n hαt
  have hyp : L27.Hyp7 T t α := ⟨hp, ht2, ht1, hCab, hC2, hCcard, hα3, hα1, hαt⟩
  exact ⟨L27.commAut_normal α, L27.commAut_inf hyp, L27.commAut_sup hyp, L27.inY_commAut hyp⟩

end CFSG.GH74.GLS.Bg.TwoGroups
