module

public import CFSG.CGT.PushingUpLit.A78L3.TJ
public import CFSG.CGT.PushingUpLit.A78T2.Data
public import CFSG.CGT.PushingUpLit.A78Sp4.F410

public section

namespace CFSG.CGT.PushingUpLit.A78L3

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.CGT.PushingUpLit.A78T2 (T2Base)
open CFSG.ABGLocalTools
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G]

theorem card_le_two_mul_inf [Finite G] {E H : Subgroup G} {a : G} (ha : a ∈ E)
    (hmul : ∀ x ∈ E, x ∉ H → x * a ∈ H) : Nat.card E ≤ 2 * Nat.card ↥(E ⊓ H) := by
  classical
  let f : ↥E → ↥(E ⊓ H) × Bool := fun x =>
    if hx : (x : G) ∈ H then (⟨x, x.2, hx⟩, false)
    else (⟨x * a, mul_mem x.2 ha, hmul x x.2 hx⟩, true)
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : (x : G) ∈ H <;> by_cases hy : (y : G) ∈ H <;>
      simp only [f, hx, hy, ↓reduceDIte, Prod.mk.injEq] at hxy
    · exact Subtype.ext (congrArg (fun z : ↥(E ⊓ H) => (z : G)) hxy.1)
    · exact absurd hxy.2 (by decide)
    · exact absurd hxy.2 (by decide)
    · exact Subtype.ext (mul_right_cancel (congrArg (fun z : ↥(E ⊓ H) => (z : G)) hxy.1))
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  linarith

theorem mem_normalizer_of_conj_le [Finite G] {x : G} {H : Subgroup G}
    (h : ∀ t ∈ H, x * t * x⁻¹ ∈ H) : x ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h y hy, fun hy => ?_⟩
  have hinj : Function.Injective (fun t : ↥H => (⟨x * t * x⁻¹, h t t.2⟩ : ↥H)) :=
    fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)
  obtain ⟨b, hb⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨_, hy⟩
  have h1 : x * b * x⁻¹ = x * y * x⁻¹ := congrArg Subtype.val hb
  have e1 : y = b := (mul_left_cancel (mul_right_cancel h1)).symm
  rw [e1]
  exact b.2

theorem cj_injective {g : G} {H K : Subgroup G} (h : cj g H = cj g K) : H = K := by
  have h1 := congrArg (cj g⁻¹) h
  rwa [cj_cj, cj_cj, inv_mul_cancel, cj_eq_self_of_mem (Subgroup.one_mem _),
    cj_eq_self_of_mem (Subgroup.one_mem _)] at h1

end Helpers

structure L3Pair (G : Type) [Group G] [Finite G] (L₁ L₂ V W T : Subgroup G) (e : ℕ) : Prop where
  side₁ : L3Side G L₁ V W T e
  side₂ : L3Side G L₂ W V T e
  sylow₁ : IsSylowOf 2 T (Subgroup.normalizer (V : Set G))
  sylow₂ : IsSylowOf 2 T (Subgroup.normalizer (W : Set G))

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.l3Pair {G : Type} [Group G] [Finite G]
    {L₁ L₂ T : Subgroup G} {e : ℕ} (h : A78Cfg G L₁ L₂ T e)
    (hZ : oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G) = ⊥) :
    L3Pair G L₁ L₂ (oTwoIn (L₁ ⊔ T)) (oTwoIn (L₂ ⊔ T)) T e :=
  ⟨h.l3Side₁ hZ, h.l3Side₂ hZ, h.hyg.sylow₁, h.hyg.sylow₂⟩

namespace L3Pair

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W T : Subgroup G} {e : ℕ}
  (P : L3Pair G L₁ L₂ V W T e)

include P

theorem two_le : 2 ≤ e := P.side₁.two_le

theorem ne_VW : V ≠ W := fun h => P.side₁.jst.not_le_V (h ▸ le_rfl)

theorem two_mul_lt : 2 * 2 ^ e < 2 ^ (2 * e) := by
  have h2 := P.two_le
  have h4 : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h2
  rw [two_mul e, pow_add]
  nlinarith

theorem caseA {E : Subgroup G} (hET : E ≤ T) (hE : ElemAb2 E) (hEJ : ¬ E ≤ V ⊔ W) :
    Nat.card E ≤ 2 * 2 ^ e := by
  obtain ⟨D₁⟩ := P.side₁.nat
  obtain ⟨D₂⟩ := P.side₂.nat
  obtain ⟨a, haE, haJ⟩ : ∃ a ∈ E, a ∉ V ⊔ W := by
    by_contra hcon
    push Not at hcon
    exact hEJ hcon
  have haa : a * a = 1 := (hE a haE a haE).2
  have h1 := card_le_two_mul_inf haE fun x hx hxJ =>
    P.side₁.mul_mem_J_of_involutions D₁ (hET hx) hxJ (hE x hx x hx).2 (hET haE) haJ haa
  have hEJ' : E ⊓ (V ⊔ W) ≤ V ⊔ W := inf_le_right
  rcases P.side₁.jst.elemAbelian_le hEJ' (fun x hx => (hE x hx.1 x hx.1).2) with hV | hW
  · have hle : E ⊓ (V ⊔ W) ≤ V ⊓ Subgroup.centralizer ({a} : Set G) := fun x hx =>
      ⟨hV hx, Subgroup.mem_centralizer_singleton_iff.2 (hE x hx.1 a haE).1⟩
    have h2 := Subgroup.card_le_of_le hle
    rw [P.side₁.card_CV D₁ (hET haE) haJ haa] at h2
    omega
  · have haJ' : a ∉ W ⊔ V := by rwa [sup_comm]
    have hle : E ⊓ (V ⊔ W) ≤ W ⊓ Subgroup.centralizer ({a} : Set G) := fun x hx =>
      ⟨hW hx, Subgroup.mem_centralizer_singleton_iff.2 (hE x hx.1 a haE).1⟩
    have h2 := Subgroup.card_le_of_le hle
    rw [P.side₂.card_CV D₂ (hET haE) haJ' haa] at h2
    omega

theorem card_le_of_le_T {E : Subgroup G} (hET : E ≤ T) (hE : ElemAb2 E) :
    Nat.card E ≤ 2 ^ (2 * e) := by
  by_cases hEJ : E ≤ V ⊔ W
  · have := P.side₁.jst.card_le_of_elemAbelian hEJ fun x hx => (hE x hx x hx).2
    rwa [P.side₁.card_V] at this
  · exact (P.caseA hET hE hEJ).trans P.two_mul_lt.le

theorem eq_of_le_T {E : Subgroup G} (hET : E ≤ T) (hE : ElemAb2 E)
    (hcard : Nat.card E = 2 ^ (2 * e)) : E = V ∨ E = W := by
  by_cases hEJ : E ≤ V ⊔ W
  · exact P.side₁.jst.mem_of_card hEJ (fun x hx => (hE x hx x hx).2) (by rw [P.side₁.card_V, hcard])
  · have := P.caseA hET hE hEJ
    have := P.two_mul_lt
    omega

theorem inf_normalizer_V {S : Subgroup G} (hTS : T ≤ S) (hS : IsPGroup 2 S) :
    S ⊓ Subgroup.normalizer (V : Set G) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact P.sylow₁.eq_of_le (le_inf hTS P.sylow₁.le) inf_le_right (hS.to_le inf_le_left)

theorem inf_normalizer_W {S : Subgroup G} (hTS : T ≤ S) (hS : IsPGroup 2 S) :
    S ⊓ Subgroup.normalizer (W : Set G) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact P.sylow₂.eq_of_le (le_inf hTS P.sylow₂.le) inf_le_right (hS.to_le inf_le_left)

section Sylow

variable {S : Subgroup G} (hTS : T ≤ S) (hS : IsPGroup 2 S)

include hTS hS in
theorem mem_T_of_cj_V {r : G} (hr : r ∈ S) (hrV : cj r V = V) : r ∈ T := by
  rw [← P.inf_normalizer_V hTS hS]
  exact ⟨hr, mem_normalizer_of_cj hrV⟩

theorem cj_V_of_normalizes {r : G} (hrT : ∀ t ∈ T, r * t * r⁻¹ ∈ T) (U : Subgroup G)
    (hU : U = V ∨ U = W) : cj r U = V ∨ cj r U = W := by
  have hUT : U ≤ T := by
    rcases hU with rfl | rfl
    · exact P.side₁.V_le_T
    · exact P.side₁.W_le_T
  have hUel : ElemAb2 U := by
    rcases hU with rfl | rfl
    · exact fun x hx y hy => ⟨(P.side₁.jst.abelian_V x hx y hy).eq, P.side₁.jst.sq_V x hx⟩
    · exact fun x hx y hy => ⟨(P.side₁.jst.abelian_V₂ x hx y hy).eq, P.side₁.jst.sq_V₂ x hx⟩
  have hUc : Nat.card U = 2 ^ (2 * e) := by
    rcases hU with rfl | rfl
    · exact P.side₁.card_V
    · exact P.side₂.card_V
  refine P.eq_of_le_T ?_ (elemAb2_cj hUel r) ((card_cj r U).trans hUc)
  intro x hx
  rw [mem_cj_iff] at hx
  have := hrT _ (hUT hx)
  simpa [mul_assoc] using this

include hTS hS in
theorem swap_of_mem_R {r : G} (hr : r ∈ S) (hrT : ∀ t ∈ T, r * t * r⁻¹ ∈ T) (hrT' : r ∉ T) :
    cj r V = W ∧ cj r W = V := by
  have hV : cj r V = W := by
    rcases P.cj_V_of_normalizes hrT V (Or.inl rfl) with h | h
    · exact absurd (P.mem_T_of_cj_V hTS hS hr h) hrT'
    · exact h
  refine ⟨hV, ?_⟩
  rcases P.cj_V_of_normalizes hrT W (Or.inr rfl) with h | h
  · exact h
  · exact absurd (cj_injective (hV.trans h.symm)) P.ne_VW

include hTS hS in
theorem mul_mem_T_of_R {x a : G} (hx : x ∈ S) (hxT : ∀ t ∈ T, x * t * x⁻¹ ∈ T) (hxT' : x ∉ T)
    (ha : a ∈ S) (haT : ∀ t ∈ T, a * t * a⁻¹ ∈ T) (haT' : a ∉ T) : x * a ∈ T := by
  refine P.mem_T_of_cj_V hTS hS (mul_mem hx ha) ?_
  rw [← cj_cj, (P.swap_of_mem_R hTS hS ha haT haT').1, (P.swap_of_mem_R hTS hS hx hxT hxT').2]

include hTS hS in
theorem caseD {E : Subgroup G} (hES : E ≤ S) (hEN : ∀ x ∈ E, ∀ t ∈ T, x * t * x⁻¹ ∈ T)
    (hE : ElemAb2 E) (hET : ¬ E ≤ T) : Nat.card E ≤ 2 * 2 ^ e := by
  obtain ⟨D₁⟩ := P.side₁.nat
  obtain ⟨a, haE, haT⟩ : ∃ a ∈ E, a ∉ T := by
    by_contra hcon
    push Not at hcon
    exact hET hcon
  have h1 := card_le_two_mul_inf haE fun x hx hxT =>
    P.mul_mem_T_of_R hTS hS (hES hx) (hEN x hx) hxT (hES haE) (hEN a haE) haT
  have hswap := P.swap_of_mem_R hTS hS (hES haE) (hEN a haE) haT
  have hZ : (E ⊓ T) ⊓ (V ⊔ W) ≤ V ⊓ W := by
    have hle : (E ⊓ T) ⊓ (V ⊔ W) ≤ V ⊔ W := inf_le_right
    have hcomm : ∀ x ∈ (E ⊓ T) ⊓ (V ⊔ W), a * x * a⁻¹ = x := fun x hx => by
      rw [(hE a haE x hx.1.1).1]; group
    rcases P.side₁.jst.elemAbelian_le hle (fun x hx => (hE x hx.1.1 x hx.1.1).2) with hV | hW
    · intro x hx
      refine ⟨hV hx, ?_⟩
      have h2 : a * x * a⁻¹ ∈ cj a V := mul_mem_cj a (hV hx)
      rwa [hswap.1, hcomm x hx] at h2
    · intro x hx
      refine ⟨?_, hW hx⟩
      have h2 : a * x * a⁻¹ ∈ cj a W := mul_mem_cj a (hW hx)
      rwa [hswap.2, hcomm x hx] at h2
  have hET' : E ⊓ T ≤ T := inf_le_right
  by_cases hEJ : E ⊓ T ≤ V ⊔ W
  · have h2 : Nat.card ↥(E ⊓ T) ≤ 2 ^ e := by
      have : E ⊓ T ≤ V ⊓ W := fun x hx => hZ ⟨hx, hEJ hx⟩
      exact (Subgroup.card_le_of_le this).trans P.side₁.card_Z.le
    omega
  ·
    obtain ⟨f, hfE, hfJ⟩ : ∃ f ∈ E ⊓ T, f ∉ V ⊔ W := by
      by_contra hcon
      push Not at hcon
      exact hEJ hcon
    have hff : f * f = 1 := (hE f hfE.1 f hfE.1).2
    have h2 := card_le_two_mul_inf (E := E ⊓ T) (H := V ⊔ W) hfE fun x hx hxJ =>
      P.side₁.mul_mem_J_of_involutions D₁ hx.2 hxJ (hE x hx.1 x hx.1).2 hfE.2 hfJ hff
    have h3 : (E ⊓ T) ⊓ (V ⊔ W) ≤ (V ⊓ W) ⊓ Subgroup.centralizer ({f} : Set G) := fun x hx =>
      ⟨hZ hx, Subgroup.mem_centralizer_singleton_iff.2 (hE x hx.1.1 f hfE.1).1⟩
    obtain ⟨z, hz, hzf⟩ := P.side₁.not_centralizes_Z D₁ hfE.2 hfJ
    have hlt : (V ⊓ W) ⊓ Subgroup.centralizer ({f} : Set G) < V ⊓ W := by
      refine lt_of_le_of_ne inf_le_left fun heq => hzf ?_
      have : z ∈ (V ⊓ W) ⊓ Subgroup.centralizer ({f} : Set G) := by rw [heq]; exact hz
      exact (Subgroup.mem_centralizer_singleton_iff.1 this.2).symm
    have h4 : 2 * Nat.card ↥((V ⊓ W) ⊓ Subgroup.centralizer ({f} : Set G)) ≤ 2 ^ e := by
      rw [← P.side₁.card_Z]
      have hidx := Subgroup.relIndex_mul_card (((V ⊓ W) ⊓ Subgroup.centralizer ({f} : Set G)))
        (V ⊓ W)
      rw [inf_eq_left.2 hlt.le] at hidx
      have hne : ((V ⊓ W) ⊓ Subgroup.centralizer ({f} : Set G)).relIndex (V ⊓ W) ≠ 1 := by
        intro h1
        exact hlt.ne (le_antisymm hlt.le (Subgroup.relIndex_eq_one.1 h1))
      have hne0 : ((V ⊓ W) ⊓ Subgroup.centralizer ({f} : Set G)).relIndex (V ⊓ W) ≠ 0 := by
        unfold Subgroup.relIndex
        exact Subgroup.index_ne_zero_of_finite
      rw [← hidx]
      exact Nat.mul_le_mul_right _ (by omega)
    have h5 := Subgroup.card_le_of_le h3
    omega

include hTS hS in
theorem mem_normalizer_T {n : G} (hn : n ∈ S)
    (hnR : ∀ r ∈ S, (∀ t ∈ T, r * t * r⁻¹ ∈ T) → ∀ t ∈ T, (n * r * n⁻¹) * t * (n * r * n⁻¹)⁻¹ ∈ T) :
    ∀ t ∈ T, n * t * n⁻¹ ∈ T := by
  have hAR : ∀ U : Subgroup G, U = V ∨ U = W → cj n U = V ∨ cj n U = W := by
    intro U hU
    have hUT : U ≤ T := by
      rcases hU with rfl | rfl
      · exact P.side₁.V_le_T
      · exact P.side₁.W_le_T
    have hUel : ElemAb2 U := by
      rcases hU with rfl | rfl
      · exact fun x hx y hy => ⟨(P.side₁.jst.abelian_V x hx y hy).eq, P.side₁.jst.sq_V x hx⟩
      · exact fun x hx y hy => ⟨(P.side₁.jst.abelian_V₂ x hx y hy).eq, P.side₁.jst.sq_V₂ x hx⟩
    have hUc : Nat.card U = 2 ^ (2 * e) := by
      rcases hU with rfl | rfl
      · exact P.side₁.card_V
      · exact P.side₂.card_V
    have hcS : cj n U ≤ S := by
      intro x hx
      rw [mem_cj_iff] at hx
      have h1 : n * (n⁻¹ * x * n) * n⁻¹ ∈ S :=
        mul_mem (mul_mem hn (hTS (hUT hx))) (inv_mem hn)
      simpa [mul_assoc] using h1
    have hcN : ∀ x ∈ cj n U, ∀ t ∈ T, x * t * x⁻¹ ∈ T := by
      intro x hx
      rw [mem_cj_iff] at hx
      have h1 := hnR _ (hTS (hUT hx)) (fun t ht => mul_mem (mul_mem (hUT hx) ht)
        (inv_mem (hUT hx)))
      simpa [mul_assoc] using h1
    by_cases hcT : cj n U ≤ T
    · exact P.eq_of_le_T hcT (elemAb2_cj hUel n) ((card_cj n U).trans hUc)
    · have := P.caseD hTS hS hcS hcN (elemAb2_cj hUel n) hcT
      rw [card_cj, hUc] at this
      have := P.two_mul_lt
      omega
  rcases hAR V (Or.inl rfl) with hV | hV
  · intro t ht
    have hnT := P.mem_T_of_cj_V hTS hS hn hV
    exact mul_mem (mul_mem hnT ht) (inv_mem hnT)
  · have hW : cj n W = V := by
      rcases hAR W (Or.inr rfl) with h | h
      · exact h
      · exact absurd (cj_injective (hV.trans h.symm)) P.ne_VW
    have hW' : cj n⁻¹ V = W := by
      rw [← hW, cj_cj, inv_mul_cancel, cj_eq_self_of_mem (Subgroup.one_mem _)]
    intro t ht
    refine P.mem_T_of_cj_V hTS hS (mul_mem (mul_mem hn (hTS ht)) (inv_mem hn)) ?_
    rw [← cj_cj, ← cj_cj, hW', cj_eq_of_mem_normalizer_set (P.side₂.T_le_V ht), hW]

end Sylow

theorem le_normalizer_T {S : Subgroup G} (hTS : T ≤ S) (hS : IsPGroup 2 S) :
    ∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup ↥S := (S ⊓ Subgroup.normalizer (T : Set G)).subgroupOf S with hR
  have hRmem : ∀ x : ↥S, x ∈ R ↔ ∀ t ∈ T, (x : G) * t * (x : G)⁻¹ ∈ T := by
    intro x
    rw [hR, Subgroup.mem_subgroupOf]
    constructor
    · intro hx t ht
      exact conj_mem_of_mem_normalizer hx.2 ht
    · intro hx
      exact ⟨x.2, mem_normalizer_of_conj_le hx⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs, t, ht, hst⟩ := hcon
  have hRtop : R < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hst ?_
    have : (⟨s, hs⟩ : ↥S) ∈ R := htop ▸ Subgroup.mem_top _
    exact (hRmem _).1 this t ht
  have hSp : IsPGroup 2 ↥S := hS
  have : Group.IsNilpotent ↥S := hSp.isNilpotent
  have hlt := Group.normalizerCondition_of_isNilpotent R hRtop
  obtain ⟨x, hxN, hxR⟩ := IsConcreteLE.exists_of_lt hlt
  apply hxR
  rw [hRmem]
  refine P.mem_normalizer_T hTS hS x.2 fun r hr hrT => ?_
  have h1 : (⟨r, hr⟩ : ↥S) ∈ R := (hRmem _).2 hrT
  have h2 := (Subgroup.mem_normalizer_iff.1 hxN ⟨r, hr⟩).1 h1
  exact (hRmem _).1 h2

theorem t2Base {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hTS : T ≤ S) (hsw : ∃ s ∈ S, s ∉ T) :
    T2Base G V W (V ⊓ W) (V ⊔ W) T S (Subgroup.normalizer (V : Set G))
      (Subgroup.normalizer (W : Set G)) e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D₁⟩ := P.side₁.nat
  have hSp : IsPGroup 2 S := hS.isPGroup
  have hN := P.le_normalizer_T hTS hSp
  have hswap : ∀ s ∈ S, s ∉ T → cj s V = W ∧ cj s W = V := fun s hs hsT =>
    P.swap_of_mem_R hTS hSp hs (hN s hs) hsT
  have hVel : ElemAb2 V := fun x hx y hy =>
    ⟨(P.side₁.jst.abelian_V x hx y hy).eq, P.side₁.jst.sq_V x hx⟩
  have hWel : ElemAb2 W := fun x hx y hy =>
    ⟨(P.side₁.jst.abelian_V₂ x hx y hy).eq, P.side₁.jst.sq_V₂ x hx⟩
  have hrankS : ∀ E : Subgroup G, E ≤ S → ElemAb2 E →
      Nat.card E ≤ 2 ^ (2 * e) ∧ (Nat.card E = 2 ^ (2 * e) → E = V ∨ E = W) := by
    intro E hES hE
    by_cases hET : E ≤ T
    · exact ⟨P.card_le_of_le_T hET hE, P.eq_of_le_T hET hE⟩
    · have h1 := P.caseD hTS hSp hES (fun x hx => hN x (hES hx)) hE hET
      have h2 := P.two_mul_lt
      exact ⟨by omega, fun h3 => by omega⟩
  have hidx : T.relIndex S ≤ 2 := by
    obtain ⟨s₀, hs₀, hs₀T⟩ := hsw
    have h1 := card_le_two_mul_inf (E := S) (H := T) hs₀ fun x hx hxT =>
      P.mul_mem_T_of_R hTS hSp hx (hN x hx) hxT hs₀ (hN s₀ hs₀) hs₀T
    have h2 := Subgroup.relIndex_mul_card T S
    rw [inf_comm, inf_eq_left.2 hTS] at h1
    rw [inf_eq_left.2 hTS] at h2
    have hpos : 0 < Nat.card T := Nat.card_pos
    have h3 : T.relIndex S * Nat.card T ≤ 2 * Nat.card T := by rw [h2]; exact h1
    exact Nat.le_of_mul_le_mul_right h3 hpos
  have hJT : V ⊔ W ≤ T := P.side₁.J_le_T
  refine
    { two_le := P.two_le
      sylow := hS
      T_le := hTS
      index := hidx
      exists_swap := hsw
      J_le := hJT
      sup := rfl
      inf := rfl
      elem_V := hVel
      elem_V₂ := hWel
      card_V := P.side₁.card_V
      card_V₂ := P.side₂.card_V
      card_Z := P.side₁.card_Z
      rank := ?_
      A_S := fun E hES hE hcard => (hrankS E hES hE).2 hcard
      normal_J := ?_
      comm_mem := fun x hx y hy =>
        P.side₁.jst.commutator_le (Subgroup.commutator_mem_commutator hx hy)
      sq_mem := ?_
      inv_mem := fun x hx hxx => P.side₁.jst.involution_mem hx hxx
      cent_S := ?_
      S_inf_M := P.inf_normalizer_V hTS hSp
      S_inf_M₂ := P.inf_normalizer_W hTS hSp
      index_J := ?_
      T_norm := fun t ht =>
        ⟨cj_eq_of_mem_normalizer_set (P.side₁.T_le_V ht),
          cj_eq_of_mem_normalizer_set (P.side₂.T_le_V ht)⟩
      swap := hswap }
  ·
    intro E hE
    obtain ⟨g, -, hg⟩ := exists_conj_le_of_isSylowOf hS le_top hE.isPGroup
    have := (hrankS _ hg (elemAb2_cj hE g)).1
    rwa [card_cj] at this
  ·
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hcj : cj (g : G) (V ⊔ W) = V ⊔ W := by
      have e1 : cj (g : G) (V ⊔ W) = cj (g : G) V ⊔ cj (g : G) W := Subgroup.map_sup _ _ _
      by_cases hgT : (g : G) ∈ T
      · rw [e1, cj_eq_of_mem_normalizer_set (P.side₁.T_le_V hgT),
          cj_eq_of_mem_normalizer_set (P.side₂.T_le_V hgT)]
      · rw [e1, (hswap g g.2 hgT).1, (hswap g g.2 hgT).2, sup_comm]
    have := mul_mem_cj (g : G) hn
    rw [hcj] at this
    simpa using this
  ·
    intro x hx
    obtain ⟨v, hv, w, hw, rfl⟩ := (P.side₁.jst.mem_sup_iff).1 hx
    rw [P.side₁.jst.sq_mul hv hw]
    exact P.side₁.jst.commutator_mem hv hw
  ·
    intro g hg hgc
    by_cases hgT : g ∈ T
    · by_contra hgJ
      obtain ⟨v, hv, hvZ⟩ := P.side₁.fixZ D₁ hgT hgJ
      exact hvZ (hgc v (Subgroup.mem_sup_left hv))
    · exfalso
      obtain ⟨v, hv, hvW⟩ : ∃ v ∈ V, v ∉ W := by
        by_contra hcon
        push Not at hcon
        exact P.side₁.jst.not_le_V₂ hcon
      have h1 : g * v * g⁻¹ ∈ W := (hswap g hg hgT).1 ▸ mul_mem_cj g hv
      have h2 : ⁅g, v⁆ ∈ W := (hgc v (Subgroup.mem_sup_left hv)).2
      apply hvW
      have e1 : v = (⁅g, v⁆)⁻¹ * (g * v * g⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact mul_mem (inv_mem h2) h1
  ·
    rw [← Subgroup.relIndex_mul_relIndex (V ⊔ W) T S hJT hTS]
    have h1 := P.side₁.relIndex_le D₁
    calc (V ⊔ W).relIndex T * T.relIndex S ≤ e * 2 := Nat.mul_le_mul h1 hidx
      _ = 2 * e := mul_comm _ _

end L3Pair

end CFSG.CGT.PushingUpLit.A78L3
