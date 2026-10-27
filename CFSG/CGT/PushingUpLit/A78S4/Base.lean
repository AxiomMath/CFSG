module

public import CFSG.CGT.PushingUpLit.A78S4.H1

public section

namespace CFSG.CGT.PushingUpLit.A78S4

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.CGT.PushingUpLit.A78L3
open CFSG.ABGLocalTools
open Matrix
open scoped commutatorElement

namespace S4Pair

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ T : Subgroup G} {e : ℕ}
  (P : S4Pair G L₁ L₂ V W Z Z₂ T e)

include P

theorem mem_Z_iff {v : G} (hv : v ∈ V) :
    v ∈ Z ↔ ∀ m ∈ Subgroup.normalizer (V : Set G), ∀ j ∈ V ⊔ W,
      v * (m * j * m⁻¹) = m * j * m⁻¹ * v := by
  constructor
  · intro hz m hm j hj
    have hmj : m * j * m⁻¹ ∈ L₁ := conj_mem_of_mem_normalizer (P.nl₁ hm) (P.side₁.J_le_L hj)
    exact (Subgroup.mem_centralizer_iff.1 (P.side₁.Z_cent hz) _ hmj).symm
  · intro hc
    by_contra hvZ
    obtain ⟨D⟩ := P.side₁.nat
    obtain ⟨fr⟩ := P.side₁.exists_frame D
    have hy0 : fr.y₀ ≠ 0 := by
      intro h0
      have := fr.hdet
      rw [h0] at this
      simp [det2] at this
    obtain ⟨M, -, hM⟩ := exists_fixSL_mulVec_eq (σ := RingEquiv.refl _) (D.κ_ne_zero hv hvZ) hy0
      (fun _ => rfl) (fun _ => rfl)
    obtain ⟨l, hl, hlM⟩ := D.ρ_surj M
    have hlv : D.κ (l * v * l⁻¹) = fr.y₀ := by rw [D.conj l hl v hv, hlM]; exact hM
    have hlvV : l * v * l⁻¹ ∈ V := D.norm l hl v hv
    obtain ⟨w, hw, hwV⟩ : ∃ w ∈ W, w ∉ V := by
      by_contra hcon
      push Not at hcon
      exact P.side₁.jst.not_le_V hcon
    have hcomm := hc l⁻¹ (D.le_normalizer (inv_mem hl)) w (Subgroup.mem_sup_right hw)
    have hmem : l * v * l⁻¹ ∈ V ⊓ Subgroup.centralizer ({w} : Set G) := by
      refine Subgroup.mem_inf.2 ⟨hlvV, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      calc l * v * l⁻¹ * w = l * (v * (l⁻¹ * w * l⁻¹⁻¹)) * l⁻¹ := by group
        _ = l * ((l⁻¹ * w * l⁻¹⁻¹) * v) * l⁻¹ := by rw [hcomm]
        _ = w * (l * v * l⁻¹) := by group
    rw [P.side₁.jst.inf_centralizer_eq hw hwV, fr.mem_N_iff hlvV, hlv, fr.hdet] at hmem
    exact one_ne_zero hmem

theorem cj_Z_le {r : G} (hrV : cj r V = W) (hrW : cj r W = V) : cj r Z ≤ Z₂ := by
  have hrV' : cj r⁻¹ W = V := by
    rw [← hrV, cj_cj, inv_mul_cancel, cj_eq_self_of_mem (Subgroup.one_mem _)]
  have hrW' : cj r⁻¹ V = W := by
    rw [← hrW, cj_cj, inv_mul_cancel, cj_eq_self_of_mem (Subgroup.one_mem _)]
  intro x hx
  rw [mem_cj_iff] at hx
  have hxW : x ∈ W := by
    have : r * (r⁻¹ * x * r) * r⁻¹ ∈ cj r V := mul_mem_cj r (P.side₁.Z_le_V hx)
    rw [hrV] at this
    simpa [mul_assoc] using this
  refine (P.symm.mem_Z_iff hxW).2 fun m hm j hj => ?_
  have hm₀ : r⁻¹ * m * r ∈ Subgroup.normalizer (V : Set G) := by
    apply mem_normalizer_of_cj
    rw [show r⁻¹ * m * r = r⁻¹ * (m * r) by group, ← cj_cj, ← cj_cj, hrV,
      cj_eq_of_mem_normalizer_set hm, hrV']
  have hj₀ : r⁻¹ * j * r ∈ V ⊔ W := by
    have e1 : cj r⁻¹ (W ⊔ V) = cj r⁻¹ W ⊔ cj r⁻¹ V := Subgroup.map_sup _ _ _
    have h1 : r⁻¹ * j * r⁻¹⁻¹ ∈ cj r⁻¹ (W ⊔ V) := mul_mem_cj r⁻¹ hj
    rw [e1, hrV', hrW'] at h1
    simpa using h1
  have h1 := (P.mem_Z_iff (P.side₁.Z_le_V hx)).1 hx _ hm₀ _ hj₀
  calc x * (m * j * m⁻¹) = r * ((r⁻¹ * x * r) * ((r⁻¹ * m * r) * (r⁻¹ * j * r) *
        (r⁻¹ * m * r)⁻¹)) * r⁻¹ := by group
    _ = r * (((r⁻¹ * m * r) * (r⁻¹ * j * r) * (r⁻¹ * m * r)⁻¹) * (r⁻¹ * x * r)) * r⁻¹ := by
        rw [h1]
    _ = m * j * m⁻¹ * x := by group

theorem swap_Z (hZ : Z ≠ ⊥) {r : G} (hrV : cj r V = W) (hrW : cj r W = V) :
    cj r Z = Z₂ ∧ cj r Z₂ = Z := by
  have hZ₂ := P.Z₂_ne_bot hZ
  refine ⟨Subgroup.eq_of_le_of_card_ge (P.cj_Z_le hrV hrW) ?_,
    Subgroup.eq_of_le_of_card_ge (P.symm.cj_Z_le hrW hrV) ?_⟩
  · rw [card_cj, P.card_Z hZ, P.card_Z₂ hZ]
  · rw [card_cj, P.card_Z hZ, P.card_Z₂ hZ]

theorem ne_VW : V ≠ W := fun h => P.side₁.jst.not_le_V (h ▸ le_rfl)

theorem card_V3 (hZ : Z ≠ ⊥) : Nat.card V = 2 ^ (3 * e) := by
  rw [P.side₁.card_V, P.card_Z hZ, ← pow_add]
  ring_nf

theorem card_W3 (hZ : Z ≠ ⊥) : Nat.card W = 2 ^ (3 * e) := by
  rw [P.side₂.card_V, P.card_Z₂ hZ, ← pow_add]
  ring_nf

theorem two_mul_lt : 2 * 2 ^ (3 * (e / 2)) < 2 ^ (3 * e) := by
  have h2 := P.side₁.two_le
  calc 2 * 2 ^ (3 * (e / 2)) = 2 ^ (3 * (e / 2) + 1) := by ring
    _ < 2 ^ (3 * e) := Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem four_mul_lt : 4 * 2 ^ e < 2 ^ (3 * e) := by
  have h2 := P.side₁.two_le
  calc 4 * 2 ^ e = 2 ^ (e + 2) := by ring
    _ < 2 ^ (3 * e) := Nat.pow_lt_pow_right (by norm_num) (by omega)

variable (hZ : Z ≠ ⊥)

include hZ

theorem caseA {E : Subgroup G} (hET : E ≤ T) (hE : ElemAb2 E) (hEJ : ¬ E ≤ V ⊔ W) :
    Nat.card E ≤ 2 * 2 ^ (3 * (e / 2)) := by
  obtain ⟨D⟩ := P.side₁.nat
  obtain ⟨a, haE, haJ⟩ : ∃ a ∈ E, a ∉ V ⊔ W := by
    by_contra hcon
    push Not at hcon
    exact hEJ hcon
  have haa : a * a = 1 := (hE a haE a haE).2
  have h1 := card_le_two_mul_inf haE fun x hx hxJ =>
    P.side₁.mul_mem_J_of_involutions D (hET hx) hxJ (hE x hx x hx).2 (hET haE) haJ haa
  have hEJ' : E ⊓ (V ⊔ W) ≤ V ⊔ W := inf_le_right
  rcases P.side₁.jst.elemAbelian_le hEJ' (fun x hx => (hE x hx.1 x hx.1).2) with hV | hW
  · have hle : E ⊓ (V ⊔ W) ≤ V ⊓ Subgroup.centralizer ({a} : Set G) := fun x hx =>
      Subgroup.mem_inf.2 ⟨hV hx, Subgroup.mem_centralizer_singleton_iff.2 (hE x hx.1 a haE).1⟩
    have h2 := Subgroup.card_le_of_le hle
    rw [P.card_CV hZ (hET haE) haJ haa] at h2
    omega
  · have haJ' : a ∉ W ⊔ V := by rwa [sup_comm]
    have hle : E ⊓ (V ⊔ W) ≤ W ⊓ Subgroup.centralizer ({a} : Set G) := fun x hx =>
      Subgroup.mem_inf.2 ⟨hW hx, Subgroup.mem_centralizer_singleton_iff.2 (hE x hx.1 a haE).1⟩
    have h2 := Subgroup.card_le_of_le hle
    rw [P.symm.card_CV (P.Z₂_ne_bot hZ) (hET haE) haJ' haa] at h2
    omega

theorem card_le_of_le_T {E : Subgroup G} (hET : E ≤ T) (hE : ElemAb2 E) :
    Nat.card E ≤ 2 ^ (3 * e) := by
  by_cases hEJ : E ≤ V ⊔ W
  · have := P.side₁.jst.card_le_of_elemAbelian hEJ fun x hx => (hE x hx x hx).2
    rwa [P.card_V3 hZ] at this
  · exact (P.caseA hZ hET hE hEJ).trans P.two_mul_lt.le

theorem eq_of_le_T {E : Subgroup G} (hET : E ≤ T) (hE : ElemAb2 E)
    (hcard : Nat.card E = 2 ^ (3 * e)) : E = V ∨ E = W := by
  by_cases hEJ : E ≤ V ⊔ W
  · exact P.side₁.jst.mem_of_card hEJ (fun x hx => (hE x hx x hx).2)
      (by rw [P.card_V3 hZ, hcard])
  · have := P.caseA hZ hET hE hEJ
    have := P.two_mul_lt
    omega

theorem card_CN_swap {a : G} (haZ : cj a Z = Z₂) :
    Nat.card ↥((V ⊓ W) ⊓ Subgroup.centralizer ({a} : Set G)) ≤ 2 ^ e := by
  set C := (V ⊓ W) ⊓ Subgroup.centralizer ({a} : Set G) with hC
  have hCZ : ∀ z ∈ C, z ∈ Z → z = 1 := by
    intro z hz hzZ
    have h1 : a * z * a⁻¹ ∈ Z₂ := haZ ▸ mul_mem_cj a hzZ
    have h2 : a * z * a⁻¹ = z := by
      rw [(Subgroup.mem_centralizer_singleton_iff.1 hz.2).symm]
      group
    rw [h2] at h1
    have h3 : z ∈ Z ⊓ Z₂ := Subgroup.mem_inf.2 ⟨hzZ, h1⟩
    rw [P.inf_Z] at h3
    exact h3
  let g : ↥C × ↥Z → ↥(V ⊓ W) := fun p => ⟨p.1 * p.2, mul_mem p.1.2.1 (P.side₁.Z_le_N p.2.2)⟩
  have hg : Function.Injective g := by
    rintro ⟨c, z⟩ ⟨c', z'⟩ hcc
    have h1 : (c : G) * z = c' * z' := congrArg Subtype.val hcc
    have h2 : (c' : G)⁻¹ * c = z' * (z : G)⁻¹ := by
      calc (c' : G)⁻¹ * c = (c' : G)⁻¹ * (c * z) * (z : G)⁻¹ := by group
        _ = (c' : G)⁻¹ * (c' * z') * (z : G)⁻¹ := by rw [h1]
        _ = z' * (z : G)⁻¹ := by group
    have h3 := hCZ _ (mul_mem (inv_mem c'.2) c.2) (by rw [h2]; exact mul_mem z'.2 (inv_mem z.2))
    have hc : (c : G) = c' := by
      have := congrArg (fun y => (c' : G) * y) h3
      simpa using this
    have hz : (z : G) = z' := by
      rw [hc] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext hc) (Subtype.ext hz)
  have h1 := Nat.card_le_card_of_injective g hg
  rw [Nat.card_prod, P.card_Z hZ, P.card_N hZ, two_mul, pow_add] at h1
  exact Nat.le_of_mul_le_mul_right h1 (by positivity)

theorem inf_normalizer_V (hsyl₁ : IsSylowOf 2 T (Subgroup.normalizer (V : Set G))) {S : Subgroup G}
    (hTS : T ≤ S) (hS : IsPGroup 2 S) : S ⊓ Subgroup.normalizer (V : Set G) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hsyl₁.eq_of_le (le_inf hTS hsyl₁.le) inf_le_right (hS.to_le inf_le_left)

section Sylow

variable (hsyl₁ : IsSylowOf 2 T (Subgroup.normalizer (V : Set G)))
  {S : Subgroup G} (hTS : T ≤ S) (hS : IsPGroup 2 S)

include hsyl₁ hTS hS

theorem mem_T_of_cj_V {r : G} (hr : r ∈ S) (hrV : cj r V = V) : r ∈ T := by
  rw [← P.inf_normalizer_V hZ hsyl₁ hTS hS]
  exact ⟨hr, mem_normalizer_of_cj hrV⟩

omit hsyl₁ hTS hS in
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
  have hUc : Nat.card U = 2 ^ (3 * e) := by
    rcases hU with rfl | rfl
    · exact P.card_V3 hZ
    · exact P.card_W3 hZ
  refine P.eq_of_le_T hZ ?_ (elemAb2_cj hUel r) ((card_cj r U).trans hUc)
  intro x hx
  rw [mem_cj_iff] at hx
  have := hrT _ (hUT hx)
  simpa [mul_assoc] using this

theorem swap_of_mem_R {r : G} (hr : r ∈ S) (hrT : ∀ t ∈ T, r * t * r⁻¹ ∈ T) (hrT' : r ∉ T) :
    cj r V = W ∧ cj r W = V := by
  have hV : cj r V = W := by
    rcases P.cj_V_of_normalizes hZ hrT V (Or.inl rfl) with h | h
    · exact absurd (P.mem_T_of_cj_V hZ hsyl₁ hTS hS hr h) hrT'
    · exact h
  refine ⟨hV, ?_⟩
  rcases P.cj_V_of_normalizes hZ hrT W (Or.inr rfl) with h | h
  · exact h
  · exact absurd (cj_injective (hV.trans h.symm)) P.ne_VW

theorem mul_mem_T_of_R {x a : G} (hx : x ∈ S) (hxT : ∀ t ∈ T, x * t * x⁻¹ ∈ T) (hxT' : x ∉ T)
    (ha : a ∈ S) (haT : ∀ t ∈ T, a * t * a⁻¹ ∈ T) (haT' : a ∉ T) : x * a ∈ T := by
  refine P.mem_T_of_cj_V hZ hsyl₁ hTS hS (mul_mem hx ha) ?_
  rw [← cj_cj, (P.swap_of_mem_R hZ hsyl₁ hTS hS ha haT haT').1,
    (P.swap_of_mem_R hZ hsyl₁ hTS hS hx hxT hxT').2]

theorem caseD {E : Subgroup G} (hES : E ≤ S) (hEN : ∀ x ∈ E, ∀ t ∈ T, x * t * x⁻¹ ∈ T)
    (hE : ElemAb2 E) (hET : ¬ E ≤ T) : Nat.card E ≤ 4 * 2 ^ e := by
  obtain ⟨D⟩ := P.side₁.nat
  obtain ⟨a, haE, haT⟩ : ∃ a ∈ E, a ∉ T := by
    by_contra hcon
    push Not at hcon
    exact hET hcon
  have h1 := card_le_two_mul_inf haE fun x hx hxT =>
    P.mul_mem_T_of_R hZ hsyl₁ hTS hS (hES hx) (hEN x hx) hxT (hES haE) (hEN a haE) haT
  have hswap := P.swap_of_mem_R hZ hsyl₁ hTS hS (hES haE) (hEN a haE) haT
  have hswZ := (P.swap_Z hZ hswap.1 hswap.2).1
  have hN : (E ⊓ T) ⊓ (V ⊔ W) ≤ (V ⊓ W) ⊓ Subgroup.centralizer ({a} : Set G) := by
    have hle : (E ⊓ T) ⊓ (V ⊔ W) ≤ V ⊔ W := inf_le_right
    have hcomm : ∀ x ∈ (E ⊓ T) ⊓ (V ⊔ W), a * x * a⁻¹ = x := fun x hx => by
      rw [(hE a haE x hx.1.1).1]; group
    have hcent : ∀ x ∈ (E ⊓ T) ⊓ (V ⊔ W), x ∈ Subgroup.centralizer ({a} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.2 (hE x hx.1.1 a haE).1
    rcases P.side₁.jst.elemAbelian_le hle (fun x hx => (hE x hx.1.1 x hx.1.1).2) with hV | hW
    · intro x hx
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hV hx, ?_⟩, hcent x hx⟩
      have h2 : a * x * a⁻¹ ∈ cj a V := mul_mem_cj a (hV hx)
      rwa [hswap.1, hcomm x hx] at h2
    · intro x hx
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, hW hx⟩, hcent x hx⟩
      have h2 : a * x * a⁻¹ ∈ cj a W := mul_mem_cj a (hW hx)
      rwa [hswap.2, hcomm x hx] at h2
  have hCN := P.card_CN_swap hZ hswZ
  by_cases hEJ : E ⊓ T ≤ V ⊔ W
  · have h2 : Nat.card ↥(E ⊓ T) ≤ 2 ^ e := by
      have : E ⊓ T ≤ (V ⊓ W) ⊓ Subgroup.centralizer ({a} : Set G) := fun x hx =>
        hN (Subgroup.mem_inf.2 ⟨hx, hEJ hx⟩)
      exact (Subgroup.card_le_of_le this).trans hCN
    omega
  · obtain ⟨f, hfE, hfJ⟩ : ∃ f ∈ E ⊓ T, f ∉ V ⊔ W := by
      by_contra hcon
      push Not at hcon
      exact hEJ hcon
    have hff : f * f = 1 := (hE f hfE.1 f hfE.1).2
    have h2 := card_le_two_mul_inf (E := E ⊓ T) (H := V ⊔ W) hfE fun x hx hxJ =>
      P.side₁.mul_mem_J_of_involutions D hx.2 hxJ (hE x hx.1 x hx.1).2 hfE.2 hfJ hff
    have h3 := (Subgroup.card_le_of_le hN).trans hCN
    omega

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
    have hUc : Nat.card U = 2 ^ (3 * e) := by
      rcases hU with rfl | rfl
      · exact P.card_V3 hZ
      · exact P.card_W3 hZ
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
    · exact P.eq_of_le_T hZ hcT (elemAb2_cj hUel n) ((card_cj n U).trans hUc)
    · have := P.caseD hZ hsyl₁ hTS hS hcS hcN (elemAb2_cj hUel n) hcT
      rw [card_cj, hUc] at this
      have := P.four_mul_lt
      omega
  rcases hAR V (Or.inl rfl) with hV | hV
  · intro t ht
    have hnT := P.mem_T_of_cj_V hZ hsyl₁ hTS hS hn hV
    exact mul_mem (mul_mem hnT ht) (inv_mem hnT)
  · have hW : cj n W = V := by
      rcases hAR W (Or.inr rfl) with h | h
      · exact h
      · exact absurd (cj_injective (hV.trans h.symm)) P.ne_VW
    have hW' : cj n⁻¹ V = W := by
      rw [← hW, cj_cj, inv_mul_cancel, cj_eq_self_of_mem (Subgroup.one_mem _)]
    intro t ht
    refine P.mem_T_of_cj_V hZ hsyl₁ hTS hS (mul_mem (mul_mem hn (hTS ht)) (inv_mem hn)) ?_
    rw [← cj_cj, ← cj_cj, hW', cj_eq_of_mem_normalizer_set (P.side₂.T_le_V ht), hW]

theorem le_normalizer_T : ∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ T := by
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
  refine P.mem_normalizer_T hZ hsyl₁ hTS hS x.2 fun r hr hrT => ?_
  have h1 : (⟨r, hr⟩ : ↥S) ∈ R := (hRmem _).2 hrT
  have h2 := (Subgroup.mem_normalizer_iff.1 hxN ⟨r, hr⟩).1 h1
  exact (hRmem _).1 h2

end Sylow

theorem sp4Base (hsyl₁ : IsSylowOf 2 T (Subgroup.normalizer (V : Set G)))
    (hsyl₂ : IsSylowOf 2 T (Subgroup.normalizer (W : Set G))) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) (hTS : T ≤ S) (hsw : ∃ s ∈ S, s ∉ T) :
    Sp4Base G V W (V ⊔ W) T S (Subgroup.normalizer (V : Set G))
      (Subgroup.normalizer (W : Set G)) e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D⟩ := P.side₁.nat
  have hSp : IsPGroup 2 S := hS.isPGroup
  have hN := P.le_normalizer_T hZ hsyl₁ hTS hSp
  have hswap : ∀ s ∈ S, s ∉ T → cj s V = W ∧ cj s W = V := fun s hs hsT =>
    P.swap_of_mem_R hZ hsyl₁ hTS hSp hs (hN s hs) hsT
  have hVel : ElemAb2 V := fun x hx y hy =>
    ⟨(P.side₁.jst.abelian_V x hx y hy).eq, P.side₁.jst.sq_V x hx⟩
  have hWel : ElemAb2 W := fun x hx y hy =>
    ⟨(P.side₁.jst.abelian_V₂ x hx y hy).eq, P.side₁.jst.sq_V₂ x hx⟩
  have hrankS : ∀ E : Subgroup G, E ≤ S → ElemAb2 E →
      Nat.card E ≤ 2 ^ (3 * e) ∧ (Nat.card E = 2 ^ (3 * e) → E = V ∨ E = W) := by
    intro E hES hE
    by_cases hET : E ≤ T
    · exact ⟨P.card_le_of_le_T hZ hET hE, P.eq_of_le_T hZ hET hE⟩
    · have h1 := P.caseD hZ hsyl₁ hTS hSp hES (fun x hx => hN x (hES hx)) hE hET
      have h2 := P.four_mul_lt
      exact ⟨by omega, fun h3 => by omega⟩
  have hidx : T.relIndex S ≤ 2 := by
    obtain ⟨s₀, hs₀, hs₀T⟩ := hsw
    have h1 := card_le_two_mul_inf (E := S) (H := T) hs₀ fun x hx hxT =>
      P.mul_mem_T_of_R hZ hsyl₁ hTS hSp hx (hN x hx) hxT hs₀ (hN s₀ hs₀) hs₀T
    have h2 := Subgroup.relIndex_mul_card T S
    rw [inf_comm, inf_eq_left.2 hTS] at h1
    rw [inf_eq_left.2 hTS] at h2
    have hpos : 0 < Nat.card T := Nat.card_pos
    have h3 : T.relIndex S * Nat.card T ≤ 2 * Nat.card T := by rw [h2]; exact h1
    exact Nat.le_of_mul_le_mul_right h3 hpos
  have hJT : V ⊔ W ≤ T := P.side₁.J_le_T
  refine
    { two_le := P.side₁.two_le
      sylow := hS
      T_le := hTS
      index := hidx
      J_le := hJT
      sup := rfl
      elem_V := hVel
      elem_V₂ := hWel
      card_V := P.card_V3 hZ
      card_V₂ := P.card_W3 hZ
      rank := ?_
      A_S := fun E hES hE hcard => (hrankS E hES hE).2 hcard
      normal_J := ?_
      card_inf := P.card_N hZ
      comm_mem := fun x hx y hy =>
        P.side₁.jst.commutator_le (Subgroup.commutator_mem_commutator hx hy)
      sq_mem := ?_
      inv_mem := fun x hx hxx => P.side₁.jst.involution_mem hx hxx
      cent_S := ?_
      S_inf_M := P.inf_normalizer_V hZ hsyl₁ hTS hSp
      S_inf_M₂ := P.symm.inf_normalizer_V (P.Z₂_ne_bot hZ) hsyl₂ hTS hSp
      T_norm := fun t ht =>
        ⟨cj_eq_of_mem_normalizer_set (P.side₁.T_le_V ht),
          cj_eq_of_mem_normalizer_set (P.side₂.T_le_V ht)⟩
      swap := hswap
      exists_swap := hsw }
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
      obtain ⟨v, hv, hvN⟩ := P.side₁.fixN D hgT hgJ
      exact hvN (hgc v (Subgroup.mem_sup_left hv))
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

end S4Pair

end CFSG.CGT.PushingUpLit.A78S4
