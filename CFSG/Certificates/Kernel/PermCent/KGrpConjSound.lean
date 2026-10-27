module

public import CFSG.Certificates.Kernel.PermCent.KGrpCSound

public section

namespace CFSG.Certificates.Kernel.PkCV.KGrp

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups

theorem mem_normalizer_of_conj {G : Type*} [Group G] {H : Subgroup G} [Finite H] (σ : G)
    (h : ∀ x ∈ H, σ * x * σ⁻¹ ∈ H) : σ ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let f : H → H := fun y => ⟨σ * y * σ⁻¹, h y y.2⟩
  have hf : Function.Injective f := fun y z e => by
    have e' : σ * (y : G) * σ⁻¹ = σ * z * σ⁻¹ := congrArg Subtype.val e
    exact Subtype.ext (by simpa using e')
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hf) ⟨_, hx⟩
  have e : σ * (y : G) * σ⁻¹ = σ * x * σ⁻¹ := congrArg Subtype.val hy
  have hyx : (y : G) = x := by simpa using e
  exact hyx ▸ y.2

theorem mem_of_sq_of_index3 {G : Type*} [Group G] [Finite G] {P A : Subgroup G} (hle : P ≤ A)
    (hN : A ≤ Subgroup.normalizer (P : Set G)) (hc : Nat.card A = 3 * Nat.card P) {x : G} (hx : x ∈ A)
    (h2 : x ^ 2 = 1) : x ∈ P := by
  have : (P.subgroupOf A).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 hN
  have hi : (P.subgroupOf A).index = 3 := by
    have e1 := Subgroup.relIndex_mul_index hle
    have e2 := Subgroup.index_mul_card P
    have e3 := Subgroup.index_mul_card A
    have hp : 0 < Nat.card P := Nat.card_pos
    have hA : A.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have e4 : P.relIndex A * A.index * Nat.card P = 3 * A.index * Nat.card P := by
      rw [e1, e2, ← e3, hc]
      ring
    have e5 := Nat.eq_of_mul_eq_mul_right hp e4
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hA) e5
  have hm := Subgroup.pow_index_mem (P.subgroupOf A) ⟨x, hx⟩
  rw [hi, Subgroup.mem_subgroupOf] at hm
  have h3 : x ^ 3 = x := by rw [pow_succ, h2, one_mul]
  simpa [h3] using hm

variable {n : Nat} [Small n]

theorem centL_conj (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) {g : CV n} (hg : g ∈ elemsC Q)
    (r : CV n) : (centL (elemsC Q) (g * r * g⁻¹)).length = (centL (elemsC Q) r).length := by
  set L := elemsC Q with hL
  have hg' : g⁻¹ ∈ L := by
    rw [hL, mem_elemsC Q hQ] at hg ⊢
    rw [← ev_inv']
    exact Q.originalSubgroup.inv_mem hg
  have hφ : ∀ x, eq22C x (g * r * g⁻¹) (g * r * g⁻¹) x =
      eq22C (g⁻¹ * x * g⁻¹⁻¹) r r (g⁻¹ * x * g⁻¹⁻¹) := by
    intro x
    rw [eq22C_eq, eq22C_eq, decide_eq_decide]
    constructor
    · intro h
      calc g⁻¹ * x * g⁻¹⁻¹ * r = g⁻¹ * (x * (g * r * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * r * g⁻¹) * x) * g := by rw [h]
        _ = r * (g⁻¹ * x * g⁻¹⁻¹) := by group
    · intro h
      calc x * (g * r * g⁻¹) = g * ((g⁻¹ * x * g⁻¹⁻¹) * r) * g⁻¹ := by group
        _ = g * (r * (g⁻¹ * x * g⁻¹⁻¹)) * g⁻¹ := by rw [h]
        _ = g * r * g⁻¹ * x := by group
  have hmem : ∀ y, y ∈ L ↔ y ∈ L.map fun z => g⁻¹ * z * g⁻¹⁻¹ := by
    intro y
    rw [List.mem_map]
    constructor
    · intro hy
      exact ⟨g * y * g⁻¹, conj_mem_elemsC Q hQ hg hy, by group⟩
    · rintro ⟨z, hz, rfl⟩
      exact conj_mem_elemsC Q hQ hg' hz
  have hnd : L.Nodup := nodup_elemsC Q hQ
  have hnd' : (L.map fun z => g⁻¹ * z * g⁻¹⁻¹).Nodup :=
    hnd.map fun a b h => by simpa using h
  have hp : (L.map fun z => g⁻¹ * z * g⁻¹⁻¹).Perm L :=
    (List.perm_ext_iff_of_nodup hnd' hnd).2 fun y => (hmem y).symm
  unfold centL
  simp only [hφ]
  rw [← (hp.filter (fun y => eq22C y r r y)).length_eq, List.filter_map, List.length_map]
  rfl

theorem le_normalizer_of_normC (QP QA : RawSchreierDatum n) (hP : ValidSchreier QP) (a b : CV n)
    (hgen : QP.original.toList = [ev a, ev b])
    (h : normC QP (QA.original.toList.map cOf) a b = true) :
    QA.originalSubgroup ≤
      Subgroup.normalizer (QP.originalSubgroup : Set (Equiv.Perm (Fin n))) := by
  unfold normC at h
  rw [List.all_eq_true] at h
  have hcP : QP.originalSubgroup = Subgroup.closure {g | g ∈ QP.original.toList} := by
    rw [RawSchreierDatum.originalSubgroup]
  have hconj : ∀ (σ : Equiv.Perm (Fin n)) (x : CV n), siftC QP (cOf σ * x * (cOf σ)⁻¹) 0 = true →
      σ * ev x * σ⁻¹ ∈ QP.originalSubgroup := by
    intro σ x hx
    have hm := (mem_iff_sift QP hP _).2 (by rw [sift_ev]; exact hx)
    rwa [← ev_mul', ← ev_mul', ← ev_inv', ev_cOf] at hm
  rw [RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
  intro σ hσ
  have h1 := h (cOf σ) (List.mem_map.2 ⟨σ, hσ, rfl⟩)
  rw [Bool.and_eq_true] at h1
  refine mem_normalizer_of_conj σ fun x hx => ?_
  have key : Subgroup.closure {g | g ∈ QP.original.toList} ≤
      QP.originalSubgroup.comap (MulAut.conj σ).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro g hg
    rw [Set.mem_setOf_eq, hgen, List.mem_cons, List.mem_singleton] at hg
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rcases hg with rfl | rfl
    · exact hconj σ a h1.1
    · exact hconj σ b h1.2
  rw [← hcP] at key
  have hx' := key hx
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hx'

theorem solvC_of_conj (QP QA : RawSchreierDatum n) (hP : ValidSchreier QP) (hA : ValidSchreier QA)
    (hle : QP.originalSubgroup ≤ QA.originalSubgroup)
    (hN : QA.originalSubgroup ≤
      Subgroup.normalizer (QP.originalSubgroup : Set (Equiv.Perm (Fin n))))
    (hc : Nat.card QA.originalSubgroup = 3 * Nat.card QP.originalSubgroup) (x0 : CV n) (c : Nat)
    (hcl : ((elemsC QP).filter fun x => orderIsC x 2).all
      (fun x => (elemsC QP).any fun g => eq22C g x0 x g) = true)
    (h0 : (centL (elemsC QP) x0).length = c) :
    solvC (elemsC QA) (elemsC QP) [c] = true := by
  unfold solvC
  rw [List.all_eq_true]
  intro τ hτ
  cases hb : (powOneC τ 2 && !decide (τ = 1))
  · rfl
  · rw [cond_true]
    rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hb
    obtain ⟨h2, h1⟩ := hb
    have h2' : τ ^ 2 = 1 := of_decide_eq_true (by rw [powOneC_eq']; exact h2)
    have hτA : ev τ ∈ QA.originalSubgroup := (mem_elemsC QA hA τ).1 hτ
    have hτP : τ ∈ elemsC QP :=
      (mem_elemsC QP hP τ).2 (mem_of_sq_of_index3 hle hN hc hτA (by rw [ev_pow', h2', ← one_eq_ev]))
    have hp1 : powOneC τ 1 = false := by
      rw [← powOneC_eq', pow_one]
      exact decide_eq_false h1
    have hord : orderIsC τ 2 = true := by
      have hr : List.range 2 = [0, 1] := rfl
      unfold orderIsC
      rw [h2, hr]
      simp [hp1]
    obtain ⟨g, hg, hgx⟩ :=
      List.any_eq_true.1 (List.all_eq_true.1 hcl τ (List.mem_filter.2 ⟨hτP, hord⟩))
    rw [eq22C_eq, decide_eq_true_iff] at hgx
    have hx' : τ = g * x0 * g⁻¹ := by rw [hgx, mul_inv_cancel_right]
    rw [hx', centL_conj QP hP hg x0, h0]
    simp

end CFSG.Certificates.Kernel.PkCV.KGrp

end
