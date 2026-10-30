module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBInputs

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open scoped MatrixGroups

namespace LinCase

def linns_unip {k : Type*} [Field k] (c : k) : SL(2, k) :=
  ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two]⟩

def linns_weyl (k : Type*) [Field k] : SL(2, k) :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

lemma linns_unip_mulVec {k : Type*} [Field k] (c : k) (v : Fin 2 → k) :
    (linns_unip c : Matrix (Fin 2) (Fin 2) k).mulVec v = ![v 0 + c * v 1, v 1] := by
  ext i
  fin_cases i <;> simp [linns_unip, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma linns_weyl_mulVec {k : Type*} [Field k] (v : Fin 2 → k) :
    (linns_weyl k : Matrix (Fin 2) (Fin 2) k).mulVec v = ![v 1, -v 0] := by
  ext i
  fin_cases i <;> simp [linns_weyl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma linns_top_of_mem_second_ne_zero {k : Type*} [Field k] (S : AddSubgroup (Fin 2 → k))
    (hS : ∀ g : SL(2, k), ∀ v ∈ S, (g : Matrix (Fin 2) (Fin 2) k).mulVec v ∈ S)
    {v : Fin 2 → k} (hv : v ∈ S) (h1 : v 1 ≠ 0) : S = ⊤ := by
  have hA : ∀ a : k, ![a, 0] ∈ S := by
    intro a
    have hc := S.sub_mem (hS (linns_unip (a / v 1)) v hv) hv
    have e : (linns_unip (a / v 1) : Matrix (Fin 2) (Fin 2) k).mulVec v - v = ![a, 0] := by
      rw [linns_unip_mulVec]
      ext i
      fin_cases i <;> simp [h1]
    rwa [e] at hc
  have hB : ∀ b : k, ![0, b] ∈ S := by
    intro b
    have hc := hS (linns_weyl k) _ (hA (-b))
    have e : (linns_weyl k : Matrix (Fin 2) (Fin 2) k).mulVec ![-b, 0] = ![0, b] := by
      rw [linns_weyl_mulVec]
      ext i
      fin_cases i <;> simp
    rwa [e] at hc
  rw [eq_top_iff]
  intro u _
  have hu : u = ![u 0, 0] + ![0, u 1] := by
    ext i
    fin_cases i <;> simp
  rw [hu]
  exact S.add_mem (hA (u 0)) (hB (u 1))

theorem linns_addSubgroup_invariant {k : Type*} [Field k] (S : AddSubgroup (Fin 2 → k))
    (hS : ∀ g : SL(2, k), ∀ v ∈ S, (g : Matrix (Fin 2) (Fin 2) k).mulVec v ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  by_cases h0 : ∀ v ∈ S, v = 0
  · left
    rw [eq_bot_iff]
    intro v hv
    exact AddSubgroup.mem_bot.2 (h0 v hv)
  · right
    push Not at h0
    obtain ⟨v, hv, hv0⟩ := h0
    by_cases h1 : v 1 = 0
    ·
      have h00 : v 0 ≠ 0 := by
        intro h00
        apply hv0
        ext i
        fin_cases i <;> simp [h00, h1]
      refine linns_top_of_mem_second_ne_zero S hS (hS (linns_weyl k) v hv) ?_
      rw [linns_weyl_mulVec]
      simp [h00]
    · exact linns_top_of_mem_second_ne_zero S hS hv h1

theorem natural_section_eq_of_invariant {G : Type*} [Group G] {X A B Z : Subgroup G}
    {k : Type*} [Field k] (h : IsNaturalSection X A B k) (hBZ : B ≤ Z) (hZA : Z ≤ A)
    (hinv : ∀ x ∈ X, ∀ z ∈ Z, x * z * x⁻¹ ∈ Z) : Z = B ∨ Z = A := by
  obtain ⟨φ, θ, -, hadd, -, hgen, hequiv⟩ := h
  have hθ0 : θ 0 ∈ B := by
    have h00 := hadd 0 0
    rw [add_zero] at h00
    have e : (θ 0 * θ 0)⁻¹ * θ 0 = (θ 0)⁻¹ := by group
    rw [e] at h00
    exact inv_mem_iff.1 h00
  have hZadd : ∀ v w, θ v ∈ Z → θ w ∈ Z → θ (v + w) ∈ Z := by
    intro v w hv hw
    have e : θ (v + w) = (θ v * θ w) * ((θ v * θ w)⁻¹ * θ (v + w)) :=
      (mul_inv_cancel_left _ _).symm
    rw [e]
    exact mul_mem (mul_mem hv hw) (hBZ (hadd v w))
  have hZneg : ∀ v, θ v ∈ Z → θ (-v) ∈ Z := by
    intro v hv
    have h1 := hadd v (-v)
    rw [add_neg_cancel] at h1
    have hc : (θ v * θ (-v))⁻¹ ∈ B := by
      have h2 := mul_mem h1 (inv_mem hθ0)
      have e2 : (θ v * θ (-v))⁻¹ * θ 0 * (θ 0)⁻¹ = (θ v * θ (-v))⁻¹ := by group
      rwa [e2] at h2
    have e3 : θ (-v) = (θ v)⁻¹ * (θ v * θ (-v)) := (inv_mul_cancel_left _ _).symm
    rw [e3]
    exact mul_mem (inv_mem hv) (hBZ (inv_mem_iff.1 hc))
  obtain ⟨S, hS⟩ : ∃ S : AddSubgroup (Fin 2 → k), ∀ v, v ∈ S ↔ θ v ∈ Z :=
    ⟨{ carrier := {v | θ v ∈ Z}
       add_mem' := fun {v w} hv hw => hZadd v w hv hw
       zero_mem' := hBZ hθ0
       neg_mem' := fun {v} hv => hZneg v hv }, fun _ => Iff.rfl⟩
  have hinvS : ∀ g : SL(2, k), ∀ v ∈ S, (g : Matrix (Fin 2) (Fin 2) k).mulVec v ∈ S := by
    intro g v hv
    have hv' : θ v ∈ Z := (hS v).1 hv
    apply (hS _).2
    obtain ⟨x, hx⟩ : ∃ x : X, φ x = g := ⟨φ.symm g, φ.apply_symm_apply g⟩
    have h1 := hequiv x v
    rw [hx] at h1
    have h2 := hinv (x : G) x.2 (θ v) hv'
    have e : θ ((g : Matrix (Fin 2) (Fin 2) k).mulVec v) =
        ((x : G) * θ v * (x : G)⁻¹) *
          (((θ ((g : Matrix (Fin 2) (Fin 2) k).mulVec v))⁻¹ * ((x : G) * θ v * (x : G)⁻¹))⁻¹) := by
      group
    rw [e]
    exact mul_mem h2 (inv_mem (hBZ h1))
  rcases linns_addSubgroup_invariant S hinvS with hbot | htop
  · left
    refine le_antisymm (fun z hz => ?_) hBZ
    obtain ⟨v, hv⟩ := hgen z (hZA hz)
    have hθvZ : θ v ∈ Z := by
      have e : θ v = z * ((θ v)⁻¹ * z)⁻¹ := by group
      rw [e]
      exact mul_mem hz (inv_mem (hBZ hv))
    have hv0 : v = 0 := by
      have hvS : v ∈ S := (hS v).2 hθvZ
      rw [hbot] at hvS
      exact AddSubgroup.mem_bot.1 hvS
    rw [hv0] at hv
    have h3 := mul_mem hθ0 hv
    rwa [mul_inv_cancel_left] at h3
  · right
    refine le_antisymm hZA (fun a ha => ?_)
    obtain ⟨v, hv⟩ := hgen a ha
    have hvS : v ∈ S := by
      rw [htop]
      exact AddSubgroup.mem_top v
    have hθvZ : θ v ∈ Z := (hS v).1 hvS
    have e : a = θ v * ((θ v)⁻¹ * a) := (mul_inv_cancel_left _ _).symm
    rw [e]
    exact mul_mem hθvZ (hBZ hv)

theorem linns_conj_apply {G : Type*} [Group G] (g x : G) :
    (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ :=
  rfl

theorem natural_section_map_conj {G : Type*} [Group G] {X A B : Subgroup G} {k : Type*}
    [Field k] (h : IsNaturalSection X A B k) (g : G) :
    IsNaturalSection (X.map (MulAut.conj g).toMonoidHom) (A.map (MulAut.conj g).toMonoidHom)
      (B.map (MulAut.conj g).toMonoidHom) k := by
  obtain ⟨φ, θ, hθA, hadd, hinj, hgen, hequiv⟩ := h
  have hinjc : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  refine ⟨(Subgroup.equivMapOfInjective X (MulAut.conj g).toMonoidHom hinjc).symm.trans φ,
    fun v => g * θ v * g⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (hθA v)
  · intro v w
    have h2 := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (hadd v w)
    convert h2 using 1
    simp only [linns_conj_apply]
    group
  · intro v hv
    obtain ⟨y, hy, hyv⟩ := Subgroup.mem_map.1 hv
    have h2 : g * y * g⁻¹ = g * θ v * g⁻¹ := hyv
    have e : y = θ v := mul_left_cancel (mul_right_cancel h2)
    exact hinj v (by rw [← e]; exact hy)
  · intro a ha
    obtain ⟨a0, ha0, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨v, hv⟩ := hgen a0 ha0
    refine ⟨v, ?_⟩
    have h2 := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hv
    convert h2 using 1
    simp only [linns_conj_apply]
    group
  · intro x v
    obtain ⟨x0, rfl⟩ :=
      (Subgroup.equivMapOfInjective X (MulAut.conj g).toMonoidHom hinjc).surjective x
    have h2 := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (hequiv x0 v)
    convert h2 using 1
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      Subgroup.coe_equivMapOfInjective_apply, linns_conj_apply]
    group

end LinCase

end CFSG.LocalAnalysis.EvenBN.U5
