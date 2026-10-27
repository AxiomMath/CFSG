module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCFrame
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCPairs

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT (diagTorus2)
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] {m : ℕ} {Q : Type*} [Group Q]

section Frame

theorem exists_frame_adapted (h2 : (2 : K) ≠ 0) (hex : ∃ a : Kˣ, (a : K) ≠ ((a⁻¹ : Kˣ) : K))
    (ψ : StatedSp m K →* Q) (hψ : ψ.ker ≤ Subgroup.center (StatedSp m K))
    (R : Fin m → Subgroup Q)
    (hR : ∀ k, ∃ P, IsHyperbolicPlane P ∧ R k = (planeGroup P).map ψ)
    (hinj : Function.Injective R)
    (hcomm : ∀ k l, k ≠ l → ∀ x ∈ R k, ∀ y ∈ R l, x * y = y * x) :
    ∃ g : StatedSp m K, ∀ k,
      (longBlock K m k).range.map (ψ.comp (MulAut.conj g).toMonoidHom) = R k := by
  choose P hP hRP using hR
  have horth : ∀ k l, k ≠ l → ∀ x ∈ P k, ∀ y ∈ P l, form x y = 0 := by
    intro k l hkl
    refine forall_form_eq_zero_of_commutator_mem_center h2 hex (hP k) (hP l) ?_ ?_
    · intro h
      exact hkl (hinj (by rw [hRP k, hRP l, h]))
    · rw [Subgroup.commutator_le]
      intro x hx y hy
      apply hψ
      have hx' : ψ x ∈ R k := by
        rw [hRP k]
        exact ⟨x, hx, rfl⟩
      have hy' : ψ y ∈ R l := by
        rw [hRP l]
        exact ⟨y, hy, rfl⟩
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def,
        hcomm k l hkl _ hx' _ hy']
      group
  obtain ⟨g, hg⟩ := exists_conj_planeGroup hP horth
  refine ⟨g, fun k => ?_⟩
  rw [hRP k, (hg k).2, Subgroup.map_map]

end Frame

section Torus

theorem conj_mul_toMonoidHom {G : Type*} [Group G] (g h : G) :
    (MulAut.conj (g * h)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (MulAut.conj h).toMonoidHom := by
  ext x
  simp [mul_assoc]

theorem exists_mulAut_comp_eq {f β : SL(2, K) →* Q} (hf : Function.Injective f)
    (hβ : Function.Injective β) (hrange : f.range = β.range) :
    ∃ α : MulAut SL(2, K), f.comp α.toMonoidHom = β := by
  have hex : ∀ x, ∃ y, f y = β x := fun x => by
    have : β x ∈ f.range := by
      rw [hrange]
      exact ⟨x, rfl⟩
    exact this
  choose a ha using hex
  have hmul : ∀ x y, a (x * y) = a x * a y := fun x y => by
    apply hf
    rw [ha, map_mul, map_mul, ha, ha]
  let α₀ : SL(2, K) →* SL(2, K) :=
    { toFun := a
      map_one' := by
        apply hf
        rw [ha, map_one, map_one]
      map_mul' := hmul }
  have hinj : Function.Injective α₀ := by
    intro x y hxy
    apply hβ
    rw [← ha x, ← ha y]
    exact congrArg f hxy
  have hsurj : Function.Surjective α₀ := by
    intro y
    have : f y ∈ β.range := by
      rw [← hrange]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := this
    refine ⟨x, hf ?_⟩
    change f (a x) = f y
    rw [ha, hx]
  refine ⟨MulEquiv.ofBijective α₀ ⟨hinj, hsurj⟩, ?_⟩
  ext x
  exact ha x

theorem mem_center_of_conj_mem_center {G : Type*} [Group G] {g x : G}
    (h : g * x * g⁻¹ ∈ Subgroup.center G) : x ∈ Subgroup.center G := by
  have h1 := Subgroup.mem_center_iff.1 h g
  have h2 : g * x * g⁻¹ = x := by
    apply mul_left_cancel (a := g)
    calc g * (g * x * g⁻¹) = g * (g * x * g⁻¹) * g * g⁻¹ := by group
      _ = g * x * g⁻¹ * g * g * g⁻¹ := by rw [h1]
      _ = g * x := by group
  rw [← h2]
  exact h

theorem injective_comp_conj_longBlock (hm : 2 ≤ m) (ψ : StatedSp m K →* Q)
    (hψ : ψ.ker ≤ Subgroup.center (StatedSp m K)) (g : StatedSp m K) (k : Fin m) :
    Function.Injective ((ψ.comp (MulAut.conj g).toMonoidHom).comp (longBlock K m k)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have hker : g * longBlock K m k A * g⁻¹ ∈ Subgroup.center (StatedSp m K) := by
    apply hψ
    simpa using hA
  have hcent : longBlock K m k A ∈ Subgroup.center (StatedSp m K) :=
    mem_center_of_conj_mem_center hker
  have hj : ∃ j : Fin m, j ≠ k := by
    by_cases hk : k.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by
        have := congrArg Fin.val h
        simp only at this
        omega⟩
    · exact ⟨⟨0, by omega⟩, fun h => by
        have := congrArg Fin.val h
        simp only at this
        omega⟩
  obtain ⟨j, hjk⟩ := hj
  have h1 : longBlock K m k A = 1 :=
    eq_one_of_mem_center_of_mem_suppGroup hcent (isSupp_longBlock k A) (t := Sum.inl j) (by
      rintro (h | h)
      · exact hjk (Sum.inl_injective h)
      · exact Sum.inl_ne_inr h)
  exact longBlock_injective k (by rw [h1, map_one])

theorem exists_conj_longBlock_torus [Finite K] (hm : 2 ≤ m) (ψ : StatedSp m K →* Q)
    (hψ : ψ.ker ≤ Subgroup.center (StatedSp m K)) (k : Fin m) (g : StatedSp m K)
    {Rk : Subgroup Q}
    (hR : (longBlock K m k).range.map (ψ.comp (MulAut.conj g).toMonoidHom) = Rk)
    (β : SL(2, K) →* Q) (hβ : Function.Injective β) (hβr : β.range = Rk) :
    ∃ c : SL(2, K), (planeTorus K m k).map
      ((ψ.comp (MulAut.conj g).toMonoidHom).comp
        (MulAut.conj (longBlock K m k c)).toMonoidHom) = (diagTorus2 K).map β := by
  set ψ' : StatedSp m K →* Q := ψ.comp (MulAut.conj g).toMonoidHom with hψ'
  have hf := injective_comp_conj_longBlock hm ψ hψ g k
  rw [← hψ'] at hf
  have hrange : (ψ'.comp (longBlock K m k)).range = β.range := by
    rw [MonoidHom.range_comp, hβr, hR]
  obtain ⟨α, hα⟩ := exists_mulAut_comp_eq hf hβ hrange
  obtain ⟨c, hc⟩ := exists_conj_diagTorus α
  refine ⟨c, ?_⟩
  have hcomp : (ψ'.comp (MulAut.conj (longBlock K m k c)).toMonoidHom).comp (longBlock K m k) =
      (ψ'.comp (longBlock K m k)).comp (MulAut.conj c).toMonoidHom := by
    ext x
    simp [map_mul, map_inv]
  rw [planeTorus, Subgroup.map_map, hcomp, ← Subgroup.map_map, ← hc, Subgroup.map_map, hα]

end Torus

section Adapted

theorem exists_adapted_model [Finite K] (hm : 2 ≤ m) (h2 : (2 : K) ≠ 0)
    (hex : ∃ a : Kˣ, (a : K) ≠ ((a⁻¹ : Kˣ) : K))
    (ψ : StatedSp m K →* Q) (hψ : ψ.ker ≤ Subgroup.center (StatedSp m K))
    (R : Fin m → Subgroup Q)
    (hR : ∀ k, ∃ P, IsHyperbolicPlane P ∧ R k = (planeGroup P).map ψ)
    (hinj : Function.Injective R)
    (hcomm : ∀ k l, k ≠ l → ∀ x ∈ R k, ∀ y ∈ R l, x * y = y * x)
    (T : Fin m → Subgroup Q)
    (hT : ∀ k, ∃ β : SL(2, K) →* Q, Function.Injective β ∧ β.range = R k ∧
      (diagTorus2 K).map β = T k) :
    ∃ g : StatedSp m K,
      (∀ k, (longBlock K m k).range.map (ψ.comp (MulAut.conj g).toMonoidHom) = R k) ∧
      ∀ k, (planeTorus K m k).map (ψ.comp (MulAut.conj g).toMonoidHom) = T k := by
  classical
  obtain ⟨g₀, hg₀⟩ := exists_frame_adapted h2 hex ψ hψ R hR hinj hcomm
  have key : ∀ s : Finset (Fin m), ∃ g : StatedSp m K,
      (∀ k, (longBlock K m k).range.map (ψ.comp (MulAut.conj g).toMonoidHom) = R k) ∧
      ∀ k ∈ s, (planeTorus K m k).map (ψ.comp (MulAut.conj g).toMonoidHom) = T k := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨g₀, hg₀, by simp⟩
    | insert k s hks ih =>
      obtain ⟨g, hg, hgT⟩ := ih
      obtain ⟨β, hβ, hβr, hβT⟩ := hT k
      obtain ⟨c, hc⟩ := exists_conj_longBlock_torus hm ψ hψ k g (hg k) β hβ hβr
      have hcomp : ψ.comp (MulAut.conj (g * longBlock K m k c)).toMonoidHom =
          (ψ.comp (MulAut.conj g).toMonoidHom).comp
            (MulAut.conj (longBlock K m k c)).toMonoidHom := by
        rw [conj_mul_toMonoidHom, MonoidHom.comp_assoc]
      refine ⟨g * longBlock K m k c, ?_, ?_⟩
      · intro j
        rw [hcomp, ← Subgroup.map_map]
        by_cases hjk : j = k
        · subst hjk
          rw [map_conj_eq_of_mem (H := (longBlock K m j).range) ⟨c, rfl⟩]
          exact hg j
        · rw [map_conj_eq_of_forall_commute (longBlock K m j).range (w := longBlock K m k c)]
          · exact hg j
          · rintro _ ⟨B, rfl⟩
            exact commute_longBlock_longBlock (Ne.symm hjk) c B
      · intro j hj
        rw [hcomp]
        by_cases hjk : j = k
        · subst hjk
          rw [hc, hβT]
        · have hjs : j ∈ s := (Finset.mem_insert.1 hj).resolve_left hjk
          rw [← Subgroup.map_map,
            map_conj_eq_of_forall_commute (planeTorus K m j) (w := longBlock K m k c)]
          · exact hgT j hjs
          · rintro _ ⟨B, -, rfl⟩
            exact commute_longBlock_longBlock (Ne.symm hjk) c B
  obtain ⟨g, hg, hgT⟩ := key Finset.univ
  exact ⟨g, hg, fun k => hgT k (Finset.mem_univ k)⟩

end Adapted

end CFSG.ClassicalInvolution.Models.SymplecticPairs
