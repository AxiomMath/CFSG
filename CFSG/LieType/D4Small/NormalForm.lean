module

public import CFSG.LieType.D4Small.Transport

public section

namespace CFSG.LieType.D4Small.D4Datum

attribute [local instance] Fintype.ofFinite Classical.propDecidable

open Finset Module

variable {G : Type*} [Group G] {K : Type*} [Field K] [Finite K] [CharP K 2]
  {D : D4Datum G K} {X : Type*} [AddCommGroup X] [Module K X] {ρ : Representation K G X}

structure IsNormalForm (D : D4Datum G K) (ρ : Representation K G X)
    (C : Finset (Fin 4 → ZMod (Nat.card Kˣ))) (j : ℕ)
    (b : (Fin 4 → ZMod (Nat.card Kˣ)) → X) : Prop where
  mem : ∀ a ∈ C, b a ≠ 0 ∧ b a ∈ D.wtSpace ρ a
  span_eq : Submodule.span K (b '' C) = ⊤
  act : ∀ α, IsD4Root α → ∀ c : K, ∀ a ∈ C, ρ (D.x α c) (b a) =
       b a + if a + (2 : ZMod (Nat.card Kˣ)) ^ j • castW _ α ∈ C then
         c ^ (2 ^ j) • b (a + (2 : ZMod (Nat.card Kˣ)) ^ j • castW _ α) else 0

namespace IsNormalForm

private theorem span_range_eq_top {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))} {j : ℕ}
    {b : (Fin 4 → ZMod (Nat.card Kˣ)) → X} (hb : IsNormalForm D ρ C j b) :
    Submodule.span K (Set.range (fun a : C => b a)) = ⊤ := by
  rw [show Set.range (fun a : C => b a) = b '' (C : Set (Fin 4 → ZMod (Nat.card Kˣ))) from by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.1, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩]
  exact hb.span_eq

theorem linearIndependent {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))} {j : ℕ}
    {b : (Fin 4 → ZMod (Nat.card Kˣ)) → X} (hb : IsNormalForm D ρ C j b) :
    LinearIndependent K (fun a : C => b a) :=
  linearIndependent_of_mem_wtSpace hb.mem

theorem rho_h {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))} {j : ℕ}
    {b : (Fin 4 → ZMod (Nat.card Kˣ)) → X} (hb : IsNormalForm D ρ C j b)
    (t : Fin 4 → Kˣ) {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C) :
    ρ (D.h t) (b a) = (wtChar a t : K) • b a :=
  (mem_wtSpace (D := D) (ρ := ρ)).mp (hb.mem a ha).2 t

noncomputable def basis {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))} {j : ℕ}
    {b : (Fin 4 → ZMod (Nat.card Kˣ)) → X} (hb : IsNormalForm D ρ C j b) : Basis C K X :=
  Basis.mk hb.linearIndependent (by rw [span_range_eq_top hb])

theorem basis_apply {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))} {j : ℕ}
    {b : (Fin 4 → ZMod (Nat.card Kˣ)) → X} (hb : IsNormalForm D ρ C j b) (a : C) :
    hb.basis a = b a := by
  simp only [IsNormalForm.basis]
  exact Basis.mk_apply hb.linearIndependent _ a

end IsNormalForm

variable {Y : Type*} [AddCommGroup Y] [Module K Y] {ρ' : Representation K G Y}
  {b' : (Fin 4 → ZMod (Nat.card Kˣ)) → Y}

namespace IsNormalForm

theorem exists_equiv {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))} {j : ℕ}
    {b : (Fin 4 → ZMod (Nat.card Kˣ)) → X} (hb : IsNormalForm D ρ C j b)
    (hb' : IsNormalForm D ρ' C j b') :
    ∃ e : X ≃ₗ[K] Y, (∀ a ∈ C, e (b a) = b' a) ∧ ∀ g x, e (ρ g x) = ρ' g (e x) := by
  let e : X ≃ₗ[K] Y := hb.basis.equiv hb'.basis (Equiv.refl C)
  let E : X →ₗ[K] Y := e.toLinearMap
  have he : ∀ a : C, E (b a) = b' a := by
    intro a
    rw [← hb.basis_apply a, ← hb'.basis_apply a]
    simp [E, e]
  let S : Subgroup G :=
    { carrier := {g | ∀ x : X, e (ρ g x) = ρ' g (e x)}
      one_mem' := by
        intro x
        simp
      mul_mem' := by
        intro g h hg hh x
        calc e (ρ (g * h) x) = e (ρ g (ρ h x)) := by
              simp only [map_mul, Module.End.mul_apply]
          _ = ρ' g (e (ρ h x)) := hg _
          _ = ρ' g (ρ' h (e x)) := by rw [hh]
          _ = ρ' (g * h) (e x) := by
              simp only [map_mul, Module.End.mul_apply]
      inv_mem' := by
        intro g hg x
        have h1 : ρ' g (e (ρ g⁻¹ x)) = e x := by
          rw [← hg (ρ g⁻¹ x)]
          simp
        have h2 : ρ' g (ρ' g⁻¹ (e x)) = e x := by simp
        exact (ρ'.apply_bijective g).injective (h1.trans h2.symm) }
  have hgen : ∀ g ∈ {g : G | ∃ α, IsD4Root α ∧ ∃ c, D.x α c = g}, g ∈ S := by
    rintro g ⟨α, hα, c, rfl⟩ x
    have hmap : E ∘ₗ ρ (D.x α c) = ρ' (D.x α c) ∘ₗ E := by
      refine hb.basis.ext ?_
      intro a
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hb.basis_apply, he a]
      rw [hb.act α hα c a a.2, hb'.act α hα c a a.2]
      by_cases hm : (a : Fin 4 → ZMod (Nat.card Kˣ)) +
          (2 : ZMod (Nat.card Kˣ)) ^ j • castW _ α ∈ C
      · rw [if_pos hm, if_pos hm, map_add, map_smul, he a, he ⟨_, hm⟩]
      · rw [if_neg hm, if_neg hm, map_add, map_zero, he a]
    exact congrArg (fun f : X →ₗ[K] Y => f x) hmap
  have hS : S = ⊤ := by
    have hle : Subgroup.closure {g : G | ∃ α, IsD4Root α ∧ ∃ c, D.x α c = g} ≤ S :=
      (Subgroup.closure_le S).mpr hgen
    rw [D.closure_eq] at hle
    exact eq_top_iff.mpr hle
  have hall : ∀ g : G, g ∈ S := by
    intro g
    rw [hS]
    exact Subgroup.mem_top g
  exact ⟨e, fun a ha => by simpa [E] using he ⟨a, ha⟩, fun g x => hall g x⟩

private theorem exists_mem_ne_neg_of_isSmallClass {N : ℕ} {σ : ZMod N}
    {C : Finset (Fin 4 → ZMod N)} (hC : IsSmallClass N σ C)
    {a : Fin 4 → ZMod N} (ha : a ∈ C) : ∃ m ∈ C, m ≠ a ∧ m ≠ -a := by
  have h2 : ({a, -a} : Finset (Fin 4 → ZMod N)).card ≤ 2 := by
    have h1 := Finset.card_insert_le a ({-a} : Finset (Fin 4 → ZMod N))
    have h0 : ({-a} : Finset (Fin 4 → ZMod N)).card ≤ 1 := by simp
    omega
  have hlt : ({a, -a} : Finset (Fin 4 → ZMod N)).card < C.card := by
    rw [hC.card_eq]
    omega
  obtain ⟨m, hm, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
  exact ⟨m, hm, hnot.1, hnot.2⟩

private theorem exists_eq_smul_b {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))} {j : ℕ}
    {b : (Fin 4 → ZMod (Nat.card Kˣ)) → X} (hb : IsNormalForm D ρ C j b)
    {T : Module.End K X} (hT : ∀ g, T * ρ g = ρ g * T) (a : C) :
    ∃ c : K, T (b a) = c • b a := by
  have hTwt : T (b a) ∈ D.wtSpace ρ a := by
    rw [mem_wtSpace]
    intro t
    have h := congrArg (fun f : Module.End K X => f (b a)) (hT (D.h t))
    simp only [Module.End.mul_apply] at h
    rw [hb.rho_h t a.2, map_smul] at h
    exact h.symm
  let d : C → K := fun x => hb.basis.repr (T (b a)) x
  have hsum : T (b a) = ∑ x : C, d x • b x := by
    rw [show T (b a) = ∑ x : C, hb.basis.repr (T (b a)) x • hb.basis x from
      (hb.basis.sum_repr (T (b a))).symm]
    simp only [d, hb.basis_apply]
  have hd : ∀ x : C, (x : Fin 4 → ZMod (Nat.card Kˣ)) ≠ a → d x = 0 := by
    intro x hxne
    have hz : wtProj D ρ x (T (b a)) = 0 := by
      rw [wtProj_of_mem (D := D) (ρ := ρ) (a := (x : _)) (b := (a : _)) hTwt]
      exact if_neg hxne
    have h := congrArg (fun z : X => wtProj D ρ x z) hsum
    rw [hz, map_sum] at h
    have hsingle : (∑ y : C, wtProj D ρ x (d y • b y)) =
        wtProj D ρ x (d x • b x) := by
      refine Finset.sum_eq_single_of_mem
        (f := fun y : C => wtProj D ρ x (d y • b y)) x (Finset.mem_univ x) ?_
      intro y _ hy
      rw [map_smul, wtProj_of_mem (D := D) (ρ := ρ) (a := (x : _)) (b := (y : _))
        (hb.mem y y.2).2]
      rw [if_neg (fun hxy => hy (Subtype.ext hxy.symm))]
      exact smul_zero _
    rw [hsingle, map_smul, wtProj_of_mem (D := D) (ρ := ρ) (a := (x : _)) (b := (x : _))
      (hb.mem x x.2).2, if_pos rfl] at h
    have hc := congrArg (fun z : X => hb.basis.repr z x) h.symm
    simpa [d, ← hb.basis_apply] using hc
  refine ⟨d a, ?_⟩
  rw [hsum]
  refine Finset.sum_eq_single_of_mem
    (f := fun y : C => d y • b y) a (Finset.mem_univ a) ?_
  intro x _ hx
  rw [hd x (fun hxa => hx (Subtype.ext hxa))]
  exact zero_smul K _

private theorem coeff_step {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))} {j : ℕ}
    {b : (Fin 4 → ZMod (Nat.card Kˣ)) → X} (hb : IsNormalForm D ρ C j b)
    {T : Module.End K X} (hT : ∀ g, T * ρ g = ρ g * T) {ca ca' : K} {a a' : C}
    {α : Fin 4 → ℤ} (hα : IsD4Root α)
    (h : (a' : Fin 4 → ZMod (Nat.card Kˣ)) =
      (a : Fin 4 → ZMod (Nat.card Kˣ)) + (2 : ZMod (Nat.card Kˣ)) ^ j • castW _ α)
    (hca : T (b a) = ca • b a) (hca' : T (b a') = ca' • b a') : ca' = ca := by
  have hcond : (a : Fin 4 → ZMod (Nat.card Kˣ)) +
      (2 : ZMod (Nat.card Kˣ)) ^ j • castW _ α ∈ C := by
    rw [← h]
    exact a'.2
  have hact : ρ (D.x α 1) (b a) = b a + b a' := by
    rw [hb.act α hα 1 a a.2, if_pos hcond, h.symm]
    simp
  have h := congrArg (fun f : Module.End K X => f (b a)) (hT (D.x α 1))
  simp only [Module.End.mul_apply] at h
  rw [hact, map_add, hca, hca', map_smul, hact, smul_add] at h
  have hcoef := congrArg (fun z : X => hb.basis.repr z a') (add_left_cancel h)
  simpa [← hb.basis_apply] using hcoef

theorem exists_eq_smul {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))} {j : ℕ}
    {b : (Fin 4 → ZMod (Nat.card Kˣ)) → X} (hb : IsNormalForm D ρ C j b)
    (hC : IsSmallClass (Nat.card Kˣ) ((2 : ZMod (Nat.card Kˣ)) ^ j) C)
    {T : Module.End K X} (hT : ∀ g, T * ρ g = ρ g * T) : ∃ c : K, T = c • 1 := by
  choose c hc using fun a => exists_eq_smul_b hb hT a
  have hstep : ∀ (a a' : C) (α : Fin 4 → ℤ), IsD4Root α →
      (a' : Fin 4 → ZMod (Nat.card Kˣ)) =
        (a : Fin 4 → ZMod (Nat.card Kˣ)) +
          (2 : ZMod (Nat.card Kˣ)) ^ j • castW _ α → c a' = c a :=
    fun a a' α hα h => coeff_step hb hT hα h (hc a) (hc a')
  obtain ⟨a₀, ha₀⟩ := Finset.card_pos.mp (by rw [hC.card_eq]; norm_num)
  let a₀' : C := ⟨a₀, ha₀⟩
  have hthird : ∃ m : C, (m : Fin 4 → ZMod (Nat.card Kˣ)) ≠ a₀ ∧
      (m : Fin 4 → ZMod (Nat.card Kˣ)) ≠ -a₀ := by
    obtain ⟨m, hm, hma, hna⟩ := exists_mem_ne_neg_of_isSmallClass hC ha₀
    exact ⟨⟨m, hm⟩, hma, hna⟩
  have hall : ∀ a : C, c a = c a₀' := by
    intro a
    by_cases ha : (a : Fin 4 → ZMod (Nat.card Kˣ)) = a₀
    · have h : a = a₀' := Subtype.ext ha
      rw [h]
    · by_cases hna : (a : Fin 4 → ZMod (Nat.card Kˣ)) = -a₀
      · obtain ⟨m, hm1, hm2⟩ := hthird
        obtain ⟨γ, hγ, hγm⟩ := hC.adj a₀ ha₀ (m : _) m.2 hm1 hm2
        have h1 : c m = c a₀' := hstep a₀' m γ hγ hγm
        have hne1 : (a : Fin 4 → ZMod (Nat.card Kˣ)) ≠ (m : _) := by
          rw [hna]
          exact fun h => hm2 h.symm
        have hne2 : (a : Fin 4 → ZMod (Nat.card Kˣ)) ≠ -(m : _) := by
          rw [hna]
          exact fun h => hm1 (neg_injective h).symm
        obtain ⟨δ, hδ, hδa⟩ := hC.adj (m : _) m.2 (a : _) a.2 hne1 hne2
        have h2 : c a = c m := hstep m a δ hδ hδa
        rw [h2, h1]
      · obtain ⟨γ, hγ, hγa⟩ := hC.adj a₀ ha₀ (a : _) a.2 ha hna
        exact hstep a₀' a γ hγ hγa
  refine ⟨c a₀', ?_⟩
  refine hb.basis.ext fun a => ?_
  rw [hb.basis_apply a]
  simp only [LinearMap.smul_apply, Module.End.one_apply]
  rw [hc a, hall a]

end IsNormalForm

end CFSG.LieType.D4Small.D4Datum
