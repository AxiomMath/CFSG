module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.Malle.Proving

theorem card_ker_comp_le {A : Type} [AddCommGroup A] [Finite A] (f g : A →+ A) :
    Nat.card (g.comp f).ker ≤ Nat.card f.ker * Nat.card g.ker := by
  let h : (g.comp f).ker →+ g.ker :=
    { toFun := fun x => ⟨f x.1, AddMonoidHom.mem_ker.mpr (AddMonoidHom.mem_ker.mp x.2)⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  have hk : Nat.card h.ker ≤ Nat.card f.ker := by
    refine Nat.card_le_card_of_injective (fun x => ⟨x.1.1, ?_⟩) ?_
    · have hx : h x.1 = 0 := AddMonoidHom.mem_ker.mp x.2
      exact AddMonoidHom.mem_ker.mpr (congrArg Subtype.val hx)
    · intro x y hxy
      have h1 := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h1)
  have hr : Nat.card h.range ≤ Nat.card g.ker :=
    Nat.card_le_card_of_injective (fun x => x.1) (fun _ _ hxy => Subtype.ext hxy)
  calc Nat.card (g.comp f).ker = Nat.card h.ker * Nat.card h.range :=
        (AddSubgroup.card_ker_mul_card_range h).symm
    _ ≤ Nat.card f.ker * Nat.card g.ker := Nat.mul_le_mul hk hr

theorem card_le_card_ker_cube {A : Type} [AddCommGroup A] [Finite A] (N : A →+ A)
    (hN : ∀ a, N (N (N a)) = 0) :
    Nat.card A ≤ Nat.card N.ker ^ 3 := by
  have htop : Nat.card A = Nat.card (N.comp (N.comp N)).ker := by
    refine Nat.card_congr (Equiv.subtypeUnivEquiv (fun a => ?_)).symm
    exact AddMonoidHom.mem_ker.mpr (hN a)
  have h3 := card_ker_comp_le (N.comp N) N
  have h2 := card_ker_comp_le N N
  rw [htop]
  calc Nat.card (N.comp (N.comp N)).ker ≤ Nat.card (N.comp N).ker * Nat.card N.ker := h3
    _ ≤ (Nat.card N.ker * Nat.card N.ker) * Nat.card N.ker := Nat.mul_le_mul_right _ h2
    _ = Nat.card N.ker ^ 3 := by ring

theorem card_le_card_ker_sub_id_cube {B : Type} [AddCommGroup B] [Finite B]
    (hB : ∀ b : B, (3 : ℕ) • b = 0) (ψ : B →+ B) (hψ : ∀ b, ψ (ψ (ψ b)) = b) :
    Nat.card B ≤ Nat.card (ψ - AddMonoidHom.id B).ker ^ 3 := by
  apply card_le_card_ker_cube (ψ - AddMonoidHom.id B)
  intro a
  have e : (ψ - AddMonoidHom.id B) ((ψ - AddMonoidHom.id B) ((ψ - AddMonoidHom.id B) a))
      = ψ (ψ (ψ a)) - (3 : ℕ) • ψ (ψ a) + (3 : ℕ) • ψ a - a := by
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.id_apply, map_sub]
    abel
  rw [e, hψ, hB (ψ (ψ a)), hB (ψ a)]
  simp

theorem card_le_card_inf_centralizer_cube {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA3 : ∀ a ∈ A, a ^ 3 = 1) {u : G} (hu : u ^ 3 = 1)
    (huA : ∀ a ∈ A, u * a * u⁻¹ ∈ A) :
    Nat.card A ≤ Nat.card (A ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) ^ 3 := by
  let _inst : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := fun x y => Subtype.ext (hAc x.1 x.2 y.1 y.2) }
  let cA : A →* A :=
    ((MulAut.conj u).toMonoidHom.comp A.subtype).codRestrict A (fun a => huA a a.2)
  let cAd : Additive A →+ Additive A := MonoidHom.toAdditive cA
  have : Finite (Additive A) := (inferInstance : Finite A)
  have hexp : ∀ x : Additive A, (3 : ℕ) • x = 0 := by
    intro x
    have h3 : (Additive.toMul x) ^ 3 = 1 := Subtype.ext (hA3 _ (Additive.toMul x).2)
    show Additive.ofMul ((Additive.toMul x) ^ 3) = Additive.ofMul 1
    rw [h3]
  have hψ : ∀ b : Additive A, cAd (cAd (cAd b)) = b := by
    intro b
    apply Additive.toMul.injective
    apply Subtype.ext
    show u * (u * (u * ((Additive.toMul b : A) : G) * u⁻¹) * u⁻¹) * u⁻¹
        = ((Additive.toMul b : A) : G)
    have hu' : u * u * u = 1 := by simpa [pow_succ, mul_assoc] using hu
    have e : u * (u * (u * ((Additive.toMul b : A) : G) * u⁻¹) * u⁻¹) * u⁻¹
        = (u * u * u) * ((Additive.toMul b : A) : G) * (u * u * u)⁻¹ := by group
    rw [e, hu']
    simp
  have h := card_le_card_ker_sub_id_cube hexp cAd hψ
  have mem : ∀ x : (cAd - AddMonoidHom.id _).ker,
      ((Additive.toMul x.1 : A) : G) ∈ (A ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) := by
    intro x
    have hx : cAd x.1 = x.1 := sub_eq_zero.mp (AddMonoidHom.mem_ker.mp x.2)
    have hc : u * ((Additive.toMul x.1 : A) : G) * u⁻¹ = ((Additive.toMul x.1 : A) : G) :=
      congrArg Subtype.val (congrArg Additive.toMul hx)
    rw [Subgroup.mem_inf]
    refine ⟨(Additive.toMul x.1).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    rw [hk]
    calc u * ((Additive.toMul x.1 : A) : G)
        = (u * ((Additive.toMul x.1 : A) : G) * u⁻¹) * u := by group
      _ = ((Additive.toMul x.1 : A) : G) * u := by rw [hc]
  have hk : Nat.card (cAd - AddMonoidHom.id _).ker
      ≤ Nat.card (A ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨((Additive.toMul x.1 : A) : G), mem x⟩ :
        (A ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G))) ?_
    intro x y hxy
    have h1 := congrArg Subtype.val hxy
    exact Subtype.ext (Additive.toMul.injective (Subtype.ext h1))
  calc Nat.card A = Nat.card (Additive A) := rfl
    _ ≤ Nat.card (cAd - AddMonoidHom.id _).ker ^ 3 := h
    _ ≤ Nat.card (A ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) ^ 3 :=
        Nat.pow_le_pow_left hk 3

end CFSG.HardMathSupport.Malle.Proving

end
