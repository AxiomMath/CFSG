module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M2Cocycle
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M2Basic

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin CFSG.Quasithin.JonesParshall

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {n : ℕ}

theorem exists_four_gf (hn : 2 ≤ n) : ∃ s : Finset (GaloisField 2 n), s.card = 4 := by
  have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 n (by omega)]
  obtain ⟨s, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (GaloisField 2 n)))
    (n := 4) (by
      rw [Finset.card_univ, hc]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
  exact ⟨s, hs.2⟩

theorem NatSec.isPerfect (S : NatSec n G) (hn : 2 ≤ n) : Group.IsPerfect ↥G := by
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect (exists_four_gf hn)
  exact Group.IsPerfect.ofSurjective (f := S.θ.symm.toMonoidHom) S.θ.symm.surjective

theorem NatSec.commV_ne_bot (S : NatSec n G) : commV G ≠ ⊥ := by
  intro h
  obtain ⟨u, hu⟩ := S.surj (Multiplicative.ofAdd (fun _ : Fin 2 => (1 : GaloisField 2 n)))
  have h1 : (u : V) = 1 := by
    have : (u : V) ∈ (⊥ : Subgroup V) := by rw [← h]; exact u.2
    exact Subgroup.mem_bot.1 this
  have h2 : u = 1 := Subtype.ext h1
  rw [h2, map_one] at hu
  have := congrFun (congrArg Multiplicative.toAdd hu) 0
  simp at this

section One

variable (S : NatSec n G) (hn : 2 ≤ n) (hV : ∀ v : V, v ^ 2 = 1)
  (hind : ∀ A B : Subgroup V, GInv G A → GInv G B → A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥)
  (ρ : Representation (ZMod 2) ↥G (Fin 2 → GaloisField 2 n))
  (hρ : ∀ (g : ↥G) (w : Fin 2 → GaloisField 2 n),
    ρ g w = (S.θ g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w)

include hn hV hind hρ in
theorem NatSec.mem_commV_of_lam (v : V) (hv : S.Lam ρ hρ v = 1) : v ∈ commV G := by
  have := S.isPerfect hn
  obtain ⟨z, hz⟩ := (S.Lam_eq_one_iff ρ hρ v).1 hv
  obtain ⟨u₀, hu₀⟩ := S.surj (Multiplicative.ofAdd z)
  have hdbl : ∀ w : Fin 2 → GaloisField 2 n, w + w = 0 := fun w =>
    funext fun i => CharTwo.add_self_eq_zero (w i)
  set v' : V := v * (u₀ : V) with hv'
  have hcv : ∀ g : ↥G, S.cv v' g = 0 := by
    intro g
    have h1 : S.cv v' g = S.cv v g + S.cv (u₀ : V) g := by
      rw [hv', S.cv_mul]
      rfl
    have h2 : S.cv v g = ρ g z - z := (congrFun hz g).symm
    have h3 : S.cv (u₀ : V) g = ρ g z - z := by
      rw [S.cv_apply_of_mem ρ hρ u₀.2 g]
      have : Multiplicative.toAdd (S.β ⟨(u₀ : V), u₀.2⟩) = z := by
        rw [hu₀]; rfl
      rw [this]
    rw [h1, h2, h3]
    exact hdbl _
  have hker : ∀ g : ↥G, (g : MulAut V) v' * v'⁻¹ ∈ commV G ⊓ fixV G := by
    intro g
    have h1 : S.β (commEl g v') = 1 := by
      have := hcv g
      exact Multiplicative.toAdd.injective (by simpa [NatSec.cv] using this)
    have h2 : commEl g v' ∈ S.β.ker := h1
    rw [S.ker, Subgroup.mem_subgroupOf] at h2
    exact h2
  let φ : ↥G →* ↥(commV G ⊓ fixV G) :=
    { toFun := fun g => ⟨(g : MulAut V) v' * v'⁻¹, hker g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => by
        apply Subtype.ext
        have h1 : ((commEl (g * h) v' : ↥(commV G)) : V) =
            (g : MulAut V) (commEl h v' : V) * (commEl g v' : V) :=
          congrArg Subtype.val (commEl_mul_left g h v')
        have h2 : (g : MulAut V) ((h : MulAut V) v' * v'⁻¹) = (h : MulAut V) v' * v'⁻¹ :=
          mem_fixV.1 (hker h).2 g g.2
        simp only [commEl_val] at h1
        rw [h2] at h1
        change ((g * h : ↥G) : MulAut V) v' * v'⁻¹ = _
        rw [h1, mul_comm]
        rfl }
  have hφ : ∀ g : ↥G, (g : MulAut V) v' * v'⁻¹ = 1 := fun g =>
    congrArg Subtype.val (eq_one_of_perfect φ g)
  have hfix : v' ∈ fixV G := fun x hx => mul_inv_eq_one.1 (hφ ⟨x, hx⟩)
  have hv'U : v' ∈ commV G := fixV_le_commV hV hind S.commV_ne_bot hfix
  have hvv : v = v' * (u₀ : V)⁻¹ := by rw [hv', mul_inv_cancel_right]
  rw [hvv]
  exact Subgroup.mul_mem _ hv'U (Subgroup.inv_mem _ u₀.2)

include hn hV hind hρ in
theorem NatSec.claim1 [Finite V] (hH : Nat.card (H1 ρ) ≤ 2 ^ n) :
    Nat.card V ≤ 2 ^ n * Nat.card ↥(commV G) := by
  have hker : (S.Lam ρ hρ).ker = commV G := by
    ext v
    rw [MonoidHom.mem_ker]
    constructor
    · exact S.mem_commV_of_lam hn hV hind ρ hρ v
    · intro hv
      exact (S.Lam_eq_one_iff ρ hρ v).2 (S.cv_mem_B1 ρ hρ hv)
  have hG : Finite ↥G := Finite.of_equiv _ S.θ.toEquiv.symm
  have hZ : Finite ↥(Z1 ρ) := Subtype.finite
  have hHf : Finite (H1 ρ) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (S.Lam ρ hρ).ker
  have h2 : Nat.card (V ⧸ (S.Lam ρ hρ).ker) = Nat.card (S.Lam ρ hρ).range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
  have h3 : Nat.card (S.Lam ρ hρ).range ≤ Nat.card (H1 ρ) :=
    calc Nat.card (S.Lam ρ hρ).range ≤ Nat.card (Multiplicative (H1 ρ)) :=
          Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = Nat.card (H1 ρ) := Nat.card_congr Multiplicative.toAdd
  have h4 : Nat.card ↥(S.Lam ρ hρ).ker = Nat.card ↥(commV G) := by rw [hker]
  calc Nat.card V = Nat.card (V ⧸ (S.Lam ρ hρ).ker) * Nat.card ↥(S.Lam ρ hρ).ker := h1
    _ ≤ 2 ^ n * Nat.card ↥(commV G) := by
        rw [h2, h4]
        exact Nat.mul_le_mul (h3.trans hH) le_rfl

end One

end CFSG.CGT.PushingUpLit.CGT6
