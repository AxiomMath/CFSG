module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57M5Cyc
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57M5D5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57M5Nat

public section

namespace CFSG.QuasithinUnique.B42A57

open CFSG.Quasithin CFSG.QuasithinUnique.A5.Delta5 Multiplicative

theorem m5_classification {S : Type} [CommGroup S] [Finite S] (hS : ∀ s : S, s * s = 1)
    (hcard : Nat.card S = 16) (L : Subgroup (MulAut S))
    (ι : ↥L ≃* ↥(alternatingGroup (Fin 5))) :
    BinaryNaturalSL L ⊤ ⊥ 2 2 ∨ AlternatingNatural L ⊤ ⊥ 5 := by
  set x : MulAut S := ((ι.symm a0' : ↥L) : MulAut S) with hxdef
  set y : MulAut S := ((ι.symm b0' : ↥L) : MulAut S) with hydef
  have hL60 : Nat.card ↥L = 60 := by
    rw [Nat.card_congr ι.toEquiv, a5_card]
  have hx5 : x ^ 5 = 1 := by
    have h : (ι.symm a0') ^ 5 = 1 := by
      rw [← map_pow, show a0' ^ 5 = 1 from Subtype.ext a0_pow, map_one]
    have := congrArg Subtype.val h
    simpa using this
  have hy3 : y ^ 3 = 1 := by
    have h : (ι.symm b0') ^ 3 = 1 := by
      rw [← map_pow, show b0' ^ 3 = 1 from Subtype.ext b0_pow, map_one]
    have := congrArg Subtype.val h
    simpa using this
  have hxy2 : (x * y) ^ 2 = 1 := by
    have h : (ι.symm a0' * ι.symm b0') ^ 2 = 1 := by
      rw [← map_mul, ← map_pow, show (a0' * b0') ^ 2 = 1 from Subtype.ext ab_pow, map_one]
    have := congrArg Subtype.val h
    simpa using this
  have hx1 : x ≠ 1 := by
    intro h
    have h1 : ι.symm a0' = 1 := Subtype.ext h
    have h2 : a0' = 1 := by
      have := congrArg ι h1
      simpa using this
    exact a0_ne (congrArg Subtype.val h2)
  have hL : L = Subgroup.closure ({x, y} : Set (MulAut S)) := eq_closure_of_equiv ι
  obtain ⟨θ, hθx⟩ := exists_cyclic_coords hS hcard x hx5 hx1
  obtain ⟨w, hθy⟩ := exists_cols θ y
  have hy3' : ∀ s, y (y (y s)) = s := fun s => by
    have : y * y * y = 1 := by simpa [pow_succ] using hy3
    simpa [MulAut.mul_apply] using congrArg (fun f : MulAut S => f s) this
  have hxy' : ∀ s, x (y (x (y s))) = s := fun s => by
    have : (x * y) * (x * y) = 1 := by simpa [pow_two] using hxy2
    simpa [MulAut.mul_apply] using congrArg (fun f : MulAut S => f s) this
  have h3 : ∀ u, lin w (lin w (lin w u)) = u := by
    intro u
    have key := congrArg (fun z => toAdd (θ z)) (hy3' (θ.symm (ofAdd u)))
    simp only [hθy, toAdd_ofAdd, MulEquiv.apply_symm_apply] at key
    simpa using key
  have h2 : ∀ u, lin wC (lin w (lin wC (lin w u))) = u := by
    intro u
    have key := congrArg (fun z => toAdd (θ z)) (hxy' (θ.symm (ofAdd u)))
    simp only [hθx, hθy, toAdd_ofAdd, MulEquiv.apply_symm_apply] at key
    simpa using key
  obtain ⟨c, hc, hcase⟩ := classify w h3 h2
  rcases hcase with hD | hN
  · exact Or.inr (alternatingNatural_five_of_data L hL60 x y hL θ w hθx hθy c hc hD)
  · exact Or.inl (binaryNaturalSL_two_two_of_data L hL60 x y hL θ w hθx hθy c hc hN)

end CFSG.QuasithinUnique.B42A57
