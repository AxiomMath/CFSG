module

public import CFSG.CGT.PushingUpLit.CGT6.Diag.IdentSetup
public import CFSG.CGT.PushingUpLit.CGT6.Diag.IdentField
public import CFSG.CGT.PushingUpLit.CGT6.Diag.IdentRep
public import CFSG.CGT.PushingUpLit.CGT6.Diag.IdentEmbed
public import CFSG.CGT.PushingUpLit.CGT6.Diag.IdentNum

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6.Diag.Ident
open scoped Matrix

theorem diagModIdent_holds : DiagMod_ident := by
  intro V _ _ hV K K' n hn hcomm hθ₀ hcardK' W hW hnt hWcard k₀ hk₀ hinf hsup
  classical
  obtain ⟨θ₀⟩ := hθ₀
  have hWinv : ∀ k ∈ K, ∀ w ∈ W, k w ∈ W := hW.2.1
  let ρ : ↥K →* AddMonoid.End (Additive ↥W) := actW K W hWinv
  have hAnt : Nontrivial (Additive ↥W) := by
    obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW.1
    exact ⟨⟨0, Additive.ofMul w, fun h => hw (Additive.ofMul.injective h).symm⟩⟩
  obtain ⟨E, hF, hMod, hFin, hlin, hscal⟩ := exists_endField ρ (hsimple_of_minInv hW)
  have hKsimple : IsSimpleGroup ↥K := by
    have := sl2Fq_isSimple hn
    exact MulEquiv.isSimpleGroup θ₀
  have hKperf : Group.IsPerfect ↥K := by
    have := sl2Fq_isPerfect hn
    exact Group.IsPerfect.ofSurjective (f := θ₀.symm.toMonoidHom) θ₀.symm.surjective
  have hcardK : Nat.card ↥K = 2 ^ n * (2 ^ (2 * n) - 1) := by
    rw [Nat.card_congr θ₀.toEquiv, card_sl2_fq (by omega)]
  have hnt' : ∃ (k : ↥K) (a : Additive ↥W), ρ k a ≠ a := by
    obtain ⟨k, hk, w, hw, hkw⟩ := hnt
    refine ⟨⟨k, hk⟩, Additive.ofMul ⟨w, hw⟩, fun h => hkw ?_⟩
    exact congrArg (fun x : Additive ↥W => ((Additive.toMul x : W) : V)) h
  have hd0 : 0 < Module.finrank E (Additive ↥W) := Module.finrank_pos
  have hd1 : Module.finrank E (Additive ↥W) ≠ 1 := finrank_ne_one ρ hlin hnt'
  have hAcard : Nat.card (Additive ↥W) = 2 ^ (2 * n) := by
    rw [Nat.card_congr (Additive.toMul : Additive ↥W ≃ ↥W)]
    exact hWcard
  have hcardA : Nat.card (Additive ↥W) = Nat.card E ^ Module.finrank E (Additive ↥W) :=
    Module.natCard_eq_pow_finrank
  obtain ⟨e, -, hEe⟩ : ∃ e, e ≤ 2 * n ∧ Nat.card E = 2 ^ e := by
    have hdvd : Nat.card E ∣ 2 ^ (2 * n) := by
      rw [← hAcard, hcardA]
      exact dvd_pow_self _ hd0.ne'
    exact (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have he1 : 1 ≤ e := by
    by_contra hcon
    have he0 : e = 0 := by omega
    have h1 : Nat.card E = 1 := by rw [hEe, he0]; rfl
    have : Nontrivial E := inferInstance
    have h2 : 1 < Nat.card E := Finite.one_lt_card
    omega
  have hed : e * Module.finrank E (Additive ↥W) = 2 * n := by
    have h1 : 2 ^ (2 * n) = 2 ^ (e * Module.finrank E (Additive ↥W)) := by
      rw [← hAcard, hcardA, hEe, ← pow_mul]
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  have hcommK : ∀ (g : ↥K) (g' : ↥K') (v : V), (g' : MulAut V) ((g : MulAut V) v) =
      (g : MulAut V) ((g' : MulAut V) v) := fun g g' v =>
    congrArg (fun m : MulAut V => m v) (hcomm g g.2 g' g'.2).symm
  have hk₀K : ∀ (g : ↥K) (v : V), k₀ ((g : MulAut V) v) = (g : MulAut V) (k₀ v) := fun g v =>
    congrArg (fun m : MulAut V => m v) (hcomm g g.2 k₀ hk₀).symm
  let Φ : Additive ↥W × Additive ↥W ≃+ Additive V :=
    AddEquiv.ofBijective (phiMap W k₀) (phiMap_bijective hinf hsup)
  have hΦ : ∀ (g : ↥K) (x y : Additive ↥W), Φ (ρ g x, ρ g y) = actV K g (Φ (x, y)) := by
    intro g x y
    show phiMap W k₀ (actW K W hWinv g x, actW K W hWinv g y) =
      actV K g (phiMap W k₀ (x, y))
    rw [phiMap_apply, phiMap_apply, actV_apply, actW_apply, actW_apply]
    simp only [toMul_ofMul, map_mul, hk₀K]
  have hcommB : ∀ (g : ↥K) (g' : ↥K') (b : Additive V),
      actV K' g' (actV K g b) = actV K g (actV K' g' b) := fun g g' b => by
    simp only [actV_apply, toMul_ofMul]
    rw [hcommK]
  have hfaith : ∀ g' : ↥K', (∀ b, actV K' g' b = b) → g' = 1 := by
    intro g' h
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    exact Additive.ofMul.injective (h (Additive.ofMul v))
  obtain ⟨f, hf⟩ := exists_embed_matrix (E := E) ρ (actV K) (actV K') Φ hΦ hcommB hscal hfaith
  let f' : ↥K' →* Matrix.GeneralLinearGroup (Fin 2) E := f.toHomUnits
  have hf' : Function.Injective f' := by
    intro a b hab
    apply hf
    exact congrArg (fun u : (Matrix (Fin 2) (Fin 2) E)ˣ => (u : Matrix (Fin 2) (Fin 2) E)) hab
  have hdvd : Nat.card ↥K' ∣ Nat.card (Matrix.GeneralLinearGroup (Fin 2) E) :=
    Subgroup.card_dvd_of_injective f' hf'
  have hnle : n ≤ e := by
    have : Fintype E := Fintype.ofFinite E
    have hGL := Matrix.card_GL_field (𝔽 := E) 2
    have hcardE : Fintype.card E = 2 ^ e := by rw [Fintype.card_eq_nat_card, hEe]
    rw [hGL, hcardE] at hdvd
    simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one] at hdvd
    apply n_le_e he1
    refine Dvd.dvd.trans ?_ hdvd
    rw [hcardK', hcardK]
    exact Dvd.intro _ rfl
  obtain ⟨hd2, hen⟩ := e_d_eq (by omega) hed hnle (by omega)
  have : Fintype E := Fintype.ofFinite E
  have : Fintype (Fq n) := Fintype.ofFinite (Fq n)
  have hcardEq : Fintype.card E = Fintype.card (Fq n) := by
    rw [Fintype.card_eq_nat_card, hEe, hen, Fintype.card_eq_nat_card,
      GaloisField.card 2 n (by omega)]
  let ι : E ≃+* Fq n := FiniteField.ringEquivOfCardEq hcardEq
  obtain ⟨θ, β, hβ⟩ := exists_natSection ι ρ hlin hd2 hnt' (Nat.card_congr θ₀.toEquiv)
  refine ⟨θ, hWinv, ?_⟩
  let β' : ↥W →* Multiplicative (Fin 2 → Fq n) :=
    { toFun := fun w => Multiplicative.ofAdd (β (Additive.ofMul w))
      map_one' := by
        show Multiplicative.ofAdd (β 0) = 1
        rw [map_zero]
        rfl
      map_mul' := fun x y => by
        show Multiplicative.ofAdd (β (Additive.ofMul (x * y))) = _
        rw [ofMul_mul, map_add]
        rfl }
  refine ⟨β', ?_, ?_, ?_⟩
  · intro m
    refine ⟨Additive.toMul (β.symm (Multiplicative.toAdd m)), ?_⟩
    show Multiplicative.ofAdd
      (β (Additive.ofMul (Additive.toMul (β.symm (Multiplicative.toAdd m))))) = m
    rw [ofMul_toMul, AddEquiv.apply_symm_apply]
    rfl
  · ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    constructor
    · intro h
      have h1 : β (Additive.ofMul w) = 0 := Multiplicative.ofAdd.injective h
      have h2 : Additive.ofMul w = 0 := β.injective (h1.trans (map_zero β).symm)
      exact congrArg (fun x : Additive ↥W => ((Additive.toMul x : W) : V)) h2
    · intro h
      have h1 : w = 1 := Subtype.ext h
      rw [h1, map_one]
  · intro x p hp
    show Multiplicative.ofAdd (β (Additive.ofMul ⟨(x : MulAut V) p, hp⟩)) =
      Multiplicative.ofAdd ((θ x : Matrix (Fin 2) (Fin 2) (Fq n)) *ᵥ β (Additive.ofMul p))
    exact congrArg Multiplicative.ofAdd (hβ x (Additive.ofMul p))

end CFSG.CGT.PushingUpLit.CGT6
