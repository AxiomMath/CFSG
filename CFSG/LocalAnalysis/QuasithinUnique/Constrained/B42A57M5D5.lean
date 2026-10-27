module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57M5Glue
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Real
public import CFSG.Quasithin.Background.B4ModelsAction

public section

namespace CFSG.QuasithinUnique.B42A57

open CFSG.Quasithin Multiplicative CFSG.QuasithinUnique.A5.Delta5 Equiv

theorem a0_pow : a0 ^ 5 = 1 := by decide +kernel

theorem b0_pow : b0 ^ 3 = 1 := by decide +kernel

theorem ab_pow : (a0 * b0) ^ 2 = 1 := by decide +kernel

theorem a0_ne : a0 ≠ 1 := by decide +kernel

@[expose] def psiD (c : V4) : Fin 5 → ZMod 2 := ![c 0, c 0 + c 1, c 1 + c 2, c 2 + c 3, c 3]

theorem psiD_even : ∀ c : V4, ∑ i, psiD c i = 0 := by decide +kernel

theorem psiD_zero : psiD 0 = 0 := by decide +kernel

theorem psiD_add : ∀ c c' : V4, psiD (c + c') = psiD c + psiD c' := by decide +kernel

theorem psiD_inj : ∀ c c' : V4, psiD c = psiD c' → c = c' := by decide +kernel

theorem psiD_surj : ∀ z : Fin 5 → ZMod 2, ∑ i, z i = 0 → ∃ c : V4, psiD c = z := by
  decide +kernel

@[expose] def PsiDHom : Multiplicative V4 →* ↥(G6.coreMod 5) where
  toFun c := ⟨ofAdd (psiD (toAdd c)), by rw [G6.mem_coreMod]; exact psiD_even _⟩
  map_one' := by
    apply Subtype.ext
    show ofAdd (psiD 0) = 1
    rw [psiD_zero]
    rfl
  map_mul' c c' := by
    apply Subtype.ext
    show ofAdd (psiD (toAdd c + toAdd c')) = ofAdd (psiD (toAdd c)) * ofAdd (psiD (toAdd c'))
    rw [psiD_add]
    rfl

theorem PsiDHom_bijective : Function.Bijective PsiDHom := by
  constructor
  · intro a b h
    have h1 : ((PsiDHom a : ↥(G6.coreMod 5)) : G6.PermMod 5) = (PsiDHom b : G6.PermMod 5) :=
      congrArg Subtype.val h
    have h2 : ofAdd (psiD (toAdd a)) = ofAdd (psiD (toAdd b)) := h1
    exact toAdd.injective (psiD_inj _ _ (ofAdd.injective h2))
  · intro z
    obtain ⟨c, hc⟩ := psiD_surj (toAdd (z : G6.PermMod 5)) (G6.mem_coreMod.1 z.2)
    refine ⟨ofAdd c, Subtype.ext ?_⟩
    show ofAdd (psiD c) = (z : G6.PermMod 5)
    rw [hc]
    rfl

@[expose] noncomputable def PsiD : Multiplicative V4 ≃* ↥(G6.coreMod 5) :=
  MulEquiv.ofBijective PsiDHom PsiDHom_bijective

theorem PsiD_apply (c : V4) : ((PsiD (ofAdd c) : ↥(G6.coreMod 5)) : G6.PermMod 5) =
    ofAdd (psiD c) := rfl

theorem act_a0_psi (c : V4) :
    G6.permAct 5 a0 (ofAdd (psiD c)) = ofAdd (psiD (lin wC c)) := by
  have key : ∀ (c : V4) (i : Fin 5), psiD c (a0⁻¹ i) = psiD (lin wC c) i := by decide +kernel
  apply toAdd.injective
  funext i
  exact key c i

theorem act_b0_psi (c : V4) :
    G6.permAct 5 b0 (ofAdd (psiD c)) = ofAdd (psiD (lin wD c)) := by
  have key : ∀ (c : V4) (i : Fin 5), psiD c (b0⁻¹ i) = psiD (lin wD c) i := by decide +kernel
  apply toAdd.injective
  funext i
  exact key c i

theorem altDn5_ker' : Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5 = (⊥ : Subgroup (G6.PermMod 5)) := by
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  rw [Subgroup.mem_bot]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz1
  have hsq : G6.allOnes 5 * G6.allOnes 5 = 1 := by decide +kernel
  have hnot : G6.allOnes 5 ∉ G6.coreMod 5 := by
    rw [G6.mem_coreMod]
    decide +kernel
  have hord : orderOf (G6.allOnes 5) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq) (by decide +kernel)
  have hmod := zpow_mod_orderOf (G6.allOnes 5) k
  rw [hord] at hmod
  simp only [Nat.cast_ofNat] at hmod
  rw [← hmod]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero]
  · exfalso
    apply hnot
    rw [← hmod, h, zpow_one] at hz2
    exact hz2

theorem altDn5_ker : (FFModel.altDn 5).ker = ⊥ := altDn5_ker'

theorem altDn5_faithful : (FFModel.altDn 5).Faithful := by
  intro (γ : ↥(alternatingGroup (Fin 5))) h
  apply Subtype.ext
  apply pact_faithful (γ : Perm (Fin 5))
  intro x hx
  funext i
  have h1 : G6.permAct 5 (γ : Perm (Fin 5)) (ofAdd x) * (ofAdd x : G6.PermMod 5)⁻¹ ∈
      Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5 :=
    h (ofAdd x : G6.PermMod 5) (by
      show (ofAdd x : G6.PermMod 5) ∈ G6.coreMod 5
      rw [G6.mem_coreMod]
      exact hx)
  rw [altDn5_ker', Subgroup.mem_bot] at h1
  have h2 : G6.permAct 5 (γ : Perm (Fin 5)) (ofAdd x) * (ofAdd x : G6.PermMod 5)⁻¹ = 1 := h1
  have h3 : G6.permAct 5 (γ : Perm (Fin 5)) (ofAdd x) = ofAdd x := mul_inv_eq_one.1 h2
  exact congrArg (fun m : G6.PermMod 5 => toAdd m i) h3

theorem eq_closure_of_equiv {S : Type} [CommGroup S] {L : Subgroup (MulAut S)}
    (ι : ↥L ≃* ↥(alternatingGroup (Fin 5))) :
    L = Subgroup.closure
      ({((ι.symm a0' : ↥L) : MulAut S), ((ι.symm b0' : ↥L) : MulAut S)} : Set (MulAut S)) := by
  have h1 : Subgroup.closure ({ι.symm a0', ι.symm b0'} : Set ↥L) = ⊤ := by
    have := congrArg (Subgroup.map ι.symm.toMonoidHom) closure_a5
    rw [MonoidHom.map_closure, Set.image_pair,
      Subgroup.map_top_of_surjective _ ι.symm.surjective] at this
    exact this
  have h2 := congrArg (Subgroup.map L.subtype) h1
  rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  exact h2.symm

theorem alternatingNatural_five_of_data {S : Type} [CommGroup S] (L : Subgroup (MulAut S))
    (hL60 : Nat.card ↥L = 60) (x y : MulAut S)
    (hL : L = Subgroup.closure ({x, y} : Set (MulAut S)))
    (θ : S ≃* Multiplicative V4) (w : Fin 4 → V4)
    (hθx : ∀ s, θ (x s) = ofAdd (lin wC (toAdd (θ s))))
    (hθy : ∀ s, θ (y s) = ofAdd (lin w (toAdd (θ s))))
    (c : V4) (hc : ∀ u, Tc c u = 0 → u = 0) (hD : ∀ u, Tc c (lin w u) = lin wD (Tc c u)) :
    AlternatingNatural L ⊤ ⊥ 5 := by
  let β : S ≃* ↥(G6.coreMod 5) := (θ.trans (TcEquiv c hc)).trans PsiD
  have hβ : ∀ s, ((β s : ↥(G6.coreMod 5)) : G6.PermMod 5) =
      ofAdd (psiD (Tc c (toAdd (θ s)))) := fun s => by
    show ((PsiD (TcEquiv c hc (θ s)) : ↥(G6.coreMod 5)) : G6.PermMod 5) = _
    rw [← ofAdd_toAdd (θ s), TcEquiv_apply, PsiD_apply, toAdd_ofAdd]
  have hx : ∀ s, ((β (x s) : ↥(G6.coreMod 5)) : G6.PermMod 5) = G6.permAct 5 a0 (β s) := by
    intro s
    rw [hβ, hβ, hθx, toAdd_ofAdd, Tc_comm, act_a0_psi]
  have hy : ∀ s, ((β (y s) : ↥(G6.coreMod 5)) : G6.PermMod 5) = G6.permAct 5 b0 (β s) := by
    intro s
    rw [hβ, hβ, hθy, toAdd_ofAdd, hD, act_b0_psi]
  have : Finite (FFModel.altDn 5).Gam := (inferInstance : Finite (alternatingGroup (Fin 5)))
  refine realizesMod_of_two_generators (FFModel.altDn_isActionModel 5) altDn5_ker altDn5_faithful L
    ?_ β x y a0' b0' hx hy hL
  show Nat.card ↥(alternatingGroup (Fin 5)) ≤ Nat.card ↥L
  rw [a5_card, hL60]

end CFSG.QuasithinUnique.B42A57
