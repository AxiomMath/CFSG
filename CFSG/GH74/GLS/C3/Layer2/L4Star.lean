module

public import CFSG.GH74.GLS.C3.Layer2.L4Wreath
public import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import CFSG.GH74.GLS.C3.Layer3.AltInvolutions

public section

namespace CFSG.GH74.GLS.C3.Layer2.L4.Star

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2.L4.Wreath CFSG.GH74.GLS.Layer3
  CFSG.GH74.GLS.C3.Layer2

abbrev Ω8 : Type := Fin 4 × Fin 2

theorem swap01_sq : (swap (0 : Fin 2) 1) * swap 0 1 = 1 := Equiv.swap_mul_self _ _

@[expose] def th0 : N4 →* Perm Ω8 where
  toFun ε := Equiv.prodCongrRight (fun i => unitsHom (swap (0 : Fin 2) 1) swap01_sq (ε i))
  map_one' := by
    ext ⟨i, j⟩ <;> simp
  map_mul' ε ε' := by
    ext ⟨i, j⟩ <;> simp [Perm.mul_apply]

theorem th0_apply (ε : N4) (i : Fin 4) (j : Fin 2) :
    th0 ε (i, j) = (i, unitsHom (swap (0 : Fin 2) 1) swap01_sq (ε i) j) := rfl

theorem th0_injective : Function.Injective th0 := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro ε hε
  rw [MonoidHom.mem_ker] at hε
  refine Subgroup.mem_bot.2 (funext fun i => ?_)
  have h := congrArg (fun g : Perm Ω8 => g (i, 0)) hε
  simp only [th0_apply, Perm.one_apply, Prod.mk.injEq, true_and] at h
  rcases Int.units_eq_one_or (ε i) with h1 | h1
  · simpa using h1
  · rw [h1, unitsHom_neg_one] at h
    simp at h

@[expose] def sBlock : Perm (Fin 4) →* Perm Ω8 where
  toFun π := Equiv.prodCongr π (Equiv.refl _)
  map_one' := by ext ⟨i, j⟩ <;> simp
  map_mul' π π' := by ext ⟨i, j⟩ <;> simp [Perm.mul_apply]

theorem sBlock_apply (π : Perm (Fin 4)) (i : Fin 4) (j : Fin 2) :
    sBlock π (i, j) = (π i, j) := rfl

theorem th0_compat' (π : Perm (Fin 4)) (ε : N4) :
    th0 (act π ε) * sBlock π = sBlock π * th0 ε := by
  ext ⟨i, j⟩
  · simp [th0_apply, sBlock_apply, Perm.mul_apply, act]
  · simp [th0_apply, sBlock_apply, Perm.mul_apply, act]

theorem th0_compat (π : Perm (Fin 4)) (ε : N4) :
    th0 (act π ε) = sBlock π * th0 ε * (sBlock π)⁻¹ := by
  rw [← th0_compat' π ε]; group

@[expose] def rho (k : ℕ) : N4 →* Perm (Fin (k + 2)) :=
  (unitsHom (swap (0 : Fin (k + 2)) 1) (Equiv.swap_mul_self _ _)).comp prodHom

@[expose] def thStar (k : ℕ) : N4 →* Perm (Ω8 ⊕ Fin (k + 2)) :=
  (Perm.sumCongrHom Ω8 (Fin (k + 2))).comp (th0.prod (rho k))

@[expose] def sStar (k : ℕ) : Perm (Fin 4) →* Perm (Ω8 ⊕ Fin (k + 2)) :=
  (Perm.sumCongrHom Ω8 (Fin (k + 2))).comp
    ((MonoidHom.inl (Perm Ω8) (Perm (Fin (k + 2)))).comp sBlock)

theorem thStar_apply (k : ℕ) (ε : N4) : thStar k ε = Perm.sumCongr (th0 ε) (rho k ε) := rfl

theorem sStar_apply (k : ℕ) (π : Perm (Fin 4)) : sStar k π = Perm.sumCongr (sBlock π) 1 := rfl

theorem thStar_injective (k : ℕ) : Function.Injective (thStar k) := by
  intro ε ε' h
  have h1 : (th0.prod (rho k)) ε = (th0.prod (rho k)) ε' := Perm.sumCongrHom_injective h
  have h2 : th0 ε = th0 ε' := congrArg Prod.fst h1
  exact th0_injective h2

theorem star_compat (k : ℕ) (π : Perm (Fin 4)) :
    (thStar k).comp (MulEquiv.toMonoidHom (actHom π)) =
      (MulEquiv.toMonoidHom (MulAut.conj (sStar k π))).comp (thStar k) := by
  ext ε : 1
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have e1 : (actHom π) ε = act π ε := rfl
  rw [e1, thStar_apply, sStar_apply, thStar_apply, Perm.sumCongr_inv, Perm.sumCongr_mul,
    Perm.sumCongr_mul]
  congr 1
  · exact th0_compat π ε
  · simp [rho, prodHom_act]

theorem sign_unitsHom_swap {α : Type*} [DecidableEq α] [Fintype α] {a b : α} (h : a ≠ b)
    (u : ℤˣ) : sign (unitsHom (swap a b) (Equiv.swap_mul_self a b) u) = u := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp [unitsHom_one]
  · rw [unitsHom_neg_one, sign_swap h]

theorem sign_th0 (ε : N4) : sign (th0 ε) = prodHom ε := by
  show sign (Equiv.prodCongrRight (fun i => unitsHom (swap (0 : Fin 2) 1) swap01_sq (ε i))) = _
  rw [Perm.sign_prodCongrRight]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact sign_unitsHom_swap (by decide) _

theorem sign_rho (k : ℕ) (ε : N4) : sign (rho k ε) = prodHom ε := by
  show sign (unitsHom (swap (0 : Fin (k + 2)) 1) (Equiv.swap_mul_self _ _) (prodHom ε)) = _
  exact sign_unitsHom_swap (by simp) _

theorem sign_thStar (k : ℕ) (ε : N4) : sign (thStar k ε) = 1 := by
  rw [thStar_apply, Perm.sign_sumCongr, sign_th0, sign_rho]
  rcases Int.units_eq_one_or (prodHom ε) with h | h <;> rw [h] <;> decide

theorem sign_sBlock (π : Perm (Fin 4)) : sign (sBlock π) = 1 := by
  have : sBlock π = Equiv.prodCongrLeft (fun _ : Fin 2 => π) := rfl
  rw [this, Perm.sign_prodCongrLeft]
  simp

theorem sign_sStar (k : ℕ) (π : Perm (Fin 4)) : sign (sStar k π) = 1 := by
  rw [sStar_apply, Perm.sign_sumCongr, sign_sBlock]; simp

@[expose] def F8 : Perm Ω8 := th0 (fun _ => -1)

theorem F8_eq : F8 = Equiv.prodCongrRight (fun _ => swap (0 : Fin 2) 1) := by
  ext ⟨i, j⟩ <;> simp [F8, th0_apply, unitsHom_neg_one]

theorem thStar_comm_v (k : ℕ) (ε : N4) :
    thStar k ε * Perm.sumCongr F8 1 = Perm.sumCongr F8 1 * thStar k ε := by
  have h1 : th0 ε * F8 = F8 * th0 ε := by rw [F8, ← map_mul, ← map_mul, mul_comm]
  rw [thStar_apply, Perm.sumCongr_mul, Perm.sumCongr_mul, h1, mul_one, one_mul]

theorem sStar_comm_v (k : ℕ) (π : Perm (Fin 4)) :
    sStar k π * Perm.sumCongr F8 1 = Perm.sumCongr F8 1 * sStar k π := by
  have h := th0_compat' π (fun _ => -1)
  have e : act π (fun _ => (-1 : ℤˣ)) = fun _ => -1 := rfl
  rw [e] at h
  have h1 : sBlock π * F8 = F8 * sBlock π := h.symm
  rw [sStar_apply, Perm.sumCongr_mul, Perm.sumCongr_mul, h1, mul_one]

@[expose] def eΩ (k : ℕ) : Ω8 ⊕ Fin (k + 2) ≃ Fin (8 + (k + 2)) :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv

theorem eΩ_two : (Equiv.permCongr (eΩ 0)) (Perm.sumCongr F8 1) =
    yPerm (n := 8 + (0 + 2)) (by norm_num) := by
  rw [F8_eq]; decide

theorem eΩ_three : (Equiv.permCongr (eΩ 1)) (Perm.sumCongr F8 1) =
    yPerm (n := 8 + (1 + 2)) (by norm_num) := by
  rw [F8_eq]; decide

section Glue

variable {k m : ℕ} (e : Ω8 ⊕ Fin (k + 2) ≃ Fin m) (h8 : 8 ≤ m)

theorem exists_hom_centralizer
    (hy : (Equiv.permCongr e) (Perm.sumCongr F8 1) = yPerm h8) :
    ∃ (θ : N4 →* ↥(centralizer ({altY h8} : Set (alternatingGroup (Fin m)))))
      (s : Perm (Fin 4) →* ↥(centralizer ({altY h8} : Set (alternatingGroup (Fin m))))),
      Function.Injective θ ∧
      (∀ π, θ.comp (MulEquiv.toMonoidHom (actHom π)) =
        (MulEquiv.toMonoidHom (MulAut.conj (s π))).comp θ) ∧
      (∀ ε, ((θ ε : alternatingGroup (Fin m)) : Perm (Fin m)) = Equiv.permCongr e (thStar k ε)) ∧
      (∀ π, ((s π : alternatingGroup (Fin m)) : Perm (Fin m)) =
        Equiv.permCongr e (sStar k π)) := by
  classical
  let P : Perm (Ω8 ⊕ Fin (k + 2)) →* Perm (Fin m) := (Equiv.permCongrHom e).toMonoidHom
  have hP : ∀ g, P g = Equiv.permCongr e g := fun g => rfl
  have hPinj : Function.Injective P := (Equiv.permCongrHom e).injective
  have hsgn : ∀ g, sign (P g) = sign g := fun g => by rw [hP]; exact Perm.sign_permCongr e g
  have hcomm_def : ∀ g : Perm (Ω8 ⊕ Fin (k + 2)), g * Perm.sumCongr F8 1 = Perm.sumCongr F8 1 * g →
      P g * yPerm h8 = yPerm h8 * P g := by
    intro g hg
    rw [← hy, ← hP, ← map_mul, ← map_mul, hg]
  let θA : N4 →* alternatingGroup (Fin m) :=
    (P.comp (thStar k)).codRestrict (alternatingGroup (Fin m)) (fun ε => by
      rw [mem_alternatingGroup]
      simp [hsgn, sign_thStar])
  let sA : Perm (Fin 4) →* alternatingGroup (Fin m) :=
    (P.comp (sStar k)).codRestrict (alternatingGroup (Fin m)) (fun π => by
      rw [mem_alternatingGroup]
      simp [hsgn, sign_sStar])
  have hθA : ∀ ε, ((θA ε : alternatingGroup (Fin m)) : Perm (Fin m)) = P (thStar k ε) :=
    fun ε => rfl
  have hsA : ∀ π, ((sA π : alternatingGroup (Fin m)) : Perm (Fin m)) = P (sStar k π) :=
    fun π => rfl
  have hθc : ∀ ε, θA ε ∈ centralizer ({altY h8} : Set (alternatingGroup (Fin m))) := by
    intro ε
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hθA]
    exact hcomm_def _ (thStar_comm_v k ε)
  have hsc : ∀ π, sA π ∈ centralizer ({altY h8} : Set (alternatingGroup (Fin m))) := by
    intro π
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hsA]
    exact hcomm_def _ (sStar_comm_v k π)
  refine ⟨θA.codRestrict _ hθc, sA.codRestrict _ hsc, ?_, ?_, fun ε => rfl, fun π => rfl⟩
  · intro ε ε' h
    have h1 : ((θA.codRestrict _ hθc ε : alternatingGroup (Fin m)) : Perm (Fin m)) =
        ((θA.codRestrict _ hθc ε' : alternatingGroup (Fin m)) : Perm (Fin m)) := by rw [h]
    exact thStar_injective k (hPinj h1)
  · intro π
    ext ε : 1
    apply Subtype.ext
    apply Subtype.ext
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.codRestrict_apply, hθA, hsA]
    have := congrArg (fun f => P (f ε)) (star_compat k π)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv] at this
    exact this

end Glue

theorem numMoved_altY {m : ℕ} (h8 : 8 ≤ m) :
    numMoved ((altY h8 : alternatingGroup (Fin m)) : Perm (Fin m)) = 8 := by
  have hc : ((altY h8 : alternatingGroup (Fin m)) : Perm (Fin m)) = yPerm h8 := rfl
  rw [hc, numMoved_eq_card_support, ← sum_cycleType, yPerm_cycleType]
  simp

theorem exists_mulEquiv_six :
    ∃ v' : alternatingGroup (Fin (6 + 4)), orderOf v' = 2 ∧
      numMoved (v' : Perm (Fin (6 + 4))) = 8 ∧
      Nonempty (W ≃* ↥(centralizer ({v'} : Set (alternatingGroup (Fin (6 + 4)))))) := by
  have h8 : 8 ≤ 6 + 4 := by norm_num
  refine ⟨altY h8, orderOf_altY h8, numMoved_altY h8, ?_⟩
  obtain ⟨θ, s, hθ, hcomp, -, -⟩ := exists_hom_centralizer (k := 0) (eΩ 0) h8 eΩ_two
  have hcard : Nat.card ↥(centralizer ({altY h8} : Set (alternatingGroup (Fin (6 + 4))))) = 384 := by
    have h := card_centralizer_altY h8
    have : (6 + 4 - 8).factorial = 2 := by decide
    rw [this] at h
    omega
  exact exists_mulEquiv_W' θ hθ s hcomp hcard

end CFSG.GH74.GLS.C3.Layer2.L4.Star
