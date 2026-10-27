module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalU62PhiLift

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

section Aux

variable {K : Type} [Field K] (h : UnitaryFieldData 2 1 K)

theorem u62lb_phi_coprime_order {N : Subgroup (primeFormP h (idGram K 6))}
    (hc : Nat.Coprime 3 (Nat.card N)) {x : primeFormP h (idGram K 6)} (hx : x ∈ N) :
    Nat.Coprime 3 (orderOf x) :=
  Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard N hx) hc

theorem u62lb_phi_shape {N : Subgroup (primeFormP h (idGram K 6))}
    (hH : ∀ i j n : Fin 6, i ≠ j → i ≠ n → j ≠ n → ∃ m ∈ plane h i j n, m ≠ 1 ∧
      N ≤ Subgroup.centralizer ({m} : Set (primeFormP h (idGram K 6))))
    (hc : Nat.Coprime 3 (Nat.card N)) (s : gramSU h (idGram K 6))
    (hs : (s : primeFormP h (idGram K 6)) ∈ N) {u v : Fin 6} (huv : u ≠ v)
    (hsuv : ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) u v ≠ 0) (a b : Fin 6) (hab : a ≠ b)
    (hne : ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) a b ≠ 0) :
    (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
  by_contra hcon
  have hne' : ¬ ((u = a ∧ v = b) ∨ (u = b ∧ v = a)) := by
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hcon (Or.inl ⟨h1.symm, h2.symm⟩)
    · exact hcon (Or.inr ⟨h2.symm, h1.symm⟩)
  obtain ⟨i, j, n, hij, hin, hjn, H⟩ := u62lb_phi_cl (K := K) huv hab hne'
  obtain ⟨m, hm, hm1, hmN⟩ := hH i j n hij hin hjn
  obtain ⟨α, β, rfl⟩ := (mem_plane_iff h i j n m).1 hm
  have hx := hmN hs
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hcomm := u62lb_phi_lift_comm h s _ (prod_planeVec i j n α β)
    (u62lb_phi_coprime_order h hc hs) hx.symm
  have hmat : (dmat (planeVec i j n α β) : GL (Fin 6) K).1 *
      ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        (dmat (planeVec i j n α β) : GL (Fin 6) K).1 := by
    have := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) hcomm
    simpa only [Units.val_mul] using this
  have e1 := u62lb_phi_entry_comm _ _ hmat u v hsuv
  have e2 := u62lb_phi_entry_comm _ _ hmat a b hne
  obtain ⟨hα, hβ⟩ := H α β e1 e2
  apply hm1
  subst hα
  subst hβ
  have : planeHom h i j n (1, 1) = 1 := by
    rw [Prod.mk_one_one, map_one]
  exact this

theorem u62lb_phi_main {N : Subgroup (primeFormP h (idGram K 6))} (hN : TorusInv h N)
    (hH : ∀ i j n : Fin 6, i ≠ j → i ≠ n → j ≠ n → ∃ m ∈ plane h i j n, m ≠ 1 ∧
      N ≤ Subgroup.centralizer ({m} : Set (primeFormP h (idGram K 6))))
    (hc : Nat.Coprime 3 (Nat.card N)) (s : gramSU h (idGram K 6))
    (hs : (s : primeFormP h (idGram K 6)) ∈ N) (hs1 : (s : primeFormP h (idGram K 6)) ≠ 1) :
    False := by
  have hk := u62lb_phi_coprime_order h hc hs
  obtain ⟨u, v, huv, hsuv⟩ := u62lb_phi_exists_offdiag h s hk hs1
  have hshape := u62lb_phi_shape h hH hc s hs huv hsuv
  obtain ⟨huu, hvv, hvu⟩ := u62lb_phi_mm h _ (u62lb_phi_unitary_entries h s) huv hsuv hshape
  set M : Matrix (Fin 6) (Fin 6) K := ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) with hM
  have hmono : ∀ a b, M a b ≠ 0 → b = Equiv.swap u v a := by
    intro a b hab
    by_cases hba : a = b
    · subst hba
      have hau : a ≠ u := by
        rintro rfl
        exact hab huu
      have hav : a ≠ v := by
        rintro rfl
        exact hab hvv
      rw [Equiv.swap_apply_of_ne_of_ne hau hav]
    · rcases hshape a b hba hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [Equiv.swap_apply_left]
      · rw [Equiv.swap_apply_right]
  obtain ⟨ω, hω⟩ : ∃ ω : Kˣ, ω ≠ 1 := by
    haveI := h.finite
    have h3 : 1 < Nat.card Kˣ := by
      rw [u62lb_card_units h]
      norm_num
    haveI : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.1 h3
    exact exists_ne 1
  set μ : Fin 6 → Kˣ := Pi.mulSingle u ω * Pi.mulSingle v ω⁻¹ with hμdef
  have hμu : μ u = ω := by
    simp [hμdef, Pi.mulSingle_eq_of_ne huv]
  have hμv : μ v = ω⁻¹ := by
    simp [hμdef, Pi.mulSingle_eq_of_ne huv.symm]
  have hμ : ∏ i, μ i = 1 := by
    simp only [hμdef, Pi.mul_apply]
    rw [Finset.prod_mul_distrib]
    simp
  set D : gramSU h (idGram K 6) := dmatS h μ hμ with hD
  set s' : gramSU h (idGram K 6) := D * s * D⁻¹ * s with hs'
  have hs'P : (s' : primeFormP h (idGram K 6)) = diagP h μ hμ * (s : primeFormP h (idGram K 6)) *
      (diagP h μ hμ)⁻¹ * (s : primeFormP h (idGram K 6)) := by
    rw [hs', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv]
    rfl
  have hs'N : (s' : primeFormP h (idGram K 6)) ∈ N := by
    rw [hs'P]
    exact N.mul_mem (hN μ hμ _ hs) hs
  have hM' : ((s' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      diagonal (fun a => (μ a : K)) * M * diagonal (fun a => (((μ a)⁻¹ : Kˣ) : K)) * M := by
    have e1 : ((s' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        ((dmat μ * (s : GL (Fin 6) K) * (dmat μ)⁻¹ * (s : GL (Fin 6) K) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) := rfl
    rw [e1, Units.val_mul, Units.val_mul, Units.val_mul, ← map_inv, coe_dmat, coe_dmat]
    rfl
  have hoff : ∀ a b, a ≠ b →
      ((s' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) a b = 0 := by
    intro a b hab
    rw [hM', u62lb_phi_prod_entry (Equiv.swap u v) (Equiv.swap_apply_self u v) M hmono _ _ a b,
      if_neg (Ne.symm hab)]
  have hdiag := u62lb_phi_diag_entries h s' (u62lb_phi_coprime_order h hc hs'N) hoff u v
  rw [hM', u62lb_phi_prod_entry (Equiv.swap u v) (Equiv.swap_apply_self u v) M hmono _ _ u u,
    u62lb_phi_prod_entry (Equiv.swap u v) (Equiv.swap_apply_self u v) M hmono _ _ v v, if_pos rfl,
    if_pos rfl, Equiv.swap_apply_left, Equiv.swap_apply_right] at hdiag
  simp only [hμu, hμv, inv_inv] at hdiag
  have hAB : M u v * M v u ≠ 0 := mul_ne_zero hsuv hvu
  have e : (ω : K) * ω = ((ω⁻¹ : Kˣ) : K) * ((ω⁻¹ : Kˣ) : K) := by
    apply mul_right_cancel₀ hAB
    linear_combination hdiag
  have h1 : (ω : K) * ((ω⁻¹ : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h4 : ω ^ 4 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    linear_combination ((ω : K) * ω) * e + ((ω : K) * ((ω⁻¹ : Kˣ) : K) + 1) * h1
  exact hω (u62lb_phi_unit_pow_four h h4)

end Aux

theorem u62lb_phi {K : Type} [Field K] (h : UnitaryFieldData 2 1 K)
    (N : Subgroup (primeFormP h (idGram K 6))) (hN : TorusInv h N) (hN1 : N ≠ ⊥)
    (hc : Nat.Coprime 3 (Nat.card N)) : NoCommutingPlane h N := by
  by_contra hnot
  have hH : ∀ i j n : Fin 6, i ≠ j → i ≠ n → j ≠ n → ∃ m ∈ plane h i j n, m ≠ 1 ∧
      N ≤ Subgroup.centralizer ({m} : Set (primeFormP h (idGram K 6))) := by
    intro i j n hij hin hjn
    by_contra hcon
    exact hnot ⟨i, j, n, hij, hin, hjn, fun m hm hm1 hle => hcon ⟨m, hm, hm1, hle⟩⟩
  obtain ⟨x0, hx0⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hN1
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (x0 : primeFormP h (idGram K 6))
  refine u62lb_phi_main h hN hH hc s ?_ ?_
  · rw [hs]
    exact x0.2
  · rw [hs]
    intro h1
    exact hx0 (Subtype.ext h1)

end CFSG.HardMathSupport.Dickson.Bal207

end
