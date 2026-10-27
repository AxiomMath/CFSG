module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

open Matrix CFSG.Open

variable {k : Type} [Field k]

theorem sl2W_conj_sl2Diag (t : kˣ) :
    (sl2W : SpecialLinearGroup (Fin 2) k) * sl2Diag t * sl2W⁻¹ = sl2Diag t⁻¹ := by
  rw [sl2W_mul_sl2Diag, mul_assoc, mul_inv_cancel, mul_one]

theorem sl2W_conj_eq_inv_of_transpose {g : SpecialLinearGroup (Fin 2) k}
    (hg : (g : Matrix (Fin 2) (Fin 2) k)ᵀ = (g : Matrix (Fin 2) (Fin 2) k)) :
    (sl2W : SpecialLinearGroup (Fin 2) k) * g * sl2W⁻¹ = g⁻¹ := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    coe_sl2W, coe_sl2W_inv]
  rw [Matrix.adjugate_fin_two_of, Matrix.adjugate_fin_two]
  have h10 : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = (g : Matrix (Fin 2) (Fin 2) k) 0 1 := by
    have := congrFun (congrFun hg 0) 1
    simpa using this
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, Matrix.vecMul_apply_eq_sum]

variable {r : ℕ}

theorem lam_sl2W_conj_lam_sl2Diag (i : Fin r) (t : kˣ) :
    lam i (sl2W : SpecialLinearGroup (Fin 2) k) * lam i (sl2Diag t) *
        (lam i (sl2W : SpecialLinearGroup (Fin 2) k))⁻¹ = (lam i (sl2Diag t))⁻¹ := by
  have h := congrArg (lam i) (sl2W_conj_sl2Diag (k := k) t)
  simpa using h

theorem lam_sl2W_conj_eq_inv_of_transpose (i : Fin r) {g : SpecialLinearGroup (Fin 2) k}
    (hg : (g : Matrix (Fin 2) (Fin 2) k)ᵀ = (g : Matrix (Fin 2) (Fin 2) k)) :
    lam i (sl2W : SpecialLinearGroup (Fin 2) k) * lam i g *
        (lam i (sl2W : SpecialLinearGroup (Fin 2) k))⁻¹ = (lam i g)⁻¹ := by
  have h := congrArg (lam i) (sl2W_conj_eq_inv_of_transpose (k := k) hg)
  simpa using h

theorem lam_injective (i : Fin r) :
    Function.Injective (lam (k := k) i) := by
  intro g h hgh
  have hmat : (pairMat (Sum.inl i) (Sum.inr i) (g : Matrix (Fin 2) (Fin 2) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      pairMat (Sum.inl i) (Sum.inr i) (h : Matrix (Fin 2) (Fin 2) k) := by
    simpa only [coe_lam] using congrArg
      (fun x : StatedSp r k => ((x : GL (Fin r ⊕ Fin r) k) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)) hgh
  obtain ⟨g00, g01, g10, g11⟩ := pairMat_apply_pair (a := Sum.inl i) (b := Sum.inr i)
    Sum.inl_ne_inr (g := (g : Matrix (Fin 2) (Fin 2) k))
  obtain ⟨h00, h01, h10, h11⟩ := pairMat_apply_pair (a := Sum.inl i) (b := Sum.inr i)
    Sum.inl_ne_inr (g := (h : Matrix (Fin 2) (Fin 2) k))
  refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
  have e00 : g 0 0 = h 0 0 := by
    have := congrFun (congrFun hmat (Sum.inl i)) (Sum.inl i)
    rw [g00, h00] at this
    exact this
  have e01 : g 0 1 = h 0 1 := by
    have := congrFun (congrFun hmat (Sum.inl i)) (Sum.inr i)
    rw [g01, h01] at this
    exact this
  have e10 : g 1 0 = h 1 0 := by
    have := congrFun (congrFun hmat (Sum.inr i)) (Sum.inl i)
    rw [g10, h10] at this
    exact this
  have e11 : g 1 1 = h 1 1 := by
    have := congrFun (congrFun hmat (Sum.inr i)) (Sum.inr i)
    rw [g11, h11] at this
    exact this
  fin_cases a <;> fin_cases b <;> assumption

theorem pi_zpowers_eq_closure (m : ℕ) (ζ : kˣ) :
    Subgroup.pi Set.univ (fun _ : Fin m => Subgroup.zpowers ζ) =
      Subgroup.closure (Set.range fun i : Fin m => Pi.mulSingle i ζ) := by
  refine le_antisymm ?_ ?_
  · intro t ht
    rw [← Finset.univ_prod_mulSingle t]
    refine Subgroup.prod_mem _ fun i _ => ?_
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (ht i (Set.mem_univ i))
    rw [← hn]
    have hsingle : (Pi.mulSingle i (ζ ^ n) : Fin m → kˣ) = (Pi.mulSingle i ζ) ^ n := by
      funext j
      by_cases hj : j = i <;> simp [Pi.mulSingle_apply, hj]
    rw [hsingle]
    exact Subgroup.zpow_mem
      (K := Subgroup.closure (Set.range fun i : Fin m => Pi.mulSingle i ζ))
      (x := Pi.mulSingle i ζ) (Subgroup.subset_closure (Set.mem_range_self i)) n
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact (Subgroup.mulSingle_mem_pi (I := Set.univ)
      (H := fun _ : Fin m => Subgroup.zpowers ζ) i ζ).mpr fun _ => Subgroup.mem_zpowers ζ

theorem pi_ite_zpowers_eq_closure (m : ℕ) (ζ : kˣ) (s : Finset (Fin m)) :
    Subgroup.pi Set.univ (fun i : Fin m =>
        (if i ∈ s then Subgroup.zpowers ζ else ⊥ : Subgroup kˣ)) =
      Subgroup.closure (Set.range fun i : {i : Fin m // i ∈ s} =>
        (Pi.mulSingle (M := fun _ : Fin m => kˣ) (i : Fin m) ζ)) := by
  refine le_antisymm ?_ ?_
  · intro t ht
    have hti : ∀ i : Fin m, i ∉ s → t i = 1 := by
      intro i hi
      have h : t i ∈ (if i ∈ s then Subgroup.zpowers ζ else ⊥ : Subgroup kˣ) :=
        (Subgroup.mem_pi Set.univ).mp ht i (Set.mem_univ i)
      rw [if_neg hi] at h
      exact Subgroup.mem_bot.mp h
    have hprod : t = ∏ i ∈ s, (Pi.mulSingle (M := fun _ : Fin m => kˣ) i (t i)) := by
      refine (Finset.univ_prod_mulSingle (M := fun _ : Fin m => kˣ) t).symm.trans ?_
      exact (Finset.prod_subset (Finset.subset_univ s) (fun i _ hi => by
        rw [hti i hi]; exact Pi.mulSingle_one i)).symm
    rw [hprod]
    refine Subgroup.prod_mem _ fun i hi => ?_
    have ht_i : t i ∈ Subgroup.zpowers ζ := by
      have h : t i ∈ (if i ∈ s then Subgroup.zpowers ζ else ⊥ : Subgroup kˣ) :=
        (Subgroup.mem_pi Set.univ).mp ht i (Set.mem_univ i)
      rwa [if_pos hi] at h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp ht_i
    rw [← hn]
    have hpow : (Pi.mulSingle (M := fun _ : Fin m => kˣ) i (ζ ^ n)) =
        (Pi.mulSingle (M := fun _ : Fin m => kˣ) i ζ) ^ n := by
      funext j
      by_cases hj : j = i <;> simp [Pi.mulSingle_apply, hj]
    rw [hpow]
    exact Subgroup.zpow_mem
      (K := Subgroup.closure (Set.range fun i : {i : Fin m // i ∈ s} =>
        (Pi.mulSingle (M := fun _ : Fin m => kˣ) (i : Fin m) ζ)))
      (x := (Pi.mulSingle (M := fun _ : Fin m => kˣ) i ζ))
      (Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩) n
  · rw [Subgroup.closure_le]
    rintro _ ⟨⟨i, hi⟩, rfl⟩
    change (Pi.mulSingle (M := fun _ : Fin m => kˣ) i ζ) ∈
      Subgroup.pi Set.univ (fun j : Fin m =>
        (if j ∈ s then Subgroup.zpowers ζ else ⊥ : Subgroup kˣ))
    rw [Subgroup.mem_pi]
    intro j _
    by_cases hji : j = i
    · subst hji
      rw [if_pos hi, Pi.mulSingle_eq_same]
      exact Subgroup.mem_zpowers ζ
    · by_cases hjs : j ∈ s
      · rw [if_pos hjs, Pi.mulSingle_eq_of_ne hji]
        exact Subgroup.one_mem _
      · rw [if_neg hjs, Pi.mulSingle_eq_of_ne hji]
        exact Subgroup.mem_bot.mpr rfl

theorem card_pi_ite_zpowers (m : ℕ) (ζ : kˣ) (s : Finset (Fin m)) :
    Nat.card (Subgroup.pi Set.univ (fun i : Fin m =>
        (if i ∈ s then Subgroup.zpowers ζ else ⊥ : Subgroup kˣ))) =
      orderOf ζ ^ s.card := by
  have hcard : Nat.card (Subgroup.pi Set.univ (fun i : Fin m =>
      (if i ∈ s then Subgroup.zpowers ζ else ⊥ : Subgroup kˣ))) =
      ∏ i : Fin m, Nat.card (if i ∈ s then Subgroup.zpowers ζ else ⊥ : Subgroup kˣ) := by
    rw [← Nat.card_pi]
    refine Nat.card_congr ((Equiv.subtypeEquivRight fun x => ?_).trans
      (Equiv.subtypePiEquivPi (p := fun i z =>
        z ∈ (if i ∈ s then Subgroup.zpowers ζ else ⊥ : Subgroup kˣ))))
    simp [Subgroup.mem_pi]
  rw [hcard]
  have hterm : ∀ i : Fin m, Nat.card (if i ∈ s then Subgroup.zpowers ζ else ⊥ : Subgroup kˣ) =
      if i ∈ s then orderOf ζ else 1 := by
    intro i
    by_cases hi : i ∈ s <;> simp [hi, Nat.card_zpowers]
  simp only [hterm]
  rw [Finset.prod_ite_mem]
  simp

theorem pow_eq_one_of_mem_map_pi_ite_zpowers {m : ℕ} {ζ : kˣ} {r : ℕ} (hζ : orderOf ζ = r)
    {s : Finset (Fin m)} {y : StatedSp m k}
    (hy : y ∈ (Subgroup.pi Set.univ (fun i : Fin m =>
      (if i ∈ s then Subgroup.zpowers ζ else ⊥ : Subgroup kˣ))).map (torusHom (r := m))) :
    y ^ r = 1 := by
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
  have htpow : t ^ r = 1 := by
    funext i
    rw [Pi.pow_apply, Pi.one_apply]
    by_cases hi : i ∈ s
    · have hmem : t i ∈ Subgroup.zpowers ζ := by
        have h : t i ∈ (if i ∈ s then Subgroup.zpowers ζ else ⊥ : Subgroup kˣ) :=
          (Subgroup.mem_pi Set.univ).mp ht i (Set.mem_univ i)
        rwa [if_pos hi] at h
      exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hmem).trans
        (by rw [hζ]))
    · have h : t i ∈ (if i ∈ s then Subgroup.zpowers ζ else ⊥ : Subgroup kˣ) :=
        (Subgroup.mem_pi Set.univ).mp ht i (Set.mem_univ i)
      rw [if_neg hi] at h
      rw [Subgroup.mem_bot.mp h, one_pow]
  rw [← map_pow, htpow, map_one]

theorem orderOf_lam (i : Fin r) (g : SpecialLinearGroup (Fin 2) k) :
    orderOf (lam i g) = orderOf g := by
  let f : SpecialLinearGroup (Fin 2) k →* StatedSp r k := lam i
  have hf : Function.Injective f := lam_injective i
  exact orderOf_injective f hf g

theorem map_pi_zpowers_torusHom (m : ℕ) (ζ : kˣ) :
    (Subgroup.pi Set.univ (fun _ : Fin m => Subgroup.zpowers ζ)).map
        (torusHom (r := m) (k := k)) =
      Subgroup.closure (Set.range fun i : Fin m =>
        torusHom (r := m) (k := k) (Pi.mulSingle i ζ)) := by
  rw [pi_zpowers_eq_closure, MonoidHom.map_closure]
  congr 1
  exact (Set.range_comp _ _).symm

theorem card_closure_single_torusHom (m : ℕ) (ζ : kˣ) :
    Nat.card (Subgroup.closure (Set.range fun i : Fin m =>
      torusHom (r := m) (k := k) (Pi.mulSingle i ζ))) = orderOf ζ ^ m := by
  rw [← map_pi_zpowers_torusHom, Subgroup.card_map_of_injective torusHom_injective]
  have hpi : Nat.card (Subgroup.pi Set.univ (fun _ : Fin m => Subgroup.zpowers ζ)) =
      ∏ _ : Fin m, Nat.card (Subgroup.zpowers ζ) := by
    rw [← Nat.card_pi]
    refine Nat.card_congr
      ((Equiv.subtypeEquivRight fun x => ?_).trans (Equiv.subtypePiEquivPi
        (p := fun _ z => z ∈ Subgroup.zpowers ζ)))
    simp [Subgroup.mem_pi]
  rw [hpi]
  simp [Nat.card_zpowers]

theorem orderOf_lam_sl2Diag (i : Fin r) (ζ : kˣ) :
    orderOf (lam i (sl2Diag ζ)) = orderOf ζ := by
  rw [lam_sl2Diag]
  rw [orderOf_injective (torusHom (r := r) (k := k))
    (torusHom_injective (r := r) (k := k))]
  exact orderOf_piMulSingle (M := fun _ : Fin r => kˣ) i ζ

end CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
