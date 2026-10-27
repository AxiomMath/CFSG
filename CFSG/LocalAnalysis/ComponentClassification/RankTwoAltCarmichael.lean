module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltIdent

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.PresentationLocal
  CFSG.Quasithin.SteinbergCB

theorem swap_mul_swap_eq_swap_mul_swap {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : swap a c * swap a b = swap a b * swap b c := by
  refine Equiv.ext fun x => ?_
  simp only [Perm.mul_apply]
  by_cases hxa : x = a
  · rw [hxa, swap_apply_left, swap_apply_of_ne_of_ne hab.symm hbc,
      swap_apply_of_ne_of_ne hab hac, swap_apply_left]
  · by_cases hxb : x = b
    · rw [hxb, swap_apply_right, swap_apply_left, swap_apply_left,
        swap_apply_of_ne_of_ne hac.symm hbc.symm]
    · by_cases hxc : x = c
      · rw [hxc, swap_apply_of_ne_of_ne hac.symm hbc.symm, swap_apply_right, swap_apply_right,
          swap_apply_right]
      · rw [swap_apply_of_ne_of_ne hxa hxb, swap_apply_of_ne_of_ne hxa hxc,
          swap_apply_of_ne_of_ne hxb hxc, swap_apply_of_ne_of_ne hxa hxb]

variable {n : ℕ} (hn : 6 ≤ n)

@[expose] def l4 : Fin n := ⟨4, by omega⟩

@[expose] def l5 : Fin n := ⟨5, by omega⟩

@[expose] def c45 (o : Fin n) : Perm (Fin n) := swap (l4 hn) (l5 hn) * swap (l5 hn) o

theorem c45_mem {o : Fin n} (ho5 : (o : ℕ) ≠ 5) :
    c45 hn o ∈ alternatingGroup (Fin n) := by
  have h45 : l4 hn ≠ l5 hn := by simp [l4, l5, Fin.ext_iff]
  have h5o : l5 hn ≠ o := fun h => ho5 (by rw [← h]; rfl)
  rw [mem_alternatingGroup, c45, Perm.sign_mul, sign_swap h45, sign_swap h5o]
  rfl

@[expose] def tau45 : Perm (Fin n) := swap ⟨0, by omega⟩ (l4 hn) * swap ⟨1, by omega⟩ (l5 hn)

theorem tau45_val (i : Fin n) : ((tau45 hn i : Fin n) : ℕ) =
    if (i : ℕ) = 0 then 4 else if (i : ℕ) = 1 then 5 else if (i : ℕ) = 4 then 0
      else if (i : ℕ) = 5 then 1 else (i : ℕ) := by
  simp only [tau45, Perm.mul_apply, swap_apply_def, l4, l5, Fin.ext_iff]
  split_ifs <;> simp_all

theorem tau45_mul_self : tau45 hn * tau45 hn = 1 := by
  refine Equiv.ext fun i => Fin.ext ?_
  rw [Perm.mul_apply, tau45_val, tau45_val, Perm.one_apply]
  split_ifs <;> simp_all

theorem tau45_inv : (tau45 hn)⁻¹ = tau45 hn := inv_eq_of_mul_eq_one_right (tau45_mul_self hn)

theorem tau45_mem : tau45 hn ∈ alternatingGroup (Fin n) := by
  have h04 : (⟨0, by omega⟩ : Fin n) ≠ l4 hn := by simp [l4, Fin.ext_iff]
  have h15 : (⟨1, by omega⟩ : Fin n) ≠ l5 hn := by simp [l5, Fin.ext_iff]
  rw [mem_alternatingGroup, tau45, Perm.sign_mul, sign_swap h04, sign_swap h15]
  rfl

@[expose] noncomputable def gam (k : CarmichaelIndex n) : alternatingGroup (Fin n) :=
  conjPerm n (tau45 hn) (carmichaelCycle k)

theorem gam_pow_three (k : CarmichaelIndex n) : gam hn k ^ 3 = 1 := by
  rw [gam, ← map_pow, carmichaelCycle_pow_three, map_one]

theorem gam_mul_sq {k l : CarmichaelIndex n} (hkl : k ≠ l) : (gam hn k * gam hn l) ^ 2 = 1 := by
  rw [gam, gam, ← map_mul, ← map_pow, carmichaelCycle_mul_sq k l hkl, map_one]

theorem closure_range_gam : Subgroup.closure (Set.range (gam hn)) = ⊤ := by
  have h := closure_range_carmichaelCycle (n := n) (by omega)
  have hmap := MonoidHom.map_closure (conjPerm n (tau45 hn)).toMonoidHom
    (Set.range (carmichaelCycle (n := n)))
  rw [h, ← Set.range_comp] at hmap
  have htop : (⊤ : Subgroup (alternatingGroup (Fin n))).map (conjPerm n (tau45 hn)).toMonoidHom =
      ⊤ := Subgroup.map_top_of_surjective _ (conjPerm n (tau45 hn)).surjective
  rw [htop] at hmap
  rw [hmap]
  rfl

theorem gam_ne_one (k : CarmichaelIndex n) : gam hn k ≠ 1 := by
  intro h
  rw [gam, MulEquiv.map_eq_one_iff] at h
  exact (carmichaelPerm_isThreeCycle k).ne_one (congrArg Subtype.val h)

theorem coe_gam (k : CarmichaelIndex n) :
    ((gam hn k : alternatingGroup (Fin n)) : Perm (Fin n)) = c45 hn (tau45 hn k) := by
  have hk := k.2
  rw [gam, conjPerm_apply, show ((carmichaelCycle k : alternatingGroup (Fin n)) : Perm (Fin n)) =
    swap ⟨0, by omega⟩ k.1 * swap ⟨0, by omega⟩ ⟨1, by omega⟩ from rfl]
  have h0 : tau45 hn ⟨0, by omega⟩ = l4 hn := Fin.ext (by rw [tau45_val]; simp [l4])
  have h1 : tau45 hn ⟨1, by omega⟩ = l5 hn := Fin.ext (by rw [tau45_val]; simp [l5])
  have hτk4 : tau45 hn k.1 ≠ l4 hn := fun h => by
    have := congrArg (fun x : Fin n => (x : ℕ)) h
    simp only [tau45_val, l4] at this
    split_ifs at this <;> omega
  have hτk5 : tau45 hn k.1 ≠ l5 hn := fun h => by
    have := congrArg (fun x : Fin n => (x : ℕ)) h
    simp only [tau45_val, l5] at this
    split_ifs at this <;> omega
  rw [show tau45 hn * (swap ⟨0, by omega⟩ k.1 * swap ⟨0, by omega⟩ ⟨1, by omega⟩) *
      (tau45 hn)⁻¹ = (tau45 hn * swap ⟨0, by omega⟩ k.1 * (tau45 hn)⁻¹) *
        (tau45 hn * swap ⟨0, by omega⟩ ⟨1, by omega⟩ * (tau45 hn)⁻¹) by group,
    ← swap_apply_apply, ← swap_apply_apply, h0, h1, c45]
  exact swap_mul_swap_eq_swap_mul_swap (by simp [l4, l5, Fin.ext_iff]) hτk4.symm hτk5.symm

@[expose] def embB : Fin n ↪ Fin (n + 4) where
  toFun m := ⟨if 2 ≤ (m : ℕ) ∧ (m : ℕ) < 6 then n + m - 2 else m, by
    have := m.isLt
    split_ifs <;> omega⟩
  inj' a b h := by
    have ha := a.isLt
    have hb := b.isLt
    have h' := congrArg Fin.val h
    dsimp only at h'
    apply Fin.ext
    split_ifs at h' <;> omega

theorem embB_val (m : Fin n) : ((embB hn m : Fin (n + 4)) : ℕ) =
    if 2 ≤ (m : ℕ) ∧ (m : ℕ) < 6 then n + m - 2 else m :=
  rfl

@[expose] noncomputable def liftA : alternatingGroup (Fin n) →* alternatingGroup (Fin (n + 4)) :=
  (((viaEmbeddingHom (Fin.castLEEmb (by omega : n ≤ n + 4))).comp
    (MulAut.conj (tau45 hn)).toMonoidHom).comp (alternatingGroup (Fin n)).subtype).codRestrict
      (alternatingGroup (Fin (n + 4))) fun z => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          Subgroup.coe_subtype]
        rw [mem_alternatingGroup, sign_viaEmbeddingHom, Perm.sign_mul, Perm.sign_mul,
          mem_alternatingGroup.mp z.2, Perm.sign_inv]
        simp

@[expose] noncomputable def liftB : alternatingGroup (Fin n) →* alternatingGroup (Fin (n + 4)) :=
  (((viaEmbeddingHom (embB hn)).comp (MulAut.conj (tau45 hn)).toMonoidHom).comp
    (alternatingGroup (Fin n)).subtype).codRestrict (alternatingGroup (Fin (n + 4))) fun z => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        Subgroup.coe_subtype]
      rw [mem_alternatingGroup, sign_viaEmbeddingHom, Perm.sign_mul, Perm.sign_mul,
        mem_alternatingGroup.mp z.2, Perm.sign_inv]
      simp

theorem viaEmbeddingHom_carmichaelPerm {N : ℕ} (ι : Fin n ↪ Fin N) (h0 : ((ι ⟨0, by omega⟩ :
    Fin N) : ℕ) = 0) (h1 : ((ι ⟨1, by omega⟩ : Fin N) : ℕ) = 1) (k : CarmichaelIndex n)
    (hk : 2 ≤ ((ι k : Fin N) : ℕ)) :
    viaEmbeddingHom ι (carmichaelPerm k) = carmichaelPerm (⟨ι k, hk⟩ : CarmichaelIndex N) := by
  have hk' := k.2
  have hN : 2 < N := by have := (ι k).isLt; omega
  have e : carmichaelPerm k = swap ⟨0, by omega⟩ k.1 * swap ⟨0, by omega⟩ ⟨1, by omega⟩ := rfl
  rw [e, map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
  have e0 : ι ⟨0, by omega⟩ = ⟨0, by omega⟩ := Fin.ext h0
  have e1 : ι ⟨1, by omega⟩ = ⟨1, by omega⟩ := Fin.ext h1
  rw [e0, e1]
  rfl

theorem liftA_gam (k : CarmichaelIndex n) :
    liftA hn (gam hn k) = carmichaelCycle (⟨⟨k, by omega⟩, k.2⟩ : CarmichaelIndex (n + 4)) := by
  apply Subtype.ext
  change viaEmbeddingHom _ (tau45 hn * ((gam hn k : alternatingGroup (Fin n)) : Perm (Fin n)) *
    (tau45 hn)⁻¹) = carmichaelPerm _
  rw [gam, conjPerm_apply, tau45_inv,
    show tau45 hn * (tau45 hn * ((carmichaelCycle k : alternatingGroup (Fin n)) : Perm (Fin n)) *
      tau45 hn) * tau45 hn = carmichaelPerm k by
        rw [← mul_assoc, ← mul_assoc, tau45_mul_self, one_mul, mul_assoc, tau45_mul_self,
          mul_one]
        rfl]
  exact viaEmbeddingHom_carmichaelPerm (by omega) _ rfl rfl k k.2

theorem liftB_gam (k : CarmichaelIndex n) :
    liftB hn (gam hn k) = carmichaelCycle (⟨embB hn k, by
      rw [embB_val]; have := k.2; split_ifs <;> omega⟩ : CarmichaelIndex (n + 4)) := by
  apply Subtype.ext
  change viaEmbeddingHom _ (tau45 hn * ((gam hn k : alternatingGroup (Fin n)) : Perm (Fin n)) *
    (tau45 hn)⁻¹) = carmichaelPerm _
  rw [gam, conjPerm_apply, tau45_inv,
    show tau45 hn * (tau45 hn * ((carmichaelCycle k : alternatingGroup (Fin n)) : Perm (Fin n)) *
      tau45 hn) * tau45 hn = carmichaelPerm k by
        rw [← mul_assoc, ← mul_assoc, tau45_mul_self, one_mul, mul_assoc, tau45_mul_self,
          mul_one]
        rfl]
  exact viaEmbeddingHom_carmichaelPerm (by omega) _ (by rw [embB_val]; simp)
    (by rw [embB_val]; simp) k _

variable {G : Type*} [Group G] {A B : Subgroup G} (ψA : A ≃* alternatingGroup (Fin n))
  (ψB : B ≃* alternatingGroup (Fin n))

@[expose] noncomputable def glueFam (k : CarmichaelIndex (n + 4)) : G :=
  if h : (k : ℕ) < n then (ψA.symm (gam hn ⟨⟨k, h⟩, k.2⟩) : G)
  else (ψB.symm (gam hn ⟨⟨k - n + 2, by have := k.1.isLt; omega⟩, by simp⟩) : G)

theorem glueFam_of_lt (k : CarmichaelIndex (n + 4)) (h : (k : ℕ) < n) :
    glueFam hn ψA ψB k = ψA.symm (gam hn ⟨⟨k, h⟩, k.2⟩) := by
  rw [glueFam, dite_eq_left h]

theorem glueFam_of_ge (k : CarmichaelIndex (n + 4)) (h : n ≤ (k : ℕ)) :
    glueFam hn ψA ψB k =
      ψB.symm (gam hn ⟨⟨k - n + 2, by have := k.1.isLt; omega⟩, by simp⟩) := by
  rw [glueFam, dite_eq_right (by omega)]

theorem sq_mul_comm_of {a b : G} (h : (a * b) ^ 2 = 1) : (b * a) ^ 2 = 1 := by
  rw [sq] at h ⊢
  calc b * a * (b * a) = a⁻¹ * (a * b * (a * b)) * a := by group
    _ = 1 := by rw [h]; group

theorem conj_c45 {v : Perm (Fin n)} (h4 : v (l4 hn) = l4 hn) (h5 : v (l5 hn) = l5 hn)
    (o : Fin n) : v * c45 hn o * v⁻¹ = c45 hn (v o) := by
  rw [c45, show v * (swap (l4 hn) (l5 hn) * swap (l5 hn) o) * v⁻¹ =
    (v * swap (l4 hn) (l5 hn) * v⁻¹) * (v * swap (l5 hn) o * v⁻¹) by group,
    ← swap_apply_apply, ← swap_apply_apply, h4, h5, c45]

variable (hT : ∀ a : A, ψA a ∈ rootV n → (a : G) ∈ Subgroup.centralizer (B : Set G))
  (hR : ∀ b : B, ψB b ∈ rootV n → (b : G) ∈ Subgroup.centralizer (A : Set G))
  (hstar : ∀ (a : A) (b : B), (ψA a : Perm (Fin n)) = c45 hn ⟨0, by omega⟩ →
    (ψB b : Perm (Fin n)) = c45 hn ⟨0, by omega⟩ → ((a : G) * b) ^ 2 = 1)

theorem exists_rootV_apply_zero {m : Fin n} (hm : (m : ℕ) < 4) :
    ∃ v ∈ rootV n, ((v : alternatingGroup (Fin n)) : Perm (Fin n)) ⟨0, by omega⟩ = m := by
  have h4 : 4 ≤ n := by omega
  refine ⟨⟨_, viaEmbeddingHom_mem_alternatingGroup' (fourEmb h4)
    (kleinFour_le_alternatingGroup (kOf_mem ⟨m, hm⟩))⟩, (mem_rootV_iff h4 _).mpr
      ⟨kOf ⟨m, hm⟩, kOf_mem _, rfl⟩, ?_⟩
  change viaEmbeddingHom (fourEmb h4) (kOf ⟨m, hm⟩) (fourEmb h4 0) = m
  rw [viaEmbeddingHom_apply_image, kOf_apply_zero]
  rfl

theorem rootV_apply_four_five {v : alternatingGroup (Fin n)} (hv : v ∈ rootV n) :
    (v : Perm (Fin n)) (l4 hn) = l4 hn ∧ (v : Perm (Fin n)) (l5 hn) = l5 hn := by
  have h4 : 4 ≤ n := by omega
  have hvP : (v : Perm (Fin n)) ∈ rootVP n := Subgroup.mem_map_of_mem _ hv
  exact ⟨apply_eq_of_mem_rootVP h4 hvP (by simp [l4]),
    apply_eq_of_mem_rootVP h4 hvP (by simp [l5])⟩

include hT hR hstar in
theorem cross_rel {m m' : Fin n} (hm : (m : ℕ) < 4) (hm' : (m' : ℕ) < 4) (a : A) (b : B)
    (ha : (ψA a : Perm (Fin n)) = c45 hn m) (hb : (ψB b : Perm (Fin n)) = c45 hn m') :
    ((a : G) * b) ^ 2 = 1 := by
  obtain ⟨v, hv, hv0⟩ := exists_rootV_apply_zero hn hm
  obtain ⟨v', hv', hv'0⟩ := exists_rootV_apply_zero hn hm'
  obtain ⟨hv4, hv5⟩ := rootV_apply_four_five hn hv
  obtain ⟨hv'4, hv'5⟩ := rootV_apply_four_five hn hv'
  set t := ψA.symm v with htdef
  set t' := ψB.symm v' with ht'def
  have htB : (t : G) ∈ Subgroup.centralizer (B : Set G) :=
    hT t (by rw [htdef, MulEquiv.apply_symm_apply]; exact hv)
  have ht'A : (t' : G) ∈ Subgroup.centralizer (A : Set G) :=
    hR t' (by rw [ht'def, MulEquiv.apply_symm_apply]; exact hv')
  have hinv4 : (v : Perm (Fin n))⁻¹ (l4 hn) = l4 hn := by rw [Perm.inv_eq_iff_eq, hv4]
  have hinv5 : (v : Perm (Fin n))⁻¹ (l5 hn) = l5 hn := by rw [Perm.inv_eq_iff_eq, hv5]
  have hinv4' : (v' : Perm (Fin n))⁻¹ (l4 hn) = l4 hn := by rw [Perm.inv_eq_iff_eq, hv'4]
  have hinv5' : (v' : Perm (Fin n))⁻¹ (l5 hn) = l5 hn := by rw [Perm.inv_eq_iff_eq, hv'5]
  have h0 := hstar (t⁻¹ * a * t) (t'⁻¹ * b * t')
    (by
      rw [map_mul, map_mul, map_inv, htdef, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
        Subgroup.coe_mul, Subgroup.coe_inv, ha,
        show ((v : Perm (Fin n)))⁻¹ * c45 hn m * (v : Perm (Fin n)) =
          ((v : Perm (Fin n)))⁻¹ * c45 hn m * ((v : Perm (Fin n))⁻¹)⁻¹ by rw [inv_inv],
        conj_c45 hn hinv4 hinv5, Perm.inv_eq_iff_eq.mpr hv0.symm])
    (by
      rw [map_mul, map_mul, map_inv, ht'def, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
        Subgroup.coe_mul, Subgroup.coe_inv, hb,
        show ((v' : Perm (Fin n)))⁻¹ * c45 hn m' * (v' : Perm (Fin n)) =
          ((v' : Perm (Fin n)))⁻¹ * c45 hn m' * ((v' : Perm (Fin n))⁻¹)⁻¹ by rw [inv_inv],
        conj_c45 hn hinv4' hinv5', Perm.inv_eq_iff_eq.mpr hv'0.symm])
  have htb : (t : G) * b = b * t := (mem_centralizer_iff.mp htB b b.2).symm
  have ht'a : (t' : G) * (t⁻¹ * a * t : A) = (t⁻¹ * a * t : A) * t' :=
    (mem_centralizer_iff.mp ht'A _ (t⁻¹ * a * t).2).symm
  have e : ((t⁻¹ * a * t : A) : G) * ((t'⁻¹ * b * t' : B) : G) =
      ((t : G) * t')⁻¹ * ((a : G) * b) * (t * t') := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at ht'a ⊢
    calc (t : G)⁻¹ * a * t * ((t' : G)⁻¹ * b * t')
        = (t' : G)⁻¹ * ((t' : G) * ((t : G)⁻¹ * a * t)) * ((t' : G)⁻¹ * b * t') := by group
      _ = (t' : G)⁻¹ * (((t : G)⁻¹ * a * t) * t') * ((t' : G)⁻¹ * b * t') := by rw [ht'a]
      _ = (t' : G)⁻¹ * (t : G)⁻¹ * a * (t * b) * t' := by group
      _ = (t' : G)⁻¹ * (t : G)⁻¹ * a * (b * t) * t' := by rw [htb]
      _ = ((t : G) * t')⁻¹ * ((a : G) * b) * (t * t') := by group
  rw [e, sq] at h0
  rw [sq]
  have h1 : ((t : G) * t')⁻¹ * (((a : G) * b) * ((a : G) * b)) * ((t : G) * t') = 1 := by
    rw [← h0]
    group
  calc ((a : G) * b) * ((a : G) * b) = ((t : G) * t') * (((t : G) * t')⁻¹ *
      (((a : G) * b) * ((a : G) * b)) * ((t : G) * t')) * ((t : G) * t')⁻¹ := by group
    _ = 1 := by rw [h1]; group

variable (hU : ∀ (a : A) (b : B) (o : Fin n), 6 ≤ (o : ℕ) →
  (ψA a : Perm (Fin n)) = c45 hn o → (ψB b : Perm (Fin n)) = c45 hn o → (a : G) = b)

theorem tau45_of_ge {i : Fin n} (hi : 6 ≤ (i : ℕ)) : tau45 hn i = i :=
  Fin.ext (by rw [tau45_val]; split_ifs <;> omega)

theorem tau45_lt_four {i : Fin n} (hi2 : 2 ≤ (i : ℕ)) (hi6 : (i : ℕ) < 6) :
    ((tau45 hn i : Fin n) : ℕ) < 4 := by
  rw [tau45_val]
  split_ifs <;> omega

include hU in
theorem symm_gam_eq (k : CarmichaelIndex n) (hk : 6 ≤ (k : ℕ)) :
    ((ψA.symm (gam hn k) : A) : G) = ψB.symm (gam hn k) :=
  hU _ _ k hk (by rw [MulEquiv.apply_symm_apply, coe_gam, tau45_of_ge hn hk])
    (by rw [MulEquiv.apply_symm_apply, coe_gam, tau45_of_ge hn hk])

include hT hR hstar hU in
theorem glueFam_rel_lt_ge (k l : CarmichaelIndex (n + 4)) (hk : (k : ℕ) < n)
    (hl : n ≤ (l : ℕ)) : (glueFam hn ψA ψB k * glueFam hn ψA ψB l) ^ 2 = 1 := by
  have hl4 := l.1.isLt
  set k' : CarmichaelIndex n := ⟨⟨k, hk⟩, k.2⟩ with hk'
  set j : CarmichaelIndex n := ⟨⟨l - n + 2, by omega⟩, by simp⟩ with hj
  rw [glueFam_of_lt hn ψA ψB k hk, glueFam_of_ge hn ψA ψB l hl]
  by_cases h6 : 6 ≤ (k : ℕ)
  · rw [symm_gam_eq hn ψA ψB hU k' h6, ← Subgroup.coe_mul, ← Subgroup.coe_pow, ← map_mul,
      ← map_pow, gam_mul_sq hn (k := k') (l := j) (fun h => by
        have := congrArg (fun x : CarmichaelIndex n => ((x : Fin n) : ℕ)) h
        simp only [hk', hj] at this
        omega), map_one]
    rfl
  · push Not at h6
    exact cross_rel hn ψA ψB hT hR hstar (tau45_lt_four hn k'.2 h6)
      (tau45_lt_four hn j.2 (by simp only [hj]; omega)) _ _
      (by rw [MulEquiv.apply_symm_apply, coe_gam]) (by rw [MulEquiv.apply_symm_apply, coe_gam])

include hT hR hstar hU in
theorem glueFam_rel (k l : CarmichaelIndex (n + 4)) (hkl : k ≠ l) :
    (glueFam hn ψA ψB k * glueFam hn ψA ψB l) ^ 2 = 1 := by
  have hne : ((k : Fin (n + 4)) : ℕ) ≠ l := fun h => hkl (Subtype.ext (Fin.ext h))
  by_cases hk : (k : ℕ) < n
  · by_cases hl : (l : ℕ) < n
    · rw [glueFam_of_lt hn ψA ψB k hk, glueFam_of_lt hn ψA ψB l hl, ← Subgroup.coe_mul,
        ← Subgroup.coe_pow, ← map_mul, ← map_pow, gam_mul_sq hn (fun h => hne (by
          have := congrArg (fun x : CarmichaelIndex n => ((x : Fin n) : ℕ)) h
          simpa using this)), map_one]
      rfl
    · exact glueFam_rel_lt_ge hn ψA ψB hT hR hstar hU k l hk (by omega)
  · by_cases hl : (l : ℕ) < n
    · exact sq_mul_comm_of (glueFam_rel_lt_ge hn ψA ψB hT hR hstar hU l k hl (by omega))
    · have hk4 := k.1.isLt
      have hl4 := l.1.isLt
      rw [glueFam_of_ge hn ψA ψB k (by omega), glueFam_of_ge hn ψA ψB l (by omega),
        ← Subgroup.coe_mul, ← Subgroup.coe_pow, ← map_mul, ← map_pow,
        gam_mul_sq hn (fun h => hne (by
          have := congrArg (fun x : CarmichaelIndex n => ((x : Fin n) : ℕ)) h
          simp only at this
          omega)), map_one]
      rfl

include hT hR hstar hU in
theorem exists_hom_of_star :
    ∃ Φ : alternatingGroup (Fin (n + 4)) →* G, Function.Injective Φ ∧ Φ.range = A ⊔ B ∧
      (∀ z, Φ (liftA hn z) = ψA.symm z) ∧ (∀ z, Φ (liftB hn z) = ψB.symm z) := by
  have h3 : ∀ k, glueFam hn ψA ψB k ^ 3 = 1 := by
    intro k
    by_cases hk : (k : ℕ) < n
    · rw [glueFam_of_lt hn ψA ψB k hk, ← Subgroup.coe_pow, ← map_pow, gam_pow_three, map_one]
      rfl
    · rw [glueFam_of_ge hn ψA ψB k (by omega), ← Subgroup.coe_pow, ← map_pow, gam_pow_three,
        map_one]
      rfl
  have hrel := glueFam_rel hn ψA ψB hT hR hstar hU
  obtain ⟨φ, hφ⟩ := exists_hom_carmichaelCycle (n := n + 4) (by omega) (glueFam hn ψA ψB) h3
    hrel
  have hA : ∀ z, φ (liftA hn z) = ψA.symm z := by
    have heq : φ.comp (liftA hn) = A.subtype.comp ψA.symm.toMonoidHom := by
      apply MonoidHom.eq_of_eqOn_dense (closure_range_gam hn)
      rintro _ ⟨k, rfl⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
      rw [liftA_gam, hφ, glueFam_of_lt hn ψA ψB _ (by simp)]
    intro z
    exact DFunLike.congr_fun heq z
  have hB : ∀ z, φ (liftB hn z) = ψB.symm z := by
    have heq : φ.comp (liftB hn) = B.subtype.comp ψB.symm.toMonoidHom := by
      apply MonoidHom.eq_of_eqOn_dense (closure_range_gam hn)
      rintro _ ⟨k, rfl⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
      rw [liftB_gam, hφ]
      have hk2 := k.2
      have hkn := k.1.isLt
      by_cases h6 : 6 ≤ (k : ℕ)
      · have hv : ((embB hn k : Fin (n + 4)) : ℕ) = k := by
          rw [embB_val]
          split_ifs <;> omega
        rw [glueFam_of_lt hn ψA ψB _ (by simp only; omega)]
        rw [← symm_gam_eq hn ψA ψB hU k h6]
        congr 3
        exact Subtype.ext (Fin.ext hv)
      · push Not at h6
        have hv : ((embB hn k : Fin (n + 4)) : ℕ) = n + k - 2 := by
          rw [embB_val]
          split_ifs <;> omega
        rw [glueFam_of_ge hn ψA ψB _ (by simp only; omega)]
        congr 3
        exact Subtype.ext (Fin.ext (by simp only [hv]; omega))
    intro z
    exact DFunLike.congr_fun heq z
  have hinj : Function.Injective φ := by
    have hsimple := alternatingGroup.isSimpleGroup (α := Fin (n + 4)) (by simp; omega)
    rcases hsimple.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff φ).mp h
    · exfalso
      have hmem : carmichaelCycle (⟨⟨2, by omega⟩, le_rfl⟩ : CarmichaelIndex (n + 4)) ∈ φ.ker :=
        h ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker, hφ, glueFam_of_lt hn ψA ψB _ (show 2 < n by omega)] at hmem
      have h1 : ψA.symm (gam hn ⟨⟨2, by omega⟩, le_rfl⟩) = 1 := Subtype.ext hmem
      exact gam_ne_one hn _ (ψA.symm.map_eq_one_iff.mp h1)
  have hrange : φ.range = Subgroup.closure (Set.range (glueFam hn ψA ψB)) :=
    (alternating_carmichael_presentation_universal_map (by omega) _ h3 hrel).2.2 φ hφ
  refine ⟨φ, hinj, le_antisymm ?_ (sup_le ?_ ?_), hA, hB⟩
  · rw [hrange, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    by_cases hk : (k : ℕ) < n
    · rw [glueFam_of_lt hn ψA ψB k hk]
      exact le_sup_left (a := A) (ψA.symm _).2
    · rw [glueFam_of_ge hn ψA ψB k (by omega)]
      exact le_sup_right (b := B) (ψB.symm _).2
  · intro a ha
    have := hA (ψA ⟨a, ha⟩)
    rw [MulEquiv.symm_apply_apply] at this
    exact ⟨_, this⟩
  · intro b hb
    have := hB (ψB ⟨b, hb⟩)
    rw [MulEquiv.symm_apply_apply] at this
    exact ⟨_, this⟩

end CFSG.ComponentClassification.RankTwoAlt
