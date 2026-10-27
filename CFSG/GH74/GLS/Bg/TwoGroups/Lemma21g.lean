module

public import CFSG.GH74.GLS.Bg.TwoGroups.A44Facts4
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma21a
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma21c

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

open Subgroup

open A44

@[expose] noncomputable def S4B1 {B : Type} [CommGroup B] (e : B ≃* Z4Z4) : Subgroup (MulAut B) :=
  (subOfList S4list1 S4_1_closed).comap (phiB e).toMonoidHom

@[expose] noncomputable def S4B2 {B : Type} [CommGroup B] (e : B ≃* Z4Z4) : Subgroup (MulAut B) :=
  (subOfList S4list2 S4_2_closed).comap (phiB e).toMonoidHom

theorem mem_S4B1 {B : Type} [CommGroup B] (e : B ≃* Z4Z4) (φ : MulAut B) :
    φ ∈ S4B1 e ↔ (phiB e φ).1 ∈ S4list1 := Iff.rfl

theorem mem_S4B2 {B : Type} [CommGroup B] (e : B ≃* Z4Z4) (φ : MulAut B) :
    φ ∈ S4B2 e ↔ (phiB e φ).1 ∈ S4list2 := Iff.rfl

theorem card_S4B1 {B : Type} [CommGroup B] (e : B ≃* Z4Z4) : Nat.card (S4B1 e) = 24 := by
  rw [Nat.card_congr ((phiB e).toEquiv.subtypeEquiv (q := fun x : G96 => x.1 ∈ S4list1)
    (fun φ => mem_S4B1 e φ)), Nat.card_eq_fintype_card]
  exact card_S4_1

theorem card_S4B2 {B : Type} [CommGroup B] (e : B ≃* Z4Z4) : Nat.card (S4B2 e) = 24 := by
  rw [Nat.card_congr ((phiB e).toEquiv.subtypeEquiv (q := fun x : G96 => x.1 ∈ S4list2)
    (fun φ => mem_S4B2 e φ)), Nat.card_eq_fintype_card]
  exact card_S4_2

theorem card_perm4 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]; decide

noncomputable def S4B1_equiv {B : Type} [CommGroup B] (e : B ≃* Z4Z4) :
    S4B1 e ≃* Equiv.Perm (Fin 4) := by
  let f : S4B1 e →* Equiv.Perm (Fin 4) := (rho4B e).comp (S4B1 e).subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hk' : (phiB e (k : MulAut B)).1 ∈ S4list1 := k.2
    have h2 : (phiB e (k : MulAut B)).1 = M4.one := by
      apply S4_inj1 _ hk'
      intro j
      have := congrArg (fun p : Equiv.Perm (Fin 4) => p j) hk
      simpa [f, rho4B_apply] using this
    have h3 : (k : MulAut B) = 1 := by
      apply (phiB e).injective
      apply Subtype.ext
      rw [map_one, G96.val_one]; exact h2
    exact Subtype.ext h3
  have hcard : Nat.card (S4B1 e) = Nat.card (Equiv.Perm (Fin 4)) := by
    rw [card_S4B1, card_perm4]
  exact MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩)

noncomputable def S4B2_equiv {B : Type} [CommGroup B] (e : B ≃* Z4Z4) :
    S4B2 e ≃* Equiv.Perm (Fin 4) := by
  let f : S4B2 e →* Equiv.Perm (Fin 4) := (rho4B e).comp (S4B2 e).subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hk' : (phiB e (k : MulAut B)).1 ∈ S4list2 := k.2
    have h2 : (phiB e (k : MulAut B)).1 = M4.one := by
      apply S4_inj2 _ hk'
      intro j
      have := congrArg (fun p : Equiv.Perm (Fin 4) => p j) hk
      simpa [f, rho4B_apply] using this
    have h3 : (k : MulAut B) = 1 := by
      apply (phiB e).injective
      apply Subtype.ext
      rw [map_one, G96.val_one]; exact h2
    exact Subtype.ext h3
  have hcard : Nat.card (S4B2 e) = Nat.card (Equiv.Perm (Fin 4)) := by
    rw [card_S4B2, card_perm4]
  exact MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩)

theorem closure_c4_t4 :
    Subgroup.closure ({finRotate 4, Equiv.swap (0 : Fin 4) 1} : Set (Equiv.Perm (Fin 4))) = ⊤ := by
  have h := Equiv.Perm.closure_cycle_adjacent_swap (σ := finRotate 4)
    (isCycle_finRotate_of_le (by norm_num)) (support_finRotate_of_le (by norm_num)) 0
  have e : finRotate 4 0 = 1 := by decide
  rw [e] at h
  exact h

theorem rel_c4 : (finRotate 4 : Equiv.Perm (Fin 4)) ^ 4 = 1 := by decide +kernel
theorem ne_c4 : (finRotate 4 : Equiv.Perm (Fin 4)) ^ 2 ≠ 1 := by decide +kernel
theorem ne_t4 : (Equiv.swap (0 : Fin 4) 1 : Equiv.Perm (Fin 4)) ≠ 1 := by decide +kernel
theorem rel_t4 : (Equiv.swap (0 : Fin 4) 1 : Equiv.Perm (Fin 4)) *
    (Equiv.swap (0 : Fin 4) 1) = 1 := by decide +kernel
theorem rel_ct : ((finRotate 4 : Equiv.Perm (Fin 4)) * Equiv.swap (0 : Fin 4) 1) ^ 3 = 1 := by
  decide +kernel
theorem ne_ct : (finRotate 4 : Equiv.Perm (Fin 4)) * Equiv.swap (0 : Fin 4) 1 ≠ 1 := by
  decide +kernel

theorem Sigma4_eq {B : Type} [CommGroup B] (e : B ≃* Z4Z4) (K : Subgroup (MulAut B))
    (eK : K ≃* Equiv.Perm (Fin 4)) : K = S4B1 e ∨ K = S4B2 e := by
  let ψ : Equiv.Perm (Fin 4) →* MulAut B := K.subtype.comp eK.symm.toMonoidHom
  have hψ : Function.Injective ψ := by
    intro p q h
    exact eK.symm.injective (Subtype.ext h)
  set a := ψ (finRotate 4) with ha
  set b := ψ (Equiv.swap (0 : Fin 4) 1) with hb
  have hrange : ∀ k ∈ K, ∃ p : Equiv.Perm (Fin 4), ψ p = k := fun k hk =>
    ⟨eK ⟨k, hk⟩, by
      show ((eK.symm (eK ⟨k, hk⟩) : K) : MulAut B) = k
      rw [MulEquiv.symm_apply_apply]⟩
  have r1 : a ^ 4 = 1 := by rw [ha, ← map_pow, rel_c4, map_one]
  have r2 : a ^ 2 ≠ 1 := by
    intro h; apply ne_c4; apply hψ; rw [map_pow, map_one]; exact h
  have r3 : b ≠ 1 := by
    intro h; apply ne_t4; apply hψ; rw [map_one]; exact h
  have r4 : b * b = 1 := by rw [hb, ← map_mul, rel_t4, map_one]
  have r5 : (a * b) ^ 3 = 1 := by rw [ha, hb, ← map_mul, ← map_pow, rel_ct, map_one]
  have r6 : a * b ≠ 1 := by
    intro h; apply ne_ct; apply hψ; rw [map_mul, map_one]; exact h
  have hm : ∀ y : MulAut B, (phiB e y).1 = M4.one → y = 1 := by
    intro y hy
    apply (phiB e).injective
    apply Subtype.ext
    rw [map_one, G96.val_one]; exact hy
  have key := S4_gen (phiB e a) (phiB e b)
    (by
      have h4 : (phiB e a) ^ 4 = 1 := by rw [← map_pow, r1, map_one]
      have h4' : (phiB e a) ^ 4 = (phiB e a ^ 2) * (phiB e a ^ 2) := by rw [← pow_add]
      have := congrArg Subtype.val h4
      rw [h4', G96.val_mul, val_sq] at this
      exact this)
    (by
      intro h
      apply r2
      apply hm
      rw [map_pow, val_sq]
      exact h)
    (by intro h; exact r3 (hm _ h))
    (by
      have := congrArg (fun t => (phiB e t).1) r4
      simp only [map_mul, map_one, G96.val_mul, G96.val_one] at this
      exact this)
    (by
      have h3 : (phiB e (a * b)) ^ 3 = 1 := by rw [← map_pow, r5, map_one]
      have := congrArg Subtype.val h3
      rw [val_cube, map_mul, G96.val_mul] at this
      exact this)
    (by
      intro h
      apply r6
      apply hm
      rw [map_mul, G96.val_mul]; exact h)
  have hfin1 : Finite (S4B1 e) := Nat.finite_of_card_ne_zero (by rw [card_S4B1]; norm_num)
  have hfin2 : Finite (S4B2 e) := Nat.finite_of_card_ne_zero (by rw [card_S4B2]; norm_num)
  have hKcard : Nat.card K = 24 := by rw [Nat.card_congr eK.toEquiv, card_perm4]
  have hclo : ∀ L : Subgroup (MulAut B), a ∈ L → b ∈ L → K ≤ L := by
    intro L haL hbL k hk
    obtain ⟨p, rfl⟩ := hrange k hk
    have hcl : Subgroup.closure
        ({finRotate 4, Equiv.swap (0 : Fin 4) 1} : Set (Equiv.Perm (Fin 4))) ≤ L.comap ψ := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact haL
      · exact hbL
    rw [closure_c4_t4] at hcl
    exact hcl (Subgroup.mem_top p)
  rcases key with ⟨ha1, hb1⟩ | ⟨ha2, hb2⟩
  · left
    exact Subgroup.eq_of_le_of_card_ge (hclo (S4B1 e) ha1 hb1) (by rw [card_S4B1, hKcard])
  · right
    exact Subgroup.eq_of_le_of_card_ge (hclo (S4B2 e) ha2 hb2) (by rw [card_S4B2, hKcard])

theorem exists_notMem_ZB {B : Type} [CommGroup B] (e : B ≃* Z4Z4) : ∃ b : B, b ∉ ZB B := by
  refine ⟨e.symm (Multiplicative.ofAdd ((1 : ZMod 4), (0 : ZMod 4))), ?_⟩
  rw [mem_ZB_iff e]
  have : vec e (e.symm (Multiplicative.ofAdd ((1 : ZMod 4), (0 : ZMod 4)))) = (1, 0) := by
    simp [vec]
  rw [this]; decide

theorem IsDd_phi {B : Type} [CommGroup B] (e : B ≃* Z4Z4) {x d : MulAut B}
    (hx : orderOf x = 3) (hd : IsDd B x d) :
    (phiB e d).1 = dd ∨ (phiB e d).1 = M4.mul dd iota := by
  obtain ⟨hdA0, hcent, hcard, hsq, hCB1, hCB2⟩ := hd
  have hmem : d ∈ zpowers (iotaB B) ⊔ zpowers (dB e) := by
    rw [← cent_A0_eq e hx, hcent]
    exact mem_sup_right (mem_zpowers d)
  rw [mem_iota_dB] at hmem
  obtain ⟨b0, hb0⟩ := exists_notMem_ZB e
  simp only [C4list, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h
  · exfalso
    have hd1 : d = 1 :=
      (phiB e).injective (Subtype.ext (by rw [map_one, G96.val_one]; exact h))
    apply hb0
    rw [← hCB1]
    show d b0 = b0
    rw [hd1]; rfl
  · exfalso
    have hd1 : d = iotaB B :=
      (phiB e).injective (Subtype.ext (by rw [phiB_iota]; exact h))
    apply hb0
    rw [← hCB2]
    show (d * iotaB B) b0 = b0
    rw [hd1, iotaB_mul_self e]; rfl
  · left; exact h
  · right; rw [h]; exact iota_dd_comm

theorem iv2_2_1_i : IV2_2_1_i := by
  intro B _ ⟨e⟩ x hx d hd
  have hdd := IsDd_phi e hx hd
  have hdsq : d * d = 1 := hd.2.2.2.1 d (mem_sup_right (mem_zpowers d))
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdsq
  have hyin : (phiB e d).1 ∈ [dd, M4.mul dd iota] := by
    rcases hdd with h | h <;> simp [h]
  refine ⟨S4B1 e, S4B2 e, ?_, ⟨S4B1_equiv e⟩, ⟨S4B2_equiv e⟩, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨k, hk1, hk2⟩ := S4_distinct
    have hkI : k.IsInv := S4_1_closed.1 k hk1
    have hmem : (phiB e).symm (G96.mk k hkI) ∈ S4B1 e := by
      rw [mem_S4B1, MulEquiv.apply_symm_apply]; exact hk1
    rw [h, mem_S4B2, MulEquiv.apply_symm_apply] at hmem
    exact hk2 hmem
  · rintro K ⟨eK⟩
    exact Sigma4_eq e K eK
  · intro a
    rw [hdinv, mem_S4B2, mem_S4B1]
    have : (phiB e (d * a * d)).1 = M4.mul (M4.mul (phiB e d).1 (phiB e a).1) (phiB e d).1 := by
      rw [map_mul, map_mul]; rfl
    rw [this]
    exact (S4_swap _ hyin (phiB e a).1 (phiB e a).2).1.symm
  · intro a
    rw [hdinv, mem_S4B2, mem_S4B1]
    have : (phiB e (d * a * d)).1 = M4.mul (M4.mul (phiB e d).1 (phiB e a).1) (phiB e d).1 := by
      rw [map_mul, map_mul]; rfl
    rw [this]
    exact (S4_swap _ hyin (phiB e a).1 (phiB e a).2).2.symm

end CFSG.GH74.GLS.Bg.TwoGroups
