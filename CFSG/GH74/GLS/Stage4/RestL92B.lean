module

public import CFSG.GH74.GLS.Stage4.RestL92A
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution

public section

namespace CFSG.GH74.GLS.Stage4.Rest.L92

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.GLS.Stage4.Rest.DodecA CFSG.GH74.BNPair

variable {G : Type} [Group G]

@[expose] def fourSub (z u : G) : Subgroup G := Subgroup.closure {z, u}

theorem fourSub_mem {z u : G} (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z) {x : G} :
    x ∈ fourSub z u ↔ x = 1 ∨ x = z ∨ x = u ∨ x = z * u := by
  have hz : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul a b _ _ ha hb =>
      have e4 : z * (z * u) = u := by
        calc z * (z * u) = (z * z) * u := by group
          _ = u := by rw [hz2, one_mul]
      have e5 : u * (z * u) = z := by
        calc u * (z * u) = (u * z) * u := by group
          _ = (z * u) * u := by rw [hzu]
          _ = z := by rw [mul_assoc, hu2, mul_one]
      have e6 : z * u * z = u := by
        calc z * u * z = (u * z) * z := by rw [hzu]
          _ = u := by rw [mul_assoc, hz2, mul_one]
      have e7 : z * u * u = z := by
        calc z * u * u = z * (u * u) := by group
          _ = z := by rw [hu2, mul_one]
      have e8 : z * u * (z * u) = 1 := by
        calc z * u * (z * u) = z * (u * z) * u := by group
          _ = z * (z * u) * u := by rw [← hzu]
          _ = (z * z) * (u * u) := by group
          _ = 1 := by rw [hz2, hu2, one_mul]
      have e9 : u * z = z * u := hzu.symm
      rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;> rw [ha, hb] <;>
        simp [hz2, hu2, e4, e5, e6, e7, e8, e9]
    | inv a _ ha =>
      have e9 : u * z = z * u := hzu.symm
      rcases ha with ha | ha | ha | ha <;> rw [ha]
      · simp
      · simp [hz]
      · simp [hu]
      · have : (z * u)⁻¹ = z * u := by
          calc (z * u)⁻¹ = u⁻¹ * z⁻¹ := by group
            _ = u * z := by rw [hu, hz]
            _ = z * u := hzu.symm
        simp [this]
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem fourSub_isKleinFour {z u : G} (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z)
    (hz1 : z ≠ 1) (hu1 : u ≠ 1) (hne : z ≠ u) : IsKleinFour ↥(fourSub z u) := by
  have hmem := fun x : G => fourSub_mem hz2 hu2 hzu (x := x)
  have hzu1 : z * u ≠ 1 := by
    intro h
    exact hne (mul_eq_one_iff_eq_inv.1 h |>.trans (inv_eq_of_mul_eq_one_right hu2))
  have hzuz : z * u ≠ z := by
    intro h
    apply hu1
    simpa using h
  have hzuu : z * u ≠ u := by
    intro h
    apply hz1
    simpa using h
  have hset : (fourSub z u : Set G) = {1, z, u, z * u} := by
    ext x
    simp only [SetLike.mem_coe, hmem, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hcard : Nat.card ↥(fourSub z u) = 4 := by
    have h1 : Nat.card ↥(fourSub z u) = (fourSub z u : Set G).ncard :=
      Nat.card_coe_set_eq (fourSub z u : Set G)
    rw [h1, hset]
    have n1 : (1 : G) ∉ ({z, u, z * u} : Set G) := by simp [hz1.symm, hu1.symm, hzu1.symm]
    have n2 : z ∉ ({u, z * u} : Set G) := by simp [hne, hzuz.symm]
    have n3 : u ∉ ({z * u} : Set G) := by simp [hzuu.symm]
    rw [Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2, Set.ncard_insert_of_notMem n3,
      Set.ncard_singleton]
  refine ⟨hcard, ?_⟩
  have hsq : ∀ x : ↥(fourSub z u), x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    have hx := (hmem x).1 x.2
    show (x : G) ^ 2 = 1
    rcases hx with h | h | h | h <;> rw [h]
    · simp
    · rw [pow_two]; exact hz2
    · rw [pow_two]; exact hu2
    · rw [pow_two]
      calc z * u * (z * u) = z * (u * z) * u := by group
        _ = z * (z * u) * u := by rw [← hzu]
        _ = (z * z) * (u * u) := by group
        _ = 1 := by rw [hz2, hu2, one_mul]
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with h | h
  · have : Subsingleton ↥(fourSub z u) := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : ↥(fourSub z u))
    omega
  · exact h

theorem hequiv_refl (H A : Subgroup G) : HEquiv H A A := ⟨MulEquiv.refl _, fun _ _ _ _ => rfl⟩

theorem inf_eq_bot_of_inequiv {H A B : Subgroup G} (hAH : HInv H A) (hBH : HInv H B)
    (hAirr : Irr H A) (hBirr : Irr H B) (hA0 : A ≠ ⊥) (hne : ¬ HEquiv H A B) : A ⊓ B = ⊥ := by
  rcases hAirr (A ⊓ B) inf_le_left (hinv_inf hAH hBH) with h | h
  · exact h
  · exfalso
    have hAB : A ≤ B := h ▸ inf_le_right
    rcases hBirr A hAB hAH with h0 | h1
    · exact hA0 h0
    · exact hne (h1 ▸ hequiv_refl H A)

theorem card_eq_inf_two {H A B M : Subgroup G} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAH : HInv H A) (hBH : HInv H B) (hAirr : Irr H A) (hBirr : Irr H B) (hA0 : A ≠ ⊥)
    (hne : ¬ HEquiv H A B) (hMle : M ≤ A ⊔ B) (hM : HInv H M) :
    Nat.card ↥M = Nat.card ↥(M ⊓ A) * Nat.card ↥(M ⊓ B) := by
  have hAB := inf_eq_bot_of_inequiv hAH hBH hAirr hBirr hA0 hne
  obtain ⟨hdec, -, -⟩ := hinv_sup_two hcomm hAH hBH hAirr hBirr hne hMle hM
  rw [← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun p : ↥(M ⊓ A) × ↥(M ⊓ B) => (⟨(p.1 : G) * (p.2 : G), M.mul_mem p.1.2.1 p.2.2.1⟩ : ↥M))
    ⟨?_, ?_⟩)).symm
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    have h1 : a * b = a' * b' := congrArg Subtype.val h
    have h2 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h1]
        _ = b' * b⁻¹ := by group
    have h3 : a'⁻¹ * a ∈ A ⊓ B := ⟨A.mul_mem (A.inv_mem ha'.2) ha.2, by
      rw [h2]; exact B.mul_mem hb'.2 (B.inv_mem hb.2)⟩
    rw [hAB, Subgroup.mem_bot] at h3
    have ha : a' = a := inv_mul_eq_one.1 h3
    subst ha
    have : b = b' := mul_left_cancel h1
    subst this
    rfl
  · rintro ⟨m, hm⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec m hm
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

theorem not_le_sup_two {H A B C : Subgroup G} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAH : HInv H A) (hBH : HInv H B) (hCH : HInv H C) (hAirr : Irr H A) (hBirr : Irr H B)
    (hCirr : Irr H C) (hA0 : A ≠ ⊥) (hB0 : B ≠ ⊥) (hC0 : C ≠ ⊥) (hne : ¬ HEquiv H A B)
    (hAC : ¬ HEquiv H C A) (hBC : ¬ HEquiv H C B) : ¬ C ≤ A ⊔ B := by
  intro hle
  obtain ⟨hdec, hCA, hCB⟩ := hinv_sup_two hcomm hAH hBH hAirr hBirr hne hle hCH
  have hAC' : ¬ A ≤ C := by
    intro h
    rcases hCirr A h hAH with h0 | h1
    · exact hA0 h0
    · exact hAC (h1 ▸ hequiv_refl H C)
  have hBC' : ¬ B ≤ C := by
    intro h
    rcases hCirr B h hBH with h0 | h1
    · exact hB0 h0
    · exact hBC (h1 ▸ hequiv_refl H C)
  have hCA0 : C ⊓ A = ⊥ := hCA.resolve_right (fun h => hAC' (h ▸ inf_le_left))
  have hCB0 : C ⊓ B = ⊥ := hCB.resolve_right (fun h => hBC' (h ▸ inf_le_left))
  apply hC0
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨a, ha, b, hb, rfl⟩ := hdec c hc
  rw [hCA0, Subgroup.mem_bot] at ha
  rw [hCB0, Subgroup.mem_bot] at hb
  simp [ha, hb]

theorem card_inf_sup_two {H A B Z : Subgroup G} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAH : HInv H A) (hBH : HInv H B) (hAirr : Irr H A) (hBirr : Irr H B) (hA0 : A ≠ ⊥)
    (hne : ¬ HEquiv H A B) (hZ : HInv H Z) :
    Nat.card ↥(Z ⊓ (A ⊔ B)) = Nat.card ↥(Z ⊓ A) * Nat.card ↥(Z ⊓ B) := by
  have h := card_eq_inf_two (M := Z ⊓ (A ⊔ B)) hcomm hAH hBH hAirr hBirr hA0 hne inf_le_right
    (hinv_inf hZ (hinv_sup hAH hBH))
  have e1 : Z ⊓ (A ⊔ B) ⊓ A = Z ⊓ A := by
    rw [inf_assoc, inf_eq_right.2 (le_sup_left : A ≤ A ⊔ B)]
  have e2 : Z ⊓ (A ⊔ B) ⊓ B = Z ⊓ B := by
    rw [inf_assoc, inf_eq_right.2 (le_sup_right : B ≤ A ⊔ B)]
  rwa [e1, e2] at h

structure L92Data (p : ℕ) (H P : Subgroup G) (z u : G) (R : ℤ → Subgroup G) : Prop where
  prime : p.Prime
  p_ne_two : p ≠ 2
  P_pGroup : IsPGroup p ↥P
  zz : z * z = 1
  uu : u * u = 1
  zu_comm : z * u = u * z
  z_ne : z ≠ 1
  u_ne : u ≠ 1
  zu_ne : z ≠ u
  z_mem : z ∈ H
  u_mem : u ∈ H
  inv : ∀ i : ℤ, 1 ≤ i → i ≤ 6 → HInv H (R i)
  ne_bot : ∀ i : ℤ, 1 ≤ i → i ≤ 6 → R i ≠ ⊥
  irr : ∀ i : ℤ, 1 ≤ i → i ≤ 6 → Irr H (R i)
  inequiv : ∀ i j : ℤ, 1 ≤ i → i ≤ 6 → 1 ≤ j → j ≤ 6 → i ≠ j → ¬ HEquiv H (R i) (R j)
  comm₁ : ∀ x ∈ R 1, ∀ y ∈ R 4, x * y = y * x
  comm₂ : ∀ x ∈ R 3, ∀ y ∈ R 6, x * y = y * x
  comm₃ : ∀ x ∈ R 5, ∀ y ∈ R 2, x * y = y * x
  cent_z : P ⊓ centralizer ({z} : Set G) = R 1 ⊔ R 4
  cent_u : P ⊓ centralizer ({u} : Set G) = R 3 ⊔ R 6
  cent_zu : P ⊓ centralizer ({z * u} : Set G) = R 5 ⊔ R 2

section Card

variable {p : ℕ} {H P : Subgroup G} {z u : G} {R : ℤ → Subgroup G}

theorem L92Data.cent_inf (hd : L92Data p H P z u R) : (R 1 ⊔ R 4) ⊓ (R 3 ⊔ R 6) = ⊥ := by
  have h36 := hd.inequiv 3 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h13 := hd.inequiv 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h16 := hd.inequiv 1 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h43 := hd.inequiv 4 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h46 := hd.inequiv 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h14 := hd.inequiv 1 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have i1 := hd.inv 1 (by norm_num) (by norm_num)
  have i4 := hd.inv 4 (by norm_num) (by norm_num)
  have i3 := hd.inv 3 (by norm_num) (by norm_num)
  have i6 := hd.inv 6 (by norm_num) (by norm_num)
  have r1 := hd.irr 1 (by norm_num) (by norm_num)
  have r4 := hd.irr 4 (by norm_num) (by norm_num)
  have r3 := hd.irr 3 (by norm_num) (by norm_num)
  have r6 := hd.irr 6 (by norm_num) (by norm_num)
  have n1 := hd.ne_bot 1 (by norm_num) (by norm_num)
  have n4 := hd.ne_bot 4 (by norm_num) (by norm_num)
  have n3 := hd.ne_bot 3 (by norm_num) (by norm_num)
  have n6 := hd.ne_bot 6 (by norm_num) (by norm_num)
  set M₀ := (R 1 ⊔ R 4) ⊓ (R 3 ⊔ R 6) with hM₀
  have hM₀H : HInv H M₀ := hinv_inf (hinv_sup i1 i4) (hinv_sup i3 i6)
  obtain ⟨hdec, hM1, hM4⟩ := hinv_sup_two hd.comm₁ i1 i4 r1 r4 h14 (inf_le_left : M₀ ≤ R 1 ⊔ R 4) hM₀H
  have hM1' : M₀ ⊓ R 1 = ⊥ := by
    refine hM1.resolve_right (fun h => ?_)
    have : R 1 ≤ M₀ := h.symm.le.trans inf_le_left
    exact not_le_sup_two hd.comm₂ i3 i6 i1 r3 r6 r1 n3 n6 n1 h36 h13 h16 (this.trans inf_le_right)
  have hM4' : M₀ ⊓ R 4 = ⊥ := by
    refine hM4.resolve_right (fun h => ?_)
    have : R 4 ≤ M₀ := h.symm.le.trans inf_le_left
    exact not_le_sup_two hd.comm₂ i3 i6 i4 r3 r6 r4 n3 n6 n4 h36 h43 h46 (this.trans inf_le_right)
  rw [eq_bot_iff]
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := hdec m hm
  rw [hM1', Subgroup.mem_bot] at ha
  rw [hM4', Subgroup.mem_bot] at hb
  simp [ha, hb]

theorem L92Data.card_eq [Finite G] (hd : L92Data p H P z u R) {Z : Subgroup G} (hZP : Z ≤ P)
    (hZ : HInv H Z) :
    (∀ i : ℤ, 1 ≤ i → i ≤ 6 → Z ⊓ R i = ⊥ ∨ Z ⊓ R i = R i) ∧
      Nat.card ↥Z = Nat.card ↥(Z ⊓ R 1) * Nat.card ↥(Z ⊓ R 4) *
        (Nat.card ↥(Z ⊓ R 3) * Nat.card ↥(Z ⊓ R 6)) *
        (Nat.card ↥(Z ⊓ R 5) * Nat.card ↥(Z ⊓ R 2)) := by
  refine ⟨fun i h1 h6 => (hd.irr i h1 h6).inf (hd.inv i h1 h6) hZ, ?_⟩
  have h14 := hd.inequiv 1 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h36 := hd.inequiv 3 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h52 := hd.inequiv 5 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hT := fourSub_isKleinFour hd.zz hd.uu hd.zu_comm hd.z_ne hd.u_ne hd.zu_ne
  have hzT : z ∈ fourSub z u := (fourSub_mem hd.zz hd.uu hd.zu_comm).2 (Or.inr (Or.inl rfl))
  have huT : u ∈ fourSub z u := (fourSub_mem hd.zz hd.uu hd.zu_comm).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hTle : fourSub z u ≤ normalizer (Z : Set G) := by
    intro g hg
    have hgH : g ∈ H := by
      rcases (fourSub_mem hd.zz hd.uu hd.zu_comm).1 hg with rfl | rfl | rfl | rfl
      · exact H.one_mem
      · exact hd.z_mem
      · exact hd.u_mem
      · exact H.mul_mem hd.z_mem hd.u_mem
    exact Subgroup.mem_normalizer_iff.2 (inv_iff_of_inv hZ hgH)
  have hodd : Odd (Nat.card ↥Z) := by
    have := Fact.mk hd.prime
    obtain ⟨k, hk⟩ := (hd.P_pGroup.to_le hZP).exists_card_eq
    rw [hk]
    exact (hd.prime.eq_two_or_odd'.resolve_left hd.p_ne_two).pow
  have hBW := CFSG.ABGLocalTools.card_mul_card_centralizer_four_sq (T := fourSub z u) (K := Z) hodd
    hTle hzT huT hd.z_ne hd.u_ne hd.zu_ne
  have hCT : Z ⊓ centralizer ((fourSub z u : Subgroup G) : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxZ, hxT⟩
    rw [CFSG.ABGLocalTools.centralizer_kleinFour_eq hzT huT hd.z_ne hd.u_ne hd.zu_ne] at hxT
    have h1 : x ∈ R 1 ⊔ R 4 := by
      rw [← hd.cent_z]
      exact ⟨hZP hxZ, hxT.1⟩
    have h2 : x ∈ R 3 ⊔ R 6 := by
      rw [← hd.cent_u]
      exact ⟨hZP hxZ, hxT.2⟩
    have : x ∈ (R 1 ⊔ R 4) ⊓ (R 3 ⊔ R 6) := ⟨h1, h2⟩
    rw [hd.cent_inf] at this
    exact this
  have hzu : z * u ∈ fourSub z u := (fourSub_mem hd.zz hd.uu hd.zu_comm).2 (Or.inr (Or.inr (Or.inr rfl)))
  have eZ : ∀ (c : G) (A : Subgroup G), P ⊓ centralizer ({c} : Set G) = A →
      Z ⊓ centralizer ({c} : Set G) = Z ⊓ A := by
    intro c A hA
    rw [← hA, ← inf_assoc, inf_eq_left.2 hZP]
  have hcard1 : Nat.card ↥(Z ⊓ centralizer ({z} : Set G)) =
      Nat.card ↥(Z ⊓ R 1) * Nat.card ↥(Z ⊓ R 4) := by
    rw [eZ z _ hd.cent_z]
    exact card_inf_sup_two hd.comm₁ (hd.inv 1 (by norm_num) (by norm_num))
      (hd.inv 4 (by norm_num) (by norm_num)) (hd.irr 1 (by norm_num) (by norm_num))
      (hd.irr 4 (by norm_num) (by norm_num)) (hd.ne_bot 1 (by norm_num) (by norm_num)) h14 hZ
  have hcard2 : Nat.card ↥(Z ⊓ centralizer ({u} : Set G)) =
      Nat.card ↥(Z ⊓ R 3) * Nat.card ↥(Z ⊓ R 6) := by
    rw [eZ u _ hd.cent_u]
    exact card_inf_sup_two hd.comm₂ (hd.inv 3 (by norm_num) (by norm_num))
      (hd.inv 6 (by norm_num) (by norm_num)) (hd.irr 3 (by norm_num) (by norm_num))
      (hd.irr 6 (by norm_num) (by norm_num)) (hd.ne_bot 3 (by norm_num) (by norm_num)) h36 hZ
  have hcard3 : Nat.card ↥(Z ⊓ centralizer ({z * u} : Set G)) =
      Nat.card ↥(Z ⊓ R 5) * Nat.card ↥(Z ⊓ R 2) := by
    rw [eZ (z * u) _ hd.cent_zu]
    exact card_inf_sup_two hd.comm₃ (hd.inv 5 (by norm_num) (by norm_num))
      (hd.inv 2 (by norm_num) (by norm_num)) (hd.irr 5 (by norm_num) (by norm_num))
      (hd.irr 2 (by norm_num) (by norm_num)) (hd.ne_bot 5 (by norm_num) (by norm_num)) h52 hZ
  rw [hCT, Subgroup.card_bot, hcard1, hcard2, hcard3] at hBW
  simpa using hBW

end Card

end CFSG.GH74.GLS.Stage4.Rest.L92
