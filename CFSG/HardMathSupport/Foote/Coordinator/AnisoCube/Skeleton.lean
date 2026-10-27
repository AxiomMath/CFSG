module

public import CFSG.LieType.SeitzGeneration.OrthCubeBlocks
public import CFSG.LieType.SeitzGeneration.HyperEx

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.AnisoCube

open CFSG.Open CFSG.LieType.SeitzGeneration

section SL3

variable {K : Type} [Field K] [Finite K]

theorem exists_sl3_orderOf {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hpq : p ∣ Nat.card K ^ 2 + Nat.card K + 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) K, orderOf g = p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let _ : Fintype K := Fintype.ofFinite K
  have hqK : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
  obtain ⟨m, hm⟩ : ∃ m, Nat.card K = m + 1 := ⟨Nat.card K - 1, by
    have := (Nat.card_pos : 0 < Nat.card K); omega⟩
  have hpq1 : ¬ p ∣ m := by
    intro h
    have h3 : p ∣ 3 := by
      have he : Nat.card K ^ 2 + Nat.card K + 1 = m * (m + 3) + 3 := by rw [hm]; ring
      rw [he] at hpq
      exact (Nat.dvd_add_right (dvd_mul_of_dvd_left h _)).1 hpq
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3)
  have hGL : p ∣ Nat.card (GL (Fin 3) K) := by
    rw [Matrix.card_GL_field, Fin.prod_univ_three, ← hqK, hm]
    refine dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ?_ _) _
    have he : (m + 1) ^ 3 - (m + 1) ^ ((0 : Fin 3) : ℕ) = m * ((m + 1) ^ 2 + (m + 1) + 1) := by
      have h3 : (m + 1) ^ 3 = m * ((m + 1) ^ 2 + (m + 1) + 1) + 1 := by ring
      simp only [Fin.val_zero, pow_zero]
      omega
    rw [he, ← hm]
    exact dvd_mul_of_dvd_right hpq _
  have hSL : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) := by
    have h := Matrix.card_SL_mul_card_units (n := Fin 3) (R := K)
    rw [Nat.card_units, hm, Nat.add_sub_cancel] at h
    rw [← h] at hGL
    exact (Nat.Prime.dvd_mul hp).1 hGL |>.resolve_right hpq1
  exact exists_prime_orderOf_dvd_card' p hSL

omit [Finite K] in
theorem eq_one_of_commute_sl3 {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {x : Matrix.SpecialLinearGroup (Fin 3) K} (hxp : x ^ p = 1) (hx : ∀ A, Commute x A) :
    x = 1 := by
  have hc : x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) :=
    Subgroup.mem_center_iff.2 fun A => (hx A).eq.symm
  obtain ⟨r, hr3, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  rw [Fintype.card_fin] at hr3
  have hrp : r ^ p = 1 := by
    have h := congrArg (fun y : Matrix.SpecialLinearGroup (Fin 3) K =>
      (y : Matrix (Fin 3) (Fin 3) K) 0 0) hxp
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at h
    rw [← hrx, ← map_pow, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq] at h
    exact h
  have hr1 : r = 1 := by
    have h3 : orderOf r ∣ 3 := orderOf_dvd_of_pow_eq_one hr3
    have hpd : orderOf r ∣ p := orderOf_dvd_of_pow_eq_one hrp
    have hcop : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)
    have h1 : orderOf r ∣ 1 := by
      have := Nat.dvd_gcd h3 hpd
      rwa [hcop.gcd_eq_one] at this
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)
  ext i j
  rw [← hrx, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

end SL3

section Frame

variable {C : Type*} [Group C] {L : Type*} [Group L]

@[expose] def cube (ψ : Fin 3 → L →* C) (g : L) : Subgroup C :=
  Subgroup.closure {ψ 0 g, ψ 1 g, ψ 2 g}

@[expose] def plane (ψ : Fin 3 → L →* C) (g : L) : Subgroup C :=
  Subgroup.closure {ψ 0 g, ψ 1 g}

variable {ψ : Fin 3 → L →* C} {g : L} {p : ℕ}

theorem mem_cube (i : Fin 3) : ψ i g ∈ cube ψ g := by
  refine Subgroup.subset_closure ?_
  have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi3 with rfl | rfl | rfl <;> simp

theorem plane_le_cube : plane ψ g ≤ cube ψ g :=
  Subgroup.closure_mono (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)

theorem dvd_of_commute_range_of_center (hinj : ∀ i, Function.Injective (ψ i))
    (hZ : ∀ x : L, x ^ p = 1 → (∀ A, Commute x A) → x = 1)
    (hg : orderOf g = p) (i : Fin 3) (a : ℤ) (h : ∀ A, Commute (ψ i (g ^ a)) (ψ i A)) :
    (p : ℤ) ∣ a := by
  have hcomm' : ∀ A, Commute (g ^ a) A := fun A =>
    hinj i (by rw [map_mul, map_mul]; exact (h A).eq)
  have hgp : g ^ p = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hga : g ^ a = 1 := by
    refine hZ _ ?_ hcomm'
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hgp,
      one_zpow]
  rw [← hg]
  exact orderOf_dvd_iff_zpow_eq_one.2 hga

theorem cube_spec_of_center (hinj : ∀ i, Function.Injective (ψ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) (hp : p.Prime)
    (hZ : ∀ x : L, x ^ p = 1 → (∀ A, Commute x A) → x = 1) (hg : orderOf g = p) :
    IsElemAbelian p (cube ψ g) ∧ Nat.card (cube ψ g) = p ^ 3 ∧
      ∀ x ∈ cube ψ g, ∃ i j k : ℤ, x = ψ 0 g ^ i * ψ 1 g ^ j * ψ 2 g ^ k := by
  have hgp : g ^ p = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have key := dvd_of_commute_range_of_center hinj hZ hg
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  obtain ⟨E, hE, hc, hgen, h0E, h1E, h2E⟩ := exists_cube_of_three hp
    (hcomm 0 1 h01 g g) (hcomm 0 2 h02 g g) (hcomm 1 2 h12 g g)
    (by rw [← map_pow, hgp, map_one]) (by rw [← map_pow, hgp, map_one])
    (by rw [← map_pow, hgp, map_one]) (by
      intro a b c habc
      have h0 : (p : ℤ) ∣ a := by
        refine key 0 a fun A => ?_
        have he : ψ 0 (g ^ a) = (ψ 1 g ^ b * ψ 2 g ^ c)⁻¹ := by
          rw [map_zpow]
          exact eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact habc)
        rw [he]
        refine Commute.inv_left (Commute.mul_left ?_ ?_)
        · exact ((hcomm 0 1 h01 A g).symm).zpow_left b
        · exact ((hcomm 0 2 h02 A g).symm).zpow_left c
      have ha : ψ 0 g ^ a = 1 := by
        obtain ⟨k, hk⟩ := h0
        rw [hk, ← map_zpow, _root_.zpow_mul, zpow_natCast, hgp, one_zpow, map_one]
      rw [ha, one_mul] at habc
      have h1 : (p : ℤ) ∣ b := by
        refine key 1 b fun A => ?_
        have he : ψ 1 (g ^ b) = (ψ 2 g ^ c)⁻¹ := by
          rw [map_zpow]
          exact eq_inv_of_mul_eq_one_left habc
        rw [he]
        exact Commute.inv_left (((hcomm 1 2 h12 A g).symm).zpow_left c)
      have hb : ψ 1 g ^ b = 1 := by
        obtain ⟨k, hk⟩ := h1
        rw [hk, ← map_zpow, _root_.zpow_mul, zpow_natCast, hgp, one_zpow, map_one]
      rw [hb, one_mul] at habc
      refine ⟨h0, h1, ?_⟩
      refine key 2 c fun A => ?_
      rw [map_zpow, habc]
      exact Commute.one_left _)
  have hEq : cube ψ g = E := by
    refine le_antisymm ?_ ?_
    · refine (Subgroup.closure_le _).2 ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      exacts [h0E, h1E, h2E]
    · intro x hx
      obtain ⟨i, j, k, rfl⟩ := hgen x hx
      exact (cube ψ g).mul_mem ((cube ψ g).mul_mem ((cube ψ g).zpow_mem (mem_cube 0) i)
        ((cube ψ g).zpow_mem (mem_cube 1) j)) ((cube ψ g).zpow_mem (mem_cube 2) k)
  rw [hEq]
  exact ⟨hE, hc, hgen⟩

theorem relIndex_cube_inf_centralizer_of_center (hinj : ∀ i, Function.Injective (ψ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) (hp : p.Prime)
    (hZ : ∀ x : L, x ^ p = 1 → (∀ A, Commute x A) → x = 1) (hg : orderOf g = p) (i : Fin 3) :
    (cube ψ g ⊓ Subgroup.centralizer ((ψ i).range : Set C)).relIndex (cube ψ g) = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hE, -, hgen⟩ := cube_spec_of_center hinj hcomm hp hZ hg
  have hgp : g ^ p = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  set E := cube ψ g with hEdef
  set F := E ⊓ Subgroup.centralizer ((ψ i).range : Set C) with hFdef
  have hcent : ∀ j, j ≠ i → ψ j g ∈ Subgroup.centralizer ((ψ i).range : Set C) := by
    intro j hji
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨A, rfl⟩
    exact (hcomm i j (Ne.symm hji) A g).eq
  have hnot : ψ i g ∉ F := by
    intro h
    have h1 := dvd_of_commute_range_of_center hinj hZ hg i 1 (fun A => by
      rw [zpow_one]
      exact ((Subgroup.mem_centralizer_iff.1 h.2) _ ⟨A, rfl⟩).symm)
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1)
  have hcommE : ∀ a b : E, a * b = b * a := fun a b => hE.1.is_comm.comm a b
  have : (F.subgroupOf E).Normal := ⟨fun n hn g' => by
    have : g' * n * g'⁻¹ = n := by rw [hcommE g' n, mul_inv_cancel_right]
    rw [this]; exact hn⟩
  let e : Fin 3 → E := fun j => ⟨ψ j g, mem_cube j⟩
  have hmk : ∀ j, j ≠ i → (QuotientGroup.mk (e j) : E ⧸ F.subgroupOf E) = 1 := by
    intro j hji
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨mem_cube j, hcent j hji⟩
  have hgen' : ∀ x : E, ∃ a : ℤ,
      (QuotientGroup.mk x : E ⧸ F.subgroupOf E) = QuotientGroup.mk (e i) ^ a := by
    intro x
    obtain ⟨a0, a1, a2, hx⟩ := hgen x x.2
    have hx' : x = e 0 ^ a0 * e 1 ^ a1 * e 2 ^ a2 := Subtype.ext (by simp [hx, e])
    rw [hx', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_zpow,
      QuotientGroup.mk_zpow, QuotientGroup.mk_zpow]
    have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hi3 with rfl | rfl | rfl
    · exact ⟨a0, by rw [hmk 1 (by decide), hmk 2 (by decide)]; simp⟩
    · exact ⟨a1, by rw [hmk 0 (by decide), hmk 2 (by decide)]; simp⟩
    · exact ⟨a2, by rw [hmk 0 (by decide), hmk 1 (by decide)]; simp⟩
  have htop : Subgroup.zpowers (QuotientGroup.mk (e i) : E ⧸ F.subgroupOf E) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, ha⟩ := hgen' x
    exact ⟨a, ha.symm⟩
  have hord : orderOf (QuotientGroup.mk (e i) : E ⧸ F.subgroupOf E) = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow]
      have : e i ^ p = 1 := Subtype.ext (by
        simp only [Subgroup.coe_pow, Subgroup.coe_one, e, ← map_pow, hgp, map_one])
      rw [this, QuotientGroup.mk_one]
    · intro h
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
      exact hnot h
  show (F.subgroupOf E).index = p
  calc (F.subgroupOf E).index = Nat.card (E ⧸ F.subgroupOf E) := Subgroup.index_eq_card _
    _ = Nat.card (⊤ : Subgroup (E ⧸ F.subgroupOf E)) := Subgroup.card_top.symm
    _ = Nat.card (Subgroup.zpowers (QuotientGroup.mk (e i) : E ⧸ F.subgroupOf E)) := by
        rw [htop]
    _ = p := by rw [Nat.card_zpowers, hord]

theorem range_le_hyperClosure_cube_of_center (hinj : ∀ i, Function.Injective (ψ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) (hp : p.Prime)
    (hZ : ∀ x : L, x ^ p = 1 → (∀ A, Commute x A) → x = 1) (hg : orderOf g = p) (i : Fin 3) :
    (ψ i).range ≤ hyperClosure p ⊤ (cube ψ g) := by
  rintro _ ⟨A, rfl⟩
  refine Subgroup.subset_closure ⟨Subgroup.mem_top _,
    cube ψ g ⊓ Subgroup.centralizer ((ψ i).range : Set C), inf_le_left,
    relIndex_cube_inf_centralizer_of_center hinj hcomm hp hZ hg i, fun f hf => ?_⟩
  exact ((Subgroup.mem_centralizer_iff.1 hf.2) _ ⟨A, rfl⟩).symm

theorem plane_spec_of_center (hinj : ∀ i, Function.Injective (ψ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) (hp : p.Prime)
    (hZ : ∀ x : L, x ^ p = 1 → (∀ A, Commute x A) → x = 1) (hg : orderOf g = p) :
    IsElemAbelian p (plane ψ g) ∧ plane ψ g ≠ ⊥ := by
  obtain ⟨hE, -, -⟩ := cube_spec_of_center hinj hcomm hp hZ hg
  refine ⟨⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hE.2 x (plane_le_cube hx)⟩, ?_⟩
  · have := hE.1.is_comm.comm ⟨a, plane_le_cube a.2⟩ ⟨b, plane_le_cube b.2⟩
    exact congrArg (fun z : cube ψ g => (z : C)) this
  · intro h
    have h0 : ψ 0 g ∈ plane ψ g := Subgroup.subset_closure (by simp)
    rw [h, Subgroup.mem_bot] at h0
    have h1 : ψ 0 g = ψ 0 1 := by rw [h0, map_one]
    have hg1 : g = 1 := hinj 0 h1
    rw [hg1, orderOf_one] at hg
    exact hp.one_lt.ne' hg.symm

theorem hyperGen_of_hyperGen_of_le {Y : Type*} [Group Y] {E E₁ : Subgroup Y}
    (h₁ : HyperGen p ⊤ E₁)
    (h : ∀ B : Subgroup Y, B ≤ E₁ → B.relIndex E₁ = p → ∀ k : Y, (∀ f ∈ B, f * k = k * f) →
      k ∈ hyperClosure p ⊤ E) :
    HyperGen p ⊤ E := by
  intro x hx
  refine (Subgroup.closure_le _).2 ?_ (h₁ hx)
  rintro k ⟨-, B, hB, hBi, hc⟩
  exact h B hB hBi k hc

end Frame

section SL3Frame

variable {C : Type*} [Group C] {K : Type} [Field K]
  {ψ : Fin 3 → Matrix.SpecialLinearGroup (Fin 3) K →* C} {g : Matrix.SpecialLinearGroup (Fin 3) K}
  {p : ℕ}

theorem dvd_of_commute_range (hinj : ∀ i, Function.Injective (ψ i)) (hp : p.Prime) (hp3 : p ≠ 3)
    (hg : orderOf g = p) (i : Fin 3) (a : ℤ) (h : ∀ A, Commute (ψ i (g ^ a)) (ψ i A)) :
    (p : ℤ) ∣ a :=
  dvd_of_commute_range_of_center hinj (fun _ hx hc => eq_one_of_commute_sl3 hp hp3 hx hc) hg i a h

theorem cube_spec (hinj : ∀ i, Function.Injective (ψ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) (hp : p.Prime) (hp3 : p ≠ 3)
    (hg : orderOf g = p) :
    IsElemAbelian p (cube ψ g) ∧ Nat.card (cube ψ g) = p ^ 3 ∧
      ∀ x ∈ cube ψ g, ∃ i j k : ℤ, x = ψ 0 g ^ i * ψ 1 g ^ j * ψ 2 g ^ k :=
  cube_spec_of_center hinj hcomm hp (fun _ hx hc => eq_one_of_commute_sl3 hp hp3 hx hc) hg

theorem isElemAbelian_cube (hinj : ∀ i, Function.Injective (ψ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) (hp : p.Prime) (hp3 : p ≠ 3)
    (hg : orderOf g = p) : IsElemAbelian p (cube ψ g) :=
  (cube_spec hinj hcomm hp hp3 hg).1

theorem card_cube (hinj : ∀ i, Function.Injective (ψ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) (hp : p.Prime) (hp3 : p ≠ 3)
    (hg : orderOf g = p) : Nat.card (cube ψ g) = p ^ 3 :=
  (cube_spec hinj hcomm hp hp3 hg).2.1

theorem relIndex_cube_inf_centralizer (hinj : ∀ i, Function.Injective (ψ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) (hp : p.Prime) (hp3 : p ≠ 3)
    (hg : orderOf g = p) (i : Fin 3) :
    (cube ψ g ⊓ Subgroup.centralizer ((ψ i).range : Set C)).relIndex (cube ψ g) = p :=
  relIndex_cube_inf_centralizer_of_center hinj hcomm hp
    (fun _ hx hc => eq_one_of_commute_sl3 hp hp3 hx hc) hg i

theorem range_le_hyperClosure_cube (hinj : ∀ i, Function.Injective (ψ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) (hp : p.Prime) (hp3 : p ≠ 3)
    (hg : orderOf g = p) (i : Fin 3) :
    (ψ i).range ≤ hyperClosure p ⊤ (cube ψ g) :=
  range_le_hyperClosure_cube_of_center hinj hcomm hp
    (fun _ hx hc => eq_one_of_commute_sl3 hp hp3 hx hc) hg i

theorem plane_spec (hinj : ∀ i, Function.Injective (ψ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) (hp : p.Prime) (hp3 : p ≠ 3)
    (hg : orderOf g = p) :
    IsElemAbelian p (plane ψ g) ∧ plane ψ g ≠ ⊥ :=
  plane_spec_of_center hinj hcomm hp (fun _ hx hc => eq_one_of_commute_sl3 hp hp3 hx hc) hg

end SL3Frame

end CFSG.HardMathSupport.Foote.Coordinator.AnisoCube
