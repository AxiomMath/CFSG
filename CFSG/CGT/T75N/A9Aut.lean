module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.CGT.T75N

open Equiv Equiv.Perm

section Count

variable {N : Type} [Group N]

@[expose] def fixSub (u : MulAut N) : Subgroup N where
  carrier := {x | u x = x}
  one_mem' := map_one u
  mul_mem' := by
    intro a b ha hb
    change u (a * b) = a * b
    rw [map_mul, show u a = a from ha, show u b = b from hb]
  inv_mem' := by
    intro a ha
    change u a⁻¹ = a⁻¹
    rw [map_inv, show u a = a from ha]

variable [Finite N]

theorem card_modEq_inf_fixSub {p n : ℕ} [Fact p.Prime] (σ : MulAut N) (hσ : σ ^ p ^ n = 1)
    (S : Subgroup N) (hS : ∀ x, x ∈ S ↔ σ x ∈ S) :
    Nat.card S ≡ Nat.card ↥(S ⊓ fixSub σ) [MOD p] := by
  classical
  have : Fintype N := Fintype.ofFinite N
  let τ : Perm ↥S := (MulAut.toPerm N σ).subtypePerm (fun x => (hS x).symm)
  have hτ : τ ^ p ^ n = 1 := by
    have h1 : τ ^ p ^ n = ((MulAut.toPerm N σ) ^ p ^ n).subtypePerm (fun x => by
        rw [← map_pow]; simp only [hσ, map_one, Perm.coe_one]; exact Iff.rfl) :=
      Perm.subtypePerm_pow _ _ _
    rw [h1]
    ext x
    simp [← map_pow, hσ]
  have hmod := Perm.card_compl_support_modEq hτ
  have hfix : ∀ y : ↥S, y ∈ τ.supportᶜ ↔ σ y.1 = y.1 := by
    intro y
    rw [Finset.mem_compl, Perm.mem_support, not_not]
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  have hcard : (τ.supportᶜ).card = Nat.card ↥(S ⊓ fixSub σ) := by
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, (hfix x.1).1 x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, (hfix _).2 y.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [hcard, ← Nat.card_eq_fintype_card] at hmod
  exact hmod.symm

end Count

section Norm

variable {N : Type} [CommGroup N]

@[expose] def nrm (u : MulAut N) : N →* N where
  toFun x := x * u x * (u ^ 2) x * (u ^ 3) x * (u ^ 4) x
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul]
    ac_rfl

theorem nrm_apply (u : MulAut N) (x : N) :
    nrm u x = x * u x * (u ^ 2) x * (u ^ 3) x * (u ^ 4) x := rfl

theorem apply_comm_of_comm {w u : MulAut N} (h : w * u = u * w) (k : ℕ) (y : N) :
    w ((u ^ k) y) = (u ^ k) (w y) := by
  have h1 : w * u ^ k = u ^ k * w := (Commute.pow_right (show Commute w u from h) k).eq
  have := congrArg (fun m : MulAut N => m y) h1
  simpa using this

theorem nrm_comm {w u : MulAut N} (h : w * u = u * w) (x : N) :
    nrm u (w x) = w (nrm u x) := by
  have h1 : ∀ y, w (u y) = u (w y) := fun y => by
    simpa using apply_comm_of_comm h 1 y
  have h2 : ∀ y, w ((u ^ 2) y) = (u ^ 2) (w y) := fun y => apply_comm_of_comm h 2 y
  have h3 : ∀ y, w ((u ^ 3) y) = (u ^ 3) (w y) := fun y => apply_comm_of_comm h 3 y
  have h4 : ∀ y, w ((u ^ 4) y) = (u ^ 4) (w y) := fun y => apply_comm_of_comm h 4 y
  simp only [nrm_apply, map_mul, h1, h2, h3, h4]

theorem nrm_self {u : MulAut N} (hu5 : u ^ 5 = 1) (x : N) : nrm u (u x) = nrm u x := by
  have e2 : u (u x) = (u ^ 2) x := by rw [pow_two, MulAut.mul_apply]
  have e3 : (u ^ 2) (u x) = (u ^ 3) x := by rw [← MulAut.mul_apply, ← pow_succ]
  have e4 : (u ^ 3) (u x) = (u ^ 4) x := by rw [← MulAut.mul_apply, ← pow_succ]
  have e5 : (u ^ 4) (u x) = x := by
    rw [← MulAut.mul_apply, ← pow_succ, hu5]; rfl
  simp only [nrm_apply, e2, e3, e4, e5]
  ac_rfl

theorem nrm_of_mem_fixSub {u : MulAut N} (h2 : ∀ a : N, a * a = 1) {x : N}
    (hx : x ∈ fixSub u) : nrm u x = x := by
  have h : ∀ k : ℕ, (u ^ k) x = x := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, MulAut.mul_apply, show u x = x from hx, ih]
  simp only [nrm_apply, h, show u x = x from hx]
  calc x * x * x * x * x = (x * x) * (x * x) * x := by ac_rfl
    _ = x := by simp [h2]

theorem nrm_mem_fixSub {u : MulAut N} (hu5 : u ^ 5 = 1) (x : N) : nrm u x ∈ fixSub u := by
  show u (nrm u x) = nrm u x
  rw [← nrm_comm (show u * u = u * u from rfl), nrm_self hu5]

@[expose] def Usub (u : MulAut N) : Subgroup N := (nrm u).ker

theorem mem_Usub {u : MulAut N} {x : N} : x ∈ Usub u ↔ nrm u x = 1 := Iff.rfl

theorem range_nrm {u : MulAut N} (hu5 : u ^ 5 = 1) (h2 : ∀ a : N, a * a = 1) :
    (nrm u).range = fixSub u := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact nrm_mem_fixSub hu5 x
  · intro hy
    exact ⟨y, nrm_of_mem_fixSub h2 hy⟩

theorem fixSub_inf_Usub {u : MulAut N} (h2 : ∀ a : N, a * a = 1) :
    fixSub u ⊓ Usub u = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  rw [Subgroup.mem_bot, ← nrm_of_mem_fixSub h2 hx1]
  exact hx2

theorem card_Usub_mul_card_fixSub {u : MulAut N} (hu5 : u ^ 5 = 1) (h2 : ∀ a : N, a * a = 1) :
    Nat.card (Usub u) * Nat.card (fixSub u) = Nat.card N := by
  rw [← range_nrm hu5 h2]
  exact Subgroup.card_ker_mul_card_range (nrm u)

theorem decomp {u : MulAut N} (hu5 : u ^ 5 = 1) (h2 : ∀ a : N, a * a = 1) (n : N) :
    ∃ f ∈ fixSub u, ∃ g ∈ Usub u, n = f * g := by
  refine ⟨nrm u n, nrm_mem_fixSub hu5 n, n * (nrm u n)⁻¹, ?_,
    by rw [mul_left_comm, mul_inv_cancel, mul_one]⟩
  rw [mem_Usub, map_mul, map_inv, nrm_of_mem_fixSub h2 (nrm_mem_fixSub hu5 n), mul_inv_cancel]

theorem mem_Usub_iff_self {u : MulAut N} (hu5 : u ^ 5 = 1) (x : N) :
    x ∈ Usub u ↔ u x ∈ Usub u := by
  rw [mem_Usub, mem_Usub, nrm_self hu5]

theorem mem_Usub_iff_comm {w u : MulAut N} (h : w * u = u * w) (x : N) :
    x ∈ Usub u ↔ w x ∈ Usub u := by
  rw [mem_Usub, mem_Usub, nrm_comm h]
  constructor
  · intro hx; rw [hx, map_one]
  · intro hx; exact (MulEquiv.map_eq_one_iff w).1 hx

end Norm

section Numeric

variable {N : Type} [CommGroup N] [Finite N]

theorem card_fixSub_Usub {u : MulAut N} (hu : u ≠ 1) (hu5 : u ^ 5 = 1)
    (h2 : ∀ a : N, a * a = 1) {d : ℕ} (hN : Nat.card N = 2 ^ d) (hd : d ≤ 6) :
    ∃ f, Nat.card (fixSub u) = 2 ^ f ∧ f + 4 = d ∧ Nat.card (Usub u) = 16 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨f, hfd, hf⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (hN ▸ Subgroup.card_subgroup_dvd_card (fixSub u))
  have hmod := card_modEq_inf_fixSub (p := 5) (n := 1) u (by simpa using hu5) ⊤ (by simp)
  rw [Subgroup.card_top, top_inf_eq, hf, hN] at hmod
  have hlt : f < d := by
    rcases lt_or_eq_of_le hfd with h | h
    · exact h
    · exfalso
      apply hu
      have htop : fixSub u = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hf, hN, h])
      ext x
      have : x ∈ fixSub u := htop ▸ Subgroup.mem_top x
      exact this
  have hf4 : f + 4 = d := by
    interval_cases d <;> interval_cases f <;> simp_all [Nat.ModEq]
  refine ⟨f, hf, hf4, ?_⟩
  have hprod := card_Usub_mul_card_fixSub hu5 h2
  rw [hf, hN, ← hf4, pow_add] at hprod
  have h16 : Nat.card (Usub u) * 2 ^ f = 16 * 2 ^ f := by rw [hprod]; ring
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h16

theorem card_modEq_one {u : MulAut N} (hu5 : u ^ 5 = 1) (h2 : ∀ a : N, a * a = 1)
    (S : Subgroup N) (hSU : S ≤ Usub u) (hS : ∀ x, x ∈ S ↔ u x ∈ S) :
    Nat.card S ≡ 1 [MOD 5] := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmod := card_modEq_inf_fixSub (p := 5) (n := 1) u (by simpa using hu5) S hS
  have hbot : S ⊓ fixSub u = ⊥ := by
    rw [eq_bot_iff, ← fixSub_inf_Usub (u := u) h2]
    exact fun x hx => ⟨hx.2, hSU hx.1⟩
  rw [hbot, Subgroup.card_bot] at hmod
  exact hmod

theorem trivial_on_Usub {u w : MulAut N} (hu : u ≠ 1) (hu5 : u ^ 5 = 1)
    (h2 : ∀ a : N, a * a = 1) {d : ℕ} (hN : Nat.card N = 2 ^ d) (hd : d ≤ 6)
    (hcom : w * u = u * w) {k : ℕ} (hw : w ^ 2 ^ k = 1) : ∀ x ∈ Usub u, w x = x := by
  obtain ⟨f, -, -, hUc⟩ := card_fixSub_Usub hu hu5 h2 hN hd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod2 := card_modEq_inf_fixSub (p := 2) (n := k) w hw (Usub u) (mem_Usub_iff_comm hcom)
  have hMinv : ∀ x, x ∈ Usub u ⊓ fixSub w ↔ u x ∈ Usub u ⊓ fixSub w := by
    intro x
    have hwu : w (u x) = u (w x) := by
      simpa using congrArg (fun m : MulAut N => m x) hcom
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨(mem_Usub_iff_self hu5 x).1 hx1, ?_⟩
      show w (u x) = u x
      rw [hwu, show w x = x from hx2]
    · rintro ⟨hx1, hx2⟩
      refine ⟨(mem_Usub_iff_self hu5 x).2 hx1, ?_⟩
      have h3 : w (u x) = u x := hx2
      rw [hwu] at h3
      exact u.injective (h3.trans (by rfl))
  have hmod5 := card_modEq_one hu5 h2 (Usub u ⊓ fixSub w) inf_le_left hMinv
  have hdvd : Nat.card ↥(Usub u ⊓ fixSub w) ∣ 2 ^ 4 :=
    (show (16 : ℕ) = 2 ^ 4 by norm_num) ▸ hUc ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, hi, hMi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hUc, hMi] at hmod2
  rw [hMi] at hmod5
  have hi4 : i = 4 := by
    interval_cases i <;> first | rfl | (exfalso; revert hmod2 hmod5; decide)
  have hMU : Usub u ⊓ fixSub w = Usub u :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hUc, hMi, hi4]; norm_num)
  intro x hx
  have : x ∈ Usub u ⊓ fixSub w := by rw [hMU]; exact hx
  exact this.2

theorem pow_five_eq_one {u : MulAut N} (h2 : ∀ a : N, a * a = 1) {d : ℕ}
    (hN : Nat.card N = 2 ^ d) (hd : d ≤ 6) {k : ℕ} (hk : u ^ 5 ^ k = 1) : u ^ 5 = 1 := by
  have hpow : ∀ a : N, a ^ 2 = 1 := fun a => by rw [pow_two]; exact h2 a
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (fun a b => mul_comm a b) hpow hN
  have hcard : Nat.card (MulAut N) = ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) := by
    rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  have h25 : ¬ 25 ∣ Nat.card (MulAut N) := by
    rw [hcard]
    interval_cases d <;> simp [Fin.prod_univ_succ]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1
    (orderOf_dvd_of_pow_eq_one hk)
  have hj1 : j ≤ 1 := by
    by_contra hlt
    push Not at hlt
    apply h25
    calc 25 = 5 ^ 2 := by norm_num
      _ ∣ 5 ^ j := pow_dvd_pow 5 hlt
      _ = orderOf u := hj.symm
      _ ∣ Nat.card (MulAut N) := orderOf_dvd_natCard u
  rw [← orderOf_dvd_iff_pow_eq_one, hj]
  calc 5 ^ j ∣ 5 ^ 1 := pow_dvd_pow 5 hj1
    _ = 5 := by norm_num

theorem card_dvd_six {u : MulAut N} (hu : u ≠ 1) (hu5 : u ^ 5 = 1) (h2 : ∀ a : N, a * a = 1)
    {d : ℕ} (hN : Nat.card N = 2 ^ d) (hd : d ≤ 6) {Sg : Subgroup (MulAut N)}
    (hSg : IsPGroup 2 Sg) (hcom : ∀ w ∈ Sg, w * u = u * w) : Nat.card Sg ∣ 6 := by
  obtain ⟨f, hfc, hf4, hUc⟩ := card_fixSub_Usub hu hu5 h2 hN hd
  have htriv : ∀ w ∈ Sg, ∀ x ∈ Usub u, w x = x := by
    intro w hw x hx
    obtain ⟨k, hk⟩ := hSg ⟨w, hw⟩
    have hk' : w ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    exact trivial_on_Usub hu hu5 h2 hN hd (hcom w hw) hk' x hx
  have hF : ∀ w ∈ Sg, ∀ x : N, x ∈ fixSub u → w x ∈ fixSub u := by
    intro w hw x hx
    show u (w x) = w x
    have hwu : w (u x) = u (w x) := by
      simpa using congrArg (fun m : MulAut N => m x) (hcom w hw)
    rw [← hwu, show u x = x from hx]
  let X := {y : ↥(fixSub u) // y ≠ 1}
  let _ : MulAction Sg X :=
    { smul := fun w y => ⟨⟨w.1 y.1.1, hF w.1 w.2 y.1.1 y.1.2⟩, fun h => y.2 (by
        apply Subtype.ext
        have h' := congrArg Subtype.val h
        exact (MulEquiv.map_eq_one_iff w.1).1 h')⟩
      one_smul := fun y => rfl
      mul_smul := fun a b y => rfl }
  have hinj : Function.Injective (MulAction.toPermHom Sg X) := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have hfix : ∀ y : X, w • y = y := fun y => by
      simpa using congrArg (fun σ : Perm X => σ y) hw
    apply Subtype.ext
    ext n
    obtain ⟨f₀, hf₀, g₀, hg₀, rfl⟩ := decomp hu5 h2 n
    rw [map_mul, htriv w.1 w.2 g₀ hg₀]
    by_cases h1 : f₀ = 1
    · rw [h1]; simp
    · have h3 : w.1 f₀ = f₀ := congrArg (fun y : X => y.1.1)
        (hfix ⟨⟨f₀, hf₀⟩, fun h => h1 (congrArg Subtype.val h)⟩)
      rw [h3]
      rfl
  have hdvd := Subgroup.card_dvd_of_injective _ hinj
  rw [Nat.card_perm] at hdvd
  have hX : Nat.card X ≤ 3 := by
    have : Fintype (fixSub u) := Fintype.ofFinite _
    have : Fintype X := Fintype.ofFinite _
    have hlt : Fintype.card X < Fintype.card (fixSub u) :=
      Fintype.card_subtype_lt (x := (1 : fixSub u)) (by simp)
    have hfc' : Fintype.card (fixSub u) = 2 ^ f := by
      rw [← Nat.card_eq_fintype_card]; exact hfc
    rw [Nat.card_eq_fintype_card (α := X)]
    have hf2 : f ≤ 2 := by omega
    have : 2 ^ f ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hf2
    omega
  refine hdvd.trans ?_
  interval_cases (Nat.card X) <;> decide

end Numeric

section Wrap

variable {N : Type} [Group N] [Finite N]

theorem pow_five_eq_one' (hc : ∀ a b : N, a * b = b * a) {u : MulAut N}
    (h2 : ∀ a : N, a * a = 1) {d : ℕ} (hN : Nat.card N = 2 ^ d) (hd : d ≤ 6) {k : ℕ}
    (hk : u ^ 5 ^ k = 1) : u ^ 5 = 1 := by
  let _ : CommGroup N := { (inferInstance : Group N) with mul_comm := hc }
  exact pow_five_eq_one h2 hN hd hk

theorem card_dvd_six' (hc : ∀ a b : N, a * b = b * a) {u : MulAut N} (hu : u ≠ 1)
    (hu5 : u ^ 5 = 1) (h2 : ∀ a : N, a * a = 1) {d : ℕ} (hN : Nat.card N = 2 ^ d) (hd : d ≤ 6)
    {Sg : Subgroup (MulAut N)} (hSg : IsPGroup 2 Sg) (hcom : ∀ w ∈ Sg, w * u = u * w) :
    Nat.card Sg ∣ 6 := by
  let _ : CommGroup N := { (inferInstance : Group N) with mul_comm := hc }
  exact card_dvd_six hu hu5 h2 hN hd hSg hcom

end Wrap

end CFSG.CGT.T75N
