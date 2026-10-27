module

public import CFSG.CGT.Stroth77.Stroth2Mho

public section

namespace CFSG.CGT.Stroth77

open CFSG.GroupTheory.HuppertProduct

variable {G : Type} [Group G] [Finite G] {X : StrothAmbient G}

theorem card_four_torsion_zmod_two_pow (n : ℕ) (hn : 2 ≤ n) :
    Nat.card {z : ZMod (2 ^ n) // (4 : ℤ) • z = 0} = 4 := by
  have hN : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show 4 = 2 ^ 2 by norm_num, ← pow_add, show 2 + (n - 2) = n by omega]
  have hpos : 0 < 2 ^ (n - 2) := pow_pos (by norm_num) _
  have hmul4 : ∀ z : ZMod (2 ^ n), (4 : ℤ) • z = 0 → 2 ^ (n - 2) ∣ z.val := by
    intro z hz
    have hz' : ((4 * z.val : ℕ) : ZMod (2 ^ n)) = 0 := by
      rw [zsmul_eq_mul] at hz
      simpa [Nat.cast_mul, ZMod.natCast_zmod_val, Int.cast_ofNat] using hz
    have hdiv : 2 ^ n ∣ 4 * z.val := (ZMod.natCast_eq_zero_iff _ _).mp hz'
    have h4dvd : 4 * 2 ^ (n - 2) ∣ 4 * z.val := by
      rw [← hN]
      exact hdiv
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 4)).mp h4dvd
  let e : {z : ZMod (2 ^ n) // (4 : ℤ) • z = 0} ≃ Fin 4 :=
    { toFun := fun z =>
        ⟨z.1.val / 2 ^ (n - 2), by
          have hMdiv := hmul4 z.1 z.2
          have hlt : 2 ^ (n - 2) * (z.1.val / 2 ^ (n - 2)) < 2 ^ (n - 2) * 4 := by
            rw [Nat.mul_div_cancel' hMdiv, mul_comm (2 ^ (n - 2)) 4, ← hN]
            exact ZMod.val_lt z.1
          exact Nat.lt_of_mul_lt_mul_left hlt⟩
      invFun := fun t =>
        ⟨((2 ^ (n - 2) * t.val : ℕ) : ZMod (2 ^ n)), by
          have h4 : ((4 * (2 ^ (n - 2) * t.val) : ℕ) : ZMod (2 ^ n)) = 0 := by
            rw [ZMod.natCast_eq_zero_iff, hN]
            exact ⟨t.val, by ring⟩
          rw [zsmul_eq_mul]
          simpa [Nat.cast_mul, Int.cast_ofNat] using h4⟩
      left_inv := fun z => by
        apply Subtype.ext
        apply ZMod.val_injective (2 ^ n)
        rw [← ZMod.natCast_zmod_val z.1]
        rw [ZMod.val_cast_of_lt (by
          rw [Nat.mul_div_cancel' (hmul4 z.1 z.2)]
          exact ZMod.val_lt z.1), ZMod.val_cast_of_lt (ZMod.val_lt z.1)]
        exact Nat.mul_div_cancel' (hmul4 z.1 z.2)
      right_inv := fun t => by
        apply Fin.ext
        change ((2 ^ (n - 2) * t.val : ℕ) : ZMod (2 ^ n)).val / 2 ^ (n - 2) = t.val
        have hlt : 2 ^ (n - 2) * t.val < 2 ^ n := by
          have h := Nat.mul_lt_mul_of_pos_left t.isLt hpos
          rwa [mul_comm (2 ^ (n - 2)) 4, ← hN] at h
        rw [ZMod.val_cast_of_lt hlt]
        exact Nat.mul_div_cancel_left t.val hpos }
  simpa using Nat.card_congr e

theorem card_omegaIn_two_of_two_le_k (Z : StrothDatum X) (hk : ∀ i, 2 ≤ Z.τ.k i) :
    Nat.card (omegaIn 2 Z.D) = 64 := by
  rw [card_omegaIn_two_eq Z.dataD.e, card_four_torsion_torus, Fin.prod_univ_three,
    card_four_torsion_zmod_two_pow (Z.τ.k 0) (hk 0),
    card_four_torsion_zmod_two_pow (Z.τ.k 1) (hk 1),
    card_four_torsion_zmod_two_pow (Z.τ.k 2) (hk 2)]
  norm_num

theorem A_index_two_omegaIn_two (Z : StrothDatum X) (hk : ∀ i, 2 ≤ Z.τ.k i) :
    (X.A.subgroupOf (omegaIn 2 Z.D)).index = 2 := by
  have hcardΩ : Nat.card (omegaIn 2 Z.D) = 64 := card_omegaIn_two_of_two_le_k Z hk
  have hcardA : Nat.card (X.A.subgroupOf (omegaIn 2 Z.D)) = 32 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (A_le_omegaIn_two Z)).toEquiv).trans
      X.card_A
  rw [Subgroup.index_eq_card_div, hcardA, hcardΩ]

theorem torus_exists_two_zsmul_eq_of_two_zsmul_eq_zero {k : Fin 3 → ℕ}
    (hk : ∀ i, 2 ≤ k i) {v : Torus k} (hv : (2 : ℤ) • v = 0) :
    ∃ w : Torus k, (2 : ℤ) • w = v := by
  obtain ⟨V, hV⟩ : ∃ V : Fin 3 → ℤ, v = Torus.ofInt k V := by
    choose V hV using fun i => ZMod.intCast_surjective (v i)
    exact ⟨V, funext fun i => by simpa [Torus.ofInt_apply] using (hV i).symm⟩
  have hEven : ∀ i, Even (V i) := by
    intro i
    have hdiv : ((2 ^ k i : ℕ) : ℤ) ∣ 2 * V i := by
      have hi : ((2 * V i : ℤ) : ZMod (2 ^ k i)) = 0 := by
        have h := congrFun (hV ▸ hv) i
        simpa only [Torus.ofInt_apply, Pi.smul_apply, Pi.zero_apply, zsmul_eq_mul,
          Int.cast_ofNat, Int.cast_mul, Int.cast_natCast] using h
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * V i) (2 ^ k i)).mp hi
    have h4 : (4 : ℤ) ∣ ((2 ^ k i : ℕ) : ℤ) := by
      have h := pow_dvd_pow (2 : ℕ) (hk i)
      exact_mod_cast h
    obtain ⟨t, ht⟩ := h4.trans hdiv
    exact even_iff_two_dvd.mpr ⟨t, by omega⟩
  obtain ⟨w, hw⟩ := (Torus.exists_two_zsmul_eq_iff
    (fun i => le_trans (by norm_num : 1 ≤ 2) (hk i)) V).mpr hEven
  exact ⟨w, by rw [hV]; exact hw⟩

theorem exists_sq_eq_of_mem_omegaIn_one (Z : StrothDatum X) (hk : ∀ i, 2 ≤ Z.τ.k i)
    {y : G} (hy : y ∈ omegaIn 1 Z.D) :
    ∃ x : G, x ∈ omegaIn 2 Z.D ∧ x * x = y := by
  have hcomm : ∀ a ∈ Z.D, ∀ b ∈ Z.D, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val
      (Z.dataD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hyD, hy2⟩ := (mem_omegaIn_iff_of_comm hcomm).mp hy
  have hy2' : y ^ 2 = 1 := by simpa using hy2
  set v : Torus Z.τ.k := Z.dataD.e (Additive.ofMul ⟨y, hyD⟩) with hv
  have hv2 : (2 : ℤ) • v = 0 := by
    calc (2 : ℤ) • v
        = Z.dataD.e ((2 : ℤ) • Additive.ofMul (⟨y, hyD⟩ : Z.D)) := by
          rw [hv, map_zsmul]
      _ = Z.dataD.e (Additive.ofMul ((⟨y, hyD⟩ : Z.D) ^ 2)) := by
          rw [ofMul_pow]
          norm_num
      _ = Z.dataD.e (Additive.ofMul (1 : Z.D)) := by
          rw [show (⟨y, hyD⟩ : Z.D) ^ 2 = 1 from Subtype.ext hy2']
      _ = 0 := by simp
  obtain ⟨w, hw⟩ := torus_exists_two_zsmul_eq_of_two_zsmul_eq_zero hk hv2
  set x : Z.D := Additive.toMul (Z.dataD.e.symm w) with hx
  have hxw : Additive.ofMul x = Z.dataD.e.symm w := by
    rw [hx]
    simp
  have hx2' : x * x = ⟨y, hyD⟩ := by
    apply Additive.ofMul.injective
    apply Z.dataD.e.injective
    have h1 : Z.dataD.e (Additive.ofMul (x * x)) = w + w := by
      rw [ofMul_mul, map_add, hxw]
      simp
    rw [h1]
    show w + w = v
    rw [← hw, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, natCast_zsmul, two_nsmul]
  have hx2 : (x : G) * (x : G) = y := by
    simpa using congrArg Subtype.val hx2'
  have hy2D : (⟨y, hyD⟩ : Z.D) ^ 2 = 1 := Subtype.ext hy2'
  have hx4D : (x : Z.D) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_two x, hx2', hy2D]
  have hx4 : (x : G) ^ 4 = 1 := by
    simpa using congrArg Subtype.val hx4D
  refine ⟨(x : G), ?_, hx2⟩
  exact mem_omegaIn_of_pow_eq_one (i := 2) x.2 (by simpa using hx4)

theorem sq_mem_omegaIn_one_of_mem_omegaIn_two (Z : StrothDatum X) {x : G}
    (hx : x ∈ omegaIn 2 Z.D) : x * x ∈ omegaIn 1 Z.D := by
  have hcomm : ∀ a ∈ Z.D, ∀ b ∈ Z.D, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val
      (Z.dataD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hxD, hx4⟩ := (mem_omegaIn_iff_of_comm hcomm).mp hx
  have hx4' : x ^ 4 = 1 := by simpa using hx4
  refine mem_omegaIn_of_pow_eq_one (i := 1) (Z.D.mul_mem hxD hxD) ?_
  rw [show 2 ^ 1 = 2 by norm_num, ← sq x, ← pow_mul]
  exact hx4'

theorem omegaIn_one_eq_set_of_sq (Z : StrothDatum X) (hk : ∀ i, 2 ≤ Z.τ.k i) :
    (omegaIn 1 Z.D : Set G) = {y | ∃ x ∈ omegaIn 2 Z.D, x * x = y} := by
  ext y
  constructor
  · intro hy
    exact exists_sq_eq_of_mem_omegaIn_one Z hk hy
  · rintro ⟨x, hx, rfl⟩
    exact sq_mem_omegaIn_one_of_mem_omegaIn_two Z hx

theorem omegaIn_one_le_of_index_two (Z : StrothDatum X) (hk : ∀ i, 2 ≤ Z.τ.k i)
    (h2 : (X.A.subgroupOf (omegaIn 2 Z.D)).index = 2) :
    omegaIn 1 Z.D ≤ X.A := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := exists_sq_eq_of_mem_omegaIn_one Z hk hy
  subst hxy
  have hmem : (⟨x, hx⟩ : omegaIn 2 Z.D) * ⟨x, hx⟩ ∈
      X.A.subgroupOf (omegaIn 2 Z.D) :=
    Subgroup.mul_self_mem_of_index_two h2 ⟨x, hx⟩
  exact Subgroup.mem_subgroupOf.mp hmem

theorem omegaIn_one_le_A (Z : StrothDatum X) (hk : ∀ i, 2 ≤ Z.τ.k i) :
    omegaIn 1 Z.D ≤ X.A :=
  omegaIn_one_le_of_index_two Z hk (A_index_two_omegaIn_two Z hk)

theorem two_zsmul_intCast_zmod_two_pow_eq_zero_iff {n : ℕ} (hn : 1 ≤ n) (a : ℤ) :
    (2 : ℤ) • ((a : ℤ) : ZMod (2 ^ n)) = 0 ↔ (2 : ℤ) ^ (n - 1) ∣ a := by
  have h1 : (2 : ℤ) • ((a : ℤ) : ZMod (2 ^ n)) = ((2 * a : ℤ) : ZMod (2 ^ n)) := by
    rw [zsmul_eq_mul]
    push_cast
    ring
  rw [h1, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hpow : ((2 ^ n : ℕ) : ℤ) = 2 * (2 : ℤ) ^ (n - 1) := by
    calc ((2 ^ n : ℕ) : ℤ) = ((2 ^ ((n - 1) + 1) : ℕ) : ℤ) := by
          rw [Nat.sub_add_cancel hn]
      _ = 2 * (2 : ℤ) ^ (n - 1) := by
          rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ']
  rw [hpow]
  exact mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)


theorem mem_mho_iff_exists_pow_of_comm {S : Subgroup G}
    (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {n : ℕ} {x : G} :
    x ∈ mho S n ↔ ∃ d ∈ S, d ^ n = x := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => simpa [eq_comm] using hy
    | one => exact ⟨1, S.one_mem, one_pow n⟩
    | mul a b _ _ ha hb =>
        obtain ⟨da, hda, rfl⟩ := ha
        obtain ⟨db, hdb, rfl⟩ := hb
        have hc : Commute da db := hcomm da hda db hdb
        exact ⟨da * db, S.mul_mem hda hdb, by rw [hc.mul_pow n]⟩
    | inv a _ ha =>
        obtain ⟨da, hda, rfl⟩ := ha
        exact ⟨da⁻¹, S.inv_mem hda, by rw [inv_pow]⟩
  · rintro ⟨d, hd, rfl⟩
    exact pow_mem_mho hd

theorem torus_exists_zsmul_eq_iff_ofInt_dvd {k : Fin 3 → ℕ} (c : ℤ) (v : Torus k) :
    (∃ u : Torus k, c • u = v) ↔
      ∃ W : Fin 3 → ℤ, v = Torus.ofInt k W ∧ ∀ i, c ∣ W i := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨U, hU⟩ := Torus.exists_ofInt u
    refine ⟨fun i => c * U i, ?_, fun i => ⟨U i, rfl⟩⟩
    rw [← hu, ← hU, ← Torus.ofInt_zsmul]
    rfl
  · rintro ⟨W, rfl, hWdiv⟩
    choose U hU using hWdiv
    refine ⟨Torus.ofInt k U, ?_⟩
    rw [← Torus.ofInt_zsmul]
    congr 1
    funext i
    show c * U i = W i
    rw [hU i]

theorem mho_two_pow_pred_eq_set (Z : StrothDatum X) (m : ℕ) :
    (mho Z.D (2 ^ (m - 1)) : Set G) =
      {x | ∃ (hx : x ∈ Z.D) (W : Fin 3 → ℤ),
        Z.dataD.e (Additive.ofMul ⟨x, hx⟩) = Torus.ofInt Z.τ.k W ∧
        ∀ i, ((2 : ℕ) ^ (m - 1) : ℤ) ∣ W i} := by
  have hcomm : ∀ a ∈ Z.D, ∀ b ∈ Z.D, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val
      (Z.dataD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  ext x
  constructor
  · intro hx
    obtain ⟨d, hd, rfl⟩ := (mem_mho_iff_exists_pow_of_comm hcomm).mp hx
    obtain ⟨U, hU⟩ := Torus.exists_ofInt (Z.dataD.e (Additive.ofMul ⟨d, hd⟩))
    refine ⟨Z.D.pow_mem hd _, fun i => ((2 : ℕ) ^ (m - 1) : ℤ) * U i, ?_,
      fun i => ⟨U i, rfl⟩⟩
    change Z.dataD.e (Additive.ofMul ((⟨d, hd⟩ : Z.D) ^ (2 ^ (m - 1)))) =
      Torus.ofInt Z.τ.k (fun i => ((2 : ℕ) ^ (m - 1) : ℤ) * U i)
    rw [ofMul_pow, map_nsmul, ← hU, ← natCast_zsmul, ← Torus.ofInt_zsmul]
    rfl
  · rintro ⟨hx, W, hWv, hWdiv⟩
    have himage : ∃ u : Torus Z.τ.k,
        ((2 : ℕ) ^ (m - 1) : ℤ) • u = Z.dataD.e (Additive.ofMul ⟨x, hx⟩) :=
      (torus_exists_zsmul_eq_iff_ofInt_dvd _ _).mpr ⟨W, hWv, hWdiv⟩
    obtain ⟨u, hu⟩ := himage
    set d : Z.D := Additive.toMul (Z.dataD.e.symm u) with hd
    have hdpow : d ^ (2 ^ (m - 1)) = ⟨x, hx⟩ := by
      apply Additive.ofMul.injective
      apply Z.dataD.e.injective
      calc Z.dataD.e (Additive.ofMul (d ^ 2 ^ (m - 1)))
          = Z.dataD.e ((2 ^ (m - 1) : ℕ) • Additive.ofMul d) := by
            rw [ofMul_pow]
        _ = (2 ^ (m - 1) : ℕ) • Z.dataD.e (Additive.ofMul d) := by
            rw [map_nsmul]
        _ = (2 ^ (m - 1) : ℕ) • u := by
            rw [show Additive.ofMul d = Z.dataD.e.symm u by rw [hd]; simp,
              AddEquiv.apply_symm_apply]
        _ = Z.dataD.e (Additive.ofMul ⟨x, hx⟩) := by
            rw [← natCast_zsmul]
            exact hu
    refine (mem_mho_iff_exists_pow_of_comm hcomm).mpr ⟨(d : G), d.2, ?_⟩
    simpa using congrArg Subtype.val hdpow

theorem mho_two_pow_pred_eq_set_c_coordinate (Z : StrothDatum X) (hm : 1 ≤ Z.τ.m) :
    (mho Z.D (2 ^ (Z.τ.m - 1)) : Set G) =
      {x | ∃ (hx : x ∈ Z.D) (W : Fin 3 → ℤ),
        Z.dataD.e (Additive.ofMul ⟨x, hx⟩) = Torus.ofInt Z.τ.k W ∧
        (2 : ℤ) • ((W 0 : ℤ) : ZMod (2 ^ Z.τ.m)) = 0 ∧
        ((2 : ℕ) ^ (Z.τ.m - 1) : ℤ) ∣ W 1 ∧
        ((2 : ℕ) ^ (Z.τ.m - 1) : ℤ) ∣ W 2} := by
  rw [mho_two_pow_pred_eq_set Z (Z.τ.m)]
  ext x
  constructor
  · rintro ⟨hx, W, hWv, hW⟩
    refine ⟨hx, W, hWv, ?_, ?_, ?_⟩
    · rw [two_zsmul_intCast_zmod_two_pow_eq_zero_iff (n := Z.τ.m) (a := W 0) hm]
      simpa [Nat.cast_pow] using hW 0
    · exact hW 1
    · exact hW 2
  · rintro ⟨hx, W, hWv, hW0, hW1, hW2⟩
    refine ⟨hx, W, hWv, ?_⟩
    intro i
    fin_cases i
    · refine (two_zsmul_intCast_zmod_two_pow_eq_zero_iff
        (n := Z.τ.m) (a := W 0) hm).mp ?_
      simpa [Nat.cast_pow] using hW0
    · exact hW1
    · exact hW2

namespace StrothWeakTypeData

variable {S : Type*} [Group S] {B : Subgroup S} {τ : StrothTypeIndex}

theorem e_c (D : StrothWeakTypeData B τ) :
    D.e (Additive.ofMul D.c) = Torus.c := by
  rw [c, ofMul_toMul, AddEquiv.apply_symm_apply]

theorem e_a (D : StrothWeakTypeData B τ) :
    D.e (Additive.ofMul D.a) = Torus.a := by
  rw [a, ofMul_toMul, AddEquiv.apply_symm_apply]

theorem e_b (D : StrothWeakTypeData B τ) :
    D.e (Additive.ofMul D.b) = Torus.b := by
  rw [b, ofMul_toMul, AddEquiv.apply_symm_apply]

theorem e_pow (D : StrothWeakTypeData B τ) (x : B) (n : ℕ) :
    D.e (Additive.ofMul (x ^ n)) = n • D.e (Additive.ofMul x) := by
  rw [ofMul_pow, map_nsmul]

theorem orderOf_c (D : StrothWeakTypeData B τ) : orderOf D.c = 2 ^ τ.m := by
  rw [c, ← addOrderOf_ofMul_eq_orderOf, ofMul_toMul, AddEquiv.addOrderOf_eq, addOrderOf_c]
  rfl

theorem orderOf_a (D : StrothWeakTypeData B τ) : orderOf D.a = 2 ^ τ.n := by
  rw [a, ← addOrderOf_ofMul_eq_orderOf, ofMul_toMul, AddEquiv.addOrderOf_eq, addOrderOf_a]
  rfl

theorem orderOf_b (D : StrothWeakTypeData B τ) : orderOf D.b = 2 ^ τ.n := by
  rw [b, ← addOrderOf_ofMul_eq_orderOf, ofMul_toMul, AddEquiv.addOrderOf_eq, addOrderOf_b,
    StrothTypeIndex.k_two]

theorem exists_zpow_c_a_b (D : StrothWeakTypeData B τ) (x : B) :
    ∃ i j l : ℤ, x = D.c ^ i * D.a ^ j * D.b ^ l := by
  let y : Torus τ.k := D.e (Additive.ofMul x)
  choose z hz using fun i : Fin 3 => ZMod.intCast_surjective (y i)
  have hy : y = z 0 • gen τ.k 0 + z 1 • gen τ.k 1 + z 2 • gen τ.k 2 := by
    funext i
    fin_cases i <;>
      simp [gen, Pi.single_eq_same, Pi.single_eq_of_ne, hz, Pi.add_apply, Pi.smul_apply]
  refine ⟨z 0, z 1, z 2, ?_⟩
  apply Additive.ofMul.injective
  apply D.e.injective
  rw [show D.e (Additive.ofMul x) = y from rfl, hy]
  simp only [ofMul_mul, ofMul_zpow, map_add, map_zsmul]
  rw [D.e_c, D.e_a, D.e_b]

theorem closure_c_a_b_of_zpow (D : StrothWeakTypeData B τ) :
    Subgroup.closure ({(D.c : S), (D.a : S), (D.b : S)} : Set S) = B := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [D.c.2, D.a.2, D.b.2]
  · intro x hx
    obtain ⟨i, j, l, h⟩ := D.exists_zpow_c_a_b ⟨x, hx⟩
    have hx' : x = (D.c : S) ^ i * (D.a : S) ^ j * (D.b : S) ^ l := by
      simpa using congrArg Subtype.val h
    rw [hx']
    let cl : Subgroup S := Subgroup.closure ({(D.c : S), (D.a : S), (D.b : S)} : Set S)
    have hc : (D.c : S) ∈ cl := Subgroup.subset_closure (by simp)
    have ha : (D.a : S) ∈ cl := Subgroup.subset_closure (by simp)
    have hb : (D.b : S) ∈ cl := Subgroup.subset_closure (by simp)
    exact cl.mul_mem (cl.mul_mem (cl.zpow_mem hc i) (cl.zpow_mem ha j)) (cl.zpow_mem hb l)

end StrothWeakTypeData

theorem mho_eq_closure_pow_of_closure_eq {G : Type*} [Group G] {S : Subgroup G} {T : Set G}
    (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hS : Subgroup.closure T = S) (n : ℕ) :
    CFSG.GroupTheory.HuppertProduct.mho S n =
      Subgroup.closure {z : G | ∃ t ∈ T, z = t ^ n} := by
  apply le_antisymm
  · refine CFSG.GroupTheory.HuppertProduct.mho_le_of_forall fun d hd => ?_
    rw [← hS] at hd
    let K : Subgroup G := Subgroup.closure {z : G | ∃ t ∈ T, z = t ^ n}
    change d ^ n ∈ K
    refine Subgroup.closure_induction (p := fun g _ => g ^ n ∈ K) ?_ ?_ ?_ ?_ hd
    · intro t ht
      exact Subgroup.subset_closure ⟨t, ht, rfl⟩
    · simpa using Subgroup.one_mem K
    · intro x y hx hy ihx ihy
      have hc : Commute x y := hcomm x (hS ▸ hx) y (hS ▸ hy)
      rw [hc.mul_pow n]
      exact Subgroup.mul_mem _ ihx ihy
    · intro x _ ih
      rw [inv_pow]
      exact Subgroup.inv_mem _ ih
  · rw [Subgroup.closure_le]
    rintro z ⟨t, ht, rfl⟩
    exact CFSG.GroupTheory.HuppertProduct.pow_mem_mho (hS ▸ Subgroup.subset_closure ht)

theorem zpow_mem_iff_even_of_not_mem_of_sq_mem {G : Type*} [Group G] {H : Subgroup G} {x : G}
    (hxH : x ∉ H) (hx2 : x ^ 2 ∈ H) (i : ℤ) :
    x ^ i ∈ H ↔ Even i := by
  rcases Int.even_or_odd' i with ⟨k, hk | hk⟩
  · rw [hk]
    have hxk : x ^ ((2 : ℤ) * k) = (x ^ (2 : ℤ)) ^ k := zpow_mul x 2 k
    rw [hxk]
    exact ⟨fun _ => even_two_mul k, fun _ =>
      (by simpa [zpow_natCast] using H.zpow_mem hx2 k)⟩
  · rw [hk]
    have h1 : (x ^ (2 : ℤ)) ^ k * x = x ^ ((2 : ℤ) * k + 1) := by
      calc (x ^ (2 : ℤ)) ^ k * x = x ^ ((2 : ℤ) * k) * x := by rw [← zpow_mul]
        _ = x ^ ((2 : ℤ) * k) * x ^ (1 : ℤ) := by rw [zpow_one]
        _ = x ^ ((2 : ℤ) * k + 1) := (zpow_add _ _ _).symm
    constructor
    · intro hmem
      have hk2 : (x ^ (2 : ℤ)) ^ k ∈ H := by
        simpa [zpow_natCast] using H.zpow_mem hx2 k
      have hxeq : x = ((x ^ (2 : ℤ)) ^ k)⁻¹ * x ^ ((2 : ℤ) * k + 1) := by
        rw [← h1]
        group
      exfalso
      exact hxH (by rw [hxeq]; exact H.mul_mem (H.inv_mem hk2) hmem)
    · intro hEven
      exact absurd hEven (Int.not_even_iff_odd.mpr ⟨k, rfl⟩)

theorem k_eq_of_family_one_two (Z : StrothDatum X)
    (hrel : Z.τ.m + 1 = Z.τ.n) (hm : Z.τ.m = 2) :
    Z.τ.k = ![2, 3, 3] := by
  rw [StrothTypeIndex.k_eq]
  funext i
  fin_cases i
  · simpa using hm
  · have hn : Z.τ.n = 3 := by omega
    simpa using hn
  · have hn : Z.τ.n = 3 := by omega
    simpa using hn

theorem even_of_four_zsmul_intCast_zmod_eight {j : ℤ}
    (h : (4 : ℤ) • ((j : ℤ) : ZMod 8) = 0) : Even j := by
  have h' : ((4 * j : ℤ) : ZMod 8) = 0 := by
    simpa [zsmul_eq_mul] using h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
  norm_num at h'
  have h8 : (8 : ℤ) = 4 * 2 := by norm_num
  rw [h8] at h'
  exact even_iff_two_dvd.mpr
    ((mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp h')

theorem even_of_four_zsmul_intCast_zmod_two_pow {n : ℕ} (hn : n = 3) {j : ℤ}
    (h : (4 : ℤ) • ((j : ℤ) : ZMod (2 ^ n)) = 0) : Even j := by
  subst hn
  exact even_of_four_zsmul_intCast_zmod_eight h

theorem exists_zpow_c_a_b_even_of_mem_omegaIn_two (Z : StrothDatum X)
    (hk1 : Z.τ.k 1 = 3) (hk2 : Z.τ.k 2 = 3) {x : G}
    (hx : x ∈ omegaIn 2 Z.D) :
    ∃ i j l : ℤ, x = (Z.dataD.c : G) ^ i * (Z.dataD.a : G) ^ j * (Z.dataD.b : G) ^ l ∧
      Even j ∧ Even l := by
  have hcomm : ∀ a ∈ Z.D, ∀ b ∈ Z.D, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val
      (Z.dataD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hxD, hx4⟩ := (mem_omegaIn_iff_of_comm hcomm).mp hx
  obtain ⟨i, j, l, hrep⟩ := Z.dataD.exists_zpow_c_a_b ⟨x, hxD⟩
  refine ⟨i, j, l, ?_, ?_, ?_⟩
  · simpa using congrArg Subtype.val hrep
  · have h4D : (⟨x, hxD⟩ : Z.D) ^ 4 = 1 := Subtype.ext hx4
    have he4 : (4 : ℤ) • Z.dataD.e (Additive.ofMul (⟨x, hxD⟩ : Z.D)) = 0 := by
      calc (4 : ℤ) • Z.dataD.e (Additive.ofMul (⟨x, hxD⟩ : Z.D))
          = Z.dataD.e ((4 : ℤ) • Additive.ofMul (⟨x, hxD⟩ : Z.D)) := by
            rw [map_zsmul]
        _ = Z.dataD.e (Additive.ofMul ((⟨x, hxD⟩ : Z.D) ^ 4)) := by
            rw [ofMul_pow]
            norm_num
        _ = 0 := by rw [h4D]; simp
    have hcoord : Z.dataD.e (Additive.ofMul (⟨x, hxD⟩ : Z.D)) =
        i • Torus.c + j • Torus.a + l • Torus.b := by
      rw [hrep]
      simp only [ofMul_mul, ofMul_zpow, map_add, map_zsmul]
      rw [Z.dataD.e_c, Z.dataD.e_a, Z.dataD.e_b]
    rw [hcoord] at he4
    have h1 := congrFun he4 1
    have hj : (4 : ℤ) • ((j : ℤ) : ZMod (2 ^ Z.τ.k 1)) = 0 := by
      simpa [Torus.c, Torus.a, Torus.b, gen, Pi.single_eq_same, Pi.single_eq_of_ne,
        Pi.add_apply, Pi.smul_apply] using h1
    exact even_of_four_zsmul_intCast_zmod_two_pow hk1 hj
  · have h4D : (⟨x, hxD⟩ : Z.D) ^ 4 = 1 := Subtype.ext hx4
    have he4 : (4 : ℤ) • Z.dataD.e (Additive.ofMul (⟨x, hxD⟩ : Z.D)) = 0 := by
      calc (4 : ℤ) • Z.dataD.e (Additive.ofMul (⟨x, hxD⟩ : Z.D))
          = Z.dataD.e ((4 : ℤ) • Additive.ofMul (⟨x, hxD⟩ : Z.D)) := by
            rw [map_zsmul]
        _ = Z.dataD.e (Additive.ofMul ((⟨x, hxD⟩ : Z.D) ^ 4)) := by
            rw [ofMul_pow]
            norm_num
        _ = 0 := by rw [h4D]; simp
    have hcoord : Z.dataD.e (Additive.ofMul (⟨x, hxD⟩ : Z.D)) =
        i • Torus.c + j • Torus.a + l • Torus.b := by
      rw [hrep]
      simp only [ofMul_mul, ofMul_zpow, map_add, map_zsmul]
      rw [Z.dataD.e_c, Z.dataD.e_a, Z.dataD.e_b]
    rw [hcoord] at he4
    have h2 := congrFun he4 2
    have hl : (4 : ℤ) • ((l : ℤ) : ZMod (2 ^ Z.τ.k 2)) = 0 := by
      simpa [Torus.c, Torus.a, Torus.b, gen, Pi.single_eq_same, Pi.single_eq_of_ne,
        Pi.add_apply, Pi.smul_apply] using h2
    exact even_of_four_zsmul_intCast_zmod_two_pow hk2 hl

theorem omegaIn_two_eq_closure_of_two (Z : StrothDatum X)
    (hk0 : Z.τ.k 0 = 2) (hk1 : Z.τ.k 1 = 3) (hk2 : Z.τ.k 2 = 3) :
    omegaIn 2 Z.D = Subgroup.closure
      ({(Z.dataD.c : G), (Z.dataD.a : G) ^ 2, (Z.dataD.b : G) ^ 2} : Set G) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨i, j, l, hx, hj, hl⟩ :=
      exists_zpow_c_a_b_even_of_mem_omegaIn_two Z hk1 hk2 hx
    rw [even_iff_exists_two_mul] at hj hl
    obtain ⟨j', hj'⟩ := hj
    obtain ⟨l', hl'⟩ := hl
    have ha : (Z.dataD.a : G) ^ j = ((Z.dataD.a : G) ^ 2) ^ j' := by
      rw [hj']
      simpa [zpow_natCast] using zpow_mul (Z.dataD.a : G) (2 : ℤ) j'
    have hb : (Z.dataD.b : G) ^ l = ((Z.dataD.b : G) ^ 2) ^ l' := by
      rw [hl']
      simpa [zpow_natCast] using zpow_mul (Z.dataD.b : G) (2 : ℤ) l'
    rw [hx, ha, hb]
    let cl : Subgroup G := Subgroup.closure
      ({(Z.dataD.c : G), (Z.dataD.a : G) ^ 2, (Z.dataD.b : G) ^ 2} : Set G)
    have hc : (Z.dataD.c : G) ∈ cl := Subgroup.subset_closure (by simp)
    have ha2 : ((Z.dataD.a : G) ^ 2) ∈ cl := Subgroup.subset_closure (by simp)
    have hb2 : ((Z.dataD.b : G) ^ 2) ∈ cl := Subgroup.subset_closure (by simp)
    exact cl.mul_mem (cl.mul_mem (cl.zpow_mem hc i) (cl.zpow_mem ha2 j'))
      (cl.zpow_mem hb2 l')
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · have hm0 : Z.τ.m = 2 := by simpa [StrothTypeIndex.m] using hk0
      have hc4 : (Z.dataD.c : G) ^ 4 = 1 := by
        apply orderOf_dvd_iff_pow_eq_one.mp
        rw [Subgroup.orderOf_coe, Z.dataD.orderOf_c, hm0]
        norm_num
      exact mem_omegaIn_of_pow_eq_one (i := 2) Z.dataD.c.2 (by simpa using hc4)
    · have hn1 : Z.τ.n = 3 := by simpa [StrothTypeIndex.n] using hk1
      have ha8 : (Z.dataD.a : G) ^ 8 = 1 := by
        apply orderOf_dvd_iff_pow_eq_one.mp
        rw [Subgroup.orderOf_coe, Z.dataD.orderOf_a, hn1]
        norm_num
      have ha24 : ((Z.dataD.a : G) ^ 2) ^ 4 = 1 := by
        rw [← pow_mul, show 2 * 4 = 8 by norm_num, ha8]
      exact mem_omegaIn_of_pow_eq_one (i := 2) (Z.D.pow_mem Z.dataD.a.2 2)
        (by simpa using ha24)
    · have hn2 : Z.τ.n = 3 := by rw [← StrothTypeIndex.k_two Z.τ]; exact hk2
      have hb8 : (Z.dataD.b : G) ^ 8 = 1 := by
        apply orderOf_dvd_iff_pow_eq_one.mp
        rw [Subgroup.orderOf_coe, Z.dataD.orderOf_b, hn2]
        norm_num
      have hb24 : ((Z.dataD.b : G) ^ 2) ^ 4 = 1 := by
        rw [← pow_mul, show 2 * 4 = 8 by norm_num, hb8]
      exact mem_omegaIn_of_pow_eq_one (i := 2) (Z.D.pow_mem Z.dataD.b.2 2)
        (by simpa using hb24)


theorem conjBy_u_sq_a_of_action (Z : StrothDatum X)
    (hu : Z.τ.action.φu Torus.a = (1 : ℤ) • Torus.b) :
    (Z.dataD.u : G)⁻¹ * ((Z.dataD.a : G) ^ 2) * Z.dataD.u = (Z.dataD.b : G) ^ 2 := by
  have ha2 : Z.dataD.e (Additive.ofMul ((Z.dataD.a) ^ 2)) = (2 : ℤ) • Torus.a := by
    rw [Z.dataD.e_pow, Z.dataD.e_a, ← natCast_zsmul]
    norm_num
  have hb2 : Z.dataD.e (Additive.ofMul ((Z.dataD.b) ^ 2)) = (2 : ℤ) • Torus.b := by
    rw [Z.dataD.e_pow, Z.dataD.e_b, ← natCast_zsmul]
    norm_num
  have hconj := Z.dataD.u_conj ((Z.dataD.a) ^ 2)
  rw [ha2] at hconj
  have hphi : Z.τ.action.φu ((2 : ℤ) • Torus.a) = (2 : ℤ) • Torus.b := by
    rw [map_zsmul, hu]
    simp
  have heq : Additive.ofMul (conjBy Z.dataD.u_mem ((Z.dataD.a) ^ 2)) =
      Additive.ofMul ((Z.dataD.b) ^ 2) := by
    apply Z.dataD.e.injective
    rw [hconj, hphi, hb2]
  simpa [conjBy] using congrArg (fun y : Z.D => (y : G)) (Additive.ofMul.injective heq)

theorem conjBy_rho_sq_a_of_action (Z : StrothDatum X)
    (hr : Z.τ.action.φρ Torus.a = (1 : ℤ) • Torus.b) :
    (Z.dataD.ρ : G)⁻¹ * ((Z.dataD.a : G) ^ 2) * Z.dataD.ρ = (Z.dataD.b : G) ^ 2 := by
  have ha2 : Z.dataD.e (Additive.ofMul ((Z.dataD.a) ^ 2)) = (2 : ℤ) • Torus.a := by
    rw [Z.dataD.e_pow, Z.dataD.e_a, ← natCast_zsmul]
    norm_num
  have hb2 : Z.dataD.e (Additive.ofMul ((Z.dataD.b) ^ 2)) = (2 : ℤ) • Torus.b := by
    rw [Z.dataD.e_pow, Z.dataD.e_b, ← natCast_zsmul]
    norm_num
  have hconj := Z.dataD.ρ_conj ((Z.dataD.a) ^ 2)
  rw [ha2] at hconj
  have hphi : Z.τ.action.φρ ((2 : ℤ) • Torus.a) = (2 : ℤ) • Torus.b := by
    rw [map_zsmul, hr]
    simp
  have heq : Additive.ofMul (conjBy Z.dataD.ρ_mem ((Z.dataD.a) ^ 2)) =
      Additive.ofMul ((Z.dataD.b) ^ 2) := by
    apply Z.dataD.e.injective
    rw [hconj, hphi, hb2]
  simpa [conjBy] using congrArg (fun y : Z.D => (y : G)) (Additive.ofMul.injective heq)


theorem conjBy_rho_sq_b_of_action (Z : StrothDatum X)
    (hk0 : Z.τ.k 0 = 2) (hk1 : Z.τ.k 1 = 3) (hk2 : Z.τ.k 2 = 3)
    (hr : Z.τ.action.φρ Torus.b =
      (-2 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b) :
    (Z.dataD.ρ : G)⁻¹ * ((Z.dataD.b : G) ^ 2) * Z.dataD.ρ =
      ((Z.dataD.a : G) ^ 2) * ((Z.dataD.b : G) ^ 2) *
        (((Z.dataD.a : G) ^ 4) * ((Z.dataD.b : G) ^ 4)) := by
  have ha2 : Z.dataD.e (Additive.ofMul ((Z.dataD.a) ^ 2)) = (2 : ℤ) • Torus.a := by
    rw [Z.dataD.e_pow, Z.dataD.e_a, ← natCast_zsmul]
    norm_num
  have hb2 : Z.dataD.e (Additive.ofMul ((Z.dataD.b) ^ 2)) = (2 : ℤ) • Torus.b := by
    rw [Z.dataD.e_pow, Z.dataD.e_b, ← natCast_zsmul]
    norm_num
  have ha4 : Z.dataD.e (Additive.ofMul ((Z.dataD.a) ^ 4)) = (4 : ℤ) • Torus.a := by
    rw [Z.dataD.e_pow, Z.dataD.e_a, ← natCast_zsmul]
    norm_num
  have hb4 : Z.dataD.e (Additive.ofMul ((Z.dataD.b) ^ 4)) = (4 : ℤ) • Torus.b := by
    rw [Z.dataD.e_pow, Z.dataD.e_b, ← natCast_zsmul]
    norm_num
  have hconj := Z.dataD.ρ_conj ((Z.dataD.b) ^ 2)
  rw [hb2] at hconj
  have hphi : Z.τ.action.φρ ((2 : ℤ) • Torus.b) =
      (2 : ℤ) • Torus.a + (2 : ℤ) • Torus.b +
        ((4 : ℤ) • Torus.a + (4 : ℤ) • Torus.b) := by
    rw [map_zsmul, hr]
    funext i
    fin_cases i
    · simp [Torus.c, Torus.a, Torus.b, gen, Pi.single_eq_same, Pi.single_eq_of_ne,
        Pi.add_apply, Pi.smul_apply, hk0, hk1, hk2]
      norm_num
      exact (ZMod.natCast_eq_zero_iff 4 (2 ^ Z.τ.k 0)).mpr (by rw [hk0]; norm_num)
    · simp [Torus.c, Torus.a, Torus.b, gen, Pi.single_eq_same, Pi.single_eq_of_ne,
        Pi.add_apply, Pi.smul_apply, hk0, hk1, hk2]
      norm_num
      simpa using (ZMod.intCast_eq_intCast_iff_dvd_sub (-2) 6 (2 ^ Z.τ.k 1)).mpr
        (by rw [hk1]; norm_num)
    · simp [Torus.c, Torus.a, Torus.b, gen, Pi.single_eq_same, Pi.single_eq_of_ne,
        Pi.add_apply, Pi.smul_apply, hk0, hk1, hk2]
      norm_num
      simpa using (ZMod.intCast_eq_intCast_iff_dvd_sub (-2) 6 (2 ^ Z.τ.k 2)).mpr
        (by rw [hk2]; norm_num)
  have htarget : Z.dataD.e (Additive.ofMul
      (((Z.dataD.a) ^ 2) * ((Z.dataD.b) ^ 2) * (((Z.dataD.a) ^ 4) * ((Z.dataD.b) ^ 4)))) =
      (2 : ℤ) • Torus.a + (2 : ℤ) • Torus.b +
        ((4 : ℤ) • Torus.a + (4 : ℤ) • Torus.b) := by
    rw [ofMul_mul, ofMul_mul, map_add, map_add, ofMul_mul, map_add, ha2, hb2, ha4, hb4]
  have heq : Additive.ofMul (conjBy Z.dataD.ρ_mem ((Z.dataD.b) ^ 2)) =
      Additive.ofMul (((Z.dataD.a) ^ 2) * ((Z.dataD.b) ^ 2) *
        (((Z.dataD.a) ^ 4) * ((Z.dataD.b) ^ 4))) := by
    apply Z.dataD.e.injective
    rw [hconj, hphi, htarget]
  simpa [conjBy] using congrArg (fun y : Z.D => (y : G)) (Additive.ofMul.injective heq)


theorem mem_A_conj_iff (Z : StrothDatum X) {g : G} (hg : g ∈ X.L) (x : G) :
    g⁻¹ * x * g ∈ X.A ↔ x ∈ X.A :=
  (Subgroup.mem_normalizer_iff''.mp (X.L_le_normalizer_A hg) x).symm

theorem sq_gens_mem_A_of_conj (Z : StrothDatum X) (hk : ∀ i, 2 ≤ Z.τ.k i)
    (huL : Z.dataD.u ∈ X.L) (hρL : Z.dataD.ρ ∈ X.L)
    (ha2Ω : (Z.dataD.a : G) ^ 2 ∈ omegaIn 2 Z.D)
    (hb2Ω : (Z.dataD.b : G) ^ 2 ∈ omegaIn 2 Z.D)
    (hu : (Z.dataD.u : G)⁻¹ * ((Z.dataD.a : G) ^ 2) * Z.dataD.u =
      (Z.dataD.b : G) ^ 2)
    (hρa : (Z.dataD.ρ : G)⁻¹ * ((Z.dataD.a : G) ^ 2) * Z.dataD.ρ =
      (Z.dataD.b : G) ^ 2)
    (hρb : (Z.dataD.ρ : G)⁻¹ * ((Z.dataD.b : G) ^ 2) * Z.dataD.ρ =
      ((Z.dataD.a : G) ^ 2) * ((Z.dataD.b : G) ^ 2) *
        (((Z.dataD.a : G) ^ 4) * ((Z.dataD.b : G) ^ 4))) :
    (Z.dataD.a : G) ^ 2 ∈ X.A ∧ (Z.dataD.b : G) ^ 2 ∈ X.A := by
  have hq : ((Z.dataD.a : G) ^ 2 ∈ X.A) ↔ ((Z.dataD.b : G) ^ 2 ∈ X.A) := by
    have h := mem_A_conj_iff Z huL ((Z.dataD.a : G) ^ 2)
    rw [hu] at h
    exact h.symm
  have hprodA : ((Z.dataD.a : G) ^ 2) * ((Z.dataD.b : G) ^ 2) ∈ X.A := by
    let Ω := omegaIn 2 Z.D
    have hq' : (⟨(Z.dataD.a : G) ^ 2, ha2Ω⟩ : Ω) ∈ X.A.subgroupOf Ω ↔
        (⟨(Z.dataD.b : G) ^ 2, hb2Ω⟩ : Ω) ∈ X.A.subgroupOf Ω := by
      simpa [Subgroup.mem_subgroupOf] using hq
    have hmem : (⟨(Z.dataD.a : G) ^ 2, ha2Ω⟩ : Ω) *
        ⟨(Z.dataD.b : G) ^ 2, hb2Ω⟩ ∈ X.A.subgroupOf Ω :=
      (Subgroup.mul_mem_iff_of_index_two (A_index_two_omegaIn_two Z hk)).mpr hq'
    exact Subgroup.mem_subgroupOf.mp hmem
  have ha4Ω1 : (Z.dataD.a : G) ^ 4 ∈ omegaIn 1 Z.D := by
    have h := sq_mem_omegaIn_one_of_mem_omegaIn_two Z ha2Ω
    simpa [pow_succ, mul_assoc] using h
  have hb4Ω1 : (Z.dataD.b : G) ^ 4 ∈ omegaIn 1 Z.D := by
    have h := sq_mem_omegaIn_one_of_mem_omegaIn_two Z hb2Ω
    simpa [pow_succ, mul_assoc] using h
  have hzA : ((Z.dataD.a : G) ^ 4) * ((Z.dataD.b : G) ^ 4) ∈ X.A :=
    X.A.mul_mem (omegaIn_one_le_A Z hk ha4Ω1) (omegaIn_one_le_A Z hk hb4Ω1)
  have hprod2A : ((Z.dataD.a : G) ^ 2) * ((Z.dataD.b : G) ^ 2) *
      (((Z.dataD.a : G) ^ 4) * ((Z.dataD.b : G) ^ 4)) ∈ X.A :=
    X.A.mul_mem hprodA hzA
  have hρmem : (Z.dataD.ρ : G)⁻¹ * ((Z.dataD.b : G) ^ 2) * Z.dataD.ρ ∈ X.A := by
    rw [hρb]
    exact hprod2A
  have hb := (mem_A_conj_iff Z hρL ((Z.dataD.b : G) ^ 2)).mp hρmem
  exact ⟨hq.mpr hb, hb⟩


theorem A_eq_closure_sq_of_two (Z : StrothDatum X) (hk : ∀ i, 2 ≤ Z.τ.k i)
    (hk0 : Z.τ.k 0 = 2) (hk1 : Z.τ.k 1 = 3) (hk2 : Z.τ.k 2 = 3)
    (ha2A : (Z.dataD.a : G) ^ 2 ∈ X.A) (hb2A : (Z.dataD.b : G) ^ 2 ∈ X.A) :
    X.A = Subgroup.closure
      ({(Z.dataD.c : G) ^ 2, (Z.dataD.a : G) ^ 2, (Z.dataD.b : G) ^ 2} : Set G) := by
  let Ω := omegaIn 2 Z.D
  let B : Subgroup G := Subgroup.closure
    ({(Z.dataD.c : G) ^ 2, (Z.dataD.a : G) ^ 2, (Z.dataD.b : G) ^ 2} : Set G)
  have hΩ : Ω = Subgroup.closure
      ({(Z.dataD.c : G), (Z.dataD.a : G) ^ 2, (Z.dataD.b : G) ^ 2} : Set G) :=
    omegaIn_two_eq_closure_of_two Z hk0 hk1 hk2
  have hcΩ : (Z.dataD.c : G) ∈ Ω := by
    rw [hΩ]
    exact Subgroup.subset_closure (by simp)
  have hc2A : (Z.dataD.c : G) ^ 2 ∈ X.A := by
    have h := Subgroup.mul_self_mem_of_index_two (A_index_two_omegaIn_two Z hk)
      (⟨(Z.dataD.c : G), hcΩ⟩ : Ω)
    simpa [pow_two] using Subgroup.mem_subgroupOf.mp h
  have hc2B : (Z.dataD.c : G) ^ 2 ∈ B := Subgroup.subset_closure (by simp)
  have hBA : B ≤ X.A := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    exacts [hc2A, ha2A, hb2A]
  have hcA : (Z.dataD.c : G) ∉ X.A := by
    intro hc
    have hleΩ : Ω ≤ X.A := by
      rw [hΩ, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      exacts [hc, ha2A, hb2A]
    have hEq : X.A = Ω := le_antisymm (A_le_omegaIn_two Z) hleΩ
    have h2 := A_index_two_omegaIn_two Z hk
    rw [hEq] at h2
    rw [Subgroup.subgroupOf_self, Subgroup.index_top] at h2
    omega
  have hcB : (Z.dataD.c : G) ∉ B := fun h => hcA (hBA h)
  apply le_antisymm
  · intro x hxA_mem
    have hxΩ : x ∈ Ω := A_le_omegaIn_two Z hxA_mem
    obtain ⟨i, j, l, hx, hj, hl⟩ :=
      exists_zpow_c_a_b_even_of_mem_omegaIn_two Z hk1 hk2 hxΩ
    rw [even_iff_exists_two_mul] at hj hl
    obtain ⟨j', hj'⟩ := hj
    obtain ⟨l', hl'⟩ := hl
    have ha : (Z.dataD.a : G) ^ j = ((Z.dataD.a : G) ^ 2) ^ j' := by
      rw [hj']
      simpa [zpow_natCast] using zpow_mul (Z.dataD.a : G) (2 : ℤ) j'
    have hb : (Z.dataD.b : G) ^ l = ((Z.dataD.b : G) ^ 2) ^ l' := by
      rw [hl']
      simpa [zpow_natCast] using zpow_mul (Z.dataD.b : G) (2 : ℤ) l'
    have hbB : ((Z.dataD.a : G) ^ 2) ^ j' * ((Z.dataD.b : G) ^ 2) ^ l' ∈ B :=
      B.mul_mem (B.zpow_mem (Subgroup.subset_closure (by simp)) j')
        (B.zpow_mem (Subgroup.subset_closure (by simp)) l')
    have hx' : x = (Z.dataD.c : G) ^ i *
        (((Z.dataD.a : G) ^ 2) ^ j' * ((Z.dataD.b : G) ^ 2) ^ l') := by
      rw [hx, ha, hb]
      group
    have hxA : x ∈ X.A ↔ (Z.dataD.c : G) ^ i ∈ X.A := by
      rw [hx']
      exact X.A.mul_mem_cancel_right (hBA hbB)
    have hxB : x ∈ B ↔ (Z.dataD.c : G) ^ i ∈ B := by
      rw [hx']
      exact B.mul_mem_cancel_right hbB
    have hparA : (Z.dataD.c : G) ^ i ∈ X.A ↔ Even i :=
      zpow_mem_iff_even_of_not_mem_of_sq_mem hcA hc2A i
    have hparB : (Z.dataD.c : G) ^ i ∈ B ↔ Even i :=
      zpow_mem_iff_even_of_not_mem_of_sq_mem hcB hc2B i
    exact hxB.mpr (hparB.mpr (hparA.mp (hxA.mp hxA_mem)))
  · exact hBA



theorem action_rho_a_of_family_one_two (Z : StrothDatum X)
    (hrel : Z.τ.m + 1 = Z.τ.n) (hm : Z.τ.m = 2) :
    Z.τ.action.φρ Torus.a = (1 : ℤ) • Torus.b := by
  rcases Z with ⟨D, hAD, hDS, τ, dataD, hL, hcent⟩
  have hk0 : τ.k 0 = 2 := by simpa [StrothTypeIndex.m] using hm
  have hk1 : τ.k 1 = 3 := by
    change τ.k 0 + 1 = τ.k 1 at hrel
    omega
  cases τ with
  | t100 m =>
      change m = 2 at hk0
      subst m
      change (Type100.action 2).φρ Torus.a = (1 : ℤ) • Torus.b
      simpa using Type100.rho_a 2
  | t101 s =>
      change s + 1 = 2 at hk0
      obtain rfl : s = 1 := by omega
      change (Type101.action 1).φρ Torus.a = (1 : ℤ) • Torus.b
      simpa using Type101.rho_a 1
  | t110 t =>
      change t + 2 = 2 at hk0
      obtain rfl : t = 0 := by omega
      change (Type110.action 0).φρ Torus.a = (1 : ℤ) • Torus.b
      simpa using Type110.rho_a 0
  | t111 t =>
      change t + 2 = 2 at hk0
      obtain rfl : t = 0 := by omega
      change (Type111.action 0).φρ Torus.a = (1 : ℤ) • Torus.b
      simpa using Type111.rho_a 0
  | _ =>
      exfalso
      simp [StrothTypeIndex.k, Type100.k, Type101.k, Type110.k, Type111.k, Type120.k,
        Type121.k, Type130.k, Type131.k, Type200.k, Type201.k, Type210.k, Type211.k,
        Type220.k, Type221.k, Type230.k, Type231.k, Type300.k, Type310.k, Type32x.k,
        Type321.k, Type331.k] at hk0 hk1
      try omega

theorem action_rho_b_of_family_one_two (Z : StrothDatum X)
    (hrel : Z.τ.m + 1 = Z.τ.n) (hm : Z.τ.m = 2) :
    Z.τ.action.φρ Torus.b =
      (-2 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  rcases Z with ⟨D, hAD, hDS, τ, dataD, hL, hcent⟩
  have hk0 : τ.k 0 = 2 := by simpa [StrothTypeIndex.m] using hm
  have hk1 : τ.k 1 = 3 := by
    change τ.k 0 + 1 = τ.k 1 at hrel
    omega
  cases τ with
  | t100 m =>
      change m = 2 at hk0
      subst m
      change (Type100.action 2).φρ Torus.b =
        (-2 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b
      exact Type100.rho_b 2
  | t101 s =>
      change s + 1 = 2 at hk0
      obtain rfl : s = 1 := by omega
      change (Type101.action 1).φρ Torus.b =
        (-2 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b
      exact Type101.rho_b 1
  | t110 t =>
      change t + 2 = 2 at hk0
      obtain rfl : t = 0 := by omega
      change (Type110.action 0).φρ Torus.b =
        (-2 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b
      exact Type110.rho_b 0
  | t111 t =>
      change t + 2 = 2 at hk0
      obtain rfl : t = 0 := by omega
      change (Type111.action 0).φρ Torus.b =
        (-2 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b
      exact Type111.rho_b 0
  | _ =>
      exfalso
      simp [StrothTypeIndex.k, Type100.k, Type101.k, Type110.k, Type111.k, Type120.k,
        Type121.k, Type130.k, Type131.k, Type200.k, Type201.k, Type210.k, Type211.k,
        Type220.k, Type221.k, Type230.k, Type231.k, Type300.k, Type310.k, Type32x.k,
        Type321.k, Type331.k] at hk0 hk1
      try omega

theorem mhoOne_eq_closure_sq_of_two (Z : StrothDatum X) :
    mhoOne Z.D = Subgroup.closure
      ({(Z.dataD.c : G) ^ 2, (Z.dataD.a : G) ^ 2, (Z.dataD.b : G) ^ 2} : Set G) := by
  have hcomm : ∀ a ∈ Z.D, ∀ b ∈ Z.D, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val
      (Z.dataD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h := mho_eq_closure_pow_of_closure_eq hcomm Z.dataD.closure_c_a_b_of_zpow 2
  have hset : {z : G | z = (Z.dataD.c : G) ^ 2 ∨ z = (Z.dataD.a : G) ^ 2 ∨
      z = (Z.dataD.b : G) ^ 2} = ({(Z.dataD.c : G) ^ 2, (Z.dataD.a : G) ^ 2,
        (Z.dataD.b : G) ^ 2} : Set G) := by
    ext z
    simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc, or_left_comm, or_comm]
  simpa [hset] using h

theorem A_eq_mhoOne_of_two_of_actions (Z : StrothDatum X) (hk : ∀ i, 2 ≤ Z.τ.k i)
    (hk0 : Z.τ.k 0 = 2) (hk1 : Z.τ.k 1 = 3) (hk2 : Z.τ.k 2 = 3)
    (hu : Z.τ.action.φu Torus.a = (1 : ℤ) • Torus.b)
    (hra : Z.τ.action.φρ Torus.a = (1 : ℤ) • Torus.b)
    (hrb : Z.τ.action.φρ Torus.b =
      (-2 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b) :
    X.A = mhoOne Z.D := by
  have huL : Z.dataD.u ∈ X.L := Z.hL ▸ Z.dataD.u_mem_L
  have hρL : Z.dataD.ρ ∈ X.L := Z.hL ▸ Z.dataD.ρ_mem_L
  have hΩ := omegaIn_two_eq_closure_of_two Z hk0 hk1 hk2
  have ha2Ω : (Z.dataD.a : G) ^ 2 ∈ omegaIn 2 Z.D := by
    rw [hΩ]
    exact Subgroup.subset_closure (by simp)
  have hb2Ω : (Z.dataD.b : G) ^ 2 ∈ omegaIn 2 Z.D := by
    rw [hΩ]
    exact Subgroup.subset_closure (by simp)
  have hu' := conjBy_u_sq_a_of_action Z hu
  have hra' := conjBy_rho_sq_a_of_action Z hra
  have hrb' := conjBy_rho_sq_b_of_action Z hk0 hk1 hk2 hrb
  obtain ⟨ha2A, hb2A⟩ := sq_gens_mem_A_of_conj Z hk huL hρL ha2Ω hb2Ω hu' hra' hrb'
  exact (A_eq_closure_sq_of_two Z hk hk0 hk1 hk2 ha2A hb2A).trans
    (mhoOne_eq_closure_sq_of_two Z).symm


theorem action_u_a_of_family_one_two (Z : StrothDatum X)
    (hrel : Z.τ.m + 1 = Z.τ.n) (hm : Z.τ.m = 2) :
    Z.τ.action.φu Torus.a = (1 : ℤ) • Torus.b := by
  rcases Z with ⟨D, hAD, hDS, τ, dataD, hL, hcent⟩
  have hk0 : τ.k 0 = 2 := by simpa [StrothTypeIndex.m] using hm
  have hk1 : τ.k 1 = 3 := by
    change τ.k 0 + 1 = τ.k 1 at hrel
    omega
  cases τ with
  | t100 m =>
      change m = 2 at hk0
      subst m
      change (Type100.action 2).φu Torus.a = (1 : ℤ) • Torus.b
      simpa using Type100.u_a 2
  | t101 s =>
      change s + 1 = 2 at hk0
      obtain rfl : s = 1 := by omega
      change (Type101.action 1).φu Torus.a = (1 : ℤ) • Torus.b
      simpa using Type101.u_a 1
  | t110 t =>
      change t + 2 = 2 at hk0
      obtain rfl : t = 0 := by omega
      change (Type110.action 0).φu Torus.a = (1 : ℤ) • Torus.b
      simpa using Type110.u_a 0
  | t111 t =>
      change t + 2 = 2 at hk0
      obtain rfl : t = 0 := by omega
      change (Type111.action 0).φu Torus.a = (1 : ℤ) • Torus.b
      simpa using Type111.u_a 0
  | _ =>
      exfalso
      simp [StrothTypeIndex.k, Type100.k, Type101.k, Type110.k, Type111.k, Type120.k,
        Type121.k, Type130.k, Type131.k, Type200.k, Type201.k, Type210.k, Type211.k,
        Type220.k, Type221.k, Type230.k, Type231.k, Type300.k, Type310.k, Type32x.k,
        Type321.k, Type331.k] at hk0 hk1
      try omega


theorem A_eq_mhoOne_of_two (Z : StrothDatum X) (hk : ∀ i, 2 ≤ Z.τ.k i)
    (hrel : Z.τ.m + 1 = Z.τ.n) (hm : Z.τ.m = 2) :
    X.A = mhoOne Z.D := by
  have hk_eq : Z.τ.k = ![2, 3, 3] := k_eq_of_family_one_two Z hrel hm
  have hk0 : Z.τ.k 0 = 2 := by rw [hk_eq]; rfl
  have hk1 : Z.τ.k 1 = 3 := by rw [hk_eq]; rfl
  have hk2 : Z.τ.k 2 = 3 := by rw [hk_eq]; rfl
  exact A_eq_mhoOne_of_two_of_actions Z hk hk0 hk1 hk2
    (action_u_a_of_family_one_two Z hrel hm)
    (action_rho_a_of_family_one_two Z hrel hm)
    (action_rho_b_of_family_one_two Z hrel hm)

theorem A_le_mhoOne_of_family_one (Z : StrothDatum X) (hk : ∀ i, 2 ≤ Z.τ.k i)
    (hrel : Z.τ.m + 1 = Z.τ.n) :
    X.A ≤ mhoOne Z.D := by
  by_cases hm3 : 3 ≤ Z.τ.m
  · have hk3 : ∀ i, 3 ≤ Z.τ.k i := by
      intro i
      rw [StrothTypeIndex.k_eq]
      fin_cases i <;> simp <;> omega
    exact A_le_mhoOne_of_three_le_k Z hk3
  · have hm2 : Z.τ.m = 2 := by
      have hlt : Z.τ.m < 3 := Nat.lt_of_not_ge hm3
      exact le_antisymm (Nat.le_of_lt_succ hlt) (hk 0)
    rw [A_eq_mhoOne_of_two Z hk hrel hm2]



theorem item224_involutions_of_family_one (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 1 = Z.τ.n) :
    ∀ z : G, z ∈ Z.centralizerInMho → z * z = 1 → z ∈ omegaIn 1 Z.D :=
  item224_involutions_of_A_le_mho Z (A_le_mhoOne_of_family_one Z hk hrel)

end CFSG.CGT.Stroth77
