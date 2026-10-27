module

public import CFSG.CGT.Stroth77.Stroth31DAFrame
public import CFSG.CGT.Stroth77.Stroth31Frame
public import CFSG.CGT.Stroth77.Stroth31Wiring
public import CFSG.GroupTheory.PGroup.OmegaComm

public section

namespace CFSG.CGT.Stroth77

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem zmod_two_mul_eq_zero {m : ℕ} (x : ZMod (2 ^ m)) (hx : 2 * x = 0) :
    x = 0 ∨ x = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  have hx' : x + x = 0 := by simpa [two_mul] using hx
  have hneg : -x = x := neg_eq_of_add_eq_zero_right hx'
  rw [ZMod.neg_eq_self_iff] at hneg
  rcases hneg with h0 | h2
  · exact Or.inl h0
  · right
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst m
      omega
    · have hval : x.val = 2 ^ (m - 1) := by
        have h2' : 2 * x.val = 2 * 2 ^ (m - 1) := by
          rw [h2, ← pow_succ', Nat.sub_add_cancel hm]
        exact Nat.mul_left_cancel (by norm_num) h2'
      haveI : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
      rw [← ZMod.natCast_zmod_val x, hval]

theorem mem_omegaIn_one_iff_of_comm {D : Subgroup G}
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) {x : G} :
    x ∈ omegaIn 1 D ↔ x ∈ D ∧ x * x = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hDcomm : ∀ a b : D, a * b = b * a := fun a b =>
      Subtype.ext (hcomm a a.2 b b.2)
    have hy2 : (y : D) ^ 2 = 1 :=
      (CFSG.mem_omega₁_iff_of_comm hDcomm).mp hy
    refine ⟨y.2, ?_⟩
    simpa [pow_two] using congrArg Subtype.val hy2
  · rintro ⟨hxD, hx2⟩
    exact ⟨⟨x, hxD⟩, Subgroup.subset_closure (by simpa [pow_two] using hx2), rfl⟩

theorem nsmul_gen_self (n : ℕ) (k : Fin 3 → ℕ) (j : Fin 3) :
    (n • gen k j) j = (n : ZMod (2 ^ k j)) := by
  simp [gen]

theorem nsmul_gen_of_ne (n : ℕ) (k : Fin 3 → ℕ) {i j : Fin 3} (h : i ≠ j) :
    (n • gen k j) i = 0 := by
  simp [gen, Pi.single_eq_of_ne h]

theorem t100_torus_decomp (m : ℕ) (z : Torus (StrothTypeIndex.t100 m).k) :
    z = (z 0).val • gen (StrothTypeIndex.t100 m).k 0 +
        (z 1).val • gen (StrothTypeIndex.t100 m).k 1 +
        (z 2).val • gen (StrothTypeIndex.t100 m).k 2 := by
  haveI h0n : NeZero (2 ^ ((StrothTypeIndex.t100 m).k 0)) := by
    rw [show (StrothTypeIndex.t100 m).k 0 = m from by
      simp [StrothTypeIndex.k, Type100.k]]
    exact ⟨pow_ne_zero m (by norm_num)⟩
  haveI h1n : NeZero (2 ^ ((StrothTypeIndex.t100 m).k 1)) := by
    rw [show (StrothTypeIndex.t100 m).k 1 = m + 1 from by
      simp [StrothTypeIndex.k, Type100.k]]
    exact ⟨pow_ne_zero (m + 1) (by norm_num)⟩
  haveI h2n : NeZero (2 ^ ((StrothTypeIndex.t100 m).k 2)) := by
    rw [show (StrothTypeIndex.t100 m).k 2 = m + 1 from by
      simp [StrothTypeIndex.k, Type100.k]]
    exact ⟨pow_ne_zero (m + 1) (by norm_num)⟩
  funext i
  fin_cases i <;> simp only [id_eq, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · rw [Pi.add_apply, Pi.add_apply,
      nsmul_gen_self (z 0).val (StrothTypeIndex.t100 m).k (0 : Fin 3),
      nsmul_gen_of_ne (z 1).val (StrothTypeIndex.t100 m).k (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide),
      nsmul_gen_of_ne (z 2).val (StrothTypeIndex.t100 m).k (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide),
      add_zero, add_zero]
    exact (ZMod.natCast_zmod_val (z 0)).symm
  · rw [Pi.add_apply, Pi.add_apply,
      nsmul_gen_of_ne (z 0).val (StrothTypeIndex.t100 m).k (i := (1 : Fin 3)) (j := (0 : Fin 3)) (by decide),
      nsmul_gen_self (z 1).val (StrothTypeIndex.t100 m).k (1 : Fin 3),
      nsmul_gen_of_ne (z 2).val (StrothTypeIndex.t100 m).k (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide),
      zero_add, add_zero]
    exact (ZMod.natCast_zmod_val (z 1)).symm
  · rw [Pi.add_apply, Pi.add_apply,
      nsmul_gen_of_ne (z 0).val (StrothTypeIndex.t100 m).k (i := (2 : Fin 3)) (j := (0 : Fin 3)) (by decide),
      nsmul_gen_of_ne (z 1).val (StrothTypeIndex.t100 m).k (i := (2 : Fin 3)) (j := (1 : Fin 3)) (by decide),
      nsmul_gen_self (z 2).val (StrothTypeIndex.t100 m).k (2 : Fin 3), zero_add, zero_add]
    exact (ZMod.natCast_zmod_val (z 2)).symm

theorem ofTorus_t100_eq {D : Subgroup G} {m : ℕ}
    (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m))
    (z : Torus (StrothTypeIndex.t100 m).k) :
    dD.ofTorus z = (dD.c : G) ^ (z 0).val * (dD.a : G) ^ (z 1).val *
      (dD.b : G) ^ (z 2).val := by
  conv_lhs => rw [t100_torus_decomp m z]
  rw [dD.ofTorus_add, dD.ofTorus_add, dD.ofTorus_nsmul, dD.ofTorus_nsmul,
    dD.ofTorus_nsmul]
  rw [← dD.c_eq, ← dD.a_eq, ← dD.b_eq]

theorem t100_coords_of_two_torsion {m : ℕ} (z : Torus (StrothTypeIndex.t100 m).k)
    (hz : z + z = 0) :
    (z 0 = 0 ∨ z 0 = ((2 ^ ((StrothTypeIndex.t100 m).k 0 - 1) : ℕ) :
      ZMod (2 ^ ((StrothTypeIndex.t100 m).k 0)))) ∧
      (z 1 = 0 ∨ z 1 = ((2 ^ ((StrothTypeIndex.t100 m).k 1 - 1) : ℕ) :
        ZMod (2 ^ ((StrothTypeIndex.t100 m).k 1)))) ∧
      (z 2 = 0 ∨ z 2 = ((2 ^ ((StrothTypeIndex.t100 m).k 2 - 1) : ℕ) :
        ZMod (2 ^ ((StrothTypeIndex.t100 m).k 2)))) := by
  refine ⟨?_, ?_, ?_⟩
  · apply zmod_two_mul_eq_zero (m := (StrothTypeIndex.t100 m).k 0)
    simpa [two_mul, Pi.add_apply] using congrFun hz 0
  · apply zmod_two_mul_eq_zero (m := (StrothTypeIndex.t100 m).k 1)
    simpa [two_mul, Pi.add_apply] using congrFun hz 1
  · apply zmod_two_mul_eq_zero (m := (StrothTypeIndex.t100 m).k 2)
    simpa [two_mul, Pi.add_apply] using congrFun hz 2

theorem omegaIn_one_t100 {D : Subgroup G} {m : ℕ}
    (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) :
    omegaIn 1 D = Subgroup.closure
      ({(dD.c : G) ^ (2 ^ (m - 1)), (dD.a : G) ^ (2 ^ m),
        (dD.b : G) ^ (2 ^ m)} : Set G) := by
  classical
  haveI : IsMulCommutative D := dD.isMulCommutative
  have hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a :=
    fun a ha b hb => mul_comm_mem_of_isMulCommutative ha hb
  let K : Subgroup G := Subgroup.closure
    ({(dD.c : G) ^ (2 ^ (m - 1)), (dD.a : G) ^ (2 ^ m),
      (dD.b : G) ^ (2 ^ m)} : Set G)
  change omegaIn 1 D = K
  apply le_antisymm
  ·
    intro x hx
    rw [mem_omegaIn_one_iff_of_comm hcomm] at hx
    obtain ⟨hxD, hx2⟩ := hx
    let xD : D := ⟨x, hxD⟩
    let z : Torus (StrothTypeIndex.t100 m).k := dD.e (Additive.ofMul xD)
    have hx2' : xD * xD = 1 := by
      apply Subtype.ext
      simpa [xD, pow_two] using hx2
    have hz : z + z = 0 := by
      have h := congrArg (fun y : D => dD.e (Additive.ofMul y)) hx2'
      simpa [z] using h
    obtain ⟨h0, h1, h2⟩ := t100_coords_of_two_torsion z hz
    have hx_eq : dD.ofTorus z = x := by
      rw [show z = dD.e (Additive.ofMul xD) from rfl]
      simpa [xD] using dD.ofTorus_e xD
    have hc_mem : (dD.c : G) ^ (z 0).val ∈ K := by
      rcases h0 with h0 | h0
      · rw [h0, ZMod.val_zero, pow_zero]
        exact K.one_mem
      · by_cases hm : m = 0
        · subst hm
          have hk0 : (StrothTypeIndex.t100 0).k 0 = 0 := by
            simp [StrothTypeIndex.k, Type100.k]
          haveI : Subsingleton (ZMod (2 ^ ((StrothTypeIndex.t100 0).k 0))) := by
            rw [hk0]
            exact ZMod.subsingleton_iff.mpr rfl
          have hzero : z 0 = 0 := Subsingleton.elim _ _
          rw [hzero, ZMod.val_zero, pow_zero]
          exact K.one_mem
        · have hval : (z 0).val = 2 ^ (m - 1) := by
            rw [h0, ZMod.val_natCast, Nat.mod_eq_of_lt]
            · simp [StrothTypeIndex.k, Type100.k]
            · have hk : (StrothTypeIndex.t100 m).k 0 = m := by
                simp [StrothTypeIndex.k, Type100.k]
              rw [hk]
              exact Nat.pow_lt_pow_right (by norm_num) (by omega)
          rw [hval]
          exact Subgroup.subset_closure (by simp)
    have ha_mem : (dD.a : G) ^ (z 1).val ∈ K := by
      rcases h1 with h1 | h1
      · rw [h1, ZMod.val_zero, pow_zero]
        exact K.one_mem
      · have hval : (z 1).val = 2 ^ m := by
          rw [h1, ZMod.val_natCast, Nat.mod_eq_of_lt]
          · simp [StrothTypeIndex.k, Type100.k]
          · have hk : (StrothTypeIndex.t100 m).k 1 = m + 1 := by
              simp [StrothTypeIndex.k, Type100.k]
            rw [hk]
            exact Nat.pow_lt_pow_right (by norm_num) (by omega)
        rw [hval]
        exact Subgroup.subset_closure (by simp)
    have hb_mem : (dD.b : G) ^ (z 2).val ∈ K := by
      rcases h2 with h2 | h2
      · rw [h2, ZMod.val_zero, pow_zero]
        exact K.one_mem
      · have hval : (z 2).val = 2 ^ m := by
          rw [h2, ZMod.val_natCast, Nat.mod_eq_of_lt]
          · simp [StrothTypeIndex.k, Type100.k]
          · have hk : (StrothTypeIndex.t100 m).k 2 = m + 1 := by
              simp [StrothTypeIndex.k, Type100.k]
            rw [hk]
            exact Nat.pow_lt_pow_right (by norm_num) (by omega)
        rw [hval]
        exact Subgroup.subset_closure (by simp)
    rw [← hx_eq, ofTorus_t100_eq]
    exact K.mul_mem (K.mul_mem hc_mem ha_mem) hb_mem
  ·
    change Subgroup.closure
      ({(dD.c : G) ^ (2 ^ (m - 1)), (dD.a : G) ^ (2 ^ m),
        (dD.b : G) ^ (2 ^ m)} : Set G) ≤ omegaIn 1 D
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    have hc_order : orderOf (dD.c : G) = 2 ^ m := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_c dD
    have ha_order : orderOf (dD.a : G) = 2 ^ (m + 1) := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_a dD
    have hb_order : orderOf (dD.b : G) = 2 ^ (m + 1) := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_b dD
    rcases hy with rfl | rfl | rfl
    · refine (mem_omegaIn_one_iff_of_comm hcomm).mpr ⟨pow_mem dD.c.2 _, ?_⟩
      by_cases hm : m = 0
      · subst hm
        have hc1 : (dD.c : G) = 1 := by
          have h := pow_orderOf_eq_one (dD.c : G)
          rw [hc_order] at h
          simpa using h
        rw [hc1]
        simp
      · rw [← pow_two, ← pow_mul,
          show 2 ^ (m - 1) * 2 = 2 ^ m from by
            rw [← pow_succ, Nat.sub_add_cancel (by omega)]]
        rw [← hc_order]
        exact pow_orderOf_eq_one _
    · refine (mem_omegaIn_one_iff_of_comm hcomm).mpr ⟨pow_mem dD.a.2 _, ?_⟩
      rw [← pow_two, ← pow_mul,
        show 2 ^ m * 2 = 2 ^ (m + 1) from (pow_succ 2 m).symm]
      rw [← ha_order]
      exact pow_orderOf_eq_one _
    · refine (mem_omegaIn_one_iff_of_comm hcomm).mpr ⟨pow_mem dD.b.2 _, ?_⟩
      rw [← pow_two, ← pow_mul,
        show 2 ^ m * 2 = 2 ^ (m + 1) from (pow_succ 2 m).symm]
      rw [← hb_order]
      exact pow_orderOf_eq_one _



theorem stroth31_hfix_frame (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)} (h : F.IsD D dD)
    (hH : NoInvolutionsCentralizing (F.S : Subgroup G) F.A)
    {C : Subgroup G} (hCR : C ≤ strothR (F.toAmbient hH) D)
    {r : G} (hrC : r ∈ C) (hrD : r ∉ D)
    (hc : strothConj r (dD.c : G) = (dD.c : G))
    (ha : strothConj r (dD.a : G) = (dD.a : G))
    (hb : strothConj r (dD.b : G) = (dD.b : G)) : False :=
  stroth31_hfix (X := F.toAmbient hH) (Z := h.toDatum hH) hCR hrC hrD hc ha hb

theorem stroth31Case1_frame (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)} (h : F.IsD D dD)
    (hH : NoInvolutionsCentralizing (F.S : Subgroup G) F.A)
    {C : Subgroup G} (hCR : C ≤ strothR (F.toAmbient hH) D)
    {r : G} (hrC : r ∈ C) (hrD : r ∉ D)
    (hu : ∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G))
    (ht : ∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G))
    (hcab : strothConj r (strothCab dD) = strothCab dD)
    (hsplit : strothConj r (dD.c : G) = (dD.c : G) ∨
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m))
    (hOmega : ∀ s : G, s ∈ D → s * s = 1 → strothConj (dD.u : G) s = s →
      strothConj (dD.t : G) s = s → s = 1 ∨ s = (strothAB dD) ^ (2 ^ m))
    (hsub1 : strothConj r (dD.c : G) = (dD.c : G) →
      strothConj r (dD.a : G) = (dD.a : G) * (strothAB dD) ^ (2 ^ m) →
      strothConj r (dD.b : G) = (dD.b : G) * (strothAB dD) ^ (2 ^ m) → False)
    (hnf2 : strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m) →
      strothConj r (dD.a : G) = (dD.a : G) * (dD.b : G) ^ (2 ^ m) ∧
      strothConj r (dD.b : G) = (dD.b : G) * (dD.a : G) ^ (2 ^ m))
    (hsub2 : strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m) →
      strothConj r (dD.a : G) = (dD.a : G) * (dD.b : G) ^ (2 ^ m) →
      strothConj r (dD.b : G) = (dD.b : G) * (dD.a : G) ^ (2 ^ m) → False) :
    False := by
  have hrN : r ∈ Subgroup.normalizer (D : Set G) :=
    strothR_le_normalizer (F.toAmbient hH) D (hCR hrC)
  have hfix : strothConj r (dD.c : G) = (dD.c : G) →
      strothConj r (dD.a : G) = (dD.a : G) →
      strothConj r (dD.b : G) = (dD.b : G) → False :=
    fun hc ha hb => stroth31_hfix_frame F h hH hCR hrC hrD hc ha hb
  exact stroth31Case1 dD hrN hu ht hcab hsplit hOmega hfix hsub1 hnf2 hsub2

theorem stroth31Case2_frame (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)} (h : F.IsD D dD)
    (hH : NoInvolutionsCentralizing (F.S : Subgroup G) F.A)
    {C : Subgroup G} (_hCR : C ≤ strothR (F.toAmbient hH) D)
    {r : G}
    (hfus : ∀ g ∈ strothR (F.toAmbient hH) D,
      g⁻¹ * (dD.u : G) * g ≠ (dD.c : G) ^ (2 ^ (m - 1)) * (dD.u : G))
    (hsplit : strothConj r (dD.c : G) = (dD.c : G) ∨
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m))
    (hnf1 : strothConj r (dD.c : G) = (dD.c : G) →
      strothConj r (dD.a : G) = (dD.a : G) * (dD.b : G) ^ (2 ^ m) ∧
      strothConj r (dD.b : G) = (dD.b : G) * (dD.a : G) ^ (2 ^ m))
    (hsub1 : strothConj r (dD.c : G) = (dD.c : G) →
      strothConj r (dD.a : G) = (dD.a : G) * (dD.b : G) ^ (2 ^ m) →
      strothConj r (dD.b : G) = (dD.b : G) * (dD.a : G) ^ (2 ^ m) → False)
    (hnf2 : strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m) →
      strothConj r (dD.a : G) = (dD.a : G) ∧ strothConj r (dD.b : G) = (dD.b : G))
    (hsub2 : (∀ g ∈ strothR (F.toAmbient hH) D,
        g⁻¹ * (dD.u : G) * g ≠ (dD.c : G) ^ (2 ^ (m - 1)) * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m) →
      strothConj r (dD.a : G) = (dD.a : G) → strothConj r (dD.b : G) = (dD.b : G) →
      False) :
    False :=
  stroth31Case2 (X := F.toAmbient hH) (Z := h.toDatum hH) dD hfus hsplit hnf1 hsub1 hnf2 hsub2

theorem stroth31Case3_frame {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)} {r : G}
    (hsplit : strothConj r (dD.c : G) = ((dD.c : G))⁻¹ ∨
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ * (strothAB dD) ^ (2 ^ m))
    (hsub1 : strothConj r (dD.c : G) = ((dD.c : G))⁻¹ → False)
    (hsub2 : strothConj r (dD.c : G) = ((dD.c : G))⁻¹ * (strothAB dD) ^ (2 ^ m) → False) :
    False :=
  stroth31Case3 dD hsplit hsub1 hsub2

theorem stroth31Case4_frame {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)} {r : G}
    (hsplit : strothConj r (dD.c : G) = ((dD.c : G))⁻¹ ∨
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ * (strothAB dD) ^ (2 ^ m))
    (hsub1 : strothConj r (dD.c : G) = ((dD.c : G))⁻¹ → False)
    (hsub2 : strothConj r (dD.c : G) = ((dD.c : G))⁻¹ * (strothAB dD) ^ (2 ^ m) → False) :
    False :=
  stroth31Case4 dD hsplit hsub1 hsub2


theorem no_index_four_D_ne_A (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)} (h : F.IsD D dD)
    (hH : NoInvolutionsCentralizing (F.S : Subgroup G) F.A)
    (hne : D ≠ F.A) (C : Subgroup G)
    (hCR : C ≤ strothR (F.toAmbient hH) D)
    (hmin : IsMinimalLModuleMod (h.toDatum hH).dataD C)
    (hfus : ∀ g ∈ strothR (F.toAmbient hH) D,
      g⁻¹ * (dD.u : G) * g ≠ (dD.c : G) ^ (2 ^ (m - 1)) * (dD.u : G))
    (hr : ∃ r : G, r ∈ C ∧ r ∉ D ∧
      strothConj r (dD.uv : G) = (dD.uv : G) ∧
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) ∧
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)))
    (hcover : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      (strothConj r (strothCab dD) = strothCab dD ∨
       strothConj r (strothCab dD) = strothCab dD * (strothAB dD) ^ (2 ^ m) ∨
       strothConj r (strothCab dD) = (strothCab dD)⁻¹ ∨
       strothConj r (strothCab dD) =
         (strothCab dD)⁻¹ * (strothAB dD) ^ (2 ^ m)))
    (hsplit1 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) ∨
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m))
    (hOmega : ∀ s : G, s ∈ D → s * s = 1 → strothConj (dD.u : G) s = s →
      strothConj (dD.t : G) s = s → s = 1 ∨ s = (strothAB dD) ^ (2 ^ m))
    (hsub1_1 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) →
      strothConj r (dD.a : G) = (dD.a : G) * (strothAB dD) ^ (2 ^ m) →
      strothConj r (dD.b : G) = (dD.b : G) * (strothAB dD) ^ (2 ^ m) → False)
    (hnf2_1 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m) →
      strothConj r (dD.a : G) = (dD.a : G) * (dD.b : G) ^ (2 ^ m) ∧
      strothConj r (dD.b : G) = (dD.b : G) * (dD.a : G) ^ (2 ^ m))
    (hsub2_1 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m) →
      strothConj r (dD.a : G) = (dD.a : G) * (dD.b : G) ^ (2 ^ m) →
      strothConj r (dD.b : G) = (dD.b : G) * (dD.a : G) ^ (2 ^ m) → False)
    (hsplit2 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) ∨
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m))
    (hnf1_2 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) →
      strothConj r (dD.a : G) = (dD.a : G) * (dD.b : G) ^ (2 ^ m) ∧
      strothConj r (dD.b : G) = (dD.b : G) * (dD.a : G) ^ (2 ^ m))
    (hsub1_2 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) →
      strothConj r (dD.a : G) = (dD.a : G) * (dD.b : G) ^ (2 ^ m) →
      strothConj r (dD.b : G) = (dD.b : G) * (dD.a : G) ^ (2 ^ m) → False)
    (hnf2_2 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m) →
      strothConj r (dD.a : G) = (dD.a : G) ∧
      strothConj r (dD.b : G) = (dD.b : G))
    (hsub2_2 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m) →
      strothConj r (dD.a : G) = (dD.a : G) →
      strothConj r (dD.b : G) = (dD.b : G) → False)
    (hsplit3 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ ∨
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ * (strothAB dD) ^ (2 ^ m))
    (hsub1_3 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ → False)
    (hsub2_3 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ * (strothAB dD) ^ (2 ^ m) → False)
    (hsplit4 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ ∨
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ * (strothAB dD) ^ (2 ^ m))
    (hsub1_4 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ → False)
    (hsub2_4 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ * (strothAB dD) ^ (2 ^ m) → False)
    (h4 : (D.subgroupOf C).index = 4) : False := by
  have hno4 : (D.subgroupOf C).index ≠ 4 := by
    apply StrothFrame.IsD.no_index_four_of_four_cases h hH C hCR hmin hr hcover
    · intro _ r hrC hrD hr2 huv ht hu hcab
      exact stroth31Case1_frame F h hH hCR hrC hrD hu ht hcab
        (hsplit1 r hrC hrD hr2 huv ht hu) hOmega
        (hsub1_1 r hrC hrD hr2 huv ht hu) (hnf2_1 r hrC hrD hr2 huv ht hu)
        (hsub2_1 r hrC hrD hr2 huv ht hu)
    · intro _ r hrC hrD hr2 huv ht hu hcab
      exact stroth31Case2_frame F h hH hCR hfus
        (hsplit2 r hrC hrD hr2 huv ht hu)
        (hnf1_2 r hrC hrD hr2 huv ht hu) (hsub1_2 r hrC hrD hr2 huv ht hu)
        (hnf2_2 r hrC hrD hr2 huv ht hu)
        (fun _ => hsub2_2 r hrC hrD hr2 huv ht hu)
    · intro _ r hrC hrD hr2 huv ht hu hc
      exact stroth31Case3_frame (dD := dD) (r := r)
        (hsplit3 r hrC hrD hr2 huv ht hu)
        (hsub1_3 r hrC hrD hr2 huv ht hu) (hsub2_3 r hrC hrD hr2 huv ht hu)
    · intro _ r hrC hrD hr2 huv ht hu hc
      exact stroth31Case4_frame (dD := dD) (r := r)
        (hsplit4 r hrC hrD hr2 huv ht hu)
        (hsub1_4 r hrC hrD hr2 huv ht hu) (hsub2_4 r hrC hrD hr2 huv ht hu)
  exact hno4 h4

theorem no_index_four (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)} (h : F.IsD D dD)
    (hH : NoInvolutionsCentralizing (F.S : Subgroup G) F.A) (C : Subgroup G)
    (hCR : C ≤ strothR (F.toAmbient hH) D)
    (hmin : IsMinimalLModuleMod (h.toDatum hH).dataD C)
    (hfus : ∀ g ∈ strothR (F.toAmbient hH) D,
      g⁻¹ * (dD.u : G) * g ≠ (dD.c : G) ^ (2 ^ (m - 1)) * (dD.u : G))
    (hr : ∃ r : G, r ∈ C ∧ r ∉ D ∧
      strothConj r (dD.uv : G) = (dD.uv : G) ∧
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) ∧
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)))
    (hcover : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      (strothConj r (strothCab dD) = strothCab dD ∨
       strothConj r (strothCab dD) = strothCab dD * (strothAB dD) ^ (2 ^ m) ∨
       strothConj r (strothCab dD) = (strothCab dD)⁻¹ ∨
       strothConj r (strothCab dD) =
         (strothCab dD)⁻¹ * (strothAB dD) ^ (2 ^ m)))
    (hsplit1 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) ∨
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m))
    (hOmega : ∀ s : G, s ∈ D → s * s = 1 → strothConj (dD.u : G) s = s →
      strothConj (dD.t : G) s = s → s = 1 ∨ s = (strothAB dD) ^ (2 ^ m))
    (hsub1_1 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) →
      strothConj r (dD.a : G) = (dD.a : G) * (strothAB dD) ^ (2 ^ m) →
      strothConj r (dD.b : G) = (dD.b : G) * (strothAB dD) ^ (2 ^ m) → False)
    (hnf2_1 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m) →
      strothConj r (dD.a : G) = (dD.a : G) * (dD.b : G) ^ (2 ^ m) ∧
      strothConj r (dD.b : G) = (dD.b : G) * (dD.a : G) ^ (2 ^ m))
    (hsub2_1 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m) →
      strothConj r (dD.a : G) = (dD.a : G) * (dD.b : G) ^ (2 ^ m) →
      strothConj r (dD.b : G) = (dD.b : G) * (dD.a : G) ^ (2 ^ m) → False)
    (hsplit2 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) ∨
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m))
    (hnf1_2 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) →
      strothConj r (dD.a : G) = (dD.a : G) * (dD.b : G) ^ (2 ^ m) ∧
      strothConj r (dD.b : G) = (dD.b : G) * (dD.a : G) ^ (2 ^ m))
    (hsub1_2 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) →
      strothConj r (dD.a : G) = (dD.a : G) * (dD.b : G) ^ (2 ^ m) →
      strothConj r (dD.b : G) = (dD.b : G) * (dD.a : G) ^ (2 ^ m) → False)
    (hnf2_2 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m) →
      strothConj r (dD.a : G) = (dD.a : G) ∧
      strothConj r (dD.b : G) = (dD.b : G))
    (hsub2_2 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m) →
      strothConj r (dD.a : G) = (dD.a : G) →
      strothConj r (dD.b : G) = (dD.b : G) → False)
    (hsplit3 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ ∨
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ * (strothAB dD) ^ (2 ^ m))
    (hsub1_3 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ → False)
    (hsub2_3 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ * (strothAB dD) ^ (2 ^ m) → False)
    (hsplit4 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ ∨
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ * (strothAB dD) ^ (2 ^ m))
    (hsub1_4 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ → False)
    (hsub2_4 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ * (strothAB dD) ^ (2 ^ m) → False)
    (h4 : (D.subgroupOf C).index = 4) : False := by
  by_cases hDA : D = F.A
  · exact no_index_four_D_eq_A F dD h hH hDA C hCR hmin h4
  · exact no_index_four_D_ne_A F h hH hDA C hCR hmin hfus hr hcover
      hsplit1 hOmega hsub1_1 hnf2_1 hsub2_1
      hsplit2 hnf1_2 hsub1_2 hnf2_2 hsub2_2
      hsplit3 hsub1_3 hsub2_3 hsplit4 hsub1_4 hsub2_4 h4

theorem stroth_3_1_frame (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)} (h : F.IsD D dD)
    (hH : NoInvolutionsCentralizing (F.S : Subgroup G) F.A) (C : Subgroup G)
    (hCR : C ≤ strothR (F.toAmbient hH) D)
    (hmin : IsMinimalLModuleMod (h.toDatum hH).dataD C)
    (hno4 : (D.subgroupOf C).index ≠ 4) :
    Nat.card C = 2 * Nat.card D :=
  StrothFrame.IsD.stroth_3_1 h hH C hCR hmin hno4

theorem stroth_3_1_frame' (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)} (h : F.IsD D dD)
    (hH : NoInvolutionsCentralizing (F.S : Subgroup G) F.A) (C : Subgroup G)
    (hCR : C ≤ strothR (F.toAmbient hH) D)
    (hmin : IsMinimalLModuleMod (h.toDatum hH).dataD C)
    (hfus : ∀ g ∈ strothR (F.toAmbient hH) D,
      g⁻¹ * (dD.u : G) * g ≠ (dD.c : G) ^ (2 ^ (m - 1)) * (dD.u : G))
    (hr : ∃ r : G, r ∈ C ∧ r ∉ D ∧
      strothConj r (dD.uv : G) = (dD.uv : G) ∧
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) ∧
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)))
    (hcover : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      (strothConj r (strothCab dD) = strothCab dD ∨
       strothConj r (strothCab dD) = strothCab dD * (strothAB dD) ^ (2 ^ m) ∨
       strothConj r (strothCab dD) = (strothCab dD)⁻¹ ∨
       strothConj r (strothCab dD) =
         (strothCab dD)⁻¹ * (strothAB dD) ^ (2 ^ m)))
    (hsplit1 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) ∨
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m))
    (hOmega : ∀ s : G, s ∈ D → s * s = 1 → strothConj (dD.u : G) s = s →
      strothConj (dD.t : G) s = s → s = 1 ∨ s = (strothAB dD) ^ (2 ^ m))
    (hsub1_1 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) →
      strothConj r (dD.a : G) = (dD.a : G) * (strothAB dD) ^ (2 ^ m) →
      strothConj r (dD.b : G) = (dD.b : G) * (strothAB dD) ^ (2 ^ m) → False)
    (hnf2_1 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m) →
      strothConj r (dD.a : G) = (dD.a : G) * (dD.b : G) ^ (2 ^ m) ∧
      strothConj r (dD.b : G) = (dD.b : G) * (dD.a : G) ^ (2 ^ m))
    (hsub2_1 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m) →
      strothConj r (dD.a : G) = (dD.a : G) * (dD.b : G) ^ (2 ^ m) →
      strothConj r (dD.b : G) = (dD.b : G) * (dD.a : G) ^ (2 ^ m) → False)
    (hsplit2 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) ∨
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m))
    (hnf1_2 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) →
      strothConj r (dD.a : G) = (dD.a : G) * (dD.b : G) ^ (2 ^ m) ∧
      strothConj r (dD.b : G) = (dD.b : G) * (dD.a : G) ^ (2 ^ m))
    (hsub1_2 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) →
      strothConj r (dD.a : G) = (dD.a : G) * (dD.b : G) ^ (2 ^ m) →
      strothConj r (dD.b : G) = (dD.b : G) * (dD.a : G) ^ (2 ^ m) → False)
    (hnf2_2 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m) →
      strothConj r (dD.a : G) = (dD.a : G) ∧
      strothConj r (dD.b : G) = (dD.b : G))
    (hsub2_2 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m) →
      strothConj r (dD.a : G) = (dD.a : G) →
      strothConj r (dD.b : G) = (dD.b : G) → False)
    (hsplit3 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ ∨
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ * (strothAB dD) ^ (2 ^ m))
    (hsub1_3 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ → False)
    (hsub2_3 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ * (strothAB dD) ^ (2 ^ m) → False)
    (hsplit4 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ ∨
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ * (strothAB dD) ^ (2 ^ m))
    (hsub1_4 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ → False)
    (hsub2_4 : ∀ r : G, r ∈ C → r ∉ D → r * r ∈ D →
      strothConj r (dD.uv : G) = (dD.uv : G) →
      (∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) →
      (∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G)) →
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ * (strothAB dD) ^ (2 ^ m) → False) :
    Nat.card C = 2 * Nat.card D :=
  StrothFrame.IsD.stroth_3_1 h hH C hCR hmin
    (fun h4 => no_index_four F h hH C hCR hmin hfus hr hcover
      hsplit1 hOmega hsub1_1 hnf2_1 hsub2_1
      hsplit2 hnf1_2 hsub1_2 hnf2_2 hsub2_2
      hsplit3 hsub1_3 hsub2_3 hsplit4 hsub1_4 hsub2_4 h4)

end CFSG.CGT.Stroth77
