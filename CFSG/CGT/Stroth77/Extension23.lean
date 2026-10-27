module

public import CFSG.CGT.Stroth77.Extension22Cocycle

public section

namespace CFSG.CGT.Stroth77

open Matrix


variable {S : Type*} [Group S] [Finite S] {B C : Subgroup S} {m : ℕ}

@[expose] def SquareIn (B : Subgroup S) (x : S) : Prop :=
  ∃ b : B, (b : S) * (b : S) = x


section Generic

variable {τ : StrothTypeIndex} {B : Subgroup S}

theorem comm_of_strothTypeData (D : StrothTypeData B τ) (x y : B) : x * y = y * x := by
  apply Additive.ofMul.injective
  apply D.e.injective
  simp only [ofMul_mul, map_add, add_comm]

theorem isSquareInSubgroup_iff_even_of_type (D : StrothTypeData B τ)
    {x : S} (hx : x ∈ B) :
    SquareIn B x ↔
      ∃ z : Torus τ.k, D.e (Additive.ofMul (⟨x, hx⟩ : B)) = 2 • z := by
  unfold SquareIn
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨D.e (Additive.ofMul b), ?_⟩
    have hb' : (⟨x, hx⟩ : B) = b * b := Subtype.ext (by simpa using hb.symm)
    rw [hb']
    simp only [ofMul_mul, map_add]
    abel
  · rintro ⟨z, hz⟩
    let b : B := Additive.toMul (D.e.symm z)
    refine ⟨b, ?_⟩
    have hb : b * b = ⟨x, hx⟩ := by
      apply Additive.ofMul.injective
      apply D.e.injective
      rw [ofMul_mul, map_add]
      have hbval : Additive.ofMul b = D.e.symm z := by simp [b]
      rw [hbval]
      rw [show D.e (D.e.symm z) = z from AddEquiv.apply_symm_apply D.e z]
      rw [hz]
      abel
    simpa using congrArg (fun y : B => (y : S)) hb

theorem isSquareInSubgroup_mul_of_type (D : StrothTypeData B τ)
    {x y : S} (hx : SquareIn B x) (hy : SquareIn B y) :
    SquareIn B (x * y) := by
  unfold SquareIn at hx hy ⊢
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨⟨a * b, B.mul_mem a.2 b.2⟩, ?_⟩
  have hab : (a : S) * b = b * a :=
    congrArg (fun z : B => (z : S)) (comm_of_strothTypeData D a b)
  change (a : S) * b * ((a : S) * b) = x * y
  calc
    (a : S) * b * ((a : S) * b) = (a : S) * (b * a) * b := by group
    _ = (a : S) * (a * b) * b := by rw [← hab]
    _ = ((a : S) * a) * (b * b) := by group
    _ = x * y := by rw [ha, hb]

theorem isSquareInSubgroup_zpow_of_even_of_type (D : StrothTypeData B τ)
    {i : ℤ} (hi : Even i) :
    SquareIn B ((D.c : S) ^ i) := by
  unfold SquareIn
  obtain ⟨k, rfl⟩ := hi
  refine ⟨⟨D.c ^ k, B.zpow_mem D.c.2 k⟩, ?_⟩
  change (D.c : S) ^ k * (D.c : S) ^ k = (D.c : S) ^ (k + k)
  rw [← _root_.zpow_add]

theorem closure_c_a_b_of_type (D : StrothTypeData B τ) :
    Subgroup.closure ({(D.c : S), (D.a : S), (D.b : S)} : Set S) = B := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact D.c.2
    · exact D.a.2
    · exact D.b.2
  · intro x hx
    let xB : B := ⟨x, hx⟩
    let y : Torus τ.k := D.e (Additive.ofMul xB)
    choose z hz using fun i : Fin 3 => ZMod.intCast_surjective (y i)
    have hc : D.e (Additive.ofMul D.c) = gen τ.k 0 := by
      simp [StrothTypeData.c, Torus.c, gen, ofMul_toMul]
    have ha : D.e (Additive.ofMul D.a) = gen τ.k 1 := by
      simp [StrothTypeData.a, Torus.a, gen, ofMul_toMul]
    have hb : D.e (Additive.ofMul D.b) = gen τ.k 2 := by
      simp [StrothTypeData.b, Torus.b, gen, ofMul_toMul]
    have hy : y = z 0 • gen τ.k 0 + z 1 • gen τ.k 1 + z 2 • gen τ.k 2 := by
      funext i
      fin_cases i <;>
        simp [gen, Pi.single_eq_same, Pi.single_eq_of_ne, hz, Pi.add_apply, Pi.smul_apply]
    have hx' : xB = D.c ^ (z 0) * D.a ^ (z 1) * D.b ^ (z 2) := by
      apply Additive.ofMul.injective
      apply D.e.injective
      rw [show D.e (Additive.ofMul xB) = y from rfl, hy]
      simp only [ofMul_mul, ofMul_zpow, map_add, map_zsmul]
      rw [hc, ha, hb]
    have hx'' : x = (D.c : S) ^ (z 0) * (D.a : S) ^ (z 1) * (D.b : S) ^ (z 2) := by
      simpa using congrArg (fun z : B => (z : S)) hx'
    rw [hx'']
    let cl : Subgroup S := Subgroup.closure ({(D.c : S), (D.a : S), (D.b : S)} : Set S)
    have hc : (D.c : S) ∈ cl := Subgroup.subset_closure (by simp)
    have ha : (D.a : S) ∈ cl := Subgroup.subset_closure (by simp)
    have hb : (D.b : S) ∈ cl := Subgroup.subset_closure (by simp)
    exact cl.mul_mem (cl.mul_mem (cl.zpow_mem hc _) (cl.zpow_mem ha _)) (cl.zpow_mem hb _)

theorem comm_of_le_centralizer_of_type (D : StrothTypeData B τ)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (x y : C) : x * y = y * x := by
  let H : Subgroup C := B.subgroupOf C
  have hindex : H.index = 2 := index_two_of_relIndex hBC hrel
  haveI : H.Normal := Subgroup.normal_of_index_eq_two hindex
  have hcard : Nat.card (C ⧸ H) = 2 := by
    rw [← Subgroup.index_eq_card, hindex]
  haveI : IsCyclic (C ⧸ H) :=
    isCyclic_of_card_dvd_prime (p := 2) (by simpa [hcard])
  have hker : (QuotientGroup.mk' H).ker ≤ Subgroup.center C := by
    rw [QuotientGroup.ker_mk']
    intro b hb
    rw [Subgroup.mem_center_iff]
    intro g
    have hbB : (b : S) ∈ B := Subgroup.mem_subgroupOf.mp hb
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hC g.2) (b : S) hbB).symm
  exact commutative_of_cyclic_center_quotient (QuotientGroup.mk' H) hker x y

theorem closure_eq_of_sq_of_type (D : StrothTypeData B τ)
    (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hd2 : d * d = (D.c : S)) :
    Subgroup.closure ({(d : S), (D.a : S), (D.b : S)} : Set S) = C := by
  let K : Subgroup S := Subgroup.closure ({(d : S), (D.a : S), (D.b : S)} : Set S)
  have hdK : d ∈ K := Subgroup.subset_closure (by simp)
  have haK : (D.a : S) ∈ K := Subgroup.subset_closure (by simp)
  have hbK : (D.b : S) ∈ K := Subgroup.subset_closure (by simp)
  have hcK : (D.c : S) ∈ K := by
    rw [← hd2]
    exact K.mul_mem hdK hdK
  have hBK : B ≤ K := by
    rw [← closure_c_a_b_of_type D, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact hcK
    · exact haK
    · exact hbK
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact hdC
    · exact hBC D.a.2
    · exact hBC D.b.2
  · intro x hxC
    have hindex : (B.subgroupOf C).index = 2 := index_two_of_relIndex hBC hrel
    rcases mem_or_exists_mul_of_index_two hdC hdB hindex hxC with hxB | ⟨b, hbB, rfl⟩
    · exact hBK hxB
    · exact K.mul_mem hdK (hBK hbB)

end Generic

namespace Type200

noncomputable abbrev PhiUV (m : ℕ) : Torus (Type200.k m) →+ Torus (Type200.k m) :=
  (Type200.action m).φuv

noncomputable abbrev PhiT (m : ℕ) : Torus (Type200.k m) →+ Torus (Type200.k m) :=
  (Type200.action m).φt

noncomputable abbrev PhiU (m : ℕ) : Torus (Type200.k m) →+ Torus (Type200.k m) :=
  (Type200.action m).φu

noncomputable abbrev PhiR (m : ℕ) : Torus (Type200.k m) →+ Torus (Type200.k m) :=
  (Type200.action m).φρ

theorem PhiU_eq (m : ℕ) :
    PhiU m = matAct (Type200.k m) Type200.uM (Type200.compat_u m) := rfl

theorem PhiR_eq (m : ℕ) :
    PhiR m = matAct (Type200.k m) Type200.ρM (Type200.compat_rho m) := rfl

theorem PhiUV_eq (m : ℕ) :
    PhiUV m = matAct (Type200.k m) Type200.uvM (Type200.compat_uv m) := rfl

theorem PhiT_eq (m : ℕ) :
    PhiT m = matAct (Type200.k m) Type200.tM (Type200.compat_t m) := rfl

end Type200

namespace StrothTypeData

variable {D : StrothTypeData B (StrothTypeIndex.t200 m)}

theorem ec_conj_u_t200 (D : StrothTypeData B (StrothTypeIndex.t200 m)) (x : B) :
    D.ec (conjBy D.u_mem x) = Type200.PhiU m (D.ec x) :=
  D.u_conj x

theorem ec_conj_t_t200 (D : StrothTypeData B (StrothTypeIndex.t200 m)) (x : B) :
    D.ec (conjBy D.t_mem x) = Type200.PhiT m (D.ec x) :=
  D.t_conj x

theorem ec_conj_ρ_t200 (D : StrothTypeData B (StrothTypeIndex.t200 m)) (x : B) :
    D.ec (conjBy D.ρ_mem x) = Type200.PhiR m (D.ec x) :=
  D.ρ_conj x

theorem ec_conj_uv_t200 (D : StrothTypeData B (StrothTypeIndex.t200 m)) (x : B) :
    D.ec (conjBy D.uv_mem x) = Type200.PhiUV m (D.ec x) :=
  D.uv_conj x

end StrothTypeData

namespace Type200

theorem PhiU_apply_gens (m : ℕ) (a b c : ℤ) :
    PhiU m (a • gen (Type200.k m) 0 + b • gen (Type200.k m) 1 +
        c • gen (Type200.k m) 2) =
      a • gen (Type200.k m) 0 + c • gen (Type200.k m) 1 +
        b • gen (Type200.k m) 2 := by
  rw [PhiU_eq, matAct_zsmul_gens]
  have hu00 : Type200.uM 0 0 = 1 := by decide
  have hu01 : Type200.uM 0 1 = 0 := by decide
  have hu02 : Type200.uM 0 2 = 0 := by decide
  have hu10 : Type200.uM 1 0 = 0 := by decide
  have hu11 : Type200.uM 1 1 = 0 := by decide
  have hu12 : Type200.uM 1 2 = 1 := by decide
  have hu20 : Type200.uM 2 0 = 0 := by decide
  have hu21 : Type200.uM 2 1 = 1 := by decide
  have hu22 : Type200.uM 2 2 = 0 := by decide
  rw [hu00, hu01, hu02, hu10, hu11, hu12, hu20, hu21, hu22]
  simp only [zero_mul, one_mul, zero_add, add_zero]

theorem PhiR_apply_gens (m : ℕ) (a b c : ℤ) :
    PhiR m (a • gen (Type200.k m) 0 + b • gen (Type200.k m) 1 +
        c • gen (Type200.k m) 2) =
      (a - c) • gen (Type200.k m) 0 + (-c) • gen (Type200.k m) 1 +
        (b - c) • gen (Type200.k m) 2 := by
  rw [PhiR_eq, matAct_zsmul_gens]
  have hr00 : Type200.ρM 0 0 = 1 := by decide
  have hr01 : Type200.ρM 0 1 = 0 := by decide
  have hr02 : Type200.ρM 0 2 = -1 := by decide
  have hr10 : Type200.ρM 1 0 = 0 := by decide
  have hr11 : Type200.ρM 1 1 = 0 := by decide
  have hr12 : Type200.ρM 1 2 = -1 := by decide
  have hr20 : Type200.ρM 2 0 = 0 := by decide
  have hr21 : Type200.ρM 2 1 = 1 := by decide
  have hr22 : Type200.ρM 2 2 = -1 := by decide
  rw [hr00, hr01, hr02, hr10, hr11, hr12, hr20, hr21, hr22]
  simp only [zero_mul, one_mul, zero_add, add_zero]
  congr 1 <;> ring

end Type200

theorem t200_square_section
    {m : ℕ} {B : Subgroup S} (D : StrothTypeData B (StrothTypeIndex.t200 m)) (x : B)
    (hu : SquareIn B ((conjBy D.u_mem x * x⁻¹ : B) : S))
    (hr : SquareIn B ((conjBy D.ρ_mem x * x⁻¹ : B) : S)) :
    ∃ i : ℤ, SquareIn B ((x : S) * (D.c : S) ^ (-i)) := by
  classical
  let y : Torus (StrothTypeIndex.t200 m).k := D.e (Additive.ofMul x)
  obtain ⟨i, j, k, hy⟩ := torus_eq_zsmul_gens ((StrothTypeIndex.t200 m).k) y
  have hmemu : ((conjBy D.u_mem x * x⁻¹ : B) : S) ∈ B := (conjBy D.u_mem x * x⁻¹).2
  have hmemr : ((conjBy D.ρ_mem x * x⁻¹ : B) : S) ∈ B := (conjBy D.ρ_mem x * x⁻¹).2
  obtain ⟨zu, hzu⟩ := (isSquareInSubgroup_iff_even_of_type D hmemu).1 hu
  obtain ⟨zr, hzr⟩ := (isSquareInSubgroup_iff_even_of_type D hmemr).1 hr
  have hmapu : D.e (Additive.ofMul (conjBy D.u_mem x * x⁻¹ : B)) =
      (StrothTypeIndex.t200 m).action.φu y - y := by
    rw [ofMul_mul, ofMul_inv, map_add, map_neg]
    have hc : D.e (Additive.ofMul (conjBy D.u_mem x)) =
        (StrothTypeIndex.t200 m).action.φu y := by
      simpa [y, StrothTypeIndex.action, StrothTypeIndex.k] using D.u_conj x
    rw [hc, sub_eq_add_neg]
  have hmapp : D.e (Additive.ofMul (conjBy D.ρ_mem x * x⁻¹ : B)) =
      (StrothTypeIndex.t200 m).action.φρ y - y := by
    rw [ofMul_mul, ofMul_inv, map_add, map_neg]
    have hc : D.e (Additive.ofMul (conjBy D.ρ_mem x)) =
        (StrothTypeIndex.t200 m).action.φρ y := by
      simpa [y, StrothTypeIndex.action, StrothTypeIndex.k] using D.ρ_conj x
    rw [hc, sub_eq_add_neg]
  have hzu' : (StrothTypeIndex.t200 m).action.φu y - y = 2 • zu := hmapu.symm.trans hzu
  have hzr' : (StrothTypeIndex.t200 m).action.φρ y - y = 2 • zr := hmapp.symm.trans hzr
  have hφu : (StrothTypeIndex.t200 m).action.φu y =
      i • gen (StrothTypeIndex.t200 m).k 0 + k • gen (StrothTypeIndex.t200 m).k 1 +
        j • gen (StrothTypeIndex.t200 m).k 2 := by
    rw [hy, map_add, map_add, map_zsmul, map_zsmul, map_zsmul]
    have h0 : (StrothTypeIndex.t200 m).action.φu
        (gen (StrothTypeIndex.t200 m).k 0) = gen (StrothTypeIndex.t200 m).k 0 := by
      show (Type200.action m).φu (gen (Type200.k m) 0) = gen (Type200.k m) 0
      simpa [Torus.c, one_zsmul] using Type200.u_c m
    have h1 : (StrothTypeIndex.t200 m).action.φu
        (gen (StrothTypeIndex.t200 m).k 1) = gen (StrothTypeIndex.t200 m).k 2 := by
      show (Type200.action m).φu (gen (Type200.k m) 1) = gen (Type200.k m) 2
      simpa [Torus.a, one_zsmul] using Type200.u_a m
    have h2 : (StrothTypeIndex.t200 m).action.φu
        (gen (StrothTypeIndex.t200 m).k 2) = gen (StrothTypeIndex.t200 m).k 1 := by
      show (Type200.action m).φu (gen (Type200.k m) 2) = gen (Type200.k m) 1
      simpa [Torus.b, one_zsmul] using Type200.u_b m
    rw [h0, h1, h2]
    abel
  have hy1 : y 1 = (j : ZMod (2 ^ (StrothTypeIndex.t200 m).k 1)) := by
    rw [hy]
    simp [gen, Pi.single_apply]
  have hy2 : y 2 = (k : ZMod (2 ^ (StrothTypeIndex.t200 m).k 2)) := by
    rw [hy]
    simp [gen, Pi.single_apply]
  have h1u : ((k - j : ℤ) : ZMod (2 ^ (StrothTypeIndex.t200 m).k 1)) = 2 * zu 1 := by
    have h := congrFun hzu' 1
    rw [hφu, hy] at h
    simpa [gen, Pi.single_apply, zsmul_eq_mul] using h
  have hkj : Even (k - j) :=
    even_of_intCast_eq_two_mul (N := (StrothTypeIndex.t200 m).k 1)
      (by simp [StrothTypeIndex.k, Type200.k]) h1u
  have hρ0 : (StrothTypeIndex.t200 m).action.φρ
      (gen (StrothTypeIndex.t200 m).k 0) = gen (StrothTypeIndex.t200 m).k 0 := by
    show (Type200.action m).φρ (gen (Type200.k m) 0) = gen (Type200.k m) 0
    simpa [Torus.c, one_zsmul] using Type200.rho_c m
  have hρ1 : (StrothTypeIndex.t200 m).action.φρ
      (gen (StrothTypeIndex.t200 m).k 1) = gen (StrothTypeIndex.t200 m).k 2 := by
    show (Type200.action m).φρ (gen (Type200.k m) 1) = gen (Type200.k m) 2
    simpa [Torus.a, one_zsmul] using Type200.rho_a m
  have hρ2 : (StrothTypeIndex.t200 m).action.φρ
      (gen (StrothTypeIndex.t200 m).k 2) =
      (-1 : ℤ) • gen (StrothTypeIndex.t200 m).k 0 +
        (-1 : ℤ) • gen (StrothTypeIndex.t200 m).k 1 +
        (-1 : ℤ) • gen (StrothTypeIndex.t200 m).k 2 := by
    show (Type200.action m).φρ (gen (Type200.k m) 2) =
      (-1 : ℤ) • gen (Type200.k m) 0 + (-1 : ℤ) • gen (Type200.k m) 1 +
        (-1 : ℤ) • gen (Type200.k m) 2
    simpa only [Torus.c, Torus.a, Torus.b] using Type200.rho_b m
  have hφρ1 : ((StrothTypeIndex.t200 m).action.φρ y) 1 =
      -(k : ZMod (2 ^ (StrothTypeIndex.t200 m).k 1)) := by
    rw [hy, map_add, map_add, map_zsmul, map_zsmul, map_zsmul]
    rw [hρ0, hρ1, hρ2]
    simp [gen, Pi.single_apply, zsmul_eq_mul]
  have hφρ2 : ((StrothTypeIndex.t200 m).action.φρ y) 2 =
      (j : ZMod (2 ^ (StrothTypeIndex.t200 m).k 2)) - (k : ZMod (2 ^ (StrothTypeIndex.t200 m).k 2)) := by
    rw [hy, map_add, map_add, map_zsmul, map_zsmul, map_zsmul]
    rw [hρ0, hρ1, hρ2]
    simp [gen, Pi.single_apply, zsmul_eq_mul]
    ring
  have h2r : ((j - 2 * k : ℤ) : ZMod (2 ^ (StrothTypeIndex.t200 m).k 2)) = 2 * zr 2 := by
    have h := congrFun hzr' 2
    simp only [Pi.sub_apply] at h
    rw [hφρ2, hy2] at h
    simp only [Pi.smul_apply, zsmul_eq_mul] at h
    convert h using 2 <;> push_cast <;> ring
  have hj2k : Even (j - 2 * k) :=
    even_of_intCast_eq_two_mul (N := (StrothTypeIndex.t200 m).k 2)
      (by simp [StrothTypeIndex.k, Type200.k]) h2r
  have h1r : ((-(k + j) : ℤ) : ZMod (2 ^ (StrothTypeIndex.t200 m).k 1)) = 2 * zr 1 := by
    have h := congrFun hzr' 1
    simp only [Pi.sub_apply] at h
    rw [hφρ1, hy1] at h
    simp only [Pi.smul_apply, zsmul_eq_mul] at h
    push_cast
    ring_nf at h ⊢
    exact h
  have hkjsum : Even (k + j) := by
    have hneg : Even (-(k + j)) :=
      even_of_intCast_eq_two_mul (N := (StrothTypeIndex.t200 m).k 1)
        (by simp [StrothTypeIndex.k, Type200.k]) h1r
    rcases hneg with ⟨t, ht⟩
    refine ⟨-t, ?_⟩
    have hneg' := congrArg Neg.neg ht
    simp only [neg_neg, neg_mul] at hneg'
    rw [hneg']
    ring
  have hj : Even j := by
    have h2k : Even (2 * k) := ⟨k, by ring⟩
    exact (Int.even_sub.mp hj2k).mpr h2k
  have hk : Even k := by
    exact (Int.even_add.mp hkjsum).mpr hj
  obtain ⟨j', hj'⟩ := hj
  obtain ⟨k', hk'⟩ := hk
  have hj2 : j = 2 * j' := by rw [hj']; ring
  have hk2 : k = 2 * k' := by rw [hk']; ring
  have hxsplit : y - i • gen (StrothTypeIndex.t200 m).k 0 =
      2 • (j' • gen (StrothTypeIndex.t200 m).k 1 +
        k' • gen (StrothTypeIndex.t200 m).k 2) := by
    rw [hy, hj2, hk2, mul_zsmul, mul_zsmul]
    simp only [smul_add]
    abel
  have hmem : (x : S) * (D.c : S) ^ (-i) ∈ B :=
    B.mul_mem x.2 (B.zpow_mem D.c.2 _)
  refine ⟨i, (isSquareInSubgroup_iff_even_of_type D hmem).2 ?_⟩
  refine ⟨j' • gen (StrothTypeIndex.t200 m).k 1 +
    k' • gen (StrothTypeIndex.t200 m).k 2, ?_⟩
  have hcgen : D.e (Additive.ofMul D.c) = gen (StrothTypeIndex.t200 m).k 0 := by
    simp [StrothTypeData.c, Torus.c, gen]
  have hxci : D.e (Additive.ofMul (x * D.c ^ (-i))) =
      y - i • gen (StrothTypeIndex.t200 m).k 0 := by
    rw [ofMul_mul, ofMul_zpow, map_add, map_zsmul, hcgen]
    rw [show D.e (Additive.ofMul x) = y from rfl, sub_eq_add_neg, neg_zsmul]
  have hsub : (⟨(x : S) * (D.c : S) ^ (-i), hmem⟩ : B) = x * D.c ^ (-i) := rfl
  rw [hsub]
  exact hxci.trans hxsplit

theorem exists_square_root_c_t200
    {m : ℕ} {B C S' : Subgroup S}
    (D : StrothTypeData B (StrothTypeIndex.t200 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (huC : D.u ∈ Subgroup.normalizer C) (hρC : D.ρ ∈ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hCS : C ≤ S') (hne : C ≠ B) :
    ∃ d : S, d ∈ C ∧ d ∉ B ∧ d * d = (D.c : S) := by
  classical
  letI : CommGroup C :=
    { (inferInstance : Group C) with mul_comm := comm_of_le_centralizer_of_type D hBC hC hrel }
  have hlt : B < C := lt_of_le_of_ne hBC hne.symm
  obtain ⟨d, hdC, hdB⟩ := SetLike.exists_of_lt hlt
  have hindex : (B.subgroupOf C).index = 2 := index_two_of_relIndex hBC hrel
  let dC : C := ⟨d, hdC⟩
  have hd2B : d * d ∈ B := by
    have h := sq_mem_of_index_two (B := B) (C := C) (x := dC) hindex
    simpa [dC] using h
  let xB : B := ⟨d * d, hd2B⟩
  have hnotsquare : ¬ SquareIn B (d * d) := by
    rintro ⟨b, hb2⟩
    let bC : C := ⟨b, hBC b.2⟩
    let zC : C := dC * bC⁻¹
    have hb2C : bC * bC = dC * dC := by
      apply Subtype.ext
      simpa [bC, dC] using hb2
    have hz2C : zC * zC = 1 := by
      calc
        zC * zC = (dC * bC⁻¹) * (dC * bC⁻¹) := rfl
        _ = (dC * dC) * (bC⁻¹ * bC⁻¹) := by rw [mul_mul_mul_comm]
        _ = (dC * dC) * (bC * bC)⁻¹ := by rw [_root_.mul_inv_rev]
        _ = 1 := by rw [hb2C]; group
    have hz2 : (zC : S) * (zC : S) = 1 := by
      simpa using congrArg (fun z : C => (z : S)) hz2C
    have hzC : (zC : S) ∈ C := zC.2
    have hzB : (zC : S) ∉ B := by
      intro hz
      have hd_eq : dC = zC * bC := by
        simp [zC, dC, bC]
      have hmem : dC ∈ B.subgroupOf C := by
        rw [hd_eq]
        exact (B.subgroupOf C).mul_mem (by simpa [Subgroup.mem_subgroupOf] using hz)
          (by simpa [Subgroup.mem_subgroupOf, bC] using b.2)
      exact hdB (by simpa [Subgroup.mem_subgroupOf] using hmem)
    exact hzB (hH (zC : S) (hCS hzC) hz2 (hC hzC))
  have square_conj (g : S) (hgB : g ∈ Subgroup.normalizer B)
      (hgC : g ∈ Subgroup.normalizer C) :
      SquareIn B ((conjBy hgB xB * xB⁻¹ : B) : S) := by
    have hconjC : g⁻¹ * d * g ∈ C :=
      (Subgroup.mem_normalizer_iff''.mp hgC d).mp hdC
    have hconjB : g⁻¹ * d * g ∉ B := by
      intro hconj
      exact hdB ((Subgroup.mem_normalizer_iff''.mp hgB d).mpr hconj)
    rcases mem_or_exists_mul_of_index_two hdC hdB hindex hconjC with hconjBinB | ⟨b, hbB, hb_eq⟩
    · exact (hconjB hconjBinB).elim
    let bB : B := ⟨b, hbB⟩
    let bC : C := ⟨b, hBC hbB⟩
    let xC : C := ⟨(xB : S), hBC xB.2⟩
    have hxC : xC = dC * dC := by
      apply Subtype.ext
      simp [xC, dC, xB]
    have hconj_eq : conjBy hgC dC = dC * bC := by
      apply Subtype.ext
      change g⁻¹ * d * g = d * b
      exact hb_eq
    refine ⟨bB, ?_⟩
    have hcoerce : ((conjBy hgB xB * xB⁻¹ : B) : S) =
        ((conjBy hgC xC * xC⁻¹ : C) : S) := rfl
    rw [hcoerce]
    change (bC : S) * (bC : S) = ((conjBy hgC xC * xC⁻¹ : C) : S)
    have hCeq : conjBy hgC xC * xC⁻¹ = bC * bC := by
      have hconj_sq : conjBy hgC xC = conjBy hgC dC * conjBy hgC dC := by
        apply Subtype.ext
        simp only [conjBy, hxC, Subgroup.coe_mul]
        group
      rw [hconj_sq, hconj_eq, hxC]
      calc
        (dC * bC) * (dC * bC) * (dC * dC)⁻¹ =
            (dC * dC) * (bC * bC) * (dC * dC)⁻¹ := by
          rw [mul_mul_mul_comm]
        _ = (bC * bC) * ((dC * dC) * (dC * dC)⁻¹) := by
          rw [mul_comm (dC * dC) (bC * bC), mul_assoc]
        _ = bC * bC := by
          have h : (dC * dC) * (dC * dC)⁻¹ = (1 : C) := mul_inv_cancel _
          rw [h, mul_one]
    exact (congrArg (fun z : C => (z : S)) hCeq).symm
  have hu : SquareIn B ((conjBy D.u_mem xB * xB⁻¹ : B) : S) :=
    square_conj D.u D.u_mem huC
  have hr : SquareIn B ((conjBy D.ρ_mem xB * xB⁻¹ : B) : S) :=
    square_conj D.ρ D.ρ_mem hρC
  obtain ⟨i, hi⟩ := t200_square_section D xB hu hr
  have hx : (xB : S) = d * d := rfl
  rw [hx] at hi
  by_cases heven : Even i
  · have hci := isSquareInSubgroup_zpow_of_even_of_type D heven
    have hx_sq : SquareIn B (d * d) := by
      have hmul := isSquareInSubgroup_mul_of_type D hi hci
      convert hmul using 1
      group
    exact (hnotsquare hx_sq).elim
  · have hodd : Odd i := by simpa using heven
    obtain ⟨t, ht⟩ := hodd
    have hi1 : Even (i - (1 : ℤ)) := ⟨t, by rw [ht]; ring⟩
    have hci1 := isSquareInSubgroup_zpow_of_even_of_type D hi1
    have hxci : SquareIn B ((d * d) * (D.c : S) ^ (-1 : ℤ)) := by
      have hmul := isSquareInSubgroup_mul_of_type D hi hci1
      have hEq : (d * d) * (D.c : S) ^ (-i) * (D.c : S) ^ (i - 1) =
          (d * d) * (D.c : S) ^ (-1 : ℤ) := by
        rw [mul_assoc, ← _root_.zpow_add]
        rw [show -i + (i - 1) = (-1 : ℤ) by ring]
      rwa [hEq] at hmul
    obtain ⟨s, hs2⟩ := hxci
    refine ⟨d * (s : S)⁻¹, C.mul_mem hdC (C.inv_mem (hBC s.2)), ?_, ?_⟩
    · intro hd'B
      apply hdB
      have hd_eq : d = (d * (s : S)⁻¹) * (s : S) := by group
      rw [hd_eq]
      exact B.mul_mem hd'B s.2
    · let sC : C := ⟨s, hBC s.2⟩
      let cC : C := ⟨(D.c : S), hBC D.c.2⟩
      have hs2C : sC * sC = dC * dC * cC⁻¹ := by
        apply Subtype.ext
        simpa [sC, dC, cC] using hs2
      let d'C : C := dC * sC⁻¹
      have hd'C : d'C * d'C = cC := by
        calc
          d'C * d'C = (dC * dC) * (sC * sC)⁻¹ := by
            simp only [d'C]
            rw [mul_mul_mul_comm, _root_.mul_inv_rev]
          _ = (dC * dC) * (dC * dC * cC⁻¹)⁻¹ := by rw [hs2C]
          _ = cC := by
            rw [_root_.mul_inv_rev, inv_inv, ← mul_assoc, mul_comm (dC * dC) cC]
            group
      have := congrArg (fun z : C => (z : S)) hd'C
      simpa [d'C, dC, sC, cC] using this

theorem exists_square_root_c_of_data_t200
    {m : ℕ} {B C S' : Subgroup S}
    (D : StrothTypeData B (StrothTypeIndex.t200 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hCS : C ≤ S') (hne : C ≠ B) :
    ∃ d : S, d ∈ C ∧ d ∉ B ∧ d * d = (D.c : S) :=
  exists_square_root_c_t200 D hBC hC hrel (hL D.u_mem_L) (hL D.ρ_mem_L)
    hH hCS hne

theorem exists_square_root_c_of_hasStrothType_t200
    {m : ℕ} {B C S' : Subgroup S}
    (hB : HasStrothType B (StrothTypeIndex.t200 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hCS : C ≤ S') (hne : C ≠ B) :
    ∃ d : S, d ∈ C ∧ d ∉ B ∧ d * d = (hB.data.c : S) :=
  exists_square_root_c_of_data_t200 hB.data hBC hC hrel hL hH hCS hne

theorem one_le_of_noInvolutionsCentralizing_t200_of_data
    {B C S' : Subgroup S} {m : ℕ}
    (D : StrothTypeData B (StrothTypeIndex.t200 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    1 ≤ m := by
  by_contra hlt
  have hm0 : m = 0 := by omega
  subst hm0
  obtain ⟨d, hdC, hdB, hd2⟩ :=
    exists_square_root_c_of_data_t200 D hBC hC hrel hL hH hcS hne
  have hc1 : (D.c : S) = 1 := by
    rw [← orderOf_eq_one_iff]
    have h := D.orderOf_c
    have hk : (StrothTypeIndex.t200 0).m = 0 := by
      have h := congrFun (StrothTypeIndex.k_eq (StrothTypeIndex.t200 0)) 0
      simpa [StrothTypeIndex.k, Type200.k] using h.symm
    rw [hk] at h
    simpa using h
  exact hdB (hH d (hcS hdC) (by rw [hd2, hc1]) (hC hdC))

theorem one_le_of_noInvolutionsCentralizing_t200
    {B C S' : Subgroup S} {m : ℕ}
    (hB : HasStrothType B (StrothTypeIndex.t200 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    1 ≤ m :=
  one_le_of_noInvolutionsCentralizing_t200_of_data hB.data hBC hC hrel hL hH hcS hne

section CocycleRel

variable {τ : StrothTypeIndex} {D : StrothTypeData B τ}

theorem mul_comm_C_of_type (D : StrothTypeData B τ) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 2 * Nat.card B)
    (x y : C) : x * y = y * x :=
  comm_of_le_centralizer_of_type D hBC hC hrel x y

theorem dC_sq_of_type (D : StrothTypeData B τ) (hBC : B ≤ C) {d : S}
    (hdC : d ∈ C) (hd2 : d * d = (D.c : S)) :
    (⟨d, hdC⟩ : C) * ⟨d, hdC⟩ = Subgroup.inclusion hBC D.c :=
  Subtype.ext hd2

theorem conj_dC_mul_of_type {g : S} (hBC : B ≤ C) {d : S} (hdC : d ∈ C)
    (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B) {b : B}
    (hb : conjBy hgC (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC b) (β : B) :
    conjBy hgC (⟨d, hdC⟩ * Subgroup.inclusion hBC β) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (b * conjBy hgB β) := by
  rw [conjBy_mul, hb, conjBy_inclusion, mul_assoc, ← map_mul]

theorem sq_rel_of_type (D : StrothTypeData B τ) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 2 * Nat.card B)
    {d : S} (hdC : d ∈ C) (hd2 : d * d = (D.c : S)) {g : S}
    (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
    {b β : B} (hb : conjBy hgC (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC b)
    (hβ : conjBy hgB D.c = D.c * β) :
    (2 : ℤ) • D.ec b = D.ec β := by
  letI : CommGroup C :=
    { (inferInstance : Group C) with mul_comm := fun x y => mul_comm_C_of_type D hBC hC hrel x y }
  have hsq : (⟨d, hdC⟩ : C) * ⟨d, hdC⟩ * Subgroup.inclusion hBC (b * b) =
      Subgroup.inclusion hBC (conjBy hgB D.c) := by
    calc (⟨d, hdC⟩ : C) * ⟨d, hdC⟩ * Subgroup.inclusion hBC (b * b)
        = ((⟨d, hdC⟩ : C) * Subgroup.inclusion hBC b) *
            (⟨d, hdC⟩ * Subgroup.inclusion hBC b) := by
          rw [map_mul]
          ac_rfl
      _ = conjBy hgC (⟨d, hdC⟩ : C) * conjBy hgC (⟨d, hdC⟩ : C) := by rw [hb]
      _ = conjBy hgC ((⟨d, hdC⟩ : C) * ⟨d, hdC⟩) := (conjBy_mul hgC _ _).symm
      _ = conjBy hgC (Subgroup.inclusion hBC D.c) := by rw [dC_sq_of_type D hBC hdC hd2]
      _ = Subgroup.inclusion hBC (conjBy hgB D.c) := conjBy_inclusion hBC hgC hgB D.c
  have hBB : D.c * (b * b) = conjBy hgB D.c := by
    apply Subgroup.inclusion_injective hBC
    rw [map_mul]
    rw [show Subgroup.inclusion hBC D.c = (⟨d, hdC⟩ : C) * ⟨d, hdC⟩ from
      (dC_sq_of_type D hBC hdC hd2).symm]
    exact hsq
  have h1 : D.ec (D.c * (b * b)) = D.ec (D.c * β) := by rw [hBB, hβ]
  rw [D.ec_mul, D.ec_mul, D.ec_mul] at h1
  rw [two_zsmul]
  exact add_left_cancel h1

theorem inv_rel_of_type (D : StrothTypeData B τ) (hBC : B ≤ C)
    {d : S} (hdC : d ∈ C) {g : S}
    (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B) {b : B}
    (hb : conjBy hgC (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC b)
    (hg2 : g * g = 1)
    (φ : Torus τ.k →+ Torus τ.k)
    (hφ : ∀ x : B, D.ec (conjBy hgB x) = φ (D.ec x)) :
    D.ec b + φ (D.ec b) = 0 := by
  have h2 : conjBy hgC (conjBy hgC (⟨d, hdC⟩ : C)) = ⟨d, hdC⟩ := by
    apply Subtype.ext
    show g⁻¹ * (g⁻¹ * (d : S) * g) * g = d
    calc g⁻¹ * (g⁻¹ * (d : S) * g) * g = (g * g)⁻¹ * (d : S) * (g * g) := by group
      _ = d := by rw [hg2]; group
  rw [hb, conj_dC_mul_of_type hBC hdC hgC hgB hb] at h2
  have h3 : Subgroup.inclusion hBC (b * conjBy hgB b) = 1 := by
    have h4 := congrArg (fun x : C => (⟨d, hdC⟩ : C)⁻¹ * x) h2
    simpa [mul_assoc] using h4
  have h4 : b * conjBy hgB b = 1 := by
    have h3' : Subgroup.inclusion hBC (b * conjBy hgB b) = Subgroup.inclusion hBC (1 : B) := by
      simpa using h3
    have := Subgroup.inclusion_injective hBC h3'
    simpa using this
  have h5 := congrArg D.ec h4
  rw [D.ec_mul, D.ec_one, hφ] at h5
  exact h5

theorem inv_rel_three_of_type (D : StrothTypeData B τ) (hBC : B ≤ C)
    {d : S} (hdC : d ∈ C) {g : S}
    (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B) {b : B}
    (hb : conjBy hgC (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC b)
    (hg3 : g * g * g = 1)
    (φ : Torus τ.k →+ Torus τ.k)
    (hφ : ∀ x : B, D.ec (conjBy hgB x) = φ (D.ec x)) :
    D.ec b + φ (D.ec b) + φ (φ (D.ec b)) = 0 := by
  have h2 : conjBy hgC (conjBy hgC (conjBy hgC (⟨d, hdC⟩ : C))) = ⟨d, hdC⟩ := by
    apply Subtype.ext
    show g⁻¹ * (g⁻¹ * (g⁻¹ * (d : S) * g) * g) * g = d
    calc g⁻¹ * (g⁻¹ * (g⁻¹ * (d : S) * g) * g) * g
        = (g * g * g)⁻¹ * (d : S) * (g * g * g) := by group
      _ = d := by rw [hg3]; group
  rw [hb] at h2
  rw [conj_dC_mul_of_type hBC hdC hgC hgB hb] at h2
  rw [conj_dC_mul_of_type hBC hdC hgC hgB hb] at h2
  rw [conjBy_mul] at h2
  have h3 : Subgroup.inclusion hBC (b * (conjBy hgB b * conjBy hgB (conjBy hgB b))) = 1 := by
    have h4 := congrArg (fun x : C => (⟨d, hdC⟩ : C)⁻¹ * x) h2
    simpa [mul_assoc] using h4
  have h4 : b * (conjBy hgB b * conjBy hgB (conjBy hgB b)) = 1 := by
    have h3' : Subgroup.inclusion hBC (b * (conjBy hgB b * conjBy hgB (conjBy hgB b))) =
        Subgroup.inclusion hBC (1 : B) := by
      simpa using h3
    have := Subgroup.inclusion_injective hBC h3'
    simpa using this
  have h5 := congrArg D.ec h4
  simp only [D.ec_mul, D.ec_one, hφ] at h5
  simpa [add_assoc] using h5

theorem rel_uv_comm_u_of_type (D : StrothTypeData B τ) (hBC : B ≤ C)
    {d : S} (hdC : d ∈ C)
    (hLu : D.u ∈ Subgroup.normalizer C) (hLuv : D.uv ∈ Subgroup.normalizer C)
    {bU bUV : B}
    (hbU : conjBy hLu (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bU)
    (hbUV : conjBy hLuv (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bUV)
    (φu φuv : Torus τ.k →+ Torus τ.k)
    (hφu : ∀ x : B, D.ec (conjBy D.u_mem x) = φu (D.ec x))
    (hφuv : ∀ x : B, D.ec (conjBy D.uv_mem x) = φuv (D.ec x)) :
    D.ec bU + φu (D.ec bUV) = D.ec bUV + φuv (D.ec bU) := by
  have h1 : conjBy hLu (conjBy hLuv (⟨d, hdC⟩ : C)) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bU * conjBy D.u_mem bUV) := by
    rw [hbUV, conj_dC_mul_of_type hBC hdC hLu D.u_mem hbU]
  have h2 : conjBy hLuv (conjBy hLu (⟨d, hdC⟩ : C)) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bUV * conjBy D.uv_mem bU) := by
    rw [hbU, conj_dC_mul_of_type hBC hdC hLuv D.uv_mem hbUV]
  have heq : conjBy hLu (conjBy hLuv (⟨d, hdC⟩ : C)) =
      conjBy hLuv (conjBy hLu (⟨d, hdC⟩ : C)) := by
    apply Subtype.ext
    show D.u⁻¹ * (D.uv⁻¹ * (d : S) * D.uv) * D.u =
      D.uv⁻¹ * (D.u⁻¹ * (d : S) * D.u) * D.uv
    calc D.u⁻¹ * (D.uv⁻¹ * (d : S) * D.uv) * D.u
        = (D.uv * D.u)⁻¹ * (d : S) * (D.uv * D.u) := by group
      _ = (D.u * D.uv)⁻¹ * (d : S) * (D.u * D.uv) := by rw [D.uv_comm_u]
      _ = D.uv⁻¹ * (D.u⁻¹ * (d : S) * D.u) * D.uv := by group
  rw [h1, h2] at heq
  have h3 : bU * conjBy D.u_mem bUV = bUV * conjBy D.uv_mem bU := by
    apply Subgroup.inclusion_injective hBC
    have h4 := congrArg (fun x : C => (⟨d, hdC⟩ : C)⁻¹ * x) heq
    simpa [mul_assoc] using h4
  have h5 := congrArg D.ec h3
  simpa [D.ec_mul, hφu, hφuv] using h5

theorem rel_t_rho_of_type (D : StrothTypeData B τ) (hBC : B ≤ C)
    {d : S} (hdC : d ∈ C)
    (hLt : D.t ∈ Subgroup.normalizer C) (hLr : D.ρ ∈ Subgroup.normalizer C)
    (hLuv : D.uv ∈ Subgroup.normalizer C) {bT bR bUV : B}
    (hbT : conjBy hLt (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bT)
    (hbR : conjBy hLr (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bR)
    (hbUV : conjBy hLuv (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bUV)
    (φt φr φuv : Torus τ.k →+ Torus τ.k)
    (hφt : ∀ x : B, D.ec (conjBy D.t_mem x) = φt (D.ec x))
    (hφr : ∀ x : B, D.ec (conjBy D.ρ_mem x) = φr (D.ec x))
    (hφuv : ∀ x : B, D.ec (conjBy D.uv_mem x) = φuv (D.ec x)) :
    D.ec bR + φr (D.ec bT) = D.ec bT + φt (D.ec bUV) + φt (φuv (D.ec bR)) := by
  have h1 : conjBy hLr (conjBy hLt (⟨d, hdC⟩ : C)) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bR * conjBy D.ρ_mem bT) := by
    rw [hbT, conj_dC_mul_of_type hBC hdC hLr D.ρ_mem hbR]
  have h2 : conjBy hLt (conjBy hLuv (conjBy hLr (⟨d, hdC⟩ : C))) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC
        (bT * conjBy D.t_mem (bUV * conjBy D.uv_mem bR)) := by
    have hr : conjBy hLuv (conjBy hLr (⟨d, hdC⟩ : C)) =
        ⟨d, hdC⟩ * Subgroup.inclusion hBC (bUV * conjBy D.uv_mem bR) := by
      rw [hbR, conj_dC_mul_of_type hBC hdC hLuv D.uv_mem hbUV]
    rw [hr, conj_dC_mul_of_type hBC hdC hLt D.t_mem hbT]
  have heq : conjBy hLr (conjBy hLt (⟨d, hdC⟩ : C)) =
      conjBy hLt (conjBy hLuv (conjBy hLr (⟨d, hdC⟩ : C))) := by
    apply Subtype.ext
    show D.ρ⁻¹ * (D.t⁻¹ * (d : S) * D.t) * D.ρ =
      D.t⁻¹ * (D.uv⁻¹ * (D.ρ⁻¹ * (d : S) * D.ρ) * D.uv) * D.t
    calc D.ρ⁻¹ * (D.t⁻¹ * (d : S) * D.t) * D.ρ
        = (D.t * D.ρ)⁻¹ * (d : S) * (D.t * D.ρ) := by group
      _ = (D.ρ * D.uv * D.t)⁻¹ * (d : S) * (D.ρ * D.uv * D.t) := by rw [D.t_rho]
      _ = D.t⁻¹ * (D.uv⁻¹ * (D.ρ⁻¹ * (d : S) * D.ρ) * D.uv) * D.t := by group
  rw [h1, h2] at heq
  have h3 : bR * conjBy D.ρ_mem bT =
      bT * conjBy D.t_mem (bUV * conjBy D.uv_mem bR) := by
    apply Subgroup.inclusion_injective hBC
    have h4 := congrArg (fun x : C => (⟨d, hdC⟩ : C)⁻¹ * x) heq
    simpa [mul_assoc] using h4
  have h5 := congrArg D.ec h3
  rw [D.ec_mul, D.ec_mul, hφr] at h5
  have e1 : D.ec (conjBy D.t_mem bUV) = φt (D.ec bUV) := hφt bUV
  have e2 : D.ec (conjBy D.t_mem (conjBy D.uv_mem bR)) = φt (φuv (D.ec bR)) := by
    rw [hφt, hφuv]
  rw [conjBy_mul, D.ec_mul, e1, e2] at h5
  simpa [map_add, add_assoc] using h5

theorem rel_u_rho_of_type (D : StrothTypeData B τ) (hBC : B ≤ C)
    {d : S} (hdC : d ∈ C)
    (hLu : D.u ∈ Subgroup.normalizer C) (hLr : D.ρ ∈ Subgroup.normalizer C)
    {bU bR : B}
    (hbU : conjBy hLu (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bU)
    (hbR : conjBy hLr (⟨d, hdC⟩ : C) = ⟨d, hdC⟩ * Subgroup.inclusion hBC bR)
    (φu φr : Torus τ.k →+ Torus τ.k)
    (hφu : ∀ x : B, D.ec (conjBy D.u_mem x) = φu (D.ec x))
    (hφr : ∀ x : B, D.ec (conjBy D.ρ_mem x) = φr (D.ec x)) :
    D.ec bR + φr (D.ec bU) + φr (φu (D.ec bR)) +
      φr (φu (φr (D.ec bU))) = 0 := by
  have hX2 : conjBy hLr (conjBy hLu (⟨d, hdC⟩ : C)) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bR * conjBy D.ρ_mem bU) := by
    rw [hbU, conj_dC_mul_of_type hBC hdC hLr D.ρ_mem hbR]
  have hX3 : conjBy hLu (conjBy hLr (conjBy hLu (⟨d, hdC⟩ : C))) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bU * conjBy D.u_mem (bR * conjBy D.ρ_mem bU)) := by
    rw [hX2, conj_dC_mul_of_type hBC hdC hLu D.u_mem hbU]
  have hX4 : conjBy hLr (conjBy hLu (conjBy hLr (conjBy hLu (⟨d, hdC⟩ : C)))) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC
        (bR * conjBy D.ρ_mem (bU * conjBy D.u_mem (bR * conjBy D.ρ_mem bU))) := by
    rw [hX3, conj_dC_mul_of_type hBC hdC hLr D.ρ_mem hbR]
  have hfin : conjBy hLr (conjBy hLu (conjBy hLr (conjBy hLu (⟨d, hdC⟩ : C)))) =
      ⟨d, hdC⟩ := by
    apply Subtype.ext
    show D.ρ⁻¹ * (D.u⁻¹ * (D.ρ⁻¹ * (D.u⁻¹ * (d : S) * D.u) * D.ρ) * D.u) * D.ρ = d
    calc D.ρ⁻¹ * (D.u⁻¹ * (D.ρ⁻¹ * (D.u⁻¹ * (d : S) * D.u) * D.ρ) * D.u) * D.ρ
        = (D.u * D.ρ * D.u * D.ρ)⁻¹ * (d : S) * (D.u * D.ρ * D.u * D.ρ) := by group
      _ = d := by rw [D.u_rho]; group
  rw [hX4] at hfin
  have hβ : Subgroup.inclusion hBC
      (bR * conjBy D.ρ_mem (bU * conjBy D.u_mem (bR * conjBy D.ρ_mem bU))) = 1 := by
    have h5 := congrArg (fun x : C => (⟨d, hdC⟩ : C)⁻¹ * x) hfin
    simpa [mul_assoc] using h5
  have h6 : bR * conjBy D.ρ_mem (bU * conjBy D.u_mem (bR * conjBy D.ρ_mem bU)) = 1 := by
    have hβ' : Subgroup.inclusion hBC
        (bR * conjBy D.ρ_mem (bU * conjBy D.u_mem (bR * conjBy D.ρ_mem bU))) =
        Subgroup.inclusion hBC (1 : B) := by
      simpa using hβ
    have := Subgroup.inclusion_injective hBC hβ'
    simpa using this
  have h7 := congrArg D.ec h6
  rw [D.ec_mul, D.ec_one, hφr, D.ec_mul, hφu, D.ec_mul, hφr] at h7
  simp only [map_add] at h7 ⊢
  linear_combination h7

end CocycleRel

namespace Type200

theorem PhiUV_apply_gens (m : ℕ) (a b c : ℤ) :
    PhiUV m (a • gen (Type200.k m) 0 + b • gen (Type200.k m) 1 +
        c • gen (Type200.k m) 2) =
      (-3 * a + b + c) • gen (Type200.k m) 0 +
        (-4 * a + b + 2 * c) • gen (Type200.k m) 1 +
        (-4 * a + 2 * b + c) • gen (Type200.k m) 2 := by
  rw [PhiUV_eq, matAct_zsmul_gens]
  have hv00 : Type200.uvM 0 0 = -3 := by decide
  have hv01 : Type200.uvM 0 1 = 1 := by decide
  have hv02 : Type200.uvM 0 2 = 1 := by decide
  have hv10 : Type200.uvM 1 0 = -4 := by decide
  have hv11 : Type200.uvM 1 1 = 1 := by decide
  have hv12 : Type200.uvM 1 2 = 2 := by decide
  have hv20 : Type200.uvM 2 0 = -4 := by decide
  have hv21 : Type200.uvM 2 1 = 2 := by decide
  have hv22 : Type200.uvM 2 2 = 1 := by decide
  rw [hv00, hv01, hv02, hv10, hv11, hv12, hv20, hv21, hv22]
  simp only [zero_mul, one_mul, zero_add, add_zero]

theorem PhiT_apply_gens (m : ℕ) (a b c : ℤ) :
    PhiT m (a • gen (Type200.k m) 0 + b • gen (Type200.k m) 1 +
        c • gen (Type200.k m) 2) =
      (a - c) • gen (Type200.k m) 0 + (4 * a - b - 2 * c) • gen (Type200.k m) 1 +
        (-c) • gen (Type200.k m) 2 := by
  rw [PhiT_eq, matAct_zsmul_gens]
  have ht00 : Type200.tM 0 0 = 1 := by decide
  have ht01 : Type200.tM 0 1 = 0 := by decide
  have ht02 : Type200.tM 0 2 = -1 := by decide
  have ht10 : Type200.tM 1 0 = 4 := by decide
  have ht11 : Type200.tM 1 1 = -1 := by decide
  have ht12 : Type200.tM 1 2 = -2 := by decide
  have ht20 : Type200.tM 2 0 = 0 := by decide
  have ht21 : Type200.tM 2 1 = 0 := by decide
  have ht22 : Type200.tM 2 2 = -1 := by decide
  rw [ht00, ht01, ht02, ht10, ht11, ht12, ht20, ht21, ht22]
  simp only [zero_mul, one_mul, zero_add, add_zero]
  congr 1 <;> ring

end Type200

theorem k200_zero (m : ℕ) : Type200.k m 0 = m := by
  simp only [Type200.k, Matrix.cons_val_zero]

theorem k200_one (m : ℕ) : Type200.k m 1 = m + 2 := by
  simp only [Type200.k, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]

theorem k200_two (m : ℕ) : Type200.k m 2 = m + 2 := by
  simp only [Type200.k, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem form_bu_t200 {m : ℕ} (hm : 1 ≤ m) {x : Torus (Type200.k m)}
    (h2 : (2 : ℤ) • x = 0) (hφ : x + Type200.PhiU m x = 0) :
    ∃ ε δ : ℕ, ε ≤ 1 ∧ δ ≤ 1 ∧
      x = ((ε : ℤ) * 2 ^ (m - 1)) • gen (Type200.k m) 0 +
        ((δ : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 1 +
        ((δ : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 2 := by
  classical
  obtain ⟨i, j, l, hx⟩ := torus_eq_zsmul_gens (Type200.k m) x
  have h2i : (2 : ZMod (2 ^ m)) * (i : ZMod (2 ^ m)) = 0 := by
    have h := h2
    rw [hx, zsmul_gens] at h
    have h' := gens_coord_zero_of_eq_zero h
    rw [k200_zero] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2j : (2 : ZMod (2 ^ (m + 2))) * (j : ZMod (2 ^ (m + 2))) = 0 := by
    have h := h2
    rw [hx, zsmul_gens] at h
    have h' := gens_coord_one_of_eq_zero h
    rw [k200_one] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2l : (2 : ZMod (2 ^ (m + 2))) * (l : ZMod (2 ^ (m + 2))) = 0 := by
    have h := h2
    rw [hx, zsmul_gens] at h
    have h' := gens_coord_two_of_eq_zero h
    rw [k200_two] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have hφ1 : (j : ZMod (2 ^ (m + 2))) + (l : ZMod (2 ^ (m + 2))) = 0 := by
    have h := hφ
    rw [hx, Type200.PhiU_eq, matAct_zsmul_gens, gens_add] at h
    have h10 : Type200.uM 1 0 = 0 := by decide
    have h11 : Type200.uM 1 1 = 0 := by decide
    have h12 : Type200.uM 1 2 = 1 := by decide
    rw [h10, h11, h12] at h
    simp only [zero_mul, mul_one, one_mul, add_zero, zero_add] at h
    have h' := gens_coord_one_of_eq_zero h
    rw [k200_one] at h'
    rw [Int.cast_add] at h'
    exact h'
  have hjl : (l : ZMod (2 ^ (m + 2))) = (j : ZMod (2 ^ (m + 2))) := by
    have h1 : (l : ZMod (2 ^ (m + 2))) = -(j : ZMod (2 ^ (m + 2))) := by
      linear_combination hφ1
    have h3 : -(j : ZMod (2 ^ (m + 2))) = (j : ZMod (2 ^ (m + 2))) := by
      linear_combination -h2j
    rw [h1, h3]
  obtain ⟨ε, hε1, hε⟩ : ∃ ε : ℕ, ε ≤ 1 ∧
      (i : ZMod (2 ^ m)) = (((ε : ℤ) * 2 ^ (m - 1) : ℤ) : ZMod (2 ^ m)) := by
    rcases (zmod_two_mul_eq_zero_iff hm (i : ZMod (2 ^ m))).1 h2i with h | h
    · exact ⟨0, by norm_num, by rw [h]; push_cast; ring⟩
    · exact ⟨1, by norm_num, by rw [h]; push_cast; ring⟩
  have hmeq : m + 2 - 1 = m + 1 := by omega
  obtain ⟨δ, hδ1, hδ⟩ : ∃ δ : ℕ, δ ≤ 1 ∧
      (j : ZMod (2 ^ (m + 2))) = (((δ : ℤ) * 2 ^ (m + 1) : ℤ) : ZMod (2 ^ (m + 2))) := by
    rcases (zmod_two_mul_eq_zero_iff (by omega : 1 ≤ m + 2)
      (j : ZMod (2 ^ (m + 2)))).1 h2j with h | h
    · exact ⟨0, by norm_num, by rw [h]; push_cast; ring⟩
    · rw [hmeq] at h
      exact ⟨1, by norm_num, by rw [h]; push_cast; ring⟩
  have hl : (l : ZMod (2 ^ (m + 2))) = (((δ : ℤ) * 2 ^ (m + 1) : ℤ) : ZMod (2 ^ (m + 2))) := by
    rw [hjl, hδ]
  refine ⟨ε, δ, hε1, hδ1, ?_⟩
  rw [hx]
  refine gens_eq_of_coord ?_ ?_ ?_
  · rw [k200_zero]
    exact hε
  · rw [k200_one]
    exact hδ
  · rw [k200_two]
    exact hl

theorem form_bt_t200 {m : ℕ} (hm : 1 ≤ m) {y : Torus (Type200.k m)}
    (h2 : (2 : ℤ) • y = (4 : ℤ) • gen (Type200.k m) 1)
    (hφ : y + Type200.PhiT m y = 0) :
    ∃ α q : ℕ, α ≤ 1 ∧ q ≤ 1 ∧
      y = (0 : ℤ) • gen (Type200.k m) 0 +
        ((2 : ℤ) + (α : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 1 +
        ((q : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 2 := by
  classical
  obtain ⟨i, j, l, hy⟩ := torus_eq_zsmul_gens (Type200.k m) y
  have h2' : (2 * i) • gen (Type200.k m) 0 + (2 * j) • gen (Type200.k m) 1 +
      (2 * l) • gen (Type200.k m) 2 =
      (0 : ℤ) • gen (Type200.k m) 0 + (4 : ℤ) • gen (Type200.k m) 1 +
        (0 : ℤ) • gen (Type200.k m) 2 := by
    rw [← zsmul_gens, ← hy, h2]
    simp
  have h2i : (2 : ZMod (2 ^ m)) * (i : ZMod (2 ^ m)) = 0 := by
    have h' := gens_coord_zero h2'
    rw [k200_zero] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2j : (2 : ZMod (2 ^ (m + 2))) * (j : ZMod (2 ^ (m + 2))) = 4 := by
    have h' := gens_coord_one h2'
    rw [k200_one] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2l : (2 : ZMod (2 ^ (m + 2))) * (l : ZMod (2 ^ (m + 2))) = 0 := by
    have h' := gens_coord_two h2'
    rw [k200_two] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have hmeq : m + 2 - 1 = m + 1 := by omega
  obtain ⟨q, hq1, hq⟩ : ∃ q : ℕ, q ≤ 1 ∧
      (l : ZMod (2 ^ (m + 2))) = (q : ZMod (2 ^ (m + 2))) *
        ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2))) := by
    rcases (zmod_two_mul_eq_zero_iff (by omega : 1 ≤ m + 2)
      (l : ZMod (2 ^ (m + 2)))).1 h2l with h | h
    · exact ⟨0, by norm_num, by linear_combination h⟩
    · rw [hmeq] at h
      exact ⟨1, by norm_num, by linear_combination h⟩
  have hφ1 : ((4 * i - 2 * l : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
    have h := hφ
    rw [hy, Type200.PhiT_eq, matAct_zsmul_gens, gens_add] at h
    have ht10 : Type200.tM 1 0 = 4 := by decide
    have ht11 : Type200.tM 1 1 = -1 := by decide
    have ht12 : Type200.tM 1 2 = -2 := by decide
    rw [ht10, ht11, ht12] at h
    have hsimp : (j + (4 * i + -1 * j + -2 * l) : ℤ) = 4 * i - 2 * l := by ring
    rw [hsimp] at h
    exact gens_coord_one_of_eq_zero h
  have h2lz : ((2 : ZMod (2 ^ (m + 2))) * (l : ZMod (2 ^ (m + 2)))) = 0 := by
    rw [hq]
    rw [show (2 : ZMod (2 ^ (m + 2))) * ((q : ZMod (2 ^ (m + 2))) *
        ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2)))) =
        ((q : ℤ) * 2 ^ (m + 2) : ℤ) by push_cast; ring]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨(q : ℤ), by push_cast; ring⟩
  have h2lzi : ((2 * l : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
    simpa using h2lz
  have h4i : ((4 * i : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
    have h := hφ1
    rw [Int.cast_sub] at h
    linear_combination h + h2lzi
  have hdvd4 : ((2 : ℤ) ^ (m + 2)) ∣ 4 * i :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (4 * i) (2 ^ (m + 2))).1 h4i
  have hdvd2 : ((2 : ℤ) ^ (m + 1)) ∣ 2 * i := by
    apply dvd_of_dvd_two_mul (k := m + 1)
    simpa [show m + 1 + 1 = m + 2 by omega, show (2 : ℤ) * (2 * i) = 4 * i by ring] using hdvd4
  have hdvd : ((2 : ℤ) ^ m) ∣ i := by
    apply dvd_of_dvd_two_mul (k := m)
    simpa using hdvd2
  have hi : (i : ZMod (2 ^ m)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdvd
  obtain ⟨α, hα1, hα⟩ : ∃ α : ℕ, α ≤ 1 ∧
      (j : ZMod (2 ^ (m + 2))) = 2 + (α : ZMod (2 ^ (m + 2))) *
        ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2))) := by
    have h2j' : (2 : ZMod (2 ^ (m + 2))) * ((j : ZMod (2 ^ (m + 2))) - 2) = 0 := by
      linear_combination h2j
    rcases (zmod_two_mul_eq_zero_iff (by omega : 1 ≤ m + 2)
      ((j : ZMod (2 ^ (m + 2))) - 2)).1 h2j' with h | h
    · exact ⟨0, by norm_num, by linear_combination h⟩
    · rw [hmeq] at h
      exact ⟨1, by norm_num, by linear_combination h⟩
  have h1 : (((2 : ℤ) + (α : ℤ) * 2 ^ (m + 1) : ℤ) : ZMod (2 ^ (m + 2))) =
      2 + (α : ZMod (2 ^ (m + 2))) * ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2))) := by
    push_cast
    ring
  have h2q : (((q : ℤ) * 2 ^ (m + 1) : ℤ) : ZMod (2 ^ (m + 2))) =
      (q : ZMod (2 ^ (m + 2))) * ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2))) := by
    push_cast
    ring
  refine ⟨α, q, hα1, hq1, ?_⟩
  rw [hy]
  refine gens_eq_of_coord ?_ ?_ ?_
  · rw [k200_zero, Int.cast_zero]
    exact hi
  · rw [k200_one, h1]
    exact hα
  · rw [k200_two, h2q]
    exact hq

theorem form_br_t200 {m : ℕ} (hm : 1 ≤ m) {z : Torus (Type200.k m)}
    (h2 : (2 : ℤ) • z = 0)
    (hφ : z + Type200.PhiR m z + Type200.PhiR m (Type200.PhiR m z) = 0) :
    ∃ θ η : ℕ, η ≤ 1 ∧ θ ≤ 1 ∧
      z = (0 : ℤ) • gen (Type200.k m) 0 + ((η : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 1 +
        ((θ : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 2 := by
  classical
  obtain ⟨i, j, l, hz⟩ := torus_eq_zsmul_gens (Type200.k m) z
  have h2' : (2 * i) • gen (Type200.k m) 0 + (2 * j) • gen (Type200.k m) 1 +
      (2 * l) • gen (Type200.k m) 2 = (0 : Torus (Type200.k m)) := by
    rw [← zsmul_gens, ← hz, h2]
  have h2i : (2 : ZMod (2 ^ m)) * (i : ZMod (2 ^ m)) = 0 := by
    have h' := gens_coord_zero_of_eq_zero h2'
    rw [k200_zero] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2j : (2 : ZMod (2 ^ (m + 2))) * (j : ZMod (2 ^ (m + 2))) = 0 := by
    have h' := gens_coord_one_of_eq_zero h2'
    rw [k200_one] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2l : (2 : ZMod (2 ^ (m + 2))) * (l : ZMod (2 ^ (m + 2))) = 0 := by
    have h' := gens_coord_two_of_eq_zero h2'
    rw [k200_two] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have hdvdj : ((2 : ℤ) ^ (m + 1)) ∣ j :=
    dvd_of_dvd_two_mul (k := m + 1) (dvd_two_mul_of_two_mul_cast_eq_zero h2j)
  have hdvdl : ((2 : ℤ) ^ (m + 1)) ∣ l :=
    dvd_of_dvd_two_mul (k := m + 1) (dvd_two_mul_of_two_mul_cast_eq_zero h2l)
  have hj0 : (j : ZMod (2 ^ m)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (pow_dvd_pow 2 (by omega : m ≤ m + 1)) hdvdj
  have hl0 : (l : ZMod (2 ^ m)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (pow_dvd_pow 2 (by omega : m ≤ m + 1)) hdvdl
  have hφ1 : ((3 * i - j - l : ℤ) : ZMod (2 ^ m)) = 0 := by
    have h := hφ
    rw [hz, Type200.PhiR_apply_gens, Type200.PhiR_apply_gens] at h
    have h0 := congrFun h 0
    simp [gen, Pi.single_apply, zsmul_eq_mul] at h0
    have hk : Type200.k m 0 = m := k200_zero m
    have h0' : (↑i + (↑i - ↑l) + (↑i - ↑j) : ZMod (2 ^ m)) = 0 := hk ▸ h0
    have hcast : (((i + (i - l) + (i - j) : ℤ)) : ZMod (2 ^ m)) = 0 := by
      simpa only [Int.cast_add, Int.cast_sub] using h0'
    have hEq : (((i + (i - l) + (i - j) : ℤ)) : ZMod (2 ^ m)) =
        (((3 * i - j - l : ℤ)) : ZMod (2 ^ m)) := by
      congr 1
      ring
    rwa [hEq] at hcast
  have h3i : (3 : ZMod (2 ^ m)) * (i : ZMod (2 ^ m)) = 0 := by
    have h := hφ1
    rw [Int.cast_sub, Int.cast_sub, Int.cast_mul] at h
    linear_combination h + hj0 + hl0
  have hdvd3 : ((2 : ℤ) ^ m) ∣ 3 * i := by
    have h3i' : (((3 : ℤ) : ZMod (2 ^ m))) * (i : ZMod (2 ^ m)) = 0 := by
      simpa using h3i
    exact dvd_of_cast_mul_eq_zero h3i'
  have hcop : IsCoprime ((2 : ℤ) ^ m) (3 : ℤ) :=
    ((show Odd (3 : ℤ) by norm_num).isCoprime_two).symm.pow_left
  have hi : (i : ZMod (2 ^ m)) = 0 := by
    have hd : ((2 : ℤ) ^ m) ∣ i :=
      Int.dvd_of_dvd_mul_right_of_gcd_one hdvd3 (Int.isCoprime_iff_gcd_eq_one.mp hcop)
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hd
  have hmeq : m + 2 - 1 = m + 1 := by omega
  obtain ⟨η, hη1, hη⟩ : ∃ η : ℕ, η ≤ 1 ∧
      (j : ZMod (2 ^ (m + 2))) = (η : ZMod (2 ^ (m + 2))) *
        ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2))) := by
    rcases (zmod_two_mul_eq_zero_iff (by omega : 1 ≤ m + 2)
      (j : ZMod (2 ^ (m + 2)))).1 h2j with h | h
    · exact ⟨0, by norm_num, by linear_combination h⟩
    · rw [hmeq] at h
      exact ⟨1, by norm_num, by linear_combination h⟩
  obtain ⟨θ, hθ1, hθ⟩ : ∃ θ : ℕ, θ ≤ 1 ∧
      (l : ZMod (2 ^ (m + 2))) = (θ : ZMod (2 ^ (m + 2))) *
        ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2))) := by
    rcases (zmod_two_mul_eq_zero_iff (by omega : 1 ≤ m + 2)
      (l : ZMod (2 ^ (m + 2)))).1 h2l with h | h
    · exact ⟨0, by norm_num, by linear_combination h⟩
    · rw [hmeq] at h
      exact ⟨1, by norm_num, by linear_combination h⟩
  have h2q : (((η : ℤ) * 2 ^ (m + 1) : ℤ) : ZMod (2 ^ (m + 2))) =
      (η : ZMod (2 ^ (m + 2))) * ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2))) := by
    push_cast
    ring
  have h3q : (((θ : ℤ) * 2 ^ (m + 1) : ℤ) : ZMod (2 ^ (m + 2))) =
      (θ : ZMod (2 ^ (m + 2))) * ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2))) := by
    push_cast
    ring
  refine ⟨θ, η, hη1, hθ1, ?_⟩
  rw [hz]
  refine gens_eq_of_coord ?_ ?_ ?_
  · rw [k200_zero, Int.cast_zero]
    exact hi
  · rw [k200_one, h2q]
    exact hη
  · rw [k200_two, h3q]
    exact hθ

theorem form_buv_t200 {m : ℕ} (hm : 1 ≤ m) {z : Torus (Type200.k m)}
    (h2 : (2 : ℤ) • z =
      (-4 : ℤ) • gen (Type200.k m) 0 + (-4 : ℤ) • gen (Type200.k m) 1 +
        (-4 : ℤ) • gen (Type200.k m) 2)
    (hφ : z + Type200.PhiUV m z = 0) :
    ∃ p r : ℕ, p ≤ 1 ∧ r ≤ 1 ∧
      z = (-2 : ℤ) • gen (Type200.k m) 0 +
        ((-2 : ℤ) + (p : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 1 +
        ((-2 : ℤ) + (r : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 2 := by
  classical
  obtain ⟨i, j, l, hz⟩ := torus_eq_zsmul_gens (Type200.k m) z
  have h2' : (2 * i) • gen (Type200.k m) 0 + (2 * j) • gen (Type200.k m) 1 +
      (2 * l) • gen (Type200.k m) 2 =
      (-4 : ℤ) • gen (Type200.k m) 0 + (-4 : ℤ) • gen (Type200.k m) 1 +
        (-4 : ℤ) • gen (Type200.k m) 2 := by
    rw [← zsmul_gens, ← hz, h2]
  have h2i : (2 : ZMod (2 ^ m)) * (i : ZMod (2 ^ m)) = -4 := by
    have h' := gens_coord_zero h2'
    rw [k200_zero] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2j : (2 : ZMod (2 ^ (m + 2))) * (j : ZMod (2 ^ (m + 2))) = -4 := by
    have h' := gens_coord_one h2'
    rw [k200_one] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2l : (2 : ZMod (2 ^ (m + 2))) * (l : ZMod (2 ^ (m + 2))) = -4 := by
    have h' := gens_coord_two h2'
    rw [k200_two] at h'
    rw [Int.cast_mul] at h'
    norm_num at h'
    exact h'
  have h2i' : (2 : ZMod (2 ^ m)) * ((i + 2 : ℤ) : ZMod (2 ^ m)) = 0 := by
    rw [Int.cast_add]
    linear_combination h2i
  obtain ⟨ev, hev1, hev⟩ : ∃ ev : ℕ, ev ≤ 1 ∧
      ((i + 2 : ℤ) : ZMod (2 ^ m)) = (((ev : ℤ) * 2 ^ (m - 1) : ℤ) : ZMod (2 ^ m)) := by
    rcases (zmod_two_mul_eq_zero_iff hm ((i + 2 : ℤ) : ZMod (2 ^ m))).1 h2i' with h | h
    · exact ⟨0, by norm_num, by rw [h]; push_cast; ring⟩
    · exact ⟨1, by norm_num, by rw [h]; push_cast; ring⟩
  have hmeq : m + 2 - 1 = m + 1 := by omega
  obtain ⟨p, hp1, hp⟩ : ∃ p : ℕ, p ≤ 1 ∧
      ((j + 2 : ℤ) : ZMod (2 ^ (m + 2))) = (((p : ℤ) * 2 ^ (m + 1) : ℤ) : ZMod (2 ^ (m + 2))) := by
    have h2j' : (2 : ZMod (2 ^ (m + 2))) * ((j + 2 : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
      rw [Int.cast_add]
      linear_combination h2j
    rcases (zmod_two_mul_eq_zero_iff (by omega : 1 ≤ m + 2)
      ((j + 2 : ℤ) : ZMod (2 ^ (m + 2)))).1 h2j' with h | h
    · exact ⟨0, by norm_num, by rw [h]; push_cast; ring⟩
    · rw [hmeq] at h
      exact ⟨1, by norm_num, by rw [h]; push_cast; ring⟩
  obtain ⟨r, hr1, hr⟩ : ∃ r : ℕ, r ≤ 1 ∧
      ((l + 2 : ℤ) : ZMod (2 ^ (m + 2))) = (((r : ℤ) * 2 ^ (m + 1) : ℤ) : ZMod (2 ^ (m + 2))) := by
    have h2l' : (2 : ZMod (2 ^ (m + 2))) * ((l + 2 : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
      rw [Int.cast_add]
      linear_combination h2l
    rcases (zmod_two_mul_eq_zero_iff (by omega : 1 ≤ m + 2)
      ((l + 2 : ℤ) : ZMod (2 ^ (m + 2)))).1 h2l' with h | h
    · exact ⟨0, by norm_num, by rw [h]; push_cast; ring⟩
    · rw [hmeq] at h
      exact ⟨1, by norm_num, by rw [h]; push_cast; ring⟩
  let i0 : ℤ := -2 + (ev : ℤ) * 2 ^ (m - 1)
  let j0 : ℤ := -2 + (p : ℤ) * 2 ^ (m + 1)
  let l0 : ℤ := -2 + (r : ℤ) * 2 ^ (m + 1)
  have hi0 : (i0 : ZMod (2 ^ m)) = (i : ZMod (2 ^ m)) := by
    have h := hev
    simp only [i0] at h ⊢
    push_cast at h ⊢
    linear_combination -h
  have hj0 : (j0 : ZMod (2 ^ (m + 2))) = (j : ZMod (2 ^ (m + 2))) := by
    have h := hp
    simp only [j0] at h ⊢
    push_cast at h ⊢
    linear_combination -h
  have hl0 : (l0 : ZMod (2 ^ (m + 2))) = (l : ZMod (2 ^ (m + 2))) := by
    have h := hr
    simp only [l0] at h ⊢
    push_cast at h ⊢
    linear_combination -h
  have hz0 : z = i0 • gen (Type200.k m) 0 + j0 • gen (Type200.k m) 1 +
      l0 • gen (Type200.k m) 2 := by
    rw [hz]
    refine gens_eq_of_coord ?_ ?_ ?_
    · exact hi0.symm
    · exact hj0.symm
    · exact hl0.symm
  have hφ' : (i0 • gen (Type200.k m) 0 + j0 • gen (Type200.k m) 1 +
      l0 • gen (Type200.k m) 2) +
      Type200.PhiUV m (i0 • gen (Type200.k m) 0 + j0 • gen (Type200.k m) 1 +
        l0 • gen (Type200.k m) 2) = 0 := by
    rwa [← hz0]
  rw [Type200.PhiUV_apply_gens] at hφ'
  have hφa : ((-4 * i0 + 2 * j0 + 2 * l0 : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
    have h := congrFun hφ' 1
    simp [gen, Pi.single_apply, zsmul_eq_mul] at h
    have hk : Type200.k m 1 = m + 2 := k200_one m
    have h' : (↑j0 + (-(4 * ↑i0) + ↑j0 + 2 * ↑l0) : ZMod (2 ^ (m + 2))) = 0 := hk ▸ h
    have hcast : (((j0 + (-4 * i0 + j0 + 2 * l0) : ℤ)) : ZMod (2 ^ (m + 2))) = 0 := by
      push_cast
      simpa [neg_mul] using h'
    have hEq : (((j0 + (-4 * i0 + j0 + 2 * l0) : ℤ)) : ZMod (2 ^ (m + 2))) =
        (((-4 * i0 + 2 * j0 + 2 * l0 : ℤ)) : ZMod (2 ^ (m + 2))) := by
      congr 1
      ring
    rwa [hEq] at hcast
  have hev0 : ev = 0 := by
    have hpow4 : (4 : ℤ) * 2 ^ (m - 1) = 2 ^ (m + 1) := by
      rw [show m + 1 = (m - 1) + 2 by omega, pow_add]
      ring
    have hid : (-4 * i0 + 2 * j0 + 2 * l0 : ℤ) =
        -((ev : ℤ) * 2 ^ (m + 1)) + (((p : ℤ) + (r : ℤ)) * 2 ^ (m + 2)) := by
      dsimp only [i0, j0, l0]
      calc
        -4 * (-2 + (ev : ℤ) * 2 ^ (m - 1)) +
            2 * (-2 + (p : ℤ) * 2 ^ (m + 1)) +
            2 * (-2 + (r : ℤ) * 2 ^ (m + 1)) =
            -((ev : ℤ) * (4 * 2 ^ (m - 1))) + (((p : ℤ) + (r : ℤ)) * 2 ^ (m + 2)) := by
          ring
        _ = -((ev : ℤ) * 2 ^ (m + 1)) + (((p : ℤ) + (r : ℤ)) * 2 ^ (m + 2)) := by
          rw [hpow4]
    have h' : ((-((ev : ℤ) * 2 ^ (m + 1)) + (((p : ℤ) + (r : ℤ)) * 2 ^ (m + 2)) : ℤ) :
        ZMod (2 ^ (m + 2))) = 0 := by
      rwa [hid] at hφa
    have hpr : ((((p : ℤ) + (r : ℤ)) * 2 ^ (m + 2) : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
      push_cast
      rw [show ((2 : ZMod (2 ^ (m + 2))) ^ (m + 2)) = 0 by
        rw [show (2 : ZMod (2 ^ (m + 2))) = ((2 : ℕ) : ZMod (2 ^ (m + 2))) by norm_num,
          ← Nat.cast_pow, ZMod.natCast_self]]
      simp
    have hev : ((-((ev : ℤ) * 2 ^ (m + 1)) : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
      have h1 := h'
      rw [Int.cast_add, Int.cast_neg] at h1
      rw [hpr, add_zero] at h1
      simpa only [Int.cast_neg] using h1
    have h : (((ev : ℤ) * 2 ^ (m + 1) : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
      have hev' : (-(((ev : ℤ) * 2 ^ (m + 1) : ℤ) : ZMod (2 ^ (m + 2)))) = 0 := by
        rw [← Int.cast_neg]
        exact hev
      exact neg_eq_zero.mp hev'
    interval_cases ev
    · rfl
    · exfalso
      have h' : (((2 ^ (m + 1) : ℕ)) : ZMod (2 ^ (m + 2))) = 0 := by
        simpa using h
      have hdvd : ((2 : ℕ) ^ (m + 2)) ∣ 2 ^ (m + 1) :=
        (ZMod.natCast_eq_zero_iff _ _).1 h'
      have hle := Nat.le_of_dvd (by positivity) hdvd
      have hlt : 2 ^ (m + 1) < 2 ^ (m + 2) :=
        Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : m + 1 < m + 2)
      omega
  have hi0' : i0 = -2 := by simp [i0, hev0]
  refine ⟨p, r, hp1, hr1, ?_⟩
  rw [hz0, hi0']

namespace Type200

theorem PhiU_c (m : ℕ) : PhiU m Torus.c = (1 : ℤ) • Torus.c :=
  Type200.u_c m

theorem PhiT_c (m : ℕ) : PhiT m Torus.c = (1 : ℤ) • Torus.c + (4 : ℤ) • Torus.a :=
  Type200.t_c m

theorem PhiR_c (m : ℕ) : PhiR m Torus.c = (1 : ℤ) • Torus.c :=
  Type200.rho_c m

theorem PhiUV_c (m : ℕ) :
    PhiUV m Torus.c = (-3 : ℤ) • Torus.c + (-4 : ℤ) • Torus.a + (-4 : ℤ) • Torus.b :=
  Type200.uv_c m

end Type200

theorem even_of_two_pow_mul_eq_zero {m : ℕ} {k : ℤ}
    (h : ((k * 2 ^ (m + 1) : ℤ) : ZMod (2 ^ (m + 2))) = 0) : Even k := by
  have hdvd : ((2 : ℤ) ^ (m + 2)) ∣ k * 2 ^ (m + 1) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (k * 2 ^ (m + 1)) (2 ^ (m + 2))).1 h
  obtain ⟨t, ht⟩ := hdvd
  have hsplit : ((2 : ℤ) ^ (m + 2)) = 2 * 2 ^ (m + 1) := by rw [pow_succ]; ring
  have hcancel : k = 2 * t := by
    apply mul_right_cancel₀ (by positivity : ((2 : ℤ) ^ (m + 1)) ≠ 0)
    rw [ht, hsplit]
    ring
  exact ⟨t, by rw [hcancel]; ring⟩

theorem even_of_two_pow_mul_eq_zero_zmod {N : ℕ} (hN : 1 ≤ N) {k : ℤ}
    (h : ((k * 2 ^ (N - 1) : ℤ) : ZMod (2 ^ N)) = 0) : Even k := by
  have hdvd : ((2 : ℤ) ^ N) ∣ k * 2 ^ (N - 1) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (k * 2 ^ (N - 1)) (2 ^ N)).1 h
  have hsplit : ((2 : ℤ) ^ N) = 2 * 2 ^ (N - 1) := by
    obtain ⟨t, rfl⟩ : ∃ t, N = t + 1 := ⟨N - 1, by omega⟩
    rw [show t + 1 - 1 = t by omega, pow_succ]
    ring
  obtain ⟨s, hs⟩ := hdvd
  have hcancel : k = 2 * s := by
    apply mul_right_cancel₀ (by positivity : ((2 : ℤ) ^ (N - 1)) ≠ 0)
    rw [hs, hsplit]
    ring
  exact ⟨s, by rw [hcancel]; ring⟩

section Concrete

variable (D : StrothTypeData B (StrothTypeIndex.t200 m))

noncomputable def bU200 (D : StrothTypeData B (StrothTypeIndex.t200 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) : B :=
  Classical.choose (exists_conj_eq hBC hrel hdC hdB D.u (hL D.u_mem_L) D.u_mem)

noncomputable def bT200 (D : StrothTypeData B (StrothTypeIndex.t200 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) : B :=
  Classical.choose (exists_conj_eq hBC hrel hdC hdB D.t (hL D.t_mem_L) D.t_mem)

noncomputable def bR200 (D : StrothTypeData B (StrothTypeIndex.t200 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) : B :=
  Classical.choose (exists_conj_eq hBC hrel hdC hdB D.ρ (hL D.ρ_mem_L) D.ρ_mem)

noncomputable def bUV200 (D : StrothTypeData B (StrothTypeIndex.t200 m)) (hBC : B ≤ C)
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hL : D.L ≤ Subgroup.normalizer C) : B :=
  Classical.choose (exists_conj_eq hBC hrel hdC hdB D.uv (hL D.uv_mem_L) D.uv_mem)

theorem conj_eq_bU200 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    conjBy (hL D.u_mem_L) (⟨d, hdC⟩ : C) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bU200 D hBC hrel hdC hdB hL) :=
  Classical.choose_spec (exists_conj_eq hBC hrel hdC hdB D.u (hL D.u_mem_L) D.u_mem)

theorem conj_eq_bT200 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    conjBy (hL D.t_mem_L) (⟨d, hdC⟩ : C) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bT200 D hBC hrel hdC hdB hL) :=
  Classical.choose_spec (exists_conj_eq hBC hrel hdC hdB D.t (hL D.t_mem_L) D.t_mem)

theorem conj_eq_bR200 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    conjBy (hL D.ρ_mem_L) (⟨d, hdC⟩ : C) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bR200 D hBC hrel hdC hdB hL) :=
  Classical.choose_spec (exists_conj_eq hBC hrel hdC hdB D.ρ (hL D.ρ_mem_L) D.ρ_mem)

theorem conj_eq_bUV200 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    conjBy (hL D.uv_mem_L) (⟨d, hdC⟩ : C) =
      ⟨d, hdC⟩ * Subgroup.inclusion hBC (bUV200 D hBC hrel hdC hdB hL) :=
  Classical.choose_spec (exists_conj_eq hBC hrel hdC hdB D.uv (hL D.uv_mem_L) D.uv_mem)

noncomputable abbrev xU200 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    Torus (Type200.k m) := by
  simpa [StrothTypeIndex.k] using D.ec (bU200 D hBC hrel hdC hdB hL)

noncomputable abbrev yT200 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    Torus (Type200.k m) := by
  simpa [StrothTypeIndex.k] using D.ec (bT200 D hBC hrel hdC hdB hL)

noncomputable abbrev zR200 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    Torus (Type200.k m) := by
  simpa [StrothTypeIndex.k] using D.ec (bR200 D hBC hrel hdC hdB hL)

noncomputable abbrev wUV200 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    Torus (Type200.k m) := by
  simpa [StrothTypeIndex.k] using D.ec (bUV200 D hBC hrel hdC hdB hL)

theorem sq_bU200 (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2 : d * d = (D.c : S)) (hL : D.L ≤ Subgroup.normalizer C) :
    (2 : ℤ) • xU200 D hBC hrel hdC hdB hL = 0 := by
  let β : B := D.c⁻¹ * conjBy D.u_mem D.c
  have hβ : conjBy D.u_mem D.c = D.c * β := by simp [β]
  have h := sq_rel_of_type D hBC hC hrel hdC hd2 (hL D.u_mem_L) D.u_mem
    (conj_eq_bU200 D hBC hrel hdC hdB hL) hβ
  have hc : D.ec D.c = Torus.c := D.ec_c
  have hconj : D.ec (conjBy D.u_mem D.c) = Torus.c := by
    rw [StrothTypeData.ec_conj_u_t200, hc]
    simpa only [StrothTypeIndex.k, one_smul] using Type200.PhiU_c m
  have hβ0 : D.ec β = 0 := by
    dsimp only [β]
    rw [D.ec_mul, D.ec_inv, hc, hconj]
    abel
  change (2 : ℤ) • D.ec (bU200 D hBC hrel hdC hdB hL) = 0
  rw [h, hβ0]

theorem sq_bT200 (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2 : d * d = (D.c : S)) (hL : D.L ≤ Subgroup.normalizer C) :
    (2 : ℤ) • yT200 D hBC hrel hdC hdB hL = (4 : ℤ) • gen (Type200.k m) 1 := by
  let β : B := D.c⁻¹ * conjBy D.t_mem D.c
  have hβ : conjBy D.t_mem D.c = D.c * β := by simp [β]
  have h := sq_rel_of_type D hBC hC hrel hdC hd2 (hL D.t_mem_L) D.t_mem
    (conj_eq_bT200 D hBC hrel hdC hdB hL) hβ
  have hc : D.ec D.c = Torus.c := D.ec_c
  have hconj : D.ec (conjBy D.t_mem D.c) =
      (1 : ℤ) • Torus.c + (4 : ℤ) • Torus.a := by
    rw [StrothTypeData.ec_conj_t_t200, hc]
    exact Type200.PhiT_c m
  have hβ0 : D.ec β = (4 : ℤ) • gen (Type200.k m) 1 := by
    dsimp only [β]
    rw [D.ec_mul, D.ec_inv, hc, hconj]
    show (-(gen (Type200.k m) 0) +
        ((1 : ℤ) • gen (Type200.k m) 0 + (4 : ℤ) • gen (Type200.k m) 1)) =
      (4 : ℤ) • gen (Type200.k m) 1
    module
  change (2 : ℤ) • D.ec (bT200 D hBC hrel hdC hdB hL) = (4 : ℤ) • gen (Type200.k m) 1
  rw [h, hβ0]

theorem sq_bR200 (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2 : d * d = (D.c : S)) (hL : D.L ≤ Subgroup.normalizer C) :
    (2 : ℤ) • zR200 D hBC hrel hdC hdB hL = 0 := by
  let β : B := D.c⁻¹ * conjBy D.ρ_mem D.c
  have hβ : conjBy D.ρ_mem D.c = D.c * β := by simp [β]
  have h := sq_rel_of_type D hBC hC hrel hdC hd2 (hL D.ρ_mem_L) D.ρ_mem
    (conj_eq_bR200 D hBC hrel hdC hdB hL) hβ
  have hc : D.ec D.c = Torus.c := D.ec_c
  have hconj : D.ec (conjBy D.ρ_mem D.c) = Torus.c := by
    rw [StrothTypeData.ec_conj_ρ_t200, hc]
    simpa only [StrothTypeIndex.k, one_smul] using Type200.PhiR_c m
  have hβ0 : D.ec β = 0 := by
    dsimp only [β]
    rw [D.ec_mul, D.ec_inv, hc, hconj]
    abel
  change (2 : ℤ) • D.ec (bR200 D hBC hrel hdC hdB hL) = 0
  rw [h, hβ0]

theorem sq_bUV200 (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2 : d * d = (D.c : S)) (hL : D.L ≤ Subgroup.normalizer C) :
    (2 : ℤ) • wUV200 D hBC hrel hdC hdB hL =
      (-4 : ℤ) • gen (Type200.k m) 0 + (-4 : ℤ) • gen (Type200.k m) 1 +
        (-4 : ℤ) • gen (Type200.k m) 2 := by
  let β : B := D.c⁻¹ * conjBy D.uv_mem D.c
  have hβ : conjBy D.uv_mem D.c = D.c * β := by simp [β]
  have h := sq_rel_of_type D hBC hC hrel hdC hd2 (hL D.uv_mem_L) D.uv_mem
    (conj_eq_bUV200 D hBC hrel hdC hdB hL) hβ
  have hc : D.ec D.c = Torus.c := D.ec_c
  have hconj : D.ec (conjBy D.uv_mem D.c) =
      (-3 : ℤ) • Torus.c + (-4 : ℤ) • Torus.a + (-4 : ℤ) • Torus.b := by
    rw [StrothTypeData.ec_conj_uv_t200, hc]
    exact Type200.PhiUV_c m
  have hβ0 : D.ec β =
      (-4 : ℤ) • gen (Type200.k m) 0 + (-4 : ℤ) • gen (Type200.k m) 1 +
        (-4 : ℤ) • gen (Type200.k m) 2 := by
    dsimp only [β]
    rw [D.ec_mul, D.ec_inv, hc, hconj]
    show (-(gen (Type200.k m) 0) +
        ((-3 : ℤ) • gen (Type200.k m) 0 + (-4 : ℤ) • gen (Type200.k m) 1 +
          (-4 : ℤ) • gen (Type200.k m) 2)) =
      (-4 : ℤ) • gen (Type200.k m) 0 + (-4 : ℤ) • gen (Type200.k m) 1 +
        (-4 : ℤ) • gen (Type200.k m) 2
    module
  change (2 : ℤ) • D.ec (bUV200 D hBC hrel hdC hdB hL) =
    (-4 : ℤ) • gen (Type200.k m) 0 + (-4 : ℤ) • gen (Type200.k m) 1 +
      (-4 : ℤ) • gen (Type200.k m) 2
  rw [h, hβ0]

theorem phi_bU200 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    xU200 D hBC hrel hdC hdB hL + Type200.PhiU m (xU200 D hBC hrel hdC hdB hL) = 0 :=
  inv_rel_of_type D hBC hdC (hL D.u_mem_L) D.u_mem
    (conj_eq_bU200 D hBC hrel hdC hdB hL) D.u_sq (Type200.PhiU m)
    (fun x => StrothTypeData.ec_conj_u_t200 D x)

theorem phi_bT200 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    yT200 D hBC hrel hdC hdB hL + Type200.PhiT m (yT200 D hBC hrel hdC hdB hL) = 0 :=
  inv_rel_of_type D hBC hdC (hL D.t_mem_L) D.t_mem
    (conj_eq_bT200 D hBC hrel hdC hdB hL) D.t_sq (Type200.PhiT m)
    (fun x => StrothTypeData.ec_conj_t_t200 D x)

theorem phi_bR200 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    zR200 D hBC hrel hdC hdB hL + Type200.PhiR m (zR200 D hBC hrel hdC hdB hL) +
      Type200.PhiR m (Type200.PhiR m (zR200 D hBC hrel hdC hdB hL)) = 0 :=
  inv_rel_three_of_type D hBC hdC (hL D.ρ_mem_L) D.ρ_mem
    (conj_eq_bR200 D hBC hrel hdC hdB hL) D.rho_cube (Type200.PhiR m)
    (fun x => StrothTypeData.ec_conj_ρ_t200 D x)

theorem phi_bUV200 (hBC : B ≤ C) (hrel : Nat.card C = 2 * Nat.card B) {d : S}
    (hdC : d ∈ C) (hdB : d ∉ B) (hL : D.L ≤ Subgroup.normalizer C) :
    wUV200 D hBC hrel hdC hdB hL + Type200.PhiUV m (wUV200 D hBC hrel hdC hdB hL) = 0 :=
  inv_rel_of_type D hBC hdC (hL D.uv_mem_L) D.uv_mem
    (conj_eq_bUV200 D hBC hrel hdC hdB hL) D.uv_sq (Type200.PhiUV m)
    (fun x => StrothTypeData.ec_conj_uv_t200 D x)

theorem form_xU200 (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2 : d * d = (D.c : S)) (hL : D.L ≤ Subgroup.normalizer C) (hm : 1 ≤ m) :
    ∃ ε δ : ℕ, ε ≤ 1 ∧ δ ≤ 1 ∧
      xU200 D hBC hrel hdC hdB hL = ((ε : ℤ) * 2 ^ (m - 1)) • gen (Type200.k m) 0 +
        ((δ : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 1 +
          ((δ : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 2 :=
  form_bu_t200 hm (sq_bU200 D hBC hC hrel hdC hdB hd2 hL)
    (phi_bU200 D hBC hrel hdC hdB hL)

theorem form_yT200 (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2 : d * d = (D.c : S)) (hL : D.L ≤ Subgroup.normalizer C) (hm : 1 ≤ m) :
    ∃ α q : ℕ, α ≤ 1 ∧ q ≤ 1 ∧
      yT200 D hBC hrel hdC hdB hL = (0 : ℤ) • gen (Type200.k m) 0 +
        ((2 : ℤ) + (α : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 1 +
          ((q : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 2 :=
  form_bt_t200 hm (sq_bT200 D hBC hC hrel hdC hdB hd2 hL)
    (phi_bT200 D hBC hrel hdC hdB hL)

theorem form_zR200 (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2 : d * d = (D.c : S)) (hL : D.L ≤ Subgroup.normalizer C) (hm : 1 ≤ m) :
    ∃ θ η : ℕ, η ≤ 1 ∧ θ ≤ 1 ∧
      zR200 D hBC hrel hdC hdB hL = (0 : ℤ) • gen (Type200.k m) 0 +
        ((η : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 1 +
          ((θ : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 2 :=
  form_br_t200 hm (sq_bR200 D hBC hC hrel hdC hdB hd2 hL)
    (phi_bR200 D hBC hrel hdC hdB hL)

theorem form_wUV200 (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2 : d * d = (D.c : S)) (hL : D.L ≤ Subgroup.normalizer C) (hm : 1 ≤ m) :
    ∃ p r : ℕ, p ≤ 1 ∧ r ≤ 1 ∧
      wUV200 D hBC hrel hdC hdB hL = (-2 : ℤ) • gen (Type200.k m) 0 +
        ((-2 : ℤ) + (p : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 1 +
          ((-2 : ℤ) + (r : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 2 :=
  form_buv_t200 hm (sq_bUV200 D hBC hC hrel hdC hdB hd2 hL)
    (phi_bUV200 D hBC hrel hdC hdB hL)

end Concrete

theorem bit_eq_of_even_add {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1)
    (h : Even ((a : ℤ) + (b : ℤ))) : a = b := by
  obtain ⟨t, ht⟩ := h
  interval_cases a <;> interval_cases b <;> omega

theorem bit_eps_of_even {ε p r : ℕ} (hε : ε ≤ 1) (hp : p ≤ 1) (hr : r ≤ 1)
    (h : Even ((r : ℤ) - (p : ℤ) + (ε : ℤ))) : ε = (p + r) % 2 := by
  obtain ⟨t, ht⟩ := h
  interval_cases ε <;> interval_cases p <;> interval_cases r <;> omega

theorem bit_q_of_even {q p α : ℕ} (hq : q ≤ 1) (hp : p ≤ 1) (hα : α ≤ 1)
    (h : Even ((p : ℤ) + (q : ℤ) + (α : ℤ))) : q = (p + α) % 2 := by
  obtain ⟨t, ht⟩ := h
  interval_cases q <;> interval_cases p <;> interval_cases α <;> omega

section Cross200

variable (D : StrothTypeData B (StrothTypeIndex.t200 m))
variable (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
  (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
  (hd2 : d * d = (D.c : S)) (hL : D.L ≤ Subgroup.normalizer C) (hm : 1 ≤ m)

theorem bit_eps_200 (hm : 1 ≤ m) {ε δ p r : ℕ} (hε : ε ≤ 1) (hδ : δ ≤ 1)
    (hp : p ≤ 1) (hr : r ≤ 1)
    (hX : xU200 D hBC hrel hdC hdB hL =
      ((ε : ℤ) * 2 ^ (m - 1)) • gen (Type200.k m) 0 +
        ((δ : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 1 +
          ((δ : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 2)
    (hW : wUV200 D hBC hrel hdC hdB hL = (-2 : ℤ) • gen (Type200.k m) 0 +
      ((-2 : ℤ) + (p : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 1 +
        ((-2 : ℤ) + (r : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 2) :
    ε = (p + r) % 2 := by
  have h := rel_uv_comm_u_of_type D hBC hdC (hL D.u_mem_L) (hL D.uv_mem_L)
    (conj_eq_bU200 D hBC hrel hdC hdB hL) (conj_eq_bUV200 D hBC hrel hdC hdB hL)
    (Type200.PhiU m) (Type200.PhiUV m)
    (fun x => StrothTypeData.ec_conj_u_t200 D x)
    (fun x => StrothTypeData.ec_conj_uv_t200 D x)
  change xU200 D hBC hrel hdC hdB hL +
      Type200.PhiU m (wUV200 D hBC hrel hdC hdB hL) =
    wUV200 D hBC hrel hdC hdB hL +
      Type200.PhiUV m (xU200 D hBC hrel hdC hdB hL) at h
  rw [hX, hW, Type200.PhiU_apply_gens, Type200.PhiUV_apply_gens] at h
  have h1 := congrFun h 1
  simp [gen, Pi.single_apply, zsmul_eq_mul] at h1
  have hNpos : 1 ≤ Type200.k m 1 := by rw [k200_one m]; omega
  have hN1 : Type200.k m 1 - 1 = m + 1 := by rw [k200_one m]; omega
  have hcast : ((((r : ℤ) - (p : ℤ) + (ε : ℤ)) * 2 ^ (Type200.k m 1 - 1) : ℤ) :
      ZMod (2 ^ (Type200.k m 1))) = 0 := by
    rw [hN1]
    have hpow2 : (2 : ZMod (2 ^ Type200.k m 1)) ^ m * 2 = 2 ^ (m + 1) := by
      rw [← pow_succ]
    have hpow4 : (4 : ZMod (2 ^ Type200.k m 1)) * 2 ^ (m - 1) = 2 ^ (m + 1) := by
      rw [show (4 : ZMod (2 ^ Type200.k m 1)) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      rw [Nat.add_comm]
      rw [show (2 : ℕ) = 1 + 1 by norm_num, ← Nat.add_assoc, Nat.sub_add_cancel hm]
    have hpow6 : (4 : ZMod (2 ^ Type200.k m 1)) * (↑ε * 2 ^ (m - 1)) =
        ↑ε * 2 ^ (m + 1) := by
      calc
        (4 : ZMod (2 ^ Type200.k m 1)) * (↑ε * 2 ^ (m - 1)) =
            ↑ε * ((4 : ZMod (2 ^ Type200.k m 1)) * 2 ^ (m - 1)) := by ring
        _ = ↑ε * 2 ^ (m + 1) := by rw [hpow4]
    have hpow5 : (2 : ZMod (2 ^ Type200.k m 1)) * (↑δ * 2 ^ (m + 1)) = 0 := by
      calc
        (2 : ZMod (2 ^ Type200.k m 1)) * (↑δ * 2 ^ (m + 1)) =
            ↑δ * ((2 : ZMod (2 ^ Type200.k m 1)) * 2 ^ (m + 1)) := by ring
        _ = ↑δ * 2 ^ (m + 2) := by
          rw [pow_add]
          norm_num
          ring
        _ = 0 := by
          rw [show m + 2 = Type200.k m 1 by rw [k200_one m]]
          rw [show (2 : ZMod (2 ^ Type200.k m 1)) = ((2 : ℕ) : ZMod (2 ^ Type200.k m 1))
            by norm_num, ← Nat.cast_pow, ZMod.natCast_self, mul_zero]
    push_cast at h1 ⊢
    rw [hpow6, hpow5] at h1
    linear_combination h1
  have he : Even ((r : ℤ) - (p : ℤ) + (ε : ℤ)) :=
    even_of_two_pow_mul_eq_zero_zmod hNpos hcast
  exact bit_eps_of_even hε hp hr he

theorem bit_alpha_q_200 (hm : 1 ≤ m) {ε δ p r α q η θ : ℕ}
    (hα : α ≤ 1) (hq : q ≤ 1) (hp : p ≤ 1) (hr : r ≤ 1)
    (hY : yT200 D hBC hrel hdC hdB hL = (0 : ℤ) • gen (Type200.k m) 0 +
      ((2 : ℤ) + (α : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 1 +
        ((q : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 2)
    (hZ : zR200 D hBC hrel hdC hdB hL = (0 : ℤ) • gen (Type200.k m) 0 +
      ((η : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 1 +
        ((θ : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 2)
    (hW : wUV200 D hBC hrel hdC hdB hL = (-2 : ℤ) • gen (Type200.k m) 0 +
      ((-2 : ℤ) + (p : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 1 +
        ((-2 : ℤ) + (r : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 2) :
    α = r ∧ q = (p + r) % 2 := by
  have h := rel_t_rho_of_type D hBC hdC (hL D.t_mem_L) (hL D.ρ_mem_L) (hL D.uv_mem_L)
    (conj_eq_bT200 D hBC hrel hdC hdB hL) (conj_eq_bR200 D hBC hrel hdC hdB hL)
    (conj_eq_bUV200 D hBC hrel hdC hdB hL)
    (Type200.PhiT m) (Type200.PhiR m) (Type200.PhiUV m)
    (fun x => StrothTypeData.ec_conj_t_t200 D x)
    (fun x => StrothTypeData.ec_conj_ρ_t200 D x)
    (fun x => StrothTypeData.ec_conj_uv_t200 D x)
  change zR200 D hBC hrel hdC hdB hL +
      Type200.PhiR m (yT200 D hBC hrel hdC hdB hL) =
    yT200 D hBC hrel hdC hdB hL +
      Type200.PhiT m (wUV200 D hBC hrel hdC hdB hL) +
        Type200.PhiT m (Type200.PhiUV m (zR200 D hBC hrel hdC hdB hL)) at h
  rw [hY, hZ, hW, Type200.PhiR_apply_gens, Type200.PhiT_apply_gens,
    Type200.PhiUV_apply_gens, Type200.PhiT_apply_gens] at h
  have hN1 : Type200.k m 1 - 1 = m + 1 := by rw [k200_one m]; omega
  have hN2 : Type200.k m 2 - 1 = m + 1 := by rw [k200_two m]; omega
  have hNpos1 : 1 ≤ Type200.k m 1 := by rw [k200_one m]; omega
  have hNpos2 : 1 ≤ Type200.k m 2 := by rw [k200_two m]; omega
  have hpow0a : (2 : ZMod (2 ^ Type200.k m 1)) ^ m * 4 = 0 := by
    rw [show (4 : ZMod (2 ^ Type200.k m 1)) = 2 ^ 2 by norm_num, ← pow_add]
    rw [show m + 2 = Type200.k m 1 by rw [k200_one m]]
    rw [show (2 : ZMod (2 ^ Type200.k m 1)) = ((2 : ℕ) : ZMod (2 ^ Type200.k m 1))
      by norm_num, ← Nat.cast_pow, ZMod.natCast_self]
  have hpow0b : (2 : ZMod (2 ^ Type200.k m 2)) ^ m * 4 = 0 := by
    rw [show (4 : ZMod (2 ^ Type200.k m 2)) = 2 ^ 2 by norm_num, ← pow_add]
    rw [show m + 2 = Type200.k m 2 by rw [k200_two m]]
    rw [show (2 : ZMod (2 ^ Type200.k m 2)) = ((2 : ℕ) : ZMod (2 ^ Type200.k m 2))
      by norm_num, ← Nat.cast_pow, ZMod.natCast_self]
  have ha := congrFun h 1
  simp [gen, Pi.single_apply, zsmul_eq_mul] at ha
  have hcasta : ((((p : ℤ) + (q : ℤ) + (α : ℤ)) * 2 ^ (Type200.k m 1 - 1) : ℤ) :
      ZMod (2 ^ Type200.k m 1)) = 0 := by
    rw [hN1]
    push_cast at ha ⊢
    linear_combination ha + ((q : ZMod (2 ^ Type200.k m 1)) + (α : ZMod (2 ^ Type200.k m 1)) -
      (r : ZMod (2 ^ Type200.k m 1)) - (η : ZMod (2 ^ Type200.k m 1))) * hpow0a
  have hb := congrFun h 2
  simp [gen, Pi.single_apply, zsmul_eq_mul] at hb
  have hcastb : ((((r : ℤ) + (α : ℤ)) * 2 ^ (Type200.k m 2 - 1) : ℤ) :
      ZMod (2 ^ Type200.k m 2)) = 0 := by
    rw [hN2]
    push_cast at hb ⊢
    linear_combination hb + ((q : ZMod (2 ^ Type200.k m 2)) - (θ : ZMod (2 ^ Type200.k m 2)) -
      (η : ZMod (2 ^ Type200.k m 2))) * hpow0b
  have hea : Even ((p : ℤ) + (q : ℤ) + (α : ℤ)) :=
    even_of_two_pow_mul_eq_zero_zmod hNpos1 hcasta
  have heb : Even ((r : ℤ) + (α : ℤ)) :=
    even_of_two_pow_mul_eq_zero_zmod hNpos2 hcastb
  have hαr : α = r := bit_eq_of_even_add hα hr (by simpa [add_comm] using heb)
  refine ⟨hαr, ?_⟩
  have hqpa : q = (p + α) % 2 := bit_q_of_even hq hp hα hea
  rw [hαr] at hqpa
  exact hqpa

theorem bit_delta_200 (hm : 1 ≤ m) {ε δ p r η θ : ℕ}
    (hε : ε ≤ 1) (hδ : δ ≤ 1) (hη : η ≤ 1) (hθ : θ ≤ 1)
    (hX : xU200 D hBC hrel hdC hdB hL =
      ((ε : ℤ) * 2 ^ (m - 1)) • gen (Type200.k m) 0 +
        ((δ : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 1 +
          ((δ : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 2)
    (hZ : zR200 D hBC hrel hdC hdB hL = (0 : ℤ) • gen (Type200.k m) 0 +
      ((η : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 1 +
        ((θ : ℤ) * 2 ^ (m + 1)) • gen (Type200.k m) 2) :
    δ = η := by
  have h := rel_u_rho_of_type D hBC hdC (hL D.u_mem_L) (hL D.ρ_mem_L)
    (conj_eq_bU200 D hBC hrel hdC hdB hL) (conj_eq_bR200 D hBC hrel hdC hdB hL)
    (Type200.PhiU m) (Type200.PhiR m)
    (fun x => StrothTypeData.ec_conj_u_t200 D x)
    (fun x => StrothTypeData.ec_conj_ρ_t200 D x)
  change zR200 D hBC hrel hdC hdB hL +
      Type200.PhiR m (xU200 D hBC hrel hdC hdB hL) +
        Type200.PhiR m (Type200.PhiU m (zR200 D hBC hrel hdC hdB hL)) +
          Type200.PhiR m (Type200.PhiU m (Type200.PhiR m
            (xU200 D hBC hrel hdC hdB hL))) = 0 at h
  rw [hX, hZ, Type200.PhiR_apply_gens, Type200.PhiU_apply_gens,
    Type200.PhiR_apply_gens, Type200.PhiU_apply_gens, Type200.PhiR_apply_gens] at h
  have h1 := congrFun h 2
  simp [gen, Pi.single_apply, zsmul_eq_mul] at h1
  have hN2 : Type200.k m 2 - 1 = m + 1 := by rw [k200_two m]; omega
  have hNpos2 : 1 ≤ Type200.k m 2 := by rw [k200_two m]; omega
  have hpow0 : (2 : ZMod (2 ^ Type200.k m 2)) ^ m * 4 = 0 := by
    rw [show (4 : ZMod (2 ^ Type200.k m 2)) = 2 ^ 2 by norm_num, ← pow_add]
    rw [show m + 2 = Type200.k m 2 by rw [k200_two m]]
    rw [show (2 : ZMod (2 ^ Type200.k m 2)) = ((2 : ℕ) : ZMod (2 ^ Type200.k m 2))
      by norm_num, ← Nat.cast_pow, ZMod.natCast_self]
  have hpow08 : (2 : ZMod (2 ^ Type200.k m 2)) ^ m * 8 = 0 := by
    rw [show (8 : ZMod (2 ^ Type200.k m 2)) = 4 * 2 by norm_num, ← mul_assoc, hpow0, zero_mul]
  have hcast : ((((δ : ℤ) + (η : ℤ)) * 2 ^ (Type200.k m 2 - 1) : ℤ) :
      ZMod (2 ^ Type200.k m 2)) = 0 := by
    rw [hN2]
    push_cast at h1 ⊢
    linear_combination h1 + ((η : ZMod (2 ^ Type200.k m 2)) - (θ : ZMod (2 ^ Type200.k m 2))) * hpow0
  have he : Even ((δ : ℤ) + (η : ℤ)) :=
    even_of_two_pow_mul_eq_zero_zmod hNpos2 hcast
  exact bit_eq_of_even_add hδ hη he

end Cross200

end CFSG.CGT.Stroth77

end
