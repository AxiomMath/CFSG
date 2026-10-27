module

public import CFSG.CGT.Stroth77.Extension22Proof
public import CFSG.CGT.Stroth77.NonSplit.StrothT

public section

namespace CFSG.CGT.Stroth77

variable {G : Type*} [Group G]

@[expose]
def NoInvolutionsCentralizing (S B : Subgroup G) : Prop :=
  ∀ z : G, z ∈ S → z * z = 1 → z ∈ Subgroup.centralizer (B : Set G) → z ∈ B

theorem NoInvolutionsCentralizing.mono {S B C : Subgroup G}
    (h : NoInvolutionsCentralizing S B) (hBC : B ≤ C) :
    NoInvolutionsCentralizing S C := by
  intro z hzS hz2 hzC
  refine hBC (h z hzS hz2 ?_)
  exact (Subgroup.centralizer_le (s := (B : Set G)) (t := (C : Set G)) hBC) hzC

def IsSplitOver (B C : Subgroup G) : Prop :=
  ∃ z : G, z * z = 1 ∧ z ∉ B ∧ C = B ⊔ Subgroup.zpowers z

theorem not_isSplitOver_of_noInvolutionsCentralizing
    {S B C : Subgroup G} (hH : NoInvolutionsCentralizing S B)
    (hCS : C ≤ S) (hC : C ≤ Subgroup.centralizer (B : Set G)) :
    ¬ IsSplitOver B C := by
  rintro ⟨z, hz2, hzB, hCeq⟩
  have hzC : z ∈ C := by
    rw [hCeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  exact hzB (hH z (hCS hzC) hz2 (hC hzC))

def IsSquareInSubgroup (B : Subgroup G) (x : G) : Prop :=
  ∃ b : B, (b : G) * (b : G) = x

theorem torus_eq_zsmul_gens (k : Fin 3 → ℕ) (y : Torus k) :
    ∃ i j l : ℤ, y = i • gen k 0 + j • gen k 1 + l • gen k 2 := by
  classical
  choose i hi using fun t : Fin 3 => ZMod.intCast_surjective (y t)
  refine ⟨i 0, i 1, i 2, ?_⟩
  funext t
  fin_cases t <;> simp [gen, Pi.single_apply, hi, zsmul_eq_mul]

theorem even_of_intCast_eq_two_mul {N : ℕ} (hN : 1 ≤ N) {n : ℤ} {w : ZMod (2 ^ N)}
    (h : (n : ZMod (2 ^ N)) = 2 * w) : Even n := by
  have h2N : (2 : ℤ) ∣ (2 : ℤ) ^ N := by
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    rw [pow_succ]
    exact ⟨(2 : ℤ) ^ M, by ring⟩
  have h' : (n : ZMod (2 ^ N)) = ((2 * (w.val : ℤ) : ℤ) : ZMod (2 ^ N)) := by
    have hw : w = (w.val : ZMod (2 ^ N)) := (ZMod.natCast_zmod_val w).symm
    rw [hw] at h
    simpa [Int.cast_mul] using h
  have hdvd : (2 : ℤ) ^ N ∣ (2 * (w.val : ℤ)) - n := by
    rwa [ZMod.intCast_eq_intCast_iff_dvd_sub] at h'
  have h2sub : (2 : ℤ) ∣ (2 * (w.val : ℤ)) - n := dvd_trans h2N hdvd
  have h2mul : (2 : ℤ) ∣ 2 * (w.val : ℤ) := dvd_mul_right 2 _
  have h2n : (2 : ℤ) ∣ n := by
    have := dvd_sub h2mul h2sub
    simpa using this
  exact (even_iff_two_dvd).2 h2n

theorem isSquareInSubgroup_iff_even
    {m : ℕ} {B : Subgroup G} (D : StrothTypeData B (StrothTypeIndex.t100 m))
    {x : G} (hx : x ∈ B) :
    IsSquareInSubgroup B x ↔
      ∃ z : Torus (StrothTypeIndex.t100 m).k,
        D.e (Additive.ofMul (⟨x, hx⟩ : B)) = 2 • z := by
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
    simpa using congrArg (fun y : B => (y : G)) hb

theorem t100_square_section
    {m : ℕ} {B : Subgroup G} (D : StrothTypeData B (StrothTypeIndex.t100 m)) (x : B)
    (hu : IsSquareInSubgroup B ((conjBy D.u_mem x * x⁻¹ : B) : G))
    (hr : IsSquareInSubgroup B ((conjBy D.ρ_mem x * x⁻¹ : B) : G)) :
    ∃ i : ℤ, IsSquareInSubgroup B ((x : G) * (D.c : G) ^ (-i)) := by
  classical
  let y : Torus (StrothTypeIndex.t100 m).k := D.e (Additive.ofMul x)
  obtain ⟨i, j, k, hy⟩ := torus_eq_zsmul_gens ((StrothTypeIndex.t100 m).k) y
  have hmemu : ((conjBy D.u_mem x * x⁻¹ : B) : G) ∈ B := (conjBy D.u_mem x * x⁻¹).2
  have hmemr : ((conjBy D.ρ_mem x * x⁻¹ : B) : G) ∈ B := (conjBy D.ρ_mem x * x⁻¹).2
  obtain ⟨zu, hzu⟩ := (isSquareInSubgroup_iff_even D hmemu).1 hu
  obtain ⟨zr, hzr⟩ := (isSquareInSubgroup_iff_even D hmemr).1 hr
  have hmapu : D.e (Additive.ofMul (conjBy D.u_mem x * x⁻¹ : B)) =
      (StrothTypeIndex.t100 m).action.φu y - y := by
    rw [ofMul_mul, ofMul_inv, map_add, map_neg]
    have hc : D.e (Additive.ofMul (conjBy D.u_mem x)) =
        (StrothTypeIndex.t100 m).action.φu y := by
      simpa [y, StrothTypeIndex.action, StrothTypeIndex.k] using D.u_conj x
    rw [hc, sub_eq_add_neg]
  have hmapp : D.e (Additive.ofMul (conjBy D.ρ_mem x * x⁻¹ : B)) =
      (StrothTypeIndex.t100 m).action.φρ y - y := by
    rw [ofMul_mul, ofMul_inv, map_add, map_neg]
    have hc : D.e (Additive.ofMul (conjBy D.ρ_mem x)) =
        (StrothTypeIndex.t100 m).action.φρ y := by
      simpa [y, StrothTypeIndex.action, StrothTypeIndex.k] using D.ρ_conj x
    rw [hc, sub_eq_add_neg]
  have hzu' : (StrothTypeIndex.t100 m).action.φu y - y = 2 • zu := hmapu.symm.trans hzu
  have hzr' : (StrothTypeIndex.t100 m).action.φρ y - y = 2 • zr := hmapp.symm.trans hzr
  have hφu : (StrothTypeIndex.t100 m).action.φu y =
      i • gen (StrothTypeIndex.t100 m).k 0 + k • gen (StrothTypeIndex.t100 m).k 1 +
        j • gen (StrothTypeIndex.t100 m).k 2 := by
    rw [hy, map_add, map_add, map_zsmul, map_zsmul, map_zsmul]
    have h0 : (StrothTypeIndex.t100 m).action.φu
        (gen (StrothTypeIndex.t100 m).k 0) = gen (StrothTypeIndex.t100 m).k 0 := by
      show (Type100.action m).φu (gen (Type100.k m) 0) = gen (Type100.k m) 0
      simpa [Torus.c, one_zsmul] using Type100.u_c m
    have h1 : (StrothTypeIndex.t100 m).action.φu
        (gen (StrothTypeIndex.t100 m).k 1) = gen (StrothTypeIndex.t100 m).k 2 := by
      show (Type100.action m).φu (gen (Type100.k m) 1) = gen (Type100.k m) 2
      simpa [Torus.a, one_zsmul] using Type100.u_a m
    have h2 : (StrothTypeIndex.t100 m).action.φu
        (gen (StrothTypeIndex.t100 m).k 2) = gen (StrothTypeIndex.t100 m).k 1 := by
      show (Type100.action m).φu (gen (Type100.k m) 2) = gen (Type100.k m) 1
      simpa [Torus.b, one_zsmul] using Type100.u_b m
    rw [h0, h1, h2]
    abel
  have hy1 : y 1 = (j : ZMod (2 ^ (StrothTypeIndex.t100 m).k 1)) := by
    rw [hy]
    simp [gen, Pi.single_apply]
  have hy2 : y 2 = (k : ZMod (2 ^ (StrothTypeIndex.t100 m).k 2)) := by
    rw [hy]
    simp [gen, Pi.single_apply]
  have h1u : ((k - j : ℤ) : ZMod (2 ^ (StrothTypeIndex.t100 m).k 1)) = 2 * zu 1 := by
    have h := congrFun hzu' 1
    rw [hφu, hy] at h
    simpa [gen, Pi.single_apply, zsmul_eq_mul] using h
  have hkj : Even (k - j) :=
    even_of_intCast_eq_two_mul (N := (StrothTypeIndex.t100 m).k 1) (by simp [StrothTypeIndex.k, Type100.k]) h1u
  have hρ0 : (StrothTypeIndex.t100 m).action.φρ
      (gen (StrothTypeIndex.t100 m).k 0) = gen (StrothTypeIndex.t100 m).k 0 := by
    show (Type100.action m).φρ (gen (Type100.k m) 0) = gen (Type100.k m) 0
    simpa [Torus.c, one_zsmul] using Type100.rho_c m
  have hρ1 : (StrothTypeIndex.t100 m).action.φρ
      (gen (StrothTypeIndex.t100 m).k 1) = gen (StrothTypeIndex.t100 m).k 2 := by
    show (Type100.action m).φρ (gen (Type100.k m) 1) = gen (Type100.k m) 2
    simpa [Torus.a, one_zsmul] using Type100.rho_a m
  have hρ2 : (StrothTypeIndex.t100 m).action.φρ
      (gen (StrothTypeIndex.t100 m).k 2) =
      (-2 : ℤ) • gen (StrothTypeIndex.t100 m).k 0 +
        (-1 : ℤ) • gen (StrothTypeIndex.t100 m).k 1 +
        (-1 : ℤ) • gen (StrothTypeIndex.t100 m).k 2 := by
    show (Type100.action m).φρ (gen (Type100.k m) 2) =
      (-2 : ℤ) • gen (Type100.k m) 0 + (-1 : ℤ) • gen (Type100.k m) 1 +
        (-1 : ℤ) • gen (Type100.k m) 2
    simpa only [Torus.c, Torus.a, Torus.b] using Type100.rho_b m
  have hφρ1 : ((StrothTypeIndex.t100 m).action.φρ y) 1 =
      -(k : ZMod (2 ^ (StrothTypeIndex.t100 m).k 1)) := by
    rw [hy, map_add, map_add, map_zsmul, map_zsmul, map_zsmul]
    rw [hρ0, hρ1, hρ2]
    simp [gen, Pi.single_apply, zsmul_eq_mul]
  have hφρ2 : ((StrothTypeIndex.t100 m).action.φρ y) 2 =
      (j : ZMod (2 ^ (StrothTypeIndex.t100 m).k 2)) - (k : ZMod (2 ^ (StrothTypeIndex.t100 m).k 2)) := by
    rw [hy, map_add, map_add, map_zsmul, map_zsmul, map_zsmul]
    rw [hρ0, hρ1, hρ2]
    simp [gen, Pi.single_apply, zsmul_eq_mul]
    ring
  have h2r : ((j - 2 * k : ℤ) : ZMod (2 ^ (StrothTypeIndex.t100 m).k 2)) = 2 * zr 2 := by
    have h := congrFun hzr' 2
    simp only [Pi.sub_apply] at h
    rw [hφρ2, hy2] at h
    simp only [Pi.smul_apply, zsmul_eq_mul] at h
    convert h using 2 <;> push_cast <;> ring
  have hj2k : Even (j - 2 * k) :=
    even_of_intCast_eq_two_mul (N := (StrothTypeIndex.t100 m).k 2) (by simp [StrothTypeIndex.k, Type100.k]) h2r
  have h1r : ((-(k + j) : ℤ) : ZMod (2 ^ (StrothTypeIndex.t100 m).k 1)) = 2 * zr 1 := by
    have h := congrFun hzr' 1
    simp only [Pi.sub_apply] at h
    rw [hφρ1, hy1] at h
    simp only [Pi.smul_apply, zsmul_eq_mul] at h
    push_cast
    ring_nf at h ⊢
    exact h
  have hkjsum : Even (k + j) := by
    have hneg : Even (-(k + j)) :=
      even_of_intCast_eq_two_mul (N := (StrothTypeIndex.t100 m).k 1) (by simp [StrothTypeIndex.k, Type100.k]) h1r
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
  have hxsplit : y - i • gen (StrothTypeIndex.t100 m).k 0 =
      2 • (j' • gen (StrothTypeIndex.t100 m).k 1 +
        k' • gen (StrothTypeIndex.t100 m).k 2) := by
    rw [hy, hj2, hk2, mul_zsmul, mul_zsmul]
    simp only [smul_add]
    abel
  have hmem : (x : G) * (D.c : G) ^ (-i) ∈ B :=
    B.mul_mem x.2 (B.zpow_mem D.c.2 _)
  refine ⟨i, (isSquareInSubgroup_iff_even D hmem).2 ?_⟩
  refine ⟨j' • gen (StrothTypeIndex.t100 m).k 1 +
    k' • gen (StrothTypeIndex.t100 m).k 2, ?_⟩
  have hcgen : D.e (Additive.ofMul D.c) = gen (StrothTypeIndex.t100 m).k 0 := by
    simp [StrothTypeData.c, Torus.c, gen]
  have hxci : D.e (Additive.ofMul (x * D.c ^ (-i))) =
      y - i • gen (StrothTypeIndex.t100 m).k 0 := by
    rw [ofMul_mul, ofMul_zpow, map_add, map_zsmul, hcgen]
    rw [show D.e (Additive.ofMul x) = y from rfl, sub_eq_add_neg, neg_zsmul]
  have hsub : (⟨(x : G) * (D.c : G) ^ (-i), hmem⟩ : B) = x * D.c ^ (-i) := rfl
  rw [hsub]
  exact hxci.trans hxsplit


theorem isSquareInSubgroup_mul
    [Finite G] {m : ℕ} {B : Subgroup G} (D : StrothTypeData B (StrothTypeIndex.t100 m))
    {x y : G} (hx : IsSquareInSubgroup B x) (hy : IsSquareInSubgroup B y) :
    IsSquareInSubgroup B (x * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨⟨a * b, B.mul_mem a.2 b.2⟩, ?_⟩
  have hab : (a : G) * b = b * a :=
    congrArg (fun z : B => (z : G)) (D.comm_t100 a b)
  change (a : G) * b * ((a : G) * b) = x * y
  calc
    (a : G) * b * ((a : G) * b) = (a : G) * (b * a) * b := by group
    _ = (a : G) * (a * b) * b := by rw [← hab]
    _ = ((a : G) * a) * (b * b) := by group
    _ = x * y := by rw [ha, hb]

theorem isSquareInSubgroup_zpow_of_even
    {m : ℕ} {B : Subgroup G} (D : StrothTypeData B (StrothTypeIndex.t100 m))
    {i : ℤ} (hi : Even i) :
    IsSquareInSubgroup B ((D.c : G) ^ i) := by
  obtain ⟨k, rfl⟩ := hi
  refine ⟨⟨D.c ^ k, B.zpow_mem D.c.2 k⟩, ?_⟩
  change (D.c : G) ^ k * (D.c : G) ^ k = (D.c : G) ^ (k + k)
  rw [← zpow_add]

section MnsModel


theorem mns_centralizer_Ag_eq : Subgroup.centralizer (Ag : Set Mns) = Ag := by
  apply le_antisymm
  · intro z hz
    have hzN : z ∈ NAg := Subgroup.centralizer_le_normalizer (Ag : Set Mns) hz
    have hnorm : normB z = true := (mem_normalizer_iff_normB (g := z)).1 hzN
    obtain ⟨l, hl, hal⟩ := normB_decomp z hnorm
    have hz_eq : z = (z * l⁻¹) * l := by group
    have hz' : (z * l⁻¹) * l ∈ Subgroup.centralizer (Ag : Set Mns) := by
      rw [hz_eq] at hz
      exact hz
    have hcheck : (bfsList gensL 40).all (fun l =>
        (gensA.all fun a => decide (l * a = a * l)) → decide (l = 1)) = true := by
      decide
    have hcheck' : ∀ l ∈ bfsList gensL 40,
        (∀ a ∈ gensA, l * a = a * l) → l = 1 := by
      intro l hl hcomm
      have h := List.all_eq_true.mp hcheck l hl
      have hg : (gensA.all fun a => decide (l * a = a * l)) = true := by
        apply List.all_eq_true.mpr
        intro a ha
        exact decide_eq_true (hcomm a ha)
      simp [hg] at h
      exact h
    have ha : z * l⁻¹ ∈ Ag := mem_Ag.2 hal
    have ha_cent : z * l⁻¹ ∈ Subgroup.centralizer (Ag : Set Mns) :=
      (Subgroup.le_centralizer_iff_isMulCommutative (K := Ag)).mpr Ag_commutative ha
    have hl_cent : l ∈ Subgroup.centralizer (Ag : Set Mns) := by
      have h1 : (z * l⁻¹)⁻¹ ∈ Subgroup.centralizer (Ag : Set Mns) := Subgroup.inv_mem _ ha_cent
      have h2 : (z * l⁻¹)⁻¹ * ((z * l⁻¹) * l) ∈ Subgroup.centralizer (Ag : Set Mns) :=
        Subgroup.mul_mem _ h1 hz'
      simpa [mul_assoc] using h2
    have hl1 : l = 1 := by
      exact hcheck' l hl (fun a ha' => by
        exact ((Subgroup.mem_centralizer_iff.mp hl_cent) a (Subgroup.subset_closure ha')).symm)
    rw [hz_eq]
    simpa [hl1] using ha
  · exact (Subgroup.le_centralizer_iff_isMulCommutative (K := Ag)).mpr Ag_commutative

theorem mns_noInvolutionsCentralizing_Ag : NoInvolutionsCentralizing Tg Ag := by
  intro z _ hz2 hz
  rw [mns_centralizer_Ag_eq] at hz
  exact hz

end MnsModel


theorem exists_square_root_c
    [Finite G] {m : ℕ} {B C S : Subgroup G}
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set G))
    (hrel : Nat.card C = 2 * Nat.card B)
    (huC : D.u ∈ Subgroup.normalizer C) (hρC : D.ρ ∈ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S B) (hCS : C ≤ S) (hne : C ≠ B) :
    ∃ d : G, d ∈ C ∧ d ∉ B ∧ d * d = (D.c : G) := by
  classical
  letI : CommGroup C :=
    { (inferInstance : Group C) with mul_comm := comm_of_le_centralizer D hBC hC hrel }
  have hlt : B < C := lt_of_le_of_ne hBC hne.symm
  obtain ⟨d, hdC, hdB⟩ := SetLike.exists_of_lt hlt
  have hindex : (B.subgroupOf C).index = 2 := index_two_of_relIndex hBC hrel
  let dC : C := ⟨d, hdC⟩
  have hd2B : d * d ∈ B := by
    have h := sq_mem_of_index_two (B := B) (C := C) (x := dC) hindex
    simpa [dC] using h
  let xB : B := ⟨d * d, hd2B⟩
  have hnotsquare : ¬ IsSquareInSubgroup B (d * d) := by
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
        _ = (dC * dC) * (bC * bC)⁻¹ := by rw [mul_inv_rev]
        _ = 1 := by rw [hb2C]; group
    have hz2 : (zC : G) * (zC : G) = 1 := by
      simpa using congrArg (fun z : C => (z : G)) hz2C
    have hzC : (zC : G) ∈ C := zC.2
    have hzB : (zC : G) ∉ B := by
      intro hz
      have hd_eq : dC = zC * bC := by
        simp [zC, dC, bC]
      have hmem : dC ∈ B.subgroupOf C := by
        rw [hd_eq]
        exact (B.subgroupOf C).mul_mem (by simpa [Subgroup.mem_subgroupOf] using hz)
          (by simpa [Subgroup.mem_subgroupOf, bC] using b.2)
      exact hdB (by simpa [Subgroup.mem_subgroupOf] using hmem)
    exact hzB (hH (zC : G) (hCS hzC) hz2 (hC hzC))
  have square_conj (g : G) (hgB : g ∈ Subgroup.normalizer B)
      (hgC : g ∈ Subgroup.normalizer C) :
      IsSquareInSubgroup B ((conjBy hgB xB * xB⁻¹ : B) : G) := by
    have hconjC : g⁻¹ * d * g ∈ C :=
      (Subgroup.mem_normalizer_iff''.mp hgC d).mp hdC
    have hconjB : g⁻¹ * d * g ∉ B := by
      intro hconj
      exact hdB ((Subgroup.mem_normalizer_iff''.mp hgB d).mpr hconj)
    rcases mem_or_exists_mul_of_index_two hdC hdB hindex hconjC with hconjBinB | ⟨b, hbB, hb_eq⟩
    · exact (hconjB hconjBinB).elim
    let bB : B := ⟨b, hbB⟩
    let bC : C := ⟨b, hBC hbB⟩
    let xC : C := ⟨(xB : G), hBC xB.2⟩
    have hxC : xC = dC * dC := by
      apply Subtype.ext
      simp [xC, dC, xB]
    have hconj_eq : conjBy hgC dC = dC * bC := by
      apply Subtype.ext
      change g⁻¹ * d * g = d * b
      exact hb_eq
    refine ⟨bB, ?_⟩
    have hcoerce : ((conjBy hgB xB * xB⁻¹ : B) : G) =
        ((conjBy hgC xC * xC⁻¹ : C) : G) := rfl
    rw [hcoerce]
    change (bC : G) * (bC : G) = ((conjBy hgC xC * xC⁻¹ : C) : G)
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
    exact (congrArg (fun z : C => (z : G)) hCeq).symm
  have hu : IsSquareInSubgroup B ((conjBy D.u_mem xB * xB⁻¹ : B) : G) :=
    square_conj D.u D.u_mem huC
  have hr : IsSquareInSubgroup B ((conjBy D.ρ_mem xB * xB⁻¹ : B) : G) :=
    square_conj D.ρ D.ρ_mem hρC
  obtain ⟨i, hi⟩ := t100_square_section D xB hu hr
  have hx : (xB : G) = d * d := rfl
  rw [hx] at hi
  by_cases heven : Even i
  · have hci := isSquareInSubgroup_zpow_of_even D heven
    have hx_sq : IsSquareInSubgroup B (d * d) := by
      have hmul := isSquareInSubgroup_mul D hi hci
      convert hmul using 1
      group
    exact (hnotsquare hx_sq).elim
  · have hodd : Odd i := by simpa using heven
    obtain ⟨t, ht⟩ := hodd
    have hi1 : Even (i - (1 : ℤ)) := ⟨t, by rw [ht]; ring⟩
    have hci1 := isSquareInSubgroup_zpow_of_even D hi1
    have hxci : IsSquareInSubgroup B ((d * d) * (D.c : G) ^ (-1 : ℤ)) := by
      have hmul := isSquareInSubgroup_mul D hi hci1
      have hEq : (d * d) * (D.c : G) ^ (-i) * (D.c : G) ^ (i - 1) =
          (d * d) * (D.c : G) ^ (-1 : ℤ) := by
        rw [mul_assoc, ← zpow_add]
        rw [show -i + (i - 1) = (-1 : ℤ) by ring]
      rwa [hEq] at hmul
    obtain ⟨s, hs2⟩ := hxci
    refine ⟨d * (s : G)⁻¹, C.mul_mem hdC (C.inv_mem (hBC s.2)), ?_, ?_⟩
    · intro hd'B
      apply hdB
      have hd_eq : d = (d * (s : G)⁻¹) * (s : G) := by group
      rw [hd_eq]
      exact B.mul_mem hd'B s.2
    · let sC : C := ⟨s, hBC s.2⟩
      let cC : C := ⟨(D.c : G), hBC D.c.2⟩
      have hs2C : sC * sC = dC * dC * cC⁻¹ := by
        apply Subtype.ext
        simpa [sC, dC, cC] using hs2
      let d'C : C := dC * sC⁻¹
      have hd'C : d'C * d'C = cC := by
        calc
          d'C * d'C = (dC * dC) * (sC * sC)⁻¹ := by
            simp only [d'C]
            rw [mul_mul_mul_comm, mul_inv_rev]
          _ = (dC * dC) * (dC * dC * cC⁻¹)⁻¹ := by rw [hs2C]
          _ = cC := by
            rw [mul_inv_rev, inv_inv, ← mul_assoc, mul_comm (dC * dC) cC]
            group
      have := congrArg (fun z : C => (z : G)) hd'C
      simpa [d'C, dC, sC, cC] using this


theorem exists_square_root_c_of_hasStrothType
    [Finite G] {m : ℕ} {B C S : Subgroup G}
    (hB : HasStrothType B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set G))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S B) (hCS : C ≤ S) (hne : C ≠ B) :
    ∃ d : G, d ∈ C ∧ d ∉ B ∧ d * d = (hB.data.c : G) :=
  exists_square_root_c hB.data hBC hC hrel (hL hB.data.u_mem_L) (hL hB.data.ρ_mem_L)
    hH hCS hne

end CFSG.CGT.Stroth77
