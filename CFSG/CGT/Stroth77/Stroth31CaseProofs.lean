module

public import CFSG.CGT.Stroth77.Stroth31Cases

public section

namespace CFSG.CGT.Stroth77

open scoped commutatorElement IsMulCommutative

variable {G : Type*} [Group G] [Finite G]

section PrintedImages

variable {D : Subgroup G} {m : ℕ}

theorem t100w_t_c (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) :
    dD.e (Additive.ofMul (conjBy dD.t_mem dD.c)) =
      (1 : ℤ) • Torus.c + (2 : ℤ) • Torus.a :=
  (dD.conj_apply dD.t_mem dD.t_conj Torus.c).trans (Type100.t_c m)

theorem t100w_t_a (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) :
    dD.e (Additive.ofMul (conjBy dD.t_mem dD.a)) = (-1 : ℤ) • Torus.a :=
  (dD.conj_apply dD.t_mem dD.t_conj Torus.a).trans (Type100.t_a m)

theorem t100w_u_a (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) :
    dD.e (Additive.ofMul (conjBy dD.u_mem dD.a)) = (1 : ℤ) • Torus.b :=
  (dD.conj_apply dD.u_mem dD.u_conj Torus.a).trans (Type100.u_a m)

@[simp] theorem e_c (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) :
    dD.e (Additive.ofMul dD.c) = Torus.c := by
  simp [StrothWeakTypeData.c]

@[simp] theorem e_a (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) :
    dD.e (Additive.ofMul dD.a) = Torus.a := by
  simp [StrothWeakTypeData.a]

@[simp] theorem e_b (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) :
    dD.e (Additive.ofMul dD.b) = Torus.b := by
  simp [StrothWeakTypeData.b]

theorem eq_of_e_eq (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) {x y : D}
    (h : dD.e (Additive.ofMul x) = dD.e (Additive.ofMul y)) : x = y := by
  have h1 : Additive.ofMul x = Additive.ofMul y := by
    simpa using congrArg dD.e.symm h
  simpa using congrArg Additive.toMul h1

theorem strothConj_mul (r x y : G) :
    strothConj r (x * y) = strothConj r x * strothConj r y := by
  simp only [strothConj]
  group

theorem strothConj_mul_eq (g h x : G) :
    strothConj (g * h) x = strothConj h (strothConj g x) := by
  simp only [strothConj]
  group

@[simp] theorem strothConj_one (r : G) : strothConj r 1 = 1 := by
  simp [strothConj]

theorem strothConj_pow (r x : G) (n : ℕ) :
    strothConj r (x ^ n) = (strothConj r x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, strothConj_mul, ih]

theorem conj_a_u (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) :
    strothConj (dD.u : G) (dD.a : G) = (dD.b : G) := by
  have h : conjBy dD.u_mem dD.a = dD.b := by
    refine eq_of_e_eq dD ?_
    rw [t100w_u_a dD]
    simp [StrothWeakTypeData.b]
  simpa [conjBy, strothConj] using congrArg (Subtype.val) h

theorem conj_c_t (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) :
    strothConj (dD.t : G) (dD.c : G) = (dD.c : G) * (dD.a : G) ^ 2 := by
  have h : conjBy dD.t_mem dD.c = dD.c * dD.a ^ 2 := by
    refine eq_of_e_eq dD ?_
    rw [t100w_t_c dD]
    have harg : Additive.ofMul (dD.c * dD.a ^ 2) =
        Additive.ofMul dD.c + (2 : ℕ) • Additive.ofMul dD.a := by
      simp
    rw [harg, map_add, map_nsmul, e_c, e_a]
    simp
  simpa [conjBy, strothConj] using congrArg (Subtype.val) h

theorem conj_a_t (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) :
    strothConj (dD.t : G) (dD.a : G) = ((dD.a : G))⁻¹ := by
  have h : conjBy dD.t_mem dD.a = dD.a⁻¹ := by
    refine eq_of_e_eq dD ?_
    rw [t100w_t_a dD]
    have harg : Additive.ofMul (dD.a⁻¹) = -(Additive.ofMul dD.a) := by
      simp
    rw [harg, map_neg, e_a]
    simp
  simpa [conjBy, strothConj] using congrArg (Subtype.val) h

end PrintedImages

section Orders

variable {D : Subgroup G} {m : ℕ}

theorem orderOf_c (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) :
    orderOf dD.c = 2 ^ m := by
  rw [StrothWeakTypeData.c, ← addOrderOf_ofMul_eq_orderOf, ofMul_toMul, AddEquiv.addOrderOf_eq,
    addOrderOf_c]
  rfl

theorem orderOf_a (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) :
    orderOf dD.a = 2 ^ (m + 1) := by
  rw [StrothWeakTypeData.a, ← addOrderOf_ofMul_eq_orderOf, ofMul_toMul, AddEquiv.addOrderOf_eq,
    addOrderOf_a]
  rfl

theorem orderOf_b (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) :
    orderOf dD.b = 2 ^ (m + 1) := by
  rw [StrothWeakTypeData.b, ← addOrderOf_ofMul_eq_orderOf, ofMul_toMul, AddEquiv.addOrderOf_eq,
    addOrderOf_b]
  rfl

end Orders

section ConjugationCalculus

variable {D : Subgroup G}

theorem strothConj_eq_of_mul_inv_mem_centralizer {D : Subgroup G} {a b : G}
    (hab : a * b⁻¹ ∈ Subgroup.centralizer (D : Set G)) {x : G} (hx : x ∈ D) :
    strothConj a x = strothConj b x := by
  have hcomm : x * (a * b⁻¹) = (a * b⁻¹) * x :=
    (Subgroup.mem_centralizer_iff.mp hab) x hx
  have h1 : strothConj (a * b⁻¹) x = x := by
    calc (a * b⁻¹)⁻¹ * x * (a * b⁻¹) = (a * b⁻¹)⁻¹ * (x * (a * b⁻¹)) := by group
      _ = (a * b⁻¹)⁻¹ * ((a * b⁻¹) * x) := by rw [hcomm]
      _ = x := by group
  have hab' : a * b⁻¹ * b = a := by group
  calc strothConj a x = strothConj (a * b⁻¹ * b) x := by rw [hab']
    _ = strothConj b (strothConj (a * b⁻¹) x) := by rw [strothConj_mul_eq]
    _ = strothConj b x := by rw [h1]

theorem strothConj_conj_commute {D : Subgroup G}
    (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) {r : G}
    (hrN : r ∈ Subgroup.normalizer (D : Set G))
    {g : G} (hg : ∃ d ∈ D, strothConj r g = d * g) {x : G} (hx : x ∈ D) :
    strothConj g (strothConj r x) = strothConj r (strothConj g x) := by
  obtain ⟨d, hdD, hd⟩ := hg
  have hd0 : r⁻¹ * g * r = d * g := hd
  have hd' : r⁻¹ * g * r * g⁻¹ = d := by rw [hd0]; group
  have h1 : r * d * r⁻¹ ∈ D := by
    have h := (Subgroup.mem_normalizer_iff''.mp (Subgroup.inv_mem _ hrN) d).mp hdD
    simpa using h
  have heq : r * d * r⁻¹ = g * r * g⁻¹ * r⁻¹ := by rw [← hd']; group
  have h2 : (r * d * r⁻¹)⁻¹ = r * g * r⁻¹ * g⁻¹ := by rw [heq]; group
  have heD : r * g * r⁻¹ * g⁻¹ ∈ D := by
    have hinv := D.inv_mem h1
    rwa [h2] at hinv
  have hcent : r * g * r⁻¹ * g⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hDc _ heD _ hy]
  have heq2 : (r * g) * (g * r)⁻¹ = r * g * r⁻¹ * g⁻¹ := by group
  have h := strothConj_eq_of_mul_inv_mem_centralizer (D := D) (a := r * g) (b := g * r)
    (by rw [heq2]; exact hcent) hx
  calc strothConj g (strothConj r x) = strothConj (r * g) x := (strothConj_mul_eq r g x).symm
    _ = strothConj (g * r) x := h
    _ = strothConj r (strothConj g x) := strothConj_mul_eq g r x

theorem mul_comm_mem_of_isMulCommutative {D : Subgroup G} [IsMulCommutative D] {x y : G}
    (hx : x ∈ D) (hy : y ∈ D) : x * y = y * x := by
  have h := mul_comm' (⟨x, hx⟩ : D) ⟨y, hy⟩
  simpa using congrArg (Subtype.val) h

theorem mem_D_of_forall_strothConj_eq_self {X : StrothAmbient G} {Z : StrothDatum X}
    {r : G} (hrS : r ∈ (X.S : Subgroup G))
    (hfix : ∀ x ∈ Z.D, strothConj r x = x) : r ∈ Z.D := by
  have hcent : r ∈ Subgroup.centralizer (Z.D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := hfix x hx
    simp only [strothConj] at h
    calc x * r = r * (r⁻¹ * x * r) := by group
      _ = r * x := by rw [h]
  have hmem : r ∈ (X.S : Subgroup G) ⊓ Subgroup.centralizer (Z.D : Set G) := ⟨hrS, hcent⟩
  simpa [Z.hcent] using hmem

end ConjugationCalculus

section Case1Reduction

variable {D : Subgroup G} {m : ℕ}

theorem strothCab_eq_mul (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) :
    strothCab dD = (dD.c : G) * strothAB dD := by
  simp [strothCab_def, strothAB_def, mul_assoc]

theorem case1_ab_fixed (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) {r : G}
    (hcab : strothConj r (strothCab dD) = strothCab dD)
    (hc : strothConj r (dD.c : G) = (dD.c : G)) :
    strothConj r (strothAB dD) = strothAB dD := by
  rw [strothCab_eq_mul] at hcab
  rw [strothConj_mul, hc] at hcab
  exact mul_left_cancel hcab

theorem case1_a_sq (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) {r : G}
    (hrN : r ∈ Subgroup.normalizer (D : Set G))
    (ht : ∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G))
    (hc : strothConj r (dD.c : G) = (dD.c : G)) :
    (strothConj r (dD.a : G)) ^ 2 = (dD.a : G) ^ 2 := by
  haveI : IsMulCommutative D := dD.isMulCommutative
  have hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x :=
    fun _ hx _ hy => mul_comm_mem_of_isMulCommutative hx hy
  have hcomm := strothConj_conj_commute (D := D) hDc hrN ht dD.c.2
  rw [hc, conj_c_t dD, strothConj_mul, hc, strothConj_pow] at hcomm
  exact (mul_left_cancel hcomm).symm

theorem strothConj_conj_commute_t (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m))
    {r : G} (hrN : r ∈ Subgroup.normalizer (D : Set G))
    (ht : ∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G)) {x : G} (hx : x ∈ D) :
    strothConj (dD.t : G) (strothConj r x) = strothConj r (strothConj (dD.t : G) x) := by
  haveI : IsMulCommutative D := dD.isMulCommutative
  exact strothConj_conj_commute (fun _ hx _ hy => mul_comm_mem_of_isMulCommutative hx hy) hrN ht hx

theorem strothConj_conj (r g x : G) :
    strothConj r (strothConj g x) = strothConj (strothConj r g) (strothConj r x) := by
  simp only [strothConj]
  group

theorem strothConj_inv (r x : G) : strothConj r x⁻¹ = (strothConj r x)⁻¹ := by
  simp only [strothConj]
  group

theorem strothConj_eq_self_of_mem_of_abelian {D : Subgroup G}
    (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) {d : G} (hd : d ∈ D) {x : G} (hx : x ∈ D) :
    strothConj d x = x := by
  have h := hDc d hd x hx
  simp only [strothConj]
  calc d⁻¹ * x * d = d⁻¹ * (x * d) := by group
    _ = d⁻¹ * (d * x) := by rw [← h]
    _ = x := by group

theorem case1_exists_involution (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) {r : G}
    (hrN : r ∈ Subgroup.normalizer (D : Set G))
    (hu : ∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G))
    (ht : ∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G))
    (hcab : strothConj r (strothCab dD) = strothCab dD)
    (hc : strothConj r (dD.c : G) = (dD.c : G)) :
    ∃ s : G, s ∈ D ∧ s * s = 1 ∧ strothConj (dD.u : G) s = s ∧
      strothConj (dD.t : G) s = s ∧
      strothConj r (dD.a : G) = (dD.a : G) * s ∧
      strothConj r (dD.b : G) = (dD.b : G) * s := by
  haveI : IsMulCommutative D := dD.isMulCommutative
  have hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x :=
    fun _ hx _ hy => mul_comm_mem_of_isMulCommutative hx hy
  obtain ⟨du, hduD, hdu⟩ := hu
  have harD : strothConj r (dD.a : G) ∈ D :=
    (Subgroup.mem_normalizer_iff''.mp hrN (dD.a : G)).mp dD.a.2
  have hsq : (strothConj r (dD.a : G)) ^ 2 = (dD.a : G) ^ 2 := case1_a_sq dD hrN ht hc
  have hab : strothConj r (strothAB dD) = strothAB dD := case1_ab_fixed dD hcab hc
  set s : G := (dD.a : G)⁻¹ * strothConj r (dD.a : G) with hs
  have hsD : s ∈ D := D.mul_mem (D.inv_mem dD.a.2) harD
  have hsval : strothConj r (dD.a : G) = (dD.a : G) * s := by rw [hs]; group
  have hss : s * s = 1 := by
    have hcomm1 : strothConj r (dD.a : G) * (dD.a : G)⁻¹ =
        (dD.a : G)⁻¹ * strothConj r (dD.a : G) :=
      mul_comm_mem_of_isMulCommutative harD (D.inv_mem dD.a.2)
    have hsq' : strothConj r (dD.a : G) * strothConj r (dD.a : G) =
        (dD.a : G) * (dD.a : G) := by
      simpa [pow_two] using hsq
    rw [hs]
    calc ((dD.a : G)⁻¹ * strothConj r (dD.a : G)) * ((dD.a : G)⁻¹ * strothConj r (dD.a : G))
        = (dD.a : G)⁻¹ * (strothConj r (dD.a : G) * (dD.a : G)⁻¹) *
            strothConj r (dD.a : G) := by group
      _ = (dD.a : G)⁻¹ * ((dD.a : G)⁻¹ * strothConj r (dD.a : G)) *
            strothConj r (dD.a : G) := by rw [hcomm1]
      _ = (dD.a : G)⁻¹ * (dD.a : G)⁻¹ *
            (strothConj r (dD.a : G) * strothConj r (dD.a : G)) := by group
      _ = (dD.a : G)⁻¹ * (dD.a : G)⁻¹ * ((dD.a : G) * (dD.a : G)) := by rw [hsq']
      _ = 1 := by group
  have hbu : strothConj r (dD.b : G) = (dD.b : G) * strothConj (dD.u : G) s := by
    have h1 : strothConj r (dD.b : G) =
        strothConj r (strothConj (dD.u : G) (dD.a : G)) := by rw [conj_a_u dD]
    rw [h1, strothConj_conj, hdu, strothConj_mul_eq,
      strothConj_eq_self_of_mem_of_abelian hDc hduD harD, hsval, strothConj_mul, conj_a_u dD]
  have hsu : strothConj (dD.u : G) s = s := by
    have h1 : ((dD.a : G) * s) * ((dD.b : G) * strothConj (dD.u : G) s) =
        (dD.a : G) * (dD.b : G) := by
      have hb : strothConj r (strothAB dD) = strothAB dD := hab
      rw [strothAB_def, strothConj_mul, hsval, hbu] at hb
      exact hb
    have hcomm_sb : s * (dD.b : G) = (dD.b : G) * s :=
      mul_comm_mem_of_isMulCommutative hsD dD.b.2
    have h2 : (dD.a : G) * (dD.b : G) * (s * strothConj (dD.u : G) s) =
        (dD.a : G) * (dD.b : G) := by
      calc (dD.a : G) * (dD.b : G) * (s * strothConj (dD.u : G) s)
          = (dD.a : G) * ((dD.b : G) * s) * strothConj (dD.u : G) s := by group
        _ = (dD.a : G) * (s * (dD.b : G)) * strothConj (dD.u : G) s := by rw [← hcomm_sb]
        _ = ((dD.a : G) * s) * ((dD.b : G) * strothConj (dD.u : G) s) := by group
        _ = (dD.a : G) * (dD.b : G) := h1
    have h3 : s * strothConj (dD.u : G) s = 1 := by
      have h2' : (dD.a : G) * (dD.b : G) * (s * strothConj (dD.u : G) s) =
          (dD.a : G) * (dD.b : G) * 1 := by rw [mul_one]; exact h2
      exact mul_left_cancel h2'
    calc strothConj (dD.u : G) s = 1 * strothConj (dD.u : G) s := (one_mul _).symm
      _ = (s * s) * strothConj (dD.u : G) s := by rw [hss]
      _ = s * (s * strothConj (dD.u : G) s) := by group
      _ = s * 1 := by rw [h3]
      _ = s := mul_one s
  have hst : strothConj (dD.t : G) s = s := by
    have hcomm := strothConj_conj_commute_t dD hrN ht dD.a.2
    rw [hsval, strothConj_mul, conj_a_t dD, strothConj_inv, hsval] at hcomm
    have hinv : ((dD.a : G) * s)⁻¹ = s * (dD.a : G)⁻¹ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hss]
    calc strothConj (dD.t : G) s =
        (dD.a : G) * ((dD.a : G)⁻¹ * strothConj (dD.t : G) s) := by group
      _ = (dD.a : G) * ((dD.a : G) * s)⁻¹ := by rw [hcomm]
      _ = (dD.a : G) * (s * (dD.a : G)⁻¹) := by rw [hinv]
      _ = s := by
          rw [show (dD.a : G) * (s * (dD.a : G)⁻¹) = ((dD.a : G) * s) * (dD.a : G)⁻¹ from by group]
          rw [mul_comm_mem_of_isMulCommutative dD.a.2 hsD]
          group
  exact ⟨s, hsD, hss, hsu, hst, hsval, by rw [hbu, hsu]⟩

theorem case1_normal_form (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) {r : G}
    (hrN : r ∈ Subgroup.normalizer (D : Set G))
    (hu : ∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G))
    (ht : ∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G))
    (hcab : strothConj r (strothCab dD) = strothCab dD)
    (hc : strothConj r (dD.c : G) = (dD.c : G))
    (hOmega : ∀ s : G, s ∈ D → s * s = 1 → strothConj (dD.u : G) s = s →
      strothConj (dD.t : G) s = s → s = 1 ∨ s = (strothAB dD) ^ (2 ^ m)) :
    (strothConj r (dD.a : G) = (dD.a : G) ∧ strothConj r (dD.b : G) = (dD.b : G)) ∨
      (strothConj r (dD.a : G) = (dD.a : G) * (strothAB dD) ^ (2 ^ m) ∧
        strothConj r (dD.b : G) = (dD.b : G) * (strothAB dD) ^ (2 ^ m)) := by
  obtain ⟨s, hsD, hss, hsu, hst, har, hbr⟩ := case1_exists_involution dD hrN hu ht hcab hc
  rcases hOmega s hsD hss hsu hst with h1 | h1
  · left
    exact ⟨by rw [har, h1, mul_one], by rw [hbr, h1, mul_one]⟩
  · right
    exact ⟨by rw [har, h1], by rw [hbr, h1]⟩

end Case1Reduction

section RemainingCases

variable {D : Subgroup G} {m : ℕ}

theorem stroth31Case1 (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) {r : G}
    (hrN : r ∈ Subgroup.normalizer (D : Set G))
    (hu : ∃ d ∈ D, strothConj r (dD.u : G) = d * (dD.u : G))
    (ht : ∃ d ∈ D, strothConj r (dD.t : G) = d * (dD.t : G))
    (hcab : strothConj r (strothCab dD) = strothCab dD)
    (hsplit : strothConj r (dD.c : G) = (dD.c : G) ∨
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m))
    (hOmega : ∀ s : G, s ∈ D → s * s = 1 → strothConj (dD.u : G) s = s →
      strothConj (dD.t : G) s = s → s = 1 ∨ s = (strothAB dD) ^ (2 ^ m))
    (hfix : strothConj r (dD.c : G) = (dD.c : G) →
      strothConj r (dD.a : G) = (dD.a : G) → strothConj r (dD.b : G) = (dD.b : G) → False)
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
  rcases hsplit with h | h
  · rcases case1_normal_form dD hrN hu ht hcab h hOmega with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact hfix h ha hb
    · exact hsub1 h ha hb
  · obtain ⟨ha, hb⟩ := hnf2 h
    exact hsub2 h ha hb

theorem stroth31Case2 {X : StrothAmbient G} {m : ℕ} {Z : StrothDatum X}
    (dD : StrothWeakTypeData Z.D (StrothTypeIndex.t100 m)) {r : G}
    (hfus : ∀ g ∈ strothR X Z.D, g⁻¹ * (dD.u : G) * g ≠
      (dD.c : G) ^ (2 ^ (m - 1)) * (dD.u : G))
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
    (hsub2 : (∀ g ∈ strothR X Z.D, g⁻¹ * (dD.u : G) * g ≠
        (dD.c : G) ^ (2 ^ (m - 1)) * (dD.u : G)) →
      strothConj r (dD.c : G) = (dD.c : G) * (strothAB dD) ^ (2 ^ m) →
      strothConj r (dD.a : G) = (dD.a : G) → strothConj r (dD.b : G) = (dD.b : G) → False) :
    False := by
  rcases hsplit with h | h
  · obtain ⟨h1, h2⟩ := hnf1 h
    exact hsub1 h h1 h2
  · obtain ⟨h1, h2⟩ := hnf2 h
    exact hsub2 hfus h h1 h2

theorem stroth31Case3 (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) {r : G}
    (hsplit : strothConj r (dD.c : G) = ((dD.c : G))⁻¹ ∨
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ * (strothAB dD) ^ (2 ^ m))
    (hsub1 : strothConj r (dD.c : G) = ((dD.c : G))⁻¹ → False)
    (hsub2 : strothConj r (dD.c : G) = ((dD.c : G))⁻¹ * (strothAB dD) ^ (2 ^ m) → False) :
    False := by
  rcases hsplit with h | h
  · exact hsub1 h
  · exact hsub2 h

theorem stroth31Case4 (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) {r : G}
    (hsplit : strothConj r (dD.c : G) = ((dD.c : G))⁻¹ ∨
      strothConj r (dD.c : G) = ((dD.c : G))⁻¹ * (strothAB dD) ^ (2 ^ m))
    (hsub1 : strothConj r (dD.c : G) = ((dD.c : G))⁻¹ → False)
    (hsub2 : strothConj r (dD.c : G) = ((dD.c : G))⁻¹ * (strothAB dD) ^ (2 ^ m) → False) :
    False := by
  rcases hsplit with h | h
  · exact hsub1 h
  · exact hsub2 h

end RemainingCases

end CFSG.CGT.Stroth77
