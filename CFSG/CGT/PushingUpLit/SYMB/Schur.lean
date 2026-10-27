module

public import CFSG.CGT.PushingUpLit.BHS6.AltCoverKernel
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS6
  CFSG.LocalAnalysis.ComponentInitial Equiv Equiv.Perm
open scoped commutatorElement

theorem hom_eq_one_of_oResidualTwo_eq_top' {H : Type*} [Group H] (h : oResidualTwo H = ⊤)
    {Q : Type*} [Group Q] (hQ : IsPGroup 2 Q) (f : H →* Q) : ∀ x, f x = 1 := by
  have hN : oResidualTwo H ≤ f.ker := by
    refine sInf_le ⟨inferInstance, ?_⟩
    exact hQ.of_injective (QuotientGroup.kerLift f) (QuotientGroup.kerLift_injective f)
  rw [h] at hN
  intro x
  exact MonoidHom.mem_ker.1 (hN (Subgroup.mem_top x))

theorem exists_order_three_lift {P M : Type*} [Group P] [Group M] (ηP : P →* M)
    (hη : Function.Surjective ηP) (hK2 : IsPGroup 2 ηP.ker) {c : M} (hc : c ^ 3 = 1) :
    ∃ y : P, ηP y = c ∧ y ^ 3 = 1 := by
  obtain ⟨y₀, hy₀⟩ := hη c
  have hy3 : y₀ ^ 3 ∈ ηP.ker := by rw [MonoidHom.mem_ker, map_pow, hy₀, hc]
  obtain ⟨e, he⟩ := hK2 ⟨y₀ ^ 3, hy3⟩
  have he' : (y₀ ^ 3) ^ (2 ^ e) = 1 := by simpa using congrArg Subtype.val he
  have h4 : 4 ^ e % 3 = 1 := by
    rw [Nat.pow_mod]
    simp
  refine ⟨y₀ ^ (4 ^ e), ?_, ?_⟩
  · rw [map_pow, hy₀]
    calc c ^ (4 ^ e) = c ^ (3 * (4 ^ e / 3) + 4 ^ e % 3) := by rw [Nat.div_add_mod]
      _ = c := by rw [pow_add, pow_mul, hc, one_pow, one_mul, h4, pow_one]
  · have h1 : y₀ ^ (3 * 2 ^ e) = 1 := by rw [pow_mul]; exact he'
    calc (y₀ ^ (4 ^ e)) ^ 3 = y₀ ^ (3 * 2 ^ e * 2 ^ e) := by
          rw [← pow_mul]
          congr 1
          rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
          ring
      _ = 1 := by rw [pow_mul, h1, one_pow]

theorem isPerfect_of_central_two_ker {H P M : Type*} [Group H] [Group P] [Group M] (π : H →* P)
    (hπ : Function.Surjective π) (hH : oResidualTwo H = ⊤) (η : P →* M)
    (hη : Function.Surjective η) (hM : commutator M = ⊤) (hK2 : IsPGroup 2 η.ker) :
    commutator P = ⊤ := by
  classical
  have hmap : (commutator P).map η = ⊤ := by
    rw [commutator, Subgroup.map_commutator, Subgroup.map_top_of_surjective η hη]
    exact hM
  have hsup : ∀ x : P, ∃ c ∈ commutator P, ∃ u ∈ η.ker, x = c * u := by
    intro x
    have hx : η x ∈ (commutator P).map η := by rw [hmap]; trivial
    obtain ⟨c, hc, hcx⟩ := hx
    refine ⟨c, hc, c⁻¹ * x, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcx]
    simp
  have hQ : IsPGroup 2 (P ⧸ commutator P) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨c, hc, u, hu, rfl⟩ := hsup x
    obtain ⟨k, hk⟩ := hK2 ⟨u, hu⟩
    refine ⟨k, ?_⟩
    have h1 : u ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff c).2 hc, one_mul, ← QuotientGroup.mk_pow,
      h1]
    rfl
  have hf := hom_eq_one_of_oResidualTwo_eq_top' hH hQ ((QuotientGroup.mk' (commutator P)).comp π)
  rw [eq_top_iff]
  intro x _
  obtain ⟨h, rfl⟩ := hπ x
  have := hf h
  simpa using this

theorem ker_le_sq_sup_of_lifts {H : Type*} [Group H] [Finite H] {n : ℕ} (hn : 5 ≤ n)
    (η : H →* alternatingGroup (Fin n)) (hη : Function.Surjective η)
    (hH : oResidualTwo H = ⊤) (hK2 : IsPGroup 2 η.ker)
    {p : Fin 4 → Fin n} (hp : Function.Injective p) {a b : H} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (haη : (η a : Perm (Fin n)) = swap (p 0) (p 2) * swap (p 0) (p 1))
    (hbη : (η b : Perm (Fin n)) = swap (p 0) (p 3) * swap (p 0) (p 1)) :
    η.ker ≤ Subgroup.zpowers ((a * b) ^ 2) ⊔ ⁅η.ker, (⊤ : Subgroup H)⁆ ∧
      ((a * b) ^ 2) ^ 2 ∈ ⁅η.ker, (⊤ : Subgroup H)⁆ := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hk3 : 3 ≤ k := by omega
  have hk0 : 0 < k := by omega
  have hk1 : 1 < k := by omega
  set N : Subgroup H := ⁅η.ker, (⊤ : Subgroup H)⁆ with hNdef
  have hNker : N ≤ η.ker := Subgroup.commutator_le_left _ _
  have hNn : N.Normal := inferInstance
  let ηP : H ⧸ N →* alternatingGroup (Fin (k + 2)) :=
    QuotientGroup.lift N η (fun x hx => hNker hx)
  have hηP : ∀ x : H, ηP (QuotientGroup.mk x) = η x := fun x => rfl
  have hηPs : Function.Surjective ηP := by
    intro y
    obtain ⟨x, hx⟩ := hη y
    exact ⟨QuotientGroup.mk x, by rw [hηP, hx]⟩
  have hker : ∀ z : H ⧸ N, z ∈ ηP.ker → ∃ x ∈ η.ker, z = QuotientGroup.mk x := by
    intro z hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    exact ⟨x, by simpa [hηP] using hz, rfl⟩
  have hKP2 : IsPGroup 2 ηP.ker := by
    intro z
    obtain ⟨x, hx, hz⟩ := hker z.1 z.2
    obtain ⟨j, hj⟩ := hK2 ⟨x, hx⟩
    refine ⟨j, Subtype.ext ?_⟩
    have h1 : x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    show z.1 ^ 2 ^ j = 1
    rw [hz, ← QuotientGroup.mk_pow, h1]
    rfl
  have hKPc : ηP.ker ≤ Subgroup.center (H ⧸ N) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hker z hz
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
    have hc : ⁅x, h⁆ ∈ N := Subgroup.commutator_mem_commutator hx (Subgroup.mem_top h)
    have h1 : (QuotientGroup.mk ⁅x, h⁆ : H ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).2 hc
    rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv] at h1
    exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)).symm
  have hperf : Group.IsPerfect (H ⧸ N) :=
    ⟨isPerfect_of_central_two_ker (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hH ηP
      hηPs (commutator_alternatingGroup_eq_top (by simpa using hn)) hKP2⟩
  let q : Fin 4 → Fin (k + 2) := fun i => ⟨i.val, by omega⟩
  have hq : Function.Injective q := fun i j h => Fin.ext (by simpa [q] using congrArg Fin.val h)
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair p q hp hq
  let cπ : alternatingGroup (Fin (k + 2)) →* alternatingGroup (Fin (k + 2)) :=
    { toFun := fun x => ⟨π * x * π⁻¹,
        (inferInstance : (alternatingGroup (Fin (k + 2))).Normal).conj_mem _ x.2 π⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hcπinj : Function.Injective cπ := fun x y h => by
    have h' := congrArg Subtype.val h
    simp only [cπ, MonoidHom.coe_mk, OneHom.coe_mk] at h'
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))
  have hcπsurj : Function.Surjective cπ := fun y => ⟨⟨π⁻¹ * y * π, by
    have := (inferInstance : (alternatingGroup (Fin (k + 2))).Normal).conj_mem _ y.2 π⁻¹
    simpa using this⟩, Subtype.ext (by simp [cπ, mul_assoc])⟩
  let ηπ : H ⧸ N →* alternatingGroup (Fin (k + 2)) := cπ.comp ηP
  have hηπs : Function.Surjective ηπ := hcπsurj.comp hηPs
  have hηπker : ηπ.ker = ηP.ker := by
    ext z
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      have h' : cπ (ηP z) = 1 := h
      exact hcπinj (h'.trans (map_one cπ).symm)
    · intro h
      show cπ (ηP z) = 1
      rw [h, map_one]
  have hKπ2 : IsPGroup 2 ηπ.ker := hηπker ▸ hKP2
  have hKπc : ηπ.ker ≤ Subgroup.center (H ⧸ N) := hηπker ▸ hKPc
  let x : Fin k → H ⧸ N := fun i =>
    if i.val = 0 then QuotientGroup.mk a
    else if i.val = 1 then QuotientGroup.mk b
    else Classical.choose (exists_order_three_lift ηπ hηπs hKπ2 (altThreeCycle_pow_three i))
  have hxspec : ∀ i : Fin k, i.val ≠ 0 → i.val ≠ 1 →
      ηπ (x i) = altThreeCycle i ∧ x i ^ 3 = 1 := fun i h0 h1 => by
    simp only [x, h0, h1, ite_false]
    exact Classical.choose_spec (exists_order_three_lift ηπ hηπs hKπ2 (altThreeCycle_pow_three i))
  have hx0 : x ⟨0, hk0⟩ = QuotientGroup.mk a := by simp [x]
  have hx1 : x ⟨1, hk1⟩ = QuotientGroup.mk b := by simp [x]
  have hq0 : q 0 = (0 : Fin (k + 2)) := Fin.ext (by simp [q])
  have hq1 : q 1 = (1 : Fin (k + 2)) := Fin.ext (by simp [q])
  have hca : ηπ (QuotientGroup.mk a) = altThreeCycle (⟨0, hk0⟩ : Fin k) := by
    apply Subtype.ext
    show π * (η a : Perm (Fin (k + 2))) * π⁻¹ = altThreeCyclePerm ⟨0, hk0⟩
    rw [haη, conj_swap_mul_swap, hπ 0, hπ 2, hπ 1, hq0, hq1]
    have : q 2 = (⟨0, hk0⟩ : Fin k).addNat 2 := Fin.ext (by simp [q])
    rw [this]
    rfl
  have hcb : ηπ (QuotientGroup.mk b) = altThreeCycle (⟨1, hk1⟩ : Fin k) := by
    apply Subtype.ext
    show π * (η b : Perm (Fin (k + 2))) * π⁻¹ = altThreeCyclePerm ⟨1, hk1⟩
    rw [hbη, conj_swap_mul_swap, hπ 0, hπ 3, hπ 1, hq0, hq1]
    have : q 3 = (⟨1, hk1⟩ : Fin k).addNat 2 := Fin.ext (by simp [q])
    rw [this]
    rfl
  have hxη : ∀ i : Fin k, ηπ (x i) = altThreeCycle i := by
    intro i
    by_cases h0 : i.val = 0
    · have hi : i = ⟨0, hk0⟩ := Fin.ext h0
      subst hi
      rw [hx0]
      exact hca
    · by_cases h1 : i.val = 1
      · have hi : i = ⟨1, hk1⟩ := Fin.ext h1
        subst hi
        rw [hx1]
        exact hcb
      · exact (hxspec i h0 h1).1
  have hx3 : ∀ i : Fin k, x i ^ 3 = 1 := by
    intro i
    by_cases h0 : i.val = 0
    · have hi : i = ⟨0, hk0⟩ := Fin.ext h0
      subst hi
      rw [hx0, ← QuotientGroup.mk_pow, ha]
      rfl
    · by_cases h1 : i.val = 1
      · have hi : i = ⟨1, hk1⟩ := Fin.ext h1
        subst hi
        rw [hx1, ← QuotientGroup.mk_pow, hb]
        rfl
      · exact (hxspec i h0 h1).2
  have hij : (⟨0, hk0⟩ : Fin k) ≠ ⟨1, hk1⟩ := by simp [Fin.ext_iff]
  have hres := ker_eq_zpowers_sq_of_alternating ηπ hηπs hKπc hKπ2 hxη hx3 (i := ⟨0, hk0⟩)
    (j := ⟨1, hk1⟩) hij
  have hy : (x ⟨0, hk0⟩ * x ⟨1, hk1⟩) ^ 2 = QuotientGroup.mk ((a * b) ^ 2) := by
    rw [hx0, hx1, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow]
  have hy2 : ((x ⟨0, hk0⟩ * x ⟨1, hk1⟩) ^ 2) ^ 2 = 1 :=
    sq_sq_lift_eq_one ηπ hKπc hKπ2 hij (hxη ⟨0, hk0⟩) (hxη ⟨1, hk1⟩) (hx3 ⟨0, hk0⟩)
      (hx3 ⟨1, hk1⟩)
  refine ⟨fun y hy' => ?_, ?_⟩
  · have hmem : (QuotientGroup.mk y : H ⧸ N) ∈ ηP.ker := by
      rw [MonoidHom.mem_ker, hηP]
      exact hy'
    rw [← hηπker, hres, hy] at hmem
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h1 : (QuotientGroup.mk (((a * b) ^ 2) ^ j) : H ⧸ N) = QuotientGroup.mk y := by
      rw [QuotientGroup.mk_zpow]
      exact hj
    have h2 : (((a * b) ^ 2) ^ j)⁻¹ * y ∈ N := QuotientGroup.eq.1 h1
    have h3 : y = ((a * b) ^ 2) ^ j * ((((a * b) ^ 2) ^ j)⁻¹ * y) := by group
    rw [h3]
    exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers _ _) h2
  · rw [hy, ← QuotientGroup.mk_pow] at hy2
    exact (QuotientGroup.eq_one_iff _).1 hy2

theorem ker_le_commutator_of_lifts {H : Type*} [Group H] [Finite H] {n : ℕ} (hn : 5 ≤ n)
    (η : H →* alternatingGroup (Fin n)) (hη : Function.Surjective η)
    (hH : oResidualTwo H = ⊤) (hK2 : IsPGroup 2 η.ker)
    {p : Fin 4 → Fin n} (hp : Function.Injective p) {a b : H} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (haη : (η a : Perm (Fin n)) = swap (p 0) (p 2) * swap (p 0) (p 1))
    (hbη : (η b : Perm (Fin n)) = swap (p 0) (p 3) * swap (p 0) (p 1))
    (hab : (a * b) ^ 2 ∈ ⁅η.ker, (⊤ : Subgroup H)⁆) :
    η.ker ≤ ⁅η.ker, (⊤ : Subgroup H)⁆ := by
  refine (ker_le_sq_sup_of_lifts hn η hη hH hK2 hp ha hb haη hbη).1.trans (sup_le ?_ le_rfl)
  exact (Subgroup.zpowers_le).2 hab

end CFSG.CGT.PushingUpLit.SYMB
