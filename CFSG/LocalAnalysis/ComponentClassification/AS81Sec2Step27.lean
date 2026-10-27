module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Kernel
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

namespace Sec2

section Lift

variable {A B : Type*} [Group A] [Group B] [Finite A] (φ : A →* B)

theorem exists_sq_eq_one_map_eq (hodd : Odd (Nat.card φ.ker)) {a : A} (ha : φ a ^ 2 = 1) :
    ∃ b : A, b ^ 2 = 1 ∧ φ b = φ a := by
  obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos a).ne'
  refine ⟨a ^ m, ?_, ?_⟩
  · have h1 : (a ^ m) ^ 2 ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_pow, map_pow, ← pow_mul, mul_comm, pow_mul, ha, one_pow]
    have h2 : ((a ^ m) ^ 2) ^ 2 ^ e = 1 := by
      rw [← pow_mul, ← pow_mul, show m * (2 * 2 ^ e) = 2 ^ e * m * 2 by ring, pow_mul, ← he,
        pow_orderOf_eq_one, one_pow]
    have hcop : Nat.Coprime (orderOf ((a ^ m) ^ 2)) (Nat.card φ.ker) :=
      Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h2)
        (Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hodd))
    exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd (Subgroup.orderOf_dvd_natCard _ h1))
  · obtain ⟨j, rfl⟩ := hm
    rw [map_pow, pow_succ, pow_mul, ha, one_pow, one_mul]

omit [Finite A] in
theorem orderOf_mul_eq_three (hker : φ.ker ≤ center A) (hodd : Odd (Nat.card φ.ker)) {a b : A}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (h3 : φ (a * b) ^ 3 = 1) (h1 : φ (a * b) ≠ 1) :
    orderOf (a * b) = 3 := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq, ha])
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq, hb])
  have hinv : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [mul_inv_rev, ha', hb', ← mul_assoc, ← sq, ha, one_mul]
  have hk : (a * b) ^ 3 ∈ φ.ker := by rw [MonoidHom.mem_ker, map_pow, h3]
  have hc : a * (a * b) ^ 3 * a⁻¹ = (a * b) ^ 3 := by
    rw [mem_center_iff.mp (hker hk) a, mul_inv_cancel_right]
  have h2 : ((a * b) ^ 3) ^ 2 = 1 := by
    have h' : a * (a * b) ^ 3 * a⁻¹ = ((a * b) ^ 3)⁻¹ := by rw [← conj_pow, hinv, inv_pow]
    rw [h'] at hc
    rw [sq]
    nth_rewrite 1 [← hc]
    exact inv_mul_cancel _
  have hcop : Nat.Coprime (orderOf ((a * b) ^ 3)) (Nat.card φ.ker) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h2) (Nat.coprime_two_left.mpr hodd)
  have h6 : (a * b) ^ 3 = 1 :=
    orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd (Subgroup.orderOf_dvd_natCard _ hk))
  exact orderOf_eq_prime h6 fun h => h1 (by rw [h, map_one])

end Lift

theorem exists_mem_commute_of_pow_three {S : Subgroup G} (hS : IsPGroup 2 S) {u h : G}
    (hu : u ^ 3 = 1) (huS : u ∈ normalizer (S : Set G)) (hh : h⁻¹ * u * h * u⁻¹ ∈ S) :
    ∃ s ∈ S, u * (h * s) = h * s * u := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype ↥S := Fintype.ofFinite _
  have hu' : u * u * u = 1 := by rw [← hu, pow_three, mul_assoc]
  have hmem : ∀ s ∈ S, h⁻¹ * u * h * s * u⁻¹ ∈ S := fun s hs => by
    have e : h⁻¹ * u * h * s * u⁻¹ = (h⁻¹ * u * h * u⁻¹) * (u * s * u⁻¹) := by group
    rw [e]
    exact S.mul_mem hh ((mem_normalizer_iff.mp huS s).mp hs)
  let f : ↥S → ↥S := fun s => ⟨h⁻¹ * u * h * s * u⁻¹, hmem s s.2⟩
  have hf3 : ∀ s, f (f (f s)) = s := fun s => Subtype.ext (by
    show h⁻¹ * u * h * (h⁻¹ * u * h * (h⁻¹ * u * h * (s : G) * u⁻¹) * u⁻¹) * u⁻¹ = s
    calc _ = h⁻¹ * (u * u * u) * h * (s : G) * (u * u * u)⁻¹ := by group
      _ = s := by rw [hu']; group)
  let σ : Equiv.Perm ↥S := ⟨f, fun s => f (f s), hf3, hf3⟩
  have hσ : σ ^ 3 ^ 1 = 1 := Equiv.ext fun s => by
    rw [pow_one, pow_three]
    exact hf3 s
  have hcard : ¬ 3 ∣ Fintype.card ↥S := by
    obtain ⟨n, hn⟩ := hS.exists_card_eq
    rw [← Nat.card_eq_fintype_card, hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  obtain ⟨s, hs⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
  refine ⟨s, s.2, ?_⟩
  have h1 : h⁻¹ * u * h * (s : G) * u⁻¹ = s := congrArg Subtype.val hs
  calc u * (h * s) = h * (h⁻¹ * u * h * (s : G) * u⁻¹) * u := by group
    _ = h * s * u := by rw [h1]

section Model

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open LinearFlag Matrix CFSG.LieType.Chevalley

variable {k : Type} [Field k]

theorem leviOne_torusSL2_mul_unipU {t : k} (ht : t ≠ 0) (b c : k) :
    leviOne k (torusSL2 ht) * unipU k 0 b c = unipU k 0 (t * t * b) (t * c) *
      leviOne k (torusSL2 ht) := by
  apply Subtype.ext
  change (leviOne k (torusSL2 ht) : Matrix (Fin 3) (Fin 3) k) * (unipU k 0 b c : Matrix _ _ k) =
    (unipU k 0 (t * t * b) (t * c) : Matrix _ _ k) * (leviOne k (torusSL2 ht) : Matrix _ _ k)
  rw [coe_leviOne, coe_unipU, coe_unipU, coe_torusSL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp

theorem exists_sq_eq_one_mul_torus [Finite k] (hk : Nat.card k = 4) :
    ∃ a b : projectiveSL 3 k, a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ (a * b) ^ 3 = 1 ∧
      a * b ∈ normalizer (projRad k 0 : Set (projectiveSL 3 k)) ∧
      a * b ∈ normalizer (projRad k 1 : Set (projectiveSL 3 k)) ∧
      ∀ i : Fin 2, ∃ w ∈ projRad k i, a * b * w * (a * b)⁻¹ ≠ w := by
  have h2 := two_eq_zero_of_card hk
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one_of_card hk
  have ht3 : t ^ 3 = 1 := by
    have : Fintype k := Fintype.ofFinite k
    have h := FiniteField.pow_card_sub_one_eq_one t ht0
    rwa [← Nat.card_eq_fintype_card, hk] at h
  have ht3' : t * t * t = 1 := by rw [← ht3]; ring
  have ht3'' : t⁻¹ * t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv, ← mul_inv, ht3', inv_one]
  let s₁ : SL2 k := ⟨!![0, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : k) * h2⟩
  let s₂ : SL2 k := ⟨!![0, t⁻¹; t, 0], by
    rw [Matrix.det_fin_two_of, inv_mul_cancel₀ ht0]
    linear_combination (-1 : k) * h2⟩
  have hc₁ : (s₁ : Matrix (Fin 2) (Fin 2) k) = !![0, 1; 1, 0] := rfl
  have hc₂ : (s₂ : Matrix (Fin 2) (Fin 2) k) = !![0, t⁻¹; t, 0] := rfl
  have hs₁ : s₁ * s₁ = 1 := SL2_ext
    (by simp [hc₁, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [hc₁, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [hc₁, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [hc₁, Matrix.mul_apply, Fin.sum_univ_two])
  have hs₂ : s₂ * s₂ = 1 := SL2_ext
    (by simp [hc₂, Matrix.mul_apply, Fin.sum_univ_two, ht0])
    (by simp [hc₂, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [hc₂, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [hc₂, Matrix.mul_apply, Fin.sum_univ_two, ht0])
  have hs : s₁ * s₂ = torusSL2 ht0 := SL2_ext
    (by simp [hc₁, hc₂, coe_torusSL2, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [hc₁, hc₂, coe_torusSL2, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [hc₁, hc₂, coe_torusSL2, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [hc₁, hc₂, coe_torusSL2, Matrix.mul_apply, Fin.sum_univ_two])
  have hd3 : torusSL2 ht0 ^ 3 = 1 := SL2_ext
    (by simp [pow_succ, coe_torusSL2, Matrix.mul_apply, Fin.sum_univ_two, ht3'])
    (by simp [pow_succ, coe_torusSL2, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [pow_succ, coe_torusSL2, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [pow_succ, coe_torusSL2, Matrix.mul_apply, Fin.sum_univ_two, ht3''])
  have hab : proj 3 k (levi k 0 s₁) * proj 3 k (levi k 0 s₂) =
      proj 3 k (levi k 0 (torusSL2 ht0)) := by
    rw [← map_mul, ← map_mul, hs]
  refine ⟨proj 3 k (levi k 0 s₁), proj 3 k (levi k 0 s₂), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, ← map_pow, sq, hs₁, map_one, map_one]
  · rw [← map_pow, ← map_pow, sq, hs₂, map_one, map_one]
  · rw [hab, ← map_pow, ← map_pow, hd3, map_one, map_one]
  · rw [hab]
    exact leviOne_mem_normalizer _
  · rw [hab, levi_zero]
    have hconj : ∀ (s : k) (hs : s ≠ 0), ∀ x ∈ projRad k 1,
        proj 3 k (leviOne k (torusSL2 hs)) * x * (proj 3 k (leviOne k (torusSL2 hs)))⁻¹ ∈
          projRad k 1 := by
      intro s hs x hx
      obtain ⟨b, c, rfl⟩ := mem_projRad_one.1 hx
      rw [← map_inv, ← map_mul, ← map_mul,
        mul_inv_eq_iff_eq_mul.2 (leviOne_torusSL2_mul_unipU hs b c)]
      exact mem_projRad_one.2 ⟨_, _, rfl⟩
    have hinv : (proj 3 k (leviOne k (torusSL2 ht0)))⁻¹ =
        proj 3 k (leviOne k (torusSL2 (inv_ne_zero ht0))) := by
      rw [← map_inv, ← map_inv]
      congr 2
      rw [eq_comm, eq_inv_iff_mul_eq_one]
      exact SL2_ext (by simp [coe_torusSL2, Matrix.mul_apply, Fin.sum_univ_two, ht0])
        (by simp [coe_torusSL2, Matrix.mul_apply, Fin.sum_univ_two])
        (by simp [coe_torusSL2, Matrix.mul_apply, Fin.sum_univ_two])
        (by simp [coe_torusSL2, Matrix.mul_apply, Fin.sum_univ_two, ht0])
    refine mem_normalizer_of_conj_mem (hconj t ht0) fun x hx => ?_
    have := hconj _ (inv_ne_zero ht0) x hx
    rwa [← hinv, inv_inv] at this
  · intro i
    have hw : proj 3 k (unipU k 0 0 1) ∈ projRad k i := by
      fin_cases i
      · exact mem_projRad_zero.2 ⟨0, 1, rfl⟩
      · exact mem_projRad_one.2 ⟨0, 1, rfl⟩
    refine ⟨_, hw, fun h => ht1 ?_⟩
    rw [hab, levi_torus_conj] at h
    have := (unipU_eq_of_proj_eq h).2.2
    rwa [mul_one] at this

end Model

end Sec2

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem eq_one_of_conj_eq_of_orderOf_eq_three (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) {u : G} (huA : u ∈ A)
    (hu3 : orderOf u = 3) (huE : ∃ e ∈ E, u⁻¹ * e * u ≠ e) {w : G} (hw : w ∈ sec2Z A E F)
    (huw : u * w * u⁻¹ = w) : w = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hw1
  have hq := hF.quasisimple
  obtain ⟨c⟩ := nonempty_l34Cover_of_odd hq hL hodd
  have hNZ := oddCore_le_center hq.1 hq.2
  have hwA : w ∈ A := hw.1
  have hZE : sec2Z A E F ≤ E := by rw [hF.sec2Z_eq]; exact inf_le_left.trans inf_le_left
  have hw2 : w ^ 2 = 1 := hF.elemE.2 w (hZE hw)
  obtain ⟨T, hT, hwT⟩ := exists_isSylowOf_mem_centerIn c hwA hw2 hw1
  have hwK : w ∉ centralizer (A : Set G) := fun h => by
    have h1 := inf_eq_bot_of_odd_center (zpowers_le.mpr h)
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hw2 hw1, pow_one]))
      hodd
    have h2 : w ∈ zpowers w ⊓ A := ⟨mem_zpowers w, hwA⟩
    rw [h1, mem_bot] at h2
    exact hw1 h2
  have huw' : u * w = w * u := by
    calc u * w = u * w * u⁻¹ * u := by group
      _ = w * u := by rw [huw]
  have hu := mem_sup_centralizer_of_commute c hNZ hT hwT hwK huA huw'
  have hKT : centralizer (A : Set G) ≤ normalizer (T : Set G) := fun k hk =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun t ht =>
      (mem_centralizer_iff.mp hk t (hT.le ht)))
  have hu' : u ∈ ((T ⊔ centralizer (A : Set G) : Subgroup G) : Set G) := hu
  rw [coe_mul_of_right_le_normalizer_left T _ hKT] at hu'
  obtain ⟨t, htT, k, hk, rfl⟩ := hu'
  have htA : t ∈ A := hT.le htT
  have hconj : ∀ a ∈ A, t * k * a * (t * k)⁻¹ = t * a * t⁻¹ := fun a ha => by
    have hka : a * k = k * a := mem_centralizer_iff.mp hk a ha
    calc t * k * a * (t * k)⁻¹ = t * (k * a) * k⁻¹ * t⁻¹ := by group
      _ = t * (a * k) * k⁻¹ * t⁻¹ := by rw [hka]
      _ = t * a * t⁻¹ := by group
  have hpow : ∀ j : ℕ, ∀ a ∈ A, (t * k) ^ j * a * ((t * k) ^ j)⁻¹ = t ^ j * a * (t ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro a _; simp
    | succ j ih =>
      intro a ha
      have hta : t * a * t⁻¹ ∈ A := A.mul_mem (A.mul_mem htA ha) (A.inv_mem htA)
      calc (t * k) ^ (j + 1) * a * ((t * k) ^ (j + 1))⁻¹
          = (t * k) ^ j * (t * k * a * (t * k)⁻¹) * ((t * k) ^ j)⁻¹ := by
            rw [pow_succ]; group
        _ = (t * k) ^ j * (t * a * t⁻¹) * ((t * k) ^ j)⁻¹ := by rw [hconj a ha]
        _ = t ^ j * (t * a * t⁻¹) * (t ^ j)⁻¹ := ih _ hta
        _ = t ^ (j + 1) * a * (t ^ (j + 1))⁻¹ := by rw [pow_succ]; group
  have hu3' : (t * k) ^ 3 = 1 := by rw [← hu3]; exact pow_orderOf_eq_one _
  have h3 : ∀ a ∈ A, Commute (t ^ 3) a := fun a ha => by
    have h1 := hpow 3 a ha
    rw [hu3', one_mul, inv_one, mul_one] at h1
    rw [Commute, SemiconjBy, mul_inv_eq_iff_eq_mul.mp h1.symm]
  obtain ⟨m, hm⟩ := hT.isPGroup ⟨t, htT⟩
  have htm : t ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hcop : Nat.Coprime 3 (2 ^ m) := Nat.Coprime.pow_right _ (by norm_num)
  have hab := Nat.gcd_eq_gcd_ab 3 (2 ^ m)
  rw [hcop.gcd_eq_one, Nat.cast_one] at hab
  have ht : t = (t ^ 3) ^ (Nat.gcdA 3 (2 ^ m)) * (t ^ 2 ^ m) ^ (Nat.gcdB 3 (2 ^ m)) := by
    rw [← zpow_natCast t 3, ← zpow_natCast t (2 ^ m), ← zpow_mul, ← zpow_mul, ← zpow_add,
      ← hab, zpow_one]
  have htC : ∀ a ∈ A, Commute t a := fun a ha => by
    rw [ht, htm, one_zpow, mul_one]
    exact (h3 a ha).zpow_left _
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hEeq := eq_inf_sup_of_le_sup hRA hF.R_le_E hF.E_le
  have hEu : E ≤ centralizer ({t * k} : Set G) := by
    rw [hEeq]
    refine sup_le (fun a ha => ?_) (fun r hr => ?_)
    · rw [mem_centralizer_singleton_iff]
      have h1 := (htC a ha.2).eq
      have h2 : a * k = k * a := mem_centralizer_iff.mp hk a ha.2
      calc a * (t * k) = (a * t) * k := by group
        _ = (t * a) * k := by rw [h1]
        _ = t * (a * k) := by group
        _ = t * (k * a) := by rw [h2]
        _ = t * k * a := by group
    · rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.mp (hRA hr) _ huA).symm
  obtain ⟨e, he, hne⟩ := huE
  apply hne
  have h1 := mem_centralizer_singleton_iff.mp (hEu he)
  calc (t * k)⁻¹ * e * (t * k) = (t * k)⁻¹ * (e * (t * k)) := by group
    _ = (t * k)⁻¹ * (t * k * e) := by rw [h1]
    _ = e := by group

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
  LinearFlag in
theorem exists_sec2U (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) :
    ∃ u : G, u ∈ A ⊓ normalizer (sec2S A R E F : Set G) ∧ orderOf u = 3 ∧
      ∃ e ∈ E, u⁻¹ * e * u ≠ e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := hF.quasisimple
  obtain ⟨c⟩ := nonempty_l34Cover_of_odd hq hL hodd
  have hO := oddCore_le_center hq.1 hq.2
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  obtain ⟨-, hTsyl, -⟩ := sylow_sup_structure hRA hR.isPGroup hF.sylow
  obtain ⟨T₀, hT₀⟩ := hTsyl
  obtain ⟨φ, hφs, hφk, hφT⟩ := c.exists_std hO T₀
  have hkerodd : Odd (Nat.card φ.ker) := by rw [hφk]; exact hodd
  have hkerZ : φ.ker ≤ center ↥A := hφk.le
  have hTsub : ((E ⊔ F) ⊓ A).subgroupOf A = T₀ := by
    rw [← hT₀]
    exact comap_map_eq_self_of_injective A.subtype_injective _
  have hle : ∀ X : Subgroup G, X ≤ (E ⊔ F) ⊓ A → X.subgroupOf A ≤ T₀ := fun X hXT x hx =>
    hTsub ▸ (hXT (mem_subgroupOf.mp hx))
  have hrad : ∀ X : Subgroup G, X ≤ (E ⊔ F) ⊓ A → IsElemAbelian 2 X → Nat.card X = 16 →
      ∃ i : Fin 2, (X.subgroupOf A).map φ = projRad c.k i := by
    intro X hXT hX hX16
    have hXA : X ≤ A := hXT.trans inf_le_right
    have h2 : ∀ x ∈ (X.subgroupOf A).map φ, x ^ 2 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, show x ^ 2 = 1 from
        Subtype.ext (by simpa using hX.2 _ (mem_subgroupOf.mp hx)), map_one]
    have h16 : Nat.card ((X.subgroupOf A).map φ) = 16 := by
      rw [card_map_of_isPGroup φ hkerodd (T₀.2.to_le (hle X hXT)), ← hX16]
      exact Nat.card_congr (subgroupOfEquivOfLe hXA).toEquiv
    rcases eq_projRad_of_le_projUnip c.card_k (hφT ▸ map_mono (hle X hXT)) h2 h16 with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hEAT : E ⊓ A ≤ (E ⊔ F) ⊓ A := inf_le_inf_right A le_sup_left
  have hFAT : F ⊓ A ≤ (E ⊔ F) ⊓ A := inf_le_inf_right A le_sup_right
  obtain ⟨i, hi⟩ := hrad (E ⊓ A) hEAT (AS76b.IsElemAbelian.mono hF.elemE inf_le_left)
    (card_inf_left hF hodd)
  obtain ⟨j, hj⟩ := hrad (F ⊓ A) hFAT (AS76b.IsElemAbelian.mono hF.elemF inf_le_left)
    (card_inf_left hF.symm hodd)
  obtain ⟨a, b, ha, hb, hab3, hab0, hab1, habw⟩ := Sec2.exists_sq_eq_one_mul_torus c.card_k
  obtain ⟨a₀, rfl⟩ := hφs a
  obtain ⟨b₀, rfl⟩ := hφs b
  obtain ⟨a₁, ha₁, ha₁φ⟩ := Sec2.exists_sq_eq_one_map_eq φ hkerodd ha
  obtain ⟨b₁, hb₁, hb₁φ⟩ := Sec2.exists_sq_eq_one_map_eq φ hkerodd hb
  have hφu : φ (a₁ * b₁) = φ a₀ * φ b₀ := by rw [map_mul, ha₁φ, hb₁φ]
  have hnorm : ∀ l : Fin 2,
      φ (a₁ * b₁) ∈ normalizer (projRad c.k l : Set (projectiveSL 3 c.k)) := fun l => by
    rw [hφu]
    fin_cases l
    exacts [hab0, hab1]
  obtain ⟨w, hw, hne⟩ := habw i
  have hu3 : orderOf (a₁ * b₁) = 3 :=
    Sec2.orderOf_mul_eq_three φ hkerZ hkerodd ha₁ hb₁ (by rw [hφu]; exact hab3)
      (fun h => hne (by rw [← hφu, h]; group))
  set u : G := ((a₁ * b₁ : ↥A) : G) with hu
  have huA : u ∈ A := (a₁ * b₁).2
  have hnX : ∀ X : Subgroup G, X ≤ (E ⊔ F) ⊓ A → ∀ l : Fin 2,
      (X.subgroupOf A).map φ = projRad c.k l → u ∈ normalizer (X : Set G) :=
    fun X hXT l hl => mem_normalizer_of_mem_normalizer_subgroupOf (hXT.trans inf_le_right)
      (mem_normalizer_of_map φ hkerZ hkerodd (T₀.2.to_le (hle X hXT)) (hl ▸ hnorm l))
  have hRu : u ∈ normalizer (R : Set G) := Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun r hr => (mem_centralizer_iff.mp (hRA hr) u huA).symm)
  have huE : u ∈ normalizer (E : Set G) := by
    rw [eq_inf_sup_of_le_sup hRA hF.R_le_E hF.E_le]
    exact mem_normalizer_sup (hnX _ hEAT i hi) hRu
  have huF : u ∈ normalizer (F : Set G) := by
    rw [eq_inf_sup_of_le_sup hRA hF.R_le_F hF.F_le]
    exact mem_normalizer_sup (hnX _ hFAT j hj) hRu
  refine ⟨u, ⟨huA, (mem_normalizer_sec2S_of_mem hF huA huE huF).2.2⟩,
    by rw [hu, Subgroup.orderOf_coe, hu3], ?_⟩
  rw [← hi] at hw
  obtain ⟨e₀, he₀, rfl⟩ := hw
  refine ⟨e₀, (mem_subgroupOf.mp he₀).1, fun h => hne ?_⟩
  have h1 : (a₁ * b₁) * e₀ * (a₁ * b₁)⁻¹ = e₀ := Subtype.ext (by
    show u * e₀ * u⁻¹ = e₀
    calc u * e₀ * u⁻¹ = u * (u⁻¹ * e₀ * u) * u⁻¹ := by rw [h]
      _ = e₀ := by group)
  rw [← hφu, ← map_inv, ← map_mul, ← map_mul, h1]

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))

include h11 hE16 hF hL hodd

theorem mem_normalizer_inf_of_orderOf_eq_three {u : G} (huA : u ∈ A)
    (huS : u ∈ normalizer (sec2S A R E F : Set G)) (hu3 : orderOf u = 3) :
    u ∈ normalizer ((E ⊓ A : Subgroup G) : Set G) ∧
      u ∈ normalizer ((F ⊓ A : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := hF.quasisimple
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  obtain ⟨-, hTsyl, -⟩ := sylow_sup_structure hRA hR.isPGroup hF.sylow
  obtain ⟨hES, hFS⟩ := le_sec2S_and_le_sec2S (A := A) (R := R) hF
  have hS2 : IsPGroup 2 (sec2S A R E F) := (isSylowOf_sec2S h11 hE16 hF hL hodd).isPGroup
  have hSA : sec2S A R E F ⊓ A = (E ⊔ F) ⊓ A :=
    hTsyl.eq_of_le (inf_le_inf_right A (sup_le hES hFS)) inf_le_right (hS2.to_le inf_le_left)
  have huT : u ∈ normalizer (((E ⊔ F) ⊓ A : Subgroup G) : Set G) := by
    rw [← hSA]
    exact inf_normalizer_le_normalizer_inf ⟨huS, le_normalizer huA⟩
  have hEeq := eq_inf_sup_of_le_sup hRA hF.R_le_E hF.E_le
  have hFeq := eq_inf_sup_of_le_sup hRA hF.R_le_F hF.F_le
  have hne : E ⊓ A ≠ F ⊓ A := fun h => hF.ne (by rw [hEeq, hFeq, h])
  have hcases : ∀ X : Subgroup G, X ≤ (E ⊔ F) ⊓ A → IsElemAbelian 2 X → Nat.card X = 16 →
      rightConjugate X u = E ⊓ A ∨ rightConjugate X u = F ⊓ A := fun X hX hXe hX16 =>
    Sec2.eq_or_eq_of_card_sixteen hq hL hodd hTsyl
      ((AschbacherTheorem3.rightConjugate_le_rightConjugate hX u).trans
        (le_of_eq ((rightConjugate_eq_self_iff _ u).mpr huT)))
      (AS76b.isElemAbelian_rightConjugate hXe u) (by rw [rightConjugate_card, hX16])
      (inf_le_inf_right A le_sup_left) (AS76b.IsElemAbelian.mono hF.elemE inf_le_left)
      (card_inf_left hF hodd)
      (inf_le_inf_right A le_sup_right) (AS76b.IsElemAbelian.mono hF.elemF inf_le_left)
      (card_inf_left hF.symm hodd) hne
  have h1 := hcases (E ⊓ A) (inf_le_inf_right A le_sup_left)
    (AS76b.IsElemAbelian.mono hF.elemE inf_le_left) (card_inf_left hF hodd)
  have h2 := hcases (F ⊓ A) (inf_le_inf_right A le_sup_right)
    (AS76b.IsElemAbelian.mono hF.elemF inf_le_left) (card_inf_left hF.symm hodd)
  have hinj : ∀ X Y : Subgroup G, rightConjugate X u = rightConjugate Y u → X = Y :=
    fun X Y h => by
      have := congrArg (fun V => rightConjugate V u⁻¹) h
      simpa [rightConjugate_mul, rightConjugate_one] using this
  have hu3' : u ^ 3 = 1 := by rw [← hu3]; exact pow_orderOf_eq_one u
  have htriple : ∀ X : Subgroup G,
      rightConjugate (rightConjugate (rightConjugate X u) u) u = X := fun X => by
    have e : rightConjugate (rightConjugate (rightConjugate X u) u) u =
        rightConjugate X (u ^ 3) := by
      rw [rightConjugate_mul, rightConjugate_mul, pow_three]
    rw [e, hu3', rightConjugate_one]
  rcases h1 with h1 | h1
  · refine ⟨(rightConjugate_eq_self_iff _ u).mp h1, ?_⟩
    rcases h2 with h2 | h2
    · exact absurd (hinj _ _ (h2.trans h1.symm)) hne.symm
    · exact (rightConjugate_eq_self_iff _ u).mp h2
  · exfalso
    rcases h2 with h2 | h2
    · have := htriple (E ⊓ A)
      rw [h1, h2, h1] at this
      exact hne this.symm
    · exact hne (hinj _ _ (h1.trans h2.symm))

theorem sec2U_facts {u : G} (huA : u ∈ A ⊓ normalizer (sec2S A R E F : Set G))
    (hu3 : orderOf u = 3) (huE : ∃ e ∈ E, u⁻¹ * e * u ≠ e) :
    u ∈ normalizer (E : Set G) ∧ u ∈ normalizer (F : Set G) ∧
      u ∈ normalizer ((E ⊓ F : Subgroup G) : Set G) ∧
        ∀ w ∈ sec2Z A E F, u * w * u⁻¹ = w → w = 1 := by
  obtain ⟨huA, huS⟩ := huA
  obtain ⟨hEA, hFA⟩ := mem_normalizer_inf_of_orderOf_eq_three h11 hE16 hF hL hodd huA huS hu3
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hRu : u ∈ normalizer (R : Set G) := centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun r hr => (mem_centralizer_iff.mp (hRA hr) u huA).symm)
  have huE' : u ∈ normalizer (E : Set G) := by
    rw [eq_inf_sup_of_le_sup hRA hF.R_le_E hF.E_le]
    exact mem_normalizer_sup hEA hRu
  have huF' : u ∈ normalizer (F : Set G) := by
    rw [eq_inf_sup_of_le_sup hRA hF.R_le_F hF.F_le]
    exact mem_normalizer_sup hFA hRu
  exact ⟨huE', huF', inf_normalizer_le_normalizer_inf ⟨huE', huF'⟩,
    fun w hw h => eq_one_of_conj_eq_of_orderOf_eq_three hF hL hodd huA hu3 huE hw h⟩

theorem sec2U_mem_normalizer_sec2H {u : G} (huA : u ∈ A ⊓ normalizer (sec2S A R E F : Set G))
    (hu3 : orderOf u = 3) (huE : ∃ e ∈ E, u⁻¹ * e * u ≠ e) :
    u ∈ normalizer (sec2H E F : Set G) := by
  obtain ⟨huE, huF, -, -⟩ := sec2U_facts h11 hE16 hF hL hodd huA hu3 huE
  exact mem_normalizer_sup (Sec2.normalizer_le_normalizer_sec2P E huE)
    (Sec2.normalizer_le_normalizer_sec2P F huF)

theorem mem_of_commute_of_sec2U {u : G} (huA : u ∈ A ⊓ normalizer (sec2S A R E F : Set G))
    (hu3 : orderOf u = 3) (huE : ∃ e ∈ E, u⁻¹ * e * u ≠ e) {e : G} (he : e ∈ E)
    (hue : u * e = e * u) : e ∈ R := by
  obtain ⟨huEn, huF, -, hufix⟩ := sec2U_facts h11 hE16 hF hL hodd huA hu3 huE
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  obtain ⟨huZ, -, -⟩ := mem_normalizer_sec2S_of_mem hF huA.1 huEn huF
  obtain ⟨a, ha, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRA hF.R_le_E hF.E_le he
  have hur : u * r = r * u := mem_centralizer_iff.mp (hRA hr) u huA.1
  have hua : u * a * u⁻¹ = a := by
    have h1 : u * a * r = a * u * r := by
      calc u * a * r = u * (a * r) := by group
        _ = a * r * u := hue
        _ = a * (r * u) := by group
        _ = a * u * r := by rw [← hur]; group
    rw [mul_right_cancel h1, mul_inv_cancel_right]
  rw [eq_one_of_conj_eq_of_sec2Z hF hL hodd huA.1 huZ hufix ha hua, one_mul]
  exact hr

end Frame

namespace Sec2

omit [Finite G] in
theorem mem_conjSetStab_conjSet {V X : Subgroup G} {n : G} (hnV : n ∈ normalizer (V : Set G))
    (hnX : n ∈ normalizer (X : Set G)) : n ∈ conjSetStab (conjSet V X) := by
  have hle : zpowers n ≤ conjSetStab (conjSet V X) := le_conjSetStab fun m hm W hW => by
    obtain ⟨θ, hθ, rfl⟩ := hW
    have hmV : m ∈ normalizer (V : Set G) := zpowers_le.mpr hnV hm
    have hmX : m ∈ normalizer (X : Set G) := zpowers_le.mpr hnX hm
    refine ⟨m⁻¹ * θ * m, ?_, ?_⟩
    · have := (mem_normalizer_iff.mp (inv_mem hmX) θ).mp hθ
      simpa using this
    · rw [rightConjugate_mul, show θ * m = m * (m⁻¹ * θ * m) by group, ← rightConjugate_mul,
        (rightConjugate_eq_self_iff V m).mpr hmV]
  exact hle (mem_zpowers n)

theorem eq_or_eq_inv_of_commute_of_pow_three {α : Type*} [Fintype α] [DecidableEq α]
    (h5 : Fintype.card α = 5) {σ τ : Equiv.Perm α} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (hστ : σ * τ = τ * σ) : τ = σ ∨ τ = σ⁻¹ := by
  have hσσσ : ∀ v, σ (σ (σ v)) = v := fun v => by
    have := congrArg (fun π : Equiv.Perm α => π v) hσ3
    simpa [pow_succ, Equiv.Perm.mul_apply] using this
  have hτττ : ∀ v, τ (τ (τ v)) = v := fun v => by
    have := congrArg (fun π : Equiv.Perm α => π v) hτ3
    simpa [pow_succ, Equiv.Perm.mul_apply] using this
  have hc : ∀ v, σ (τ v) = τ (σ v) := fun v => by
    have := congrArg (fun π : Equiv.Perm α => π v) hστ
    simpa [Equiv.Perm.mul_apply] using this
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h
    push Not at h
    exact hσ1 (Equiv.ext h)
  set b := σ a with hb
  set c := σ b with hcdef
  have hab : a ≠ b := fun h => ha h.symm
  have hbc : b ≠ c := fun h => ha (σ.injective h.symm)
  have hac : a ≠ c := fun h => ha (by
    have h1 : σ c = σ a := by rw [← h]
    rw [hcdef, hσσσ] at h1
    exact h1.symm)
  have hσc : σ c = a := hσσσ a
  have hcard : (Finset.univ \ ({a, b, c} : Finset α)).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, h5,
      Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
  obtain ⟨d, e, hde, hdeq⟩ := Finset.card_eq_two.mp hcard
  have hd : d ∉ ({a, b, c} : Finset α) := by
    have : d ∈ Finset.univ \ ({a, b, c} : Finset α) := by rw [hdeq]; simp
    exact (Finset.mem_sdiff.mp this).2
  have he : e ∉ ({a, b, c} : Finset α) := by
    have : e ∈ Finset.univ \ ({a, b, c} : Finset α) := by rw [hdeq]; simp
    exact (Finset.mem_sdiff.mp this).2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd he
  have hall : ∀ v, v = a ∨ v = b ∨ v = c ∨ v = d ∨ v = e := fun v => by
    by_cases hv : v ∈ ({a, b, c} : Finset α)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      tauto
    · have : v ∈ Finset.univ \ ({a, b, c} : Finset α) :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩
      rw [hdeq] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      tauto
  have hfixσ : ∀ v, v = d ∨ v = e → σ v = v := by
    have hσde : ∀ v, v = d ∨ v = e → σ v = d ∨ σ v = e := fun v hv => by
      rcases hall (σ v) with h | h | h | h | h
      · exfalso
        have : v = c := σ.injective (h.trans hσc.symm)
        rcases hv with rfl | rfl <;> simp_all
      · exfalso
        have : v = a := σ.injective h
        rcases hv with rfl | rfl <;> simp_all
      · exfalso
        have : v = b := σ.injective h
        rcases hv with rfl | rfl <;> simp_all
      · exact Or.inl h
      · exact Or.inr h
    have hσd := hσde d (Or.inl rfl)
    have hσe := hσde e (Or.inr rfl)
    have hd' : σ d = d := by
      rcases hσd with h | h
      · exact h
      · exfalso
        rcases hσe with h' | h'
        · have h3 := hσσσ d
          rw [h, h', h] at h3
          exact hde h3.symm
        · exact hde (σ.injective (h.trans h'.symm))
    have he' : σ e = e := by
      rcases hσe with h | h
      · exact absurd (σ.injective (h.trans hd'.symm)) (fun h' => hde h'.symm)
      · exact h
    rintro v (rfl | rfl)
    · exact hd'
    · exact he'
  have hτde : ∀ v, v = d ∨ v = e → τ v = d ∨ τ v = e := fun v hv => by
    have hfix : σ (τ v) = τ v := by rw [hc, hfixσ v hv]
    rcases hall (τ v) with h | h | h | h | h
    · rw [h] at hfix
      exact absurd hfix ha
    · rw [h] at hfix
      exact absurd hfix.symm hbc
    · rw [h, hσc] at hfix
      exact absurd hfix hac
    · exact Or.inl h
    · exact Or.inr h
  have hτd : τ d = d := by
    rcases hτde d (Or.inl rfl) with h | h
    · exact h
    · exfalso
      rcases hτde e (Or.inr rfl) with h' | h'
      · have h3 := hτττ d
        rw [h, h', h] at h3
        exact hde h3.symm
      · exact hde (τ.injective (h.trans h'.symm))
  have hτe : τ e = e := by
    rcases hτde e (Or.inr rfl) with h | h
    · exact absurd (τ.injective (h.trans hτd.symm)) (fun h' => hde h'.symm)
    · exact h
  have hτa : τ a = a ∨ τ a = b ∨ τ a = c := by
    rcases hall (τ a) with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exfalso
      have : σ (τ a) = τ a := by rw [h]; exact hfixσ d (Or.inl rfl)
      rw [hc] at this
      exact ha (τ.injective this)
    · exfalso
      have : σ (τ a) = τ a := by rw [h]; exact hfixσ e (Or.inr rfl)
      rw [hc] at this
      exact ha (τ.injective this)
  have hτb : τ b = σ (τ a) := by rw [hb, ← hc]
  have hτc : τ c = σ (τ b) := by rw [hcdef, ← hc]
  rcases hτa with h | h | h
  · exfalso
    apply hτ1
    refine Equiv.ext fun v => ?_
    rcases hall v with rfl | rfl | rfl | rfl | rfl
    · exact h
    · rw [hτb, h]; rfl
    · rw [hτc, hτb, h]; rfl
    · exact hτd
    · exact hτe
  · left
    refine Equiv.ext fun v => ?_
    rcases hall v with rfl | rfl | rfl | rfl | rfl
    · exact h
    · rw [hτb, h]
    · rw [hτc, hτb, h, hσc]
    · rw [hτd, hfixσ _ (Or.inl rfl)]
    · rw [hτe, hfixσ _ (Or.inr rfl)]
  · right
    have e1 : τ (σ a) = a := by rw [← hb, hτb, h, hσc]
    have e2 : τ (σ b) = b := by rw [← hcdef, hτc, hτb, h, hσc]
    have e3 : τ (σ c) = c := by rw [hσc, h]
    have e4 : τ (σ d) = d := by rw [hfixσ _ (Or.inl rfl), hτd]
    have e5 : τ (σ e) = e := by rw [hfixσ _ (Or.inr rfl), hτe]
    rw [eq_inv_iff_mul_eq_one]
    refine Equiv.ext fun v => ?_
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    rcases hall v with h' | h' | h' | h' | h' <;> rw [h']
    · exact e1
    · exact e2
    · exact e3
    · exact e4
    · exact e5

omit [Finite G] in
theorem FourLines.comp_perm {V Z : Subgroup G} {W : Fin 4 → Subgroup G}
    (hL : FourLines V Z W) (σ : Equiv.Perm (Fin 4)) : FourLines V Z (W ∘ σ) where
  elem := hL.elem
  card := hL.card
  cardZ := hL.cardZ
  Z_le i := hL.Z_le (σ i)
  le i := hL.le (σ i)
  cardW i := hL.cardW (σ i)
  inf i j hij := hL.inf (σ i) (σ j) (σ.injective.ne hij)

theorem FourLines.mem_of_fix_of_not_forall {V Z : Subgroup G} {W : Fin 4 → Subgroup G}
    (hL : FourLines V Z W) {n : G} (hnZ : n ∈ normalizer (Z : Set G))
    (hnW : ∀ i, n ∈ normalizer ((W i : Subgroup G) : Set G))
    (hn : ¬ ∀ f ∈ V, f⁻¹ * (n⁻¹ * f * n) ∈ Z) {f : G} (hf : f ∈ V)
    (hfix : f⁻¹ * (n⁻¹ * f * n) ∈ Z) : f ∈ Z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hL.exists_mul (i := 0) (j := 1) (by decide) hf
  have hc : ∀ i, ∀ w ∈ W i, n⁻¹ * w * n ∈ W i := fun i w hw => by
    simpa using (mem_normalizer_iff.mp (inv_mem (hnW i)) w).mp hw
  have haV := hL.le 0 ha
  have hbV := hL.le 1 hb
  have hcomm := hL.comm (V.inv_mem hbV) (V.mul_mem (V.inv_mem haV) (hL.le 0 (hc 0 a ha)))
  have e : (a * b)⁻¹ * (n⁻¹ * (a * b) * n) = (a⁻¹ * (n⁻¹ * a * n)) * (b⁻¹ * (n⁻¹ * b * n)) := by
    calc (a * b)⁻¹ * (n⁻¹ * (a * b) * n) = b⁻¹ * (a⁻¹ * (n⁻¹ * a * n)) * (n⁻¹ * b * n) := by
          group
      _ = (a⁻¹ * (n⁻¹ * a * n)) * b⁻¹ * (n⁻¹ * b * n) := by rw [hcomm]
      _ = (a⁻¹ * (n⁻¹ * a * n)) * (b⁻¹ * (n⁻¹ * b * n)) := by group
  have ha' : a⁻¹ * (n⁻¹ * a * n) ∈ W 0 := (W 0).mul_mem ((W 0).inv_mem ha) (hc 0 a ha)
  have hb' : b⁻¹ * (n⁻¹ * b * n) ∈ W 1 := (W 1).mul_mem ((W 1).inv_mem hb) (hc 1 b hb)
  have hfa : a⁻¹ * (n⁻¹ * a * n) ∈ Z := by
    have h1 : a⁻¹ * (n⁻¹ * a * n) =
        ((a * b)⁻¹ * (n⁻¹ * (a * b) * n)) * (b⁻¹ * (n⁻¹ * b * n))⁻¹ := by
      rw [e]
      group
    have h2 : a⁻¹ * (n⁻¹ * a * n) ∈ W 0 ⊓ W 1 :=
      ⟨ha', h1 ▸ (W 1).mul_mem (hL.Z_le 1 hfix) ((W 1).inv_mem hb')⟩
    rwa [hL.inf 0 1 (by decide)] at h2
  have hfb : b⁻¹ * (n⁻¹ * b * n) ∈ Z := by
    have h1 : b⁻¹ * (n⁻¹ * b * n) =
        (a⁻¹ * (n⁻¹ * a * n))⁻¹ * ((a * b)⁻¹ * (n⁻¹ * (a * b) * n)) := by
      rw [e]
      group
    rw [h1]
    exact Z.mul_mem (Z.inv_mem hfa) hfix
  have haZ : a ∈ Z := by
    by_contra haZ
    exact hn (hL.forall_mem_of_fix hnZ hnW ha haZ hfa)
  have hbZ : b ∈ Z := by
    by_contra hbZ
    have hL' := hL.comp_perm (Equiv.swap 0 1)
    have hb0 : b ∈ (W ∘ Equiv.swap 0 1) 0 := by simpa using hb
    exact hn (hL'.forall_mem_of_fix hnZ (fun i => hnW _) hb0 hbZ hfb)
  exact Z.mul_mem haZ hbZ

end Sec2

section FrameXH

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))

include h11 hE16 hF hL hodd

theorem mem_centralizer_sec2Z_of_forall {q : G}
    (hq : ∀ s ∈ sec2S A R E F, s⁻¹ * (q⁻¹ * s * q) ∈ sec2Z A E F) :
    q ∈ centralizer (sec2Z A E F : Set G) := by
  have hZ := centerIn_sec2S_eq h11 hE16 hF hL hodd
  have hZS : sec2Z A E F ≤ sec2S A R E F := fun z hz => by rw [← hZ] at hz; exact hz.1
  have hcza : ∀ z ∈ sec2Z A E F, ∀ s ∈ sec2S A R E F, Commute z s := fun z hz s hs => by
    rw [← hZ] at hz
    exact (mem_centralizer_iff.mp hz.2 s hs).symm
  have hq' : (⁅sec2S A R E F, sec2S A R E F⁆ : Subgroup G) ≤ centralizer ({q} : Set G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def, mem_centralizer_singleton_iff]
    have hza := hq a ha
    have hzb := hq b hb
    have ha' : q⁻¹ * a * q = (a⁻¹ * (q⁻¹ * a * q)) * a := by
      rw [(hcza _ hza a ha).eq]
      group
    have hb' : q⁻¹ * b * q = (b⁻¹ * (q⁻¹ * b * q)) * b := by
      rw [(hcza _ hzb b hb).eq]
      group
    have key : q⁻¹ * (a * b * a⁻¹ * b⁻¹) * q = a * b * a⁻¹ * b⁻¹ := by
      calc q⁻¹ * (a * b * a⁻¹ * b⁻¹) * q = (q⁻¹ * a * q) * (q⁻¹ * b * q) * (q⁻¹ * a * q)⁻¹ *
            (q⁻¹ * b * q)⁻¹ := by group
        _ = (a⁻¹ * (q⁻¹ * a * q)) * a * ((b⁻¹ * (q⁻¹ * b * q)) * b) *
            ((a⁻¹ * (q⁻¹ * a * q)) * a)⁻¹ * ((b⁻¹ * (q⁻¹ * b * q)) * b)⁻¹ := by
            rw [← ha', ← hb']
        _ = a * b * a⁻¹ * b⁻¹ := Sec2.commutator_mul_mul_of_commute (hcza _ hza a ha)
            (hcza _ hza b hb) (hcza _ hzb a ha) (hcza _ hzb b hb) (hcza _ hza _ (hZS hzb))
    calc a * b * a⁻¹ * b⁻¹ * q = q * (q⁻¹ * (a * b * a⁻¹ * b⁻¹) * q) := by group
      _ = q * (a * b * a⁻¹ * b⁻¹) := by rw [key]
  rw [commutator_sec2S_eq h11 hE16 hF hL hodd] at hq'
  exact mem_centralizer_iff.mpr fun z hz => mem_centralizer_singleton_iff.mp (hq' hz)


variable {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F) {h : G} (hh : h ∈ sec2P E)
  (hhS : h ∉ sec2S A R E F) (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))
  (h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E)))

include hx hxS hh hhS h4 h4'

theorem forall_mem_of_fix_E_of_mem {n : G} (hnZ : n ∈ normalizer (sec2Z A E F : Set G))
    (hfixE : ∀ V ∈ conjSet E (sec2H E F), n ∈ normalizer (V : Set G))
    (hfixF : ∀ V ∈ conjSet F (sec2H E F), n ∈ normalizer (V : Set G)) {E' F' : Subgroup G}
    (hE' : E' ∈ conjSet E (sec2H E F)) (hF' : F' ∈ conjSet F (sec2H E F)) {v : G}
    (hv : v ∈ E' ⊓ F') (hvZ : v ∉ sec2Z A E F) (hnv : v⁻¹ * (n⁻¹ * v * n) ∈ sec2Z A E F) :
    ∀ e ∈ E', e⁻¹ * (n⁻¹ * e * n) ∈ sec2Z A E F := by
  obtain ⟨-, hF5⟩ := ncard_conjSet_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  obtain ⟨W, hW0, hWmem, hWne⟩ := Sec2.exists_fin_four_of_ncard_eq_five hF5 hF'
  have hL4 := fourLines_of_mem_conjSet_E h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hE' hWmem hWne
  have hv' : v ∈ E' ⊓ W 0 := by rw [hW0]; exact hv
  exact hL4.forall_mem_of_fix hnZ
    (fun i => inf_normalizer_le_normalizer_inf ⟨hfixE E' hE', hfixF _ (hWmem i)⟩) hv' hvZ hnv

theorem forall_mem_of_fix_F_of_mem {n : G} (hnZ : n ∈ normalizer (sec2Z A E F : Set G))
    (hfixE : ∀ V ∈ conjSet E (sec2H E F), n ∈ normalizer (V : Set G))
    (hfixF : ∀ V ∈ conjSet F (sec2H E F), n ∈ normalizer (V : Set G)) {E' F' : Subgroup G}
    (hE' : E' ∈ conjSet E (sec2H E F)) (hF' : F' ∈ conjSet F (sec2H E F)) {v : G}
    (hv : v ∈ F' ⊓ E') (hvZ : v ∉ sec2Z A E F) (hnv : v⁻¹ * (n⁻¹ * v * n) ∈ sec2Z A E F) :
    ∀ f ∈ F', f⁻¹ * (n⁻¹ * f * n) ∈ sec2Z A E F := by
  obtain ⟨hE5, -⟩ := ncard_conjSet_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  obtain ⟨W, hW0, hWmem, hWne⟩ := Sec2.exists_fin_four_of_ncard_eq_five hE5 hE'
  have hL4 := fourLines_of_mem_conjSet_F h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hF' hWmem hWne
  have hv' : v ∈ F' ⊓ W 0 := by rw [hW0]; exact hv
  exact hL4.forall_mem_of_fix hnZ
    (fun i => inf_normalizer_le_normalizer_inf ⟨hfixF F' hF', hfixE _ (hWmem i)⟩) hv' hvZ hnv

theorem forall_mem_sec2S_of_forall_mem_F_of_mem {n : G}
    (hnZ : n ∈ normalizer (sec2Z A E F : Set G))
    (hfixE : ∀ V ∈ conjSet E (sec2H E F), n ∈ normalizer (V : Set G))
    (hfixF : ∀ V ∈ conjSet F (sec2H E F), n ∈ normalizer (V : Set G))
    (hcen : ∀ f ∈ F, f⁻¹ * (n⁻¹ * f * n) ∈ sec2Z A E F) :
    ∀ s ∈ sec2S A R E F, s⁻¹ * (n⁻¹ * s * n) ∈ sec2Z A E F := by
  set H := sec2H E F with hHdef
  have hFmem : F ∈ conjSet F H := ⟨1, one_mem _, (rightConjugate_one F).symm⟩
  have hEmem : E ∈ conjSet E H := ⟨1, one_mem _, (rightConjugate_one E).symm⟩
  have hE' : ∀ E' ∈ conjSet E H, ∀ e ∈ E', e⁻¹ * (n⁻¹ * e * n) ∈ sec2Z A E F := by
    intro E' hE'
    obtain ⟨v, hv, hvZ⟩ :=
      exists_mem_inf_not_mem_sec2Z_of_mem h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hE' hFmem
    exact forall_mem_of_fix_E_of_mem h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hnZ hfixE hfixF hE'
      hFmem hv hvZ (hcen v hv.2)
  have hSx := (rightConjugate_inf_eq_and_sec2S_eq h11 hE16 hF hL hodd hx hxS).2
  have hExmem : rightConjugate E x ∈ conjSet E H := ⟨x, mem_sup_right hx, rfl⟩
  have hExS : rightConjugate E x ≤ sec2S A R E F := hSx ▸ le_sup_right
  have hExN : rightConjugate E x ≤ normalizer (E : Set G) :=
    hExS.trans (sec2S_le_normalizer_left hF hL hodd)
  have hZ := centerIn_sec2S_eq h11 hE16 hF hL hodd
  intro s hs
  have hs' : s ∈ ((E ⊔ rightConjugate E x : Subgroup G) : Set G) := hSx ▸ hs
  rw [coe_mul_of_right_le_normalizer_left E _ hExN] at hs'
  obtain ⟨e, he, e', he', rfl⟩ := hs'
  have h1 := hE' E hEmem e he
  have h2 := hE' _ hExmem e' he'
  have he'Z : e' ∈ normalizer (sec2Z A E F : Set G) := by
    rw [← hZ]
    exact mem_normalizer_centerIn (le_normalizer (hExS he'))
  have e₁ : (e * e')⁻¹ * (n⁻¹ * (e * e') * n) =
      (e'⁻¹ * (e⁻¹ * (n⁻¹ * e * n)) * e') * (e'⁻¹ * (n⁻¹ * e' * n)) := by group
  rw [e₁]
  refine mul_mem ?_ h2
  have := (mem_normalizer_iff.mp (inv_mem he'Z) _).mp h1
  rwa [inv_inv] at this

theorem mem_sec2Z_of_fix_of_not_forall {n : G} (hnZ : n ∈ normalizer (sec2Z A E F : Set G))
    (hfixE : ∀ V ∈ conjSet E (sec2H E F), n ∈ normalizer (V : Set G))
    (hfixF : ∀ V ∈ conjSet F (sec2H E F), n ∈ normalizer (V : Set G))
    (hn : ¬ ∀ s ∈ sec2S A R E F, s⁻¹ * (n⁻¹ * s * n) ∈ sec2Z A E F) {s : G}
    (hs : s ∈ sec2S A R E F) (hfix : s⁻¹ * (n⁻¹ * s * n) ∈ sec2Z A E F) : s ∈ sec2Z A E F := by
  set H := sec2H E F with hHdef
  obtain ⟨-, hF5⟩ := ncard_conjSet_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hFmem : F ∈ conjSet F H := ⟨1, one_mem _, (rightConjugate_one F).symm⟩
  have hEmem : E ∈ conjSet E H := ⟨1, one_mem _, (rightConjugate_one E).symm⟩
  have hE' : ∀ E' ∈ conjSet E H, ∀ e ∈ E', e⁻¹ * (n⁻¹ * e * n) ∈ sec2Z A E F →
      e ∈ sec2Z A E F := by
    intro E' hE'
    have hnE' : ¬ ∀ e ∈ E', e⁻¹ * (n⁻¹ * e * n) ∈ sec2Z A E F := fun hall => hn (by
      obtain ⟨v, hv, hvZ⟩ :=
        exists_mem_inf_not_mem_sec2Z_of_mem h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hE' hFmem
      have hcF := forall_mem_of_fix_F_of_mem h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hnZ hfixE
        hfixF hE' hFmem ⟨hv.2, hv.1⟩ hvZ (hall v hv.1)
      exact forall_mem_sec2S_of_forall_mem_F_of_mem h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hnZ
        hfixE hfixF hcF)
    obtain ⟨W, -, hWmem, hWne⟩ := Sec2.exists_fin_four_of_ncard_eq_five hF5 hFmem
    have hL4 :=
      fourLines_of_mem_conjSet_E h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hE' hWmem hWne
    exact fun e he hfe => hL4.mem_of_fix_of_not_forall hnZ
      (fun i => inf_normalizer_le_normalizer_inf ⟨hfixE E' hE', hfixF _ (hWmem i)⟩) hnE' he hfe
  obtain ⟨hinf, hSx⟩ := rightConjugate_inf_eq_and_sec2S_eq h11 hE16 hF hL hodd hx hxS
  have hExmem : rightConjugate E x ∈ conjSet E H := ⟨x, mem_sup_right hx, rfl⟩
  have hExS : rightConjugate E x ≤ sec2S A R E F := hSx ▸ le_sup_right
  have hExN : rightConjugate E x ≤ normalizer (E : Set G) :=
    hExS.trans (sec2S_le_normalizer_left hF hL hodd)
  have hZ := centerIn_sec2S_eq h11 hE16 hF hL hodd
  have hZEx : sec2Z A E F ≤ rightConjugate E x := by rw [← hinf]; exact inf_le_left
  have hs' : s ∈ ((E ⊔ rightConjugate E x : Subgroup G) : Set G) := hSx ▸ hs
  rw [coe_mul_of_right_le_normalizer_left E _ hExN] at hs'
  obtain ⟨e, he, e', he', rfl⟩ := hs'
  have hnE : n⁻¹ ∈ normalizer (E : Set G) := inv_mem (hfixE E hEmem)
  have hnEx : n⁻¹ ∈ normalizer (rightConjugate E x : Set G) := inv_mem (hfixE _ hExmem)
  set a := e⁻¹ * (n⁻¹ * e * n) with ha
  set b := e'⁻¹ * (n⁻¹ * e' * n) with hb
  have haE : a ∈ E := E.mul_mem (E.inv_mem he) (by simpa using (mem_normalizer_iff.mp hnE e).mp he)
  have hbEx : b ∈ rightConjugate E x := (rightConjugate E x).mul_mem
    ((rightConjugate E x).inv_mem he') (by simpa using (mem_normalizer_iff.mp hnEx e').mp he')
  have e₁ : (e * e')⁻¹ * (n⁻¹ * (e * e') * n) = (e'⁻¹ * a * e') * b := by rw [ha, hb]; group
  rw [e₁] at hfix
  have hc1 : e'⁻¹ * a * e' ∈ E := by
    have := (mem_normalizer_iff.mp (inv_mem (hExN he')) a).mp haE
    simpa [mul_assoc] using this
  have hc2 : e'⁻¹ * a * e' ∈ rightConjugate E x := by
    have h1 : e'⁻¹ * a * e' = ((e'⁻¹ * a * e') * b) * b⁻¹ := by group
    rw [h1]
    exact (rightConjugate E x).mul_mem (hZEx hfix) ((rightConjugate E x).inv_mem hbEx)
  have hc : e'⁻¹ * a * e' ∈ sec2Z A E F := by
    rw [← hinf]
    exact ⟨hc2, hc1⟩
  have he'Z : e' ∈ normalizer (sec2Z A E F : Set G) := by
    rw [← hZ]
    exact mem_normalizer_centerIn (le_normalizer (hExS he'))
  have haZ : a ∈ sec2Z A E F := by
    have := (mem_normalizer_iff.mp he'Z _).mp hc
    simpa [mul_assoc] using this
  have hbZ : b ∈ sec2Z A E F := by
    have h1 : b = (e'⁻¹ * a * e')⁻¹ * ((e'⁻¹ * a * e') * b) := by group
    rw [h1]
    exact mul_mem (inv_mem hc) hfix
  exact mul_mem (hE' E hEmem e he haZ) (hE' _ hExmem e' he' hbZ)

theorem actsAsF4Scalar_of_fix {n : G} (hnS : n ∈ normalizer (sec2S A R E F : Set G))
    (hnZ : n ∈ normalizer (sec2Z A E F : Set G))
    (hfixE : ∀ V ∈ conjSet E (sec2H E F), n ∈ normalizer (V : Set G))
    (hfixF : ∀ V ∈ conjSet F (sec2H E F), n ∈ normalizer (V : Set G))
    (hn : ¬ ∀ s ∈ sec2S A R E F, s⁻¹ * (n⁻¹ * s * n) ∈ sec2Z A E F) (hn3 : n ^ 3 = 1) :
    ActsAsF4Scalar n (sec2S A R E F) (sec2Z A E F) := by
  refine ⟨hnS, hnZ, fun s hs => ?_⟩
  have hcS : ∀ t ∈ sec2S A R E F, n⁻¹ * t * n ∈ sec2S A R E F := fun t ht => by
    simpa using (mem_normalizer_iff.mp (inv_mem hnS) t).mp ht
  have hs1 := hcS s hs
  have hs2 : n⁻¹ * n⁻¹ * s * n * n ∈ sec2S A R E F := by
    have := hcS _ hs1
    simpa [mul_assoc] using this
  set N := s * (n⁻¹ * s * n) * (n⁻¹ * n⁻¹ * s * n * n) with hN
  have hNS : N ∈ sec2S A R E F := mul_mem (mul_mem hs hs1) hs2
  refine mem_sec2Z_of_fix_of_not_forall h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hnZ hfixE
    hfixF hn hNS ?_
  have hn3' : n⁻¹ * n⁻¹ * n⁻¹ * s * n * n * n = s := by
    have : n * n * n = 1 := by rw [← hn3, pow_three, mul_assoc]
    calc n⁻¹ * n⁻¹ * n⁻¹ * s * n * n * n = (n * n * n)⁻¹ * s * (n * n * n) := by group
      _ = s := by rw [this, inv_one, one_mul, mul_one]
  have e₁ : N⁻¹ * (n⁻¹ * N * n) = N⁻¹ * s⁻¹ * N * s := by
    rw [hN]
    calc (s * (n⁻¹ * s * n) * (n⁻¹ * n⁻¹ * s * n * n))⁻¹ *
          (n⁻¹ * (s * (n⁻¹ * s * n) * (n⁻¹ * n⁻¹ * s * n * n)) * n)
        = (s * (n⁻¹ * s * n) * (n⁻¹ * n⁻¹ * s * n * n))⁻¹ *
          ((n⁻¹ * s * n) * (n⁻¹ * n⁻¹ * s * n * n) * (n⁻¹ * n⁻¹ * n⁻¹ * s * n * n * n)) := by
          group
      _ = (s * (n⁻¹ * s * n) * (n⁻¹ * n⁻¹ * s * n * n))⁻¹ *
          ((n⁻¹ * s * n) * (n⁻¹ * n⁻¹ * s * n * n) * s) := by rw [hn3']
      _ = (s * (n⁻¹ * s * n) * (n⁻¹ * n⁻¹ * s * n * n))⁻¹ * s⁻¹ *
          (s * (n⁻¹ * s * n) * (n⁻¹ * n⁻¹ * s * n * n)) * s := by group
  rw [e₁]
  have := (sq_mem_and_commutator_mem_sec2Z h11 hE16 hF hL hodd ((sec2S A R E F).inv_mem hNS)
    ((sec2S A R E F).inv_mem hs)).2
  simpa using this

theorem exists_mem_sec2H_mem_normalizer_not_mem {V V' : Subgroup G}
    (hV : V ∈ conjSet F (sec2H E F)) (hV' : V' ∈ conjSet F (sec2H E F)) (hne : V ≠ V') :
    ∃ q ∈ sec2H E F, q ∈ normalizer (V : Set G) ∧ q ∉ normalizer (V' : Set G) := by
  classical
  set H := sec2H E F with hHdef
  have hHQ : H ≤ Sec2.conjSetStab (conjSet F H) := Sec2.le_conjSetStab fun k hk W ⟨θ, hθ, hW⟩ =>
    ⟨θ * k, mul_mem hθ hk, by rw [hW, rightConjugate_mul]⟩
  set ψ := Sec2.conjPermHom hHQ with hψ
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  have hIF : InducesA5 H (conjSet F H) := by
    have := inducesA5_sec2H h11 hE16 hF.symm hL hodd hh (hSc ▸ hhS) hx (hSc ▸ hxS) h4' h4
    rwa [show sec2H F E = sec2H E F from sup_comm _ _] at this
  have hQ5 : Nat.card ↥(conjSet F H) = 5 := hIF.1
  have : Fintype ↥(conjSet F H) := Fintype.ofFinite _
  have hcard := Sec2.card_range_conjPermHom hHQ hIF
  have hperm : Nat.card (Equiv.Perm ↥(conjSet F H)) = 120 := by
    rw [Nat.card_perm, hQ5]
    decide
  have hidx : ψ.range.index = 2 := by
    have := ψ.range.index_mul_card
    rw [hcard, hperm] at this
    omega
  have hrange : ψ.range = alternatingGroup ↥(conjSet F H) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx
  have hQ5' : (conjSet F H).ncard = 5 := by rw [← Nat.card_coe_set_eq]; exact hQ5
  have h3 : ((conjSet F H \ {V}) \ {V'}).ncard = 3 := by
    rw [Set.ncard_sdiff_singleton_of_mem (show V' ∈ conjSet F H \ {V} from
      ⟨hV', fun h => hne (Set.mem_singleton_iff.mp h).symm⟩),
      Set.ncard_sdiff_singleton_of_mem hV, hQ5']
  obtain ⟨r, t, w, hrt, -, -, hrtw⟩ := Set.ncard_eq_three.mp h3
  have hr : r ∈ (conjSet F H \ {V}) \ {V'} := by rw [hrtw]; simp
  have ht : t ∈ (conjSet F H \ {V}) \ {V'} := by rw [hrtw]; simp
  simp only [Set.mem_sdiff, Set.mem_singleton_iff] at hr ht
  set V₀ : ↥(conjSet F H) := ⟨V, hV⟩
  set V₁ : ↥(conjSet F H) := ⟨V', hV'⟩
  set r₀ : ↥(conjSet F H) := ⟨r, hr.1.1⟩
  set t₀ : ↥(conjSet F H) := ⟨t, ht.1.1⟩
  have hV₁r : V₁ ≠ r₀ := fun h => hr.2 (congrArg Subtype.val h).symm
  have hrt₀ : r₀ ≠ t₀ := fun h => hrt (congrArg Subtype.val h)
  set γ := Equiv.swap V₁ r₀ * Equiv.swap r₀ t₀ with hγ
  have hγalt : γ ∈ alternatingGroup ↥(conjSet F H) := by
    rw [Equiv.Perm.mem_alternatingGroup, hγ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hV₁r,
      Equiv.Perm.sign_swap hrt₀]
    decide
  obtain ⟨q, hq⟩ := (hrange ▸ hγalt : γ ∈ ψ.range)
  have hVr : V₀ ≠ r₀ := fun h => hr.1.2 (congrArg Subtype.val h).symm
  have hVt : V₀ ≠ t₀ := fun h => ht.1.2 (congrArg Subtype.val h).symm
  have hVV₁ : V₀ ≠ V₁ := fun h => hne (congrArg Subtype.val h)
  have hV₁t : V₁ ≠ t₀ := fun h => ht.2 (congrArg Subtype.val h).symm
  have hγV : γ V₀ = V₀ := by
    rw [hγ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hVr hVt,
      Equiv.swap_apply_of_ne_of_ne hVV₁ hVr]
  have hγV' : γ V₁ = r₀ := by
    rw [hγ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hV₁r hV₁t,
      Equiv.swap_apply_left]
  refine ⟨q, q.2, ?_, fun hqV' => ?_⟩
  · have h1 := congrArg Subtype.val (show ψ q V₀ = V₀ by rw [hq]; exact hγV)
    rw [hψ, Sec2.conjPermHom_apply] at h1
    simpa using inv_mem ((rightConjugate_eq_self_iff _ _).mp h1)
  · have h1 : ψ q V₁ = V₁ := Subtype.ext (by
      rw [hψ, Sec2.conjPermHom_apply]
      exact (rightConjugate_eq_self_iff _ _).mpr (inv_mem hqV'))
    rw [hq, hγV'] at h1
    exact hV₁r h1.symm

theorem forall_mem_normalizer_F_of_mem {n : G} (hnS : n ∈ normalizer (sec2S A R E F : Set G))
    (hnH : n ∈ normalizer (sec2H E F : Set G))
    (hfixE : ∀ V ∈ conjSet E (sec2H E F), n ∈ normalizer (V : Set G)) :
    (∀ q ∈ sec2H E F, n⁻¹ * q⁻¹ * n * q ∈ sec2S A R E F) ∧
      ∀ V ∈ conjSet F (sec2H E F), n ∈ normalizer (V : Set G) := by
  set H := sec2H E F with hHdef
  obtain ⟨hpl, -⟩ := planes_sec2S_facts h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hSN : ∀ V ∈ conjSet E H ∪ conjSet F H, sec2S A R E F ≤ normalizer (V : Set G) :=
    fun V hV => sec2S_le_normalizer_of_sec2Z_le h11 hE16 hF hL hodd (hpl V hV).2.2.1
      (hpl V hV).2.2.2
  have hEinv : ∀ V ∈ conjSet E H, ∀ q ∈ H, rightConjugate V q ∈ conjSet E H := by
    rintro V ⟨θ, hθ, rfl⟩ q hq
    exact ⟨θ * q, mul_mem hθ hq, rightConjugate_mul E θ q⟩
  have hcomm : ∀ q ∈ H, n⁻¹ * q⁻¹ * n * q ∈ sec2S A R E F := by
    intro q hq
    have hnq : n⁻¹ * q⁻¹ * n ∈ H := by
      have := (mem_normalizer_iff.mp (inv_mem hnH) q⁻¹).mp (inv_mem hq)
      simpa using this
    refine mem_sec2S_of_forall h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' (mul_mem hnq hq)
      fun V hV => ?_
    have h1 := hfixE _ (hEinv V hV q⁻¹ (inv_mem hq))
    rw [← AschbacherTheorem3.rightConjugate_normalizer, mem_rightConjugate_iff, inv_inv] at h1
    have e : n⁻¹ * q⁻¹ * n * q = n⁻¹ * (q⁻¹ * n * q) := by group
    rw [e]
    exact mul_mem (inv_mem (hfixE V hV)) h1
  refine ⟨hcomm, ?_⟩
  have hFmem : F ∈ conjSet F H := ⟨1, one_mem _, (rightConjugate_one F).symm⟩
  have hFH := conjSet_F_sec2H_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hEH := conjSet_E_sec2H_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have hdisj : ∀ V ∈ conjSet F H, V ∉ conjSet E H := fun V hV hV' => by
    rw [hFH] at hV
    rw [hEH] at hV'
    exact not_mem_sec2Fam_of_mem_sec2Fam h11 hE16 hF hL hodd hx hxS hh hhS hV hV'
  have hperm : ∀ V ∈ conjSet F H, rightConjugate V n ∈ conjSet F H := by
    rcases image_conjSet_sec2H_eq_or h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hnS with h1 | h1
    · exact fun V hV => h1 ▸ ⟨V, hV, rfl⟩
    · exfalso
      have hFn : rightConjugate F n ∈ conjSet E H := h1 ▸ ⟨F, hFmem, rfl⟩
      have h2 := (rightConjugate_eq_self_iff _ n⁻¹).mpr (inv_mem (hfixE _ hFn))
      rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h2
      exact hdisj F hFmem (h2 ▸ hFn)
  intro V hV
  by_contra hVn
  have hne : V ≠ rightConjugate V n := fun h => hVn ((rightConjugate_eq_self_iff _ n).mp h.symm)
  obtain ⟨q, hq, hqV, hqV'⟩ :=
    exists_mem_sec2H_mem_normalizer_not_mem h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hV
      (hperm V hV) hne
  apply hqV'
  obtain ⟨c, hcdef⟩ : ∃ c, c = n⁻¹ * q⁻¹ * n * q := ⟨_, rfl⟩
  have hcS : c ∈ normalizer (rightConjugate V n : Set G) :=
    (hSN _ (Or.inr (hperm V hV))) (hcdef ▸ hcomm q hq)
  rw [← (rightConjugate_eq_self_iff _ q)]
  have e : n * q = q * n * c := by rw [hcdef]; group
  calc rightConjugate (rightConjugate V n) q = rightConjugate V (n * q) := rightConjugate_mul V n q
    _ = rightConjugate (rightConjugate (rightConjugate V q) n) c := by
        rw [e]
        simp only [rightConjugate_mul, mul_assoc]
    _ = rightConjugate (rightConjugate V n) c := by rw [(rightConjugate_eq_self_iff V q).mpr hqV]
    _ = rightConjugate V n := (rightConjugate_eq_self_iff _ c).mpr hcS

theorem exists_mem_conjSet_not_mem_normalizer {u : G}
    (huA' : u ∈ A ⊓ normalizer (sec2S A R E F : Set G)) (hu3 : orderOf u = 3)
    (huE' : ∃ e ∈ E, u⁻¹ * e * u ≠ e) :
    ∃ V ∈ conjSet E (sec2H E F), u ∉ normalizer (V : Set G) := by
  by_contra hall
  push Not at hall
  set H := sec2H E F with hHdef
  obtain ⟨huE, -, huEF, hufix⟩ := sec2U_facts h11 hE16 hF hL hodd huA' hu3 huE'
  have huA : u ∈ A := huA'.1
  set C := centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) with hCdef
  have hF₀'mem : sec2F0 A F h ∈ conjSet E H := by
    rw [conjSet_E_sec2H_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4']
    exact Set.mem_insert _ _
  have hC := sec2P_inf_normalizer_sec2F0_symm_eq h11 hE16 hF hL hodd hh hhS h4'
  have hPN := sec2P_le_normalizer_centralizerMod h11 hE16 hF hL hodd
  have huP : u ∈ normalizer (sec2P E : Set G) := Sec2.normalizer_le_normalizer_sec2P E huE
  have hfix' : ∀ w ∈ E ⊓ F ⊓ A, u⁻¹ * w * u⁻¹⁻¹ = w → w = 1 := fun w hw h1 => by
    refine hufix w (hF.sec2Z_eq ▸ hw) ?_
    calc u * w * u⁻¹ = u * (u⁻¹ * w * u⁻¹⁻¹) * u⁻¹ := by rw [h1]
      _ = w := by group
  have hP : ∀ p ∈ sec2P E, p ∈ C := by
    intro p hp
    have hVp : rightConjugate (sec2F0 A F h) p ∈ conjSet E H := by
      obtain ⟨θ, hθ, hθe⟩ := hF₀'mem
      refine ⟨θ * p, mul_mem hθ (mem_sup_left hp), ?_⟩
      rw [hθe, rightConjugate_mul]
    have h1 := (rightConjugate_eq_self_iff _ u).mpr (hall _ hVp)
    have h2 := hall _ hF₀'mem
    have e1 : rightConjugate (sec2F0 A F h) (u⁻¹ * p * u) = rightConjugate (sec2F0 A F h) p := by
      rw [rightConjugate_mul] at h1
      rw [show u⁻¹ * p * u = u⁻¹ * (p * u) by group, ← rightConjugate_mul,
        (rightConjugate_eq_self_iff _ u⁻¹).mpr (inv_mem h2), h1]
    have e2 : rightConjugate (sec2F0 A F h) (u⁻¹ * p * u * p⁻¹) = sec2F0 A F h := by
      rw [← rightConjugate_mul, e1, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
    have h3' : u⁻¹ * p * u * p⁻¹ ∈ sec2P E ⊓ normalizer (sec2F0 A F h : Set G) := by
      refine ⟨(sec2P E).mul_mem ?_ ((sec2P E).inv_mem hp),
        (rightConjugate_eq_self_iff _ _).mp e2⟩
      simpa using (mem_normalizer_iff.mp (inv_mem huP) p).mp hp
    have h3 : u⁻¹ * p * u * p⁻¹ ∈ C := by
      rw [hC] at h3'
      exact h3'
    have h4 : p⁻¹ * (u⁻¹ * p * u⁻¹⁻¹) ∈ C := by
      have := (mem_normalizer_iff.mp (hPN (inv_mem hp)) _).mp h3
      simpa [mul_assoc] using this
    exact mem_centralizerMod_of_conj_mem h11 hE16 hF hL hodd (A.inv_mem huA) (inv_mem huE)
      (inv_mem huEF) hfix' hp h4
  exact hhS (mem_sup_right (hP h hh))


theorem exists_sec2Y {u : G} (huA : u ∈ A ⊓ normalizer (sec2S A R E F : Set G))
    (hu3 : orderOf u = 3) (huE : ∃ e ∈ E, u⁻¹ * e * u ≠ e) :
    ∃ y : G, y ∈ sec2H E F ⊓ normalizer (R : Set G) ⊓ centralizer ({u} : Set G) ∧
      orderOf y = 3 := by
  classical
  set H := sec2H E F with hHdef
  obtain ⟨huEn, -, -, -⟩ := sec2U_facts h11 hE16 hF hL hodd huA hu3 huE
  have huH := sec2U_mem_normalizer_sec2H h11 hE16 hF hL hodd huA hu3 huE
  have hu3' : u ^ 3 = 1 := by rw [← hu3]; exact pow_orderOf_eq_one u
  have hS2 : IsPGroup 2 (sec2S A R E F) := (isSylowOf_sec2S h11 hE16 hF hL hodd).isPGroup
  have hSH := sec2S_le_sec2H hF
  set X := Sec2.conjSetStab (conjSet E H) with hXdef
  have huX : u ∈ X := Sec2.mem_conjSetStab_conjSet huEn huH
  have hHX : H ≤ X := Sec2.le_conjSetStab fun k hk V ⟨θ, hθ, hV⟩ =>
    ⟨θ * k, mul_mem hθ hk, by rw [hV, rightConjugate_mul]⟩
  set ψ := Sec2.conjPermHom (le_refl X) with hψ
  have hIE : InducesA5 H (conjSet E H) :=
    inducesA5_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have : Fintype ↥(conjSet E H) := Fintype.ofFinite _
  have hEmem : E ∈ conjSet E H := ⟨1, one_mem _, (rightConjugate_one E).symm⟩
  set σ := ψ ⟨u, huX⟩ with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow, show (⟨u, huX⟩ : ↥X) ^ 3 = 1 from Subtype.ext (by simpa using hu3'),
      map_one]
  have hσ1 : σ ≠ 1 := fun h1 => by
    obtain ⟨V, hV, huV⟩ :=
      exists_mem_conjSet_not_mem_normalizer h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' huA hu3 huE
    exact huV ((Sec2.conjPermHom_eq_one_iff (le_refl X) _).mp h1 V hV)
  have hσo : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hσA : σ ∈ alternatingGroup ↥(conjSet E H) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    have h := congrArg Equiv.Perm.sign hσ3
    rw [map_pow, map_one] at h
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h' | h'
    · exact h'
    · rw [h'] at h
      exact absurd h (by decide)
  have hcard := Sec2.card_range_conjPermHom hHX hIE
  have hperm : Nat.card (Equiv.Perm ↥(conjSet E H)) = 120 := by
    rw [Nat.card_perm, hIE.1]
    decide
  have hidx : (Sec2.conjPermHom hHX).range.index = 2 := by
    have := (Sec2.conjPermHom hHX).range.index_mul_card
    rw [hcard, hperm] at this
    omega
  obtain ⟨⟨h₀, hh₀⟩, hh₀σ⟩ :=
    ((Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx).symm ▸ hσA :
      σ ∈ (Sec2.conjPermHom hHX).range)
  have hψh₀ : ψ ⟨h₀, hHX hh₀⟩ = σ := by
    rw [← hh₀σ]
    exact Equiv.ext fun V => Subtype.ext rfl
  have hc : h₀⁻¹ * u * h₀ * u⁻¹ ∈ sec2S A R E F := by
    have hcH : h₀⁻¹ * u * h₀ * u⁻¹ ∈ H := by
      have := H.mul_mem (H.inv_mem hh₀) ((mem_normalizer_iff.mp huH h₀).mp hh₀)
      simpa [mul_assoc] using this
    refine mem_sec2S_of_forall h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hcH fun V hV => ?_
    have h1 : ψ ⟨h₀⁻¹ * u * h₀ * u⁻¹, hHX hcH⟩ = 1 := by
      have e : (⟨h₀⁻¹ * u * h₀ * u⁻¹, hHX hcH⟩ : ↥X) =
          (⟨h₀, hHX hh₀⟩ : ↥X)⁻¹ * ⟨u, huX⟩ * ⟨h₀, hHX hh₀⟩ * (⟨u, huX⟩ : ↥X)⁻¹ :=
        Subtype.ext (by simp)
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hψh₀, ← hσ]
      group
    exact (Sec2.conjPermHom_eq_one_iff (le_refl X) _).mp h1 V hV
  obtain ⟨s, hs, hus⟩ := Sec2.exists_mem_commute_of_pow_three hS2 hu3' huA.2 hc
  have hh'H : h₀ * s ∈ H := H.mul_mem hh₀ (hSH hs)
  have hψs : ψ ⟨s, hHX (hSH hs)⟩ = 1 := by
    obtain ⟨hpl, -⟩ := planes_sec2S_facts h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
    refine (Sec2.conjPermHom_eq_one_iff (le_refl X) _).mpr fun V hV => ?_
    exact sec2S_le_normalizer_of_sec2Z_le h11 hE16 hF hL hodd (hpl V (Or.inl hV)).2.2.1
      (hpl V (Or.inl hV)).2.2.2 hs
  have hψh' : ψ ⟨h₀ * s, hHX hh'H⟩ = σ := by
    have e : (⟨h₀ * s, hHX hh'H⟩ : ↥X) = ⟨h₀, hHX hh₀⟩ * ⟨s, hHX (hSH hs)⟩ := rfl
    rw [e, map_mul, hψh₀, hψs, mul_one]
  have hh'E : h₀ * s ∈ normalizer (E : Set G) := by
    have h1 : ((σ ⟨E, hEmem⟩ : ↥(conjSet E H)) : Subgroup G) = E := by
      rw [hσ, Sec2.conjPermHom_apply]
      exact (rightConjugate_eq_self_iff _ _).mpr (inv_mem huEn)
    rw [← hψh', Sec2.conjPermHom_apply] at h1
    simpa using inv_mem ((rightConjugate_eq_self_iff _ _).mp h1)
  obtain ⟨e, m, hm3, hm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (h₀ * s)).ne' 3 (by norm_num)
  set y := (h₀ * s) ^ m with hy
  have hyH : y ∈ H := H.pow_mem hh'H m
  have hψy : ψ ⟨y, hHX hyH⟩ = σ ^ m := by
    rw [← hψh', ← map_pow]
    rfl
  have hyu : y * u = u * y := by
    have hc' : Commute (h₀ * s) u := hus.symm
    exact (hc'.pow_left m).eq
  have hy1 : y ≠ 1 := fun h1 => by
    have h2 : σ ^ m = 1 := by
      rw [← hψy]
      exact (Sec2.conjPermHom_eq_one_iff (le_refl X) _).mpr fun V _ => by
        simp only [h1]
        exact one_mem _
    exact hm3 (hσo ▸ orderOf_dvd_of_pow_eq_one h2)
  have hy3 : y ^ 3 = 1 := by
    have hy3H : y ^ 3 ∈ H := H.pow_mem hyH 3
    have hy3S : y ^ 3 ∈ sec2S A R E F := by
      refine mem_sec2S_of_forall h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hy3H
        ((Sec2.conjPermHom_eq_one_iff (le_refl X) ⟨y ^ 3, hHX hy3H⟩).mp ?_)
      have e : (⟨y ^ 3, hHX hy3H⟩ : ↥X) = (⟨y, hHX hyH⟩ : ↥X) ^ 3 := rfl
      rw [e, map_pow, hψy, ← pow_mul, mul_comm, pow_mul, hσ3, one_pow]
    obtain ⟨n, hn⟩ := hS2 ⟨y ^ 3, hy3S⟩
    have h2 : (y ^ 3) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h3 : (y ^ 3) ^ 3 ^ e = 1 := by
      rw [hy, ← pow_mul, ← pow_mul, show m * (3 * 3 ^ e) = 3 ^ e * m * 3 by ring, pow_mul, ← hm,
        pow_orderOf_eq_one, one_pow]
    have hcop : Nat.Coprime (2 ^ n) (3 ^ e) :=
      Nat.Coprime.pow _ _ (by norm_num)
    have h4 : orderOf (y ^ 3) = 1 := Nat.eq_one_of_dvd_one (hcop ▸
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3))
    exact orderOf_eq_one_iff.mp h4
  have hyE : y ∈ normalizer (E : Set G) := (normalizer (E : Set G)).pow_mem hh'E m
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hyR : y ∈ normalizer (R : Set G) := mem_normalizer_fintype fun r hr => by
    have hre : y * r * y⁻¹ ∈ E := (mem_normalizer_iff.mp hyE r).mp (hF.R_le_E hr)
    refine mem_of_commute_of_sec2U h11 hE16 hF hL hodd huA hu3 huE hre ?_
    have hur : u * r = r * u := mem_centralizer_iff.mp (hRA hr) u huA.1
    have hyu' : u * y⁻¹ = y⁻¹ * u := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hyu, ← mul_assoc, inv_mul_cancel, one_mul]
    calc u * (y * r * y⁻¹) = y * (u * r) * y⁻¹ := by rw [← mul_assoc, ← mul_assoc, ← hyu]; group
      _ = y * r * (u * y⁻¹) := by rw [hur]; group
      _ = y * r * y⁻¹ * u := by rw [hyu']; group
  exact ⟨y, ⟨⟨hyH, hyR⟩, mem_centralizer_singleton_iff.mpr hyu⟩, orderOf_eq_prime hy3 hy1⟩

theorem step27_core {u ξ : G} (hufix : ∀ w ∈ sec2Z A E F, u * w * u⁻¹ = w → w = 1)
    (hξS : ξ ∈ normalizer (sec2S A R E F : Set G)) (hξH : ξ ∈ normalizer (sec2H E F : Set G))
    (hξfix : ∀ V ∈ conjSet E (sec2H E F), ξ ∈ normalizer (V : Set G))
    (hξu : ∀ w ∈ sec2Z A E F, ξ * w * ξ⁻¹ = u * w * u⁻¹) (hξ3 : ξ ^ 3 = 1) :
    ξ ≠ 1 ∧ ActsAsF4Scalar ξ (sec2S A R E F) (sec2Z A E F) ∧
      closure {c | ∃ w ∈ sec2Z A E F, c = w⁻¹ * ξ⁻¹ * w * ξ} = sec2Z A E F ∧
      ∀ q ∈ sec2H E F, ξ⁻¹ * q⁻¹ * ξ * q ∈ sec2S A R E F := by
  have hZ := centerIn_sec2S_eq h11 hE16 hF hL hodd
  have hξZ : ξ ∈ normalizer (sec2Z A E F : Set G) := by
    rw [← hZ]
    exact mem_normalizer_centerIn hξS
  obtain ⟨hcomm, hfixF⟩ :=
    forall_mem_normalizer_F_of_mem h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hξS hξH hξfix
  have hfpf : ∀ w ∈ sec2Z A E F, ξ⁻¹ * w * ξ = w → w = 1 := fun w hw h1 => by
    refine hufix w hw ?_
    rw [← hξu w hw]
    calc ξ * w * ξ⁻¹ = ξ * (ξ⁻¹ * w * ξ) * ξ⁻¹ := by rw [h1]
      _ = w := by group
  have hZ1 : sec2Z A E F ≠ ⊥ := fun h => by
    have := hF.card_sec2Z hodd
    rw [h, card_bot] at this
    omega
  obtain ⟨⟨w₀, hw₀⟩, hw₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ1
  have hn : ¬ ∀ s ∈ sec2S A R E F, s⁻¹ * (ξ⁻¹ * s * ξ) ∈ sec2Z A E F := fun hall => by
    have hC := mem_centralizer_sec2Z_of_forall h11 hE16 hF hL hodd hall
    have h1 : ξ⁻¹ * w₀ * ξ = w₀ := by
      rw [mul_assoc, mem_centralizer_iff.mp hC w₀ hw₀]
      group
    exact hw₀1 (Subtype.ext (hfpf w₀ hw₀ h1))
  refine ⟨fun h1 => hn fun s hs => by rw [h1]; simp, actsAsF4Scalar_of_fix h11 hE16 hF hL hodd
    hx hxS hh hhS h4 h4' hξS hξZ hξfix hfixF hn hξ3, ?_, hcomm⟩
  have hcZ : ∀ w ∈ sec2Z A E F, ξ⁻¹ * w * ξ ∈ sec2Z A E F := fun w hw => by
    simpa using (mem_normalizer_iff.mp (inv_mem hξZ) w).mp hw
  refine le_antisymm ((closure_le _).mpr ?_) (fun z hz => ?_)
  · rintro _ ⟨w, hw, rfl⟩
    have := (sec2Z A E F).mul_mem ((sec2Z A E F).inv_mem hw) (hcZ w hw)
    simpa [mul_assoc] using this
  · let φ : ↥(sec2Z A E F) → ↥(sec2Z A E F) := fun w =>
      ⟨(w : G)⁻¹ * (ξ⁻¹ * w * ξ), (sec2Z A E F).mul_mem ((sec2Z A E F).inv_mem w.2)
        (hcZ w w.2)⟩
    have hφ : Function.Injective φ := fun w₁ w₂ h12 => by
      have h' : (w₁ : G)⁻¹ * (ξ⁻¹ * w₁ * ξ) = (w₂ : G)⁻¹ * (ξ⁻¹ * w₂ * ξ) :=
        congrArg Subtype.val h12
      have hw₂ := (sec2Z A E F).inv_mem w₂.2
      have e2 : ξ⁻¹ * w₁ * ξ = w₁ * ((w₂ : G)⁻¹ * (ξ⁻¹ * w₂ * ξ)) := by
        calc ξ⁻¹ * w₁ * ξ = w₁ * ((w₁ : G)⁻¹ * (ξ⁻¹ * w₁ * ξ)) := by group
          _ = w₁ * ((w₂ : G)⁻¹ * (ξ⁻¹ * w₂ * ξ)) := by rw [h']
      have hfix : ξ⁻¹ * ((w₁ : G) * (w₂ : G)⁻¹) * ξ = (w₁ : G) * (w₂ : G)⁻¹ := by
        calc ξ⁻¹ * ((w₁ : G) * (w₂ : G)⁻¹) * ξ = (ξ⁻¹ * w₁ * ξ) * (ξ⁻¹ * w₂ * ξ)⁻¹ := by group
          _ = (w₁ * ((w₂ : G)⁻¹ * (ξ⁻¹ * w₂ * ξ))) * (ξ⁻¹ * w₂ * ξ)⁻¹ := by rw [e2]
          _ = (w₁ : G) * (w₂ : G)⁻¹ := by group
      have h1 := hfpf _ ((sec2Z A E F).mul_mem w₁.2 hw₂) hfix
      exact Subtype.ext (mul_inv_eq_one.mp h1)
    obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.mp hφ) ⟨z, hz⟩
    apply Subgroup.subset_closure
    refine ⟨w, w.2, ?_⟩
    have := congrArg Subtype.val hw
    simp only [φ] at this
    rw [← this]
    group

theorem exists_xi_of_sec2UY {u y : G} (huy : Sec2UY A R E F u y) :
    ∃ ξ : G, orderOf ξ = 3 ∧ (u = ξ * y ∨ u = ξ * y⁻¹) ∧
      ActsAsF4Scalar ξ (sec2S A R E F) (sec2Z A E F) ∧
      closure {c | ∃ w ∈ sec2Z A E F, c = w⁻¹ * ξ⁻¹ * w * ξ} = sec2Z A E F ∧
      ξ ∈ normalizer (sec2H E F : Set G) ∧
      (∀ q ∈ sec2H E F, ξ⁻¹ * q⁻¹ * ξ * q ∈ sec2S A R E F) ∧
      (∀ V ∈ conjSet E (sec2H E F), ξ ∈ normalizer (V : Set G)) ∧
      ∀ V ∈ conjSet F (sec2H E F), ξ ∈ normalizer (V : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := sec2H E F with hHdef
  obtain ⟨huA', hu3, huE, ⟨⟨hyH, -⟩, hyu⟩, hy3⟩ := id huy
  have huS := huA'.2
  obtain ⟨huEn, -, -, hufix⟩ := sec2U_facts h11 hE16 hF hL hodd huA' hu3 huE
  have huH := sec2U_mem_normalizer_sec2H h11 hE16 hF hL hodd huA' hu3 huE
  have hyu' : y * u = u * y := mem_centralizer_singleton_iff.mp hyu
  have hHS := sec2H_le_normalizer_sec2S h11 hE16 hF hL hodd
  have hHC := sec2H_le_centralizer_sec2Z h11 hE16 hF hL hodd
  set X := Sec2.conjSetStab (conjSet E H) with hXdef
  have huX : u ∈ X := Sec2.mem_conjSetStab_conjSet huEn huH
  have hHX : H ≤ X := Sec2.le_conjSetStab fun k hk V ⟨θ, hθ, hV⟩ =>
    ⟨θ * k, mul_mem hθ hk, by rw [hV, rightConjugate_mul]⟩
  set ψ := Sec2.conjPermHom (le_refl X) with hψ
  have hIE : InducesA5 H (conjSet E H) :=
    inducesA5_sec2H h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  have : Fintype ↥(conjSet E H) := Fintype.ofFinite _
  have h5 : Fintype.card ↥(conjSet E H) = 5 := by rw [Fintype.card_eq_nat_card]; exact hIE.1
  set σ := ψ ⟨u, huX⟩ with hσ
  set τ := ψ ⟨y, hHX hyH⟩ with hτ
  have hu3' : u ^ 3 = 1 := by rw [← hu3]; exact pow_orderOf_eq_one u
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow, show (⟨u, huX⟩ : ↥X) ^ 3 = 1 from Subtype.ext (by simpa using hu3'),
      map_one]
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτ, ← map_pow, show (⟨y, hHX hyH⟩ : ↥X) ^ 3 = 1 from Subtype.ext (by simpa using hy3'),
      map_one]
  have hσ1 : σ ≠ 1 := fun h1 => by
    obtain ⟨V, hV, huV⟩ :=
      exists_mem_conjSet_not_mem_normalizer h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' huA' hu3 huE
    exact huV ((Sec2.conjPermHom_eq_one_iff (le_refl X) _).mp h1 V hV)
  have hτ1 : τ ≠ 1 := fun h1 => by
    have hyS := mem_sec2S_of_forall h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hyH
      ((Sec2.conjPermHom_eq_one_iff (le_refl X) _).mp h1)
    have hS2 : IsPGroup 2 (sec2S A R E F) := (isSylowOf_sec2S h11 hE16 hF hL hodd).isPGroup
    obtain ⟨k, hk⟩ := hS2 ⟨y, hyS⟩
    have hyk : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h3 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hyk
    rw [hy3] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  have hστ : σ * τ = τ * σ := by
    rw [hσ, hτ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyu'.symm
  have key : ∀ ε : ℤ, ψ (⟨u, huX⟩ * ⟨y, hHX hyH⟩ ^ ε) = 1 →
      ∃ ξ : G, ξ = u * y ^ ε ∧ orderOf ξ = 3 ∧
        ActsAsF4Scalar ξ (sec2S A R E F) (sec2Z A E F) ∧
        closure {c | ∃ w ∈ sec2Z A E F, c = w⁻¹ * ξ⁻¹ * w * ξ} = sec2Z A E F ∧
        ξ ∈ normalizer (sec2H E F : Set G) ∧
        (∀ q ∈ sec2H E F, ξ⁻¹ * q⁻¹ * ξ * q ∈ sec2S A R E F) ∧
        (∀ V ∈ conjSet E (sec2H E F), ξ ∈ normalizer (V : Set G)) ∧
        ∀ V ∈ conjSet F (sec2H E F), ξ ∈ normalizer (V : Set G) := by
    intro ε hψξ
    have hξfix : ∀ V ∈ conjSet E H, u * y ^ ε ∈ normalizer (V : Set G) := fun V hV => by
      have := (Sec2.conjPermHom_eq_one_iff (le_refl X) _).mp hψξ V hV
      simpa using this
    have hyε : y ^ ε ∈ H := H.zpow_mem hyH ε
    have hξS : u * y ^ ε ∈ normalizer (sec2S A R E F : Set G) := mul_mem huS (hHS hyε)
    have hξH : u * y ^ ε ∈ normalizer (sec2H E F : Set G) := mul_mem huH (le_normalizer hyε)
    have hξu : ∀ w ∈ sec2Z A E F, u * y ^ ε * w * (u * y ^ ε)⁻¹ = u * w * u⁻¹ := fun w hw => by
      have h1 : y ^ ε * w = w * y ^ ε := (mem_centralizer_iff.mp (hHC hyε) w hw).symm
      calc u * y ^ ε * w * (u * y ^ ε)⁻¹ = u * (y ^ ε * w) * (y ^ ε)⁻¹ * u⁻¹ := by group
        _ = u * (w * y ^ ε) * (y ^ ε)⁻¹ * u⁻¹ := by rw [h1]
        _ = u * w * u⁻¹ := by group
    have hξ3 : (u * y ^ ε) ^ 3 = 1 := by
      have hc : Commute u (y ^ ε) := (Commute.zpow_right (Commute.symm hyu') ε)
      rw [hc.mul_pow, hu3', one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hy3', one_zpow]
    obtain ⟨hξ1, hF4, hcl, hcomm⟩ := step27_core h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hufix
      hξS hξH hξfix hξu hξ3
    exact ⟨_, rfl, orderOf_eq_prime hξ3 hξ1, hF4, hcl, hξH, hcomm, hξfix,
      (forall_mem_normalizer_F_of_mem h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' hξS hξH
        hξfix).2⟩
  rcases Sec2.eq_or_eq_inv_of_commute_of_pow_three h5 hσ3 hσ1 hτ3 hτ1 hστ with h1 | h1
  · obtain ⟨ξ, hξ, rest⟩ := key (-1) (by rw [map_mul, map_zpow, ← hσ, ← hτ, h1]; group)
    exact ⟨ξ, rest.1, Or.inl (by rw [hξ]; group), rest.2⟩
  · obtain ⟨ξ, hξ, rest⟩ := key 1 (by rw [map_mul, map_zpow, ← hσ, ← hτ, h1]; group)
    exact ⟨ξ, rest.1, Or.inr (by rw [hξ]; group), rest.2⟩

theorem exists_of_sec2UY {u y : G} (huy : Sec2UY A R E F u y) :
    ∃ ξ : G, orderOf ξ = 3 ∧ (u = ξ * y ∨ u = ξ * y⁻¹) ∧
      ActsAsF4Scalar ξ (sec2S A R E F) (sec2Z A E F) ∧
      closure {c | ∃ w ∈ sec2Z A E F, c = w⁻¹ * ξ⁻¹ * w * ξ} = sec2Z A E F ∧
      ξ ∈ normalizer (sec2H E F : Set G) ∧
      ∀ q ∈ sec2H E F, ξ⁻¹ * q⁻¹ * ξ * q ∈ sec2S A R E F := by
  obtain ⟨ξ, k1, k2, k3, k4, k5, k6, -, -⟩ :=
    exists_xi_of_sec2UY h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' huy
  exact ⟨ξ, k1, k2, k3, k4, k5, k6⟩

theorem exists_sec2UY : ∃ u y : G, Sec2UY A R E F u y := by
  obtain ⟨u, huA, hu3, huE⟩ := exists_sec2U hF hL hodd
  obtain ⟨y, hy, hy3⟩ := exists_sec2Y h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' huA hu3 huE
  exact ⟨u, y, huA, hu3, huE, hy, hy3⟩

end FrameXH

theorem step27_of (h11 : Step11)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (h22iv : Step22iv) : Step27 := by
  intro G _ _ A R g E F hS
  have hF := hS.frame
  have hL := hS.type
  have hodd := hS.odd
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  have h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)) :=
    h22iv G A R g F E ⟨hF.symm, hL, hodd, hS.below⟩
  have h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E)) := h22iv G A R g E F hS
  obtain ⟨h, hh, hhC⟩ := exists_mem_sec2P_not_mem_centralizerMod h11 hE16 hF hL hodd
  have hhS : h ∉ sec2S A R E F := fun hS' => hhC (by
    rw [← sec2S_inf_sec2P h11 hE16 hF hL hodd]
    exact ⟨hS', hh⟩)
  obtain ⟨x, hx, hxC⟩ := exists_mem_sec2P_not_mem_centralizerMod h11 hE16 hF.symm hL hodd
  have hxS : x ∉ sec2S A R E F := fun hS' => hxC (by
    rw [← sec2S_inf_sec2P h11 hE16 hF.symm hL hodd, hSc]
    exact ⟨hS', hx⟩)
  exact ⟨exists_sec2UY h11 hE16 hF hL hodd hx hxS hh hhS h4 h4',
    fun u y huy => exists_of_sec2UY h11 hE16 hF hL hodd hx hxS hh hhS h4 h4' huy⟩

end CFSG.ComponentClassification.AS81
