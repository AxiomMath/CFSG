module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Two5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Two

open Subgroup
open Matrix
open CFSG.Open
open CFSG.Blueprint.Chevalley
open CFSG.SeitzReduction.E6Pilot
open CFSG.SeitzReduction.LinearPilot
open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private abbrev I01 : Finset (Fin 6) := {0, 1}

private abbrev I23 : Finset (Fin 6) := {2, 3}

private abbrev I45 : Finset (Fin 6) := {4, 5}

private abbrev I0123 : Finset (Fin 6) := I45ᶜ

private theorem I45_card : I45.card = 2 := by decide

private theorem I23_card : I23.card = 2 := by decide

private theorem I0123_card : I0123.card = 4 := by decide

private theorem disjoint_I01_I23 : Disjoint I01 I23 := by decide

private theorem I01_subset_I0123 : I01 ⊆ I0123 := by decide

private theorem I23_subset_I0123 : I23 ⊆ I0123 := by decide

private theorem disjoint_I0123_I45 : Disjoint I0123 I45 := by decide

omit [CharP K 2] in
private theorem blockSpecialLinear_inf_eq_bot_of_disjoint {F : Type*} [Field F]
    {I J : Finset (Fin 6)} (h : Disjoint I J) :
    blockSpecialLinear (K := F) I ⊓ blockSpecialLinear J = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hg
  refine Subgroup.mem_bot.2 (Subtype.ext (Matrix.ext fun i j => ?_))
  by_cases hi : i ∈ I
  · rw [mem_blockSpecialLinear.1 h2 i j
      (Or.inl (Finset.disjoint_left.1 h hi))]
    rfl
  · rw [mem_blockSpecialLinear.1 h1 i j (Or.inl hi)]
    rfl

private theorem blockSL_inf_eq_bot_of_disjoint_of_card_two
    {I J : Finset (Fin 6)} (h : Disjoint I J) (hJ : J.card = 2) :
    blockSL (K := K) I ⊓ blockSL (K := K) J = ⊥ := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hJ
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxI, hxJ⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨A, hA, hAx⟩ := mem_blockSL.1 hxI
  obtain ⟨B, hB, hBx⟩ := mem_blockSL.1 hxJ
  have hAB : A⁻¹ * B ∈ LinearFlag.scalars 6 K :=
    LinearFlag.proj_eq_proj_iff.1 (hAx.trans hBx.symm)
  obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.1 hAB
  have hc' : ((A⁻¹ * B : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      Matrix.diagonal (fun _ : Fin 6 => (c : K)) := by
    rw [hc, Matrix.scalar_apply]
  have hBA : (B : Matrix (Fin 6) (Fin 6) K) =
      (A : Matrix (Fin 6) (Fin 6) K) * Matrix.diagonal (fun _ : Fin 6 => (c : K)) := by
    have h1 : (B : Matrix (Fin 6) (Fin 6) K) =
        (A * (A⁻¹ * B) : Matrix.SpecialLinearGroup (Fin 6) K).1 :=
      congrArg Subtype.val (show B = A * (A⁻¹ * B) from by group)
    have h2 : (A * (A⁻¹ * B) : Matrix.SpecialLinearGroup (Fin 6) K).1 =
        (A : Matrix (Fin 6) (Fin 6) K) * (A⁻¹ * B : Matrix.SpecialLinearGroup (Fin 6) K).1 :=
      Matrix.SpecialLinearGroup.coe_mul A (A⁻¹ * B)
    rw [h1, h2, hc']
  have hAentry : ∀ i ∈ ({a, b} : Finset (Fin 6)), ∀ j ∈ ({a, b} : Finset (Fin 6)),
      (A : Matrix (Fin 6) (Fin 6) K) i j = (1 : Matrix (Fin 6) (Fin 6) K) i j := by
    intro i hi j hj
    exact mem_blockSpecialLinear.1 hA i j
      (Or.inl (Finset.disjoint_right.1 h hi))
  have hBaa : (B : Matrix (Fin 6) (Fin 6) K) a a = (c : K) := by
    rw [hBA, Matrix.mul_diagonal,
      hAentry a (by simp) a (by simp), Matrix.one_apply_eq, one_mul]
  have hBbb : (B : Matrix (Fin 6) (Fin 6) K) b b = (c : K) := by
    rw [hBA, Matrix.mul_diagonal,
      hAentry b (by simp) b (by simp), Matrix.one_apply_eq, one_mul]
  have hBab : (B : Matrix (Fin 6) (Fin 6) K) a b = 0 := by
    rw [hBA, Matrix.mul_diagonal,
      hAentry a (by simp) b (by simp), Matrix.one_apply_ne hab, zero_mul]
  have hBba : (B : Matrix (Fin 6) (Fin 6) K) b a = 0 := by
    rw [hBA, Matrix.mul_diagonal,
      hAentry b (by simp) a (by simp), Matrix.one_apply_ne hab.symm, zero_mul]
  have hdet := det_eq_of_agrees_one_pair (K := K) (n := 6) hab
    (mem_blockSpecialLinear.1 hB)
  rw [hBaa, hBbb, hBab, hBba] at hdet
  have hdet1 : (B : Matrix (Fin 6) (Fin 6) K).det = 1 := B.2
  rw [hdet1] at hdet
  have hc2 : (c : K) ^ 2 = 1 := by
    simpa [pow_two] using hdet.symm
  have hc1 : c = 1 := Units.ext (eq_one_of_sq_eq_one hc2)
  have hAB1 : A⁻¹ * B = 1 := by
    apply Subtype.ext
    rw [hc', hc1]
    simp
  have hBAeq : B = A := by
    calc B = A * (A⁻¹ * B) := by group
      _ = A * 1 := by rw [hAB1]
      _ = A := mul_one A
  have hA1 : A = 1 := by
    have hmem : A ∈ blockSpecialLinear (K := K) I ⊓
        blockSpecialLinear (K := K) ({a, b} : Finset (Fin 6)) := by
      refine ⟨hA, ?_⟩
      rw [← hBAeq]
      exact hB
    rw [blockSpecialLinear_inf_eq_bot_of_disjoint (F := K) h, Subgroup.mem_bot] at hmem
    exact hmem
  have hB1 : B = 1 := hBAeq.trans hA1
  rw [← hBx, hB1, map_one]
  simp

private theorem exists_mem_blockSL_orderOf_eq_prime {a b : Fin 6} (hab : a ≠ b) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) :
    ∃ x : LinearFlag.projectiveSL 6 K, x ∈ blockSL (K := K) ({a, b} : Finset (Fin 6)) ∧
      orderOf x = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, hXle, -, hXcard⟩ := exists_torusQ1 (K := K) (n := 6) hab
  have hpX : p ∣ Nat.card X := by rw [hXcard]; exact hpq
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := X) p hpX
  exact ⟨x, hXle x.2, (Subgroup.orderOf_coe x).trans hxord⟩

private theorem centralizer_sup_eq_inf_centralizer {G : Type*} [Group G] (A B : Subgroup G) :
    Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) := by
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  ext z
  constructor
  · intro hz
    exact ⟨fun a ha => hz a (Or.inl ha), fun b hb => hz b (Or.inr hb)⟩
  · rintro ⟨hA, hB⟩ x (hx | hx)
    · exact hA x hx
    · exact hB x hx

private theorem isElemAbelian_zpowers_sup_three {x₁ x₂ x₃ : LinearFlag.projectiveSL 6 K} {p : ℕ}
    (h₁ : x₁ ∈ blockSL (K := K) I01) (h₂ : x₂ ∈ blockSL (K := K) I23)
    (h₃ : x₃ ∈ blockSL (K := K) I45)
    (ho₁ : orderOf x₁ = p) (ho₂ : orderOf x₂ = p) (ho₃ : orderOf x₃ = p) :
    IsElemAbelian p
        ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃ :
          Subgroup (LinearFlag.projectiveSL 6 K))) ∧
      Nat.card ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃ :
        Subgroup (LinearFlag.projectiveSL 6 K))) = p ^ 3 := by
  have hz1 : Subgroup.zpowers x₁ ≤ blockSL (K := K) I01 := Subgroup.zpowers_le.mpr h₁
  have hz2 : Subgroup.zpowers x₂ ≤ blockSL (K := K) I23 := Subgroup.zpowers_le.mpr h₂
  have hz3 : Subgroup.zpowers x₃ ≤ blockSL (K := K) I45 := Subgroup.zpowers_le.mpr h₃
  have hcard1 : Nat.card (Subgroup.zpowers x₁) = p := by rw [Nat.card_zpowers, ho₁]
  have hcard2 : Nat.card (Subgroup.zpowers x₂) = p := by rw [Nat.card_zpowers, ho₂]
  have hcard3 : Nat.card (Subgroup.zpowers x₃) = p := by rw [Nat.card_zpowers, ho₃]
  have hcomm12 : ∀ a ∈ Subgroup.zpowers x₁, ∀ b ∈ Subgroup.zpowers x₂, a * b = b * a := by
    intro a ha b hb
    exact (commute_blockSL_of_disjoint (K := K) disjoint_I01_I23 a (hz1 ha) b (hz2 hb)).eq
  have hcomm13 : ∀ a ∈ Subgroup.zpowers x₁, ∀ b ∈ Subgroup.zpowers x₃, a * b = b * a := by
    intro a ha b hb
    have hd : Disjoint I01 I45 := by decide
    exact (commute_blockSL_of_disjoint (K := K) hd a (hz1 ha) b (hz3 hb)).eq
  have hcomm23 : ∀ a ∈ Subgroup.zpowers x₂, ∀ b ∈ Subgroup.zpowers x₃, a * b = b * a := by
    intro a ha b hb
    have hd : Disjoint I23 I45 := by decide
    exact (commute_blockSL_of_disjoint (K := K) hd a (hz2 ha) b (hz3 hb)).eq
  have hinf12 : Subgroup.zpowers x₁ ⊓ Subgroup.zpowers x₂ = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
    have hy' : y ∈ blockSL (K := K) I01 ⊓ blockSL (K := K) I23 := ⟨hz1 hy1, hz2 hy2⟩
    rw [blockSL_inf_eq_bot_of_disjoint_of_card_two (K := K) disjoint_I01_I23 I23_card,
      Subgroup.mem_bot] at hy'
    simpa using hy'
  have hcard12 : Nat.card ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ :
      Subgroup (LinearFlag.projectiveSL 6 K))) = p ^ 2 := by
    have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (Subgroup.zpowers x₁) (Subgroup.zpowers x₂) hcomm12).1
    rw [hinf12, Subgroup.card_bot, hcard1, hcard2] at hc
    simpa [pow_two] using hc
  have h12I : Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ ≤ blockSL (K := K) I0123 :=
    sup_le (hz1.trans (blockSL_mono I01_subset_I0123))
      (hz2.trans (blockSL_mono I23_subset_I0123))
  have hinf3 : ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ :
      Subgroup (LinearFlag.projectiveSL 6 K))) ⊓ Subgroup.zpowers x₃ = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    obtain ⟨hy12, hy3⟩ := Subgroup.mem_inf.1 hy
    have hy' : y ∈ blockSL (K := K) I0123 ⊓ blockSL (K := K) I45 :=
      ⟨h12I hy12, hz3 hy3⟩
    rw [blockSL_inf_eq_bot_of_disjoint_of_card_two (K := K) disjoint_I0123_I45 I45_card,
      Subgroup.mem_bot] at hy'
    simpa using hy'
  have hcent3 : Subgroup.zpowers x₃ ≤ Subgroup.centralizer
      (((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) : Subgroup (LinearFlag.projectiveSL 6 K)) :
        Set (LinearFlag.projectiveSL 6 K)) := by
    rw [centralizer_sup_eq_inf_centralizer]
    refine le_inf ?_ ?_
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcomm13 a ha b hb
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcomm23 a ha b hb
  have hnorm3 : Subgroup.zpowers x₃ ≤ Subgroup.normalizer
      (((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) : Subgroup (LinearFlag.projectiveSL 6 K)) :
        Set (LinearFlag.projectiveSL 6 K)) :=
    hcent3.trans (Subgroup.centralizer_le_normalizer _)
  have hcard123 : Nat.card
      ((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃ :
        Subgroup (LinearFlag.projectiveSL 6 K))) = p ^ 3 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) (Subgroup.zpowers x₃) hnorm3
      (disjoint_iff.mpr hinf3), hcard12, hcard3]
    ring
  have hH1ea : IsElemAbelian p (Subgroup.zpowers x₁) :=
    isElemAbelian_zpowers (by rw [← ho₁]; exact pow_orderOf_eq_one x₁)
  have hH2ea : IsElemAbelian p (Subgroup.zpowers x₂) :=
    isElemAbelian_zpowers (by rw [← ho₂]; exact pow_orderOf_eq_one x₂)
  have hH3ea : IsElemAbelian p (Subgroup.zpowers x₃) :=
    isElemAbelian_zpowers (by rw [← ho₃]; exact pow_orderOf_eq_one x₃)
  have hH12ea : IsElemAbelian p (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) :=
    IsElemAbelian.sup_of_commute hH1ea hH2ea hcomm12
  have hcomm123 : ∀ a ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂,
      ∀ b ∈ Subgroup.zpowers x₃, a * b = b * a := by
    intro a ha b hb
    have hbC : b ∈ Subgroup.centralizer
        (((Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) : Subgroup
          (LinearFlag.projectiveSL 6 K)) : Set (LinearFlag.projectiveSL 6 K)) := hcent3 hb
    exact Subgroup.mem_centralizer_iff.1 hbC a ha
  have hH123ea : IsElemAbelian p
      (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃) :=
    IsElemAbelian.sup_of_commute hH12ea hH3ea hcomm123
  exact ⟨hH123ea, hcard123⟩

private theorem commutator_mem_blockSL_of_mem_centralizer_pow {a b : Fin 6} (hab : a ≠ b)
    {y : Matrix.SpecialLinearGroup (Fin 6) K}
    (hy : y ∈ blockSpecialLinear (K := K) ({a, b} : Finset (Fin 6)))
    (hyy : y * y ≠ 1)
    (hym : (LinearFlag.proj 6 K y) ^ (Nat.card K + 1) = 1)
    {g h : LinearFlag.projectiveSL 6 K}
    (hg : g ∈ Subgroup.centralizer
      ({LinearFlag.proj 6 K y} : Set (LinearFlag.projectiveSL 6 K)))
    (hh : h ∈ Subgroup.centralizer
      ({LinearFlag.proj 6 K y} : Set (LinearFlag.projectiveSL 6 K))) :
    g * h * g⁻¹ * h⁻¹ ∈ blockSL (K := K) ({a, b} : Finset (Fin 6))ᶜ := by
  have hlift : ∀ g ∈ Subgroup.centralizer
      ({LinearFlag.proj 6 K y} : Set (LinearFlag.projectiveSL 6 K)),
      ∃ A : Matrix.SpecialLinearGroup (Fin 6) K, LinearFlag.proj 6 K A = g ∧
        A ∈ Subgroup.centralizer ({y} : Set (Matrix.SpecialLinearGroup (Fin 6) K)) := by
    intro g hg
    obtain ⟨A, rfl⟩ := LinearFlag.proj_surjective 6 K g
    refine ⟨A, rfl, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_eq_mul_of_proj_commute
      (Subgroup.mem_centralizer_singleton_iff.1 hg) hym
  obtain ⟨A, rfl, hA⟩ := hlift g hg
  obtain ⟨B, rfl, hB⟩ := hlift h hh
  have hmem : A * B * A⁻¹ * B⁻¹ ∈ blockSpecialLinear (K := K) ({a, b} : Finset (Fin 6))ᶜ :=
    commutator_agrees_one_of_mem_centralizer hab (mem_blockSpecialLinear.1 hy) hyy hA hB
  have := proj_mem_blockSL hmem
  simpa only [map_mul, map_inv] using this

private theorem normal_blockSL_compl_of_centralizer_pow {a b : Fin 6} (hab : a ≠ b)
    {y : Matrix.SpecialLinearGroup (Fin 6) K}
    (hy : y ∈ blockSpecialLinear (K := K) ({a, b} : Finset (Fin 6)))
    (hyy : y * y ≠ 1)
    (hym : (LinearFlag.proj 6 K y) ^ (Nat.card K + 1) = 1)
    (hQle : blockSL (K := K) ({a, b} : Finset (Fin 6))ᶜ ≤ Subgroup.centralizer
      ({LinearFlag.proj 6 K y} : Set (LinearFlag.projectiveSL 6 K))) :
    ((blockSL (K := K) ({a, b} : Finset (Fin 6))ᶜ).subgroupOf
      (Subgroup.centralizer ({LinearFlag.proj 6 K y} :
        Set (LinearFlag.projectiveSL 6 K)))).Normal := by
  refine ⟨fun x hx c => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hcomm := commutator_mem_blockSL_of_mem_centralizer_pow hab hy hyy hym c.2 x.2
  have h1 : (c : LinearFlag.projectiveSL 6 K) * (x : LinearFlag.projectiveSL 6 K) *
      (c : LinearFlag.projectiveSL 6 K)⁻¹ =
      ((c : LinearFlag.projectiveSL 6 K) * (x : LinearFlag.projectiveSL 6 K) *
        (c : LinearFlag.projectiveSL 6 K)⁻¹ * (x : LinearFlag.projectiveSL 6 K)⁻¹) *
        (x : LinearFlag.projectiveSL 6 K) := by group
  rw [h1]
  exact (blockSL (K := K) ({a, b} : Finset (Fin 6))ᶜ).mul_mem hcomm hx

private theorem blockSL_I0123_le_centralizer {x : LinearFlag.projectiveSL 6 K}
    (hx : x ∈ blockSL (K := K) I45) :
    blockSL (K := K) I0123 ≤ Subgroup.centralizer ({x} : Set (LinearFlag.projectiveSL 6 K)) := by
  intro q hq
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (commute_blockSL_of_disjoint (K := K) disjoint_I0123_I45 q hq x hx).eq

private theorem isQuasisimple_blockSL_I0123 :
    CFSG.Open.IsQuasisimple ↥(blockSL (K := K) I0123) := by
  have hq : CFSG.IsQuasisimple ↥(blockSL (K := K) I0123) :=
    isQuasisimple_blockSL (K := K) (I := I0123) (n := 6)
      (by rw [I0123_card]; norm_num) (by rw [I0123_card]; norm_num)
      (Or.inl (by rw [I0123_card]; norm_num))
  exact ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩

private theorem dvd_card_blockSL_I0123 {p : ℕ} (hpq : p ∣ Nat.card K + 1) :
    p ∣ Nat.card (blockSL (K := K) I0123) := by
  obtain ⟨e⟩ := blockSL_mulEquiv (K := K) (I := I0123) (n := 6)
    (by rw [I0123_card]; norm_num)
  let e4 : blockSL (K := K) I0123 ≃*
      Matrix.SpecialLinearGroup (Fin 4) K :=
    e.trans (reindexSpecialLinear (K := K) (finCongr I0123_card))
  have hcard : Nat.card (blockSL (K := K) I0123) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 4) K) := Nat.card_congr e4.toEquiv
  rw [hcard, LinearFlag.card_SL_eq (K := K) (n := 4) (by norm_num)]
  have hpq' : p ∣ Nat.card K ^ 2 - 1 := by
    have h1 : Nat.card K + 1 ∣ Nat.card K ^ 2 - 1 := by
      have h : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
        simpa using Nat.sq_sub_sq (Nat.card K) 1
      rw [h]
      exact dvd_mul_right _ _
    exact hpq.trans h1
  have hprod : p ∣ ∏ j ∈ Finset.Icc 2 4, (Nat.card K ^ j - 1) :=
    hpq'.trans (Finset.dvd_prod_of_mem (fun j => Nat.card K ^ j - 1) (by simp))
  exact Dvd.dvd.mul_left hprod (Nat.card K ^ (4 * (4 - 1) / 2))

private theorem exists_lift_blockSL_I45 {p : ℕ} (hp3 : 3 ≤ p)
    (hpq : p ∣ Nat.card K + 1) {x : LinearFlag.projectiveSL 6 K}
    (hx : x ∈ blockSL (K := K) I45) (hxord : orderOf x = p) :
    ∃ y : Matrix.SpecialLinearGroup (Fin 6) K,
      y ∈ blockSpecialLinear (K := K) I45 ∧ LinearFlag.proj 6 K y = x ∧
      y * y ≠ 1 ∧ x ^ (Nat.card K + 1) = 1 := by
  obtain ⟨y, hy, hyx⟩ := mem_blockSL.1 hx
  have hyy : y * y ≠ 1 := by
    intro h
    have h1 : x * x = 1 := by rw [← hyx, ← map_mul, h, map_one]
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    rw [hxord] at h2
    exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
  have hxpow : x ^ (Nat.card K + 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hxord]
    exact hpq
  exact ⟨y, hy, hyx, hyy, hxpow⟩

private theorem normal_subgroupOf_map {G H : Type*} [Group G] [Group H] {f : G →* H}
    {Q C : Subgroup G} (hQC : Q ≤ C) (hQn : (Q.subgroupOf C).Normal) :
    ((Q.map f).subgroupOf (C.map f)).Normal := by
  refine ⟨fun x hx c => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.1 hx
  obtain ⟨d, hd, hde⟩ := Subgroup.mem_map.1 c.2
  have hmem : d * q * d⁻¹ ∈ Q := by
    have h := hQn.conj_mem (⟨q, hQC hq⟩ : ↥C) hq ⟨d, hd⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  rw [← hqx, ← hde]
  refine Subgroup.mem_map.2 ⟨d * q * d⁻¹, hmem, ?_⟩
  simp only [map_mul, map_inv]

private theorem e6TwoLayerData_aux (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (hpq : p ∣ Nat.card K + 1) :
    ∃ R3 : Subgroup (adjointGroup .E6 K),
      R3 ≤ a5Levi K ∧ IsElemAbelian p R3 ∧ Nat.card R3 = p ^ 3 ∧
      ∃ z : adjointGroup .E6 K, z ∈ R3 ∧ z ≠ 1 ∧
      ∃ Q : Subgroup (adjointGroup .E6 K),
        Q ≤ a5Levi K ⊓ Subgroup.centralizer ({z} : Set (adjointGroup .E6 K)) ∧
        CFSG.Open.IsQuasisimple ↥Q ∧ p ∣ Nat.card Q ∧
        (Q.subgroupOf (a5Levi K ⊓
          Subgroup.centralizer ({z} : Set (adjointGroup .E6 K)))).Normal := by
  obtain ⟨x₁, hx₁, ho₁⟩ :=
    exists_mem_blockSL_orderOf_eq_prime (K := K) (a := 0) (b := 1) (by decide) hp hpq
  obtain ⟨x₂, hx₂, ho₂⟩ :=
    exists_mem_blockSL_orderOf_eq_prime (K := K) (a := 2) (b := 3) (by decide) hp hpq
  obtain ⟨x₃, hx₃, ho₃⟩ :=
    exists_mem_blockSL_orderOf_eq_prime (K := K) (a := 4) (b := 5) (by decide) hp hpq
  let R3' : Subgroup (LinearFlag.projectiveSL 6 K) :=
    Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃
  let Q' : Subgroup (LinearFlag.projectiveSL 6 K) := blockSL (K := K) I0123
  have hR3'ea : IsElemAbelian p R3' :=
    (isElemAbelian_zpowers_sup_three hx₁ hx₂ hx₃ ho₁ ho₂ ho₃).1
  have hR3'card : Nat.card R3' = p ^ 3 :=
    (isElemAbelian_zpowers_sup_three hx₁ hx₂ hx₃ ho₁ ho₂ ho₃).2
  have hx₃R3' : x₃ ∈ R3' := Subgroup.mem_sup_right (Subgroup.mem_zpowers x₃)
  have hQ'le : Q' ≤ Subgroup.centralizer ({x₃} : Set (LinearFlag.projectiveSL 6 K)) :=
    blockSL_I0123_le_centralizer hx₃
  have hQ'q : CFSG.Open.IsQuasisimple ↥Q' := isQuasisimple_blockSL_I0123
  have hpQ' : p ∣ Nat.card Q' := dvd_card_blockSL_I0123 hpq
  obtain ⟨y, hy, hyx, hyy, hx₃pow⟩ := exists_lift_blockSL_I45 hp3 hpq hx₃ ho₃
  have hQ'le_y : blockSL (K := K) ({4, 5} : Finset (Fin 6))ᶜ ≤
      Subgroup.centralizer ({LinearFlag.proj 6 K y} :
        Set (LinearFlag.projectiveSL 6 K)) := by
    rw [hyx]
    simpa [Q'] using hQ'le
  have hQ'n : (Q'.subgroupOf
      (Subgroup.centralizer ({x₃} : Set (LinearFlag.projectiveSL 6 K)))).Normal := by
    rw [← hyx]
    exact normal_blockSL_compl_of_centralizer_pow (a := 4) (b := 5) (by decide)
      hy hyy (by rwa [hyx]) hQ'le_y
  let e := CFSG.SeitzReduction.E6Pilot.a5LeviProjEquiv K
  let eA : LinearFlag.projectiveSL 6 K →* adjointGroup .E6 K :=
    (a5Levi K).subtype.comp e.toMonoidHom
  have heA_inj : Function.Injective eA :=
    (a5Levi K).subtype_injective.comp e.injective
  have heA_range : eA.range = a5Levi K := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).2
    · intro hg
      exact ⟨e.symm ⟨g, hg⟩, by simp [eA]⟩
  let R3 : Subgroup (adjointGroup .E6 K) := R3'.map eA
  let z : adjointGroup .E6 K := eA x₃
  let Q : Subgroup (adjointGroup .E6 K) := Q'.map eA
  have hR3le : R3 ≤ a5Levi K := by
    change R3'.map eA ≤ a5Levi K
    rw [← heA_range]
    exact Subgroup.map_le_range eA R3'
  have hR3ea : IsElemAbelian p R3 := CFSG.SectionRank.isElemAbelian_map hR3'ea eA
  have hR3card : Nat.card R3 = p ^ 3 := by
    change Nat.card (R3'.map eA) = p ^ 3
    rw [Subgroup.card_map_of_injective heA_inj, hR3'card]
  have hzR3 : z ∈ R3 := Subgroup.mem_map_of_mem eA hx₃R3'
  have hzne : z ≠ 1 := by
    have hx₃ne : x₃ ≠ 1 := by
      intro hx
      rw [hx, orderOf_one] at ho₃
      exact hp.ne_one ho₃.symm
    intro h
    apply hx₃ne
    apply e.injective
    have h' : (e x₃ : a5Levi K) = 1 := by
      apply Subtype.ext
      show (↑(e x₃) : adjointGroup .E6 K) = 1
      exact h
    simpa using h'
  have hQle_a5 : Q ≤ a5Levi K := by
    change Q'.map eA ≤ a5Levi K
    rw [← heA_range]
    exact Subgroup.map_le_range eA Q'
  have hQz : Q ≤ Subgroup.centralizer ({z} : Set (adjointGroup .E6 K)) := by
    intro w hw
    change w ∈ Q'.map eA at hw
    obtain ⟨q, hqQ, rfl⟩ := Subgroup.mem_map.1 hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    show eA q * eA x₃ = eA x₃ * eA q
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 (hQ'le hqQ)]
  have hQle : Q ≤ a5Levi K ⊓
      Subgroup.centralizer ({z} : Set (adjointGroup .E6 K)) := le_inf hQle_a5 hQz
  have hQq' : CFSG.IsQuasisimple ↥Q' := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hQ'q
  let eQ : ↥Q' ≃* ↥Q := Subgroup.equivMapOfInjective Q' eA heA_inj
  have hQq : CFSG.Open.IsQuasisimple ↥Q := CFSG.Quasithin.A3.isQuasisimple_iff_open.mp
    (CFSG.IsQuasisimple.of_mulEquiv eQ.symm hQq')
  have hpQ : p ∣ Nat.card Q := by
    rwa [show Nat.card Q = Nat.card Q' from (Nat.card_congr eQ.toEquiv).symm]
  have hQn_map : ((Q'.map eA).subgroupOf
      ((Subgroup.centralizer ({x₃} : Set (LinearFlag.projectiveSL 6 K))).map eA)).Normal :=
    normal_subgroupOf_map (f := eA) hQ'le hQ'n
  have hCeq : (Subgroup.centralizer ({x₃} : Set (LinearFlag.projectiveSL 6 K))).map eA =
      a5Levi K ⊓ Subgroup.centralizer ({z} : Set (adjointGroup .E6 K)) := by
    apply le_antisymm
    · refine le_inf ?_ ?_
      · rw [← heA_range]
        exact Subgroup.map_le_range eA _
      · intro g hg
        obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hg
        rw [Subgroup.mem_centralizer_singleton_iff]
        show eA c * eA x₃ = eA x₃ * eA c
        rw [← map_mul, ← map_mul,
          Subgroup.mem_centralizer_singleton_iff.1 hc]
    · intro g hg
      obtain ⟨hga, hgz⟩ := Subgroup.mem_inf.1 hg
      rw [← heA_range] at hga
      obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hga
      refine Subgroup.mem_map.2 ⟨c, ?_, hc⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply heA_inj
      rw [map_mul, map_mul, hc]
      exact Subgroup.mem_centralizer_singleton_iff.1 hgz
  have hQn : (Q.subgroupOf (a5Levi K ⊓
      Subgroup.centralizer ({z} : Set (adjointGroup .E6 K)))).Normal := by
    rw [← hCeq]
    change ((Q'.map eA).subgroupOf
      ((Subgroup.centralizer ({x₃} : Set (LinearFlag.projectiveSL 6 K))).map eA)).Normal
    exact hQn_map
  exact ⟨R3, hR3le, hR3ea, hR3card, z, hzR3, hzne, Q, hQle, hQq, hpQ, hQn⟩

theorem e6TwoLayerData_holds : E6TwoLayerData := by
  unfold E6TwoLayerData
  intro K hK hKf hKc p hp hp3 hpq
  letI : Field K := hK
  letI : Finite K := hKf
  letI : CharP K 2 := hKc
  exact e6TwoLayerData_aux (K := K) p hp hp3 hpq

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Two
