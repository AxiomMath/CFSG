module

public import CFSG.CGT.Harada80.RhoLin
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Iwasawa

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Harada80

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

section Transitive

variable {K : Type*} [Field K] [CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2 K]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_mem_elementaryGroup_apply_eq_of_map_eq_one (hQ : (polarBilin Q).Nondegenerate)
    (hd : 4 ≤ Module.finrank K V) {x y : V} (hx : Q x = 1) (hy : Q y = 1) :
    ∃ g ∈ elementaryGroup Q, g x = y := by
  have hd3 : 3 ≤ Module.finrank K V := by omega
  obtain ⟨u, hu, hxu⟩ := exists_singular_polar_eq_one hQ hd3 hx
  obtain ⟨v, hv, hyv⟩ := exists_singular_polar_eq_one hQ hd3 hy
  have hu0 : u ≠ 0 := fun h => by
    rw [h, polar_zero_right] at hxu
    exact zero_ne_one hxu
  have hv0 : v ≠ 0 := fun h => by
    rw [h, polar_zero_right] at hyv
    exact zero_ne_one hyv
  obtain ⟨g₁, hg₁, hg₁uv⟩ := exists_mem_elementaryGroup_apply_eq_f2 hQ hd hu0 hv0 hu hv
  have hx₁ : Q (g₁ x) = 1 := by
    rw [map_of_mem (elementaryGroup_le_orthogonalGroup Q hg₁), hx]
  have hp₁ : polar Q v (g₁ x) = 1 := by
    rw [← hg₁uv, polar_map_of_mem (elementaryGroup_le_orthogonalGroup Q hg₁),
      polar_comm, hxu]
  have hp₂ : polar Q v y = 1 := by rw [polar_comm, hyv]
  refine ⟨eichler Q v ((1 : K)⁻¹ • (y - g₁ x)) * g₁, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (eichler_mem_elementaryGroup Q _ _) hg₁
  · rw [LinearEquiv.mul_apply,
      eichler_apply_eq_of_polar_eq hv (hx₁.trans hy.symm) hp₁ hp₂ one_ne_zero]

end Transitive

private theorem card_vec (m : ℕ) : Nat.card (Vec m) = 2 ^ (2 * m + 2) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_coord_fun (α := ZMod 2)
    (Fin m ⊕ Fin m ⊕ Fin 2), Nat.card_zmod, Fintype.card_sum, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_fin]
  ring

private theorem arith_nonsingular (m : ℕ) :
    2 ^ (2 * m + 2) - (1 + (2 ^ (m + 1) + 1) * (2 ^ m - 1)) =
      2 ^ m * (2 ^ (m + 1) + 1) := by
  have hx : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hsub : 2 ^ m - 1 + 1 = 2 ^ m := Nat.sub_add_cancel hx
  have h1 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  have h2 : 2 ^ (2 * m + 2) = 4 * (2 ^ m) ^ 2 := by
    rw [show 2 * m + 2 = m * 2 + 2 by ring, pow_add, pow_mul]
    norm_num
    ring
  have h3 : 1 + (2 ^ (m + 1) + 1) * (2 ^ m - 1) ≤ 2 ^ (2 * m + 2) := by
    rw [h1, h2]
    nlinarith
  rw [Nat.sub_eq_iff_eq_add h3, h1, h2]
  nlinarith

private theorem card_singular_eq_zero_set (m : ℕ) :
    Nat.card {v : Vec m // quadQ m v = 0} = 1 + (2 ^ (m + 1) + 1) * (2 ^ m - 1) := by
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 :=
    CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.irreducible_one_one
  have h := (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus (K := ZMod 2)
    (b := (1 : ZMod 2)) (c := (1 : ZMod 2)) m hirr).1
  rw [Nat.card_zmod] at h
  have hcast : ((1 + (2 ^ (m + 1) + 1) * (2 ^ m - 1) : ℕ) : ℤ) =
      1 + ((2 : ℤ) ^ (m + 1) + 1) * ((2 : ℤ) ^ m - 1) := by
    have h2m : ((2 ^ m - 1 : ℕ) : ℤ) = (2 : ℤ) ^ m - 1 := by
      rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    have h2m1 : ((2 ^ (m + 1) : ℕ) : ℤ) = (2 : ℤ) ^ (m + 1) := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      h2m1, h2m]
  exact Nat.cast_injective (h.trans hcast.symm)

theorem card_singular_quadQ (m : ℕ) :
    Nat.card {v : Vec m // v ≠ 0 ∧ quadQ m v = 0} = (2 ^ (m + 1) + 1) * (2 ^ m - 1) := by
  classical
  let s : Set (Vec m) := {v | quadQ m v = 0}
  have h0 := card_singular_eq_zero_set m
  have hmem : (0 : Vec m) ∈ s := by simp [s]
  have hcard : Nat.card {v : Vec m // v ≠ 0 ∧ quadQ m v = 0} = (s \ {0}).ncard := by
    rw [← Nat.card_coe_set_eq (s \ {0})]
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun v => ?_))
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, s]
    tauto
  have hdiff : (s \ {0}).ncard = s.ncard - 1 := Set.ncard_sdiff_singleton_of_mem hmem
  have hs : Nat.card {v : Vec m // quadQ m v = 0} = s.ncard := by
    rw [← Nat.card_coe_set_eq s]
    exact Nat.card_congr (Equiv.subtypeEquivProp (by rfl))
  rw [hcard, hdiff, ← hs, h0]
  omega

theorem card_nonsingular_quadQ (m : ℕ) :
    Nat.card {v : Vec m // quadQ m v = 1} = 2 ^ m * (2 ^ (m + 1) + 1) := by
  classical
  let s : Set (Vec m) := {v | quadQ m v = 0}
  have hset : (Set.ofPred (fun v : Vec m => quadQ m v = 1)) = sᶜ := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, s]
    constructor
    · intro h h0
      rw [h] at h0
      exact zero_ne_one h0.symm
    · intro h
      rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one (quadQ m v) with h0 | h1
      · exact absurd h0 h
      · exact h1
  have hN : Nat.card {v : Vec m // quadQ m v = 1} = sᶜ.ncard := by
    rw [← Nat.card_coe_set_eq (sᶜ)]
    exact Nat.card_congr (Equiv.subtypeEquivProp hset)
  have hcompl : sᶜ.ncard = Nat.card (Vec m) - s.ncard :=
    Set.ncard_compl s (Set.toFinite s) (Set.toFinite sᶜ)
  have hs : Nat.card {v : Vec m // quadQ m v = 0} = s.ncard := by
    rw [← Nat.card_coe_set_eq s]
    exact Nat.card_congr (Equiv.subtypeEquivProp (by rfl))
  have hNval : Nat.card {v : Vec m // quadQ m v = 1} =
      Nat.card (Vec m) - Nat.card {v : Vec m // quadQ m v = 0} := by
    rw [hN, hcompl, ← hs]
  rw [hNval, card_vec, card_singular_eq_zero_set]
  exact arith_nonsingular m

namespace Setting

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ} {S : Setting G M J m}

private theorem four_le_finrank (S : Setting G M J m) :
    4 ≤ Module.finrank (ZMod 2) (Vec m) := by
  rw [CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.finrank_minus]
  rcases S.m_eq with h | h <;> omega

private noncomputable def vecEquiv (S : Setting G M J m) (hZ : blockZ J = ⊥) :
    ↥(blockU J) ≃ Vec m :=
  Equiv.ofBijective S.vec ⟨S.vec_injective hZ, S.vec_surjective⟩

@[instance_reducible]
private def conjMulAction (S : Setting G M J m) : MulAction ↥M ↥(blockU J) :=
  letI : SMul ↥M ↥(blockU J) :=
    ⟨fun x u => ⟨(x : G) * (u : G) * (x : G)⁻¹, conj_mem_blockU S x.2 u.2⟩⟩
  { one_smul := fun u => Subtype.ext (by
      show (1 : G) * (u : G) * (1 : G)⁻¹ = (u : G)
      simp)
    mul_smul := fun x y u => Subtype.ext (by
      show ((x * y : ↥M) : G) * (u : G) * ((x * y : ↥M) : G)⁻¹ =
        (x : G) * ((y : G) * (u : G) * (y : G)⁻¹) * (x : G)⁻¹
      simp [mul_assoc]) }

private theorem exists_conj_eq_of_mem_elementaryGroup (hZ : blockZ J = ⊥)
    {a a' : ↥(blockU J)} {g : Vec m ≃ₗ[ZMod 2] Vec m}
    (hg : g ∈ elementaryGroup (quadQ m)) (hgv : g (S.vec a) = S.vec a') :
    ∃ ℓ ∈ J, ℓ * (a : G) * ℓ⁻¹ = a' := by
  obtain ⟨ℓ, hℓ⟩ := S.exists_lin_eq_of_mem_elementaryGroup hZ hg
  let x : ↥M := Subgroup.inclusion S.le ℓ
  have hℓx : S.lin hZ x = g := hℓ
  refine ⟨(ℓ : G), ℓ.2, ?_⟩
  have h1 : S.vec (⟨(ℓ : G) * (a : G) * (ℓ : G)⁻¹,
      conj_mem_blockU S (S.le ℓ.2) a.2⟩ : ↥(blockU J)) = S.vec a' := by
    have h2 := S.lin_vec hZ x a
    rw [hℓx, hgv] at h2
    exact h2.symm
  exact congrArg Subtype.val (S.vec_injective hZ h1)

private theorem card_nonsingular_set (hZ : blockZ J = ⊥) :
    (Set.ofPred (fun a : ↥(blockU J) => quadQ m (S.vec a) = 1)).ncard =
      2 ^ m * (2 ^ (m + 1) + 1) := by
  rw [← card_nonsingular_quadQ m,
    ← Nat.card_coe_set_eq (Set.ofPred (fun a : ↥(blockU J) => quadQ m (S.vec a) = 1))]
  refine Nat.card_congr (Equiv.subtypeEquiv (vecEquiv (S := S) hZ) (fun a => ?_))
  exact Iff.rfl

private theorem card_singular_set (hZ : blockZ J = ⊥) :
    (Set.ofPred (fun a : ↥(blockU J) => a ≠ 1 ∧ quadQ m (S.vec a) = 0)).ncard =
      (2 ^ (m + 1) + 1) * (2 ^ m - 1) := by
  rw [← card_singular_quadQ m,
    ← Nat.card_coe_set_eq
      (Set.ofPred (fun a : ↥(blockU J) => a ≠ 1 ∧ quadQ m (S.vec a) = 0))]
  refine Nat.card_congr (Equiv.subtypeEquiv (vecEquiv (S := S) hZ) (fun a => ?_))
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 ((S.vec_eq_zero_iff hZ).mp h), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 ((S.vec_eq_zero_iff hZ).mpr h), h2⟩

theorem card_eq_mul_card_centralizer_of_nonsingular (hZ : blockZ J = ⊥) {b : ↥(blockU J)}
    (hb : quadQ m (S.vec b) = 1) :
    Nat.card M = 2 ^ m * (2 ^ (m + 1) + 1) *
      Nat.card ↥(M ⊓ Subgroup.centralizer ({(b : G)} : Set G)) := by
  letI : MulAction ↥M ↥(blockU J) := conjMulAction (S := S)
  have horbit : MulAction.orbit ↥M b = {a : ↥(blockU J) | quadQ m (S.vec a) = 1} := by
    ext a
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨x, rfl⟩
      change quadQ m (S.vec (⟨(x : G) * (b : G) * (x : G)⁻¹,
        conj_mem_blockU S x.2 b.2⟩ : ↥(blockU J))) = 1
      rw [← S.lin_vec hZ x b, S.quadQ_lin hZ x (S.vec b), hb]
    · intro ha
      obtain ⟨g, hg, hgv⟩ := exists_mem_elementaryGroup_apply_eq_of_map_eq_one
        (Q := quadQ m) (nondegenerate_quadQ m) (four_le_finrank (S := S)) hb ha
      obtain ⟨ℓ, hℓJ, hℓ⟩ := exists_conj_eq_of_mem_elementaryGroup (S := S) hZ hg hgv
      refine ⟨⟨ℓ, S.le hℓJ⟩, ?_⟩
      apply Subtype.ext
      exact hℓ
  have hstab : MulAction.stabilizer ↥M b =
      (M ⊓ Subgroup.centralizer ({(b : G)} : Set G)).subgroupOf M := by
    ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    change (⟨(x : G) * (b : G) * (x : G)⁻¹, conj_mem_blockU S x.2 b.2⟩ :
        ↥(blockU J)) = b ↔
      (x : G) ∈ M ∧ (x : G) * (b : G) = (b : G) * (x : G)
    exact ⟨fun h => ⟨x.2, mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val h)⟩,
      fun h => Subtype.ext (mul_inv_eq_iff_eq_mul.mpr h.2)⟩
  have hOS : Nat.card (MulAction.orbit ↥M b) * Nat.card (MulAction.stabilizer ↥M b) =
      Nat.card ↥M := by
    have h := (Subgroup.card_mul_index (MulAction.stabilizer ↥M b)).symm
    rw [h, MulAction.index_stabilizer, Nat.card_coe_set_eq (MulAction.orbit ↥M b)]
    ring
  rw [← hOS, horbit, hstab, Nat.card_coe_set_eq, card_nonsingular_set (S := S) hZ,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : M ⊓
      Subgroup.centralizer ({(b : G)} : Set G) ≤ M)).toEquiv]

theorem card_eq_mul_card_centralizer_of_singular (hZ : blockZ J = ⊥) {u : ↥(blockU J)}
    (hu1 : u ≠ 1) (hu : quadQ m (S.vec u) = 0) :
    Nat.card M = (2 ^ (m + 1) + 1) * (2 ^ m - 1) *
      Nat.card ↥(M ⊓ Subgroup.centralizer ({(u : G)} : Set G)) := by
  letI : MulAction ↥M ↥(blockU J) := conjMulAction (S := S)
  have horbit : MulAction.orbit ↥M u =
      {a : ↥(blockU J) | a ≠ 1 ∧ quadQ m (S.vec a) = 0} := by
    ext a
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨x, rfl⟩
      change (⟨(x : G) * (u : G) * (x : G)⁻¹, conj_mem_blockU S x.2 u.2⟩ :
          ↥(blockU J)) ≠ 1 ∧
        quadQ m (S.vec (⟨(x : G) * (u : G) * (x : G)⁻¹,
          conj_mem_blockU S x.2 u.2⟩ : ↥(blockU J))) = 0
      constructor
      · intro h
        have hv : S.vec (⟨(x : G) * (u : G) * (x : G)⁻¹,
            conj_mem_blockU S x.2 u.2⟩ : ↥(blockU J)) = 0 := by
          rw [h, S.vec_one]
        rw [← S.lin_vec hZ x u] at hv
        exact hu1 ((S.vec_eq_zero_iff hZ).mp ((S.lin hZ x).map_eq_zero_iff.mp hv))
      · rw [← S.lin_vec hZ x u, S.quadQ_lin hZ x (S.vec u), hu]
    · rintro ⟨ha1, ha⟩
      obtain ⟨g, hg, hgv⟩ := exists_mem_elementaryGroup_apply_eq_f2
        (Q := quadQ m) (nondegenerate_quadQ m) (four_le_finrank (S := S))
        (fun h => hu1 ((S.vec_eq_zero_iff hZ).mp h))
        (fun h => ha1 ((S.vec_eq_zero_iff hZ).mp h)) hu ha
      obtain ⟨ℓ, hℓJ, hℓ⟩ := exists_conj_eq_of_mem_elementaryGroup (S := S) hZ hg hgv
      refine ⟨⟨ℓ, S.le hℓJ⟩, ?_⟩
      apply Subtype.ext
      exact hℓ
  have hstab : MulAction.stabilizer ↥M u =
      (M ⊓ Subgroup.centralizer ({(u : G)} : Set G)).subgroupOf M := by
    ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    change (⟨(x : G) * (u : G) * (x : G)⁻¹, conj_mem_blockU S x.2 u.2⟩ :
        ↥(blockU J)) = u ↔
      (x : G) ∈ M ∧ (x : G) * (u : G) = (u : G) * (x : G)
    exact ⟨fun h => ⟨x.2, mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val h)⟩,
      fun h => Subtype.ext (mul_inv_eq_iff_eq_mul.mpr h.2)⟩
  have hOS : Nat.card (MulAction.orbit ↥M u) * Nat.card (MulAction.stabilizer ↥M u) =
      Nat.card ↥M := by
    have h := (Subgroup.card_mul_index (MulAction.stabilizer ↥M u)).symm
    rw [h, MulAction.index_stabilizer, Nat.card_coe_set_eq (MulAction.orbit ↥M u)]
    ring
  rw [← hOS, horbit, hstab, Nat.card_coe_set_eq, card_singular_set (S := S) hZ,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : M ⊓
      Subgroup.centralizer ({(u : G)} : Set G) ≤ M)).toEquiv]

theorem conj_ne_of_singular_of_nonsingular (hZ : blockZ J = ⊥) {u b : ↥(blockU J)}
    (hu1 : u ≠ 1) (hu : quadQ m (S.vec u) = 0) (hb : quadQ m (S.vec b) = 1)
    (hC : Subgroup.centralizer ({(u : G)} : Set G) ≤ M) (g : G) : g * (u : G) * g⁻¹ ≠ b := by
  intro hgub
  have hconj : IsConj (u : G) (b : G) := isConj_iff.mpr ⟨g, hgub⟩
  have hidx : (Subgroup.centralizer ({(u : G)} : Set G)).index =
      (Subgroup.centralizer ({(b : G)} : Set G)).index := by
    rw [Subgroup.index_centralizer_eq_ncard, Subgroup.index_centralizer_eq_ncard,
      IsConj.conjugatesOf_eq hconj]
  have hcardC : Nat.card ↥(Subgroup.centralizer ({(u : G)} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({(b : G)} : Set G)) := by
    have h1 := (Subgroup.centralizer ({(u : G)} : Set G)).card_mul_index
    have h2 := (Subgroup.centralizer ({(b : G)} : Set G)).card_mul_index
    haveI : (Subgroup.centralizer ({(u : G)} : Set G)).FiniteIndex :=
      Subgroup.finiteIndex_of_finite
    rw [← hidx] at h2
    exact Nat.mul_right_cancel (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
      (h1.trans h2.symm)
  have hdvd : Nat.card ↥(M ⊓ Subgroup.centralizer ({(b : G)} : Set G)) ∣
      Nat.card ↥(Subgroup.centralizer ({(u : G)} : Set G)) := by
    rw [hcardC]
    exact Subgroup.card_dvd_of_le (inf_le_right : M ⊓
      Subgroup.centralizer ({(b : G)} : Set G) ≤
        Subgroup.centralizer ({(b : G)} : Set G))
  obtain ⟨k, hk⟩ := hdvd
  have hCu : Nat.card ↥(M ⊓ Subgroup.centralizer ({(u : G)} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({(u : G)} : Set G)) := by
    rw [inf_eq_right.mpr hC]
  have hN := card_eq_mul_card_centralizer_of_nonsingular (S := S) hZ hb
  have hS := card_eq_mul_card_centralizer_of_singular (S := S) hZ hu1 hu
  have hEq : 2 ^ m * (2 ^ (m + 1) + 1) *
        Nat.card ↥(M ⊓ Subgroup.centralizer ({(b : G)} : Set G)) =
      (2 ^ (m + 1) + 1) * (2 ^ m - 1) *
        Nat.card ↥(Subgroup.centralizer ({(u : G)} : Set G)) := by
    rw [← hN, hS, hCu]
  rw [hk] at hEq
  have hpos : 0 < Nat.card ↥(M ⊓ Subgroup.centralizer ({(b : G)} : Set G)) := by
    haveI : Nonempty ↥(M ⊓ Subgroup.centralizer ({(b : G)} : Set G)) := ⟨1, Subgroup.one_mem _⟩
    exact Nat.card_pos
  have hcancel : 2 ^ m * (2 ^ (m + 1) + 1) =
      (2 ^ (m + 1) + 1) * (2 ^ m - 1) * k := by
    refine Nat.mul_right_cancel hpos ?_
    calc 2 ^ m * (2 ^ (m + 1) + 1) *
          Nat.card ↥(M ⊓ Subgroup.centralizer ({(b : G)} : Set G))
        = (2 ^ (m + 1) + 1) * (2 ^ m - 1) *
            (Nat.card ↥(M ⊓ Subgroup.centralizer ({(b : G)} : Set G)) * k) := hEq
      _ = ((2 ^ (m + 1) + 1) * (2 ^ m - 1) * k) *
            Nat.card ↥(M ⊓ Subgroup.centralizer ({(b : G)} : Set G)) := by ring
  have hdvdN : (2 ^ (m + 1) + 1) * (2 ^ m - 1) ∣ 2 ^ m * (2 ^ (m + 1) + 1) :=
    ⟨k, hcancel⟩
  rcases S.m_eq with hm | hm
  · rw [hm] at hdvdN
    norm_num at hdvdN
  · rw [hm] at hdvdN
    norm_num at hdvdN

end Setting

end CFSG.CGT.Harada80
