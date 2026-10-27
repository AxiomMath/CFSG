module

public import CFSG.LieType.SeitzGeneration.UnitaryHeisTensorCenters
public import CFSG.LieType.SeitzGeneration.InnerThreeUnitaryLeaves

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.CTP CFSG.LieType.BorelTits

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem closure_centralizers_unitarySU_of_dvd_add_one_gu (h : UnitaryFieldData ℓ f K)
    (hp : p.Prime) (hpq : p ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2)
    (G : Subgroup (primeFormUnitary h (idGram K (n + 1))))
    (hcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x) (hexp : ∀ x ∈ G, x ^ p = 1)
    (hcard : Nat.card G = p ^ 2) :
    Subgroup.closure {g : unitarySU ℓ f K (n + 1) |
      ∃ x ∈ G, x ≠ 1 ∧ (g : GL (Fin (n + 1)) K) * (x : GL (Fin (n + 1)) K) =
        (x : GL (Fin (n + 1)) K) * (g : GL (Fin (n + 1)) K)} = ⊤ := by
  classical
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag h hp hpq G hcomm hexp
  let Pg : GL (Fin (n + 1)) K := (P : GL (Fin (n + 1)) K)
  let Dg : G → GL (Fin (n + 1)) K := fun x =>
    Pg⁻¹ * ((x : primeFormUnitary h (idGram K (n + 1))) : GL (Fin (n + 1)) K) * Pg
  have hdiag : ∀ x : G,
      ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K).IsDiag :=
    fun x => hP _ x.2
  have hDmul : ∀ x y : G, Dg (x * y) = Dg x * Dg y := by
    intro x y
    simp only [Dg, Subgroup.coe_mul]
    group
  have hD1 : Dg 1 = 1 := by simp [Dg]
  let χ : Fin (n + 1) → G →* K := fun c =>
    { toFun := fun x => ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c
      map_one' := by simp [hD1]
      map_mul' := fun x y => by
        simp only [hDmul, Units.val_mul]
        exact mul_apply_diag_of_isDiag (hdiag x) c }
  have hnz : ∀ (x : G) (c : Fin (n + 1)),
      ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c ≠ 0 := by
    intro x c
    have h1 : (((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
        (((Dg x)⁻¹ : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) c c = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [mul_apply_diag_of_isDiag (hdiag x)] at h1
    exact left_ne_zero_of_mul_eq_one h1
  have hexpE : ∀ x : G, x ^ p = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  have hcommblock : ∀ i : Fin n, ∃ x : G, x ≠ 1 ∧ ∀ A : Matrix (Fin 2) (Fin 2) K,
      blockMat (n + 1) i A * ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
        ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
          blockMat (n + 1) i A := by
    intro i
    obtain ⟨x, hx1, -, hxeq⟩ := exists_ne_one_hom_eq hp hexpE hcard (χ i.castSucc) (χ i.succ)
    refine ⟨x, hx1, fun A => ?_⟩
    have hD : ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
        Matrix.diagonal (fun c => ((Dg x : GL (Fin (n + 1)) K) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c) := ((hdiag x).diagonal_diag).symm
    rw [hD]
    exact blockMat_mul_diagonal_comm (by omega) _ (hnz x) i.castSucc i.succ (by simp) (by simp)
      hxeq A
  let φ := conjSU h P
  set S := Subgroup.closure {g : unitarySU ℓ f K (n + 1) |
      ∃ x ∈ G, x ≠ 1 ∧ (g : GL (Fin (n + 1)) K) * (x : GL (Fin (n + 1)) K) =
        (x : GL (Fin (n + 1)) K) * (g : GL (Fin (n + 1)) K)} with hS
  have hblock : ∀ (i : Fin n) (y : unitarySU ℓ f K (n + 1)) (A : Matrix (Fin 2) (Fin 2) K),
      (((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) K) = blockMat (n + 1) i A → φ y ∈ S := by
    intro i y A hA
    obtain ⟨x, hx1, hxc⟩ := hcommblock i
    refine Subgroup.subset_closure ⟨(x : primeFormUnitary h (idGram K (n + 1))), x.2,
      fun h1 => hx1 (Subtype.ext h1), ?_⟩
    have hYD : ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Dg x =
        Dg x * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) := by
      apply Units.ext
      simp only [Units.val_mul]
      rw [hA]
      exact hxc A
    have hxeq : ((x : primeFormUnitary h (idGram K (n + 1))) : GL (Fin (n + 1)) K) =
        Pg * Dg x * Pg⁻¹ := by
      simp [Dg, mul_assoc]
    show Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹ *
        ((x : primeFormUnitary h (idGram K (n + 1))) : GL (Fin (n + 1)) K) =
      ((x : primeFormUnitary h (idGram K (n + 1))) : GL (Fin (n + 1)) K) *
        (Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹)
    rw [hxeq]
    calc Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹ *
          (Pg * Dg x * Pg⁻¹)
        = Pg * (((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Dg x) * Pg⁻¹ := by group
      _ = Pg * (Dg x * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K)) * Pg⁻¹ := by
        rw [hYD]
      _ = Pg * Dg x * Pg⁻¹ *
          (Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹) := by group
  let ε : Su K ℓ f (n + 1) ≃* unitarySU ℓ f K (n + 1) :=
    MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU h.card_eq_sq (n + 1))
  let ι : Fin n → (Su K ℓ f 2 →* unitarySU ℓ f K (n + 1)) := fun i =>
    ε.toMonoidHom.comp (blockEmb2 K ℓ f n i)
  have hgen : ⨆ i : Fin n, (ι i).range = ⊤ := by
    have h1 := iSup_range_blockEmb2 (K := K) (p := ℓ) (f := f) h.card_eq_sq hq n
    have h2 := congrArg (Subgroup.map ε.toMonoidHom) h1
    rw [Subgroup.map_iSup, Subgroup.map_top_of_surjective _ ε.surjective] at h2
    simpa [ι, MonoidHom.range_comp] using h2
  have hle' : (⨆ i : Fin n, (ι i).range).map φ.toMonoidHom ≤ S := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact hblock i _ ((a : Su K ℓ f 2) : GL (Fin 2) K) rfl
  rw [hgen, Subgroup.map_top_of_surjective _ φ.surjective] at hle'
  exact top_unique hle'

theorem pow_eq_one_of_dvd_pow_eq_one_p {G : Type*} [Monoid G] {x : G} {p a : ℕ}
    (hx : x ^ p = 1) (ha : p ∣ a) : x ^ a = 1 := by
  obtain ⟨k, rfl⟩ := ha
  rw [pow_mul, hx, one_pow]

theorem add_pred_mul_self_eq_p {p : ℕ} (hp : p.Prime) (t : ℕ) : t + (p - 1) * t = p * t := by
  conv_rhs => rw [← Nat.sub_add_cancel hp.one_lt.le]
  ring

@[expose] def commPairSubgroupP {G : Type*} [Group G] {x y : G} (hp : p.Prime)
    (hxy : Commute x y) (hx : x ^ p = 1) (hy : y ^ p = 1) : Subgroup G where
  carrier := {z | ∃ a b : ℕ, z = x ^ a * y ^ b}
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d, comm_pair_pow_mul hxy a b c d⟩
  one_mem' := ⟨0, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨a, b, rfl⟩
    refine ⟨(p - 1) * a, (p - 1) * b, inv_eq_of_mul_eq_one_right ?_⟩
    rw [comm_pair_pow_mul hxy, add_pred_mul_self_eq_p hp a, add_pred_mul_self_eq_p hp b, pow_mul,
      pow_mul, hx, hy, one_pow, one_pow, one_mul]

theorem commPairSubgroupP_exp {G : Type*} [Group G] {x y : G} (hp : p.Prime) (hxy : Commute x y)
    (hx : x ^ p = 1) (hy : y ^ p = 1) : ∀ a ∈ commPairSubgroupP hp hxy hx hy, a ^ p = 1 := by
  rintro _ ⟨a, b, rfl⟩
  rw [(hxy.pow_pow a b).mul_pow p, ← pow_mul, ← pow_mul, mul_comm a p, mul_comm b p, pow_mul,
    pow_mul, hx, hy, one_pow, one_pow, one_mul]

theorem commPairSubgroupP_comm {G : Type*} [Group G] {x y : G} (hp : p.Prime) (hxy : Commute x y)
    (hx : x ^ p = 1) (hy : y ^ p = 1) :
    ∀ a ∈ commPairSubgroupP hp hxy hx hy, ∀ b ∈ commPairSubgroupP hp hxy hx hy,
      a * b = b * a := by
  rintro _ ⟨a, b, rfl⟩ _ ⟨c, d, rfl⟩
  rw [comm_pair_pow_mul hxy, comm_pair_pow_mul hxy, add_comm a c, add_comm b d]

theorem card_commPairSubgroupP {G : Type*} [Group G] {x y : G} (hp : p.Prime)
    (hxy : Commute x y) (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hind : ∀ a b : ℕ, x ^ a * y ^ b = 1 → p ∣ a ∧ p ∣ b) :
    Nat.card (commPairSubgroupP hp hxy hx hy) = p ^ 2 := by
  have hpos : 0 < p := hp.pos
  let φ : Fin p × Fin p → commPairSubgroupP hp hxy hx hy := fun q =>
    ⟨x ^ (q.1 : ℕ) * y ^ (q.2 : ℕ), q.1, q.2, rfl⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨i, j⟩ ⟨k, l⟩ hφ'
      have h1 : x ^ (i : ℕ) * y ^ (j : ℕ) = x ^ (k : ℕ) * y ^ (l : ℕ) :=
        congrArg Subtype.val hφ'
      have h2 : x ^ ((i : ℕ) + (p - 1) * (k : ℕ)) * y ^ ((j : ℕ) + (p - 1) * (l : ℕ)) = 1 := by
        rw [← comm_pair_pow_mul hxy, h1, comm_pair_pow_mul hxy, add_pred_mul_self_eq_p hp,
          add_pred_mul_self_eq_p hp, pow_mul, pow_mul, hx, hy, one_pow, one_pow, one_mul]
      obtain ⟨h4, h5⟩ := hind _ _ h2
      have hp1' : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
        have := hp.two_le
        omega
      have hik : (i : ℕ) = k := by
        have hz : ((i : ℕ) : ℤ) - ((k : ℕ) : ℤ) = 0 := by
          apply Int.eq_zero_of_abs_lt_dvd (m := (p : ℤ))
          · have hcast : (((i : ℕ) + (p - 1) * (k : ℕ) : ℕ) : ℤ) =
                ((i : ℕ) : ℤ) + ((p : ℤ) - 1) * ((k : ℕ) : ℤ) := by
              rw [Nat.cast_add, Nat.cast_mul, hp1']
            have e : ((i : ℕ) : ℤ) - ((k : ℕ) : ℤ) =
                (((i : ℕ) + (p - 1) * (k : ℕ) : ℕ) : ℤ) - (p : ℤ) * ((k : ℕ) : ℤ) := by
              rw [hcast]; ring
            rw [e]
            exact dvd_sub (Int.natCast_dvd_natCast.2 h4) (dvd_mul_right _ _)
          · rw [abs_lt]
            have := i.2
            have := k.2
            constructor <;> omega
        omega
      have hjl : (j : ℕ) = l := by
        have hz : ((j : ℕ) : ℤ) - ((l : ℕ) : ℤ) = 0 := by
          apply Int.eq_zero_of_abs_lt_dvd (m := (p : ℤ))
          · have hcast : (((j : ℕ) + (p - 1) * (l : ℕ) : ℕ) : ℤ) =
                ((j : ℕ) : ℤ) + ((p : ℤ) - 1) * ((l : ℕ) : ℤ) := by
              rw [Nat.cast_add, Nat.cast_mul, hp1']
            have e : ((j : ℕ) : ℤ) - ((l : ℕ) : ℤ) =
                (((j : ℕ) + (p - 1) * (l : ℕ) : ℕ) : ℤ) - (p : ℤ) * ((l : ℕ) : ℤ) := by
              rw [hcast]; ring
            rw [e]
            exact dvd_sub (Int.natCast_dvd_natCast.2 h5) (dvd_mul_right _ _)
          · rw [abs_lt]
            have := j.2
            have := l.2
            constructor <;> omega
        omega
      exact Prod.ext (Fin.ext hik) (Fin.ext hjl)
    · rintro ⟨z, a, b, rfl⟩
      refine ⟨(⟨a % p, Nat.mod_lt _ hpos⟩, ⟨b % p, Nat.mod_lt _ hpos⟩), ?_⟩
      apply Subtype.ext
      show x ^ (a % p) * y ^ (b % p) = x ^ a * y ^ b
      rw [← pow_eq_pow_mod a hx, ← pow_eq_pow_mod b hy]
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ)]
  simp [sq]

theorem eq_top_of_abelian_pth [Finite K] [Fact ℓ.Prime] [CharP K ℓ] (h : UnitaryFieldData ℓ f K)
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ ℓ ^ f + 1) (hn : 2 ≤ n) {x y : GL (Fin n) K}
    (hx : x ∈ primeFormUnitary h (idGram K n)) (hy : y ∈ primeFormUnitary h (idGram K n))
    (hxy : x * y = y * x) (hx1 : x ^ p = 1) (hy1 : y ^ p = 1)
    (hind : ∀ a b : ℕ, x ^ a * y ^ b = 1 → p ∣ a ∧ p ∣ b)
    {H : Subgroup (SUid (unitaryInvolution K ℓ f) n)}
    (hH : ∀ a b : ℕ, ¬ (p ∣ a ∧ p ∣ b) →
      HeisTensor.Cent H ((x ^ a * y ^ b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : H = ⊤ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  classical
  let X : primeFormUnitary h (idGram K (m + 1)) := ⟨x, hx⟩
  let Y : primeFormUnitary h (idGram K (m + 1)) := ⟨y, hy⟩
  have hXY : Commute X Y := Subtype.ext hxy
  have hX : X ^ p = 1 := Subtype.ext (by simpa [X] using hx1)
  have hY : Y ^ p = 1 := Subtype.ext (by simpa [Y] using hy1)
  have hind' : ∀ a b : ℕ, X ^ a * Y ^ b = 1 → p ∣ a ∧ p ∣ b := by
    intro a b hab
    apply hind a b
    have := congrArg Subtype.val hab
    simpa [X, Y] using this
  have hq : ℓ ^ f ≠ 2 := by
    intro h2
    rw [h2] at hpq
    have := Nat.le_of_dvd (by norm_num) hpq
    omega
  have htop := closure_centralizers_unitarySU_of_dvd_add_one_gu h hp hpq hq
    (commPairSubgroupP hp hXY hX hY) (commPairSubgroupP_comm hp hXY hX hY)
    (commPairSubgroupP_exp hp hXY hX hY) (card_commPairSubgroupP hp hXY hX hY hind')
  let ε : SUid (unitaryInvolution K ℓ f) (m + 1) ≃* unitarySU ℓ f K (m + 1) :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq (m + 1))
  let Hc : Subgroup (unitarySU ℓ f K (m + 1)) := H.comap ε.symm.toMonoidHom
  have hsub : ∀ g : unitarySU ℓ f K (m + 1),
      (∃ x' ∈ commPairSubgroupP hp hXY hX hY, x' ≠ 1 ∧
        (g : GL (Fin (m + 1)) K) * (x' : GL (Fin (m + 1)) K) =
          (x' : GL (Fin (m + 1)) K) * (g : GL (Fin (m + 1)) K)) → g ∈ Hc := by
    rintro g ⟨x', hx'G, hx'1, hcg⟩
    obtain ⟨a, b, hab⟩ := hx'G
    have hnd : ¬ (p ∣ a ∧ p ∣ b) := by
      rintro ⟨ha, hb⟩
      apply hx'1
      rw [hab, pow_eq_one_of_dvd_pow_eq_one_p hX ha, pow_eq_one_of_dvd_pow_eq_one_p hY hb, one_mul]
    have hx'GL : ((x' : primeFormUnitary h (idGram K (m + 1))) : GL (Fin (m + 1)) K) =
        x ^ a * y ^ b := by
      rw [hab]; simp [X, Y]
    have hcomm' : ((g : GL (Fin (m + 1)) K)) * (x ^ a * y ^ b) =
        (x ^ a * y ^ b) * ((g : GL (Fin (m + 1)) K)) := by
      rw [← hx'GL]; exact hcg
    have hmat : ((g : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
        ((x ^ a * y ^ b : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
        ((x ^ a * y ^ b : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
          ((g : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
      rw [← Units.val_mul, ← Units.val_mul, hcomm']
    show ε.symm g ∈ H
    exact hH a b hnd (ε.symm g) hmat
  have hHc : Hc = ⊤ := by
    rw [eq_top_iff, ← htop, Subgroup.closure_le]
    intro g hg
    exact hsub g hg
  rw [eq_top_iff]
  intro g _
  have hgc : ε g ∈ Hc := hHc ▸ Subgroup.mem_top _
  simpa [Hc] using hgc

end CFSG.LieType.SeitzGeneration
