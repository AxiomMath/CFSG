module

public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.OutdiagAbelian

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.CTP
  CFSG.ClassicalInvolution.Phan CFSG.RankThree.PartOne.KCUnitaryModel

variable {ℓ f n : ℕ} {K : Type} [Field K]

@[expose] def FixUn (ℓ f n : ℕ) (K : Type) [Field K] (M : Matrix (Fin n) (Fin n) K) :
    Set (unitarySU ℓ f K n) :=
  {g | ∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M =
    c • (M * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))}

theorem mem_FixUn_of_mul_comm {M : Matrix (Fin n) (Fin n) K} {g : unitarySU ℓ f K n}
    (hg : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M =
      M * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : g ∈ FixUn ℓ f n K M :=
  ⟨1, by rw [one_smul]; exact hg⟩

theorem closure_planeFixUn_abelian_of_cube_roots (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2) (hn : 3 ≤ n)
    {x y : GL (Fin n) K} (hx : x ∈ primeFormUnitary h (idGram K n))
    (hy : y ∈ primeFormUnitary h (idGram K n)) (hxy : x * y = y * x) {α β : K} (hα : α ≠ 0)
    (hβ : β ≠ 0) (hx3 : ((x ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hy3 : ((y ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = β • 1)
    (hind : ∀ a b : ℕ,
      (∃ c : K, ((x ^ a * y ^ b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1) →
        3 ∣ a ∧ 3 ∣ b)
    (hcx : ∃ μ : K, μ ^ 3 = α) (hcy : ∃ ν : K, ν ^ 3 = β) :
    Subgroup.closure (FixUn ℓ f n K (x : Matrix (Fin n) (Fin n) K) ∪
      FixUn ℓ f n K (y : Matrix (Fin n) (Fin n) K) ∪
      FixUn ℓ f n K ((x * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∪
      FixUn ℓ f n K ((x * y ^ 2 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = ⊤ := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hfin := h.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨μ, hμ⟩ := hcx
  obtain ⟨ν, hν⟩ := hcy
  have hμ0 : μ ≠ 0 := by rintro rfl; exact hα (by rw [← hμ]; norm_num)
  have hν0 : ν ≠ 0 := by rintro rfl; exact hβ (by rw [← hν]; norm_num)
  have hnorm : ∀ {g : GL (Fin (m + 1)) K}, g ∈ primeFormUnitary h (idGram K (m + 1)) →
      ∀ {lam : K}, ((g ^ 3 : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
        lam • 1 → h.bar lam * lam = 1 := by
    intro g hg lam hlam
    have h1 := mem_primeFormUnitary.1 (pow_mem hg 3)
    simp only [idGram, Units.val_one] at h1
    rw [hlam, barTranspose_smul_mul_smul] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simpa using h2
  have hαN : α ^ (ℓ ^ f + 1) = 1 := by
    have := hnorm hx hx3
    rwa [h.bar_apply, ← pow_succ] at this
  have hβN : β ^ (ℓ ^ f + 1) = 1 := by
    have := hnorm hy hy3
    rwa [h.bar_apply, ← pow_succ] at this
  have hμN := bar_mul_eq_one_of_cube h hq3 hμ0 hμ hαN
  have hνN := bar_mul_eq_one_of_cube h hq3 hν0 hν hβN
  have hμiN : h.bar μ⁻¹ * μ⁻¹ = 1 := by rw [map_inv₀, ← mul_inv, hμN, inv_one]
  have hνiN : h.bar ν⁻¹ * ν⁻¹ = 1 := by rw [map_inv₀, ← mul_inv, hνN, inv_one]
  have hx3' : (x : Matrix (Fin (m + 1)) (Fin (m + 1)) K) ^ 3 = α • 1 := by
    rw [← Units.val_pow_eq_pow_val]; exact hx3
  have hy3' : (y : Matrix (Fin (m + 1)) (Fin (m + 1)) K) ^ 3 = β • 1 := by
    rw [← Units.val_pow_eq_pow_val]; exact hy3
  obtain ⟨sx, hsx⟩ : ∃ u : Kˣ, (u : K) = μ⁻¹ := ⟨Units.mk0 _ (inv_ne_zero hμ0), rfl⟩
  obtain ⟨sy, hsy⟩ : ∃ u : Kˣ, (u : K) = ν⁻¹ := ⟨Units.mk0 _ (inv_ne_zero hν0), rfl⟩
  obtain ⟨xn, hxn⟩ : ∃ g : GL (Fin (m + 1)) K,
      g = Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) sx * x := ⟨_, rfl⟩
  obtain ⟨yn, hyn⟩ : ∃ g : GL (Fin (m + 1)) K,
      g = Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) sy * y := ⟨_, rfl⟩
  have hxnU : xn ∈ primeFormUnitary h (idGram K (m + 1)) := by
    rw [hxn, show sx = Units.mk0 μ⁻¹ (inv_ne_zero hμ0) from Units.ext (by rw [hsx]; rfl)]
    exact smul_mem_primeFormUnitary h hx (inv_ne_zero hμ0) hμiN
  have hynU : yn ∈ primeFormUnitary h (idGram K (m + 1)) := by
    rw [hyn, show sy = Units.mk0 ν⁻¹ (inv_ne_zero hν0) from Units.ext (by rw [hsy]; rfl)]
    exact smul_mem_primeFormUnitary h hy (inv_ne_zero hν0) hνiN
  have hxn3 : xn ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hxn, coe_scalarGL_mul, smul_pow, hx3', smul_smul, hsx, ← hμ,
      ← mul_pow, inv_mul_cancel₀ hμ0, one_pow, one_smul, Units.val_one]
  have hyn3 : yn ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hyn, coe_scalarGL_mul, smul_pow, hy3', smul_smul, hsy, ← hν,
      ← mul_pow, inv_mul_cancel₀ hν0, one_pow, one_smul, Units.val_one]
  have hxyn : Commute xn yn := by
    rw [hxn, hyn]
    exact Commute.mul_left (Commute.mul_right (commute_scalarGL sx _) (commute_scalarGL sx _))
      (Commute.mul_right (commute_scalarGL sy x).symm hxy)
  let xu : primeFormUnitary h (idGram K (m + 1)) := ⟨xn, hxnU⟩
  let yu : primeFormUnitary h (idGram K (m + 1)) := ⟨yn, hynU⟩
  have hxyu : Commute xu yu := Subtype.ext hxyn.eq
  have hpair : ({xu, yu} : Set (primeFormUnitary h (idGram K (m + 1)))).Pairwise Commute := by
    rw [Set.pairwise_pair]; exact fun _ => ⟨hxyu, hxyu.symm⟩
  have hcomE : IsMulCommutative (Subgroup.closure ({xu, yu} : Set (primeFormUnitary h
      (idGram K (m + 1))))) := Subgroup.isMulCommutative_closure hpair
  have hcommE : ∀ u ∈ Subgroup.closure ({xu, yu} : Set (primeFormUnitary h (idGram K (m + 1)))),
      ∀ v ∈ Subgroup.closure ({xu, yu} : Set (primeFormUnitary h (idGram K (m + 1)))),
        u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hcomE.is_comm.comm (⟨u, hu⟩ : Subgroup.closure ({xu, yu} :
      Set (primeFormUnitary h (idGram K (m + 1))))) ⟨v, hv⟩)
  have hexpE : ∀ u ∈ Subgroup.closure ({xu, yu} : Set (primeFormUnitary h (idGram K (m + 1)))),
      u ^ 3 = 1 := by
    intro u hu
    refine Subgroup.closure_induction (p := fun u _ => u ^ 3 = 1) ?_ (by simp) ?_ ?_ hu
    · intro u hu
      rcases hu with rfl | hu
      · exact Subtype.ext hxn3
      · rw [Set.mem_singleton_iff] at hu
        rw [hu]; exact Subtype.ext hyn3
    · intro u v hu hv hu3 hv3
      rw [Commute.mul_pow (hcommE u hu v hv), hu3, hv3, one_mul]
    · intro u hu hu3
      rw [inv_pow, hu3, inv_one]
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag h Nat.prime_three hq3 _ hcommE hexpE
  have hxuE : xu ∈ Subgroup.closure ({xu, yu} : Set (primeFormUnitary h (idGram K (m + 1)))) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hyuE : yu ∈ Subgroup.closure ({xu, yu} : Set (primeFormUnitary h (idGram K (m + 1)))) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  set Pg : GL (Fin (m + 1)) K := (P : GL (Fin (m + 1)) K) with hPg
  have hdx : ((Pg⁻¹ * xn * Pg : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K).IsDiag := hP xu hxuE
  have hdy : ((Pg⁻¹ * yn * Pg : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K).IsDiag := hP yu hyuE
  obtain ⟨a, ha⟩ : ∃ a : Fin (m + 1) → K,
      ((Pg⁻¹ * xn * Pg : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
        diagonal a :=
    ⟨_, hdx.diagonal_diag.symm⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin (m + 1) → K,
      ((Pg⁻¹ * yn * Pg : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
        diagonal b :=
    ⟨_, hdy.diagonal_diag.symm⟩
  have hcube1 : ∀ (g : GL (Fin (m + 1)) K) (d : Fin (m + 1) → K), g ^ 3 = 1 →
      ((Pg⁻¹ * g * Pg : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
        diagonal d → ∀ i, d i ^ 3 = 1 := by
    intro g d hg3 hgd i
    have h1 : (Pg⁻¹ * g * Pg) ^ 3 = 1 := by
      have := conj_pow (a := Pg⁻¹) (b := g) (i := 3)
      rw [inv_inv] at this
      rw [this, hg3]; group
    have h2 : (diagonal d : Matrix (Fin (m + 1)) (Fin (m + 1)) K) ^ 3 = 1 := by
      rw [← hgd, ← Units.val_pow_eq_pow_val, h1, Units.val_one]
    rw [diagonal_pow] at h2
    have := congrFun (congrFun h2 i) i
    simpa using this
  have ha3 := hcube1 xn a hxn3 ha
  have hb3 := hcube1 yn b hyn3 hb
  have hxline : ((xn : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      (sx : K) • (x : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
    rw [hxn, coe_scalarGL_mul]
  have hyline : ((yn : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      (sy : K) • (y : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
    rw [hyn, coe_scalarGL_mul]
  have hline : ∀ t : ℕ, ((xn * yn ^ t : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
        ((sx : K) * (sy : K) ^ t) •
          ((x * y ^ t : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
    intro t
    rw [Units.val_mul, Units.val_pow_eq_pow_val, hxn, hyn, coe_scalarGL_mul, coe_scalarGL_mul,
      smul_pow, Units.val_mul, Units.val_pow_eq_pow_val, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]
  have hsx0 : (sx : K) ≠ 0 := sx.ne_zero
  have hsy0 : (sy : K) ≠ 0 := sy.ne_zero
  have hS : ∀ i : Fin m, ∃ g : GL (Fin (m + 1)) K,
      (∀ A : Matrix (Fin 2) (Fin 2) K,
        blockMat (m + 1) i A * (((P : GL (Fin (m + 1)) K)⁻¹ * g * P : GL (Fin (m + 1)) K) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
          (((P : GL (Fin (m + 1)) K)⁻¹ * g * P : GL (Fin (m + 1)) K) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) K) * blockMat (m + 1) i A) ∧
      ∀ w : unitarySU ℓ f K (m + 1), (w : GL (Fin (m + 1)) K) * g = g * w →
        w ∈ Subgroup.closure (FixUn ℓ f (m + 1) K (x : Matrix (Fin (m + 1)) (Fin (m + 1)) K) ∪
          FixUn ℓ f (m + 1) K (y : Matrix (Fin (m + 1)) (Fin (m + 1)) K) ∪
          FixUn ℓ f (m + 1) K ((x * y : GL (Fin (m + 1)) K) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) K) ∪
          FixUn ℓ f (m + 1) K ((x * y ^ 2 : GL (Fin (m + 1)) K) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) K)) := by
    intro i
    have haj : a i.succ ≠ 0 := fun h0 => by
      have := ha3 i.succ; rw [h0] at this; norm_num at this
    have hbj : b i.succ ≠ 0 := fun h0 => by
      have := hb3 i.succ; rw [h0] at this; norm_num at this
    have hr : (a i.castSucc * (a i.succ)⁻¹) ^ 3 = 1 := by
      rw [mul_pow, inv_pow, ha3 i.castSucc, ha3 i.succ, inv_one, one_mul]
    have hu : (b i.castSucc * (b i.succ)⁻¹) ^ 3 = 1 := by
      rw [mul_pow, inv_pow, hb3 i.castSucc, hb3 i.succ, inv_one, one_mul]
    have hlines : ∃ (g : GL (Fin (m + 1)) K) (L : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
        (c : K) (d : Fin (m + 1) → K),
        c ≠ 0 ∧ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = c • L ∧
        (L = (x : Matrix (Fin (m + 1)) (Fin (m + 1)) K) ∨
          L = (y : Matrix (Fin (m + 1)) (Fin (m + 1)) K) ∨
          L = ((x * y : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) ∨
          L = ((x * y ^ 2 : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) ∧
        (∀ k, d k ≠ 0) ∧ d i.castSucc = d i.succ ∧
        ((Pg⁻¹ * g * Pg : GL (Fin (m + 1)) K) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) = diagonal d := by
      have ha0 : ∀ k, a k ≠ 0 := fun k h0 => by
        have := ha3 k; rw [h0] at this; norm_num at this
      have hb0 : ∀ k, b k ≠ 0 := fun k h0 => by
        have := hb3 k; rw [h0] at this; norm_num at this
      rcases cube_roots_cases hr hu with h1 | h1 | h1 | h1
      · exact ⟨xn, _, _, a, hsx0, hxline, Or.inl rfl, ha0, (mul_inv_eq_one₀ haj).1 h1, ha⟩
      · exact ⟨yn, _, _, b, hsy0, hyline, Or.inr (Or.inl rfl), hb0,
          (mul_inv_eq_one₀ hbj).1 h1, hb⟩
      · refine ⟨xn * yn, _, (sx : K) * (sy : K) ^ 1, fun k => a k * b k,
          mul_ne_zero hsx0 (pow_ne_zero 1 hsy0), by simpa using hline 1,
          Or.inr (Or.inr (Or.inl (by simp))), fun k => mul_ne_zero (ha0 k) (hb0 k), ?_, ?_⟩
        · field_simp at h1
          linear_combination h1
        · have : Pg⁻¹ * (xn * yn) * Pg = (Pg⁻¹ * xn * Pg) * (Pg⁻¹ * yn * Pg) := by group
          rw [this, Units.val_mul, ha, hb, diagonal_mul_diagonal]
      · refine ⟨xn * yn ^ 2, _, (sx : K) * (sy : K) ^ 2, fun k => a k * b k ^ 2,
          mul_ne_zero hsx0 (pow_ne_zero 2 hsy0), hline 2, Or.inr (Or.inr (Or.inr rfl)),
          fun k => mul_ne_zero (ha0 k) (pow_ne_zero 2 (hb0 k)), ?_, ?_⟩
        · field_simp at h1
          linear_combination h1
        · have : Pg⁻¹ * (xn * yn ^ 2) * Pg = (Pg⁻¹ * xn * Pg) * (Pg⁻¹ * yn * Pg) ^ 2 := by
            simp only [pow_two]; group
          rw [this, Units.val_mul, Units.val_pow_eq_pow_val, ha, hb, diagonal_pow,
            diagonal_mul_diagonal]
          rfl
    obtain ⟨g, L, c, d, hc, hgL, hL, hd0, hdeq, hdg⟩ := hlines
    refine ⟨g, fun A => ?_, fun w hw => ?_⟩
    · rw [hdg]
      exact blockMat_mul_diagonal_comm (by omega) d hd0 i.castSucc i.succ (by simp) (by simp)
        hdeq A
    · have hwL : ((w : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) * L =
          L * ((w : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
        have h1 := congrArg Units.val hw
        rw [Units.val_mul, Units.val_mul, hgL, Matrix.mul_smul, Matrix.smul_mul] at h1
        exact smul_right_injective _ hc h1
      have hwF : w ∈ FixUn ℓ f (m + 1) K L := mem_FixUn_of_mul_comm hwL
      refine Subgroup.subset_closure ?_
      rcases hL with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl (Or.inl hwF))
      · exact Or.inl (Or.inl (Or.inr hwF))
      · exact Or.inl (Or.inr hwF)
      · exact Or.inr hwF
  exact eq_top_of_block_centralizers (n := m) h hq P _ hS

end CFSG.LieType.SeitzGeneration
