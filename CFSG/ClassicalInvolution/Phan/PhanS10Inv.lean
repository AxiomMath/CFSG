module

public import CFSG.ClassicalInvolution.Phan.PhanH7Model
public import CFSG.ClassicalInvolution.Phan.PhanB4Inf
public import CFSG.ClassicalInvolution.Phan.PhanS5Act

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.PhanB3
  CFSG.ClassicalInvolution.PhanD4 CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock)
open CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras CFSG.ClassicalInvolution.WeakCT
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped MatrixGroups

section SL2

variable {F : Type} [Field F]

theorem SL2_eq_one_or_neg_one_of_mul_self (h2 : (2 : F) ≠ 0) (A : SL(2, F)) (h : A * A = 1) :
    A = 1 ∨ A = -1 := by
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  have hA : (A : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have := congrArg (fun B : SL(2, F) => (B : Matrix (Fin 2) (Fin 2) F)) h
    simpa using this
  have e00 := congrFun (congrFun hA 0) 0
  have e01 := congrFun (congrFun hA 0) 1
  have e10 := congrFun (congrFun hA 1) 0
  have e11 := congrFun (congrFun hA 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  set a := (A : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set b := (A : Matrix (Fin 2) (Fin 2) F) 0 1 with hb
  set c := (A : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d := (A : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  by_cases had : a + d = 0
  · exfalso
    apply h2
    have hd' : d = -a := by linear_combination had
    rw [hd'] at hdet
    linear_combination (-1 : F) * e00 - hdet
  · have hb0 : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right had
    have hc0 : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right had
    rw [hb0, hc0] at e00 e11 hdet
    have haa : a * a = 1 := by linear_combination e00
    have had1 : a * d = 1 := by linear_combination hdet
    have ha0 : a ≠ 0 := fun h0 => by rw [h0] at haa; simp at haa
    have hda : d = a := by
      apply mul_left_cancel₀ ha0
      linear_combination had1 - haa
    have hpm : a = 1 ∨ a = -1 := by
      have : (a - 1) * (a + 1) = 0 := by linear_combination haa
      rcases mul_eq_zero.mp this with h1 | h1
      · exact Or.inl (by linear_combination h1)
      · exact Or.inr (by linear_combination h1)
    rcases hpm with h1 | h1
    · left
      refine Subtype.ext (Matrix.ext fun i j => ?_)
      fin_cases i <;> fin_cases j <;> simp [← ha, ← hb, ← hc, ← hd, hb0, hc0, hda, h1]
    · right
      refine Subtype.ext (Matrix.ext fun i j => ?_)
      fin_cases i <;> fin_cases j <;> simp [← ha, ← hb, ← hc, ← hd, hb0, hc0, hda, h1]

end SL2

section Node1

variable {F : Type} [Field F] {h2 : (2 : F) ≠ 0}

theorem U1_spec [Finite F] (Dθ : ThetaData F h2) (h4 : 4 ≤ Nat.card F) :
    ((longBlock F 2 1).range.map Dθ.θ).map (spinAction (quadOdd 3 F)) = (fr1 h2).La.range ∧
      ∀ r ∈ (longBlock F 2 1).range.map Dθ.θ, spinAction (quadOdd 3 F) r = 1 → r = 1 := by
  have hU1eq : (longBlock F 2 1).range.map Dθ.θ =
      ((hyp1 h2).longSL2 (i := 0) (j := 1) (by decide) true false).range := by
    rw [← MonoidHom.range_comp, ← spBlock_one_eq_longBlock,
      theta_comp_spBlock_one h2 Dθ.isLevi Dθ.coe_θ]
  obtain ⟨h1, -, h3⟩ := longSL2_spec (hyp1 h2) (i := 0) (j := 1) (by decide) true false h4
  rw [hU1eq]
  exact ⟨h1, h3⟩

end Node1

section Inv

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {hK : Nat.card K = (p ^ f) ^ 2} {F : Type} [Field F] {h2 : (2 : F) ≠ 0}
  {C : B2Coord hK F h2} {G : Type} [Group G] (E : PhanFamilyB3 C G)

@[expose] noncomputable def sInv (i : Fin 3) : G :=
  tor E i (negOne (unitaryInvolution K p f))

variable {E}

theorem sInv_mem_range (i : Fin 3) : sInv E i ∈ (E.ι i).range :=
  ⟨torusTwo (unitaryInvolution K p f) (negOne (unitaryInvolution K p f)), rfl⟩

theorem sInv_mul_self (i : Fin 3) : sInv E i * sInv E i = 1 := by
  rw [sInv, ← map_mul, negOne_mul_self, map_one]

theorem sInv_ne_one (hg : GoodFamily E) (h2K : (2 : K) ≠ 0) (i : Fin 3) : sInv E i ≠ 1 := by
  intro h
  have h' : torusTwo (unitaryInvolution K p f) (negOne (unitaryInvolution K p f)) = 1 :=
    hg.inj i (by simpa [sInv, tor] using h.trans (map_one (E.ι i)).symm)
  exact negOne_ne_one _ h2K (torusTwo_injective _ (by rw [h', map_one]))

theorem sInv_mem_torusSub (i : Fin 3) : sInv E i ∈ torusSub E :=
  ⟨Pi.mulSingle i (negOne (unitaryInvolution K p f)), mTor_mulSingle E i _⟩

theorem torusSub_comm_sInv {t : G} (ht : t ∈ torusSub E) (i : Fin 3) :
    t * sInv E i = sInv E i * t := by
  obtain ⟨τ, rfl⟩ := ht
  rw [mTor_apply]
  have h0 : Commute (tor E 0 (τ 0)) (sInv E i) := tor_comm E 0 i _ _
  have h1 : Commute (tor E 1 (τ 1)) (sInv E i) := tor_comm E 1 i _ _
  have h2' : Commute (tor E 2 (τ 2)) (sInv E i) := tor_comm E 2 i _ _
  exact ((h0.mul_left h1).mul_left h2')

end Inv

section Model

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2} {M : ModelB3 p f h2}
  {E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))}

theorem spinAction_sInv_zero (hg : GoodFamily E) (h2K : (2 : GaloisField p (2 * f)) ≠ 0)
    (hr : (E.ι 0).range = M.U 0) :
    spinAction (quadOdd 3 (GaloisField p f)) (sInv E 0) = (fr0 h2).La (-1) := by
  have hmem : sInv E 0 ∈ M.R₀ := by
    have := sInv_mem_range (E := E) 0
    rw [hr] at this
    exact this
  obtain ⟨A, hA⟩ : spinAction (quadOdd 3 (GaloisField p f)) (sInv E 0) ∈ (fr0 h2).La.range := by
    rw [← M.map_eq]
    exact ⟨_, hmem, rfl⟩
  have hsq : A * A = 1 := by
    apply (fr0 h2).La_injective
    rw [map_mul, hA, ← map_mul, sInv_mul_self, map_one, map_one]
  have h2F : (2 : GaloisField p f) ≠ 0 := h2
  rcases SL2_eq_one_or_neg_one_of_mul_self h2F A hsq with h | h
  · exfalso
    refine sInv_ne_one hg h2K 0 (M.inj _ hmem ?_)
    rw [← hA, h, map_one]
  · rw [← hA, h]

theorem spinAction_sInv_one (hg : GoodFamily E) (h2K : (2 : GaloisField p (2 * f)) ≠ 0)
    (h4 : 4 ≤ Nat.card (GaloisField p f)) (hr : (E.ι 1).range = M.U 1) :
    spinAction (quadOdd 3 (GaloisField p f)) (sInv E 1) = (fr1 h2).La (-1) := by
  obtain ⟨hmap, hinj⟩ := U1_spec M.D h4
  have hmem : sInv E 1 ∈ (longBlock (GaloisField p f) 2 1).range.map M.D.θ := by
    have := sInv_mem_range (E := E) 1
    rw [hr] at this
    exact this
  obtain ⟨A, hA⟩ : spinAction (quadOdd 3 (GaloisField p f)) (sInv E 1) ∈ (fr1 h2).La.range := by
    rw [← hmap]
    exact ⟨_, hmem, rfl⟩
  have hsq : A * A = 1 := by
    apply (fr1 h2).La_injective
    rw [map_mul, hA, ← map_mul, sInv_mul_self, map_one, map_one]
  have h2F : (2 : GaloisField p f) ≠ 0 := h2
  rcases SL2_eq_one_or_neg_one_of_mul_self h2F A hsq with h | h
  · exfalso
    refine sInv_ne_one hg h2K 1 (hinj _ hmem ?_)
    rw [← hA, h, map_one]
  · rw [← hA, h]

end Model

section Eigen

variable {F : Type} [Field F] {h2 : (2 : F) ≠ 0}

theorem La0_neg_one_P (s z : F) :
    (fr0 h2).La (-1) (mk7 s 0 0 s 0 0 z) = -mk7 s 0 0 s 0 0 z := by
  rw [La0_neg_one, neg_mk7]
  simp

theorem La1_neg_one_P (s z : F) :
    (fr1 h2).La (-1) (mk7 s 0 0 s 0 0 z) = mk7 s 0 0 s 0 0 z := by
  rw [La1_neg_one]
  simp

theorem La0_neg_one_Pp (a b : F) :
    (fr0 h2).La (-1) (mk7 0 a b 0 (-a) (-b) 0) = -mk7 0 a b 0 (-a) (-b) 0 := by
  rw [La0_neg_one, neg_mk7]
  simp

theorem La1_neg_one_Pp (a b : F) :
    (fr1 h2).La (-1) (mk7 0 a b 0 (-a) (-b) 0) = -mk7 0 a b 0 (-a) (-b) 0 := by
  rw [La1_neg_one, neg_mk7]
  simp

theorem exists_P_of_eigen (y : W7 F) (h0 : (fr0 h2).La (-1) y = -y)
    (h1 : (fr1 h2).La (-1) y = y) : ∃ s z : F, y = mk7 s 0 0 s 0 0 z := by
  have hx : ∀ t : F, t = -t → t = 0 := fun t ht => by
    have : (2 : F) * t = 0 := by linear_combination ht
    exact (mul_eq_zero.mp this).resolve_left h2
  rw [La0_neg_one] at h0
  rw [La1_neg_one] at h1
  have a1 := congrFun h1 (.inl 1)
  have a2 := congrFun h1 (.inl 2)
  have a3 := congrFun h1 (.inr (.inl 1))
  have a4 := congrFun h1 (.inr (.inl 2))
  have b0 := congrFun h0 (.inl 0)
  simp at a1 a2 a3 a4 b0
  have e1 := hx _ a1.symm
  have e2 := hx _ a2.symm
  have e3 := hx _ a3.symm
  have e4 := hx _ a4.symm
  refine ⟨y (.inl 0), y (.inr (.inr ())), ?_⟩
  conv_lhs => rw [mk7_eta y]
  rw [e1, e2, e3, e4, ← b0]

theorem exists_Pp_of_eigen (y : W7 F) (h0 : (fr0 h2).La (-1) y = -y)
    (h1 : (fr1 h2).La (-1) y = -y) : ∃ a b : F, y = mk7 0 a b 0 (-a) (-b) 0 := by
  have hx : ∀ t : F, t = -t → t = 0 := fun t ht => by
    have : (2 : F) * t = 0 := by linear_combination ht
    exact (mul_eq_zero.mp this).resolve_left h2
  rw [La0_neg_one] at h0
  rw [La1_neg_one] at h1
  have a1 := congrFun h1 (.inl 0)
  have a2 := congrFun h1 (.inr (.inl 0))
  have a3 := congrFun h1 (.inr (.inr ()))
  have b1 := congrFun h0 (.inr (.inl 1))
  have b2 := congrFun h0 (.inr (.inl 2))
  simp at a1 a2 a3 b1 b2
  have e1 := hx _ a1
  have e2 := hx _ a2
  have e3 := hx _ a3
  refine ⟨y (.inl 1), y (.inl 2), ?_⟩
  conv_lhs => rw [mk7_eta y]
  have f1 : y (.inr (.inl 1)) = -y (.inl 1) := by linear_combination b1
  have f2 : y (.inr (.inl 2)) = -y (.inl 2) := by linear_combination b2
  rw [e1, e2, e3, f1, f2]

end Eigen

section TorusP

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2} {M : ModelB3 p f h2}
  {E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))}

theorem spinAction_comm_sInv {t : spinGroup (quadOdd 3 (GaloisField p f))} (ht : t ∈ torusSub E)
    (i : Fin 3) (x : W7 (GaloisField p f)) :
    spinAction (quadOdd 3 (GaloisField p f)) t
        (spinAction (quadOdd 3 (GaloisField p f)) (sInv E i) x) =
      spinAction (quadOdd 3 (GaloisField p f)) (sInv E i)
        (spinAction (quadOdd 3 (GaloisField p f)) t x) := by
  rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul,
    torusSub_comm_sInv ht i]

theorem torus_mapsTo_P (hg : GoodFamily E) (h2K : (2 : GaloisField p (2 * f)) ≠ 0)
    (h4 : 4 ≤ Nat.card (GaloisField p f)) (hr : ∀ i, (E.ι i).range = M.U i)
    {t : spinGroup (quadOdd 3 (GaloisField p f))} (ht : t ∈ torusSub E) (s z : GaloisField p f) :
    ∃ s' z' : GaloisField p f,
      spinAction (quadOdd 3 (GaloisField p f)) t (mk7 s 0 0 s 0 0 z) = mk7 s' 0 0 s' 0 0 z' := by
  have s0 := spinAction_sInv_zero hg h2K (hr 0)
  have s1 := spinAction_sInv_one hg h2K h4 (hr 1)
  refine exists_P_of_eigen (h2 := h2) _ ?_ ?_
  · rw [← s0, ← spinAction_comm_sInv ht 0, s0, La0_neg_one_P, map_neg]
  · rw [← s1, ← spinAction_comm_sInv ht 1, s1, La1_neg_one_P]

theorem torus_mapsTo_Pp (hg : GoodFamily E) (h2K : (2 : GaloisField p (2 * f)) ≠ 0)
    (h4 : 4 ≤ Nat.card (GaloisField p f)) (hr : ∀ i, (E.ι i).range = M.U i)
    {t : spinGroup (quadOdd 3 (GaloisField p f))} (ht : t ∈ torusSub E) (a b : GaloisField p f) :
    ∃ a' b' : GaloisField p f,
      spinAction (quadOdd 3 (GaloisField p f)) t (mk7 0 a b 0 (-a) (-b) 0) =
        mk7 0 a' b' 0 (-a') (-b') 0 := by
  have s0 := spinAction_sInv_zero hg h2K (hr 0)
  have s1 := spinAction_sInv_one hg h2K h4 (hr 1)
  refine exists_Pp_of_eigen (h2 := h2) _ ?_ ?_
  · rw [← s0, ← spinAction_comm_sInv ht 0, s0, La0_neg_one_Pp, map_neg]
  · rw [← s1, ← spinAction_comm_sInv ht 1, s1, La1_neg_one_Pp, map_neg]

end TorusP

end CFSG.ClassicalInvolution.PhanB3.S
