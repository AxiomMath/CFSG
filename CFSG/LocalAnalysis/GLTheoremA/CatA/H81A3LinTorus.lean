module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinBlock
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeLift
import CFSG.RankThree.PartOne.CTP.SeitzDiag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81.LinA3

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.CatalogueBHigherLinearAction

variable {F : Type} [Field F]

abbrev torusSet (p : ℕ) (F : Type) [Field F] : Set (Fin 4 → F) :=
  {d | (∀ i, d i ^ p = 1) ∧ ∏ i, d i = 1}

theorem natCard_torusSet_le [Finite F] {p : ℕ} (hp : 0 < p) :
    Nat.card (torusSet p F) ≤ p ^ 3 := by
  classical
  set R : Set F := {x | x ^ p = 1} with hR
  have hRcard : Nat.card R ≤ p := by
    have hsub : R ⊆ ((Polynomial.nthRoots p (1 : F)).toFinset : Set F) := fun x hx => by
      rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hp]
      exact hx
    calc Nat.card R ≤ Nat.card ((Polynomial.nthRoots p (1 : F)).toFinset : Set F) :=
          Nat.card_mono (Set.toFinite _) hsub
      _ = (Polynomial.nthRoots p (1 : F)).toFinset.card := Nat.card_coe_set_eq _ |>.trans
          (Set.ncard_coe_finset _)
      _ ≤ (Polynomial.nthRoots p (1 : F)).card := Multiset.toFinset_card_le _
      _ ≤ p := Polynomial.card_nthRoots p 1
  let φ : torusSet p F → (Fin 3 → R) := fun d k =>
    ⟨(d : Fin 4 → F) (Fin.castSucc k), d.2.1 _⟩
  have hφ : Function.Injective φ := by
    intro d e hde
    have h3 : ∀ k : Fin 3, (d : Fin 4 → F) (Fin.castSucc k) = (e : Fin 4 → F) (Fin.castSucc k) :=
      fun k => congrArg Subtype.val (congrFun hde k)
    have hprod : ∀ x : torusSet p F, ∏ i, (x : Fin 4 → F) i =
        (x : Fin 4 → F) 0 * (x : Fin 4 → F) 1 * (x : Fin 4 → F) 2 * (x : Fin 4 → F) 3 := by
      intro x
      rw [Fin.prod_univ_four]
    have hd := d.2.2
    have he := e.2.2
    rw [hprod] at hd he
    have h0 := h3 0
    have h1 := h3 1
    have h2 := h3 2
    simp only [Fin.castSucc_zero] at h0
    have h1' : (d : Fin 4 → F) 1 = (e : Fin 4 → F) 1 := h1
    have h2' : (d : Fin 4 → F) 2 = (e : Fin 4 → F) 2 := h2
    have hne : (d : Fin 4 → F) 0 * (d : Fin 4 → F) 1 * (d : Fin 4 → F) 2 ≠ 0 := by
      intro h0'
      rw [h0', zero_mul] at hd
      exact zero_ne_one hd
    have h33 : (d : Fin 4 → F) 3 = (e : Fin 4 → F) 3 := by
      have : (d : Fin 4 → F) 0 * (d : Fin 4 → F) 1 * (d : Fin 4 → F) 2 * (d : Fin 4 → F) 3 =
          (d : Fin 4 → F) 0 * (d : Fin 4 → F) 1 * (d : Fin 4 → F) 2 * (e : Fin 4 → F) 3 := by
        rw [hd, h0, h1', h2', he]
      exact mul_left_cancel₀ hne this
    apply Subtype.ext
    funext i
    fin_cases i
    · exact h0
    · exact h1'
    · exact h2'
    · exact h33
  have : Finite R := Set.toFinite _
  calc Nat.card (torusSet p F) ≤ Nat.card (Fin 3 → R) := Nat.card_le_card_of_injective φ hφ
    _ = Nat.card R ^ 3 := by rw [Nat.card_fun, Nat.card_fin]
    _ ≤ p ^ 3 := Nat.pow_le_pow_left hRcard 3

variable [Finite F]

theorem exists_conjAut_diagSL_mem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : F, IsPrimitiveRoot ζ p) {P : Subgroup (projectiveSL 4 F)}
    (hP : IsElemAbelian p P) (hcard : Nat.card P = p ^ 3) :
    ∃ g : GL (Fin 4) F, ∀ (d : Fin 4 → F) (hd : ∏ i, d i = 1), (∀ i, d i ^ p = 1) →
      proj 4 F (diagSL d hd) ∈ P.map (conjAut 4 F g).toMonoidHom := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hnp : ∀ z ∈ (proj 4 F).ker, z ^ p = 1 → z = 1 := fun z hz hzp => by
    rw [ker_proj] at hz
    exact eq_one_of_mem_scalars_of_pow_eq_one hp hp2 hz hzp
  obtain ⟨A, hAP, -, hAel, hAcard⟩ :=
    CFSG.StandardType.TableBUE.exists_lift_of_noTorsion (proj 4 F) (proj_surjective 4 F) hp hnp hP
  set E : Subgroup (GL (Fin 4) F) := A.map SpecialLinearGroup.toGL with hE
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAel.1.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.CTP.exists_conj_diagonal_of_exponent_prime hζ E
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hAcomm a ha b hb])
    (by
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hAel.2 a ha, map_one])
  refine ⟨g, ?_⟩
  set c := slConjugation 4 F g with hc
  set A' : Subgroup (SpecialLinearGroup (Fin 4) F) := A.map c.toMonoidHom with hA'
  have hA'P : A'.map (proj 4 F) = P.map (conjAut 4 F g).toMonoidHom := by
    rw [← hAP, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hdiag : ∀ x ∈ A', ∀ i j, i ≠ j → (x : Matrix (Fin 4) (Fin 4) F) i j = 0 := by
    rintro _ ⟨a, ha, rfl⟩ i j hij
    have h := hg (SpecialLinearGroup.toGL a) ⟨a, ha, rfl⟩ i j hij
    rw [MulEquiv.coe_toMonoidHom, hc, coe_slConjugation]
    rwa [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h
  have hpow : ∀ x ∈ A', x ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hAel.2 a ha, map_one]
  have hA'card : Nat.card A' = p ^ 3 := by
    rw [hA', Subgroup.card_map_of_injective c.injective, hAcard, hcard]
  have hmemT : ∀ x : A', (fun i => ((x : SpecialLinearGroup (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) i i) ∈ torusSet p F := by
    intro x
    have hxd : ((x : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        diagonal fun i => ((x : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) i i := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · rw [diagonal_apply_ne _ hij, hdiag x x.2 i j hij]
    refine ⟨fun i => ?_, ?_⟩
    · have h1 := congrArg (fun y : SpecialLinearGroup (Fin 4) F =>
        (y : Matrix (Fin 4) (Fin 4) F) i i) (hpow x x.2)
      simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
        one_apply_eq] at h1
      rw [hxd, diagonal_pow, diagonal_apply_eq] at h1
      exact h1
    · have h1 := Matrix.SpecialLinearGroup.det_coe (x : SpecialLinearGroup (Fin 4) F)
      rw [hxd, det_diagonal] at h1
      exact h1
  let δ : A' → torusSet p F := fun x => ⟨_, hmemT x⟩
  have hδ : Function.Injective δ := by
    intro x y hxy
    have h1 := congrArg Subtype.val hxy
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    by_cases hij : i = j
    · subst hij
      exact congrFun h1 i
    · rw [hdiag x x.2 i j hij, hdiag y y.2 i j hij]
  have hT : Nat.card (torusSet p F) ≤ Nat.card A' := by
    rw [hA'card]
    exact natCard_torusSet_le hp.pos
  have : Finite (torusSet p F) := Set.toFinite _
  have hbij := hδ.bijective_of_nat_card_le hT
  intro d hd hdp
  obtain ⟨x, hx⟩ := hbij.2 ⟨d, hdp, hd⟩
  have hxd : (x : SpecialLinearGroup (Fin 4) F) = diagSL d hd := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [coe_diagSL]
    have h1 := congrArg Subtype.val hx
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
      exact congrFun h1 i
    · rw [diagonal_apply_ne _ hij, hdiag x x.2 i j hij]
  rw [← hA'P, ← hxd]
  exact Subgroup.mem_map_of_mem _ x.2

end CFSG.LocalAnalysis.GLTheoremA.H81.LinA3
