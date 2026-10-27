module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318
public import CFSG.RankThree.CentralCover.SteinbergBNChevalleySplitTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE8Model
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318Local

open CFSG.Open CFSG.HardMathSupport.Dickson.I271

namespace Gen2318LocalAux

open CFSG.LieType.Steinberg.CentralExt.SLClosed

abbrev SLn (n : ℕ) (F : Type) [Field F] : Type := Matrix.SpecialLinearGroup (Fin n) F

theorem exists_lift_sl {F : Type} [Field F] [Finite F] {m : ℕ} (hm : 2 ≤ m)
    (hsep : Separating m F) {K S : Type} [Group K] [Group S]
    (ρ : K →* S) (hρ : Function.Surjective ρ) (hρk : ρ.ker ≤ Subgroup.center K)
    (π : SLn (m + 1) F →* S) :
    ∃ σ : SLn (m + 1) F →* K, ∀ g, ρ (σ g) = π g := by
  let W : Subgroup (SLn (m + 1) F × K) :=
    { carrier := {x | π x.1 = ρ x.2}
      mul_mem' := fun {a b} ha hb => by
        show π (a * b).1 = ρ (a * b).2
        rw [Prod.fst_mul, Prod.snd_mul, map_mul, map_mul]
        exact congrArg₂ (· * ·) ha hb
      one_mem' := by
        show π (1 : SLn (m + 1) F × K).1 = ρ (1 : SLn (m + 1) F × K).2
        simp
      inv_mem' := fun {a} ha => by
        show π (a⁻¹).1 = ρ (a⁻¹).2
        rw [Prod.fst_inv, Prod.snd_inv, map_inv, map_inv]
        exact congrArg (·⁻¹) ha }
  let p1 : W →* SLn (m + 1) F := (MonoidHom.fst _ _).comp W.subtype
  have hp1 : Function.Surjective p1 := by
    intro g
    obtain ⟨k, hk⟩ := hρ (π g)
    exact ⟨⟨(g, k), hk.symm⟩, rfl⟩
  have hcen : p1.ker ≤ Subgroup.center W := by
    intro x hx
    have h1 : (x : SLn (m + 1) F × K).1 = 1 := by
      rw [MonoidHom.mem_ker] at hx
      exact hx
    have hz : (x : SLn (m + 1) F × K).2 ∈ Subgroup.center K := by
      apply hρk
      rw [MonoidHom.mem_ker]
      have hx' : π (x : SLn (m + 1) F × K).1 = ρ (x : SLn (m + 1) F × K).2 := x.2
      rw [h1, map_one] at hx'
      exact hx'.symm
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · show (y : SLn (m + 1) F × K).1 * (x : SLn (m + 1) F × K).1 =
        (x : SLn (m + 1) F × K).1 * (y : SLn (m + 1) F × K).1
      rw [h1, mul_one, one_mul]
    · show (y : SLn (m + 1) F × K).2 * (x : SLn (m + 1) F × K).2 =
        (x : SLn (m + 1) F × K).2 * (y : SLn (m + 1) F × K).2
      exact Subgroup.mem_center_iff.1 hz _
  obtain ⟨s, hs⟩ := sl_exists_section_of_separating hm hsep hp1 hcen
  refine ⟨(MonoidHom.snd _ _).comp (W.subtype.comp s), fun g => ?_⟩
  have hmem : π (s g : SLn (m + 1) F × K).1 = ρ (s g : SLn (m + 1) F × K).2 := (s g).2
  have hfst : (s g : SLn (m + 1) F × K).1 = g := hs g
  calc ρ (((MonoidHom.snd _ _).comp (W.subtype.comp s)) g)
      = ρ (s g : SLn (m + 1) F × K).2 := rfl
    _ = π (s g : SLn (m + 1) F × K).1 := hmem.symm
    _ = π g := by rw [hfst]

section Torus

variable {F : Type} [Field F]

theorem card_mu3 [Finite F] (hF : Nat.card F = 4) : Nat.card (rootsOfUnity 3 F) = 3 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have h4 : Fintype.card F = 4 := by rw [Fintype.card_eq_nat_card]; exact hF
  rw [card_rootsOfUnity_eq_gcd 3, h4]
  norm_num

@[expose] def tDiag {M : ℕ} (x : Fin M → rootsOfUnity 3 F) : Fin (M + 1 + 1) → Fˣ :=
  Fin.snoc (α := fun _ => Fˣ)
    (Fin.snoc (α := fun _ => Fˣ) (fun j => ((x j : rootsOfUnity 3 F) : Fˣ))
      (∏ j, ((x j : rootsOfUnity 3 F) : Fˣ))⁻¹) 1

theorem tDiag_castSucc_castSucc {M : ℕ} (x : Fin M → rootsOfUnity 3 F) (j : Fin M) :
    tDiag x j.castSucc.castSucc = ((x j : rootsOfUnity 3 F) : Fˣ) := by
  simp [tDiag]

theorem tDiag_last_castSucc {M : ℕ} (x : Fin M → rootsOfUnity 3 F) :
    tDiag x (Fin.last M).castSucc = (∏ j, ((x j : rootsOfUnity 3 F) : Fˣ))⁻¹ := by
  simp [tDiag]

theorem tDiag_last {M : ℕ} (x : Fin M → rootsOfUnity 3 F) :
    tDiag x (Fin.last (M + 1)) = 1 := by
  simp [tDiag]

theorem tDiag_mul {M : ℕ} (x y : Fin M → rootsOfUnity 3 F) :
    tDiag (x * y) = tDiag x * tDiag y := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [tDiag_last]
  | cast i =>
    induction i using Fin.lastCases with
    | last => simp [tDiag_last_castSucc, Finset.prod_mul_distrib, mul_inv, mul_comm]
    | cast j => simp [tDiag_castSucc_castSucc]

theorem prod_tDiag {M : ℕ} (x : Fin M → rootsOfUnity 3 F) : ∏ i, tDiag x i = 1 := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  simp [tDiag_castSucc_castSucc, tDiag_last_castSucc, tDiag_last]

@[expose] def torusElt {M : ℕ} (x : Fin M → rootsOfUnity 3 F) :
    Matrix.SpecialLinearGroup (Fin (M + 1 + 1)) F :=
  ⟨Matrix.diagonal (fun i => ((tDiag x i : Fˣ) : F)), by
    rw [Matrix.det_diagonal, ← Units.coe_prod, prod_tDiag, Units.val_one]⟩

theorem torusElt_mul {M : ℕ} (x y : Fin M → rootsOfUnity 3 F) :
    torusElt (x * y) = torusElt x * torusElt y := by
  apply Subtype.ext
  change Matrix.diagonal (fun i => ((tDiag (x * y) i : Fˣ) : F)) =
    Matrix.diagonal (fun i => ((tDiag x i : Fˣ) : F)) *
      Matrix.diagonal (fun i => ((tDiag y i : Fˣ) : F))
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [tDiag_mul]
  simp

@[expose] def torusHom (M : ℕ) :
    (Fin M → rootsOfUnity 3 F) →* Matrix.SpecialLinearGroup (Fin (M + 1 + 1)) F :=
  MonoidHom.mk' torusElt (fun x y => torusElt_mul x y)

theorem torusHom_apply {M : ℕ} (x : Fin M → rootsOfUnity 3 F) :
    torusHom (F := F) M x = torusElt x :=
  rfl

theorem torusHom_injective (M : ℕ) : Function.Injective (torusHom (F := F) M) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hdiag : ∀ i, tDiag x i = 1 := by
    intro i
    have h := congrArg (fun A : Matrix.SpecialLinearGroup (Fin (M + 1 + 1)) F =>
      (A : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) F) i i) hx
    change Matrix.diagonal (fun k => ((tDiag x k : Fˣ) : F)) i i =
      (1 : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) F) i i at h
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h
    exact Units.ext h
  funext j
  apply Subtype.ext
  have h := hdiag j.castSucc.castSucc
  rw [tDiag_castSucc_castSucc] at h
  simpa using h

@[expose] def trSL {n : ℕ} (i j : Fin n) (h : i ≠ j) (c : F) :
    Matrix.SpecialLinearGroup (Fin n) F :=
  ⟨Matrix.transvection i j c, Matrix.det_transvection_of_ne i j h c⟩

theorem tDiag_eq_of_central {M : ℕ} (x : Fin M → rootsOfUnity 3 F)
    (hz : torusElt x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (M + 1 + 1)) F))
    {i j : Fin (M + 1 + 1)} (hij : i ≠ j) :
    ((tDiag x i : Fˣ) : F) = ((tDiag x j : Fˣ) : F) := by
  have hc := Subgroup.mem_center_iff.1 hz (trSL (F := F) i j hij 1)
  have h := congrArg (fun A : Matrix.SpecialLinearGroup (Fin (M + 1 + 1)) F =>
    (A : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) F) i j) hc
  have hD : (torusElt x : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) F) =
      Matrix.diagonal (fun k => ((tDiag x k : Fˣ) : F)) := rfl
  have hT : (trSL (F := F) i j hij 1 : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) F) =
      Matrix.transvection i j 1 := rfl
  simp only [Matrix.SpecialLinearGroup.coe_mul, hD, hT] at h
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  simp [Matrix.transvection, Matrix.single_apply, hij] at h
  exact h.symm

theorem torusElt_eq_one_of_central {M : ℕ} (x : Fin M → rootsOfUnity 3 F)
    (hz : torusElt x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (M + 1 + 1)) F)) :
    x = 1 := by
  have hall : ∀ i : Fin (M + 1 + 1), tDiag x i = 1 := by
    intro i
    by_cases hi : i = Fin.last (M + 1)
    · rw [hi, tDiag_last]
    · apply Units.ext
      rw [tDiag_eq_of_central x hz hi, tDiag_last, Units.val_one]
  funext j
  apply Subtype.ext
  have h := hall j.castSucc.castSucc
  rw [tDiag_castSucc_castSucc] at h
  simpa using h

theorem zero_ne_one_fin (M : ℕ) : (0 : Fin (M + 1 + 1)) ≠ 1 := by
  simp [Fin.ext_iff]

@[expose] def rootSL (M : ℕ) (c : F) : Matrix.SpecialLinearGroup (Fin (M + 1 + 1)) F :=
  trSL (0 : Fin (M + 1 + 1)) 1 (zero_ne_one_fin M) c

theorem rootSL_mul (M : ℕ) (c d : F) : rootSL (F := F) M c * rootSL M d = rootSL M (c + d) := by
  apply Subtype.ext
  have h := zero_ne_one_fin M
  change Matrix.transvection (0 : Fin (M + 1 + 1)) 1 c * Matrix.transvection (0 : Fin (M + 1 + 1)) 1 d =
    Matrix.transvection (0 : Fin (M + 1 + 1)) 1 (c + d)
  simp [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, h.symm, add_assoc, Matrix.single_add]

theorem rootSL_zero (M : ℕ) : rootSL (F := F) M 0 = 1 := by
  apply Subtype.ext
  change Matrix.transvection (0 : Fin (M + 1 + 1)) 1 (0 : F) = 1
  simp [Matrix.transvection]

theorem torusElt_mul_rootSL (M : ℕ) (x : Fin M → rootsOfUnity 3 F) (c : F) :
    torusElt x * rootSL M c =
      rootSL M (((tDiag x 0 : Fˣ) : F) * c * ((tDiag x 1 : Fˣ) : F)⁻¹) * torusElt x := by
  apply Subtype.ext
  change Matrix.diagonal (fun k => ((tDiag x k : Fˣ) : F)) * Matrix.transvection (0 : Fin (M + 1 + 1)) 1 c =
    Matrix.transvection (0 : Fin (M + 1 + 1)) 1 (((tDiag x 0 : Fˣ) : F) * c * ((tDiag x 1 : Fˣ) : F)⁻¹) *
      Matrix.diagonal (fun k => ((tDiag x k : Fˣ) : F))
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases h01 : (0 : Fin (M + 1 + 1)) = a ∧ (1 : Fin (M + 1 + 1)) = b
  · obtain ⟨rfl, rfl⟩ := h01
    have hne : ((tDiag x 1 : Fˣ) : F) ≠ 0 := Units.ne_zero _
    simp [zero_ne_one_fin M]
  · by_cases hab : a = b
    · subst hab
      simp [h01]
    · simp [hab, h01]

theorem rootSL_not_central (M : ℕ) (h2 : (2 : F) = 0) :
    rootSL M 1 ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin (M + 1 + 1)) F) := by
  intro hz
  have hc := Subgroup.mem_center_iff.1 hz
    (trSL (F := F) (1 : Fin (M + 1 + 1)) 0 (Ne.symm (zero_ne_one_fin M)) 1)
  have h := congrArg (fun A : Matrix.SpecialLinearGroup (Fin (M + 1 + 1)) F =>
    (A : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) F) 0 0) hc
  have key : ((Matrix.transvection (1 : Fin (M + 1 + 1)) 0 (1 : F) *
      Matrix.transvection (0 : Fin (M + 1 + 1)) 1 (1 : F) : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) F)) 0 0 =
      ((Matrix.transvection (0 : Fin (M + 1 + 1)) 1 (1 : F) *
        Matrix.transvection (1 : Fin (M + 1 + 1)) 0 (1 : F) : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) F)) 0 0 :=
    h
  have hL : ((Matrix.transvection (1 : Fin (M + 1 + 1)) 0 (1 : F) *
      Matrix.transvection (0 : Fin (M + 1 + 1)) 1 (1 : F) : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) F)) 0 0 = 1 := by
    simp [Matrix.mul_apply, Matrix.one_apply, Matrix.transvection, Matrix.single_apply, zero_ne_one_fin M]
  have hR : ((Matrix.transvection (0 : Fin (M + 1 + 1)) 1 (1 : F) *
      Matrix.transvection (1 : Fin (M + 1 + 1)) 0 (1 : F) : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) F)) 0 0 = 0 := by
    simp [Matrix.mul_apply, Matrix.one_apply, Matrix.transvection, Matrix.single_apply, zero_ne_one_fin M, h2,
      Finset.sum_add_distrib, add_mul, mul_add, ite_mul, mul_ite, one_add_one_eq_two]
  rw [hL, hR] at key
  exact one_ne_zero key

end Torus


section Generic

theorem exists_lift_gen {G S K : Type} [Group G] [Group S] [Group K] [Finite G] [Finite K]
    (hsec : ∀ (E : Type) [Group E] [Finite E] (p : E →* G), Function.Surjective p →
      p.ker ≤ Subgroup.center E → ∃ s : G →* E, ∀ g, p (s g) = g)
    (ρ : K →* S) (hρ : Function.Surjective ρ) (hρk : ρ.ker ≤ Subgroup.center K) (π : G →* S) :
    ∃ σ : G →* K, ∀ g, ρ (σ g) = π g := by
  let W : Subgroup (G × K) :=
    { carrier := {x | π x.1 = ρ x.2}
      mul_mem' := fun {a b} ha hb => by
        show π (a * b).1 = ρ (a * b).2
        rw [Prod.fst_mul, Prod.snd_mul, map_mul, map_mul]
        exact congrArg₂ (· * ·) ha hb
      one_mem' := by
        show π (1 : G × K).1 = ρ (1 : G × K).2
        simp
      inv_mem' := fun {a} ha => by
        show π (a⁻¹).1 = ρ (a⁻¹).2
        rw [Prod.fst_inv, Prod.snd_inv, map_inv, map_inv]
        exact congrArg (·⁻¹) ha }
  let p1 : W →* G := (MonoidHom.fst _ _).comp W.subtype
  have hp1 : Function.Surjective p1 := by
    intro g
    obtain ⟨k, hk⟩ := hρ (π g)
    exact ⟨⟨(g, k), hk.symm⟩, rfl⟩
  have hcen : p1.ker ≤ Subgroup.center W := by
    intro x hx
    have h1 : (x : G × K).1 = 1 := by
      rw [MonoidHom.mem_ker] at hx
      exact hx
    have hz : (x : G × K).2 ∈ Subgroup.center K := by
      apply hρk
      rw [MonoidHom.mem_ker]
      have hx' : π (x : G × K).1 = ρ (x : G × K).2 := x.2
      rw [h1, map_one] at hx'
      exact hx'.symm
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · show (y : G × K).1 * (x : G × K).1 = (x : G × K).1 * (y : G × K).1
      rw [h1, mul_one, one_mul]
    · show (y : G × K).2 * (x : G × K).2 = (x : G × K).2 * (y : G × K).2
      exact Subgroup.mem_center_iff.1 hz _
  obtain ⟨s, hs⟩ := hsec W p1 hp1 hcen
  refine ⟨(MonoidHom.snd _ _).comp (W.subtype.comp s), fun g => ?_⟩
  have hmem : π (s g : G × K).1 = ρ (s g : G × K).2 := (s g).2
  have hfst : (s g : G × K).1 = g := hs g
  calc ρ (((MonoidHom.snd _ _).comp (W.subtype.comp s)) g)
      = ρ (s g : G × K).2 := rfl
    _ = π (s g : G × K).1 := hmem.symm
    _ = π g := by rw [hfst]

theorem core_generic {G S K : Type} [Group G] [Group S] [Group K] [Finite G] [Finite K]
    (hsec : ∀ (E : Type) [Group E] [Finite E] (p : E →* G), Function.Surjective p →
      p.ker ≤ Subgroup.center E → ∃ s : G →* E, ∀ g, p (s g) = g)
    (π : G →* S) (hπ : Function.Surjective π) (hπk : π.ker = Subgroup.center G)
    (ρ : K →* S) (hρ : Function.Surjective ρ) (hρk : ρ.ker = Subgroup.center K)
    {A : Type} [CommGroup A] [Finite A] (Ehom : A →* G) (hAel : ∀ x : A, x ^ 3 = 1)
    (r : ℕ) (hAcard : Nat.card A = 3 ^ r)
    (hAcen : ∀ x : A, Ehom x ∈ Subgroup.center G → x = 1)
    {B : Type} [Group B] (Phom : B →* G) (hB2 : ∀ b : B, b ^ 2 = 1) (b₀ : B)
    (hb₀ : Phom b₀ ∉ Subgroup.center G)
    (hconj : ∀ x : A, ∀ b : B, ∃ b' : B, Ehom x * Phom b * (Ehom x)⁻¹ = Phom b') :
    ∃ E P : Subgroup K, IsElemAbelian 3 E ∧ E ⊓ Subgroup.center K = ⊥ ∧ r ≤ CFSG.Open.pRank 3 E ∧
      P ≠ ⊥ ∧ IsPGroup 2 P ∧ E ≤ Subgroup.normalizer (P : Set K) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_lift_gen hsec ρ hρ hρk.le π
  have hmk : ∀ g : G, ρ (σ g) = 1 ↔ g ∈ Subgroup.center G := by
    intro g
    rw [hσ g, ← MonoidHom.mem_ker, hπk]
  have hρc : ∀ k : K, k ∈ Subgroup.center K → ρ k = 1 := fun k hk => by
    rw [← hρk] at hk
    exact MonoidHom.mem_ker.1 hk
  let Eh : A →* K := σ.comp Ehom
  let Ph : B →* K := σ.comp Phom
  have hEinj : Function.Injective Eh := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hc : Ehom x ∈ Subgroup.center G :=
      (hmk (Ehom x)).1 ((congrArg ρ hx).trans (map_one ρ))
    exact hAcen x hc
  have hEcard : Nat.card Eh.range = 3 ^ r := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hEinj).toEquiv, hAcard]
  have hEel : IsElemAbelian 3 Eh.range := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      show (a : K) * (b : K) = (b : K) * (a : K)
      rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨x, rfl⟩ := ha
      rw [← map_pow, hAel x, map_one]
  have hEdisj : Eh.range ⊓ Subgroup.center K = ⊥ := by
    rw [eq_bot_iff]
    rintro k ⟨⟨y, rfl⟩, hk⟩
    have hy : Ehom y ∈ Subgroup.center G := (hmk (Ehom y)).1 (hρc _ hk)
    rw [Subgroup.mem_bot, hAcen y hy, map_one]
  have hPne : Ph.range ≠ ⊥ := by
    intro h
    have hmem : Ph b₀ ∈ Ph.range := ⟨b₀, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    have hσ1 : σ (Phom b₀) = 1 := hmem
    exact hb₀ ((hmk (Phom b₀)).1 (by rw [hσ1, map_one]))
  have hPel : IsPGroup 2 Ph.range := by
    intro g
    obtain ⟨b, hb⟩ := g.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hb, ← map_pow, hB2 b, map_one]
  have hconjP : ∀ x : A, ∀ g ∈ Ph.range, Eh x * g * (Eh x)⁻¹ ∈ Ph.range := by
    rintro x _ ⟨b, rfl⟩
    obtain ⟨b', hb'⟩ := hconj x b
    refine ⟨b', ?_⟩
    show σ (Phom b') = σ (Ehom x) * σ (Phom b) * (σ (Ehom x))⁻¹
    rw [← hb', map_mul, map_mul, map_inv]
  have hEN : Eh.range ≤ Subgroup.normalizer (Ph.range : Set K) := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hconjP x h hh
    · intro hh
      have h3 := hconjP x⁻¹ _ hh
      simpa [mul_assoc] using h3
  refine ⟨Eh.range, Ph.range, hEel, hEdisj, ?_, hPne, hPel, hEN⟩
  exact le_of_eq (i271_pRank_eq Nat.prime_three hEel hEcard).symm

end Generic

section Core

variable {F : Type} [Field F]

@[expose] def rootHom (M : ℕ) : Multiplicative F →* Matrix.SpecialLinearGroup (Fin (M + 1 + 1)) F :=
  MonoidHom.mk' (fun a => rootSL M (Multiplicative.toAdd a)) (fun a b => by
    rw [toAdd_mul, rootSL_mul])

theorem rootHom_pow_two (M : ℕ) (h2 : (2 : F) = 0) (a : Multiplicative F) :
    rootHom (F := F) M (a ^ 2) = 1 := by
  change rootSL M (Multiplicative.toAdd (a ^ 2)) = 1
  rw [toAdd_pow, nsmul_eq_mul, Nat.cast_ofNat, h2, zero_mul, rootSL_zero]

theorem core_typeA {K : Type} [Group K] [Finite K] {M : ℕ} (hM : 3 ≤ M)
    (hF : Nat.card F = 4) [Finite F] (h2 : (2 : F) = 0)
    (ρ : K →* Matrix.SpecialLinearGroup (Fin (M + 1 + 1)) F ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (M + 1 + 1)) F))
    (hρ : Function.Surjective ρ) (hρk : ρ.ker = Subgroup.center K) :
    ∃ E P : Subgroup K, IsElemAbelian 3 E ∧ E ⊓ Subgroup.center K = ⊥ ∧ M ≤ CFSG.Open.pRank 3 E ∧
      P ≠ ⊥ ∧ IsPGroup 2 P ∧ E ≤ Subgroup.normalizer (P : Set K) := by
  classical
  have hsep : Separating (M + 1) F :=
    separating_of_card (by omega) (by omega) (fun h => by omega) (fun h => by omega)
  obtain ⟨σ, hσ⟩ := exists_lift_sl (by omega) hsep ρ hρ hρk.le
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin (M + 1 + 1)) F)))
  have hmk : ∀ g : Matrix.SpecialLinearGroup (Fin (M + 1 + 1)) F,
      ρ (σ g) = 1 ↔ g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (M + 1 + 1)) F) := by
    intro g
    rw [hσ g, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have key : ∀ g : Matrix.SpecialLinearGroup (Fin (M + 1 + 1)) F, σ g = 1 →
      g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (M + 1 + 1)) F) := fun g hg =>
    (hmk g).1 (by rw [hg, map_one])
  have hρc : ∀ k : K, k ∈ Subgroup.center K → ρ k = 1 := fun k hk => by
    rw [← hρk] at hk
    exact MonoidHom.mem_ker.1 hk
  let Ehom : (Fin M → rootsOfUnity 3 F) →* K := σ.comp (torusHom (F := F) M)
  let Phom : Multiplicative F →* K := σ.comp (rootHom (F := F) M)
  have hEinj : Function.Injective Ehom := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact torusElt_eq_one_of_central x (key (torusElt x) hx)
  have hEcard : Nat.card Ehom.range = 3 ^ M := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hEinj).toEquiv, Nat.card_fun, card_mu3 hF]
    simp
  have hpow3 : ∀ x : Fin M → rootsOfUnity 3 F, x ^ 3 = 1 := by
    intro x
    funext j
    apply Subtype.ext
    have hj := (mem_rootsOfUnity 3 ((x j : rootsOfUnity 3 F) : Fˣ)).1 (x j).2
    simpa using hj
  have hEel : IsElemAbelian 3 Ehom.range := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      show (a : K) * (b : K) = (b : K) * (a : K)
      rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨x, rfl⟩ := ha
      rw [← map_pow, hpow3 x, map_one]
  have hEdisj : Ehom.range ⊓ Subgroup.center K = ⊥ := by
    rw [eq_bot_iff]
    rintro k ⟨⟨y, rfl⟩, hk⟩
    have hy : y = 1 := torusElt_eq_one_of_central y ((hmk (torusElt y)).1 (hρc _ hk))
    rw [Subgroup.mem_bot, hy, map_one]
  have hPne : Phom.range ≠ ⊥ := by
    intro h
    have hmem : Phom (Multiplicative.ofAdd (1 : F)) ∈ Phom.range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact rootSL_not_central M h2 (key (rootSL M 1) hmem)
  have hPel : IsPGroup 2 Phom.range := by
    intro g
    obtain ⟨a, ha⟩ := g.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← ha, ← map_pow]
    change σ (rootHom (F := F) M (a ^ 2)) = 1
    rw [rootHom_pow_two M h2, map_one]
  have hconj : ∀ x : Fin M → rootsOfUnity 3 F, ∀ g ∈ Phom.range,
      Ehom x * g * (Ehom x)⁻¹ ∈ Phom.range := by
    rintro x _ ⟨a, rfl⟩
    refine ⟨Multiplicative.ofAdd (((tDiag x 0 : Fˣ) : F) * Multiplicative.toAdd a *
      ((tDiag x 1 : Fˣ) : F)⁻¹), ?_⟩
    have h1 : torusElt x * rootSL M (Multiplicative.toAdd a) * (torusElt x)⁻¹ =
        rootSL M (((tDiag x 0 : Fˣ) : F) * Multiplicative.toAdd a * ((tDiag x 1 : Fˣ) : F)⁻¹) := by
      rw [torusElt_mul_rootSL]
      group
    change σ (rootSL M _) = σ (torusElt x) * σ (rootSL M (Multiplicative.toAdd a)) * (σ (torusElt x))⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, h1]
    rfl
  have hEN : Ehom.range ≤ Subgroup.normalizer (Phom.range : Set K) := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hconj x h hh
    · intro hh
      have h3 := hconj x⁻¹ _ hh
      simpa [mul_assoc] using h3
  refine ⟨Ehom.range, Phom.range, hEel, hEdisj, ?_, hPne, hPel, hEN⟩
  exact le_of_eq (i271_pRank_eq Nat.prime_three hEel hEcard).symm

end Core

theorem typeA_witness (K : Type) [Group K] [Finite K] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q).Valid) (hq : IsTwoPow q 2) (n : ℕ) (hn : 2 ≤ n)
    (hrn : r + 1 = 3 ^ n)
    (e : K ⧸ Subgroup.center K ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.A r q, hv⟩) :
    ∃ E P : Subgroup K, IsElemAbelian 3 E ∧ E ⊓ Subgroup.center K = ⊥ ∧
      r - 1 ≤ CFSG.Open.pRank 3 E ∧ P ≠ ⊥ ∧ IsPGroup 2 P ∧ E ≤ Subgroup.normalizer (P : Set K) := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨hq1, hq2⟩ := hq
  have h9 : 9 ≤ 3 ^ n := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨M, rfl⟩ : ∃ M, r = M + 1 := ⟨r - 1, by omega⟩
  have hM : 3 ≤ M := by omega
  let Φ := e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL (M + 1) q hv)
  let ρ : K →* Matrix.SpecialLinearGroup (Fin (M + 1 + 1)) (GaloisField q.p q.exponent) ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (M + 1 + 1)) (GaloisField q.p q.exponent)) :=
    Φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hρ : Function.Surjective ρ := Φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρk : ρ.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker]
    change Φ (QuotientGroup.mk x) = 1 ↔ x ∈ Subgroup.center K
    rw [map_eq_one_iff Φ Φ.injective, QuotientGroup.eq_one_iff]
  have hexp : q.exponent ≠ 0 := by rw [hq2]; norm_num
  have hF : Nat.card (GaloisField q.p q.exponent) = 4 := by
    rw [GaloisField.card q.p q.exponent hexp, hq1, hq2]
    norm_num
  have h2 : (2 : GaloisField q.p q.exponent) = 0 := by
    have h : ((2 : ℕ) : GaloisField q.p q.exponent) = 0 := by
      rw [← hq1]
      exact CharP.cast_eq_zero _ _
    exact_mod_cast h
  obtain ⟨E, P, hE, hdisj, hrk, hP, hP2, hEN⟩ :=
    core_typeA (K := K) (F := GaloisField q.p q.exponent) hM hF h2 ρ hρ hρk
  exact ⟨E, P, hE, hdisj, by simpa using hrk, hP, hP2, hEN⟩

end Gen2318LocalAux


section F4

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley


theorem charP_two_of_card_four (K' : Type) [Field K'] [Finite K'] (h : Nat.card K' = 4) :
    CharP K' 2 := by
  classical
  haveI : Fintype K' := Fintype.ofFinite K'
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' K'
  rw [Fintype.card_eq_nat_card, h] at hcard
  have hdvd : p ∣ 4 := by
    rw [hcard]
    exact dvd_pow_self p (PNat.ne_zero n)
  have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hp2 : p = 2 := by
    interval_cases p <;> first | rfl | exact absurd hdvd (by decide) | exact absurd hp (by decide)
  rw [hp2] at hchar
  exact hchar

theorem xUnit_inj_gen (τ : Tag) {K' : Type} [Field K'] (i : Fin τ.rank) {c c' : K'}
    (h : xUnit τ K' i c = xUnit τ K' i c') : c = c' :=
  xOp_injective i (congrArg Units.val h)


theorem pow3_pi {ι : Type} {K' : Type} [Field K'] (x : ι → rootsOfUnity 3 K') : x ^ 3 = 1 := by
  funext j
  apply Subtype.ext
  have hj := (mem_rootsOfUnity 3 ((x j : rootsOfUnity 3 K') : K'ˣ)).1 (x j).2
  simpa using hj

theorem adjoint_torus_witness (τ : Tag) {K' : Type} [Field K'] [Finite K'] [CharP K' 2]
    (hK' : Nat.card K' = 2 ^ 2) (hpos : 0 < τ.rank)
    (hsec : ∀ (E : Type) [Group E] [Finite E] (p : E →* ↥(adjointGroup τ K')), Function.Surjective p →
      p.ker ≤ Subgroup.center E → ∃ s : ↥(adjointGroup τ K') →* E, ∀ g, p (s g) = g)
    (hmem : ∀ a : Fin τ.rank → K'ˣ, rootDiagUnit τ a ∈ adjointGroup τ K')
    {K : Type} [Group K] [Finite K]
    (ρ : K →* CFSG.Blueprint.AdjointQuotient τ K') (hρ : Function.Surjective ρ)
    (hρk : ρ.ker = Subgroup.center K) :
    ∃ E P : Subgroup K, IsElemAbelian 3 E ∧ E ⊓ Subgroup.center K = ⊥ ∧
      τ.rank ≤ CFSG.Open.pRank 3 E ∧ P ≠ ⊥ ∧ IsPGroup 2 P ∧
      E ≤ Subgroup.normalizer (P : Set K) := by
  classical
  have h2K : (2 : K') = 0 := by
    have h := CharP.cast_eq_zero K' 2
    exact_mod_cast h
  haveI : Finite (ModGL τ K') := CFSG.LieType.Chevalley.finite_modGL
  let G := ↥(adjointGroup τ K')
  let π : G →* CFSG.Blueprint.AdjointQuotient τ K' := QuotientGroup.mk' (Subgroup.center G)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective (Subgroup.center G)
  have hπk : π.ker = Subgroup.center G := QuotientGroup.ker_mk' (Subgroup.center G)
  have hmulD : ∀ a b : Fin τ.rank → K'ˣ,
      rootDiagUnit τ (a * b) = rootDiagUnit τ a * rootDiagUnit τ b :=
    fun a b => map_mul (CFSG.LieType.Chevalley.rootDiagUnitHom τ K') a b
  let liftA : (Fin τ.rank → rootsOfUnity 3 K') → (Fin τ.rank → K'ˣ) :=
    fun x j => ((x j : rootsOfUnity 3 K') : K'ˣ)
  let Ehom : (Fin τ.rank → rootsOfUnity 3 K') →* G :=
    MonoidHom.mk' (fun x => ⟨rootDiagUnit τ (liftA x), hmem _⟩) (fun x y => Subtype.ext (by
      show rootDiagUnit τ (liftA (x * y)) = rootDiagUnit τ (liftA x) * rootDiagUnit τ (liftA y)
      rw [← hmulD]
      congr 1))
  have hAel : ∀ x : (Fin τ.rank → rootsOfUnity 3 K'), x ^ 3 = 1 := fun x => pow3_pi x
  have hAcard : Nat.card (Fin τ.rank → rootsOfUnity 3 K') = 3 ^ τ.rank := by
    rw [Nat.card_fun, Gen2318LocalAux.card_mu3 (F := K') (by rw [hK']; norm_num)]
    simp
  let i₀ : Fin τ.rank := ⟨0, hpos⟩
  have hconjc : ∀ (i : Fin τ.rank) (a : Fin τ.rank → K'ˣ) (c : K'),
      rootDiagUnit τ a * xUnit τ K' i c * (rootDiagUnit τ a)⁻¹ =
        xUnit τ K' i ((a i : K') * c) :=
    fun i a c => (root_diagonal_conjugation τ K' a).1 i c
  have hAcen : ∀ x : (Fin τ.rank → rootsOfUnity 3 K'), Ehom x ∈ Subgroup.center G → x = 1 := by
    intro x hx
    have key : ∀ i : Fin τ.rank, liftA x i = 1 := by
      intro i
      have hc := Subgroup.mem_center_iff.1 hx ⟨xUnit τ K' i 1, xUnit_mem_adjointGroup i 1⟩
      have h2 : Ehom x * ⟨xUnit τ K' i 1, xUnit_mem_adjointGroup i 1⟩ * (Ehom x)⁻¹ =
          ⟨xUnit τ K' i 1, xUnit_mem_adjointGroup i 1⟩ := by
        rw [← hc, mul_inv_cancel_right]
      have h3 := congrArg Subtype.val h2
      have h4 : rootDiagUnit τ (liftA x) * xUnit τ K' i 1 * (rootDiagUnit τ (liftA x))⁻¹ =
          xUnit τ K' i 1 := h3
      rw [hconjc i (liftA x) 1] at h4
      have h5 := xUnit_inj_gen τ i h4
      exact Units.ext (by simpa using h5)
    funext j
    apply Subtype.ext
    exact (key j).trans (by simp)
  let Phom : Multiplicative K' →* G :=
    MonoidHom.mk' (fun b => ⟨xUnit τ K' i₀ (Multiplicative.toAdd b), xUnit_mem_adjointGroup i₀ _⟩)
      (fun b c => Subtype.ext (by
        show xUnit τ K' i₀ (Multiplicative.toAdd (b * c)) =
          xUnit τ K' i₀ (Multiplicative.toAdd b) * xUnit τ K' i₀ (Multiplicative.toAdd c)
        rw [toAdd_mul, xUnit_add]))
  have hB2 : ∀ b : Multiplicative K', b ^ 2 = 1 := by
    intro b
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, Nat.cast_ofNat, h2K, zero_mul]
  have hnt : Nontrivial (rootsOfUnity 3 K') := by
    have hc3 : Nat.card (rootsOfUnity 3 K') = 3 :=
      Gen2318LocalAux.card_mu3 (F := K') (by rw [hK']; norm_num)
    have : 1 < Nat.card (rootsOfUnity 3 K') := by omega
    exact (Finite.one_lt_card_iff_nontrivial).1 this
  have hb₀ : Phom (Multiplicative.ofAdd (1 : K')) ∉ Subgroup.center G := by
    intro hz
    obtain ⟨ζ, hζ⟩ := exists_ne (1 : rootsOfUnity 3 K')
    let a : Fin τ.rank → rootsOfUnity 3 K' := fun j => if j = i₀ then ζ else 1
    have hc := Subgroup.mem_center_iff.1 hz (Ehom a)
    have h1 : Ehom a * Phom (Multiplicative.ofAdd (1 : K')) * (Ehom a)⁻¹ =
        Phom (Multiplicative.ofAdd (1 : K')) := by
      rw [hc, mul_inv_cancel_right]
    have h2 := congrArg Subtype.val h1
    have h3 : rootDiagUnit τ (liftA a) * xUnit τ K' i₀ 1 * (rootDiagUnit τ (liftA a))⁻¹ =
        xUnit τ K' i₀ 1 := h2
    rw [hconjc i₀ (liftA a) 1] at h3
    have h4 := xUnit_inj_gen τ i₀ h3
    have h5 : liftA a i₀ = 1 := Units.ext (by simpa using h4)
    have ha : liftA a i₀ = ((ζ : rootsOfUnity 3 K') : K'ˣ) := by simp [liftA, a, i₀]
    have hζ1 : ((ζ : rootsOfUnity 3 K') : K'ˣ) = 1 := ha ▸ h5
    exact hζ (Subtype.ext hζ1)
  have hconj : ∀ (x : Fin τ.rank → rootsOfUnity 3 K') (b : Multiplicative K'),
      ∃ b' : Multiplicative K', Ehom x * Phom b * (Ehom x)⁻¹ = Phom b' := by
    intro x b
    refine ⟨Multiplicative.ofAdd (((liftA x i₀ : K'ˣ) : K') * Multiplicative.toAdd b), ?_⟩
    apply Subtype.ext
    exact hconjc i₀ (liftA x) (Multiplicative.toAdd b)
  obtain ⟨E, P, h1, h2, h3, h4, h5, h6⟩ :=
    Gen2318LocalAux.core_generic hsec π hπ hπk ρ hρ hρk Ehom hAel τ.rank hAcard hAcen Phom hB2
      (Multiplicative.ofAdd 1) hb₀ hconj
  exact ⟨E, P, h1, h2, h3, h4, h5, h6⟩

theorem f4_four_witness {K : Type} [Group K] [Finite K] {K' : Type} [Field K'] [Finite K']
    (hK' : Nat.card K' = 2 ^ 2) (ρ : K →* CFSG.Blueprint.AdjointQuotient Tag.F4 K')
    (hρ : Function.Surjective ρ) (hρk : ρ.ker = Subgroup.center K) :
    ∃ E P : Subgroup K, IsElemAbelian 3 E ∧ E ⊓ Subgroup.center K = ⊥ ∧
      Tag.F4.rank ≤ CFSG.Open.pRank 3 E ∧ P ≠ ⊥ ∧ IsPGroup 2 P ∧
      E ≤ Subgroup.normalizer (P : Set K) := by
  haveI : CharP K' 2 := charP_two_of_card_four K' (by rw [hK']; norm_num)
  exact adjoint_torus_witness Tag.F4 hK' (by decide)
    (fun E _ _ p hp hc => CFSG.LieType.Steinberg.CentralExt.FieldFour.f4_four_exists_section hK' E p hp hc)
    (fun a => CFSG.RankThree.Chevalley.torusGroup_le_adjointGroup_F4
      (CFSG.RankThree.Chevalley.F4_rootDiagUnit_mem_torusGroup a)) ρ hρ hρk

theorem typeF4_witness (K : Type) [Group K] [Finite K]
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 q).Valid) (hq : IsTwoPow q 2)
    (e : K ⧸ Subgroup.center K ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.F4 q, hv⟩) :
    ∃ E P : Subgroup K, IsElemAbelian 3 E ∧ E ⊓ Subgroup.center K = ⊥ ∧
      rho2318 (TauCeti.LieTypeIndex.F4 q) ≤ CFSG.Open.pRank 3 E ∧ P ≠ ⊥ ∧ IsPGroup 2 P ∧
      E ≤ Subgroup.normalizer (P : Set K) := by
  obtain ⟨hq1, hq2⟩ := hq
  have hK4 : Nat.card (GaloisField 2 2) = TauCeti.PrimePower.card q := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card 2 2 (by norm_num), hq1, hq2]
  obtain ⟨ψ0⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 q hv hq1 (GaloisField 2 2) hK4
  let ψ := e.trans ψ0.symm
  have hK' : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  let ρ : K →* CFSG.Blueprint.AdjointQuotient Tag.F4 (GaloisField 2 2) :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hρ : Function.Surjective ρ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρk : ρ.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker]
    change ψ (QuotientGroup.mk x) = 1 ↔ x ∈ Subgroup.center K
    rw [map_eq_one_iff ψ ψ.injective, QuotientGroup.eq_one_iff]
  have hrk : rho2318 (TauCeti.LieTypeIndex.F4 q) = Tag.F4.rank := rfl
  obtain ⟨E, P, h1, h2, h3, h4, h5, h6⟩ := f4_four_witness hK' ρ hρ hρk
  exact ⟨E, P, h1, h2, hrk ▸ h3, h4, h5, h6⟩

theorem e8_four_witness {K : Type} [Group K] [Finite K] {K' : Type} [Field K'] [Finite K']
    (hK' : Nat.card K' = 2 ^ 2) (ρ : K →* CFSG.Blueprint.AdjointQuotient Tag.E8 K')
    (hρ : Function.Surjective ρ) (hρk : ρ.ker = Subgroup.center K) :
    ∃ E P : Subgroup K, IsElemAbelian 3 E ∧ E ⊓ Subgroup.center K = ⊥ ∧
      Tag.E8.rank ≤ CFSG.Open.pRank 3 E ∧ P ≠ ⊥ ∧ IsPGroup 2 P ∧
      E ≤ Subgroup.normalizer (P : Set K) := by
  haveI : CharP K' 2 := charP_two_of_card_four K' (by rw [hK']; norm_num)
  exact adjoint_torus_witness Tag.E8 hK' (by decide)
    (fun E _ _ p hp hc => CFSG.LieType.Steinberg.CentralExt.FieldFour.e8_four_exists_section hK' E p hp hc)
    (fun a => CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_mem_torusGroup_E8 a)) ρ hρ hρk

theorem typeE8_witness (K : Type) [Group K] [Finite K]
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid) (hq : IsTwoPow q 2)
    (e : K ⧸ Subgroup.center K ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.E8 q, hv⟩) :
    ∃ E P : Subgroup K, IsElemAbelian 3 E ∧ E ⊓ Subgroup.center K = ⊥ ∧
      rho2318 (TauCeti.LieTypeIndex.E8 q) ≤ CFSG.Open.pRank 3 E ∧ P ≠ ⊥ ∧ IsPGroup 2 P ∧
      E ≤ Subgroup.normalizer (P : Set K) := by
  obtain ⟨hq1, hq2⟩ := hq
  have hK4 : Nat.card (GaloisField 2 2) = TauCeti.PrimePower.card q := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card 2 2 (by norm_num), hq1, hq2]
  obtain ⟨ψ0⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_E8 q hv hq1 (GaloisField 2 2) hK4
  let ψ := e.trans ψ0.symm
  have hK' : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  let ρ : K →* CFSG.Blueprint.AdjointQuotient Tag.E8 (GaloisField 2 2) :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hρ : Function.Surjective ρ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρk : ρ.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker]
    change ψ (QuotientGroup.mk x) = 1 ↔ x ∈ Subgroup.center K
    rw [map_eq_one_iff ψ ψ.injective, QuotientGroup.eq_one_iff]
  have hrk : rho2318 (TauCeti.LieTypeIndex.E8 q) = 6 := rfl
  obtain ⟨E, P, h1, h2, h3, h4, h5, h6⟩ := e8_four_witness hK' ρ hρ hρk
  refine ⟨E, P, h1, h2, ?_, h4, h5, h6⟩
  rw [hrk]
  exact le_trans (by decide) h3

@[expose] def Gen2318Open : TauCeti.LieTypeIndex → Prop
  | .twistedA _ _ => True
  | .E6 _ => True
  | .E7 _ => True
  | .E8 q => ¬ IsTwoPow q 2
  | _ => False

@[expose] def Gen2318Residual : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → ∀ d : TauCeti.ValidLieTypeIndex,
    Gen2318Index d.1 → Gen2318Open d.1 →
      Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∃ E P : Subgroup K, IsElemAbelian 3 E ∧ E ⊓ Subgroup.center K = ⊥ ∧
          rho2318 d.1 ≤ CFSG.Open.pRank 3 E ∧ P ≠ ⊥ ∧ IsPGroup 2 ↥P ∧
          E ≤ Subgroup.normalizer (P : Set K)

theorem gen2318TwoLocal_of_residual (hR : Gen2318Residual) :
    Gen2318TwoLocal := by
  intro K _ _ hq d hd hiso
  by_cases hopen : Gen2318Open d.1
  · exact hR K hq d hd hopen hiso
  obtain ⟨idx, hv⟩ := d
  obtain ⟨e⟩ := hiso
  cases idx with
  | A r q =>
    obtain ⟨hq, n, hn2, hrn⟩ := hd
    exact Gen2318LocalAux.typeA_witness K r q hv hq n hn2 hrn e
  | F4 q => exact typeF4_witness K q hv hd e
  | E8 q =>
    have hq4 : IsTwoPow q 2 := by
      unfold Gen2318Open at hopen
      exact not_not.1 hopen
    exact typeE8_witness K q hv hq4 e
  | twistedA r q => exact absurd trivial hopen
  | E6 q => exact absurd trivial hopen
  | E7 q => exact absurd trivial hopen
  | B r q => exact hd.elim
  | C r q => exact hd.elim
  | D r q => exact hd.elim
  | twistedD r q => exact hd.elim
  | G2 q => exact hd.elim
  | twistedE6 q => exact hd.elim
  | trialityD4 q => exact hd.elim
  | suzuki m => exact hd.elim
  | reeG2 m => exact hd.elim
  | reeF4 m => exact hd.elim
  | tits => exact hd.elim

end F4

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318Local


end
