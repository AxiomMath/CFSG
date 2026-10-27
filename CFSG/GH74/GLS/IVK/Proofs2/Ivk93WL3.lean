module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WLeaves
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WPGL
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TypeOne

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.Sp4Rec CFSG.ComponentClassification.CatalogueBProjectiveInvolution
  CFSG.ComponentClassification.CatalogueBGeneralLinear
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

theorem ivk93w_gl2_scalar_of_commute_sl2 {F : Type} [Field F] {g : GL (Fin 2) F}
    (hg : ∀ t : SL(2, F), g * Matrix.SpecialLinearGroup.toGL t =
      Matrix.SpecialLinearGroup.toGL t * g) :
    ∃ c : Fˣ, g = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  have hd1 : (!![(1 : F), 1; 0, 1]).det = 1 := by simp [Matrix.det_fin_two]
  have hd2 : (!![(1 : F), 0; 1, 1]).det = 1 := by simp [Matrix.det_fin_two]
  have h1 := congrArg Units.val (hg ⟨!![(1 : F), 1; 0, 1], hd1⟩)
  have h2 := congrArg Units.val (hg ⟨!![(1 : F), 0; 1, 1], hd2⟩)
  simp only [Matrix.SpecialLinearGroup.toGL, Units.val_mul, MonoidHom.coe_mk, OneHom.coe_mk] at h1 h2
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d : F, (g : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [hM] at h1 h2
  have e1 := congrFun (congrFun h1 0) 0
  have e2 := congrFun (congrFun h1 0) 1
  have e3 := congrFun (congrFun h2 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
  have hc : c = 0 := e1
  have hb : b = 0 := e3
  have hda : d = a := by linear_combination -e2
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det g).ne_zero
  rw [hM, Matrix.det_fin_two_of, hb, hc, hda] at hdet
  have ha : a ≠ 0 := by
    intro h0
    apply hdet
    rw [h0]
    ring
  refine ⟨Units.mk0 a ha, Units.ext ?_⟩
  rw [hM, Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, hb, hc, hda]

theorem ivk93w_comm_of_odd {F : Type} [Field F] {n : ℕ} [Nonempty (Fin n)] (hn : Odd n)
    (A : GL (Fin n) F) (hinv : Matrix.ProjGenLinGroup.mk A ^ 2 = 1) (g : GL (Fin n) F)
    (hg : Matrix.ProjGenLinGroup.mk g ∈
      centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin n) F))) :
    g * A = A * g := by
  let B : projectiveCentralizerLift A := ⟨g, hg⟩
  have h1 := scalarDisplacement_square_eq_one A hinv B
  have h2 := scalarDisplacement_spec A B
  have h3 : scalarDisplacement A B ^ n = 1 := by
    have h4 := congrArg Matrix.GeneralLinearGroup.det h2
    simp only [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h4
    have h5 : Matrix.GeneralLinearGroup.det A * Matrix.GeneralLinearGroup.det g *
        scalarDisplacement A B ^ n = Matrix.GeneralLinearGroup.det A * Matrix.GeneralLinearGroup.det g * 1 := by
      rw [mul_one]
      exact h4.trans (mul_comm _ _)
    exact mul_left_cancel h5
  have h6 : scalarDisplacement A B = 1 := by
    obtain ⟨k, hk⟩ := hn
    have hpow : ∀ m : ℕ, m = 2 * k + 1 → scalarDisplacement A B ^ m = scalarDisplacement A B := by
      intro m hm
      rw [hm, pow_succ, pow_mul, h1, one_pow, one_mul]
    rw [← hpow n hk]
    exact h3
  exact (scalarDisplacement_eq_one_iff A B).1 h6

theorem ivk93w_gl1_comm {F : Type} [Field F] (a b : GL (Fin 1) F) : a * b = b * a := by
  apply Units.ext
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem ivk93w_l3_key {F : Type} [Field F] [Finite F] {x : StatedProj (StatedSL 3 F)}
    {B : Subgroup (StatedProj (StatedSL 3 F))} (A : GL (Fin 3) F)
    (hA : CatFactsL4U4.projToPGL 3 F x = Matrix.ProjGenLinGroup.mk A)
    (hinv : Matrix.ProjGenLinGroup.mk A ^ 2 = 1)
    (e : ↥(centralizer ({A} : Set (GL (Fin 3) F))) ≃* GL (Fin 2) F × GL (Fin 1) F)
    (hscal : ∀ c : Fˣ, e (ordinaryCentralizerScalar A c) =
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c, Matrix.GeneralLinearGroup.scalar (Fin 1) c))
    {L : Subgroup ↥(centralizer ({A} : Set (GL (Fin 3) F)))}
    (he : L.map e.toMonoidHom = (specialLinearRange 2 F).prod ⊥)
    (hLM : L.map (ordinaryCentralizerProjection A) =
      (B.map (CatFactsL4U4.projToPGL 3 F)).subgroupOf
        (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin 3) F))))
    {a : StatedProj (StatedSL 3 F)} (hax : a * x = x * a) (hcent : ∀ y ∈ B, a * y = y * a) :
    ∃ g : ↥(centralizer ({A} : Set (GL (Fin 3) F))),
      Matrix.ProjGenLinGroup.mk (g : GL (Fin 3) F) = CatFactsL4U4.projToPGL 3 F a ∧
      ∃ (c : Fˣ) (d : GL (Fin 1) F), e g = (Matrix.GeneralLinearGroup.scalar (Fin 2) c, d) := by
  classical
  have : Nonempty (Fin 3) := ⟨0⟩
  set φ := CatFactsL4U4.projToPGL 3 F with hφdef
  obtain ⟨g₀, hg₀⟩ := Matrix.ProjGenLinGroup.mk_surjective (φ a)
  have hg₀A : Matrix.ProjGenLinGroup.mk g₀ ∈
      centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin 3) F)) := by
    rw [mem_centralizer_singleton_iff, hg₀, ← hA, ← map_mul, ← map_mul, hax]
  have hcomm := ivk93w_comm_of_odd (by decide : Odd 3) A hinv g₀ hg₀A
  let g : ↥(centralizer ({A} : Set (GL (Fin 3) F))) :=
    ⟨g₀, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩
  refine ⟨g, hg₀, ?_⟩
  rcases hp : e g with ⟨g₁, g₂⟩
  have hsl : ∀ t : SL(2, F), g₁ * Matrix.SpecialLinearGroup.toGL t =
      Matrix.SpecialLinearGroup.toGL t * g₁ := by
    intro t
    have hmem : ((Matrix.SpecialLinearGroup.toGL t : GL (Fin 2) F), (1 : GL (Fin 1) F)) ∈
        L.map e.toMonoidHom := by
      rw [he]
      exact ⟨⟨t, rfl⟩, Subgroup.mem_bot.2 rfl⟩
    obtain ⟨ℓ, hℓL, hℓe⟩ := hmem
    have hℓM : ordinaryCentralizerProjection A ℓ ∈ (B.map φ).subgroupOf
        (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set (Matrix.ProjGenLinGroup (Fin 3) F))) := by
      rw [← hLM]
      exact ⟨ℓ, hℓL, rfl⟩
    obtain ⟨y, hyB, hy⟩ : ∃ y ∈ B, φ y = Matrix.ProjGenLinGroup.mk (ℓ : GL (Fin 3) F) :=
      Subgroup.mem_subgroupOf.1 hℓM
    have h1 := hcent y hyB
    have h2 : Matrix.ProjGenLinGroup.mk (g₀ * (ℓ : GL (Fin 3) F)) =
        Matrix.ProjGenLinGroup.mk ((ℓ : GL (Fin 3) F) * g₀) := by
      have h1' := congrArg φ h1
      rw [map_mul, map_mul, ← hg₀, hy] at h1'
      rw [map_mul, map_mul]
      exact h1'
    obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.1 h2
    have h3 : g * ℓ * ordinaryCentralizerScalar A u = ℓ * g := Subtype.ext hu
    have h4 := congrArg e h3
    have hℓe' : e ℓ = (Matrix.SpecialLinearGroup.toGL t, 1) := hℓe
    simp only [map_mul] at h4
    rw [hℓe', hp, hscal u] at h4
    have h5 := congrArg Prod.snd h4
    have h6 := congrArg Prod.fst h4
    simp only [Prod.snd_mul, Prod.fst_mul, mul_one] at h5 h6
    have hu1 : u = 1 := ivk95l_scalar_eq_one (by norm_num : 1 ≤ 1)
      (by simpa using h5)
    rw [hu1, map_one, mul_one] at h6
    exact h6
  obtain ⟨c, hc⟩ := ivk93w_gl2_scalar_of_commute_sl2 hsl
  exact ⟨c, g₂, by rw [hc]⟩

theorem ivk93w_odd_commutator_outer_three {F : Type} [Field F] [Finite F] :
    Odd (Nat.card (commutator (Outer (projectiveSL 3 F)))) := by
  obtain ⟨N, -, hN, hcomm⟩ := OuterDerived.exists_linear_outer_diagonal (K := F) (n := 3) le_rfl
  have hle : commutator (Outer (projectiveSL 3 F)) ≤ N := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact hcomm x y
  have h1 : Nat.card (commutator (Outer (projectiveSL 3 F))) ∣ Nat.card N :=
    Subgroup.card_dvd_of_le hle
  exact Odd.of_dvd_nat (Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_left 3 _))
    (h1.trans hN)

theorem ivk93w_odd_commutator_outer_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : Odd (Nat.card (commutator (Outer B)))) : Odd (Nat.card (commutator (Outer A))) := by
  refine h.of_dvd_nat ?_
  have hinj : Function.Injective (OuterAutomorphisms.equivalence e).toMonoidHom :=
    (OuterAutomorphisms.equivalence e).injective
  have h1 : (commutator (Outer A)).map (OuterAutomorphisms.equivalence e).toMonoidHom ≤
      commutator (Outer B) := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  rw [← Subgroup.card_map_of_injective hinj (K := commutator (Outer A))]
  exact Subgroup.card_dvd_of_le h1

theorem ivk93w_odd_commutator_outer_psl3 {p f : ℕ} {J : Type} [Group J]
    (hJ : LieModel J .PSL 3 p f) : Odd (Nat.card (commutator (Outer J))) := by
  obtain ⟨F, _, _, -, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hJ
  exact ivk93w_odd_commutator_outer_of_equiv e ivk93w_odd_commutator_outer_three

theorem ivk93w_l3_false {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    {x : StatedProj (StatedSL 3 F)} {q : ℕ} {B : Subgroup (StatedProj (StatedSL 3 F))}
    (h : Ivk93W x q B) (hQ : Ivk93WQuat x B) : False := by
  classical
  obtain ⟨A, r, s, e, L, hA, hne, hinv, hr, hs, hrs, hscal, hL, h2r, he, hLM, hBle, ⟨ψ⟩⟩ :=
    h.blockData h2 (Or.inl rfl)
  have hr2 : r = 2 := by omega
  have hs1 : s = 1 := by omega
  subst hr2
  subst hs1
  have h5 := h.five_le_of_equiv_sl2 ψ
  have hO : pPrimeCore 2 ↥B = ⊥ := by
    rw [← CFSG.pPrimeCore_map_iso 2 ψ, CatFactsSp4.pPrimeCore_SL2 h2 (by omega), Subgroup.map_bot]
  obtain ⟨Q, hQC, hxQ, hQ8, ⟨a, ha, b, hb, haa, hbb, hab⟩, hcomm⟩ := hQ
  have hcent : ∀ a ∈ Q, ∀ y ∈ B, a * y = y * a := by
    intro a ha y hy
    have h1 := hcomm a ha y hy
    have hOB : pPrimeCoreOf 2 B = ⊥ := by
      unfold pPrimeCoreOf
      rw [hO, Subgroup.map_bot]
    rw [hOB, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hax : ∀ a ∈ Q, a * x = x * a := fun a ha =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hQC ha))
  obtain ⟨ga, hga, ca, da, hea⟩ := ivk93w_l3_key A hA hinv e hscal he hLM (hax a ha)
    (hcent a ha)
  obtain ⟨gb, hgb, cb, db, heb⟩ := ivk93w_l3_key A hA hinv e hscal he hLM (hax b hb)
    (hcent b hb)
  have hgg : ga * gb = gb * ga := by
    apply e.injective
    rw [map_mul, map_mul, hea, heb]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul, ← map_mul, mul_comm]
    · exact ivk93w_gl1_comm da db
  apply hab
  apply CatFactsL4U4.projToPGL_injective 3
  rw [map_mul, map_mul, ← hga, ← hgb, ← map_mul, ← map_mul]
  exact congrArg _ (congrArg Subtype.val hgg)

theorem ivk93w_l3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93WEmptyQ (fun X _ => LieModel X .PSL 3 p f) := by
  intro p f hp hp2 hf J _ _ hJ x q B h _ hQ
  have hQx : Ivk93WQuat x B := hQ (ivk93w_odd_commutator_outer_psl3 hJ)
  obtain ⟨⟨-, -, -⟩, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSL hJ
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_natCard hodd
  have : Finite (StatedProj (StatedSL 3 F)) := Finite.of_equiv _ e.toEquiv
  exact ivk93w_l3_false h2 (h.of_equiv e) (hQx.of_equiv e)

end CFSG.GH74.GLS.IVK.Proofs2
