module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveSquare
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveA4Weyl
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveFrameElt
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FivePurityLang
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveSolvable

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (charVal)


namespace E8FiveSq

theorem rootChar_eq_of_charVal_eq {τ : Tag} {M : Type} [Field M] {ω : Mˣ} (hω : orderOf ω = 5)
    {k k' : Fin τ.rank → ℕ} {a a' : Fin τ.rank → Mˣ} (ha : ∀ i, a i = ω ^ k i)
    (ha' : ∀ i, a' i = ω ^ k' i) {l l' : Fin τ.rank → ℤ}
    (h : charVal (fun i => ((k i : ℕ) : ZMod 5)) l = charVal (fun i => ((k' i : ℕ) : ZMod 5)) l') :
    rootChar a l = rootChar a' l' := by
  rw [rootChar_eq_zpow k a ha, rootChar_eq_zpow k' a' ha', zpow_eq_zpow_iff_modEq, hω]
  rw [charVal_natCast_eq, charVal_natCast_eq] at h
  exact (ZMod.intCast_eq_intCast_iff _ _ 5).1 h

theorem exists_exps_of_mem {K : Type} [Field K] [Finite K] {ω : (AlgebraicClosure K)ˣ}
    (hω : orderOf ω = 5) {E₀ : Subgroup (adjointGroup Tag.E8 K)} (D : LangPlaneData Tag.E8 K E₀)
    {x₀ x₁ : adjointGroup Tag.E8 K} (hgen : E₀ ≤ Subgroup.closure {x₀, x₁})
    {k₀ k₁ : Fin Tag.E8.rank → ℕ}
    (ha₀ : rootDiagUnit Tag.E8 (fun l => ω ^ k₀ l) = diagMap D x₀)
    (ha₁ : rootDiagUnit Tag.E8 (fun l => ω ^ k₁ l) = diagMap D x₁)
    {e : adjointGroup Tag.E8 K} (he : e ∈ E₀) :
    ∃ i j : ℕ, rootDiagUnit Tag.E8 (fun l => ω ^ (i * k₀ l + j * k₁ l)) = diagMap D e := by
  have h5 : ω ^ 5 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hmul : ∀ a b : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit Tag.E8 (a * b) = rootDiagUnit Tag.E8 a * rootDiagUnit Tag.E8 b :=
    fun a b => map_mul (rootDiagUnitHom Tag.E8 (AlgebraicClosure K)) a b
  have hinv : ∀ a : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit Tag.E8 a⁻¹ = (rootDiagUnit Tag.E8 a)⁻¹ :=
    fun a => map_inv (rootDiagUnitHom Tag.E8 (AlgebraicClosure K)) a
  have hone : rootDiagUnit Tag.E8 (1 : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ) = 1 :=
    map_one (rootDiagUnitHom Tag.E8 (AlgebraicClosure K))
  let S : Subgroup (adjointGroup Tag.E8 K) :=
    { carrier := {e | ∃ i j : ℕ,
        rootDiagUnit Tag.E8 (fun l => ω ^ (i * k₀ l + j * k₁ l)) = diagMap D e}
      one_mem' := ⟨0, 0, by
        rw [map_one, ← hone]
        congr 1
        funext l
        simp⟩
      mul_mem' := by
        rintro e e' ⟨i, j, h⟩ ⟨i', j', h'⟩
        refine ⟨i + i', j + j', ?_⟩
        rw [map_mul, ← h, ← h', ← hmul]
        congr 1
        funext l
        simp only [Pi.mul_apply, ← pow_add]
        congr 1
        ring
      inv_mem' := by
        rintro e ⟨i, j, h⟩
        refine ⟨4 * i, 4 * j, ?_⟩
        rw [map_inv, ← h, ← hinv]
        congr 1
        funext l
        simp only [Pi.inv_apply]
        rw [eq_inv_iff_mul_eq_one, ← pow_add]
        have e5 : 4 * i * k₀ l + 4 * j * k₁ l + (i * k₀ l + j * k₁ l) =
            5 * (i * k₀ l + j * k₁ l) := by ring
        rw [e5, pow_mul, h5, one_pow] }
  have hS : E₀ ≤ S := hgen.trans ((Subgroup.closure_le S).2 (by
    rintro y (rfl | rfl)
    · show ∃ i j : ℕ, rootDiagUnit Tag.E8 (fun l => ω ^ (i * k₀ l + j * k₁ l)) = diagMap D y
      refine ⟨1, 0, ?_⟩
      rw [← ha₀]
      congr 1
      funext l
      simp
    · show ∃ i j : ℕ, rootDiagUnit Tag.E8 (fun l => ω ^ (i * k₀ l + j * k₁ l)) = diagMap D y
      refine ⟨0, 1, ?_⟩
      rw [← ha₁]
      congr 1
      funext l
      simp))
  exact hS he

theorem isSolvable_centralizer_of_regular_five {K : Type} [Field K] [Finite K]
    (hpK : ¬ 5 ∣ Nat.card K) {E₀ : Subgroup (adjointGroup Tag.E8 K)}
    (hE₀p : ∀ x ∈ E₀, x ^ 5 = 1) (hE₀c : Nat.card E₀ = 5 ^ 2) (D : LangPlaneData Tag.E8 K E₀)
    (hreg : ∀ α, IsRoot Tag.E8 α → ¬ D.Kills α) :
    Group.IsSolvable ↥(Subgroup.centralizer (E₀ : Set (adjointGroup Tag.E8 K))) := by
  obtain ⟨ω, hω⟩ := exists_orderOf_eq_five_of_not_dvd hpK
  obtain ⟨x₀, hx₀, x₁, hx₁, -, -, k₀, k₁, ha₀, ha₁, hreg'⟩ :=
    exists_planeColumns hω hE₀p hE₀c D hreg
  refine isSolvable_centralizer_of_familyStab D hreg fun a ha => ?_
  have hstab : ∀ (x : adjointGroup Tag.E8 K) (hx : x ∈ E₀) (k : Fin Tag.E8.rank → ℕ),
      rootDiagUnit Tag.E8 (fun l => ω ^ k l) = diagMap D x →
        ∀ w : WeylGroup Tag.E8, (∀ v, rootChar (a ⟨x, hx⟩) (w • v) = rootChar (a ⟨x, hx⟩) v) →
          w ∈ dualWeylStabilizer (fun i => ((k i : ℕ) : ZMod 5)) := by
    intro x hx k hk w hw
    have h : a ⟨x, hx⟩ = fun l => ω ^ k l :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective
        ((ha ⟨x, hx⟩).trans hk.symm)
    refine mem_dualWeylStabilizer.2 fun v => ?_
    have hv := hw v
    rw [h] at hv
    exact (rootChar_eq_rootChar_iff hω k _ (fun _ => rfl) _ _).1 hv
  refine ⟨_, isSolvable_inf_dualWeylStabilizer hreg', fun w hw => Subgroup.mem_inf.2
    ⟨hstab x₀ hx₀ k₀ ha₀ w (hw ⟨x₀, hx₀⟩), hstab x₁ hx₁ k₁ ha₁ w (hw ⟨x₁, hx₁⟩)⟩⟩

theorem exists_conj_frameElt {K : Type} [Field K] [Finite K] (hpK : ¬ 5 ∣ Nat.card K)
    {E₀ : Subgroup (adjointGroup Tag.E8 K)} (hE₀p : ∀ x ∈ E₀, x ^ 5 = 1)
    (hE₀c : Nat.card E₀ = 5 ^ 2) (D : LangPlaneData Tag.E8 K E₀)
    (hreg : ∀ α, IsRoot Tag.E8 α → ¬ D.Kills α) {V : WeylGroup Tag.E8} (hV1 : V ≠ 1)
    (hV : ∀ x ∈ E₀, ∀ a : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit Tag.E8 a = diagMap D x → ∀ v, rootChar a (V • v) = rootChar a v)
    (F : E8FiveFrameElt K) {e : adjointGroup Tag.E8 K} (he : e ∈ E₀) (he1 : e ≠ 1) :
    ∃ g : adjointGroup Tag.E8 K, g * e * g⁻¹ = F.z := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : F.ω ^ 5 = 1 := by rw [← F.hω]; exact pow_orderOf_eq_one F.ω
  obtain ⟨x₀, hx₀, x₁, hx₁, -, hgen, k₀, k₁, ha₀, ha₁, hreg'⟩ :=
    exists_planeColumns F.hω hE₀p hE₀c D hreg
  have hfix : ∀ (k : Fin Tag.E8.rank → ℕ) (x : adjointGroup Tag.E8 K), x ∈ E₀ →
      rootDiagUnit Tag.E8 (fun l => F.ω ^ k l) = diagMap D x →
        V ∈ dualWeylStabilizer (fun i => ((k i : ℕ) : ZMod 5)) := by
    intro k x hx hk
    refine mem_dualWeylStabilizer.2 fun v => ?_
    exact (rootChar_eq_rootChar_iff F.hω k _ (fun _ => rfl) _ _).1 (hV x hx _ hk v)
  obtain ⟨y, hy, hy₀, hy₁⟩ :=
    exists_orderOf_eq_five_of_fix hreg' hV1 (hfix k₀ x₀ hx₀ ha₀) (hfix k₁ x₁ hx₁ ha₁)
  obtain ⟨i, j, hij⟩ := exists_exps_of_mem F.hω D hgen ha₀ ha₁ he
  have hne : (i : ZMod 5) • (fun l => ((k₀ l : ℕ) : ZMod 5)) +
      (j : ZMod 5) • (fun l => ((k₁ l : ℕ) : ZMod 5)) ≠ 0 := by
    intro h0
    apply he1
    apply diagMap_injective D
    rw [← hij, map_one]
    have hone : rootDiagUnit Tag.E8 (1 : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ) = 1 :=
      map_one (rootDiagUnitHom Tag.E8 (AlgebraicClosure K))
    rw [← hone]
    congr 1
    funext l
    have hl := congrFun h0 l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hl
    have hdvd : 5 ∣ i * k₀ l + j * k₁ l := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
      exact hl
    obtain ⟨m, hm⟩ := hdvd
    show F.ω ^ (i * k₀ l + j * k₁ l) = 1
    rw [hm, pow_mul, h5, one_pow]
  obtain ⟨u, hu⟩ := exists_orbit_of_fix hreg' hy hy₀ hy₁ hne
  have hcolE : (fun l => ((i * k₀ l + j * k₁ l : ℕ) : ZMod 5)) =
      (i : ZMod 5) • (fun l => ((k₀ l : ℕ) : ZMod 5)) +
        (j : ZMod 5) • (fun l => ((k₁ l : ℕ) : ZMod 5)) := by
    funext l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hcol4 : (fun l : Fin Tag.E8.rank => ((if l = 4 then 1 else 0 : ℕ) : ZMod 5)) =
      Pi.single (4 : Fin Tag.E8.rank) (1 : ZMod 5) := by
    funext l
    by_cases hl : l = 4
    · subst hl
      simp
    · simp [hl]
  have hu' : ∀ v : Fin Tag.E8.rank → ℤ,
      rootChar (fun l => F.ω ^ (i * k₀ l + j * k₁ l)) (u • v) =
        rootChar (Pi.mulSingle (4 : Fin Tag.E8.rank) F.ω) v := by
    intro v
    refine rootChar_eq_of_charVal_eq F.hω (k := fun l => i * k₀ l + j * k₁ l)
      (k' := fun l => if l = 4 then 1 else 0) (a := fun l => F.ω ^ (i * k₀ l + j * k₁ l))
      (a' := Pi.mulSingle (4 : Fin Tag.E8.rank) F.ω) (fun _ => rfl) (fun l => ?_) ?_
    · by_cases hl : l = 4
      · subst hl
        simp
      · simp [hl]
    · show charVal (fun l => ((i * k₀ l + j * k₁ l : ℕ) : ZMod 5)) (u • v) =
        charVal (fun l : Fin Tag.E8.rank => ((if l = 4 then 1 else 0 : ℕ) : ZMod 5)) v
      rw [hcolE, hcol4]
      exact hu v
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hpK'⟩ := CharP.exists K
  obtain ⟨n, hpp, hcard⟩ := FiniteField.card K p
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hq : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hp5 : p ≠ 5 := by
    rintro rfl
    exact hpK (by rw [hq]; exact dvd_pow_self 5 n.ne_zero)
  have hFDz := F.hFDz (iterateFrobenius (AlgebraicClosure K) p n) fun c => by
    rw [iterateFrobenius_def, hq]
  obtain ⟨g, hg⟩ := lang_core_five hp5 (Nat.one_le_iff_ne_zero.2 n.ne_zero) hq F.ω F.hω F.Dz F.Q
    F.hDz F.hQ F.hs hFDz F.hQd F.z F.hz D.g0 D.hg0C (D.c * e * D.c⁻¹) _
    (hij.trans (diagMap_apply D e)) u hu'
  exact ⟨g * D.c, by rw [← hg]; group⟩

theorem planeCl_eq_top_of_frameElt {K : Type} [Field K] [Finite K] (hpK : ¬ 5 ∣ Nat.card K)
    {E₀ : Subgroup (adjointGroup Tag.E8 K)} (hE₀p : ∀ x ∈ E₀, x ^ 5 = 1)
    (hE₀c : Nat.card E₀ = 5 ^ 2) (D : LangPlaneData Tag.E8 K E₀)
    (hreg : ∀ α, IsRoot Tag.E8 α → ¬ D.Kills α) {V : WeylGroup Tag.E8} (hV1 : V ≠ 1)
    (hV : ∀ x ∈ E₀, ∀ a : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit Tag.E8 a = diagMap D x → ∀ v, rootChar a (V • v) = rootChar a v)
    (F : E8FiveFrameElt K) : planeCl E₀ = ⊤ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨a, ha, b, hb, ha1, hb1, hgen⟩ := exists_gens_of_plane (p := 5) hE₀p hE₀c
  obtain ⟨X, hX⟩ := F.frame
  obtain ⟨ga, hga⟩ := exists_conj_frameElt hpK hE₀p hE₀c D hreg hV1 hV F ha ha1
  obtain ⟨gb, hgb⟩ := exists_conj_frameElt hpK hE₀p hE₀c D hreg hV1 hV F hb hb1
  have hXa : ClosingFrameAt a (X.map (MulAut.conj ga⁻¹).toMonoidHom) := by
    have := hX.conj ga⁻¹
    rwa [show ga⁻¹ * F.z * ga⁻¹⁻¹ = a by rw [← hga]; group] at this
  have hXb : ClosingFrameAt b (X.map (MulAut.conj gb⁻¹).toMonoidHom) := by
    have := hX.conj gb⁻¹
    rwa [show gb⁻¹ * F.z * gb⁻¹⁻¹ = b by rw [← hgb]; group] at this
  exact planeCl_eq_top_of_closingFrames ha hb ha1 hb1 hgen hXa hXb
    (isSolvable_centralizer_of_regular_five hpK hE₀p hE₀c D hreg)

end E8FiveSq

end CFSG.LieType.SeitzGeneration.ExcHigh
