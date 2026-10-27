module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311c
public import CFSG.LieType.SeitzGeneration.NonabParabolic
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
import CFSG.LieType.SeitzGeneration.QuasiHigh
public import CFSG.LieType.SeitzGeneration.OuterLinearField
import CFSG.LieType.SeitzGeneration.OuterLinearTwo
public import CFSG.LieType.SeitzGeneration.Inner
public import CFSG.RankThree.PartOne.CTP.SeitzToral

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)
open Matrix
open scoped commutatorElement

section Unip

variable {F : Type*} [Field F] {n : ℕ}

theorem one_add_pow_of_mul_self_eq_zero {φ : Matrix (Fin n) (Fin n) F} (h : φ * φ = 0) (m : ℕ) :
    (1 + φ) ^ m = 1 + (m : F) • φ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih]
    simp only [Nat.cast_succ, add_smul, one_smul, add_mul, mul_add, Matrix.mul_one,
      Matrix.one_mul, Matrix.smul_mul, h, smul_zero, add_zero]
    abel

theorem unipSL_pow_ringChar [Finite F] {W : Submodule F (Fin n → F)} {φ : Matrix (Fin n) (Fin n) F}
    (hφ : φ ∈ thetaSpace W) : unipSL hφ ^ ringChar F = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_unipSL, one_add_pow_of_mul_self_eq_zero (thetaSpace_mul hφ hφ),
    ringChar.Nat.cast_ringChar, zero_smul, add_zero]
  rfl

@[expose] def uniCentralizerGens (H : Subgroup (SpecialLinearGroup (Fin n) F)) :
    Set (SpecialLinearGroup (Fin n) F) :=
  {g | (∃ x ∈ H, x ∉ Subgroup.center (SpecialLinearGroup (Fin n) F) ∧
    ⁅g, x⁆ ∈ Subgroup.center (SpecialLinearGroup (Fin n) F)) ∧ g ^ ringChar F = 1}

theorem unip_mem_closure_uniCentralizerGens [Finite F] {p : ℕ} [Fact p.Prime] (hpF : (p : F) ≠ 0)
    {H : Subgroup (SpecialLinearGroup (Fin n) F)} {a b : SpecialLinearGroup (Fin n) F}
    (ha : a ∈ H) (hb : b ∈ H) (hap : a ^ p ∈ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hbp : b ^ p ∈ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hab : ⁅a, b⁆ ∈ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hline : ∀ j : ℕ, a * b ^ j ∉ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hbc : b ∉ Subgroup.center (SpecialLinearGroup (Fin n) F))
    {W : Submodule F (Fin n → F)}
    (hW : ∀ x ∈ H, ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W)
    (g : SpecialLinearGroup (Fin n) F) (hg : (g : Matrix (Fin n) (Fin n) F) - 1 ∈ thetaSpace W) :
    g ∈ Subgroup.closure (uniCentralizerGens H) := by
  classical
  set K := Subgroup.closure (uniCentralizerGens H) with hK
  set φ : Matrix (Fin n) (Fin n) F := (g : Matrix (Fin n) (Fin n) F) - 1 with hφ
  have hA : conjAction a ^ p = 1 := by
    rw [← map_pow]; exact conjAction_eq_one_of_mem_center hap
  have hB : conjAction b ^ p = 1 := by
    rw [← map_pow]; exact conjAction_eq_one_of_mem_center hbp
  have hAB : Commute (conjAction a) (conjAction b) := by
    have h1 : a * b = ⁅a, b⁆ * (b * a) := by
      simp only [commutatorElement_def]; group
    show conjAction a * conjAction b = conjAction b * conjAction a
    rw [← map_mul, ← map_mul, h1, map_mul, conjAction_eq_one_of_mem_center hab, one_mul]
  obtain ⟨u, v, hu, hv, hsum, hmem⟩ := exists_decomp_lines hpF hAB hA hB φ
  have hAS : ∀ x ∈ thetaSpace W, conjAction a x ∈ thetaSpace W := fun x hx =>
    conjAction_mem_thetaSpace hW ha hx
  have hBS : ∀ x ∈ thetaSpace W, conjAction b x ∈ thetaSpace W := fun x hx =>
    conjAction_mem_thetaSpace hW hb hx
  obtain ⟨huS, hvS⟩ := hmem (thetaSpace W) hAS hBS hg
  have hu_mem : ∀ j : ZMod p, ∃ h : u j ∈ thetaSpace W, unipSL h ∈ K := fun j => by
    refine ⟨huS j, Subgroup.subset_closure ⟨⟨a * b ^ j.val,
      H.mul_mem ha (H.pow_mem hb _), hline _, ?_⟩, unipSL_pow_ringChar _⟩⟩
    have hfix : conjAction (a * b ^ j.val) (u j) = u j := by
      simpa only [map_mul, map_pow] using hu j
    have hcomm := commute_unipSL (huS j) (commute_of_conjAction_eq hfix)
    rw [commutatorElement_eq_one_iff_mul_comm.2 hcomm.symm.eq]
    exact one_mem _
  have hv_mem : ∃ h : v ∈ thetaSpace W, unipSL h ∈ K := by
    refine ⟨hvS, Subgroup.subset_closure ⟨⟨b, hb, hbc, ?_⟩, unipSL_pow_ringChar _⟩⟩
    have hcomm := commute_unipSL hvS (commute_of_conjAction_eq hv)
    rw [commutatorElement_eq_one_iff_mul_comm.2 hcomm.symm.eq]
    exact one_mem _
  let T : AddSubmonoid (Matrix (Fin n) (Fin n) F) :=
    { carrier := {ψ | ∃ h : ψ ∈ thetaSpace W, unipSL h ∈ K}
      zero_mem' := ⟨(thetaSpace W).zero_mem, by
        have : unipSL (thetaSpace W).zero_mem = 1 := Subtype.ext (by simp [coe_unipSL])
        rw [this]; exact K.one_mem⟩
      add_mem' := by
        rintro ψ ψ' ⟨h, hKψ⟩ ⟨h', hKψ'⟩
        refine ⟨(thetaSpace W).add_mem h h', ?_⟩
        have : unipSL ((thetaSpace W).add_mem h h') = unipSL h * unipSL h' := Subtype.ext (by
          show 1 + (ψ + ψ') = (1 + ψ) * (1 + ψ')
          simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, thetaSpace_mul h h',
            add_zero]
          abel)
        rw [this]; exact K.mul_mem hKψ hKψ' }
  have hφT : φ ∈ T := by
    rw [hsum]
    exact T.add_mem (T.sum_mem fun j _ => hu_mem j) hv_mem
  obtain ⟨h, hKφ⟩ := hφT
  have : unipSL h = g := Subtype.ext (by
    show 1 + φ = (g : Matrix (Fin n) (Fin n) F)
    rw [hφ]; abel)
  rwa [this] at hKφ

theorem closure_uniCentralizerGens_eq_top_of_invariant [Finite F] {p : ℕ} [Fact p.Prime]
    (hpF : (p : F) ≠ 0) {H : Subgroup (SpecialLinearGroup (Fin n) F)}
    (hH : (Nat.card H : F) ≠ 0) {a b : SpecialLinearGroup (Fin n) F} (ha : a ∈ H) (hb : b ∈ H)
    (hap : a ^ p ∈ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hbp : b ^ p ∈ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hab : ⁅a, b⁆ ∈ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hline : ∀ j : ℕ, a * b ^ j ∉ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hbc : b ∉ Subgroup.center (SpecialLinearGroup (Fin n) F))
    {W : Submodule F (Fin n → F)} (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤)
    (hWH : ∀ x ∈ H, ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W) :
    Subgroup.closure (uniCentralizerGens H) = ⊤ := by
  obtain ⟨W', hc, hW'H⟩ := exists_invariant_compl hH hWH
  have hW'0 : W' ≠ ⊥ := fun h => hWt (by
    have := codisjoint_iff.1 hc.2
    rwa [h, sup_bot_eq] at this)
  exact eq_top_of_unip_isCompl hc hW0 hW'0
    (unip_mem_closure_uniCentralizerGens hpF ha hb hap hbp hab hline hbc hWH)
    (unip_mem_closure_uniCentralizerGens hpF ha hb hap hbp hab hline hbc hW'H)

end Unip

section Psl

variable {F : Type*} [Field F] {n : ℕ}

theorem uniClosure_psl_of_reducible [Finite F] {p : ℕ} (hp : p.Prime)
    (hpF : (p : F) ≠ 0)
    (hZF : (Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) F)) : F) ≠ 0)
    (E : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) {W : Submodule F (Fin n → F)} (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤)
    (hWE : ∀ x : SpecialLinearGroup (Fin n) F,
      QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) x ∈ E →
        ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W) :
    Subgroup.closure {k : ProjectiveSpecialLinearGroup (Fin n) F |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k ∧ k ^ ringChar F = 1} = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set Z := Subgroup.center (SpecialLinearGroup (Fin n) F) with hZ
  set π : SpecialLinearGroup (Fin n) F →* ProjectiveSpecialLinearGroup (Fin n) F :=
    QuotientGroup.mk' Z with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Z := QuotientGroup.ker_mk' _
  set H : Subgroup (SpecialLinearGroup (Fin n) F) := E.comap π with hH
  obtain ⟨x, hxE, y, hyE, hy1, hxy⟩ := exists_independent_pair hp E hexp hcard
  obtain ⟨a, rfl⟩ := hπ x
  obtain ⟨b, rfl⟩ := hπ y
  have hmemZ : ∀ g : SpecialLinearGroup (Fin n) F, g ∈ Z ↔ π g = 1 := fun g => by
    rw [← hker, MonoidHom.mem_ker]
  have hcardH : Nat.card H = Nat.card E * Nat.card Z := by
    let φ : H →* E := (π.comp H.subtype).codRestrict E (fun h => h.2)
    have hφ : Function.Surjective φ := fun e => by
      obtain ⟨g, hg⟩ := hπ (e : ProjectiveSpecialLinearGroup (Fin n) F)
      exact ⟨⟨g, by simp [hH, hg]⟩, Subtype.ext hg⟩
    have hker_le : π.ker ≤ H := fun z hz => by
      rw [hH, Subgroup.mem_comap, MonoidHom.mem_ker.1 hz]; exact E.one_mem
    have hφker : φ.ker = π.ker.subgroupOf H := by
      ext g
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have hN : Nat.card φ.ker = Nat.card Z := by
      rw [hφker, ← hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv
    rw [← Subgroup.card_ker_mul_card_of_surjective hφ, hN, mul_comm]
  have hHF : (Nat.card H : F) ≠ 0 := by
    rw [hcardH, hcard, Nat.cast_mul, Nat.cast_pow]
    exact mul_ne_zero (pow_ne_zero 2 hpF) hZF
  have hgen : Subgroup.closure (uniCentralizerGens H) = ⊤ := by
    refine closure_uniCentralizerGens_eq_top_of_invariant hpF hHF (a := a) (b := b)
      (Subgroup.mem_comap.2 hxE) (Subgroup.mem_comap.2 hyE) ?_ ?_ ?_ ?_ ?_ hW0 hWt ?_
    · rw [hmemZ, map_pow]; exact hexp _ hxE
    · rw [hmemZ, map_pow]; exact hexp _ hyE
    · rw [hmemZ, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ hxE _ hyE)
    · intro j hj
      rw [hmemZ, map_mul, map_pow] at hj
      apply hxy
      have : π a = ((π b) ^ j)⁻¹ := eq_inv_of_mul_eq_one_left hj
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j)
    · intro hb
      exact hy1 ((hmemZ b).1 hb)
    · exact fun g hg => hWE g hg
  rw [eq_top_iff]
  have hle : (Subgroup.closure (uniCentralizerGens H)).map π ≤ Subgroup.closure
      {k : ProjectiveSpecialLinearGroup (Fin n) F |
        ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k ∧ k ^ ringChar F = 1} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, ⟨⟨c, hcH, hcZ, hgc⟩, hgr⟩, rfl⟩
    refine Subgroup.subset_closure ⟨π c, hcH, fun h1 => hcZ ((hmemZ c).2 h1), ?_, ?_⟩
    · have h1 : ⁅π g, π c⁆ = 1 := by
        rw [← map_commutatorElement]; exact (hmemZ _).1 hgc
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    · rw [← map_pow, hgr, map_one]
  rw [hgen, Subgroup.map_top_of_surjective π hπ] at hle
  exact hle

theorem exists_invariant_of_plane_sl_prime {p : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hpF : (p : F) ≠ 0)
    {E : Subgroup (SpecialLinearGroup (Fin n) F)}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) :
    ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ x ∈ E, ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hxE, y, hyE, hy1, hxy⟩ := exists_independent_pair hp E hexp hcard
  let ρ : SpecialLinearGroup (Fin n) F → Module.End F (Fin n → F) := fun g =>
    Matrix.toLin' (g : Matrix (Fin n) (Fin n) F)
  have hmul : ∀ g h, ρ (g * h) = ρ g * ρ h := fun g h => by
    simp only [ρ, Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin'_mul]
    rfl
  have hone : ρ 1 = 1 := by
    simp only [ρ, Matrix.SpecialLinearGroup.coe_one, Matrix.toLin'_one]
    rfl
  have hpow : ∀ (g : SpecialLinearGroup (Fin n) F) (k : ℕ), ρ (g ^ k) = ρ g ^ k := by
    intro g k
    induction k with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ k ih => rw [pow_succ, hmul, ih, pow_succ]
  have hρ : ∀ g v, ρ g v = (g : Matrix (Fin n) (Fin n) F).mulVec v := fun g v => by
    simp [ρ, Matrix.toLin'_apply]
  have hAB : Commute (ρ x) (ρ y) := by
    show ρ x * ρ y = ρ y * ρ x
    rw [← hmul, ← hmul, hcomm x hxE y hyE]
  have hA : ρ x ^ p = 1 := by rw [← hpow, hexp x hxE, hone]
  have hB : ρ y ^ p = 1 := by rw [← hpow, hexp y hyE, hone]
  set i₀ : Fin n := ⟨0, by omega⟩
  set m : Fin n → F := Pi.single i₀ 1 with hmdef
  have hm0 : m ≠ 0 := by
    intro h
    have := congrFun h i₀
    simp [m] at this
  obtain ⟨u, v, hu, hv, hsum, -⟩ := exists_decomp_lines hpF hAB hA hB m
  obtain ⟨z, hzE, hz1, w, hw0, hzw⟩ : ∃ z ∈ E, z ≠ 1 ∧ ∃ w : Fin n → F, w ≠ 0 ∧ ρ z w = w := by
    by_cases hv0 : v = 0
    · have hj : ∃ j, u j ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hm0
        rw [hsum, hv0, add_zero]
        exact Finset.sum_eq_zero fun j _ => hcon j
      obtain ⟨j, hj⟩ := hj
      refine ⟨x * y ^ j.val, E.mul_mem hxE (E.pow_mem hyE _), ?_, u j, hj, ?_⟩
      · intro h
        apply hxy
        have : x = (y ^ j.val)⁻¹ := eq_inv_of_mul_eq_one_left h
        rw [this]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
      · rw [hmul, hpow]
        exact hu j
    · exact ⟨y, hyE, hy1, v, hv0, hv⟩
  let W : Submodule F (Fin n → F) := LinearMap.ker (ρ z - 1)
  have hmemW : ∀ w, w ∈ W ↔ ρ z w = w := fun w => by
    simp [W, LinearMap.mem_ker, sub_eq_zero]
  have hWE : ∀ x ∈ E, ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W := fun x hx w hw => by
    rw [← hρ, hmemW] at *
    rw [← Module.End.mul_apply, ← hmul, hcomm z hzE x hx, hmul, Module.End.mul_apply, hw]
  have hW0 : W ≠ ⊥ := fun h => hw0 (by
    have : w ∈ W := (hmemW w).2 hzw
    rw [h] at this
    exact (Submodule.mem_bot F).1 this)
  have hWt : W ≠ ⊤ := fun h => hz1 (by
    have h1 : ρ z = 1 := LinearMap.ext fun v => (hmemW v).1 (h ▸ Submodule.mem_top)
    have h2 : (z : Matrix (Fin n) (Fin n) F) = 1 := by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_one]
      exact h1
    exact Subtype.ext h2)
  exact ⟨W, hW0, hWt, hWE⟩

end Psl

section PslAb

variable {F : Type} [Field F] [Finite F] {n : ℕ}

theorem uniClosure_psl_ab {p : ℕ} (hp : p.Prime) (hn : 2 ≤ n) (hpF : (p : F) ≠ 0)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)))
    (E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) F))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : Matrix.ProjectiveSpecialLinearGroup (Fin n) F |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k ∧ k ^ ringChar F = 1} = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite (Matrix.SpecialLinearGroup (Fin n) F) :=
    Finite.of_injective (Subtype.val : Matrix.SpecialLinearGroup (Fin n) F →
      Matrix (Fin n) (Fin n) F) Subtype.val_injective
  set Z := Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F) with hZdef
  set π : Matrix.SpecialLinearGroup (Fin n) F →* Matrix.ProjectiveSpecialLinearGroup (Fin n) F :=
    QuotientGroup.mk' Z with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Z := QuotientGroup.ker_mk' _
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  obtain ⟨E', hE'map, hE'dis⟩ := CFSG.RankThree.PartOne.CTP.SeitzToral.exists_lift_of_coprime_ker
    π hπ (by rwa [hker]) E hEp
  have hE'mem : ∀ x ∈ E', π x ∈ E := fun x hx => hE'map ▸ ⟨x, hx, rfl⟩
  have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    intro a ha b hb
    have hc : a * b * a⁻¹ * b⁻¹ ∈ E' :=
      E'.mul_mem (E'.mul_mem (E'.mul_mem ha hb) (E'.inv_mem ha)) (E'.inv_mem hb)
    have hk : a * b * a⁻¹ * b⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      have := hcomm _ (hE'mem a ha) _ (hE'mem b hb)
      rw [this]
      group
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.disjoint_def.mp hE'dis hc hk)
  have hE'exp : ∀ a ∈ E', a ^ p = 1 := by
    intro a ha
    have hk : a ^ p ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hexp _ (hE'mem a ha)
    exact Subgroup.disjoint_def.mp hE'dis (E'.pow_mem ha p) hk
  have hE'card : Nat.card E' = p ^ 2 := by
    let fπ : E' →* E := (π.comp E'.subtype).codRestrict E (fun x => hE'mem x.1 x.2)
    have hfπsurj : Function.Surjective fπ := by
      intro e
      have : (e : Matrix.ProjectiveSpecialLinearGroup (Fin n) F) ∈ E'.map π := hE'map ▸ e.2
      obtain ⟨x, hx, hxe⟩ := this
      exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
    have hfπinj : Function.Injective fπ := by
      intro x y hxy
      have h1 : π x.1 = π y.1 := congrArg Subtype.val hxy
      have h2 : x.1⁻¹ * y.1 ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
      have h3' : x.1⁻¹ * y.1 = 1 :=
        Subgroup.disjoint_def.mp hE'dis (E'.mul_mem (E'.inv_mem x.2) y.2) h2
      exact Subtype.ext (inv_mul_eq_one.mp h3')
    rw [← hcard]
    exact Nat.card_congr (Equiv.ofBijective fπ ⟨hfπinj, hfπsurj⟩)
  obtain ⟨W, hW0, hWt, hWE'⟩ :=
    exists_invariant_of_plane_sl_prime hp (by omega) hpF hE'comm hE'exp hE'card
  refine uniClosure_psl_of_reducible hp hpF (natCast_card_center_ne_zero (by omega)) E hcomm hexp hcard hW0
    hWt ?_
  intro x hx w hw
  obtain ⟨e, he, hex⟩ : ∃ e ∈ E', π e = π x := by
    have : π x ∈ E'.map π := hE'map ▸ hx
    obtain ⟨e, he, h⟩ := this
    exact ⟨e, he, h⟩
  have hz : x * e⁻¹ ∈ Z := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, ← hex, mul_inv_cancel]
  obtain ⟨r, -, hr⟩ := exists_scalar_of_mem_center (by omega) hz
  have hxe : (x : Matrix (Fin n) (Fin n) F) = r • (e : Matrix (Fin n) (Fin n) F) := by
    have h1 : x = (x * e⁻¹) * e := by group
    have h2 := congrArg
      (fun g : Matrix.SpecialLinearGroup (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) h1
    simp only [Matrix.SpecialLinearGroup.coe_mul, hr, Matrix.smul_mul, Matrix.one_mul] at h2
    exact h2
  rw [hxe, Matrix.smul_mulVec]
  exact W.smul_mem r (hWE' e he w hw)

end PslAb

section Model

theorem uniPlaneGen_of_inner_model {K P : Type*} [Group K] [Group P] {p r : ℕ}
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) (e : K ≃* P)
    (hP : ∀ E₁ : Subgroup P, IsElemAbelian p E₁ → Nat.card E₁ = p ^ 2 →
      Subgroup.closure {k' : P | ∃ x ∈ E₁, x ≠ 1 ∧ k' * x = x * k' ∧ k' ^ r = 1} = ⊤)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hinner : E ≤ (MulAut.conj : K →* MulAut K).range) : UniPlaneGen r E := by
  set E₀ : Subgroup K := E.comap (MulAut.conj : K →* MulAut K) with hE₀
  have hmap : E₀.map (MulAut.conj : K →* MulAut K) = E := Subgroup.map_comap_eq_self hinner
  have hE₀el : IsElemAbelian p E₀ := isElemAbelian_comap_conj hinj hE
  have hE₀card : Nat.card E₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap, hc]
  have hE₁el : IsElemAbelian p (E₀.map e.toMonoidHom) := CFSG.Open.IsElemAbelian.map hE₀el _
  have hE₁card : Nat.card (E₀.map e.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective e.injective, hE₀card]
  have h1 := hP _ hE₁el hE₁card
  have hle : (⊤ : Subgroup P) ≤
      (Subgroup.closure {k : K | ∃ x ∈ E₀, x ≠ 1 ∧ k * x = x * k ∧ k ^ r = 1}).map e.toMonoidHom := by
    rw [MonoidHom.map_closure, ← h1]
    refine Subgroup.closure_mono ?_
    rintro k' ⟨_, ⟨x, hx, rfl⟩, hx1, hk, hkr⟩
    refine ⟨e.symm k', ⟨x, hx, ?_, ?_, ?_⟩, by simp⟩
    · rintro rfl
      exact hx1 (map_one _)
    · apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hk
    · apply e.injective
      rw [map_pow, MulEquiv.apply_symm_apply, hkr, map_one]
  have h2 : Subgroup.closure {k : K | ∃ x ∈ E₀, x ≠ 1 ∧ k * x = x * k ∧ k ^ r = 1} = ⊤ := by
    rw [eq_top_iff]
    intro k _
    obtain ⟨c, hc', hck⟩ := hle (Subgroup.mem_top (e k))
    exact (e.injective hck) ▸ hc'
  rw [UniPlaneGen, eq_top_iff, ← h2, Subgroup.closure_le]
  rintro k ⟨x, hx, hx1, hk, hkr⟩
  refine mem_uniPlaneClosure (E := E) (e := MulAut.conj x) hx ?_ ?_ (n := 1) (by rw [pow_one]; exact hkr)
  · intro h
    exact hx1 (hinj (by simpa using h))
  · rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    exact hk.symm

end Model

theorem uniPlaneGen_inner_A {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) {p : ℕ} (hp : p.Prime)
    (hpq : p ≠ q.p) (hlift : ¬ (p ∣ q.card - 1 ∧ p ∣ m + 1))
    {E : Subgroup (MulAut (Cat ⟨.A m q, hv⟩))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hinner : InnerPlane ⟨.A m q, hv⟩ p E) : UniPlaneGen q.p E := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Fact p.Prime := ⟨hp⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm1 : 1 ≤ m := hrange.1
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hfour : 3 ≤ m + 1 ∨ ∃ s : Finset (GaloisField q.p q.exponent), s.card = 4 := by
    by_cases h3 : 3 ≤ m + 1
    · exact Or.inl h3
    · right
      have h4 : 4 ≤ q.card := hrange.2 (by omega)
      have : Fintype (GaloisField q.p q.exponent) := Fintype.ofFinite _
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ :
        Finset (GaloisField q.p q.exponent))) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcardF]; exact h4)
      exact ⟨s, hs⟩
  let e := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv
  have hsimple := (CFSG.LinearGroups.linear_projective_simple (n := m + 1)
    (K := GaloisField q.p q.exponent) (by omega) hfour).2.1
  have hperf := (CFSG.LinearGroups.linear_projective_perfect (n := m + 1)
    (K := GaloisField q.p q.exponent) (by omega) hfour).commutator_eq_top
  have hinjP := conj_injective_of_simple_perfect hperf
  have hchar : ringChar (GaloisField q.p q.exponent) = q.p := ringChar.eq _ _
  have hpF : (p : GaloisField q.p q.exponent) ≠ 0 := by
    intro h0
    have hdvd : q.p ∣ p := (CharP.cast_eq_zero_iff (GaloisField q.p q.exponent) q.p p).1 h0
    exact hpq ((Nat.prime_dvd_prime_iff_eq q.prime_p hp).1 hdvd).symm
  have hZ : ¬ p ∣ Nat.card (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField q.p q.exponent))) := by
    intro hdvd
    have h1 := hdvd.trans (CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (n := m + 1) (by omega)
      (GaloisField q.p q.exponent))
    rw [hcardF] at h1
    exact hlift ⟨h1.trans (Nat.gcd_dvd_right _ _), h1.trans (Nat.gcd_dvd_left _ _)⟩
  refine uniPlaneGen_of_inner_model (r := q.p) (conj_injective_of_mulEquiv e hinjP) e ?_ hE hc hinner
  intro E₁ hE₁ hcard₁
  have h := uniClosure_psl_ab (F := GaloisField q.p q.exponent) hp (by omega) hpF hZ E₁
    (fun x hx y hy => congrArg Subtype.val (hE₁.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hE₁.2 hcard₁
  rwa [hchar] at h

theorem uniSeitzPlanes_inner_linear :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ IsLinearIndex d.1 ∧ CentralPrimeFree p d.1 := by
  rintro ⟨d, hv⟩ p hp _ hpd _ E hE hc ⟨hinner, ⟨m, q, hd⟩, hlift⟩
  subst hd
  have hpd' : p ≠ q.p := by simpa using hpd
  have h := uniPlaneGen_inner_A hv hp hpd' hlift hE hc hinner
  simpa using h

section Congr

variable {K L : Type*} [Group K] [Group L]

theorem uniPlaneClosure_map_congr (e : K ≃* L) (r : ℕ) (E : Subgroup (MulAut K)) :
    uniPlaneClosure r (E.map (MulAut.congr e).toMonoidHom) = (uniPlaneClosure r E).map e.toMonoidHom := by
  unfold uniPlaneClosure
  rw [MonoidHom.map_closure]
  apply le_antisymm
  · refine Subgroup.closure_mono ?_
    rintro l ⟨_, ⟨ε, hε, rfl⟩, hε1, hεl, n, hn⟩
    refine ⟨e.symm l, ⟨ε, hε, ?_, ?_, n, ?_⟩, by simp⟩
    · rintro rfl
      exact hε1 (map_one _)
    · have := congrArg e.symm hεl
      simpa [MulAut.congr_apply] using this
    · apply e.injective
      rw [map_pow, MulEquiv.apply_symm_apply, hn, map_one]
  · refine Subgroup.closure_mono ?_
    rintro _ ⟨k, ⟨ε, hε, hε1, hεk, n, hn⟩, rfl⟩
    refine ⟨(MulAut.congr e).toMonoidHom ε, ⟨ε, hε, rfl⟩, ?_, ?_, n, ?_⟩
    · intro h
      exact hε1 ((MulAut.congr e).map_eq_one_iff.mp h)
    · simp [MulAut.congr_apply, hεk]
    · simp [← map_pow, hn]

theorem uniPlaneGen_map_congr (e : K ≃* L) (r : ℕ) (E : Subgroup (MulAut K)) :
    UniPlaneGen r (E.map (MulAut.congr e).toMonoidHom) ↔ UniPlaneGen r E := by
  unfold UniPlaneGen
  rw [uniPlaneClosure_map_congr]
  constructor
  · intro h
    have := congrArg (Subgroup.comap e.toMonoidHom) h
    rwa [Subgroup.comap_map_eq_self_of_injective e.injective, Subgroup.comap_top] at this
  · intro h
    rw [h, Subgroup.map_top_of_surjective _ e.surjective]

end Congr

section LinearOuter

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne.CTP
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

variable {n : ℕ} {K : Type} [Field K]

theorem transvection_pow_ringChar {i j : Fin n} (hij : i ≠ j) (c : K) :
    SpecialLinearGroup.transvection hij c ^ ringChar K = 1 := by
  have h : ∀ m : ℕ, SpecialLinearGroup.transvection hij c ^ m =
      SpecialLinearGroup.transvection hij ((m : K) * c) := by
    intro m
    induction m with
    | zero => simp [SpecialLinearGroup.transvection_coeff_zero]
    | succ m ih =>
      rw [pow_succ, ih, ← SpecialLinearGroup.transvection_add]
      congr 1
      push_cast
      ring
  rw [h, ringChar.Nat.cast_ringChar, zero_mul, SpecialLinearGroup.transvection_coeff_zero]

theorem slSub_le_closure_transvection (k : Subfield K) :
    slSub n k ≤ Subgroup.closure {g : SpecialLinearGroup (Fin n) K |
      ∃ (i j : Fin n) (hij : i ≠ j) (c : K), c ∈ k ∧ g = SpecialLinearGroup.transvection hij c} := by
  rintro _ ⟨h, rfl⟩
  have hh : h ∈ Subgroup.closure (Set.range (TransvectionStruct.toSpecialLinearGroup :
      TransvectionStruct (Fin n) k → SpecialLinearGroup (Fin n) k)) := by
    rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
    exact Subgroup.mem_top h
  have hmap := Subgroup.mem_map_of_mem (SpecialLinearGroup.map k.subtype) hh
  rw [MonoidHom.map_closure] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
  refine ⟨t.i, t.j, t.hij, (t.c : K), t.c.2, ?_⟩
  rw [TransvectionStruct.toSpecialLinearGroup_def, Matrix.SpecialLinearGroup.map_transvection]
  rfl

theorem slSub_le_comap_uniPlaneClosure_gl {k : Subfield K} (σ : K ≃+* K)
    (hk : ∀ x, x ∈ k ↔ σ x = x) {E : Subgroup (MulAut (projectiveSL n K))}
    (hσE : fieldAut n K σ ∈ E) (hσout : ∀ B : GL (Fin n) K, fieldAut n K σ ≠ conjAut n K B)
    {G : GL (Fin n) K} (hGE : conjAut n K G ∈ E) (M : GL (Fin n) K)
    (hGM : (G : Matrix (Fin n) (Fin n) K) * (M : Matrix (Fin n) (Fin n) K).map σ = M) :
    slSub n k ≤ (uniPlaneClosure (ringChar K) E).comap (proj n K) ∧
      ∀ B ∈ slSub n k, slConjugation n K M B ∈ (uniPlaneClosure (ringChar K) E).comap (proj n K) := by
  set α : MulAut (projectiveSL n K) := conjAut n K G * fieldAut n K σ with hα
  have hαE : α ∈ E := E.mul_mem hGE hσE
  have hf1 : fieldAut n K σ ≠ 1 := fun h => hσout 1 (by rw [h, map_one])
  have hα1 : α ≠ 1 := by
    intro h
    apply hσout G⁻¹
    have h1 : fieldAut n K σ = (conjAut n K G)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1, map_inv]
  have hfixB : ∀ B ∈ slSub n k, fieldAut n K σ (proj n K B) = proj n K B := by
    intro B hB
    rw [fieldAut_proj]
    congr 1
    apply Subtype.ext
    ext i j
    simp [SpecialLinearGroup.map_apply_coe, (hk _).mp ((mem_slSub.mp hB) i j)]
  have hGM' : G * GeneralLinearGroup.map (σ : K →+* K) M = M := Units.ext (by simpa using hGM)
  have hfixM : ∀ B ∈ slSub n k, α (conjAut n K M (proj n K B)) = conjAut n K M (proj n K B) := by
    intro B hB
    calc α (conjAut n K M (proj n K B))
        = conjAut n K G (fieldAut n K σ (conjAut n K M (proj n K B))) := rfl
      _ = conjAut n K G (conjAut n K (GeneralLinearGroup.map (σ : K →+* K) M)
            (proj n K B)) := by rw [fieldAut_conjAut_apply, hfixB B hB]
      _ = conjAut n K (G * GeneralLinearGroup.map (σ : K →+* K) M) (proj n K B) := by
          rw [map_mul]; rfl
      _ = conjAut n K M (proj n K B) := by rw [hGM']
  set T : Set (SpecialLinearGroup (Fin n) K) := {g | ∃ (i j : Fin n) (hij : i ≠ j) (c : K), c ∈ k ∧
    g = SpecialLinearGroup.transvection hij c} with hT
  have hTk : ∀ g ∈ T, g ∈ slSub n k := by
    rintro _ ⟨i, j, hij, c, hc, rfl⟩
    exact transvection_mem_slSub hij hc
  have hTr : ∀ g ∈ T, g ^ ringChar K = 1 := by
    rintro _ ⟨i, j, hij, c, -, rfl⟩
    exact transvection_pow_ringChar hij c
  refine ⟨(slSub_le_closure_transvection k).trans ((Subgroup.closure_le _).2 fun g hg => ?_),
    fun B hB => ?_⟩
  · rw [SetLike.mem_coe, Subgroup.mem_comap]
    exact mem_uniPlaneClosure hσE hf1 (hfixB g (hTk g hg)) (n := 1)
      (by rw [pow_one, ← map_pow, hTr g hg, map_one])
  · have hle : (slSub n k).map (slConjugation n K M).toMonoidHom ≤
        (uniPlaneClosure (ringChar K) E).comap (proj n K) := by
      refine (Subgroup.map_mono (slSub_le_closure_transvection k)).trans ?_
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨g, hg, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, ← conjAut_proj]
      refine mem_uniPlaneClosure hαE hα1 (hfixM g (hTk g hg)) (n := 1) ?_
      rw [pow_one, ← map_pow, ← map_pow, hTr g hg, map_one, map_one]
    exact hle ⟨B, hB, rfl⟩

theorem uniPlaneGen_of_comap_eq_top {r : ℕ} {E : Subgroup (MulAut (projectiveSL n K))}
    (h : (uniPlaneClosure r E).comap (proj n K) = ⊤) : UniPlaneGen r E := by
  rw [UniPlaneGen, eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := proj_surjective n K x
  have hy : y ∈ (uniPlaneClosure r E).comap (proj n K) := h ▸ Subgroup.mem_top y
  exact hy

theorem uniPlaneGen_of_unit_pair {k : Subfield K} (σ : K ≃+* K) (hk : ∀ x, x ∈ k ↔ σ x = x)
    (hpair : ∀ M : GL (Fin n) K,
      (slSub n k).map (slConjugation n K M).toMonoidHom ≠ slSub n k →
        Subgroup.closure ((slSub n k : Set (SpecialLinearGroup (Fin n) K)) ∪
          ((slSub n k).map (slConjugation n K M).toMonoidHom :
            Set (SpecialLinearGroup (Fin n) K))) = ⊤)
    {E : Subgroup (MulAut (projectiveSL n K))} (hσE : fieldAut n K σ ∈ E)
    (hσout : ∀ B : GL (Fin n) K, fieldAut n K σ ≠ conjAut n K B)
    {G : GL (Fin n) K} (hGE : conjAut n K G ∈ E)
    (hG : ∀ c : K, (G : Matrix (Fin n) (Fin n) K) ≠ c • 1) {M : GL (Fin n) K}
    (hGM : (G : Matrix (Fin n) (Fin n) K) * (M : Matrix (Fin n) (Fin n) K).map σ = M) :
    UniPlaneGen (ringChar K) E := by
  obtain ⟨hkH, hMH⟩ := slSub_le_comap_uniPlaneClosure_gl σ hk hσE hσout hGE M hGM
  have hclos := hpair M (slConjugation_map_ne_of_unit σ hk G hG M hGM)
  refine uniPlaneGen_of_comap_eq_top (eq_top_iff.mpr ?_)
  rw [← hclos, Subgroup.closure_le]
  rintro x (hx | ⟨B, hB, rfl⟩)
  · exact hkH hx
  · exact hMH B hB

theorem uniPlaneGen_of_field_outer [Finite K] {ℓ f p : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hn : 3 ≤ n) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) {E : Subgroup (MulAut (projectiveSL n K))}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2) (hout : ¬ E ≤ linearAutGroup n K) :
    UniPlaneGen (ringChar K) E := by
  classical
  obtain ⟨h, σ, x, c, hσ, hKk, hσout, hσE, hxE, hxσ, hxns, hxp, hcσ⟩ :=
    exists_field_normal_form hℓ hf hn hK hp hp2 hpℓ hE hc hout
  set k : Subfield K := semilinearFixedSubfield σ with hkdef
  have hk : ∀ y, y ∈ k ↔ σ y = y := fun y => Iff.rfl
  have hn0 : 0 < n := by omega
  have hc0 : c ≠ 0 :=
    ne_zero_of_gl_coe_eq_smul hn0 (G := x ^ p) (a := c) (by
      rw [Units.val_pow_eq_pow_val]
      exact hxp)
  obtain ⟨μ, hμ⟩ := CFSG.ABGLocalTools.exists_prod_pow_eq σ (c := c⁻¹) (by rw [map_inv₀, hcσ])
  rw [hσ] at hμ
  have hμ0 : μ ≠ 0 := by
    intro h0
    have h1 : ∏ i ∈ Finset.range p, (σ ^ i) μ = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr hp.pos) (by simp [h0])
    rw [hμ] at h1
    exact inv_ne_zero hc0 h1
  obtain ⟨M₀, hdet, hM₀⟩ := exists_fixed_matrix_smul hp hℓ hf hK σ hσ hxσ hxp
    (by rw [hμ]; exact inv_mul_cancel₀ hc0)
  let M : GL (Fin n) K := Matrix.nonsingInvUnit M₀ hdet
  let G : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) (Units.mk0 μ hμ0) * x
  have hGcoe : (G : Matrix (Fin n) (Fin n) K) = μ • (x : Matrix (Fin n) (Fin n) K) := by
    rw [Units.val_mul, scalarGL_coe_eq_smul, Matrix.smul_mul, Matrix.one_mul]
    rfl
  have hGE : conjAut n K G ∈ E.map (MulAut.congr h⁻¹).toMonoidHom := by
    rw [map_mul, conjAut_scalar, one_mul]
    exact hxE
  have hGns : ∀ a : K, (G : Matrix (Fin n) (Fin n) K) ≠ a • 1 := by
    intro a ha
    apply hxns (μ⁻¹ * a)
    rw [hGcoe] at ha
    have h1 := congrArg (fun Z => μ⁻¹ • Z) ha
    simpa [smul_smul, hμ0] using h1
  have hGM : (G : Matrix (Fin n) (Fin n) K) * (M : Matrix (Fin n) (Fin n) K).map σ = M := by
    rw [hGcoe]
    exact hM₀
  have hpl : UniPlaneGen (ringChar K) (E.map (MulAut.congr h⁻¹).toMonoidHom) :=
    uniPlaneGen_of_unit_pair σ hk (fun M' hne => pairSL_closure hp hp2 hKk hn M' hne) hσE hσout hGE
      hGns hGM
  exact (uniPlaneGen_map_congr h⁻¹ _ E).1 hpl

theorem uniPlaneGen_outer_A {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) (hm : 2 ≤ m) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p) (hlift : ¬ (p ∣ q.card - 1 ∧ p ∣ m + 1))
    {E : Subgroup (MulAut (Cat ⟨.A m q, hv⟩))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hout : ¬ InnerPlane ⟨.A m q, hv⟩ p E) : UniPlaneGen q.p E := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let e : Cat ⟨.A m q, hv⟩ ≃* projectiveSL (m + 1) (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _)
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have hcop : Nat.Coprime p (Nat.gcd (m + 1) (Nat.card (GaloisField q.p q.exponent) - 1)) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => hlift ⟨?_, ?_⟩
    · rw [← hcardF]
      exact hd.trans (Nat.gcd_dvd_right _ _)
    · exact hd.trans (Nat.gcd_dvd_left _ _)
  have hchar : ringChar (GaloisField q.p q.exponent) = q.p := ringChar.eq _ _
  set E' := E.map (MulAut.congr e).toMonoidHom with hE'
  have hE'el : IsElemAbelian p E' := isElemAbelian_map_congr e hE
  have hE'c : Nat.card E' = p ^ 2 := (card_map_congr e E).trans hc
  have hE'out : ¬ E' ≤ (MulAut.conj : projectiveSL (m + 1) (GaloisField q.p q.exponent) →*
      MulAut (projectiveSL (m + 1) (GaloisField q.p q.exponent))).range :=
    not_le_range_conj_map_congr e hout
  have hD : ¬ E' ≤ linearAutGroup (m + 1) (GaloisField q.p q.exponent) := by
    intro hle
    apply hE'out
    intro a ha
    exact CFSG.RankThree.PartOne.KCLinPlane.inner_of_mem_linearAut_of_pow_eq_one (by omega)
      hcop (hle ha) (hE'el.2 a ha)
  have h := uniPlaneGen_of_field_outer q.prime_p q.exponent_pos (by omega) hKq hp hp2 hpq hE'el hE'c hD
  rw [hchar] at h
  exact (uniPlaneGen_map_congr e _ E).1 h

theorem uniSeitzPlanes_outer_linear :
    UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ (∃ (m : ℕ) (q : TauCeti.PrimePower), d.1 = .A m q ∧
      2 ≤ m) ∧ CentralPrimeFree p d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hout, ⟨m, q, hd, hm⟩, hlift⟩
  subst hd
  have hpd' : p ≠ q.p := by simpa using hpd
  have h := uniPlaneGen_outer_A hv hm hp hp2 hpd' hlift hE hc hout
  simpa using h

end LinearOuter

section LinearTwoOuter

open CFSG.RankThree.PartOne.CTP
open CFSG.GorensteinWalter (PSL2 psl2FieldAut)
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent (fixedSubfield)

theorem closure_pow_ringChar_eq_top_psl (n : ℕ) (K : Type) [Field K] :
    Subgroup.closure {x : Matrix.ProjectiveSpecialLinearGroup (Fin n) K | x ^ ringChar K = 1} = ⊤ := by
  have h := Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin n)
    (K := K)
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K)) x
  have hg : g ∈ Subgroup.closure (Set.range (TransvectionStruct.toSpecialLinearGroup :
      TransvectionStruct (Fin n) K → Matrix.SpecialLinearGroup (Fin n) K)) := by
    rw [h]
    exact Subgroup.mem_top g
  have hmap := Subgroup.mem_map_of_mem
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))) hg
  rw [MonoidHom.map_closure] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
  show (QuotientGroup.mk' _ t.toSpecialLinearGroup) ^ ringChar K = 1
  rw [← map_pow, TransvectionStruct.toSpecialLinearGroup_def, transvection_pow_ringChar, map_one]

theorem fixedSubgroup_le_closure_psl2 {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {σ : MulAut (PSL2 F)} (hσ : IsOuterOfOrder p σ) :
    fixedSubgroup σ ≤ Subgroup.closure {x | σ x = x ∧ x ^ ringChar F = 1} := by
  obtain ⟨τ, β, hτ, rfl⟩ := exists_conj_fieldAut hp hodd hσ
  obtain ⟨φ⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.nonempty_mulEquiv_fixed_psl2FieldAut hodd hτ
  have hchar : ringChar (fixedSubfield F τ) = ringChar F := by
    have : CharP (fixedSubfield F τ) (ringChar F) := inferInstance
    exact ringChar.eq _ _
  rw [fixedSubgroup_eq_signalizer, signalizerFixedSubgroup_conj]
  rintro _ ⟨y, hy, rfl⟩
  have hz : φ ⟨y, hy⟩ ∈ Subgroup.closure {z : PSL2 (fixedSubfield F τ) |
      z ^ ringChar (fixedSubfield F τ) = 1} := by
    rw [closure_pow_ringChar_eq_top_psl]
    exact Subgroup.mem_top _
  have h1 : (⟨y, hy⟩ : ↥(signalizerFixedSubgroup (psl2FieldAut F τ))) ∈
      (Subgroup.closure {z : PSL2 (fixedSubfield F τ) | z ^ ringChar (fixedSubfield F τ) = 1}).map
        φ.symm.toMonoidHom := ⟨_, hz, by simp⟩
  rw [MonoidHom.map_closure] at h1
  have h2 := Subgroup.mem_map_of_mem
    (β.toMonoidHom.comp (signalizerFixedSubgroup (psl2FieldAut F τ)).subtype) h1
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  have hw : psl2FieldAut F τ ((φ.symm z : ↥(signalizerFixedSubgroup (psl2FieldAut F τ))) : PSL2 F) =
      ((φ.symm z : ↥(signalizerFixedSubgroup (psl2FieldAut F τ))) : PSL2 F) := (φ.symm z).2
  refine ⟨?_, ?_⟩
  · simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hw]
  · have hz' : z ^ ringChar F = 1 := by rw [← hchar]; exact hz
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
    rw [← map_pow, ← Subgroup.coe_pow, ← map_pow, hz', map_one, Subgroup.coe_one, map_one]

theorem uniPlaneGen_of_fieldAutData {K : Type} [Group K] [IsSimpleGroup K] (hnab : ∃ a b : K, a * b ≠ b * a)
    {p r : ℕ} (hp : p.Prime) (hd : FieldAutData K p)
    (hfix : ∀ τ : MulAut K, IsOuterOfOrder p τ →
      fixedSubgroup τ ≤ Subgroup.closure {x | τ x = x ∧ x ^ r = 1})
    (E : Subgroup (MulAut K)) [hE : CFSG.IsElementaryAbelian p E] (hEc : Nat.card E = p ^ 2)
    (hout : ¬ ∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g) : UniPlaneGen r E := by
  have : Fact p.Prime := ⟨hp⟩
  have hinj := conj_injective_of_simple hnab
  obtain ⟨k, hk1, hkE⟩ := hd.out_rank E hE hEc
  push Not at hout
  obtain ⟨σ, hσE, hσinn⟩ := hout
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hσ1 : σ ≠ 1 := fun h => hσinn 1 (by rw [h, map_one])
  have hσp : σ ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian σ hσE
  have hσo : IsOuterOfOrder p σ := ⟨orderOf_eq_prime hσp hσ1, hσinn⟩
  have hkp : k ^ p = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian _ hkE
  have hcomm : σ * MulAut.conj k = MulAut.conj k * σ := hcommE σ hσE _ hkE
  have hστE : σ * MulAut.conj k ∈ E := E.mul_mem hσE hkE
  have hστ1 : σ * MulAut.conj k ≠ 1 := by
    intro h
    apply hσinn k⁻¹
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_left h
  have hστp : (σ * MulAut.conj k) ^ p = 1 := by
    rw [(show Commute σ (MulAut.conj k) from hcomm).mul_pow, hσp, ← map_pow, hkp, map_one, one_mul]
  have hστo : IsOuterOfOrder p (σ * MulAut.conj k) := by
    refine ⟨orderOf_eq_prime hστp hστ1, fun g h => hσinn (g * k⁻¹) ?_⟩
    rw [map_mul, map_inv, ← h, mul_assoc, mul_inv_cancel, mul_one]
  have hσk : σ k = k := apply_eq_of_commute_conj hinj hcomm
  have hkP : k ∈ fixedSubgroup σ := hσk
  have hpdvd : p ∣ Nat.card (fixedSubgroup σ) := by
    have hord : orderOf k = p := (orderOf_eq_prime hkp hk1 : orderOf k = p)
    have h1 : orderOf (⟨k, hkP⟩ : fixedSubgroup σ) ∣ Nat.card (fixedSubgroup σ) :=
      orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, hord] at h1
  have hne : fixedSubgroup σ ≠ fixedSubgroup (σ * MulAut.conj k) := by
    intro heq
    apply hk1
    refine hd.center σ hσo hpdvd k hkP fun y hy => ?_
    have hy' : y ∈ fixedSubgroup (σ * MulAut.conj k) := heq ▸ hy
    have h1 : σ y = y := hy
    have h2 : (σ * MulAut.conj k) y = y := hy'
    have h3 : σ (k * y * k⁻¹) = k * y * k⁻¹ := by
      rw [map_mul, map_mul, map_inv, hσk, h1]
    have h4 : σ (k * y * k⁻¹) = y := by
      simpa [MulAut.mul_apply, MulAut.conj_apply] using h2
    rw [h4] at h3
    calc k * y = k * y * k⁻¹ * k := by group
      _ = y * k := by rw [← h3]
  rcases hd.gen σ _ hσo hστo hne with hg | hsmall
  · rw [UniPlaneGen, eq_top_iff, ← hg, Subgroup.closure_le]
    rintro x (hx | hx)
    · refine ((Subgroup.closure_le _).2 ?_) (hfix σ hσo hx)
      rintro y ⟨hy, hyr⟩
      exact mem_uniPlaneClosure hσE hσ1 hy (n := 1) (by rw [pow_one]; exact hyr)
    · refine ((Subgroup.closure_le _).2 ?_) (hfix _ hστo hx)
      rintro y ⟨hy, hyr⟩
      exact mem_uniPlaneClosure hστE hστ1 hy (n := 1) (by rw [pow_one]; exact hyr)
  · exact absurd hpdvd hsmall

theorem uniPlaneGen_outer_A1 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) (hq2 : q.p ≠ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut (Cat ⟨.A 1 q, hv⟩))} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hout : ¬ InnerPlane ⟨.A 1 q, hv⟩ p E) : UniPlaneGen q.p E := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Fact p.Prime := ⟨hp⟩
  let e : Cat ⟨.A 1 q, hv⟩ ≃* PSL2 (GaloisField q.p q.exponent) :=
    CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have h4 : 4 ≤ q.card := hrange.2 rfl
  have hfour : 3 ≤ 2 ∨ ∃ s : Finset (GaloisField q.p q.exponent), s.card = 4 := by
    right
    have : Fintype (GaloisField q.p q.exponent) := Fintype.ofFinite _
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ :
      Finset (GaloisField q.p q.exponent))) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcardF]; exact h4)
    exact ⟨s, hs⟩
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (n := 2)
    (K := GaloisField q.p q.exponent) le_rfl hfour
  have hperf := (CFSG.LinearGroups.linear_projective_perfect (n := 2)
    (K := GaloisField q.p q.exponent) le_rfl hfour).commutator_eq_top
  have hnab : ∃ a b : PSL2 (GaloisField q.p q.exponent), a * b ≠ b * a :=
    exists_noncomm_of_perfect hperf
  have hchar : ringChar (GaloisField q.p q.exponent) = q.p := ringChar.eq _ _
  have hd : FieldAutData (PSL2 (GaloisField q.p q.exponent)) p :=
    fieldAutData_psl2_odd_prime hp hp2 (by rw [hchar]; exact hq2)
  have hEi : CFSG.IsElementaryAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
    rw [card_map_congr, hc]
  have hout' : ¬ ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h
    exact not_le_range_conj_map_congr e hout fun φ hφ => (h φ hφ).imp fun g hg => hg.symm
  have h := uniPlaneGen_of_fieldAutData hnab hp hd
    (fun τ hτ => fixedSubgroup_le_closure_psl2 hp (hp.odd_of_ne_two hp2) hτ)
    (E.map (MulAut.congr e).toMonoidHom) hc' hout'
  rw [hchar] at h
  exact (uniPlaneGen_map_congr e _ E).1 h

theorem uniSeitzPlanes_outer_A1 :
    UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ (∃ q, d.1 = .A 1 q) ∧ d.1.characteristic ≠ 2 := by
  rintro ⟨d, hv⟩ p hp hp2 _ _ E hE hc ⟨hout, ⟨q, hd⟩, hq2⟩
  subst hd
  have hq2' : q.p ≠ 2 := by simpa using hq2
  have h := uniPlaneGen_outer_A1 hv hq2' hp hp2 hE hc hout
  simpa using h

end LinearTwoOuter

section LinearK

variable {G : Type} [Group G] [Finite G]

theorem uniSeitzPlanes_linear :
    UniSeitzPlanes fun d p _ => IsLinearIndex d.1 ∧ d.1.characteristic ≠ 2 ∧ CentralPrimeFree p d.1 := by
  have h₂ : UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ IsLinearIndex d.1 ∧
      d.1.characteristic ≠ 2 ∧ CentralPrimeFree p d.1 :=
    UniSeitzPlanes.of_cover (fun d p _ _ E ⟨hi, ⟨m, q, hd⟩, hc2, hc⟩ => by
      rcases (show m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with rfl | rfl | hm
      · exfalso
        have hv := d.2
        rw [hd] at hv
        have := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
        omega
      · exact Or.inr ⟨hi, ⟨q, hd⟩, hc2⟩
      · exact Or.inl ⟨hi, ⟨m, q, hd, hm⟩, hc⟩) uniSeitzPlanes_outer_linear uniSeitzPlanes_outer_A1
  exact UniSeitzPlanes.of_cover (fun d p _ _ E hE => by
    by_cases hi : InnerPlane d p E
    · exact Or.inl ⟨hi, hE.1, hE.2.2⟩
    · exact Or.inr ⟨hi, hE⟩) uniSeitzPlanes_inner_linear h₂

end LinearK

section ExcParabolic

set_option linter.unusedSectionVars false

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge

theorem conj_injective_cat_untwisted {τ : Tag} {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : Even.UntwistedBridgeAll τ c) (q : TauCeti.PrimePower) (hv : (c q).Valid) :
    Function.Injective (MulAut.conj : Cat ⟨c q, hv⟩ →* MulAut (Cat ⟨c q, hv⟩)) := by
  obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup hB q hv
  exact conj_injective_of_mulEquiv e
    (conj_injective_of_center_eq_bot (center_adjointGroup_eq_bot (τ := τ) (K := K)))

theorem conj_injective_cat_twisted (t : TwistTag) {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : Even.TwistedBridgeAll t c) (q : TauCeti.PrimePower) (hv : (c q).Valid) :
    Function.Injective (MulAut.conj : Cat ⟨c q, hv⟩ →* MulAut (Cat ⟨c q, hv⟩)) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨K, _, _, hK, hKchar⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (q.p ^ q.exponent) ^ t.order ∧ CharP K q.p :=
    ⟨GaloisField q.p (q.exponent * t.order), inferInstance, inferInstance, by
      rw [GaloisField.card _ _ (Nat.mul_pos q.exponent_pos t.order_pos).ne', pow_mul],
      inferInstance⟩
  obtain ⟨σ, hσ, -, -⟩ := finite_graph_field_parameter_fields t q.prime_p q.exponent_pos K hK
  have hσ'' : ∀ x, σ.toRingHom x = x ^ (q.p ^ q.exponent) := fun x => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ]
  have hσ' : ∀ x, σ.toRingHom x = x ^ q.card := fun x => by
    rw [TauCeti.PrimePower.card_def]
    exact hσ'' x
  obtain ⟨φ⟩ := hB q hv K (by rw [TauCeti.PrimePower.card_def]; exact hK) σ.toRingHom hσ'
  have hperf := finite_fixed_root_group_perfect t q.prime_p q.exponent_pos K hK σ.toRingHom hσ''
  have hZ : Subgroup.center ↥(graphFixedRootGroup t K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  obtain ⟨ψ⟩ := nonempty_derivedCentralQuotient_equiv _ _ hperf.2.2.1 hZ
  exact conj_injective_of_mulEquiv (φ.symm.trans ψ) (conj_injective_of_center_eq_bot hZ)

theorem conj_injective_cat_of_chevalleyExc {d : TauCeti.ValidLieTypeIndex} (hd : IsChevalleyExcIndex d.1) :
    Function.Injective (MulAut.conj : Cat d →* MulAut (Cat d)) := by
  obtain ⟨d, hv⟩ := d
  rcases hd with ((⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩) | (⟨q, rfl⟩ | ⟨q, rfl⟩))
  · exact conj_injective_cat_untwisted Even.chevalleyBridgesAll.g2 q hv
  · exact conj_injective_cat_untwisted Even.chevalleyBridgesAll.f4 q hv
  · exact conj_injective_cat_untwisted Even.chevalleyBridgesAll.e6 q hv
  · exact conj_injective_cat_untwisted Even.chevalleyBridgesAll.e7 q hv
  · exact conj_injective_cat_untwisted Even.chevalleyBridgesAll.e8 q hv
  · exact conj_injective_cat_twisted .D4 Even.chevalleyBridgesAll.trialityD4 q hv
  · exact conj_injective_cat_twisted .E6 Even.chevalleyBridgesAll.twistedE6 q hv

theorem uniSeitzPlanes_excParabolic :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ IsChevalleyExcIndex d.1 ∧ NormalizesRSubgroup d E := by
  rintro d p hp _ hpd _ E hE hc ⟨hin, hd, R, hR1, hRp, hRn⟩
  have hinj := conj_injective_cat_of_chevalleyExc hd
  set E₀ : Subgroup (Cat d) := E.comap (MulAut.conj : Cat d →* MulAut (Cat d)) with hE₀
  have hmap : E₀.map (MulAut.conj : Cat d →* MulAut (Cat d)) = E := Subgroup.map_comap_eq_self hin
  have hE₀el : IsElemAbelian p E₀ := isElemAbelian_comap_conj hinj hE
  have hE₀card : Nat.card E₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap, hc]
  have hp1 := hp.one_lt
  have hE₀1 : E₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE₀card
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp1
    omega
  have hN : NormalizesRSub d E₀ := ⟨R, hR1, hRp, fun x hx => hRn _ hx⟩
  have h := QuasiHigh.seitzExcParabolicRChevalley d p hp hpd hd E₀ hE₀el hE₀1 hN
  rw [UniPlaneGen, eq_top_iff]
  refine h.trans ((Subgroup.closure_le _).2 ?_)
  rintro x ⟨-, ⟨n, hn⟩, B, hBE, hBi, hxB⟩
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hB : B = ⊥ := (Subgroup.eq_bot_iff_forall B).2 hcon
    rw [hB, Subgroup.relIndex_bot_left, hE₀card] at hBi
    have : p < p ^ 2 := by nlinarith
    omega
  refine mem_uniPlaneClosure (e := MulAut.conj b) (hBE hbB) ?_ ?_ hn
  · intro h1
    exact hb1 (hinj (by rw [h1, map_one]))
  · rw [MulAut.conj_apply, Subgroup.mem_centralizer_iff.1 hxB b hbB, mul_inv_cancel_right]

end ExcParabolic

@[expose] def OddCpfRest (d : TauCeti.ValidLieTypeIndex) (p : ℕ) (E : Subgroup (MulAut (Cat d))) : Prop :=
  OddCpf d p E ∧ ¬ IsLinearIndex d.1 ∧
    ¬ (InnerPlane d p E ∧ IsChevalleyExcIndex d.1 ∧ NormalizesRSubgroup d E)

section Assembly

set_option linter.unusedSectionVars false

theorem uniSeitzPlanes_oddCpf_of_rest (h : UniSeitzPlanes OddCpfRest) : UniSeitzPlanes OddCpf := by
  have h₂ : UniSeitzPlanes fun d p E => OddCpf d p E ∧ ¬ IsLinearIndex d.1 :=
    UniSeitzPlanes.of_cover (fun d p _ _ E hE => by
      by_cases hx : InnerPlane d p E ∧ IsChevalleyExcIndex d.1 ∧ NormalizesRSubgroup d E
      · exact Or.inl hx
      · exact Or.inr ⟨hE.1, hE.2, hx⟩) uniSeitzPlanes_excParabolic h
  exact UniSeitzPlanes.of_cover (fun d p _ _ E hE => by
    by_cases hl : IsLinearIndex d.1
    · exact Or.inl ⟨hl, hE.1, hE.2⟩
    · exact Or.inr ⟨hE, hl⟩) uniSeitzPlanes_linear h₂

theorem input23_11Thm4_of_uniRest (hU : UniSeitzPlanes OddCpfRest) (hR : Input23_11Thm4Rest) :
    Inputs2311.Input23_11Thm4 :=
  input23_11Thm4_of_uni (uniSeitzPlanes_oddCpf_of_rest hU) hR

theorem input23_11Bar_of_uniRest (hU : UniSeitzPlanes OddCpfRest) (hR : Input23_11Thm4Rest)
    (hs : Inputs2311.Input14_2Struct) : Inputs2311.Input23_11Bar :=
  Inputs2311.input23_11Bar_of_thm4 (input23_11Thm4_of_uniRest hU hR) hs

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
