module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseANaturalCoord
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesInternal

public section

open scoped MatrixGroups commutatorElement Pointwise

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open CFSG.QuasithinUnique.Setup.SL2Modules

namespace CaseAAux

section Generic

open Subgroup

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] [CharP E 2]

theorem fin_two_eq_zero_or_one (s : Fin 2) : s = 0 ∨ s = 1 := by
  fin_cases s <;> simp

theorem tensorRep_pair_fixed {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ) {a b : ι}
    (hab : a ≠ b) (hall : ∀ c, c = a ∨ c = b) (g : SL(2, F))
    (hg : twistMat E (e a) g = twistMat E (e b) g) :
    tensorRep F E e g (fun x => if x a = x b then 0 else 1) =
      (fun x => if x a = x b then 0 else 1) := by
  funext x'
  rw [tensorRep_apply]
  set x₀₁ : ι → Fin 2 := fun c => if c = a then 0 else 1 with hx₀₁
  set x₁₀ : ι → Fin 2 := fun c => if c = a then 1 else 0 with hx₁₀
  have hba : b ≠ a := hab.symm
  have h01a : x₀₁ a = 0 := by simp [hx₀₁]
  have h01b : x₀₁ b = 1 := by simp [hx₀₁, hba]
  have h10a : x₁₀ a = 1 := by simp [hx₁₀]
  have h10b : x₁₀ b = 0 := by simp [hx₁₀, hba]
  have hne : x₀₁ ≠ x₁₀ := fun h => by
    have := congrFun h a
    rw [h01a, h10a] at this
    exact absurd this (by decide)
  have hprod : ∀ x : ι → Fin 2, tmatE E e g x' x =
      twistMat E (e a) g (x' a) (x a) * twistMat E (e b) g (x' b) (x b) := fun x =>
    Fintype.prod_eq_mul a b hab (fun c hc => by
      rcases hall c with h | h
      · exact absurd h hc.1
      · exact absurd h hc.2)
  rw [Fintype.sum_eq_add x₀₁ x₁₀ hne]
  · rw [hprod, hprod, h01a, h01b, h10a, h10b, ← hg]
    simp only [show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide, ite_false,
      mul_one]
    set M := twistMat E (e a) g
    have hdet := twistMat_det (k := E) (e a) g
    rcases fin_two_eq_zero_or_one (x' a) with h1 | h1 <;>
      rcases fin_two_eq_zero_or_one (x' b) with h2 | h2 <;>
      rw [h1, h2]
    · simp only [ite_true]
      rw [mul_comm (M 0 1) (M 0 0)]
      exact CharTwo.add_self_eq_zero _
    · simp only [show (0 : Fin 2) ≠ 1 by decide, ite_false]
      linear_combination hdet
    · simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false]
      linear_combination hdet
    · simp only [ite_true]
      rw [mul_comm (M 1 1) (M 1 0)]
      exact CharTwo.add_self_eq_zero _
  · intro x hx
    by_cases hxe : x a = x b
    · simp [hxe]
    · exfalso
      rcases fin_two_eq_zero_or_one (x a) with h1 | h1
      · have h2 : x b = 1 := by
          rcases fin_two_eq_zero_or_one (x b) with h2 | h2
          · exact absurd (h1.trans h2.symm) hxe
          · exact h2
        refine hx.1 (funext fun c => ?_)
        rcases hall c with rfl | rfl
        · rw [h1, h01a]
        · rw [h2, h01b]
      · have h2 : x b = 0 := by
          rcases fin_two_eq_zero_or_one (x b) with h2 | h2
          · exact h2
          · exact absurd (h1.trans h2.symm) hxe
        refine hx.2 (funext fun c => ?_)
        rcases hall c with rfl | rfl
        · rw [h1, h10a]
        · rw [h2, h10b]


omit [CharP E 2] in
theorem twistMat_add_of_fixed [CharP E 2] {f : ℕ} (g : SL(2, F))
    (hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) F) i j ^ 2 ^ f = g i j) (i : ℕ) :
    twistMat E (i + f) g = twistMat E i g := by
  ext a c
  rw [twistMat_apply, twistMat_apply, pow_add, mul_comm, pow_mul, ← map_pow, hg]

theorem natural_of_fixedPointFree {f : ℕ} (hf : 1 ≤ f) {F : Type*} [Field F] [Fintype F]
    (hF : Fintype.card F = 2 ^ (2 * f)) {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (ρ : Representation (ZMod 2) SL(2, F) W) (hirr : ρ.IsIrreducible)
    (hnt : ∃ g, ρ g ≠ 1) (hW : Nat.card W = (2 ^ (2 * f)) ^ 2) (g : SL(2, F))
    (hgσ : ∀ i j, (g : Matrix (Fin 2) (Fin 2) F) i j ^ 2 ^ f = g i j)
    (hfix : ∀ w, ρ g w = w → w = 0) :
    ∃ φ : W ≃+ (Fin 2 → F),
      ∀ g w, φ (ρ g w) = (g : Matrix (Fin 2) (Fin 2) F).mulVec (φ w) := by
  classical
  have : CharP F 2 := charP_two_of_card_eq hF
  have : Fact ρ.IsIrreducible := ⟨hirr⟩
  obtain ⟨d, hd1, hDcard, hdesc⟩ :=
    binary_SL2_irreducible_Frobenius_descent (by omega : 1 ≤ 2 * f) hF ρ hnt
  have hfinD : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  let b := Module.finBasis (EndRing ρ) W
  obtain ⟨E, hEF, hEfin, hEchar, ιF, ιD, J, hJne, hJn, ⟨Φ⟩, hshift, hdim⟩ := hdesc b
  obtain ⟨r, hr⟩ : ∃ r, J.card = r := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := hr ▸ Finset.card_pos.mpr hJne
  have hWr : Nat.card W = 2 ^ (d * 2 ^ r) := by
    have h1 := natCard_eq_pow_finrank (ρ := ρ)
    rw [hDcard, hdim, ← pow_mul, hr] at h1
    exact h1
  have hdr : d * 2 ^ r = 4 * f := by
    have h1 : (2 : ℕ) ^ (d * 2 ^ r) = 2 ^ (4 * f) := by
      rw [← hWr, hW, ← pow_mul]; ring_nf
    exact Nat.pow_right_injective le_rfl h1
  have hnr : 2 * f ≤ r * d := hr ▸ n_le_card_mul (by omega) (by omega) hJn hJne hshift
  have hr2 : r ≤ 2 := by
    have h2r : 2 ^ r = 2 * 2 ^ (r - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h1 : d * 2 ^ (r - 1) ≤ d * r := by
      have : d * 2 ^ r ≤ 2 * (r * d) := by omega
      rw [h2r] at this
      nlinarith
    exact le_two_of_two_pow_pred_le hr1 (Nat.le_of_mul_le_mul_left h1 (by omega))
  rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
  ·
    have hd : d = 2 * f := by omega
    subst hd
    have hdim2 : Module.finrank (EndRing ρ) W = 2 := by rw [hdim, hr]; rfl
    exact exists_natural_iso (by omega) hF ρ hnt hDcard hdim2
  ·
    exfalso
    have hd : d = f := by omega
    subst hd
    obtain ⟨a, ha⟩ := hJne
    set b' := (a + d) % (2 * d) with hb'
    have hb'J : b' ∈ J := by
      have : b' ∈ J.image (fun i => (i + d) % (2 * d)) := Finset.mem_image_of_mem _ ha
      rwa [hshift] at this
    have ha2 : a < 2 * d := hJn a ha
    have hab : a ≠ b' := by
      intro h
      rw [hb'] at h
      rcases (by omega : a + d < 2 * d ∨ 2 * d ≤ a + d) with h3 | h3
      · rw [Nat.mod_eq_of_lt h3] at h; omega
      · rw [Nat.mod_eq_sub_mod h3, Nat.mod_eq_of_lt (by omega)] at h; omega
    let _ := ιF.toAlgebra
    have htw : twistMat E a g = twistMat E b' g := by
      rw [hb', twistMat_mod hF, twistMat_add_of_fixed g hgσ]
    set ea : ↥J := ⟨a, ha⟩
    set eb : ↥J := ⟨b', hb'J⟩
    have heab : ea ≠ eb := fun h => hab (congrArg Subtype.val h)
    have hall : ∀ c : ↥J, c = ea ∨ c = eb := by
      intro c
      by_contra hc
      push Not at hc
      have h3 : ({ea, eb, c} : Finset ↥J).card ≤ (Finset.univ : Finset ↥J).card :=
        Finset.card_le_univ _
      rw [Finset.card_univ, Fintype.card_coe, hr, Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨heab, fun h => hc.1 h.symm⟩), Finset.card_pair (fun h => hc.2 h.symm)] at h3
      omega
    set v₀ : (↥J → Fin 2) → E := fun x => if x ea = x eb then 0 else 1 with hv₀
    have hv₀fix : frobTensor F E J g v₀ = v₀ :=
      tensorRep_pair_fixed (fun i : ↥J => (i : ℕ)) heab hall g htw
    have hv₀ne : v₀ ≠ 0 := by
      intro h
      have := congrFun h (fun c => if c = ea then 0 else 1)
      simp [hv₀, heab.symm] at this
    have hcount := natCard_fixW_pow ρ b (fun _ : Unit => g) ιF ιD J Φ
    have hW1 : Nat.card {w : W // ∀ _ : Unit, ρ g w = w} = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨0, fun _ => map_zero _⟩, fun w => Subtype.ext (hfix w.1 (w.2 ()))⟩
    rw [hW1, one_pow] at hcount
    have h2 : 1 < Nat.card {y : (↥J → Fin 2) → E // ∀ _ : Unit, frobTensor F E J g y = y} := by
      have : Finite {y : (↥J → Fin 2) → E // ∀ _ : Unit, frobTensor F E J g y = y} :=
        Subtype.finite
      refine Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨⟨0, fun _ => map_zero _⟩,
        ⟨v₀, fun _ => hv₀fix⟩, fun h => hv₀ne (congrArg Subtype.val h).symm⟩⟩
    omega


theorem le_card_of_invariant {n : ℕ} (hn : 2 ≤ n) (hn3 : n ≠ 3) {F : Type*} [Field F]
    [Fintype F] (hF : Fintype.card F = 2 ^ n) {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [Finite M] (ρ : Representation (ZMod 2) SL(2, F) M) (U : Submodule (ZMod 2) M)
    (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) (hnt : ∃ g, ∃ u ∈ U, ρ g u ≠ u) :
    2 ^ (2 * n) ≤ Nat.card U := by
  classical
  have : CharP F 2 := charP_two_of_card_eq hF
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have : IsSimpleGroup SL(2, F) := CFSG.LocalAnalysis.EvenBN.GMSK.sl2_isSimpleGroup h2
    (hF ▸ (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n))
  let e : SL(2, F) → (U ≃+ U) := fun g =>
    { toFun := fun u => ⟨ρ g u, hU g u u.2⟩
      invFun := fun u => ⟨ρ g⁻¹ u, hU g⁻¹ u u.2⟩
      left_inv := fun u => Subtype.ext (by
        change ρ g⁻¹ (ρ g u) = u
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply])
      right_inv := fun u => Subtype.ext (by
        change ρ g (ρ g⁻¹ u) = u
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])
      map_add' := fun u v => Subtype.ext (map_add (ρ g) (u : M) v) }
  let ρU : SL(2, F) →* MulAut (Multiplicative U) :=
    { toFun := fun g => AddEquiv.toMultiplicative (e g)
      map_one' := by
        ext u
        change ρ 1 (Multiplicative.toAdd u : U) = (Multiplicative.toAdd u : U)
        rw [map_one, Module.End.one_apply]
      map_mul' := fun g h => by
        ext u
        change ρ (g * h) (Multiplicative.toAdd u : U) = ρ g (ρ h (Multiplicative.toAdd u : U))
        rw [map_mul, Module.End.mul_apply] }
  have hinj : Function.Injective ρU := by
    rw [← MonoidHom.ker_eq_bot_iff]
    have := MonoidHom.normal_ker ρU
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρU.ker with hk | hk
    · exact hk
    · exfalso
      obtain ⟨g, u, hu, hgu⟩ := hnt
      have hg : g ∈ ρU.ker := hk ▸ Subgroup.mem_top g
      rw [MonoidHom.mem_ker] at hg
      have := congrArg (fun φ : MulAut (Multiplicative U) =>
        ((Multiplicative.toAdd (φ (Multiplicative.ofAdd ⟨u, hu⟩)) : U) : M)) hg
      exact hgu this
  have : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  obtain ⟨dU, hdU⟩ : ∃ dU, Nat.card U = 2 ^ dU := ⟨_, by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U)
    rwa [Nat.card_zmod] at this⟩
  have hX : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ Nat.card SL(2, F) := by
    rw [CFSG.GorensteinWalter.sl2_card_formula, Nat.card_eq_fintype_card, hF]
  have hN : Nat.card (Multiplicative U) = 2 ^ dU := hdU
  have hle := CFSG.CGT.Timmesfeld75.lemma27_psl2 hn hn3 hX ρU hinj hN
  rw [hdU]
  exact Nat.pow_le_pow_right (by norm_num) hle


theorem exists_complement_of_fixedPointFree {X : Type*} [Group X] [Finite X]
    {W C : Subgroup X} [hWn : W.Normal] [hCn : C.Normal]
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hWC : W ≤ C)
    (hcop : Nat.Coprime (Nat.card W) (W.relIndex C)) {h : X} (hC : h ∈ C)
    (hfix : ∀ a ∈ W, h * a * h⁻¹ = a → a = 1) :
    ∃ Y : Subgroup X, W ⊓ Y = ⊥ ∧ ∀ x : X, ∃ a ∈ W, ∃ y ∈ Y, x = a * y := by
  classical
  set W' : Subgroup C := W.subgroupOf C with hW'
  have : W'.Normal := hWn.subgroupOf C
  have : IsMulCommutative W' := ⟨⟨fun a b => Subtype.ext (Subtype.ext
    (hWab _ (mem_subgroupOf.mp a.2) _ (mem_subgroupOf.mp b.2)))⟩⟩
  have hcop' : Nat.Coprime (Nat.card W') W'.index := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv]
    exact hcop
  obtain ⟨R', hR'⟩ := Subgroup.exists_right_complement'_of_coprime hcop'
  have hdisj : ∀ r ∈ R', r ∈ W' → r = 1 := fun r hr hrW =>
    Subgroup.disjoint_def.mp hR'.disjoint hrW hr
  have hdec : ∀ c : C, ∃ a ∈ W', ∃ r ∈ R', c = a * r := fun c => by
    obtain ⟨⟨a, r⟩, har, -⟩ := Subgroup.IsComplement.existsUnique hR' c
    exact ⟨a, a.2, r, r.2, har.symm⟩
  set R : Subgroup X := R'.map C.subtype with hRdef
  refine ⟨normalizer (R : Set X), ?_, fun x => ?_⟩
  ·
    rw [eq_bot_iff]
    rintro y ⟨hyW, hyN⟩
    have hyC : ∀ r ∈ R, y * r = r * y := by
      intro r hr
      have h1 : y * r * y⁻¹ ∈ R := (mem_normalizer_iff.mp hyN r).mp hr
      have hrC : r ∈ C := by obtain ⟨r', -, rfl⟩ := hr; exact r'.2
      have h2 : y * r * y⁻¹ * r⁻¹ ∈ W := by
        have : r * y⁻¹ * r⁻¹ ∈ W := hWn.conj_mem _ (inv_mem hyW) r
        rw [show y * r * y⁻¹ * r⁻¹ = y * (r * y⁻¹ * r⁻¹) by group]
        exact mul_mem hyW this
      have h3 : y * r * y⁻¹ * r⁻¹ ∈ R := mul_mem h1 (inv_mem hr)
      obtain ⟨c, hc, hce⟩ := h3
      have hcW : c ∈ W' := by
        rw [mem_subgroupOf]; change (C.subtype c) ∈ W; rw [hce]; exact h2
      have h4 := hdisj c hc hcW
      rw [h4, map_one] at hce
      calc y * r = y * r * y⁻¹ * r⁻¹ * (r * y) := by group
        _ = r * y := by rw [← hce, one_mul]
    obtain ⟨a, ha, r, hr, hhr⟩ := hdec ⟨h, hC⟩
    have hh : h = (a : X) * (r : X) := congrArg Subtype.val hhr
    have hyr := hyC r ⟨r, hr, rfl⟩
    have hya := hWab y hyW (a : X) (mem_subgroupOf.mp ha)
    refine hfix y hyW ?_
    rw [hh]
    calc (a : X) * (r : X) * y * ((a : X) * (r : X))⁻¹ =
        (a : X) * (r * y) * (r : X)⁻¹ * (a : X)⁻¹ := by group
      _ = (a : X) * (y * r) * (r : X)⁻¹ * (a : X)⁻¹ := by rw [hyr]
      _ = (a : X) * y * (a : X)⁻¹ := by group
      _ = y := by rw [← hya, mul_inv_cancel_right]
  ·
    set φ : C →* C := (MulAut.conjNormal x).toMonoidHom with hφ
    have hφapp : ∀ c : C, ((φ c : C) : X) = x * c * x⁻¹ := fun c => rfl
    set K' : Subgroup C := R'.map φ with hK'
    have hWK : W' ⊓ K' = ⊥ := by
      rw [eq_bot_iff]
      rintro c ⟨hcW, r, hr, rfl⟩
      have hrW : r ∈ W' := by
        rw [mem_subgroupOf]
        have h1 : x⁻¹ * ((φ r : C) : X) * x⁻¹⁻¹ ∈ W :=
          hWn.conj_mem _ (mem_subgroupOf.mp hcW) x⁻¹
        rw [hφapp] at h1
        simpa [mul_assoc] using h1
      rw [hdisj r hr hrW, map_one]
      exact one_mem _
    have hWK' : (W' : Set C) * (K' : Set C) = Set.univ := by
      refine Set.eq_univ_of_forall fun c => ?_
      set c' : C := ⟨x⁻¹ * c * x, by
        have := hCn.conj_mem _ c.2 x⁻¹
        simpa using this⟩ with hc'
      obtain ⟨a, ha, r, hr, hcar⟩ := hdec c'
      refine ⟨φ a, ?_, φ r, ⟨r, hr, rfl⟩, ?_⟩
      · rw [SetLike.mem_coe, mem_subgroupOf, hφapp]
        exact hWn.conj_mem _ (mem_subgroupOf.mp ha) x
      · apply Subtype.ext
        change ((φ a : C) : X) * ((φ r : C) : X) = c
        rw [hφapp, hφapp]
        have : (c' : X) = (a : X) * r := congrArg Subtype.val hcar
        rw [hc'] at this
        calc x * (a : X) * x⁻¹ * (x * r * x⁻¹) = x * ((a : X) * r) * x⁻¹ := by group
          _ = x * (x⁻¹ * c * x) * x⁻¹ := by rw [← this]
          _ = c := by group
    have hWR' : (W' : Set C) * (R' : Set C) = Set.univ := by
      refine Set.eq_univ_of_forall fun c => ?_
      obtain ⟨a, ha, r, hr, hcar⟩ := hdec c
      exact ⟨a, ha, r, hr, hcar.symm⟩
    have hWRb : W' ⊓ R' = ⊥ := by
      rw [eq_bot_iff]
      rintro c ⟨hcW, hcR⟩
      exact hdisj c hcR hcW
    obtain ⟨n, hn, hK⟩ := CFSG.SolvableHall.abelian_normal_hall_complement_conjugacy W' hcop'
      hWR' hWK' hWRb hWK
    refine ⟨(n : X)⁻¹, inv_mem (mem_subgroupOf.mp hn), (n : X) * x, ?_, by group⟩
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨r, hr, rfl⟩ := hy
    have h1 : φ r ∈ K' := ⟨r, hr, rfl⟩
    rw [hK] at h1
    obtain ⟨r', hr', hr'e⟩ := h1
    have h2 : x * (r : X) * x⁻¹ = (n : X)⁻¹ * r' * n := by
      rw [← hφapp, ← hr'e]
      simp
    refine ⟨r', hr', ?_⟩
    change (r' : X) = (n : X) * x * r * ((n : X) * x)⁻¹
    rw [show (n : X) * x * r * ((n : X) * x)⁻¹ = n * (x * r * x⁻¹) * (n : X)⁻¹ by group, h2]
    group

end Generic

end CaseAAux

open CaseAAux

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.OddStandard.Seitz77 (Datum)
open Matrix CFSG.ComponentClassification.CatalogueSchreierLinearTwo

namespace WData

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G} {q : ℕ}

instance instCommGroupWN (w : WData d Vi q) : CommGroup w.WN :=
  { (inferInstance : Group w.WN) with
    mul_comm := fun x y => Subtype.ext (Subtype.ext (comm_of_isElemAbelian w.elem
      (mem_subgroupOf.mp x.2) (mem_subgroupOf.mp y.2))) }

instance instModuleWN (w : WData d Vi q) : Module (ZMod 2) (Additive w.WN) :=
  AddCommGroup.zmodModule fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, ofMul_eq_zero]
    exact Subtype.ext (Subtype.ext (w.elem.2 _ (mem_subgroupOf.mp (Additive.toMul x).2)))

@[expose] noncomputable def actN (w : WData d Vi q) :
    w.N →* Module.End (ZMod 2) (Additive w.WN) where
  toFun n := AddMonoidHom.toZModLinearMap 2
    (MonoidHom.toAdditive (MulAut.conjNormal n).toMonoidHom)
  map_one' := by
    ext x
    simp
  map_mul' m n := by
    ext x
    simp [MulAut.conjNormal_apply, mul_assoc]

theorem coe_actN_apply (w : WData d Vi q) (n : w.N) (x : Additive w.WN) :
    (((Additive.toMul (w.actN n x) : w.WN) : w.N) : G) =
      (n : G) * (((Additive.toMul x : w.WN) : w.N) : G) * (n : G)⁻¹ := rfl

@[expose] noncomputable def act (w : WData d Vi q) :
    w.Nbar →* Module.End (ZMod 2) (Additive w.WN) :=
  QuotientGroup.lift w.WN w.actN (fun y hy => by
    rw [MonoidHom.mem_ker]
    ext x
    rw [coe_actN_apply]
    rw [comm_of_isElemAbelian w.elem (mem_subgroupOf.mp hy)
      (mem_subgroupOf.mp (Additive.toMul x).2), mul_inv_cancel_right]
    rfl)

theorem act_projBar (w : WData d Vi q) (n : w.N) : w.act (w.projBar n) = w.actN n :=
  QuotientGroup.lift_mk' _ _ n

abbrev coeW (w : WData d Vi q) (x : Additive w.WN) : G := ((Additive.toMul x : w.WN) : w.N)

theorem coeW_mem (w : WData d Vi q) (x : Additive w.WN) : w.coeW x ∈ w.W :=
  mem_subgroupOf.mp (Additive.toMul x).2

theorem coeW_add (w : WData d Vi q) (x y : Additive w.WN) :
    w.coeW (x + y) = w.coeW x * w.coeW y := rfl

theorem coeW_zero (w : WData d Vi q) : w.coeW 0 = 1 := rfl

theorem coeW_injective (w : WData d Vi q) : Function.Injective w.coeW := fun _ _ h =>
  Additive.toMul.injective (Subtype.ext (Subtype.ext h))

theorem coeW_eq_one_iff (w : WData d Vi q) (x : Additive w.WN) : w.coeW x = 1 ↔ x = 0 :=
  ⟨fun h => w.coeW_injective (h.trans (w.coeW_zero).symm), fun h => h ▸ w.coeW_zero⟩

theorem exists_coeW_eq (w : WData d Vi q) {y : G} (hy : y ∈ w.W) :
    ∃ x : Additive w.WN, w.coeW x = y :=
  ⟨Additive.ofMul ⟨⟨y, w.W_le_N hy⟩, mem_subgroupOf.mpr hy⟩, rfl⟩

theorem coeW_act (w : WData d Vi q) (n : w.N) (x : Additive w.WN) :
    w.coeW (w.act (w.projBar n) x) = (n : G) * w.coeW x * (n : G)⁻¹ := by
  rw [act_projBar]; rfl

abbrev Vsub (w : WData d Vi q) : Submodule (ZMod 2) (Additive w.WN) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup ((Vi.subgroupOf w.N).subgroupOf w.WN))

theorem mem_Vsub (w : WData d Vi q) (x : Additive w.WN) : x ∈ w.Vsub ↔ w.coeW x ∈ Vi := Iff.rfl

noncomputable abbrev kappa (w : WData d Vi q) : Additive w.WN →ₗ[ZMod 2] Additive w.WN :=
  w.act w.tbar - LinearMap.id

theorem coeW_kappa (w : WData d Vi q) (x : Additive w.WN) :
    w.coeW (w.kappa x) = d.t * w.coeW x * d.t * (w.coeW x)⁻¹ := by
  have h1 : w.kappa x = w.act w.tbar x + -x := by
    rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_add_neg]
  rw [h1, coeW_add, coeW_act]
  have h2 : w.coeW (-x) = (w.coeW x)⁻¹ := rfl
  rw [h2, inv_eq_of_mul_eq_one_right d.t_mul_self]

theorem kappa_mem (w : WData d Vi q) (x : Additive w.WN) : w.kappa x ∈ w.Vsub := by
  rw [mem_Vsub, coeW_kappa]
  exact w.comm_mem _ (w.coeW_mem x)

theorem exists_kappa_eq (w : WData d Vi q) {v : Additive w.WN} (hv : v ∈ w.Vsub) :
    ∃ x, w.kappa x = v := by
  obtain ⟨y, hy, hyv⟩ := w.comm_onto _ hv
  obtain ⟨x, rfl⟩ := w.exists_coeW_eq hy
  exact ⟨x, w.coeW_injective (by rw [coeW_kappa, hyv]; rfl)⟩

theorem act_tbar_eq_iff (w : WData d Vi q) (x : Additive w.WN) :
    w.act w.tbar x = x ↔ x ∈ w.Vsub := by
  rw [mem_Vsub, ← SetLike.ext_iff.mp w.fix (w.coeW x)]
  constructor
  · intro h
    refine ⟨w.coeW_mem x, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := congrArg w.coeW h
    rw [coeW_act] at h1
    change d.t * w.coeW x * d.t⁻¹ = w.coeW x at h1
    calc w.coeW x * d.t = d.t * w.coeW x * d.t⁻¹ * d.t := by rw [h1]
      _ = d.t * w.coeW x := by group
  · rintro ⟨-, hx⟩
    apply w.coeW_injective
    rw [coeW_act]
    change d.t * w.coeW x * d.t⁻¹ = w.coeW x
    rw [← mem_centralizer_singleton_iff.mp hx, mul_inv_cancel_right]

theorem kappa_eq_zero_iff (w : WData d Vi q) (x : Additive w.WN) :
    w.kappa x = 0 ↔ x ∈ w.Vsub := by
  rw [← act_tbar_eq_iff, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem act_kappa (w : WData d Vi q) {g : w.Nbar} (hg : g * w.tbar = w.tbar * g)
    (x : Additive w.WN) : w.act g (w.kappa x) = w.kappa (w.act g x) := by
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hg]

end WData

namespace WData

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G} {q : ℕ}
  {K : Type} [Field K]

abbrev levE (w : WData d Vi q) (D : LeviData A Vi K) (B : SL(2, K)) : w.N :=
  ⟨D.lev B, w.lev_mem_N D B⟩

abbrev levQ (w : WData d Vi q) (D : LeviData A Vi K) (B : SL(2, K)) : w.Nbar :=
  w.projBar (w.levE D B)

theorem levBar_mem_Lbar (w : WData d Vi q) (D : LeviData A Vi K) (B : SL(2, K)) :
    w.levQ D B ∈ w.Lbar D.lev.range :=
  ⟨w.levE D B, mem_subgroupOf.mpr ⟨B, rfl⟩, rfl⟩

theorem levBar_comm_tbar (w : WData d Vi q) (D : LeviData A Vi K) (B : SL(2, K)) :
    w.levQ D B * w.tbar = w.tbar * w.levQ D B :=
  mem_centralizer_singleton_iff.mp (w.Lbar_le_centralizer D (w.levBar_mem_Lbar D B))

theorem coeW_act_levBar (w : WData d Vi q) (D : LeviData A Vi K) (B : SL(2, K))
    (x : Additive w.WN) :
    w.coeW (w.act (w.levQ D B) x) = D.lev B * w.coeW x * (D.lev B)⁻¹ :=
  w.coeW_act (w.levE D B) x

theorem exists_act_levBar_eq (w : WData d Vi q) (D : LeviData A Vi K) {v v' : Additive w.WN}
    (hv : v ∈ w.Vsub) (hv' : v' ∈ w.Vsub) (h0 : v ≠ 0) (h0' : v' ≠ 0) :
    ∃ B, w.act (w.levQ D B) v = v' := by
  obtain ⟨B, hB⟩ := D.transitive _ hv _ hv' (fun h => h0 ((w.coeW_eq_one_iff v).mp h))
    (fun h => h0' ((w.coeW_eq_one_iff v').mp h))
  exact ⟨B, w.coeW_injective (by rw [coeW_act_levBar]; exact hB)⟩

theorem act_levBar_dElt_eq (w : WData d Vi q) (D : LeviData A Vi K) {μ : Kˣ} (hμ : μ ≠ 1)
    {x : Additive w.WN} (hx : w.act (w.levQ D (dElt μ)) x = x) : x = 0 := by
  have hfixV : ∀ v ∈ w.Vsub, w.act (w.levQ D (dElt μ)) v = v → v = 0 := by
    intro v hv hfix
    have hvr : w.coeW v ∈ D.ι.range := by rw [D.range_ι]; exact hv
    obtain ⟨u, hu⟩ := hvr
    have h1 := congrArg w.coeW hfix
    rw [coeW_act_levBar, ← hu, D.lev_conj] at h1
    have h2 := Multiplicative.ofAdd.injective (D.ι_injective h1)
    have hu0 : Multiplicative.toAdd u = 0 := by
      funext i
      have h3 := congrFun h2 i
      fin_cases i
      · have h4 : (μ : K) * (Multiplicative.toAdd u) 0 = (Multiplicative.toAdd u) 0 := by
          simp [dElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h3
          exact h3
        have h5 : ((μ : K) - 1) * (Multiplicative.toAdd u) 0 = 0 := by
          rw [sub_mul, one_mul, h4, sub_self]
        have hμ1 : (μ : K) - 1 ≠ 0 := sub_ne_zero.mpr (fun h => hμ (Units.ext h))
        simpa using (mul_eq_zero.mp h5).resolve_left hμ1
      · have h4 : ((μ⁻¹ : Kˣ) : K) * (Multiplicative.toAdd u) 1 = (Multiplicative.toAdd u) 1 := by
          simp [dElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h3
          rw [Units.val_inv_eq_inv_val]
          exact h3
        have h5 : (((μ⁻¹ : Kˣ) : K) - 1) * (Multiplicative.toAdd u) 1 = 0 := by
          rw [sub_mul, one_mul, h4, sub_self]
        have hμ1 : ((μ⁻¹ : Kˣ) : K) - 1 ≠ 0 :=
          sub_ne_zero.mpr (fun h => hμ (inv_eq_one.mp (Units.ext h)))
        simpa using (mul_eq_zero.mp h5).resolve_left hμ1
    have hu1 : u = 1 := by
      rw [← ofAdd_toAdd u, hu0, ofAdd_zero]
    rw [← w.coeW_eq_one_iff, ← hu, hu1, map_one]
  have hκ : w.kappa x = 0 := by
    refine hfixV _ (w.kappa_mem x) ?_
    rw [w.act_kappa (w.levBar_comm_tbar D _), hx]
  exact hfixV x ((w.kappa_eq_zero_iff x).mp hκ) hx

theorem act_tor_eq (w : WData d Vi q) (D : LeviData A Vi K) {l : Kˣ} (hl : (l : K) ^ 3 ≠ 1)
    {x : Additive w.WN} (hx : w.act (w.projBar ⟨D.tor l, w.tor_mem_N D l⟩) x = x) : x = 0 := by
  have hcomm : w.projBar ⟨D.tor l, w.tor_mem_N D l⟩ * w.tbar =
      w.tbar * w.projBar ⟨D.tor l, w.tor_mem_N D l⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (d.comm_t_of_mem (D.tor_mem l))
  have hfixV : ∀ v ∈ w.Vsub, w.act (w.projBar ⟨D.tor l, w.tor_mem_N D l⟩) v = v → v = 0 := by
    intro v hv hfix
    have hvr : w.coeW v ∈ D.ι.range := by rw [D.range_ι]; exact hv
    obtain ⟨u, hu⟩ := hvr
    have h1 := congrArg w.coeW hfix
    rw [coeW_act, ← hu] at h1
    change D.tor l * D.ι u * (D.tor l)⁻¹ = D.ι u at h1
    rw [D.tor_conj] at h1
    have h2 : (l : K) ^ 3 • Multiplicative.toAdd u = Multiplicative.toAdd u :=
      Multiplicative.ofAdd.injective (D.ι_injective h1)
    have hu0 : Multiplicative.toAdd u = 0 := by
      have h3 : ((l : K) ^ 3 - 1) • Multiplicative.toAdd u = 0 := by
        rw [sub_smul, one_smul, h2, sub_self]
      exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hl)
    have hu1 : u = 1 := by
      rw [← ofAdd_toAdd u, hu0, ofAdd_zero]
    rw [← w.coeW_eq_one_iff, ← hu, hu1, map_one]
  have hκ : w.kappa x = 0 := by
    refine hfixV _ (w.kappa_mem x) ?_
    rw [w.act_kappa hcomm, hx]
  exact hfixV x ((w.kappa_eq_zero_iff x).mp hκ) hx

theorem card_Vsub (w : WData d Vi q) : Nat.card w.Vsub = Nat.card Vi := by
  refine Nat.card_congr
    { toFun := fun x => ⟨w.coeW x, x.2⟩
      invFun := fun v => ⟨Additive.ofMul ⟨⟨v, w.W_le_N (w.le_W v.2)⟩,
        mem_subgroupOf.mpr (w.le_W v.2)⟩, v.2⟩
      left_inv := fun x => rfl
      right_inv := fun v => rfl }

theorem card_WN (w : WData d Vi q) : Nat.card (Additive w.WN) = q ^ 4 := by
  rw [← w.card]
  exact Nat.card_congr ((Additive.toMul).trans (subgroupOfEquivOfLe w.W_le_N).toEquiv)

end WData

namespace CaseACoord

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G} {f : ℕ}
  {w : WData d Vi (2 ^ f)} {L : Subgroup G} {K : Type} [Field K] {D : LeviData A Vi K}

noncomputable def rho (C : CaseACoord f w L) :
    Representation (ZMod 2) (SpecialLinearGroup (Fin 2) C.F) (Additive w.WN) :=
  w.act.comp ((w.Ebar L).subtype.comp C.ψ.symm.toMonoidHom)

theorem rho_ψ (C : CaseACoord f w L) (x : w.Ebar L) : C.rho (C.ψ x) = w.act x := by
  simp [rho]

theorem rho_isIrreducible [Finite G] {f' : ℕ} (hf : 3 ≤ f') {V₁ V₂ : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f')) (hW : Vi = V₁ ∨ Vi = V₂) {w : WData d Vi (2 ^ f')}
    [Finite K] (hKc : Nat.card K = 2 ^ f') (C : CaseACoord f' w D.lev.range) :
    C.rho.IsIrreducible := by
  classical
  have : Fintype C.F := Fintype.ofFinite _
  have hF : Fintype.card C.F = 2 ^ (2 * f') := by rw [Fintype.card_eq_nat_card, C.card]
  obtain ⟨-, -, hVc⟩ := hR.property hW
  have hcardV : Nat.card w.Vsub = 2 ^ (2 * f') := by
    rw [w.card_Vsub, hVc, ← pow_mul, mul_comm]
  have hLE : ∀ B, w.levQ D B ∈ w.Ebar D.lev.range := fun B =>
    le_normalClosure (w.levBar_mem_Lbar D B)
  have hrhoL : ∀ B, C.rho (C.ψ ⟨_, hLE B⟩) = w.act (w.levQ D B) := fun B => C.rho_ψ _
  obtain ⟨μ, hμ⟩ : ∃ μ : Kˣ, μ ≠ 1 := exists_unit_ne_one (by
    rw [hKc]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f' := Nat.pow_le_pow_right (by norm_num) (by omega))
  have hVne : Vi ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hVc
    have : 1 < (2 ^ f') ^ 2 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
    omega
  obtain ⟨v₀, hv₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hVne
  obtain ⟨x₀, hx₀⟩ := w.exists_coeW_eq (w.le_W v₀.2)
  have hx₀V : x₀ ∈ w.Vsub := by rw [WData.mem_Vsub, hx₀]; exact v₀.2
  have hx₀0 : x₀ ≠ 0 := fun h0 => hv₀1 (Subtype.ext (by rw [← hx₀, h0, WData.coeW_zero]; rfl))
  have hmove : w.act (w.levQ D (dElt μ)) x₀ ≠ x₀ := fun h1 =>
    hx₀0 (w.act_levBar_dElt_eq D hμ h1)
  rw [CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff]
  refine ⟨⟨⟨x₀, 0, hx₀0⟩⟩, fun U hU => ?_⟩
  have hUL : ∀ B, ∀ u ∈ U, w.act (w.levQ D B) u ∈ U := fun B u hu => by
    rw [← hrhoL]; exact hU _ u hu
  have hd1 : (∀ v ∈ w.Vsub, v ∈ U) ∨ (∀ v ∈ U, v ∈ w.Vsub → v = 0) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨v, hvV, hvU⟩, ⟨u, huU, huV, hu0⟩⟩ := hcon
    apply hvU
    by_cases hv0 : v = 0
    · rw [hv0]; exact U.zero_mem
    · obtain ⟨B, hB⟩ := w.exists_act_levBar_eq D huV hvV hu0 hv0
      rw [← hB]; exact hUL B u huU
  have hd2 : (∀ v ∈ w.Vsub, ∃ u ∈ U, w.kappa u = v) ∨ (∀ u ∈ U, w.kappa u = 0) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨v, hvV, hvU⟩, ⟨u, huU, hu0⟩⟩ := hcon
    by_cases hv0 : v = 0
    · exact hvU 0 U.zero_mem (by rw [map_zero, hv0])
    · obtain ⟨B, hB⟩ := w.exists_act_levBar_eq D (w.kappa_mem u) hvV hu0 hv0
      exact hvU _ (hUL B u huU) (by rw [← w.act_kappa (w.levBar_comm_tbar D B), hB])
  have hbound : (∃ u ∈ U, w.act (w.levQ D (dElt μ)) u ≠ u) → 2 ^ (2 * (2 * f')) ≤ Nat.card U :=
    fun ⟨u, hu, hne⟩ => le_card_of_invariant (by omega) (by omega) hF C.rho U hU
      ⟨_, u, hu, by rw [hrhoL]; exact hne⟩
  have hlt : 2 ^ (2 * f') < 2 ^ (2 * (2 * f')) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rcases hd2 with hk | hk
  · rcases hd1 with hv | hv
    ·
      right
      rw [eq_top_iff]
      intro x _
      obtain ⟨u, hu, hux⟩ := hk _ (w.kappa_mem x)
      have h1 : x - u ∈ w.Vsub := by
        rw [← w.kappa_eq_zero_iff, map_sub, hux, sub_self]
      have h2 := U.add_mem (hv _ h1) hu
      rwa [sub_add_cancel] at h2
    ·
      exfalso
      obtain ⟨u₀, hu₀, hu₀x⟩ := hk x₀ hx₀V
      have hne : w.act (w.levQ D (dElt μ)) u₀ ≠ u₀ := fun h1 => hmove (by
        rw [← hu₀x, w.act_kappa (w.levBar_comm_tbar D _), h1])
      have hle : Nat.card U ≤ Nat.card w.Vsub := by
        refine Nat.card_le_card_of_injective (fun u => ⟨w.kappa u, w.kappa_mem u⟩) ?_
        intro u u' huu
        have h1 : w.kappa ((u : Additive w.WN) - u') = 0 := by
          rw [map_sub, sub_eq_zero]
          exact congrArg Subtype.val huu
        have h2 := hv _ (U.sub_mem u.2 u'.2) ((w.kappa_eq_zero_iff _).mp h1)
        exact Subtype.ext (sub_eq_zero.mp h2)
      have := hbound ⟨u₀, hu₀, hne⟩
      omega
  · rcases hd1 with hv | hv
    ·
      exfalso
      have hUV : ∀ u ∈ U, u ∈ w.Vsub := fun u hu => (w.kappa_eq_zero_iff u).mp (hk u hu)
      have hle : Nat.card U ≤ Nat.card w.Vsub :=
        Nat.card_le_card_of_injective (fun u => ⟨u, hUV u u.2⟩) (fun u u' h =>
          Subtype.ext (by simpa using congrArg Subtype.val h))
      have := hbound ⟨x₀, hv x₀ hx₀V, hmove⟩
      omega
    ·
      left
      rw [eq_bot_iff]
      intro u hu
      exact hv u hu ((w.kappa_eq_zero_iff u).mp (hk u hu))

theorem exists_natural [Finite G] {f' : ℕ} (hf : 3 ≤ f') {V₁ V₂ : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f')) (hW : Vi = V₁ ∨ Vi = V₂) {w : WData d Vi (2 ^ f')}
    [Finite K] (hKc : Nat.card K = 2 ^ f') (C : CaseACoord f' w D.lev.range) :
    ∃ φ : Additive w.WN ≃+ (Fin 2 → C.F),
      ∀ g x, φ (C.rho g x) = (g : Matrix (Fin 2) (Fin 2) C.F).mulVec (φ x) := by
  classical
  have : Fintype C.F := Fintype.ofFinite _
  have hF : Fintype.card C.F = 2 ^ (2 * f') := by rw [Fintype.card_eq_nat_card, C.card]
  have hLE : ∀ B, w.levQ D B ∈ w.Ebar D.lev.range := fun B =>
    le_normalClosure (w.levBar_mem_Lbar D B)
  obtain ⟨μ, hμ⟩ : ∃ μ : Kˣ, μ ≠ 1 := exists_unit_ne_one (by
    rw [hKc]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f' := Nat.pow_le_pow_right (by norm_num) (by omega))
  set g₀ := C.ψ ⟨_, hLE (dElt μ)⟩ with hg₀
  have hrho : C.rho g₀ = w.act (w.levQ D (dElt μ)) := C.rho_ψ _
  have hfix : ∀ x, C.rho g₀ x = x → x = 0 := fun x hx =>
    w.act_levBar_dElt_eq D hμ (by rw [← hrho]; exact hx)
  have hnt : ∃ g, C.rho g ≠ 1 := by
    refine ⟨g₀, fun h1 => ?_⟩
    obtain ⟨-, -, hVc⟩ := hR.property hW
    have hVne : Vi ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hVc
      have : 1 < (2 ^ f') ^ 2 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
      omega
    obtain ⟨v₀, hv₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hVne
    obtain ⟨x₀, hx₀⟩ := w.exists_coeW_eq (w.le_W v₀.2)
    have hx₀0 : x₀ ≠ 0 := fun h0 => hv₀1 (Subtype.ext (by rw [← hx₀, h0, WData.coeW_zero]; rfl))
    exact hx₀0 (hfix x₀ (by rw [h1]; rfl))
  have hWc : Nat.card (Additive w.WN) = (2 ^ (2 * f')) ^ 2 := by
    rw [w.card_WN, ← pow_mul, ← pow_mul]; ring_nf
  exact natural_of_fixedPointFree (by omega) hF C.rho (C.rho_isIrreducible hf hR hW hKc)
    hnt hWc g₀ (fun i j => C.ψ_Lbar_pow (w.levBar_mem_Lbar D (dElt μ)) i j) hfix

theorem exists_natural_coord [Finite G] {f' : ℕ} (hf : 3 ≤ f') {V₁ V₂ : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f')) (hW : Vi = V₁ ∨ Vi = V₂) {w : WData d Vi (2 ^ f')}
    [Finite K] (hKc : Nat.card K = 2 ^ f') (C : CaseACoord f' w D.lev.range) :
    ∃ ι : Multiplicative (Fin 2 → C.F) →* G, Function.Injective ι ∧ ι.range = w.W ∧
      ∀ (n : w.N) (hn : w.projBar n ∈ w.Ebar D.lev.range) (v : Multiplicative (Fin 2 → C.F)),
        (n : G) * ι v * (n : G)⁻¹ = ι (Multiplicative.ofAdd
          ((C.ψ ⟨_, hn⟩ : Matrix (Fin 2) (Fin 2) C.F).mulVec (Multiplicative.toAdd v))) := by
  obtain ⟨φ, hφ⟩ := C.exists_natural hf hR hW hKc
  let ι : Multiplicative (Fin 2 → C.F) →* G :=
    { toFun := fun v => w.coeW (φ.symm (Multiplicative.toAdd v))
      map_one' := by simp [WData.coeW_zero]
      map_mul' := fun u v => by
        rw [toAdd_mul, map_add, WData.coeW_add] }
  have hsymm : ∀ (g : SpecialLinearGroup (Fin 2) C.F) u,
      φ.symm ((g : Matrix (Fin 2) (Fin 2) C.F).mulVec u) = C.rho g (φ.symm u) :=
    fun g u => φ.injective (by rw [hφ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply])
  refine ⟨ι, fun u v huv => ?_, ?_, fun n hn v => ?_⟩
  · have h1 := w.coeW_injective huv
    exact Multiplicative.toAdd.injective (φ.symm.injective h1)
  · apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact w.coeW_mem _
    · intro y hy
      obtain ⟨x, rfl⟩ := w.exists_coeW_eq hy
      exact ⟨Multiplicative.ofAdd (φ x), by
        change w.coeW (φ.symm (φ x)) = _
        rw [AddEquiv.symm_apply_apply]⟩
  · change (n : G) * w.coeW (φ.symm (Multiplicative.toAdd v)) * (n : G)⁻¹ =
      w.coeW (φ.symm _)
    rw [toAdd_ofAdd, hsymm, ← w.coeW_act, ← C.rho_ψ ⟨_, hn⟩]

theorem exists_unit_pow_three_ne_one {K : Type*} [Field K] [Finite K] (hK : 5 ≤ Nat.card K) :
    ∃ l : Kˣ, (l : K) ^ 3 ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have htop : rootsOfUnity 3 K = ⊤ := by
    rw [eq_top_iff]
    intro l _
    rw [mem_rootsOfUnity]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hcon l, Units.val_one])
  have h1 := card_rootsOfUnity K 3
  rw [htop, Subgroup.card_top, Nat.card_units] at h1
  omega

theorem exists_complement [Finite G] {f' : ℕ} (hf : 3 ≤ f') {w : WData d Vi (2 ^ f')}
    [Finite K] (hKc : Nat.card K = 2 ^ f') (C : CaseACoord f' w D.lev.range) :
    ∃ Y : Subgroup G, Y ≤ w.N ∧ w.W ⊓ Y = ⊥ ∧ d.t ∈ Y ∧
      ∀ n ∈ w.N, ∃ a ∈ w.W, ∃ y ∈ Y, n = a * y := by
  classical
  obtain ⟨l, hl⟩ := exists_unit_pow_three_ne_one (K := K) (by
    rw [hKc]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f' := Nat.pow_le_pow_right (by norm_num) hf)
  set O := standardComponentOddCore w.Nbar with hO
  set C' : Subgroup w.N := O.comap w.projBar with hC'
  have : C'.Normal := (inferInstance : O.Normal).comap _
  have hWab : ∀ a ∈ w.WN, ∀ b ∈ w.WN, a * b = b * a := fun a ha b hb =>
    Subtype.ext (comm_of_isElemAbelian w.elem (mem_subgroupOf.mp ha) (mem_subgroupOf.mp hb))
  have hWC : w.WN ≤ C' := fun a ha => by
    rw [hC', mem_comap, (w.projBar_eq_one_iff a).mpr (mem_subgroupOf.mp ha)]
    exact one_mem _
  have hcop : Nat.Coprime (Nat.card w.WN) (w.WN.relIndex C') := by
    have h1 : w.WN.relIndex C' = w.projBar.ker.relIndex C' :=
      congrArg (fun H : Subgroup w.N => H.relIndex C') (QuotientGroup.ker_mk' w.WN).symm
    have h2 : w.WN.relIndex C' = Nat.card O := by
      rw [h1, relIndex_ker, hC', map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
    have h3 : Nat.card w.WN = 2 ^ (4 * f') := by
      rw [Nat.card_congr (subgroupOfEquivOfLe w.W_le_N).toEquiv, w.card, ← pow_mul, mul_comm]
    rw [h2, h3]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr
      (CFSG.LocalAnalysis.EvenBN.GMSK.odd_card_standardComponentOddCore _))
  set hN : w.N := ⟨D.tor l, w.tor_mem_N D l⟩ with hhN
  have hhC : hN ∈ C' := by
    rw [hC', mem_comap]
    exact (QuotientGroup.eq_one_iff _).mp (C.projTil_tor hKc l)
  have hfix : ∀ a ∈ w.WN, hN * a * hN⁻¹ = a → a = 1 := by
    intro a ha hfa
    have h1 : w.act (w.projBar hN) (Additive.ofMul (⟨a, ha⟩ : w.WN)) =
        Additive.ofMul (⟨a, ha⟩ : w.WN) := by
      apply w.coeW_injective
      rw [WData.coeW_act]
      change (hN : G) * (a : G) * (hN : G)⁻¹ = a
      exact congrArg Subtype.val hfa
    have h2 := w.act_tor_eq D hl h1
    have h3 : (⟨a, ha⟩ : w.WN) = 1 := Additive.ofMul.injective h2
    exact congrArg Subtype.val h3
  obtain ⟨Y', hY'W, hY'dec⟩ :=
    exists_complement_of_fixedPointFree hWab hWC hcop hhC hfix
  obtain ⟨a, ha, y, hy, hty⟩ := hY'dec w.tN
  have haW : (a : G) ∈ w.W := mem_subgroupOf.mp ha
  have ht2 := d.t_mul_self
  have htinv : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right ht2
  have hyG : (y : G) = (a : G)⁻¹ * d.t := by
    have := congrArg Subtype.val hty
    simp only [Subgroup.coe_mul] at this
    change d.t = (a : G) * y at this
    rw [this]; group
  have hy2 : y * y = 1 := by
    have hyy : y * y ∈ w.WN := by
      rw [mem_subgroupOf]
      change (y : G) * y ∈ w.W
      rw [hyG]
      have : d.t * (a : G)⁻¹ * d.t⁻¹ ∈ w.W :=
        (mem_normalizer_iff.mp w.t_norm _).mp (inv_mem haW)
      rw [show (a : G)⁻¹ * d.t * ((a : G)⁻¹ * d.t) = (a : G)⁻¹ * (d.t * (a : G)⁻¹ * d.t⁻¹) by
        rw [htinv]; group]
      exact mul_mem (inv_mem haW) this
    have : y * y ∈ w.WN ⊓ Y' := ⟨hyy, mul_mem hy hy⟩
    rw [hY'W] at this
    exact this
  have ha2 : (a : G) * a = 1 := by rw [← sq]; exact w.elem.2 _ haW
  have hainv : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hat : (a : G) * d.t = d.t * a := by
    have h1 : (a : G) * d.t * ((a : G) * d.t) = 1 := by
      rw [← hainv, ← hyG]; exact congrArg Subtype.val hy2
    have h3 : d.t * (a : G) * d.t = a := by
      calc d.t * (a : G) * d.t = (a : G)⁻¹ * ((a : G) * d.t * ((a : G) * d.t)) := by group
        _ = a := by rw [h1, mul_one, hainv]
    calc (a : G) * d.t = d.t * (a : G) * d.t * d.t := by rw [h3]
      _ = d.t * a := by rw [mul_assoc _ d.t d.t, ht2, mul_one]
  have haV : (a : G) ∈ Vi :=
    (SetLike.ext_iff.mp w.fix _).mp ⟨haW, mem_centralizer_singleton_iff.mpr hat⟩
  obtain ⟨w', hw', hw'a⟩ := w.comm_onto _ haV
  have hyconj : (y : G) = w' * d.t * w'⁻¹ := by
    rw [hyG, hainv, hat, ← hw'a]
    calc d.t * (d.t * w' * d.t * w'⁻¹) = (d.t * d.t) * w' * d.t * w'⁻¹ := by group
      _ = w' * d.t * w'⁻¹ := by rw [ht2, one_mul]
  have hw'N : w' ∈ w.N := w.W_le_N hw'
  set Y : Subgroup G := (Y'.map w.N.subtype).map (MulAut.conj w'⁻¹).toMonoidHom with hYdef
  have hYN : Y ≤ w.N := by
    rintro _ ⟨_, ⟨z, -, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact mul_mem (mul_mem (inv_mem hw'N) z.2) hw'N
  refine ⟨Y, hYN, ?_, ?_, fun n hn => ?_⟩
  · rw [eq_bot_iff]
    rintro _ ⟨hxW, ⟨_, ⟨z, hz, rfl⟩, rfl⟩⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hxW ⊢
    have hzW : (z : G) ∈ w.W := by
      have := (mem_normalizer_iff.mp hw'N _).mp hxW
      simpa [mul_assoc] using this
    have : z ∈ w.WN ⊓ Y' := ⟨mem_subgroupOf.mpr hzW, hz⟩
    rw [hY'W, mem_bot] at this
    rw [this]
    simp
  · refine ⟨_, ⟨y, hy, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_subtype]
    rw [hyconj]
    group
  · obtain ⟨b, hb, z, hz, hnbz⟩ := hY'dec ⟨n, hn⟩
    have hbW : (b : G) ∈ w.W := mem_subgroupOf.mp hb
    have hn' : n = (b : G) * z := congrArg Subtype.val hnbz
    have hzN : (z : G) ∈ w.N := z.2
    have hc : (z : G) * w'⁻¹ * (z : G)⁻¹ ∈ w.W := (mem_normalizer_iff.mp hzN _).mp (inv_mem hw')
    refine ⟨(b : G) * ((z : G) * w'⁻¹ * (z : G)⁻¹) * w', mul_mem (mul_mem hbW hc) hw',
      w'⁻¹ * z * w', ⟨_, ⟨z, hz, rfl⟩, by simp⟩, ?_⟩
    rw [hn']
    group

end CaseACoord

namespace WData

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G} {q : ℕ}

abbrev Ehat (w : WData d Vi q) (L : Subgroup G) : Subgroup G :=
  ((w.Ebar L).comap w.projBar).map w.N.subtype

theorem mem_Ehat (w : WData d Vi q) (L : Subgroup G) {x : G} :
    x ∈ w.Ehat L ↔ ∃ hx : x ∈ w.N, w.projBar ⟨x, hx⟩ ∈ w.Ebar L := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hx'⟩
    exact ⟨⟨x, hx⟩, hx', rfl⟩

theorem Ehat_le_N (w : WData d Vi q) (L : Subgroup G) : w.Ehat L ≤ w.N :=
  map_subtype_le _

theorem W_le_Ehat (w : WData d Vi q) (L : Subgroup G) : w.W ≤ w.Ehat L := fun x hx =>
  (w.mem_Ehat L).mpr ⟨w.W_le_N hx, by
    rw [(w.projBar_eq_one_iff _).mpr hx]; exact one_mem _⟩

end WData

namespace CaseACoord

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G} {f : ℕ}
  {w : WData d Vi (2 ^ f)} {L : Subgroup G} {K : Type} [Field K] {D : LeviData A Vi K}

theorem exists_Ehat_complement [Finite G] {f' : ℕ} (hf : 3 ≤ f') {w : WData d Vi (2 ^ f')}
    [Finite K] (hKc : Nat.card K = 2 ^ f') (C : CaseACoord f' w D.lev.range) :
    ∃ (X : Subgroup G) (θ : X ≃* SpecialLinearGroup (Fin 2) C.F), X ≤ w.Ehat D.lev.range ∧
      w.W ⊓ X = ⊥ ∧ (∀ e ∈ w.Ehat D.lev.range, ∃ a ∈ w.W, ∃ x ∈ X, e = a * x) ∧
      ∀ (x : X) (hxN : (x : G) ∈ w.N) (hxE : w.projBar ⟨x, hxN⟩ ∈ w.Ebar D.lev.range),
        θ x = C.ψ ⟨_, hxE⟩ := by
  obtain ⟨Y, hYN, hWY, -, hdec⟩ := C.exists_complement hf hKc
  set E := w.Ehat D.lev.range with hE
  set X := E ⊓ Y with hX
  have hXN : ∀ x ∈ X, x ∈ w.N := fun x hx => hYN hx.2
  have hXE : ∀ (x : G) (hx : x ∈ X), w.projBar ⟨x, hXN x hx⟩ ∈ w.Ebar D.lev.range := by
    intro x hx
    obtain ⟨hxN, hxE⟩ := (w.mem_Ehat _).mp hx.1
    exact hxE
  let θ₀ : X →* SpecialLinearGroup (Fin 2) C.F :=
    { toFun := fun x => C.ψ ⟨_, hXE x x.2⟩
      map_one' := by
        rw [← map_one C.ψ]
        congr 1
      map_mul' := fun x y => by
        rw [← map_mul C.ψ]
        congr 1 }
  have hinj : Function.Injective θ₀ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (⟨_, hXE x x.2⟩ : w.Ebar D.lev.range) = 1 := C.ψ.injective (by rw [map_one]; exact hx)
    have h2 : w.projBar ⟨x, hXN x x.2⟩ = 1 := congrArg Subtype.val h1
    have h3 : (x : G) ∈ w.W := (w.projBar_eq_one_iff _).mp h2
    have h4 : (x : G) ∈ w.W ⊓ Y := ⟨h3, x.2.2⟩
    rw [hWY, mem_bot] at h4
    exact Subtype.ext h4
  have hsurj : Function.Surjective θ₀ := by
    intro g
    set e := C.ψ.symm g
    obtain ⟨n, hne⟩ := QuotientGroup.mk'_surjective w.WN (e : w.Nbar)
    obtain ⟨a, ha, y, hy, hny⟩ := hdec n n.2
    have hyN : y ∈ w.N := hYN hy
    have hyn : w.projBar ⟨y, hyN⟩ = e := by
      rw [← hne]
      rw [w.projBar_eq_iff]
      change y⁻¹ * (n : G) ∈ w.W
      rw [hny]
      have : y⁻¹ * (a * y) = y⁻¹ * a * y⁻¹⁻¹ := by group
      rw [this]
      exact (mem_normalizer_iff.mp (inv_mem hyN) a).mp ha
    have hyE : y ∈ E := (w.mem_Ehat _).mpr ⟨hyN, by rw [hyn]; exact e.2⟩
    refine ⟨⟨y, hyE, hy⟩, ?_⟩
    change C.ψ ⟨_, hXE y ⟨hyE, hy⟩⟩ = g
    rw [← C.ψ.apply_symm_apply g]
    congr 1
    exact Subtype.ext hyn
  refine ⟨X, MulEquiv.ofBijective θ₀ ⟨hinj, hsurj⟩, inf_le_left, ?_, ?_, fun x hxN hxE => rfl⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxW, -, hxY⟩
    have : x ∈ w.W ⊓ Y := ⟨hxW, hxY⟩
    rwa [hWY] at this
  · intro e he
    obtain ⟨a, ha, y, hy, hey⟩ := hdec e (w.Ehat_le_N _ he)
    refine ⟨a, ha, y, ⟨?_, hy⟩, hey⟩
    have : y = a⁻¹ * e := by rw [hey]; group
    rw [this]
    exact E.mul_mem (E.inv_mem (w.W_le_Ehat _ ha)) he

open CFSG.OddStandard.Seitz77 (uelt exists_uelt uelt_mul uelt_inj)
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover (unipAll)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)

theorem nonempty_sylow_equiv_unipAll [Finite G] {f' : ℕ} (hf : 3 ≤ f') {V₁ V₂ : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f')) (hW : Vi = V₁ ∨ Vi = V₂) {w : WData d Vi (2 ^ f')}
    [Finite K] (hKc : Nat.card K = 2 ^ f') (C : CaseACoord f' w D.lev.range) {S : Subgroup G}
    (hS : IsSylowOf 2 S (w.Ehat D.lev.range)) : Nonempty (S ≃* unipAll C.F) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype C.F := Fintype.ofFinite _
  have hFc : Fintype.card C.F = 2 ^ (2 * f') := by rw [Fintype.card_eq_nat_card, C.card]
  obtain ⟨ι, hιi, hιr, hιc⟩ := C.exists_natural_coord hf hR hW hKc
  obtain ⟨X, θ, hXE, hWX, hdec, hθ⟩ := C.exists_Ehat_complement hf hKc
  set E := w.Ehat D.lev.range with hE
  have hXN : ∀ x : X, (x : G) ∈ w.N := fun x => w.Ehat_le_N _ (hXE x.2)
  have hXEb : ∀ x : X, w.projBar ⟨x, hXN x⟩ ∈ w.Ebar D.lev.range := fun x =>
    ((w.mem_Ehat _).mp (hXE x.2)).2
  have hact : ∀ (x : X) (v : Multiplicative (Fin 2 → C.F)), (x : G) * ι v * (x : G)⁻¹ =
      ι (Multiplicative.ofAdd (((θ x : SpecialLinearGroup (Fin 2) C.F) :
        Matrix (Fin 2) (Fin 2) C.F).mulVec (Multiplicative.toAdd v))) := by
    intro x v
    rw [hθ x (hXN x) (hXEb x)]
    exact hιc ⟨x, hXN x⟩ (hXEb x) v
  let u : C.F → G := fun a => ((θ.symm (uElt a) : X) : G)
  have hu_add : ∀ a b, u (a + b) = u a * u b := fun a b => by
    simp only [u]
    rw [uElt_add, map_mul, Subgroup.coe_mul]
  have hu_act : ∀ a (v : Fin 2 → C.F), u a * ι (Multiplicative.ofAdd v) * (u a)⁻¹ =
      ι (Multiplicative.ofAdd ![v 0 + a * v 1, v 1]) := by
    intro a v
    rw [hact, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    congr 2
    funext i
    fin_cases i <;> simp [uElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  let Φf : unipAll C.F → G := fun g =>
    ι (Multiplicative.ofAdd ![CFSG.OddStandard.Seitz77.coordC g,
      CFSG.OddStandard.Seitz77.coordB g]) * u (CFSG.OddStandard.Seitz77.coordA g)
  have hΦ : ∀ a b c : C.F, Φf (uelt a b c) = ι (Multiplicative.ofAdd ![c, b]) * u a := by
    intro a b c
    simp [Φf]
  have hΦmul : ∀ g g' : unipAll C.F, Φf (g * g') = Φf g * Φf g' := by
    intro g g'
    obtain ⟨a, b, c, rfl⟩ := exists_uelt g
    obtain ⟨a', b', c', rfl⟩ := exists_uelt g'
    rw [uelt_mul, hΦ, hΦ, hΦ, hu_add]
    have h1 : ι (Multiplicative.ofAdd ![c, b]) * u a * (ι (Multiplicative.ofAdd ![c', b']) * u a') =
        ι (Multiplicative.ofAdd ![c, b]) * (u a * ι (Multiplicative.ofAdd ![c', b']) * (u a)⁻¹) *
          (u a * u a') := by group
    rw [h1, hu_act, ← map_mul, ← ofAdd_add]
    congr 3
    funext i
    fin_cases i
    · simp; ring
    · simp
  let Φ : unipAll C.F →* G :=
    { toFun := Φf
      map_one' := by
        have h1 : (1 : unipAll C.F) = uelt 0 0 0 := (CFSG.OddStandard.Seitz77.uelt_zero).symm
        rw [h1, hΦ]
        have h2 : u 0 = 1 := by simp [u, uElt_zero]
        rw [h2, mul_one]
        have h3 : (Multiplicative.ofAdd ![(0 : C.F), 0]) = 1 := by
          rw [← ofAdd_zero]; congr 1; funext i; fin_cases i <;> rfl
        rw [h3, map_one]
      map_mul' := hΦmul }
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨a, b, c, rfl⟩ := exists_uelt g
    change Φf (uelt a b c) = 1 at hg
    rw [hΦ] at hg
    have h1 : u a ∈ w.W ⊓ X := by
      refine ⟨?_, (θ.symm (uElt a)).2⟩
      have : u a = (ι (Multiplicative.ofAdd ![c, b]))⁻¹ := eq_inv_of_mul_eq_one_right hg
      rw [this, ← hιr]
      exact Subgroup.inv_mem _ ⟨_, rfl⟩
    rw [hWX, mem_bot] at h1
    have ha : uElt a = 1 := by
      have h2 : θ.symm (uElt a) = 1 := Subtype.ext h1
      rw [← map_one θ.symm] at h2
      exact θ.symm.injective h2
    have ha0 : a = 0 := by
      have := congrArg (fun M : SpecialLinearGroup (Fin 2) C.F =>
        (M : Matrix (Fin 2) (Fin 2) C.F) 0 1) ha
      simpa [uElt] using this
    rw [h1, mul_one] at hg
    have hcb : Multiplicative.ofAdd ![c, b] = 1 := hιi (by rw [hg, map_one])
    have hc : c = 0 := by
      have := congrFun (congrArg Multiplicative.toAdd hcb) 0
      simpa using this
    have hb : b = 0 := by
      have := congrFun (congrArg Multiplicative.toAdd hcb) 1
      simpa using this
    rw [ha0, hb, hc]
    exact CFSG.OddStandard.Seitz77.uelt_zero
  set S₀ := Φ.range with hS₀
  have hS₀E : S₀ ≤ E := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨a, b, c, rfl⟩ := exists_uelt g
    change Φf (uelt a b c) ∈ E
    rw [hΦ]
    exact E.mul_mem (w.W_le_Ehat _ (hιr ▸ ⟨_, rfl⟩)) (hXE (θ.symm (uElt a)).2)
  have hcardS₀ : Nat.card S₀ = 2 ^ (6 * f') := by
    rw [hS₀, ← Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv,
      CFSG.OddStandard.Seitz77.card_unipAll, C.card, ← pow_mul]
    ring_nf
  have hcardE : Nat.card E = Nat.card w.W * Nat.card X := by
    rw [← Nat.card_prod]
    refine (Nat.card_congr (Equiv.ofBijective (fun p : w.W × X => (⟨(p.1 : G) * p.2,
      E.mul_mem (w.W_le_Ehat _ p.1.2) (hXE p.2.2)⟩ : E)) ⟨?_, ?_⟩)).symm
    · rintro ⟨a, x⟩ ⟨a', x'⟩ hax
      have h1 : (a : G) * x = a' * x' := congrArg Subtype.val hax
      have h2 : (a' : G)⁻¹ * a = x' * (x : G)⁻¹ := by
        calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * x) * (x : G)⁻¹ := by group
          _ = (a' : G)⁻¹ * (a' * x') * (x : G)⁻¹ := by rw [h1]
          _ = x' * (x : G)⁻¹ := by group
      have h3 : (a' : G)⁻¹ * a ∈ w.W ⊓ X :=
        ⟨w.W.mul_mem (w.W.inv_mem a'.2) a.2, h2 ▸ X.mul_mem x'.2 (X.inv_mem x.2)⟩
      rw [hWX, mem_bot] at h3
      have haa : (a : G) = a' := by
        calc (a : G) = a' * ((a' : G)⁻¹ * a) := by group
          _ = a' := by rw [h3, mul_one]
      have hxx : (x : G) = x' := by
        calc (x : G) = (a : G)⁻¹ * (a * x) := by group
          _ = (a' : G)⁻¹ * (a' * x') := by rw [h1, haa]
          _ = x' := by group
      exact Prod.ext (Subtype.ext haa) (Subtype.ext hxx)
    · rintro ⟨e, he⟩
      obtain ⟨a, ha, x, hx, rfl⟩ := hdec e he
      exact ⟨(⟨a, ha⟩, ⟨x, hx⟩), rfl⟩
  have hfacE : (Nat.card E).factorization 2 = 6 * f' := by
    rw [hcardE, Nat.card_congr θ.toEquiv, w.card,
      Nat.factorization_mul (by positivity)
        (Nat.card_pos (α := SpecialLinearGroup (Fin 2) C.F)).ne',
      Finsupp.add_apply, ← pow_mul, Nat.Prime.factorization_pow Nat.prime_two,
      factorization_card_sl2 (by omega) hFc]
    simp
    ring
  have hS₀syl : IsSylowOf 2 S₀ E := isSylowOf_of_card hS₀E (by rw [hcardS₀, hfacE])
  obtain ⟨Q, hQ⟩ := hS
  obtain ⟨Q₀, hQ₀⟩ := hS₀syl
  have e₁ : S ≃* (Q : Subgroup E) := by
    rw [← hQ]
    exact (Subgroup.equivMapOfInjective _ _ E.subtype_injective).symm
  have e₂ : S₀ ≃* (Q₀ : Subgroup E) := by
    rw [← hQ₀]
    exact (Subgroup.equivMapOfInjective _ _ E.subtype_injective).symm
  exact ⟨(e₁.trans (Sylow.equiv Q Q₀)).trans
    (e₂.symm.trans (MonoidHom.ofInjective hΦinj).symm)⟩

end CaseACoord


namespace Hyp

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ}

open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover (unipAll)
open CFSG.ABGLocalTools (IsSylowOf)

theorem seitz31
    (hf : 3 ≤ f) (d : Datum A) {V₁ V₂ Vi : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : Vi = V₁ ∨ Vi = V₂)
    (hN : normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (Vi : Set G))
    (w : WData d Vi (2 ^ f))
    {K : Type} [Field K] [Finite K] (D : LeviData A Vi K) (hKc : Nat.card K = 2 ^ f)
    (hA : w.CaseA f D.lev.range)
    (hO : ⁅standardComponentOddCore w.Nbar, w.Ebar D.lev.range⁆ = ⊥) :
    ∃ C : CaseACoord f w D.lev.range,
      (∃ ι : Multiplicative (Fin 2 → C.F) →* G, Function.Injective ι ∧ ι.range = w.W ∧
        ∀ (n : w.N) (hn : w.projBar n ∈ w.Ebar D.lev.range) (v : Multiplicative (Fin 2 → C.F)),
          (n : G) * ι v * (n : G)⁻¹ = ι (Multiplicative.ofAdd
            ((C.ψ ⟨_, hn⟩ : Matrix (Fin 2) (Fin 2) C.F).mulVec (Multiplicative.toAdd v)))) ∧
      (∃ X : Subgroup G, X ≤ w.Ehat D.lev.range ∧ w.W ⊓ X = ⊥ ∧
        ∀ e ∈ w.Ehat D.lev.range, ∃ a ∈ w.W, ∃ x ∈ X, e = a * x) ∧
      ∀ S : Subgroup G, IsSylowOf 2 S (w.Ehat D.lev.range) → Nonempty (S ≃* unipAll C.F) := by
  obtain ⟨C⟩ := WData.CaseA.nonempty_coord hf hR hW hN hKc hA hO
  obtain ⟨X, -, hXE, hWX, hdec, -⟩ := C.exists_Ehat_complement hf hKc
  exact ⟨C, C.exists_natural_coord hf hR hW hKc, ⟨X, hXE, hWX, hdec⟩,
    fun S hS => C.nonempty_sylow_equiv_unipAll hf hR hW hKc hS⟩

theorem seitz31_of_seitz27
    (hG : CFSG.CGT.Timmesfeld75.Goldschmidt1974)
    (hGMS : GMSK.GMSLinearStandardLayerListKRankOneStatement) (hL3 : LinearThreeExclusion27)
    (hG23 : G2ThreeExclusion27) (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (h : Hyp G A f) (d : Datum A) {V₁ V₂ Vi : Subgroup G} (hR : Radicals d.V V₁ V₂ (2 ^ f))
    (hW : Vi = V₁ ∨ Vi = V₂) (w : WData d Vi (2 ^ f)) {K : Type} [Field K] [Finite K]
    (D : LeviData A Vi K) (hKc : Nat.card K = 2 ^ f) (hA : w.CaseA f D.lev.range) :
    ∃ C : CaseACoord f w D.lev.range,
      (∃ ι : Multiplicative (Fin 2 → C.F) →* G, Function.Injective ι ∧ ι.range = w.W ∧
        ∀ (n : w.N) (hn : w.projBar n ∈ w.Ebar D.lev.range) (v : Multiplicative (Fin 2 → C.F)),
          (n : G) * ι v * (n : G)⁻¹ = ι (Multiplicative.ofAdd
            ((C.ψ ⟨_, hn⟩ : Matrix (Fin 2) (Fin 2) C.F).mulVec (Multiplicative.toAdd v)))) ∧
      (∃ X : Subgroup G, X ≤ w.Ehat D.lev.range ∧ w.W ⊓ X = ⊥ ∧
        ∀ e ∈ w.Ehat D.lev.range, ∃ a ∈ w.W, ∃ x ∈ X, e = a * x) ∧
      ∀ S : Subgroup G, IsSylowOf 2 S (w.Ehat D.lev.range) → Nonempty (S ≃* unipAll C.F) :=
  seitz31 h.three_le d hR hW (h.normalizer_adj_le d hR hW) w D hKc hA
    (h.commutator_oddCore_Ebar hG hGMS hL3 hG23 hK d hR hW w D hKc)

end Hyp

end CFSG.LocalAnalysis.EvenBN.LinearThree
