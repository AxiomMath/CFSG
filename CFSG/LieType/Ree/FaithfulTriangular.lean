module

public import CFSG.LieType.Chevalley.Native
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits

variable {τ : Tag} {K : Type} [Field K]

theorem exists_apply_ne_zero_of_mul {f g : Module.End K (RootModule τ K)} {a b : Label τ}
    (h : (f * g) (Finsupp.single b 1) a ≠ 0) :
    ∃ c, f (Finsupp.single c 1) a ≠ 0 ∧ g (Finsupp.single b 1) c ≠ 0 := by
  rw [Module.End.mul_apply, ← Finsupp.sum_single (g (Finsupp.single b 1)), Finsupp.sum, map_sum,
    Finsupp.finsetSum_apply] at h
  obtain ⟨c, hc, hc'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [← Finsupp.smul_single_one, map_smul, Finsupp.smul_apply, smul_eq_mul] at hc'
  exact ⟨c, right_ne_zero_of_mul hc', Finsupp.mem_support_iff.mp hc⟩

theorem rootVec_apply_inr (γ : Fin τ.rank → ℤ) (δ : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    rootVec τ K γ (Sum.inr δ) = if γ = δ.1 then 1 else 0 := by
  classical
  by_cases hγ : IsRoot τ γ
  · rw [CFSG.LieType.Chevalley.rootVec_eq_single hγ, Finsupp.single_apply]
    by_cases h : γ = δ.1
    · rw [ite_eq_left h, ite_eq_left (by rw [Sum.inr.injEq]; exact Subtype.ext h)]
    · rw [ite_eq_right h, ite_eq_right fun h' => h (congrArg Subtype.val (Sum.inr_injective h'))]
  · rw [rootVec, dite_eq_right hγ, ite_eq_right fun h : γ = δ.1 => hγ (h ▸ δ.2)]
    rfl

@[expose] def IsUpper (f : Module.End K (RootModule τ K)) : Prop :=
  ∀ a b : Label τ, f (Finsupp.single b 1) a ≠ 0 → labelWt τ b ≤ labelWt τ a

theorem isUpper_one : IsUpper (1 : Module.End K (RootModule τ K)) := by
  intro a b h
  rw [Module.End.one_apply] at h
  obtain ⟨rfl, -⟩ := Finsupp.single_apply_ne_zero.1 h
  exact le_rfl

theorem IsUpper.mul {f g : Module.End K (RootModule τ K)} (hf : IsUpper f) (hg : IsUpper g) :
    IsUpper (f * g) := by
  intro a b h
  obtain ⟨c, h1, h2⟩ := exists_apply_ne_zero_of_mul h
  exact (hg c b h2).trans (hf a c h1)

theorem PreservesWeights.isUpper {f : Module.End K (RootModule τ K)} (hf : PreservesWeights f) :
    IsUpper f :=
  fun a b h => (hf a b h).ge

variable (τ K) in
@[expose] def upperSubgroup : Subgroup (adjointGroup τ K) where
  carrier := {g | IsUpper (glRep _ g) ∧ IsUpper (glRep _ g⁻¹)}
  mul_mem' {g h} hg hh := ⟨by rw [map_mul]; exact hg.1.mul hh.1,
    by rw [mul_inv_rev, map_mul]; exact hh.2.mul hg.2⟩
  one_mem' := ⟨by rw [map_one]; exact isUpper_one, by rw [inv_one, map_one]; exact isUpper_one⟩
  inv_mem' {g} hg := ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

theorem isUpper_of_mem_X {α : Root τ} (hα : 0 < height α.1) {g : adjointGroup τ K}
    (hg : g ∈ (nativeRootSubgroups τ K).X α) : IsUpper (glRep _ g) := by
  intro a b h
  by_cases hab : a = b
  · rw [hab]
  · have h' : ((g : ModGL τ K) : Module.End K (RootModule τ K)) (Finsupp.single b 1) a -
        (Finsupp.single b 1 : RootModule τ K) a ≠ 0 := by
      rwa [Finsupp.single_eq_of_ne hab, sub_zero]
    obtain ⟨k, -, hk⟩ := (nativeRootSubgroups τ K).weight_shift α g hg a b h'
    rw [hk]
    exact le_add_of_nonneg_right (nsmul_nonneg (fun j => (IsRoot.height_pos_iff α.2).1 hα j) k)

theorem labelWt_eq_of_monomial [Finite K] (m : monomialGroup τ K) {a b : Label τ}
    (h : glRep _ (m : adjointGroup τ K) (Finsupp.single b 1) a ≠ 0) :
    labelWt τ a = weylHom τ K m • labelWt τ b :=
  isMonomial_weylHom m a b (by simpa using h)

theorem preservesWeights_of_mem_H [Finite K] {g : adjointGroup τ K}
    (hg : g ∈ (nativeData τ K).H) : PreservesWeights (glRep _ g) := by
  obtain ⟨k, hk, rfl⟩ := RootGroupData.mem_H_iff.mp hg
  intro a b h
  have := labelWt_eq_of_monomial k h
  change weylHom τ K k = 1 at hk
  rwa [hk, one_smul] at this

theorem B_le_upperSubgroup [Finite K] : (nativeData τ K).B ≤ upperSubgroup τ K :=
  sup_le (fun _ hg => ⟨PreservesWeights.isUpper (preservesWeights_of_mem_H hg),
      PreservesWeights.isUpper (preservesWeights_of_mem_H (inv_mem hg))⟩)
    (iSup₂_le fun _ hα _ hg => ⟨isUpper_of_mem_X hα hg, isUpper_of_mem_X hα (inv_mem hg)⟩)

theorem isUpper_of_mem_B [Finite K] {g : adjointGroup τ K} (hg : g ∈ (nativeData τ K).B) :
    IsUpper (glRep _ g) :=
  (B_le_upperSubgroup hg).1

theorem le_inv_smul_of_fixes [Finite K] (m : monomialGroup τ K) {b : adjointGroup τ K}
    (hb : b ∈ (nativeData τ K).B) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (h : glRep _ ((m : adjointGroup τ K) * b) (rootVec τ K β) = rootVec τ K β) :
    β ≤ (weylHom τ K m)⁻¹ • β := by
  rw [CFSG.LieType.Chevalley.rootVec_eq_single hβ] at h
  have hne : (glRep _ (m : adjointGroup τ K) * glRep _ b) (Finsupp.single (Sum.inr ⟨β, hβ⟩) 1)
      (Sum.inr ⟨β, hβ⟩) ≠ 0 := by
    rw [← map_mul, h, Finsupp.single_eq_same]
    exact one_ne_zero
  obtain ⟨c, h1, h2⟩ := exists_apply_ne_zero_of_mul hne
  have e1 : β = weylHom τ K m • labelWt τ c := labelWt_eq_of_monomial m h1
  have e2 : β ≤ labelWt τ c := isUpper_of_mem_B hb _ _ h2
  rwa [e1, inv_smul_smul, ← e1]

theorem inv_smul_eq_of_fixes [Finite K] (m : monomialGroup τ K) {b : adjointGroup τ K}
    (hb : b ∈ (nativeData τ K).B) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (h₁ : glRep _ ((m : adjointGroup τ K) * b) (rootVec τ K β) = rootVec τ K β)
    (h₂ : glRep _ ((m : adjointGroup τ K) * b) (rootVec τ K (-β)) = rootVec τ K (-β)) :
    (weylHom τ K m)⁻¹ • β = β := by
  have e1 := le_inv_smul_of_fixes m hb hβ h₁
  have e2 := le_inv_smul_of_fixes m hb (IsRoot.neg hβ) h₂
  rw [smul_neg, neg_le_neg_iff] at e2
  exact le_antisymm e2 e1

theorem le_of_isUpper_conj [Finite K] (n : monomialGroup τ K)
    (hn : ∀ v : Fin τ.rank → ℤ, weylHom τ K n • v = -v) {g : adjointGroup τ K}
    (hg : IsUpper (glRep _ ((n : adjointGroup τ K)⁻¹ * g * (n : adjointGroup τ K))))
    {a b : Label τ}
    (h : glRep _ g (Finsupp.single b 1) a ≠ 0) : labelWt τ a ≤ labelWt τ b := by
  have hg' : g = (n : adjointGroup τ K) *
      ((n : adjointGroup τ K)⁻¹ * g * (n : adjointGroup τ K)) *
      ((n⁻¹ : monomialGroup τ K) : adjointGroup τ K) := by
    rw [Subgroup.coe_inv]
    group
  rw [hg', map_mul, map_mul] at h
  obtain ⟨c, h1, h2⟩ := exists_apply_ne_zero_of_mul h
  obtain ⟨d, h3, h4⟩ := exists_apply_ne_zero_of_mul h1
  have e1 := labelWt_eq_of_monomial n h3
  have e3 := hg d c h4
  have e4 := labelWt_eq_of_monomial n⁻¹ h2
  have hinv : ∀ v : Fin τ.rank → ℤ, (weylHom τ K n)⁻¹ • v = -v := fun v => by
    rw [inv_smul_eq_iff, hn, neg_neg]
  rw [hn] at e1
  rw [map_inv, hinv] at e4
  rw [e4] at e3
  rw [e1]
  exact neg_le.2 e3

theorem preservesWeights_of_isUpper [Finite K] (n : monomialGroup τ K)
    (hn : ∀ v : Fin τ.rank → ℤ, weylHom τ K n • v = -v) {g : adjointGroup τ K}
    (hg : IsUpper (glRep _ g))
    (hg' : IsUpper (glRep _ ((n : adjointGroup τ K)⁻¹ * g * (n : adjointGroup τ K)))) :
    PreservesWeights (glRep _ g) :=
  fun a b h => le_antisymm (le_of_isUpper_conj n hn hg' h) (hg a b h)

@[expose] def RaisesHeight (s : ℤ) (f : Module.End K (RootModule τ K)) : Prop :=
  ∀ a b : Label τ, f (Finsupp.single b 1) a ≠ 0 →
    s * height (labelWt τ b) < s * height (labelWt τ a)

variable {s : ℤ} {f g : Module.End K (RootModule τ K)}

theorem RaisesHeight.mul_left (hg : PreservesWeights g) (hf : RaisesHeight s f) :
    RaisesHeight s (g * f) := by
  intro a b h
  obtain ⟨c, h1, h2⟩ := exists_apply_ne_zero_of_mul h
  rw [hg a c h1]
  exact hf c b h2

theorem RaisesHeight.mul_right (hf : RaisesHeight s f) (hg : PreservesWeights g) :
    RaisesHeight s (f * g) := by
  intro a b h
  obtain ⟨c, h1, h2⟩ := exists_apply_ne_zero_of_mul h
  rw [← hg c b h2]
  exact hf a c h1

theorem RaisesHeight.sub (hf : RaisesHeight s f) (hg : RaisesHeight s g) :
    RaisesHeight s (f - g) := by
  intro a b h
  rw [LinearMap.sub_apply, Finsupp.sub_apply] at h
  by_cases hf0 : f (Finsupp.single b 1) a = 0
  · rw [hf0, zero_sub, neg_ne_zero] at h
    exact hg a b h
  · exact hf a b hf0

theorem PreservesWeights.sub_one (hf : PreservesWeights f) : PreservesWeights (f - 1) := by
  intro a b h
  rw [LinearMap.sub_apply, Module.End.one_apply, Finsupp.sub_apply] at h
  by_cases hf0 : f (Finsupp.single b 1) a = 0
  · rw [hf0, zero_sub, neg_ne_zero] at h
    obtain ⟨rfl, -⟩ := Finsupp.single_apply_ne_zero.1 h
    rfl
  · exact hf a b hf0

theorem eq_zero_of_raisesHeight (hf : RaisesHeight s f) (hp : PreservesWeights f) : f = 0 := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => ?_)
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_comp,
    LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_contra h
  have h1 := hf a b h
  rw [hp a b h] at h1
  exact lt_irrefl _ h1

theorem raisesHeight_of_mem_X {α : Root τ} (hs : 0 < s * height α.1) {g : adjointGroup τ K}
    (hg : g ∈ (nativeRootSubgroups τ K).X α) : RaisesHeight s (glRep _ g - 1) := by
  intro a b h
  rw [LinearMap.sub_apply, Module.End.one_apply, Finsupp.sub_apply] at h
  obtain ⟨k, hk, hw⟩ := (nativeRootSubgroups τ K).weight_shift α g hg a b h
  have hht : height (labelWt τ a) = height (labelWt τ b) + k * height α.1 := by
    rw [hw]
    simp [height, Finset.sum_add_distrib, Finset.mul_sum]
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  have := mul_pos hk' hs
  rw [hht, mul_add]
  linarith [show s * (k * height α.1) = k * (s * height α.1) by ring]

theorem mul_sub_one_mul (A X B : Module.End K (RootModule τ K)) :
    A * (X - 1) * B = A * X * B - A * B :=
  LinearMap.ext fun v => by
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub]

theorem mul_sub_one (A X : Module.End K (RootModule τ K)) : A * (X - 1) = A * X - A :=
  LinearMap.ext fun v => by
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub]

theorem commute_of_preservesWeights {g x : adjointGroup τ K}
    (hg : PreservesWeights (glRep _ g)) (hgi : PreservesWeights (glRep _ g⁻¹))
    (hz : PreservesWeights (glRep _ (g * x * g⁻¹ * x⁻¹))) (hx : RaisesHeight s (glRep _ x - 1)) :
    g * x = x * g := by
  set z := g * x * g⁻¹ * x⁻¹ with hzdef
  have hzx : z * x = g * x * g⁻¹ := by
    rw [hzdef]
    group
  have h1 : glRep _ g * glRep _ x * glRep _ g⁻¹ = glRep _ z * glRep _ x := by
    rw [← map_mul, ← map_mul, ← map_mul, hzx]
  have h2 : glRep _ g * glRep _ g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have key : glRep _ z - 1 =
      glRep _ g * (glRep _ x - 1) * glRep _ g⁻¹ - glRep _ z * (glRep _ x - 1) := by
    rw [mul_sub_one_mul, h1, h2, mul_sub_one]
    exact (sub_sub_sub_cancel_left (1 : Module.End K (RootModule τ K)) (glRep _ z)
      (glRep _ z * glRep _ x)).symm
  have hz1 : glRep _ z - 1 = 0 := by
    refine eq_zero_of_raisesHeight (s := s) ?_ (PreservesWeights.sub_one hz)
    rw [key]
    exact ((hx.mul_left hg).mul_right hgi).sub (hx.mul_left hz)
  have hz1' : z = 1 := glRep_injective _ (by rw [map_one]; exact sub_eq_zero.1 hz1)
  calc g * x = z * (x * g) := by rw [hzdef]; group
    _ = x * g := by rw [hz1', one_mul]

theorem PreservesWeights.apply_inr {h : Module.End K (RootModule τ K)} (hh : PreservesWeights h)
    (y : RootModule τ K) (γ : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    h y (Sum.inr γ) = h (Finsupp.single (Sum.inr γ) 1) (Sum.inr γ) * y (Sum.inr γ) := by
  classical
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply, mul_add]
  | single c r =>
    rw [← Finsupp.smul_single_one, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul,
      smul_eq_mul]
    by_cases hc : c = Sum.inr γ
    · subst hc
      rw [Finsupp.single_eq_same, mul_one, mul_comm]
    · have h0 : h (Finsupp.single c 1) (Sum.inr γ) = 0 := by
        by_contra hne
        have := hh _ _ hne
        rcases c with i | δ
        · exact γ.2.ne_zero this
        · exact hc (congrArg Sum.inr (Subtype.ext this.symm))
      rw [h0, Finsupp.single_eq_of_ne (Ne.symm hc)]
      ring

theorem xOp_rootVec_apply_add (k : Fin τ.rank) (c : K) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h₁ : α ≠ Pi.single k 1) (h₂ : α ≠ -Pi.single k 1) (hr : IsRoot τ (α + Pi.single k 1)) :
    xOp τ K k c (rootVec τ K α) (Sum.inr ⟨α + Pi.single k 1, hr⟩) =
      ((stringDown τ k α + 1 : ℕ) : K) * c := by
  have hn : ∀ n : ℕ, (α + (n : ℤ) • Pi.single k 1 = α + Pi.single k 1) ↔ n = 1 := by
    intro n
    constructor
    · intro h
      have := congrFun h k
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
        add_right_inj] at this
      exact_mod_cast this
    · rintro rfl
      simp
  rw [xOp_eq_sum_xCoeff, LinearMap.sum_apply, Finsupp.finsetSum_apply]
  simp only [LinearMap.smul_apply, xCoeff_rootVec_of_ne k _ hα h₁ h₂, Finsupp.smul_apply,
    smul_eq_mul, rootVec_apply_inr, hn]
  simp [mul_comm]

theorem stringDown_eq_zero {k : Fin τ.rank} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h₁ : α ≠ Pi.single k 1) (h₂ : α ≠ -Pi.single k 1) (hq : ¬IsRoot τ (α - Pi.single k 1)) :
    stringDown τ k α = 0 := by
  obtain ⟨-, hs⟩ := isRoot_add_smul_single_iff hα k h₁ h₂
  by_contra h0
  apply hq
  have := (hs (-1)).2 ⟨by omega, by omega⟩
  rwa [neg_one_smul, ← sub_eq_add_neg] at this

theorem rootVec_fixed_of_witness {h : Module.End K (RootModule τ K)} (hh : PreservesWeights h)
    {k : Fin τ.rank} (hk : h * xOp τ K k 1 = xOp τ K k 1 * h) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (h₁ : α ≠ Pi.single k 1) (h₂ : α ≠ -Pi.single k 1)
    (hr : IsRoot τ (α + Pi.single k 1)) (hq : ¬IsRoot τ (α - Pi.single k 1))
    (hfix : h (rootVec τ K (α + Pi.single k 1)) = rootVec τ K (α + Pi.single k 1)) :
    h (rootVec τ K α) = rootVec τ K α := by
  have hμ := hh.apply_rootVec hα
  set μ := h (rootVec τ K α) (Sum.inr ⟨α, hα⟩)
  have hx := xOp_rootVec_apply_add k (1 : K) hα h₁ h₂ hr
  rw [stringDown_eq_zero hα h₁ h₂ hq, zero_add, Nat.cast_one, mul_one] at hx
  have key := congrArg (fun f : Module.End K (RootModule τ K) =>
    f (rootVec τ K α) (Sum.inr ⟨α + Pi.single k 1, hr⟩)) hk
  simp only [Module.End.mul_apply] at key
  rw [PreservesWeights.apply_inr hh, ← CFSG.LieType.Chevalley.rootVec_eq_single hr, hfix, hμ,
    map_smul, Finsupp.smul_apply, smul_eq_mul, hx, rootVec_apply_inr, ite_eq_left rfl] at key
  rw [hμ, show μ = 1 by simpa using key.symm, one_smul]

theorem rootVec_fixed_reflect {h : Module.End K (RootModule τ K)} {i : Fin τ.rank}
    (hn : h * (weylElt τ K i 1 : Module.End K (RootModule τ K)) =
      (weylElt τ K i 1 : Module.End K (RootModule τ K)) * h)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hfix : h (rootVec τ K α) = rootVec τ K α) :
    h (rootVec τ K (reflect τ i α)) = rootVec τ K (reflect τ i α) := by
  have hw := weylElt_rootVec (R := K) i 1 hα
  rw [one_zpow, Units.val_one, mul_one] at hw
  have hu : ((-1 : K) ^ stringDown τ i α) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  have key := congrArg (fun f : Module.End K (RootModule τ K) => f (rootVec τ K α)) hn
  simp only [Module.End.mul_apply, hfix, hw, map_smul] at key
  exact smul_right_injective _ hu key

theorem rootVec_fixed_of_simple {h : Module.End K (RootModule τ K)}
    (hn : ∀ i, h * (weylElt τ K i 1 : Module.End K (RootModule τ K)) =
      (weylElt τ K i 1 : Module.End K (RootModule τ K)) * h)
    (hs : ∀ j, h (rootVec τ K (Pi.single j 1)) = rootVec τ K (Pi.single j 1))
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) : h (rootVec τ K α) = rootVec τ K α := by
  induction hα with
  | basis j => exact hs j
  | reflect i hv ih => exact rootVec_fixed_reflect (hn i) hv ih

theorem commute_weylElt {h : Module.End K (RootModule τ K)} {i : Fin τ.rank}
    (hx : h * xOp τ K i 1 = xOp τ K i 1 * h) (hy : h * yOp τ K i (-1) = yOp τ K i (-1) * h) :
    h * (weylElt τ K i 1 : Module.End K (RootModule τ K)) =
      (weylElt τ K i 1 : Module.End K (RootModule τ K)) * h := by
  have hw : (weylElt τ K i 1 : Module.End K (RootModule τ K)) =
      xOp τ K i 1 * yOp τ K i (-1) * xOp τ K i 1 := by
    rw [coe_weylElt, inv_one, Units.val_one]
  rw [hw]
  calc h * (xOp τ K i 1 * yOp τ K i (-1) * xOp τ K i 1)
      = (h * xOp τ K i 1) * yOp τ K i (-1) * xOp τ K i 1 := by simp only [mul_assoc]
    _ = xOp τ K i 1 * (h * yOp τ K i (-1)) * xOp τ K i 1 := by
      rw [hx]
      simp only [mul_assoc]
    _ = xOp τ K i 1 * yOp τ K i (-1) * (h * xOp τ K i 1) := by
      rw [hy]
      simp only [mul_assoc]
    _ = xOp τ K i 1 * yOp τ K i (-1) * xOp τ K i 1 * h := by
      rw [hx]
      simp only [mul_assoc]

theorem rootVec_fixed_of_foldr {h : Module.End K (RootModule τ K)}
    (hn : ∀ i, h * (weylElt τ K i 1 : Module.End K (RootModule τ K)) =
      (weylElt τ K i 1 : Module.End K (RootModule τ K)) * h)
    {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) (u : List (Fin τ.rank))
    (hfix : h (rootVec τ K (u.foldr (reflect τ) v)) = rootVec τ K (u.foldr (reflect τ) v)) :
    h (rootVec τ K v) = rootVec τ K v := by
  induction u with
  | nil => exact hfix
  | cons i u ih =>
    apply ih
    have hβ : IsRoot τ (u.foldr (reflect τ) v) := by
      clear ih hfix
      induction u with
      | nil => exact hv
      | cons j u ih' => exact .reflect j ih'
    have := rootVec_fixed_reflect (hn i) (.reflect i hβ) hfix
    rwa [reflect_reflect] at this

theorem eq_one_of_fixes_simple {h : Module.End K (RootModule τ K)}
    (hx : ∀ i, h * xOp τ K i 1 = xOp τ K i 1 * h)
    (hy : ∀ i, h * yOp τ K i (-1) = yOp τ K i (-1) * h)
    (hs : ∀ j, h (rootVec τ K (Pi.single j 1)) = rootVec τ K (Pi.single j 1)) : h = 1 := by
  have hr : ∀ α, IsRoot τ α → h (rootVec τ K α) = rootVec τ K α :=
    fun α hα => rootVec_fixed_of_simple (fun i => commute_weylElt (hx i) (hy i)) hs hα
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.one_apply]
  rcases b with i | ⟨α, hα⟩
  · change h (hVec τ K i) = hVec τ K i
    have key := congrArg (fun f : Module.End K (RootModule τ K) =>
      f (rootVec τ K (-Pi.single i 1))) (hx i)
    simp only [Module.End.mul_apply, hr _ (isRoot_neg_single τ i), xOp_rootVec_neg_single',
      one_smul, one_pow, map_add, hr _ (isRoot_single τ i)] at key
    exact add_left_cancel (add_right_cancel key)
  · rw [← CFSG.LieType.Chevalley.rootVec_eq_single hα]
    exact hr α hα

end CFSG.LieType.Ree
