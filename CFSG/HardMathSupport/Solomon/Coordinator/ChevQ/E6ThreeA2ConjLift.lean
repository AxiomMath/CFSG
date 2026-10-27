module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourSc

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

set_option linter.unusedSectionVars false

section PinnedPow

variable {k : Type} [Field k]
  {p : ℕ} [CharP k p]

theorem pinnedX_pow_eq_one_char (γ : Fin Tag.E6.rank → ℤ) (c : k) :
    pinnedX Tag.E6 k γ c ^ p = 1 := by
  have h : ∀ n : ℕ, pinnedX Tag.E6 k γ c ^ n = pinnedX Tag.E6 k γ (n • c) := by
    intro n
    induction n with
    | zero => rw [pow_zero, zero_smul, pinnedX_zero]
    | succ n ih => rw [pow_succ, ih, succ_nsmul, pinnedX_add]
  rw [h, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, pinnedX_zero]

end PinnedPow

section Lift


variable {k : Type} [Field k] [Finite k] {p : ℕ} [hpp : Fact p.Prime] [CharP k p]

theorem commute_minTorus_of_pinnedX_char (hp3 : p ≠ 3) (u : Fin Tag.E6.rank → kˣ)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ rootCharKernel (e6RootParams u)) (c : k)
    {gl : e6Data_valid.minGroup k}
    (hgl : ((e6Isogeny k gl : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = pinnedX Tag.E6 k γ c) :
    gl * minTorus e6Data_valid k u = minTorus e6Data_valid k u * gl := by
  set T := minTorus e6Data_valid k u with hT
  set x := pinnedX Tag.E6 k γ c with hx
  set d := rootDiagUnit Tag.E6 (e6RootParams u) with hd
  have hπT : ((e6Isogeny k T : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = d :=
    e6Isogeny_minTorus u
  have hxp : x ^ p = 1 := pinnedX_pow_eq_one_char γ c
  have hxd : d * x = x * d := by
    have h := rootDiagUnit_conj_pinnedX (e6RootParams u) hγ.1 c
    rw [hγ.2, Units.val_one, one_mul, mul_inv_eq_iff_eq_mul] at h
    exact h
  have hsq : gl ^ p ∈ Subgroup.center (e6Data_valid.minGroup k) := by
    refine mem_center_of_isogeny_eq_one ?_
    rw [map_pow, Subgroup.coe_pow, hgl, hxp]
  set κ := gl * T * gl⁻¹ * T⁻¹ with hκ
  have hκc : κ ∈ Subgroup.center (e6Data_valid.minGroup k) := by
    refine mem_center_of_isogeny_eq_one ?_
    rw [hκ, map_mul, map_mul, map_mul, map_inv, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hgl, hπT]
    calc x * d * x⁻¹ * d⁻¹ = (x * d) * x⁻¹ * d⁻¹ := rfl
      _ = (d * x) * x⁻¹ * d⁻¹ := by rw [hxd]
      _ = 1 := by group
  have hκ' := Subgroup.mem_center_iff.1 hκc
  have hglT : gl * T * gl⁻¹ = κ * T := by rw [hκ]; group
  have hpow : ∀ n : ℕ, gl ^ n * T * (gl ^ n)⁻¹ = κ ^ n * T := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc gl ^ (n + 1) * T * (gl ^ (n + 1))⁻¹
          = gl * (gl ^ n * T * (gl ^ n)⁻¹) * gl⁻¹ := by group
        _ = gl * (κ ^ n * T) * gl⁻¹ := by rw [ih]
        _ = (gl * κ ^ n) * T * gl⁻¹ := by group
        _ = (κ ^ n * gl) * T * gl⁻¹ := by
          rw [(Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ hκc n)) gl]
        _ = κ ^ n * (gl * T * gl⁻¹) := by group
        _ = κ ^ (n + 1) * T := by rw [hglT, pow_succ]; group
  have hκp : κ ^ p = 1 := by
    have h1 := hpow p
    have h2 : gl ^ p * T * (gl ^ p)⁻¹ = T := by
      rw [← Subgroup.mem_center_iff.1 hsq T]
      group
    rw [h2] at h1
    calc κ ^ p = κ ^ p * T * T⁻¹ := by group
      _ = T * T⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel T
  obtain ⟨v, hv, hv3⟩ := exists_minTorus_of_mem_center_E6 hκc
  have hκ3 : κ ^ 3 = 1 := by
    rw [hv, ← map_pow]
    have : v ^ 3 = 1 := funext fun j => by simpa using hv3 j
    rw [this, map_one]
  have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hpp.out Nat.prime_three).2 hp3
  have hκ1 : κ = 1 := by
    have h1 : orderOf κ ∣ p := orderOf_dvd_of_pow_eq_one hκp
    have h2 : orderOf κ ∣ 3 := orderOf_dvd_of_pow_eq_one hκ3
    have h3 : orderOf κ ∣ Nat.gcd p 3 := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one] at h3
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_one h3)
  have h3 : gl * T * gl⁻¹ = T := by rw [hglT, hκ1, one_mul]
  calc gl * T = gl * T * gl⁻¹ * gl := by group
    _ = T * gl := by rw [h3]

theorem commute_minTorus_of_mem_toralRootGroup_char (hp3 : p ≠ 3) (u : Fin Tag.E6.rank → kˣ)
    {g : ModGL Tag.E6 k} (hg : g ∈ toralRootGroup Tag.E6 k (e6RootParams u))
    {gl : e6Data_valid.minGroup k}
    (hgl : ((e6Isogeny k gl : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = g) :
    gl * minTorus e6Data_valid k u = minTorus e6Data_valid k u * gl := by
  set π : e6Data_valid.minGroup k →* ModGL Tag.E6 k :=
    (adjointGroup Tag.E6 k).subtype.comp (e6Isogeny k) with hπ
  set X : Set (ModGL Tag.E6 k) := Set.range (fun q : Fin Tag.E6.rank × kˣ =>
      torusElt Tag.E6 k q.1 q.2) ∪
    {y | ∃ γ ∈ rootCharKernel (e6RootParams u), ∃ c : k, y = pinnedX Tag.E6 k γ c} with hX
  have hker : ∀ g' : e6Data_valid.minGroup k, π g' = 1 → ∀ y, g' * y = y * g' := fun g' h y =>
    (Subgroup.mem_center_iff.1 (mem_center_of_isogeny_eq_one h) y).symm
  have hgen : ∀ y ∈ X, ∃ g', π g' = y ∧ g' * minTorus e6Data_valid k u =
      minTorus e6Data_valid k u * g' := by
    rintro y (⟨⟨i, t⟩, rfl⟩ | ⟨γ, hγ, c, rfl⟩)
    · refine ⟨e6Data_valid.hm k i t, ?_, ?_⟩
      · change ((e6Isogeny k (e6Data_valid.hm k i t) : adjointGroup Tag.E6 k) :
          ModGL Tag.E6 k) = torusElt Tag.E6 k i t
        rw [torusElt_eq_rootDiagUnit]
        exact e6Isogeny_hm_eq i t
      · rw [← minTorus_mulSingle, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨g', hg'⟩ := e6Isogeny_surjective k ⟨pinnedX Tag.E6 k γ c,
        pinnedX_mem_adjointGroup γ c⟩
      have hg'' : ((e6Isogeny k g' : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
          pinnedX Tag.E6 k γ c := by rw [hg']
      exact ⟨g', hg'', commute_minTorus_of_pinnedX_char hp3 u hγ c hg''⟩
  have hle : toralRootGroup Tag.E6 k (e6RootParams u) ≤ Subgroup.closure X := by
    refine sup_le ?_ ?_
    · exact Subgroup.closure_mono Set.subset_union_left
    · refine iSup₂_le fun γ hγ => (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      exact Subgroup.subset_closure (Set.mem_union_right _ ⟨γ, hγ, c, rfl⟩)
  exact (commute_of_mem_closure_lift π _ hker hgen g (hle hg)).2 gl hgl

theorem rootChar_e6Shift_of_commute_lift_char (hp3 : p ≠ 3) (u : Fin Tag.E6.rank → kˣ)
    {cl : e6Data_valid.minGroup k} (hcl : cl * minTorus e6Data_valid k u =
      minTorus e6Data_valid k u * cl)
    {w : WeylGroup Tag.E6} {h u' v' : ModGL Tag.E6 k} (hh : h ∈ torusGroup Tag.E6 k)
    (hu' : u' ∈ rootSpan Tag.E6 k (rootCharKernel (e6RootParams u)))
    (hv' : v' ∈ rootSpan Tag.E6 k (rootCharKernel (e6RootParams u)))
    (hdec : ((e6Isogeny k cl : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      h * u' * canonicalRep (coxeterSystem Tag.E6) k w * v')
    (hw : w ∈ rootCharStabilizer (e6RootParams u)) :
    rootChar (e6RootParams u) (e6Shift w) = 1 := by
  set a := e6RootParams u with ha
  set T := minTorus e6Data_valid k u with hT
  have hM₁ : h * u' ∈ toralRootGroup Tag.E6 k a :=
    mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hu')
  have hM₂ : v' ∈ toralRootGroup Tag.E6 k a := Subgroup.mem_sup_right hv'
  have hadj : ∀ {x : ModGL Tag.E6 k}, x ∈ toralRootGroup Tag.E6 k a → x ∈ adjointGroup Tag.E6 k :=
    fun hx => (toralRootGroup_le a hx).1
  obtain ⟨l₁, hl₁⟩ := e6Isogeny_surjective k ⟨h * u', hadj hM₁⟩
  obtain ⟨l₂, hl₂⟩ := e6Isogeny_surjective k ⟨v', hadj hM₂⟩
  have hl₁' : ((e6Isogeny k l₁ : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = h * u' := by
    rw [hl₁]
  have hl₂' : ((e6Isogeny k l₂ : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = v' := by
    rw [hl₂]
  have c₁ := commute_minTorus_of_mem_toralRootGroup_char hp3 u hM₁ hl₁'
  have c₂ := commute_minTorus_of_mem_toralRootGroup_char hp3 u hM₂ hl₂'
  set y := l₁⁻¹ * cl * l₂⁻¹ with hy
  have hyT : T * y = y * T := by
    have e1 : l₁⁻¹ * T = T * l₁⁻¹ := by
      calc l₁⁻¹ * T = l₁⁻¹ * (T * l₁) * l₁⁻¹ := by group
        _ = l₁⁻¹ * (l₁ * T) * l₁⁻¹ := by rw [c₁]
        _ = T * l₁⁻¹ := by group
    have e2 : l₂⁻¹ * T = T * l₂⁻¹ := by
      calc l₂⁻¹ * T = l₂⁻¹ * (T * l₂) * l₂⁻¹ := by group
        _ = l₂⁻¹ * (l₂ * T) * l₂⁻¹ := by rw [c₂]
        _ = T * l₂⁻¹ := by group
    calc T * y = T * l₁⁻¹ * cl * l₂⁻¹ := by rw [hy]; group
      _ = l₁⁻¹ * (T * cl) * l₂⁻¹ := by rw [← e1]; group
      _ = l₁⁻¹ * (cl * T) * l₂⁻¹ := by rw [hcl]
      _ = l₁⁻¹ * cl * (T * l₂⁻¹) := by group
      _ = l₁⁻¹ * cl * (l₂⁻¹ * T) := by rw [e2]
      _ = y * T := by rw [hy]; group
  have hyπ : ((e6Isogeny k y : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      rootDiagUnit Tag.E6 (e6RootParams (1 : Fin Tag.E6.rank → kˣ)) *
        canonicalRep (coxeterSystem Tag.E6) k w := by
    have e : e6RootParams (1 : Fin Tag.E6.rank → kˣ) = 1 := by
      funext j
      simp [e6RootParams]
    rw [e, rootDiagUnit_one, one_mul, hy, map_mul, map_mul, map_inv, map_inv, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hl₁', hl₂', hdec]
    group
  exact rootChar_e6Shift_of_commute hyT (e6Isogeny_minTorus u) hyπ rfl rfl hw

end Lift

section Centralizer


variable {k : Type} [Field k] [Finite k] {p : ℕ} [hpp : Fact p.Prime] [CharP k p]

theorem mem_toralRootGroup_of_commute_lift_char (hp3 : p ≠ 3) (u : Fin Tag.E6.rank → kˣ)
    (hu3 : ∀ j, e6RootParams u j ^ 3 = 1) {c : ModGL Tag.E6 k}
    (hcC : c ∈ toralCentralizer Tag.E6 k (e6RootParams u)) {cl : e6Data_valid.minGroup k}
    (hcl : ((e6Isogeny k cl : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = c)
    (hcomm : cl * minTorus e6Data_valid k u = minTorus e6Data_valid k u * cl) :
    c ∈ toralRootGroup Tag.E6 k (e6RootParams u) := by
  obtain ⟨w, hw, h, hh, u', hu', v', hv', hdec⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors Tag.E6 k (e6RootParams u)).1 c hcC
  have hdec' : ((e6Isogeny k cl : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      h * u' * canonicalRep (coxeterSystem Tag.E6) k w * v' := by
    rw [hcl, hdec]
  have hshift := rootChar_e6Shift_of_commute_lift_char hp3 u hcomm hh
    (rootSpan_mono Set.inter_subset_left hu') (rootSpan_mono Set.inter_subset_left hv') hdec' hw
  have hwS : w ∈ kernelReflectionGroup (e6RootParams u) :=
    mem_kernelReflectionGroup_of_e6Shift (e6RootParams u) hu3 hw hshift
  have hnM : canonicalRep (coxeterSystem Tag.E6) k w ∈
      toralRootGroup Tag.E6 k (e6RootParams u) := by
    have hk := kernelReflectionGroup_le_ker (K := k) (e6RootParams u)
      (show (⟨w, hw⟩ : rootCharStabilizerSubgroup (e6RootParams u)) ∈
        (kernelReflectionGroup (e6RootParams u)).subgroupOf
          (rootCharStabilizerSubgroup (e6RootParams u)) from hwS)
    rw [MonoidHom.mem_ker, weylToralQuotientHom_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hk
    exact hk
  rw [hdec]
  exact mul_mem (mul_mem (mul_mem (Subgroup.mem_sup_left hh)
    (Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hu'))) hnM)
    (Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hv'))

end Centralizer

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
