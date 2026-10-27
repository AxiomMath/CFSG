module

public import CFSG.ClassicalInvolution.Uniform.U8Shape

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.RouteD (conjSub_mem_fundamentalSubgroups)
open scoped MatrixGroups commutatorElement


section Layer3

variable {K : Type*} [Group K]

@[expose] def LayerAt3 (Fund : Set (Subgroup K)) (R₀ : Subgroup K) : Prop :=
  ∃ L : Subgroup K, CFSG.Open.IsQuasisimple ↥L ∧ L ≤ Subgroup.centralizer (R₀ : Set K) ∧
    (∀ x ∈ Subgroup.centralizer (R₀ : Set K), x ^ 3 = 1 → x ∈ L) ∧ L ∉ Fund

@[expose] def StdLayer3 (R₀ R₂ : Subgroup K) : Prop :=
  ∃ L : Subgroup K, CFSG.Open.IsQuasisimple ↥L ∧ L ≤ Subgroup.centralizer (R₀ : Set K) ∧
    (∀ x ∈ Subgroup.centralizer (R₀ : Set K), x ^ 3 = 1 → x ∈ L) ∧ R₂ ≤ L ∧ R₂ ≠ L

theorem layerAt3_of_stdLayer3 [Finite K] {Fund : Set (Subgroup K)}
    (hsingle : ∀ R ∈ Fund, ∀ R' ∈ Fund, ∃ g : K, R' = conjSub g R) {R₀ R₂ : Subgroup K}
    (hR₂ : R₂ ∈ Fund) (h : StdLayer3 R₀ R₂) : LayerAt3 Fund R₀ := by
  obtain ⟨L, hLq, hLC, hL3, hR₂L, hne⟩ := h
  exact ⟨L, hLq, hLC, hL3, not_mem_of_le_of_ne hsingle hR₂ hR₂L hne⟩

theorem LayerAt3.conj {Fund : Set (Subgroup K)} (hFund : ∀ S ∈ Fund, ∀ g : K, conjSub g S ∈ Fund)
    {R : Subgroup K} (h : LayerAt3 Fund R) (g : K) : LayerAt3 Fund (conjSub g R) := by
  obtain ⟨L, hLq, hLC, hL3, hLF⟩ := h
  refine ⟨conjSub g L, (open_isQuasisimple_conjSub g).2 hLq,
    (conjSub_le_centralizer_iff g).2 hLC, ?_, ?_⟩
  · intro x hx hx3
    have hx' : g⁻¹ * x * g ∈ Subgroup.centralizer (R : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have h1 := Subgroup.mem_centralizer_iff.mp hx (g * r * g⁻¹) (conj_mem_conjSub hr)
      calc r * (g⁻¹ * x * g) = g⁻¹ * ((g * r * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * r * g⁻¹)) * g := by rw [h1]
        _ = (g⁻¹ * x * g) * r := by group
    have hx'3 : (g⁻¹ * x * g) ^ 3 = 1 := by
      have := conj_pow (a := g⁻¹) (b := x) (i := 3)
      rw [inv_inv] at this
      rw [this, hx3]
      group
    exact ⟨g⁻¹ * x * g, hL3 _ hx' hx'3, by
      change g * (g⁻¹ * x * g) * g⁻¹ = x
      group⟩
  · intro hmem
    apply hLF
    have := hFund _ hmem g⁻¹
    rwa [conjSub_inv_conjSub] at this

end Layer3

section Group3

variable {K : Type*} [Group K]

theorem le_of_pow_three_of_le_sup_of_commutes {A B : Subgroup K}
    (h : A ≤ Subgroup.centralizer (B : Set K))
    (hA2 : ∀ a ∈ A, (∀ y ∈ A, a * y = y * a) → a * a = 1) {x : K} (hx : x ∈ A ⊔ B)
    (hxA : x ∈ Subgroup.centralizer (A : Set K)) (hx3 : x ^ 3 = 1) : x ∈ B := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_centralizer h).mp hx
  have hAB : ∀ {a' b' : K}, a' ∈ A → b' ∈ B → a' * b' = b' * a' := fun {a' b'} ha' hb' =>
    (Subgroup.mem_centralizer_iff.mp (h ha') b' hb').symm
  have hacen : ∀ y ∈ A, a * y = y * a := by
    intro y hy
    have h1 := Subgroup.mem_centralizer_iff.mp hxA y hy
    have h2 : y * a * b = a * y * b := by
      calc y * a * b = y * (a * b) := by group
        _ = a * b * y := h1
        _ = a * (b * y) := by group
        _ = a * (y * b) := by rw [(hAB hy hb).symm]
        _ = a * y * b := by group
    exact (mul_right_cancel h2).symm
  have ha2 : a * a = 1 := hA2 a ha hacen
  have hcomm : Commute a b := hAB ha hb
  have h3 : (a * b) ^ 3 = a ^ 3 * b ^ 3 := hcomm.mul_pow 3
  have ha3 : a ^ 3 = a := by
    calc a ^ 3 = a * (a * a) := pow_three a
      _ = a := by rw [ha2, mul_one]
  rw [h3, ha3] at hx3
  have hbinv : b ^ 3 = a⁻¹ := eq_inv_of_mul_eq_one_right hx3
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have haB : a ∈ B := by
    rw [← hainv, ← hbinv]
    exact B.pow_mem hb 3
  exact B.mul_mem haB hb

theorem central_sq_of_equiv_sl2 {G : Type} [Group G] {R : Subgroup G} {F : Type} [Field F]
    [Finite F] (hF : Odd (Nat.card F)) (eR : R ≃* SL(2, F)) :
    ∀ a ∈ R, (∀ y ∈ R, a * y = y * a) → a * a = 1 := by
  intro a ha hcen
  rcases CFSG.ClassicalInvolution.Asc77.eq_one_or_eq_sl2Inv_of_central eR ha
      hcen with h1 | h1
  · rw [h1, mul_one]
  · rw [h1]
    exact CFSG.ClassicalInvolution.Asc77.sl2Inv_mul_self hF eR

end Group3

section Toral

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem torus_mul_self_eq_one (hK3 : Nat.card K = 3) {h : ModGL τ K} (hh : h ∈ torusGroup τ K) :
    h * h = 1 := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  rw [← rootDiagUnit_mul]
  have : l * l = 1 := by
    funext i
    have h2 : Nat.card Kˣ = 2 := by rw [Nat.card_units, hK3]
    have h3 := pow_card_eq_one' (G := Kˣ) (x := l i)
    rw [h2, pow_two] at h3
    simpa using h3
  rw [this]
  exact rootDiagUnit_one

theorem toralCentralizer_pow_three_mem (hK : ringChar K ≠ 2) (hK3 : Nat.card K = 3)
    {a : Fin τ.rank → Kˣ} (ha : ∀ i, a i = 1 ∨ a i = -1) {x : ModGL τ K}
    (hx : x ∈ toralCentralizer τ K a) (hx3 : x ^ 3 = 1) :
    x ∈ rootSpan τ K (rootCharKernel a) := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  set X := toralCentralizer τ K a with hX
  set S := rootSpan τ K (rootCharKernel a) with hS
  obtain ⟨-, -, -, -, φ, hφ, -⟩ := Chevalley_toral_centralizer_root_generated_quotient τ K a
  have hNnorm : (S.subgroupOf X).Normal :=
    (odd_toral_involution_centralizer_p_component_root_reduction τ K hK a ha).2.1
  set M' := (toralRootGroup τ K a).subgroupOf X with hM'
  have hsq : ∀ y : X ⧸ M', y * y = 1 := by
    intro y
    obtain ⟨q, rfl⟩ := hφ y
    obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hc := orderOf_dvd_two_of_charQuotient (maskChar (signTupleBits a))
      (QuotientGroup.mk ⟨w, (mem_rootCharStabilizer_iff hK ha).1 hw⟩ :
        CharQuotient (maskChar (signTupleBits a)))
    have hq1 := orderOf_dvd_iff_pow_eq_one.1 hc
    rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq1
    rw [← map_mul]
    convert map_one φ
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      kernelReflectionGroup_eq_kernelWeylGroup hK ha]
    exact hq1
  set xX : X := ⟨x, hx⟩ with hxXdef
  have hxX3 : xX ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hxM : xX ∈ M' := by
    have h1 := hsq (QuotientGroup.mk xX)
    have h3 : (QuotientGroup.mk xX : X ⧸ M') ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, hxX3, QuotientGroup.mk_one]
    have : (QuotientGroup.mk xX : X ⧸ M') = 1 := by
      calc (QuotientGroup.mk xX : X ⧸ M')
          = (QuotientGroup.mk xX) ^ 3 * ((QuotientGroup.mk xX) * (QuotientGroup.mk xX))⁻¹ := by
            group
        _ = 1 := by rw [h3, h1]; simp
    exact (QuotientGroup.eq_one_iff xX).1 this
  have h2 : M' = (torusGroup τ K).subgroupOf X ⊔ S.subgroupOf X :=
    Subgroup.subgroupOf_sup (torusGroup_le_toralCentralizer a)
      (rootSpan_rootCharKernel_le_toralCentralizer a)
  set π := QuotientGroup.mk' (S.subgroupOf X) with hπdef
  have hN : (S.subgroupOf X).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hπ : π xX ∈ ((torusGroup τ K).subgroupOf X).map π := by
    have : π xX ∈ M'.map π := Subgroup.mem_map_of_mem π hxM
    rw [h2, Subgroup.map_sup, hN, sup_bot_eq] at this
    exact this
  obtain ⟨t, ht, hπt⟩ := hπ
  have ht2 : t * t = 1 :=
    Subtype.ext (torus_mul_self_eq_one hK3 (Subgroup.mem_subgroupOf.1 ht))
  have hπ1 : π xX = 1 := by
    have h1 : π xX * π xX = 1 := by rw [← hπt, ← map_mul, ht2, map_one]
    have h3 : π xX ^ 3 = 1 := by rw [← map_pow, hxX3, map_one]
    calc π xX = (π xX) ^ 3 * (π xX * π xX)⁻¹ := by group
      _ = 1 := by rw [h3, h1]; simp
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff xX).1 hπ1)

end Toral

section Adj

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem stdLayer3_adjoint (hK : ringChar K ≠ 2) (hK3 : Nat.card K = 3) (k : Fin τ.rank)
    {δ₂ δ₃ : Fin τ.rank → ℤ} (hS : LayerShape (zChar τ k) (Pi.single k 1) δ₂ δ₃)
    (hZ : ∀ a ∈ (rootGroup (rootOperatorFamily τ) K (Pi.single k 1) ⊔
        rootGroup (rootOperatorFamily τ) K (-Pi.single k 1)),
      (∀ y ∈ (rootGroup (rootOperatorFamily τ) K (Pi.single k 1) ⊔
        rootGroup (rootOperatorFamily τ) K (-Pi.single k 1)), a * y = y * a) → a * a = 1) :
    StdLayer3 (rootGroup (rootOperatorFamily τ) K (Pi.single k 1) ⊔
        rootGroup (rootOperatorFamily τ) K (-Pi.single k 1))
      (rootGroup (rootOperatorFamily τ) K δ₂ ⊔ rootGroup (rootOperatorFamily τ) K (-δ₂)) := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  set F := rootOperatorFamily τ with hF
  set χ := zChar τ k with hχ
  set e : Fin τ.rank → ℤ := Pi.single k 1 with he
  set i₁ : KernelComponent χ := Quotient.mk _ ⟨e, hS.mem_e⟩ with hi₁
  set i₂ : KernelComponent χ := Quotient.mk _ ⟨δ₂, hS.mem₂⟩ with hi₂
  have hi12 : i₁ ≠ i₂ := hS.mk_e_ne
  have hi21 : i₂ ≠ i₁ := fun h => hi12 h.symm
  set S₁ := componentRootSpan K χ i₁ with hS₁def
  set S₂ := componentRootSpan K χ i₂ with hS₂def
  have hS₁le : S₁ ≤ adjointGroup τ K :=
    (componentRootSpan_le K i₁).trans (rootSpan_le_adjointGroup K _)
  have hS₂le : S₂ ≤ adjointGroup τ K :=
    (componentRootSpan_le K i₂).trans (rootSpan_le_adjointGroup K _)
  have hS₁ : S₁ = rootSubgroup τ K e ⊔ rootSubgroup τ K (-e) := by
    have hset : {α | ∃ h : α ∈ kernelRoots χ,
        (Quotient.mk (kernelRootSetoid χ) ⟨α, h⟩ : KernelComponent χ) = i₁} = {e, -e} := by
      ext α
      constructor
      · rintro ⟨h, hα⟩
        exact (hS.mk_eq_e_iff α h).1 hα
      · rintro (rfl | rfl)
        · exact ⟨hS.mem_e, rfl⟩
        · exact ⟨neg_mem_kernelRoots hS.mem_e, (hS.mk_eq_e_iff _ _).2 (Or.inr rfl)⟩
    change rootSpan τ K _ = _
    rw [hset, CFSG.LieType.Chevalley.OddToralFixed.rootSpan_pair]
  set G := ↥(adjointGroup τ K) with hG
  set Rstd : Subgroup G := rootGroup F K e ⊔ rootGroup F K (-e) with hRstd
  have hRstd' : Rstd = S₁.subgroupOf (adjointGroup τ K) := by
    rw [hS₁, hRstd]
    exact (subgroupOf_rootSubgroup_sup_eq F hS.mem_e.1).symm
  have mem_Rstd : ∀ y : G, y ∈ Rstd ↔ (y : ModGL τ K) ∈ S₁ := fun y => by
    rw [hRstd', Subgroup.mem_subgroupOf]
  set L : Subgroup G := S₂.subgroupOf (adjointGroup τ K) with hL
  have mem_L : ∀ y : G, y ∈ L ↔ (y : ModGL τ K) ∈ S₂ := fun y => Subgroup.mem_subgroupOf
  have hG4 : ∀ δ (h : δ ∈ kernelRoots χ), δ ≠ e → δ ≠ -e → rootGroup F K δ ≤ L := by
    intro δ h hne hne'
    have hle : rootSubgroup τ K δ ≤ S₂ := by
      have := rootSubgroup_le_componentRootSpan K (χ := χ) ⟨δ, h⟩
      rwa [hS.conn δ h hne hne'] at this
    rw [← subgroupOf_rootSubgroup_eq_rootGroup F h.1]
    exact fun x hx => hle hx
  refine ⟨L, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hδ₂neg : δ₂ ≠ -δ₂ := fun h => (hS.mem₂.1.ne_zero) (funext fun j => by
      have := congrFun h j
      simp only [Pi.neg_apply] at this
      simp only [Pi.zero_apply]
      omega)
    have hmem : ∀ γ (h : γ ∈ kernelRoots χ), γ ≠ e → γ ≠ -e → γ ∈ componentRoots χ i₂ :=
      fun γ h hne hne' => ⟨h, hS.conn γ h hne hne'⟩
    have hcard : 2 < (componentRoots χ i₂).ncard := by
      have hfin : (componentRoots χ i₂).Finite := by
        refine (finite_setOf_isRoot τ).subset fun γ hγ => ?_
        obtain ⟨hγ', -⟩ := hγ
        exact hγ'.1
      rw [Set.two_lt_ncard_iff hfin]
      refine ⟨δ₂, δ₃, -δ₂, hmem δ₂ hS.mem₂ hS.ne₂ hS.ne₂',
        hmem δ₃ hS.mem₃ hS.ne₃ hS.ne₃',
        hmem (-δ₂) (neg_mem_kernelRoots hS.mem₂) ?_ ?_, hS.ne₃₂.symm, hδ₂neg, ?_⟩
      · intro h
        exact hS.ne₂' (neg_eq_iff_eq_neg.mp h)
      · intro h
        exact hS.ne₂ (neg_inj.mp h)
      · intro h
        exact hS.ne₃₂' h
    have hq : CFSG.IsQuasisimple ↥S₂ := isQuasisimple_componentRootSpan hK hcard
    exact (open_isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hS₂le)).2 (open_isQuasisimple hq)
  ·
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : (x : ModGL τ K) ∈ Subgroup.centralizer (S₁ : Set (ModGL τ K)) :=
      componentRootSpan_le_centralizer K hi21 ((mem_L x).1 hx)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h1 _ ((mem_Rstd y).1 hy))
  ·
    intro x hx hx3
    set z₀ : G := torusHom K k (-1) with hz₀
    have hz₀R : z₀ ∈ Rstd := torus_le_rankOne k ⟨-1, rfl⟩
    have hz₀val : (z₀ : ModGL τ K) = rootDiagUnit τ (zTuple τ K k) :=
      torusElt_eq_rootDiagUnit k (-1)
    have hb := zTuple_mem (τ := τ) (K := K) k
    have hCz := centralizer_eq_subgroupOf_toralCentralizer (zTuple τ K k) z₀ hz₀val
    have hxz : x ∈ Subgroup.centralizer ({z₀} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Subgroup.mem_centralizer_iff.mp hx _ hz₀R
    rw [hCz] at hxz
    have hxX : (x : ModGL τ K) ∈ toralCentralizer τ K (zTuple τ K k) := hxz
    have hx3' : (x : ModGL τ K) ^ 3 = 1 := by
      have := congrArg (fun y : G => (y : ModGL τ K)) hx3
      simpa using this
    have hxS := toralCentralizer_pow_three_mem hK hK3 hb hxX hx3'
    have hker : rootCharKernel (zTuple τ K k) = kernelRoots χ := by
      rw [rootCharKernel_eq_kernelRoots hK hb, signTupleBits_zTuple hK]
      rfl
    rw [hker] at hxS
    have hSsup : rootSpan τ K (kernelRoots χ) = S₁ ⊔ S₂ := by
      rw [← iSup_componentRootSpan K]
      refine le_antisymm (iSup_le fun i => ?_)
        (sup_le (le_iSup (fun i => componentRootSpan K χ i) i₁)
          (le_iSup (fun i => componentRootSpan K χ i) i₂))
      rcases hS.exists_eq i with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    rw [hSsup] at hxS
    have hxC : (x : ModGL τ K) ∈ Subgroup.centralizer (S₁ : Set (ModGL τ K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hy : (⟨s, hS₁le hs⟩ : G) ∈ Rstd := (mem_Rstd _).2 hs
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx _ hy)
    have hA2 : ∀ a ∈ S₁, (∀ y ∈ S₁, a * y = y * a) → a * a = 1 := by
      intro a ha hcen
      have haG : a ∈ adjointGroup τ K := hS₁le ha
      have haR : (⟨a, haG⟩ : G) ∈ Rstd := (mem_Rstd _).2 ha
      have := hZ ⟨a, haG⟩ haR (fun y hy => Subtype.ext (hcen _ ((mem_Rstd y).1 hy)))
      exact congrArg Subtype.val this
    exact (mem_L x).2 (le_of_pow_three_of_le_sup_of_commutes
      (componentRootSpan_le_centralizer K hi12) hA2 hxS hxC hx3')
  ·
    refine sup_le (hG4 δ₂ hS.mem₂ hS.ne₂ hS.ne₂') (hG4 (-δ₂) (neg_mem_kernelRoots hS.mem₂) ?_ ?_)
    · intro h
      exact hS.ne₂' (neg_eq_iff_eq_neg.mp h)
    · intro h
      exact hS.ne₂ (neg_inj.mp h)
  ·
    intro heq
    have h3 : rootGroup F K δ₃ ≤ L := hG4 δ₃ hS.mem₃ hS.ne₃ hS.ne₃'
    rw [← heq] at h3
    apply not_rootSubgroup_le_rootSubgroup_sup (K := K) hS.mem₂.1 hS.mem₃.1 hS.ne₃₂ hS.ne₃₂'
    have hR₂ : (rootSubgroup τ K δ₂ ⊔ rootSubgroup τ K (-δ₂)).subgroupOf (adjointGroup τ K) =
        rootGroup F K δ₂ ⊔ rootGroup F K (-δ₂) := subgroupOf_rootSubgroup_sup_eq F hS.mem₂.1
    intro y hy
    have hy' : (⟨y, rootSubgroup_le_adjointGroup δ₃ hy⟩ : G) ∈ rootGroup F K δ₃ := by
      rw [← subgroupOf_rootSubgroup_eq_rootGroup F hS.mem₃.1]
      exact hy
    have := h3 hy'
    rw [← hR₂] at this
    exact this

end Adj

section Assembly

open CFSG.LieType.Steinberg.Adjoint

variable {n : ℕ}

theorem hasLayer3_of_std3 {t : StatedLieTag}
    (hfin : Finite (modelUniv t n 3 1 Fact.out).K)
    (hsingle : ∀ R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Fact.out).D,
      ∀ R' ∈ fundamentalSubgroups t (modelUniv t n 3 1 Fact.out).D, ∃ g, R' = conjSub g R)
    {Rstd R₂ : Subgroup (modelUniv t n 3 1 Fact.out).K}
    (hRstd : Rstd ∈ fundamentalSubgroups t (modelUniv t n 3 1 Fact.out).D)
    (hR₂ : R₂ ∈ fundamentalSubgroups t (modelUniv t n 3 1 Fact.out).D)
    (h : StdLayer3 Rstd R₂) : HasLayer3 t n := by
  intro R₀ hR₀
  obtain ⟨g, hg⟩ := hsingle Rstd hRstd R₀ hR₀
  rw [hg]
  exact LayerAt3.conj (fun S hS g => conjSub_mem_fundamentalSubgroups hS g)
    (layerAt3_of_stdLayer3 hsingle hR₂ h) g

theorem natCard_galoisField_three_one : Nat.card (GaloisField 3 1) = 3 := by
  rw [GaloisField.card 3 1 (by norm_num)]
  norm_num

theorem odd_natCard_galoisField_three_one : Odd (Nat.card (GaloisField 3 1)) := by
  rw [natCard_galoisField_three_one]
  decide

theorem hasLayer3_F4 (hadm : StatedLieAdmissible .F4 n 3 1) : HasLayer3 .F4 n := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hfund : IsFundTag .F4 := trivial
  obtain ⟨δ₂, δ₃, hS, hlong⟩ := layerShape_F4
  have hfin : Finite (modelUniv .F4 n 3 1 Fact.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 Fact.out trivial hadm
  have hsingle := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .F4 n 3 1 Fact.out
    trivial hadm (by decide) (by decide)
  have hlongE := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .F4 n 3 1 Fact.out
    trivial hadm ⟨0, by show 0 < 4; decide⟩ (by show 0 < 2; decide)
  have hRstd := (⟨1, _, Or.inl hlongE, (conjSub_one _).symm⟩ :
    _ ∈ fundamentalSubgroups .F4 (modelUniv .F4 n 3 1 Fact.out).D)
  obtain ⟨eR⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
    hp2 hfund hadm (by decide) (by decide) hRstd
  have hstd := stdLayer3_adjoint (K := GaloisField 3 1) (ringChar_galoisField_ne_two hp2)
    natCard_galoisField_three_one (⟨0, by decide⟩ : Fin Tag.F4.rank) hS
    (central_sq_of_equiv_sl2 odd_natCard_galoisField_three_one eR)
  refine hasLayer3_of_std3 hfin hsingle hRstd ?_ hstd
  exact ⟨1, δ₂, Or.inl (CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_f4Datum_of_iform_eq_four
    hS.mem₂.1 hlong), (conjSub_one _).symm⟩

theorem hasLayer3_E8 (hadm : StatedLieAdmissible .E8 n 3 1) : HasLayer3 .E8 n := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hfund : IsFundTag .E8 := trivial
  obtain ⟨δ₂, δ₃, hS⟩ := layerShape_E8
  have hfin : Finite (modelUniv .E8 n 3 1 Fact.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 Fact.out trivial hadm
  have hsingle := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .E8 n 3 1 Fact.out
    trivial hadm (by decide) (by decide)
  have hlong := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .E8 n 3 1 Fact.out
    trivial hadm
  have hall : ∀ γ : Fin Tag.E8.rank → ℤ, IsRoot .E8 γ →
      IsLongestRoot (modelUniv .E8 n 3 1 Fact.out).D γ := fun γ hγ =>
    CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_of_mem_roots_of_forall_single _ rfl
      (fun k => hlong k trivial) (mem_adjDatum_roots.2 hγ)
  have hRstd := (⟨1, _, Or.inl (hall _ (IsRoot.basis (⟨0, by decide⟩ : Fin Tag.E8.rank))),
    (conjSub_one _).symm⟩ : _ ∈ fundamentalSubgroups .E8 (modelUniv .E8 n 3 1 Fact.out).D)
  obtain ⟨eR⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
    hp2 hfund hadm (by decide) (by decide) hRstd
  have hstd := stdLayer3_adjoint (K := GaloisField 3 1) (ringChar_galoisField_ne_two hp2)
    natCard_galoisField_three_one (⟨0, by decide⟩ : Fin Tag.E8.rank) hS
    (central_sq_of_equiv_sl2 odd_natCard_galoisField_three_one eR)
  refine hasLayer3_of_std3 hfin hsingle hRstd ?_ hstd
  exact ⟨1, δ₂, Or.inl (hall _ hS.mem₂.1), (conjSub_one _).symm⟩

end Assembly

end CFSG.ClassicalInvolution.Uniform
