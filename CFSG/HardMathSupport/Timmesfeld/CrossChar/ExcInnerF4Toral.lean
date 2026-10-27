module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Root
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Basic
public import CFSG.LieType.AlgebraicGroups.ToralRootCover
public import CFSG.Quasithin.Background.SmithCurtisChevAmb
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Families

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Subnormal

variable {G : Type*} [Group G]

theorem isSubnormal_subgroupOf_step {A B C : Subgroup G} (hAB : A ≤ B)
    (hB : (B.subgroupOf C).IsSubnormal) (h : ∀ y ∈ B, ∀ a ∈ A, y * a * y⁻¹ ∈ A) :
    (A.subgroupOf C).IsSubnormal := by
  refine Subgroup.IsSubnormal.step _ _ (fun z hz => hAB hz) hB ?_
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hn' : (n : ↥C).1 ∈ A := hn
  simpa [Subgroup.mem_subgroupOf] using h g.1.1 g.2 (n : ↥C).1 hn'

theorem isSubnormal_map_subgroupOf {G' : Type*} [Group G'] (f : G →* G')
    {L X : Subgroup G} (hLX : L ≤ X)
    (hL : (L.subgroupOf X).IsSubnormal) {C : Subgroup G'} (hXC : X.map f ≤ C)
    (hX : ((X.map f).subgroupOf C).IsSubnormal) : ((L.map f).subgroupOf C).IsSubnormal := by
  have hle : (L.map f).subgroupOf C ≤ (X.map f).subgroupOf C :=
    Subgroup.comap_mono (Subgroup.map_mono hLX)
  refine Subgroup.IsSubnormal.trans hle ?_ hX
  let ψ : X →* ((X.map f).subgroupOf C) :=
    { toFun := fun x => ⟨⟨f x, hXC ⟨x, x.2, rfl⟩⟩, ⟨x, x.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hψ : Function.Surjective ψ := by
    rintro ⟨⟨y, hyC⟩, hyX⟩
    obtain ⟨x, hx, hxy⟩ := hyX
    exact ⟨⟨x, hx⟩, Subtype.ext (Subtype.ext hxy)⟩
  have h1 := hL.map hψ
  convert h1 using 1
  ext ⟨⟨y, hyC⟩, hyX⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hLX hl⟩, hl, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    have := congrArg (fun z : ((X.map f).subgroupOf C) => ((z : C) : G')) hxy
    simpa [ψ] using this

end Subnormal

section Inner

variable {K : Type*} [Group K] [Finite K] {p : ℕ}

theorem localDeltaIn_eq_bot_of_inner_components (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    {H : Subgroup (MulAut K)} (hH : innerAut K ≤ H) (D₀ : Subgroup K) {S : Set K}
    (hS : Subgroup.closure S = ⊤)
    (hcomp : ∀ s ∈ S, ∃ d ∈ D₀, d ≠ 1 ∧ ∃ L : Subgroup K, s ∈ L ∧
      L ≤ Subgroup.centralizer ({d} : Set K) ∧ CFSG.IsQuasisimple L ∧
      (L.subgroupOf (Subgroup.centralizer ({d} : Set K))).IsSubnormal ∧
      ¬ Nat.Coprime p (Nat.card L)) :
    localDeltaIn p H (D₀.map (MulAut.conj : K →* MulAut K)) = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot, ← fixSub_eq_top_iff, eq_top_iff, ← hS, Subgroup.closure_le]
  intro s hs
  obtain ⟨d, hd, hd1, L, hsL, hLC, hLq, hLsn, hLp⟩ := hcomp s hs
  set e : MulAut K := MulAut.conj d with hedef
  have he : e ∈ D₀.map (MulAut.conj : K →* MulAut K) := ⟨d, hd, rfl⟩
  have he1 : e ≠ 1 := fun h => hd1 (hinj (h.trans (map_one MulAut.conj).symm))
  set C : Subgroup (MulAut K) := H ⊓ Subgroup.centralizer ({e} : Set (MulAut K)) with hCdef
  have hcomm : ∀ x ∈ Subgroup.centralizer ({d} : Set K), MulAut.conj x * e = e * MulAut.conj x :=
    fun x hx => by
      have h1 : x * d = d * x := Subgroup.mem_centralizer_singleton_iff.1 hx
      rw [hedef, ← map_mul, ← map_mul, h1]
  have hXC : (Subgroup.centralizer ({d} : Set K)).map (MulAut.conj : K →* MulAut K) ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_inf.2 ⟨hH ⟨x, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 (hcomm x hx)⟩
  have hXn : (((Subgroup.centralizer ({d} : Set K)).map
      (MulAut.conj : K →* MulAut K)).subgroupOf C).IsSubnormal := by
    refine Subgroup.Normal.isSubnormal ⟨fun n hn y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨x, hx, hxn⟩ := hn
    have hy := (Subgroup.mem_inf.1 y.2).2
    have hye : (y : MulAut K) * e = e * y := Subgroup.mem_centralizer_singleton_iff.1 hy
    refine ⟨(y : MulAut K) x, ?_, ?_⟩
    ·
      have hyd : (y : MulAut K) d = d := by
        apply hinj
        rw [← mul_conj_mul_inv, ← hedef, hye, mul_inv_cancel_right]
      have h1 : x * d = d * x := Subgroup.mem_centralizer_singleton_iff.1 hx
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      have h2 := congrArg (y : MulAut K) h1
      rwa [map_mul, map_mul, hyd] at h2
    · change MulAut.conj ((y : MulAut K) x) = (y : MulAut K) * (n : MulAut K) * (y : MulAut K)⁻¹
      rw [← mul_conj_mul_inv, ← hxn]
  have hTC : L.map (MulAut.conj : K →* MulAut K) ≤ C :=
    (Subgroup.map_mono hLC).trans hXC
  have hcompL : CFSG.IsComponent ((L.map (MulAut.conj : K →* MulAut K)).subgroupOf C) := by
    refine ⟨?_, isSubnormal_map_subgroupOf _ hLC hLsn hXC hXn⟩
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((L.equivMapOfInjective _ hinj).trans (Subgroup.subgroupOfEquivOfLe hTC).symm) hLq
  exact le_fixSub_of_component hp hinj hg he he1 hTC hcompL hLp hsL

theorem isSubnormal_subgroupOf_centralizer {G : Type*} [Group G] {A : Subgroup G} (d : A)
    {L : Subgroup G} (hsn : (L.subgroupOf (A ⊓ Subgroup.centralizer {(d : G)})).IsSubnormal) :
    ((L.subgroupOf A).subgroupOf (Subgroup.centralizer ({d} : Set A))).IsSubnormal := by
  let φ : ↥(A ⊓ Subgroup.centralizer {(d : G)}) →* ↥(Subgroup.centralizer ({d} : Set A)) :=
    { toFun := fun x => ⟨⟨x, x.2.1⟩, Subgroup.mem_centralizer_singleton_iff.2
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 x.2.2))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hφ : Function.Surjective φ := by
    rintro ⟨⟨y, hyA⟩, hyc⟩
    exact ⟨⟨y, hyA, Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hyc))⟩, rfl⟩
  convert hsn.map hφ using 1
  ext ⟨⟨y, hyA⟩, hyc⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · intro hy
    exact ⟨⟨y, hyA, Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hyc))⟩, hy, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    have h1 : (x : G) = y := congrArg (fun z : ↥(Subgroup.centralizer ({d} : Set A)) =>
      ((z : A) : G)) hxy
    rw [← h1]
    exact hx

theorem localDeltaIn_eq_bot_of_inner_components_ambient {G : Type*} [Group G] {A : Subgroup G}
    [Finite A] (hp : p.Prime) (hinj : Function.Injective (MulAut.conj : A →* MulAut A))
    {H : Subgroup (MulAut A)} (hH : innerAut A ≤ H) (D₀ : Subgroup A) {S : Set A}
    (hS : Subgroup.closure S = ⊤)
    (hcomp : ∀ s ∈ S, ∃ d ∈ D₀, d ≠ 1 ∧ ∃ L : Subgroup G, (s : G) ∈ L ∧
      L ≤ A ⊓ Subgroup.centralizer {(d : G)} ∧ CFSG.IsQuasisimple L ∧
      (L.subgroupOf (A ⊓ Subgroup.centralizer {(d : G)})).IsSubnormal ∧
      ¬ Nat.Coprime p (Nat.card L)) :
    localDeltaIn p H (D₀.map (MulAut.conj : A →* MulAut A)) = ⊥ := by
  refine localDeltaIn_eq_bot_of_inner_components hp hinj hH D₀ hS fun s hs => ?_
  obtain ⟨d, hd, hd1, L, hsL, hLC, hLq, hLsn, hLp⟩ := hcomp s hs
  have hLA : L ≤ A := hLC.trans inf_le_left
  refine ⟨d, hd, hd1, L.subgroupOf A, hsL, fun x hx => ?_, ?_,
    isSubnormal_subgroupOf_centralizer d hLsn, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.2
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hLC hx).2))
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLA).symm hLq
  · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLA).toEquiv]

end Inner

section Toral

variable {τ : Tag} {K : Type} [Field K]

theorem componentRootSpan_le_toralCentralizer
    (a : Fin τ.rank → Kˣ) (i : KernelComponent (rootCharHom a)) :
    componentRootSpan K (rootCharHom a) i ≤ toralCentralizer τ K a := fun _ hu =>
  Subgroup.mem_inf.2 ⟨rootSpan_le_adjointGroup K _ hu,
    rootSpan_le_centralizer a (fun _ hα => hα.1) hu⟩

theorem isSubnormal_componentRootSpan
    (a : Fin τ.rank → Kˣ) (i : KernelComponent (rootCharHom a)) :
    ((componentRootSpan K (rootCharHom a) i).subgroupOf (toralCentralizer τ K a)).IsSubnormal := by
  obtain ⟨-, -, -, hSi, -⟩ :=
    root_character_kernel_orthogonal_central_product τ K (rootCharHom a)
  obtain ⟨hMX, hMn, -⟩ := Chevalley_toral_centralizer_root_generated_quotient τ K a
  obtain ⟨hSR, hSRn⟩ := hSi i
  have hRM : rootSpan τ K (kernelRoots (rootCharHom a)) ≤ toralRootGroup τ K a :=
    le_sup_right
  have h0 : ((toralRootGroup τ K a).subgroupOf (toralCentralizer τ K a)).IsSubnormal :=
    hMn.isSubnormal
  have hNR : toralRootGroup τ K a ≤ Subgroup.normalizer
      (rootSpan τ K (kernelRoots (rootCharHom a)) : Set (ModGL τ K)) :=
    sup_le (CFSG.Quasithin.SmithCurtis.Chev.torusGroup_le_normalizer_rootSpan _
      fun _ hα => hα.1) Subgroup.le_normalizer
  have h1 : ((rootSpan τ K (kernelRoots (rootCharHom a))).subgroupOf
      (toralCentralizer τ K a)).IsSubnormal :=
    isSubnormal_subgroupOf_step hRM h0 fun y hy r hr =>
      (Subgroup.mem_normalizer_iff.1 (hNR hy) r).1 hr
  refine isSubnormal_subgroupOf_step hSR h1 fun y hy s hs => ?_
  have := hSRn.conj_mem ⟨s, hSR hs⟩ (Subgroup.mem_subgroupOf.2 hs) ⟨y, hy⟩
  exact Subgroup.mem_subgroupOf.1 this

theorem rootDiagUnit_injective :
    Function.Injective (rootDiagUnit τ : (Fin τ.rank → Kˣ) → ModGL τ K) := by
  intro b b' h
  funext i
  have hv := congrArg (fun g : ModGL τ K => (g : Module.End K (RootModule τ K))
    (rootVec τ K (Pi.single i 1))) h
  change rootDiag b (rootVec τ K _) = rootDiag b' (rootVec τ K _) at hv
  rw [rootDiag_rootVec _ (isRoot_single τ i), rootDiag_rootVec _ (isRoot_single τ i)] at hv
  have hne : rootVec τ K (Pi.single i 1 : Fin τ.rank → ℤ) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot (isRoot_single τ i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h1 := smul_left_injective K hne hv
  have e : ∀ c : Fin τ.rank → Kˣ, rootChar c (Pi.single i 1) = c i := fun c => by
    have := rootChar_nsmul_single c i 1
    rwa [one_nsmul, pow_one] at this
  rw [e, e] at h1
  exact Units.ext h1

theorem torusGroup_le_range_rootDiagUnitHom :
    torusGroup τ K ≤ (rootDiagUnitHom τ K).range := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, u⟩, rfl⟩
  exact ⟨_, (torusElt_eq_rootDiagUnit i u).symm⟩

theorem exists_rootChar_eq_one
    [Finite K] {p : ℕ} (hp : p.Prime) {B : Subgroup (ModGL τ K)} (hB : B ≤ torusGroup τ K)
    (hpow : ∀ x ∈ B, x ^ p = 1) (hcard : p < Nat.card B) (α : Fin τ.rank → ℤ) :
    ∃ a : Fin τ.rank → Kˣ, rootDiagUnit τ a ∈ B ∧ rootDiagUnit τ a ≠ 1 ∧ rootChar a α = 1 := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  by_contra hne
  push Not at hne
  set T₀ := B.comap (rootDiagUnitHom τ K) with hT₀
  let χ : (Fin τ.rank → Kˣ) →* Kˣ :=
    { toFun := fun a => rootChar a α
      map_one' := by simp [rootChar]
      map_mul' := fun a b => by simp only [rootChar, Pi.mul_apply, mul_zpow,
        Finset.prod_mul_distrib] }
  have hχ : ∀ a, χ a = rootChar a α := fun _ => rfl
  have h1 : Nat.card B ≤ Nat.card T₀ := by
    refine Nat.card_le_card_of_surjective (fun a : T₀ => (⟨rootDiagUnit τ a, a.2⟩ : B)) ?_
    rintro ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := torusGroup_le_range_rootDiagUnitHom (hB hb)
    exact ⟨⟨a, hb⟩, rfl⟩
  have hker : ∀ a ∈ T₀, χ a = 1 → a = 1 := by
    intro a ha hχa
    by_contra ha1
    exact hne a ha (fun h => ha1 (rootDiagUnit_injective (h.trans rootDiagUnit_one.symm))) hχa
  have hpowa : ∀ a ∈ T₀, a ^ p = 1 := by
    intro a ha
    have h2 : rootDiagUnit τ (a ^ p) = rootDiagUnit τ a ^ p := map_pow (rootDiagUnitHom τ K) a p
    have h3 : rootDiagUnit τ a ^ p = 1 := hpow _ ha
    exact rootDiagUnit_injective (by rw [h2, h3, rootDiagUnit_one])
  let f : T₀ → rootsOfUnity p K := fun a => ⟨χ a, by
    rw [mem_rootsOfUnity, ← map_pow, hpowa a a.2, map_one]⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h3 : χ ((a : Fin τ.rank → Kˣ) * (b : Fin τ.rank → Kˣ)⁻¹) = 1 := by
      have : χ a = χ b := congrArg (fun z : rootsOfUnity p K => (z : Kˣ)) hab
      rw [map_mul, map_inv, this, mul_inv_cancel]
    have h4 := hker _ (T₀.mul_mem a.2 (T₀.inv_mem b.2)) h3
    exact Subtype.ext (mul_inv_eq_one.1 h4)
  have h5 := Nat.card_le_card_of_injective f hf
  have h6 := card_rootsOfUnity K p
  omega

end Toral

section ToralInner

variable {τ : Tag} {K : Type} [Field K]

theorem closure_pinnedX_eq_top :
    Subgroup.closure {x : adjointGroup τ K | ∃ α, IsRoot τ α ∧ ∃ c,
      (x : ModGL τ K) = pinnedX τ K α c} = ⊤ := by
  set S := {x : adjointGroup τ K | ∃ α, IsRoot τ α ∧ ∃ c, (x : ModGL τ K) = pinnedX τ K α c}
  have hle : rootSpan τ K {α | IsRoot τ α} ≤
      (Subgroup.closure S).map (adjointGroup τ K).subtype := by
    refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    exact ⟨⟨pinnedX τ K α c, pinnedX_mem_adjointGroup α c⟩,
      Subgroup.subset_closure ⟨α, hα, c, rfl⟩, rfl⟩
  rw [← adjointGroup_eq_rootSpan] at hle
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  obtain ⟨y, hy, hyx⟩ := hle hx
  have : y = ⟨x, hx⟩ := Subtype.ext hyx
  rw [← this]
  exact hy

theorem mulAut_conj_injective_adjointGroup
    [Finite K] :
    Function.Injective (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)) := by
  intro g g' h
  have hc : g'⁻¹ * g ∈ Subgroup.center (adjointGroup τ K) :=
    Subgroup.mem_center_iff.2 fun x => by
      have e := congrArg (fun φ : MulAut (adjointGroup τ K) => φ x) h
      simp only [MulAut.conj_apply] at e
      calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
        _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [e]
        _ = g'⁻¹ * g * x := by group
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

theorem localDeltaIn_eq_bot_of_toral
    [Finite K] {p : ℕ}
    (hp : p.Prime) {t : Kˣ} (htp : orderOf t = p) (ht : t ^ 2 ≠ 1)
    {H : Subgroup (MulAut (adjointGroup τ K))} (hH : innerAut (adjointGroup τ K) ≤ H)
    (D₀ : Subgroup (adjointGroup τ K)) (hpow : ∀ x ∈ D₀, x ^ p = 1) (hcard : p < Nat.card D₀)
    (htor : ∀ x ∈ D₀, (x : ModGL τ K) ∈ torusGroup τ K) :
    localDeltaIn p H
      (D₀.map (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K))) = ⊥ := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  have hinj := mulAut_conj_injective_adjointGroup (τ := τ) (K := K)
  have hB : D₀.map (adjointGroup τ K).subtype ≤ torusGroup τ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact htor x hx
  have hBpow : ∀ y ∈ D₀.map (adjointGroup τ K).subtype, y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hpow x hx, map_one]
  have hBcard : p < Nat.card (D₀.map (adjointGroup τ K).subtype) := by
    rwa [Subgroup.card_map_of_injective (adjointGroup τ K).subtype_injective]
  refine localDeltaIn_eq_bot_of_inner_components_ambient hp hinj hH D₀ closure_pinnedX_eq_top ?_
  rintro s ⟨α, hα, c, hsc⟩
  obtain ⟨w, k, rfl⟩ := isRoot_iff_exists_smul_single.1 hα
  obtain ⟨a, ⟨d, hd, hda⟩, ha1, hχ⟩ := exists_rootChar_eq_one hp hB hBpow hBcard
    (w • (Pi.single k 1 : Fin τ.rank → ℤ))
  have hda' : (d : ModGL τ K) = rootDiagUnit τ a := hda
  have hαk : w • (Pi.single k 1 : Fin τ.rank → ℤ) ∈ kernelRoots (rootCharHom a) := ⟨hα, hχ⟩
  have hαi : w • (Pi.single k 1 : Fin τ.rank → ℤ) ∈
      componentRoots (rootCharHom a) ⟦⟨_, hαk⟩⟧ := ⟨hαk, rfl⟩
  refine ⟨d, hd, fun h => ha1 (by rw [← hda', h]; rfl),
    componentRootSpan K (rootCharHom a) ⟦⟨_, hαk⟩⟧, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsc]
    exact pinnedX_mem_rootSpan hαi c
  · rw [hda']
    exact componentRootSpan_le_toralCentralizer a _
  · exact isQuasisimple_componentRootSpan_of_sq_ne_one ht _
  · rw [hda']
    exact isSubnormal_componentRootSpan a _
  · have hmem := componentTorus_le_componentRootSpan K (rootCharHom a) _
      (canonicalRep_conj_torusElt_mem (K := K) hαi t)
    have h1 := orderOf_dvd_natCard (⟨_, hmem⟩ : componentRootSpan K (rootCharHom a) ⟦⟨_, hαk⟩⟧)
    rw [Subgroup.orderOf_mk, orderOf_canonicalRep_conj_torusElt hp w k htp ht] at h1
    rw [Nat.Prime.coprime_iff_not_dvd hp, not_not]
    exact h1

end ToralInner

end CFSG.HardMathSupport.Timmesfeld.CrossChar
