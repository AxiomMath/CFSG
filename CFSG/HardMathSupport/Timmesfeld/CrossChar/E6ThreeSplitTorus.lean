module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldReduction
public import CFSG.LieType.Chevalley.OddToralInvolutionComponents
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcComp
public import CFSG.LieType.AlgebraicGroups.ToralRootCover
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)

section Chain

variable {K : Type*} [Group K]

theorem isSubnormal_conj_of_chain {x : MulAut K} {H : Subgroup (MulAut K)}
    (hH : innerAut K ≤ H) {T T₁ : Subgroup K} (hTT₁ : T ≤ T₁) (hT₁F : T₁ ≤ fixSub x)
    (hTn : ∀ y ∈ T₁, ∀ t ∈ T, y * t * y⁻¹ ∈ T)
    (hT₁n : ∀ f ∈ fixSub x, ∀ t ∈ T₁, f * t * f⁻¹ ∈ T₁)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) :
    ((T.map (MulAut.conj : K →* MulAut K)).subgroupOf
      (H ⊓ Subgroup.centralizer ({x} : Set (MulAut K)))).IsSubnormal := by
  have hB := isSubnormal_conj_of_normal_in_fixSub hH hT₁F hT₁n hinj
  refine Subgroup.IsSubnormal.step _ _ (fun z hz => Subgroup.mem_subgroupOf.2
    (Subgroup.map_mono hTT₁ (Subgroup.mem_subgroupOf.1 hz))) hB ?_
  refine ⟨fun n hn g => ?_⟩
  have hn' : ((n : ↥(H ⊓ Subgroup.centralizer ({x} : Set (MulAut K)))) : MulAut K) ∈
      T.map (MulAut.conj : K →* MulAut K) :=
    Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hn)
  have hg' : ((g : ↥(H ⊓ Subgroup.centralizer ({x} : Set (MulAut K)))) : MulAut K) ∈
      T₁.map (MulAut.conj : K →* MulAut K) := Subgroup.mem_subgroupOf.1 g.2
  obtain ⟨t, ht, htn⟩ := hn'
  obtain ⟨y, hy, hyg⟩ := hg'
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 ⟨y * t * y⁻¹, hTn y hy t ht, ?_⟩)
  simp only [map_mul, map_inv, htn, hyg, Subgroup.coe_mul, Subgroup.coe_inv]

end Chain

section Units

variable {K : Type} [Field K] [Finite K]

theorem exists_units_sq_ne_one (hK4 : 4 ≤ Nat.card K) : ∃ t : Kˣ, (t : K) ^ 2 ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have : Fintype Kˣ := Fintype.ofFinite _
  have h1 : (Finset.univ.filter fun z : Kˣ => z ^ 2 = 1).card ≤ 2 :=
    IsCyclic.card_pow_eq_one_le (by norm_num)
  have h2 : (Finset.univ.filter fun z : Kˣ => z ^ 2 = 1) = Finset.univ :=
    Finset.filter_true_of_mem fun z _ => Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hcon z)
  rw [h2, Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_units] at h1
  omega

omit [Finite K] in
theorem torusElt_pow' {τ : Tag}
    (k : Fin τ.rank) (t : Kˣ) (n : ℕ) :
    torusElt τ K k t ^ n = torusElt τ K k (t ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, torusElt_one]
  | succ n ih => rw [pow_succ, ih, ← torusElt_mul, pow_succ]

end Units

section Count

variable {τ : Tag} {K : Type} [Field K] [Finite K]


theorem exists_rootDiagAut_mem_rootChar_eq_one
    {p : ℕ} (hp : p.Prime)
    {D : Subgroup (MulAut (adjointGroup τ K))} (hD : IsElemAbelian p D)
    (hcard : p ^ 2 ≤ Nat.card D) (hDT : D ≤ (rootDiagAutHom τ K).range)
    (α : Fin τ.rank → ℤ) :
    ∃ a : Fin τ.rank → Kˣ, rootDiagAut τ K a ∈ D ∧ rootDiagAut τ K a ≠ 1 ∧
      rootChar a α = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hpar : ∀ x : D, ∃ a : Fin τ.rank → Kˣ, rootDiagAut τ K a = x := fun x => hDT x.2
  choose par hpar using hpar
  have hparmul : ∀ x y : D, par (x * y) = par x * par y := fun x y =>
    rootDiagAutHom_injective (by
      rw [map_mul]
      change rootDiagAut τ K (par (x * y)) =
        rootDiagAut τ K (par x) * rootDiagAut τ K (par y)
      rw [hpar, hpar, hpar]
      rfl)
  let P : D →* (Fin τ.rank → Kˣ) := MonoidHom.mk' par hparmul
  let χα : (Fin τ.rank → Kˣ) →* Kˣ := MonoidHom.mk' (fun a => rootChar a α) fun a b => by
    simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]
  let φ : D →* Kˣ := χα.comp P
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    refine hcon (par x) ?_ ?_ hx
    · rw [hpar]
      exact x.2
    · rw [hpar]
      exact fun h => hx1 (Subtype.ext h)
  have hφp : ∀ x : D, φ x ^ p = 1 := fun x => by
    rw [← map_pow]
    have hx : x ^ p = 1 := Subtype.ext (hD.2 x x.2)
    rw [hx, map_one]
  have : Fintype Kˣ := Fintype.ofFinite _
  have : Fintype D := Fintype.ofFinite _
  have hle : Nat.card D ≤ p := by
    rw [Nat.card_eq_fintype_card]
    calc Fintype.card D = (Finset.univ.image φ).card := by
          rw [Finset.card_image_of_injective _ hφ, Finset.card_univ]
      _ ≤ (Finset.univ.filter fun z : Kˣ => z ^ p = 1).card := by
          refine Finset.card_le_card fun z hz => ?_
          obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hz
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hφp x⟩
      _ ≤ p := IsCyclic.card_pow_eq_one_le hp.pos
  have hp2 : p < p ^ 2 := by
    have := hp.two_le
    nlinarith
  omega

@[expose] def IsSplitToral
    (D : Subgroup (MulAut (adjointGroup τ K))) : Prop :=
  ∃ ψ : MulAut (adjointGroup τ K), D.map (MulAut.conj ψ).toMonoidHom ≤ (rootDiagAutHom τ K).range

@[expose] def HasSplitToralPlane
    (p : ℕ) (D : Subgroup (MulAut (adjointGroup τ K))) : Prop :=
  ∃ E : Subgroup (MulAut (adjointGroup τ K)), E ≤ D ∧ IsElemAbelian p E ∧ p ^ 2 ≤ Nat.card E ∧
    IsSplitToral E

end Count

section Split


variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem rootSubgroup_le_fixSub_of_mem_localDeltaIn (hK4 : 4 ≤ Nat.card K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {H D : Subgroup (MulAut (adjointGroup τ K))}
    (hH : innerAut (adjointGroup τ K) ≤ H) {g : MulAut (adjointGroup τ K)}
    (hg : g ∈ localDeltaIn p H D) {a : Fin τ.rank → Kˣ} (haD : rootDiagAut τ K a ∈ D)
    (ha1 : rootDiagAut τ K a ≠ 1) (hap : rootDiagAut τ K a ^ p = 1) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hχ : rootChar a α = 1) :
    rootSubgroup τ K α ≤ (fixSub g).map (adjointGroup τ K).subtype := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL τ K) := finite_modGL
  have hinj := mulAut_conj_injective_of_center_eq_bot
    (center_adjointGroup_eq_bot (τ := τ) (K := K))
  set x := rootDiagAut τ K a with hx
  set χ := CFSG.LieType.AlgebraicGroups.rootCharHom (τ := τ) a with hχdef
  have hαk : α ∈ kernelRoots χ := ⟨hα, hχ⟩
  set i : KernelComponent χ := ⟦⟨α, hαk⟩⟧ with hi
  set S := componentRootSpan K χ i with hS
  have hS1 : S ≤ rootSpan τ K (rootCharKernel a) := componentRootSpan_le K i
  have hS2 : rootSpan τ K (rootCharKernel a) ≤ toralCentralizer τ K a :=
    rootSpan_rootCharKernel_le_toralCentralizer a
  have hSC : S ≤ adjointGroup τ K := (hS1.trans hS2).trans inf_le_left
  have hS1n : ∀ y ∈ rootSpan τ K (rootCharKernel a), ∀ s ∈ S, y * s * y⁻¹ ∈ S :=
    fun y hy s hs => (Subgroup.mem_normalizer_iff.1 (rootSpan_le_normalizer K i hy) s).1 hs
  have hS2n : ∀ f ∈ toralCentralizer τ K a, ∀ s ∈ rootSpan τ K (rootCharKernel a),
      f * s * f⁻¹ ∈ rootSpan τ K (rootCharKernel a) := fun f hf s hs =>
    (Subgroup.normal_subgroupOf_iff hS2).1 (rootSpan_rootCharKernel_normal a) s f hs hf
  have hfix : ∀ u : adjointGroup τ K, u ∈ fixSub x ↔ (u : ModGL τ K) ∈ toralCentralizer τ K a := by
    intro u
    rw [mem_fixSub, Subtype.ext_iff, hx, coe_rootDiagAut, conj_eq_iff_mem_centralizer]
    exact ⟨fun h => ⟨u.2, h⟩, fun h => h.2⟩
  set T : Subgroup (adjointGroup τ K) := S.subgroupOf (adjointGroup τ K) with hT
  set T₁ : Subgroup (adjointGroup τ K) :=
    (rootSpan τ K (rootCharKernel a)).subgroupOf (adjointGroup τ K) with hT₁
  have hTT₁ : T ≤ T₁ := fun u hu => Subgroup.mem_subgroupOf.2 (hS1 (Subgroup.mem_subgroupOf.1 hu))
  have hT₁F : T₁ ≤ fixSub x := fun u hu => (hfix u).2 (hS2 (Subgroup.mem_subgroupOf.1 hu))
  have hTn : ∀ y ∈ T₁, ∀ t ∈ T, y * t * y⁻¹ ∈ T := fun y hy t ht =>
    Subgroup.mem_subgroupOf.2 (hS1n _ (Subgroup.mem_subgroupOf.1 hy) _
      (Subgroup.mem_subgroupOf.1 ht))
  have hT₁n : ∀ f ∈ fixSub x, ∀ t ∈ T₁, f * t * f⁻¹ ∈ T₁ := fun f hf t ht =>
    Subgroup.mem_subgroupOf.2 (hS2n _ ((hfix f).1 hf) _ (Subgroup.mem_subgroupOf.1 ht))
  have hTC : T.map (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)) ≤
      H ⊓ Subgroup.centralizer ({x} : Set (MulAut (adjointGroup τ K))) := by
    rintro _ ⟨t, ht, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hH ⟨t, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (conj_commute_of_mem_fixSub (hT₁F (hTT₁ ht))).symm
  obtain ⟨t, ht⟩ := exists_units_sq_ne_one hK4
  have hSq : CFSG.IsQuasisimple S :=
    CFSG.StandardType.LayerExc.isQuasisimple_componentRootSpan_of_sq_ne_one ht
  have eT : T ≃* S := Subgroup.subgroupOfEquivOfLe hSC
  have hTq : CFSG.IsQuasisimple T := CFSG.LocalCores.isQuasisimple_of_mulEquiv eT.symm hSq
  have hcomp : CFSG.IsComponent ((T.map (MulAut.conj : adjointGroup τ K →*
      MulAut (adjointGroup τ K))).subgroupOf
        (H ⊓ Subgroup.centralizer ({x} : Set (MulAut (adjointGroup τ K))))) := by
    refine ⟨?_, isSubnormal_conj_of_chain hH hTT₁ hT₁F hTn hT₁n hinj⟩
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((T.equivMapOfInjective _ hinj).trans (Subgroup.subgroupOfEquivOfLe hTC).symm) hTq
  have ha : a ^ p = 1 := rootDiagAutHom_injective (by rw [map_pow, map_one]; exact hap)
  have hane : a ≠ 1 := fun h => ha1 (by rw [hx, h]; exact (rootDiagAutHom τ K).map_one)
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hane
  set ζ := a j with hζ
  have hζp : ζ ^ p = 1 := by rw [hζ, ← Pi.pow_apply, ha, Pi.one_apply]
  have hζo : orderOf ζ = p := orderOf_eq_prime hζp hj
  have hζ2 : (ζ : K) ^ 2 ≠ 1 := by
    intro h2
    have h2' : ζ ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h2)
    have hdvd := orderOf_dvd_of_pow_eq_one h2'
    rw [hζo] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd)
  obtain ⟨w, k, hwk⟩ := isRoot_iff_exists_smul_single.1 hα
  set h := canonicalRep (coxeterSystem τ) K w * torusElt τ K k ζ *
    (canonicalRep (coxeterSystem τ) K w)⁻¹ with hh_def
  have hhS : h ∈ S := componentTorus_le_componentRootSpan K χ i
    (canonicalRep_conj_torusElt_mem (K := K) (by rw [hwk]; exact ⟨hαk, rfl⟩) ζ)
  have hm : ∑ l, τ.cartan k l * (w⁻¹ • α) l = 2 := by
    rw [← corootPair_smul_single, hwk, corootPair]
    exact Int.mul_ediv_cancel _ (iform_self_pos_of_isRoot hα).ne'
  have hhp : h ^ p = 1 := by
    rw [hh_def, conj_pow, torusElt_pow', hζp, torusElt_one, mul_one, mul_inv_cancel]
  have hh1 : h ≠ 1 := by
    intro h1
    have e := canonicalRep_conj_torusElt_conj_pinnedX (K := K) w k ζ hα 1
    rw [← hh_def, h1, one_mul, inv_one, mul_one, hm] at e
    have e' := pinnedX_injective τ K α e
    apply hζ2
    have : (((ζ ^ (2 : ℤ)) : Kˣ) : K) = 1 := by rw [mul_one] at e'; exact e'.symm
    rwa [zpow_two, Units.val_mul, ← pow_two] at this
  have hho : orderOf (⟨h, hhS⟩ : S) = p := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hhp hh1
  have hTp : ¬ Nat.Coprime p (Nat.card T) := by
    rw [Nat.card_congr eT.toEquiv, ← Nat.Prime.dvd_iff_not_coprime hp, ← hho]
    exact orderOf_dvd_natCard _
  have hfixT := le_fixSub_of_component hp hinj hg haD ha1 hTC hcomp hTp
  intro u hu
  have huS : u ∈ S := rootSubgroup_le_componentRootSpan K ⟨α, hαk⟩ hu
  exact ⟨⟨u, hSC huS⟩, hfixT (Subgroup.mem_subgroupOf.2 huS), rfl⟩

theorem localDeltaIn_eq_bot_of_le_rootDiagAutHom_range (hK4 : 4 ≤ Nat.card K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {D : Subgroup (MulAut (adjointGroup τ K))}
    (hD : IsElemAbelian p D) (hcard : p ^ 2 ≤ Nat.card D)
    (hDT : D ≤ (rootDiagAutHom τ K).range) {H : Subgroup (MulAut (adjointGroup τ K))}
    (hH : innerAut (adjointGroup τ K) ≤ H) : localDeltaIn p H D = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot, ← fixSub_eq_top_iff, eq_top_iff]
  have hroot : rootSpan τ K {α | IsRoot τ α} ≤ (fixSub g).map (adjointGroup τ K).subtype := by
    refine iSup₂_le fun α hα => ?_
    obtain ⟨a, haD, ha1, hχ⟩ := exists_rootDiagAut_mem_rootChar_eq_one hp hD hcard hDT α
    exact rootSubgroup_le_fixSub_of_mem_localDeltaIn hK4 hp hp2 hH hg haD ha1 (hD.2 _ haD) hα hχ
  intro u _
  have hu : (u : ModGL τ K) ∈ rootSpan τ K {α | IsRoot τ α} := by
    rw [← adjointGroup_eq_rootSpan]
    exact u.2
  obtain ⟨v, hv, hvu⟩ := hroot hu
  have hvu' : v = u := Subtype.ext hvu
  rwa [← hvu']

theorem localDeltaIn_eq_bot_of_conj_le_rootDiagAutHom_range (hK4 : 4 ≤ Nat.card K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {D : Subgroup (MulAut (adjointGroup τ K))}
    (hD : IsElemAbelian p D) (hcard : p ^ 2 ≤ Nat.card D) (ψ : MulAut (adjointGroup τ K))
    (hDT : D.map (MulAut.conj ψ).toMonoidHom ≤ (rootDiagAutHom τ K).range)
    {H : Subgroup (MulAut (adjointGroup τ K))} (hH : innerAut (adjointGroup τ K) ≤ H) :
    localDeltaIn p H D = ⊥ := by
  set φ : MulAut (adjointGroup τ K) →* MulAut (adjointGroup τ K) :=
    (MulAut.conj ψ).toMonoidHom with hφdef
  have hφ : Function.Injective φ := (MulAut.conj ψ).injective
  have hD' : IsElemAbelian p (D.map φ) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨y, hy, rfl⟩⟩ := a
      obtain ⟨_, ⟨z, hz, rfl⟩⟩ := b
      apply Subtype.ext
      change φ y * φ z = φ z * φ y
      have := congrArg Subtype.val (hD.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
      rw [← map_mul, ← map_mul]
      exact congrArg φ this
    · rintro _ ⟨y, hy, rfl⟩
      rw [← map_pow, hD.2 y hy, map_one]
  have hcard' : p ^ 2 ≤ Nat.card (D.map φ) := by rwa [Subgroup.card_map_of_injective hφ]
  have hH' : innerAut (adjointGroup τ K) ≤ H.map φ := by
    rintro _ ⟨y, rfl⟩
    refine ⟨MulAut.conj (ψ⁻¹ y), hH ⟨ψ⁻¹ y, rfl⟩, ?_⟩
    change ψ * MulAut.conj (ψ⁻¹ y) * ψ⁻¹ = MulAut.conj y
    rw [mul_conj_mul_inv, MulAut.apply_inv_self]
  have h0 := localDeltaIn_eq_bot_of_le_rootDiagAutHom_range hK4 hp hp2 hD' hcard' hDT hH'
  have hle := map_localDeltaIn_le p φ hφ H D
  rw [h0, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ hφ] at hle
  exact hle


theorem localDeltaIn_eq_bot_of_isSplitToral {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {D : Subgroup (MulAut (adjointGroup τ K))} (hD : IsElemAbelian p D)
    (hcard : p ^ 2 ≤ Nat.card D) (hDs : IsSplitToral D)
    {H : Subgroup (MulAut (adjointGroup τ K))} (hH : innerAut (adjointGroup τ K) ≤ H) :
    localDeltaIn p H D = ⊥ := by
  obtain ⟨ψ, hψ⟩ := hDs
  by_cases hK4 : 4 ≤ Nat.card K
  · exact localDeltaIn_eq_bot_of_conj_le_rootDiagAutHom_range hK4 hp hp2 hD hcard ψ hψ hH
  exfalso
  have hKu : Nat.card Kˣ ≤ 2 := by
    rw [Nat.card_units]
    omega
  have htriv : ∀ y ∈ D, y = 1 := by
    intro y hy
    obtain ⟨a, ha⟩ := hψ ⟨y, hy, rfl⟩
    have hap : a ^ p = 1 := rootDiagAutHom_injective (by
      rw [map_pow, ha, map_one, ← map_pow, hD.2 y hy, map_one])
    have ha1 : a = 1 := funext fun i => by
      have h1 : a i ^ p = 1 := by rw [← Pi.pow_apply, hap, Pi.one_apply]
      have h2 : orderOf (a i) ∣ Nat.card Kˣ := orderOf_dvd_natCard _
      rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one h1) with h | h
      · exact orderOf_eq_one_iff.1 h
      · exfalso
        have h3 := Nat.le_of_dvd Nat.card_pos h2
        have := hp.two_le
        omega
    have hy1 : (MulAut.conj ψ).toMonoidHom y = 1 := by
      rw [← ha, ha1, map_one]
    exact (MulAut.conj ψ).injective (hy1.trans (map_one _).symm)
  have hbot : D = ⊥ := (Subgroup.eq_bot_iff_forall D).2 htriv
  rw [hbot, Subgroup.card_bot] at hcard
  have := hp.two_le
  nlinarith

theorem localDeltaIn_eq_bot_of_hasSplitToralPlane {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {D : Subgroup (MulAut (adjointGroup τ K))} (hDs : HasSplitToralPlane p D)
    {H : Subgroup (MulAut (adjointGroup τ K))} (hH : innerAut (adjointGroup τ K) ≤ H) :
    localDeltaIn p H D = ⊥ := by
  obtain ⟨E, hED, hE, hEc, hEs⟩ := hDs
  exact le_bot_iff.1 ((localDeltaIn_antitone H hED).trans
    (localDeltaIn_eq_bot_of_isSplitToral hp hp2 hE hEc hEs hH).le)

end Split

end CFSG.HardMathSupport.Timmesfeld.CrossChar
