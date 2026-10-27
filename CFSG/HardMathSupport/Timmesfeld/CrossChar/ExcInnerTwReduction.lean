module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {L : Type} [Field L]

@[expose] def RootSL2Generated
    (A : Subgroup (ModGL τ L)) : Prop :=
  Subgroup.closure {x : A | ∃ β, IsRoot τ β ∧ (x : ModGL τ L) ∈ rootSpan τ L {β, -β}} = ⊤

@[expose] def RootComponentsQuasisimple
    (A : Subgroup (ModGL τ L)) (p : ℕ) : Prop :=
  ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ A → rootDiagUnit τ a ≠ 1 →
    rootDiagUnit τ a ^ p = 1 → ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (componentRootSpan L (rootCharHom a) i ⊓ A : Subgroup (ModGL τ L))

theorem exists_rootChar_eq_one_of_finite
    {p : ℕ} (hp : p.Prime) {B : Subgroup (ModGL τ L)} [Finite B]
    (hB : B ≤ torusGroup τ L) (hpow : ∀ x ∈ B, x ^ p = 1) (hcard : p < Nat.card B)
    (α : Fin τ.rank → ℤ) :
    ∃ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ B ∧ rootDiagUnit τ a ≠ 1 ∧ rootChar a α = 1 := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  by_contra hne
  push Not at hne
  set T₀ := B.comap (rootDiagUnitHom τ L) with hT₀
  have : Finite T₀ := Finite.of_injective (fun a : T₀ => (⟨rootDiagUnit τ a, a.2⟩ : B))
    fun a b h => Subtype.ext (rootDiagUnit_injective (congrArg Subtype.val h))
  let χ : (Fin τ.rank → Lˣ) →* Lˣ :=
    { toFun := fun a => rootChar a α
      map_one' := by simp [rootChar]
      map_mul' := fun a b => by simp only [rootChar, Pi.mul_apply, mul_zpow,
        Finset.prod_mul_distrib] }
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
    have h2 : rootDiagUnit τ (a ^ p) = rootDiagUnit τ a ^ p := map_pow (rootDiagUnitHom τ L) a p
    have h3 : rootDiagUnit τ a ^ p = 1 := hpow _ ha
    exact rootDiagUnit_injective (by rw [h2, h3, rootDiagUnit_one])
  let f : T₀ → rootsOfUnity p L := fun a => ⟨χ a, by
    rw [mem_rootsOfUnity, ← map_pow, hpowa a a.2, map_one]⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h3 : χ ((a : Fin τ.rank → Lˣ) * (b : Fin τ.rank → Lˣ)⁻¹) = 1 := by
      have : χ a = χ b := congrArg (fun z : rootsOfUnity p L => (z : Lˣ)) hab
      rw [map_mul, map_inv, this, mul_inv_cancel]
    have h4 := hker _ (T₀.mul_mem a.2 (T₀.inv_mem b.2)) h3
    exact Subtype.ext (mul_inv_eq_one.1 h4)
  have h5 := Nat.card_le_card_of_injective f hf
  have h6 := card_rootsOfUnity L p
  omega

theorem isSubnormal_inf_subgroupOf {G : Type*} [Group G] {S T : Subgroup G}
    (hS : (S.subgroupOf T).IsSubnormal) (A : Subgroup G) :
    ((S ⊓ A).subgroupOf (T ⊓ A)).IsSubnormal := by
  convert hS.comap (Subgroup.inclusion (inf_le_left : T ⊓ A ≤ T)) using 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_inclusion,
    Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, (Subgroup.mem_inf.1 x.2).2⟩⟩

theorem localDeltaIn_eq_bot_of_rootSL2 {A : Subgroup (ModGL τ L)} [Finite A]
    (hAC : A ≤ adjointGroup τ L) (hinj : Function.Injective (MulAut.conj : A →* MulAut A))
    {p : ℕ} (hp : p.Prime) {ζ : Lˣ} (hζp : orderOf ζ = p) (hζ2 : ζ ^ 2 ≠ 1)
    (hζA : ∀ (w : WeylGroup τ) (k : Fin τ.rank),
      canonicalRep (coxeterSystem τ) L w * torusElt τ L k ζ *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ ∈ A)
    (hgen : RootSL2Generated A) (hqs : RootComponentsQuasisimple A p)
    {H : Subgroup (MulAut A)} (hH : innerAut A ≤ H) (D₀ : Subgroup A)
    (hpow : ∀ x ∈ D₀, x ^ p = 1) (hcard : p < Nat.card D₀)
    (htor : ∀ x ∈ D₀, (x : ModGL τ L) ∈ torusGroup τ L) :
    localDeltaIn p H (D₀.map (MulAut.conj : A →* MulAut A)) = ⊥ := by
  classical
  have hB : D₀.map A.subtype ≤ torusGroup τ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact htor x hx
  have hBpow : ∀ y ∈ D₀.map A.subtype, y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hpow x hx, map_one]
  have hBcard : p < Nat.card (D₀.map A.subtype) := by
    rwa [Subgroup.card_map_of_injective A.subtype_injective]
  have : Finite (D₀.map A.subtype) :=
    Finite.of_surjective (A.subtype.subgroupMap D₀) (A.subtype.subgroupMap_surjective D₀)
  refine localDeltaIn_eq_bot_of_inner_components_ambient hp hinj hH D₀ hgen ?_
  rintro s ⟨β, hβ, hsβ⟩
  obtain ⟨w, k, rfl⟩ := isRoot_iff_exists_smul_single.1 hβ
  obtain ⟨a, ⟨d, hd, hda⟩, ha1, hχ⟩ := exists_rootChar_eq_one_of_finite hp hB hBpow hBcard
    (w • (Pi.single k 1 : Fin τ.rank → ℤ))
  have hda' : (d : ModGL τ L) = rootDiagUnit τ a := hda
  have hαk : w • (Pi.single k 1 : Fin τ.rank → ℤ) ∈ kernelRoots (rootCharHom a) := ⟨hβ, hχ⟩
  have hαi : w • (Pi.single k 1 : Fin τ.rank → ℤ) ∈
      componentRoots (rootCharHom a) ⟦⟨_, hαk⟩⟧ := ⟨hαk, rfl⟩
  have hnegi := (isRootComponent_componentRoots (χ := rootCharHom a) ⟦⟨_, hαk⟩⟧).neg_mem _ hαi
  have hQ : rootSpan τ L {w • (Pi.single k 1 : Fin τ.rank → ℤ),
      -(w • (Pi.single k 1 : Fin τ.rank → ℤ))} ≤
      componentRootSpan L (rootCharHom a) ⟦⟨_, hαk⟩⟧ := by
    refine iSup₂_le fun γ hγ => le_iSup₂_of_le (f := fun δ (_ : δ ∈ componentRoots
      (rootCharHom a) ⟦⟨_, hαk⟩⟧) => rootSubgroup τ L δ) γ ?_ le_rfl
    rcases hγ with rfl | hγ
    · exact hαi
    · rw [Set.mem_singleton_iff.1 hγ]
      exact hnegi
  have hdA : rootDiagUnit τ a ∈ A := hda' ▸ d.2
  refine ⟨d, hd, fun h => ha1 (by rw [← hda', h]; rfl),
    componentRootSpan L (rootCharHom a) ⟦⟨_, hαk⟩⟧ ⊓ A, ⟨hQ hsβ, s.2⟩, ?_, ?_, ?_, ?_⟩
  · rw [hda']
    exact fun x hx => Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2,
      (Subgroup.mem_inf.1 (componentRootSpan_le_toralCentralizer a _ (Subgroup.mem_inf.1 hx).1)).2⟩
  · exact hqs a hdA (fun h => ha1 h) (by rw [← hda', ← Subgroup.coe_pow, hpow d hd]; rfl) _
  · rw [hda']
    have h1 := isSubnormal_inf_subgroupOf (isSubnormal_componentRootSpan a ⟦⟨_, hαk⟩⟧) A
    have h2 : toralCentralizer τ L a ⊓ A = A ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
      ext x
      simp only [toralCentralizer, Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hAC h.1, h.2⟩, h.1⟩⟩
    rwa [h2] at h1
  · have hmem := componentTorus_le_componentRootSpan L (rootCharHom a) _
      (canonicalRep_conj_torusElt_mem (K := L) hαi ζ)
    have hmemA : canonicalRep (coxeterSystem τ) L w * torusElt τ L k ζ *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ ∈
        componentRootSpan L (rootCharHom a) ⟦⟨_, hαk⟩⟧ ⊓ A :=
      Subgroup.mem_inf.2 ⟨hmem, hζA w k⟩
    have h1 := orderOf_dvd_natCard (⟨_, hmemA⟩ :
      ↥(componentRootSpan L (rootCharHom a) ⟦⟨_, hαk⟩⟧ ⊓ A))
    rw [Subgroup.orderOf_mk, orderOf_canonicalRep_conj_torusElt hp w k hζp hζ2] at h1
    rw [Nat.Prime.coprime_iff_not_dvd hp, not_not]
    exact h1

end CFSG.HardMathSupport.Timmesfeld.CrossChar
