module

public import CFSG.ClassicalInvolution.Uniform.U9NoExcCore
public import CFSG.ClassicalInvolution.Uniform.U8Adj
public import CFSG.ClassicalInvolution.Q3.Q3ExcToral

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.ModelFacts (Gen3 gen3_of_equiv_sl2)
open scoped MatrixGroups commutatorElement



section Toral

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot
  CFSG.LieType.Steinberg.Adjoint
open CFSG.ClassicalInvolution.Q3 (exc3_exists_rankOne_of_member)
open CFSG.ClassicalInvolution.ModelFacts (not_rootSubgroup_le_rootSubgroup_sup)

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem not_two_lt_ncard_of_span_eq {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ}
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ kernelRoots χ)
    (h : componentRootSpan K χ ⟦⟨γ, hγ⟩⟧ = rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ)) :
    ¬ 2 < (componentRoots χ ⟦⟨γ, hγ⟩⟧).ncard := by
  have hsub : componentRoots χ ⟦⟨γ, hγ⟩⟧ ⊆ {γ, -γ} := by
    intro δ hδ
    obtain ⟨hδK, hδc⟩ := hδ
    have hle := rootSubgroup_le_componentRootSpan K (χ := χ) ⟨δ, hδK⟩
    rw [hδc, h] at hle
    by_contra hnot
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnot
    exact not_rootSubgroup_le_rootSubgroup_sup (K := K) hγ.1 hδK.1 hnot.1 hnot.2 hle
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({γ, -γ} : Set (Fin τ.rank → ℤ)).ncard ≤ 2 := by
    have := Set.ncard_insert_le γ ({-γ} : Set (Fin τ.rank → ℤ))
    rw [Set.ncard_singleton] at this
    exact this
  omega

theorem toralCentralizer_map_conj_eq (hK3 : Nat.card K = 3) {b : Fin τ.rank → Kˣ}
    (hb : ∀ i, b i = 1 ∨ b i = -1)
    (hU : ∀ i j : KernelComponent (maskChar (signTupleBits b)),
      ¬ 2 < (componentRoots (maskChar (signTupleBits b)) i).ncard →
      ¬ 2 < (componentRoots (maskChar (signTupleBits b)) j).ncard → i = j)
    {L : Subgroup (ModGL τ K)} (eL : SL(2, ZMod 3) ≃* L) (hLX : L ≤ toralCentralizer τ K b)
    (hsub : CFSG.Open.IsSubnormal L (toralCentralizer τ K b)) {y : ModGL τ K}
    (hy : y ∈ toralCentralizer τ K b) : L.map (MulAut.conj y).toMonoidHom = L := by
  classical
  set X := toralCentralizer τ K b with hX
  set M := L.map (MulAut.conj y).toMonoidHom with hM
  have hMX : M ≤ X := by
    rintro _ ⟨x, hx, rfl⟩
    exact X.mul_mem (X.mul_mem hy (hLX hx)) (X.inv_mem hy)
  have hMsub : CFSG.Open.IsSubnormal M X := isSubnormal_map_conj_of_mem hsub hy
  let eM : SL(2, ZMod 3) ≃* M := eL.trans
    (L.equivMapOfInjective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective)
  obtain ⟨γ, hγ, hLγ, hrγ⟩ := exc3_exists_rankOne_of_member hK3 hb hU eL hLX hsub
  obtain ⟨γ', hγ', hMγ', hrγ'⟩ := exc3_exists_rankOne_of_member hK3 hb hU eM hMX hMsub
  have hcls : (⟦⟨γ, hγ⟩⟧ : KernelComponent (maskChar (signTupleBits b))) = ⟦⟨γ', hγ'⟩⟧ :=
    hU _ _ (not_two_lt_ncard_of_span_eq hγ hrγ) (not_two_lt_ncard_of_span_eq hγ' hrγ')
  rw [hMγ', hLγ, hcls]

end Toral

section RankOne

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot
  CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.ModelFacts
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.RouteD.Exotic

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem rankOne_le_and_isSubnormal_toralCentralizer (hK : ringChar K ≠ 2) (k : Fin τ.rank)
    {δ₂ δ₃ : Fin τ.rank → ℤ} (hS : LayerShape (zChar τ k) (Pi.single k 1) δ₂ δ₃) :
    rootSubgroup τ K (Pi.single k 1) ⊔ rootSubgroup τ K (-Pi.single k 1) ≤
        toralCentralizer τ K (zTuple τ K k) ∧
      CFSG.Open.IsSubnormal
        (rootSubgroup τ K (Pi.single k 1) ⊔ rootSubgroup τ K (-Pi.single k 1))
        (toralCentralizer τ K (zTuple τ K k)) := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  set χ := zChar τ k with hχ
  set e : Fin τ.rank → ℤ := Pi.single k 1 with he
  set i₁ : KernelComponent χ := Quotient.mk _ ⟨e, hS.mem_e⟩ with hi₁
  set i₂ : KernelComponent χ := Quotient.mk _ ⟨δ₂, hS.mem₂⟩ with hi₂
  have hi12 : i₁ ≠ i₂ := hS.mk_e_ne
  have hi21 : i₂ ≠ i₁ := fun h => hi12 h.symm
  set S₁ := componentRootSpan K χ i₁ with hS₁def
  set S₂ := componentRootSpan K χ i₂ with hS₂def
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
  have hSsup : rootSpan τ K (kernelRoots χ) = S₁ ⊔ S₂ := by
    rw [← iSup_componentRootSpan K]
    refine le_antisymm (iSup_le fun i => ?_)
      (sup_le (le_iSup (fun i => componentRootSpan K χ i) i₁)
        (le_iSup (fun i => componentRootSpan K χ i) i₂))
    rcases hS.exists_eq i with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  have hb := zTuple_mem (τ := τ) (K := K) k
  have hker : rootCharKernel (zTuple τ K k) = kernelRoots χ := by
    rw [rootCharKernel_eq_kernelRoots hK hb, signTupleBits_zTuple hK]
    rfl
  have hSX : rootSpan τ K (kernelRoots χ) ≤ toralCentralizer τ K (zTuple τ K k) := by
    rw [← hker]
    exact rootSpan_rootCharKernel_le_toralCentralizer _
  have hNnorm : ((rootSpan τ K (kernelRoots χ)).subgroupOf
      (toralCentralizer τ K (zTuple τ K k))).Normal := by
    have := (odd_toral_involution_centralizer_p_component_root_reduction τ K hK (zTuple τ K k)
      hb).2.1
    rwa [hker] at this
  have hS₁S : S₁ ≤ rootSpan τ K (kernelRoots χ) := hSsup ▸ le_sup_left
  have hN₁ : (S₁.subgroupOf (rootSpan τ K (kernelRoots χ))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hS₁S, hSsup]
    refine sup_le Subgroup.le_normalizer ?_
    intro x hx
    exact Subgroup.centralizer_le_normalizer _ (componentRootSpan_le_centralizer K hi21 hx)
  rw [← hS₁]
  exact ⟨hS₁S.trans hSX, CFSG.Open.IsSubnormal.step hS₁S hN₁
    (CFSG.Open.IsSubnormal.step hSX hNnorm (CFSG.Open.IsSubnormal.refl _))⟩

end RankOne

section Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot
  CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.Q3 (UniqIsolated exc3_small_unique exc3_nonempty_equiv_sl2Three)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

variable {τ : Tag} {K : Type} [Group K] [Finite K]

theorem twinRatio_notMem_center_of_toral (θ : K →* ModGL τ (GaloisField 3 1))
    (hker : θ.ker ≤ Subgroup.center K) (hk3 : ∀ x ∈ θ.ker, x ^ 3 = 1 → x = 1)
    (hcen : ∀ c ∈ Subgroup.center K, θ c = 1)
    (hadj : ∀ g : K, θ g ∈ adjointGroup τ (GaloisField 3 1)) {Fund : Set (Subgroup K)}
    (hsingle : ∀ R ∈ Fund, ∀ R' ∈ Fund, ∃ g : K, R' = conjSub g R)
    (hgen : ∀ R ∈ Fund, Gen3 R) (k : Fin τ.rank) {δ₂ δ₃ : Fin τ.rank → ℤ}
    (hS : LayerShape (zChar τ k) (Pi.single k 1) δ₂ δ₃)
    (hU : ∀ χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ, UniqIsolated τ χ)
    {R₀ : Subgroup K} (hR₀ : R₀ ∈ Fund) (e₀ : R₀ ≃* SL(2, GaloisField 3 1))
    (himg : R₀.map θ = rootSubgroup τ (GaloisField 3 1) (Pi.single k 1) ⊔
      rootSubgroup τ (GaloisField 3 1) (-Pi.single k 1))
    (hinj : ∀ x ∈ R₀, θ x = 1 → x = 1) {R₁ R₂ : Subgroup K} (h₁ : R₁ ∈ Fund) (h₂ : R₂ ∈ Fund)
    (hne : R₁ ≠ R₂) (e₁ : R₁ ≃* SL(2, GaloisField 3 1)) (e₂ : R₂ ≃* SL(2, GaloisField 3 1)) :
    sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∉ Subgroup.center K := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hK : ringChar (GaloisField 3 1) ≠ 2 :=
    CFSG.ClassicalInvolution.ModelFacts.ringChar_galoisField_ne_two hp2
  have hK3 : Nat.card (GaloisField 3 1) = 3 := natCard_galoisField_three_one
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_natCard_galoisField_three_one
  have : Finite (ModGL τ (GaloisField 3 1)) := finite_modGL
  set F := GaloisField 3 1 with hF
  set e : Fin τ.rank → ℤ := Pi.single k 1 with he
  set S₁ : Subgroup (ModGL τ F) := rootSubgroup τ F e ⊔ rootSubgroup τ F (-e) with hS₁
  obtain ⟨hS₁X, hS₁sub⟩ := rankOne_le_and_isSubnormal_toralCentralizer hK k hS
  have hθR : Function.Injective (θ.comp R₀.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hinj x.1 x.2 hx)
  have hrange : (θ.comp R₀.subtype).range = S₁ := by
    rw [← himg]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  let eS : SL(2, F) ≃* S₁ := e₀.symm.trans
    ((MonoidHom.ofInjective hθR).trans (MulEquiv.subgroupCongr hrange))
  obtain ⟨eL⟩ := exc3_nonempty_equiv_sl2Three hK3 eS
  have hb := zTuple_mem (τ := τ) (K := F) k
  have hU' : ∀ i j : KernelComponent (maskChar (signTupleBits (zTuple τ F k))),
      ¬ 2 < (componentRoots (maskChar (signTupleBits (zTuple τ F k))) i).ncard →
      ¬ 2 < (componentRoots (maskChar (signTupleBits (zTuple τ F k))) j).ncard → i = j :=
    fun i j hi hj => exc3_small_unique hK (hU _) i j hi hj
  refine twinRatio_notMem_center_of_normalizes θ hker hk3 hcen hsingle hgen hodd hR₀ e₀ ?_ h₁ h₂
    hne e₁ e₂
  intro g hg
  set z := θ (sl2Inv e₀) with hz
  have hz_mem : z ∈ S₁ := himg ▸ Subgroup.mem_map_of_mem θ (sl2Inv_mem e₀)
  have hz2 : z * z = 1 := by rw [hz, ← map_mul, sl2Inv_mul_self hodd e₀, map_one]
  have hz1 : z ≠ 1 := fun h => sl2Inv_ne_one hodd e₀ (hinj _ (sl2Inv_mem e₀) h)
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hzval : z = torusElt τ F k (-1) := eq_torusElt_neg_one hK k hz_mem hzord
  have hzd : z = rootDiagUnit τ (zTuple τ F k) := hzval.trans (torusElt_eq_rootDiagUnit k (-1))
  have hzc : z * θ g = θ g * z := hg.symm
  have hyX : θ g ∈ toralCentralizer τ F (zTuple τ F k) := by
    rw [mem_toralCentralizer]
    refine ⟨hadj g, ?_⟩
    rw [← hzd, hzc]
    group
  have hconj := toralCentralizer_map_conj_eq hK3 hb hU' eL hS₁X hS₁sub hyX
  have h1 : (conjSub g R₀).map θ = S₁.map (MulAut.conj (θ g)).toMonoidHom := by
    rw [← himg]
    change (R₀.map (MulAut.conj g).toMonoidHom).map θ = _
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [map_mul, map_inv]
  rw [h1, hconj, himg]

end Adjoint

section AdjointModel

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.RouteD.Exotic

variable {τ : Tag}

theorem rootGroup_map_subtype {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (rootGroup (rootOperatorFamily τ) (GaloisField 3 1) α).map
        (adjointGroup τ (GaloisField 3 1)).subtype =
      rootSubgroup τ (GaloisField 3 1) α := by
  rw [← subgroupOf_rootSubgroup_eq_rootGroup (rootOperatorFamily τ) hα,
    Subgroup.subgroupOf_map_subtype]
  exact inf_of_le_left (rootSubgroup_le_adjointGroup α)

theorem twinRatio_notMem_center_adjoint (k : Fin τ.rank) {δ₂ δ₃ : Fin τ.rank → ℤ}
    (hS : LayerShape (zChar τ k) (Pi.single k 1) δ₂ δ₃)
    (hU : ∀ χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ, CFSG.ClassicalInvolution.Q3.UniqIsolated τ χ)
    {Fund : Set (Subgroup ↥(adjointGroup τ (GaloisField 3 1)))}
    (hsingle : ∀ R ∈ Fund, ∀ R' ∈ Fund, ∃ g, R' = conjSub g R)
    (hgen : ∀ R ∈ Fund, Gen3 R) {R₀ : Subgroup ↥(adjointGroup τ (GaloisField 3 1))}
    (hR₀ : R₀ ∈ Fund)
    (hR₀eq : R₀ = rootGroup (rootOperatorFamily τ) (GaloisField 3 1) (Pi.single k 1) ⊔
      rootGroup (rootOperatorFamily τ) (GaloisField 3 1) (-Pi.single k 1))
    (e₀ : R₀ ≃* SL(2, GaloisField 3 1)) {R₁ R₂ : Subgroup ↥(adjointGroup τ (GaloisField 3 1))}
    (h₁ : R₁ ∈ Fund) (h₂ : R₂ ∈ Fund) (hne : R₁ ≠ R₂) (e₁ : R₁ ≃* SL(2, GaloisField 3 1))
    (e₂ : R₂ ≃* SL(2, GaloisField 3 1)) :
    sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∉ Subgroup.center ↥(adjointGroup τ (GaloisField 3 1)) := by
  classical
  have : Finite (ModGL τ (GaloisField 3 1)) := finite_modGL
  refine twinRatio_notMem_center_of_toral (adjointGroup τ (GaloisField 3 1)).subtype ?_ ?_ ?_
    (fun g => g.2) hsingle hgen k hS hU hR₀ e₀ ?_ ?_ h₁ h₂ hne e₁ e₂
  · rw [Subgroup.ker_subtype]
    exact bot_le
  · intro x hx _
    exact Subtype.ext (MonoidHom.mem_ker.1 hx)
  · intro c hc
    have hcb := (Subgroup.eq_bot_iff_forall _).1
      (center_adjointGroup_eq_bot (τ := τ) (K := GaloisField 3 1)) c hc
    rw [hcb, map_one]
  · rw [hR₀eq, Subgroup.map_sup, rootGroup_map_subtype hS.mem_e.1,
      rootGroup_map_subtype (CFSG.ClassicalInvolution.ModelFacts.neg_mem_kernelRoots hS.mem_e).1]
  · intro x _ hx
    exact Subtype.ext (MonoidHom.mem_ker.1 hx)

end AdjointModel

section Cover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.RouteD.Exotic

variable {τ : Tag} {K : Type} [Group K] [Finite K]

theorem twinRatio_notMem_center_cover (θ : K →* ↥(adjointGroup τ (GaloisField 3 1)))
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center K)
    (hk3 : ∀ x ∈ θ.ker, x ^ 3 = 1 → x = 1) (k : Fin τ.rank) {δ₂ δ₃ : Fin τ.rank → ℤ}
    (hS : LayerShape (zChar τ k) (Pi.single k 1) δ₂ δ₃)
    (hU : ∀ χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ, CFSG.ClassicalInvolution.Q3.UniqIsolated τ χ)
    {Fund : Set (Subgroup K)} (hsingle : ∀ R ∈ Fund, ∀ R' ∈ Fund, ∃ g, R' = conjSub g R)
    (hgen : ∀ R ∈ Fund, Gen3 R) {R₀ : Subgroup K} (hR₀ : R₀ ∈ Fund)
    (e₀ : R₀ ≃* SL(2, GaloisField 3 1))
    (himg : R₀.map θ = rootGroup (rootOperatorFamily τ) (GaloisField 3 1) (Pi.single k 1) ⊔
      rootGroup (rootOperatorFamily τ) (GaloisField 3 1) (-Pi.single k 1))
    (hinj : ∀ x ∈ R₀, θ x = 1 → x = 1) {R₁ R₂ : Subgroup K} (h₁ : R₁ ∈ Fund) (h₂ : R₂ ∈ Fund)
    (hne : R₁ ≠ R₂) (e₁ : R₁ ≃* SL(2, GaloisField 3 1)) (e₂ : R₂ ≃* SL(2, GaloisField 3 1)) :
    sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∉ Subgroup.center K := by
  classical
  have : Finite (ModGL τ (GaloisField 3 1)) := finite_modGL
  refine twinRatio_notMem_center_of_toral ((adjointGroup τ (GaloisField 3 1)).subtype.comp θ)
    ?_ ?_ ?_ (fun g => (θ g).2) hsingle hgen k hS hU hR₀ e₀ ?_ ?_ h₁ h₂ hne e₁ e₂
  · intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact Subtype.ext hx
  · intro x hx h3
    apply hk3 x _ h3
    rw [MonoidHom.mem_ker] at hx ⊢
    exact Subtype.ext hx
  · intro c hc
    have hcc : θ c ∈ Subgroup.center ↥(adjointGroup τ (GaloisField 3 1)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := hθ y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc x]
    have hcb := (Subgroup.eq_bot_iff_forall _).1
      (center_adjointGroup_eq_bot (τ := τ) (K := GaloisField 3 1)) _ hcc
    simp [hcb]
  · rw [← Subgroup.map_map, himg, Subgroup.map_sup, rootGroup_map_subtype hS.mem_e.1,
      rootGroup_map_subtype (CFSG.ClassicalInvolution.ModelFacts.neg_mem_kernelRoots hS.mem_e).1]
  · intro x hx h1
    exact hinj x hx (Subtype.ext h1)

end Cover

end CFSG.ClassicalInvolution.Uniform
