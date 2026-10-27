module

public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.PlaneAssembly
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.PerxFamily
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.Layer01
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.Cert01
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.SplitTwo

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Lattice CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KGD

open scoped Matrix

set_option linter.unusedSectionVars false


section Kill

theorem exists_kill_elem {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (F : E7ThreeFrame K L ℓ f p (-1)) (hK : Nat.card K = ℓ ^ f) [Fact p.Prime]
    {c : adjointGroup .E7 K} {E : Subgroup (adjointGroup .E7 K)} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3)
    (hT : ∀ x ∈ E, psiC F.g0 c x ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {y : adjointGroup .E7 K} (hy : y ∈ E) {τ : List ℤ} {X : List (List ℤ)} (hX : SpanGen τ X) :
    ∃ e ∈ E, e ∉ Subgroup.zpowers y ∧ ∀ be : Fin Tag.E7.rank → Lˣ,
      rootDiagUnit .E7 be = psiC F.g0 c e → ∀ l ∈ X, rootChar be (toVec Tag.E7.rank l) = 1 := by
  classical
  have hFr : ∀ x, iterateFrobenius L ℓ f x = x ^ Nat.card K := fun x => by
    rw [hK]; exact iterateFrobenius_def ℓ f x
  have hinj : Function.Injective (rootDiagUnitHom .E7 L) := rootDiagUnit_injective
  have hbE : ∀ e : E, ∃ b : Fin Tag.E7.rank → Lˣ,
      rootDiagUnit .E7 b = (psiC F.g0 c).comp E.subtype e := by
    intro e
    have h := hT e e.2
    rw [F.hT] at h
    obtain ⟨b, -, hb⟩ := h
    exact ⟨b, hb⟩
  obtain ⟨χ, hχ⟩ := exists_rootCharHom ((psiC F.g0 c).comp E.subtype) hbE (toVec Tag.E7.rank τ)
  obtain ⟨e, hey, hχe⟩ := CFSG.HardMathSupport.Lang.TwE6Step3.exists_mem_ker_not_mem_zpowers hE hEc
    χ hy
  refine ⟨e, e.2, hey, fun be hbe l hl => ?_⟩
  have hTe := hT e e.2
  rw [F.hT] at hTe
  obtain ⟨be₀, hbeF, hbe₀⟩ := hTe
  have hbe_eq : be = be₀ := hinj (hbe.trans hbe₀.symm)
  subst hbe_eq
  have hbe' : rootDiagUnit .E7 be = (psiC F.g0 c).comp E.subtype e := hbe
  have hτ : rootChar be (toVec Tag.E7.rank τ) = 1 := by
    rw [← hχ e be hbe']
    exact hχe
  exact rootChar_kill_of_spanGen hFr hbeF hX hτ l hl

theorem mul_commute_rootDiagUnit {L : Type} [Field L] [IsAlgClosed L] (be : Fin Tag.E7.rank → Lˣ)
    {S : Set (Fin Tag.E7.rank → ℤ)} (hS : S ⊆ rootCharKernel be) {t a : ModGL .E7 L}
    (ht : t ∈ torusGroup .E7 L) (ha : a ∈ rootSpan .E7 L S) :
    rootDiagUnit .E7 be * (t * a) = (t * a) * rootDiagUnit .E7 be := by
  have h1 : t * rootDiagUnit .E7 be = rootDiagUnit .E7 be * t :=
    torusGroup_comm ht (rootDiagUnit_mem_torusGroup be)
  have h2 : rootDiagUnit .E7 be * a = a * rootDiagUnit .E7 be :=
    (Subgroup.mem_centralizer_singleton_iff.1 (CFSG.LieType.Chevalley.rootSpan_le_centralizer be hS ha)).symm
  calc rootDiagUnit .E7 be * (t * a) = (rootDiagUnit .E7 be * t) * a := by group
    _ = (t * rootDiagUnit .E7 be) * a := by rw [h1]
    _ = t * (rootDiagUnit .E7 be * a) := by group
    _ = t * (a * rootDiagUnit .E7 be) := by rw [h2]
    _ = (t * a) * rootDiagUnit .E7 be := by group

end Kill

section Main

theorem e7SixLinesKind_01 : E7SixLinesKind [0, 1] := by
  intro K _ _ ℓ f p _ _ L _ _ _ _ F hf hK hp hp3 hpf c E hE hEc hT y hy hy1 b hb cert hcert hker
    hkinds hσ0 k hk
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hFr : ∀ x, iterateFrobenius L ℓ f x = x ^ Nat.card K := fun x => by
    rw [hK]; exact iterateFrobenius_def ℓ f x
  have hε : ((-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1) := Or.inr rfl
  have hstab := e7T3_stabHyp F hK hp hp3 hε hpf
  have hyo : orderOf y = p := orderOf_eq_prime (hE.2 y hy) hy1
  have hhy : F.g0⁻¹ * adjEmb .E7 K L (c * y * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    simpa [psiC_apply] using hT y hy
  obtain ⟨b', hb', hap, hb1, hbh, huniq⟩ := e7_three_prelim F hp hyo c hhy
  have hbb : b = b' := huniq b (by rw [hb, psiC_apply])
  rw [← hbb] at hbh
  have hq2 : 2 < ℓ ^ f := by
    have hKq : 2 ≤ Nat.card K := Finite.one_lt_card
    rw [← hK]
    exact e7T3_q_gt_two hp3 rfl hKq hpf rfl
  obtain ⟨hgood, hσB, hσspan, τ, hτA, hτspan⟩ := cert_cases01 cert hcert hkinds hσ0
  have hcomps := hgood.1
  rcases hcc : cert.comps with _ | ⟨cm₀, _ | ⟨cm₁, _ | ⟨cm₂, rest⟩⟩⟩
  · rw [hcc] at hkinds; simp at hkinds
  · rw [hcc] at hkinds; simp at hkinds
  · rw [hcc] at hkinds hcomps
    have hg₀ : cm₀.Good e7T3Word cert.w := hcomps cm₀ List.mem_cons_self
    have hg₁ : cm₁.Good e7T3Word cert.w :=
      hcomps cm₁ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    have hk₀ : cm₀.kind < 4 := hg₀.2.1
    have hk₁ : cm₁.kind < 4 := hg₁.2.1
    have hkk : cm₀.kind = 0 ∧ cm₁.kind = 1 := by simpa using hkinds
    have hset := e7T3_rootSet_two hcc hk₀ hk₁
    rw [hkk.1, hkk.2] at hset
    set v := (coxeterSystem Tag.E7).wordProd cert.w with hv
    have hKer : rootCharKernel b = (fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 0) ∪
        (fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 1) := hker.trans hset
    obtain ⟨P₀, hP₀eq, hfac₀⟩ := e7T3_layer_A2_eq (k := K) hf hK hε (fun _ => hq2) F.hnW hg₀ hkk.1
    obtain ⟨P₁, hfac₁⟩ := e7T3_layer_A1 hf hε F.hnW hg₁ hkk.2
    rw [hkk.1] at hP₀eq hfac₀
    rw [hkk.2] at hfac₁
    have hS₀ := isRoot_image_parabolicRoots v (e7T3J 0)
    have hS₁ := isRoot_image_parabolicRoots v (e7T3J 1)
    have horth : ∀ α ∈ (fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 0),
        ∀ β ∈ (fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 1),
          iform (τ := Tag.E7) α β = 0 := by
      rintro _ ⟨α', hα', rfl⟩ _ ⟨β', hβ', rfl⟩
      rw [iform_smul]
      rw [parabolicRoots_e7T3J (by norm_num : (0 : ℕ) < 4)] at hα'
      rw [parabolicRoots_e7T3J (by norm_num : (1 : ℕ) < 4)] at hβ'
      obtain ⟨l, hl, rfl⟩ := hα'
      obtain ⟨l', hl', rfl⟩ := hβ'
      exact e7T3_orth_A2_A1 l hl l' hl'
    have horth' : ∀ α ∈ (fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 0),
        ∀ β ∈ (fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 1),
          α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ β) = 0 := fun α hα β hβ => by
      rw [dotProduct_mulVec_eq_iform]
      exact horth α hα β hβ
    have hfam := sigmaFactor_union_E7 hS₀ hS₁ horth hfac₀ hfac₁
    obtain ⟨ψ, hψinj, hψ, hψHQ, hψθ, hPψ⟩ := e7_perx_of_family F hK hp hyo c hstab hhy hbh
      (P := Sum.elim (fun _ : Unit => P₀) (fun _ : Unit => P₁)) (by rw [hKer]; exact hfam)
    have hψ' : ∀ z, ψ z = psiC F.g0 c (z : adjointGroup .E7 K) := fun z => by
      rw [hψ, psiC_apply]
    have hkC : k ∈ Subgroup.centralizer ({y} : Set (adjointGroup .E7 K)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]; exact hk
    set k' : Subgroup.centralizer ({y} : Set (adjointGroup .E7 K)) := ⟨k, hkC⟩ with hk'
    have hm : ψ k' ∈ torusGroup .E7 L ⊔ rootSpan .E7 L
        ((fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 0) ∪
          (fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 1)) := by
      have := hψHQ k'
      rwa [hKer] at this
    have hJ₀ := e7T3_stab_A2 hε F.hnW hg₀ hkk.1
    have hJ₁ := e7T3_stab_A1 hε F.hnW hg₁ hkk.2
    obtain ⟨t, htH, htθ, a₀, ha₀, ha₀θ, a₁, ha₁, ha₁θ, hmeq⟩ := e7_fixedSplit_A2_3A1
      iterateFrobenius_bijective Finite.one_lt_card hFr F.hnm v hJ₀ hJ₁ hm (hψθ k')
    have ha₀P : a₀ ∈ P₀ := by
      rw [hP₀eq]
      exact Subgroup.mem_inf.2 ⟨ha₀, ha₀θ⟩
    obtain ⟨k₀', hk₀'⟩ := hPψ (Sum.inl ()) ha₀P
    have hcomm : a₀ * a₁ = a₁ * a₀ :=
      rootSpan_commute_of_orth (τ := Tag.E7) (Or.inr (Or.inr (Or.inl rfl))) hS₀ hS₁ horth'
        a₀ ha₀ a₁ ha₁
    have hψk₁ : ψ (k' * k₀'⁻¹) = t * a₁ := by
      rw [map_mul, map_inv, hk₀', hmeq]
      calc t * a₀ * a₁ * a₀⁻¹ = t * (a₀ * a₁) * a₀⁻¹ := by group
        _ = t * (a₁ * a₀) * a₀⁻¹ := by rw [hcomm]
        _ = t * a₁ := by group
    obtain ⟨e₁, he₁E, he₁y, he₁k⟩ := exists_kill_elem F hK hE hEc hT hy hσspan
    have hS₁sub : ∀ be : Fin Tag.E7.rank → Lˣ,
        (∀ l ∈ e7CompB cert, rootChar be (toVec Tag.E7.rank l) = 1) →
        (fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 1) ⊆ rootCharKernel be := by
      intro be hbe α hα
      refine ⟨hS₁ α hα, ?_⟩
      obtain ⟨γ, hγ, rfl⟩ := hα
      rw [parabolicRoots_e7T3J (by norm_num : (1 : ℕ) < 4)] at hγ
      obtain ⟨l, hl, rfl⟩ := hγ
      show rootChar be (v • toVec Tag.E7.rank l) = 1
      rw [hv, wordProd_smul_toVec7]
      exact hbe _ (List.mem_map.2 ⟨l, hl, rfl⟩)
    have hS₀sub : ∀ be : Fin Tag.E7.rank → Lˣ,
        (∀ l ∈ e7CompA cert, rootChar be (toVec Tag.E7.rank l) = 1) →
        (fun γ => v • γ) '' parabolicRoots Tag.E7 (e7T3J 0) ⊆ rootCharKernel be := by
      intro be hbe α hα
      refine ⟨hS₀ α hα, ?_⟩
      obtain ⟨γ, hγ, rfl⟩ := hα
      rw [parabolicRoots_e7T3J (by norm_num : (0 : ℕ) < 4)] at hγ
      obtain ⟨l, hl, rfl⟩ := hγ
      show rootChar be (v • toVec Tag.E7.rank l) = 1
      rw [hv, wordProd_smul_toVec7]
      exact hbe _ (List.mem_map.2 ⟨l, hl, rfl⟩)
    have hψk₁' : psiC F.g0 c (((k' * k₀'⁻¹ : Subgroup.centralizer
        ({y} : Set (adjointGroup .E7 K))) : adjointGroup .E7 K)) = t * a₁ :=
      (hψ' _).symm.trans hψk₁
    have hcomm₁ : ((k' * k₀'⁻¹ : Subgroup.centralizer
        ({y} : Set (adjointGroup .E7 K))) : adjointGroup .E7 K) * e₁ =
        e₁ * ((k' * k₀'⁻¹ : Subgroup.centralizer
          ({y} : Set (adjointGroup .E7 K))) : adjointGroup .E7 K) := by
      apply psiC_injective F.g0 c
      have hTe := hT e₁ he₁E
      rw [F.hT] at hTe
      obtain ⟨be, -, hbe⟩ := hTe
      have hbe' : rootDiagUnit .E7 be = psiC F.g0 c e₁ := hbe
      have h := mul_commute_rootDiagUnit be (hS₁sub be (he₁k be hbe')) htH ha₁
      rw [map_mul, map_mul, hψk₁', ← hbe']
      exact h.symm
    have hk₁y : ((k' * k₀'⁻¹ : Subgroup.centralizer ({y} : Set (adjointGroup .E7 K))) :
        adjointGroup .E7 K) * y = y * ((k' * k₀'⁻¹ : Subgroup.centralizer
          ({y} : Set (adjointGroup .E7 K))) : adjointGroup .E7 K) :=
      Subgroup.mem_centralizer_singleton_iff.1 (k' * k₀'⁻¹).2
    have h₁ := CFSG.HardMathSupport.Lang.TwE6Step3.mem_hyperClosure_of_commute_pair hE hEc hy
      he₁E hy1 he₁y hk₁y hcomm₁
    obtain ⟨e₀, he₀E, he₀y, he₀k⟩ := exists_kill_elem F hK hE hEc hT hy hτspan
    have hψk₀ : psiC F.g0 c (k₀' : adjointGroup .E7 K) = a₀ := (hψ' k₀').symm.trans hk₀'
    have hcomm₀ : (k₀' : adjointGroup .E7 K) * e₀ = e₀ * (k₀' : adjointGroup .E7 K) := by
      apply psiC_injective F.g0 c
      have hTe := hT e₀ he₀E
      rw [F.hT] at hTe
      obtain ⟨be, -, hbe⟩ := hTe
      have hbe' : rootDiagUnit .E7 be = psiC F.g0 c e₀ := hbe
      have h := mul_commute_rootDiagUnit be (hS₀sub be (he₀k be hbe')) (one_mem _)
        (a := a₀) ha₀
      rw [map_mul, map_mul, hψk₀, ← hbe']
      simpa using h.symm
    have hk₀y : (k₀' : adjointGroup .E7 K) * y = y * (k₀' : adjointGroup .E7 K) :=
      Subgroup.mem_centralizer_singleton_iff.1 k₀'.2
    have h₀ := CFSG.HardMathSupport.Lang.TwE6Step3.mem_hyperClosure_of_commute_pair hE hEc hy
      he₀E hy1 he₀y hk₀y hcomm₀
    have : k = ((k' * k₀'⁻¹ : Subgroup.centralizer ({y} : Set (adjointGroup .E7 K))) :
        adjointGroup .E7 K) * (k₀' : adjointGroup .E7 K) := by
      simp [hk']
    rw [this]
    exact mul_mem h₁ h₀
  · rw [hcc] at hkinds; simp at hkinds

end Main

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
