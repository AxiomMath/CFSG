module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QXTor
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QXComp
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QCov

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.Foote5.OddLieCore.Exc

theorem evenCent_of_mulEquiv {X : Type} [Group X] {z : X} (hz : orderOf z = 2)
    {H : Type*} [Group H] (Θ : centralizer ({z} : Set X) ≃* H) {ι : Type*}
    (S : ι → Subgroup H) (hS : ∀ i, IsComponent (S i)) (hSe : ∀ i, Even (Nat.card (S i)))
    (hcomm : ∀ g h : H, (∀ i, ∀ s ∈ S i, s * g = g * s) → (∀ i, ∀ s ∈ S i, s * h = h * s) →
      g * h = h * g)
    (hinv : ∀ g h : H, (∀ i, ∀ s ∈ S i, s * g = g * s) → (∀ i, ∀ s ∈ S i, s * h = h * s) →
      g * g = 1 → h * h = 1 → g ≠ 1 → h ≠ 1 → g = h) :
    EvenCentComm X z ∧ EvenCentInv X z := by
  have hlift : ∀ y : centralizer ({z} : Set X),
      (∀ K : Subgroup (centralizer ({z} : Set X)), IsComponent K → Even (Nat.card K) →
        ∀ k ∈ K, (k : X) * (y : X) = (y : X) * k) → ∀ i, ∀ s ∈ S i, s * Θ y = Θ y * s := by
    intro y hy i s hs
    have hK : IsComponent ((S i).map Θ.symm.toMonoidHom) :=
      LocalCores.isComponent_map_mulEquiv Θ.symm (hS i)
    have hKe : Even (Nat.card ((S i).map Θ.symm.toMonoidHom)) := by
      rw [← Nat.card_congr ((S i).equivMapOfInjective _ Θ.symm.injective).toEquiv]
      exact hSe i
    have h1 := hy _ hK hKe (Θ.symm s) ⟨s, hs, rfl⟩
    have h2 : Θ.symm s * y = y * Θ.symm s := Subtype.ext h1
    have h3 := congrArg Θ h2
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
  have hzC : z ∈ centralizer ({z} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hzcent : ∀ i, ∀ s ∈ S i, s * Θ ⟨z, hzC⟩ = Θ ⟨z, hzC⟩ * s := by
    intro i s _
    have h2 : Θ.symm s * ⟨z, hzC⟩ = ⟨z, hzC⟩ * Θ.symm s :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Θ.symm s).2)
    have h3 := congrArg Θ h2
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
  refine ⟨fun g hg g' hg' hgc hgc' => ?_, fun g hg hgc hgg => ?_⟩
  · have h := hcomm _ _ (hlift ⟨g, hg⟩ hgc) (hlift ⟨g', hg'⟩ hgc')
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (Θ.injective h)
  · by_cases hg1 : g = 1
    · exact Or.inl hg1
    · refine Or.inr ?_
      have hz1 : z ≠ 1 := fun h1 => by
        rw [h1, orderOf_one] at hz
        exact absurd hz (by norm_num)
      have hzz : z * z = 1 := by
        rw [← sq, ← hz]
        exact pow_orderOf_eq_one z
      have h := hinv (Θ ⟨g, hg⟩) (Θ ⟨z, hzC⟩) (hlift ⟨g, hg⟩ hgc) hzcent
        (by rw [← map_mul, ← map_one Θ]; exact congrArg Θ (Subtype.ext hgg))
        (by rw [← map_mul, ← map_one Θ]; exact congrArg Θ (Subtype.ext hzz))
        (fun h1 => hg1 (congrArg Subtype.val (Θ.injective (h1.trans (map_one Θ).symm))))
        (fun h1 => hz1 (congrArg Subtype.val (Θ.injective (h1.trans (map_one Θ).symm))))
      exact congrArg Subtype.val (Θ.injective h)

variable {τ : Tag} {K : Type} [Field K]

theorem rootChar_piSingle_eq_coord (l : Fin τ.rank → Kˣ) (j : Fin τ.rank) :
    rootChar l (Pi.single j 1) = l j := by
  have h := rootChar_nsmul_single l j 1
  rwa [one_smul, pow_one] at h

theorem rootChar_eq_one_of_commute_pinnedX_one
    {l : Fin τ.rank → Kˣ} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (h : rootDiagUnit τ l * pinnedX τ K β 1 = pinnedX τ K β 1 * rootDiagUnit τ l) :
    rootChar l β = 1 := by
  have h1 := rootDiagUnit_conj_pinnedX l hβ (1 : K)
  rw [h, mul_inv_cancel_right] at h1
  have h2 := pinnedX_injective τ K β h1
  rw [mul_one] at h2
  exact Units.ext h2.symm

theorem eq_one_of_rootDiagUnit_eq_one
    {a : Fin τ.rank → Kˣ} (h : rootDiagUnit τ a = 1) : a = 1 := by
  funext j
  have h1 := rootChar_eq_one_of_commute_pinnedX_one (K := K) (l := a) (isRoot_single τ j)
    (by rw [h, one_mul, mul_one])
  rw [rootChar_piSingle_eq_coord] at h1
  exact h1

theorem rootDiagUnit_eq_of_single
    {i : Fin τ.rank} {l l' : Fin τ.rank → Kˣ} (hl : ∀ j, j ≠ i → l j = 1)
    (hl' : ∀ j, j ≠ i → l' j = 1) (h2 : rootDiagUnit τ l * rootDiagUnit τ l = 1)
    (h2' : rootDiagUnit τ l' * rootDiagUnit τ l' = 1) (h1 : rootDiagUnit τ l ≠ 1)
    (h1' : rootDiagUnit τ l' ≠ 1) : rootDiagUnit τ l = rootDiagUnit τ l' := by
  classical
  have key : ∀ m : Fin τ.rank → Kˣ, (∀ j, j ≠ i → m j = 1) →
      rootDiagUnit τ m * rootDiagUnit τ m = 1 → rootDiagUnit τ m ≠ 1 →
        m = fun j => if j = i then -1 else 1 := by
    intro m hm hm2 hm1
    have hmm : m * m = 1 := eq_one_of_rootDiagUnit_eq_one (by rw [rootDiagUnit_mul]; exact hm2)
    have hmi : (m i : K) * m i = 1 := by
      have h3 := congrArg Units.val (congrFun hmm i)
      simpa using h3
    rcases mul_self_eq_one_iff.1 hmi with h | h
    · refine absurd ?_ hm1
      have hm' : m = 1 := funext fun j => by
        by_cases hj : j = i
        · rw [hj]
          exact Units.ext h
        · exact hm j hj
      rw [hm', rootDiagUnit_one]
    · funext j
      by_cases hj : j = i
      · rw [hj]
        simp only [ite_true]
        exact Units.ext (by rw [h, Units.val_neg, Units.val_one])
      · simp only [hj, ite_false]
        exact hm j hj
  rw [key l hl h2 h1, key l' hl' h2' h1']

theorem toral_rootFactors_centComm
    [Finite K] (hK2 : ringChar K ≠ 2) (hK5 : 5 ≤ Nat.card K)
    {c : Fin τ.rank → Kˣ} (hc : ∀ i, c i = 1 ∨ c i = -1)
    (hW : ∀ w ∈ rootCharStabilizer c, (∀ β ∈ posRoots (rootCharKernel c), w • β = β) → w = 1)
    (g h : toralCentralizer τ K c)
    (hg : ∀ ψ : KernelComponent (maskChar (signTupleBits c)),
      ∀ s ∈ (componentRootSpan K (maskChar (signTupleBits c)) ψ).subgroupOf
        (toralCentralizer τ K c), s * g = g * s)
    (hh : ∀ ψ : KernelComponent (maskChar (signTupleBits c)),
      ∀ s ∈ (componentRootSpan K (maskChar (signTupleBits c)) ψ).subgroupOf
        (toralCentralizer τ K c), s * h = h * s) : g * h = h * g := by
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_of_commute_kernelRoots hK5 hW g.2
    (commute_pinnedX_of_commute_rootFactors hK2 hc hg)
  obtain ⟨l', hl'⟩ := exists_rootDiagUnit_of_commute_kernelRoots hK5 hW h.2
    (commute_pinnedX_of_commute_rootFactors hK2 hc hh)
  apply Subtype.ext
  change (g : ModGL τ K) * h = h * g
  rw [hl, hl', ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

theorem toral_rootFactors_centInv
    [Finite K] (hK2 : ringChar K ≠ 2) (hK5 : 5 ≤ Nat.card K)
    {c : Fin τ.rank → Kˣ} (hc : ∀ i, c i = 1 ∨ c i = -1)
    (hW : ∀ w ∈ rootCharStabilizer c, (∀ β ∈ posRoots (rootCharKernel c), w • β = β) → w = 1)
    {i : Fin τ.rank} (hci : ∀ j, j ≠ i → c j = 1) (g h : toralCentralizer τ K c)
    (hg : ∀ ψ : KernelComponent (maskChar (signTupleBits c)),
      ∀ s ∈ (componentRootSpan K (maskChar (signTupleBits c)) ψ).subgroupOf
        (toralCentralizer τ K c), s * g = g * s)
    (hh : ∀ ψ : KernelComponent (maskChar (signTupleBits c)),
      ∀ s ∈ (componentRootSpan K (maskChar (signTupleBits c)) ψ).subgroupOf
        (toralCentralizer τ K c), s * h = h * s)
    (hg2 : g * g = 1) (hh2 : h * h = 1) (hg1 : g ≠ 1) (hh1 : h ≠ 1) : g = h := by
  have hcg := commute_pinnedX_of_commute_rootFactors hK2 hc hg
  have hch := commute_pinnedX_of_commute_rootFactors hK2 hc hh
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_of_commute_kernelRoots hK5 hW g.2 hcg
  obtain ⟨l', hl'⟩ := exists_rootDiagUnit_of_commute_kernelRoots hK5 hW h.2 hch
  have hcoord : ∀ (m : Fin τ.rank → Kˣ) (x : toralCentralizer τ K c),
      (x : ModGL τ K) = rootDiagUnit τ m →
      (∀ β ∈ rootCharKernel c, ∀ t : K, (x : ModGL τ K) * pinnedX τ K β t = pinnedX τ K β t * x) →
      ∀ j, j ≠ i → m j = 1 := by
    intro m x hx hxc j hj
    have h1 := hxc _ ⟨isRoot_single τ j, by rw [rootChar_piSingle_eq_coord, hci j hj]⟩ 1
    rw [hx] at h1
    have h2 := rootChar_eq_one_of_commute_pinnedX_one (isRoot_single τ j) h1
    rwa [rootChar_piSingle_eq_coord] at h2
  apply Subtype.ext
  rw [hl, hl']
  refine rootDiagUnit_eq_of_single (hcoord l g hl hcg) (hcoord l' h hl' hch) ?_ ?_ ?_ ?_
  · rw [← hl]
    exact congrArg Subtype.val hg2
  · rw [← hl']
    exact congrArg Subtype.val hh2
  · rw [← hl]
    exact fun h1 => hg1 (Subtype.ext h1)
  · rw [← hl']
    exact fun h1 => hh1 (Subtype.ext h1)

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
