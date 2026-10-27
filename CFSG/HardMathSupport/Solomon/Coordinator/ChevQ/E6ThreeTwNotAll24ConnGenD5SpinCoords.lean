module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
public import CFSG.HardMathSupport.Lang.TwE6Step3.TwoA2Split
public import CFSG.LieType.Chevalley.CorootCoordinates

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Tables
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Lang.TwE6Step3

set_option linter.unusedSectionVars false


section Prod

theorem prod_zpow_prod_comm {ι κ : Type*} {L : Type} [Field L] (s : Finset ι) (t : Finset κ)
    (a : ι → Lˣ) (M : ι → κ → ℤ) (γ : κ → ℤ) :
    ∏ k ∈ t, (∏ i ∈ s, a i ^ M i k) ^ γ k = ∏ i ∈ s, a i ^ ∑ k ∈ t, M i k * γ k := by
  calc ∏ k ∈ t, (∏ i ∈ s, a i ^ M i k) ^ γ k
      = ∏ k ∈ t, ∏ i ∈ s, (a i ^ M i k) ^ γ k :=
        Finset.prod_congr rfl fun k _ => (Finset.prod_zpow _ _ _).symm
    _ = ∏ i ∈ s, ∏ k ∈ t, (a i ^ M i k) ^ γ k := Finset.prod_comm
    _ = ∏ i ∈ s, a i ^ ∑ k ∈ t, M i k * γ k := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← prod_zpow_eq_zpow_sum]
        exact Finset.prod_congr rfl fun k _ => (zpow_mul _ _ _).symm

end Prod

section Torus

variable {L : Type} [Field L]

theorem supportedTorusHom_eq_rootDiagUnit (J : Set (Fin Tag.E6.rank)) [Fintype J] (a : J → Lˣ) :
    supportedTorusHom Tag.E6 L J a =
      rootDiagUnit Tag.E6 (fun l => ∏ j : J, a j ^ Tag.E6.cartan j l) := by
  have hmem : supportedTorusHom Tag.E6 L J a ∈ torusGroup Tag.E6 L :=
    supportedTorus_le_torusGroup J (supportedTorusHom_mem J a)
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hmem
  have hbl : b = fun l => ∏ j : J, a j ^ Tag.E6.cartan j l := by
    funext l
    have h1 := torusRootChar_supportedTorusHom J a (isRoot_single Tag.E6 l)
    rw [hb, torusRootChar_rootDiagUnit' b (isRoot_single Tag.E6 l)] at h1
    have hs : ∀ j : J, ∑ k, Tag.E6.cartan j k * (Pi.single l 1 : Fin Tag.E6.rank → ℤ) k =
        Tag.E6.cartan j l := fun j => by
      rw [Finset.sum_eq_single l (fun k _ hk => by rw [Pi.single_eq_of_ne hk, mul_zero])
        (fun h => absurd (Finset.mem_univ l) h), Pi.single_eq_same, mul_one]
    simp only [hs] at h1
    rw [← T1b.rootChar_single b l]
    exact Units.ext h1
  rw [hb, hbl]

theorem rootChar_prodCoroot (Δ : Finset (Fin Tag.E6.rank → ℤ))
    (hΔ : ∀ β ∈ Δ, IsRoot Tag.E6 β) (c : (Fin Tag.E6.rank → ℤ) → Lˣ)
    (γ : Fin Tag.E6.rank → ℤ) :
    rootChar (fun i => ∏ β ∈ Δ, c β ^ corootPair β (Pi.single i 1)) γ =
      ∏ β ∈ Δ, c β ^ corootPair β γ := by
  unfold rootChar
  rw [prod_zpow_prod_comm Δ Finset.univ c (fun β i => corootPair β (Pi.single i 1)) γ]
  refine Finset.prod_congr rfl fun β hβ => ?_
  rw [corootPair_eq_sum (hΔ β hβ) γ]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem weylAct_nativeTuple (w : WeylGroup Tag.E6) (Jf : Finset (Fin Tag.E6.rank))
    (a : Fin Tag.E6.rank → Lˣ) (l : Fin Tag.E6.rank) :
    T1b.weylAct w (fun m => ∏ j ∈ Jf, a j ^ Tag.E6.cartan j m) l =
      ∏ j ∈ Jf, a j ^ corootPair (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) (Pi.single l 1) := by
  unfold T1b.weylAct rootChar
  rw [prod_zpow_prod_comm Jf Finset.univ a (fun j m => Tag.E6.cartan j m) (w⁻¹ • Pi.single l 1)]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [corootPair_smul_single]

theorem smul_single_injective (w : WeylGroup Tag.E6) :
    Function.Injective fun j : Fin Tag.E6.rank => w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
  intro j j' h
  have h1 : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single j' 1 := smul_left_cancel w h
  have h2 := congrFun h1 j
  by_contra hne
  rw [Pi.single_eq_same, Pi.single_eq_of_ne' (Ne.symm hne)] at h2
  exact one_ne_zero h2

theorem isRoot_of_mem_image (w : WeylGroup Tag.E6) (Jf : Finset (Fin Tag.E6.rank))
    {β : Fin Tag.E6.rank → ℤ}
    (hβ : β ∈ Jf.image fun j => w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) :
    IsRoot Tag.E6 β := by
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hβ
  exact IsRoot.smul (isRoot_single Tag.E6 j) w

theorem torus_coords_of_conj (w : WeylGroup Tag.E6) (Jf : Finset (Fin Tag.E6.rank))
    {t : ModGL Tag.E6 L}
    (ht : t ∈ torusGroup Tag.E6 L ⊓
      rootSpan Tag.E6 L ((fun α => w • α) '' parabolicRoots Tag.E6 (↑Jf : Set (Fin Tag.E6.rank)))) :
    ∃ c : (Fin Tag.E6.rank → ℤ) → Lˣ, t = rootDiagUnit Tag.E6 (fun i =>
      ∏ β ∈ Jf.image (fun j => w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)),
        c β ^ corootPair β (Pi.single i 1)) := by
  classical
  obtain ⟨htH, htQ⟩ := Subgroup.mem_inf.1 ht
  have hg' : (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ * t *
      canonicalRep (coxeterSystem Tag.E6) L w ∈ supportedTorus Tag.E6 L (↑Jf : Set _) := by
    rw [← torusGroup_inf_rootSpan_parabolicRoots]
    refine Subgroup.mem_inf.2 ⟨canonicalRep_inv_conj_mem_torusGroup w htH, ?_⟩
    refine canonicalRep_inv_conj_mem_rootSpan w (fun γ hγ => ?_) htQ
    obtain ⟨α, hα, rfl⟩ := hγ
    exact ⟨IsRoot.smul hα.1 w, by rwa [inv_smul_smul]⟩
  obtain ⟨a, ha⟩ := mem_supportedTorus.1 hg'
  rw [supportedTorusHom_eq_rootDiagUnit] at ha
  set n := canonicalRep (coxeterSystem Tag.E6) L w with hn
  let a' : Fin Tag.E6.rank → Lˣ := fun j => if h : j ∈ Jf then a ⟨j, by simpa using h⟩ else 1
  have hA : ∀ m, (∏ j : (↑Jf : Set (Fin Tag.E6.rank)), a j ^ Tag.E6.cartan j m) =
      ∏ j ∈ Jf, a' j ^ Tag.E6.cartan j m := by
    intro m
    rw [Finset.prod_subtype Jf (p := fun x => x ∈ (↑Jf : Set (Fin Tag.E6.rank)))
      (fun x => Iff.rfl) (fun j => a' j ^ Tag.E6.cartan j m)]
    exact Finset.prod_congr rfl fun j _ => by simp [a', j.2]
  have ht' : t = n * (n⁻¹ * t * n) * n⁻¹ := by group
  refine ⟨fun β => a' (Function.invFun
    (fun j : Fin Tag.E6.rank => w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) β), ?_⟩
  rw [ht', ← ha, T1b.canonicalRep_conj_rootDiagUnit]
  congr 1
  funext l
  rw [show (fun m => ∏ j : (↑Jf : Set (Fin Tag.E6.rank)), a j ^ Tag.E6.cartan j m) =
    fun m => ∏ j ∈ Jf, a' j ^ Tag.E6.cartan j m from funext hA, weylAct_nativeTuple,
    Finset.prod_image (fun j _ j' _ h => smul_single_injective w h)]
  refine Finset.prod_congr rfl fun j _ => ?_
  beta_reduce
  rw [Function.leftInverse_invFun (smul_single_injective w) j]

theorem coords_unique_of_conj (w : WeylGroup Tag.E6) (Jf : Finset (Fin Tag.E6.rank))
    (hν : ∀ j₀ ∈ Jf, ∃ ν : Fin Tag.E6.rank → ℤ, ∀ j ∈ Jf,
      ∑ k, Tag.E6.cartan j k * ν k = if j = j₀ then 1 else 0)
    {c c' : (Fin Tag.E6.rank → ℤ) → Lˣ}
    (h : rootDiagUnit Tag.E6 (fun i : Fin Tag.E6.rank =>
        ∏ β ∈ Jf.image (fun j => w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)),
          c β ^ corootPair β (Pi.single i 1)) =
      (rootDiagUnit Tag.E6 (fun i : Fin Tag.E6.rank =>
        ∏ β ∈ Jf.image (fun j => w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)),
          c' β ^ corootPair β (Pi.single i 1)) : ModGL Tag.E6 L))
    {β : Fin Tag.E6.rank → ℤ}
    (hβ : β ∈ Jf.image fun j => w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) :
    c β = c' β := by
  classical
  have htuple := CFSG.LieType.Chevalley.rootDiagUnit_injective h
  obtain ⟨j₀, hj₀, rfl⟩ := Finset.mem_image.1 hβ
  obtain ⟨ν, hν'⟩ := hν j₀ hj₀
  have h1 := congrArg (fun b => rootChar b (w • ν)) htuple
  rw [rootChar_prodCoroot _ (fun _ hβ => isRoot_of_mem_image w Jf hβ),
    rootChar_prodCoroot _ (fun _ hβ => isRoot_of_mem_image w Jf hβ),
    Finset.prod_image (fun j _ j' _ h => smul_single_injective w h),
    Finset.prod_image (fun j _ j' _ h => smul_single_injective w h)] at h1
  have hcp : ∀ j ∈ Jf, corootPair (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) (w • ν) =
      if j = j₀ then 1 else 0 := by
    intro j hj
    rw [corootPair_smul_single, inv_smul_smul]
    exact hν' j hj
  have hsingle : ∀ f : (Fin Tag.E6.rank → ℤ) → Lˣ,
      ∏ j ∈ Jf, f (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) ^
        corootPair (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) (w • ν) =
        f (w • (Pi.single j₀ 1 : Fin Tag.E6.rank → ℤ)) := by
    intro f
    rw [Finset.prod_eq_single j₀ (fun j hj hne => by rw [hcp j hj, if_neg hne, zpow_zero])
      (fun h => absurd hj₀ h), hcp j₀ hj₀, if_pos rfl, zpow_one]
  rw [hsingle c, hsingle c'] at h1
  exact h1

end Torus

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
