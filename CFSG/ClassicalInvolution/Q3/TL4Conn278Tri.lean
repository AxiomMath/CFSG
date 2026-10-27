module

public import CFSG.ClassicalInvolution.Asc77.AscT8T1
import CFSG.ClassicalInvolution.Q3.Q3CLWylA
public import CFSG.ClassicalInvolution.Asc77.AscT3SConfEng
public import CFSG.ClassicalInvolution.Q3.Q3CLStd
public import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8T (TriFrame)
open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc (Std8Core)

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section Rep

variable {W : Subgroup G}

theorem repElt_eq_iff_gen (c : Q3CL.Thompson.Ctx Ω W) (ρ σ : Rep Ω W) :
    T8.repElt ρ = T8.repElt σ ↔ ρ.K = σ.K :=
  ⟨fun h => c.K_eq_of_img_eq ρ σ (congrArg Subtype.val h),
    fun h => Subtype.ext (c.img_eq_of_K_eq ρ σ h)⟩

theorem repElt_commute_iff_gen (c : Q3CL.Thompson.Ctx Ω W) (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K) :
    T8.repElt ρ * T8.repElt σ = T8.repElt σ * T8.repElt ρ ↔ σ.K ∈ omegaNbr Ω ρ.K :=
  ⟨fun h => c.omega_of_comm ρ σ hne (congrArg Subtype.val h),
    fun h => Subtype.ext (c.comm_of_omega ρ σ h)⟩

theorem rep_le_centralizer_gen (c : Q3CL.Thompson.Ctx Ω W) (ρ σ : Rep Ω W)
    (hσ : σ.K = ρ.K ∨ σ.K ∈ omegaNbr Ω ρ.K) {v : G} (hv : IsUniqueInvolution σ.K v) :
    ρ.R ≤ Subgroup.centralizer ({v} : Set G) :=
  Q3CL.Wyl.rep_le_centralizer c ρ σ hσ hv

end Rep

section Third

variable {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_third_of_abelian_gen (hs : Std8Core Ω K J S R T W z t) (hE4 : ¬ MuIsoE4 Ω W)
    (hab : ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) :
    ∃ τ : Rep Ω W, τ.K ≠ K ∧ τ.K ≠ J := by
  have hP := Q3CL.T8R.Loc.partIHyp_of_std8 hs
  have hc := Q3CL.T8.ctxOf hP hs.hW.1
  by_contra hcon
  push Not at hcon
  set a := T8.repElt (Q3CL.T8R.Loc.stdRepK hs) with ha
  set b := T8.repElt (Q3CL.T8R.Loc.stdRepJ hs) with hb
  have hall : ∀ d ∈ muDelta Ω W, d = a ∨ d = b := by
    intro d hd
    obtain ⟨τ, rfl⟩ := T8.exists_rep_of_mem_muDelta hd
    by_cases h1 : τ.K = K
    · left
      exact (repElt_eq_iff_gen hc τ (Q3CL.T8R.Loc.stdRepK hs)).mpr h1
    · right
      exact (repElt_eq_iff_gen hc τ (Q3CL.T8R.Loc.stdRepJ hs)).mpr (hcon τ h1)
  have haΔ : a ∈ muDelta Ω W := T8.repElt_mem _
  have hbΔ : b ∈ muDelta Ω W := T8.repElt_mem _
  have hne : a ≠ b := fun h =>
    hs.hJ.2.1 ((repElt_eq_iff_gen hc (Q3CL.T8R.Loc.stdRepK hs)
      (Q3CL.T8R.Loc.stdRepJ hs)).mp h).symm
  apply hE4
  refine MuTab.nonempty_mulEquiv_klein (Q3T8.Asc77.Thompson.muDelta_mul_self hP.hyp hs.hW.1 haΔ)
    (Q3T8.Asc77.Thompson.muDelta_mul_self hP.hyp hs.hW.1 hbΔ)
    (Subtype.ext (hab _ a.2 _ b.2)) (muDelta_ne_one hs.hW.1 haΔ) (muDelta_ne_one hs.hW.1 hbΔ) hne
    ?_
  rw [eq_top_iff, ← closure_muDelta_eq_top Ω W]
  refine (Subgroup.closure_le _).mpr fun d hd => ?_
  rcases hall d hd with h | h
  · rw [h]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · rw [h]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

end Third

section Frame

theorem triFrame_comm_gen {M : Fin 3 → Subgroup G} {x : Fin 3 → G} {R : Fin 3 → Subgroup G}
    (hF : TriFrame Ω M x R) (hΩ : HypOmegaGen Ω) (i j : Fin 3) : x i * x j = x j * x i := by
  by_cases hij : i = j
  · rw [hij]
  · exact Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ (hF.inv i) (hF.nbr i j hij) (hF.inv j)

variable {K J K' : Subgroup G} {z t z' : G}

theorem not_mem_closure_pair_of_triangle (hΩ : HypOmegaGen Ω)
    (hnt : ∀ L ∈ Ω, ∀ L' ∈ twinSet Ω L, L' = L) (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (hz' : IsUniqueInvolution K' z') (hJ : J ∈ omegaNbr Ω K)
    (hK'K : K' ∈ omegaNbr Ω K) (hK'J : K' ∈ omegaNbr Ω J) (hne : z' ≠ z * t) :
    z' ∉ Subgroup.closure ({z, t} : Set G) := by
  intro hmem
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hJ ht
  have hJΩ : J ∈ Ω := hJ.1
  rcases T3CII.closure_pair_cases hz.sq ht.sq hzt hmem with h | h | h | h
  · exact hz'.ne_one h
  · subst h
    exact hK'K.2.1 (hnt K hK K' ⟨hK'K.1, z', hz, hz'⟩)
  · subst h
    exact hK'J.2.1 (hnt J hJΩ K' ⟨hK'J.1, z', ht, hz'⟩)
  · exact hne h

theorem isElemAbelian_closure_triangle (hΩ : HypOmegaGen Ω) (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (hz' : IsUniqueInvolution K' z') (hJ : J ∈ omegaNbr Ω K)
    (hK'K : K' ∈ omegaNbr Ω K) (hK'J : K' ∈ omegaNbr Ω J) :
    IsElemAbelian 2 (Subgroup.closure ({z, t, z'} : Set G)) :=
  T8T.isElemAbelian_closure_three hz.sq ht.sq hz'.sq
    (Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hJ ht)
    (Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hK'K hz')
    (Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hK'J hz')

theorem natCard_closure_triangle (hΩ : HypOmegaGen Ω)
    (hnt : ∀ L ∈ Ω, ∀ L' ∈ twinSet Ω L, L' = L) (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (hz' : IsUniqueInvolution K' z') (hJ : J ∈ omegaNbr Ω K)
    (hK'K : K' ∈ omegaNbr Ω K) (hK'J : K' ∈ omegaNbr Ω J) (hne : z' ≠ z * t) :
    Nat.card ↥(Subgroup.closure ({z, t, z'} : Set G)) = 8 := by
  have hzt : z ≠ t := fun h => by
    subst h
    exact hJ.2.1 (hnt K hK J ⟨hJ.1, z, hz, ht⟩)
  exact T8T.natCard_closure_three hz.sq ht.sq hz'.sq
    (Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hJ ht)
    (Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hK'K hz')
    (Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hK'J hz') hz.ne_one ht.ne_one hzt hz'.ne_one
    (not_mem_closure_pair_of_triangle hΩ hnt hK hz ht hz' hJ hK'K hK'J hne)

omit [Finite G] in
theorem closure_pair_le_closure_triangle :
    Subgroup.closure ({z, t} : Set G) ≤ Subgroup.closure ({z, t, z'} : Set G) :=
  Subgroup.closure_mono (by
    intro w hw
    rcases hw with rfl | rfl
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _))

end Frame

section Extract

variable {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_triFrame_of_abelian (hs : Std8Core Ω K J S R T W z t) (hE4 : ¬ MuIsoE4 Ω W)
    (hab : ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) :
    ∃ (K' R' : Subgroup G) (z' : G), TriFrame Ω ![K, J, K'] ![z, t, z'] ![R, T, R'] := by
  have hP := Q3CL.T8R.Loc.partIHyp_of_std8 hs
  have hc := Q3CL.T8.ctxOf hP hs.hW.1
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  obtain ⟨τ, hτK, hτJ⟩ := exists_third_of_abelian_gen hs hE4 hab
  obtain ⟨z₂, hz₂⟩ := hΩ.exists_uniqueInvolution τ.hK
  let ρ : Fin 3 → Rep Ω W := ![Q3CL.T8R.Loc.stdRepK hs, Q3CL.T8R.Loc.stdRepJ hs, τ]
  let zz : Fin 3 → G := ![z, t, z₂]
  have hzz : ∀ i, IsUniqueInvolution (ρ i).K (zz i) := by
    intro i
    fin_cases i
    · exact hs.hz
    · exact hs.ht
    · exact hz₂
  have hne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hs.hJ.2.1.symm
    · exact hτK.symm
    · exact hs.hJ.2.1
    · exact absurd rfl hij
    · exact hτJ.symm
    · exact hτK
    · exact hτJ
    · exact absurd rfl hij
  have hnbr : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K := by
    intro i j hij
    refine (repElt_commute_iff_gen hc (ρ i) (ρ j) (hne i j hij)).mp ?_
    exact Subtype.ext (hab _ (T8.repElt (ρ i)).2 _ (T8.repElt (ρ j)).2)
  have hrel : ∀ i j, (ρ j).K = (ρ i).K ∨ (ρ j).K ∈ omegaNbr Ω (ρ i).K := by
    intro i j
    by_cases h : i = j
    · subst h
      exact Or.inl rfl
    · exact Or.inr (hnbr i j h)
  have hKE : ∀ i, (ρ i).K = ![K, J, τ.K] i := by
    intro i
    fin_cases i <;> rfl
  have hRE : ∀ i, (ρ i).R = ![R, T, τ.R] i := by
    intro i
    fin_cases i <;> rfl
  have hzE : ∀ i, zz i = ![z, t, z₂] i := by
    intro i
    fin_cases i <;> rfl
  exact ⟨τ.K, τ.R, z₂,
    { mem := fun i => by
        rw [← hKE i]
        exact (ρ i).hK
      inv := fun i => by
        rw [← hKE i, ← hzE i]
        exact hzz i
      nbr := fun i j hij => by
        rw [← hKE i, ← hKE j]
        exact hnbr i j hij
      syl := fun i => by
        rw [← hKE i, ← hRE i]
        exact (ρ i).hRK
      cent := fun i j => by
        rw [← hRE i, ← hzE j]
        exact rep_le_centralizer_gen hc (ρ i) (ρ j) (hrel i j) (hzz j) }⟩

theorem exists_triFrame_of_std8Core (hs : Std8Core Ω K J S R T W z t) (hE4 : ¬ MuIsoE4 Ω W)
    (hab : ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x)
    (hE8 : ∀ K' ∈ omegaNbr Ω K, K' ∈ omegaNbr Ω J → ∀ z' : G, IsUniqueInvolution K' z' →
      z' ≠ z * t) :
    ∃ (K' R' : Subgroup G) (z' : G), TriFrame Ω ![K, J, K'] ![z, t, z'] ![R, T, R'] ∧
      z' ∉ Subgroup.closure ({z, t} : Set G) := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  obtain ⟨K', R', z₂, hF⟩ := exists_triFrame_of_abelian hs hE4 hab
  have h02 : K' ∈ omegaNbr Ω K := hF.nbr 0 2 (by decide)
  have h12 : K' ∈ omegaNbr Ω J := hF.nbr 1 2 (by decide)
  have hz₂ : IsUniqueInvolution K' z₂ := hF.inv 2
  exact ⟨K', R', z₂, hF, not_mem_closure_pair_of_triangle hΩ hnt hs.stand.mem hs.hz hs.ht hz₂
    hs.hJ h02 h12 (hE8 K' h02 h12 z₂ hz₂)⟩

end Extract

end CFSG.ClassicalInvolution.Q3.TL4
