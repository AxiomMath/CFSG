module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentFrame
public import CFSG.LieType.SeitzGeneration.OrthRelRoot
import CFSG.LieType.SeitzGeneration.OrthEvenSingular
import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOnePlanes
import CFSG.RankThree.PartOne.K159.RowFourType
import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityTransvection
public import CFSG.LieType.SeitzGeneration.OrthHyperRoot
public import CFSG.RankThree.PartOne.KC.LinearPlaneBlocks

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173U

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.OrthBlk
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {k : ℕ} {U : Fin k → Submodule F V}

@[expose] def IsFlip (Q : QuadraticForm F V) (U : Fin k → Submodule F V) (d d' : V ≃ₗ[F] V)
    (J : Finset (Fin k)) : Prop :=
  d' ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ (∀ x ∈ polarPerp Q (⨆ j, U j), d' x = x) ∧
    ∀ j, ∀ x ∈ U j, d' x = if j ∈ J then d⁻¹ x else d x

@[expose] def IsEvenFlip (Q : QuadraticForm F V) (U : Fin k → Submodule F V) (d d' : V ≃ₗ[F] V) : Prop :=
  ∃ J : Finset (Fin k), Even J.card ∧ IsFlip Q U d d' J

theorem isFlip_self {d : V ≃ₗ[F] V} (hd : d ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hfix : ∀ x ∈ polarPerp Q (⨆ j, U j), d x = x) : IsFlip Q U d d ∅ :=
  ⟨hd, hfix, fun j x _ => by simp⟩

private theorem exists_isFlip_of_maps_aux1 {W : Submodule F V}
    (h : (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate) : PolarNondegOn Q W := by
  intro x hx hperp
  have h' := h.1 ⟨x, hx⟩ (fun y => by
    simpa [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype_cent] using hperp y y.2)
  exact congrArg Subtype.val h'

private theorem exists_isFlip_of_maps_aux2 (hU : IsPlaneSystem Q U) {d : V ≃ₗ[F] V}
    (hmaps : ∀ j, ∀ x ∈ U j, d x ∈ U j) (j : Fin k) {s : V} (hs : s ∈ U j) :
    d.symm s ∈ U j := by
  let φ : (U j) →ₗ[F] (U j) :=
    { toFun := fun x => ⟨d x, hmaps j x x.2⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun c x => Subtype.ext (by simp) }
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have h : d x.1 = d y.1 := congrArg Subtype.val hxy
    exact Subtype.ext (by simpa using congrArg d.symm h)
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective (f := φ)).1 hφinj ⟨s, hs⟩
  have hdy : d y.1 = s := congrArg Subtype.val hy
  have : d.symm s = y.1 := by rw [← hdy, LinearEquiv.symm_apply_apply]
  rw [this]; exact y.2

private theorem exists_isFlip_of_maps_aux3 (hU : IsPlaneSystem Q U) {i j : Fin k} (hij : i ≠ j)
    {g h : V ≃ₗ[F] V} (hgp : ∀ x ∈ perp Q (U i), g x = x) (hhp : ∀ x ∈ perp Q (U j), h x = x)
    (hgi : ∀ x ∈ U i, g x ∈ U i) (hhj : ∀ x ∈ U j, h x ∈ U j) : g * h = h * g := by
  have hP : PolarNondegOn Q (U i ⊔ U j) := by
    have h := hU.nondeg_biSup ({i, j} : Finset (Fin k))
    rw [show (⨆ x ∈ ({i, j} : Finset (Fin k)), U x) = U i ⊔ U j by
      rw [Finset.iSup_insert, Finset.iSup_singleton]] at h
    exact exists_isFlip_of_maps_aux1 h
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.1
    ((isCompl_perp hP).sup_eq_top ▸ Submodule.mem_top (x := x))
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hp
  have hri : r ∈ perp Q (U i) := mem_perp.2 fun y hy => mem_perp.1 hr y (Submodule.mem_sup_left hy)
  have hrj : r ∈ perp Q (U j) := mem_perp.2 fun y hy => mem_perp.1 hr y (Submodule.mem_sup_right hy)
  have hui : u ∈ perp Q (U j) := mem_perp.2 fun y hy => hU.perp j i (Ne.symm hij) y hy u hu
  have hvj : v ∈ perp Q (U i) := mem_perp.2 fun y hy => hU.perp i j hij y hy v hv
  have hgu : h (g u) = g u :=
    hhp (g u) (mem_perp.2 fun y hy => hU.perp j i (Ne.symm hij) y hy (g u) (hgi u hu))
  have hhv : g (h v) = h v :=
    hgp (h v) (mem_perp.2 fun y hy => hU.perp i j hij y hy (h v) (hhj v hv))
  simp only [LinearEquiv.mul_apply, map_add, hhp u hui, hgp v hvj, hgu, hhv, hgp r hri, hhp r hrj]

private theorem exists_isFlip_of_maps_aux4 {d : V ≃ₗ[F] V}
    (hS : ∀ j, PolarNondegOn Q (U j)) (hmaps : ∀ j, ∀ x ∈ U j, d x ∈ U j)
    (h2 : ∀ j, ∀ s ∈ U j, d.symm s ∈ U j) (hd : d ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (j : Fin k) : extendId (hS j) d (hmaps j) (h2 j) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  obtain ⟨u, hu, r, hr, rfl⟩ := Submodule.mem_sup.1
    ((isCompl_perp (hS j)).sup_eq_top ▸ Submodule.mem_top (x := v))
  rw [show extendId (hS j) d (hmaps j) (h2 j) (u + r) = d u + r by
      simpa using extendId_apply (hS j) (hmaps j) (h2 j) hu hr,
    QuadraticMap.map_add Q (d u) r, QuadraticMap.map_add Q u r,
    mem_perp.1 hr (d u) (hmaps j u hu), mem_perp.1 hr u hu,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hd u]

private theorem exists_isFlip_of_maps_aux5 {σ : Fin k → V ≃ₗ[F] V}
    (comm : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).Pairwise (Function.onFun Commute σ))
    (hσfix : ∀ i j, i ≠ j → σ i ∈ stabPW (U j))
    (hσU : ∀ j, ∀ x ∈ U j, σ j x ∈ U j) (j : Fin k) {x : V} (hx : x ∈ U j) :
    (Finset.univ.noncommProd σ comm) x = σ j x := by
  have hcomm' : ((Finset.univ.erase j : Finset (Fin k)) : Set (Fin k)).Pairwise
      (Function.onFun Commute σ) :=
    fun _ hx _ hy hxy => comm (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy) hxy
  rw [← Finset.noncommProd_erase_mul Finset.univ (Finset.mem_univ j) σ comm hcomm', LinearEquiv.mul_apply]
  have herase : ∀ y ∈ U j, (Finset.univ.erase j).noncommProd σ hcomm' y = y := by
    intro y hy
    refine Finset.noncommProd_induction (Finset.univ.erase j) σ hcomm' (fun g => g y = y)
      (fun a b ha hb => by rw [LinearEquiv.mul_apply, hb, ha]) rfl (fun i hi => ?_)
    exact mem_stabPW.1 (hσfix i j (Finset.mem_erase.mp hi).1) y hy
  exact herase (σ j x) (hσU j x hx)

private theorem exists_isFlip_of_maps_aux6 (hU : IsPlaneSystem Q U) (J : Finset (Fin k))
    {d : V ≃ₗ[F] V} {t : Fin k → V ≃ₗ[F] V}
    (htO : ∀ j, t j ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (htU : ∀ j, ∀ x ∈ U j, t j x = d x)
    (htfix : ∀ j, ∀ x ∈ perp Q (U j), t j x = x)
    (hmaps : ∀ j, ∀ x ∈ U j, d x ∈ U j) (h2 : ∀ j, ∀ x ∈ U j, d.symm x ∈ U j) :
    ∃ σ : Fin k → V ≃ₗ[F] V,
      (∀ j, σ j = if j ∈ J then (t j)⁻¹ else t j) ∧
      (∀ j, σ j ∈ TauCeti.QuadraticMap.orthogonalGroup Q) ∧
      (∀ j, ∀ x ∈ U j, σ j x ∈ U j) ∧
      (∀ i j, i ≠ j → σ i ∈ stabPW (U j)) ∧
      (∀ j, ∀ x ∈ U j, σ j x = if j ∈ J then d⁻¹ x else d x) := by
  have htinvU : ∀ j, ∀ x ∈ U j, (t j)⁻¹ x = d.symm x := fun j x hx => by
    have hdx := h2 j x hx
    have h1 : t j (d.symm x) = x := by rw [htU j _ hdx, LinearEquiv.apply_symm_apply]
    calc (t j)⁻¹ x = (t j)⁻¹ (t j (d.symm x)) := by rw [h1]
      _ = d.symm x := LinearEquiv.symm_apply_apply (t j) _
  let σ : Fin k → V ≃ₗ[F] V := fun j => if j ∈ J then (t j)⁻¹ else t j
  have hσdef : ∀ j, σ j = if j ∈ J then (t j)⁻¹ else t j := fun j => rfl
  refine ⟨σ, hσdef, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [hσdef j]
    by_cases hj : j ∈ J
    · rw [if_pos hj]; exact Subgroup.inv_mem _ (htO j)
    · rw [if_neg hj]; exact htO j
  · intro j x hx
    rw [hσdef j]
    by_cases hj : j ∈ J
    · rw [if_pos hj, htinvU j x hx]; exact h2 j x hx
    · rw [if_neg hj, htU j x hx]; exact hmaps j x hx
  · intro i j hij
    refine mem_stabPW.2 fun x hx => ?_
    have hxi : x ∈ perp Q (U i) := mem_perp.2 fun y hy => hU.perp i j hij y hy x hx
    have hti := htfix i x hxi
    rw [hσdef i]
    by_cases hi : i ∈ J
    · rw [if_pos hi]
      calc (t i)⁻¹ x = (t i)⁻¹ (t i x) := by rw [hti]
        _ = x := LinearEquiv.symm_apply_apply (t i) x
    · rw [if_neg hi]; exact hti
  · intro j x hx
    rw [hσdef j]
    split_ifs with hj
    · rw [htinvU j x hx]; rfl
    · rw [htU j x hx]

private theorem exists_isFlip_of_maps_aux7 (J : Finset (Fin k)) {t σ : Fin k → V ≃ₗ[F] V}
    (hσdef : ∀ j, σ j = if j ∈ J then (t j)⁻¹ else t j)
    (hcommt : ∀ i j, i ≠ j → Commute (t i) (t j)) :
    ∀ i j, i ≠ j → Commute (σ i) (σ j) := by
  intro i j hij
  have ht := hcommt i j hij
  rw [hσdef i, hσdef j]
  by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
  · rw [if_pos hi, if_pos hj]; exact ht.inv_left.inv_right
  · rw [if_pos hi, if_neg hj]; exact ht.inv_left
  · rw [if_neg hi, if_pos hj]; exact ht.inv_right
  · rw [if_neg hi, if_neg hj]; exact ht

theorem exists_isFlip_of_maps (hU : IsPlaneSystem Q U) {d : V ≃ₗ[F] V}
    (hd : d ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hmaps : ∀ j, ∀ x ∈ U j, d x ∈ U j)
    (J : Finset (Fin k)) : ∃ d' : V ≃ₗ[F] V, IsFlip Q U d d' J := by
  classical
  have hS : ∀ j, PolarNondegOn Q (U j) := fun j => exists_isFlip_of_maps_aux1 (hU.nondeg j)
  have h2 : ∀ j, ∀ s ∈ U j, d.symm s ∈ U j := fun j s hs => exists_isFlip_of_maps_aux2 hU hmaps j hs
  let t : Fin k → V ≃ₗ[F] V := fun j => extendId (hS j) d (hmaps j) (h2 j)
  have htU : ∀ j, ∀ x ∈ U j, t j x = d x := fun j x hx => by
    simpa using extendId_apply (hS j) (hmaps j) (h2 j) hx (zero_mem (perp Q (U j)))
  have htfix : ∀ j, ∀ x ∈ perp Q (U j), t j x = x := fun j x hx => by
    simpa using extendId_apply (hS j) (hmaps j) (h2 j) (zero_mem (U j)) hx
  have htO : ∀ j, t j ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun j => by
    simpa only [t] using exists_isFlip_of_maps_aux4 hS hmaps h2 hd j
  have hcommt : ∀ i j, i ≠ j → Commute (t i) (t j) := fun i j hij =>
    exists_isFlip_of_maps_aux3 hU hij (htfix i) (htfix j)
      (fun x hx => by rw [htU i x hx]; exact hmaps i x hx)
      (fun x hx => by rw [htU j x hx]; exact hmaps j x hx)
  obtain ⟨σ, hσdef, hσO, hσU, hσfix, hσval⟩ :=
    exists_isFlip_of_maps_aux6 hU J htO htU htfix hmaps h2
  have hcommσ := exists_isFlip_of_maps_aux7 J hσdef hcommt
  have hcomm : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).Pairwise (Function.onFun Commute σ) := by
    rw [Finset.coe_univ]; exact Set.pairwise_univ.2 fun i j hij => hcommσ i j hij
  refine ⟨Finset.univ.noncommProd σ hcomm, ?_, ?_, ?_⟩
  · exact Finset.noncommProd_induction Finset.univ σ hcomm
      (fun g => g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
      (fun a b ha hb => Subgroup.mul_mem _ ha hb) (Subgroup.one_mem _) (fun i _ => hσO i)
  · intro x hx
    refine Finset.noncommProd_induction Finset.univ σ hcomm (fun g => g x = x)
      (fun a b ha hb => by rw [LinearEquiv.mul_apply, hb, ha]) rfl (fun i _ => ?_)
    have hxi : x ∈ perp Q (U i) := mem_perp.2 fun y hy => mem_polarPerp_iff.1 hx y (le_iSup U i hy)
    rw [hσdef i]
    by_cases hi : i ∈ J
    · rw [if_pos hi]
      calc (t i)⁻¹ x = (t i)⁻¹ (t i x) := by rw [htfix i x hxi]
        _ = x := LinearEquiv.symm_apply_apply (t i) x
    · rw [if_neg hi]; exact htfix i x hxi
  · intro j x hx
    rw [exists_isFlip_of_maps_aux5 hcomm hσfix hσU j hx, hσval j x hx]

theorem polarNondegOn_iSup_of_isPlaneSystem (hU : IsPlaneSystem Q U) : PolarNondegOn Q (⨆ j, U j) := by
  have h := hU.nondeg_biSup Finset.univ
  have e : (⨆ j ∈ (Finset.univ : Finset (Fin k)), U j) = ⨆ j, U j := by simp
  rw [e] at h
  intro x hx hperp
  have := h.1 ⟨x, hx⟩ (fun y => by
    simpa [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype_cent] using hperp y y.2)
  exact congrArg Subtype.val this

private theorem exists_hypPair_sum_of_ne_aux2 (hU : IsPlaneSystem Q U) (j : Fin k) {x : V}
    (hx : x ∈ U j) (hQx : Q x = 0) : x = 0 := by
  by_contra hx0
  refine hU.not_isPlusType j ⟨Submodule.span F {(⟨x, hx⟩ : U j)}, ?_, ?_⟩
  · rw [finrank_span_singleton (v := (⟨x, hx⟩ : U j)) (by simpa using hx0), hU.finrank_eq j]
  · intro y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    simp [QuadraticMap.comp_apply, QuadraticMap.map_smul, hQx]

private theorem exists_hypPair_sum_of_ne_aux3 (hU : IsPlaneSystem Q U) {a b : Fin k} (hab : a ≠ b)
    {s y z : V} (hs0 : s ≠ 0) (hy : y ∈ U a) (hz : z ∈ U b) (hyz : y + z = s)
    (hQyz : Q y = Q z) (hQy : Q y = 0) : False := by
  have hz0 : Q z = 0 := by rw [← hQyz]; exact hQy
  by_cases hy0 : y = 0
  · have hzne : z ≠ 0 := by
      intro hz0'; exact hs0 (by rw [← hyz, hy0, hz0', add_zero])
    exact hzne (exists_hypPair_sum_of_ne_aux2 hU b hz hz0)
  · exact hy0 (exists_hypPair_sum_of_ne_aux2 hU a hy hQy)

theorem exists_hypPair_sum_of_ne (hU : IsPlaneSystem Q U) {a b : Fin k} (hab : a ≠ b) :
    ∃ y₁ z₁ y₂ z₂ : V, y₁ ∈ U a ∧ z₁ ∈ U b ∧ y₂ ∈ U a ∧ z₂ ∈ U b ∧ Q y₁ ≠ 0 ∧ Q y₂ ≠ 0 ∧
      Q y₁ = Q z₁ ∧ Q y₂ = Q z₂ ∧ polar Q (y₁ + z₁) (y₂ + z₂) ≠ 0 := by
  have hP : PolarNondegOn Q (U a ⊔ U b) := by
    have h := hU.nondeg_biSup ({a, b} : Finset (Fin k))
    rw [show (⨆ j ∈ ({a, b} : Finset (Fin k)), U j) = U a ⊔ U b by
      rw [Finset.iSup_insert, Finset.iSup_singleton]] at h
    exact exists_isFlip_of_maps_aux1 h
  have h3 : 3 ≤ Module.finrank F (U a ⊔ U b : Submodule F V) := by
    have h := hU.finrank_biSup ({a, b} : Finset (Fin k))
    rw [show (⨆ j ∈ ({a, b} : Finset (Fin k)), U j) = U a ⊔ U b by
      rw [Finset.iSup_insert, Finset.iSup_singleton], Finset.card_pair hab] at h
    omega
  obtain ⟨s, hsP, hs0, hsQ⟩ := exists_singular_of_three_le_any (Q := Q) h3
  obtain ⟨f, hfP, hfQ, hsf⟩ := exists_partner_of_polarNondegOn hP hsP hs0 hsQ
  obtain ⟨y₁, hy₁, z₁, hz₁, hs_eq⟩ := Submodule.mem_sup.1 hsP
  obtain ⟨y₂, hy₂, z₂, hz₂, hf_eq⟩ := Submodule.mem_sup.1 hfP
  have hsum : ∀ {y z s' : V}, y ∈ U a → z ∈ U b → y + z = s' → Q s' = 0 → Q y + Q z = 0 := by
    intro y z s' hy hz hyz hs'
    have h : Q (y + z) = 0 := by rw [hyz, hs']
    rwa [QuadraticMap.map_add Q y z, hU.perp a b hab y hy z hz, add_zero] at h
  have hQ₁ : Q y₁ = Q z₁ := add_right_cancel ((hsum hy₁ hz₁ hs_eq hsQ).trans
    (CharTwo.add_self_eq_zero (Q z₁)).symm)
  have hQ₂ : Q y₂ = Q z₂ := add_right_cancel ((hsum hy₂ hz₂ hf_eq hfQ).trans
    (CharTwo.add_self_eq_zero (Q z₂)).symm)
  have hf0 : f ≠ 0 := by
    intro hf
    rw [hf, QuadraticMap.polar_zero_right] at hsf
    exact zero_ne_one hsf
  refine ⟨y₁, z₁, y₂, z₂, hy₁, hz₁, hy₂, hz₂, ?_, ?_, hQ₁, hQ₂, ?_⟩
  · exact fun h0 => exists_hypPair_sum_of_ne_aux3 hU hab hs0 hy₁ hz₁ hs_eq hQ₁ h0
  · exact fun h0 => exists_hypPair_sum_of_ne_aux3 hU hab hf0 hy₂ hz₂ hf_eq hQ₂ h0
  · rw [hs_eq, hf_eq, hsf]; exact one_ne_zero

private theorem aeval_mem_rootSet_specialBlock_aux1 (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hh1 : h ≠ X - 1) :
    h = reciprocalPolynomial h ∧ h.natDegree = 2 ∧
    ∃ (ι : (Fin (primaryMultiplicity x.toLinearMap h) → AdjoinRoot h) →ₗ[F] V),
      Function.Injective ι ∧ LinearMap.range ι = primaryComponent x.toLinearMap h ∧
      (∀ a, algebraMap F (AdjoinRoot h) (Q (ι a)) =
        ∑ i, a i * frobPow F (AdjoinRoot h) 1 (a i)) ∧
      (∀ a, x.toLinearMap (ι a) = ι (AdjoinRoot.root h • a)) := by
  classical
  have hself : h = reciprocalPolynomial h :=
    (hx.reciprocal_eq_of_dvd_card_succ hp hpq hh hh1).symm
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨d, hdeg, hσ2, hσne, hcard, halg, hroot, ι, hinj, hrange, hQι, hxι⟩ :=
    hx.selfDualModel hpodd hh hh1 hself
  have hdeg2 : h.natDegree = 2 :=
    CFSG.RankThree.PartOne.K159.natDegree_eq_two_of_dvd_card_add_one hx hp hp2 hpq hh hh1
  have hd1 : d = 1 := by omega
  subst hd1
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
  have hfin : Module.finrank F (AdjoinRoot h) = 2 * 1 := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  have hQιE : ∀ a, algebraMap F (AdjoinRoot h) (Q (ι a)) =
      ∑ i, a i * frobPow F (AdjoinRoot h) 1 (a i) := by
    intro a
    obtain ⟨hmem, hq⟩ := hQι a
    rw [hq, algebraMap_trace_fixedSubfield F (AdjoinRoot h) hfin ⟨_, hmem⟩]
    simp [frobPow_apply]
  exact ⟨hself, hdeg2, ι, hinj, hrange, hQιE, fun a => hxι a⟩

private theorem aeval_mem_rootSet_specialBlock_aux2 (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hh1 : h ≠ X - 1)
    (ι : (Fin (primaryMultiplicity x.toLinearMap h) → AdjoinRoot h) →ₗ[F] V)
    (hxι : ∀ a, x.toLinearMap (ι a) = ι (AdjoinRoot.root h • a)) :
    ∀ (q : F[X]) (a : Fin (primaryMultiplicity x.toLinearMap h) → AdjoinRoot h),
      aeval x.toLinearMap q (ι a) = ι (AdjoinRoot.mk h q • a) := by
  classical
  have hxpow : ∀ (n : ℕ) (a : Fin (primaryMultiplicity x.toLinearMap h) → AdjoinRoot h),
      (x.toLinearMap ^ n) (ι a) = ι (AdjoinRoot.root h ^ n • a) := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
        intro a
        conv_lhs => rw [pow_succ, Module.End.mul_apply, hxι, ih]
        congr 1
        rw [← mul_smul, ← pow_succ]
  intro q
  induction q using Polynomial.induction_on' with
  | add p r hp' hr' =>
      intro a
      simp only [map_add, LinearMap.add_apply, add_smul]
      rw [hp', hr']
  | monomial n c =>
      intro a
      rw [aeval_monomial]
      have hmk : AdjoinRoot.mk h (monomial n c) =
          algebraMap F (AdjoinRoot h) c * AdjoinRoot.root h ^ n := by
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
        rfl
      rw [hmk, Module.End.mul_apply, Module.algebraMap_end_apply, hxpow]
      rw [show c • ι (AdjoinRoot.root h ^ n • a) = ι (c • (AdjoinRoot.root h ^ n • a)) from
        (map_smul ι c _).symm]
      congr 1
      rw [mul_smul, algebraMap_smul]

private theorem aeval_mem_rootSet_specialBlock_aux3 (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hh1 : h ≠ X - 1)
    (ι : (Fin (primaryMultiplicity x.toLinearMap h) → AdjoinRoot h) →ₗ[F] V)
    (hQιE : ∀ a, algebraMap F (AdjoinRoot h) (Q (ι a)) =
      ∑ i, a i * frobPow F (AdjoinRoot h) 1 (a i))
    (hact : ∀ (q : F[X]) (a : Fin (primaryMultiplicity x.toLinearMap h) → AdjoinRoot h),
      aeval x.toLinearMap q (ι a) = ι (AdjoinRoot.mk h q • a)) :
    ∀ (q : F[X]) (a : Fin (primaryMultiplicity x.toLinearMap h) → AdjoinRoot h),
      algebraMap F (AdjoinRoot h) (Q (aeval x.toLinearMap q (ι a))) =
        AdjoinRoot.mk h q * frobPow F (AdjoinRoot h) 1 (AdjoinRoot.mk h q) *
          algebraMap F (AdjoinRoot h) (Q (ι a)) := by
  intro q a
  rw [hact, hQιE (AdjoinRoot.mk h q • a), hQιE a]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

private theorem aeval_mem_rootSet_specialBlock_aux4 (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hh1 : h ≠ X - 1) :
    ∃ (H : primaryComponent x.toLinearMap h → primaryComponent x.toLinearMap h → AdjoinRoot h),
      (∀ u w c, Algebra.trace F (AdjoinRoot h) (H u w * c) =
        polar Q (u : V) ((c • w : primaryComponent x.toLinearMap h) : V)) ∧
      (∀ u u' w, H (u + u') w = H u w + H u' w) ∧
      (∀ u w w', H u (w + w') = H u w + H u w') ∧
      (∀ c u w, H (c • u) w = frobPow F (AdjoinRoot h) 1 c * H u w) ∧
      (∀ c u w, H u (c • w) = c * H u w) ∧
      (∀ u w, H w u = frobPow F (AdjoinRoot h) 1 (H u w)) ∧
      (∀ z : AdjoinRoot h, algebraMap F (AdjoinRoot h) (Algebra.trace F (AdjoinRoot h) z) =
        z + frobPow F (AdjoinRoot h) 1 z) := by
  classical
  have hself : h = reciprocalPolynomial h :=
    (hx.reciprocal_eq_of_dvd_card_succ hp hpq hh hh1).symm
  have hdeg2 : h.natDegree = 2 :=
    CFSG.RankThree.PartOne.K159.natDegree_eq_two_of_dvd_card_add_one hx hp hp2 hpq hh hh1
  obtain ⟨d, H, hdeg, hroot, htr, hadd₁, hadd₂, hsm₁, hsm₂, hsymm⟩ :=
    hx.exists_selfDual_hermitian (hp.odd_of_ne_two hp2) hh hh1 hself
  have hd1 : d = 1 := by omega
  subst hd1
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
  have hfin : Module.finrank F (AdjoinRoot h) = 2 * 1 := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  have htrace : ∀ z : AdjoinRoot h,
      algebraMap F (AdjoinRoot h) (Algebra.trace F (AdjoinRoot h) z) =
        z + frobPow F (AdjoinRoot h) 1 z := by
    intro z
    rw [FiniteField.algebraMap_trace_eq_sum_pow F (AdjoinRoot h) z]
    have h2 : Module.finrank F (AdjoinRoot h) = 2 := by simpa using hfin
    rw [h2]
    simp [frobPow_apply, Finset.sum_range_succ]
  refine ⟨H, htr, hadd₁, hadd₂, ?_, hsm₂, hsymm, htrace⟩
  exact fun c u w => by rw [hsm₁]

private theorem aeval_mem_rootSet_specialBlock_aux5 (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hh1 : h ≠ X - 1)
    (ι : (Fin (primaryMultiplicity x.toLinearMap h) → AdjoinRoot h) →ₗ[F] V)
    (hrange : LinearMap.range ι = primaryComponent x.toLinearMap h)
    (hQιE : ∀ a, algebraMap F (AdjoinRoot h) (Q (ι a)) =
      ∑ i, a i * frobPow F (AdjoinRoot h) 1 (a i))
    (hQsmul : ∀ (q : F[X]) (a : Fin (primaryMultiplicity x.toLinearMap h) → AdjoinRoot h),
      algebraMap F (AdjoinRoot h) (Q (aeval x.toLinearMap q (ι a))) =
        AdjoinRoot.mk h q * frobPow F (AdjoinRoot h) 1 (AdjoinRoot.mk h q) *
          algebraMap F (AdjoinRoot h) (Q (ι a)))
    (htrace : ∀ z : AdjoinRoot h,
      algebraMap F (AdjoinRoot h) (Algebra.trace F (AdjoinRoot h) z) =
        z + frobPow F (AdjoinRoot h) 1 z) :
    ∀ (c : AdjoinRoot h) (v : primaryComponent x.toLinearMap h),
      polar Q (v : V) ((c • v : primaryComponent x.toLinearMap h) : V) =
        Q (v : V) * Algebra.trace F (AdjoinRoot h) c := by
  intro c v
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective (g := h) c
  · obtain ⟨a, ha⟩ := LinearMap.mem_range.mp (show v.1 ∈ LinearMap.range ι from by
      rw [hrange]; exact v.2)
    have hmem : ι a ∈ primaryComponent x.toLinearMap h := by
      rw [← hrange]; exact LinearMap.mem_range.mpr ⟨a, rfl⟩
    have hv : v = ⟨ι a, hmem⟩ := Subtype.ext ha.symm
    rw [hv]
    set w := aeval x.toLinearMap q (ι a) with hw
    have hcoe : (((AdjoinRoot.mk h q) • (⟨ι a, hmem⟩ : primaryComponent x.toLinearMap h) :
        primaryComponent x.toLinearMap h) : V) = w :=
      coe_mk_smul_primaryComponent x.toLinearMap h q ⟨ι a, hmem⟩
    rw [hcoe]
    have hpol : polar Q (ι a) w = Q (ι a + w) + Q (ι a) + Q w := by
      rw [QuadraticMap.polar, CharTwo.sub_eq_add, CharTwo.sub_eq_add]
    rw [hpol]
    have h1map : aeval x.toLinearMap (1 + q) =
        (1 : Module.End F V) + aeval x.toLinearMap q := by
      rw [map_add, map_one]
    have h1q : aeval x.toLinearMap (1 + q) (ι a) = ι a + w := by
      rw [h1map, LinearMap.add_apply, Module.End.one_apply]
    apply (algebraMap F (AdjoinRoot h)).injective
    rw [map_add, map_add, map_mul, htrace, ← h1q, hQsmul (1 + q) a, hQsmul q a, hQιE a]
    simp only [map_add, map_one]
    haveI : CharP (AdjoinRoot h) 2 :=
      charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective F (AdjoinRoot h)) 2
    have h2 : (2 : AdjoinRoot h) = 0 := CharP.cast_eq_zero (AdjoinRoot h) 2
    ring_nf
    simp [h2]

private theorem aeval_mem_rootSet_specialBlock_aux6 (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hh1 : h ≠ X - 1)
    (H : primaryComponent x.toLinearMap h → primaryComponent x.toLinearMap h → AdjoinRoot h)
    (htr : ∀ u w c, Algebra.trace F (AdjoinRoot h) (H u w * c) =
      polar Q (u : V) ((c • w : primaryComponent x.toLinearMap h) : V))
    (hpolar : ∀ (c : AdjoinRoot h) (v : primaryComponent x.toLinearMap h),
      polar Q (v : V) ((c • v : primaryComponent x.toLinearMap h) : V) =
        Q (v : V) * Algebra.trace F (AdjoinRoot h) c) :
    ∀ v : primaryComponent x.toLinearMap h,
      H v v = algebraMap F (AdjoinRoot h) (Q (v : V)) := by
  intro v
  refine eq_of_trace_mul_eq (K := F) (E := AdjoinRoot h) (e := H v v)
    (e' := algebraMap F (AdjoinRoot h) (Q (v : V))) (fun c => ?_)
  rw [htr v v c, hpolar c v]
  rw [show algebraMap F (AdjoinRoot h) (Q (v : V)) * c = Q (v : V) • c from
    (Algebra.smul_def (R := F) (Q (v : V)) c).symm]
  rw [LinearMap.map_smul (Algebra.trace F (AdjoinRoot h)) (Q (v : V)) c, smul_eq_mul]

private theorem aeval_mem_rootSet_specialBlock_aux7 {E : Type} [Field E] [CharP E 2] {a b : E} (hab : a + b = 0) : b = a := by
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at hab
  exact hab.symm

private theorem aeval_mem_rootSet_specialBlock_aux8 (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hh1 : h ≠ X - 1)
    (H : primaryComponent x.toLinearMap h → primaryComponent x.toLinearMap h → AdjoinRoot h) (htr : ∀ u w c, Algebra.trace F (AdjoinRoot h) (H u w * c) = polar Q (u : V) ((c • w : primaryComponent x.toLinearMap h) : V))
    (hsm₂ : ∀ c u w, H u (c • w) = c * H u w) (hsymm : ∀ u w, H w u = frobPow F (AdjoinRoot h) 1 (H u w)) (htrace : ∀ z : AdjoinRoot h, algebraMap F (AdjoinRoot h) (Algebra.trace F (AdjoinRoot h) z) = z + frobPow F (AdjoinRoot h) 1 z)
    (hσσ : ∀ z : AdjoinRoot h, frobPow F (AdjoinRoot h) 1 (frobPow F (AdjoinRoot h) 1 z) = z) (uU : primaryComponent x.toLinearMap h) (cE : AdjoinRoot h) (hQu : Q (uU : V) = 0) (huw : polar Q (uU : V) ((cE • uU : primaryComponent x.toLinearMap h) : V) = 0) (hQw : Q ((cE • uU : primaryComponent x.toLinearMap h) : V) = 0) :
    ∀ v : primaryComponent x.toLinearMap h, eichler Q (uU : V) ((cE • uU : primaryComponent x.toLinearMap h) : V) (v : V) = ((v + ((cE + frobPow F (AdjoinRoot h) 1 cE) * H uU v) • uU : primaryComponent x.toLinearMap h) : V) := by
  intro v
  rw [eichler_apply hQu huw]
  have hp1 : polar Q (v : V) (uU : V) = Algebra.trace F (AdjoinRoot h) (H v uU) := by
    have h := htr v uU 1
    rw [one_smul, mul_one] at h
    exact h.symm
  have hpc : polar Q (v : V) ((cE • uU : primaryComponent x.toLinearMap h) : V) =
      Algebra.trace F (AdjoinRoot h) (H v uU * cE) := (htr v uU cE).symm
  rw [hp1, hpc]
  rw [hQw, zero_mul, add_zero, sub_eq_add_neg]
  have hneg : ∀ z : V, -z = z := by
    intro z
    rw [neg_eq_iff_add_eq_zero, ← two_smul F z, show (2 : F) = 0 from CharP.cast_eq_zero F 2,
      zero_smul]
  rw [hneg]
  rw [← Submodule.coe_smul (Algebra.trace F (AdjoinRoot h) (H v uU)) (cE • uU),
    ← Submodule.coe_smul (Algebra.trace F (AdjoinRoot h) (H v uU * cE)) uU]
  rw [← Submodule.coe_add, ← Submodule.coe_add, ← Subtype.ext_iff]
  have hm1 : (Algebra.trace F (AdjoinRoot h) (H v uU)) • (cE • uU) =
      ((H v uU + frobPow F (AdjoinRoot h) 1 (H v uU)) * cE) • uU := by
    rw [← algebraMap_smul (AdjoinRoot h) (Algebra.trace F (AdjoinRoot h) (H v uU)),
      htrace, mul_smul]
  have hm2 : (Algebra.trace F (AdjoinRoot h) (H v uU * cE)) • uU =
      (H v uU * cE + frobPow F (AdjoinRoot h) 1 (H v uU * cE)) • uU := by
    rw [← algebraMap_smul (AdjoinRoot h)
      (Algebra.trace F (AdjoinRoot h) (H v uU * cE)), htrace]
  rw [hm1, hm2]
  rw [show H uU v = frobPow F (AdjoinRoot h) 1 (H v uU) from by
    rw [hsymm uU v, hσσ]]
  conv_lhs => rw [add_assoc, ← add_smul]
  rw [map_mul, add_right_inj]
  rw [show ((H v uU + frobPow F (AdjoinRoot h) 1 (H v uU)) * cE +
      (H v uU * cE + frobPow F (AdjoinRoot h) 1 (H v uU) * frobPow F (AdjoinRoot h) 1 cE)) =
      (cE + frobPow F (AdjoinRoot h) 1 cE) * frobPow F (AdjoinRoot h) 1 (H v uU) from by
    have h2 : (2 : AdjoinRoot h) = 0 := by
      haveI : CharP (AdjoinRoot h) 2 :=
        charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective F (AdjoinRoot h)) 2
      exact CharP.cast_eq_zero (AdjoinRoot h) 2
    ring_nf
    simp [h2]]

private theorem aeval_mem_rootSet_specialBlock_aux9 (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hh1 : h ≠ X - 1)
    (H : primaryComponent x.toLinearMap h → primaryComponent x.toLinearMap h → AdjoinRoot h)
    (htr : ∀ u w c, Algebra.trace F (AdjoinRoot h) (H u w * c) =
      polar Q (u : V) ((c • w : primaryComponent x.toLinearMap h) : V))
    (hHvv : ∀ v : primaryComponent x.toLinearMap h, H v v = algebraMap F (AdjoinRoot h) (Q (v : V)))
    (ι : (Fin (primaryMultiplicity x.toLinearMap h) → AdjoinRoot h) →ₗ[F] V)
    (hrange : LinearMap.range ι = primaryComponent x.toLinearMap h)
    (hQsmul : ∀ (q : F[X]) (a : Fin (primaryMultiplicity x.toLinearMap h) → AdjoinRoot h),
      algebraMap F (AdjoinRoot h) (Q (aeval x.toLinearMap q (ι a))) =
        AdjoinRoot.mk h q * frobPow F (AdjoinRoot h) 1 (AdjoinRoot.mk h q) *
          algebraMap F (AdjoinRoot h) (Q (ι a)))
    {u : V} (hu : u ∈ primaryComponent x.toLinearMap h) (hQu : Q u = 0) (c : F[X]) :
    polar Q u ((((AdjoinRoot.mk h c) • (⟨u, hu⟩ : primaryComponent x.toLinearMap h) :
      primaryComponent x.toLinearMap h) : V)) = 0 ∧
      Q ((((AdjoinRoot.mk h c) • (⟨u, hu⟩ : primaryComponent x.toLinearMap h) :
        primaryComponent x.toLinearMap h) : V)) = 0 := by
  classical
  obtain ⟨a, ha⟩ := LinearMap.mem_range.mp (show u ∈ LinearMap.range ι from by rw [hrange]; exact hu)
  have huι : u = ι a := ha.symm
  have hHuu : H ⟨u, hu⟩ ⟨u, hu⟩ = 0 := by
    rw [hHvv ⟨u, hu⟩, hQu, map_zero]
  constructor
  · have hT := htr ⟨u, hu⟩ ⟨u, hu⟩ (AdjoinRoot.mk h c)
    rw [hHuu, zero_mul, map_zero] at hT
    exact hT.symm
  · have hq := hQsmul c a
    rw [← huι, hQu] at hq
    simp only [map_zero, mul_zero] at hq
    rw [show (((AdjoinRoot.mk h c) • (⟨u, hu⟩ : primaryComponent x.toLinearMap h) :
      primaryComponent x.toLinearMap h) : V) = aeval x.toLinearMap c u from
      coe_mk_smul_primaryComponent x.toLinearMap h c ⟨u, hu⟩]
    exact (algebraMap F (AdjoinRoot h)).injective (by simpa using hq)

private theorem aeval_mem_rootSet_specialBlock_aux10 (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hh1 : h ≠ X - 1) (hself : h = reciprocalPolynomial h)
    (H : primaryComponent x.toLinearMap h → primaryComponent x.toLinearMap h → AdjoinRoot h) (htr : ∀ u w c, Algebra.trace F (AdjoinRoot h) (H u w * c) = polar Q (u : V) ((c • w : primaryComponent x.toLinearMap h) : V))
    (hHvv : ∀ v : primaryComponent x.toLinearMap h, H v v = algebraMap F (AdjoinRoot h) (Q (v : V))) (hadd₁ : ∀ u u' w, H (u + u') w = H u w + H u' w) (hadd₂ : ∀ u w w', H u (w + w') = H u w + H u w')
    (hsm₁ : ∀ c u w, H (c • u) w = frobPow F (AdjoinRoot h) 1 c * H u w) (hsm₂ : ∀ c u w, H u (c • w) = c * H u w) (hsymm : ∀ u w, H w u = frobPow F (AdjoinRoot h) 1 (H u w))
    (htrace : ∀ z : AdjoinRoot h, algebraMap F (AdjoinRoot h) (Algebra.trace F (AdjoinRoot h) z) = z + frobPow F (AdjoinRoot h) 1 z) (hσσ : ∀ z : AdjoinRoot h, frobPow F (AdjoinRoot h) 1 (frobPow F (AdjoinRoot h) 1 z) = z)
    (uU : primaryComponent x.toLinearMap h) (cE : AdjoinRoot h) (hQu : Q (uU : V) = 0) (huw : polar Q (uU : V) ((cE • uU : primaryComponent x.toLinearMap h) : V) = 0) (hQw : Q ((cE • uU : primaryComponent x.toLinearMap h) : V) = 0) :
    ∃ hsup : eichler Q (uU : V) ((cE • uU : primaryComponent x.toLinearMap h) : V) ∈ supportedBlock Q x h, blockDet Q x h ⟨eichler Q (uU : V) ((cE • uU : primaryComponent x.toLinearMap h) : V), hsup⟩ = 1 := by
  classical
  haveI : CharP (AdjoinRoot h) 2 := charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective F (AdjoinRoot h)) 2
  have horbit : orbitSpace x.toLinearMap h = primaryComponent x.toLinearMap h := by rw [orbitSpace, ← hself, sup_idem]
  have hc := hx.isCompl_orbit_others hh
  rw [horbit] at hc
  have hufix : ∀ r ∈ othersSpace x.toLinearMap h, eichler Q (uU : V) ((cE • uU : primaryComponent x.toLinearMap h) : V) r = r := by
    intro r hr; refine eichler_apply_of_polar_eq_zero ?_ ?_
    · rw [polar_comm]; exact hx.polar_orbit_others hh (by rw [horbit]; exact uU.2) hr
    · rw [polar_comm]; exact hx.polar_orbit_others hh (by rw [horbit]; exact (cE • uU).2) hr
  let aE : AdjoinRoot h := cE + frobPow F (AdjoinRoot h) 1 cE
  have he : H uU uU = 0 := by rw [hHvv uU, hQu, map_zero]
  have hσa : frobPow F (AdjoinRoot h) 1 aE = -aE := by
    rw [CharTwo.neg_eq]
    change frobPow F (AdjoinRoot h) 1 (cE + frobPow F (AdjoinRoot h) 1 cE) = cE + frobPow F (AdjoinRoot h) 1 cE
    rw [map_add, hσσ, add_comm]
  let γ : BlockGL x h := unitaryTransvection H hadd₂ hsm₂ he aE
  have hpres : ∀ y y' : primaryComponent x.toLinearMap h, H ((γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) y) ((γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) y') = H y y' := by
    intro y y'
    rw [show ((γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) y) = y + (aE * H uU y) • uU from unitaryTransvection_apply H hadd₂ hsm₂ he aE y, show ((γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) y') = y' + (aE * H uU y') • uU from unitaryTransvection_apply H hadd₂ hsm₂ he aE y']
    exact hermitian_transvection_preserves (frobPow F (AdjoinRoot h) 1) H hadd₁ hadd₂ hsm₁ hsm₂ hsymm he hσa y y'
  have hγrange : γ ∈ (blockGL Q x h).range := (hx.mem_range_blockGL_selfDual_iff hh hh1 hself H htr γ).mpr hpres
  obtain ⟨g₀, hg₀⟩ := hγrange
  let g : V ≃ₗ[F] V := eichler Q (uU : V) ((cE • uU : primaryComponent x.toLinearMap h) : V)
  have hgv : ∀ v : V, g v = g₀.1 v := by
    intro v
    obtain ⟨vU, hvU, r, hr, rfl⟩ := exists_add_of_isCompl hc v
    let vV : primaryComponent x.toLinearMap h := ⟨vU, hvU⟩
    show g (vU + r) = g₀.1 (vU + r)
    rw [map_add, map_add, hufix r hr, (mem_supportedBlock.mp g₀.2).2 r hr]
    have h1 : g (vV : V) = ((vV + (aE * H uU vV) • uU : primaryComponent x.toLinearMap h) : V) := aeval_mem_rootSet_specialBlock_aux8 hp hp2 hpq hx hh hh1 H htr hsm₂ hsymm htrace hσσ uU cE hQu huw hQw vV
    have h2 : g₀.1 (vV : V) = ((vV + (aE * H uU vV) • uU : primaryComponent x.toLinearMap h) : V) := by
      rw [← coe_blockGL (Q := Q) (x := x) h g₀ vV, hg₀]
      change (((γ : BlockGL x h) : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) vV : V) = _
      rw [unitaryTransvection_apply H hadd₂ hsm₂ he aE vV]
    rw [h1, h2]
  have hsup : g ∈ supportedBlock Q x h := by rw [show g = g₀.1 from LinearEquiv.ext hgv]; exact g₀.2
  have hsub : (⟨g, hsup⟩ : supportedBlock Q x h) = g₀ := Subtype.ext (LinearEquiv.ext hgv)
  exact ⟨hsup, by rw [blockDet_apply, hsub, hg₀]; exact det_unitaryTransvection H hadd₂ hsm₂ he aE⟩

private theorem exists_decomp_of_polar_eq_zero_aux1 (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hh1 : h ≠ X - 1)
    (H : primaryComponent x.toLinearMap h → primaryComponent x.toLinearMap h → AdjoinRoot h)
    (htr : ∀ u w c, Algebra.trace F (AdjoinRoot h) (H u w * c) = polar Q (u : V) ((c • w : primaryComponent x.toLinearMap h) : V))
    (hadd₁ : ∀ u u' w, H (u + u') w = H u w + H u' w)
    (hsm₁ : ∀ c u w, H (c • u) w = frobPow F (AdjoinRoot h) 1 c * H u w)
    (hsymm : ∀ u w, H w u = frobPow F (AdjoinRoot h) 1 (H u w))
    (hHvv : ∀ v : primaryComponent x.toLinearMap h, H v v = algebraMap F (AdjoinRoot h) (Q (v : V)))
    (yU zU : primaryComponent x.toLinearMap h) (hyz : ∀ c : F[X], polar Q ((aeval x.toLinearMap c) (yU : V)) (zU : V) = 0) :
    H yU zU = 0 ∧ H (yU + zU) yU = algebraMap F (AdjoinRoot h) (Q (yU : V)) := by
  classical
  have hHyz : H yU zU = 0 := by
    refine eq_zero_of_trace_mul_eq_zero F (AdjoinRoot h) (fun b => ?_)
    obtain ⟨c, rfl⟩ := (frobPow F (AdjoinRoot h) 1).surjective b
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective (g := h) c
    rw [mul_comm, ← hsm₁ (AdjoinRoot.mk h q) yU zU]
    have h2 := htr ((AdjoinRoot.mk h q) • yU) zU 1
    rw [one_smul, mul_one] at h2
    rw [h2]
    rw [show (((AdjoinRoot.mk h q) • yU : primaryComponent x.toLinearMap h) : V) =
      aeval x.toLinearMap q (yU : V) from coe_mk_smul_primaryComponent x.toLinearMap h q yU]
    exact hyz q
  refine ⟨hHyz, ?_⟩
  rw [hadd₁, hHvv yU, hsymm yU zU, hHyz, map_zero, add_zero]

private theorem exists_decomp_of_polar_eq_zero_aux2 {x : V ≃ₗ[F] V} {h : F[X]} [Fact (Irreducible h)]
    (H : primaryComponent x.toLinearMap h → primaryComponent x.toLinearMap h → AdjoinRoot h) (htr : ∀ u w c, Algebra.trace F (AdjoinRoot h) (H u w * c) = polar Q (u : V) ((c • w : primaryComponent x.toLinearMap h) : V))
    (hadd₂ : ∀ u w w', H u (w + w') = H u w + H u w') (hsm₂ : ∀ c u w, H u (c • w) = c * H u w)
    (htrace : ∀ z : AdjoinRoot h, algebraMap F (AdjoinRoot h) (Algebra.trace F (AdjoinRoot h) z) = z + frobPow F (AdjoinRoot h) 1 z)
    (yU zU wU : primaryComponent x.toLinearMap h) (hHuy : H (yU + zU) yU = algebraMap F (AdjoinRoot h) (Q (yU : V))) (hQy : Q (yU : V) ≠ 0) (hdeg2 : h.natDegree = 2) (hwu : polar Q ((yU : V) + (zU : V)) (wU : V) = 0) :
    ∃ (a : F) (v : primaryComponent x.toLinearMap h),
      H (yU + zU) v = 0 ∧ (wU : V) = a • (yU : V) + (v : V) := by
  classical
  haveI : CharP (AdjoinRoot h) 2 :=
    charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective F (AdjoinRoot h)) 2
  have htr_uw : Algebra.trace F (AdjoinRoot h) (H (yU + zU) wU) = 0 := by
    have h := htr (yU + zU) wU 1
    rw [one_smul, mul_one] at h
    exact h.trans hwu
  obtain ⟨z, hzdef⟩ : ∃ z : AdjoinRoot h, z = H (yU + zU) wU := ⟨_, rfl⟩
  have hzfix : frobPow F (AdjoinRoot h) 1 z = z := by
    refine aeval_mem_rootSet_specialBlock_aux7 ?_
    rw [← htrace z, hzdef, htr_uw, map_zero]
  have hzmem : z ∈ fixedSubfield F (AdjoinRoot h) 1 := by
    rw [mem_fixedSubfield]; simpa [frobPow_apply] using hzfix
  have hfin : Module.finrank F (AdjoinRoot h) = 2 * 1 := by
    rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, hdeg2]
  have hfr : Module.finrank F ↥(fixedSubfield F (AdjoinRoot h) 1) = 1 := by
    rw [finrank_fixedSubfield (K := F) (E := AdjoinRoot h) (d := 1) hfin]
  have hbot : fixedSubfield F (AdjoinRoot h) 1 = ⊥ :=
    IntermediateField.finrank_eq_one_iff.mp hfr
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp (hbot ▸ hzmem)
  let a₀ : F := a * (Q (yU : V))⁻¹
  have ha₀ : algebraMap F (AdjoinRoot h) a₀ =
      H (yU + zU) wU * (algebraMap F (AdjoinRoot h) (Q (yU : V)))⁻¹ := by
    change algebraMap F (AdjoinRoot h) (a * (Q (yU : V))⁻¹) = _
    rw [map_mul, map_inv₀, ha, hzdef]
  refine ⟨a₀, wU + a₀ • yU, ?_, ?_⟩
  · have hvU : (wU + a₀ • yU : primaryComponent x.toLinearMap h) = wU + a₀ • yU := rfl
    rw [show wU + a₀ • yU = wU + (algebraMap F (AdjoinRoot h) a₀) • yU from by
      rw [algebraMap_smul]]
    rw [hadd₂, hsm₂, hHuy, ha₀]
    have hne : algebraMap F (AdjoinRoot h) (Q (yU : V)) ≠ 0 :=
      fun hh => hQy ((algebraMap F (AdjoinRoot h)).injective (by simpa using hh))
    rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
    exact CharTwo.add_self_eq_zero _
  · change (wU : V) = a₀ • (yU : V) + ((wU + a₀ • yU : primaryComponent x.toLinearMap h) : V)
    rw [Submodule.coe_add, Submodule.coe_smul]
    rw [add_comm (wU : V) (a₀ • (yU : V)), ← add_assoc, ← add_smul,
      show a₀ + a₀ = 0 from CharTwo.add_self_eq_zero a₀, zero_smul, zero_add]

theorem aeval_mem_rootSet_specialBlock (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hh1 : h ≠ X - 1) {u : V} (hu : u ∈ primaryComponent x.toLinearMap h) (hQu : Q u = 0) (c : F[X]) :
    (aeval x.toLinearMap c) u ∈ rootSet Q (specialBlock Q x h) u := by

  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : CharP (AdjoinRoot h) 2 :=
    charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective F (AdjoinRoot h)) 2
  obtain ⟨hself, hdeg2, ι, hinj, hrange, hQιE, hxι⟩ := aeval_mem_rootSet_specialBlock_aux1 hp hp2 hpq hx hh hh1
  have hact := aeval_mem_rootSet_specialBlock_aux2 hp hp2 hpq hx hh hh1 ι hxι
  have hQsmul := aeval_mem_rootSet_specialBlock_aux3 hp hp2 hpq hx hh hh1 ι hQιE hact
  obtain ⟨H, htr, hadd₁, hadd₂, hsm₁, hsm₂, hsymm, htrace⟩ := aeval_mem_rootSet_specialBlock_aux4 hp hp2 hpq hx hh hh1
  have hpolar := aeval_mem_rootSet_specialBlock_aux5 hp hp2 hpq hx hh hh1 ι hrange hQιE hQsmul htrace
  have hHvv := aeval_mem_rootSet_specialBlock_aux6 hp hp2 hpq hx hh hh1 H htr hpolar
  have hfin : Module.finrank F (AdjoinRoot h) = 2 * 1 := by
    rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, hdeg2]
  have hσσ : ∀ z, frobPow F (AdjoinRoot h) 1 (frobPow F (AdjoinRoot h) 1 z) = z :=
    fun z => frobPow_frobPow (K := F) (E := AdjoinRoot h) (d := 1) hfin z
  obtain ⟨huw, hQw⟩ := aeval_mem_rootSet_specialBlock_aux9 hp hp2 hpq hx hh hh1 H htr hHvv ι hrange hQsmul (u := u) hu hQu c
  obtain ⟨hsup, hdet⟩ := aeval_mem_rootSet_specialBlock_aux10 hp hp2 hpq hx hh hh1 hself H htr hHvv hadd₁ hadd₂ hsm₁ hsm₂ hsymm
    htrace hσσ (⟨u, hu⟩ : primaryComponent x.toLinearMap h) (AdjoinRoot.mk h c) hQu huw hQw
  have hw_eq : (((AdjoinRoot.mk h c) • (⟨u, hu⟩ : primaryComponent x.toLinearMap h) :
      primaryComponent x.toLinearMap h) : V) = aeval x.toLinearMap c u :=
    coe_mk_smul_primaryComponent x.toLinearMap h c ⟨u, hu⟩
  refine mem_rootSet.mpr ⟨?_, ?_⟩
  · rw [← hw_eq]; exact huw
  · rw [← hw_eq]; exact mem_specialBlock.mpr ⟨hsup, hdet⟩

private theorem exists_siegel_mem_specialBlock_aux1_inv
    {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]} [Fact (Irreducible h)]
    {d : ℕ} (hd : finrank F (AdjoinRoot h) = 2 * d)
    (hσroot : (frobPow F (AdjoinRoot h) d) (AdjoinRoot.root h) = (AdjoinRoot.root h)⁻¹)
    (hlam0 : AdjoinRoot.root h ≠ 0)
    (ι : (Fin (Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h)) →
      AdjoinRoot h) ≃ₗ[AdjoinRoot h] primaryComponent x.toLinearMap h)
    (a : Fin (Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h)) → AdjoinRoot h) :
    Q (ι (AdjoinRoot.root h • a) : V) - ∑ i, hermitianForm hd ((AdjoinRoot.root h • a) i) =
      Q (ι a : V) - ∑ i, hermitianForm hd (a i) := by
  rw [map_smul ι]
  have hxq : Q ((AdjoinRoot.root h • ι a : primaryComponent x.toLinearMap h) : V) =
      Q (ι a : V) := by
    rw [coe_root_smul_primaryComponent]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx.mem _
  have hherm : ∀ z : AdjoinRoot h, hermitianForm hd (AdjoinRoot.root h * z) =
      hermitianForm hd z := by
    intro z
    rw [hermitianForm_apply, hermitianForm_apply]
    congr 1
    apply Subtype.ext
    rw [coe_unitaryNorm, coe_unitaryNorm, map_mul, hσroot]
    have h1 : AdjoinRoot.root h * z * (AdjoinRoot.root h)⁻¹ = z := by
      rw [mul_comm (AdjoinRoot.root h) z, mul_assoc, mul_inv_cancel₀ hlam0, mul_one]
    rw [← mul_assoc, h1]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hxq]
  refine congrArg₂ HSub.hSub rfl ?_
  rw [Finset.sum_congr rfl fun i _ => hherm (a i)]

private theorem exists_siegel_mem_specialBlock_aux1_hQ
    {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]} [Fact (Irreducible h)]
    {d : ℕ} (hd : finrank F (AdjoinRoot h) = 2 * d)
    (hσroot : (frobPow F (AdjoinRoot h) d) (AdjoinRoot.root h) = (AdjoinRoot.root h)⁻¹)
    (hbal : ∀ (a : AdjoinRoot h) (u w : primaryComponent x.toLinearMap h),
      componentPolar Q x h (a • u) w =
        componentPolar Q x h u ((frobPow F (AdjoinRoot h) d) a • w))
    {ι : (Fin (Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h)) →
      AdjoinRoot h) ≃ₗ[AdjoinRoot h] primaryComponent x.toLinearMap h}
    (hι : ∀ a b, componentPolar Q x h (ι a) (ι b) =
      Algebra.trace F (AdjoinRoot h) (∑ i, (frobPow F (AdjoinRoot h) d) (a i) * b i))
    (hlam1 : AdjoinRoot.root h ≠ 1) (hlamp : AdjoinRoot.root h ^ p = 1)
    (hlam0 : AdjoinRoot.root h ≠ 0) :
    ∀ a, Q (ι a : V) = ∑ i, hermitianForm hd (a i) := by
  intro a
  have hD : ∀ a, Q (ι a : V) - ∑ i, hermitianForm hd (a i) = 0 := by
    refine eq_zero_of_additive_smul_invariant (hx.cast_ne_zero) hlam1 hlamp
      (AddMonoidHom.mk' (fun a => Q (ι a : V) - ∑ i, hermitianForm hd (a i)) ?_) ?_
    · intro a b
      show Q (ι (a + b) : V) - ∑ i, hermitianForm hd ((a + b) i) =
        (Q (ι a : V) - ∑ i, hermitianForm hd (a i)) +
          (Q (ι b : V) - ∑ i, hermitianForm hd (b i))
      rw [map_add ι, Submodule.coe_add, QuadraticMap.map_add (⇑Q) (ι a : V) (ι b : V),
        ← componentPolar_apply, hι a b]
      have hTr : (∑ i, Algebra.trace F (AdjoinRoot h)
          (a i * frobPow F (AdjoinRoot h) d (b i))) =
          Algebra.trace F (AdjoinRoot h) (∑ i, (frobPow F (AdjoinRoot h) d) (a i) * b i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by
          rw [← Algebra.trace_eq_of_algEquiv (frobPow F (AdjoinRoot h) d)
            (a i * frobPow F (AdjoinRoot h) d (b i)), map_mul, frobPow_frobPow F (AdjoinRoot h) hd,
            mul_comm]
      have hsum : (∑ i, hermitianForm hd ((a + b) i)) =
          (∑ i, hermitianForm hd (a i)) + (∑ i, hermitianForm hd (b i)) +
          Algebra.trace F (AdjoinRoot h) (∑ i, (frobPow F (AdjoinRoot h) d) (a i) * b i) := by
        rw [Finset.sum_congr rfl fun i _ => by
          rw [Pi.add_apply, QuadraticMap.map_add (⇑(hermitianForm hd)), hermitianForm_polar],
          Finset.sum_add_distrib, Finset.sum_add_distrib, hTr]
      rw [hsum]; ring
    · intro a
      exact exists_siegel_mem_specialBlock_aux1_inv hx hd hσroot hlam0 ι a
  exact sub_eq_zero.mp (hD a)

private theorem exists_siegel_mem_specialBlock_aux1_final
    {x : V ≃ₗ[F] V} {h : F[X]} [Fact (Irreducible h)]
    (hd : finrank F (AdjoinRoot h) = 2 * 1)
    (ι : (Fin (Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h)) →
      AdjoinRoot h) ≃ₗ[AdjoinRoot h] primaryComponent x.toLinearMap h)
    (hι : ∀ a b, componentPolar Q x h (ι a) (ι b) =
      Algebra.trace F (AdjoinRoot h) (∑ i, (frobPow F (AdjoinRoot h) 1) (a i) * b i))
    (hQ : ∀ a, Q (ι a : V) = ∑ i, hermitianForm hd (a i))
    {v : V} (hv : v ∈ primaryComponent x.toLinearMap h) :
    hermForm (AdjoinRoot h) (componentPolar Q x h)
        ⟨v, hv⟩ ⟨v, hv⟩ = algebraMap F (AdjoinRoot h) (Q v) := by
  have hHι : ∀ a b, hermForm (AdjoinRoot h) (componentPolar Q x h) (ι a) (ι b) =
      ∑ i, (frobPow F (AdjoinRoot h) 1) (a i) * b i := by
    intro a b
    refine hermForm_eq_of_trace (AdjoinRoot h) (componentPolar Q x h) fun c => ?_
    rw [show c • ι b = ι (c • b) from (map_smul ι c b).symm, hι a (c • b)]
    congr 1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    ring
  have hkey : ∀ z : AdjoinRoot h,
      algebraMap F (AdjoinRoot h) (hermitianForm hd z) = z * frobPow F (AdjoinRoot h) 1 z := by
    intro z
    rw [hermitianForm_apply, algebraMap_trace_fixedSubfield F (AdjoinRoot h) hd,
      Finset.sum_range_one, coe_unitaryNorm]
    simp
  rw [show (⟨v, hv⟩ : primaryComponent x.toLinearMap h) = ι (ι.symm ⟨v, hv⟩) from
    (ι.apply_symm_apply _).symm]
  rw [hHι]
  have hQv := hQ (ι.symm ⟨v, hv⟩)
  rw [ι.apply_symm_apply] at hQv
  rw [hQv, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hkey, mul_comm]

private theorem exists_siegel_mem_specialBlock_aux1 (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hh1 : h ≠ X - 1)
    {v : V} (hv : v ∈ primaryComponent x.toLinearMap h) :
    hermForm (AdjoinRoot h) (componentPolar Q x h)
        ⟨v, hv⟩ ⟨v, hv⟩ = algebraMap F (AdjoinRoot h) (Q v) := by
  classical
  have hirr := irreducible_of_mem_primaryFactors hh
  have hself : h = reciprocalPolynomial h :=
    (hx.reciprocal_eq_of_dvd_card_succ hp hpq hh hh1).symm
  have hdeg2 :=
    CFSG.RankThree.PartOne.K159.natDegree_eq_two_of_dvd_card_add_one hx hp hp2 hpq hh hh1
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hsm1, hsm2, hsymm⟩ :=
    hx.exists_selfDual_hermitian (hp.odd_of_ne_two hp2) hh hh1 hself
  have hd : finrank F (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  have hd1 : d = 1 := by omega
  subst hd1
  have hmon := monic_of_mem_primaryFactors hh
  have hlam1 : AdjoinRoot.root h ≠ 1 := root_ne_one hmon hh1
  have hlamp : AdjoinRoot.root h ^ p = 1 := root_pow_eq_one (hx.dvd_X_pow_sub_one hh)
  have hp0 : p ≠ 0 := fun h0 => hx.cast_ne_zero (by rw [h0]; simp)
  have hlam0 : AdjoinRoot.root h ≠ 0 := fun h0 => by
    rw [h0, zero_pow hp0] at hlamp
    exact zero_ne_one hlamp
  set σ := frobPow F (AdjoinRoot h) 1 with hσdef
  have hσroot : σ (AdjoinRoot.root h) = (AdjoinRoot.root h)⁻¹ := by
    rw [hσdef, frobPow_apply, hroot]
  have hbal := hx.polar_smul_balanced σ hσroot hlam0
  have hnd : ∀ u : primaryComponent x.toLinearMap h,
      (∀ w, componentPolar Q x h u w = 0) → u = 0 := fun u hu =>
    Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => hu ⟨w, hw⟩)
  obtain ⟨ι, hι⟩ := exists_hermitian_trace_coordinates (componentPolar Q x h) σ
    (isUnitaryInvolution F (AdjoinRoot h) hd) (fun u w => QuadraticMap.polar_comm Q _ _) hbal hnd
  have hQ := exists_siegel_mem_specialBlock_aux1_hQ hx hd hσroot hbal hι hlam1 hlamp hlam0
  exact exists_siegel_mem_specialBlock_aux1_final hd ι hι hQ hv

private theorem exists_siegel_mem_specialBlock_aux2 {E W : Type*} [Field E] [CharP E 2]
    [AddCommGroup W] [Module E W] (σ : E →+* E) (H : W → W → E)
    (hadd1 : ∀ u u' w, H (u + u') w = H u w + H u' w)
    (hadd2 : ∀ u w w', H u (w + w') = H u w + H u w')
    (hsm1 : ∀ (c : E) u w, H (c • u) w = σ c * H u w)
    (hsm2 : ∀ (c : E) u w, H u (c • w) = c * H u w)
    (hsymm : ∀ u w, H w u = σ (H u w)) (hσσ : ∀ c, σ (σ c) = c)
    {u v : W} (huu : H u u = 0) (huv : H u v = 0) (hvu : H v u = 0)
    {a : E} (ha : a + σ a = H v v) (w w' : W) :
    H (w + H u w • (v + a • u) + H v w • u)
      (w' + H u w' • (v + a • u) + H v w' • u) = H w w' := by
  simp only [hadd1, hadd2, hsm1, hsm2, smul_add, smul_smul]
  rw [huu, huv, hvu]
  simp only [map_zero, zero_mul, mul_zero, add_zero]
  have hwv : H w v = σ (H v w) := hsymm v w
  have hwu : H w u = σ (H u w) := hsymm u w
  rw [hwv, hwu]
  simp only [hσσ, map_mul, map_add]
  have h2 : (2:E) = 0 := CharP.cast_eq_zero E 2
  have h1 : σ a + a = H v v := by rw [add_comm]; exact ha
  rw [← h1]
  ring_nf
  rw [h2]
  simp


private theorem exists_siegel_mem_specialBlock_aux3_part1 (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hh1 : h ≠ X - 1) :
    h = reciprocalPolynomial h ∧ finrank F (AdjoinRoot h) = 2 * 1 ∧
      (∀ c, frobPow F (AdjoinRoot h) 1 (frobPow F (AdjoinRoot h) 1 c) = c) ∧
      (∀ a u w, componentPolar Q x h (a • u) w =
        componentPolar Q x h u (frobPow F (AdjoinRoot h) 1 a • w)) := by
  classical
  have hirr : Irreducible h := Fact.out
  have hself : h = reciprocalPolynomial h :=
    (hx.reciprocal_eq_of_dvd_card_succ hp hpq hh hh1).symm
  obtain ⟨d, -, hdeg, hroot, -, -, -, -, -, -⟩ :=
    hx.exists_selfDual_hermitian (hp.odd_of_ne_two hp2) hh hh1 hself
  have hd2 : h.natDegree = 2 :=
    CFSG.RankThree.PartOne.K159.natDegree_eq_two_of_dvd_card_add_one hx hp hp2 hpq hh hh1
  have hd : finrank F (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  have hd1 : d = 1 := by
    have h := hdeg
    rw [hd2] at h
    omega
  subst hd1
  have hσroot : frobPow F (AdjoinRoot h) 1 (AdjoinRoot.root h) = (AdjoinRoot.root h)⁻¹ := by
    rw [frobPow_apply, hroot]
  have hlamp : AdjoinRoot.root h ^ p = 1 := root_pow_eq_one (hx.dvd_X_pow_sub_one hh)
  have hp0 : p ≠ 0 := fun h0 => hx.cast_ne_zero (by rw [h0]; simp)
  have hlam0 : AdjoinRoot.root h ≠ 0 := fun h0 => by
    rw [h0, zero_pow hp0] at hlamp
    exact zero_ne_one hlamp
  have hbal := hx.polar_smul_balanced (frobPow F (AdjoinRoot h) 1) hσroot hlam0
  exact ⟨hself, hd, fun c => frobPow_frobPow F (AdjoinRoot h) hd c, hbal⟩

private theorem exists_siegel_mem_specialBlock_aux3_part2 {x : V ≃ₗ[F] V} {h : F[X]}
    [Fact (Irreducible h)]
    (hσinvol : ∀ c, frobPow F (AdjoinRoot h) 1 (frobPow F (AdjoinRoot h) 1 c) = c)
    (hbal : ∀ a u w, componentPolar Q x h (a • u) w =
      componentPolar Q x h u (frobPow F (AdjoinRoot h) 1 a • w)) :
    (∀ u w c, Algebra.trace F (AdjoinRoot h)
        (hermForm (AdjoinRoot h) (componentPolar Q x h) u w * c) =
      componentPolar Q x h u (c • w)) ∧
    (∀ u u' w, hermForm (AdjoinRoot h) (componentPolar Q x h) (u + u') w =
      hermForm (AdjoinRoot h) (componentPolar Q x h) u w +
        hermForm (AdjoinRoot h) (componentPolar Q x h) u' w) ∧
    (∀ u w w', hermForm (AdjoinRoot h) (componentPolar Q x h) u (w + w') =
      hermForm (AdjoinRoot h) (componentPolar Q x h) u w +
        hermForm (AdjoinRoot h) (componentPolar Q x h) u w') ∧
    (∀ (c : AdjoinRoot h) u w, hermForm (AdjoinRoot h) (componentPolar Q x h) (c • u) w =
      frobPow F (AdjoinRoot h) 1 c * hermForm (AdjoinRoot h) (componentPolar Q x h) u w) ∧
    (∀ (c : AdjoinRoot h) u w, hermForm (AdjoinRoot h) (componentPolar Q x h) u (c • w) =
      c * hermForm (AdjoinRoot h) (componentPolar Q x h) u w) ∧
    (∀ u w, hermForm (AdjoinRoot h) (componentPolar Q x h) w u =
      frobPow F (AdjoinRoot h) 1 (hermForm (AdjoinRoot h) (componentPolar Q x h) u w)) := by
  refine ⟨fun u w c => ?_, fun u u' w => ?_, fun u w w' => ?_, fun c u w => ?_,
    fun c u w => ?_, fun u w => ?_⟩
  · exact trace_hermForm_mul (AdjoinRoot h) (componentPolar Q x h) u w c
  · exact hermForm_add_left (AdjoinRoot h) (componentPolar Q x h) u u' w
  · exact hermForm_add_right (AdjoinRoot h) (componentPolar Q x h) u w w'
  · exact hermForm_smul_left (frobPow F (AdjoinRoot h) 1) hbal c u w
  · exact hermForm_smul_right (AdjoinRoot h) (componentPolar Q x h) c u w
  · exact hermForm_symm (frobPow F (AdjoinRoot h) 1) hσinvol
      (fun a b => QuadraticMap.polar_comm Q _ _) hbal u w

private theorem exists_siegel_mem_specialBlock_aux3_part3 {x : V ≃ₗ[F] V} {h : F[X]} {y z : V}
    (hQ : Q (y + z) = 0)
    (hyz : ∀ c : F[X], polar Q ((aeval x.toLinearMap c) y) z = 0) :
    (∀ (c : AdjoinRoot h) (w : primaryComponent x.toLinearMap h),
      ((c • w : primaryComponent x.toLinearMap h) : V) =
        aeval x.toLinearMap (Classical.choose (AdjoinRoot.mk_surjective c)) (w : V)) ∧
    Q y = Q z := by
  have hyz1 : polar Q y z = 0 := by
    have := hyz 1
    simpa using this
  have hcoe : ∀ (c : AdjoinRoot h) (w : primaryComponent x.toLinearMap h),
      ((c • w : primaryComponent x.toLinearMap h) : V) =
        aeval x.toLinearMap (Classical.choose (AdjoinRoot.mk_surjective c)) (w : V) := by
    intro c w
    conv_lhs => rw [show c = AdjoinRoot.mk h (Classical.choose (AdjoinRoot.mk_surjective c)) from
      (Classical.choose_spec (AdjoinRoot.mk_surjective c)).symm]
    rw [coe_mk_smul_primaryComponent]
  have h1 : Q y + Q z = 0 := by
    have h := hQ
    rw [QuadraticMap.map_add Q y z, hyz1, add_zero] at h
    exact h
  have h2 : Q y - Q z = 0 := by
    rw [sub_eq_add_neg, CharTwo.neg_eq]
    exact h1
  exact ⟨hcoe, sub_eq_zero.mp h2⟩

private theorem exists_siegel_mem_specialBlock_aux3_part4 {x : V ≃ₗ[F] V} {h : F[X]}
    [Fact (Irreducible h)] [CharP (AdjoinRoot h) 2]
    {H : primaryComponent x.toLinearMap h → primaryComponent x.toLinearMap h → AdjoinRoot h}
    (htr : ∀ u w c, Algebra.trace F (AdjoinRoot h) (H u w * c) =
      componentPolar Q x h u (c • w))
    (hadd1 : ∀ u u' w, H (u + u') w = H u w + H u' w)
    (hadd2 : ∀ u w w', H u (w + w') = H u w + H u w')
    (hsymm : ∀ u w, H w u = frobPow F (AdjoinRoot h) 1 (H u w))
    (hdiag : ∀ (w : V) (hw : w ∈ primaryComponent x.toLinearMap h),
      H ⟨w, hw⟩ ⟨w, hw⟩ = algebraMap F (AdjoinRoot h) (Q w))
    (hcoe : ∀ (c : AdjoinRoot h) (w : primaryComponent x.toLinearMap h),
      ((c • w : primaryComponent x.toLinearMap h) : V) =
        aeval x.toLinearMap (Classical.choose (AdjoinRoot.mk_surjective c)) (w : V))
    {y z v : V} (hy : y ∈ primaryComponent x.toLinearMap h)
    (hz : z ∈ primaryComponent x.toLinearMap h) (hv : v ∈ primaryComponent x.toLinearMap h)
    (hQyz : Q y = Q z)
    (hyz : ∀ c : F[X], polar Q ((aeval x.toLinearMap c) y) z = 0)
    (hvu : ∀ c : F[X], polar Q (y + z) ((aeval x.toLinearMap c) v) = 0) :
    H ⟨y + z, Submodule.add_mem _ hy hz⟩ ⟨y + z, Submodule.add_mem _ hy hz⟩ = 0 ∧
    H ⟨y + z, Submodule.add_mem _ hy hz⟩ ⟨v, hv⟩ = 0 ∧
    H ⟨v, hv⟩ ⟨y + z, Submodule.add_mem _ hy hz⟩ = 0 ∧
    H ⟨y + z, Submodule.add_mem _ hy hz⟩ ⟨y, hy⟩ = algebraMap F (AdjoinRoot h) (Q y) := by
  let u : primaryComponent x.toLinearMap h := ⟨y + z, Submodule.add_mem _ hy hz⟩
  let yU : primaryComponent x.toLinearMap h := ⟨y, hy⟩
  let zU : primaryComponent x.toLinearMap h := ⟨z, hz⟩
  let vU : primaryComponent x.toLinearMap h := ⟨v, hv⟩
  have hu_eq : u = yU + zU := Subtype.ext rfl
  have hHzu0 : H zU yU = 0 := by
    refine eq_of_trace_mul_eq (K := F) fun c => ?_
    rw [zero_mul, map_zero, htr, componentPolar_apply]
    rw [show ((c • yU : primaryComponent x.toLinearMap h) : V) =
      aeval x.toLinearMap (Classical.choose (AdjoinRoot.mk_surjective c)) y from hcoe c yU]
    rw [QuadraticMap.polar_comm]
    exact hyz _
  have hHyz : H yU zU = 0 := by rw [hsymm zU yU, hHzu0, map_zero]
  have hHuv : H u vU = 0 := by
    refine eq_of_trace_mul_eq (K := F) fun c => ?_
    rw [zero_mul, map_zero, htr, componentPolar_apply]
    rw [show ((c • vU : primaryComponent x.toLinearMap h) : V) =
      aeval x.toLinearMap (Classical.choose (AdjoinRoot.mk_surjective c)) v from hcoe c vU]
    exact hvu _
  have hHuu : H u u = 0 := by
    rw [hu_eq, hadd1, hadd2 yU, hadd2 zU]
    rw [hHyz, hHzu0, hdiag y hy, hdiag z hz, hQyz]
    simp [CharTwo.add_self_eq_zero]
  have hHuy : H u yU = algebraMap F (AdjoinRoot h) (Q y) := by
    rw [hu_eq, hadd1, hHzu0, add_zero, hdiag y hy]
  have hHvu0 : H vU u = 0 := by rw [hsymm u vU, hHuv, map_zero]
  exact ⟨hHuu, hHuv, hHvu0, hHuy⟩

private theorem exists_siegel_mem_specialBlock_aux3_part5 {E W : Type*} [Field E] [CharP E 2]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (σ : E →+* E) (H : W → W → E)
    (hadd1 : ∀ u u' w, H (u + u') w = H u w + H u' w)
    (hadd2 : ∀ u w w', H u (w + w') = H u w + H u w')
    (hsm1 : ∀ (c : E) u w, H (c • u) w = σ c * H u w)
    (hsm2 : ∀ (c : E) u w, H u (c • w) = c * H u w)
    (hsymm : ∀ u w, H w u = σ (H u w)) (hσσ : ∀ c, σ (σ c) = c)
    {u v : W} (huu : H u u = 0) (huv : H u v = 0) (hvu : H v u = 0)
    {a : E} (ha : a + σ a = H v v) :
    ∃ S : (Module.End E W)ˣ,
      (∀ w, (S : Module.End E W) w = w + H u w • (v + a • u) + H v w • u) ∧
      (∀ w w', H ((S : Module.End E W) w) ((S : Module.End E W) w') = H w w') ∧
      LinearMap.det ((S : (Module.End E W)ˣ) : Module.End E W) = 1 := by
  have hφ₁ : hermTransvectionForm H hadd2 hsm2 u 1 (v + a • u) = 0 := by
    show (1 : E) * H u (v + a • u) = 0
    rw [one_mul, hadd2, huv, hsm2, huu, mul_zero, add_zero]
  have hφ₂ : hermTransvectionForm H hadd2 hsm2 v 1 u = 0 := by
    show (1 : E) * H v u = 0
    rw [one_mul, hvu]
  let S : (Module.End E W)ˣ :=
    transvectionUnit (hermTransvectionForm H hadd2 hsm2 u 1) (v + a • u) hφ₁ *
      transvectionUnit (hermTransvectionForm H hadd2 hsm2 v 1) u hφ₂
  have hSapp : ∀ w : W, (S : Module.End E W) w =
      w + H u w • (v + a • u) + H v w • u := by
    intro w
    show ((transvectionUnit (hermTransvectionForm H hadd2 hsm2 u 1) (v + a • u) hφ₁ :
        (Module.End E W)ˣ) : Module.End E W)
        (((transvectionUnit (hermTransvectionForm H hadd2 hsm2 v 1) u hφ₂ :
          (Module.End E W)ˣ) : Module.End E W) w) = _
    rw [transvectionUnit_apply, transvectionUnit_apply]
    show w + ((1 : E) * H v w) • u +
        ((1 : E) * H u (w + ((1 : E) * H v w) • u)) • (v + a • u) = _
    rw [one_mul, one_mul, hadd2, hsm2, huu, mul_zero, add_zero]
    abel
  have hSpres : ∀ w w' : W, H ((S : Module.End E W) w) ((S : Module.End E W) w') = H w w' := by
    intro w w'
    rw [hSapp, hSapp]
    exact exists_siegel_mem_specialBlock_aux2 σ H hadd1 hadd2 hsm1 hsm2 hsymm hσσ huu huv hvu ha w w'
  have hSdet : LinearMap.det ((S : (Module.End E W)ˣ) : Module.End E W) = 1 := by
    show LinearMap.det ((transvectionUnit (hermTransvectionForm H hadd2 hsm2 u 1) (v + a • u) hφ₁ *
      transvectionUnit (hermTransvectionForm H hadd2 hsm2 v 1) u hφ₂ :
        (Module.End E W)ˣ) : Module.End E W) = 1
    rw [Units.val_mul, map_mul, det_transvectionUnit, det_transvectionUnit, one_mul]
  exact ⟨S, hSapp, hSpres, hSdet⟩

private theorem exists_siegel_mem_specialBlock_aux3_part6 (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hh1 : h ≠ X - 1) {y z v : V}
    (hy : y ∈ primaryComponent x.toLinearMap h) (hz : z ∈ primaryComponent x.toLinearMap h)
    (hv : v ∈ primaryComponent x.toLinearMap h) (hQ : Q (y + z) = 0)
    (hyz : ∀ c : F[X], polar Q ((aeval x.toLinearMap c) y) z = 0)
    (hvu : ∀ c : F[X], polar Q (y + z) ((aeval x.toLinearMap c) v) = 0) :
    ∃ g ∈ specialBlock Q x h, g (y + z) = y + z ∧
      ∃ c : F[X], g y = y + Q y • v + (aeval x.toLinearMap c) (y + z) := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : CharP (AdjoinRoot h) 2 := charP_of_injective_algebraMap (algebraMap F (AdjoinRoot h)).injective 2
  obtain ⟨hself, hd, hσinvol, hbal⟩ := exists_siegel_mem_specialBlock_aux3_part1 hp hp2 hpq hx hh hh1
  obtain ⟨hcoe, hQyz⟩ := exists_siegel_mem_specialBlock_aux3_part3 hQ hyz
  obtain ⟨htr, hadd1, hadd2, hsm1, hsm2, hsymm⟩ :=
    exists_siegel_mem_specialBlock_aux3_part2 (x := x) (h := h) hσinvol hbal
  let H : primaryComponent x.toLinearMap h → primaryComponent x.toLinearMap h → AdjoinRoot h :=
    hermForm (AdjoinRoot h) (componentPolar Q x h)
  have hdiag := fun (w : V) (hw : w ∈ primaryComponent x.toLinearMap h) =>
    exists_siegel_mem_specialBlock_aux1 hp hp2 hpq hx hh hh1 hw
  obtain ⟨hHuu, hHuv, hHvu0, hHuy⟩ :=
    exists_siegel_mem_specialBlock_aux3_part4 (H := H) htr hadd1 hadd2 hsymm hdiag hcoe hy hz hv hQyz hyz hvu
  let u : primaryComponent x.toLinearMap h := ⟨y + z, Submodule.add_mem _ hy hz⟩
  let yU : primaryComponent x.toLinearMap h := ⟨y, hy⟩
  let vU : primaryComponent x.toLinearMap h := ⟨v, hv⟩
  obtain ⟨a, ha⟩ := (isUnitaryInvolution F (AdjoinRoot h) hd).trace_surj (H vU vU) (hsymm vU vU).symm
  obtain ⟨S, hSapp, hSpres, hSdet⟩ := exists_siegel_mem_specialBlock_aux3_part5
    (frobPow F (AdjoinRoot h) 1).toRingEquiv.toRingHom H hadd1 hadd2 hsm1 hsm2 hsymm hσinvol
    hHuu hHuv hHvu0 ha
  obtain ⟨g, hgS⟩ := (hx.mem_range_blockGL_selfDual_iff hh hh1 hself H
    (fun u w c => trace_hermForm_mul (AdjoinRoot h) (componentPolar Q x h) u w c) S).mpr hSpres
  have hgdet : blockDet Q x h ⟨g.1, g.2⟩ = 1 := by rw [blockDet_apply, hgS, hSdet]
  refine ⟨g.1, mem_specialBlock.mpr ⟨g.2, hgdet⟩, ?_, ?_⟩
  · have h1 : ((S : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) u) = u := by
      rw [hSapp]; simp [show H ⟨y + z, Submodule.add_mem _ hy hz⟩ u = 0 from hHuu, show H ⟨v, hv⟩ u = 0 from hHvu0]
    have hthis := coe_blockGL (Q := Q) (x := x) h g u
    rw [hgS, h1] at hthis
    exact hthis.symm
  · have h1 : ((S : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) yU) =
        yU + algebraMap F (AdjoinRoot h) (Q y) • vU + (H u yU * a + H vU yU) • u := by
      rw [hSapp, show H ⟨y + z, Submodule.add_mem _ hy hz⟩ yU = algebraMap F (AdjoinRoot h) (Q y) from hHuy, smul_add, smul_smul, add_smul]; abel
    have hthis := coe_blockGL (Q := Q) (x := x) h g yU
    rw [hgS, h1] at hthis
    obtain ⟨c, hc⟩ := AdjoinRoot.mk_surjective (H u yU * a + H vU yU)
    refine ⟨c, ?_⟩
    have hc' : (H u yU * a + H vU yU) • u = (AdjoinRoot.mk h c) • u := by rw [hc]
    rw [← hthis, hc']
    simp only [Submodule.coe_add]
    rw [coe_algebraMap_smul_primaryComponent, coe_mk_smul_primaryComponent]

private theorem exists_siegel_mem_specialBlock_aux3 (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hh1 : h ≠ X - 1) {y z v : V} (hy : y ∈ primaryComponent x.toLinearMap h)
    (hz : z ∈ primaryComponent x.toLinearMap h) (hv : v ∈ primaryComponent x.toLinearMap h)
    (hQ : Q (y + z) = 0) (hyz : ∀ c : F[X], polar Q ((aeval x.toLinearMap c) y) z = 0)
    (hvu : ∀ c : F[X], polar Q (y + z) ((aeval x.toLinearMap c) v) = 0) :
    ∃ g ∈ specialBlock Q x h, g (y + z) = y + z ∧
      ∃ c : F[X], g y = y + Q y • v + (aeval x.toLinearMap c) (y + z) :=
  exists_siegel_mem_specialBlock_aux3_part6 hp hp2 hpq hx hh hh1 hy hz hv hQ hyz hvu

theorem exists_siegel_mem_specialBlock (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hh1 : h ≠ X - 1) {y z v : V} (hy : y ∈ primaryComponent x.toLinearMap h)
    (hz : z ∈ primaryComponent x.toLinearMap h) (hv : v ∈ primaryComponent x.toLinearMap h)
    (hQ : Q (y + z) = 0) (hyz : ∀ c : F[X], polar Q ((aeval x.toLinearMap c) y) z = 0)
    (hvu : ∀ c : F[X], polar Q (y + z) ((aeval x.toLinearMap c) v) = 0) :
    ∃ g ∈ specialBlock Q x h, g (y + z) = y + z ∧
      ∃ c : F[X], g y = y + Q y • v + (aeval x.toLinearMap c) (y + z) :=
  exists_siegel_mem_specialBlock_aux3 hp hp2 hpq hx hh hh1 hy hz hv hQ hyz hvu

theorem exists_decomp_of_polar_eq_zero (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hh1 : h ≠ X - 1) {y z : V} (hy : y ∈ primaryComponent x.toLinearMap h)
    (hz : z ∈ primaryComponent x.toLinearMap h) (hQ : Q (y + z) = 0) (hQy : Q y ≠ 0)
    (hyz : ∀ c : F[X], polar Q ((aeval x.toLinearMap c) y) z = 0) {w : V}
    (hw : w ∈ primaryComponent x.toLinearMap h) (hwu : polar Q (y + z) w = 0) :
    ∃ (a : F) (v : V), v ∈ primaryComponent x.toLinearMap h ∧
      (∀ c : F[X], polar Q (y + z) ((aeval x.toLinearMap c) v) = 0) ∧ w = a • y + v := by

  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : CharP (AdjoinRoot h) 2 :=
    charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective F (AdjoinRoot h)) 2
  obtain ⟨hself, hdeg2, ι, hinj, hrange, hQιE, hxι⟩ := aeval_mem_rootSet_specialBlock_aux1 hp hp2 hpq hx hh hh1
  have hact := aeval_mem_rootSet_specialBlock_aux2 hp hp2 hpq hx hh hh1 ι hxι
  have hQsmul := aeval_mem_rootSet_specialBlock_aux3 hp hp2 hpq hx hh hh1 ι hQιE hact
  obtain ⟨H, htr, hadd₁, hadd₂, hsm₁, hsm₂, hsymm, htrace⟩ := aeval_mem_rootSet_specialBlock_aux4 hp hp2 hpq hx hh hh1
  have hpolar := aeval_mem_rootSet_specialBlock_aux5 hp hp2 hpq hx hh hh1 ι hrange hQιE hQsmul htrace
  have hHvv := aeval_mem_rootSet_specialBlock_aux6 hp hp2 hpq hx hh hh1 H htr hpolar
  let yU : primaryComponent x.toLinearMap h := ⟨y, hy⟩
  let zU : primaryComponent x.toLinearMap h := ⟨z, hz⟩
  let wU : primaryComponent x.toLinearMap h := ⟨w, hw⟩
  obtain ⟨hHyz, hHuy⟩ := exists_decomp_of_polar_eq_zero_aux1 hp hp2 hpq hx hh hh1 H htr hadd₁ hsm₁ hsymm hHvv yU zU
    (fun c => by rw [show (yU : V) = y from rfl, show (zU : V) = z from rfl]; exact hyz c)
  obtain ⟨a, vU, hHuv, hwv⟩ := exists_decomp_of_polar_eq_zero_aux2 (x := x) (h := h) H htr hadd₂ hsm₂ htrace yU zU wU hHuy
    (by rw [show (yU : V) = y from rfl]; exact hQy) hdeg2 (by
      rw [show (yU : V) = y from rfl, show (zU : V) = z from rfl, show (wU : V) = w from rfl]
      exact hwu)
  refine ⟨a, (vU : V), vU.2, ?_, ?_⟩
  · intro c
    have hT := htr (yU + zU) vU (AdjoinRoot.mk h c)
    rw [hHuv, zero_mul, map_zero] at hT
    rw [← coe_mk_smul_primaryComponent x.toLinearMap h c vU]
    simpa [yU, zU] using hT.symm
  · simpa [yU, wU] using hwv

private theorem mem_rootSet_of_polar_eq_zero_aux1 {x : V ≃ₗ[F] V} (c : F) (u : V) :
    (aeval x.toLinearMap (C c * X)) u = c • (x u) := by
  rw [Polynomial.C_mul_X_eq_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
    Module.algebraMap_end_apply, pow_one]
  rfl

private theorem mem_rootSet_of_polar_eq_zero_aux2 (hp : p.Prime) {d : V ≃ₗ[F] V}
    (hd : OddOrderIsometry Q p d) (hmaps : ∀ j, ∀ x ∈ U j, d x ∈ U j) (j : Fin k) :
    ∀ x ∈ U j, d⁻¹ x ∈ U j := by
  have hdinv : d⁻¹ = d ^ (p - 1) := by
    have hp1 : 1 ≤ p := hp.one_le
    have h : d * d ^ (p - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hp1, hd.pow_eq_one]
    exact inv_eq_of_mul_eq_one_right h
  intro x hx
  rw [hdinv]
  have hpow : ∀ n : ℕ, (d ^ n) x ∈ U j := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [pow_succ', LinearEquiv.mul_apply]; exact hmaps j _ ih
  exact hpow (p - 1)

private theorem mem_rootSet_of_polar_eq_zero_aux3 {a c : Fin k} {d d'' : V ≃ₗ[F] V}
    (hd'' : IsFlip Q U d d'' {a, c}) (hmaps : ∀ j, ∀ x ∈ U j, d x ∈ U j)
    (hinv : ∀ j, ∀ x ∈ U j, d⁻¹ x ∈ U j) (j : Fin k) :
    ∀ x ∈ U j, d'' x ∈ U j := by
  intro x hx
  rw [hd''.2.2 j x hx]
  split_ifs with hj
  · exact hinv j x hx
  · exact hmaps j x hx

private theorem mem_rootSet_of_polar_eq_zero_aux11 {a c : Fin k} {d d'' : V ≃ₗ[F] V}
    (hd : OddOrderIsometry Q p d) (hd'' : IsFlip Q U d d'' {a, c})
    (hmaps : ∀ j, ∀ x ∈ U j, d x ∈ U j) (hinv : ∀ j, ∀ x ∈ U j, d⁻¹ x ∈ U j)
    (j : Fin k) : ∀ y ∈ U j, (d'' ^ p) y = y := by
  intro y hy
  have hdinvpow : (d⁻¹) ^ p = 1 := by rw [inv_pow, hd.pow_eq_one, inv_one]
  have hmem_inv : ∀ m : ℕ, ((d⁻¹) ^ m) y ∈ U j := by
    intro m
    induction m with
    | zero => simpa using hy
    | succ m ih => rw [pow_succ', LinearEquiv.mul_apply]; exact hinv j _ ih
  have hmem_d : ∀ m : ℕ, (d ^ m) y ∈ U j := by
    intro m
    induction m with
    | zero => simpa using hy
    | succ m ih => rw [pow_succ', LinearEquiv.mul_apply]; exact hmaps j _ ih
  by_cases hj : j ∈ ({a, c} : Finset (Fin k))
  · have hag : ∀ s ∈ U j, d'' s = d⁻¹ s := fun s hs => by rw [hd''.2.2 j s hs, if_pos hj]
    have hpow : ∀ m : ℕ, (d'' ^ m) y = ((d⁻¹) ^ m) y := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [pow_succ', pow_succ', LinearEquiv.mul_apply, LinearEquiv.mul_apply, ih]
        exact hag _ (hmem_inv m)
    rw [hpow p, hdinvpow]
    rfl
  · have hag : ∀ s ∈ U j, d'' s = d s := fun s hs => by rw [hd''.2.2 j s hs, if_neg hj]
    have hpow : ∀ m : ℕ, (d'' ^ m) y = (d ^ m) y := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [pow_succ', pow_succ', LinearEquiv.mul_apply, LinearEquiv.mul_apply, ih]
        exact hag _ (hmem_d m)
    rw [hpow p, hd.pow_eq_one]
    rfl

private theorem mem_rootSet_of_polar_eq_zero_aux4 {a c : Fin k} (hU : IsPlaneSystem Q U)
    {d d'' : V ≃ₗ[F] V}
    (hd : OddOrderIsometry Q p d) (hd'' : IsFlip Q U d d'' {a, c})
    (hmaps : ∀ j, ∀ x ∈ U j, d x ∈ U j) (hinv : ∀ j, ∀ x ∈ U j, d⁻¹ x ∈ U j) :
    d'' ^ p = 1 := by
  have hkeyW : ∀ w ∈ (⨆ j, U j), (d'' ^ p) w = w := by
    intro w hw
    refine Submodule.iSup_induction U (motive := fun w => (d'' ^ p) w = w) hw
      (fun j y hy => mem_rootSet_of_polar_eq_zero_aux11 hd hd'' hmaps hinv j y hy)
      (map_zero _) ?_
    intro x y hx hy
    rw [map_add, hx, hy]
  have hfixpow : ∀ w ∈ polarPerp Q (⨆ j, U j), (d'' ^ p) w = w := by
    intro w hw
    have : ∀ n : ℕ, (d'' ^ n) w = w := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ', LinearEquiv.mul_apply, ih]; exact hd''.2.1 w hw
    exact this p
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ (⨆ j, U j) ⊔ polarPerp Q (⨆ j, U j) := by
    rw [hU.isCompl_iSup.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add, hkeyW w hw, hfixpow z hz]
  simp

private theorem mem_rootSet_of_polar_eq_zero_aux5 (hp : p.Prime) (hpq : p ∣ Nat.card F + 1)
    {a c : Fin k} {d : V ≃ₗ[F] V} (hd : OddOrderIsometry Q p d) {h : F[X]}
    (hh : h ∈ primaryFactors d.toLinearMap) (hh1 : h ≠ X - 1)
    (hUh : ∀ j, U j ≤ primaryComponent d.toLinearMap h)
    {d'' : V ≃ₗ[F] V} (hd'' : IsFlip Q U d d'' {a, c})
    (hd''maps : ∀ j, ∀ x ∈ U j, d'' x ∈ U j) :
    ∀ j, U j ≤ primaryComponent d''.toLinearMap h := by
  have hself := CFSG.RankThree.PartOne.K159.reciprocalPolynomial_eq_of_dvd_card_add_one hd hpq hh
  intro j x hx
  rw [mem_primaryComponent]
  by_cases hj : j ∈ ({a, c} : Finset (Fin k))
  · have hag : ∀ s ∈ U j, d'' s = d⁻¹ s := fun s hs => by rw [hd''.2.2 j s hs, if_pos hj]
    have hae := CFSG.RankThree.PartOne.KCLinPlane.aeval_apply_eq_of_agree (x := d''.toLinearMap)
      (y := (d⁻¹).toLinearMap) (by exact fun s hs => hd''maps j s hs)
      (fun s hs => hag s hs) h hx
    rw [hae]
    have h0 : h.coeff 0 ≠ 0 := hd.coeff_zero_ne hh
    have hx' : x ∈ primaryComponent d.toLinearMap h := hUh j hx
    have h2 := (mem_primaryComponent_reciprocalPolynomial (x := d) h0).mp (hself.symm ▸ hx')
    exact h2
  · have hag : ∀ s ∈ U j, d'' s = d s := fun s hs => by rw [hd''.2.2 j s hs, if_neg hj]
    have hae := CFSG.RankThree.PartOne.KCLinPlane.aeval_apply_eq_of_agree (x := d''.toLinearMap)
      (y := d.toLinearMap) (by exact fun s hs => hd''maps j s hs)
      (fun s hs => hag s hs) h hx
    rw [hae]
    exact mem_primaryComponent.mp (hUh j hx)

private theorem mem_rootSet_of_polar_eq_zero_aux6 (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {d : V ≃ₗ[F] V} (hd : OddOrderIsometry Q p d) {h : F[X]}
    (hh : h ∈ primaryFactors d.toLinearMap) (hh1 : h ≠ X - 1)
    {y : V} (hy : y ∈ primaryComponent d.toLinearMap h) :
    d y + d⁻¹ y = (h.coeff 1) • y := by
  have hmon := monic_of_mem_primaryFactors hh
  have hself := CFSG.RankThree.PartOne.K159.reciprocalPolynomial_eq_of_dvd_card_add_one hd hpq hh
  have h0 : h.coeff 0 ≠ 0 := hd.coeff_zero_ne hh
  have hcoeff0 : h.coeff 0 = 1 := by
    have h1 : h.coeff 0 * h.coeff 0 = 1 := by
      have h2 := coeff_zero_reciprocalPolynomial (h := h) hmon
      rw [hself] at h2
      calc h.coeff 0 * h.coeff 0 = (h.coeff 0)⁻¹ * h.coeff 0 :=
            congrArg (fun x => x * h.coeff 0) h2
        _ = 1 := inv_mul_cancel₀ h0
    have h1' : h.coeff 0 ^ 2 = 1 := by rw [pow_two]; exact h1
    rcases sq_eq_one_iff.mp h1' with h2 | h2
    · exact h2
    · simpa [CharTwo.neg_eq] using h2
  have hdeg2 : h.natDegree = 2 :=
    CFSG.RankThree.PartOne.K159.natDegree_eq_two_of_dvd_card_add_one hd hp hp2 hpq hh hh1
  have hc2 : h.coeff 2 = 1 := by
    have := hmon.coeff_natDegree
    rwa [hdeg2] at this
  have hyy : d (d y) + (h.coeff 1) • d y + y = 0 := by
    have h1 : aeval d.toLinearMap h y = 0 := mem_primaryComponent.mp hy
    rw [Polynomial.aeval_eq_sum_range' (n := 3) (by omega)] at h1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, LinearMap.add_apply,
      LinearMap.smul_apply, hc2, pow_zero, Module.End.one_apply, pow_one, one_smul] at h1
    have h2 : (d.toLinearMap ^ 2) y = d (d y) := by rw [pow_two, Module.End.mul_apply]; rfl
    rw [h2] at h1
    simp only [LinearEquiv.coe_coe] at h1
    calc d (d y) + h.coeff 1 • d y + y = h.coeff 0 • y + h.coeff 1 • d y + d (d y) := by
          rw [hcoeff0, one_smul]; abel
      _ = 0 := h1
  have hdh : d y + (h.coeff 1) • y + d⁻¹ y = 0 := by
    have h := congrArg (fun v => d.symm v) hyy
    rw [map_add, map_add, map_zero, map_smul, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply] at h
    simpa [add_assoc] using h
  have hgoal : d y + d⁻¹ y + (h.coeff 1) • y = 0 := by
    rw [← hdh]; abel
  have hneg : d y + d⁻¹ y = -((h.coeff 1) • y) := add_eq_zero_iff_eq_neg.mp hgoal
  have hneg' : -((h.coeff 1) • y) = (h.coeff 1) • y :=
    neg_eq_self_of_two_eq_zero (K := F) CharTwo.two_eq_zero ((h.coeff 1) • y)
  exact hneg.trans hneg'

private theorem mem_rootSet_of_polar_eq_zero_aux7 {a b c : Fin k} {d d'' : V ≃ₗ[F] V}
    (hd'' : IsFlip Q U d d'' {a, c}) (hab : a ≠ b) (hbc : b ≠ c)
    {t : F} (ht : t ≠ 0) {y z : V} (hy : y ∈ U a) (hz : z ∈ U b)
    (hrel : d y + d⁻¹ y = t • y) (f : F) :
    (aeval d.toLinearMap (C (f * t⁻¹) * X)) (y + z) +
      (aeval d''.toLinearMap (C (f * t⁻¹) * X)) (y + z) = f • y := by
  have hdy : d'' y = d⁻¹ y := by rw [hd''.2.2 a y hy, if_pos (by simp)]
  have hdz : d'' z = d z := by
    have hbz : b ∉ ({a, c} : Finset (Fin k)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hab, hbc⟩
    rw [hd''.2.2 b z hz, if_neg hbz]
  rw [mem_rootSet_of_polar_eq_zero_aux1 (x := d) (f * t⁻¹) (y + z),
      mem_rootSet_of_polar_eq_zero_aux1 (x := d'') (f * t⁻¹) (y + z),
      map_add, map_add, hdy, hdz]
  have hcancel : (f * t⁻¹) • d z + (f * t⁻¹) • d z = 0 := by
    rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]
  calc (f * t⁻¹) • (d y + d z) + (f * t⁻¹) • (d⁻¹ y + d z)
      = (f * t⁻¹) • d y + (f * t⁻¹) • d⁻¹ y +
          ((f * t⁻¹) • d z + (f * t⁻¹) • d z) := by
        rw [smul_add, smul_add]; abel
    _ = (f * t⁻¹) • d y + (f * t⁻¹) • d⁻¹ y := by rw [hcancel, add_zero]
    _ = (f * t⁻¹) • (d y + d⁻¹ y) := by rw [smul_add]
    _ = (f * t⁻¹) • (t • y) := by rw [hrel]
    _ = f • y := by
      rw [show (f * t⁻¹) • (t • y) = ((f * t⁻¹) * t) • y from
        smul_smul (f * t⁻¹) t y]
      rw [mul_assoc, inv_mul_cancel₀ ht, mul_one]

private theorem mem_rootSet_of_polar_eq_zero_aux8 {h : F[X]} (hirr : Irreducible h)
    (hmon : h.Monic) (hne : h ≠ X - 1) : h.eval 1 ≠ 0 := by
  intro h0
  have h3 : (X - C 1 : F[X]) ∣ h := Polynomial.dvd_iff_isRoot.2 h0
  have h4 := (irreducible_X_sub_C (1 : F)).associated_of_dvd hirr h3
  exact hne (by simpa using
    (Polynomial.eq_of_monic_of_associated (monic_X_sub_C (1 : F)) hmon h4).symm)

private theorem mem_rootSet_of_polar_eq_zero_aux9 (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {d : V ≃ₗ[F] V} (hd : OddOrderIsometry Q p d) {h : F[X]}
    (hh : h ∈ primaryFactors d.toLinearMap) (hh1 : h ≠ X - 1) : h.coeff 1 ≠ 0 := by
  have hmon := monic_of_mem_primaryFactors hh
  have hirr := irreducible_of_mem_primaryFactors hh
  have hself := CFSG.RankThree.PartOne.K159.reciprocalPolynomial_eq_of_dvd_card_add_one hd hpq hh
  have h0 : h.coeff 0 ≠ 0 := hd.coeff_zero_ne hh
  have hcoeff0 : h.coeff 0 = 1 := by
    have h1 : h.coeff 0 * h.coeff 0 = 1 := by
      have h2 := coeff_zero_reciprocalPolynomial (h := h) hmon
      rw [hself] at h2
      calc h.coeff 0 * h.coeff 0 = (h.coeff 0)⁻¹ * h.coeff 0 :=
            congrArg (fun x => x * h.coeff 0) h2
        _ = 1 := inv_mul_cancel₀ h0
    have h1' : h.coeff 0 ^ 2 = 1 := by rw [pow_two]; exact h1
    rcases sq_eq_one_iff.mp h1' with h2 | h2
    · exact h2
    · simpa [CharTwo.neg_eq] using h2
  have hdeg2 : h.natDegree = 2 :=
    CFSG.RankThree.PartOne.K159.natDegree_eq_two_of_dvd_card_add_one hd hp hp2 hpq hh hh1
  have hc2 : h.coeff 2 = 1 := by
    have := hmon.coeff_natDegree
    rwa [hdeg2] at this
  have heval1 : h.eval 1 = h.coeff 1 := by
    rw [Polynomial.eval_eq_sum_range' (n := 3) (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hc2, hcoeff0, pow_zero,
      pow_one, one_pow, one_mul, mul_one]
    rw [add_assoc, add_comm (h.coeff 1) 1, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  intro ht0
  exact mem_rootSet_of_polar_eq_zero_aux8 hirr hmon hh1 (by rw [heval1, ht0])

private theorem mem_rootSet_of_polar_eq_zero_aux10 (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {h : F[X]}
    (hhx : h ∈ primaryFactors x.toLinearMap) (hh1 : h ≠ X - 1) {u : V}
    (hu : u ∈ primaryComponent x.toLinearMap h)
    (hQu : Q u = 0) {H : Subgroup (V ≃ₗ[F] V)} (hle : specialBlock Q x h ≤ H) (f : F[X]) :
    (aeval x.toLinearMap f) u ∈ rootSet Q H u := by
  have h := aeval_mem_rootSet_specialBlock hp hp2 hpq hx hhx hh1 hu hQu f
  exact mem_rootSet.2 ⟨(mem_rootSet.1 h).1, hle (mem_rootSet.1 h).2⟩

private theorem mem_rootSet_of_polar_eq_zero_aux12 (hU : IsPlaneSystem Q U) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {d : V ≃ₗ[F] V} (hd : OddOrderIsometry Q p d)
    (hmaps : ∀ j, ∀ x ∈ U j, d x ∈ U j) {h : F[X]}
    (hh : h ∈ primaryFactors d.toLinearMap) (hh1 : h ≠ X - 1)
    (hUh : ∀ j, U j ≤ primaryComponent d.toLinearMap h) {a b c : Fin k} (hab : a ≠ b)
    (hbc : b ≠ c) {d'' : V ≃ₗ[F] V} (hd'' : IsFlip Q U d d'' {a, c}) {y z : V}
    (hy : y ∈ U a) (hz : z ∈ U b) (hQyz : Q y = Q z) (hQy : Q y ≠ 0) :
    OddOrderIsometry Q p d'' ∧ h ∈ primaryFactors d''.toLinearMap ∧
      d y + d⁻¹ y = (h.coeff 1) • y ∧ h.coeff 1 ≠ 0 ∧ Q (y + z) = 0 ∧
      y + z ∈ primaryComponent d''.toLinearMap h := by
  have hy_d : y ∈ primaryComponent d.toLinearMap h := hUh a hy
  have hz_d : z ∈ primaryComponent d.toLinearMap h := hUh b hz
  have hQu : Q (y + z) = 0 := by
    rw [QuadraticMap.map_add Q y z, hU.perp a b hab y hy z hz, hQyz, add_zero]
    exact CharTwo.add_self_eq_zero (Q z)
  have hdisj : Disjoint (U a) (U b) := by
    have h := hU.disjoint_biSup (a := a) (s := {b}) (by simp [hab])
    simpa using h
  have hu0 : y + z ≠ 0 := by
    intro h0
    have hyz' : y = z := by
      have : y = -z := eq_neg_of_add_eq_zero_left h0
      have hzs : -z = z := neg_eq_self_of_two_eq_zero (K := F) CharTwo.two_eq_zero z
      rwa [hzs] at this
    have hyb : y = 0 := (Submodule.mem_bot F).1 (hdisj.le_bot ⟨hy, by rw [hyz']; exact hz⟩)
    exact hQy (by rw [hyb, map_zero])
  have hinv : ∀ j, ∀ x ∈ U j, d⁻¹ x ∈ U j := mem_rootSet_of_polar_eq_zero_aux2 hp hd hmaps
  have hd''maps : ∀ j, ∀ x ∈ U j, d'' x ∈ U j := mem_rootSet_of_polar_eq_zero_aux3 hd'' hmaps hinv
  have hd''pow : d'' ^ p = 1 := mem_rootSet_of_polar_eq_zero_aux4 hU hd hd'' hmaps hinv
  have hd''odd : OddOrderIsometry Q p d'' := ⟨hd''.1, hd''pow, hd.cast_ne_zero, hd.regular⟩
  have hUh'' : ∀ j, U j ≤ primaryComponent d''.toLinearMap h :=
    mem_rootSet_of_polar_eq_zero_aux5 hp hpq hd hh hh1 hUh hd'' hd''maps
  have hu'' : y + z ∈ primaryComponent d''.toLinearMap h :=
    (primaryComponent d''.toLinearMap h).add_mem (hUh'' a hy) (hUh'' b hz)
  have hh'' : h ∈ primaryFactors d''.toLinearMap :=
    CFSG.RankThree.PartOne.KCUnitaryMixing.mem_primaryFactors_of_apply_eq_zero
      (irreducible_of_mem_primaryFactors hh) (monic_of_mem_primaryFactors hh)
      (mem_primaryComponent.mp hu'') hu0
  exact ⟨hd''odd, hh'', mem_rootSet_of_polar_eq_zero_aux6 hp hp2 hpq hd hh hh1 hy_d,
    mem_rootSet_of_polar_eq_zero_aux9 hp hp2 hpq hd hh hh1, hQu, hu''⟩

private theorem mem_rootSet_of_polar_eq_zero_aux14 {a b c : Fin k} {d d'' : V ≃ₗ[F] V}
    (hd'' : IsFlip Q U d d'' {a, c}) (hab : a ≠ b) (hbc : b ≠ c) {h : F[X]}
    {H : Subgroup (V ≃ₗ[F] V)} {y z : V} (hy : y ∈ U a) (hz : z ∈ U b)
    (hrel : d y + d⁻¹ y = (h.coeff 1) • y) (htt : h.coeff 1 ≠ 0)
    (hgen_d : ∀ f : F[X], (aeval d.toLinearMap f) (y + z) ∈ rootSet Q H (y + z))
    (hgen_d'' : ∀ f : F[X], (aeval d''.toLinearMap f) (y + z) ∈ rootSet Q H (y + z)) :
    ∀ f : F, f • y ∈ rootSet Q H (y + z) := by
  intro f
  have h := (rootSet Q H (y + z)).add_mem
    (hgen_d (C (f * (h.coeff 1)⁻¹) * X)) (hgen_d'' (C (f * (h.coeff 1)⁻¹) * X))
  convert h using 1
  exact (mem_rootSet_of_polar_eq_zero_aux7 hd'' hab hbc htt hy hz hrel f).symm

private theorem mem_rootSet_of_polar_eq_zero_aux15 (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {d : V ≃ₗ[F] V} (hd : OddOrderIsometry Q p d) {h : F[X]}
    (hh : h ∈ primaryFactors d.toLinearMap) (hh1 : h ≠ X - 1) {H : Subgroup (V ≃ₗ[F] V)}
    (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hH₁ : specialBlock Q d h ≤ H)
    {y z : V} (hy_d : y ∈ primaryComponent d.toLinearMap h)
    (hz_d : z ∈ primaryComponent d.toLinearMap h) (hQu : Q (y + z) = 0)
    (hyz : ∀ f : F[X], polar Q ((aeval d.toLinearMap f) y) z = 0)
    (hgen_d : ∀ f : F[X], (aeval d.toLinearMap f) (y + z) ∈ rootSet Q H (y + z))
    (hyR : y ∈ rootSet Q H (y + z)) (hQy : Q y ≠ 0) :
    ∀ v ∈ primaryComponent d.toLinearMap h,
      (∀ f : F[X], polar Q (y + z) ((aeval d.toLinearMap f) v) = 0) →
        v ∈ rootSet Q H (y + z) := by
  intro v hv hvu
  set v' : V := (Q y)⁻¹ • v with hv'
  have hv'p : v' ∈ primaryComponent d.toLinearMap h := Submodule.smul_mem _ (Q y)⁻¹ hv
  have hvu' : ∀ f : F[X], polar Q (y + z) ((aeval d.toLinearMap f) v') = 0 := by
    intro f
    rw [hv', map_smul, QuadraticMap.polar_smul_right, hvu f, smul_zero]
  obtain ⟨g, hg, hgu, f, hgy⟩ :=
    exists_siegel_mem_specialBlock hp hp2 hpq hd hh hh1 hy_d hz_d hv'p hQu hyz hvu'
  have hgyR : g y ∈ rootSet Q H (y + z) := by
    have := rootSet_map hHO (hH₁ hg) hyR
    rwa [hgu] at this
  have hQyv' : Q y • v' = v := by rw [hv', smul_smul, mul_inv_cancel₀ hQy, one_smul]
  have hv_eq : v = g y - y - (aeval d.toLinearMap f) (y + z) := by
    rw [hgy, hQyv']; abel
  rw [hv_eq]
  exact (rootSet Q H (y + z)).sub_mem
    ((rootSet Q H (y + z)).sub_mem hgyR hyR) (hgen_d f)

theorem mem_rootSet_of_polar_eq_zero (hU : IsPlaneSystem Q U) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {d : V ≃ₗ[F] V} (hd : OddOrderIsometry Q p d)
    (hmaps : ∀ j, ∀ x ∈ U j, d x ∈ U j) (hfix : ∀ x ∈ polarPerp Q (⨆ j, U j), d x = x)
    {h : F[X]} (hh : h ∈ primaryFactors d.toLinearMap) (hh1 : h ≠ X - 1)
    (hUh : ∀ j, U j ≤ primaryComponent d.toLinearMap h) {a b c : Fin k} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) {d'' : V ≃ₗ[F] V} (hd'' : IsFlip Q U d d'' {a, c})
    {H : Subgroup (V ≃ₗ[F] V)} (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hH₁ : specialBlock Q d h ≤ H) (hH₂ : specialBlock Q d'' h ≤ H) {y z : V} (hy : y ∈ U a)
    (hz : z ∈ U b) (hQyz : Q y = Q z) (hQy : Q y ≠ 0) :
    ∀ w ∈ (⨆ j, U j : Submodule F V), polar Q (y + z) w = 0 → w ∈ rootSet Q H (y + z) := by
  classical
  intro w hw hwu
  obtain ⟨hd''odd, hh'', hrel, htt, hQu, hu''⟩ :=
    mem_rootSet_of_polar_eq_zero_aux12 hU hp hp2 hpq hd hmaps hh hh1 hUh hab hbc hd'' hy hz hQyz hQy
  have hy_d : y ∈ primaryComponent d.toLinearMap h := hUh a hy
  have hz_d : z ∈ primaryComponent d.toLinearMap h := hUh b hz
  have hu_d : y + z ∈ primaryComponent d.toLinearMap h :=
    (primaryComponent d.toLinearMap h).add_mem hy_d hz_d
  have hgen_d : ∀ f : F[X], (aeval d.toLinearMap f) (y + z) ∈ rootSet Q H (y + z) :=
    fun f => mem_rootSet_of_polar_eq_zero_aux10 hp hp2 hpq hd hh hh1 hu_d hQu hH₁ f
  have hgen_d'' : ∀ f : F[X], (aeval d''.toLinearMap f) (y + z) ∈ rootSet Q H (y + z) :=
    fun f => mem_rootSet_of_polar_eq_zero_aux10 hp hp2 hpq hd''odd hh'' hh1 hu'' hQu hH₂ f
  have hsmR : ∀ f : F, f • y ∈ rootSet Q H (y + z) :=
    mem_rootSet_of_polar_eq_zero_aux14 hd'' hab hbc hy hz hrel htt hgen_d hgen_d''
  have hyR : y ∈ rootSet Q H (y + z) := by
    have := hsmR 1
    rwa [one_smul] at this
  have hyz : ∀ f : F[X], polar Q ((aeval d.toLinearMap f) y) z = 0 := by
    intro f
    exact hU.perp a b hab ((aeval d.toLinearMap f) y)
      (CFSG.RankThree.PartOne.KCLinPlane.aeval_mem_of_stable (fun s hs => hmaps a s hs) f hy)
      z hz
  have hvR := mem_rootSet_of_polar_eq_zero_aux15 hp hp2 hpq hd hh hh1 hHO hH₁ hy_d hz_d hQu hyz
    hgen_d hyR hQy
  obtain ⟨f, v, hv, hvu, hwv⟩ := exists_decomp_of_polar_eq_zero hp hp2 hpq hd hh hh1 hy_d hz_d
    hQu hQy hyz (iSup_le hUh hw) hwu
  rw [hwv]
  exact (rootSet Q H (y + z)).add_mem (hsmR f) (hvR v hv hvu)

theorem eichler_mem_iSup_specialBlock (hk : 3 ≤ k) (hU : IsPlaneSystem Q U) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {d : V ≃ₗ[F] V} (hd : OddOrderIsometry Q p d)
    (hmaps : ∀ j, ∀ x ∈ U j, d x ∈ U j) (hfix : ∀ x ∈ polarPerp Q (⨆ j, U j), d x = x)
    {h : F[X]} (hh : h ∈ primaryFactors d.toLinearMap) (hh1 : h ≠ X - 1)
    (hUh : ∀ j, U j ≤ primaryComponent d.toLinearMap h) :
    ∀ e ∈ (⨆ j, U j : Submodule F V), ∀ w ∈ (⨆ j, U j : Submodule F V),
      eichler Q e w ∈ ⨆ d' ∈ {d' : V ≃ₗ[F] V | IsEvenFlip Q U d d'}, specialBlock Q d' h := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc⟩ : ∃ a b c : Fin k, a ≠ b ∧ a ≠ c ∧ b ≠ c :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, by simp [Fin.ext_iff], by simp [Fin.ext_iff],
      by simp [Fin.ext_iff]⟩
  obtain ⟨d'', hd''⟩ := exists_isFlip_of_maps hU hd.mem hmaps ({a, c} : Finset (Fin k))
  set S : Set (V ≃ₗ[F] V) := {d' | IsEvenFlip Q U d d'} with hS
  set H : Subgroup (V ≃ₗ[F] V) := ⨆ d' ∈ S, specialBlock Q d' h with hH
  have hdS : d ∈ S := ⟨∅, by simp, isFlip_self hd.mem hfix⟩
  have hd''S : d'' ∈ S := ⟨{a, c}, by rw [Finset.card_pair hac]; exact even_two, hd''⟩
  have hH₁ : specialBlock Q d h ≤ H := le_iSup₂_of_le d hdS le_rfl
  have hH₂ : specialBlock Q d'' h ≤ H := le_iSup₂_of_le d'' hd''S le_rfl
  have hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q := iSup₂_le fun d' _ g hg =>
    (Subgroup.mem_inf.1 (specialBlock_le_isometryCentralizer h hg)).1
  obtain ⟨y₁, z₁, y₂, z₂, hy₁, hz₁, hy₂, hz₂, hQy₁, hQy₂, hQ₁, hQ₂, hpol⟩ :=
    exists_hypPair_sum_of_ne hU hab
  have hsing : ∀ {y z : V}, y ∈ U a → z ∈ U b → Q y = Q z → Q (y + z) = 0 := by
    intro y z hy hz hQ
    rw [QuadraticMap.map_add Q y z, hU.perp a b hab y hy z hz, hQ, add_zero]
    exact CharTwo.add_self_eq_zero _
  have hmemW : ∀ {y z : V}, y ∈ U a → z ∈ U b → y + z ∈ (⨆ j, U j : Submodule F V) := fun hy hz =>
    Submodule.add_mem _ (Submodule.mem_iSup_of_mem a hy) (Submodule.mem_iSup_of_mem b hz)
  exact eichler_mem_of_relRoot hHO (polarNondegOn_iSup_of_isPlaneSystem hU) (hmemW hy₁ hz₁) (hmemW hy₂ hz₂)
    (hsing hy₁ hz₁ hQ₁) (hsing hy₂ hz₂ hQ₂) hpol
    (fun w hw hwu => (mem_rootSet.1 (mem_rootSet_of_polar_eq_zero hU hp hp2 hpq hd hmaps hfix hh hh1 hUh
      hab hac hbc hd'' hHO hH₁ hH₂ hy₁ hz₁ hQ₁ hQy₁ w hw hwu)).2)
    (fun w hw hwu => (mem_rootSet.1 (mem_rootSet_of_polar_eq_zero hU hp hp2 hpq hd hmaps hfix hh hh1 hUh
      hab hac hbc hd'' hHO hH₁ hH₂ hy₂ hz₂ hQ₂ hQy₂ w hw hwu)).2)

end CFSG.LocalAnalysis.GLTheoremA.T173U

end
