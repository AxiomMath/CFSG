module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3QuotEdge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3Quot

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)}

theorem le_of_four {S D : Subgroup Y} {z j : Y} (hz : z * z = 1) (hj : j * j = 1)
    (hzj : z * j = j * z) (hz1 : z ≠ 1) (hj1 : j ≠ 1) (hne : z ≠ j) (hD : Odd (Nat.card D))
    (hzD : z ∈ Subgroup.normalizer (D : Set Y)) (hjD : j ∈ Subgroup.normalizer (D : Set Y))
    (hCz : Subgroup.centralizer ({z} : Set Y) ≤ S) (hCj : Subgroup.centralizer ({j} : Set Y) ≤ S)
    (hCzj : Subgroup.centralizer ({z * j} : Set Y) ≤ S) : D ≤ S := by
  set E : Subgroup Y := Subgroup.closure ({z, j} : Set Y) with hEdef
  have hzE : z ∈ E := Subgroup.subset_closure (by simp)
  have hjE : j ∈ E := Subgroup.subset_closure (by simp)
  have hEcomm : E ≤ Subgroup.centralizer (E : Set Y) := by
    rw [hEdef, Subgroup.centralizer_closure, Subgroup.closure_le]
    rintro x (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] <;>
      rintro y (rfl | rfl)
    · rfl
    · exact hzj.symm
    · exact hzj
    · rfl
  have hEab : IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · exact (Subgroup.mem_centralizer_iff.mp (hEcomm a.2) b b.2).symm
    · rw [pow_two]
      exact mul_self_eq_one_of_mem_closure_pair hz hj hzj hx
  have h2 : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hz) hz1
  have hle : Subgroup.zpowers z ≤ E := Subgroup.zpowers_le.mpr hzE
  have hdvd : 2 ∣ Nat.card E := h2 ▸ Subgroup.card_dvd_of_le hle
  have hjn : j ∉ Subgroup.zpowers z := fun h =>
    (eq_one_or_eq_of_mem_zpowers hz h).elim hj1 (Ne.symm hne)
  have hne2 : Nat.card E ≠ 2 := fun h =>
    hjn ((Subgroup.eq_of_le_of_card_ge hle (by rw [h, h2])) ▸ hjE)
  have hpos : 0 < Nat.card E := Nat.card_pos
  have h4 : 2 ^ 2 ≤ Nat.card E := by omega
  have hEN : E ≤ Subgroup.normalizer (D : Set Y) := by
    rw [hEdef, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hzD
    · exact hjD
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_two
    hEab h4 hEN (Nat.coprime_two_left.mpr hD)
  rw [← hgen]
  refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
  refine inf_le_right.trans ?_
  rcases (mem_closure_pair_iff hz hj hzj).mp ha with h | h | h | h
  · exact absurd h ha1
  · rw [h]; exact hCz
  · rw [h]; exact hCj
  · rw [h]; exact hCzj

theorem le_conjStab_of_forall_mem {H : Subgroup Y} {C : Set (Subgroup Y)}
    (h : ∀ g ∈ H, ∀ M ∈ C, conjSub g M ∈ C) : H ≤ conjStab C := by
  intro g hg M
  refine ⟨fun hM => ?_, fun hM => h g hg M hM⟩
  have := h g⁻¹ (H.inv_mem hg) _ hM
  rwa [conjSub_inv_conjSub] at this

theorem aStar_eq_of_mem {K L : Subgroup Y} (hK : K ∈ Φ) (hL : L ∈ aStar Φ K) :
    aStar Φ L = aStar Φ K :=
  Set.Subset.antisymm (aStar_subset_aStar_of_mem hL)
    (aStar_subset_aStar_of_mem (mem_aStar_symm hK hL).2)

theorem centralizer_le_conjStab_aStar_of_mem (hc : ConjInvariant Φ) {K L : Subgroup Y}
    (hK : K ∈ Φ) (hL : L ∈ aStar Φ K) {e : Y} (he : IsUniqueInvolution L e) :
    Subgroup.centralizer ({e} : Set Y) ≤ conjStab (aStar Φ K) := by
  have h1 := centralizer_le_conjStab_aStar hc (mem_of_mem_aStar hK hL) he
  rwa [aStar_eq_of_mem hK hL] at h1

theorem centralizer_le_conjStab_dstarComp_of_mem (hΦ : HypOmegaGen Φ) {K L : Subgroup Y}
    (hK : K ∈ Φ) (hL : L ∈ dstarComp Φ K) {e : Y} (he : IsUniqueInvolution L e) :
    Subgroup.centralizer ({e} : Set Y) ≤ conjStab (dstarComp Φ K) := by
  have hc := hΦ.conjInvariant
  obtain ⟨hLΦ, hKL⟩ := mem_dstarComp_symm hK hL
  refine le_conjStab_of_forall_mem fun c hc' M hM => ?_
  have hce : c * e * c⁻¹ = e := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc'
    rw [this]
    group
  have hcL : conjSub c L ∈ dstarComp Φ K := by
    by_cases hLc : conjSub c L = L
    · rw [hLc]
      exact hL
    · have hzc : IsUniqueInvolution (conjSub c L) e := by
        have := he.conj c
        rwa [hce] at this
      have hnbr := Q3CL.T3.twin_mem_omegaNbr hΦ hLΦ (hc c L hLΦ) hLc he hzc
      exact hL.tail ⟨hc c L hLΦ, Or.inl (Q3T6.Mu.omegaNbr_subset_omegaStarNbr hΦ L hnbr)⟩
  have hLM : M ∈ dstarComp Φ L := hKL.trans hM
  exact hcL.trans (dstarComp_conj hc hLM c)

theorem exists_conj_mul_involution (hΦ : HypOmegaGen Φ) {K J : Subgroup Y} (hK : K ∈ Φ)
    {zK zJ : Y} (hv : AViol Φ K J zK zJ) :
    ∃ t ∈ J, IsUniqueInvolution (conjSub t K) (zK * zJ) := by
  obtain ⟨u, v, R, T, c⟩ := Sec6Gen.exists_cfg64 hΦ hK hv.mem hv.hzK hv.hzJ hv.star hv.not_nbr
  obtain ⟨t, ht, htv⟩ := c.symm.exists_r
  refine ⟨t, c.hT.1 ht, ?_⟩
  have := hv.hzK.conj t
  rwa [c.conj_t_z ht htv] at this

theorem conjStab_aStar_of_four (hΦ : HypOmegaGen Φ) {K J : Subgroup Y} (hK : K ∈ Φ) {zK zJ : Y}
    (hv : AViol Φ K J zK zJ) {D : Subgroup Y} (hD : Odd (Nat.card D))
    (hzK : zK ∈ Subgroup.normalizer (D : Set Y)) (hzJ : zJ ∈ Subgroup.normalizer (D : Set Y)) :
    D ≤ conjStab (aStar Φ K) := by
  have hc := hΦ.conjInvariant
  have hJA : J ∈ aStar Φ K := Relation.ReflTransGen.single ⟨hv.mem, Or.inl ⟨zK, zJ, hv⟩⟩
  obtain ⟨t, htJ, ht⟩ := exists_conj_mul_involution hΦ hK hv
  have hKtA : conjSub t K ∈ aStar Φ K :=
    (mem_conjStab_iff.mp (le_conjStab_aStar hc hK hJA htJ) K).mpr Relation.ReflTransGen.refl
  exact le_of_four hv.hzK.sq hv.hzJ.sq (aViol_involution_comm hΦ hv) hv.hzK.ne_one
    hv.hzJ.ne_one (aViol_involution_ne hΦ hK hv) hD hzK hzJ
    (centralizer_le_conjStab_aStar_of_mem hc hK Relation.ReflTransGen.refl hv.hzK)
    (centralizer_le_conjStab_aStar_of_mem hc hK hJA hv.hzJ)
    (centralizer_le_conjStab_aStar_of_mem hc hK hKtA ht)

theorem le_conjStab_aStar_of_normal (hΦ : HypOmegaGen Φ) {X : Subgroup Y} [X.Normal]
    (hX : Odd (Nat.card X)) {K : Subgroup Y} (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K) :
    X ≤ conjStab (aStar Φ K) := by
  obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp hA
  exact conjStab_aStar_of_four hΦ hK hv hX (mem_normalizer_of_normal X zK)
    (mem_normalizer_of_normal X zJ)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3Quot
