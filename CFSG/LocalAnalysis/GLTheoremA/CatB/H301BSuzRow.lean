module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BSuzDat
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BDefs
public import CFSG.Sporadic.Bridge.SuzSurj
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphismsCongr
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzOuterReduce
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenTr

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.SuzOddCore
open scoped commutatorElement

section Aut

variable
  {S : Type} [Group S]

@[expose] noncomputable def suzAutIso (θ : S ≃* suzM) : MulAut S ≃* ↥suzT :=
  (MulAut.congr θ).trans (MulEquiv.ofBijective suzConjT suzConjT_bijective).symm

theorem suzConjT_suzAutIso (θ : S ≃* suzM) (α : MulAut S) :
    suzConjT (suzAutIso θ α) = MulAut.congr θ α :=
  (MulEquiv.ofBijective suzConjT suzConjT_bijective).apply_symm_apply (MulAut.congr θ α)

theorem suzAutIso_mem_iff (θ : S ≃* suzM) (α : MulAut S) :
    α ∈ (MulAut.conj : S →* MulAut S).range ↔
      ((suzAutIso θ α : ↥suzT) : Equiv.Perm (Fin 1782)) ∈ suzM := by
  have h1 : α ∈ (MulAut.conj : S →* MulAut S).range ↔
      MulAut.congr θ α ∈ (MulAut.conj : suzM →* MulAut suzM).range :=
    (ComponentClassification.OuterAutomorphisms.congr_mem_inner_iff θ α).symm
  rw [h1, ← suzConjT_map_suzM, ← suzConjT_suzAutIso θ α]
  constructor
  · rintro ⟨u, hu, hu'⟩
    exact Subgroup.mem_subgroupOf.mp (suzConjT_bijective.1 hu' ▸ hu)
  · exact fun h => ⟨_, Subgroup.mem_subgroupOf.mpr h, rfl⟩

theorem commutator_mem_suzM (s t : ↥suzT) :
    ((⁅s, t⁆ : ↥suzT) : Equiv.Perm (Fin 1782)) ∈ suzM := by
  have hidx := suzM_index_T
  have e : ⁅s, t⁆ = (s * t) * (s⁻¹ * t⁻¹) := by rw [commutatorElement_def]; group
  have : ⁅s, t⁆ ∈ suzM.subgroupOf suzT := by
    rw [e, Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
      Subgroup.mul_mem_iff_of_index_two hidx, inv_mem_iff, inv_mem_iff]
  exact Subgroup.mem_subgroupOf.mp this

end Aut

section Row


theorem rowSuz_holds (hU : USuz) : I301BRow .suz := by
  intro S _ _ hS B I K R0 R1 y hBinn hBe hBc hyB hy1 _ _ _ hR0y hR0 hR0c _ _ hKB hR1 hKB1 h01
  obtain ⟨i, hi, ⟨e₁⟩⟩ := hS
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  have θ : S ≃* suzM := (e₁.trans (by exact b.symm)).trans suzEquivM
  set Φ : MulAut S ≃* ↥suzT := suzAutIso θ with hΦ
  haveI : Finite (MulAut S) := Finite.of_equiv _ Φ.symm.toEquiv
  have hR0c' : Nat.card R0 = 2 ^ 5 := hR0c
  have hBe' : IsElemAbelian 3 B := hBe
  have hBc' : Nat.card B = 3 ^ 3 := hBc
  have hR0e : timmesfeldIsExtraspecial ↥R0 := hR0.resolve_right (by rw [hR0c']; norm_num)
  obtain ⟨c, hc1, -⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center ↥R0)).mp hR0e.2.2.2
  set z : MulAut S := ((c : ↥R0) : MulAut S) with hz
  have hzR0 : z ∈ R0 := (c : ↥R0).2
  have hzc : ∀ r ∈ R0, r * z = z * r := fun r hr =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 c.2 ⟨r, hr⟩)
  have hz1 : z ≠ 1 := fun h => hc1 (Subtype.ext (Subtype.ext h))
  have hz2 : orderOf z = 2 := by
    have h1 : orderOf c ∣ 2 := hR0e.2.2.2 ▸ orderOf_dvd_natCard c
    have h2 : orderOf c ≠ 1 := fun h => hc1 (orderOf_eq_one_iff.1 h)
    have h3 : orderOf c = 2 := ((Nat.dvd_prime Nat.prime_two).1 h1).resolve_left h2
    rw [hz, Subgroup.orderOf_coe, Subgroup.orderOf_coe, h3]
  have hBA : B ≤ K ⊔ B := le_sup_right
  have hBz : B ≤ Subgroup.centralizer ({z} : Set (MulAut S)) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.2
      (comm_of_mem_normalizer hR0e hzR0 hzc hz1 (hKB (hBA ha)))
  have hzM : ((Φ z : ↥suzT) : Equiv.Perm (Fin 1782)) ∈ suzM := by
    have h1 : (c : ↥R0) ∈ commutator ↥R0 := by
      rw [hR0e.2.1, hR0e.2.2.1]
      exact c.2
    have h2 : commutator ↥R0 ≤ ((suzM.subgroupOf suzT).comap Φ.toMonoidHom).subgroupOf R0 := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      show ((Φ ⁅(a : MulAut S), (b : MulAut S)⁆ : ↥suzT) : Equiv.Perm (Fin 1782)) ∈ suzM
      rw [map_commutatorElement]
      exact commutator_mem_suzM _ _
    exact h2 h1
  have hg2 : orderOf ((Φ z : ↥suzT) : Equiv.Perm (Fin 1782)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hz2]
  have hBM : ∀ x ∈ B, ((Φ x : ↥suzT) : Equiv.Perm (Fin 1782)) ∈ suzM := fun x hx =>
    (suzAutIso_mem_iff θ x).1 (hBinn hx)
  obtain ⟨cc, hcc, hcase⟩ := suzM_involution_class hzM hg2
  rcases hcase with hcc0 | hcc1
  ·
    exfalso
    have hsub : (B.map Φ.toMonoidHom).map suzT.subtype ≤
        centM ((Φ z : ↥suzT) : Equiv.Perm (Fin 1782)) := by
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, hBM x hx⟩
      have h := Subgroup.mem_centralizer_singleton_iff.1 (hBz hx)
      exact congrArg Subtype.val (by rw [← map_mul, ← map_mul, h] : Φ x * Φ z = Φ z * Φ x)
    have h27 : 3 ^ 3 ∣ Nat.card (centM ((Φ z : ↥suzT) : Equiv.Perm (Fin 1782))) := by
      have h1 := Subgroup.card_dvd_of_le hsub
      rwa [Subgroup.card_map_of_injective suzT.subtype_injective,
        Subgroup.card_map_of_injective Φ.injective, hBc'] at h1
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -, -, -, -, h16, -, -, -, -⟩ :=
      CTUC_Suz_four_exact_involution_centralizers
    have hcard : Nat.card (centM (suzInv 0)) = 161280 := by
      rw [← (h11 0 (by norm_num)).2]
      exact h16
    rw [← hcc0, ← Nat.card_congr
      (CFSG.EvenSporadicStandard.SuzOuter.centM_conj_equiv hcc (suzInv 0)).toEquiv, hcard] at h27
    norm_num at h27
  ·
    set cT : ↥suzT := ⟨cc, hcc⟩ with hcT
    let e : MulAut S ≃* ↥suzT := Φ.trans (MulAut.conj cT⁻¹)
    have hez : e z = suzT1 := by
      apply Subtype.ext
      have h : cc * suzInv 1 * cc⁻¹ = ((Φ z : ↥suzT) : Equiv.Perm (Fin 1782)) := hcc1
      show (cc : Equiv.Perm (Fin 1782))⁻¹ * ((Φ z : ↥suzT) : Equiv.Perm (Fin 1782)) *
        ((cc : Equiv.Perm (Fin 1782))⁻¹)⁻¹ = suzInv 1
      rw [← h]
      group
    have D : TwoCentralData 3 (e z) suzQT := by
      rw [hez]
      exact twoCentralData_suz hU
    have D' := TwoCentralData.comap e D
    exact index_four_core D' (by norm_num) hBe' hBc' hyB hy1 hR0e hR0c' hzR0 hzc
      (fun r hr => (Subgroup.mem_centralizer_singleton_iff.1 (hR0y hr)).symm) hKB hR1 hKB1 h01

end Row

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
