module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Solomon

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG.Open CFSG.EvenSporadicStandard

private theorem socle_alt6_not_comm : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hnc : ¬ IsMulCommutative (alternatingGroup (Fin 6)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    simp
  exact hnc ⟨⟨fun a b => hcon a b⟩⟩

private theorem socle_complement_of_injective {C : Type*} [Group C] (N : Subgroup C) [N.Normal]
    (hinj : Function.Injective (QuotientGroup.mk' N)) (A : Subgroup C) (w : C)
    (hw : orderOf w = 2) (hwA : w ∉ A) (hidx : ∀ c : C, c ∈ A ∨ c * w ∈ A) :
    ∃ U : Subgroup (C ⧸ N), Disjoint U (zpowers (QuotientGroup.mk' N w)) ∧
      U ⊔ zpowers (QuotientGroup.mk' N w) = ⊤ := by
  refine ⟨A.map (QuotientGroup.mk' N), ?_, ?_⟩
  · rw [Subgroup.disjoint_def]
    intro x hxU hxz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hxU
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxz
    have hn' : QuotientGroup.mk' N (w ^ n) = QuotientGroup.mk' N c := (map_zpow _ w n).trans hn
    have hcn : c = w ^ n := hinj hn'.symm
    have hmod : w ^ (n % 2) = w ^ n := by
      simpa [hw] using zpow_mod_orderOf w n
    rcases Int.emod_two_eq_zero_or_one n with h0 | h1
    · rw [h0, zpow_zero] at hmod
      rw [hcn, ← hmod, map_one]
    · exfalso
      rw [h1, zpow_one] at hmod
      apply hwA
      rw [hmod, ← hcn]
      exact hc
  · rw [eq_top_iff]
    intro y _
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective N y
    rcases hidx c with hc | hc
    · exact Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ hc)
    · have hmem : QuotientGroup.mk' N (c * w) ∈ A.map (QuotientGroup.mk' N) :=
        Subgroup.mem_map_of_mem _ hc
      have hwinv : (QuotientGroup.mk' N w)⁻¹ ∈ zpowers (QuotientGroup.mk' N w) :=
        inv_mem (Subgroup.mem_zpowers _)
      have heq : QuotientGroup.mk' N c =
          QuotientGroup.mk' N (c * w) * (QuotientGroup.mk' N w)⁻¹ := by
        rw [map_mul, mul_assoc, mul_inv_cancel, mul_one]
      rw [heq]
      exact mul_mem (Subgroup.mem_sup_left hmem) (Subgroup.mem_sup_right hwinv)

theorem perfect_le_socle {K : Type} [Group K] [Finite K] (S : Subgroup K) [S.Normal]
    (hC : centralizer (S : Set K) = ⊥)
    (hsolv : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥S))
    (D : Subgroup K) (hD : Nonempty (↥D ≃* alternatingGroup (Fin 6))) : D ≤ S := by
  obtain ⟨e⟩ := hD
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup ↥D := e.isSimpleGroup
  let φ : K →* CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥S :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥S)).comp
      (MulAut.conjNormal (H := S))
  let ψ : ↥D →* CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥S := φ.comp D.subtype
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with hker | hker
  ·
    exfalso
    have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hker
    haveI : Group.IsSolvable ↥D := Group.isSolvable_of_isSolvable_injective hinj
    have hcomm : ∀ a b : ↥D, a * b = b * a :=
      IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance
    obtain ⟨a, b, hab⟩ := socle_alt6_not_comm
    apply hab
    have h := congrArg e (hcomm (e.symm a) (e.symm b))
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h
  ·
    intro d hd
    have hdker : (⟨d, hd⟩ : ↥D) ∈ ψ.ker := by
      rw [hker]
      exact Subgroup.mem_top _
    have h1 : QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥S)
        (MulAut.conjNormal (H := S) d) = 1 := MonoidHom.mem_ker.mp hdker
    have hinner : MulAut.conjNormal (H := S) d ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner ↥S :=
      (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨s, hs⟩ := hinner
    have hcent : (s : K)⁻¹ * d ∈ centralizer (S : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hx := congrArg (fun f : MulAut ↥S => ((f ⟨h, hh⟩ : ↥S) : K)) hs
      simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at hx
      calc h * ((s : K)⁻¹ * d) = (s : K)⁻¹ * ((s : K) * h * (s : K)⁻¹) * d := by group
        _ = (s : K)⁻¹ * (d * h * d⁻¹) * d := by rw [hx]
        _ = (s : K)⁻¹ * d * h := by group
    rw [hC, Subgroup.mem_bot] at hcent
    have hds : (s : K) = d := inv_mul_eq_one.mp hcent
    rw [← hds]
    exact s.2

theorem m10_complement {K : Type} [Group K] [Finite K] (S : Subgroup K) [S.Normal] {z : K}
    (hz : orderOf z = 2) (hfc : fusionOddCore ↥(centralizer ({z} : Set K)) = ⊥) (hzS : z ∉ S)
    (hidx : ∀ k : K, k ∈ S ∨ k * z ∈ S) :
    ∃ U : Subgroup (↥(centralizer ({z} : Set K)) ⧸ fusionOddCore ↥(centralizer ({z} : Set K))),
      Disjoint U (zpowers (Fin76b.zbarC K z)) ∧ U ⊔ zpowers (Fin76b.zbarC K z) = ⊤ := by
  have hinj : Function.Injective
      (QuotientGroup.mk' (fusionOddCore ↥(centralizer ({z} : Set K)))) :=
    (MonoidHom.ker_eq_bot_iff
      (QuotientGroup.mk' (fusionOddCore ↥(centralizer ({z} : Set K))))).mp
      (by rw [QuotientGroup.ker_mk', hfc])
  have hzC : z ∈ centralizer ({z} : Set K) := mem_centralizer_singleton_iff.2 rfl
  have hw : orderOf (⟨z, hzC⟩ : ↥(centralizer ({z} : Set K))) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hz
  have hwA : (⟨z, hzC⟩ : ↥(centralizer ({z} : Set K))) ∉
      S.subgroupOf (centralizer ({z} : Set K)) :=
    fun h => hzS (Subgroup.mem_subgroupOf.mp h)
  have hidx' : ∀ c : ↥(centralizer ({z} : Set K)),
      c ∈ S.subgroupOf (centralizer ({z} : Set K)) ∨
        c * ⟨z, hzC⟩ ∈ S.subgroupOf (centralizer ({z} : Set K)) := by
    intro c
    rcases hidx (c : K) with h | h
    · exact Or.inl (Subgroup.mem_subgroupOf.mpr h)
    · exact Or.inr (Subgroup.mem_subgroupOf.mpr h)
  exact socle_complement_of_injective (fusionOddCore ↥(centralizer ({z} : Set K))) hinj
    (S.subgroupOf (centralizer ({z} : Set K))) ⟨z, hzC⟩ hw hwA hidx'

end CFSG.ComponentClassification.CatFC
