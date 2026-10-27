module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic
public import CFSG.LocalAnalysis.ComponentInitial.StandardBasics
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.GroupTheory.CentralizerMap

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open CFSG.Open (standardComponentIsStandard)

variable {G : Type} [Group G]

@[expose] def ComponentAtCentralInvolutions (X : Subgroup G) : Prop :=
  ∀ x : G, orderOf x = 2 → x ∈ centralizer (X : Set G) →
    IsComponentIn X (centralizer ({x} : Set G))

private theorem centralizer_map_conj (X : Subgroup G) (g : G) :
    (Subgroup.centralizer (X : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  apply le_antisymm
  · exact Subgroup.map_centralizer_le_centralizer_image (X : Set G)
      (MulAut.conj g).toMonoidHom
  · intro y hy
    rw [Subgroup.mem_map]
    refine ⟨(MulAut.conj g).symm y, ?_, MulEquiv.apply_symm_apply (MulAut.conj g) y⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : MulAut.conj g x ∈ X.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
    have hcomm := (Subgroup.mem_centralizer_iff.mp hy) (MulAut.conj g x) hx'
    have h := congrArg (MulAut.conj g).symm hcomm
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h
    exact h

private theorem componentAtCentralInvolutions_conj {X : Subgroup G}
    (h2 : ComponentAtCentralInvolutions X) (g : G) :
    ComponentAtCentralInvolutions (X.map (MulAut.conj g).toMonoidHom) := by
  intro t' ht'2 ht'C
  let t : G := (MulAut.conj g).symm t'
  have ht_eq : MulAut.conj g t = t' := MulEquiv.apply_symm_apply (MulAut.conj g) t'
  have ht2 : orderOf t = 2 := by
    rw [← MulEquiv.orderOf_eq (MulAut.conj g) t, ht_eq, ht'2]
  have htC : t ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at ht'C ⊢
    intro x hx
    have hx' : MulAut.conj g x ∈ X.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
    have hcomm := ht'C (MulAut.conj g x) hx'
    have h := congrArg (MulAut.conj g).symm hcomm
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h
    exact h
  have hm := IsComponentIn.map_mulEquiv (h2 t ht2 htC) (MulAut.conj g)
  rw [CFSG.centralizer_singleton_map, ht_eq] at hm
  exact hm

private theorem conj_eq_self_of_involution_mem_centralizers [Finite G] {X : Subgroup G}
    (h2 : ComponentAtCentralInvolutions X)
    (h4 : ∀ g : G, ⁅X, X.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    {g t : G} (ht2 : orderOf t = 2)
    (htC : t ∈ Subgroup.centralizer (X : Set G))
    (htCg : t ∈ (Subgroup.centralizer (X : Set G)).map (MulAut.conj g).toMonoidHom) :
    X.map (MulAut.conj g).toMonoidHom = X := by
  have hXcomp : IsComponentIn X (Subgroup.centralizer ({t} : Set G)) := h2 t ht2 htC
  have htC' : t ∈ Subgroup.centralizer
      ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    rw [centralizer_map_conj X g] at htCg
    exact htCg
  have hXgcomp : IsComponentIn (X.map (MulAut.conj g).toMonoidHom)
      (Subgroup.centralizer ({t} : Set G)) :=
    componentAtCentralInvolutions_conj h2 g t ht2 htC'
  by_contra hne
  have hne' : X ≠ X.map (MulAut.conj g).toMonoidHom := fun h => hne h.symm
  have hcomm := IsComponentIn.commute_of_ne hXcomp hXgcomp hne'
  have hbot : ⁅X, X.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hcomm a ha b hb).symm
  exact h4 g hbot

theorem isQuasisimple_of_standard {X : Subgroup G} (hX : standardComponentIsStandard X) :
    IsQuasisimple X := by
  obtain ⟨hq, -⟩ := hX
  exact (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native X).1 hq

theorem exists_involution_of_standard [Finite G] {X : Subgroup G}
    (hX : standardComponentIsStandard X) :
    ∃ t : G, orderOf t = 2 ∧ t ∈ centralizer (X : Set G) := by
  obtain ⟨-, hev, -⟩ := hX
  have hdvd : 2 ∣ Nat.card ↥(Subgroup.centralizer (X : Set G)) := even_iff_two_dvd.mp hev
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht2⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.centralizer (X : Set G))) 2 hdvd
  exact ⟨(t : G), by rw [Subgroup.orderOf_coe, ht2], t.2⟩

theorem componentAtCentralInvolutions_of_standard [Finite G] {X : Subgroup G}
    (hX : standardComponentIsStandard X) : ComponentAtCentralInvolutions X := by
  intro x hx2 hxC
  obtain ⟨-, hLT, hnorm, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hX hxC hx2
  exact isComponentIn_of_normal hLT (isQuasisimple_of_standard hX) hnorm

theorem inC_of_standard [Finite G] {X : Subgroup G} (hX : standardComponentIsStandard X) :
    InC X := by
  obtain ⟨t, ht2, htC⟩ := exists_involution_of_standard hX
  exact ⟨t, ht2, componentAtCentralInvolutions_of_standard hX t ht2 htC⟩

theorem standard_of_componentAtCentralInvolutions [Finite G] {X : Subgroup G} (hX : InC X)
    (h2 : ComponentAtCentralInvolutions X)
    (h4 : ∀ g : G, ⁅X, X.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    standardComponentIsStandard X := by
  obtain ⟨x₀, hx₀2, hcomp₀⟩ := hX
  have hq : CFSG.Open.IsQuasisimple X :=
    (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native X).2
      (IsComponentIn.isQuasisimple hcomp₀)
  have hx₀C : x₀ ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (IsComponentIn.le hcomp₀ hy) x₀
      (Set.mem_singleton x₀)).symm
  have hev : Even (Nat.card ↥(Subgroup.centralizer (X : Set G))) := by
    have hdvd : orderOf x₀ ∣ Nat.card ↥(Subgroup.centralizer (X : Set G)) :=
      Subgroup.orderOf_dvd_natCard _ hx₀C
    rw [hx₀2] at hdvd
    exact even_iff_two_dvd.mpr hdvd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t₀, ht₀2⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.centralizer (X : Set G))) 2 (even_iff_two_dvd.mp hev)
  have htight : ∀ g : G, g ∉ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) →
      Odd (Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓
        (Subgroup.centralizer (X : Set G)).map (MulAut.conj g).toMonoidHom)) := by
    intro g hg
    rcases Nat.even_or_odd (Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓
        (Subgroup.centralizer (X : Set G)).map (MulAut.conj g).toMonoidHom)) with h | h
    · exfalso
      obtain ⟨t, ht2⟩ := exists_prime_orderOf_dvd_card'
        (G := ↥(Subgroup.centralizer (X : Set G) ⊓
          (Subgroup.centralizer (X : Set G)).map (MulAut.conj g).toMonoidHom)) 2
        (even_iff_two_dvd.mp h)
      have ht2G : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe, ht2]
      have hXeq : X.map (MulAut.conj g).toMonoidHom = X :=
        conj_eq_self_of_involution_mem_centralizers h2 h4 ht2G t.2.1 t.2.2
      have hCeq : (Subgroup.centralizer (X : Set G)).map (MulAut.conj g).toMonoidHom
          = Subgroup.centralizer (X : Set G) := by
        have := centralizer_map_conj X g
        rw [hXeq] at this
        exact this
      exact hg (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hCeq)
    · exact h
  have hnorm : Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) =
      Subgroup.normalizer (X : Set G) := by
    apply le_antisymm
    · intro g hg
      have hCg : (Subgroup.centralizer (X : Set G)).map (MulAut.conj g).toMonoidHom
          = Subgroup.centralizer (X : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
      let t : G := MulAut.conj g (t₀ : G)
      have ht2 : orderOf t = 2 := by
        show orderOf (MulAut.conj g (t₀ : G)) = 2
        rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, ht₀2]
      have htCg_map : t ∈ (Subgroup.centralizer (X : Set G)).map
          (MulAut.conj g).toMonoidHom := ⟨(t₀ : G), t₀.2, rfl⟩
      have htC : t ∈ Subgroup.centralizer (X : Set G) := by
        rw [hCg] at htCg_map
        exact htCg_map
      have hXeq : X.map (MulAut.conj g).toMonoidHom = X :=
        conj_eq_self_of_involution_mem_centralizers h2 h4 ht2 htC htCg_map
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hXeq
    · intro g hg
      have hXg : X.map (MulAut.conj g).toMonoidHom = X :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
      have hCg : (Subgroup.centralizer (X : Set G)).map (MulAut.conj g).toMonoidHom
          = Subgroup.centralizer (X : Set G) := by
        have := centralizer_map_conj X g
        rw [hXg] at this
        exact this
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hCg
  exact ⟨hq, hev, htight, hnorm, h4⟩

end CFSG.OddStandard.SmallF3.Omega
