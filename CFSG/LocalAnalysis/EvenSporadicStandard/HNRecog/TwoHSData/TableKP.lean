module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableK
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongrK
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableISpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem map_zpowers_sup_eq :
    (zpowers pA ⊔ zpowers pZ).map P1408.subtype =
      closure ({elemA, elemZ} : Set (Equiv.Perm (Fin 1408))) := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure,
    Subgroup.zpowers_eq_closure, ← Subgroup.closure_union, Set.insert_eq]
  rfl

theorem two_mul_le_of_dvd_of_lt {n N : ℕ} (hdvd : n ∣ N) (hlt : n < N) : 2 * n ≤ N := by
  obtain ⟨m, rfl⟩ := hdvd
  rcases m with _ | _ | m
  · simp at hlt
  · simp at hlt
  · nlinarith

variable {E_P : Subgroup ↥P1408}

theorem map_inf_centralizer_eq
    (hE : ∀ x : ↥P1408, x ∈ E_P ↔ (x : Equiv.Perm (Fin 1408)) ∈ blocks1408) :
    (E_P ⊓ centralizer ({pZ} : Set ↥P1408)).map P1408.subtype = kSub1408 := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.coe_subtype, mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨x, ⟨hxE, hxc⟩, rfl⟩
    exact ⟨⟨x.2, congrArg Subtype.val hxc⟩, (hE x).1 hxE⟩
  · rintro ⟨⟨hgP, hgc⟩, hgb⟩
    exact ⟨⟨g, hgP⟩, ⟨(hE _).2 hgb, Subtype.ext hgc⟩, rfl⟩

section Cert


theorem K_shape_P (hP : Nat.card ↥P1408 = 177408000)
    (hE : ∀ x : ↥P1408, x ∈ E_P ↔ (x : Equiv.Perm (Fin 1408)) ∈ blocks1408) :
    IsShapeK ↥(E_P ⊓ centralizer ({pZ} : Set ↥P1408)) := by
  have hmap := map_inf_centralizer_eq hE
  exact IsShapeK.of_mulEquiv
    ((Subgroup.equivMapOfInjective (E_P ⊓ centralizer ({pZ} : Set ↥P1408)) P1408.subtype
      (Subgroup.subtype_injective P1408)).trans (MulEquiv.subgroupCongr hmap)).symm
    (tableKFacts_of hP).shape


theorem center_K_P (hP : Nat.card ↥P1408 = 177408000)
    (hE : ∀ x : ↥P1408, x ∈ E_P ↔ (x : Equiv.Perm (Fin 1408)) ∈ blocks1408)
    (g : ↥(E_P ⊓ centralizer ({pZ} : Set ↥P1408))) :
    g ∈ center ↥(E_P ⊓ centralizer ({pZ} : Set ↥P1408)) ↔
      (g : ↥P1408) ∈ zpowers pA ⊔ zpowers pZ := by
  have hmap := map_inf_centralizer_eq hE
  have hbasic := twoHSBasic_spec
  constructor
  · intro hg
    have hy : ((g : ↥P1408) : Equiv.Perm (Fin 1408)) ∈ kSub1408 := by
      rw [← hmap]
      exact Subgroup.mem_map.2 ⟨(g : ↥P1408), g.2, rfl⟩
    have hcomm : ∀ h ∈ kSub1408, ((g : ↥P1408) : Equiv.Perm (Fin 1408)) * h =
        h * ((g : ↥P1408) : Equiv.Perm (Fin 1408)) := by
      intro h hh
      rw [← hmap] at hh
      obtain ⟨k, hkK, hkw⟩ := Subgroup.mem_map.1 hh
      have := congrArg (fun x : ↥(E_P ⊓ centralizer ({pZ} : Set ↥P1408)) =>
        ((x : ↥P1408) : Equiv.Perm (Fin 1408))) (Subgroup.mem_center_iff.1 hg ⟨k, hkK⟩)
      simp only [Subgroup.coe_mul, Subgroup.coe_subtype] at this hkw
      rw [← hkw]
      exact this.symm
    have hmem := (tableKFacts_of hP).center _ hy hcomm
    rw [← map_zpowers_sup_eq] at hmem
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 hmem
    have : x = (g : ↥P1408) := Subtype.ext hxg
    rw [← this]
    exact hx
  · intro hg
    have hpAE : pA ∈ E_P := (hE pA).2 hbasic.2.2.2.2.2.1
    have hpZE : pZ ∈ E_P := (hE pZ).2 hbasic.2.2.2.2.2.2.1
    have hcentA : ∀ x : ↥P1408, pA * x = x * pA := fun x => Subtype.ext (elemA_comm x.2)
    have hpAc : pA ∈ centralizer ({pZ} : Set ↥P1408) := by
      rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hcentA pZ).symm
    have hpZc : pZ ∈ centralizer ({pZ} : Set ↥P1408) := by
      rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
    let K : Subgroup ↥P1408 := E_P ⊓ centralizer ({pZ} : Set ↥P1408)
    have hAV : pA ∈ (center ↥K).map K.subtype := by
      refine Subgroup.mem_map.2 ⟨⟨pA, Subgroup.mem_inf.2 ⟨hpAE, hpAc⟩⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (hcentA k).symm
    have hZV : pZ ∈ (center ↥K).map K.subtype := by
      refine Subgroup.mem_map.2 ⟨⟨pZ, Subgroup.mem_inf.2 ⟨hpZE, hpZc⟩⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (mem_centralizer_iff.1 (Subgroup.mem_inf.1 k.2).2 pZ rfl).symm
    have hsup : zpowers pA ⊔ zpowers pZ ≤ (center ↥K).map K.subtype :=
      sup_le (Subgroup.zpowers_le.2 hAV) (Subgroup.zpowers_le.2 hZV)
    obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.1 (hsup hg)
    have hcg' : c = g := Subtype.ext hcg
    rw [← hcg']
    exact hc

end Cert

end CFSG.EvenSporadicStandard.HNRecog
