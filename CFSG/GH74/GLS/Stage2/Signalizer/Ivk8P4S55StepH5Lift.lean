module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrLift
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrPerf
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Cross

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

section Cover

theorem exists_perfect_map_eq {A B : Type*} [Group A] [Finite A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) (L : Subgroup B) (hL : ⁅L, L⁆ = L) :
    ∃ N : Subgroup A, N ≤ L.comap f ∧ N.map f = L ∧ ⁅N, N⁆ = N := by
  classical
  have hne : ∃ n, ∃ N : Subgroup A, N ≤ L.comap f ∧ N.map f = L ∧ Nat.card N = n :=
    ⟨_, L.comap f, le_rfl, Subgroup.map_comap_eq_self_of_surjective hf L, rfl⟩
  obtain ⟨N, hNle, hNmap, hNcard⟩ := Nat.find_spec hne
  refine ⟨N, hNle, hNmap, ?_⟩
  have h1 : ⁅N, N⁆ ≤ N := by
    simpa only [sup_idem] using Subgroup.commutator_le_sup N N
  have hmin : Nat.find hne ≤ Nat.card ↥⁅N, N⁆ :=
    Nat.find_min' hne ⟨⁅N, N⁆, h1.trans hNle, by rw [Subgroup.map_commutator, hNmap, hL], rfl⟩
  rw [← hNcard] at hmin
  exact Subgroup.eq_of_le_of_card_ge h1 hmin

theorem map_perfCore_comap_of_perfect {A B : Type*} [Group A] [Finite A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) (L : Subgroup B) (hL : ⁅L, L⁆ = L) :
    (perfCore (L.comap f)).map f = L := by
  obtain ⟨N, hNle, hNmap, hNperf⟩ := exists_perfect_map_eq f hf L hL
  refine le_antisymm ((Subgroup.map_mono (perfCore_le _)).trans (Subgroup.map_comap_le f L)) ?_
  calc L = N.map f := hNmap.symm
    _ ≤ (perfCore (L.comap f)).map f := Subgroup.map_mono (le_perfCore hNle hNperf)

theorem exists_cover_quasisimple (K : Type*) [Group K] [Finite K] (L : Subgroup (K ⧸ center K))
    (hL : IsQuasisimple ↥L) :
    ∃ M : Subgroup K,
      (∀ x : K, (QuotientGroup.mk x : K ⧸ center K) ∈ normalizer (L : Set (K ⧸ center K)) →
        x ∈ normalizer (M : Set K)) ∧
      M.map (QuotientGroup.mk' (center K)) = L ∧ IsQuasisimple ↥M ∧
      Nonempty ((↥M ⧸ center ↥M) ≃* (↥L ⧸ center ↥L)) := by
  set ν : K →* K ⧸ center K := QuotientGroup.mk' (center K) with hν
  have hνs : Function.Surjective ν := QuotientGroup.mk'_surjective _
  have hLp : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hL.1
  set M : Subgroup K := perfCore (L.comap ν) with hMdef
  have hMp : ⁅M, M⁆ = M := commutator_perfCore _
  have hMmap : M.map ν = L := map_perfCore_comap_of_perfect ν hνs L hLp
  have hle : M ≤ L.comap ν := perfCore_le _
  let ρ : ↥M →* ↥L := (ν.comp M.subtype).codRestrict L (fun m => hle m.2)
  have hρs : Function.Surjective ρ := by
    intro l
    have hl : (l : K ⧸ center K) ∈ M.map ν := by rw [hMmap]; exact l.2
    obtain ⟨m, hm, hml⟩ := hl
    exact ⟨⟨m, hm⟩, Subtype.ext hml⟩
  have hker : ρ.ker ≤ center ↥M := by
    intro m hm
    have h1 : ν (m : K) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hm)
    have h2 : (m : K) ∈ center K := (QuotientGroup.eq_one_iff _).mp h1
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro g
    exact Subtype.ext (h2 g)
  have hMperf : Group.IsPerfect ↥M := Subgroup.isPerfect_iff.mpr hMp
  have hq : IsQuasisimple ↥M :=
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective hMperf ρ hρs hker).mpr hL
  have hcen : (center ↥L).comap ρ = center ↥M :=
    CFSG.LocalCores.comap_center_eq_of_perfect hMperf ρ hρs hker
  let Ψ : ↥M →* ↥L ⧸ center ↥L := (QuotientGroup.mk' (center ↥L)).comp ρ
  have hΨ : Function.Surjective Ψ := (QuotientGroup.mk'_surjective _).comp hρs
  have hΨker : center ↥M = Ψ.ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcen]
  exact ⟨M, fun x hx => mem_normalizer_perfCore (mem_normalizer_comap ν hx), hMmap, hq,
    ⟨(QuotientGroup.quotientMulEquivOfEq hΨker).trans
      (QuotientGroup.quotientKerEquivOfSurjective Ψ hΨ)⟩⟩

theorem quasisimple_map_subtype {Γ : Type*} [Group Γ] (K : Subgroup Γ) (M : Subgroup ↥K)
    (hM : IsQuasisimple ↥M) :
    IsQuasisimple ↥(M.map K.subtype) ∧
      Nonempty ((↥(M.map K.subtype) ⧸ center ↥(M.map K.subtype)) ≃* (↥M ⧸ center ↥M)) := by
  let e : ↥M ≃* ↥(M.map K.subtype) := M.equivMapOfInjective K.subtype K.subtype_injective
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hM, ?_⟩
  exact ⟨QuotientGroup.congr (center ↥(M.map K.subtype)) (center ↥M) e.symm
    (Subgroup.map_center_eq e.symm)⟩

end Cover

section Types

theorem OddChev.of_mulEquiv {r : ℕ} {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : OddChev r Y) : OddChev r Y' := by
  obtain ⟨hr, hr2, h⟩ := h
  refine ⟨hr, hr2, ?_⟩
  rcases h with ⟨f, hf, h⟩ | ⟨f, hf, h⟩ | ⟨f, hf, h⟩ | ⟨f, hf, h⟩ | ⟨f, hf, h⟩ | ⟨f, hf, h⟩ |
    ⟨f, hf, h8, h⟩ | ⟨f, hf, h8, h⟩ | ⟨h3, f, hf, h⟩
  · exact Or.inl ⟨f, hf, lieModel_of_mulEquiv e h⟩
  · exact Or.inr (Or.inl ⟨f, hf, lieModel_of_mulEquiv e h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, lieModel_of_mulEquiv e h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, lieModel_of_mulEquiv e h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, lieModel_of_mulEquiv e h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, lieModel_of_mulEquiv e h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨f, hf, h8, lieModel_of_mulEquiv e h⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨f, hf, h8, lieModel_of_mulEquiv e h⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨h3, f, hf, lieModel_of_mulEquiv e h⟩)))))))

end Types

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
