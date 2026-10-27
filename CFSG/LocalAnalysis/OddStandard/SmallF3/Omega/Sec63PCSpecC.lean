module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCSpecA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Pocket
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1CheckSpecD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.ComponentClassification.HarrisLit.P1 Certificates.Asc82Fbar

variable {n : ℕ}

theorem slList_complete : ∀ A : SL2F3, A ∈ slList () := by decide +kernel

theorem slCode_lt (A : SL2F3) : slCode A < 81 := by
  have h1 := ZMod.val_lt (A.1 0 0)
  have h2 := ZMod.val_lt (A.1 0 1)
  have h3 := ZMod.val_lt (A.1 1 0)
  have h4 := ZMod.val_lt (A.1 1 1)
  unfold slCode
  omega

theorem pocketOK_chain {sift : Table → Bool} {cap ord : ℕ} {gs : List Table} {t₂ : Table}
    {tg : Equiv.Perm (Fin n)} {rho : List Table} (hn : n < 2 ^ 32) (ht : Rep n t₂ tg)
    (hgs : ∀ g ∈ gs, inCOK n sift t₂ g = true) (henum : enumOK n cap ord gs = true)
    (h : pocketOK n cap gs t₂ rho = true) :
    ∃ K : Subgroup (Equiv.Perm (Fin n)), tg ∈ K ∧ K ≤ genOf n gs ∧
      (∀ k ∈ K, ∀ m ∈ genOf n gs, m * k * m⁻¹ ∈ K) ∧ IsSL23Mod ↥K := by
  have hgp : ∀ g ∈ gs, permOK n g = true := fun g hg => permOK_of_inCOK (hgs g hg)
  have hgc : ∀ c ∈ gs, permOK n c = true ∧ invOK n c (invT n c) = true :=
    fun g hg => ⟨permOK_of_inCOK (hgs g hg), invOK_of_inCOK (hgs g hg)⟩
  simp only [pocketOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hlen, hpr⟩, hhom⟩, hinj⟩, hany⟩, hmem⟩, hK24⟩, hnorm⟩ := h
  have hperm : ∀ A : SL2F3, permOK n (rhoT n rho A) = true := by
    intro A
    have hA : slCode A < rho.length := by rw [hlen]; exact slCode_lt A
    rw [rhoT, List.getD_eq_getElem _ _ hA]
    exact hpr _ (List.getElem_mem hA)
  have hrep : ∀ A : SL2F3, Rep n (rhoT n rho A) (tp n (rhoT n rho A)) := fun A => rep_tp (hperm A)
  have hmul : ∀ A B : SL2F3,
      tp n (rhoT n rho (A * B)) = tp n (rhoT n rho A) * tp n (rhoT n rho B) := by
    intro A B
    exact ((tblEq_iff_eq (Rep.compT (hrep A) (hrep B)) (hrep (A * B))).1
      (hhom A (slList_complete A) B (slList_complete B))).symm
  let ρ : SL2F3 →* Equiv.Perm (Fin n) := MonoidHom.mk' (fun A => tp n (rhoT n rho A)) hmul
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro A hA
    have h1 : tblEq n (rhoT n rho A) (idT n) = true :=
      (tblEq_idT_iff hn (hrep A)).2 hA
    rcases hinj A (slList_complete A) with h2 | h2
    · rw [h1] at h2
      exact absurd h2 (by decide)
    · exact h2
  obtain ⟨A₂, -, hA₂⟩ := hany
  have hA₂' : ρ A₂ = tg := (tblEq_iff_eq (hrep A₂) ht).1 hA₂
  have hKset : genOf n (slList ()|>.map (rhoT n rho)) = ρ.range := by
    rw [genOf, ← Subgroup.closure_eq ρ.range, MonoidHom.coe_range]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨A, -, rfl⟩ := List.mem_map.mp (by simpa using hx)
      exact ⟨A, rfl⟩
    · rintro ⟨A, rfl⟩
      exact ⟨rhoT n rho A, by simpa using List.mem_map_of_mem (slList_complete A), rfl⟩
  have hKM : ρ.range ≤ genOf n gs := by
    rintro _ ⟨A, rfl⟩
    exact tp_mem_genOf_of_memT hn hgp henum (hperm A)
      (hmem _ (List.mem_map_of_mem (slList_complete A)))
  have hN := normOK_spec hn (fun g hg => by
    obtain ⟨A, -, rfl⟩ := List.mem_map.mp hg
    exact hperm A) hK24 hgc hnorm
  rw [hKset] at hN
  refine ⟨ρ.range, ⟨A₂, hA₂'⟩, hKM, fun k hk m hm => ?_, ?_⟩
  · exact (mem_normalizer_iff.mp (hN hm) k).mp hk
  · exact isSL23Mod_of_mulEquiv (MonoidHom.ofInjective hρinj) isSL23Mod_sl2f3

end CFSG.OddStandard.SmallF3.Omega
