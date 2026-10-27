module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.U35Final
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.HNB.UnitaryBridge
public import Certificates.Certificate34002

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open CFSG.ComponentClassification.SolMax.SwapP2 CFSG.RankThree.PartOne.HNB
  CFSG.Open.StatedSUFieldChange CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.Monster.B.Co2 HNUnitaryBridge

noncomputable abbrev i50 : Subgroup (Equiv.Perm (Fin 50)) := (ExactFin.u35FC ()).ctx.chP.sub 50

private theorem nonempty_psu3_mulEquiv_of_chain
    [Fact (Nat.Prime 5)] (cd : ExactFin.ChainData) (hP : cd.check 50 = true) (hk6 : cd.k = 6)
    (hS6 : cd.S.extract 0 6 = smallPerms) (hcP : Nat.card (cd.sub 50) = cd.order 50)
    (hordP : cd.order 50 = 126000) : Nonempty (↥(CFSG.Open.PSU3 5 1) ≃* ↥(cd.sub 50)) := by
  have hB := CFSG.EvenSporadicStandard.HNRecog.Section3Model.psu3_five_statedClassicalModel
  have hsz : 6 ≤ cd.S.size := hk6 ▸ ExactFin.ChainData.k_le_size 50 hP
  have hSi : ∀ i < 6, cd.S[i]! = smallPerms[i]! := by
    intro i hi
    have h1 : (cd.S.extract 0 6)[i]! = cd.S[i]! := by
      rw [getElem!_pos _ i (by simp; omega), getElem!_pos _ i (by omega), Array.getElem_extract]
      simp
    rw [← h1, hS6]
  let I : Subgroup (Equiv.Perm (Fin 50)) := cd.sub 50
  let g : Fin 6 → I := fun k => ⟨permOfArr 50 cd.S[(k : ℕ)]!,
    Subgroup.subset_closure ⟨k, by omega, rfl⟩⟩
  have hgen : Subgroup.closure (Set.range g) = ⊤ := by
    apply Subgroup.map_injective I.subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have himg : (I.subtype '' Set.range g : Set (Equiv.Perm (Fin 50))) =
        {x | ∃ i < cd.k, x = permOfArr 50 cd.S[i]!} := by
      ext x
      constructor
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, by omega, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨g ⟨i, by omega⟩, ⟨_, rfl⟩, rfl⟩
    rw [himg]
    rfl
  have hρ : ∀ (k : Fin 6) (x : Fin 50),
      (I.subtype (g k) x : ℕ) = (smallPerms[(k : ℕ)]!)[(x : ℕ)]! := by
    intro k x
    have hrep := ExactFin.ChainData.rep_gs 50 hP (i := (k : ℕ)) (by omega)
    have := hrep x
    rw [hSi k k.2] at this
    exact this.symm
  have hcardI : Nat.card I = 126000 := by
    change Nat.card (cd.sub 50) = _
    rw [hcP, hordP]
  obtain ⟨eI⟩ := nonempty_mulEquiv_psu3 g hgen I.subtype I.subtype_injective hρ hcardI
  obtain ⟨-, K, _, _, hK, ⟨eS⟩⟩ := hB
  haveI : Fintype K := Fintype.ofFinite K
  have hKK : Fintype.card K = Fintype.card F25 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, F25.card]
    norm_num
  let eK : K ≃+* F25 := FiniteField.ringEquivOfCardEq hKK
  exact ⟨eS.trans ((statedProjSUEquiv eK 3 (5 ^ 1)).trans eI.symm)⟩

theorem nonempty_psu3_mulEquiv_i50
    [Fact (Nat.Prime 5)] : Nonempty (↥(CFSG.Open.PSU3 5 1) ≃* ↥i50) := by
  have hc : ExactFin.u35FCCheck () = true := Certificates.certificate34002
  simp only [ExactFin.u35FCCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hok, hk6⟩, hS6⟩, hordP⟩, -⟩ := hc
  obtain ⟨hP, -, -, -, -, hcP, -⟩ := ExactFin.Ctx.sound 50 _ ((ExactFin.u35FC ()).ctx_ok 50 hok)
  exact nonempty_psu3_mulEquiv_of_chain _ hP hk6 hS6 hcP hordP

theorem card_i50 : Nat.card i50 = 126000 := by
  have hc : ExactFin.u35FCCheck () = true := Certificates.certificate34002
  simp only [ExactFin.u35FCCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hok, -⟩, -⟩, hordP⟩, -⟩ := hc
  obtain ⟨-, -, -, -, -, hcP, -⟩ := ExactFin.Ctx.sound 50 _ ((ExactFin.u35FC ()).ctx_ok 50 hok)
  change Nat.card ((ExactFin.u35FC ()).ctx.chP.sub 50) = _
  rw [hcP, hordP]

theorem nonempty_mulEquiv_i50_of_le_range {U : Type*} [Group U]
    [Finite U] (ρ : U →* Equiv.Perm (Fin 50)) (hU : Nat.card U = 126000) (hle : i50 ≤ ρ.range) :
    Nonempty (U ≃* ↥i50) := by
  have hrange : Nat.card ρ.range ≤ Nat.card U :=
    Nat.card_le_card_of_surjective _ ρ.rangeRestrict_surjective
  have hge : Nat.card i50 ≤ Nat.card ρ.range := Subgroup.card_le_of_le hle
  rw [card_i50] at hge
  have heq : i50 = ρ.range := Subgroup.eq_of_le_of_card_ge hle (by rw [card_i50]; omega)
  have hbij : Function.Bijective ρ.rangeRestrict :=
    ρ.rangeRestrict_surjective.bijective_of_nat_card_le (by omega)
  exact ⟨(MulEquiv.ofBijective _ hbij).trans (MulEquiv.subgroupCongr heq.symm)⟩

private theorem exists_gens_of_chain (cd : ExactFin.ChainData) (hP : cd.check 50 = true)
    (hk6 : cd.k = 6) (hS6 : cd.S.extract 0 6 = smallPerms) :
    ∃ σ : Fin 6 → Equiv.Perm (Fin 50),
      (∀ (k : Fin 6) (x : Fin 50), (σ k x : ℕ) = (smallPerms[(k : ℕ)]!)[(x : ℕ)]!) ∧
        Subgroup.closure (Set.range σ) = cd.sub 50 := by
  have hsz : 6 ≤ cd.S.size := hk6 ▸ ExactFin.ChainData.k_le_size 50 hP
  have hSi : ∀ i < 6, cd.S[i]! = smallPerms[i]! := by
    intro i hi
    have h1 : (cd.S.extract 0 6)[i]! = cd.S[i]! := by
      rw [getElem!_pos _ i (by simp; omega), getElem!_pos _ i (by omega), Array.getElem_extract]
      simp
    rw [← h1, hS6]
  refine ⟨fun k => permOfArr 50 cd.S[(k : ℕ)]!, fun k x => ?_, ?_⟩
  · have hrep := ExactFin.ChainData.rep_gs 50 hP (i := (k : ℕ)) (by omega)
    have := hrep x
    rw [hSi k k.2] at this
    exact this.symm
  · change Subgroup.closure _ = Subgroup.closure {g | ∃ i < cd.k, g = permOfArr 50 cd.S[i]!}
    congr 1
    ext g
    simp only [Set.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, by omega⟩, rfl⟩

theorem exists_gens_i50 :
    ∃ σ : Fin 6 → Equiv.Perm (Fin 50),
      (∀ (k : Fin 6) (x : Fin 50), (σ k x : ℕ) = (smallPerms[(k : ℕ)]!)[(x : ℕ)]!) ∧
        Subgroup.closure (Set.range σ) = i50 := by
  have hc : ExactFin.u35FCCheck () = true := Certificates.certificate34002
  simp only [ExactFin.u35FCCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hok, hk6⟩, hS6⟩, -⟩, -⟩ := hc
  obtain ⟨hP, -, -, -, -, -, -⟩ := ExactFin.Ctx.sound 50 _ ((ExactFin.u35FC ()).ctx_ok 50 hok)
  exact exists_gens_of_chain _ hP hk6 hS6

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
