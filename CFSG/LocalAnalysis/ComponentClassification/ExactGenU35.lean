module

public import CFSG.LocalAnalysis.ComponentClassification.ExactGenLift
public import CFSG.LocalAnalysis.ComponentClassification.ExactGenAut
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions
public import CFSG.RankThree.PartOne.HNB.UnitaryBridge
public import Certificates.Certificate34002

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2

open CFSG.RankThree.PartOne.HNB CFSG.Open.StatedSUFieldChange CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.Monster.B.Co2 HNUnitaryBridge


theorem getElem!_extract_zero {α : Type*} [Inhabited α] (a : Array α) {i k : ℕ} (hi : i < k)
    (hk : k ≤ a.size) : (a.extract 0 k)[i]! = a[i]! := by
  rw [getElem!_pos _ i (by simp; omega), getElem!_pos _ i (by omega), Array.getElem_extract]
  simp

theorem nonempty_mulEquiv_psu3_subgroup
    {I : Subgroup (Equiv.Perm (Fin 50))} (g : Fin 6 → I) (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hρ : ∀ (k : Fin 6) (x : Fin 50), (I.subtype (g k) x : ℕ) = (smallPerms[(k : ℕ)]!)[(x : ℕ)]!)
    (hcard : Nat.card I = 126000) : Nonempty (I ≃* PSU3) :=
  nonempty_mulEquiv_psu3 g hgen I.subtype I.subtype_injective hρ hcard

theorem exactCore_U35 (S : Type) [Group S] [Finite S] (h : Blueprint.LieModel S .PSU 3 5 1) :
    ExactCore S := by
  have hB : StatedClassicalModel S .PSU 3 5 1 :=
    Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  have hc : ExactFin.u35FCCheck () = true := Certificates.certificate34002
  simp only [ExactFin.u35FCCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hok, hk6⟩, hS6⟩, hordP⟩, hordN⟩ := hc
  obtain ⟨hP, hN, -, -, -, hcP, -⟩ := ExactFin.Ctx.sound 50 _ ((ExactFin.u35FC ()).ctx_ok 50 hok)
  have hsz : 6 ≤ (ExactFin.u35FC ()).ctx.chP.S.size := hk6 ▸ ExactFin.ChainData.k_le_size 50 hP
  have hSi : ∀ i < 6, (ExactFin.u35FC ()).ctx.chP.S[i]! = smallPerms[i]! := by
    intro i hi
    exact (getElem!_extract_zero _ hi (by omega)).symm.trans (congrArg (fun a => a[i]!) hS6)
  let I : Subgroup (Equiv.Perm (Fin 50)) := (ExactFin.u35FC ()).ctx.chP.sub 50
  let g : Fin 6 → I := fun k => ⟨permOfArr 50 (ExactFin.u35FC ()).ctx.chP.S[(k : ℕ)]!,
    Subgroup.subset_closure ⟨k, by omega, rfl⟩⟩
  have hgen : Subgroup.closure (Set.range g) = ⊤ := by
    apply Subgroup.map_injective I.subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have himg : (I.subtype '' Set.range g : Set (Equiv.Perm (Fin 50))) =
        {x | ∃ i < (ExactFin.u35FC ()).ctx.chP.k, x = permOfArr 50
          (ExactFin.u35FC ()).ctx.chP.S[i]!} := by
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
    have h2 : ((ExactFin.u35FC ()).ctx.chP.S[(k : ℕ)]!)[(x : ℕ)]! = (smallPerms[(k : ℕ)]!)[(x : ℕ)]! :=
      congrArg (fun a => a[(x : ℕ)]!) (hSi k k.2)
    have e : I.subtype (g k) = (ExactFin.u35FC ()).ctx.chP.gs 50 (k : ℕ) := rfl
    exact (congrArg (fun p : Equiv.Perm (Fin 50) => (p x : ℕ)) e).trans ((hrep x).symm.trans h2)
  have hcardI : Nat.card I = 126000 := by
    change Nat.card ((ExactFin.u35FC ()).ctx.chP.sub 50) = _
    rw [hcP, hordP]
  obtain ⟨eI⟩ := nonempty_mulEquiv_psu3_subgroup g hgen hρ hcardI
  obtain ⟨hB1, hB2, -⟩ := CFSG.RankThree.Classical.unitary_three_five_model S hB
  have hOut := (LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound S 3 5 1 hB).2.2.1
  obtain ⟨-, K, _, _, hK, ⟨eS⟩⟩ := hB
  haveI : Fintype K := Fintype.ofFinite K
  have hKK : Fintype.card K = Fintype.card F25 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, F25.card]
    norm_num
  let eK : K ≃+* F25 := FiniteField.ringEquivOfCardEq hKK
  have eSI : S ≃* I := eS.trans ((statedProjSUEquiv eK 3 (5 ^ 1)).trans eI.symm)
  have hout : (Nat.card (Outer S)).factorization 2 ≤ 1 := by
    rw [hOut]
    norm_num [Nat.factorization_def _ Nat.prime_two]
    decide +kernel
  have hk : 1 + ((ExactFin.u35FC ()).ctx.chP.order 50).factorization 2 ≤
      ((ExactFin.u35FC ()).ctx.chN.order 50).factorization 2 := by
    rw [hordP, hordN, Nat.factorization_def _ Nat.prime_two, Nat.factorization_def _ Nat.prime_two]
    decide +kernel
  exact ExactFin.coreStmt_of_model 50 (ExactFin.u35FC ()) hok eSI hB2.commutator_eq_top hout hk

end CFSG.ComponentClassification.SolMax.SwapP2
