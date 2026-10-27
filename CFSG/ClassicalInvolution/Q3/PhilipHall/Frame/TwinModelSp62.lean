module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinModelSpCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentResModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinModel

open CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Balance

theorem field_two_elements {K : Type} [Field K] [Finite K] (h : Nat.card K = 2) (c : K) :
    c = 0 ∨ c = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  by_contra hc
  push Not at hc
  have h3 : ({0, 1, c} : Finset K).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨0, 1, c, zero_ne_one, hc.1.symm, hc.2.symm, rfl⟩
  have h' := Finset.card_le_univ ({0, 1, c} : Finset K)
  rw [h3, Fintype.card_eq_nat_card] at h'
  omega

theorem statedScalars_eq_bot {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (h : Nat.card K = 2) : StatedScalars ι K = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨c, rfl⟩
  have hc : (c : K) = 1 := (field_two_elements h c).resolve_left c.ne_zero
  have : c = 1 := Units.ext hc
  rw [this, map_one]
  exact Subgroup.one_mem _

noncomputable def statedProjEquiv {n : ℕ} {K : Type} [Field K] [Finite K] (h : Nat.card K = 2) :
    StatedProj (StatedSp n K) ≃* StatedSp n K :=
  (QuotientGroup.quotientMulEquivOfEq
    (by rw [statedScalars_eq_bot h, Subgroup.bot_subgroupOf] :
      (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) = ⊥)).trans
    QuotientGroup.quotientBot

theorem oddCoreIn_centralizer_eq_bot_of_equiv {n : ℕ} {K : Type} [Field K] [Finite K]
    (h : Nat.card K = 2) {Q : Type} [Group Q] [Finite Q] (f : Q ≃* StatedSp n K) {s : Q}
    (hs : orderOf s = 2) : oddCoreIn (Subgroup.centralizer ({s} : Set Q)) = ⊥ := by
  have hK := field_two_elements h
  have hs2 : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rw [hs, sq] at this
    exact this
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hs
    omega
  set ρ : Q →* Module.End K (Fin n ⊕ Fin n → K) := (natRep (StatedSp n K)).comp f.toMonoidHom
    with hρdef
  have hinj : Function.Injective ρ := (natRep_injective _).comp f.injective
  have hiso : IsIsometric (spForm n K) ρ := fun g u v => isIsometric_natRep_statedSp n K (f g) u v
  have htr : ∀ x : Fin n ⊕ Fin n → K, ∃ g : Q, IsTrans (spForm n K) ρ g x := by
    intro x
    obtain ⟨g, hg⟩ := exists_natRep_eq_of_isometry n K
      { toFun := fun v => v + (spForm n K).β x v • x
        map_add' := fun u v => by
          simp only [(spForm n K).add_right, add_smul]
          abel
        map_smul' := fun a v => by
          simp only [(spForm n K).smul_right, RingHom.id_apply, smul_add, smul_smul] }
      (fun u v => ((spForm n K).β_transvection rfl (spForm_self n K) x u v))
    refine ⟨f.symm g, fun v => ?_⟩
    simp only [hρdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact hg v
  have := Fintype.ofFinite Q
  exact le_bot_iff.mp (le_of_eq (eq_bot_of_normalized_odd (spForm_self n K) hK hiso hinj htr hs2 hs1
    (oddCoreIn (Subgroup.centralizer ({s} : Set Q)))
    (oddCoreIn_le _) (fun c hc x hx => conj_mem_oddCoreIn hc hx)
    (odd_card_oddCoreIn _)))

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinModel

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes

open CFSG.Assembly.LowTwoRank

theorem modelFactSp62 : ModelFactSp62 := by
  intro Q _ _ hQ s hs
  have hcl : StatedClassicalModel Q .PSp 3 2 1 := by
    rcases hQ with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hcl
    all_goals exact absurd h0 (by norm_num)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcl
  have hK2 : Nat.card K = 2 := by simpa using hK
  exact TwinModel.oddCoreIn_centralizer_eq_bot_of_equiv hK2
    (e.trans (TwinModel.statedProjEquiv hK2)) hs

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
