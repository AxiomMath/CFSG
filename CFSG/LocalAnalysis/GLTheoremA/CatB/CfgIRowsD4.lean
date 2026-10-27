module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgIMain
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.CfgI

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremA
open CFSG.ClassicalGroups.Orthogonal

section Model

variable (F : Type) [Field F]

@[expose] def wOf (x : (Fin 3 → F) × (Fin 3 → F)) : Fin 4 ⊕ Fin 4 → F
  | .inl i => Fin.cases 0 x.1 i
  | .inr i => Fin.cases 0 x.2 i

theorem wOf_add (x y : (Fin 3 → F) × (Fin 3 → F)) : wOf F (x + y) = wOf F x + wOf F y := by
  funext k
  rcases k with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp [wOf]

theorem wOf_zero : wOf F 0 = 0 := by
  funext k
  rcases k with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp [wOf]

@[expose] def uE : Fin 4 ⊕ Fin 4 → F := Pi.single (Sum.inl 0) 1

theorem uE_singular : CFSG.LieType.Universal.Spin.quadPlus 4 F (uE F) = 0 := by
  rw [CFSG.LieType.Universal.Spin.quadPlus_apply]
  simp [uE, Pi.single_apply]

theorem polar_uE_wOf (x : (Fin 3 → F) × (Fin 3 → F)) :
    QuadraticMap.polar (CFSG.LieType.Universal.Spin.quadPlus 4 F) (uE F) (wOf F x) = 0 := by
  rw [CFSG.LieType.Universal.Spin.polar_quadPlus, Fin.sum_univ_four]
  simp [uE, wOf, Pi.single_apply]

@[expose] noncomputable def psiW : Multiplicative ((Fin 3 → F) × (Fin 3 → F)) →*
    elementaryGroup (CFSG.LieType.Universal.Spin.quadPlus 4 F) where
  toFun x := ⟨eichler _ (uE F) (wOf F (Multiplicative.toAdd x)),
    eichler_mem_elementaryGroup _ _ _⟩
  map_one' := Subtype.ext (by
    show eichler _ (uE F) (wOf F 0) = 1
    rw [wOf_zero, eichler_zero_right])
  map_mul' x y := Subtype.ext (by
    show eichler _ (uE F) (wOf F (Multiplicative.toAdd x + Multiplicative.toAdd y)) =
      eichler _ (uE F) (wOf F (Multiplicative.toAdd x)) *
        eichler _ (uE F) (wOf F (Multiplicative.toAdd y))
    rw [eichler_mul (polar_uE_wOf F _) (polar_uE_wOf F _), wOf_add])

theorem polar_f0_uE :
    QuadraticMap.polar (CFSG.LieType.Universal.Spin.quadPlus 4 F) (Pi.single (Sum.inr 0) 1)
      (uE F) = 1 := by
  rw [CFSG.LieType.Universal.Spin.polar_quadPlus, Fin.sum_univ_four]
  simp [uE, Pi.single_apply]

theorem eq_zero_of_scalar (x : (Fin 3 → F) × (Fin 3 → F)) {c : F}
    (h : ∀ v, eichler (CFSG.LieType.Universal.Spin.quadPlus 4 F) (uE F) (wOf F x) v = c • v) :
    x = 0 := by
  have hf := h (Pi.single (Sum.inr 0) 1)
  rw [eichler_apply (uE_singular F) (polar_uE_wOf F x), polar_f0_uE] at hf
  have hk : ∀ k : Fin 4 ⊕ Fin 4, k ≠ Sum.inl 0 → k ≠ Sum.inr 0 → wOf F x k = 0 := by
    intro k hk1 hk2
    have := congrFun hf k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_mul, uE,
      Pi.single_apply, if_neg hk1, if_neg hk2, mul_zero, sub_zero, zero_add] at this
    exact this
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · have := hk (Sum.inl j.succ) (by simp) (by simp)
    simpa [wOf] using this
  · have := hk (Sum.inr j.succ) (by simp) (by simp)
    simpa [wOf] using this

theorem isElemAbelian_top_six (h3 : (3 : F) = 0) :
    IsElemAbelian 3 (⊤ : Subgroup (Multiplicative ((Fin 3 → F) × (Fin 3 → F)))) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (mul_comm _ _)⟩⟩, fun x _ => ?_⟩
  rw [← toAdd_eq_zero, toAdd_pow]
  ext j <;> simp [nsmul_eq_mul, h3]

theorem exists_E_six [Finite F] [CharP F 3] :
    ∃ E : Subgroup (ProjElementary (CFSG.LieType.Universal.Spin.quadPlus 4 F)),
      IsElemAbelian 3 E ∧ Nat.card E = Nat.card F ^ 6 := by
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  let ψP : Multiplicative ((Fin 3 → F) × (Fin 3 → F)) →*
      ProjElementary (CFSG.LieType.Universal.Spin.quadPlus 4 F) :=
    (QuotientGroup.mk' _).comp (psiW F)
  have hinj : Function.Injective ψP := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx0 := (QuotientGroup.eq_one_iff _).1 hx
    rw [Subgroup.mem_subgroupOf, mem_scalars] at hx0
    obtain ⟨c, hc⟩ := hx0
    exact toAdd_eq_zero.1 (eq_zero_of_scalar F _ hc)
  refine ⟨(⊤ : Subgroup _).map ψP, (isElemAbelian_top_six F h3).map ψP, ?_⟩
  rw [Subgroup.card_map_of_injective hinj, Subgroup.card_top,
    Nat.card_congr (Multiplicative.toAdd :
      Multiplicative ((Fin 3 → F) × (Fin 3 → F)) ≃ (Fin 3 → F) × (Fin 3 → F)),
    Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
  ring

end Model

theorem cfgIRank_D4_three {row : S8.Row} (hIq : row.Iq = S8.isD4of 3) (hIz : row.Iz = 1)
    (hrank : row.rank = 6) : CfgIRankRow 3 row := by
  intro Q _ _ hcat hcard
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rw [hIq] at hi
  rw [hIz] at hcard
  have hbot : Subgroup.center Q = ⊥ := (Subgroup.eq_bot_iff_card _).2 hcard
  cases i with
  | cyclic p hp => exact False.elim hi
  | alternating n hn => exact False.elim hi
  | sporadic s => exact False.elim hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | D n q =>
      by_cases hn : n = 4
      · subst hn
        have hq : q.card = 3 := hi
        have hcard' : q.p ^ q.exponent = 3 := (TauCeti.PrimePower.card_def q).symm.trans hq
        have hpe : q.p = 3 ∧ q.exponent = 1 := (Nat.Prime.pow_eq_iff Nat.prime_three).1 hcard'
        have hchar : TauCeti.ValidLieTypeIndex.characteristic ⟨.D 4 q, hv⟩ = 3 :=
          (TauCeti.LieTypeIndex.characteristic_D 4 q).trans hpe.1
        have hCharP : CharP ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) 3 := by
          rw [← hchar]
          infer_instance
        have hK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) = 3 := by
          rw [TauCeti.ValidLieTypeIndex.card_fixedField]
          simp [TauCeti.ValidLieTypeIndex.fieldOrder, TauCeti.PrimePower.card_def, hpe.1, hpe.2]
        haveI : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) :=
          Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
        let f : Q ⧸ Subgroup.center Q ≃* Q :=
          (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
        let e' := (f.symm.trans e).trans
          ((CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 q
            hv).trans
            (statedProjEquiv
              (CFSG.LieType.Universal.Spin.coe_quadPlus 4
                ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩))
              (commutator_orthogonalGroup_quadPlus (by norm_num))))
        obtain ⟨E, hE, hEc⟩ := exists_E_six ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩)
        refine ⟨E.map e'.symm.toMonoidHom, isElemAbelian_map_of_injective e'.symm.injective hE, ?_⟩
        rw [hbot, inf_bot_eq, Subgroup.card_bot, Subgroup.card_map_of_injective e'.symm.injective,
          hEc, hK, hrank]
        norm_num
      · exfalso
        revert hi
        rcases n with _ | _ | _ | _ | _ | n <;> simp_all [S8.isD4of, onLie]
    | _ => exact False.elim hi

theorem cfgIRank_fi24_three : CfgIRankRow 3 S8.Row.fi24 :=
  cfgIRank_D4_three rfl rfl rfl

theorem cfgIRank_fi24h_three : CfgIRankRow 3 S8.Row.fi24h :=
  cfgIRank_D4_three rfl rfl rfl

end CFSG.LocalAnalysis.GLTheoremA.S8.CfgI
