module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoF4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.LieType.Steinberg.CentralExt.F4TwoMultiplier

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup glaPComponent_isComponent_of_le_layer)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.HardMathSupport.Dickson.Bal207 (CompShape)
open CFSG.HardMathSupport.Dickson.Bal207.FamF42 (F42CompType isoInvariant_f42CompType
  compShape_F4_two)
open CFSG.Blueprint.Chevalley

theorem card_of_f42CompType {Q : Type} [Group Q] (h : F42CompType Q) : Nat.card Q = 1451520 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (le_refl 1) (by rw [hF]; norm_num)
  have hZ := CFSG.HardMathSupport.Dickson.Bal207.center_statedSp_eq_bot_of_charP_two (K := F) 3
  rw [Nat.card_congr e.toEquiv, hZ,
    show Nat.card (StatedSp 3 F ⧸ (⊥ : Subgroup (StatedSp 3 F))) = Nat.card (StatedSp 3 F) from
      Nat.card_congr QuotientGroup.quotientBot.toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF]
  decide

theorem card_of_isA6 {Q : Type} [Group Q] (h : catalogIs Q S8.isA6) : Nat.card Q = 360 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with hi | hi
  · cases i with
    | alternating n hn =>
      have hn6 : n = 6 := hi
      subst hn6
      rw [Nat.card_congr e.toEquiv]
      have h2 := two_mul_nat_card_alternatingGroup (α := Fin 6)
      have hp : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
      change Nat.card (alternatingGroup (Fin 6)) = 360
      omega
    | _ => exact hi.elim
  · cases i with
    | lie j =>
      obtain ⟨d, hv⟩ := j
      cases d with
      | A n q =>
        rcases n with _ | _ | n
        · exact hi.elim
        · have hq : q.card = 9 := hi
          have hdup := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
          rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hdup
          exact (hdup (Or.inl ⟨rfl, Or.inr (Or.inr hq)⟩)).elim
        · exact hi.elim
      | _ => exact hi.elim
    | _ => exact hi.elim

theorem exists_ne_comm_of_simple_perfect {H : Type*} [Group H] [IsSimpleGroup H]
    (h : commutator H = ⊤) : ∃ a b : H, a * b ≠ b * a := by
  haveI : Group.IsPerfect H := ⟨h⟩
  by_contra hc
  apply Group.IsPerfect.not_isMulCommutative H
  refine IsMulCommutative.of_comm fun a b => ?_
  by_contra hab
  exact hc ⟨a, b, hab⟩

theorem center_eq_bot_of_f4two
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (hO : GLAPPrimeCore 3 Y = ⊥) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (e : Y ⧸ Subgroup.center Y ≃* ↥(adjointGroup Tag.F4 K)) : Subgroup.center Y = ⊥ := by
  haveI : Group.IsPerfect Y :=
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native Y).1 hY).1
  let η : Y →* ↥(adjointGroup Tag.F4 K) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))
  have hη : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = Subgroup.center Y := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (Subgroup.center Y) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hle := CFSG.LieType.Steinberg.CentralExt.F4Two.f4_two_card_ker_le_two hK η hη hker.le
  rw [hker] at hle
  have hpos : 0 < Nat.card (Subgroup.center Y) := Nat.card_pos
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.center Y)) := by
    interval_cases h : Nat.card (Subgroup.center Y) <;> norm_num
  have hsub : Subgroup.center Y ≤ CFSG.pPrimeCore 3 Y := le_sSup ⟨inferInstance, hcop⟩
  have hO' : CFSG.pPrimeCore 3 Y = ⊥ := hO
  rw [hO'] at hsub
  exact le_bot_iff.1 hsub

section F4


theorem i1431InspF42_holds : I1431InspF42 := by
  intro Y _ _ hY hO hcat τ hτ A hA hT
  obtain ⟨hTc, -⟩ := hT
  have h360 : Nat.card (PSimple 3 A) = 360 := card_of_isA6 hTc
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rcases i with _ | _ | ⟨d, hv⟩ | _
  · exact hi.elim
  · exact hi.elim
  · cases d with
    | F4 q =>
      have hq2 : q.card = 2 := hi
      obtain ⟨hp, -⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq Nat.prime_two
        (s := 1) (by norm_num) (hq2.trans (by norm_num))
      have hK : Nat.card (GaloisField 2 1) = 2 := by
        rw [GaloisField.card 2 1 (by norm_num)]
        norm_num
      obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 q hv hp (GaloisField 2 1)
        (by rw [hK, hq2])
      have hZad : Subgroup.center ↥(adjointGroup Tag.F4 (GaloisField 2 1)) = ⊥ :=
        CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
      let e' : (Y ⧸ Subgroup.center Y) ≃* ↥(adjointGroup Tag.F4 (GaloisField 2 1)) :=
        e.trans (eB.symm.trans
          ((QuotientGroup.quotientMulEquivOfEq hZad).trans QuotientGroup.quotientBot))
      have hZ : Subgroup.center Y = ⊥ := center_eq_bot_of_f4two hY hO hK e'
      let E : Y ≃* ↥(adjointGroup Tag.F4 (GaloisField 2 1)) :=
        (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e'
      haveI : Nontrivial (PSimple 3 A) := by
        rw [← Finite.one_lt_card_iff_nontrivial, h360]
        norm_num
      by_cases hτ1 : τ = 1
      ·
        have htop : fixSubgroup τ = ⊤ := by
          rw [hτ1]
          exact fixSubgroup_one_eq_top
        rw [htop] at hA
        haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
        haveI : IsSimpleGroup Y :=
          ((QuotientGroup.quotientMulEquivOfEq hZ).trans
            QuotientGroup.quotientBot).symm.isSimpleGroup
        have hAt : A = ⊤ := KDSpor.eq_top_of_glaPComponent_top hA
        subst hAt
        obtain ⟨φ⟩ := KDSpor.nonempty_pSimple_top_equiv Nat.prime_three
          (exists_ne_comm_of_simple_perfect hY.1) hA
        have hcard := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨_, hv⟩
          (Y ⧸ Subgroup.center Y) ⟨e⟩
        have hYc : Nat.card (Y ⧸ Subgroup.center Y) = Nat.card Y :=
          Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
            QuotientGroup.quotientBot).toEquiv
        rw [hYc, ← Nat.card_congr φ.toEquiv, h360] at hcard
        simp only [lieOrderFormula, CFSG.Open.orderF4, hq2] at hcard
        norm_num at hcard
      ·
        have hpow : MulAut.congr E τ ^ 3 = 1 := by rw [← map_pow, hτ, map_one]
        have hne : MulAut.congr E τ ≠ 1 := fun h =>
          hτ1 ((MulAut.congr E).injective (h.trans (map_one _).symm))
        have hsh : CompShape F42CompType τ :=
          CompShape.of_congr isoInvariant_f42CompType E (compShape_F4_two hK _ hpow hne)
        have hlay := hsh.layer _ hA.1 (glaPComponent_perfect hA)
        have hAc := (glaPComponent_isComponent_of_le_layer hA hlay).1
        obtain ⟨φ⟩ := I1431C2.nonempty_centerQuot_equiv_psimple hAc.2.2 inferInstance
        have h1 := card_of_f42CompType (hsh.type A hAc)
        rw [Nat.card_congr φ.toEquiv, h360] at h1
        norm_num at h1
    | _ => exact hi.elim
  · exact hi.elim

end F4

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
