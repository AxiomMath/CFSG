module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThAbstract
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SimpleLeaf

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

section Simple

variable {Q : Type} [Group Q] [Finite Q]

theorem normal_coprime_eq_bot_of_gla {p : ℕ} {C : Subgroup Q} (hO : GLAPPrimeCoreOf p C = ⊥)
    (N : Subgroup ↥C) (hN : N.Normal) (hcop : Nat.Coprime p (Nat.card N)) : N = ⊥ := by
  have hO' : CFSG.pPrimeCore p ↥C = ⊥ := by
    unfold GLAPPrimeCoreOf at hO
    exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).1 hO
  have : N ≤ CFSG.pPrimeCore p ↥C := le_sSup ⟨hN, hcop⟩
  rw [hO'] at this
  exact le_bot_iff.1 this

theorem shapeRkAt_of_simple_small_index {t : Q} (ht3 : orderOf t = 3)
    (hO : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({t} : Set Q)) = ⊥)
    (E : Subgroup Q) (hEC : E ≤ Subgroup.centralizer ({t} : Set Q))
    (hs : IsSimpleGroup ↥E) (hnab : ∃ a b : ↥E, a * b ≠ b * a) (h3 : 3 ∣ Nat.card ↥E)
    (hnd : ∀ n ≤ 14, ¬ Nat.card ↥E ∣ n.factorial)
    (hC : Nat.card ↥(Subgroup.centralizer ({t} : Set Q)) < 15 * Nat.card ↥E)
    (hG : LeafType 3 ↥E) : ShapeRkAt 3 (LeafType 3) (fun _ _ => True) t := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({t} : Set Q) with hCdef
  have hEZ : Subgroup.center ↥E = ⊥ := center_eq_bot_of_simple_nonab hnab
  set E' : Subgroup ↥C := E.subgroupOf C with hE'def
  have eE : ↥E' ≃* ↥E := Subgroup.subgroupOfEquivOfLe hEC
  haveI : IsSimpleGroup ↥E' := eE.isSimpleGroup_congr.2 hs
  have hcardE' : Nat.card E' = Nat.card E := Nat.card_congr eE.toEquiv
  have hEpos : 0 < Nat.card E := Nat.card_pos
  have hidx : E'.index ≤ 14 := by
    have h1 : E'.index * Nat.card E' = Nat.card C := Subgroup.index_mul_card E'
    rw [hcardE'] at h1
    by_contra h
    have : 15 ≤ E'.index := by omega
    nlinarith
  have hnormE' : E'.Normal := by
    refine normal_of_simple_not_dvd_factorial E' ?_
    rw [hcardE']
    exact hnd _ hidx
  have hLn : ∀ g ∈ C, ∀ l ∈ E, g * l * g⁻¹ ∈ E := by
    intro g hg l hl
    have := hnormE'.conj_mem ⟨l, hEC hl⟩ (Subgroup.mem_subgroupOf.2 hl) ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hLq : CFSG.Open.IsQuasisimple ↥E := by
    refine ⟨?_, ((QuotientGroup.quotientMulEquivOfEq hEZ).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥E) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have h1 : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.1 h1)
    · exact h
  have hcore : GLAPPrimeCore 3 ↥E = ⊥ := by
    haveI := hs
    exact glaPPrimeCore_eq_bot_of_simple Nat.prime_three h3
  have hcent : IsPGroup 3 ↥(C ⊓ Subgroup.centralizer (E : Set Q)) := by
    set Z : Subgroup Q := C ⊓ Subgroup.centralizer (E : Set Q) with hZdef
    have hZC : Z ≤ C := inf_le_left
    set Z0 : Subgroup ↥C := Z.subgroupOf C with hZ0def
    have eZ : ↥Z0 ≃* ↥Z := Subgroup.subgroupOfEquivOfLe hZC
    haveI hZ0n : Z0.Normal := by
      constructor
      intro x hx g
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      refine ⟨C.mul_mem (C.mul_mem g.2 x.2) (C.inv_mem g.2), Subgroup.mem_centralizer_iff.2 ?_⟩
      intro e he
      have he' : (g : Q)⁻¹ * e * g ∈ E := by
        simpa using hLn _ (C.inv_mem g.2) e he
      have h1 := Subgroup.mem_centralizer_iff.1 hx.2 _ he'
      calc e * (g * x * g⁻¹ : ↥C) = g * ((g : Q)⁻¹ * e * g * x) * (g : Q)⁻¹ := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
        _ = g * (x * ((g : Q)⁻¹ * e * g)) * (g : Q)⁻¹ := by rw [h1]
        _ = (g * x * g⁻¹ : ↥C) * e := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
    have htZ : t ∈ Z := ⟨htC, Subgroup.mem_centralizer_iff.2 fun h hh =>
      Subgroup.mem_centralizer_singleton_iff.1 (hEC hh)⟩
    have hs0Z : (⟨t, htC⟩ : ↥C) ∈ Z0 := Subgroup.mem_subgroupOf.2 htZ
    have hs0c : ∀ c : ↥C, c * (⟨t, htC⟩ : ↥C) = (⟨t, htC⟩ : ↥C) * c := fun c =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 c.2)
    have hs03 : orderOf (⟨t, htC⟩ : ↥C) = 3 := by rw [Subgroup.orderOf_mk]; exact ht3
    have hinj : Function.Injective ((QuotientGroup.mk' E').comp Z0.subtype) := by
      rw [injective_iff_map_eq_one]
      intro z hz
      have hzE : (z : ↥C) ∈ E' := (QuotientGroup.eq_one_iff _).1 hz
      have hzE2 : ((z : ↥C) : Q) ∈ E := Subgroup.mem_subgroupOf.1 hzE
      have hzZ : ((z : ↥C) : Q) ∈ Subgroup.centralizer (E : Set Q) :=
        (Subgroup.mem_subgroupOf.1 z.2).2
      have hmem : (⟨((z : ↥C) : Q), hzE2⟩ : ↥E) ∈ Subgroup.center ↥E := by
        rw [Subgroup.mem_center_iff]
        intro b
        exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hzZ b b.2))
      rw [hEZ, Subgroup.mem_bot] at hmem
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg Subtype.val hmem
      simpa using this
    have hZ0card : Nat.card Z0 < 18 := by
      have h1 := Subgroup.card_dvd_of_injective _ hinj
      have h2 : Nat.card (↥C ⧸ E') = E'.index := rfl
      rw [h2] at h1
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1
      omega
    have hO' := normal_coprime_eq_bot_of_gla hO
    have hp := isPGroup_three_of_small_central hs0Z hs03 hs0c hZ0card hO'
    exact hp.of_equiv eZ
  exact shapeRkAt_of_normal_quasisimple Nat.prime_three hEC hLn hLq h3 (by
    simpa [inf_comm] using hcent)
    (LeafType.of_equiv (pSimpleEquivSelf E hcore hEZ).symm hG) trivial

end Simple

end CFSG.HardMathSupport.Dickson.I271
