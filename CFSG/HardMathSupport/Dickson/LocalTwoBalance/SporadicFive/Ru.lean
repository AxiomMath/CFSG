module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10Red
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestRu
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalTwoFrontier

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier

private theorem gLAPPrimeCoreOf_centralizer_subtype_eq_bot {M : Type*} [Group M] {P : Subgroup M}
    {p : ℕ} {x : M} (hx : x ∈ P)
    (h : GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set M) ⊓ P) = ⊥) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({(⟨x, hx⟩ : P)} : Set P)) = ⊥ := by
  have hc : (Subgroup.centralizer ({(⟨x, hx⟩ : P)} : Set P)).map P.subtype =
      Subgroup.centralizer ({x} : Set M) ⊓ P := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, z.2⟩
      have := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hz)
      simpa using this
    · intro hy
      obtain ⟨hyc, hyP⟩ := Subgroup.mem_inf.1 hy
      refine ⟨⟨y, hyP⟩, Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_), rfl⟩
      simpa using Subgroup.mem_centralizer_singleton_iff.1 hyc
  have hmap := map_glaPPrimeCoreOf_of_injective p P.subtype P.subtype_injective
    (Subgroup.centralizer ({(⟨x, hx⟩ : P)} : Set P))
  rw [hc, h] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).1 hmap

private theorem innerAut_eq_top_of_mulEquiv' {K K' : Type*} [Group K] [Group K']
    (e : K ≃* K') (h : innerAut K' = ⊤) : innerAut K = ⊤ := by
  rw [eq_top_iff]
  intro σ _
  have hσ : MulAut.congr e σ ∈ innerAut K' := h ▸ Subgroup.mem_top _
  obtain ⟨g', hg'⟩ := hσ
  refine ⟨e.symm g', ?_⟩
  apply (MulAut.congr e).injective
  rw [← hg']
  ext z
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem sporadicTwoBalanceFive_Ru :
    SporadicTwoBalanceFive .Ru := by
  intro S _ _ hS hnab he
  obtain ⟨e⟩ := he
  obtain ⟨hb⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  let eN : S ≃* Blueprint.NativeSporadic.Ru := e.trans hb.symm
  let f : S ≃* ↥ruP := eN.trans ruEquivP
  have hcen : Subgroup.center S = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  have hinn : innerAut S = ⊤ := by
    have hP : innerAut ↥ruP = ⊤ := by
      obtain ⟨-, hbij, -, -⟩ := CTUC_Ru_full_inner_automorphisms_and_second_centralizer
      exact MonoidHom.range_eq_top.2 hbij.2
    exact innerAut_eq_top_of_mulEquiv' f hP
  obtain ⟨hA0C, -, hA0P, hA0card, -, hA0cent, hA0le⟩ := ruFiveA0_spec
  have hmem0 : Subgroup.zpowers (ruFiveLine 0) ∈
      {H : Subgroup (Equiv.Perm (Fin 4060)) | H ≤ ruFiveQ ∧ Nat.card H = 5} := by
    rw [(R3E_Ru_full_five_centralizer_structures).2.1.1]
    exact ⟨0, rfl⟩
  have hz0Q : ruFiveLine 0 ∈ ruFiveQ := hmem0.1 (Subgroup.mem_zpowers _)
  have hz0P : ruFiveLine 0 ∈ ruP := ruFiveQ_le_P hz0Q
  have hz0o : orderOf (ruFiveLine 0) = 5 := by
    rw [← Nat.card_zpowers]
    exact hmem0.2
  have hC0 : ruFiveC0 = Subgroup.centralizer {ruFiveLine 0} ⊓ ruP := ruFiveC0_spec.1
  have hcommA : ∀ a ∈ ruFiveA0, a * ruFiveLine 0 = ruFiveLine 0 * a := fun a ha => by
    have haC : a ∈ ruFiveC0 := hA0C ha
    rw [hC0] at haC
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 haC).1
  have hz0A : ruFiveLine 0 ∈ ruFiveA0 := by
    apply hA0le
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun a ha => hcommA a ha, ?_⟩
    rw [hC0]
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, hz0P⟩
  have hcardS : Nat.card (ruFiveA0.subgroupOf ruP) = 5 ^ (Nat.card ruP).factorization 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA0P).toEquiv, hA0card,
      factorization_card_ruP_five]
    norm_num
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 5 ↥ruP, (Q : Subgroup ↥ruP) = ruFiveA0.subgroupOf ruP :=
    ⟨Sylow.ofCard _ hcardS, rfl⟩
  have hQmem : ∀ g : ↥ruP, g ∈ Q ↔ (g : Equiv.Perm (Fin 4060)) ∈ ruFiveA0 := fun g => by
    change g ∈ (Q : Subgroup ↥ruP) ↔ _
    rw [hQ, Subgroup.mem_subgroupOf]
  have hQc : Nat.card Q = 5 ^ 3 := by
    change Nat.card (Q : Subgroup ↥ruP) = _
    rw [hQ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA0P).toEquiv, hA0card]
    norm_num
  have hzQ : (⟨ruFiveLine 0, hz0P⟩ : ↥ruP) ∈ Q := (hQmem _).2 hz0A
  have hzo : orderOf (⟨ruFiveLine 0, hz0P⟩ : ↥ruP) = 5 := by
    rw [Subgroup.orderOf_mk]
    exact hz0o
  have hzc : ∀ g ∈ Q, g * ⟨ruFiveLine 0, hz0P⟩ = ⟨ruFiveLine 0, hz0P⟩ * g :=
    fun g hg => Subtype.ext (hcommA _ ((hQmem g).1 hg))
  have hnc : ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcomm' : ∀ a ∈ ruFiveA0, ∀ b ∈ ruFiveA0, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hcon ⟨a, hA0P ha⟩ ((hQmem _).2 ha) ⟨b, hA0P hb⟩ ((hQmem _).2 hb))
    have hle : ruFiveA0 ≤ Subgroup.centralizer (ruFiveA0 : Set (Equiv.Perm (Fin 4060))) ⊓
        ruFiveC0 := fun a ha =>
      Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun b hb => hcomm' b hb a ha, hA0C ha⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [hA0card, hA0cent] at h1
    norm_num at h1
  have hO : GLAPPrimeCoreOf 5
      (Subgroup.centralizer ({(⟨ruFiveLine 0, hz0P⟩ : ↥ruP)} : Set ↥ruP)) = ⊥ :=
    gLAPPrimeCoreOf_centralizer_subtype_eq_bot hz0P
      (gLAPPrimeCoreOf_ruFiveRecord_eq_bot 0 (Or.inl rfl))
  exact isLocallyBalancedAbs_two_of_sylow_card_cube Nat.prime_five f hcen hinn Q hQc hzQ hzo hzc
    hnc hO

end CFSG.HardMathSupport.Dickson.LocalTwoBalance
