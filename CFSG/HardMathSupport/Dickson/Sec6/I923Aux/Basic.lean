module

public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldReduce

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def Y923 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → CFSG.IsKGroup Y →
    CFSG.Open.GLAPPrimeCore 3 Y = ⊥ → ∀ α : MulAut Y, α ^ 3 = 1 → α ∉ innAutDerived Y →
      ∀ J : Subgroup Y, GLAPComponent 3 (Lemma510Ns.fixSub α) J →
        ∀ r0 : ℕ, 10 ≤ r0 → IsTypeL2 r0 (barOf 3 J) → IsTypeL2 (r0 ^ 3) Y

theorem input9_2_3_of_Y (h : Y923) : Input9_2_3 innAutDerivedVocab := by
  intro G _ _ I hq hK x hx hx3 hnot J hJ r0 hr0 hT
  have hKbar : CFSG.IsKGroup (barOf 3 I) := CFSG.IsKGroup.quotient hK _
  have hcore : CFSG.Open.GLAPPrimeCore 3 (barOf 3 I) = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCore_quotient_eq_bot Nat.prime_three
  have hα3 := Lemma510Ns.barAut_pow_three hx hx3
  have hnot' : barAut 3 I ⟨x, hx⟩ ∉ innAutDerived (barOf 3 I) := fun hm => hnot ⟨hx, hm⟩
  obtain ⟨J₁, hJ₁, rfl⟩ := Lemma510Ns.exists_comp_subgroupOf (inf_le_left : I ⊓ Cs x ≤ I) hJ
  have hJ₂ := Lemma510Ns.comp_map_fixSub hx hx3 hJ₁
  have hT' := l2fld_isTypeL2_of_mulEquiv (Lemma510Ns.liftEquiv J₁) hT
  exact h (barOf 3 I) hq hKbar hcore _ hα3 hnot' _ hJ₂ r0 hr0 hT'

theorem y923_of_typeL2 (hU : L2OrderUnique) (h1 : L2Aut3Classification) (h2 : L2FieldFixed)
    (h0 : L2CentreThree) {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (hO : CFSG.Open.GLAPPrimeCore 3 Y = ⊥) {s : ℕ} (hs : IsTypeL2 s Y) {α : MulAut Y}
    (h3 : α ^ 3 = 1) (hnot : α ∉ innAutDerived Y) {J : Subgroup Y}
    (hJ : GLAPComponent 3 (Lemma510Ns.fixSub α) J) {r0 : ℕ} (hr0 : 10 ≤ r0)
    (hT : IsTypeL2 r0 (barOf 3 J)) : IsTypeL2 (r0 ^ 3) Y := by
  rcases l2fld_core hU h1 h2 h0 hY hO hs h3 hJ hT with ⟨ha, -⟩ | ⟨-, -, hs3 | ⟨h45, -⟩⟩
  · exact absurd (ha ▸ one_mem _) hnot
  · exact hs3 ▸ hs
  · omega

theorem exists_not_comm_of_quasisimple {Y : Type} [Group Y] (hq : CFSG.Open.IsQuasisimple Y) :
    ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a := by
  obtain ⟨hperf, hsimple⟩ := hq
  by_contra hab
  push Not at hab
  have hcomm : ∀ a b : Y, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center Y := by
    intro a b
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hab (a : Y ⧸ Subgroup.center Y) b]
    group
  have hle : commutator Y ≤ Subgroup.center Y := by
    rw [commutator, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def]
    exact hcomm a b
  rw [hperf, top_le_iff] at hle
  have hall : ∀ q : Y ⧸ Subgroup.center Y, q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x => exact (QuotientGroup.eq_one_iff x).2 (hle ▸ Subgroup.mem_top x)
  have := hsimple
  obtain ⟨a, b, hab'⟩ := exists_pair_ne (Y ⧸ Subgroup.center Y)
  exact hab' ((hall a).trans (hall b).symm)

theorem inCatalog_of_quasisimple {Y : Type} [Group Y] (hK : CFSG.IsKGroup Y)
    (hq : CFSG.Open.IsQuasisimple Y) : CFSG.Assembly.InCatalog (Y ⧸ Subgroup.center Y) := by
  have e : (↥(⊤ : Subgroup Y) ⧸ (Subgroup.center Y).subgroupOf (⊤ : Subgroup Y)) ≃*
      (Y ⧸ Subgroup.center Y) :=
    QuotientGroup.congr _ _ Subgroup.topEquiv (by
      ext x
      simp [Subgroup.mem_map, Subgroup.mem_subgroupOf])
  have hnorm : ((Subgroup.center Y).subgroupOf (⊤ : Subgroup Y)).Normal :=
    Subgroup.Normal.subgroupOf inferInstance _
  have hs : IsSimpleGroup
      (↥(⊤ : Subgroup Y) ⧸ (Subgroup.center Y).subgroupOf (⊤ : Subgroup Y)) :=
    e.isSimpleGroup_congr.2 hq.2
  exact CFSG.Assembly.inCatalog_isoInvariant e.symm (hK ⊤ _ hs)

theorem inner_of_pow_three {T : Type*} [Group T] [Finite T] (h : ¬ 3 ∣ Nat.card (Outer T))
    {β : MulAut T} (hβ : β ^ 3 = 1) : β ∈ inner T := by
  have : Finite (MulAut T) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut T))
  have hQ : (QuotientGroup.mk β : Outer T) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hβ]
    rfl
  have hdvd3 : orderOf (QuotientGroup.mk β : Outer T) ∣ 3 := orderOf_dvd_of_pow_eq_one hQ
  have hdvdN : orderOf (QuotientGroup.mk β : Outer T) ∣ Nat.card (Outer T) :=
    orderOf_dvd_natCard _
  have h1 : orderOf (QuotientGroup.mk β : Outer T) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd3 with h1 | h3
    · exact h1
    · exact absurd (h3 ▸ hdvdN) h
  exact (QuotientGroup.eq_one_iff β).1 (orderOf_eq_one_iff.1 h1)

theorem mem_innAutDerived_of_card_outer {Y T : Type} [Group Y] [Group T] [Finite T]
    (hY : CFSG.Open.IsQuasisimple Y) (e : (Y ⧸ Subgroup.center Y) ≃* T)
    (h : ¬ 3 ∣ Nat.card (Outer T)) {α : MulAut Y} (h3 : α ^ 3 = 1) : α ∈ innAutDerived Y := by
  haveI : Group.IsPerfect Y := ⟨hY.1⟩
  have hβ3 : (MulAut.congr e (centerDescend Y α)) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, h3, map_one, map_one]
  have hinn : IsInnerAut (MulAut.congr e (centerDescend Y α)) := inner_of_pow_three h hβ3
  have hinn' : IsInnerAut (centerDescend Y α) := (isInnerAut_congr e _).1 hinn
  exact innerAut_le_innAutDerived Y (isInnerAut_of_isInnerAut_centerDescend hinn')

theorem mem_innAutDerived_alt_ne_six {Y : Type} [Group Y] (hY : CFSG.Open.IsQuasisimple Y)
    {n : ℕ} (hn : 5 ≤ n) (h6 : n ≠ 6)
    (e : (Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin n)) {α : MulAut Y} (h3 : α ^ 3 = 1) :
    α ∈ innAutDerived Y := by
  haveI : Group.IsPerfect Y := ⟨hY.1⟩
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn h6
  have hβ3 : (MulAut.congr e (centerDescend Y α)) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, h3, map_one, map_one]
  obtain ⟨σ, hσ⟩ := hbij.2 (MulAut.congr e (centerDescend Y α))
  have hσ3 : σ ^ 3 = 1 := hbij.1 (by rw [map_pow, hσ, hβ3, map_one])
  have hsign : σ.sign = 1 := by
    have h := congrArg Equiv.Perm.sign hσ3
    rw [map_pow, map_one] at h
    rcases Int.units_eq_one_or σ.sign with h1 | h1
    · exact h1
    · exact absurd h (by rw [h1]; decide)
  have hσA : σ ∈ alternatingGroup (Fin n) := Equiv.Perm.mem_alternatingGroup.2 hsign
  have hinn : IsInnerAut (MulAut.congr e (centerDescend Y α)) := by
    refine ⟨⟨σ, hσA⟩, ?_⟩
    rw [← hσ]
    ext x
    simp [MulAut.conjNormal_apply, MulAut.conj_apply]
  have hinn' : IsInnerAut (centerDescend Y α) := (isInnerAut_congr e _).1 hinn
  exact innerAut_le_innAutDerived Y (isInnerAut_of_isInnerAut_centerDescend hinn')

theorem two_dvd_card_outer_alt_six : 2 ∣ Nat.card (Outer (alternatingGroup (Fin 6))) := by
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num)
  have hdvd : Nat.card (Equiv.Perm (Fin 6)) ∣ Nat.card (MulAut (alternatingGroup (Fin 6))) := by
    have h := Subgroup.card_subgroup_dvd_card
      (MulAut.conjNormal (H := alternatingGroup (Fin 6)) :
        Equiv.Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range
    rwa [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at h
  have hperm : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_perm, Nat.card_fin]
    decide
  have hquot := (inner (alternatingGroup (Fin 6))).card_eq_card_quotient_mul_card_subgroup
  rw [CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.inner_card] at hquot
  rw [hperm] at hdvd
  change Nat.card (MulAut (alternatingGroup (Fin 6))) =
    Nat.card (MulAut (alternatingGroup (Fin 6)) ⧸ inner (alternatingGroup (Fin 6))) * 360 at hquot
  change 2 ∣ Nat.card (MulAut (alternatingGroup (Fin 6)) ⧸ inner (alternatingGroup (Fin 6)))
  omega

theorem not_three_dvd_card_outer_alt_six :
    ¬ 3 ∣ Nat.card (Outer (alternatingGroup (Fin 6))) := by
  have h4 := CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.outer_card_le_four
  have h2 := two_dvd_card_outer_alt_six
  have hpos : 0 < Nat.card (Outer (alternatingGroup (Fin 6))) := Nat.card_pos
  omega

end CFSG.HardMathSupport.Dickson.Sec6.I923
