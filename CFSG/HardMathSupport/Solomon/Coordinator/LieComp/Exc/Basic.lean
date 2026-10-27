module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md42047359a2a
open scoped commutatorElement

theorem three_dvd_card_of_glaPComponent {G : Type*} [Group G] [Finite G] {X J : Subgroup G}
    (hJ : GLAPComponent 3 X J) : 3 ∣ Nat.card J := by
  have hQ : CFSG.Open.IsQuasisimple (↥J ⧸ GLAPPrimeCore 3 ↥J) :=
    isQuasisimple_quotient_of_glaPComponent hJ
  set P : Subgroup ↥J := GLAPPrimeCore 3 ↥J with hPdef
  have hQnt : Nontrivial (↥J ⧸ P) := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    have := hQ.2.toNontrivial
    have : Subsingleton ((↥J ⧸ P) ⧸ Subgroup.center (↥J ⧸ P)) :=
      (QuotientGroup.mk'_surjective (Subgroup.center (↥J ⧸ P))).subsingleton
    exact not_subsingleton _ this
  have hdvd : 3 ∣ Nat.card (↥J ⧸ P) := by
    by_contra hnd
    have hc : Nat.Coprime 3 (Nat.card (↥J ⧸ P)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd
    have hbot : GLAPPrimeCore 3 (↥J ⧸ P) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
    have htop : (⊤ : Subgroup (↥J ⧸ P)) ≤ GLAPPrimeCore 3 (↥J ⧸ P) :=
      le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩
    rw [hbot] at htop
    obtain ⟨u, v, huv⟩ := exists_pair_ne (↥J ⧸ P)
    exact huv ((Subgroup.mem_bot.1 (htop (Subgroup.mem_top u))).trans
      (Subgroup.mem_bot.1 (htop (Subgroup.mem_top v))).symm)
  have h2 : Nat.card (↥J ⧸ P) ∣ Nat.card J := by
    have := Subgroup.index_dvd_card P
    simpa [Subgroup.index] using this
  exact hdvd.trans h2

theorem noThreeComponents_of_not_dvd {S : Type} [Group S] [Finite S] (h : ¬ 3 ∣ Nat.card S)
    (β : MulAut S) : NoThreeComponents β := by
  intro J hJ
  have h1 : 3 ∣ Nat.card J := three_dvd_card_of_glaPComponent hJ
  have h2 : Nat.card J ∣ Nat.card S := Subgroup.card_subgroup_dvd_card J
  exact h (h1.trans h2)

theorem noThreeComponents_of_isSolvable {S : Type} [Group S] [Finite S] (β : MulAut S)
    (h : Group.IsSolvable ↥(fixSubgroup β)) : NoThreeComponents β := by
  intro J hJ
  have hQ : CFSG.Open.IsQuasisimple (↥J ⧸ GLAPPrimeCore 3 ↥J) :=
    isQuasisimple_quotient_of_glaPComponent hJ
  have hJC : J ≤ fixSubgroup β := hJ.1
  haveI : Group.IsSolvable ↥J :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJC)
  haveI : Group.IsSolvable (↥J ⧸ GLAPPrimeCore 3 ↥J) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥J))
  haveI : Group.IsPerfect (↥J ⧸ GLAPPrimeCore 3 ↥J) := ⟨hQ.1⟩
  haveI : Nontrivial (↥J ⧸ GLAPPrimeCore 3 ↥J) := by
    have := hQ.2.toNontrivial
    exact (QuotientGroup.mk_surjective (s := Subgroup.center (↥J ⧸ GLAPPrimeCore 3 ↥J))).nontrivial
  exact Group.IsPerfect.not_isSolvable (↥J ⧸ GLAPPrimeCore 3 ↥J) inferInstance

theorem eq_of_isComponentOf_of_perfect_le {G : Type*} [Group G] [Finite G] {C J K : Subgroup G}
    (hJ : IsComponentOf J C) (hperf : ∀ P : Subgroup G, P ≤ C → ⁅P, P⁆ = P → P ≤ J)
    (hK : IsComponentOf K C) : K = J := by
  obtain ⟨-, h⟩ := component_mem_named_factors (ι := Unit) (fun _ => J) (fun _ => hJ)
    (fun P hPC hP => by
      simpa using hperf P hPC (Subgroup.isPerfect_iff.1 ⟨hP⟩)) hK
  exact h

theorem isChevSimple_of_lie {q : ℕ} {X : Type} [Group X] (idx : TauCeti.ValidLieTypeIndex)
    (hq : idx.1.characteristic = q) (e : X ≃* (TauCeti.CFSGIndex.lie idx).Group) :
    CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q X :=
  Or.inl ⟨TauCeti.CFSGIndex.lie idx, by simpa [CFSG.Yardstones.Md0ec50421ce4.onLie] using hq,
    ⟨e⟩⟩

theorem isEmpty_mulEquiv_alt6_of_card_ne {X : Type*} [Group X] (h : Nat.card X ≠ 360) :
    IsEmpty (X ≃* alternatingGroup (Fin 6)) := by
  refine ⟨fun e => h ?_⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
    Fintype.card_fin]
  decide

theorem lieFactorData_of_simple {q : ℕ} {X : Type} [Group X] [IsSimpleGroup X]
    (hnc : ∃ a b : X, a * b ≠ b * a)
    (h : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q X) : LieFactorData q X := by
  have hq := b3Lie_isQuasisimple_of_simple hnc
  have hZ : Subgroup.center X = ⊥ := b3Lie_center_eq_bot hnc
  let eZ : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨hq.1, isChevSimple_congr eZ.symm h, fun _ => ?_⟩
  rw [hZ, Subgroup.card_bot]
  norm_num

theorem lieCompExport_of_unique_component {q : ℕ} {S : Type} [Group S] [Finite S]
    {β : MulAut S} (hlayer : PerfectInLayer β) {J : Subgroup S}
    (hJ : IsComponentOf J (fixSubgroup β))
    (hperf : ∀ P : Subgroup S, P ≤ fixSubgroup β → ⁅P, P⁆ = P → P ≤ J)
    (hX : ∃ (X : Type) (_ : Group X) (_ : Finite X), LieFactorData q X ∧
      ∃ f : X →* ↥J, Function.Surjective f ∧ f.ker ≤ Subgroup.center X)
    (hA6 : IsEmpty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 6))) :
    LieCompExport q β := by
  refine ⟨hlayer, fun K hK => ?_, fun ⟨K, hK, ⟨a⟩⟩ => ?_⟩
  · obtain rfl := eq_of_isComponentOf_of_perfect_le hJ hperf hK
    exact hX
  · obtain rfl := eq_of_isComponentOf_of_perfect_le hJ hperf hK
    exact (hA6.false a).elim

theorem lieCompExport_of_normal_quasisimple {q : ℕ} {S : Type} [Group S] [Finite S]
    {β : MulAut S} {J : Subgroup S} (hJC : J ≤ fixSubgroup β)
    [(J.subgroupOf (fixSubgroup β)).Normal] (hJq : CFSG.IsQuasisimple ↥J)
    (hsol : Group.IsSolvable (↥(fixSubgroup β) ⧸ J.subgroupOf (fixSubgroup β)))
    (hX : ∃ (X : Type) (_ : Group X) (_ : Finite X), LieFactorData q X ∧
      ∃ f : X →* ↥J, Function.Surjective f ∧ f.ker ≤ Subgroup.center X)
    (hA6 : IsEmpty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 6))) :
    LieCompExport q β := by
  have hJc : IsComponentOf J (fixSubgroup β) :=
    ⟨hJC, CFSG.Open.IsSubnormal.step hJC inferInstance (CFSG.Open.IsSubnormal.refl _),
      LieSemisimple.open_isQuasisimple hJq⟩
  exact lieCompExport_of_unique_component
    (LieSemisimple.perfectInLayer_of_normal_quasisimple hJC hJq hsol) hJc
    (fun P hPC hP => LieSemisimple.perfect_le_of_solvable_quotient hJC hsol hPC hP) hX hA6

theorem fixSubgroup_congr {S G : Type*} [Group S] [Group G] (e : S ≃* G) (β : MulAut S) :
    fixSubgroup (MulAut.congr e β) = (fixSubgroup β).map (e : S →* G) := by
  ext x
  rw [mem_fixSubgroup]
  refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
  rw [mem_fixSubgroup]
  show e (β (e.symm x)) = x ↔ β (e.symm x) = e.symm x
  exact e.eq_symm_apply.symm

noncomputable def fixSubgroupCongrEquiv {S G : Type*} [Group S] [Group G] (e : S ≃* G)
    (β : MulAut S) : ↥(fixSubgroup β) ≃* ↥(fixSubgroup (MulAut.congr e β)) :=
  ((fixSubgroup β).equivMapOfInjective (e : S →* G) e.injective).trans
    (MulEquiv.subgroupCongr (fixSubgroup_congr e β).symm)

theorem isSolvable_fixSubgroup_of_congr {S G : Type*} [Group S] [Group G] (e : S ≃* G)
    {β : MulAut S} (h : Group.IsSolvable ↥(fixSubgroup (MulAut.congr e β))) :
    Group.IsSolvable ↥(fixSubgroup β) :=
  Group.isSolvable_of_isSolvable_injective (f := (fixSubgroupCongrEquiv e β).toMonoidHom)
    (fixSubgroupCongrEquiv e β).injective

theorem isEmpty_quotient_center_alt6 {J : Type*} [Group J] (hZ : Subgroup.center J = ⊥)
    (h : IsEmpty (J ≃* alternatingGroup (Fin 6))) :
    IsEmpty ((J ⧸ Subgroup.center J) ≃* alternatingGroup (Fin 6)) :=
  ⟨fun f => h.false (((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).symm.trans f)⟩

theorem lieCompExport_of_derived_eq_simple {q : ℕ} {S : Type} [Group S] [Finite S] {δ : MulAut S}
    {J : Subgroup S} (hder : ⁅fixSubgroup δ, fixSubgroup δ⁆ = J) (hs : IsSimpleGroup J)
    (hnc : ∃ a b : J, a * b ≠ b * a)
    (hX : ∃ (X : Type) (_ : Group X) (_ : Finite X), LieFactorData q X ∧
      ∃ f : X →* ↥J, Function.Surjective f ∧ f.ker ≤ Subgroup.center X)
    (hA6 : IsEmpty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 6))) :
    LieCompExport q δ := by
  have hJC : J ≤ fixSubgroup δ := by
    rw [← hder]
    exact Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact (fixSubgroup δ).mul_mem ((fixSubgroup δ).mul_mem ((fixSubgroup δ).mul_mem ha hb)
        ((fixSubgroup δ).inv_mem ha)) ((fixSubgroup δ).inv_mem hb)
  haveI hJnorm : (J.subgroupOf (fixSubgroup δ)).Normal := by
    rw [← hder]
    have h := Subgroup.normal_subgroupOf_commutator_sup (fixSubgroup δ) (fixSubgroup δ)
    rwa [sup_idem] at h
  have hsol : Group.IsSolvable (↥(fixSubgroup δ) ⧸ J.subgroupOf (fixSubgroup δ)) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      ← hder]
    have e : (((x * y)⁻¹ * (y * x) : ↥(fixSubgroup δ)) : S) =
        ⁅((y⁻¹ : ↥(fixSubgroup δ)) : S), ((x⁻¹ : ↥(fixSubgroup δ)) : S)⁆ := by
      simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact Subgroup.commutator_mem_commutator (y⁻¹).2 (x⁻¹).2
  exact lieCompExport_of_normal_quasisimple hJC
    (LieSemisimple.isQuasisimple_of_isSimpleGroup hs hnc) hsol hX hA6

theorem lieCompExport_of_fixSubgroup_eq {q : ℕ} {G : Type} [Group G] {α γ : MulAut G}
    (h : fixSubgroup α = fixSubgroup γ) (hα : LieCompExport q α) : LieCompExport q γ := by
  refine ⟨fun P hP hPP => ?_, fun K hK => ?_, fun ⟨K, hK, hA⟩ => ?_⟩
  · rw [← h] at hP ⊢
    exact hα.layer P hP hPP
  · rw [← h] at hK
    exact hα.comps K hK
  · rw [← h] at hK
    exact hα.a6 ⟨K, hK, hA⟩

theorem pow_apply_eq_of_fix' {G : Type*} [Group G] {α : MulAut G} {x : G} (h : α x = x)
    (n : ℕ) : (α ^ n) x = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, h]

theorem fixSubgroup_pow_eq_of_pow_pow' {G : Type*} [Group G] {α : MulAut G} {r s : ℕ}
    (h : (α ^ r) ^ s = α) : fixSubgroup (α ^ r) = fixSubgroup α := by
  ext x
  rw [mem_fixSubgroup, mem_fixSubgroup]
  exact ⟨fun hx => by rw [← h]; exact pow_apply_eq_of_fix' hx s,
    fun hx => pow_apply_eq_of_fix' hx r⟩

theorem lieCompExport_of_conj {q : ℕ} {G : Type} [Group G] (γ β : MulAut G)
    (h : LieCompExport q (γ * β * γ⁻¹)) : LieCompExport q β := by
  refine LieCompExport.of_congr (γ : G ≃* G) ?_
  have hc : MulAut.congr (γ : G ≃* G) β = γ * β * γ⁻¹ := by
    ext x
    rfl
  rw [hc]
  exact h

theorem characteristic_eq_lieIndexChar (d : TauCeti.LieTypeIndex) :
    d.characteristic = lieIndexChar d := by
  cases d <;> simp [lieIndexChar]

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
