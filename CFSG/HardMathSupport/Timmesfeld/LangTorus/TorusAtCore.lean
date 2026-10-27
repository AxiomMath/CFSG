module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false



theorem conj_inv_comp_conj {G : Type*} [Group G] (g : G) :
    (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply]
  group

theorem conj_conj_inv {G : Type*} [Group G] (g x : G) :
    g⁻¹ * (g * x * g⁻¹) * g = x := by group


theorem commutator_eq_of_perfect_of_relIndex_le_three {G : Type*} [Group G] {I M : Subgroup G}
    [Finite M] (hIM : I ≤ M) (hperf : ⁅I, I⁆ = I) (hidx : I.relIndex M ≤ 3) : ⁅M, M⁆ = I := by
  classical
  set I' : Subgroup ↥M := I.subgroupOf M with hI'
  have hI'idx : I'.index ≤ 3 := hidx
  have hI'perf : ⁅I', I'⁆ = I' := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, hI', Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hIM, hperf]
  have hfin : Finite (↥M ⧸ I') := Subgroup.finite_quotient_of_finiteIndex
  have hcard : Nat.card (↥M ⧸ I') ≤ 3 := hI'idx
  let φ := MulAction.toPermHom ↥M (↥M ⧸ I')
  haveI : Group.IsSolvable (Equiv.Perm (↥M ⧸ I')) := Equiv.Perm.isSolvable (by omega)
  have hH : I'.map φ = ⊥ := by
    by_contra hne
    have := Group.IsSolvable.commutator_lt_of_ne_bot hne
    rw [← Subgroup.map_commutator, hI'perf] at this
    exact lt_irrefl _ this
  have hker : I' ≤ φ.ker := fun x hx => by
    have : φ x ∈ I'.map φ := ⟨x, hx, rfl⟩
    rw [hH] at this
    exact this
  have hcore : I'.normalCore = φ.ker := Subgroup.normalCore_eq_ker I'
  have hnorm : I'.Normal := by
    have : I' = I'.normalCore := le_antisymm (hcore ▸ hker) (Subgroup.normalCore_le I')
    rw [this]
    infer_instance
  have hcomm : IsMulCommutative (↥M ⧸ I') := by
    refine IsMulCommutative.of_comm fun a b => ?_
    exact mul_comm_of_card_le_three (Nat.card_pos) hcard a b
  have hle : ⁅(⊤ : Subgroup ↥M), ⊤⁆ ≤ I' :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.1 hcomm
  apply le_antisymm
  · have h1 : ⁅M, M⁆ = Subgroup.map M.subtype ⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆ := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [h1]
    calc Subgroup.map M.subtype ⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆ ≤ I'.map M.subtype :=
          Subgroup.map_mono hle
      _ = I := by rw [hI', Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hIM]
  · calc I = ⁅I, I⁆ := hperf.symm
      _ ≤ ⁅M, M⁆ := Subgroup.commutator_mono hIM hIM

namespace LangDatum

variable {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L)

@[expose] noncomputable def fix : Subgroup (ModGL τ L) :=
  adjointGroup τ L ⊓ D.Φ.eqLocus (MonoidHom.id _)

theorem mem_fix {y : ModGL τ L} : y ∈ D.fix ↔ y ∈ adjointGroup τ L ∧ D.Φ y = y := Iff.rfl

theorem torus_le_model : D.torus ≤ D.model := by
  intro x hx
  obtain ⟨h1, h2⟩ := mem_twistedTorusOf.1 hx
  exact ⟨torusGroup_le_adjointGroup' h1, h2⟩

theorem map_conj_model : D.model.map (MulAut.conj D.g0).toMonoidHom = D.fix := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxC, hx⟩, rfl⟩
    refine ⟨(adjointGroup τ L).mul_mem ((adjointGroup τ L).mul_mem D.g0_mem hxC)
      ((adjointGroup τ L).inv_mem D.g0_mem), ?_⟩
    change D.Φ (D.g0 * x * D.g0⁻¹) = D.g0 * x * D.g0⁻¹
    have hx' : D.n * D.Φ x * D.n⁻¹ = x := hx
    rw [map_mul, map_mul, map_inv, D.lang]
    calc D.g0 * D.n * D.Φ x * (D.g0 * D.n)⁻¹ = D.g0 * (D.n * D.Φ x * D.n⁻¹) * D.g0⁻¹ := by group
      _ = D.g0 * x * D.g0⁻¹ := by rw [hx']
  · rintro ⟨hyC, hy⟩
    refine ⟨D.g0⁻¹ * y * D.g0, ⟨(adjointGroup τ L).mul_mem ((adjointGroup τ L).mul_mem ((adjointGroup τ L).inv_mem D.g0_mem) hyC)
      D.g0_mem, ?_⟩, ?_⟩
    · change D.n * D.Φ (D.g0⁻¹ * y * D.g0) * D.n⁻¹ = D.g0⁻¹ * y * D.g0
      have hy' : D.Φ y = y := hy
      rw [map_mul, map_mul, map_inv, D.lang, hy']
      group
    · change D.g0 * (D.g0⁻¹ * y * D.g0) * D.g0⁻¹ = y
      group

theorem map_conj_Γ : D.Γ.map (MulAut.conj D.g0).toMonoidHom = ⁅D.fix, D.fix⁆ := by
  rw [LangDatum.Γ, Subgroup.map_commutator, map_conj_model]

theorem isMulCommutative_torus : IsMulCommutative D.torus := by
  refine IsMulCommutative.of_comm fun a b => ?_
  obtain ⟨x, hx⟩ := torusGroup_le_range_rootDiagUnitHom (mem_twistedTorusOf.1 a.2).1
  obtain ⟨y, hy⟩ := torusGroup_le_range_rootDiagUnitHom (mem_twistedTorusOf.1 b.2).1
  apply Subtype.ext
  show (a : ModGL τ L) * b = b * a
  rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm x y]

end LangDatum

structure LangDescent {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L) (p : ℕ)
    {C : Type} [Group C] (ι : C →* ModGL τ L) : Prop where
  finite_fix : Finite D.fix
  range_le : ι.range ≤ D.fix
  pgroup_le : ∀ P : Subgroup (ModGL τ L), P ≤ D.fix → IsPGroup p P → P ≤ ι.range
  derived : ⁅D.fix, D.fix⁆ = ι.range

namespace LangDescent

variable {τ : Tag} {L : Type} [Field L] {D : LangDatum τ L} {p : ℕ}
  {C : Type} [Group C] {ι : C →* ModGL τ L}

theorem model_eq (D : LangDatum τ L) :
    D.model = D.fix.map (MulAut.conj D.g0⁻¹).toMonoidHom := by
  rw [← LangDatum.map_conj_model, Subgroup.map_map]
  rw [conj_inv_comp_conj, Subgroup.map_id]

theorem Γ_eq (h : LangDescent D p ι) :
    D.Γ = ι.range.map (MulAut.conj D.g0⁻¹).toMonoidHom := by
  have h1 := D.map_conj_Γ
  rw [h.derived] at h1
  rw [← h1, Subgroup.map_map]
  rw [conj_inv_comp_conj, Subgroup.map_id]

theorem Γ_le_model (h : LangDescent D p ι) : D.Γ ≤ D.model := by
  rw [h.Γ_eq, model_eq]
  exact Subgroup.map_mono h.range_le

theorem finite_model (h : LangDescent D p ι) : Finite D.model := by
  have := h.finite_fix
  rw [model_eq]
  exact Finite.of_surjective ((MulAut.conj D.g0⁻¹).toMonoidHom.subgroupMap D.fix)
    ((MulAut.conj D.g0⁻¹).toMonoidHom.subgroupMap_surjective D.fix)

theorem pgroup_le_Γ (h : LangDescent D p ι) (P : Subgroup (ModGL τ L)) (hP : P ≤ D.model)
    (hpP : IsPGroup p P) : P ≤ D.Γ := by
  have hmap : P.map (MulAut.conj D.g0).toMonoidHom ≤ D.fix := by
    rw [← LangDatum.map_conj_model]
    exact Subgroup.map_mono hP
  have hpg : IsPGroup p (P.map (MulAut.conj D.g0).toMonoidHom) := hpP.map _
  have h1 := h.pgroup_le _ hmap hpg
  intro x hx
  have : D.g0 * x * D.g0⁻¹ ∈ ι.range := h1 ⟨x, hx, rfl⟩
  rw [h.Γ_eq]
  exact ⟨_, this, conj_conj_inv _ _⟩

noncomputable def mulEquiv (h : LangDescent D p ι) (hι : Function.Injective ι) : C ≃* D.Γ :=
  (MonoidHom.ofInjective hι).trans
    ((Subgroup.equivMapOfInjective ι.range (MulAut.conj D.g0⁻¹).toMonoidHom
      (MulAut.conj D.g0⁻¹).injective).trans (MulEquiv.subgroupCongr h.Γ_eq.symm))

end LangDescent

theorem exists_langSetup_of_sylow {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (hF : FrobeniusOnRoots) (D : LangDatum τ L) {p : ℕ} (hp : p.Prime) (hq : 5 ≤ p ∨ 4 ≤ D.q)
    (hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0) (hpq : ¬ p ∣ D.q)
    {C : Type} [Group C] (ι : C →* ModGL τ L) (hι : Function.Injective ι)
    (hd : LangDescent D p ι)
    (hsyl : ∃ S₀ : Sylow p D.Γ, (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) :
    ∃ S : LangSetup τ L p, S.D = D ∧
      (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
      Nonempty (C ≃* S.Γ) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hfm := hd.finite_model
  obtain ⟨ρ, hρ⟩ := hF τ L D
  have hcomm := D.isMulCommutative_torus
  have hcomm' : IsMulCommutative ↥(D.torus ⊓ D.Γ) :=
    IsMulCommutative.of_comm fun a b => Subtype.ext (by
      have := hcomm
      exact setLike_mul_comm a.2.1 b.2.1)
  let E : Subgroup (ModGL τ L) := torsionSubgroup (D.torus ⊓ D.Γ) hcomm' p
  exact ⟨⟨D, ρ, hρ, E, hp, hq, hqpow, hpq, hfm, fun x hx => hx.1, fun x hx => hx.2,
    fun x hx hxp => ⟨hx, hxp⟩⟩, rfl, hsyl, ⟨hd.mulEquiv hι⟩⟩

theorem exists_sylow_Γ_of_conj {τ : Tag} {L : Type} [Field L] {D : LangDatum τ L} {p : ℕ}
    (hp : p.Prime) {C : Type} [Group C] {ι : C →* ModGL τ L} (hι : Function.Injective ι)
    (hd : LangDescent D p ι) (S : Sylow p C)
    (hS : ∀ x ∈ (S : Subgroup C), D.g0⁻¹ * ι x * D.g0 ∈ D.torus) :
    ∃ S₀ : Sylow p D.Γ, (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hfm := hd.finite_model
  haveI : Finite D.Γ :=
    Finite.of_injective (Subgroup.inclusion hd.Γ_le_model) (Subgroup.inclusion_injective _)
  let e : C ≃* D.Γ := hd.mulEquiv hι
  haveI : Finite C := Finite.of_equiv _ e.symm.toEquiv
  have he : ∀ x : C, ((e x : D.Γ) : ModGL τ L) = D.g0⁻¹ * ι x * D.g0 := fun x => by
    change (MulAut.conj D.g0⁻¹) (ι x) = _
    rw [MulAut.conj_apply, inv_inv]
  have hcard : Nat.card ((S : Subgroup C).map e.toMonoidHom) =
      p ^ (Nat.card D.Γ).factorization p := by
    rw [Subgroup.card_map_of_injective e.injective, Sylow.card_eq_multiplicity,
      Nat.card_congr e.toEquiv]
  refine ⟨Sylow.ofCard _ hcard, ?_⟩
  rw [Sylow.coe_ofCard]
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, he]
  exact hS x hx

theorem exists_langSetup_of_descent_sub {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (hF : FrobeniusOnRoots) (D : LangDatum τ L) {p : ℕ} (hp : p.Prime) (hq : 5 ≤ p ∨ 4 ≤ D.q)
    (hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0) (hpq : ¬ p ∣ D.q)
    {C : Type} [Group C] (ι : C →* ModGL τ L) (hι : Function.Injective ι)
    (hd : LangDescent D p ι)
    (hord : ∃ H : Subgroup (ModGL τ L), H ≤ D.torus ∧
      (Nat.card C).factorization p ≤ (Nat.card H).factorization p) :
    ∃ S : LangSetup τ L p, S.D = D ∧
      (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
      Nonempty (C ≃* S.Γ) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hfm := hd.finite_model
  have hTM := D.torus_le_model
  haveI hTfin : Finite D.torus :=
    Finite.of_injective (Subgroup.inclusion hTM) (Subgroup.inclusion_injective hTM)
  have hΓfin : Finite D.Γ :=
    Finite.of_injective (Subgroup.inclusion hd.Γ_le_model) (Subgroup.inclusion_injective _)
  obtain ⟨H, hHT, hCH⟩ := hord
  have hord' : (Nat.card C).factorization p ≤ (Nat.card D.torus).factorization p := by
    refine hCH.trans ?_
    haveI : Finite H :=
      Finite.of_injective (Subgroup.inclusion hHT) (Subgroup.inclusion_injective hHT)
    have hdvd : Nat.card H ∣ Nat.card D.torus := Subgroup.card_dvd_of_le hHT
    exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hdvd p
  refine exists_langSetup_of_sylow hF D hp hq hqpow hpq ι hι hd ?_
  obtain ⟨P0⟩ : Nonempty (Sylow p D.torus) := inferInstance
  set P1 : Subgroup (ModGL τ L) := (P0 : Subgroup D.torus).map D.torus.subtype with hP1
  have hP1T : P1 ≤ D.torus := Subgroup.map_subtype_le _
  have hP1p : IsPGroup p P1 := P0.isPGroup'.map _
  have hP1Γ : P1 ≤ D.Γ := hd.pgroup_le_Γ P1 (hP1T.trans hTM) hP1p
  have hP1card : Nat.card P1 = p ^ (Nat.card D.torus).factorization p := by
    rw [hP1, Subgroup.card_map_of_injective D.torus.subtype_injective, Sylow.card_eq_multiplicity]
  set P2 : Subgroup D.Γ := P1.subgroupOf D.Γ with hP2
  have hP2card : Nat.card P2 = Nat.card P1 := by
    rw [← Subgroup.card_map_of_injective D.Γ.subtype_injective, hP2, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hP1Γ]
  have hΓcard : Nat.card D.Γ = Nat.card C := (Nat.card_congr (hd.mulEquiv hι).toEquiv).symm
  have hle : (Nat.card D.torus).factorization p ≤ (Nat.card D.Γ).factorization p := by
    have hdvd : p ^ (Nat.card D.torus).factorization p ∣ Nat.card D.Γ := by
      rw [← hP1card, ← hP2card]
      exact Subgroup.card_subgroup_dvd_card P2
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').1 hdvd
  have hcard : Nat.card P2 = p ^ (Nat.card D.Γ).factorization p := by
    rw [hP2card, hP1card]
    congr 1
    rw [hΓcard]
    exact le_antisymm (hΓcard ▸ hle) hord'
  refine ⟨Sylow.ofCard P2 hcard, ?_⟩
  rw [Sylow.coe_ofCard]
  intro x hx
  exact Subgroup.mem_subgroupOf.2 (hP1T hx)

theorem exists_langSetup_of_descent {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (hF : FrobeniusOnRoots) (D : LangDatum τ L) {p : ℕ} (hp : p.Prime) (hq : 5 ≤ p ∨ 4 ≤ D.q)
    (hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0) (hpq : ¬ p ∣ D.q)
    {C : Type} [Group C] (ι : C →* ModGL τ L) (hι : Function.Injective ι)
    (hd : LangDescent D p ι)
    (hord : (Nat.card C).factorization p ≤ (Nat.card D.torus).factorization p) :
    ∃ S : LangSetup τ L p, S.D = D ∧
      (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
      Nonempty (C ≃* S.Γ) :=
  exists_langSetup_of_descent_sub hF D hp hq hqpow hpq ι hι hd ⟨D.torus, le_rfl, hord⟩

end CFSG.HardMathSupport.Timmesfeld.LangTorus
