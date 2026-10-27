module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXEasyModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXTw

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

private theorem fixSubgroup_conj_eq_centralizer_single {T : Type} [Group T] (r : T) :
    fixSubgroup (MulAut.conj r) = Subgroup.centralizer ({r} : Set T) := by
  ext y
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup,
    Subgroup.mem_centralizer_singleton_iff]
  change r * y * r⁻¹ = y ↔ y * r = r * y
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

private theorem modelSel_of_inner_selection {p : ℕ} {T : Type} [Group T] [Finite T]
    (hZ : Subgroup.center T = ⊥)
    (h : ∀ β : MulAut T, β ∈ innAutDerived T → β ^ p = 1 → β ≠ 1 →
      ∀ P : Subgroup T, P ≤ fixSubgroup β → IsPGroup 2 ↥P → P ≠ ⊥ →
        ∃ J : Subgroup T, IsComponentOf J (fixSubgroup β) ∧
          p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) ∧ ⁅P, J⁆ ≠ ⊥ ∧
          P ≤ J ⊔ (fixSubgroup β ⊓ Subgroup.centralizer (J : Set T))) :
    ModelSel p T := by
  intro r hrp hr1 P hPC hP2 hP1
  have hfix := fixSubgroup_conj_eq_centralizer_single r
  have hβ1 : MulAut.conj r ≠ 1 := by
    intro h1
    apply hr1
    have hz : r ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 : r * g * r⁻¹ = g := by
        have := congrArg (fun f : MulAut T => f g) h1
        simpa [MulAut.conj_apply] using this
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    rw [hZ] at hz
    exact Subgroup.mem_bot.1 hz
  have hβp : (MulAut.conj r) ^ p = 1 := by rw [← map_pow, hrp, map_one]
  have hβmem : MulAut.conj r ∈ innAutDerived T :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived T ⟨r, rfl⟩
  obtain ⟨J, hJc, hJp, hJa, hJP⟩ := h _ hβmem hβp hβ1 P (by rw [hfix]; exact hPC) hP2 hP1
  rw [hfix] at hJc hJP
  exact ⟨J, hJc, hJp, hJa, hJP⟩


theorem exists_native_model_twisted {t : TwistTag}
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.TwistedBridgeAll t c) (q : TauCeti.PrimePower)
    (hv : (c q).Valid) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      Nat.card K = (q.p ^ q.exponent) ^ t.order ∧ (∀ x, σ x = x ^ (q.p ^ q.exponent)) ∧
        Nonempty (TauCeti.ValidLieTypeIndex.Group ⟨c q, hv⟩ ≃*
          ↥(graphFixedRootGroup t K σ.toRingHom)) := by
  obtain ⟨K, _, _, hK, -⟩ :=
    CFSG.LieType.SeitzGeneration.exists_field_pow q (m := t.order) t.order_pos
  rw [TauCeti.PrimePower.card_def] at hK
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields t q.prime_p q.exponent_pos K hK
  have hσ' : ∀ x, σ.toRingHom x = x ^ (q.p ^ q.exponent) := fun x => hσ x
  obtain ⟨φ⟩ := hB q hv K (by rw [TauCeti.PrimePower.card_def]; exact hK) σ.toRingHom
    (fun x => by rw [TauCeti.PrimePower.card_def]; exact hσ' x)
  exact ⟨K, inferInstance, inferInstance, σ, hK, hσ,
    ⟨φ.symm.trans (CFSG.TauCetiBridge.Twisted.nativeEquiv q.prime_p q.exponent_pos hK hσ')⟩⟩

private theorem exists_modelSel_E6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid) (hq2 : q.p = 2)
    (hq4 : 4 ≤ q.card) (hpq : p ∣ q.card ^ 2 - 1)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group) :
    ∃ (T : Type) (_ : Group T) (_ : Finite T), Nonempty (X ≃* T) ∧ ModelSel p T := by
  obtain ⟨K, _, _, hK, hKchar, ⟨φ⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  have hK2 : ringChar K = 2 := by
    haveI : CharP K 2 := by rw [← hq2]; exact hKchar
    exact ringChar.eq K 2
  exact ⟨↥(adjointGroup Tag.E6 K), inferInstance, inferInstance, ⟨e.trans φ⟩,
    modelSel_adjointGroup (Or.inr (Or.inr (Or.inl rfl))) hK2 (by rw [hK]; exact hq4) hp hp2
      (by rw [hK]; exact hpq)⟩

private theorem exists_modelSel_twistedE6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type}
    [Group X] (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid)
    (hq2 : q.p = 2) (hq4 : 4 ≤ q.card) (hpq : p ∣ q.card ^ 2 - 1)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) :
    ∃ (T : Type) (_ : Group T) (_ : Finite T), Nonempty (X ≃* T) ∧ ModelSel p T := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨ψ⟩⟩ := exists_native_model_twisted
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv
  have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
  have hK2 : Nat.card K = (2 ^ q.exponent) ^ 2 := by
    rw [hq2] at hK
    exact hK
  have hσ2 : ∀ c, σ c = c ^ (2 ^ q.exponent) := by
    rw [hq2] at hσ
    exact hσ
  rw [hqc] at hq4 hpq
  refine ⟨↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom), inferInstance, inferInstance,
    ⟨e.trans ψ⟩, ?_⟩
  exact modelSel_of_inner_selection (exceptional_fixed_center_trivial TwistTag.E6 K σ)
    fun β hβmem hβp hβ1 P hPβ hP2 hP1 => exists_comp_of_two_twistedE6 q.exponent_pos hK2 σ hσ2
      hq4 hp hp2 hpq β hβmem hβp hβ1 P hPβ hP2 hP1

private theorem exists_modelSel_trialityD4 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type}
    [Group X] (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (hq2 : q.p = 2) (hq4 : 4 ≤ q.card) (hpq : p ∣ q.card ^ 2 - 1)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) :
    ∃ (T : Type) (_ : Group T) (_ : Finite T), Nonempty (X ≃* T) ∧ ModelSel p T := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨ψ⟩⟩ := exists_native_model_twisted
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv
  have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
  have hK3 : Nat.card K = (2 ^ q.exponent) ^ 3 := by
    rw [hq2] at hK
    exact hK
  have hσ2 : ∀ c, σ c = c ^ (2 ^ q.exponent) := by
    rw [hq2] at hσ
    exact hσ
  rw [hqc] at hq4 hpq
  refine ⟨↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom), inferInstance, inferInstance,
    ⟨e.trans ψ⟩, ?_⟩
  exact modelSel_of_inner_selection (exceptional_fixed_center_trivial TwistTag.D4 K σ)
    fun β hβmem hβp hβ1 P hPβ hP2 hP1 => exists_comp_of_two_trialityD4 q.exponent_pos hK3 σ hσ2
      hq4 hp hp2 hpq β hβmem hβp hβ1 P hPβ hP2 hP1

theorem exists_modelSel_e6Easy {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    (h : catalogIs X (t263GE6Easy p)) :
    ∃ (T : Type) (_ : Group T) (_ : Finite T), Nonempty (X ≃* T) ∧ ModelSel p T := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | E6 q =>
      obtain ⟨hq2, hq4, hpq, -⟩ := hi
      exact exists_modelSel_E6 hp hp2 q hv hq2 hq4 hpq e
    | twistedE6 q =>
      obtain ⟨hq2, hq4, hpq, -⟩ := hi
      exact exists_modelSel_twistedE6 hp hp2 q hv hq2 hq4 hpq e
    | _ => exact False.elim hi
  | cyclic r hr => exact False.elim hi
  | alternating n hn => exact False.elim hi
  | sporadic s => exact False.elim hi

theorem exists_modelSel_td4Easy {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    (h : catalogIs X (t263GTD4Easy p)) :
    ∃ (T : Type) (_ : Group T) (_ : Finite T), Nonempty (X ≃* T) ∧ ModelSel p T := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | trialityD4 q =>
      obtain ⟨hq2, hq4, hpq⟩ := hi
      exact exists_modelSel_trialityD4 hp hp2 q hv hq2 hq4 hpq e
    | _ => exact False.elim hi
  | cyclic r hr => exact False.elim hi
  | alternating n hn => exact False.elim hi
  | sporadic s => exact False.elim hi

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
