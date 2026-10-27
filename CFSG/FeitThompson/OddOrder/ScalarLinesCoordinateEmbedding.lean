module

public import CFSG.FeitThompson.Foundations.FiniteFieldUnitsCyclic
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {q : ℕ}

theorem existsUnique_units_forall_apply_eq_smul {L : Submodule k V} (hL : finrank k L = 1)
    (a : V ≃ₗ[k] V) (ha : ∀ v ∈ L, a v ∈ L) :
    ∃! c : kˣ, ∀ v ∈ L, a v = (c : k) • v := by
  have hne : L ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hL
    exact absurd hL (by norm_num)
  obtain ⟨v₀, hv₀L, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hspan : L = k ∙ v₀ := eq_span_singleton_of_mem_of_finrank_eq_one hL hv₀L hv₀
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hspan ▸ ha v₀ hv₀L)
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_smul] at hc
    exact hv₀ (by simpa using a.map_eq_zero_iff.1 hc.symm)
  refine ⟨Units.mk0 c hc0, ?_, ?_⟩
  · intro v hv
    rw [hspan] at hv
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [map_smul, ← hc, Units.val_mk0, smul_comm]
  · intro c' hc'
    have h : c • v₀ = (c' : k) • v₀ := hc.trans (hc' v₀ hv₀L)
    have h2 : (c - (c' : k)) • v₀ = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.1 h2 with h' | h'
    · exact Units.ext (sub_eq_zero.1 h').symm
    · exact absurd h' hv₀

noncomputable def zmodNeZeroEquivFin (q : ℕ) [NeZero q] :
    {i : ZMod q // i ≠ 0} ≃ Fin (q - 1) := by
  classical
  refine Finite.equivFinOfCardEq ?_
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_subtype_compl]

structure ScalarLineSystem (k V : Type*) [Field k] [AddCommGroup V] [Module k V] (q : ℕ) where
  prime_index : q.Prime
  L : ZMod q → Submodule k V
  finrank_L : ∀ i, finrank k (L i) = 1
  b : V ≃ₗ[k] V
  A : Subgroup (V ≃ₗ[k] V)
  indep_L : iSupIndep L
  iSup_L : ⨆ i, L i = ⊤
  orderOf_b : orderOf b = q
  map_b_L : ∀ i, (L i).map (b : V →ₗ[k] V) = L (i + 1)
  A_ne_bot : A ≠ ⊥
  map_L : ∀ a ∈ A, ∀ i, (L i).map ((a : V ≃ₗ[k] V) : V →ₗ[k] V) = L i
  b_mem_normalizer : b ∈ Subgroup.normalizer A
  inf_centralizer_b : A ⊓ Subgroup.centralizer {b} = ⊥

namespace ScalarLineSystem

theorem neZero_index (S : ScalarLineSystem k V q) : NeZero q :=
  ⟨Nat.Prime.ne_zero S.prime_index⟩

variable (S : ScalarLineSystem k V q)

theorem eq_one_of_commute {a : V ≃ₗ[k] V} (ha : a ∈ S.A) (hab : Commute a S.b) : a = 1 := by
  have h : a ∈ S.A ⊓ Subgroup.centralizer {S.b} :=
    ⟨ha, Subgroup.mem_centralizer_singleton_iff.2 hab⟩
  rw [S.inf_centralizer_b] at h
  simpa using h

theorem mem_L_of_mem_L {a : V ≃ₗ[k] V} (ha : a ∈ S.A) (i : ZMod q) {v : V} (hv : v ∈ S.L i) :
    a v ∈ S.L i := by
  have := Submodule.mem_map_of_mem (f := ((a : V ≃ₗ[k] V) : V →ₗ[k] V)) hv
  rwa [S.map_L a ha i] at this

theorem symm_b_mem_L (i : ZMod q) {v : V} (hv : v ∈ S.L (i + 1)) : S.b.symm v ∈ S.L i := by
  rw [← S.map_b_L i] at hv
  obtain ⟨y, hy, hyv⟩ := Submodule.mem_map.1 hv
  simpa [← hyv] using hy

theorem conj_mem {a : V ≃ₗ[k] V} (ha : a ∈ S.A) : S.b * a * S.b⁻¹ ∈ S.A :=
  (Subgroup.mem_normalizer_iff.1 S.b_mem_normalizer a).1 ha

theorem conj_inv_mem {a : V ≃ₗ[k] V} (ha : a ∈ S.A) : S.b⁻¹ * a * S.b ∈ S.A := by
  simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ S.b_mem_normalizer) a).1 ha

noncomputable def lineScalar (i : ZMod q) (a : S.A) : kˣ :=
  (existsUnique_units_forall_apply_eq_smul (S.finrank_L i) (a : V ≃ₗ[k] V)
    (fun _ hv => S.mem_L_of_mem_L a.2 i hv)).choose

theorem apply_eq_lineScalar_smul (i : ZMod q) (a : S.A) {v : V} (hv : v ∈ S.L i) :
    (a : V ≃ₗ[k] V) v = (S.lineScalar i a : k) • v :=
  (existsUnique_units_forall_apply_eq_smul (S.finrank_L i) (a : V ≃ₗ[k] V)
    (fun _ hv => S.mem_L_of_mem_L a.2 i hv)).choose_spec.1 v hv

theorem eq_lineScalar (i : ZMod q) (a : S.A) {c : kˣ}
    (hc : ∀ v ∈ S.L i, (a : V ≃ₗ[k] V) v = (c : k) • v) : c = S.lineScalar i a :=
  (existsUnique_units_forall_apply_eq_smul (S.finrank_L i) (a : V ≃ₗ[k] V)
    (fun _ hv => S.mem_L_of_mem_L a.2 i hv)).choose_spec.2 c hc

theorem lineScalar_mul (i : ZMod q) (a a' : S.A) :
    S.lineScalar i (a * a') = S.lineScalar i a * S.lineScalar i a' := by
  refine (S.eq_lineScalar i (a * a') ?_).symm
  intro v hv
  have h1 : ((a * a' : S.A) : V ≃ₗ[k] V) v = (a : V ≃ₗ[k] V) ((a' : V ≃ₗ[k] V) v) := by
    simp [LinearEquiv.mul_apply]
  rw [h1, S.apply_eq_lineScalar_smul i a' hv, map_smul, S.apply_eq_lineScalar_smul i a hv]
  simp [smul_smul, mul_comm]

theorem lineScalar_one (i : ZMod q) : S.lineScalar i 1 = 1 :=
  (S.eq_lineScalar i 1 (fun v _ => by simp)).symm

noncomputable def lineScalarHom (i : ZMod q) : S.A →* kˣ where
  toFun := S.lineScalar i
  map_one' := S.lineScalar_one i
  map_mul' := S.lineScalar_mul i

@[simp] theorem lineScalarHom_apply (i : ZMod q) (a : S.A) :
    S.lineScalarHom i a = S.lineScalar i a := (rfl)

theorem lineScalar_inv (i : ZMod q) (a : S.A) :
    S.lineScalar i a⁻¹ = (S.lineScalar i a)⁻¹ := by
  simpa using map_inv (S.lineScalarHom i) a

theorem lineScalar_conj (i : ZMod q) (a : S.A) :
    S.lineScalar (i + 1) ⟨S.b * a * S.b⁻¹, S.conj_mem a.2⟩ = S.lineScalar i a := by
  refine (S.eq_lineScalar (i + 1) ⟨S.b * a * S.b⁻¹, S.conj_mem a.2⟩ ?_).symm
  intro v hv
  have hb : S.b.symm v ∈ S.L i := S.symm_b_mem_L i hv
  change (S.b * (a : V ≃ₗ[k] V) * S.b⁻¹) v = _
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  change S.b ((a : V ≃ₗ[k] V) (S.b.symm v)) = _
  rw [S.apply_eq_lineScalar_smul i a hb, map_smul, LinearEquiv.apply_symm_apply]

theorem apply_eq_smul_of_forall_lineScalar_eq {a : S.A} {c : kˣ}
    (h : ∀ i, S.lineScalar i a = c) (v : V) : (a : V ≃ₗ[k] V) v = (c : k) • v := by
  have hspan : Submodule.span k (⋃ i, (S.L i : Set V)) = ⊤ := by
    rw [← Submodule.iSup_eq_span, S.iSup_L]
  have key := LinearMap.ext_on (σ₁₂ := RingHom.id k) (f := ((a : V ≃ₗ[k] V) : V →ₗ[k] V))
    (g := (c : k) • LinearMap.id) hspan ?_
  · exact LinearMap.congr_fun key v
  · rintro w hw
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hw
    simp [S.apply_eq_lineScalar_smul i a hi, h i]

theorem eq_one_of_forall_lineScalar_eq {a : S.A} {c : kˣ} (h : ∀ i, S.lineScalar i a = c) :
    a = 1 := by
  have hscal := S.apply_eq_smul_of_forall_lineScalar_eq h
  have hcomm : Commute (a : V ≃ₗ[k] V) S.b := by
    apply LinearEquiv.toLinearMap_injective
    ext v
    change ((a : V ≃ₗ[k] V) * S.b) v = (S.b * (a : V ≃ₗ[k] V)) v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hscal, hscal, map_smul]
  exact Subtype.ext (S.eq_one_of_commute a.2 hcomm)

theorem eq_of_forall_lineScalar_eq {a a' : S.A}
    (h : ∀ i, S.lineScalar i a = S.lineScalar i a') : a = a' := by
  have h1 : ∀ i, S.lineScalar i (a * a'⁻¹) = 1 := fun i => by
    rw [S.lineScalar_mul, S.lineScalar_inv, h i, mul_inv_cancel]
  have := S.eq_one_of_forall_lineScalar_eq h1
  rwa [mul_inv_eq_one] at this

theorem isMulCommutative_A : IsMulCommutative S.A :=
  ⟨⟨fun a a' => S.eq_of_forall_lineScalar_eq fun i => by
    rw [S.lineScalar_mul, S.lineScalar_mul, mul_comm]⟩⟩

theorem lineScalarHom_range_add_one (i : ZMod q) :
    (S.lineScalarHom (i + 1)).range = (S.lineScalarHom i).range := by
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    refine ⟨⟨S.b⁻¹ * a * S.b, S.conj_inv_mem a.2⟩, ?_⟩
    have h := S.lineScalar_conj i ⟨S.b⁻¹ * a * S.b, S.conj_inv_mem a.2⟩
    simp only [lineScalarHom_apply]
    rw [← h]
    congr 1
    exact Subtype.ext (by group)
  · rintro x ⟨a, rfl⟩
    exact ⟨⟨S.b * a * S.b⁻¹, S.conj_mem a.2⟩, by simpa using S.lineScalar_conj i a⟩

theorem lineScalarHom_range_add_natCast (i : ZMod q) (n : ℕ) :
    (S.lineScalarHom (i + (n : ZMod q))).range = (S.lineScalarHom i).range := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h : (i + ((n + 1 : ℕ) : ZMod q)) = (i + (n : ZMod q)) + 1 := by push_cast; ring
      rw [h, S.lineScalarHom_range_add_one, ih]

theorem lineScalarHom_range_eq (i j : ZMod q) :
    (S.lineScalarHom i).range = (S.lineScalarHom j).range := by
  have := S.neZero_index
  have key : ∀ l : ZMod q, (S.lineScalarHom l).range = (S.lineScalarHom 0).range := fun l => by
    simpa using S.lineScalarHom_range_add_natCast 0 l.val
  rw [key i, key j]

noncomputable def scalarImage : Subgroup kˣ := (S.lineScalarHom 0).range

theorem lineScalarHom_range_eq_scalarImage (i : ZMod q) :
    (S.lineScalarHom i).range = S.scalarImage := S.lineScalarHom_range_eq i 0

theorem lineScalar_mem_scalarImage (i : ZMod q) (a : S.A) : S.lineScalar i a ∈ S.scalarImage := by
  rw [← S.lineScalarHom_range_eq_scalarImage i]
  exact ⟨a, rfl⟩

theorem scalarImage_ne_bot : S.scalarImage ≠ ⊥ := by
  intro h
  refine S.A_ne_bot (S.A.eq_bot_iff_forall.2 fun a ha => ?_)
  have h1 : ∀ i, S.lineScalar i ⟨a, ha⟩ = 1 := fun i => by
    have hmem := S.lineScalar_mem_scalarImage i ⟨a, ha⟩
    rw [h] at hmem
    simpa using hmem
  simpa using S.eq_one_of_forall_lineScalar_eq h1

noncomputable def scalarOrder : ℕ := Nat.card S.scalarImage

theorem scalarOrder_eq_natCard : S.scalarOrder = Nat.card S.scalarImage := (rfl)

theorem scalarOrder_dvd_card_sub_one : S.scalarOrder ∣ Nat.card k - 1 := by
  rw [S.scalarOrder_eq_natCard, ← Nat.card_units k,
    natCard_eq_natCard_range_leftCoset_mul_natCard S.scalarImage]
  exact Dvd.intro_left _ rfl

noncomputable def lineScalarHomD (i : ZMod q) : S.A →* S.scalarImage :=
  (S.lineScalarHom i).codRestrict S.scalarImage (S.lineScalar_mem_scalarImage i)

@[simp] theorem coe_lineScalarHomD_apply (i : ZMod q) (a : S.A) :
    ((S.lineScalarHomD i a : S.scalarImage) : kˣ) = S.lineScalar i a := (rfl)

noncomputable def ratioHom : S.A →* ({i : ZMod q // i ≠ 0} → S.scalarImage) :=
  MonoidHom.pi fun i => S.lineScalarHomD i.1 / S.lineScalarHomD 0

theorem coe_ratioHom_apply (a : S.A) (i : {i : ZMod q // i ≠ 0}) :
    ((S.ratioHom a i : S.scalarImage) : kˣ) = S.lineScalar i.1 a * (S.lineScalar 0 a)⁻¹ := by
  simp [ratioHom, div_eq_mul_inv]

theorem injective_ratioHom : Function.Injective S.ratioHom := by
  rw [injective_iff_map_eq_one]
  intro a ha
  refine S.eq_one_of_forall_lineScalar_eq (c := S.lineScalar 0 a) fun i => ?_
  by_cases hi : i = 0
  · rw [hi]
  · have h := congrFun ha ⟨i, hi⟩
    have h2 : S.lineScalar i a * (S.lineScalar 0 a)⁻¹ = 1 := by
      have hco := S.coe_ratioHom_apply a ⟨i, hi⟩
      rw [h] at hco
      simpa using hco.symm
    rwa [mul_inv_eq_one] at h2

section Finite

variable [Finite k]

theorem isCyclic_scalarImage : IsCyclic S.scalarImage :=
  haveI := isCyclic_units_of_finite_field k
  Subgroup.isCyclic _

theorem one_lt_scalarOrder : 1 < S.scalarOrder := by
  rw [S.scalarOrder_eq_natCard]
  exact (Subgroup.one_lt_card_iff_ne_bot _).2 S.scalarImage_ne_bot

noncomputable def ratioMulEquiv :
    ({i : ZMod q // i ≠ 0} → S.scalarImage) ≃*
      (Fin (q - 1) → Multiplicative (ZMod S.scalarOrder)) :=
  haveI := S.neZero_index
  MulEquiv.arrowCongr (zmodNeZeroEquivFin q) (zmodCyclicMulEquiv S.isCyclic_scalarImage).symm

noncomputable def ratioZModHom :
    S.A →* (Fin (q - 1) → Multiplicative (ZMod S.scalarOrder)) :=
  S.ratioMulEquiv.toMonoidHom.comp S.ratioHom

theorem injective_ratioZModHom : Function.Injective S.ratioZModHom :=
  S.ratioMulEquiv.injective.comp S.injective_ratioHom

noncomputable def mulEquivRange : S.A ≃* S.ratioZModHom.range :=
  MonoidHom.ofInjective S.injective_ratioZModHom

end Finite

end ScalarLineSystem

end

end CFSG.FeitThompson
