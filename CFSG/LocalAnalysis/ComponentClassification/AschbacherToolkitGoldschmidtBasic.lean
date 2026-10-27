module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Sylow

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Goldschmidt

open CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTheorem3

theorem center_eq_bot_of_nontrivial {G : Type*} [Group G] [IsSimpleGroup G]
    (h : Nontrivial (G ⧸ Subgroup.center G)) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hb | ht
  · exact hb
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    apply hab
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    rw [QuotientGroup.eq, ht]
    exact Subgroup.mem_top _

section Action

variable {Y : Type} [Group Y] {X E : Subgroup Y}

@[expose] def conjAct (hEX : E ≤ Subgroup.normalizer (X : Set Y)) : ↥E →* MulAut ↥X where
  toFun e :=
    { toFun := fun x => ⟨(e : Y) * x * (e : Y)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hEX e.2) x).mp x.2⟩
      invFun := fun x => ⟨(e : Y)⁻¹ * x * (e : Y), by
        apply (Subgroup.mem_normalizer_iff.mp (hEX e.2) ((e : Y)⁻¹ * x * (e : Y))).mpr
        have h : (e : Y) * ((e : Y)⁻¹ * x * (e : Y)) * (e : Y)⁻¹ = x := by group
        rw [h]
        exact x.2⟩
      left_inv := fun x => Subtype.ext (by
        change (e : Y)⁻¹ * ((e : Y) * x * (e : Y)⁻¹) * (e : Y) = x
        group)
      right_inv := fun x => Subtype.ext (by
        change (e : Y) * ((e : Y)⁻¹ * x * (e : Y)) * (e : Y)⁻¹ = x
        group)
      map_mul' := fun x y => Subtype.ext (by
        change (e : Y) * ((x : Y) * y) * (e : Y)⁻¹ =
          (e : Y) * x * (e : Y)⁻¹ * ((e : Y) * y * (e : Y)⁻¹)
        group) }
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change ((1 : E) : Y) * x * ((1 : E) : Y)⁻¹ = x
    simp
  map_mul' e e' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change ((e * e' : E) : Y) * x * ((e * e' : E) : Y)⁻¹ =
      (e : Y) * ((e' : Y) * x * (e' : Y)⁻¹) * (e : Y)⁻¹
    simp only [Subgroup.coe_mul]
    group

theorem conjAct_apply (hEX : E ≤ Subgroup.normalizer (X : Set Y)) (e : E) (x : X) :
    ((conjAct hEX e x : X) : Y) = (e : Y) * x * (e : Y)⁻¹ := rfl

theorem card_eq_mul_card_range (hEX : E ≤ Subgroup.normalizer (X : Set Y)) :
    Nat.card E = Nat.card (E ⊓ Subgroup.centralizer (X : Set Y) : Subgroup Y) *
      Nat.card (conjAct hEX).range := by
  have hmemC : ∀ e : (conjAct hEX).ker,
      ((e : E) : Y) ∈ Subgroup.centralizer (X : Set Y) := by
    intro e
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := congrArg (fun φ : MulAut X => ((φ ⟨x, hx⟩ : X) : Y)) (MonoidHom.mem_ker.mp e.2)
    change ((e : E) : Y) * x * ((e : E) : Y)⁻¹ = x at h
    calc x * ((e : E) : Y) = ((e : E) : Y) * x * ((e : E) : Y)⁻¹ * ((e : E) : Y) := by rw [h]
      _ = ((e : E) : Y) * x := by group
  have hmemK : ∀ c : (E ⊓ Subgroup.centralizer (X : Set Y) : Subgroup Y),
      (⟨c, (Subgroup.mem_inf.mp c.2).1⟩ : E) ∈ (conjAct hEX).ker := by
    intro c
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (c : Y) * x * (c : Y)⁻¹ = x
    have h := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp c.2).2 x x.2
    rw [← h]
    group
  have hker : Nat.card (conjAct hEX).ker =
      Nat.card (E ⊓ Subgroup.centralizer (X : Set Y) : Subgroup Y) :=
    Nat.card_congr
      { toFun := fun e => ⟨((e : E) : Y), Subgroup.mem_inf.mpr ⟨(e : E).2, hmemC e⟩⟩
        invFun := fun c => ⟨⟨c, (Subgroup.mem_inf.mp c.2).1⟩, hmemK c⟩
        left_inv := fun e => rfl
        right_inv := fun c => rfl }
  rw [← hker]
  exact (Subgroup.card_ker_mul_card_range (conjAct hEX)).symm

end Action

section Sylow

variable {Y : Type} [Group Y] {X P : Subgroup Y} {Q : Subgroup X}

theorem coe_mem_iff (hQ : Q.map X.subtype = P) {x : X} : (x : Y) ∈ P ↔ x ∈ Q := by
  constructor
  · intro hx
    rw [← hQ] at hx
    obtain ⟨x', hx', hxx'⟩ := hx
    have : x' = x := Subtype.ext hxx'
    rwa [← this]
  · intro hx
    rw [← hQ]
    exact ⟨x, hx, rfl⟩

theorem omegaOne_map (hQ : Q.map X.subtype = P) : (omegaOne Q).map X.subtype = omegaOne P := by
  unfold omegaOne
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hx2⟩, rfl⟩
    exact ⟨(coe_mem_iff hQ).mpr hx, by
      change ((x : Y)) ^ 2 = 1
      rw [← Subgroup.coe_pow, hx2, Subgroup.coe_one]⟩
  · rintro ⟨hy, hy2⟩
    rw [← hQ] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    apply Subtype.ext
    change (x : Y) ^ 2 = 1 at hy2
    rw [Subgroup.coe_pow, hy2, Subgroup.coe_one]

theorem coe_mem_omegaOne_iff (hQ : Q.map X.subtype = P) {x : X} :
    (x : Y) ∈ omegaOne P ↔ x ∈ omegaOne Q := by
  rw [← omegaOne_map hQ]
  constructor
  · rintro ⟨x', hx', hxx'⟩
    have : x' = x := Subtype.ext hxx'
    rwa [← this]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem card_omegaOne (hQ : Q.map X.subtype = P) :
    Nat.card (omegaOne Q) = Nat.card (omegaOne P) := by
  rw [← omegaOne_map hQ, Subgroup.card_map_of_injective X.subtype_injective]

end Sylow

section Properties

variable {Y : Type} [Group Y] {X P E : Subgroup Y} {Q : Subgroup X}

theorem conjAct_range_properties (hQ : Q.map X.subtype = P) (hE : IsElemAbelian 2 E)
    (hEX : E ≤ Subgroup.normalizer (X : Set Y)) (hEP : E ≤ Subgroup.normalizer (P : Set Y))
    (hEcent : ∀ e ∈ E, ∀ x ∈ omegaOne P, e * x = x * e)
    (hEcomm : ∀ e ∈ E, ∀ p ∈ P, e⁻¹ * p⁻¹ * e * p ∈ omegaOne P) :
    ∀ α ∈ (conjAct hEX).range,
      α * α = 1 ∧ (∀ q ∈ Q, α q ∈ Q) ∧ (∀ q ∈ Q, q ^ 2 = 1 → α q = q) ∧
        ∀ q ∈ Q, q⁻¹ * α q ∈ omegaOne Q := by
  rintro _ ⟨e, rfl⟩
  have he2 : (e : Y) ^ 2 = 1 := hE.2 e e.2
  have heinv : (e : Y)⁻¹ = e := by
    rw [sq] at he2
    exact inv_eq_of_mul_eq_one_right he2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_mul]
    have h1 : e * e = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, ← sq, he2, Subgroup.coe_one]
    rw [h1, map_one]
  · intro q hq
    rw [← coe_mem_iff hQ]
    rw [conjAct_apply]
    exact (Subgroup.mem_normalizer_iff.mp (hEP e.2) q).mp ((coe_mem_iff hQ).mpr hq)
  · intro q hq hq2
    apply Subtype.ext
    rw [conjAct_apply]
    have hqo : (q : Y) ∈ omegaOne P := (coe_mem_omegaOne_iff hQ).mpr (mem_omegaOne hq hq2)
    rw [hEcent e e.2 q hqo]
    group
  · intro q hq
    rw [← coe_mem_omegaOne_iff hQ]
    have h := hEcomm e e.2 q ((coe_mem_iff hQ).mpr hq)
    have h' := (omegaOne P).inv_mem h
    have e1 : (((q⁻¹ * conjAct hEX e q : X)) : Y) =
        ((e : Y)⁻¹ * (q : Y)⁻¹ * e * q)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, conjAct_apply]
      calc (q : Y)⁻¹ * ((e : Y) * q * (e : Y)⁻¹) = (q : Y)⁻¹ * e * q * e := by
            rw [heinv]
            group
        _ = (q : Y)⁻¹ * (e : Y)⁻¹ * q * e := by rw [heinv]
        _ = ((e : Y)⁻¹ * (q : Y)⁻¹ * e * q)⁻¹ := by group
    rw [e1]
    exact h'

end Properties

end Goldschmidt

end CFSG.ComponentClassification.AschbacherToolkit
