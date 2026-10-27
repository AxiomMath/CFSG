module

public import CFSG.ClassicalInvolution.Q3.TA3SOLCoreQuot

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution
open scoped MatrixGroups commutatorElement

@[expose] def TwoSL2Shape (X : Type) [Group X] (t : X) (F : Type) [Field F] : Prop :=
  ∃ H₁ H₂ : Subgroup X, H₁ ≤ Subgroup.centralizer ({t} : Set X) ∧
    H₂ ≤ Subgroup.centralizer ({t} : Set X) ∧ (∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) ∧
    Nonempty (H₁ ≃* SL(2, F)) ∧ Nonempty (H₂ ≃* SL(2, F))

@[expose] def NormalSimpleShape (X : Type) [Group X] (t : X) : Prop :=
  ∃ L : Subgroup X, L ≤ Subgroup.centralizer ({t} : Set X) ∧
    Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (L : Set X) ∧
    IsSimpleGroup L ∧ Group.IsPerfect L ∧
    ∀ a ∈ Subgroup.centralizer (L : Set X), ∀ b ∈ Subgroup.centralizer (L : Set X),
      a ^ 2 ≠ 1 → b ^ 2 ≠ 1 → a * b = b * a

section Transport

variable {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {t : X}

theorem mem_map_symm_iff {H : Subgroup Y} {x : X} :
    x ∈ H.map e.symm.toMonoidHom ↔ e x ∈ H := by
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm]

theorem map_symm_le_centralizer {H : Subgroup Y}
    (h : H ≤ Subgroup.centralizer ({e t} : Set Y)) :
    H.map e.symm.toMonoidHom ≤ Subgroup.centralizer ({t} : Set X) := by
  intro x hx
  have hc := Subgroup.mem_centralizer_singleton_iff.mp (h ((mem_map_symm_iff e).mp hx))
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply e.injective
  rw [map_mul, map_mul]
  exact hc

theorem map_mem_centralizer {x : X} (hx : x ∈ Subgroup.centralizer ({t} : Set X)) :
    e x ∈ Subgroup.centralizer ({e t} : Set Y) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  rw [← map_mul, ← map_mul, hx]

theorem TwoSL2Shape.of_mulEquiv {F : Type} [Field F] (h : TwoSL2Shape Y (e t) F) :
    TwoSL2Shape X t F := by
  obtain ⟨H₁, H₂, h₁, h₂, hc, ⟨e₁⟩, ⟨e₂⟩⟩ := h
  refine ⟨H₁.map e.symm.toMonoidHom, H₂.map e.symm.toMonoidHom, map_symm_le_centralizer e h₁,
    map_symm_le_centralizer e h₂, fun a ha b hb => ?_,
    ⟨(e.symm.subgroupMap H₁).symm.trans e₁⟩, ⟨(e.symm.subgroupMap H₂).symm.trans e₂⟩⟩
  apply e.injective
  rw [map_mul, map_mul]
  exact hc _ ((mem_map_symm_iff e).mp ha) _ ((mem_map_symm_iff e).mp hb)

theorem NormalSimpleShape.of_mulEquiv (h : NormalSimpleShape Y (e t)) : NormalSimpleShape X t := by
  obtain ⟨L, hLC, hCN, hsimp, hperf, hab⟩ := h
  have hCL : ∀ a ∈ Subgroup.centralizer ((L.map e.symm.toMonoidHom : Subgroup X) : Set X),
      e a ∈ Subgroup.centralizer (L : Set Y) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff] at ha ⊢
    intro l hl
    have h1 := ha (e.symm l) ((mem_map_symm_iff e).mpr (by rwa [MulEquiv.apply_symm_apply]))
    have h2 := congrArg e h1
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  refine ⟨L.map e.symm.toMonoidHom, map_symm_le_centralizer e hLC, fun x hx => ?_,
    (e.symm.subgroupMap L).symm.isSimpleGroup,
    Group.IsPerfect.ofSurjective (f := (e.symm.subgroupMap L).toMonoidHom)
      (MulEquiv.surjective _), fun a ha b hb ha2 hb2 => ?_⟩
  · have hn := hCN (map_mem_centralizer e hx)
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro y
    rw [mem_map_symm_iff, mem_map_symm_iff, map_mul, map_mul, map_inv]
    exact hn (e y)
  · apply e.injective
    rw [map_mul, map_mul]
    refine hab _ (hCL a ha) _ (hCL b hb) ?_ ?_
    · rwa [← map_pow, Ne, MulEquiv.map_eq_one_iff]
    · rwa [← map_pow, Ne, MulEquiv.map_eq_one_iff]

end Transport

variable {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R} {t : X}

theorem not_fourGenerated_of_twoSL2Shape (hD : TightDatum R S t) {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F) (h : TwoSL2Shape X t F) :
    ¬ TwoSubgroupsFourGenerated X := by
  obtain ⟨H₁, H₂, h₁, h₂, hc, ⟨e₁⟩, ⟨e₂⟩⟩ := h
  have := isPerfect_of_equiv_sl2 h4 e₁
  have := isPerfect_of_equiv_sl2 h4 e₂
  obtain ⟨φ₁, hi₁, hr₁, -⟩ := exists_q8_of_mulEquiv_sl2 hF H₁ e₁
  obtain ⟨φ₂, hi₂, hr₂, -⟩ := exists_q8_of_mulEquiv_sl2 hF H₂ e₂
  exact datum_not_fourGenerated hD h₁ h₂ hc φ₁ φ₂ hi₁ hi₂ hr₁ hr₂

theorem datum_le_centralizer_of_normalSimple (hD : TightDatum R S t) {L : Subgroup X}
    (hLC : L ≤ Subgroup.centralizer ({t} : Set X))
    (hCN : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (L : Set X))
    [IsSimpleGroup L] [Group.IsPerfect L] : R ≤ Subgroup.centralizer (L : Set X) := by
  have hRN : R ≤ Subgroup.normalizer (L : Set X) := hD.cent.trans hCN
  have hLN : L ≤ Subgroup.normalizer (R : Set X) := hLC.trans hD.le_normalizer
  have hNn : (R.subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hLN g.2) n).mp hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.subgroupOf L) with hbot | htop
  · intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : l * r * l⁻¹ * r⁻¹ ∈ R :=
      R.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLN hl) r).mp hr) (R.inv_mem hr)
    have h2 : l * r * l⁻¹ * r⁻¹ ∈ L := by
      rw [mul_assoc, mul_assoc]
      refine L.mul_mem hl ?_
      rw [← mul_assoc]
      exact (Subgroup.mem_normalizer_iff.mp (hRN hr) l⁻¹).mp (L.inv_mem hl)
    have h3 : (⟨_, h2⟩ : L) ∈ R.subgroupOf L := h1
    rw [hbot, Subgroup.mem_bot] at h3
    have h4 : l * r * l⁻¹ * r⁻¹ = 1 := congrArg Subtype.val h3
    calc l * r = l * r * l⁻¹ * r⁻¹ * (r * l) := by group
      _ = r * l := by rw [h4, one_mul]
  · exfalso
    have hLR : L ≤ R := fun l hl => by
      have : (⟨l, hl⟩ : L) ∈ R.subgroupOf L := by rw [htop]; exact Subgroup.mem_top _
      exact this
    have hcomm := datum_commutator_mem hD hLC
    have hLO : L ≤ oddCoreImg R := by
      rw [← Subgroup.commutator_eq_self (H := L), Subgroup.commutator_le]
      intro a ha b hb
      exact hcomm a ha b (hLR hb)
    have hodd : Odd (Nat.card L) :=
      (odd_natCard_oddCoreImg R).of_dvd_nat (Subgroup.card_dvd_of_le hLO)
    exact Group.IsPerfect.not_isSolvable L (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)

theorem q8_pair : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 ≠ 1 ∧
    (QuaternionGroup.xa 0 : QuaternionGroup 2) ^ 2 ≠ 1 ∧
    (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
  decide

theorem false_of_normalSimpleShape (hD : TightDatum R S t) (h : NormalSimpleShape X t) : False := by
  obtain ⟨L, hLC, hCN, hsimp, hperf, hab⟩ := h
  have hRC := datum_le_centralizer_of_normalSimple hD hLC hCN
  obtain ⟨φ, hφ, hφR, -⟩ := datum_exists_q8 hD
  obtain ⟨hx, hy, hxy⟩ := q8_pair
  refine hxy (hφ ?_)
  rw [map_mul, map_mul]
  refine hab _ (hRC (hφR _)) _ (hRC (hφR _)) ?_ ?_
  · rwa [← map_pow, Ne, (injective_iff_map_eq_one' φ).mp hφ]
  · rwa [← map_pow, Ne, (injective_iff_map_eq_one' φ).mp hφ]

end CFSG.ClassicalInvolution.Q3.TA3
