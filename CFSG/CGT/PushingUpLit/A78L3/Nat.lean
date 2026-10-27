module

public import CFSG.CGT.PushingUpLit.A78Sp4.ModJ
public import CFSG.CGT.PushingUpLit.A78Sp4.FieldSL2

public section

namespace CFSG.CGT.PushingUpLit.A78L3

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open Matrix

structure NatCoord (G : Type) [Group G] (L V : Subgroup G) (F : Type) [Field F] where
  κ : G → Fin 2 → F
  ρ : G → SpecialLinearGroup (Fin 2) F
  κ_mul : ∀ v ∈ V, ∀ w ∈ V, κ (v * w) = κ v + κ w
  κ_inj : ∀ v ∈ V, ∀ w ∈ V, κ v = κ w → v = w
  κ_surj : ∀ x : Fin 2 → F, ∃ v ∈ V, κ v = x
  ρ_mul : ∀ l ∈ L, ∀ m ∈ L, ρ (l * m) = ρ l * ρ m
  ρ_surj : ∀ g : SpecialLinearGroup (Fin 2) F, ∃ l ∈ L, ρ l = g
  ρ_eq_one : ∀ l ∈ L, ρ l = 1 ↔ l ∈ V
  norm : ∀ l ∈ L, ∀ v ∈ V, l * v * l⁻¹ ∈ V
  conj : ∀ l ∈ L, ∀ v ∈ V, κ (l * v * l⁻¹) = (ρ l : Matrix (Fin 2) (Fin 2) F) *ᵥ κ v

section Construction

variable {G : Type} [Group G] {L T J : Subgroup G} {e : ℕ}

theorem nonempty_natCoord_of_isNatSL {L V : Subgroup G} (hnat : BHS.IsNatSL L V e)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hCL : L ⊓ Subgroup.centralizer (V : Set G) = L ⊓ V)
    (hnorm : ∀ l ∈ L, ∀ v ∈ V, l * v * l⁻¹ ∈ V) :
    Nonempty (NatCoord G L V (GaloisField 2 e)) := by
  classical
  obtain ⟨φ, ψ, hs, hk, hψs, hψk, hψc⟩ := hnat
  let κ : G → Fin 2 → GaloisField 2 e := fun g =>
    if hg : g ∈ V then Multiplicative.toAdd (ψ ⟨g, hg⟩) else 0
  let ρ : G → SpecialLinearGroup (Fin 2) (GaloisField 2 e) := fun g =>
    if hg : g ∈ L then φ ⟨g, hg⟩ else 1
  have hκ : ∀ (g : G) (hg : g ∈ V), κ g = Multiplicative.toAdd (ψ ⟨g, hg⟩) := fun g hg => by
    simp only [κ, hg, ↓reduceDIte]
  have hρ : ∀ (g : G) (hg : g ∈ L), ρ g = φ ⟨g, hg⟩ := fun g hg => by
    simp only [ρ, hg, ↓reduceDIte]
  refine ⟨{
    κ := κ
    ρ := ρ
    κ_mul := ?_
    κ_inj := ?_
    κ_surj := ?_
    ρ_mul := ?_
    ρ_surj := ?_
    ρ_eq_one := ?_
    norm := hnorm
    conj := ?_ }⟩
  · intro v hv w hw
    rw [hκ v hv, hκ w hw, hκ _ (mul_mem hv hw)]
    rw [show (⟨v * w, mul_mem hv hw⟩ : ↥V) = ⟨v, hv⟩ * ⟨w, hw⟩ from rfl, map_mul, toAdd_mul]
  · intro v hv w hw hvw
    rw [hκ v hv, hκ w hw] at hvw
    have h1 : ψ (⟨v, hv⟩ * (⟨w, hw⟩ : ↥V)⁻¹) = 1 := by
      rw [map_mul, map_inv, Multiplicative.toAdd.injective hvw, mul_inv_cancel]
    have h2 : (⟨v, hv⟩ * (⟨w, hw⟩ : ↥V)⁻¹ : ↥V) ∈ ψ.ker := h1
    rw [hψk, Subgroup.mem_subgroupOf, hZ, Subgroup.mem_bot] at h2
    have h3 : v * w⁻¹ = 1 := h2
    exact mul_inv_eq_one.1 h3
  · intro x
    obtain ⟨⟨v, hv⟩, hvx⟩ := hψs (Multiplicative.ofAdd x)
    exact ⟨v, hv, by rw [hκ v hv, hvx, toAdd_ofAdd]⟩
  · intro l hl m hm
    rw [hρ l hl, hρ m hm, hρ _ (mul_mem hl hm), ← map_mul]
    rfl
  · intro g
    obtain ⟨⟨l, hl⟩, hlg⟩ := hs g
    exact ⟨l, hl, by rw [hρ l hl, hlg]⟩
  · intro l hl
    rw [hρ l hl]
    constructor
    · intro h1
      have h2 : (⟨l, hl⟩ : ↥L) ∈ φ.ker := h1
      rw [hk, Subgroup.mem_subgroupOf, hCL] at h2
      exact h2.2
    · intro hlV
      have h3 : (⟨l, hl⟩ : ↥L) ∈ φ.ker := by
        rw [hk, Subgroup.mem_subgroupOf, hCL]
        exact ⟨hl, hlV⟩
      exact h3
  · intro l hl v hv
    rw [hκ _ (hnorm l hl v hv), hκ v hv, hρ l hl, hψc ⟨l, hl⟩ ⟨v, hv⟩ (hnorm l hl v hv),
      toAdd_ofAdd]

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Side.nonempty_natCoord [Finite G]
    (h : A78Side G L T J e)
    (hZ : oTwoIn (L ⊔ T) ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    Nonempty (NatCoord G L (oTwoIn (L ⊔ T)) (GaloisField 2 e)) :=
  nonempty_natCoord_of_isNatSL h.nat hZ h.inf_V_eq_centralizer.symm h.conj_V_L

end Construction

theorem coe_mulVec_eq_smul {F : Type} [Field F] (g : SpecialLinearGroup (Fin 2) F)
    (u : Fin 2 → F) : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ u = g • u := rfl

namespace NatCoord

variable {G : Type} [Group G] {L V : Subgroup G} {F : Type} [Field F] (D : NatCoord G L V F)

theorem ρ_mulVec_mul {l m : G} (hl : l ∈ L) (hm : m ∈ L) (u : Fin 2 → F) :
    (D.ρ (l * m) : Matrix (Fin 2) (Fin 2) F) *ᵥ u =
      (D.ρ l : Matrix (Fin 2) (Fin 2) F) *ᵥ ((D.ρ m : Matrix (Fin 2) (Fin 2) F) *ᵥ u) := by
  simp only [coe_mulVec_eq_smul]
  rw [D.ρ_mul l hl m hm, mul_smul]

theorem ρ_mulVec_of_mem {v : G} (hvL : v ∈ L) (hv : v ∈ V) (u : Fin 2 → F) :
    (D.ρ v : Matrix (Fin 2) (Fin 2) F) *ᵥ u = u := by
  simp only [coe_mulVec_eq_smul]
  rw [(D.ρ_eq_one v hvL).2 hv, one_smul]

theorem κ_one : D.κ 1 = 0 := by
  have h := D.κ_mul 1 V.one_mem 1 V.one_mem
  rw [one_mul] at h
  have h2 : D.κ 1 + D.κ 1 = D.κ 1 + 0 := by rw [← h, add_zero]
  exact add_left_cancel h2

theorem κ_inv {v : G} (hv : v ∈ V) : D.κ v⁻¹ = -D.κ v := by
  have h := D.κ_mul v hv v⁻¹ (inv_mem hv)
  rw [mul_inv_cancel, D.κ_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem κ_eq_zero_iff {v : G} (hv : v ∈ V) : D.κ v = 0 ↔ v = 1 := by
  constructor
  · intro h0
    exact D.κ_inj v hv 1 V.one_mem (by rw [h0, D.κ_one])
  · rintro rfl
    exact D.κ_one

theorem κ_ne_zero {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) : D.κ v ≠ 0 := fun h0 =>
  hv1 ((D.κ_eq_zero_iff hv).1 h0)

theorem ρ_one : D.ρ 1 = 1 := (D.ρ_eq_one 1 L.one_mem).2 V.one_mem

theorem ρ_inv {l : G} (hl : l ∈ L) : D.ρ l⁻¹ = (D.ρ l)⁻¹ := by
  have h := D.ρ_mul l hl l⁻¹ (inv_mem hl)
  rw [mul_inv_cancel, D.ρ_one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

include D in
theorem card_V : Nat.card V = Nat.card F ^ 2 := by
  have hb : Function.Bijective (fun v : V => D.κ v) :=
    ⟨fun v w hvw => Subtype.ext (D.κ_inj v v.2 w w.2 hvw), fun x => by
      obtain ⟨v, hv, hvx⟩ := D.κ_surj x
      exact ⟨⟨v, hv⟩, hvx⟩⟩
  rw [Nat.card_eq_of_bijective _ hb, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2),
    Fintype.card_fin]

theorem κ_comm {w l : G} (hw : w ∈ V) (hl : l ∈ L) :
    D.κ (w * (l * w⁻¹ * l⁻¹)) =
      D.κ w - (D.ρ l : Matrix (Fin 2) (Fin 2) F) *ᵥ D.κ w := by
  rw [D.κ_mul w hw _ (D.norm l hl _ (inv_mem hw)), D.conj l hl _ (inv_mem hw), D.κ_inv hw,
    mulVec_neg, sub_eq_add_neg]

include D in
theorem le (hVL : ∀ v ∈ V, ∀ l ∈ L, v * l * v⁻¹ ∈ L) : V ≤ L := by
  have hcomm : ∀ (w : G), w ∈ V → ∀ l ∈ L, w * (l * w⁻¹ * l⁻¹) ∈ L := by
    intro w hw l hl
    have : w * (l * w⁻¹ * l⁻¹) = (w * l * w⁻¹) * l⁻¹ := by group
    rw [this]
    exact mul_mem (hVL w hw l hl) (inv_mem hl)
  have h0 : ∀ x : F, ∃ g ∈ L, g ∈ V ∧ D.κ g = ![x, 0] := by
    intro x
    obtain ⟨w, hw, hwx⟩ := D.κ_surj ![0, -x]
    obtain ⟨l, hl, hlu⟩ := D.ρ_surj (CFSG.SL2MinimalFaithful.unipotent 1)
    refine ⟨w * (l * w⁻¹ * l⁻¹), hcomm w hw l hl, mul_mem hw (D.norm l hl _ (inv_mem hw)), ?_⟩
    rw [D.κ_comm hw hl, hlu, hwx, CFSG.SL2MinimalFaithful.coe_unipotent]
    ext i
    fin_cases i <;> simp
  have h1 : ∀ y : F, ∃ g ∈ L, g ∈ V ∧ D.κ g = ![0, y] := by
    intro y
    obtain ⟨w, hw, hwy⟩ := D.κ_surj ![-y, 0]
    let u : SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; 1, 1], by simp [det_fin_two]⟩
    obtain ⟨l, hl, hlu⟩ := D.ρ_surj u
    refine ⟨w * (l * w⁻¹ * l⁻¹), hcomm w hw l hl, mul_mem hw (D.norm l hl _ (inv_mem hw)), ?_⟩
    rw [D.κ_comm hw hl, hlu, hwy]
    ext i
    fin_cases i <;> simp [u]
  intro v hv
  obtain ⟨g₀, hg₀L, hg₀V, hg₀⟩ := h0 (D.κ v 0)
  obtain ⟨g₁, hg₁L, hg₁V, hg₁⟩ := h1 (D.κ v 1)
  have e : v = g₀ * g₁ := by
    refine D.κ_inj v hv _ (mul_mem hg₀V hg₁V) ?_
    rw [D.κ_mul g₀ hg₀V g₁ hg₁V, hg₀, hg₁]
    ext i
    fin_cases i <;> simp
  rw [e]
  exact mul_mem hg₀L hg₁L

include D in
theorem exists_conj {v w : G} (hv : v ∈ V) (hv1 : v ≠ 1) (hw : w ∈ V) (hw1 : w ≠ 1) :
    ∃ l ∈ L, l * v * l⁻¹ = w := by
  obtain ⟨M, -, hM⟩ := exists_fixSL_mulVec_eq (σ := RingEquiv.refl F) (D.κ_ne_zero hv hv1)
    (D.κ_ne_zero hw hw1) (fun _ => rfl) (fun _ => rfl)
  obtain ⟨l, hl, hlM⟩ := D.ρ_surj M
  refine ⟨l, hl, D.κ_inj _ (D.norm l hl v hv) w hw ?_⟩
  rw [D.conj l hl v hv, hlM]
  exact hM

end NatCoord

section Stabilizer

variable {F : Type} [Field F] [CharP F 2]

theorem sq_eq_one_of_mulVec_eq {g : SpecialLinearGroup (Fin 2) F} {x : Fin 2 → F} (hx : x ≠ 0)
    (hgx : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ x = x) : g * g = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hdet : g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
    have := g.2
    rwa [det_fin_two] at this
  have e0 := congrFun hgx 0
  have e1 := congrFun hgx 1
  simp only [mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
  have hD : (g.1 0 0 - 1) * (g.1 1 1 - 1) - g.1 0 1 * g.1 1 0 = 0 := by
    by_cases h0 : x 0 = 0
    · have h1 : x 1 ≠ 0 := by
        intro h1
        apply hx
        ext i
        fin_cases i
        · exact h0
        · exact h1
      apply mul_left_cancel₀ h1
      rw [mul_zero]
      linear_combination (g.1 0 0 - 1) * e1 - g.1 1 0 * e0
    · apply mul_left_cancel₀ h0
      rw [mul_zero]
      linear_combination (g.1 1 1 - 1) * e0 - g.1 0 1 * e1
  have htr : g.1 0 0 + g.1 1 1 = 0 := by
    linear_combination -hD + hdet + h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination g.1 0 0 * htr - hdet - h2
  · linear_combination g.1 0 1 * htr
  · linear_combination g.1 1 0 * htr
  · linear_combination g.1 1 1 * htr - hdet - h2

end Stabilizer

namespace NatCoord

variable {G : Type} [Group G] {L V : Subgroup G} {F : Type} [Field F] [CharP F 2]
  (D : NatCoord G L V F)

include D in
theorem sq_mem_of_comm {v l : G} (hv : v ∈ V) (hv1 : v ≠ 1) (hl : l ∈ L) (hlv : l * v = v * l) :
    l * l ∈ V := by
  have hfix : (D.ρ l : Matrix (Fin 2) (Fin 2) F) *ᵥ D.κ v = D.κ v := by
    rw [← D.conj l hl v hv]
    congr 1
    rw [hlv]
    group
  have := sq_eq_one_of_mulVec_eq (D.κ_ne_zero hv hv1) hfix
  rw [← D.ρ_mul l hl l hl] at this
  exact (D.ρ_eq_one _ (mul_mem hl hl)).1 this

include D in
theorem isPGroup_inf_centralizer (hV : ∀ x ∈ V, x * x = 1) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    IsPGroup 2 ↥(L ⊓ Subgroup.centralizer ({v} : Set G)) := by
  intro g
  refine ⟨2, ?_⟩
  have hgL : (g : G) ∈ L := g.2.1
  have hgv : (g : G) * v = v * g := Subgroup.mem_centralizer_singleton_iff.1 g.2.2
  have h1 := hV _ (D.sq_mem_of_comm hv hv1 hgL hgv)
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  calc (g : G) ^ 2 ^ 2 = (g : G) * g * ((g : G) * g) := by
        rw [show (2 : ℕ) ^ 2 = 2 + 2 by norm_num, pow_add, pow_two]
    _ = 1 := h1

end NatCoord

section Cfg

variable {G : Type} [Group G] [Finite G] {L₁ L₂ T : Subgroup G} {e : ℕ}

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Side.card_V {J : Subgroup G} {L : Subgroup G}
    (h : A78Side G L T J e) (he : e ≠ 0) :
    Nat.card (oTwoIn (L ⊔ T)) =
      2 ^ (2 * e) * Nat.card ↥(oTwoIn (L ⊔ T) ⊓ Subgroup.centralizer (L : Set G)) := by
  obtain ⟨φ, ψ, -, -, hψs, hψk, -⟩ := h.nat
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv] at h1
  have h2 : Nat.card (Multiplicative (Fin 2 → GaloisField 2 e)) = 2 ^ (2 * e) := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2),
      Fintype.card_fin, GaloisField.card 2 e he]
    ring
  have h3 : Nat.card ψ.ker =
      Nat.card ↥(oTwoIn (L ⊔ T) ⊓ Subgroup.centralizer (L : Set G)) := by
    rw [hψk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h1, h2, h3]

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.inf_centralizer_V₂_eq_bot
    (h : A78Cfg G L₁ L₂ T e)
    (hZ : oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G) = ⊥) :
    oTwoIn (L₂ ⊔ T) ⊓ Subgroup.centralizer (L₂ : Set G) = ⊥ := by
  have he : e ≠ 0 := by have := h.two_le; omega
  have h1 := h.side₁.card_V he
  have h2 := h.side₂.card_V he
  rw [hZ, Subgroup.card_bot, mul_one] at h1
  have h3 : Nat.card (oTwoIn (L₂ ⊔ T)) = Nat.card (oTwoIn (L₁ ⊔ T)) := h.jStructure.card_V₂_eq
  rw [h3, h1] at h2
  have hpos : 0 < 2 ^ (2 * e) := by positivity
  have h4 : Nat.card ↥(oTwoIn (L₂ ⊔ T) ⊓ Subgroup.centralizer (L₂ : Set G)) = 1 := by
    have : 2 ^ (2 * e) * 1 =
        2 ^ (2 * e) * Nat.card ↥(oTwoIn (L₂ ⊔ T) ⊓ Subgroup.centralizer (L₂ : Set G)) := by
      rw [mul_one]; exact h2
    exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
  exact Subgroup.card_eq_one.1 h4

end Cfg

end CFSG.CGT.PushingUpLit.A78L3
