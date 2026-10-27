module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Cases

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

open Subgroup Matrix

theorem mulVec_units (a b : GL12) (v : Vec12) :
    (a : Mat12) *ᵥ ((b : Mat12) *ᵥ v) = ((a * b : GL12) : Mat12) *ᵥ v := by
  rw [mulVec_mulVec, Units.val_mul]

theorem units_one_mulVec (v : Vec12) : ((1 : GL12) : Mat12) *ᵥ v = v := by
  rw [Units.val_one, one_mulVec]

theorem card_fixM_conj (x y : GL12) :
    Nat.card (fixM ((x * y * x⁻¹ : GL12) : Mat12)) = Nat.card (fixM (y : Mat12)) := by
  refine (Nat.card_congr
    { toFun := fun v => ⟨((x⁻¹ : GL12) : Mat12) *ᵥ v.1, ?_⟩
      invFun := fun v => ⟨(x : Mat12) *ᵥ v.1, ?_⟩
      left_inv := fun v => ?_
      right_inv := fun v => ?_ })
  · have hv : ((x * y * x⁻¹ : GL12) : Mat12) *ᵥ v.1 = v.1 := v.2
    show (y : Mat12) *ᵥ (((x⁻¹ : GL12) : Mat12) *ᵥ v.1) = ((x⁻¹ : GL12) : Mat12) *ᵥ v.1
    rw [mulVec_units, show y * x⁻¹ = x⁻¹ * (x * y * x⁻¹) by group, ← mulVec_units, hv]
  · have hv : (y : Mat12) *ᵥ v.1 = v.1 := v.2
    show ((x * y * x⁻¹ : GL12) : Mat12) *ᵥ ((x : Mat12) *ᵥ v.1) = (x : Mat12) *ᵥ v.1
    rw [mulVec_units, show x * y * x⁻¹ * x = x * y by group, ← mulVec_units, hv]
  · ext1
    show (x : Mat12) *ᵥ (((x⁻¹ : GL12) : Mat12) *ᵥ v.1) = v.1
    rw [mulVec_units, mul_inv_cancel, units_one_mulVec]
  · ext1
    show ((x⁻¹ : GL12) : Mat12) *ᵥ ((x : Mat12) *ᵥ v.1) = v.1
    rw [mulVec_units, inv_mul_cancel, units_one_mulVec]

namespace Stage2Hyp

variable {G : Type*} [Group G] {M : Model} {t : G} {TH W : Subgroup G}
  {φ : W ≃* Multiplicative (Fin 12 → ZMod 2)} {D : CaseData}

theorem isMax_of_second [Finite G] (h : Stage2Hyp M t TH W φ) (hM : ModelFacts M)
    (hF : CaseFacts M D) {S : Subgroup GL12} (hTCS : M.TC ≤ S) {τ z : GL12}
    (hcls : ∀ s ∈ S, s * s = 1 → s ≠ 1 → Nat.card (fixM (s : Mat12)) ≤ 2 ^ 7 →
      Nat.card M.TC ≤ Nat.card ↥(S ⊓ centralizer ({s} : Set GL12)) →
        ∃ y ∈ S, s = y * M.tbar * y⁻¹ ∨ s = y * τ * y⁻¹)
    (hzX : z ∈ Xof W φ) (hzτ : z * τ = τ * z) (hz8 : z ^ 8 = 1) (hz4 : z ^ 4 ≠ 1)
    (hno8 : ∀ c ∈ M.CC, c ^ 8 = 1 → c ^ 4 = 1) :
    ∀ Z : Subgroup GL12, Z ≤ Xof W φ → IsPGroup 2 Z → S ≤ Z → Z = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Z hZX hZ2 hSZ
  by_contra hne
  obtain ⟨m, hmZ, hmS, hmN⟩ := exists_mem_normalizer_of_lt hZ2 hSZ (Ne.symm hne)
  have hmX := hZX hmZ
  have hsS : m * M.tbar * m⁻¹ ∈ S := (mem_normalizer_iff.1 hmN _).1 (hTCS hF.tbar_mem_TC)
  have hs2 : m * M.tbar * m⁻¹ * (m * M.tbar * m⁻¹) = 1 := by
    calc m * M.tbar * m⁻¹ * (m * M.tbar * m⁻¹) = m * (M.tbar * M.tbar) * m⁻¹ := by group
      _ = 1 := by rw [hF.tbar_sq, mul_one, mul_inv_cancel]
  have hs1 : m * M.tbar * m⁻¹ ≠ 1 := fun e => hF.tbar_ne_one (by
    calc M.tbar = m⁻¹ * (m * M.tbar * m⁻¹) * m := by group
      _ = 1 := by rw [e]; group)
  have hcard : Nat.card M.TC ≤
      Nat.card ↥(S ⊓ centralizer ({m * M.tbar * m⁻¹} : Set GL12)) := by
    refine Nat.card_le_card_of_injective (fun x => ⟨m * x * m⁻¹,
      (mem_normalizer_iff.1 hmN _).1 (hTCS x.2), ?_⟩) ?_
    · show m * x * m⁻¹ ∈ centralizer ({m * M.tbar * m⁻¹} : Set GL12)
      rw [mem_centralizer_singleton_iff]
      have hx := hF.tbar_central x x.2
      calc m * x * m⁻¹ * (m * M.tbar * m⁻¹) = m * (x * M.tbar) * m⁻¹ := by group
        _ = m * (M.tbar * x) * m⁻¹ := by rw [hx]
        _ = m * M.tbar * m⁻¹ * (m * x * m⁻¹) := by group
    · intro x y e
      have e' : m * (x : GL12) * m⁻¹ = m * y * m⁻¹ := congrArg Subtype.val e
      exact Subtype.ext (by simpa using e')
  have hfix : Nat.card (fixM ((m * M.tbar * m⁻¹ : GL12) : Mat12)) ≤ 2 ^ 7 := by
    rw [card_fixM_conj]
    exact hM.card_fixM_tbar
  obtain ⟨y, hyS, hy | hy⟩ := hcls _ hsS hs2 hs1 hfix hcard
  ·
    have hwX : y⁻¹ * m ∈ Xof W φ := (Xof W φ).mul_mem ((Xof W φ).inv_mem (hZX (hSZ hyS))) hmX
    have hwt : y⁻¹ * m * M.tbar = M.tbar * (y⁻¹ * m) := by
      calc y⁻¹ * m * M.tbar = y⁻¹ * (m * M.tbar * m⁻¹) * m := by group
        _ = y⁻¹ * (y * M.tbar * y⁻¹) * m := by rw [hy]
        _ = M.tbar * (y⁻¹ * m) := by group
    have hwC := h.mem_CC_of_commute hwX hwt
    have hwZ : y⁻¹ * m ∈ Z := Z.mul_mem (Z.inv_mem (hSZ hyS)) hmZ
    have hwNS : y⁻¹ * m ∈ normalizer (S : Set GL12) :=
      (normalizer (S : Set GL12)).mul_mem ((normalizer (S : Set GL12)).inv_mem
        (le_normalizer hyS)) hmN
    have hTC : S ⊓ M.CC = M.TC :=
      hF.TC_max _ (hZ2.to_le (inf_le_left.trans hSZ)) (le_inf hTCS hF.TC_le_CC) inf_le_right
    have hwN : y⁻¹ * m ∈ normalizer (M.TC : Set GL12) := by
      rw [← hTC, mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨hxS, hxC⟩
        exact ⟨(mem_normalizer_iff.1 hwNS x).1 hxS,
          M.CC.mul_mem (M.CC.mul_mem hwC hxC) (M.CC.inv_mem hwC)⟩
      · rintro ⟨hxS, hxC⟩
        refine ⟨(mem_normalizer_iff.1 hwNS x).2 hxS, ?_⟩
        have e : x = (y⁻¹ * m)⁻¹ * ((y⁻¹ * m) * x * (y⁻¹ * m)⁻¹) * (y⁻¹ * m) := by group
        rw [e]
        exact M.CC.mul_mem (M.CC.mul_mem (M.CC.inv_mem hwC) hxC) hwC
    have h2 : IsPGroup 2 (M.TC ⊔ zpowers (y⁻¹ * m) : Subgroup GL12) :=
      IsPGroup.to_sup_of_normal_left' hF.TC_pgroup (hZ2.to_le ((zpowers_le).2 hwZ))
        ((zpowers_le).2 hwN)
    have h3 := hF.TC_max _ h2 le_sup_left (sup_le hF.TC_le_CC ((zpowers_le).2 hwC))
    have hwT : y⁻¹ * m ∈ M.TC :=
      h3 ▸ (le_sup_right : zpowers (y⁻¹ * m) ≤ M.TC ⊔ zpowers (y⁻¹ * m)) (mem_zpowers _)
    apply hmS
    have e : m = y * (y⁻¹ * m) := by group
    rw [e]
    exact S.mul_mem hyS (hTCS hwT)
  ·
    have hxX : y⁻¹ * m ∈ Xof W φ := (Xof W φ).mul_mem ((Xof W φ).inv_mem (hZX (hSZ hyS))) hmX
    have hxt : y⁻¹ * m * M.tbar * (y⁻¹ * m)⁻¹ = τ := by
      calc y⁻¹ * m * M.tbar * (y⁻¹ * m)⁻¹ = y⁻¹ * (m * M.tbar * m⁻¹) * y := by group
        _ = y⁻¹ * (y * τ * y⁻¹) * y := by rw [hy]
        _ = τ := by group
    set x := y⁻¹ * m with hxdef
    have hwX : x⁻¹ * z * x ∈ Xof W φ :=
      (Xof W φ).mul_mem ((Xof W φ).mul_mem ((Xof W φ).inv_mem hxX) hzX) hxX
    have hwt : x⁻¹ * z * x * M.tbar = M.tbar * (x⁻¹ * z * x) := by
      have e : M.tbar = x⁻¹ * τ * x := by rw [← hxt]; group
      rw [e]
      calc x⁻¹ * z * x * (x⁻¹ * τ * x) = x⁻¹ * (z * τ) * x := by group
        _ = x⁻¹ * (τ * z) * x := by rw [hzτ]
        _ = x⁻¹ * τ * x * (x⁻¹ * z * x) := by group
    have hwC := h.mem_CC_of_commute hwX hwt
    have hpow : ∀ n : ℕ, (x⁻¹ * z * x) ^ n = x⁻¹ * z ^ n * x := fun n => by
      have e : x⁻¹ * z * x = x⁻¹ * z * x⁻¹⁻¹ := by rw [inv_inv]
      rw [e, conj_pow, inv_inv]
    have hw8 : (x⁻¹ * z * x) ^ 8 = 1 := by rw [hpow, hz8, mul_one, inv_mul_cancel]
    have hw4 := hno8 _ hwC hw8
    rw [hpow] at hw4
    apply hz4
    calc z ^ 4 = x * (x⁻¹ * z ^ 4 * x) * x⁻¹ := by group
      _ = 1 := by rw [hw4]; group

end Stage2Hyp

end CFSG.EvenSmallLie.OmegaEight.Stage2
