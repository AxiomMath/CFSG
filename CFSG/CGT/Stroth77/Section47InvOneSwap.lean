module

public import CFSG.CGT.Stroth76.SylowCwConj

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

namespace Stroth47Inv1

@[expose] def swapStabilizer (c₁ w₀ : G) (hw₀ : w₀ * w₀ = 1) : Subgroup G where
  carrier := {h | h * w₀ = w₀ * h ∧ (h⁻¹ * c₁ * h = c₁ ∨ h⁻¹ * c₁ * h = c₁ * w₀)}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨haw, ha⟩ ⟨hbw, hb⟩
    refine ⟨?_, ?_⟩
    · calc (a * b) * w₀ = a * (b * w₀) := by rw [mul_assoc]
        _ = a * (w₀ * b) := by rw [hbw]
        _ = (a * w₀) * b := by rw [mul_assoc]
        _ = (w₀ * a) * b := by rw [haw]
        _ = w₀ * (a * b) := by rw [mul_assoc]
    · have hconj : (a * b)⁻¹ * c₁ * (a * b) = b⁻¹ * (a⁻¹ * c₁ * a) * b := by
        group
      rw [hconj]
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · left
        rw [ha, hb]
      · right
        rw [ha]
        exact hb
      · right
        rw [ha]
        calc b⁻¹ * (c₁ * w₀) * b = b⁻¹ * c₁ * (w₀ * b) := by group
          _ = b⁻¹ * c₁ * (b * w₀) := by rw [← hbw]
          _ = (b⁻¹ * c₁ * b) * w₀ := by group
          _ = c₁ * w₀ := by rw [hb]
      · left
        rw [ha]
        calc b⁻¹ * (c₁ * w₀) * b = b⁻¹ * c₁ * (w₀ * b) := by group
          _ = b⁻¹ * c₁ * (b * w₀) := by rw [← hbw]
          _ = (b⁻¹ * c₁ * b) * w₀ := by group
          _ = (c₁ * w₀) * w₀ := by rw [hb]
          _ = c₁ := by rw [mul_assoc, hw₀, mul_one]
  inv_mem' := by
    rintro a ⟨haw, ha⟩
    have haw' : a⁻¹ * w₀ = w₀ * a⁻¹ := by
      calc a⁻¹ * w₀ = a⁻¹ * w₀ * (a * a⁻¹) := by group
        _ = a⁻¹ * (w₀ * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * w₀) * a⁻¹ := by rw [← haw]
        _ = w₀ * a⁻¹ := by group
    refine ⟨haw', ?_⟩
    simp only [inv_inv]
    rcases ha with ha | ha
    · left
      calc a * c₁ * a⁻¹ = a * (a⁻¹ * c₁ * a) * a⁻¹ := by rw [ha]
        _ = c₁ := by group
    · right
      have haw2 : a * w₀ * a⁻¹ = w₀ := by
        calc a * w₀ * a⁻¹ = (a * w₀) * a⁻¹ := by rw [mul_assoc]
          _ = (w₀ * a) * a⁻¹ := by rw [haw]
          _ = w₀ := by group
      have h1 : c₁ = a * (c₁ * w₀) * a⁻¹ := by
        calc c₁ = a * (a⁻¹ * c₁ * a) * a⁻¹ := by group
          _ = a * (c₁ * w₀) * a⁻¹ := by rw [ha]
      have h3 : c₁ = (a * c₁ * a⁻¹) * w₀ := by
        calc c₁ = a * (c₁ * w₀) * a⁻¹ := h1
          _ = (a * c₁ * a⁻¹) * (a * w₀ * a⁻¹) := by group
          _ = (a * c₁ * a⁻¹) * w₀ := by rw [haw2]
      calc a * c₁ * a⁻¹ = (a * c₁ * a⁻¹) * 1 := by group
        _ = (a * c₁ * a⁻¹) * (w₀ * w₀) := by rw [hw₀]
        _ = ((a * c₁ * a⁻¹) * w₀) * w₀ := by group
        _ = c₁ * w₀ := by rw [← h3]

omit [Finite G] in
@[simp] theorem mem_swapStabilizer {c₁ w₀ : G} {hw₀ : w₀ * w₀ = 1} {h : G} :
    h ∈ swapStabilizer c₁ w₀ hw₀ ↔
      h * w₀ = w₀ * h ∧ (h⁻¹ * c₁ * h = c₁ ∨ h⁻¹ * c₁ * h = c₁ * w₀) :=
  Iff.rfl

omit [Finite G] in
theorem conj_mem_swapStabilizer {c₁ w₀ : G} {hw₀ : w₀ * w₀ = 1} {h : G}
    (hh : h ∈ swapStabilizer c₁ w₀ hw₀) :
    h * c₁ * h⁻¹ = c₁ ∨ h * c₁ * h⁻¹ = c₁ * w₀ := by
  have hh' := (swapStabilizer c₁ w₀ hw₀).inv_mem hh
  simpa using hh'.2

omit [Finite G] in
theorem index_le_two_of_le_swapStabilizer {c₁ w₀ : G} {hw₀ : w₀ * w₀ = 1} {P : Subgroup G}
    (hP : P ≤ swapStabilizer c₁ w₀ hw₀) :
    ((P ⊓ Subgroup.centralizer {c₁} : Subgroup G).subgroupOf P).index ≤ 2 := by
  let K : Subgroup G := P ⊓ Subgroup.centralizer {c₁}
  have hKP : K ≤ P := inf_le_left
  let KP : Subgroup ↥P := K.subgroupOf P
  have hcomm_of_conj {x : G} (h : x⁻¹ * c₁ * x = c₁) : x * c₁ = c₁ * x := by
    have h1 : x * c₁ * x⁻¹ = c₁ := by
      calc x * c₁ * x⁻¹ = x * (x⁻¹ * c₁ * x) * x⁻¹ := by rw [h]
        _ = c₁ := by group
    calc x * c₁ = x * c₁ * x⁻¹ * x := by group
      _ = c₁ * x := by rw [h1]
  change KP.index ≤ 2
  by_cases htop : KP = ⊤
  · rw [htop, Subgroup.index_top]
    omega
  obtain ⟨a, -, haKP⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr htop)
  have haP : (a : G) ∈ P := a.2
  have haK : (a : G) ∉ K := fun h => haKP (Subgroup.mem_subgroupOf.mpr h)
  have haR : (a : G) ∉ Subgroup.centralizer {c₁} := fun h =>
    haK (Subgroup.mem_inf.mpr ⟨haP, h⟩)
  have haW : (a : G) * w₀ = w₀ * a := (mem_swapStabilizer.mp (hP haP)).1
  have ha₁ : (a : G)⁻¹ * c₁ * a = c₁ * w₀ := by
    rcases (mem_swapStabilizer.mp (hP haP)).2 with h | h
    · exfalso
      exact haR (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm_of_conj h))
    · exact h
  have h2 : KP.index = 2 :=
    Subgroup.index_eq_two_iff_exists_notMem_and.mpr ⟨a, haKP, fun z => ?_⟩
  · omega
  · by_cases hz : z ∈ KP
    · exact Or.inr hz
    · refine Or.inl ?_
      have hzP : (z : G) ∈ P := z.2
      have hzK : (z : G) ∉ K := fun h => hz (Subgroup.mem_subgroupOf.mpr h)
      have hzR : (z : G) ∉ Subgroup.centralizer {c₁} := fun h =>
        hzK (Subgroup.mem_inf.mpr ⟨hzP, h⟩)
      have hz₁ : (z : G)⁻¹ * c₁ * z = c₁ * w₀ := by
        rcases (mem_swapStabilizer.mp (hP hzP)).2 with h | h
        · exfalso
          exact hzR (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm_of_conj h))
        · exact h
      have hprod_conj : ((z : G) * a)⁻¹ * c₁ * ((z : G) * a) = c₁ := by
        calc ((z : G) * a)⁻¹ * c₁ * ((z : G) * a)
            = (a : G)⁻¹ * ((z : G)⁻¹ * c₁ * (z : G)) * a := by group
          _ = (a : G)⁻¹ * (c₁ * w₀) * a := by rw [hz₁]
          _ = (a : G)⁻¹ * c₁ * (w₀ * a) := by group
          _ = (a : G)⁻¹ * c₁ * (a * w₀) := by rw [← haW]
          _ = ((a : G)⁻¹ * c₁ * a) * w₀ := by group
          _ = (c₁ * w₀) * w₀ := by rw [ha₁]
          _ = c₁ := by rw [mul_assoc, hw₀, mul_one]
      have hcomm : ((z : G) * a) * c₁ = c₁ * ((z : G) * a) :=
        hcomm_of_conj hprod_conj
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr
        ⟨P.mul_mem hzP haP, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩)

omit [Finite G] in
theorem card_le_two_mul_card_inf_centralizer {c₁ w₀ : G} {hw₀ : w₀ * w₀ = 1} {P : Subgroup G}
    (hP : P ≤ swapStabilizer c₁ w₀ hw₀) :
    Nat.card P ≤ 2 * Nat.card (P ⊓ Subgroup.centralizer {c₁} : Subgroup G) := by
  let K : Subgroup G := P ⊓ Subgroup.centralizer {c₁}
  have hKP : K ≤ P := inf_le_left
  let KP : Subgroup ↥P := K.subgroupOf P
  have hidx : KP.index ≤ 2 :=
    index_le_two_of_le_swapStabilizer (c₁ := c₁) (w₀ := w₀) (hw₀ := hw₀) hP
  have hcardKP : Nat.card KP = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKP).toEquiv
  have hcardP := Subgroup.card_mul_index KP
  have hle : Nat.card KP * KP.index ≤ Nat.card KP * 2 := Nat.mul_le_mul_left _ hidx
  rw [hcardP] at hle
  rw [hcardKP] at hle
  calc Nat.card P ≤ Nat.card (P ⊓ Subgroup.centralizer {c₁} : Subgroup G) * 2 := hle
    _ = 2 * Nat.card (P ⊓ Subgroup.centralizer {c₁} : Subgroup G) := by rw [mul_comm]

theorem exists_conj_le_of_swap {S W : Subgroup G} {c₁ w₀ x₀ : G} (hS : IsPGroup 2 S)
    (hsyl : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.centralizer {c₁} →
      ∃ x ∈ Subgroup.centralizer {c₁}, ∀ q ∈ Q, x⁻¹ * q * x ∈ S)
    (hw : ∀ y ∈ S, y * w₀ = w₀ * y) (hw₀2 : w₀ * w₀ = 1) (hw₀1 : w₀ ≠ 1)
    (hx₀ : x₀ ∈ S) (hx₀c₁ : x₀⁻¹ * c₁ * x₀ = c₁ * w₀)
    (hW : IsPGroup 2 W) (hWw : W ≤ Subgroup.centralizer {w₀})
    (hWc : ∀ h ∈ W, h⁻¹ * c₁ * h = c₁ ∨ h⁻¹ * c₁ * h = c₁ * w₀) :
    ∃ y ∈ Subgroup.centralizer {c₁} ⊓ Subgroup.centralizer {w₀}, ∀ h ∈ W, y⁻¹ * h * y ∈ S := by
  classical
  let H : Subgroup G := swapStabilizer c₁ w₀ hw₀2
  let U : Subgroup G := S ⊓ H
  let T₀ : Subgroup G := S ⊓ Subgroup.centralizer {c₁}
  have hUH : U ≤ H := inf_le_right
  have hUS : U ≤ S := inf_le_left
  have hU2 : IsPGroup 2 U := hS.to_le hUS
  have hx₀H : x₀ ∈ H := by
    rw [show H = swapStabilizer c₁ w₀ hw₀2 from rfl, mem_swapStabilizer]
    exact ⟨hw x₀ hx₀, Or.inr hx₀c₁⟩
  have hx₀U : x₀ ∈ U := Subgroup.mem_inf.mpr ⟨hx₀, hx₀H⟩
  have hx₀T : x₀ ∉ T₀ := by
    intro hx
    have hc : x₀⁻¹ * c₁ * x₀ = c₁ := by
      have hcx : x₀ * c₁ = c₁ * x₀ :=
        Subgroup.mem_centralizer_singleton_iff.1 hx.2
      calc x₀⁻¹ * c₁ * x₀ = x₀⁻¹ * (c₁ * x₀) := by group
        _ = x₀⁻¹ * (x₀ * c₁) := by rw [← hcx]
        _ = c₁ := by group
    rw [hc] at hx₀c₁
    have h1 : c₁ * 1 = c₁ * w₀ := by simpa using hx₀c₁
    exact hw₀1 (mul_left_cancel h1).symm
  have hT₀U : T₀ ≤ U := by
    intro t ht
    refine Subgroup.mem_inf.mpr ⟨ht.1, ?_⟩
    rw [show H = swapStabilizer c₁ w₀ hw₀2 from rfl, mem_swapStabilizer]
    refine ⟨hw t ht.1, Or.inl ?_⟩
    have hct : t * c₁ = c₁ * t := Subgroup.mem_centralizer_singleton_iff.1 ht.2
    calc t⁻¹ * c₁ * t = t⁻¹ * (c₁ * t) := by group
      _ = t⁻¹ * (t * c₁) := by rw [← hct]
      _ = c₁ := by group
  have hUT : U ⊓ Subgroup.centralizer {c₁} = T₀ := by
    ext x
    constructor
    · rintro ⟨hxU, hxC⟩
      exact Subgroup.mem_inf.mpr ⟨hUS hxU, hxC⟩
    · intro hx
      exact Subgroup.mem_inf.mpr ⟨hT₀U hx, hx.2⟩
  have hcardU : Nat.card U = 2 * Nat.card T₀ := by
    have hidx : ((U ⊓ Subgroup.centralizer {c₁} : Subgroup G).subgroupOf U).index ≤ 2 :=
      index_le_two_of_le_swapStabilizer (c₁ := c₁) (w₀ := w₀) (hw₀ := hw₀2) hUH
    have hne : ((U ⊓ Subgroup.centralizer {c₁} : Subgroup G).subgroupOf U) ≠ ⊤ := by
      intro htop
      have hx : (⟨x₀, hx₀U⟩ : ↥U) ∈
          ((U ⊓ Subgroup.centralizer {c₁} : Subgroup G).subgroupOf U) := by
        rw [htop]
        exact Subgroup.mem_top _
      have hx' : x₀ ∈ U ⊓ Subgroup.centralizer {c₁} := Subgroup.mem_subgroupOf.mp hx
      exact hx₀T (hUT ▸ hx')
    have hne1 : ((U ⊓ Subgroup.centralizer {c₁} : Subgroup G).subgroupOf U).index ≠ 1 :=
      fun h1 => hne (Subgroup.index_eq_one.mp h1)
    have hne0 := Subgroup.index_ne_zero_of_finite
      (H := ((U ⊓ Subgroup.centralizer {c₁} : Subgroup G).subgroupOf U))
    have hidx2 : ((U ⊓ Subgroup.centralizer {c₁} : Subgroup G).subgroupOf U).index = 2 := by
      omega
    have hcard := Subgroup.card_mul_index
      ((U ⊓ Subgroup.centralizer {c₁} : Subgroup G).subgroupOf U)
    have hcardsub : Nat.card ((U ⊓ Subgroup.centralizer {c₁} : Subgroup G).subgroupOf U) =
        Nat.card (U ⊓ Subgroup.centralizer {c₁} : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [hcardsub, hidx2, hUT] at hcard
    calc Nat.card U = Nat.card T₀ * 2 := hcard.symm
      _ = 2 * Nat.card T₀ := by rw [mul_comm]
  have hcardH : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ H → Nat.card P ≤ Nat.card U := by
    intro P hP hPH
    have h1 := card_le_two_mul_card_inf_centralizer (c₁ := c₁) (w₀ := w₀) (hw₀ := hw₀2) hPH
    have h2 : Nat.card (P ⊓ Subgroup.centralizer {c₁} : Subgroup G) ≤ Nat.card T₀ := by
      let Q : Subgroup G := P ⊓ Subgroup.centralizer {c₁}
      have hQ2 : IsPGroup 2 Q := hP.to_le inf_le_left
      have hQC : Q ≤ Subgroup.centralizer {c₁} := inf_le_right
      obtain ⟨x, hxC, hxS⟩ := hsyl Q hQ2 hQC
      have hmap_le : Q.map (MulAut.conj x⁻¹).toMonoidHom ≤ T₀ := by
        rintro _ ⟨q, hq, rfl⟩
        have hqmap : (MulEquiv.toMonoidHom (MulAut.conj x⁻¹)) q = x⁻¹ * q * x := by
          simp
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · simpa [hqmap] using hxS q hq
        · have hqC : q * c₁ = c₁ * q := Subgroup.mem_centralizer_singleton_iff.1 hq.2
          have hxinv : x⁻¹ * c₁ = c₁ * x⁻¹ :=
            Subgroup.mem_centralizer_singleton_iff.1 ((Subgroup.centralizer {c₁}).inv_mem hxC)
          rw [hqmap, Subgroup.mem_centralizer_singleton_iff]
          calc x⁻¹ * q * x * c₁ = x⁻¹ * q * (x * c₁) := by group
            _ = x⁻¹ * q * (c₁ * x) := by
                rw [Subgroup.mem_centralizer_singleton_iff.1 hxC]
            _ = x⁻¹ * (q * c₁) * x := by group
            _ = x⁻¹ * (c₁ * q) * x := by rw [hqC]
            _ = (x⁻¹ * c₁) * q * x := by group
            _ = (c₁ * x⁻¹) * q * x := by rw [hxinv]
            _ = c₁ * (x⁻¹ * q * x) := by group
      have hmap_card : Nat.card (Q.map (MulAut.conj x⁻¹).toMonoidHom) = Nat.card Q :=
        Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective
      calc Nat.card Q = Nat.card (Q.map (MulAut.conj x⁻¹).toMonoidHom) := hmap_card.symm
        _ ≤ Nat.card T₀ := Subgroup.card_le_of_le hmap_le
    calc Nat.card P ≤ 2 * Nat.card (P ⊓ Subgroup.centralizer {c₁} : Subgroup G) := h1
      _ ≤ 2 * Nat.card T₀ := Nat.mul_le_mul_left 2 h2
      _ = Nat.card U := hcardU.symm
  let UH : Subgroup ↥H := U.subgroupOf H
  have hUH2 : IsPGroup 2 UH := hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUH).symm
  obtain ⟨P, hUP⟩ := hUH2.exists_le_sylow
  let PG : Subgroup G := (P : Subgroup ↥H).map H.subtype
  have hPG2 : IsPGroup 2 PG := P.isPGroup'.map H.subtype
  have hPGH : PG ≤ H := Subgroup.map_subtype_le _
  have hUPG : U ≤ PG := by
    intro u hu
    exact ⟨⟨u, hUH hu⟩, hUP (Subgroup.mem_subgroupOf.mpr hu), rfl⟩
  have hPGcard : Nat.card PG = Nat.card (P : Subgroup ↥H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hle : Nat.card PG ≤ Nat.card U := hcardH PG hPG2 hPGH
  have hge : Nat.card U ≤ Nat.card PG := Subgroup.card_le_of_le hUPG
  have hPGeq : PG = U := (Subgroup.eq_of_le_of_card_ge hUPG hle).symm
  have hPUH : (P : Subgroup ↥H) = UH := by
    ext x
    constructor
    · intro hx
      have hxPG : (x : G) ∈ PG := ⟨x, hx, rfl⟩
      rw [hPGeq] at hxPG
      exact Subgroup.mem_subgroupOf.mpr hxPG
    · intro hx
      have hxU : (x : G) ∈ U := Subgroup.mem_subgroupOf.mp hx
      have hxPG : (x : G) ∈ PG := by rw [hPGeq]; exact hxU
      obtain ⟨p, hp, hpx⟩ := hxPG
      have hpx' : p = x := Subtype.ext hpx
      rwa [← hpx']
  have hWH : W ≤ H := by
    intro h hh
    rw [show H = swapStabilizer c₁ w₀ hw₀2 from rfl, mem_swapStabilizer]
    exact ⟨Subgroup.mem_centralizer_singleton_iff.1 (hWw hh), hWc h hh⟩
  let WH : Subgroup ↥H := W.subgroupOf H
  have hWH2 : IsPGroup 2 WH := hW.of_equiv (Subgroup.subgroupOfEquivOfLe hWH).symm
  obtain ⟨Q, hWQ⟩ := hWH2.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥H Q P
  have hkW : ∀ h ∈ W, (k : G) * h * (k : G)⁻¹ ∈ U := by
    intro h hh
    have hhWH : (⟨h, hWH hh⟩ : ↥H) ∈ (WH : Subgroup ↥H) :=
      Subgroup.mem_subgroupOf.mpr hh
    have hQ : (⟨h, hWH hh⟩ : ↥H) ∈ (Q : Subgroup ↥H) := hWQ hhWH
    have hmem : MulAut.conj k (⟨h, hWH hh⟩ : ↥H) ∈ (P : Subgroup ↥H) := by
      rw [← hk, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hQ
    rw [hPUH] at hmem
    have hmemU : ((MulAut.conj k (⟨h, hWH hh⟩ : ↥H) : ↥H) : G) ∈ U :=
      Subgroup.mem_subgroupOf.mp hmem
    simpa [MulAut.conj_apply] using hmemU
  have hkH : (k : G) ∈ H := k.2
  have hkw : (k : G) * w₀ = w₀ * k := (mem_swapStabilizer.mp hkH).1
  have hkc : (k : G) * c₁ * (k : G)⁻¹ = c₁ ∨
      (k : G) * c₁ * (k : G)⁻¹ = c₁ * w₀ := conj_mem_swapStabilizer hkH
  have hx₀w : x₀ * w₀ = w₀ * x₀ := hw x₀ hx₀
  have hx₀c₁' : x₀ * c₁ * x₀⁻¹ = c₁ * w₀ := by
    have h1 : c₁ = x₀ * (c₁ * w₀) * x₀⁻¹ := by
      calc c₁ = x₀ * (x₀⁻¹ * c₁ * x₀) * x₀⁻¹ := by group
        _ = x₀ * (c₁ * w₀) * x₀⁻¹ := by rw [hx₀c₁]
    have h2 : x₀ * w₀ * x₀⁻¹ = w₀ := by
      calc x₀ * w₀ * x₀⁻¹ = (x₀ * w₀) * x₀⁻¹ := by rw [mul_assoc]
        _ = (w₀ * x₀) * x₀⁻¹ := by rw [hx₀w]
        _ = w₀ := by group
    have h3 : c₁ = (x₀ * c₁ * x₀⁻¹) * w₀ := by
      calc c₁ = x₀ * (c₁ * w₀) * x₀⁻¹ := h1
        _ = (x₀ * c₁ * x₀⁻¹) * (x₀ * w₀ * x₀⁻¹) := by group
        _ = (x₀ * c₁ * x₀⁻¹) * w₀ := by rw [h2]
    calc x₀ * c₁ * x₀⁻¹ = (x₀ * c₁ * x₀⁻¹) * 1 := by group
      _ = (x₀ * c₁ * x₀⁻¹) * (w₀ * w₀) := by rw [hw₀2]
      _ = ((x₀ * c₁ * x₀⁻¹) * w₀) * w₀ := by group
      _ = c₁ * w₀ := by rw [← h3]
  have hcomm_of_conj {x : G} (h : x⁻¹ * c₁ * x = c₁) : x * c₁ = c₁ * x := by
    have h1 : x * c₁ * x⁻¹ = c₁ := by
      calc x * c₁ * x⁻¹ = x * (x⁻¹ * c₁ * x) * x⁻¹ := by rw [h]
        _ = c₁ := by group
    calc x * c₁ = x * c₁ * x⁻¹ * x := by group
      _ = c₁ * x := by rw [h1]
  rcases hkc with hkc | hkc
  · refine ⟨(k : G)⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have hcomm : (k : G) * c₁ = c₁ * k := by
          calc (k : G) * c₁ = (k : G) * c₁ * (k : G)⁻¹ * k := by group
            _ = c₁ * k := by rw [hkc]
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Commute.inv_left ((commute_iff_eq _ _).2 hcomm)).eq
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Commute.inv_left ((commute_iff_eq _ _).2 hkw)).eq
    · intro h hh
      have hmem := hkW h hh
      simpa using hUS hmem
  · refine ⟨(k : G)⁻¹ * x₀⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have hyconj : ((k : G)⁻¹ * x₀⁻¹)⁻¹ * c₁ * ((k : G)⁻¹ * x₀⁻¹) = c₁ := by
          calc ((k : G)⁻¹ * x₀⁻¹)⁻¹ * c₁ * ((k : G)⁻¹ * x₀⁻¹)
              = x₀ * ((k : G) * c₁ * (k : G)⁻¹) * x₀⁻¹ := by group
            _ = x₀ * (c₁ * w₀) * x₀⁻¹ := by rw [hkc]
            _ = (x₀ * c₁ * x₀⁻¹) * (x₀ * w₀ * x₀⁻¹) := by group
            _ = (x₀ * c₁ * x₀⁻¹) * w₀ := by
                congr 1
                calc x₀ * w₀ * x₀⁻¹ = (x₀ * w₀) * x₀⁻¹ := by rw [mul_assoc]
                  _ = (w₀ * x₀) * x₀⁻¹ := by rw [hx₀w]
                  _ = w₀ := by group
            _ = (c₁ * w₀) * w₀ := by rw [hx₀c₁']
            _ = c₁ := by rw [mul_assoc, hw₀2, mul_one]
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm_of_conj hyconj)
      · have hkw' : (k : G)⁻¹ * w₀ = w₀ * (k : G)⁻¹ :=
          by
          simpa using (Commute.inv_left ((commute_iff_eq _ _).2 hkw)).eq
        have hx₀w' : x₀⁻¹ * w₀ = w₀ * x₀⁻¹ :=
          (Commute.inv_left ((commute_iff_eq _ _).2 hx₀w)).eq
        exact Subgroup.mem_centralizer_singleton_iff.mpr (by
          calc ((k : G)⁻¹ * x₀⁻¹) * w₀ = (k : G)⁻¹ * (x₀⁻¹ * w₀) := by group
            _ = (k : G)⁻¹ * (w₀ * x₀⁻¹) := by rw [hx₀w']
            _ = ((k : G)⁻¹ * w₀) * x₀⁻¹ := by group
            _ = (w₀ * (k : G)⁻¹) * x₀⁻¹ := by rw [hkw']
            _ = w₀ * ((k : G)⁻¹ * x₀⁻¹) := by rw [mul_assoc])
    · intro h hh
      have hmem := hUS (hkW h hh)
      have hx₀S : x₀ ∈ S := hx₀
      have hconj_mem : x₀ * ((k : G) * h * (k : G)⁻¹) * x₀⁻¹ ∈ S :=
        S.mul_mem (S.mul_mem hx₀S hmem) (S.inv_mem hx₀S)
      simpa [mul_assoc] using hconj_mem

theorem isConj_of_isConj_mul (S : Sylow 2 G) {c₁ w₀ k : G} (hc₁S : c₁ ∈ (S : Subgroup G))
    (hc₁2 : c₁ * c₁ = 1) (hc₁1 : c₁ ≠ 1)
    (hw : ∀ x ∈ (S : Subgroup G), x * w₀ = w₀ * x)
    (hK4 : ∀ l ∈ (S : Subgroup G), l * l = 1 → l ≠ 1 → l ≠ w₀ →
      ∃ q ∈ (S : Subgroup G), q⁻¹ * l * q = l * w₀)
    (hc₁w₀ : ¬ IsConj c₁ w₀) (hkc₁ : k * c₁ = c₁ * k) (hne : c₁ ≠ k)
    (hq : IsConj k (c₁ * k)) (htype : IsConj k c₁ ∨ IsConj k w₀) :
    IsConj k c₁ := by
  rcases htype with h | h
  · exact h
  · exfalso
    have hfact : ∀ x ∈ (S : Subgroup G), IsConj c₁ x → x ≠ w₀ →
        ∃ q ∈ (S : Subgroup G), q⁻¹ * x * q = x * w₀ := by
      intro x hxS hcx hxw
      have hx2 : x * x = 1 := by
        obtain ⟨g, hg⟩ := isConj_iff.1 hcx
        calc x * x = (g * c₁ * g⁻¹) * (g * c₁ * g⁻¹) := by rw [hg]
          _ = g * (c₁ * c₁) * g⁻¹ := by group
          _ = 1 := by rw [hc₁2]; group
      have hx1 : x ≠ 1 := by
        intro hx
        apply hc₁1
        rw [hx] at hcx
        exact isConj_one_left.1 hcx
      exact hK4 x hxS hx2 hx1 hxw
    have hzS : (S : Subgroup G) ≤ Subgroup.centralizer {w₀} := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hw x hx)
    have hconj : IsConj c₁ (c₁ * k) :=
      Stroth76.isConj_mul_of_isConj_central_of_conj S hzS hfact h hc₁S hkc₁.symm hne
    exact hc₁w₀ (hconj.trans (hq.symm.trans h))

theorem false_of_swap {S T Du Dk : Subgroup G} {c₁ w₀ x₀ a₁ k : G} (hS : IsPGroup 2 S)
    (hT : T = S ⊓ Subgroup.centralizer {c₁})
    (hsyl : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.centralizer {c₁} →
      ∃ x ∈ Subgroup.centralizer {c₁}, ∀ q ∈ Q, x⁻¹ * q * x ∈ S)
    (hc₁S : c₁ ∈ S)
    (hw₀S : w₀ ∈ S) (hw : ∀ y ∈ S, y * w₀ = w₀ * y) (hw₀2 : w₀ * w₀ = 1) (hw₀1 : w₀ ≠ 1)
    (hc₁w₀ : ¬ IsConj c₁ w₀) (hx₀ : x₀ ∈ S) (hx₀c₁ : x₀⁻¹ * c₁ * x₀ = c₁ * w₀)
    (hkT : k ∈ T) (hkDk : k ∈ Dk) (hkDu : k ∉ Du) (hk2 : k * k = 1) (hkc₁ : k ≠ c₁)
    (hk : IsConj k c₁) (hc₁k : IsConj (c₁ * k) c₁)
    (hDu : ∀ l ∈ Du, l * l = 1 → l ≠ 1 → l ≠ c₁ → IsConj l c₁ → ¬ IsConj (c₁ * l) c₁)
    (hT4 : ∀ y ∈ T, y ∉ Du → y * y = 1 →
      Nat.card (T ⊓ Subgroup.centralizer {y} : Subgroup G) ≤
        Nat.card (T ⊓ Subgroup.centralizer {k} : Subgroup G))
    (hDk : ∀ y ∈ T, y ∉ Du → y * y = 1 → y ∉ Dk →
      Nat.card (T ⊓ Subgroup.centralizer {y} : Subgroup G) <
        Nat.card (T ⊓ Subgroup.centralizer {k} : Subgroup G))
    (ha₁ : a₁ ∈ T) (hT6 : ∀ y ∈ Dk, y ∉ Du → a₁⁻¹ * y * a₁ = w₀ * y)
    (hZ : ∀ z ∈ T ⊓ Subgroup.centralizer {k},
      (∀ y ∈ T ⊓ Subgroup.centralizer {k}, z * y = y * z) →
        z = 1 ∨ z = c₁ ∨ z = w₀ ∨ z = c₁ * w₀ ∨ z = k ∨ z = c₁ * k ∨ z = w₀ * k ∨
          z = c₁ * w₀ * k)
    (hT78 : ∀ y ∈ Dk, y ∉ Du → y * y = 1 → ∀ x ∈ S, x * y = y * x → x * c₁ = c₁ * x) :
    False := by
  classical
  have hc₁2 : c₁ * c₁ = 1 := by
    obtain ⟨h, hh⟩ := isConj_iff.1 hk
    calc c₁ * c₁ = (h * k * h⁻¹) * (h * k * h⁻¹) := by rw [hh]
      _ = h * (k * k) * h⁻¹ := by group
      _ = 1 := by rw [hk2]; group
  have hc₁1 : c₁ ≠ 1 := by
    intro h1
    have hk1 : k = 1 := by
      obtain ⟨h, hh⟩ := isConj_iff.1 hk
      rw [h1] at hh
      calc k = h⁻¹ * (h * k * h⁻¹) * h := by group
        _ = 1 := by rw [hh]; group
    exact hkc₁ (hk1.trans h1.symm)
  have hk1 : k ≠ 1 := by
    intro h
    have hc1 : c₁ = 1 := by
      have h' := hk
      rw [h] at h'
      exact isConj_one_right.1 h'
    exact hkc₁ (by rw [h, hc1])
  have hTS : T ≤ S := by rw [hT]; exact inf_le_left
  have hTC : T ≤ Subgroup.centralizer {c₁} := by rw [hT]; exact inf_le_right
  have hkS : k ∈ S := hTS hkT
  have hkc : k * c₁ = c₁ * k :=
    Subgroup.mem_centralizer_singleton_iff.1 (hTC hkT)
  have hw₀T : w₀ ∈ T := by
    rw [hT]
    exact Subgroup.mem_inf.mpr ⟨hw₀S,
      Subgroup.mem_centralizer_singleton_iff.mpr (hw c₁ hc₁S).symm⟩
  set R : Subgroup G := T ⊓ Subgroup.centralizer {k} with hR
  have hRT : R ≤ T := by rw [hR]; exact inf_le_left
  have hR2 : IsPGroup 2 R := (hS.to_le hTS).to_le hRT
  have hkR : k ∈ R := by
    rw [hR]
    exact Subgroup.mem_inf.mpr ⟨hkT,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hc₁T : c₁ ∈ T := by
    rw [hT]
    exact Subgroup.mem_inf.mpr ⟨hc₁S,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hc₁R : c₁ ∈ R := by
    rw [hR]
    exact Subgroup.mem_inf.mpr ⟨hc₁T,
      Subgroup.mem_centralizer_singleton_iff.mpr hkc.symm⟩
  have hw₀R : w₀ ∈ R := by
    rw [hR]
    exact Subgroup.mem_inf.mpr ⟨hw₀T,
      Subgroup.mem_centralizer_singleton_iff.mpr (hw k hkS).symm⟩
  obtain ⟨h₀, hh₀⟩ := isConj_iff.1 hk
  let g₀ : G := h₀⁻¹
  have hg₀ : g₀⁻¹ * k * g₀ = c₁ := by
    simpa [g₀] using hh₀
  let R₀ : Subgroup G := R.map (MulAut.conj g₀⁻¹).toMonoidHom
  have hR₀2 : IsPGroup 2 R₀ := hR2.map _
  have hR₀C : R₀ ≤ Subgroup.centralizer {c₁} := by
    rintro _ ⟨r, hr, rfl⟩
    have hr' : r ∈ T ⊓ Subgroup.centralizer {k} := hR ▸ hr
    have hrk : r * k = k * r :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hr').2
    have hcomm := ((commute_iff_eq r k).2 hrk).conj g₀⁻¹
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      simpa [MulAut.conj_apply, hg₀] using hcomm.eq)
  obtain ⟨x, hxC, hxS⟩ := hsyl R₀ hR₀2 hR₀C
  have hxcomm : x * c₁ = c₁ * x :=
    Subgroup.mem_centralizer_singleton_iff.1 hxC
  have hxinv : x⁻¹ * c₁ * x = c₁ := by
    calc x⁻¹ * c₁ * x = x⁻¹ * (c₁ * x) := by group
      _ = x⁻¹ * (x * c₁) := by rw [← hxcomm]
      _ = c₁ := by group
  let g : G := g₀ * x
  have hgk : g⁻¹ * k * g = c₁ := by
    calc g⁻¹ * k * g = x⁻¹ * (g₀⁻¹ * k * g₀) * x := by
          simp [g]
          group
      _ = x⁻¹ * c₁ * x := by rw [hg₀]
      _ = c₁ := hxinv
  have hgR_le : ∀ r ∈ R, g⁻¹ * r * g ∈ T := by
    intro r hr
    have hr' : r ∈ T ⊓ Subgroup.centralizer {k} := hR ▸ hr
    have hrT : r ∈ T := (Subgroup.mem_inf.1 hr').1
    have hrk : r * k = k * r :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hr').2
    have hrR₀ : (MulAut.conj g₀⁻¹) r ∈ R₀ := ⟨r, hr, rfl⟩
    have hmemS : g⁻¹ * r * g ∈ S := by
      have h := hxS _ hrR₀
      simpa [g, MulAut.conj_apply, mul_assoc] using h
    have hcomm := ((commute_iff_eq r k).2 hrk).conj g⁻¹
    have hcommc : (g⁻¹ * r * g) * c₁ = c₁ * (g⁻¹ * r * g) := by
      simpa [hgk] using hcomm.eq
    rw [hT]
    exact Subgroup.mem_inf.mpr ⟨hmemS,
      Subgroup.mem_centralizer_singleton_iff.mpr hcommc⟩
  let k' : G := g⁻¹ * c₁ * g
  have hk'T : k' ∈ T := hgR_le c₁ hc₁R
  have hk'2 : k' * k' = 1 := by
    calc (g⁻¹ * c₁ * g) * (g⁻¹ * c₁ * g) = g⁻¹ * (c₁ * c₁) * g := by group
      _ = 1 := by rw [hc₁2]; group
  have hk'conj : IsConj k' c₁ := by
    refine isConj_iff.2 ⟨g, ?_⟩
    change g * (g⁻¹ * c₁ * g) * g⁻¹ = c₁
    group
  have hk'1 : k' ≠ 1 := by
    intro h
    have hk'g : g⁻¹ * c₁ * g = 1 := by simpa [k'] using h
    have hconj : IsConj c₁ 1 := by
      refine isConj_iff.2 ⟨g⁻¹, ?_⟩
      simpa using hk'g
    exact hc₁1 (isConj_one_left.1 hconj)
  have hk'c₁ : k' ≠ c₁ := by
    intro h
    have hk'g : g⁻¹ * c₁ * g = c₁ := by simpa [k'] using h
    have hgcomm : g * c₁ = c₁ * g := by
      have h1 : g * c₁ * g⁻¹ = c₁ := by
        calc g * c₁ * g⁻¹ = g * (g⁻¹ * c₁ * g) * g⁻¹ := by rw [hk'g]
          _ = c₁ := by group
      calc g * c₁ = g * c₁ * g⁻¹ * g := by group
        _ = c₁ * g := by rw [h1]
    have hg₀comm : g₀ * c₁ = c₁ * g₀ := by
      have hxinvcomm : x⁻¹ * c₁ = c₁ * x⁻¹ :=
        (Commute.inv_left ((commute_iff_eq x c₁).2 hxcomm)).eq
      have hgcomm' : g * x⁻¹ * c₁ = c₁ * (g * x⁻¹) := by
        calc g * x⁻¹ * c₁ = g * (x⁻¹ * c₁) := by group
          _ = g * (c₁ * x⁻¹) := by rw [hxinvcomm]
          _ = (g * c₁) * x⁻¹ := by group
          _ = (c₁ * g) * x⁻¹ := by rw [hgcomm]
          _ = c₁ * (g * x⁻¹) := by group
      have hg₀eq : g₀ = g * x⁻¹ := by simp [g, mul_assoc]
      rwa [hg₀eq]
    have hk_eq : k = c₁ := by
      have hcomm : Commute g₀ c₁ := (commute_iff_eq g₀ c₁).2 hg₀comm
      calc k = g₀ * (g₀⁻¹ * k * g₀) * g₀⁻¹ := by group
        _ = g₀ * c₁ * g₀⁻¹ := by rw [hg₀]
        _ = c₁ := by rw [hcomm.eq]; group
    exact hkc₁ hk_eq
  have hk'Du : k' ∉ Du := by
    intro hk'Du
    refine hDu k' hk'Du hk'2 hk'1 hk'c₁ hk'conj ?_
    have hc₁k' : IsConj (c₁ * k') c₁ := by
      have hconj : IsConj (c₁ * k) (c₁ * k') := by
        refine isConj_iff.2 ⟨g⁻¹, ?_⟩
        calc g⁻¹ * (c₁ * k) * (g⁻¹)⁻¹ = (g⁻¹ * k * g) * (g⁻¹ * c₁ * g) := by
              rw [inv_inv]
              calc g⁻¹ * (c₁ * k) * g = g⁻¹ * (k * c₁) * g := by rw [hkc]
                _ = (g⁻¹ * k * g) * (g⁻¹ * c₁ * g) := by group
          _ = c₁ * k' := by rw [hgk]
      exact hconj.symm.trans hc₁k
    exact hc₁k'
  let K' : Subgroup G := T ⊓ Subgroup.centralizer {k'}
  have hRg_le : R.map (MulAut.conj g⁻¹).toMonoidHom ≤ K' := by
    rintro _ ⟨r, hr, rfl⟩
    have hr' : r ∈ T ⊓ Subgroup.centralizer {k} := hR ▸ hr
    have hrT : r ∈ T := (Subgroup.mem_inf.1 hr').1
    have hrC : r * c₁ = c₁ * r :=
      Subgroup.mem_centralizer_singleton_iff.1 (hTC hrT)
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · simpa [MulAut.conj_apply] using hgR_le r hr
    have hcomm := ((commute_iff_eq r c₁).2 hrC).conj g⁻¹
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      simpa [MulAut.conj_apply, k'] using hcomm.eq)
  have hRg_card : Nat.card (R.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card R :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hK'card_le : Nat.card K' ≤ Nat.card R := by
    have h := hT4 k' hk'T hk'Du hk'2
    rw [hR] at h
    exact h
  have hRg_eq : R.map (MulAut.conj g⁻¹).toMonoidHom = K' :=
    Subgroup.eq_of_le_of_card_ge hRg_le (by rw [hRg_card]; exact hK'card_le)
  have hk'Dk : k' ∈ Dk := by
    by_contra hk'Dk
    have hlt : Nat.card K' < Nat.card R := by
      have h := hDk k' hk'T hk'Du hk'2 hk'Dk
      rw [hR] at h
      exact h
    have heq : Nat.card K' = Nat.card R := by rw [← hRg_eq, hRg_card]
    omega
  have hk't6 : a₁⁻¹ * k' * a₁ = w₀ * k' := hT6 k' hk'Dk hk'Du
  have ha₁c : a₁ * c₁ = c₁ * a₁ :=
    Subgroup.mem_centralizer_singleton_iff.1 (hTC ha₁)
  have hK'_norm_le : K'.map (MulAut.conj a₁⁻¹).toMonoidHom ≤ K' := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ T ⊓ Subgroup.centralizer {k'} := hy
    have hyT : y ∈ T := (Subgroup.mem_inf.1 hy').1
    have hyk' : y * k' = k' * y :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hy').2
    have hqmap : (MulEquiv.toMonoidHom (MulAut.conj a₁⁻¹)) y = a₁⁻¹ * y * a₁ := by
      simp
    rw [hqmap]
    have hqT : a₁⁻¹ * y * a₁ ∈ T := T.mul_mem (T.mul_mem (T.inv_mem ha₁) hyT) ha₁
    refine Subgroup.mem_inf.mpr ⟨hqT, ?_⟩
    have hw₀k' : w₀ * (w₀ * k') = k' := by rw [← mul_assoc, hw₀2, one_mul]
    have hq_w : (a₁⁻¹ * y * a₁) * w₀ = w₀ * (a₁⁻¹ * y * a₁) :=
      hw _ (hTS hqT)
    have hq_wk : (a₁⁻¹ * y * a₁) * (w₀ * k') = (w₀ * k') * (a₁⁻¹ * y * a₁) := by
      have h := ((commute_iff_eq y k').2 hyk').conj a₁⁻¹
      simpa [MulAut.conj_apply, hk't6] using h.eq
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (a₁⁻¹ * y * a₁) * k' = (a₁⁻¹ * y * a₁) * (w₀ * (w₀ * k')) := by
          rw [hw₀k']
      _ = ((a₁⁻¹ * y * a₁) * w₀) * (w₀ * k') := by group
      _ = (w₀ * (a₁⁻¹ * y * a₁)) * (w₀ * k') := by rw [hq_w]
      _ = w₀ * ((a₁⁻¹ * y * a₁) * (w₀ * k')) := by group
      _ = w₀ * ((w₀ * k') * (a₁⁻¹ * y * a₁)) := by rw [hq_wk]
      _ = (w₀ * (w₀ * k')) * (a₁⁻¹ * y * a₁) := by group
      _ = k' * (a₁⁻¹ * y * a₁) := by rw [hw₀k']
  have hK'_norm_eq : K'.map (MulAut.conj a₁⁻¹).toMonoidHom = K' :=
    Subgroup.eq_of_le_of_card_ge hK'_norm_le (by
      rw [Subgroup.card_map_of_injective (MulAut.conj a₁⁻¹).injective])
  let n : G := g * a₁ * g⁻¹
  have ha₁c_inv : a₁⁻¹ * c₁ * a₁ = c₁ := by
    calc a₁⁻¹ * c₁ * a₁ = a₁⁻¹ * (c₁ * a₁) := by group
      _ = a₁⁻¹ * (a₁ * c₁) := by rw [← ha₁c]
      _ = c₁ := by group
  have hgk' : g * k' * g⁻¹ = c₁ := by
    change g * (g⁻¹ * c₁ * g) * g⁻¹ = c₁
    group
  have hnk : n⁻¹ * k * n = k := by
    calc n⁻¹ * k * n = g * a₁⁻¹ * (g⁻¹ * k * g) * a₁ * g⁻¹ := by
          simp [n]
          group
      _ = g * a₁⁻¹ * c₁ * a₁ * g⁻¹ := by rw [hgk]
      _ = g * (a₁⁻¹ * c₁ * a₁) * g⁻¹ := by group
      _ = g * c₁ * g⁻¹ := by rw [ha₁c_inv]
      _ = k := by rw [← hgk]; group
  have hnc₁ : n⁻¹ * c₁ * n = (g * w₀ * g⁻¹) * c₁ := by
    calc n⁻¹ * c₁ * n = g * a₁⁻¹ * (g⁻¹ * c₁ * g) * a₁ * g⁻¹ := by
          simp [n]
          group
      _ = g * a₁⁻¹ * k' * a₁ * g⁻¹ := by rfl
      _ = g * (a₁⁻¹ * k' * a₁) * g⁻¹ := by group
      _ = g * (w₀ * k') * g⁻¹ := by rw [hk't6]
      _ = (g * w₀ * g⁻¹) * c₁ := by rw [← hgk']; group
  have hmemR : ∀ z : G, z ∈ R ↔ g⁻¹ * z * g ∈ K' := by
    intro z
    constructor
    · intro hz
      have hz' : (MulAut.conj g⁻¹) z ∈ R.map (MulAut.conj g⁻¹).toMonoidHom :=
        ⟨z, hz, rfl⟩
      have hz'' : (MulAut.conj g⁻¹) z ∈ K' := by rwa [hRg_eq] at hz'
      simpa [MulAut.conj_apply] using hz''
    · intro hz
      have hz' : (MulAut.conj g⁻¹) z ∈ R.map (MulAut.conj g⁻¹).toMonoidHom := by
        rw [hRg_eq]
        simpa [MulAut.conj_apply] using hz
      obtain ⟨r, hr, hr_eq⟩ := hz'
      have hrz : r = z := by
        have := congrArg (MulAut.conj g) hr_eq
        simpa [MulAut.conj_apply] using this
      rwa [hrz] at hr
  have hn_norm_R : ∀ y ∈ R, n⁻¹ * y * n ∈ R := by
    intro y hy
    refine (hmemR _).mpr ?_
    have hyK' : g⁻¹ * y * g ∈ K' := (hmemR y).mp hy
    have hstep : a₁⁻¹ * (g⁻¹ * y * g) * a₁ ∈ K' := by
      rw [← hK'_norm_eq]
      exact ⟨g⁻¹ * y * g, hyK', by simp⟩
    have hgoal : g⁻¹ * (n⁻¹ * y * n) * g = a₁⁻¹ * (g⁻¹ * y * g) * a₁ := by
      simp [n]
      group
    rw [hgoal]
    exact hstep
  have hn_norm_R' : ∀ y ∈ R, n * y * n⁻¹ ∈ R := by
    intro y hy
    have hmap_le : R.map (MulAut.conj n⁻¹).toMonoidHom ≤ R := by
      rintro _ ⟨r, hr, rfl⟩
      simpa [MulAut.conj_apply] using hn_norm_R r hr
    have hcardmap : Nat.card (R.map (MulAut.conj n⁻¹).toMonoidHom) = Nat.card R :=
      Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective
    have hmap_eq : R.map (MulAut.conj n⁻¹).toMonoidHom = R :=
      Subgroup.eq_of_le_of_card_ge hmap_le (by rw [hcardmap])
    have hy' : y ∈ R.map (MulAut.conj n⁻¹).toMonoidHom := by rw [hmap_eq]; exact hy
    obtain ⟨r, hr, hry⟩ := hy'
    have hrz : r = n * y * n⁻¹ := by
      have hry' : n⁻¹ * r * n = y := by simpa [MulAut.conj_apply] using hry
      calc r = n * (n⁻¹ * r * n) * n⁻¹ := by group
        _ = n * y * n⁻¹ := by rw [hry']
    rwa [hrz] at hr
  have hnNorm : n ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hn_norm_R' y hy
    · intro hy
      have := hn_norm_R _ hy
      simpa [mul_assoc] using this
  have hn2 : IsPGroup 2 (Subgroup.zpowers n) := by
    have ha₁S : a₁ ∈ S := hTS ha₁
    have hnS : n ∈ S.map (MulAut.conj g).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨a₁, ha₁S, ?_⟩
      simp [n, MulAut.conj_apply]
    exact (hS.map (MulAut.conj g).toMonoidHom).to_le (Subgroup.zpowers_le.mpr hnS)
  let W : Subgroup G := R ⊔ Subgroup.zpowers n
  have hW2 : IsPGroup 2 W :=
    IsPGroup.to_sup_of_normal_left' (p := 2) hR2 hn2 (Subgroup.zpowers_le.mpr hnNorm)
  let w : G := g * w₀ * g⁻¹
  have hw₀K' : w₀ ∈ K' := by
    refine Subgroup.mem_inf.mpr ⟨hw₀T, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hw k' (hTS hk'T)).symm
  have hwR : w ∈ R := by
    refine (hmemR w).mpr ?_
    have : g⁻¹ * w * g = w₀ := by simp [w]; group
    rw [this]
    exact hw₀K'
  have hwZ : ∀ y ∈ R, w * y = y * w := by
    intro y hy
    have hyK' : g⁻¹ * y * g ∈ K' := (hmemR y).mp hy
    have hyS : g⁻¹ * y * g ∈ S := hTS (Subgroup.mem_inf.1 hyK').1
    have hcomm : w₀ * (g⁻¹ * y * g) = (g⁻¹ * y * g) * w₀ := (hw _ hyS).symm
    have hyx : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    calc w * y = (g * w₀ * g⁻¹) * (g * (g⁻¹ * y * g) * g⁻¹) := by
          exact congrArg (fun z => (g * w₀ * g⁻¹) * z) hyx
      _ = g * (w₀ * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * w₀) * g⁻¹ := by rw [hcomm]
      _ = (g * (g⁻¹ * y * g) * g⁻¹) * (g * w₀ * g⁻¹) := by group
      _ = y * w := by
          rw [show w = g * w₀ * g⁻¹ from rfl]
          exact congrArg (fun z => z * (g * w₀ * g⁻¹)) hyx.symm
  have hwZ' : ∀ y ∈ T ⊓ Subgroup.centralizer {k}, w * y = y * w := by
    intro y hy
    exact hwZ y (hR.symm ▸ hy)
  have hw_cases := hZ w (hR ▸ hwR) hwZ'
  have hwconj : IsConj w w₀ := (isConj_iff.2 ⟨g, by simp [w]⟩).symm
  have hc₁w₀C : IsConj (c₁ * w₀) c₁ := by
    have h : IsConj c₁ (c₁ * w₀) := by
      refine isConj_iff.2 ⟨x₀⁻¹, ?_⟩
      simpa using hx₀c₁
    exact h.symm
  have hwkC : IsConj (w₀ * k) c₁ := by
    have h : IsConj k (w₀ * k) := by
      refine isConj_iff.2 ⟨a₁⁻¹, ?_⟩
      simpa using hT6 k hkDk hkDu
    exact h.symm.trans hk
  have hc₁w₀kC : IsConj (c₁ * w₀ * k) c₁ := by
    have h1 : IsConj (c₁ * k) (c₁ * w₀ * k) := by
      refine isConj_iff.2 ⟨a₁⁻¹, ?_⟩
      have ha₁c_inv : a₁⁻¹ * c₁ = c₁ * a₁⁻¹ :=
        (Commute.inv_left ((commute_iff_eq a₁ c₁).2 ha₁c)).eq
      calc a₁⁻¹ * (c₁ * k) * (a₁⁻¹)⁻¹ = c₁ * (a₁⁻¹ * k * a₁) := by
            rw [inv_inv]
            calc a₁⁻¹ * (c₁ * k) * a₁ = (a₁⁻¹ * c₁) * k * a₁ := by group
              _ = (c₁ * a₁⁻¹) * k * a₁ := by rw [ha₁c_inv]
              _ = c₁ * (a₁⁻¹ * k * a₁) := by group
        _ = c₁ * (w₀ * k) := by rw [hT6 k hkDk hkDu]
        _ = c₁ * w₀ * k := by group
    exact h1.symm.trans hc₁k
  have hw_eq : w = w₀ := by
    rcases hw_cases with h | h | h | h | h | h | h | h
    · exfalso
      rw [h] at hwconj
      exact hw₀1 (isConj_one_right.1 hwconj)
    · rw [h] at hwconj
      exact absurd hwconj hc₁w₀
    · exact h
    · exfalso
      have h' : IsConj c₁ w₀ := hc₁w₀C.symm.trans (by rwa [h] at hwconj)
      exact hc₁w₀ h'
    · exfalso
      have h' : IsConj c₁ w₀ := hk.symm.trans (by rwa [h] at hwconj)
      exact hc₁w₀ h'
    · exfalso
      have h' : IsConj c₁ w₀ := hc₁k.symm.trans (by rwa [h] at hwconj)
      exact hc₁w₀ h'
    · exfalso
      have h' : IsConj c₁ w₀ := hwkC.symm.trans (by rwa [h] at hwconj)
      exact hc₁w₀ h'
    · exfalso
      have h' : IsConj c₁ w₀ := hc₁w₀kC.symm.trans (by rwa [h] at hwconj)
      exact hc₁w₀ h'
  have hgw : g * w₀ * g⁻¹ = w₀ := by simpa [w] using hw_eq
  have hgn : g * w₀ = w₀ * g := by
    calc g * w₀ = g * w₀ * g⁻¹ * g := by group
      _ = w₀ * g := by rw [hgw]
  have hgninv : g⁻¹ * w₀ = w₀ * g⁻¹ :=
    (Commute.inv_left ((commute_iff_eq g w₀).2 hgn)).eq
  have hnw : n * w₀ = w₀ * n := by
    calc n * w₀ = (g * a₁ * g⁻¹) * w₀ := rfl
      _ = g * a₁ * (g⁻¹ * w₀) := by group
      _ = g * a₁ * (w₀ * g⁻¹) := by rw [hgninv]
      _ = g * (a₁ * w₀) * g⁻¹ := by group
      _ = g * (w₀ * a₁) * g⁻¹ := by rw [hw a₁ (hTS ha₁)]
      _ = (g * w₀) * (a₁ * g⁻¹) := by group
      _ = (w₀ * g) * (a₁ * g⁻¹) := by rw [hgn]
      _ = w₀ * (g * a₁ * g⁻¹) := by group
      _ = w₀ * n := rfl
  have hnc₁' : n⁻¹ * c₁ * n = c₁ * w₀ := by
    calc n⁻¹ * c₁ * n = (g * w₀ * g⁻¹) * c₁ := hnc₁
      _ = w₀ * c₁ := by rw [hgw]
      _ = c₁ * w₀ := (hw c₁ hc₁S).symm
  have hRw : R ≤ Subgroup.centralizer {w₀} := by
    intro r hr
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hw r (hTS (hRT hr)))
  have hWw : W ≤ Subgroup.centralizer {w₀} := by
    refine sup_le hRw ?_
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hnw)
  have hR_H : R ≤ swapStabilizer c₁ w₀ hw₀2 := by
    intro r hr
    rw [mem_swapStabilizer]
    refine ⟨hw r (hTS (hRT hr)), Or.inl ?_⟩
    have hrc : r * c₁ = c₁ * r :=
      Subgroup.mem_centralizer_singleton_iff.1 (hTC (hRT hr))
    calc r⁻¹ * c₁ * r = r⁻¹ * (c₁ * r) := by group
      _ = r⁻¹ * (r * c₁) := by rw [← hrc]
      _ = c₁ := by group
  have hn_H : n ∈ swapStabilizer c₁ w₀ hw₀2 := by
    rw [mem_swapStabilizer]
    exact ⟨hnw, Or.inr hnc₁'⟩
  have hWH : W ≤ swapStabilizer c₁ w₀ hw₀2 :=
    sup_le hR_H (Subgroup.zpowers_le.mpr hn_H)
  have hWc : ∀ z ∈ W, z⁻¹ * c₁ * z = c₁ ∨ z⁻¹ * c₁ * z = c₁ * w₀ :=
    fun z hz => (mem_swapStabilizer.mp (hWH hz)).2
  obtain ⟨y, hyC, hyS⟩ :=
    exists_conj_le_of_swap (S := S) (W := W) (c₁ := c₁) (w₀ := w₀) (x₀ := x₀)
      hS hsyl hw hw₀2 hw₀1 hx₀ hx₀c₁ hW2 hWw hWc
  have hyc₁ : y * c₁ = c₁ * y :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hyC).1
  have hyw₀ : y * w₀ = w₀ * y :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hyC).2
  have hyc : y⁻¹ * c₁ * y = c₁ := by
    calc y⁻¹ * c₁ * y = y⁻¹ * (c₁ * y) := by group
      _ = y⁻¹ * (y * c₁) := by rw [← hyc₁]
      _ = c₁ := by group
  have hyw : y⁻¹ * w₀ * y = w₀ := by
    calc y⁻¹ * w₀ * y = y⁻¹ * (w₀ * y) := by group
      _ = y⁻¹ * (y * w₀) := by rw [← hyw₀]
      _ = w₀ := by group
  let k₂ : G := y⁻¹ * k * y
  have hk₂S : k₂ ∈ S := by
    have := hyS k (Subgroup.mem_sup_left hkR)
    simpa [k₂] using this
  have hk₂T : k₂ ∈ T := by
    rw [hT]
    refine Subgroup.mem_inf.mpr ⟨hk₂S, ?_⟩
    have hcomm := ((commute_iff_eq k c₁).2 hkc).conj y⁻¹
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      simpa [k₂, hyc] using hcomm.eq)
  have hk₂2 : k₂ * k₂ = 1 := by
    calc (y⁻¹ * k * y) * (y⁻¹ * k * y) = y⁻¹ * (k * k) * y := by group
      _ = 1 := by rw [hk2]; group
  have hk₂1 : k₂ ≠ 1 := by
    intro h
    apply hk1
    have h' : y⁻¹ * k * y = 1 := by simpa [k₂] using h
    calc k = y * (y⁻¹ * k * y) * y⁻¹ := by group
      _ = 1 := by rw [h']; group
  have hk₂c₁ : k₂ ≠ c₁ := by
    intro h
    apply hkc₁
    have h' : y⁻¹ * k * y = c₁ := by simpa [k₂] using h
    calc k = y * (y⁻¹ * k * y) * y⁻¹ := by group
      _ = y * c₁ * y⁻¹ := by rw [h']
      _ = c₁ := by rw [hyc₁]; group
  have hk₂conj : IsConj k₂ c₁ := by
    have h : IsConj k k₂ := by
      refine isConj_iff.2 ⟨y⁻¹, ?_⟩
      simp [k₂]
    exact h.symm.trans hk
  have hc₁k₂ : IsConj (c₁ * k₂) c₁ := by
    have h : IsConj (c₁ * k) (c₁ * k₂) := by
      refine isConj_iff.2 ⟨y⁻¹, ?_⟩
      calc y⁻¹ * (c₁ * k) * (y⁻¹)⁻¹ = (y⁻¹ * c₁ * y) * (y⁻¹ * k * y) := by
            rw [inv_inv]
            group
        _ = c₁ * k₂ := by rw [hyc]
    exact h.symm.trans hc₁k
  have hk₂Du : k₂ ∉ Du := by
    intro hk₂Du
    exact hDu k₂ hk₂Du hk₂2 hk₂1 hk₂c₁ hk₂conj hc₁k₂
  have hRy_le : R.map (MulAut.conj y⁻¹).toMonoidHom ≤
      (T ⊓ Subgroup.centralizer ({k₂} : Set G) : Subgroup G) := by
    rintro _ ⟨r, hr, rfl⟩
    have hr' : r ∈ T ⊓ Subgroup.centralizer {k} := hR ▸ hr
    have hrT : r ∈ T := (Subgroup.mem_inf.1 hr').1
    have hrC : r * c₁ = c₁ * r :=
      Subgroup.mem_centralizer_singleton_iff.1 (hTC hrT)
    have hrk : r * k = k * r :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hr').2
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hT]
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have := hyS r (Subgroup.mem_sup_left hr)
        simpa [MulAut.conj_apply] using this
      · have hcomm := ((commute_iff_eq r c₁).2 hrC).conj y⁻¹
        exact Subgroup.mem_centralizer_singleton_iff.mpr (by
          simpa [MulAut.conj_apply, hyc] using hcomm.eq)
    · have hcomm := ((commute_iff_eq r k).2 hrk).conj y⁻¹
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        simpa [MulAut.conj_apply, k₂] using hcomm.eq)
  have hRy_card : Nat.card (R.map (MulAut.conj y⁻¹).toMonoidHom) = Nat.card R :=
    Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective
  have hK₂card_le : Nat.card (T ⊓ Subgroup.centralizer ({k₂} : Set G) : Subgroup G) ≤
      Nat.card R := by
    have h := hT4 k₂ hk₂T hk₂Du hk₂2
    rw [hR] at h
    exact h
  have hRy_eq : R.map (MulAut.conj y⁻¹).toMonoidHom =
      (T ⊓ Subgroup.centralizer ({k₂} : Set G) : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hRy_le (by rw [hRy_card]; exact hK₂card_le)
  have hk₂Dk : k₂ ∈ Dk := by
    by_contra hk₂Dk
    have hlt : Nat.card (T ⊓ Subgroup.centralizer ({k₂} : Set G) : Subgroup G) <
        Nat.card R := by
      have h := hDk k₂ hk₂T hk₂Du hk₂2 hk₂Dk
      rw [hR] at h
      exact h
    have heq : Nat.card (T ⊓ Subgroup.centralizer ({k₂} : Set G) : Subgroup G) =
        Nat.card R := by
      rw [← hRy_eq, hRy_card]
    omega
  have hxS : y⁻¹ * n * y ∈ S := hyS n (Subgroup.mem_sup_right (Subgroup.mem_zpowers n))
  have hnk_comm : n * k = k * n := by
    calc n * k = n * (n⁻¹ * k * n) := by rw [hnk]
      _ = k * n := by group
  have hxk₂ : (y⁻¹ * n * y) * k₂ = k₂ * (y⁻¹ * n * y) := by
    have hcomm := ((commute_iff_eq n k).2 hnk_comm).conj y⁻¹
    simpa [k₂, MulAut.conj_apply] using hcomm.eq
  have hxc₁ : (y⁻¹ * n * y) * c₁ = c₁ * (y⁻¹ * n * y) :=
    hT78 k₂ hk₂Dk hk₂Du hk₂2 (y⁻¹ * n * y) hxS hxk₂
  have hxconj1 : (y⁻¹ * n * y)⁻¹ * c₁ * (y⁻¹ * n * y) = c₁ := by
    calc (y⁻¹ * n * y)⁻¹ * c₁ * (y⁻¹ * n * y) =
        (y⁻¹ * n * y)⁻¹ * (c₁ * (y⁻¹ * n * y)) := by group
      _ = (y⁻¹ * n * y)⁻¹ * ((y⁻¹ * n * y) * c₁) := by rw [← hxc₁]
      _ = c₁ := by group
  have hyc' : y * c₁ * y⁻¹ = c₁ := by
    calc y * c₁ * y⁻¹ = y * (y⁻¹ * c₁ * y) * y⁻¹ := by rw [hyc]
      _ = c₁ := by group
  have hxconj : (y⁻¹ * n * y)⁻¹ * c₁ * (y⁻¹ * n * y) = c₁ * w₀ := by
    calc (y⁻¹ * n * y)⁻¹ * c₁ * (y⁻¹ * n * y) =
        y⁻¹ * n⁻¹ * (y * c₁ * y⁻¹) * n * y := by group
      _ = y⁻¹ * n⁻¹ * c₁ * n * y := by rw [hyc']
      _ = y⁻¹ * (n⁻¹ * c₁ * n) * y := by group
      _ = y⁻¹ * (c₁ * w₀) * y := by rw [hnc₁']
      _ = (y⁻¹ * c₁ * y) * (y⁻¹ * w₀ * y) := by group
      _ = c₁ * w₀ := by rw [hyc, hyw]
  have h1 : c₁ = c₁ * w₀ := hxconj1.symm.trans hxconj
  have h2 : c₁ * 1 = c₁ * w₀ := by simpa using h1
  exact hw₀1 (mul_left_cancel h2).symm

end Stroth47Inv1

end CFSG.CGT.Stroth77
