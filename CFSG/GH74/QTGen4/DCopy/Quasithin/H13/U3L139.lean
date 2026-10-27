module

public import CFSG.Quasithin.H13.U3L139
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L13x7

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6
open scoped commutatorElement

@[expose] def Stmt13_2_2_9L1_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → IsA6On L V → IsHatA6 L →
      normalizer (L₁Of L (fsuV1 T V) : Set G) ≤ normalizer (L : Set G)

variable {G : Type} [Group G]

theorem stmt13_3_9_core_F4 [CFSG.GH74.QTGen4.Finite4 G] (h1332 : Stmt13_3_2_F4) (h1226 : Stmt12_2_6_F4)
    (h1228 : Stmt12_2_8_F4) (h1338 : A6.Stmt13_3_8_F4) (hL1 : Stmt13_2_2_9L1_F4)
    {T L V H Y : Subgroup G} {v : G} (hH : QTH13 G T L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) (hA6 : IsA6On L V) (hHin : InH T H)
    (hHM : ¬ H ≤ normalizer (L : Set G)) (hY2 : oTwoRes Y = Y) (hYH : Y ≤ H)
    (hHY : H ≤ normalizer (Y : Set G)) (hv : v ∈ fsuV1 T V) (hvL : v ∉ centralizer (L : Set G))
    (hYv : Y ≤ normalizer (L : Set G) ⊓ centralizer ({v} : Set G)) (F : Frame139 T L V)
    (hYV1' : ∀ y ∈ Y, y ∈ normalizer (V : Set G) → y ∈ normalizer (fsuV1 T V : Set G)) :
    Y = ⊥ ∨
      (autOn Y V = autOn (L₁Of L (fsuV1 T V)) V ∧
        (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) →
          Y = L₁Of L (fsuV1 T V)) ∧
        (IsHatA6 L → Y = l1plus T L V) ∧ IsPGroup 2 ↥(Y ⊓ centralizer (V : Set G))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁def
  set Y₁ := orderThreeSubgroup Y with hY₁def

  obtain ⟨h5, ⟨hTL, -, hMmax, huniq⟩, ⟨-, hall⟩, -⟩ := h1332 G T L hH L hH.faithful
  have hU : IsUniqueM (L ⊔ T) (normalizer (L : Set G)) :=
    ⟨⟨hMmax, sup_le le_normalizer hTL⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
  obtain ⟨hVT, -, -, -⟩ := hall V hV
  have hLV : L ≤ normalizer (V : Set G) := hV.2.2.1
  have hVf := fun w (hw : w ∈ V) => mem_reducedAggregate' (hV.1 hw)
  have hO : pCoreOf 2 L ≤ centralizer (V : Set G) := by
    refine (pCoreOf_le_pCoreOf_sup hTL).trans ?_
    intro k hk
    exact mem_centralizer_iff.2 fun w hw => ((hVf w hw).2.1 k hk).symm
  have hyp := hyp1223_of_F4 h1332 hH hV
  have hcharL : CharTwo L := A5.charTwo_of_faithful hH.qtke.2.1 hH.sylow hH.faithful
  have hOT : pCoreOf 2 L ≤ T := (pCoreOf_le_pCoreOf_sup hTL).trans
    (F7.isSylowTwoOf_pCoreOf_le (A5.isSylowTwoOf_of_le hH.sylow le_sup_right))
  have hsyl : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A5.isSylowTwoOf_of_le hH.sylow le_sup_right) le_sup_left
      (sup_le le_normalizer hTL)
  have hL1L : L₁ ≤ L := (oTwoRes_le _).trans inf_le_left
  have hL1N : L₁ ≤ normalizer (V : Set G) := hL1L.trans hLV
  have hTV1 : T ≤ normalizer (fsuV1 T V : Set G) := T_le_normalizer_fsuV1 T V
  have hTL1 : T ≤ normalizer (L₁ : Set G) := A5.le_normalizer_oTwoRes_of_le_normalizer
    (fun t ht => inf_normalizer_le_normalizer_inf ⟨hTL ht, le_normalizer (hTV1 ht)⟩)
  have hO1T : pCoreOf 2 L₁ ≤ T := (pCoreOf_le_pCoreOf_sup hTL1).trans
    (F7.isSylowTwoOf_pCoreOf_le (A5.isSylowTwoOf_of_le hH.sylow le_sup_right))

  have hv1 : v ≠ 1 := fun h => hvL (h ▸ one_mem _)
  have hYN : Y ≤ normalizer (V : Set G) := by
    have hYz : Y ≤ normalizer ((zpowers v : Subgroup G) : Set G) := fun y hy =>
      (centralizer_le_normalizer (zpowers v)) (by
        rw [zpowers_eq_closure, centralizer_closure]
        exact (hYv hy).2)
    have h := (h1226 G T L V hyp).2 (zpowers v) Y (fun h => hv1 (by
      have := mem_zpowers v
      rwa [h, mem_bot] at this)) (zpowers_le.2 hv.1) hYz
    intro y hy
    have h1 : y ∈ Y ⊓ normalizer (L : Set G) := ⟨hy, (hYv hy).1⟩
    rw [h] at h1
    exact h1.2
  have hYV1 : Y ≤ normalizer (fsuV1 T V : Set G) := fun y hy => hYV1' y hy (hYN hy)

  have hY23 : IsTwoThreeGroup Y := (h1338 G T L L H Y hH hH.faithful hHin hHM hY2 hYH hHY
    fun y hy => (hYv hy).1).2

  have h3L : ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L := by
    intro x hx hx3
    rcases h1228 G T L V hyp with h | h | ⟨-, h⟩
    · rw [← h]
      exact subset_closure ⟨hx, 1, by rw [pow_one, ← hx3, pow_orderOf_eq_one]⟩
    · exfalso
      have hcase := a6_or_hatA6_of_isA6On hLV hO h5 hA6
      have hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 ∨
          Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1080 := by
        rcases hcase with he | ⟨-, hz, ⟨e⟩⟩
        · left
          obtain ⟨e⟩ := he
          rw [Nat.card_congr e.toEquiv, card_alt6]
        · right
          have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
            (center (↥L ⧸ CFSG.pCore 2 ↥L))
          rw [Nat.card_congr e.toEquiv, card_alt6, hz] at h1
          rw [h1]
      rcases h with he5 | h32
      · obtain ⟨e5⟩ := he5
        have := Nat.card_congr e5.toEquiv
        rw [card_alt5] at this
        omega
      · obtain ⟨e3⟩ := nonempty_equiv_SL32_of_lieModel h32
        have := Nat.card_congr e3.toEquiv
        rw [HSType.card_SL_three_two] at this
        omega
    · rw [h]
      exact subset_closure ⟨hx, hx3⟩

  have hNY1 : normalizer (Y : Set G) ≤ normalizer (Y₁ : Set G) :=
    le_normalizer_orderThreeSubgroup Y
  have hTY : T ≤ normalizer (Y : Set G) := hHin.1.trans hHY
  have hTY1 : T ≤ normalizer (Y₁ : Set G) := hTY.trans hNY1
  have hY1Y : Y₁ ≤ Y := orderThreeSubgroup_le Y
  have hY1N : Y₁ ≤ normalizer (V : Set G) := hY1Y.trans hYN

  have hY1L1 : Y₁ ≤ L₁ := (closure_le _).2 fun y hy =>
    subset_closure ⟨⟨h3L y (hYv hy.1).1 hy.2, hYV1 hy.1⟩, 3, by decide, by
      rw [← hy.2, pow_orderOf_eq_one]⟩

  have hY1bot : Y₁ = ⊥ → Y = ⊥ := by
    intro h
    have hY2g : IsPGroup 2 Y := isPGroup_two_of_no_three hY23 fun x hx hx3 => by
      have := mem_orderThreeSubgroup hx hx3
      rw [← hY₁def, h, mem_bot] at this
      rw [this, orderOf_one] at hx3
      exact absurd hx3 (by decide)
    rw [← hY2]
    refine eq_bot_iff.2 ((closure_le _).2 fun y hy => ?_)
    obtain ⟨hyY, m, hm, hym⟩ := hy
    obtain ⟨k, hk⟩ := hY2g ⟨y, hyY⟩
    have h1 : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 := (pow_gcd_eq_one (a := y)).2 ⟨hym, h1⟩
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hm)),
      pow_one] at h2
    exact h2

  have hTLY1 : T ⊓ L ≤ normalizer (Y₁ : Set G) := inf_le_left.trans hTY1
  obtain ⟨hY1A4, hY1dich⟩ := F.dichotomy hsyl hY1N (hY1Y.trans hYV1)
    (orderThreeSubgroup_le_oTwoRes Y) hTLY1
  obtain ⟨hYA4, -⟩ := F.dichotomy hsyl hYN hYV1 (le_of_eq hY2.symm)
    (inf_le_left.trans hTY)
  have hL1A4 : ∀ x (hx : x ∈ normalizer (V : Set G)), x ∈ L₁ → InA4 (F.ρ ⟨x, hx⟩) := by
    intro x hx hxL1
    obtain ⟨hA, -⟩ := F.dichotomy hsyl (X := L₁) hL1N
      ((oTwoRes_le _).trans inf_le_right) (oTwoRes_le_oTwoRes _)
      (inf_le_left.trans hTL1)
    exact hA x hx hxL1

  have hY1nY : Y ≤ normalizer (Y₁ : Set G) := le_normalizer.trans hNY1
  by_cases hY1 : Y₁ = ⊥
  · exact Or.inl (hY1bot hY1)
  right
  have hcase := a6_or_hatA6_of_isA6On hLV hO h5 hA6
  have h1337 := stmt13_3_7_of_F4 h1332 h1228 G T L V hH hV hA6
  have hCL : L ⊓ centralizer (V : Set G) ≤ o2Z L :=
    centralizer_le_o2Z_of_isA6On hLV hO hyp.quasisimple hA6

  have hP1 : L₁ ⊓ pCoreOf 2 L ≤ pCoreOf 2 L₁ :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun x hx => inf_normalizer_le_normalizer_inf ⟨le_normalizer hx,
        LieType.BorelTits.le_normalizer_pCoreOf 2 L (hL1L hx)⟩)
      ((LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_right)

  have hex : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) → ¬ IsHatA6 L := by
    rintro ⟨e⟩ ⟨-, hz, ⟨e'⟩⟩
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center (↥L ⧸ CFSG.pCore 2 ↥L))
    rw [Nat.card_congr e.toEquiv, card_alt6, hz, Nat.card_congr e'.toEquiv, card_alt6] at h1
    omega

  have hYsup : (∀ σ, InA4 σ → ∃ x : G, ∃ hx : x ∈ normalizer (V : Set G), x ∈ Y₁ ∧
      F.ρ ⟨x, hx⟩ = σ) → Y ≤ Y₁ ⊔ (Y ⊓ centralizer (V : Set G)) := by
    intro himg y hy
    obtain ⟨x, hxN, hxY1, hx⟩ := himg _ (hYA4 y (hYN hy) hy)
    have hc := F.inv_mul_mem (hYN hy) hxN hx
    rw [show y = x * (x⁻¹ * y) by group]
    exact mul_mem (mem_sup_left hxY1)
      (mem_sup_right (mem_inf.2 ⟨mul_mem (inv_mem (hY1Y hxY1)) hy, hc⟩))
  rcases hcase with he | hhat
  ·
    have hC3 : ¬ 3 ∣ Nat.card (centralizer (V : Set G)) :=
      h1337.resolve_right fun h => hex he h.1
    have hY1C : ¬ Y₁ ≤ centralizer (V : Set G) := by
      intro hle
      apply hY1
      refine eq_bot_iff.2 ((closure_le _).2 fun y hy => ?_)
      exfalso
      apply hC3
      have := Subgroup.orderOf_dvd_natCard (centralizer (V : Set G))
        (hle (mem_orderThreeSubgroup hy.1 hy.2))
      rwa [hy.2] at this
    have himg := hY1dich.resolve_left hY1C

    have hL1le : L₁ ≤ Y₁ ⊔ pCoreOf 2 L₁ := by
      intro l hl
      obtain ⟨x, hxN, hxY1, hx⟩ := himg _ (hL1A4 l (hL1N hl) hl)
      have hc := F.inv_mul_mem (hL1N hl) hxN hx
      have hcL1 : x⁻¹ * l ∈ L₁ := mul_mem (inv_mem (hY1L1 hxY1)) hl
      have hcO : x⁻¹ * l ∈ pCoreOf 2 L :=
        o2Z_le_pCoreOf_of_a6 he (hCL ⟨hL1L hcL1, hc⟩)
      rw [show l = x * (x⁻¹ * l) by group]
      exact mul_mem (mem_sup_left hxY1) (mem_sup_right (hP1 ⟨hcL1, hcO⟩))
    have hL1Y1 : L₁ ≤ Y₁ :=
      (oTwoRes_le_oTwoRes _).trans (oTwoRes_le_of_le_sup hL1le
        (LieType.BorelTits.pCoreOf_isPGroup 2 _) (hO1T.trans hTY1))
    have hY1eq : Y₁ = L₁ := le_antisymm hY1L1 hL1Y1

    have hYC23 : A6.IsTwoThreeGroup (Y ⊓ centralizer (V : Set G)) := fun p hp hpd =>
      hY23 p hp (hpd.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hYC2 : IsPGroup 2 ↥(Y ⊓ centralizer (V : Set G)) := by
      refine isPGroup_two_of_no_three hYC23 fun x hx hx3 => hC3 ?_
      have := Subgroup.orderOf_dvd_natCard (centralizer (V : Set G)) hx.2
      rwa [hx3] at this
    have hYL1 : Y ≤ L₁ := calc
      Y = oTwoRes Y := hY2.symm
      _ ≤ Y₁ := oTwoRes_le_of_le_sup (hYsup himg) hYC2 (inf_le_left.trans hY1nY)
      _ = L₁ := hY1eq
    have hYeq : Y = L₁ := le_antisymm hYL1 (hY1eq ▸ hY1Y)
    exact ⟨by rw [hYeq], fun _ => hYeq, fun h => absurd h (hex he), hYC2⟩
  ·
    have hne : ¬ Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) :=
      fun he => hex he hhat

    have h3L0 : ∀ y ∈ centralizer (V : Set G), orderOf y = 3 → y ∈ l0 L := by
      intro y hy hy3
      rcases h1337 with h | ⟨-, -, h0⟩
      · exfalso
        apply h
        have := Subgroup.orderOf_dvd_natCard (centralizer (V : Set G)) hy
        rwa [hy3] at this
      · rw [h0]
        exact mem_orderThreeSubgroup hy hy3
    have hO0T : pCoreOf 2 (l0 L) ≤ T := pCoreOf_l0_le.trans hOT
    have hNL0 := normalizer_l0_le hhat hcharL hTL hU

    have hY1C : ¬ Y₁ ≤ centralizer (V : Set G) := by
      intro hle
      obtain ⟨y, hyY, hy3⟩ : ∃ y ∈ Y, orderOf y = 3 := by
        by_contra hno
        push Not at hno
        exact hY1 (eq_bot_iff.2 ((closure_le _).2 fun y hy => absurd hy.2 (hno y hy.1)))
      have hyY1 := mem_orderThreeSubgroup hyY hy3
      have hL0Y1 : l0 L ≤ Y₁ :=
        l0_le_of_mem hhat (hO0T.trans hTY1) hyY1 (h3L0 y (hle hyY1) hy3) hy3
      have hY1L0 : Y₁ ≤ l0 L := (closure_le _).2 fun x hx =>
        h3L0 x (hle (mem_orderThreeSubgroup hx.1 hx.2)) hx.2
      have hY1eq : Y₁ = l0 L := le_antisymm hY1L0 hL0Y1
      exact hHM ((hHY.trans hNY1).trans (hY1eq ▸ hNL0))
    have himg := hY1dich.resolve_left hY1C

    have hZ0 : o2Z L ≤ l0 L ⊔ pCoreOf 2 L := by
      intro x hx
      obtain ⟨c, hc, -, -, hdec⟩ := exists_l0_c hhat.2.1
      rcases hdec x hx with h | h | h
      · exact mem_sup_right h
      · rw [show x = (c * c)⁻¹ * (c * c * x) by group]
        exact mul_mem (inv_mem (mem_sup_left (mul_mem hc hc))) (mem_sup_right h)
      · rw [show x = c⁻¹ * (c * x) by group]
        exact mul_mem (inv_mem (mem_sup_left hc)) (mem_sup_right h)
    have hL0N : l0 L ≤ normalizer (pCoreOf 2 L : Set G) :=
      l0_le_L.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 L)

    have hZC : o2Z L ≤ centralizer (V : Set G) := by
      intro z hz
      have hzL : z ∈ L := o2Z_le_L hz
      have hzN := hLV hzL
      refine (F.rho_eq_one_iff hzN).1 ?_
      obtain ⟨hA012, hA234, hcen⟩ := c012_c234
      obtain ⟨g₁, hg₁L, hg₁⟩ := (F.image_L c012).2 hA012
      obtain ⟨g₂, hg₂L, hg₂⟩ := (F.image_L c234).2 hA234
      have hcomm : ∀ g : ↥(normalizer (V : Set G)), (g : G) ∈ L →
          F.ρ ⟨z, hzN⟩ * F.ρ g = F.ρ g * F.ρ ⟨z, hzN⟩ := by
        intro g hg
        have h1 := (mem_o2Z_iff.1 hz).2 g hg
        have h2 : F.ρ ⟨z * g * z⁻¹ * g⁻¹, mul_mem (mul_mem (mul_mem hzN g.2) (inv_mem hzN))
            (inv_mem g.2)⟩ = 1 :=
          (F.rho_eq_one_iff _).2 (hO h1)
        have e : (⟨z * g * z⁻¹ * g⁻¹, mul_mem (mul_mem (mul_mem hzN g.2) (inv_mem hzN))
            (inv_mem g.2)⟩ : ↥(normalizer (V : Set G))) = ⟨z, hzN⟩ * g * ⟨z, hzN⟩⁻¹ * g⁻¹ := rfl
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
        calc F.ρ ⟨z, hzN⟩ * F.ρ g = (F.ρ ⟨z, hzN⟩ * F.ρ g * (F.ρ ⟨z, hzN⟩)⁻¹ * (F.ρ g)⁻¹) *
              (F.ρ g * F.ρ ⟨z, hzN⟩) := by group
          _ = F.ρ g * F.ρ ⟨z, hzN⟩ := by rw [h2, one_mul]
      exact hcen _ (hg₁ ▸ hcomm g₁ hg₁L) (hg₂ ▸ hcomm g₂ hg₂L)
    have hL0L1 : l0 L ≤ L₁ := A6.oTwoRes_mono fun z hz =>
      ⟨o2Z_le_L hz, (centralizer_le_normalizer (fsuV1 T V : Subgroup G))
        (centralizer_le (inf_le_left : fsuV1 T V ≤ V) (hZC hz))⟩

    have hdecomp : ∀ l ∈ L₁, ∃ y ∈ Y₁, ∃ l₀ ∈ l0 L, ∃ o ∈ L₁ ⊓ pCoreOf 2 L, l = y * l₀ * o := by
      intro l hl
      obtain ⟨x, hxN, hxY1, hx⟩ := himg _ (hL1A4 l (hL1N hl) hl)
      have hc := F.inv_mul_mem (hL1N hl) hxN hx
      have hcL1 : x⁻¹ * l ∈ L₁ := mul_mem (inv_mem (hY1L1 hxY1)) hl
      have hcZ : x⁻¹ * l ∈ l0 L ⊔ pCoreOf 2 L := hZ0 (hCL ⟨hL1L hcL1, hc⟩)
      rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hL0N] at hcZ
      obtain ⟨l₀, hl₀, o, ho, hlo⟩ := Set.mem_mul.1 hcZ
      have hoL1 : o ∈ L₁ := by
        have : o = l₀⁻¹ * (x⁻¹ * l) := by rw [← hlo]; group
        rw [this]
        exact mul_mem (inv_mem (hL0L1 hl₀)) hcL1
      refine ⟨x, hxY1, l₀, hl₀, o, mem_inf.2 ⟨hoL1, ho⟩, ?_⟩
      rw [mul_assoc x, hlo]
      group

    have h3 : ∀ y ∈ Y₁, y ∈ centralizer (V : Set G) → orderOf y ≠ 3 := by
      intro y hyY1 hyC hy3
      have hL0Y1 : l0 L ≤ Y₁ := l0_le_of_mem hhat (hO0T.trans hTY1) hyY1 (h3L0 y hyC hy3) hy3
      have hL1le : L₁ ≤ Y₁ ⊔ pCoreOf 2 L₁ := by
        intro l hl
        obtain ⟨x, hx, l₀, hl₀, o, ho, rfl⟩ := hdecomp l hl
        exact mul_mem (mul_mem (mem_sup_left hx) (mem_sup_left (hL0Y1 hl₀)))
          (mem_sup_right (hP1 ho))
      have hL1Y1 : L₁ ≤ Y₁ :=
        (oTwoRes_le_oTwoRes _).trans (oTwoRes_le_of_le_sup hL1le
          (LieType.BorelTits.pCoreOf_isPGroup 2 _) (hO1T.trans hTY1))
      have hY1eq : Y₁ = L₁ := le_antisymm hY1L1 hL1Y1
      exact hHM ((hHY.trans hNY1).trans (hY1eq ▸ hL1 G T L V hH hV hA6 hhat))

    have hYC23 : A6.IsTwoThreeGroup (Y ⊓ centralizer (V : Set G)) := fun p hp hpd =>
      hY23 p hp (hpd.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hYC2 : IsPGroup 2 ↥(Y ⊓ centralizer (V : Set G)) :=
      isPGroup_two_of_no_three hYC23 fun x hx hx3 =>
        h3 x (mem_orderThreeSubgroup hx.1 hx3) hx.2 hx3
    have hYY1 : Y ≤ Y₁ := calc
      Y = oTwoRes Y := hY2.symm
      _ ≤ Y₁ := oTwoRes_le_of_le_sup (hYsup himg) hYC2 (inf_le_left.trans hY1nY)
    have hYeq1 : Y = Y₁ := le_antisymm hYY1 hY1Y
    have hYL1 : Y ≤ L₁ := hYY1.trans hY1L1

    set P := L₁ ⊓ pCoreOf 2 L with hPdef
    have hP2 : IsPGroup 2 P := (LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_right
    have hPT : P ≤ T := inf_le_right.trans hOT
    have hTP : T ≤ normalizer (P : Set G) := fun t ht =>
      inf_normalizer_le_normalizer_inf ⟨hTL1 ht,
        LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (hTL ht)⟩

    have hLp : l1plus T L V ≤ Y := by
      have hcomm : ⁅L₁, T ⊓ L⁆ ≤ Y ⊔ P := by
        rw [commutator_le]
        intro l hl t ht
        obtain ⟨y, hy, l₀, hl₀, o, ho, rfl⟩ := hdecomp l hl
        have hyY : y ∈ Y := hY1Y hy
        have hl₀P : l₀ * o * l₀⁻¹ ∈ P :=
          (mem_normalizer_iff.1 (inf_normalizer_le_normalizer_inf
            ⟨le_normalizer (hL0L1 hl₀), hL0N hl₀⟩) o).1 ho
        set k := y * (l₀ * o * l₀⁻¹) with hk
        have hkYP : k ∈ Y ⊔ P := mul_mem (mem_sup_left hyY) (mem_sup_right hl₀P)
        have htYP : (t : G) ∈ normalizer ((Y ⊔ P : Subgroup G) : Set G) :=
          C1.mem_normalizer_sup (hTY ht.1) (hTP ht.1)
        have hk' : t * k⁻¹ * t⁻¹ ∈ Y ⊔ P := (mem_normalizer_iff.1 htYP _).1 (inv_mem hkYP)
        have hl₀t : l₀ * t * l₀⁻¹ * t⁻¹ ∈ P := by
          have h1 : t * l₀⁻¹ * t⁻¹ ∈ l0 L :=
            (mem_normalizer_iff.1 (L_le_normalizer_l0 ht.2) _).1 (inv_mem hl₀)
          have e : l₀ * t * l₀⁻¹ * t⁻¹ = l₀ * (t * l₀⁻¹ * t⁻¹) := by group
          refine mem_inf.2 ⟨?_, (mem_o2Z_iff.1 (oTwoRes_le _ hl₀)).2 t ht.2⟩
          rw [e]
          exact hL0L1 (mul_mem hl₀ h1)
        have e : ⁅y * l₀ * o, t⁆ = k * (l₀ * t * l₀⁻¹ * t⁻¹) * (t * k⁻¹ * t⁻¹) := by
          rw [commutatorElement_def, hk]
          group
        rw [e]
        exact mul_mem (mul_mem hkYP (mem_sup_right hl₀t)) hk'
      exact oTwoRes_le_of_le_sup hcomm hP2 (hPT.trans hTY)

    have hYLp : Y ≤ l1plus T L V := by
      set K := ⁅Y, T ⊓ L⁆ with hKdef
      have hKY : K ≤ Y := commutator_le_left_of_le_normalizer (inf_le_left.trans hTY)
      have hKN : K ≤ normalizer (V : Set G) := hKY.trans hYN
      have hTK : T ⊓ L ≤ normalizer (K : Set G) :=
        CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer _ _ _
          (inf_le_left.trans hTY) le_normalizer
      have hKA4 : ∀ x (hx : x ∈ normalizer (V : Set G)), x ∈ K → InA4 (F.ρ ⟨x, hx⟩) :=
        fun x hx hxK => hYA4 x hx (hKY hxK)

      obtain ⟨hcA4, hc3, hc1, h012⟩ := comm_c012_d1
      obtain ⟨y, hyN, hyY1, hy⟩ := himg c012 h012
      obtain ⟨t, htTL, ht⟩ := F.exists_TL hsyl d1_mem.1 d1_mem.2
      have hyY : y ∈ Y := hY1Y hyY1
      have hk : ⁅y, (t : G)⁆ ∈ K := commutator_mem_commutator hyY htTL
      have hkρ : F.ρ ⟨⁅y, (t : G)⁆, hKN hk⟩ = c012 * d1 * c012⁻¹ * d1⁻¹ := by
        have e : (⟨⁅y, (t : G)⁆, hKN hk⟩ : ↥(normalizer (V : Set G))) =
            ⟨y, hyN⟩ * t * ⟨y, hyN⟩⁻¹ * t⁻¹ := by
          apply Subtype.ext
          simp [commutatorElement_def]
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hy, ht]
      have hKimg := F.surj_of_three hsyl hKN hTK hKA4 hk (by rw [hkρ]; exact hc3)
        (by rw [hkρ]; exact hc1)

      have hYK : Y ≤ K ⊔ (Y ⊓ centralizer (V : Set G)) := by
        intro y' hy'
        obtain ⟨x, hxN, hxK, hx⟩ := hKimg _ (hYA4 y' (hYN hy') hy')
        have hc := F.inv_mul_mem (hYN hy') hxN hx
        rw [show y' = x * (x⁻¹ * y') by group]
        exact mul_mem (mem_sup_left hxK)
          (mem_sup_right (mem_inf.2 ⟨mul_mem (inv_mem (hKY hxK)) hy', hc⟩))
      have hYK' : Y ≤ K := calc
        Y = oTwoRes Y := hY2.symm
        _ ≤ K := oTwoRes_le_of_le_sup hYK hYC2
          (inf_le_left.trans (le_normalizer_commutator_left' Y (T ⊓ L)))
      calc Y = oTwoRes Y := hY2.symm
        _ ≤ oTwoRes ⁅L₁, T ⊓ L⁆ := A6.oTwoRes_mono (hYK'.trans (commutator_mono hYL1 le_rfl))
    have hAut : autOn L₁ V ≤ autOn Y V := autOn_le_of_forall fun l hl hlN => by
      obtain ⟨x, hxN, hxY1, hx⟩ := himg _ (hL1A4 l hlN hl)
      exact ⟨x, hYeq1 ▸ hxY1, hxN, F.inv_mul_mem hlN hxN hx⟩
    exact ⟨le_antisymm (autOn_le_autOn V hYL1) hAut, fun he => absurd he hne,
      fun _ => le_antisymm hYLp hLp, hYC2⟩

end CFSG.Quasithin.H13.U3
