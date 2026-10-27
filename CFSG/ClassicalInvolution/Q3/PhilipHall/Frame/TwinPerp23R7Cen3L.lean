module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Y9
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfMembers
import CFSG.ClassicalInvolution.AschTight.Sec7L714F

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

@[expose] def E64CenComm : Prop :=
  ∀ α₁ ∈ AE.e64Sets, ∀ α₂ ∈ AE.e64Sets, ∀ α₃ ∈ AE.e64Sets, ∀ (h₁ : α₁.card = 4) (h₂ : α₂.card = 4)
    (h₃ : α₃.card = 4) (b₁ b₂ b₃ : Bool),
    ∀ a ∈ AE.memBar α₁ h₁ b₁ ⊔ AE.memBar α₂ h₂ b₂ ⊔ AE.memBar α₃ h₃ b₃,
      (∀ y ∈ AE.memBar α₁ h₁ b₁, a * y = y * a) → (∀ y ∈ AE.memBar α₂ h₂ b₂, a * y = y * a) →
      (∀ y ∈ AE.memBar α₃ h₃ b₃, a * y = y * a) →
        a ∈ ⁅AE.memBar α₁ h₁ b₁ ⊔ AE.memBar α₂ h₂ b₂ ⊔ AE.memBar α₃ h₃ b₃,
          AE.memBar α₁ h₁ b₁ ⊔ AE.memBar α₂ h₂ b₂ ⊔ AE.memBar α₃ h₃ b₃⁆

namespace F7Z

section Gen

variable {G : Type} [Group G]

theorem mul_pow_orderOf {a b : G} (hab : a * b = b * a) (ha : a * a = 1) (hb : Odd (orderOf b)) :
    (a * b) ^ orderOf b = a := by
  rw [(Commute.mul_pow hab) (orderOf b), pow_orderOf_eq_one, mul_one]
  obtain ⟨k, hk⟩ := hb
  rw [hk, pow_succ, pow_mul, pow_two, ha, one_pow, one_mul]

theorem centMod_conj {J : Subgroup G} {a : G} (h : CentMod J a) (x : G) :
    CentMod (conjSub x J) (x * a * x⁻¹) := by
  intro b hb
  rw [mem_conjSub_iff] at hb
  rw [Asc77.Thompson.oddCoreOf_conjSub_eq, mem_conjSub_iff]
  have h1 := h _ hb
  have e : x⁻¹ * (x * a * x⁻¹ * b * (x * a * x⁻¹)⁻¹ * b⁻¹) * x =
      a * (x⁻¹ * b * x) * a⁻¹ * (x⁻¹ * b * x)⁻¹ := by group
  rw [e]
  exact h1

variable [Finite G]

theorem mem_of_mem_sup_odd {E H : Subgroup G} {e : G} (hHE : H ≤ E)
    (hEe : E ≤ Subgroup.centralizer ({e} : Set G)) (he2 : e * e = 1) (he : e ∈ oddCoreOf E ⊔ H) :
    e ∈ H := by
  rw [sup_comm] at he
  have hHN : H ≤ Subgroup.normalizer ((oddCoreOf E : Subgroup G) : Set G) :=
    hHE.trans (Sec7.le_normalizer_oddCoreOf E)
  have he' : e ∈ ((H ⊔ oddCoreOf E : Subgroup G) : Set G) := he
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHN] at he'
  obtain ⟨h, hh, o, ho, hho⟩ := he'
  have hoe : o * e = e * o :=
    Subgroup.mem_centralizer_singleton_iff.mp (hEe (oddCoreOf_le_self E ho))
  have hh' : h = e * o⁻¹ := by rw [← hho]; group
  have hcomm : e * o⁻¹ = o⁻¹ * e := by
    calc e * o⁻¹ = o⁻¹ * (o * e) * o⁻¹ := by group
      _ = o⁻¹ * (e * o) * o⁻¹ := by rw [hoe]
      _ = o⁻¹ * e := by group
  have hodd : Odd (orderOf o⁻¹) := by
    rw [orderOf_inv]
    exact Odd.of_dvd_nat (odd_natCard_oddCoreOf E) (Subgroup.orderOf_dvd_natCard _ ho)
  have h1 := mul_pow_orderOf hcomm he2 hodd
  rw [← hh'] at h1
  rw [← h1]
  exact H.pow_mem hh _

end Gen

section Ident

variable {Q : Type} [Group Q] {P : Set (Subgroup Q)}

@[expose] def incl (hspan : TC.Thin.pSpan P = ⊤) : Q →* ↥(TC.Thin.pSpan P) where
  toFun x := ⟨x, by rw [hspan]; exact Subgroup.mem_top x⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem map_incl (hspan : TC.Thin.pSpan P = ⊤) {n : ℕ} (φ : ↥(TC.Thin.pSpan P) →* AE.AEQ n)
    (L : Subgroup Q) : L.map (φ.comp (incl hspan)) = (L.subgroupOf (TC.Thin.pSpan P)).map φ := by
  ext a
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_comp, Function.comp_apply]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨incl hspan l, hl, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩

theorem mem_center_of_phi {n : ℕ} {𝒜 : Set (Finset (Fin n))} {H : Subgroup (AE.AEQ n)}
    (hspan : TC.Thin.pSpan P = ⊤) (I : TC.Thin.AEIdentOn P n 𝒜 H) {x : Q}
    (hx : I.φ (incl hspan x) = 1) : x ∈ Subgroup.center Q := by
  have hk := I.ker_le (MonoidHom.mem_ker.mpr hx)
  exact Subgroup.mem_center_iff.mpr fun y =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hk (incl hspan y))

theorem incl_mem_commutator (hspan : TC.Thin.pSpan P = ⊤) {x : Q} (hx : x ∈ commutator Q) :
    incl hspan x ∈ commutator ↥(TC.Thin.pSpan P) := by
  have h : (commutator Q).map (incl hspan) ≤ commutator ↥(TC.Thin.pSpan P) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact h (Subgroup.mem_map_of_mem _ hx)

theorem mem_commutator_of_e64 (hM : E64CenComm) (hspan : TC.Thin.pSpan P = ⊤)
    (I : TC.Thin.AEIdentOn P 7 AE.e64Sets AE.e64Sub) {L₁ L₂ L₃ : Subgroup Q} (h₁ : L₁ ∈ P)
    (h₂ : L₂ ∈ P) (h₃ : L₃ ∈ P) {x : Q} (hx : x ∈ L₁ ⊔ L₂ ⊔ L₃) (hc₁ : ∀ y ∈ L₁, x * y = y * x)
    (hc₂ : ∀ y ∈ L₂, x * y = y * x) (hc₃ : ∀ y ∈ L₃, x * y = y * x)
    (hZ : (L₁ ⊔ L₂ ⊔ L₃) ⊓ Subgroup.center Q = ⊥) : x ∈ commutator Q := by
  set Ψ : Q →* AE.AEQ 7 := I.φ.comp (incl hspan) with hΨ
  obtain ⟨α₁, hα₁, hc₁', b₁, hl₁⟩ := I.label _ h₁
  obtain ⟨α₂, hα₂, hc₂', b₂, hl₂⟩ := I.label _ h₂
  obtain ⟨α₃, hα₃, hc₃', b₃, hl₃⟩ := I.label _ h₃
  have hm₁ : L₁.map Ψ = AE.memBar α₁ hc₁' b₁ := (map_incl hspan I.φ L₁).trans hl₁
  have hm₂ : L₂.map Ψ = AE.memBar α₂ hc₂' b₂ := (map_incl hspan I.φ L₂).trans hl₂
  have hm₃ : L₃.map Ψ = AE.memBar α₃ hc₃' b₃ := (map_incl hspan I.φ L₃).trans hl₃
  set H₀ := L₁ ⊔ L₂ ⊔ L₃ with hH₀
  have hmap : H₀.map Ψ = AE.memBar α₁ hc₁' b₁ ⊔ AE.memBar α₂ hc₂' b₂ ⊔ AE.memBar α₃ hc₃' b₃ := by
    rw [hH₀, Subgroup.map_sup, Subgroup.map_sup, hm₁, hm₂, hm₃]
  have hcm : ∀ {L : Subgroup Q}, (∀ y ∈ L, x * y = y * x) → ∀ y ∈ L.map Ψ, Ψ x * y = y * Ψ x := by
    intro L hL y hy
    obtain ⟨l, hl, rfl⟩ := hy
    rw [← map_mul, ← map_mul, hL l hl]
  have hxm : Ψ x ∈ AE.memBar α₁ hc₁' b₁ ⊔ AE.memBar α₂ hc₂' b₂ ⊔ AE.memBar α₃ hc₃' b₃ := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hx
  have hd := hM α₁ hα₁ α₂ hα₂ α₃ hα₃ hc₁' hc₂' hc₃' b₁ b₂ b₃ (Ψ x) hxm
    (by rw [← hm₁]; exact hcm hc₁) (by rw [← hm₂]; exact hcm hc₂) (by rw [← hm₃]; exact hcm hc₃)
  rw [← hmap, ← Subgroup.map_commutator] at hd
  obtain ⟨c, hc, hcx⟩ := hd
  have hcH : c ∈ H₀ := by
    have h : ⁅H₀, H₀⁆ ≤ H₀ := Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => by
      rw [commutatorElement_def]
      exact H₀.mul_mem (H₀.mul_mem (H₀.mul_mem hg₁ hg₂) (H₀.inv_mem hg₁)) (H₀.inv_mem hg₂)
    exact h hc
  have hk : I.φ (incl hspan (c⁻¹ * x)) = 1 := by
    have : Ψ (c⁻¹ * x) = 1 := by rw [map_mul, map_inv, hcx, inv_mul_cancel]
    exact this
  have hkc := mem_center_of_phi hspan I hk
  have hk1 : c⁻¹ * x = 1 := by
    have h : c⁻¹ * x ∈ H₀ ⊓ Subgroup.center Q := ⟨H₀.mul_mem (H₀.inv_mem hcH) hx, hkc⟩
    rw [hZ] at h
    exact Subgroup.mem_bot.mp h
  rw [← inv_mul_eq_one.mp hk1, commutator_def]
  exact Subgroup.commutator_mono le_top le_top hc

theorem eq_one_of_center_commutator (hspan : TC.Thin.pSpan P = ⊤)
    (I : TC.Thin.AEIdentOn P 7 AE.e64Sets AE.e64Sub)
    (hinj : ∀ x ∈ commutator ↥(TC.Thin.pSpan P), I.φ x = 1 → x = 1) {x : Q}
    (hxc : x ∈ Subgroup.center Q) (hxd : x ∈ commutator Q) : x = 1 := by
  have hZ : Subgroup.center ↥I.φ.range = ⊥ := by
    rw [I.range_eq]
    exact TwinThinPf.center_e64_eq_bot
  have hmem : (⟨I.φ (incl hspan x), incl hspan x, rfl⟩ : ↥I.φ.range) ∈ Subgroup.center ↥I.φ.range := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨_, y, rfl⟩
    apply Subtype.ext
    show I.φ y * I.φ (incl hspan x) = I.φ (incl hspan x) * I.φ y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxc (y : Q))
  rw [hZ, Subgroup.mem_bot] at hmem
  have h1 : I.φ (incl hspan x) = 1 := congrArg Subtype.val hmem
  have h2 := hinj _ (incl_mem_commutator hspan hxd) h1
  exact congrArg Subtype.val h2

end Ident

end F7Z

section Steps

variable {n : ℕ}

@[expose] def P23E7N2 (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
        ∀ Z : Subgroup Y, P23ZData t u e Z →
          ∀ x ∈ Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.normalizer (Z : Set Y),
            x * e * x⁻¹ ≠ e → x * e * x⁻¹ ≠ e * t →
              e ∈ Subgroup.normalizer ((conjSub x (conjSub g (tightCore R)) : Subgroup Y) : Set Y) →
                ¬ CentMod (conjSub x (conjSub g (tightCore R))) e ∧
                  ¬ CentMod (conjSub x (conjSub g (tightCore R))) (e * t)

section Facts

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y} {Z : Subgroup Y}

theorem p23_Z_conj_J (hc : P23Cfg n Y R S t K' W u e g) (hZd : P23ZData t u e Z) {a : Y}
    (ha : a ∈ Z) :
    conjSub a (conjSub g (tightCore R)) = conjSub g (tightCore R) ∨
      (conjSub a (conjSub g (tightCore R)) = conjSub g K' ∧
        conjSub a (conjSub g K') = conjSub g (tightCore R)) := by
  have hd := hc.data
  have hau : a * u = u * a := Subgroup.mem_centralizer_singleton_iff.mp (hZd.le_u ha)
  have hae : a * e = e * a := hZd.comm a ha e hZd.he
  have hc' : g⁻¹ * a * g ∈ Subgroup.centralizer ({t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : a * (g * t * g⁻¹) = (g * t * g⁻¹) * a := by
      rw [hd.hgt]
      calc a * (u * e) = (a * u) * e := by group
        _ = (u * a) * e := by rw [hau]
        _ = u * (a * e) := by group
        _ = u * (e * a) := by rw [hae]
        _ = (u * e) * a := by group
    calc g⁻¹ * a * g * t = g⁻¹ * (a * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * a) * g := by rw [h1]
      _ = t * (g⁻¹ * a * g) := by group
  have hcg : ∀ X : Subgroup Y, conjSub a (conjSub g X) = conjSub g (conjSub (g⁻¹ * a * g) X) := by
    intro X
    rw [← conjSub_mul, ← conjSub_mul]
    congr 1
    group
  rcases p23_conj_twins hc hc' with ⟨h1, -⟩ | ⟨h1, h2⟩
  · left
    rw [hcg, h1]
  · right
    exact ⟨by rw [hcg, h1], by rw [hcg, h2]⟩

theorem p23_conj_not_normalizer (hN2 : P23E7N2 n) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g) (hno : ¬ SecNoExit R e)
    (hE : ECase1 R W e) (hZ : u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)))
    (hZd : P23ZData t u e Z) {m : Y}
    (hm : m ∈ Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.normalizer (Z : Set Y))
    (h1 : m * e * m⁻¹ ≠ e) (h2 : m * e * m⁻¹ ≠ e * t) :
    m * e * m⁻¹ ∉ Subgroup.normalizer ((conjSub g (tightCore R) : Subgroup Y) : Set Y) := by
  intro hN
  have hmt : m * t = t * m := Subgroup.mem_centralizer_singleton_iff.mp hm.1
  have hmt' : m * t * m⁻¹ = t := by rw [hmt, mul_inv_cancel_right]
  have hmt'' : m⁻¹ * t * m⁻¹⁻¹ = t := by
    rw [inv_inv]
    calc m⁻¹ * t * m = m⁻¹ * (t * m) := by group
      _ = m⁻¹ * (m * t) := by rw [hmt]
      _ = t := by group
  have hm' : m⁻¹ ∈ Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.normalizer (Z : Set Y) :=
    Subgroup.inv_mem _ hm
  have h1' : m⁻¹ * e * m⁻¹⁻¹ ≠ e := by
    intro h
    apply h1
    calc m * e * m⁻¹ = m * (m⁻¹ * e * m⁻¹⁻¹) * m⁻¹ := by rw [h]
      _ = e := by group
  have h2' : m⁻¹ * e * m⁻¹⁻¹ ≠ e * t := by
    intro h
    apply h2
    have ht2 : t * t = 1 := hZd.sq t hZd.ht
    have h3 : e = (m * e * m⁻¹) * t := by
      calc e = m * (m⁻¹ * e * m⁻¹⁻¹) * m⁻¹ := by group
        _ = m * (e * t) * m⁻¹ := by rw [h]
        _ = (m * e * m⁻¹) * (m * t * m⁻¹) := by group
        _ = (m * e * m⁻¹) * t := by rw [hmt']
    calc m * e * m⁻¹ = (m * e * m⁻¹) * (t * t) := by rw [ht2, mul_one]
      _ = ((m * e * m⁻¹) * t) * t := by group
      _ = e * t := by rw [← h3]
  have heN : e ∈ Subgroup.normalizer
      ((conjSub m⁻¹ (conjSub g (tightCore R)) : Subgroup Y) : Set Y) := by
    rw [mem_normalizer_iff_conjSub_eq, ← conjSub_mul,
      show e * m⁻¹ = m⁻¹ * (m * e * m⁻¹) by group, conjSub_mul, mem_normalizer_iff_conjSub_eq.mp hN]
  obtain ⟨hn1, hn2⟩ := hN2 hcit hP Y R S t K' W u e g hc hno hE hZ Z hZd m⁻¹ hm' h1' h2' heN
  have hwZ : m * e * m⁻¹ ∈ Z := by
    have h := conjSub_eq_of_mem_normalizer hm.2
    rw [← h]
    exact conj_mem_conjSub hZd.he
  rcases p23E7W714_proved hcit hP Y R S t K' W u e g hc hno hE hZ Z hZd _ hwZ hN with h | h
  · apply hn1
    have h3 := F7Z.centMod_conj h m⁻¹
    rwa [show m⁻¹ * (m * e * m⁻¹) * m⁻¹⁻¹ = e by group] at h3
  · apply hn2
    have h3 := F7Z.centMod_conj h m⁻¹
    have e1 : m⁻¹ * (m * e * m⁻¹ * t) * m⁻¹⁻¹ = e * t := by
      calc m⁻¹ * (m * e * m⁻¹ * t) * m⁻¹⁻¹ = e * (m⁻¹ * t * m⁻¹⁻¹) := by group
        _ = e * t := by rw [hmt'']
    rwa [e1] at h3

end Facts

theorem p23E7Cen3_of_lemL (hL : P23E7LemL n) (hNC : P23E7NC n) (hN2 : P23E7N2 n)
    (hM : E64CenComm) : P23E7Cen3 n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hE hZ xe xt xu hxe hxt hxu q₁ q₂ hq₁ hq₂ hq₁₂ hcen hsq
  rw [p23_stabMod_eq hc hE xe xt xu hxe hxt hxu, Subgroup.mem_centralizer_singleton_iff] at hq₁ hq₂
  clear hq₁₂ hsq
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hF1, hFt⟩ := hne
  obtain ⟨Z, hZd⟩ := p23E7ZEx_proved hcit hP Y R S t K' W u e g hc hno hE hZ
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hK' : K' ∈ Om R := hc.std.hK'.1
  have hKg : conjSub g (tightCore R) ∈ Om R := hΩ.conjInvariant g _ hK
  have hZ2 : IsPGroup 2 Z := hZd.isPGroup
  have he2 : e * e = 1 := hd.he2
  have ht2 : t * t = 1 := hZd.sq t hZd.ht
  have hOodd : Odd (Nat.card (oddCoreOf (Subgroup.centralizer ({t} : Set Y)))) := odd_natCard_oddCoreOf (Subgroup.centralizer ({t} : Set Y))
  have hZC : ∀ {a : Y}, a ∈ Z → a ∈ (Subgroup.centralizer ({t} : Set Y)) := fun ha => hZd.le_t ha
  have heC : e ∈ (Subgroup.centralizer ({t} : Set Y)) := hZC hZd.he
  have htC : t ∈ (Subgroup.centralizer ({t} : Set Y)) := hZC hZd.ht
  have hxe' : xe = ⟨e, heC⟩ := Subtype.ext hxe
  have hxt' : xt = ⟨t, htC⟩ := Subtype.ext hxt
  have hconjZ : ∀ {m : Y}, m ∈ (Subgroup.centralizer ({t} : Set Y)) ⊓ Subgroup.normalizer (Z : Set Y) → ∀ {a : Y}, a ∈ Z →
      m * a * m⁻¹ ∈ Z := by
    intro m hm a ha
    have h := conjSub_eq_of_mem_normalizer hm.2
    rw [← h]
    exact conj_mem_conjSub ha
  have hmt : ∀ {m : Y}, m ∈ (Subgroup.centralizer ({t} : Set Y)) ⊓ Subgroup.normalizer (Z : Set Y) → m * t * m⁻¹ = t := by
    intro m hm
    rw [Subgroup.mem_centralizer_singleton_iff.mp hm.1, mul_inv_cancel_right]
  have hπt : ∀ q : ↥(Subgroup.centralizer ({t} : Set Y)) ⧸ classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)), q * F7I.piC (Subgroup.centralizer ({t} : Set Y)) xt = F7I.piC (Subgroup.centralizer ({t} : Set Y)) xt * q := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y))) q
    show F7I.piC (Subgroup.centralizer ({t} : Set Y)) c * F7I.piC (Subgroup.centralizer ({t} : Set Y)) xt = F7I.piC (Subgroup.centralizer ({t} : Set Y)) xt * F7I.piC (Subgroup.centralizer ({t} : Set Y)) c
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (c : Y) * xt = xt * c
    rw [hxt]
    exact Subgroup.mem_centralizer_singleton_iff.mp c.2
  have hlift : ∀ q : ↥(Subgroup.centralizer ({t} : Set Y)) ⧸ classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)), ∃ m : Y,
      ∃ hm : m ∈ (Subgroup.centralizer ({t} : Set Y)) ⊓ Subgroup.normalizer (Z : Set Y), F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩ = q := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y))) q
    obtain ⟨o, ho, m, hm, hcm⟩ := hZd.frattini c c.2
    refine ⟨m, hm, ?_⟩
    have h1 : c = ⟨o, oddCoreOf_le_self (Subgroup.centralizer ({t} : Set Y)) ho⟩ * ⟨m, hm.1⟩ := Subtype.ext hcm
    show F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩ = F7I.piC (Subgroup.centralizer ({t} : Set Y)) c
    rw [h1, map_mul, (F7I.piC_eq_one_iff (⟨o, _⟩ : ↥(Subgroup.centralizer ({t} : Set Y)))).mpr ho, one_mul]
  have hπconj : ∀ {m : Y} (hm : m ∈ (Subgroup.centralizer ({t} : Set Y)) ⊓ Subgroup.normalizer (Z : Set Y)) {a : Y} (ha : a ∈ (Subgroup.centralizer ({t} : Set Y)))
      (hma : m * a * m⁻¹ ∈ (Subgroup.centralizer ({t} : Set Y))), F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m * a * m⁻¹, hma⟩ =
        F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩ * F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨a, ha⟩ * (F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩)⁻¹ := by
    intro m hm a ha hma
    rw [← map_mul, ← map_inv, ← map_mul]
    rfl
  obtain ⟨m₁, hm₁, hπ₁⟩ := hlift q₁
  obtain ⟨m₂, hm₂, hπ₂⟩ := hlift q₂
  have he₁Z : m₁ * e * m₁⁻¹ ∈ Z := hconjZ hm₁ hZd.he
  have he₂Z : m₂ * e * m₂⁻¹ ∈ Z := hconjZ hm₂ hZd.he
  obtain ⟨f, hfdef⟩ : ∃ f : Y, f = e * (m₁ * e * m₁⁻¹) * (m₂ * e * m₂⁻¹) := ⟨_, rfl⟩
  have hfZ : f ∈ Z := by
    rw [hfdef]
    exact Z.mul_mem (Z.mul_mem hZd.he he₁Z) he₂Z
  have hπe₁ : F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m₁ * e * m₁⁻¹, hZC he₁Z⟩ = q₁ * F7I.piC (Subgroup.centralizer ({t} : Set Y)) xe * q₁⁻¹ := by
    rw [hπconj hm₁ heC (hZC he₁Z), hπ₁, hxe']
  have hπe₂ : F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m₂ * e * m₂⁻¹, hZC he₂Z⟩ = q₂ * F7I.piC (Subgroup.centralizer ({t} : Set Y)) xe * q₂⁻¹ := by
    rw [hπconj hm₂ heC (hZC he₂Z), hπ₂, hxe']
  have hF : F7I.piC (Subgroup.centralizer ({t} : Set Y)) xe * (q₁ * F7I.piC (Subgroup.centralizer ({t} : Set Y)) xe * q₁⁻¹) * (q₂ * F7I.piC (Subgroup.centralizer ({t} : Set Y)) xe * q₂⁻¹) =
      F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨f, hZC hfZ⟩ := by
    rw [← hπe₁, ← hπe₂, hxe', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hfdef.symm
  rw [hF] at hcen hF1 hFt
  have hfinv : ∀ {m : Y}, m ∈ (Subgroup.centralizer ({t} : Set Y)) ⊓ Subgroup.normalizer (Z : Set Y) → m * f * m⁻¹ = f := by
    intro m hm
    have hmf : m * f * m⁻¹ ∈ Z := hconjZ hm hfZ
    have h1 : F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m * f * m⁻¹, hZC hmf⟩ = F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨f, hZC hfZ⟩ := by
      rw [hπconj hm (hZC hfZ) (hZC hmf), hcen, mul_inv_cancel_right]
    have h2 : (m * f * m⁻¹)⁻¹ * f ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)) := (F7I.piC_eq_iff _ _).mp h1
    have h3 : (m * f * m⁻¹)⁻¹ * f ∈ Z := Z.mul_mem (Z.inv_mem hmf) hfZ
    exact inv_mul_eq_one.mp (Sec13.L94T.eq_one_of_isPGroup_of_odd hZ2 hOodd h3 h2)
  have hnc : ∀ {m : Y} (hm : m ∈ (Subgroup.centralizer ({t} : Set Y)) ⊓ Subgroup.normalizer (Z : Set Y)) (hmZ : m * e * m⁻¹ ∈ Z),
      (∀ q, q * F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m * e * m⁻¹, hZC hmZ⟩ = F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m * e * m⁻¹, hZC hmZ⟩ * q) → False := by
    intro m hm hmZ hcq
    refine hNC hcit hP Y R S t K' W u e g hc hno hE hZ xe hxe fun q => ?_
    rw [hπconj hm heC (hZC hmZ)] at hcq
    have h := hcq (F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩ * q * (F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩)⁻¹)
    rw [hxe']
    have h4 : F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩ * (q * F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨e, heC⟩) * (F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩)⁻¹ =
        F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩ * (F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨e, heC⟩ * q) * (F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩)⁻¹ := by
      calc F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩ * (q * F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨e, heC⟩) * (F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩)⁻¹ =
            F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩ * q * (F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩)⁻¹ *
              (F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩ * F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨e, heC⟩ * (F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩)⁻¹) := by group
        _ = (F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩ * F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨e, heC⟩ * (F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩)⁻¹) *
              (F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩ * q * (F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩)⁻¹) := h
        _ = F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩ * (F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨e, heC⟩ * q) * (F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩)⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h4)
  have hcentral_mul : ∀ a b : ↥(Subgroup.centralizer ({t} : Set Y)) ⧸ classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)), (∀ q, q * a = a * q) →
      (∀ q, q * b = b * q) → ∀ q, q * (a⁻¹ * b) = (a⁻¹ * b) * q := by
    intro a b ha hb q
    have hai : q * a⁻¹ = a⁻¹ * q := by
      calc q * a⁻¹ = a⁻¹ * (a * q) * a⁻¹ := by group
        _ = a⁻¹ * (q * a) * a⁻¹ := by rw [ha q]
        _ = a⁻¹ * q := by group
    calc q * (a⁻¹ * b) = (q * a⁻¹) * b := by group
      _ = a⁻¹ * (q * b) := by rw [hai]; group
      _ = a⁻¹ * (b * q) := by rw [hb q]
      _ = (a⁻¹ * b) * q := by group
  have hne : ∀ {m : Y} (hm : m ∈ (Subgroup.centralizer ({t} : Set Y)) ⊓ Subgroup.normalizer (Z : Set Y)) {q : ↥(Subgroup.centralizer ({t} : Set Y)) ⧸ classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y))},
      F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m, hm.1⟩ = q → ¬ (q * F7I.piC (Subgroup.centralizer ({t} : Set Y)) xe = F7I.piC (Subgroup.centralizer ({t} : Set Y)) xe * q) → m * e * m⁻¹ ≠ e := by
    intro m hm q hπ hq h
    apply hq
    have h1 : F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨m * e * m⁻¹, hZC (hconjZ hm hZd.he)⟩ = F7I.piC (Subgroup.centralizer ({t} : Set Y)) xe := by
      rw [hxe']
      congr 1
      exact Subtype.ext h
    rw [hπconj hm heC _, hπ, ← hxe'] at h1
    calc q * F7I.piC (Subgroup.centralizer ({t} : Set Y)) xe = (q * F7I.piC (Subgroup.centralizer ({t} : Set Y)) xe * q⁻¹) * q := by group
      _ = F7I.piC (Subgroup.centralizer ({t} : Set Y)) xe * q := by rw [h1]
  have hne₁ : m₁ * e * m₁⁻¹ ≠ e := hne hm₁ hπ₁ hq₁
  have hne₂ : m₂ * e * m₂⁻¹ ≠ e := hne hm₂ hπ₂ hq₂
  have hcomm₁₂ : (m₁ * e * m₁⁻¹) * (m₂ * e * m₂⁻¹) = (m₂ * e * m₂⁻¹) * (m₁ * e * m₁⁻¹) :=
    hZd.comm _ he₁Z _ he₂Z
  have hcomme₁ : e * (m₁ * e * m₁⁻¹) = (m₁ * e * m₁⁻¹) * e := hZd.comm _ hZd.he _ he₁Z
  have hcomme₂ : e * (m₂ * e * m₂⁻¹) = (m₂ * e * m₂⁻¹) * e := hZd.comm _ hZd.he _ he₂Z
  have hnet : ∀ {a b : Y} (ha : a ∈ Z) (hb : b ∈ Z), (f = t * b) →
      (∀ q, q * F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨b, hZC hb⟩ = F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨b, hZC hb⟩ * q) := by
    intro a b _ hb hfb q
    have h1 : F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨b, hZC hb⟩ = (F7I.piC (Subgroup.centralizer ({t} : Set Y)) xt)⁻¹ * F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨f, hZC hfZ⟩ := by
      rw [hxt', ← map_inv, ← map_mul]
      congr 1
      apply Subtype.ext
      show b = t⁻¹ * f
      rw [hfb]
      group
    rw [h1]
    exact hcentral_mul _ _ hπt hcen q
  have hnet₁ : m₁ * e * m₁⁻¹ ≠ e * t := by
    intro h
    refine hnc hm₂ he₂Z (hnet hZd.he he₂Z ?_)
    rw [hfdef, h]
    calc e * (e * t) * (m₂ * e * m₂⁻¹) = (e * e) * t * (m₂ * e * m₂⁻¹) := by group
      _ = t * (m₂ * e * m₂⁻¹) := by rw [he2, one_mul]
  have hnet₂ : m₂ * e * m₂⁻¹ ≠ e * t := by
    intro h
    refine hnc hm₁ he₁Z (hnet hZd.he he₁Z ?_)
    have hte : t * e = e * t := hZd.comm t hZd.ht e hZd.he
    rw [hfdef, h, hcomme₁]
    calc m₁ * e * m₁⁻¹ * e * (e * t) = m₁ * e * m₁⁻¹ * (e * e) * t := by group
      _ = m₁ * e * m₁⁻¹ * t := by rw [he2, mul_one]
      _ = t * (m₁ * e * m₁⁻¹) := (hZd.comm _ he₁Z t hZd.ht)
  have hnotN₁ := p23_conj_not_normalizer hN2 hcit hP hc hno hE hZ hZd hm₁ hne₁ hnet₁
  have hnotN₂ := p23_conj_not_normalizer hN2 hcit hP hc hno hE hZ hZd hm₂ hne₂ hnet₂
  obtain ⟨heK, heK', heJ⟩ := hc.centMod_e
  have heJN : e ∈ Subgroup.normalizer ((conjSub g (tightCore R) : Subgroup Y) : Set Y) :=
    F7E.mem_normalizer_of_centMod heJ he2
  have hswap : ∀ {a : Y}, a ∈ Z →
      a ∉ Subgroup.normalizer ((conjSub g (tightCore R) : Subgroup Y) : Set Y) →
      conjSub a (conjSub g (tightCore R)) = conjSub g K' ∧
        conjSub a (conjSub g K') = conjSub g (tightCore R) := by
    intro a ha haN
    rcases p23_Z_conj_J hc hZd ha with h | h
    · exact absurd (mem_normalizer_iff_conjSub_eq.mpr h) haN
    · exact h
  have hfN : f ∈ Subgroup.normalizer ((conjSub g (tightCore R) : Subgroup Y) : Set Y) := by
    obtain ⟨-, h₁b⟩ := hswap he₁Z hnotN₁
    obtain ⟨h₂a, -⟩ := hswap he₂Z hnotN₂
    rw [hfdef, mem_normalizer_iff_conjSub_eq, conjSub_mul (e * (m₁ * e * m₁⁻¹)) (m₂ * e * m₂⁻¹),
      conjSub_mul e (m₁ * e * m₁⁻¹), h₂a, h₁b, mem_normalizer_iff_conjSub_eq.mp heJN]
  have hf1 : f ≠ 1 := by
    intro h
    apply hF1
    have h1 : (⟨f, hZC hfZ⟩ : ↥(Subgroup.centralizer ({t} : Set Y))) = 1 := Subtype.ext h
    rw [h1, map_one]
  have hft : f ≠ t := by
    intro h
    apply hFt
    rw [hxt']
    congr 1
    exact Subtype.ext h
  have hW714 := p23E7W714_proved hcit hP Y R S t K' W u e g hc hno hE hZ Z hZd f hfZ hfN
  have hft1 : f * t ≠ 1 := by
    intro h
    apply hft
    calc f = f * t * t := by rw [mul_assoc, ht2, mul_one]
      _ = t := by rw [h, one_mul]
  obtain ⟨f', hf'Z, hf'J, hf'1, hf'inv, hf'cases⟩ : ∃ f' : Y, f' ∈ Z ∧
      CentMod (conjSub g (tightCore R)) f' ∧ f' ≠ 1 ∧
      (∀ m : Y, m ∈ (Subgroup.centralizer ({t} : Set Y)) ⊓ Subgroup.normalizer (Z : Set Y) → m * f' * m⁻¹ = f') ∧
        (f' = f ∨ f' = f * t) := by
    rcases hW714 with h | h
    · exact ⟨f, hfZ, h, hf1, fun m hm => hfinv hm, Or.inl rfl⟩
    · refine ⟨f * t, Z.mul_mem hfZ hZd.ht, h, hft1, fun m hm => ?_, Or.inr rfl⟩
      calc m * (f * t) * m⁻¹ = (m * f * m⁻¹) * (m * t * m⁻¹) := by group
        _ = f * t := by rw [hfinv hm, hmt hm]
  have hf'2 : f' * f' = 1 := hZd.sq f' hf'Z
  have hf'e : f' * e = e * f' := hZd.comm f' hf'Z e hZd.he
  obtain ⟨hKf', hK'f'⟩ := hZd.centMod hc hf'Z
  have hECent : CentModE R e f' := p23ECent_proved hcit hP Y R S t K' W u e g hc hno hE hZ f' hf'2
    (Subgroup.mem_centralizer_singleton_iff.mpr hf'e) hKf' hK'f' hf'J
  have hVZ : Subgroup.zpowers f' ≤ Z := Subgroup.zpowers_le.mpr hf'Z
  have hV1 : Subgroup.zpowers f' ≠ ⊥ := by
    intro h
    apply hf'1
    have h1 := Subgroup.mem_zpowers f'
    rw [h] at h1
    exact Subgroup.mem_bot.mp h1
  have hVa : ∀ m, m ∈ (Subgroup.centralizer ({t} : Set Y)) ⊓ Subgroup.normalizer (Z : Set Y) →
      Subgroup.zpowers f' ≤ aSub R Z (m * e * m⁻¹) := by
    intro m hm
    rw [Subgroup.zpowers_le, mem_aSub_iff (hZd.le_cent (hconjZ hm hZd.he))]
    refine ⟨hf'Z, ?_⟩
    have h := (centModE_conj (R := R) m e f').mpr hECent
    rwa [hf'inv m hm] at h
  have h1N : (1 : Y) ∈ (Subgroup.centralizer ({t} : Set Y)) ⊓ Subgroup.normalizer (Z : Set Y) := Subgroup.one_mem _
  have hVe : Subgroup.zpowers f' ≤ aSub R Z e := by
    have h := hVa 1 h1N
    rwa [show (1 : Y) * e * 1⁻¹ = e by group] at h
  have heO : e ∈ p23Orb Z t e := ⟨1, h1N, by group⟩
  obtain ⟨hspan, I, hinj, hsec⟩ := hL hcit hP Y R S t K' W u e g hc hno hE hZ Z hZd _ hVZ hV1 e heO
    (m₁ * e * m₁⁻¹) ⟨m₁, hm₁, rfl⟩ (Ne.symm hne₁) hVe (hVa m₁ hm₁)
  have hV2 : IsPGroup 2 (Subgroup.closure ({f', e, e} : Set Y)) :=
    F7V.isPGroup_closure_three hf'2 he2 he2 hf'e hf'e rfl
  have hf'V : f' ∈ Subgroup.closure ({f', e, e} : Set Y) := Subgroup.subset_closure (by simp)
  have heV : e ∈ Subgroup.closure ({f', e, e} : Set Y) := Subgroup.subset_closure (by simp)
  have hsyl : ∀ {J : Subgroup Y}, CentMod J f' → CentMod J e →
      ∃ R' : Subgroup Y, IsSylow2In R' J ∧ (∀ r ∈ R', r * f' = f' * r) ∧ ∀ r ∈ R', r * e = e * r := by
    intro J hJf hJe
    obtain ⟨R', hR', -, h1, h2⟩ := F7V.exists_sylow_comm_pair hV2
      (F7V.closure_three_le (F7E.mem_normalizer_of_centMod hJf hf'2)
        (F7E.mem_normalizer_of_centMod hJe he2) (F7E.mem_normalizer_of_centMod hJe he2))
      hf'V heV hJf hJe
    exact ⟨R', hR', h1, h2⟩
  obtain ⟨R₀, hR₀, hR₀f, hR₀e⟩ := hsyl hKf' heK
  obtain ⟨R₀', hR₀', hR₀'f, hR₀'e⟩ := hsyl hK'f' heK'
  obtain ⟨R₁, hR₁, hR₁f, hR₁e⟩ := hsyl hf'J heJ
  have hcen_e : ∀ {B : Subgroup Y}, (∀ r ∈ B, r * e = e * r) →
      B ≤ Subgroup.centralizer ({e} : Set Y) :=
    fun h r hr => Subgroup.mem_centralizer_singleton_iff.mpr (h r hr)
  have hgen := p23EGen_proved hcit hP Y R S t K' W u e g hc hno hE hZ R₀ R₀' R₁ hR₀ hR₀' hR₁
    (hcen_e hR₀e) (hcen_e hR₀'e) (hcen_e hR₁e)
  have hR₀R := Asc77.mem_RSet_of_isSylow2In hK hR₀
  have hR₀'R := Asc77.mem_RSet_of_isSylow2In hK' hR₀'
  have hR₁R := Asc77.mem_RSet_of_isSylow2In hKg hR₁
  have hHE : R₀ ⊔ R₀' ⊔ R₁ ≤ rLayer (Om R) e :=
    sup_le (sup_le (F7C.le_rLayer hR₀R (hcen_e hR₀e)) (F7C.le_rLayer hR₀'R (hcen_e hR₀'e)))
      (F7C.le_rLayer hR₁R (hcen_e hR₁e))
  have heH : e ∈ R₀ ⊔ R₀' ⊔ R₁ :=
    F7Z.mem_of_mem_sup_odd hHE (F7C.rLayer_le_centralizer e) he2 (hgen (p23_e_mem_rLayer hc))
  have hBV : ∀ {B : Subgroup Y}, (∀ r ∈ B, r * f' = f' * r) →
      B ≤ Subgroup.centralizer ((Subgroup.zpowers f' : Subgroup Y) : Set Y) := by
    intro B hB r hr
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_left (show Commute f' r from (hB r hr).symm) k).eq
  have hconjC : ∀ {B : Subgroup Y} (m a : Y), (∀ r ∈ B, r * a = a * r) →
      ∀ r ∈ conjSub m B, r * (m * a * m⁻¹) = (m * a * m⁻¹) * r := by
    intro B m a hB r hr
    rw [mem_conjSub_iff] at hr
    have h := hB _ hr
    calc r * (m * a * m⁻¹) = m * ((m⁻¹ * r * m) * a) * m⁻¹ := by group
      _ = m * (a * (m⁻¹ * r * m)) * m⁻¹ := by rw [h]
      _ = (m * a * m⁻¹) * r := by group
  have hkey : ∀ m, m ∈ (Subgroup.centralizer ({t} : Set Y)) ⊓ Subgroup.normalizer (Z : Set Y) → ∀ y, y = m * e * m⁻¹ →
      ∃ hy : y ∈ rLayerSub (Om R) (Subgroup.zpowers f'),
        F7I.piC _ ⟨y, hy⟩ ∈ commutator (SecQuot (rLayerSub (Om R) (Subgroup.zpowers f'))) := by
    intro m hm y hy
    have hmf := hf'inv m hm
    have hB : ∀ {J R' : Subgroup Y}, J ∈ Om R → IsSylow2In R' J → (∀ r ∈ R', r * f' = f' * r) →
        (∀ r ∈ R', r * e = e * r) →
        secImage (rLayerSub (Om R) (Subgroup.zpowers f')) (conjSub m R') ∈
            p23SecFamV R (Subgroup.zpowers f') ∧
          conjSub m R' ≤ rLayerSub (Om R) (Subgroup.zpowers f') ∧
          conjSub m R' ≤ rLayer (Om R) y ∧ ∀ r ∈ conjSub m R', r * y = y * r := by
      intro J R' hJ hR' hRf hRe
      have hRR : conjSub m R' ∈ RSet (Om R) :=
        Q3CL.Thompson.conjSub_mem_RSet hΩ (Asc77.mem_RSet_of_isSylow2In hJ hR') m
      have hc1 : ∀ r ∈ conjSub m R', r * f' = f' * r := by
        intro r hr
        have h := hconjC m f' hRf r hr
        rwa [hmf] at h
      have hc2 : ∀ r ∈ conjSub m R', r * y = y * r := by
        intro r hr
        rw [hy]
        exact hconjC m e hRe r hr
      have hRV := hBV hc1
      refine ⟨⟨_, hRR, hRV, rfl⟩, F7C.le_rLayerSub hRR hRV, ?_, hc2⟩
      rw [hy, rLayer_conj]
      exact conjSub_mono (F7C.le_rLayer (Asc77.mem_RSet_of_isSylow2In hJ hR') (hcen_e hRe))
    obtain ⟨hP₀, hY₀, hE₀, hc₀⟩ := hB hK hR₀ hR₀f hR₀e
    obtain ⟨hP₀', hY₀', hE₀', hc₀'⟩ := hB hK' hR₀' hR₀'f hR₀'e
    obtain ⟨hP₁, hY₁, hE₁, hc₁⟩ := hB hKg hR₁ hR₁f hR₁e
    have hyH : y ∈ conjSub m R₀ ⊔ conjSub m R₀' ⊔ conjSub m R₁ := by
      have h : conjSub m (R₀ ⊔ R₀' ⊔ R₁) = conjSub m R₀ ⊔ conjSub m R₀' ⊔ conjSub m R₁ := by
        simp only [conjSub, Subgroup.map_sup]
      rw [← h, hy]
      exact conj_mem_conjSub heH
    have hyY : y ∈ rLayerSub (Om R) (Subgroup.zpowers f') := sup_le (sup_le hY₀ hY₀') hY₁ hyH
    refine ⟨hyY, ?_⟩
    have hyO : y ∈ p23Orb Z t e := ⟨m, hm, hy⟩
    have hVy : Subgroup.zpowers f' ≤ aSub R Z y := hy ▸ hVa m hm
    have himg : secImage (rLayerSub (Om R) (Subgroup.zpowers f'))
          (conjSub m R₀ ⊔ conjSub m R₀' ⊔ conjSub m R₁) =
        secImage (rLayerSub (Om R) (Subgroup.zpowers f')) (conjSub m R₀) ⊔
          secImage (rLayerSub (Om R) (Subgroup.zpowers f')) (conjSub m R₀') ⊔
          secImage (rLayerSub (Om R) (Subgroup.zpowers f')) (conjSub m R₁) := by
      unfold secImage
      rw [Subgroup.subgroupOf_sup (sup_le hY₀ hY₀') hY₁, Subgroup.subgroupOf_sup hY₀ hY₀',
        Subgroup.map_sup, Subgroup.map_sup]
    have hmemL : F7I.piC _ ⟨y, hyY⟩ ∈
        secImage (rLayerSub (Om R) (Subgroup.zpowers f')) (conjSub m R₀) ⊔
          secImage (rLayerSub (Om R) (Subgroup.zpowers f')) (conjSub m R₀') ⊔
          secImage (rLayerSub (Om R) (Subgroup.zpowers f')) (conjSub m R₁) := by
      rw [← himg]
      exact F7I.mem_map_piC.mpr ⟨⟨y, hyY⟩, hyH, rfl⟩
    have hcomm : ∀ {B : Subgroup Y}, (∀ r ∈ B, r * y = y * r) →
        ∀ z ∈ secImage (rLayerSub (Om R) (Subgroup.zpowers f')) B,
          F7I.piC _ ⟨y, hyY⟩ * z = z * F7I.piC _ ⟨y, hyY⟩ := by
      intro B hBc z hz
      obtain ⟨b, hb, rfl⟩ := F7I.mem_map_piC.mp hz
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hBc _ hb).symm
    have hle : ∀ {B : Subgroup Y}, B ≤ rLayer (Om R) y →
        secImage (rLayerSub (Om R) (Subgroup.zpowers f')) B ≤
          secImage (rLayerSub (Om R) (Subgroup.zpowers f'))
            (rLayer (Om R) y ⊓ rLayerSub (Om R) (Subgroup.zpowers f')) := by
      intro B hBE z hz
      obtain ⟨b, hb, rfl⟩ := F7I.mem_map_piC.mp hz
      exact F7I.mem_map_piC.mpr ⟨b, ⟨hBE hb, b.2⟩, rfl⟩
    refine F7Z.mem_commutator_of_e64 hM hspan I hP₀ hP₀' hP₁ hmemL (hcomm hc₀) (hcomm hc₀')
      (hcomm hc₁) ?_
    exact eq_bot_iff.mpr (le_trans (inf_le_inf_right _ (sup_le (sup_le (hle hE₀) (hle hE₀')) (hle hE₁)))
      (hsec y hyO hVy).le)
  have htR₀ : t ∈ R₀ := Q3CP.mem_of_isSylow2In_of_isUniqueInvolution hz hR₀
  have hR₀c : ∀ r ∈ R₀, r * t = t * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_unique hz (hR₀.1 hr))
  have hR₀V := hBV hR₀f
  have hR₀Y : R₀ ≤ rLayerSub (Om R) (Subgroup.zpowers f') := F7C.le_rLayerSub hR₀R hR₀V
  have htY : t ∈ rLayerSub (Om R) (Subgroup.zpowers f') := hR₀Y htR₀
  have htcomm : F7I.piC _ ⟨t, htY⟩ ∈ commutator (SecQuot (rLayerSub (Om R) (Subgroup.zpowers f'))) := by
    have hPL : secImage (rLayerSub (Om R) (Subgroup.zpowers f')) R₀ ∈ p23SecFamV R (Subgroup.zpowers f') :=
      ⟨R₀, hR₀R, hR₀V, rfl⟩
    have hmem : F7I.piC _ ⟨t, htY⟩ ∈ secImage (rLayerSub (Om R) (Subgroup.zpowers f')) R₀ :=
      F7I.mem_map_piC.mpr ⟨⟨t, htY⟩, htR₀, rfl⟩
    have hcm : ∀ z ∈ secImage (rLayerSub (Om R) (Subgroup.zpowers f')) R₀,
        F7I.piC _ ⟨t, htY⟩ * z = z * F7I.piC _ ⟨t, htY⟩ := by
      intro z hz
      obtain ⟨b, hb, rfl⟩ := F7I.mem_map_piC.mp hz
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hR₀c _ hb).symm
    have hle : secImage (rLayerSub (Om R) (Subgroup.zpowers f')) R₀ ≤
        secImage (rLayerSub (Om R) (Subgroup.zpowers f'))
          (rLayer (Om R) e ⊓ rLayerSub (Om R) (Subgroup.zpowers f')) := by
      intro z hz
      obtain ⟨b, hb, rfl⟩ := F7I.mem_map_piC.mp hz
      exact F7I.mem_map_piC.mpr ⟨b, ⟨F7C.le_rLayer hR₀R (hcen_e hR₀e) hb, b.2⟩, rfl⟩
    refine F7Z.mem_commutator_of_e64 hM hspan I hPL hPL hPL ?_ hcm hcm hcm ?_
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hmem)
    · exact eq_bot_iff.mpr (le_trans (inf_le_inf_right _ (sup_le (sup_le hle hle) hle))
        (hsec e heO hVe).le)
  obtain ⟨heY, he_c⟩ := hkey 1 h1N e (by group)
  obtain ⟨he₁Y, he₁_c⟩ := hkey m₁ hm₁ _ rfl
  obtain ⟨he₂Y, he₂_c⟩ := hkey m₂ hm₂ _ rfl
  have hfY : f ∈ rLayerSub (Om R) (Subgroup.zpowers f') := by
    rw [hfdef]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ heY he₁Y) he₂Y
  have hf'Y : f' ∈ rLayerSub (Om R) (Subgroup.zpowers f') := by
    rcases hf'cases with h | h
    · exact (congrArg (fun x => x ∈ rLayerSub (Om R) (Subgroup.zpowers f')) h).mpr hfY
    · exact (congrArg (fun x => x ∈ rLayerSub (Om R) (Subgroup.zpowers f')) h).mpr
        (Subgroup.mul_mem _ hfY htY)
  have hcf : F7I.piC _ ⟨f, hfY⟩ ∈ commutator (SecQuot (rLayerSub (Om R) (Subgroup.zpowers f'))) := by
    have h : (⟨f, hfY⟩ : ↥(rLayerSub (Om R) (Subgroup.zpowers f'))) =
        ⟨e, heY⟩ * ⟨m₁ * e * m₁⁻¹, he₁Y⟩ * ⟨m₂ * e * m₂⁻¹, he₂Y⟩ := Subtype.ext hfdef
    rw [h, map_mul, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ he_c he₁_c) he₂_c
  have hcc : F7I.piC _ ⟨f', hf'Y⟩ ∈
      commutator (SecQuot (rLayerSub (Om R) (Subgroup.zpowers f'))) := by
    rcases hf'cases with h | h
    · have h1 : (⟨f', hf'Y⟩ : ↥(rLayerSub (Om R) (Subgroup.zpowers f'))) = ⟨f, hfY⟩ := Subtype.ext h
      rw [h1]
      exact hcf
    · have h1 : (⟨f', hf'Y⟩ : ↥(rLayerSub (Om R) (Subgroup.zpowers f'))) = ⟨f, hfY⟩ * ⟨t, htY⟩ :=
        Subtype.ext h
      rw [h1, map_mul]
      exact Subgroup.mul_mem _ hcf htcomm
  have hcZ : F7I.piC _ ⟨f', hf'Y⟩ ∈
      Subgroup.center (SecQuot (rLayerSub (Om R) (Subgroup.zpowers f'))) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective
      (classicalInvolutionOddCore ↥(rLayerSub (Om R) (Subgroup.zpowers f'))) z
    show F7I.piC _ b * F7I.piC _ ⟨f', hf'Y⟩ = F7I.piC _ ⟨f', hf'Y⟩ * F7I.piC _ b
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (F7C.rLayerSub_le_centralizer _ b.2) f'
      (Subgroup.mem_zpowers f')).symm
  have hc1 := F7Z.eq_one_of_center_commutator hspan I hinj hcZ hcc
  have hO : f' ∈ oddCoreOf (rLayerSub (Om R) (Subgroup.zpowers f')) := (F7I.piC_eq_one_iff _).mp hc1
  exact hf'1 (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hO
    (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf'2))

theorem p23E7Y_of_lemL (hT : Thm4RTwinBelow 3 n) (hT4 : TwinThmE.T4Supply)
    (hmodel : TwinDisc.ExitE4.E4ModelDStar) (hD4 : TwinCentRes.ModelFactD42) (hMu : P23E4Mu n)
    (hTwo : P23Two n) (hα : P23Alpha n) (hL : P23E7LemL n) (hN2 : P23E7N2 n)
    (hM : E64CenComm) : P23E7Y n :=
  p23E7Y_of_lemL_cen3 hT hT4 hmodel hD4 hMu hTwo hα hL
    (p23E7Cen3_of_lemL hL (p23E7NC_proved hT hTwo hα) hN2 hM)

end Steps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
