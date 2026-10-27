module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.NA
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L A T : Subgroup G} {z t : G}
  {W W₁ W₂ : Subgroup G}

private theorem conj_mul_conj_eq_of_sub_mem {A W : Subgroup G} [IsMulCommutative ↥W]
    {s z : G} (hAW : A ≤ W) (hsA : s ∈ centralizer (A : Set G))
    (hzA : z ∈ centralizer (A : Set G))
    (hs : ∀ w ∈ W, s * w * s⁻¹ * w⁻¹ ∈ A)
    (hz : ∀ w ∈ W, z * w * z⁻¹ * w⁻¹ ∈ A) :
    ∀ w ∈ W, s * (z * w * z⁻¹) * s⁻¹ = z * (s * w * s⁻¹) * z⁻¹ := by
  intro w hw
  set a : G := s * w * s⁻¹ * w⁻¹ with ha
  set b : G := z * w * z⁻¹ * w⁻¹ with hb
  have haA : a ∈ A := hs w hw
  have hbA : b ∈ A := hz w hw
  have hsa : s * a * s⁻¹ = a := by
    rw [show s * a = a * s from (mem_centralizer_iff.1 hsA a haA).symm]
    group
  have hza : z * a * z⁻¹ = a := by
    rw [show z * a = a * z from (mem_centralizer_iff.1 hzA a haA).symm]
    group
  have hsb : s * b * s⁻¹ = b := by
    rw [show s * b = b * s from (mem_centralizer_iff.1 hsA b hbA).symm]
    group
  have hzb : z * b * z⁻¹ = b := by
    rw [show z * b = b * z from (mem_centralizer_iff.1 hzA b hbA).symm]
    group
  have hab : a * b = b * a :=
    congrArg Subtype.val (mul_comm' (⟨a, hAW haA⟩ : W) ⟨b, hAW hbA⟩)
  have haw : a * w = s * w * s⁻¹ := by rw [ha]; group
  have hbw : b * w = z * w * z⁻¹ := by rw [hb]; group
  calc s * (z * w * z⁻¹) * s⁻¹ = s * (b * w) * s⁻¹ := by rw [← hbw]
    _ = (s * b * s⁻¹) * (s * w * s⁻¹) := by group
    _ = b * (a * w) := by rw [hsb, ← haw]
    _ = (b * a) * w := by group
    _ = (a * b) * w := by rw [hab]
    _ = a * (b * w) := by group
    _ = (z * a * z⁻¹) * (z * w * z⁻¹) := by rw [hza, hbw]
    _ = z * (a * w) * z⁻¹ := by group
    _ = z * (s * w * s⁻¹) * z⁻¹ := by rw [← haw]

private theorem WHyp.conj_eq_one_or_conj_z (h : WHyp G L A T z t W W₁ W₂) {r : G}
    (hr : r ∈ R₀ A z) :
    (∀ w ∈ W, r * w * r⁻¹ = w) ∨ (∀ w ∈ W, r * w * r⁻¹ = z * w * z⁻¹) := by
  have hzW : z ∈ normalizer (W : Set G) := h.z_mem_normalizer
  have hcoe : (↑(W ⊔ zpowers z) : Set G) = (W : Set G) * (zpowers z : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left W (zpowers z) (zpowers_le.2 hzW)
  have hr' : r ∈ (W : Set G) * (zpowers z : Set G) := by
    rw [← hcoe]
    rwa [h.R₀_eq] at hr
  obtain ⟨v, hv, k, hk, rfl⟩ := hr'
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  haveI : IsMulCommutative ↥W := h.elemAb.toIsMulCommutative
  have hvfix : ∀ w ∈ W, v * w * v⁻¹ = w := by
    intro w hw
    have hcomm : v * w = w * v :=
      congrArg Subtype.val (mul_comm' (⟨v, hv⟩ : W) ⟨w, hw⟩)
    calc v * w * v⁻¹ = (w * v) * v⁻¹ := by rw [hcomm]
      _ = w := by group
  have hzpow : z ^ j = 1 ∨ z ^ j = z := by
    rcases Int.even_or_odd' j with ⟨m, hm | hm⟩
    · left
      rw [hm, zpow_mul, zpow_two, h.hyp.z_sq, one_zpow]
    · right
      rw [hm, zpow_add, zpow_mul, zpow_two, h.hyp.z_sq, one_zpow, one_mul, zpow_one]
  rcases hzpow with h1 | hz
  · left
    intro w hw
    simpa [h1] using hvfix w hw
  · right
    intro w hw
    rw [hz]
    have hzwW : z * w * z⁻¹ ∈ W := (mem_normalizer_iff.1 hzW w).1 hw
    calc (v * z) * w * (v * z)⁻¹ = v * (z * w * z⁻¹) * v⁻¹ := by group
      _ = z * w * z⁻¹ := hvfix (z * w * z⁻¹) hzwW

theorem WHyp.exists_mem_M_of_commute (h : WHyp G L A T z t W W₁ W₂) {n : G}
    (hn : n ∈ normalizer (W : Set G))
    (hc : ∀ w ∈ W, n * (z * w * z⁻¹) * n⁻¹ = z * (n * w * n⁻¹) * z⁻¹) :
    ∃ m ∈ M A z, ∀ w ∈ W, n * w * n⁻¹ = m * w * m⁻¹ := by
  classical
  let C : Subgroup G := centralizer (W : Set G)
  let E : Subgroup G := C ⊔ zpowers z
  have hzW : z ∈ normalizer (W : Set G) := h.z_mem_normalizer
  have hzC : z ∈ normalizer (C : Set G) :=
    CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer W hzW
  have hnC : n ∈ normalizer (C : Set G) :=
    CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer W hn
  have hWcent : W ≤ C := by
    haveI : IsMulCommutative ↥W := h.elemAb.toIsMulCommutative
    exact Subgroup.le_centralizer (H := W)
  have hEC : E ≤ centralizer (A : Set G) :=
    sup_le (Subgroup.centralizer_le h.e3.A_le) h.hyp.zpowers_le_centralizer_A
  have hRE : R₀ A z ≤ E := by
    rw [h.R₀_eq]
    exact sup_le (hWcent.trans le_sup_left) le_sup_right
  have heC : n * z * n⁻¹ * z⁻¹ ∈ C := by
    rw [mem_centralizer_iff]
    intro w hw
    have hzw : z⁻¹ * w * z ∈ W := (mem_normalizer_iff''.1 hzW w).1 hw
    have hxW : n⁻¹ * (z⁻¹ * w * z) * n ∈ W := (mem_normalizer_iff''.1 hn _).1 hzw
    have hc' := hc (n⁻¹ * (z⁻¹ * w * z) * n) hxW
    have hew : (n * z * n⁻¹ * z⁻¹) * w * (n * z * n⁻¹ * z⁻¹)⁻¹ = w := by
      calc (n * z * n⁻¹ * z⁻¹) * w * (n * z * n⁻¹ * z⁻¹)⁻¹
          = n * (z * (n⁻¹ * (z⁻¹ * w * z) * n) * z⁻¹) * n⁻¹ := by group
        _ = z * (n * (n⁻¹ * (z⁻¹ * w * z) * n) * n⁻¹) * z⁻¹ := hc'
        _ = w := by group
    calc w * (n * z * n⁻¹ * z⁻¹)
        = ((n * z * n⁻¹ * z⁻¹) * w * (n * z * n⁻¹ * z⁻¹)⁻¹) *
            (n * z * n⁻¹ * z⁻¹) := by rw [hew]
      _ = (n * z * n⁻¹ * z⁻¹) * w := by group
  have hnzE : n * z * n⁻¹ ∈ E := by
    have h1 : n * z * n⁻¹ = (n * z * n⁻¹ * z⁻¹) * z := by group
    rw [h1]
    exact mul_mem_sup heC (mem_zpowers z)
  have hmapC : C.map (MulAut.conj n).toMonoidHom ≤ C := by
    have h' := Subgroup.map_centralizer_le_centralizer_image (s := (W : Set G))
      (f := (MulAut.conj n).toMonoidHom)
    have himg : (MulAut.conj n).toMonoidHom '' (W : Set G) = W :=
      Subgroup.mem_normalizer_iff_conj_image_eq.1 hn
    rwa [himg] at h'
  have hmapE : E.map (MulAut.conj n).toMonoidHom ≤ E := by
    change (C ⊔ zpowers z).map (MulAut.conj n).toMonoidHom ≤ C ⊔ zpowers z
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le (hmapC.trans le_sup_left) ?_
    simpa using zpowers_le.2 hnzE
  have hPE : (R₀ A z).map (MulAut.conj n).toMonoidHom ≤ E :=
    (Subgroup.map_mono hRE).trans hmapE
  have hP : IsPGroup 2 ↥((R₀ A z).map (MulAut.conj n).toMonoidHom) := by
    refine IsPGroup.of_card (n := 21) ?_
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj n).toMonoidHom)
      (MulAut.conj n).injective, h.e2.card_R₀]
  obtain ⟨x, hxE, hxP⟩ :=
    h.exists_conj_le_R₀_of_le (H := E) (P := (R₀ A z).map (MulAut.conj n).toMonoidHom)
      hRE hEC hP hPE
  let Q : Subgroup G := (R₀ A z).map (MulAut.conj (x * n)).toMonoidHom
  have hQle : Q ≤ R₀ A z := by
    rintro _ ⟨r, hr, rfl⟩
    have hp : n * r * n⁻¹ ∈ (R₀ A z).map (MulAut.conj n).toMonoidHom := ⟨r, hr, rfl⟩
    have hmem := hxP (n * r * n⁻¹) hp
    simpa [Q, mul_assoc] using hmem
  have hQcard : Nat.card Q = 2 ^ 21 := by
    change Nat.card ↥((R₀ A z).map (MulAut.conj (x * n)).toMonoidHom) = 2 ^ 21
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj (x * n)).toMonoidHom)
      (MulAut.conj (x * n)).injective, h.e2.card_R₀]
  have hQeq : Q = R₀ A z :=
    Subgroup.eq_of_le_of_card_ge hQle (by rw [hQcard, h.e2.card_R₀])
  have hxnN : x * n ∈ normalizer (R₀ A z : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 (by simpa [Q] using hQeq)
  have hxnM : x * n ∈ M A z := h.normalizer_R₀_le hxnN
  have hxE' : x ∈ (C : Set G) * (zpowers z : Set G) := by
    have hcoe : (↑(C ⊔ zpowers z) : Set G) = (C : Set G) * (zpowers z : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left C (zpowers z) (zpowers_le.2 hzC)
    rw [← hcoe]
    exact hxE
  obtain ⟨c, hc, k, hk, hxck⟩ := hxE'
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have hzR : z ∈ R₀ A z := h.hyp.B_le_R₀ (mem_sup_right (mem_zpowers z))
  have hzM : z ∈ M A z := hzR.1
  refine ⟨z ^ (-j) * (x * n), mul_mem ((M A z).zpow_mem hzM (-j)) hxnM, ?_⟩
  intro w hw
  have hdC : z ^ (-j) * c * z ^ j ∈ C := by
    have hzpowN : z ^ (-j) ∈ normalizer (C : Set G) := (normalizer (C : Set G)).zpow_mem hzC (-j)
    have hmem := (mem_normalizer_iff.1 hzpowN c).1 hc
    simpa using hmem
  have hnw : n * w * n⁻¹ ∈ W := (mem_normalizer_iff.1 hn w).1 hw
  have hdcomm : (z ^ (-j) * c * z ^ j) * (n * w * n⁻¹) =
      (n * w * n⁻¹) * (z ^ (-j) * c * z ^ j) :=
    (mem_centralizer_iff.1 hdC (n * w * n⁻¹) hnw).symm
  have hm_eq : z ^ (-j) * (x * n) = (z ^ (-j) * c * z ^ j) * n := by
    rw [← hxck]
    group
  calc n * w * n⁻¹
      = (z ^ (-j) * c * z ^ j) * (n * w * n⁻¹) * (z ^ (-j) * c * z ^ j)⁻¹ := by
          rw [hdcomm]
          group
    _ = (z ^ (-j) * (x * n)) * w * (z ^ (-j) * (x * n))⁻¹ := by
          rw [hm_eq]
          group

theorem WHyp.exists_mem_M_of_mem_centralizer (h : WHyp G L A T z t W W₁ W₂) {n : G}
    (hn : n ∈ normalizer (W : Set G)) (hnA : n ∈ centralizer (A : Set G)) :
    ∃ m ∈ M A z, ∀ w ∈ W, n * w * n⁻¹ = m * w * m⁻¹ := by
  classical
  haveI : IsMulCommutative ↥W := h.elemAb.toIsMulCommutative
  let s : G := n * z * n⁻¹
  have hzA : z ∈ centralizer (A : Set G) :=
    h.hyp.zpowers_le_centralizer_A (mem_zpowers z)
  have hsN : s ∈ normalizer (W : Set G) :=
    mul_mem (mul_mem hn h.z_mem_normalizer) (inv_mem hn)
  have hsA : s ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    have ha' : n⁻¹ * a * n ∈ A := by
      have hcomm : a * n = n * a := mem_centralizer_iff.1 hnA a ha
      have heq : n⁻¹ * a * n = a := by
        calc n⁻¹ * a * n = n⁻¹ * (a * n) := by group
          _ = n⁻¹ * (n * a) := by rw [hcomm]
          _ = a := by group
      rwa [heq]
    have hzfix : z * (n⁻¹ * a * n) * z⁻¹ = n⁻¹ * a * n := by
      have hcomm : (n⁻¹ * a * n) * z = z * (n⁻¹ * a * n) :=
        mem_centralizer_iff.1 hzA (n⁻¹ * a * n) ha'
      calc z * (n⁻¹ * a * n) * z⁻¹ = ((n⁻¹ * a * n) * z) * z⁻¹ := by rw [hcomm]
        _ = n⁻¹ * a * n := by group
    have hsfix : s * a * s⁻¹ = a := by
      calc s * a * s⁻¹ = n * (z * (n⁻¹ * a * n) * z⁻¹) * n⁻¹ := by
              simp only [s]
              group
        _ = n * (n⁻¹ * a * n) * n⁻¹ := by rw [hzfix]
        _ = a := by group
    calc a * s = (s * a * s⁻¹) * s := by rw [hsfix]
      _ = s * a := by group
  have hs2 : s * s = 1 := by
    calc s * s = n * (z * z) * n⁻¹ := by
          simp only [s]
          group
      _ = 1 := by rw [h.hyp.z_sq]; group
  have hsdiff : ∀ w ∈ W, s * w * s⁻¹ * w⁻¹ ∈ A := by
    intro w hw
    have hw' : n⁻¹ * w * n ∈ W := (mem_normalizer_iff''.1 hn w).1 hw
    have hdelta : z * (n⁻¹ * w * n) * z⁻¹ * (n⁻¹ * w * n)⁻¹ ∈ A := by
      have hmem := h.e2.delta_mem (r := n⁻¹ * w * n) (h.e3.le_R₀ hw')
      simpa [delta, h.hyp.z_inv, mul_assoc] using hmem
    have hfix : n * (z * (n⁻¹ * w * n) * z⁻¹ * (n⁻¹ * w * n)⁻¹) * n⁻¹ =
        z * (n⁻¹ * w * n) * z⁻¹ * (n⁻¹ * w * n)⁻¹ := by
      rw [show n * (z * (n⁻¹ * w * n) * z⁻¹ * (n⁻¹ * w * n)⁻¹) =
          (z * (n⁻¹ * w * n) * z⁻¹ * (n⁻¹ * w * n)⁻¹) * n from
        (mem_centralizer_iff.1 hnA _ hdelta).symm]
      group
    have heq : s * w * s⁻¹ * w⁻¹ =
        n * (z * (n⁻¹ * w * n) * z⁻¹ * (n⁻¹ * w * n)⁻¹) * n⁻¹ := by
      simp only [s]
      group
    rw [heq, hfix]
    exact hdelta
  have hzdiff : ∀ w ∈ W, z * w * z⁻¹ * w⁻¹ ∈ A := by
    intro w hw
    have hmem := h.e2.delta_mem (r := w) (h.e3.le_R₀ hw)
    simpa [delta, h.hyp.z_inv, mul_assoc] using hmem
  have hc_s : ∀ w ∈ W, s * (z * w * z⁻¹) * s⁻¹ = z * (s * w * s⁻¹) * z⁻¹ :=
    conj_mul_conj_eq_of_sub_mem h.e3.A_le hsA hzA hsdiff hzdiff
  obtain ⟨m, hmM, hmact⟩ := h.exists_mem_M_of_commute (n := s) hsN hc_s
  have hmA : m ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    have hsfix : s * a * s⁻¹ = a := by
      rw [show s * a = a * s from (mem_centralizer_iff.1 hsA a ha).symm]
      group
    have hmfix : m * a * m⁻¹ = a := by
      rw [← hmact a (h.e3.A_le ha)]
      exact hsfix
    calc a * m = (m * a * m⁻¹) * m := by rw [hmfix]
      _ = m * a := by group
  obtain ⟨r, hrR, x, hxLN, hmrx⟩ := h.hyp.exists_mul_of_mem_M h.e2 hmM
  have hrC : r ∈ centralizer (A : Set G) := hrR.2
  have hxC : x ∈ centralizer (A : Set G) := by
    have h1 : r⁻¹ * m ∈ centralizer (A : Set G) := mul_mem (inv_mem hrC) hmA
    have hx_eq : x = r⁻¹ * m := by rw [hmrx]; group
    rwa [hx_eq]
  have hxA : x ∈ A := by
    have h1 : x ∈ L ⊓ centralizer (A : Set G) := ⟨hxLN.1, hxC⟩
    rwa [h.hyp.jc.centralizer_eq] at h1
  have hxW : x ∈ centralizer (W : Set G) := by
    rw [mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val (mul_comm' (⟨w, hw⟩ : W) ⟨x, h.e3.A_le hxA⟩)
  have hmr : ∀ w ∈ W, m * w * m⁻¹ = r * w * r⁻¹ := by
    intro w hw
    have hxfix : x * w * x⁻¹ = w := by
      have hcomm : w * x = x * w := mem_centralizer_iff.1 hxW w hw
      calc x * w * x⁻¹ = (w * x) * x⁻¹ := by rw [← hcomm]
        _ = w := by group
    rw [hmrx]
    calc (r * x) * w * (r * x)⁻¹ = r * (x * w * x⁻¹) * r⁻¹ := by group
      _ = r * w * r⁻¹ := by rw [hxfix]
  have hsr : ∀ w ∈ W, s * w * s⁻¹ = r * w * r⁻¹ := by
    intro w hw
    rw [hmact w hw, hmr w hw]
  rcases h.conj_eq_one_or_conj_z hrR with hr1 | hrz
  · exfalso
    have hscent : s ∈ centralizer (W : Set G) := by
      rw [mem_centralizer_iff]
      intro w hw
      have h := hsr w hw
      rw [hr1 w hw] at h
      calc w * s = (s * w * s⁻¹) * s := by rw [h]
        _ = s * w := by group
    have hnC : n ∈ normalizer (centralizer (W : Set G) : Set G) :=
      CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer W hn
    have hzC : z ∈ centralizer (W : Set G) := by
      have hz_eq : z = n⁻¹ * s * n := by
        simp only [s]
        group
      have h1 : n⁻¹ * s * n ∈ centralizer (W : Set G) := by
        simpa using (mem_normalizer_iff.1 (inv_mem hnC) s).1 hscent
      rwa [← hz_eq] at h1
    have hWA : W ≤ A := by
      intro w hw
      rw [h.mem_A_iff hw]
      exact (mem_centralizer_iff.1 hzC w hw).symm
    have hEq : A = W := le_antisymm h.e3.A_le hWA
    have hcard : Nat.card A = Nat.card W := by rw [hEq]
    rw [h.hyp.jc.module.card, h.e3.card] at hcard
    norm_num at hcard
  · have hc_n : ∀ w ∈ W, n * (z * w * z⁻¹) * n⁻¹ = z * (n * w * n⁻¹) * z⁻¹ := by
      intro w hw
      have hnw : n * w * n⁻¹ ∈ W := (mem_normalizer_iff.1 hn w).1 hw
      have h1 : s * (n * w * n⁻¹) * s⁻¹ = z * (n * w * n⁻¹) * z⁻¹ := by
        rw [hsr (n * w * n⁻¹) hnw, hrz (n * w * n⁻¹) hnw]
      calc n * (z * w * z⁻¹) * n⁻¹ = s * (n * w * n⁻¹) * s⁻¹ := by
            simp only [s]
            group
        _ = z * (n * w * n⁻¹) * z⁻¹ := h1
    exact h.exists_mem_M_of_commute hn hc_n

theorem WHyp.exists_mem_M_of_normalizes (h : WHyp G L A T z t W W₁ W₂)
    (hA : ∀ n ∈ normalizer (W : Set G), ∀ a ∈ A, n * a * n⁻¹ ∈ A) {n : G}
    (hn : n ∈ normalizer (W : Set G)) :
    ∃ m ∈ M A z, ∀ w ∈ W, n * w * n⁻¹ = m * w * m⁻¹ := by
  classical
  let D : Subgroup G := normalizer (W : Set G) ⊓ centralizer (A : Set G)
  let s : G := n * z * n⁻¹
  have hRD : R₀ A z ≤ D :=
    le_inf (inf_le_left.trans h.e3.M_le) inf_le_right
  have hDC : D ≤ centralizer (A : Set G) := inf_le_right
  have hnN : n ∈ normalizer (A : Set G) := by
    rw [mem_normalizer_iff]
    intro a
    exact ⟨hA n hn a, fun ha => by
      have h := hA n⁻¹ (inv_mem hn) (n * a * n⁻¹) ha
      have h' : n⁻¹ * (n * a * n⁻¹) * n ∈ A := by simpa only [inv_inv] using h
      have heq : n⁻¹ * (n * a * n⁻¹) * n = a := by group
      rwa [heq] at h'⟩
  have hzA : z ∈ centralizer (A : Set G) :=
    h.hyp.zpowers_le_centralizer_A (mem_zpowers z)
  have hsN : s ∈ normalizer (W : Set G) :=
    mul_mem (mul_mem hn h.z_mem_normalizer) (inv_mem hn)
  have hsC : s ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    have ha' : n⁻¹ * a * n ∈ A := (mem_normalizer_iff''.1 hnN a).1 ha
    have hzfix : z * (n⁻¹ * a * n) * z⁻¹ = n⁻¹ * a * n := by
      have hcomm : (n⁻¹ * a * n) * z = z * (n⁻¹ * a * n) :=
        mem_centralizer_iff.1 hzA (n⁻¹ * a * n) ha'
      calc z * (n⁻¹ * a * n) * z⁻¹ = ((n⁻¹ * a * n) * z) * z⁻¹ := by rw [hcomm]
        _ = n⁻¹ * a * n := by group
    have hsfix : s * a * s⁻¹ = a := by
      calc s * a * s⁻¹ = n * (z * (n⁻¹ * a * n) * z⁻¹) * n⁻¹ := by
              simp only [s]
              group
        _ = n * (n⁻¹ * a * n) * n⁻¹ := by rw [hzfix]
        _ = a := by group
    calc a * s = (s * a * s⁻¹) * s := by rw [hsfix]
      _ = s * a := by group
  have hs2 : s * s = 1 := by
    calc s * s = n * (z * z) * n⁻¹ := by
          simp only [s]
          group
      _ = 1 := by rw [h.hyp.z_sq]; group
  have hElem : IsElementaryAbelian 2 ↥(zpowers s) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) (by rw [pow_two]; exact hs2)
  have hP : IsPGroup 2 ↥(zpowers s) := hElem.isPGroup 2 ↥(zpowers s)
  have hPD : zpowers s ≤ D := zpowers_le.2 ⟨hsN, hsC⟩
  obtain ⟨x, hxD, hxconj⟩ :=
    h.exists_conj_le_R₀_of_le (H := D) (P := zpowers s) hRD hDC hP hPD
  have hxN : x ∈ normalizer (W : Set G) := hxD.1
  have hxC : x ∈ centralizer (A : Set G) := hxD.2
  let r : G := x * s * x⁻¹
  have hrR : r ∈ R₀ A z := hxconj s (mem_zpowers s)
  have hrConj : IsConj z r := by
    refine isConj_iff.2 ⟨x * n, ?_⟩
    simp only [r, s]
    group
  have hrW : r ∉ W := fun hw => h.not_isConj hw hrConj
  have hr2 : r * r = 1 := by
    calc r * r = x * (s * s) * x⁻¹ := by
          simp only [r]
          group
      _ = 1 := by rw [hs2]; group
  have hzrA : z * r ∈ A := h.mul_mem_A_of_mul_self hrR hrW hr2
  have hxA : x ∈ normalizer (A : Set G) :=
    Subgroup.centralizer_le_normalizer (A : Set G) hxC
  have hyA : x * n ∈ normalizer (A : Set G) := mul_mem hxA hnN
  have hyzB : (x * n) * z * (x * n)⁻¹ ∈ B A z := by
    have h1 : (x * n) * z * (x * n)⁻¹ = z * (z * r) := by
      rw [show (x * n) * z * (x * n)⁻¹ = r from by
        simp only [r, s]
        group]
      calc r = (z * z) * r := by rw [h.hyp.z_sq, one_mul]
        _ = z * (z * r) := by group
    rw [h1]
    have hmem : z * (z * r) ∈ zpowers z ⊔ A :=
      mul_mem_sup (S := zpowers z) (T := A) (mem_zpowers z) hzrA
    rwa [sup_comm] at hmem
  have hmapA : A.map (MulAut.conj (x * n)).toMonoidHom ≤ A := by
    intro a ha
    rcases ha with ⟨b, hb, rfl⟩
    simpa [mul_assoc] using (mem_normalizer_iff.1 hyA b).1 hb
  have hmapZ : (zpowers z).map (MulAut.conj (x * n)).toMonoidHom ≤ B A z := by
    rw [MonoidHom.map_zpowers]
    simpa [mul_assoc] using zpowers_le.2 hyzB
  have hmapB : (B A z).map (MulAut.conj (x * n)).toMonoidHom ≤ B A z := by
    rw [show B A z = A ⊔ zpowers z from rfl, Subgroup.map_sup]
    exact sup_le (hmapA.trans le_sup_left) hmapZ
  have hcardB : Nat.card ((B A z).map (MulAut.conj (x * n)).toMonoidHom) =
      Nat.card (B A z) :=
    Subgroup.card_map_of_injective (f := (MulAut.conj (x * n)).toMonoidHom)
      (MulAut.conj (x * n)).injective
  have hBeq : (B A z).map (MulAut.conj (x * n)).toMonoidHom = B A z :=
    Subgroup.eq_of_le_of_card_ge hmapB (by rw [hcardB])
  have hyM : x * n ∈ M A z :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 hBeq
  obtain ⟨m', hm'M, hm'act⟩ :=
    h.exists_mem_M_of_mem_centralizer (n := x⁻¹) (inv_mem hxN) (inv_mem hxC)
  refine ⟨m' * (x * n), mul_mem hm'M hyM, ?_⟩
  intro w hw
  have hyw : (x * n) * w * (x * n)⁻¹ ∈ W :=
    (mem_normalizer_iff.1 (mul_mem hxN hn) w).1 hw
  have hxact := hm'act ((x * n) * w * (x * n)⁻¹) hyw
  calc n * w * n⁻¹ = x⁻¹ * ((x * n) * w * (x * n)⁻¹) * x := by
        rw [show n = x⁻¹ * (x * n) from by group]
        group
    _ = m' * ((x * n) * w * (x * n)⁻¹) * m'⁻¹ := by simpa using hxact
    _ = (m' * (x * n)) * w * (m' * (x * n))⁻¹ := by group

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
