module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.MFusionBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Step3b
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.YInterface

public section

namespace CFSG.EvenSporadicStandard.J4Std.MFusion

open Subgroup CFSG.EvenSporadicStandard.J4Std

variable {G : Type} [Group G] {L U T0 : Subgroup G} {z : G} {Y : Subgroup G}

theorem conj_mem_Csub (hS : Setting L z) (hD : LocalData L U T0)
    (htrans : ∀ u ∈ U, ∃ n ∈ Nsub U z, n * z * n⁻¹ = z * u) {n c : G} (hn : n ∈ Nsub U z)
    (hc : c ∈ Csub U z) : n * c * n⁻¹ ∈ Csub U z := by
  obtain ⟨hcN, hcU⟩ := mem_Csub.1 hc
  refine mem_Csub.2 ⟨mul_mem (mul_mem hn hcN) (inv_mem hn), fun u hu => ?_⟩
  have hu' : n⁻¹ * u * n ∈ U := by
    have := conj_U_mem hS hD htrans (inv_mem hn) hu
    rwa [inv_inv] at this
  have := hcU _ hu'
  calc n * c * n⁻¹ * u = n * (c * (n⁻¹ * u * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * u * n) * c) * n⁻¹ := by rw [this]
    _ = u * (n * c * n⁻¹) := by group

theorem z_mem_Csub (hS : Setting L z) (hD : LocalData L U T0) : z ∈ Csub U z :=
  V_le_Csub hS hD z_mem_V

theorem mem_normalizer_of_conj_mem [Finite G] (hW : WeakData U z Y) {g : G}
    (hg : ∀ y ∈ Y, g * y * g⁻¹ ∈ Csub U z) : g ∈ normalizer (Y : Set G) := by
  have hmem : ∀ a ∈ conjSub g Y, ∃ y ∈ Y, a = g * y * g⁻¹ := fun a ha =>
    ⟨g⁻¹ * a * g, mem_conjSub_iff.1 ha, by group⟩
  have hA : conjSub g Y = Y := by
    apply hW.unique_Y
    · intro a ha
      obtain ⟨y, hy, rfl⟩ := hmem a ha
      exact hg y hy
    · intro a ha
      obtain ⟨y, hy, rfl⟩ := hmem a ha
      calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
        _ = 1 := by rw [hW.Y_sq y hy]; group
    · intro a ha b hb
      obtain ⟨y, hy, rfl⟩ := hmem a ha
      obtain ⟨y', hy', rfl⟩ := hmem b hb
      calc g * y * g⁻¹ * (g * y' * g⁻¹) = g * (y * y') * g⁻¹ := by group
        _ = g * (y' * y) * g⁻¹ := by rw [hW.Y_comm y hy y' hy']
        _ = g * y' * g⁻¹ * (g * y * g⁻¹) := by group
    · rw [card_conjSub, hW.card_Y]
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have := conj_mem_conjSub (g := g) hx
    rwa [hA] at this
  · intro hx
    rw [← hA] at hx
    have := mem_conjSub_iff.1 hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this

theorem N_le_M [Finite G] (hS : Setting L z) (hD : LocalData L U T0)
    (htrans : ∀ u ∈ U, ∃ n ∈ Nsub U z, n * z * n⁻¹ = z * u) (hY : YStruct L U z Y)
    (hW : WeakData U z Y) : Nsub U z ≤ normalizer (Y : Set G) := fun _ hn =>
  mem_normalizer_of_conj_mem hW fun _ hy => conj_mem_Csub hS hD htrans hn (hY.le_W hy)

theorem mem_Nsub_of_normalizer_comm (hS : Setting L z) (hD : LocalData L U T0)
    (hW : WeakData U z Y) (hUY : U ≤ Y) {c : G} (hcM : c ∈ normalizer (Y : Set G))
    (hcz : c * z = z * c) : c ∈ Nsub U z := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  have key : ∀ d : G, d ∈ normalizer (Y : Set G) → d * z = z * d →
      ∀ u ∈ U, d * u * d⁻¹ ∈ U := by
    intro d hdM hdz u hu
    have hdY : d * u * d⁻¹ ∈ Y := (mem_normalizer_iff.1 hdM u).1 (hUY hu)
    apply hW.cent_Y _ hdY
    have hzu : z * u = u * z := hS.z_comm u (hUL hu)
    have hdz' : d⁻¹ * z = z * d⁻¹ := (Commute.inv_left (show Commute d z from hdz)).eq
    calc d * u * d⁻¹ * z = d * u * (d⁻¹ * z) := by group
      _ = d * u * (z * d⁻¹) := by rw [hdz']
      _ = d * (u * z) * d⁻¹ := by group
      _ = d * (z * u) * d⁻¹ := by rw [hzu]
      _ = (d * z) * u * d⁻¹ := by group
      _ = (z * d) * u * d⁻¹ := by rw [hdz]
      _ = z * (d * u * d⁻¹) := by group
  have hV : ∀ d : G, (∀ u ∈ U, d * u * d⁻¹ ∈ U) → d * z = z * d →
      ∀ x ∈ Vsub U z, d * x * d⁻¹ ∈ Vsub U z := by
    intro d hdU hdz x hx
    obtain ⟨u, hu, hxu⟩ := (mem_Vsub_iff hS hUL).1 hx
    rcases hxu with rfl | rfl
    · exact U_le_V (hdU x hu)
    · have : d * (z * u) * d⁻¹ = z * (d * u * d⁻¹) := by
        calc d * (z * u) * d⁻¹ = (d * z) * u * d⁻¹ := by group
          _ = z * d * u * d⁻¹ := by rw [hdz]
          _ = z * (d * u * d⁻¹) := by group
      rw [this]
      exact mul_mem z_mem_V (U_le_V (hdU u hu))
  have hcz' : c⁻¹ * z = z * c⁻¹ := (Commute.inv_left (show Commute c z from hcz)).eq
  rw [Nsub, mem_normalizer_iff]
  intro x
  refine ⟨hV c (key c hcM hcz) hcz x, fun hx => ?_⟩
  have := hV c⁻¹ (key c⁻¹ (inv_mem hcM) hcz') hcz' _ hx
  rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at this

theorem cent_le_N [Finite G] (hS : Setting L z) (hD : LocalData L U T0)
    (htrans : ∀ u ∈ U, ∃ n ∈ Nsub U z, n * z * n⁻¹ = z * u) (hY : YStruct L U z Y)
    (hW : WeakData U z Y) {m : G} (hm : m ∈ normalizer (Y : Set G)) {y : G} (hy : y ∈ Y)
    (hmz : m * z * m⁻¹ = z * y) : m ∈ Nsub U z := by
  have hconjW : m * z * m⁻¹ ∈ Csub U z := by
    rw [hmz]
    exact mul_mem (z_mem_Csub hS hD) (hY.le_W hy)
  obtain ⟨u', hu', hmu'⟩ := hW.conj_W m hconjW
  have hyu : y = u' := mul_left_cancel (hmz.symm.trans hmu')
  obtain ⟨w, hw, hwz⟩ := hW.z_conj_W u' hu'
  have hwN : w ∈ Nsub U z := (mem_Csub.1 hw).1
  have hwM : w ∈ normalizer (Y : Set G) := N_le_M hS hD htrans hY hW hwN
  have hcM : w⁻¹ * m ∈ normalizer (Y : Set G) := mul_mem (inv_mem hwM) hm
  have hcz : w⁻¹ * m * z = z * (w⁻¹ * m) := by
    have h1 : w⁻¹ * m * z * (w⁻¹ * m)⁻¹ = z := by
      calc w⁻¹ * m * z * (w⁻¹ * m)⁻¹ = w⁻¹ * (m * z * m⁻¹) * w := by group
        _ = w⁻¹ * (z * u') * w := by rw [hmz, hyu]
        _ = w⁻¹ * (w * z * w⁻¹) * w := by rw [hwz]
        _ = z := by group
    calc w⁻¹ * m * z = (w⁻¹ * m * z * (w⁻¹ * m)⁻¹) * (w⁻¹ * m) := by group
      _ = z * (w⁻¹ * m) := by rw [h1]
  have hcN := mem_Nsub_of_normalizer_comm hS hD hW hY.U_le hcM hcz
  have : m = w * (w⁻¹ * m) := by group
  rw [this]
  exact mul_mem hwN hcN

theorem N_eq (hS : Setting L z) (hD : LocalData L U T0) (hW : WeakData U z Y) {n : G}
    (hn : n ∈ Nsub U z) : ∃ w ∈ Csub U z, ∃ h ∈ Hloc L U, n = w * h := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  obtain ⟨u, hu, hnz⟩ := conj_eq_mul_of_N hS hUL hn
  obtain ⟨w, hw, hwz⟩ := hW.z_conj_W u hu
  have hwN : w ∈ Nsub U z := (mem_Csub.1 hw).1
  have hcN : w⁻¹ * n ∈ Nsub U z := mul_mem (inv_mem hwN) hn
  have hcz : w⁻¹ * n * z = z * (w⁻¹ * n) := by
    have h1 : w⁻¹ * n * z * (w⁻¹ * n)⁻¹ = z := by
      calc w⁻¹ * n * z * (w⁻¹ * n)⁻¹ = w⁻¹ * (n * z * n⁻¹) * w := by group
        _ = w⁻¹ * (z * u) * w := by rw [hnz]
        _ = w⁻¹ * (w * z * w⁻¹) * w := by rw [hwz]
        _ = z := by group
    calc w⁻¹ * n * z = (w⁻¹ * n * z * (w⁻¹ * n)⁻¹) * (w⁻¹ * n) := by group
      _ = z * (w⁻¹ * n) := by rw [h1]
  have hmem : w⁻¹ * n ∈ Nsub U z ⊓ centralizer ({z} : Set G) :=
    mem_inf.2 ⟨hcN, mem_centralizer_singleton_iff.2 hcz⟩
  rw [N_inf_centralizer_eq hS hUL] at hmem
  obtain ⟨h, hh, hcases⟩ := (mem_Vsub_iff hS Hloc_le_L).1 hmem
  rcases hcases with hc | hc
  · exact ⟨w, hw, h, hh, by rw [← hc]; group⟩
  · refine ⟨w * z, mul_mem hw (z_mem_Csub hS hD), h, hh, ?_⟩
    calc n = w * (w⁻¹ * n) := by group
      _ = w * (z * h) := by rw [hc]
      _ = w * z * h := by group

end CFSG.EvenSporadicStandard.J4Std.MFusion
