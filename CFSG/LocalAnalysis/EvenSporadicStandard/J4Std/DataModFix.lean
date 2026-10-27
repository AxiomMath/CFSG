module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataModBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataModMap
public import Certificates.Certificate25140
public import CFSG.Sporadic.J4

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataMod

open Subgroup CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem chkFixRoot_spec {r : ℕ} (h : chkFixRoot r = true) :
    (∀ s ∈ fixWords r, (∀ ℓ ∈ s, ℓ ∈ letters) ∧ s.foldr act r = r) ∧
      ∀ d < 2048, (∀ s ∈ fixWords r, s.foldr act d < 2048) ∧
        ((∀ s ∈ fixWords r, s.foldr act d = d) → d = 0 ∨ d = r) := by
  unfold chkFixRoot at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.contains_iff_mem, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun s hs => h1 s hs, fun d hd => ?_⟩
  obtain ⟨h3, h4⟩ := h2 d hd
  refine ⟨h3, fun hfix => ?_⟩
  rcases h4 with (h4 | h4) | h4
  · exfalso
    have hall : (fixWords r).all (fun s => s.foldr act d == d) = true :=
      List.all_eq_true.2 fun s hs => beq_iff_eq.2 (hfix s hs)
    rw [hall] at h4
    exact absurd h4 (by decide)
  · exact Or.inl h4
  · exact Or.inr h4

theorem chkFix_spec {r : ℕ} (hr : r = 1 ∨ r = 3) :
    (∀ s ∈ fixWords r, (∀ ℓ ∈ s, ℓ ∈ letters) ∧ s.foldr act r = r) ∧
      ∀ d < 2048, (∀ s ∈ fixWords r, s.foldr act d < 2048) ∧
        ((∀ s ∈ fixWords r, s.foldr act d = d) → d = 0 ∨ d = r) := by
  have h := Certificates.certificate25140
  unfold chkFix at h
  rw [Bool.and_eq_true] at h
  rcases hr with rfl | rfl
  · exact chkFixRoot_spec h.1
  · exact chkFixRoot_spec h.2

theorem fixData_J :
    FixData (⊤ : Subgroup J) (Eg uJ 11) := by
  have hF := j4Facts
  have hM := hF.mat
  intro x hx hx1 w hw hfix
  obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hx
  have hc0 : c ≠ 0 := fun h0 => hx1 (by rw [h0, eta_zero])
  obtain ⟨r, hr, k, hk, hkr⟩ := exists_Hconj_root hM hc0 hc
  obtain ⟨hfixr, hall⟩ := chkFix_spec hr
  have hw' : k⁻¹ * w * k ∈ Eg uJ 11 := by
    have := Hj_normalizes_Eg hM k⁻¹ (Hj.inv_mem hk) w hw
    simpa using this
  obtain ⟨d, hd, hdeq⟩ := (mem_Eg_iff (elem_uJ hM)).1 hw'
  have hfixd : ∀ s ∈ fixWords r, s.foldr act d = d := by
    intro s hs
    obtain ⟨hsL, hsr⟩ := hfixr s hs
    have hS : wordProd xJ s ∈ Hj := wordProd_mem_Hj hsL
    have h1 : (k * wordProd xJ s * k⁻¹) * eta uJ 11 c * (k * wordProd xJ s * k⁻¹)⁻¹ =
        eta uJ 11 c := by
      have e : (k * wordProd xJ s * k⁻¹) * eta uJ 11 c * (k * wordProd xJ s * k⁻¹)⁻¹ =
          k * (wordProd xJ s * (k⁻¹ * eta uJ 11 c * k) * (wordProd xJ s)⁻¹) * k⁻¹ := by group
      have e2 : k⁻¹ * eta uJ 11 c * k = eta uJ 11 r := by rw [← hkr]; group
      rw [e, e2, wordProd_conj hM hsL, hsr]
      exact hkr
    have h2 := hfix _ ((mem_Hloc_top hF).2 (Hj.mul_mem (Hj.mul_mem hk hS) (Hj.inv_mem hk))) h1
    have h3 : wordProd xJ s * eta uJ 11 d * (wordProd xJ s)⁻¹ = eta uJ 11 d := by
      rw [← hdeq]
      have e : wordProd xJ s * (k⁻¹ * w * k) * (wordProd xJ s)⁻¹ =
          k⁻¹ * ((k * wordProd xJ s * k⁻¹) * w * (k * wordProd xJ s * k⁻¹)⁻¹) * k := by group
      rw [e, h2]
    rw [wordProd_conj hM hsL] at h3
    exact eta_inj hM _ ((hall d hd).1 s hs) d hd h3
  rcases (hall d hd).2 hfixd with h0 | h0
  · left
    rw [h0, eta_zero] at hdeq
    calc w = k * (k⁻¹ * w * k) * k⁻¹ := by group
      _ = 1 := by rw [hdeq]; group
  · right
    rw [h0] at hdeq
    calc w = k * (k⁻¹ * w * k) * k⁻¹ := by group
      _ = eta uJ 11 c := by rw [hdeq]; exact hkr

end CFSG.EvenSporadicStandard.J4Std.DataMod

namespace CFSG.EvenSporadicStandard.J4Std

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem fixData_J4
    {G : Type} [Group G] (ι : J →* G)
    (hι : Function.Injective ι) : FixData ι.range ((Eg uJ 11).map ι) :=
  DataMod.fixData_map ι hι _ DataMod.fixData_J

end CFSG.EvenSporadicStandard.J4Std
