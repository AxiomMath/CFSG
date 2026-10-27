module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NPStep5
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.TopStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.LitCompBInner

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
open CFSG.EvenSporadicStandard.HSStd

namespace NPSetting

section Step6

variable {G : Type} [Group G] [Finite G] {X : Subgroup G} {u x : G} {h s : G}

theorem exists_conj_h_u (hNP : KDNP) (h15 : FS79Lemma15Sec G) (hh : IsNPCentralLift X u x h)
    (hS : NPSetting G X u x (zpowers h) s) : ∃ c : G, h = c * u * c⁻¹ := by
  have hx2 : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hS.xinv, pow_two] at h
  have hx_ne : x ≠ 1 := by
    rintro rfl
    exact (by norm_num : (1 : ℕ) ≠ 2) (by simpa using hS.xinv)
  have hxhat_mem : s * x * s⁻¹ ∈ jOf X x := by
    rw [← hS.map_conj_A]
    exact Subgroup.mem_map.2 ⟨x, hS.x_mem_A hNP h15 hh, by simp [MulAut.conj_apply]⟩
  have hxhat_ne : s * x * s⁻¹ ≠ 1 := by
    intro h
    refine hx_ne ((MulAut.conj s).injective ?_)
    have h1 : (MulAut.conj s) x = 1 := by simpa [MulAut.conj_apply] using h
    rw [h1, map_one]
  have hxhat_sq : (s * x * s⁻¹) * (s * x * s⁻¹) = 1 := by
    have h1 : (MulAut.conj s) x * (MulAut.conj s) x = 1 := by
      rw [← map_mul, hx2, map_one]
    simpa [MulAut.conj_apply] using h1
  obtain ⟨k, hkX, hkx, -⟩ :=
    hS.facts.G5 (s * x * s⁻¹) hxhat_mem hxhat_ne hxhat_sq
  have hku : k * u = u * k := mem_centralizer_iff.1 hS.out.mem k hkX
  have hsh : s * h * s⁻¹ = h :=
    hS.s_mul_h (hS.mul_self_central_lift hNP h15 hh) hh.ne_one
  have hu_eq : u = h * x := by
    rw [hS.h_eq_mul hNP h15 hh, mul_assoc, hx2, mul_one]
  have hsu : s * u * s⁻¹ = h * (s * x * s⁻¹) := by
    rw [hu_eq]
    calc s * (h * x) * s⁻¹ = (s * h * s⁻¹) * (s * x * s⁻¹) := by group
      _ = h * (s * x * s⁻¹) := by rw [hsh]
  have hkh : k * h * k⁻¹ = h * (s * x * s⁻¹) := by
    have h1 : k * h * k⁻¹ = u * (k * x * k⁻¹) := by
      rw [hS.h_eq_mul hNP h15 hh]
      calc k * (u * x) * k⁻¹ = (k * u) * x * k⁻¹ := by group
        _ = (u * k) * x * k⁻¹ := by rw [hku]
        _ = u * (k * x * k⁻¹) := by group
    rw [h1, hkx, ← mul_assoc, ← hS.h_eq_mul hNP h15 hh]
  have hkey : k * h * k⁻¹ = s * u * s⁻¹ := by rw [hkh, hsu]
  have hh_eq : h = k⁻¹ * (s * u * s⁻¹) * k := by
    rw [← hkey]
    group
  exact ⟨k⁻¹ * s, by rw [hh_eq]; group⟩

theorem dvd_card_centralizer (hh : IsNPCentralLift X u x h)
    (hS : NPSetting G X u x (zpowers h) s) :
    3600 ∣ Nat.card ↥(centralizer ({h} : Set G)) := by
  have hc : ∀ a ∈ jOf X x, ∀ b ∈ npA X x s, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.1 (hS.A_le_D hb)) a ha
  have hinf : jOf X x ⊓ npA X x s = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact Subgroup.mem_bot.2 (hS.facts.J_center z hz.1 fun j' hj' =>
      ((mem_centralizer_iff.1 (hS.A_le_D hz.2)) j' hj').symm)
  have hA : jOf X x ≤ centralizer ({h} : Set G) := by
    intro j hj
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 hh.mem_D) j hj
  have hB : npA X x s ≤ centralizer ({h} : Set G) := hS.isCompIn_A_centralizer.1
  have h := card_mul_card_dvd_of_commute hc hinf hA hB
  rw [hS.facts.card_J, hS.card_A] at h
  norm_num at h
  exact h

theorem false_of_normalized (hNP : KDNP) (h15 : FS79Lemma15Sec G)
    (hcard : Nat.card ↥(centralizer ({u} : Set G)) = 380160) (hh : IsNPCentralLift X u x h)
    (hS : NPSetting G X u x (zpowers h) s) : False := by
  obtain ⟨c, hc⟩ := hS.exists_conj_h_u hNP h15 hh
  have h1 := hS.dvd_card_centralizer hh
  rw [hc, card_centralizer_conj, hcard] at h1
  omega

theorem false_of_setting {T₀ : Subgroup G} {s₀ : G} (hNP : KDNP) (h15 : FS79Lemma15Sec G)
    (hcard : Nat.card ↥(centralizer ({u} : Set G)) = 380160)
    (hS : NPSetting G X u x T₀ s₀) : False := by
  obtain ⟨h, s, hh, hS'⟩ := hS.exists_normalized hNP h15
  exact hS'.false_of_normalized hNP h15 hcard hh

end Step6

end NPSetting

section Export

variable {G : Type} [Group G] [Finite G]

theorem not_fiveALink_into (hNP : KDNP) (hUG : Induction.Balance.UHered G)
    {X : Subgroup G} {u x : G} (hO : Out G X u) (hxX : x ∈ X) (hx2 : orderOf x = 2)
    (hx240 : Nat.card ↥(X ⊓ centralizer ({x} : Set G)) = 240)
    (hcent : X ⊓ centralizer (jOf X x : Set G) = zpowers x)
    (hF : PropA.Facts X u x) (hR : RbcFacts X u x) (L' : Subgroup G) :
    ¬ FiveALink (jOf X x) L' := by
  intro hL
  obtain ⟨T₀, s₀, hS⟩ := npSetting_of_fiveALink hO hxX hx2 hx240 hcent hF hR hL
  exact hS.false_of_setting hNP
    (fun Y _ _ hY => Induction.fs79Lemma15At_of_uhered Y (hUG.of_section hY)) hO.card_centralizer

end Export

end CFSG.EvenSporadicStandard.M12Std.Rbc
