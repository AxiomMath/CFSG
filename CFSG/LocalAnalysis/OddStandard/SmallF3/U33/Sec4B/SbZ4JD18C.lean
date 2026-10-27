module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD18B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD14B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD15

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

private lemma inv_comm_mem_V (hZ : ∀ m ∈ Mc, m ∉ Q → m * m ∉ Y)
    {m₀ : H} (hm₀ : m₀ ∈ Mc) (hm₀Q : m₀ ∉ Q) {u : H} (hu : u ∈ Mc)
    (hu2 : u * u = 1) (hcomm : m₀ * τ * u = u * (m₀ * τ)) : u ∈ V := by
  have huQ : u ∈ Q := by
    by_contra huQ
    exact (hZ u hu huQ) (by rw [hu2]; exact Y.one_mem)
  have huY : u ∈ Y := h.Y_mem u huQ hu2
  have hτu : τ * u = u * τ := tau_comm_Y h hMh hMc huY
  have hm₀u : m₀ * u = u * m₀ := by
    have h : m₀ * u * τ = u * m₀ * τ := by
      calc m₀ * u * τ = m₀ * (u * τ) := by group
        _ = m₀ * (τ * u) := by rw [← hτu]
        _ = m₀ * τ * u := by group
        _ = u * (m₀ * τ) := hcomm
        _ = u * m₀ * τ := by group
    exact mul_right_cancel h
  exact cent_Y_eq_V h hMh hMc hm₀ hm₀Q huY hm₀u.symm

theorem card_inv_D_le (hb : ZJBound t) (hZ : ∀ m ∈ Mc, m ∉ Q → m * m ∉ Y)
    (hK : ∀ x ∈ Mc, x ∉ Q → x * x ∉ Q ⊓ centralizer ({t * τ} : Set H))
    {T : H → Prop} (hT : ZJClass T Q t τ l) {m₀ : H} (hm₀ : m₀ ∈ Mc) (hm₀Q : m₀ ∉ Q)
    (hβ : m₀ * τ * (m₀ * τ) = 1) (hTβ : T (m₀ * τ)) :
    {x : H | x ∈ zjVh Mc t τ l ⊓ centralizer ({m₀ * τ} : Set H) ⊓ centralizer (V : Set H) ∧
      x * x = 1}.ncard ≤ 8 := by
  let S : Set H := {x : H | x ∈ zjVh Mc t τ l ⊓ centralizer ({m₀ * τ} : Set H) ⊓
    centralizer (V : Set H) ∧ x * x = 1}
  change S.ncard ≤ 8
  have hVcard : (V : Set H).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact h.card_V
  have hSsub : S ⊆ (V : Set H) ∪ (fun v => v * (m₀ * τ)) '' (V : Set H) := by
    intro x hx
    rcases hx with ⟨hxmem, hx2⟩
    obtain ⟨hxVhβ, hxCV⟩ := Subgroup.mem_inf.mp hxmem
    obtain ⟨hxVh, hxCβ⟩ := Subgroup.mem_inf.mp hxVhβ
    have hβx : (m₀ * τ) * x = x * (m₀ * τ) :=
      (Subgroup.mem_centralizer_singleton_iff.mp hxCβ).symm
    have hxVhV : x ∈ zjVh Mc t τ l ⊓ centralizer (V : Set H) := ⟨hxVh, hxCV⟩
    rw [cent_V_Vh h hMh hMc] at hxVhV
    obtain ⟨m, hm, hx_eq⟩ := (mem_McTT_iff h hMh hMc).mp hxVhV
    rcases hx_eq with hxm | hxmt | hxmτ | hxmtτ
    · left
      rw [hxm]
      exact inv_comm_mem_V h hMh hMc hZ hm₀ hm₀Q hm (by rw [← hxm]; exact hx2)
        (by rw [← hxm]; exact hβx)
    · exfalso
      have hd2 : m * t * (m * t) = 1 := by rw [← hxmt]; exact hx2
      have hdβ : m₀ * τ * (m * t) = m * t * (m₀ * τ) := by rw [← hxmt]; exact hβx
      exact no_inv_Mct h hMh hMc hb hK hT hm₀ hβ hTβ hm hd2 hdβ
    · right
      refine ⟨x * (m₀ * τ), ?_, ?_⟩
      · have hτm₀ : τ * m₀ * τ = m₀⁻¹ := by
          have hh := congrArg (fun y => m₀⁻¹ * y) hβ
          simpa [mul_assoc] using hh
        have hyMc : x * (m₀ * τ) ∈ Mc := by
          rw [hxmτ]
          have hkey : m * τ * (m₀ * τ) = m * m₀⁻¹ := by
            calc m * τ * (m₀ * τ) = m * (τ * m₀ * τ) := by group
              _ = m * m₀⁻¹ := by rw [hτm₀]
          rw [hkey]
          exact Mc.mul_mem hm (Mc.inv_mem hm₀)
        have hy2 : (x * (m₀ * τ)) * (x * (m₀ * τ)) = 1 := by
          have hxβ : x * (m₀ * τ) = (m₀ * τ) * x := hβx.symm
          calc (x * (m₀ * τ)) * (x * (m₀ * τ))
              = x * ((m₀ * τ) * x) * (m₀ * τ) := by group
            _ = x * (x * (m₀ * τ)) * (m₀ * τ) := by rw [← hxβ]
            _ = (x * x) * ((m₀ * τ) * (m₀ * τ)) := by group
            _ = 1 := by rw [hx2, hβ, mul_one]
        have hβy : (m₀ * τ) * (x * (m₀ * τ)) = (x * (m₀ * τ)) * (m₀ * τ) := by
          calc (m₀ * τ) * (x * (m₀ * τ)) = ((m₀ * τ) * x) * (m₀ * τ) := by group
            _ = (x * (m₀ * τ)) * (m₀ * τ) := by rw [hβx]
        exact inv_comm_mem_V h hMh hMc hZ hm₀ hm₀Q hyMc hy2 hβy
      · calc (x * (m₀ * τ)) * (m₀ * τ) = x * ((m₀ * τ) * (m₀ * τ)) := by group
          _ = x := by rw [hβ, mul_one]
    · exfalso
      have hd2 : m * (t * τ) * (m * (t * τ)) = 1 := by rw [← hxmtτ]; exact hx2
      have hdβ : m₀ * τ * (m * (t * τ)) = m * (t * τ) * (m₀ * τ) := by
        rw [← hxmtτ]; exact hβx
      exact no_inv_Mctau_t h hMh hMc hb hK hT hm₀ hβ hTβ hm hd2 hdβ
  calc S.ncard ≤ ((V : Set H) ∪ (fun v => v * (m₀ * τ)) '' (V : Set H)).ncard :=
        Set.ncard_le_ncard hSsub
    _ ≤ (V : Set H).ncard + ((fun v => v * (m₀ * τ)) '' (V : Set H)).ncard :=
        Set.ncard_union_le _ _
    _ ≤ 4 + 4 := by
        refine Nat.add_le_add ?_ ?_
        · exact le_of_eq hVcard
        · calc ((fun v => v * (m₀ * τ)) '' (V : Set H)).ncard ≤ (V : Set H).ncard :=
              Set.ncard_image_le
            _ = 4 := hVcard
    _ = 8 := by norm_num

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
