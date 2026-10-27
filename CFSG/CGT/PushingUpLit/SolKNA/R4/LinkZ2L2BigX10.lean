module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigX9
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big31

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Cit3


variable {r n : ℕ}

theorem z2BigXPlusA_of_hweak (hw : Z2BigHweak r n) : Z2BigXPlusA r n := by
  intro hr Y _ _ R S t J u R₀ T₀ P hs h1 _ _ x hxA hx2 hout g hg
  have hxt' : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxA.1.2
  have hxu' : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp hxA.2
  obtain ⟨m, hm⟩ := hs.exists_conj_u
  have hQ2 : IsPGroup 2 ↥(conjSub g ((P : Subgroup Y) ⊓ Subgroup.centralizer ({x} : Set Y))) :=
    (P.isPGroup'.to_le inf_le_left).map _
  have hQa : conjSub g ((P : Subgroup Y) ⊓ Subgroup.centralizer ({x} : Set Y)) ≤
      Subgroup.centralizer ({t * u} : Set Y) := by
    intro q hq
    rw [mem_conjSub_iff] at hq
    have h1 : g⁻¹ * q * g * x = x * (g⁻¹ * q * g) :=
      Subgroup.mem_centralizer_singleton_iff.mp hq.2
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    have h2 : g * (g⁻¹ * q * g * x) * g⁻¹ = g * (x * (g⁻¹ * q * g)) * g⁻¹ := by rw [h1]
    rw [show g * (g⁻¹ * q * g * x) * g⁻¹ = q * (g * x * g⁻¹) by group,
      show g * (x * (g⁻¹ * q * g)) * g⁻¹ = g * x * g⁻¹ * q by group] at h2
    exact h2
  obtain ⟨c, hc, hcQ⟩ := hs.exists_conj_le hQ2 hQa
  obtain ⟨k, hk⟩ : ∃ k : Y, k = c * g := ⟨_, rfl⟩
  have hkx : k * x * k⁻¹ = t * u := by
    rw [hk, show c * g * x * (c * g)⁻¹ = c * (g * x * g⁻¹) * c⁻¹ by group, hg,
      conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hc)]
  have hkP : ∀ q ∈ (P : Subgroup Y), q * x = x * q → k * q * k⁻¹ ∈ (P : Subgroup Y) := by
    intro q hq hqx
    apply hcQ
    rw [hk, show c * g * q * (c * g)⁻¹ = c * (g * q * g⁻¹) * c⁻¹ by group]
    have hq' : q ∈ (P : Subgroup Y) ⊓ Subgroup.centralizer ({x} : Set Y) :=
      ⟨hq, Subgroup.mem_centralizer_singleton_iff.mpr hqx⟩
    exact conj_mem_conjSub (conj_mem_conjSub hq' g) c
  have htne : t ≠ 1 := hs.large.datum.isUniqueInvolution_core.ne_one
  have ht₁ : k * t * k⁻¹ ∈ edgeCent (P : Subgroup Y) t u := by
    have h2 := hw hr Y R S t J u R₀ T₀ P hs h1 t hs.t_mem_R₀ htne k⁻¹
      (by rw [inv_inv]; exact hkP t hs.t_mem_P hxt'.symm)
    rwa [inv_inv] at h2
  have hu₁ : k * u * k⁻¹ ∈ edgeCent (P : Subgroup Y) t u := by
    have e : k * u * k⁻¹ = (k * m)⁻¹⁻¹ * t * (k * m)⁻¹ := by rw [← hm]; group
    rw [e]
    refine hw hr Y R S t J u R₀ T₀ P hs h1 t hs.t_mem_R₀ htne (k * m)⁻¹ ?_
    rw [← e]
    exact hkP u hs.u_mem_P hxu'.symm
  set Q' := conjSub k⁻¹ ((P : Subgroup Y) ⊓ Subgroup.centralizer ({k * t * k⁻¹} : Set Y) ⊓
    Subgroup.centralizer ({k * u * k⁻¹} : Set Y)) with hQ'
  have hQ'2 : IsPGroup 2 ↥Q' := (P.isPGroup'.to_le (inf_le_left.trans inf_le_left)).map _
  have hcomm_conj : ∀ {q a : Y}, k * q * k⁻¹ * (k * a * k⁻¹) = k * a * k⁻¹ * (k * q * k⁻¹) →
      q * a = a * q := by
    intro q a h
    have h2 : k⁻¹ * (k * q * k⁻¹ * (k * a * k⁻¹)) * k = k⁻¹ * (k * a * k⁻¹ * (k * q * k⁻¹)) * k :=
      by rw [h]
    rwa [show k⁻¹ * (k * q * k⁻¹ * (k * a * k⁻¹)) * k = q * a by group,
      show k⁻¹ * (k * a * k⁻¹ * (k * q * k⁻¹)) * k = a * q by group] at h2
  have hQ't : Q' ≤ Subgroup.centralizer ({t} : Set Y) := by
    intro q hq
    rw [hQ', mem_conjSub_iff, inv_inv] at hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm_conj (Subgroup.mem_centralizer_singleton_iff.mp hq.1.2)
  have hQ'u : Q' ≤ Subgroup.centralizer ({u} : Set Y) := by
    intro q hq
    rw [hQ', mem_conjSub_iff, inv_inv] at hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm_conj (Subgroup.mem_centralizer_singleton_iff.mp hq.2)
  have hmemQ' : ∀ q ∈ (P : Subgroup Y), q * (k * t * k⁻¹) = k * t * k⁻¹ * q →
      q * (k * u * k⁻¹) = k * u * k⁻¹ * q → k⁻¹ * q * k ∈ Q' := by
    intro q hq h1 h2
    rw [hQ', mem_conjSub_iff, inv_inv, show k * (k⁻¹ * q * k) * k⁻¹ = q by group]
    exact ⟨⟨hq, Subgroup.mem_centralizer_singleton_iff.mpr h1⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr h2⟩
  have htQ' : k⁻¹ * t * k ∈ Q' := hmemQ' t hs.t_mem_P
    (Subgroup.mem_centralizer_singleton_iff.mp ht₁.1.2).symm
    (Subgroup.mem_centralizer_singleton_iff.mp hu₁.1.2).symm
  have huQ' : k⁻¹ * u * k ∈ Q' := hmemQ' u hs.u_mem_P
    (Subgroup.mem_centralizer_singleton_iff.mp ht₁.2).symm
    (Subgroup.mem_centralizer_singleton_iff.mp hu₁.2).symm
  obtain ⟨d, hd, hdQ⟩ := hs.exists_conj_le_edgeCent hQ'2 hQ't hQ'u
  have ht'' : d * (k⁻¹ * t * k) * d⁻¹ ∈ edgeCent (P : Subgroup Y) t u :=
    hdQ (conj_mem_conjSub htQ' d)
  have hu'' : d * (k⁻¹ * u * k) * d⁻¹ ∈ edgeCent (P : Subgroup Y) t u :=
    hdQ (conj_mem_conjSub huQ' d)
  have hinner : ∀ y ∈ edgeCent (P : Subgroup Y) t u, ∀ h : Y, y = h * t * h⁻¹ →
      InnerModOdd (linkLayer R t) y ∧
        InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) y := by
    intro y hy h hyh
    by_contra hnot
    have hy2 : y * y = 1 := by
      rw [hyh, show h * t * h⁻¹ * (h * t * h⁻¹) = h * (t * t) * h⁻¹ by group, hs.t2]
      group
    exact z2BigXPlusT_holds r n hr Y R S t J u R₀ T₀ P hs h1 y hy hy2 (not_and_or.mp hnot) h⁻¹
      (by rw [hyh]; group)
  obtain ⟨hi1t, hi1u⟩ := hinner _ ht'' (d * k⁻¹) (by group)
  obtain ⟨hi2t, hi2u⟩ := hinner _ hu'' (d * k⁻¹ * m) (by rw [← hm]; group)
  have e : d * (k⁻¹ * t * k) * d⁻¹ * (d * (k⁻¹ * u * k) * d⁻¹) = d * x * d⁻¹ := by
    rw [show d * (k⁻¹ * t * k) * d⁻¹ * (d * (k⁻¹ * u * k) * d⁻¹) =
      d * (k⁻¹ * (t * u) * k) * d⁻¹ by group, ← hkx]
    group
  rcases hout with hxt | hxu
  · apply hxt
    rw [innerModOdd_conj_iff x d, hs.conjSub_Λt_fix (conj_eq_of_comm
      (Subgroup.mem_centralizer_singleton_iff.mp hd.1))]
    rw [← e]
    exact innerModOdd_mul hi1t hi2t (hs.conjSub_Λt_of_mem ht'')
  · apply hxu
    rw [innerModOdd_conj_iff x d, hs.conjSub_Λu_fix (conj_eq_of_comm
      (Subgroup.mem_centralizer_singleton_iff.mp hd.2))]
    rw [← e]
    exact innerModOdd_mul hi1u hi2u (hs.conjSub_Λu_of_mem ht'')

theorem z2BigXPlusA_holds (r n : ℕ) : Z2BigXPlusA r n :=
  z2BigXPlusA_of_hweak (z2BigHweak_holds r n)

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
