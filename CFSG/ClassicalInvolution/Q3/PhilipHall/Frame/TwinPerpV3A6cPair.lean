module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cEStrOf
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6bOdd
public import CFSG.Sporadic.Th.Chain
public import CFSG.Sporadic.ThSchreier.AutCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

variable {n : ℕ}


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

section Labels

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {c : Y}

theorem LayerCtx.lab_mem (L : LayerCtx Ω c) {J : Subgroup Y} (hJ : J ∈ PY Ω c) {α : Finset (Fin 6)}
    {h : α.card = 4} {b : Bool}
    (hl : (J.subgroupOf (pSpan (PY Ω c))).map L.I.φ = memBar α h b) :
    (∀ k ∈ J, L.ρ k ∈ memBar α h b) ∧ ∀ x ∈ memBar α h b, ∃ k ∈ J, L.ρ k = x := by
  constructor
  · intro k hk
    rw [L.hρ.onSpan k (le_pSpan hJ hk), ← hl]
    exact L.I.mem_map hJ hk
  · intro x hx
    rw [← hl] at hx
    obtain ⟨l, hl', hφ⟩ := L.I.exists_of_mem_map hJ hx
    exact ⟨l, hl', by rw [L.hρ.onSpan l (le_pSpan hJ hl')]; exact hφ⟩

theorem LayerCtx.twin_labels (L : LayerCtx Ω c) {K₃ K₄ : Subgroup Y} {t : Y} (h3 : K₃ ∈ PY Ω c)
    (h4 : K₄ ∈ PY Ω c) (hz3 : IsUniqueInvolution K₃ t) (hz4 : IsUniqueInvolution K₄ t)
    (hcomm : ∀ x ∈ K₃, ∀ y ∈ K₄, x * y = y * x) :
    ∃ (α : Finset (Fin 6)) (h : α.card = 4) (b : Bool),
      (K₃.subgroupOf (pSpan (PY Ω c))).map L.I.φ = memBar α h b ∧
      (K₄.subgroupOf (pSpan (PY Ω c))).map L.I.φ = memBar α h (!b) ∧ L.ρ t = zBar α h := by
  obtain ⟨α, h, b, hl3⟩ := L.I.label K₃ h3
  obtain ⟨α', h', b', hl4⟩ := L.I.label K₄ h4
  have hn5 : 5 ≤ 6 := by norm_num
  have e3 := L.I.map_eq_zBar hn5 h3 (L.h8 K₃ h3.1) hl3 hz3
  have e4 := L.I.map_eq_zBar hn5 h4 (L.h8 K₄ h4.1) hl4 hz4
  have hαα : α = α' := AE.eq_of_zBar_eq (by norm_num) (e3.symm.trans e4)
  subst hαα
  have hbb : b' = !b := by
    by_contra hne
    have hb : b' = b := by
      cases b <;> cases b' <;> simp_all
    subst hb
    obtain ⟨x, hx, x', hx', hxx⟩ := AE.exists_not_comm_memBar hn5 α h b'
    rw [← hl3] at hx
    rw [← hl4] at hx'
    obtain ⟨k, hk, rfl⟩ := L.I.exists_of_mem_map h3 hx
    obtain ⟨k', hk', rfl⟩ := L.I.exists_of_mem_map h4 hx'
    apply hxx
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm k hk k' hk')
  subst hbb
  exact ⟨α, h, b, hl3, hl4, by rw [L.hρ.onSpan t (le_pSpan h3 hz3.mem)]; exact e3⟩

end Labels

section Algebra

variable {Y : Type} [Group Y]

theorem comm_of_conj_eq {k x : Y} (hh : k * x * k⁻¹ = x) : k * x = x * k := by
  calc k * x = k * x * k⁻¹ * k := by group
    _ = x * k := by rw [hh]

theorem inverting_inv {t j : Y} (htt : t * t = 1) (hjj : j * j = t) : j⁻¹ = j * t :=
  inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hjj, htt])

theorem inverting_sq {J : Subgroup Y} {t a j : Y} (hq : Q8Facts J t) (ha : a ∈ J) (hj : j ∈ J)
    (hja : j * a * j⁻¹ = a * t) : j * j = t := by
  have ht1 : t ≠ 1 := hq.z_ne
  have hnc : j * a * j⁻¹ = a → False := by
    intro hx
    rw [hx] at hja
    apply ht1
    exact (mul_left_cancel (a := a) (by rw [mul_one]; exact hja)).symm
  rcases hq.sq_cases j hj with h | h
  · exfalso
    rcases hq.sq_one j hj h with h1 | h1
    · exact hnc (by rw [h1]; group)
    · exact hnc (by rw [h1, show t * a = a * t from hq.z_central a ha]; group)
  · exact h

end Algebra

section Datum

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y}

theorem v3AE6cPair_of (F : AE6Fin) (hE : V3AE6E n) : V3AE6cPair n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr j hjK hja e he e' he'
  classical
  obtain ⟨L⟩ := exists_layerCtx H
  obtain ⟨hEab, hcE, htE, -⟩ := hE Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr
  obtain ⟨hStd, hFo, hα, h2g, -⟩ := H.ex
  have hd := hStd.datum
  have hFr := frameCalc_of H fr
  have hspan : pSpan (PY Ω[R] (u₁ * u₂)) = rLayer Ω[R] (u₁ * u₂) := pSpan_PY h2g
  have hEE : ae6E Ω[R] (u₁ * u₂) = pCoreOf 2 (pSpan (PY Ω[R] (u₁ * u₂))) := by
    unfold ae6E
    rw [hspan]
  have hcard : Nat.card ↥(pCoreOf 2 (pSpan (PY Ω[R] (u₁ * u₂)))) = 32 := by
    have h1 := hEab.1
    rw [hEE] at h1
    rw [h1]
    norm_num
  have hsq : ∀ x ∈ pCoreOf 2 (pSpan (PY Ω[R] (u₁ * u₂))), x * x = 1 := by
    intro x hx
    rw [← hEE] at hx
    exact hEab.2 x hx
  have hconj : ∀ g ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y),
      ∀ x ∈ pCoreOf 2 (pSpan (PY Ω[R] (u₁ * u₂))),
        g * x * g⁻¹ ∈ pCoreOf 2 (pSpan (PY Ω[R] (u₁ * u₂))) := by
    intro g hg x hx
    have hgc : g * (u₁ * u₂) * g⁻¹ = u₁ * u₂ := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hg]
      group
    have h1 := cent_normalizes_E H hgc
    rw [hEE] at h1
    have h2 := conj_mem_conjSub (n := g) hx
    rwa [h1] at h2
  have Sx := estr_of L (hEE ▸ hcard) (hEE ▸ hcE) hsq hconj
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  obtain ⟨hcen3, hcen4⟩ := A6b.members_le_centralizer hStd hFo h2g
  have h3 : K₃ ∈ PY Ω[R] (u₁ * u₂) := ⟨hd.hK₃.1, hcen3⟩
  have h4 : K₄ ∈ PY Ω[R] (u₁ * u₂) := ⟨hFo.1.1, hcen4⟩
  have cKK' := commOf H (memKOf H) (memKPOf H) (neKPKOf H).symm
  have cK3 := commOf H (memKOf H) (memK₃Of H) (neK₃KOf H).symm
  have cK4 := commOf H (memKOf H) (memK₄Of H) (neK₄KOf H).symm
  have cK'3 := commOf H (memKPOf H) (memK₃Of H) (neK₃KPOf H).symm
  have cK'4 := commOf H (memKPOf H) (memK₄Of H) (neK₄KPOf H).symm
  have cK34 := commOf H (memK₃Of H) (memK₄Of H) (neK₄K₃Of H).symm
  obtain ⟨α, hα4, b, hl3, hl4, hρt⟩ := L.twin_labels h3 h4 (uniqInvOf H (memK₃Of H))
    (uniqInvOf H (memK₄Of H)) (fun x hx y hy => cK34 x hx y hy)
  have hqK := q8Of H (memKOf H)
  have hqK' := q8Of H (memKPOf H)
  obtain ⟨j', hj'K', hj'a⟩ := exists_inverting H (memKPOf H) fr.h₂.1 hFr.s₂
  have hjj : j * j = t := inverting_sq hqK fr.h₁.1 hjK hja
  have hj'j' : j' * j' = t := inverting_sq hqK' fr.h₂.1 hj'K' hj'a
  have hcjj' : j' * j = j * j' := (cKK' j hjK j' hj'K').symm
  have hj2 : j * a₂ * j⁻¹ = a₂ := conj_eq_of_comm (cKK' j hjK a₂ fr.h₂.1)
  have hjt : j * t * j⁻¹ = t := conj_eq_of_comm (hqK.z_central j hjK).symm
  have hj'1 : j' * a₁ * j'⁻¹ = a₁ := conj_eq_of_comm (cKK' a₁ fr.h₁.1 j' hj'K').symm
  have hj't : j' * t * j'⁻¹ = t := conj_eq_of_comm (hqK'.z_central j' hj'K').symm
  have hdc : j * j' * (u₁ * u₂) * (j * j')⁻¹ = u₁ * u₂ := by
    rw [← fr.hu]
    calc j * j' * (a₁ * a₂) * (j * j')⁻¹
        = j * (j' * a₁ * j'⁻¹) * (j' * a₂ * j'⁻¹) * j⁻¹ := by group
      _ = j * a₁ * (a₂ * t) * j⁻¹ := by rw [hj'1, hj'a]
      _ = (j * a₁ * j⁻¹) * (j * a₂ * j⁻¹) * (j * t * j⁻¹) := by group
      _ = (a₁ * t) * a₂ * t := by rw [hja, hj2, hjt]
      _ = a₁ * (t * a₂) * t := by group
      _ = a₁ * (a₂ * t) * t := by rw [hFr.t₂]
      _ = a₁ * a₂ * (t * t) := by group
      _ = a₁ * a₂ := by rw [hFr.tt, mul_one]
  have hjinv : j⁻¹ = j * t := inverting_inv hFr.tt hjj
  have hjaj : j * a₁ * j = a₁ := by
    have h1 : j * a₁ * (j * t) = a₁ * t := by rw [← hjinv]; exact hja
    have h2 : j * a₁ * j * t = a₁ * t := by rw [← h1]; group
    exact mul_right_cancel h2
  have T : TwinStr (u₁ * u₂) t j a₁ (j * j') (pSpan (PY Ω[R] (u₁ * u₂)))
      (pCoreOf 2 (pSpan (PY Ω[R] (u₁ * u₂)))) K₃ K₄ L.ρ α hα4 b :=
    { t_mem := hEE ▸ htE
      rho_t := hρt
      K₃X := fun k hk => le_pSpan h3 hk
      K₄X := fun k hk => le_pSpan h4 hk
      K₃_lab := L.lab_mem h3 hl3
      K₄_lab := L.lab_mem h4 hl4
      j_c := by
        rw [← fr.hu]
        exact (refl₁_act hFr hja (cKK' j hjK a₂ fr.h₂.1) (cK3 j hjK a₃ fr.h₃.1)
          (cK4 j hjK a₄ fr.h₄.1) (hqK.z_central j hjK).symm).1
      j_t := (hqK.z_central j hjK).symm
      j_K₃ := fun k hk => cK3 j hjK k hk
      j_K₄ := fun k hk => cK4 j hjK k hk
      a_C := by
        rw [Subgroup.mem_centralizer_singleton_iff, ← fr.hu]
        calc a₁ * (a₁ * a₂) = a₁ * (a₂ * a₁) := by rw [hFr.c₁₂]
          _ = a₁ * a₂ * a₁ := by group
      a_sq := hFr.s₁
      a_t := hFr.t₁.symm
      a_K₃ := fun k hk => cK3 a₁ fr.h₁.1 k hk
      a_K₄ := fun k hk => cK4 a₁ fr.h₁.1 k hk
      d_C := Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_conj_eq hdc)
      d_sq := by
        calc j * j' * (j * j') = j * (j' * j) * j' := by group
          _ = j * (j * j') * j' := by rw [hcjj']
          _ = (j * j) * (j' * j') := by group
          _ = t * t := by rw [hjj, hj'j']
          _ = 1 := hFr.tt
      d_a := by
        calc j * j' * a₁ * (j * j')⁻¹ = j * (j' * a₁ * j'⁻¹) * j⁻¹ := by group
          _ = j * a₁ * j⁻¹ := by rw [hj'1]
          _ = a₁ * t := hja
      d_t := by
        have e1 : j * t = t * j := (hqK.z_central j hjK).symm
        have e2 : j' * t = t * j' := (hqK'.z_central j' hj'K').symm
        calc j * j' * t = j * (j' * t) := by group
          _ = j * (t * j') := by rw [e2]
          _ = (j * t) * j' := by group
          _ = (t * j) * j' := by rw [e1]
          _ = t * (j * j') := by group
      d_K₃ := by
        intro k hk
        calc j * j' * k = j * (j' * k) := by group
          _ = j * (k * j') := by rw [cK'3 j' hj'K' k hk]
          _ = (j * k) * j' := by group
          _ = (k * j) * j' := by rw [cK3 j hjK k hk]
          _ = k * (j * j') := by group
      d_K₄ := by
        intro k hk
        calc j * j' * k = j * (j' * k) := by group
          _ = j * (k * j') := by rw [cK'4 j' hj'K' k hk]
          _ = (j * k) * j' := by group
          _ = (k * j) * j' := by rw [cK4 j hjK k hk]
          _ = k * (j * j') := by group
      j_d := by
        calc j⁻¹ * (j * j') * j = j' * j := by group
          _ = j * j' := hcjj'
      j_a := by
        calc j⁻¹ * a₁ * j = (j * t) * a₁ * j := by rw [hjinv]
          _ = j * (t * a₁) * j := by group
          _ = j * (a₁ * t) * j := by rw [hFr.t₁]
          _ = j * a₁ * (t * j) := by group
          _ = j * a₁ * (j * t) := by rw [(hqK.z_central j hjK)]
          _ = (j * a₁ * j) * t := by group
          _ = a₁ * t := by rw [hjaj] }
  rw [hEE] at he he'
  exact TwinStr.pair_core Sx T F e he e' he'

end Datum

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c
