module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cRefl
public import CFSG.Certificates.Kernel.ThDemp.OrbCent

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

section Orbit

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y}

theorem D_memOmega (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {Rm : Subgroup Y}
    (hRm : Rm ∈ DSet Ω[R] W) : Rm ∈ Ω[R] := by
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hRm.1
  have : J = Rm := hRJ.2.2 J le_rfl (h2gOf H J hJ) hRJ.1
  rwa [this] at hJ

theorem tau_ne_t (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) : a₁ * a₂ * a₃ * a₄ ≠ t := by
  intro h
  have F := frameCalc_of H fr
  obtain ⟨k, hk, hka⟩ := exists_inverting H (memKPOf H) fr.h₂.1 F.s₂
  have c1 : k * a₁ = a₁ * k := commOf H (memKPOf H) (memKOf H) (neKPKOf H) k hk a₁ fr.h₁.1
  have c3 : k * a₃ = a₃ * k := commOf H (memKPOf H) (memK₃Of H) (neK₃KPOf H).symm k hk a₃ fr.h₃.1
  have c4 : k * a₄ = a₄ * k := commOf H (memKPOf H) (memK₄Of H) (neK₄KPOf H).symm k hk a₄ fr.h₄.1
  have ct : k * t = t * k := ((q8Of H (memKPOf H)).z_central k hk).symm
  have e : k * (a₁ * a₂ * a₃ * a₄) * k⁻¹ = a₁ * a₂ * a₃ * a₄ * t := by
    calc k * (a₁ * a₂ * a₃ * a₄) * k⁻¹
        = (k * a₁ * k⁻¹) * (k * a₂ * k⁻¹) * (k * a₃ * k⁻¹) * (k * a₄ * k⁻¹) := by group
      _ = a₁ * (a₂ * t) * a₃ * a₄ := by
          rw [conj_eq_of_comm c1, hka, conj_eq_of_comm c3, conj_eq_of_comm c4]
      _ = a₁ * a₂ * (t * a₃) * a₄ := by group
      _ = a₁ * a₂ * (a₃ * t) * a₄ := by rw [F.t₃]
      _ = a₁ * a₂ * a₃ * (t * a₄) := by group
      _ = a₁ * a₂ * a₃ * (a₄ * t) := by rw [F.t₄]
      _ = a₁ * a₂ * a₃ * a₄ * t := by group
  rw [h, conj_eq_of_comm ct, F.tt] at e
  exact (stdOf H).datum.hz.ne_one (by rw [e])

theorem uW_mem (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) : a₁ * a₂ ∈ W :=
  W.mul_mem fr.h₁.2 fr.h₂.2

theorem tauW_mem (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) : a₁ * a₂ * a₃ * a₄ ∈ W :=
  W.mul_mem (W.mul_mem (W.mul_mem fr.h₁.2 fr.h₂.2) fr.h₃.2) fr.h₄.2

theorem u_sq {t a₁ a₂ : Y} (hc : a₁ * a₂ = a₂ * a₁) (h1 : a₁ * a₁ = t) (h2 : a₂ * a₂ = t)
    (htt : t * t = 1) : a₁ * a₂ * (a₁ * a₂) = 1 := by
  have h : (a₁ * a₂) ^ 2 = 1 := by
    rw [(show Commute a₁ a₂ from hc).mul_pow, pow_two a₁, pow_two a₂, h1, h2, htt]
  rwa [pow_two] at h

theorem tau_member (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) :
    conjSub y K ∈ Ω[R] ∧ IsUniqueInvolution (conjSub y K) (a₁ * a₂ * a₃ * a₄) ∧
      conjSub y K ∈ DSet Ω[R] W := by
  have hz : IsUniqueInvolution (conjSub y K) (a₁ * a₂ * a₃ * a₄) := by
    have := (uniqInvOf H (memKOf H)).conj y
    rwa [fr.hy] at this
  have hΩ' : conjSub y K ∈ Ω[R] := (hypOf H).conjInvariant y K (memKOf H).1
  exact ⟨hΩ', hz, twin_mem_DSet (partIOf H) (h2gOf H) H.hW (tauW_mem fr) hΩ' hz⟩

theorem exists_s (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) :
    ∃ s ∈ MGrp Ω[R] W, s * t * s⁻¹ = a₁ * a₂ * a₃ * a₄ * t ∧
      s * (a₁ * a₂ * a₃ * a₄) * s⁻¹ = a₁ * a₂ * a₃ * a₄ ∧
      (s * (a₁ * a₂) * s⁻¹ = a₁ * a₂ ∨ s * (a₁ * a₂) * s⁻¹ = a₁ * a₂ * (a₁ * a₂ * a₃ * a₄)) := by
  have F := frameCalc_of H fr
  obtain ⟨hJΩ, hJz, hJD⟩ := tau_member H fr
  have hab := abelianOf H
  have hΩ := hypOf H
  have hJ2 : IsPGroup 2 ↥(conjSub y K) := h2gOf H _ hJΩ
  have hJsyl : IsSylow2In (conjSub y K) (conjSub y K) :=
    ⟨le_rfl, hJ2, fun V' hV' _ hK' => le_antisymm hV' hK'⟩
  have hex : ∃ s ∈ conjSub y K, s * t ≠ t * s := by
    by_contra hno
    push Not at hno
    have hJc : conjSub y K ≤ Subgroup.centralizer ({t} : Set Y) := fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hno s hs)
    have hne : K ≠ conjSub y K := fun h => tau_ne_t H fr (by
      have h' : IsUniqueInvolution K (a₁ * a₂ * a₃ * a₄) := by rw [h]; exact hJz
      exact h'.eq (uniqInvOf H (memKOf H)))
    have hJR : conjSub y K ∈ RSet Ω[R] := mem_RSet_of_isSylow2In hJΩ hJsyl
    have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hJR
    have hnorm : conjSub y K ≤ Subgroup.normalizer (K : Set Y) :=
      Sec6Gen.le_normalizer_of_le_centralizer hΩ (memKOf H).1 hJΩ hne (uniqInvOf H (memKOf H))
        le_rfl hJ2 (by omega) hJc
    have hnb : conjSub y K ∈ omegaNbr Ω[R] K := ⟨hJΩ, fun h => hne h.symm, conjSub y K, hJR, le_rfl, hnorm⟩
    have hperp := kPerp_datum (stdOf H).perp (stdOf H).datum.mem (stdOf H).datum.hz
    have hmem : conjSub y K ∈ twinSet Ω[R] K := by
      rw [← hperp]
      exact Set.mem_insert_of_mem _ hnb
    exact tau_ne_t H fr (hJz.eq (uniqInvOf H hmem))
  obtain ⟨s, hs, hst⟩ := hex
  have hsM : s ∈ MGrp Ω[R] W := Thompson.le_MGrp_of_mem_D hJD hs
  have hsN : s ∈ Subgroup.normalizer (W : Set Y) := hJD.2 hs
  have hconjW : ∀ x ∈ W, s * x * s⁻¹ ∈ W := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hsN x).mp hx
  have hq := q8Facts_of_iso hJz (members_q8_of_isPGroup (stdOf H).perp (h2gOf H) _ hJΩ).some
  have key : ∀ w ∈ W, w * w = 1 →
      s * w * s⁻¹ = w ∨ s * w * s⁻¹ = a₁ * a₂ * a₃ * a₄ * w := by
    intro w hwW hw2
    have hrm := refl_mem hΩ H.hW hJD hJΩ hJ2 hs hwW
    set A := s * w * s⁻¹ with hA
    have hAW : A ∈ W := hconjW w hwW
    have hAA : A * A = 1 := by
      calc A * A = s * (w * w) * s⁻¹ := by rw [hA]; group
        _ = 1 := by rw [hw2]; group
    have hAw : A * w = w * A := hab _ hAW _ hwW
    have hwi : w⁻¹ * w⁻¹ = 1 := by rw [← mul_inv_rev, hw2, inv_one]
    have hAwi : A * w⁻¹ = w⁻¹ * A := by
      calc A * w⁻¹ = w⁻¹ * (w * A) * w⁻¹ := by group
        _ = w⁻¹ * (A * w) * w⁻¹ := by rw [hAw]
        _ = w⁻¹ * A := by group
    have hc2 : (A * w⁻¹) * (A * w⁻¹) = 1 := by
      calc (A * w⁻¹) * (A * w⁻¹) = A * (w⁻¹ * A) * w⁻¹ := by group
        _ = A * (A * w⁻¹) * w⁻¹ := by rw [hAwi]
        _ = (A * A) * (w⁻¹ * w⁻¹) := by group
        _ = 1 := by rw [hAA, hwi, one_mul]
    rcases hJz.unique (A * w⁻¹) hrm.1 hc2 with h1 | h1
    · left
      calc A = A * w⁻¹ * w := by group
        _ = w := by rw [h1, one_mul]
    · right
      calc A = A * w⁻¹ * w := by group
        _ = a₁ * a₂ * a₃ * a₄ * w := by rw [h1]
  have htW := tmemOf H
  have hstt : s * t * s⁻¹ = a₁ * a₂ * a₃ * a₄ * t := by
    rcases key t htW F.tt with h | h
    · exact absurd (by calc s * t = (s * t * s⁻¹) * s := by group
                          _ = t * s := by rw [h]) hst
    · exact h
  refine ⟨s, hsM, hstt, ?_, ?_⟩
  · have hτs : a₁ * a₂ * a₃ * a₄ * s = s * (a₁ * a₂ * a₃ * a₄) := hq.z_central s hs
    exact conj_eq_of_comm hτs.symm
  · rcases key (a₁ * a₂) (uW_mem fr) (u_sq F.c₁₂ F.s₁ F.s₂ F.tt) with h | h
    · exact Or.inl h
    · right
      rw [h]
      exact hab _ (tauW_mem fr) _ (uW_mem fr)

@[expose] def InZ (t τ x : Y) : Prop := x = 1 ∨ x = t ∨ x = τ ∨ x = τ * t

theorem InZ.mul {t τ a b : Y} (ht2 : t * t = 1) (hτ2 : τ * τ = 1) (htτ : t * τ = τ * t)
    (ha : InZ t τ a) (hb : InZ t τ b) : InZ t τ (a * b) := by
  have e1 : τ * t * t = τ := by rw [mul_assoc, ht2, mul_one]
  have e2 : τ * (τ * t) = t := by rw [← mul_assoc, hτ2, one_mul]
  rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;> rw [ha, hb]
  · left; rw [one_mul]
  · right; left; rw [one_mul]
  · right; right; left; rw [one_mul]
  · right; right; right; rw [one_mul]
  · right; left; rw [mul_one]
  · left; exact ht2
  · right; right; right; exact htτ
  · right; right; left
    calc t * (τ * t) = (t * τ) * t := by rw [mul_assoc]
      _ = τ * t * t := by rw [htτ]
      _ = τ := e1
  · right; right; left; rw [mul_one]
  · right; right; right; rfl
  · left; exact hτ2
  · right; left; exact e2
  · right; right; right; rw [mul_one]
  · right; right; left; exact e1
  · right; left
    calc τ * t * τ = τ * (t * τ) := by rw [mul_assoc]
      _ = τ * (τ * t) := by rw [htτ]
      _ = t := e2
  · left
    calc τ * t * (τ * t) = τ * (t * τ) * t := by group
      _ = τ * (τ * t) * t := by rw [htτ]
      _ = t * t := by rw [e2]
      _ = 1 := ht2

theorem conjZ (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) {g : Y}
    (hg : g ∈ Subgroup.normalizer (W : Set Y)) {x : Y} (hx : InZ t (a₁ * a₂ * a₃ * a₄) x) :
    InZ t (a₁ * a₂ * a₃ * a₄) (g * x * g⁻¹) := by
  have F := frameCalc_of H fr
  have hΩ := hypOf H
  have hmem : ∀ {J : Subgroup Y} {z : Y}, J ∈ DSet Ω[R] W → IsUniqueInvolution J z →
      InZ t (a₁ * a₂ * a₃ * a₄) (g * z * g⁻¹) := by
    intro J z hJD hz
    have hJD' := Q3CL.Thompson.conjSub_mem_D hΩ hJD hg
    have hz' := hz.conj g
    rcases inv_trich H fr (D_memOmega H hJD') hJD' hz' with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have ht : InZ t (a₁ * a₂ * a₃ * a₄) (g * t * g⁻¹) := hmem H.hK (uniqInvOf H (memKOf H))
  have hτ : InZ t (a₁ * a₂ * a₃ * a₄) (g * (a₁ * a₂ * a₃ * a₄) * g⁻¹) :=
    hmem (tau_member H fr).2.2 (tau_member H fr).2.1
  rcases hx with hx | hx | hx | hx
  · left; rw [hx]; group
  · rw [hx]; exact ht
  · rw [hx]; exact hτ
  · rw [hx]
    have : g * (a₁ * a₂ * a₃ * a₄ * t) * g⁻¹ =
        (g * (a₁ * a₂ * a₃ * a₄) * g⁻¹) * (g * t * g⁻¹) := by group
    rw [this]
    exact InZ.mul F.tt (tau_sq F) (t_tau_comm F) hτ ht

theorem comm_sq_one {A w : Y} (hAA : A * A = 1) (hww : w * w = 1) (hAw : A * w = w * A) :
    (A * w⁻¹) * (A * w⁻¹) = 1 := by
  have hwi : w⁻¹ * w⁻¹ = 1 := by rw [← mul_inv_rev, hww, inv_one]
  have hAwi : A * w⁻¹ = w⁻¹ * A := by
    calc A * w⁻¹ = w⁻¹ * (w * A) * w⁻¹ := by group
      _ = w⁻¹ * (A * w) * w⁻¹ := by rw [hAw]
      _ = w⁻¹ * A := by group
  calc (A * w⁻¹) * (A * w⁻¹) = A * (w⁻¹ * A) * w⁻¹ := by group
    _ = A * (A * w⁻¹) * w⁻¹ := by rw [hAwi]
    _ = (A * A) * (w⁻¹ * w⁻¹) := by group
    _ = 1 := by rw [hAA, hwi, one_mul]

theorem gen_step (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) {Rm : Subgroup Y} (hRm : Rm ∈ DSet Ω[R] W)
    {r : Y} (hr : r ∈ Rm) :
    ∃ x, InZ t (a₁ * a₂ * a₃ * a₄) x ∧ r * (a₁ * a₂) * r⁻¹ = a₁ * a₂ * x := by
  have F := frameCalc_of H fr
  have hΩ := hypOf H
  have hRΩ := D_memOmega H hRm
  have hab := abelianOf H
  have hrN : r ∈ Subgroup.normalizer (W : Set Y) := hRm.2 hr
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hRΩ
  have hu2 := u_sq F.c₁₂ F.s₁ F.s₂ F.tt
  have huW := uW_mem fr
  have hrm := refl_mem hΩ H.hW hRm hRΩ (h2gOf H _ hRΩ) hr huW
  have hAW : r * (a₁ * a₂) * r⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hrN _).mp huW
  have hAA : r * (a₁ * a₂) * r⁻¹ * (r * (a₁ * a₂) * r⁻¹) = 1 := by
    calc r * (a₁ * a₂) * r⁻¹ * (r * (a₁ * a₂) * r⁻¹) = r * (a₁ * a₂ * (a₁ * a₂)) * r⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hc2 := comm_sq_one hAA hu2 (hab _ hAW _ huW)
  have hxW : r * (a₁ * a₂) * r⁻¹ * (a₁ * a₂)⁻¹ ∈ W := hrm.2
  refine ⟨r * (a₁ * a₂) * r⁻¹ * (a₁ * a₂)⁻¹, ?_, ?_⟩
  · rcases hz.unique _ hrm.1 hc2 with h | h
    · exact Or.inl h
    · rw [h]
      rcases inv_trich H fr hRΩ hRm hz with h' | h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr h'))
  · calc r * (a₁ * a₂) * r⁻¹ = (r * (a₁ * a₂) * r⁻¹ * (a₁ * a₂)⁻¹) * (a₁ * a₂) := by group
      _ = a₁ * a₂ * (r * (a₁ * a₂) * r⁻¹ * (a₁ * a₂)⁻¹) := hab _ hxW _ huW

theorem orbit_mem (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) :
    ∀ m ∈ MGrp Ω[R] W, ∃ x, InZ t (a₁ * a₂ * a₃ * a₄) x ∧ m * (a₁ * a₂) * m⁻¹ = a₁ * a₂ * x := by
  have F := frameCalc_of H fr
  let C : Y → Prop := fun m => m ∈ Subgroup.normalizer (W : Set Y) ∧
    ∃ x, InZ t (a₁ * a₂ * a₃ * a₄) x ∧ m * (a₁ * a₂) * m⁻¹ = a₁ * a₂ * x
  have hmul : ∀ m₁ m₂, C m₁ → C m₂ → C (m₁ * m₂) := by
    rintro m₁ m₂ ⟨hm₁, x₁, hx₁, e₁⟩ ⟨hm₂, x₂, hx₂, e₂⟩
    refine ⟨Subgroup.mul_mem _ hm₁ hm₂, x₁ * (m₁ * x₂ * m₁⁻¹),
      InZ.mul F.tt (tau_sq F) (t_tau_comm F) hx₁ (conjZ H fr hm₁ hx₂), ?_⟩
    calc m₁ * m₂ * (a₁ * a₂) * (m₁ * m₂)⁻¹ = m₁ * (m₂ * (a₁ * a₂) * m₂⁻¹) * m₁⁻¹ := by group
      _ = (m₁ * (a₁ * a₂) * m₁⁻¹) * (m₁ * x₂ * m₁⁻¹) := by rw [e₂]; group
      _ = a₁ * a₂ * (x₁ * (m₁ * x₂ * m₁⁻¹)) := by rw [e₁]; group
  intro m hm
  have key : C m := by
    refine Subgroup.iSup_induction (C := C) (fun Rm : Subgroup Y => ⨆ (_ : Rm ∈ DSet Ω[R] W), Rm) hm
      ?_ ⟨Subgroup.one_mem _, 1, Or.inl rfl, by group⟩ hmul
    intro Rm z hz
    refine Subgroup.iSup_induction (C := C) (fun _ : Rm ∈ DSet Ω[R] W => Rm) hz ?_
      ⟨Subgroup.one_mem _, 1, Or.inl rfl, by group⟩ hmul
    intro hRm r hr
    exact ⟨hRm.2 hr, gen_step H fr hRm hr⟩
  exact key.2

theorem orbit_two_trans (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) {j : Y} (hjK : j ∈ K)
    (hja : j * a₁ * j⁻¹ = a₁ * t) :
    ∀ m ∈ MGrp Ω[R] W, m * (a₁ * a₂) * m⁻¹ = a₁ * a₂ ∨
      ∃ g ∈ MGrp Ω[R] W, g * (a₁ * a₂) * g⁻¹ = a₁ * a₂ ∧
        g * (j * (a₁ * a₂) * j⁻¹) * g⁻¹ = m * (a₁ * a₂) * m⁻¹ := by
  intro m hm
  have F := frameCalc_of H fr
  obtain ⟨x, hx, hmx⟩ := orbit_mem H fr m hm
  have hjM : j ∈ MGrp Ω[R] W := Thompson.le_MGrp_of_mem_D H.hK hjK
  have hj2 : j * a₂ = a₂ * j := commOf H (memKOf H) (memKPOf H) (neKPKOf H).symm j hjK a₂ fr.h₂.1
  have hj3 : j * a₃ = a₃ * j := commOf H (memKOf H) (memK₃Of H) (neK₃KOf H).symm j hjK a₃ fr.h₃.1
  have hj4 : j * a₄ = a₄ * j := commOf H (memKOf H) (memK₄Of H) (neK₄KOf H).symm j hjK a₄ fr.h₄.1
  have hjt : j * t = t * j := ((q8Of H (memKOf H)).z_central j hjK).symm
  obtain ⟨hju, hjτ, hjt'⟩ := refl₁_act F hja hj2 hj3 hj4 hjt
  obtain ⟨r, hr, hra⟩ := exists_inverting H (memK₃Of H) fr.h₃.1 F.s₃
  have hr1 : r * a₁ = a₁ * r := commOf H (memK₃Of H) (memKOf H) (neK₃KOf H) r hr a₁ fr.h₁.1
  have hr2 : r * a₂ = a₂ * r := commOf H (memK₃Of H) (memKPOf H) (neK₃KPOf H) r hr a₂ fr.h₂.1
  have hr4 : r * a₄ = a₄ * r := commOf H (memK₃Of H) (memK₄Of H) (neK₄K₃Of H).symm r hr a₄ fr.h₄.1
  have hrt : r * t = t * r := ((q8Of H (memK₃Of H)).z_central r hr).symm
  obtain ⟨hru, hrτ, hrt'⟩ := refl₃_act F hra hr1 hr2 hr4 hrt
  have hrM : r ∈ MGrp Ω[R] W := Thompson.le_MGrp_of_mem_D H.hK₃ hr
  obtain ⟨s, hsM, hst, -, hsu⟩ := exists_s H fr
  have T := two_trans_alg (MGrp Ω[R] W) hjM hrM hsM F.tt (tau_sq F) (t_tau_comm F) hju hjt' hjτ
    hru hrt' hrτ hst hsu
  rcases hx with hx | hx | hx | hx
  · left
    rw [hmx, hx, mul_one]
  · right
    refine ⟨1, Subgroup.one_mem _, by group, ?_⟩
    rw [hju, hmx, hx]
    group
  · right
    obtain ⟨g, hg, hg1, hg2⟩ := T (a₁ * a₂ * (a₁ * a₂ * a₃ * a₄)) (Or.inr (Or.inl rfl))
    exact ⟨g, hg, hg1, by rw [hju, hg2, hmx, hx]⟩
  · right
    obtain ⟨g, hg, hg1, hg2⟩ := T (a₁ * a₂ * (a₁ * a₂ * a₃ * a₄) * t) (Or.inr (Or.inr rfl))
    exact ⟨g, hg, hg1, by rw [hju, hg2, hmx, hx, mul_assoc]⟩

end Orbit

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c
