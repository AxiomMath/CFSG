module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

section Base


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {S₁ : Sylow 2 Y} {R₁ R₂ : Subgroup Y} {t₁ u₁ u₂ : Y}

theorem twinSet_eq (hP : PerpHypR r n Y R S t)
    (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t
      t₁ u₁ u₂) :
    twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) = {tightCore R, K'} :=
  hP.perp.symm.trans hyp.std.2

theorem not_commute_ord4
    (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t
      t₁ u₁ u₂) {J : Subgroup Y} (hJ : J ∈ CoreAssembly.conjClass (tightCore R)) {a : Y}
    (ha : IsUniqueInvolution J a) {y : Y} (hya : y * t * y⁻¹ ≠ a) {x : Y} (hx : x ∈ J)
    (hx4 : orderOf x = 4) : (y * t * y⁻¹) * x ≠ x * (y * t * y⁻¹) :=
  T7F25.Asc77.T7ER.not_commute_of_conj hyp.std.setting hyp.hW hyp.hE4 hJ ha hya hx hx4

theorem conj_four_dvd (hP : PerpHypR r n Y R S t)
    (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t
      t₁ u₁ u₂) {y₀ g : Y} (hy₀ : y₀ ∈ R₁ ∨ y₀ ∈ R₂) (h4 : 4 ∣ orderOf y₀)
    (hg : g⁻¹ * y₀ * g ∈ (S₁ : Subgroup Y)) :
    g * t * g⁻¹ = t ∧ (g⁻¹ * y₀ * g ∈ R₁ ∨ g⁻¹ * y₀ * g ∈ R₂) := by
  classical
  have hs := hyp.std.setting
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hs.stand.hyp
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := hs.stand.mem
  have hzK : IsUniqueInvolution (tightCore R) t := hs.hz
  have hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) := hs.hK'
  have hzK' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hzK hK'
  have hK'Ω : K' ∈ CoreAssembly.conjClass (tightCore R) := hK'.1
  have hR₁ : IsSylow2In R₁ (tightCore R) :=
    T7F25.Asc77.T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hyp.hR.1 hyp.hR.2.1
  have hR₂ : IsSylow2In R₂ K' :=
    T7F25.Asc77.T7C.isSylow2In_of_mem_RSet_of_le hΩ hK'Ω hyp.hR'.1 hyp.hR'.2.1
  obtain ⟨J, hJΩ, hzJ, hy₀J, hRJ⟩ : ∃ J : Subgroup Y, J ∈ CoreAssembly.conjClass (tightCore R) ∧
      IsUniqueInvolution J t ∧ y₀ ∈ J ∧ (J = tightCore R ∨ J = K') := by
    rcases hy₀ with h | h
    · exact ⟨tightCore R, hK, hzK, hR₁.1 h, Or.inl rfl⟩
    · exact ⟨K', hK'Ω, hzK', hR₂.1 h, Or.inr rfl⟩
  have hJ'Ω : conjSub g⁻¹ J ∈ CoreAssembly.conjClass (tightCore R) :=
    hΩ.conjInvariant g⁻¹ J hJΩ
  have hJ't : IsUniqueInvolution (conjSub g⁻¹ J) (g⁻¹ * t * g) := by
    have := hzJ.conj g⁻¹
    simpa using this
  have hw : g⁻¹ * y₀ * g ∈ conjSub g⁻¹ J := by
    have := conj_mem_conjSub (n := g⁻¹) hy₀J
    simpa using this
  have hord : orderOf (g⁻¹ * y₀ * g) = orderOf y₀ := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) y₀
    simpa [MulAut.conj_apply] using h
  set w : Y := g⁻¹ * y₀ * g with hwdef
  have hk : orderOf w / 4 ≠ 0 := by
    have hpos : 0 < orderOf w := orderOf_pos w
    have h4w : 4 ∣ orderOf w := by rw [hord]; exact h4
    exact (Nat.div_pos (Nat.le_of_dvd hpos h4w) (by norm_num)).ne'
  have hkd : orderOf w / 4 ∣ orderOf w := Nat.div_dvd_of_dvd (by rw [hord]; exact h4)
  have hw'4 : orderOf (w ^ (orderOf w / 4)) = 4 := by
    rw [orderOf_pow_of_dvd hk hkd]
    exact Nat.div_div_self (by rw [hord]; exact h4) (orderOf_pos w).ne'
  have hw'J : w ^ (orderOf w / 4) ∈ conjSub g⁻¹ J := (conjSub g⁻¹ J).pow_mem hw _
  have hw'S : w ^ (orderOf w / 4) ∈ (S₁ : Subgroup Y) := (S₁ : Subgroup Y).pow_mem hg _
  have hcomm := hyp.hzS _ hw'S
  have hat : g⁻¹ * t * g = t := by
    by_contra hat
    have := not_commute_ord4 hyp hJ'Ω hJ't (y := 1) (by simpa using Ne.symm hat) hw'J hw'4
    simp only [one_mul, inv_one, mul_one] at this
    exact this hcomm.symm
  refine ⟨?_, ?_⟩
  · have := congrArg (fun x => g * x * g⁻¹) hat
    simpa [mul_assoc] using this.symm
  ·
    have hmem : conjSub g⁻¹ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) :=
      ⟨hJ'Ω, t, hzK, hat ▸ hJ't⟩
    rw [twinSet_eq hP hyp] at hmem
    rcases hmem with h | h
    · left
      have hwK : w ∈ tightCore R := h ▸ hw
      have hle : tightCore R ⊓ (S₁ : Subgroup Y) = R₁ :=
        hR₁.2.2 _ inf_le_left (S₁.isPGroup'.to_le inf_le_right)
          (le_inf hR₁.1 hyp.hR.2.2)
      have : w ∈ tightCore R ⊓ (S₁ : Subgroup Y) := ⟨hwK, hg⟩
      rwa [hle] at this
    · right
      have hwK : w ∈ K' := by
        rw [Set.mem_singleton_iff] at h
        exact h ▸ hw
      have hle : K' ⊓ (S₁ : Subgroup Y) = R₂ :=
        hR₂.2.2 _ inf_le_left (S₁.isPGroup'.to_le inf_le_right)
          (le_inf hR₂.1 hyp.hR'.2.2)
      have : w ∈ K' ⊓ (S₁ : Subgroup Y) := ⟨hwK, hg⟩
      rwa [hle] at this

theorem exists_order_four_of_isFAut {R' : Subgroup Y} {a : Y} (hF : IsFAut R' a) :
    ∃ w ∈ R', w * a = a * w ∧ orderOf w = 4 := by
  obtain ⟨haN, ha2, Q, R₀, hQ, hQq, hR₀, hcard⟩ := hF
  obtain ⟨k, hk, ⟨e⟩⟩ := hQq
  have hQle : Q ≤ R' ⊓ Subgroup.centralizer ({a} : Set Y) := hQ.1
  refine ⟨((e.symm (QuaternionGroup.xa 0) : ↥Q) : Y), (hQle (e.symm _).2).1, ?_, ?_⟩
  · have := Subgroup.mem_centralizer_singleton_iff.mp (hQle (e.symm (QuaternionGroup.xa 0)).2).2
    exact this
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_xa]

end Base

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
