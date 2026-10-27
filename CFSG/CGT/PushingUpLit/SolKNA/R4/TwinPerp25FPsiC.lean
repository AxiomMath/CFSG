module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FPsiB
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FB
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FPsiA
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FQb
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FQc

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

section Psi


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {S₁ : Sylow 2 Y} {R₁ R₂ : Subgroup Y} {t₁ u₁ u₂ : Y}

theorem exists_psi (hr : 4 ≤ r) (hP : PerpHypR r n Y R S t)
    (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t
      t₁ u₁ u₂) :
    ∃ (A : Type) (_ : CommGroup A) (Ψ : ↥(S₁ : Subgroup Y) →* A),
      (∀ (g : Y) (hg : g ∈ (S₁ : Subgroup Y)), (g ∈ R₁ ∨ g ∈ R₂) → Ψ ⟨g, hg⟩ = 1) ∧
      (∀ (g : Y) (hg : g ∈ (S₁ : Subgroup Y)), g * g = 1 → (∃ y : Y, y * t * y⁻¹ = g) →
        Ψ ⟨g, hg⟩ = 1) ∧
      (∀ (a : Y) (ha : a ∈ (S₁ : Subgroup Y)), a * a = 1 → IsFAut R₂ a → Ψ ⟨a, ha⟩ = 1 →
        ∃ x ∈ R₁, (a * x) * (a * x) = 1 ∧ IsFAut R₁ (a * x)) := by
  classical
  obtain ⟨t', hT⟩ := T7F25.Asc77.T7T.exists_hyp25T hyp
  set N : Subgroup Y := T7F2.Nsub S₁ R₁ with hNdef
  have hN2 : IsPGroup 2 ↥N := S₁.isPGroup'.to_le inf_le_left
  have hNR : ∀ y ∈ N, conjSub y R₁ = R₁ := fun y hy => (T7F2.mem_Nsub.mp hy).2
  obtain ⟨x, y, m, c, hNa⟩ := T7F2.exists_coord hT.hqR hT.hzR hN2 hNR
  have s : T7F2.Out.Setting R₁ N x y m := ⟨c, hT.R_le_N, hNR, hNa⟩
  have hm2 : 2 ≤ m := by
    have h1 := c.natCard
    rw [card_R₁ hr hP hyp] at h1
    have := Nat.pow_right_injective (le_refl 2) h1
    omega
  obtain ⟨α, hα⟩ := exists_multHom (x := x) (m := 2 ^ (m + 1)) c.hord (by positivity) N
    (fun h hh => s.conj_mem_a hh (Subgroup.mem_zpowers x))
  have ht'2 : t' * t' = 1 := hT.ht'2
  have ht'inv : t'⁻¹ = t' := hT.ht'inv
  let τ : ↥N →* ↥N := MonoidHom.mk' (fun g => ⟨t' * (g : Y) * t'⁻¹, hT.N_conj g.2⟩) (by
    intro a b
    apply Subtype.ext
    show t' * ((a : Y) * (b : Y)) * t'⁻¹ = (t' * (a : Y) * t'⁻¹) * (t' * (b : Y) * t'⁻¹)
    group)
  have hττ : ∀ g : ↥N, τ (τ g) = g := by
    intro g
    apply Subtype.ext
    show t' * (t' * (g : Y) * t'⁻¹) * t'⁻¹ = g
    rw [ht'inv]
    calc t' * (t' * (g : Y) * t') * t' = (t' * t') * (g : Y) * (t' * t') := by group
      _ = g := by rw [ht'2]; group
  let A := (ZMod (2 ^ (m + 1)))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (2 ^ (m + 1)))ˣ)
  let ψ : ↥N →* A := (QuotientGroup.mk' (Subgroup.zpowers (-1 : (ZMod (2 ^ (m + 1)))ˣ))).comp
    (α * α.comp τ)
  have hψ : ∀ g : ↥N, ψ g = QuotientGroup.mk (α g * α (τ g)) := fun g => rfl
  have hinv : ∀ (g : Y) (hg : g ∈ N) (hg' : t' * g * t'⁻¹ ∈ N),
      ψ ⟨t' * g * t'⁻¹, hg'⟩ = ψ ⟨g, hg⟩ := by
    intro g hg hg'
    have e : τ ⟨g, hg⟩ = ⟨t' * g * t'⁻¹, hg'⟩ := rfl
    rw [← e, hψ, hψ, hττ, mul_comm]
  obtain ⟨Ψ, hΨ1, hΨ2⟩ := exists_extHom (A := A) (P := (S₁ : Subgroup Y)) (N := N)
    (fun g hg => (T7F2.mem_Nsub.mp hg).1) hT.ht'S ht'2 hT.t'_not_mem_N (fun g hg => hT.S_cover hg)
    (fun g hg => hT.N_conj hg) ψ hinv
  have hs := hyp.std.setting
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := hs.stand.mem
  have hzK : IsUniqueInvolution (tightCore R) t := hs.hz
  have hxR : x ∈ R₁ := c.ha
  have hxS : x ∈ (S₁ : Subgroup Y) := hyp.hR.2.2 hxR
  have hα1 : ∀ u : ↥N, (u : Y) * x = x * (u : Y) → α u = 1 := fun u hu =>
    alpha_eq_one c hα (by rw [mul_inv_eq_iff_eq_mul]; exact hu)
  have hone : ∀ q : (ZMod (2 ^ (m + 1)))ˣ, q = 1 ∨ q = -1 →
      q ∈ Subgroup.zpowers (-1 : (ZMod (2 ^ (m + 1)))ˣ) := by
    rintro q (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  have hsd : ∀ (u : Y) (hu : u ∈ N), u * u = 1 → (∃ y₁ : Y, y₁ * t * y₁⁻¹ = u) → u ≠ t →
      α ⟨u, hu⟩ = -1 := by
    intro u huN hu2 ⟨y₁, hy₁⟩ hut
    obtain ⟨i, j, -, hx, hy⟩ := s.coord_of_mem huN
    have hno : ¬ ∃ w ∈ R₁, orderOf w = 4 ∧ w * u = u * w := by
      rintro ⟨w, hwR, hw4, hwc⟩
      have hwK : w ∈ tightCore R := hyp.hR.2.1 hwR
      exact not_commute_ord4 hyp hK hzK (y := y₁) (by rw [hy₁]; exact hut) hwK hw4
        (by rw [hy₁]; exact hwc.symm)
    obtain ⟨hdvd, -⟩ := sd_coord c hm2 hu2 hx hy hno
    exact alpha_eq_neg_one c hα (h := ⟨u, huN⟩) hx hdvd
  refine ⟨A, inferInstance, Ψ, ?_, ?_, ?_⟩
  ·
    intro g hg hgR
    have hgN : g ∈ N := by
      rcases hgR with h | h
      exacts [hT.R_le_N h, hT.R'_le_N h]
    rw [hΨ1 g hg hgN, hψ, QuotientGroup.eq_one_iff]
    rcases hgR with h | h
    · have h1 := alpha_eq_pm_one_of_mem_R c hα (h := ⟨g, hgN⟩) h
      have hτ : t' * g * t'⁻¹ ∈ R₂ := by
        have := conj_mem_conjSub (n := t') h
        rwa [hT.ht'R] at this
      have h2 : α (τ ⟨g, hgN⟩) = 1 := hα1 _ (hT.hcomm x hxR _ hτ).symm
      rw [h2, mul_one]
      exact hone _ h1
    · have h1 : α ⟨g, hgN⟩ = 1 := hα1 _ (hT.hcomm x hxR g h).symm
      have hτ : t' * g * t'⁻¹ ∈ R₁ := by
        have := conj_mem_conjSub (n := t') h
        rwa [hT.ht'R'] at this
      have h2 := alpha_eq_pm_one_of_mem_R c hα (h := τ ⟨g, hgN⟩) hτ
      rw [h1, one_mul]
      exact hone _ h2
  ·
    intro g hg hg2 ⟨y₀, hy₀⟩
    by_cases hgN : g ∈ N
    · rw [hΨ1 g hg hgN, hψ, QuotientGroup.eq_one_iff]
      by_cases hgt : g = t
      · have h1 : α ⟨g, hgN⟩ = 1 := hα1 _ (by
          show g * x = x * g
          rw [hgt]; exact (hyp.hzS x hxS).symm)
        have h2 : α (τ ⟨g, hgN⟩) = 1 := hα1 _ (by
          show t' * g * t'⁻¹ * x = x * (t' * g * t'⁻¹)
          have e : t' * g * t'⁻¹ = g := by
            rw [hgt]
            have := hyp.hzS t' hT.ht'S
            calc t' * t * t'⁻¹ = (t * t') * t'⁻¹ := by rw [this]
              _ = t := by group
          rw [e, hgt]; exact (hyp.hzS x hxS).symm)
        rw [h1, h2, mul_one]
        exact Subgroup.one_mem _
      · have h1 := hsd g hgN hg2 ⟨y₀, hy₀⟩ hgt
        have hτN : t' * g * t'⁻¹ ∈ N := hT.N_conj hgN
        have h2 : α (τ ⟨g, hgN⟩) = -1 := by
          refine hsd (t' * g * t'⁻¹) hτN ?_ ⟨t' * y₀, ?_⟩ ?_
          · calc t' * g * t'⁻¹ * (t' * g * t'⁻¹) = t' * (g * g) * t'⁻¹ := by group
              _ = 1 := by rw [hg2]; group
          · rw [← hy₀]; group
          · intro hc
            apply hgt
            have e : g = t'⁻¹ * (t' * g * t'⁻¹) * t' := by group
            rw [e, hc]
            have := hyp.hzS t' hT.ht'S
            calc t'⁻¹ * t * t' = t'⁻¹ * (t * t') := by group
              _ = t'⁻¹ * (t' * t) := by rw [this]
              _ = t := by group
        rw [h1, h2, neg_mul_neg, one_mul]
        exact Subgroup.one_mem _
    · have htg : t' * g ∈ N := (hT.S_cover hg).resolve_left hgN
      rw [hΨ2 g hg htg, hψ, QuotientGroup.eq_one_iff]
      have hτ : τ ⟨t' * g, htg⟩ = (⟨t' * g, htg⟩ : ↥N)⁻¹ := by
        apply Subtype.ext
        show t' * (t' * g) * t'⁻¹ = (t' * g)⁻¹
        have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
        rw [mul_inv_rev, hgi, ht'inv]
        calc t' * (t' * g) * t' = (t' * t') * g * t' := by group
          _ = g * t' := by rw [ht'2, one_mul]
      rw [hτ, map_inv, mul_inv_cancel]
      exact Subgroup.one_mem _
  ·
    intro a ha ha2 hF hΨa
    have haN : a ∈ N := hT.mem_N_of_conj_R' ha (mem_normalizer_iff_conjSub_eq.mp hF.1)
    rw [hΨ1 a ha haN, hψ, QuotientGroup.eq_one_iff] at hΨa
    have hF₁ : IsFAut R₁ (t' * a * t'⁻¹) := by
      have := T7U.isFAut_conjSub hF t'
      rwa [hT.ht'R'] at this
    have ha'N : t' * a * t'⁻¹ ∈ N := hT.N_conj haN
    have ha'2 : (t' * a * t'⁻¹) * (t' * a * t'⁻¹) ∈ Subgroup.zpowers t := by
      have : (t' * a * t'⁻¹) * (t' * a * t'⁻¹) = 1 := by
        calc _ = t' * (a * a) * t'⁻¹ := by group
          _ = 1 := by rw [ha2]; group
      rw [this]
      exact Subgroup.one_mem _
    obtain ⟨-, hx', -⟩ := T7U.coord_of_isFAut hT.hqR hT.hzR s ha'N hF₁ ha'2
    have hαa' : ((α (τ ⟨a, haN⟩) : (ZMod (2 ^ (m + 1)))ˣ) : ZMod (2 ^ (m + 1))) =
        ((1 + 2 ^ m : ℤ) : ZMod (2 ^ (m + 1))) :=
      alpha_cast_eq c hα (h := τ ⟨a, haN⟩) (i := 1 + 2 ^ m) hx'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hΨa
    have hε : α ⟨a, haN⟩ * α (τ ⟨a, haN⟩) = 1 ∨ α ⟨a, haN⟩ * α (τ ⟨a, haN⟩) = -1 := by
      rcases Int.even_or_odd k with he | ho
      · left; rw [← hk]; exact he.neg_one_zpow
      · right; rw [← hk]; exact ho.neg_one_zpow
    set β : ZMod (2 ^ (m + 1)) := ((α ⟨a, haN⟩ : (ZMod (2 ^ (m + 1)))ˣ) : ZMod (2 ^ (m + 1)))
      with hβ
    have hE : ((1 + 2 ^ m : ℤ) : ZMod (2 ^ (m + 1))) = 1 + 2 ^ m := by push_cast; rfl
    have hsq := one_add_two_pow_sq m (by omega)
    have hcast : β * (1 + 2 ^ m) = 1 ∨ β * (1 + 2 ^ m) = -1 := by
      rcases hε with h | h
      · left
        have := congrArg Units.val h
        simpa [hαa', hE, Units.val_mul] using this
      · right
        have := congrArg Units.val h
        simpa [hαa', hE, Units.val_mul] using this
    have hdiv : (2 : ℤ) ^ (m + 1) ∣ ((β.val : ℕ) : ℤ) - (1 + 2 ^ m) ∨
        (2 : ℤ) ^ (m + 1) ∣ ((β.val : ℕ) : ℤ) - (-1 + 2 ^ m) := by
      have hM : (((2 ^ (m + 1) : ℕ)) : ℤ) = (2 : ℤ) ^ (m + 1) := by push_cast; rfl
      have hval : (((β.val : ℕ) : ℤ) : ZMod (2 ^ (m + 1))) = β := by
        simp [hβ]
      rcases hcast with h | h
      · left
        have hb : β = 1 + 2 ^ m := by
          calc β = β * ((1 + 2 ^ m) * (1 + 2 ^ m)) := by rw [hsq, mul_one]
            _ = (β * (1 + 2 ^ m)) * (1 + 2 ^ m) := by ring
            _ = 1 + 2 ^ m := by rw [h, one_mul]
        have h5 : (((β.val : ℕ) : ℤ) : ZMod (2 ^ (m + 1))) = ((1 + 2 ^ m : ℤ) : ZMod (2 ^ (m + 1))) := by
          rw [hval, hb, hE]
        have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h5
        rw [hM] at this
        exact dvd_sub_comm.mp this
      · right
        have hb : β = -1 + 2 ^ m := by
          have h1 : β = -(1 + 2 ^ m) := by
            calc β = β * ((1 + 2 ^ m) * (1 + 2 ^ m)) := by rw [hsq, mul_one]
              _ = (β * (1 + 2 ^ m)) * (1 + 2 ^ m) := by ring
              _ = -(1 + 2 ^ m) := by rw [h]; ring
          rw [h1]
          linear_combination (-1 : ZMod (2 ^ (m + 1))) * (two_pow_add_two_pow m)
        have h5 : (((β.val : ℕ) : ℤ) : ZMod (2 ^ (m + 1))) =
            ((-1 + 2 ^ m : ℤ) : ZMod (2 ^ (m + 1))) := by
          rw [hval, hb]; push_cast; rfl
        have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h5
        rw [hM] at this
        exact dvd_sub_comm.mp this
    have hx : a * x * a⁻¹ = x ^ (((β.val : ℕ) : ℤ)) := by
      rw [zpow_natCast]; exact hα ⟨a, haN⟩
    exact classify_fAut s hm2 hN2 hT.hqR hT.hzR haN ha2 hx hdiv

end Psi

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
