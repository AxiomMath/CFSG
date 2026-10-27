module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0ModDiag
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0ModNrm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0ModDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0ModCoord

public section

namespace CFSG.OddStandard.SmallF3.Omega

open T84Mod Matrix Certificates.Asc82NormA6
open Certificates.A5GL42 (Mat4)

variable {G : Type} [Group G] {E B : Subgroup G} {hBE : B ≤ E} {u : MulAut ↥E}
  {hfix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B} {A : Subgroup (MulAut ↥E)}
  {hAu : ∀ a ∈ A, a * u = u * a}

private theorem t84b_frame_sq (F : Frame E B hBE u hfix A hAu) {h : MulAut ↥E}
    (hhu : h * u = u * h) (hh2B : ∀ e : ↥E, (e : G) ∈ B → h (h e) = e)
    {X : Mat4}
    (hXB : ∀ b : ↥B, Multiplicative.toAdd (F.eB (resB hBE u hfix h hhu b)) =
      X *ᵥ Multiplicative.toAdd (F.eB b)) : X * X = 1 := by
  have hg : (h * h) * u = u * (h * h) := by
    calc (h * h) * u = h * (h * u) := by rw [mul_assoc]
      _ = h * (u * h) := by rw [hhu]
      _ = (h * u) * h := by rw [mul_assoc]
      _ = (u * h) * h := by rw [hhu]
      _ = u * (h * h) := by rw [mul_assoc]
  have hresmul : resB hBE u hfix (h * h) hg =
      resB hBE u hfix h hhu * resB hBE u hfix h hhu :=
    resB_mul hBE u hfix h h hhu hhu hg
  have hresid : ∀ b : ↥B, resB hBE u hfix (h * h) hg b = b := by
    intro b
    have hinj : Function.Injective (embB hBE) :=
      fun _ _ hb => Subtype.ext (congrArg (fun e : ↥E => (e : G)) hb)
    apply hinj
    rw [embB_resB]
    change h (h (embB hBE b)) = embB hBE b
    exact hh2B (embB hBE b) b.2
  have h1 : ∀ b : ↥B, Multiplicative.toAdd (F.eB (resB hBE u hfix (h * h) hg b)) =
      (X * X) *ᵥ Multiplicative.toAdd (F.eB b) := by
    intro b
    rw [hresmul]
    change Multiplicative.toAdd
        (F.eB (resB hBE u hfix h hhu (resB hBE u hfix h hhu b))) =
      (X * X) *ᵥ Multiplicative.toAdd (F.eB b)
    rw [hXB (resB hBE u hfix h hhu b), hXB b, Matrix.mulVec_mulVec]
  have h2 : ∀ b : ↥B, Multiplicative.toAdd (F.eB (resB hBE u hfix (h * h) hg b)) =
      1 *ᵥ Multiplicative.toAdd (F.eB b) := by
    intro b
    rw [hresid b, Matrix.one_mulVec]
  exact Frame.matrix_unique F (h * h) hg (X * X) 1 h1 h2

private theorem t84b_frame_comm_mat (F : Frame E B hBE u hfix A hAu) {h k : MulAut ↥E}
    (hhu : h * u = u * h) (hku : k * u = u * k)
    (hkh : ∀ e : ↥E, (e : G) ∈ B → k (h e) = h (k e))
    {X Y : Mat4}
    (hXB : ∀ b : ↥B, Multiplicative.toAdd (F.eB (resB hBE u hfix h hhu b)) =
      X *ᵥ Multiplicative.toAdd (F.eB b))
    (hYB : ∀ b : ↥B, Multiplicative.toAdd (F.eB (resB hBE u hfix k hku b)) =
      Y *ᵥ Multiplicative.toAdd (F.eB b)) : Y * X = X * Y := by
  have hkuh : (k * h) * u = u * (k * h) := by
    calc (k * h) * u = k * (h * u) := by rw [mul_assoc]
      _ = k * (u * h) := by rw [hhu]
      _ = (k * u) * h := by rw [mul_assoc]
      _ = (u * k) * h := by rw [hku]
      _ = u * (k * h) := by rw [mul_assoc]
  have hresmul : resB hBE u hfix (k * h) hkuh =
      resB hBE u hfix k hku * resB hBE u hfix h hhu :=
    resB_mul hBE u hfix k h hku hhu hkuh
  have hA : ∀ b : ↥B, Multiplicative.toAdd (F.eB (resB hBE u hfix (k * h) hkuh b)) =
      (Y * X) *ᵥ Multiplicative.toAdd (F.eB b) := by
    intro b
    rw [hresmul]
    change Multiplicative.toAdd
        (F.eB (resB hBE u hfix k hku (resB hBE u hfix h hhu b))) =
      (Y * X) *ᵥ Multiplicative.toAdd (F.eB b)
    rw [hYB (resB hBE u hfix h hhu b), hXB b, Matrix.mulVec_mulVec]
  have hres_eq : ∀ b : ↥B, resB hBE u hfix (k * h) hkuh b =
      resB hBE u hfix h hhu (resB hBE u hfix k hku b) := by
    intro b
    have hinj : Function.Injective (embB hBE) :=
      fun _ _ hb => Subtype.ext (congrArg (fun e : ↥E => (e : G)) hb)
    apply hinj
    calc embB hBE (resB hBE u hfix (k * h) hkuh b)
        = (k * h) (embB hBE b) := embB_resB hBE u hfix (k * h) hkuh b
      _ = k (h (embB hBE b)) := by rw [MulAut.mul_apply]
      _ = h (k (embB hBE b)) := hkh (embB hBE b) b.2
      _ = h (embB hBE (resB hBE u hfix k hku b)) := by rw [embB_resB]
      _ = embB hBE (resB hBE u hfix h hhu (resB hBE u hfix k hku b)) :=
            (embB_resB hBE u hfix h hhu (resB hBE u hfix k hku b)).symm
  have hB : ∀ b : ↥B, Multiplicative.toAdd (F.eB (resB hBE u hfix (k * h) hkuh b)) =
      (X * Y) *ᵥ Multiplicative.toAdd (F.eB b) := by
    intro b
    rw [hres_eq b]
    change Multiplicative.toAdd
        (F.eB (resB hBE u hfix h hhu (resB hBE u hfix k hku b))) =
      (X * Y) *ᵥ Multiplicative.toAdd (F.eB b)
    rw [hXB (resB hBE u hfix k hku b), hYB b, Matrix.mulVec_mulVec]
  exact Frame.matrix_unique F (k * h) hkuh (Y * X) (X * Y) hA hB

private theorem t84b_frame_comm (F : Frame E B hBE u hfix A hAu) {m X Y : Mat4}
    {h' k : MulAut ↥E} (hYX : Y * X = X * Y) (hh' : Acts F.θ h' (Dm m X))
    (hY : Acts F.θ k (Dm m Y) ∨ Acts F.θ k (Dm m Y * blk 1 1)) :
    k * h' = h' * k := by
  have hcommu : Dm m X * blk 1 1 = blk 1 1 * Dm m X := by
    rw [Dm, blk_commute_u]
  rcases hY with hY0 | hY1
  · have hA : Acts F.θ (k * h') (Dm m (Y * X)) := by
      rw [← Dm_mul]
      exact hY0.mul hh'
    have hB : Acts F.θ (h' * k) (Dm m (Y * X)) := by
      have h := hh'.mul hY0
      rw [Dm_mul, ← hYX] at h
      exact h
    exact Acts.ext hA hB
  · have hmat : (Dm m Y * blk 1 1) * Dm m X = Dm m X * (Dm m Y * blk 1 1) := by
      calc (Dm m Y * blk 1 1) * Dm m X
          = Dm m Y * (blk 1 1 * Dm m X) := by rw [mul_assoc]
        _ = Dm m Y * (Dm m X * blk 1 1) := by rw [← hcommu]
        _ = (Dm m Y * Dm m X) * blk 1 1 := by rw [mul_assoc]
        _ = Dm m (Y * X) * blk 1 1 := by rw [Dm_mul]
        _ = Dm m (X * Y) * blk 1 1 := by rw [hYX]
        _ = (Dm m X * Dm m Y) * blk 1 1 := by rw [← Dm_mul]
        _ = Dm m X * (Dm m Y * blk 1 1) := by rw [mul_assoc]
    refine Acts.ext (hY1.mul hh') ?_
    have h := hh'.mul hY1
    rw [← hmat] at h
    exact h

theorem sec8t84FactModB_of_cert : Sec8T84FactModB := by
  intro G _ E B hE hB hBE u A h hu2 hfix hrange hA hAu hAf hhu hhA hh2B hh8
  have hinj : Function.Injective (resHom hBE u hfix A hAu) :=
    resHom_injective hBE u hfix A hAu hAf
  let Hr : Subgroup (MulAut ↥B) := (resHom hBE u hfix A hAu).range
  have hHr : Nonempty (↥Hr ≃* alternatingGroup (Fin 6)) :=
    ⟨(MonoidHom.ofInjective hinj).symm.trans hA.some⟩
  obtain ⟨eB, ψH, hact, -⟩ := sec8t84_a6_conj B hB Hr hHr
  let ψ : ↥A ≃* alternatingGroup (Fin 6) := (MonoidHom.ofInjective hinj).trans ψH
  have hres : ∀ (a : ↥A) (b : ↥B),
      Multiplicative.toAdd (eB (resB hBE u hfix (a : MulAut ↥E) (hAu a a.2) b)) =
        rho ((ψ a : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) *ᵥ
          Multiplicative.toAdd (eB b) := by
    intro a b
    have hcoe : ((MonoidHom.ofInjective hinj a : ↥Hr) : MulAut ↥B) =
        resB hBE u hfix (a : MulAut ↥E) (hAu a a.2) := by
      change resHom hBE u hfix A hAu a = resB hBE u hfix (a : MulAut ↥E) (hAu a a.2)
      rw [resHom_apply]
    have hh := hact (MonoidHom.ofInjective hinj a) b
    rwa [hcoe] at hh
  obtain ⟨θ, hθ, hθu⟩ := exists_adapted E B hE hBE u hu2 hfix hrange eB
  let F : Frame E B hBE u hfix A hAu :=
    { eB := eB, ψ := ψ, θ := θ, res_acts := hres, θ_emb := hθ, θ_u := hθu }
  obtain ⟨m, hm⟩ := Frame.exists_frame F
  obtain ⟨X, hX, hXB⟩ := Frame.normalizer F hm h hhu hhA
  have hXX : X * X = 1 := t84b_frame_sq F hhu hh2B hXB
  have hsq : ∀ h' : MulAut ↥E, Acts F.θ h' (Dm m X) → h' * h' = 1 := by
    intro h' hh'
    have hmul : Acts F.θ (h' * h') (Dm m X * Dm m X) := hh'.mul hh'
    rw [Dm_mul, hXX, Dm_one] at hmul
    exact Acts.ext hmul (acts_one F.θ)
  have hcard : ∀ h' : MulAut ↥E, Acts F.θ h' (Dm m X) →
      Nat.card {e : ↥E // h' e = e} = 64 := by
    intro h' hh'
    rw [Acts.card_fix hh', card_fix_Dm, ← Frame.card_fix_B F h hhu X hXB, hh8]
    norm_num
  have hcomm' : ∀ (k h' : MulAut ↥E), k * u = u * k →
      (∀ a ∈ A, k * a * k⁻¹ ∈ A) → (∀ e : ↥E, (e : G) ∈ B → k (h e) = h (k e)) →
      Acts F.θ h' (Dm m X) → k * h' = h' * k := by
    intro k h' hku hkA hkh hh'
    obtain ⟨Y, hY, hYB⟩ := Frame.normalizer F hm k hku hkA
    exact t84b_frame_comm F (t84b_frame_comm_mat F hhu hku hkh hXB hYB) hh' hY
  rcases hX with hX0 | hX1
  · exact ⟨h, Or.inl rfl, hsq h hX0, hcard h hX0,
      fun k hku hkA hkh => hcomm' k h hku hkA hkh hX0⟩
  · have hh' : Acts F.θ (h * u) (Dm m X) := by
      have hh := hX1.mul F.θ_u
      rwa [mul_assoc, blk_u_mul_self, mul_one] at hh
    exact ⟨h * u, Or.inr rfl, hsq (h * u) hh', hcard (h * u) hh',
      fun k hku hkA hkh => hcomm' k (h * u) hku hkA hkh hh'⟩

end CFSG.OddStandard.SmallF3.Omega
