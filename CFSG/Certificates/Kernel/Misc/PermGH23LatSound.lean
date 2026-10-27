module

public import Certificates.Data.Kernel.Misc.PermGH23Lat
public import CFSG.Certificates.Kernel.Misc.PermGH23Clos
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.Misc.GH23

open Equiv CFSG.KC.LQT CFSG.KC.Misc.Clos
  CFSG.OddStandard.SmallF3.HarrisU33.GH23Data CFSG.OddStandard.SmallF3.HarrisU33.Outside

theorem gh23Code_mul3 (a b c : Perm (Fin 8)) :
    gh23Code (a * b * c) = mul8 (mul8 (gh23Code a) (gh23Code b)) (gh23Code c) := by
  rw [gh23_enc.enc_mul, gh23_enc.enc_mul]

theorem gh23_covAt_sound {H : Subgroup (Perm (Fin 8))} {N nR k : ℕ} {EP EA RA W : ℕ → ℕ}
    (hP : ExactList gh23Code H N EP) (h : covAt EP EA RA W N nR k = true)
    {σ : Perm (Fin 8)} (hσ : gh23Code σ = EA k) :
    ∃ j < nR, ∀ ρ : Perm (Fin 8), gh23Code ρ = EA (RA j) →
      ∃ π ∈ H, ∃ κ ∈ H, π * ρ * κ = σ := by
  unfold covAt at h
  simp only [P.letB_eq] at h
  obtain ⟨hp, h⟩ := P.andB_iff.1 h
  obtain ⟨hq, h⟩ := P.andB_iff.1 h
  obtain ⟨hj, he⟩ := P.andB_iff.1 h
  refine ⟨_, Nat.blt_eq.mp hj, fun ρ hρ => ?_⟩
  obtain ⟨π, hπ, hπc⟩ := hP.1 _ (Nat.blt_eq.mp hp)
  obtain ⟨κ, hκ, hκc⟩ := hP.1 _ (Nat.blt_eq.mp hq)
  refine ⟨π, hπ, κ, hκ, gh23_code_injective ?_⟩
  rw [gh23Code_mul3, hπc, hρ, hκc, hσ]
  exact Nat.eq_of_beq_eq_true he

theorem gh23_wVal_mem {K H : Subgroup (Perm (Fin 8))} {N r X : ℕ} {EP : ℕ → ℕ}
    (hP : ExactList gh23Code H N EP) (hHK : H ≤ K) {ρ : Perm (Fin 8)} (hρ : ρ ∈ K)
    (hr : gh23Code ρ = r) :
    ∀ n, (∀ l ≤ n, wIdx X l < N) → ∃ τ ∈ K, gh23Code τ = wVal EP r X n := by
  intro n
  induction n with
  | zero =>
    intro hl
    obtain ⟨π, hπ, hc⟩ := hP.1 _ (hl 0 le_rfl)
    exact ⟨π, hHK hπ, hc⟩
  | succ n ih =>
    intro hl
    obtain ⟨τ, hτ, hc⟩ := ih fun l hl' => hl l (Nat.le_succ_of_le hl')
    obtain ⟨π, hπ, hπc⟩ := hP.1 _ (hl (n + 1) le_rfl)
    refine ⟨τ * ρ * π, K.mul_mem (K.mul_mem hτ hρ) (hHK hπ), ?_⟩
    change _ = mul8 (mul8 (wVal EP r X n) r) (EP (wIdx X (n + 1)))
    rw [gh23Code_mul3, hc, hr, hπc]

theorem gh23_joinAt_sound {N nG NA R : ℕ} {EP G EA NQ NGQ WX : ℕ → ℕ} {EQ GQ : ℕ → ℕ → ℕ}
    {cs : List ℕ} {Qg : ℕ → List ℕ}
    (hcs : cs = (List.range nG).map G) (hP : ExactList gh23Code (gh23Sub cs) N EP)
    (hQg : ∀ t < 41, Qg t = (List.range (NGQ t)).map (GQ t))
    (hQ : ∀ t < 41, ExactList gh23Code (gh23Sub (Qg t)) (NQ t) (EQ t))
    (h : joinAt EP N G nG EA NA EQ NQ NGQ GQ R WX = true) :
    fld R 0 15 < NA ∧ ∃ t < 41, ∀ ρ : Perm (Fin 8), gh23Code ρ = EA (fld R 0 15) →
      gh23Sub cs ⊔ Subgroup.zpowers ρ = gh23Sub (Qg t) := by
  unfold joinAt at h
  simp only [P.letB_eq] at h
  obtain ⟨ha, h⟩ := P.andB_iff.1 h
  obtain ⟨ht, h⟩ := P.andB_iff.1 h
  obtain ⟨hx, h⟩ := P.andB_iff.1 h
  obtain ⟨hx1, hx2⟩ := P.andB_iff.1 hx
  obtain ⟨hg, hw⟩ := P.andB_iff.1 h
  rw [P.allN_iff] at hg hw
  have ht' := Nat.blt_eq.mp ht
  refine ⟨Nat.blt_eq.mp ha, _, ht', fun ρ hρ => ?_⟩
  have hQt := hQ _ ht'
  have memQ : ∀ {σ : Perm (Fin 8)} {y : ℕ}, y < NQ (fld R 15 6) →
      EQ (fld R 15 6) y = gh23Code σ → σ ∈ gh23Sub (Qg (fld R 15 6)) := by
    intro σ y hy he
    obtain ⟨g, hg, hc⟩ := hQt.1 y hy
    rwa [gh23_code_injective (hc.trans he)] at hg
  apply le_antisymm
  · apply sup_le
    · refine (Subgroup.closure_le _).2 fun σ hσ => ?_
      change gh23Code σ ∈ cs at hσ
      rw [hcs, List.mem_map] at hσ
      obtain ⟨i, hi, hiσ⟩ := hσ
      obtain ⟨hy1, hy2⟩ := P.andB_iff.1 (hg i (List.mem_range.mp hi))
      exact memQ (Nat.blt_eq.mp hy1) ((Nat.eq_of_beq_eq_true hy2).trans hiσ)
    · rw [Subgroup.zpowers_le]
      exact memQ (Nat.blt_eq.mp hx1) ((Nat.eq_of_beq_eq_true hx2).trans hρ.symm)
  · refine (Subgroup.closure_le _).2 fun σ hσ => ?_
    change gh23Code σ ∈ Qg _ at hσ
    rw [hQg _ ht', List.mem_map] at hσ
    obtain ⟨i, hi, hiσ⟩ := hσ
    have hwi := hw i (List.mem_range.mp hi)
    unfold wordOK at hwi
    simp only [P.letB_eq] at hwi
    obtain ⟨hc, hwi⟩ := P.andB_iff.1 hwi
    obtain ⟨hl, hv⟩ := P.andB_iff.1 hwi
    rw [P.allN_iff] at hl
    have hc' := Nat.blt_eq.mp hc
    obtain ⟨τ, hτ, hτc⟩ := gh23_wVal_mem hP le_sup_left
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers ρ)) hρ (fld (WX i) 0 5 - 1)
      (fun l hl' => Nat.blt_eq.mp (hl l (by omega)))
    have : τ = σ := gh23_code_injective (hτc.trans ((Nat.eq_of_beq_eq_true hv).trans hiσ))
    exact this ▸ hτ

end CFSG.KC.Misc.GH23

end
