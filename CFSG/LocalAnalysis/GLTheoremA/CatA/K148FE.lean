module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148FD
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148FFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD91

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K148F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

variable {G : Type} [Group G] [Finite G]

theorem k148f_G2_simple' {P : Type} [Group P] [Finite P] {q : TauCeti.PrimePower} (hq2p : q.p = 2)
    (hq : 2 ≤ q.exponent) (hP : catalogIs P (CFSG.LocalAnalysis.GLTheoremA.I2023.isTD4Of q))
    {F : Subgroup P} (hF : catalogIs ↥F (isG2n q.exponent)) : IsSimpleGroup ↥F ∧ 3 ∣ Nat.card ↥F := by
  have hcard : q.card = 2 ^ q.exponent := by
    rw [TauCeti.PrimePower.card_def, hq2p]
  have h2 : 2 < 2 ^ q.exponent := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hq
  have h3 : ¬ 3 ∣ 2 ^ q.exponent := fun h =>
    absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have hPbig : catalogIs P (onLie isTrialityD4Big) := by
    refine catalogIs_imp ?_ hP
    intro i hi
    cases i with
    | lie j =>
      obtain ⟨d, hv⟩ := j
      cases d with
      | trialityD4 q' =>
        have hq' : q'.card = q.card := hi
        show 2 < q'.card ∧ ¬ 3 ∣ q'.card
        rw [hq', hcard]
        exact ⟨h2, h3⟩
      | _ => exact (show False from hi).elim
    | _ => exact (show False from hi).elim
  have hFbig : catalogIs ↥F (onLie isG2Big) := by
    refine catalogIs_imp ?_ hF
    intro i hi
    cases i with
    | lie j =>
      obtain ⟨d, hv⟩ := j
      cases d with
      | G2 q' =>
        obtain ⟨hp, he⟩ : q'.p = 2 ∧ q'.exponent = q.exponent := hi
        show 2 < q'.card ∧ ¬ 3 ∣ q'.card
        have hc' : q'.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hp, he]
        rw [hc']
        exact ⟨h2, h3⟩
      | _ => exact (show False from hi).elim
    | _ => exact (show False from hi).elim
  obtain ⟨hs, -, h3F⟩ := (kd91_holds P hPbig).2.2 ↥F hFbig
  exact ⟨hs, h3F⟩

theorem k148f_fieldAut_transport {p : ℕ} {X Y : Type} [Group X] [Group Y] (hY : commutator Y = ⊤)
    (e : Y ≃* X) {φ : MulAut X} {ψ : MulAut Y} (hcomp : ∀ a : Y, φ (e a) = e (ψ a))
    (h : K148FFieldAut p X φ) : K148FFieldAut p Y ψ := by
  let he' : Y ⧸ Subgroup.center Y ≃* X ⧸ Subgroup.center X := k148f_psimple_congr e
  unfold K148FFieldAut at h ⊢
  refine lemma102_marking_transport hY he' (fun lab R _ I F θ hP => ?_) h
  refine lemma102_primeField_mono hP (fun α hα => ?_)
  intro a b hab
  have hab' : φ (e a) = e b := by rw [hcomp a, hab]
  have key := hα (e a) (e b) hab'
  have ea : ∀ l : Y, he' (QuotientGroup.mk l) = QuotientGroup.mk (e l) := by
    intro l
    unfold he' k148f_psimple_congr
    exact QuotientGroup.congr_mk _ _ _ _ l
  show α (θ (he' (QuotientGroup.mk a))) = θ (he' (QuotientGroup.mk b))
  rw [ea a, ea b]
  exact key

end CFSG.LocalAnalysis.GLTheoremA.K148F

end
