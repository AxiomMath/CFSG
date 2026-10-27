module

public import CFSG.GroupTheory.Extraspecial2PG
public import CFSG.GroupTheory.ExtraspecialCentralizerInnerAut
public import CFSG.GroupTheory.SupCommute
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.CoprimeDecomp

public section

namespace CFSG.GroupTheory

open Subgroup
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_eq_inf_centralizer_inf_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {F P : Subgroup G} (hF : IsExtraspecial2 F) (hP : IsPGroup p P)
    (hNP : P ≤ normalizer (F : Set G)) (hnot : ¬ P ≤ centralizer (F : Set G)) :
    ⁅P, F⁆ = F ⊓ centralizer ((F ⊓ centralizer (P : Set G) : Subgroup G) : Set G) ∧
      (center F).map F.subtype ≤ ⁅P, F⁆ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hFe : IsExtraspecialPGroup 2 F := CFSG.IsExtraspecial2.toIsExtraspecialPGroup hF
  set Z : Subgroup G := (center F).map F.subtype with hZ
  set C : Subgroup G := F ⊓ centralizer (P : Set G) with hC
  set K : Subgroup G := ⁅P, F⁆ with hK
  have hZF : ⁅F, F⁆ = Z := hF.2.1
  have hZcard : Nat.card Z = 2 := by rw [← hZF]; exact hF.2.2
  have hPZ : ∀ n ∈ P, ∀ c ∈ Z, n * c * n⁻¹ = c := by
    intro n hn c hc
    obtain ⟨c', hc', rfl⟩ := hc
    have h1 := mulAut_apply_eq_of_mem_center hFe.2.2.2 (F.normalizerMonoidHom ⟨n, hNP hn⟩) hc'
    exact congrArg Subtype.val h1
  have hcop : Nat.Coprime p (Nat.card F) := by
    obtain ⟨n, hn⟩ := hF.1.exists_card_eq
    rw [hn]
    refine Nat.prime_two.coprime_pow_of_not_dvd (a := p) (m := n) ?_
    intro h2p
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p).symm
  have hdecomp : F ≤ C ⊔ K := by
    have h1 := le_sup_centralizer_commutator (X := G) (p := p) (Y := F) (B := P) hP hNP hcop
    simpa only [hC, hK, Subgroup.commutator_comm] using h1
  have hKF : K ≤ F := by
    simpa only [hK, Subgroup.commutator_comm] using
      commutator_le_of_normalizer (Y := F) (B := P) hNP
  have hCK : ⁅C, K⁆ = ⊥ := by
    have hZP : ⁅Z, P⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have h1 := hPZ n hn c hc
      calc n * c = n * c * n⁻¹ * n := by group
        _ = c * n := by rw [h1]
    have h1 : ⁅⁅F, C⁆, P⁆ = ⊥ := by
      have hle : ⁅⁅F, C⁆, P⁆ ≤ ⁅Z, P⁆ :=
        Subgroup.commutator_mono (hZF ▸ Subgroup.commutator_mono le_rfl inf_le_left) le_rfl
      exact le_bot_iff.mp (hZP ▸ hle)
    have h2 : ⁅⁅C, P⁆, F⁆ = ⊥ := by
      have hCP : ⁅C, P⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
      rw [hCP]
      simp
    have hKC : ⁅⁅P, F⁆, C⁆ = ⊥ :=
      Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := P) (H₂ := F) (H₃ := C) h1 h2
    simpa only [hK, Subgroup.commutator_comm] using hKC
  have hcomm : ∀ c ∈ C, ∀ k ∈ K, Commute c k := by
    intro c hc k hk
    have hc' : c ∈ centralizer (K : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hCK hc
    exact (Subgroup.mem_centralizer_iff.mp hc' k hk).symm
  have hFcentr : F ⊓ centralizer (F : Set G) = Z :=
    (CFSG.center_map_subtype_eq_inf_centralizer F).symm
  have hZK : Z ≤ K := by
    have hKne : K ≠ ⊥ := fun hbot => hnot (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
    have hFnorm : F ≤ normalizer (K : Set G) := by
      have hCnorm : C ≤ normalizer (K : Set G) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hCK).trans
          (Subgroup.centralizer_le_normalizer (K : Set G))
      have hKnorm : K ≤ normalizer (K : Set G) := Subgroup.le_normalizer
      exact hdecomp.trans (sup_le hCnorm hKnorm)
    have hKFK : ⁅K, F⁆ ≤ K := commutator_le_of_normalizer (Y := K) (B := F) hFnorm
    have hKFZ : ⁅K, F⁆ ≤ Z := (Subgroup.commutator_mono hKF le_rfl).trans hZF.le
    have hZKne : Z ⊓ K ≠ ⊥ := by
      intro hbot
      have hKFbot : ⁅K, F⁆ = ⊥ := by
        refine le_bot_iff.mp ?_
        calc ⁅K, F⁆ ≤ K ⊓ Z := le_inf hKFK hKFZ
          _ = ⊥ := by simpa only [inf_comm] using hbot
      have hKcent : K ≤ centralizer (F : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKFbot
      have hKZ : K ≤ Z := by
        calc K ≤ F ⊓ centralizer (F : Set G) := le_inf hKF hKcent
          _ = Z := hFcentr
      apply hKne
      refine le_bot_iff.mp ?_
      calc K ≤ K ⊓ Z := le_inf le_rfl hKZ
        _ = ⊥ := by simpa only [inf_comm] using hbot
    have hdvd : Nat.card (Z ⊓ K : Subgroup G) ∣ Nat.card Z :=
      Subgroup.card_dvd_of_le inf_le_left
    rw [hZcard] at hdvd
    have hne1 : Nat.card (Z ⊓ K : Subgroup G) ≠ 1 := by
      intro h1
      exact hZKne ((Subgroup.eq_bot_iff_card (H := (Z ⊓ K))).mpr h1)
    have h2 : Nat.card (Z ⊓ K : Subgroup G) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    have hEq : Z ⊓ K = Z :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hZcard, h2])
    simpa only [hEq] using (inf_le_right : Z ⊓ K ≤ K)
  refine ⟨le_antisymm (le_inf hKF ?_) ?_, hZK⟩
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by
      rw [Subgroup.commutator_comm]; exact hCK)
  · rintro f ⟨hfF, hfC⟩
    obtain ⟨c, hc, k, hk, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp (hdecomp hfF)
    have hcF : c ∈ F := hc.1
    have hcC : ∀ c' ∈ C, c' * c = c * c' := by
      intro c' hc'
      have h1 : c' * (c * k) = (c * k) * c' := (Subgroup.mem_centralizer_iff.mp hfC c' hc')
      have h2 : c' * k = k * c' := (hcomm c' hc' k hk).eq
      have h3 : c' * c * k = c * c' * k := by
        calc c' * c * k = c' * (c * k) := by rw [mul_assoc]
          _ = (c * k) * c' := h1
          _ = c * (k * c') := by rw [mul_assoc]
          _ = c * (c' * k) := by rw [h2]
          _ = c * c' * k := by rw [mul_assoc]
      exact mul_right_cancel h3
    have hcZ : c ∈ Z := by
      rw [← hFcentr, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      refine ⟨hcF, fun x hx => ?_⟩
      obtain ⟨c', hc', k', hk', rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp (hdecomp hx)
      have h1 : c * k' = k' * c := (hcomm c hc k' hk').eq
      calc c' * k' * c = c' * (k' * c) := by rw [mul_assoc]
        _ = c' * (c * k') := by rw [h1]
        _ = c' * c * k' := by rw [mul_assoc]
        _ = c * c' * k' := by rw [hcC c' hc']
        _ = c * (c' * k') := by rw [mul_assoc]
    exact K.mul_mem (hZK hcZ) hk

end CFSG.GroupTheory
