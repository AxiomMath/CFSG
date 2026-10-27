module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44GolayStab
public import Certificates.Certificate25300

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.EvenSporadicStandard.Wong77.Module MulAction

@[expose] def golayFix (k : ℕ) : Subgroup (Equiv.Perm (Fin 23)) where
  carrier := {g | g ∈ permStab golayCode ∧ ∀ x : Fin 23, x.val < k → g x = x}
  mul_mem' := fun {a b} ha hb =>
    ⟨(permStab golayCode).mul_mem ha.1 hb.1, fun x hx => by
      rw [Equiv.Perm.mul_apply, hb.2 x hx, ha.2 x hx]⟩
  one_mem' := ⟨(permStab golayCode).one_mem, fun _ _ => rfl⟩
  inv_mem' := fun {a} ha =>
    ⟨(permStab golayCode).inv_mem ha.1, fun x hx => by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact (ha.2 x hx).symm⟩

theorem mem_golayFix {k : ℕ} {g : Equiv.Perm (Fin 23)} :
    g ∈ golayFix k ↔ g ∈ permStab golayCode ∧ ∀ x : Fin 23, x.val < k → g x = x := Iff.rfl

theorem golayFix_one : permStab golayCode ⊓ stabilizer (Equiv.Perm (Fin 23)) (0 : Fin 23) =
    golayFix 1 := by
  ext g
  rw [Subgroup.mem_inf, mem_stabilizer_iff, mem_golayFix]
  refine and_congr_right fun _ => ⟨fun h x hx => ?_, fun h => h 0 (by decide)⟩
  have : x = 0 := Fin.ext (by simpa using hx)
  rw [this]
  exact h

theorem golayFix_inf_stabilizer {k : ℕ} (hk : k < 23) :
    golayFix k ⊓ stabilizer (Equiv.Perm (Fin 23)) (golayBasePt k) = golayFix (k + 1) := by
  have hv : (golayBasePt k).val = k := Nat.mod_eq_of_lt hk
  ext g
  rw [Subgroup.mem_inf, mem_stabilizer_iff, mem_golayFix, mem_golayFix]
  constructor
  · rintro ⟨⟨hg, h⟩, hb⟩
    refine ⟨hg, fun x hx => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | hx
    · exact h x hx
    · have : x = golayBasePt k := Fin.ext (by rw [hv]; exact hx)
      rw [this]
      exact hb
  · rintro ⟨hg, h⟩
    exact ⟨⟨hg, fun x hx => h x (Nat.lt_succ_of_lt hx)⟩, h _ (by rw [hv]; exact Nat.lt_succ_self k)⟩

theorem card_golayFix_le {k k' c : ℕ} (hk : k < 23) (hk' : k' = k + 1) (S : Finset (Fin 23))
    (hc : S.card = c) (h : ∀ g ∈ golayFix k, g (golayBasePt k) ∈ S) :
    Nat.card (golayFix k) ≤ c * Nat.card (golayFix k') := by
  have := card_le_mul_card_inf_stabilizer (golayFix k) (golayBasePt k) S h
  rwa [golayFix_inf_stabilizer hk, hc, ← hk'] at this

theorem card_permStab_golay_zero_le :
    Nat.card ↥(permStab golayCode ⊓ stabilizer (Equiv.Perm (Fin 23)) (0 : Fin 23)) ≤ 443520 := by
  obtain ⟨h1, h2, h3, h4, h5, hinj⟩ := golayAutCheck_sound Certificates.certificate25300
  rw [golayFix_one]
  have s1 := card_golayFix_le (k := 1) (k' := 2) (by norm_num) (by norm_num) _ h1 fun g hg =>
    mem_colClass_golayCol1 hg.1 hg.2 (golayBasePt 1)
  have s2 := card_golayFix_le (k := 2) (k' := 3) (by norm_num) (by norm_num) _ h2 fun g hg =>
    mem_colClass_golayCol1 hg.1 hg.2 (golayBasePt 2)
  have s3 := card_golayFix_le (k := 3) (k' := 4) (by norm_num) (by norm_num) _ h3 fun g hg =>
    mem_colClass_golayCol1 hg.1 hg.2 (golayBasePt 3)
  have s4 := card_golayFix_le (k := 4) (k' := 5) (by norm_num) (by norm_num) _ h4 fun g hg =>
    mem_colClass_golayCol1 hg.1 hg.2 (golayBasePt 4)
  have s5 := card_golayFix_le (k := 5) (k' := 6) (by norm_num) (by norm_num) _ h5 fun g hg =>
    mem_colClass_golayCol1 hg.1 hg.2 (golayBasePt 5)
  have s6 : Nat.card (golayFix 6) = 1 := by
    have : golayFix 6 = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun g hg =>
      eq_one_of_fix_six hinj hg.1 hg.2
    rw [this, Subgroup.card_bot]
  omega

end CFSG.EvenSporadicStandard.TwoFi22.DS81
