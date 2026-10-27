module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426Psi
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltZ
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltUtil

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426Lift

variable {Y : Type} [Group Y] [Finite Y]

theorem card_center_dvd_three {K : Subgroup Y} (hK : K.Normal) (hq : CFSG.Open.IsQuasisimple ↥K)
    (hcore : GLAPPrimeCore 3 ↥K = ⊥) {n : ℕ} (hn : 5 ≤ n) (hn7 : n = 7)
    (eK : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin n)) :
    Nat.card (Subgroup.center ↥K) = 1 ∨ Nat.card (Subgroup.center ↥K) = 3 := by
  rcases KD264Z.center_eq_bot_or_three Nat.prime_three (by norm_num) hq hcore hn eK with h | h
  · left
    rw [h, Subgroup.card_bot]
  · right
    exact h.1

theorem exists_lift {K : Subgroup Y} (hK : K.Normal) (hq : CFSG.Open.IsQuasisimple ↥K)
    (hcore : GLAPPrimeCore 3 ↥K = ⊥)
    (eK : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin 7))
    (T0 : Subgroup (alternatingGroup (Fin 7))) (hT0 : Nat.card T0 = 4) :
    ∃ TK : Subgroup ↥K, Nat.card TK = 4 ∧ TK ⊓ Subgroup.center ↥K = ⊥ ∧
      TK ⊔ Subgroup.center ↥K = T0.comap (KD1426Psi.piK K eK) := by
  classical
  set π := KD1426Psi.piK K eK with hπ
  set Z := Subgroup.center ↥K with hZ
  have hZc : Nat.card Z = 1 ∨ Nat.card Z = 3 := card_center_dvd_three hK hq hcore (by norm_num)
    (rfl) eK
  have hker : π.ker = Z := by
    ext k
    rw [MonoidHom.mem_ker, KD1426Psi.piK_eq_one_iff]
  have hrange : T0 ≤ π.range := by
    intro x _
    obtain ⟨k, hk⟩ := KD1426Psi.piK_surjective K eK x
    exact ⟨k, hk⟩
  have hQcard : Nat.card (T0.comap π) = 4 * Nat.card Z := by
    rw [KD264Util.card_comap_eq_mul π T0 hrange, hT0, hker]
  have h4dvd : 2 ^ 2 ∣ Nat.card (T0.comap π) := by
    rw [hQcard]
    rcases hZc with h | h <;> rw [h] <;> norm_num
  obtain ⟨Q1, hQ1⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4dvd
  set TK : Subgroup ↥K := Q1.map (T0.comap π).subtype with hTKdef
  have hTKcard : Nat.card TK = 4 := by
    rw [hTKdef, Subgroup.card_map_of_injective (T0.comap π).subtype_injective]
    norm_num at hQ1
    exact hQ1
  have hTKQ : TK ≤ T0.comap π := by
    intro k hk
    obtain ⟨q, _, rfl⟩ := Subgroup.mem_map.1 hk
    exact q.2
  have hZQ : Z ≤ T0.comap π := by
    intro k hk
    rw [Subgroup.mem_comap]
    have h1 : π k = 1 := (KD1426Psi.piK_eq_one_iff K eK k).2 hk
    rw [h1]
    exact Subgroup.one_mem _
  have hTKbot : TK ⊓ Z = ⊥ := by
    have d1 : Nat.card ↥(TK ⊓ Z) ∣ 4 := by
      rw [← hTKcard]
      exact Subgroup.card_dvd_of_le (inf_le_left : TK ⊓ Z ≤ TK)
    have d2 : Nat.card ↥(TK ⊓ Z) ∣ Nat.card Z :=
      Subgroup.card_dvd_of_le (inf_le_right : TK ⊓ Z ≤ Z)
    have h1 : Nat.card ↥(TK ⊓ Z) = 1 := by
      have hg : Nat.card ↥(TK ⊓ Z) ∣ Nat.gcd 4 (Nat.card Z) := Nat.dvd_gcd d1 d2
      rcases hZc with h | h
      · rw [h] at hg
        simpa using hg
      · rw [h] at hg
        have : Nat.gcd 4 3 = 1 := by norm_num
        rw [this] at hg
        exact Nat.dvd_one.1 hg
    exact Subgroup.eq_bot_of_card_eq _ h1
  have hZnorm : Z ≤ Subgroup.normalizer (TK : Set ↥K) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hc := Subgroup.mem_center_iff.1 hz h
    rw [← hc, mul_inv_cancel_right]
  have hprod := card_sup_mul_card_inf_of_le_normalizer hZnorm
  rw [hTKbot, Subgroup.card_bot, hTKcard, mul_one] at hprod
  have hsup : TK ⊔ Z = T0.comap π := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hTKQ hZQ)
    rw [hQcard, hprod]
  exact ⟨TK, hTKcard, hTKbot, hsup⟩

end CFSG.LocalAnalysis.GLTheoremA.KD1426Lift

end
