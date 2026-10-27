module

public import CFSG.GroupTheory.CoprimeActionSupport.FixedFreeNormalizerScalarExtension
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.SquarefreeAbelianCentrality

theorem centralizes {F : Type*} [Field F] {H : Type*} [Group H] [Finite H]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F H V) (hρ : Function.Injective ρ)
    (C : Subgroup H) [IsCyclic C] (hsf : Squarefree (Nat.card C))
    (hfix : ∀ c ∈ C, c ≠ 1 → LinearMap.ker (ρ c - LinearMap.id) = (⊥ : Submodule F V))
    (E : Subgroup H) [IsMulCommutative E] (hCE : C ≤ Subgroup.normalizer (E : Set H))
    (hEF : (Nat.card E : F) ≠ 0) (hCF : (Nat.card C : F) ≠ 0) :
    C ≤ Subgroup.centralizer (E : Set H) := by
  classical
  have hprime : ∀ c : C, (orderOf c).Prime → (c : H) ∈ Subgroup.centralizer (E : Set H) := by
    intro c hc
    set q := orderOf c with hq
    haveI : Fact q.Prime := ⟨hc⟩
    have hoH : orderOf (c : H) = q := by
      rw [hq]; exact Subgroup.orderOf_coe c
    have hc1 : (c : H) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hoH
      exact hc.one_lt.ne hoH
    have hqF : (q : F) ≠ 0 := by
      intro h0
      obtain ⟨k, hk⟩ := (orderOf_dvd_natCard c : orderOf c ∣ Nat.card C)
      apply hCF
      rw [hk, Nat.cast_mul, ← hq, h0, zero_mul]
    have hcard : Nat.card (Subgroup.zpowers (c : H)) = q := by
      rw [Nat.card_zpowers, hoH]
    have hD : (⨅ d ∈ Subgroup.zpowers (c : H), LinearMap.ker (ρ d - LinearMap.id))
        = (⊥ : Submodule F V) := by
      rw [eq_bot_iff, ← hfix c c.2 hc1]
      exact iInf₂_le (c : H) (Subgroup.mem_zpowers _)
    have hDE : Subgroup.zpowers (c : H) ≤ Subgroup.normalizer (E : Set H) := by
      rw [Subgroup.zpowers_le]; exact hCE c.2
    have := CFSG.GroupTheory.CoprimeActionSupport.FixedFreeNormalizerScalarExtension.centralizes
      ρ hρ q (Subgroup.zpowers (c : H)) hcard hD E hDE hEF hqF
    exact this (Subgroup.mem_zpowers _)
  by_contra hnot
  set D : Subgroup C := (Subgroup.centralizer (E : Set H)).comap C.subtype with hDdef
  have hidx : D.index ≠ 1 := by
    intro h
    apply hnot
    intro x hx
    have : (⟨x, hx⟩ : C) ∈ D := by rw [Subgroup.index_eq_one] at h; rw [h]; trivial
    exact this
  obtain ⟨q, hqp, hqd⟩ := Nat.exists_prime_and_dvd hidx
  haveI : Fact q.Prime := ⟨hqp⟩
  have hmul : Nat.card D * D.index = Nat.card C := Subgroup.card_mul_index D
  have hqC : q ∣ Nat.card C := hmul ▸ Dvd.dvd.mul_left hqd _
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := C) q hqC
  have hcD : c ∈ D := hprime c (hc ▸ hqp)
  have hqD : q ∣ Nat.card D := by
    have h := orderOf_dvd_natCard (⟨c, hcD⟩ : D)
    rw [Subgroup.orderOf_mk] at h
    rwa [hc] at h
  have : q * q ∣ Nat.card C := by
    rw [← hmul]; exact Nat.mul_dvd_mul hqD hqd
  exact hqp.not_isUnit (hsf q this)

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.SquarefreeAbelianCentrality
