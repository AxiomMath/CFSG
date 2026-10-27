module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Timmesfeld.Balance.Alt

open Subgroup

variable {M : Type*} [Group M]

private theorem card_comap_mk (O : Subgroup M) [O.Normal] (K : Subgroup (M ⧸ O)) :
    Nat.card (K.comap (QuotientGroup.mk' O)) = Nat.card O * Nat.card K :=
  QuotientGroup.card_preimage_mk O (K : Set (M ⧸ O))

private theorem le_normalizer_of_forward {H K : Subgroup M}
    (h : ∀ x ∈ K, ∀ y ∈ H, x * y * x⁻¹ ∈ H) : K ≤ normalizer (H : Set M) := by
  intro x hx
  rw [mem_normalizer_iff]
  refine fun y => ⟨fun hy => h x hx y hy, fun hy => ?_⟩
  have := h x⁻¹ (inv_mem hx) _ hy
  simpa [mul_assoc] using this

private theorem exists_normalized_two_sylow [Finite M] {p : ℕ} (hp : p.Prime) {V K : Subgroup M}
    (hK : K ≤ normalizer (V : Set M)) (hKp : IsPGroup p K) (hnd : ¬ p ∣ Nat.card V)
    (hV2 : 2 ∣ Nat.card V) :
    ∃ S : Subgroup M, S ≠ ⊥ ∧ IsPGroup 2 S ∧ K ≤ normalizer (S : Set M) := by
  classical
  have := Fact.mk hp
  let f : K →* MulAut V := V.normalizerMonoidHom.comp (Subgroup.inclusion hK)
  let _ : MulDistribMulAction K V := MulDistribMulAction.compHom V f
  have hcard : Nat.card (Sylow 2 V) ∣ Nat.card V :=
    (Sylow.card_dvd_index (default : Sylow 2 V)).trans (Subgroup.index_dvd_card _)
  have hnd' : ¬ p ∣ Nat.card (Sylow 2 V) := fun h => hnd (h.trans hcard)
  have hfix : (MulAction.fixedPoints K (Sylow 2 V)).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hmod := hKp.card_modEq_card_fixedPoints (Sylow 2 V)
    rw [hne] at hmod
    have h0 : Nat.card (↥(∅ : Set (Sylow 2 V))) = 0 := by simp
    rw [h0] at hmod
    exact hnd' ((Nat.modEq_zero_iff_dvd).1 hmod)
  obtain ⟨Q, hQ⟩ := hfix
  rw [MulAction.mem_fixedPoints] at hQ
  refine ⟨(Q : Subgroup V).map V.subtype, ?_, ?_, ?_⟩
  · intro h
    exact Q.ne_bot_of_dvd_card hV2 ((Subgroup.map_eq_bot_iff_of_injective (Q : Subgroup V) V.subtype_injective).1 h)
  · exact Q.isPGroup'.map V.subtype
  · refine le_normalizer_of_forward fun x hx y hy => ?_
    obtain ⟨s, hs, rfl⟩ := hy
    have h1 := Subgroup.smul_mem_pointwise_smul s (⟨x, hx⟩ : K) (Q : Subgroup V) hs
    rw [← Sylow.pointwise_smul_def, hQ] at h1
    exact ⟨_, h1, rfl⟩

theorem exists_lift_twoLocal
    {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (O : Subgroup M) [O.Normal] (hO : Nat.Coprime p (Nat.card O))
    (Pbar T : Subgroup (M ⧸ O))
    (hP : IsMulCommutative Pbar ∧ ∀ x ∈ Pbar, x ^ p = 1)
    (hT : T ≠ ⊥ ∧ IsPGroup 2 T)
    (hPT : Pbar ≤ Subgroup.centralizer (T : Set (M ⧸ O))) :
    ∃ P S : Subgroup M, IsMulCommutative P ∧ (∀ x ∈ P, x ^ p = 1) ∧
      Nat.card P = Nat.card Pbar ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
      P ≤ Subgroup.normalizer (S : Set M) := by
  classical
  have hpf := Fact.mk hp
  set π : M →* M ⧸ O := QuotientGroup.mk' O with hπ
  have hker : ∀ x, π x = 1 ↔ x ∈ O := fun x => QuotientGroup.eq_one_iff x
  have hPbar : IsPGroup p Pbar := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hP.2 g g.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hPbar
  set Mhat : Subgroup M := Pbar.comap π with hMhat
  have hMhatcard : Nat.card Mhat = Nat.card O * p ^ n := by
    rw [hMhat, card_comap_mk, hn]
  let P0 : Sylow p Mhat := default
  have hP0card : Nat.card P0 = p ^ n := by
    rw [P0.card_eq_multiplicity, hMhatcard,
      Nat.factorization_mul Nat.card_pos.ne' (pow_pos hp.pos n).ne', Nat.factorization_pow]
    have h0 : (Nat.card O).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun h => hp.one_lt.ne' (hO.eq_one_of_dvd h)
    simp [h0, hp.factorization_self]
  set Pm : Subgroup M := (P0 : Subgroup Mhat).map Mhat.subtype with hPm
  have hPmcard : Nat.card Pm = p ^ n := by
    rw [hPm, Subgroup.card_map_of_injective Mhat.subtype_injective]; exact hP0card
  have hPmp : IsPGroup p Pm := P0.isPGroup'.map Mhat.subtype
  have hPmle : Pm ≤ Mhat := by
    rintro _ ⟨x, -, rfl⟩; exact x.2
  have hPmπ : ∀ x ∈ Pm, π x ∈ Pbar := fun x hx => hPmle hx
  have hinj : ∀ x ∈ Pm, π x = 1 → x = 1 := by
    intro x hx h1
    have hxO : x ∈ O := (hker x).1 h1
    obtain ⟨k, hk⟩ := hPmp ⟨x, hx⟩
    have hk' : x ^ (p ^ k) = 1 := congrArg Subtype.val hk
    have h2 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h3 : orderOf x ∣ Nat.card O := by
      have := Subgroup.orderOf_dvd_natCard O hxO
      exact this
    have h4 : orderOf x ∣ Nat.gcd (p ^ k) (Nat.card O) := Nat.dvd_gcd h2 h3
    rw [(Nat.Coprime.pow_left k hO)] at h4
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
  have hcomm : ∀ x ∈ Pm, ∀ y ∈ Pm, x * y = y * x := by
    intro x hx y hy
    have hc : π x * π y = π y * π x :=
      congrArg Subtype.val (hP.1.is_comm.comm ⟨π x, hPmπ x hx⟩ ⟨π y, hPmπ y hy⟩)
    have := hinj (x * y * (y * x)⁻¹) (mul_mem (mul_mem hx hy) (inv_mem (mul_mem hy hx)))
      (by rw [map_mul, map_inv, map_mul, map_mul, hc, mul_inv_cancel])
    exact mul_inv_eq_one.1 this
  have hexp : ∀ x ∈ Pm, x ^ p = 1 := fun x hx =>
    hinj (x ^ p) (pow_mem hx p) (by rw [map_pow]; exact hP.2 _ (hPmπ x hx))
  set V : Subgroup M := T.comap π with hV
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hT.2
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hT.1 (Subgroup.card_eq_one.1 (by simpa using hm))
  have hVcard : Nat.card V = Nat.card O * 2 ^ m := by rw [hV, card_comap_mk, hm]
  have hnd : ¬ p ∣ Nat.card V := by
    intro h
    have hc : Nat.Coprime p (Nat.card V) := by
      rw [hVcard]
      exact Nat.Coprime.mul_right hO
        (Nat.Coprime.pow_right m ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
    exact hp.one_lt.ne' (hc.eq_one_of_dvd h)
  have hV2 : 2 ∣ Nat.card V := by
    rw [hVcard]; exact Dvd.dvd.mul_left (dvd_pow_self 2 hm0) _
  have hPmN : Pm ≤ normalizer (V : Set M) := by
    refine le_normalizer_of_forward fun x hx y hy => ?_
    have hy' : π y ∈ T := hy
    have hc := mem_centralizer_iff.1 (hPT (hPmπ x hx)) (π y) hy'
    show π (x * y * x⁻¹) ∈ T
    have : π (x * y * x⁻¹) = π y := by
      rw [map_mul, map_mul, map_inv, ← hc]; simp
    rw [this]; exact hy'
  obtain ⟨S, hS, hS2, hSN⟩ := exists_normalized_two_sylow hp hPmN hPmp hnd hV2
  exact ⟨Pm, S, ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, hexp, hPmcard.trans hn.symm,
    hS, hS2, hSN⟩

end CFSG.HardMathSupport.Timmesfeld.Balance.Alt
