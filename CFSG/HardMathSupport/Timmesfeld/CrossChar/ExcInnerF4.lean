module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerReduction
public import CFSG.RankThree.PartOne.K133H.F4Torus

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge

theorem localDeltaIn_eq_bot_of_map_conj {M : Type*} [Group M] {p : ℕ} {H D : Subgroup M} {c : M}
    (hc : c ∈ H) (h : localDeltaIn p H (D.map (MulAut.conj c).toMonoidHom) = ⊥) :
    localDeltaIn p H D = ⊥ := by
  have hH : H.map (MulAut.conj c).toMonoidHom = H := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact H.mul_mem (H.mul_mem hc hy) (H.inv_mem hc)
    · intro hx
      refine ⟨c⁻¹ * x * c, H.mul_mem (H.mul_mem (H.inv_mem hc) hx) hc, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hle := map_localDeltaIn_le p (MulAut.conj c).toMonoidHom (MulAut.conj c).injective H D
  rw [hH, h, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj c).injective] at hle
  exact hle

theorem exists_orderOf_units_of_dvd {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) : ∃ t : Kˣ, orderOf t = p ∧ t ^ 2 ≠ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_units])
  refine ⟨t, ht, fun h => hp2 ?_⟩
  have h1 := orderOf_dvd_of_pow_eq_one h
  rw [ht] at h1
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1

section Toral

variable {τ : Tag} {K : Type} [Field K]


theorem localDeltaIn_eq_bot_of_conj_toral [Finite K] {p : ℕ} (hp : p.Prime) {t : Kˣ}
    (htp : orderOf t = p) (ht : t ^ 2 ≠ 1) {H : Subgroup (MulAut (adjointGroup τ K))}
    (hH : innerAut (adjointGroup τ K) ≤ H) {D : Subgroup (MulAut (adjointGroup τ K))}
    (hDin : D ≤ innerAut (adjointGroup τ K)) (hpow : ∀ x ∈ D, x ^ p = 1) (hcard : p < Nat.card D)
    (g : adjointGroup τ K)
    (htor : ∀ x ∈ D.comap (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)),
      ((g * x * g⁻¹ : adjointGroup τ K) : ModGL τ K) ∈ torusGroup τ K) :
    localDeltaIn p H D = ⊥ := by
  have hinj := mulAut_conj_injective_adjointGroup (τ := τ) (K := K)
  set D₀ := D.comap (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)) with hD₀
  have hDD : D₀.map MulAut.conj = D := Subgroup.map_comap_eq_self hDin
  refine localDeltaIn_eq_bot_of_map_conj (c := MulAut.conj g) (hH ⟨g, rfl⟩) ?_
  have hmap : D.map (MulAut.conj (MulAut.conj g)).toMonoidHom =
      (D₀.map (MulAut.conj g).toMonoidHom).map MulAut.conj := by
    conv_lhs => rw [← hDD]
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [hmap]
  refine localDeltaIn_eq_bot_of_toral hp htp ht hH _ ?_ ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : (MulAut.conj y) ^ p = 1 := hpow _ hy
    have hyp : y ^ p = 1 := hinj (by rw [map_pow, hy', map_one])
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_pow, hyp, mul_one, mul_inv_cancel]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    rwa [← hDD, Subgroup.card_map_of_injective hinj] at hcard
  · rintro _ ⟨y, hy, rfl⟩
    exact htor y hy

theorem localDeltaIn_eq_bot_adjointF4_of_dvd_sub_one (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1)
    {H : Subgroup (MulAut (adjointGroup Tag.F4 K))} (hH : innerAut (adjointGroup Tag.F4 K) ≤ H)
    {D : Subgroup (MulAut (adjointGroup Tag.F4 K))} (hDin : D ≤ innerAut (adjointGroup Tag.F4 K))
    (hpow : ∀ x ∈ D, x ^ p = 1) (hcard : p < Nat.card D) : localDeltaIn p H D = ⊥ := by
  obtain ⟨t, htp, ht⟩ := exists_orderOf_units_of_dvd hp (by omega) hpq
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.F4) (K := K)
  set D₀ := D.comap (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K))
  have hpow₀ : ∀ x ∈ D₀.map (adjointGroup Tag.F4 K).subtype, x ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (MulAut.conj y) ^ p = 1 := hpow _ hy
    have hyp : y ^ p = 1 := hinj (by rw [map_pow, hy', map_one])
    rw [← map_pow, hyp, map_one]
  obtain ⟨g, hg, hgT⟩ := CFSG.RankThree.PartOne.K133H.exists_conj_into_torus_F4 hp hp5 hpq
    (Subgroup.map_subtype_le D₀) hpow₀
  exact localDeltaIn_eq_bot_of_conj_toral hp htp ht hH hDin hpow hcard ⟨g, hg⟩
    fun x hx => hgT ⟨x, ⟨x, hx, rfl⟩, rfl⟩

theorem isInnerLocallyBalanced_adjointF4_of_dvd_sub_one (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1) :
    IsInnerLocallyBalanced p (adjointGroup Tag.F4 K) := by
  intro D hD hcard hDin H hH _
  refine localDeltaIn_eq_bot_adjointF4_of_dvd_sub_one K hp hp5 hpq hH hDin hD.2 ?_
  rw [hcard]
  calc p = p ^ 1 := (pow_one p).symm
    _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)

theorem innerPlanes_adjointF4_of_dvd_sub_one (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1)
    (E : Subgroup (MulAut (adjointGroup Tag.F4 K))) (hEin : E ≤ innerAut (adjointGroup Tag.F4 K))
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    (H : Subgroup (MulAut (adjointGroup Tag.F4 K))) (hH : innerAut (adjointGroup Tag.F4 K) ≤ H) :
    localDeltaIn p H E = ⊥ := by
  refine localDeltaIn_eq_bot_adjointF4_of_dvd_sub_one K hp hp5 hpq hH hEin hE.2 ?_
  rw [hcard]
  calc p = p ^ 1 := (pow_one p).symm
    _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)

end Toral

section Residual

@[expose] def F4InnerResidual : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p : ℕ), p.Prime → p ≠ 2 → ¬ p ∣ Nat.card K →
    ∀ D : Subgroup (MulAut (adjointGroup Tag.F4 K)), IsElemAbelian p D → Nat.card D = p ^ 3 →
      D ≤ innerAut (adjointGroup Tag.F4 K) →
      (p ∣ Nat.card K + 1 ∨ (p = 3 ∧ ∀ g : adjointGroup Tag.F4 K,
        ∃ x ∈ D.comap (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)),
          ((g * x * g⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) ∉ torusGroup Tag.F4 K)) →
      ∀ H : Subgroup (MulAut (adjointGroup Tag.F4 K)), innerAut (adjointGroup Tag.F4 K) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.F4 K))) →
          localDeltaIn p H D = ⊥

theorem dvd_sub_one_or_dvd_add_one_of_degCount_F4 {p q : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q)
    (hcnt : 3 ≤ degCount Tag.F4 (orderOf ((q : ℕ) : ZMod p))) : p ∣ q - 1 ∨ p ∣ q + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hq : 1 ≤ q := Nat.pos_of_ne_zero fun h => hpq (h ▸ dvd_zero p)
  obtain ⟨e, he⟩ : ∃ e, orderOf ((q : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt
  have h30 := le_thirty_of_degCount_pos (τ := Tag.F4) (e := e) (by simp) (by omega)
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpq
  have h1 : 1 ≤ e := Nat.pos_of_ne_zero he0
  interval_cases e <;> first | exact absurd hcnt (by decide) | skip
  · left
    simpa using (dvd_pow_sub_one_iff_orderOf (d := 1) hq he).2 dvd_rfl
  · right
    have hx2 : ((q : ℕ) : ZMod p) ^ 2 = 1 := he ▸ pow_orderOf_eq_one _
    have hx1 : ((q : ℕ) : ZMod p) ≠ 1 := fun h => by
      rw [h, orderOf_one] at he
      exact absurd he (by norm_num)
    have hx : ((q : ℕ) : ZMod p) = -1 :=
      ((mul_self_eq_one_iff.1 (by rw [← sq, hx2])).resolve_left hx1)
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one, hx]
    exact neg_add_cancel _

end Residual

section Families


theorem crossCharInnerAt_F4_dvd_sub_one :
    CrossCharInnerAt .F4 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .F4 q ∧ 5 ≤ p ∧
      p ∣ q.card - 1 := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc ⟨q, hd, hp5, hpq⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  rw [← hK] at hpq
  exact (isInnerLocallyBalanced_adjointF4_of_dvd_sub_one K hp hp5 hpq).of_mulEquiv e

theorem crossCharInnerAt_F4_ge_three_of_residual (h : F4InnerResidual) :
    CrossCharInnerAt .F4 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .F4 q ∧
      3 ≤ degCount Tag.F4 (orderOf ((q.card : ℕ) : ZMod p)) := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc ⟨q, hd, hcnt⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have hpK : ¬ p ∣ Nat.card K := hK ▸ not_dvd_card_of_ne hp hpq
  rw [← hK] at hcnt
  refine IsInnerLocallyBalanced.of_mulEquiv e ?_
  intro D hD hcard hDin H hH hDH
  rcases dvd_sub_one_or_dvd_add_one_of_degCount_F4 hp hpK hcnt with h1 | h1
  · rcases eq_three_or_five_le hp hp2 with rfl | h5
    · by_cases htor : ∃ g : adjointGroup Tag.F4 K, ∀ x ∈ D.comap
          (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)),
          ((g * x * g⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) ∈ torusGroup Tag.F4 K
      · obtain ⟨g, hg⟩ := htor
        obtain ⟨t, htp, ht⟩ := exists_orderOf_units_of_dvd hp hp2 h1
        refine localDeltaIn_eq_bot_of_conj_toral hp htp ht hH hDin hD.2 ?_ g hg
        rw [hcard]
        norm_num
      · push Not at htor
        exact h K 3 hp hp2 hpK D hD hcard hDin (Or.inr ⟨rfl, htor⟩) H hH hDH
    · exact isInnerLocallyBalanced_adjointF4_of_dvd_sub_one K hp h5 h1 D hD hcard hDin H hH hDH
  · exact h K p hp hp2 hpK D hD hcard hDin (Or.inl h1) H hH hDH

theorem crossCharInnerAt_F4_ge_three_of_split
    (h : CrossCharInnerAt .F4 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .F4 q ∧
      (p = 3 ∨ p ∣ q.card + 1)) :
    CrossCharInnerAt .F4 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .F4 q ∧
      3 ≤ degCount Tag.F4 (orderOf ((q.card : ℕ) : ZMod p)) := by
  rintro idx hk p hp hp2 hc ⟨q, hd, hcnt⟩
  have hpq : p ≠ q.p := fun h => hc (by rw [hd]; simp [h])
  rcases dvd_sub_one_or_dvd_add_one_of_degCount_F4 hp (not_dvd_card_of_ne hp hpq) hcnt with
    h1 | h1
  · rcases eq_three_or_five_le hp hp2 with rfl | h5
    · exact h idx hk 3 hp hp2 hc ⟨q, hd, Or.inl rfl⟩
    · exact crossCharInnerAt_F4_dvd_sub_one idx hk p hp hp2 hc ⟨q, hd, h5, h1⟩
  · exact h idx hk p hp hp2 hc ⟨q, hd, Or.inr h1⟩

theorem crossCharFamAt_F4_ge_three_of_residual (h : F4InnerResidual) :
    CrossCharFamAt .F4 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .F4 q ∧
      3 ≤ degCount Tag.F4 (orderOf ((q.card : ℕ) : ZMod p)) :=
  crossCharFamAt_F4_ge_three_of_inner (crossCharInnerAt_F4_ge_three_of_residual h)

end Families

end CFSG.HardMathSupport.Timmesfeld.CrossChar
