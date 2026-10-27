module

public import CFSG.LieType.Sp6Spin.CaseAB

public section

namespace CFSG.LieType.Sp6Spin

open CFSG.LieType.TorusWeights CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Assembly.LowTwoRank TauCeti.GLSymplecticFin
  QuadraticMap

attribute [local instance] Fintype.ofFinite Classical.propDecidable

namespace SpinSetting

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  (S : SpinSetting K V)

private theorem wtProj_eq_zero_of_fixed {t : Fin 3 → Kˣ} {t₀ : Kˣ}
    (ht : t = Pi.mulSingle 0 t₀) (hord : orderOf t₀ = Nat.card Kˣ)
    {x : ZMod (Nat.card Kˣ)} (hx : x ≠ 0)
    (hpat : ∀ a : Fin 3 → ZMod (Nat.card Kˣ),
      S.mult a = if ∀ i, a i = x ∨ a i = -x then 1 else 0)
    {v : V} (hv : S.ψ (diagHom 3 K t) v = v) :
    ∀ a : Fin 3 → ZMod (Nat.card Kˣ), wtProj (diagHom 3 K) S.ρ a v = 0 := by
  intro a
  let w : V := wtProj (diagHom 3 K) S.ρ a v
  have hwmem : w ∈ S.X a := wtProj_mem (diagHom 3 K) S.ρ a v
  have hwfix : S.ψ (diagHom 3 K t) w = w := by
    have h := congrArg (fun f : Module.End K V => f v)
      (wtProj_comm_h (diagHom 3 K) S.ρ a t)
    simp only [LinearMap.comp_apply] at h
    rw [show S.ρ (diagHom 3 K t) v = v from
      (S.ρ_apply (diagHom 3 K t) v).trans hv] at h
    rw [← S.ρ_apply (diagHom 3 K t) w]
    exact h
  by_contra hw0
  have hchar : (wtChar a t : K) = 1 := by
    have h := (S.mem_X (a := a)).mp hwmem t
    rw [hwfix] at h
    have hmul : (1 - (wtChar a t : K)) • w = 0 := by
      rw [sub_smul, one_smul, ← h, sub_self]
    rcases smul_eq_zero.mp hmul with h1 | h1
    · exact (sub_eq_zero.mp h1).symm
    · exact absurd h1 hw0
  have hchar' : wtChar a t = 1 := Units.ext hchar
  have hchar2 : t₀ ^ (a 0).val = 1 := by
    rw [wtChar_apply, Finset.prod_eq_single (0 : Fin 3)] at hchar'
    · rw [ht] at hchar'
      simpa using hchar'
    · intro i _ hi
      rw [ht]
      simp [Pi.mulSingle_eq_of_ne hi]
    · intro h
      exact absurd (Finset.mem_univ 0) h
  have hNval : Nat.card Kˣ ∣ (a 0).val := by
    have h := orderOf_dvd_of_pow_eq_one hchar2
    rwa [hord] at h
  have ha0val : (a 0).val = 0 := Nat.eq_zero_of_dvd_of_lt hNval (ZMod.val_lt (a 0))
  have ha0 : a 0 = 0 := by
    rw [← ZMod.natCast_zmod_val (a 0), ha0val, Nat.cast_zero]
  have hmult : S.mult a ≠ 0 := by
    intro h
    refine hw0 ?_
    rw [S.X_eq_bot_iff.mpr h] at hwmem
    simpa using hwmem
  have hcond : ∀ i, a i = x ∨ a i = -x := by
    by_contra hc
    rw [hpat a, if_neg hc] at hmult
    exact hmult rfl
  rcases hcond 0 with h0 | h0
  · exact hx (h0.symm.trans ha0)
  · have hne : -x ≠ 0 := by simpa using hx
    exact hne (h0.symm.trans ha0)

theorem exists_odd_orderOf_fixedPointFree :
    ∃ g : StatedSp 3 K, Odd (orderOf g) ∧ ∀ v, S.ψ g v = v → v = 0 := by
  obtain ⟨x, hx, hpat⟩ := S.exists_isSpinPattern
  obtain ⟨t₀, ht₀⟩ := IsCyclic.exists_generator (α := Kˣ)
  let t : Fin 3 → Kˣ := Pi.mulSingle 0 t₀
  let g : StatedSp 3 K := diagHom 3 K t
  have ht₀ord : orderOf t₀ = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers ht₀
  have htN : t ^ Nat.card Kˣ = 1 := by
    funext i
    simp only [Pi.pow_apply, t, Pi.one_apply]
    by_cases hi : i = 0
    · subst hi
      rw [Pi.mulSingle_eq_same, pow_card_eq_one']
    · rw [Pi.mulSingle_eq_of_ne hi, one_pow]
  have hgN : g ^ Nat.card Kˣ = 1 := by
    change (diagHom 3 K t) ^ Nat.card Kˣ = 1
    rw [← map_pow, htN, map_one]
  have hdvd : orderOf g ∣ Nat.card Kˣ := orderOf_dvd_of_pow_eq_one hgN
  refine ⟨g, Odd.of_dvd_nat odd_natCard_units hdvd, ?_⟩
  intro v hv
  have hfixed := wtProj_eq_zero_of_fixed S (t := t) (t₀ := t₀) rfl ht₀ord hx hpat hv
  calc v = ∑ a, wtProj (diagHom 3 K) S.ρ a v := (sum_wtProj (diagHom 3 K) S.ρ v).symm
    _ = 0 := by simp [hfixed]

end SpinSetting

theorem exists_odd_orderOf_fixedPointFree (K : Type) [Field K] [Finite K] [CharP K 2]
    (V : Type) [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
    (hK : 4 ≤ Nat.card K) (hV : Module.finrank K V = 8)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (ψ : StatedSp 3 K →* (V ≃ₗ[K] V)) (hψ : ∀ g v, Q (ψ g v) = Q v)
    (hirr : ∀ W : Submodule K V, (∀ g, ∀ w ∈ W, ψ g w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ g : StatedSp 3 K, Odd (orderOf g) ∧ ∀ v, ψ g v = v → v = 0 :=
  (⟨hK, hV, Q, hQ, ψ, hψ, hirr⟩ : SpinSetting K V).exists_odd_orderOf_fixedPointFree

end CFSG.LieType.Sp6Spin
