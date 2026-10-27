module

public import CFSG.Open.StatedAPI
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3

open CFSG.Open CFSG.Open.StatedAPI

noncomputable section

theorem sq_eq_one_of_mem_ker {K : Type} [Field K] {y : StatedSp 3 K}
    (hy : (QuotientGroup.mk y : StatedProj (StatedSp 3 K)) = 1) : y ^ 2 = 1 := by
  have hy' : y ∈ (StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K) := by
    rw [← QuotientGroup.ker_mk' ((StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K))]
    exact hy
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hy'
  obtain ⟨c, hc⟩ := hy'
  have hcH : Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) c ∈ StatedSp 3 K := by
    rw [hc]
    exact y.2
  have hc2 := (scalar_mem_statedSp_iff (K := K) (by norm_num) c).1 hcH
  apply Subtype.ext
  rw [Subgroup.coe_pow, OneMemClass.coe_one]
  have hyc : ((y : GL (Fin 3 ⊕ Fin 3) K)) = Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) c :=
    hc.symm
  rw [hyc, ← map_pow, hc2, map_one]

theorem lift_exists (K : Type) [Field K] [Finite K] (E : Subgroup (StatedProj (StatedSp 3 K)))
    (hc : Nat.card E = 27) :
    ∃ P : Subgroup (StatedSp 3 K),
      (∀ x ∈ P, (QuotientGroup.mk x : StatedProj (StatedSp 3 K)) = 1 → x = 1) ∧
        P.map (QuotientGroup.mk' ((StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf
          (StatedSp 3 K))) = E := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' ((StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K))
    with hπ
  set E' : Subgroup (StatedSp 3 K) := E.comap π with hE'
  let ρ' : E' →* E := (π.comp E'.subtype).codRestrict E (fun x => x.2)
  have hρ : Function.Surjective ρ' := by
    intro e
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e : StatedProj (StatedSp 3 K))
    refine ⟨⟨x, ?_⟩, ?_⟩
    · show π x ∈ E
      have hx' : π x = (e : StatedProj (StatedSp 3 K)) := hx
      rw [hx']
      exact e.2
    · apply Subtype.ext
      exact hx
  have hcardE' : Nat.card E' = 27 * Nat.card ρ'.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ'.ker
    have hq : Nat.card (E' ⧸ ρ'.ker) = Nat.card E :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ' hρ).toEquiv
    rw [hq, hc] at h1
    exact h1
  have exp_two' : ∀ y : E', ρ' y = 1 → y ^ 2 = 1 := by
    intro y hy
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    apply sq_eq_one_of_mem_ker
    have h2 : π (y : StatedSp 3 K) = 1 := congrArg Subtype.val hy
    exact h2
  have hkerρ : ¬ 3 ∣ Nat.card ρ'.ker := by
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ρ'.ker) 3 hdvd
    have hx2 : (x : E') ^ 2 = 1 := exp_two' x.1 (MonoidHom.mem_ker.1 x.2)
    have hx3 : (x : E') ^ 3 = 1 := by
      have h := pow_orderOf_eq_one (x : E')
      rwa [Subgroup.orderOf_coe, hx] at h
    have h1 : (x : E') = 1 := by
      calc (x : E') = (x : E') ^ 3 * ((x : E') ^ 2)⁻¹ := by group
        _ = 1 := by rw [hx3, hx2, inv_one, mul_one]
    have h2 : orderOf (x : E') = 3 := by rw [Subgroup.orderOf_coe, hx]
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have h27 : 3 ^ 3 ∣ Nat.card E' := ⟨Nat.card ρ'.ker, by rw [hcardE']; norm_num⟩
  obtain ⟨P0, hP0⟩ := Sylow.exists_subgroup_card_pow_prime (G := E') 3 h27
  have hinf : P0 ⊓ ρ'.ker = ⊥ := by
    have hd1 : Nat.card (P0 ⊓ ρ'.ker : Subgroup E') ∣ 3 ^ 3 := by
      rw [← hP0]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card (P0 ⊓ ρ'.ker : Subgroup E') ∣ Nat.card ρ'.ker :=
      Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd1
    have hcard1 : Nat.card (P0 ⊓ ρ'.ker : Subgroup E') = 1 := by
      rcases i with _ | i
      · simpa using hi
      · exfalso
        apply hkerρ
        have h3d : 3 ∣ Nat.card (P0 ⊓ ρ'.ker : Subgroup E') := by
          rw [hi]
          exact dvd_pow_self 3 (Nat.succ_ne_zero i)
        exact dvd_trans h3d hd2
    exact Subgroup.eq_bot_of_card_eq _ hcard1
  have hΨinj : Function.Injective (ρ'.comp P0.subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyI : (y : E') ∈ P0 ⊓ ρ'.ker := ⟨y.2, hy⟩
    rw [hinf] at hyI
    exact Subtype.ext (Subgroup.mem_bot.1 hyI)
  have hΨbij : Function.Bijective (ρ'.comp P0.subtype) :=
    Function.Injective.bijective_of_nat_card_le hΨinj (by rw [hP0, hc]; norm_num)
  refine ⟨P0.map E'.subtype, ?_, ?_⟩
  · intro x hx hπx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hρy : ρ' y = 1 := by
      apply Subtype.ext
      exact hπx
    have hyI : y ∈ P0 ⊓ ρ'.ker := ⟨hy, hρy⟩
    rw [hinf] at hyI
    rw [Subgroup.mem_bot.1 hyI]
    rfl
  · ext e
    constructor
    · intro he
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 he
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      exact (ρ' y).2
    · intro he
      obtain ⟨z, hz⟩ := hΨbij.2 ⟨e, he⟩
      refine Subgroup.mem_map.2 ⟨E'.subtype (z : E'), Subgroup.mem_map.2 ⟨(z : E'), z.2, rfl⟩, ?_⟩
      exact congrArg Subtype.val hz

end

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3

end
