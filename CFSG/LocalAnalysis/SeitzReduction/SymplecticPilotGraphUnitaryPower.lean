module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndOddBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotEndFieldBasic

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup

variable {G : Type*} [Group G] [Finite G] {X Q : Type*} [Group X] [Group Q] [Finite Q]
  [IsCyclic Q]

theorem exists_normal_index_two_of_fieldFactor {M : Subgroup G} (ρ : M →* MulAut X)
    (hker : Odd (Nat.card ρ.ker)) (hInn : ∀ g : X, ∃ m : M, ρ m = MulAut.conj g)
    (Φ : MulAut X →* Q) (s : Q →* MulAut X) (hs : ∀ c, Φ (s c) = c)
    (h2 : ∀ d ∈ Φ.ker, ∀ k : ℕ, d ^ 2 ^ k = 1 → d ∈ (MulAut.conj : X →* MulAut X).range)
    {t : G} (htM : t ∈ M) (ht : orderOf t = 2) (hts : ρ ⟨t, htM⟩ ∈ s.range)
    (hout : ρ ⟨t, htM⟩ ∉ (MulAut.conj : X →* MulAut X).range)
    (hinv : ∀ d ∈ Φ.ker, d * ρ ⟨t, htM⟩ * d⁻¹ * (ρ ⟨t, htM⟩)⁻¹ ∈
      (MulAut.conj : X →* MulAut X).range → d ∈ (MulAut.conj : X →* MulAut X).range)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : CommGroup Q := IsCyclic.commGroup
  set α := ρ ⟨t, htM⟩ with hαdef
  set A := ρ.range with hAdef
  have : Finite A := Finite.of_surjective _ ρ.rangeRestrict_surjective
  have hαA : α ∈ A := ⟨_, rfl⟩
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have hα2 : α ^ 2 = 1 := EPilot.action_sq_eq_one ρ htM ht2
  obtain ⟨ι, hι⟩ := hts
  have hα1 : α ≠ 1 := fun h => hout ⟨1, by rw [map_one, h]⟩
  have hαp : IsPGroup 2 (zpowers (⟨α, hαA⟩ : A)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, pow_one]
    exact orderOf_eq_prime hα2 hα1
  obtain ⟨P, hP⟩ := hαp.exists_le_sylow
  have hαP : (⟨α, hαA⟩ : A) ∈ (P : Subgroup A) := hP (mem_zpowers _)
  set ΦA : A →* Q := Φ.comp A.subtype with hΦA
  set R := ΦA.range with hR
  set P' : Sylow 2 R := P.mapSurjective ΦA.rangeRestrict_surjective with hP'
  obtain ⟨c₀, hc₀⟩ := IsCyclic.exists_generator (α := (P' : Subgroup R))
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 P'.isPGroup'
  have hc₀o : orderOf c₀ = 2 ^ a := (orderOf_eq_card_of_forall_mem_zpowers hc₀).trans ha
  set c : Q := ((c₀ : R) : Q) with hcdef
  have hco : orderOf c = 2 ^ a := by
    rw [hcdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc₀o]
  have hRidx : ¬ 2 ^ (a + 1) ∣ Nat.card R := by
    intro hdvd
    rw [← (P' : Subgroup R).card_mul_index, ha, pow_succ] at hdvd
    exact P'.not_dvd_index (Nat.dvd_of_mul_dvd_mul_left (by positivity) hdvd)
  have hΦα : Φ α = ι := by rw [← hι, hs]
  have hιP' : (⟨ι, ⟨⟨α, hαA⟩, hΦα⟩⟩ : R) ∈ (P' : Subgroup R) := by
    rw [hP', Sylow.coe_mapSurjective]
    exact ⟨_, hαP, Subtype.ext hΦα⟩
  have hι1 : ι ≠ 1 := by
    rintro rfl
    exact hα1 (by rw [← hι, map_one])
  have ha1 : 1 ≤ a := by
    by_contra h0
    obtain rfl : a = 0 := by omega
    have hcard1 : Nat.card (P' : Subgroup R) = 1 := by rw [ha, pow_zero]
    have hsub : Subsingleton (P' : Subgroup R) := (Nat.card_eq_one_iff_unique.1 hcard1).1
    have h1 : (⟨_, hιP'⟩ : (P' : Subgroup R)) = 1 := Subsingleton.elim _ _
    exact hι1 (congrArg (fun z : (P' : Subgroup R) => ((z : R) : Q)) h1)
  have hc₀P : (c₀ : R) ∈ (P : Subgroup A).map ΦA.rangeRestrict := c₀.2
  obtain ⟨b, hbP, hbc⟩ := hc₀P
  have hbc' : Φ (b : MulAut X) = c := congrArg Subtype.val hbc
  have hcomm : (b : MulAut X) * α * (b : MulAut X)⁻¹ * α⁻¹ ∈
      (MulAut.conj : X →* MulAut X).range := by
    set w : A := b * ⟨α, hαA⟩ * b⁻¹ * (⟨α, hαA⟩ : A)⁻¹ with hw
    have hwP : w ∈ (P : Subgroup A) :=
      mul_mem (mul_mem (mul_mem hbP hαP) (inv_mem hbP)) (inv_mem hαP)
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨w, hwP⟩
    refine h2 _ ?_ k ?_
    · rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (Φ _) (Φ α),
        mul_assoc, mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
    · have hk' := congrArg (fun z : (P : Subgroup A) => ((z : A) : MulAut X)) hk
      simpa [hw] using hk'
  set d : MulAut X := (b : MulAut X) * (s c)⁻¹ with hd
  have hdker : d ∈ Φ.ker := by
    rw [MonoidHom.mem_ker, hd, map_mul, map_inv, hbc', hs, mul_inv_cancel]
  have hdα : d * α * d⁻¹ * α⁻¹ = (b : MulAut X) * α * (b : MulAut X)⁻¹ * α⁻¹ := by
    have hsc : (s c)⁻¹ * α * s c = α := by
      rw [← hι, ← map_inv, ← map_mul, ← map_mul, mul_comm c⁻¹ ι, inv_mul_cancel_right]
    rw [hd, mul_inv_rev, inv_inv]
    calc (b : MulAut X) * (s c)⁻¹ * α * (s c * (b : MulAut X)⁻¹) * α⁻¹
        = (b : MulAut X) * ((s c)⁻¹ * α * s c) * (b : MulAut X)⁻¹ * α⁻¹ := by group
      _ = _ := by rw [hsc]
  have hdI : d ∈ (MulAut.conj : X →* MulAut X).range := hinv d hdker (hdα ▸ hcomm)
  have hscA : s c ∈ A := by
    have h1 : s c = d⁻¹ * (b : MulAut X) := by rw [hd]; group
    obtain ⟨g, hg⟩ := hdI
    obtain ⟨m, hm⟩ := hInn g
    rw [h1]
    exact mul_mem (inv_mem ⟨m, hm.trans hg⟩) b.2
  have hsinj : Function.Injective s := fun x y hxy => by rw [← hs x, ← hs y, hxy]
  have hsco : orderOf (s c) = 2 ^ a := (orderOf_injective s hsinj c).trans hco
  obtain ⟨x, hxρ, hxo⟩ := LinearPilot.exists_orderOf_eq_of_odd_ker ρ hker hscA hsco
  set H : Subgroup M := (Φ.comp ρ).ker with hH
  have hxQ : orderOf (QuotientGroup.mk' H ⟨(x : G), x.2⟩) = 2 ^ a := by
    rw [← orderOf_injective _ (QuotientGroup.kerLift_injective (Φ.comp ρ))]
    change orderOf (QuotientGroup.kerLift (Φ.comp ρ) (x : M ⧸ (Φ.comp ρ).ker)) = 2 ^ a
    rw [QuotientGroup.kerLift_mk, MonoidHom.comp_apply, hxρ, hs, hco]
  have hRange : (Φ.comp ρ).range = R := by
    ext q
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨⟨ρ m, ⟨m, rfl⟩⟩, rfl⟩
    · rintro ⟨⟨y, ⟨m, hm⟩⟩, rfl⟩
      exact ⟨m, by rw [MonoidHom.comp_apply, hm]; rfl⟩
  have hQ : ¬ 2 ^ (a + 1) ∣ Nat.card (M ⧸ H) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (Φ.comp ρ)).toEquiv, hRange]
    exact hRidx
  have hcpow : c ^ 2 ^ (a - 1) = ι := by
    have h2a : 2 ^ (a - 1) * 2 = 2 ^ a := by rw [← pow_succ]; congr 1; omega
    refine EPilot.eq_of_sq_eq_one_of_ne_one_of_isCyclic ?_ ?_ ?_ hι1
    · rw [← pow_mul, h2a, ← hco, pow_orderOf_eq_one]
    · rw [← hΦα, ← map_pow, hα2, map_one]
    · intro h1
      have := orderOf_le_of_pow_eq_one (by positivity) h1
      rw [hco] at this
      have : 2 ^ (a - 1) < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
  have hxpowM : (x : G) ^ 2 ^ (a - 1) ∈ M := pow_mem x.2 _
  have hρx : ρ ⟨(x : G) ^ 2 ^ (a - 1), hxpowM⟩ = α := by
    have h1 : (⟨(x : G) ^ 2 ^ (a - 1), hxpowM⟩ : M) = x ^ 2 ^ (a - 1) := Subtype.ext (by simp)
    rw [h1, map_pow, hxρ, ← map_pow, hcpow, hι]
  have hxsq : ((x : G) ^ 2 ^ (a - 1)) ^ 2 = 1 := by
    rw [← pow_mul, show 2 ^ (a - 1) * 2 = 2 ^ a by rw [← pow_succ]; congr 1; omega,
      ← hxo, ← Subgroup.orderOf_coe, pow_orderOf_eq_one]
  have hconj : IsConj t ((x : G) ^ 2 ^ (a - 1)) :=
    EPilot.isConj_of_action_eq ρ hker htM hxpowM ht2 hxsq hρx.symm
  exact EPilot.exists_normal_index_two_of_unique_of_quotientSub H huniq x.2 ha1
    (by rw [Subgroup.orderOf_coe, hxo]) hxQ hQ hconj

end CFSG.SeitzReduction.SymplecticPilot
