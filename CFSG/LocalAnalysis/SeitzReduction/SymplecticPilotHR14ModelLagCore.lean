module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OPNonembed
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaOuterCount

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Module CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

variable {K : Type} [Field K]

section Small

variable {M : Type} [AddCommGroup M] [Module K M]

theorem eq_one_of_pow_prime_of_not_dvd [Finite K] [FiniteDimensional K M] {y : M ≃ₗ[K] M}
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hy : y ^ ℓ = 1) (hℓq : ¬ ℓ ∣ Nat.card K)
    (hord : ∀ j, 1 ≤ j → j ≤ finrank K M → ¬ ℓ ∣ Nat.card K ^ j - 1) : y = 1 := by
  have := Fintype.ofFinite K
  rcases (Nat.dvd_prime hℓ).1 (orderOf_dvd_of_pow_eq_one hy) with h1 | h1
  · exact orderOf_eq_one_iff.1 h1
  · exfalso
    have h2 : orderOf y ∣ Nat.card (M ≃ₗ[K] M) := orderOf_dvd_natCard y
    rw [h1, natCard_linearEquiv_self_eq] at h2
    refine not_dvd_prod_pow_sub_pow hℓ (by rwa [← Nat.card_eq_fintype_card]) ?_ h2
    intro j hj hjd
    rw [← Nat.card_eq_fintype_card]
    exact hord j hj hjd

theorem eq_one_of_fix_of_finrank_le [Finite K] [FiniteDimensional K M] {y : M ≃ₗ[K] M}
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hy : y ^ ℓ = 1) (hℓK : (ℓ : K) ≠ 0) (hℓq : ¬ ℓ ∣ Nat.card K)
    (C : Submodule K M) (hC : ∀ c ∈ C, y c = c) {d : ℕ} (hd : finrank K M ≤ finrank K C + d)
    (hord : ∀ j, 1 ≤ j → j ≤ d → ¬ ℓ ∣ Nat.card K ^ j - 1) : y = 1 := by
  set D := LinearMap.range ((y : M →ₗ[K] M) - 1) with hD
  have hker : LinearMap.ker ((y : M →ₗ[K] M) - 1) ⊓ D = ⊥ := ker_inf_range_sub_one_eq_bot hy hℓK
  have hCker : C ≤ LinearMap.ker ((y : M →ₗ[K] M) - 1) := fun c hc => by
    rw [LinearMap.mem_ker]
    simp [hC c hc]
  have hDC : D ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [← hker]
    exact ⟨hCker hv.2, hv.1⟩
  have hdimD : finrank K D ≤ d := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq D C
    rw [hDC, finrank_bot] at h1
    have h2 := Submodule.finrank_le (D ⊔ C)
    omega
  have hU : ∀ w ∈ zpowers y, ∀ u ∈ D, (MonoidHom.id (M ≃ₗ[K] M)) w u ∈ D := by
    intro w hw u hu
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hu
    refine ⟨(y ^ k) v, ?_⟩
    have hc : (y ^ k) (y v) = y ((y ^ k) v) := by
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, (Commute.zpow_left rfl k).eq]
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply,
      MonoidHom.id_apply, map_sub, hc]
  set res := opRestrict (MonoidHom.id (M ≃ₗ[K] M)) (zpowers y) D hU with hres
  have hres1 : res ⟨y, mem_zpowers y⟩ = 1 := by
    refine eq_one_of_pow_prime_of_not_dvd hℓ ?_ hℓq fun j hj hjd => hord j hj (hjd.trans hdimD)
    rw [← map_pow, show (⟨y, mem_zpowers y⟩ : zpowers y) ^ ℓ = 1 from Subtype.ext hy, map_one]
  have hDker : D ≤ LinearMap.ker ((y : M →ₗ[K] M) - 1) := by
    intro u hu
    have := congrArg (fun f : D ≃ₗ[K] D => ((f ⟨u, hu⟩ : D) : M)) hres1
    simp only [hres, opRestrict_apply, MonoidHom.id_apply] at this
    rw [LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply]
    rw [this]
    simp
  have hD0 : D = ⊥ := by
    rw [eq_bot_iff, ← hker]
    exact le_inf hDker le_rfl
  rw [hD, LinearMap.range_eq_bot, sub_eq_zero] at hD0
  exact LinearEquiv.ext fun v => by
    have := LinearMap.congr_fun hD0 v
    simpa using this

theorem eq_one_of_isSimpleGroup {X Z : Type*} [Group X] [IsSimpleGroup X] [Group Z]
    (f : X →* Z) {x : X} (hx : x ≠ 1) (hfx : f x = 1) (g : X) : f g = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · exact absurd ((MonoidHom.ker_eq_bot_iff f).1 h (by rw [hfx, map_one])) hx
  · exact MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top g)

end Small

section Core

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (finrank_standard)

theorem isoSeq_le_isoSeq_finrank {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {H : Type} [Group H] (F : ReflForm K V) (ρ : H →* Module.End K V)
    (R : Subgroup H) (j : ℕ) : isoSeq F ρ R j ≤ isoSeq F ρ R (finrank K V) := by
  rcases le_total j (finrank K V) with h | h
  · exact isoSeq_mono F ρ R h
  · rw [isoSeq_eq_of_le F ρ R h]

theorem card_le_of_lagrangian_core [Finite K] [CharP K 2] {H : Type} [Group H] [Finite H]
    {m n : ℕ} (hm : 1 ≤ m) (hn : n + 1 = 2 * m) (ψ : H →* StatedSp n K)
    (hψ : Function.Injective ψ)
    (R X : Subgroup H) (hR : IsPGroup 2 R) (hXN : X ≤ normalizer (R : Set H))
    [IsSimpleGroup X] (hXp : Group.IsPerfect X) (hRX : ⁅R, X⁆ = R)
    (hC : ∀ r ∈ R, (∀ x ∈ X, x * r = r * x) → r = 1)
    {x : H} (hx : x ∈ X) (hx1 : x ≠ 1) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hxℓ : x ^ ℓ = 1)
    (hord : ∀ j, 1 ≤ j → j < 2 * m → ¬ ℓ ∣ Nat.card K ^ j - 1) :
    Nat.card R ≤ Nat.card K ^ (2 * m * (m - 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ : H →* Module.End K (Fin n ⊕ Fin n → K) := (natRep (StatedSp n K)).comp ψ with hρdef
  have hρ : IsIsometric (spForm n K) ρ := fun h u v => isIsometric_natRep_statedSp n K (ψ h) u v
  have hinj : Function.Injective ρ := (natRep_injective _).comp hψ
  have hdimV : finrank K (Fin n ⊕ Fin n → K) = 2 * n := finrank_standard
  set W := isoSeq (spForm n K) ρ R (finrank K (Fin n ⊕ Fin n → K)) with hWdef
  have hWiso : (spForm n K).IsTotallyIsotropic W :=
    isoSeq_isTotallyIsotropic (spForm n K) ρ R (finrank K (Fin n ⊕ Fin n → K))
  have hk : 2 * finrank K W ≤ 2 * n := by
    have : 2 * finrank K W ≤ finrank K (Fin n ⊕ Fin n → K) :=
      two_mul_finrank_le_of_isTotallyIsotropic (spForm n K) hWiso
    omega
  have hℓK : (ℓ : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K 2] at h0
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).1 h0).symm
  have hℓq : ¬ ℓ ∣ Nat.card K := by
    have := Fintype.ofFinite K
    obtain ⟨f, -, hf⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hf]
    intro hd
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow hd))
  have hxX : (⟨x, hx⟩ : X) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hxXℓ : (⟨x, hx⟩ : X) ^ ℓ = 1 := Subtype.ext (by simp [hxℓ])
  have hXW : ∀ g ∈ X, ∀ u ∈ W, opNatEquiv ψ g u ∈ W := fun g hg u hu =>
    apply_mem_isoSeq (spForm n K) ρ hρ R _ (hXN hg) hu
  have hXP : ∀ g ∈ X, ∀ u ∈ (spForm n K).perp W, opNatEquiv ψ g u ∈ (spForm n K).perp W :=
    fun g hg u hu => hρ.apply_mem_perp_of_forall (fun w hw => hXW _ (inv_mem hg) w hw) hu
  have hfixW : ∀ g ∈ X, ∀ u ∈ W, ρ g u = u := by
    set res := opRestrict (opNatEquiv ψ) X W hXW with hres
    have h1 : res ⟨x, hx⟩ = 1 := by
      refine eq_one_of_pow_prime_of_not_dvd hℓ ?_ hℓq fun j hj hjk => hord j hj (by omega)
      rw [← map_pow, hxXℓ, map_one]
    intro g hg u hu
    have h2 := eq_one_of_isSimpleGroup res hxX h1 ⟨g, hg⟩
    exact congrArg (fun f : W ≃ₗ[K] W => ((f ⟨u, hu⟩ : W) : Fin n ⊕ Fin n → K)) h2
  have htriv : ∀ g ∈ X, ∀ k, ∀ v ∈ isoSeq (spForm n K) ρ R (k + 1),
      ρ g v - v ∈ isoSeq (spForm n K) ρ R k := fun g hg k v hv => by
    rw [hfixW g hg v (isoSeq_le_isoSeq_finrank _ ρ R _ hv), sub_self]
    exact zero_mem _
  have hkm : finrank K W + 1 ≤ m := by
    by_contra hkm
    set P := (spForm n K).perp W with hPdef
    set res' := opRestrict (opNatEquiv ψ) X P hXP with hres'
    have hWP : W ≤ P := hWiso
    have hCdim : finrank K (W.comap P.subtype) = finrank K W :=
      (Submodule.comapSubtypeEquivOfLe hWP).finrank_eq
    have hPdim : finrank K P + finrank K W = 2 * n := by
      have : finrank K P + finrank K W = finrank K (Fin n ⊕ Fin n → K) :=
        finrank_perp_add_finrank (spForm n K) W
      omega
    have h1 : res' ⟨x, hx⟩ = 1 := by
      refine eq_one_of_fix_of_finrank_le hℓ ?_ hℓK hℓq (W.comap P.subtype) ?_ (d := 2 * m - 1)
        ?_ ?_
      · rw [← map_pow, hxXℓ, map_one]
      · intro c hc
        exact Subtype.ext (hfixW x hx c hc)
      · rw [hCdim]
        omega
      · intro j hj hjd
        exact hord j hj (by omega)
    have hfixP : ∀ g ∈ X, ∀ u ∈ P, ρ g u = u := by
      intro g hg u hu
      have h2 := eq_one_of_isSimpleGroup res' hxX h1 ⟨g, hg⟩
      exact congrArg (fun f : P ≃ₗ[K] P => ((f ⟨u, hu⟩ : P) : Fin n ⊕ Fin n → K)) h2
    have hmid : ∀ g ∈ X, ∀ v ∈ (spForm n K).perp W, ρ g v - v ∈ W := fun g hg v hv => by
      rw [hfixP g hg v hv, sub_self]
      exact zero_mem _
    have hbot := eq_bot_of_le_normalizer_of_triv (spForm n K) ρ 2 hρ hinj R hXp hXN htriv hmid
    rw [hbot, Subgroup.mem_bot] at hx
    exact hx1 hx
  have hcount := spBorelTitsCountInput_holds K (Fin n ⊕ Fin n → K) (spForm n K) H ρ hρ hinj R X
    hR hXN hXp hRX hC htriv
  refine hcount.trans (Nat.pow_le_pow_right Nat.card_pos ?_)
  obtain ⟨k, hkdef⟩ : ∃ k, finrank K W = k := ⟨_, rfl⟩
  rw [hkdef] at hkm
  rw [hkdef, hdimV]
  obtain ⟨t, ht⟩ : ∃ t, m = k + 1 + t := ⟨m - (k + 1), by omega⟩
  have e1 : 2 * n - 2 * k = 2 * k + 4 * t + 2 := by omega
  have e2 : m - 1 = k + t := by omega
  rw [e1, e2, ht]
  nlinarith

end Core

end CFSG.SeitzReduction.SymplecticPilot
