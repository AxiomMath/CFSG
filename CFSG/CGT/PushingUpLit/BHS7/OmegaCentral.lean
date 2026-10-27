module

public import CFSG.CGT.PushingUpLit.BHS7.OmegaBasic

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

@[expose] def omegaJoin (G T : Subgroup Γ) : Subgroup Γ := ⨆ E ∈ omegaSet G T, E

@[expose] def omegaW (G T : Subgroup Γ) : Subgroup Γ := ⨆ E ∈ omegaSet G T, blockW E

@[expose] def omegaR (G T : Subgroup Γ) : Subgroup Γ :=
  G ⊓ Subgroup.centralizer (omegaW G T : Set Γ)

theorem blockW_conjSub (g : Γ) (E : Subgroup Γ) :
    blockW (A1b.conjSub g E) = A1b.conjSub g (blockW E) := by
  unfold blockW
  rw [pCoreOf_conjSub, omegaOneCenterOf_conjSub, commutator_conjSub]

theorem mem_normalizer_biSup {𝒮 : Set (Subgroup Γ)} (f : Subgroup Γ → Subgroup Γ) {g : Γ}
    (hf : ∀ K, A1b.conjSub g (f K) = f (A1b.conjSub g K))
    (hf' : ∀ K, A1b.conjSub g⁻¹ (f K) = f (A1b.conjSub g⁻¹ K))
    (h : ∀ K ∈ 𝒮, A1b.conjSub g K ∈ 𝒮) (h' : ∀ K ∈ 𝒮, A1b.conjSub g⁻¹ K ∈ 𝒮) :
    g ∈ Subgroup.normalizer ((⨆ K ∈ 𝒮, f K : Subgroup Γ) : Set Γ) := by
  have key : ∀ z : Γ, (∀ K, A1b.conjSub z (f K) = f (A1b.conjSub z K)) →
      (∀ K ∈ 𝒮, A1b.conjSub z K ∈ 𝒮) →
      A1b.conjSub z (⨆ K ∈ 𝒮, f K : Subgroup Γ) ≤ ⨆ K ∈ 𝒮, f K := by
    intro z hz hz'
    rw [conjSub_iSup]
    refine iSup_le fun K => ?_
    rw [conjSub_iSup]
    refine iSup_le fun hK => ?_
    rw [hz K]
    exact le_iSup₂_of_le (f := fun (K' : Subgroup Γ) (_ : K' ∈ 𝒮) => f K')
      (A1b.conjSub z K) (hz' K hK) le_rfl
  exact mem_normalizer_of_conjSub_le (key g hf h) (key g⁻¹ hf' h')

variable {G T : Subgroup Γ}

theorem omegaJoin_le : omegaJoin G T ≤ G := by
  refine iSup₂_le fun E hE => ?_
  obtain ⟨g, -, hb⟩ := (mem_btBlocksMax_of_mem_bStarG hE.1).1
  exact hb.le

theorem le_normalizer_omegaW : G ≤ Subgroup.normalizer ((omegaW G T : Subgroup Γ) : Set Γ) :=
  fun g hg =>
    mem_normalizer_biSup blockW (fun K => (blockW_conjSub g K).symm)
      (fun K => (blockW_conjSub g⁻¹ K).symm) (fun _ hK => conjSub_mem_omegaSet hK hg)
      (fun _ hK => conjSub_mem_omegaSet hK (G.inv_mem hg))

theorem le_normalizer_omegaR : G ≤ Subgroup.normalizer ((omegaR G T : Subgroup Γ) : Set Γ) :=
  fun _ hg => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hg, B6.le_normalizer_centralizer le_normalizer_omegaW hg⟩

theorem omegaR_le : omegaR G T ≤ G := inf_le_left

theorem blockW_le_omegaW {E : Subgroup Γ} (hE : E ∈ omegaSet G T) : blockW E ≤ omegaW G T :=
  le_iSup₂_of_le (f := fun (E' : Subgroup Γ) (_ : E' ∈ omegaSet G T) => blockW E') E hE le_rfl

theorem le_omegaJoin {E : Subgroup Γ} (hE : E ∈ omegaSet G T) : E ≤ omegaJoin G T :=
  le_iSup₂_of_le (f := fun (E' : Subgroup Γ) (_ : E' ∈ omegaSet G T) => E') E hE le_rfl

variable [Finite Γ]

theorem omega_not_le_omegaR (h : MinCex G T) {E : Subgroup Γ}
    (hE : E ∈ omegaSet G T) : ¬ E ≤ omegaR G T := by
  intro hER
  have hEb : IsBTBlock G T E := omega_isBTBlock h hE
  have hWne : blockW E ≠ ⊥ := by
    rw [blockW_eq_pCoreOf hEb]
    exact pCoreOf_ne_bot hEb (charTwo_of_isBTBlock h.charTwo h.sylow hEb)
  have hperf : ⁅blockW E, E⁆ = blockW E := by
    rw [blockW_eq_pCoreOf hEb]
    exact hEb.perfect
  apply hWne
  rw [← hperf, eq_bot_iff, Subgroup.commutator_le]
  intro w hw e he
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact Subgroup.mem_centralizer_iff.mp (hER he).2 w (blockW_le_omegaW hE hw)

omit [Finite Γ] in
theorem mem_of_odd_orderOf_sup {R T : Subgroup Γ} (hT : IsPGroup 2 ↥T)
    (hTR : T ≤ Subgroup.normalizer (R : Set Γ)) {x : Γ} (hx : x ∈ R ⊔ T)
    (hodd : Odd (orderOf x)) : x ∈ R := by
  have hRH : R ≤ R ⊔ T := le_sup_left
  have hHN : R ⊔ T ≤ Subgroup.normalizer (R : Set Γ) := sup_le Subgroup.le_normalizer hTR
  have : (R.subgroupOf (R ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRH).mpr hHN
  have hx' : x ∈ T ⊔ R := by rwa [sup_comm]
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right T R hTR] at hx'
  obtain ⟨t, ht, r, hr, rfl⟩ := hx'
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  set π := QuotientGroup.mk' (R.subgroupOf (R ⊔ T)) with hπ
  have hxH : t * r ∈ R ⊔ T := hx
  have hπr : π ⟨r, (le_sup_left : R ≤ R ⊔ T) hr⟩ = 1 := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hr
  have hπx : π ⟨t * r, hxH⟩ = π ⟨t, (le_sup_right : T ≤ R ⊔ T) ht⟩ := by
    have : (⟨t * r, hxH⟩ : ↥(R ⊔ T)) = ⟨t, (le_sup_right : T ≤ R ⊔ T) ht⟩ *
        ⟨r, (le_sup_left : R ≤ R ⊔ T) hr⟩ := rfl
    rw [this, map_mul, hπr, mul_one]
  have hd1 : orderOf (π ⟨t * r, hxH⟩) ∣ orderOf (t * r) := by
    have h1 := orderOf_map_dvd π (⟨t * r, hxH⟩ : ↥(R ⊔ T))
    have h2 : orderOf (⟨t * r, hxH⟩ : ↥(R ⊔ T)) = orderOf (t * r) := Subgroup.orderOf_mk _ _
    rwa [h2] at h1
  have hd2 : orderOf (π ⟨t * r, hxH⟩) ∣ 2 ^ k := by
    rw [hπx]
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow]
    have : (⟨t, (le_sup_right : T ≤ R ⊔ T) ht⟩ : ↥(R ⊔ T)) ^ (2 ^ k) = 1 := by
      have h3 : t ^ (2 ^ k) = 1 := by
        have := congrArg (fun z : ↥T => (z : Γ)) hk
        simpa using this
      exact Subtype.ext h3
    rw [this, map_one]
  have hcop : Nat.Coprime (2 ^ k) (orderOf (t * r)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h1 : orderOf (π ⟨t * r, hxH⟩) = 1 :=
    Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hd2 hd1)
  have h2 : π ⟨t * r, hxH⟩ = 1 := orderOf_eq_one_iff.mp h1
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact h2

end CFSG.CGT.PushingUpLit.BHS7
