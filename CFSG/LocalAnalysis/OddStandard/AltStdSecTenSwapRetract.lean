module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapLift
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup Equiv Equiv.Perm

open scoped Pointwise

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

theorem CentData.not_sq (hC : CentData z ι) (y : G) : y * y ≠ z := by
  intro hy
  have hyz : y ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    rw [← hy]
    group
  obtain ⟨σ, hσ | hσ⟩ := hC.cases y hyz
  · apply hC.ne_z (σ * σ)
    rw [map_mul, ← hσ, hy]
  · apply hC.ne_z (σ * σ)
    rw [map_mul]
    have h : z = (z * ι σ) * (z * ι σ) := by rw [← hσ, hy]
    have h2 : (z * ι σ) * (z * ι σ) = ι σ * ι σ := by
      calc (z * ι σ) * (z * ι σ) = z * (ι σ * z) * ι σ := by group
        _ = z * (z * ι σ) * ι σ := by rw [hC.comm σ]
        _ = (z * z) * (ι σ * ι σ) := by group
        _ = ι σ * ι σ := by rw [hC.mul_self, one_mul]
    rw [← h2]
    exact h.symm

theorem CentData.exists_twist (hC : CentData z ι) :
    ∃ ι' : Perm (Fin 10) →* G, CentData z ι' ∧ (∀ σ, sign σ = 1 → ι' σ = ι σ) ∧
      (∀ σ, sign σ = -1 → ι' σ = z * ι σ) := by
  let f : Perm (Fin 10) → G := fun σ => if sign σ = 1 then ι σ else z * ι σ
  have hf_mul : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    simp only [f]
    have hab : sign (a * b) = sign a * sign b := Equiv.Perm.sign_mul a b
    rcases Int.units_eq_one_or (sign a) with ha | ha <;>
      rcases Int.units_eq_one_or (sign b) with hb | hb
    · rw [if_pos (by rw [hab, ha, hb, one_mul]), if_pos ha, if_pos hb, map_mul]
    · rw [if_neg (by rw [hab, ha, hb]; decide), if_pos ha, if_neg (by rw [hb]; decide),
        map_mul]
      rw [← mul_assoc, hC.comm a, mul_assoc]
    · rw [if_neg (by rw [hab, ha, hb]; decide), if_neg (by rw [ha]; decide), if_pos hb,
        map_mul]
      rw [mul_assoc]
    · rw [if_pos (by rw [hab, ha, hb]; decide), if_neg (by rw [ha]; decide),
        if_neg (by rw [hb]; decide), map_mul]
      have h : (z * ι a) * (z * ι b) = ι a * ι b := by
        calc (z * ι a) * (z * ι b) = z * (ι a * z) * ι b := by group
          _ = z * (z * ι a) * ι b := by rw [hC.comm a]
          _ = (z * z) * (ι a * ι b) := by group
          _ = ι a * ι b := by rw [hC.mul_self, one_mul]
      exact h.symm
  let ι' : Perm (Fin 10) →* G := MonoidHom.mk' f hf_mul
  have h1 : ∀ σ, sign σ = 1 → ι' σ = ι σ := by
    intro σ hs
    show (if sign σ = 1 then ι σ else z * ι σ) = ι σ
    rw [if_pos hs]
  have h2 : ∀ σ, sign σ = -1 → ι' σ = z * ι σ := by
    intro σ hs
    show (if sign σ = 1 then ι σ else z * ι σ) = z * ι σ
    rw [if_neg]
    rw [hs]
    decide
  have hzι : ∀ σ, z * (z * ι σ) = ι σ := fun σ => by
    rw [← mul_assoc, hC.mul_self, one_mul]
  have hinj : Function.Injective ι' := by
    intro a b hab
    rcases Int.units_eq_one_or (sign a) with ha | ha <;>
      rcases Int.units_eq_one_or (sign b) with hb | hb
    · rw [h1 a ha, h1 b hb] at hab
      exact hC.inj hab
    · exfalso
      have h : ι (a * b⁻¹) = z := by
        rw [map_mul, map_inv, ← h1 a ha, hab, h2 b hb]
        group
      exact hC.ne_z _ h
    · exfalso
      have h : ι (b * a⁻¹) = z := by
        rw [map_mul, map_inv, ← h1 b hb, ← hab, h2 a ha]
        group
      exact hC.ne_z _ h
    · have h : ι a = ι b := by
        rw [h2 a ha, h2 b hb] at hab
        exact mul_left_cancel hab
      exact hC.inj h
  have hcomm : ∀ σ, z * ι' σ = ι' σ * z := by
    intro σ
    rcases Int.units_eq_one_or (sign σ) with hs | hs
    · rw [h1 σ hs]
      exact hC.comm σ
    · rw [h2 σ hs, hzι σ]
      rw [mul_assoc, ← hC.comm σ, ← mul_assoc, hC.mul_self, one_mul]
  have hne : ∀ σ, ι' σ ≠ z := by
    intro σ hs
    rcases Int.units_eq_one_or (sign σ) with h | h
    · rw [h1 σ h] at hs
      exact hC.ne_z σ hs
    · rw [h2 σ h] at hs
      have hι : ι σ = 1 := by
        have hs' : z * ι σ = z * 1 := by rw [hs, mul_one]
        exact mul_left_cancel hs'
      have hσ1 : σ = 1 := hC.inj (by rw [hι, map_one])
      rw [hσ1] at h
      exact absurd h (by decide)
  refine ⟨ι', ⟨hC.order, hinj, hcomm, hne, ?_⟩, h1, h2⟩
  intro g hg
  obtain ⟨σ, hσ | hσ⟩ := hC.cases g hg
  · rcases Int.units_eq_one_or (sign σ) with hs | hs
    · exact ⟨σ, Or.inl (by rw [h1 σ hs, hσ])⟩
    · exact ⟨σ, Or.inr (by rw [hσ, h2 σ hs, hzι σ])⟩
  · rcases Int.units_eq_one_or (sign σ) with hs | hs
    · exact ⟨σ, Or.inr (by rw [h1 σ hs, hσ])⟩
    · exact ⟨σ, Or.inl (by rw [hσ, h2 σ hs])⟩

theorem NoSwapConj.twist (hC : CentData z ι) (hN : NoSwapConj z ι) {ι' : Perm (Fin 10) →* G}
    (h1 : ∀ σ, sign σ = 1 → ι' σ = ι σ) (h2 : ∀ σ, sign σ = -1 → ι' σ = z * ι σ) :
    NoSwapConj z ι' := by
  intro σ hσ
  have hs : sign σ = -1 := hσ.sign_eq
  have hz : z * ι' σ = ι σ := by
    rw [h2 σ hs]
    exact (by rw [← mul_assoc, hC.mul_self, one_mul] : z * (z * ι σ) = ι σ)
  constructor
  · rw [h2 σ hs]
    exact (hN σ hσ).2
  · rw [hz]
    exact (hN σ hσ).1

theorem SymSec.card_centralizer [Finite G] {x : G}
    {π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10)}
    (hS : SymSec x π) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    Nat.card ↥(centralizer ({x} : Set G)) = 2 * Nat.factorial 10 := by
  have hx2' : (selfC x) ^ 2 = 1 := by
    rw [pow_two]
    apply Subtype.ext
    simpa [selfC] using hx2
  have hx1' : selfC x ≠ 1 := by
    intro h
    apply hx1
    have := congrArg (Subtype.val) h
    simpa [selfC] using this
  have horder : orderOf (selfC x) = 2 := orderOf_eq_prime hx2' hx1'
  have hker : π.ker = zpowers (selfC x) := by
    ext c
    rw [MonoidHom.mem_ker, hS.ker c, mem_zpowers_selfC_iff hx2]
  have hkercard : Nat.card ↥(π.ker) = 2 := by
    rw [hker, Nat.card_zpowers, horder]
  have hrange : π.range = ⊤ := MonoidHom.range_eq_top.2 hS.surj
  have hquot : Nat.card (↥(centralizer ({x} : Set G)) ⧸ π.ker) = Nat.factorial 10 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange π).toEquiv, hrange,
      Subgroup.card_top, Nat.card_perm, Nat.card_fin]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (π.ker), hquot, hkercard, Nat.mul_comm]

theorem isConj_of_retraction {x : G} {π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10)}
    (hS : SymSec x π) {κ : ↥(centralizer ({x} : Set G)) →* ℤˣ} (hκ : κ (selfC x) = -1)
    {c c' : ↥(centralizer ({x} : Set G))} (hπ : IsConj (π c) (π c')) (hκc : κ c = κ c') :
    IsConj (c : G) (c' : G) := by
  obtain ⟨g', hg'⟩ := isConj_iff.1 hπ.symm
  obtain ⟨g, hg⟩ := hS.surj g'
  let d : ↥(centralizer ({x} : Set G)) := g * c' * g⁻¹
  have hπd : π d = π c := by
    simp only [d, map_mul, map_inv, hg]
    exact hg'
  have hmem : π (d * c⁻¹) = 1 := by
    rw [map_mul, map_inv, hπd]
    group
  have hκd : κ d = κ c := by
    have hd : κ d = κ c' := by
      simp only [d, map_mul, map_inv]
      rw [mul_comm (κ g) (κ c')]
      group
    rw [hd, hκc]
  rcases (hS.ker (d * c⁻¹)).1 hmem with h1 | h1
  · have hd : d = c := by
      have h1' : d * c⁻¹ = 1 := Subtype.ext h1
      rwa [mul_inv_eq_one] at h1'
    refine (isConj_iff.2 ⟨(g : G), ?_⟩).symm
    have hdc : (d : G) = (c : G) := congrArg Subtype.val hd
    rw [← hdc]
    simp only [d]
    rfl
  · have h1' : d * c⁻¹ = selfC x := Subtype.ext (by simpa [selfC] using h1)
    have hd : d = selfC x * c := by
      calc d = d * c⁻¹ * c := by group
        _ = selfC x * c := by rw [h1']
    have hc : (-1 : ℤˣ) = 1 := by
      have h := hκd
      rw [hd, map_mul, hκ] at h
      have := congrArg (fun u : ℤˣ => u * (κ c)⁻¹) h
      simpa [mul_assoc] using this
    exact absurd hc (by decide)

private theorem mem_zpowers_iff_eq_one_or_of_mul_self {H : Type*} [Group H] {g : H}
    (hg : g * g = 1) (c : H) : c ∈ zpowers g ↔ c = 1 ∨ c = g := by
  constructor
  · intro hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    have hg2 : g ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hg
    rw [zpow_eq_zpow_emod k hg2]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left; rw [h0, zpow_zero]
    · right; rw [h1, zpow_one]
  · intro h
    rcases h with h1 | h1
    · rw [h1]; exact Subgroup.one_mem _
    · rw [h1]; exact Subgroup.mem_zpowers g

private theorem card_sup_of_commute_inf_eq_bot {H : Type*} [Group H] {P Q : Subgroup H}
    (hcomm : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a) (h : P ⊓ Q = ⊥) :
    Nat.card ↥(P ⊔ Q) = Nat.card ↥P * Nat.card ↥Q := by
  have hLE : P ≤ Subgroup.normalizer (Q : Set H) :=
    (show P ≤ Subgroup.centralizer (Q : Set H) from
      fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => (hcomm a ha b hb).symm).trans
      (Subgroup.centralizer_le_normalizer (Q : Set H))
  have hset : (↑(P ⊔ Q) : Set H) = (P : Set H) * (Q : Set H) :=
    Subgroup.coe_mul_of_left_le_normalizer_right P Q hLE
  have hbij : Function.Bijective (fun x : ↥P × ↥Q =>
      (⟨(x.1 : H) * (x.2 : H), Subgroup.mul_mem_sup x.1.2 x.2.2⟩ : ↥(P ⊔ Q))) := by
    constructor
    · rintro ⟨a1, b1⟩ ⟨a2, b2⟩ heq
      have he : (a1 : H) * b1 = a2 * b2 := Subtype.ext_iff.mp heq
      have hkey : (a2⁻¹ * a1 : H) = b2 * b1⁻¹ := by
        have := congrArg (fun x : H => a2⁻¹ * x * b1⁻¹) he
        simpa [mul_assoc] using this
      have hmem : (a2⁻¹ * a1 : H) ∈ P ⊓ Q := by
        refine ⟨P.mul_mem (P.inv_mem a2.2) a1.2, ?_⟩
        rw [hkey]
        exact Q.mul_mem b2.2 (Q.inv_mem b1.2)
      have hone : (a2⁻¹ * a1 : H) = 1 := by rw [h] at hmem; exact hmem
      have ha : a1 = a2 := Subtype.ext (inv_mul_eq_one.1 hone).symm
      have hb : b1 = b2 := by
        have hb1 : (b2 * b1⁻¹ : H) = 1 := hkey ▸ hone
        exact Subtype.ext (mul_inv_eq_one.1 hb1).symm
      exact Prod.ext ha hb
    · rintro ⟨w, hw⟩
      have hw' : w ∈ (P : Set H) * (Q : Set H) := by
        rw [← hset, SetLike.mem_coe]
        exact hw
      obtain ⟨a, ha, b, hb, rfl⟩ := hw'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  calc Nat.card ↥(P ⊔ Q) = Nat.card (↥P × ↥Q) :=
        (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
    _ = Nat.card ↥P * Nat.card ↥Q := Nat.card_prod P Q

private theorem selfC_mul_self {x : G} (hx2 : x * x = 1) : selfC x * selfC x = 1 := by
  apply Subtype.ext
  simpa [selfC] using hx2

private theorem selfC_ne_one {x : G} (hx1 : x ≠ 1) : selfC x ≠ 1 := by
  intro h
  apply hx1
  have := congrArg (Subtype.val) h
  simpa [selfC] using this

private theorem factorization_factorial_eight : (Nat.factorial 8).factorization 2 = 7 := by
  have hp : Nat.Prime 2 := by norm_num
  have hn : Nat.factorial 8 ≠ 0 := Nat.factorial_ne_zero 8
  have hge : 7 ≤ (Nat.factorial 8).factorization 2 := by
    rw [← hp.pow_dvd_iff_le_factorization hn]
    norm_num
  have hle : (Nat.factorial 8).factorization 2 ≤ 7 := by
    by_contra h
    have h8 : 2 ^ 8 ∣ Nat.factorial 8 :=
      (hp.pow_dvd_iff_le_factorization hn).2 (by omega)
    norm_num at h8
  omega

private theorem factorization_two_mul_factorial_ten :
    (2 * Nat.factorial 10).factorization 2 = 9 := by
  have hp : Nat.Prime 2 := by norm_num
  have hn : 2 * Nat.factorial 10 ≠ 0 := by positivity
  have hge : 9 ≤ (2 * Nat.factorial 10).factorization 2 := by
    rw [← hp.pow_dvd_iff_le_factorization hn]
    norm_num
  have hle : (2 * Nat.factorial 10).factorization 2 ≤ 9 := by
    by_contra h
    have h10 : 2 ^ 10 ∣ 2 * Nat.factorial 10 :=
      (hp.pow_dvd_iff_le_factorization hn).2 (by omega)
    norm_num at h10
  omega

theorem exists_complement [Finite G] (hC : CentData z ι) {x : G}
    {π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10)} (hOS : OneSided z ι x π) :
    ∃ K : Subgroup ↥(centralizer ({x} : Set G)),
      zpowers (selfC x) ⊓ K = ⊥ ∧ zpowers (selfC x) ⊔ K = ⊤ := by
  have hτ0 : τ₀ * τ₀ = 1 := Equiv.swap_mul_self 8 9
  have hx2 : x * x = 1 := by
    rw [hOS.eq, ← map_mul, hτ0, map_one]
  have hx1 : x ≠ 1 := by
    intro h
    have h' : x = ι 1 := by rw [h, map_one]
    have h'' : τ₀ = 1 := hC.inj (by rw [← hOS.eq, h'])
    exact absurd h'' (by decide)
  have hzx : z ∈ centralizer ({x} : Set G) := by
    rw [hOS.eq]
    exact hC.z_mem_centralizer τ₀
  let zC : ↥(centralizer ({x} : Set G)) := ⟨z, hzx⟩
  have hβmem : ∀ ρ : Perm (Fin 8), ι (liftS8 ρ) ∈ centralizer ({x} : Set G) := by
    intro ρ
    rw [mem_centralizer_singleton_iff, hOS.eq, ← map_mul, ← map_mul, liftS8_mul_τ₀ ρ]
  let β : Perm (Fin 8) →* ↥(centralizer ({x} : Set G)) :=
    (ι.comp liftS8).codRestrict (centralizer ({x} : Set G)) hβmem
  have hβinj : Function.Injective β := by
    intro ρ ρ' h
    apply liftS8_injective
    apply hC.inj
    simpa [β] using congrArg Subtype.val h
  obtain ⟨P8⟩ := (Sylow.nonempty : Nonempty (Sylow 2 (Perm (Fin 8))))
  let B : Subgroup ↥(centralizer ({x} : Set G)) := (P8 : Subgroup (Perm (Fin 8))).map β
  let Q : Subgroup ↥(centralizer ({x} : Set G)) := zpowers zC ⊔ B
  let V : Subgroup ↥(centralizer ({x} : Set G)) := zpowers (selfC x)
  have hzC2 : zC * zC = 1 := by
    apply Subtype.ext
    simpa [zC] using hC.mul_self
  have hzC1 : zC ≠ 1 := by
    intro h
    have hz1 : z = 1 := by
      have := congrArg Subtype.val h
      simpa [zC] using this
    exact hC.ne_z 1 (by rw [map_one]; exact hz1.symm)
  have hzβ : zC ∈ Subgroup.centralizer (B : Set ↥(centralizer ({x} : Set G))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    obtain ⟨ρ, _, hρ⟩ := Subgroup.mem_map.1 hc
    rw [← hρ]
    exact Subtype.ext (by simpa [zC, β] using (hC.comm (liftS8 ρ)).symm)
  have hLE : zpowers zC ≤ Subgroup.normalizer (B : Set ↥(centralizer ({x} : Set G))) :=
    (Subgroup.zpowers_le.2 hzβ).trans (Subgroup.centralizer_le_normalizer _)
  have hQset : (Q : Set ↥(centralizer ({x} : Set G))) =
      (zpowers zC : Set ↥(centralizer ({x} : Set G))) *
        (B : Set ↥(centralizer ({x} : Set G))) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLE
  have hP8card : Nat.card ↥(P8 : Subgroup (Perm (Fin 8))) = 2 ^ 7 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_perm, Nat.card_fin, factorization_factorial_eight]
  have hzCcard : Nat.card ↥(zpowers zC) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hzC2) hzC1
  have hBcard : Nat.card ↥B = 2 ^ 7 := by
    change Nat.card ↥((P8 : Subgroup (Perm (Fin 8))).map β) = 2 ^ 7
    rw [Subgroup.card_map_of_injective hβinj, hP8card]
  have hbot : zpowers zC ⊓ B = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro c hc
    rw [Subgroup.mem_inf] at hc
    rcases (mem_zpowers_iff_eq_one_or_of_mul_self hzC2 c).1 hc.1 with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hc
      obtain ⟨ρ, _, hρ⟩ := Subgroup.mem_map.1 hc.2
      have hz : ι (liftS8 ρ) = z := by
        have := congrArg Subtype.val hρ
        simpa [zC, β] using this
      exact hC.ne_z _ hz
  have hcomm_zβ : ∀ a ∈ zpowers zC, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.1 ((Subgroup.zpowers_le.2 hzβ) ha) b hb).symm
  have hQcard : Nat.card ↥Q = 2 ^ 8 := by
    have := card_sup_of_commute_inf_eq_bot (H := ↥(centralizer ({x} : Set G))) hcomm_zβ hbot
    change Nat.card ↥(zpowers zC ⊔ B) = 2 ^ 8
    rw [this, hzCcard, hBcard]
    norm_num
  have hVcard : Nat.card ↥V = 2 := by
    change Nat.card ↥(zpowers (selfC x)) = 2
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact selfC_mul_self hx2) (selfC_ne_one hx1)
  have hself_cent : selfC x ∈ Subgroup.centralizer (Q : Set ↥(centralizer ({x} : Set G))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : q ∈ (zpowers zC : Set ↥(centralizer ({x} : Set G))) *
        (B : Set ↥(centralizer ({x} : Set G))) := by
      rw [← hQset, SetLike.mem_coe]; exact hq
    obtain ⟨a, ha, b, hb, rfl⟩ := hq'
    have ha_comm : a * selfC x = selfC x * a := by
      rcases (mem_zpowers_iff_eq_one_or_of_mul_self hzC2 a).1 ha with ha1 | ha1
      · simp only [ha1, one_mul, mul_one]
      · rw [ha1]
        exact Subtype.ext (by simpa [zC, selfC, hOS.eq] using hC.comm τ₀)
    have hb_comm : b * selfC x = selfC x * b := by
      obtain ⟨ρ, _, hρ⟩ := Subgroup.mem_map.1 hb
      rw [← hρ]
      exact Subtype.ext (by
        simpa [selfC, β, hOS.eq] using
          (show ι (liftS8 ρ) * ι τ₀ = ι τ₀ * ι (liftS8 ρ) from by
            rw [← map_mul, ← map_mul, liftS8_mul_τ₀ ρ]))
    calc a * b * selfC x = a * (b * selfC x) := by group
      _ = a * (selfC x * b) := by rw [hb_comm]
      _ = a * selfC x * b := by group
      _ = selfC x * a * b := by rw [ha_comm]
      _ = selfC x * (a * b) := by group
  have hcommVQ : ∀ a ∈ V, ∀ b ∈ Q, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.1 ((Subgroup.zpowers_le.2 hself_cent) ha) b hb).symm
  have hVQbot : V ⊓ Q = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro c hc
    rw [Subgroup.mem_inf] at hc
    rcases (mem_zpowers_iff_eq_one_or_of_mul_self (selfC_mul_self hx2) c).1 hc.1 with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hc
      have hcQ : selfC x ∈ (zpowers zC : Set ↥(centralizer ({x} : Set G))) *
          (B : Set ↥(centralizer ({x} : Set G))) := by
        rw [← hQset, SetLike.mem_coe]
        exact hc.2
      obtain ⟨a, ha, b, hb, hab⟩ := hcQ
      rcases (mem_zpowers_iff_eq_one_or_of_mul_self hzC2 a).1 ha with ha1 | ha1
      · simp only [ha1, one_mul] at hab
        obtain ⟨ρ, _, hρ⟩ := Subgroup.mem_map.1 hb
        rw [← hρ] at hab
        have hxβ : x = ι (liftS8 ρ) := by
          have := congrArg Subtype.val hab
          simpa [selfC, β] using this.symm
        have hρτ : liftS8 ρ = τ₀ := hC.inj (by rw [← hxβ, hOS.eq])
        have h8 := congrArg (fun f : Perm (Fin 10) => f 8) hρτ
        rw [liftS8_apply_eight] at h8
        rw [show (τ₀ : Perm (Fin 10)) 8 = 9 from Equiv.swap_apply_left 8 9] at h8
        exact absurd h8 (by decide)
      · rw [ha1] at hab
        obtain ⟨ρ, _, hρ⟩ := Subgroup.mem_map.1 hb
        rw [← hρ] at hab
        have hxβ : x = z * ι (liftS8 ρ) := by
          have := congrArg Subtype.val hab
          simpa [selfC, zC, β] using this.symm
        have hz : ι (τ₀ * (liftS8 ρ)⁻¹) = z := by
          rw [map_mul, map_inv, ← hOS.eq, hxβ]
          group
        exact hC.ne_z _ hz
  have hVQcard : Nat.card ↥(V ⊔ Q) = 2 ^ 9 := by
    have := card_sup_of_commute_inf_eq_bot (H := ↥(centralizer ({x} : Set G))) hcommVQ hVQbot
    change Nat.card ↥(zpowers (selfC x) ⊔ Q) = 2 ^ 9
    rw [this, hVcard, hQcard]
    norm_num
  have hCcard : Nat.card ↥(centralizer ({x} : Set G)) = 2 * Nat.factorial 10 :=
    hOS.sec.card_centralizer hx2 hx1
  have hfac : (Nat.card ↥(centralizer ({x} : Set G))).factorization 2 = 9 := by
    rw [hCcard]
    exact factorization_two_mul_factorial_ten
  have hcard : Nat.card ↥(V ⊔ Q) =
      2 ^ (Nat.card ↥(centralizer ({x} : Set G))).factorization 2 := by
    rw [hfac]
    exact hVQcard
  haveI hVnorm : V.Normal := normal_zpowers_selfC x
  haveI hVcomm : IsMulCommutative V := IsMulCommutative.of_comm fun a b => Subtype.ext (by
    have ha : (a : ↥(centralizer ({x} : Set G))) ∈
        Subgroup.center ↥(centralizer ({x} : Set G)) :=
      zpowers_le.2 (selfC_mem_center x) a.2
    exact (Subgroup.mem_center_iff.1 ha (b : ↥(centralizer ({x} : Set G)))).symm)
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 1) (by rw [hVcard]; norm_num)
  refine (CFSG.Quasithin.gaschutz (p := 2) (V := V) hVp
    (Sylow.ofCard (V ⊔ Q) hcard)).2 ⟨Q, ?_, hVQbot, ?_⟩
  · rw [Sylow.coe_ofCard]
    exact le_sup_right
  · rw [Sylow.coe_ofCard]

theorem exists_retraction [Finite G] (hC : CentData z ι) {x : G}
    {π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10)} (hOS : OneSided z ι x π) :
    ∃ κ : ↥(centralizer ({x} : Set G)) →* ℤˣ, Retraction z x κ := by
  classical
  let C := ↥(centralizer ({x} : Set G))
  let V : Subgroup C := zpowers (selfC x)
  obtain ⟨K, hVKbot, hVKsup⟩ := exists_complement (G := G) hC hOS
  have hx2 : x * x = 1 := by
    rw [hOS.eq, ← map_mul, show τ₀ * τ₀ = 1 from Equiv.swap_mul_self 8 9, map_one]
  have hx1 : x ≠ 1 := by
    intro h
    have h' : x = ι 1 := by rw [h, map_one]
    have h'' : τ₀ = 1 := hC.inj (by rw [← hOS.eq, h'])
    exact absurd h'' (by decide)
  have hzx : z ∈ centralizer ({x} : Set G) := by
    rw [hOS.eq]
    exact hC.z_mem_centralizer τ₀
  haveI hVnorm : V.Normal := normal_zpowers_selfC x
  have hiff : ∀ c d : C, c * d ∈ K ↔ (c ∈ K ↔ d ∈ K) := by
    intro c d
    have hc : c ∈ V ⊔ K := by rw [hVKsup]; trivial
    have hd : d ∈ V ⊔ K := by rw [hVKsup]; trivial
    obtain ⟨v, hv, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hc
    obtain ⟨v', hv', k', hk', rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hd
    have hgen : ∀ w ∈ V, ∀ m ∈ K, (w * m : C) ∈ K ↔ w = 1 := by
      intro w hw m hm
      constructor
      · intro h
        have hwK : w ∈ K := by
          have := K.mul_mem h (K.inv_mem hm)
          rwa [mul_assoc, mul_inv_cancel, mul_one] at this
        have : w ∈ V ⊓ K := ⟨hw, hwK⟩
        rw [hVKbot] at this
        exact this
      · rintro rfl; simpa using hm
    have hv'le : v' ∈ Subgroup.center C := zpowers_le.2 (selfC_mem_center x) hv'
    have hprod : (v * k) * (v' * k') = (v * v') * (k * k') := by
      calc (v * k) * (v' * k') = v * (k * v') * k' := by group
        _ = v * (v' * k) * k' := by rw [Subgroup.mem_center_iff.1 hv'le k]
        _ = (v * v') * (k * k') := by group
    rw [hprod, hgen (v * v') (V.mul_mem hv hv') (k * k') (K.mul_mem hk hk'),
      hgen v hv k hk, hgen v' hv' k' hk']
    constructor
    · intro h
      exact ⟨fun hv1 => by rw [hv1, one_mul] at h; exact h,
        fun hv'1 => by rw [hv'1, mul_one] at h; exact h⟩
    · intro h
      rcases (mem_zpowers_iff_eq_one_or_of_mul_self (selfC_mul_self hx2) v).1 hv with hv1 | hv1
      · rw [hv1, h.mp hv1, mul_one]
      · have hv'1 : v' = selfC x := by
          rcases (mem_zpowers_iff_eq_one_or_of_mul_self (selfC_mul_self hx2) v').1 hv' with h' | h'
          · exact absurd (h.mpr h') (by rw [hv1]; exact selfC_ne_one hx1)
          · exact h'
        rw [hv1, hv'1]
        exact selfC_mul_self hx2
  let κ₀ : C →* ℤˣ := MonoidHom.mk' (fun c : C => if c ∈ K then 1 else -1) (by
    intro c d
    by_cases hc : c ∈ K <;> by_cases hd : d ∈ K
    · rw [if_pos ((hiff c d).2 (iff_of_true hc hd)), if_pos hc, if_pos hd, mul_one]
    · rw [if_neg (fun h => hd (((hiff c d).1 h).mp hc)), if_pos hc, if_neg hd]
      simp
    · rw [if_neg (fun h => hc (((hiff c d).1 h).mpr hd)), if_neg hc, if_pos hd]
      simp
    · rw [if_pos ((hiff c d).2 (iff_of_false hc hd)), if_neg hc, if_neg hd]
      norm_num)
  have hself_notK : selfC x ∉ K := by
    intro h
    have : selfC x ∈ V ⊓ K := ⟨Subgroup.mem_zpowers (selfC x), h⟩
    rw [hVKbot] at this
    exact selfC_ne_one hx1 this
  have hκ₀self : κ₀ (selfC x) = -1 := by
    change (if selfC x ∈ K then (1 : ℤˣ) else -1) = -1
    rw [if_neg hself_notK]
  let zC : C := ⟨z, hzx⟩
  by_cases hz1 : κ₀ zC = 1
  · refine ⟨κ₀, ?_, ?_⟩
    · exact hκ₀self
    · intro hz
      rw [show (⟨z, hz⟩ : C) = zC from Subtype.ext rfl]
      exact hz1
  · have hz1' : κ₀ zC = -1 := by
      rcases Int.units_eq_one_or (κ₀ zC) with h | h
      · exact absurd h hz1
      · exact h
    refine ⟨κ₀ * (Equiv.Perm.sign.comp π), ?_, ?_⟩
    · change (κ₀ * (Equiv.Perm.sign.comp π)) (selfC x) = -1
      rw [MonoidHom.mul_apply, MonoidHom.comp_apply]
      have hπx : π (selfC x) = 1 := (hOS.sec.ker (selfC x)).2 (Or.inr rfl)
      rw [hπx, map_one, hκ₀self, mul_one]
    · intro hz
      rw [show (⟨z, hz⟩ : C) = zC from Subtype.ext rfl, MonoidHom.mul_apply,
        MonoidHom.comp_apply]
      have hπz : π zC = τ₀ := hOS.swap hzx
      rw [hπz, show Equiv.Perm.sign τ₀ = -1 from Equiv.Perm.sign_swap (by decide), hz1']
      norm_num

end CFSG.OddStandard.AltStdSec.SwapPattern
