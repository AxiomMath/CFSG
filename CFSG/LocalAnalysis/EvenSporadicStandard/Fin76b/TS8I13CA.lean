module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13Case
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8E614Def
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13R

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

theorem relIndex_ker_dvd_two {Γ : Type*} [Group Γ] (φ : Γ →* ℤˣ) (K : Subgroup Γ) :
    φ.ker.relIndex K ∣ 2 := by
  rw [Subgroup.relIndex_dvd_two_iff]
  by_cases hK : K ≤ φ.ker
  · exact ⟨1, K.one_mem, fun b hb => Or.inr (hK hb)⟩
  · obtain ⟨a, haK, ha⟩ := SetLike.not_le_iff_exists.1 hK
    have ha' : φ a = -1 :=
      (Int.units_eq_one_or (φ a)).resolve_left (fun h => ha (MonoidHom.mem_ker.2 h))
    refine ⟨a, haK, fun b hb => ?_⟩
    rcases Int.units_eq_one_or (φ b) with hb1 | hb1
    · exact Or.inr (MonoidHom.mem_ker.2 hb1)
    · refine Or.inl (MonoidHom.mem_ker.2 ?_)
      rw [map_mul, hb1, ha']
      decide

@[expose] noncomputable def signProd {G : Type*} [Group G] {E : Subgroup G}
    (π : MulAut ↥E →* Equiv.Perm (Fin 5)) : MulAut ↥E × MulAut ↥E →* ℤˣ :=
  MonoidHom.mk' (fun x => Equiv.Perm.sign (π x.1) * Equiv.Perm.sign (π x.2)) fun x y => by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    exact mul_mul_mul_comm _ _ _ _

@[expose] noncomputable def fstSign {G : Type*} [Group G] {E : Subgroup G}
    (π : MulAut ↥E →* Equiv.Perm (Fin 5)) : MulAut ↥E × MulAut ↥E →* ℤˣ :=
  (Equiv.Perm.sign.comp π).comp (MonoidHom.fst _ _)

@[expose] def altE {G : Type*} [Group G] {E : Subgroup G}
    (π : MulAut ↥E →* Equiv.Perm (Fin 5)) : Subgroup (MulAut ↥E) :=
  (alternatingGroup (Fin 5)).comap π

theorem mem_altE {G : Type*} [Group G] {E : Subgroup G} {π : MulAut ↥E →* Equiv.Perm (Fin 5)}
    {a : MulAut ↥E} : a ∈ altE π ↔ Equiv.Perm.sign (π a) = 1 := by
  rw [altE, Subgroup.mem_comap, Equiv.Perm.mem_alternatingGroup]

theorem units_mul_eq_one_of_ne {u v : ℤˣ} (hu : u ≠ 1) (hv : v ≠ 1) : u * v = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl
  · exact absurd rfl hu
  · exact absurd rfl hu
  · exact absurd rfl hv
  · decide

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ)

theorem mem_range_iff {π : MulAut ↥E →* Equiv.Perm (Fin 5)}
    (hA : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔ Equiv.Perm.sign (π a) = Equiv.Perm.sign (π b))
    (x : MulAut ↥E × MulAut ↥E) :
    x ∈ c.rho.range ↔ Equiv.Perm.sign (π x.1) = Equiv.Perm.sign (π x.2) := by
  have h := hA x.1 x.2
  rwa [Prod.mk.eta] at h

theorem range_eq_ker {π : MulAut ↥E →* Equiv.Perm (Fin 5)}
    (hA : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔ Equiv.Perm.sign (π a) = Equiv.Perm.sign (π b)) :
    c.rho.range = (signProd π).ker := by
  ext x
  rw [MonoidHom.mem_ker, mem_range_iff c hA]
  change _ ↔ Equiv.Perm.sign (π x.1) * Equiv.Perm.sign (π x.2) = 1
  constructor
  · intro e
    rw [e, Int.units_mul_self]
  · intro e
    rw [mul_eq_one_iff_eq_inv, Int.units_inv_eq_self] at e
    exact e

theorem hbigA {π : MulAut ↥E →* Equiv.Perm (Fin 5)}
    (hA : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔ Equiv.Perm.sign (π a) = Equiv.Perm.sign (π b))
    (hE : EFacts614 E t) :
    ∀ ψ : ↥c.rho.range, ψ * ψ = 1 →
      2 ^ 9 ∣ Nat.card ↥(Subgroup.centralizer ({ψ} : Set ↥c.rho.range)) := by
  intro ψ hψ
  have hψ0 : ψ.1 * ψ.1 = 1 := congrArg Subtype.val hψ
  have ha : ψ.1.1 * ψ.1.1 = 1 := congrArg Prod.fst hψ0
  have hb : ψ.1.2 * ψ.1.2 = 1 := congrArg Prod.snd hψ0
  have hmap : (Subgroup.centralizer ({ψ} : Set ↥c.rho.range)).map c.rho.range.subtype =
      c.rho.range ⊓ Subgroup.centralizer ({ψ.1} : Set (MulAut ↥E × MulAut ↥E)) := by
    ext x
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨γ.2, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hγ))⟩
    · rintro ⟨hx, hxD⟩
      exact ⟨⟨x, hx⟩, mem_centralizer_singleton_iff.2
        (Subtype.ext (mem_centralizer_singleton_iff.1 hxD)), rfl⟩
  have hcardH : Nat.card ↥(Subgroup.centralizer ({ψ} : Set ↥c.rho.range)) =
      Nat.card ↥(c.rho.range ⊓ Subgroup.centralizer ({ψ.1} : Set (MulAut ↥E × MulAut ↥E))) := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective Subtype.val_injective).symm
  have hprod : Subgroup.centralizer ({ψ.1} : Set (MulAut ↥E × MulAut ↥E)) =
      (Subgroup.centralizer ({ψ.1.1} : Set (MulAut ↥E))).prod
        (Subgroup.centralizer ({ψ.1.2} : Set (MulAut ↥E))) := by
    ext x
    simp only [mem_centralizer_singleton_iff, Subgroup.mem_prod, Prod.ext_iff, Prod.fst_mul,
      Prod.snd_mul]
  have hCard : 2 ^ 10 ∣
      Nat.card ↥(Subgroup.centralizer ({ψ.1} : Set (MulAut ↥E × MulAut ↥E))) := by
    rw [hprod, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
      (show (2 : ℕ) ^ 10 = 32 * 32 by norm_num)]
    exact Nat.mul_dvd_mul (hE.cent_dvd ψ.1.1 ha) (hE.cent_dvd ψ.1.2 hb)
  have hdvd : c.rho.range.relIndex
      (Subgroup.centralizer ({ψ.1} : Set (MulAut ↥E × MulAut ↥E))) ∣ 2 := by
    have h := relIndex_ker_dvd_two (signProd π)
      (Subgroup.centralizer ({ψ.1} : Set (MulAut ↥E × MulAut ↥E)))
    rw [← range_eq_ker c hA] at h
    exact h
  have hmain := relIndex_mul_card (H := c.rho.range)
    (K := Subgroup.centralizer ({ψ.1} : Set (MulAut ↥E × MulAut ↥E)))
  rw [hcardH]
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · rw [h, one_mul] at hmain
    rw [← hmain] at hCard
    exact dvd_trans (pow_dvd_pow 2 (by norm_num)) hCard
  · rw [h] at hmain
    rw [← hmain] at hCard
    rw [(show (2 : ℕ) ^ 10 = 2 * 2 ^ 9 by norm_num)] at hCard
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hCard

variable {c}

theorem IsRs.exists_prod_eq {Rs : Subgroup G} (hR : c.IsRs Rs)
    {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π)
    (hA : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔ Equiv.Perm.sign (π a) = Equiv.Perm.sign (π b)) :
    ∃ S₁ S₂ : Subgroup (MulAut ↥E),
      c.Rhat (Rs ⊓ c.N1) ⊓ (altE π).prod (altE π) = S₁.prod S₂ := by
  have hfst : ∀ x : MulAut ↥E × MulAut ↥E, fstSign π x = Equiv.Perm.sign (π x.1) :=
    fun x => rfl
  have hAPmem : ∀ x : MulAut ↥E × MulAut ↥E, x ∈ (altE π).prod (altE π) ↔
      x ∈ c.rho.range ∧ fstSign π x = 1 := by
    intro x
    rw [mem_range_iff c hA, Subgroup.mem_prod, mem_altE, mem_altE, hfst]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1.trans h2.symm, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1.symm.trans h2⟩
  have hAPΓ : (altE π).prod (altE π) ≤ c.rho.range := fun x hx => ((hAPmem x).1 hx).1
  have hRhΓ : c.Rhat (Rs ⊓ c.N1) ≤ c.rho.range := c.Rhat_le_range _
  have eAP : (altE π).prod (altE π) = (fstSign π).ker ⊓ c.rho.range := by
    ext x
    rw [hAPmem, mem_inf, MonoidHom.mem_ker]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have eRh : c.Rhat (Rs ⊓ c.N1) ⊓ (altE π).prod (altE π) =
      (fstSign π).ker ⊓ c.Rhat (Rs ⊓ c.N1) := by
    ext x
    rw [mem_inf, mem_inf, hAPmem, MonoidHom.mem_ker]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h3, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, hRhΓ h2, h1⟩
  have hAP2 : ((altE π).prod (altE π)).relIndex c.rho.range = 2 := by
    have hd : ((altE π).prod (altE π)).relIndex c.rho.range ∣ 2 := by
      rw [eAP, inf_relIndex_right]
      exact relIndex_ker_dvd_two _ _
    have hne : ((altE π).prod (altE π)).relIndex c.rho.range ≠ 1 := by
      rw [Ne, relIndex_eq_one]
      intro hle
      obtain ⟨τ, hτ⟩ := hπ.surj (Equiv.swap (0 : Fin 5) 1)
      have hmem : (τ, τ) ∈ c.rho.range := (hA τ τ).2 rfl
      have h2 := (hAPmem (τ, τ)).1 (hle hmem)
      have h3 : Equiv.Perm.sign (π τ) = 1 := h2.2
      rw [hτ, Equiv.Perm.sign_swap (by decide)] at h3
      exact absurd h3 (by decide)
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact absurd h hne
    · exact h
  have hRodd : ¬ 2 ∣ (c.Rhat (Rs ⊓ c.N1)).relIndex c.rho.range := fun hd =>
    hR.R_odd (dvd_trans hd (c.Rhat_relIndex_dvd _))
  have hHR : (c.Rhat (Rs ⊓ c.N1) ⊓ (altE π).prod (altE π)).relIndex (c.Rhat (Rs ⊓ c.N1)) ∣ 2 := by
    rw [eRh, inf_relIndex_right]
    exact relIndex_ker_dvd_two _ _
  have hodd : ¬ 2 ∣ (c.Rhat (Rs ⊓ c.N1) ⊓ (altE π).prod (altE π)).relIndex
      ((altE π).prod (altE π)) := by
    have h1 := relIndex_mul_relIndex (c.Rhat (Rs ⊓ c.N1) ⊓ (altE π).prod (altE π))
      ((altE π).prod (altE π)) c.rho.range inf_le_right hAPΓ
    have h2 := relIndex_mul_relIndex (c.Rhat (Rs ⊓ c.N1) ⊓ (altE π).prod (altE π))
      (c.Rhat (Rs ⊓ c.N1)) c.rho.range inf_le_left hRhΓ
    rw [hAP2] at h1
    rcases (Nat.dvd_prime Nat.prime_two).1 hHR with h | h
    · rw [h] at h2
      omega
    · rw [h] at h2
      omega
  have hH : IsPGroup 2 (c.Rhat (Rs ⊓ c.N1) ⊓ (altE π).prod (altE π) :
      Subgroup (MulAut ↥E × MulAut ↥E)) :=
    (c.Rhat_pgroup hR.R_pgroup).to_le inf_le_left
  have hmax := max_of_odd_relIndex hH hodd
  obtain ⟨heq, -⟩ := eq_prod_of_max (Θ₁ := altE π) (Θ₂ := altE π) hH inf_le_right hmax
  exact ⟨_, _, heq⟩

theorem IsRs.Rhat_mem_even {Rs : Subgroup G} (hR : c.IsRs Rs)
    {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π)
    (hA : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔ Equiv.Perm.sign (π a) = Equiv.Perm.sign (π b))
    {a : MulAut ↥E} (ha : (a, a⁻¹) ∈ c.Rhat (Rs ⊓ c.N1))
    (hev : Equiv.Perm.sign (π a) = 1) : (a, 1) ∈ c.Rhat (Rs ⊓ c.N1) := by
  obtain ⟨S₁, S₂, hS⟩ := hR.exists_prod_eq hπ hA
  have hmem : (a, a⁻¹) ∈ c.Rhat (Rs ⊓ c.N1) ⊓ (altE π).prod (altE π) := by
    refine Subgroup.mem_inf.2 ⟨ha, Subgroup.mem_prod.2 ⟨mem_altE.2 hev, mem_altE.2 ?_⟩⟩
    simp [map_inv, hev]
  rw [hS] at hmem
  have h1 : (a, (1 : MulAut ↥E)) ∈ S₁.prod S₂ :=
    Subgroup.mem_prod.2 ⟨(Subgroup.mem_prod.1 hmem).1, S₂.one_mem⟩
  rw [← hS] at h1
  exact (Subgroup.mem_inf.1 h1).1

theorem IsRs.Rhat_mem_odd {Rs : Subgroup G} (hR : c.IsRs Rs) (hTRs : T ≤ Rs)
    {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π)
    (hA : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔ Equiv.Perm.sign (π a) = Equiv.Perm.sign (π b))
    {a : MulAut ↥E} (ha : (a, a⁻¹) ∈ c.Rhat (Rs ⊓ c.N1))
    (hodd : Equiv.Perm.sign (π a) ≠ 1) :
    (a * convN ⟨σ, c.hσ.norm_E⟩, (1 : MulAut ↥E)) ∈ c.Rhat (Rs ⊓ c.N1) := by
  have hsσ : (convN ⟨σ, c.hσ.norm_E⟩, convN ⟨σ, c.hσ.norm_E⟩) ∈ c.Rhat (Rs ⊓ c.N1) :=
    c.mem_Rhat.2 ⟨⟨σ, c.sigma_mem_N1⟩, ⟨hTRs c.hσ.mem_T, c.sigma_mem_N1⟩, c.rho_sigma⟩
  have hprod := mul_mem ha hsσ
  rw [Prod.mk_mul_mk] at hprod
  have hs1 : Equiv.Perm.sign (π (convN ⟨σ, c.hσ.norm_E⟩)) ≠ 1 := by
    have h := c.pi_sigma_odd hπ
    rwa [Equiv.Perm.mem_alternatingGroup] at h
  obtain ⟨S₁, S₂, hS⟩ := hR.exists_prod_eq hπ hA
  have hP : (a * convN ⟨σ, c.hσ.norm_E⟩, a⁻¹ * convN ⟨σ, c.hσ.norm_E⟩) ∈
      c.Rhat (Rs ⊓ c.N1) ⊓ (altE π).prod (altE π) := by
    refine Subgroup.mem_inf.2 ⟨hprod, Subgroup.mem_prod.2 ⟨mem_altE.2 ?_, mem_altE.2 ?_⟩⟩
    · simp only [map_mul]
      exact units_mul_eq_one_of_ne hodd hs1
    · simp only [map_mul, map_inv]
      exact units_mul_eq_one_of_ne (inv_ne_one.2 hodd) hs1
  rw [hS] at hP
  have h1 : (a * convN ⟨σ, c.hσ.norm_E⟩, (1 : MulAut ↥E)) ∈ S₁.prod S₂ :=
    Subgroup.mem_prod.2 ⟨(Subgroup.mem_prod.1 hP).1, S₂.one_mem⟩
  rw [← hS] at h1
  exact (Subgroup.mem_inf.1 h1).1

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
