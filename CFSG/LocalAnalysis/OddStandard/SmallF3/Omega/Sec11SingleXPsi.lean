module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11SingleXRho

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

namespace S11sCtx

variable {G : Type} [Group G] [Finite G] {t z : G} {K1 K2 T R : Subgroup G}
  {ρ : ↥R →* MulAut ↥(K1 ⊔ K2)} {a x : G} (c : S11sCtx t z K1 K2 T R ρ a x)

include c

theorem psi_sq {s : G} (hsR : s ∈ R) (hs2 : s * s = 1) : ρ ⟨s, hsR⟩ * ρ ⟨s, hsR⟩ = 1 := by
  rw [← map_mul]
  have h : (⟨s, hsR⟩ : ↥R) * ⟨s, hsR⟩ = 1 := by
    ext
    simpa using hs2
  rw [h, map_one]

theorem psi_keepA {s b : G} (hsR : s ∈ R)
    (hQ1 : ∀ q ∈ twoCoreIn K1, s * q * s⁻¹ ∈ twoCoreIn K1) (hb : b ∈ twoCoreIn K1)
    (hsb : s * b * s⁻¹ * b⁻¹ ∉ zpowers z) :
    ∀ y ∈ K1.subgroupOf (K1 ⊔ K2), ρ ⟨s, hsR⟩ y ∈ K1.subgroupOf (K1 ⊔ K2) := by
  rcases c.pair.s11s_block_A (ρ ⟨s, hsR⟩) with h | h
  · exact h
  · exfalso
    let b' : ↥(K1 ⊔ K2) := ⟨b, mem_sup_left (twoCoreIn_le_self K1 hb)⟩
    have hb'A : b' ∈ K1.subgroupOf (K1 ⊔ K2) := twoCoreIn_le_self K1 hb
    have hpsiB : ρ ⟨s, hsR⟩ b' ∈ K2.subgroupOf (K1 ⊔ K2) := h b' hb'A
    have hpsiA : ρ ⟨s, hsR⟩ b' ∈ K1.subgroupOf (K1 ⊔ K2) := by
      show ((ρ ⟨s, hsR⟩ b' : ↥(K1 ⊔ K2)) : G) ∈ K1
      rw [c.rho_Q ⟨s, hsR⟩ b' (c.Q1_le_Q hb)]
      exact twoCoreIn_le_self K1 (hQ1 b hb)
    have hsq : ρ ⟨s, hsR⟩ b' * ρ ⟨s, hsR⟩ b' = 1 := c.pair.inf_sq ⟨hpsiA, hpsiB⟩
    have hb'sq : b' * b' = 1 := by
      apply (ρ ⟨s, hsR⟩).injective
      rw [map_mul, hsq, map_one]
    have hbsq : b * b = 1 := by
      have := congrArg (fun k : ↥(K1 ⊔ K2) => (k : G)) hb'sq
      simpa using this
    have hbz : b ∈ zpowers z := c.q8.invol1 b hb hbsq
    have hsz : s * z = z * s := Subgroup.mem_centralizer_singleton_iff.mp (c.R_H hsR)
    have hcomm : s * b = b * s := by
      have hzmem : z ∈ Subgroup.centralizer ({s} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hsz.symm
      exact (Subgroup.mem_centralizer_singleton_iff.mp
        (Subgroup.zpowers_le.mpr hzmem hbz)).symm
    have hone : s * b * s⁻¹ * b⁻¹ = 1 := by
      rw [hcomm]
      group
    exact hsb (by rw [hone]; exact Subgroup.one_mem (zpowers z))

theorem psi_keepB {s : G} (hsR : s ∈ R)
    (hQ2 : ∀ q ∈ twoCoreIn K2, s * q * s⁻¹ ∈ twoCoreIn K2) :
    ∀ y ∈ K2.subgroupOf (K1 ⊔ K2), ρ ⟨s, hsR⟩ y ∈ K2.subgroupOf (K1 ⊔ K2) := by
  have hb2 : ∃ b2 ∈ twoCoreIn K2, b2 ∉ zpowers z := by
    by_contra h
    push_neg at h
    have hcard : Nat.card (twoCoreIn K2) ≤ Nat.card (zpowers z) := Subgroup.card_le_of_le h
    rw [c.q8.card2, Nat.card_zpowers] at hcard
    have hord : orderOf z ≤ 2 :=
      orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact c.q8.z_sq)
    omega
  obtain ⟨b2, hb2mem, hb2z⟩ := hb2
  rcases c.pair.s11s_block_B (ρ ⟨s, hsR⟩) with h | h
  · exact h
  · exfalso
    let b2' : ↥(K1 ⊔ K2) := ⟨b2, mem_sup_right (twoCoreIn_le_self K2 hb2mem)⟩
    have hb2'B : b2' ∈ K2.subgroupOf (K1 ⊔ K2) := twoCoreIn_le_self K2 hb2mem
    have hpsiA : ρ ⟨s, hsR⟩ b2' ∈ K1.subgroupOf (K1 ⊔ K2) := h b2' hb2'B
    have hpsiB : ρ ⟨s, hsR⟩ b2' ∈ K2.subgroupOf (K1 ⊔ K2) := by
      show ((ρ ⟨s, hsR⟩ b2' : ↥(K1 ⊔ K2)) : G) ∈ K2
      rw [c.rho_Q ⟨s, hsR⟩ b2' (c.Q2_le_Q hb2mem)]
      exact twoCoreIn_le_self K2 (hQ2 b2 hb2mem)
    have hsq : ρ ⟨s, hsR⟩ b2' * ρ ⟨s, hsR⟩ b2' = 1 := c.pair.inf_sq ⟨hpsiA, hpsiB⟩
    have hb2'sq : b2' * b2' = 1 := by
      apply (ρ ⟨s, hsR⟩).injective
      rw [map_mul, hsq, map_one]
    have hb2sq : b2 * b2 = 1 := by
      have := congrArg (fun k : ↥(K1 ⊔ K2) => (k : G)) hb2'sq
      simpa using this
    exact hb2z (c.q8.invol2 b2 hb2mem hb2sq)

theorem psi_triv {s : G} (hsR : s ∈ R) (h2 : ActsTrivModZ z s (twoCoreIn K2)) :
    ∀ q : SL23, q ^ 4 = 1 →
      ρ ⟨s, hsR⟩ (c.pair.embB q) * (c.pair.embB q)⁻¹ ∈
        K1.subgroupOf (K1 ⊔ K2) ⊓ K2.subgroupOf (K1 ⊔ K2) := by
  intro q hq
  have hg : ((c.pair.embB q : ↥(K1 ⊔ K2)) : G) ∈ twoCoreIn K2 := c.embB_mem_Q2 hq
  have hz : s * ((c.pair.embB q : ↥(K1 ⊔ K2)) : G) * s⁻¹ *
      (((c.pair.embB q : ↥(K1 ⊔ K2)) : G))⁻¹ ∈ zpowers z := h2 _ hg
  refine ⟨?_, ?_⟩
  · show ((ρ ⟨s, hsR⟩ (c.pair.embB q) * (c.pair.embB q)⁻¹ : ↥(K1 ⊔ K2)) : G) ∈ K1
    rw [Subgroup.coe_mul, Subgroup.coe_inv,
      c.rho_Q ⟨s, hsR⟩ (c.pair.embB q) (c.Q2_le_Q hg)]
    exact Subgroup.zpowers_le.mpr c.z_K1 hz
  · show ((ρ ⟨s, hsR⟩ (c.pair.embB q) * (c.pair.embB q)⁻¹ : ↥(K1 ⊔ K2)) : G) ∈ K2
    rw [Subgroup.coe_mul, Subgroup.coe_inv,
      c.rho_Q ⟨s, hsR⟩ (c.pair.embB q) (c.Q2_le_Q hg)]
    exact Subgroup.zpowers_le.mpr c.z_K2 hz

theorem psi_not {s b : G} (hsR : s ∈ R) (hb : b ∈ twoCoreIn K1)
    (hsb : s * b * s⁻¹ * b⁻¹ ∉ zpowers z) :
    ¬ ∃ q : SL23, q ^ 4 = 1 ∧ ∀ y ∈ K1.subgroupOf (K1 ⊔ K2),
      ρ ⟨s, hsR⟩ y = c.pair.embA q * y * (c.pair.embA q)⁻¹ := by
  rintro ⟨q, hq, hψ⟩
  let b' : ↥(K1 ⊔ K2) := ⟨b, mem_sup_left (twoCoreIn_le_self K1 hb)⟩
  have hb' : b' ∈ K1.subgroupOf (K1 ⊔ K2) := twoCoreIn_le_self K1 hb
  have hconj : ρ ⟨s, hsR⟩ b' = c.pair.embA q * b' * (c.pair.embA q)⁻¹ := hψ b' hb'
  have hcoe : s * b * s⁻¹ = ((c.pair.embA q : ↥(K1 ⊔ K2)) : G) * b *
      (((c.pair.embA q : ↥(K1 ⊔ K2)) : G))⁻¹ := by
    have h := congrArg (fun k : ↥(K1 ⊔ K2) => (k : G)) hconj
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [c.rho_Q ⟨s, hsR⟩ b' (c.Q1_le_Q hb)] at h
    simpa using h
  have hg : ((c.pair.embA q : ↥(K1 ⊔ K2)) : G) ∈ twoCoreIn K1 := c.embA_mem_Q1 hq
  have hmem : ((c.pair.embA q : ↥(K1 ⊔ K2)) : G) * b *
      (((c.pair.embA q : ↥(K1 ⊔ K2)) : G))⁻¹ * b⁻¹ ∈ zpowers z :=
    (c.q8.elem1 ((c.pair.embA q : ↥(K1 ⊔ K2)) : G) hg b hb).1
  exact hsb (hcoe.symm ▸ hmem)

theorem psi_class {s b : G} (hsR : s ∈ R) (hs2 : s * s = 1)
    (hQ1 : ∀ q ∈ twoCoreIn K1, s * q * s⁻¹ ∈ twoCoreIn K1)
    (hQ2 : ∀ q ∈ twoCoreIn K2, s * q * s⁻¹ ∈ twoCoreIn K2)
    (h2 : ActsTrivModZ z s (twoCoreIn K2)) (hb : b ∈ twoCoreIn K1)
    (hsb : s * b * s⁻¹ * b⁻¹ ∉ zpowers z) :
    (∀ y ∈ K1.subgroupOf (K1 ⊔ K2), ρ ⟨s, hsR⟩ y ∈ K1.subgroupOf (K1 ⊔ K2)) ∧
      Equiv.Perm.sign (c.pair.theta (ρ ⟨s, hsR⟩)) = -1 ∧
      ∃ q : SL23, q ^ 4 = 1 ∧ ∀ y ∈ K2.subgroupOf (K1 ⊔ K2),
        ρ ⟨s, hsR⟩ y = c.pair.embB q * y * (c.pair.embB q)⁻¹ := by
  have hA := c.psi_keepA hsR hQ1 hb hsb
  obtain ⟨hsign, hq⟩ := c.pair.s11s_psi_class (c.psi_sq hsR hs2) hA (c.psi_keepB hsR hQ2)
    (c.psi_triv hsR h2) (c.psi_not hsR hb hsb)
  exact ⟨hA, hsign, hq⟩

end S11sCtx

end CFSG.OddStandard.SmallF3.Omega
