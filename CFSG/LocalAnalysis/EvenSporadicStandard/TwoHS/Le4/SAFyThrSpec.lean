module

public import CFSG.RankThree.Native.HSMcLSmall
public import Certificates.Certificate26792

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.RankThree.Native

section Cent


theorem fyThr_parts : fyThrCentOK = true ∧ fyThrFuseOK = true := by
  have h : fyThrOK = true := Certificates.certificate26792
  simpa only [fyThrOK, Bool.and_eq_true] using h

theorem fyThr_card_cent :
    Nat.card ↥(Subgroup.centralizer ({permOfArr 100 fyThrX} : Set (Equiv.Perm (Fin 100))) ⊓
      hs100P) ≤ 360 := by
  have hc := fyThr_parts.1
  simp only [fyThrCentOK, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hv, h0⟩, hfix⟩, hlen⟩, htail⟩ := hc
  have hx : Rep 100 fyThrX (permOfArr 100 fyThrX) := rep_of_validA hv
  have hA := hs100ChainArrays
  have hF := chainCheckFacts hs100_chain_check.1
  have hQ := hs100Chain_valid
  have hbc : hs100Chain.baseCount = 5 := by
    rw [← hA.base_size]
    rfl
  have hi0 : 0 < hs100Chain.baseCount := by omega
  have hb0 : ((hs100Chain.base.get ⟨0, hi0⟩ : Fin 100) : ℕ) = 0 := by
    rw [hA.base_val]
    rfl
  have hfix0 : permOfArr 100 fyThrX (hs100Chain.base.get ⟨0, hi0⟩) =
      hs100Chain.base.get ⟨0, hi0⟩ := by
    apply Fin.ext
    rw [← hx, hb0, h0]
  have h1 := card_centralizer_inf_levelSubgroup_le hA hF hQ hx hi0 hfix0
  have h2 := card_centralizer_inf_levelSubgroup_le_of_tailOK hA hF hQ hx (m := 1) (by omega)
    (E := fyThrE) (by
      rw [hbc]
      exact htail)
  rw [hs100P_eq_original, ← hs100Chain.levelSubgroup_zero_eq_original hQ]
  have hcount : fixLevCount 100 (rawLevels 100 hs100StrongArrs hs100BaseArr) fyThrX 0 = 10 := hfix
  rw [hcount] at h1
  calc _ ≤ 10 * Nat.card ↥(Subgroup.centralizer ({permOfArr 100 fyThrX} :
        Set (Equiv.Perm (Fin 100))) ⊓ hs100Chain.levelSubgroup (0 + 1)) := h1
    _ ≤ 10 * 36 := Nat.mul_le_mul_left _ (h2.trans hlen.le)

theorem fyThr_fuse_spec :
    ∃ Q : Subgroup (Equiv.Perm (Fin 100)), Q ≤ hs100P ∧ Nat.card Q = 9 ∧
      ∀ z ∈ Q, z ≠ 1 → ∃ g ∈ hs100P, g * permOfArr 100 fyThrX * g⁻¹ = z := by
  have hf := fyThr_parts.2
  simp only [fyThrFuseOK, Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨⟨henum, hsize⟩, hsift⟩, hall⟩ := hf
  have hps : ∀ p ∈ fyThrKeys, p < 100 := by
    intro p hp
    simp only [fyThrKeys, List.mem_cons, List.not_mem_nil, or_false] at hp
    omega
  have hA := hs100ChainArrays
  have hc := hs100_chain_check.1
  have hmemP : ∀ {g : Array ℕ}, validA 100 g = true →
      siftA 100 fyThrLevels hs100BaseArr 0 g = true → permOfArr 100 g ∈ hs100P := by
    intro g hv hs
    rw [hs100P_eq_original]
    exact (siftA_iff_mem_originalSubgroup hA (by norm_num) hc (rep_of_validA hv)).1 hs
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec hps henum
  have hx : Rep 100 fyThrX (permOfArr 100 fyThrX) := by
    have hv : validA 100 fyThrX = true := by
      have := fyThr_parts.1
      simp only [fyThrCentOK, Bool.and_eq_true] at this
      exact this.1.1.1.1
    exact rep_of_validA hv
  refine ⟨Subgroup.closure (permsA 100 fyThrQGens), ?_, hcard.trans hsize, ?_⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hmemP (enumOK_gens_valid henum hk) (allLt_spec hsift hk)
  · intro z hz hz1
    obtain ⟨i, hi, rfl⟩ := (hmem z).1 hz
    have hrep := rep_of_validA (hval i hi)
    have hmemL : fyThrQCert.pts[i]! ∈ fyThrQCert.pts.toList := by
      rw [getElem!_pos _ i hi]
      exact Array.mem_toList_iff.2 (Array.getElem_mem hi)
    have h1 := List.all_eq_true.1 hall _ hmemL
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h1
    rcases h1 with h1 | ⟨g, hg, ⟨hgv, hgs⟩, hge⟩
    · exact absurd ((eqA_iff hrep rep_idA).1 h1) hz1
    · refine ⟨permOfArr 100 g, hmemP hgv hgs, ?_⟩
      have hgr := rep_of_validA hgv
      have e := (eqA_iff (rep_compA hgr hx) (rep_compA hrep hgr)).1 hge
      rw [e, mul_inv_cancel_right]

end Cent

section Sylow

theorem exists_conj_mem_of_sylow {M : Type*} [Group M] [Finite M] {P Q : Subgroup M}
    (hQP : Q ≤ P) {p : ℕ} [hp : Fact p.Prime]
    (hQ : Nat.card Q = p ^ (Nat.card P).factorization p) {a : M} (ha : a ∈ P)
    (hap : orderOf a = p) : ∃ g ∈ P, g⁻¹ * a * g ∈ Q := by
  have hQ' : Nat.card (Q.subgroupOf P) = p ^ (Nat.card P).factorization p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hQP).toEquiv, hQ]
  let S₀ : Sylow p P := Sylow.ofCard (Q.subgroupOf P) hQ'
  have hS₀ : (S₀ : Subgroup P) = Q.subgroupOf P := Sylow.coe_ofCard _ _
  have hpgrp : IsPGroup p (zpowers (⟨a, ha⟩ : P)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hap, pow_one])
  obtain ⟨S, hS⟩ := hpgrp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P S₀ S
  have haS : (⟨a, ha⟩ : P) ∈ (S : Subgroup P) := hS (Subgroup.mem_zpowers _)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at haS
  rw [hS₀, Subgroup.mem_subgroupOf] at haS
  refine ⟨(g : M), g.2, ?_⟩
  simpa [MulAut.smul_def, ← map_inv, MulAut.conj_apply, mul_assoc] using haS

end Sylow

section Three


theorem card_hs100P_factorization : (Nat.card hs100P).factorization 3 = 2 := by
  rw [card_hs100P, show (44352000 : ℕ) = 3 ^ 2 * 4928000 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Nat.factorization_eq_zero_of_not_dvd
      (by norm_num)]
  simp

theorem fyThr_fusion {a : Equiv.Perm (Fin 100)} (ha : a ∈ hs100P) (ha3 : orderOf a = 3) :
    ∃ g ∈ hs100P, g * permOfArr 100 fyThrX * g⁻¹ = a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQP, hQ9, hQz⟩ := fyThr_fuse_spec
  obtain ⟨h, hh, hhQ⟩ := exists_conj_mem_of_sylow hQP (p := 3)
    (by rw [hQ9, card_hs100P_factorization]; norm_num) ha ha3
  have hne : h⁻¹ * a * h ≠ 1 := by
    intro h1
    have : a = 1 := by
      calc a = h * (h⁻¹ * a * h) * h⁻¹ := by group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at ha3
    omega
  obtain ⟨g, hg, hgz⟩ := hQz _ hhQ hne
  refine ⟨h * g, hs100P.mul_mem hh hg, ?_⟩
  calc h * g * permOfArr 100 fyThrX * (h * g)⁻¹
      = h * (g * permOfArr 100 fyThrX * g⁻¹) * h⁻¹ := by group
    _ = a := by rw [hgz]; group

theorem hs100_order_three :
    (∀ a ∈ hs100P, ∀ b ∈ hs100P, orderOf a = 3 → orderOf b = 3 →
      ∃ g ∈ hs100P, g * a * g⁻¹ = b) ∧
    (∀ a ∈ hs100P, orderOf a = 3 →
      Nat.card ↥(Subgroup.centralizer ({a} : Set (Equiv.Perm (Fin 100))) ⊓ hs100P) ≤ 360) := by
  constructor
  · intro a ha b hb ha3 hb3
    obtain ⟨g, hg, hga⟩ := fyThr_fusion ha ha3
    obtain ⟨g', hg', hgb⟩ := fyThr_fusion hb hb3
    refine ⟨g' * g⁻¹, hs100P.mul_mem hg' (hs100P.inv_mem hg), ?_⟩
    rw [← hgb, ← hga]
    group
  · intro a ha ha3
    obtain ⟨g, hg, hga⟩ := fyThr_fusion ha ha3
    rw [← card_centralizer_inf_conj hs100P hg hga]
    exact fyThr_card_cent

end Three

end CFSG.EvenSporadicStandard.TwoHS
