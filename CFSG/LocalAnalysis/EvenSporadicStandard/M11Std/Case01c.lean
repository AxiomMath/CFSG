module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M11Std.Case01b

public section

namespace CFSG.EvenSporadicStandard.M11Std

open Subgroup

variable {G : Type} [Group G] [Finite G] (H : Setting G)

namespace Setting

theorem relIndex_S {P : Subgroup G} (hcard : Nat.card P = 64) (hSP : H.S ≤ P) :
    H.S.relIndex P = 2 := by
  have hc : Nat.card (H.S.subgroupOf P) = 32 := by
    rw [← H.card_S]; exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSP).toEquiv)
  have := Subgroup.card_mul_index (H.S.subgroupOf P)
  rw [hc, hcard] at this
  show (H.S.subgroupOf P).index = 2
  omega

theorem no_normal_E8 {P : Subgroup G} (hP : IsPGroup 2 P) (hcard : Nat.card P = 64)
    (hSP : H.S ≤ P) {E : Subgroup G} (hEP : E ≤ P) (hEcard : Nat.card E = 8)
    (hsq : ∀ e ∈ E, e * e = 1) (hcomm : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e)
    (hnorm : ∀ p ∈ P, ∀ e ∈ E, p * e * p⁻¹ ∈ E) : False := by
  have hle : H.S ⊓ E ≤ H.W := by
    rintro _ ⟨hnS, hnE⟩
    obtain ⟨m, rfl⟩ := (mem_S H).1 hnS
    by_contra hW
    have hmW : ¬ SMod.inW m := fun h => hW ⟨m, h, rfl⟩
    have hm2 : SMod.mul m m = SMod.one := by
      apply H.psi_injective
      rw [H.psi_mul, H.psi_one]
      exact hsq _ hnE
    obtain ⟨y, hy⟩ := SMod.exists_noncomm m hm2 (fun h => hmW ((SMod.isCentral_iff m).1 h))
    have h1 : H.psi y * H.psi m * (H.psi y)⁻¹ ∈ E := hnorm _ (hSP (H.psi_mem_S y)) _ hnE
    have h2 := hcomm _ hnE _ h1
    rw [H.psi_conj, ← H.psi_mul, ← H.psi_mul] at h2
    exact hy (H.psi_injective h2)
  have h4 : 4 ≤ Nat.card (H.S ⊓ E : Subgroup G) := by
    have hrel : (H.S ⊓ E).relIndex E = H.S.relIndex E := Subgroup.inf_relIndex_right H.S E
    have hfin : H.S.relIndex P ≠ 0 := by rw [H.relIndex_S hcard hSP]; norm_num
    have hle2 : H.S.relIndex E ≤ 2 := by
      have := Subgroup.relIndex_le_of_le_right hEP hfin
      rwa [H.relIndex_S hcard hSP] at this
    have hc := Subgroup.card_mul_index ((H.S ⊓ E).subgroupOf E)
    have hc' : Nat.card ((H.S ⊓ E).subgroupOf E) = Nat.card (H.S ⊓ E : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [hc', hEcard] at hc
    have hidx : ((H.S ⊓ E).subgroupOf E).index ≤ 2 := by
      have : ((H.S ⊓ E).subgroupOf E).index = (H.S ⊓ E).relIndex E := rfl
      rw [this, hrel]; exact hle2
    by_contra hlt
    push Not at hlt
    have : Nat.card (H.S ⊓ E : Subgroup G) * ((H.S ⊓ E).subgroupOf E).index ≤ 3 * 2 :=
      Nat.mul_le_mul (by omega) hidx
    omega
  have hEq : H.S ⊓ E = H.W :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [H.card_W]; exact h4)
  have htE : H.t ∈ E := by
    have : H.t ∈ H.S ⊓ E := hEq ▸ H.t_mem_W
    exact this.2
  have hES : E ≤ H.S := by
    intro e he
    rw [← H.centralizer_inf_eq_S hP hSP]
    refine ⟨mem_centralizer_singleton_iff.2 ?_, hEP he⟩
    exact hcomm _ he _ htE
  have : H.S ⊓ E = E := inf_eq_right.2 hES
  rw [this] at hEq
  rw [hEq, H.card_W] at hEcard
  omega

theorem exists_conj_eq {U P : Subgroup G} (hU : IsPGroup 2 U) (hUidx : ¬ 2 ∣ U.index)
    (hP : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.index) : ∃ c : G, ∀ x, x ∈ U ↔ c * x * c⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G (hU.toSylow hUidx) (hP.toSylow hPidx)
  refine ⟨c, fun x => ?_⟩
  have h : ((c • hU.toSylow hUidx : Sylow 2 G) : Subgroup G) = P := by
    rw [hc]; rfl
  rw [Sylow.coe_subgroup_smul] at h
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨u, hu, hux⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hx
    simp only [MulAut.smul_def, MulAut.conj_apply, mul_left_inj, mul_right_inj] at hux
    exact hux ▸ hu

theorem exists_normal_E8 (h0 : ¬ IsConj H.t (H.a ^ 4)) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hcard : Nat.card P = 64) (hSP : H.S ≤ P) (hPidx : ¬ 2 ∣ P.index) :
    ∃ E : Subgroup G, E ≤ P ∧ Nat.card E = 8 ∧ (∀ e ∈ E, e * e = 1) ∧
      (∀ e ∈ E, ∀ f ∈ E, e * f = f * e) ∧ (∀ p ∈ P, ∀ e ∈ E, p * e * p⁻¹ ∈ E) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyP, hyS, hyN⟩ := H.exists_y hP hcard hSP
  have hyt := H.conj_eq_tz hP hcard hSP hyP hyS
  have h64 := H.sixtyfour_dvd_normalizer h0 hyN hyt
  set N : Subgroup G := Subgroup.normalizer (H.E1 : Set G) with hNdef
  have hE1N : H.E1 ≤ N := Subgroup.le_normalizer
  have hE1p : IsPGroup 2 (H.E1.subgroupOf N) := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE1N).toEquiv, H.card_E1]; norm_num
  have hnormal : (H.E1.subgroupOf N).Normal := ⟨fun e he n => by
    rw [Subgroup.mem_subgroupOf] at he ⊢
    exact (Subgroup.mem_normalizer_iff.1 n.2 e).1 he⟩
  let Q : Sylow 2 N := default
  have hEQ : H.E1.subgroupOf N ≤ Q := hE1p.le_sylow_of_normal Q
  let U : Subgroup G := (Q : Subgroup N).map N.subtype
  have hUN : U ≤ N := by
    rintro _ ⟨q, -, rfl⟩; exact q.2
  have hUp : IsPGroup 2 U := Q.isPGroup'.map N.subtype
  have hUcard : Nat.card U = Nat.card Q :=
    Subgroup.card_map_of_injective N.subtype_injective
  have hGP : Nat.card G = 64 * P.index := by rw [← hcard]; exact (Subgroup.card_mul_index P).symm
  have hQ := Q.card_eq_multiplicity
  have hfacN : 6 ≤ (Nat.card N).factorization 2 := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.card_pos).ne']
    simpa using h64
  have hQ64 : 64 ≤ Nat.card Q := by
    rw [hQ]
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (Nat.card N).factorization 2 := Nat.pow_le_pow_right (by norm_num) hfacN
  obtain ⟨P', hUP'⟩ := hUp.exists_le_sylow
  have hP'card : Nat.card P' = 64 := by
    rw [P'.card_eq_multiplicity]
    have hPs := (hP.toSylow hPidx).card_eq_multiplicity
    simpa [hcard] using hPs.symm
  have hUle : Nat.card U ≤ 64 := by
    rw [← hP'card]; exact Subgroup.card_le_of_le hUP'
  have hU64 : Nat.card U = 64 := by omega
  have hUidx : U.index = P.index := by
    have h1 := Subgroup.card_mul_index U
    rw [hU64] at h1
    omega
  obtain ⟨c, hc⟩ := exists_conj_eq hUp (by rw [hUidx]; exact hPidx) hP hPidx
  have hE1U : ∀ e ∈ H.E1, e ∈ U := fun e he => ⟨⟨e, hE1N he⟩, hEQ (by
    rw [Subgroup.mem_subgroupOf]; exact he), rfl⟩
  refine ⟨H.E1.map (cj c), ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    exact (hc e).1 (hE1U e he)
  · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, H.card_E1]
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨m, hm, rfl⟩ := he
    rw [cj_apply]
    calc c * H.psi m * c⁻¹ * (c * H.psi m * c⁻¹) = c * (H.psi m * H.psi m) * c⁻¹ := by group
      _ = 1 := by rw [← H.psi_mul, SMod.inE1_sq m hm, H.psi_one]; group
  · rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩
    obtain ⟨m, hm, rfl⟩ := he
    obtain ⟨m', hm', rfl⟩ := hf
    rw [cj_apply, cj_apply]
    calc c * H.psi m * c⁻¹ * (c * H.psi m' * c⁻¹) = c * (H.psi m * H.psi m') * c⁻¹ := by group
      _ = c * (H.psi m' * H.psi m) * c⁻¹ := by
          rw [← H.psi_mul, ← H.psi_mul, SMod.inE1_comm m m' hm hm']
      _ = c * H.psi m' * c⁻¹ * (c * H.psi m * c⁻¹) := by group
  · intro p hp x hx
    obtain ⟨e, he, rfl⟩ := hx
    have hq : c⁻¹ * p * c ∈ U := (hc _).2 (by rwa [show c * (c⁻¹ * p * c) * c⁻¹ = p by group])
    have hqN : c⁻¹ * p * c ∈ Subgroup.normalizer (H.E1 : Set G) := hUN hq
    have := (Subgroup.mem_normalizer_iff.1 hqN e).1 he
    refine ⟨_, this, ?_⟩
    rw [cj_apply, cj_apply]
    group

theorem false_case01 (h0 : ¬ IsConj H.t (H.a ^ 4))
    (hn : Nat.card {x : G // IsConj H.t x} % 4 = 2) : False := by
  obtain ⟨P, hP, hSP, hcard, hidx⟩ := H.exists_P hn
  obtain ⟨E, hEP, hEc, hsq, hcomm, hnorm⟩ := H.exists_normal_E8 h0 hP hcard hSP hidx
  exact H.no_normal_E8 hP hcard hSP hEP hEc hsq hcomm hnorm

end Setting

end CFSG.EvenSporadicStandard.M11Std
