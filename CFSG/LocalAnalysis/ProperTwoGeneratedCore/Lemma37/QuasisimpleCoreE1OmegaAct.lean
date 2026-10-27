module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1OmegaSet

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open Equiv Equiv.Perm CFSG.Sporadic.Th.Max3

theorem e1_not_genuine_cases : ∀ v : Fin 64, c3Mul v v = 0 → v ≠ 0 → e1Gen true true v = false →
    (e1E v ∧ v ≠ 40) ∨ v = 16 ∨ v = 48 ∨ c3Conj 1 v = 16 ∨ c3Conj 1 v = 48 := by decide

theorem e1_exists_genuine_mul_conj : ∀ v : Fin 64, c3Mul v v = 0 → v ≠ 0 →
    e1Gen true true v = false → ∃ w : Fin 64,
      e1Gen true true (c3Mul v (c3Conj w v)) = true ∧ c3Mul v (c3Conj w v) ≠ 0 := by
  decide +kernel

theorem e1_genuine_three : ∀ v : Fin 64, ∃ g h k : Fin 64, e1Gen true true g = true ∧
    e1Gen true true h = true ∧ e1Gen true true k = true ∧ c3Mul (c3Mul g h) k = v := by
  decide +kernel

theorem kappaWord_facts : E1Data.kappaWord 1 = 32 ∧ E1Data.kappaWord 2 = 16 ∧
    E1Data.kappaWord 3 = 48 := by decide

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
  (htype : ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
    s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
      CaseC3.Genuine (Subgroup.center J) s)
  (hOu : CFSG.pPrimeCore 2 (Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) = ⊥)
  (hOz : CFSG.pPrimeCore 2
    (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}) = ⊥)
include d

@[expose] noncomputable def wordZ (v : Fin 64) :
    Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} :=
  ⟨_, d.map_le_centralizer_forty (d.caseC3BCD.caseC3Word_mem v)⟩

theorem wordZ_mul (v w : Fin 64) : d.wordZ v * d.wordZ w = d.wordZ (c3Mul v w) :=
  Subtype.ext (d.caseC3BCD.caseC3Word_mul v w)

theorem coe_toCentralizer_kappaX (i : Fin 4) :
    ((d.toCentralizer (d.kappaX i) : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) :
      J ⧸ Subgroup.center J) = caseC3Word (Subgroup.center J) u m y x (kappaWord i) := by
  rw [coe_toCentralizer, d.mk_kappaX]

include htype

theorem exists_conj_kappaWord {s : J ⧸ Subgroup.center J}
    (hs : s ∈ Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}) (hss : s * s = 1)
    (hgen : ¬ CaseC3.Genuine (Subgroup.center J) s) :
    ∃ h ∈ Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}, ∃ i : Fin 4,
      h * s * h⁻¹ = caseC3Word (Subgroup.center J) u m y x (kappaWord i) := by
  have hb := d.caseC3BCD
  set C := Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}
  have hs1 : s ≠ 1 := fun h1 => hgen (h1 ▸ ⟨1, QuotientGroup.mk_one _, mul_one 1⟩)
  obtain ⟨k, hk, v, hvv, hv0, hkv⟩ := d.exists_conj_caseC3Word d.map_le_centralizer_forty hs hss hs1
  have hv : e1Gen true true v = false := by
    rw [← Bool.not_eq_true, ← hb.genuine_iff_of_typeD htype, ← hkv]
    intro h'
    have h'' := CaseC3.genuine_conj _ h' k
    rw [show k⁻¹ * (k * s * k⁻¹) * k = s by group] at h''
    exact hgen h''
  have hw1 : caseC3Word (Subgroup.center J) u m y x 1 ∈ C :=
    d.map_le_centralizer_forty (hb.caseC3Word_mem 1)
  have hconj1 : ∀ i : Fin 4, c3Conj 1 v = kappaWord i → ∃ h ∈ C, ∃ i : Fin 4,
      h * s * h⁻¹ = caseC3Word (Subgroup.center J) u m y x (kappaWord i) := fun i hi =>
    ⟨_, C.mul_mem hw1 hk, i, by
      rw [← hi, ← hb.caseC3Word_conj, ← hkv]
      group⟩
  rcases e1_not_genuine_cases v hvv hv0 hv with ⟨hE, h40⟩ | h | h | h | h
  · obtain ⟨h, hh, hhu⟩ := d.exists_conj_self_of_e1E htype le_rfl hE hv0 h40
    refine ⟨h⁻¹ * k, C.mul_mem (C.inv_mem hh) hk, 1, ?_⟩
    rw [kappaWord_facts.1, CaseC3BCD.caseC3Word_thirtytwo,
      show h⁻¹ * k * s * (h⁻¹ * k)⁻¹ = h⁻¹ * (k * s * k⁻¹) * h by group, hkv, ← hhu]
    group
  · exact ⟨k, hk, 2, by rw [kappaWord_facts.2.1, ← h, hkv]⟩
  · exact ⟨k, hk, 3, by rw [kappaWord_facts.2.2, ← h, hkv]⟩
  · exact hconj1 2 (h.trans kappaWord_facts.2.1.symm)
  · exact hconj1 3 (h.trans kappaWord_facts.2.2.symm)

include hOu hOz

@[expose] noncomputable def subX :
    SubMulAction (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40})
      ((J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J))) where
  carrier := d.deltaW 32 ∪ d.deltaW 8
  smul_mem' g _ hβ := d.smul_mem_deltaX_of_mem_centralizer htype hOu hOz g.2 hβ

theorem card_subX :
    Nat.card (d.subX htype hOu hOz) = 9 :=
  (Nat.card_coe_set_eq (d.deltaW 32 ∪ d.deltaW 8)).trans d.ncard_deltaX

@[expose] noncomputable def eX :
    d.subX htype hOu hOz ≃ Fin 9 :=
  Finite.equivFinOfCardEq (d.card_subX htype hOu hOz)

@[expose] noncomputable def psiZ :
    Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} →* Perm (Fin 9) :=
  (permCongrHom (d.eX htype hOu hOz)).toMonoidHom.comp (MulAction.toPermHom _ _)

theorem psiZ_apply_eq_iff
    (g : Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40})
    (i : Fin 9) : d.psiZ htype hOu hOz g i = i ↔
      (g : J ⧸ Subgroup.center J) • (((d.eX htype hOu hOz).symm i :
        d.subX htype hOu hOz) : (J ⧸ Subgroup.center J) ⧸
          B.map (QuotientGroup.mk' (Subgroup.center J))) = ((d.eX htype hOu hOz).symm i : _) := by
  change d.eX htype hOu hOz (g • (d.eX htype hOu hOz).symm i) = i ↔ _
  rw [← Equiv.eq_symm_apply, Subtype.ext_iff, SubMulAction.val_smul]
  rfl

theorem omegaZ_mem_subX :
    d.omegaZ ∈ d.subX htype hOu hOz :=
  Or.inl (d.omegaZ_mem_deltaW 32)

theorem existsUnique_psiZ_fixed
    {g : Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}}
    (hgen : CaseC3.Genuine (Subgroup.center J) (g : J ⧸ Subgroup.center J)) (hg1 : g ≠ 1) :
    ∃! i, d.psiZ htype hOu hOz g i = i := by
  have hg1' : (g : J ⧸ Subgroup.center J) ≠ 1 := fun h => hg1 (Subtype.ext h)
  refine ⟨d.eX htype hOu hOz ⟨_, d.omegaZ_mem_subX htype hOu hOz⟩, ?_, fun i hi => ?_⟩
  · dsimp only
    rw [psiZ_apply_eq_iff, Equiv.symm_apply_apply]
    exact d.smul_omegaZ g.2
  · dsimp only at hi
    rw [psiZ_apply_eq_iff] at hi
    rw [← (d.eX htype hOu hOz).apply_symm_apply i]
    exact congrArg _ (Subtype.ext (d.eq_omegaZ_of_genuine g.2 hgen hg1' hi))

theorem exists_two_psiZ_fixed
    {g : Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}} (hgg : g * g = 1)
    (hgen : ¬ CaseC3.Genuine (Subgroup.center J) (g : J ⧸ Subgroup.center J)) :
    ∃ i j, i ≠ j ∧ d.psiZ htype hOu hOz g i = i ∧ d.psiZ htype hOu hOz g j = j := by
  obtain ⟨h, hh, i, hhi⟩ := d.exists_conj_kappaWord htype g.2
    (congrArg Subtype.val hgg) hgen
  obtain ⟨β, hβ, hβ0⟩ := Set.exists_ne_of_one_lt_ncard
    (by rw [d.ncard_deltaW_thirtytwo]; omega : 1 < (d.deltaW 32).ncard) d.omegaZ
  have hfix : (g : J ⧸ Subgroup.center J) • (h⁻¹ • β) = h⁻¹ • β := by
    have h1 := d.smul_eq_self_of_rho5C_eq_one (d.rho5C_kappaX i)
      (by rw [← d.deltaW_thirtytwo]; exact hβ)
    rw [coe_toCentralizer_kappaX, ← hhi] at h1
    have h2 : (g : J ⧸ Subgroup.center J) • (h⁻¹ • β) =
        h⁻¹ • ((h * (g : J ⧸ Subgroup.center J) * h⁻¹) • β) := by
      rw [smul_smul, smul_smul]
      congr 1
      group
    rw [h2, h1]
  have hmem : h⁻¹ • β ∈ d.subX htype hOu hOz :=
    d.smul_mem_deltaX_of_mem_centralizer htype hOu hOz (Subgroup.inv_mem _ hh) (Or.inl hβ)
  have hne : h⁻¹ • β ≠ d.omegaZ := fun h' => hβ0 (by
    rw [← smul_inv_smul h β, h', d.smul_omegaZ hh])
  refine ⟨d.eX htype hOu hOz ⟨_, d.omegaZ_mem_subX htype hOu hOz⟩,
    d.eX htype hOu hOz ⟨_, hmem⟩, fun h' => hne ?_, ?_, ?_⟩
  · exact (congrArg Subtype.val ((d.eX htype hOu hOz).injective h')).symm
  · rw [psiZ_apply_eq_iff, Equiv.symm_apply_apply]
    exact d.smul_omegaZ g.2
  · rw [psiZ_apply_eq_iff, Equiv.symm_apply_apply]
    exact hfix

theorem psiZ_ne_one_of_genuine
    {g : Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}}
    (hgen : CaseC3.Genuine (Subgroup.center J) (g : J ⧸ Subgroup.center J)) (hg1 : g ≠ 1) :
    d.psiZ htype hOu hOz g ≠ 1 := fun h1 => by
  obtain ⟨i, -, huniq⟩ := d.existsUnique_psiZ_fixed htype hOu hOz hgen hg1
  have h0 := huniq 0 (by dsimp only; rw [h1, Perm.one_apply])
  have h1' := huniq 1 (by dsimp only; rw [h1, Perm.one_apply])
  exact absurd (h0.trans h1'.symm) (by decide)

theorem psiZ_injective :
    Function.Injective (d.psiZ htype hOu hOz) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb := d.caseC3BCD
  set C := Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}
  set K := (d.psiZ htype hOu hOz).ker
  have hKn : K.Normal := MonoidHom.normal_ker _
  have hgenK : ∀ v : Fin 64, e1Gen true true v = true → v ≠ 0 → d.wordZ v ∉ K := fun v hv hv0 h =>
    d.psiZ_ne_one_of_genuine htype hOu hOz ((hb.genuine_iff_of_typeD htype v).mpr hv)
      (fun h1 => hv0 (hb.caseC3Word_eq_one_iff.mp (congrArg Subtype.val h1)))
      (MonoidHom.mem_ker.mp h)
  have hinv : ∀ k ∈ K, k * k = 1 → k = 1 := by
    intro k hk hkk
    by_contra hk1
    have hk1' : (k : J ⧸ Subgroup.center J) ≠ 1 := fun h => hk1 (Subtype.ext h)
    obtain ⟨h, hh, v, hvv, hv0, hhv⟩ := d.exists_conj_caseC3Word d.map_le_centralizer_forty k.2
      (congrArg Subtype.val hkk) hk1'
    have hvK : d.wordZ v ∈ K := by
      rw [show d.wordZ v = ⟨h, hh⟩ * k * ⟨h, hh⟩⁻¹ from Subtype.ext hhv.symm]
      exact hKn.conj_mem k hk _
    by_cases hv : e1Gen true true v = true
    · exact hgenK v hv hv0 hvK
    · obtain ⟨w, hw, hw0⟩ := e1_exists_genuine_mul_conj v hvv hv0 (by simpa using hv)
      apply hgenK _ hw hw0
      rw [← d.wordZ_mul, show d.wordZ (c3Conj w v) = d.wordZ w * d.wordZ v * (d.wordZ w)⁻¹ from
        Subtype.ext (hb.caseC3Word_conj w v).symm]
      exact K.mul_mem hvK (hKn.conj_mem _ hvK _)
  have hodd : Odd (Nat.card K) := by
    by_contra hev
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hev
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 hev
    have hk' : orderOf (k : C) = 2 := by rw [Subgroup.orderOf_coe, hk]
    have hkk : (k : C) * (k : C) = 1 := by rw [← pow_two, ← hk', pow_orderOf_eq_one]
    rw [hinv _ k.2 hkk, orderOf_one] at hk'
    exact absurd hk' (by decide)
  have hle : K ≤ CFSG.pPrimeCore 2 C := le_sSup ⟨hKn, Nat.coprime_two_left.mpr hodd⟩
  rw [hOz, le_bot_iff] at hle
  exact (MonoidHom.ker_eq_bot_iff _).mp hle

theorem sign_psiZ_of_genuine
    {g : Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}}
    (hgen : CaseC3.Genuine (Subgroup.center J) (g : J ⧸ Subgroup.center J)) :
    sign (d.psiZ htype hOu hOz g) = 1 := by
  by_cases hg1 : g = 1
  · rw [hg1, map_one, Perm.sign_one]
  · have hgg : g * g = 1 := Subtype.ext (CaseC3.mul_self_of_genuine hgen)
    exact (cycleType_of_existsUnique_fixed (by rw [← map_mul, hgg, map_one])
      (d.existsUnique_psiZ_fixed htype hOu hOz hgen hg1)).2

theorem sign_psiZ_wordZ
    (v : Fin 64) : sign (d.psiZ htype hOu hOz (d.wordZ v)) = 1 := by
  have hb := d.caseC3BCD
  obtain ⟨g, h, k, hg, hh, hk, rfl⟩ := e1_genuine_three v
  have hgen : ∀ w : Fin 64, e1Gen true true w = true →
      sign (d.psiZ htype hOu hOz (d.wordZ w)) = 1 := fun w hw =>
    d.sign_psiZ_of_genuine htype hOu hOz ((hb.genuine_iff_of_typeD htype w).mpr hw)
  rw [← d.wordZ_mul, ← d.wordZ_mul, map_mul, map_mul, map_mul, map_mul, hgen g hg, hgen h hh,
    hgen k hk, mul_one, mul_one]

omit hOu in
theorem card_centralizer_forty_of_pPrimeCore :
    Nat.card (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}) = 192 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.pPrimeCore 2 (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}))
  rw [d.card_centralizer_forty_quotient_pPrimeCore htype, hOz, Subgroup.card_bot, mul_one] at h
  exact h

theorem sign_psiZ
    (g : Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}) :
    sign (d.psiZ htype hOu hOz g) = 1 := by
  have hb := d.caseC3BCD
  set f : Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} →* ℤˣ :=
    Perm.sign.comp (d.psiZ htype hOu hOz)
  have hS'f : ((S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J))).subgroupOf
      (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}) ≤ f.ker := by
    intro s hs
    obtain ⟨v, hv⟩ := hb.exists_caseC3Word (Subgroup.mem_subgroupOf.mp hs)
    rw [MonoidHom.mem_ker, show s = d.wordZ v from Subtype.ext hv.symm]
    exact d.sign_psiZ_wordZ htype hOu hOz v
  have hS' : Nat.card (((S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J))).subgroupOf
      (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40})) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.map_le_centralizer_forty).toEquiv]
    exact hb.card_map_top
  have hidx : f.ker.index ≤ 2 := by
    rw [Subgroup.index_ker]
    calc Nat.card f.range ≤ Nat.card ℤˣ := Subgroup.card_le_card_group _
      _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hidx0 : f.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmul := Subgroup.card_mul_index f.ker
  rw [d.card_centralizer_forty_of_pPrimeCore htype hOz] at hmul
  have hdvd := Subgroup.card_dvd_of_le hS'f
  rw [hS'] at hdvd
  have h1 : f.ker.index = 1 := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc] at hmul
    rcases (show f.ker.index = 1 ∨ f.ker.index = 2 by omega) with h | h
    · exact h
    · rw [h] at hmul
      omega
  have hg : g ∈ f.ker := by
    rw [Subgroup.index_eq_one.mp h1]
    exact Subgroup.mem_top g
  exact (MonoidHom.mem_ker (f := f)).mp hg

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
