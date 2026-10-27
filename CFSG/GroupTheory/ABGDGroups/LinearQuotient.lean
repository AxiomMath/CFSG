module

public import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
public import CFSG.GroupTheory.ABGDGroups.WreathedDGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupPSL2

public noncomputable section

namespace CFSG.ABGDGroups

open CFSG.QuasiDihedralFusion
open CFSG.GorensteinWalter (PGammaL2 PSL2 PGL2 IsOddPrimePower HasDihedralSylowTwo
  pGammaL2PSLRange pGammaL2PGLRange)
open scoped commutatorElement

section Transfer

variable {G G' : Type*} [Group G] [Group G'] [Finite G] {π : G →* G'}

theorem nonempty_mulEquiv_mapSurjective (hπ : Function.Surjective π)
    (hker : Odd (Nat.card π.ker)) (P : Sylow 2 G) :
    Nonempty ((P : Subgroup G) ≃* ((P.mapSurjective hπ : Sylow 2 G') : Subgroup G')) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdisj : (P : Subgroup G) ⊓ π.ker = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
    apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
    rw [hk]
    exact (Nat.coprime_two_left.mpr hker).pow_left k
  have hinj : Function.Injective (π.comp (P : Subgroup G).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ (P : Subgroup G) ⊓ π.ker := ⟨x.2, hx⟩
    rw [hdisj, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext hx')
  have hrange : (π.comp (P : Subgroup G).subtype).range =
      ((P.mapSurjective hπ : Sylow 2 G') : Subgroup G') := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Sylow.coe_mapSurjective]
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

theorem hasDihedralSylowTwo_iff_of_surjective (hπ : Function.Surjective π)
    (hker : Odd (Nat.card π.ker)) : HasDihedralSylowTwo G' ↔ HasDihedralSylowTwo G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro h P
    obtain ⟨m, hm, ⟨e⟩⟩ := h (P.mapSurjective hπ)
    obtain ⟨f⟩ := nonempty_mulEquiv_mapSurjective hπ hker P
    exact ⟨m, hm, ⟨f.trans e⟩⟩
  · intro h Q
    obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective hπ 2 Q
    obtain ⟨m, hm, ⟨e⟩⟩ := h P
    obtain ⟨f⟩ := nonempty_mulEquiv_mapSurjective hπ hker P
    exact ⟨m, hm, ⟨f.symm.trans e⟩⟩

theorem hasSemidihedralSylow_iff_of_surjective (hπ : Function.Surjective π)
    (hker : Odd (Nat.card π.ker)) (n : ℕ) :
    HasSemidihedralSylow G' n ↔ HasSemidihedralSylow G n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun P => ?_⟩
    obtain ⟨e⟩ := h (P.mapSurjective hπ)
    obtain ⟨f⟩ := nonempty_mulEquiv_mapSurjective hπ hker P
    exact ⟨e.trans f.symm⟩
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun Q => ?_⟩
    obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective hπ 2 Q
    obtain ⟨e⟩ := h P
    obtain ⟨f⟩ := nonempty_mulEquiv_mapSurjective hπ hker P
    exact ⟨e.trans f⟩

theorem hasWreathedSylow_iff_of_surjective (hπ : Function.Surjective π)
    (hker : Odd (Nat.card π.ker)) (n : ℕ) :
    HasWreathedSylow G' n ↔ HasWreathedSylow G n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun P => ?_⟩
    obtain ⟨e⟩ := h (P.mapSurjective hπ)
    obtain ⟨f⟩ := nonempty_mulEquiv_mapSurjective hπ hker P
    exact ⟨f.trans e⟩
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun Q => ?_⟩
    obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective hπ 2 Q
    obtain ⟨e⟩ := h P
    obtain ⟨f⟩ := nonempty_mulEquiv_mapSurjective hπ hker P
    exact ⟨f.symm.trans e⟩

end Transfer

section Quotient

variable {H : Type} [Group H] [Finite H]

theorem odd_card_ker_mk'_oddCore :
    Odd (Nat.card (QuotientGroup.mk' (CFSG.oddCore H)).ker) := by
  rw [QuotientGroup.ker_mk']
  exact odd_card_oddCore H

theorem hasWreathedSylow_quotient_oddCore_iff (n : ℕ) :
    HasWreathedSylow (H ⧸ CFSG.oddCore H) n ↔ HasWreathedSylow H n :=
  hasWreathedSylow_iff_of_surjective (QuotientGroup.mk'_surjective _) odd_card_ker_mk'_oddCore n

theorem isDGroup_quotient_oddCore (hH : IsDGroup H) :
    IsDGroup (H ⧸ CFSG.oddCore H) := by
  set π := QuotientGroup.mk' (CFSG.oddCore H)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : Odd (Nat.card π.ker) := odd_card_ker_mk'_oddCore
  rcases hH with ⟨hDih, hNC⟩ | ⟨K, hK⟩
  · left
    refine ⟨(hasDihedralSylowTwo_iff_of_surjective hπ hker).mpr hDih, ?_⟩
    rintro ⟨N, hNn, hNcop, hN2⟩
    apply hNC
    refine ⟨N.comap π, hNn.comap π, ?_, ?_⟩
    · rw [CFSG.Semidihedral.FixedFieldCentralizer.preimage_card π hπ N]
      exact Nat.Coprime.mul_right (Nat.coprime_two_left.mpr hker) hNcop
    · have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp π) :=
        (QuotientGroup.mk'_surjective N).comp hπ
      have hk : ((QuotientGroup.mk' N).comp π).ker = N.comap π := by
        rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      exact hN2.of_equiv (((QuotientGroup.quotientMulEquivOfEq hk).symm.trans
        (QuotientGroup.quotientKerEquivOfSurjective _ hsurj))).symm
  · right
    rcases hK.sylow with ⟨n, hSD, hKD⟩ | ⟨n, hW, -⟩
    · refine ⟨K.map π, ?_⟩
      have hKn : K.Normal := hK.normal
      have hOK : CFSG.oddCore H ≤ K := by
        have hdvd := Subgroup.relIndex_dvd_index_of_normal K (CFSG.oddCore H)
        rw [hK.index_eq_two] at hdvd
        have hodd : Odd (K.relIndex (CFSG.oddCore H)) :=
          (odd_card_oddCore H).of_dvd_nat (Subgroup.relIndex_dvd_card _ _)
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact Subgroup.relIndex_eq_one.mp h
        · rw [h] at hodd
          exact absurd hodd (by decide)
      have hkerK : Odd (Nat.card (π.subgroupMap K).ker) := by
        have hle : (π.subgroupMap K).ker.map K.subtype ≤ CFSG.oddCore H := by
          rintro _ ⟨x, hx, rfl⟩
          have h1 : π x = 1 := congrArg Subtype.val hx
          rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h1
        rw [← Subgroup.card_map_of_injective K.subtype_injective]
        exact (odd_card_oddCore H).of_dvd_nat (Subgroup.card_dvd_of_le hle)
      refine ⟨hK.normal.map π hπ, ?_, ?_, Or.inl ⟨n,
        (hasSemidihedralSylow_iff_of_surjective hπ hker n).mpr hSD, ?_⟩⟩
      · rw [Subgroup.index_map_eq K hπ (by rwa [QuotientGroup.ker_mk']), hK.index_eq_two]
      · intro M hM
        apply hK.noIndexTwo (M.comap (π.subgroupMap K))
        rwa [Subgroup.index_comap_of_surjective M (π.subgroupMap_surjective K)]
      · exact (hasDihedralSylowTwo_iff_of_surjective (π.subgroupMap_surjective K) hkerK).mpr hKD
    · exact ⟨K.map π, (isDGroupData_quotient_oddCore hK hW).1⟩

end Quotient

theorem eq_bot_of_normal_of_odd_card_psl2 {F : Type} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (X : Subgroup (PSL2 F)) [X.Normal]
    (hX : Odd (Nat.card X)) : X = ⊥ := by
  have h2 : 2 ∣ Nat.card (PSL2 F) := by
    obtain ⟨P⟩ : Nonempty (Sylow 2 (PSL2 F)) := inferInstance
    obtain ⟨m, -, ⟨e⟩⟩ := CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hF P
    have hP : Nat.card (P : Subgroup (PSL2 F)) = 2 * 2 ^ m := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    exact (Dvd.intro _ hP.symm).trans (Subgroup.card_subgroup_dvd_card _)
  have hodd : Odd (Nat.card F) := by
    obtain ⟨p, f, -, hpodd, -, hq⟩ := hF
    rw [hq]
    exact hpodd.pow
  have hone : 1 < Nat.card F := Finite.one_lt_card
  by_cases h3 : Nat.card F = 3
  ·
    have hcard : Nat.card (PSL2 F) = 12 := by
      rw [CFSG.GorensteinWalter.psl2_card_formula F hF, h3]
      norm_num
    have hdvd : Nat.card X ∣ 3 * 4 := by
      rw [show 3 * 4 = 12 by norm_num, ← hcard]
      exact Subgroup.card_subgroup_dvd_card X
    have hcop : Nat.Coprime (Nat.card X) 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact (Nat.coprime_two_right.mpr hX).pow_right 2
    have hX3 : Nat.card X ∣ 3 := hcop.dvd_of_dvd_mul_right hdvd
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3X : IsPGroup 3 X := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hX3 with h | h
      · exact IsPGroup.of_card (n := 0) (by rw [h, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [h, pow_one])
    exact CFSG.GorensteinWalter.normal_pSubgroup_eq_bot_of_psl2_odd F hF 3 Nat.prime_three
      (by decide) X inferInstance h3X
  · have h4 : 4 ≤ Nat.card F := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal X with h | h
    · exact h
    · rw [h, Subgroup.card_top] at hX
      exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hX)

namespace IsLinearDecomposition

variable {H : Type} [Group H] [Finite H] {F : Type} [Field F] [Finite F] {ι : H →* PGammaL2 F}
  {L E : Subgroup H} {S : Sylow 2 H}

theorem oddCore_eq_bot (hd : IsLinearDecomposition ι L E S) : CFSG.oddCore H = ⊥ := by
  set O := CFSG.oddCore H
  set L₀ := linearCore ι
  have hL₀n : L₀.Normal := hd.linearCore_normal
  obtain ⟨eL₀⟩ := hd.nonempty_linearCore_mulEquiv
  have hF := hd.isOddPrimePower_card
  have hOL : O ⊓ L₀ = ⊥ := by
    have hXodd : Odd (Nat.card (O.subgroupOf L₀)) := by
      rw [← Subgroup.card_map_of_injective L₀.subtype_injective, Subgroup.subgroupOf_map_subtype]
      exact (odd_card_oddCore H).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have : ((O.subgroupOf L₀).map eL₀.toMonoidHom).Normal :=
      (Subgroup.Normal.subgroupOf inferInstance L₀).map _ eL₀.surjective
    have hbot := eq_bot_of_normal_of_odd_card_psl2 hF ((O.subgroupOf L₀).map eL₀.toMonoidHom)
      (by rwa [Subgroup.card_map_of_injective eL₀.injective])
    rw [Subgroup.map_eq_bot_iff_of_injective _ eL₀.injective, Subgroup.subgroupOf_eq_bot] at hbot
    exact disjoint_iff.mp hbot
  have hcomm : O ≤ Subgroup.centralizer (L₀ : Set H) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, eq_bot_iff, ← hOL]
    exact Subgroup.commutator_le_inf O L₀
  by_cases h3 : 3 < Nat.card F
  · rw [eq_bot_iff]
    intro o ho
    have hcent : ι o ∈ Subgroup.centralizer (pGammaL2PSLRange F : Set (PGammaL2 F)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [← hd.map_linearCore] at hz
      obtain ⟨l, hl, rfl⟩ := hz
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp (hcomm ho) l hl]
    rw [CFSG.GorensteinWalter.pGammaL2_pslRange_centralizer_eq_bot F hF h3,
      Subgroup.mem_bot] at hcent
    exact Subgroup.mem_bot.mpr (hd.injective (hcent.trans (map_one ι).symm))
  ·
    have hodd : Odd (Nat.card F) := by
      obtain ⟨p, f, -, hpodd, -, hq⟩ := hF
      rw [hq]
      exact hpodd.pow
    have hone : 1 < Nat.card F := Finite.one_lt_card
    have h3' : Nat.card F = 3 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have hAut : Nat.card (F ≃+* F) = 1 :=
      CFSG.Semidihedral.SemilinearOuterQuotient.fieldAut_card F (p := 3) Nat.prime_three
        (by rw [h3', pow_one])
    have hΓ : Nat.card (PGammaL2 F) = 24 := by
      rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
        CFSG.GorensteinWalter.pgl2_card_formula, hAut, h3']
      norm_num
    have hHle : Nat.card H ≤ 24 := hΓ ▸ Nat.card_le_card_of_injective ι hd.injective
    have hL₀card : Nat.card L₀ = 12 := by
      rw [Nat.card_congr eL₀.toEquiv, CFSG.GorensteinWalter.psl2_card_formula F hF, h3']
      norm_num
    have hidx : L₀.index ≤ 2 := by
      have h := L₀.card_mul_index
      rw [hL₀card] at h
      omega
    have hinj : Function.Injective ((QuotientGroup.mk' L₀).comp O.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have hx' : (x : H) ∈ O ⊓ L₀ := by
        refine ⟨x.2, ?_⟩
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at hx
        exact hx
      rw [hOL, Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.mpr (Subtype.ext hx')
    have hO2 : Nat.card O ≤ 2 := by
      have h := Nat.card_le_card_of_injective _ hinj
      rw [← Subgroup.index_eq_card] at h
      omega
    have hO1 : Nat.card O = 1 := by
      obtain ⟨k, hk⟩ := odd_card_oddCore H
      have hk' : Nat.card O = 2 * k + 1 := hk
      omega
    exact Subgroup.card_eq_one.mp hO1

omit [Finite H] in
theorem commutator_eq_linearCore (hd : IsLinearDecomposition ι L E S) (h3 : 3 < Nat.card F) :
    commutator H = linearCore ι := by
  apply le_antisymm hd.commutator_le_linearCore
  obtain ⟨eL₀⟩ := hd.nonempty_linearCore_mulEquiv
  have := CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three F h3
  have : Group.IsPerfect (linearCore ι) :=
    Group.IsPerfect.ofSurjective (f := eL₀.symm.toMonoidHom) eL₀.symm.surjective
  rw [← Subgroup.commutator_eq_self (H := linearCore ι), commutator_def]
  exact Subgroup.commutator_mono le_top le_top

end IsLinearDecomposition

end CFSG.ABGDGroups
