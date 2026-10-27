module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem
public import CFSG.ClassicalInvolution.QuaternionStructure.Lifting
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196

open CFSG CFSG.GorensteinWalter CFSG.ClassicalInvolution.QuaternionStructure
open scoped MatrixGroups

theorem index_sup_eq_two {Q : Type*} [Group Q] [Finite Q] {N O : Subgroup Q} [N.Normal]
    (hN : N.index = 2) (hO : Odd (Nat.card O)) : (N ⊔ O).index = 2 := by
  have h1 : (N ⊔ O).index ∣ 2 := hN ▸ Subgroup.index_dvd_of_le le_sup_left
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exfalso
    have htop : N ⊔ O = ⊤ := Subgroup.index_eq_one.mp h
    have h2 : N.relIndex (O ⊔ N) = N.relIndex O := Subgroup.relIndex_sup_right O N
    rw [sup_comm, htop, Subgroup.relIndex_top_right, hN] at h2
    have h3 : 2 ∣ Nat.card O := h2 ▸ Subgroup.relIndex_dvd_card N O
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h3)
  · exact h

theorem commutator_le_of_index_eq_two {Q : Type*} [Group Q] {N : Subgroup Q} (hN : N.index = 2) :
    commutator Q ≤ N := by
  rw [commutator_def, Subgroup.commutator_le]
  intro g _ h _
  rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hN,
    Subgroup.mul_mem_iff_of_index_two hN, Subgroup.mul_mem_iff_of_index_two hN,
    Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
  tauto

theorem eq_top_of_normal_of_odd_index_quotient {Q : Type*} [Group Q]
    (hgen : ∀ M : Subgroup Q, M.Normal → Odd M.index → M = ⊤) (O : Subgroup Q) [O.Normal]
    (M : Subgroup (Q ⧸ O)) (hM : M.Normal) (hodd : Odd M.index) : M = ⊤ := by
  have h1 := hgen (M.comap (QuotientGroup.mk' O)) (hM.comap _)
    (by rwa [Subgroup.index_comap_of_surjective M (QuotientGroup.mk'_surjective O)])
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O x
  have hy : y ∈ M.comap (QuotientGroup.mk' O) := h1 ▸ Subgroup.mem_top y
  exact hy

theorem natCard_pgl2_eq {F : Type*} [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F)) :
    Nat.card (PGL2 F) = 2 * Nat.card (PSL2 F) := by
  have h1 := pgl2_psl2Range_index_eq_two F hF
  have h2 := Subgroup.card_mul_index
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range
  rw [h1, ← Nat.card_congr (MonoidHom.ofInjective
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).toEquiv] at h2
  rw [← h2]
  ring

theorem natCard_psl2_of_card_eq_three {F : Type} [Field F] [Finite F] (h3 : Nat.card F = 3) :
    Nat.card (PSL2 F) = 12 := by
  have : Fintype F := Fintype.ofFinite F
  let eK : ZMod 3 ≃+* F :=
    ZMod.ringEquivOfPrime F Nat.prime_three (by simpa [Nat.card_eq_fintype_card] using h3)
  rw [← Nat.card_congr (psl2RingEquiv eK).toEquiv,
    Nat.card_congr psl2_three_equiv_alternatingGroup.toEquiv, nat_card_alternatingGroup,
    Nat.card_fin]
  rfl

theorem nonempty_commutator_mulEquiv_psl2 {Q : Type} [Group Q] [Finite Q] {F : Type} [Field F]
    [Finite F] (hF : IsOddPrimePower (Nat.card F)) (e : Q ≃* PGL2 F) :
    Nonempty (commutator Q ≃* PSL2 F) := by
  by_cases h3 : Nat.card F = 3
  · have : Fintype F := Fintype.ofFinite F
    let eK : ZMod 3 ≃+* F :=
      ZMod.ringEquivOfPrime F Nat.prime_three (by simpa [Nat.card_eq_fintype_card] using h3)
    obtain ⟨eC⟩ := commutator_mulEquiv_alternatingGroup_of_mulEquiv_perm_four
      (e.trans ((pgl2RingEquiv eK).symm.trans pgl2_three_equiv_perm))
    exact ⟨(eC.trans psl2_three_equiv_alternatingGroup.symm).trans (psl2RingEquiv eK)⟩
  · have hodd := odd_natCard_of_isOddPrimePower hF
    have hone : 1 < Nat.card F := Finite.one_lt_card
    have hgt : 3 < Nat.card F := by
      obtain ⟨k, hk⟩ := hodd
      omega
    exact commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three F hF hgt e

theorem gw_index_two {Q : Type} [Group Q] [Finite Q] (hD : HasDihedralSylowTwo Q)
    (hgen : ∀ M : Subgroup Q, M.Normal → Odd M.index → M = ⊤) {N : Subgroup Q} [N.Normal]
    (hN : N.index = 2) (h8 : 8 ∣ Nat.card Q) :
    IsPGroup 2 ↥(N.map (QuotientGroup.mk' (pPrimeCore 2 Q))) ∨
      ∃ (F : Type) (_ : Field F) (_ : Finite F), IsOddPrimePower (Nat.card F) ∧
        Nonempty (↥(N.map (QuotientGroup.mk' (pPrimeCore 2 Q))) ≃* PSL2 F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (pPrimeCore 2 Q).Normal := pPrimeCore_normal
  have hπs : Function.Surjective (QuotientGroup.mk' (pPrimeCore 2 Q)) :=
    QuotientGroup.mk'_surjective _
  have hOodd : Odd (Nat.card (pPrimeCore 2 Q)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hN' : (N.map (QuotientGroup.mk' (pPrimeCore 2 Q))).index = 2 := by
    rw [Subgroup.index_map, QuotientGroup.ker_mk', MonoidHom.range_eq_top.mpr hπs,
      Subgroup.index_top, mul_one]
    exact index_sup_eq_two hN hOodd
  have : (N.map (QuotientGroup.mk' (pPrimeCore 2 Q))).Normal :=
    Subgroup.Normal.map inferInstance _ hπs
  have h8' : 8 ∣ Nat.card (Q ⧸ pPrimeCore 2 Q) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 Q)] at h8
    have hc : Nat.Coprime 8 (Nat.card (pPrimeCore 2 Q)) := by
      have := Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hOodd)
      simpa using this
    exact hc.dvd_of_dvd_mul_right h8
  have hgen' := eq_top_of_normal_of_odd_index_quotient hgen (pPrimeCore 2 Q)
  have hsimple : IsSimpleGroup (Q ⧸ pPrimeCore 2 Q) → False := by
    intro hs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (pPrimeCore 2 Q)))
      with h | h
    · rw [h, Subgroup.index_bot] at hN'
      rw [hN'] at h8'
      omega
    · rw [h, Subgroup.index_top] at hN'
      omega
  rcases CFSG.GorensteinWalter.gorensteinWalter Q hD with ⟨-, h2⟩ | ⟨-, ⟨e⟩⟩ |
    ⟨-, F, hFpp, L, hLn, hLodd, hLmodel⟩
  · exact Or.inl (h2.to_subgroup _)
  · exfalso
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact hsimple e.isSimpleGroup
  · have hL : L = ⊤ := hgen' L hLn hLodd
    let eTop : (Q ⧸ pPrimeCore 2 Q) ≃* L :=
      Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hL.symm)
    rcases hLmodel with heL | heL
    · obtain ⟨eL⟩ := heL
      exfalso
      by_cases h3 : Nat.card F = 3
      · rw [Nat.card_congr (eTop.trans eL).toEquiv, natCard_psl2_of_card_eq_three h3] at h8'
        omega
      · have hodd := odd_natCard_of_isOddPrimePower hFpp
        have hone : 1 < Nat.card F := Finite.one_lt_card
        have hgt : 3 < Nat.card F := by
          obtain ⟨k, hk⟩ := hodd
          omega
        rcases BenderSuzuki.External.huppert_blackburn_XI_example_1_3_a F with
          ⟨_hOmegaCard, _rho, _iota, _hrho, _hiota, _hiota_apply, _hrho_apply,
            _hiota_normal, _hiota_index, _hsharp, hlarge, _hsmall_two, _hsmall_three⟩
        have : IsSimpleGroup (PSL2 F) := (hlarge hgt).1
        exact hsimple (eTop.trans eL).isSimpleGroup
    · obtain ⟨eL⟩ := heL
      right
      refine ⟨F, inferInstance, inferInstance, hFpp, ?_⟩
      obtain ⟨eC⟩ := nonempty_commutator_mulEquiv_psl2 hFpp (eTop.trans eL)
      have hle := commutator_le_of_index_eq_two hN'
      have hcard : Nat.card ↥(N.map (QuotientGroup.mk' (pPrimeCore 2 Q))) ≤
          Nat.card ↥(commutator (Q ⧸ pPrimeCore 2 Q)) := by
        have h1 := Subgroup.card_mul_index (N.map (QuotientGroup.mk' (pPrimeCore 2 Q)))
        rw [hN', Nat.card_congr (eTop.trans eL).toEquiv, natCard_pgl2_eq hFpp,
          ← Nat.card_congr eC.toEquiv] at h1
        omega
      have heq := Subgroup.eq_of_le_of_card_ge hle hcard
      exact ⟨(MulEquiv.subgroupCongr heq.symm).trans eC⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196
