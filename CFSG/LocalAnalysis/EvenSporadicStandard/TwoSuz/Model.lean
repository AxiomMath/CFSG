module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.Faithful
public import CFSG.Sporadic.Recognition.SuzMultiplier
public import Certificates.Certificate25001
public import Certificates.Certificate15030
public import Certificates.Certificate15031
public import Certificates.Certificate15032
public import Certificates.Certificate15033
public import Certificates.Certificate15034
public import Certificates.Certificate15035

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

open Subgroup CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.SuzMultiplier
  CFSG.Sporadic.Recognition.CoverTransfer

open CFSG.Sporadic.Presentation.Suz (R0)
open CFSG.Sporadic.SuzOddCore (suzM suzM_isSimpleGroup)

theorem ofMt_negM : ofMt negM = -1 := by
  ext i k
  have hp : 12 * i.val + k.val < 144 := by omega
  simp only [ofMt, Matrix.of_apply]
  rw [negM, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hp, dite_true, Option.getD_some]
  have h1 : (12 * i.val + k.val) / 12 = i.val := by omega
  have h2 : (12 * i.val + k.val) % 12 = k.val := by omega
  rw [h1, h2, Matrix.neg_apply, Matrix.one_apply]
  by_cases h : i = k
  · subst h
    simp only [ite_true]
    decide
  · have : i.val ≠ k.val := fun h' => h (Fin.ext h')
    rw [ite_eq_right this, ite_eq_right h]
    decide

section Rho


theorem coverCheck_facts :
    coverMats.size = 9 ∧ coverGS.valid = true ∧
      (∀ w ∈ suzCover, coverGS.eval (wordCodes w) = oneM) ∧
      coverGS.eval (wordCodes suzR3) = oneM ∧ coverGS.eval [6, 6] = negM ∧
      mulM negM matA = coverGS.eval ((CFSG.Sporadic.Bridge.SuzGPL.Native.surjWords.getD 0 []).map
        zCode) ∧
      mulM negM matB = coverGS.eval ((CFSG.Sporadic.Bridge.SuzGPL.Native.surjWords.getD 1 []).map
        zCode) := by
  have h := Certificates.certificate25001
  simp only [coverCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h4, h5, h6, h7, h8⟩

theorem coverGS_valid : coverGS.valid = true := coverCheck_facts.2.1

@[expose] def Yu (i : Fin gcS) : GL12 := coverGS.letterU coverGS_valid (2 * i.val)

theorem letterU_odd (i : ℕ) :
    coverGS.letterU coverGS_valid (2 * i + 1) = (coverGS.letterU coverGS_valid (2 * i))⁻¹ := by
  refine Units.ext ?_
  have h1 : (2 * i + 1) % 2 = 1 := by omega
  have h2 : (2 * i + 1) / 2 = i := by omega
  have h3 : (2 * i) % 2 = 0 := by omega
  have h4 : (2 * i) / 2 = i := by omega
  simp only [GenSys.letterU, h1, h2, h3, h4, ite_true, one_ne_zero, ite_false]
  rfl

theorem lift_Yu_mk (w : List (Fin gcS × Bool)) :
    FreeGroup.lift Yu (FreeGroup.mk w) = coverGS.evalU coverGS_valid (wordCodes w) := by
  rw [FreeGroup.lift_mk, GenSys.evalU, wordCodes, List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  obtain ⟨i, b⟩ := l
  cases b
  · simp only [Function.comp_apply, Bool.false_eq_true, Bool.cond_false, ite_false]
    exact (letterU_odd i.val).symm ▸ rfl
  · simp only [Function.comp_apply, Bool.cond_true, ite_true, add_zero]
    rfl

theorem evalU_eq_one {w : List ℕ} (h : coverGS.eval w = oneM) :
    coverGS.evalU coverGS_valid w = 1 := by
  refine Units.ext ?_
  rw [← GenSys.ofMt_eval, h, ofMt_oneM]
  rfl

theorem rho_rels : ∀ r ∈ coverRelators (wordSet R0) suzCommW, FreeGroup.lift Yu r = 1 := by
  rw [coverRelators_suzCommW]
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  rw [lift_Yu_mk]
  exact evalU_eq_one (coverCheck_facts.2.2.1 w hw)

@[expose] noncomputable def rho : SuzCover →* GL12 := PresentedGroup.toGroup rho_rels

theorem rho_of (i : Fin gcS) : rho (PresentedGroup.of i) = Yu i := by
  rw [rho]
  exact PresentedGroup.toGroup.of rho_rels

theorem rho_mk (w : List (Fin gcS × Bool)) :
    rho (PresentedGroup.mk _ (FreeGroup.mk w)) = coverGS.evalU coverGS_valid (wordCodes w) := by
  rw [rho, ← lift_Yu_mk]
  rfl

theorem rho_suzZ : rho suzZ = 1 := by
  rw [suzZ, rho_mk]
  exact evalU_eq_one coverCheck_facts.2.2.2.1

theorem rho_sq_d : rho (PresentedGroup.of suzD ^ 2) = -1 := by
  have h := coverCheck_facts.2.2.2.2.1
  have hd : suzD.val = 3 := rfl
  have e : coverGS.evalU coverGS_valid [6, 6] = Yu suzD * Yu suzD := by
    simp only [GenSys.evalU, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, Yu, hd]
  have h2 : ((Yu suzD * Yu suzD : GL12) : Matrix (Fin 12) (Fin 12) (ZMod 3)) = ofMt negM := by
    rw [← e, ← GenSys.ofMt_eval, h]
  rw [map_pow, rho_of, pow_two]
  refine Units.ext ?_
  rw [h2, ofMt_negM]
  rfl

end Rho

theorem neg_one_ne_one_GL : (-1 : GL12) ≠ 1 := by
  intro h
  have := congrArg (fun u : GL12 => (u : Matrix (Fin 12) (Fin 12) (ZMod 3)) 0 0) h
  revert this
  decide

section Embedding


theorem exists_embedding {L : Type} [Group L] [Finite L] [Group.IsPerfect L] (q : L →* suzM)
    (hq : Function.Surjective q) {t : L} (ht : orderOf t = 2) (hker : q.ker = zpowers t)
    (hcen : zpowers t ≤ center L) :
    ∃ (φ : SuzCover →* L) (ψ : L →* GL12), Function.Surjective φ ∧ Function.Injective ψ ∧
      q.comp φ = suzπ Certificates.certificate15030 ∧ ψ.comp φ = rho ∧ ψ t = -1 := by
  have hTab := Certificates.certificate15030
  have hRho0 := Certificates.certificate15031
  have hRhoJ2 := Certificates.certificate15032
  have hL0 := Certificates.certificate15033
  have hL1 := Certificates.certificate15034
  have hL2 := Certificates.certificate15035
  obtain ⟨hfin, -⟩ := card_suzCover_le hL0 hL1 hL2
  have hkerc : q.ker ≤ center L := hker ▸ hcen
  obtain ⟨φ, hφ, hcomp⟩ := exists_surjective_lift (isPresentation_suzGen hTab)
    suzCommW_mem_commutator (lift_suzCommW hTab) q hq hkerc
  obtain ⟨hk3, hP⟩ := card_ker_eq_three_of_doubleCover hTab hRho0 hL0 hL1 hL2 q hq ht hker φ hφ
  have hkπ : Nat.card (suzπ hTab).ker = 6 := by
    have h1 := card_suzCover hTab
    rw [card_griessHopfMultiplier_eq_card_ker hTab, hP] at h1
    omega
  have hzπ : suzZ ∈ (suzπ hTab).ker := suzπ_suzZ hTab
  have hdπ : (PresentedGroup.of suzD : SuzCover) ^ 2 ∈ (suzπ hTab).ker := by
    rw [MonoidHom.mem_ker, map_pow, suzπ_of hTab]
    exact suzGen_d_sq hTab
  have h3 : 3 ∣ orderOf suzZ := by
    have := orderOf_map_dvd (suzRho0 hRho0) suzZ
    rwa [orderOf_suzRho0_suzZ] at this
  have hord : orderOf suzZ ∣ 6 := by
    have : orderOf (⟨suzZ, hzπ⟩ : (suzπ hTab).ker) ∣ 6 := hkπ ▸ orderOf_dvd_natCard _
    rwa [← Subgroup.orderOf_coe] at this
  have hord3 : orderOf suzZ = 3 := by
    by_contra hne
    have hpos : 0 < orderOf suzZ :=
      Nat.pos_of_ne_zero fun h0 => by rw [h0] at hord; norm_num at hord
    have h6 : orderOf suzZ = 6 := by
      obtain ⟨k, hk⟩ := h3
      have hle6 := Nat.le_of_dvd (by norm_num) hord
      have hk1 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h] at hk; omega
        · exact h
      have hk2 : k ≤ 2 := by omega
      interval_cases k
      · exact absurd hk hne
      · omega
    have hle : zpowers suzZ ≤ (suzπ hTab).ker := zpowers_le.2 hzπ
    have heq : zpowers suzZ = (suzπ hTab).ker :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, h6, hkπ])
    have hmem : (PresentedGroup.of suzD : SuzCover) ^ 2 ∈ zpowers suzZ := heq ▸ hdπ
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hmem
    have := congrArg rho hn
    rw [rho_sq_d, map_zpow, rho_suzZ, one_zpow] at this
    exact neg_one_ne_one_GL this.symm
  have hz3 : suzZ ^ 3 = 1 := by rw [← hord3]; exact pow_orderOf_eq_one _
  have hexp : ∀ c ∈ q.ker, c ^ 2 = 1 := by
    intro c hc
    rw [hker] at hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ht, pow_orderOf_eq_one,
      one_zpow]
  have hφz : φ suzZ = 1 := by
    have hmem : φ suzZ ∈ q.ker := by
      rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hcomp]
      exact suzπ_suzZ hTab
    have h2 := hexp _ hmem
    have h3' : φ suzZ ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
    calc φ suzZ = φ suzZ ^ 3 * (φ suzZ ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3', h2]; simp
  have hkφ : φ.ker = zpowers suzZ := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hφz) ?_
    rw [hk3, Nat.card_zpowers, hord3]
  have hle : φ.ker ≤ rho.ker := by
    rw [hkφ, zpowers_le]
    exact rho_suzZ
  let ψ : L →* GL12 :=
    (φ.liftOfRightInverse (Function.surjInv hφ) (Function.rightInverse_surjInv hφ)) ⟨rho, hle⟩
  have hψφ : ψ.comp φ = rho :=
    MonoidHom.liftOfRightInverse_comp φ _ (Function.rightInverse_surjInv hφ) ⟨rho, hle⟩
  have hdsq : φ (PresentedGroup.of suzD) ^ 2 = t := by
    refine sq_eq_of_lift_conj_d hTab hRho0 hRhoJ2 hL0 hL1 hL2 q hq ht hker hcen (h := 1) ?_
    rw [← MonoidHom.comp_apply, hcomp, suzπ_of hTab]
    group
  have hψt : ψ t = -1 := by
    rw [← hdsq, ← map_pow, ← MonoidHom.comp_apply, hψφ, rho_sq_d]
  have : IsSimpleGroup suzM := suzM_isSimpleGroup
  exact ⟨φ, ψ, hφ, CFSG.EvenSporadicStandard.TwoRu.injective_of_ker_zpowers hq ht hker ψ
    (by rw [hψt]; exact neg_one_ne_one_GL), hcomp, hψφ, hψt⟩

end Embedding

end CFSG.EvenSporadicStandard.TwoSuz
