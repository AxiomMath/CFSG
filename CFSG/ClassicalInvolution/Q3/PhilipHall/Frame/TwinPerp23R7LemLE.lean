module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLS4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLAbs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7EGenD
import CFSG.ClassicalInvolution.AschTight.Sec7L714F

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


theorem exists_pi_M {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W E : Subgroup G}
    (φ : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)) (hME : MGrp Ω W ≤ E)
    (hOEn : E ≤ Subgroup.normalizer (oddCoreOf E : Set G)) :
    ∃ π : ↥(MGrp Ω W) →* Equiv.Perm (Fin 3), Function.Surjective π ∧
      (∀ m : ↥(MGrp Ω W), (m : G) ∈ oddCoreOf E → π m = 1) ∧
      (∀ m : ↥(MGrp Ω W), π m = 1 → ∃ w ∈ W, ∃ c ∈ OCW W, w * c = ((m * m : ↥(MGrp Ω W)) : G)) := by
  have hMn : MGrp Ω W ≤ Subgroup.normalizer (W : Set G) :=
    Asc77.Thompson.MGrp_le_normalizer Ω W
  let ψ₀ : ↥(MGrp Ω W) →* NQuot (W ⊔ OCW W) :=
    (Asc77.Thompson.piN W).comp (Subgroup.inclusion hMn)
  have hψ₀ : ∀ m : ↥(MGrp Ω W), ψ₀ m ∈ muGroup Ω W := by
    intro m
    have h1 : Asc77.Thompson.piG W (m : G) = ψ₀ m := by
      rw [Asc77.Thompson.piG_of_mem (hMn m.2)]; rfl
    rw [← h1]
    exact Asc77.Thompson.piG_mem_muGroup (Subgroup.mem_sup_left m.2)
  let ψ : ↥(MGrp Ω W) →* ↥(muGroup Ω W) := ψ₀.codRestrict _ hψ₀
  have hψs : Function.Surjective ψ := by
    intro q
    obtain ⟨m, hm, hq⟩ := Asc77.Thompson.mem_muGroup_iff.mp q.2
    have hmem : m ∈ ((MGrp Ω W ⊔ OCW W : Subgroup G) : Set G) := hm
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (MGrp Ω W) (OCW W)
      (hMn.trans (Asc77.Thompson.normalizer_le_normalizer_OCW W))] at hmem
    obtain ⟨a, ha, c, hc, rfl⟩ := hmem
    have hcN : c ∈ Subgroup.normalizer (W : Set G) := Asc77.Thompson.OCW_le_normalizer W hc
    refine ⟨⟨a, ha⟩, Subtype.ext ?_⟩
    show ψ₀ ⟨a, ha⟩ = (q : NQuot (W ⊔ OCW W))
    rw [hq, Asc77.Thompson.piG_mul (hMn ha) hcN,
      Asc77.Thompson.piG_of_mem_sup (Subgroup.mem_sup_right hc), mul_one,
      Asc77.Thompson.piG_of_mem (hMn ha)]
    rfl
  have hψker : ∀ m : ↥(MGrp Ω W), ψ m = 1 → (m : G) ∈ W ⊔ OCW W := by
    intro m hm
    have h1 : ψ₀ m = 1 := congrArg Subtype.val hm
    exact (Asc77.Thompson.piN_eq_one_iff W ⟨m, hMn m.2⟩).mp h1
  have hB : ∀ m : ↥(MGrp Ω W), (m : G) ∈ oddCoreOf E → φ (ψ m) = 1 := by
    intro m hmO
    let B : Subgroup ↥(MGrp Ω W) := (oddCoreOf E).comap (MGrp Ω W).subtype
    haveI hBn : B.Normal := ⟨fun x hx g => by
      have hx' : (x : G) ∈ oddCoreOf E := hx
      have := (Subgroup.mem_normalizer_iff.mp (hOEn (hME g.2)) (x : G)).mp hx'
      exact this⟩
    have hBodd : Odd (Nat.card B) := by
      have h1 : Nat.card B = Nat.card (B.map (MGrp Ω W).subtype) :=
        Nat.card_congr (Subgroup.equivMapOfInjective B _ (MGrp Ω W).subtype_injective).toEquiv
      have h2 : B.map (MGrp Ω W).subtype ≤ oddCoreOf E := by
        rintro _ ⟨x, hx, rfl⟩
        exact hx
      rw [h1]
      exact (odd_natCard_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le h2)
    let Q4 : Subgroup (Equiv.Perm (Fin 4)) := B.map (φ.toMonoidHom.comp ψ)
    haveI : Q4.Normal := Subgroup.Normal.map hBn _ (φ.surjective.comp hψs)
    have hQodd : Odd (Nat.card Q4) := hBodd.of_dvd_nat (Subgroup.card_map_dvd _ _)
    have hQ : Q4 = ⊥ := perm4_oddNormal_trivial Q4 hQodd
    have hm : (φ.toMonoidHom.comp ψ) m ∈ Q4 := Subgroup.mem_map_of_mem _ hmO
    rw [hQ, Subgroup.mem_bot] at hm
    exact hm
  refine ⟨s4ToS3.comp (φ.toMonoidHom.comp ψ), ?_, ?_, ?_⟩
  · intro s
    obtain ⟨g4, hg4⟩ := s4ToS3_surjective s
    obtain ⟨q, hq⟩ := φ.surjective g4
    obtain ⟨m, hm⟩ := hψs q
    refine ⟨m, ?_⟩
    show s4ToS3 (φ (ψ m)) = s
    rw [hm, hq, hg4]
  · intro m hmO
    show s4ToS3 (φ (ψ m)) = 1
    rw [hB m hmO, map_one]
  · intro m hπ1
    have h4 : φ (ψ m) * φ (ψ m) = 1 := s4ToS3_ker_sq hπ1
    rw [← map_mul, ← map_mul] at h4
    have hsq : ψ (m * m) = 1 := φ.map_eq_one_iff.mp h4
    exact Asc77.Thompson.mem_sup_OCW_iff.mp (hψker _ hsq)

theorem pow_mem_oddCore_of_sq {G : Type} [Group G] [Finite G] {W E M : Subgroup G}
    (hW2 : IsPGroup 2 W) (hE : E ≤ oddCoreOf E ⊔ (E ⊓ Subgroup.normalizer (W : Set G)))
    (hME : M ≤ E) {m : G} (hm : m ∈ M) {w c : G} (hw : w ∈ W) (hc : c ∈ OCW W)
    (hwc : w * c = m * m) : ∃ k : ℕ, m ^ (2 ^ k) ∈ oddCoreOf E := by
  obtain ⟨j, hj⟩ := hW2 ⟨w, hw⟩
  have hwj : w ^ (2 ^ j) = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hwcc : Commute w c := Subgroup.mem_centralizer_iff.mp
    (Asc77.Thompson.OCW_le_centralizer W hc) w hw
  have hmpow : m ^ (2 ^ (j + 1)) = c ^ (2 ^ j) := by
    have e1 : m ^ (2 ^ (j + 1)) = (m * m) ^ (2 ^ j) := by
      rw [← sq, ← pow_mul, ← pow_succ']
    rw [e1, ← hwc, hwcc.mul_pow, hwj, one_mul]
  refine ⟨j + 1, F7G.inf_OCW_le hE ⟨Subgroup.pow_mem _ (hME hm) _, ?_⟩⟩
  rw [hmpow]
  exact Subgroup.pow_mem _ hc _

section E

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem modS3O_rLayer (hc : P23Cfg n Y R S t K' W u e g) (hE : ECase1 R W e) :
    ModS3O ↥(rLayer (Om R) e) := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hd := hc.data
  obtain ⟨φ⟩ := hd.hS4
  have hNe := normalizer_le_centralizer_e hd
  have hME : MGrp (Om R) W ≤ rLayer (Om R) e :=
    iSup₂_le fun R' hR' => F7C.le_rLayer hR'.1 (hR'.2.trans hNe)
  have hEM : rLayer (Om R) e ≤ oddCoreOf (rLayer (Om R) e) ⊔ MGrp (Om R) W :=
    F7G.rLayer_le_sup_MGrp hΩ hE
  have hOEn : rLayer (Om R) e ≤ Subgroup.normalizer (oddCoreOf (rLayer (Om R) e) : Set Y) :=
    Sec7.le_normalizer_oddCoreOf _
  obtain ⟨πM, hπMs, hπMO, hπM2⟩ := exists_pi_M φ hME hOEn
  refine modS3O_of_le_sup hME hOEn hEM πM hπMs hπMO fun m hm1 => ?_
  obtain ⟨w, hw, c, hc', hwc⟩ := hπM2 m hm1
  exact pow_mem_oddCore_of_sq (Asc77.Thompson.isPGroup_of_mem_WSet hd.hW) hE hME m.2 hw hc' hwc

end E

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
