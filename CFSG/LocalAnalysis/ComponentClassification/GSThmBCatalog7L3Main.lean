module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdL3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdSp4Row
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L3Uni

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7Std

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem card_psl2_of_odd {K : Type} [Field K] [Finite K] {s : ℕ} (hs : Odd s)
    (hK : Nat.card K = s) : Nat.card (GorensteinWalter.PSL2 K) = s * (s ^ 2 - 1) / 2 := by
  rw [Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj 2 K).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK]
  simp only [show 2 * (2 - 1) / 2 = 1 from rfl, pow_one, show Finset.Icc 2 2 = {2} from rfl,
    Finset.prod_singleton]
  have h2 : Nat.gcd 2 (s - 1) = 2 :=
    Nat.gcd_eq_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hs odd_one))
  rw [h2]

theorem isQuasisimple_of_model {H : Type} [Group H] [Finite H]
    (hC : centralizer (generalizedFitting H : Set H) = ⊥) {x : H} (hx : orderOf x = 2)
    {L : Subgroup H} (hLx : L ≤ centralizer ({x} : Set H)) (hLF : L ≤ generalizedFitting H)
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set H)))) {M : Type*} [Group M]
    [Finite M] (θ : ↥(generalizedFitting H) ≃* M)
    (hB : ∀ α : MulAut M, α ^ 2 = 1 → α ≠ 1 → ∀ L' : Subgroup (fixedSubgroup α),
      IsPComponent 2 L' → CFSG.IsQuasisimple L') : CFSG.IsQuasisimple L := by
  obtain ⟨α, hα2, hα1, L', hL'le, hL'pc, ⟨eL'⟩⟩ := exists_fixed_pComponent hC hx hLx hLF hL θ
  have h1 := hB α hα2 hα1 _ hL'pc
  rw [isQuasisimple_congr (subgroupOfEquivOfLe hL'le)] at h1
  exact (isQuasisimple_congr eL').mp h1

variable {H : Type} [Group H] [Finite H]

theorem l3EpsL2Input : L3EpsL2Input := by
  intro H _ _ hsimp hC p f hp hp2 hf hm x hx L hLF hLx hL p' f' hp' hp'2 hf' h5 hLm
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have : (generalizedFitting H).Normal := LocalCores.generalized_fitting_characteristic.2
  set C := centralizer ({x} : Set H) with hCdef
  obtain ⟨-, F', _, _, hF', ⟨eF'⟩⟩ :=
    LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hLm
  have hQodd : Odd (p' ^ f') := (hp'.odd_of_ne_two hp'2).pow
  let eB : L ⧸ pPrimeCore 2 L ≃* GorensteinWalter.PSL2 F' :=
    eF'.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F').symm
  have hQ3 : 3 < Nat.card F' := by rw [hF']; omega
  have hcardB : Nat.card (L ⧸ pPrimeCore 2 L) = p' ^ f' * ((p' ^ f') ^ 2 - 1) / 2 := by
    rw [Nat.card_congr eB.toEquiv, card_psl2_of_odd hQodd hF']
  have hLq : CFSG.IsQuasisimple L := by
    rcases hm with hm | hm
    · obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ :=
        LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hm
      have : CharP K p := finite_field_prime_power_characteristic hp hf hK
      have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
      let φ' : ↥(generalizedFitting H) ≃* LinearFlag.projectiveSL 3 K :=
        φ.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
          (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))
      have : Finite (LinearFlag.projectiveSL 3 K) := Finite.of_equiv _ φ'.toEquiv
      exact isQuasisimple_of_model hC hx hLx hLF hL φ' fun α hα2 hα1 L' hL' =>
        CatalogueBLinearHigherB.odd_higher_linear_involution_fixed_p_components 3 K hK2
          (le_refl 3) α hα1 hα2 2 Nat.prime_two L' hL'
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
        LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hm
      have hud : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
      let θ : ↥(generalizedFitting H) ≃* unitaryPSU hud 3 :=
        e.trans (unitaryPSUEquiv hud (by norm_num)).symm
      have : Finite (unitaryPSU hud 3) := Finite.of_equiv _ θ.toEquiv
      exact isQuasisimple_of_model hC hx hLx hLF hL θ fun α hα2 hα1 L' hL' =>
        CatalogueBUnitaryB.odd_unitary_involution_fixed_p_components hud hp2 (le_refl 3) α
          (orderOf_eq_prime hα2 hα1) 2 Nat.prime_two L' hL'
  have hcore : pPrimeCore 2 L = center L := by
    apply le_antisymm
    · rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hLq (pPrimeCore 2 L)
        with h | h
      · exact h
      · exfalso
        have h1 : Nat.card (L ⧸ pPrimeCore 2 L) = 1 := by
          have := Subgroup.index_top (G := L)
          rw [← h] at this
          exact this
        rw [hcardB] at h1
        have h25 : 25 ≤ (p' ^ f') ^ 2 := by nlinarith
        have : 5 * 24 ≤ p' ^ f' * ((p' ^ f') ^ 2 - 1) :=
          Nat.mul_le_mul h5 (by omega)
        omega
    · intro z hz
      have hz' : (QuotientGroup.mk z : L ⧸ pPrimeCore 2 L) ∈ center (L ⧸ pPrimeCore 2 L) := by
        rw [mem_center_iff]
        intro g
        obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (mem_center_iff.mp hz) g']
      exact (QuotientGroup.eq_one_iff z).mp
        (OddSelector.Catalog7L3.eq_one_of_mem_center_psl2 hQ3 eB hz')
  have hZodd : Odd (Nat.card (center L)) := by
    rw [← hcore]
    have h := (pPrimeCore_coprime_card (p := 2) (G := L))
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two] at h
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)
  let eZ : L ⧸ center L ≃* L ⧸ pPrimeCore 2 L := QuotientGroup.quotientMulEquivOfEq hcore.symm
  have hLmZ : Blueprint.LieModel (L ⧸ center L) .PSL 2 p' f' :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm hLm
  have hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p' f' :=
    LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hLmZ
  have hLC : CFSG.Assembly.IsComponentOf L C := by
    have hsub : (L.subgroupOf C).IsSubnormal := hL.choose_spec.2.1
    have hq : CFSG.IsQuasisimple (L.subgroupOf C) :=
      (isQuasisimple_congr (subgroupOfEquivOfLe hLx)).mpr hLq
    exact (isComponentOf_iff_isComponent_subgroupOf hLx).mpr ⟨hq, hsub⟩
  obtain ⟨k₀, _, _, hk₀, h3, ⟨eL⟩⟩ : ∃ (k₀ : Type) (_ : Field k₀) (_ : Finite k₀),
      Nat.card k₀ = p ^ f ∧ 3 < Nat.card k₀ ∧ Nonempty (L ≃* GorensteinWalter.PSL2 k₀) := by
    rcases hm with hm | hm
    · obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ :=
        LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hm
      let φ' : ↥(generalizedFitting H) ≃* LinearFlag.projectiveSL 3 K :=
        φ.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
          (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))
      obtain ⟨h3, hiso⟩ := OddSelector.Catalog7L3.psl3_component_iso hC hx hLF hLC hZodd hp'2
        hsrc hp hp2 hf hK φ'
      exact ⟨K, inferInstance, inferInstance, hK, h3, hiso⟩
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
        LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hm
      have hWnab : ∃ u v : ↥(generalizedFitting H), u * v ≠ v * u := by
        obtain ⟨a, b, hab⟩ := hLq.2.2
        obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
        refine ⟨⟨a', hLF a'.2⟩, ⟨b', hLF b'.2⟩, fun h => hab ?_⟩
        have h1 : a' * b' = b' * a' := by
          apply Subtype.ext
          have h2 := congrArg (fun w : ↥(generalizedFitting H) => (w : H)) h
          simpa using h2
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h1]
      have hLCW : CFSG.Assembly.IsComponentOf L (generalizedFitting H ⊓ C) :=
        isComponentOf_of_le hLC (le_inf hLF hLC.1) inf_le_right
      exact OddClassSelector.Catalog7L3.psu3_component_iso hsimp hWnab hC hx hLCW
        (Or.inl ⟨p', f', hp', hp'2, hf', h5, hLmZ, hZodd⟩) hp hp2 hf hK rfl e
  have hZL : center L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact (mem_bot).mpr (OddSelector.Catalog7L3.eq_one_of_mem_center_psl2 h3 eL hz)
  have hcardL : Nat.card L = p' ^ f' * ((p' ^ f') ^ 2 - 1) / 2 := by
    have h1 := (pPrimeCore 2 L).card_eq_card_quotient_mul_card_subgroup
    have h2 : Nat.card (pPrimeCore 2 L) = 1 := by rw [hcore, hZL, card_bot]
    rw [h2, mul_one, hcardB] at h1
    exact h1
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hcardL' : Nat.card L = p ^ f * ((p ^ f) ^ 2 - 1) / 2 := by
    rw [Nat.card_congr eL.toEquiv, card_psl2_of_odd hodd hk₀]
  have hQ : p' ^ f' = p ^ f := by
    have h1 := hcardL.symm.trans hcardL'
    have h2 : p' ^ f' * ((p' ^ f') ^ 2 - 1) = p ^ f * ((p ^ f) ^ 2 - 1) := by
      have ha := two_dvd_mul_sq_sub (p' ^ f')
      have hb := two_dvd_mul_sq_sub (p ^ f)
      omega
    exact eq_of_mul_sq_sub_eq (Nat.one_le_pow _ _ hp'.pos) (Nat.one_le_pow _ _ hp.pos) h2
  have hpp : p' = p := by
    have h1 : p' ∣ p ^ f := hQ ▸ dvd_pow_self p' (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp' hp).mp (hp'.dvd_of_dvd_pow h1)
  subst hpp
  exact ⟨rfl, Nat.pow_right_injective hp'.two_le hQ⟩

end Catalog7Std

end CFSG.ComponentClassification.GSThmB
