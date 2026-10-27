module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLCen
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLS4
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7EGen
import CFSG.ClassicalInvolution.AschTight.Sec7L714F

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp

section EZ

variable {G : Type} [Group G] [Finite G]

theorem exists_psi_M {Ω : Set (Subgroup G)} {W E : Subgroup G}
    (φ : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)) (hME : MGrp Ω W ≤ E)
    (hOEn : E ≤ Subgroup.normalizer (oddCoreOf E : Set G)) :
    ∃ ψ : ↥(MGrp Ω W) →* Equiv.Perm (Fin 4), Function.Surjective ψ ∧
      (∀ m : ↥(MGrp Ω W), (m : G) ∈ oddCoreOf E → ψ m = 1) ∧
      (∀ m : ↥(MGrp Ω W), ψ m = 1 → (m : G) ∈ W ⊔ OCW W) := by
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
  refine ⟨φ.toMonoidHom.comp ψ, φ.surjective.comp hψs, fun m hm => hB m hm, fun m hm => ?_⟩
  exact hψker m (φ.map_eq_one_iff.mp hm)

theorem perm4_central_eq_one (σ : Equiv.Perm (Fin 4)) (h : ∀ τ : Equiv.Perm (Fin 4), σ * τ = τ * σ) :
    σ = 1 := by
  revert σ
  decide +kernel

theorem odd_orderOf_of_mem_oddCoreOf {H : Subgroup G} {x : G} (hx : x ∈ oddCoreOf H) :
    Odd (orderOf x) :=
  (odd_natCard_oddCoreOf H).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hx)

theorem eq_one_of_commute_odd {W : Subgroup G} (hW2 : IsPGroup 2 W) {a b : G} (ha : a ∈ W)
    (hab : Commute a b) (hb : Odd (orderOf b)) (hodd : Odd (orderOf (a * b))) : a = 1 := by
  obtain ⟨k, hk⟩ := hW2 ⟨a, ha⟩
  have hk' : a ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  have hco : (orderOf a).Coprime (orderOf b) := by
    rw [hj]
    exact Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hb)
  rw [hab.orderOf_mul_eq_mul_orderOf_of_coprime hco] at hodd
  have h2 : Odd (2 ^ j) := hj ▸ (Nat.odd_mul.mp hodd).1
  have hj0 : j = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr h2) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.mp hj

theorem omegaOneCenter_of_fix {Ω : Set (Subgroup G)} {W E : Subgroup G} {e : G} (hW2 : IsPGroup 2 W)
    (φ : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)) (hME : MGrp Ω W ≤ E)
    (hE : E ≤ oddCoreOf E ⊔ (E ⊓ Subgroup.normalizer (W : Set G)))
    (hEM : E ≤ oddCoreOf E ⊔ MGrp Ω W) (heE : e ∈ E)
    (hfix : ∀ w ∈ W, (∀ y ∈ MGrp Ω W, y * w = w * y) → w = 1 ∨ w = e) :
    OmegaOneCenter E e := by
  intro z hz hzc _
  have hOEn : E ≤ Subgroup.normalizer (oddCoreOf E : Set G) :=
    Sec7.le_normalizer_oddCoreOf _
  have hOn : ∀ x ∈ E, ∀ o ∈ oddCoreOf E, x * o * x⁻¹ ∈ oddCoreOf E := fun x hx o ho =>
    (Subgroup.mem_normalizer_iff.mp (hOEn hx) o).mp ho
  obtain ⟨ψ, hψs, hψO, hψker⟩ := exists_psi_M φ hME hOEn
  have hzmem : z ∈ ((MGrp Ω W ⊔ oddCoreOf E : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hEM hz
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (MGrp Ω W) (oddCoreOf E)
    (hME.trans hOEn)] at hzmem
  obtain ⟨m, hm, o, ho, rfl⟩ := hzmem
  have hmE : m ∈ E := hME hm
  have hcomm_m : ∀ y ∈ E, m * y * m⁻¹ * y⁻¹ ∈ oddCoreOf E := by
    intro y hy
    have h1 := hzc y hy
    have h2 : y * o * y⁻¹ ∈ oddCoreOf E := hOn y hy o ho
    have h3 : (m * o) * (o⁻¹ * (y * o * y⁻¹)) * (m * o)⁻¹ ∈ oddCoreOf E :=
      hOn _ hz _ ((oddCoreOf E).mul_mem ((oddCoreOf E).inv_mem ho) h2)
    have := (oddCoreOf E).mul_mem h3 h1
    convert this using 1
    group
  have hψc : ∀ y : ↥(MGrp Ω W), ψ ⟨m, hm⟩ * ψ y = ψ y * ψ ⟨m, hm⟩ := by
    intro y
    have h1 : ((⟨m, hm⟩ * y * ⟨m, hm⟩⁻¹ * y⁻¹ : ↥(MGrp Ω W)) : G) ∈ oddCoreOf E := by
      have := hcomm_m (y : G) (hME y.2)
      simpa using this
    have h2 := hψO _ h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h2)
  have hψ1 : ψ ⟨m, hm⟩ = 1 := perm4_central_eq_one _ fun τ => by
    obtain ⟨y, rfl⟩ := hψs τ
    exact hψc y
  obtain ⟨w, hw, c, hc, hwc⟩ : ∃ w ∈ W, ∃ c ∈ OCW W, w * c = m :=
    Asc77.Thompson.mem_sup_OCW_iff.mp (hψker ⟨m, hm⟩ hψ1)
  have hwcomm : ∀ y ∈ MGrp Ω W, y * w = w * y := by
    intro y hy
    have hyN : y ∈ Subgroup.normalizer (W : Set G) := Asc77.Thompson.MGrp_le_normalizer Ω W hy
    have hyNc : y ∈ Subgroup.normalizer (OCW W : Set G) :=
      Asc77.Thompson.normalizer_le_normalizer_OCW W hyN
    have hc' : c * (y * c⁻¹ * y⁻¹) ∈ OCW W :=
      (OCW W).mul_mem hc ((Subgroup.mem_normalizer_iff.mp hyNc c⁻¹).mp ((OCW W).inv_mem hc))
    have hw'' : y * w⁻¹ * y⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hyN w⁻¹).mp (W.inv_mem hw)
    have hcw : Commute (c * (y * c⁻¹ * y⁻¹)) (y * w⁻¹ * y⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp (Asc77.Thompson.OCW_le_centralizer W hc') _ hw'').symm
    have hcm := hcomm_m y (hME hy)
    rw [← hwc] at hcm
    have hexp : w * c * y * (w * c)⁻¹ * y⁻¹ =
        (w * (y * w⁻¹ * y⁻¹)) * (c * (y * c⁻¹ * y⁻¹)) := by
      have e1 : w * c * y * (w * c)⁻¹ * y⁻¹ =
          w * ((c * (y * c⁻¹ * y⁻¹)) * (y * w⁻¹ * y⁻¹)) := by group
      rw [e1, hcw.eq]
      group
    rw [hexp] at hcm
    have hcom2 : Commute (w * (y * w⁻¹ * y⁻¹)) (c * (y * c⁻¹ * y⁻¹)) := by
      have : Commute w (c * (y * c⁻¹ * y⁻¹)) :=
        Subgroup.mem_centralizer_iff.mp (Asc77.Thompson.OCW_le_centralizer W hc') w hw
      exact this.mul_left hcw.symm
    have ha1 : w * (y * w⁻¹ * y⁻¹) = 1 :=
      eq_one_of_commute_odd hW2 (W.mul_mem hw hw'') hcom2
        (odd_orderOf_of_mem_oddCoreOf (H := Subgroup.centralizer (W : Set G)) hc')
        (odd_orderOf_of_mem_oddCoreOf hcm)
    have h3 : y * w⁻¹ * y⁻¹ = w⁻¹ := eq_inv_of_mul_eq_one_right ha1
    have h4 : y * w * y⁻¹ = w := by
      have := congrArg (fun x => x⁻¹) h3
      simpa [mul_assoc] using this
    exact mul_inv_eq_iff_eq_mul.mp h4
  have hw1 := hfix w hw hwcomm
  have hwE : w ∈ E := by
    rcases hw1 with h | h
    · rw [h]; exact E.one_mem
    · rw [h]; exact heE
  have hcE : c ∈ E := by
    have : c = w⁻¹ * m := by rw [← hwc]; group
    rw [this]
    exact E.mul_mem (E.inv_mem hwE) hmE
  have hcO : c ∈ oddCoreOf E := F7G.inf_OCW_le hE ⟨hcE, hc⟩
  rcases hw1 with h | h
  · left
    rw [← hwc, h, one_mul]
    exact (oddCoreOf E).mul_mem hcO ho
  · right
    have : e⁻¹ * (m * o) = c * o := by rw [← hwc, h]; group
    rw [this]
    exact (oddCoreOf E).mul_mem hcO ho

end EZ

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
