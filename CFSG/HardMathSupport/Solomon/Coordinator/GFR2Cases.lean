module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2Defs
public import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimKProofTriple
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
open scoped commutatorElement

theorem gfr2_central_of_cover {Y : Type} [Group Y] [Finite Y] {J₁ : Subgroup Y}
    (hZ : Nat.card (Subgroup.center Y) = 3) (hZJ : Subgroup.center Y ≤ J₁)
    (hbar : Nat.card (Subgroup.center (barOf 3 J₁)) = 3) {y : Y} (hy3 : y ^ 3 = 1) (hyJ : y ∈ J₁)
    (hyc : ∀ j ∈ J₁, y * j = j * y) : y ∈ Subgroup.center Y := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π : ↥J₁ →* barOf 3 J₁ := QuotientGroup.mk' (GLAPPrimeCore 3 ↥J₁) with hπ
  set Zs : Subgroup ↥J₁ := (Subgroup.center Y).subgroupOf J₁ with hZs
  have hZsmap : Zs.map J₁.subtype = Subgroup.center Y := by
    rw [hZs, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hZJ]
  have hZscard : Nat.card Zs = 3 := by
    rw [← hZ, ← hZsmap, Subgroup.card_map_of_injective J₁.subtype_injective]
  have hz3 : ∀ z ∈ Subgroup.center Y, z ^ 3 = 1 := by
    intro z hz
    have h := pow_card_eq_one' (G := Subgroup.center Y) (x := ⟨z, hz⟩)
    rw [hZ] at h
    exact congrArg Subtype.val h
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥J₁)) :=
    coprime_card_gLAPPrimeCore_aux 3 ↥J₁
  have hcore1 : ∀ u : ↥J₁, u ∈ GLAPPrimeCore 3 ↥J₁ → u ^ 3 = 1 → u = 1 := by
    intro u hu hu3
    have h1 : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
    have h2 : orderOf u ∣ Nat.card (GLAPPrimeCore 3 ↥J₁) := by
      have := orderOf_dvd_natCard (⟨u, hu⟩ : ↥(GLAPPrimeCore 3 ↥J₁))
      rwa [← Subgroup.orderOf_coe] at this
    have h3 : orderOf u = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    exact orderOf_eq_one_iff.1 h3
  have hinj : Function.Injective (π.comp Zs.subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨z, hz⟩ h
    have h' : π z = 1 := h
    have hzc : (z : Y) ∈ Subgroup.center Y := by
      have := (Subgroup.mem_subgroupOf).1 hz
      exact this
    have hz1 : z = 1 := by
      apply hcore1 z (QuotientGroup.eq_one_iff _ |>.1 h')
      apply Subtype.ext
      exact hz3 _ hzc
    exact Subtype.ext hz1
  have hMcard : Nat.card (Zs.map π) = 3 := by
    have : (π.comp Zs.subtype).range = Zs.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    calc Nat.card (Zs.map π) = Nat.card (π.comp Zs.subtype).range := by rw [this]
      _ = Nat.card Zs := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      _ = 3 := hZscard
  have hMle : Zs.map π ≤ Subgroup.center (barOf 3 J₁) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥J₁) w
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hzc : (z : Y) ∈ Subgroup.center Y := (Subgroup.mem_subgroupOf).1 hz
    exact Subgroup.mem_center_iff.1 hzc j
  have hMeq : Zs.map π = Subgroup.center (barOf 3 J₁) :=
    Subgroup.eq_of_le_of_card_ge hMle (by rw [hbar, hMcard])
  have hycen : π ⟨y, hyJ⟩ ∈ Subgroup.center (barOf 3 J₁) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥J₁) w
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (hyc j j.2).symm
  rw [← hMeq] at hycen
  obtain ⟨z, hz, hzy⟩ := hycen
  have hzc : (z : Y) ∈ Subgroup.center Y := (Subgroup.mem_subgroupOf).1 hz
  have hcore : z⁻¹ * ⟨y, hyJ⟩ ∈ GLAPPrimeCore 3 ↥J₁ := QuotientGroup.eq.1 hzy
  have hu3 : (z⁻¹ * ⟨y, hyJ⟩ : ↥J₁) ^ 3 = 1 := by
    apply Subtype.ext
    show ((z : Y)⁻¹ * y) ^ 3 = 1
    have hcomm : Commute ((z : Y)⁻¹) y :=
      (Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hzc) y).symm
    rw [hcomm.mul_pow, inv_pow, hz3 _ hzc, hy3]
    simp
  have hu1 := hcore1 _ hcore hu3
  have hyz : y = (z : Y) := by
    have := congrArg Subtype.val hu1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at this
    calc y = (z : Y) * ((z : Y)⁻¹ * y) := by group
      _ = (z : Y) := by rw [this, mul_one]
  rw [hyz]
  exact hzc

theorem gfr2_card_alt_six : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem gfr2_card_isHatSix {X : Type*} [Group X] (h : IsHatSix X) : Nat.card X = 1080 := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
  rw [hZ, Nat.card_congr e.toEquiv, gfr2_card_alt_six] at h1
  omega

theorem gfr2_nat_card_center_of_cases {X : Type*} [Group X] (h : IsHatON X ∨ IsHatSix X) :
    Nat.card (Subgroup.center X) = 3 := by
  rcases h with h | h
  · exact h.2.1
  · exact h.2.1

theorem gfr2_cases (hR1 : GapFinalLayerON) (hOG : UniquenessMaximal.InputONGroup)
    (hP : GapFinalPumpup) {Y : Type} [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y)
    (hKg : CFSG.Open.IsKGroup Y) (hcore : GLAPPrimeCore 3 Y = ⊥) {y : Y} (hy3 : y ^ 3 = 1)
    {J₁ : Subgroup Y} (hJ₁ : GLAPComponent 3 (Subgroup.centralizer ({y} : Set Y)) J₁)
    (hty : IsHatON (barOf 3 J₁) ∨ IsHatSix (barOf 3 J₁)) (hyJ : y ∈ J₁) :
    y ∈ Subgroup.center Y ∨ IsMJRType Y := by
  by_cases hyc : y ∈ Subgroup.center Y
  · exact Or.inl hyc
  right
  have hJ1c : ∀ j ∈ J₁, y * j = j * y := fun j hj =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hJ₁.1 hj)).symm
  set x : MulAut Y := MulAut.conj y with hx
  have hx3 : x ^ 3 = 1 := by rw [hx, ← map_pow, hy3, map_one]
  have hx1 : x ≠ 1 := fun h =>
    hyc (CFSG.RankThree.PartTwo.Sec10.Step1012ClaimKProof.conj_eq_one_iff.1 h)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hfix : Lemma510Ns.fixSub x = Subgroup.centralizer ({y} : Set Y) := by
    ext z
    rw [Lemma510Ns.mem_fixSub, Subgroup.mem_centralizer_singleton_iff, hx, MulAut.conj_apply]
    constructor
    · intro h
      calc z * y = y * z * y⁻¹ * y := by rw [h]
        _ = y * z := by group
    · intro h
      rw [← h]
      group
  have hJ₁' : GLAPComponent 3 (Lemma510Ns.fixSub x) J₁ := by rw [hfix]; exact hJ₁
  rcases hP Y hq hKg hcore x hxo J₁ hJ₁' hty with hON | hSix | hMJR
  · exfalso
    apply hyc
    have hall := (hR1 Y hON x hx3).2 J₁ hJ₁'
    exact gfr2_central_of_cover hON.2.1 hall.1 (gfr2_nat_card_center_of_cases hty) hy3 hyJ hJ1c
  · exfalso
    apply hyc
    have h1 := gfr2_card_isHatSix hSix
    have hbar : Nat.card (barOf 3 J₁) ∣ Nat.card J₁ := Subgroup.card_quotient_dvd_card _
    have hJY : Nat.card J₁ ∣ Nat.card Y := Subgroup.card_subgroup_dvd_card J₁
    have hbc := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (barOf 3 J₁))
    rw [gfr2_nat_card_center_of_cases hty] at hbc
    have hbig : Nat.card (barOf 3 J₁) = 1080 := by
      rcases hty with h | h
      · exfalso
        have h2 := (UniquenessMaximal.isSimple_card_of_isHatON hOG h).2
        rw [h2] at hbc
        have : Nat.card J₁ ∣ 1080 := h1 ▸ hJY
        have h4 := Nat.le_of_dvd (by norm_num) (hbar.trans this)
        unfold orderON at hbc
        omega
      · have h2 := gfr2_card_isHatSix h
        exact h2
    have hJeq : Nat.card J₁ = Nat.card Y := by
      have h5 : Nat.card J₁ ∣ 1080 := h1 ▸ hJY
      have h6 : 1080 ∣ Nat.card J₁ := hbig ▸ hbar
      exact (Nat.dvd_antisymm h5 h6).trans h1.symm
    have htop : J₁ = ⊤ := Subgroup.eq_top_of_card_eq J₁ hJeq
    rw [Subgroup.mem_center_iff]
    intro g
    exact (hJ1c g (htop ▸ Subgroup.mem_top g)).symm
  · exact hMJR

end CFSG.HardMathSupport.Solomon.Coordinator
