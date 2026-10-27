module

import CFSG.ClassicalInvolution.AschTight.Sec7L714F
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LL2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLAbs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

section Cen

variable {G : Type} [Group G] [Finite G]

@[expose] def OmegaOneCenter (E : Subgroup G) (f : G) : Prop :=
  ∀ z ∈ E, (∀ y ∈ E, z * y * z⁻¹ * y⁻¹ ∈ oddCoreOf E) → z * z ∈ oddCoreOf E →
    z ∈ oddCoreOf E ∨ f⁻¹ * z ∈ oddCoreOf E

theorem OmegaOneCenter.conj {E : Subgroup G} {f : G} (h : OmegaOneCenter E f) (m : G) :
    OmegaOneCenter (conjSub m E) (m * f * m⁻¹) := by
  intro z hz hc hsq
  rw [mem_conjSub_iff] at hz
  have hO : ∀ w : G, w ∈ oddCoreOf (conjSub m E) ↔ m⁻¹ * w * m ∈ oddCoreOf E := fun w => by
    rw [Asc77.Thompson.oddCoreOf_conjSub_eq, mem_conjSub_iff]
  have hc' : ∀ y ∈ E, (m⁻¹ * z * m) * y * (m⁻¹ * z * m)⁻¹ * y⁻¹ ∈ oddCoreOf E := by
    intro y hy
    have := (hO _).mp (hc (m * y * m⁻¹) (conj_mem_conjSub hy))
    convert this using 1
    group
  have hsq' : (m⁻¹ * z * m) * (m⁻¹ * z * m) ∈ oddCoreOf E := by
    have := (hO _).mp hsq
    convert this using 1
    group
  rcases h _ hz hc' hsq' with h1 | h1
  · left
    exact (hO _).mpr h1
  · right
    refine (hO _).mpr ?_
    convert h1 using 1
    group

theorem HasS3Quot.of_mulEquiv' {E E' : Type} [Group E] [Group E'] (e : E ≃* E') (h : HasS3Quot E) :
    HasS3Quot E' := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨π.comp e.symm.toMonoidHom, hπ.comp e.symm.surjective⟩

theorem Ea_eq_top_of_central {Φ : Set (Subgroup G)} (hgen : omegaGen Φ = ⊤) {a : G}
    (ha : a ∈ Subgroup.center G) : Ea Φ a = ⊤ := by
  rw [eq_top_iff, ← hgen]
  refine iSup₂_le fun L hL => ?_
  exact le_Ea hL fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    ((Subgroup.mem_center_iff.mp ha x))

theorem hasS3Quot_of_central {Φ : Set (Subgroup G)} (hgen : omegaGen Φ = ⊤) {a : G}
    (ha : a ∈ Subgroup.center G) (h : HasS3Quot ↥(Ea Φ a)) : HasS3Quot G := by
  rw [Ea_eq_top_of_central hgen ha] at h
  exact HasS3Quot.of_mulEquiv' Subgroup.topEquiv h

theorem eq_one_of_sq_eq_one_of_odd {H : Type} [Group H] {d : H} (hd2 : d * d = 1)
    (hodd : ∃ k : ℕ, d ^ (2 * k + 1) = 1) : d = 1 := by
  obtain ⟨k, hk⟩ := hodd
  have h2 : d ^ 2 = 1 := by rw [pow_two]; exact hd2
  have : d ^ (2 * k + 1) = d := by rw [pow_succ, pow_mul, h2, one_pow, one_mul]
  rw [← this]
  exact hk

theorem exists_odd_pow_eq_one {E : Subgroup G} {x : G} (hx : x ∈ oddCoreOf E) :
    ∃ k : ℕ, x ^ (2 * k + 1) = 1 := by
  have h1 : orderOf (⟨x, hx⟩ : ↥(oddCoreOf E)) ∣ Nat.card ↥(oddCoreOf E) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  obtain ⟨k, hk⟩ := (oddCoreOf_odd_natCard E).of_dvd_nat h1
  exact ⟨k, by rw [← hk]; exact pow_orderOf_eq_one x⟩

theorem inf_oddCoreOf_le_of_cover {X E H : Subgroup G} (hHE : H ≤ E) (hHX : H ≤ X)
    (hcov : E ≤ oddCoreOf E ⊔ H) : oddCoreOf X ⊓ H ≤ oddCoreOf E := by
  refine F7L.le_oddCoreOf_of_cover hHE hcov inf_le_right ?_ ?_
  · intro g hg
    exact mem_normalizer_inf' (Sec7.le_normalizer_oddCoreOf X (hHX hg)) (Subgroup.le_normalizer hg)
  · exact (odd_natCard_oddCoreOf X).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

theorem comm_mem_oddCore_of_central {X : Subgroup G} {y h : ↥X}
    (hy : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) y ∈ Subgroup.center (SecQuot X)) :
    y * h * y⁻¹ * h⁻¹ ∈ classicalInvolutionOddCore ↥X := by
  have hc := Subgroup.mem_center_iff.mp hy (QuotientGroup.mk' (classicalInvolutionOddCore ↥X) h)
  have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) (y * h * y⁻¹ * h⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    have := commutatorElement_eq_one_iff_mul_comm.mpr hc.symm
    rw [commutatorElement_def] at this
    exact this
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem central_inf_eq_bot {X E : Subgroup G} {f : G} (hfX : f ∈ X) (hf2 : f * f = 1)
    (hcovV : E ≤ oddCoreOf E ⊔ (E ⊓ X)) (hY3 : OmegaOneCenter E f)
    (hcen : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨f, hfX⟩ ∈
      Subgroup.center (SecQuot X) → False) :
    secImage X (E ⊓ X) ⊓ Subgroup.center (SecQuot X) = ⊥ := by
  set N := classicalInvolutionOddCore ↥X with hN
  have hOEn : E ≤ Subgroup.normalizer (oddCoreOf E : Set G) := Sec7.le_normalizer_oddCoreOf E
  have hinfN : oddCoreOf X ⊓ (E ⊓ X) ≤ oddCoreOf E :=
    inf_oddCoreOf_le_of_cover inf_le_left inf_le_right hcovV
  have hinv : ∀ d ∈ secImage X (E ⊓ X), d ∈ Subgroup.center (SecQuot X) → d * d = 1 → d = 1 := by
    intro d hdE hdZ hd2
    obtain ⟨y, hy, rfl⟩ := hdE
    have hyEX : (y : G) ∈ E ⊓ X := Subgroup.mem_subgroupOf.mp hy
    have hxE : (y : G) ∈ E := hyEX.1
    have hA : ∀ y' ∈ E, (y : G) * y' * (y : G)⁻¹ * y'⁻¹ ∈ oddCoreOf E := by
      intro y' hy'
      have hy'' : y' ∈ ((oddCoreOf E ⊔ (E ⊓ X) : Subgroup G) : Set G) := hcovV hy'
      rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (inf_le_left.trans hOEn)] at hy''
      obtain ⟨o, ho, h, hh, rfl⟩ := hy''
      have hcomm : (y : G) * h * (y : G)⁻¹ * h⁻¹ ∈ oddCoreOf E := by
        have h1 := comm_mem_oddCore_of_central (h := ⟨h, hh.2⟩) hdZ
        have h2 : (y : G) * h * (y : G)⁻¹ * h⁻¹ ∈ oddCoreOf X :=
          mem_oddCoreOf_iff.mpr ⟨((y * ⟨h, hh.2⟩ * y⁻¹ * ⟨h, hh.2⟩⁻¹ : ↥X)).2, h1⟩
        have h3 : (y : G) * h * (y : G)⁻¹ * h⁻¹ ∈ E ⊓ X :=
          (E ⊓ X).mul_mem ((E ⊓ X).mul_mem ((E ⊓ X).mul_mem hyEX hh) ((E ⊓ X).inv_mem hyEX))
            ((E ⊓ X).inv_mem hh)
        exact hinfN ⟨h2, h3⟩
      have hxo : (y : G) * o * (y : G)⁻¹ ∈ oddCoreOf E :=
        (Subgroup.mem_normalizer_iff.mp (hOEn hxE) o).mp ho
      have e : (y : G) * (o * h) * (y : G)⁻¹ * (o * h)⁻¹ =
          ((y : G) * o * (y : G)⁻¹) * ((y : G) * h * (y : G)⁻¹ * h⁻¹) * o⁻¹ := by group
      rw [e]
      exact (oddCoreOf E).mul_mem ((oddCoreOf E).mul_mem hxo hcomm) ((oddCoreOf E).inv_mem ho)
    have hB : (y : G) * (y : G) ∈ oddCoreOf E := by
      have h1 : QuotientGroup.mk' N (y * y) = 1 := by rw [map_mul]; exact hd2
      have h2 : (y : G) * (y : G) ∈ oddCoreOf X :=
        mem_oddCoreOf_iff.mpr ⟨(y * y : ↥X).2, (QuotientGroup.eq_one_iff _).mp h1⟩
      exact hinfN ⟨h2, (E ⊓ X).mul_mem hyEX hyEX⟩
    rcases hY3 (y : G) hxE hA hB with h1 | h1
    ·
      obtain ⟨k, hk⟩ := exists_odd_pow_eq_one h1
      refine eq_one_of_sq_eq_one_of_odd hd2 ⟨k, ?_⟩
      have : y ^ (2 * k + 1) = 1 := Subtype.ext (by simpa using hk)
      rw [← map_pow, this, map_one]
    ·
      exfalso
      apply hcen
      set fy : ↥X := ⟨f, hfX⟩ with hfy
      set o : ↥X := fy⁻¹ * y with ho
      have hoO : ((o : ↥X) : G) ∈ oddCoreOf E := by
        have : ((o : ↥X) : G) = f⁻¹ * (y : G) := rfl
        rw [this]; exact h1
      obtain ⟨k, hk⟩ := exists_odd_pow_eq_one hoO
      have hodd : (QuotientGroup.mk' N o) ^ (2 * k + 1) = 1 := by
        have : o ^ (2 * k + 1) = 1 := Subtype.ext (by simpa using hk)
        rw [← map_pow, this, map_one]
      have hfb2 : QuotientGroup.mk' N fy * QuotientGroup.mk' N fy = 1 := by
        rw [← map_mul]
        have : fy * fy = 1 := Subtype.ext hf2
        rw [this, map_one]
      have hmo : QuotientGroup.mk' N o = (QuotientGroup.mk' N fy)⁻¹ * QuotientGroup.mk' N y := by
        rw [ho, map_mul, map_inv]
      have hsq : QuotientGroup.mk' N o * QuotientGroup.mk' N o = 1 := by
        rw [hmo]
        have hcd := Subgroup.mem_center_iff.mp hdZ ((QuotientGroup.mk' N fy)⁻¹)
        calc (QuotientGroup.mk' N fy)⁻¹ * QuotientGroup.mk' N y *
              ((QuotientGroup.mk' N fy)⁻¹ * QuotientGroup.mk' N y)
            = (QuotientGroup.mk' N fy)⁻¹ * (QuotientGroup.mk' N y * (QuotientGroup.mk' N fy)⁻¹) *
                QuotientGroup.mk' N y := by group
          _ = (QuotientGroup.mk' N fy)⁻¹ * ((QuotientGroup.mk' N fy)⁻¹ * QuotientGroup.mk' N y) *
                QuotientGroup.mk' N y := by rw [← hcd]
          _ = ((QuotientGroup.mk' N fy) * (QuotientGroup.mk' N fy))⁻¹ *
                (QuotientGroup.mk' N y * QuotientGroup.mk' N y) := by
              have hcd2 := Subgroup.mem_center_iff.mp hdZ (QuotientGroup.mk' N y)
              group
          _ = 1 := by rw [hfb2, hd2]; simp
      have ho1 : QuotientGroup.mk' N o = 1 := eq_one_of_sq_eq_one_of_odd hsq ⟨k, hodd⟩
      have hdf : QuotientGroup.mk' N y = QuotientGroup.mk' N fy := by
        have := hmo ▸ ho1
        exact (inv_mul_eq_one.mp this).symm
      rw [← hdf]
      exact hdZ
  rw [eq_bot_iff]
  rintro c ⟨hcE, hcZ⟩
  rw [Subgroup.mem_bot]
  have hO : classicalInvolutionOddCore (SecQuot X) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥X
  obtain ⟨k, hk⟩ := center_pow_two hO hcZ
  have key : ∀ k : ℕ, ∀ c : SecQuot X, c ∈ secImage X (E ⊓ X) →
      c ∈ Subgroup.center (SecQuot X) → c ^ (2 ^ k) = 1 → c = 1 := by
    intro k
    induction k with
    | zero => intro c _ _ h; simpa using h
    | succ k ih =>
      intro c hcE hcZ h
      have hc2E : c * c ∈ secImage X (E ⊓ X) := Subgroup.mul_mem _ hcE hcE
      have hc2Z : c * c ∈ Subgroup.center (SecQuot X) := Subgroup.mul_mem _ hcZ hcZ
      have h2 : (c * c) ^ (2 ^ k) = 1 := by rw [← pow_two, ← pow_mul, ← pow_succ']; exact h
      exact hinv c hcE hcZ (ih (c * c) hc2E hc2Z h2)
  exact key k c hcE hcZ hk

end Cen

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
