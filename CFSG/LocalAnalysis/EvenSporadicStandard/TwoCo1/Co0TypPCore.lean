module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0TypFixed
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0TypPow

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisQuot

@[expose] def permPart (R : Subgroup latticeO) : Subgroup AutPerm where
  carrier := {p | ∃ a : C, gO a * PO p ∈ R}
  one_mem' := ⟨0, by rw [gO_zero, PO_one, mul_one]; exact R.one_mem⟩
  mul_mem' := by
    rintro p q ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨b + (permC q).symm a, ?_⟩
    have e : gO b * PO q * (gO a * PO p) = gO (b + (permC q).symm a) * PO (p * q) := by
      calc gO b * PO q * (gO a * PO p) = gO b * (PO q * gO a) * PO p := by simp only [mul_assoc]
        _ = gO b * (gO ((permC q).symm a) * PO q) * PO p := by rw [PO_mul_gO]
        _ = gO b * gO ((permC q).symm a) * (PO q * PO p) := by simp only [mul_assoc]
        _ = gO (b + (permC q).symm a) * PO (p * q) := by rw [gO_add, PO_mul]
    rw [← e]
    exact R.mul_mem hb ha
  inv_mem' := by
    rintro p ⟨a, ha⟩
    refine ⟨(permC p⁻¹).symm a, ?_⟩
    convert R.inv_mem ha using 1
    rw [_root_.mul_inv_rev, gO_inv, ← PO_inv, PO_mul_gO]

theorem PO_mul_gO_mul_PO_mul_PO_inv (h p : AutPerm) (a : C) :
    PO h * (gO a * PO p) * (PO h)⁻¹ = gO ((permC h).symm a) * PO (h⁻¹ * (p * h)) := by
  rw [← PO_inv, PO_mul h⁻¹ (p * h), PO_mul p h]
  calc PO h * (gO a * PO p) * PO h⁻¹ = (PO h * gO a) * PO p * PO h⁻¹ := by simp only [mul_assoc]
    _ = gO ((permC h).symm a) * PO h * PO p * PO h⁻¹ := by rw [PO_mul_gO]
    _ = gO ((permC h).symm a) * (PO h * PO p * PO h⁻¹) := by simp only [mul_assoc]

theorem conj_gO_mem_signSub {g : latticeO} (hg : g ∈ monoSub ⊤) (x : latticeO)
    (hx : x ∈ signSub) : g * x * g⁻¹ ∈ signSub := by
  obtain ⟨a, p, -, rfl⟩ := hg
  obtain ⟨b, rfl⟩ := mem_signSub.1 hx
  refine mem_signSub.2 ⟨(permC p).symm b, ?_⟩
  rw [_root_.mul_inv_rev, gO_inv, ← PO_inv]
  calc gO a * PO p * gO b * (PO p⁻¹ * gO a)
      = gO a * (PO p * gO b * PO p⁻¹) * gO a := by simp only [mul_assoc]
    _ = gO a * gO ((permC p).symm b) * gO a := by rw [PO_inv, PO_mul_gO']
    _ = gO ((permC p).symm b) * (gO a * gO a) := by rw [gO_comm a, mul_assoc]
    _ = gO ((permC p).symm b) := by rw [gO_mul_self, mul_one]

theorem le_normalizer_signSub {H : Subgroup latticeO} (hH : H ≤ monoSub ⊤) :
    H ≤ Subgroup.normalizer (signSub : Set latticeO) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_gO_mem_signSub (hH hg) x, fun hx => ?_⟩
  have := conj_gO_mem_signSub (hH (H.inv_mem hg)) _ hx
  simpa [mul_assoc] using this

theorem isPGroup_signSub : IsPGroup 2 signSub := IsPGroup.of_card natCard_signSub

theorem finite_monoSub_stabC (d : C) : Finite (monoSub (stabC d)) := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [card_monoSub]
  have : Nat.card (stabC d) ≠ 0 := Nat.card_pos.ne'
  positivity

theorem pCoreOf_monoSub_le : CFSG.Open.pCoreOf 2 (monoSub (stabC dod₂)) ≤ signSub := by
  set H := monoSub (stabC dod₂) with hH
  set R := CFSG.Open.pCoreOf 2 H with hR
  have : Finite H := finite_monoSub_stabC dod₂
  have hRH : R ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hRp : IsPGroup 2 R := (CFSG.LieType.BorelTits.pCore_isPGroup (G := H) 2).map H.subtype
  have hRn : H ≤ Subgroup.normalizer (R : Set latticeO) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hstab : permPart R ≤ stabC dod₂ := by
    rintro p ⟨a, ha⟩
    obtain ⟨a', p', hp', e⟩ := hRH ha
    rwa [(gO_mul_PO_inj e).2]
  have hpg : IsPGroup 2 (permPart R) := by
    refine IsPGroup.iff_orderOf.2 fun p => ?_
    obtain ⟨a, ha⟩ := p.2
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.1 hRp ⟨_, ha⟩
    have h1 : (gO a * PO p.1) ^ 2 ^ m = 1 := by
      have := pow_orderOf_eq_one (⟨_, ha⟩ : R)
      rw [hm] at this
      exact congrArg Subtype.val this
    have h2 : (p.1 : AutPerm) ^ 2 ^ m = 1 := pow_eq_one_of_gO_mul_PO_pow_eq_one h1
    have h3 : orderOf p ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one (Subtype.ext h2)
    exact (Nat.dvd_prime_pow Nat.prime_two).1 h3 |>.imp fun k hk => hk.2
  have hnorm : ∀ h ∈ stabC dod₂, ∀ r ∈ permPart R, h * r * h⁻¹ ∈ permPart R := by
    rintro h hh p ⟨a, ha⟩
    have hmem : PO h⁻¹ ∈ H := PO_mem_monoSub ((stabC dod₂).inv_mem hh)
    have h1 := (Subgroup.mem_normalizer_iff.1 (hRn hmem) _).1 ha
    rw [PO_mul_gO_mul_PO_mul_PO_inv] at h1
    exact ⟨_, by simpa [mul_assoc] using h1⟩
  have htriv := stab_normal_two_trivial (permPart R) hpg hstab hnorm
  intro e he
  obtain ⟨a, p, hp, rfl⟩ := hRH he
  have : p = 1 := htriv p ⟨a, he⟩
  subst this
  exact mem_signSub.2 ⟨a, by rw [PO_one, mul_one]⟩

end CFSG.EvenSporadicStandard.TwoCo1
