module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Sig5

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523

open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
  CFSG.Sporadic.Schreier Subgroup

theorem eq_one_of_fixes_E0
    (α : MulAut GJ) (n : ℕ)
    (hα : α ^ (2 ^ n) = 1) (hfix : ∀ g ∈ E0, α g = g) : α = 1 := by
  set r : R := rAutEquiv.symm α with hrdef
  have hr : rAutEquiv r = α := rAutEquiv.apply_symm_apply α
  have hrg : ∀ g : GJ, (r : Equiv.Perm (Fin 315)) * g.1 * (r : Equiv.Perm (Fin 315))⁻¹ = (α g).1 := by
    intro g
    rw [← hr, rAutEquiv_apply]
    rfl
  have hrpow : r ^ (2 ^ n) = 1 := rAutEquiv.injective (by rw [map_pow, hr, hα, map_one])
  have hrpow' : (r : Equiv.Perm (Fin 315)) ^ (2 ^ n) = 1 := by
    have := congrArg (fun x : R => (x : Equiv.Perm (Fin 315))) hrpow
    simpa using this
  have hcomm : ∀ g ∈ E0, (r : Equiv.Perm (Fin 315)) * g.1 = g.1 * (r : Equiv.Perm (Fin 315)) := by
    intro g hg
    have := hrg g
    rw [hfix g hg] at this
    calc (r : Equiv.Perm (Fin 315)) * g.1
        = ((r : Equiv.Perm (Fin 315)) * g.1 * (r : Equiv.Perm (Fin 315))⁻¹) *
            (r : Equiv.Perm (Fin 315)) := by group
      _ = g.1 * (r : Equiv.Perm (Fin 315)) := by rw [this]
  have key : ∀ q : GJ, (∀ g ∈ E0, q * g = g * q) → q ^ (2 ^ n) = 1 → q = 1 := by
    intro q hq hq2
    have hqc : q ∈ centralizer ((E0 : Subgroup GJ) : Set GJ) :=
      mem_centralizer_iff.2 fun g hg => (hq g hg).symm
    rw [centralizer_E0] at hqc
    have h3 : q ^ 3 = 1 := cube_of_mem_P3 (E0_le_P3 hqc)
    have hd : orderOf q ∣ Nat.gcd 3 (2 ^ n) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hq2)
    have hg : Nat.gcd 3 (2 ^ n) = 1 := Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)
    rw [hg] at hd
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)
  rcases (mem_R_iff (r : Equiv.Perm (Fin 315))).1 r.2 with hP | hPu
  · have hq1 : (⟨(r : Equiv.Perm (Fin 315)), hP⟩ : GJ) = 1 :=
      key _ (fun g hg => Subtype.ext (hcomm g hg)) (Subtype.ext (by simpa using hrpow'))
    have : r = 1 := Subtype.ext (by have := congrArg Subtype.val hq1; simpa using this)
    rw [← hr, this, map_one]
  · exfalso
    have hu : permU⁻¹ = permU := permU_inv
    have huu : permU * permU = 1 := permU_mul_self
    set rr : Equiv.Perm (Fin 315) := (r : Equiv.Perm (Fin 315)) with hrr
    have hconj : permU * (rr * permU) * permU⁻¹ = permU * rr := by group
    have hrsq : rr * rr ∈ P := by
      have h1 := permU_conj_mem _ hPu
      rw [hconj] at h1
      have e : rr * rr = (rr * permU) * (permU * rr) := by
        calc rr * rr = rr * (permU * permU) * rr := by rw [huu, mul_one]
          _ = (rr * permU) * (permU * rr) := by group
      rw [e]
      exact P.mul_mem hPu h1
    have hq1 : (⟨rr * rr, hrsq⟩ : GJ) = 1 := by
      refine key _ (fun g hg => Subtype.ext ?_) (Subtype.ext ?_)
      · show rr * rr * g.1 = g.1 * (rr * rr)
        rw [mul_assoc, hcomm g hg, ← mul_assoc, hcomm g hg, mul_assoc]
      · show (rr * rr) ^ (2 ^ n) = 1
        rw [← pow_two, ← pow_mul, mul_comm, pow_mul, hrpow', one_pow]
    have hrr1 : rr * rr = 1 := by
      have := congrArg Subtype.val hq1
      simpa using this
    have hrne : rr ≠ 1 := by
      intro h
      rw [h, one_mul] at hPu
      exact permU_not_mem hPu
    have hord : orderOf rr = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact hrr1) hrne
    have hleft : permU⁻¹ * rr ∈ P := by
      have h1 := permU_conj_mem _ hPu
      rw [hconj] at h1
      rw [hu]
      exact h1
    obtain ⟨c, hc, hrc⟩ := outer_classes.1 rr hleft hord
    set E1 : Subgroup (Equiv.Perm (Fin 315)) :=
      (E0.map P.subtype).map (MulAut.conj c⁻¹).toMonoidHom with hE1
    have hE1card : Nat.card E1 = 9 := by
      rw [hE1, Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective P), card_E0]
      norm_num
    have hle : E1 ≤ centralizerIn P permU := by
      rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      rw [centralizerIn, Subgroup.mem_inf]
      refine ⟨?_, ?_⟩
      · have := P.mul_mem (P.mul_mem (P.inv_mem hc) g.2) (P.inv_mem (P.inv_mem hc))
        simpa [MulAut.conj_apply] using this
      · rw [mem_centralizer_singleton_iff]
        have h := hcomm g hg
        rw [hrc] at h
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_subtype]
        calc c⁻¹ * g.1 * c * permU = c⁻¹ * (g.1 * (c * permU * c⁻¹)) * c := by group
          _ = c⁻¹ * ((c * permU * c⁻¹) * g.1) * c := by rw [h]
          _ = permU * (c⁻¹ * g.1 * c) := by group
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hE1card, outer_classes.2.2, (centOuter_facts).2.1] at hdvd
    omega

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523
