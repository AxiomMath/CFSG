module

public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem card_center_pQuot_dvd_mul {p : ℕ} (hp : p.Prime) {A B C : Type} [Group A] [Group B]
    [Group C] [Finite A] [Finite B] (Φ : A →* B) (hΦ : Nat.Coprime p (Nat.card Φ.ker))
    (hZ : IsPGroup p (Subgroup.center B)) (f : A →* C) (hf : Function.Surjective f)
    (hker : ∀ x, f x = 1 → Φ x ∈ Subgroup.center B)
    (hA : CFSG.Open.IsQuasisimple (A ⧸ GLAPPrimeCore p A))
    (hZA : IsPGroup p (Subgroup.center (A ⧸ GLAPPrimeCore p A)))
    (hC : Nontrivial (C ⧸ GLAPPrimeCore p C)) :
    Nat.card (Subgroup.center (A ⧸ GLAPPrimeCore p A)) ∣
      Nat.card (Subgroup.center (C ⧸ GLAPPrimeCore p C)) * Nat.card (Subgroup.center B) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite C := Finite.of_surjective f hf
  have hgs : Function.Surjective (pQuotMapOfSurjective hp f hf) :=
    pQuotMapOfSurjective_surjective hp f hf
  set g := pQuotMapOfSurjective hp f hf with hg
  have hN : g.ker ≤ Subgroup.center (A ⧸ GLAPPrimeCore p A) :=
    ker_pQuotMapOfSurjective_le_center hp f hf hA hC
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (hZA.to_le hN)
  have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore p A)
  have e2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore p C)
  have e3 : Nat.card A = Nat.card f.ker * Nat.card C := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [MonoidHom.range_eq_top.2 hf, Subgroup.card_top] at h
    exact h.symm
  have e4 : Nat.card (A ⧸ GLAPPrimeCore p A) =
      Nat.card g.ker * Nat.card (C ⧸ GLAPPrimeCore p C) := by
    have h := Subgroup.card_ker_mul_card_range g
    rw [MonoidHom.range_eq_top.2 hgs, Subgroup.card_top] at h
    exact h.symm
  have hcpos : 0 < Nat.card (C ⧸ GLAPPrimeCore p C) := Nat.card_pos
  have key : Nat.card g.ker * Nat.card (GLAPPrimeCore p A) =
      Nat.card f.ker * Nat.card (GLAPPrimeCore p C) := by
    refine Nat.eq_of_mul_eq_mul_left hcpos ?_
    calc Nat.card (C ⧸ GLAPPrimeCore p C) * (Nat.card g.ker * Nat.card (GLAPPrimeCore p A))
        = (Nat.card g.ker * Nat.card (C ⧸ GLAPPrimeCore p C)) * Nat.card (GLAPPrimeCore p A) := by
          ring
      _ = Nat.card A := by rw [← e4, ← e1]
      _ = Nat.card f.ker * (Nat.card (C ⧸ GLAPPrimeCore p C) * Nat.card (GLAPPrimeCore p C)) := by
          rw [e3, e2]
      _ = Nat.card (C ⧸ GLAPPrimeCore p C) * (Nat.card f.ker * Nat.card (GLAPPrimeCore p C)) := by
          ring
  have hcopC : Nat.Coprime (Nat.card g.ker) (Nat.card (GLAPPrimeCore p C)) := by
    rw [hk]
    exact Nat.Coprime.pow_left k CFSG.pPrimeCore_coprime_card
  have hnκ : Nat.card g.ker ∣ Nat.card f.ker :=
    hcopC.dvd_of_dvd_mul_right (Dvd.intro _ key)
  have hκ : Nat.card f.ker ∣ Nat.card Φ.ker * Nat.card (Subgroup.center B) := by
    set Ψ : f.ker →* B := Φ.comp f.ker.subtype with hΨ
    have h1 := Subgroup.card_ker_mul_card_range Ψ
    have h2 : Nat.card Ψ.ker ∣ Nat.card Φ.ker := by
      have hle : Ψ.ker.map f.ker.subtype ≤ Φ.ker := by
        rintro _ ⟨x, hx, rfl⟩
        exact hx
      have hmap : Nat.card (Ψ.ker.map f.ker.subtype) = Nat.card Ψ.ker :=
        Subgroup.card_map_of_injective f.ker.subtype_injective
      rw [← hmap]
      exact Subgroup.card_dvd_of_le hle
    have h3 : Nat.card Ψ.range ∣ Nat.card (Subgroup.center B) := by
      refine Subgroup.card_dvd_of_le ?_
      rintro _ ⟨x, rfl⟩
      exact hker x.1 (MonoidHom.mem_ker.1 x.2)
    rw [← h1]
    exact Nat.mul_dvd_mul h2 h3
  have hnZ : Nat.card g.ker ∣ Nat.card (Subgroup.center B) := by
    have hcop : Nat.Coprime (Nat.card g.ker) (Nat.card Φ.ker) := by
      rw [hk]
      exact Nat.Coprime.pow_left k hΦ
    exact hcop.dvd_of_dvd_mul_left (hnκ.trans hκ)
  have hz : Nat.card (Subgroup.center (A ⧸ GLAPPrimeCore p A)) ∣
      Nat.card g.ker * Nat.card (Subgroup.center (C ⧸ GLAPPrimeCore p C)) := by
    set Zc := Subgroup.center (A ⧸ GLAPPrimeCore p A) with hZc
    set g' : Zc →* C ⧸ GLAPPrimeCore p C := g.comp Zc.subtype with hg'
    have h1 := Subgroup.card_ker_mul_card_range g'
    have h2 : Nat.card g'.ker ∣ Nat.card g.ker := by
      have hle : g'.ker.map Zc.subtype ≤ g.ker := by
        rintro _ ⟨x, hx, rfl⟩
        exact hx
      have hmap : Nat.card (g'.ker.map Zc.subtype) = Nat.card g'.ker :=
        Subgroup.card_map_of_injective Zc.subtype_injective
      rw [← hmap]
      exact Subgroup.card_dvd_of_le hle
    have h3 : Nat.card g'.range ∣ Nat.card (Subgroup.center (C ⧸ GLAPPrimeCore p C)) := by
      refine Subgroup.card_dvd_of_le ?_
      rintro _ ⟨x, rfl⟩
      exact Subgroup.map_center_le_center hgs ⟨x.1, x.2, rfl⟩
    rw [← h1]
    exact Nat.mul_dvd_mul h2 h3
  refine hz.trans ?_
  rw [mul_comm (Nat.card (Subgroup.center (C ⧸ GLAPPrimeCore p C)))]
  exact Nat.mul_dvd_mul_right hnZ _

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
