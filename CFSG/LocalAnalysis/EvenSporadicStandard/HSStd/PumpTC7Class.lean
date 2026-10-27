module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYLin

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpTC7

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.EvenSporadicStandard.HSStd.FiveY

variable {n : ℕ}

theorem mem_class_iff {gs : Array (Array ℕ)} {ps : List ℕ}
    (hgs : ∀ k < gs.size, validA n gs[k]! = true) {x : Array ℕ} {c : ArrCert}
    (hc : arrCertOK (fun k a => conjA n gs[k]! a) gs.size (validA n) (keyA n ps) x c = true)
    (y : Equiv.Perm (Fin n)) :
    (∃ g ∈ Subgroup.closure (permsA n gs), y = g * permOfArr n x * g⁻¹) ↔
      ∃ i < c.pts.size, permOfArr n c.pts[i]! = y := by
  classical
  set R := Subgroup.closure (permsA n gs) with hR
  set X := permOfArr n x with hX
  let gens' : ℕ → ConjAct (Equiv.Perm (Fin n)) := fun k =>
    ConjAct.toConjAct (permOfArr n gs[k]!)
  have hact : ∀ k < gs.size, ∀ a, validA n a = true →
      permOfArr n (conjA n gs[k]! a) = gens' k • permOfArr n a := by
    intro k hk a ha
    rw [ConjAct.smul_def]
    exact permOfArr_eq_of_rep (rep_conjA (hgs k hk) (rep_of_validA ha))
  have horb := orbit_of_arrCertOK (G := ConjAct (Equiv.Perm (Fin n)))
    (X := Equiv.Perm (Fin n)) (dec := permOfArr n) (gens := gens') hc hact
  set H : Subgroup (ConjAct (Equiv.Perm (Fin n))) :=
    Subgroup.closure (gens' '' {k | k < gs.size}) with hH
  have hHR : H = R.map (ConjAct.toConjAct : Equiv.Perm (Fin n) ≃* _).toMonoidHom := by
    rw [hH, hR, MonoidHom.map_closure]
    congr 1
    ext g
    simp only [Set.mem_image, permsA, Set.mem_ofPred_eq, gens']
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨permOfArr n gs[k]!, ⟨k, hk, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, rfl⟩
  have hHmem : ∀ g : ConjAct (Equiv.Perm (Fin n)), g ∈ H ↔ ConjAct.ofConjAct g ∈ R := by
    intro g
    rw [hHR, Subgroup.mem_map_equiv]
    rfl
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hmem : g * X * g⁻¹ ∈ MulAction.orbit H X :=
      ⟨⟨ConjAct.toConjAct g, (hHmem _).2 hg⟩, by simp [ConjAct.smul_def]⟩
    rw [horb] at hmem
    obtain ⟨i, hi, e⟩ := hmem
    exact ⟨i, hi, e⟩
  · rintro ⟨i, hi, rfl⟩
    have hmem : permOfArr n c.pts[i]! ∈ MulAction.orbit H X := by
      rw [horb]
      exact ⟨i, hi, rfl⟩
    obtain ⟨⟨h, hh⟩, e⟩ := hmem
    exact ⟨ConjAct.ofConjAct h, (hHmem h).1 hh, by rw [← e]; simp [ConjAct.smul_def]⟩

end CFSG.EvenSporadicStandard.HSStd.PumpTC7
