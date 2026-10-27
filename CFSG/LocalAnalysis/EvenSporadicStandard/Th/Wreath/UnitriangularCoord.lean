module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowBoundsAct
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.SylowCard

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup Matrix

variable {G : Type} [Group G] [Finite G] {L S A B : Subgroup G} {z : G}

private theorem matHom_eq_one_iff_mem_B (W : ThLocalIn L S A B z)
    {c : G → (Fin 4 → ZMod 2)} (hc : IsCoord A c)
    (m : S →* Matrix (Fin 4) (Fin 4) (ZMod 2)) (hm : ∀ s : S, IsRep A c s (m s)) (s : S) :
    m s = 1 ↔ (s : G) ∈ B := by
  constructor
  · intro h1
    refine (W.mem_B_iff (s : G) (W.S_le s.2)).2 fun a ha => ?_
    have h2 : c ((s : G) * a * (s : G)⁻¹) = c a := by
      rw [hm s a ha, h1, Matrix.one_mulVec]
    have h3 : (s : G) * a * (s : G)⁻¹ = a :=
      hc.inj _ (W.conj_mem_A_of_mem_S s.2 ha) _ ha h2
    calc (s : G) * a = ((s : G) * a * (s : G)⁻¹) * (s : G) := by group
      _ = a * (s : G) := by rw [h3]
  · intro hsB
    have hcomm := (W.mem_B_iff (s : G) (W.S_le s.2)).1 hsB
    refine hc.rep_unique (hm s) ?_
    intro a ha
    rw [Matrix.one_mulVec]
    have h3 : (s : G) * a * (s : G)⁻¹ = a := by
      rw [hcomm a ha]
      group
    rw [h3]

private theorem range_card_of_ker (W : ThLocalIn L S A B z) {H : Type*} [Group H]
    (ρ : S →* H) (hρ : ∀ s : S, ρ s = 1 ↔ (s : G) ∈ B) :
    Nat.card ρ.range = 2 ^ 6 := by
  have h := SylowBounds.natCard_eq_mul_natCard_inf (B := B) ρ hρ
  rw [inf_of_le_right W.B_le_S] at h
  have hpow : Nat.card ρ.range * Nat.card B = 2 ^ 6 * Nat.card B := by
    rw [← h, W.card_S, W.B_card]
    norm_num
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hpow

theorem ThLocalIn.exists_coord_unitriangular (W : ThLocalIn L S A B z) :
    ∃ c : G → (Fin 4 → ZMod 2), IsCoord A c ∧
      (∀ s ∈ S, ∃ g ∈ CFSG.Quasithin.FFC.UT 4,
        IsRep A c s (g : Matrix (Fin 4) (Fin 4) (ZMod 2))) ∧
      ∀ g ∈ CFSG.Quasithin.FFC.UT 4,
        ∃ s ∈ S, IsRep A c s (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
  classical
  obtain ⟨k, c₀, j, hkL, hkA, hkodd, hkfix, hj, hc₀mul, hc₀inj, hc₀onto, hc₀rep⟩ :=
    exists_singer_coord W.A_comm W.A_sq W.A_card W.surj
  have hc₀ : IsCoord A c₀ := ⟨hc₀mul, hc₀inj, hc₀onto⟩
  have hSA : ∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ ∈ A :=
    fun s hs a ha => W.conj_mem_A_of_mem_S hs ha
  obtain ⟨m, hm⟩ := hc₀.exists_matHom S hSA
  let μ : S →* GL (Fin 4) (ZMod 2) := m.toHomUnits
  have hμval : ∀ s : S, ((μ s : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = m s :=
    fun s => by simp [μ, MonoidHom.coe_toHomUnits]
  have hμker : ∀ s : S, μ s = 1 ↔ (s : G) ∈ B := by
    intro s
    rw [show μ s = 1 ↔ m s = 1 from by rw [← Units.val_eq_one, hμval s]]
    exact matHom_eq_one_iff_mem_B W hc₀ m hm s
  have hrangeμ : Nat.card μ.range = 2 ^ 6 := range_card_of_ker W μ hμker
  have hpμ : IsPGroup 2 μ.range := IsPGroup.of_card (n := 6) hrangeμ
  obtain ⟨h, hhUT⟩ := SylowBounds.exists_conj_le_UT hpμ
  let Hmat : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    ((h⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))
  let hmat : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    ((h : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))
  let c : G → (Fin 4 → ZMod 2) := fun a => Hmat *ᵥ c₀ a
  have hHh : Hmat * hmat = 1 := by
    simp only [Hmat, hmat]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hhH : hmat * Hmat = 1 := by
    simp only [Hmat, hmat]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hc : IsCoord A c := by
    refine ⟨?_, ?_, ?_⟩
    · intro a ha b hb
      simp only [c]
      rw [hc₀.mul a ha b hb, Matrix.mulVec_add]
    · intro a ha b hb hab
      apply hc₀.inj a ha b hb
      have h1 : (hmat * Hmat) *ᵥ c₀ a = (hmat * Hmat) *ᵥ c₀ b := by
        simpa only [c, Matrix.mulVec_mulVec] using congrArg (fun v => hmat *ᵥ v) hab
      simpa [hhH] using h1
    · intro u
      obtain ⟨a, ha, hda⟩ := hc₀.onto (hmat *ᵥ u)
      refine ⟨a, ha, ?_⟩
      simp only [c]
      rw [hda, Matrix.mulVec_mulVec, hHh, Matrix.one_mulVec]
  let ν : S →* GL (Fin 4) (ZMod 2) := (MulAut.conj h⁻¹).toMonoidHom.comp μ
  have hνval : ∀ s : S,
      ((ν s : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = Hmat * m s * hmat := by
    intro s
    simp [ν, Hmat, hmat, MulAut.conj_apply, MonoidHom.coe_toHomUnits, hμval s]
  have hνker : ∀ s : S, ν s = 1 ↔ (s : G) ∈ B := by
    intro s
    have h1 : ν s = 1 ↔ μ s = 1 := by
      constructor
      · intro hs
        have hs' : (MulAut.conj h⁻¹) (μ s) = (MulAut.conj h⁻¹) 1 := by
          simpa [ν] using hs
        exact (MulAut.conj h⁻¹).injective hs'
      · intro hs
        simp [ν, hs]
    exact h1.trans (hμker s)
  have hrepν : ∀ s : S, IsRep A c (s : G) ((ν s : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
    intro s a ha
    have he : (Hmat * m s * hmat) * Hmat = Hmat * m s := by
      rw [mul_assoc, hhH, mul_one]
    calc
      c ((s : G) * a * (s : G)⁻¹) = Hmat *ᵥ (m s *ᵥ c₀ a) := by
        simp only [c]
        rw [hm s a ha]
      _ = (Hmat * m s) *ᵥ c₀ a := by rw [Matrix.mulVec_mulVec]
      _ = ((Hmat * m s * hmat) * Hmat) *ᵥ c₀ a := by rw [he]
      _ = (Hmat * m s * hmat) *ᵥ (Hmat *ᵥ c₀ a) :=
        (Matrix.mulVec_mulVec (c₀ a) (Hmat * m s * hmat) Hmat).symm
      _ = ((ν s : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ c a := by
        rw [hνval s]
  have hleν : ν.range ≤ CFSG.Quasithin.FFC.UT 4 := by
    intro x hx
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 hx
    simpa [ν, MulAut.conj_apply] using hhUT (μ s) ⟨s, rfl⟩
  have hrangeν : Nat.card ν.range = 2 ^ 6 := range_card_of_ker W ν hνker
  have hcardUT : Nat.card (CFSG.Quasithin.FFC.UT 4) = 2 ^ 6 := by
    rw [CFSG.Quasithin.FFC.card_UT]
  have heq : ν.range = CFSG.Quasithin.FFC.UT 4 :=
    Subgroup.eq_of_le_of_card_ge hleν (by rw [hcardUT, hrangeν])
  refine ⟨c, hc, ?_, ?_⟩
  · intro s hs
    refine ⟨ν ⟨s, hs⟩, ?_, hrepν ⟨s, hs⟩⟩
    simpa [ν, MulAut.conj_apply] using hhUT (μ ⟨s, hs⟩) ⟨⟨s, hs⟩, rfl⟩
  · intro g hg
    have hg' : g ∈ ν.range := by rw [heq]; exact hg
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.1 hg'
    exact ⟨s, s.2, by rw [← hs]; exact hrepν s⟩

theorem ThLocalIn.exists_mem_S_isRep_of_unitriangular {c : G → (Fin 4 → ZMod 2)}
    (hsurj : ∀ g ∈ CFSG.Quasithin.FFC.UT 4,
      ∃ s ∈ S, IsRep A c s (g : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    {i j : Fin 4} (hij : i < j) :
    ∃ s ∈ S, IsRep A c s (1 + Matrix.single i j 1) := by
  obtain ⟨s, hs, hrep⟩ := hsurj (CFSG.Quasithin.FFC.elemTv i j (ne_of_lt hij))
    (CFSG.Quasithin.FFC.elemTv_mem_UT hij)
  exact ⟨s, hs, by simpa only [CFSG.Quasithin.FFC.elemTv_val] using hrep⟩

end CFSG.EvenSporadicStandard.ThStd
