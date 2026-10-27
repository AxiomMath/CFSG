module

public import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Struct

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.AutL3
  CFSG.Quasithin.A318P CFSG.RankThree.PartTwo.KFacts

theorem exists_mem_D_of_frame {M : Type} [Group M] [Finite M] {C : Type} [Group C] [Finite C]
    [IsCyclic C] (F : L3Frame M C) (Ee : Subgroup (MulAut M)) (hE : CFSG.Open.IsElemAbelian 3 Ee)
    (hcard : Nat.card Ee = 27) : ∃ x ∈ Ee, x ∈ F.D ∧ x ≠ 1 := by
  have hle : Ee ≤ F.E := by
    intro x hx
    have h3 : x ^ 3 = 1 := hE.2 x hx
    have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h1
    · have : x = 1 := orderOf_eq_one_iff.1 h1
      rw [this]; exact F.E.one_mem
    · exact F.mem_E.2 (F.three_mem x 1 (by rw [h1]; norm_num))
  set ρ : ↥Ee →* C := F.rho.comp (Subgroup.inclusion hle) with hρ
  have hker : ∀ x : ↥Ee, ρ x = 1 ↔ (x : MulAut M) ∈ F.D := fun x =>
    F.rho_eq_one_iff ⟨x, hle x.2⟩
  have hcube : ∀ c ∈ ρ.range, c ^ 3 = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : (x : ↥Ee) ^ 3 = 1 := Subtype.ext (hE.2 x x.2)
    rw [this, map_one]
  have hrcard : Nat.card ρ.range ≤ 3 :=
    card_le_three_of_pow (fun c => Subtype.ext (by simpa using hcube c c.2))
  have hmul := Subgroup.card_ker_mul_card_range ρ
  have hne : ρ.ker ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot, hcard] at hmul
    omega
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  refine ⟨(z : MulAut M), z.2, (hker z).1 hz, fun h => hz1 ?_⟩
  exact Subtype.ext (Subtype.ext h)

theorem autStruct_of_frame {Y M : Type} [Group Y] [Finite Y] [Group M] [Finite M] {C : Type}
    [Group C] [Finite C] [IsCyclic C] (hY : CFSG.Open.IsQuasisimple Y)
    (ε : (Y ⧸ Subgroup.center Y) ≃* M) (F : L3Frame M C)
    (hD9 : ∀ E : Subgroup (MulAut M), E ≤ F.D → CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 9)
    (hfield : ∀ (α : MulAut Y) (h : MulAut M) (c : C), orderOf c = 3 →
      MulAut.congr ε (centerDescend Y α) = h * F.fld c * h⁻¹ → IsFieldAutThree α)
    (hdiag : ∀ α : MulAut Y, MulAut.congr ε (centerDescend Y α) ∈ F.D →
      Lemma54Ns.IsInnDiagThree α)
    (E : Subgroup (MulAut Y)) (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : Nat.card E = 27) :
    (∃ b ∈ E, IsFieldAutThree b ∧ b ≠ 1) ∧ ∃ x ∈ E, Lemma54Ns.IsInnDiagThree x ∧ x ≠ 1 := by
  refine ⟨?_, ?_⟩
  · obtain ⟨G, hGE, hidx, hG⟩ := l3Aut_of_frame hY ε F hD9 hfield E hE
    have h1 := Subgroup.card_mul_index (G.subgroupOf E)
    have h2 : Nat.card (G.subgroupOf E) = Nat.card G :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hGE).toEquiv
    have hne : G ≠ ⊥ := by
      intro hbot
      have hG1 : Nat.card G = 1 := by rw [hbot, Subgroup.card_bot]
      rw [h2, hG1, hcard] at h1
      omega
    obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    exact ⟨b, hGE hb, hG b hb, fun h => hb1 (Subtype.ext h)⟩
  · set Φ : MulAut Y →* MulAut M := (MulAut.congr ε).toMonoidHom.comp (centerDescend Y) with hΦ
    have hinj : Function.Injective Φ := phi_injective hY ε
    have hE' : CFSG.Open.IsElemAbelian 3 (E.map Φ) := isElemAbelian_map Φ hE
    have hc' : Nat.card (E.map Φ) = 27 := by
      rw [Subgroup.card_map_of_injective hinj, hcard]
    obtain ⟨x', hx'E, hx'D, hx'1⟩ := exists_mem_D_of_frame F (E.map Φ) hE' hc'
    obtain ⟨x, hx, rfl⟩ := hx'E
    exact ⟨x, hx, hdiag x hx'D, fun h => hx'1 (by rw [h, map_one])⟩

end CFSG.HardMathSupport.Solomon.Coordinator
