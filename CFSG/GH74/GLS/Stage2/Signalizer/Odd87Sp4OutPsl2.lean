module

public import CFSG.GH74.Generic.BProg.B2.PumpupTableL2
import CFSG.GH74.Generic.BProg.B1.PilotS4Facts
import CFSG.GH74.Generic.JMaxShapes
import CFSG.GH74.Generic.S1.Exo.Q3HNoQ8L2

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic.BProg
  CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.Filter.ClassicalOdd
  CFSG.GH74.Generic.BProg.B2.PumpupTableBasic CFSG.GH74.Generic.BProg.B2.PumpupTableL2

private theorem injective_of_center_trivial {X Q : Type} [Group X] [Group Q] (π : X →* Q)
    (hker : ∀ x, π x = 1 → x ∈ center X) (hZ : ∀ z : X, (∀ g : X, g * z = z * g) → z = 1) :
    Function.Injective π :=
  (injective_iff_map_eq_one π).2 fun a ha => hZ a (Subgroup.mem_center_iff.1 (hker a ha))

private theorem center_trivial_of_simple_of_q8 {X : Type} [Group X] (hs : IsSimpleGroup X)
    (ψ : Q8 →* X) (hψ : Function.Injective ψ) : ∀ z : X, (∀ g : X, g * z = z * g) → z = 1 := by
  intro z hz
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with hb | ht
  · have hzc : z ∈ center X := Subgroup.mem_center_iff.2 hz
    rw [hb] at hzc
    exact hzc
  · exfalso
    have hc : ψ (QuaternionGroup.a 1) ∈ center X := by
      rw [ht]
      exact Subgroup.mem_top _
    have h := Subgroup.mem_center_iff.1 hc (ψ (QuaternionGroup.xa 0))
    rw [← map_mul, ← map_mul] at h
    exact (by decide : (QuaternionGroup.xa 0 : Q8) * QuaternionGroup.a 1 ≠
      QuaternionGroup.a 1 * QuaternionGroup.xa 0) (hψ h)

section Certified

theorem not_qShapeNS_of_central_hom_psl2 {X Q : Type} [Group X] [Finite X] [Group Q] [Finite Q]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (π : X →* Q)
    (hker : ∀ x, π x = 1 → x ∈ center X) (hQ : LieModel Q .PSL 2 p f) : ¬ QShapeNS X := by
  intro hX
  have hsec : SectionalTwoRankLE Q 2 := sectionalTwoRankLE_two_of_psl2_model hp2 hQ
  rcases hX with h1 | h3 | h4 | h5
  · obtain ⟨z, φ, _, -, hcen, hφ, hφz, -⟩ := CFSG.GH74.L5U5.IsSL4Model.exists_q8_frame h1
    have hV4 : ∀ a : V4, a ^ 2 = 1 := CFSG.GH74.L5U5.V4_sq
    refine not_sectionalTwoRankLE_of_surjection 2 (π.comp φ) (q8Frattini.prodMap q8Frattini)
      (q8Frattini_surjective.prodMap q8Frattini_surjective)
      (fun a b => Prod.ext (mul_comm _ _) (mul_comm _ _))
      (fun a => Prod.ext (hV4 a.1) (hV4 a.2)) ?_ ?_ hsec
    · rw [Nat.card_prod, card_V4]
      norm_num
    · intro g hg
      rcases (hcen _).1 (hker _ hg) with h | h
      · have : g = 1 := hφ (by rw [h, map_one])
        rw [this]
        exact (q8Frattini.prodMap q8Frattini).ker.one_mem
      · have : g = (QuaternionGroup.a 2, QuaternionGroup.a 2) := hφ (by rw [h, hφz])
        rw [this, MonoidHom.mem_ker]
        exact Prod.ext CFSG.GH74.L5U5.q8Frattini_a_two CFSG.GH74.L5U5.q8Frattini_a_two
  · obtain ⟨ψ, hψ⟩ := exists_q8_of_shape13 (Or.inr h3)
    obtain ⟨_, _, -, -, -, hmod⟩ := h3
    have hinj : Function.Injective π := injective_of_center_trivial π hker
      (center_trivial_of_simple_of_q8 (isSimpleGroup_of_lieModel_L3' hmod) ψ hψ)
    exact CFSG.GH74.Generic.S1.Exo.no_q8_of_psl2_model hp hp2 (stated_of_lieModel (Or.inl rfl) hQ)
      (π.comp ψ) (hinj.comp hψ)
  · have hinj : Function.Injective π := injective_of_center_trivial π hker
      (CFSG.GH74.Generic.BProg.B1.PilotS4.center_of_qShape4 h4)
    exact (rankCertified_of_shape45 (Or.inl h4)).not_sectionalTwoRankLE
      (SectionalTwoRankLE.of_injective π hinj hsec)
  · have hinj : Function.Injective π := injective_of_center_trivial π hker
      (CFSG.GH74.Generic.BProg.B1.PilotS5.center_of_isSporadic h5)
    exact (rankCertified_of_shape45 (Or.inr h5)).not_sectionalTwoRankLE
      (SectionalTwoRankLE.of_injective π hinj hsec)

end Certified

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
