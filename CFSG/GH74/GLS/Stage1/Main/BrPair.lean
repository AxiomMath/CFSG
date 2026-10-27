module

public import CFSG.GH74.GLS.Stage1.Main.Bridge
public import CFSG.GH74.GLS.Stage1.Main.BrPairStd4
public import CFSG.GH74.GLS.Stage1.Main.BrPairSwap
public import CFSG.GH74.GLS.Stage1.Main.BrPairModel
public import CFSG.GH74.GLS.Stage2.Final.ClassicalN
public import CFSG.GH74.GLS.Stage2.Final.ModelIVK410Final

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6.Prod
  CFSG.GH74.GLS.Stage2.Final
open scoped commutatorElement

theorem exists_model7 {q : ℕ} (hodd : Odd q) (h5 : 5 ≤ q) (w1 : Prop) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = q) :
    ∃ (Gs : Type) (_ : Group Gs) (_ : Finite Gs) (p f : ℕ), IsClassicalModel Gs p f ∧ Model7 Gs q w1 := by
  obtain ⟨p, f, hp, hf, hpf⟩ := exists_prime_pow_of_field F
  have hqpf : q = p ^ f := hF.symm.trans hpf
  have hp2 : p ≠ 2 := prime_ne_two_of_odd hp hf hqpf hodd
  have h3 : 3 < p ^ f := by omega
  by_cases hw : w1
  · obtain ⟨Gs, iGs, fGs, hL⟩ := exists_model_psp p f hp hf h3
    exact ⟨Gs, iGs, fGs, p, f, ⟨hp, hp2, h3, Or.inl hL⟩,
      Or.inl ⟨hw, by rw [hqpf]; exact isPSp4_of_lieModel hL⟩⟩
  · have hq4 : q % 4 = 3 ∨ q % 4 = 1 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    rcases hq4 with h4 | h4
    · have h8 : p ^ f % 8 ≠ 1 := by omega
      obtain ⟨Gs, iGs, fGs, hL⟩ := exists_model_psl p f hp hf
      exact ⟨Gs, iGs, fGs, p, f, ⟨hp, hp2, h3, Or.inr (Or.inl ⟨h8, hL⟩)⟩,
        Or.inr ⟨hw, Or.inl ⟨h4, by rw [hqpf]; exact isLnEps_psl_of_lieModel hL⟩⟩⟩
    · have h8 : p ^ f % 8 ≠ 7 := by omega
      obtain ⟨Gs, iGs, fGs, hL⟩ := exists_model_psu p f hp hf
      exact ⟨Gs, iGs, fGs, p, f, ⟨hp, hp2, h3, Or.inr (Or.inr ⟨h8, hL⟩)⟩,
        Or.inr ⟨hw, Or.inr ⟨h4, by rw [hqpf]; exact isLnEps_psu_of_lieModel hL⟩⟩⟩

theorem pairBridge7_thm (hII : II4_4_4_center) (h44 : II4_44) (h41 : Prop4_1) : PairBridge7 := by
  intro G _ _ z S q w hcen hT hbase
  obtain ⟨K₁, K₂, hs, hodd, h5, hK₁, hK₂, hT7⟩ := hT
  have hM := m4_of_std hII hs
  have hXC : K₁ ⊔ K₂ ⊔ S ≤ centralizer ({z} : Set G) :=
    sup_le (sup_le hM.K₁_le hM.K₂_le) hs.sylow.le
  have hcomps := comps_of_std4 hII h41 hs
  have hsw : ∃ s ∈ S, Swaps z s (imgBar z K₁) (imgBar z K₂) := by
    obtain ⟨F, iF, fF, hFq, -⟩ := id hK₁
    obtain ⟨Gs, iGs, fGs, p, f, hGs, hmod⟩ := exists_model7 hodd h5 (w = 1) hFq
    obtain ⟨S'⟩ : Nonempty (Sylow 2 Gs) := inferInstance
    obtain ⟨z', hz'o, hcenS'⟩ := modelCenter Gs p f hGs S'
    have hC := hT7 Gs z' S' hmod hz'o hcenS'
    have hSp : IVK.IsSp4L4U4 Gs q := by
      rcases hmod with ⟨-, hP⟩ | ⟨-, hLU⟩
      · exact Or.inl hP
      · exact Or.inr hLU
    have hz'mem : z' ∈ ((center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype) := by
      rw [hcenS']
      exact mem_zpowers z'
    obtain ⟨c, hc', hcz⟩ := hz'mem
    have hcz' : (c : Gs) = z' := hcz
    have hz'S' : z' ∈ (S' : Subgroup Gs) := hcz' ▸ c.2
    have hz'c : ∀ x ∈ (S' : Subgroup Gs), x * z' = z' * x := by
      intro x hx
      have := Subgroup.mem_center_iff.1 hc' ⟨x, hx⟩
      rw [← hcz']
      exact congrArg Subtype.val this
    obtain ⟨t', w', E₁, E₂, ht'S, hw'S, ht'o, hw'o, hcomm', hprod', hinter', ht'c, hEz, hE₂, hsl2,
        hinterE, hcommE, hnormE, hw1iff, hcls, htzne, hEfus, hpgl, hwfus, -⟩ :=
      ivk_4_10 Gs q hodd h5 hSp S' z' hz'S' hz'o hz'c
    obtain ⟨ht, hc₁, hc₂, hne, hu₁, hu₂⟩ :=
      model_swap_data h5 hz'o hz'c hEz hE₂ hsl2 hinterE hcommE ht'S ht'o
    exact exists_swap_of_compat hXC (fun H hH => isComponent_map_barOf hII hs hH) hcomps hC hc₁ hc₂ hne
      ⟨t', ht⟩ ht'S hu₁ hu₂
  exact ⟨imgBar z K₁, imgBar z K₂,
    stage1Pair_of_std4 hII h44 h41 hs hodd h5 hK₁ hK₂ hbase hsw⟩

end CFSG.GH74.GLS.Stage1.Main
