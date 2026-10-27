module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29S1B
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Dih
import CFSG.GH74.GLS.IVK.Lifted.Out
import CFSG.GH74.GLS.Stage2.Local.Lemma23e
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSylow

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.Assembly.LowTwoRank
  CFSG.GorensteinWalter CFSG.GH74.GLS.IVK.Lifted

namespace L29S1

section Out

theorem out_comm_of_hasSL2Model {L : Type} [Group L] {q : ℕ} (hodd : Odd q) (hgt : 3 < q)
    (hs : HasSL2Model L (fun r => r = q)) (α β : MulAut L) :
    α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : L →* MulAut L).range := by
  obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := hs
  have hq' : Nat.card F = q := hq
  let e' : L ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.trans (specialLinearGroupEquivStatedSL 2 F).symm
  obtain ⟨s, hsc⟩ := out_abelian_sl (hq' ▸ hodd) (hq' ▸ hgt) (MulAut.congr e' α)
    (MulAut.congr e' β)
  refine ⟨e'.symm s, ?_⟩
  apply (MulAut.congr e').injective
  have hc : MulAut.congr e' (MulAut.conj (e'.symm s)) = MulAut.conj s := by
    ext x
    simp [MulAut.conj_apply]
  rw [hc, hsc]
  simp only [map_mul, map_inv]

end Out

section Psl2

variable {H : Type} [Group H] {L₁ L₂ : Subgroup H} {u : H}

theorem exists_equiv_psl2_diagHom_range (h : SwapData L₁ L₂ u) [Finite H] {q : ℕ} (hodd : Odd q)
    (hs₁ : HasSL2Model ↥L₁ (fun r => r = q)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
      Nonempty (↥(diagHom h).range ≃* PSL2 F) := by
  obtain ⟨hZ, -⟩ := sl2_model_center_inv hodd hs₁
  obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := hs₁
  have hq' : Nat.card F = q := hq
  refine ⟨F, hF, hFin, hq', ⟨?_⟩⟩
  let e' : ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.trans (specialLinearGroupEquivStatedSL 2 F).symm
  have hker : (diagHom h).ker = center ↥L₁ := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro ha b
      have h1 : (a : H) * (u * (a : H) * u⁻¹) = 1 := ha
      have h2 : (a : H) = (u * (a : H) * u⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h3 : (a : H) ∈ L₂ := by
        rw [h2]
        exact L₂.inv_mem (h.mem₂ a.2)
      exact Subtype.ext (h.comm b b.2 a h3)
    · intro ha
      have h3 : (a : H) ∈ L₂ :=
        central_mem_of_card_inf h.comm hZ h.card a.2
          (fun c hc => congrArg Subtype.val (ha ⟨c, hc⟩))
      have ha2 : (a : H) ∈ L₁ ⊓ L₂ := ⟨a.2, h3⟩
      have hu : u * (a : H) * u⁻¹ = a := by rw [h.commute_u ha2]; group
      show (a : H) * (u * (a : H) * u⁻¹) = 1
      rw [hu]
      exact h.mul_self_of_mem_inf ha2
  exact (QuotientGroup.quotientKerEquivRange (diagHom h)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.congr (center ↥L₁) (center (Matrix.SpecialLinearGroup (Fin 2) F)) e'
        (Subgroup.map_center_eq e')))

end Psl2

section Sylow

theorem isCyclic_or_isDihedral_of_psl2 {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {Y : Type} [Group Y] (e : Y ≃* PSL2 F) {P : Type} [Group P] (hP : IsPGroup 2 P)
    (f : P →* Y) (hf : Function.Injective f) : IsCyclic P ∨ IsDihedral P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  have hr : IsPGroup 2 ↥f.range := hP.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨T, hT⟩ := hr.exists_le_sylow
  obtain ⟨m, hm, ⟨φ⟩⟩ :=
    ComponentClassification.AutL2Facts.sylow_two_dihedral_of_equiv e
      (ABGLocalTools.isOddPrimePower_card_of_odd hodd) T
  have h2m : 2 ≤ 2 ^ m :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hdih : IsDihedral ↥(T : Subgroup Y) := ⟨2 * 2 ^ m, 2 ^ m, rfl, h2m, ⟨φ⟩⟩
  let eP : P ≃* ↥(f.range.subgroupOf (T : Subgroup Y)) :=
    (MonoidHom.ofInjective hf).trans (Subgroup.subgroupOfEquivOfLe hT).symm
  rcases subgroup_of_dihedral hdih (f.range.subgroupOf (T : Subgroup Y)) with hc | hd
  · exact Or.inl (eP.isCyclic.mpr hc)
  · obtain ⟨m', k, hm', hk, ⟨g⟩⟩ := hd
    exact Or.inr ⟨m', k, hm', hk, ⟨eP.trans g⟩⟩

end Sylow

end L29S1

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
