module

public import CFSG.GH74.GLS.IVK.Lifted.Std6Glue
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Basic

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.ABGLocalTools
  CFSG.ABGDGroups CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

section OutSL

variable {F : Type} [Field F] [Finite F]

theorem out_abelian_sl (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α β : MulAut (SpecialLinearGroup (Fin 2) F)) :
    α * β * α⁻¹ * β⁻¹ ∈
      (MulAut.conj : SpecialLinearGroup (Fin 2) F →* MulAut (SpecialLinearGroup (Fin 2) F)).range := by
  have hK := isOddPrimePower_card_of_odd hodd
  have : IsCyclic (F ≃+* F) := isCyclic_ringEquiv F
  have hcomm : ∀ a b : F ≃+* F, a * b = b * a := fun a b =>
    (IsCyclic.isMulCommutative (α := F ≃+* F)).is_comm.comm a b
  rw [mem_inn_iff hodd h3]
  have hγ : gammaOf hodd h3 (α * β * α⁻¹ * β⁻¹) = ⁅gammaOf hodd h3 α, gammaOf hodd h3 β⁆ := by
    rw [commutatorElement_def]
    simp only [map_mul, map_inv]
  rw [hγ]
  constructor
  · show (SemidirectProduct.rightHom ⁅gammaOf hodd h3 α, gammaOf hodd h3 β⁆ : F ≃+* F) = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ _)
  · rw [left_mem_range_toPGL_iff hK, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)

end OutSL

section OutDict

variable {Q : Type} [Group Q]

theorem innOf_normal (Q : Type) [Group Q] : (innOf Q).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨q, rfl⟩ := hn
  refine ⟨g q, ?_⟩
  ext x
  simp [MulAut.conj_apply]

theorem dict_out_abelian (h2A7 : II4_2A7) [Finite Q] (hQ : IsSL2Or2A7 Q) (α β : MulAut Q) :
    α * β * α⁻¹ * β⁻¹ ∈ innOf Q := by
  rcases sl_or_a7 hQ with ⟨F, _, _, hodd, h3, ⟨e⟩⟩ | h7
  · obtain ⟨s, hs⟩ := out_abelian_sl hodd h3 (MulAut.congr e α) (MulAut.congr e β)
    refine ⟨e.symm s, ?_⟩
    apply (MulAut.congr e).injective
    rw [congr_conj, MulEquiv.apply_symm_apply, hs]
    simp only [map_mul, map_inv]
  · have hidx := (h2A7 Q h7).2.2.2.1
    rw [Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
      Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
    tauto

end OutDict

section Std6r1Out

variable {G : Type} [Group G] [Finite G] {z : G} {S K : Subgroup G}

@[expose] noncomputable def phiHom (K : Subgroup G) : ↥(normalizer (K : Set G)) →* MulAut (Hat K) where
  toFun c := phi K c c.2
  map_one' := phi_one_aux K _
  map_mul' x y := phi_mul K x.2 y.2

omit [Finite G] in
theorem phiHom_apply (K : Subgroup G) (c : ↥(normalizer (K : Set G))) :
    phiHom K c = phi K c c.2 := rfl

theorem std6r1_C_normalizes (h : Std6r1 G z S K) {c : G} (hc : c ∈ centralizer ({z} : Set G)) :
    c ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  have h1 := std6r1_cmap_eq h (inv_mem hc)
  have h2 : x ∈ cmap c⁻¹ K ↔ c⁻¹⁻¹ * x * c⁻¹ ∈ K := mem_cmap
  rw [h1, inv_inv] at h2
  exact h2

theorem commBar_phi_inner (h2A7 : II4_2A7) {K : Subgroup G} (hQ : IsSL2Or2A7 (Hat K))
    (hCN : Cz z ≤ normalizer (K : Set G)) {a : G} (haN : a ∈ normalizer (K : Set G))
    (haa : a * a = 1) (hcomm : a ∈ commBar z) : phi K a haN ∈ innOf (Hat K) := by
  have : (innOf (Hat K)).Normal := innOf_normal _
  have hOutComm : ∀ x y : MulAut (Hat K) ⧸ innOf (Hat K), x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with | H α => ?_
    induction y using QuotientGroup.induction_on with | H β => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have := dict_out_abelian h2A7 hQ β⁻¹ α⁻¹
    simpa [mul_assoc] using this
  let _ : CommGroup (MulAut (Hat K) ⧸ innOf (Hat K)) :=
    { (inferInstance : Group (MulAut (Hat K) ⧸ innOf (Hat K))) with mul_comm := hOutComm }
  let ρ : ↥(Cz z) →* (MulAut (Hat K) ⧸ innOf (Hat K)) :=
    (QuotientGroup.mk' (innOf (Hat K))).comp ((phiHom K).comp (Subgroup.inclusion hCN))
  set m := Nat.card ↥(Oz z) with hm
  have hmodd : Odd m := card_Oz_odd
  let ν : ↥(Cz z) →* (MulAut (Hat K) ⧸ innOf (Hat K)) := (powMonoidHom m).comp ρ
  have hνcomm : ∀ x y : ↥(Cz z), ν ⁅x, y⁆ = 1 := by
    intro x y
    have : ρ ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
    show (ρ ⁅x, y⁆) ^ m = 1
    rw [this, one_pow]
  have hνO : ∀ o ∈ Oz z, ∃ ho : o ∈ Cz z, ν ⟨o, ho⟩ = 1 := by
    intro o ho
    have hoC : o ∈ Cz z := TwoThin.pPrimeCoreOf_le (Cz z) ho
    refine ⟨hoC, ?_⟩
    have h1 : (⟨o, ho⟩ : ↥(Oz z)) ^ m = 1 := pow_card_eq_one'
    have h2 : o ^ m = 1 := by simpa using congrArg Subtype.val h1
    show (ρ ⟨o, hoC⟩) ^ m = 1
    rw [← map_pow]
    have : (⟨o, hoC⟩ : ↥(Cz z)) ^ m = 1 := Subtype.ext (by simpa using h2)
    rw [this, map_one]
  let M : Subgroup G := ν.ker.map (Cz z).subtype
  have h1 : ⁅Cz z, Cz z⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro c₁ hc₁ c₂ hc₂
    exact Subgroup.mem_map.2 ⟨⁅⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⁆, hνcomm _ _, rfl⟩
  have h2 : Oz z ≤ M := by
    intro o ho
    obtain ⟨hoC, hν⟩ := hνO o ho
    exact Subgroup.mem_map.2 ⟨⟨o, hoC⟩, hν, rfl⟩
  have h3 : commBar z ≤ M := sup_le h1 h2
  obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 (h3 hcomm)
  have hxa' : (x : G) = a := hxa
  have hρm : (ρ x) ^ m = 1 := hx
  have hρ2 : ρ x * ρ x = 1 := by
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (by simp [hxa', haa])
    rw [this, map_one]
  have hρ1 : ρ x = 1 := by
    obtain ⟨k, hk⟩ := hmodd
    have : (ρ x) ^ (2 * k + 1) = ρ x := by
      rw [pow_succ, pow_mul, sq, hρ2, one_pow, one_mul]
    rw [← this, ← hk]
    exact hρm
  have hxN : (x : G) ∈ normalizer (K : Set G) := hCN x.2
  have hρx : ρ x = QuotientGroup.mk (phi K (x : G) hxN) := rfl
  have hin : phi K (x : G) hxN ∈ innOf (Hat K) := by
    rw [hρx] at hρ1
    exact (QuotientGroup.eq_one_iff _).1 hρ1
  subst hxa'
  exact hin

theorem ivk_3_2a_r1_of_II4 (h44 : II4_44) (h2A7 : II4_2A7) :
    CFSG.GH74.GLS.Stage1.Thm3.Sec6.IVK_3_2a_r1 := by
  intro G _ _ z S K h a ha ha2 haz haF hac hcomm
  obtain ⟨haN, hF⟩ := haF
  have ha2' : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha2, sq] at this
  have hOK := std6_hatOK h44 h.toStd6 (std6r1_comp_rigid h)
  have hCN : Cz z ≤ normalizer (K : Set G) := fun c hc => std6r1_C_normalizes h hc
  obtain ⟨c, hc⟩ := commBar_phi_inner h2A7 hOK.sl2 hCN haN ha2' hcomm
  have hcz : c ∈ Subgroup.center (Hat K) := dict_inner h2A7 hOK.sl2 c (by rw [hc]; exact hF)
  have h1' : phi K a haN = 1 := by rw [← hc]; exact conj_eq_one_of_mem_center hcz
  exact hac ((phi_eq_one_iff K haN).1 h1')

end Std6r1Out

end CFSG.GH74.GLS.IVK.Lifted
