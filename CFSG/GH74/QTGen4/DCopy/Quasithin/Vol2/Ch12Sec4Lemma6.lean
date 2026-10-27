module

public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma6
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4Cx

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative Pointwise

@[expose] def NormalizerR1Le1246_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Cx1242 G T L V →
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    ∀ E : Subgroup G, E ≤ V → Nat.card E = 4 → T ≤ Subgroup.normalizer (E : Set G) →
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) ≤
        Subgroup.normalizer (L : Set G)

variable {G : Type} [Group G]

theorem lemma12_4_6_of_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (hpre : Pre1242_F4)
    (hN : NormalizerR1Le1246_F4) : Lemma12_4_6_F4 := by
  intro G _ _ T L V hcx h3' E hEV hE4 hTE v hvE hvL
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hcx.hyp
  obtain ⟨z, hf⟩ := CxFacts.of_F4 h331 h1222 hpre hcx (Or.inl h3')
  have := hf.comm
  obtain ⟨hV16, -, -, hnat⟩ := cx_l3_module_F4 h1222 hcx hf h3'
  obtain ⟨hR, hidx⟩ := cx_relIndex_eq_two hcx hf hV16 hnat hEV hE4 hTE hvE hvL
  refine ⟨?_, hidx⟩
  have hR₁v : T ⊓ Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer ({v} : Set G) :=
    hR ▸ inf_le_right
  have hR₁p : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer (E : Set G)) := hyp.sylow.1.to_le inf_le_left
  have hcardR : Nat.card T = 2 * Nat.card ↥(T ⊓ Subgroup.centralizer (E : Set G)) := by
    have h1 := Subgroup.relIndex_mul_card (T ⊓ Subgroup.centralizer (E : Set G)) T
    rw [show T ⊓ Subgroup.centralizer (E : Set G) ⊓ T =
      T ⊓ Subgroup.centralizer (E : Set G) from inf_eq_left.2 inf_le_left, hidx] at h1
    exact h1.symm
  obtain ⟨S, hRS, hS⟩ := QuasithinUnique.exists_isSylowTwoOf_of_le hR₁v hR₁p
  suffices hSR : S = T ⊓ Subgroup.centralizer (E : Set G) by
    rw [← hSR]
    exact hS
  by_contra hne
  have hlt : T ⊓ Subgroup.centralizer (E : Set G) < S := lt_of_le_of_ne hRS (Ne.symm hne)

  have : Group.IsNilpotent ↥S := hS.isPGroup.isNilpotent
  have hRS' : (T ⊓ Subgroup.centralizer (E : Set G)).subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hne (le_antisymm (fun x hx => ?_) hRS)
    have h1 : (⟨x, hx⟩ : ↥S) ∈ (T ⊓ Subgroup.centralizer (E : Set G)).subgroupOf S :=
      h ▸ Subgroup.mem_top _
    exact h1
  obtain ⟨s, hsN, hsR⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hRS')
  have hsN' : (s : G) ∈ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    by_cases hy : y ∈ S
    · have h1 := (Subgroup.mem_normalizer_iff.1 hsN) ⟨y, hy⟩
      simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using h1
    · constructor
      · intro h
        exact absurd (hRS h) hy
      · intro h
        exfalso
        apply hy
        have h2 := S.mul_mem (S.mul_mem (S.inv_mem s.2) (hRS h)) s.2
        rwa [show (s : G)⁻¹ * ((s : G) * y * (s : G)⁻¹) * s = y by group] at h2

  set N := S ⊓ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G)
  have hNM : N ≤ Subgroup.normalizer (L : Set G) :=
    inf_le_right.trans (hN G T L V hcx h3' E hEV hE4 hTE)
  have hNv : N ≤ Subgroup.centralizer ({v} : Set G) := inf_le_left.trans hS.le
  have hNp : IsPGroup 2 N := hS.isPGroup.to_le inf_le_left
  have h2N := cx_two_mul_card_le hcx hf hV16 hnat (hEV hvE) hvL hNM hNv hNp
  have hRN : T ⊓ Subgroup.centralizer (E : Set G) < N := by
    refine lt_of_le_of_ne (le_inf hRS Subgroup.le_normalizer) fun h => hsR ?_
    have h1 : (s : G) ∈ N := ⟨s.2, hsN'⟩
    rw [← h] at h1
    exact h1
  have := Subgroup.card_lt_of_lt hRN
  omega

end CFSG.Quasithin.H13
