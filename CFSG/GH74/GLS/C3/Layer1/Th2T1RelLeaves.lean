module

public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelAPI
public import CFSG.GH74.GLS.C3.Layer1.Thm1FmemberF

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Thm1
open scoped commutatorElement

@[expose] def B_thm1_P31s_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K : Subgroup G), Is2TerminalU2Triple x y K →
      (HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) →
      ¬ HasL2Model (kBar K) (fun q => q = 5) →
      (∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) ∧
      (∀ K' : Subgroup G, IsPCompIn 2 (centralizer ({x} : Set G)) K' → K' = K) ∧
      (∃ Q : Subgroup G, IsSylowOf 2 Q (CMK (centralizer ({x} : Set G)) K) ∧
        (IsCyclic ↥Q ∨ C3.Layer1.P34.IsMaximalClassTwoGroup ↥Q)) ∧
      ∀ T : Subgroup G, Setup1D x K T →
        (∃ f : G, IsFMember x K T f ∧ C3.Layer1.P34.InducesFAutL2A7 f K) ∧
        (∃ n : ℕ, 3 ≤ n ∧ IVK.IsDihedralTwoGroup ↥(T ⊓ K) n) ∧
        ∃ z ∈ T ⊓ K, orderOf z = 2 ∧ (∀ p ∈ T ⊓ K, z * p = p * z) ∧
          ∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, w * p = p * w) → w = 1 ∨ w = z

@[expose] def B_thm1_P31c_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K : Subgroup G), Is2TerminalU2Triple x y K →
      ¬ HasL2Model (kBar K) (fun q => q = 5) → IsSylowOf 2 (zpowers x) (CxK x K)

@[expose] def B_thm1_L32'_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K : Subgroup G) (f : G), FMax3 x y K f →
      ¬ HasL2Model (kBar K) (fun q => q = 5) →
      IsPCompIn 2 (centralizer ({f} : Set G)) (pumpJ K f) ∧
      (∀ c ∈ centralizer ({f} : Set G), ∀ j ∈ pumpJ K f, c * j * c⁻¹ ∈ pumpJ K f) ∧
      ∃ r : ℕ, Odd r ∧ 5 ≤ r ∧ HasL2Model (kBar (layerI K f)) (fun q => q = r) ∧
        (HasL2Model (kBar K) (fun q => q = r ^ 2) ∨
          (r = 5 ∧ Nonempty (kBar K ≃* alternatingGroup (Fin 7)))) ∧
        (HasL2Model (kBar (pumpJ K f)) (fun q => q = r) ∨
          HasL2Model (kBar (pumpJ K f)) (fun q => q = r ^ 2) ∨
          Nonempty (kBar (pumpJ K f) ≃* alternatingGroup (Fin 7))) ∧
        (Nonempty (kBar (pumpJ K f) ≃* alternatingGroup (Fin 7)) →
          HasL2Model (kBar K) (fun q => q = 5 ^ 2) ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7)))

@[expose] def B_thm1_FmemberF_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K : Subgroup G), Is2TerminalU2Triple x y K →
      (HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) →
      (∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) →
      ∀ T : Subgroup G, Setup1D x K T → ∀ f : G, IsFMember x K T f →
        ¬ HasL2Model (kBar K) (fun q => q = 5) → P34.InducesFAutL2A7 f K

theorem thm1_FmemberF_of_rel
    (h2hb : IVK.IVK_1_2h_b) : B_thm1_FmemberF_rel := by
  intro G _ _ hG hV x y K h𝒰 hshape hKN T hT f hfm h5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hfT, hf2, hfc, hfx, hlayer⟩ := hfm
  have hKC : K ≤ centralizer ({x} : Set G) := h𝒰.1.1.2.1
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hQ2 := card_le_two_of_noV2Fine hV h𝒰 h5
  obtain ⟨hcen, hAut⟩ := kBar_autData_rel h2hb hV h𝒰 hshape h5
  obtain ⟨E₁, hE₁T, hE₁, hE₁16⟩ := exists_E₁ hT.sylowT (by rw [h𝒰.2.2.1.2, hG.pRank_eq_four])
  have hfC : f ∈ centralizer ({x} : Set G) := hT.sylowT.le hfT
  obtain ⟨f₁, z₁, -, -, -, -, -, -, -, hz₁, -, -, -, -, hFA, hinner, -⟩ :=
    core_lift_G hKC hKN hT.sylowT hcen hAut hE₁T hE₁ hE₁16 hQ2
  have hfCT : (⟨f, hfC⟩ : ↥(centralizer ({x} : Set G))) ∈
      T.subgroupOf (centralizer ({x} : Set G)) := hfT
  have hf2' : orderOf (⟨f, hfC⟩ : ↥(centralizer ({x} : Set G))) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hf2
  have hfc' : ∀ p ∈ (T ⊓ K).subgroupOf (centralizer ({x} : Set G)),
      (⟨f, hfC⟩ : ↥(centralizer ({x} : Set G))) * p = p * ⟨f, hfC⟩ :=
    fun p hp => Subtype.ext (hfc p hp)
  by_cases hinn : Back.actHom hKN ⟨f, hfC⟩ ∈ IVK.innAut (kBar K)
  · exfalso
    rcases hinner ⟨f, hfC⟩ hfCT hfc' hinn with h1 | ⟨h1, hsolv⟩
    ·
      have hfker : (⟨f, hfC⟩ : ↥(centralizer ({x} : Set G))) ∈ (Back.actHom hKN).ker := h1
      rw [Back.actHom_ker hKN] at hfker
      have hfCMK : f ∈ CMK (centralizer ({x} : Set G)) K := hfker
      have hφx : Back.actHom hKN ⟨x, hxC⟩ = 1 :=
        (Back.actHom_eq_one_iff_commutator_mem hKN ⟨x, hxC⟩).2 (fun k hk => by
          have hxk : x * k = k * x := (mem_centralizer_singleton_iff.1 (hKC hk)).symm
          have : ⁅k, x⁆ = 1 := by
            rw [commutatorElement_def, ← hxk]
            group
          rw [this]
          exact (pPrimeCoreOf 2 K).one_mem)
      have hxker : (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G))) ∈ (Back.actHom hKN).ker := hφx
      rw [Back.actHom_ker hKN] at hxker
      have hxCMK : x ∈ CMK (centralizer ({x} : Set G)) K := hxker
      have hx2 : orderOf x = 2 := h𝒰.1.1.1
      have hfxc : f * x = x * f := mem_centralizer_singleton_iff.1 hfC
      obtain ⟨V, hVle, hV4, hVcard⟩ :=
        LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute hf2
          hx2 hfxc hfx
      have hVC : V ≤ CMK (centralizer ({x} : Set G)) K := by
        refine hVle.trans ((Subgroup.closure_le _).2 ?_)
        intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · exact hfCMK
        · exact hxCMK
      have := hQ2 V hVC hV4
      omega
    ·
      have hz₁K : (z₁ : G) ∈ K := hz₁.2
      have hφz₁ : Back.actHom hKN z₁ =
          MulAut.conj (QuotientGroup.mk (⟨(z₁ : G), hz₁K⟩ : ↥K) : kBar K) :=
        Back.actHom_of_mem hKN hz₁K z₁.2
      have hsolvC : Group.IsSolvable ↥(K ⊓ centralizer ({f} : Set G)) :=
        isSolvable_cent_of_inner hKN hfC (h1.trans hφz₁) (hsolv _ hφz₁.symm)
      exact hlayer (pLayerOf_eq_bot_of_solvable hsolvC)
  · exact ⟨U1a.mem_normalizer_of_norm hKN hfC, hFA ⟨f, hfC⟩ hfCT hf2' hfc' hinn⟩

end CFSG.GH74.GLS
