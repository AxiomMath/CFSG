module

public import CFSG.ClassicalInvolution.Q3.Q3T7EApp
public import CFSG.ClassicalInvolution.Q3.Q3T7P25H01
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2201
public import CFSG.ClassicalInvolution.Q3.Q3T7M03
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Model

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
theorem thmE_apply
    (hE : Q3T7E.ThmEWithSylow3) {K K' : Subgroup G} {z : G} (hst :
    Q3T8.Asc77.AscStand Ω K)
    (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) {H : Subgroup G}
    (hstd : StdCent Ω K H z)
    (htrans : ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J) : H = ⊤ :=
  Q3T7E.thmE_apply3 hE hst.toStand3 hz hK' hne hstd htrans
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}
namespace Hyp22
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.Hyp22

theorem hzK'
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) : IsUniqueInvolution K' z :=
  isUniqueInvolution_of_mem_twinSet h.std.hz h.std.hK'

theorem hzK₃
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) : IsUniqueInvolution K₃ z :=
  isUniqueInvolution_of_mem_twinSet h.std.hz h.hK₃

theorem sq₁
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) : u₁ * u₁ = z :=
  T7A.sq_eq_of_orderOf_four h.std.hz h.hu₁.1 h.hu₁.2

theorem sq₂
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) : u₂ * u₂ = z :=
  T7A.sq_eq_of_orderOf_four h.hzK' h.hu₂.1 h.hu₂.2

theorem sq₃
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) : u₃ * u₃ = z :=
  T7A.sq_eq_of_orderOf_four h.hzK₃ h.hu₃.1 h.hu₃.2

theorem comm_z₁
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) : z * u₁ = u₁ * z :=
  e189_commute_of_mem h.std.hz h.hu₁.1

theorem comm_z₂
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) : z * u₂ = u₂ * z :=
  e189_commute_of_mem h.hzK' h.hu₂.1

theorem comm_z₃
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) : z * u₃ = u₃ * z :=
  e189_commute_of_mem h.hzK₃ h.hu₃.1

theorem sq_12
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) : (u₁ * u₂) * (u₁ * u₂) = 1 :=
  h.hB.2 _ T7B.mem_closure_fst

theorem sq_23
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) : (u₂ * u₃) * (u₂ * u₃) = 1 :=
  h.hB.2 _ T7B.mem_closure_thd

theorem comm₁₂
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) : u₁ * u₂ = u₂ * u₁ :=
  T7B.comm_of_mul_self_eq_one h.sq₁ h.sq₂ h.std.hz.sq h.comm_z₁ h.sq_12

theorem comm₂₃
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) : u₂ * u₃ = u₃ * u₂ :=
  T7B.comm_of_mul_self_eq_one h.sq₂ h.sq₃ h.std.hz.sq h.comm_z₂ h.sq_23

theorem eq_13
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    u₁ * u₃ = z * ((u₁ * u₂) * (u₂ * u₃)) := by
  have h1 : (u₁ * u₂) * (u₂ * u₃) = u₁ * z * u₃ := by
    calc (u₁ * u₂) * (u₂ * u₃) = u₁ * (u₂ * u₂) * u₃ := by group
      _ = u₁ * z * u₃ := by rw [h.sq₂]
  calc u₁ * u₃ = (z * z) * (u₁ * u₃) := by rw [h.std.hz.sq, one_mul]
    _ = z * (z * u₁) * u₃ := by group
    _ = z * (u₁ * z) * u₃ := by rw [h.comm_z₁]
    _ = z * ((u₁ * u₂) * (u₂ * u₃)) := by rw [h1]; group

theorem mem_B_13
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    u₁ * u₃ ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  rw [h.eq_13]
  exact Subgroup.mul_mem _ T7B.mem_closure_snd
    (Subgroup.mul_mem _ T7B.mem_closure_fst T7B.mem_closure_thd)

theorem sq_13
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) : (u₁ * u₃) * (u₁ * u₃) = 1 :=
  h.hB.2 _ h.mem_B_13

theorem comm₁₃
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) : u₁ * u₃ = u₃ * u₁ :=
  T7B.comm_of_mul_self_eq_one h.sq₁ h.sq₃ h.std.hz.sq h.comm_z₁ h.sq_13

theorem closure_rotate
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₂ * u₃, z, u₃ * u₁} : Set G) =
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact T7B.mem_closure_thd
    · exact T7B.mem_closure_snd
    · rw [← h.comm₁₃]
      exact h.mem_B_13
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · have e : u₁ * u₂ = z * ((u₂ * u₃) * (u₃ * u₁)) := by
        calc u₁ * u₂ = (z * z) * (u₁ * u₂) := by rw [h.std.hz.sq, one_mul]
          _ = z * (z * u₁ * u₂) := by group
          _ = z * (u₁ * z * u₂) := by rw [h.comm_z₁]
          _ = z * (u₂ * z * u₁) := by
              rw [show u₁ * z * u₂ = u₁ * (z * u₂) by group, h.comm_z₂,
                show u₂ * z * u₁ = u₂ * (z * u₁) by group, h.comm_z₁,
                show u₁ * (u₂ * z) = (u₁ * u₂) * z by group,
                show u₂ * (u₁ * z) = (u₂ * u₁) * z by group, h.comm₁₂]
          _ = z * ((u₂ * u₃) * (u₃ * u₁)) := by
              rw [show (u₂ * u₃) * (u₃ * u₁) = u₂ * (u₃ * u₃) * u₁ by group, h.sq₃]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp)))
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)

theorem rotate
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) : Q3T8.Asc77.Hyp22 Ω K' K₃ K z u₂ u₃ u₁
    := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hKK' : K ∈ twinSet Ω K' := by
    rw [twinSet_eq_of_mem_twinSet h.std.hz h.std.hK']
    exact mem_twinSet_self hK h.std.hz
  have hperp : KPerp Ω K' = KPerp Ω K := ((CFSG.ClassicalInvolution.Q3.Q3T7M.l6_3 G Ω hΩ K hK K'
      h.std.hK').1).symm
  have htw : twinSet Ω K' = twinSet Ω K := twinSet_eq_of_mem_twinSet h.std.hz h.std.hK'
  refine
    { std := Q3T8.Asc77.Std7.of_twin h.std h.std.hK' h.hK₃ h.hK₃K'
      perp := by rw [hperp, htw]; exact h.perp
      hK₃ := hKK'
      hK₃K := h.std.hne.symm
      hK₃K' := h.hK₃K.symm
      hu₁ := h.hu₂
      hu₂ := h.hu₃
      hu₃ := h.hu₁
      hB := ?_ }
  rw [h.closure_rotate]
  exact h.hB

theorem isElemAbelian2_closure
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    IsElemAbelian2 (Subgroup.closure ({u₁ * u₂, z} : Set G)) 2 := by
  have hne : u₁ * u₂ ≠ z := by
    intro he
    have hK' : K' ∈ Ω := h.std.hK'.1
    have hK : K ∈ Ω := h.std.stand.mem
    refine Q3T8.Asc77.T7A.not_mem_inf_of_orderOf_four h.std.stand.hyp hK hK' h.std.hne h.hu₂.2 ?_
        h.hu₂.1
    have : u₂ = u₁⁻¹ * z := by rw [← he]; group
    rw [this]
    exact K.mul_mem (K.inv_mem h.hu₁.1) h.std.hz.mem
  have h1 : u₁ * u₂ ≠ 1 := by
    intro he
    have hK' : K' ∈ Ω := h.std.hK'.1
    have hK : K ∈ Ω := h.std.stand.mem
    refine Q3T8.Asc77.T7A.not_mem_inf_of_orderOf_four h.std.stand.hyp hK hK' h.std.hne h.hu₂.2 ?_
        h.hu₂.1
    have : u₂ = u₁⁻¹ := eq_inv_of_mul_eq_one_right he
    rw [this]
    exact K.inv_mem h.hu₁.1
  have hcomm : (u₁ * u₂) * z = z * (u₁ * u₂) := by
    calc (u₁ * u₂) * z = u₁ * (u₂ * z) := by group
      _ = u₁ * (z * u₂) := by rw [h.comm_z₂]
      _ = (u₁ * z) * u₂ := by group
      _ = (z * u₁) * u₂ := by rw [h.comm_z₁]
      _ = z * (u₁ * u₂) := by group
  exact T7A.isElemAbelian2_closure_pair h.sq_12 h.std.hz.sq h1 h.std.hz.ne_one hne hcomm
end Hyp22
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
    CFSG.ClassicalInvolution.Generic.CoreAssembly
open scoped commutatorElement MatrixGroups
section Component
variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem twinShape_of_twin
    (hΦ : Q3T8.Asc77.HypOmega Φ) (D :
    Q3T8.Asc77.OmegaLie Φ) (hcard : D.card = 1) (hgen : omegaGen Φ = ⊤) (i : Fin D.card) (hG2 :
    D.tag i ≠ .G2) (hD4 : D.tag i ≠ .trialityD4)
    {R R' : Subgroup (D.model i).K} (hR : R ∈ fundamentalSubgroups (D.tag i) (D.model i).D)
    (hR' : R' ∈ fundamentalSubgroups (D.tag i) (D.model i).D) (hK : R.map (D.hom i) ∈ Φ)
    (hK'Φ : R'.map (D.hom i) ∈ Φ) {z : X} (hzK : IsUniqueInvolution (R.map (D.hom i)) z)
    (hzK' : IsUniqueInvolution (R'.map (D.hom i)) z)
    (hne : R.map (D.hom i) ≠ R'.map (D.hom i)) :
    R ≠ R' ∧ Commutes R R' ∧
      ∃ x ∈ R, ∃ x' ∈ R', x * x = 1 ∧ x ≠ 1 ∧ x' * x' = 1 ∧ x' ≠ 1 ∧ D.hom i x = z ∧
        D.hom i x' = z := by
  classical
  have hΩ : Uniform.HypOmegaModU (.sl2 3 1) Φ := hΦ.toModU
  have hRM : R ∈ D.cls i := ⟨hR, hK⟩
  have hR'M : R' ∈ D.cls i := ⟨hR', hK'Φ⟩
  have hRR' : R ≠ R' := fun h => hne (by rw [h])
  obtain ⟨hgR, hk3, hinj, ⟨eR⟩⟩ := OmegaLie.facts3 hΩ D hcard hgen i hG2 hD4 hRM
  obtain ⟨-, -, hinj', ⟨eR'⟩⟩ := OmegaLie.facts3 hΩ D hcard hgen i hG2 hD4 hR'M
  obtain ⟨hcomm, -⟩ := Uniform.ih8_twin_data3 hΩ hΦ.exact (D.ker_le_center i) hk3 hgR hK hK'Φ
    hne hzK hzK'
  have hodd : Odd (Nat.card (GaloisField 3 (D.exp i))) := by
    rw [GaloisField.card 3 (D.exp i) (by have := (D.admissible i).2.1; omega)]
    exact (Nat.Prime.odd_of_ne_two Nat.prime_three (by norm_num)).pow
  refine ⟨hRR', hcomm, sl2Inv eR, sl2Inv_mem eR, sl2Inv eR', sl2Inv_mem eR',
    sl2Inv_mul_self hodd eR, sl2Inv_ne_one hodd eR, sl2Inv_mul_self hodd eR',
    sl2Inv_ne_one hodd eR', ?_, ?_⟩
  · have hmem : D.hom i (sl2Inv eR) ∈ R.map (D.hom i) := Subgroup.mem_map_of_mem _ (sl2Inv_mem eR)
    have hsq : D.hom i (sl2Inv eR) * D.hom i (sl2Inv eR) = 1 := by
      rw [← map_mul, sl2Inv_mul_self hodd eR, map_one]
    rcases hzK.unique _ hmem hsq with h | h
    · exact absurd (hinj _ (sl2Inv_mem eR) 1 R.one_mem (by rw [h, map_one])) (sl2Inv_ne_one hodd eR)
    · exact h
  · have hmem : D.hom i (sl2Inv eR') ∈ R'.map (D.hom i) :=
      Subgroup.mem_map_of_mem _ (sl2Inv_mem eR')
    have hsq : D.hom i (sl2Inv eR') * D.hom i (sl2Inv eR') = 1 := by
      rw [← map_mul, sl2Inv_mul_self hodd eR', map_one]
    rcases hzK'.unique _ hmem hsq with h | h
    · exact absurd (hinj' _ (sl2Inv_mem eR') 1 R'.one_mem (by rw [h, map_one]))
        (sl2Inv_ne_one hodd eR')
    · exact h
end Component
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Generic

theorem thmEWithSylow_of_nonToral [Fact Q3T7E.ThmEWithSylow3] (hNT : G2D4Models.G2NonToralGenerate
    3) :
    Q3T7E.ThmEWithSylow3 := Fact.out
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
open scoped commutatorElement MatrixGroups

structure TransSection {X : Type} [Group X] (Φ : Set (Subgroup X)) :
    Prop where
  hyp : Q3T7M.HM Φ
  oddCore : classicalInvolutionOddCore X = ⊥
  gen : omegaGen Φ = ⊤
  trans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L
  aEmpty : ∀ J ∈ Φ, AEmpty Φ J
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected
theorem TransSection.toGen
    {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (h : Q3T8.Asc77.TransSection Φ) : Q3T8.Asc77.GenSection Φ := ⟨h.hyp, h.oddCore, h.gen, h.aEmpty⟩
section Dich
variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem transSection_or_dConnected
    {n :
    ℕ} (h4 : Uniform.Thm4BelowU 3 1 n)
    (hlt : Nat.card X < n) (h : Q3T8.Asc77.GenSection Φ) : DConnected Φ ∨ Q3T8.Asc77.TransSection Φ
        := by
  rcases dConnected_or_transitive25 h4 hlt h.hyp h.oddCore h.aEmpty with hc | ht
  · exact Or.inl hc
  · exact Or.inr ⟨h.hyp, h.oddCore, h.gen, ht, h.aEmpty⟩
end Dich
section Statements

@[expose] def Thm6SectBelow'
    (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n →
      ∀ Φ : Set (Subgroup X), Q3T8.Asc77.GenSection Φ → Φ.Nonempty → (⊤ : Subgroup X) ∉ Φ →
        DEdgeless Φ →
          HasLieType 3 1 Φ .PSL 3 ∨ HasLieType 3 1 Φ .PSU 3 ∨ HasLieType 3 1 Φ .G2 0 ∨
            HasLieType 3 1 Φ .trialityD4 0 ∨ Uniform.HasM11TypeU 3 1 Φ
end Statements

theorem thm6SectBelow'_of_citBelow
    (hP1
    : Ih8SmallEdge 3) {n : ℕ} (hn : Q3T8.Generic.CITBelowU n) :
    Q3T8.Asc77.Thm6SectBelow' n := by
  intro X _ _ hlt Φ hG hne htop hDE
  rcases dConnected_or_transitive25 (Uniform.thm4BelowU_of_citBelowT hn) hlt hG.hyp hG.oddCore
    hG.aEmpty with hc | htrans
  · exfalso
    obtain ⟨K, hK⟩ := hne
    have hall : ∀ J ∈ Φ, J = K := by
      intro J hJ
      rcases Relation.ReflTransGen.cases_head (hc K hK J hJ) with h | ⟨M, ⟨hM, hadj⟩, -⟩
      · exact h.symm
      · exact absurd hadj (hDE K hK M hM)
    have hle : omegaGen Φ ≤ K := by
      unfold omegaGen
      exact iSup₂_le fun J hJ => (hall J hJ) ▸ le_rfl
    rw [hG.gen, top_le_iff] at hle
    exact htop (hle ▸ hK)
  · have hT : Q3T7.TransSect3 Φ := ⟨hG.hyp, hG.oddCore, hG.gen, htrans, hG.aEmpty⟩
    rcases Q3T7.thm6SectBelowU_of hn X hlt Φ hT hne htop hDE with h | h | h | h | h
    · exact Or.inl (hasLieType_of_hasLieTypeU h)
    · exact Or.inr (Or.inl (hasLieType_of_hasLieTypeU h))
    · exact Or.inr (Or.inr (Or.inl (hasLieType_of_hasLieTypeU h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hasLieType_of_hasLieTypeU h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
