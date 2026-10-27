module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Lift
public import CFSG.GH74.GLS.Stage2.Final.L26.G2Basic
public import CFSG.GH74.GLS.Stage2.Final.L26.G2Three

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.GH74.GLS.Stage2.Final CFSG.ComponentClassification CFSG.Blueprint
open scoped commutatorElement

section Perfect

variable {Y : Type} [Group Y]

theorem perfect_le_left_of_commute {A B K : Subgroup Y} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hsol : Group.IsSolvable ↥B) (hK : Group.IsPerfect ↥K) (hKAB : K ≤ A ⊔ B) : K ≤ A := by
  have hAle : A ≤ A ⊔ B := le_sup_left
  have hN : (A.subgroupOf (A ⊔ B)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAle]
    exact sup_le Subgroup.le_normalizer (L26.le_normalizer_of_pairwise_commute hcomm)
  let f : ↥B →* ↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B) :=
    (QuotientGroup.mk' (A.subgroupOf (A ⊔ B))).comp (Subgroup.inclusion le_sup_right)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, b, hb, rfl⟩ := L26.exists_mul_of_mem_sup_of_commute hcomm hy
    refine ⟨⟨b, hb⟩, ?_⟩
    show (QuotientGroup.mk (⟨b, (le_sup_right : B ≤ A ⊔ B) hb⟩ : ↥(A ⊔ B)) : ↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B)) =
      QuotientGroup.mk ⟨a * b, hy⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show (b⁻¹ * (a * b) : Y) ∈ A
    have : b⁻¹ * (a * b) = a := by
      rw [hcomm a ha b hb, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]
    exact ha
  have : Group.IsSolvable (↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B)) :=
    Group.isSolvable_of_surjective (f := f) hf
  let g : ↥K →* ↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B) :=
    (QuotientGroup.mk' (A.subgroupOf (A ⊔ B))).comp (Subgroup.inclusion hKAB)
  have hrange : Group.IsPerfect ↥g.range :=
    Group.IsPerfect.ofSurjective (f := g.rangeRestrict) g.rangeRestrict_surjective
  have hbot : g.range = ⊥ := by
    by_contra hne
    have : Nontrivial ↥g.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable ↥g.range inferInstance
  intro k hk
  have h1 : g ⟨k, hk⟩ = 1 := by
    have : g ⟨k, hk⟩ ∈ g.range := ⟨⟨k, hk⟩, rfl⟩
    rw [hbot] at this
    exact this
  have h2 : (QuotientGroup.mk (⟨k, hKAB hk⟩ : ↥(A ⊔ B)) : ↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B)) = 1 := h1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
  exact h2

end Perfect

section Three

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {r₁ r₂ : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem g3_components (h : G2Shape z S r₁ 3 L₁ L₂) :
    IsComponent L₁ ∧ ∀ K : Subgroup (CentralizerBar z), IsComponent K → K = L₁ := by
  obtain ⟨hodd₁, hodd₂, hg₁, hprod, hm₁, hm₂, -, h3, -, -, -, -⟩ := h
  obtain ⟨hsup, hcomm, hcard⟩ := hprod
  have hc₁ : IsComponent L₁ :=
    L26.isComponent_of_sl2_pair hsup hcomm (LBar_normal z) hodd₁ (by omega) hm₁
  refine ⟨hc₁, fun K hK => ?_⟩
  have hKF : K ≤ generalizedFitting (CentralizerBar z) :=
    (CFSG.LocalCores.component_le_layer hK).trans le_sup_right
  have hKL : K ≤ L₁ ⊔ L₂ := by
    rw [(h3 rfl).2] at hKF
    rw [hsup]
    exact hKF.trans (Subgroup.map_subtype_le _)
  have hsol₂ : Group.IsSolvable ↥L₂ := L26.isSolvable_of_hasSL2Model_three' hm₂
  have hKL₁ : K ≤ L₁ := perfect_le_left_of_commute hcomm hsol₂ hK.1.1 hKL
  have hsub : (K.subgroupOf L₁).IsSubnormal := (CFSG.LocalCores.component_overgroup hK hKL₁).2
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hc₁.1 hsub with
    htop | hcen
  · apply le_antisymm hKL₁
    intro y hy
    have : (⟨y, hy⟩ : ↥L₁) ∈ K.subgroupOf L₁ := by rw [htop]; trivial
    exact this
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hK.1
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have h1 : (⟨(a : CentralizerBar z), hKL₁ a.2⟩ : ↥L₁) ∈ center ↥L₁ := hcen a.2
    have h2 := Subgroup.mem_center_iff.mp h1 ⟨(b : CentralizerBar z), hKL₁ b.2⟩
    have h3 : (a : CentralizerBar z) * b = b * a := congrArg Subtype.val h2.symm
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext h3


structure Pair3Facts (z : G) (r₁ r₂ : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)) : Prop where
  odd₁ : Odd r₁
  odd₂ : Odd r₂
  prod : IsCentralProd L₁ L₂ (LBar z)
  sl₁ : HasSL2Model ↥L₁ (fun r => r = r₁)
  sl₂ : HasSL2Model ↥L₂ (fun r => r = r₂)
  fitting_le : generalizedFitting (CentralizerBar z) ≤ LBar z

theorem zbarC_mem_inf3 (hp : Pair3Facts z r₁ r₂ L₁ L₂) :
    toBar z ⟨z, mem_Cen_self z⟩ ∈ L₁ ⊓ L₂ := by
  have hc := toBar_z_mem_center z
  have hF : toBar z ⟨z, mem_Cen_self z⟩ ∈ generalizedFitting (CentralizerBar z) := by
    refine CFSG.centralizer_generalizedFitting_le (CentralizerBar z) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro f _
    exact Subgroup.mem_center_iff.mp hc f
  replace hF := hp.fitting_le hF
  rw [← hp.prod.1] at hF
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute' hp.prod.2.1 hF
  have hcen := Subgroup.mem_center_iff.mp hc
  have hacen : ∀ c ∈ L₁, a * c = c * a := by
    intro c hc1
    have h1 := hcen c
    rw [hab] at h1
    have h2 : b * c = c * b := (hp.prod.2.1 c hc1 b hb).symm
    have : a * c * b = c * a * b := by
      calc a * c * b = a * (c * b) := by rw [mul_assoc]
        _ = a * (b * c) := by rw [h2]
        _ = a * b * c := by rw [mul_assoc]
        _ = c * (a * b) := h1.symm
        _ = c * a * b := by rw [mul_assoc]
    exact mul_right_cancel this
  have hbcen : ∀ d ∈ L₂, b * d = d * b := by
    intro d hd
    have h1 := hcen d
    rw [hab] at h1
    have h2 : a * d = d * a := hp.prod.2.1 a ha d hd
    have : a * (b * d) = a * (d * b) := by
      calc a * (b * d) = a * b * d := by rw [mul_assoc]
        _ = d * (a * b) := h1.symm
        _ = d * a * b := by rw [mul_assoc]
        _ = a * d * b := by rw [h2]
        _ = a * (d * b) := by rw [mul_assoc]
    exact mul_left_cancel this
  have key : ∀ {L M : Subgroup (CentralizerBar z)} {r : ℕ}, Odd r →
      (∀ a ∈ L, ∀ b ∈ M, a * b = b * a) →
      Nat.card ↥(L ⊓ M) = 2 → HasSL2Model ↥L (fun s => s = r) → ∀ a ∈ L,
      (∀ c ∈ L, a * c = c * a) → a ∈ M := by
    intro L M r hr hLM hW hsl a ha hac
    have hZc : Nat.card ↥((center ↥L).map L.subtype) = 2 := by
      rw [Subgroup.card_map_of_injective L.subtype_injective]
      exact card_center_of_hasSL2Model hr hsl
    have hle : L ⊓ M ≤ (center ↥L).map L.subtype := by
      intro w hw
      refine Subgroup.mem_map.2 ⟨⟨w, hw.1⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro c
      exact Subtype.ext (hLM c.1 c.2 w hw.2)
    have heq : L ⊓ M = (center ↥L).map L.subtype :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hW, hZc])
    have haZ : a ∈ (center ↥L).map L.subtype := by
      refine Subgroup.mem_map.2 ⟨⟨a, ha⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro c
      exact Subtype.ext (hac c.1 c.2).symm
    rw [← heq] at haZ
    exact haZ.2
  have haL₂ : a ∈ L₂ := key hp.odd₁ hp.prod.2.1 hp.prod.2.2 hp.sl₁ a ha hacen
  have hbL₁ : b ∈ L₁ := by
    refine key (L := L₂) (M := L₁) hp.odd₂ (fun x hx y hy => (hp.prod.2.1 y hy x hx).symm) ?_ hp.sl₂ b hb hbcen
    rw [inf_comm]
    exact hp.prod.2.2
  rw [hab]
  exact ⟨L₁.mul_mem ha hbL₁, L₂.mul_mem haL₂ hb⟩


end Three

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
