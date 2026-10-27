module

public import CFSG.GH74.GLS.Stage1.Thm4.Burnside98
public import CFSG.GH74.GLS.Stage1.Thm4.L98d

public section

namespace CFSG.GH74.GLS.Stage1.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
open scoped commutatorElement

section DOf

variable {G : Type} [Group G] [Finite G] {z : G}

theorem mem_normalizer_Oz {c : G} (hc : c ∈ Cz z) : c ∈ normalizer ((Oz z : Subgroup G) : Set G) :=
  Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => Oz_conj hc hy, fun hy => by
    have := Oz_conj (inv_mem hc) hy
    simpa [mul_assoc] using this⟩

@[expose] def DOf (z : G) (K : Subgroup G) : Subgroup ↥(Cz z) :=
  (centralizerSection K (Oz z)).subgroupOf (Cz z)

end DOf

namespace Ctx98

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {z t : G} {S K : Subgroup G}
  (h : Ctx98 G Lh z t S K)

include h

theorem mem_DOf_iff {x : ↥(Cz z)} : x ∈ DOf z K ↔ ∀ k ∈ K, ⁅k, (x : G)⁆ ∈ Oz z := by
  constructor
  · intro hx
    exact hx.2.2
  · intro hx
    exact ⟨h.mem_normalizer x.2, mem_normalizer_Oz x.2, hx⟩

theorem DOf_normal : (DOf z K).Normal := ⟨fun x hx g => by
  rw [h.mem_DOf_iff] at hx ⊢
  intro k hk
  have hg : (g : G) ∈ Cz z := g.2
  have hk' : (g : G)⁻¹ * k * (g : G) ∈ K := by
    have := (Subgroup.mem_normalizer_iff.1 (h.mem_normalizer (inv_mem hg)) k).1 hk
    simpa using this
  have e : ⁅k, ((g * x * g⁻¹ : ↥(Cz z)) : G)⁆ =
      (g : G) * ⁅(g : G)⁻¹ * k * (g : G), (x : G)⁆ * (g : G)⁻¹ := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact Oz_conj hg (hx _ hk')⟩

theorem fstar_core {c : G} (hc : c ∈ Cz z) (hcomm : ∀ k ∈ K, ⁅k, c⁆ ∈ Oz z) :
    c ∈ zpowers z ⊔ Oz z := by
  haveI := h.DOf_normal
  let zc : ↥(Cz z) := ⟨z, h.z_cen⟩
  have hzc : ∀ g : ↥(Cz z), g * zc = zc * g := fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  have hzD : zc ∈ DOf z K := (h.mem_DOf_iff).2 fun k hk => by
    have : ⁅k, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (h.z_comm hk)
    rw [this]
    exact one_mem _
  have hord : orderOf zc = 2 := by rw [Subgroup.orderOf_mk]; exact h.z_ord
  have hzS : zc ∈ S.subgroupOf (Cz z) := h.z_mem_S
  have hSD : S.subgroupOf (Cz z) ⊓ DOf z K = zpowers zc := by
    apply le_antisymm
    · rintro x ⟨hxS, hxD⟩
      have hxS' : (x : G) ∈ S := hxS
      have hxc : (x : G) ∈ cSec K := by
        refine ⟨h.mem_normalizer x.2, ?_, ?_⟩
        · exact Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => h.pPrimeCoreOf_conj x.2 hy,
            fun hy => by
              have := h.pPrimeCoreOf_conj (inv_mem x.2) hy
              simpa [mul_assoc] using this⟩
        · intro k hk
          have h1 : ⁅k, (x : G)⁆ ∈ Oz z := (h.mem_DOf_iff.1 hxD) k hk
          have h2 : ⁅k, (x : G)⁆ ∈ K := by
            have : (x : G) * k⁻¹ * (x : G)⁻¹ ∈ K :=
              (Subgroup.mem_normalizer_iff.1 (h.mem_normalizer x.2) k⁻¹).1 (inv_mem hk)
            have e : ⁅k, (x : G)⁆ = k * ((x : G) * k⁻¹ * (x : G)⁻¹) := by
              simp only [commutatorElement_def]; group
            rw [e]
            exact mul_mem hk this
          rw [← h.Oz_inf_K]
          exact ⟨h1, h2⟩
      have hxQ : (x : G) ∈ Qof S K := ⟨hxS', hxc⟩
      rw [h.q1] at hxQ
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxQ
      exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa using hk)⟩
    · exact le_inf ((Subgroup.zpowers_le).2 hzS) ((Subgroup.zpowers_le).2 hzD)
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (zpowers zc) (DOf z K) := by
    have := CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer (N := DOf z K) h.sylowC le_top
      (by rw [Subgroup.normalizer_eq_top_iff.2 inferInstance])
    rwa [hSD] at this
  obtain ⟨M, hMD, hMn, hModd, hDle⟩ := exists_odd_normal_complement inferInstance hord hzc hzD hSyl
  have hMle : M ≤ pPrimeCore 2 ↥(Cz z) := le_sSup ⟨hMn, (Nat.coprime_two_left).2 hModd⟩
  have hcD : (⟨c, hc⟩ : ↥(Cz z)) ∈ DOf z K := (h.mem_DOf_iff).2 hcomm
  have h2 := Subgroup.mem_map_of_mem (Cz z).subtype (hDle hcD)
  rw [Subgroup.map_sup] at h2
  have h3 : (zpowers zc).map (Cz z).subtype = zpowers z := by
    rw [MonoidHom.map_zpowers]; rfl
  rw [h3] at h2
  have h4 : M.map (Cz z).subtype ≤ Oz z := fun y ⟨m, hm, hmy⟩ => ⟨m, hMle hm, hmy⟩
  exact (sup_le (h4.trans le_sup_right) le_sup_left : M.map (Cz z).subtype ⊔ zpowers z ≤
    zpowers z ⊔ Oz z) h2

end Ctx98

theorem step9_8_fstar : Step9_8_Fstar := by
  intro G _ _ Lh _ z t S K hstd hr1 hq1 c hc hcomm
  exact (show Ctx98 G Lh z t S K from ⟨hstd, hr1, hq1⟩).fstar_core hc hcomm

end CFSG.GH74.GLS.Stage1.Thm4
