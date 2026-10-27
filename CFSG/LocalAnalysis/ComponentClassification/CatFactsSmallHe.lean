module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5Elim
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallHeModel
public import CFSG.Sporadic.HeldB.AlmostSimple
public import CFSG.LieType.Steinberg.CentralExt.Model

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.Sporadic.HeldB
open CFSG.ComponentClassification.FixedCommutingProduct

theorem exists_ne_comm_of_center_eq_bot {G : Type*} [Group G] [Nontrivial G]
    (h : center G = ⊥) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  have : x ∈ center G := mem_center_iff.2 fun g => (hc g x)
  rw [h, mem_bot] at this
  exact hx this

theorem cfHeNoA5 : CFHeNoA5 := by
  intro Y _ _ he₀ t ht L hLC hLp hφ
  obtain ⟨e₀⟩ := he₀
  obtain ⟨φ⟩ := hφ
  have hF : CFSG.generalizedFitting Y = GeneralizedFitting.subgroup Y :=
    CFSG.generalizedFitting_eq_componentClassification Y
  set F := GeneralizedFitting.subgroup Y with hFdef
  have : F.Normal := GeneralizedFitting.normal Y
  let e : F ≃* Blueprint.NativeSporadic.He := (MulEquiv.subgroupCongr hF.symm).trans e₀
  let eP : F ≃* heP := e.trans heEquivP
  have hsimple : IsSimpleGroup F := by
    have : IsSimpleGroup heP := heP_simple
    exact (MulEquiv.isSimpleGroup_congr eP).2 this
  have : Nontrivial F := hsimple.toNontrivial
  have hnab : ∃ a b : F, a * b ≠ b * a := by
    have hZ : center F = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have h1 : eP z ∈ center heP := by
        rw [mem_center_iff]
        intro g
        obtain ⟨f, rfl⟩ := eP.surjective g
        rw [← map_mul, ← map_mul, (mem_center_iff.1 hz) f]
      rw [heP_center_eq_bot, mem_bot] at h1
      exact (mem_bot).2 (eP.injective (by rw [h1, map_one]))
    exact exists_ne_comm_of_center_eq_bot hZ
  have hcentF := centralizer_generalizedFitting_eq_bot hsimple hnab
  have hidx := index_generalizedFitting_le_two_of_outer
    CFSG.Sporadic.Schreier.AT_He_Schreier.1 hsimple hnab e
  set C := centralizer ({t} : Set Y)
  have hL₁sn : (L.subgroupOf C).IsSubnormal := hLp.choose_spec.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL₁perf : Group.IsPerfect (L.subgroupOf C) :=
    CatalogueBHeldSmallCore.pComponent_perfect 2 _ hLp
  obtain ⟨h5, h8⟩ := five_dvd_not_eight_of_oddBar φ
  have hLperf : ⁅L, L⁆ = L := by
    have h1 : ⁅L.subgroupOf C, L.subgroupOf C⁆ = L.subgroupOf C := isPerfect_iff.1 hL₁perf
    have h2 := congrArg (map C.subtype) h1
    rwa [map_commutator, subgroupOf_map_subtype, inf_eq_left.2 hLC] at h2
  have hcommY : commutator Y ≤ F := by
    have hcard : Nat.card (Y ⧸ F) ≤ 2 := by rw [← index_eq_card]; exact hidx
    have : IsCyclic (Y ⧸ F) := LieType.Steinberg.isCyclic_of_card_le_two hcard
    exact Normal.quotient_commutative_iff_commutator_le.1 inferInstance
  have hLF : L ≤ F := by
    rw [← hLperf]
    exact (commutator_mono le_top le_top).trans hcommY
  let α : MulAut F := MulAut.conjNormal t
  have hα : orderOf α = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
    · intro h1
      have ht1 : t ∈ centralizer (F : Set Y) := by
        rw [mem_centralizer_iff]
        intro f hf
        have h2 := congrArg (fun β : MulAut F => ((β ⟨f, hf⟩ : F) : Y)) h1
        simp only [α, MulAut.conjNormal_apply, MulAut.one_apply] at h2
        calc f * t = (t * f * t⁻¹) * t := by rw [h2]
          _ = t * f := by group
      rw [hcentF, mem_bot] at ht1
      rw [ht1, orderOf_one] at ht
      exact absurd ht (by norm_num)
  let ψ : fixedSubgroup α →* C :=
    { toFun := fun f => ⟨((f : F) : Y), mem_centralizer_singleton_iff.2 (by
        have h1 : α (f : F) = f := f.2
        have h2 := congrArg Subtype.val h1
        simp only [α, MulAut.conjNormal_apply] at h2
        calc ((f : F) : Y) * t = (t * (f : F) * t⁻¹) * t := by rw [h2]
          _ = t * (f : F) := by group)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hψ : Function.Injective ψ := fun a b h => by
    have h' := congrArg (fun x : C => (x : Y)) h
    exact Subtype.ext (Subtype.ext h')
  have hrange : L.subgroupOf C ≤ ψ.range := by
    intro l hl
    have hlF : (l : Y) ∈ F := hLF hl
    have hfix : (⟨(l : Y), hlF⟩ : F) ∈ fixedSubgroup α := by
      show α ⟨(l : Y), hlF⟩ = ⟨(l : Y), hlF⟩
      apply Subtype.ext
      simp only [α, MulAut.conjNormal_apply]
      have := mem_centralizer_singleton_iff.1 l.2
      calc t * (l : Y) * t⁻¹ = (l : Y) * t * t⁻¹ := by rw [this]
        _ = l := by group
    exact ⟨⟨_, hfix⟩, rfl⟩
  have hcardL : Nat.card ((L.subgroupOf C).comap ψ) = Nat.card L := by
    rw [← card_map_of_injective hψ, map_comap_eq, inf_eq_right.2 hrange,
      Nat.card_congr (subgroupOfEquivOfLe hLC).toEquiv]
  have hgood := He.good5_fixedSubgroup eP α hα _ (hL₁sn.comap ψ) (hcardL ▸ h5)
  exact h8 (hcardL ▸ hgood)

end CFSG.ComponentClassification.CatFactsSmall
