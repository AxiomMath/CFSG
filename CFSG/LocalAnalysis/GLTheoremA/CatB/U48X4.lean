module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48X3
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48X2


public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X4

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X2
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X3
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (SU4 fieldSU4 fieldFactor4)
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K)
open scoped commutatorElement



variable {G : Type} [Group G] [Finite G]

theorem derived_three_in_ipart {I : Subgroup G} {γ : MulAut SU4}
    (hγ3 : γ ^ 3 = 1) (hff : fieldFactor4 γ ≠ 1) (hcardF : Nat.card (fixSub γ) = 25920)
    (ψ : ↥I →* ↥(fixSub γ)) (hψs : Function.Surjective ψ) (hψk : ¬ 3 ∣ Nat.card ψ.ker)
    {y : G} (hyI : y ∈ I) (hy3 : y ^ 3 = 1) (hyc : IsCentralIn 3 y I) :
    ∃ Q : Subgroup G, IsPGroup 3 Q ∧ Q ≤ ⁅I ⊓ Subgroup.centralizer ({y} : Set G),
        I ⊓ Subgroup.centralizer ({y} : Set G)⁆ ∧
      ∃ g ∈ Q, ∃ g' ∈ Q, g * g' ≠ g' * g := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, a, hg, hκ⟩ := ipart_central_conj hγ3 hff hcardF ψ hψs hψk hyI hyc
  set z : SU4 := ((ψ ⟨y, hyI⟩ : ↥(fixSub γ)) : SU4) with hzdef
  set φ : K ≃+* K := fieldFactor4 γ with hφdef
  have hφ3 : φ ^ 3 = 1 := by rw [hφdef, ← map_pow, hγ3, map_one]
  set κ : MulAut SU4 := MulAut.conj g⁻¹ with hκdef
  have hκapp : ∀ x : SU4, κ x = g⁻¹ * x * g := fun x => by
    rw [hκdef, MulAut.conj_apply, inv_inv]
  set Ch : Subgroup SU4 := Subgroup.centralizer ({z} : Set SU4) ⊓ fixSub γ with hChdef
  have hzz : g⁻¹ * tau4 (.ofAdd fun _ => a) * g = z := by
    rw [← hg]; group
  have hκC0 : ∀ x ∈ C0 a φ, κ x ∈ Ch := by
    intro x hx
    obtain ⟨hxc, hxf⟩ := mem_C0.1 hx
    rw [hκapp, hChdef, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨?_, hκ x (mem_fixSub.2 hxf)⟩
    rw [← hzz]
    calc g⁻¹ * x * g * (g⁻¹ * tau4 (.ofAdd fun _ => a) * g)
        = g⁻¹ * (x * tau4 (.ofAdd fun _ => a)) * g := by group
      _ = g⁻¹ * (tau4 (.ofAdd fun _ => a) * x) * g := by rw [hxc]
      _ = g⁻¹ * tau4 (.ofAdd fun _ => a) * g * (g⁻¹ * x * g) := by group
  have hle : (C0 a φ).map κ.toMonoidHom ≤ Ch := by
    rintro _ ⟨x, hx, rfl⟩
    exact hκC0 x hx
  have hκE : ∀ e ∈ ⁅C0 a φ, C0 a φ⁆, κ e ∈ ⁅Ch, Ch⁆ := by
    intro e he
    have hmap : κ e ∈ (⁅C0 a φ, C0 a φ⁆).map κ.toMonoidHom := Subgroup.mem_map_of_mem _ he
    rw [Subgroup.map_commutator] at hmap
    exact Subgroup.commutator_mono hle hle hmap
  set ψ' : ↥I →* SU4 := (fixSub γ).subtype.comp ψ with hψ'
  have hψ'app : ∀ x : ↥I, ψ' x = ((ψ x : ↥(fixSub γ)) : SU4) := fun x => rfl
  let yI : ↥I := ⟨y, hyI⟩
  have hyI3 : yI ^ 3 = 1 := Subtype.ext (by simpa using hy3)
  set HI : Subgroup ↥I := (I ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf I with hHI
  have hmapHI : HI.map ψ' = Ch := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hxc : (x : G) ∈ I ⊓ Subgroup.centralizer ({y} : Set G) := Subgroup.mem_subgroupOf.1 hx
      have hcomm : (x : G) * y = y * (x : G) := Subgroup.mem_centralizer_singleton_iff.1 hxc.2
      have hxy : x * yI = yI * x := Subtype.ext hcomm
      have h2 := congrArg ψ hxy
      rw [map_mul, map_mul] at h2
      rw [hψ'app, hChdef, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      refine ⟨?_, (ψ x).2⟩
      have h3 := congrArg (fun t : ↥(fixSub γ) => (t : SU4)) h2
      simpa [hzdef] using h3
    · rintro m hm
      rw [hChdef, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hm
      have hmF : m ∈ fixSub γ := hm.2
      have hrange : (⟨m, hmF⟩ : ↥(fixSub γ)) ∈ ψ.range := hψs _ |> fun ⟨x, hx⟩ => ⟨x, hx⟩
      have hc : (⟨m, hmF⟩ : ↥(fixSub γ)) * ψ yI = ψ yI * (⟨m, hmF⟩ : ↥(fixSub γ)) := by
        apply Subtype.ext
        simpa [hzdef] using hm.1
      obtain ⟨h, hh, hψh⟩ := exists_mem_centralizer_lift Nat.prime_three ψ hψk hyI3 hrange hc
      refine ⟨h, ?_, ?_⟩
      · rw [hHI, SetLike.mem_coe, Subgroup.mem_subgroupOf]
        refine ⟨h.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        have := congrArg (fun t : ↥I => (t : G)) hh
        simpa using this
      · rw [hψ'app, hψh]
  set D : Subgroup ↥I := ⁅HI, HI⁆ with hD
  set π : ↥D →* SU4 := ψ'.comp D.subtype with hπ
  have hrange : π.range = ⁅Ch, Ch⁆ := by
    rw [hπ, MonoidHom.range_comp, Subgroup.range_subtype, hD, Subgroup.map_commutator, hmapHI]
  have hkerle : ¬ 3 ∣ Nat.card π.ker := by
    intro h3
    apply hψk
    refine h3.trans ?_
    rw [← Subgroup.card_map_of_injective (K := π.ker) (f := D.subtype) D.subtype_injective]
    apply Subgroup.card_dvd_of_le
    rintro _ ⟨x, hx, rfl⟩
    have hx1 : ψ' x = 1 := hx
    rw [MonoidHom.mem_ker]
    rw [hψ'app] at hx1
    exact Subtype.ext (by simpa using hx1)
  obtain ⟨E, hE3, hEC, g₁, hg₁, g₂, hg₂, hne⟩ := exists_three_derived_noncomm a hφ3
  set E₁ : Subgroup SU4 := E.map κ.toMonoidHom with hE₁
  have hE₁3 : IsPGroup 3 E₁ := hE3.map κ.toMonoidHom
  have hE₁π : E₁ ≤ π.range := by
    rw [hrange]
    rintro _ ⟨e, he, rfl⟩
    exact hκE e (hEC he)
  obtain ⟨W, hW3, hWmap, -⟩ := exists_pSubgroup_lift Nat.prime_three π hkerle hE₁3 hE₁π
  have hsub : D.map I.subtype ≤
      ⁅I ⊓ Subgroup.centralizer ({y} : Set G), I ⊓ Subgroup.centralizer ({y} : Set G)⁆ := by
    rw [hD, Subgroup.map_commutator, hHI, Subgroup.subgroupOf_map_subtype]
    rw [inf_eq_left.2 inf_le_left]
  refine ⟨(W.map D.subtype).map I.subtype, (hW3.map D.subtype).map I.subtype, ?_, ?_⟩
  · rintro _ ⟨x, ⟨w, hw, rfl⟩, rfl⟩
    exact hsub (Subgroup.mem_map_of_mem _ w.2)
  · have hw : ∀ g ∈ E, ∃ w ∈ W, π w = κ g := by
      intro g hg
      have hmem : κ g ∈ W.map π := by
        rw [hWmap]
        exact Subgroup.mem_map_of_mem _ hg
      obtain ⟨w, hw, hπw⟩ := Subgroup.mem_map.1 hmem
      exact ⟨w, hw, hπw⟩
    obtain ⟨w₁, hw₁, hπ₁⟩ := hw g₁ hg₁
    obtain ⟨w₂, hw₂, hπ₂⟩ := hw g₂ hg₂
    refine ⟨I.subtype (D.subtype w₁), Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hw₁),
      I.subtype (D.subtype w₂), Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hw₂), ?_⟩
    intro hcomm
    apply hne
    have h1 : w₁ * w₂ = w₂ * w₁ := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hcomm
    have h3 := congrArg π h1
    rw [map_mul, map_mul, hπ₁, hπ₂] at h3
    have h4 : κ (g₁ * g₂) = κ (g₂ * g₁) := by
      rw [map_mul, map_mul]
      exact h3
    exact κ.injective h4

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X4
