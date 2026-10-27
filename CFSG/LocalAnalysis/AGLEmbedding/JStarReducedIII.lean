module

public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.IIIaLists
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedLinTwo
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamiliesAux
import CFSG.LocalAnalysis.AGLEmbedding.KFactsFamilies

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem jStarElimData_of_hom {Y L : Type} [Group Y] [Group L] [Finite L] {p n : ℕ}
    [Fact p.Prime] (ρ : Y →* MulAut L)
    (hinn : (MulAut.conj : L →* MulAut L).range ≤ ρ.range) (hker : IsPGroup p ρ.ker)
    (hcard : ∀ S : Subgroup Y, IsPGroup p S → Nat.card S ∣ p ^ n * n) {Jt : Subgroup Y}
    (φ : Jt →* PSL2GF p n) (hsurj : Function.Surjective φ) (hcop : p.Coprime (Nat.card φ.ker))
    (hinj : Jt ⊓ ρ.ker = ⊥) : JStarElimData L p n := by
  have hinj' : Function.Injective (ρ.comp Jt.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : (x : Y) ∈ Jt ⊓ ρ.ker := ⟨x.2, hx⟩
    rw [hinj, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext hx')
  let e : Jt ≃* (ρ.comp Jt.subtype).range := MonoidHom.ofInjective hinj'
  refine ⟨ρ.range, (ρ.comp Jt.subtype).range, hinn, ?_, ?_, φ.comp e.symm.toMonoidHom,
    hsurj.comp e.symm.surjective, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · intro S hS hSp
    calc Nat.card S = Nat.card ((S.comap ρ).map ρ) := by rw [Subgroup.map_comap_eq_self hS]
      _ ∣ Nat.card (S.comap ρ) := Subgroup.card_map_dvd _ _
      _ ∣ p ^ n * n := hcard _ (hSp.comap_of_ker_isPGroup ρ hker)
  · have hc : Nat.card (φ.comp e.symm.toMonoidHom).ker = Nat.card φ.ker :=
      Nat.card_congr (e.symm.toEquiv.subtypeEquiv fun _ => Iff.rfl)
    rw [hc]
    exact hcop

namespace JStarHyp

variable {Y : Type} [Group Y] [Finite Y] {p n : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
  {Y₀ Jt Xt : Subgroup Y} {φ : Jt →* PSL2GF p n}

open CFSG.ComponentClassification in
theorem jStarElimData_center_quotient (h : JStarHyp p n Rb Y₀ Jt Xt φ) {K : Subgroup Y}
    (hK : IsComponentOf K ⊤) (huniq : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype) :
    JStarElimData (K ⧸ Subgroup.center K) p n := by
  have hp : p.Prime := Fact.out
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have hmem : ∀ c ∈ Subgroup.centralizer (K : Set Y), orderOf c = p → c ∈ K :=
    fun c hc hcp => mem_of_mem_centralizer_of_orderOf_eq Rb hKn
      (fun c hc hcp => Subgroup.map_subtype_le _ (hcent c hc hcp)) hc hcp
  have hCp : IsPGroup p (Subgroup.centralizer (K : Set Y)) :=
    isPGroup_centralizer_of_forall_mem hp h.ne_two h.red.core_eq_bot hKn hmem
  let ρ : Y →* MulAut (K ⧸ Subgroup.center K) :=
    (PerfectAutomorphisms.centerQuotientHom K).comp MulAut.conjNormal
  have hρK : ∀ k : K, ρ k = MulAut.conj (QuotientGroup.mk' (Subgroup.center K) k) := by
    intro k
    rw [← OuterAutomorphisms.centerQuotient_conj]
    refine congrArg (PerfectAutomorphisms.centerQuotientHom K) ?_
    ext x
    simp [MulAut.conjNormal_apply, MulAut.conj_apply]
  have hker : ρ.ker ≤ Subgroup.centralizer (K : Set Y) := by
    intro y hy
    have h1 : MulAut.conjNormal y = (1 : MulAut K) :=
      PerfectAutomorphisms.centerQuotientHom_injective K (hy.trans (map_one _).symm)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h2 := congrArg Subtype.val (DFunLike.congr_fun h1 ⟨x, hx⟩)
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    calc x * y = y * x * y⁻¹ * y := by rw [h2]
      _ = y * x := by group
  have hkerp : IsPGroup p ρ.ker := hCp.to_le hker
  refine jStarElimData_of_hom ρ ?_ hkerp h.card_dvd φ h.surj h.coprime ?_
  · rintro _ ⟨l, rfl⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) l
    exact ⟨k, hρK k⟩
  · refine h.eq_bot_of_isPGroup inf_le_left ?_ (hkerp.to_le inf_le_right)
    exact (le_inf Subgroup.le_normalizer (by rw [Subgroup.normalizer_eq_top]; exact le_top)).trans
      Subgroup.inf_normalizer_le_normalizer_inf

theorem jStarConcl_of_unique_component (h : JStarHyp p n Rb Y₀ Jt Xt φ)
    (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor)
    (hEL : KFactJStarElimLie) (hEA : KFactJStarElimAlt) (hES : KFactJStarElimSpor)
    {K : Subgroup Y} (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K)
    (hnc : ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y))
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype) :
    JStarConcl p n Jt := by
  have hp2 := h.ne_two
  have hn := h.three_le
  have hdata := h.jStarElimData_center_quotient hK huniq hcent
  obtain ⟨i, ⟨e⟩⟩ := h.catalog.isCatalogGroup_center_quotient hK
  cases i with
  | cyclic q hq =>
    exact (not_nonempty_mulEquiv_zmod
      (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.2.2)
      ⟨e⟩).elim
  | alternating m hm =>
    obtain rfl := hP1A p Y Rb Y₀ h.red h.catalog K hK huniq hnc hcent m hm ⟨e⟩
    exact (hEA p n hp2 hn _ ⟨e⟩ hdata).elim
  | lie d =>
    by_cases hL2 : ∃ m, IsLinTwoIndex p m d
    · obtain ⟨m, hm⟩ := hL2
      exact h.jStarConcl_of_isLinTwoIndex hK huniq hcent hm ⟨e⟩
    · exact (hEL p n hp2 hn _ hK.2.2.2 d
        (hP1L p Y Rb Y₀ h.red h.catalog K hK huniq hnc hcent d ⟨e⟩) hL2 ⟨e⟩ hdata).elim
  | sporadic s =>
    exact (hES p n hp2 hn _ s
      (hP1S p Y Rb Y₀ h.red h.catalog K hK huniq hnc hcent s ⟨e⟩) ⟨e⟩ hdata).elim

end JStarHyp

theorem jStarIII (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor)
    (hEL : KFactJStarElimLie) (hEA : KFactJStarElimAlt) (hES : KFactJStarElimSpor) :
    StmtJStarIII := fun h _ hK huniq hnc hcent =>
  h.jStarConcl_of_unique_component hP1L hP1A hP1S hEL hEA hES hK huniq hnc hcent

end CFSG.AGLEmbedding
