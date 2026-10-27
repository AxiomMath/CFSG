module

public import CFSG.ClassicalInvolution.Q3.TL3S8Zstar
public import CFSG.Goldschmidt.Steps.G310Comp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

theorem goldschmidtSimpleType_of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : goldschmidtSimpleType L) : goldschmidtSimpleType L' := by
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ |
    ⟨p, f, hp, hodd, hf0, h5, hmod, ⟨e'⟩⟩ | ⟨m, hm, hcard⟩ | he'
  · exact Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans e'⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hodd, hf0, h5, hmod, ⟨e.symm.trans e'⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨m, hm, by rw [← Nat.card_congr e.toEquiv, hcard]⟩))))
  · obtain ⟨e'⟩ := he'
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.symm.trans e'⟩))))

variable {G : Type} [Group G] [Finite G]


theorem goldschmidt_fstar [IsSimpleGroup (genFittingFStar G)]
    (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a) (hO : classicalInvolutionOddCore G = ⊥)
    (T : Sylow 2 G) {A : Subgroup G} (hA1 : A ≠ ⊥) (hAT : A ≤ (T : Subgroup G))
    (hAab : IsMulCommutative A) (hcl : fusionStronglyClosed (A : Set G) (T : Subgroup G)) :
    A ≤ genFittingFStar G ∧ goldschmidtSimpleType ↥(genFittingFStar G) := by
  obtain ⟨ha, -, hc⟩ :=
    CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian G T A hAT hAab hcl
  set M : Subgroup G := Subgroup.normalClosure (A : Set G) with hM
  set F : Subgroup G := genFittingFStar G with hFdef
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hFn : F.Normal := genFittingFStar_normal G
  have hAM : A ≤ M := Subgroup.le_normalClosure
  obtain ⟨a₀, ha₀A, ha₀1⟩ : ∃ a ∈ A, a ≠ 1 := (Subgroup.bot_or_exists_ne_one A).resolve_left hA1
  have hFA : F ≤ M := genFittingFStar_le_of_normal hnab hMn (hAM ha₀A) ha₀1
  have hC : Subgroup.centralizer (F : Set G) = ⊥ := centralizer_genFittingFStar_eq_bot hnab
  have hO' : goldschmidtOddCore G = ⊥ := hO
  have hodd : goldschmidtOddCore ↥M = ⊥ :=
    CFSG.Goldschmidt.G310.goldschmidtOddCore_eq_bot_of_isSubnormal hO' hMn.isSubnormal
  set π := QuotientGroup.mk' (goldschmidtOddCore ↥M) with hπ
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hodd
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  set K : Subgroup (↥M ⧸ goldschmidtOddCore ↥M) := (F.subgroupOf M).map π with hK
  have hKn : K.Normal := (Subgroup.normal_subgroupOf).map π (QuotientGroup.mk'_surjective _)
  let e : ↥K ≃* ↥F :=
    (Subgroup.equivMapOfInjective (F.subgroupOf M) π hπinj).symm.trans
      (Subgroup.subgroupOfEquivOfLe hFA)
  have hKs : IsSimpleGroup ↥K := e.isSimpleGroup
  have hKnab : ∃ a b : ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e.symm a, e.symm b, fun h' => hab (e.symm.injective ?_)⟩
    rw [map_mul, map_mul, h']
  obtain ⟨hquasi, -⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hKnab
  have hcomp : IsComponentOf K ⊤ :=
    ⟨le_top, IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤),
      Group.isPerfect_def.mp hquasi.1, hquasi.2.1⟩
  have hcentK : ∀ x : ↥M ⧸ goldschmidtOddCore ↥M, (∀ k ∈ K, k * x = x * k) → x = 1 := by
    intro x hx
    obtain ⟨m, rfl⟩ := hπsurj x
    have hm : (m : G) ∈ Subgroup.centralizer (F : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have h1 := hx (π ⟨f, hFA hf⟩)
        (Subgroup.mem_map.mpr ⟨⟨f, hFA hf⟩, Subgroup.mem_subgroupOf.mpr hf, rfl⟩)
      rw [← map_mul, ← map_mul] at h1
      have h2 := congrArg Subtype.val (hπinj h1)
      simpa using h2
    rw [hC, Subgroup.mem_bot] at hm
    have : m = 1 := Subtype.ext hm
    rw [this, map_one]
  have hle : ∀ L : Subgroup (↥M ⧸ goldschmidtOddCore ↥M), ⁅L, K⁆ = ⊥ → L = ⊥ := by
    intro L hL
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hL
    rw [eq_bot_iff]
    intro l hl
    rw [Subgroup.mem_bot]
    exact hcentK l fun k hk => (Subgroup.mem_centralizer_iff.mp (hL hl)) k hk
  have hE : goldschmidtLayer (↥M ⧸ goldschmidtOddCore ↥M) ≤ K := by
    rw [goldschmidtLayer.eq_sSup]
    refine sSup_le fun L hL => ?_
    rcases CFSG.Goldschmidt.N8a _ L K hL hcomp.2.1 with h | h
    · exact h
    · exfalso
      have hL0 := hle L h
      obtain ⟨-, hsimp⟩ := hL.2.2
      haveI : Subsingleton ↥L := ⟨fun a b => Subtype.ext (by
        have ha' : (a : ↥M ⧸ goldschmidtOddCore ↥M) ∈ (⊥ : Subgroup _) := by
          rw [← hL0]; exact a.2
        have hb' : (b : ↥M ⧸ goldschmidtOddCore ↥M) ∈ (⊥ : Subgroup _) := by
          rw [← hL0]; exact b.2
        rw [Subgroup.mem_bot] at ha' hb'
        rw [ha', hb'])⟩
      have hsub : Subsingleton (↥L ⧸ Subgroup.center ↥L) :=
        (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).subsingleton
      exact (not_nontrivial_iff_subsingleton.mpr hsub) hsimp.toNontrivial
  have hP : pCore 2 (↥M ⧸ goldschmidtOddCore ↥M) = ⊥ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hPn := CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal
      (G := ↥M ⧸ goldschmidtOddCore ↥M) 2
    have := (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup
      (G := ↥M ⧸ goldschmidtOddCore ↥M) 2).isNilpotent
    have h := CFSG.Goldschmidt.N8c _ K _ hcomp hPn inferInstance
    exact hle _ (by rw [Subgroup.commutator_comm]; exact h)
  have htop : (⊤ : Subgroup (↥M ⧸ goldschmidtOddCore ↥M)) ≤ K := by
    rw [← ha, hP, bot_sup_eq]
    exact hE
  have hAF : A ≤ F := by
    intro a haA
    obtain ⟨f, hf, hfe⟩ := Subgroup.mem_map.mp (htop (Subgroup.mem_top (π ⟨a, hAM haA⟩)))
    have h1 : (f : G) = a := congrArg Subtype.val (hπinj hfe)
    rw [← h1]
    exact Subgroup.mem_subgroupOf.mp hf
  refine ⟨hAF, ?_⟩
  have hZ : Subgroup.center ↥K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hKnab
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  let e2 : (↥K ⧸ Subgroup.center ↥K) ≃* ↥F :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e
  exact goldschmidtSimpleType_of_mulEquiv e2 (hc K hcomp)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar
