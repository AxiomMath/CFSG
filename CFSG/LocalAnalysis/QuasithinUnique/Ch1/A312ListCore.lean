module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBasic
public import CFSG.Quasithin.Background.A3Structure321

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open scoped Pointwise
open CFSG.Open CFSG.SectionRank CFSG.Assembly.LowTwoRank
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem isSolvable_map_hom {G G' : Type*} [Group G] [Group G'] (f : G →* G') (H : Subgroup G)
    (h : Group.IsSolvable ↥H) : Group.IsSolvable ↥(H.map f) := by
  have := h
  have hs : Function.Surjective ((f.comp H.subtype).rangeRestrict) :=
    MonoidHom.rangeRestrict_surjective _
  have := Group.isSolvable_of_surjective hs
  rwa [MonoidHom.range_comp, Subgroup.range_subtype] at this

theorem exists_conj_of_isSylowTwoOf {X : Type} [Group X] [Finite X] {S₁ S₂ : Subgroup X}
    (h₁ : CFSG.QuasithinUnique.IsSylowTwoOf S₁ ⊤) (h₂ : CFSG.QuasithinUnique.IsSylowTwoOf S₂ ⊤) :
    ∃ g : X, S₁.map (MulAut.conj g).toMonoidHom = S₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ∀ S : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ → ¬ 2 ∣ S.index := by
    intro S hS
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  let P₁ : Sylow 2 X := h₁.2.1.toSylow (hidx S₁ h₁)
  let P₂ : Sylow 2 X := h₂.2.1.toSylow (hidx S₂ h₂)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P₁ P₂
  refine ⟨g, ?_⟩
  have h := congrArg (fun T : Sylow 2 X => (T : Subgroup X)) hg
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  exact h

theorem A312For.of_sylow {X : Type} [Group X] [Finite X] (T₀ : Subgroup X)
    (hT₀ : CFSG.QuasithinUnique.IsSylowTwoOf T₀ ⊤)
    (h : ∀ B ∈ lFamily T₀, B ≠ ⊤ → A312Case B ⊤) : A312For X := by
  intro T hT B hB hBtop
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf hT₀ hT
  let e : X ≃* X := (MulAut.conj g).symm
  have hT' : T.map e.toMonoidHom = T₀ := by
    rw [← hg]
    exact map_map_symm (MulAut.conj g) T₀
  have hB' : B.map e.toMonoidHom ∈ lFamily T₀ := by
    have h1 := cComp_map_mulEquiv e (show B ∈ cComp (B ⊔ T) from hB)
    rw [Subgroup.map_sup, hT'] at h1
    exact h1
  have hne : B.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hBtop
    have := congrArg (Subgroup.map e.symm.toMonoidHom) htop
    rw [map_map_symm, Subgroup.map_top_of_surjective _ e.symm.surjective] at this
    exact this
  exact A312Case.of_mulEquiv e (h _ hB' hne)

theorem A312For.of_solvable_overgroups {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    (T₀ : Subgroup X) (hT₀ : CFSG.QuasithinUnique.IsSylowTwoOf T₀ ⊤)
    (h : ∀ M : Subgroup X, T₀ ≤ M → M ≠ ⊤ → Group.IsSolvable ↥M) : A312For X := by
  refine A312For.of_sylow T₀ hT₀ fun B hB hBtop => ?_
  exfalso
  have hB' : B ∈ cComp (B ⊔ T₀) := hB
  have hne : B ⊔ T₀ ≠ ⊤ := by
    intro htop
    rw [htop] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')
  have hsolv : Group.IsSolvable ↥(B ⊔ T₀) := h _ le_sup_right hne
  exact not_isSolvable_of_mem_cComp hB'
    (Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (le_of_mem_cComp hB' : B ≤ B ⊔ T₀))
      (Subgroup.inclusion_injective _))

theorem cComp_top_eq_of_hom {N S : Type} [Group N] [Finite N] [Group S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) (hperf : ⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆ = ⊤)
    (f : N →* S) (hf : Function.Surjective f) (hker : Group.IsSolvable f.ker) :
    ∀ L ∈ cComp (⊤ : Subgroup N), L = ⊤ := by
  intro L hL
  have : Finite S := Finite.of_surjective f hf
  have hLf : L.map f ∈ cComp (⊤ : Subgroup S) := map_mem_cComp_top f hf hker hL
  have hq : CFSG.IsQuasisimple S := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hS).1
  have hLtop : L.map f = ⊤ := A321.cComp_eq_top_of_quasisimple hq hLf
  have hkerN : Subgroup.normalizer (f.ker : Set N) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have h3 := cComp_commutator_perfectCore hL (le_top : f.ker ≤ ⊤) hker
    (by rw [hkerN]; exact le_top)
  have hsup : L ⊔ f.ker = ⊤ := by
    rw [← Subgroup.comap_map_eq, hLtop, Subgroup.comap_top]
  rw [hsup, perfectCore_eq_self_of_perfect hperf] at h3
  exact h3.2.symm

theorem lFamily_eq_perfectCore {X : Type} [Group X] [Finite X] {T B : Subgroup X}
    (hB : B ∈ lFamily T) {S : Type} [Group S] [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a)
    (f : ↥(perfectCore (B ⊔ T)) →* S) (hf : Function.Surjective f)
    (hker : Group.IsSolvable f.ker) : B = perfectCore (B ⊔ T) := by
  have hBM : B ∈ cComp (B ⊔ T) := hB
  have hBN : B ≤ perfectCore (B ⊔ T) := by
    calc B = perfectCore B := (perfectCore_eq_self_of_perfect (perfect_of_mem_cComp hBM)).symm
      _ ≤ perfectCore (B ⊔ T) := perfectCore_mono (le_of_mem_cComp hBM)
  have hBN' : B ∈ cComp (perfectCore (B ⊔ T)) := cComp_mem_of_le hBM hBN (perfectCore_le _)
  have hB' : B.subgroupOf (perfectCore (B ⊔ T)) ∈ cComp (⊤ : Subgroup ↥(perfectCore (B ⊔ T))) := by
    have := A312.mem_cComp_subgroupOf (le_refl (perfectCore (B ⊔ T))) hBN'
    rwa [Subgroup.subgroupOf_self] at this
  have hperf : ⁅(⊤ : Subgroup ↥(perfectCore (B ⊔ T))), (⊤ : Subgroup ↥(perfectCore (B ⊔ T)))⁆ =
      ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr (perfectCore_perfect (B ⊔ T)))
  have htop := cComp_top_eq_of_hom hS hperf f hf hker _ hB'
  exact le_antisymm hBN (Subgroup.subgroupOf_eq_top.mp htop)

end CFSG.QuasithinUnique.Vol2Native.A312L
