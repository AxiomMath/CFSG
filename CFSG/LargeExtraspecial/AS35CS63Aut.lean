module

public import CFSG.LargeExtraspecial.AS35CS63Cases
public import CFSG.LargeExtraspecial.S8CorBUniv
public import CFSG.Timmesfeld.Final.Simple
public import CFSG.LargeExtraspecial.AS35CS63Res

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Timmesfeld

namespace S63

@[expose] def AutL32Input : Prop :=
  ∀ (Y : Type) [Group Y], Blueprint.LieModel Y .PSL 3 2 1 →
    ∀ H : Subgroup (MulAut Y), IsPGroup 2 H → Nat.card H ≤ 2 ^ 4

@[expose] def AutA6Input : Prop :=
  ∀ (Y : Type) [Group Y], Nonempty (Y ≃* alternatingGroup (Fin 6)) →
    ∀ H : Subgroup (MulAut Y), IsPGroup 2 H → 2 ^ 5 ≤ Nat.card H → ∃ h ∈ H, orderOf h = 8

variable {X : Type} [Group X] [Finite X] {ζ : X} {F : Subgroup X}

omit [Finite X] in
theorem not_mem_ZU_of_simple (hs : IsSimpleGroup (UZ ζ)) : ζ ∉ ZU ζ := by
  intro h
  obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
  exact hab ((eq_one_of_mem_ZU h a).trans (eq_one_of_mem_ZU h b).symm)

namespace SmithConf

variable (hC : SmithConf ζ F)
include hC

theorem perfect (hs : IsSimpleGroup (UZ ζ)) :
    ⁅normalClosure ({ζ} : Set X), normalClosure ({ζ} : Set X)⁆ = normalClosure ({ζ} : Set X) :=
  S8.commutator_normalClosure_eq_of_isConj_mul hC.hyp.orderOf_eq hC.setup.fusion hs

omit [Finite X] in
theorem mem_center_F_iff {c : X} (hc : c ∈ F) :
    (⟨c, hc⟩ : F) ∈ center F ↔ c = 1 ∨ c = ζ := by
  have hζZ : (⟨ζ, hC.hyp.zeta_mem⟩ : F) ∈ center F := mem_center_iff.mpr fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (hC.hyp.le_centralizer y.2))
  have hζ1 : (⟨ζ, hC.hyp.zeta_mem⟩ : F) ≠ 1 := fun h => by
    have := hC.hyp.orderOf_eq
    rw [show ζ = 1 from congrArg Subtype.val h, orderOf_one] at this
    exact absurd this (by norm_num)
  obtain ⟨w, -, hw⟩ := (Nat.card_eq_two_iff' (1 : center F)).1 hC.hyp.extraspecial.2.2.2
  constructor
  · intro h
    by_cases h1 : c = 1
    · exact Or.inl h1
    · right
      have e1 := hw ⟨⟨c, hc⟩, h⟩ (fun h' => h1 (congrArg (fun v : center F => ((v : F) : X)) h'))
      have e2 := hw ⟨⟨ζ, hC.hyp.zeta_mem⟩, hζZ⟩
        (fun h' => hζ1 (congrArg (fun v : center F => (v : F)) h'))
      exact congrArg (fun v : center F => ((v : F) : X)) (e1.trans e2.symm)
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact hζZ

theorem zeta_mem_of_normal {N : Subgroup X} (hNF : N ≤ F) (hNn : ∀ f ∈ F, ∀ n ∈ N, f * n * f⁻¹ ∈ N)
    (hN : N ≠ ⊥) : ζ ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N' := N.subgroupOf F with hN'
  have hN'n : N'.Normal := ⟨fun n hn g => by
    rw [hN', mem_subgroupOf] at hn ⊢
    exact hNn g g.2 n hn⟩
  have hN'b : N' ≠ ⊥ := by
    intro h
    apply hN
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hNF hx⟩ : F) ∈ N' := by rw [hN', mem_subgroupOf]; exact hx
    rw [h, mem_bot] at this
    exact (mem_bot).mpr (congrArg Subtype.val this)
  have hnil : Group.IsNilpotent F := hC.hyp.extraspecial.1.isNilpotent
  obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hN'b)
  have hcN : ((c : F) : X) ∈ N := mem_subgroupOf.mp (mem_inf.mp c.2).1
  rcases (hC.mem_center_F_iff (c : F).2).mp (mem_inf.mp c.2).2 with h | h
  · exact absurd (Subtype.ext (Subtype.ext h)) hc1
  · rwa [h] at hcN

theorem eq_one_of_mem_centralizer (hs : IsSimpleGroup (UZ ζ)) {f : X} (hf : f ∈ F)
    (hfc : f ∈ centralizer (normalClosure ({ζ} : Set X) : Set X)) : f = 1 := by
  set N := F ⊓ centralizer (normalClosure ({ζ} : Set X) : Set X) with hN
  have hUn : (normalClosure ({ζ} : Set X)).Normal := normalClosure_normal
  by_contra hf1
  have hNb : N ≠ ⊥ := fun h => hf1 (by
    have : f ∈ N := ⟨hf, hfc⟩
    rwa [h, mem_bot] at this)
  have hζN := hC.zeta_mem_of_normal inf_le_left (fun g hg n hn => mem_inf.mpr
    ⟨F.mul_mem (F.mul_mem hg (mem_inf.mp hn).1) (F.inv_mem hg),
      (Subgroup.normal_centralizer (H := normalClosure ({ζ} : Set X))).conj_mem n
        (mem_inf.mp hn).2 g⟩) hNb
  apply not_mem_ZU_of_simple hs
  refine ⟨⟨ζ, subset_normalClosure (Set.mem_singleton ζ)⟩, mem_center_iff.mpr fun u =>
    Subtype.ext ?_, rfl⟩
  exact mem_centralizer_iff.mp hζN.2 u u.2

noncomputable abbrev conjAut (ζ : X) : X →* MulAut (UZ ζ) :=
  have : (normalClosure ({ζ} : Set X)).Normal := normalClosure_normal
  (ComponentClassification.PerfectAutomorphisms.centerQuotientHom
    ↥(normalClosure ({ζ} : Set X))).comp MulAut.conjNormal

theorem eq_one_of_conjAut_eq_one (hs : IsSimpleGroup (UZ ζ)) {f : X} (hf : f ∈ F)
    (h1 : conjAut ζ f = 1) : f = 1 := by
  have hUn : (normalClosure ({ζ} : Set X)).Normal := normalClosure_normal
  have hperf : Group.IsPerfect ↥(normalClosure ({ζ} : Set X)) :=
    Subgroup.isPerfect_iff.mpr (hC.perfect hs)
  have h2 : MulAut.conjNormal f = (1 : MulAut ↥(normalClosure ({ζ} : Set X))) :=
    ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective _ (by
      rw [map_one]; exact h1)
  refine hC.eq_one_of_mem_centralizer hs hf (mem_centralizer_iff.mpr fun u hu => ?_)
  have h3 := congrArg (fun φ : MulAut ↥(normalClosure ({ζ} : Set X)) => ((φ ⟨u, hu⟩ :
    ↥(normalClosure ({ζ} : Set X))) : X)) h2
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
  calc u * f = f * u * f⁻¹ * f := by rw [h3]
    _ = f * u := by group

theorem injective_conjAut (hs : IsSimpleGroup (UZ ζ)) :
    Function.Injective ((conjAut ζ).comp F.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro f hf
  rw [mem_bot]
  exact Subtype.ext (hC.eq_one_of_conjAut_eq_one hs f.2 hf)

theorem card_map_conjAut (hs : IsSimpleGroup (UZ ζ)) :
    Nat.card ((conjAut ζ).comp F.subtype).range = Nat.card F := by
  rw [MonoidHom.range_eq_map, card_map_of_injective (hC.injective_conjAut hs), card_top]

theorem pow_four_eq_one {f : X} (hf : f ∈ F) : f ^ 4 = 1 := by
  have h2 := RankThree.Literature.FSmith.sq_mem_center hC.hyp.extraspecial (⟨f, hf⟩ : F)
  have h3 := RankThree.Literature.FSmith.sq_eq_one_of_mem_center hC.hyp.extraspecial h2
  have : (⟨f, hf⟩ : F) ^ 4 = 1 := by rw [show 4 = 2 * 2 from rfl, pow_mul]; exact h3
  simpa using congrArg Subtype.val this

end SmithConf

theorem smith57Input_of (hL3 : AutL32Input) (hA6 : AutA6Input) :
    ∀ (X : Type) [Group X] [Finite X] (ζ : X) (F : Subgroup X), SmithConf ζ F →
      (Blueprint.LieModel (UZ ζ) .PSL 3 2 1 → False) ∧
        (Nonempty (UZ ζ ≃* alternatingGroup (Fin 6)) → False) := by
  intro X _ _ ζ F hC
  have hF2 : IsPGroup 2 F := hC.hyp.extraspecial.1
  have hH2 : IsPGroup 2 ((SmithConf.conjAut ζ).comp F.subtype).range :=
    hF2.of_surjective _ ((SmithConf.conjAut ζ).comp F.subtype).rangeRestrict_surjective
  refine ⟨fun hL => ?_, fun ⟨e⟩ => ?_⟩
  · have hs : IsSimpleGroup (UZ ζ) := Timmesfeld.isSimpleGroup_of_lieModel hL
    have h := hL3 (UZ ζ) hL _ hH2
    rw [hC.card_map_conjAut hs] at h
    have := hC.hyp.width
    omega
  · have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    have hs : IsSimpleGroup (UZ ζ) := e.isSimpleGroup
    obtain ⟨φ, hφ, hord⟩ := hA6 (UZ ζ) ⟨e⟩ _ hH2 (by rw [hC.card_map_conjAut hs]; exact
      hC.hyp.width)
    obtain ⟨f, rfl⟩ := hφ
    have h4 : ((SmithConf.conjAut ζ).comp F.subtype f) ^ 4 = 1 := by
      rw [← map_pow]
      have : f ^ 4 = 1 := Subtype.ext (by simpa using hC.pow_four_eq_one f.2)
      rw [this, map_one]
    have h8 := orderOf_dvd_of_pow_eq_one h4
    rw [hord] at h8
    exact absurd h8 (by norm_num)

end S63

end CFSG.LargeExtraspecial
