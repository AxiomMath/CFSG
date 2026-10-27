module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitBranch
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitCert

public section

namespace CFSG.EvenSmallLie.OmegaEight.NSplit

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]

@[expose] def ω0 (ε : Eps) : Fin (mOf ε) := ⟨0, by cases ε <;> decide⟩

namespace Branch

variable {ε : Eps} {t : G} {Q TH : Subgroup G} {ψ : V6 → G} (hB : Branch ε t Q TH ψ)
include hB


omit [Group G] hB in
theorem gam_ω0 : gam ε (ω0 ε) = 0 := gam_zero ε

omit [Group G] hB in
theorem alphaZ_ω0_iff (σ : affGroup ε) :
    alphaZ ε σ (ω0 ε) = ω0 ε ↔ (σ : Equiv.Perm V6) 0 = 0 := by
  constructor
  · intro h
    have := gam_alphaZ ε σ (ω0 ε)
    rw [h, gam_ω0] at this
    exact this.symm
  · intro h
    apply (zEquiv ε).injective
    apply Subtype.ext
    change gam ε (alphaZ ε σ (ω0 ε)) = gam ε (ω0 ε)
    rw [gam_alphaZ, gam_ω0, h]

theorem stab_iff (n : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) :
    alphaZ ε (hB.piHom n) (ω0 ε) = ω0 ε ↔ (n : G) * t * (n : G)⁻¹ = t := by
  rw [alphaZ_ω0_iff, hB.piHom_apply, hB.affF_eq_iff n.2, hB.ψ_zero, mul_one]

theorem alphaZ_transitive (ω : Fin (mOf ε)) : ∃ σ : affGroup ε, alphaZ ε σ (ω0 ε) = ω := by
  have hz : gam ε ω ∈ Zset t Q ψ := (hB.Zset_eq _).2 (qfV_gam ε ω.2)
  obtain ⟨g, hg, hgt⟩ := hz
  refine ⟨hB.piHom ⟨g, hg⟩, (zEquiv ε).injective (Subtype.ext ?_)⟩
  change gam ε (alphaZ ε (hB.piHom ⟨g, hg⟩) (ω0 ε)) = gam ε ω
  rw [gam_alphaZ, gam_ω0, hB.piHom_apply]
  exact (hB.affF_eq_iff hg 0 _).2 (by rw [hB.ψ_zero, mul_one, hgt])

omit hB in
theorem mem_N_of_levi {k : G} (hk : k ∈ centralizer ({t} : Set G) ⊓ normalizer (Q : Set G)) :
    k ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
  mem_normalizer_sup hk.2 (mem_normalizer_zpowers (mem_centralizer_singleton_iff.1 hk.1))

@[expose] def stabN : Subgroup (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) where
  carrier := {n | alphaZ ε (hB.piHom n) (ω0 ε) = ω0 ε}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_mul, Equiv.Perm.coe_mul, Function.comp_apply] at *
    rw [hb, ha]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, map_inv] at *
    conv_lhs => rw [← ha]
    exact perm_inv_apply' _ _

theorem exists_delta : ∃ δ : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) → V7,
    (∀ n m, alphaZ ε (hB.piHom n) (ω0 ε) = ω0 ε → alphaZ ε (hB.piHom m) (ω0 ε) = ω0 ε →
      δ (n * m) = δ n + rhoE ε (hB.piHom n) (δ m)) ∧ ∀ x, δ (hB.ι x) = x := by
  obtain ⟨X, hXle, hXE, hXo⟩ := hB.levi
  let X' := X.subgroupOf (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))
  have hXι : ∀ x, hB.ι x ∈ X' → hB.ι x = 1 := by
    intro x hx
    have h1 : (hB.ι x : G) ∈ X ⊓ (Q ⊔ zpowers t) := ⟨hx, hB.ιG_mem_E x⟩
    rw [hXE, mem_bot] at h1
    exact Subtype.ext h1
  have hdec : ∀ n ∈ hB.stabN, ∃ x, ∃ k ∈ X', n = hB.ι x * k := by
    intro n hn
    have h0 : ((hB.piHom n : affGroup ε) : Equiv.Perm V6) 0 = 0 := (alphaZ_ω0_iff _).1 hn
    have hO : ((hB.piHom n : affGroup ε) : Equiv.Perm V6) ∈ orthGroup ε :=
      mem_orthGroup_of_mem_affGroup (hB.piHom n).2 h0
    obtain ⟨k, hkX, hk⟩ := hXo _ hO
    have hkN := mem_N_of_levi (hXle hkX)
    let k' : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) := ⟨k, hkN⟩
    have hkt : k * t * k⁻¹ = t := by
      rw [mem_centralizer_singleton_iff.1 (hXle hkX).1, mul_inv_cancel_right]
    have hπk : hB.piHom k' = hB.piHom n := by
      apply Subtype.ext
      apply Equiv.ext
      intro v
      rw [hB.piHom_apply, ← hk v, hB.affF_eq_add hkN,
        (hB.affF_eq_iff hkN 0 0).2 (by rw [hB.ψ_zero, mul_one, hkt]), zero_add]
    have hker : hB.piHom (n * k'⁻¹) = 1 := by rw [map_mul, map_inv, hπk, mul_inv_cancel]
    obtain ⟨x, hx⟩ := hB.exists_ι_of_piHom _ hker
    exact ⟨x, k', hkX, by rw [hx]; group⟩
  have hιNK : ∀ x, hB.ι x ∈ hB.stabN := fun x => by
    change alphaZ ε (hB.piHom (hB.ι x)) (ω0 ε) = ω0 ε
    rw [hB.piHom_ι, map_one, Equiv.Perm.one_apply]
  obtain ⟨δ, hδ, hδι⟩ := exists_retraction hB.piHom hB.ι hB.ι_add hB.ι_inj (rhoE ε) hB.conj_ι
    hB.piHom_ι hB.stabN X' hXι hdec hιNK
  exact ⟨δ, fun n m hn hm => hδ n m hn hm, hδι⟩


theorem exists_section : ∃ σ : affGroup ε →* normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G),
    ∀ g, hB.piHom (σ g) = g := by
  obtain ⟨δ, hδ, hδι⟩ := hB.exists_delta
  exact exists_splitting hB.piHom hB.piHom_surjective hB.ι hB.ι_add hB.piHom_ι
    hB.exists_ι_of_piHom (rhoE ε) hB.conj_ι (sGen ε) (closure_sGen ε) rels7
    (fun w hw => wordProd_sGen ε hw) (fun h hh => exists_hom_of_rels ε h hh) (alphaZ ε) (ω0 ε)
    hB.alphaZ_transitive δ hδ hδι (fun m c hm => fox_split ε m c hm)

theorem exists_complement : ∃ X : Subgroup G,
    X ≤ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) ∧ X ⊓ (Q ⊔ zpowers t) = ⊥ ∧
      ∀ n ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G), ∃ e ∈ Q ⊔ zpowers t,
        ∃ x ∈ X, n = e * x := by
  obtain ⟨σ, hσ⟩ := hB.exists_section
  refine ⟨σ.range.map (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)).subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rw [eq_bot_iff]
    rintro _ ⟨⟨y, ⟨g, rfl⟩, rfl⟩, hy⟩
    have h1 : hB.piHom (σ g) = 1 :=
      (hB.piHom_eq_one_iff (σ g)).2 hy
    rw [hσ] at h1
    rw [h1, map_one]
    exact one_mem _
  · intro n hn
    let n' : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) := ⟨n, hn⟩
    have hk : hB.piHom (n' * (σ (hB.piHom n'))⁻¹) = 1 := by
      rw [map_mul, map_inv, hσ, mul_inv_cancel]
    obtain ⟨x, hx⟩ := hB.exists_ι_of_piHom _ hk
    refine ⟨hB.ι x, hB.ιG_mem_E x, σ (hB.piHom n'), ⟨σ (hB.piHom n'), ⟨_, rfl⟩, rfl⟩, ?_⟩
    have := congrArg Subtype.val hx
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [ι_coe] at this
    change n = ιG t ψ x * (σ (hB.piHom n') : G)
    rw [this]
    group
    rfl

theorem section_conj (σ σ' : affGroup ε →* normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))
    (hσ : ∀ g, hB.piHom (σ g) = g) (hσ' : ∀ g, hB.piHom (σ' g) = g) :
    ∃ y : V7, ∀ g, σ' g = hB.ι y * σ g * (hB.ι y)⁻¹ :=
  splitting_conj hB.piHom hB.ι hB.ι_add hB.ι_inj hB.exists_ι_of_piHom (rhoE ε) hB.conj_ι
    (sGen ε) (closure_sGen ε) rels7 (fun w hw => wordProd_sGen ε hw)
    (fun e he => by
      obtain ⟨x, hx⟩ := fox_h1 ε e he
      refine ⟨x, fun i => ?_⟩
      have h1 : ∀ a b : V7, a + b = a - b := fun a b => by
        rw [sub_eq_add_neg, CharTwo.neg_eq]
      exact (hx i).trans (h1 _ _)) σ σ' hσ hσ'

end Branch

end CFSG.EvenSmallLie.OmegaEight.NSplit
