module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAltTwoPGammaBlock
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAltTwoPGammaCore

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open Equiv Equiv.Perm

variable {Ω : Type} [DecidableEq Ω] [Fintype Ω]

theorem mem_blockStab_of_forall_mem_or_forall_not_mem {O : Finset Ω}
    (hO : 2 * O.card = Fintype.card Ω) {σ : Perm Ω}
    (h : (∀ i ∈ O, σ i ∈ O) ∨ ∀ i ∈ O, σ i ∉ O) : σ ∈ blockStab O := by
  classical
  have hcomp : Oᶜ.card = O.card := by
    rw [Finset.card_compl]
    omega
  rw [mem_blockStab_iff]
  rcases h with h | h
  ·
    have himg : O.image σ = O :=
      Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.2 h) (by
        rw [Finset.card_image_of_injective O σ.injective])
    left
    intro x
    constructor
    · exact h x
    · intro hx
      by_contra hxO
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 (by rw [himg]; exact hx)
      exact hxO (σ.injective hyx ▸ hy)
  ·
    have himg : O.image σ = Oᶜ :=
      Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.2 fun i hi =>
        Finset.mem_compl.2 (h i hi)) (by
          rw [Finset.card_image_of_injective O σ.injective, hcomp])
    have himg' : Oᶜ.image σ = O :=
      Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.2 fun i hi => by
        by_contra hiO
        obtain ⟨y, hy, hyx⟩ :=
          Finset.mem_image.1 (himg.symm ▸ Finset.mem_compl.2 hiO)
        exact Finset.mem_compl.1 hi (σ.injective hyx ▸ hy)) (by
          rw [Finset.card_image_of_injective Oᶜ σ.injective, hcomp])
    right
    intro x
    constructor
    · exact h x
    · intro hx
      by_contra hxO
      have hmem : σ x ∈ Oᶜ.image σ :=
        Finset.mem_image.2 ⟨x, Finset.mem_compl.2 hxO, rfl⟩
      rw [himg'] at hmem
      exact hx hmem

theorem exists_injective_alternatingGroup_prod_of_perfect {O : Finset Ω}
    {V : Subgroup (Perm Ω)} (hV : ⁅V, V⁆ = V) (hVO : V ≤ blockStab O) :
    ∃ f : ↥V →* alternatingGroup {x // x ∈ O} × alternatingGroup {x // x ∉ O},
      Function.Injective f := by
  classical
  by_cases hΩ : Nonempty Ω
  · obtain ⟨x₀⟩ := hΩ
    have hpresV : ∀ g : ↥V, V.subtype g ∈ blockStab O := fun g => hVO g.2
    have hker₁ : ∀ v : ↥V, ∀ x, x ∈ O ↔ (v : Perm Ω) x ∈ O := fun v =>
      (blockChar_eq_one_iff (O₁ := O) V.subtype hpresV x₀ v).1
        (eq_one_of_perfect hV (blockChar (O₁ := O) V.subtype hpresV x₀) v)
    have hker₂ : ∀ v : ↥V, ∀ x, x ∉ O ↔ (v : Perm Ω) x ∉ O := fun v x =>
      not_congr (hker₁ v x)
    have hsign₁ : ∀ v : ↥V, Perm.sign (restrBlock V.subtype O hker₁ v) = 1 := fun v =>
      eq_one_of_perfect hV (Perm.sign.comp (restrBlock V.subtype O hker₁)) v
    let r₂ : ↥V →* Perm {x // x ∉ O} :=
      { toFun := fun v => (v : Perm Ω).subtypePerm fun x => (hker₂ v x).symm
        map_one' := by ext x; rfl
        map_mul' := by intro v w; ext x; rfl }
    have hsign₂ : ∀ v : ↥V, Perm.sign (r₂ v) = 1 := fun v =>
      eq_one_of_perfect hV (Perm.sign.comp r₂) v
    let f₁ : ↥V →* alternatingGroup {x // x ∈ O} :=
      (restrBlock V.subtype O hker₁).codRestrict _
        fun v => Perm.mem_alternatingGroup.2 (hsign₁ v)
    let f₂ : ↥V →* alternatingGroup {x // x ∉ O} :=
      r₂.codRestrict _ fun v => Perm.mem_alternatingGroup.2 (hsign₂ v)
    refine ⟨f₁.prod f₂, ?_⟩
    rw [injective_iff_map_eq_one]
    intro v hv
    have h1 : (restrBlock V.subtype O hker₁ v : Perm {x // x ∈ O}) = 1 :=
      congrArg Subtype.val (Prod.ext_iff.1 hv).1
    have h2 : (r₂ v : Perm {x // x ∉ O}) = 1 :=
      congrArg Subtype.val (Prod.ext_iff.1 hv).2
    have hr₁ : ∀ x : {x // x ∈ O},
        (((restrBlock V.subtype O hker₁) v x : {x // x ∈ O}) : Ω) = (v : Perm Ω) x :=
      fun x => restrBlock_apply V.subtype O hker₁ v x
    have hr₂ : ∀ x : {x // x ∉ O},
        (((r₂ v) x : {x // x ∉ O}) : Ω) = (v : Perm Ω) x := fun x => rfl
    apply Subtype.ext
    show (v : Perm Ω) = 1
    ext x
    by_cases hx : x ∈ O
    · have h := congrArg
        (fun t : Perm {x // x ∈ O} => ((t ⟨x, hx⟩ : {x // x ∈ O}) : Ω)) h1
      rw [hr₁] at h
      simpa using h
    · have h := congrArg
        (fun t : Perm {x // x ∉ O} => ((t ⟨x, hx⟩ : {x // x ∉ O}) : Ω)) h2
      rw [hr₂] at h
      simpa using h
  ·
    haveI : IsEmpty Ω := ⟨fun x => hΩ ⟨x⟩⟩
    haveI : Subsingleton ↥V := ⟨fun a b => by
      apply Subtype.ext
      ext x
      exact isEmptyElim x⟩
    refine ⟨1, fun a b _ => Subsingleton.elim a b⟩

theorem card_le_of_perfect_of_preserves {B : Finset (Fin 10)} (hB : B.card = 5)
    {V : Subgroup (Perm (Fin 10))} (hV : ⁅V, V⁆ = V)
    (hpres : ∀ y ∈ V, (∀ i ∈ B, y i ∈ B) ∨ ∀ i ∈ B, y i ∉ B) :
    Nat.card V ≤ 3600 := by
  have hO : 2 * B.card = Fintype.card (Fin 10) := by
    rw [hB]
    norm_num
  have hVO : V ≤ blockStab B := fun y hy =>
    mem_blockStab_of_forall_mem_or_forall_not_mem hO (hpres y hy)
  obtain ⟨f, hf⟩ := exists_injective_alternatingGroup_prod_of_perfect hV hVO
  have hle : Nat.card V ≤
      Nat.card (alternatingGroup {x // x ∈ B} × alternatingGroup {x // x ∉ B}) :=
    Nat.card_le_card_of_injective f hf
  have hcard₁ : Nat.card {x // x ∈ B} = 5 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hB]
  have hcard₂ : Nat.card {x // x ∉ B} = 5 := by
    rw [Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (fun x => x ∈ B), Fintype.card_fin, Fintype.card_coe, hB]
  haveI : Nontrivial {x // x ∈ B} :=
    nontrivial_iff.2 (Fintype.one_lt_card_iff.1 (by
      rw [Fintype.card_coe, hB]
      norm_num))
  haveI : Nontrivial {x // x ∉ B} :=
    nontrivial_iff.2 (Fintype.one_lt_card_iff.1 (by
      rw [Fintype.card_subtype_compl (fun x => x ∈ B), Fintype.card_fin,
        Fintype.card_coe, hB]
      norm_num))
  have hc₁ : Nat.card (alternatingGroup {x // x ∈ B}) = 60 := by
    rw [nat_card_alternatingGroup, hcard₁]
    norm_num
  have hc₂ : Nat.card (alternatingGroup {x // x ∉ B}) = 60 := by
    rw [nat_card_alternatingGroup, hcard₂]
    norm_num
  have hcard : Nat.card
      (alternatingGroup {x // x ∈ B} × alternatingGroup {x // x ∉ B}) = 3600 := by
    rw [Nat.card_prod, hc₁, hc₂]
  exact hle.trans (le_of_eq hcard)

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
