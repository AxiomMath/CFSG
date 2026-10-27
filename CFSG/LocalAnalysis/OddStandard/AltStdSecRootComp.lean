module

public import CFSG.LocalAnalysis.ComponentInitial.AlternatingLocalComponents
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPerm
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPermBridge
public import CFSG.LocalAnalysis.OddStandard.AltStdSecStdAlt

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal Equiv

section PermImg

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (e : L ≃* alternatingGroup (Fin n))

@[expose] def permImg (M : Subgroup G) : Subgroup (Perm (Fin n)) :=
  ((M.subgroupOf L).map e.toMonoidHom).map (alternatingGroup (Fin n)).subtype

theorem mem_permImg {M : Subgroup G} {σ : Perm (Fin n)} :
    σ ∈ permImg e M ↔
      ∃ x : L, (x : G) ∈ M ∧ ((e x : alternatingGroup (Fin n)) : Perm (Fin n)) = σ := by
  constructor
  · rintro ⟨a, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩

theorem permImg_le_alt (M : Subgroup G) : permImg e M ≤ alternatingGroup (Fin n) := by
  intro σ hσ
  obtain ⟨x, -, rfl⟩ := (mem_permImg e).1 hσ
  exact (e x).2

theorem corr_permImg {M : Subgroup G} (hM : M ≤ L) : corr (X := G) e (permImg e M) = M := by
  ext x
  rw [mem_corr]
  constructor
  · rintro ⟨hx, hmem⟩
    obtain ⟨x', hx', h'⟩ := (mem_permImg e).1 hmem
    have : x' = ⟨x, hx⟩ := e.injective (Subtype.ext h')
    rw [this] at hx'
    exact hx'
  · intro hx
    exact ⟨hM hx, (mem_permImg e).2 ⟨⟨x, hM hx⟩, hx, rfl⟩⟩

noncomputable def permImgEquiv {M : Subgroup G} (hM : M ≤ L) : M ≃* permImg e M :=
  (MulEquiv.subgroupCongr (corr_permImg e hM).symm).trans
    (corrEquiv e (permImg_le_alt e M))

end PermImg

section Fixed

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem map_ofSubtype_alternatingGroup_eq_altSub (p : α → Prop) [DecidablePred p]
    (F : Finset α) (hF : ∀ i, i ∈ F ↔ p i) :
    (alternatingGroup (Subtype p)).map Perm.ofSubtype = altSub F := by
  ext σ
  rw [mem_altSub]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    have hτ' : τ ∈ alternatingGroup (Subtype p) := hτ
    refine ⟨?_, fun i hi => Perm.ofSubtype_apply_of_not_mem τ (fun hp => hi ((hF i).2 hp))⟩
    rw [Perm.sign_ofSubtype]
    exact Perm.mem_alternatingGroup.1 hτ'
  · rintro ⟨hs, hfix⟩
    have hpres : ∀ x, p (σ x) ↔ p x := by
      intro x
      constructor
      · intro hx
        by_contra hnx
        have h1 : σ x = x := hfix x (fun hmem => hnx ((hF x).1 hmem))
        exact hnx (by rw [h1] at hx; exact hx)
      · intro hx
        by_contra hnx
        have h1 : σ (σ x) = σ x := hfix _ (fun hmem => hnx ((hF _).1 hmem))
        have h2 := σ.injective h1
        exact hnx (by rw [h2]; exact hx)
    have hnp : ∀ x, σ x ≠ x → p x := fun x hx => by
      by_contra hnp
      exact hx (hfix x fun hmem => hnp ((hF x).1 hmem))
    refine ⟨σ.subtypePerm hpres, ?_, Perm.ofSubtype_subtypePerm hpres hnp⟩
    show σ.subtypePerm hpres ∈ alternatingGroup (Subtype p)
    rw [Perm.mem_alternatingGroup, ← Perm.sign_ofSubtype, Perm.ofSubtype_subtypePerm hpres hnp]
    exact hs

end Fixed

section Normal

open CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ}

theorem eq_altSub_of_normal_quasisimple {t : Perm (Fin n)} (ht : orderOf t = 2)
    (htA : t ∈ alternatingGroup (Fin n)) {K : Subgroup (Perm (Fin n))}
    (hKA : K ≤ alternatingGroup (Fin n)) (hKt : K ≤ centralizer ({t} : Set (Perm (Fin n))))
    (hKn : ∀ c ∈ alternatingGroup (Fin n), c ∈ centralizer ({t} : Set (Perm (Fin n))) →
      ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    {f : ℕ} (hf : 5 ≤ f) (eK : K ≃* alternatingGroup (Fin f)) :
    K = altSub (Finset.univ.filter fun i => t i = i) ∧
      5 ≤ (Finset.univ.filter fun i => t i = i).card := by
  classical
  have hcN : centralizer ({t} : Set (Perm (Fin n))) = normalizer (zpowers t : Set (Perm (Fin n))) :=
    centralizer_singleton_eq_normalizer_zpowers ht
  have hle : K ≤ alternatingGroup (Fin n) ⊓ normalizer (zpowers t : Set (Perm (Fin n))) := by
    intro k hk
    refine Subgroup.mem_inf.2 ⟨hKA hk, ?_⟩
    rw [← hcN]
    exact hKt hk
  have hnormal : (K.subgroupOf (alternatingGroup (Fin n) ⊓
      normalizer (zpowers t : Set (Perm (Fin n))))).Normal := by
    refine ⟨fun k hk g => ?_⟩
    have hk' : (k : Perm (Fin n)) ∈ K := hk
    obtain ⟨hgA, hgN⟩ := Subgroup.mem_inf.1 g.2
    have hgC : (g : Perm (Fin n)) ∈ centralizer ({t} : Set (Perm (Fin n))) := by
      rw [hcN]
      exact hgN
    exact hKn _ hgA hgC _ hk'
  have hcomp : CFSG.Assembly.IsComponentOf K (alternatingGroup (Fin n) ⊓
      normalizer (zpowers t : Set (Perm (Fin n)))) :=
    ⟨hle, CFSG.Assembly.IsSubnormal.step hle hnormal (CFSG.Assembly.IsSubnormal.refl _),
      isQuasisimple_of_alt hf eK⟩
  obtain ⟨hdeg, hK⟩ := ordinary_permutation_local_component_fixed_support
    (T := alternatingGroup (Fin n)) le_rfl Nat.prime_two (zpowers_le.2 htA)
    (isPGroup_zpowers_of_orderOf_eq_two ht) hcomp
  have hset : MulAction.fixedPoints (zpowers t) (Fin n) =
      ((Finset.univ.filter fun i => t i = i : Finset (Fin n)) : Set (Fin n)) := by
    ext i
    rw [mem_fixedPoints_zpowers_iff]
    simp
  refine ⟨?_, ?_⟩
  · rw [hK]
    convert map_ofSubtype_alternatingGroup_eq_altSub
      (fun i => i ∈ MulAction.fixedPoints (zpowers t) (Fin n))
      (Finset.univ.filter fun i => t i = i) (fun i => by
        rw [Finset.mem_filter, mem_fixedPoints_zpowers_iff]
        simp)
  · rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset] at hdeg
    exact hdeg

end Normal

end CFSG.OddStandard.AltStdSec
