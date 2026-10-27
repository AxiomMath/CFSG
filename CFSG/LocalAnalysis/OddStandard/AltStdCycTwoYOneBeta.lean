module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoYOneBetaAux

public section
namespace CFSG.OddStandard.AltStdCycTwo.YOne
open Subgroup Equiv Equiv.Perm AltStdSec AltStdBal CFSG.ComponentClassification
variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z : G}

theorem no_beta_of_core {θ : L ≃* alternatingGroup (Fin n)} (B : Two.Base G L Q n z)
    (hn : 11 ≤ n) (hlook : AltLookupAt (n - 4)) (hn8 : 8 ≤ n)
    (hcore₂ : CFSG.oddCore (centralizer ({((invE₂ θ hn8 : L) : G)} : Set G)) = ⊥)
    {K : Subgroup G}
    (hKX : K ≤ centralizer ({((invE θ hn8 : L) : G)} : Set G))
    (hK : CFSG.IsComponent (K.subgroupOf (centralizer ({((invE θ hn8 : L) : G)} : Set G))))
    (hβ : K ≤ centralizer (fixGroup θ (invE θ hn8) : Set G)) : False := by
  classical
  set e := invE θ hn8 with he
  set e₂ := invE₂ θ hn8 with he₂
  have hθe : θ e = dtE hn8 := MulEquiv.apply_symm_apply θ _
  have hθe₂ : θ e₂ = dtE₂ hn8 := MulEquiv.apply_symm_apply θ _
  set X := centralizer ({(e : G)} : Set G) with hX
  set X₂ := centralizer ({(e₂ : G)} : Set G) with hX₂
  have hKq : CFSG.IsQuasisimple K :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hKX) hK.1
  have : Group.IsPerfect K := hKq.1
  have hKX₂ : K ≤ X₂ := fun k hk => mem_centralizer_singleton_iff.2
    (mem_centralizer_iff.1 (hβ hk) _ (invE₂_mem_fixGroup θ hn8)).symm
  have hKcomp : CFSG.Assembly.IsComponentOf K (X₂ ⊓ centralizer ({(e : G)} : Set G)) := by
    have h1 : CFSG.Assembly.IsComponentOf K X :=
      (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hKX).2 hK
    exact h1.of_le_of_le (le_inf hKX₂ hKX) inf_le_right
  have hsupp₂ : ((θ e₂ : alternatingGroup (Fin n)) : Perm (Fin n)).support.card = 4 := by
    rw [hθe₂]; exact support_card_dtE₂ hn8
  have hO₂ : CFSG.oddCore X₂ = ⊥ := hcore₂
  have heX₂ : (e : G) ∈ X₂ := fixGroup_le_centralizer θ e₂ (invE_mem_fixGroup θ hn8)
  have he2 : (e : G) * e = 1 := by
    have : e * e = 1 := by rw [← sq, ← orderOf_invE θ hn8]; exact pow_orderOf_eq_one _
    exact congrArg Subtype.val this
  have hKlayer := layer_le_of_balance hO₂ heX₂ he2 hKcomp
  have h₂ := localDatum_of_four_of_core (θ := θ) B hn (orderOf_invE₂ θ hn8) hsupp₂ hcore₂
  set F₂ := fixFin ((θ e₂ : alternatingGroup (Fin n)) : Perm (Fin n)) with hF₂
  have hlook₂ : AltLookupAt (Fintype.card F₂) := by
    rw [Fintype.card_coe, hF₂, card_fixFin, hsupp₂]
    exact hlook
  have hmemF₂ : ∀ i : Fin n, (i : ℕ) < 4 → i ∈ F₂ := by
    intro i hi
    rw [hF₂, hθe₂, mem_fixFin_dtE₂]
    exact Or.inl hi
  set s₁ : F₂ := ⟨⟨0, by omega⟩, hmemF₂ _ (by simp)⟩
  set s₂ : F₂ := ⟨⟨1, by omega⟩, hmemF₂ _ (by simp)⟩
  set s₃ : F₂ := ⟨⟨2, by omega⟩, hmemF₂ _ (by simp)⟩
  set s₄ : F₂ := ⟨⟨3, by omega⟩, hmemF₂ _ (by simp)⟩
  have : Group.IsPerfect (K.subgroupOf X₂) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hKX₂).symm.toMonoidHom)
      (subgroupOfEquivOfLe hKX₂).symm.surjective
  have hPD : ∀ x ∈ K.subgroupOf X₂, ∀ d : (fixGroup θ e₂).subgroupOf X₂,
      (((etaW θ e₂ d : alternatingGroup F₂) : Perm F₂) = swap s₁ s₂ * swap s₃ s₄ ∨
        ∀ s ∈ ({s₁, s₂, s₃, s₄} : Finset F₂), ((etaW θ e₂ d : alternatingGroup F₂) : Perm F₂) s =
          s) → x * d = d * x := by
    intro x hx d hd
    apply Subtype.ext
    have hxK : (x : G) ∈ K := hx
    have hspec := ofSubtype_etaW θ e₂ d
    rcases hd with hd | hd
    ·
      rw [hd, map_mul, Perm.ofSubtype_swap_eq, Perm.ofSubtype_swap_eq] at hspec
      have hde : (⟨d, fixGroup_le θ e₂ ((d : (fixGroup θ e₂).subgroupOf X₂)).2⟩ : L) = e := by
        apply θ.injective
        apply Subtype.ext
        rw [← hspec, hθe]
        rfl
      have hd' : ((d : X₂) : G) = e := congrArg Subtype.val hde
      show (x : G) * d = d * x
      rw [hd']
      exact mem_centralizer_singleton_iff.1 (hKX hxK)
    ·
      have hdLe : ((d : X₂) : G) ∈ fixGroup θ e := by
        refine mem_corr.2 ⟨fixGroup_le θ e₂ d.2, ?_⟩
        rw [← hspec]
        refine mem_altSub.2 ⟨?_, fun i hi => ?_⟩
        · rw [hspec]
          exact Perm.mem_alternatingGroup.1 (θ _).2
        · rw [hθe, mem_fixFin_dtE, not_le] at hi
          rw [Perm.ofSubtype_apply_of_mem (p := fun x => x ∈ F₂) _ (hmemF₂ i hi)]
          have hi' : (⟨i, hmemF₂ i hi⟩ : F₂) ∈ ({s₁, s₂, s₃, s₄} : Finset F₂) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, s₁, s₂, s₃, s₄, Subtype.ext_iff,
              Fin.ext_iff]
            omega
          rw [hd _ hi']
      show (x : G) * d = d * x
      exact (mem_centralizer_iff.1 (hβ hxK) _ hdLe).symm
  have hcent := h₂.perfect_le_centralizer (etaW θ e₂) hlook₂
    (s₁ := s₁) (s₂ := s₂) (s₃ := s₃) (s₄ := s₄)
    (by simp [s₁, s₂, Subtype.ext_iff, Fin.ext_iff])
    (by simp [s₁, s₃, Subtype.ext_iff, Fin.ext_iff])
    (by simp [s₁, s₄, Subtype.ext_iff, Fin.ext_iff])
    (by simp [s₂, s₃, Subtype.ext_iff, Fin.ext_iff])
    (by simp [s₂, s₄, Subtype.ext_iff, Fin.ext_iff])
    (by simp [s₃, s₄, Subtype.ext_iff, Fin.ext_iff]) hKlayer hPD
  have hKLe₂ : K ≤ centralizer (fixGroup θ e₂ : Set G) := by
    intro k hk
    have h1 := hcent (show (⟨k, hKX₂ hk⟩ : X₂) ∈ K.subgroupOf X₂ from hk)
    exact (mem_centralizer_subgroupOf_iff (fixGroup_le_centralizer θ e₂)).1 h1
  have hKL : K ≤ centralizer (L : Set G) := by
    intro k hk
    have hL : L ≤ centralizer ({k} : Set G) := by
      refine le_centralizer_of_corr θ (F₁ := fixFin ((θ e : alternatingGroup (Fin n)) :
        Perm (Fin n))) (F₂ := F₂) ?_ ?_ ?_ ?_
      · have hsub : ({⟨8, by omega⟩, ⟨9, by omega⟩, ⟨10, by omega⟩} : Finset (Fin n)) ⊆
            fixFin ((θ e : alternatingGroup (Fin n)) : Perm (Fin n)) ∩ F₂ := by
          intro i hi
          rw [Finset.mem_inter, hF₂, hθe, hθe₂, mem_fixFin_dtE, mem_fixFin_dtE₂]
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl | rfl <;> simp
        refine le_trans ?_ (Finset.card_le_card hsub)
        rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
          Finset.card_singleton]
      · ext i
        simp only [Finset.mem_union, Finset.mem_univ, iff_true]
        rw [hF₂, hθe, hθe₂, mem_fixFin_dtE, mem_fixFin_dtE₂]
        omega
      · intro l hl
        exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hβ hk) l hl)
      · intro l hl
        exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hKLe₂ hk) l hl)
    rw [mem_centralizer_iff]
    intro l hl
    exact mem_centralizer_singleton_iff.1 (hL hl)
  exact not_quasisimple_le_centralizer B.cyc hKq hKL

end CFSG.OddStandard.AltStdCycTwo.YOne
