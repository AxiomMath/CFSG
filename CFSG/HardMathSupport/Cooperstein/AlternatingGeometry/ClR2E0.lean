module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClE0
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClKlein
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClClean
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClD8
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClR2

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique
open CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
open scoped commutatorElement

namespace Classif.Pre

variable {d : ℕ} {W : Subgroup (Perm (Fin d))} {ι : Type*} {E : ι → Subgroup (Perm (Fin d))}
  (P : Pre W E)

theorem lambda_iff_orbit (i0 : ι) {x : Fin d} (hx : Nat.card (orbit (E i0) x) = 4)
    (hex : ∃ z, partner P.twoGroup z = z) (z : Fin d) :
    partner P.twoGroup z = z ↔ z ∈ orbit (E i0) x := by
  constructor
  · exact unmatched_mem_orbit_of_fourOrbit P.twoGroup (P.le i0) (P.exp i0) (P.shape i0) hx
  · intro hz
    by_contra hm
    have hsub : (orbit (E i0) z : Set (Fin d)) ⊆ {z, partner P.twoGroup z} := by
      rintro _ ⟨⟨w, hw⟩, rfl⟩
      exact P.blockTrivial_of_unmatched hex w (P.le i0 hw) z hm
    have h2 : (orbit (E i0) z : Set (Fin d)).ncard ≤ 2 := by
      calc (orbit (E i0) z : Set (Fin d)).ncard ≤ ({z, partner P.twoGroup z} : Set (Fin d)).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := by
          calc ({z, partner P.twoGroup z} : Set (Fin d)).ncard
              ≤ ({partner P.twoGroup z} : Set (Fin d)).ncard + 1 := Set.ncard_insert_le z _
            _ = 2 := by simp
    have heq : orbit (E i0) z = orbit (E i0) x := orbit_eq_iff.2 hz
    rw [heq, ← Nat.card_coe_set_eq, hx] at h2
    omega

end Classif.Pre

variable {G : Type} [Group G] [Finite G]

theorem false_of_klein_theta (hE0 : E0Statement) (hE0n : E0NotYStatement) {X S L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X)
    (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L) {m : ℕ} (hm : 8 < m)
    (e : ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m))
    {θ : ↥(L ⊔ S) →* Perm (Fin m)} (hNS : NaturalSectionTheta S L m θ)
    (hθS : ∀ m' : ↥(L ⊔ S), θ m' = 1 → (m' : G) ∈ S)
    (hunm : ∃ z : Fin m, ∀ y, z ≠ y →
      swap z y ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m))))
    (hfix : ∀ p q : Fin m, IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) p q →
        ∀ s : ↥(L ⊔ S), (s : G) ∈ S → θ s p = p ∨ θ s p = q)
    (Λ : Finset (Fin m))
    (hΛunm : ∀ z, z ∈ Λ ↔ ∀ y, z ≠ y →
      swap z y ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m))))
    (hΛcard : Λ.card = 4) (e0 : Fin 4 → Fin m) (he0 : Function.Injective e0)
    (hrange : Set.range e0 = (↑Λ : Set (Fin m)))
    (hD1S : swap (e0 0) (e0 1) * swap (e0 2) (e0 3) ∈ (S.subgroupOf (L ⊔ S)).map θ)
    (hD2S : swap (e0 0) (e0 2) * swap (e0 1) (e0 3) ∈ (S.subgroupOf (L ⊔ S)).map θ)
    (hD3S : swap (e0 0) (e0 3) * swap (e0 1) (e0 2) ∈ (S.subgroupOf (L ⊔ S)).map θ)
    (hD1W : swap (e0 0) (e0 1) * swap (e0 2) (e0 3) ∈
      ((thompsonJ S).subgroupOf (L ⊔ S)).map θ)
 : False := by
  classical
  have hNS' := hNS
  obtain ⟨hSL, hA', hLs, hpS, hkerP, hsh⟩ := theta_node_data hX hA hL hm e hNS
  have hS2 : IsPGroup 2 S := hA'.twoRadical.isPGroup
  have hP := pre_of_theta hS2 (le_sup_right : S ≤ L ⊔ S) θ hsh
  set W : Subgroup (Perm (Fin m)) := ((thompsonJ S).subgroupOf (L ⊔ S)).map θ with hW
  set Sstar : Subgroup (Perm (Fin m)) := (S.subgroupOf (L ⊔ S)).map θ with hSstar
  have hex : ∃ z, Classif.partner hP.twoGroup z = z := by
    obtain ⟨z, hz⟩ := hunm
    refine ⟨z, ?_⟩
    by_contra hne
    obtain ⟨y, hy1, hy2⟩ := (Classif.partner_ne_iff hP.twoGroup).1 hne
    exact hz y hy1 hy2
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = Classif.partner hP.twoGroup := ⟨_, rfl⟩
  have hωω : ∀ y, ω (ω y) = y := fun y => by rw [hωdef]; exact Classif.partner_partner _ y
  have hωsw : ∀ y, ω y ≠ y → swap y (ω y) ∈ W := fun y hy => by
    rw [hωdef] at hy ⊢; exact Classif.swap_partner_mem hP.twoGroup hy
  have hWS : W ≤ Sstar := Subgroup.map_mono (Subgroup.comap_mono
    (iSup_le fun A => iSup_le fun hA => hA.1 : thompsonJ S ≤ S))
  have hΛmem : ∀ z, z ∈ Λ ↔ ω z = z := by
    intro z
    rw [hΛunm, hωdef]
    constructor
    · intro h
      by_contra hne
      obtain ⟨y, hy1, hy2⟩ := (Classif.partner_ne_iff hP.twoGroup).1 hne
      exact h y hy1 hy2
    · intro h y hy1 hy2
      have := Classif.partner_eq_of_swap_mem hP.twoGroup hy1 hy2
      rw [h] at this
      exact hy1 this
  have hiso : ∀ y, ω y ≠ y → IsIsoPair W y (ω y) := fun y hy => by
    refine ⟨Ne.symm hy, hωsw y hy, fun w hw => ?_⟩
    rw [hωdef] at hy ⊢
    exact hP.blockTrivial_of_unmatched hex w hw y hy
  have hK : ∀ y, ω y ≠ y → swap y (ω y) ∈ Sstar := fun y hy => hWS (hωsw y hy)
  have hfix' : ∀ s ∈ Sstar, ∀ y, ω y ≠ y → s y = y ∨ s y = ω y := by
    rintro _ ⟨s0, hs0, rfl⟩ y hy
    exact hfix y (ω y) (hiso y hy) s0 (Subgroup.mem_subgroupOf.1 hs0)
  let P' : Subgroup (Perm (Fin m)) := Classif.matchedFixed ω Sstar
  have hP'S : P' ≤ Sstar := fun p hp => (Classif.mem_matchedFixed.1 hp).1
  have hDoffmem : ∀ D : Perm (Fin m), D ∈ Sstar → (∀ i, i ∉ Set.range e0 → D i = i) → D ∈ P' := by
    intro D hDS hDoff
    refine Classif.mem_matchedFixed.2 ⟨hDS, fun y hy => hDoff y ?_⟩
    intro hyr
    rw [hrange] at hyr
    exact hy ((hΛmem y).1 (Finset.mem_coe.1 hyr))
  have hD1 : swap (e0 0) (e0 1) * swap (e0 2) (e0 3) ∈ P' :=
    hDoffmem _ hD1S (fun i hi => swapProd_off _ _ _ _ hi)
  have hD2 : swap (e0 0) (e0 2) * swap (e0 1) (e0 3) ∈ P' :=
    hDoffmem _ hD2S (fun i hi => swapProd_off _ _ _ _ hi)
  have hD3 : swap (e0 0) (e0 3) * swap (e0 1) (e0 2) ∈ P' :=
    hDoffmem _ hD3S (fun i hi => swapProd_off _ _ _ _ hi)
  have hP2 : IsPGroup 2 P' :=
    ((hS2.comap_subtype (K := L ⊔ S)).map θ).to_le hP'S
  have hsupp : ∀ p ∈ P', ∀ i, i ∉ Set.range e0 → p i = i := by
    intro p hp i hi
    have : ω i ≠ i := fun h => hi (by rw [hrange]; exact (hΛmem i).2 h)
    exact (Classif.mem_matchedFixed.1 hp).2 i this
  have hfin4 : ∀ a b : Fin 4, ∃ v : Perm (Fin 4), (v = 1 ∨ v = swap 0 1 * swap 2 3 ∨
      v = swap 0 2 * swap 1 3 ∨ v = swap 0 3 * swap 1 2) ∧ v a = b := by decide
  have htrans : ∀ i ∈ Λ, ∀ j ∈ Λ, ∃ p ∈ ({1, swap (e0 0) (e0 1) * swap (e0 2) (e0 3),
      swap (e0 0) (e0 2) * swap (e0 1) (e0 3), swap (e0 0) (e0 3) * swap (e0 1) (e0 2)} :
      Set (Perm (Fin m))), p i = j := by
    intro i hi j hj
    have hi' : i ∈ Set.range e0 := by rw [hrange]; exact hi
    have hj' : j ∈ Set.range e0 := by rw [hrange]; exact hj
    obtain ⟨a, rfl⟩ := hi'
    obtain ⟨b, rfl⟩ := hj'
    obtain ⟨v, hv, hva⟩ := hfin4 a b
    rcases hv with rfl | rfl | rfl | rfl
    · exact ⟨1, by simp, by rw [Perm.one_apply]; exact congrArg e0 hva⟩
    · exact ⟨swap (e0 0) (e0 1) * swap (e0 2) (e0 3), by simp,
        by rw [swapProd_frame he0, hva]⟩
    · exact ⟨swap (e0 0) (e0 2) * swap (e0 1) (e0 3), by simp,
        by rw [swapProd_frame he0, hva]⟩
    · exact ⟨swap (e0 0) (e0 3) * swap (e0 1) (e0 2), by simp,
        by rw [swapProd_frame he0, hva]⟩
  have hdn : ∀ (a b c d : Fin 4), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      swap (e0 a) (e0 b) * swap (e0 c) (e0 d) ∈ alternatingGroup (Fin m) := by
    intro a b c d hab hac had hbc hbd hcd
    rw [mem_alternatingGroup, map_mul, sign_swap (fun h => hab (he0 h)),
      sign_swap (fun h => hcd (he0 h))]
    rfl
  have hmlt : 4 < m := by omega
  have hdich := quad_dichotomy he0 hP2 hsupp hD1 hD2 hD3
  have hd01 : e0 0 ≠ e0 1 := fun h => absurd (he0 h) (by decide)
  have hd02 : e0 0 ≠ e0 2 := fun h => absurd (he0 h) (by decide)
  have hd03 : e0 0 ≠ e0 3 := fun h => absurd (he0 h) (by decide)
  have hd12 : e0 1 ≠ e0 2 := fun h => absurd (he0 h) (by decide)
  have hd13 : e0 1 ≠ e0 3 := fun h => absurd (he0 h) (by decide)
  have hd23 : e0 2 ≠ e0 3 := fun h => absurd (he0 h) (by decide)
  have hD3eq : swap (e0 0) (e0 1) * swap (e0 2) (e0 3) * (swap (e0 0) (e0 2) * swap (e0 1) (e0 3)) =
      swap (e0 0) (e0 3) * swap (e0 1) (e0 2) := dbl_mul hd01 hd02 hd03 hd12 hd13 hd23
  have hdich' : ((∀ p ∈ P', p = 1 ∨ p = swap (e0 0) (e0 1) * swap (e0 2) (e0 3) ∨
        p = swap (e0 0) (e0 2) * swap (e0 1) (e0 3) ∨ p = swap (e0 0) (e0 3) * swap (e0 1) (e0 2)) ∧
      swap (e0 0) (e0 2) * swap (e0 1) (e0 3) ∈ W) ∨
      ∃ p ∈ P', ∃ x y z : Fin 4, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ p (e0 x) = e0 y ∧ p (e0 y) = e0 x ∧
        p (e0 z) = e0 z := by
    rcases hdich with hV | hR
    swap
    · exact Or.inr hR
    by_cases hD2W : swap (e0 0) (e0 2) * swap (e0 1) (e0 3) ∈ W
    · exact Or.inl ⟨hV, hD2W⟩
    right
    have hD3W : swap (e0 0) (e0 3) * swap (e0 1) (e0 2) ∉ W := by
      intro h3
      apply hD2W
      have : swap (e0 0) (e0 2) * swap (e0 1) (e0 3) =
          (swap (e0 0) (e0 1) * swap (e0 2) (e0 3))⁻¹ * (swap (e0 0) (e0 3) * swap (e0 1) (e0 2)) := by
        rw [← hD3eq]; group
      rw [this]
      exact W.mul_mem (W.inv_mem hD1W) h3
    have hmatchex : ∃ p, ω p ≠ p := by
      by_contra hcon
      push Not at hcon
      have : Λ = Finset.univ := Finset.eq_univ_of_forall fun q => (hΛmem q).2 (hcon q)
      rw [this, Finset.card_univ, Fintype.card_fin] at hΛcard
      omega
    obtain ⟨-, -, -, hAθ', -, -⟩ := hNS'
    have hSR : Sstar ≤ θ.range := fun s hs => by
      obtain ⟨t, -, rfl⟩ := hs
      exact ⟨t, rfl⟩
    have hAltR : alternatingGroup (Fin m) ≤ θ.range := fun σ hσ => by
      obtain ⟨l, hl⟩ := hAθ' σ hσ
      exact ⟨_, hl⟩
    have hunmω : ∀ y, ω y = y → ∀ q, y ≠ q → swap y q ∉ W := by
      intro y hy q hyq hmem
      have := Classif.partner_eq_of_swap_mem hP.twoGroup hyq hmem
      rw [← hωdef, hy] at this
      exact hyq this
    have ht : swap (e0 0) (e0 1) ∈ Sstar :=
      swap_mem_of_d8 he0 ω hωω W Sstar θ.range hP.twoGroup hWS hSR hAltR hωsw
        (fun w hw y hy => (hiso y hy).2.2 w hw) hunmω
        (fun q => by rw [hrange, Finset.mem_coe, hΛmem]) hmatchex hD1W hD2W hD3W
        (fun U h1 h2 h3 h4 => le_theta_S_of_normal_two hA' (le_sup_right : S ≤ L ⊔ S) θ hθS W rfl U
          h1 h2 h3 h4)
    refine ⟨swap (e0 0) (e0 1), Classif.mem_matchedFixed.2 ⟨ht, fun y hy => ?_⟩, 0, 1, 2,
      by decide, by decide, by decide, swap_apply_left _ _, swap_apply_right _ _,
      swap_apply_of_ne_of_ne (fun h => hd02 h.symm) (fun h => hd12 h.symm)⟩
    refine swap_apply_of_ne_of_ne (fun h => ?_) (fun h => ?_)
    · exact hy ((hΛmem y).1 (by rw [← Finset.mem_coe, ← hrange]; exact ⟨0, h.symm⟩) |> fun h' => h')
    · exact hy ((hΛmem y).1 (by rw [← Finset.mem_coe, ← hrange]; exact ⟨1, h.symm⟩) |> fun h' => h')
  rcases hdich' with ⟨hV, hD2W⟩ | ⟨p', hp'P, a, b, c, hab, hac, hbc, hpa, hpb, hpc⟩
  ·
    have hD3W : swap (e0 0) (e0 3) * swap (e0 1) (e0 2) ∈ W := by
      have := W.mul_mem hD1W hD2W
      rwa [hD3eq] at this
    obtain ⟨π, hπ, -, -, hequiv, hθV⟩ := hNS'
    have hnf := hnf_of_unmatched (S := S) (L := L) θ hunm
    have hD := eOffenderData_of_not_full hA' (Or.inr (by omega)) π θ hπ hequiv hθV hnf
    have hmem1 : (1 : Perm (Fin m)) ∈ P' := P'.one_mem
    have hiff : ∀ p, p ∈ P' ↔ p = 1 ∨ p = swap (e0 0) (e0 1) * swap (e0 2) (e0 3) ∨
        p = swap (e0 0) (e0 2) * swap (e0 1) (e0 3) ∨ p = swap (e0 0) (e0 3) * swap (e0 1) (e0 2) := by
      intro p
      refine ⟨hV p, ?_⟩
      rintro (rfl | rfl | rfl | rfl)
      · exact hmem1
      · exact hD1
      · exact hD2
      · exact hD3
    have hcount : Nat.card {z : Fin m // Classif.partner hP.twoGroup z ≠ z} + Λ.card = m := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      have h1 : Λ = Finset.univ.filter fun z : Fin m => ¬ (Classif.partner hP.twoGroup z ≠ z) := by
        ext z; simp [hΛmem, hωdef]
      rw [h1, Finset.card_filter_add_card_filter_not (s := Finset.univ), Finset.card_univ,
        Fintype.card_fin]
    have h2N := hP.two_mul_isoCount_eq hex
    have hm10 : 10 ≤ m := by omega
    have hcard4 : Nat.card P' = 4 := by
      have hdist : ∀ a b : Fin 4, a ≠ b → e0 a ≠ e0 b := fun a b h h' => h (he0 h')
      have hD1a : (swap (e0 0) (e0 1) * swap (e0 2) (e0 3)) (e0 0) = e0 1 := by
        rw [swapProd_frame he0]; rfl
      have hD2a : (swap (e0 0) (e0 2) * swap (e0 1) (e0 3)) (e0 0) = e0 2 := by
        rw [swapProd_frame he0]; rfl
      have hD3a : (swap (e0 0) (e0 3) * swap (e0 1) (e0 2)) (e0 0) = e0 3 := by
        rw [swapProd_frame he0]; rfl
      have hF : ({1, swap (e0 0) (e0 1) * swap (e0 2) (e0 3),
          swap (e0 0) (e0 2) * swap (e0 1) (e0 3), swap (e0 0) (e0 3) * swap (e0 1) (e0 2)} :
          Finset (Perm (Fin m))).card = 4 := by
        refine Classif.card_four ?_ ?_ ?_ ?_ ?_ ?_
        · intro h; have := congrArg (fun f : Perm (Fin m) => f (e0 0)) h
          simp only [Perm.one_apply, hD1a] at this; exact hdist 0 1 (by decide) this
        · intro h; have := congrArg (fun f : Perm (Fin m) => f (e0 0)) h
          simp only [Perm.one_apply, hD2a] at this; exact hdist 0 2 (by decide) this
        · intro h; have := congrArg (fun f : Perm (Fin m) => f (e0 0)) h
          simp only [Perm.one_apply, hD3a] at this; exact hdist 0 3 (by decide) this
        · intro h; have := congrArg (fun f : Perm (Fin m) => f (e0 0)) h
          rw [hD1a, hD2a] at this; exact hdist 1 2 (by decide) this
        · intro h; have := congrArg (fun f : Perm (Fin m) => f (e0 0)) h
          rw [hD1a, hD3a] at this; exact hdist 1 3 (by decide) this
        · intro h; have := congrArg (fun f : Perm (Fin m) => f (e0 0)) h
          rw [hD2a, hD3a] at this; exact hdist 2 3 (by decide) this
      rw [← hF, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun p => by
        rw [hiff p]; simp [Finset.mem_insert, Finset.mem_singleton])
    have hsq : ∀ p ∈ P', p * p = 1 := by
      intro p hp
      have hsqD : ∀ (v : Perm (Fin 4)), (∀ i, v (v i) = i) → ∀ a b c d : Fin 4,
          v = swap a b * swap c d →
          (swap (e0 a) (e0 b) * swap (e0 c) (e0 d)) * (swap (e0 a) (e0 b) * swap (e0 c) (e0 d)) = 1 := by
        intro v hv a b c d hvdef
        refine eq_of_frame (e := e0) (fun i hi => ?_) (fun i _ => rfl) (fun i => ?_)
        · rw [Perm.mul_apply, swapProd_off a b c d hi, swapProd_off a b c d hi]
        · rw [Perm.mul_apply, swapProd_frame he0, swapProd_frame he0, ← hvdef, hv]; rfl
      rcases (hiff p).1 hp with rfl | rfl | rfl | rfl
      · simp
      · exact hsqD _ (by decide) 0 1 2 3 rfl
      · exact hsqD _ (by decide) 0 2 1 3 rfl
      · exact hsqD _ (by decide) 0 3 1 2 rfl
    have hoff : ∀ p ∈ P', ∀ i, i ∉ Λ → p i = i := by
      intro p hp i hi
      have : ω i ≠ i := fun h => hi ((hΛmem i).2 h)
      exact (Classif.mem_matchedFixed.1 hp).2 i this
    have htr' : ∀ i ∈ Λ, ∀ j ∈ Λ, ∃ p ∈ P', p i = j := by
      intro i hi j hj
      obtain ⟨p, hp, hpij⟩ := htrans i hi j hj
      refine ⟨p, ?_, hpij⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      exact (hiff p).2 hp
    have hθeq : Sstar = P' ⊔ Subgroup.closure {τ | ∃ x, x ∉ Λ ∧ τ = swap x (ω x)} := by
      have hKeq : Classif.matchedK ω = Subgroup.closure {τ | ∃ x, x ∉ Λ ∧ τ = swap x (ω x)} := by
        unfold Classif.matchedK
        congr 1
        ext τ
        simp only [Set.mem_ofPred_eq, hΛmem]
      rw [← hKeq]
      apply le_antisymm
      · intro s hs
        obtain ⟨κ, hκ, p, hp, rfl⟩ := Classif.eq_matchedK_mul hωω hK hfix' hs
        rw [sup_comm]
        exact Subgroup.mul_mem_sup hκ hp
      · refine sup_le hP'S ?_
        refine (Subgroup.closure_le Sstar).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        exact hK y hy
    have hJ : Sstar ≤ W := by
      rw [hθeq]
      refine sup_le ?_ ((Subgroup.closure_le W).2 ?_)
      · intro p hp
        rcases (hiff p).1 hp with rfl | rfl | rfl | rfl
        · exact W.one_mem
        · exact hD1W
        · exact hD2W
        · exact hD3W
      · rintro _ ⟨y, hy, rfl⟩
        exact hωsw y (fun h => hy ((hΛmem y).2 h))
    by_cases hY : HY S L
    · exact hE0 G X S L hA hL hSL m hm10 θ hNS hθS hD hJ Λ hΛcard P' hcard4 hsq hoff htr' ω hωω
        (fun x hx => (hΛmem x).1 hx) (fun x hx hω => hx ((hΛmem x).2 hω)) hθeq hY
    · exact hE0n G X S L hA hL hSL m hm10 θ hNS hθS hD hJ Λ hΛcard P' hcard4 hsq hoff htr' ω hωω
        (fun x hx => (hΛmem x).1 hx) (fun x hx hω => hx ((hΛmem x).2 hω)) hθeq hY
  ·
    obtain ⟨s0, hs0, hs0p⟩ := hP'S hp'P
    obtain ⟨-, -, -, hAθ, -, -⟩ := hNS'
    have hmem1 : (1 : Perm (Fin m)) ∈ P' := P'.one_mem
    let Pk : Subgroup (Perm (Fin m)) := P' ⊓ alternatingGroup (Fin m)
    have hΓ : ∃ k : Fin m, k ∉ Λ := by
      by_contra hcon
      push Not at hcon
      have : Λ = Finset.univ := Finset.eq_univ_of_forall hcon
      rw [this, Finset.card_univ, Fintype.card_fin] at hΛcard
      omega
    have hmemΛ : ∀ a, e0 a ∈ Λ := fun a => Finset.mem_coe.1 (hrange ▸ Set.mem_range_self a)
    have hs : (s0 : G) ∈ S := Subgroup.mem_subgroupOf.1 hs0
    have hPS : ∀ p ∈ Pk, ∃ l : ↥L, (l : G) ∈ S ∧ θ (Subgroup.inclusion le_sup_left l) = p := by
      intro p hp
      obtain ⟨s1, hs1, hs1p⟩ := hP'S hp.1
      obtain ⟨l, hl⟩ := hAθ p hp.2
      refine ⟨l, ?_, hl⟩
      have h1 : θ (s1⁻¹ * ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩) = 1 := by
        rw [map_mul, map_inv, hs1p, hl, inv_mul_cancel]
      have h2 := hθS _ h1
      have h3 : (s1 : G) ∈ S := Subgroup.mem_subgroupOf.1 hs1
      have h4 : (l : G) = (s1 : G) * ((s1⁻¹ * ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ :
          ↥(L ⊔ S)) : G) := by simp
      rw [h4]
      exact S.mul_mem h3 h2
    have hPfix : ∀ p ∈ Pk, ∀ i : Fin m, i ∉ Λ → p i = i := by
      intro p hp i hi
      have : ω i ≠ i := fun h => hi ((hΛmem i).2 h)
      exact (Classif.mem_matchedFixed.1 hp.1).2 i this
    have hPtrans : ∀ i ∈ Λ, ∀ j ∈ Λ, ∃ p ∈ Pk, p i = j := by
      intro i hi j hj
      obtain ⟨p, hp, hpij⟩ := htrans i hi j hj
      refine ⟨p, ?_, hpij⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact ⟨hD1, hdn 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)⟩
      · exact ⟨hD2, hdn 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)⟩
      · exact ⟨hD3, hdn 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)⟩
    exact RichardWeiss.Proving.false_of_swap_mem_theta hA hL hSL (by omega) hNS Λ hΓ Pk hPS hPfix
      hPtrans (hmemΛ a) (hmemΛ b) (hmemΛ c) (fun h => hab (he0 h)) (fun h => hac (he0 h))
      (fun h => hbc (he0 h)) hs (by rw [hs0p]; exact hpa) (by rw [hs0p]; exact hpb)
      (by rw [hs0p]; exact hpc)


theorem false_of_fourOrbit_fixed (hE0 : E0Statement) (hE0n : E0NotYStatement) {X S L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X)
    (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L) {m : ℕ} (hm : 8 < m)
    (e : ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m))
    {θ : ↥(L ⊔ S) →* Perm (Fin m)} (hNS : NaturalSectionTheta S L m θ)
    (hθS : ∀ m' : ↥(L ⊔ S), θ m' = 1 → (m' : G) ∈ S)
    {A : Subgroup G} (hAm : IsMaxElemAbelian S A) {x : Fin m}
    (hx : Nat.card (orbit ((A.subgroupOf (L ⊔ S)).map θ) x) = 4)
    (hunm : ∃ z : Fin m, ∀ y, z ≠ y →
      swap z y ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m))))
    (_hcnt : Nat.card {x : Fin m // ∃ y, x < y ∧
          IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) x y} = 3 ∨
        5 ≤ Nat.card {x : Fin m // ∃ y, x < y ∧
          IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) x y})
    (hfix : ∀ p q : Fin m, IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) p q →
        ∀ s : ↥(L ⊔ S), (s : G) ∈ S → θ s p = p ∨ θ s p = q)
    : False := by
  classical
  have hNS' := hNS
  obtain ⟨hSL, hA', hLs, hpS, hkerP, hsh⟩ := theta_node_data hX hA hL hm e hNS
  have hS2 : IsPGroup 2 S := hA'.twoRadical.isPGroup
  have hP := pre_of_theta hS2 (le_sup_right : S ≤ L ⊔ S) θ hsh
  set W : Subgroup (Perm (Fin m)) := ((thompsonJ S).subgroupOf (L ⊔ S)).map θ with hW
  set Sstar : Subgroup (Perm (Fin m)) := (S.subgroupOf (L ⊔ S)).map θ with hSstar
  have hex : ∃ z, Classif.partner hP.twoGroup z = z := by
    obtain ⟨z, hz⟩ := hunm
    refine ⟨z, ?_⟩
    by_contra hne
    obtain ⟨y, hy1, hy2⟩ := (Classif.partner_ne_iff hP.twoGroup).1 hne
    exact hz y hy1 hy2
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = Classif.partner hP.twoGroup := ⟨_, rfl⟩
  have hωω : ∀ y, ω (ω y) = y := fun y => by rw [hωdef]; exact Classif.partner_partner _ y
  have hΛ : ∀ z, ω z = z ↔ z ∈ orbit ((A.subgroupOf (L ⊔ S)).map θ) x := by
    intro z
    rw [hωdef]
    exact hP.lambda_iff_orbit ⟨A, hAm⟩ hx hex z
  have hωcomm : ∀ w ∈ W, ∀ z, ω (w z) = w (ω z) := fun w hw z => by
    rw [hωdef]; exact Classif.partner_comm hP.twoGroup hw z
  have hωsw : ∀ y, ω y ≠ y → swap y (ω y) ∈ W := fun y hy => by
    rw [hωdef] at hy ⊢; exact Classif.swap_partner_mem hP.twoGroup hy
  set E_A : Subgroup (Perm (Fin m)) := (A.subgroupOf (L ⊔ S)).map θ with hE_A
  have hAJ : A ≤ thompsonJ S :=
    le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian S A) => A) A hAm
  have hEW : E_A ≤ W := Subgroup.map_mono (Subgroup.comap_mono hAJ)
  have hWS : W ≤ Sstar := Subgroup.map_mono (Subgroup.comap_mono
    (iSup_le fun A => iSup_le fun hA => hA.1 : thompsonJ S ≤ S))
  have hE2 : Offender.IsExp2 E_A := hP.exp ⟨A, hAm⟩
  let Λ : Finset (Fin m) := Finset.univ.filter fun z => ω z = z
  have hΛmem : ∀ z, z ∈ Λ ↔ ω z = z := fun z => by simp [Λ]
  have hΛset : (↑Λ : Set (Fin m)) = orbit E_A x := by
    ext z; simp only [Finset.mem_coe, hΛmem, hΛ]
  have hΛcard : Λ.card = 4 := by
    rw [← Set.ncard_coe_finset, hΛset, ← Nat.card_coe_set_eq]; exact hx
  let e0 : Fin 4 ↪o Fin m := Λ.orderEmbOfFin hΛcard
  have he0 : Function.Injective e0 := e0.injective
  have hrange : Set.range e0 = (↑Λ : Set (Fin m)) := Finset.range_orderEmbOfFin Λ hΛcard
  have horb : ∀ z, z ∈ orbit E_A (e0 0) ↔ z ∈ Set.range e0 := by
    intro z
    have h0 : e0 0 ∈ orbit E_A x := by
      rw [← hΛset, ← hrange]; exact ⟨0, rfl⟩
    have : orbit E_A (e0 0) = orbit E_A x := orbit_eq_iff.2 h0
    rw [this, hrange, ← hΛset]
  obtain ⟨⟨ε1, hε1, hf1⟩, ⟨ε2, hε2, hf2⟩, ⟨ε3, hε3, hf3⟩⟩ := klein_elements hE2 he0 horb
  have hiso : ∀ y, ω y ≠ y → IsIsoPair W y (ω y) := fun y hy => by
    refine ⟨Ne.symm hy, hωsw y hy, fun w hw => ?_⟩
    rw [hωdef] at hy ⊢
    exact hP.blockTrivial_of_unmatched hex w hw y hy
  have hK : ∀ y, ω y ≠ y → swap y (ω y) ∈ Sstar := fun y hy => hWS (hωsw y hy)
  have hfix' : ∀ s ∈ Sstar, ∀ y, ω y ≠ y → s y = y ∨ s y = ω y := by
    rintro _ ⟨s0, hs0, rfl⟩ y hy
    exact hfix y (ω y) (hiso y hy) s0 (Subgroup.mem_subgroupOf.1 hs0)
  let P' : Subgroup (Perm (Fin m)) := Classif.matchedFixed ω Sstar
  have hP'S : P' ≤ Sstar := fun p hp => (Classif.mem_matchedFixed.1 hp).1
  have hDmem : ∀ ε ∈ E_A, ∀ D : Perm (Fin m), (∀ i, ε (e0 i) = D (e0 i)) →
      (∀ i, i ∉ Set.range e0 → D i = i) → D ∈ P' := by
    intro ε hε D hεD hDoff
    obtain ⟨κ, hκ, hκeq⟩ := Classif.exists_matchedK_eq hωω hK hfix' ε (hWS (hEW hε))
    have hKS : Classif.matchedK ω ≤ Sstar := by
      refine (Subgroup.closure_le Sstar).2 ?_
      rintro _ ⟨y, hy, rfl⟩
      exact hK y hy
    have hmem : κ⁻¹ * ε ∈ P' := by
      refine Classif.mem_matchedFixed.2 ⟨Sstar.mul_mem (Sstar.inv_mem (hKS hκ)) (hWS (hEW hε)),
        fun y hy => ?_⟩
      rw [Perm.mul_apply, ← hκeq y hy]; simp
    have hEq : κ⁻¹ * ε = D := by
      refine eq_of_frame (e := e0) (fun i hi => ?_) hDoff (fun i => ?_)
      · have : ω i ≠ i := fun h => hi (by rw [hrange]; exact (hΛmem i).2 h)
        exact (Classif.mem_matchedFixed.1 hmem).2 i this
      · rw [Perm.mul_apply, ← hεD i]
        have hmemε : ε (e0 i) ∈ Set.range e0 := by
          rw [← horb]
          obtain ⟨⟨h, hh⟩, hhi⟩ := (horb (e0 i)).2 ⟨i, rfl⟩
          have h1 : ε (e0 i) = (ε * h) (e0 0) := by rw [Perm.mul_apply]; exact congrArg ε hhi.symm
          exact ⟨⟨ε * h, E_A.mul_mem hε hh⟩, h1.symm⟩
        have hunm' : ω (ε (e0 i)) = ε (e0 i) := by
          have : ε (e0 i) ∈ (↑Λ : Set (Fin m)) := by rw [← hrange]; exact hmemε
          exact (hΛmem _).1 this
        exact Perm.inv_eq_iff_eq.2 (Classif.matchedK_fix hωω hκ hunm').symm
    rw [← hEq]; exact hmem
  have hD1 : swap (e0 0) (e0 1) * swap (e0 2) (e0 3) ∈ P' :=
    hDmem ε1 hε1 _ (fun i => by rw [hf1, swapProd_frame he0]) (fun i hi => swapProd_off _ _ _ _ hi)
  have hD2 : swap (e0 0) (e0 2) * swap (e0 1) (e0 3) ∈ P' :=
    hDmem ε2 hε2 _ (fun i => by rw [hf2, swapProd_frame he0]) (fun i hi => swapProd_off _ _ _ _ hi)
  have hD3 : swap (e0 0) (e0 3) * swap (e0 1) (e0 2) ∈ P' :=
    hDmem ε3 hε3 _ (fun i => by rw [hf3, swapProd_frame he0]) (fun i hi => swapProd_off _ _ _ _ hi)
  have hDW : ∀ ε ∈ E_A, ∀ D : Perm (Fin m), (∀ i, ε (e0 i) = D (e0 i)) →
      (∀ i, i ∉ Set.range e0 → D i = i) → D ∈ W := by
    intro ε hε D hεD hDoff
    obtain ⟨g0, hg0, hg0F, hg0off⟩ := exists_clean ω (fun y => ω y ≠ y) (fun x hx => hx)
      (fun x _ => hωω x) (fun x hx => by
        show ω (ω x) ≠ ω x
        rw [hωω x]; exact fun h => hx h.symm) W (fun x hx => hωsw x hx) ε (hEW hε)
      (fun y hy => by
        have hy' : Classif.partner hP.twoGroup y ≠ y := by rw [← hωdef]; exact hy
        have := hP.blockTrivial_of_unmatched hex ε (hEW hε) y hy'
        rwa [← hωdef] at this)
    have hEq : g0 = D := by
      refine eq_of_frame (e := e0) (fun i hi => ?_) hDoff (fun i => ?_)
      · exact hg0F i (fun h => hi (by rw [hrange]; exact (hΛmem i).2 h))
      · have hΛi : ¬ ω (e0 i) ≠ e0 i := by
          intro h
          have : e0 i ∈ Λ := by rw [← Finset.mem_coe, ← hrange]; exact Set.mem_range_self i
          exact h ((hΛmem _).1 this)
        rw [hg0off (e0 i) hΛi, hεD i]
    rw [← hEq]; exact hg0
  have hD1W : swap (e0 0) (e0 1) * swap (e0 2) (e0 3) ∈ W :=
    hDW ε1 hε1 _ (fun i => by rw [hf1, swapProd_frame he0]) (fun i hi => swapProd_off _ _ _ _ hi)
  refine false_of_klein_theta hE0 hE0n hX hA hL hm e hNS hθS hunm hfix Λ ?_ hΛcard e0 he0 hrange
    (hP'S hD1) (hP'S hD2) (hP'S hD3) hD1W
  intro z
  rw [hΛmem, hωdef]
  constructor
  · intro h y hy1 hy2
    have := Classif.partner_eq_of_swap_mem hP.twoGroup hy1 hy2
    rw [h] at this
    exact hy1 this
  · intro h
    by_contra hne
    obtain ⟨y, hy1, hy2⟩ := (Classif.partner_ne_iff hP.twoGroup).1 hne
    exact h y hy1 hy2

theorem eightTenNodeFourOrbitFixed_of_E0 (hE0 : E0Statement) (hE0n : E0NotYStatement) :
    EightTenNodeFourOrbitFixed := by
  intro G _ _ X S L hX hA hL m hm e hN θ hNS hθS A hAm x hx hunm hcnt hfix
  classical
  exact (false_of_fourOrbit_fixed hE0 hE0n hX hA hL hm e hNS hθS hAm hx hunm hcnt hfix).elim

theorem eightTenNodeFourOrbit_of_E0 (hE0 : E0Statement) (hE0n : E0NotYStatement) :
    EightTenNodeFourOrbit :=
  eightTenNodeFourOrbit_of_fixed (eightTenNodeFourOrbitFixed_of_E0 hE0 hE0n)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
