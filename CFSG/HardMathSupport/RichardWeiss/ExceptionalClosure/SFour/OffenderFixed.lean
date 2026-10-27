module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Star
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.Core
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.OffenderAux
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.OffenderChain
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.OffenderMax
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockBridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open scoped commutatorElement

theorem mk_ewp_xvec_ne {d : ℕ} (hd : 5 ≤ d) (f : Perm (Fin d)) {p q : Fin d} (hpq : p ≠ q)
    (hp1 : f p ≠ p) (hp2 : f p ≠ q) :
    (QuotientAddGroup.mk (evenWeightPerm f (xvec p q)) : altHeart d) ≠
      QuotientAddGroup.mk (xvec p q) := by
  classical
  intro h
  have h1 := QuotientAddGroup.eq.1 h.symm
  obtain ⟨c, hc⟩ := (mem_evenWeightOnes_iff d _).1 h1
  have hcoord : ∀ y, c = -((xvec p q : evenWeight d) : Fin d → ZMod 2) y +
      ((xvec p q : evenWeight d) : Fin d → ZMod 2) (f⁻¹ y) := fun y => (hc y).symm
  obtain ⟨r, hr⟩ : ∃ r : Fin d, r ∉ ({p, q, f p, f q} : Finset (Fin d)) := by
    have hlt : ({p, q, f p, f q} : Finset (Fin d)).card < (Finset.univ : Finset (Fin d)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      have := Finset.card_le_four (a := p) (b := q) (c := f p) (d := f q)
      omega
    obtain ⟨r, -, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    exact ⟨r, hr⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hr
  have hfr1 : f⁻¹ r ≠ p := fun h' => hr3 (by rw [Equiv.Perm.inv_eq_iff_eq] at h'; exact h')
  have hfr2 : f⁻¹ r ≠ q := fun h' => hr4 (by rw [Equiv.Perm.inv_eq_iff_eq] at h'; exact h')
  have hc0 : c = 0 := by
    have := hcoord r
    simp only [xvec_apply, hr1, hr2, hfr1, hfr2, ite_false] at this
    rw [this]; decide
  have hf1 : f⁻¹ (f p) = p := by simp
  have h' := hcoord (f p)
  simp only [xvec_apply, hf1, hp1, hp2, hpq, ite_true, ite_false, hc0] at h'
  revert h'
  decide

variable {G : Type} [Group G] [Finite G]

theorem commutator_ne_bot_of_fixed_vector {S L : Subgroup G}
    (hA : Asc81bHyp (L ⊔ S) S) (hSL : S ≤ Subgroup.normalizer (L : Set G)) {d : ℕ}
    (π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart d)) (θ : ↥(L ⊔ S) →* Perm (Fin d))
    (hπ : Function.Surjective π) (hequiv : SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ)
    (hθV : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G))
    (hoff : ∀ A : Subgroup G, IsMaxElemAbelian S A →
      Nat.card ((A.subgroupOf (L ⊔ S)).map θ) ≤
        (altFix d ((A.subgroupOf (L ⊔ S)).map θ)).index)
    (x : evenWeight d)
    (hx : ∀ m : ↥(L ⊔ S), (m : G) ∈ thompsonJ S → evenWeightPerm (θ m) x = x)
    (s : ↥(L ⊔ S)) (hsS : (s : G) ∈ S)
    (hs : (QuotientAddGroup.mk (evenWeightPerm (θ s) x) : altHeart d) ≠
      QuotientAddGroup.mk x) :
    ⁅omegaOneCenterOf (thompsonJ S), S⁆ ≠ ⊥ := by
  classical
  have hSM : S ≤ L ⊔ S := le_sup_right
  have hLM : L ≤ L ⊔ S := le_sup_left
  have hVel : IsElemAbelian 2 (blockV S L) :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isElemAbelian_blockV S L
  have hMV : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.sup_le_normalizer_blockV S L
  have hVn : ∀ m ∈ L ⊔ S, ∀ v ∈ blockV S L, m * v * m⁻¹ ∈ blockV S L := fun m hm v hv =>
    (Subgroup.mem_normalizer_iff.1 (hMV hm) v).1 hv
  have hML : L ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (fun y hy => Subgroup.le_normalizer hy) hSL
  have hXn : ∀ m ∈ L ⊔ S, ∀ y ∈ ⁅blockV S L, L⁆, m * y * m⁻¹ ∈ ⁅blockV S L, L⁆ :=
    fun m hm y hy => conj_mem_commutator' (hMV hm) (hML hm) hy
  have hVS : blockV S L ≤ S :=
    (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _).trans hA.twoCore_le
  have hUV : ⁅blockV S L, L⁆ ≤ blockV S L := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    rw [commutatorElement_def]
    have := hVn l (hLM hl) v⁻¹ ((blockV S L).inv_mem hv)
    simpa [mul_assoc] using (blockV S L).mul_mem hv this
  have hhA : ∀ A : Subgroup G, A ≤ thompsonJ S →
      (QuotientAddGroup.mk x : altHeart d) ∈ altFix d ((A.subgroupOf (L ⊔ S)).map θ) := by
    intro A hAJ
    refine mk_mem_altFix_of_fixed x ?_
    rintro _ ⟨m, hm, rfl⟩
    exact hx m (hAJ (Subgroup.mem_subgroupOf.1 hm))
  obtain ⟨u, hu⟩ := hπ (Multiplicative.ofAdd (QuotientAddGroup.mk x : altHeart d))
  have hcentA : ∀ A : Subgroup G, IsMaxElemAbelian S A →
      ∀ a ∈ A, a * (u : G) = (u : G) * a := by
    intro A hAmax a ha
    have hAJ : A ≤ thompsonJ S := le_iSup₂_of_le A hAmax le_rfl
    have hAM : A ≤ L ⊔ S := hAmax.1.trans hSM
    have hn1 := relIndex_le_card_image hAM θ hθV
    have hV : (Subgroup.centralizer (A : Set G)).relIndex (blockV S L) ≤
        Nat.card ((A.subgroupOf (L ⊔ S)).map θ) :=
      (relIndex_le_of_isMaxElemAbelian hAmax hVel hVS).trans hn1
    have := mem_centralizer_of_mem_altFix hπ hequiv hUV hV (hoff A hAmax) (hhA A hAJ) u hu
    exact Subgroup.mem_centralizer_iff.1 this a ha
  let z : G := (u : G)
  have hzV : z ∈ blockV S L := hUV u.2
  have hz2 : z ^ 2 = 1 := hVel.2 z hzV
  have hzS : z ∈ S := hVS hzV
  obtain ⟨A0, hA0⟩ := CFSG.Quasithin.exists_isMaxElemAbelian S
  have hzJ : z ∈ thompsonJ S := by
    have hzAm : z ∈ A0 := mem_of_commute_isMaxElemAbelian hA0 hzS hz2 (hcentA A0 hA0)
    have hA0J : A0 ≤ thompsonJ S := le_iSup₂_of_le A0 hA0 le_rfl
    exact hA0J hzAm
  have hzcent : ∀ j ∈ thompsonJ S, j * z = z * j := by
    have hJle : thompsonJ S ≤ Subgroup.centralizer ({z} : Set G) :=
      iSup₂_le fun A hA a ha => Subgroup.mem_centralizer_iff.2 fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (hcentA A hA a ha).symm
    intro j hj
    exact (Subgroup.mem_centralizer_iff.1 (hJle hj) z rfl).symm
  have hzZ : z ∈ omegaOneCenterOf (thompsonJ S) :=
    Subgroup.subset_closure ⟨⟨hzJ, Subgroup.mem_centralizer_iff.2 fun y hy => (hzcent y hy)⟩, hz2⟩
  intro hbot
  have hcm : ⁅z, (s : G)⁆ ∈ ⁅omegaOneCenterOf (thompsonJ S), S⁆ :=
    Subgroup.commutator_mem_commutator hzZ hsS
  rw [hbot, Subgroup.mem_bot] at hcm
  have hzs : (s : G) * z * (s : G)⁻¹ = z := by
    have : z * (s : G) * z⁻¹ * (s : G)⁻¹ = 1 := hcm
    have h2 : z * (s : G) = (s : G) * z := by
      have := congrArg (fun y => y * (s : G) * z) this
      simpa [mul_assoc] using this
    rw [← h2]; group
  have hu' : (s : G) * z * (s : G)⁻¹ ∈ ⁅blockV S L, L⁆ := hXn s s.2 z u.2
  have hequ := hequiv s u ⟨(s : G) * z * (s : G)⁻¹, hu'⟩ rfl x (by rw [hu]; rfl)
  have hu'u : (⟨(s : G) * z * (s : G)⁻¹, hu'⟩ : ↥⁅blockV S L, L⁆) = u := Subtype.ext hzs
  rw [hu'u, hu, toAdd_ofAdd] at hequ
  exact hs hequ.symm

theorem ewp_xvec_eq_of_pair {d : ℕ} (g : Perm (Fin d)) {p q : Fin d}
    (hg : (g p = p ∧ g q = q) ∨ (g p = q ∧ g q = p)) :
    evenWeightPerm g (xvec p q) = xvec p q := by
  classical
  apply Subtype.ext
  funext i
  have h1 : ((evenWeightPerm g (xvec p q) : evenWeight d) : Fin d → ZMod 2) i =
      (if g⁻¹ i = p then 1 else 0) + (if g⁻¹ i = q then 1 else 0) := rfl
  rw [h1, xvec_apply]
  have e1 : g⁻¹ i = p ↔ i = g p := by rw [Equiv.Perm.inv_eq_iff_eq]
  have e2 : g⁻¹ i = q ↔ i = g q := by rw [Equiv.Perm.inv_eq_iff_eq]
  simp only [e1, e2]
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, add_comm]

theorem commutator_ne_bot_of_moved_pair {S L : Subgroup G}
    (hA : Asc81bHyp (L ⊔ S) S) (hSL : S ≤ Subgroup.normalizer (L : Set G)) {d : ℕ} (hd : 5 ≤ d)
    (π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart d)) (θ : ↥(L ⊔ S) →* Perm (Fin d))
    (hπ : Function.Surjective π) (hequiv : SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ)
    (hθV : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G))
    (hoff : ∀ A : Subgroup G, IsMaxElemAbelian S A →
      Nat.card ((A.subgroupOf (L ⊔ S)).map θ) ≤
        (altFix d ((A.subgroupOf (L ⊔ S)).map θ)).index)
    {p q : Fin d} (hpq : p ≠ q)
    (hJ : ∀ m : ↥(L ⊔ S), (m : G) ∈ thompsonJ S →
      (θ m p = p ∧ θ m q = q) ∨ (θ m p = q ∧ θ m q = p))
    (s : ↥(L ⊔ S)) (hsS : (s : G) ∈ S) (hs1 : θ s p ≠ p) (hs2 : θ s p ≠ q) :
    ⁅omegaOneCenterOf (thompsonJ S), S⁆ ≠ ⊥ :=
  commutator_ne_bot_of_fixed_vector hA hSL π θ hπ hequiv hθV hoff (xvec p q)
    (fun m hm => ewp_xvec_eq_of_pair (θ m) (hJ m hm)) s hsS (mk_ewp_xvec_ne hd (θ s) hpq hs1 hs2)

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
