module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.Core
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.OffenderMax
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.OffenderChain
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.OffenderCount
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ThetaSCore
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Star
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockBridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open scoped commutatorElement

variable {G : Type} [Group G]

theorem swap_mem_Wr (r s : ℕ) (k : Fin r) :
    swap (Sum.inl (k, false) : OmegaE r s) (Sum.inl (k, true)) ∈ Wr r s := by
  classical
  have h := embL_blockTransp r s k false
  simp only [Bool.not_false] at h
  rw [h]
  exact ⟨blockTransp k, swap_mem_blockFix rfl, rfl⟩

theorem permCongr_swap' {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β) (x y : α) :
    e.permCongr (swap x y) = swap (e x) (e y) := by
  refine Equiv.ext fun w => ?_
  rw [Equiv.permCongr_apply]
  by_cases h1 : e.symm w = x
  · have hw : w = e x := by rw [← h1]; simp
    subst hw
    simp
  by_cases h2 : e.symm w = y
  · have hw : w = e y := by rw [← h2]; simp
    subst hw
    simp
  have h3 : w ≠ e x := fun h => h1 (by rw [h]; simp)
  have h4 : w ≠ e y := fun h => h2 (by rw [h]; simp)
  rw [swap_apply_of_ne_of_ne h1 h2, swap_apply_of_ne_of_ne h3 h4]
  simp

variable [Finite G]

theorem commutator_ne_bot_of_offender {S L : Subgroup G}
    (hA : Asc81bHyp (L ⊔ S) S) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    {r d : ℕ} (hr : r = 3 ∨ 5 ≤ r) (e : Fin d ≃ OmegaE r 4)
    (π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart d)) (θ : ↥(L ⊔ S) →* Perm (Fin d))
    (hπ : Function.Surjective π)
    (hAlt : ∀ σ ∈ alternatingGroup (Fin d),
      ∃ l : ↥L, θ ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ = σ)
    (hequiv : SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ)
    (hθV : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G))
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    (hW : ((thompsonJ S).subgroupOf (L ⊔ S)).map (e.permCongrHom.toMonoidHom.comp θ) = Wr r 4)
    :
    ⁅omegaOneCenterOf (thompsonJ S), S⁆ ≠ ⊥ := by
  classical
  have hSM : S ≤ L ⊔ S := le_sup_right
  have hLM : L ≤ L ⊔ S := le_sup_left
  let θ' : ↥(L ⊔ S) →* Perm (OmegaE r 4) := e.permCongrHom.toMonoidHom.comp θ
  have hθ'def : ∀ m, θ' m = e.permCongr (θ m) := fun m => rfl
  have hθ'e : ∀ m x, θ' m (e x) = e (θ m x) := fun m x => by
    rw [hθ'def]; simp [Equiv.permCongr_apply]
  have hθ'inj : ∀ m, θ' m = 1 → θ m = 1 := fun m h => by
    apply e.permCongrHom.injective
    rw [map_one]; exact h
  have hker' : ∀ m : ↥(L ⊔ S), θ' m = 1 → (m : G) ∈ S := fun m h => hθS m (hθ'inj m h)
  have hAlt' : ∀ x ∈ alternatingGroup (OmegaE r 4), ∃ m : ↥(L ⊔ S), θ' m = x := by
    intro x hx
    have hx' : e.permCongr.symm x ∈ alternatingGroup (Fin d) := by
      rw [mem_alternatingGroup] at hx ⊢
      rw [← hx]
      have := Equiv.Perm.sign_permCongr e (e.permCongr.symm x)
      rw [← this]; simp
    obtain ⟨l, hl⟩ := hAlt _ hx'
    exact ⟨_, by rw [hθ'def, hl]; exact Equiv.apply_symm_apply _ _⟩
  have hVel : IsElemAbelian 2 (blockV S L) :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isElemAbelian_blockV S L
  have hMV : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.sup_le_normalizer_blockV S L
  have hVn : ∀ m ∈ L ⊔ S, ∀ v ∈ blockV S L, m * v * m⁻¹ ∈ blockV S L := fun m hm v hv =>
    (Subgroup.mem_normalizer_iff.1 (hMV hm) v).1 hv
  have hML : L ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (fun x hx => Subgroup.le_normalizer hx) hSL
  have hXn : ∀ m ∈ L ⊔ S, ∀ x ∈ ⁅blockV S L, L⁆, m * x * m⁻¹ ∈ ⁅blockV S L, L⁆ :=
    fun m hm x hx => conj_mem_commutator' (hMV hm) (hML hm) hx
  have hVS : blockV S L ≤ S :=
    (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _).trans hA.twoCore_le
  have hUV : ⁅blockV S L, L⁆ ≤ blockV S L := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    rw [commutatorElement_def]
    have := hVn l (hLM hl) v⁻¹ ((blockV S L).inv_mem hv)
    simpa [mul_assoc] using (blockV S L).mul_mem hv this
  let a : Fin r → Fin d := fun k => e.symm (Sum.inl (k, false))
  let b : Fin r → Fin d := fun k => e.symm (Sum.inl (k, true))
  let γ : Fin 4 → Fin d := fun j => e.symm (Sum.inr j)
  have hd : d = 2 * r + 4 := by
    have h1 : d = Fintype.card (OmegaE r 4) := by
      rw [← Fintype.card_congr e]; simp
    simp only [OmegaE, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool] at h1
    omega
  have hr3 : 3 ≤ r := by omega
  have hd3 : 3 ≤ d := by omega
  have hainj : Function.Injective a := fun i j h => by
    have := Sum.inl.inj (e.symm.injective h)
    exact (Prod.mk.inj this).1
  have hba : ∀ i j, b i ≠ a j := fun i j h => by
    have := Sum.inl.inj (e.symm.injective h)
    exact absurd (Prod.mk.inj this).2 (by simp)
  have haγ : ∀ i j, a i ≠ γ j := fun i j h => Sum.inl_ne_inr (e.symm.injective h)
  have hbγ : ∀ i j, b i ≠ γ j := fun i j h => Sum.inl_ne_inr (e.symm.injective h)
  have hW' : ∀ m ∈ (thompsonJ S).subgroupOf (L ⊔ S), θ' m ∈ Wr r 4 := fun m hm =>
    hW ▸ ⟨m, hm, rfl⟩
  let xh0 : evenWeight d := xvec (γ 0) (γ 2)
  have hhA : ∀ A : Subgroup G, A ≤ thompsonJ S →
      (QuotientAddGroup.mk xh0 : altHeart d) ∈ altFix d ((A.subgroupOf (L ⊔ S)).map θ) := by
    intro A hAJ
    refine mk_mem_altFix_of_fixed xh0 ?_
    rintro _ ⟨m, hm, rfl⟩
    have hmW : θ' m ∈ Wr r 4 :=
      hW' m (Subgroup.mem_subgroupOf.2 (hAJ (Subgroup.mem_subgroupOf.1 hm)))
    obtain ⟨x, -, hxe⟩ := hmW
    have hθm : ∀ j, θ m (γ j) = γ j := fun j => by
      apply e.injective
      rw [← hθ'e, show e (γ j) = Sum.inr j from by simp [γ], ← hxe]
      simp [embL_apply_inr]
    apply Subtype.ext
    funext p
    have key : ∀ j, (θ m)⁻¹ p = γ j ↔ p = γ j := fun j => by
      rw [Equiv.Perm.inv_eq_iff_eq, hθm]
    show xh0.1 ((θ m)⁻¹ p) = xh0.1 p
    simp only [xh0, xvec_apply, key]
  obtain ⟨u, hu⟩ := hπ (Multiplicative.ofAdd (QuotientAddGroup.mk xh0 : altHeart d))
  have hcentA : ∀ A : Subgroup G, IsMaxElemAbelian S A →
      ∀ a ∈ A, a * (u : G) = (u : G) * a := by
    intro A hAmax a ha
    have hAJ : A ≤ thompsonJ S := le_iSup₂_of_le A hAmax le_rfl
    have hAM : A ≤ L ⊔ S := hAmax.1.trans hSM
    obtain ⟨n, hn1, hn2⟩ := exists_count_le_index_altFix e θ hθV hW.le A hAJ
    have hV : (Subgroup.centralizer (A : Set G)).relIndex (blockV S L) ≤ n :=
      (relIndex_le_of_isMaxElemAbelian hAmax hVel hVS).trans hn1
    have := mem_centralizer_of_mem_altFix hπ hequiv hUV hV hn2 (hhA A hAJ) u hu
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
  let embR : Perm (Fin 4) →* Perm (OmegaE r 4) :=
    (Perm.sumCongrHom (Fin r × Bool) (Fin 4)).comp (MonoidHom.inr _ _)
  have hembR : ∀ σ, embR σ = Perm.sumCongr 1 σ := fun σ => rfl
  obtain ⟨hPN, hP2, hPnorm, hPmax⟩ := theta_S_normal_pCore hA hSM θ' hker' hAlt' hW (by omega)
  have hUN : ∀ g ∈ K4.map embR, g ∈ Subgroup.normalizer (Wr r 4 : Set (Perm (OmegaE r 4))) := by
    rintro _ ⟨σ, -, rfl⟩
    rw [hembR]
    exact sumCongr_mem_normalizer (Subgroup.one_mem _ : (1 : Perm (Fin r × Bool)) ∈
      wStab (Fin r) Bool) σ
  have hUnorm : ∀ h ∈ Subgroup.normalizer (Wr r 4 : Set (Perm (OmegaE r 4))),
      ∀ g ∈ K4.map embR, h * g * h⁻¹ ∈ K4.map embR := by
    intro h hh g hg
    obtain ⟨σ1, h1, σ2, rfl⟩ := mem_normalizer_Wr_iff.1 hh
    obtain ⟨σ, hσ, rfl⟩ := hg
    refine ⟨σ2 * σ * σ2⁻¹, K4_normal σ2 σ hσ, ?_⟩
    rw [hembR, hembR, Perm.sumCongr_inv, Perm.sumCongr_mul, Perm.sumCongr_mul]
    simp
  have hsK := hPmax (K4.map embR) hUN (K4_isPGroup.map embR) hUnorm
    (show embR (swap 0 1 * swap 2 3) ∈ K4.map embR from ⟨_, a4_mem_K4, rfl⟩)
  obtain ⟨s, hs, hsθ⟩ := hsK
  have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
  have hsγ : ∀ j, θ s (γ j) = γ ((swap (0 : Fin 4) 1 * swap (2 : Fin 4) 3 : Perm (Fin 4)) j) :=
    fun j => by
    apply e.injective
    rw [← hθ'e, hsθ, hembR]
    simp [γ]
  have hsM : (s : G) ∈ L ⊔ S := s.2
  intro hbot
  have hcm : ⁅z, (s : G)⁆ ∈ ⁅omegaOneCenterOf (thompsonJ S), S⁆ :=
    Subgroup.commutator_mem_commutator hzZ hsS
  rw [hbot, Subgroup.mem_bot] at hcm
  have hzs : (s : G) * z * (s : G)⁻¹ = z := by
    have : z * (s : G) * z⁻¹ * (s : G)⁻¹ = 1 := hcm
    have h2 : z * (s : G) = (s : G) * z := by
      have := congrArg (fun x => x * (s : G) * z) this
      simpa [mul_assoc] using this
    rw [← h2]; group
  have hu' : (s : G) * z * (s : G)⁻¹ ∈ ⁅blockV S L, L⁆ := hXn s hsM z u.2
  have hequ := hequiv s u ⟨(s : G) * z * (s : G)⁻¹, hu'⟩ rfl (xvec (γ 0) (γ 2))
    (by rw [hu]; rfl)
  have hu'u : (⟨(s : G) * z * (s : G)⁻¹, hu'⟩ : ↥⁅blockV S L, L⁆) = u := Subtype.ext hzs
  rw [hu'u, hu, toAdd_ofAdd] at hequ
  have hγinj : Function.Injective γ := fun i j h => Sum.inr.inj (e.symm.injective h)
  have e0 : (swap (0 : Fin 4) 1 * swap (2 : Fin 4) 3 : Perm (Fin 4)) 0 = 1 := by decide
  have e2 : (swap (0 : Fin 4) 1 * swap (2 : Fin 4) 3 : Perm (Fin 4)) 2 = 3 := by decide
  obtain ⟨q, hq⟩ : ∃ q : Fin d, q ∉ ({γ 0, γ 1, γ 2, γ 3} : Finset (Fin d)) := by
    have hlt : ({γ 0, γ 1, γ 2, γ 3} : Finset (Fin d)).card < (Finset.univ : Finset (Fin d)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      have := Finset.card_le_four (a := γ 0) (b := γ 1) (c := γ 2) (d := γ 3)
      omega
    obtain ⟨q, -, hq⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    exact ⟨q, hq⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
  exact mk_ewp_ne (θ s) (by rw [hsγ, e0]) (by rw [hsγ, e2])
    hq.1 hq.2.1 hq.2.2.1 hq.2.2.2
    (fun h => absurd (hγinj h) (by decide)) (fun h => absurd (hγinj h) (by decide))
    (fun h => absurd (hγinj h) (by decide)) hequ.symm

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
