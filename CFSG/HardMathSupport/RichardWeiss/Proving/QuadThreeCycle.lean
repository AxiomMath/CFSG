module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.CocycleGen
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockBridge
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ThetaShapes
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFourCocycle

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open
open CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G} {N : ℕ}

omit [Finite G] in
theorem conj_mul_inv_mem_centralizer_of_fix (hN : 7 ≤ N)
    {π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart N)} {θ : ↥(L ⊔ S) →* Perm (Fin N)}
    (hker : π.ker =
      (⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅blockV S L, L⁆)
    (hAθ : ∀ σ ∈ alternatingGroup (Fin N), ∃ l : ↥L, θ (Subgroup.inclusion le_sup_left l) = σ)
    (hequiv : SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ)
    (hf : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G))
    (hLA : ∀ l : ↥L, θ (Subgroup.inclusion le_sup_left l) ∈ alternatingGroup (Fin N))
    (Δ : Finset (Fin N)) (hΓ : ∃ k : Fin N, k ∉ Δ)
    (P : Subgroup (Perm (Fin N)))
    (hPS : ∀ p ∈ P, ∃ l : ↥L, (l : G) ∈ S ∧ θ (Subgroup.inclusion le_sup_left l) = p)
    (hPfix : ∀ p ∈ P, ∀ i : Fin N, i ∉ Δ → p i = i)
    (hPtrans : ∀ i ∈ Δ, ∀ j ∈ Δ, ∃ p ∈ P, p i = j)
    {v : G} (hvV : v ∈ blockV S L) (hvS : ∀ t ∈ S, t * v = v * t)
    (l : ↥L) (hl : ∀ i : Fin N, i ∉ Δ → θ (Subgroup.inclusion le_sup_left l) i = i) :
    (l : G) * v * (l : G)⁻¹ * v⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  classical
  set ι : ↥L →* ↥(L ⊔ S) := Subgroup.inclusion le_sup_left with hι
  have hVel := CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isElemAbelian_blockV S L
  have hcommV : ∀ a ∈ blockV S L, ∀ b ∈ blockV S L, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVel.1.is_comm.comm (⟨a, ha⟩ : ↥(blockV S L)) ⟨b, hb⟩)
  let D : ↥L → G := fun g => (g : G) * v * (g : G)⁻¹ * v⁻¹
  have hDW : ∀ g : ↥L, D g ∈ ⁅blockV S L, L⁆ := fun g => by
    have h := Subgroup.commutator_mem_commutator g.2 hvV
    rw [Subgroup.commutator_comm] at h
    simpa only [commutatorElement_def] using h
  have hDV : ∀ g : ↥L, D g ∈ blockV S L := fun g => commutator_blockV_le S L (hDW g)
  have hDmul : ∀ g g' : ↥L, D (g * g') = ((g : G) * D g' * (g : G)⁻¹) * D g := by
    intro g g'
    simp only [D, Subgroup.coe_mul]
    group
  have hwd : ∀ g g' : ↥L, θ (ι g) = θ (ι g') → D g = D g' := by
    intro g g' h
    have h1 : θ (ι (g'⁻¹ * g)) = 1 := by rw [map_mul, map_mul, map_inv, map_inv, h, inv_mul_cancel]
    have h2 : v * ((g' : G)⁻¹ * g) = ((g' : G)⁻¹ * g) * v := by
      have h3 := Subgroup.mem_centralizer_iff.1 (hf _ h1) v hvV
      simpa [hι] using h3
    have h4 : (g : G) * v * (g : G)⁻¹ = (g' : G) * v * (g' : G)⁻¹ := by
      calc (g : G) * v * (g : G)⁻¹ = (g' : G) * (((g' : G)⁻¹ * g) * v) * (g : G)⁻¹ := by group
        _ = (g' : G) * (v * ((g' : G)⁻¹ * g)) * (g : G)⁻¹ := by rw [h2]
        _ = (g' : G) * v * (g' : G)⁻¹ := by group
    simp only [D, h4]
  let c : Perm (Fin N) → altHeart N := fun σ =>
    if h : ∃ g : ↥L, θ (ι g) = σ then Multiplicative.toAdd (π ⟨D h.choose, hDW h.choose⟩) else 0
  have hc : ∀ g : ↥L, c (θ (ι g)) = Multiplicative.toAdd (π ⟨D g, hDW g⟩) := by
    intro g
    have h : ∃ g' : ↥L, θ (ι g') = θ (ι g) := ⟨g, rfl⟩
    have h1 : (⟨D h.choose, hDW h.choose⟩ : ↥⁅blockV S L, L⁆) = ⟨D g, hDW g⟩ :=
      Subtype.ext (hwd _ _ h.choose_spec)
    simp only [c, dite_eq_left h, h1]
  have hconj : ∀ (g : ↥L) (w : ↥⁅blockV S L, L⁆) (hw : (g : G) * w * (g : G)⁻¹ ∈ ⁅blockV S L, L⁆),
      Multiplicative.toAdd (π ⟨(g : G) * w * (g : G)⁻¹, hw⟩) =
        altAct (θ (ι g)) (Multiplicative.toAdd (π w)) := by
    intro g w hw
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (π w))
    have h := hequiv (ι g) w ⟨_, hw⟩ rfl x hx.symm
    rw [h, ← hx, altAct_mk]
  have hcoc : ∀ σ ∈ alternatingGroup (Fin N), ∀ τ ∈ alternatingGroup (Fin N),
      c (σ * τ) = c σ + altAct σ (c τ) := by
    intro σ hσ τ hτ
    obtain ⟨g, rfl⟩ := hAθ σ hσ
    obtain ⟨g', rfl⟩ := hAθ τ hτ
    have hmem : (g : G) * D g' * (g : G)⁻¹ ∈ ⁅blockV S L, L⁆ :=
      conj_mem_commutator_blockV g.2 (hDW g')
    rw [← map_mul θ, ← map_mul ι, hc, hc, hc]
    have h1 : (⟨D (g * g'), hDW _⟩ : ↥⁅blockV S L, L⁆) =
        ⟨D g, hDW g⟩ * ⟨(g : G) * D g' * (g : G)⁻¹, hmem⟩ :=
      Subtype.ext (by
        show D (g * g') = D g * ((g : G) * D g' * (g : G)⁻¹)
        rw [hDmul]
        exact hcommV _ (commutator_blockV_le S L hmem) _ (hDV g))
    rw [h1, map_mul, toAdd_mul, hconj g ⟨D g', hDW g'⟩ hmem]
  have hPA : P ≤ alternatingGroup (Fin N) := by
    intro p hp
    obtain ⟨g, -, rfl⟩ := hPS p hp
    exact hLA g
  have hcP : ∀ p ∈ P, c p = 0 := by
    intro p hp
    obtain ⟨g, hgS, rfl⟩ := hPS p hp
    rw [hc]
    have h1 : (⟨D g, hDW g⟩ : ↥⁅blockV S L, L⁆) = 1 := by
      apply Subtype.ext
      show (g : G) * v * (g : G)⁻¹ * v⁻¹ = 1
      rw [hvS _ hgS]
      group
    rw [h1, map_one, toAdd_one]
  have hDC : ∀ g : ↥L, (∀ i : Fin N, i ∉ Δ → θ (ι g) i = i) →
      D g ∈ Subgroup.centralizer (L : Set G) := by
    intro g hg
    have h0 := altCocycle_eq_zero_of_fix hN Δ hΓ P hPA hPfix hPtrans c hcoc hcP (hLA g) hg
    rw [hc, toAdd_eq_zero] at h0
    have h2 : (⟨D g, hDW g⟩ : ↥⁅blockV S L, L⁆) ∈ π.ker := h0
    rw [hker, Subgroup.mem_subgroupOf] at h2
    exact h2.2
  exact hDC l hl

omit [Finite G] in
theorem conj_eq_of_fix_of_odd (hN : 7 ≤ N)
    {π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart N)} {θ : ↥(L ⊔ S) →* Perm (Fin N)}
    (hker : π.ker =
      (⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅blockV S L, L⁆)
    (hAθ : ∀ σ ∈ alternatingGroup (Fin N), ∃ l : ↥L, θ (Subgroup.inclusion le_sup_left l) = σ)
    (hequiv : SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ)
    (hf : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G))
    (hLA : ∀ l : ↥L, θ (Subgroup.inclusion le_sup_left l) ∈ alternatingGroup (Fin N))
    (Δ : Finset (Fin N)) (hΓ : ∃ k : Fin N, k ∉ Δ)
    (P : Subgroup (Perm (Fin N)))
    (hPS : ∀ p ∈ P, ∃ l : ↥L, (l : G) ∈ S ∧ θ (Subgroup.inclusion le_sup_left l) = p)
    (hPfix : ∀ p ∈ P, ∀ i : Fin N, i ∉ Δ → p i = i)
    (hPtrans : ∀ i ∈ Δ, ∀ j ∈ Δ, ∃ p ∈ P, p i = j)
    {v : G} (hvV : v ∈ blockV S L) (hvS : ∀ t ∈ S, t * v = v * t)
    (l : ↥L) (hl : ∀ i : Fin N, i ∉ Δ → θ (Subgroup.inclusion le_sup_left l) i = i)
    {m : ℕ} (hm : Odd m) (hlm : (l : G) ^ m = 1) :
    (l : G) * v * (l : G)⁻¹ = v := by
  classical
  have hC := conj_mul_inv_mem_centralizer_of_fix hN hker hAθ hequiv hf hLA Δ hΓ P hPS hPfix
    hPtrans hvV hvS l hl
  have hVel := CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isElemAbelian_blockV S L
  have hDV : (l : G) * v * (l : G)⁻¹ * v⁻¹ ∈ blockV S L := by
    have h := Subgroup.commutator_mem_commutator l.2 hvV
    rw [Subgroup.commutator_comm] at h
    have hDW : (l : G) * v * (l : G)⁻¹ * v⁻¹ ∈ ⁅blockV S L, L⁆ := by
      simpa only [commutatorElement_def] using h
    exact commutator_blockV_le S L hDW
  set κ := (l : G) * v * (l : G)⁻¹ * v⁻¹ with hκdef
  have hκ2 : κ ^ 2 = 1 := hVel.2 κ hDV
  have hgκ : (l : G) * κ * (l : G)⁻¹ = κ := by
    have h := Subgroup.mem_centralizer_iff.1 hC (l : G) l.2
    rw [h, mul_inv_cancel_right]
  have hgw : (l : G) * v * (l : G)⁻¹ = κ * v := by
    rw [hκdef]
    group
  have hκ1 : κ = 1 :=
    CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.eq_one_of_conj_eq_mul hgw hgκ hκ2 hm hlm
  have h := hκ1
  rw [hκdef] at h
  exact mul_inv_eq_one.1 h

theorem normalizer_of_transitive_support_of_odd (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hN : 7 ≤ N)
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} (hNS : NaturalSectionTheta S L N θ)
    (Δ : Finset (Fin N)) (hΓ : ∃ k : Fin N, k ∉ Δ)
    (P : Subgroup (Perm (Fin N)))
    (hPS : ∀ p ∈ P, ∃ l : ↥L, (l : G) ∈ S ∧ θ (Subgroup.inclusion le_sup_left l) = p)
    (hPfix : ∀ p ∈ P, ∀ i : Fin N, i ∉ Δ → p i = i)
    (hPtrans : ∀ i ∈ Δ, ∀ j ∈ Δ, ∃ p ∈ P, p i = j)
    (l : ↥L) (hl : ∀ i : Fin N, i ∉ Δ → θ (Subgroup.inclusion le_sup_left l) i = i)
    {m : ℕ} (hm : Odd m) (hlm : (l : G) ^ m = 1) :
    (l : G) ∈ Subgroup.normalizer (S : Set G) := by
  classical
  obtain ⟨π, hπ, hker, hAθ, hequiv, hf⟩ := hNS
  have hLA : ∀ l : ↥L, θ (Subgroup.inclusion le_sup_left l) ∈ alternatingGroup (Fin N) :=
    theta_mem_alternatingGroup hL.perfect θ
  have hvS : ∀ v ∈ CFSG.Quasithin.omegaOneCenterOf S, ∀ t ∈ S, t * v = v * t := by
    intro v hv t ht
    have hvC : v ∈ Subgroup.centralizer (S : Set G) :=
      ((Subgroup.closure_le _).2 (fun x hx => hx.1.2) :
        CFSG.Quasithin.omegaOneCenterOf S ≤ Subgroup.centralizer (S : Set G)) hv
    exact Subgroup.mem_centralizer_iff.1 hvC t ht
  have hcent : ∀ v ∈ CFSG.Quasithin.omegaOneCenterOf S, (l : G) * v * (l : G)⁻¹ = v :=
    fun v hv => conj_eq_of_fix_of_odd hN hker hAθ hequiv hf hLA Δ hΓ P hPS hPfix
      hPtrans (omegaOneCenterOf_le_blockV hA hL hSL hv) (hvS v hv) l hl hm hlm
  have hlN : (l : G) ∈ Subgroup.normalizer (CFSG.Quasithin.omegaOneCenterOf S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hcent h hh]
      exact hh
    · intro hh
      have h2 := hcent _ hh
      have h3 : (l : G) * h * (l : G)⁻¹ = h := by
        calc (l : G) * h * (l : G)⁻¹ =
            (l : G)⁻¹ * ((l : G) * ((l : G) * h * (l : G)⁻¹) * (l : G)⁻¹) * (l : G) := by group
          _ = (l : G)⁻¹ * ((l : G) * h * (l : G)⁻¹) * (l : G) := by rw [h2]
          _ = h := by group
      rwa [h3] at hh
  have hle : X ⊓ Subgroup.normalizer (CFSG.Quasithin.omegaOneCenterOf S : Set G) ≤
      CFSG.Quasithin.cgsIn X S :=
    le_iSup_of_le (CFSG.Quasithin.omegaOneCenterOf S)
      (le_iSup_of_le (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le S)
        (le_iSup_of_le (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot
          hA.twoRadical.isPGroup hA.twoRadical.2.1)
          (le_iSup_of_le (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf S) le_rfl)))
  rw [hA.cgs] at hle
  exact (hle ⟨hL.le l.2, hlN⟩).2

omit [Finite G] in
theorem theta_mem_normalizer_map {θ : ↥(L ⊔ S) →* Perm (Fin N)} (l : ↥L)
    (hlN : (l : G) ∈ Subgroup.normalizer (S : Set G)) :
    θ (Subgroup.inclusion le_sup_left l) ∈
      Subgroup.normalizer
        (((S.subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin N))) : Set (Perm (Fin N))) := by
  classical
  have hι : ∀ (m : ↥(L ⊔ S)), ((Subgroup.inclusion le_sup_left l * m *
      (Subgroup.inclusion le_sup_left l)⁻¹ : ↥(L ⊔ S)) : G) = (l : G) * (m : G) * (l : G)⁻¹ := by
    intro m; simp
  have hlN' := Subgroup.mem_normalizer_iff.1 hlN
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨Subgroup.inclusion le_sup_left l * m * (Subgroup.inclusion le_sup_left l)⁻¹, ?_, ?_⟩
    · show _ ∈ S.subgroupOf (L ⊔ S)
      rw [Subgroup.mem_subgroupOf, hι]
      exact (hlN' (m : G)).1 (Subgroup.mem_subgroupOf.1 hm)
    · rw [map_mul, map_mul, map_inv]
  · rintro ⟨m, hm, hz⟩
    refine ⟨(Subgroup.inclusion le_sup_left l)⁻¹ * m * Subgroup.inclusion le_sup_left l, ?_, ?_⟩
    · show _ ∈ S.subgroupOf (L ⊔ S)
      rw [Subgroup.mem_subgroupOf]
      have hm' := Subgroup.mem_subgroupOf.1 hm
      have h1 : (((Subgroup.inclusion le_sup_left l)⁻¹ * m *
          Subgroup.inclusion le_sup_left l : ↥(L ⊔ S)) : G) =
          (l : G)⁻¹ * (m : G) * (l : G) := by simp
      rw [h1]
      refine (hlN' ((l : G)⁻¹ * (m : G) * (l : G))).2 ?_
      have : (l : G) * ((l : G)⁻¹ * (m : G) * (l : G)) * (l : G)⁻¹ = (m : G) := by group
      rw [this]
      exact hm'
    · rw [map_mul, map_mul, map_inv, hz]
      group

theorem threeCycle_mem_normalizer_of_transitive_support (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hN : 7 ≤ N)
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} (hNS : NaturalSectionTheta S L N θ)
    (Δ : Finset (Fin N)) (hΓ : ∃ k : Fin N, k ∉ Δ) (P : Subgroup (Perm (Fin N)))
    (hPS : ∀ p ∈ P, ∃ l : ↥L, (l : G) ∈ S ∧ θ (Subgroup.inclusion le_sup_left l) = p)
    (hPfix : ∀ p ∈ P, ∀ i : Fin N, i ∉ Δ → p i = i)
    (hPtrans : ∀ i ∈ Δ, ∀ j ∈ Δ, ∃ p ∈ P, p i = j)
    {σ : Perm (Fin N)} (hσ : σ.IsThreeCycle) (hσfix : ∀ i : Fin N, i ∉ Δ → σ i = i) :
    σ ∈ Subgroup.normalizer
      (((S.subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin N))) : Set (Perm (Fin N))) := by
  classical
  have hNS' := hNS
  obtain ⟨-, -, -, hAθ, -, -⟩ := hNS'
  obtain ⟨l, hl0⟩ := hAθ σ hσ.mem_alternatingGroup
  have hl : θ (Subgroup.inclusion le_sup_left l) = σ := hl0
  have hord : orderOf (l : G) ≠ 0 := (orderOf_pos (l : G)).ne'
  obtain ⟨a, m, hm, hdec⟩ := Nat.exists_eq_two_pow_mul_odd hord
  have hlm : ((l ^ 2 ^ a : ↥L) : G) ^ m = 1 := by
    rw [Subgroup.coe_pow, ← pow_mul, ← hdec]
    exact pow_orderOf_eq_one _
  have hθl : θ (Subgroup.inclusion le_sup_left (l ^ 2 ^ a)) = σ ^ 2 ^ a := by
    rw [map_pow, map_pow, hl]
  have hfix : ∀ i : Fin N, i ∉ Δ → θ (Subgroup.inclusion le_sup_left (l ^ 2 ^ a)) i = i := by
    intro i hi
    rw [hθl]
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self (hσfix i hi) _
  have hlN := normalizer_of_transitive_support_of_odd hA hL hSL hN hNS Δ hΓ P hPS hPfix
    hPtrans (l ^ 2 ^ a) hfix hm hlm
  have hmem := theta_mem_normalizer_map (θ := θ) (l ^ 2 ^ a) hlN
  rw [hθl] at hmem
  have hσeq : (σ ^ 2 ^ a) ^ 2 ^ a = σ := by
    have hord3 : σ ^ 3 = 1 := by
      have h := pow_orderOf_eq_one σ
      rwa [hσ.orderOf] at h
    have h4 : 2 ^ a * 2 ^ a = 4 ^ a := by
      rw [← mul_pow]
      norm_num
    have h41 : 4 ^ a % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    rw [← pow_mul, h4, pow_eq_pow_mod _ hord3, h41, pow_one]
  have h5 := pow_mem hmem (2 ^ a)
  rwa [hσeq] at h5

theorem false_of_swap_mem_theta (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hN : 7 ≤ N)
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} (hNS : NaturalSectionTheta S L N θ)
    (Δ : Finset (Fin N)) (hΓ : ∃ k : Fin N, k ∉ Δ) (P : Subgroup (Perm (Fin N)))
    (hPS : ∀ p ∈ P, ∃ l : ↥L, (l : G) ∈ S ∧ θ (Subgroup.inclusion le_sup_left l) = p)
    (hPfix : ∀ p ∈ P, ∀ i : Fin N, i ∉ Δ → p i = i)
    (hPtrans : ∀ i ∈ Δ, ∀ j ∈ Δ, ∃ p ∈ P, p i = j)
    {a b c : Fin N} (ha : a ∈ Δ) (hb : b ∈ Δ) (hc : c ∈ Δ) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c)
    {s : ↥(L ⊔ S)} (hs : (s : G) ∈ S) (hsa : θ s a = b) (hsb : θ s b = a) (hsc : θ s c = c) :
    False := by
  classical
  set Z : Subgroup (Perm (Fin N)) := (S.subgroupOf (L ⊔ S)).map θ with hZ
  have hZ2 : IsPGroup 2 Z := (hA.twoRadical.isPGroup.comap_subtype (K := L ⊔ S)).map θ
  set σ : Perm (Fin N) := swap a b * swap a c with hσdef
  have hσ : σ.IsThreeCycle := Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  have hσa : σ a = c := by
    simp [hσdef, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hac.symm, hbc.symm]
  have hσb : σ b = a := by
    simp [hσdef, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hab.symm, hbc]
  have hσc : σ c = b := by
    simp [hσdef, Equiv.Perm.mul_apply]
  have hσfix : ∀ i : Fin N, i ≠ a → i ≠ b → i ≠ c → σ i = i := by
    intro i hia hib hic
    simp [hσdef, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hia, hib, hic]
  have hσinvA : σ⁻¹ a = b := Equiv.Perm.inv_eq_iff_eq.2 hσb.symm
  have hσinvB : σ⁻¹ b = c := Equiv.Perm.inv_eq_iff_eq.2 hσc.symm
  have hσinvC : σ⁻¹ c = a := Equiv.Perm.inv_eq_iff_eq.2 hσa.symm
  have hkey : σ * θ s = θ s * σ⁻¹ := by
    refine Equiv.ext fun y => ?_
    simp only [Equiv.Perm.mul_apply]
    by_cases hya : y = a
    · rw [hya, hsa, hσinvA, hsb, hσb]
    by_cases hyb : y = b
    · rw [hyb, hsb, hσinvB, hsc, hσa]
    by_cases hyc : y = c
    · rw [hyc, hsc, hσinvC, hsa, hσc]
    have hy1 : σ⁻¹ y = y := Equiv.Perm.inv_eq_iff_eq.2 (hσfix y hya hyb hyc).symm
    rw [hy1]
    have h1 : θ s y ≠ a := fun h => hyb ((θ s).injective (h.trans hsb.symm))
    have h2 : θ s y ≠ b := fun h => hya ((θ s).injective (h.trans hsa.symm))
    have h3 : θ s y ≠ c := fun h => hyc ((θ s).injective (h.trans hsc.symm))
    exact hσfix _ h1 h2 h3
  have hσΔ : ∀ i : Fin N, i ∉ Δ → σ i = i := fun i hi =>
    hσfix i (fun h => hi (by rw [h]; exact ha)) (fun h => hi (by rw [h]; exact hb))
      (fun h => hi (by rw [h]; exact hc))
  have hσN := threeCycle_mem_normalizer_of_transitive_support hA hL hSL hN hNS Δ hΓ P hPS hPfix
    hPtrans hσ hσΔ
  have hsZ : θ s ∈ Z := ⟨s, Subgroup.mem_subgroupOf.2 hs, rfl⟩
  have hmem : σ * θ s * σ⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.1 hσN (θ s)).1 hsZ
  rw [hkey] at hmem
  have hg : σ⁻¹ * σ⁻¹ ∈ Z := by
    have h := Z.mul_mem (Z.inv_mem hsZ) hmem
    rwa [show (θ s)⁻¹ * (θ s * σ⁻¹ * σ⁻¹) = σ⁻¹ * σ⁻¹ by group] at h
  have hσ3 : σ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one σ
    rwa [hσ.orderOf] at h
  have h3 : (σ⁻¹ * σ⁻¹) ^ 3 = 1 := by
    calc (σ⁻¹ * σ⁻¹) ^ 3 = (σ ^ 3)⁻¹ ^ 2 := by group
      _ = 1 := by rw [hσ3, inv_one, one_pow]
  obtain ⟨k, hk⟩ := hZ2 ⟨σ⁻¹ * σ⁻¹, hg⟩
  have hk' : (σ⁻¹ * σ⁻¹) ^ 2 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  have hgcd : (σ⁻¹ * σ⁻¹) ^ Nat.gcd (2 ^ k) 3 = 1 := pow_gcd_eq_one.2 ⟨hk', h3⟩
  have hcop : Nat.gcd (2 ^ k) 3 = 1 :=
    Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (by norm_num))
  rw [hcop, pow_one] at hgcd
  have hτ3 : σ⁻¹ ^ 3 = 1 := by rw [inv_pow, hσ3, inv_one]
  have hinv : σ⁻¹ = 1 := by
    calc σ⁻¹ = σ⁻¹ ^ 3 * σ⁻¹ := by rw [hτ3, one_mul]
      _ = (σ⁻¹ * σ⁻¹) * (σ⁻¹ * σ⁻¹) := by group
      _ = 1 := by rw [hgcd, one_mul]
  have hσ1 : σ = 1 := inv_eq_one.1 hinv
  have hord := hσ.orderOf
  rw [hσ1, orderOf_one] at hord
  norm_num at hord

end CFSG.HardMathSupport.RichardWeiss.Proving

end
