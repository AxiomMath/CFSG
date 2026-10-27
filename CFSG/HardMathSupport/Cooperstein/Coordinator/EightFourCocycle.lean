module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.AltCocycle
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Star
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderGlue

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.AGLEmbedding (blockV)

variable {G : Type} [Group G] {S L : Subgroup G} {N : ℕ}

theorem commutator_blockV_le (S L : Subgroup G) : ⁅blockV S L, L⁆ ≤ blockV S L := by
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have hlV := (le_sup_left.trans (sup_le_normalizer_blockV S L)) hl
  have h1 : l * v⁻¹ * l⁻¹ ∈ blockV S L := (Subgroup.mem_normalizer_iff.1 hlV _).1 (inv_mem hv)
  have h2 := mul_mem hv h1
  rwa [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc l]

theorem conj_mem_commutator_blockV {l : G} (hl : l ∈ L) {w : G} (hw : w ∈ ⁅blockV S L, L⁆) :
    l * w * l⁻¹ ∈ ⁅blockV S L, L⁆ := by
  have hlV := (le_sup_left.trans (sup_le_normalizer_blockV S L)) hl
  have hlL : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hl
  have h1 : (⁅blockV S L, L⁆ : Subgroup G).map (MulAut.conj l : G →* G) = ⁅blockV S L, L⁆ := by
    rw [Subgroup.map_commutator, Subgroup.mem_normalizer_iff_map_conj_eq.1 hlV,
      Subgroup.mem_normalizer_iff_map_conj_eq.1 hlL]
  have h2 : (MulAut.conj l) w ∈ (⁅blockV S L, L⁆ : Subgroup G).map (MulAut.conj l : G →* G) :=
    ⟨w, hw, rfl⟩
  rw [h1] at h2
  simpa using h2

theorem theta_eq_one_of_centralizes (hN : 5 ≤ N)
    {π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart N)} {θ : ↥(L ⊔ S) →* Perm (Fin N)}
    (hπ : Function.Surjective π) (hequiv : SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ)
    {m : ↥(L ⊔ S)} (hm : (m : G) ∈ Subgroup.centralizer (blockV S L : Set G)) : θ m = 1 := by
  refine perm_eq_one_of_altHeart_fixed hN (θ m) fun x => ?_
  obtain ⟨u, hu⟩ := hπ (Multiplicative.ofAdd (QuotientAddGroup.mk x))
  have hu' : (u : G) = (m : G) * u * (m : G)⁻¹ := by
    have h := Subgroup.mem_centralizer_iff.1 hm (u : G) (commutator_blockV_le S L u.2)
    rw [← h, mul_inv_cancel_right]
  have h := hequiv m u u hu' x (by rw [hu]; rfl)
  rw [hu] at h
  exact h.symm

theorem theta_mem_alternatingGroup (hperf : ⁅L, L⁆ = L) (θ : ↥(L ⊔ S) →* Perm (Fin N))
    (l : ↥L) : θ (Subgroup.inclusion le_sup_left l) ∈ alternatingGroup (Fin N) := by
  let f : ↥L →* ℤˣ := Perm.sign.comp (θ.comp (Subgroup.inclusion le_sup_left))
  have h2 : commutator ↥L = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_subtype_commutator, hperf, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h3 : l ∈ f.ker := Abelianization.commutator_subset_ker f (h2 ▸ Subgroup.mem_top l)
  exact mem_alternatingGroup.2 (MonoidHom.mem_ker.1 h3)

theorem conj_eq_of_fix (hN : 7 ≤ N)
    {π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart N)} {θ : ↥(L ⊔ S) →* Perm (Fin N)}
    (hker : π.ker =
      (⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅blockV S L, L⁆)
    (hAθ : ∀ σ ∈ alternatingGroup (Fin N), ∃ l : ↥L, θ (Subgroup.inclusion le_sup_left l) = σ)
    (hequiv : SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ)
    (hf : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G))
    (hLA : ∀ l : ↥L, θ (Subgroup.inclusion le_sup_left l) ∈ alternatingGroup (Fin N))
    (Δ : Finset (Fin N)) (hΔ : 5 ≤ Δ.card) (hΓ : ∃ k : Fin N, k ∉ Δ)
    (P : Subgroup (Perm (Fin N)))
    (hPS : ∀ p ∈ P, ∃ l : ↥L, (l : G) ∈ S ∧ θ (Subgroup.inclusion le_sup_left l) = p)
    (hPfix : ∀ p ∈ P, ∀ i : Fin N, i ∉ Δ → p i = i)
    (hPtrans : ∀ i ∈ Δ, ∀ j ∈ Δ, ∃ p ∈ P, p i = j)
    {v : G} (hvV : v ∈ blockV S L) (hvS : ∀ t ∈ S, t * v = v * t)
    (l : ↥L) (hl : ∀ i : Fin N, i ∉ Δ → θ (Subgroup.inclusion le_sup_left l) i = i) :
    (l : G) * v * (l : G)⁻¹ = v := by
  classical
  set ι : ↥L →* ↥(L ⊔ S) := Subgroup.inclusion le_sup_left with hι
  have hcommV : ∀ a ∈ blockV S L, ∀ b ∈ blockV S L, a * b = b * a := by
    intro a ha b hb
    have h : IsMulCommutative ↥(blockV S L) :=
      (CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _).1
    exact congrArg Subtype.val (h.is_comm.comm (⟨a, ha⟩ : ↥(blockV S L)) ⟨b, hb⟩)
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
  have hlift : ∀ a : ↥(alternatingGroup ↥Δ), ∃ g : ↥L,
      θ (ι g) = ((alternatingGroup.ofSubtype Δ a : ↥(alternatingGroup (Fin N))) : Perm (Fin N)) :=
    fun a => hAθ _ (alternatingGroup.ofSubtype Δ a).2
  have hfixΔ : ∀ (a : ↥(alternatingGroup ↥Δ)) (i : Fin N), i ∉ Δ →
      ((alternatingGroup.ofSubtype Δ a : ↥(alternatingGroup (Fin N))) : Perm (Fin N)) i = i := by
    intro a i hi
    rw [alternatingGroup.coe_ofSubtype]
    exact Perm.ofSubtype_apply_of_not_mem _ hi
  let lift : ↥(alternatingGroup ↥Δ) → ↥L := fun a => (hlift a).choose
  have hliftθ : ∀ a, θ (ι (lift a)) =
      ((alternatingGroup.ofSubtype Δ a : ↥(alternatingGroup (Fin N))) : Perm (Fin N)) :=
    fun a => (hlift a).choose_spec
  have hDlift : ∀ a, D (lift a) ∈ Subgroup.centralizer (L : Set G) := fun a =>
    hDC (lift a) fun i hi => by rw [hliftθ]; exact hfixΔ a i hi
  let Φ : ↥(alternatingGroup ↥Δ) →* G := MonoidHom.mk' (fun a => D (lift a)) fun a b => by
    have h1 : θ (ι (lift (a * b))) = θ (ι (lift a * lift b)) := by
      rw [hliftθ, map_mul ι, map_mul θ, hliftθ, hliftθ, map_mul, Subgroup.coe_mul]
    show D (lift (a * b)) = D (lift a) * D (lift b)
    rw [hwd _ _ h1, hDmul]
    have h2 : (lift a : G) * D (lift b) * (lift a : G)⁻¹ = D (lift b) := by
      have h3 := Subgroup.mem_centralizer_iff.1 (hDlift b) (lift a : G) (lift a).2
      rw [h3, mul_inv_cancel_right]
    rw [h2]
    exact hcommV _ (hDV _) _ (hDV _)
  have hΦ : ∀ a, Φ a = 1 := by
    have hcomm : commutator ↥(alternatingGroup ↥Δ) ≤ Φ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact hcommV _ (hDV _) _ (hDV _)
    have htop := commutator_alternatingGroup_eq_top (α := ↥Δ)
      (by rw [Nat.card_eq_fintype_card, Fintype.card_coe]; exact hΔ)
    intro a
    exact hcomm (htop ▸ Subgroup.mem_top a)
  obtain ⟨a, ha⟩ := (alternatingGroup.mem_range_ofSubtype_iff Δ ⟨θ (ι l), hLA l⟩).2 (by
    intro i hi
    rw [Perm.mem_support] at hi
    by_contra h
    exact hi (hl i h))
  have h1 : θ (ι (lift a)) = θ (ι l) := by
    rw [hliftθ, ha]
  have h2 : D l = 1 := by
    rw [← hwd _ _ h1]
    exact hΦ a
  exact mul_inv_eq_one.1 h2

end CFSG.HardMathSupport.Cooperstein.Coordinator
