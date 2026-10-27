module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7Dim
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7SixNat
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7SixSplit
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7SixPerfect
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7SixAux

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open scoped commutatorElement

theorem inj_of_section {X : Type} [Group X] {T : Subgroup X} (hV : IsElemAbelian 2 (gnV T))
    {L : Subgroup (X ⧸ gnC T)} (eL : ↥L ≃* alternatingGroup (Fin 7)) (hperf : commutator ↥L = ⊤)
    {K N : Subgroup X} (hK : K = L.comap (QuotientGroup.mk' (gnC T))) (hN : N = ⁅gnV T, K⁆)
    (π : ↥N →* Multiplicative (altHeart 7)) (hπs : Function.Surjective π)
    (hπe : ∀ (l : X) (hl : QuotientGroup.mk' (gnC T) l ∈ L) (u v : ↥N), (v : X) = l * u * l⁻¹ →
      Multiplicative.toAdd (π v) =
        altAct (eL ⟨QuotientGroup.mk' (gnC T) l, hl⟩ : Equiv.Perm (Fin 7))
          (Multiplicative.toAdd (π u)))
    (hπk : ∀ u : ↥N, π u = 1 → ∀ k ∈ K, k * u * k⁻¹ = u) : Function.Injective π := by
  classical
  let _ : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  have hVn : (gnV T).Normal := CFSG.AGLEmbeddingD2.GN.normal_gnV T
  have hKmem : ∀ k : X, k ∈ K ↔ QuotientGroup.mk' (gnC T) k ∈ L := fun k => by rw [hK]; rfl
  have hNV : N ≤ gnV T := hN ▸ Subgroup.commutator_le_left _ _
  have hKN : K ≤ Subgroup.normalizer (N : Set X) :=
    hN ▸ Subgroup.normalizer_commutator_ge_right _ _
  let ρL := gnRep hV
  let ρ : alternatingGroup (Fin 7) →* Module.End (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    ρL.comp (L.subtype.comp eL.symm.toMonoidHom)
  have hρ : ∀ a x, ρ a x = ρL ((eL.symm a : ↥L) : X ⧸ gnC T) x := fun a x => rfl
  have hlift : ∀ a : alternatingGroup (Fin 7), ∃ k : X, k ∈ K ∧
      (QuotientGroup.mk k : X ⧸ gnC T) = ((eL.symm a : ↥L) : X ⧸ gnC T) := by
    intro a
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective ((eL.symm a : ↥L) : X ⧸ gnC T)
    refine ⟨k, (hKmem k).2 ?_, hk⟩
    have : QuotientGroup.mk' (gnC T) k = ((eL.symm a : ↥L) : X ⧸ gnC T) := hk
    rw [this]
    exact (eL.symm a).2
  have helt : ∀ (a : alternatingGroup (Fin 7)) (k : X),
      (QuotientGroup.mk k : X ⧸ gnC T) = ((eL.symm a : ↥L) : X ⧸ gnC T) →
        ∀ x, elt hV (ρ a x) = k * elt hV x * k⁻¹ := by
    intro a k hk x
    rw [hρ, ← hk]
    exact elt_gnRep hV k x
  let N0 : AddSubgroup (Additive (IntMod (gnV T) hV)) := (modOf hV N).toAddSubgroup
  have hN0mem : ∀ x, x ∈ N0 ↔ elt hV x ∈ N := fun x => Iff.rfl
  have hN0inv : ∀ (a : alternatingGroup (Fin 7)), ∀ x ∈ N0, ρ a x ∈ N0 := by
    intro a x hx
    obtain ⟨k, hkK, hk⟩ := hlift a
    rw [hN0mem, helt a k hk]
    exact (Subgroup.mem_normalizer_iff.1 (hKN hkK) _).1 ((hN0mem x).1 hx)
  let π0 : ↥N0 →+ altHeart 7 :=
    { toFun := fun x => Multiplicative.toAdd (π ⟨elt hV x.1, (hN0mem x.1).1 x.2⟩)
      map_zero' := by
        have h1 : (⟨elt hV ((0 : ↥N0) : Additive (IntMod (gnV T) hV)),
            (hN0mem _).1 (0 : ↥N0).2⟩ : ↥N) = 1 := Subtype.ext (elt_zero hV)
        show Multiplicative.toAdd (π ⟨elt hV ((0 : ↥N0) : Additive (IntMod (gnV T) hV)), _⟩) = 0
        rw [h1, map_one, toAdd_one]
      map_add' := fun x y => by
        have h1 : (⟨elt hV ((x + y : ↥N0) : Additive (IntMod (gnV T) hV)),
            (hN0mem _).1 (x + y : ↥N0).2⟩ : ↥N) =
            ⟨elt hV x.1, (hN0mem x.1).1 x.2⟩ * ⟨elt hV y.1, (hN0mem y.1).1 y.2⟩ :=
          Subtype.ext (elt_add hV x.1 y.1)
        show Multiplicative.toAdd (π ⟨elt hV ((x + y : ↥N0) : Additive (IntMod (gnV T) hV)), _⟩) =
          Multiplicative.toAdd (π ⟨elt hV x.1, _⟩) + Multiplicative.toAdd (π ⟨elt hV y.1, _⟩)
        rw [h1, map_mul, toAdd_mul] }
  have hπ0s : Function.Surjective π0 := by
    intro a
    obtain ⟨u, hu⟩ := hπs (Multiplicative.ofAdd a)
    obtain ⟨w, hw⟩ := exists_elt hV (hNV u.2)
    have hwN : w ∈ N0 := (hN0mem w).2 (hw ▸ u.2)
    refine ⟨⟨w, hwN⟩, ?_⟩
    have h1 : (⟨elt hV w, (hN0mem w).1 hwN⟩ : ↥N) = u := Subtype.ext hw
    show Multiplicative.toAdd (π ⟨elt hV w, _⟩) = a
    rw [h1, hu]
    rfl
  have hπ0e : ∀ (a : alternatingGroup (Fin 7)) (x : ↥N0),
      π0 ⟨ρ a x, hN0inv a x x.2⟩ = altAct (a : Equiv.Perm (Fin 7)) (π0 x) := by
    intro a x
    obtain ⟨k, hkK, hk⟩ := hlift a
    have hkL : QuotientGroup.mk' (gnC T) k ∈ L := (hKmem k).1 hkK
    have h1 := hπe k hkL ⟨elt hV x.1, (hN0mem x.1).1 x.2⟩
      ⟨elt hV (ρ a x.1), (hN0mem _).1 (hN0inv a x.1 x.2)⟩ (by
        show elt hV (ρ a x.1) = k * elt hV x.1 * k⁻¹
        exact helt a k hk x.1)
    have h2 : (⟨QuotientGroup.mk' (gnC T) k, hkL⟩ : ↥L) = eL.symm a := Subtype.ext hk
    rw [h2, MulEquiv.apply_symm_apply] at h1
    exact h1
  have hπ0k : ∀ x : ↥N0, π0 x = 0 → ∀ a, ρ a x = x := by
    intro x hx a
    obtain ⟨k, hkK, hk⟩ := hlift a
    have h1 : π ⟨elt hV x.1, (hN0mem x.1).1 x.2⟩ = 1 := by
      have : Multiplicative.toAdd (π ⟨elt hV x.1, (hN0mem x.1).1 x.2⟩) = 0 := hx
      exact Multiplicative.toAdd.injective this
    have h2 := hπk _ h1 k hkK
    apply elt_injective hV
    rw [helt a k hk]
    exact h2
  have hmodN : modOf hV N = commOn (gnRep hV) L ⊤ := by
    have e := subOf_commOn hV L
    rw [← hK, ← hN] at e
    rw [← e, modOf_subOf]
  have hperf0 : N0 ≤ AddSubgroup.closure
      {y | ∃ a : alternatingGroup (Fin 7), ∃ z ∈ N0, y = ρ a z - z} := by
    intro x hx
    have hx1 : x ∈ commOn (gnRep hV) L ⊤ := by rw [← hmodN]; exact hx
    have hx2 : x ∈ commOn (gnRep hV) L (commOn (gnRep hV) L ⊤) :=
      commOn_le_commOn_commOn (gnRep hV) hperf hx1
    have hspan := span_subset_addClosure
      {w | ∃ g ∈ L, ∃ u ∈ commOn (gnRep hV) L ⊤, w = gnRep hV g u - u} hx2
    refine AddSubgroup.closure_mono ?_ hspan
    rintro y ⟨g, hg, u, hu, rfl⟩
    have hu' : u ∈ N0 := by
      show u ∈ modOf hV N
      rw [hmodN]
      exact hu
    refine ⟨eL ⟨g, hg⟩, u, hu', ?_⟩
    rw [hρ]
    simp only [MulEquiv.symm_apply_apply]
    rfl
  have hinj0 := injective_of_natural_section ρ N0 hN0inv π0 hπ0s hπ0e hπ0k hperf0
  rw [injective_iff_map_eq_one]
  intro u hu
  obtain ⟨w, hw⟩ := exists_elt hV (hNV u.2)
  have hwN : w ∈ N0 := (hN0mem w).2 (hw ▸ u.2)
  have h1 : (⟨elt hV w, (hN0mem w).1 hwN⟩ : ↥N) = u := Subtype.ext hw
  have h2 : π0 ⟨w, hwN⟩ = π0 0 := by
    show Multiplicative.toAdd (π ⟨elt hV w, _⟩) = π0 0
    rw [h1, hu, toAdd_one, map_zero]
  have h3 : (⟨w, hwN⟩ : ↥N0) = 0 := hinj0 h2
  have h4 : w = 0 := congrArg Subtype.val h3
  apply Subtype.ext
  rw [← hw, h4]
  exact elt_zero hV

theorem natural_of_relIndex_six
    {X : Type} [Group X] [Finite X] {T : Subgroup X} (hX : GNSetting X T)
    {L : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤) (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L)
    (eL : ↥L ≃* alternatingGroup (Fin 7))
    (h6 : (⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ ⊓
        Subgroup.centralizer ((L.comap (QuotientGroup.mk' (gnC T)) : Subgroup X) : Set X)).relIndex
      ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ = 2 ^ 6)
    (θ : ↥((Subgroup.normalizer (L : Set (X ⧸ gnC T))).comap (QuotientGroup.mk' (gnC T))) →*
      Equiv.Perm (Fin 7))
    (hθ : ∀ (g : ↥((Subgroup.normalizer (L : Set (X ⧸ gnC T))).comap
        (QuotientGroup.mk' (gnC T)))) (l l' : ↥L),
      (l' : X ⧸ gnC T) = QuotientGroup.mk' (gnC T) g * l * (QuotientGroup.mk' (gnC T) g)⁻¹ →
        (eL l' : Equiv.Perm (Fin 7)) = θ g * (eL l : Equiv.Perm (Fin 7)) * (θ g)⁻¹)
    (_hθL : ∀ (g : ↥((Subgroup.normalizer (L : Set (X ⧸ gnC T))).comap
        (QuotientGroup.mk' (gnC T)))) (l : ↥L),
      (l : X ⧸ gnC T) = QuotientGroup.mk' (gnC T) g → θ g = (eL l : Equiv.Perm (Fin 7))) :
    ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ ⊓
        Subgroup.centralizer ((L.comap (QuotientGroup.mk' (gnC T)) : Subgroup X) : Set X) = ⊥ ∧
      ∃ φ : ↥⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ →* Multiplicative (altHeart 7),
        Function.Bijective φ ∧
        ∀ (g : ↥((Subgroup.normalizer (L : Set (X ⧸ gnC T))).comap
          (QuotientGroup.mk' (gnC T)))) (u v : ↥⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆),
          (v : X) = g * u * g⁻¹ →
          Multiplicative.toAdd (φ v) = altAct (θ g) (Multiplicative.toAdd (φ u)) := by
  classical
  have hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow
  have hVab : IsElemAbelian 2 (gnV T) := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.isElemAbelian_gnV T hX
  have hperf : commutator ↥L = ⊤ := commutator_eq_top_of_equiv_alt7 eL
  obtain ⟨hHI, -⟩ := a7_clause_dim T hX.charTwo hQT L hL hJ eL
  have hGF := EightFive.gf2EightFive_of_b42L42Core EightFive.b42L42Core_holds
  have hdich := exists_naturalOn_or_four_ne hGF hX hL hJ eL
  have hVn : (gnV T).Normal := CFSG.AGLEmbeddingD2.GN.normal_gnV T
  generalize hK : L.comap (QuotientGroup.mk' (gnC T)) = K at hHI h6 hdich ⊢
  generalize hN : ⁅gnV T, K⁆ = N at hHI h6 ⊢
  generalize hZ : N ⊓ Subgroup.centralizer (K : Set X) = Z at hHI h6 ⊢
  have hKmem : ∀ k : X, k ∈ K ↔ QuotientGroup.mk' (gnC T) k ∈ L := fun k => by rw [← hK]; rfl
  have hVcomm : ∀ x ∈ gnV T, ∀ y ∈ gnV T, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hVab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hNV : N ≤ gnV T := hN ▸ Subgroup.commutator_le_left _ _
  have hKN : K ≤ Subgroup.normalizer (N : Set X) :=
    hN ▸ Subgroup.normalizer_commutator_ge_right _ _
  have hZN : Z ≤ N := hZ ▸ inf_le_left
  have hZcen : Z ≤ Subgroup.centralizer (K : Set X) := hZ ▸ inf_le_right
  have hZc : ∀ z ∈ Z, ∀ k ∈ K, k * z = z * k := fun z hz k hk =>
    Subgroup.mem_centralizer_iff.1 (hZcen hz) k hk
  have hZV : Z ≤ gnV T := hZN.trans hNV
  have hKZ : K ≤ Subgroup.normalizer (Z : Set X) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : k * x * k⁻¹ = x := by rw [hZc x hx k hk]; group
      rw [this]
      exact hx
    · intro hx
      have h1 := hZc _ hx k⁻¹ (K.inv_mem hk)
      have hxy : x = k * x * k⁻¹ := by
        calc x = k⁻¹ * (k * x * k⁻¹) * k := by group
          _ = (k * x * k⁻¹) * k⁻¹ * k := by rw [h1]
          _ = k * x * k⁻¹ := by group
      rw [hxy]
      exact hx
  have hlift : ∀ a : alternatingGroup (Fin 7), ∃ k : X, k ∈ K ∧
      (QuotientGroup.mk k : X ⧸ gnC T) = ((eL.symm a : ↥L) : X ⧸ gnC T) := by
    intro a
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective ((eL.symm a : ↥L) : X ⧸ gnC T)
    refine ⟨k, (hKmem k).2 ?_, hk⟩
    have : QuotientGroup.mk' (gnC T) k = ((eL.symm a : ↥L) : X ⧸ gnC T) := hk
    rw [this]
    exact (eL.symm a).2
  obtain ⟨-, hHI2⟩ := hHI
  rw [hN, hZ] at hHI2
  have hN1 : N ≤ ⁅N, K⁆ := by
    have := comm_le_comm_comm hVab hperf (le_refl (gnV T))
    rw [hK, hN] at this
    exact this
  have hNeq : ∀ W : Subgroup X, W ≤ gnV T → (∃ k ∈ K, ∃ w ∈ W, k * w * k⁻¹ ≠ w) →
      N = ⁅W, K⁆ := by
    intro W hWV hmove
    have hM1N : ⁅W, K⁆ ≤ N := hN ▸ Subgroup.commutator_mono hWV le_rfl
    have hKM1 : K ≤ Subgroup.normalizer ((⁅W, K⁆ : Subgroup X) : Set X) := Subgroup.normalizer_commutator_ge_right _ _
    have hM1comm : ⁅⁅W, K⁆, K⁆ ≤ ⁅W, K⁆ := Subgroup.le_normalizer_iff_commutator_le_left.1 hKM1
    have hM1Z : ¬ ⁅W, K⁆ ≤ Z := by
      intro hZ'
      have h1 : ⁅⁅W, K⁆, K⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact hZ'.trans hZcen
      have h2 : ⁅W, K⁆ ≤ ⁅⁅W, K⁆, K⁆ := by
        rw [← hK]
        exact comm_le_comm_comm hVab hperf hWV
      rw [h1] at h2
      obtain ⟨k, hk, w, hw, hne⟩ := hmove
      apply hne
      have h3 : ⁅w, k⁆ ∈ ⁅W, K⁆ := Subgroup.commutator_mem_commutator hw hk
      have h4 := h2 h3
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h4
      calc k * w * k⁻¹ = w * k * k⁻¹ := by rw [h4]
        _ = w := by group
    have hKsup : K ≤ Subgroup.normalizer ((⁅W, K⁆ ⊔ Z : Subgroup X) : Set X) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      rw [Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.1 (hKM1 hk),
        Subgroup.mem_normalizer_iff_map_conj_eq.1 (hKZ hk)]
    have hsup : ⁅W, K⁆ ⊔ Z = N := by
      rcases hHI2 (⁅W, K⁆ ⊔ Z) le_sup_right (sup_le hM1N hZN) hKsup with h | h
      · exact absurd (h ▸ le_sup_left) hM1Z
      · exact h
    have hcomm' : ∀ a ∈ ⁅W, K⁆, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
      hVcomm a ((hM1N.trans hNV) ha) b (hZV hb)
    have hNK : ⁅N, K⁆ ≤ ⁅W, K⁆ := by
      rw [← hsup, Subgroup.commutator_le]
      intro x hx k hk
      obtain ⟨m, hm, z, hz, rfl⟩ := mem_sup_of_commute hcomm' hx
      have hzk := hZc z hz k hk
      have e : ⁅m * z, k⁆ = ⁅m, k⁆ := by
        have h5 : z * k * z⁻¹ = k := by rw [← hzk]; group
        simp only [commutatorElement_def]
        calc m * z * k * (m * z)⁻¹ * k⁻¹ = m * (z * k * z⁻¹) * m⁻¹ * k⁻¹ := by group
          _ = m * k * m⁻¹ * k⁻¹ := by rw [h5]
      rw [e]
      exact hM1comm (Subgroup.commutator_mem_commutator hm hk)
    exact le_antisymm (hN1.trans hNK) (hM1N)
  rcases hdich with ⟨g0, W, π, hg0, hWV, hZW, hmove, hWK, hπk, hπi⟩ |
    ⟨W, U, hWV, hZW, hmove, hWK, hWU, hUV, hUK, hcard⟩
  swap
  · exfalso
    have hNW := hNeq W hWV hmove
    have hNU : N ≤ U := hNW ▸ hWU
    have h1 := Subgroup.card_le_of_le hNU
    have h2 : Z.relIndex N * Nat.card (Z ⊓ N : Subgroup X) = Nat.card N :=
      Subgroup.relIndex_mul_card Z N
    rw [h6] at h2
    have h3 : 0 < Nat.card (Z ⊓ N : Subgroup X) := Nat.card_pos
    have h4 : 2 ^ 6 ≤ Nat.card N := by
      rw [← h2]
      exact Nat.le_mul_of_pos_right _ h3
    rw [hcard] at h1
    omega
  have hNW : N = ⁅W, K⁆ := hNeq W hWV hmove
  have hπi' : ∀ (l : X) (hl : QuotientGroup.mk' (gnC T) l ∈ L) (u u' : ↥⁅W, K⁆),
      (u' : X) = l * u * l⁻¹ → Multiplicative.toAdd (π u') =
        altAct (g0 ⟨QuotientGroup.mk' (gnC T) l, hl⟩ : Equiv.Perm (Fin 7))
          (Multiplicative.toAdd (π u)) := by
    intro l hl u u' hu'
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (π u))
    have := hπi l hl u u' hu' x hx.symm
    rw [this, ← hx]
    rfl
  obtain ⟨c, hc⟩ := exists_conj_of_surjective eL g0 hg0
  let π' : ↥N →* Multiplicative (altHeart 7) := π.comp (Subgroup.inclusion hNW.le)
  let π1 : ↥N →* Multiplicative (altHeart 7) :=
    (AddMonoidHom.toMultiplicative (altAct c⁻¹)).comp π'
  have hπ1 : ∀ u, Multiplicative.toAdd (π1 u) = altAct c⁻¹ (Multiplicative.toAdd (π' u)) :=
    fun u => rfl
  have hKcl : ∀ (l : X) (hl : QuotientGroup.mk' (gnC T) l ∈ L) (u v : ↥N), (v : X) = l * u * l⁻¹ →
      Multiplicative.toAdd (π' v) =
        altAct (g0 ⟨QuotientGroup.mk' (gnC T) l, hl⟩ : Equiv.Perm (Fin 7))
          (Multiplicative.toAdd (π' u)) := fun l hl u v hv =>
    hπi' l hl (Subgroup.inclusion hNW.le u) (Subgroup.inclusion hNW.le v) hv
  have hπ1e : ∀ (l : X) (hl : QuotientGroup.mk' (gnC T) l ∈ L) (u v : ↥N), (v : X) = l * u * l⁻¹ →
      Multiplicative.toAdd (π1 v) =
        altAct (eL ⟨QuotientGroup.mk' (gnC T) l, hl⟩ : Equiv.Perm (Fin 7))
          (Multiplicative.toAdd (π1 u)) := by
    intro l hl u v hv
    have h1 := hKcl l hl u v hv
    have h2 : c⁻¹ * (g0 ⟨QuotientGroup.mk' (gnC T) l, hl⟩ : Equiv.Perm (Fin 7)) =
        (eL ⟨QuotientGroup.mk' (gnC T) l, hl⟩ : Equiv.Perm (Fin 7)) * c⁻¹ := by
      rw [hc ⟨QuotientGroup.mk' (gnC T) l, hl⟩]
      group
    rw [hπ1, hπ1, h1, ← altAct_mul, h2, altAct_mul]
  have hπ1k : ∀ u : ↥N, π1 u = 1 → ∀ k ∈ K, k * u * k⁻¹ = u := by
    intro u hu k hk
    have h0 : altAct c⁻¹ (Multiplicative.toAdd (π' u)) = 0 := by
      rw [← hπ1, hu]
      rfl
    have h1 : Multiplicative.toAdd (π' u) = 0 := by
      have := congrArg (altAct c) h0
      rwa [altAct_apply_inv, map_zero] at this
    have h2 : π (Subgroup.inclusion hNW.le u) = 1 := Multiplicative.toAdd.injective h1
    exact hπk _ h2 k hk
  have hZker : ∀ u : ↥N, (u : X) ∈ Z → π1 u = 1 := by
    intro u hu
    have hfix : ∀ σ ∈ alternatingGroup (Fin 7),
        altAct σ (Multiplicative.toAdd (π1 u)) = Multiplicative.toAdd (π1 u) := by
      intro σ hσ
      obtain ⟨k, hkK, hk⟩ := hlift ⟨σ, hσ⟩
      have hkL := (hKmem k).1 hkK
      have h1 := hπ1e k hkL u u (by
        have := hZc u hu k hkK
        rw [this]
        group)
      have h2 : (⟨QuotientGroup.mk' (gnC T) k, hkL⟩ : ↥L) = eL.symm ⟨σ, hσ⟩ := Subtype.ext hk
      rw [h2, MulEquiv.apply_symm_apply] at h1
      exact h1.symm
    have h0 := altHeart_seven_fixed _ hfix
    exact Multiplicative.toAdd.injective h0
  have hπ1s : Function.Surjective π1 := by
    let U : AddSubgroup (altHeart 7) :=
      { carrier := {a | ∃ u : ↥N, Multiplicative.toAdd (π1 u) = a}
        zero_mem' := ⟨1, by rw [map_one, toAdd_one]⟩
        add_mem' := by
          rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
          exact ⟨u * v, by rw [map_mul, toAdd_mul]⟩
        neg_mem' := by
          rintro _ ⟨u, rfl⟩
          exact ⟨u⁻¹, by rw [map_inv, toAdd_inv]⟩ }
    have hU : ∀ σ ∈ alternatingGroup (Fin 7), ∀ x : evenWeight 7,
        (QuotientAddGroup.mk x : altHeart 7) ∈ U →
          (QuotientAddGroup.mk (evenWeightPerm σ x) : altHeart 7) ∈ U := by
      intro σ hσ x hx
      obtain ⟨u, hu⟩ := hx
      obtain ⟨k, hkK, hk⟩ := hlift ⟨σ, hσ⟩
      have hkL := (hKmem k).1 hkK
      have hv : k * (u : X) * k⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.1 (hKN hkK) _).1 u.2
      refine ⟨⟨k * u * k⁻¹, hv⟩, ?_⟩
      have h1 := hπ1e k hkL u ⟨k * u * k⁻¹, hv⟩ rfl
      have h2 : (⟨QuotientGroup.mk' (gnC T) k, hkL⟩ : ↥L) = eL.symm ⟨σ, hσ⟩ := Subtype.ext hk
      rw [h2, MulEquiv.apply_symm_apply] at h1
      rw [h1, hu]
      rfl
    rcases altHeart_irreducible (by norm_num) U hU with hb | ht
    · exfalso
      have hNZ : N ≤ Z := by
        intro u hu
        have h1 : Multiplicative.toAdd (π1 ⟨u, hu⟩) ∈ U := ⟨⟨u, hu⟩, rfl⟩
        rw [hb, AddSubgroup.mem_bot] at h1
        have h2 : π1 ⟨u, hu⟩ = 1 := Multiplicative.toAdd.injective h1
        have h3 := hπ1k ⟨u, hu⟩ h2
        rw [← hZ]
        refine ⟨hu, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
        have := h3 k hk
        calc k * u = k * u * k⁻¹ * k := by group
          _ = u * k := by rw [this]
      have h1 : ⁅N, K⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact hNZ.trans hZcen
      have h2 : N ≤ ⊥ := h1 ▸ hN1
      obtain ⟨k, hk, w, hw, hne⟩ := hmove
      apply hne
      have h3 : ⁅w, k⁆ ∈ N := by
        rw [hNW]
        exact Subgroup.commutator_mem_commutator hw hk
      have h4 : ⁅w, k⁆ = 1 := Subgroup.mem_bot.1 (h2 h3)
      rw [commutatorElement_eq_one_iff_mul_comm] at h4
      calc k * w * k⁻¹ = w * k * k⁻¹ := by rw [h4]
        _ = w := by group
    · intro a
      have : Multiplicative.toAdd a ∈ U := by rw [ht]; exact AddSubgroup.mem_top _
      obtain ⟨u, hu⟩ := this
      exact ⟨u, Multiplicative.toAdd.injective hu⟩
  have hπ1inj : Function.Injective π1 :=
    inj_of_section hVab eL hperf hK.symm hN.symm π1 hπ1s hπ1e hπ1k
  have hZbot : Z = ⊥ := by
    refine le_bot_iff.1 fun z hz => ?_
    have hzN : z ∈ N := hZN hz
    have h1 : π1 ⟨z, hzN⟩ = 1 := hZker ⟨z, hzN⟩ hz
    have h2 : (⟨z, hzN⟩ : ↥N) = 1 := hπ1inj (h1.trans (map_one π1).symm)
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h2)
  refine ⟨hZbot, π1, ⟨hπ1inj, hπ1s⟩, ?_⟩
  intro g u v hv
  have hgn : QuotientGroup.mk' (gnC T) (g : X) ∈ Subgroup.normalizer (L : Set (X ⧸ gnC T)) := g.2
  have hgK : ∀ x : X, x ∈ K ↔ (g : X) * x * (g : X)⁻¹ ∈ K := fun x => by
    rw [hKmem, hKmem, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.1 hgn _
  have hgKnorm : (g : X) ∈ Subgroup.normalizer (K : Set X) := Subgroup.mem_normalizer_iff.2 hgK
  have hgVnorm : (g : X) ∈ Subgroup.normalizer ((gnV T : Subgroup X) : Set X) :=
    Subgroup.le_normalizer_of_normal (Subgroup.mem_top _)
  have hgnorm : (g : X) ∈ Subgroup.normalizer (N : Set X) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← hN, Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.1 hgVnorm,
      Subgroup.mem_normalizer_iff_map_conj_eq.1 hgKnorm]
  have hgN : ∀ x : X, x ∈ N ↔ (g : X) * x * (g : X)⁻¹ ∈ N := fun x =>
    Subgroup.mem_normalizer_iff.1 hgnorm x
  let cg : ↥N →* ↥N :=
    { toFun := fun u => ⟨(g : X) * u * (g : X)⁻¹, (hgN u).1 u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        group) }
  have hcgi : Function.Injective cg := by
    intro a b h
    have h1 : (g : X) * a * (g : X)⁻¹ = (g : X) * b * (g : X)⁻¹ := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  let φ' : ↥N →* Multiplicative (altHeart 7) :=
    (AddMonoidHom.toMultiplicative (altAct (θ g)⁻¹)).comp (π1.comp cg)
  have hφ'a : ∀ x, Multiplicative.toAdd (φ' x) =
      altAct (θ g)⁻¹ (Multiplicative.toAdd (π1 (cg x))) := fun x => rfl
  have hφ'i : Function.Injective φ' := by
    intro a b h
    have h1 : altAct (θ g)⁻¹ (Multiplicative.toAdd (π1 (cg a))) =
        altAct (θ g)⁻¹ (Multiplicative.toAdd (π1 (cg b))) := by
      rw [← hφ'a, ← hφ'a, h]
    have h2 := congrArg (altAct (θ g)) h1
    rw [altAct_apply_inv, altAct_apply_inv] at h2
    exact hcgi (hπ1inj (Multiplicative.toAdd.injective h2))
  let r : ↥K → ↥N → ↥N := fun k u => ⟨(k : X) * u * (k : X)⁻¹,
    (Subgroup.mem_normalizer_iff.1 (hKN k.2) _).1 u.2⟩
  let α : ↥K → Equiv.Perm (Fin 7) := fun k =>
    (eL ⟨QuotientGroup.mk' (gnC T) (k : X), (hKmem k).1 k.2⟩ : Equiv.Perm (Fin 7))
  have hα : ∀ σ ∈ alternatingGroup (Fin 7), ∃ k, α k = σ := by
    intro σ hσ
    obtain ⟨k, hkK, hk⟩ := hlift ⟨σ, hσ⟩
    refine ⟨⟨k, hkK⟩, ?_⟩
    have h2 : (⟨QuotientGroup.mk' (gnC T) k, (hKmem k).1 hkK⟩ : ↥L) = eL.symm ⟨σ, hσ⟩ :=
      Subtype.ext hk
    show (eL ⟨QuotientGroup.mk' (gnC T) k, (hKmem k).1 hkK⟩ : Equiv.Perm (Fin 7)) = σ
    rw [h2, MulEquiv.apply_symm_apply]
  have e1 : ∀ k u, Multiplicative.toAdd (π1 (r k u)) =
      altAct (α k) (Multiplicative.toAdd (π1 u)) := fun k u =>
    hπ1e (k : X) ((hKmem k).1 k.2) u (r k u) rfl
  have e2 : ∀ k u, Multiplicative.toAdd (φ' (r k u)) =
      altAct (α k) (Multiplicative.toAdd (φ' u)) := by
    intro k u
    have hk' : (g : X) * (k : X) * (g : X)⁻¹ ∈ K := (hgK k).1 k.2
    have hkL : QuotientGroup.mk' (gnC T) (k : X) ∈ L := (hKmem k).1 k.2
    have hl'L : QuotientGroup.mk' (gnC T) ((g : X) * (k : X) * (g : X)⁻¹) ∈ L := (hKmem _).1 hk'
    have h1 := hπ1e ((g : X) * (k : X) * (g : X)⁻¹) hl'L (cg u) (cg (r k u)) (by
      show (g : X) * ((k : X) * u * (k : X)⁻¹) * (g : X)⁻¹ =
        (g : X) * (k : X) * (g : X)⁻¹ * ((g : X) * u * (g : X)⁻¹) * ((g : X) * (k : X) * (g : X)⁻¹)⁻¹
      group)
    have h2 := hθ g ⟨QuotientGroup.mk' (gnC T) (k : X), hkL⟩
      ⟨QuotientGroup.mk' (gnC T) ((g : X) * (k : X) * (g : X)⁻¹), hl'L⟩
      (by simp only [map_mul, map_inv])
    have h3 : (θ g)⁻¹ * ((θ g) * α k * (θ g)⁻¹) = α k * (θ g)⁻¹ := by group
    rw [hφ'a, hφ'a, h1]
    show altAct (θ g)⁻¹ (altAct (eL ⟨QuotientGroup.mk' (gnC T) ((g : X) * (k : X) * (g : X)⁻¹),
      hl'L⟩ : Equiv.Perm (Fin 7)) (Multiplicative.toAdd (π1 (cg u)))) =
      altAct (α k) (altAct (θ g)⁻¹ (Multiplicative.toAdd (π1 (cg u))))
    rw [h2, ← altAct_mul, h3, altAct_mul]
  have hφeq : φ' = π1 := eq_of_equivariant r α hα π1 φ' ⟨hπ1inj, hπ1s⟩ hφ'i e1 e2
  have h1 : v = cg u := Subtype.ext hv
  have h2 : Multiplicative.toAdd (φ' u) = Multiplicative.toAdd (π1 u) :=
    congrArg (fun f : ↥N →* Multiplicative (altHeart 7) => Multiplicative.toAdd (f u)) hφeq
  rw [h1]
  calc Multiplicative.toAdd (π1 (cg u))
      = altAct (θ g) (altAct (θ g)⁻¹ (Multiplicative.toAdd (π1 (cg u)))) :=
        (altAct_apply_inv _ _).symm
    _ = altAct (θ g) (Multiplicative.toAdd (π1 u)) := by rw [← hφ'a, h2]

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
