module

public import CFSG.ClassicalInvolution.Asc77.WP3LayerPair

public section

namespace CFSG.ClassicalInvolution.Asc77.ExactLayer

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Sets

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem tqMembers_conj (hΩ : ConjInvariant Ω) (g c : G) :
    tqMembers Ω (g * c * g⁻¹) = conjSub g '' tqMembers Ω c := by
  ext K'
  constructor
  · intro hK'
    refine ⟨conjSub g⁻¹ K', ⟨hΩ g⁻¹ K' hK'.1, ?_⟩, conjSub_conjSub_inv g K'⟩
    have h := trivialOnQuot_conjSub hK'.2 g⁻¹
    have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
    rwa [e] at h
  · rintro ⟨K, hK, rfl⟩
    exact ⟨hΩ g K hK.1, trivialOnQuot_conjSub hK.2 g⟩

theorem exactFamily_conj (hΩ : ConjInvariant Ω) (g c : G) :
    exactFamily Ω (g * c * g⁻¹) = conjSub g '' exactFamily Ω c := by
  ext K'
  constructor
  · rintro ⟨K, hK, rfl⟩
    rw [tqMembers_conj hΩ] at hK
    obtain ⟨K₀, hK₀, rfl⟩ := hK
    exact ⟨exactCore c K₀, ⟨K₀, hK₀, rfl⟩, (exactCore_conjSub g c K₀).symm⟩
  · rintro ⟨_, ⟨K, hK, rfl⟩, rfl⟩
    refine ⟨conjSub g K, ?_, (exactCore_conjSub g c K).symm⟩
    rw [tqMembers_conj hΩ]
    exact ⟨K, hK, rfl⟩

theorem exactLayer_conj (hΩ : ConjInvariant Ω) (g c : G) :
    exactLayer Ω (g * c * g⁻¹) = conjSub g (exactLayer Ω c) := by
  rw [exactLayer_eq_iSup, exactLayer_eq_iSup, exactFamily_conj hΩ, iSup_image]
  unfold conjSub
  rw [Subgroup.map_iSup]
  refine iSup_congr fun K' => ?_
  rw [Subgroup.map_iSup]

end Sets

section OddQuotient

variable {G : Type} [Group G]

@[expose] noncomputable def centralizerConj (g c : G) :
    ↥(Subgroup.centralizer ({c} : Set G)) ≃* ↥(Subgroup.centralizer ({g * c * g⁻¹} : Set G)) :=
  (Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
    (MulEquiv.subgroupCongr (conjSub_centralizer_singleton g c))

theorem coe_centralizerConj (g c : G) (x : ↥(Subgroup.centralizer ({c} : Set G))) :
    ((centralizerConj g c x : ↥(Subgroup.centralizer ({g * c * g⁻¹} : Set G))) : G) =
      g * (x : G) * g⁻¹ := rfl

@[expose] noncomputable def oddQuotConj (g c : G) : OddQuot c ≃* OddQuot (g * c * g⁻¹) :=
  QuotientGroup.congr (componentClassificationOddCore _) (componentClassificationOddCore _)
    (centralizerConj g c) (OddCore.equiv_invariant (centralizerConj g c))

theorem oddQuotConj_oddQuotMk (g c : G) (x : ↥(Subgroup.centralizer ({c} : Set G))) :
    oddQuotConj g c (oddQuotMk c x) = oddQuotMk (g * c * g⁻¹) (centralizerConj g c x) := rfl

theorem map_centralizerConj_subgroupOf (g c : G) (K : Subgroup G) :
    (K.subgroupOf (Subgroup.centralizer ({c} : Set G))).map (centralizerConj g c).toMonoidHom =
      (conjSub g K).subgroupOf (Subgroup.centralizer ({g * c * g⁻¹} : Set G)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact conj_mem_conjSub hx
  · intro hy
    have hyC : (y : G) ∈ conjSub g (Subgroup.centralizer ({c} : Set G)) := by
      rw [conjSub_centralizer_singleton]
      exact y.2
    have hxC : g⁻¹ * (y : G) * g ∈ Subgroup.centralizer ({c} : Set G) := mem_conjSub_iff.mp hyC
    refine ⟨⟨g⁻¹ * (y : G) * g, hxC⟩, mem_conjSub_iff.mp hy, Subtype.ext ?_⟩
    show g * (g⁻¹ * (y : G) * g) * g⁻¹ = y
    group

theorem map_oddQuotConj_modOdd (g c : G) (K : Subgroup G) :
    (modOdd c K).map (oddQuotConj g c).toMonoidHom = modOdd (g * c * g⁻¹) (conjSub g K) := by
  unfold modOdd
  rw [Subgroup.map_map]
  have hcomm : (oddQuotConj g c).toMonoidHom.comp (oddQuotMk c) =
      (oddQuotMk (g * c * g⁻¹)).comp (centralizerConj g c).toMonoidHom := rfl
  rw [hcomm, ← Subgroup.map_map, map_centralizerConj_subgroupOf]

end OddQuotient

section ImagesConj

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exactImages_conj (hΩ : ConjInvariant Ω) (g c : G) :
    exactImages Ω (g * c * g⁻¹) =
      Subgroup.map (oddQuotConj g c).toMonoidHom '' exactImages Ω c := by
  unfold exactImages memberImages
  rw [centMembers_exactFamily, centMembers_exactFamily, exactFamily_conj hΩ, Set.image_image,
    Set.image_image]
  refine Set.image_congr fun K _ => ?_
  exact (map_oddQuotConj_modOdd g c K).symm

theorem exactJoin_conj (hΩ : ConjInvariant Ω) (g c : G) :
    exactJoin Ω (g * c * g⁻¹) = (exactJoin Ω c).map (oddQuotConj g c).toMonoidHom := by
  unfold exactJoin memberJoin
  rw [centMembers_exactFamily, centMembers_exactFamily, exactFamily_conj hΩ, iSup_image,
    Subgroup.map_iSup]
  refine iSup_congr fun K => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun _ => (map_oddQuotConj_modOdd g c K).symm

end ImagesConj

section LieTransport

variable {p f : ℕ} [Fact p.Prime]

theorem restrictFamily_conj {G : Type} [Group G] (Φ : Set (Subgroup G)) {Y Y' : Subgroup G}
    (g : G) (hY : conjSub g Y = Y') :
    ∃ e : ↥Y ≃* ↥Y', (∀ x : ↥Y, ((e x : ↥Y') : G) = g * (x : G) * g⁻¹) ∧
      restrictFamily (conjSub g '' Φ) Y' = Subgroup.map e.toMonoidHom '' restrictFamily Φ Y := by
  subst hY
  have hmap : ∀ L : Subgroup G, (L.subgroupOf Y).map
      (Subgroup.equivMapOfInjective Y (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toMonoidHom = (conjSub g L).subgroupOf (conjSub g Y) := by
    intro L
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact conj_mem_conjSub hx
    · intro hy
      obtain ⟨x, hxY, hx⟩ := y.2
      refine ⟨⟨x, hxY⟩, ?_, Subtype.ext hx⟩
      have h1 : g⁻¹ * (y : G) * g ∈ L := mem_conjSub_iff.mp hy
      have h2 : g⁻¹ * (y : G) * g = x := by
        rw [← hx]
        show g⁻¹ * (g * x * g⁻¹) * g = x
        group
      show x ∈ L
      rwa [h2] at h1
  refine ⟨Subgroup.equivMapOfInjective Y (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
    fun x => rfl, ?_⟩
  ext L'
  constructor
  · rintro ⟨_, ⟨L, hL, rfl⟩, hLY, rfl⟩
    have hLY' : L ≤ Y := by
      have h := conjSub_mono (n := g⁻¹) hLY
      rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at h
    exact ⟨L.subgroupOf Y, ⟨L, hL, hLY', rfl⟩, hmap L⟩
  · rintro ⟨_, ⟨L, hL, hLY, rfl⟩, rfl⟩
    exact ⟨conjSub g L, ⟨L, hL, rfl⟩, conjSub_mono hLY, hmap L⟩

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exactPair_conj (hΩ : ConjInvariant Ω) (g c : G) :
    ∃ e : ↥(exactLayer Ω c) ≃* ↥(exactLayer Ω (g * c * g⁻¹)),
      (∀ x : ↥(exactLayer Ω c), ((e x : ↥(exactLayer Ω (g * c * g⁻¹))) : G) = g * (x : G) * g⁻¹) ∧
      exactPair Ω (g * c * g⁻¹) = Subgroup.map e.toMonoidHom '' exactPair Ω c := by
  obtain ⟨e, he, hfam⟩ := restrictFamily_conj (exactFamily Ω c) g (exactLayer_conj hΩ g c).symm
  refine ⟨e, he, ?_⟩
  show restrictFamily (exactFamily Ω (g * c * g⁻¹)) (exactLayer Ω (g * c * g⁻¹)) = _
  rw [exactFamily_conj hΩ]
  exact hfam

theorem lieSystemMod_exactFamily_conj (hΩ : ConjInvariant Ω) (g c : G)
    (h : LieSystemMod p f (exactPair Ω c)) : LieSystemMod p f (exactPair Ω (g * c * g⁻¹)) := by
  obtain ⟨e, -, he⟩ := exactPair_conj hΩ g c
  rw [he]
  exact LieSystemMod.congr e h

end LieTransport

section DecompositionTransport

theorem isOddLieComponent_map {X X' : Type} [Group X] [Group X'] (e : X ≃* X') {L : Subgroup X}
    (h : IsOddLieComponent L) : IsOddLieComponent (L.map e.toMonoidHom) := by
  obtain ⟨t, n, p, f, hp, hn, ht, hmodel⟩ := h
  refine ⟨t, n, p, f, hp, hn, ht, ?_⟩
  let eL : ↥L ≃* ↥(L.map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective L e.toMonoidHom e.injective
  have hc : (Subgroup.center ↥L).map eL.toMonoidHom = Subgroup.center ↥(L.map e.toMonoidHom) :=
    Subgroup.map_center_eq eL
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.congr _ _ eL hc) hmodel

noncomputable def lieDecompositionMap {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    {Ψ : Set (Subgroup X)} {Y : Subgroup X} (D : LieDecomposition Ψ Y) :
    LieDecomposition (Subgroup.map e.toMonoidHom '' Ψ) (Y.map e.toMonoidHom) where
  ι := D.ι
  Q i := (D.Q i).map e.toMonoidHom
  quasisimple i := isQuasisimple_map_of_ker_le_center e.toMonoidHom
    (by rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]; exact bot_le)
    (D.quasisimple i)
  commute i j hij := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    rw [D.commute i j hij a ha b hb]
  iSup_eq := by rw [← Subgroup.map_iSup, D.iSup_eq]
  exists_le := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨i, hi⟩ := D.exists_le L hL
    exact ⟨i, Subgroup.map_mono hi⟩
  rankOne_or_lie i := by
    rcases D.rankOne_or_lie i with ⟨⟨L, hL, hLQ⟩, hmin⟩ | hlie
    · left
      refine ⟨⟨L.map e.toMonoidHom, ⟨L, hL, rfl⟩, by rw [hLQ]⟩, ?_⟩
      rintro _ ⟨L₁, hL₁, rfl⟩ hle
      have h1 : L₁ ≤ D.Q i := (Subgroup.map_le_map_iff_of_injective e.injective).mp hle
      rw [hmin L₁ hL₁ h1]
    · right
      exact isOddLieComponent_map e hlie

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem lieDecomposition_exactFamily_conj (hΩ : ConjInvariant Ω) (g c : G)
    (h : Nonempty (LieDecomposition (exactImages Ω c) (exactJoin Ω c))) :
    Nonempty (LieDecomposition (exactImages Ω (g * c * g⁻¹)) (exactJoin Ω (g * c * g⁻¹))) := by
  obtain ⟨D⟩ := h
  rw [exactImages_conj hΩ, exactJoin_conj hΩ]
  exact ⟨lieDecompositionMap (oddQuotConj g c) D⟩

end DecompositionTransport

end CFSG.ClassicalInvolution.Asc77.ExactLayer
