module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarDerived
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarInvol
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarHCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

@[expose] def embE {G : Type} [Group G] (t : G) (E : Subgroup ↥(centralizer ({t} : Set G))) :
    ↥E →* G :=
  (centralizer ({t} : Set G)).subtype.comp E.subtype

theorem embE_injective {G : Type} [Group G] (t : G) (E : Subgroup ↥(centralizer ({t} : Set G))) :
    Function.Injective (embE t E) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem index_eq_two_of_not_mem {H : Type} [Group H] {E : Subgroup H} (hdvd : E.index ∣ 2)
    {s : H} (hs : s ∉ E) : E.index = 2 := by
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact absurd (Subgroup.index_eq_one.1 h ▸ mem_top s) hs
  · exact h

section Sylow

theorem inf_eq_map_T0 {H : Type} [Group H] [Finite H] {E : Subgroup H} (M : CoverModel ↥E)
    (hcard : Nat.card ↥E = 88704000) {S : Subgroup H} (hS : IsPGroup 2 S)
    (hT : M.T0.map E.subtype ≤ S) : S ⊓ E = M.T0.map E.subtype := by
  have hQ : IsPGroup 2 (S.comap E.subtype) := hS.comap_subtype
  have hle : M.T0 ≤ S.comap E.subtype := fun x hx => hT (Subgroup.mem_map_of_mem E.subtype hx)
  have heq := M.eq_of_le_isPGroup hcard hQ hle
  apply le_antisymm
  · intro y hy
    obtain ⟨hyS, hyE⟩ := Subgroup.mem_inf.1 hy
    have : (⟨y, hyE⟩ : ↥E) ∈ S.comap E.subtype := hyS
    rw [heq] at this
    exact ⟨⟨y, hyE⟩, this, rfl⟩
  · exact le_inf hT (Subgroup.map_subtype_le _)

end Sylow

section Data

variable
  {G : Type} [Group G]

theorem embE_tE {t : G} (ht2 : orderOf t = 2) {E : Subgroup ↥(centralizer ({t} : Set G))}
    (hE : IsHSCover ↥(centralizer ({t} : Set G)) E) (M : CoverMaps ↥E) :
    embE t E M.tE = t := by
  have ht1 : t ≠ 1 := fun h => by
    rw [h, orderOf_one] at ht2
    exact absurd ht2 (by decide)
  have hcomm : ∀ y : ↥(centralizer ({t} : Set G)),
      y * (⟨t, mem_centralizer_singleton_iff.2 rfl⟩ : ↥(centralizer ({t} : Set G))) =
        ⟨t, mem_centralizer_singleton_iff.2 rfl⟩ * y := fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.1 y.2)
  have htE : (⟨t, mem_centralizer_singleton_iff.2 rfl⟩ : ↥(centralizer ({t} : Set G))) ∈ E :=
    hE.centralizer_le (mem_centralizer_iff.2 fun y _ => hcomm y)
  have hcen : (⟨⟨t, mem_centralizer_singleton_iff.2 rfl⟩, htE⟩ : ↥E) ∈ center ↥E :=
    Subgroup.mem_center_iff.2 fun z => Subtype.ext (hcomm z)
  rcases (M.mem_center_iff hE.card_center).1 hcen with h | h
  · exact absurd (congrArg (fun x : ↥E => (((x : ↥(centralizer ({t} : Set G))) : G))) h) ht1
  · exact congrArg (fun x : ↥E => (((x : ↥(centralizer ({t} : Set G))) : G))) h.symm

theorem harCoreData_of_cover {t : G} (ht2 : orderOf t = 2)
    {E : Subgroup ↥(centralizer ({t} : Set G))}
    (hE : IsHSCover ↥(centralizer ({t} : Set G)) E) (M : CoverModel ↥E)
    (hcent : ∀ h : ↥(centralizer ({t} : Set G)),
      (∀ y ∈ M.T0.map E.subtype, h * y = y * h) → h ∈ E)
    {S : Subgroup ↥(centralizer ({t} : Set G))} (hSE : S ⊓ E = M.T0.map E.subtype)
    (hder : ⁅S, S⁆ = M.T0'.map E.subtype) :
    HarCoreData t (embE t E M.z1E) (S.map (centralizer ({t} : Set G)).subtype)
      (E.map (centralizer ({t} : Set G)).subtype) (M.T0.map (embE t E))
      (M.T0'.map (embE t E)) (M.W0.map (embE t E)) := by
  have hι := embE_injective t E
  have hιt := embE_tE ht2 hE M.toCoverMaps
  have ht1 : t ≠ 1 := fun h => by
    rw [h, orderOf_one] at ht2
    exact absurd ht2 (by decide)
  have hmap : ∀ X : Subgroup ↥E, X.map (embE t E) =
      (X.map E.subtype).map (centralizer ({t} : Set G)).subtype := fun X => by
    rw [Subgroup.map_map]
    rfl
  refine
    { t_sq := ?_, t_ne_one := ht1, z1_ne_one := ?_, z1_ne_t := ?_, t_mem := ?_, z1_mem := ?_,
      S_comm_t := ?_, T0_eq := ?_, Eg_norm := ?_, z1_comm := ?_, cent_le := ?_, centre := ?_,
      derived := ?_, W0_eq := ?_, card_T0_t := ?_, card_T0_z2 := ?_, card_T0'_t := ?_,
      card_T0'_z1 := ?_, card_T0'_z2 := ?_, card_W0_t := ?_, card_W0_z2 := ?_ }
  · have := pow_orderOf_eq_one t
    rwa [ht2] at this
  · exact fun h => M.z1E_ne_one (hι (by rw [h, map_one]))
  · exact fun h => M.z1E_ne_tE (hι (h.trans hιt.symm))
  · have h := Subgroup.mem_map_of_mem (embE t E) M.tE_mem_T0
    rwa [hιt] at h
  · exact Subgroup.mem_map_of_mem _ M.z1E_mem_T0
  · rintro _ ⟨s, -, rfl⟩
    exact mem_centralizer_singleton_iff.1 s.2
  · rw [hmap, ← hSE, Subgroup.map_inf _ _ _ (centralizer ({t} : Set G)).subtype_injective]
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨e, he, rfl⟩
    exact ⟨s * e * s⁻¹, Subgroup.Normal.conj_mem hE.normal e he s, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, M.z1E_comm y hy]
  · intro x hx hxy
    have hxH : x ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hx
    have h := hcent ⟨x, hxH⟩ (by
      rintro _ ⟨y, hy, rfl⟩
      exact Subtype.ext (hxy (embE t E y) (Subgroup.mem_map_of_mem _ hy)))
    exact ⟨⟨x, hxH⟩, h, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ hc
    have hc' : ∀ y ∈ M.T0, x * y = y * x := fun y hy => hι (by
      rw [map_mul, map_mul]
      exact hc (embE t E y) (Subgroup.mem_map_of_mem _ hy))
    rcases M.centre_T0 hx hc' with h | h | h | h
    · exact Or.inl (by rw [h, map_one])
    · exact Or.inr (Or.inl (by rw [h, hιt]))
    · exact Or.inr (Or.inr (Or.inl (by rw [h])))
    · exact Or.inr (Or.inr (Or.inr (by rw [h, map_mul, hιt])))
  · rw [hmap, ← hder, Subgroup.map_commutator]
  · rw [CoverMaps.W0, MonoidHom.map_closure, Set.image_union, ← Subgroup.coe_map]
    congr 1
    apply congrArg (fun A => (M.T0'.map (embE t E) : Set G) ∪ A)
    ext z
    constructor
    · rintro ⟨y, ⟨hyT, hy2⟩, rfl⟩
      exact ⟨Subgroup.mem_map_of_mem _ hyT, by rw [← map_pow, hy2, map_one]⟩
    · rintro ⟨⟨y, hyT, rfl⟩, hz2⟩
      exact ⟨y, ⟨hyT, hι (by rw [map_pow, hz2, map_one])⟩, rfl⟩
  · show Nat.card {y : M.T0.map (embE t E) // (y : G) ^ 2 = t} = 80
    have h := card_sq_map (embE t E) hι M.T0 M.tE
    rw [hιt] at h
    rw [← h]
    exact M.card_sq_T0_tE
  · show Nat.card {y : M.T0.map (embE t E) // (y : G) ^ 2 = t * embE t E M.z1E} = 48
    rw [show t * embE t E M.z1E = embE t E (M.tE * M.z1E) by rw [map_mul, hιt],
      ← card_sq_map (embE t E) hι]
    exact M.card_sq_T0_z2E
  · show Nat.card {y : M.T0'.map (embE t E) // (y : G) ^ 2 = t} = 16
    have h := card_sq_map (embE t E) hι M.T0' M.tE
    rw [hιt] at h
    rw [← h]
    exact M.card_sq_T0'_tE
  · show Nat.card {y : M.T0'.map (embE t E) // (y : G) ^ 2 = embE t E M.z1E} = 32
    rw [← card_sq_map (embE t E) hι]
    exact M.card_sq_T0'_z1E
  · show Nat.card {y : M.T0'.map (embE t E) // (y : G) ^ 2 = t * embE t E M.z1E} = 16
    rw [show t * embE t E M.z1E = embE t E (M.tE * M.z1E) by rw [map_mul, hιt],
      ← card_sq_map (embE t E) hι]
    exact M.card_sq_T0'_z2E
  · show Nat.card {y : M.W0.map (embE t E) // (y : G) ^ 2 = t} = 48
    have h := card_sq_map (embE t E) hι M.W0 M.tE
    rw [hιt] at h
    rw [← h]
    exact M.card_sq_W0_tE
  · show Nat.card {y : M.W0.map (embE t E) // (y : G) ^ 2 = t * embE t E M.z1E} = 16
    rw [show t * embE t E M.z1E = embE t E (M.tE * M.z1E) by rw [map_mul, hιt],
      ← card_sq_map (embE t E) hι]
    exact M.card_sq_W0_z2E

end Data

section Main

theorem haradaShape_aux {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht2 : orderOf t = 2)
    (E : Subgroup ↥(centralizer ({t} : Set G)))
    (hE : IsHSCover ↥(centralizer ({t} : Set G)) E) :
    IsF5Centralizer ↥(centralizer ({t} : Set G)) E := by
  have hEn := hE.normal
  have hperf := hE.perfect
  have hZ := hE.card_center
  obtain ⟨M⟩ := exists_coverModel hperf hZ hE.quotient
  have hcard := card_eq_of_double_cover hZ hE.quotient
  obtain ⟨D⟩ := exists_thetaData (E := E) M.toCoverMaps
  obtain ⟨S, hTS⟩ := (M.isPGroup_T0.map E.subtype).exists_le_sylow
  have hSE := inf_eq_map_T0 M hcard S.isPGroup' hTS
  have hder := D.commutator_eq hE M S.isPGroup' hTS
  have hData := harCoreData_of_cover ht2 hE M
    (fun h hh => D.mem_of_centralizer hE M hh) hSE hder
  have hι := embE_injective t E
  have hιt := embE_tE ht2 hE M.toCoverMaps
  by_cases hN : ∀ n ∈ normalizer (((S : Subgroup ↥(centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype : Subgroup G) : Set G), n * t * n⁻¹ = t
  ·
    have hNH : normalizer (((S : Subgroup ↥(centralizer ({t} : Set G))).map
        (centralizer ({t} : Set G)).subtype : Subgroup G) : Set G) ≤ centralizer ({t} : Set G) :=
      fun n hn => mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 (hN n hn))
    obtain ⟨P, hP⟩ :=
      CFSG.ComponentClassification.StandardRecognition.exists_sylow_eq_map_of_normalizer_map_le
        (centralizer ({t} : Set G)) S hNH
    have hinv : ∀ u ∈ E.map (centralizer ({t} : Set G)).subtype, u ^ 2 = 1 → u ≠ 1 → u ≠ t →
        ∃ e ∈ E.map (centralizer ({t} : Set G)).subtype,
          e * u * e⁻¹ = embE t E M.z1E ∨ e * u * e⁻¹ = t * embE t E M.z1E := by
      rintro _ ⟨u₀, hu₀, rfl⟩ hu2 hu1 hut
      have hu2' : (⟨u₀, hu₀⟩ : ↥E) ^ 2 = 1 := hι (by rw [map_pow, map_one]; exact hu2)
      have hu1' : (⟨u₀, hu₀⟩ : ↥E) ≠ 1 := fun h => hu1 (by
        have := congrArg (embE t E) h
        rw [map_one] at this
        exact this)
      have hut' : (⟨u₀, hu₀⟩ : ↥E) ≠ M.tE := fun h => hut (by
        have := congrArg (embE t E) h
        rw [hιt] at this
        exact this)
      obtain ⟨e, he⟩ := M.exists_conj_of_involution hZ hu2' hu1' hut'
      refine ⟨embE t E e, ⟨(e : ↥(centralizer ({t} : Set G))), e.2, rfl⟩, ?_⟩
      rcases he with he | he
      · refine Or.inl ?_
        have := congrArg (embE t E) he
        simp only [map_mul, map_inv] at this
        exact this
      · refine Or.inr ?_
        have := congrArg (embE t E) he
        simp only [map_mul, map_inv, hιt] at this
        exact this
    have hfus := harCore_S hData P hP.symm hN hinv
    obtain ⟨g, hgt, hgc⟩ := exists_fused_commuting_involution hnonab ht2
    have hpH : g * t * g⁻¹ ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hgc
    have hpE : (⟨g * t * g⁻¹, hpH⟩ : ↥(centralizer ({t} : Set G))) ∉ E := by
      intro h
      apply hgt
      have := hfus g⁻¹ (by
        rw [inv_inv]
        exact ⟨_, h, rfl⟩)
      rwa [inv_inv] at this
    refine
      { toIsHSCover := hE
        index_eq_two := index_eq_two_of_not_mem hE.index_dvd_two hpE
        exists_outer_involution := ⟨⟨g * t * g⁻¹, hpH⟩, hpE, Subtype.ext ?_⟩ }
    have h2 : t ^ 2 = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht2] at this
    show (g * t * g⁻¹) ^ 2 = 1
    rw [conj_pow, h2]
    group
  ·
    obtain ⟨n, hn, hnt⟩ : ∃ n ∈ normalizer (((S : Subgroup ↥(centralizer ({t} : Set G))).map
        (centralizer ({t} : Set G)).subtype : Subgroup G) : Set G), n * t * n⁻¹ ≠ t := by
      by_contra hcon
      exact hN fun n hn => by_contra fun hne => hcon ⟨n, hn, hne⟩
    obtain ⟨⟨s, hsS, hsE⟩, ⟨v, hvS, hv2, hvE⟩⟩ := harCore_NS hData hn hnt
    obtain ⟨s₀, hs₀, rfl⟩ := hsS
    obtain ⟨v₀, hv₀, rfl⟩ := hvS
    exact
      { toIsHSCover := hE
        index_eq_two := index_eq_two_of_not_mem hE.index_dvd_two (fun h => hsE ⟨s₀, h, rfl⟩)
        exists_outer_involution :=
          ⟨v₀, fun h => hvE ⟨v₀, h, rfl⟩, Subtype.ext (by simpa using hv2)⟩ }

theorem haradaCentralizerShape : HaradaCentralizerShape := by
  intro G _ _ _ hnonab t ht2 E hE
  exact haradaShape_aux hnonab ht2 E hE

end Main

end CFSG.EvenSporadicStandard.TwoHS
