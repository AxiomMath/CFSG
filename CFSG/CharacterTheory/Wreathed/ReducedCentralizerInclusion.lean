module

public import CFSG.CharacterTheory.Wreathed.OddNormalQuotientInvolutions
public import CFSG.CharacterTheory.Wreathed.CyclicOddScalarQuotient

public noncomputable section

namespace CFSG.Wreathed.ReducedCentralizerInclusion

universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H]

theorem oddCore_map_of_surjective [Finite G] [Finite H]
    (phi : G →* H) (hphi : Function.Surjective phi)
    (hker : Odd (Nat.card phi.ker)) :
    (CFSG.oddCore G).map phi = CFSG.oddCore H := by
  apply le_antisymm
  · apply le_sSup
    refine ⟨Subgroup.Normal.map inferInstance phi hphi, ?_⟩
    exact (CFSG.ComponentClassification.OddCore.odd_card G).of_dvd_nat
      (Subgroup.card_map_dvd _ phi)
  · let P := (CFSG.oddCore H).comap phi
    have hPodd : Odd (Nat.card P) := CyclicOddScalarQuotient.comap_odd_card phi hphi hker
      (CFSG.oddCore H) (CFSG.ComponentClassification.OddCore.odd_card H)
    have hPle : P ≤ CFSG.oddCore G :=
      le_sSup ⟨Subgroup.Normal.comap inferInstance phi, hPodd⟩
    have hmap : P.map phi = CFSG.oddCore H :=
      Subgroup.map_comap_eq_self_of_surjective hphi _
    rw [← hmap]
    exact Subgroup.map_mono hPle

theorem oddCore_comap_of_surjective [Finite G] [Finite H]
    (phi : G →* H) (hphi : Function.Surjective phi)
    (hker : Odd (Nat.card phi.ker)) :
    (CFSG.oddCore H).comap phi = CFSG.oddCore G := by
  apply le_antisymm
  · apply le_sSup
    exact ⟨Subgroup.Normal.comap inferInstance phi,
      CyclicOddScalarQuotient.comap_odd_card phi hphi hker _
        (CFSG.ComponentClassification.OddCore.odd_card H)⟩
  · intro g hg
    change phi g ∈ CFSG.oddCore H
    rw [← oddCore_map_of_surjective phi hphi hker]
    exact Subgroup.mem_map_of_mem phi hg

@[expose] def reducedSurjectionEquiv [Finite G] [Finite H]
    (phi : G →* H) (hphi : Function.Surjective phi)
    (hker : Odd (Nat.card phi.ker)) :
    G ⧸ CFSG.oddCore G ≃* H ⧸ CFSG.oddCore H := by
  let f := (QuotientGroup.mk' (CFSG.oddCore H)).comp phi
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp hphi
  have hk : f.ker = CFSG.oddCore G := by
    ext g
    change (QuotientGroup.mk' (CFSG.oddCore H)) (phi g) = 1 ↔ _
    change ((phi g : H) : H ⧸ CFSG.oddCore H) = 1 ↔ g ∈ CFSG.oddCore G
    rw [QuotientGroup.eq_one_iff]
    change g ∈ (CFSG.oddCore H).comap phi ↔ g ∈ CFSG.oddCore G
    rw [oddCore_comap_of_surjective phi hphi hker]
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

theorem reducedSurjectionEquiv_mk [Finite G] [Finite H]
    (phi : G →* H) (hphi : Function.Surjective phi)
    (hker : Odd (Nat.card phi.ker)) (g : G) :
    reducedSurjectionEquiv phi hphi hker (QuotientGroup.mk' (CFSG.oddCore G) g) =
      QuotientGroup.mk' (CFSG.oddCore H) (phi g) := rfl

theorem oddCore_map_of_injective_normal_range [Finite H]
    (phi : G →* H) (hphi : Function.Injective phi) (hnormal : phi.range.Normal) :
    (CFSG.oddCore G).map phi = phi.range ⊓ CFSG.oddCore H := by
  let : phi.range.Normal := hnormal
  let e := MonoidHom.ofInjective hphi
  calc
    (CFSG.oddCore G).map phi =
        ((CFSG.oddCore G).map e.toMonoidHom).map phi.range.subtype := by
      rw [Subgroup.map_map]
      rfl
    _ = (CFSG.oddCore phi.range).map phi.range.subtype := by
      have he : (CFSG.oddCore G).map e.toMonoidHom = CFSG.oddCore phi.range :=
        CFSG.ComponentClassification.OddCore.equiv_invariant e
      rw [he]
    _ = phi.range ⊓ CFSG.oddCore H :=
      CFSG.ComponentClassification.OddCore.normal_intersection H phi.range

theorem oddCore_comap_of_injective_normal_range [Finite H]
    (phi : G →* H) (hphi : Function.Injective phi) (hnormal : phi.range.Normal) :
    (CFSG.oddCore H).comap phi = CFSG.oddCore G := by
  ext g
  change phi g ∈ CFSG.oddCore H ↔ g ∈ CFSG.oddCore G
  rw [← Subgroup.mem_map_iff_mem hphi,
    oddCore_map_of_injective_normal_range phi hphi hnormal]
  exact (and_iff_right ((show phi g ∈ phi.range from ⟨g, rfl⟩))).symm

@[expose] def reducedNormalInclusion [Finite H]
    (phi : G →* H) (hphi : Function.Injective phi) (hnormal : phi.range.Normal) :
    G ⧸ CFSG.oddCore G →* H ⧸ CFSG.oddCore H := by
  let f := (QuotientGroup.mk' (CFSG.oddCore H)).comp phi
  have hk : f.ker = CFSG.oddCore G := by
    ext g
    change (QuotientGroup.mk' (CFSG.oddCore H)) (phi g) = 1 ↔ _
    change ((phi g : H) : H ⧸ CFSG.oddCore H) = 1 ↔ g ∈ CFSG.oddCore G
    rw [QuotientGroup.eq_one_iff]
    change g ∈ (CFSG.oddCore H).comap phi ↔ g ∈ CFSG.oddCore G
    rw [oddCore_comap_of_injective_normal_range phi hphi hnormal]
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  exact f.range.subtype.comp e.toMonoidHom

theorem reducedNormalInclusion_mk [Finite H]
    (phi : G →* H) (hphi : Function.Injective phi) (hnormal : phi.range.Normal) (g : G) :
    reducedNormalInclusion phi hphi hnormal (QuotientGroup.mk' (CFSG.oddCore G) g) =
      QuotientGroup.mk' (CFSG.oddCore H) (phi g) := rfl

theorem reducedNormalInclusion_injective [Finite H]
    (phi : G →* H) (hphi : Function.Injective phi) (hnormal : phi.range.Normal) :
    Function.Injective (reducedNormalInclusion phi hphi hnormal) := by
  unfold reducedNormalInclusion
  exact Subtype.val_injective.comp (MulEquiv.injective _)

theorem reducedNormalInclusion_range [Finite H]
    (phi : G →* H) (hphi : Function.Injective phi) (hnormal : phi.range.Normal) :
    (reducedNormalInclusion phi hphi hnormal).range =
      phi.range.map (QuotientGroup.mk' (CFSG.oddCore H)) := by
  ext h
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore G) g
    rw [reducedNormalInclusion_mk]
    exact Subgroup.mem_map.mpr ⟨phi a, (show phi a ∈ phi.range from ⟨a, rfl⟩), rfl⟩
  · rintro ⟨b, ⟨a, rfl⟩, rfl⟩
    exact ⟨QuotientGroup.mk' (CFSG.oddCore G) a,
      reducedNormalInclusion_mk phi hphi hnormal a⟩

theorem reducedNormalInclusion_normal [Finite H]
    (phi : G →* H) (hphi : Function.Injective phi) (hnormal : phi.range.Normal) :
    (reducedNormalInclusion phi hphi hnormal).range.Normal := by
  rw [reducedNormalInclusion_range]
  exact hnormal.map _ (QuotientGroup.mk'_surjective _)

theorem reducedNormalInclusion_odd_index [Finite H]
    (phi : G →* H) (hphi : Function.Injective phi) (hnormal : phi.range.Normal)
    (hindex : Odd phi.range.index) :
    Odd (reducedNormalInclusion phi hphi hnormal).range.index := by
  rw [reducedNormalInclusion_range]
  exact hindex.of_dvd_nat (Subgroup.index_map_dvd phi.range (QuotientGroup.mk'_surjective _))

theorem involution_mem_normal_of_odd_index
    (L : Subgroup H) [L.Normal] (hindex : Odd L.index) (t : H)
    (ht : orderOf t = 2) : t ∈ L := by
  let q := QuotientGroup.mk' L
  have hqodd : Odd (Nat.card (H ⧸ L)) := by
    simpa only [Subgroup.index_eq_card] using hindex
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have hqt2 : q t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hqt1 : q t = 1 :=
    (OddNormalQuotientInvolutions.odd_power_eq (q t) hqt2 hqodd).symm.trans
      (pow_card_eq_one' (x := q t))
  exact (QuotientGroup.eq_one_iff t).mp hqt1

@[expose] def centralizerInclusion (L : Subgroup H) (t : H) (htL : t ∈ L) :
    Subgroup.centralizer ({(⟨t, htL⟩ : L)} : Set L) →*
      Subgroup.centralizer ({t} : Set H) :=
  (L.subtype.comp (Subgroup.centralizer ({(⟨t, htL⟩ : L)} : Set L)).subtype).codRestrict
    (Subgroup.centralizer ({t} : Set H)) (fun x =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg L.subtype (Subgroup.mem_centralizer_singleton_iff.mp x.property)))

theorem centralizerInclusion_coe (L : Subgroup H) (t : H) (htL : t ∈ L)
    (b : Subgroup.centralizer ({(⟨t, htL⟩ : L)} : Set L)) :
    (centralizerInclusion L t htL b : H) = ((b : L) : H) := rfl

theorem centralizerInclusion_injective (L : Subgroup H) (t : H) (htL : t ∈ L) :
    Function.Injective (centralizerInclusion L t htL) := by
  intro b c hbc
  exact Subtype.ext (Subtype.ext
    (congrArg (fun x : Subgroup.centralizer {t} => (x : H)) hbc))

theorem centralizerInclusion_range (L : Subgroup H) (t : H) (htL : t ∈ L) :
    (centralizerInclusion L t htL).range = L.subgroupOf (Subgroup.centralizer {t}) := by
  ext c
  constructor
  · rintro ⟨b, rfl⟩
    exact (b : L).property
  · intro hc
    let b : L := ⟨(c : H), hc⟩
    have hb : b ∈ Subgroup.centralizer ({(⟨t, htL⟩ : L)} : Set L) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.property))
    exact ⟨⟨b, hb⟩, rfl⟩

theorem centralizerInclusion_normal (L : Subgroup H) [L.Normal]
    (t : H) (htL : t ∈ L) : (centralizerInclusion L t htL).range.Normal := by
  rw [centralizerInclusion_range]
  infer_instance

theorem centralizerInclusion_odd_index (L : Subgroup H) [L.Normal]
    (hindex : Odd L.index) (t : H) (htL : t ∈ L) :
    Odd (centralizerInclusion L t htL).range.index := by
  rw [centralizerInclusion_range]
  change Odd (L.comap (Subgroup.centralizer {t}).subtype).index
  rw [Subgroup.index_comap, Subgroup.range_subtype]
  exact hindex.of_dvd_nat (Subgroup.relIndex_dvd_index_of_normal L _)

theorem centralizerQuotient_odd_kernel
    (O : Subgroup G) [O.Normal] (hO : Odd (Nat.card O)) (v : G) :
    Odd (Nat.card (OddNormalQuotientInvolutions.centralizerQuotient O v).ker) := by
  rw [OddNormalQuotientInvolutions.centralizerQuotient_ker]
  let f : O.subgroupOf (Subgroup.centralizer {v}) →* O :=
    ((Subgroup.centralizer {v}).subtype.comp
      (O.subgroupOf (Subgroup.centralizer {v})).subtype).codRestrict O (fun x => x.property)
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun x : O => (x : G)) hab))
  have hc := Subgroup.card_map_of_injective (K := (⊤ : Subgroup _)) (f := f) hf
  rw [Subgroup.card_top, Subgroup.map_top] at hc
  exact hO.of_dvd_nat (hc ▸ Subgroup.card_subgroup_dvd_card f.range)

@[expose] def reducedCentralizerEquiv [Finite G]
    (O : Subgroup G) [O.Normal] (hO : Odd (Nat.card O))
    (v : G) (hv : orderOf v = 2) :
    Subgroup.centralizer {v} ⧸ CFSG.oddCore (Subgroup.centralizer {v}) ≃*
      Subgroup.centralizer {QuotientGroup.mk' O v} ⧸
        CFSG.oddCore (Subgroup.centralizer {QuotientGroup.mk' O v}) :=
  reducedSurjectionEquiv (OddNormalQuotientInvolutions.centralizerQuotient O v)
    (OddNormalQuotientInvolutions.centralizerQuotient_surjective O hO v hv)
    (centralizerQuotient_odd_kernel O hO v)

theorem reducedCentralizerEquiv_mk [Finite G]
    (O : Subgroup G) [O.Normal] (hO : Odd (Nat.card O))
    (v : G) (hv : orderOf v = 2) (c : Subgroup.centralizer {v}) :
    reducedCentralizerEquiv O hO v hv
      (QuotientGroup.mk' (CFSG.oddCore (Subgroup.centralizer {v})) c) =
    QuotientGroup.mk' (CFSG.oddCore (Subgroup.centralizer {QuotientGroup.mk' O v}))
      (OddNormalQuotientInvolutions.centralizerQuotient O v c) := rfl

theorem quotient_involution_mem
    (O : Subgroup G) [O.Normal] (hO : Odd (Nat.card O))
    (L : Subgroup (G ⧸ O)) [L.Normal] (hindex : Odd L.index)
    (v : G) (hv : orderOf v = 2) : QuotientGroup.mk' O v ∈ L :=
  involution_mem_normal_of_odd_index L hindex _
    (OddNormalQuotientInvolutions.quotient_involution O hO v hv)

@[expose] def reducedCentralizerInjection [Finite G]
    (O : Subgroup G) [O.Normal] (hO : Odd (Nat.card O))
    (L : Subgroup (G ⧸ O)) [L.Normal] (hindex : Odd L.index)
    (v : G) (hv : orderOf v = 2) :
    Subgroup.centralizer
        ({(⟨QuotientGroup.mk' O v, quotient_involution_mem O hO L hindex v hv⟩ : L)} : Set L)
      ⧸ CFSG.oddCore (Subgroup.centralizer
        ({(⟨QuotientGroup.mk' O v, quotient_involution_mem O hO L hindex v hv⟩ : L)} : Set L))
      →* Subgroup.centralizer {v} ⧸ CFSG.oddCore (Subgroup.centralizer {v}) :=
  (reducedCentralizerEquiv O hO v hv).symm.toMonoidHom.comp
    (reducedNormalInclusion
      (centralizerInclusion L _ (quotient_involution_mem O hO L hindex v hv))
      (centralizerInclusion_injective L _ _)
      (centralizerInclusion_normal L _ _))

theorem reducedCentralizerInjection_mk [Finite G]
    (O : Subgroup G) [O.Normal] (hO : Odd (Nat.card O))
    (L : Subgroup (G ⧸ O)) [L.Normal] (hindex : Odd L.index)
    (v : G) (hv : orderOf v = 2)
    (b : Subgroup.centralizer
      ({(⟨QuotientGroup.mk' O v, quotient_involution_mem O hO L hindex v hv⟩ : L)} : Set L)) :
    reducedCentralizerEquiv O hO v hv
      (reducedCentralizerInjection O hO L hindex v hv (QuotientGroup.mk' (CFSG.oddCore
        (Subgroup.centralizer
          ({(⟨QuotientGroup.mk' O v, quotient_involution_mem O hO L hindex v hv⟩ : L)} : Set L)))
        b)) =
      QuotientGroup.mk' (CFSG.oddCore (Subgroup.centralizer {QuotientGroup.mk' O v}))
        (centralizerInclusion L _ (quotient_involution_mem O hO L hindex v hv) b) := by
  unfold reducedCentralizerInjection
  change (reducedCentralizerEquiv O hO v hv)
    ((reducedCentralizerEquiv O hO v hv).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  exact reducedNormalInclusion_mk _ _ _ b

theorem reducedCentralizerInjection_injective [Finite G]
    (O : Subgroup G) [O.Normal] (hO : Odd (Nat.card O))
    (L : Subgroup (G ⧸ O)) [L.Normal] (hindex : Odd L.index)
    (v : G) (hv : orderOf v = 2) :
    Function.Injective (reducedCentralizerInjection O hO L hindex v hv) :=
  (reducedCentralizerEquiv O hO v hv).symm.injective.comp
    (reducedNormalInclusion_injective _ _ _)

theorem reducedCentralizerInjection_range [Finite G]
    (O : Subgroup G) [O.Normal] (hO : Odd (Nat.card O))
    (L : Subgroup (G ⧸ O)) [L.Normal] (hindex : Odd L.index)
    (v : G) (hv : orderOf v = 2) :
    (reducedCentralizerInjection O hO L hindex v hv).range =
      ((L.subgroupOf (Subgroup.centralizer {QuotientGroup.mk' O v})).map
        (QuotientGroup.mk' (CFSG.oddCore (Subgroup.centralizer {QuotientGroup.mk' O v})))).map
          (reducedCentralizerEquiv O hO v hv).symm.toMonoidHom := by
  unfold reducedCentralizerInjection
  rw [MonoidHom.range_comp, reducedNormalInclusion_range, centralizerInclusion_range]

theorem reducedCentralizerInjection_normal [Finite G]
    (O : Subgroup G) [O.Normal] (hO : Odd (Nat.card O))
    (L : Subgroup (G ⧸ O)) [L.Normal] (hindex : Odd L.index)
    (v : G) (hv : orderOf v = 2) :
    (reducedCentralizerInjection O hO L hindex v hv).range.Normal := by
  unfold reducedCentralizerInjection
  rw [MonoidHom.range_comp]
  exact (reducedNormalInclusion_normal _ _ _).map _
    (reducedCentralizerEquiv O hO v hv).symm.surjective

theorem reducedCentralizerInjection_odd_index [Finite G]
    (O : Subgroup G) [O.Normal] (hO : Odd (Nat.card O))
    (L : Subgroup (G ⧸ O)) [L.Normal] (hindex : Odd L.index)
    (v : G) (hv : orderOf v = 2) :
    Odd (reducedCentralizerInjection O hO L hindex v hv).range.index := by
  unfold reducedCentralizerInjection
  rw [MonoidHom.range_comp]
  exact (reducedNormalInclusion_odd_index _ _ _
    (centralizerInclusion_odd_index L hindex _ _)).of_dvd_nat
      (Subgroup.index_map_dvd _ (reducedCentralizerEquiv O hO v hv).symm.surjective)

theorem centralizer_oddCore_map [Finite G]
    (O : Subgroup G) [O.Normal] (hO : Odd (Nat.card O))
    (v : G) (hv : orderOf v = 2) :
    (CFSG.oddCore (Subgroup.centralizer {v})).map
      (OddNormalQuotientInvolutions.centralizerQuotient O v) =
        CFSG.oddCore (Subgroup.centralizer {QuotientGroup.mk' O v}) :=
  oddCore_map_of_surjective _
    (OddNormalQuotientInvolutions.centralizerQuotient_surjective O hO v hv)
    (centralizerQuotient_odd_kernel O hO v)

theorem ambient_centralizer_oddCore_map [Finite G]
    (O : Subgroup G) [O.Normal] (hO : Odd (Nat.card O))
    (v : G) (hv : orderOf v = 2) :
    ((CFSG.oddCore (Subgroup.centralizer {v})).map
      (Subgroup.centralizer {v}).subtype).map (QuotientGroup.mk' O) =
        (CFSG.oddCore (Subgroup.centralizer {QuotientGroup.mk' O v})).map
          (Subgroup.centralizer {QuotientGroup.mk' O v}).subtype := by
  rw [Subgroup.map_map]
  have heq : (QuotientGroup.mk' O).comp (Subgroup.centralizer {v}).subtype =
      (Subgroup.centralizer {QuotientGroup.mk' O v}).subtype.comp
        (OddNormalQuotientInvolutions.centralizerQuotient O v) := rfl
  rw [heq, ← Subgroup.map_map, centralizer_oddCore_map O hO v hv]

theorem centralizerInclusion_core_intersection [Finite H]
    (L : Subgroup H) [L.Normal] (t : H) (htL : t ∈ L) :
    (CFSG.oddCore (Subgroup.centralizer ({(⟨t, htL⟩ : L)} : Set L))).map
        (centralizerInclusion L t htL) =
      L.subgroupOf (Subgroup.centralizer {t}) ⊓ CFSG.oddCore (Subgroup.centralizer {t}) := by
  rw [oddCore_map_of_injective_normal_range _ (centralizerInclusion_injective L t htL)
    (centralizerInclusion_normal L t htL), centralizerInclusion_range]

theorem odd_kernel_and_normal_odd_index_preserve_reduced_centralizer_inclusion [Finite G]
    (O : Subgroup G) [O.Normal] (hO : Odd (Nat.card O))
    (L : Subgroup (G ⧸ O)) [L.Normal] (hindex : Odd L.index)
    (v : G) (hv : orderOf v = 2) :
    let alpha := QuotientGroup.mk' O
    let vbar := alpha v
    let hvL := quotient_involution_mem O hO L hindex v hv
    let C := Subgroup.centralizer {v}
    let Cbar := Subgroup.centralizer {vbar}
    let B := Subgroup.centralizer ({(⟨vbar, hvL⟩ : L)} : Set L)
    let j := centralizerInclusion L vbar hvL
    let psi := reducedCentralizerEquiv O hO v hv
    let iota := reducedCentralizerInjection O hO L hindex v hv
    vbar ∈ L ∧ C.map alpha = Cbar ∧
      ((CFSG.oddCore C).map C.subtype).map alpha = (CFSG.oddCore Cbar).map Cbar.subtype ∧
      (∀ c : C, psi (QuotientGroup.mk' (CFSG.oddCore C) c) =
        QuotientGroup.mk' (CFSG.oddCore Cbar)
          (OddNormalQuotientInvolutions.centralizerQuotient O v c)) ∧
      (CFSG.oddCore B).map j = L.subgroupOf Cbar ⊓ CFSG.oddCore Cbar ∧
      Function.Injective iota ∧ iota.range.Normal ∧ Odd iota.range.index ∧
      ∀ b : B, psi (iota (QuotientGroup.mk' (CFSG.oddCore B) b)) =
        QuotientGroup.mk' (CFSG.oddCore Cbar) (j b) := by
  dsimp only
  exact ⟨quotient_involution_mem O hO L hindex v hv,
    OddNormalQuotientInvolutions.centralizer_map O hO v hv,
    ambient_centralizer_oddCore_map O hO v hv, reducedCentralizerEquiv_mk O hO v hv,
    centralizerInclusion_core_intersection L _ _,
    reducedCentralizerInjection_injective O hO L hindex v hv,
    reducedCentralizerInjection_normal O hO L hindex v hv,
    reducedCentralizerInjection_odd_index O hO L hindex v hv,
    reducedCentralizerInjection_mk O hO L hindex v hv⟩

end CFSG.Wreathed.ReducedCentralizerInclusion
