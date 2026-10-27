module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeULift
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeUModel

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

namespace HeU

theorem exists_pair_lift {H : Type*} [Group H] [Finite H] {v₁ v₂ : H ⧸ pPrimeCore 2 H}
    (h₁ : v₁ * v₁ = 1) (h₂ : v₂ * v₂ = 1) (hc : v₁ * v₂ = v₂ * v₁) :
    ∃ u₁ u₂ : H, u₁ * u₁ = 1 ∧ u₂ * u₂ = 1 ∧ u₁ * u₂ = u₂ * u₁ ∧
      QuotientGroup.mk' (pPrimeCore 2 H) u₁ = v₁ ∧
      QuotientGroup.mk' (pPrimeCore 2 H) u₂ = v₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 H) with hπ
  set V : Subgroup (H ⧸ pPrimeCore 2 H) := zpowers v₁ ⊔ zpowers v₂ with hV
  have hVe : IsElemTwo V := (isElemTwo_zpowers h₁).sup (isElemTwo_zpowers h₂) (by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute v₁ v₂ from hc) i j).eq)
  set P : Subgroup H := V.comap π with hP
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥P) := inferInstance
  let f : ↥P →* ↥V := (π.comp P.subtype).codRestrict V fun x => x.2
  have hf : Function.Surjective f := by
    rintro ⟨v, hv⟩
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 H) v
    exact ⟨⟨h, hv⟩, rfl⟩
  have htop : ((R.mapSurjective hf : Sylow 2 ↥V) : Subgroup ↥V) = ⊤ :=
    ((R.mapSurjective hf).is_maximal' (hVe.isPGroup.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  set S : Subgroup H := (R : Subgroup ↥P).map P.subtype with hS
  have hSp : IsPGroup 2 S := R.isPGroup'.map P.subtype
  have hlift : ∀ v ∈ V, ∃ u ∈ S, π u = v := by
    intro v hv
    have hmem : (⟨v, hv⟩ : ↥V) ∈ (R : Subgroup ↥P).map f := by rw [htop]; exact mem_top _
    obtain ⟨r, hr, hrv⟩ := mem_map.mp hmem
    exact ⟨(r : H), mem_map_of_mem P.subtype hr, congrArg Subtype.val hrv⟩
  obtain ⟨u₁, hu₁S, hu₁⟩ := hlift v₁ (mem_sup_left (mem_zpowers v₁))
  obtain ⟨u₂, hu₂S, hu₂⟩ := hlift v₂ (mem_sup_right (mem_zpowers v₂))
  have hinj := GSThmB.OddQuot.injOn_of_isPGroup hSp
  refine ⟨u₁, u₂, ?_, ?_, ?_, hu₁, hu₂⟩
  · exact hinj (mul_mem hu₁S hu₁S) (one_mem S) (by rw [map_mul, hu₁, h₁, map_one])
  · exact hinj (mul_mem hu₂S hu₂S) (one_mem S) (by rw [map_mul, hu₂, h₂, map_one])
  · exact hinj (mul_mem hu₁S hu₂S) (mul_mem hu₂S hu₁S) (by rw [map_mul, map_mul, hu₁, hu₂, hc])

theorem mul_mul_self_eq_one {H : Type*} [Group H] {u₁ u₂ : H} (h₁ : u₁ * u₁ = 1)
    (h₂ : u₂ * u₂ = 1) (hc : u₁ * u₂ = u₂ * u₁) : u₁ * u₂ * (u₁ * u₂) = 1 := by
  calc u₁ * u₂ * (u₁ * u₂) = u₁ * (u₂ * u₁) * u₂ := by group
    _ = u₁ * (u₁ * u₂) * u₂ := by rw [hc]
    _ = (u₁ * u₁) * (u₂ * u₂) := by group
    _ = 1 := by rw [h₁, h₂, one_mul]


theorem exists_four_layers {H : Type} [Group H] [Finite H]
    (e : H ⧸ pPrimeCore 2 H ≃* Blueprint.NativeSporadic.He) :
    ∃ u₁ u₂ : H, u₁ * u₁ = 1 ∧ u₂ * u₂ = 1 ∧ u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₁ ≠ u₂ ∧
      u₁ * u₂ = u₂ * u₁ ∧ ∀ w : H, (w = u₁ ∨ w = u₂ ∨ w = u₁ * u₂) →
        ∃ T : Subgroup H, T ≤ centralizer ({w} : Set H) ∧
          IsPComponent 2 (T.subgroupOf (centralizer ({w} : Set H))) ∧
          IsL34Type (↥T ⧸ Open.fusionZStar ↥T) ∧
          u₁ ∈ (Open.fusionZStar ↥T).map T.subtype ∧
          u₂ ∈ (Open.fusionZStar ↥T).map T.subtype := by
  set Q := H ⧸ pPrimeCore 2 H with hQ
  set π := QuotientGroup.mk' (pPrimeCore 2 H) with hπ
  let e' : ↥(⊤ : Subgroup Q) ≃* Blueprint.NativeSporadic.He := Subgroup.topEquiv.trans e
  obtain ⟨v₁, -, v₂, -, hs₁, hs₂, hn₁, hn₂, hne, hc, hw⟩ := exists_twoA_four_of_held e'
  obtain ⟨u₁, u₂, hu₁, hu₂, huc, hπ₁, hπ₂⟩ := exists_pair_lift hs₁ hs₂ hc
  have hn : ∀ u : H, ∀ v : Q, π u = v → v ≠ 1 → u ≠ 1 := by
    rintro u v huv hv rfl
    rw [map_one] at huv
    exact hv huv.symm
  refine ⟨u₁, u₂, hu₁, hu₂, hn u₁ v₁ hπ₁ hn₁, hn u₂ v₂ hπ₂ hn₂, ?_, huc, ?_⟩
  · rintro rfl
    exact hne (hπ₁.symm.trans hπ₂)
  intro w hwc
  have hww : w * w = 1 := by
    rcases hwc with rfl | rfl | rfl
    · exact hu₁
    · exact hu₂
    · exact mul_mul_self_eq_one hu₁ hu₂ huc
  have hwv : π w = v₁ ∨ π w = v₂ ∨ π w = v₁ * v₂ := by
    rcases hwc with rfl | rfl | rfl
    · exact Or.inl hπ₁
    · exact Or.inr (Or.inl hπ₂)
    · exact Or.inr (Or.inr (by rw [map_mul, hπ₁, hπ₂]))
  obtain ⟨htwo, hv₁Z, hv₂Z⟩ := hw (π w) (mem_top _) hwv
  set K := gsFixedLayer (⊤ : Subgroup Q) (π w) with hKdef
  have hKC : K ≤ centralizer ({π w} : Set Q) :=
    (gsFixedLayer_le_inf _ _).trans inf_le_right
  have hKp : IsPComponent 2 (K.subgroupOf (centralizer ({π w} : Set Q))) := by
    have h := isPComponent_gsFixedLayer_of_held e' htwo
    rwa [top_inf_eq] at h
  obtain ⟨hKperf, hKt⟩ := heldTwoALayerFact Q ⊤ ⟨e'⟩ (π w) htwo
  obtain ⟨T, hTC, hTp, htype, hZ⟩ := exists_layer_lift hww hKC hKp hKperf hKt
  have hc₁ : u₁ ∈ centralizer ({w} : Set H) := by
    rw [mem_centralizer_singleton_iff]
    rcases hwc with h | h | h
    · rw [h]
    · rw [h, huc]
    · rw [h, ← mul_assoc, hu₁, one_mul, mul_assoc, ← huc, ← mul_assoc, hu₁, one_mul]
  have hc₂ : u₂ ∈ centralizer ({w} : Set H) := by
    rw [mem_centralizer_singleton_iff]
    rcases hwc with h | h | h
    · rw [h, huc]
    · rw [h]
    · rw [h, mul_assoc u₁, hu₂, mul_one, ← mul_assoc, ← huc, mul_assoc, hu₂, mul_one]
  exact ⟨T, hTC, hTp, htype, hZ u₁ hc₁ hu₁ (hπ₁ ▸ hv₁Z), hZ u₂ hc₂ hu₂ (hπ₂ ▸ hv₂Z)⟩

theorem exists_four_layers_in {X : Type} [Group X] [Finite X] {a : X} {L : Subgroup X}
    (hLa : L ≤ centralizer ({a} : Set X))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X))))
    (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He) :
    ∃ u₁ ∈ L, ∃ u₂ ∈ L, u₁ * u₁ = 1 ∧ u₂ * u₂ = 1 ∧ u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₁ ≠ u₂ ∧
      u₁ * u₂ = u₂ * u₁ ∧ ∀ w : X, (w = u₁ ∨ w = u₂ ∨ w = u₁ * u₂) →
        ∃ T : Subgroup X, T ≤ L ∧
          T ≤ centralizer ({a} : Set X) ⊓ centralizer ({w} : Set X) ∧
          IsPComponent 2 (T.subgroupOf (centralizer ({a} : Set X) ⊓ centralizer ({w} : Set X))) ∧
          IsL34Type (↥T ⧸ Open.fusionZStar ↥T) ∧
          u₁ ∈ (Open.fusionZStar ↥T).map T.subtype ∧
          u₂ ∈ (Open.fusionZStar ↥T).map T.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u₁, u₂, h₁, h₂, hn₁, hn₂, hne, hc, hall⟩ := exists_four_layers e
  refine ⟨u₁, u₁.2, u₂, u₂.2, congrArg Subtype.val h₁, congrArg Subtype.val h₂,
    fun h => hn₁ (Subtype.ext h), fun h => hn₂ (Subtype.ext h), fun h => hne (Subtype.ext h),
    congrArg Subtype.val hc, ?_⟩
  intro w hw
  obtain ⟨w', hw', rfl⟩ : ∃ w' : ↥L, (w' = u₁ ∨ w' = u₂ ∨ w' = u₁ * u₂) ∧ (w' : X) = w := by
    rcases hw with h | h | h
    · exact ⟨u₁, Or.inl rfl, h.symm⟩
    · exact ⟨u₂, Or.inr (Or.inl rfl), h.symm⟩
    · exact ⟨u₁ * u₂, Or.inr (Or.inr rfl), h.symm⟩
  obtain ⟨T', hT'C, hT'p, hT't, hZ₁, hZ₂⟩ := hall w' hw'
  set Cw := centralizer ({(w' : X)} : Set X) with hCw
  set Ca := centralizer ({a} : Set X) with hCa
  set T : Subgroup X := T'.map L.subtype with hTdef
  have hTL : T ≤ L := map_subtype_le _
  have hTLw : T ≤ L ⊓ Cw := by
    rintro _ ⟨t, ht, rfl⟩
    refine mem_inf.mpr ⟨t.2, ?_⟩
    have h := hT'C ht
    show (t : X) ∈ Cw
    rw [hCw, mem_centralizer_singleton_iff]
    rw [mem_centralizer_singleton_iff] at h
    exact congrArg Subtype.val h
  have hT1 : IsPComponent 2 (T.subgroupOf (L ⊓ Cw)) := by
    rw [← UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (X := L) inf_le_left 2
      Nat.prime_two]
    have h1 : T.subgroupOf L = T' := comap_map_eq_self_of_injective L.subtype_injective T'
    have h2 : (L ⊓ Cw).subgroupOf L = centralizer ({w'} : Set ↥L) := by
      ext y
      rw [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
      exact ⟨fun h => Subtype.ext h.2, fun h => ⟨y.2, congrArg Subtype.val h⟩⟩
    rw [h1, h2]
    exact hT'p
  have hLs : (L.subgroupOf Ca).IsSubnormal :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L Ca hLa).1 hL).1
  have hLs' : ((L ⊓ Cw).subgroupOf (Ca ⊓ Cw)).IsSubnormal := by
    have h1 : ((L.subgroupOf Ca).subgroupOf ((Ca ⊓ Cw).subgroupOf Ca)).IsSubnormal :=
      hLs.subgroupOf
    have h2 := h1.map (f := (subgroupOfEquivOfLe (inf_le_left : Ca ⊓ Cw ≤ Ca)).toMonoidHom)
      (subgroupOfEquivOfLe (inf_le_left : Ca ⊓ Cw ≤ Ca)).surjective
    convert h2 using 1
    ext k
    simp only [mem_subgroupOf, mem_inf, mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨hkL, -⟩
      exact ⟨⟨⟨k, (mem_inf.mp k.2).1⟩, k.2⟩, hkL, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, (mem_inf.mp ((subgroupOfEquivOfLe (inf_le_left : Ca ⊓ Cw ≤ Ca)) y).2).2⟩
  have hT2 := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hTLw
    (inf_le_inf_right _ hLa) hLs').mpr hT1
  let eT : ↥T' ≃* ↥T := T'.equivMapOfInjective L.subtype L.subtype_injective
  have hker : ¬ 2 ∣ Nat.card eT.toMonoidHom.ker := by
    rw [show eT.toMonoidHom.ker = ⊥ from (MonoidHom.ker_eq_bot_iff _).mpr eT.injective,
      card_bot]
    norm_num
  obtain ⟨eZ⟩ :=
    GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective eT.toMonoidHom eT.surjective hker
  have hcomap :=
    GSThmB.OddQuot.comap_fusionZStar_of_surjective eT.toMonoidHom eT.surjective hker
  have hmem : ∀ x : ↥L, x ∈ (Open.fusionZStar ↥T').map T'.subtype →
      (x : X) ∈ (Open.fusionZStar ↥T).map T.subtype := by
    rintro x ⟨t, ht, rfl⟩
    refine ⟨eT t, ?_, rfl⟩
    rw [← hcomap] at ht
    exact ht
  exact ⟨T, hTL, hTLw.trans (inf_le_inf_right _ hLa), hT2,
    LieType.CurtisTits.lieModel_of_mulEquiv eZ hT't, hmem _ hZ₁, hmem _ hZ₂⟩

end HeU

end CFSG.ComponentClassification.GrSLit
