module

public import CFSG.GH74.Uniqueness.SU.SU8Count
public import CFSG.GH74.Uniqueness.SU.SU8Outer
public import CFSG.GH74.Uniqueness.SU.SU8Prod

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.Bender CFSG.GH74.Uniqueness.SU.SU4
  CFSG.GH74.Uniqueness.SU.SU8.Setup

namespace L205

variable {G : Type} [Group G] [Finite G]

theorem bar_inj_of_pgroup {H T : Subgroup G} (hT : IsPGroup 2 T) {x y : ↥H} (hx : (x : G) ∈ T)
    (hy : (y : G) ∈ T) (h : bar H x = bar H y) : x = y := by
  have h1 : x⁻¹ * y ∈ pPrimeCore 2 ↥H := bar_eq_bar_iff.mp h
  have hxy : ((x⁻¹ * y : ↥H) : G) ∈ T := T.mul_mem (T.inv_mem hx) hy
  obtain ⟨k, hk⟩ := hT ⟨((x⁻¹ * y : ↥H) : G), hxy⟩
  have hk' : (x⁻¹ * y) ^ (2 ^ k) = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hk)
  exact inv_mul_eq_one.mp (eq_one_of_mem_odd (odd_card_core H) h1 hk')

theorem lemma205_aux {H L A T : Subgroup G} (hLH : L ≤ H) (hLN : H ≤ normalizer (L : Set G))
    (hZ : center ↥(hbarImage H L) = ⊥) (hTH : IsSylowIn H T) (hAT : A ≤ T)
    (hTc : ∀ s ∈ T, ∀ a ∈ A, s * a * s⁻¹ = a) (hAL : Nat.card ↥(A ⊓ L) = 4)
    (hexists : ∀ PT : Sylow 2 ↥H, ∃ PK : Sylow 2 ↥(hbarImage H L),
      ∀ g : ↥(hbarImage H L), g ∈ (PK : Subgroup ↥(hbarImage H L)) ↔
        ∃ s ∈ (PT : Subgroup ↥H) ⊓ L.subgroupOf H, (g : Hbar H) = bar H s)
    (hPK4 : ∀ P : Sylow 2 ↥(hbarImage H L), Nat.card (P : Subgroup ↥(hbarImage H L)) = 4)
    (hinner : ∀ S : Subgroup (Hbar H), IsSylowIn ⊤ S → ∀ P : Sylow 2 ↥(hbarImage H L),
      (∀ s ∈ S, ∀ x : ↥(hbarImage H L), x ∈ (P : Subgroup ↥(hbarImage H L)) →
        s * (x : Hbar H) * s⁻¹ = x) →
      ∀ h : Hbar H, ∃ k : ↥(hbarImage H L), ∀ x : ↥(hbarImage H L),
        h * (x : Hbar H) * h⁻¹ = (k : Hbar H) * x * (k : Hbar H)⁻¹)
    (hQ2 : Nat.card T = 4 * Nat.card ↥(T ⊓ centralizerBar H L) →
      Nat.card ↥(T ⊓ centralizerBar H L) = 2) :
    Nonempty (Hbar H ≃* Multiplicative (ZMod 2) × ↥(hbarImage H L)) := by
  classical
  have hTH' : IsSylowIn H T := hTH
  have hKnormal : (hbarImage H L).Normal := hbarImage_normal hLH hLN
  let PT : Sylow 2 ↥H := Burn.sylowOf hTH'
  obtain ⟨PK, hPK⟩ := hexists PT
  let Sb : Sylow 2 (Hbar H) :=
    PT.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥H))
  have hSb : (Sb : Subgroup (Hbar H)) = (PT : Subgroup ↥H).map (bar H) :=
    Sylow.coe_mapSurjective _ PT
  have hSbSyl : IsSylowIn ⊤ (Sb : Subgroup (Hbar H)) := by
    refine ⟨le_top, Sb.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp Sb.not_dvd_index)
  have hTpg : IsPGroup 2 T := hTH.2.1
  have hTH2 : T ≤ H := hTH.1
  have hinj : ∀ {x y : ↥H}, (x : G) ∈ T → (y : G) ∈ T → bar H x = bar H y → x = y :=
    fun hx hy h => bar_inj_of_pgroup hTpg hx hy h
  have hmemSb : ∀ s : Hbar H, s ∈ (Sb : Subgroup (Hbar H)) ↔
      ∃ x : ↥H, (x : G) ∈ T ∧ bar H x = s := by
    intro s
    rw [hSb]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hPKcard : Nat.card (PK : Subgroup ↥(hbarImage H L)) = 4 := hPK4 PK
  have hALH : ∀ a ∈ A ⊓ L, a ∈ H := fun a ha => hLH ha.2
  let ALk : ↥(A ⊓ L) → ↥(hbarImage H L) := fun a =>
    ⟨bar H ⟨a.1, hALH a.1 a.2⟩, bar_mem_hbarImage a.2.2⟩
  have hALk_mem : ∀ a : ↥(A ⊓ L), ALk a ∈ (PK : Subgroup ↥(hbarImage H L)) := by
    intro a
    refine (hPK (ALk a)).mpr ⟨⟨a.1, hALH a.1 a.2⟩, ⟨hAT a.2.1, a.2.2⟩, rfl⟩
  have hALk_inj : Function.Injective ALk := by
    intro a b hab
    have h1 : bar H ⟨a.1, hALH a.1 a.2⟩ = bar H ⟨b.1, hALH b.1 b.2⟩ :=
      congrArg Subtype.val hab
    have h2 := hinj (hAT a.2.1) (hAT b.2.1) h1
    have h3 : (a.1 : G) = (b.1 : G) := congrArg (fun x : ↥H => (x : G)) h2
    exact Subtype.ext h3
  have hPKeq : ∀ p : ↥(hbarImage H L), p ∈ (PK : Subgroup ↥(hbarImage H L)) →
      ∃ a : ↥(A ⊓ L), ALk a = p := by
    have hrange : Set.range ALk = ((PK : Subgroup ↥(hbarImage H L)) : Set _) := by
      apply Set.eq_of_subset_of_ncard_le
      · rintro _ ⟨a, rfl⟩; exact hALk_mem a
      · rw [Set.ncard_range_of_injective hALk_inj, ← Nat.card_coe_set_eq]
        rw [hAL]
        exact hPKcard.le
      · exact Set.toFinite _
    intro p hp
    have : p ∈ Set.range ALk := by rw [hrange]; exact hp
    exact this
  have hP : ∀ s ∈ (Sb : Subgroup (Hbar H)), ∀ x : ↥(hbarImage H L),
      x ∈ (PK : Subgroup ↥(hbarImage H L)) → s * (x : Hbar H) * s⁻¹ = x := by
    intro s hs x hx
    obtain ⟨s₀, hs₀, rfl⟩ := (hmemSb s).mp hs
    obtain ⟨a, rfl⟩ := hPKeq x hx
    have := hTc (s₀ : G) hs₀ a.1 (a.2.1)
    have h2 : (s₀ : ↥H) * ⟨a.1, hALH a.1 a.2⟩ * s₀⁻¹ = ⟨a.1, hALH a.1 a.2⟩ :=
      Subtype.ext this
    show bar H s₀ * bar H ⟨a.1, hALH a.1 a.2⟩ * (bar H s₀)⁻¹ = bar H ⟨a.1, hALH a.1 a.2⟩
    rw [← map_inv, ← map_mul, ← map_mul, h2]
  have hinner' := hinner _ hSbSyl PK hP
  have hsup : ∀ h : Hbar H, ∃ k ∈ hbarImage H L,
      k⁻¹ * h ∈ centralizer ((hbarImage H L : Subgroup (Hbar H)) : Set (Hbar H)) := by
    intro h
    obtain ⟨k, hk⟩ := hinner' h
    refine ⟨(k : Hbar H), k.2, Subgroup.mem_centralizer_iff.mpr (fun g hg => ?_)⟩
    have h1 := hk ⟨g, hg⟩
    have h2 : h * g = k * g * (k : Hbar H)⁻¹ * h := by
      calc h * g = (h * g * h⁻¹) * h := by group
        _ = (k * g * (k : Hbar H)⁻¹) * h := by rw [h1]
    calc g * ((k : Hbar H)⁻¹ * h) = (k : Hbar H)⁻¹ * (k * g * (k : Hbar H)⁻¹ * h) := by
          group
      _ = (k : Hbar H)⁻¹ * (h * g) := by rw [h2]
      _ = ((k : Hbar H)⁻¹ * h) * g := by group
  have hKC : hbarImage H L ⊓ centralizer
      ((hbarImage H L : Subgroup (Hbar H)) : Set (Hbar H)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.1⟩ : ↥(hbarImage H L)) ∈ center ↥(hbarImage H L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2)
    rw [hZ, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
  have hPKS : ∀ p : ↥(hbarImage H L), p ∈ (PK : Subgroup ↥(hbarImage H L)) →
      (p : Hbar H) ∈ (Sb : Subgroup (Hbar H)) := by
    intro p hp
    obtain ⟨s, hs, hps⟩ := (hPK p).mp hp
    rw [hps]
    exact (hmemSb _).mpr ⟨s, Subgroup.mem_subgroupOf.mp hs.1, rfl⟩
  set C : Subgroup (Hbar H) :=
    centralizer ((hbarImage H L : Subgroup (Hbar H)) : Set (Hbar H)) with hC
  have hWQ : Nat.card ↥((Sb : Subgroup (Hbar H)) ⊓ C) =
      Nat.card ↥(T ⊓ centralizerBar H L) := by
    symm
    apply Nat.card_congr
    refine Equiv.ofBijective (fun q : ↥(T ⊓ centralizerBar H L) =>
      (⟨bar H ⟨q.1, (mem_centralizerBar.mp q.2.2).1⟩, ?_, ?_⟩ :
        ↥((Sb : Subgroup (Hbar H)) ⊓ C))) ⟨?_, ?_⟩
    · exact (hmemSb _).mpr ⟨_, q.2.1, rfl⟩
    · refine Subgroup.mem_centralizer_iff.mpr (fun g hg => ?_)
      obtain ⟨l, hl, rfl⟩ := mem_hbarImage.mp hg
      exact (mem_centralizerBar.mp q.2.2).2 l hl
    · intro q q' h
      have h1 := congrArg Subtype.val h
      have h2 := hinj q.2.1 q'.2.1 h1
      have h3 : (q.1 : G) = (q'.1 : G) := congrArg (fun x : ↥H => (x : G)) h2
      exact Subtype.ext h3
    · rintro ⟨w, hwS, hwC⟩
      obtain ⟨x, hxT, rfl⟩ := (hmemSb w).mp hwS
      refine ⟨⟨(x : G), hxT, ?_⟩, rfl⟩
      refine (mem_centralizerBar (H := H) (L := L) (g := (x : G))).mpr ⟨x.2, fun l hl => ?_⟩
      exact Subgroup.mem_centralizer_iff.mp hwC (bar H l) (bar_mem_hbarImage hl)
  have hTSb : Nat.card T = Nat.card (Sb : Subgroup (Hbar H)) := by
    apply Nat.card_congr
    refine Equiv.ofBijective (fun x : ↥T =>
      (⟨bar H ⟨x.1, hTH2 x.2⟩, (hmemSb _).mpr ⟨_, x.2, rfl⟩⟩ :
        ↥(Sb : Subgroup (Hbar H)))) ⟨?_, ?_⟩
    · intro x y h
      have h1 := congrArg Subtype.val h
      have h2 := hinj x.2 y.2 h1
      have h3 : (x.1 : G) = (y.1 : G) := congrArg (fun x : ↥H => (x : G)) h2
      exact Subtype.ext h3
    · rintro ⟨w, hw⟩
      obtain ⟨x, hxT, rfl⟩ := (hmemSb w).mp hw
      exact ⟨⟨(x : G), hxT⟩, rfl⟩
  have hSbcard := Prod.card_sylow_split (hbarImage H L) hKC hsup Sb.isPGroup' PK hPKS
  have hTQ : Nat.card T = 4 * Nat.card ↥(T ⊓ centralizerBar H L) := by
    rw [hTSb, hSbcard, hPKcard, hWQ]
  have hQ2' := hQ2 hTQ
  have hW2 : Nat.card ↥((Sb : Subgroup (Hbar H)) ⊓ C) = 2 := by rw [hWQ]; exact hQ2'
  have hC2 := Prod.card_centralizer_eq_two (hbarImage H L) hKC hsup (pPrimeCore_hbar H)
    hSbSyl PK hPKS hW2
  have hCZ : Nonempty (↥C ≃* Multiplicative (ZMod 2)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic ↥C := isCyclic_of_prime_card hC2
    have hcard : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)]
      exact Nat.card_zmod 2
    exact ⟨mulEquivOfCyclicCardEq (hC2.trans hcard.symm)⟩
  obtain ⟨eC⟩ := hCZ
  exact ⟨(Prod.prodEquiv (hbarImage H L) hKC hsup).symm.trans
    (MulEquiv.prodComm.trans (MulEquiv.prodCongr eC (MulEquiv.refl _)))⟩

theorem lemma205_of_lin
    {z : G} {S L A : Subgroup G} (hyp : Hyp20A z S L A)
    (hZ : center ↥(hbarImage (Hz z) L) = ⊥) (hlin : BenderType ↥(hbarImage (Hz z) L) 2 1 1) :
    Nonempty (Hbar (Hz z) ≃* Multiplicative (ZMod 2) × ↥(hbarImage (Hz z) L)) := by
  have o := out203 hyp hZ
  obtain ⟨T, hT, hAT, hcl⟩ := hyp.exists_syl
  have hTH : T ≤ Hz z := o.syl_le_H hT hAT hcl hyp
  have hnormL := hyp.normal_subgroupOf
  have hKn : (hbarImage (Hz z) L).Normal := hbarImage_normal hyp.L_le hyp.L_normal
  refine lemma205_aux hyp.L_le hyp.L_normal hZ (Burn.sylowIn_of_le hT hTH le_top) hAT
    (o.syl_centralizes hT hAT hcl) (by rw [o.act.card_AL]; norm_num) ?_ ?_ ?_ ?_
  · intro PT
    exact Lift.exists_sylow_image (O := pPrimeCore 2 ↥(Hz z)) (L := L.subgroupOf (Hz z)) PT
  · intro P
    obtain ⟨t, hc⟩ := hlin.exists_benderCore P
    rw [hc.card_eq]; norm_num
  · intro S hS P hP
    exact Outer.forall_inner_of_sylow_centralizes (hbarImage (Hz z) L) hlin hS P hP
  · exact o.card_Q hyp hT hAT hcl

end L205

end CFSG.GH74.Uniqueness.SU.SU8
