module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Tools
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Class

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.Open (aschbacherThm5Core aschbacherThm5OddCore aschbacherThm5Preimage
  aschbacherThm5Centralizes aschbacherThm5IsSemisimple)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def layerBar (D A : Subgroup G) : Subgroup (D ⧸ aschbacherThm5OddCore D) :=
  ((twoPrimeLayerIn A).subgroupOf D).map (QuotientGroup.mk' (aschbacherThm5OddCore D))

omit [Finite G] in
theorem map_conj_eq_rightConjugate (X : Subgroup G) (h : G) :
    X.map (MulAut.conj h).toMonoidHom = rightConjugate X h⁻¹ := by
  rw [rightConjugate, inv_inv]

omit [Finite G] in
theorem preimage_layerBar {D A : Subgroup G} (hAD : twoPrimeLayerIn A ≤ D) :
    aschbacherThm5Preimage D (layerBar D A) = twoPrimeLayerIn A ⊔ oddCoreIn D := by
  unfold aschbacherThm5Preimage layerBar
  rw [comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup, subgroupOf_map_subtype,
    inf_of_le_left hAD]
  rfl

namespace MainSetting

variable {Q : Subgroup G} (hS : MainSetting Q)
include hS

omit [Finite G] in
theorem tight_of_mem {A : Subgroup G} (hA : A ∈ linkedClass Q) : TightlyEmbedded A := by
  obtain ⟨⟨a, rfl⟩, -⟩ := hA
  exact rightConjugate_tightlyEmbedded Q hS.tight a

theorem four_of_mem {A : Subgroup G} (hA : A ∈ linkedClass Q) :
    HasFourGroup (twoPrimeLayerIn A) := by
  obtain ⟨⟨a, rfl⟩, -⟩ := hA
  exact hS.four_rightConjugate a

omit [Finite G] hS in
theorem linkedLayer_le_normalizer_oddCoreIn :
    linkedLayer Q ≤ normalizer (oddCoreIn (linkedLayer Q) : Set G) :=
  normalIn_le_normalizer (oddCoreIn_normalIn _)

theorem oddCoreIn_le_normalizer_of_mem {A : Subgroup G} (hA : A ∈ linkedClass Q) :
    oddCoreIn (linkedLayer Q) ≤ normalizer (A : Set G) :=
  oddCoreIn_le_normalizer (hS.tight_of_mem hA) (twoPrimeLayerIn_le A)
    (twoPrimeLayerIn_le_linkedLayer hA) (hS.four_of_mem hA)

omit [Finite G] in
theorem odd_card_inf {A B : Subgroup G} (hA : A ∈ linkedClass Q) (hB : B ∈ linkedClass Q)
    (hne : A ≠ B) : Odd (Nat.card (A ⊓ B : Subgroup G)) := by
  obtain ⟨⟨a, rfl⟩, -⟩ := hA
  obtain ⟨⟨b, rfl⟩, -⟩ := hB
  exact Nat.not_even_iff_odd.mp fun h => hne (eq_of_even_inf_rightConjugate hS.tight h)

theorem eq_of_layerBar_eq {A B : Subgroup G} (hA : A ∈ linkedClass Q) (hB : B ∈ linkedClass Q)
    (h : layerBar (linkedLayer Q) A = layerBar (linkedLayer Q) B) : A = B := by
  by_contra hne
  have hpre := congrArg (aschbacherThm5Preimage (linkedLayer Q)) h
  rw [preimage_layerBar (twoPrimeLayerIn_le_linkedLayer hA),
    preimage_layerBar (twoPrimeLayerIn_le_linkedLayer hB)] at hpre
  obtain ⟨E, hEK, hE, hE4⟩ := hS.four_of_mem hA
  have hEne : E ≠ ⊥ := fun h => by rw [h, card_bot] at hE4; norm_num at hE4
  obtain ⟨⟨u, huE⟩, hu1⟩ := ne_bot_iff_exists_ne_one.mp hEne
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hu2 : u ^ 2 ^ 1 = 1 := by simpa using hE u huE
  have huB : u ∈ B := by
    have hu : u ∈ twoPrimeLayerIn B ⊔ oddCoreIn (linkedLayer Q) :=
      hpre ▸ mem_sup_left (hEK huE)
    exact mem_of_two_element_of_le_sup (twoPrimeLayerIn_le B) (odd_card_oddCoreIn _)
      ((twoPrimeLayerIn_le_linkedLayer hB).trans linkedLayer_le_normalizer_oddCoreIn)
      (hS.oddCoreIn_le_normalizer_of_mem hB) hu hu2
  have huA : u ∈ A := twoPrimeLayerIn_le A (hEK huE)
  have hz : Nat.card (zpowers u) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hE u huE) hu1']
  have heven : Even (Nat.card (A ⊓ B : Subgroup G)) :=
    even_iff_two_dvd.mpr (hz ▸ card_dvd_of_le ((zpowers_le).mpr ⟨huA, huB⟩))
  exact Nat.not_even_iff_odd.mpr (hS.odd_card_inf hA hB hne) heven

theorem aschbacherThm5IsSemisimple_layerBar {A : Subgroup G} (hA : A ∈ linkedClass Q) :
    aschbacherThm5IsSemisimple (layerBar (linkedLayer Q) A) := by
  have hAD := twoPrimeLayerIn_le_linkedLayer hA
  have hlay : CFSG.layer (layerBar (linkedLayer Q) A) = ⊤ :=
    layer_map_mk_eq_top hAD (inf_oddCoreIn_eq (hS.normalIn_linkedLayer hA))
      (isSemisimpleQ_twoPrimeLayerIn A)
  refine aschbacherThm5IsSemisimple_of_layer_eq_top hlay fun hbot => ?_
  have hpre := congrArg (aschbacherThm5Preimage (linkedLayer Q)) hbot
  rw [preimage_layerBar hAD] at hpre
  have hle : twoPrimeLayerIn A ≤ oddCoreIn (linkedLayer Q) := by
    have h1 : twoPrimeLayerIn A ≤ twoPrimeLayerIn A ⊔ oddCoreIn (linkedLayer Q) := le_sup_left
    rw [hpre] at h1
    refine h1.trans ?_
    unfold aschbacherThm5Preimage
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
    rfl
  exact Nat.not_even_iff_odd.mpr ((odd_card_oddCoreIn _).of_dvd_nat (card_dvd_of_le hle))
    (hS.four_of_mem hA).even_card

omit hS in
theorem commutator_mem_inf {A B : Subgroup G} (hL : Linked A B) :
    ∀ t ∈ twoPrimeLayerIn B, ∀ k ∈ twoPrimeLayerIn A,
      t * k * t⁻¹ * k⁻¹ ∈ twoPrimeLayerIn A ⊓ twoPrimeLayerIn B := by
  intro t ht k hk
  have htA := normalizer_le_normalizer_twoPrimeLayerIn A (hL.2 ht)
  have hkB := normalizer_le_normalizer_twoPrimeLayerIn B (hL.1 hk)
  refine mem_inf.mpr ⟨mul_mem ((mem_normalizer_iff.mp htA k).mp hk) (inv_mem hk), ?_⟩
  have : t * k * t⁻¹ * k⁻¹ = t * (k * t⁻¹ * k⁻¹) := by group
  rw [this]
  exact mul_mem ht ((mem_normalizer_iff.mp hkB _).mp (inv_mem ht))

theorem inf_le_oddCoreIn {A B : Subgroup G} (hA : A ∈ linkedClass Q) (hB : B ∈ linkedClass Q)
    (hne : A ≠ B) : twoPrimeLayerIn A ⊓ twoPrimeLayerIn B ≤ oddCoreIn (linkedLayer Q) :=
  le_oddCoreIn (normalIn_of_le_normalizer (inf_le_left.trans (twoPrimeLayerIn_le_linkedLayer hA))
      ((le_inf (hS.linkedLayer_le_normalizer hA) (hS.linkedLayer_le_normalizer hB)).trans
        (inf_normalizer_le_normalizer_inf _ _)))
    ((hS.odd_card_inf hA hB hne).of_dvd_nat
      (card_dvd_of_le (inf_le_inf (twoPrimeLayerIn_le A) (twoPrimeLayerIn_le B))))

theorem commute_layerBar {A B : Subgroup G} (hA : A ∈ linkedClass Q) (hB : B ∈ linkedClass Q)
    (hne : A ≠ B) : ∀ x ∈ layerBar (linkedLayer Q) A, ∀ y ∈ layerBar (linkedLayer Q) B,
      x * y = y * x := by
  rintro _ ⟨k, hk, rfl⟩ _ ⟨t, ht, rfl⟩
  have hc := hS.inf_le_oddCoreIn hB hA (Ne.symm hne)
    (commutator_mem_inf (hS.linked_of_mem hB hA) k hk t ht)
  have h1 : QuotientGroup.mk' (aschbacherThm5OddCore (linkedLayer Q)) (k * t * k⁻¹ * t⁻¹) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (mem_oddCoreIn_iff.mp hc).2
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  calc _ = (QuotientGroup.mk' _ k * QuotientGroup.mk' _ t * (QuotientGroup.mk' _ k)⁻¹ *
        (QuotientGroup.mk' _ t)⁻¹) * (QuotientGroup.mk' _ t * QuotientGroup.mk' _ k) := by group
    _ = _ := by rw [h1, one_mul]

omit [Finite G] hS in
theorem iSup_layerBar_eq_top {ι : Type*} (J : ι → Subgroup G)
    (hJ : ∀ A ∈ linkedClass Q, ∃ i, J i = A) :
    ⨆ i, layerBar (linkedLayer Q) (J i) = ⊤ := by
  set L := ⨆ i, layerBar (linkedLayer Q) (J i)
  set π := QuotientGroup.mk' (aschbacherThm5OddCore (linkedLayer Q))
  have h1 : linkedLayer Q ≤ (L.comap π).map (linkedLayer Q).subtype := by
    refine iSup₂_le fun A hA => ?_
    obtain ⟨i, rfl⟩ := hJ A hA
    intro x hx
    refine ⟨⟨x, twoPrimeLayerIn_le_linkedLayer hA hx⟩, ?_, rfl⟩
    exact le_iSup (fun i => layerBar (linkedLayer Q) (J i)) i ⟨_, hx, rfl⟩
  have h2 : L.comap π = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hyx⟩ := h1 x.2
    rwa [show y = x from Subtype.ext hyx] at hy
  rw [← map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) L, h2,
    map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem map_preimage_layerBar {h : G} (hh : h ∈ normalizer (linkedLayer Q : Set G))
    {A : Subgroup G} (hA : A ∈ linkedClass Q) :
    (aschbacherThm5Preimage (linkedLayer Q) (layerBar (linkedLayer Q) A)).map
        (MulAut.conj h).toMonoidHom =
      aschbacherThm5Preimage (linkedLayer Q)
        (layerBar (linkedLayer Q) (rightConjugate A h⁻¹)) := by
  have hh' : h⁻¹ ∈ normalizer (linkedLayer Q : Set G) := inv_mem hh
  have hA' := hS.rightConjugate_mem_linkedClass_of_mem_normalizer hh' hA
  rw [preimage_layerBar (twoPrimeLayerIn_le_linkedLayer hA),
    preimage_layerBar (twoPrimeLayerIn_le_linkedLayer hA'), Subgroup.map_sup,
    map_conj_eq_rightConjugate, map_conj_eq_rightConjugate, ← twoPrimeLayerIn_rightConjugate,
    ← oddCoreIn_rightConjugate, (rightConjugate_eq_self_iff _ _).mpr hh']

theorem mem_normalizer_of_centralizes {A : Subgroup G} (hA : A ∈ linkedClass Q) {t : G}
    (ht : aschbacherThm5Centralizes (aschbacherThm5Core (linkedLayer Q))
      (aschbacherThm5Preimage (linkedLayer Q) (layerBar (linkedLayer Q) A)) t) :
    t ∈ normalizer (A : Set G) ∧
      ∀ k ∈ twoPrimeLayerIn A, t * k * t⁻¹ * k⁻¹ ∈ oddCoreIn A := by
  have hAD := twoPrimeLayerIn_le_linkedLayer hA
  rw [preimage_layerBar hAD] at ht
  set P := twoPrimeLayerIn A ⊔ oddCoreIn (linkedLayer Q)
  have hc : ∀ a ∈ P, t⁻¹ * a⁻¹ * t * a ∈ oddCoreIn (linkedLayer Q) := ht
  have hP : ∀ a ∈ P, t⁻¹ * a * t ∈ P := by
    intro a ha
    have h1 := hc a⁻¹ (inv_mem ha)
    rw [inv_inv] at h1
    have : t⁻¹ * a * t = (t⁻¹ * a * t * a⁻¹) * a := by group
    rw [this]
    exact mul_mem (mem_sup_right h1) ha
  obtain ⟨E, hEK, hE, hE4⟩ := hS.four_of_mem hA
  have hEne : E ≠ ⊥ := fun h => by rw [h, card_bot] at hE4; norm_num at hE4
  obtain ⟨⟨u, huE⟩, hu1⟩ := ne_bot_iff_exists_ne_one.mp hEne
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have huK := hEK huE
  have hv : (t⁻¹ * u * t) ^ 2 = 1 := by
    rw [show t⁻¹ * u * t = t⁻¹ * u * t⁻¹⁻¹ by rw [inv_inv], conj_pow, hE u huE, mul_one,
      mul_inv_cancel]
  have hvA : t⁻¹ * u * t ∈ A :=
    mem_of_two_element_of_le_sup (twoPrimeLayerIn_le A) (odd_card_oddCoreIn _)
      (hAD.trans linkedLayer_le_normalizer_oddCoreIn) (hS.oddCoreIn_le_normalizer_of_mem hA)
      (hP u (mem_sup_left huK)) (k := 1) (by rw [pow_one]; exact hv)
  have hvAt : t⁻¹ * u * t ∈ rightConjugate A t := by
    rw [mem_rightConjugate_iff, show t * (t⁻¹ * u * t) * t⁻¹ = u by group]
    exact twoPrimeLayerIn_le A huK
  have hv1 : t⁻¹ * u * t ≠ 1 := by
    intro h
    apply hu1'
    rw [show u = t * (t⁻¹ * u * t) * t⁻¹ by group, h]
    group
  have heven : Even (Nat.card (A ⊓ rightConjugate A t : Subgroup G)) := by
    have hz : Nat.card (zpowers (t⁻¹ * u * t)) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hv hv1]
    exact even_iff_two_dvd.mpr (hz ▸ card_dvd_of_le ((zpowers_le).mpr ⟨hvA, hvAt⟩))
  have htN : t ∈ normalizer (A : Set G) := mem_normalizer_of_even_inf (hS.tight_of_mem hA) heven
  refine ⟨htN, fun k hk => ?_⟩
  have htK := normalizer_le_normalizer_twoPrimeLayerIn A htN
  have ha : t * k⁻¹ * t⁻¹ ∈ twoPrimeLayerIn A := (mem_normalizer_iff.mp htK _).mp (inv_mem hk)
  have h1 := hc (t * k⁻¹ * t⁻¹) (mem_sup_left ha)
  have h2 : t⁻¹ * (t * k⁻¹ * t⁻¹)⁻¹ * t * (t * k⁻¹ * t⁻¹) = (t * k * t⁻¹ * k⁻¹)⁻¹ := by group
  rw [h2] at h1
  have h3 : t * k * t⁻¹ * k⁻¹ ∈ oddCoreIn (linkedLayer Q) := by simpa using inv_mem h1
  have h4 : t * k * t⁻¹ * k⁻¹ ∈ twoPrimeLayerIn A :=
    mul_mem ((mem_normalizer_iff.mp htK k).mp hk) (inv_mem hk)
  have h5 : t * k * t⁻¹ * k⁻¹ ∈ twoPrimeLayerIn A ⊓ oddCoreIn (linkedLayer Q) := ⟨h4, h3⟩
  rw [inf_oddCoreIn_eq (hS.normalIn_linkedLayer hA), oddCoreIn_twoPrimeLayerIn] at h5
  exact h5

theorem coversLayer_of_centralizes {A : Subgroup G} (hA : A ∈ linkedClass Q) {t : G} {k : ℕ}
    (hk : t ^ (2 ^ k) = 1)
    (ht : aschbacherThm5Centralizes (aschbacherThm5Core (linkedLayer Q))
      (aschbacherThm5Preimage (linkedLayer Q) (layerBar (linkedLayer Q) A)) t) :
    CoversLayer (zpowers t) A := by
  obtain ⟨htA, hcA⟩ := hS.mem_normalizer_of_centralizes hA ht
  exact coversLayer_of_commutator (isPGroup_zpowers_of_pow_eq_one hk) ((zpowers_le).mpr htA)
    (zpowers_commutator_mem (normalizer_le_normalizer_twoPrimeLayerIn A htA)
      (normalizer_le_normalizer_oddCoreIn A htA) hcA)

omit [Finite G] hS in
theorem centralizer_zpowers_ne_top_of_not_mem_center {t : G} (ht : t ∉ center G) :
    centralizer (zpowers t : Set G) ≠ ⊤ := by
  intro htop
  apply ht
  rw [mem_center_iff]
  intro g
  have hg : g ∈ centralizer (zpowers t : Set G) := htop ▸ mem_top g
  exact (mem_centralizer_iff.mp hg t (mem_zpowers t)).symm

theorem mem_normalizer_of_centralizes_fusion {A B : Subgroup G} (hA : A ∈ linkedClass Q)
    (hB : B ∈ linkedClass Q) {t g : G} (htwo : ∃ k : ℕ, t ^ (2 ^ k) = 1) (hZ : t ∉ center G)
    (hti : aschbacherThm5Centralizes (aschbacherThm5Core (linkedLayer Q))
      (aschbacherThm5Preimage (linkedLayer Q) (layerBar (linkedLayer Q) A)) t)
    (htj : aschbacherThm5Centralizes (aschbacherThm5Core (linkedLayer Q))
      (aschbacherThm5Preimage (linkedLayer Q) (layerBar (linkedLayer Q) B)) (g⁻¹ * t * g)) :
    g ∈ normalizer (linkedLayer Q : Set G) := by
  obtain ⟨k, hk⟩ := htwo
  have hcA := hS.coversLayer_of_centralizes hA hk hti
  have hk' : (g⁻¹ * t * g) ^ (2 ^ k) = 1 := by
    rw [show g⁻¹ * t * g = g⁻¹ * t * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hk, mul_one,
      mul_inv_cancel]
  have hcB := hS.coversLayer_of_centralizes hB hk' htj
  have hz : rightConjugate (zpowers (g⁻¹ * t * g)) g⁻¹ = zpowers t := by
    rw [rightConjugate, inv_inv, MonoidHom.map_zpowers]
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hcB' : CoversLayer (zpowers t) (rightConjugate B g⁻¹) := by
    rw [← hz]
    exact coversLayer_rightConjugate_iff.mpr hcB
  obtain ⟨⟨a, rfl⟩, hQA⟩ := hA
  obtain ⟨⟨b, rfl⟩, hQB⟩ := hB
  rw [rightConjugate_mul] at hcB'
  have hmem : rightConjugate Q (b * g⁻¹) ∈ linkedClass Q := by
    rcases hS.star a (b * g⁻¹) _ (isPGroup_zpowers_of_pow_eq_one hk)
        (centralizer_zpowers_ne_top_of_not_mem_center hZ) hcA hcB' with h | h
    · rw [← h]
      exact ⟨⟨a, rfl⟩, hQA⟩
    · exact hS.mem_linkedClass_of_linked ⟨⟨a, rfl⟩, hQA⟩ h
  have h1 : Linked (rightConjugate Q 1) (rightConjugate Q (b * g⁻¹)) := by
    rw [rightConjugate_one]
    exact hmem.2
  have h2 : Linked (rightConjugate Q g) (rightConjugate Q b) := by
    have := linked_rightConjugate_iff (g := g) |>.mpr h1
    rwa [rightConjugate_mul, rightConjugate_mul, one_mul, inv_mul_cancel_right] at this
  have h3 : Linked (rightConjugate Q b) (rightConjugate Q 1) := by
    rw [rightConjugate_one]
    exact hQB.symm
  have h4 := hS.trans h2 h3
  rw [rightConjugate_one] at h4
  exact hS.mem_normalizer_linkedLayer_of_linked h4.symm

theorem le_inf_sup_of_covers {A X M : Subgroup G} (hA : A ∈ linkedClass Q) (hXM : X ≤ M)
    (hcov : ∀ a ∈ twoPrimeLayerIn A, ∃ x ∈ X, ∃ o ∈ oddCoreIn (linkedLayer Q), a = x * o) :
    twoPrimeLayerIn A ≤ (twoPrimeLayerIn A ⊓ M) ⊔ oddCoreIn A := by
  set K := twoPrimeLayerIn A
  set O := oddCoreIn (linkedLayer Q)
  have hKD : K ≤ linkedLayer Q := twoPrimeLayerIn_le_linkedLayer hA
  have hKO : K ≤ normalizer (O : Set G) := hKD.trans linkedLayer_le_normalizer_oddCoreIn
  have hOA : O ≤ normalizer (A : Set G) := hS.oddCoreIn_le_normalizer_of_mem hA
  have hAK : A ≤ normalizer (K : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_twoPrimeLayerIn A)
  have hOodd := odd_card_oddCoreIn (linkedLayer Q)
  set V := K ⊔ O
  have hVO : V ≤ normalizer (O : Set G) := sup_le hKO le_normalizer
  have hOn : (O.subgroupOf V).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hVO
  have h2 : ∀ u ∈ K, ∀ j : ℕ, u ^ (2 ^ j) = 1 → u ∈ (K ⊓ M) ⊔ oddCoreIn A := by
    intro u hu j hj
    obtain ⟨x, hxX, o, ho, hux⟩ := hcov u hu
    have huV : u ∈ V := mem_sup_left hu
    have hxV : x ∈ V := by
      have : x = u * o⁻¹ := by rw [hux]; group
      rw [this]
      exact mul_mem huV (mem_sup_right (inv_mem ho))
    have hπ : QuotientGroup.mk' (O.subgroupOf V) ⟨x, hxV⟩ =
        QuotientGroup.mk' (O.subgroupOf V) ⟨u, huV⟩ := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      show x⁻¹ * u ∈ O
      rw [hux, inv_mul_cancel_left]
      exact ho
    have hπu : QuotientGroup.mk' (O.subgroupOf V) ⟨x, hxV⟩ ^ (2 ^ j) = 1 := by
      rw [hπ, ← map_pow]
      have : (⟨u, huV⟩ : V) ^ (2 ^ j) = 1 := Subtype.ext (by simpa using hj)
      rw [this, map_one]
    obtain ⟨y, hy, ⟨i, hi⟩, hyπ⟩ := exists_two_element_pow _ hπu
    have hyX : (y : G) ∈ X := by
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
      simp only [SubgroupClass.coe_zpow]
      exact zpow_mem hxX n
    have hy2 : (y : G) ^ (2 ^ i) = 1 := by simpa using congrArg Subtype.val hi
    have hyK : (y : G) ∈ K :=
      mem_of_two_element_of_le_sup_of_le (twoPrimeLayerIn_le A) hAK hOodd hKO hOA y.2 hy2
    have hyu : (y : G)⁻¹ * u ∈ O := by
      have h := QuotientGroup.eq.mp (hyπ.trans hπ)
      exact h
    have hyuO : (y : G)⁻¹ * u ∈ oddCoreIn A := by
      have h : (y : G)⁻¹ * u ∈ K ⊓ O := mem_inf.mpr ⟨mul_mem (inv_mem hyK) hu, hyu⟩
      rwa [inf_oddCoreIn_eq (hS.normalIn_linkedLayer hA), oddCoreIn_twoPrimeLayerIn] at h
    have : u = y * ((y : G)⁻¹ * u) := by group
    rw [this]
    exact mul_mem (mem_sup_left ⟨hyK, hXM hyX⟩) (mem_sup_right hyuO)
  refine (le_oUpperTwoPrime_sup_oddCoreIn (isSemisimpleQ_twoPrimeLayerIn A)).trans
    (sup_le ?_ ?_)
  · rw [oUpperTwoPrime, closure_le]
    rintro u ⟨hu, j, hj⟩
    exact h2 u hu j hj
  · rw [oddCoreIn_twoPrimeLayerIn]
    exact le_sup_right

end MainSetting

@[expose] def NormalInConjNormalizer (Q : Subgroup G) : Prop :=
  ∀ (g : G) (A : Subgroup G), A ∈ linkedClass Q →
    twoPrimeLayerIn A ≤ (twoPrimeLayerIn A ⊓
      rightConjugate (normalizer (linkedLayer Q : Set G)) g) ⊔ oddCoreIn A →
    NormalIn (twoPrimeLayerIn A ⊓ rightConjugate (normalizer (linkedLayer Q : Set G)) g)
      (twoPrimeLayerIn (rightConjugate (normalizer (linkedLayer Q : Set G)) g))

namespace MainSetting

variable {Q : Subgroup G} (hS : MainSetting Q)
include hS

theorem mem_normalizer_of_covers (hN : NormalInConjNormalizer Q) {A : Subgroup G}
    (hA : A ∈ linkedClass Q) (g : G) (X : Subgroup G)
    (hX : X ≤ (normalizer (linkedLayer Q : Set G)).map (MulAut.conj g⁻¹).toMonoidHom)
    (hcov : ∀ a ∈ aschbacherThm5Preimage (linkedLayer Q) (layerBar (linkedLayer Q) A),
      ∃ x ∈ X, ∃ o ∈ aschbacherThm5Core (linkedLayer Q), a = x * o) :
    g ∈ normalizer (linkedLayer Q : Set G) := by
  set M := rightConjugate (normalizer (linkedLayer Q : Set G)) g
  have hXM : X ≤ M := hX
  have hKD := twoPrimeLayerIn_le_linkedLayer hA
  have hcov' : ∀ a ∈ twoPrimeLayerIn A, ∃ x ∈ X, ∃ o ∈ oddCoreIn (linkedLayer Q), a = x * o :=
    fun a ha => hcov a (by rw [preimage_layerBar hKD]; exact mem_sup_left ha)
  have hcover := hS.le_inf_sup_of_covers hA hXM hcov'
  have hNX₀ := hN g A hA hcover
  have hX₀s : IsSemisimpleQ (twoPrimeLayerIn A ⊓ M) :=
    isSemisimpleQ_of_le_sup inf_le_left (by rw [oddCoreIn_twoPrimeLayerIn]; exact hcover)
      (isSemisimpleQ_twoPrimeLayerIn A)
  have hKO : twoPrimeLayerIn A ≤ normalizer (oddCoreIn A : Set G) :=
    (twoPrimeLayerIn_le A).trans (normalIn_le_normalizer (oddCoreIn_normalIn A))
  have hX₀4 : HasFourGroup (twoPrimeLayerIn A ⊓ M) := by
    obtain ⟨E, hEK, hE, hE4⟩ := hS.four_of_mem hA
    exact HasFourGroup.of_le_sup (odd_card_oddCoreIn A) (inf_le_left.trans hKO) (hEK.trans hKO)
      (hEK.trans hcover) hE hE4
  have hMD : M = normalizer (rightConjugate (linkedLayer Q) g : Set G) :=
    AschbacherTheorem3.rightConjugate_normalizer _ g
  have hDM : NormalIn (rightConjugate (linkedLayer Q) g) M := by
    rw [hMD]
    exact normalIn_of_le_normalizer le_normalizer le_rfl
  refine mem_normalizer_linkedLayer_of_subset fun B hB => ?_
  obtain ⟨⟨a, rfl⟩, hQA⟩ := hA
  obtain ⟨⟨b, rfl⟩, hQB⟩ := hB
  rw [rightConjugate_mul]
  have hYD : NormalIn (twoPrimeLayerIn (rightConjugate Q (b * g)))
      (rightConjugate (linkedLayer Q) g) := by
    rw [← rightConjugate_mul, twoPrimeLayerIn_rightConjugate]
    exact (normalIn_map_iff (MulAut.conj g⁻¹).injective).mpr
      (hS.normalIn_linkedLayer ⟨⟨b, rfl⟩, hQB⟩)
  have hYsub := isSubnormal_quotImage_of_subgroupOf (isSubnormal_subgroupOf_of_normalIn hYD hDM)
  have hY4 := hS.four_rightConjugate (b * g)
  rcases eq_or_normalizes_of_quotImage (rightConjugate_tightlyEmbedded Q hS.tight a)
      (rightConjugate_tightlyEmbedded Q hS.tight (b * g)) (eq_of_even_inf_rightConjugate hS.tight)
      (hS.caseI (b * g) a) (hS.caseI a (b * g)) (inf_le_left.trans (twoPrimeLayerIn_le _))
      (twoPrimeLayerIn_le _) inf_le_right (hYD.1.trans hDM.1) (isSubnormal_quotImage hNX₀)
      (layer_quotImage_eq_top hNX₀ hX₀s) hYsub hX₀4 hY4 with h | h
  · rw [← h]
    exact ⟨⟨a, rfl⟩, hQA⟩
  · exact hS.mem_linkedClass_of_linked ⟨⟨a, rfl⟩, hQA⟩ ⟨h.2, h.1⟩

end MainSetting

end CFSG.ComponentClassification.Asc75T4
