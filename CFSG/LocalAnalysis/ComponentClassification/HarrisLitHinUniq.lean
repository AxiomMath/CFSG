module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorBasic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinAut

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def NoCommQS {G : Type*} [Group G] (C L : Subgroup G) : Prop :=
  ∀ N : Subgroup G, N ≤ C → (N.subgroupOf C).IsSubnormal → IsQuasisimple ↥N →
    2 ∣ Nat.card N → (∀ n ∈ N, ∀ l ∈ L, n * l = l * n) → False

section Layer

variable {Y : Type} [Group Y] [Finite Y] {C : Subgroup Y} {p m : ℕ}

theorem noCommQS_layerIn (hL : Blueprint.LieModel ↥(GSThmB.layerIn C) .PSL 2 p m) :
    NoCommQS C (GSThmB.layerIn C) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro N hNC hsn hq h2 hcomm
  set N' := N.subgroupOf C with hN'
  have eN : ↥N' ≃* ↥N := subgroupOfEquivOfLe hNC
  have hq' : IsQuasisimple ↥N' := LocalCores.isQuasisimple_of_mulEquiv eN.symm hq
  have hp : IsPComponent 2 N' := by
    refine LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 ⟨hq', hsn⟩
      fun hle => ?_
    have h2' : 2 ∣ Nat.card ↥N' := by rw [Nat.card_congr eN.toEquiv]; exact h2
    exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl
      (h2'.trans (Subgroup.card_dvd_of_le hle)) (pPrimeCore_coprime_card (p := 2) (G := ↥C))
  have hle : N' ≤ pLayer ↥C 2 := le_sSup hp
  have hZ := center_pLayer_eq_bot hL
  have h1 : ∀ n ∈ N, n = 1 := by
    intro n hn
    have hnC : n ∈ C := hNC hn
    have hnL : (⟨n, hnC⟩ : ↥C) ∈ pLayer ↥C 2 := hle (mem_subgroupOf.mpr hn)
    have hcen : (⟨⟨n, hnC⟩, hnL⟩ : ↥(pLayer ↥C 2)) ∈ center ↥(pLayer ↥C 2) := by
      rw [mem_center_iff]
      intro y
      apply Subtype.ext
      apply Subtype.ext
      exact (hcomm n hn _ ⟨_, y.2, rfl⟩).symm
    rw [hZ, mem_bot] at hcen
    exact congrArg (fun z : ↥(pLayer ↥C 2) => ((z : ↥C) : Y)) hcen
  have hnt := LocalCores.isQuasisimple_nontrivial hq
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := hnt.exists_pair_ne
  apply hab
  apply Subtype.ext
  change a = b
  rw [h1 a ha, h1 b hb]

end Layer

section Transport

variable {G G' : Type*} [Group G] [Group G'] {C L : Subgroup G}

theorem map_subgroupOf_equivMap (f : G →* G') (hf : Function.Injective f) {N : Subgroup G}
    (hNC : N ≤ C) :
    (N.subgroupOf C).map (C.equivMapOfInjective f hf).toMonoidHom =
      (N.map f).subgroupOf (C.map f) := by
  ext ⟨x, hx⟩
  constructor
  · rintro ⟨⟨c, hc⟩, hcN, hcx⟩
    rw [mem_subgroupOf]
    have : f c = x := congrArg Subtype.val hcx
    change x ∈ N.map f
    rw [← this]
    exact ⟨c, mem_subgroupOf.mp hcN, rfl⟩
  · intro h
    rw [mem_subgroupOf] at h
    obtain ⟨n, hn, rfl⟩ := h
    exact ⟨⟨n, hNC hn⟩, mem_subgroupOf.mpr hn, rfl⟩

theorem NoCommQS.map (f : G →* G') (hf : Function.Injective f) (h : NoCommQS C L) :
    NoCommQS (C.map f) (L.map f) := by
  intro N' hN'C hsn hq h2 hcomm
  set N := N'.comap f with hNdef
  have hN'r : N' ≤ f.range := hN'C.trans (map_le_range f C)
  have hNN' : N.map f = N' := map_comap_eq_self hN'r
  have hNC : N ≤ C := by
    intro x hx
    obtain ⟨c, hc, hcx⟩ := hN'C hx
    rw [← hf hcx]
    exact hc
  have eN : ↥N ≃* ↥N' := (N.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hNN')
  refine h N hNC ?_ (LocalCores.isQuasisimple_of_mulEquiv eN.symm hq)
    (by rw [Nat.card_congr eN.toEquiv]; exact h2) ?_
  · have hcomap : (N'.subgroupOf (C.map f)).comap (C.equivMapOfInjective f hf).toMonoidHom =
        N.subgroupOf C := by
      ext ⟨x, hx⟩
      simp only [mem_comap, mem_subgroupOf, MulEquiv.coe_toMonoidHom, hNdef]
      rfl
    rw [← hcomap]
    exact hsn.comap _
  · intro n hn l hl
    apply hf
    rw [map_mul, map_mul]
    exact hcomm (f n) hn (f l) ⟨l, hl, rfl⟩

theorem NoCommQS.of_map (f : G →* G') (hf : Function.Injective f)
    (h : NoCommQS (C.map f) (L.map f)) : NoCommQS C L := by
  intro N hNC hsn hq h2 hcomm
  have eN : ↥N ≃* ↥(N.map f) := N.equivMapOfInjective f hf
  refine h (N.map f) (map_mono hNC) ?_ (LocalCores.isQuasisimple_of_mulEquiv eN hq)
    (by rw [← Nat.card_congr eN.toEquiv]; exact h2) ?_
  · rw [← map_subgroupOf_equivMap f hf hNC]
    exact hsn.map (C.equivMapOfInjective f hf).surjective
  · rintro _ ⟨n, hn, rfl⟩ _ ⟨l, hl, rfl⟩
    rw [← map_mul, ← map_mul, hcomm n hn l hl]

theorem map_conj_fixedPoints {G : Type} [Group G] (hZ : center G = ⊥) (α : MulAut G) :
    (fixedPoints α).map (MulAut.conj : G →* MulAut G) =
      (MulAut.conj : G →* MulAut G).range ⊓ centralizer {α} := by
  ext σ
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, rfl⟩, (conj_mem_centralizer_iff hZ α y).mpr hy⟩
  · rintro ⟨⟨y, rfl⟩, hσ⟩
    exact ⟨y, (conj_mem_centralizer_iff hZ α y).mp hσ, rfl⟩

end Transport

section Lift

variable {S : Type*} [Group S] (Z : Subgroup S) [Z.Normal]

theorem conj_mem_map_fixed (hZ : Z ≤ center S) (φ : MulAut S)
    (hφZ : Z.map φ.toMonoidHom = Z) {x h : S ⧸ Z}
    (hx : x ∈ fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z φ hφZ))
    (hh : h ∈ (fixedSubgroup φ).map (QuotientGroup.mk' Z)) :
    x * h * x⁻¹ ∈ (fixedSubgroup φ).map (QuotientGroup.mk' Z) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z x
  obtain ⟨k, hk, rfl⟩ := hh
  have hg : QuotientGroup.mk' Z (φ g) = QuotientGroup.mk' Z g := by
    rw [← CatalogueBFixedCentralQuotient.onQuotient_mk Z φ hφZ g]
    exact hx
  obtain ⟨z, hz, hgz⟩ : ∃ z ∈ Z, φ g = g * z := by
    refine ⟨g⁻¹ * φ g, ?_, by group⟩
    have := (QuotientGroup.eq (s := Z)).mp hg.symm
    exact this
  have hzc := mem_center_iff.mp (hZ hz)
  refine ⟨g * k * g⁻¹, ?_, by simp⟩
  have hk' : φ k = k := hk
  change φ (g * k * g⁻¹) = g * k * g⁻¹
  rw [map_mul, map_mul, map_inv, hgz, hk']
  calc g * z * k * (g * z)⁻¹ = g * (z * k * z⁻¹) * g⁻¹ := by group
    _ = g * k * g⁻¹ := by rw [← hzc k, mul_inv_cancel_right]

theorem false_of_noCommQS_lift (hZ : Z ≤ center S) (φ : MulAut S)
    (hφZ : Z.map φ.toMonoidHom = Z) {X : Subgroup (S ⧸ Z)}
    (hU : NoCommQS (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z φ hφZ)) X)
    {Y : Subgroup S} (hYX : ∀ x ∈ X, ∃ y ∈ Y, QuotientGroup.mk' Z y = x) {N : Subgroup S}
    (hNφ : N ≤ fixedSubgroup φ) (hnorm : ∀ g ∈ fixedSubgroup φ, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hq : IsQuasisimple ↥N) (hNZ : N ⊓ Z = ⊥) (h2 : 2 ∣ Nat.card N)
    (hcomm : ∀ n ∈ N, ∀ y ∈ Y, n * y = y * n) : False := by
  set π := QuotientGroup.mk' Z with hπ
  set F := fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z φ hφZ) with hF
  set M := (fixedSubgroup φ).map π with hM
  have hfix : ∀ g ∈ fixedSubgroup φ, π g ∈ F := by
    intro g hg
    change CatalogueBFixedCentralQuotient.onQuotient Z φ hφZ (π g) = π g
    rw [hπ, CatalogueBFixedCentralQuotient.onQuotient_mk]
    exact congrArg _ hg
  have hMF : M ≤ F := by
    rintro _ ⟨g, hg, rfl⟩
    exact hfix g hg
  have hNM : N.map π ≤ M := map_mono hNφ
  have hinj : Function.Injective (π.comp N.subtype) := by
    rw [injective_iff_map_eq_one]
    intro n hn
    have hnZ : (n : S) ∈ Z := (QuotientGroup.eq_one_iff _).mp hn
    have : (n : S) ∈ N ⊓ Z := ⟨n.2, hnZ⟩
    rw [hNZ, mem_bot] at this
    exact Subtype.ext this
  have hrange : (π.comp N.subtype).range = N.map π := by
    rw [MonoidHom.range_comp, range_subtype]
  let eN : ↥N ≃* ↥(N.map π) := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  refine hU (N.map π) (hNM.trans hMF) ?_ (LocalCores.isQuasisimple_of_mulEquiv eN hq)
    (by rw [← Nat.card_congr eN.toEquiv]; exact h2) ?_
  ·
    have hMn : (M.subgroupOf F).Normal := by
      refine ⟨fun h hh x => ?_⟩
      rw [mem_subgroupOf] at hh ⊢
      exact conj_mem_map_fixed Z hZ φ hφZ x.2 hh
    have hNn : (((N.map π).subgroupOf F).subgroupOf (M.subgroupOf F)).Normal := by
      refine ⟨fun h hh x => ?_⟩
      rw [mem_subgroupOf, mem_subgroupOf] at hh ⊢
      obtain ⟨n, hn, hnh⟩ := hh
      have hx : ((x : ↥F) : S ⧸ Z) ∈ M := mem_subgroupOf.mp x.2
      obtain ⟨g, hg, hgx⟩ := hx
      refine ⟨g * n * g⁻¹, hnorm g hg n hn, ?_⟩
      simp only [map_mul, map_inv, hnh, hgx, Subgroup.coe_mul, Subgroup.coe_inv]
    exact IsSubnormal.step _ _ (fun x hx => by
      rw [mem_subgroupOf] at hx ⊢
      exact hNM hx) hMn.isSubnormal hNn
  · rintro _ ⟨n, hn, rfl⟩ x hx
    obtain ⟨y, hy, rfl⟩ := hYX x hx
    rw [← map_mul, ← map_mul, hcomm n hn y hy]

end Lift

section Socle

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem fixed_component_of_socle_noComm {A : Type*} [Group A] {W : Subgroup A} [W.Normal]
    (hCW : centralizer (W : Set A) = ⊥) {P : Type} [Group P] (θ : W ≃* P) (hZ : center P = ⊥)
    {a : A} {L : Subgroup A} (hL : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}))
    (hU : NoCommQS (W ⊓ centralizer {a}) L) :
    ∃ (ρ : A →* MulAut P) (X : Subgroup P), Function.Injective ρ ∧ inner P ≤ ρ.range ∧
      CFSG.Assembly.IsComponentOf X (fixedSubgroup (ρ a)) ∧ L.map ρ = X.map MulAut.conj ∧
      Nonempty (L ≃* X) ∧ NoCommQS (fixedSubgroup (ρ a)) X := by
  have hcj := OddClassSelector.conj_injective hZ
  obtain ⟨ρ, hinj, hρW, -, -⟩ := OutcomeLocal.socle_extension hCW θ hZ
  obtain ⟨hWimg, hCWimg, -⟩ := OutcomeLocal.socle_images hinj θ hρW a
  have hL₁ := SymmetricLocal.isComponentOf_map_of_injective ρ hinj hL
  rw [hCWimg] at hL₁
  obtain ⟨hX, hXmap⟩ := OddClassSelector.isComponentOf_comap_conj hcj hL₁
  refine ⟨ρ, (L.map ρ).comap MulAut.conj, hinj, ?_, hX, hXmap.symm, ⟨?_⟩, ?_⟩
  · rw [← hWimg]
    exact Subgroup.map_le_range ρ W
  · exact (L.equivMapOfInjective ρ hinj).trans ((MulEquiv.subgroupCongr hXmap.symm).trans
      (((L.map ρ).comap MulAut.conj).equivMapOfInjective _ hcj).symm)
  · have h1 := hU.map ρ hinj
    rw [hCWimg, ← hXmap] at h1
    have hfix : (fixedSubgroup (ρ a)).map (MulAut.conj : P →* MulAut P) =
        inner P ⊓ centralizer {ρ a} := map_conj_fixedPoints hZ (ρ a)
    rw [← hfix] at h1
    exact h1.of_map _ hcj

end Socle

end CFSG.ComponentClassification.HarrisLit.Hin
