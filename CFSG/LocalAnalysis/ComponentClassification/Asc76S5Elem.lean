module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Rep

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G]

theorem centralizer_singleton_le_normalizer {K T : Subgroup G} (hK : TightlyEmbedded K)
    (hTK : T ≤ K) (hT : IsPGroup 2 T) {t : G} (ht : t ∈ T) (ht1 : t ≠ 1) :
    centralizer ({t} : Set G) ≤ normalizer (K : Set G) := by
  have hzT : zpowers t ≤ T := (zpowers_le).mpr ht
  have hzeven : Even (Nat.card (zpowers t)) :=
    even_card_of_isPGroup (hT.to_le hzT) fun h => ht1 ((zpowers_eq_bot).mp h)
  intro c hc
  have hc' : c ∈ centralizer (zpowers t : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hh
    have h1 : Commute t c := (mem_centralizer_singleton_iff.mp hc).symm
    exact (h1.zpow_left n).eq
  exact normalizer_le_normalizer_of_tightlyEmbedded hK (hzT.trans hTK) hzeven
    (centralizer_le_normalizer _ hc')

theorem inf_centralizer_singleton_eq {K R T : Subgroup G} (hK : TightlyEmbedded K) {g : G}
    (hg : g ∉ normalizer (K : Set G))
    (hT : IsSylowOf 2 T (rightConjugate K g ⊓ normalizer (K : Set G)))
    (hR : IsSylowOf 2 R K) (hTR : T ≤ normalizer (R : Set G)) {t : G} (ht : t ∈ T)
    (ht1 : t ≠ 1) : R ⊓ centralizer ({t} : Set G) = R ⊓ centralizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT1 : T ≠ ⊥ := fun h => ht1 (by rw [h] at ht; exact mem_bot.mp ht)
  have hle : R ⊓ centralizer (T : Set G) ≤ R ⊓ centralizer ({t} : Set G) :=
    inf_le_inf_left R (centralizer_le (Set.singleton_subset_iff.mpr ht))
  have hCN : centralizer ({t} : Set G) ≤ normalizer (rightConjugate K g : Set G) :=
    centralizer_singleton_le_normalizer (tightlyEmbedded_rightConjugate hK g)
      (hT.le.trans inf_le_left) hT.isPGroup ht ht1
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 (K ⊓ normalizer (rightConjugate K g : Set G))
  have hcard := card_eq_card_of_overlap hK hg hT hT1 hP
  have h1 : Nat.card (R ⊓ centralizer ({t} : Set G) : Subgroup G) ≤ Nat.card P :=
    card_le_of_isSylowOf hP (le_inf (inf_le_left.trans hR.le) (inf_le_right.trans hCN))
      (hR.isPGroup.to_le inf_le_left)
  obtain ⟨e⟩ := inf_centralizer_mulEquiv_of_tightlyEmbedded hK hg hT hT1 hR hTR
  have h2 : Nat.card (R ⊓ centralizer (T : Set G) : Subgroup G) = Nat.card T :=
    Nat.card_congr e.toEquiv
  exact (eq_of_le_of_card_ge hle (by omega)).symm

theorem exists_mul_mem_inf_centralizer {A R T : Subgroup G} {g : G}
    (hK : TightlyEmbedded (centralizer (A : Set G)))
    (hg : g ∉ normalizer (centralizer (A : Set G) : Set G))
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g ⊓
      normalizer (centralizer (A : Set G) : Set G)))
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hTR : T ≤ normalizer (R : Set G))
    (hTAK : T ≤ A ⊔ centralizer (A : Set G)) {u : G} (hu : u ∈ T) :
    ∃ a ∈ A, ∃ r ∈ R ⊓ centralizer (T : Set G), u = a * r := by
  by_cases hu1 : u = 1
  · exact ⟨1, one_mem _, 1, one_mem _, by rw [hu1, mul_one]⟩
  obtain ⟨m, hm⟩ := hT.isPGroup ⟨u, hu⟩
  have hm' : u ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  obtain ⟨a, ha, r, hr, hur⟩ := exists_mul_of_mem_sup_centralizer hR (hTAK hu) (hTR hu) hm'
  refine ⟨a, ha, r, ?_, hur⟩
  rw [← inf_centralizer_singleton_eq hK hg hT hR hTR hu hu1]
  refine ⟨hr, ?_⟩
  show r ∈ centralizer ({u} : Set G)
  rw [mem_centralizer_singleton_iff, hur]
  have hc : Commute a r := commute_of_mem_centralizer ha (hR.le hr)
  calc r * (a * r) = a * r * r := by rw [← mul_assoc, ← hc.eq]
    _ = a * r * r := rfl

theorem isSylowOf_of_le_sup_centralizer {A R T : Subgroup G} {g : G}
    (hK : TightlyEmbedded (centralizer (A : Set G)))
    (hg : g ∉ normalizer (centralizer (A : Set G) : Set G))
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g ⊓
      normalizer (centralizer (A : Set G) : Set G)))
    (hT1 : T ≠ ⊥) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hTR : T ≤ normalizer (R : Set G)) (hTAK : T ≤ A ⊔ centralizer (A : Set G))
    (hCn : ((R ⊓ centralizer (T : Set G)).subgroupOf R).Normal) :
    IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnot
  set K := centralizer (A : Set G) with hKdef
  set C := R ⊓ centralizer (T : Set G) with hCdef
  have hnoc : ∀ u ∈ T, u ≠ 1 → ¬ R ≤ centralizer ({u} : Set G) := fun u hu hu1 hRu =>
    hnot (isSylowOf_of_le_centralizer hK hg hT hR hu hu1 hRu)
  have hex : ∀ u : T, ∃ r : C, (u : G) * (r : G)⁻¹ ∈ A := by
    intro u
    obtain ⟨a, ha, r, hr, hur⟩ := exists_mul_mem_inf_centralizer hK hg hT hR hTR hTAK u.2
    exact ⟨⟨r, hr⟩, by rw [hur, mul_inv_cancel_right]; exact ha⟩
  choose f hf using hex
  have hfinj : Function.Injective f := by
    intro u u' huu'
    have h1 := hf u
    have h2 := hf u'
    rw [huu'] at h1
    set r : G := (f u' : G) with hr
    have hrK : r ∈ K := (f u').2.1 |> hR.le
    have hmem : (u : G)⁻¹ * u' ∈ A := by
      have h3 := A.mul_mem (A.inv_mem h1) h2
      have h4 : ((u : G) * r⁻¹)⁻¹ * ((u' : G) * r⁻¹) = r * ((u : G)⁻¹ * u') * r⁻¹ := by group
      rw [h4] at h3
      have hc : Commute (r * ((u : G)⁻¹ * u') * r⁻¹) r :=
        commute_of_mem_centralizer h3 hrK
      have h5 : r * ((u : G)⁻¹ * u') * r⁻¹ = (u : G)⁻¹ * u' := by
        have := hc.eq
        calc r * ((u : G)⁻¹ * u') * r⁻¹ = r⁻¹ * (r * (r * ((u : G)⁻¹ * u') * r⁻¹)) := by group
          _ = r⁻¹ * (r * ((u : G)⁻¹ * u') * r⁻¹ * r) := by rw [this]
          _ = (u : G)⁻¹ * u' := by group
      rwa [h5] at h3
    by_contra hne
    have hne' : (u : G)⁻¹ * u' ≠ 1 := by
      intro h
      apply hne
      exact Subtype.ext (inv_mul_eq_one.mp h)
    refine hnoc _ (T.mul_mem (T.inv_mem u.2) u'.2) hne' fun x hx => ?_
    rw [mem_centralizer_singleton_iff]
    exact ((commute_of_mem_centralizer hmem (hR.le hx)).eq).symm
  obtain ⟨e⟩ := inf_centralizer_mulEquiv_of_tightlyEmbedded hK hg hT hT1 hR hTR
  have hcardC : Nat.card T = Nat.card C := (Nat.card_congr e.toEquiv).symm
  have hfbij : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr ⟨hfinj, hcardC⟩
  have hRn : Group.IsNilpotent R := hR.isPGroup.isNilpotent
  have hCR : C ≤ R := inf_le_left
  have hC1 : C.subgroupOf R ≠ ⊥ := by
    intro h
    have hCb : C = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hCR hx⟩ : R) ∈ C.subgroupOf R := hx
      rw [h, mem_bot] at this
      exact mem_bot.mpr (congrArg Subtype.val this)
    have h1 : Nat.card C = 1 := by rw [hCb, card_bot]
    rw [← hcardC] at h1
    exact hT1 (card_eq_one.mp h1)
  have hz := Group.IsNilpotent.inf_center_ne_bot_of_normal hC1
  obtain ⟨⟨z, hzmem⟩, hz1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hz
  have hz1 : z ≠ 1 := fun h => hz1' (Subtype.ext h)
  have hzC : (z : R).val ∈ C := mem_subgroupOf.mp hzmem.1
  obtain ⟨u₁, hu₁⟩ := hfbij.2 ⟨(z : R), hzC⟩
  obtain ⟨u₀, hu₀⟩ := hfbij.2 1
  have hcen : ∀ u : T, (u : G) ≠ 1 → (∀ x ∈ R, x * (f u : G) = (f u : G) * x) → False := by
    intro u hu1 hfz
    refine hnoc u u.2 hu1 fun x hx => ?_
    rw [mem_centralizer_singleton_iff]
    obtain ⟨a, ha', hu⟩ : ∃ a ∈ A, (u : G) = a * (f u : G) :=
      ⟨_, hf u, (inv_mul_cancel_right (u : G) (f u : G)).symm⟩
    rw [hu]
    have hca : Commute a x := commute_of_mem_centralizer ha' (hR.le hx)
    calc x * (a * (f u : G)) = a * (x * (f u : G)) := by rw [← mul_assoc, ← hca.eq, mul_assoc]
      _ = a * ((f u : G) * x) := by rw [hfz x hx]
      _ = a * (f u : G) * x := (mul_assoc _ _ _).symm
  by_cases hu₁1 : (u₁ : G) = 1
  · have hu₀1 : (u₀ : G) ≠ 1 := by
      intro h
      have : u₀ = u₁ := Subtype.ext (h.trans hu₁1.symm)
      rw [this, hu₁] at hu₀
      apply hz1
      have h2 : ((⟨(z : G), hzC⟩ : C) : G) = 1 := by rw [hu₀]; rfl
      exact Subtype.ext h2
    refine hcen u₀ hu₀1 fun x hx => ?_
    rw [hu₀]
    simp
  · refine hcen u₁ hu₁1 fun x hx => ?_
    rw [hu₁]
    have h := congrArg Subtype.val (mem_center_iff.mp hzmem.2 ⟨x, hx⟩)
    simpa using h

end CFSG.ComponentClassification.Asc76.Sec5
