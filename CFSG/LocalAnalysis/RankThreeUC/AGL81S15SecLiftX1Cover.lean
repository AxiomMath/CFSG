module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecLiftX1Lift
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecLiftX1Setting

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeUC

private theorem surjective_mk_comp_inclusion {G : Type} [Group G] {A B E : Subgroup G}
    [(B.subgroupOf A).Normal] [IsSimpleGroup (↥A ⧸ B.subgroupOf A)] (hEA : E ≤ A)
    (hEn : ∀ a ∈ A, ∀ e ∈ E, a * e * a⁻¹ ∈ E) (hEB : ¬ E ≤ B) :
    Function.Surjective ((QuotientGroup.mk' (B.subgroupOf A)).comp (Subgroup.inclusion hEA)) := by
  have hn : (E.subgroupOf A).Normal := ⟨fun n hn a => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hEn a a.2 n hn⟩
  have hR : ((QuotientGroup.mk' (B.subgroupOf A)).comp (Subgroup.inclusion hEA)).range =
      (E.subgroupOf A).map (QuotientGroup.mk' (B.subgroupOf A)) := by
    ext y
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨Subgroup.inclusion hEA e, Subgroup.mem_subgroupOf.2 e.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, Subgroup.mem_subgroupOf.1 ha⟩, rfl⟩
  rcases (hn.map _ (QuotientGroup.mk'_surjective (B.subgroupOf A))).eq_bot_or_eq_top with h | h
  · refine absurd (fun e he => ?_) hEB
    have h1 : QuotientGroup.mk' (B.subgroupOf A) ⟨e, hEA he⟩ ∈
        (E.subgroupOf A).map (QuotientGroup.mk' (B.subgroupOf A)) :=
      ⟨⟨e, hEA he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    exact h1
  · rw [← MonoidHom.range_eq_top, hR, h]

variable {X : Type} [Group X] [Finite X]

theorem le_gnLayerPre_of_isComponentOf {T L : Subgroup X}
    (h : CFSG.Open.IsComponentOf (L.map (toStar T)) ⊤) : L ≤ gnLayerPre T :=
  fun _ hx => Subgroup.mem_comap.2 (le_sSup (show L.map (toStar T) ∈
    {K | CFSG.Open.IsComponentOf K ⊤} from h) (Subgroup.mem_map_of_mem _ hx))

theorem gnCoverP_sup_of_normal {T T₁ T₂ L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hX : GNSetting X T) (hcomp : GNYComponent T T₁ T₂ Ls) (hlift : LiftOf T L Ls)
    (hLn : L.Normal) :
    GNCoverP (T.subgroupOf (L ⊔ T)) (T₁.subgroupOf (L ⊔ T)) (T₂.subgroupOf (L ⊔ T)) := by
  intro p hp hp2 A B _ _ _ _ hAB hpd
  have hgn₁ := gnSetting_sup_of_normal hX hLn
  have hle := le_gnLayerPre_of_isComponentOf (isComponentOf_map_toStar_subgroupOf le_sup_right
    le_sup_left hLn hgn₁ hlift.1 (not_le_gnC_of_liftOf hcomp.1 hlift))
  haveI := hLn
  obtain ⟨k, hk⟩ := relIndex_two_pow_of_sup_eq_top hgn₁.sylow.2.1
    (Subgroup.normal_subgroupOf : (L.subgroupOf (L ⊔ T)).Normal) (sup_subgroupOf_sup_eq_top L T) A
  have h1 : B.relIndex A ∣ (L.subgroupOf (L ⊔ T) ⊓ A).relIndex A :=
    Subgroup.relIndex_dvd_of_le_left A fun x hx => hAB ⟨hx.2, hle hx.1⟩
  rw [hk] at h1
  exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
    (hp.dvd_of_dvd_pow (hpd.trans h1))) hp2

theorem gnCoverSec_sup_of_normal {T T₁ T₂ L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hX : GNSetting X T) (hT₁ : T₁ ≤ CFSG.Quasithin.omegaOneCenterOf T)
    (hcomp : GNYComponent T T₁ T₂ Ls) (hlift : LiftOf T L Ls) (hLn : L.Normal) :
    GNCoverSec (T.subgroupOf (L ⊔ T)) (T₁.subgroupOf (L ⊔ T)) (T₂.subgroupOf (L ⊔ T)) := by
  intro S _ hS hns
  obtain ⟨B, A, hBn, -, -, -, hsimp, ⟨e⟩⟩ := hS
  haveI := hBn
  haveI := hLn
  have hgn₁ := gnSetting_sup_of_normal hX hLn
  have hDB : ¬ A ⊓ L.subgroupOf (L ⊔ T) ≤ B := by
    intro hD
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 (↥A ⧸ B.subgroupOf A) := by
      intro g
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
      obtain ⟨k, hk⟩ := exists_pow_two_pow_mem_of_mem_normal_sup hLn hX.sylow.2.1 (a : ↥(L ⊔ T)).2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      refine hD (Subgroup.mem_inf.2 ⟨(a ^ 2 ^ k).2, ?_⟩)
      rw [Subgroup.mem_subgroupOf]
      exact hk
    haveI := hp.isNilpotent
    exact hns (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  have hnD : ∀ a ∈ A, ∀ d ∈ A ⊓ L.subgroupOf (L ⊔ T), a * d * a⁻¹ ∈ A ⊓ L.subgroupOf (L ⊔ T) :=
    fun a ha d hd => ⟨A.mul_mem (A.mul_mem ha hd.1) (A.inv_mem ha),
      (Subgroup.normal_subgroupOf : (L.subgroupOf (L ⊔ T)).Normal).conj_mem d hd.2 a⟩
  set gD := e.toMonoidHom.comp ((QuotientGroup.mk' (B.subgroupOf A)).comp
    (Subgroup.inclusion (inf_le_left : A ⊓ L.subgroupOf (L ⊔ T) ≤ A))) with hgD
  have hgDs : Function.Surjective gD :=
    e.surjective.comp (surjective_mk_comp_inclusion inf_le_left hnD hDB)
  by_cases hDC : A ⊓ L.subgroupOf (L ⊔ T) ⊓ gnC (T.subgroupOf (L ⊔ T)) ≤ B
  ·
    obtain ⟨f, -, hf, -⟩ := CFSG.AGLEmbedding.exists_surjective_comp_eq
      ((toStar (T.subgroupOf (L ⊔ T))).subgroupMap (A ⊓ L.subgroupOf (L ⊔ T)))
      (MonoidHom.subgroupMap_surjective _ _) gD hgDs (by
        intro d hd
        rw [MonoidHom.mem_ker, Subtype.ext_iff] at hd
        have hdC : (d : ↥(L ⊔ T)) ∈ gnC (T.subgroupOf (L ⊔ T)) := (QuotientGroup.eq_one_iff _).1 hd
        have h1 : QuotientGroup.mk' (B.subgroupOf A)
            (Subgroup.inclusion (inf_le_left : A ⊓ L.subgroupOf (L ⊔ T) ≤ A) d) = 1 :=
          (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 (hDC ⟨d.2, hdC⟩))
        rw [MonoidHom.mem_ker, hgD, MonoidHom.comp_apply, MonoidHom.comp_apply, h1, map_one])
    by_cases h3 : (L.subgroupOf (L ⊔ T)).map (toStar (T.subgroupOf (L ⊔ T))) ≤
        gnImg (T.subgroupOf (L ⊔ T))
          (Subgroup.normalizer ((T₂.subgroupOf (L ⊔ T) : Subgroup ↥(L ⊔ T)) : Set ↥(L ⊔ T)))
    ·
      let A₀ := ((A ⊓ L.subgroupOf (L ⊔ T)).map (toStar (T.subgroupOf (L ⊔ T)))).comap
          (toStar (T.subgroupOf (L ⊔ T))) ⊓
        Subgroup.normalizer ((T₂.subgroupOf (L ⊔ T) : Subgroup ↥(L ⊔ T)) : Set ↥(L ⊔ T))
      let ρ₀ : ↥A₀ →* ↥((A ⊓ L.subgroupOf (L ⊔ T)).map (toStar (T.subgroupOf (L ⊔ T)))) :=
        ((toStar (T.subgroupOf (L ⊔ T))).comp A₀.subtype).codRestrict _ fun a => a.2.1
      have hρ₀ : Function.Surjective ρ₀ := by
        rintro ⟨y, hy⟩
        obtain ⟨n, hn, hny⟩ := h3 (Subgroup.map_mono inf_le_right hy)
        exact ⟨⟨n, Subgroup.mem_inf.2 ⟨Subgroup.mem_comap.2 (hny ▸ hy), hn⟩⟩, Subtype.ext hny⟩
      refine Or.inr (Or.inl ⟨A₀, f.comp ρ₀, inf_le_right, ?_⟩)
      rw [MonoidHom.coe_comp]
      exact hf.comp hρ₀
    · exact Or.inr (Or.inr ⟨_, gnYComponent_subgroupOf le_sup_right le_sup_left hLn hgn₁ hT₁ hcomp
        hlift h3, _, f, Subgroup.map_mono inf_le_right, hf⟩)
  ·
    have hC₁ : gnC (T.subgroupOf (L ⊔ T)) ≤ Subgroup.normalizer
        ((T₁.subgroupOf (L ⊔ T) : Subgroup ↥(L ⊔ T)) : Set ↥(L ⊔ T)) := by
      refine le_trans (fun c hc => ?_) (Subgroup.centralizer_le_normalizer _)
      rw [gnC_subgroupOf_eq le_sup_right, Subgroup.mem_subgroupOf] at hc
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc _
        ((hT₁.trans (omegaOneCenterOf_le_uCore (L ⊔ T) T)) (Subgroup.mem_subgroupOf.mp ht)))
    have hnE : ∀ a ∈ A, ∀ d ∈ A ⊓ L.subgroupOf (L ⊔ T) ⊓ gnC (T.subgroupOf (L ⊔ T)),
        a * d * a⁻¹ ∈ A ⊓ L.subgroupOf (L ⊔ T) ⊓ gnC (T.subgroupOf (L ⊔ T)) :=
      fun a ha d hd => ⟨hnD a ha d hd.1, (gnC_normal _).conj_mem d hd.2 a⟩
    exact Or.inl ⟨_, e.toMonoidHom.comp ((QuotientGroup.mk' (B.subgroupOf A)).comp
      (Subgroup.inclusion (inf_le_left.trans inf_le_left))), inf_le_right.trans hC₁,
      e.surjective.comp (surjective_mk_comp_inclusion _ hnE hDC)⟩

end CFSG.LocalAnalysis.RankThreeUC.S15
