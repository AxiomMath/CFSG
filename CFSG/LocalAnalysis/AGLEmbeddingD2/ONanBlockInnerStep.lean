module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltDichotomy
public import CFSG.LocalAnalysis.AGLEmbeddingD2.BlockInnerAt
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive

public section

namespace CFSG.AGLEmbeddingD2.InnerStep

open CFSG.Open CFSG.AGLEmbedding

section Group

variable {Y : Type*} [Group Y]

theorem le_normalizer_centralizer (Lb : Subgroup Y) :
    Lb ≤ Subgroup.normalizer (Subgroup.centralizer (Lb : Set Y) : Set Y) :=
  Subgroup.le_normalizer.trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _))

theorem conj_conj_apply_of_mem_centralizer {Lb : Subgroup Y} {c s : Y}
    (hc : c ∈ Subgroup.centralizer (Lb : Set Y)) (hs : s ∈ Subgroup.normalizer (Lb : Set Y))
    {w : Y} (hw : w ∈ Lb) : (c * s * c⁻¹) * w * (c * s * c⁻¹)⁻¹ = s * w * s⁻¹ := by
  have hcw : c⁻¹ * w * c = w := by
    have := Subgroup.mem_centralizer_iff.mp hc w hw
    rw [mul_assoc, this, inv_mul_cancel_left]
  have hsw : s * w * s⁻¹ ∈ Lb := (Subgroup.mem_normalizer_iff.mp hs w).mp hw
  have hc2 : c * (s * w * s⁻¹) * c⁻¹ = s * w * s⁻¹ := by
    have := Subgroup.mem_centralizer_iff.mp hc _ hsw
    rw [← this, mul_inv_cancel_right]
  calc (c * s * c⁻¹) * w * (c * s * c⁻¹)⁻¹ = c * (s * (c⁻¹ * w * c) * s⁻¹) * c⁻¹ := by group
    _ = c * (s * w * s⁻¹) * c⁻¹ := by rw [hcw]
    _ = s * w * s⁻¹ := hc2

theorem exists_mem_of_inner {Lb Sb Pb : Subgroup Y}
    (hSL : Sb ≤ Subgroup.normalizer (Lb : Set Y))
    (hB : ∀ l ∈ Lb, (∀ s ∈ Sb, ∃ s' ∈ Sb, ∀ w ∈ Lb,
        (l * s * l⁻¹) * w * (l * s * l⁻¹)⁻¹ = s' * w * s'⁻¹) → l ∈ Pb)
    {x : Y} (hx : x ∈ Subgroup.normalizer (Sb : Set Y))
    (hxLC : x ∈ Lb ⊔ Subgroup.centralizer (Lb : Set Y)) :
    ∃ l ∈ Pb, x * l⁻¹ ∈ Subgroup.centralizer (Lb : Set Y) := by
  set Cb := Subgroup.centralizer (Lb : Set Y) with hCb
  have hLC := le_normalizer_centralizer Lb
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Lb Cb hLC] at hxLC
  obtain ⟨l, hl, c, hc, rfl⟩ := hxLC
  refine ⟨l, hB l hl fun s hs => ⟨l * c * s * (l * c)⁻¹, ?_, fun w hw => ?_⟩, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hx s).mp hs
  · have hw' : l⁻¹ * w * l ∈ Lb := Lb.mul_mem (Lb.mul_mem (Lb.inv_mem hl) hw) hl
    have key := conj_conj_apply_of_mem_centralizer hc (hSL hs) hw'
    calc (l * s * l⁻¹) * w * (l * s * l⁻¹)⁻¹ = l * (s * (l⁻¹ * w * l) * s⁻¹) * l⁻¹ := by group
      _ = l * ((c * s * c⁻¹) * (l⁻¹ * w * l) * (c * s * c⁻¹)⁻¹) * l⁻¹ := by rw [key]
      _ = (l * c * s * (l * c)⁻¹) * w * (l * c * s * (l * c)⁻¹)⁻¹ := by group
  · have : l * c * l⁻¹ ∈ Cb := (Subgroup.mem_normalizer_iff.mp (hLC hl) c).mp hc
    simpa [mul_assoc] using this

theorem card_dvd_card_range_of_ker_le {W S Λ : Type*} [Group W] [Group S] [Group Λ]
    (ρ : W →* Λ) (ψ : W →* S) (hψ : Function.Surjective ψ) (hker : ρ.ker ≤ ψ.ker) :
    Nat.card S ∣ Nat.card ρ.range := by
  have h1 := Subgroup.index_ker ψ
  have h2 := Subgroup.index_ker ρ
  rw [MonoidHom.range_eq_top_of_surjective ψ hψ, Subgroup.card_top] at h1
  rw [← h1, ← h2]
  exact Subgroup.index_dvd_of_le hker

theorem card_dvd_of_inner_quotient {Lb J : Subgroup Y}
    (hJ : J ≤ Subgroup.normalizer (Lb : Set Y)) {W : Type*} [Group W] (β : W →* Y)
    (hβN : ∀ w, β w ∈ Subgroup.normalizer (Lb : Set Y))
    (hβJ : ∀ w, ∃ l ∈ J, β w * l⁻¹ ∈ Subgroup.centralizer (Lb : Set Y))
    {Q : Type*} [Group Q] (φ : W →* Q) (hφ : Function.Surjective φ)
    (hker : ∀ w, β w ∈ Subgroup.centralizer (Lb : Set Y) → φ w = 1) :
    Nat.card Q ∣ Nat.card J := by
  set Nn := Subgroup.normalizer (Lb : Set Y) with hNn
  set ρ : Nn →* MulAut Lb := Lb.normalizerMonoidHom with hρ
  have hρker : ∀ g : Nn, ρ g = 1 ↔ (g : Y) ∈ Subgroup.centralizer (Lb : Set Y) := by
    intro g
    constructor
    · intro h1
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h2 := congrArg (fun f : MulAut Lb => ((f ⟨w, hw⟩ : Lb) : Y)) h1
      simp only [hρ, MulAut.one_apply] at h2
      change (g : Y) * w * (g : Y)⁻¹ = w at h2
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    · intro hg
      ext ⟨w, hw⟩
      change (g : Y) * w * (g : Y)⁻¹ = w
      rw [mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_centralizer_iff.mp hg w hw).symm
  set β' : W →* Nn := β.codRestrict Nn hβN with hβ'
  set f : W →* MulAut Lb := ρ.comp β' with hf
  have hfk : f.ker ≤ φ.ker := fun w hw => hker w ((hρker (β' w)).mp hw)
  have hrange : f.range ≤ (J.subgroupOf Nn).map ρ := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨l, hl, hxl⟩ := hβJ w
    refine ⟨⟨l, hJ hl⟩, Subgroup.mem_subgroupOf.mpr hl, ?_⟩
    have h1 : ρ (β' w * (⟨l, hJ hl⟩ : Nn)⁻¹) = 1 := (hρker _).mpr hxl
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1.symm
  calc Nat.card Q ∣ Nat.card f.range := card_dvd_card_range_of_ker_le f φ hφ hfk
    _ ∣ Nat.card ((J.subgroupOf Nn).map ρ) := Subgroup.card_dvd_of_le hrange
    _ ∣ Nat.card (J.subgroupOf Nn) := Subgroup.card_map_dvd _ _
    _ = Nat.card J := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ).toEquiv

end Group

section Block

variable {G : Type} [Group G]

theorem mem_normalizer_barM_of_mem {M X : Subgroup G} {g : G} (hgM : g ∈ M)
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hgM⟩ ∈
      Subgroup.normalizer (barM M X : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  Subgroup.le_normalizer_map _
    (Subgroup.mem_map_of_mem _ (Subgroup.le_normalizer_comap M.subtype hgX))

theorem mem_normalizer_barM_of_mem_barM_normalizer {M S : Subgroup G}
    {x : ↥M ⧸ CFSG.pCore 2 ↥M} (hx : x ∈ barM M (Subgroup.normalizer (S : Set G))) :
    x ∈ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  obtain ⟨m, hm, rfl⟩ := hx
  exact mem_normalizer_barM_of_mem m.2 (Subgroup.mem_subgroupOf.mp hm)

theorem card_dvd_card_blockPL {M S L U : Subgroup G}
    (hSL : barM M S ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hB : BlockInnerNormalizerAt M S L) (hUM : U ≤ M)
    (hUN : U ≤ Subgroup.normalizer (S : Set G))
    (hUL : barM M U ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {Q : Type*} [Group Q] (φ : U →* Q) (hφ : Function.Surjective φ)
    (hker : ∀ u ∈ centralizerBar M hUM (barM M L), φ u = 1) :
    Nat.card Q ∣ Nat.card (blockPL M S L) := by
  set Lb := barM M L with hLb
  have hPL : blockPL M S L ≤ Lb := barM_mono inf_le_right
  have hUK : ∀ u : U, barElt M hUM u ∈ barM M (Subgroup.normalizer (S : Set G)) := fun u =>
    barM_mono hUN (barElt_mem_barM hUM u)
  refine card_dvd_of_inner_quotient (hPL.trans Subgroup.le_normalizer) (barElt M hUM)
    (fun u => (sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _))
      (hUL (barElt_mem_barM hUM u))) (fun u => ?_) φ hφ hker
  exact exists_mem_of_inner hSL hB (mem_normalizer_barM_of_mem_barM_normalizer (hUK u))
    (hUL (barElt_mem_barM hUM u))

end Block

end CFSG.AGLEmbeddingD2.InnerStep
