module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10 (cs)
open CFSG.LocalAnalysis.GLTheoremA.S172 (Cfg172)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (AutThreePowInner)

theorem exists_zpowers_eq_of_card_eq_prime {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {H : Subgroup G} (hH : Nat.card H = p) : ∃ g : G, Subgroup.zpowers g = H :=
  (Subgroup.isCyclic_iff_exists_zpowers_eq_top H).1 (isCyclic_of_prime_card hH)

theorem centralizer_zpowers_eq {G : Type*} [Group G] (d : G) :
    Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G) =
      Subgroup.centralizer ({d} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem centralizer_zpowers_sup_zpowers_eq {G : Type*} [Group G] (d y : G) :
    Subgroup.centralizer ((Subgroup.zpowers d ⊔ Subgroup.zpowers y : Subgroup G) : Set G) =
      Subgroup.centralizer ({d, y} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
    Subgroup.centralizer_closure, Set.singleton_union]

theorem nonempty_model_of_cfg {G₀ : Type} [Group G₀] {m p : ℕ} {QS : TauCeti.CFSGIndex → Prop}
    (hθ : ∀ (X : Type) [Group X], catalogIs X QS → Nonempty (X ≃* G₀))
    (hR : LiftableRank p G₀ m) {Ω : Type} [Group Ω] [Finite Ω] {S B D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg172 p S B D K x) (hBin : ∀ b ∈ B, b ∈ S ⊔ Subgroup.centralizer (S : Set Ω))
    (hS : catalogIs (PSimple p S) QS) : Nonempty (S172Model S B G₀) := by
  haveI := hR.nontrivial
  obtain ⟨e⟩ := hθ _ hS
  exact S172Model.nonempty_of_pSimple_equiv hcfg.normal hcfg.qs hBin e

variable {Ω : Type} [Group Ω]

theorem inf_centralizer_eq_zpowers_of_cfg [Finite Ω] {p : ℕ} {S B : Subgroup Ω} {D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg172 p S B D K x) {D' : Subgroup Ω} (hD'B : D' ≤ B) (hxD' : x ∈ D') :
    D' ⊓ Subgroup.centralizer (S : Set Ω) = Subgroup.zpowers x := by
  apply le_antisymm
  · intro b hb
    exact (hcfg.cent b (hD'B hb.1)).1 hb.2
  · rw [le_inf_iff]
    exact ⟨Subgroup.zpowers_le.2 hxD',
      Subgroup.zpowers_le.2 ((hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x))⟩

theorem centralizer_le_of_mem_cfg [Finite Ω] {p : ℕ} {S B : Subgroup Ω} {D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg172 p S B D K x) {D' : Subgroup Ω} (hxD' : x ∈ D') :
    ∀ b ∈ B, b ∈ Subgroup.centralizer (S : Set Ω) → b ∈ D' := by
  intro b hb hbc
  exact Subgroup.zpowers_le.2 hxD' ((hcfg.cent b hb).1 hbc)

namespace S172Model

variable {S B : Subgroup Ω} {G₀ : Type} [Group G₀] (M : S172Model S B G₀)

theorem card_img_eq_prime [Finite Ω] {p : ℕ} {D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg172 p S B D K x) {D' : Subgroup Ω} (hD'B : D' ≤ B) (hxD' : x ∈ D')
    (hcard : Nat.card D' = p ^ 2) : Nat.card (M.img D') = p := by
  have hp := hcfg.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 := M.card_img_mul_card_inf hD'B
  rw [inf_centralizer_eq_zpowers_of_cfg hcfg hD'B hxD', Nat.card_zpowers,
    orderOf_eq_prime (hcfg.elem.2 x hcfg.mem) hcfg.ne_one, hcard] at h1
  refine Nat.eq_of_mul_eq_mul_right hp.pos ?_
  rw [h1]
  ring

theorem exists_isE2_img_eq [Finite Ω] {p : ℕ} {D K : Subgroup Ω} {x : Ω} (hcfg : Cfg172 p S B D K x)
    {y : G₀} (hy : y ∈ M.β.range) (hy1 : y ≠ 1) (hyp : y ^ p = 1) :
    ∃ D₁ : Subgroup Ω, D₁ ≤ B ∧ (∀ b ∈ B, b ∈ Subgroup.centralizer (S : Set Ω) → b ∈ D₁) ∧
      M.img D₁ = Subgroup.zpowers y ∧ IsElemAbelian p D₁ ∧ Nat.card D₁ = p ^ 2 ∧ x ∈ D₁ := by
  have hp := hcfg.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hyr : Subgroup.zpowers y ≤ M.β.range := Subgroup.zpowers_le.2 hy
  have hxD₁ : x ∈ M.preimg (Subgroup.zpowers y) :=
    M.centralizer_le_preimg _ x hcfg.mem ((hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x))
  refine ⟨M.preimg (Subgroup.zpowers y), M.preimg_le _, M.centralizer_le_preimg _,
    M.img_preimg hyr, hcfg.elem.mono (M.preimg_le _), ?_, hxD₁⟩
  have h1 := M.card_img_mul_card_inf (M.preimg_le (Subgroup.zpowers y))
  rw [M.img_preimg hyr, inf_centralizer_eq_zpowers_of_cfg hcfg (M.preimg_le _) hxD₁, Nat.card_zpowers,
    Nat.card_zpowers, orderOf_eq_prime hyp hy1,
    orderOf_eq_prime (hcfg.elem.2 x hcfg.mem) hcfg.ne_one] at h1
  rw [← h1]
  ring

theorem exists_layer_data [Finite Ω] {p : ℕ} {D K : Subgroup Ω} {x : Ω} (hcfg : Cfg172 p S B D K x)
    {QK : TauCeti.CFSGIndex → Prop} (hK : catalogIs (PSimple p K) QK) :
    ∃ d ∈ M.β.range, M.img D = Subgroup.zpowers d ∧
      LayerIs p (Subgroup.centralizer ({d} : Set G₀)) QK ∧
      M.β.range ⊓ Subgroup.centralizer
        (GLALayer (Subgroup.centralizer ({d} : Set G₀)) : Set G₀) = Subgroup.zpowers d := by
  have hp := hcfg.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hDB, hDe, hDc, hxmem, hKeq, hKc, hDK⟩ := hcfg.std
  obtain ⟨d, hd⟩ := exists_zpowers_eq_of_card_eq_prime (p := p) (M.card_img_eq_prime hcfg hDB hxmem hDc)
  have hdr : d ∈ M.β.range := M.img_le_range D (hd ▸ Subgroup.mem_zpowers d)
  have hKc' : IsComponentOf (GLALayer (S ⊓ cs D)) (S ⊓ cs D) := by
    rw [← hKeq]
    exact hKc
  have hLK : LayerIs p (S ⊓ cs D) QK :=
    ⟨hKc', (catalogIs_pSimple_congr_eq hKeq).1 hK⟩
  have hcenteq : Subgroup.centralizer (M.img D : Set G₀) = Subgroup.centralizer ({d} : Set G₀) := by
    rw [← hd, centralizer_zpowers_eq]
  refine ⟨d, hdr, hd.symm, ?_, ?_⟩
  · rw [← hcenteq]
    exact (M.layerIs_centralizer_img_iff hp hDB).2 hLK
  · rw [← hcenteq, ← M.img_cs_glaLayer hDB hKc', ← hKeq, ← M.img_inf_left, ← hDK, ← hd]

end S172Model

theorem exist_of_model_of_mem_sup {G₀ : Type} [Group G₀] {m p : ℕ}
    {QS QK Q₁ Q₂ : TauCeti.CFSGIndex → Prop}
    (hθ : ∀ (X : Type) [Group X], catalogIs X QS → Nonempty (X ≃* G₀))
    (hR : LiftableRank p G₀ m) (hM : ModelExist p G₀ m QK Q₁ Q₂)
    (Ω : Type) [Group Ω] [Finite Ω] (S B D K : Subgroup Ω) (x : Ω) (hcfg : Cfg172 p S B D K x)
    (hBin : ∀ b ∈ B, b ∈ S ⊔ Subgroup.centralizer (S : Set Ω))
    (hS : catalogIs (PSimple p S) QS) (hK : catalogIs (PSimple p K) QK) :
    ∃ D₁ K₁ : Subgroup Ω, GLAStdSubPre p B x S D₁ K₁ ∧ catalogIs (PSimple p K₁) Q₁ ∧
      catalogIs (PSimple p (GLALayer (S ⊓ cs (D ⊔ D₁)))) Q₂ := by
  have hp := hcfg.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨M⟩ := nonempty_model_of_cfg hθ hR hcfg hBin hS
  have hBb := M.isElemAbelian_range_β hcfg.elem
  obtain ⟨d, hdr, hd, hLd, hCd⟩ := M.exists_layer_data hcfg hK
  obtain ⟨y, hyr, hyd, hLy, hCy, hLdy⟩ := hM M.β.range hBb (M.card_range_β hcfg hR) d hdr hLd hCd
  have hy1 : y ≠ 1 := fun h => hyd (h ▸ Subgroup.one_mem _)
  obtain ⟨D₁, hD₁B, hD₁x, hD₁img, hD₁e, hD₁card, hxD₁⟩ :=
    M.exists_isE2_img_eq hcfg hyr hy1 (hBb.2 y hyr)
  have hcentY : Subgroup.centralizer (M.img D₁ : Set G₀) = Subgroup.centralizer ({y} : Set G₀) := by
    rw [hD₁img, centralizer_zpowers_eq]
  obtain ⟨hKc₁, hK₁⟩ := (M.layerIs_centralizer_img_iff hp hD₁B).1 (by rw [hcentY]; exact hLy)
  have hK₁S : GLALayer (S ⊓ cs D₁) ≤ S := hKc₁.1.trans inf_le_left
  have hD₁K : D₁ = B ⊓ cs (GLALayer (S ⊓ cs D₁)) := by
    refine M.eq_inf_of_img_eq hD₁B hD₁x
      (fun b _ hbc => Subgroup.centralizer_le (fun a ha => hK₁S ha) hbc) ?_
    rw [M.img_cs_glaLayer hD₁B hKc₁, hcentY, hCy, hD₁img]
  refine ⟨D₁, GLALayer (S ⊓ cs D₁), ⟨hD₁B, hD₁e, hD₁card, hxD₁, rfl, hKc₁, hD₁K⟩, hK₁, ?_⟩
  obtain ⟨hDB, -⟩ := hcfg.std
  have hcent2 : Subgroup.centralizer (M.img (D ⊔ D₁) : Set G₀) =
      Subgroup.centralizer ({d, y} : Set G₀) := by
    rw [M.img_sup hDB hD₁B, hd, hD₁img, centralizer_zpowers_sup_zpowers_eq]
  exact ((M.layerIs_centralizer_img_iff hp (sup_le hDB hD₁B)).1 (by rw [hcent2]; exact hLdy)).2

theorem false_of_modelSolvable_of_mem_sup {G₀ : Type} [Group G₀] {m p : ℕ}
    {QS QK : TauCeti.CFSGIndex → Prop}
    (hθ : ∀ (X : Type) [Group X], catalogIs X QS → Nonempty (X ≃* G₀))
    (hR : LiftableRank p G₀ m) (hMS : ModelSolvable p G₀ m QK)
    (Ω : Type) [Group Ω] [Finite Ω] (S B D K : Subgroup Ω) (x : Ω) (hcfg : Cfg172 p S B D K x)
    (hBin : ∀ b ∈ B, b ∈ S ⊔ Subgroup.centralizer (S : Set Ω))
    (hS : catalogIs (PSimple p S) QS) (hK : catalogIs (PSimple p K) QK) : False := by
  have hp := hcfg.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨M⟩ := nonempty_model_of_cfg hθ hR hcfg hBin hS
  have hBb := M.isElemAbelian_range_β hcfg.elem
  obtain ⟨d, hdr, hd, hLd, hCd⟩ := M.exists_layer_data hcfg hK
  obtain ⟨hDB, hDe, hDc, hxmem, hKeq, hKc, hDK⟩ := hcfg.std
  obtain ⟨E, ⟨hEB, hEe, hEc⟩, hDE, hne⟩ := hcfg.e3
  have hnle : ¬ E ≤ D := by
    intro h
    have h1 := Subgroup.card_le_of_le h
    rw [hEc, hDc] at h1
    have := Nat.pow_lt_pow_right hp.one_lt (show 2 < 3 by norm_num)
    omega
  obtain ⟨e', he'E, he'D⟩ := SetLike.not_le_iff_exists.1 hnle
  have heB : e' ∈ B := hEB he'E
  have hed : M.β ⟨e', heB⟩ ∉ Subgroup.zpowers d := by
    intro h
    rw [← hd] at h
    exact he'D (M.mem_of_β_mem_img (centralizer_le_of_mem_cfg hcfg hxmem) h)
  have hsolv := hMS M.β.range hBb (M.card_range_β hcfg hR) d hdr hLd hCd (M.β ⟨e', heB⟩)
    ⟨_, rfl⟩ hed
  have hsub : ({d, M.β ⟨e', heB⟩} : Set G₀) ⊆ (M.img E : Set G₀) := by
    intro g hg
    rcases hg with rfl | rfl
    · exact M.img_mono hDE (hd ▸ Subgroup.mem_zpowers g)
    · exact M.mem_img.2 ⟨⟨e', heB⟩, he'E, rfl⟩
  have hle : M.csImg E ≤ Subgroup.centralizer ({d, M.β ⟨e', heB⟩} : Set G₀) :=
    (M.csImg_le_centralizer_img E).trans (Subgroup.centralizer_le hsub)
  haveI : Group.IsSolvable ↥(Subgroup.centralizer ({d, M.β ⟨e', heB⟩} : Set G₀)) := hsolv
  have hKc' : IsComponentOf (GLALayer (S ⊓ cs D)) (S ⊓ cs D) := by
    rw [← hKeq]
    exact hKc
  have hKS : K ≤ S := by
    rw [hKeq]
    exact hKc'.1.trans inf_le_left
  exact hne (M.glaPLayer_eq_bot_of_csImg_le hp hle hKS)

end CFSG.LocalAnalysis.GLTheoremA.S172X

end
