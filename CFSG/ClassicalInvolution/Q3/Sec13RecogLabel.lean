module

public import CFSG.ClassicalInvolution.Q3.TL3T13
import CFSG.ClassicalInvolution.Q3.TL3T52
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Trans
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2ConjE64
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3Conj
public import CFSG.ClassicalInvolution.Q3.AE.E64
public import CFSG.ClassicalInvolution.Q3.TL4D1Facts

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

private theorem labMapConjSub {M : Type*} [Group M] (φ : G →* M) (g : G) (K : Subgroup G) :
    (conjSub g K).map φ = conjSub (φ g) (K.map φ) := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv, mul_assoc]

private theorem labMapSubgroupOf {M : Type*} [Group M] {L K : Subgroup G} (hLK : L ≤ K)
    (φ : G →* M) : (L.subgroupOf K).map (φ.comp K.subtype) = L.map φ := by
  rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLK]

private theorem labRangeComp {M : Type*} [Group M] {Ω : Set (Subgroup G)}
    (hgen : pSpan Ω = ⊤) (φ : G →* M) : (φ.comp (pSpan Ω).subtype).range = φ.range := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype, hgen, ← MonoidHom.range_eq_map]

private theorem labComplMap {n : ℕ} (e : Equiv.Perm (Fin n)) (s : Finset (Fin n)) :
    (sᶜ).map e.toEmbedding = (s.map e.toEmbedding)ᶜ := by
  ext x
  simp only [Finset.mem_map, Finset.mem_compl, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨y, hy, rfl⟩ ⟨z, hz, hzy⟩
    exact hy (e.injective hzy ▸ hz)
  · intro hx
    exact ⟨e.symm x, fun h => hx ⟨e.symm x, h, by simp⟩, by simp⟩

private theorem labCardCompl : ∀ ℓ ∈ AE.fanoLines, ℓᶜ.card = 4 := by decide +kernel

private theorem labCardPlane : ∀ β ∈ AE.affinePlanes, β.card = 4 := by decide +kernel

private theorem labE64Card : ∀ α ∈ AE.e64Sets, α.card = 4 := by
  rintro α ⟨ℓ, hℓ, rfl⟩
  exact labCardCompl ℓ hℓ

private theorem labE29Card : ∀ α ∈ AE.e29Sets, α.card = 4 := fun α hα => labCardPlane α hα

private theorem labExistsNotMem {n : ℕ} (hn : 5 ≤ n) {β : Finset (Fin n)} (hβ : β.card = 4) :
    ∃ j : Fin n, j ∉ β := by
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ β := fun x _ => hcon x
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin, hβ] at h1
  omega

private theorem labMapEq {n : ℕ} {A : Subgroup (Equiv.Perm (Fin n))}
    {α0 α β : Finset (Fin n)} (hα0 : α0.card = 4) (hα : α.card = 4) (hβ : β.card = 4)
    {t t' : Equiv.Perm (Fin n)} (ht : t ∈ A) (ht' : t' ∈ A) (hαt : ∀ x ∈ α0, t x ∈ α)
    (hβt : ∀ x ∈ α0, t' x ∈ β) : ∃ s ∈ A, α.map s.toEmbedding = β := by
  have e1 : α0.map t.toEmbedding = α := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact hαt y hy
    · rw [Finset.card_map, hα0, hα]
  have e2 : α0.map t'.toEmbedding = β := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact hβt y hy
    · rw [Finset.card_map, hα0, hβ]
  have hcomp : t.toEmbedding.trans (t' * t⁻¹).toEmbedding = t'.toEmbedding :=
    Function.Embedding.ext fun x => by simp
  refine ⟨t' * t⁻¹, A.mul_mem ht' (A.inv_mem ht), ?_⟩
  rw [← e1, Finset.map_map, hcomp, e2]

private theorem labAltTrans {n : ℕ} (hn : 5 ≤ n) :
    ∀ α ∈ {β : Finset (Fin n) | β.card = 4}, ∀ β ∈ {β : Finset (Fin n) | β.card = 4},
      ∃ s ∈ alternatingGroup (Fin n), α.map s.toEmbedding = β := by
  intro α hα β hβ
  have hα' : α.card = 4 := hα
  have hβ' : β.card = 4 := hβ
  obtain ⟨σ, hσ, hsub⟩ := PhilipHall.Frame.TwinDisc.AE5.exists_even_perm hn hα' hβ'
  refine ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσ, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact hsub y hy
  · rw [Finset.card_map, hα', hβ']

private theorem labE64Trans :
    ∀ α ∈ AE.e64Sets, ∀ β ∈ AE.e64Sets, ∃ s ∈ AE.l32, α.map s.toEmbedding = β := by
  rintro α ⟨ℓ, hℓ, rfl⟩ β ⟨ℓ', hℓ', rfl⟩
  obtain ⟨t, -, ht1, ht2, -⟩ := PhilipHall.Frame.TwinThinPf.perm_target ℓ hℓ
  obtain ⟨t', -, ht1', ht2', -⟩ := PhilipHall.Frame.TwinThinPf.perm_target ℓ' hℓ'
  have hm : PhilipHall.Frame.TwinThinPf.pc t.1 ∈ AE.l32 := ht2
  have hm' : PhilipHall.Frame.TwinThinPf.pc t'.1 ∈ AE.l32 := ht2'
  exact labMapEq PhilipHall.Frame.TwinThinPf.α0_card (labCardCompl ℓ hℓ) (labCardCompl ℓ' hℓ')
    hm hm' ht1 ht1'

private theorem labE29Trans :
    ∀ α ∈ AE.e29Sets, ∀ β ∈ AE.e29Sets, ∃ s ∈ AE.agl32, α.map s.toEmbedding = β := by
  intro α hα β hβ
  obtain ⟨t, -, ht1, -, ht2, -⟩ := PhilipHall.Frame.TwinThinPf.P3.perm_target8 α hα
  obtain ⟨t', -, ht1', -, ht2', -⟩ := PhilipHall.Frame.TwinThinPf.P3.perm_target8 β hβ
  have hm : PhilipHall.Frame.TwinThinPf.pc t ∈ AE.agl32 := ht2
  have hm' : PhilipHall.Frame.TwinThinPf.pc t' ∈ AE.agl32 := ht2'
  exact labMapEq PhilipHall.Frame.TwinThinPf.P3.α0_card (labCardPlane α hα)
    (labCardPlane β hβ) hm hm' ht1 ht1'

private theorem labE64Closure :
    ∀ α ∈ AE.e64Sets, ∀ s ∈ AE.l32, α.map s.toEmbedding ∈ AE.e64Sets := by
  rintro α ⟨ℓ, hℓ, rfl⟩ s hs
  have hs' : ∀ r ∈ AE.fanoLines, r.map s.toEmbedding ∈ AE.fanoLines ∧
      r.map s⁻¹.toEmbedding ∈ AE.fanoLines := hs
  exact ⟨ℓ.map s.toEmbedding, (hs' ℓ hℓ).1, labComplMap s ℓ⟩

private theorem labE29Closure :
    ∀ α ∈ AE.e29Sets, ∀ s ∈ AE.agl32, α.map s.toEmbedding ∈ AE.e29Sets := by
  intro α hα s hs
  have hs' : ∀ r ∈ AE.affinePlanes, r.map s.toEmbedding ∈ AE.affinePlanes ∧
      r.map s⁻¹.toEmbedding ∈ AE.affinePlanes := hs
  exact (hs' α hα).1

private theorem labLabels {Ω : Set (Subgroup G)}
    (hinv : ∀ g : G, ∀ L ∈ Ω, conjSub g L ∈ Ω)
    (htrans : ∀ L ∈ Ω, ∀ L' ∈ Ω, ∃ g : G, conjSub g L = L') (hgen : pSpan Ω = ⊤)
    {n : ℕ} (hn : 5 ≤ n) {A : Subgroup (Equiv.Perm (Fin n))}
    (hA : ∀ s ∈ A, Equiv.Perm.sign s = 1)
    {𝒜 : Set (Finset (Fin n))} (h𝒜 : ∀ α ∈ 𝒜, α.card = 4)
    (hcl : ∀ α ∈ 𝒜, ∀ s ∈ A, α.map s.toEmbedding ∈ 𝒜)
    (htr : ∀ α ∈ 𝒜, ∀ β ∈ 𝒜, ∃ s ∈ A, α.map s.toEmbedding = β)
    {φ : G →* AE.AEQ n} (hinj : Function.Injective φ) (hrange : φ.range = AE.aeBarOver A)
    {K : Subgroup G} (hK : K ∈ Ω) {α : Finset (Fin n)} (hα : α ∈ 𝒜) {b : Bool}
    (hKφ : K.map φ = AE.memBar α (h𝒜 α hα) b) :
    (φ.comp (pSpan Ω).subtype).range = φ.range ∧
      (φ.comp (pSpan Ω).subtype).ker ≤ Subgroup.center ↥(pSpan Ω) ∧
      (∀ L ∈ Ω, ∃ β ∈ 𝒜, ∃ (h : β.card = 4) (c : Bool),
        (L.subgroupOf (pSpan Ω)).map (φ.comp (pSpan Ω).subtype) = AE.memBar β h c) ∧
      (∀ β ∈ 𝒜, ∀ (h : β.card = 4) (c : Bool), ∃ L ∈ Ω,
        (L.subgroupOf (pSpan Ω)).map (φ.comp (pSpan Ω).subtype) = AE.memBar β h c) := by
  have hlab : ∀ L ∈ Ω, (L.subgroupOf (pSpan Ω)).map (φ.comp (pSpan Ω).subtype) = L.map φ :=
    fun L hL => labMapSubgroupOf (le_pSpan hL) φ
  have hinj' : Function.Injective (φ.comp (pSpan Ω).subtype) :=
    fun x y hxy => Subtype.ext (hinj hxy)
  refine ⟨labRangeComp hgen φ, ?_, ?_, ?_⟩
  · intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : y = 1 := hinj' (hy.trans (map_one _).symm)
    rw [h1]
    exact Subgroup.one_mem _
  ·
    intro L hL
    obtain ⟨g, hg⟩ := htrans K hK L hL
    have hx : φ g ∈ AE.aeBarOver A := by
      rw [← hrange]
      exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
    obtain ⟨w, hw, hwg⟩ := Subgroup.mem_map.mp hx
    have hwA : w.perm ∈ A := hw.2
    obtain ⟨c, hc⟩ := AE.exists_conj_memBar_map w α (h𝒜 α hα) b
    refine ⟨α.map w.perm.toEmbedding, hcl α hα w.perm hwA, h𝒜 _ (hcl α hα w.perm hwA), c, ?_⟩
    rw [hlab L hL, ← hg, labMapConjSub, hKφ, ← hwg]
    exact hc
  ·
    intro β hβ hβcard c
    obtain ⟨s, hsA, hs⟩ := htr α hα β hβ
    have hw0 : AE.Wr.ofPerm s ∈ AE.aeSubOver A := AE.ofPerm_mem_aeSubOver hsA (hA s hsA)
    have hmain : ∃ w ∈ AE.aeSubOver A,
        conjSub (AE.mkQ n w) (AE.memBar α (h𝒜 α hα) b) = AE.memBar β hβcard c := by
      subst hs
      obtain ⟨c₁, hc₁⟩ := AE.exists_conj_ofPerm_memBar s α (h𝒜 α hα) b
      have hc₁' : conjSub (AE.mkQ n (AE.Wr.ofPerm s)) (AE.memBar α (h𝒜 α hα) b) =
          AE.memBar (α.map s.toEmbedding) hβcard c₁ := hc₁
      by_cases hcc : c₁ = c
      · exact ⟨AE.Wr.ofPerm s, hw0, by rw [hc₁', hcc]⟩
      · obtain ⟨j, hj⟩ := labExistsNotMem hn hβcard
        have hj' : j ∉ Set.range (AE.emb (α.map s.toEmbedding) hβcard) := by
          rw [AE.range_emb]
          exact hj
        have hf : conjSub (AE.mkQ n (AE.twinVec (AE.emb (α.map s.toEmbedding) hβcard) j))
            (AE.memBar (α.map s.toEmbedding) hβcard c₁) =
            AE.memBar (α.map s.toEmbedding) hβcard (!c₁) :=
          PhilipHall.Frame.TwinDisc.AE5.conj_memBar_flip hn hβcard hj c₁
        have hnot : (!c₁) = c := by
          revert hcc
          cases c₁ <;> cases c <;> decide
        refine ⟨AE.twinVec (AE.emb (α.map s.toEmbedding) hβcard) j * AE.Wr.ofPerm s,
          (AE.aeSubOver A).mul_mem (AE.twinVec_mem _ hj' A) hw0, ?_⟩
        rw [map_mul, CFSG.ClassicalInvolution.Generic.conjSub_mul, hc₁', hf, hnot]
    obtain ⟨w, hw, hwc⟩ := hmain
    have hmw : AE.mkQ n w ∈ AE.aeBarOver A := Subgroup.mem_map_of_mem _ hw
    rw [← hrange, MonoidHom.mem_range] at hmw
    obtain ⟨g', hg'⟩ := hmw
    refine ⟨conjSub g' K, hinv g' K hK, ?_⟩
    rw [hlab _ (hinv g' K hK), labMapConjSub, hg', hKφ, hwc]

theorem nonempty_aeIdent_of_hom {Ω : Set (Subgroup G)}
    (hinv : ∀ g : G, ∀ L ∈ Ω, conjSub g L ∈ Ω)
    (htrans : ∀ L ∈ Ω, ∀ L' ∈ Ω, ∃ g : G, conjSub g L = L') (hgen : pSpan Ω = ⊤) {n : ℕ}
    (hn : 5 ≤ n) (φ : G →* AE.AEQ n) (hinj : Function.Injective φ)
    (hrange : φ.range = TL4.aeModel n) {K : Subgroup G} (hK : K ∈ Ω) {α : Finset (Fin n)}
    (hα : α.card = 4) {b : Bool} (hKφ : K.map φ = AE.memBar α hα b) :
    Nonempty (AEIdent Ω n) := by
  have hrange' : φ.range = AE.aeBarOver (alternatingGroup (Fin n)) := by
    rw [hrange, TL4.aeModel_eq n]
  obtain ⟨h1, h2, h3, h4⟩ := labLabels hinv htrans hgen hn (A := alternatingGroup (Fin n))
    TL4.alt_sign (𝒜 := {β : Finset (Fin n) | β.card = 4}) (fun _ h => h)
    (fun α hα s _ => by
      have hα' : α.card = 4 := hα
      show (α.map s.toEmbedding).card = 4
      rw [Finset.card_map, hα'])
    (labAltTrans hn) hinj hrange' hK (show α ∈ {β : Finset (Fin n) | β.card = 4} from hα) hKφ
  refine ⟨⟨φ.comp (pSpan Ω).subtype, h1.trans hrange, h2, ?_, ?_⟩⟩
  · intro L hL
    obtain ⟨β, -, hβ, c, e⟩ := h3 L hL
    exact ⟨β, hβ, c, e⟩
  · intro β hβ c
    exact h4 β hβ hβ c

theorem nonempty_aeIdentOn_e64_of_hom {Ω : Set (Subgroup G)}
    (hinv : ∀ g : G, ∀ L ∈ Ω, conjSub g L ∈ Ω)
    (htrans : ∀ L ∈ Ω, ∀ L' ∈ Ω, ∃ g : G, conjSub g L = L') (hgen : pSpan Ω = ⊤)
    (φ : G →* AE.AEQ 7) (hinj : Function.Injective φ) (hrange : φ.range = AE.e64Sub)
    {K : Subgroup G} (hK : K ∈ Ω) {α : Finset (Fin 7)} (hαS : α ∈ AE.e64Sets) (hα : α.card = 4)
    {b : Bool} (hKφ : K.map φ = AE.memBar α hα b) :
    Nonempty (AEIdentOn Ω 7 AE.e64Sets AE.e64Sub) := by
  have hrange' : φ.range = AE.aeBarOver AE.l32 := hrange
  obtain ⟨h1, h2, h3, h4⟩ := labLabels hinv htrans hgen (by norm_num) (A := AE.l32)
    TL4.l32_sign (𝒜 := AE.e64Sets) labE64Card labE64Closure labE64Trans hinj hrange' hK hαS hKφ
  exact ⟨⟨φ.comp (pSpan Ω).subtype, h1.trans hrange, h2, h3, h4⟩⟩

theorem nonempty_aeIdentOn_e29_of_hom {Ω : Set (Subgroup G)}
    (hinv : ∀ g : G, ∀ L ∈ Ω, conjSub g L ∈ Ω)
    (htrans : ∀ L ∈ Ω, ∀ L' ∈ Ω, ∃ g : G, conjSub g L = L') (hgen : pSpan Ω = ⊤)
    (φ : G →* AE.AEQ 8) (hinj : Function.Injective φ) (hrange : φ.range = AE.e29Sub)
    {K : Subgroup G} (hK : K ∈ Ω) {α : Finset (Fin 8)} (hαS : α ∈ AE.e29Sets) (hα : α.card = 4)
    {b : Bool} (hKφ : K.map φ = AE.memBar α hα b) :
    Nonempty (AEIdentOn Ω 8 AE.e29Sets AE.e29Sub) := by
  have hrange' : φ.range = AE.aeBarOver AE.agl32 := hrange
  obtain ⟨h1, h2, h3, h4⟩ := labLabels hinv htrans hgen (by norm_num) (A := AE.agl32)
    TL4.agl32_sign (𝒜 := AE.e29Sets) labE29Card labE29Closure labE29Trans hinj hrange' hK hαS
    hKφ
  exact ⟨⟨φ.comp (pSpan Ω).subtype, h1.trans hrange, h2, h3, h4⟩⟩

end CFSG.ClassicalInvolution.Q3.Sec13
