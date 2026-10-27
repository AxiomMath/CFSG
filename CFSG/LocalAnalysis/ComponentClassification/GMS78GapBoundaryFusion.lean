module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma313
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4ElemDefs

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace Sec4Elem

variable {L T U₁ : Subgroup G} {f : ℕ}

theorem gmsV_eq (h : Sec3 G L T) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) :
    gmsV L T = (T ⊓ L) ⊔ (T ⊓ centralizer (L : Set G)) := by
  show gmsA L T ⊔ _ = _
  rw [h.gmsA_eq_of_psl2 hf e]

theorem exists_map_eq_V
    (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {t : G}
    (ht : t ∈ T ⊓ centralizer (L : Set G)) (ht1 : t ≠ 1) {P : Subgroup G}
    (hPC : P ≤ centralizer ({t} : Set G)) (hP : IsPGroup 2 P) :
    ∃ k : G, ∀ E : Subgroup G, E ≤ P → IsElemAbelian 2 E →
      Nat.card (gmsV L T) ≤ Nat.card E → E.map (MulAut.conj k).toMonoidHom = gmsV L T := by
  have hT₀ := h.isElemAbelian_T₀ hF
  have htt : t * t = 1 := by rw [← sq]; exact hT₀.2 t ht
  have hPN := hPC.trans (h.centralizer_le_normalizer_of_mem (mem_inf.mp ht).2 ht1 htt)
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf h.sylow hPN hP
  refine ⟨k, fun E hEP hEel hcard => ?_⟩
  have hET : E.map (MulAut.conj k).toMonoidHom ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact hk x (hEP hx)
  have hc : Nat.card (E.map (MulAut.conj k).toMonoidHom) = Nat.card E :=
    card_map_of_injective (MulAut.conj k).injective
  rw [gmsV_eq h hf e] at hcard ⊢
  exact h.eq_of_psl2 hF hf e hET (isElemAbelian_map _ hEel) (by rw [hc]; exact hcard)

theorem conj_ne_of_card_eq
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ f)
    {a t : G} (ha : a ∈ gmsA L T) (ht : t ∈ T ⊓ centralizer (L : Set G)) (ht1 : t ≠ 1) (g : G) :
    g * a * g⁻¹ ≠ t := by
  intro hgat
  obtain ⟨hVc, hVel, -, -, -⟩ := hX.vFacts h hF
  set V := gmsV L T with hVdef
  have haV : a ∈ V := mem_sup_left ha
  have hle : U₁ ⊔ V ≤ centralizer ({a} : Set G) := by
    refine sup_le (fun u hu => mem_centralizer_singleton_iff.mpr (hE.comm hu (hE.A_le ha)))
      fun v hv => mem_centralizer_singleton_iff.mpr ?_
    exact congrArg Subtype.val (hVel.1.is_comm.comm ⟨v, hv⟩ ⟨a, haV⟩)
  set P := (U₁ ⊔ V).map (MulAut.conj g).toMonoidHom with hPdef
  have hPC : P ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : x * a = a * x := mem_centralizer_singleton_iff.mp (hle hx)
    refine mem_centralizer_singleton_iff.mpr ?_
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hgat]
    calc g * x * g⁻¹ * (g * a * g⁻¹) = g * (x * a) * g⁻¹ := by group
      _ = g * (a * x) * g⁻¹ := by rw [h1]
      _ = g * a * g⁻¹ * (g * x * g⁻¹) := by group
  have hVT : V ≤ T := sup_le (inf_le_left.trans inf_le_left) inf_le_left
  have hP2 : IsPGroup 2 P :=
    (hE.sylow.isPGroup.to_le (sup_le_sup_left hVT U₁)).map _
  obtain ⟨k, hk⟩ := exists_map_eq_V h hF hf e ht ht1 hPC hP2
  have hmap : ∀ E : Subgroup G, E ≤ U₁ ⊔ V → IsElemAbelian 2 E → Nat.card V ≤ Nat.card E →
      E.map (MulAut.conj (k * g)).toMonoidHom = V := by
    intro E hE' hEel hcard
    have h1 := hk (E.map (MulAut.conj g).toMonoidHom) (map_mono hE') (isElemAbelian_map _ hEel)
      (by rw [card_map_of_injective (MulAut.conj g).injective]; exact hcard)
    rw [hVdef, ← h1, map_map]
    congr 1
    ext x
    simp [mul_assoc]
  have hU := hmap U₁ le_sup_left hE.elem (by rw [hVc, hE.card, hq, sq])
  have hV := hmap V le_sup_right hVel le_rfl
  have hUV : U₁ = V := map_injective (MulAut.conj (k * g)).injective (hU.trans hV.symm)
  have h2 := hE.inf_V
  rw [hUV, inf_idem] at h2
  rw [← hUV] at h2
  exact (ne_of_gt hE.lt) h2

theorem exists_conj_eq_V
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (h313 : Lemma313 L T (2 ^ f))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ f)
    (hfus : ∃ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 ∧ ∃ g : G, g * t * g⁻¹ ∈ U₁) :
    ∃ c : G, (gmsV L T).map (MulAut.conj c).toMonoidHom = U₁ ∧
      ∀ a ∈ gmsA L T, c * a * c⁻¹ ∈ gmsA L T := by
  obtain ⟨t, ht, ht1, g, hgt⟩ := hfus
  obtain ⟨hVc, hVel, -, -, -⟩ := hX.vFacts h hF
  set E := U₁.map (MulAut.conj g⁻¹).toMonoidHom with hEdef
  have hEC : E ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨u, hu, rfl⟩
    have h1 := hE.comm hu hgt
    refine mem_centralizer_singleton_iff.mpr ?_
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * u * g * t = g⁻¹ * (u * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * u) * g := by rw [h1]
      _ = t * (g⁻¹ * u * g) := by group
  have hEel : IsElemAbelian 2 E := isElemAbelian_map _ hE.elem
  have hE2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hEel.2 x x.2)⟩
  obtain ⟨k, hk⟩ := exists_map_eq_V h hF hf e ht ht1 hEC hE2
  have h1 := hk E le_rfl hEel (by
    rw [hEdef, card_map_of_injective (MulAut.conj g⁻¹).injective, hVc, hE.card, hq, sq])
  rw [hEdef, map_map] at h1
  set c := g * k⁻¹ with hcdef
  have hU : (gmsV L T).map (MulAut.conj c).toMonoidHom = U₁ := by
    rw [← h1, map_map]
    convert map_id U₁ using 2
    ext x
    simp [hcdef, mul_assoc]
  refine ⟨c, hU, ?_⟩
  have hcA : ∀ a ∈ gmsA L T, c⁻¹ * a * c ∈ gmsA L T := by
    intro a ha
    have haU : a ∈ (gmsV L T).map (MulAut.conj c).toMonoidHom := hU ▸ hE.A_le ha
    obtain ⟨v, hv, hva⟩ := mem_map.mp haU
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hva
    have hv' : c⁻¹ * a * c⁻¹⁻¹ ∈ gmsV L T := by
      rw [← hva]
      simpa [mul_assoc] using hv
    simpa using h313.stronglyClosed a ha c⁻¹ hv'
  have hle : (gmsA L T).map (MulAut.conj c⁻¹).toMonoidHom ≤ gmsA L T := by
    rintro _ ⟨a, ha, rfl⟩
    simpa using hcA a ha
  have heq := Subgroup.eq_of_le_of_card_ge hle
    (by rw [card_map_of_injective (MulAut.conj c⁻¹).injective])
  intro a ha
  rw [← heq] at ha
  obtain ⟨b, hb, rfl⟩ := mem_map.mp ha
  simpa [mul_assoc] using hb

theorem exists_conj_mem_T₀
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (h313 : Lemma313 L T (2 ^ f))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ f)
    (hfus : ∃ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 ∧ ∃ g : G, g * t * g⁻¹ ∈ U₁)
    {u : G} (hu : u ∈ U₁) (huA : u ∉ gmsA L T) :
    ∃ x : G, x * u * x⁻¹ ∈ T ⊓ centralizer (L : Set G) ∧ x * u * x⁻¹ ≠ 1 := by
  obtain ⟨c, hU, hcA⟩ := hE.exists_conj_eq_V h hF hf e hX h313 hq hfus
  have huV : u ∈ (gmsV L T).map (MulAut.conj c).toMonoidHom := hU ▸ hu
  obtain ⟨v, hv, hvu⟩ := mem_map.mp huV
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hvu
  have hvA : v ∉ gmsA L T := fun hvA => huA (hvu ▸ hcA v hvA)
  obtain ⟨Q, ⟨⟨y, rfl⟩, -⟩, hvQ, hv1⟩ := (h313.cover v hv).mp hvA
  rw [mem_rightConjugate_iff] at hvQ
  refine ⟨y * c⁻¹, ?_, ?_⟩
  · have : y * c⁻¹ * u * (y * c⁻¹)⁻¹ = y * v * y⁻¹ := by rw [← hvu]; group
    rw [this]
    exact hvQ
  · have : y * c⁻¹ * u * (y * c⁻¹)⁻¹ = y * v * y⁻¹ := by rw [← hvu]; group
    rw [this]
    intro h1
    apply hv1
    calc v = y⁻¹ * (y * v * y⁻¹) * y := by group
      _ = 1 := by rw [h1]; group

theorem mem_A_of_conj_mem
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (h313 : Lemma313 L T (2 ^ f))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ f)
    (hfus : ∃ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 ∧ ∃ g : G, g * t * g⁻¹ ∈ U₁)
    {x : G} (hx : x ∈ U₁ ⊔ (T ⊓ centralizer (L : Set G))) (hxx : x * x = 1) {g : G}
    (hgx : g * x * g⁻¹ ∈ gmsA L T) : x ∈ gmsA L T := by
  by_contra hxA
  have hT₀ := h.isElemAbelian_T₀ hF
  obtain ⟨y, hyt, hyt1⟩ : ∃ y : G, y * x * y⁻¹ ∈ T ⊓ centralizer (L : Set G) ∧
      y * x * y⁻¹ ≠ 1 := by
    rcases hE.mem_or_mem hT₀ hx hxx with hxU | hxV
    · exact hE.exists_conj_mem_T₀ h hF hf e hX h313 hq hfus hxU hxA
    · obtain ⟨Q, ⟨⟨y, rfl⟩, -⟩, hxQ, hx1⟩ := (h313.cover x hxV).mp hxA
      rw [mem_rightConjugate_iff] at hxQ
      refine ⟨y, hxQ, fun h1 => hx1 ?_⟩
      calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
        _ = 1 := by rw [h1]; group
  apply hE.conj_ne_of_card_eq h hF hf e hX hq hgx hyt hyt1 (y * g⁻¹)
  group

end Sec4Elem

end CFSG.ComponentClassification.GMS78
