module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415W0
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

namespace L415

namespace IsProd

variable {G : Type*} [Group G] [Finite G] {E K₁ K₂ : Subgroup G} {s : G}

theorem map_K₂_of_map_K₁ (h : IsProd E K₁ K₂ s) (hE : E.Normal) {g : G}
    (h1 : K₁.map (MulAut.conj g).toMonoidHom = K₁) : K₂.map (MulAut.conj g).toMonoidHom = K₂ := by
  rcases LocalCores.distinct_components_commute
      (LocalCores.isComponent_map_mulEquiv (MulAut.conj g) (h.isComponent₂ hE))
      (h.isComponent₂ hE) with h2 | h2
  · exact h2
  · exfalso
    rcases LocalCores.distinct_components_commute
        (LocalCores.isComponent_map_mulEquiv (MulAut.conj g) (h.isComponent₂ hE))
        (h.isComponent₁ hE) with h3 | h3
    · apply h.K₁_ne_K₂
      apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
      rw [h1, h3]
    · have hNE : K₂.map (MulAut.conj g).toMonoidHom ≤ E := by
        rintro _ ⟨y, hy, rfl⟩
        exact hE.conj_mem y (h.K₂_le hy) g
      have hb := h.eq_bot_of_commute hNE h3 h2
      obtain ⟨a, b, hab⟩ := h.nonabelian₂
      apply hab
      have ha : (MulAut.conj g) (a : G) ∈ (⊥ : Subgroup G) := hb ▸ ⟨a, a.2, rfl⟩
      have hb' : (MulAut.conj g) (b : G) ∈ (⊥ : Subgroup G) := hb ▸ ⟨b, b.2, rfl⟩
      rw [mem_bot, map_eq_one_iff _ (MulAut.conj g).injective] at ha hb'
      exact Subtype.ext (by simp [ha, hb'])

theorem map_K₁_of_comm (h : IsProd E K₁ K₂ s) (hE : E.Normal) {z₁ g : G} (hz₁ : z₁ ∈ K₁)
    (hz₁1 : z₁ ≠ 1) (hg : g * z₁ = z₁ * g) : K₁.map (MulAut.conj g).toMonoidHom = K₁ := by
  rcases h.conj_cases hE g with h1 | h1
  · exact h1
  · exfalso
    have h2 : g * z₁ * g⁻¹ ∈ K₂ := by
      rw [← h1]
      exact ⟨z₁, hz₁, rfl⟩
    have h3 : g * z₁ * g⁻¹ = z₁ := by rw [hg]; group
    have h4 : z₁ ∈ K₁ ⊓ K₂ := mem_inf.mpr ⟨hz₁, h3 ▸ h2⟩
    rw [h.inf_eq, mem_bot] at h4
    exact hz₁1 h4

omit [Finite G] in
theorem mem_normalizer_iff_map (K : Subgroup G) (g : G) :
    g ∈ normalizer (K : Set G) ↔ K.map (MulAut.conj g).toMonoidHom = K := by
  constructor
  · intro hg
    rw [mem_normalizer_iff] at hg
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hg y).mp hy
    · intro hx
      refine ⟨g⁻¹ * x * g, (hg _).mpr (by simpa [mul_assoc] using hx), ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  · intro hK
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [← hK]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← hK] at hy
      obtain ⟨k, hk, hky⟩ := hy
      have : k = y := (MulAut.conj g).injective hky
      rwa [← this]

theorem normalizer_normal (h : IsProd E K₁ K₂ s) (hE : E.Normal) :
    (normalizer (K₁ : Set G)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_normalizer_iff_map] at hn ⊢
  have hn₂ := h.map_K₂_of_map_K₁ hE hn
  have hcomp3 : (MulAut.conj (g * n * g⁻¹)).toMonoidHom = (MulAut.conj g).toMonoidHom.comp
      ((MulAut.conj n).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom) := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  have hback : ∀ H : Subgroup G,
      (H.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = H := by
    intro H
    have hid : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    rw [map_map, hid, map_id]
  rw [hcomp3, ← map_map, ← map_map]
  rcases h.conj_cases hE g⁻¹ with h1 | h1
  · rw [h1, hn]
    conv_lhs => rw [← h1]
    exact hback K₁
  · rw [h1, hn₂, ← h1]
    exact hback K₁

end IsProd

theorem isSylowOf_W₀_of {X : Type} [Group X] [Finite X] {β t z₁ : X}
    {Kb₁ Kb₂ : Subgroup (MBar β)} (htM : t ∈ centralizer ({β} : Set X))
    (hprod : IsProd (layer (MBar β)) Kb₁ Kb₂ (QuotientGroup.mk ⟨t, htM⟩))
    {W : Subgroup X} (hW : IsSylowOf 2 W (centralizer {β})) (hz₁W : z₁ ∈ W)
    (hz₁2 : z₁ ^ 2 = 1) (hz₁ne : z₁ ≠ t * z₁ * t⁻¹)
    (hmk : ∀ hz₁ : z₁ ∈ centralizer ({β} : Set X),
      (QuotientGroup.mk ⟨z₁, hz₁⟩ : MBar β) ∈ Kb₁)
    (hcomm : ∀ x ∈ W, ∀ hx : x ∈ centralizer ({β} : Set X), x * z₁ = z₁ * x ↔
      Kb₁.map (MulAut.conj (QuotientGroup.mk ⟨x, hx⟩ : MBar β)).toMonoidHom = Kb₁) :
    IsSylowOf 2 (W ⊓ centralizer {z₁}) (centralizer {z₁} ⊓ centralizer {β}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := centralizer ({β} : Set X) with hMdef
  have hWM : W ≤ M := hW.le
  have hWp := hW.isPGroup
  have hE : (layer (MBar β)).Normal := by
    have := LocalCores.layer_characteristic (G := MBar β)
    infer_instance
  have hz₁M : z₁ ∈ M := hWM hz₁W
  set zb₁ : MBar β := QuotientGroup.mk ⟨z₁, hz₁M⟩ with hzb₁
  have hzbK : zb₁ ∈ Kb₁ := hmk hz₁M
  have hzb1 : zb₁ ≠ 1 := by
    intro h1
    have h2 : z₁ = 1 := mk_injOn hWM hWp hz₁W (one_mem W) (h1.trans rfl)
    exact hz₁ne (by rw [h2]; group)
  set N := normalizer (Kb₁ : Set (MBar β)) with hNdef
  have hN : N.Normal := hprod.normalizer_normal hE
  have hCN : centralizer {zb₁} ≤ N := fun g hg =>
    (L415.IsProd.mem_normalizer_iff_map _ _).mpr
      (hprod.map_K₁_of_comm hE hzbK hzb1 (mem_centralizer_singleton_iff.mp hg))
  have hbar : barOf M (W ⊓ centralizer {z₁}) = barOf M W ⊓ N := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : (x : X) ∈ W ⊓ centralizer {z₁} := hx
      refine mem_inf.mpr ⟨⟨x, hx'.1, rfl⟩, ?_⟩
      exact (L415.IsProd.mem_normalizer_iff_map _ _).mpr
        ((hcomm x hx'.1 x.2).mp (mem_centralizer_singleton_iff.mp hx'.2))
    · intro y hy
      obtain ⟨⟨x, hxW, rfl⟩, hxN⟩ := mem_inf.mp hy
      have hxW' : (x : X) ∈ W := hxW
      refine ⟨x, mem_inf.mpr ⟨hxW', mem_centralizer_singleton_iff.mpr ((hcomm x hxW' x.2).mpr
        ((L415.IsProd.mem_normalizer_iff_map _ _).mp hxN))⟩, rfl⟩
  have hSylN : IsSylowOf 2 (barOf M W ⊓ N) N :=
    (isSylowOf_barOf hW).inf_of_le_normalizer le_top fun g _ => by
      rw [mem_normalizer_iff]
      intro y
      refine ⟨fun hy => hN.conj_mem y hy g, fun hy => ?_⟩
      have := hN.conj_mem _ hy g⁻¹
      simpa [mul_assoc] using this
  have hle : barOf M W ⊓ N ≤ centralizer {zb₁} := by
    rw [← hbar]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : X) ∈ W ⊓ centralizer {z₁} := hx
    have h1 : (x : X) * z₁ = z₁ * x := mem_centralizer_singleton_iff.mp hx'.2
    rw [mem_centralizer_singleton_iff, hzb₁, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext h1
  have hSylC : IsSylowOf 2 (barOf M (W ⊓ centralizer {z₁})) (centralizer {zb₁}) := by
    rw [hbar]
    exact hSylN.of_le hle hCN
  have hW₀le : W ⊓ centralizer {z₁} ≤ centralizer {z₁} ⊓ M := fun x hx =>
    mem_inf.mpr ⟨(mem_inf.mp hx).2, hWM (mem_inf.mp hx).1⟩
  have hW₀p : IsPGroup 2 ↥(W ⊓ centralizer {z₁}) := hWp.to_le inf_le_left
  obtain ⟨P, hP, hW₀P⟩ := exists_isSylowOf_ge hW₀p hW₀le
  have hPM : P ≤ M := hP.le.trans inf_le_right
  have hPbar := isSylowOf_barOf_centralizer hz₁M hz₁2 hP
  have hcard : Nat.card P = Nat.card ↥(W ⊓ centralizer {z₁}) := by
    rw [← card_barOf hPM hP.isPGroup, ← card_barOf (hW₀le.trans inf_le_right) hW₀p,
      hPbar.card_eq, hSylC.card_eq]
  have hPeq : P = W ⊓ centralizer {z₁} := (eq_of_le_of_card_ge hW₀P hcard.le).symm
  rw [← hPeq]
  exact hP


end L415


variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ} {hs : Setting46e t L p f S w z V i j}
  {Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} {W : Subgroup X} {z₁ : X}

namespace Config415

variable (hc : Config415 hs Kb₁ Kb₂ W z₁)
include hc

theorem isSylowOf_W₀ : IsSylowOf 2 (W ⊓ centralizer {z₁})
    (centralizer {z₁} ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) :=
  L415.isSylowOf_W₀_of (hc.isSylowOf_W.le hc.t_mem_W) hc.prod hc.isSylowOf_W hc.z₁_mem hc.sq_z₁
    hc.z₁_ne hc.mk_z₁ hc.comm_iff

end Config415

end CFSG.ComponentClassification.HarrisLit
