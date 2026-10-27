module

public import CFSG.HardMathSupport.Lang.E6Descent.SylowCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanFixedThreeGroup

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open scoped Pointwise
open CFSG.Open (IsElemAbelian)

theorem exists_conj_mem_sylow {G : Type*} [Group G] [Finite G] (P : Sylow 3 G) {Q : Subgroup G}
    (hQ : IsPGroup 3 Q) : ∃ g : G, ∀ x ∈ Q, g * x * g⁻¹ ∈ (P : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hQR⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R P
  refine ⟨g, fun x hx => ?_⟩
  have h1 : x ∈ (R : Subgroup G) := hQR hx
  have h2 := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (R : Subgroup G) h1
  have h3 : ((g • R : Sylow 3 G) : Subgroup G) = MulAut.conj g • (R : Subgroup G) := rfl
  rw [← h3, hg] at h2
  simpa [MulAut.smul_def] using h2

theorem index_le_three_of_sup_zpowers {H : Type*} [Group H] [Finite H] (L : Subgroup H) [L.Normal]
    {u : H} (hu3 : u ^ 3 = 1) (hH : L ⊔ Subgroup.zpowers u = ⊤) : L.index ≤ 3 := by
  set π := QuotientGroup.mk' L with hπ
  have h1 : (⊤ : Subgroup (H ⧸ L)) = Subgroup.zpowers (π u) := by
    have h2 : (L ⊔ Subgroup.zpowers u).map π = (⊤ : Subgroup H).map π := by rw [hH]
    rw [Subgroup.map_sup, MonoidHom.map_zpowers,
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective L)] at h2
    have h3 : L.map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
    rw [h3, bot_sup_eq] at h2
    exact h2.symm
  have h4 : Nat.card (H ⧸ L) = orderOf (π u) := by
    have : Nat.card (⊤ : Subgroup (H ⧸ L)) = Nat.card (H ⧸ L) := Subgroup.card_top
    rw [← this, h1, Nat.card_zpowers]
  rw [Subgroup.index_eq_card, h4]
  exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [← map_pow, hu3, map_one])

theorem card_subgroupOf_of_le {G : Type*} [Group G] {A B : Subgroup G} (h : A ≤ B) :
    Nat.card (A.subgroupOf B) = Nat.card A :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem exists_noncentral_fixed_of_sylow_normal (hB : RankBoundTStar)
    {H : Type} [Group H] [Finite H] {L Z F₀ T₀ : Subgroup H} [L.Normal] {u : H}
    (hZL : Z ≤ L) (hZcen : ∀ z ∈ Z, ∀ h : H, z * h = h * z) (hZp : IsPGroup 3 Z)
    (hZ3 : Nat.card Z ≤ 3) (hu3 : u ^ 3 = 1) (huL : u ∉ L)
    (hH : L ⊔ Subgroup.zpowers u = ⊤)
    (hF₀L : F₀ ≤ L) (hZF₀ : Z ≤ F₀) (hF₀p : IsPGroup 3 F₀)
    (hF₀c : ∀ a ∈ F₀, ∀ b ∈ F₀, a * b * a⁻¹ * b⁻¹ ∈ Z) (hF₀e : ∀ a ∈ F₀, a ^ 3 ∈ Z)
    (hF₀o : 27 * Nat.card Z ≤ Nat.card F₀)
    (hT₀L : T₀ ≤ L) (hT₀p : IsPGroup 3 T₀)
    (hT₀o : 81 * Nat.card Z ≤ Nat.card T₀) :
    ∃ y ∈ L, IsPGroup 3 (Subgroup.zpowers y) ∧ y * u = u * y ∧ y ∉ Z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZn : Z.Normal := ⟨fun z hz g => by
    have e : g * z * g⁻¹ = z := by rw [← hZcen z hz g, mul_inv_cancel_right]
    rw [e]; exact hz⟩
  have hLidx : L.index ≤ 3 := index_le_three_of_sup_zpowers L hu3 hH
  obtain ⟨P, hPu⟩ := (CFSG.AGLEmbedding.FixedThree.isPGroup_zpowers_of_pow_eq_one (g := u)
    (k := 1) (by simpa using hu3)).exists_le_sylow
  have huP : u ∈ (P : Subgroup H) := hPu (Subgroup.mem_zpowers u)
  have hZP : Z ≤ (P : Subgroup H) := hZp.le_sylow_of_normal P
  obtain ⟨g₁, hg₁⟩ := exists_conj_mem_sylow P hF₀p
  obtain ⟨g₂, hg₂⟩ := exists_conj_mem_sylow P hT₀p
  set Pc : Subgroup H := (P : Subgroup H) with hPc
  set F : Subgroup H := F₀.map (MulAut.conj g₁).toMonoidHom with hF
  set T : Subgroup H := T₀.map (MulAut.conj g₂).toMonoidHom with hT
  have hFmem : ∀ y, y ∈ F ↔ ∃ x ∈ F₀, g₁ * x * g₁⁻¹ = y := by
    intro y
    simp only [hF, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hTmem : ∀ y, y ∈ T ↔ ∃ x ∈ T₀, g₂ * x * g₂⁻¹ = y := by
    intro y
    simp only [hT, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hZfix : ∀ z ∈ Z, ∀ g : H, g * z * g⁻¹ = z := fun z hz g => by
    rw [← hZcen z hz g, mul_inv_cancel_right]
  have hFP : F ≤ Pc := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := (hFmem y).1 hy
    exact hg₁ x hx
  have hTP : T ≤ Pc := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := (hTmem y).1 hy
    exact hg₂ x hx
  have hTL : T ≤ L := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := (hTmem y).1 hy
    exact Subgroup.Normal.conj_mem ‹L.Normal› x (hT₀L hx) g₂
  have hFL : F ≤ L := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := (hFmem y).1 hy
    exact Subgroup.Normal.conj_mem ‹L.Normal› x (hF₀L hx) g₁
  have hZF : Z ≤ F := fun z hz => (hFmem z).2 ⟨z, hZF₀ hz, hZfix z hz g₁⟩
  have hFcard : Nat.card F = Nat.card F₀ :=
    Subgroup.card_map_of_injective (MulAut.conj g₁).injective
  have hTcard : Nat.card T = Nat.card T₀ :=
    Subgroup.card_map_of_injective (MulAut.conj g₂).injective
  have : (L.subgroupOf Pc).Normal := inferInstance
  have hS3 : (L.subgroupOf Pc).index ≤ 3 := by
    have h1 : (L.subgroupOf Pc).index = L.relIndex Pc := rfl
    have h2 := Subgroup.relIndex_dvd_index_of_normal L Pc
    rw [h1]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h2).trans hLidx
  obtain ⟨y, hyS, hyu, hyZ⟩ := exists_noncentral_fixed_of_maxClassRank hB
    (P := ↥Pc) (Z := Z.subgroupOf Pc) (S := L.subgroupOf Pc) (F := F.subgroupOf Pc)
    (u := (⟨u, huP⟩ : ↥Pc)) P.isPGroup'
    (fun z hz g => Subtype.ext (hZcen _ hz _))
    (by rw [card_subgroupOf_of_le hZP]; exact hZ3)
    hS3 (fun z hz => hZL hz)
    (Subtype.ext (by simpa using hu3))
    (fun h => huL h)
    (fun z hz => hZF hz) (fun a ha => hFL ha)
    (fun a ha b hb => by
      obtain ⟨x, hx, hxa⟩ := (hFmem _).1 ha
      obtain ⟨x', hx', hxb⟩ := (hFmem _).1 hb
      have hxa' : g₁ * x * g₁⁻¹ = (a : H) := hxa
      have hxb' : g₁ * x' * g₁⁻¹ = (b : H) := hxb
      show ((a : H) * b * (a : H)⁻¹ * (b : H)⁻¹) ∈ Z
      rw [← hxa', ← hxb']
      have : g₁ * x * g₁⁻¹ * (g₁ * x' * g₁⁻¹) * (g₁ * x * g₁⁻¹)⁻¹ * (g₁ * x' * g₁⁻¹)⁻¹ =
          g₁ * (x * x' * x⁻¹ * x'⁻¹) * g₁⁻¹ := by group
      rw [this, hZfix _ (hF₀c x hx x' hx') g₁]
      exact hF₀c x hx x' hx')
    (fun a ha => by
      obtain ⟨x, hx, hxa⟩ := (hFmem _).1 ha
      have hxa' : g₁ * x * g₁⁻¹ = (a : H) := hxa
      show (a : H) ^ 3 ∈ Z
      rw [← hxa']
      have : (g₁ * x * g₁⁻¹) ^ 3 = g₁ * x ^ 3 * g₁⁻¹ := conj_pow
      rw [this, hZfix _ (hF₀e x hx) g₁]
      exact hF₀e x hx)
    (by rw [card_subgroupOf_of_le hZP, card_subgroupOf_of_le hFP, hFcard]; exact hF₀o)
    (by
      have h1 : Nat.card (T.subgroupOf Pc) ≤ Nat.card (L.subgroupOf Pc) := by
        refine Nat.card_le_card_of_injective (Subgroup.inclusion ?_) (Subgroup.inclusion_injective _)
        intro t ht
        exact hTL ht
      rw [card_subgroupOf_of_le hZP]
      rw [card_subgroupOf_of_le hTP, hTcard] at h1
      exact hT₀o.trans h1)
  refine ⟨(y : H), hyS, ?_, ?_, hyZ⟩
  · obtain ⟨k, hk⟩ := P.isPGroup' y
    exact CFSG.AGLEmbedding.FixedThree.isPGroup_zpowers_of_pow_eq_one (k := k)
      (by simpa using congrArg Subtype.val hk)
  · exact congrArg Subtype.val hyu

end CFSG.HardMathSupport.Lang.E6Descent
