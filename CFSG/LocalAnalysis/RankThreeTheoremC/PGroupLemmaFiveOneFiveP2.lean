module

public import CFSG.LocalAnalysis.RankThreeTheoremC.PGroupLemmaFiveOneFive
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.SectionRank Subgroup
open PGroupL515

variable {G : Type} [Group G] [Finite G]

namespace PGroupL515

section Basic

variable {Y : Subgroup G}

omit [Finite G] in
theorem mul_mul_inv_eq_of_mem_center {a w : G} (ha : a ∈ Y)
    (hw : w ∈ Y ⊓ centralizer (Y : Set G)) : a * w * a⁻¹ = w := by
  rw [mem_centralizer_iff.mp hw.2 a ha, mul_inv_cancel_right]

omit [Finite G] in
theorem conj_mem_center {n z : G} (hn : n ∈ normalizer (Y : Set G))
    (hz : z ∈ Y ⊓ centralizer (Y : Set G)) : n * z * n⁻¹ ∈ Y ⊓ centralizer (Y : Set G) := by
  refine ⟨(mem_normalizer_iff.mp hn z).mp hz.1, mem_centralizer_iff.mpr fun h hh => ?_⟩
  have hh' : n⁻¹ * h * n ∈ Y := by
    have := (mem_normalizer_iff.mp (inv_mem hn) h).mp hh
    rwa [inv_inv] at this
  have hc := mem_centralizer_iff.mp hz.2 _ hh'
  calc h * (n * z * n⁻¹) = n * ((n⁻¹ * h * n) * z) * n⁻¹ := by group
    _ = n * (z * (n⁻¹ * h * n)) * n⁻¹ := by rw [hc]
    _ = n * z * n⁻¹ * h := by group

omit [Finite G] in
theorem normalizer_le_normalizer_center :
    normalizer (Y : Set G) ≤ normalizer ((Y ⊓ centralizer (Y : Set G) : Subgroup G) : Set G) := by
  intro n hn
  rw [mem_normalizer_iff]
  intro z
  refine ⟨conj_mem_center hn, fun hz => ?_⟩
  have := conj_mem_center (inv_mem hn) hz
  simpa [mul_assoc] using this

omit [Finite G] in
theorem le_normalizer_of_forall_conj_mem {P E : Subgroup G}
    (h : ∀ s ∈ P, ∀ e ∈ E, s * e * s⁻¹ ∈ E) : P ≤ normalizer (E : Set G) := by
  intro s hs
  rw [mem_normalizer_iff]
  intro e
  refine ⟨h s hs e, fun he => ?_⟩
  have := h s⁻¹ (inv_mem hs) _ he
  simpa [mul_assoc] using this

theorem mul_card_le_card_of_lt {p : ℕ} [hp : Fact p.Prime] {A B : Subgroup G} (hB : IsPGroup p B)
    (h : A < B) : p * Nat.card A ≤ Nat.card B := by
  obtain ⟨b, hb⟩ := hB.exists_card_eq
  obtain ⟨a, ha⟩ := (hB.to_le h.le).exists_card_eq
  have hlt := Subgroup.card_lt_of_lt h
  rw [ha, hb] at hlt ⊢
  have := (Nat.pow_lt_pow_iff_right hp.out.one_lt).mp hlt
  calc p * p ^ a = p ^ (a + 1) := by ring
    _ ≤ p ^ b := Nat.pow_le_pow_right hp.out.pos this

end Basic

end PGroupL515

section Extraspecial

variable {p : ℕ} [hp : Fact p.Prime] {Y : Subgroup G}

omit [Fact p.Prime] in
theorem IsExtraspecialExpP.exists_ne (hY : IsExtraspecialExpP p Y) :
    ∃ a b : Y, a * b ≠ b * a := by
  by_contra h
  push Not at h
  exact hY.1 ⟨⟨h⟩⟩

omit [Fact p.Prime] in
theorem IsExtraspecialExpP.not_le_center (hY : IsExtraspecialExpP p Y) :
    ¬ Y ≤ Y ⊓ centralizer (Y : Set G) := by
  intro h
  obtain ⟨a, b, hab⟩ := hY.exists_ne
  exact hab (Subtype.ext (mem_centralizer_iff.mp (h b.2).2 a a.2))

omit [Fact p.Prime] in
theorem IsExtraspecialExpP.isElemAbelian_center (hY : IsExtraspecialExpP p Y) :
    IsElemAbelian p (Y ⊓ centralizer (Y : Set G)) :=
  ⟨⟨⟨fun a b => Subtype.ext (mem_centralizer_iff.mp b.2.2 a a.2.1)⟩⟩,
    fun z hz => hY.2.2 z hz.1⟩

theorem IsExtraspecialExpP.card_center (hY : IsExtraspecialExpP p Y) :
    Nat.card (Y ⊓ centralizer (Y : Set G) : Subgroup G) = p := by
  obtain ⟨-, hZ, -⟩ := CFSG.SectionRank.Ccomm.nonabelian_prime_cube_central_structure hY.2.1
    hY.exists_ne
  have e : Y ⊓ centralizer (Y : Set G) = (center Y).map Y.subtype := by
    ext z
    constructor
    · intro hz
      refine ⟨⟨z, hz.1⟩, mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
      exact mem_centralizer_iff.mp hz.2 g g.2
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, mem_centralizer_iff.mpr fun h hh => ?_⟩
      exact congrArg Subtype.val (mem_center_iff.mp hw ⟨h, hh⟩)
  rw [e, card_map_of_injective Y.subtype_injective, hZ]

theorem IsExtraspecialExpP.mem_sup_centralizer_of_forall (hY : IsExtraspecialExpP p Y) {t : G}
    (ht : t ∈ normalizer (Y : Set G))
    (htr : ∀ y ∈ Y, y⁻¹ * (t * y * t⁻¹) ∈ Y ⊓ centralizer (Y : Set G)) :
    t ∈ Y ⊔ centralizer (Y : Set G) := by
  obtain ⟨-, -, -, -, -, -, hinn⟩ :=
    CFSG.SectionRank.Ccomm.nonabelian_prime_cube_central_structure hY.2.1 hY.exists_ne
  obtain ⟨g, hg⟩ := hinn (Y.normalizerMonoidHom ⟨t, ht⟩) fun x => by
    refine mem_center_iff.mpr fun h => Subtype.ext ?_
    have hx := (htr x x.2).2
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, normalizerMonoidHom_apply_apply_coe]
    exact mem_centralizer_iff.mp hx h h.2
  have key : ∀ h ∈ Y, t * h * t⁻¹ = g * h * (g : G)⁻¹ := fun h hh => by
    have := congrArg (fun β : MulAut Y => ((β ⟨h, hh⟩ : Y) : G)) hg
    simpa [normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] using this
  have hc : (g : G)⁻¹ * t ∈ centralizer (Y : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    calc h * ((g : G)⁻¹ * t) = (g : G)⁻¹ * (g * h * (g : G)⁻¹) * t := by group
      _ = (g : G)⁻¹ * (t * h * t⁻¹) * t := by rw [key h hh]
      _ = (g : G)⁻¹ * t * h := by group
  have e : t = g * ((g : G)⁻¹ * t) := by group
  rw [e]
  exact mul_mem_sup g.2 hc

end Extraspecial

namespace PGroupL515

theorem exists_mem_not_mem_forall_conj {p : ℕ} [Fact p.Prime] {P B Z K : Subgroup G}
    (hP : IsPGroup p P) (hB : IsPGroup p B) (hPB : P ≤ normalizer (B : Set G)) (hZK : Z ≤ K)
    (hKB : K ≤ B) (hZn : P ⊔ B ≤ normalizer (Z : Set G)) (hKn : P ⊔ B ≤ normalizer (K : Set G))
    (hKZ : ¬ K ≤ Z) : ∃ k ∈ K, k ∉ Z ∧ ∀ s ∈ P, k⁻¹ * (s * k * s⁻¹) ∈ Z := by
  set W := P ⊔ B with hW
  have hWp : IsPGroup p W := hP.to_sup_of_normal_right' hB hPB
  have hZW : Z ≤ W := (hZK.trans hKB).trans le_sup_right
  have hKW : K ≤ W := hKB.trans le_sup_right
  haveI hZnorm : (Z.subgroupOf W).Normal := (normal_subgroupOf_iff_le_normalizer hZW).mpr hZn
  haveI hKnorm : (K.subgroupOf W).Normal := (normal_subgroupOf_iff_le_normalizer hKW).mpr hKn
  set f := QuotientGroup.mk' (Z.subgroupOf W)
  set Kq := (K.subgroupOf W).map f
  haveI : Kq.Normal := Subgroup.Normal.map hKnorm f (QuotientGroup.mk'_surjective _)
  haveI : Group.IsNilpotent (W ⧸ Z.subgroupOf W) := (hWp.to_quotient _).isNilpotent
  have hKq : Kq ≠ ⊥ := by
    obtain ⟨k, hkK, hkZ⟩ := Set.not_subset.mp hKZ
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨f ⟨k, hKW hkK⟩, ⟨k, hKW hkK⟩, mem_subgroupOf.mpr hkK, rfl⟩, fun h => hkZ ?_⟩
    have h' : f ⟨k, hKW hkK⟩ = 1 := congrArg Subtype.val h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h'
    exact h'
  obtain ⟨⟨q, hq⟩, hq1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hKq)
  obtain ⟨⟨k, hkW⟩, hkK, rfl⟩ := hq.1
  refine ⟨k, mem_subgroupOf.mp hkK, fun hkZ => hq1 (Subtype.ext ?_), fun s hs => ?_⟩
  · change f ⟨k, hkW⟩ = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hkZ
  · have hc : f ⟨s, le_sup_left (a := P) hs⟩ * f ⟨k, hkW⟩ = f ⟨k, hkW⟩ * f ⟨s, le_sup_left (a := P) hs⟩ :=
      mem_center_iff.mp hq.2 _
    have h1 : f (⟨k, hkW⟩⁻¹ * (⟨s, le_sup_left (a := P) hs⟩ * ⟨k, hkW⟩ *
        ⟨s, le_sup_left (a := P) hs⟩⁻¹)) = 1 := by
      simp only [map_mul, map_inv]
      rw [hc]
      group
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    simpa using h1

end PGroupL515

section Normalized

variable {p : ℕ} [hp : Fact p.Prime] {Y : Subgroup G}

theorem IsExtraspecialExpP.exists_normalized_sq (hY : IsExtraspecialExpP p Y) {P : Subgroup G}
    (hP : IsPGroup p P) (hPX : P ≤ normalizer (Y : Set G)) :
    ∃ E : Subgroup G, E ≤ Y ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      Y ⊓ centralizer (Y : Set G) ≤ E ∧ P ≤ normalizer (E : Set G) := by
  set Z := Y ⊓ centralizer (Y : Set G) with hZ
  have hYp : IsPGroup p Y := IsPGroup.of_card hY.2.1
  have hXZ := normalizer_le_normalizer_center (Y := Y)
  obtain ⟨y, hy, hyZ, hyP⟩ := exists_mem_not_mem_forall_conj hP hYp hPX inf_le_left le_rfl
    (sup_le (hPX.trans hXZ) (le_normalizer.trans hXZ)) (sup_le hPX le_normalizer)
    hY.not_le_center
  set E := zpowers y ⊔ Z with hE
  have hEY : E ≤ Y := sup_le (zpowers_le.mpr hy) inf_le_left
  have hEe : IsElemAbelian p E :=
    (isElemAbelian_zpowers (hY.2.2 y hy)).sup_of_commute hY.isElemAbelian_center
      fun a ha b hb => mem_centralizer_iff.mp hb.2 a (zpowers_le.mpr hy ha)
  have hZE : Z < E := lt_of_le_of_ne le_sup_right fun h =>
    hyZ (by change y ∈ Z; rw [h]; exact le_sup_left (a := zpowers y) (b := Z) (mem_zpowers y))
  have hEY' : E < Y := lt_of_le_of_ne hEY fun h => hY.1 (h ▸ hEe.1)
  have h1 := mul_card_le_card_of_lt (hYp.to_le hEY) hZE
  have h2 := mul_card_le_card_of_lt hYp hEY'
  rw [hY.card_center] at h1
  rw [hY.2.1] at h2
  refine ⟨E, hEY, hEe, ?_, le_sup_right, le_normalizer_of_forall_conj_mem fun s hs e he => ?_⟩
  · have : Nat.card E ≤ p ^ 2 := by
      have h3 : p * Nat.card E ≤ p * p ^ 2 := by rw [← pow_succ']; exact h2
      exact Nat.le_of_mul_le_mul_left h3 hp.out.pos
    rw [← pow_two] at h1
    omega
  · have hle : E ≤ E.comap (MulAut.conj s).toMonoidHom := by
      refine sup_le (zpowers_le.mpr ?_) fun z hz => ?_
      · change s * y * s⁻¹ ∈ E
        have e : s * y * s⁻¹ = y * (y⁻¹ * (s * y * s⁻¹)) := by group
        rw [e]
        exact E.mul_mem (le_sup_left (a := zpowers y) (b := Z) (mem_zpowers y))
          (le_sup_right (a := zpowers y) (b := Z) (hyP s hs))
      · change s * z * s⁻¹ ∈ E
        exact le_sup_right (a := zpowers y) (b := Z) (conj_mem_center (hPX hs) hz)
    exact hle he

theorem IsExtraspecialExpP.forall_conj_mem_center_of_ne (hY : IsExtraspecialExpP p Y)
    {P : Subgroup G} (hP : IsPGroup p P) (hPX : P ≤ normalizer (Y : Set G))
    {E₁ E₂ : Subgroup G} (h1Y : E₁ ≤ Y) (h2Y : E₂ ≤ Y) (h1c : Nat.card E₁ = p ^ 2)
    (h2c : Nat.card E₂ = p ^ 2) (h1Z : Y ⊓ centralizer (Y : Set G) ≤ E₁)
    (h2Z : Y ⊓ centralizer (Y : Set G) ≤ E₂) (h1N : P ≤ normalizer (E₁ : Set G))
    (h2N : P ≤ normalizer (E₂ : Set G)) (hne : E₁ ≠ E₂) :
    ∀ s ∈ P, ∀ y ∈ Y, y⁻¹ * (s * y * s⁻¹) ∈ Y ⊓ centralizer (Y : Set G) := by
  set Z := Y ⊓ centralizer (Y : Set G) with hZ
  have hYp : IsPGroup p Y := IsPGroup.of_card hY.2.1
  have hXZ := normalizer_le_normalizer_center (Y := Y)
  let F : Subgroup G :=
    { carrier := {y | y ∈ Y ∧ ∀ s ∈ P, y⁻¹ * (s * y * s⁻¹) ∈ Z}
      one_mem' := ⟨Y.one_mem, fun s _ => by
        rw [mul_one, mul_inv_cancel, inv_one, mul_one]; exact Z.one_mem⟩
      mul_mem' := by
        rintro a b ⟨ha, hha⟩ ⟨hb, hhb⟩
        refine ⟨Y.mul_mem ha hb, fun s hs => ?_⟩
        have e : (a * b)⁻¹ * (s * (a * b) * s⁻¹) =
            b⁻¹ * (a⁻¹ * (s * a * s⁻¹)) * b⁻¹⁻¹ * (b⁻¹ * (s * b * s⁻¹)) := by group
        rw [e, mul_mul_inv_eq_of_mem_center (Y.inv_mem hb) (hha s hs)]
        exact Z.mul_mem (hha s hs) (hhb s hs)
      inv_mem' := by
        rintro a ⟨ha, hha⟩
        refine ⟨Y.inv_mem ha, fun s hs => ?_⟩
        have e : a⁻¹⁻¹ * (s * a⁻¹ * s⁻¹) = a * (a⁻¹ * (s * a * s⁻¹))⁻¹ * a⁻¹ := by group
        rw [e, mul_mul_inv_eq_of_mem_center ha (Z.inv_mem (hha s hs))]
        exact Z.inv_mem (hha s hs) }
  have hFY : F ≤ Y := fun y hy => hy.1
  have hZF : Z ≤ F := fun z hz => ⟨hz.1, fun s hs => Z.mul_mem (Z.inv_mem hz)
    (conj_mem_center (hPX hs) hz)⟩
  have hcZ := hY.card_center
  have hEF : ∀ E : Subgroup G, E ≤ Y → Nat.card E = p ^ 2 → Z ≤ E →
      P ≤ normalizer (E : Set G) → E ≤ F := by
    intro E hEY hEc hZE hPE
    have hEp : IsPGroup p E := hYp.to_le hEY
    have hEZ : ¬ E ≤ Z := fun h => by
      have := Subgroup.card_le_of_le h
      rw [hEc, hcZ] at this
      have : p ^ 1 < p ^ 2 := (Nat.pow_lt_pow_iff_right hp.out.one_lt).mpr (by norm_num)
      rw [pow_one] at this
      omega
    obtain ⟨e, heE, heZ, heP⟩ := exists_mem_not_mem_forall_conj hP hEp hPE hZE le_rfl
      (sup_le (hPX.trans hXZ) ((hEY.trans le_normalizer).trans hXZ)) (sup_le hPE le_normalizer)
      hEZ
    have hlt : Z < F ⊓ E := lt_of_le_of_ne (le_inf hZF hZE) fun h =>
      heZ (by change e ∈ Z; rw [h]; exact (⟨⟨hEY heE, heP⟩, heE⟩ : e ∈ F ⊓ E))
    have hc := mul_card_le_card_of_lt (hEp.to_le inf_le_right) hlt
    rw [hcZ, ← pow_two, ← hEc] at hc
    exact (Subgroup.eq_of_le_of_card_ge inf_le_right hc) ▸ inf_le_left
  have hE1F := hEF E₁ h1Y h1c h1Z h1N
  have hE2F := hEF E₂ h2Y h2c h2Z h2N
  have hlt : E₁ < E₁ ⊔ E₂ := lt_of_le_of_ne le_sup_left fun h => hne
    (Subgroup.eq_of_le_of_card_ge (h ▸ le_sup_right) (by rw [h1c, h2c])).symm
  have hc := mul_card_le_card_of_lt (hYp.to_le (sup_le h1Y h2Y)) hlt
  rw [h1c, ← pow_succ', ← hY.2.1] at hc
  have hFeq : F = Y := Subgroup.eq_of_le_of_card_ge hFY
    (hc.trans (Subgroup.card_le_of_le (sup_le hE1F hE2F)))
  intro s hs y hy
  exact (hFeq ▸ hy : y ∈ F).2 s hs

end Normalized

theorem pGroupExtraspecialNormalizer : PGroupExtraspecialNormalizer G := by
  intro p hp _ Y hY M hM
  haveI : Fact p.Prime := ⟨hp⟩
  set Z := Y ⊓ centralizer (Y : Set G) with hZ
  set X := normalizer (Y : Set G) with hX
  by_cases htriv : ∀ T : Subgroup G, T ≤ X → IsPGroup p T → ∀ t ∈ T, ∀ y ∈ Y,
      y⁻¹ * (t * y * t⁻¹) ∈ Z
  · exact Or.inr fun T hTX hT t ht =>
      hY.mem_sup_centralizer_of_forall (hTX ht) (htriv T hTX hT t ht)
  left
  push Not at htriv
  obtain ⟨T, hTX, hT, t, ht, y, hy, hty⟩ := htriv
  have hPM : ∀ P : Subgroup G, P ≤ X → IsPGroup p P → P ≤ M := by
    intro P hPX hP
    obtain ⟨E, hEY, hEe, hEc, -, hPE⟩ := hY.exists_normalized_sq hP hPX
    exact hPE.trans (hM E hEY hEe hEc)
  have hT' : IsPGroup p (T.subgroupOf X) := hT.comap_of_injective X.subtype X.subtype_injective
  obtain ⟨S, hS⟩ := hT'.exists_le_sylow
  set SG := (S : Subgroup X).map X.subtype with hSG
  have hSGX : SG ≤ X := map_subtype_le _
  have hSGp : IsPGroup p SG := S.isPGroup'.map _
  have hTSG : T ≤ SG := fun a ha => ⟨⟨a, hTX ha⟩, hS (mem_subgroupOf.mpr ha), rfl⟩
  obtain ⟨E₀, hE₀Y, hE₀e, hE₀c, hZE₀, hSE₀⟩ := hY.exists_normalized_sq hSGp hSGX
  intro x hx
  set xX : X := ⟨x, hx⟩ with hxX
  have hSM : (S : Subgroup X) ≤ M.subgroupOf X := fun a ha =>
    mem_subgroupOf.mpr (hPM SG hSGX hSGp ⟨a, ha, rfl⟩)
  have hS'M : ((xX • S : Sylow p X) : Subgroup X) ≤ M.subgroupOf X := fun a ha =>
    mem_subgroupOf.mpr (hPM _ (map_subtype_le _) ((xX • S).isPGroup'.map _) ⟨a, ha, rfl⟩)
  obtain ⟨h, hh, heq⟩ := exists_mem_eq_map_conj_of_sylow_le (xX • S) S hS'M hSM
  set n : G := ((h * xX : X) : G) with hn_def
  have hnX : n ∈ X := (h * xX).2
  have hn : ∀ s ∈ SG, n⁻¹ * s * n ∈ SG := by
    rintro _ ⟨s₀, hs₀, rfl⟩
    rw [heq] at hs₀
    obtain ⟨s₁, hs₁, rfl⟩ := hs₀
    rw [SetLike.mem_coe, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hs₁
    obtain ⟨s₂, hs₂, rfl⟩ := hs₁
    refine ⟨s₂, hs₂, ?_⟩
    simp only [hn_def, hxX, MulAut.smul_def, MulAut.conj_apply, MulEquiv.coe_toMonoidHom,
      coe_subtype, Subgroup.coe_mul, InvMemClass.coe_inv]
    group
  set E₂ := E₀.map (MulAut.conj n).toMonoidHom with hE₂
  have hE₂Y : E₂ ≤ Y := by
    rintro _ ⟨e, he, rfl⟩
    exact (mem_normalizer_iff.mp hnX e).mp (hE₀Y he)
  have hE₂c : Nat.card E₂ = p ^ 2 := by
    rw [card_map_of_injective (MulAut.conj n).injective, hE₀c]
  have hZE₂ : Z ≤ E₂ := fun z hz => mem_map_conj_iff.mpr (hZE₀ (by
    simpa using conj_mem_center (inv_mem hnX) hz))
  have hSE₂ : SG ≤ normalizer (E₂ : Set G) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro e
    rw [mem_map_conj_iff, mem_map_conj_iff]
    rw [mem_normalizer_iff.mp (hSE₀ (hn s hs)) (n⁻¹ * e * n)]
    constructor <;> intro hh' <;> convert hh' using 1 <;> group
  have hE : E₂ = E₀ := by
    by_contra hne
    exact hty (hY.forall_conj_mem_center_of_ne hSGp hSGX hE₀Y hE₂Y hE₀c hE₂c hZE₀ hZE₂ hSE₀ hSE₂
      (Ne.symm hne) t (hTSG ht) y hy)
  have k1 : ∀ e, e ∈ E₂ ↔ n⁻¹ * e * n ∈ E₀ := fun e => mem_map_conj_iff
  rw [hE] at k1
  have hnM : n ∈ M := by
    apply hM E₀ hE₀Y hE₀e hE₀c
    rw [mem_normalizer_iff]
    intro e
    rw [k1 (n * e * n⁻¹)]
    simp [mul_assoc]
  have e : x = ((h : X) : G)⁻¹ * n := by
    simp [hn_def, hxX]
  rw [e]
  exact M.mul_mem (M.inv_mem (mem_subgroupOf.mp hh)) hnM

end CFSG.LocalAnalysis.RankThreeTheoremC
