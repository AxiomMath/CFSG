module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4HomoResU

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

theorem mem_sylow_of_mem_normalizer {X : Type} [Group X] [Finite X] (U : Sylow 2 X) {y : X}
    (hy : y ∈ normalizer ((U : Subgroup X) : Set X)) (hyy : y * y = 1) :
    y ∈ (U : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsPGroup 2 (zpowers y ⊔ (U : Subgroup X) : Subgroup X) :=
    (isPGroup_zpowers_of_mul_self hyy).to_sup_of_normal_right' U.isPGroup' (zpowers_le.mpr hy)
  have h2 := U.is_maximal' h1 le_sup_right
  rw [← h2]
  exact (le_sup_left : zpowers y ≤ _) (mem_zpowers y)

theorem mem_sylow_of_commute {X : Type} [Group X] [Finite X]
    (hX : fusionIsBenderGroup X) (U : Sylow 2 X) {x y : X} (hxU : x ∈ (U : Subgroup X))
    (hx1 : x ≠ 1) (hyx : y * x = x * y) (hyy : y * y = 1) : y ∈ (U : Subgroup X) :=
  mem_sylow_of_mem_normalizer U (RankTwoBender.centralizer_le_normalizer_of_mem hX U hxU hx1
    (mem_centralizer_singleton_iff.mpr hyx)) hyy

variable {G : Type} [Group G] [Finite G] {L T : Subgroup G} {f : ℕ}

theorem exists_ne_one_of_two_le_card {H : Subgroup G} (hH : 2 ≤ Nat.card H) : ∃ h ∈ H, h ≠ 1 := by
  have h1 : H ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot H).mp (by omega)
  obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h1
  exact ⟨a, ha, fun h2 => ha1 (Subtype.ext h2)⟩

omit [Finite G] in
theorem eq_one_of_mem_center_of_mul_self {L : Subgroup G} (hZ : Odd (Nat.card (center L)))
    {z : L} (hz : z ∈ center L) (hzz : z * z = 1) : z = 1 := by
  have h1 : orderOf (⟨z, hz⟩ : center L) ∣ Nat.card (center L) := orderOf_dvd_natCard _
  have h2 : orderOf (⟨z, hz⟩ : center L) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simp [sq, hzz]))
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h3 | h3
  · exact congrArg Subtype.val (orderOf_eq_one_iff.mp h3)
  · rw [h3] at h1
    exact absurd (even_iff_two_dvd.mpr h1) (Nat.not_even_iff_odd.mpr hZ)

namespace Sec3

theorem mem_of_mk_mem_range (h : Sec3 G L T) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {c : G} (hc : c ∈ L) (hcc : c * c = 1)
    (hcR : QuotientGroup.mk' (center L) (⟨c, hc⟩ : L) ∈ (sylowProj h.isSylowOf_T₁.le).range) :
    c ∈ T ⊓ L := by
  have hZ := odd_card_center_of_psl2 h.hyp.standard.1.1 hf e
  have hel := isElemAbelian_of_psl2 hZ (by omega) e h.isSylowOf_T₁
  obtain ⟨a, ha⟩ := hcR
  rw [sylowProj_apply] at ha
  have hz : (⟨a, h.isSylowOf_T₁.le a.2⟩ : L)⁻¹ * ⟨c, hc⟩ ∈ center L := QuotientGroup.eq.mp ha
  set a' : L := ⟨a, h.isSylowOf_T₁.le a.2⟩ with ha'
  set z : L := a'⁻¹ * ⟨c, hc⟩ with hzdef
  have hcz : (⟨c, hc⟩ : L) = a' * z := by rw [hzdef, mul_inv_cancel_left]
  have hza : z * a' = a' * z := (mem_center_iff.mp hz a').symm
  have haa : a' * a' = 1 := Subtype.ext (by
    show (a : G) * a = 1
    rw [← sq]
    exact hel.2 a a.2)
  have hcc' : (⟨c, hc⟩ : L) * ⟨c, hc⟩ = 1 := Subtype.ext hcc
  have hzz : z * z = 1 := by
    rw [hcz] at hcc'
    calc z * z = a' * a' * (z * z) := by rw [haa, one_mul]
      _ = a' * z * (a' * z) := by
        rw [mul_assoc a' z, ← mul_assoc z a' z, hza]; group
      _ = 1 := hcc'
  have hz1 := eq_one_of_mem_center_of_mul_self hZ hz hzz
  rw [hz1, mul_one] at hcz
  have : c = (a : G) := congrArg Subtype.val hcz
  rw [this]
  exact a.2

end Sec3

omit [Finite G] in
theorem commutator_zpowers_le_inf_centralizer {A : Subgroup G} (hA : IsElemAbelian 2 A) {x : G}
    (hxx : x * x = 1) (hxA : ∀ a ∈ A, x * a * x⁻¹ ∈ A) :
    ⁅A, zpowers x⁆ ≤ A ⊓ centralizer ({x} : Set G) := by
  rw [Subgroup.commutator_le]
  intro a ha g hg
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have haa : a * a = 1 := by rw [← sq]; exact hA.2 a ha
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hcomm : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b := fun b hb c hc =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨b, hb⟩ ⟨c, hc⟩)
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
  have hpow : x ^ k = 1 ∨ x ^ k = x := by
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, zpow_mul, zpow_two, hxx, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, zpow_two, hxx, one_zpow, one_mul]
  rcases hpow with h1 | h1 <;> rw [h1]
  · rw [commutatorElement_def, mul_one, mul_inv_cancel, one_mul, inv_one]
    exact one_mem _
  · rw [commutatorElement_def, ha', hx']
    have hb : x * a * x ∈ A := by simpa [hx'] using hxA a ha
    have hmem : a * x * a * x ∈ A := by
      rw [show a * x * a * x = a * (x * a * x) by group]
      exact mul_mem ha hb
    refine mem_inf.mpr ⟨hmem, mem_centralizer_singleton_iff.mpr ?_⟩
    calc a * x * a * x * x = a * (x * a * x) * x := by group
      _ = (x * a * x) * a * x := by rw [hcomm a ha _ hb]
      _ = x * (a * x * a * x) := by group

theorem card_le_card_inf_centralizer_sq {A : Subgroup G} (hA : IsElemAbelian 2 A) {x : G}
    (hxx : x * x = 1) (hxA : ∀ a ∈ A, x * a * x⁻¹ ∈ A) :
    Nat.card A ≤ Nat.card (A ⊓ centralizer ({x} : Set G) : Subgroup G) ^ 2 := by
  have hxN : x ∈ normalizer (A : Set G) := by
    rw [mem_normalizer_iff]
    intro a
    refine ⟨hxA a, fun ha => ?_⟩
    have := hxA _ ha
    have e1 : x * (x * a * x⁻¹) * x⁻¹ = (x * x) * a * (x * x)⁻¹ := by group
    rwa [e1, hxx, one_mul, inv_one, mul_one] at this
  have h1 := card_le_card_inf_centralizer_mul hA.1 hxN
  have h2 := card_le_of_le (commutator_zpowers_le_inf_centralizer hA hxx hxA)
  calc Nat.card A ≤ Nat.card (A ⊓ centralizer ({x} : Set G) : Subgroup G) *
        Nat.card (⁅A, zpowers x⁆ : Subgroup G) := h1
    _ ≤ Nat.card (A ⊓ centralizer ({x} : Set G) : Subgroup G) *
        Nat.card (A ⊓ centralizer ({x} : Set G) : Subgroup G) := Nat.mul_le_mul_left _ h2
    _ = _ := (sq _).symm

namespace Sec3

theorem card_le_two_mul_inf_rightConjugate_of_conj
    (h : Sec3 G L T) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {q : ℕ} (h313 : Lemma313 L T q) {w y : G}
    (hw : y * w * y⁻¹ ∈ centralizer (L : Set G)) (hw1 : w ≠ 1) (hww : w * w = 1)
    {E : Subgroup G} (hEel : IsElemAbelian 2 E)
    (hroot : ∀ a ∈ E, ∃ g : G, g * a * g⁻¹ ∈ gmsA L T)
    (hEw : E ≤ centralizer ({w} : Set G)) :
    Nat.card E ≤ 2 * Nat.card (E ⊓ rightConjugate L y : Subgroup G) := by
  have hZ := odd_card_center_of_psl2 h.hyp.standard.1.1 hf e
  have hAel : IsElemAbelian 2 (gmsA L T) := by
    rw [h.gmsA_eq_of_psl2 hf e]
    exact isElemAbelian_of_psl2 hZ (by omega) e h.isSylowOf_T₁
  have hB := (rankTwoBenderType_iff.mp h.hyp.bender).fusionIsBenderGroup
  set c := MulAut.conj y with hc
  set E' := E.map c.toMonoidHom with hE'
  have hE'el : IsElemAbelian 2 E' := isElemAbelian_map _ hEel
  have ht1 : y * w * y⁻¹ ≠ 1 := fun h1 => hw1 (conj_eq_one_iff.mp h1)
  have htt : y * w * y⁻¹ * (y * w * y⁻¹) = 1 := by
    calc y * w * y⁻¹ * (y * w * y⁻¹) = y * (w * w) * y⁻¹ := by group
      _ = 1 := by rw [hww]; group
  have hE'N : E' ≤ normalizer (L : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    refine h.centralizer_le_normalizer_of_mem hw ht1 htt (mem_centralizer_singleton_iff.mpr ?_)
    have haw : a * w = w * a := mem_centralizer_singleton_iff.mp (hEw ha)
    simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc y * a * y⁻¹ * (y * w * y⁻¹) = y * (a * w) * y⁻¹ := by group
      _ = y * (w * a) * y⁻¹ := by rw [haw]
      _ = y * w * y⁻¹ * (y * a * y⁻¹) := by group
  have h1 := card_le_two_mul_inf h.hyp.standard.1.1 hB hE'N hE'el
  have h2 : E' ⊓ (L ⊔ centralizer (L : Set G)) ≤ (E ⊓ rightConjugate L y).map c.toMonoidHom := by
    rintro _ ⟨⟨a, ha, rfl⟩, hLK⟩
    refine ⟨a, mem_inf.mpr ⟨ha, (mem_rightConjugate_iff _ _ _).mpr ?_⟩, rfl⟩
    obtain ⟨g, hg⟩ := hroot a ha
    have haa : g * a * g⁻¹ * (g * a * g⁻¹) = 1 := by rw [← sq]; exact hAel.2 _ hg
    have hconj : (y * g⁻¹) * (g * a * g⁻¹) * (y * g⁻¹)⁻¹ = y * a * y⁻¹ := by group
    have := h.conj_mem_of_mem_sup hf e h313 hg haa (y := y * g⁻¹) (by
      rw [hconj]
      simpa [hc] using hLK)
    rwa [hconj] at this
  have h3 := card_le_of_le h2
  rw [card_map_of_injective c.injective] at h3
  have h4 : Nat.card E' = Nat.card E := card_map_of_injective c.injective
  omega

theorem exists_second_sylow (h : Sec3 G L T) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {x : G} (hxT : x ∈ T)
    (hxV : x ∉ gmsV L T) (hxx : x * x = 1) :
    ∃ l ∈ L, (∀ a ∈ T ⊓ L, x * (l * a * l⁻¹) * x⁻¹ ∈
        (T ⊓ L).map (MulAut.conj l).toMonoidHom) ∧
      ∀ a ∈ T ⊓ L, ∀ b ∈ T ⊓ L, a ≠ 1 → b ≠ 1 → a * (l * b * l⁻¹) ≠ l * b * l⁻¹ * a := by
  classical
  have hLp := h.hyp.standard.1.1
  have hZ := odd_card_center_of_psl2 hLp hf e
  have hel := isElemAbelian_of_psl2 hZ (by omega) e h.isSylowOf_T₁
  have hB := (rankTwoBenderType_iff.mp h.hyp.bender).fusionIsBenderGroup
  have hP := h.isSylowOf_T₁
  obtain ⟨R, hR⟩ := exists_sylow_range hP
  have hinj := sylowProj_injective hZ hP.isPGroup hP.le
  have hxN : x ∈ normalizer (L : Set G) := h.sylow.le hxT
  have hxLK : x ∉ L ⊔ centralizer (L : Set G) := fun hm => hxV ((h.mem_V_iff hf e hxT).mpr hm)
  have hαα : quotAutHom L ⟨x, hxN⟩ * quotAutHom L ⟨x, hxN⟩ = 1 := by
    rw [← map_mul]
    have : (⟨x, hxN⟩ * ⟨x, hxN⟩ : normalizer (L : Set G)) = 1 := Subtype.ext hxx
    rw [this, map_one]
  have hnotin := (quotAut_props hLp hxN hxLK (by rw [hxx]; exact one_mem _)).2
  have hxP : ∀ p ∈ T ⊓ L, x * p * x⁻¹ ∈ T ⊓ L := fun p hp =>
    (mem_normalizer_iff.mp (h.mem_normalizer_T₁ hxT) p).mp hp
  have hαR : ∀ s ∈ (R : Subgroup (rankTwoQuot L)),
      quotAutHom L ⟨x, hxN⟩ s ∈ (R : Subgroup (rankTwoQuot L)) := by
    intro s hs
    rw [← hR] at hs ⊢
    obtain ⟨p, rfl⟩ := hs
    exact ⟨⟨x * p * x⁻¹, hxP p p.2⟩, (quotAutHom_sylowProj hP.le hxN hxP p).symm⟩
  rcases AschbacherToolkit.Bender.invDichotomyAt_of_mulEquiv_psl2 (by omega) e R _ hαα hαR with
    hinner | ⟨x₁, hx₁N, hx₁⟩
  · exact absurd hinner hnotin
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (center L) x₁
  set π := QuotientGroup.mk' (center L) with hπ
  have hπa : ∀ a (ha : a ∈ T ⊓ L), π (⟨a, ha.2⟩ : L) ∈ (R : Subgroup (rankTwoQuot L)) :=
    fun a ha => by
      rw [← hR]
      exact ⟨⟨a, ha⟩, rfl⟩
  have hπ1 : ∀ a (ha : a ∈ T ⊓ L), a ≠ 1 → π (⟨a, ha.2⟩ : L) ≠ 1 := fun a ha ha1 h1 => by
    apply ha1
    have h2 : sylowProj hP.le ⟨a, ha⟩ = sylowProj hP.le 1 := by
      rw [map_one]
      exact h1
    exact congrArg Subtype.val (hinj h2)
  refine ⟨(l : G), l.2, fun a ha => ?_, fun a ha b hb ha1 hb1 hab => ?_⟩
  ·
    have hcL : ((l : G))⁻¹ * (x * ((l : G) * a * ((l : G))⁻¹) * x⁻¹) * (l : G) ∈ L := by
      have h1 : (l : G) * a * ((l : G))⁻¹ ∈ L := mul_mem (mul_mem l.2 ha.2) (inv_mem l.2)
      have h2 : x * ((l : G) * a * ((l : G))⁻¹) * x⁻¹ ∈ L := (mem_normalizer_iff.mp hxN _).mp h1
      exact mul_mem (mul_mem (inv_mem l.2) h2) l.2
    have hcc : ((l : G))⁻¹ * (x * ((l : G) * a * ((l : G))⁻¹) * x⁻¹) * (l : G) *
        (((l : G))⁻¹ * (x * ((l : G) * a * ((l : G))⁻¹) * x⁻¹) * (l : G)) = 1 := by
      have haa : a * a = 1 := by rw [← sq]; exact hel.2 a ha
      calc ((l : G))⁻¹ * (x * ((l : G) * a * ((l : G))⁻¹) * x⁻¹) * (l : G) *
            (((l : G))⁻¹ * (x * ((l : G) * a * ((l : G))⁻¹) * x⁻¹) * (l : G)) =
          ((l : G))⁻¹ * x * (l : G) * (a * a) * ((l : G))⁻¹ * x⁻¹ * (l : G) := by group
        _ = 1 := by rw [haa]; group
    have hcEq : (π l)⁻¹ * quotAutHom L ⟨x, hxN⟩ (π l * π ⟨a, ha.2⟩ * (π l)⁻¹) * π l =
        π ⟨((l : G))⁻¹ * (x * ((l : G) * a * ((l : G))⁻¹) * x⁻¹) * (l : G), hcL⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul, quotAutHom_apply_mk, ← map_mul, ← map_mul]
      congr 1
    have hc := hx₁ _ (hπa a ha)
    rw [hcEq, ← hR] at hc
    have hmem := h.mem_of_mk_mem_range hf e hcL hcc hc
    refine ⟨_, hmem, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  ·
    have hc₂L : (l : G) * b * ((l : G))⁻¹ ∈ L := mul_mem (mul_mem l.2 hb.2) (inv_mem l.2)
    have hbb : b * b = 1 := by rw [← sq]; exact hel.2 b hb
    have hc₂eq : π (⟨(l : G) * b * ((l : G))⁻¹, hc₂L⟩ : L) = π l * π ⟨b, hb.2⟩ * (π l)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    have hc₂c₂ : π (⟨(l : G) * b * ((l : G))⁻¹, hc₂L⟩ : L) *
        π ⟨(l : G) * b * ((l : G))⁻¹, hc₂L⟩ = 1 := by
      rw [hc₂eq]
      calc π l * π ⟨b, hb.2⟩ * (π l)⁻¹ * (π l * π ⟨b, hb.2⟩ * (π l)⁻¹) =
          π l * (π ⟨b, hb.2⟩ * π ⟨b, hb.2⟩) * (π l)⁻¹ := by group
        _ = 1 := by
          rw [← map_mul]
          have : (⟨b, hb.2⟩ * ⟨b, hb.2⟩ : L) = 1 := Subtype.ext hbb
          rw [this, map_one]
          group
    have hcomm : π (⟨(l : G) * b * ((l : G))⁻¹, hc₂L⟩ : L) * π ⟨a, ha.2⟩ =
        π ⟨a, ha.2⟩ * π ⟨(l : G) * b * ((l : G))⁻¹, hc₂L⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hab.symm
    have hc₂R := mem_sylow_of_commute hB R (hπa a ha) (hπ1 a ha ha1) hcomm hc₂c₂
    have hc₂R' : π (⟨(l : G) * b * ((l : G))⁻¹, hc₂L⟩ : L) ∈
        ((π l • R : Sylow 2 _) : Subgroup _) := by
      rw [AschbacherToolkit.Bender.Omega.mem_conj_smul_iff, hc₂eq]
      have : (π l)⁻¹ * (π l * π ⟨b, hb.2⟩ * (π l)⁻¹) * π l = π ⟨b, hb.2⟩ := by group
      rw [this]
      exact hπa b hb
    have hc₂1 : π (⟨(l : G) * b * ((l : G))⁻¹, hc₂L⟩ : L) ≠ 1 := by
      rw [hc₂eq]
      intro h1
      apply hπ1 b hb hb1
      calc π ⟨b, hb.2⟩ = (π l)⁻¹ * (π l * π ⟨b, hb.2⟩ * (π l)⁻¹) * π l := by group
        _ = 1 := by rw [h1]; group
    have hRR := RankTwoBender.eq_of_mem_of_mem hB hc₂1 hc₂R hc₂R'
    exact hx₁N (Sylow.smul_eq_iff_mem_normalizer.mp hRR.symm)

end Sec3

omit [Finite G] in
theorem commute_of_mul_mem_center {L : Subgroup G} (hZ : Odd (Nat.card (center L))) {u v : L}
    (hu : u * u = 1) (hv : v * v = 1) (hz : u * v * u * v ∈ center L) : u * v = v * u := by
  have hzu : u * (u * v * u * v) * u = u * v * u * v := by
    calc u * (u * v * u * v) * u = (u * v * u * v) * u * u := by rw [mem_center_iff.mp hz u]
      _ = (u * v * u * v) * (u * u) := by group
      _ = u * v * u * v := by rw [hu, mul_one]
  have hzz : (u * v * u * v) * (u * v * u * v) = 1 := by
    have h1 : u * (u * v * u * v) * u = v * u * v * u := by
      calc u * (u * v * u * v) * u = (u * u) * v * u * v * u := by group
        _ = v * u * v * u := by rw [hu]; group
    calc (u * v * u * v) * (u * v * u * v) = (v * u * v * u) * (u * v * u * v) := by
          rw [← h1, hzu]
      _ = v * u * v * (u * u) * v * u * v := by group
      _ = v * u * (v * v) * u * v := by rw [hu]; group
      _ = v * (u * u) * v := by rw [hv]; group
      _ = v * v := by rw [hu]; group
      _ = 1 := hv
  have h1 := eq_one_of_mem_center_of_mul_self hZ hz hzz
  have h2 : (u * v) * (u * v) = 1 := by rw [← h1]; group
  have h3 := eq_inv_of_mul_eq_one_left h2
  rwa [mul_inv_rev, inv_eq_of_mul_eq_one_right hu, inv_eq_of_mul_eq_one_right hv] at h3

namespace Sec3

theorem commute_of_commute (h : Sec3 G L T) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {l c₁ c₂ : G} (hl : l ∈ L)
    (hlK : l ∉ centralizer (L : Set G)) (hll : l * l ∈ centralizer (L : Set G)) (hc₁ : c₁ ∈ L)
    (hc₂ : c₂ ∈ L) (hc₁₁ : c₁ * c₁ = 1) (hc₂₂ : c₂ * c₂ = 1) (h₁ : l * c₁ = c₁ * l)
    (h₂ : l * c₂ = c₂ * l) : c₁ * c₂ = c₂ * c₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := odd_card_center_of_psl2 h.hyp.standard.1.1 hf e
  have hB := (rankTwoBenderType_iff.mp h.hyp.bender).fusionIsBenderGroup
  set π := QuotientGroup.mk' (center L) with hπ
  set lL : L := ⟨l, hl⟩
  set u : L := ⟨c₁, hc₁⟩
  set v : L := ⟨c₂, hc₂⟩
  have hu : u * u = 1 := Subtype.ext hc₁₁
  have hv : v * v = 1 := Subtype.ext hc₂₂
  have hcenter : ∀ {z : L}, (z : G) ∈ centralizer (L : Set G) → z ∈ center L := fun {z} hz =>
    mem_center_iff.mpr fun g => Subtype.ext ((mem_centralizer_iff.mp hz g g.2))
  have hπl : π lL ≠ 1 := by
    intro h1
    apply hlK
    have h2 : lL ∈ center L := (QuotientGroup.eq_one_iff _).mp h1
    exact mem_centralizer_iff.mpr fun g hg =>
      (congrArg Subtype.val ((mem_center_iff.mp h2) ⟨g, hg⟩))
  have hπll : π lL * π lL = 1 := by
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr (hcenter hll)
  obtain ⟨S, hS⟩ := (isPGroup_zpowers_of_mul_self hπll).exists_le_sylow
  have hlS : π lL ∈ (S : Subgroup (rankTwoQuot L)) := hS (mem_zpowers _)
  have hcomm : ∀ {w : L}, (l * (w : G) = w * l) → π w * π lL = π lL * π w := fun {w} hw => by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hw.symm
  have huS := mem_sylow_of_commute hB S hlS hπl (hcomm (w := u) h₁)
    (by rw [← map_mul, hu, map_one])
  have hvS := mem_sylow_of_commute hB S hlS hπl (hcomm (w := v) h₂)
    (by rw [← map_mul, hv, map_one])
  have huC := RankTwoBender.mem_centralizer_of_involution hB S huS
    (by rw [sq, ← map_mul, hu, map_one])
  have huv : π u * π v = π v * π u := (mem_centralizer_iff.mp huC (π v) hvS).symm
  have hz : u * v * u * v ∈ center L := by
    have h1 : π (v * u) = π (u * v) := by rw [map_mul, map_mul, huv]
    have h2 := QuotientGroup.eq.mp h1
    have h3 : (v * u)⁻¹ * (u * v) = u * v * u * v := by
      have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
      have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
      rw [mul_inv_rev, hu', hv']
      group
    rwa [h3] at h2
  have := commute_of_mul_mem_center hZ hu hv hz
  exact congrArg Subtype.val this

end Sec3

end CFSG.ComponentClassification.GMS78
