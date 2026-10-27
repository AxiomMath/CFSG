module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBender
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutLinear
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutUnitary
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace BenderExt

open CFSG.Open Bender
open scoped MatrixGroups

structure BenderData (X : Type*) [Group X] [Finite X] : Prop where
  borel : ∃ q k : ℕ, 4 ≤ q ∧ fusionBenderBorel X q k
  nested : ∀ T : Sylow 2 X, NestedAt (T : Subgroup X)
  aut : ∀ T : Sylow 2 X, AutControlAt (T : Subgroup X)
  cent : ∀ T : Sylow 2 X, CentPairAt (T : Subgroup X)
  simple : IsSimpleGroup X

theorem benderData_of_isBenderGroup {X : Type*} [Group X] [Finite X]
    (hX : fusionIsBenderGroup X) : BenderData X := by
  refine ⟨?_, nestedAt_of_isBenderGroup hX, ?_, ?_,
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hX⟩
  · rcases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · have : Finite PSL(2, GaloisField 2 f) := Finite.of_surjective e e.surjective
      refine ⟨2 ^ f, 1, ?_, ?_⟩
      · calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      · exact (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1
          f hf).map_mulEquiv e.symm
    · have : Finite (PSU3 2 f) := Finite.of_surjective e e.surjective
      refine ⟨2 ^ f, 3, ?_, (bender_psu3_borel_full f hf).map_mulEquiv e.symm⟩
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    · have : Finite (Sz a) := Finite.of_surjective e e.surjective
      refine ⟨2 ^ (2 * a + 1), 2, ?_, (bender_suzuki_borel_full a ha).map_mulEquiv e.symm⟩
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · rcases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · exact autControlAt_of_mulEquiv_psl2 hf e
    · exact autControlAt_of_mulEquiv_psu3 hf e
    · exact autControlAt_of_mulEquiv_sz ha e
  · rcases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · exact centPairAt_of_mulEquiv_psl2 hf e
    · exact centPairAt_of_mulEquiv_psu3 hf e
    · exact centPairAt_of_mulEquiv_sz ha e

variable {Y : Type*} [Group Y]

structure ExtData (K : Subgroup Y) (P T : Subgroup Y) : Prop where
  inf_centralizer : K ⊓ Subgroup.centralizer (K : Set Y) = ⊥
  centralizer_le : Subgroup.centralizer (K : Set Y) ≤ P
  le_K : T ≤ K
  le_P : T ≤ P
  mem_T : ∀ x ∈ P, x ∈ K → x ∈ T
  sq_center : ∀ z ∈ sylowCenter T, z ^ 2 = 1
  card_center : 4 ≤ Nat.card (sylowCenter T)
  omega_one : ∀ t ∈ T, t ^ 2 = 1 → t ∈ sylowCenter T
  trans : ∀ z₁ ∈ sylowCenter T, ∀ z₂ ∈ sylowCenter T, z₁ ≠ 1 → z₂ ≠ 1 →
    ∃ n ∈ K, n ∈ Subgroup.normalizer (T : Set Y) ∧ n⁻¹ * z₁ * n = z₂
  nest : ∀ B₁ B₂ : Subgroup Y, B₁ ≤ T → B₂ ≤ T → ⁅B₁, B₂⁆ = ⊥ →
    (∀ b ∈ (B₁ : Set Y) ∪ B₂, ∀ k ∈ K, k⁻¹ * b * k ∈ T → k⁻¹ * b * k ∈ (B₁ : Set Y) ∪ B₂) →
      B₁ ≤ B₂ ∨ B₂ ≤ B₁
  cent : ∀ s ∈ T, s ∉ sylowCenter T → ∃ n ∈ K, n ∈ Subgroup.normalizer (T : Set Y) ∧
    ∀ t ∈ T, t * s = s * t → t * (n⁻¹ * s * n) = n⁻¹ * s * n * t → t ∈ sylowCenter T
  aut : ∀ y ∈ P, (∀ z ∈ sylowCenter T, y * z = z * y) →
    y ∉ T ⊔ Subgroup.centralizer (K : Set Y) →
      y ^ 2 ∈ T ⊔ Subgroup.centralizer (K : Set Y) ∧
      (y ^ 2 ∈ sylowCenter T → ∀ t ∈ T, y * t * y⁻¹ = t → t ∈ sylowCenter T) ∧
      ∃ t ∈ T, t⁻¹ * (y * t * y⁻¹) ∉ sylowCenter T

namespace Bridge

variable {K T : Subgroup Y}

theorem mem_sylowCenter_subgroupOf (hTK : T ≤ K) (x : K) :
    x ∈ sylowCenter (T.subgroupOf K) ↔ (x : Y) ∈ sylowCenter T := by
  rw [mem_sylowCenter, mem_sylowCenter, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun t ht => ?_⟩
    have := hc ⟨t, hTK ht⟩ (by rw [Subgroup.mem_subgroupOf]; exact ht)
    exact congrArg Subtype.val this
  · rintro ⟨hx, hc⟩
    exact ⟨hx, fun t ht => Subtype.ext (hc t ht)⟩

theorem mem_normalizer_subgroupOf (hTK : T ≤ K) (n : K) :
    n ∈ Subgroup.normalizer ((T.subgroupOf K : Subgroup K) : Set K) →
      (n : Y) ∈ Subgroup.normalizer (T : Set Y) := by
  intro hn
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro g
  constructor
  · intro hg
    have := (hn ⟨g, hTK hg⟩).mp (by rw [Subgroup.mem_subgroupOf]; exact hg)
    rw [Subgroup.mem_subgroupOf] at this
    exact this
  · intro hg
    have hgK : g ∈ K := by
      have h1 : (n : Y) * g * (n : Y)⁻¹ ∈ K := hTK hg
      have h2 : (n : Y)⁻¹ * ((n : Y) * g * (n : Y)⁻¹) * (n : Y) ∈ K :=
        K.mul_mem (K.mul_mem (K.inv_mem n.2) h1) n.2
      simpa [mul_assoc] using h2
    have := (hn ⟨g, hgK⟩).mpr (by rw [Subgroup.mem_subgroupOf]; exact hg)
    rw [Subgroup.mem_subgroupOf] at this
    exact this

end Bridge

open Bridge in
theorem extData_of_benderData [Finite Y] (K : Subgroup Y) [K.Normal] (hK : BenderData K)
    (P : Sylow 2 Y) (hKP : K ⊔ (P : Subgroup Y) = ⊤) :
    ExtData K P ((P : Subgroup Y) ⊓ K) := by
  classical
  set T := (P : Subgroup Y) ⊓ K with hTdef
  set C := Subgroup.centralizer (K : Set Y) with hCdef
  have hTK : T ≤ K := inf_le_right
  obtain ⟨T', hT'⟩ := CFSG.Glauberman.sylow_inf_normal P (N := K)
  obtain ⟨q, k, hq4, hB⟩ := hK.borel
  obtain ⟨hSE, hZ2, hZcard, hTcard⟩ := benderBorel_sylowCenter hB T'
  have : IsSimpleGroup K := hK.simple
  have hmemT : ∀ x : K, x ∈ (T' : Subgroup K) ↔ (x : Y) ∈ T := fun x => by
    rw [hT', Subgroup.mem_subgroupOf]
  have hZ : ∀ x : K, x ∈ sylowCenter (T' : Subgroup K) ↔ (x : Y) ∈ sylowCenter T := fun x => by
    rw [hT']
    exact mem_sylowCenter_subgroupOf hTK x
  have hN : ∀ n : K, n ∈ Subgroup.normalizer ((T' : Subgroup K) : Set K) →
      (n : Y) ∈ Subgroup.normalizer (T : Set Y) := fun n hn => by
    rw [hT'] at hn
    exact mem_normalizer_subgroupOf hTK n hn
  have hZliftY : ∀ z ∈ sylowCenter T, ∃ z' : K, (z' : Y) = z ∧ z' ∈ sylowCenter (T' : Subgroup K) :=
    fun z hz => ⟨⟨z, hTK (sylowCenter_le T hz)⟩, rfl, (hZ _).mpr hz⟩
  have hcenterK : Subgroup.center K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
    · exact h
    · exfalso
      apply hSE.1
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_normalizer_iff]
      intro t
      have hx : x ∈ Subgroup.center K := by rw [h]; exact Subgroup.mem_top x
      rw [← (Subgroup.mem_center_iff.mp hx t), mul_inv_cancel_right]
  have hKC : K ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hxK, hxC⟩
    have hx : (⟨x, hxK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC g g.2)
    rw [hcenterK, Subgroup.mem_bot] at hx
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hx
  have hCP : C ≤ P := by
    have hC2 : IsPGroup 2 C := by
      intro c
      have hcY : (c : Y) ∈ K ⊔ (P : Subgroup Y) := by rw [hKP]; exact Subgroup.mem_top _
      obtain ⟨x, hx, p, hp, hxp⟩ := Subgroup.mem_sup_of_normal_left.mp hcY
      obtain ⟨n, hn⟩ := P.isPGroup' ⟨p, hp⟩
      refine ⟨n, ?_⟩
      have hpn : p ^ (2 ^ n) = 1 := by
        have := congrArg Subtype.val hn
        simpa using this
      have hmk1 : (QuotientGroup.mk' K) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      have hmk : (QuotientGroup.mk' K) ((c : Y) ^ (2 ^ n)) = 1 := by
        rw [map_pow, ← hxp, map_mul, hmk1, one_mul, ← map_pow, hpn, map_one]
      have hcK : (c : Y) ^ (2 ^ n) ∈ K := (QuotientGroup.eq_one_iff _).mp hmk
      have hcC : (c : Y) ^ (2 ^ n) ∈ C := C.pow_mem c.2 _
      have h1 : (c : Y) ^ (2 ^ n) ∈ K ⊓ C := ⟨hcK, hcC⟩
      rw [hKC, Subgroup.mem_bot] at h1
      exact Subtype.ext (by simpa using h1)
    exact hC2.le_sylow_of_normal P
  refine ⟨hKC, hCP, hTK, inf_le_left, fun x hxP hxK => ⟨hxP, hxK⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro z hz
    obtain ⟨z', rfl, hz'⟩ := hZliftY z hz
    have := hZ2 z' hz'
    exact congrArg Subtype.val this
  ·
    have hcard : Nat.card (sylowCenter T) = Nat.card (sylowCenter (T' : Subgroup K)) := by
      have hmap : (sylowCenter (T' : Subgroup K)).map K.subtype = sylowCenter T := by
        ext y
        constructor
        · rintro ⟨y', hy', rfl⟩
          exact (hZ y').mp hy'
        · intro hy
          obtain ⟨z', rfl, hz'⟩ := hZliftY y hy
          exact ⟨z', hz', rfl⟩
      rw [← hmap, Subgroup.card_map_of_injective K.subtype_injective]
    rw [hcard, hZcard]
    exact hq4
  ·
    intro t ht ht2
    by_cases ht1 : t = 1
    · rw [ht1]
      exact (sylowCenter T).one_mem
    have hM := isStronglyEmbedded_of_fusion hSE
    have hZnt : 1 < Nat.card (sylowCenter (T' : Subgroup K)) := by rw [hZcard]; omega
    obtain ⟨⟨z, hzZ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      ((Subgroup.one_lt_card_iff_ne_bot _).mp hZnt)
    have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
    set t' : K := ⟨t, hTK ht⟩
    have ht'T : t' ∈ (T' : Subgroup K) := (hmemT t').mpr ht
    have ht'1 : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
    have ht'2 : t' ^ 2 = 1 := Subtype.ext (by simpa using ht2)
    have hmemN : ∀ x ∈ (T' : Subgroup K), x ∈ Subgroup.normalizer ((T' : Subgroup K) : Set K) :=
      fun x hx => Subgroup.le_normalizer hx
    obtain ⟨g, hg, hgz⟩ := hM.involutions_conjugate_in (hmemN _ (sylowCenter_le _ hzZ))
      ⟨hz1', hZ2 _ hzZ⟩
      (hmemN _ ht'T) ⟨ht'1, ht'2⟩
    have hmem := conj_mem_sylowCenter hg hzZ
    have hgz' : g⁻¹ * z * g = t' := hgz
    rw [hgz'] at hmem
    exact (hZ t').mp hmem
  ·
    intro z₁ hz₁ z₂ hz₂ h₁ h₂
    obtain ⟨z₁', rfl, hz₁'⟩ := hZliftY z₁ hz₁
    obtain ⟨z₂', rfl, hz₂'⟩ := hZliftY z₂ hz₂
    obtain ⟨n, hn, hnz⟩ := normalizer_transitive_center hSE hZ2 hz₁' hz₂'
      (fun h => h₁ (congrArg Subtype.val h)) (fun h => h₂ (congrArg Subtype.val h))
    exact ⟨n, n.2, hN n hn, congrArg Subtype.val hnz⟩
  ·
    intro B₁ B₂ hB₁ hB₂ hc hcl
    have hnest := hK.nested T'
    rw [hT'] at hnest
    have hB₁K : B₁ ≤ K := hB₁.trans hTK
    have hB₂K : B₂ ≤ K := hB₂.trans hTK
    have hmemB : ∀ (B : Subgroup Y) (x : K), x ∈ B.subgroupOf K ↔ (x : Y) ∈ B := fun B x =>
      Subgroup.mem_subgroupOf
    rcases hnest (B₁.subgroupOf K) (B₂.subgroupOf K)
      (fun x hx => by rw [hmemB] at hx; rw [Subgroup.mem_subgroupOf]; exact hB₁ hx)
      (fun x hx => by rw [hmemB] at hx; rw [Subgroup.mem_subgroupOf]; exact hB₂ hx)
      (by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro x hx y hy
        rw [hmemB] at hx hy
        rw [Subgroup.mem_bot]
        apply Subtype.ext
        have := Subgroup.commutator_mem_commutator hx hy
        rw [hc, Subgroup.mem_bot] at this
        simpa [commutatorElement_def] using this)
      (by
        intro a ha x hx
        have ha' : (a : Y) ∈ (B₁ : Set Y) ∪ B₂ := by
          rcases ha with ha | ha
          · exact Or.inl ((hmemB B₁ a).mp ha)
          · exact Or.inr ((hmemB B₂ a).mp ha)
        have hx' : (x : Y)⁻¹ * a * x ∈ T := by
          have h := hx
          rw [Subgroup.mem_subgroupOf] at h
          simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
        rcases hcl a ha' x x.2 hx' with h | h
        · left
          exact (hmemB B₁ _).mpr
            (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv, SetLike.mem_coe] using h)
        · right
          exact (hmemB B₂ _).mpr
            (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv, SetLike.mem_coe] using h))
      with h | h
    · left
      intro x hx
      have := h ((hmemB B₁ ⟨x, hB₁K hx⟩).mpr hx)
      exact (hmemB B₂ ⟨x, hB₁K hx⟩).mp this
    · right
      intro x hx
      have := h ((hmemB B₂ ⟨x, hB₂K hx⟩).mpr hx)
      exact (hmemB B₁ ⟨x, hB₂K hx⟩).mp this
  ·
    intro s hs hsZ
    have hcent := hK.cent T'
    set s' : K := ⟨s, hTK hs⟩
    obtain ⟨n, hn, hpair⟩ := hcent s' ((hmemT s').mpr hs) (fun h => hsZ ((hZ s').mp h))
    refine ⟨n, n.2, hN n hn, fun t ht hc₁ hc₂ => ?_⟩
    set t' : K := ⟨t, hTK ht⟩
    have := hpair t' ((hmemT t').mpr ht) (Subtype.ext hc₁) (Subtype.ext (by simpa using hc₂))
    exact (hZ t').mp this
  ·
    intro y hy hyZ hyout
    set α : MulAut K := MulAut.conjNormal y with hα
    have hαapp : ∀ x : K, (α x : Y) = y * x * y⁻¹ := fun x => MulAut.conjNormal_apply y x
    have hαT : ∀ s ∈ (T' : Subgroup K), α s ∈ (T' : Subgroup K) := by
      intro s hs
      rw [hmemT] at hs ⊢
      rw [hαapp]
      refine ⟨?_, (inferInstance : K.Normal).conj_mem _ (hTK hs) y⟩
      exact (P : Subgroup Y).mul_mem ((P : Subgroup Y).mul_mem hy hs.1)
        ((P : Subgroup Y).inv_mem hy)
    have hαZ : ∀ z ∈ sylowCenter (T' : Subgroup K), α z = z := by
      intro z hz
      apply Subtype.ext
      rw [hαapp, hyZ _ ((hZ z).mp hz), mul_inv_cancel_right]
    have hαpow : ∃ n : ℕ, α ^ (2 ^ n) = 1 := by
      obtain ⟨n, hn⟩ := P.isPGroup' ⟨y, hy⟩
      refine ⟨n, ?_⟩
      have hyn : y ^ (2 ^ n) = 1 := by
        have := congrArg Subtype.val hn
        simpa using this
      rw [hα, ← map_pow, hyn, map_one]
    have hconj_mem : ∀ s : K, (∀ x : K, α x = MulAut.conj s x) →
        y ∈ T ⊔ C ∨ s ∉ (T' : Subgroup K) := by
      intro s hs
      by_cases hsT : s ∈ (T' : Subgroup K)
      · left
        have hsC : (s : Y)⁻¹ * y ∈ C := by
          rw [Subgroup.mem_centralizer_iff]
          intro g hg
          have h := congrArg Subtype.val (hs ⟨g, hg⟩)
          rw [hαapp, MulAut.conj_apply] at h
          change y * g * y⁻¹ = (s : Y) * g * (s : Y)⁻¹ at h
          calc g * ((s : Y)⁻¹ * y) = (s : Y)⁻¹ * ((s : Y) * g * (s : Y)⁻¹) * y := by group
            _ = (s : Y)⁻¹ * (y * g * y⁻¹) * y := by rw [h]
            _ = (s : Y)⁻¹ * y * g := by group
        have := Subgroup.mul_mem_sup ((hmemT s).mp hsT) hsC
        rwa [mul_inv_cancel_left] at this
      · right
        exact hsT
    have hαout : ∀ s ∈ (T' : Subgroup K), α ≠ MulAut.conj s := by
      intro s hs heq
      rcases hconj_mem s (fun x => by rw [heq]) with h | h
      · exact hyout h
      · exact h hs
    obtain ⟨⟨s, hs, hs2⟩, hfix, ⟨t, ht, htZ⟩⟩ := hK.aut T' α hαT hαZ hαpow hαout
    refine ⟨?_, ?_, ?_⟩
    ·
      have hs2' : ∀ x : K, (α ^ 2) x = MulAut.conj s x := fun x => by rw [hs2]
      have hα2 : α ^ 2 = MulAut.conjNormal (y ^ 2) := by rw [hα, map_pow]
      have hsC : (s : Y)⁻¹ * y ^ 2 ∈ C := by
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        have h := congrArg Subtype.val (hs2' ⟨g, hg⟩)
        rw [hα2, MulAut.conjNormal_apply, MulAut.conj_apply] at h
        change y ^ 2 * g * (y ^ 2)⁻¹ = (s : Y) * g * (s : Y)⁻¹ at h
        calc g * ((s : Y)⁻¹ * y ^ 2) = (s : Y)⁻¹ * ((s : Y) * g * (s : Y)⁻¹) * y ^ 2 := by group
          _ = (s : Y)⁻¹ * (y ^ 2 * g * (y ^ 2)⁻¹) * y ^ 2 := by rw [h]
          _ = (s : Y)⁻¹ * y ^ 2 * g := by group
      have := Subgroup.mul_mem_sup ((hmemT s).mp hs) hsC
      rwa [mul_inv_cancel_left] at this
    ·
      intro hy2 t ht hyt
      have hy2K : y ^ 2 ∈ K := hTK (sylowCenter_le T hy2)
      set z : K := ⟨y ^ 2, hy2K⟩
      have hzZ : z ∈ sylowCenter (T' : Subgroup K) := (hZ z).mpr hy2
      have hα2 : α ^ 2 = MulAut.conj z := by
        rw [hα, ← map_pow]
        exact MulAut.conjNormal_val (H := K) (h := z)
      set t' : K := ⟨t, hTK ht⟩
      have := hfix ⟨z, hzZ, hα2⟩ t' ((hmemT t').mpr ht) (Subtype.ext (by rw [hαapp]; exact hyt))
      exact (hZ t').mp this
    ·
      refine ⟨t, (hmemT t).mp ht, fun h => htZ ((hZ _).mpr ?_)⟩
      have e : ((t⁻¹ * α t : K) : Y) = (t : Y)⁻¹ * (y * t * y⁻¹) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hαapp]
      rw [e]
      exact h

end BenderExt

end CFSG.ComponentClassification.AschbacherToolkit
