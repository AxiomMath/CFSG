module

public import CFSG.LocalAnalysis.ComponentClassification.AS81L34Odd
public import CFSG.LocalAnalysis.ComponentClassification.AS81Cover
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step13Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover LinearFlag

section Kernel

variable {A B : Type} [Group A] [Group B] [Finite A] (φ : A →* B)

omit [Finite A] in
theorem le_of_isPGroup_of_le_sup_ker (hker : φ.ker ≤ center A) (hodd : Odd (Nat.card φ.ker))
    {H P : Subgroup A} (hH : IsPGroup 2 H) (hP : IsPGroup 2 P) (hPH : P ≤ H ⊔ φ.ker) : P ≤ H := by
  intro p hp
  have hN : φ.ker ≤ normalizer (H : Set A) := fun z hz =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x _ =>
      (mem_center_iff.mp (hker hz) x))
  have hp' : p ∈ ((H ⊔ φ.ker : Subgroup A) : Set A) := hPH hp
  rw [coe_mul_of_right_le_normalizer_left H φ.ker hN, Set.mem_mul] at hp'
  obtain ⟨h, hh, z, hz, rfl⟩ := hp'
  obtain ⟨m, hm⟩ := hP ⟨h * z, hp⟩
  obtain ⟨n, hn⟩ := hH ⟨h, hh⟩
  have hm' : (h * z) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hn' : h ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hcomm : Commute h z := mem_center_iff.mp (hker hz) h
  have hz2 : z ^ 2 ^ (m + n) = 1 := by
    have h1 : (h * z) ^ 2 ^ (m + n) = 1 := by rw [pow_add, pow_mul, hm', one_pow]
    have h2 : h ^ 2 ^ (m + n) = 1 := by rw [pow_add, mul_comm, pow_mul, hn', one_pow]
    rw [hcomm.mul_pow, h2, one_mul] at h1
    exact h1
  have hzodd : Odd (orderOf z) := by
    have := Subgroup.orderOf_dvd_natCard φ.ker hz
    exact hodd.of_dvd_nat this
  have hz1 : z = 1 := by
    have hdvd := orderOf_dvd_of_pow_eq_one hz2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rcases j with _ | j
    · rw [pow_zero] at hj
      exact orderOf_eq_one_iff.mp hj
    · rw [hj, pow_succ] at hzodd
      exact absurd hzodd (by simp [Nat.odd_mul])
  rw [hz1, mul_one]
  exact hh

theorem eq_of_map_eq_of_isPGroup (hodd : Odd (Nat.card φ.ker)) {H : Subgroup A}
    (hH : IsPGroup 2 H) {x y : A} (hx : x ∈ H) (hy : y ∈ H) (h : φ x = φ y) : x = y := by
  have h1 : x⁻¹ * y ∈ H ⊓ φ.ker :=
    ⟨H.mul_mem (H.inv_mem hx) hy,
      MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, h, inv_mul_cancel])⟩
  rw [AschbacherTightEmbedding.two_subgroup_of_odd_eq_bot _ _ (hH.to_le inf_le_left)
    (hodd.of_dvd_nat (card_dvd_of_le inf_le_right)) le_rfl, mem_bot, inv_mul_eq_one] at h1
  exact h1

theorem card_map_of_isPGroup (hodd : Odd (Nat.card φ.ker)) {H : Subgroup A}
    (hH : IsPGroup 2 H) : Nat.card (H.map φ) = Nat.card H := by
  have hinj : Function.Injective (φ.comp H.subtype) := fun x y h =>
    Subtype.ext (eq_of_map_eq_of_isPGroup φ hodd hH x.2 y.2 h)
  have h1 : ((⊤ : Subgroup H).map (φ.comp H.subtype)) = H.map φ := by
    rw [← map_map, ← MonoidHom.range_eq_map, range_subtype]
  rw [← h1, card_map_of_injective hinj, card_top]

theorem mem_normalizer_of_map (hker : φ.ker ≤ center A) (hodd : Odd (Nat.card φ.ker))
    {H : Subgroup A} (hH : IsPGroup 2 H) {n : A}
    (hn : φ n ∈ normalizer ((H.map φ : Subgroup B) : Set B)) : n ∈ normalizer (H : Set A) := by
  rw [mem_normalizer_iff_map_conj_eq]
  have hle : H.map (MulAut.conj n).toMonoidHom ≤ H := by
    refine le_of_isPGroup_of_le_sup_ker φ hker hodd hH (hH.map _) ?_
    rw [← comap_map_eq]
    rintro _ ⟨x, hx, rfl⟩
    show φ (n * x * n⁻¹) ∈ H.map φ
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp hn _).mp ⟨x, hx, rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [card_map_of_injective (MulAut.conj n).injective])

end Kernel

section Cover

variable {A : Type} [Group A] [Finite A]

theorem L34Cover.ker_comp (c : L34Cover A) (hO : standardComponentOddCore A ≤ center A) :
    (c.π.comp (QuotientGroup.mk' (standardComponentOddCore A))).ker = center A := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, c.ker_eq]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have h1 : z⁻¹ * x ∈ standardComponentOddCore A := QuotientGroup.eq.mp hzx
    have := (center A).mul_mem hz (hO h1)
    simpa using this
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem L34Cover.exists_std (c : L34Cover A) (hO : standardComponentOddCore A ≤ center A)
    (T : Sylow 2 A) :
    ∃ φ : A →* projectiveSL 3 c.k, Function.Surjective φ ∧ φ.ker = center A ∧
      (T : Subgroup A).map φ = projUnip c.k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ₀ := c.π.comp (QuotientGroup.mk' (standardComponentOddCore A))
  have hφ₀ : Function.Surjective φ₀ := c.surj.comp (QuotientGroup.mk'_surjective _)
  have hker₀ := c.ker_comp hO
  obtain ⟨-, -, ⟨S₀, hS₀⟩, -⟩ := field_four_central_two_cover_parabolic_normalizers c.card_k
    (MonoidHom.id (projectiveSL 3 c.k)) Function.surjective_id
    (by rw [MonoidHom.ker_id]; exact bot_le)
    (by
      rw [MonoidHom.ker_id]
      exact isElementaryAbelian_of_sq_eq_one fun x hx => by
        rw [mem_bot] at hx
        rw [hx, one_pow])
  set S := T.mapSurjective hφ₀
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (projectiveSL 3 c.k) S S₀
  refine ⟨(MulAut.conj x).toMonoidHom.comp φ₀, (MulAut.conj x).surjective.comp hφ₀, ?_, ?_⟩
  · rw [← hker₀]
    ext y
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact Iff.rfl
  · have h1 : ((S : Subgroup _).map (MulAut.conj x).toMonoidHom) = (S₀ : Subgroup _) := by
      rw [← hx, Sylow.coe_subgroup_smul]
      ext y
      rw [mem_pointwise_smul_iff_inv_smul_mem, mem_map]
      constructor
      · rintro ⟨s, hs, rfl⟩
        have hs' : (MulAut.conj x)⁻¹ • ((MulAut.conj x).toMonoidHom s) = s := by
          rw [MulAut.smul_def, MulEquiv.coe_toMonoidHom, MulAut.inv_apply,
            MulEquiv.symm_apply_apply]
        rw [hs']
        exact hs
      · intro hy
        refine ⟨x⁻¹ * y * x, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
        simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hy
    rw [← map_map, ← Sylow.coe_mapSurjective hφ₀ T, h1, hS₀, comap_id]

end Cover

section Component

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_isPGroup_zpowers_of_odd {X : Type} [Group X] [Finite X] {z : X}
    (h2 : IsPGroup 2 (zpowers z)) (hodd : Odd (orderOf z)) : z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  rw [Nat.card_zpowers] at hn
  rcases n with _ | n
  · rw [pow_zero] at hn
    exact orderOf_eq_one_iff.mp hn
  · rw [hn, pow_succ] at hodd
    exact absurd hodd (by simp [Nat.odd_mul])

theorem nonempty_l34Cover_of_odd {A : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥A)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) :
    Nonempty (L34Cover ↥A) := by
  refine exists_l34Cover hq.1 hL hq.2 fun z hz h2 => ?_
  have hz1 : z = 1 := eq_one_of_isPGroup_zpowers_of_odd h2
    (hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hz))
  rw [hz1, one_pow]

omit [Finite G] in
theorem mem_normalizer_of_mem_normalizer_subgroupOf {A H : Subgroup G} (hHA : H ≤ A) {n : ↥A}
    (hn : n ∈ normalizer ((H.subgroupOf A : Subgroup ↥A) : Set ↥A)) :
    (n : G) ∈ normalizer (H : Set G) := by
  rw [← subgroupOf_normalizer_eq hHA, mem_subgroupOf] at hn
  exact hn

theorem map_centerIn_eq {A B : Type} [Group A] [Group B] [Finite A] (φ : A →* B)
    (hodd : Odd (Nat.card φ.ker)) {T : Subgroup A} (hT : IsPGroup 2 T) :
    (centerIn T).map φ = centerIn (T.map φ) := by
  apply le_antisymm
  · rintro _ ⟨t, ⟨htT, htC⟩, rfl⟩
    refine ⟨⟨t, htT, rfl⟩, ?_⟩
    show φ t ∈ centralizer ((T.map φ : Subgroup B) : Set B)
    rw [mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    have htC' : t ∈ centralizer (T : Set A) := htC
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp htC' s hs]
  · rintro _ ⟨⟨t, htT, rfl⟩, htC⟩
    refine ⟨t, ⟨htT, ?_⟩, rfl⟩
    have htC' : φ t ∈ centralizer ((T.map φ : Subgroup B) : Set B) := htC
    show t ∈ centralizer (T : Set A)
    rw [mem_centralizer_iff]
    intro s hs
    have h1 := mem_centralizer_iff.mp htC' (φ s) ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul] at h1
    exact eq_of_map_eq_of_isPGroup φ hodd hT (T.mul_mem hs htT) (T.mul_mem htT hs) h1

theorem exists_conj_eq_of_card_sixteen {A H : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥A)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) (hHA : H ≤ A)
    (hH : IsElemAbelian 2 H) (hH16 : Nat.card H = 16) {h h' : G} (hh : h ∈ H) (hh' : h' ∈ H)
    (h1 : h ≠ 1) (h1' : h' ≠ 1) : ∃ n ∈ A ⊓ normalizer (H : Set G), n * h * n⁻¹ = h' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c⟩ := nonempty_l34Cover_of_odd hq hL hodd
  have hO := oddCore_le_center hq.1 hq.2
  have hH₀ : IsPGroup 2 (H.subgroupOf A) := (isPGroup_two_of_isElemAbelian hH).comap_subtype
  obtain ⟨T, hT⟩ := hH₀.exists_le_sylow
  obtain ⟨φ, hφs, hφk, hφT⟩ := c.exists_std hO T
  have hkerodd : Odd (Nat.card φ.ker) := by rw [hφk]; exact hodd
  have hkerZ : φ.ker ≤ center ↥A := hφk.le
  have hH₀2 : ∀ x ∈ (H.subgroupOf A).map φ, x ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (by simpa using hH.2 _ (mem_subgroupOf.mp hx)),
      map_one]
  have hH₀16 : Nat.card ((H.subgroupOf A).map φ) = 16 := by
    rw [card_map_of_isPGroup φ hkerodd hH₀, ← hH16]
    exact Nat.card_congr (subgroupOfEquivOfLe hHA).toEquiv
  have hH₀U : (H.subgroupOf A).map φ ≤ projUnip c.k := hφT ▸ map_mono hT
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, (H.subgroupOf A).map φ = projRad c.k i := by
    rcases eq_projRad_of_le_projUnip c.card_k hH₀U hH₀2 hH₀16 with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  set h₀ : ↥A := ⟨h, hHA hh⟩
  set h₀' : ↥A := ⟨h', hHA hh'⟩
  have hh₀ : h₀ ∈ H.subgroupOf A := hh
  have hh₀' : h₀' ∈ H.subgroupOf A := hh'
  have hne : ∀ x ∈ H.subgroupOf A, (x : G) ≠ 1 → φ x ≠ 1 := fun x hx hx1 e =>
    hx1 (congrArg Subtype.val (eq_of_map_eq_of_isPGroup φ hkerodd hH₀ hx (one_mem _)
      (by rw [e, map_one])))
  obtain ⟨y, hyN, hy⟩ := exists_mem_normalizer_conj_eq i (hi ▸ ⟨h₀, hh₀, rfl⟩)
    (hi ▸ ⟨h₀', hh₀', rfl⟩) (hne h₀ hh₀ h1) (hne h₀' hh₀' h1')
  obtain ⟨n, rfl⟩ := hφs y
  have hnN : n ∈ normalizer ((H.subgroupOf A : Subgroup ↥A) : Set ↥A) :=
    mem_normalizer_of_map φ hkerZ hkerodd hH₀ (hi ▸ hyN)
  have hnh : n * h₀ * n⁻¹ = h₀' :=
    eq_of_map_eq_of_isPGroup φ hkerodd hH₀ ((mem_normalizer_iff.mp hnN h₀).mp hh₀) hh₀'
      (by rw [map_mul, map_mul, map_inv, hy])
  exact ⟨n, ⟨n.2, mem_normalizer_of_mem_normalizer_subgroupOf hHA hnN⟩,
    congrArg Subtype.val hnh⟩

theorem exists_torus_of_card_sixteen {A H T : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥A)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
    (hTsyl : IsSylowOf 2 T A) (hHT : H ≤ T) (hH : IsElemAbelian 2 H)
    (hH16 : Nat.card H = 16) :
    ∃ y ∈ A ⊓ normalizer (H : Set G) ⊓ normalizer (centerIn T : Set G),
      ∀ w ∈ centerIn T, y * w * y⁻¹ = w → w = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c⟩ := nonempty_l34Cover_of_odd hq hL hodd
  have hO := oddCore_le_center hq.1 hq.2
  obtain ⟨T₀, hT₀⟩ := hTsyl
  have hTA : T ≤ A := hT₀ ▸ map_subtype_le _
  have hHA : H ≤ A := hHT.trans hTA
  obtain ⟨φ, hφs, hφk, hφT⟩ := c.exists_std hO T₀
  have hkerodd : Odd (Nat.card φ.ker) := by rw [hφk]; exact hodd
  have hkerZ : φ.ker ≤ center ↥A := hφk.le
  have hTsub : T.subgroupOf A = T₀ := by
    rw [← hT₀]
    exact comap_map_eq_self_of_injective A.subtype_injective _
  have hT₀2 : IsPGroup 2 (T₀ : Subgroup ↥A) := T₀.2
  have hH₀T : H.subgroupOf A ≤ T₀ := fun x hx => hTsub ▸ (hHT (mem_subgroupOf.mp hx))
  have hH₀ : IsPGroup 2 (H.subgroupOf A) := hT₀2.to_le hH₀T
  have hsubodd : Odd (Nat.card A.subtype.ker) := by
    rw [ker_subtype, card_bot]
    exact odd_one
  have hW : (centerIn (T₀ : Subgroup ↥A)).map A.subtype = centerIn T := by
    rw [map_centerIn_eq A.subtype hsubodd hT₀2, hT₀]
  have hW₀ : (centerIn T).subgroupOf A = centerIn (T₀ : Subgroup ↥A) := by
    rw [← hW]
    exact comap_map_eq_self_of_injective A.subtype_injective _
  have hW₀2 : IsPGroup 2 ((centerIn T).subgroupOf A) := hW₀ ▸ hT₀2.to_le inf_le_left
  have hWA : centerIn T ≤ A := (inf_le_left : centerIn T ≤ T).trans hTA
  have hH₀2' : ∀ x ∈ (H.subgroupOf A).map φ, x ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (by simpa using hH.2 _ (mem_subgroupOf.mp hx)),
      map_one]
  have hH₀16 : Nat.card ((H.subgroupOf A).map φ) = 16 := by
    rw [card_map_of_isPGroup φ hkerodd hH₀, ← hH16]
    exact Nat.card_congr (subgroupOfEquivOfLe hHA).toEquiv
  have hH₀U : (H.subgroupOf A).map φ ≤ projUnip c.k := hφT ▸ map_mono hH₀T
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, (H.subgroupOf A).map φ = projRad c.k i := by
    rcases eq_projRad_of_le_projUnip c.card_k hH₀U hH₀2' hH₀16 with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  have hWφ : ((centerIn T).subgroupOf A).map φ = projCenterW c.k := by
    rw [hW₀, map_centerIn_eq φ hkerodd hT₀2, hφT, ← center_projUnip]
    ext x
    constructor
    · rintro ⟨hxU, hxC⟩
      refine ⟨⟨x, hxU⟩, mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
      exact mem_centralizer_iff.mp hxC y y.2
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      show (y : projectiveSL 3 c.k) ∈ centralizer ((projUnip c.k : Subgroup _) : Set _)
      rw [mem_centralizer_iff]
      intro z hz
      exact congrArg Subtype.val (mem_center_iff.mp hy ⟨z, hz⟩)
  obtain ⟨y, ⟨hyR, hyW⟩, hyfix⟩ := exists_torus c.card_k i
  obtain ⟨n, rfl⟩ := hφs y
  have hnH : n ∈ normalizer ((H.subgroupOf A : Subgroup ↥A) : Set ↥A) :=
    mem_normalizer_of_map φ hkerZ hkerodd hH₀ (hi ▸ hyR)
  have hnW : n ∈ normalizer (((centerIn T).subgroupOf A : Subgroup ↥A) : Set ↥A) :=
    mem_normalizer_of_map φ hkerZ hkerodd hW₀2 (hWφ ▸ hyW)
  refine ⟨n, ⟨⟨n.2, mem_normalizer_of_mem_normalizer_subgroupOf hHA hnH⟩,
    mem_normalizer_of_mem_normalizer_subgroupOf hWA hnW⟩, fun w hw hfix => ?_⟩
  set w₀ : ↥A := ⟨w, hWA hw⟩
  have hw₀ : w₀ ∈ (centerIn T).subgroupOf A := hw
  have hfix₀ : n * w₀ * n⁻¹ = w₀ := Subtype.ext hfix
  have hφw : φ w₀ = 1 := by
    refine hyfix (φ w₀) (hWφ ▸ ⟨w₀, hw₀, rfl⟩) ?_
    rw [← map_inv, ← map_mul, ← map_mul, hfix₀]
  have := eq_of_map_eq_of_isPGroup φ hkerodd hW₀2 hw₀ (one_mem _) (by rw [hφw, map_one])
  exact congrArg Subtype.val this

end Component

end CFSG.ComponentClassification.AS81
