module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Cover59
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm32Tools

public section

namespace CFSG.ComponentClassification.TBLit.L34FU

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.GrSLit

variable {X : Type} [Group X]

theorem conj_mem_zStarIn {J : Subgroup X} {j z : X} (hj : j ∈ J) (hz : z ∈ zStarIn J) :
    j * z * j⁻¹ ∈ zStarIn J := by
  obtain ⟨z', hz', rfl⟩ := hz
  exact ⟨⟨j, hj⟩ * z' * ⟨j, hj⟩⁻¹, (Open.fusionZStar_normal ↥J).conj_mem z' hz' ⟨j, hj⟩, by simp⟩

theorem conj_mem_oddIn {J : Subgroup X} {j d : X} (hj : j ∈ J) (hd : d ∈ oddIn J) :
    j * d * j⁻¹ ∈ oddIn J := by
  obtain ⟨d', hd', rfl⟩ := hd
  have hn : (pPrimeCore 2 ↥J).Normal := inferInstance
  exact ⟨⟨j, hj⟩ * d' * ⟨j, hj⟩⁻¹, hn.conj_mem d' hd' ⟨j, hj⟩, by simp⟩

theorem oddIn_le_zStarIn (J : Subgroup X) : oddIn J ≤ zStarIn J := by
  intro o ho
  rw [zStarIn, GSThmB.map_fusionZStar_eq]
  have hoJ : o ∈ J := map_subtype_le _ ho
  refine mem_inf.mpr ⟨hoJ, mem_coreActionKernel.mpr ⟨le_normalizer hoJ, fun j hj => ?_⟩⟩
  have h1 := conj_mem_oddIn (inv_mem hj) (inv_mem ho)
  rw [inv_inv] at h1
  exact mul_mem h1 ho

theorem normalizer_le_normalizer_zStarIn (J : Subgroup X) :
    normalizer (J : Set X) ≤ normalizer (zStarIn J : Set X) :=
  UnbalancedGS.normalizer_le_normalizer_map_of_characteristic J (Open.fusionZStar ↥J)

variable [Finite X]

theorem zStarIn_le_of_sup {K₀ K : Subgroup X} (hle : K₀ ≤ K) (hsup : K₀ ⊔ oddIn K = K) :
    zStarIn K₀ ≤ zStarIn K := by
  have hO : oddIn K₀ ≤ oddIn K := FooteLit.oddCoreIn_le_of_sup hle hsup
  have hKN : K₀ ≤ normalizer ((oddIn K : Subgroup X) : Set X) := fun k hk =>
    GrS5.normalizer_le_normalizer_oddIn K (le_normalizer (hle hk))
  intro z hz
  rw [zStarIn, GSThmB.map_fusionZStar_eq] at hz ⊢
  obtain ⟨hzK₀, hzC⟩ := mem_inf.mp hz
  obtain ⟨-, hzC⟩ := mem_coreActionKernel.mp hzC
  refine mem_inf.mpr ⟨hle hzK₀, mem_coreActionKernel.mpr ⟨le_normalizer (hle hzK₀), ?_⟩⟩
  intro k hk
  have hk' : k ∈ ((K₀ ⊔ oddIn K : Subgroup X) : Set X) := by rw [hsup]; exact hk
  rw [coe_mul_of_left_le_normalizer_right K₀ (oddIn K) hKN] at hk'
  obtain ⟨k₀, hk₀, o, ho, rfl⟩ := hk'
  have h1 : k₀⁻¹ * z⁻¹ * k₀ * z ∈ oddIn K := hO (hzC k₀ hk₀)
  have hzK : z ∈ K := hle hzK₀
  have h2 : z⁻¹ * o * z ∈ oddIn K := by
    have := conj_mem_oddIn (inv_mem hzK) ho
    rwa [inv_inv] at this
  have e : (k₀ * o)⁻¹ * z⁻¹ * (k₀ * o) * z = o⁻¹ * (k₀⁻¹ * z⁻¹ * k₀ * z) * (z⁻¹ * o * z) := by
    group
  rw [e]
  exact mul_mem (mul_mem (inv_mem ho) h1) h2

theorem inf_zStarIn_eq {K₀ K : Subgroup X} (hle : K₀ ≤ K) (hsup : K₀ ⊔ oddIn K = K) :
    K₀ ⊓ zStarIn K = zStarIn K₀ :=
  le_antisymm (GrS5.inf_zStarIn_le_zStarIn_of_le hle)
    (le_inf (map_subtype_le _) (zStarIn_le_of_sup hle hsup))

omit [Finite X] in
@[expose] def commZStar (J : Subgroup X) (x : X) : Subgroup X where
  carrier := {j | j ∈ J ∧ j⁻¹ * x⁻¹ * j * x ∈ zStarIn J}
  one_mem' := ⟨J.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨haJ, ha⟩ ⟨hbJ, hb⟩
    refine ⟨J.mul_mem haJ hbJ, ?_⟩
    have e : (a * b)⁻¹ * x⁻¹ * (a * b) * x =
        b⁻¹ * (a⁻¹ * x⁻¹ * a * x) * b⁻¹⁻¹ * (b⁻¹ * x⁻¹ * b * x) := by group
    rw [e]
    exact mul_mem (conj_mem_zStarIn (inv_mem hbJ) ha) hb
  inv_mem' := by
    rintro a ⟨haJ, ha⟩
    refine ⟨J.inv_mem haJ, ?_⟩
    have e : a⁻¹⁻¹ * x⁻¹ * a⁻¹ * x = a * (a⁻¹ * x⁻¹ * a * x)⁻¹ * a⁻¹ := by group
    rw [e]
    exact conj_mem_zStarIn haJ (inv_mem ha)

omit [Finite X] in
theorem mem_commZStar {J : Subgroup X} {x j : X} :
    j ∈ commZStar J x ↔ j ∈ J ∧ j⁻¹ * x⁻¹ * j * x ∈ zStarIn J :=
  Iff.rfl

omit [Finite X] in
theorem card_subtype_eq_card_commZStar (J : Subgroup X) (x : X) :
    Nat.card {j : J // (j : X)⁻¹ * x⁻¹ * j * x ∈ zStarIn J} = Nat.card (commZStar J x) :=
  Nat.card_congr
    { toFun := fun j => ⟨j.1, j.1.2, j.2⟩
      invFun := fun j => ⟨⟨j.1, j.2.1⟩, j.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

omit [Finite X] in
theorem zStarIn_le_commZStar {J : Subgroup X} {x : X} (hx : x ∈ normalizer (J : Set X)) :
    zStarIn J ≤ commZStar J x := by
  intro z hz
  refine ⟨map_subtype_le _ hz, ?_⟩
  have h1 : x⁻¹ * z * x ∈ zStarIn J := by
    have := (mem_normalizer_iff.mp (normalizer_le_normalizer_zStarIn J (inv_mem hx)) z).mp hz
    rwa [inv_inv] at this
  rw [show z⁻¹ * x⁻¹ * z * x = z⁻¹ * (x⁻¹ * z * x) by group]
  exact mul_mem (inv_mem hz) h1

theorem commZStar_eq_sup {K₀ K : Subgroup X} (hle : K₀ ≤ K) (hsup : K₀ ⊔ oddIn K = K) {x : X}
    (hxK : x ∈ normalizer (K : Set X)) (hxK₀ : x ∈ normalizer (K₀ : Set X)) :
    commZStar K x = commZStar K₀ x ⊔ zStarIn K := by
  have hZ := inf_zStarIn_eq hle hsup
  have hKN : K₀ ≤ normalizer ((oddIn K : Subgroup X) : Set X) := fun k hk =>
    GrS5.normalizer_le_normalizer_oddIn K (le_normalizer (hle hk))
  apply le_antisymm
  · intro j hj
    obtain ⟨hjK, hj⟩ := mem_commZStar.mp hj
    have hj' : j ∈ ((K₀ ⊔ oddIn K : Subgroup X) : Set X) := by rw [hsup]; exact hjK
    rw [coe_mul_of_left_le_normalizer_right K₀ (oddIn K) hKN] at hj'
    obtain ⟨k₀, hk₀, o, ho, rfl⟩ := hj'
    have hoZ : o ∈ zStarIn K := oddIn_le_zStarIn K ho
    have hoK : o ∈ K := map_subtype_le _ ho
    have hox : o⁻¹ * x⁻¹ * o * x ∈ zStarIn K := (zStarIn_le_commZStar hxK hoZ).2
    have hk₀x : k₀⁻¹ * x⁻¹ * k₀ * x ∈ zStarIn K := by
      have e : k₀⁻¹ * x⁻¹ * k₀ * x = o * (((k₀ * o)⁻¹ * x⁻¹ * (k₀ * o) * x) *
          (o⁻¹ * x⁻¹ * o * x)⁻¹) * o⁻¹ := by group
      rw [e]
      exact conj_mem_zStarIn hoK (mul_mem hj (inv_mem hox))
    have hk₀xK₀ : k₀⁻¹ * x⁻¹ * k₀ * x ∈ K₀ := by
      have h1 : x⁻¹ * k₀ * x ∈ K₀ := by
        have := (mem_normalizer_iff.mp (inv_mem hxK₀) k₀).mp hk₀
        rwa [inv_inv] at this
      rw [show k₀⁻¹ * x⁻¹ * k₀ * x = k₀⁻¹ * (x⁻¹ * k₀ * x) by group]
      exact mul_mem (inv_mem hk₀) h1
    have hk₀Z : k₀⁻¹ * x⁻¹ * k₀ * x ∈ zStarIn K₀ := hZ ▸ mem_inf.mpr ⟨hk₀xK₀, hk₀x⟩
    exact mul_mem_sup ⟨hk₀, hk₀Z⟩ hoZ
  · refine sup_le (fun j hj => ⟨hle hj.1, zStarIn_le_of_sup hle hsup hj.2⟩)
      (zStarIn_le_commZStar hxK)

theorem card_commZStar_mul {K₀ K : Subgroup X} (hle : K₀ ≤ K) (hsup : K₀ ⊔ oddIn K = K)
    {x : X} (hxK : x ∈ normalizer (K : Set X)) (hxK₀ : x ∈ normalizer (K₀ : Set X)) :
    Nat.card (commZStar K x) * Nat.card (zStarIn K₀) =
      Nat.card (commZStar K₀ x) * Nat.card (zStarIn K) := by
  have hZ := inf_zStarIn_eq hle hsup
  have hF := commZStar_eq_sup hle hsup hxK hxK₀
  have hAK : commZStar K₀ x ≤ K := fun j hj => hle hj.1
  have hZK : zStarIn K ≤ K := map_subtype_le _
  set A : Subgroup ↥K := (commZStar K₀ x).subgroupOf K with hA
  set Zs : Subgroup ↥K := (zStarIn K).subgroupOf K with hZs
  have hZsn : Zs.Normal := by
    rw [hZs, zStarIn, ← comap_subtype, comap_map_eq_self_of_injective K.subtype_injective]
    infer_instance
  have hinf : zStarIn K ⊓ commZStar K₀ x = zStarIn K₀ := by
    apply le_antisymm
    · intro z hz
      rw [← hZ]
      exact mem_inf.mpr ⟨(mem_inf.mp hz).2.1, (mem_inf.mp hz).1⟩
    · exact le_inf (zStarIn_le_of_sup hle hsup) (zStarIn_le_commZStar hxK₀)
  have hrel := relIndex_sup_right A Zs
  have hcardK : ∀ H : Subgroup ↥K, Nat.card ↥(H.map K.subtype) = Nat.card H := fun H =>
    card_map_of_injective K.subtype_injective
  have hmapA : A.map K.subtype = commZStar K₀ x := by
    rw [hA, subgroupOf_map_subtype, inf_eq_left.mpr hAK]
  have hmapZ : Zs.map K.subtype = zStarIn K := by
    rw [hZs, subgroupOf_map_subtype, inf_eq_left.mpr hZK]
  have hmapF : (A ⊔ Zs).map K.subtype = commZStar K x := by
    rw [Subgroup.map_sup, hmapA, hmapZ, hF]
  have hmapI : (Zs ⊓ A).map K.subtype = zStarIn K₀ := by
    rw [Subgroup.map_inf _ _ _ K.subtype_injective, hmapA, hmapZ, hinf]
  have h1 := relIndex_mul_card Zs (A ⊔ Zs)
  rw [inf_eq_left.mpr (le_sup_right : Zs ≤ A ⊔ Zs)] at h1
  have h2 := relIndex_mul_card Zs A
  rw [← hmapF, ← hmapA, ← hmapI, ← hmapZ, hcardK, hcardK, hcardK, hcardK, ← h1, ← h2, hrel]
  ring

end CFSG.ComponentClassification.TBLit.L34FU
