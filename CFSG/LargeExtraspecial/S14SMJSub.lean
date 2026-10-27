module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.S3Basic
public import CFSG.LargeExtraspecial.Transport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMJ

open Subgroup

variable {G : Type} [Group G] (S : Setting G) (K : Subgroup G) (hzK : S.z ∈ K)

@[expose] def zK : K := ⟨S.z, hzK⟩

abbrev CK : Subgroup K := centralizer ({zK S K hzK} : Set K)

@[expose] def ιK : CK S K hzK →* G := K.subtype.comp (CK S K hzK).subtype

theorem ιK_injective : Function.Injective (ιK S K hzK) :=
  K.subtype_injective.comp (CK S K hzK).subtype_injective

theorem mem_CK_iff {x : K} : x ∈ CK S K hzK ↔ (x : G) ∈ S.M := by
  rw [mem_centralizer_singleton_iff, S.mem_M_iff]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem ιK_mem_M (c : CK S K hzK) : ιK S K hzK c ∈ S.M := (mem_CK_iff S K hzK).mp c.2

@[expose] def QK : Subgroup (CK S K hzK) := S.QG.comap (ιK S K hzK)

theorem map_QK : (QK S K hzK).map (ιK S K hzK) = S.QG ⊓ K := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨c, hc, rfl⟩
    exact ⟨hc, (c : K).2⟩
  · rintro x ⟨hxQ, hxK⟩
    exact ⟨⟨⟨x, hxK⟩, (mem_CK_iff S K hzK).mpr (S.QG_le_M hxQ)⟩, hxQ, rfl⟩

@[expose] noncomputable def QKEquiv : QK S K hzK ≃* ↥(S.QG ⊓ K) :=
  ((QK S K hzK).equivMapOfInjective (ιK S K hzK) (ιK_injective S K hzK)).trans
    (MulEquiv.subgroupCongr (map_QK S K hzK))

@[expose] noncomputable def conjCK (m : G) (hmK : m ∈ K) (hm : m ∈ S.M) :
    CK S K hzK ≃* CK S K hzK where
  toFun c := ⟨⟨m * c * m⁻¹, K.mul_mem (K.mul_mem hmK (c : K).2) (K.inv_mem hmK)⟩,
    (mem_CK_iff S K hzK).mpr (S.M.mul_mem (S.M.mul_mem hm (ιK_mem_M S K hzK c)) (S.M.inv_mem hm))⟩
  invFun c := ⟨⟨m⁻¹ * c * m, K.mul_mem (K.mul_mem (K.inv_mem hmK) (c : K).2) hmK⟩,
    (mem_CK_iff S K hzK).mpr (S.M.mul_mem (S.M.mul_mem (S.M.inv_mem hm) (ιK_mem_M S K hzK c)) hm)⟩
  left_inv c := Subtype.ext (Subtype.ext (by
    change m⁻¹ * (m * ((c : K) : G) * m⁻¹) * m = ((c : K) : G)
    group))
  right_inv c := Subtype.ext (Subtype.ext (by
    change m * (m⁻¹ * ((c : K) : G) * m) * m⁻¹ = ((c : K) : G)
    group))
  map_mul' a b := Subtype.ext (Subtype.ext (by
    change m * (((a : K) : G) * ((b : K) : G)) * m⁻¹ =
      m * ((a : K) : G) * m⁻¹ * (m * ((b : K) : G) * m⁻¹)
    group))

section Sub

variable (hext : IsExtraspecialPGroup 2 ↥(S.QG ⊓ K))
  (hcent : ∀ c ∈ K, c ∈ S.M → (∀ q ∈ S.QG ⊓ K, c * q = q * c) → c ∈ S.QG)
  (hO2 : ∀ P : Subgroup G, P ≤ K ⊓ S.M → (∀ c ∈ K ⊓ S.M, ∀ p ∈ P, c * p * c⁻¹ ∈ P) →
    IsPGroup 2 P → P ≤ S.QG)

@[expose] noncomputable def subSetting : Setting K where
  z := zK S K hzK
  orderOf_z := by
    rw [zK, Subgroup.orderOf_mk]
    exact S.orderOf_z
  Q := QK S K hzK
  normal := ⟨fun x hx c => by
    change ιK S K hzK (c * x * c⁻¹) ∈ S.QG
    rw [map_mul, map_mul, map_inv]
    exact S.conj_mem_QG (ιK_mem_M S K hzK c) hx⟩
  extraspecial :=
    CFSG.LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv (QKEquiv S K hzK).symm hext
  centralizer_le := by
    intro c hc
    change ιK S K hzK c ∈ S.QG
    refine hcent _ (c : K).2 (ιK_mem_M S K hzK c) fun q hq => ?_
    obtain ⟨q', hq', rfl⟩ : q ∈ (QK S K hzK).map (ιK S K hzK) := by
      rw [map_QK]
      exact hq
    have := mem_centralizer_iff.mp hc q' hq'
    rw [← map_mul, ← map_mul, this]
  le_of_normal := by
    intro P hP hP2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set R := CFSG.pCore 2 (CK S K hzK) with hR
    have hPR : P ≤ R := le_sSup ⟨hP, hP2⟩
    have hle : R.map (ιK S K hzK) ≤ S.QG := by
      refine hO2 _ ?_ ?_ (CFSG.pCore_isPGroup.map _)
      · rintro _ ⟨c, -, rfl⟩
        exact ⟨(c : K).2, ιK_mem_M S K hzK c⟩
      · rintro m ⟨hmK, hm⟩ _ ⟨c, hc, rfl⟩
        have hmap := CFSG.pCore_map_iso 2 (conjCK S K hzK m hmK hm)
        refine ⟨conjCK S K hzK m hmK hm c, ?_, rfl⟩
        rw [← hR] at hmap
        rw [← hmap]
        exact ⟨c, hc, rfl⟩
    intro c hc
    exact hle ⟨c, hPR hc, rfl⟩

theorem mem_subSetting_QG_iff {x : K} :
    x ∈ (subSetting S K hzK hext hcent hO2).QG ↔ (x : G) ∈ S.QG := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact hc
  · intro hx
    exact ⟨⟨x, (mem_CK_iff S K hzK).mpr (S.QG_le_M hx)⟩, hx, rfl⟩

theorem mem_subSetting_M_iff {x : K} :
    x ∈ (subSetting S K hzK hext hcent hO2).M ↔ (x : G) ∈ S.M :=
  mem_CK_iff S K hzK

theorem card_subSetting_Q :
    Nat.card (subSetting S K hzK hext hcent hO2).Q = Nat.card ↥(S.QG ⊓ K) :=
  Nat.card_congr (QKEquiv S K hzK).toEquiv

theorem subSetting_width [Finite G] {n : ℕ} (hn : Nat.card ↥(S.QG ⊓ K) = 2 ^ (1 + 2 * n)) :
    (subSetting S K hzK hext hcent hO2).width = n :=
  (subSetting S K hzK hext hcent hO2).width_eq (by rw [card_subSetting_Q]; exact hn)

end Sub

end CFSG.LargeExtraspecial.S14.SMJ
