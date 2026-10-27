module

public import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.ComponentClassification.GSThmB.CF24

open CFSG Subgroup

variable {L P : Type*} [Group L] [Group P]

theorem conj_mem_map_fix (Q : L →* P) (α : MulAut L) (t : P)
    (hQα : ∀ x, Q (α x) = t * Q x * t⁻¹) (hker : Q.ker ≤ center L) (F : Subgroup L)
    (hF : ∀ y, y ∈ F ↔ α y = y) {g : P} (hgQ : g ∈ Q.range) (hgt : g * t = t * g) {f : P}
    (hf : f ∈ F.map Q) : g * f * g⁻¹ ∈ F.map Q := by
  obtain ⟨x, rfl⟩ := hgQ
  obtain ⟨y, hy, rfl⟩ := hf
  have hz : x⁻¹ * α x ∈ center L := by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hQα, ← hgt]
    group
  refine ⟨x * y * x⁻¹, (hF _).2 ?_, by rw [map_mul, map_mul, map_inv]⟩
  have hαx : α x = x * (x⁻¹ * α x) := by group
  have hzc := mem_center_iff.mp hz y
  rw [map_mul, map_mul, map_inv, (hF y).1 hy, hαx]
  calc x * (x⁻¹ * α x) * y * (x * (x⁻¹ * α x))⁻¹ =
      x * ((x⁻¹ * α x) * y) * (x⁻¹ * α x)⁻¹ * x⁻¹ := by group
    _ = x * y * x⁻¹ := by rw [← hzc]; group

theorem isSubnormal_map_subgroupOf (Q : L →* P) {F K : Subgroup L} (hKF : K ≤ F)
    (hsn : (K.subgroupOf F).IsSubnormal) {C : Subgroup P} (hFC : F.map Q ≤ C)
    (hnorm : ((F.map Q).subgroupOf C).Normal) : ((K.map Q).subgroupOf C).IsSubnormal := by
  set R := (F.map Q).subgroupOf C with hR
  set H := (K.map Q).subgroupOf C with hH
  have hHR : H ≤ R := fun y hy => by
    rw [hH, mem_subgroupOf] at hy
    rw [hR, mem_subgroupOf]
    exact map_mono hKF hy
  let ψ : F →* R :=
    { toFun := fun f => ⟨⟨Q f, hFC (mem_map_of_mem Q f.2)⟩, by
        rw [hR, mem_subgroupOf]
        exact mem_map_of_mem Q f.2⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        apply Subtype.ext
        simp }
  have hψ : Function.Surjective ψ := by
    rintro ⟨⟨r, hrC⟩, hr⟩
    rw [hR, mem_subgroupOf] at hr
    obtain ⟨y, hy, hyr⟩ := hr
    exact ⟨⟨y, hy⟩, Subtype.ext (Subtype.ext hyr)⟩
  have heq : (K.subgroupOf F).map ψ = H.subgroupOf R := by
    ext r
    constructor
    · rintro ⟨f, hf, rfl⟩
      rw [mem_subgroupOf, hH, mem_subgroupOf]
      exact mem_map_of_mem Q (mem_subgroupOf.1 hf)
    · intro hr
      rw [mem_subgroupOf, hH, mem_subgroupOf] at hr
      obtain ⟨k, hk, hkr⟩ := hr
      exact ⟨⟨k, hKF hk⟩, mem_subgroupOf.2 hk, Subtype.ext (Subtype.ext hkr)⟩
  have h1 : (H.subgroupOf R).IsSubnormal := heq ▸ hsn.map hψ
  exact IsSubnormal.trans hHR h1 hnorm.isSubnormal

@[expose] def toMap (Q : L →* P) (K : Subgroup L) : K →* K.map Q :=
  (Q.comp K.subtype).codRestrict (K.map Q) fun k => mem_map_of_mem Q k.2

theorem toMap_surjective (Q : L →* P) (K : Subgroup L) : Function.Surjective (toMap Q K) := by
  rintro ⟨_, ⟨k, hk, rfl⟩⟩
  exact ⟨⟨k, hk⟩, rfl⟩

theorem ker_toMap_le (Q : L →* P) (hker : Q.ker ≤ center L) (K : Subgroup L) :
    (toMap Q K).ker ≤ center K := by
  intro k hk
  have hk' : (k : L) ∈ Q.ker := by
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val hk
  rw [mem_center_iff]
  intro g
  exact Subtype.ext (mem_center_iff.mp (hker hk') g)

theorem exists_toMap_ne_one (Q : L →* P) (hker : Q.ker ≤ center L) {K : Subgroup L}
    (hK : IsQuasisimple K) : ∃ k, toMap Q K k ≠ 1 := by
  by_contra h
  push Not at h
  have hc : ∀ k : K, k ∈ center K := fun k => ker_toMap_le Q hker K (h k)
  obtain ⟨-, -, a, b, hab⟩ := hK
  apply hab
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp (hc b) a]

theorem isQuasisimple_map (Q : L →* P) (hker : Q.ker ≤ center L) {K : Subgroup L}
    (hK : IsQuasisimple K) : IsQuasisimple (K.map Q) :=
  LieType.CurtisTits.isQuasisimple_of_surjective hK (toMap_surjective Q K)
    (exists_toMap_ne_one Q hker hK)

theorem card_map_quotient_center (Q : L →* P) (hker : Q.ker ≤ center L) {K : Subgroup L}
    (hK : IsQuasisimple K) :
    Nat.card (K.map Q ⧸ center (K.map Q)) = Nat.card (K ⧸ center K) :=
  (Nat.card_congr (LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hK
    (toMap_surjective Q K) (ker_toMap_le Q hker K)).toEquiv).symm

theorem map_center_eq (Q : L →* P) (hker : Q.ker ≤ center L) {K : Subgroup L}
    (hK : IsQuasisimple K) : center (K.map Q) = (center K).map (toMap Q K) :=
  LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hK (toMap_surjective Q K)
    (ker_toMap_le Q hker K)

end CFSG.ComponentClassification.GSThmB.CF24
