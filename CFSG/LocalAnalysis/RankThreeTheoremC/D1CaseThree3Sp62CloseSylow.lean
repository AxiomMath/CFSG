module

import CFSG.LocalAnalysis.PreuniquenessRankFour.Confinement
import CFSG.LocalAnalysis.LyonsUnitaryFour.Fusion
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_not_mem_of_lt_three {J T : Subgroup G} (hT : IsPGroup 3 T)
    (hJT : J < T) : ∃ x ∈ T, x ∉ J ∧ x ∈ Subgroup.normalizer (J : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsNilpotent T := hT.isNilpotent
  have hlt : J.subgroupOf T < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hJT.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : T) ∈ J.subgroupOf T := by
      rw [htop]
      trivial
    exact Subgroup.mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := T) _ hlt)
  refine ⟨y, y.2, fun h => hyP (Subgroup.mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (Subgroup.normalizer (J : Set G)).subgroupOf T := by
    rw [Subgroup.subgroupOf_normalizer_eq hJT.le]
    exact hyN
  exact Subgroup.mem_subgroupOf.mp hy

theorem eq_of_isPGroup_of_fixed3 {J B : Subgroup G}
    (hJp : IsPGroup 3 J) (hJc : IsMulCommutative J)
    (hfix : ∀ n ∈ Subgroup.normalizer (J : Set G), IsPGroup 3 (Subgroup.zpowers n) →
      n ∈ Subgroup.normalizer (B : Set G) → n ∈ Subgroup.centralizer (J : Set G))
    (hSylC : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (J : Set G) → IsPGroup 3 S → J ≤ S →
      S = J)
    {T : Subgroup G} (hTC : T ≤ Subgroup.centralizer (B : Set G)) (hTp : IsPGroup 3 T)
    (hJT : J ≤ T) : T = J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  obtain ⟨t, htT, htJ, htN⟩ := exists_mem_normalizer_not_mem_of_lt_three hTp
    (lt_of_le_of_ne hJT (Ne.symm hne))
  have htcJ : t ∈ Subgroup.centralizer (J : Set G) :=
    hfix t htN (hTp.to_le (Subgroup.zpowers_le.mpr htT))
      (Subgroup.centralizer_le_normalizer _ (hTC htT))
  have hS2p : IsPGroup 3 ↥(J ⊔ Subgroup.zpowers t : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hJp (hTp.to_le (Subgroup.zpowers_le.mpr htT))
      (Subgroup.zpowers_le.mpr htN)
  have hS2C : J ⊔ Subgroup.zpowers t ≤ Subgroup.centralizer (J : Set G) :=
    sup_le (Subgroup.le_centralizer_iff_isMulCommutative.mpr hJc)
      (Subgroup.zpowers_le.mpr htcJ)
  have hEq := hSylC _ hS2C hS2p le_sup_left
  exact htJ (hEq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t))

omit [Finite G] in
theorem hfix_of_frame3 {J B : Subgroup G}
    (h48 : (Subgroup.centralizer (J : Set G)).relIndex (Subgroup.normalizer (J : Set G)) ∣ 48)
    (hBJ : B ≤ J)
    (hidx : (Subgroup.normalizer (B : Set G)).relIndex (Subgroup.normalizer (J : Set G)) = 3) :
    ∀ n ∈ Subgroup.normalizer (J : Set G), IsPGroup 3 (Subgroup.zpowers n) →
      n ∈ Subgroup.normalizer (B : Set G) → n ∈ Subgroup.centralizer (J : Set G) := by
  intro t htN hzp htB
  set N := Subgroup.normalizer (J : Set G) with hN
  set C := (Subgroup.centralizer (J : Set G)).subgroupOf N with hC
  have hCn : C.Normal := by
    rw [hC, ← Subgroup.normalizerMonoidHom_ker]
    infer_instance
  set π := QuotientGroup.mk' C with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective C
  set S := (Subgroup.normalizer (B : Set G)).subgroupOf N with hS
  have hCS : C ≤ S := by
    intro c hc
    have hcJ : (c : G) ∈ Subgroup.centralizer (J : Set G) := Subgroup.mem_subgroupOf.mp hc
    have hcB : (c : G) ∈ Subgroup.centralizer (B : Set G) :=
      Subgroup.centralizer_le (by exact hBJ) hcJ
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.centralizer_le_normalizer _ hcB)
  have htS : (⟨t, htN⟩ : N) ∈ S := Subgroup.mem_subgroupOf.mpr htB
  set AS := S.map π with hAS
  have hS' : AS.comap π = S := by
    rw [hAS, Subgroup.comap_map_eq π S, hπ, QuotientGroup.ker_mk', sup_eq_left.mpr hCS]
  have hind : AS.index = 3 := by
    have := Subgroup.index_comap_of_surjective AS hπs
    rw [hS'] at this
    rw [← this]
    exact hidx
  have hQ : Nat.card AS * 3 ∣ 48 := by
    have := Subgroup.card_mul_index AS
    rw [hind] at this
    rw [this]
    exact h48
  have hAS16 : Nat.card AS ∣ 16 := by
    have : Nat.card AS * 3 ∣ 16 * 3 := by simpa using hQ
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
  obtain ⟨k, hk⟩ := hzp ⟨t, Subgroup.mem_zpowers t⟩
  have hτ3 : (π ⟨t, htN⟩) ^ 3 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨t, htN⟩ : N) ^ 3 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hτAS : π ⟨t, htN⟩ ∈ AS := Subgroup.mem_map_of_mem π htS
  have hord1 : orderOf (π ⟨t, htN⟩) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hτ3
  have hord2 : orderOf (π ⟨t, htN⟩) ∣ 16 := by
    have h1 : orderOf (⟨π ⟨t, htN⟩, hτAS⟩ : AS) ∣ Nat.card AS := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact h1.trans hAS16
  have hτ : orderOf (π ⟨t, htN⟩) = 1 := by
    have hcop : Nat.Coprime (3 ^ k) 16 := Nat.Coprime.pow_left k (by norm_num)
    exact Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hord1 hord2)
  have htC : (⟨t, htN⟩ : N) ∈ C := (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp hτ)
  exact Subgroup.mem_subgroupOf.mp htC

structure ElemFrame3 (P J B : Subgroup G) : Prop where
  le_P : J ≤ P
  elem : IsElemAbelian 3 J
  card_J : Nat.card J = 3 ^ 3
  le_J : B ≤ J
  card_B : Nat.card B = 3
  unique : ∀ J' : Subgroup G, J' ≤ P → IsElemAbelian 3 J' → Nat.card J' = 3 ^ 3 → J' = J
  cent : P ⊓ Subgroup.centralizer (J : Set G) ≤ J

theorem sylow_of_elemFrame3 {P : Sylow 3 G} {J B : Subgroup G}
    (hF : ElemFrame3 (P : Subgroup G) J B)
    (h48 : (Subgroup.centralizer (J : Set G)).relIndex (Subgroup.normalizer (J : Set G)) ∣ 48)
    (hidx : (Subgroup.normalizer (B : Set G)).relIndex (Subgroup.normalizer (J : Set G)) = 3) :
    ∀ T : Subgroup G, T ≤ Subgroup.centralizer (B : Set G) → IsPGroup 3 T → J ≤ T → T = J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJp : IsPGroup 3 J := IsPGroup.of_card hF.card_J
  have hJc : IsMulCommutative J := hF.elem.1
  refine fun T hTC hTp hJT => eq_of_isPGroup_of_fixed3 hJp hJc
    (hfix_of_frame3 h48 hF.le_J hidx) ?_ hTC hTp hJT
  intro S hSC hSp hJS
  obtain ⟨c, -, hc⟩ := CFSG.LyonsUnitaryFour.exists_conj_le_sylow_of_le P (H := ⊤) le_top
    le_top hSp
  set J' := J.map (MulAut.conj c).toMonoidHom with hJ'
  have hJ'P : J' ≤ (P : Subgroup G) := by
    rintro _ ⟨j, hj, rfl⟩
    exact hc j (hJS hj)
  have hJ'e : IsElemAbelian 3 J' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hF.elem
      (MulAut.conj c).toMonoidHom
  have hJ'card : Nat.card J' = 3 ^ 3 := by
    rw [hJ', Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact hF.card_J
  have hJ'J : J' = J := hF.unique J' hJ'P hJ'e hJ'card
  refine le_antisymm (fun s hs => ?_) hJS
  have hsP : c * s * c⁻¹ ∈ (P : Subgroup G) := hc s hs
  have hsC : c * s * c⁻¹ ∈ Subgroup.centralizer (J' : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨j, hj, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp (hSC hs) j hj
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * j * c⁻¹ * (c * s * c⁻¹) = c * (j * s) * c⁻¹ := by group
      _ = c * (s * j) * c⁻¹ := by rw [this]
      _ = c * s * c⁻¹ * (c * j * c⁻¹) := by group
  rw [hJ'J] at hsC
  have hsJ : c * s * c⁻¹ ∈ J := hF.cent ⟨hsP, hsC⟩
  rw [← hJ'J] at hsJ
  obtain ⟨j, hj, hjs⟩ := hsJ
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hjs
  have : j = s := by
    have h1 : c * j * c⁻¹ = c * s * c⁻¹ := hjs
    simpa using h1
  exact this ▸ hj

theorem relIndex_eq_of_cover3 {N A C S : Subgroup G} (hAN : A ≤ N) (hCS : C ≤ S)
    [hCn : (C.subgroupOf N).Normal] (hcard : C.relIndex N ∣ C.relIndex A) :
    S.relIndex N = S.relIndex A := by
  set C' := C.subgroupOf N with hC'
  let φ : ↥A →* ↥N ⧸ C' := (QuotientGroup.mk' C').comp (Subgroup.inclusion hAN)
  have hker : φ.ker = C.subgroupOf A := by
    ext a
    simp only [MonoidHom.mem_ker, φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hC', Subgroup.coe_inclusion]
  have hrange : Nat.card φ.range = Nat.card (↥A ⧸ C.subgroupOf A) := by
    rw [← hker]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv).symm
  have hle : Nat.card φ.range ≤ Nat.card (↥N ⧸ C') := Subgroup.card_le_card_group _
  have hpos : 0 < Nat.card φ.range := Nat.card_pos
  have hrange_eq : Nat.card φ.range = Nat.card (↥N ⧸ C') :=
    le_antisymm hle (Nat.le_of_dvd hpos (hrange ▸ hcard))
  have htop : φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ hrange_eq
  have hsurj : ∀ n ∈ N, ∃ a ∈ A, a⁻¹ * n ∈ C := by
    intro n hn
    have hmem : (QuotientGroup.mk (⟨n, hn⟩ : ↥N) : ↥N ⧸ C') ∈ φ.range := by
      rw [htop]; trivial
    obtain ⟨a, ha⟩ := hmem
    refine ⟨a, a.2, ?_⟩
    have h1 : (QuotientGroup.mk' C') (Subgroup.inclusion hAN a) =
        QuotientGroup.mk (⟨n, hn⟩ : ↥N) := ha
    have h2 := (QuotientGroup.eq (s := C')).mp h1
    simpa [hC', Subgroup.mem_subgroupOf] using h2
  let F : ↥A ⧸ (A ⊓ S).subgroupOf A → ↥N ⧸ (N ⊓ S).subgroupOf N :=
    Quotient.map' (fun a : ↥A => (⟨a, hAN a.2⟩ : ↥N)) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hab ⊢
      exact ⟨N.mul_mem (N.inv_mem (hAN a.2)) (hAN b.2), hab.2⟩)
  have hF : Function.Bijective F := by
    constructor
    · intro x y
      induction x using Quotient.inductionOn' with | _ a => ?_
      induction y using Quotient.inductionOn' with | _ b => ?_
      intro hxy
      have h1 : Quotient.mk'' (⟨a, hAN a.2⟩ : ↥N) = (Quotient.mk'' (⟨b, hAN b.2⟩ : ↥N) :
          ↥N ⧸ (N ⊓ S).subgroupOf N) := hxy
      have h2 := Quotient.exact' h1
      rw [QuotientGroup.leftRel_apply] at h2
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply]
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h2 ⊢
      exact ⟨A.mul_mem (A.inv_mem a.2) b.2, h2.2⟩
    · intro y
      induction y using Quotient.inductionOn' with | _ n => ?_
      obtain ⟨a, haA, hc⟩ := hsurj n n.2
      refine ⟨Quotient.mk'' (⟨a, haA⟩ : ↥A), ?_⟩
      show Quotient.mk'' (⟨a, hAN haA⟩ : ↥N) = Quotient.mk'' n
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply]
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact ⟨N.mul_mem (N.inv_mem (hAN haA)) n.2, hCS hc⟩
  have h := Nat.card_congr (Equiv.ofBijective F hF)
  have h' : (N ⊓ S).relIndex N = (A ⊓ S).relIndex A := by
    simpa [Subgroup.relIndex, Subgroup.index] using h.symm
  rwa [inf_comm N S, Subgroup.inf_relIndex_right, inf_comm A S, Subgroup.inf_relIndex_right]
    at h'

end CFSG.LocalAnalysis.RankThreeTheoremC
