module

public import CFSG.CGT.Stroth77.Section226I
public import CFSG.CGT.Stroth77.Section226Z2Z8End

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

namespace StrothTypeIndex

private theorem m_eq_n_or_family (τ : StrothTypeIndex) :
    τ.m = τ.n ∨ τ.m + 1 = τ.n ∨ τ.m + 2 = τ.n := by
  cases τ <;> simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type100.k,
    Type101.k, Type110.k, Type111.k, Type120.k, Type121.k, Type130.k, Type131.k, Type200.k,
    Type201.k, Type210.k, Type211.k, Type220.k, Type221.k, Type230.k, Type231.k, Type300.k,
    Type310.k, Type32x.k, Type321.k, Type331.k]

private theorem eq_t200_one_or_t201_one (τ : StrothTypeIndex) (hm : τ.m = 1) (hn : τ.n = 3) :
    τ = .t200 1 ∨ τ = .t201 1 := by
  cases τ <;> simp_all [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type100.k,
    Type101.k, Type110.k, Type111.k, Type120.k, Type121.k, Type130.k, Type131.k, Type200.k,
    Type201.k, Type210.k, Type211.k, Type220.k, Type221.k, Type230.k, Type231.k, Type300.k,
    Type310.k, Type32x.k, Type321.k, Type331.k] <;> omega

end StrothTypeIndex

namespace StrothFrame.IsD

theorem stroth_2_26_frame_of_H4
    (H4 : (∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
        {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD → τ.m + 1 = τ.n →
        2 ≤ τ.m →
        IsSylowIn 2 (Subgroup.normalizer (D : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
        ∀ (k : ℕ), k ≤ τ.n - 1 → ∀ (B : Subgroup G),
          B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
            Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) →
          Nonempty (Additive ↥B ≃+ (ZMod (2 ^ k) × ZMod (2 ^ (k + 1)) × ZMod (2 ^ (k + 1)))) →
          B ≤ D) →
      (∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
        {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD → τ.m + 2 = τ.n →
        2 ≤ τ.m →
        IsSylowIn 2 (Subgroup.normalizer (D : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
        ∀ (k : ℕ), k ≤ τ.n - 2 → ∀ (B : Subgroup G),
          B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
            Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) →
          Nonempty (Additive ↥B ≃+ (ZMod (2 ^ k) × ZMod (2 ^ (k + 2)) × ZMod (2 ^ (k + 2)))) →
          B ≤ Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G)) →
      (∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
        {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD → τ.m + 2 = τ.n →
        2 ≤ τ.m →
        IsSylowIn 2 (Subgroup.normalizer (D : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
            Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) ≠ D →
        ∃ s ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
            Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G),
          (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
              Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) ⊓
              Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) =
            D ⊔ Subgroup.zpowers s ∧
          s * s = (dD.c : G) ∧ ⁅Subgroup.zpowers s, D⁆ = ⁅Subgroup.zpowers dD.ρ, omegaIn 1 D⁆) →
      ∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
        {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD →
        IsSylowIn 2 (Subgroup.normalizer (D : Set G))
          ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
        τ.m + 1 = τ.n ∨ τ.m + 2 = τ.n → 2 ≤ τ.m → ∀ {B : Subgroup G},
        B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) →
        D ≤ Subgroup.normalizer (B : Set G) → B ≠ D →
        (∃ g : G, B = D.map (MulAut.conj g).toMonoidHom) → False)
    (H2b : ∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
      {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD → τ.m + 1 = τ.n →
      2 ≤ τ.m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      ∀ (k : ℕ), k ≤ τ.n - 1 → ∀ (B : Subgroup G),
        B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) →
        Nonempty (Additive ↥B ≃+ (ZMod (2 ^ k) × ZMod (2 ^ (k + 1)) × ZMod (2 ^ (k + 1)))) →
        B ≤ D)
    (H3two : ∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
      {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD → τ.m + 2 = τ.n →
      2 ≤ τ.m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      ∀ (k : ℕ), k ≤ τ.n - 2 → ∀ (B : Subgroup G),
        B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) →
        Nonempty (Additive ↥B ≃+ (ZMod (2 ^ k) × ZMod (2 ^ (k + 2)) × ZMod (2 ^ (k + 2)))) →
        B ≤ Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G))
    (H3three : ∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
      {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD → τ.m + 2 = τ.n →
      2 ≤ τ.m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) ⊓
          Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) ≠ D →
      ∃ s ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) ⊓
          Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
            Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) =
          D ⊔ Subgroup.zpowers s ∧
        s * s = (dD.c : G) ∧ ⁅Subgroup.zpowers s, D⁆ = ⁅Subgroup.zpowers dD.ρ, omegaIn 1 D⁆)
    {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D' : Subgroup G} {τ' : StrothTypeIndex}
    {dD' : StrothWeakTypeData D' τ'} (h : F.IsD D' dD')
    (hns : IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)))
    {B : Subgroup G}
    (hBR : B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G))
    (hBn : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G), ∀ b ∈ B,
      x * b * x⁻¹ ∈ B)
    (hne : B ≠ D') (hconj : ∃ g : G, B = D'.map (MulAut.conj g).toMonoidHom) :
    τ'.m = τ'.n := by
  rcases τ'.m_eq_n_or_family with hmn | hfam
  · exact hmn
  exfalso
  have hcomm : ∀ x ∈ D', ∀ y ∈ D', x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (dD'.isMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨g, hg⟩ := hconj
  have hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rw [hg]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (map_mul _ x y).symm.trans ((congrArg _ (hcomm x hx y hy)).trans (map_mul _ y x))
  have hcard : Nat.card B = Nat.card D' := by
    rw [hg]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hDR : D' ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G) := fun d hd =>
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨h.le_S hd, Subgroup.le_normalizer hd⟩,
      Subgroup.mem_centralizer_iff.mpr fun w hw => hcomm w (omegaIn_le 1 D' hw) d hd⟩
  have hDB : D' ≤ Subgroup.normalizer (B : Set G) := fun d hd =>
    Subgroup.mem_normalizer_iff.mpr fun b => ⟨fun hb => hBn d (hDR hd) b hb, fun hb => by
      have := hBn d⁻¹ (hDR (inv_mem hd)) _ hb
      rwa [show d⁻¹ * (d * b * d⁻¹) * d⁻¹⁻¹ = b by group] at this⟩
  by_cases hm : 2 ≤ τ'.m
  · exact H4 H2b H3two H3three h hns hfam hm hBR hDB hne ⟨g, hg⟩
  have hD : Nat.card D' = 2 ^ (τ'.m + τ'.n + τ'.n) := by
    have := dD'.card
    rwa [StrothTypeIndex.k_two] at this
  by_cases h32 : τ'.m + τ'.n + τ'.n ≤ 5
  · refine h.false_of_le_R_of_card_le ?_ hBR hB hcard hne
    rw [hD]
    exact (Nat.pow_le_pow_right two_pos h32).trans (by norm_num)
  · exact h.false_of_le_R_of_t2m1 (τ'.eq_t200_one_or_t201_one (by omega) (by omega)) hns hBR hB
      hcard hne

theorem stroth_2_26_frame_of_contracts
    (H2b : ∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
      {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD → τ.m + 1 = τ.n →
      2 ≤ τ.m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      ∀ (k : ℕ), k ≤ τ.n - 1 → ∀ (B : Subgroup G),
        B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) →
        Nonempty (Additive ↥B ≃+ (ZMod (2 ^ k) × ZMod (2 ^ (k + 1)) × ZMod (2 ^ (k + 1)))) →
        B ≤ D)
    (H3two : ∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
      {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD → τ.m + 2 = τ.n →
      2 ≤ τ.m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      ∀ (k : ℕ), k ≤ τ.n - 2 → ∀ (B : Subgroup G),
        B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) →
        Nonempty (Additive ↥B ≃+ (ZMod (2 ^ k) × ZMod (2 ^ (k + 2)) × ZMod (2 ^ (k + 2)))) →
        B ≤ Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G))
    (H3three : ∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
      {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD → τ.m + 2 = τ.n →
      2 ≤ τ.m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) ⊓
          Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) ≠ D →
      ∃ s ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) ⊓
          Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
            Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) =
          D ⊔ Subgroup.zpowers s ∧
        s * s = (dD.c : G) ∧ ⁅Subgroup.zpowers s, D⁆ = ⁅Subgroup.zpowers dD.ρ, omegaIn 1 D⁆)
    {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D' : Subgroup G} {τ' : StrothTypeIndex}
    {dD' : StrothWeakTypeData D' τ'} (h : F.IsD D' dD')
    (hns : IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)))
    {B : Subgroup G}
    (hBR : B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G))
    (hBn : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G), ∀ b ∈ B,
      x * b * x⁻¹ ∈ B)
    (hne : B ≠ D') (hconj : ∃ g : G, B = D'.map (MulAut.conj g).toMonoidHom) :
    τ'.m = τ'.n :=
  stroth_2_26_frame_of_H4 @false_of_le_R_of_le_normalizer_of_two_le H2b H3two H3three h hns hBR
    hBn hne hconj

theorem stroth_2_26_frame_allConj
    (H2b : ∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
      {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD → τ.m + 1 = τ.n →
      2 ≤ τ.m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      ∀ (k : ℕ), k ≤ τ.n - 1 → ∀ (B : Subgroup G),
        B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) →
        Nonempty (Additive ↥B ≃+ (ZMod (2 ^ k) × ZMod (2 ^ (k + 1)) × ZMod (2 ^ (k + 1)))) →
        B ≤ D)
    (H3two : ∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
      {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD → τ.m + 2 = τ.n →
      2 ≤ τ.m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      ∀ (k : ℕ), k ≤ τ.n - 2 → ∀ (B : Subgroup G),
        B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) →
        Nonempty (Additive ↥B ≃+ (ZMod (2 ^ k) × ZMod (2 ^ (k + 2)) × ZMod (2 ^ (k + 2)))) →
        B ≤ Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G))
    (H3three : ∀ {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
      {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}, F.IsD D dD → τ.m + 2 = τ.n →
      2 ≤ τ.m →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) ⊓
          Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) ≠ D →
      ∃ s ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) ⊓
          Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
            Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) =
          D ⊔ Subgroup.zpowers s ∧
        s * s = (dD.c : G) ∧ ⁅Subgroup.zpowers s, D⁆ = ⁅Subgroup.zpowers dD.ρ, omegaIn 1 D⁆)
    {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D' : Subgroup G} {τ' : StrothTypeIndex}
    {dD' : StrothWeakTypeData D' τ'} (h : F.IsD D' dD')
    (hns : IsSylowIn 2 (Subgroup.normalizer (D' : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G)))
    (_hall : ∀ x : G, x ∈ omegaIn 1 D' → orderOf x = 2 →
      ∀ y : G, y ∈ omegaIn 1 D' → orderOf y = 2 → ∃ g : G, y = g * x * g⁻¹)
    {B : Subgroup G}
    (hBR : B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G))
    (hBn : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D' : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D' : Subgroup G) : Set G), ∀ b ∈ B,
      x * b * x⁻¹ ∈ B)
    (hne : B ≠ D') (hconj : ∃ g : G, B = D'.map (MulAut.conj g).toMonoidHom) :
    τ'.m = τ'.n :=
  stroth_2_26_frame_of_contracts H2b H3two H3three h hns hBR hBn hne hconj

end StrothFrame.IsD

end CFSG.CGT.Stroth77
