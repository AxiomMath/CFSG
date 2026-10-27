module

public import CFSG.ClassicalInvolution.Phan.PhanB5Block

public section

namespace CFSG.ClassicalInvolution.PhanB3

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.Assembly.LowTwoRank (StatedSp)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {hK : Nat.card K = (p ^ f) ^ 2} {F : Type} [Field F] {h2 : (2 : F) ≠ 0}
  {C : B2Coord hK F h2} {G : Type} [Group G] {Y : Type} [Group Y]
  {S : PhanFamilyB3 C G} {E : PhanFamilyB3 C Y}

theorem Lsup_zero_one_le : Lsup S {0, 1} ≤ S.θ.range := by
  refine iSup₂_le fun j hj => ?_
  rcases hj with hj | hj
  · subst hj
    rintro _ ⟨A, rfl⟩
    exact ⟨embSUid (unitaryInvolution K p f) 2 A, (ι_zero S A).symm⟩
  · obtain rfl : j = 1 := hj
    rintro _ ⟨A, rfl⟩
    exact ⟨embSUid (unitaryInvolution K p f) 0 A, (ι_one_θ S A).symm⟩

theorem Lsup_one_two_le : Lsup S {1, 2} ≤ S.ϑ.range := by
  refine iSup₂_le fun j hj => ?_
  rcases hj with hj | hj
  · subst hj
    rintro _ ⟨A, rfl⟩
    exact ⟨C.ℓ A, (ι_one_ϑ S A).symm⟩
  · obtain rfl : j = 2 := hj
    rintro _ ⟨A, rfl⟩
    exact ⟨C.s A, (ι_two S A).symm⟩

theorem IsBlockHom.agree_of_factor (hinj : Function.Injective (mTor S)) {J : Set (Fin 3)}
    {φN : Lsup S J →* Y} (hφ : IsBlockHom (E := E) J φN) {a b : Fin 3} (ha : a ∈ J)
    (hb : b ∈ J) (t : Fin 3 → normOne (unitaryInvolution K p f)) (hmem : mTor S t ∈ Lsup S J)
    (y w : normOne (unitaryInvolution K p f)) (h : mTor S t = tor S a y * tor S b w) :
    φN ⟨mTor S t, hmem⟩ = mTor E t := by
  have ht : t = Pi.mulSingle a y * Pi.mulSingle b w :=
    hinj (by rw [h, map_mul, mTor_mulSingle, mTor_mulSingle])
  have hprod : (⟨mTor S t, hmem⟩ : Lsup S J) =
      ⟨S.ι a (torusTwo (unitaryInvolution K p f) y), ι_mem_Lsup ha _⟩ *
        ⟨S.ι b (torusTwo (unitaryInvolution K p f) w), ι_mem_Lsup hb _⟩ :=
    Subtype.ext h
  rw [hprod, map_mul, hφ a ha, hφ b hb, ht, map_mul, mTor_mulSingle, mTor_mulSingle]
  rfl

variable (hq : 3 ≤ p ^ f) (hg : GoodFamily S)

include hK hq hg in
theorem IsBlockHom.agree_zero_one {J : Set (Fin 3)} (hJ : J = {0, 1})
    {φN : Lsup S J →* Y} (hφ : IsBlockHom (E := E) J φN) (h2K : (2 : K) ≠ 0)
    (t : Fin 3 → normOne (unitaryInvolution K p f)) (hmem : mTor S t ∈ Lsup S J) :
    φN ⟨mTor S t, hmem⟩ = mTor E t := by
  have hmem' : mTor S t ∈ S.θ.range := by
    rw [hJ] at hmem
    exact Lsup_zero_one_le hmem
  obtain ⟨B, hB⟩ := hmem'
  obtain ⟨y, w, hyw⟩ := hg.exists_tor_of_θ hq (B := B) (by rw [hB]; exact mTor_mem_torusSub S t)
  refine hφ.agree_of_factor (hg.mTor_injective h2K) (a := 0) (b := 1)
    (by rw [hJ]; exact Or.inl rfl) (by rw [hJ]; exact Or.inr rfl) t hmem y w ?_
  rw [← hB, hyw]

include hK hq hg in
theorem IsBlockHom.agree_one_two {J : Set (Fin 3)} (hJ : J = {1, 2})
    {φN : Lsup S J →* Y} (hφ : IsBlockHom (E := E) J φN) (h2K : (2 : K) ≠ 0)
    (t : Fin 3 → normOne (unitaryInvolution K p f)) (hmem : mTor S t ∈ Lsup S J) :
    φN ⟨mTor S t, hmem⟩ = mTor E t := by
  have hmem' : mTor S t ∈ S.ϑ.range := by
    rw [hJ] at hmem
    exact Lsup_one_two_le hmem
  obtain ⟨B, hB⟩ := hmem'
  obtain ⟨y, w, hyw⟩ := hg.exists_tor_of_ϑ hq (g := B) (by rw [hB]; exact mTor_mem_torusSub S t)
  refine hφ.agree_of_factor (hg.mTor_injective h2K) (a := 1) (b := 2)
    (by rw [hJ]; exact Or.inl rfl) (by rw [hJ]; exact Or.inr rfl) t hmem y w ?_
  rw [← hB, hyw]

include hK hq hg in
theorem IsBlockHom.agree_zero_two {J : Set (Fin 3)} (hJ : J = {0, 2})
    {φN : Lsup S J →* Y} (hφ : IsBlockHom (E := E) J φN) (h2K : (2 : K) ≠ 0)
    (t : Fin 3 → normOne (unitaryInvolution K p f)) (hmem : mTor S t ∈ Lsup S J) :
    φN ⟨mTor S t, hmem⟩ = mTor E t := by
  have hNT := range_le_normalizer_zero_two (S := S)
  have hmem' : mTor S t ∈ ((S.ι 0).range ⊔ (S.ι 2).range : Subgroup G) := by
    rw [← Lsup_pair, ← hJ]
    exact hmem
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hNT] at hmem'
  obtain ⟨x, ⟨A, rfl⟩, z, ⟨B, rfl⟩, hxz0⟩ := hmem'
  have hxz : S.ι 0 A * S.ι 2 B = mTor S t := hxz0
  obtain ⟨y, w, hyw⟩ := hg.exists_tor_of_far hq (A := A) (B := B)
    (by rw [hxz]; exact mTor_mem_torusSub S t)
  exact hφ.agree_of_factor (hg.mTor_injective h2K) (a := 0) (b := 2)
    (by rw [hJ]; exact Or.inl rfl) (by rw [hJ]; exact Or.inr rfl) t hmem y w
    (by rw [← hxz, hyw])

include hK hq hg in
theorem IsBlockHom.agree (h2K : (2 : K) ≠ 0) {J : Set (Fin 3)} (hJ : J.encard ≤ 2)
    {φN : Lsup S J →* Y} (hφ : IsBlockHom (E := E) J φN)
    (t : Fin 3 → normOne (unitaryInvolution K p f)) (hmem : mTor S t ∈ Lsup S J) :
    φN ⟨mTor S t, hmem⟩ = mTor E t := by
  have hinj := hg.mTor_injective h2K
  rcases hJ.lt_or_eq with h | h
  · have h1 : J.encard ≤ 1 := by
      have : (2 : ℕ∞) = 1 + 1 := by norm_num
      rw [this] at h
      exact (ENat.lt_add_one_iff (by simp)).1 h
    rcases Set.encard_le_one_iff_eq.1 h1 with rfl | ⟨a, rfl⟩
    · have h1 : mTor S t = 1 := by
        have := hmem
        rw [Lsup_empty, Subgroup.mem_bot] at this
        exact this
      have ht : t = 1 := hinj (by rw [h1, map_one])
      have : (⟨mTor S t, hmem⟩ : Lsup S ∅) = 1 := Subtype.ext h1
      rw [this, map_one, ht, map_one]
    · have hmem' : mTor S t ∈ (S.ι a).range := by
        rw [← Lsup_singleton]
        exact hmem
      obtain ⟨A, hA⟩ := hmem'
      obtain ⟨y, hy⟩ := hg.exists_tor_of_mem_range hq a (A := A)
        (by rw [hA]; exact mTor_mem_torusSub S t)
      refine hφ.agree_of_factor hinj (a := a) (b := a) rfl rfl t hmem y 1 ?_
      rw [map_one, mul_one, ← hA, hy]
  · obtain ⟨a, b, hab, rfl⟩ := Set.encard_eq_two.1 h
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | skip
    · exact hφ.agree_zero_one hq hg rfl h2K t hmem
    · exact hφ.agree_zero_two hq hg rfl h2K t hmem
    · exact hφ.agree_zero_one hq hg (Set.pair_comm _ _) h2K t hmem
    · exact hφ.agree_one_two hq hg rfl h2K t hmem
    · exact hφ.agree_zero_two hq hg (Set.pair_comm _ _) h2K t hmem
    · exact hφ.agree_one_two hq hg (Set.pair_comm _ _) h2K t hmem

end CFSG.ClassicalInvolution.PhanB3
