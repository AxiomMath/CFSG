module

public import CFSG.GH74.GLS.Bg.TwoGroups.L26Case
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma22

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L26

variable {T : Type} [Group T] [Finite T]

theorem conj_mem_O2 (hp : IsPGroup 2 T) (α : MulAut T)
    (hα : α ^ 3 = 1) (hfix : ∀ g : T, α g = g → g = 1) (A : Subgroup T) [A.Normal]
    (hAα : ∀ a ∈ A, α a ∈ A) (g : T) :
    (MulAut.conjNormal g : MulAut ↥A) ∈ O2 (O2res
      (Subgroup.closure (Set.range (MulAut.conjNormal (H := A)) ∪ {L23.xRes α A hAα}))) := by
  set cH : T →* MulAut ↥A := MulAut.conjNormal with hcH
  set αA : MulAut ↥A := L23.xRes α A hAα with hαA
  set 𝒜 : Subgroup (MulAut ↥A) := Subgroup.closure (Set.range cH ∪ {αA}) with h𝒜
  have hcH𝒜 : ∀ g, cH g ∈ 𝒜 := fun g => Subgroup.subset_closure (Or.inl ⟨g, rfl⟩)
  have hα𝒜 : αA ∈ 𝒜 := Subgroup.subset_closure (Or.inr rfl)
  have hαA3 : αA ^ 3 = 1 := by
    refine MulEquiv.ext fun a => ?_
    apply Subtype.ext
    rw [L23.xRes_pow, hα]
    rfl
  have hmul : ∀ g : T, αA * cH g = cH (α g) * αA := by
    intro g
    refine MulEquiv.ext fun a => ?_
    apply Subtype.ext
    show α (g * (a : T) * g⁻¹) = α g * α (a : T) * (α g)⁻¹
    rw [map_mul, map_mul, map_inv]
  have hconjα : ∀ g : T, αA * cH g * αA⁻¹ = cH (α g) := by
    intro g
    rw [mul_inv_eq_iff_eq_mul]
    exact hmul g
  have hN : ∀ N : Subgroup (MulAut ↥A), N ≤ 𝒜 → 𝒜 ≤ Subgroup.normalizer (N : Set (MulAut ↥A)) →
      (∃ k : ℕ, N.relIndex 𝒜 = 2 ^ k) → ∀ g : T, cH g ∈ N := by
    intro N hN𝒜 hNn ⟨k, hk⟩
    have hαN : αA ∈ N := by
      have hnorm : (N.subgroupOf 𝒜).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hN𝒜).mpr hNn
      have h1 := Subgroup.pow_index_mem (N.subgroupOf 𝒜) (⟨αA, hα𝒜⟩ : 𝒜)
      have hidx : (N.subgroupOf 𝒜).index = 2 ^ k := hk
      rw [hidx] at h1
      have hx3 : (⟨αA, hα𝒜⟩ : 𝒜) ^ 3 = 1 := Subtype.ext hαA3
      have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
      obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num : 1 < 3)
      have h2 : (⟨αA, hα𝒜⟩ : 𝒜) ^ (2 ^ k * m) = ⟨αA, hα𝒜⟩ := by
        rw [pow_eq_pow_mod _ hx3, hm, pow_one]
      have h3 : (⟨αA, hα𝒜⟩ : 𝒜) ∈ N.subgroupOf 𝒜 := by
        rw [← h2, pow_mul]
        exact pow_mem h1 m
      exact h3
    have hsub : ∀ g : T, cH g * (cH (α g))⁻¹ ∈ N := by
      intro g
      have h1 : cH g * αA * (cH g)⁻¹ ∈ N :=
        ((Subgroup.mem_normalizer_iff.mp (hNn (hcH𝒜 g)) αA).mp hαN)
      have h2 := mul_mem h1 (inv_mem hαN)
      have e : cH g * αA * (cH g)⁻¹ * αA⁻¹ = cH g * (cH (α g))⁻¹ := by
        rw [← hconjα g]; group
      rwa [e] at h2
    have hcomm : commAut α ≤ N.comap cH := by
      apply (Subgroup.closure_le (N.comap cH)).mpr
      rintro _ ⟨x, rfl⟩
      have e : cH (x⁻¹ * α x) = cH x⁻¹ * (cH (α x⁻¹))⁻¹ := by
        rw [← map_inv cH (α x⁻¹), ← map_mul, map_inv α, inv_inv]
      show cH (x⁻¹ * α x) ∈ N
      rw [e]
      exact hsub x⁻¹
    have htop : commAut α = ⊤ := commAut_eq_top hp α 1 (by rw [pow_one]; exact hα) hfix
    intro g
    have : g ∈ N.comap cH := hcomm (by rw [htop]; exact Subgroup.mem_top g)
    exact this
  have h𝒜n : 𝒜 ≤ Subgroup.normalizer (cH.range : Set (MulAut ↥A)) := by
    apply (Subgroup.closure_le (Subgroup.normalizer (cH.range : Set (MulAut ↥A)))).mpr
    rintro x (⟨y, rfl⟩ | hx)
    · exact Subgroup.le_normalizer ⟨y, rfl⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      show αA ∈ Subgroup.normalizer (cH.range : Set (MulAut ↥A))
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨α y, (hconjα y).symm⟩
      · rintro ⟨y, hy⟩
        refine ⟨α⁻¹ y, ?_⟩
        have e := hconjα (α⁻¹ y)
        rw [MulAut.apply_inv_self, hy] at e
        exact mul_left_cancel (mul_right_cancel e)
  have hTle : cH.range ≤ O2res 𝒜 := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    refine Subgroup.mem_iInf.mpr ?_
    rintro ⟨N, hN1, hN2, hN3⟩
    exact hN N hN1 hN2 hN3 y
  have hTn : O2res 𝒜 ≤ Subgroup.normalizer (cH.range : Set (MulAut ↥A)) := by
    intro x hx
    apply h𝒜n
    exact (Subgroup.mem_iInf.mp hx ⟨𝒜, le_rfl, Subgroup.le_normalizer, 0, by simp⟩)
  have hTp : IsPGroup 2 cH.range :=
    hp.of_surjective cH.rangeRestrict (MonoidHom.rangeRestrict_surjective cH)
  exact Subgroup.mem_iSup_of_mem (⟨cH.range, hTle, hTn, hTp⟩ :
    {N : Subgroup (MulAut ↥A) // N ≤ O2res 𝒜 ∧
      O2res 𝒜 ≤ Subgroup.normalizer (N : Set (MulAut ↥A)) ∧ IsPGroup 2 N}) ⟨g, rfl⟩

theorem k3_prop : K3Prop := by
  intro T _ _ hp α hα hfix A hAn hAα hAc hθ hCA hcard g h hhA hh4
  obtain ⟨θ⟩ := hθ
  have hA64 : Nat.card A = 64 := by
    rw [Nat.card_congr θ.toEquiv, Nat.card_eq_fintype_card]; decide
  have hQcard : Nat.card (T ⧸ A) = 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup A
    rw [hA64] at h1 hcard
    omega
  have hq3 : (quotAut A α hAα) ^ 3 = 1 := quotAut_pow_eq_one A α hAα 3 hα
  have hqfix : ∀ e ∈ (⊤ : Subgroup (T ⧸ A)), quotAut A α hAα e = e → e = 1 := by
    intro e _ he
    induction e using QuotientGroup.induction_on with
    | _ x =>
      rw [quotAut_mk] at he
      have hx : x⁻¹ * α x ∈ A := QuotientGroup.eq.mp he.symm
      obtain ⟨s, hs, hαs⟩ := exists_fixed_coset3 hp α 1 (by rw [pow_one]; exact hα) A hAα x hx
      have hs1 : s = 1 := hfix s hαs
      rw [hs1, mul_one] at hs
      have hxA : x ∈ A := by simpa using inv_mem hs
      exact (QuotientGroup.eq_one_iff x).mpr hxA
  have hsq : ∀ q : T ⧸ A, q * q = 1 := fun q =>
    (elem_of_fpf (quotAut A α hAα) hq3 ⊤ (by rw [Subgroup.card_top]; exact hQcard)
      (fun e _ => Subgroup.mem_top _) hqfix).1 q (Subgroup.mem_top q)
  have hgg : g * g ∈ A := by
    have := hsq (QuotientGroup.mk g)
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at this
    exact this
  let commA : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with mul_comm := fun a b => Subtype.ext (hAc a a.2 b b.2) }
  have hb := conj_mem_O2 hp α hα hfix A hAα g
  have hb2 : (MulAut.conjNormal g : MulAut ↥A) * MulAut.conjNormal g = 1 := by
    rw [← map_mul]
    refine MulEquiv.ext fun a => ?_
    apply Subtype.ext
    show (g * g) * (a : T) * (g * g)⁻¹ = a
    rw [hAc (g * g) hgg a a.2]
    group
  have key := iv2_2_2 ↥A ⟨θ⟩ _ _ hb hb2 ⟨h, hhA⟩ (Subtype.ext (by simpa using hh4))
  have key' := congrArg Subtype.val key
  simpa [MulAut.conjNormal_apply] using key'

end L26

end CFSG.GH74.GLS.Bg.TwoGroups
