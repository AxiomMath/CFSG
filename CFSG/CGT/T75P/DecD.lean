module

public import CFSG.CGT.T75P.DecC

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups Matrix

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n : ℕ}

theorem transvection_one_mulVec {F : Type} [Field F] {i j : Fin n} (hij : i ≠ j)
    (v : Fin n → F) :
    ((Matrix.SpecialLinearGroup.transvection hij (1 : F) : SL(n, F)) :
        Matrix (Fin n) (Fin n) F) *ᵥ v = v + v j • Pi.single i 1 := by
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec_eq, one_mul]

theorem two_le_of_ctx (hc : Sec6Ctx T T₁ n 1) : 2 ≤ n := by
  have h4 := hc.hy.card
  rw [hc.hT] at h4
  by_contra hlt
  push Not at hlt
  interval_cases n <;> simp at h4

theorem inf_centralizer_hSub_eq_bot (hc : Sec6Ctx T T₁ n 1)
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n 1) :
    T ⊓ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) = ⊥ := by
  classical
  have hn : 2 ≤ n := two_le_of_ctx hc
  obtain ⟨hTH, hHN, -⟩ := hSub_data T T₁
  obtain ⟨hN, e, φ, hcompat⟩ := hnat
  have hnorm : (T.subgroupOf (hSub T (normIn T₁ T))).Normal := hN
  rw [eq_bot_iff]
  rintro t ⟨htT, htC⟩
  rw [Subgroup.mem_bot]
  by_contra ht1
  have hv : Multiplicative.toAdd (φ ⟨t, htT⟩) ≠ 0 := by
    intro h0
    have : φ ⟨t, htT⟩ = 1 := by rw [← ofAdd_toAdd (φ ⟨t, htT⟩), h0]; rfl
    have h1 := φ.injective (this.trans (map_one φ).symm)
    exact ht1 (congrArg Subtype.val h1)
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  obtain ⟨i, hij⟩ := exists_ne j
  obtain ⟨q, hq⟩ := e.surjective (Matrix.SpecialLinearGroup.transvection hij (1 : GaloisField 2 1))
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  have hmem : (h : G) * t * (h : G)⁻¹ ∈ T := conj_mem_of_mem_normalizer (hHN h.2) htT
  have h1 := hcompat h ⟨t, htT⟩ hmem
  rw [hq, transvection_one_mulVec hij] at h1
  have hcomm : (h : G) * t = t * (h : G) := (Subgroup.mem_centralizer_iff.1 htC) _ h.2
  have h2 : (⟨(h : G) * t * (h : G)⁻¹, hmem⟩ : ↥T) = ⟨t, htT⟩ := by
    apply Subtype.ext
    calc (h : G) * t * (h : G)⁻¹ = t * (h : G) * (h : G)⁻¹ := by rw [hcomm]
      _ = t := by group
  rw [h2] at h1
  have h3 := congrArg Multiplicative.toAdd h1
  rw [toAdd_ofAdd] at h3
  have h4 := congrFun h3 i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h4
  have h5 : Multiplicative.toAdd (φ ⟨t, htT⟩) j = 0 := by
    have : Multiplicative.toAdd (φ ⟨t, htT⟩) i + Multiplicative.toAdd (φ ⟨t, htT⟩) j =
        Multiplicative.toAdd (φ ⟨t, htT⟩) i + 0 := by rw [add_zero]; exact h4.symm
    exact add_left_cancel this
  exact hj h5

theorem normalizer_eq_mul (h62 : Sec62) (h63 : Sec63) (hc : Sec6Ctx T T₁ n 1)
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n 1) {k : ℕ} (ch : TransvChain n k) {g : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) :
    ∃ h ∈ hSub T (normIn T₁ T), ∃ c ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G),
      g = h * c := by
  obtain ⟨hTH, hHN, -⟩ := hSub_data T T₁
  obtain ⟨h, hh, cbar, hcbar, hgh⟩ := exists_mul_of_natural hHN hnat hg
  obtain ⟨t, htT, hct⟩ := exists_mul_mem_centralizer_hSub h62 h63 hc hnat ch hcbar
  have hct' : t * cbar = cbar * t := (Subgroup.mem_centralizer_iff.1 hcbar) t htT
  refine ⟨h * t⁻¹, (hSub T (normIn T₁ T)).mul_mem hh ((hSub T (normIn T₁ T)).inv_mem (hTH htT)),
    cbar * t, hct, ?_⟩
  rw [hgh, ← hct']
  group

theorem inf_hSub_centralizer_eq_bot (hc : Sec6Ctx T T₁ n 1)
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n 1) :
    hSub T (normIn T₁ T) ⊓ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) = ⊥ := by
  obtain ⟨hTH, hHN, -⟩ := hSub_data T T₁
  have hHC := inf_centralizer_eq_of_natural hTH hHN hnat
  rw [eq_bot_iff]
  rintro x ⟨hxH, hxC⟩
  have hxCT : x ∈ Subgroup.centralizer (T : Set G) := Subgroup.centralizer_le hTH hxC
  have hxT : x ∈ T := by
    have := Subgroup.mem_inf.2 ⟨hxH, hxCT⟩
    rwa [hHC] at this
  have := Subgroup.mem_inf.2 ⟨hxT, hxC⟩
  rwa [inf_centralizer_hSub_eq_bot hc hnat] at this

theorem relIndex_eq_card_centralizer (h62 : Sec62) (h63 : Sec63) (hc : Sec6Ctx T T₁ n 1)
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n 1) {k : ℕ} (ch : TransvChain n k) :
    T.relIndex (Subgroup.centralizer (T : Set G)) =
      Nat.card ↥(Subgroup.centralizer (hSub T (normIn T₁ T) : Set G)) := by
  classical
  obtain ⟨hTH, hHN, -⟩ := hSub_data T T₁
  have hCle : Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) ≤
      Subgroup.centralizer (T : Set G) := Subgroup.centralizer_le hTH
  have hTC := inf_centralizer_hSub_eq_bot hc hnat
  let f : ↥(Subgroup.centralizer (hSub T (normIn T₁ T) : Set G)) →
      ↥(Subgroup.centralizer (T : Set G)) ⧸ T.subgroupOf (Subgroup.centralizer (T : Set G)) :=
    fun c => QuotientGroup.mk ⟨(c : G), hCle c.2⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro a b hab
      have h1 := QuotientGroup.eq.1 hab
      rw [Subgroup.mem_subgroupOf] at h1
      have h1' : (a : G)⁻¹ * b ∈ T := by simpa using h1
      have h2 : (a : G)⁻¹ * b ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) :=
        (Subgroup.centralizer (hSub T (normIn T₁ T) : Set G)).mul_mem
          ((Subgroup.centralizer (hSub T (normIn T₁ T) : Set G)).inv_mem a.2) b.2
      have h3 : (a : G)⁻¹ * b ∈ T ⊓ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) :=
        Subgroup.mem_inf.2 ⟨h1', h2⟩
      rw [hTC, Subgroup.mem_bot] at h3
      exact Subtype.ext (inv_mul_eq_one.1 h3)
    · intro y
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨t, htT, hct⟩ := exists_mul_mem_centralizer_hSub h62 h63 hc hnat ch y.2
      refine ⟨⟨(y : G) * t, hct⟩, ?_⟩
      show QuotientGroup.mk (⟨(y : G) * t, hCle hct⟩ : ↥(Subgroup.centralizer (T : Set G))) =
        QuotientGroup.mk y
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have hval : (((⟨(y : G) * t, hCle hct⟩ : ↥(Subgroup.centralizer (T : Set G)))⁻¹ * y :
          ↥(Subgroup.centralizer (T : Set G))) : G) = t⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hval]
      exact T.inv_mem htT
  exact Nat.card_congr (Equiv.ofBijective f hbij).symm

end CFSG.CGT.T75P
