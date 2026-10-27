module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OFactsF1Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] def U4CentTwoPlus : Prop :=
  ∀ (V : Type) [Group V] [Finite V], CFSG.Blueprint.LieModel V .PSU 4 3 1 →
    ∀ Q₁ Q₂ : Subgroup V,
      Nonempty (↥Q₁ ≃* QuaternionGroup 2) → Nonempty (↥Q₂ ≃* QuaternionGroup 2) →
      ⁅Q₁, Q₂⁆ = ⊥ → Nat.card ↥(Q₁ ⊔ Q₂) = 32 →
      IsPGroup 2 (Subgroup.centralizer (((Q₁ ⊔ Q₂ : Subgroup V) : Subgroup V) : Set V))

theorem u43CentTwoPlus_of (h : U4CentTwoPlus) : U43CentTwoPlus := by
  intro U _ _ _hq htwo Q₁ Q₂ hQ₁ hQ₂ hcomm hcard hZ
  classical
  let Z : Subgroup U := Subgroup.center U
  have hZcard : Nat.card ↥Z = 2 := by simpa [Z] using htwo.1
  haveI hZn : Z.Normal := by
    simpa [Z] using Subgroup.instNormalCenter (G := U)
  let V := U ⧸ Z
  let mk : U →* V := QuotientGroup.mk' Z
  let Q : Subgroup U := Q₁ ⊔ Q₂
  have hQZ : (Q₁ ⊔ Q₂) ⊓ Z = ⊥ := by simpa [Q, Z] using hZ
  have hQ₁Z : Q₁ ⊓ Z = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hz' : z ∈ (Q₁ ⊔ Q₂) ⊓ Z := ⟨Subgroup.mem_sup_left hz.1, hz.2⟩
    rw [hQZ] at hz'
    exact Subgroup.mem_bot.mp hz'
  have hQ₂Z : Q₂ ⊓ Z = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hz' : z ∈ (Q₁ ⊔ Q₂) ⊓ Z := ⟨Subgroup.mem_sup_right hz.1, hz.2⟩
    rw [hQZ] at hz'
    exact Subgroup.mem_bot.mp hz'
  have hinj_mk {P : Subgroup U} (hPZ : P ⊓ Z = ⊥) :
      Function.Injective (mk.subgroupMap P) := by
    intro a b hab
    have hab' : mk (a : U) = mk (b : U) := congrArg Subtype.val hab
    have hdiv : (a : U) / (b : U) ∈ Z := QuotientGroup.eq_iff_div_mem.mp hab'
    have hdivP : (a : U) / (b : U) ∈ P := P.div_mem a.2 b.2
    have hbot : (a : U) / (b : U) ∈ (⊥ : Subgroup U) := by
      rw [← hPZ]
      exact ⟨hdivP, hdiv⟩
    have h1 : (a : U) / (b : U) = 1 := Subgroup.mem_bot.mp hbot
    exact Subtype.ext (div_eq_one.mp h1)
  let Qbar₁ : Subgroup V := Q₁.map mk
  let Qbar₂ : Subgroup V := Q₂.map mk
  have hQbar₁ : Nonempty (↥Qbar₁ ≃* QuaternionGroup 2) := by
    obtain ⟨e⟩ := hQ₁
    exact ⟨(MulEquiv.ofBijective (mk.subgroupMap Q₁)
      ⟨hinj_mk hQ₁Z, mk.subgroupMap_surjective Q₁⟩).symm.trans e⟩
  have hQbar₂ : Nonempty (↥Qbar₂ ≃* QuaternionGroup 2) := by
    obtain ⟨e⟩ := hQ₂
    exact ⟨(MulEquiv.ofBijective (mk.subgroupMap Q₂)
      ⟨hinj_mk hQ₂Z, mk.subgroupMap_surjective Q₂⟩).symm.trans e⟩
  have hsup : Qbar₁ ⊔ Qbar₂ = (Q₁ ⊔ Q₂).map mk :=
    (Subgroup.map_sup Q₁ Q₂ mk).symm
  have hcommbar : ⁅Qbar₁, Qbar₂⁆ = ⊥ := by
    dsimp only [Qbar₁, Qbar₂]
    rw [← Subgroup.map_commutator Q₁ Q₂ mk, hcomm, Subgroup.map_bot]
  have hcardbar : Nat.card ↥(Qbar₁ ⊔ Qbar₂) = 32 := by
    have hcardmap : Nat.card ↥((Q₁ ⊔ Q₂).map mk) = Nat.card ↥(Q₁ ⊔ Q₂) :=
      (Nat.card_congr (MulEquiv.ofBijective (mk.subgroupMap (Q₁ ⊔ Q₂))
        ⟨hinj_mk hQZ, mk.subgroupMap_surjective (Q₁ ⊔ Q₂)⟩).toEquiv).symm
    rw [hsup, hcardmap, hcard]
  have hVcent : IsPGroup 2 (Subgroup.centralizer
      (((Qbar₁ ⊔ Qbar₂ : Subgroup V) : Subgroup V) : Set V)) :=
    h V (by simpa [V, Z] using htwo.2) Qbar₁ Qbar₂ hQbar₁ hQbar₂ hcommbar hcardbar
  let C : Subgroup U := Subgroup.centralizer (Q : Set U)
  let ψ : ↥C →* V := mk.comp C.subtype
  have hZC : Z ≤ C := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro q _
    exact Subgroup.mem_center_iff.mp hz q
  have hker : ψ.ker = Z.subgroupOf C := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx' : mk (x : U) = 1 := by simpa [ψ] using hx
      exact (QuotientGroup.eq_one_iff (x : U)).mp hx'
    · intro hx
      have hx' : mk (x : U) = 1 := (QuotientGroup.eq_one_iff (x : U)).mpr hx
      simpa [ψ] using hx'
  have hkercard : Nat.card ↥ψ.ker = 2 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv, hZcard]
  have hrange_le : ψ.range ≤ Subgroup.centralizer
      (((Qbar₁ ⊔ Qbar₂ : Subgroup V) : Subgroup V) : Set V) := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hsup] at hy
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
    change mk q * mk (x : U) = mk (x : U) * mk q
    rw [← map_mul, ← map_mul]
    exact congrArg mk (Subgroup.mem_centralizer_iff.mp x.2 q hq)
  obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.mp hVcent
  have hrange_dvd : Nat.card ↥ψ.range ∣
      Nat.card ↥(Subgroup.centralizer
        (((Qbar₁ ⊔ Qbar₂ : Subgroup V) : Subgroup V) : Set V)) := by
    have h := Subgroup.card_subgroup_dvd_card
      (ψ.range.subgroupOf (Subgroup.centralizer
        (((Qbar₁ ⊔ Qbar₂ : Subgroup V) : Subgroup V) : Set V)))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hrange_le).toEquiv] at h
  have hcard_range_dvd : Nat.card ↥ψ.range ∣ 2 ^ n := hrange_dvd.trans hn
  have hcardC : Nat.card ↥C = 2 * Nat.card ↥ψ.range := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hkercard] at h
    exact h.symm
  have hC_dvd : Nat.card ↥C ∣ 2 ^ (n + 1) := by
    rw [hcardC, pow_succ]
    simpa [Nat.mul_comm] using mul_dvd_mul_left 2 hcard_range_dvd
  change IsPGroup 2 ↥C
  exact IsPGroup.of_card_dvd_pow hC_dvd

end CFSG.OddStandard.SmallF3.Omega
