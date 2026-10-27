module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PDh
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PI

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

variable {X : Type} [Group X] [Finite X]
  {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X} {w z : X} {V : Subgroup X}
  {i j : ℕ} {z₁ τ α : X} {K₂ W 𝒱 : Subgroup X}

namespace Data415B

variable (hD : Data415B t L p f S w z V i j z₁ τ α K₂ W 𝒱)
include hD

open DihedralGroup in
theorem exists_lambdaF (hlt : barOf (centralizer {z₁}) K₂ < layer (MBar z₁))
    (hsyl : IsSylowOf 2 (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ layer (MBar z₁))
      (layer (MBar z₁)))
    (hdih : GorensteinWalter.HasDihedralSylowTwo ↥(layer (MBar z₁))) :
    ∃ l ∈ barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}),
      l * l = (QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ : MBar z₁) ∧
      ∀ v ∈ barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}), v * l * v⁻¹ = l ∨
        v * l * v⁻¹ = l * (QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ : MBar z₁) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEn : (layer (MBar z₁)).Normal := by
    have := LocalCores.layer_characteristic (G := MBar z₁)
    infer_instance
  obtain ⟨Q, hQ⟩ := hsyl.exists_sylow_eq_subgroupOf
  obtain ⟨m, hm1, ⟨eQ⟩⟩ := hdih Q
  let e₀ : ↥(barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ layer (MBar z₁)) ≃*
      DihedralGroup (2 ^ m) :=
    ((subgroupOfEquivOfLe hsyl.le).symm.trans (MulEquiv.subgroupCongr hQ.symm)).trans eQ
  have hcardR : Nat.card ↥(barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓
      layer (MBar z₁)) = 2 * 2 ^ m := by
    rw [Nat.card_congr e₀.toEquiv, DihedralGroup.nat_card]
  have h8 : 8 ≤ 2 * 2 ^ m := by
    obtain ⟨Q', hQ'K, hQ'2, hQ'8, -⟩ := hD.exists_sylow_K₂F
    have h1 := card_le_twoPart hQ'2 (hQ'K.trans hlt.le)
    have h2 : Nat.card ↥(barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ layer (MBar z₁)) =
        twoPart (layer (MBar z₁)) := hsyl.card_eq
    calc 8 ≤ Nat.card ↥Q' := hQ'8
      _ ≤ twoPart (layer (MBar z₁)) := h1
      _ = 2 * 2 ^ m := by rw [← h2, hcardR]
  have hm : 2 ≤ m := by
    by_contra h
    have h1 : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hz₂V : (QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ : MBar z₁) ∈
      barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) := mk_mem_barOf hD.z₂_mem_F hD.z₂_mem_V₀
  have hz₂E := hlt.le hD.z₂F_mem
  set zR : ↥(barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ layer (MBar z₁)) :=
    ⟨_, hz₂V, hz₂E⟩ with hzR
  have hzRc : e₀ zR = r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
    rcases L415.dih_central hm (c := e₀ zR) (fun d => by
      obtain ⟨d, rfl⟩ := e₀.surjective d
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hD.V₀F_comm_z₂F d.2.1).symm) with h | h
    · exfalso
      have h1 : zR = 1 := e₀.injective (by rw [h, map_one])
      have h2 := hD.orderOf_z₂F
      rw [show (QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ : MBar z₁) = 1 from
        congrArg Subtype.val h1, orderOf_one] at h2
      norm_num at h2
    · exact h
  set lR := e₀.symm (r ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))) with hlR
  have hlR2 : lR * lR = zR := by
    apply e₀.injective
    rw [map_mul, hlR, MulEquiv.apply_symm_apply, L415.dih_sq_quarter hm, hzRc]
  refine ⟨lR, lR.2.1, congrArg Subtype.val hlR2, fun v hv => ?_⟩
  have hyV : v * (lR : MBar z₁) * v⁻¹ ∈ barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) :=
    mul_mem (mul_mem hv lR.2.1) (inv_mem hv)
  have hyE : v * (lR : MBar z₁) * v⁻¹ ∈ layer (MBar z₁) := hEn.conj_mem _ lR.2.2 v
  set yR : ↥(barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ layer (MBar z₁)) :=
    ⟨_, hyV, hyE⟩ with hyR
  have hvz : v * (zR : MBar z₁) * v⁻¹ = (zR : MBar z₁) := by
    have h1 := hD.V₀F_comm_z₂F hv
    calc v * (zR : MBar z₁) * v⁻¹ =
        (v * (QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ : MBar z₁)) * v⁻¹ := rfl
      _ = ((QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ : MBar z₁) * v) * v⁻¹ := by rw [h1]
      _ = (zR : MBar z₁) := mul_inv_cancel_right _ _
  have hyR2 : yR * yR = zR := by
    apply Subtype.ext
    change v * (lR : MBar z₁) * v⁻¹ * (v * (lR : MBar z₁) * v⁻¹) = _
    rw [show v * (lR : MBar z₁) * v⁻¹ * (v * (lR : MBar z₁) * v⁻¹) =
      v * ((lR : MBar z₁) * (lR : MBar z₁)) * v⁻¹ by group]
    rw [show (lR : MBar z₁) * (lR : MBar z₁) = (zR : MBar z₁) from congrArg Subtype.val hlR2]
    exact hvz
  have hsq : e₀ yR * e₀ yR = r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
    rw [← map_mul, hyR2, hzRc]
  rcases L415.dih_sq_eq hm hsq with h | h
  · left
    have h1 : yR = lR := by rw [hlR, ← h, MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val h1
  · right
    have h1 : yR = lR * zR := by
      apply e₀.injective
      rw [h, map_mul, hlR, MulEquiv.apply_symm_apply, hzRc]
    exact congrArg Subtype.val h1

theorem exists_ell (hlt : barOf (centralizer {z₁}) K₂ < layer (MBar z₁))
    (hsyl : IsSylowOf 2 (barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) ⊓ layer (MBar z₁))
      (layer (MBar z₁)))
    (hdih : GorensteinWalter.HasDihedralSylowTwo ↥(layer (MBar z₁))) :
    ∃ ℓ ∈ 𝒱 ⊓ centralizer {z₁}, ℓ * ℓ = t * z₁ * t⁻¹ ∧
      ∀ v ∈ 𝒱 ⊓ centralizer {z₁}, v * ℓ * v⁻¹ = ℓ ∨ v * ℓ * v⁻¹ = ℓ * (t * z₁ * t⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, hl, hl2, hlv⟩ := hD.exists_lambdaF hlt hsyl hdih
  obtain ⟨l', hl'V, hl'π⟩ := hl
  have hP : IsPGroup 2 ↥((𝒱 ⊓ centralizer {z₁}).subgroupOf (centralizer ({z₁} : Set X))) :=
    (hD.fd.isSylowOf_𝒱₀.isPGroup).comap_subtype
  have hinj := GSThmB.OddQuot.injOn_of_isPGroup hP
  have hz₂P : (⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ : ↥(centralizer ({z₁} : Set X))) ∈
      (𝒱 ⊓ centralizer {z₁}).subgroupOf (centralizer ({z₁} : Set X)) := hD.z₂_mem_V₀
  refine ⟨l', hl'V, ?_, fun v hv => ?_⟩
  · have h1 : l' * l' = ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ := by
      refine hinj (mul_mem hl'V hl'V) hz₂P ?_
      change QuotientGroup.mk (l' * l') = (QuotientGroup.mk ⟨t * z₁ * t⁻¹, hD.z₂_mem_F⟩ : MBar z₁)
      rw [QuotientGroup.mk_mul]
      change (QuotientGroup.mk' _ l') * (QuotientGroup.mk' _ l') = _
      rw [hl'π]
      exact hl2
    exact congrArg Subtype.val h1
  · have hvF : v ∈ centralizer ({z₁} : Set X) := (mem_inf.mp hv).2
    have hvP : (⟨v, hvF⟩ : ↥(centralizer ({z₁} : Set X))) ∈
        (𝒱 ⊓ centralizer {z₁}).subgroupOf (centralizer ({z₁} : Set X)) := hv
    have hvV : (QuotientGroup.mk ⟨v, hvF⟩ : MBar z₁) ∈
        barOf (centralizer {z₁}) (𝒱 ⊓ centralizer {z₁}) := mk_mem_barOf hvF hv
    have hconjP : (⟨v, hvF⟩ : ↥(centralizer ({z₁} : Set X))) * l' * ⟨v, hvF⟩⁻¹ ∈
        (𝒱 ⊓ centralizer {z₁}).subgroupOf (centralizer ({z₁} : Set X)) :=
      mul_mem (mul_mem hvP hl'V) (inv_mem hvP)
    have hπc : QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z₁} : Set X)))
        ((⟨v, hvF⟩ : ↥(centralizer ({z₁} : Set X))) * l' * ⟨v, hvF⟩⁻¹) =
        (QuotientGroup.mk ⟨v, hvF⟩ : MBar z₁) * l * (QuotientGroup.mk ⟨v, hvF⟩ : MBar z₁)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hl'π]
      rfl
    rcases hlv _ hvV with h | h
    · left
      have h1 := hinj hconjP hl'V (by rw [hπc, h, ← hl'π])
      exact congrArg Subtype.val h1
    · right
      have h1 := hinj hconjP (mul_mem hl'V hz₂P) (by
        rw [hπc, h, map_mul, hl'π]
        rfl)
      exact congrArg Subtype.val h1

end Data415B

end CFSG.ComponentClassification.HarrisLit
