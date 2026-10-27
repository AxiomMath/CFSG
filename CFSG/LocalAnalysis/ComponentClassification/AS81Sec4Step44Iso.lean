module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step44Theta

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Hexa CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native HeSylow

variable {G : Type} [Group G] [Finite G] {E F : Subgroup G}

section Rho

variable {S₁ W : Subgroup G} (hWS₁ : W ≤ S₁) (hWS : W ⊓ (E ⊔ F) = ⊥)
  (hWc : Nat.card W * 2 ^ 8 = Nat.card S₁) (hSS₁ : E ⊔ F ≤ S₁)
  (hS₁N : S₁ ≤ normalizer ((E ⊔ F : Subgroup G) : Set G))
  (hS256 : Nat.card (E ⊔ F : Subgroup G) = 2 ^ 8)
  {Θ : Fin 256 → G} (hΘS : ∀ i, Θ i ∈ E ⊔ F) (hΘi : Function.Injective Θ)
  (hΘm : ∀ i j, Θ (smStarF i j) = Θ i * Θ j)

include hS256 hΘS hΘi in
theorem exists_theta_eq {x : G} (hx : x ∈ E ⊔ F) : ∃ i, Θ i = x := by
  let f : Fin 256 → ↥(E ⊔ F) := fun i => ⟨Θ i, hΘS i⟩
  have hf : Function.Injective f := fun i j h => hΘi (congrArg Subtype.val h)
  have hb := hf.bijective_of_nat_card_le (by
    rw [hS256, Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  obtain ⟨i, hi⟩ := hb.2 ⟨x, hx⟩
  exact ⟨i, congrArg Subtype.val hi⟩

include hΘm in
omit [Finite G] in
theorem theta_zero : Θ 0 = 1 := by
  have h := hΘm 0 0
  have e : smStarF 0 0 = 0 := Fin.ext smStar_zero
  rw [e] at h
  exact left_eq_mul.mp h


include hWS₁ hWS hWc hSS₁ hS₁N hS256 hΘS hΘi hΘm in
theorem exists_rho (hWC : ∀ w ∈ W, (∀ s ∈ E ⊔ F, w * s * w⁻¹ = s) → w = 1) :
    ∃ ρ : ↥S₁ →* Equiv.Perm (Fin 256), Function.Injective ρ ∧
      (∀ σ i, ρ ⟨Θ σ, hSS₁ (hΘS σ)⟩ i = smStarF σ i) ∧
      ∀ w (hw : w ∈ W) i, Θ (ρ ⟨w, hWS₁ hw⟩ i) = w * Θ i * w⁻¹ := by
  classical
  let β : Fin 256 → ↥S₁ ⧸ W.subgroupOf S₁ := fun i =>
    QuotientGroup.mk (⟨Θ i, hSS₁ (hΘS i)⟩ : ↥S₁)
  have hβi : Function.Injective β := by
    intro i j h
    have h0 := QuotientGroup.eq.mp (show (QuotientGroup.mk ⟨Θ i, hSS₁ (hΘS i)⟩ :
      ↥S₁ ⧸ W.subgroupOf S₁) = QuotientGroup.mk ⟨Θ j, hSS₁ (hΘS j)⟩ from h)
    have h' : (Θ i)⁻¹ * Θ j ∈ W := h0
    have h1 : (Θ i)⁻¹ * Θ j ∈ W ⊓ (E ⊔ F) :=
      Subgroup.mem_inf.mpr ⟨h', mul_mem (inv_mem (hΘS i)) (hΘS j)⟩
    rw [hWS, mem_bot, inv_mul_eq_one] at h1
    exact hΘi h1
  have hcardQ : Nat.card (↥S₁ ⧸ W.subgroupOf S₁) = 2 ^ 8 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (W.subgroupOf S₁)
    rw [Nat.card_congr (subgroupOfEquivOfLe hWS₁).toEquiv, ← hWc] at h
    exact (Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := W)) (by rw [← h, mul_comm])).symm
  have hβb : Function.Bijective β :=
    hβi.bijective_of_nat_card_le (by
      rw [hcardQ, Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  let βE : Fin 256 ≃ ↥S₁ ⧸ W.subgroupOf S₁ := Equiv.ofBijective β hβb
  let ρ : ↥S₁ →* Equiv.Perm (Fin 256) := (Equiv.permCongrHom βE.symm).toMonoidHom.comp
    (MulAction.toPermHom ↥S₁ (↥S₁ ⧸ W.subgroupOf S₁))
  have hρ : ∀ (x : ↥S₁) i j, ρ x i = j ↔ (Θ j)⁻¹ * ((x : G) * Θ i) ∈ W := by
    intro x i j
    have e1 : ρ x i = βE.symm (x • βE i) := rfl
    rw [e1, Equiv.symm_apply_eq]
    have e2 : x • βE i = QuotientGroup.mk (x * ⟨Θ i, hSS₁ (hΘS i)⟩) := rfl
    have e3 : βE j = QuotientGroup.mk (⟨Θ j, hSS₁ (hΘS j)⟩ : ↥S₁) := rfl
    rw [e2, e3, QuotientGroup.eq, mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · intro h
      have := inv_mem h
      rwa [mul_inv_rev, inv_inv] at this
    · intro h
      have := inv_mem h
      rwa [mul_inv_rev, inv_inv] at this
  have hconjS : ∀ x ∈ S₁, ∀ i, x * Θ i * x⁻¹ ∈ E ⊔ F := fun x hx i =>
    (mem_normalizer_iff.mp (hS₁N hx) _).mp (hΘS i)
  have hW : ∀ w (hw : w ∈ W) i, Θ (ρ ⟨w, hWS₁ hw⟩ i) = w * Θ i * w⁻¹ := by
    intro w hw i
    obtain ⟨j, hj⟩ := exists_theta_eq hS256 hΘS hΘi (hconjS w (hWS₁ hw) i)
    have hρj : ρ ⟨w, hWS₁ hw⟩ i = j := by
      rw [hρ, hj]
      have e : (w * Θ i * w⁻¹)⁻¹ * (w * Θ i) = w := by group
      rw [e]
      exact hw
    rw [hρj, hj]
  refine ⟨ρ, ?_, fun σ i => ?_, hW⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    have h0 : ρ x 0 = 0 := by rw [hx]; rfl
    rw [hρ, theta_zero hΘm, inv_one, one_mul, mul_one] at h0
    have hxc : ∀ s ∈ E ⊔ F, (x : G) * s * (x : G)⁻¹ = s := by
      intro s hs
      obtain ⟨i, rfl⟩ := exists_theta_eq hS256 hΘS hΘi hs
      have h1 := hW x h0 i
      have e : (⟨(x : G), hWS₁ h0⟩ : ↥S₁) = x := rfl
      rw [e, hx] at h1
      exact h1.symm
    exact Subtype.ext (hWC x h0 hxc)
  · rw [hρ, hΘm]
    have e : (Θ σ * Θ i)⁻¹ * ((⟨Θ σ, hSS₁ (hΘS σ)⟩ : ↥S₁) * Θ i) = 1 := by
      show (Θ σ * Θ i)⁻¹ * (Θ σ * Θ i) = 1
      group
    rw [e]
    exact one_mem _


section Img

variable {ρ : ↥S₁ →* Equiv.Perm (Fin 256)} (hρi : Function.Injective ρ)
  (hρS : ∀ σ i, ρ ⟨Θ σ, hSS₁ (hΘS σ)⟩ i = smStarF σ i)
  (hρW : ∀ w (hw : w ∈ W) i, Θ (ρ ⟨w, hWS₁ hw⟩ i) = w * Θ i * w⁻¹)

include hΘi hΘm hρW in
omit [Finite G] in
theorem rho_mem_hexaN (h44 : step44Check = true) {T : Subgroup G}
    (hWT : W ≤ normalizer (T : Set G)) (hΘ1 : ∃ t₁ ∈ T, ∀ i, t₁ * Θ i * t₁⁻¹ = Θ (smTauF 1 0 i))
    (hΘ2 : ∃ t₂ ∈ T, ∀ i, t₂ * Θ i * t₂⁻¹ = Θ (smTauF 0 1 i))
    (hΘT : ∀ t ∈ T, ∃ a b : ℕ, ∀ i, t * Θ i * t⁻¹ = Θ (smTauF a b i)) {w : G} (hw : w ∈ W) :
    ρ ⟨w, hWS₁ hw⟩ ∈ hexaN := by
  have hmul : ∀ i j, ρ ⟨w, hWS₁ hw⟩ (smStarF i j) =
      smStarF (ρ ⟨w, hWS₁ hw⟩ i) (ρ ⟨w, hWS₁ hw⟩ j) := by
    intro i j
    apply hΘi
    rw [hρW w hw, hΘm, hΘm, hρW w hw, hρW w hw]
    group
  obtain ⟨t₁, ht₁T, ht₁⟩ := hΘ1
  obtain ⟨t₂, ht₂T, ht₂⟩ := hΘ2
  have hwN := hWT hw
  obtain ⟨a₁, b₁, h₁⟩ := hΘT (w * t₁ * w⁻¹) ((mem_normalizer_iff.mp hwN t₁).mp ht₁T)
  obtain ⟨a₂, b₂, h₂⟩ := hΘT (w * t₂ * w⁻¹) ((mem_normalizer_iff.mp hwN t₂).mp ht₂T)
  refine mem_hexaN_of_aut h44 hmul (s1 := (a₁, b₁)) (s2 := (a₂, b₂)) (fun i => ?_) (fun i => ?_)
  · apply hΘi
    rw [hρW w hw, ← ht₁, ← h₁, hρW w hw]
    group
  · apply hΘi
    rw [hρW w hw, ← ht₂, ← h₂, hρW w hw]
    group

include hρi hρS hS256 hΘS in
omit [Finite G] in
theorem map_rho_sup (h44 : step44Check = true) : ((E ⊔ F).subgroupOf S₁).map ρ = smLamGrp := by
  have hle : smLamGrp ≤ ((E ⊔ F).subgroupOf S₁).map ρ := by
    refine grpN_le fun a ha => ?_
    obtain ⟨x, hx, hxa⟩ := smLamGens_get h44 ha
    have e : permOfArr 256 a = ρ ⟨Θ ⟨x, hx⟩, hSS₁ (hΘS _)⟩ := by
      refine Equiv.ext fun i => Fin.ext ?_
      rw [hxa i, hρS]
      rfl
    rw [e]
    exact Subgroup.mem_map_of_mem ρ (show (⟨Θ ⟨x, hx⟩, hSS₁ (hΘS _)⟩ : ↥S₁) ∈
      (E ⊔ F).subgroupOf S₁ from hΘS _)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_smLamGrp h44, Subgroup.card_map_of_injective hρi,
    Nat.card_congr (subgroupOfEquivOfLe hSS₁).toEquiv, hS256]
  norm_num

include hρi hρS hS256 hΘS hΘi in
theorem conj_mem_smLamGrp (h44 : step44Check = true) {β : Equiv.Perm (Fin 256)} (hβ : β ∈ smAut)
    {x : Equiv.Perm (Fin 256)} (hx : x ∈ smLamGrp) : β * x * β⁻¹ ∈ smLamGrp := by
  rw [← map_rho_sup hSS₁ hS256 hΘS hρi hρS h44] at hx ⊢
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨σ, hσ⟩ := exists_theta_eq hS256 hΘS hΘi (show (s : G) ∈ E ⊔ F from hs)
  have e : s = ⟨Θ σ, hSS₁ (hΘS σ)⟩ := Subtype.ext hσ.symm
  rw [e]
  refine ⟨⟨Θ (β σ), hSS₁ (hΘS _)⟩, hΘS _, Equiv.ext fun i => ?_⟩
  rw [hρS, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hρS, hβ σ (β⁻¹ i),
    Equiv.Perm.inv_def, Equiv.apply_symm_apply]

include hWS₁ hWS hWc hSS₁ hS₁N hS256 hρi hρS hΘS in
theorem range_rho (h44 : step44Check = true) :
    ρ.range = smLamGrp ⊔ (W.subgroupOf S₁).map ρ := by
  have hsup : (E ⊔ F) ⊔ W = S₁ := by
    have hcard := card_sup_mul_card_inf (H := E ⊔ F) (R := W) (hWS₁.trans hS₁N)
    rw [inf_comm, hWS, Subgroup.card_bot, mul_one, hS256] at hcard
    refine Subgroup.eq_of_le_of_card_ge (sup_le hSS₁ hWS₁) ?_
    rw [hcard, ← hWc, mul_comm]
  have htop : (E ⊔ F).subgroupOf S₁ ⊔ W.subgroupOf S₁ = ⊤ := by
    apply Subgroup.map_injective S₁.subtype_injective
    rw [Subgroup.map_sup, subgroupOf_map_subtype, subgroupOf_map_subtype,
      inf_eq_left.mpr hSS₁, inf_eq_left.mpr hWS₁, hsup, ← MonoidHom.range_eq_map,
      range_subtype]
  rw [← map_rho_sup hSS₁ hS256 hΘS hρi hρS h44, ← Subgroup.map_sup, htop,
    MonoidHom.range_eq_map]


omit [Finite G] in
theorem factorization_two_pow_mul_nine (k : ℕ) : (2 ^ k * 9).factorization 2 = k := by
  rw [Nat.factorization_mul (by positivity) (by norm_num), Finsupp.coe_add, Pi.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 9), add_zero]

include hWS₁ hWS hWc hSS₁ hS₁N hS256 hΘS hΘi hΘm hρi hρS hρW in
theorem nonempty_equiv_Y32_of_rho (h44 : step44Check = true) {T : Subgroup G}
    (hWT : W ≤ normalizer (T : Set G)) (hΘ1 : ∃ t₁ ∈ T, ∀ i, t₁ * Θ i * t₁⁻¹ = Θ (smTauF 1 0 i))
    (hΘ2 : ∃ t₂ ∈ T, ∀ i, t₂ * Θ i * t₂⁻¹ = Θ (smTauF 0 1 i))
    (hΘT : ∀ t ∈ T, ∃ a b : ℕ, ∀ i, t * Θ i * t⁻¹ = Θ (smTauF a b i)) (hW8 : Nat.card W = 8) :
    Nonempty (↥S₁ ≃* ↥Y32) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : (W.subgroupOf S₁).map ρ ≤ hexaN := by
    rintro _ ⟨w, hw, rfl⟩
    exact rho_mem_hexaN hWS₁ hΘi hΘm hρW h44 hWT hΘ1 hΘ2 hΘT (w := w) hw
  have hcard : Nat.card ((W.subgroupOf S₁).map ρ) = 8 := by
    rw [Subgroup.card_map_of_injective hρi, Nat.card_congr (subgroupOfEquivOfLe hWS₁).toEquiv,
      hW8]
  have h72 : (Nat.card hexaN).factorization 2 = 3 := by
    rw [card_hexaN h44, show (72 : ℕ) = 2 ^ 3 * 9 by norm_num, factorization_two_pow_mul_nine]
  have hsyl : IsSylowOf 2 ((W.subgroupOf S₁).map ρ) hexaN :=
    isSylowOf_of_card hle (by rw [hcard, h72]; norm_num)
  have hsylP : IsSylowOf 2 hexaP hexaN :=
    isSylowOf_of_card (hexaP_le_hexaN h44) (by rw [card_hexaP h44, h72]; norm_num)
  obtain ⟨β, hβ, hβx⟩ := hsylP.exists_mem_conj hsyl
  have hβA : β ∈ smAut := hexaN_le_smAut h44 hβ
  have hL : smLamGrp.map (MulAut.conj β).toMonoidHom = smLamGrp := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact conj_mem_smLamGrp hSS₁ hS256 hΘS hΘi hρi hρS h44 hβA hy
    · intro x hx
      refine ⟨β⁻¹ * x * β⁻¹⁻¹,
        conj_mem_smLamGrp hSS₁ hS256 hΘS hΘi hρi hρS h44 (inv_mem hβA) hx, ?_⟩
      show β * (β⁻¹ * x * β⁻¹⁻¹) * β⁻¹ = x
      group
  have hP : (W.subgroupOf S₁).map ρ = hexaP.map (MulAut.conj β).toMonoidHom := by
    ext x
    rw [hβx, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hrange : ρ.range = hexaAb.map (MulAut.conj β).toMonoidHom := by
    rw [range_rho hWS₁ hWS hWc hSS₁ hS₁N hS256 hΘS hρi hρS h44, hexaAb_eq, Subgroup.map_sup, hL,
      hP]
  obtain ⟨e⟩ := nonempty_hexaAb_equiv h44
  exact ⟨(MonoidHom.ofInjective hρi).trans ((MulEquiv.subgroupCongr hrange).trans
    ((hexaAb.equivMapOfInjective (MulAut.conj β).toMonoidHom (MulAut.conj β).injective).symm.trans
      e))⟩

include hWS₁ hWS hWc hSS₁ hS₁N hS256 hΘS hΘi hΘm hρi hρS hρW in
theorem nonempty_equiv_X16_of_rho (h44 : step44Check = true) {T : Subgroup G}
    (hWT : W ≤ normalizer (T : Set G)) (hΘ1 : ∃ t₁ ∈ T, ∀ i, t₁ * Θ i * t₁⁻¹ = Θ (smTauF 1 0 i))
    (hΘ2 : ∃ t₂ ∈ T, ∀ i, t₂ * Θ i * t₂⁻¹ = Θ (smTauF 0 1 i))
    (hΘT : ∀ t ∈ T, ∃ a b : ℕ, ∀ i, t * Θ i * t⁻¹ = Θ (smTauF a b i))
    (hΘE : ∀ i, Θ i ∈ E ↔ i.val < 64) (hWE : W ≤ normalizer (E : Set G)) (hW4 : Nat.card W = 4) :
    Nonempty (↥S₁ ≃* ↥X16) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : (W.subgroupOf S₁).map ρ ≤ hexaNE := by
    rintro _ ⟨w, hw, rfl⟩
    refine mem_hexaNE_of h44 (rho_mem_hexaN hWS₁ hΘi hΘm hρW h44 hWT hΘ1 hΘ2 hΘT (w := w) hw)
      fun i hi => ?_
    have h1 := hρW w hw i
    have e : (⟨(w : G), hWS₁ hw⟩ : ↥S₁) = w := rfl
    rw [e] at h1
    rw [← hΘE, h1]
    exact (mem_normalizer_iff.mp (hWE hw) _).mp ((hΘE i).2 hi)
  have hcard : Nat.card ((W.subgroupOf S₁).map ρ) = 4 := by
    rw [Subgroup.card_map_of_injective hρi, Nat.card_congr (subgroupOfEquivOfLe hWS₁).toEquiv,
      hW4]
  have h36 : (Nat.card hexaNE).factorization 2 = 2 := by
    rw [card_hexaNE h44, show (36 : ℕ) = 2 ^ 2 * 9 by norm_num, factorization_two_pow_mul_nine]
  have hsyl : IsSylowOf 2 ((W.subgroupOf S₁).map ρ) hexaNE :=
    isSylowOf_of_card hle (by rw [hcard, h36]; norm_num)
  have hsylP : IsSylowOf 2 hexaPE hexaNE :=
    isSylowOf_of_card (hexaPE_le_hexaNE h44) (by rw [card_hexaPE h44, h36]; norm_num)
  obtain ⟨β, hβ, hβx⟩ := hsylP.exists_mem_conj hsyl
  have hβA : β ∈ smAut := hexaN_le_smAut h44 (hexaNE_le_hexaN h44 hβ)
  have hL : smLamGrp.map (MulAut.conj β).toMonoidHom = smLamGrp := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact conj_mem_smLamGrp hSS₁ hS256 hΘS hΘi hρi hρS h44 hβA hy
    · intro x hx
      refine ⟨β⁻¹ * x * β⁻¹⁻¹,
        conj_mem_smLamGrp hSS₁ hS256 hΘS hΘi hρi hρS h44 (inv_mem hβA) hx, ?_⟩
      show β * (β⁻¹ * x * β⁻¹⁻¹) * β⁻¹ = x
      group
  have hP : (W.subgroupOf S₁).map ρ = hexaPE.map (MulAut.conj β).toMonoidHom := by
    ext x
    rw [hβx, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hrange : ρ.range = hexaAa.map (MulAut.conj β).toMonoidHom := by
    rw [range_rho hWS₁ hWS hWc hSS₁ hS₁N hS256 hΘS hρi hρS h44, hexaAa_eq, Subgroup.map_sup, hL,
      hP]
  obtain ⟨e⟩ := nonempty_hexaAa_equiv h44
  exact ⟨(MonoidHom.ofInjective hρi).trans ((MulEquiv.subgroupCongr hrange).trans
    ((hexaAa.equivMapOfInjective (MulAut.conj β).toMonoidHom (MulAut.conj β).injective).symm.trans
      e))⟩

end Img

end Rho

theorem sylow_equiv_model (hc15 : hexaCheck = true) (hS : hexaStabCheck = true)
    (h44 : step44Check = true) {A R : Subgroup G} {g : G}
    (hD : PlaneData G A R g E F) (hD' : PlaneData G A R g F E) {S₁ : Subgroup G}
    (hS₁ : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G))) :
    (Nat.card S₁ = 2 ^ 10 ∧ Nonempty (↥S₁ ≃* ↥X16)) ∨
      (Nat.card S₁ = 2 ^ 11 ∧ Nonempty (↥S₁ ≃* ↥Y32)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨rep, hc, hRg⟩ := PlaneData.exists_hexaCoord_Rg hS hD hD'
  obtain ⟨W, T, hWS₁, hWS, hWc, hWT, hTK, hT3, hTψ⟩ :=
    exists_complement hc15 hS h44 hD hD' hc hRg hS₁
  obtain ⟨Θ, hΘS, hΘi, hΘm, hΘE, hΘ1, hΘ2, hΘT⟩ :=
    exists_thetaS hc15 hS h44 hD hc hRg hTK hT3 hTψ
  have hSS₁ : E ⊔ F ≤ S₁ := hD.sup_le_sylow hS₁
  have hS256 : Nat.card (E ⊔ F : Subgroup G) = 2 ^ 8 := hD.card_sup
  have hWC : ∀ w ∈ W, (∀ s ∈ E ⊔ F, w * s * w⁻¹ = s) → w = 1 := by
    intro w hw hws
    obtain ⟨k, hk⟩ := hS₁.isPGroup ⟨w, hWS₁ hw⟩
    have hk' : w ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hwC : w ∈ centralizer (E : Set G) := mem_centralizer_iff.mpr fun e he => by
      calc e * w = (w * e * w⁻¹) * w := by rw [hws e (mem_sup_left he)]
        _ = w * e := by group
    rw [hD.centralizer_eq] at hwC
    have hwE := mem_of_mem_sup_odd' (hD.isPGroup_sup.to_le le_sup_left)
      (AS76b.odd_card_oddCoreIn _) (hD.centralizer_eq ▸ le_sup_right) hwC hk'
    have h1 : w ∈ W ⊓ (E ⊔ F) := Subgroup.mem_inf.mpr ⟨hw, mem_sup_left hwE⟩
    rwa [hWS, mem_bot] at h1
  obtain ⟨ρ, hρi, hρS, hρW⟩ := exists_rho hWS₁ hWS hWc hSS₁ hS₁.le hS256 hΘS hΘi hΘm hWC
  have hle : (W.subgroupOf S₁).map ρ ≤ hexaN := by
    rintro _ ⟨w, hw, rfl⟩
    exact rho_mem_hexaN hWS₁ hΘi hΘm hρW h44 hWT hΘ1 hΘ2 hΘT (w := w) hw
  have hdvd : Nat.card W ∣ 72 := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective hρi, Nat.card_congr (subgroupOfEquivOfLe hWS₁).toEquiv,
      card_hexaN h44] at h
  have h10 : 2 ^ 10 ≤ Nat.card S₁ := by
    rw [← hD.card_inf_sylow hD' hS₁]
    exact Subgroup.card_le_of_le inf_le_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hS₁.isPGroup.to_le hWS₁)
  have hk3 : k ≤ 3 := by
    by_contra h
    have h16 : 2 ^ 4 ∣ 72 := (pow_dvd_pow 2 (by omega : 4 ≤ k)).trans (hk ▸ hdvd)
    norm_num at h16
  rw [← hWc, hk] at h10
  interval_cases k
  · norm_num at h10
  · norm_num at h10
  · have hcard : Nat.card S₁ = 2 ^ 10 := by rw [← hWc, hk]; norm_num
    have hS₁E : S₁ ≤ normalizer (E : Set G) := by
      have h := Subgroup.eq_of_le_of_card_ge (inf_le_left : S₁ ⊓ normalizer (E : Set G) ≤ S₁)
        (by rw [hcard, hD.card_inf_sylow hD' hS₁])
      rw [← h]
      exact inf_le_right
    exact Or.inl ⟨hcard, nonempty_equiv_X16_of_rho hWS₁ hWS hWc hSS₁ hS₁.le hS256 hΘS hΘi hΘm
      hρi hρS hρW h44 hWT hΘ1 hΘ2 hΘT hΘE (hWS₁.trans hS₁E) (by rw [hk]; norm_num)⟩
  · have hcard : Nat.card S₁ = 2 ^ 11 := by rw [← hWc, hk]; norm_num
    exact Or.inr ⟨hcard, nonempty_equiv_Y32_of_rho hWS₁ hWS hWc hSS₁ hS₁.le hS256 hΘS hΘi hΘm
      hρi hρS hρW h44 hWT hΘ1 hΘ2 hΘT (by rw [hk]; norm_num)⟩

end CFSG.ComponentClassification.AS81
