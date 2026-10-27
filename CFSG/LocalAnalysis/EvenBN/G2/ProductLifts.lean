module

public import CFSG.LocalAnalysis.EvenBN.G2.ProductN1Decomp
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.H13.J4Order

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

section Part1

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc
  mem_centerMod_iff mem_centralizerMod_iff)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_inf mem_normalizer_sup
  map_conj_eq_of_mem_normalizer mem_normalizer_of_map_conj_eq)

namespace ProductLiftsAux

section Factor

variable {G : Type*} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2]

theorem sl2_not_isPGroup (hK4 : 4 ≤ Nat.card K) : ¬ IsPGroup 2 SL(2, K) := by
  intro hp
  haveI := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK4
  haveI := Common.sl2_isSimpleGroup_of_charTwo (k := K) hK4
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent SL(2, K) := hp.isNilpotent
  haveI : Group.IsSolvable SL(2, K) := inferInstance
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial SL(2, K)
  rw [Group.IsPerfect.commutator_eq_top] at h1
  exact lt_irrefl _ h1

theorem factor_perfect {N M L Ast : Subgroup G} (hLN : L ≤ N) (hML : M ≤ L)
    (hN : ∀ x ∈ N, ∃ a ∈ Ast, ∃ m ∈ M, x = a * m) (hAM : Ast ⊓ M = ⊥)
    (hq : IsQuotientIso L M SL(2, K)) (hK4 : 4 ≤ Nat.card K) :
    ⁅L ⊓ Ast, L ⊓ Ast⁆ = L ⊓ Ast := by
  obtain ⟨φ, hφ, hker⟩ := hq
  set A : Subgroup G := L ⊓ Ast with hA
  have hAL : A ≤ L := inf_le_left
  let ψ : A →* SL(2, K) := φ.comp (Subgroup.inclusion hAL)
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : Subgroup.inclusion hAL x ∈ φ.ker := hx
    rw [hker, mem_subgroupOf] at hx1
    have : (x : G) ∈ Ast ⊓ M := ⟨x.2.2, hx1⟩
    rw [hAM, mem_bot] at this
    exact Subtype.ext this
  have hψsurj : Function.Surjective ψ := by
    intro s
    obtain ⟨l, rfl⟩ := hφ s
    obtain ⟨a, ha, m, hm, hlam⟩ := hN l (hLN l.2)
    have haL : a ∈ L := by
      have : a = (l : G) * m⁻¹ := by rw [hlam]; group
      rw [this]; exact mul_mem l.2 (inv_mem (hML hm))
    refine ⟨⟨a, haL, ha⟩, ?_⟩
    have hmker : φ ⟨m, hML hm⟩ = 1 := by
      have : (⟨m, hML hm⟩ : L) ∈ φ.ker := by rw [hker, mem_subgroupOf]; exact hm
      exact this
    have : l = Subgroup.inclusion hAL ⟨a, haL, ha⟩ * ⟨m, hML hm⟩ := Subtype.ext hlam
    simp only [ψ, MonoidHom.comp_apply, this, map_mul, hmker, mul_one]
  let e : A ≃* SL(2, K) := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  haveI := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK4
  haveI : Group.IsPerfect A :=
    Group.IsPerfect.ofSurjective (f := (e.symm : SL(2, K) →* A)) e.symm.surjective
  have h2 := congrArg (Subgroup.map A.subtype) (Group.IsPerfect.commutator_eq_top (G := A))
  rwa [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h2

theorem mem_normalizer_commutator_self {L : Subgroup G} {g : G}
    (hg : g ∈ normalizer (L : Set G)) : g ∈ normalizer (⁅L, L⁆ : Subgroup G) := by
  apply mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer hg]

section PCore

variable [Finite G]

theorem pCoreOf_eq_inf {M L H : Subgroup G} (hM2 : IsPGroup 2 M)
    (hLM : L ≤ normalizer (M : Set G)) (hHL : H ≤ L) (hLH : L ≤ normalizer (H : Set G))
    (hq : IsQuotientIso L M SL(2, K)) (hK4 : 4 ≤ Nat.card K) :
    pCoreOf 2 H = H ⊓ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ ?_
  · set X : Subgroup G := pCoreOf 2 H with hX
    have hXH : X ≤ H := LieType.BorelTits.pCoreOf_le 2 H
    have hXL : X ≤ L := hXH.trans hHL
    have hLX : L ≤ normalizer (X : Set G) := fun g hg =>
      LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H (hLH hg)
    obtain ⟨φ, hφ, hker⟩ := hq
    haveI : (X.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer hXL).2 hLX
    haveI := Common.sl2_isSimpleGroup_of_charTwo (k := K) hK4
    have hXp : IsPGroup 2 X := LieType.BorelTits.pCoreOf_isPGroup 2 H
    have hYp : IsPGroup 2 (X.subgroupOf L) := hXp.comap_subtype
    haveI hnm : ((X.subgroupOf L).map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
    have hmap : (X.subgroupOf L).map φ = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((X.subgroupOf L).map φ) with h | h
      · exact h
      · exfalso
        have hp : IsPGroup 2 ((X.subgroupOf L).map φ) := hYp.map φ
        rw [h] at hp
        exact sl2_not_isPGroup hK4 (hp.of_equiv Subgroup.topEquiv)
    intro x hx
    refine ⟨hXH hx, ?_⟩
    have h1 : (⟨x, hXL hx⟩ : L) ∈ X.subgroupOf L := hx
    have h2 : φ ⟨x, hXL hx⟩ = 1 := by
      have := Subgroup.mem_map_of_mem φ h1
      rwa [hmap, mem_bot] at this
    have h3 : (⟨x, hXL hx⟩ : L) ∈ φ.ker := h2
    rw [hker, mem_subgroupOf] at h3
    exact h3
  · refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ (hM2.to_le inf_le_right)
    intro h hh
    exact mem_normalizer_inf (hLH (hHL hh)) (hLM (hHL hh))

end PCore

end Factor

section Transfer

theorem central_mem_commutator_of_perfect {Γ : Type*} [Group Γ] [Finite Γ]
    (hΓ : Group.IsPerfect Γ) {Q : Subgroup Γ} (hQ : Odd Q.index) {z : Γ} (hzQ : z ∈ Q)
    (hzc : ∀ g : Γ, g * z = z * g) {e : ℕ} (hze : z ^ (2 ^ e) = 1) : z ∈ ⁅Q, Q⁆ := by
  classical
  let ϕ : Q →* Abelianization Q := Abelianization.of
  let τ : Γ →* Abelianization Q := MonoidHom.transfer ϕ
  have hτ : ∀ g : Γ, τ g = 1 := by
    intro g
    have h1 : commutator Γ ≤ τ.ker := Abelianization.commutator_subset_ker τ
    rw [hΓ.commutator_eq_top] at h1
    exact h1 (mem_top g)
  have key : ∀ (k : ℕ) (g₀ : Γ), g₀⁻¹ * z ^ k * g₀ ∈ Q → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc : g₀ * z ^ k = z ^ k * g₀ := (Commute.pow_right (hzc g₀) k).eq
    calc g₀⁻¹ * z ^ k * g₀ = g₀⁻¹ * (z ^ k * g₀) := by group
      _ = g₀⁻¹ * (g₀ * z ^ k) := by rw [hc]
      _ = z ^ k := by group
  have h2 := MonoidHom.transfer_eq_pow ϕ z key
  have h3 := hτ z
  have h4 : ϕ ⟨z ^ Q.index, MonoidHom.transfer_eq_pow_aux z key⟩ = 1 := by
    rw [← h2]; exact h3
  have h5 : (⟨z ^ Q.index, MonoidHom.transfer_eq_pow_aux z key⟩ : Q) ∈ commutator Q := by
    rw [← Abelianization.ker_of]; exact h4
  have h6 : z ^ Q.index ∈ ⁅Q, Q⁆ := by
    have := Subgroup.mem_map_of_mem Q.subtype h5
    rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_subtype] at this
  have hcop : Nat.Coprime Q.index (orderOf z) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hze)
      (Nat.Coprime.pow_right e hQ.coprime_two_right)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hcop (orderOf_pos z).ne'
  have h7 : z ^ (Q.index * m) = z := by
    rw [← pow_mod_orderOf, hm, pow_mod_orderOf, pow_one]
  rw [← h7, pow_mul]
  exact pow_mem h6 m

theorem mem_commutator_sup_of_central_section {G : Type*} [Group G] [Finite G]
    {K Y Q : Subgroup G} (hYK : Y ≤ K) (hKY : K ≤ normalizer (Y : Set G))
    (hperf : K ≤ ⁅K, K⁆ ⊔ Y) (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q K) {z : G} (hzQ : z ∈ Q)
    (hz : ∀ g ∈ K, ⁅z, g⁆ ∈ Y) : z ∈ ⁅Q, Q⁆ ⊔ Y := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQK, hQ2, hQidx⟩ := (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).1 hQ
  have hzK : z ∈ K := hQK hzQ
  haveI hYn : (Y.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hYK).2 hKY
  let π : K →* K ⧸ Y.subgroupOf K := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Y.subgroupOf K := QuotientGroup.ker_mk' _
  have hKK : ⁅K, K⁆ ≤ K := commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]; exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hmapK : map K.subtype (commutator K) = ⁅K, K⁆ := by
    rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  have hmapπ : map π (commutator K) = commutator (K ⧸ Y.subgroupOf K) := by
    rw [commutator_def, commutator_def, map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 hπ]
  have hΓ : Group.IsPerfect (K ⧸ Y.subgroupOf K) := by
    refine ⟨eq_top_iff.2 fun γ _ => ?_⟩
    obtain ⟨k, rfl⟩ := hπ γ
    have hk := hperf k.2
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right ⁅K, K⁆ Y (hKK.trans hKY)] at hk
    obtain ⟨c, hc, y, hy, hcy⟩ := Set.mem_mul.1 hk
    have hcK : c ∈ K := hKK hc
    have hcmem : (⟨c, hcK⟩ : K) ∈ commutator K := by
      rw [← hmapK] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      exact hc'
    rw [← hmapπ]
    have hπk : π k = π ⟨c, hcK⟩ := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hcy]
      simpa using inv_mem hy
    rw [hπk]
    exact mem_map_of_mem π hcmem
  set QK : Subgroup K := Q.subgroupOf K with hQK'
  set Q' : Subgroup (K ⧸ Y.subgroupOf K) := QK.map π with hQ'
  have hQ'odd : Odd Q'.index := by
    have h1 : Q'.index ∣ QK.index := by
      rw [hQ', Subgroup.index_map, MonoidHom.range_eq_top.2 hπ, index_top, mul_one]
      exact Subgroup.index_dvd_of_le le_sup_left
    have h2 : Odd QK.index := by
      have : ¬ 2 ∣ QK.index := hQidx
      exact Nat.odd_iff.2 (by omega)
    exact h2.of_dvd_nat h1
  have hzQK : (⟨z, hzK⟩ : K) ∈ QK := hzQ
  obtain ⟨e, he⟩ := hQ2 ⟨z, hzQ⟩
  have hze : z ^ (2 ^ e) = 1 := congrArg Subtype.val he
  have hzc : ∀ γ : K ⧸ Y.subgroupOf K, γ * π ⟨z, hzK⟩ = π ⟨z, hzK⟩ * γ := by
    intro γ
    obtain ⟨k, rfl⟩ := hπ γ
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      mem_subgroupOf]
    have hkz : (k : G) * z ∈ normalizer (Y : Set G) := mul_mem (hKY k.2) (hKY hzK)
    have h1 : ((k : G) * z)⁻¹ * ⁅z, (k : G)⁆ * ((k : G) * z) ∈ Y :=
      ((mem_normalizer_iff''.1 hkz _).1 (hz k k.2))
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have e1 : ((k : G) * z)⁻¹ * ⁅z, (k : G)⁆ * ((k : G) * z) = ((k : G) * z)⁻¹ * (z * k) := by
      simp only [commutatorElement_def]; group
    rwa [e1] at h1
  have hQ'1 := central_mem_commutator_of_perfect hΓ hQ'odd (mem_map_of_mem π hzQK) hzc (e := e)
    (by rw [← map_pow]; exact (by
      have : (⟨z, hzK⟩ : K) ^ (2 ^ e) = 1 := Subtype.ext hze
      rw [this, map_one]))
  rw [hQ', ← Subgroup.map_commutator] at hQ'1
  obtain ⟨c, hc, hcz⟩ := hQ'1
  have hcQ : (c : G) ∈ ⁅Q, Q⁆ := by
    have h1 : map K.subtype ⁅QK, QK⁆ = ⁅Q, Q⁆ := by
      rw [Subgroup.map_commutator, hQK', Subgroup.subgroupOf_map_subtype, inf_of_le_left hQK]
    rw [← h1]
    exact mem_map_of_mem K.subtype hc
  have h2 : (c : G)⁻¹ * z ∈ Y := by
    have := QuotientGroup.eq.1 hcz
    rw [mem_subgroupOf] at this
    simpa using this
  have : z = (c : G) * ((c : G)⁻¹ * z) := by group
  rw [this]
  exact mul_mem (mem_sup_left hcQ) (mem_sup_right h2)

end Transfer

section Diagonal

variable {Γ : Type*} [Group Γ]

theorem mem_conjg_iff_of_invol {τ : Γ} (hτ : τ * τ = 1) {X : Subgroup Γ} {x : Γ} :
    x ∈ Xᵍ[τ] ↔ τ * x * τ ∈ X := by
  rw [Common.mem_map_conj_inv_iff, inv_eq_of_mul_eq_one_right hτ]

theorem conj_mem_conjg_of_invol {τ : Γ} (hτ : τ * τ = 1) {X : Subgroup Γ} {x : Γ}
    (hx : x ∈ X) : τ * x * τ ∈ Xᵍ[τ] := by
  rw [mem_conjg_iff_of_invol hτ]
  have : τ * (τ * x * τ) * τ = x := by
    calc τ * (τ * x * τ) * τ = (τ * τ) * x * (τ * τ) := by group
      _ = x := by rw [hτ]; group
  rw [this]; exact hx

theorem commutatorElement_mul_left_of_commute {e a b : Γ} (hea : e * a = a * e)
    (heb : e * b = b * e) : ⁅e * a, b⁆ = ⁅a, b⁆ := by
  have h1 : e * (a * b * a⁻¹) = (a * b * a⁻¹) * e := by
    have hai : e * a⁻¹ = a⁻¹ * e := (Commute.inv_right (show Commute e a from hea)).eq
    calc e * (a * b * a⁻¹) = (e * a) * b * a⁻¹ := by group
      _ = a * (e * b) * a⁻¹ := by rw [hea]; group
      _ = a * (b * e) * a⁻¹ := by rw [heb]
      _ = a * b * (e * a⁻¹) := by group
      _ = a * b * (a⁻¹ * e) := by rw [hai]
      _ = (a * b * a⁻¹) * e := by group
  simp only [commutatorElement_def]
  calc e * a * b * (e * a)⁻¹ * b⁻¹ = e * (a * b * a⁻¹) * e⁻¹ * b⁻¹ := by group
    _ = (a * b * a⁻¹) * e * e⁻¹ * b⁻¹ := by rw [h1]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_right_of_commute {e a b : Γ} (hea : e * a = a * e)
    (heb : e * b = b * e) : ⁅a, e * b⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv (e * b) a, commutatorElement_mul_left_of_commute heb hea,
    commutatorElement_inv]

theorem sup_conjg_commutator_eq_bot {τ : Γ} {B₁ B₂ : Subgroup Γ}
    (h11 : ⁅B₁, B₁ᵍ[τ]⁆ = ⊥) (h22 : ⁅B₂, B₂ᵍ[τ]⁆ = ⊥) (h12 : ⁅B₁, B₂ᵍ[τ]⁆ = ⊥)
    (h21 : ⁅B₂, B₁ᵍ[τ]⁆ = ⊥) : ⁅B₂ ⊔ B₁, (B₂ ⊔ B₁)ᵍ[τ]⁆ = ⊥ := by
  rw [Subgroup.map_sup, commutator_eq_bot_iff_le_centralizer]
  refine sup_le ?_ ?_
  · rw [le_centralizer_iff]
    exact sup_le (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 h22))
      (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 h21))
  · rw [le_centralizer_iff]
    exact sup_le (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 h12))
      (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 h11))

theorem commutator_fixed_eq_diag {τ : Γ} (hτ : τ * τ = 1) {B₁ B₂ : Subgroup Γ}
    (h11 : ⁅B₁, B₁ᵍ[τ]⁆ = ⊥) (h22 : ⁅B₂, B₂ᵍ[τ]⁆ = ⊥) (h12 : ⁅B₁, B₂ᵍ[τ]⁆ = ⊥)
    (h21 : ⁅B₂, B₁ᵍ[τ]⁆ = ⊥) {S : Subgroup Γ} (hS : ∀ s ∈ S, τ * s * τ = s)
    (hdec : ∀ s ∈ S, ∃ b₂ ∈ B₂, ∃ x ∈ B₂, ∃ b₁ ∈ B₁, ∃ y ∈ B₁,
      s = b₂ * (τ * x * τ) * b₁ * (τ * y * τ))
    {s s' : Γ} (hs : s ∈ S) (hs' : s' ∈ S) :
    ∃ w ∈ ⁅B₂ ⊔ B₁, B₂ ⊔ B₁⁆, ⁅s, s'⁆ = w * (τ * w * τ) := by
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hττ : ∀ g : Γ, τ * (τ * g * τ) * τ = g := fun g => by
    calc τ * (τ * g * τ) * τ = (τ * τ) * g * (τ * τ) := by group
      _ = g := by rw [hτ]; group
  set Sg : Subgroup Γ := B₂ ⊔ B₁ with hSg
  have hSgc : ⁅Sg, Sgᵍ[τ]⁆ = ⊥ := sup_conjg_commutator_eq_bot h11 h22 h12 h21
  have hcomm : ∀ a ∈ Sg, ∀ b ∈ Sg, a * (τ * b * τ) = (τ * b * τ) * a := fun a ha b hb =>
    (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hSgc ha) _
      (conj_mem_conjg_of_invol hτ hb)).symm
  have core : ∀ s ∈ S, ∃ e ∈ Sg, ∃ f ∈ Sg, ∃ w₀ ∈ Sg, e = τ * f * τ ∧
      s = e * (w₀ * (τ * w₀ * τ)) := by
    intro s hs
    obtain ⟨b₂, hb₂, x, hx, b₁, hb₁, y, hy, hsd⟩ := hdec s hs
    have hu : b₂ * b₁ ∈ Sg := mul_mem (mem_sup_left hb₂) (mem_sup_right hb₁)
    have hw : x * y ∈ Sg := mul_mem (mem_sup_left hx) (mem_sup_right hy)
    have hb₁x : (τ * x * τ) * b₁ = b₁ * (τ * x * τ) :=
      mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 h12 hb₁) _
        (conj_mem_conjg_of_invol hτ hx)
    have hsu : s = (b₂ * b₁) * (τ * (x * y) * τ) := by
      rw [hsd]
      have : τ * (x * y) * τ = (τ * x * τ) * (τ * y * τ) := by
        calc τ * (x * y) * τ = τ * x * (τ * τ) * y * τ := by rw [hτ]; group
          _ = (τ * x * τ) * (τ * y * τ) := by group
      rw [this]
      calc b₂ * (τ * x * τ) * b₁ * (τ * y * τ)
          = b₂ * ((τ * x * τ) * b₁) * (τ * y * τ) := by group
        _ = b₂ * (b₁ * (τ * x * τ)) * (τ * y * τ) := by rw [hb₁x]
        _ = b₂ * b₁ * ((τ * x * τ) * (τ * y * τ)) := by group
    have hfix := hS s hs
    have h1 : (τ * (b₂ * b₁) * τ) * (x * y) = (b₂ * b₁) * (τ * (x * y) * τ) := by
      have h0 := hfix
      rw [hsu] at h0
      have e : τ * ((b₂ * b₁) * (τ * (x * y) * τ)) * τ = (τ * (b₂ * b₁) * τ) * (x * y) := by
        calc τ * ((b₂ * b₁) * (τ * (x * y) * τ)) * τ
            = (τ * (b₂ * b₁) * τ) * (x * y) * (τ * τ) := by group
          _ = (τ * (b₂ * b₁) * τ) * (x * y) := by rw [hτ, mul_one]
      rw [← e]; exact h0
    have hcw : (x * y) * (τ * (b₂ * b₁) * τ) = (τ * (b₂ * b₁) * τ) * (x * y) :=
      hcomm _ hw _ hu
    have h2 : (x * y) * (τ * (b₂ * b₁) * τ) = (b₂ * b₁) * (τ * (x * y) * τ) := hcw.trans h1
    have h3 : τ * (b₂ * b₁) * τ = (x * y)⁻¹ * ((b₂ * b₁) * (τ * (x * y) * τ)) :=
      eq_inv_mul_of_mul_eq h2
    have he : (x * y)⁻¹ * (b₂ * b₁) = τ * ((b₂ * b₁) * (x * y)⁻¹) * τ := by
      have e1 : τ * ((b₂ * b₁) * (x * y)⁻¹) * τ =
          (τ * (b₂ * b₁) * τ) * (τ * (x * y)⁻¹ * τ) := by
        calc τ * ((b₂ * b₁) * (x * y)⁻¹) * τ = τ * (b₂ * b₁) * (τ * τ) * (x * y)⁻¹ * τ := by
              rw [hτ]; group
          _ = (τ * (b₂ * b₁) * τ) * (τ * (x * y)⁻¹ * τ) := by group
      have e2 : τ * (x * y)⁻¹ * τ = (τ * (x * y) * τ)⁻¹ := by
        rw [show (τ * (x * y) * τ)⁻¹ = τ⁻¹ * (x * y)⁻¹ * τ⁻¹ by group, hτi]
      rw [e1, e2, h3]
      group
    have hfS : (b₂ * b₁) * (x * y)⁻¹ ∈ Sg := mul_mem hu (inv_mem hw)
    refine ⟨(x * y)⁻¹ * (b₂ * b₁), mul_mem (inv_mem hw) hu, (b₂ * b₁) * (x * y)⁻¹, hfS,
      x * y, hw, he, ?_⟩
    have hec : (x * y) * ((x * y)⁻¹ * (b₂ * b₁)) = ((x * y)⁻¹ * (b₂ * b₁)) * (x * y) := by
      rw [he]; exact hcomm _ hw _ hfS
    rw [hsu]
    calc (b₂ * b₁) * (τ * (x * y) * τ)
        = ((x * y) * ((x * y)⁻¹ * (b₂ * b₁))) * (τ * (x * y) * τ) := by group
      _ = (((x * y)⁻¹ * (b₂ * b₁)) * (x * y)) * (τ * (x * y) * τ) := by rw [hec]
      _ = ((x * y)⁻¹ * (b₂ * b₁)) * ((x * y) * (τ * (x * y) * τ)) := by group
  obtain ⟨e, he, f, hf, w₀, hw₀, hef, hsd⟩ := core s hs
  obtain ⟨e', he', f', hf', w₀', hw₀', hef', hsd'⟩ := core s' hs'
  have hcδ : ∀ c ∈ Sg, ∀ f ∈ Sg, c = τ * f * τ → ∀ w ∈ Sg,
      c * (w * (τ * w * τ)) = (w * (τ * w * τ)) * c := by
    intro c hc f hf hcf w hw
    have h1 : c * w = w * c := by
      rw [hcf]; exact (hcomm w hw f hf).symm
    have h2 : c * (τ * w * τ) = (τ * w * τ) * c := hcomm c hc w hw
    calc c * (w * (τ * w * τ)) = (c * w) * (τ * w * τ) := by group
      _ = (w * c) * (τ * w * τ) := by rw [h1]
      _ = w * (c * (τ * w * τ)) := by group
      _ = w * ((τ * w * τ) * c) := by rw [h2]
      _ = (w * (τ * w * τ)) * c := by group
  have hee' : e * e' = e' * e := by
    rw [hef']; exact hcomm e he f' hf'
  have hes' : e * s' = s' * e := by
    rw [hsd']
    calc e * (e' * (w₀' * (τ * w₀' * τ))) = (e * e') * (w₀' * (τ * w₀' * τ)) := by group
      _ = (e' * e) * (w₀' * (τ * w₀' * τ)) := by rw [hee']
      _ = e' * (e * (w₀' * (τ * w₀' * τ))) := by group
      _ = e' * ((w₀' * (τ * w₀' * τ)) * e) := by rw [hcδ e he f hf hef w₀' hw₀']
      _ = (e' * (w₀' * (τ * w₀' * τ))) * e := by group
  have hstep1 : ⁅s, s'⁆ = ⁅w₀ * (τ * w₀ * τ), s'⁆ := by
    rw [hsd]
    exact commutatorElement_mul_left_of_commute (hcδ e he f hf hef w₀ hw₀) hes'
  have hstep2 : ⁅w₀ * (τ * w₀ * τ), s'⁆ = ⁅w₀ * (τ * w₀ * τ), w₀' * (τ * w₀' * τ)⁆ := by
    rw [hsd']
    exact commutatorElement_mul_right_of_commute
      (hcδ e' he' f' hf' hef' w₀ hw₀) (hcδ e' he' f' hf' hef' w₀' hw₀')
  refine ⟨⁅w₀, w₀'⁆, Subgroup.commutator_mem_commutator hw₀ hw₀', ?_⟩
  rw [hstep1, hstep2]
  have hδ := map_commutatorElement (Common.diagonalHom Sg τ hSgc) ⟨w₀, hw₀⟩ ⟨w₀', hw₀'⟩
  rw [Common.diagonalHom_apply_of_mul_self hSgc hτ, Common.diagonalHom_apply_of_mul_self hSgc hτ,
    Common.diagonalHom_apply_of_mul_self hSgc hτ] at hδ
  exact hδ.symm

end Diagonal

section Coprime

variable {G : Type*} [Group G] [Finite G]

theorem fixed_mul_mem_of_coprime {X Z S Y : Subgroup G} (hXZ : X ≤ normalizer (Z : Set G))
    (hSX : S ≤ normalizer (X : Set G)) (hSZ : S ≤ normalizer (Z : Set G))
    (hsolv : Group.IsSolvable X) (hcop : (Nat.card S).Coprime (Nat.card X))
    (hCZ : Z ⊓ centralizer (S : Set G) ≤ Y) {b m : G} (hb : b ∈ X) (hm : m ∈ Z)
    (hfix : ∀ s ∈ S, s * (b * m) * s⁻¹ = b * m) : b * m ∈ X ⊔ Y := by
  have hNX : X ⊓ Z ≤ X := inf_le_left
  have hXN : X ≤ normalizer ((X ⊓ Z : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_inf (Subgroup.le_normalizer hx) (hXZ hx)
  have hSN : S ≤ normalizer ((X ⊓ Z : Subgroup G) : Set G) := fun s hs =>
    mem_normalizer_inf (hSX hs) (hSZ hs)
  have hf : ∀ s ∈ S, b⁻¹ * (s * b * s⁻¹) ∈ X ⊓ Z := by
    intro s hs
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hb) ((mem_normalizer_iff.1 (hSX hs) b).1 hb), ?_⟩
    have h1 := hfix s hs
    have e : b⁻¹ * (s * b * s⁻¹) = m * (s * m * s⁻¹)⁻¹ := by
      have : s * b * s⁻¹ = b * m * (s * m * s⁻¹)⁻¹ := by
        calc s * b * s⁻¹ = (s * (b * m) * s⁻¹) * (s * m * s⁻¹)⁻¹ := by group
          _ = (b * m) * (s * m * s⁻¹)⁻¹ := by rw [h1]
          _ = b * m * (s * m * s⁻¹)⁻¹ := rfl
      rw [this]; group
    rw [e]
    exact mul_mem hm (inv_mem ((mem_normalizer_iff.1 (hSZ hs) m).1 hm))
  obtain ⟨c, hc, n, hn, hbcn⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime hNX hXN hSX hSN
    hsolv hcop hb hf
  have hcX : c ∈ X := (Subgroup.mem_inf.1 hc).1
  have hcS : c ∈ centralizer (S : Set G) := (Subgroup.mem_inf.1 hc).2
  have hnZ : n ∈ Z := (Subgroup.mem_inf.1 hn).2
  have hnm : n * m ∈ Z ⊓ centralizer (S : Set G) := by
    refine Subgroup.mem_inf.2 ⟨mul_mem hnZ hm, mem_centralizer_iff.2 fun s hs => ?_⟩
    have hcs : s * c = c * s := mem_centralizer_iff.1 hcS s hs
    have hbm : b * m = c * (n * m) := by rw [hbcn]; group
    have h2 := hfix s hs
    rw [hbm] at h2
    have h3 : s * (n * m) = (n * m) * s := by
      have : c * (s * (n * m)) = c * ((n * m) * s) := by
        calc c * (s * (n * m)) = (c * s) * (n * m) := by group
          _ = (s * c) * (n * m) := by rw [hcs]
          _ = (s * (c * (n * m)) * s⁻¹) * s := by group
          _ = (c * (n * m)) * s := by rw [h2]
          _ = c * ((n * m) * s) := by group
      exact mul_left_cancel this
    exact h3
  rw [hbcn, mul_assoc]
  exact mul_mem (mem_sup_left hcX) (mem_sup_right (hCZ hnm))

end Coprime

section Centralizer

variable {G : Type*} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]

theorem le_pcore_of_centralizes {M L N Y : Subgroup G} (hLN : L ≤ N)
    (hNM : N ≤ normalizer (M : Set G)) (hNY : N ≤ normalizer (Y : Set G))
    (hNL : N ≤ normalizer (L : Set G)) (hML : M ≤ L)
    (hYB : Y ≤ ⁅L, L⁆ ⊓ M) (hq : IsQuotientIso L M SL(2, K)) (hK4 : 4 ≤ Nat.card K)
    (hBab : ∀ x ∈ ⁅L, L⁆ ⊓ M, ∀ y ∈ ⁅L, L⁆ ⊓ M, ⁅x, y⁆ ∈ Y)
    (hnc : ¬ ∀ b ∈ ⁅L, L⁆ ⊓ M, ∀ k ∈ ⁅L, L⁆, ⁅k, b⁆ ∈ Y) :
    ∀ k ∈ ⁅L, L⁆, (∀ y ∈ ⁅L, L⁆ ⊓ M, ⁅k, y⁆ ∈ Y) → k ∈ M := by
  set K' : Subgroup G := ⁅L, L⁆ with hK'
  set B : Subgroup G := K' ⊓ M with hB
  have hK'L : K' ≤ L := commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]; exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hLK' : L ≤ normalizer (K' : Set G) := fun g hg =>
    mem_normalizer_commutator_self (hNL (hLN hg))
  have hLB : L ≤ normalizer (B : Set G) := fun g hg =>
    mem_normalizer_inf (hLK' hg) (hNM (hLN hg))
  set C : Subgroup G := K' ⊓ centralizerMod Y B with hC
  have hCK' : C ≤ K' := inf_le_left
  have hCL : C ≤ L := hCK'.trans hK'L
  have hmemC : ∀ k, k ∈ C ↔ k ∈ K' ∧ ∀ y ∈ B, ⁅k, y⁆ ∈ Y := by
    intro k
    rw [hC, mem_inf, mem_centralizerMod_iff]
    constructor
    · rintro ⟨hk, -, h⟩
      exact ⟨hk, fun y hy => h y hy (hNY (hLN (hK'L (mem_inf.1 hy).1)))⟩
    · rintro ⟨hk, h⟩
      exact ⟨hk, hNY (hLN (hK'L hk)), fun y hy _ => h y hy⟩
  have hLC : L ≤ normalizer (C : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    have key : ∀ g ∈ L, ∀ k ∈ C, g * k * g⁻¹ ∈ C := by
      intro g hg k hk
      rw [hmemC] at hk ⊢
      refine ⟨(mem_normalizer_iff.1 (hLK' hg) k).1 hk.1, fun y hy => ?_⟩
      have hy' : g⁻¹ * y * g ∈ B := by
        have := (mem_normalizer_iff.1 (hLB (inv_mem hg)) y).1 hy
        simpa using this
      have h1 := hk.2 _ hy'
      have h2 : g * ⁅k, g⁻¹ * y * g⁆ * g⁻¹ ∈ Y := (mem_normalizer_iff.1 (hNY (hLN hg)) _).1 h1
      have e : g * ⁅k, g⁻¹ * y * g⁆ * g⁻¹ = ⁅g * k * g⁻¹, y⁆ := by
        simp only [commutatorElement_def]; group
      rwa [e] at h2
    intro x
    refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
    have := key g⁻¹ (inv_mem hg) _ hx
    simpa [mul_assoc] using this
  obtain ⟨φ, hφ, hker⟩ := hq
  haveI : (C.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer hCL).2 hLC
  haveI := Common.sl2_isSimpleGroup_of_charTwo (k := K) hK4
  haveI hnm : ((C.subgroupOf L).map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((C.subgroupOf L).map φ) with h | h
  · intro k hk hkc
    have hkC : k ∈ C := (hmemC k).2 ⟨hk, hkc⟩
    have h1 : (⟨k, hCL hkC⟩ : L) ∈ C.subgroupOf L := hkC
    have h2 : φ ⟨k, hCL hkC⟩ = 1 := by
      have := Subgroup.mem_map_of_mem φ h1
      rwa [h, mem_bot] at this
    have h3 : (⟨k, hCL hkC⟩ : L) ∈ φ.ker := h2
    rw [hker, mem_subgroupOf] at h3
    exact h3
  · exfalso
    apply hnc
    intro b hb k hk
    have hkL : k ∈ L := hK'L hk
    have hmem : φ ⟨k, hkL⟩ ∈ (C.subgroupOf L).map φ := by rw [h]; exact mem_top _
    obtain ⟨c, hc, hck⟩ := hmem
    have hcC : (c : G) ∈ C := hc
    have hm : (c : G)⁻¹ * k ∈ M := by
      have : c⁻¹ * ⟨k, hkL⟩ ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hck, inv_mul_cancel]
      rw [hker, mem_subgroupOf] at this
      simpa using this
    have hmK' : (c : G)⁻¹ * k ∈ K' := mul_mem (inv_mem (hCK' hcC)) hk
    have hmB : (c : G)⁻¹ * k ∈ B := mem_inf.2 ⟨hmK', hm⟩
    have hcb := ((hmemC _).1 hcC).2 b hb
    have hmb := hBab _ hmB b hb
    have e : ⁅k, b⁆ = ⁅(c : G) * ((c : G)⁻¹ * k), b⁆ := by
      congr 1; group
    rw [e]
    have e2 : ⁅(c : G) * ((c : G)⁻¹ * k), b⁆ =
        (c : G) * ⁅(c : G)⁻¹ * k, b⁆ * (c : G)⁻¹ * ⁅(c : G), b⁆ := by
      simp only [commutatorElement_def]; group
    rw [e2]
    exact mul_mem (mem_normalizer_iff.1 (hNY (hLN (hCL hcC))) _ |>.1 hmb) hcb

end Centralizer

section Step3

variable {G : Type*} [Group G]

theorem le_of_centralizes_mod {t : G} {Y W N L K₂ B₂ B₁ : Subgroup G}
    (hYN : N ≤ normalizer (Y : Set G))
    (hdec : ∀ x ∈ N, ∃ k ∈ K₂, ∃ k' ∈ K₂ᵍ[t], ∃ w ∈ W, x = k * k' * w)
    (hKK : ∀ k ∈ K₂, ∀ y ∈ K₂ᵍ[t], ⁅k, y⁆ ∈ Y)
    (hWN : ∀ w ∈ W, ∀ n ∈ N, ⁅w, n⁆ ∈ Y)
    (hcen : ∀ k' ∈ K₂ᵍ[t], (∀ y ∈ B₂ᵍ[t], ⁅k', y⁆ ∈ Y) → k' ∈ B₂ᵍ[t])
    (hB₁ : ∀ x ∈ B₁, ∀ y ∈ B₂ᵍ[t], ⁅x, y⁆ ∈ Y) (hB₁N : B₁ ≤ N)
    (hK₂N : K₂ ≤ N) (hK₂tN : K₂ᵍ[t] ≤ N) (hB₂K : B₂ᵍ[t] ≤ K₂ᵍ[t]) (hB₂N : B₂ᵍ[t] ≤ N)
    (hK₂L : K₂ ≤ L) (hWL : W ≤ L) (hB₂tL : B₂ᵍ[t] ≤ L) : B₁ ≤ L := by
  intro b hb
  obtain ⟨k, hk, k', hk', w, hw, hbkw⟩ := hdec b (hB₁N hb)
  have hkN := hK₂N hk
  have hk'N := hK₂tN hk'
  have hk'' : k' ∈ B₂ᵍ[t] := by
    refine hcen k' hk' fun y hy => ?_
    have hyN := hB₂N hy
    have h1 : ⁅b, y⁆ ∈ Y := hB₁ b hb y hy
    have h2 : ⁅w, y⁆ ∈ Y := hWN w hw y hyN
    have h3 : ⁅k, y⁆ ∈ Y := hKK k hk y (hB₂K hy)
    have e : ⁅b, y⁆ = (k * k') * ⁅w, y⁆ * (k * k')⁻¹ * (k * ⁅k', y⁆ * k⁻¹ * ⁅k, y⁆) := by
      rw [hbkw]; simp only [commutatorElement_def]; group
    rw [e] at h1
    have h4 : (k * k') * ⁅w, y⁆ * (k * k')⁻¹ ∈ Y :=
      (mem_normalizer_iff.1 (hYN (mul_mem hkN hk'N)) _).1 h2
    have h5 : k * ⁅k', y⁆ * k⁻¹ ∈ Y := by
      have := mul_mem (inv_mem h4) h1
      rw [inv_mul_cancel_left] at this
      have := mul_mem this (inv_mem h3)
      rwa [mul_inv_cancel_right] at this
    have h6 := (mem_normalizer_iff''.1 (hYN hkN) _).1 h5
    have e2 : k⁻¹ * (k * ⁅k', y⁆ * k⁻¹) * k = ⁅k', y⁆ := by group
    rwa [e2] at h6
  rw [hbkw]
  exact mul_mem (mul_mem (hK₂L hk) (hB₂tL hk'')) (hWL hw)

end Step3

end ProductLiftsAux

end Part1

section Part2

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc
  mem_centerMod_iff mem_centralizerMod_iff commutator_mem_iff_proj)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_inf mem_normalizer_sup
  map_conj_eq_of_mem_normalizer mem_normalizer_of_map_conj_eq)

namespace ProductLiftsAux

section DiagonalG

variable {Γ : Type*} [Group Γ]

theorem commutator_conjg_eq_bot_of_forall {τ : Γ} (hτ : τ * τ = 1) {A B : Subgroup Γ}
    (h : ∀ x ∈ A, ∀ y ∈ B, x * (τ * y * τ) = (τ * y * τ) * x) : ⁅A, Bᵍ[τ]⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [mem_centralizer_iff]
  intro z hz
  have hz' : τ * z * τ ∈ B := (mem_conjg_iff_of_invol hτ).1 hz
  have e : z = τ * (τ * z * τ) * τ := by
    calc z = (τ * τ) * z * (τ * τ) := by rw [hτ]; group
      _ = τ * (τ * z * τ) * τ := by group
  have := h x hx _ hz'
  rw [← e] at this
  exact this.symm

theorem commutator_sup_le_of_normalizes {A B : Subgroup Γ} (hAB : A ≤ normalizer (B : Set Γ))
    (hAab : ∀ x ∈ A, ∀ y ∈ A, ⁅x, y⁆ = 1) : ⁅A ⊔ B, A ⊔ B⁆ ≤ B := by
  rw [commutator_le]
  intro x hx y hy
  have hxe : x ∈ ((A : Set Γ) * B) := by
    rw [← coe_mul_of_left_le_normalizer_right A B hAB]; exact hx
  have hye : y ∈ ((A : Set Γ) * B) := by
    rw [← coe_mul_of_left_le_normalizer_right A B hAB]; exact hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hxe
  obtain ⟨a', ha', b', hb', rfl⟩ := Set.mem_mul.1 hye
  have hnB : ∀ g ∈ A ⊔ B, g ∈ normalizer (B : Set Γ) := fun g hg => by
    have : A ⊔ B ≤ normalizer (B : Set Γ) := sup_le hAB Subgroup.le_normalizer
    exact this hg
  have hy' : a' * b' ∈ normalizer (B : Set Γ) :=
    hnB _ (mul_mem (mem_sup_left ha') (mem_sup_right hb'))
  have h1 : ⁅a * b, a' * b'⁆ = a * ⁅b, a' * b'⁆ * a⁻¹ * ⁅a, a' * b'⁆ := by
    simp only [commutatorElement_def]; group
  have h2 : ⁅b, a' * b'⁆ ∈ B := by
    have : (a' * b') * b⁻¹ * (a' * b')⁻¹ ∈ B := (mem_normalizer_iff.1 hy' _).1 (inv_mem hb)
    have e : ⁅b, a' * b'⁆ = b * ((a' * b') * b⁻¹ * (a' * b')⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]; exact mul_mem hb this
  have h3 : ⁅a, a' * b'⁆ ∈ B := by
    have e : ⁅a, a' * b'⁆ = ⁅a, a'⁆ * (a' * ⁅a, b'⁆ * a'⁻¹) := by
      simp only [commutatorElement_def]; group
    have h4 : ⁅a, b'⁆ ∈ B := by
      have : a * b' * a⁻¹ ∈ B := (mem_normalizer_iff.1 (hAB ha) b').1 hb'
      rw [commutatorElement_def]; exact mul_mem this (inv_mem hb')
    have h5 : a' * ⁅a, b'⁆ * a'⁻¹ ∈ B := (mem_normalizer_iff.1 (hAB ha') _).1 h4
    rw [e, hAab a ha a' ha', one_mul]; exact h5
  rw [h1]
  exact mul_mem ((mem_normalizer_iff.1 (hAB ha) _).1 h2) h3

end DiagonalG

section Bar

open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient

variable {G : Type*} [Group G] {Y : Subgroup G}

theorem proj_mem_bar_iff {X : Subgroup G} (hXN : X ≤ normalizer (Y : Set G))
    (g : normalizer (Y : Set G)) : proj Y g ∈ bar Y X ↔ (g : G) ∈ X ⊔ Y := by
  constructor
  · rintro ⟨x, hx, hxg⟩
    have h1 := proj_eq_proj_iff.1 hxg
    have : (g : G) = (x : G) * ((x : G)⁻¹ * g) := by group
    rw [this]
    exact mul_mem (mem_sup_left (mem_subgroupOf.1 hx)) (mem_sup_right h1)
  · intro hg
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right X Y hXN] at hg
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.1 hg
    refine ⟨⟨x, hXN hx⟩, mem_subgroupOf.2 hx, ?_⟩
    rw [proj_eq_proj_iff]
    simp only
    rw [← hxy]
    simpa using hy

theorem lift_bar_eq_sup {X : Subgroup G} (hXN : X ≤ normalizer (Y : Set G)) :
    lift (bar Y X) = X ⊔ Y := by
  ext g
  rw [mem_lift_iff]
  constructor
  · rintro ⟨hg, h⟩
    exact (proj_mem_bar_iff hXN ⟨g, hg⟩).1 h
  · intro hg
    have hXY : X ⊔ Y ≤ normalizer (Y : Set G) := sup_le hXN le_normalizer
    exact ⟨hXY hg, (proj_mem_bar_iff hXN ⟨g, hXY hg⟩).2 hg⟩

theorem lift_inf (Y₁ Y₂ : Subgroup (Bar Y)) : lift (Y₁ ⊓ Y₂) = lift Y₁ ⊓ lift Y₂ := by
  ext g
  constructor
  · intro hg
    obtain ⟨hgN, h⟩ := mem_lift_iff.1 hg
    exact mem_inf.2 ⟨mem_lift_iff.2 ⟨hgN, (mem_inf.1 h).1⟩,
      mem_lift_iff.2 ⟨hgN, (mem_inf.1 h).2⟩⟩
  · intro hg
    obtain ⟨hgN, h1⟩ := mem_lift_iff.1 (mem_inf.1 hg).1
    obtain ⟨_, h2⟩ := mem_lift_iff.1 (mem_inf.1 hg).2
    exact mem_lift_iff.2 ⟨hgN, mem_inf.2 ⟨h1, h2⟩⟩

end Bar

section Alpha

open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient

variable {G : Type*} [Group G] [Finite G]

theorem alpha_le_B2 {t : G} (ht : t * t = 1) {Y B₁ B₂ P F5 S : Subgroup G} {q : ℕ}
    (hYt : t ∈ normalizer (Y : Set G)) (hPY : P ≤ normalizer (Y : Set G))
    (hB₁P : B₁ ≤ P) (hB₂P : B₂ ≤ P)
    (hB₁N : ∀ p ∈ P, ∀ b ∈ B₁, p * b * p⁻¹ ∈ B₁) (hB₂N : ∀ p ∈ P, ∀ b ∈ B₂, p * b * p⁻¹ ∈ B₂)
    (hYB₂ : Y ≤ B₂) (hYF : Y ≤ F5) (hF5P : F5 ≤ P)
    (hPP : ∀ p ∈ P, ∀ p' ∈ P, ⁅p, p'⁆ ∈ F5)
    (h11 : ∀ x ∈ B₁, ∀ y ∈ B₁ᵍ[t], ⁅x, y⁆ ∈ Y) (h22 : ∀ x ∈ B₂, ∀ y ∈ B₂ᵍ[t], ⁅x, y⁆ ∈ Y)
    (h12 : ∀ x ∈ B₁, ∀ y ∈ B₂ᵍ[t], ⁅x, y⁆ ∈ Y) (h21 : ∀ x ∈ B₂, ∀ y ∈ B₁ᵍ[t], ⁅x, y⁆ ∈ Y)
    (hab₁ : ∀ x ∈ B₁, ∀ y ∈ B₁, ⁅x, y⁆ ∈ Y) (hab₂ : ∀ x ∈ B₂, ∀ y ∈ B₂, ⁅x, y⁆ ∈ Y)
    (hSP : S ≤ P) (hSt : ∀ s ∈ S, t * s * t = s)
    (hdec : ∀ s ∈ S, ∃ b₂ ∈ B₂, ∃ b₂' ∈ B₂ᵍ[t], ∃ b₁ ∈ B₁, ∃ b₁' ∈ B₁ᵍ[t],
      s = b₂ * b₂' * b₁ * b₁')
    (hS : q ^ 2 * Nat.card Y ≤ Nat.card (⁅S, S⁆ ⊔ Y : Subgroup G))
    (hX : Nat.card ((B₁ ⊔ Y) ⊓ F5 : Subgroup G) ≤ q ^ 2 * Nat.card Y) :
    F5 ⊓ B₁ ≤ B₂ := by
  classical
  have hYN : Y ≤ normalizer (Y : Set G) := Subgroup.le_normalizer
  have hB₁N' : B₁ ≤ normalizer (Y : Set G) := hB₁P.trans hPY
  have hB₂N' : B₂ ≤ normalizer (Y : Set G) := hB₂P.trans hPY
  have hSN' : S ≤ normalizer (Y : Set G) := hSP.trans hPY
  have hFN' : F5 ≤ normalizer (Y : Set G) := hF5P.trans hPY
  have hPN' : P ≤ normalizer (Y : Set G) := hPY
  let π := proj Y
  let τ : Bar Y := π ⟨t, hYt⟩
  have hτ : τ * τ = 1 := by
    have : (⟨t, hYt⟩ * ⟨t, hYt⟩ : normalizer (Y : Set G)) = 1 := Subtype.ext ht
    rw [← map_mul, this, map_one]
  have hconj : ∀ (x : G) (hx : x ∈ normalizer (Y : Set G))
      (hx' : t * x * t ∈ normalizer (Y : Set G)),
      π ⟨t * x * t, hx'⟩ = τ * π ⟨x, hx⟩ * τ := by
    intro x hx hx'
    have : (⟨t * x * t, hx'⟩ : normalizer (Y : Set G)) = ⟨t, hYt⟩ * ⟨x, hx⟩ * ⟨t, hYt⟩ := rfl
    rw [this, map_mul, map_mul]
  have htN : ∀ x ∈ normalizer (Y : Set G), t * x * t ∈ normalizer (Y : Set G) := fun x hx =>
    mul_mem (mul_mem hYt hx) hYt
  have hbar : ∀ {X : Subgroup G} {z : Bar Y}, z ∈ bar Y X →
      ∃ x ∈ X, ∃ hx : x ∈ normalizer (Y : Set G), z = π ⟨x, hx⟩ := by
    rintro X z ⟨x, hx, rfl⟩
    exact ⟨x, mem_subgroupOf.1 hx, x.2, rfl⟩
  have hmemb : ∀ {X : Subgroup G} {x : G} (hx : x ∈ normalizer (Y : Set G)), x ∈ X →
      π ⟨x, hx⟩ ∈ bar Y X := fun hx hX => proj_mem_bar hX
  have hcomm : ∀ {A B : Subgroup G}, A ≤ normalizer (Y : Set G) → B ≤ normalizer (Y : Set G) →
      (∀ x ∈ A, ∀ y ∈ Bᵍ[t], ⁅x, y⁆ ∈ Y) →
      ∀ z ∈ bar Y A, ∀ w ∈ bar Y B, z * (τ * w * τ) = (τ * w * τ) * z := by
    intro A B hA hB h z hz w hw
    obtain ⟨x, hx, hxN, rfl⟩ := hbar hz
    obtain ⟨y, hy, hyN, rfl⟩ := hbar hw
    have hyt : t * y * t ∈ normalizer (Y : Set G) := htN y hyN
    rw [← hconj y hyN hyt]
    have h1 := h x hx (t * y * t) (conj_mem_conjg_of_invol ht hy)
    exact ((commutator_mem_iff_proj hxN hyt).2 (by simpa [commutatorElement_def] using h1)).symm
  set b₁ : Subgroup (Bar Y) := bar Y B₁ with hb₁
  set b₂ : Subgroup (Bar Y) := bar Y B₂ with hb₂
  set sb : Subgroup (Bar Y) := bar Y S with hsb
  have h11' : ⁅b₁, b₁ᵍ[τ]⁆ = ⊥ :=
    commutator_conjg_eq_bot_of_forall hτ (hcomm hB₁N' hB₁N' h11)
  have h22' : ⁅b₂, b₂ᵍ[τ]⁆ = ⊥ :=
    commutator_conjg_eq_bot_of_forall hτ (hcomm hB₂N' hB₂N' h22)
  have h12' : ⁅b₁, b₂ᵍ[τ]⁆ = ⊥ :=
    commutator_conjg_eq_bot_of_forall hτ (hcomm hB₁N' hB₂N' h12)
  have h21' : ⁅b₂, b₁ᵍ[τ]⁆ = ⊥ :=
    commutator_conjg_eq_bot_of_forall hτ (hcomm hB₂N' hB₁N' h21)
  have hSτ : ∀ z ∈ sb, τ * z * τ = z := by
    intro z hz
    obtain ⟨s, hs, hsN, rfl⟩ := hbar hz
    rw [← hconj s hsN (htN s hsN)]
    exact congrArg π (Subtype.ext (hSt s hs))
  have hconj' : ∀ (x : G) (hx : x ∈ normalizer (Y : Set G))
      (hx' : t * x * t ∈ normalizer (Y : Set G)),
      π ⟨x, hx⟩ = τ * π ⟨t * x * t, hx'⟩ * τ := by
    intro x hx hx'
    rw [hconj x hx hx']
    calc π ⟨x, hx⟩ = (τ * τ) * π ⟨x, hx⟩ * (τ * τ) := by rw [hτ]; group
      _ = τ * (τ * π ⟨x, hx⟩ * τ) * τ := by group
  have htt : ∀ g : G, t * (t * g * t) * t = g := fun g => by
    calc t * (t * g * t) * t = (t * t) * g * (t * t) := by group
      _ = g := by rw [ht]; group
  have hdecΓ : ∀ z ∈ sb, ∃ c₂ ∈ b₂, ∃ x ∈ b₂, ∃ c₁ ∈ b₁, ∃ y ∈ b₁,
      z = c₂ * (τ * x * τ) * c₁ * (τ * y * τ) := by
    intro z hz
    obtain ⟨s, hs, hsN, rfl⟩ := hbar hz
    obtain ⟨c₂, hc₂, d₂, hd₂, c₁, hc₁, d₁, hd₁, hsd⟩ := hdec s hs
    have hx : t * d₂ * t ∈ B₂ := (mem_conjg_iff_of_invol ht).1 hd₂
    have hy : t * d₁ * t ∈ B₁ := (mem_conjg_iff_of_invol ht).1 hd₁
    have hxN : t * d₂ * t ∈ normalizer (Y : Set G) := hB₂N' hx
    have hyN : t * d₁ * t ∈ normalizer (Y : Set G) := hB₁N' hy
    have hc₂N := hB₂N' hc₂
    have hc₁N := hB₁N' hc₁
    have hd₂N : d₂ ∈ normalizer (Y : Set G) := by
      have := htN _ hxN
      rwa [htt] at this
    have hd₁N : d₁ ∈ normalizer (Y : Set G) := by
      have := htN _ hyN
      rwa [htt] at this
    have e1 : (⟨s, hsN⟩ : normalizer (Y : Set G)) =
        ⟨c₂, hc₂N⟩ * ⟨d₂, hd₂N⟩ * ⟨c₁, hc₁N⟩ * ⟨d₁, hd₁N⟩ := Subtype.ext hsd
    refine ⟨π ⟨c₂, hc₂N⟩, hmemb hc₂N hc₂, π ⟨t * d₂ * t, hxN⟩, hmemb hxN hx,
      π ⟨c₁, hc₁N⟩, hmemb hc₁N hc₁, π ⟨t * d₁ * t, hyN⟩, hmemb hyN hy, ?_⟩
    rw [e1, map_mul, map_mul, map_mul, hconj' d₂ hd₂N hxN, hconj' d₁ hd₁N hyN]
  have hcommΓ : ∀ {A B : Subgroup G}, A ≤ normalizer (Y : Set G) → B ≤ normalizer (Y : Set G) →
      (∀ x ∈ A, ∀ y ∈ B, ⁅x, y⁆ ∈ Y) → ∀ z ∈ bar Y A, ∀ w ∈ bar Y B, z * w = w * z := by
    intro A B hA hB h z hz w hw
    obtain ⟨x, hx, hxN, rfl⟩ := hbar hz
    obtain ⟨y, hy, hyN, rfl⟩ := hbar hw
    have h1 := h x hx y hy
    exact ((commutator_mem_iff_proj hxN hyN).2 (by simpa [commutatorElement_def] using h1)).symm
  have hb₁ab : ∀ x ∈ b₁, ∀ y ∈ b₁, ⁅x, y⁆ = 1 := fun x hx y hy =>
    commutatorElement_eq_one_iff_mul_comm.2 (hcommΓ hB₁N' hB₁N' hab₁ x hx y hy)
  have hb₂ab : ∀ x ∈ b₂, ∀ y ∈ b₂, ⁅x, y⁆ = 1 := fun x hx y hy =>
    commutatorElement_eq_one_iff_mul_comm.2 (hcommΓ hB₂N' hB₂N' hab₂ x hx y hy)
  have hnormΓ : ∀ {A B : Subgroup G}, A ≤ P → B ≤ normalizer (Y : Set G) →
      (∀ p ∈ P, ∀ b ∈ B, p * b * p⁻¹ ∈ B) →
      bar Y A ≤ normalizer (bar Y B : Set (Bar Y)) := by
    intro A B hA hB hN z hz
    obtain ⟨x, hx, hxN, rfl⟩ := hbar hz
    refine mem_normalizer_fintype fun y hy => ?_
    rw [SetLike.mem_coe] at hy ⊢
    obtain ⟨y₀, hy₀, hy₀N, rfl⟩ := hbar hy
    have hxyN : x * y₀ * x⁻¹ ∈ normalizer (Y : Set G) :=
      mul_mem (mul_mem hxN hy₀N) (inv_mem hxN)
    have e : π (⟨x, hxN⟩ * ⟨y₀, hy₀N⟩ * ⟨x, hxN⟩⁻¹) = π ⟨x * y₀ * x⁻¹, hxyN⟩ := rfl
    rw [map_mul, map_mul, map_inv] at e
    rw [e]
    exact hmemb hxyN (hN x (hA hx) y₀ hy₀)
  have hb₁n : b₁ ≤ normalizer (b₂ : Set (Bar Y)) := hnormΓ hB₁P hB₂N' hB₂N
  have hb₂n : b₂ ≤ normalizer (b₁ : Set (Bar Y)) := hnormΓ hB₂P hB₁N' hB₁N
  have hξb₁ : ⁅b₂ ⊔ b₁, b₂ ⊔ b₁⁆ ≤ b₁ := commutator_sup_le_of_normalizes hb₂n hb₂ab
  have hξb₂ : ⁅b₂ ⊔ b₁, b₂ ⊔ b₁⁆ ≤ b₂ := by
    rw [sup_comm]; exact commutator_sup_le_of_normalizes hb₁n hb₁ab
  have hξφ : ⁅b₂ ⊔ b₁, b₂ ⊔ b₁⁆ ≤ bar Y F5 := by
    have h1 : b₂ ⊔ b₁ ≤ bar Y P := sup_le (bar_mono hB₂P) (bar_mono hB₁P)
    have h2 : ⁅bar Y P, bar Y P⁆ = bar Y ⁅P, P⁆ :=
      (Common.map_subgroupOf_commutator (proj Y) hPN' hPN').symm
    have h3 : bar Y ⁅P, P⁆ ≤ bar Y F5 := bar_mono (commutator_le.2 hPP)
    exact (commutator_mono h1 h1).trans (h2.le.trans h3)
  have hYpos : 0 < Nat.card Y := Nat.card_pos
  have hup : Nat.card (b₁ ⊓ bar Y F5 : Subgroup (Bar Y)) ≤ q ^ 2 := by
    have h1 : lift (b₁ ⊓ bar Y F5) = (B₁ ⊔ Y) ⊓ F5 := by
      rw [lift_inf, lift_bar_eq_sup hB₁N', lift_bar_eq_sup hFN', sup_eq_left.2 hYF]
    have h2 := card_lift (A := Y) (b₁ ⊓ bar Y F5)
    rw [h1] at h2
    rw [h2] at hX
    exact Nat.le_of_mul_le_mul_right hX hYpos
  have hSS : ⁅S, S⁆ ≤ normalizer (Y : Set G) := by
    rw [commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (hSN' ha) (hSN' hb)) (inv_mem (hSN' ha))) (inv_mem (hSN' hb))
  have hlow : q ^ 2 ≤ Nat.card (⁅sb, sb⁆ : Subgroup (Bar Y)) := by
    have e : ⁅sb, sb⁆ = bar Y ⁅S, S⁆ :=
      (Common.map_subgroupOf_commutator (proj Y) hSN' hSN').symm
    have h1 : lift (⁅sb, sb⁆) = ⁅S, S⁆ ⊔ Y := by
      rw [e, lift_bar_eq_sup hSS]
    have h2 := card_lift (A := Y) (⁅sb, sb⁆ : Subgroup (Bar Y))
    rw [h1] at h2
    rw [h2] at hS
    exact Nat.le_of_mul_le_mul_right hS hYpos
  have hSgc : ⁅b₂ ⊔ b₁, (b₂ ⊔ b₁)ᵍ[τ]⁆ = ⊥ := sup_conjg_commutator_eq_bot h11' h22' h12' h21'
  set δ : ↥(b₂ ⊔ b₁) →* Bar Y := Common.diagonalHom (b₂ ⊔ b₁) τ hSgc with hδ
  set ξ : Subgroup (Bar Y) := ⁅b₂ ⊔ b₁, b₂ ⊔ b₁⁆ with hξ
  have hξSg : ξ ≤ b₂ ⊔ b₁ := by
    rw [hξ, commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  set R : Subgroup (Bar Y) := (ξ.subgroupOf (b₂ ⊔ b₁)).map δ with hR
  have hsbR : ⁅sb, sb⁆ ≤ R := by
    rw [commutator_le]
    intro s hs s' hs'
    obtain ⟨w, hw, hws⟩ := commutator_fixed_eq_diag hτ h11' h22' h12' h21' hSτ hdecΓ hs hs'
    refine ⟨⟨w, hξSg hw⟩, mem_subgroupOf.2 hw, ?_⟩
    rw [hδ, Common.diagonalHom_apply_of_mul_self hSgc hτ, hws]
  have hRξ : Nat.card R ≤ Nat.card ξ := by
    have : Nat.card (ξ.subgroupOf (b₂ ⊔ b₁)) = Nat.card ξ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hξSg).toEquiv
    rw [← this]
    exact Nat.card_le_card_of_surjective _ (MonoidHom.subgroupMap_surjective δ _)
  have hlow' : q ^ 2 ≤ Nat.card ξ :=
    hlow.trans ((Subgroup.card_le_of_le hsbR).trans hRξ)
  have hξeq : ξ = b₁ ⊓ bar Y F5 :=
    Subgroup.eq_of_le_of_card_ge (le_inf hξb₁ hξφ) (hup.trans hlow')
  intro x hx
  obtain ⟨hxF, hxB⟩ := mem_inf.1 hx
  have hxN : x ∈ normalizer (Y : Set G) := hFN' hxF
  have h1 : π ⟨x, hxN⟩ ∈ b₁ ⊓ bar Y F5 := mem_inf.2 ⟨hmemb hxN hxB, hmemb hxN hxF⟩
  rw [← hξeq] at h1
  have h2 := hξb₂ h1
  have h3 := (proj_mem_bar_iff hB₂N' ⟨x, hxN⟩).1 h2
  rwa [sup_eq_left.2 hYB₂] at h3

end Alpha

end ProductLiftsAux

end Part2

section Part3

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc
  mem_centerMod_iff mem_centralizerMod_iff commutator_mem_iff_proj)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux
  (mem_sup_iff_of_le_normalizer mem_sup_iff_of_le_normalizer')

namespace ProductLiftsAux

section Generic

variable {G : Type*} [Group G]

theorem dedekind {A B P : Subgroup G} (hBP : B ≤ P) (hAB : A ≤ normalizer (B : Set G)) :
    P ⊓ (A ⊔ B) = (P ⊓ A) ⊔ B := by
  refine le_antisymm ?_ (sup_le (inf_le_inf_left P le_sup_left) (le_inf hBP le_sup_right))
  intro x hx
  obtain ⟨hxP, hxAB⟩ := mem_inf.1 hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hAB).1 hxAB
  have haP : a ∈ P := by
    have := mul_mem hxP (inv_mem (hBP hb))
    simpa using this
  exact mul_mem (mem_sup_left (mem_inf.2 ⟨haP, ha⟩)) (mem_sup_right hb)

theorem commutator_mul_mem {X : Subgroup G} {b b' m m' : G} (hb : b ∈ X) (hb' : b' ∈ X)
    (hm : m ∈ normalizer (X : Set G)) (hm' : m' ∈ normalizer (X : Set G))
    (hmm : m * m' * m⁻¹ * m'⁻¹ ∈ X) :
    (b * m) * (b' * m') * (b * m)⁻¹ * (b' * m')⁻¹ ∈ X := by
  open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient in
  have hbm : b * m ∈ normalizer (X : Set G) := mul_mem (le_normalizer hb) hm
  have hbm' : b' * m' ∈ normalizer (X : Set G) := mul_mem (le_normalizer hb') hm'
  have e1 : CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient.proj X ⟨b * m, hbm⟩ =
      CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient.proj X ⟨m, hm⟩ := by
    rw [CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient.proj_eq_proj_iff]
    have := (mem_normalizer_iff''.1 hm b⁻¹).1 (inv_mem hb)
    simpa [mul_assoc] using this
  have e2 : CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient.proj X ⟨b' * m', hbm'⟩ =
      CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient.proj X ⟨m', hm'⟩ := by
    rw [CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient.proj_eq_proj_iff]
    have := (mem_normalizer_iff''.1 hm' b'⁻¹).1 (inv_mem hb')
    simpa [mul_assoc] using this
  refine (commutator_mem_iff_proj hbm hbm').1 ?_
  rw [e1, e2]
  exact (commutator_mem_iff_proj hm hm').2 hmm

theorem split_center {U Y B B' D P : Subgroup G}
    (hD : ∀ x ∈ D, ∃ b ∈ B, ∃ b' ∈ B', x = b * b')
    (hUB' : U ≤ B') (hBB' : B ⊓ B' = U) (hBP : B ≤ P) (hB'P : B' ≤ P)
    (hBN : ∀ p ∈ P, ∀ x ∈ B, p * x * p⁻¹ ∈ B) (hB'N : ∀ p ∈ P, ∀ x ∈ B', p * x * p⁻¹ ∈ B')
    (hYD : Y ≤ D) (hDD : ∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ ∈ U)
    (hBD : B ≤ D) (hB'D : B' ≤ D)
    (hYc : ∀ y ∈ Y, ∀ p ∈ P, ⁅y, p⁆ ∈ U) (hYc' : ∀ x ∈ P, (∀ p ∈ P, ⁅x, p⁆ ∈ U) → x ∈ Y) :
    ∀ y ∈ Y, ∃ b ∈ B ⊓ Y, ∃ b' ∈ B' ⊓ Y, y = b * b' := by
  intro y hy
  obtain ⟨b, hb, b', hb', hyb⟩ := hD y (hYD hy)
  have hbY : b ∈ Y := by
    refine hYc' b (hBP hb) fun p hp => ?_
    have h1 := hYc y hy p hp
    set c' : G := ⁅b', p⁆ with hc'
    set c : G := ⁅b, p⁆ with hc
    have hc'B' : c' ∈ B' := by
      have : c' = b' * (p * b'⁻¹ * p⁻¹) := by
        rw [hc']; simp only [commutatorElement_def]; group
      rw [this]
      exact mul_mem hb' (hB'N p hp _ (inv_mem hb'))
    have hcB : c ∈ B := by
      have : c = b * (p * b⁻¹ * p⁻¹) := by
        rw [hc]; simp only [commutatorElement_def]; group
      rw [this]
      exact mul_mem hb (hBN p hp _ (inv_mem hb))
    have e : ⁅y, p⁆ = (⁅b, c'⁆ * c') * c := by
      rw [hyb, hc', hc]; simp only [commutatorElement_def]; group
    have h2 : ⁅b, c'⁆ ∈ U := hDD b (hBD hb) c' (hB'D hc'B')
    rw [e] at h1
    have h3 : c' * c ∈ U := by
      rw [mul_assoc] at h1
      have := mul_mem (inv_mem h2) h1
      rwa [inv_mul_cancel_left] at this
    have h4 : c ∈ B' := by
      have h5 : c = c'⁻¹ * (c' * c) := by group
      rw [h5]
      exact mul_mem (inv_mem hc'B') (hUB' h3)
    have h6 : c ∈ B ⊓ B' := mem_inf.2 ⟨hcB, h4⟩
    rwa [hBB'] at h6
  refine ⟨b, mem_inf.2 ⟨hb, hbY⟩, b', mem_inf.2 ⟨hb', ?_⟩, hyb⟩
  have : b' = b⁻¹ * y := by rw [hyb]; group
  rw [this]
  exact mul_mem (inv_mem hbY) hy

end Generic

end ProductLiftsAux

end Part3

section Part4

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc
  mem_centerMod_iff mem_centralizerMod_iff commutator_mem_iff_proj)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux
  (mem_sup_iff_of_le_normalizer mem_sup_iff_of_le_normalizer' Sl2Pair)
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_inf mem_normalizer_sup)

namespace ProductLiftsAux

section Generic2

variable {G : Type*} [Group G]

theorem inf_sup_le_of_split {U Y B B' P : Subgroup G}
    (hsplit : ∀ y ∈ Y, ∃ b ∈ B ⊓ Y, ∃ b' ∈ B' ⊓ Y, y = b * b')
    (hUY : U ≤ Y) (hBB' : B ⊓ B' = U) (hBP : B ≤ P) (hB'P : B' ≤ P)
    (hPY : P ≤ normalizer (Y : Set G)) (hB'N : ∀ p ∈ P, ∀ x ∈ B', p * x * p⁻¹ ∈ B') :
    (B ⊔ Y) ⊓ (B' ⊔ Y) ≤ Y := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
  obtain ⟨b, hb, y, hy, rfl⟩ := (mem_sup_iff_of_le_normalizer (hBP.trans hPY)).1 hx1
  obtain ⟨b', hb', y', hy', hxe⟩ := (mem_sup_iff_of_le_normalizer (hB'P.trans hPY)).1 hx2
  have hby : b = b' * (y' * y⁻¹) := by
    calc b = (b * y) * y⁻¹ := by group
      _ = (b' * y') * y⁻¹ := by rw [hxe]
      _ = b' * (y' * y⁻¹) := by group
  obtain ⟨c, hc, c', hc', hcc⟩ := hsplit (y' * y⁻¹) (mul_mem hy' (inv_mem hy))
  obtain ⟨hcB, hcY⟩ := mem_inf.1 hc
  obtain ⟨hc'B', hc'Y⟩ := mem_inf.1 hc'
  have hbcc : b = c * (((c⁻¹ * b' * c) * c')) := by
    rw [hby, hcc]; group
  have he' : (c⁻¹ * b' * c) * c' ∈ B' := by
    have h1 : c⁻¹ * b' * c⁻¹⁻¹ ∈ B' := hB'N c⁻¹ (inv_mem (hBP hcB)) b' hb'
    rw [inv_inv] at h1
    exact mul_mem h1 hc'B'
  have he : (c⁻¹ * b' * c) * c' ∈ B := by
    have : (c⁻¹ * b' * c) * c' = c⁻¹ * b := by rw [hbcc]; group
    rw [this]
    exact mul_mem (inv_mem hcB) hb
  have heU : (c⁻¹ * b' * c) * c' ∈ U := by
    have : (c⁻¹ * b' * c) * c' ∈ B ⊓ B' := mem_inf.2 ⟨he, he'⟩
    rwa [hBB'] at this
  have hbY : b ∈ Y := by
    rw [hbcc]
    exact mul_mem hcY (hUY heU)
  exact mul_mem hbY hy

theorem inf_le_sup_of_prod {P M B B' Λ Λ' : Subgroup G}
    (hP : ∀ p ∈ P, ∃ m ∈ M, ∃ b ∈ B, ∃ b' ∈ B', p = m * b * b')
    (hBΛ : B ≤ Λ) (hB'Λ' : B' ≤ Λ') (hΛ : Λ ⊓ Λ' = M) (hMΛ : M ≤ Λ) : P ⊓ Λ ≤ B ⊔ M := by
  intro x hx
  obtain ⟨hxP, hxΛ⟩ := mem_inf.1 hx
  obtain ⟨m, hm, b, hb, b', hb', rfl⟩ := hP x hxP
  have hb'M : b' ∈ M := by
    have h1 : b' ∈ Λ := by
      have := mul_mem (inv_mem (mul_mem (hMΛ hm) (hBΛ hb))) hxΛ
      simpa [mul_assoc] using this
    rw [← hΛ]
    exact mem_inf.2 ⟨h1, hB'Λ' hb'⟩
  exact mul_mem (mul_mem (mem_sup_right hm) (mem_sup_left hb)) (mem_sup_right hb'M)

theorem prod_decomp {P M D W Z₁ Z₂ B₂ B₂' B₁ B₁' : Subgroup G}
    (hPMD : ∀ p ∈ P, ∃ m ∈ M, ∃ d ∈ D, p = m * d)
    (hM : ∀ m ∈ M, ∃ z₁ ∈ Z₁, ∃ z₂ ∈ Z₂, m = z₁ * z₂)
    (hZ₁ : ∀ z ∈ Z₁, ∃ b ∈ B₂, ∃ w ∈ W, z = b * w)
    (hZ₂ : ∀ z ∈ Z₂, ∃ b ∈ B₂', ∃ w ∈ W, z = b * w)
    (hD : ∀ x ∈ D, ∃ b ∈ B₁, ∃ b' ∈ B₁', x = b * b')
    (hWD : W ≤ D) (hB₂'P : B₂' ≤ P) (hDN : ∀ p ∈ P, ∀ x ∈ D, p * x * p⁻¹ ∈ D) :
    ∀ p ∈ P, ∃ b₂ ∈ B₂, ∃ b₂' ∈ B₂', ∃ b₁ ∈ B₁, ∃ b₁' ∈ B₁', p = b₂ * b₂' * b₁ * b₁' := by
  intro p hp
  obtain ⟨m, hm, d, hd, rfl⟩ := hPMD p hp
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := hM m hm
  obtain ⟨b, hb, w, hw, rfl⟩ := hZ₁ z₁ hz₁
  obtain ⟨b', hb', w', hw', rfl⟩ := hZ₂ z₂ hz₂
  have h1 : b'⁻¹ * w * b'⁻¹⁻¹ ∈ D := hDN b'⁻¹ (inv_mem (hB₂'P hb')) w (hWD hw)
  rw [inv_inv] at h1
  have hδ : (b'⁻¹ * w * b') * w' * d ∈ D := mul_mem (mul_mem h1 (hWD hw')) hd
  obtain ⟨b₁, hb₁, b₁', hb₁', hδe⟩ := hD _ hδ
  refine ⟨b, hb, b', hb', b₁, hb₁, b₁', hb₁', ?_⟩
  calc b * w * (b' * w') * d = b * b' * ((b'⁻¹ * w * b') * w' * d) := by group
    _ = b * b' * (b₁ * b₁') := by rw [hδe]
    _ = b * b' * b₁ * b₁' := by group

theorem commutator_sup_le_sup {B M Y : Subgroup G} (hBM : B ≤ normalizer (M : Set G))
    (hMB : M ≤ normalizer (B : Set G)) (hMY : M ≤ normalizer (Y : Set G))
    (hMM : ⁅M, M⁆ ≤ Y) : ⁅B ⊔ M, B ⊔ M⁆ ≤ B ⊔ Y := by
  rw [commutator_le]
  intro x hx x' hx'
  obtain ⟨b, hb, m, hm, rfl⟩ := (mem_sup_iff_of_le_normalizer hBM).1 hx
  obtain ⟨b', hb', m', hm', rfl⟩ := (mem_sup_iff_of_le_normalizer hBM).1 hx'
  have hmN : ∀ g ∈ M, g ∈ normalizer ((B ⊔ Y : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_sup (hMB hg) (hMY hg)
  have hmm : m * m' * m⁻¹ * m'⁻¹ ∈ B ⊔ Y := by
    have := hMM (Subgroup.commutator_mem_commutator hm hm')
    exact mem_sup_right (by simpa [commutatorElement_def] using this)
  rw [commutatorElement_def]
  exact commutator_mul_mem (mem_sup_left hb) (mem_sup_left hb') (hmN m hm) (hmN m' hm') hmm

end Generic2

section Generic3

variable {G : Type} [Group G]

@[expose] def commSubgroup (U : Subgroup G) (z : G) : Subgroup G where
  carrier := {c | c ∈ normalizer (U : Set G) ∧ z * c * z⁻¹ * c⁻¹ ∈ U}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have e : z * (a * b) * z⁻¹ * (a * b)⁻¹ =
        (z * a * z⁻¹ * a⁻¹) * (a * (z * b * z⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e]
    exact mul_mem ha' ((mem_normalizer_iff.1 ha _).1 hb')
  one_mem' := ⟨one_mem _, by simpa using one_mem U⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have e : z * a⁻¹ * z⁻¹ * a⁻¹⁻¹ = a⁻¹ * (z * a * z⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 (inv_mem ha) _).1 (inv_mem ha')

theorem mem_commSubgroup_iff {U : Subgroup G} {z g : G} :
    g ∈ commSubgroup U z ↔ g ∈ normalizer (U : Set G) ∧ z * g * z⁻¹ * g⁻¹ ∈ U := Iff.rfl

theorem inf_le_center {Kp Kp' W Y N : Subgroup G} (hsup : N = Kp ⊔ Kp' ⊔ W) (hYN : Y ≤ N)
    (hNY : N ≤ normalizer (Y : Set G)) (hc : ⁅Kp, Kp'⁆ ≤ Y) (hcen : centerMod Y N = W) :
    Kp ⊓ Kp' ≤ W := by
  intro e he
  obtain ⟨heK, heK'⟩ := mem_inf.1 he
  have hKpN : Kp ≤ N := by rw [hsup]; exact le_sup_left.trans le_sup_left
  have hKp'N : Kp' ≤ N := by rw [hsup]; exact le_sup_right.trans le_sup_left
  have hWN : W ≤ N := by rw [hsup]; exact le_sup_right
  have hinv : ∀ g : G, g * e * g⁻¹ * e⁻¹ ∈ Y → e * g * e⁻¹ * g⁻¹ ∈ Y := fun g h => by
    have h2 := inv_mem h
    have e2 : (g * e * g⁻¹ * e⁻¹)⁻¹ = e * g * e⁻¹ * g⁻¹ := by group
    rwa [e2] at h2
  have hK1 : Kp ≤ commSubgroup Y e := fun g hg => by
    refine mem_commSubgroup_iff.2 ⟨hNY (hKpN hg), hinv g ?_⟩
    have := hc (Subgroup.commutator_mem_commutator hg heK')
    rwa [commutatorElement_def] at this
  have hK2 : Kp' ≤ commSubgroup Y e := fun g hg => by
    refine mem_commSubgroup_iff.2 ⟨hNY (hKp'N hg), ?_⟩
    have := hc (Subgroup.commutator_mem_commutator heK hg)
    rwa [commutatorElement_def] at this
  have hW : W ≤ commSubgroup Y e := fun g hg => by
    refine mem_commSubgroup_iff.2 ⟨hNY (hWN hg), hinv g ?_⟩
    have hg' : g ∈ centerMod Y N := by rw [hcen]; exact hg
    exact ((ProductN1Aux.mem_centerMod_iff_of_le hYN hNY).1 hg').2 e (hKpN heK)
  have hNe : N ≤ commSubgroup Y e := by
    rw [hsup]; exact sup_le (sup_le hK1 hK2) hW
  rw [← hcen]
  exact (ProductN1Aux.mem_centerMod_iff_of_le hYN hNY).2
    ⟨hKpN heK, fun a ha => (mem_commSubgroup_iff.1 (hNe ha)).2⟩

end Generic3

end ProductLiftsAux

end Part4

section Part5

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc
  mem_centerMod_iff mem_centralizerMod_iff commutator_mem_iff_proj)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux
  (mem_sup_iff_of_le_normalizer mem_sup_iff_of_le_normalizer' Sl2Pair mem_normalizer_of_pow_mem
    le_normalizer_of_commutator_mem)
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_inf mem_normalizer_sup)

namespace ProductLiftsAux

section Generic4

variable {G : Type*} [Group G]

theorem inf_le_Y [Finite G] {t : G} (ht : t * t = 1) {Kp B Y W P : Subgroup G}
    (hE : Kp ⊓ Kpᵍ[t] ≤ W) (hWP : W ≤ P) (hQ : IsSylowOf 2 (P ⊓ Kp) Kp) (hYK : Y ≤ Kp)
    (hKY : Kp ≤ normalizer (Y : Set G)) (hperf : Kp ≤ ⁅Kp, Kp⁆ ⊔ Y)
    (hc : ⁅Kp, Kpᵍ[t]⁆ ≤ Y) (hQc : ⁅P ⊓ Kp, P ⊓ Kp⁆ ≤ B ⊔ Y) (hYt : Yᵍ[t] = Y)
    (hsplit : (B ⊔ Y) ⊓ (Bᵍ[t] ⊔ Y) ≤ Y) : Kp ⊓ Kpᵍ[t] ≤ Y := by
  have key : ∀ e ∈ Kp ⊓ Kpᵍ[t], e ∈ B ⊔ Y := by
    intro e he
    obtain ⟨heK, heK'⟩ := mem_inf.1 he
    have hePKp : e ∈ P ⊓ Kp := mem_inf.2 ⟨hWP (hE he), heK⟩
    have hcen : ∀ g ∈ Kp, ⁅e, g⁆ ∈ Y := by
      intro g hg
      have h1 := hc (Subgroup.commutator_mem_commutator hg heK')
      have h2 := inv_mem h1
      rw [commutatorElement_inv] at h2
      exact h2
    have h1 := mem_commutator_sup_of_central_section hYK hKY hperf hQ hePKp hcen
    exact (sup_le hQc le_sup_right) h1
  intro e he
  have he1 := key e he
  have het : t * e * t ∈ Kp ⊓ Kpᵍ[t] := by
    obtain ⟨heK, heK'⟩ := mem_inf.1 he
    exact mem_inf.2 ⟨(mem_conjg_iff_of_invol ht).1 heK', conj_mem_conjg_of_invol ht heK⟩
  have he2 : e ∈ (B ⊔ Y)ᵍ[t] := (mem_conjg_iff_of_invol ht).2 (key _ het)
  rw [Subgroup.map_sup, hYt] at he2
  exact hsplit (mem_inf.2 ⟨he1, he2⟩)

theorem levi_decomp {N M Λ Cen : Subgroup G} (hΛN : Λ ≤ N) (hMΛ : M ≤ Λ)
    (hCenM : Cen ≤ normalizer (M : Set G)) (hcompl : N = Cen ⊔ M) :
    ∀ x ∈ Λ, ∃ a ∈ Λ ⊓ Cen, ∃ m ∈ M, x = a * m := by
  intro x hx
  obtain ⟨a, ha, m, hm, rfl⟩ := (mem_sup_iff_of_le_normalizer hCenM).1 (hcompl ▸ hΛN hx)
  refine ⟨a, mem_inf.2 ⟨?_, ha⟩, m, hm, rfl⟩
  have := mul_mem hx (inv_mem (hMΛ hm))
  simpa using this

theorem le_normalizer_of_sup {N Kp Kp' W Y : Subgroup G} (hsup : N = Kp ⊔ Kp' ⊔ W)
    (hc : ⁅Kp, Kp'⁆ ≤ Y) (hYK : Y ≤ Kp) (hW : W ≤ normalizer (Kp : Set G)) :
    N ≤ normalizer (Kp : Set G) := by
  rw [hsup]
  refine sup_le (sup_le Subgroup.le_normalizer ?_) hW
  refine le_normalizer_of_commutator_mem fun x hx y hy => ?_
  have h1 := Subgroup.commutator_mem_commutator hx hy
  rw [Subgroup.commutator_comm] at h1
  exact hYK (hc h1)

theorem fixed_le_sup [Finite G] {X Z S T Y : Subgroup G} (hXZ : X ≤ normalizer (Z : Set G))
    (hSX : S ≤ normalizer (X : Set G)) (hSZ : S ≤ normalizer (Z : Set G))
    (hX2 : IsPGroup 2 X) (hSodd : Odd (Nat.card S)) (hCZ : Z ⊓ centralizer (S : Set G) ≤ Y)
    (hT : T ≤ X ⊔ Z) (hTS : T ≤ centralizer (S : Set G)) : T ≤ X ⊔ Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsolv : Group.IsSolvable X := by
    haveI : Group.IsNilpotent X := hX2.isNilpotent
    infer_instance
  have hcop : (Nat.card S).Coprime (Nat.card X) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := X)).1 hX2
    rw [hn]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hSodd)
  intro x hx
  obtain ⟨b, hb, m, hm, rfl⟩ := (mem_sup_iff_of_le_normalizer hXZ).1 (hT hx)
  refine fixed_mul_mem_of_coprime hXZ hSX hSZ hsolv hcop hCZ hb hm fun s hs => ?_
  have := mem_centralizer_iff.1 (hTS hx) s hs
  rw [this]
  group

theorem fixed_le [Finite G] {X Z S T : Subgroup G} (hXZ : X ≤ normalizer (Z : Set G))
    (hSX : S ≤ normalizer (X : Set G)) (hSZ : S ≤ normalizer (Z : Set G))
    (hX2 : IsPGroup 2 X) (hSodd : Odd (Nat.card S)) (hCZ : Z ⊓ centralizer (S : Set G) = ⊥)
    (hT : T ≤ X ⊔ Z) (hTS : T ≤ centralizer (S : Set G)) : T ≤ X := by
  simpa using fixed_le_sup (Y := ⊥) hXZ hSX hSZ hX2 hSodd hCZ.le hT hTS

end Generic4

section Generic5

variable {G : Type} [Group G]

theorem le_normalizer_of_odd_card {F : Type} [Field F] [Finite F] [Finite G]
    {N D K K' J : Subgroup G} (hS : Sl2Pair F N D K K') (hJN : J ≤ normalizer (N : Set G))
    (hJD : J ≤ normalizer (D : Set G)) (hodd : Odd (Nat.card J)) : J ≤ normalizer (K : Set G) :=
  fun g hg => by
  refine mem_normalizer_of_pow_mem hS.ne (Sl2Pair.conj_factor hS (hJN hg) (hJD hg))
    (Sl2Pair.conj_factor hS.symm (hJN hg) (hJD hg)).symm hodd ?_
  have h1 : (⟨g, hg⟩ : J) ^ Nat.card J = 1 := pow_card_eq_one'
  have h2 : g ^ Nat.card J = 1 := by
    have := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  rw [h2]
  exact one_mem _

theorem card_inf_sylow {F : Type} [Field F] [Finite F] [Finite G] {N D K K' P : Subgroup G}
    (hS : Sl2Pair F N D K K') (hP : IsSylowOf 2 P N) (hDP : D ≤ P) :
    Nat.card (P ⊓ K : Subgroup G) = Nat.card D * Nat.card F := by
  have hDK : D ≤ K := by
    rw [← hS.inf_eq]; exact inf_le_left
  have h1 := hS.relIndex_sylow hP hDP
  have h2 := Subgroup.relIndex_mul_card D (P ⊓ K)
  rw [inf_eq_left.2 (le_inf hDP hDK), h1] at h2
  rw [← h2, mul_comm]

end Generic5

end ProductLiftsAux

end Part5

section Part6

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc
  mem_centerMod_iff mem_centralizerMod_iff commutator_mem_iff_proj)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux
  (mem_sup_iff_of_le_normalizer mem_sup_iff_of_le_normalizer' Sl2Pair mem_normalizer_of_pow_mem
    le_normalizer_of_commutator_mem conj_inf conj_sup conj_commutator conj_conj_of_mul_self
    conj_eq_of_mem_normalizer card_conj pCoreOf_conj mem_normalizer_of_conj_eq
    mem_normalizer_pCoreOf)
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_inf mem_normalizer_sup)

namespace ProductLiftsAux

structure Cfg {G : Type} [Group G] [Finite G] (K : Type) [Field K] [Finite K] [CharP K 2]
    (t : G) (U Y W F M D P N₁ N₂ Λ₁ Λ₂ J₃ J₄ J S Ast : Subgroup G) : Prop where
  t_sq : t * t = 1
  K_four : 4 ≤ Nat.card K
  U_le_Y : U ≤ Y
  Y_le_W : Y ≤ W
  W_le_F : W ≤ F
  F_le_M : F ≤ M
  F_le_D : F ≤ D
  M_le_P : M ≤ P
  D_le_P : D ≤ P
  M_inf_D : M ⊓ D = F
  P_mul : ∀ p ∈ P, ∃ m ∈ M, ∃ d ∈ D, p = m * d
  P_comm : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ F
  M_comm : ⁅M, M⁆ = Y
  D_comm : ⁅D, D⁆ = U
  P_center : centerMod U P = Y
  card_U : Nat.card U = Nat.card K ^ 2
  card_Y : Nat.card Y = Nat.card K ^ 4
  card_W : Nat.card W = Nat.card K ^ 6
  card_F : Nat.card F = Nat.card K ^ 8
  card_M : Nat.card M = Nat.card K ^ 10
  card_D : Nat.card D = Nat.card K ^ 10
  card_P : Nat.card P = Nat.card K ^ 12
  P_norm_M : P ≤ normalizer (M : Set G)
  P_norm_D : P ≤ normalizer (D : Set G)
  N₁_norm_D : N₁ ≤ normalizer (D : Set G)
  N₂_norm_M : N₂ ≤ normalizer (M : Set G)
  N₂_norm_W : N₂ ≤ normalizer (W : Set G)
  t_norm_M : t ∈ normalizer (M : Set G)
  t_norm_D : t ∈ normalizer (D : Set G)
  t_norm_W : t ∈ normalizer (W : Set G)
  t_norm_P : t ∈ normalizer (P : Set G)
  sylow₁ : IsSylowOf 2 P N₁
  sylow₂ : IsSylowOf 2 P N₂
  fac₁ : IsFactor D N₁ Λ₁ t K
  fac₂ : IsFactor M N₂ Λ₂ t K
  label : (P ⊓ Λ₁)ᵍ[t] = centerMod Y (P ⊓ Λ₂) ⊔ D
  compl₁ : N₁ = (N₁ ⊓ centralizer (J₃ : Set G)) ⊔ D
  compl₁' : (N₁ ⊓ centralizer (J₃ : Set G)) ⊓ D = ⊥
  Ast_le : Ast ≤ N₂ ⊓ centralizer (J₄ : Set G)
  compl₂ : N₂ = Ast ⊔ M
  compl₂' : Ast ⊓ M = ⊥
  cen_inf : (N₂ ⊓ centralizer (J₄ : Set G)) ⊓ M ≤ Y
  J_odd : Odd (Nat.card J)
  J₃_le : J₃ ≤ J
  J₄_le : J₄ ≤ J
  J_norm_N₁ : J ≤ normalizer (N₁ : Set G)
  J_norm_N₂ : J ≤ normalizer (N₂ : Set G)
  J_norm_D : J ≤ normalizer (D : Set G)
  J_norm_M : J ≤ normalizer (M : Set G)
  rel_center : W.relIndex (centerMod W Λ₂) = Nat.card K ^ 2
  center_sup : centerMod W Λ₂ ⊔ centerMod W (Λ₂ᵍ[t]) = M
  hat_sup : (⁅Λ₂, Λ₂⁆ ⊔ W) ⊔ (⁅Λ₂, Λ₂⁆ ⊔ W)ᵍ[t] = N₂
  hat_levi : ⁅Λ₂, Λ₂⁆ ⊔ W = (Λ₂ ⊓ Ast) ⊔ centerMod W (Λ₂ᵍ[t])
  center_pcore : centerMod W (Λ₂ᵍ[t]) = pCoreOf 2 (⁅Λ₂, Λ₂⁆ ⊔ W)
  center_P₂ : centerMod W (P ⊓ Λ₂) = F ⊔ centerMod W Λ₂
  center_P₂' : centerMod Y (P ⊓ Λ₂) = centerMod W (P ⊓ Λ₂)
  Kp_perfect : ⁅⁅Λ₂, Λ₂⁆ ⊔ Y, ⁅Λ₂, Λ₂⁆ ⊔ Y⁆ ⊔ Y = ⁅Λ₂, Λ₂⁆ ⊔ Y
  Kp_comm : ⁅⁅Λ₂, Λ₂⁆ ⊔ Y, (⁅Λ₂, Λ₂⁆ ⊔ Y)ᵍ[t]⁆ ≤ Y
  Zt_pcore : centerMod U (Λ₁ᵍ[t]) = pCoreOf 2 (⁅Λ₁, Λ₁⁆ ⊔ U)
  Z_sup : centerMod U Λ₁ ⊔ centerMod U (Λ₁ᵍ[t]) = D
  Z_inf : centerMod U Λ₁ ⊓ centerMod U (Λ₁ᵍ[t]) = U
  center_N₂_Y : centerMod Y N₂ = W
  center_N₂_W : centerMod W N₂ = W
  S_le_P : S ≤ P
  S_fix : ∀ s ∈ S, t * s * t = s
  S_card : Nat.card K ^ 2 * Nat.card Y ≤ Nat.card (⁅S, S⁆ ⊔ Y : Subgroup G)

end ProductLiftsAux

end Part6

section Part7

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc
  mem_centerMod_iff mem_centralizerMod_iff commutator_mem_iff_proj)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux
  (mem_sup_iff_of_le_normalizer mem_sup_iff_of_le_normalizer' Sl2Pair mem_normalizer_of_pow_mem
    le_normalizer_of_commutator_mem conj_inf conj_sup conj_commutator conj_conj_of_mul_self
    conj_eq_of_mem_normalizer card_conj pCoreOf_conj mem_normalizer_of_conj_eq
    mem_normalizer_pCoreOf)
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_inf mem_normalizer_sup)

namespace ProductLiftsAux

namespace Cfg

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
  {t : G} {U Y W F M D P N₁ N₂ Λ₁ Λ₂ J₃ J₄ J S Ast : Subgroup G}
  (c : Cfg K t U Y W F M D P N₁ N₂ Λ₁ Λ₂ J₃ J₄ J S Ast)

include c

theorem U_le_D : U ≤ D := c.U_le_Y.trans (c.Y_le_W.trans (c.W_le_F.trans c.F_le_D))

theorem Y_le_M : Y ≤ M := c.Y_le_W.trans (c.W_le_F.trans c.F_le_M)

theorem W_le_M : W ≤ M := c.W_le_F.trans c.F_le_M

theorem W_le_D : W ≤ D := c.W_le_F.trans c.F_le_D

theorem P_two : IsPGroup 2 P := c.sylow₂.isPGroup

theorem P_le_N₁ : P ≤ N₁ := c.sylow₁.le

theorem P_le_N₂ : P ≤ N₂ := c.sylow₂.le

theorem t_norm_U : t ∈ normalizer (U : Set G) := by
  have := mem_normalizer_commutator_self c.t_norm_D
  rwa [c.D_comm] at this

theorem t_norm_Y : t ∈ normalizer (Y : Set G) := by
  have := mem_normalizer_commutator_self c.t_norm_M
  rwa [c.M_comm] at this

theorem t_norm_F : t ∈ normalizer (F : Set G) := by
  rw [← c.M_inf_D]
  exact mem_normalizer_inf c.t_norm_M c.t_norm_D

theorem conj_M : Mᵍ[t] = M := conj_eq_of_mem_normalizer c.t_norm_M

theorem conj_D : Dᵍ[t] = D := conj_eq_of_mem_normalizer c.t_norm_D

theorem conj_U : Uᵍ[t] = U := conj_eq_of_mem_normalizer c.t_norm_U

theorem conj_Y : Yᵍ[t] = Y := conj_eq_of_mem_normalizer c.t_norm_Y

theorem conj_W : Wᵍ[t] = W := conj_eq_of_mem_normalizer c.t_norm_W

theorem conj_F : Fᵍ[t] = F := conj_eq_of_mem_normalizer c.t_norm_F

theorem P_norm_U : P ≤ normalizer (U : Set G) := fun g hg => by
  have := mem_normalizer_commutator_self (c.P_norm_D hg)
  rwa [c.D_comm] at this

theorem P_norm_Y : P ≤ normalizer (Y : Set G) := fun g hg => by
  have := mem_normalizer_commutator_self (c.P_norm_M hg)
  rwa [c.M_comm] at this

theorem N₂_norm_Y : N₂ ≤ normalizer (Y : Set G) := fun g hg => by
  have := mem_normalizer_commutator_self (c.N₂_norm_M hg)
  rwa [c.M_comm] at this

theorem conj_conj (X : Subgroup G) : (Xᵍ[t])ᵍ[t] = X := conj_conj_of_mul_self c.t_sq X

theorem sl₁ : Sl2Pair K N₁ D Λ₁ (Λ₁ᵍ[t]) :=
  ProductN1Aux.isFactor_sl2Pair c.fac₁ c.t_sq c.K_four

theorem sl₂ : Sl2Pair K N₂ M Λ₂ (Λ₂ᵍ[t]) :=
  ProductN1Aux.isFactor_sl2Pair c.fac₂ c.t_sq c.K_four

theorem D_le_Λ₁ : D ≤ Λ₁ := c.fac₁.X_le

theorem D_le_Λ₁t : D ≤ Λ₁ᵍ[t] := by
  rw [← c.fac₁.inf]; exact inf_le_right

theorem M_le_Λ₂ : M ≤ Λ₂ := c.fac₂.X_le

theorem M_le_Λ₂t : M ≤ Λ₂ᵍ[t] := by
  rw [← c.fac₂.inf]; exact inf_le_right

theorem Λ₁_le_N₁ : Λ₁ ≤ N₁ := c.fac₁.le

theorem Λ₂_le_N₂ : Λ₂ ≤ N₂ := c.fac₂.le

theorem Λ₂t_le_N₂ : Λ₂ᵍ[t] ≤ N₂ := by rw [← c.fac₂.sup]; exact le_sup_right

theorem N₁_norm_Λ₁ : N₁ ≤ normalizer (Λ₁ : Set G) := c.sl₁.le_normalizer

theorem N₁_norm_Λ₁t : N₁ ≤ normalizer ((Λ₁ᵍ[t] : Subgroup G) : Set G) :=
  c.sl₁.symm.le_normalizer

theorem N₂_norm_Λ₂ : N₂ ≤ normalizer (Λ₂ : Set G) := c.sl₂.le_normalizer

theorem N₂_norm_Λ₂t : N₂ ≤ normalizer ((Λ₂ᵍ[t] : Subgroup G) : Set G) :=
  c.sl₂.symm.le_normalizer

end Cfg

end ProductLiftsAux

end Part7

section Part8

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc
  mem_centerMod_iff mem_centralizerMod_iff commutator_mem_iff_proj)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux
  (mem_sup_iff_of_le_normalizer mem_sup_iff_of_le_normalizer' Sl2Pair mem_normalizer_of_pow_mem
    le_normalizer_of_commutator_mem conj_inf conj_sup conj_commutator conj_conj_of_mul_self
    conj_eq_of_mem_normalizer card_conj pCoreOf_conj mem_normalizer_of_conj_eq
    mem_normalizer_pCoreOf)
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_inf mem_normalizer_sup)

namespace ProductLiftsAux

namespace Cfg

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
  {t : G} {U Y W F M D P N₁ N₂ Λ₁ Λ₂ J₃ J₄ J S Ast : Subgroup G}
  (c : Cfg K t U Y W F M D P N₁ N₂ Λ₁ Λ₂ J₃ J₄ J S Ast)

include c

theorem U_le_Kp₁ : U ≤ ⁅Λ₁, Λ₁⁆ := by
  rw [← c.D_comm]; exact commutator_mono c.D_le_Λ₁ c.D_le_Λ₁

theorem B₁_eq {B₁ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G)) :
    B₁ = centerMod U (Λ₁ᵍ[t]) := by
  rw [hB₁, c.Zt_pcore, sup_eq_left.2 c.U_le_Kp₁]

theorem B₁t_eq {B₁ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G)) :
    B₁ᵍ[t] = centerMod U Λ₁ := by
  have h := ProductN1Aux.centerMod_conj (U := U) (A := Λ₁ᵍ[t]) c.t_norm_U
    (c.U_le_D.trans c.D_le_Λ₁t)
  rw [c.conj_conj] at h
  rw [c.B₁_eq hB₁, ← h]

theorem B₁_sup {B₁ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G)) :
    B₁ ⊔ B₁ᵍ[t] = D := by
  rw [c.B₁t_eq hB₁, c.B₁_eq hB₁, sup_comm]; exact c.Z_sup

theorem B₁_inf {B₁ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G)) :
    B₁ ⊓ B₁ᵍ[t] = U := by
  rw [c.B₁t_eq hB₁, c.B₁_eq hB₁, inf_comm]; exact c.Z_inf

theorem U_le_B₁ {B₁ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G)) : U ≤ B₁ := by
  rw [← c.B₁_inf hB₁]; exact inf_le_left

theorem U_le_B₁t {B₁ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G)) :
    U ≤ B₁ᵍ[t] := by
  rw [← c.B₁_inf hB₁]; exact inf_le_right

theorem B₁_le_D {B₁ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G)) : B₁ ≤ D := by
  rw [← c.B₁_sup hB₁]; exact le_sup_left

theorem B₁t_le_D {B₁ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G)) :
    B₁ᵍ[t] ≤ D := by
  rw [← c.B₁_sup hB₁]; exact le_sup_right

theorem P_norm_B₁ {B₁ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G)) :
    P ≤ normalizer (B₁ : Set G) := fun g hg => by
  rw [c.B₁_eq hB₁]
  exact ProductN1Aux.mem_normalizer_centerMod (c.P_norm_U hg) (c.N₁_norm_Λ₁t (c.P_le_N₁ hg))
    (c.U_le_D.trans c.D_le_Λ₁t)

theorem P_norm_B₁t {B₁ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G)) :
    P ≤ normalizer ((B₁ᵍ[t] : Subgroup G) : Set G) := fun g hg => by
  rw [c.B₁t_eq hB₁]
  exact ProductN1Aux.mem_normalizer_centerMod (c.P_norm_U hg) (c.N₁_norm_Λ₁ (c.P_le_N₁ hg))
    (c.U_le_D.trans c.D_le_Λ₁)

theorem B₁_le_P {B₁ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G)) : B₁ ≤ P :=
  (c.B₁_le_D hB₁).trans c.D_le_P

theorem B₁t_le_P {B₁ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G)) :
    B₁ᵍ[t] ≤ P :=
  (c.B₁t_le_D hB₁).trans c.D_le_P

theorem B₁_conj {B₁ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G)) :
    ∀ p ∈ P, ∀ x ∈ B₁, p * x * p⁻¹ ∈ B₁ := fun p hp x hx =>
  (mem_normalizer_iff.1 (c.P_norm_B₁ hB₁ hp) x).1 hx

theorem B₁t_conj {B₁ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G)) :
    ∀ p ∈ P, ∀ x ∈ B₁ᵍ[t], p * x * p⁻¹ ∈ B₁ᵍ[t] := fun p hp x hx =>
  (mem_normalizer_iff.1 (c.P_norm_B₁t hB₁ hp) x).1 hx

theorem D_mul {B₁ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G)) :
    ∀ x ∈ D, ∃ b ∈ B₁, ∃ b' ∈ B₁ᵍ[t], x = b * b' := fun x hx => by
  have hx' : x ∈ B₁ ⊔ B₁ᵍ[t] := by rw [c.B₁_sup hB₁]; exact hx
  obtain ⟨b, hb, b', hb', rfl⟩ :=
    (mem_sup_iff_of_le_normalizer ((c.B₁_le_P hB₁).trans (c.P_norm_B₁t hB₁))).1 hx'
  exact ⟨b, hb, b', hb', rfl⟩

theorem card_B₁ {B₁ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G)) :
    Nat.card B₁ = Nat.card K ^ 6 := by
  have h1 := CFSG.LocalAnalysis.EvenBN.TrialityD4.card_sup_mul_card_inf_eq_D4 (A := B₁)
    (B := B₁ᵍ[t]) ((c.B₁t_le_P hB₁).trans (c.P_norm_B₁ hB₁))
  rw [c.B₁_sup hB₁, c.B₁_inf hB₁, card_conj, c.card_D, c.card_U] at h1
  have h2 : Nat.card B₁ * Nat.card B₁ = Nat.card K ^ 6 * Nat.card K ^ 6 := by
    rw [← h1]; ring
  exact Nat.mul_self_inj.1 h2

end Cfg

end ProductLiftsAux

end Part8

section Part9

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc
  mem_centerMod_iff mem_centralizerMod_iff commutator_mem_iff_proj)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux
  (mem_sup_iff_of_le_normalizer mem_sup_iff_of_le_normalizer' Sl2Pair mem_normalizer_of_pow_mem
    le_normalizer_of_commutator_mem conj_inf conj_sup conj_commutator conj_conj_of_mul_self
    conj_eq_of_mem_normalizer card_conj pCoreOf_conj mem_normalizer_of_conj_eq
    mem_normalizer_pCoreOf conj_mono mem_conj_iff)
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_inf mem_normalizer_sup)

namespace ProductLiftsAux

section Gen

variable {G : Type*} [Group G] [Finite G]

theorem conj_normalizer_le {A B : Subgroup G} {g : G} (h : A ≤ normalizer (B : Set G)) :
    Aᵍ[g] ≤ normalizer ((Bᵍ[g] : Subgroup G) : Set G) := by
  intro x hx
  refine mem_normalizer_fintype fun n hn => ?_
  rw [SetLike.mem_coe, mem_conj_iff] at hn ⊢
  rw [mem_conj_iff] at hx
  have e : g * (x * n * x⁻¹) * g⁻¹ = (g * x * g⁻¹) * (g * n * g⁻¹) * (g * x * g⁻¹)⁻¹ := by group
  rw [e]
  exact (mem_normalizer_iff.1 (h hx) _).1 hn

end Gen

namespace Cfg

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
  {t : G} {U Y W F M D P N₁ N₂ Λ₁ Λ₂ J₃ J₄ J S Ast : Subgroup G}
  (c : Cfg K t U Y W F M D P N₁ N₂ Λ₁ Λ₂ J₃ J₄ J S Ast)

include c

theorem M_two : IsPGroup 2 M := c.P_two.to_le c.M_le_P

theorem Y_le_Kp : Y ≤ ⁅Λ₂, Λ₂⁆ := by
  rw [← c.M_comm]; exact commutator_mono c.M_le_Λ₂ c.M_le_Λ₂

theorem Kp_le_Λ₂ : ⁅Λ₂, Λ₂⁆ ≤ Λ₂ := commutator_le.2 fun a ha b hb => by
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem Λ₂_norm_Kp : Λ₂ ≤ normalizer ((⁅Λ₂, Λ₂⁆ : Subgroup G) : Set G) := fun g hg =>
  mem_normalizer_commutator_self (Subgroup.mem_normalizer_iff.2 fun x => by
    constructor <;> intro hx
    · exact mul_mem (mul_mem hg hx) (inv_mem hg)
    · have := mul_mem (mul_mem (inv_mem hg) hx) hg
      simpa [mul_assoc] using this)

theorem Λ₂_norm_M : Λ₂ ≤ normalizer (M : Set G) := c.Λ₂_le_N₂.trans c.N₂_norm_M

theorem Λ₂_norm_W : Λ₂ ≤ normalizer (W : Set G) := c.Λ₂_le_N₂.trans c.N₂_norm_W

theorem Λ₂_norm_Y : Λ₂ ≤ normalizer (Y : Set G) := c.Λ₂_le_N₂.trans c.N₂_norm_Y

theorem derived_eq : (⁅Λ₂, Λ₂⁆ : Subgroup G) ⊔ Y = ⁅Λ₂, Λ₂⁆ := sup_eq_left.2 c.Y_le_Kp

theorem conj_Kp : (⁅Λ₂, Λ₂⁆ : Subgroup G)ᵍ[t] = ⁅Λ₂ᵍ[t], Λ₂ᵍ[t]⁆ := conj_commutator _ _ _

theorem N₂_eq_sup : N₂ = ⁅Λ₂, Λ₂⁆ ⊔ (⁅Λ₂, Λ₂⁆ : Subgroup G)ᵍ[t] ⊔ W := by
  rw [← c.hat_sup, conj_sup, c.conj_W, sup_sup_sup_comm, sup_idem]

theorem Kpt_le_Λ₂t : (⁅Λ₂, Λ₂⁆ : Subgroup G)ᵍ[t] ≤ Λ₂ᵍ[t] := conj_mono c.Kp_le_Λ₂ t

theorem Kp_comm' : ⁅(⁅Λ₂, Λ₂⁆ : Subgroup G), (⁅Λ₂, Λ₂⁆ : Subgroup G)ᵍ[t]⁆ ≤ Y := by
  have := c.Kp_comm
  rwa [c.derived_eq] at this

theorem Kp_perfect' : (⁅Λ₂, Λ₂⁆ : Subgroup G) ≤ ⁅⁅Λ₂, Λ₂⁆, ⁅Λ₂, Λ₂⁆⁆ ⊔ Y := by
  have := c.Kp_perfect
  rw [c.derived_eq] at this
  exact this.ge

theorem Y_le_Kpt : Y ≤ (⁅Λ₂, Λ₂⁆ : Subgroup G)ᵍ[t] := by
  rw [← c.conj_Y]; exact conj_mono c.Y_le_Kp t

theorem N₂_norm_Kp : N₂ ≤ normalizer ((⁅Λ₂, Λ₂⁆ : Subgroup G) : Set G) :=
  le_normalizer_of_sup c.N₂_eq_sup c.Kp_comm' c.Y_le_Kp
    (c.W_le_M.trans c.M_le_Λ₂ |>.trans c.Λ₂_norm_Kp)

theorem B₂_eq {B₂ : Subgroup G} (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    B₂ = ⁅Λ₂, Λ₂⁆ ⊓ M :=
  hB₂.trans (pCoreOf_eq_inf c.M_two c.Λ₂_norm_M c.Kp_le_Λ₂ c.Λ₂_norm_Kp c.fac₂.quot c.K_four)

theorem B₂_le_Kp {B₂ : Subgroup G} (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    B₂ ≤ ⁅Λ₂, Λ₂⁆ := by rw [c.B₂_eq hB₂]; exact inf_le_left

theorem B₂_le_M {B₂ : Subgroup G} (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    B₂ ≤ M := by rw [c.B₂_eq hB₂]; exact inf_le_right

theorem Y_le_B₂ {B₂ : Subgroup G} (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    Y ≤ B₂ := by rw [c.B₂_eq hB₂]; exact le_inf c.Y_le_Kp c.Y_le_M

theorem B₂_le_P {B₂ : Subgroup G} (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    B₂ ≤ P := (c.B₂_le_M hB₂).trans c.M_le_P

theorem N₂_norm_B₂ {B₂ : Subgroup G} (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    N₂ ≤ normalizer (B₂ : Set G) := fun g hg => by
  rw [hB₂]; exact mem_normalizer_pCoreOf (c.N₂_norm_Kp hg)

theorem B₂_conj {B₂ : Subgroup G} (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    ∀ p ∈ P, ∀ x ∈ B₂, p * x * p⁻¹ ∈ B₂ := fun p hp x hx =>
  (mem_normalizer_iff.1 (c.N₂_norm_B₂ hB₂ (c.P_le_N₂ hp)) x).1 hx

theorem Z₂t_eq {B₂ : Subgroup G} (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    centerMod W (Λ₂ᵍ[t]) = B₂ ⊔ W := by
  rw [c.center_pcore]
  have hHL : (⁅Λ₂, Λ₂⁆ : Subgroup G) ⊔ W ≤ Λ₂ := sup_le c.Kp_le_Λ₂ (c.W_le_M.trans c.M_le_Λ₂)
  have hLH : Λ₂ ≤ normalizer (((⁅Λ₂, Λ₂⁆ : Subgroup G) ⊔ W : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_sup (c.Λ₂_norm_Kp hg) (c.Λ₂_norm_W hg)
  rw [pCoreOf_eq_inf c.M_two c.Λ₂_norm_M hHL hLH c.fac₂.quot c.K_four, inf_comm,
    dedekind c.W_le_M (c.Kp_le_Λ₂.trans c.Λ₂_norm_W), inf_comm M, ← c.B₂_eq hB₂]

theorem Z₂_eq {B₂ : Subgroup G} (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    centerMod W Λ₂ = B₂ᵍ[t] ⊔ W := by
  have h := ProductN1Aux.centerMod_conj (U := W) (A := Λ₂ᵍ[t]) c.t_norm_W
    (c.W_le_M.trans c.M_le_Λ₂t)
  rw [c.conj_conj, c.Z₂t_eq hB₂, conj_sup, c.conj_W] at h
  exact h

theorem B₂t_le_Z₂ {B₂ : Subgroup G} (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    B₂ᵍ[t] ≤ centerMod W Λ₂ := by
  rw [c.Z₂_eq hB₂]; exact le_sup_left

theorem Ast_le_N₂ : Ast ≤ N₂ := c.Ast_le.trans inf_le_left

theorem Ast_norm_M : Ast ≤ normalizer (M : Set G) := c.Ast_le_N₂.trans c.N₂_norm_M

theorem levi₂ {A₂ : Subgroup G}
    (hA₂ : A₂ = Λ₂ ⊓ Ast) :
    ∀ x ∈ Λ₂, ∃ a ∈ A₂, ∃ m ∈ M, x = a * m := by
  rw [hA₂]
  exact levi_decomp c.Λ₂_le_N₂ c.M_le_Λ₂ c.Ast_norm_M c.compl₂

theorem A₂_perfect {A₂ : Subgroup G}
    (hA₂ : A₂ = Λ₂ ⊓ Ast) : ⁅A₂, A₂⁆ = A₂ := by
  rw [hA₂]
  refine factor_perfect c.Λ₂_le_N₂ c.M_le_Λ₂ (fun x hx => ?_) c.compl₂' c.fac₂.quot c.K_four
  obtain ⟨a, ha, m, hm, rfl⟩ := (mem_sup_iff_of_le_normalizer c.Ast_norm_M).1 (c.compl₂ ▸ hx)
  exact ⟨a, ha, m, hm, rfl⟩

theorem A₂_le_Kp {A₂ : Subgroup G}
    (hA₂ : A₂ = Λ₂ ⊓ Ast) : A₂ ≤ ⁅Λ₂, Λ₂⁆ := by
  have hle : A₂ ≤ Λ₂ := by rw [hA₂]; exact inf_le_left
  calc A₂ = ⁅A₂, A₂⁆ := (c.A₂_perfect hA₂).symm
    _ ≤ ⁅Λ₂, Λ₂⁆ := commutator_mono hle hle

theorem Kp_eq_sup {A₂ B₂ : Subgroup G} (hA₂ : A₂ = Λ₂ ⊓ Ast)
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) : (⁅Λ₂, Λ₂⁆ : Subgroup G) = A₂ ⊔ B₂ := by
  refine le_antisymm (fun k hk0 => ?_) (sup_le (c.A₂_le_Kp hA₂) (c.B₂_le_Kp hB₂))
  have hk : k ∈ ⁅Λ₂, Λ₂⁆ ⊔ W := mem_sup_left hk0
  rw [c.hat_levi, ← hA₂, c.Z₂t_eq hB₂] at hk
  have hA₂N : A₂ ≤ normalizer (((B₂ ⊔ W : Subgroup G)) : Set G) := by
    rw [← c.Z₂t_eq hB₂]
    intro g hg
    have hgN₂ : g ∈ N₂ := by
      rw [hA₂] at hg
      exact c.Ast_le_N₂ (mem_inf.1 hg).2
    exact ProductN1Aux.mem_normalizer_centerMod (c.N₂_norm_W hgN₂) (c.N₂_norm_Λ₂t hgN₂)
      (c.W_le_M.trans c.M_le_Λ₂t)
  obtain ⟨a, ha, z, hz, rfl⟩ := (mem_sup_iff_of_le_normalizer hA₂N).1 hk
  have hzK : z ∈ ⁅Λ₂, Λ₂⁆ := by
    have := mul_mem (inv_mem (c.A₂_le_Kp hA₂ ha)) hk0
    simpa using this
  have hzM : z ∈ M := (sup_le (c.B₂_le_M hB₂) c.W_le_M) hz
  have hzB : z ∈ B₂ := by
    rw [c.B₂_eq hB₂]; exact mem_inf.2 ⟨hzK, hzM⟩
  exact mul_mem (mem_sup_left ha) (mem_sup_right hzB)

end Cfg

end ProductLiftsAux

end Part9

section Part10

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc
  mem_centerMod_iff mem_centralizerMod_iff commutator_mem_iff_proj)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux
  (mem_sup_iff_of_le_normalizer mem_sup_iff_of_le_normalizer' Sl2Pair mem_normalizer_of_pow_mem
    le_normalizer_of_commutator_mem conj_inf conj_sup conj_commutator conj_conj_of_mul_self
    conj_eq_of_mem_normalizer card_conj pCoreOf_conj mem_normalizer_of_conj_eq
    mem_normalizer_pCoreOf conj_mono mem_conj_iff)
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_inf mem_normalizer_sup)

namespace ProductLiftsAux

namespace Cfg

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
  {t : G} {U Y W F M D P N₁ N₂ Λ₁ Λ₂ J₃ J₄ J S Ast : Subgroup G}
  (c : Cfg K t U Y W F M D P N₁ N₂ Λ₁ Λ₂ J₃ J₄ J S Ast)

include c

theorem B₂t_le_P₁t {B₂ : Subgroup G} (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    B₂ᵍ[t] ≤ (P ⊓ Λ₁)ᵍ[t] := by
  have h1 : centerMod W Λ₂ ≤ centerMod Y (P ⊓ Λ₂) := by
    rw [c.center_P₂', c.center_P₂]; exact le_sup_right
  have h2 : centerMod Y (P ⊓ Λ₂) ≤ (P ⊓ Λ₁)ᵍ[t] := by rw [c.label]; exact le_sup_left
  exact (c.B₂t_le_Z₂ hB₂).trans (h1.trans h2)

theorem B₂t_le_Λ₁t {B₂ : Subgroup G} (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    B₂ᵍ[t] ≤ Λ₁ᵍ[t] :=
  (c.B₂t_le_P₁t hB₂).trans (conj_mono inf_le_right t)

theorem B₂_le_Λ₁ {B₂ : Subgroup G} (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    B₂ ≤ Λ₁ := by
  have := conj_mono (c.B₂t_le_Λ₁t hB₂) t
  rwa [c.conj_conj, c.conj_conj] at this

theorem B₂t_le_M {B₂ : Subgroup G} (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    B₂ᵍ[t] ≤ M := by
  have := conj_mono (c.B₂_le_M hB₂) t
  rwa [c.conj_M] at this

theorem D6 {B₁ B₂ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G))
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    ∀ x ∈ B₁, ∀ y ∈ B₂ᵍ[t], x * y * x⁻¹ * y⁻¹ ∈ Y := by
  intro x hx y hy
  rw [c.B₁_eq hB₁] at hx
  obtain ⟨-, -, hc⟩ := (mem_centerMod_iff (c.U_le_D.trans c.D_le_Λ₁t)).1 hx
  have hyN : y ∈ normalizer (U : Set G) :=
    c.P_norm_U (c.M_le_P (c.B₂t_le_M hB₂ hy))
  exact c.U_le_Y (hc y (c.B₂t_le_Λ₁t hB₂ hy) hyN)

theorem D6' {B₁ B₂ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G))
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    ∀ x ∈ B₁ᵍ[t], ∀ y ∈ B₂, x * y * x⁻¹ * y⁻¹ ∈ Y := by
  intro x hx y hy
  rw [c.B₁t_eq hB₁] at hx
  obtain ⟨-, -, hc⟩ := (mem_centerMod_iff (c.U_le_D.trans c.D_le_Λ₁)).1 hx
  have hyN : y ∈ normalizer (U : Set G) := c.P_norm_U (c.B₂_le_P hB₂ hy)
  exact c.U_le_Y (hc y (c.B₂_le_Λ₁ hB₂ hy) hyN)

theorem Kp_norm_Kpt : (⁅Λ₂, Λ₂⁆ : Subgroup G) ≤
    normalizer (((⁅Λ₂, Λ₂⁆ : Subgroup G)ᵍ[t] : Subgroup G) : Set G) :=
  le_normalizer_of_commutator_mem fun x hx y hy =>
    c.Y_le_Kpt (c.Kp_comm' (Subgroup.commutator_mem_commutator hx hy))

theorem M_norm_Kpt : M ≤ normalizer (((⁅Λ₂, Λ₂⁆ : Subgroup G)ᵍ[t] : Subgroup G) : Set G) :=
  fun g hg => conj_normalizer_le (g := t) c.Λ₂_norm_Kp (c.M_le_Λ₂t hg)

theorem N₂_dec : ∀ x ∈ N₂, ∃ k ∈ (⁅Λ₂, Λ₂⁆ : Subgroup G), ∃ k' ∈ (⁅Λ₂, Λ₂⁆ : Subgroup G)ᵍ[t],
    ∃ w ∈ W, x = k * k' * w := by
  intro x hx
  have hx' : x ∈ ((⁅Λ₂, Λ₂⁆ : Subgroup G) ⊔ (⁅Λ₂, Λ₂⁆ : Subgroup G)ᵍ[t]) ⊔ W := by
    rw [← c.N₂_eq_sup]; exact hx
  have hWN : W ≤ normalizer ((((⁅Λ₂, Λ₂⁆ : Subgroup G) ⊔ (⁅Λ₂, Λ₂⁆ : Subgroup G)ᵍ[t]) :
      Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_sup (c.Λ₂_norm_Kp (c.W_le_M.trans c.M_le_Λ₂ hg))
      (c.M_norm_Kpt (c.W_le_M hg))
  obtain ⟨u, hu, w, hw, rfl⟩ := (mem_sup_iff_of_le_normalizer' hWN).1 hx'
  obtain ⟨k, hk, k', hk', rfl⟩ := (mem_sup_iff_of_le_normalizer c.Kp_norm_Kpt).1 hu
  exact ⟨k, hk, k', hk', w, hw, rfl⟩

theorem not_centralizes {A₂ B₂ : Subgroup G} (hA₂ : A₂ = Λ₂ ⊓ Ast)
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    ¬ ∀ b ∈ ⁅Λ₂ᵍ[t], Λ₂ᵍ[t]⁆ ⊓ M, ∀ k ∈ ⁅Λ₂ᵍ[t], Λ₂ᵍ[t]⁆, ⁅k, b⁆ ∈ Y := by
  intro h
  have hBt : B₂ᵍ[t] = ⁅Λ₂ᵍ[t], Λ₂ᵍ[t]⁆ ⊓ M := by
    rw [c.B₂_eq hB₂, conj_inf, c.conj_M, c.conj_Kp]
  have hMc : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ Y := fun x hx y hy => by
    have := Subgroup.commutator_mem_commutator hx hy
    rwa [c.M_comm, commutatorElement_def] at this
  have hL : Λ₂ ≤ A₂ ⊔ M := fun x hx => by
    obtain ⟨a, ha, m, hm, rfl⟩ := c.levi₂ hA₂ x hx
    exact mul_mem (mem_sup_left ha) (mem_sup_right hm)
  have hLt : Λ₂ᵍ[t] ≤ A₂ᵍ[t] ⊔ M := by
    have := conj_mono hL t
    rwa [conj_sup, c.conj_M] at this
  have hBW : B₂ᵍ[t] ≤ W := by
    intro b hb
    have hbM : b ∈ M := c.B₂t_le_M hB₂ hb
    have hbZ : b ∈ centerMod W Λ₂ := c.B₂t_le_Z₂ hB₂ hb
    have hWΛ : W ≤ Λ₂ := c.W_le_M.trans c.M_le_Λ₂
    have hΛc := ((ProductN1Aux.mem_centerMod_iff_of_le hWΛ c.Λ₂_norm_W).1 hbZ).2
    have h1 : Λ₂ ≤ commSubgroup W b := fun g hg =>
      mem_commSubgroup_iff.2 ⟨c.Λ₂_norm_W hg, hΛc g hg⟩
    have h2 : A₂ᵍ[t] ≤ commSubgroup W b := fun g hg => by
      have hgK : g ∈ ⁅Λ₂ᵍ[t], Λ₂ᵍ[t]⁆ := by
        rw [← c.conj_Kp]; exact conj_mono (c.A₂_le_Kp hA₂) t hg
      refine mem_commSubgroup_iff.2 ⟨c.N₂_norm_W (c.Λ₂t_le_N₂ (c.Kpt_le_Λ₂t
        (c.conj_Kp ▸ hgK))), ?_⟩
      have hb' : b ∈ ⁅Λ₂ᵍ[t], Λ₂ᵍ[t]⁆ ⊓ M := by rw [← hBt]; exact hb
      have h3 : g * b * g⁻¹ * b⁻¹ ∈ Y := by
        have := h b hb' g hgK
        rwa [commutatorElement_def] at this
      have h4 := inv_mem h3
      have e : (g * b * g⁻¹ * b⁻¹)⁻¹ = b * g * b⁻¹ * g⁻¹ := by group
      rw [e] at h4
      exact c.Y_le_W h4
    have h3 : M ≤ commSubgroup W b := fun g hg =>
      mem_commSubgroup_iff.2 ⟨c.N₂_norm_W (c.M_le_Λ₂.trans c.Λ₂_le_N₂ hg),
        c.Y_le_W (hMc b hbM g hg)⟩
    have hN : N₂ ≤ commSubgroup W b := by
      rw [← c.fac₂.sup]; exact sup_le h1 (hLt.trans (sup_le h2 h3))
    have hbN : b ∈ centerMod W N₂ :=
      (ProductN1Aux.mem_centerMod_iff_of_le (c.W_le_M.trans (c.M_le_Λ₂.trans c.Λ₂_le_N₂))
        c.N₂_norm_W).2 ⟨c.M_le_Λ₂.trans c.Λ₂_le_N₂ hbM,
        fun a ha => (mem_commSubgroup_iff.1 (hN ha)).2⟩
    rwa [c.center_N₂_W] at hbN
  have h5 := c.rel_center
  rw [c.Z₂_eq hB₂, sup_eq_right.2 hBW, Subgroup.relIndex_self] at h5
  have h4 := c.K_four
  have : 4 * 4 ≤ Nat.card K ^ 2 := by rw [sq]; exact Nat.mul_le_mul h4 h4
  omega

theorem B₁_le_Λ₂ {A₂ B₁ B₂ : Subgroup G} (hA₂ : A₂ = Λ₂ ⊓ Ast)
    (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G))
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) : B₁ ≤ Λ₂ := by
  have hBt : B₂ᵍ[t] = ⁅Λ₂ᵍ[t], Λ₂ᵍ[t]⁆ ⊓ M := by
    rw [c.B₂_eq hB₂, conj_inf, c.conj_M, c.conj_Kp]
  have hMc : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ Y := fun x hx y hy => by
    have := Subgroup.commutator_mem_commutator hx hy
    rwa [c.M_comm, commutatorElement_def] at this
  refine le_of_centralizes_mod (t := t) (Y := Y) (W := W) (N := N₂) (K₂ := ⁅Λ₂, Λ₂⁆)
    (B₂ := B₂) c.N₂_norm_Y c.N₂_dec ?_ ?_ ?_ (c.D6 hB₁ hB₂) ((c.B₁_le_P hB₁).trans c.P_le_N₂)
    (c.Kp_le_Λ₂.trans c.Λ₂_le_N₂) (c.Kpt_le_Λ₂t.trans c.Λ₂t_le_N₂)
    (conj_mono (c.B₂_le_Kp hB₂) t) ((c.B₂t_le_M hB₂).trans (c.M_le_Λ₂.trans c.Λ₂_le_N₂))
    c.Kp_le_Λ₂ (c.W_le_M.trans c.M_le_Λ₂) ((c.B₂t_le_M hB₂).trans c.M_le_Λ₂)
  · intro k hk y hy
    have := c.Kp_comm' (Subgroup.commutator_mem_commutator hk hy)
    rwa [commutatorElement_def] at this
  · intro w hw n hn
    have hw' : w ∈ centerMod Y N₂ := by rw [c.center_N₂_Y]; exact hw
    have := ((ProductN1Aux.mem_centerMod_iff_of_le (c.Y_le_M.trans (c.M_le_Λ₂.trans c.Λ₂_le_N₂))
      c.N₂_norm_Y).1 hw').2 n hn
    rwa [commutatorElement_def]
  · intro k' hk' h
    have hk'' : k' ∈ ⁅Λ₂ᵍ[t], Λ₂ᵍ[t]⁆ := by rw [← c.conj_Kp]; exact hk'
    have hYB : Y ≤ ⁅Λ₂ᵍ[t], Λ₂ᵍ[t]⁆ ⊓ M := le_inf (c.conj_Kp ▸ c.Y_le_Kpt) c.Y_le_M
    have hBab : ∀ x ∈ ⁅Λ₂ᵍ[t], Λ₂ᵍ[t]⁆ ⊓ M, ∀ y ∈ ⁅Λ₂ᵍ[t], Λ₂ᵍ[t]⁆ ⊓ M, ⁅x, y⁆ ∈ Y :=
      fun x hx y hy => hMc x (mem_inf.1 hx).2 y (mem_inf.1 hy).2
    have key := le_pcore_of_centralizes (M := M) (L := Λ₂ᵍ[t]) (N := N₂) (Y := Y)
      c.Λ₂t_le_N₂ c.N₂_norm_M c.N₂_norm_Y c.N₂_norm_Λ₂t c.M_le_Λ₂t hYB c.sl₂.isoK' c.K_four hBab
      (c.not_centralizes hA₂ hB₂) k' hk'' (fun y hy => h y (by rw [hBt]; exact hy))
    rw [hBt]
    exact mem_inf.2 ⟨hk'', key⟩

theorem P₂_eq {A₂ B₁ B₂ : Subgroup G} (hA₂ : A₂ = Λ₂ ⊓ Ast)
    (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G))
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) : P ⊓ Λ₂ = B₁ ⊔ M := by
  have hB₁Λ := c.B₁_le_Λ₂ hA₂ hB₁ hB₂
  refine le_antisymm ?_ (sup_le (le_inf (c.B₁_le_P hB₁) hB₁Λ) (le_inf c.M_le_P c.M_le_Λ₂))
  refine inf_le_sup_of_prod (B' := B₁ᵍ[t]) (fun p hp => ?_) hB₁Λ ?_ c.fac₂.inf c.M_le_Λ₂
  · obtain ⟨m, hm, d, hd, rfl⟩ := c.P_mul p hp
    obtain ⟨b, hb, b', hb', rfl⟩ := c.D_mul hB₁ d hd
    exact ⟨m, hm, b, hb, b', hb', by group⟩
  · exact conj_mono hB₁Λ t

end Cfg

end ProductLiftsAux

end Part10

section Part11

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc
  mem_centerMod_iff mem_centralizerMod_iff commutator_mem_iff_proj)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux
  (mem_sup_iff_of_le_normalizer mem_sup_iff_of_le_normalizer' Sl2Pair mem_normalizer_of_pow_mem
    le_normalizer_of_commutator_mem conj_inf conj_sup conj_commutator conj_conj_of_mul_self
    conj_eq_of_mem_normalizer card_conj pCoreOf_conj mem_normalizer_of_conj_eq
    mem_normalizer_pCoreOf conj_mono mem_conj_iff)
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_inf mem_normalizer_sup)
open CFSG.LocalAnalysis.EvenBN.TrialityD4 (card_sup_mul_card_inf_eq_D4)

namespace ProductLiftsAux

namespace Cfg

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
  {t : G} {U Y W F M D P N₁ N₂ Λ₁ Λ₂ J₃ J₄ J S Ast : Subgroup G}
  (c : Cfg K t U Y W F M D P N₁ N₂ Λ₁ Λ₂ J₃ J₄ J S Ast)

include c

theorem card_P₂ : Nat.card (P ⊓ Λ₂ : Subgroup G) = Nat.card K ^ 11 := by
  rw [card_inf_sylow c.sl₂ c.sylow₂ c.M_le_P, c.card_M]; ring

theorem card_P₁ : Nat.card (P ⊓ Λ₁ : Subgroup G) = Nat.card K ^ 11 := by
  rw [card_inf_sylow c.sl₁ c.sylow₁ c.D_le_P, c.card_D]; ring

theorem card_α {A₂ B₁ B₂ : Subgroup G} (hA₂ : A₂ = Λ₂ ⊓ Ast)
    (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G))
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    Nat.card (B₁ ⊓ M : Subgroup G) = Nat.card K ^ 5 := by
  have h1 := card_sup_mul_card_inf_eq_D4 (A := M) (B := B₁) ((c.B₁_le_P hB₁).trans c.P_norm_M)
  rw [sup_comm, ← c.P₂_eq hA₂ hB₁ hB₂, c.card_P₂, c.card_M, c.card_B₁ hB₁, inf_comm] at h1
  have hq : 0 < Nat.card K ^ 11 := pow_pos Nat.card_pos 11
  have h2 : Nat.card K ^ 11 * Nat.card (B₁ ⊓ M : Subgroup G) = Nat.card K ^ 11 * Nat.card K ^ 5 :=
    h1.trans (by ring)
  exact Nat.eq_of_mul_eq_mul_left hq h2

theorem Y_split {B₁ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G)) :
    ∀ y ∈ Y, ∃ b ∈ B₁ ⊓ Y, ∃ b' ∈ B₁ᵍ[t] ⊓ Y, y = b * b' := by
  refine split_center (U := U) (D := D) (P := P) (c.D_mul hB₁) (c.U_le_B₁t hB₁) (c.B₁_inf hB₁)
    (c.B₁_le_P hB₁) (c.B₁t_le_P hB₁) (c.B₁_conj hB₁) (c.B₁t_conj hB₁)
    (c.Y_le_W.trans (c.W_le_F.trans c.F_le_D)) (fun x hx y hy => ?_) (c.B₁_le_D hB₁)
    (c.B₁t_le_D hB₁) (fun y hy p hp => ?_) (fun x hx hxc => ?_)
  · have := Subgroup.commutator_mem_commutator hx hy
    rwa [c.D_comm, commutatorElement_def] at this
  · have hy' : y ∈ centerMod U P := by rw [c.P_center]; exact hy
    obtain ⟨-, -, hc⟩ := (mem_centerMod_iff (c.U_le_D.trans c.D_le_P)).1 hy'
    have := hc p hp (c.P_norm_U hp)
    rwa [commutatorElement_def]
  · have : x ∈ centerMod U P := by
      refine (mem_centerMod_iff (c.U_le_D.trans c.D_le_P)).2 ⟨hx, c.P_norm_U hx, fun a ha _ => ?_⟩
      have := hxc a ha
      rwa [commutatorElement_def] at this
    rwa [c.P_center] at this

theorem card_B₁_inf_Y {B₁ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G)) :
    Nat.card (B₁ ⊓ Y : Subgroup G) = Nat.card K ^ 3 := by
  set X : Subgroup G := B₁ ⊓ Y with hX
  set Z : Subgroup G := B₁ᵍ[t] ⊓ Y with hZ
  have hZN : Z ≤ normalizer (X : Set G) := fun z hz =>
    mem_normalizer_inf (c.P_norm_B₁ hB₁ (c.B₁t_le_P hB₁ (mem_inf.1 hz).1))
      (c.P_norm_Y (c.B₁t_le_P hB₁ (mem_inf.1 hz).1))
  have h1 := card_sup_mul_card_inf_eq_D4 hZN |>.symm
  have hsup : X ⊔ Z = Y := by
    refine le_antisymm (sup_le inf_le_right inf_le_right) (fun y hy => ?_)
    obtain ⟨b, hb, b', hb', rfl⟩ := c.Y_split hB₁ y hy
    exact mul_mem (mem_sup_left hb) (mem_sup_right hb')
  have hinf : X ⊓ Z = U := by
    refine le_antisymm ?_
      (le_inf (le_inf (c.U_le_B₁ hB₁) c.U_le_Y) (le_inf (c.U_le_B₁t hB₁) c.U_le_Y))
    intro x hx
    obtain ⟨hxX, hxZ⟩ := mem_inf.1 hx
    rw [← c.B₁_inf hB₁]
    exact mem_inf.2 ⟨(mem_inf.1 hxX).1, (mem_inf.1 hxZ).1⟩
  have hZc : Nat.card Z = Nat.card X := by
    have : Z = Xᵍ[t] := by rw [hX, conj_inf, c.conj_Y]
    rw [this, card_conj]
  rw [hsup, hinf, hZc, c.card_Y, c.card_U] at h1
  have h2 : Nat.card X * Nat.card X = Nat.card K ^ 3 * Nat.card K ^ 3 := h1.trans (by ring)
  exact Nat.mul_self_inj.1 h2

theorem B₁Y_inf {B₁ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G)) :
    (B₁ ⊔ Y) ⊓ (B₁ᵍ[t] ⊔ Y) ≤ Y :=
  inf_sup_le_of_split (c.Y_split hB₁) c.U_le_Y (c.B₁_inf hB₁) (c.B₁_le_P hB₁) (c.B₁t_le_P hB₁)
    c.P_norm_Y (c.B₁t_conj hB₁)

theorem B₁_inf_F_eq {B₁ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G)) :
    F ⊓ B₁ = B₁ ⊓ M := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨hxF, hxB⟩ := mem_inf.1 hx
    exact mem_inf.2 ⟨hxB, c.F_le_M hxF⟩
  · obtain ⟨hxB, hxM⟩ := mem_inf.1 hx
    refine mem_inf.2 ⟨?_, hxB⟩
    rw [← c.M_inf_D]
    exact mem_inf.2 ⟨hxM, c.B₁_le_D hB₁ hxB⟩

theorem card_αY_le {A₂ B₁ B₂ : Subgroup G} (hA₂ : A₂ = Λ₂ ⊓ Ast)
    (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G))
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    Nat.card ((B₁ ⊔ Y) ⊓ F : Subgroup G) ≤ Nat.card K ^ 2 * Nat.card Y := by
  have hYF : Y ≤ F := c.Y_le_W.trans c.W_le_F
  have hB₁N : B₁ ≤ normalizer (Y : Set G) := (c.B₁_le_P hB₁).trans c.P_norm_Y
  have h1 : (B₁ ⊔ Y) ⊓ F = Y ⊔ (F ⊓ B₁) := by
    rw [inf_comm, dedekind hYF hB₁N, sup_comm]
  have hFB : F ⊓ B₁ ≤ normalizer (Y : Set G) := inf_le_right.trans hB₁N
  have h2 := card_sup_mul_card_inf_eq_D4 hFB
  have h3 : Y ⊓ (F ⊓ B₁) = B₁ ⊓ Y := by
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨hxY, hxFB⟩ := mem_inf.1 hx
      exact mem_inf.2 ⟨(mem_inf.1 hxFB).2, hxY⟩
    · obtain ⟨hxB, hxY⟩ := mem_inf.1 hx
      exact mem_inf.2 ⟨hxY, mem_inf.2 ⟨hYF hxY, hxB⟩⟩
  rw [h3, c.card_B₁_inf_Y hB₁, c.B₁_inf_F_eq hB₁, c.card_α hA₂ hB₁ hB₂, c.card_Y] at h2
  rw [h1, c.B₁_inf_F_eq hB₁]
  have hq : 0 < Nat.card K ^ 3 := pow_pos Nat.card_pos 3
  have h4 : Nat.card (Y ⊔ (B₁ ⊓ M) : Subgroup G) = Nat.card K ^ 2 * Nat.card K ^ 4 :=
    Nat.eq_of_mul_eq_mul_right hq (h2.trans (by ring))
  rw [h4, c.card_Y]

end Cfg

end ProductLiftsAux

end Part11

section Part12

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc
  mem_centerMod_iff mem_centralizerMod_iff commutator_mem_iff_proj)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux
  (mem_sup_iff_of_le_normalizer mem_sup_iff_of_le_normalizer' Sl2Pair mem_normalizer_of_pow_mem
    le_normalizer_of_commutator_mem conj_inf conj_sup conj_commutator conj_conj_of_mul_self
    conj_eq_of_mem_normalizer card_conj pCoreOf_conj mem_normalizer_of_conj_eq
    mem_normalizer_pCoreOf conj_mono mem_conj_iff)
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_inf mem_normalizer_sup)
open CFSG.LocalAnalysis.EvenBN.TrialityD4 (card_sup_mul_card_inf_eq_D4)

namespace ProductLiftsAux

namespace Cfg

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
  {t : G} {U Y W F M D P N₁ N₂ Λ₁ Λ₂ J₃ J₄ J S Ast : Subgroup G}
  (c : Cfg K t U Y W F M D P N₁ N₂ Λ₁ Λ₂ J₃ J₄ J S Ast)

include c

theorem D_comm_mem : ∀ x ∈ D, ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ U := fun x hx y hy => by
  have := Subgroup.commutator_mem_commutator hx hy
  rwa [c.D_comm, commutatorElement_def] at this

theorem M_comm_mem : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ Y := fun x hx y hy => by
  have := Subgroup.commutator_mem_commutator hx hy
  rwa [c.M_comm, commutatorElement_def] at this

theorem P_dec {B₁ B₂ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G))
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    ∀ p ∈ P, ∃ b₂ ∈ B₂, ∃ b₂' ∈ B₂ᵍ[t], ∃ b₁ ∈ B₁, ∃ b₁' ∈ B₁ᵍ[t],
      p = b₂ * b₂' * b₁ * b₁' := by
  have hB₂N : B₂ ≤ normalizer (W : Set G) :=
    ((c.B₂_le_M hB₂).trans (c.M_le_Λ₂.trans c.Λ₂_le_N₂)).trans c.N₂_norm_W
  have hB₂tN : B₂ᵍ[t] ≤ normalizer (W : Set G) :=
    ((c.B₂t_le_M hB₂).trans (c.M_le_Λ₂.trans c.Λ₂_le_N₂)).trans c.N₂_norm_W
  have hZ12 : (B₂ ⊔ W) ≤ normalizer (((B₂ᵍ[t] ⊔ W : Subgroup G)) : Set G) := by
    rw [← c.Z₂_eq hB₂]
    intro g hg
    have hgM : g ∈ M := (sup_le (c.B₂_le_M hB₂) c.W_le_M) hg
    have hgN : g ∈ N₂ := c.M_le_Λ₂.trans c.Λ₂_le_N₂ hgM
    exact ProductN1Aux.mem_normalizer_centerMod (c.N₂_norm_W hgN) (c.N₂_norm_Λ₂ hgN)
      (c.W_le_M.trans c.M_le_Λ₂)
  have hM : ∀ m ∈ M, ∃ z₁ ∈ B₂ ⊔ W, ∃ z₂ ∈ B₂ᵍ[t] ⊔ W, m = z₁ * z₂ := by
    intro m hm
    have hm' : m ∈ (B₂ ⊔ W) ⊔ (B₂ᵍ[t] ⊔ W) := by
      rw [← c.Z₂t_eq hB₂, ← c.Z₂_eq hB₂, sup_comm, c.center_sup]; exact hm
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := (mem_sup_iff_of_le_normalizer hZ12).1 hm'
    exact ⟨z₁, hz₁, z₂, hz₂, rfl⟩
  exact prod_decomp (Z₁ := B₂ ⊔ W) (Z₂ := B₂ᵍ[t] ⊔ W) c.P_mul hM
    (fun z hz => (mem_sup_iff_of_le_normalizer hB₂N).1 hz)
    (fun z hz => (mem_sup_iff_of_le_normalizer hB₂tN).1 hz) (c.D_mul hB₁) c.W_le_D
    ((c.B₂t_le_M hB₂).trans c.M_le_P)
    (fun p hp x hx => (mem_normalizer_iff.1 (c.P_norm_D hp) x).1 hx)

theorem α_le_B₂ {A₂ B₁ B₂ : Subgroup G} (hA₂ : A₂ = Λ₂ ⊓ Ast)
    (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G))
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) : B₁ ⊓ M ≤ B₂ := by
  have hYF : Y ≤ F := c.Y_le_W.trans c.W_le_F
  have h11 : ∀ x ∈ B₁, ∀ y ∈ B₁ᵍ[t], x * y * x⁻¹ * y⁻¹ ∈ Y := fun x hx y hy =>
    c.U_le_Y (c.D_comm_mem x (c.B₁_le_D hB₁ hx) y (c.B₁t_le_D hB₁ hy))
  have h22 : ∀ x ∈ B₂, ∀ y ∈ B₂ᵍ[t], x * y * x⁻¹ * y⁻¹ ∈ Y := fun x hx y hy => by
    have := c.Kp_comm' (Subgroup.commutator_mem_commutator (c.B₂_le_Kp hB₂ hx)
      (conj_mono (c.B₂_le_Kp hB₂) t hy))
    rwa [commutatorElement_def] at this
  have h21 : ∀ x ∈ B₂, ∀ y ∈ B₁ᵍ[t], x * y * x⁻¹ * y⁻¹ ∈ Y := fun x hx y hy => by
    have h := inv_mem (c.D6' hB₁ hB₂ y hy x hx)
    have e : (y * x * y⁻¹ * x⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ := by group
    rwa [e] at h
  have hab₁ : ∀ x ∈ B₁, ∀ y ∈ B₁, x * y * x⁻¹ * y⁻¹ ∈ Y := fun x hx y hy =>
    c.U_le_Y (c.D_comm_mem x (c.B₁_le_D hB₁ hx) y (c.B₁_le_D hB₁ hy))
  have hab₂ : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y * x⁻¹ * y⁻¹ ∈ Y := fun x hx y hy =>
    c.M_comm_mem x (c.B₂_le_M hB₂ hx) y (c.B₂_le_M hB₂ hy)
  have key := alpha_le_B2 (t := t) c.t_sq (Y := Y) (B₁ := B₁) (B₂ := B₂) (P := P) (F5 := F)
    (S := S) (q := Nat.card K) c.t_norm_Y c.P_norm_Y (c.B₁_le_P hB₁) (c.B₂_le_P hB₂)
    (c.B₁_conj hB₁) (c.B₂_conj hB₂) (c.Y_le_B₂ hB₂) hYF (c.F_le_M.trans c.M_le_P) c.P_comm
    h11 h22 (c.D6 hB₁ hB₂) h21 hab₁ hab₂ c.S_le_P c.S_fix
    (fun s hs => c.P_dec hB₁ hB₂ s (c.S_le_P hs)) c.S_card (c.card_αY_le hA₂ hB₁ hB₂)
  rw [← c.B₁_inf_F_eq hB₁]
  exact key

end Cfg

end ProductLiftsAux

end Part12

section Part13

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc
  mem_centerMod_iff mem_centralizerMod_iff commutator_mem_iff_proj)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux
  (mem_sup_iff_of_le_normalizer mem_sup_iff_of_le_normalizer' Sl2Pair mem_normalizer_of_pow_mem
    le_normalizer_of_commutator_mem conj_inf conj_sup conj_commutator conj_conj_of_mul_self
    conj_eq_of_mem_normalizer card_conj pCoreOf_conj mem_normalizer_of_conj_eq
    mem_normalizer_pCoreOf conj_mono mem_conj_iff)
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_inf mem_normalizer_sup)
open CFSG.LocalAnalysis.EvenBN.TrialityD4 (card_sup_mul_card_inf_eq_D4)

namespace ProductLiftsAux

namespace Cfg

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
  {t : G} {U Y W F M D P N₁ N₂ Λ₁ Λ₂ J₃ J₄ J S Ast : Subgroup G}
  (c : Cfg K t U Y W F M D P N₁ N₂ Λ₁ Λ₂ J₃ J₄ J S Ast)

include c

theorem U_le_M : U ≤ M := c.U_le_Y.trans c.Y_le_M

theorem F_eq_sup {A₂ B₁ B₂ : Subgroup G} (hA₂ : A₂ = Λ₂ ⊓ Ast)
    (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G))
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    (B₁ ⊓ M) ⊔ (B₁ ⊓ M)ᵍ[t] = F := by
  set α : Subgroup G := B₁ ⊓ M with hα
  have hαF : α ≤ F := fun x hx => by
    rw [← c.M_inf_D]
    exact mem_inf.2 ⟨(mem_inf.1 hx).2, c.B₁_le_D hB₁ (mem_inf.1 hx).1⟩
  have hαtF : αᵍ[t] ≤ F := by
    have := conj_mono hαF t
    rwa [c.conj_F] at this
  refine Subgroup.eq_of_le_of_card_ge (sup_le hαF hαtF) ?_
  have hαtB : αᵍ[t] ≤ B₁ᵍ[t] := conj_mono inf_le_left t
  have hαN : αᵍ[t] ≤ normalizer (α : Set G) := fun g hg => by
    have hgP : g ∈ P := c.B₁t_le_P hB₁ (hαtB hg)
    exact mem_normalizer_inf (c.P_norm_B₁ hB₁ hgP) (c.P_norm_M hgP)
  have h1 := card_sup_mul_card_inf_eq_D4 hαN
  have hinf : α ⊓ αᵍ[t] = U := by
    refine le_antisymm (fun x hx => ?_) (le_inf (le_inf (c.U_le_B₁ hB₁) c.U_le_M) ?_)
    · rw [← c.B₁_inf hB₁]
      exact mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 hx).1).1, hαtB (mem_inf.1 hx).2⟩
    · have := conj_mono (le_inf (c.U_le_B₁ hB₁) c.U_le_M) t
      rwa [c.conj_U] at this
  rw [hinf, card_conj, c.card_α hA₂ hB₁ hB₂, c.card_U] at h1
  have h2 : Nat.card K ^ 8 * Nat.card K ^ 2 = Nat.card (α ⊔ αᵍ[t] : Subgroup G) * Nat.card K ^ 2 :=
    (by ring : Nat.card K ^ 8 * Nat.card K ^ 2 = Nat.card K ^ 5 * Nat.card K ^ 5).trans h1.symm
  have h3 := Nat.eq_of_mul_eq_mul_right (pow_pos Nat.card_pos 2) h2
  rw [c.card_F]
  exact h3.le

theorem F_le_sup {A₂ B₁ B₂ : Subgroup G} (hA₂ : A₂ = Λ₂ ⊓ Ast)
    (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G))
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) : F ≤ B₂ ⊔ B₂ᵍ[t] := by
  rw [← c.F_eq_sup hA₂ hB₁ hB₂]
  exact sup_le_sup (c.α_le_B₂ hA₂ hB₁ hB₂) (conj_mono (c.α_le_B₂ hA₂ hB₁ hB₂) t)

theorem M_eq_sup {A₂ B₁ B₂ : Subgroup G} (hA₂ : A₂ = Λ₂ ⊓ Ast)
    (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G))
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) : B₂ ⊔ B₂ᵍ[t] = M := by
  have hW : W ≤ B₂ ⊔ B₂ᵍ[t] := c.W_le_F.trans (c.F_le_sup hA₂ hB₁ hB₂)
  refine le_antisymm (sup_le (c.B₂_le_M hB₂) (c.B₂t_le_M hB₂)) ?_
  rw [← c.center_sup, c.Z₂_eq hB₂, c.Z₂t_eq hB₂]
  exact sup_le (sup_le le_sup_right hW) (sup_le le_sup_left hW)

theorem Kp_le_N₂ : (⁅Λ₂, Λ₂⁆ : Subgroup G) ≤ N₂ := c.Kp_le_Λ₂.trans c.Λ₂_le_N₂

theorem Kp_inf_Kpt {A₂ B₁ B₂ : Subgroup G} (hA₂ : A₂ = Λ₂ ⊓ Ast)
    (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G))
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    (⁅Λ₂, Λ₂⁆ : Subgroup G) ⊓ (⁅Λ₂, Λ₂⁆ : Subgroup G)ᵍ[t] = Y := by
  have hE : (⁅Λ₂, Λ₂⁆ : Subgroup G) ⊓ (⁅Λ₂, Λ₂⁆ : Subgroup G)ᵍ[t] ≤ W :=
    inf_le_center c.N₂_eq_sup (c.Y_le_M.trans (c.M_le_Λ₂.trans c.Λ₂_le_N₂)) c.N₂_norm_Y
      c.Kp_comm' c.center_N₂_Y
  have hQ : IsSylowOf 2 (P ⊓ ⁅Λ₂, Λ₂⁆) (⁅Λ₂, Λ₂⁆ : Subgroup G) :=
    c.sylow₂.inf_of_le_normalizer c.Kp_le_N₂ c.N₂_norm_Kp
  have hP₂ := c.P₂_eq hA₂ hB₁ hB₂
  have hsub : P ⊓ ⁅Λ₂, Λ₂⁆ ≤ B₁ ⊔ M := by
    rw [← hP₂]; exact inf_le_inf_left P c.Kp_le_Λ₂
  have hQc : ⁅P ⊓ ⁅Λ₂, Λ₂⁆, P ⊓ ⁅Λ₂, Λ₂⁆⁆ ≤ B₁ ⊔ Y :=
    (commutator_mono hsub hsub).trans (commutator_sup_le_sup
      ((c.B₁_le_P hB₁).trans c.P_norm_M) (c.M_le_P.trans (c.P_norm_B₁ hB₁))
      (c.M_le_P.trans c.P_norm_Y) (by rw [c.M_comm]))
  have hle := inf_le_Y (t := t) c.t_sq (B := B₁) (W := W) (P := P) hE (c.W_le_M.trans c.M_le_P)
    hQ c.Y_le_Kp (c.Kp_le_Λ₂.trans c.Λ₂_norm_Y) c.Kp_perfect' c.Kp_comm' hQc c.conj_Y
    (c.B₁Y_inf hB₁)
  exact le_antisymm hle (le_inf c.Y_le_Kp c.Y_le_Kpt)

theorem B₂_inf {A₂ B₁ B₂ : Subgroup G} (hA₂ : A₂ = Λ₂ ⊓ Ast)
    (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G))
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) : B₂ ⊓ B₂ᵍ[t] = Y := by
  refine le_antisymm ?_ (le_inf (c.Y_le_B₂ hB₂) ?_)
  · rw [← c.Kp_inf_Kpt hA₂ hB₁ hB₂]
    exact inf_le_inf (c.B₂_le_Kp hB₂) (conj_mono (c.B₂_le_Kp hB₂) t)
  · have := conj_mono (c.Y_le_B₂ hB₂) t
    rwa [c.conj_Y] at this

theorem N₂_eq_sup' {A₂ B₁ B₂ : Subgroup G} (hA₂ : A₂ = Λ₂ ⊓ Ast)
    (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G))
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    N₂ = (⁅Λ₂, Λ₂⁆ : Subgroup G) ⊔ (⁅Λ₂, Λ₂⁆ : Subgroup G)ᵍ[t] := by
  have hW : W ≤ (⁅Λ₂, Λ₂⁆ : Subgroup G) ⊔ (⁅Λ₂, Λ₂⁆ : Subgroup G)ᵍ[t] :=
    calc W ≤ M := c.W_le_M
      _ = B₂ ⊔ B₂ᵍ[t] := (c.M_eq_sup hA₂ hB₁ hB₂).symm
      _ ≤ (⁅Λ₂, Λ₂⁆ : Subgroup G) ⊔ (⁅Λ₂, Λ₂⁆ : Subgroup G)ᵍ[t] :=
        sup_le_sup (c.B₂_le_Kp hB₂) (conj_mono (c.B₂_le_Kp hB₂) t)
  refine le_antisymm ?_ (sup_le c.Kp_le_N₂ (c.Kpt_le_Λ₂t.trans c.Λ₂t_le_N₂))
  rw [c.N₂_eq_sup]
  exact sup_le le_rfl hW

end Cfg

end ProductLiftsAux

end Part13

section Part14

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc
  mem_centerMod_iff mem_centralizerMod_iff commutator_mem_iff_proj)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux
  (mem_sup_iff_of_le_normalizer mem_sup_iff_of_le_normalizer' Sl2Pair mem_normalizer_of_pow_mem
    le_normalizer_of_commutator_mem conj_inf conj_sup conj_commutator conj_conj_of_mul_self
    conj_eq_of_mem_normalizer card_conj pCoreOf_conj mem_normalizer_of_conj_eq
    mem_normalizer_pCoreOf conj_mono mem_conj_iff)
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_inf mem_normalizer_sup)
open CFSG.LocalAnalysis.EvenBN.TrialityD4 (card_sup_mul_card_inf_eq_D4)

namespace ProductLiftsAux

namespace Cfg

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
  {t : G} {U Y W F M D P N₁ N₂ Λ₁ Λ₂ J₃ J₄ J S Ast : Subgroup G}
  (c : Cfg K t U Y W F M D P N₁ N₂ Λ₁ Λ₂ J₃ J₄ J S Ast)

include c

theorem J_norm_Λ₁ : J ≤ normalizer (Λ₁ : Set G) :=
  le_normalizer_of_odd_card c.sl₁ c.J_norm_N₁ c.J_norm_D c.J_odd

theorem J_norm_Λ₂ : J ≤ normalizer (Λ₂ : Set G) :=
  le_normalizer_of_odd_card c.sl₂ c.J_norm_N₂ c.J_norm_M c.J_odd

theorem J_norm_B₁ {B₁ : Subgroup G} (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G)) :
    J ≤ normalizer (B₁ : Set G) := fun g hg => by
  rw [hB₁]; exact mem_normalizer_pCoreOf (mem_normalizer_commutator_self (c.J_norm_Λ₁ hg))

theorem J_norm_B₂ {B₂ : Subgroup G} (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    J ≤ normalizer (B₂ : Set G) := fun g hg => by
  rw [hB₂]; exact mem_normalizer_pCoreOf (mem_normalizer_commutator_self (c.J_norm_Λ₂ hg))

theorem odd_J₃ : Odd (Nat.card J₃) :=
  c.J_odd.of_dvd_nat (Subgroup.card_dvd_of_le c.J₃_le)

theorem odd_J₄ : Odd (Nat.card J₄) :=
  c.J_odd.of_dvd_nat (Subgroup.card_dvd_of_le c.J₄_le)

theorem M_inf_cen : M ⊓ centralizer (J₄ : Set G) ≤ Y := fun x hx =>
  c.cen_inf (mem_inf.2 ⟨mem_inf.2 ⟨c.M_le_Λ₂.trans c.Λ₂_le_N₂ (mem_inf.1 hx).1, (mem_inf.1 hx).2⟩,
    (mem_inf.1 hx).1⟩)

theorem D_inf_cen : D ⊓ centralizer (J₃ : Set G) = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxD, hxC⟩ := mem_inf.1 hx
  have : x ∈ (N₁ ⊓ centralizer (J₃ : Set G)) ⊓ D :=
    mem_inf.2 ⟨mem_inf.2 ⟨c.D_le_Λ₁.trans c.Λ₁_le_N₁ hxD, hxC⟩, hxD⟩
  rwa [c.compl₁'] at this

theorem T₂_le_B₁ {A₂ B₁ B₂ : Subgroup G} (hA₂ : A₂ = Λ₂ ⊓ Ast)
    (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G))
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) : P ⊓ A₂ ≤ B₁ ⊔ Y := by
  have hA₂Λ : A₂ ≤ Λ₂ := by rw [hA₂]; exact inf_le_left
  refine fixed_le_sup (X := B₁) (Z := M) (S := J₄) ((c.B₁_le_P hB₁).trans c.P_norm_M)
    (c.J₄_le.trans (c.J_norm_B₁ hB₁)) (c.J₄_le.trans c.J_norm_M)
    (c.P_two.to_le (c.B₁_le_P hB₁)) c.odd_J₄ c.M_inf_cen ?_ ?_
  · exact (inf_le_inf_left P hA₂Λ).trans (c.P₂_eq hA₂ hB₁ hB₂).le
  · intro x hx
    have := (mem_inf.1 hx).2
    rw [hA₂] at this
    exact (mem_inf.1 (c.Ast_le (mem_inf.1 this).2)).2

theorem P₁_eq {B₂ : Subgroup G} (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    P ⊓ Λ₁ = B₂ ⊔ D := by
  have h1 : (P ⊓ Λ₁)ᵍ[t] = B₂ᵍ[t] ⊔ D := by
    rw [c.label, c.center_P₂', c.center_P₂, c.Z₂_eq hB₂]
    refine le_antisymm (sup_le (sup_le (c.F_le_D.trans le_sup_right)
      (sup_le le_sup_left (c.W_le_D.trans le_sup_right))) le_sup_right)
      (sup_le ((le_sup_left.trans le_sup_right).trans le_sup_left) le_sup_right)
  have h2 := congrArg (fun X : Subgroup G => Xᵍ[t]) h1
  simp only [c.conj_conj, conj_sup, c.conj_D] at h2
  exact h2

theorem T₁_le_B₂ {A₁ B₂ : Subgroup G} (hA₁ : A₁ = Λ₁ ⊓ centralizer (J₃ : Set G))
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) : P ⊓ A₁ ≤ B₂ := by
  have hA₁Λ : A₁ ≤ Λ₁ := by rw [hA₁]; exact inf_le_left
  refine fixed_le (X := B₂) (Z := D) (S := J₃) ((c.B₂_le_P hB₂).trans c.P_norm_D)
    (c.J₃_le.trans (c.J_norm_B₂ hB₂)) (c.J₃_le.trans c.J_norm_D)
    (c.P_two.to_le (c.B₂_le_P hB₂)) c.odd_J₃ c.D_inf_cen ?_ ?_
  · exact (inf_le_inf_left P hA₁Λ).trans (c.P₁_eq hB₂).le
  · intro x hx
    have := (mem_inf.1 hx).2
    rw [hA₁] at this
    exact (mem_inf.1 this).2

theorem P₂_eq_T₂M {A₂ : Subgroup G} (hA₂ : A₂ = Λ₂ ⊓ Ast) :
    P ⊓ Λ₂ = (P ⊓ A₂) ⊔ M := by
  have hA₂Λ : A₂ ≤ Λ₂ := by rw [hA₂]; exact inf_le_left
  refine le_antisymm (fun x hx => ?_)
    (sup_le (inf_le_inf_left P hA₂Λ) (le_inf c.M_le_P c.M_le_Λ₂))
  obtain ⟨hxP, hxΛ⟩ := mem_inf.1 hx
  obtain ⟨a, ha, m, hm, rfl⟩ := c.levi₂ hA₂ x hxΛ
  have haP : a ∈ P := by
    have := mul_mem hxP (inv_mem (c.M_le_P hm))
    simpa using this
  exact mul_mem (mem_sup_left (mem_inf.2 ⟨haP, ha⟩)) (mem_sup_right hm)

theorem P₁_eq_T₁D {A₁ : Subgroup G} (hA₁ : A₁ = Λ₁ ⊓ centralizer (J₃ : Set G)) :
    P ⊓ Λ₁ = (P ⊓ A₁) ⊔ D := by
  have hA₁Λ : A₁ ≤ Λ₁ := by rw [hA₁]; exact inf_le_left
  refine le_antisymm (fun x hx => ?_)
    (sup_le (inf_le_inf_left P hA₁Λ) (le_inf c.D_le_P c.D_le_Λ₁))
  obtain ⟨hxP, hxΛ⟩ := mem_inf.1 hx
  obtain ⟨a, ha, m, hm, rfl⟩ := levi_decomp c.Λ₁_le_N₁ c.D_le_Λ₁ (inf_le_left.trans c.N₁_norm_D)
    c.compl₁ x hxΛ
  have haP : a ∈ P := by
    have := mul_mem hxP (inv_mem (c.D_le_P hm))
    simpa using this
  have haA : a ∈ A₁ := by
    rw [hA₁]; exact mem_inf.2 ⟨(mem_inf.1 ha).1, (mem_inf.1 (mem_inf.1 ha).2).2⟩
  exact mul_mem (mem_sup_left (mem_inf.2 ⟨haP, haA⟩)) (mem_sup_right hm)

theorem M_inf_T₂ {A₂ : Subgroup G} (hA₂ : A₂ = Λ₂ ⊓ Ast) :
    M ⊓ (P ⊓ A₂) = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxM, hxPA⟩ := mem_inf.1 hx
  have hxA := (mem_inf.1 hxPA).2
  rw [hA₂] at hxA
  have : x ∈ Ast ⊓ M := mem_inf.2 ⟨(mem_inf.1 hxA).2, hxM⟩
  rwa [c.compl₂'] at this

theorem D_inf_T₁ {A₁ : Subgroup G} (hA₁ : A₁ = Λ₁ ⊓ centralizer (J₃ : Set G)) :
    D ⊓ (P ⊓ A₁) = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxD, hxPA⟩ := mem_inf.1 hx
  have hxA := (mem_inf.1 hxPA).2
  rw [hA₁] at hxA
  have : x ∈ (N₁ ⊓ centralizer (J₃ : Set G)) ⊓ D :=
    mem_inf.2 ⟨mem_inf.2 ⟨c.Λ₁_le_N₁ (mem_inf.1 hxA).1, (mem_inf.1 hxA).2⟩, hxD⟩
  rwa [c.compl₁'] at this

theorem card_T₂ {A₂ : Subgroup G} (hA₂ : A₂ = Λ₂ ⊓ Ast) :
    Nat.card (P ⊓ A₂ : Subgroup G) = Nat.card K := by
  have h1 := card_sup_mul_card_inf_eq_D4 (A := M) (B := P ⊓ A₂) (inf_le_left.trans c.P_norm_M)
  rw [c.M_inf_T₂ hA₂, Subgroup.card_bot (G := G), mul_one, sup_comm, ← c.P₂_eq_T₂M hA₂,
    c.card_P₂, c.card_M] at h1
  have hq : 0 < Nat.card K ^ 10 := pow_pos Nat.card_pos 10
  refine Nat.eq_of_mul_eq_mul_left hq ?_
  rw [← h1]; ring

theorem card_T₁ {A₁ : Subgroup G} (hA₁ : A₁ = Λ₁ ⊓ centralizer (J₃ : Set G)) :
    Nat.card (P ⊓ A₁ : Subgroup G) = Nat.card K := by
  have h1 := card_sup_mul_card_inf_eq_D4 (A := D) (B := P ⊓ A₁) (inf_le_left.trans c.P_norm_D)
  rw [c.D_inf_T₁ hA₁, Subgroup.card_bot (G := G), mul_one, sup_comm, ← c.P₁_eq_T₁D hA₁,
    c.card_P₁, c.card_D] at h1
  have hq : 0 < Nat.card K ^ 10 := pow_pos Nat.card_pos 10
  refine Nat.eq_of_mul_eq_mul_left hq ?_
  rw [← h1]; ring

theorem card_B₂ {A₂ B₁ B₂ : Subgroup G} (hA₂ : A₂ = Λ₂ ⊓ Ast)
    (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G))
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) : Nat.card B₂ = Nat.card K ^ 7 := by
  have hN : B₂ᵍ[t] ≤ normalizer (B₂ : Set G) := fun g hg =>
    c.N₂_norm_B₂ hB₂ ((c.B₂t_le_M hB₂).trans (c.M_le_Λ₂.trans c.Λ₂_le_N₂) hg)
  have h1 := card_sup_mul_card_inf_eq_D4 hN
  rw [c.M_eq_sup hA₂ hB₁ hB₂, c.B₂_inf hA₂ hB₁ hB₂, card_conj, c.card_M, c.card_Y] at h1
  have h2 : Nat.card B₂ * Nat.card B₂ = Nat.card K ^ 7 * Nat.card K ^ 7 :=
    h1.symm.trans (by ring)
  exact Nat.mul_self_inj.1 h2

theorem B₁_le_T₂B₂ {A₂ B₁ B₂ : Subgroup G} (hA₂ : A₂ = Λ₂ ⊓ Ast)
    (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G))
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) : B₁ ≤ (P ⊓ A₂) ⊔ B₂ := by
  intro b hb
  obtain ⟨a, ha, m, hm, rfl⟩ := c.levi₂ hA₂ b (c.B₁_le_Λ₂ hA₂ hB₁ hB₂ hb)
  have haP : a ∈ P := by
    have := mul_mem (c.B₁_le_P hB₁ hb) (inv_mem (c.M_le_P hm))
    simpa using this
  have haT : a ∈ P ⊓ A₂ := mem_inf.2 ⟨haP, ha⟩
  have hB₁Y : B₁ ≤ normalizer (Y : Set G) := (c.B₁_le_P hB₁).trans c.P_norm_Y
  obtain ⟨b', hb', y, hy, hay⟩ :=
    (mem_sup_iff_of_le_normalizer hB₁Y).1 (c.T₂_le_B₁ hA₂ hB₁ hB₂ haT)
  have hymB₁ : y * m ∈ B₁ := by
    have h1 := mul_mem (inv_mem hb') hb
    have e : b'⁻¹ * (a * m) = y * m := by rw [hay]; group
    rwa [e] at h1
  have hymB₂ : y * m ∈ B₂ :=
    c.α_le_B₂ hA₂ hB₁ hB₂ (mem_inf.2 ⟨hymB₁, mul_mem (c.Y_le_M hy) hm⟩)
  have hmB : m ∈ B₂ := by
    have := mul_mem (inv_mem (c.Y_le_B₂ hB₂ hy)) hymB₂
    rwa [inv_mul_cancel_left] at this
  exact mul_mem (mem_sup_left haT) (mem_sup_right hmB)

theorem final_eq {A₁ A₂ B₁ B₂ : Subgroup G} (hA₁ : A₁ = Λ₁ ⊓ centralizer (J₃ : Set G))
    (hA₂ : A₂ = Λ₂ ⊓ Ast)
    (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G))
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    (P ⊓ A₁) ⊔ B₁ ⊔ Y = (P ⊓ A₂) ⊔ B₂ := by
  have hle : (P ⊓ A₁) ⊔ B₁ ⊔ Y ≤ (P ⊓ A₂) ⊔ B₂ :=
    sup_le (sup_le ((c.T₁_le_B₂ hA₁ hB₂).trans le_sup_right) (c.B₁_le_T₂B₂ hA₂ hB₁ hB₂))
      ((c.Y_le_B₂ hB₂).trans le_sup_right)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hT₂N : P ⊓ A₂ ≤ normalizer (B₂ : Set G) := fun g hg =>
    c.N₂_norm_B₂ hB₂ (c.P_le_N₂ (mem_inf.1 hg).1)
  have h2 := card_sup_mul_card_inf_eq_D4 hT₂N
  have hinf₂ : B₂ ⊓ (P ⊓ A₂) = ⊥ :=
    eq_bot_iff.2 (fun x hx => by
      rw [← c.M_inf_T₂ hA₂]
      exact mem_inf.2 ⟨c.B₂_le_M hB₂ (mem_inf.1 hx).1, (mem_inf.1 hx).2⟩)
  rw [hinf₂, Subgroup.card_bot (G := G), mul_one, sup_comm, c.card_B₂ hA₂ hB₁ hB₂,
    c.card_T₂ hA₂] at h2
  have hB₁Y : B₁ ⊔ Y ≤ D := sup_le (c.B₁_le_D hB₁) (c.Y_le_W.trans c.W_le_D)
  have hT₁N : P ⊓ A₁ ≤ normalizer ((B₁ ⊔ Y : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_sup (c.P_norm_B₁ hB₁ (mem_inf.1 hg).1) (c.P_norm_Y (mem_inf.1 hg).1)
  have h3 := card_sup_mul_card_inf_eq_D4 hT₁N
  have hinf₁ : (B₁ ⊔ Y) ⊓ (P ⊓ A₁) = ⊥ :=
    eq_bot_iff.2 (fun x hx => by
      rw [← c.D_inf_T₁ hA₁]
      exact mem_inf.2 ⟨hB₁Y (mem_inf.1 hx).1, (mem_inf.1 hx).2⟩)
  have hBY : Nat.card (B₁ ⊔ Y : Subgroup G) = Nat.card K ^ 7 := by
    have h4 := card_sup_mul_card_inf_eq_D4 (A := Y) (B := B₁)
      ((c.B₁_le_P hB₁).trans c.P_norm_Y)
    rw [sup_comm, inf_comm, c.card_B₁_inf_Y hB₁, c.card_Y, c.card_B₁ hB₁] at h4
    have hq : 0 < Nat.card K ^ 3 := pow_pos Nat.card_pos 3
    exact Nat.eq_of_mul_eq_mul_right hq (h4.trans (by ring))
  rw [hinf₁, Subgroup.card_bot (G := G), mul_one, sup_comm, hBY, c.card_T₁ hA₁] at h3
  rw [sup_assoc]
  exact (h2.trans h3.symm).le

end Cfg

end ProductLiftsAux

end Part14

section Part15

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc
  mem_centerMod_iff mem_centralizerMod_iff commutator_mem_iff_proj)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups
open CFSG.ABGLocalTools (IsSylowOf)

namespace ProductLiftsAux

namespace Cfg

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
  {t : G} {U Y W F M D P N₁ N₂ Λ₁ Λ₂ J₃ J₄ J S Ast : Subgroup G}

theorem master (c : Cfg K t U Y W F M D P N₁ N₂ Λ₁ Λ₂ J₃ J₄ J S Ast) :
    (N₂ = (⁅Λ₂, Λ₂⁆ ⊔ Y) ⊔ (⁅Λ₂, Λ₂⁆ ⊔ Y)ᵍ[t] ∧
      (⁅Λ₂, Λ₂⁆ ⊔ Y) ⊓ (⁅Λ₂, Λ₂⁆ ⊔ Y)ᵍ[t] = Y ∧
      ⁅⁅Λ₂, Λ₂⁆ ⊔ Y, (⁅Λ₂, Λ₂⁆ ⊔ Y)ᵍ[t]⁆ ≤ Y ∧
      ⁅Λ₂, Λ₂⁆ ⊔ Y = (Λ₂ ⊓ Ast) ⊔ pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G) ∧
      pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G) ⊔ (pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G))ᵍ[t] = M ∧
      pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G) ⊓ (pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G))ᵍ[t] = Y) ∧
    (P ⊓ (Λ₁ ⊓ centralizer (J₃ : Set G))) ⊔ pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G) ⊔ Y =
      (P ⊓ (Λ₂ ⊓ Ast)) ⊔ pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G) := by
  obtain ⟨B₁, hB₁⟩ : ∃ B₁ : Subgroup G, B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G) := ⟨_, rfl⟩
  obtain ⟨B₂, hB₂⟩ : ∃ B₂ : Subgroup G, B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G) := ⟨_, rfl⟩
  obtain ⟨A₁, hA₁⟩ : ∃ A₁ : Subgroup G, A₁ = Λ₁ ⊓ centralizer (J₃ : Set G) := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A₂ : Subgroup G, A₂ = Λ₂ ⊓ Ast := ⟨_, rfl⟩
  rw [← hB₁, ← hB₂, ← hA₁, ← hA₂, c.derived_eq]
  exact ⟨⟨c.N₂_eq_sup' hA₂ hB₁ hB₂, c.Kp_inf_Kpt hA₂ hB₁ hB₂, c.Kp_comm', c.Kp_eq_sup hA₂ hB₂,
    c.M_eq_sup hA₂ hB₁ hB₂, c.B₂_inf hA₂ hB₁ hB₂⟩, c.final_eq hA₁ hA₂ hB₁ hB₂⟩

end Cfg

end ProductLiftsAux

end Part15

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure (BarM barMap barSub)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer (ExactClosure)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (FieldAlternative ProductAlternative)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

open CFSG.LocalAnalysis.EvenBN.TrialityD4 (card_sup_mul_card_inf_eq_D4)

private theorem cfg_of_lane (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) {Λ₁ Λ₂ : Subgroup G}
    (hL : Labelled d t Λ₁ Λ₂) :
    ProductLiftsAux.Cfg K t (yamadaU₁ d t) (yamadaY₂ d t) (yamadaW₃ d t) (yamadaF₅ d t)
      (yamadaM₆ d t) (yamadaD₇ d t) (yamadaP d t) (yamadaN₁ d t) (yamadaN₂ d t) Λ₁ Λ₂ d.J₃ d.J₄
      d.J d.S hp.Astar := by
  have ht2 : t * t = 1 := h.t_mul_t
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  have hD := hQ.doubling
  have hKN₂ : yamadaK₂ d ≤ normalizer (yamadaM₆ d t : Set G) :=
    (commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb) :
        yamadaK₂ d ≤ L ⊓ normalizer (d.Y : Set G)).trans
      (h.normalizer_L_le_yamadaD₇_M₆ hW d hK hQ).2
  have hKN₁ : yamadaK₁ d ≤ normalizer (yamadaD₇ d t : Set G) :=
    (commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb) :
        yamadaK₁ d ≤ L ⊓ normalizer (d.U : Set G)).trans
      (h.normalizer_L_le_yamadaD₇_M₆ hW d hK hQ).1
  have hN₂M : yamadaN₂ d t ≤ normalizer (yamadaM₆ d t : Set G) :=
    yamadaN₂_le_normalizer d t hKN₂
  have hN₁D : yamadaN₁ d t ≤ normalizer (yamadaD₇ d t : Set G) :=
    yamadaN₁_le_normalizer d t hKN₁
  have hNN₁ : normalizer (yamadaD₇ d t : Set G) ≤ normalizer (yamadaN₁ d t : Set G) := by
    have hN : ((yamadaN₁ d t).subgroupOf (normalizer (yamadaD₇ d t : Set G))).Normal :=
      Common.RankOneLayerRadical.normal_subgroupOf_normalClosureInNormalizer hKN₁
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hN₁D).1 hN
  have hNN₂ : normalizer (yamadaM₆ d t : Set G) ≤ normalizer (yamadaN₂ d t : Set G) := by
    have hN : ((yamadaN₂ d t).subgroupOf (normalizer (yamadaM₆ d t : Set G))).Normal :=
      Common.RankOneLayerRadical.normal_subgroupOf_normalClosureInNormalizer hKN₂
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hN₂M).1 hN
  have h57 := h.yamada_5_57_1 hW d hK hQ
  have h572 := h.yamada_5_57_2 hW d hK hQ
  have h551 := h.yamada_5_55_1 hW d hK hQ
  have hcD := h.card_yamadaD₇ hW d hK hQ
  have hser := h.yamada_series_card hW d hK hQ
  have hserc := h.yamada_series_inf_centralizer hW d hK hQ
  have h51 := h.yamada_5_51 hW d hK hQ
  have hPDM := h.yamadaP_le_normalizer_D₇_M₆ hW d hK hQ
  have h3 := h.yamada_7_3 hW d hK hQ hp hL.fac₂
  have h4 := h.yamada_7_4 hW d hK hQ hp hL.fac₂
  have h9 := h.yamada_7_9 hW d hK hQ hp hL
  have h6 := h.yamada_7_6 hW d hK hQ hp hL.fac₁
  have hcen := h.yamadaN₂_centers hW d hK hQ hp.sylow₂ (hp.exact₂.choose_spec.1)
  have hcards := d.cards
  have h3d := d.yamada_3_12_commutators hK4
  have hPmul : ∀ p ∈ yamadaP d t, ∃ m ∈ yamadaM₆ d t, ∃ d' ∈ yamadaD₇ d t, p = m * d' := by
    intro p hp
    have : p ∈ ((yamadaM₆ d t : Set G) * (yamadaD₇ d t : Set G)) := by
      rw [← h.yamadaP_eq_mul hW d hK hQ]; exact hp
    obtain ⟨m, hm, d', hd', rfl⟩ := Set.mem_mul.1 this
    exact ⟨m, hm, d', hd', rfl⟩
  have hS_le : d.S ≤ yamadaP d t := by rw [← hserc.2.2.2.2.2]; exact inf_le_left
  have hSC : d.S ≤ centralizer ({t} : Set G) := fun x hx => by
    have hx' : x ∈ yamadaP d t ⊓ centralizer ({t} : Set G) := by
      rw [hserc.2.2.2.2.2]; exact hx
    exact (mem_inf.1 hx').2
  have hS_fix : ∀ s ∈ d.S, t * s * t = s := by
    intro s hs
    have h1 : s * t = t * s := mem_centralizer_singleton_iff.1 (hSC hs)
    calc t * s * t = t * (s * t) := by rw [mul_assoc]
      _ = t * (t * s) := by rw [h1]
      _ = s := by rw [← mul_assoc, ht2, one_mul]
  have hPY : yamadaP d t ≤ normalizer (yamadaY₂ d t : Set G) := fun g hg => by
    have := ProductLiftsAux.mem_normalizer_commutator_self (hPDM.2 hg)
    rwa [h551.2.2] at this
  have hS_card : Nat.card K ^ 2 * Nat.card (yamadaY₂ d t) ≤
      Nat.card (⁅d.S, d.S⁆ ⊔ yamadaY₂ d t : Subgroup G) := by
    have hFS : ⁅d.S, d.S⁆ ≤ d.S := commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    have hFN : ⁅d.S, d.S⁆ ≤ normalizer (yamadaY₂ d t : Set G) := hFS.trans (hS_le.trans hPY)
    have h1 := card_sup_mul_card_inf_eq_D4 (A := yamadaY₂ d t) (B := ⁅d.S, d.S⁆) hFN
    have hle : yamadaY₂ d t ⊓ ⁅d.S, d.S⁆ ≤ d.Y := by
      rw [← hserc.2.1]; exact inf_le_inf_left _ (hFS.trans hSC)
    have hinf : Nat.card (yamadaY₂ d t ⊓ ⁅d.S, d.S⁆ : Subgroup G) ≤ Nat.card K ^ 2 := by
      rw [← hcards.2.1]; exact Subgroup.card_le_of_le hle
    have hF : Nat.card (⁅d.S, d.S⁆ : Subgroup G) = Nat.card K ^ 4 := by
      rw [h3d.2.2.1]; exact hcards.2.2.2.2.1
    rw [hF, hser.2.1] at h1
    rw [sup_comm]
    have hq : 0 < Nat.card K ^ 2 := pow_pos Nat.card_pos 2
    refine Nat.le_of_mul_le_mul_right ?_ hq
    calc Nat.card K ^ 2 * Nat.card (yamadaY₂ d t) * Nat.card K ^ 2
        = Nat.card (yamadaY₂ d t ⊔ ⁅d.S, d.S⁆ : Subgroup G) *
          Nat.card (yamadaY₂ d t ⊓ ⁅d.S, d.S⁆ : Subgroup G) := by rw [h1, hser.2.1]; ring
      _ ≤ Nat.card (yamadaY₂ d t ⊔ ⁅d.S, d.S⁆ : Subgroup G) * Nat.card K ^ 2 :=
        Nat.mul_le_mul_left _ hinf
  exact
    { t_sq := ht2
      K_four := hQ.four_le
      U_le_Y := le_sup_left
      Y_le_W := (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t).trans
        (h.yamadaW₃_facts hW d hK hD).2.2.2.1
      W_le_F := Setup.Q44.W₃_le_F₅ d t
      F_le_M := h572.1
      F_le_D := h572.2.1
      M_le_P := h572.2.2.1
      D_le_P := h572.2.2.2.1
      M_inf_D := h572.2.2.2.2.2.1
      P_mul := hPmul
      P_comm := fun x hx y hy => (h572.2.2.2.2.2.2 x hx y hy).2
      M_comm := h551.2.2
      D_comm := h551.1.2
      P_center := h6.2.2.1.1
      card_U := hser.1
      card_Y := hser.2.1
      card_W := hser.2.2.1
      card_F := hser.2.2.2.1
      card_M := hser.2.2.2.2.1
      card_D := hcD
      card_P := hser.2.2.2.2.2
      P_norm_M := hPDM.2
      P_norm_D := hPDM.1
      N₁_norm_D := hN₁D
      N₂_norm_M := hN₂M
      N₂_norm_W := hcen.1
      t_norm_M := SeriesN2Aux.t_mem_normalizer_M₆ hW h d hK hQ
      t_norm_D := h51.2.2.2.1
      t_norm_W := Setup.Q44.t_mem_normalizer_W₃ hW h d hK hD
      t_norm_P := SeriesN2Aux.t_mem_normalizer_P hW h d hK hQ
      sylow₁ := hp.sylow₁
      sylow₂ := hp.sylow₂
      fac₁ := hL.fac₁
      fac₂ := hL.fac₂
      label := hL.label
      compl₁ := hp.compl₁.1
      compl₁' := hp.compl₁.2.1
      Ast_le := hp.Astar_spec.le_cen
      compl₂ := hp.Astar_spec.sup_eq
      compl₂' := hp.Astar_spec.inf_eq
      cen_inf := hp.inf₂
      J_odd := odd_card_J d
      J₃_le := J₃_le_J d
      J₄_le := J₄_le_J d
      J_norm_N₁ := (h.J_le_normalizer_yamadaD₇ hW d hK hQ).trans hNN₁
      J_norm_N₂ := (h.J_le_normalizer_yamadaM₆ hW d hK hQ).trans hNN₂
      J_norm_D := h.J_le_normalizer_yamadaD₇ hW d hK hQ
      J_norm_M := h.J_le_normalizer_yamadaM₆ hW d hK hQ
      rel_center := h3.1.1
      center_sup := h3.1.2.1
      hat_sup := h3.2.1.1
      hat_levi := h3.2.2.1.1
      center_pcore := h3.2.2.1.2
      center_P₂ := h3.2.2.2
      center_P₂' := h4.1.2
      Kp_perfect := h4.2.1
      Kp_comm := h4.2.2
      Zt_pcore := h9.1.2.2.2.2.2.1
      Z_sup := h9.1.2.2.2.2.2.2.1
      Z_inf := h9.1.2.2.2.2.2.2.2
      center_N₂_Y := hcen.2.1
      center_N₂_W := hcen.2.2.1
      S_le_P := hS_le
      S_fix := hS_fix
      S_card := hS_card }

theorem yamada_7_11 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) {Λ₁ Λ₂ : Subgroup G}
    (hL : Labelled d t Λ₁ Λ₂) :
    (yamadaN₂ d t = derivedMod (yamadaY₂ d t) Λ₂ ⊔ (derivedMod (yamadaY₂ d t) Λ₂)ᵍ[t] ∧
      derivedMod (yamadaY₂ d t) Λ₂ ⊓ (derivedMod (yamadaY₂ d t) Λ₂)ᵍ[t] = yamadaY₂ d t ∧
      ⁅derivedMod (yamadaY₂ d t) Λ₂, (derivedMod (yamadaY₂ d t) Λ₂)ᵍ[t]⁆ ≤ yamadaY₂ d t ∧
      derivedMod (yamadaY₂ d t) Λ₂ = leviFactor₂ hp.Astar Λ₂ ⊔ pCoreOf 2 (derived₁ Λ₂) ∧
      pCoreOf 2 (derived₁ Λ₂) ⊔ (pCoreOf 2 (derived₁ Λ₂))ᵍ[t] = yamadaM₆ d t ∧
      pCoreOf 2 (derived₁ Λ₂) ⊓ (pCoreOf 2 (derived₁ Λ₂))ᵍ[t] = yamadaY₂ d t) ∧
    (yamadaP d t ⊓ leviFactor₁ d Λ₁) ⊔ pCoreOf 2 (derived₁ Λ₁) ⊔ yamadaY₂ d t =
      (yamadaP d t ⊓ leviFactor₂ hp.Astar Λ₂) ⊔ pCoreOf 2 (derived₁ Λ₂) :=
  ProductLiftsAux.Cfg.master (cfg_of_lane hW h d hK hQ hp hL)

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
