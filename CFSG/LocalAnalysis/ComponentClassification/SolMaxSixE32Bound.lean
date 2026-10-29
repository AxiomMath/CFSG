module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE32Perm
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixGenBase
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.ComponentClassification.SolMax.Sig36.E32

open Equiv Perm Subgroup

namespace Bound

private def w₁ : Perm (Fin 9) := swap 0 2 * swap 1 3

private def w₂ : Perm (Fin 9) := swap 2 4 * swap 3 5

private def τ₀ : Perm (Fin 9) := swap 0 1

private def ζ₀ : Perm (Fin 9) := w₁ * w₂

private def κ₀ : Perm (Fin 9) := τ₀ * ζ₀ * τ₀⁻¹ * ζ₀⁻¹

private theorem w₁_mem : w₁ ∈ centralizer ({σ₀} : Set (Perm (Fin 9))) := by
  rw [mem_centralizer_singleton_iff]
  decide

private theorem w₂_mem : w₂ ∈ centralizer ({σ₀} : Set (Perm (Fin 9))) := by
  rw [mem_centralizer_singleton_iff]
  decide

private theorem τ₀_mem : τ₀ ∈ centralizer ({σ₀} : Set (Perm (Fin 9))) := by
  rw [mem_centralizer_singleton_iff]
  decide

private theorem w₁_mul_self : w₁ * w₁ = 1 := by decide

private theorem w₂_mul_self : w₂ * w₂ = 1 := by decide

private theorem ζ₀_pow_three : ζ₀ ^ 3 = 1 := by decide

private theorem κ₀_mul_self : κ₀ * κ₀ = 1 := by decide

private theorem κ₀_ne_one : κ₀ ≠ 1 := by decide

private theorem σ₀_eq_permOf : σ₀ = SixGen.permOf [(0, 1), (2, 3), (4, 5)] := by decide

private theorem card_centralizer_σ₀ :
    Nat.card (centralizer ({σ₀} : Set (Perm (Fin 9)))) = 288 := by
  rw [σ₀_eq_permOf]
  exact SixGen.card_centralizer_u₀

private theorem card_le_of_le_centralizer {T : Subgroup (Perm (Fin 9))}
    (hT : T ≤ centralizer ({σ₀} : Set (Perm (Fin 9)))) (hT2 : IsPGroup 2 T) :
    Nat.card T ≤ 32 := by
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 2)).mp hT2
  have hdvd : Nat.card T ∣ 288 := card_centralizer_σ₀ ▸ Subgroup.card_dvd_of_le hT
  by_contra hlt
  push Not at hlt
  have hb6 : 6 ≤ b := by
    by_contra h
    push Not at h
    interval_cases b <;> omega
  have h64 : 2 ^ 6 ∣ 288 := (pow_dvd_pow 2 hb6).trans (hb ▸ hdvd)
  omega

private theorem card_map_eq_of_card_gt {G' : Type*} [Group G'] [Finite G']
    (π : G' →* Perm (Fin 9)) (hrange : π.range = centralizer ({σ₀} : Set (Perm (Fin 9))))
    (hker : ∀ R : Subgroup G', R ≤ π.ker → IsPGroup 2 R → Nat.card R ≤ 2)
    {R : Subgroup G'} (hR : IsPGroup 2 R) (hlt : 32 < Nat.card R) :
    Nat.card (R.map π) = 32 := by
  have h1 := Subgroup.card_ker_mul_card_range (π.domRestrict R)
  rw [MonoidHom.domRestrict_range] at h1
  have hker' : Nat.card (π.domRestrict R).ker ≤ 2 := by
    have h2 := hker ((π.domRestrict R).ker.map R.subtype) ?_ ?_
    · rwa [Subgroup.card_subtype] at h2
    · rintro _ ⟨y, hy, rfl⟩
      exact hy
    · exact (hR.to_subgroup (π.domRestrict R).ker).map R.subtype
  have hle : R.map π ≤ centralizer ({σ₀} : Set (Perm (Fin 9))) :=
    hrange ▸ Subgroup.map_le_range π R
  have h3 := card_le_of_le_centralizer hle (hR.map π)
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 2)).mp (hR.map π)
  have h4 : Nat.card (π.domRestrict R).ker * Nat.card (R.map π) ≤ 2 * Nat.card (R.map π) :=
    Nat.mul_le_mul_right _ hker'
  have h5 : 16 < Nat.card (R.map π) := by omega
  have hb5 : b ≤ 5 := by
    by_contra h
    push Not at h
    have : 2 ^ 6 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h
    omega
  interval_cases b <;> omega

private theorem isPGroup_zpowers_of_mul_self {M : Type*} [Group M] {a : M} (ha : a * a = 1) :
    IsPGroup 2 (Subgroup.zpowers a) := by
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ha)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

open scoped Pointwise in
private theorem exists_conj_le_of_max {M : Type*} [Group M] [Finite M] {H Sc B : Subgroup M}
    (hSH : Sc ≤ H) (hS2 : IsPGroup 2 Sc) (hBH : B ≤ H) (hB2 : IsPGroup 2 B)
    (hmax : ∀ T : Subgroup M, T ≤ H → IsPGroup 2 T → Nat.card T ≤ Nat.card Sc) :
    ∃ h ∈ H, ∀ b ∈ B, h * b * h⁻¹ ∈ Sc := by
  have hScard : Nat.card Sc = 2 ^ (Nat.card H).factorization 2 := by
    apply le_antisymm
    · obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp hS2
      have hdvd : 2 ^ a ∣ Nat.card H := ha ▸ Subgroup.card_dvd_of_le hSH
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
      rw [ha]
      exact Nat.pow_le_pow_right (by norm_num) this
    · obtain ⟨P⟩ : Nonempty (Sylow 2 H) := Sylow.nonempty
      have h1 := hmax ((P : Subgroup H).map H.subtype) (Subgroup.map_subtype_le _)
        (P.isPGroup'.map H.subtype)
      rwa [Subgroup.card_subtype, Sylow.card_eq_multiplicity] at h1
  have hS₁ : Nat.card (Sc.subgroupOf H) = 2 ^ (Nat.card H).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hSH).toEquiv, hScard]
  have hB₁ : IsPGroup 2 (B.subgroupOf H) := hB2.of_equiv (subgroupOfEquivOfLe hBH).symm
  obtain ⟨T, hT⟩ := hB₁.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H T (Sylow.ofCard _ hS₁)
  refine ⟨h, h.2, fun b hb => ?_⟩
  have key : ((h • T : Sylow 2 H) : Subgroup H) = Sc.subgroupOf H := by
    rw [hh, Sylow.coe_ofCard]
  rw [Sylow.coe_subgroup_smul] at key
  have h1 : MulAut.conj h • (⟨b, hBH hb⟩ : H) ∈ MulAut.conj h • (T : Subgroup H) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hT (show (⟨b, hBH hb⟩ : H) ∈ B.subgroupOf H from hb))
  rw [key] at h1
  simpa [MulAut.smul_def, MulAut.conj_apply, mem_subgroupOf] using h1

private theorem mem_map_of_mul_self_eq_one {G' : Type*} [Group G'] [Finite G']
    (π : G' →* Perm (Fin 9)) (hrange : π.range = centralizer ({σ₀} : Set (Perm (Fin 9))))
    {F : Subgroup G'} [F.Normal] {R : Subgroup G'} (hRF : R ≤ F) (hR : IsPGroup 2 R)
    (hR32 : Nat.card (R.map π) = 32) {w : Perm (Fin 9)}
    (hw : w ∈ centralizer ({σ₀} : Set (Perm (Fin 9)))) (hw2 : w * w = 1) : w ∈ F.map π := by
  have hRle : R.map π ≤ centralizer ({σ₀} : Set (Perm (Fin 9))) :=
    hrange ▸ Subgroup.map_le_range π R
  obtain ⟨z, hz, hzw⟩ := exists_conj_le_of_max (H := centralizer ({σ₀} : Set (Perm (Fin 9))))
    (Sc := R.map π) (B := zpowers w) hRle (hR.map π) (zpowers_le.mpr hw)
    (isPGroup_zpowers_of_mul_self hw2)
    (fun T hT hT2 => hR32 ▸ card_le_of_le_centralizer hT hT2)
  obtain ⟨r, hr, hrz⟩ := hzw w (mem_zpowers w)
  obtain ⟨g, hg⟩ : z ∈ π.range := hrange ▸ hz
  refine ⟨g⁻¹ * r * g, ?_, ?_⟩
  · have := Subgroup.Normal.conj_mem (inferInstance : F.Normal) r (hRF hr) g⁻¹
    simpa using this
  · rw [map_mul, map_mul, map_inv, hg, hrz]
    group

private theorem mem_of_pow_two_pow_mem {M : Type*} [Group M] {ζ : M} (h3 : ζ ^ 3 = 1)
    {K : Subgroup M} {k : ℕ} (hk : ζ ^ (2 ^ k) ∈ K) : ζ ∈ K := by
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left _ (by norm_num)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num)
  have : ζ = (ζ ^ (2 ^ k)) ^ m := by
    rw [← pow_mul, pow_eq_pow_mod _ h3, hm, pow_one]
  rw [this]
  exact pow_mem hk m

private theorem two_power_mem_core {G' : Type*} [Group G'] {E₁ E₂ : Subgroup G'}
    (h₁ : IsPGroup 2 E₁) (h₂ : IsPGroup 2 E₂) (hN₂ : (E₂ ⊔ pPrimeCore 2 G').Normal) {f : G'}
    (hf : f ∈ (E₁ ⊔ pPrimeCore 2 G') ⊔ (E₂ ⊔ pPrimeCore 2 G')) :
    ∃ k : ℕ, f ^ (2 ^ k) ∈ pPrimeCore 2 G' := by
  set O := pPrimeCore 2 G' with hO
  haveI : O.Normal := pPrimeCore_normal
  set mk : G' →* G' ⧸ O := QuotientGroup.mk' O with hmk
  have hN : (E₂.map mk).Normal := by
    have : (E₂ ⊔ O).map mk = E₂.map mk := by
      rw [Subgroup.map_sup, hmk, QuotientGroup.map_mk'_self, sup_bot_eq]
    rw [← this]
    exact Subgroup.Normal.map hN₂ mk (QuotientGroup.mk'_surjective O)
  have hP : IsPGroup 2 (E₁.map mk ⊔ E₂.map mk : Subgroup (G' ⧸ O)) :=
    (h₁.map mk).to_sup_of_normal_right (h₂.map mk)
  have hmem : mk f ∈ (E₁.map mk ⊔ E₂.map mk : Subgroup (G' ⧸ O)) := by
    have h1 : mk f ∈ ((E₁ ⊔ O) ⊔ (E₂ ⊔ O)).map mk := Subgroup.mem_map_of_mem mk hf
    have h2 : ((E₁ ⊔ O) ⊔ (E₂ ⊔ O)).map mk = E₁.map mk ⊔ E₂.map mk := by
      simp only [Subgroup.map_sup, hmk, QuotientGroup.map_mk'_self, sup_bot_eq]
    rwa [h2] at h1
  obtain ⟨k, hk⟩ := hP ⟨mk f, hmem⟩
  refine ⟨k, ?_⟩
  have : mk (f ^ (2 ^ k)) = 1 := by
    have := congrArg Subtype.val hk
    simpa [map_pow] using this
  exact (QuotientGroup.eq_one_iff _).mp this

private def conjAut {X : Type} [Group X] {G : Subgroup X} {n : X}
    (hn : ∀ g ∈ G, n * g * n⁻¹ ∈ G) (hn' : ∀ g ∈ G, n⁻¹ * g * n ∈ G) : ↥G ≃* ↥G where
  toFun g := ⟨n * g * n⁻¹, hn g g.2⟩
  invFun g := ⟨n⁻¹ * g * n, hn' g g.2⟩
  left_inv g := by ext; simp [mul_assoc]
  right_inv g := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

end Bound

section Bound

open Bound

theorem card_le_of_normal_mod_O {G' : Type*} [Group G'] [Finite G']
    (π : G' →* Perm (Fin 9)) (hrange : π.range = centralizer ({σ₀} : Set (Perm (Fin 9))))
    (hker : ∀ R : Subgroup G', R ≤ π.ker → IsPGroup 2 R → Nat.card R ≤ 2)
    {F : Subgroup G'} [F.Normal] (hF : ∀ f ∈ F, ∃ k : ℕ, f ^ (2 ^ k) ∈ pPrimeCore 2 G')
    {R : Subgroup G'} (hRF : R ≤ F) (hR : IsPGroup 2 R) : Nat.card R ≤ 32 := by
  by_contra hlt
  push Not at hlt
  have h32 := card_map_eq_of_card_gt π hrange hker hR hlt
  have hζF : ζ₀ ∈ F.map π :=
    mul_mem (mem_map_of_mul_self_eq_one π hrange hRF hR h32 w₁_mem w₁_mul_self)
      (mem_map_of_mul_self_eq_one π hrange hRF hR h32 w₂_mem w₂_mul_self)
  obtain ⟨f, hfF, hfζ⟩ := hζF
  obtain ⟨k, hk⟩ := hF f hfF
  have hpow : ζ₀ ^ (2 ^ k) ∈ (pPrimeCore 2 G').map π :=
    ⟨f ^ (2 ^ k), hk, by rw [map_pow, hfζ]⟩
  have hζO : ζ₀ ∈ (pPrimeCore 2 G').map π := mem_of_pow_two_pow_mem ζ₀_pow_three hpow
  obtain ⟨g, hg⟩ : τ₀ ∈ π.range := hrange ▸ τ₀_mem
  have hconj : τ₀ * ζ₀ * τ₀⁻¹ ∈ (pPrimeCore 2 G').map π := by
    obtain ⟨o, ho, hoζ⟩ := hζO
    refine ⟨g * o * g⁻¹, Subgroup.Normal.conj_mem pPrimeCore_normal o ho g, ?_⟩
    rw [map_mul, map_mul, map_inv, hg, hoζ]
  have hκ : κ₀ ∈ (pPrimeCore 2 G').map π := mul_mem hconj (inv_mem hζO)
  have hord : orderOf κ₀ = 2 := orderOf_eq_prime (by rw [sq]; exact κ₀_mul_self) κ₀_ne_one
  have hdvd : 2 ∣ Nat.card ((pPrimeCore 2 G').map π) := by
    have := Subgroup.orderOf_dvd_natCard _ hκ
    rwa [hord] at this
  have hdvdO : 2 ∣ Nat.card (pPrimeCore 2 G') := hdvd.trans (Subgroup.card_map_dvd _ π)
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 G')) := pPrimeCore_coprime_card
  exact absurd (Nat.Coprime.eq_one_of_dvd hcop hdvdO) (by norm_num)

theorem conj_of_normal_mod_O {G' : Type*} [Group G'] [Finite G']
    (π : G' →* Perm (Fin 9)) (hrange : π.range = centralizer ({σ₀} : Set (Perm (Fin 9))))
    (hker : ∀ R : Subgroup G', R ≤ π.ker → IsPGroup 2 R → Nat.card R ≤ 2)
    (φ : G' ≃* G') {E₁ : Subgroup G'} (h2 : IsPGroup 2 E₁) (hc : Nat.card E₁ = 32)
    (hN : (E₁ ⊔ pPrimeCore 2 G').Normal) :
    ∃ g : G', E₁.map φ.toMonoidHom = E₁.map (MulAut.conj g).toMonoidHom := by
  set O := pPrimeCore 2 G' with hO
  set E₂ := E₁.map φ.toMonoidHom with hE₂
  have hOφ : O.map φ.toMonoidHom = O := pPrimeCore_map_iso 2 φ
  have hN₂ : (E₂ ⊔ O).Normal := by
    have : E₂ ⊔ O = (E₁ ⊔ O).map φ.toMonoidHom := by rw [Subgroup.map_sup, hOφ]
    rw [this]
    exact Subgroup.Normal.map hN _ φ.surjective
  have h2₂ : IsPGroup 2 E₂ := h2.map _
  have hc₂ : Nat.card E₂ = 32 := by
    rw [hE₂, Subgroup.card_map_of_injective φ.injective, hc]
  haveI : (E₁ ⊔ O).Normal := hN
  haveI : (E₂ ⊔ O).Normal := hN₂
  haveI : ((E₁ ⊔ O) ⊔ (E₂ ⊔ O)).Normal := Subgroup.sup_normal _ _
  have hE₁F : E₁ ≤ (E₁ ⊔ O) ⊔ (E₂ ⊔ O) := le_sup_left.trans le_sup_left
  have hE₂F : E₂ ≤ (E₁ ⊔ O) ⊔ (E₂ ⊔ O) := le_sup_left.trans le_sup_right
  have hFO : ∀ f ∈ (E₁ ⊔ O) ⊔ (E₂ ⊔ O), ∃ k : ℕ, f ^ (2 ^ k) ∈ O := fun f hf =>
    two_power_mem_core h2 h2₂ hN₂ hf
  obtain ⟨h, -, hhE⟩ := exists_conj_le_of_max (H := (E₁ ⊔ O) ⊔ (E₂ ⊔ O)) (Sc := E₂) (B := E₁)
    hE₂F h2₂ hE₁F h2
    (fun T hT hT2 => hc₂ ▸ card_le_of_normal_mod_O π hrange hker hFO hT hT2)
  refine ⟨h, ?_⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨b, hb, rfl⟩
    exact hhE b hb
  · have h1 : Nat.card (E₁.map (MulAut.conj h).toMonoidHom) = Nat.card E₁ :=
      Subgroup.card_map_of_injective (MulAut.conj h).injective
    rw [h1, hc, hc₂]

end Bound

theorem frattini_E32 {X : Type} [Group X] [Finite X] {G : Subgroup X}
    (π : ↥G →* Perm (Fin 9)) (hrange : π.range = centralizer ({σ₀} : Set (Perm (Fin 9))))
    (hker : ∀ R : Subgroup ↥G, R ≤ π.ker → IsPGroup 2 R → Nat.card R ≤ 2)
    {E Λ : Subgroup X} (hEG : E ≤ G) (hE2 : IsPGroup 2 E) (hE : Nat.card E = 32)
    (hΛG : Λ ≤ G) (hΛn : ∀ g ∈ G, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) (hΛ : Odd (Nat.card Λ))
    (hEΛ : ∀ g ∈ G, ∀ e ∈ E, g * e * g⁻¹ ∈ E ⊔ Λ)
    {n : X} (hn : ∀ g ∈ G, n * g * n⁻¹ ∈ G) (hn' : ∀ g ∈ G, n⁻¹ * g * n ∈ G) :
    ∃ f ∈ G, E.map (MulAut.conj n).toMonoidHom = E.map (MulAut.conj f).toMonoidHom := by
  set φ : ↥G ≃* ↥G := Bound.conjAut hn hn' with hφ
  set E₁ : Subgroup ↥G := E.subgroupOf G with hE₁
  set Λ₁ : Subgroup ↥G := Λ.subgroupOf G with hΛ₁
  have hE₁2 : IsPGroup 2 E₁ := hE2.of_equiv (subgroupOfEquivOfLe hEG).symm
  have hE₁c : Nat.card E₁ = 32 := by
    rw [hE₁, Nat.card_congr (subgroupOfEquivOfLe hEG).toEquiv, hE]
  have hΛ₁N : Λ₁.Normal := ⟨fun l hl g => hΛn g g.2 l hl⟩
  have hΛ₁c : Nat.Coprime 2 (Nat.card Λ₁) := by
    rw [hΛ₁, Nat.card_congr (subgroupOfEquivOfLe hΛG).toEquiv]
    exact hΛ.coprime_two_left
  have hΛ₁O : Λ₁ ≤ pPrimeCore 2 ↥G := le_sSup ⟨hΛ₁N, hΛ₁c⟩
  have hN : (E₁ ⊔ pPrimeCore 2 ↥G).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hle : E₁ ⊔ pPrimeCore 2 ↥G ≤
        (E₁ ⊔ pPrimeCore 2 ↥G).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun e he => ?_) (fun o ho => ?_)
      · have h1 : g * e * g⁻¹ ∈ E₁ ⊔ Λ₁ := by
          rw [hE₁, hΛ₁, ← Subgroup.subgroupOf_sup hEG hΛG]
          exact hEΛ g g.2 e he
        exact sup_le_sup_left hΛ₁O E₁ h1
      · exact mem_sup_right (Subgroup.Normal.conj_mem pPrimeCore_normal o ho g)
    exact hle hx
  obtain ⟨g, hg⟩ := conj_of_normal_mod_O π hrange hker φ hE₁2 hE₁c hN
  refine ⟨(g : X), g.2, ?_⟩
  have hmapφ : ∀ K : Subgroup ↥G, (K.map φ.toMonoidHom).map G.subtype =
      (K.map G.subtype).map (MulAut.conj n).toMonoidHom := by
    intro K
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hmapg : ∀ K : Subgroup ↥G, (K.map (MulAut.conj g).toMonoidHom).map G.subtype =
      (K.map G.subtype).map (MulAut.conj (g : X)).toMonoidHom := by
    intro K
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hEE : E₁.map G.subtype = E := map_subgroupOf_eq_of_le hEG
  calc E.map (MulAut.conj n).toMonoidHom
      = (E₁.map G.subtype).map (MulAut.conj n).toMonoidHom := by rw [hEE]
    _ = (E₁.map φ.toMonoidHom).map G.subtype := (hmapφ E₁).symm
    _ = (E₁.map (MulAut.conj g).toMonoidHom).map G.subtype := by rw [hg]
    _ = (E₁.map G.subtype).map (MulAut.conj (g : X)).toMonoidHom := hmapg E₁
    _ = E.map (MulAut.conj (g : X)).toMonoidHom := by rw [hEE]

end CFSG.ComponentClassification.SolMax.Sig36.E32
