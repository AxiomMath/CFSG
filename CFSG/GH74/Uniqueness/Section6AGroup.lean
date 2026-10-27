module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Uniqueness.Section6A

open Subgroup

section Group

variable {X : Type} [Group X]

theorem odd_card_sup_of_le_normalizer [Finite X] {K R : Subgroup X}
    (hRK : R ≤ normalizer (K : Set X)) (hK : Odd (Nat.card K)) (hR : Odd (Nat.card R)) :
    Odd (Nat.card (K ⊔ R : Subgroup X)) := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hRK
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hRK
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient R K hRK
  rw [sup_comm, Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf (R ⊔ K)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (le_sup_right : K ≤ R ⊔ K)).toEquiv]
  exact (Odd.of_dvd_nat hR (Subgroup.card_quotient_dvd_card _)).mul hK

theorem mem_normalizer_of_conj_mem {H : Subgroup X} {t : X} (ht : t * t = 1)
    (h : ∀ x ∈ H, t * x * t⁻¹ ∈ H) : t ∈ normalizer (H : Set X) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h x hx, fun hx => ?_⟩
  have h1 := h _ hx
  have e : t * (t * x * t⁻¹) * t⁻¹ = x := by
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
      _ = x := by rw [ht, hti, ht]; group
  rwa [e] at h1

theorem mem_normalizer_sup_of_conj_mem {A B : Subgroup X} {t : X} (ht : t * t = 1)
    (hA : ∀ x ∈ A, t * x * t⁻¹ ∈ A ⊔ B) (hB : ∀ x ∈ B, t * x * t⁻¹ ∈ A ⊔ B) :
    t ∈ normalizer ((A ⊔ B : Subgroup X) : Set X) := by
  refine mem_normalizer_of_conj_mem ht fun x hx => ?_
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj t).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · simpa using hA a ha
    · simpa using hB b hb
  simpa using hle hx

theorem odd_orderOf_of_isPGroup {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {R : Subgroup X}
    (hR : IsPGroup q R) {x : X} (hx : x ∈ R) : Odd (orderOf x) := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hR ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [hk]
  exact (hq.odd_of_ne_two hq2).pow

theorem isSylowOf_sup_of_le [Finite X] {p : ℕ} (hp : p.Prime) {K R Q : Subgroup X}
    (hRK : R ≤ normalizer (K : Set X)) (hR : IsPGroup p R)
    (hQ : ABGLocalTools.IsSylowOf p Q K) (hQR : Q ≤ R) :
    ABGLocalTools.IsSylowOf p R (K ⊔ R) := by
  have : Fact p.Prime := ⟨hp⟩
  set G : Subgroup X := K ⊔ R with hG
  have hRG : R ≤ G := le_sup_right
  have hKG : K ≤ G := le_sup_left
  have hGK : G ≤ normalizer (K : Set X) := sup_le Subgroup.le_normalizer hRK
  obtain ⟨Q', hQ'⟩ := (hR.comap_subtype (K := G)).exists_le_sylow
  set R₁ : Subgroup X := (Q' : Subgroup ↥G).map G.subtype with hR₁
  have hR₁syl : ABGLocalTools.IsSylowOf p R₁ G := ⟨Q', rfl⟩
  have hRR₁ : R ≤ R₁ := fun x hx =>
    ⟨⟨x, hRG hx⟩, hQ' (show (⟨x, hRG hx⟩ : ↥G) ∈ R.subgroupOf G from hx), rfl⟩
  have hR₁p : IsPGroup p R₁ := hR₁syl.isPGroup
  have hinf : ABGLocalTools.IsSylowOf p (R₁ ⊓ K) K := hR₁syl.inf_of_le_normalizer hKG hGK
  have hQle : Q ≤ R₁ ⊓ K := le_inf (hQR.trans hRR₁) hQ.le
  have hinfQ : R₁ ⊓ K = Q := hQ.eq_of_le hQle inf_le_right hR₁p.to_inf_left
  have hR₁R : R₁ ≤ R := by
    intro x hx
    have hxG : x ∈ (R ⊔ K : Subgroup X) := by
      rw [sup_comm]
      exact hR₁syl.le hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right R K hRK] at hxG
    obtain ⟨r, hr, k, hk, hrk⟩ := hxG
    subst hrk
    have hkR₁ : k ∈ R₁ := by
      have := R₁.mul_mem (R₁.inv_mem (hRR₁ hr)) hx
      simpa using this
    have hkQ : k ∈ Q := by
      rw [← hinfQ]
      exact ⟨hkR₁, hk⟩
    exact R.mul_mem hr (hQR hkQ)
  have hReq : R = R₁ := (le_antisymm hR₁R hRR₁).symm
  rw [hReq]
  exact hR₁syl

theorem pPrimeCore_sup_eq_bot [Finite X] {p : ℕ} (hp : p.Prime) {K R : Subgroup X}
    (hRK : R ≤ normalizer (K : Set X)) (hR : IsPGroup p R)
    (hK : pPrimeCore p ↥K = ⊥) : pPrimeCore p ↥(K ⊔ R) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  set G : Subgroup X := K ⊔ R with hG
  have hKG : K ≤ G := le_sup_left
  have hRG : R ≤ G := le_sup_right
  have hGK : G ≤ normalizer (K : Set X) := sup_le Subgroup.le_normalizer hRK
  set N : Subgroup X := (pPrimeCore p ↥G).map G.subtype with hN
  have hNG : N ≤ G := Subgroup.map_subtype_le _
  have hGN : G ≤ normalizer (N : Set X) :=
    ABGLocalTools.le_normalizer_map_subtype G (pPrimeCore p ↥G)
  have hNcop : Nat.Coprime p (Nat.card N) := by
    rw [hN, Subgroup.card_map_of_injective G.subtype_injective]
    exact pPrimeCore_coprime_card
  have hNK : N ≤ K := by
    intro n hn
    have hnG : n ∈ G := hNG hn
    have hnG' : n ∈ (R ⊔ K : Subgroup X) := by
      rw [sup_comm]
      exact hnG
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right R K hRK] at hnG'
    obtain ⟨r, hr, k, hk, hrk⟩ := hnG'
    obtain ⟨a, ha⟩ := hR ⟨r, hr⟩
    have ha' : r ^ (p ^ a) = 1 := by simpa using congrArg Subtype.val ha
    have hK'n : (K.subgroupOf G).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKG).mpr hGK
    let q : ↥G →* ↥G ⧸ K.subgroupOf G := QuotientGroup.mk' (K.subgroupOf G)
    let ng : ↥G := ⟨n, hnG⟩
    let rg : ↥G := ⟨r, hRG hr⟩
    let kg : ↥G := ⟨k, hKG hk⟩
    have hng : ng = rg * kg := Subtype.ext hrk.symm
    have hkg : q kg = 1 := (QuotientGroup.eq_one_iff kg).mpr hk
    have hq : q ng = q rg := by rw [hng, map_mul, hkg, mul_one]
    have hpow : (q ng) ^ (p ^ a) = 1 := by
      rw [hq, ← map_pow]
      have : rg ^ (p ^ a) = 1 := Subtype.ext (by simpa [rg] using ha')
      rw [this, map_one]
    have hdvd1 : orderOf (q ng) ∣ p ^ a := orderOf_dvd_of_pow_eq_one hpow
    have hdvd2 : orderOf (q ng) ∣ Nat.card N := by
      refine (orderOf_map_dvd q ng).trans ?_
      have : orderOf ng = orderOf n := Subgroup.orderOf_mk _ _
      rw [this]
      exact Subgroup.orderOf_dvd_natCard N hn
    have hcop : Nat.Coprime (orderOf (q ng)) (p ^ a) :=
      (Nat.Coprime.pow_right a (Nat.Coprime.coprime_dvd_left hdvd2 hNcop.symm))
    have h1 : orderOf (q ng) = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd1
    have hq1 : q ng = 1 := orderOf_eq_one_iff.mp h1
    exact (QuotientGroup.eq_one_iff ng).mp hq1
  have hNbot : N = ⊥ := by
    have hKN : K ≤ normalizer (N : Set X) := hKG.trans hGN
    have hNn : (N.subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
    have hcop : Nat.Coprime p (Nat.card (N.subgroupOf K)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv]
      exact hNcop
    have hle : N.subgroupOf K ≤ pPrimeCore p ↥K := le_sSup ⟨hNn, hcop⟩
    rw [hK] at hle
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hNK hx⟩ : ↥K) ∈ N.subgroupOf K := hx
    have h2 := hle h1
    rw [Subgroup.mem_bot] at h2 ⊢
    exact congrArg Subtype.val h2
  exact (Subgroup.map_eq_bot_iff_of_injective _ G.subtype_injective).mp hNbot

theorem le_normalizer_closure {M : Subgroup X} {S : Set X}
    (h : ∀ m ∈ M, ∀ x ∈ S, m * x * m⁻¹ ∈ S) :
    M ≤ normalizer ((Subgroup.closure S : Subgroup X) : Set X) := by
  have hmap : ∀ m ∈ M, ∀ x ∈ Subgroup.closure S, m * x * m⁻¹ ∈ Subgroup.closure S := by
    intro m hm x hx
    have hle : Subgroup.closure S ≤
        (Subgroup.closure S).comap (MulAut.conj m).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have e : (MulAut.conj m).toMonoidHom y = m * y * m⁻¹ := by simp
      rw [e]
      exact Subgroup.subset_closure (h m hm y hy)
    simpa using hle hx
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hmap m hm x hx, fun hx => ?_⟩
  have h1 := hmap m⁻¹ (M.inv_mem hm) _ hx
  have e : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
  rwa [e] at h1

theorem mem_normalizer_of_forall_isSylowOf [Finite X] {O Y : Subgroup X} {z : X} (hz : z * z = 1)
    (hYO : Y ≤ O)
    (h : ∀ q : ℕ, q.Prime → q ∣ Nat.card O → ∃ P : Subgroup X,
      ABGLocalTools.IsSylowOf q P O ∧ z ∈ normalizer ((Y ⊔ P : Subgroup X) : Set X)) :
    z ∈ normalizer (O : Set X) := by
  classical
  choose! P hPsyl hPz using h
  set H : Subgroup X := ⨆ q ∈ (Nat.card O).primeFactors, (Y ⊔ P q) with hH
  have hmem : ∀ q ∈ (Nat.card O).primeFactors, q.Prime ∧ q ∣ Nat.card O := fun q hq =>
    ⟨Nat.prime_of_mem_primeFactors hq, Nat.dvd_of_mem_primeFactors hq⟩
  have hSylle : ∀ q ∈ (Nat.card O).primeFactors, Y ⊔ P q ≤ H := fun q hq =>
    le_iSup₂_of_le (f := fun q (_ : q ∈ (Nat.card O).primeFactors) => Y ⊔ P q) q hq le_rfl
  have hHO : H ≤ O := iSup₂_le fun q hq =>
    sup_le hYO (hPsyl q (hmem q hq).1 (hmem q hq).2).le
  have hzH : z ∈ normalizer (H : Set X) := by
    refine mem_normalizer_of_conj_mem hz fun x hx => ?_
    have hle : H ≤ H.comap (MulAut.conj z).toMonoidHom := by
      refine iSup₂_le fun q hq y hy => ?_
      have h1 : z * y * z⁻¹ ∈ Y ⊔ P q :=
        (Subgroup.mem_normalizer_iff.mp (hPz q (hmem q hq).1 (hmem q hq).2) y).mp hy
      rw [Subgroup.mem_comap]
      simpa using hSylle q hq h1
    simpa using hle hx
  have hOH : O ≤ H := by
    by_contra hnot
    have hne : H.relIndex O ≠ 1 := fun h1 => hnot (Subgroup.relIndex_eq_one.mp h1)
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne
    have hqO : q ∣ Nat.card O := hqdvd.trans (Subgroup.relIndex_dvd_card H O)
    have hqmem : q ∈ (Nat.card O).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hqO, Nat.card_pos.ne'⟩
    have : Fact q.Prime := ⟨hq⟩
    have hsyl := (ABGLocalTools.isSylowOf_iff).mp (hPsyl q hq hqO)
    have hPH : P q ≤ H := (le_sup_right : P q ≤ Y ⊔ P q).trans (hSylle q hqmem)
    have hmul := Subgroup.relIndex_mul_relIndex (P q) H O hPH hHO
    exact hsyl.2.2 (by rw [← hmul]; exact Dvd.dvd.mul_left hqdvd _)
  rw [le_antisymm hHO hOH] at hzH
  exact hzH

end Group

end CFSG.GH74.Uniqueness.Section6A
