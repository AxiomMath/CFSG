module

public import CFSG.GH74.GLS.IVK.Lifted.Lem52
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Closed

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.ABGLocalTools
  CFSG.ABGDGroups CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm3.Sec7 CFSG.GH74.GLS.Stage1.Thm6 CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped commutatorElement

section QLevel

variable {F : Type} [Field F] [Finite F] {Q : Type} [Group Q]

theorem sl_outer_conj [Finite Q] (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (e : Q ≃* SpecialLinearGroup (Fin 2) F) {ξ ξ' : MulAut Q} (hξ2 : ξ * ξ = 1) (hξ'2 : ξ' * ξ' = 1)
    (hξ : ξ ∉ innOf Q) (hξ' : ξ' ∉ innOf Q)
    (hσ : (gammaOf hodd h3 (MulAut.congr e ξ)).right = 1)
    (hσ' : (gammaOf hodd h3 (MulAut.congr e ξ')).right = 1) :
    ∃ k : Q, MulAut.conj k * ξ * (MulAut.conj k)⁻¹ = ξ' := by
  have hL2 : L2Field F := ⟨hodd, h3⟩
  let ι : MulAut Q →* MulAut (PSL2 F) := psl2AutHom.comp (MulAut.congr e).toMonoidHom
  have hι : Function.Injective ι :=
    (psl2AutHom_injective hodd h3).comp (MulAut.congr e).injective
  let π : Q →* PSL2 F :=
    (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F))).comp e.toMonoidHom
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp e.surjective
  have hιconj : ∀ x : Q, ι (MulAut.conj x) = MulAut.conj (π x) := by
    intro x
    show psl2AutHom (MulAut.congr e (MulAut.conj x)) = _
    rw [congr_conj, psl2AutHom_conj]
    rfl
  let e₀ : PSL2 F ≃* L2 F := (L2.equivPSL F).symm
  have hdiag : ∀ η : MulAut Q, (gammaOf hodd h3 (MulAut.congr e η)).right = 1 → ι η ∈ innDiagSub e₀ := by
    intro η hη
    rw [mem_innDiagSub_iff]
    have : ι η = psl2AutHom (MulAut.congr e η) := rfl
    rw [this, fieldProj_psl2AutHom hodd h3]
    exact hη
  have hout : ∀ η : MulAut Q, η ∉ innOf Q → ι η ∉ innAut (PSL2 F) := by
    intro η hη hmem
    obtain ⟨u, hu⟩ := hmem
    obtain ⟨k, rfl⟩ := hπ u
    apply hη
    refine ⟨k, ?_⟩
    apply hι
    rw [hιconj, hu]
  have hord : ∀ η : MulAut Q, η * η = 1 → η ∉ innOf Q → orderOf (ι η) = 2 := by
    intro η hη2 hη
    have h1 : ι η ≠ 1 := by
      intro h
      apply hη
      have : η = 1 := hι (h.trans (map_one ι).symm)
      rw [this]
      exact one_mem _
    refine orderOf_eq_prime ?_ h1
    rw [pow_two, ← map_mul, hη2, map_one]
  obtain ⟨a, ha, hax⟩ := outer_involutions_conj e₀ hL2 (hdiag ξ hσ) (hout ξ hξ) (hdiag ξ' hσ')
    (hout ξ' hξ') (hord ξ hξ2 hξ) (hord ξ' hξ'2 hξ')
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨k, rfl⟩ := hπ u
  refine ⟨k, ?_⟩
  apply hι
  rw [map_mul, map_mul, map_inv, hιconj, hax]

omit [Finite F] in
theorem exists_twist_aux [Finite F] (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (e : Q ≃* SpecialLinearGroup (Fin 2) F) (ξ : MulAut Q) (hξ2 : ξ * ξ = 1) (hξ : ξ ≠ 1) :
    ∃ x₁ : Q, orderOf x₁ = 4 ∧ ξ x₁ = x₁⁻¹ := by
  have hord : orderOf ξ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hξ2) hξ
  exact ivk_1_13 F hodd h3 Q (e.trans (specialLinearGroupEquivStatedSL 2 F)) ξ hord

end QLevel

section Outer

theorem exists_central_of_normal_card_two {H : Type} [Group H] (N : Subgroup H) [N.Normal]
    (hN : Nat.card N = 2) : ∃ u : H, u ≠ 1 ∧ u ∈ Subgroup.center H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥N := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 (by rw [hN])
  have hu' : orderOf (u : H) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  refine ⟨(u : H), fun h => ?_, ?_⟩
  · rw [h, orderOf_one] at hu'
    omega
  · rw [Subgroup.mem_center_iff]
    intro g
    have hmem : g * (u : H) * g⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance _ u.2 g
    have h1 : zpowers (u : H) = N := by
      apply Subgroup.eq_of_le_of_card_ge (zpowers_le.2 u.2)
      rw [Nat.card_zpowers, hu', hN]
    have hmem' : g * (u : H) * g⁻¹ ∈ zpowers (u : H) := by
      rw [h1]
      exact hmem
    rcases eq_one_or_of_mem_zpowers_two hu' hmem' with h | h
    · exfalso
      have : (u : H) = 1 := by
        have h2 : g⁻¹ * (g * (u : H) * g⁻¹) * g = u := by group
        rw [h, mul_one, inv_mul_cancel] at h2
        exact h2.symm
      rw [this, orderOf_one] at hu'
      omega
    · calc g * (u : H) = (g * (u : H) * g⁻¹) * g := by group
        _ = (u : H) * g := by rw [h]

variable {G : Type} [Group G] [Finite G]

theorem phi_not_inner_of_pglQuot {K : Subgroup G} {z w : G} {q : ℕ} (hK : HatSL2 K q)
    (hzK : z ∈ K) (hKz : K ≤ centralizer ({z} : Set G)) (hz2 : orderOf z = 2)
    (hcen : Nat.card (Subgroup.center (Hat K)) = 2) (hwN : w ∈ normalizer (K : Set G))
    (hPG : ∃ (Fq : Type) (_ : Field Fq) (_ : Finite Fq), Nat.card Fq = q ∧ PGLQuot z w K Fq) :
    ¬ phi K w hwN ∈ innOf (Hat K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F₀, hF₀f, hF₀fin, hF₀q, ⟨e₀⟩⟩ := hK
  obtain ⟨Fq, hFqf, hFqfin, hFqq, hN, ⟨ψ⟩⟩ := hPG
  have hHat : Nat.card (Hat K) = q * (q ^ 2 - 1) := by
    rw [Nat.card_congr e₀.toEquiv,
      ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F₀).toEquiv, sl2_card_formula, hF₀q]
  have hPGL : Nat.card (PGL2 Fq) = q * (q ^ 2 - 1) := by rw [pgl2_card_formula, hFqq]
  intro hin
  set X : Subgroup G := K ⊔ zpowers w with hXdef
  have hXN : X ≤ normalizer (K : Set G) := sup_le le_normalizer (zpowers_le.2 hwN)
  set N₀ : Subgroup ↥X := (pPrimeCoreOf 2 K ⊔ zpowers z).subgroupOf X with hN₀
  let Φ : ↥X →* MulAut (Hat K) := (phiHom K).comp (Subgroup.inclusion hXN)
  have hΦ : ∀ x : ↥X, Φ x = phi K (x : G) (hXN x.2) := fun x => rfl
  have hzS : IsPGroup 2 ↥(zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2]; norm_num)
  have hc₀c : hatMk K ⟨z, hzK⟩ ∈ Subgroup.center (Hat K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := hatMk_surjective K y
    show hatMk K k * hatMk K ⟨z, hzK⟩ = hatMk K ⟨z, hzK⟩ * hatMk K k
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (k : G) * z = z * (k : G)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hKz k.2)
  have hsub : pPrimeCoreOf 2 K ⊔ zpowers z ≤ cSec K := by
    refine sup_le (fun o ho => ?_) ?_
    · obtain ⟨hoK, h0⟩ := (mem_pPrimeCoreOf_iff_hatMk K o).1 ho
      refine (phi_eq_one_iff K (le_normalizer hoK)).1 ?_
      rw [phi_of_mem K hoK, h0, map_one]
    · rw [zpowers_le]
      refine (phi_eq_one_iff K (le_normalizer hzK)).1 ?_
      rw [phi_of_mem K hzK]
      exact conj_eq_one_of_mem_center hc₀c
  have hN₀ker : N₀ ≤ Φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hΦ]
    exact (phi_eq_one_iff K (hXN x.2)).2 (hsub (Subgroup.mem_subgroupOf.1 hx))
  have hnormal : N₀.Normal := hN
  let Φb : ↥X ⧸ N₀ →* MulAut (Hat K) := QuotientGroup.lift N₀ Φ hN₀ker
  have hXinn : ∀ x : ↥X, Φ x ∈ innOf (Hat K) := by
    let I : Subgroup G := ((innOf (Hat K)).comap (phiHom K)).map (normalizer (K : Set G)).subtype
    have hKI : K ≤ I := fun k hk =>
      ⟨⟨k, le_normalizer hk⟩, ⟨hatMk K ⟨k, hk⟩, (phi_of_mem K hk).symm⟩, rfl⟩
    have hwI : w ∈ I := ⟨⟨w, hwN⟩, hin, rfl⟩
    have hXI : X ≤ I := sup_le hKI (zpowers_le.2 hwI)
    intro x
    obtain ⟨n, hn, hnx⟩ := hXI x.2
    have : n = ⟨(x : G), hXN x.2⟩ := Subtype.ext hnx
    rw [this] at hn
    exact hn
  have hrange : Φb.range = innOf (Hat K) := by
    apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      induction u using QuotientGroup.induction_on with | H x => ?_
      exact hXinn x
    · rintro _ ⟨y, rfl⟩
      obtain ⟨k, rfl⟩ := hatMk_surjective K y
      have hkX : (k : G) ∈ X := mem_sup_left k.2
      refine ⟨QuotientGroup.mk ⟨(k : G), hkX⟩, ?_⟩
      show Φ ⟨(k : G), hkX⟩ = MulAut.conj (hatMk K k)
      rw [hΦ]
      exact phi_of_mem K k.2
  have hinnCard : 2 * Nat.card ↥(innOf (Hat K)) = Nat.card (Hat K) := by
    have h1 := Subgroup.card_ker_mul_card_range (MulAut.conj : Hat K →* MulAut (Hat K))
    have h2 : (MulAut.conj : Hat K →* MulAut (Hat K)).ker = Subgroup.center (Hat K) := by
      ext y
      rw [MonoidHom.mem_ker]
      exact ⟨mem_center_of_conj_eq_one, conj_eq_one_of_mem_center⟩
    rw [h2, hcen] at h1
    exact h1
  have hquot : Nat.card (↥X ⧸ N₀) = q * (q ^ 2 - 1) := by
    rw [Nat.card_congr ψ.toEquiv, hPGL]
  have hker := Subgroup.card_ker_mul_card_range Φb
  rw [hquot, hrange, ← hHat, ← hinnCard] at hker
  have hinnpos : 0 < Nat.card ↥(innOf (Hat K)) := Nat.card_pos
  have hker2 : Nat.card Φb.ker = 2 := by
    have : Nat.card Φb.ker * Nat.card ↥(innOf (Hat K)) = 2 * Nat.card ↥(innOf (Hat K)) := hker
    exact Nat.eq_of_mul_eq_mul_right hinnpos this
  obtain ⟨u, hu1, huc⟩ := exists_central_of_normal_card_two Φb.ker hker2
  have hψu : ψ u ∈ Subgroup.center (PGL2 Fq) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨v, rfl⟩ := ψ.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact (Subgroup.mem_center_iff.1 huc v)
  rw [pgl2_center_eq_bot Fq, Subgroup.mem_bot] at hψu
  exact hu1 (ψ.injective (hψu.trans (map_one ψ).symm))

end Outer

section SylowLift

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_of_mul_mem_odd {O : Subgroup G} (hOodd : Odd (Nat.card ↥O)) {x x' : G}
    (hx2 : x * x = 1) (hx'2 : x' * x' = 1) (hx1 : x ≠ 1) (hx1' : x' ≠ 1)
    (hnorm : ∀ n ∈ O, x' * n * x'⁻¹ ∈ O) (hxO : x * x'⁻¹ ∈ O) :
    ∃ g ∈ O ⊔ zpowers x', g * x * g⁻¹ = x' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H₀ : Subgroup G := O ⊔ zpowers x' with hH₀
  have hx'H : x' ∈ H₀ := mem_sup_right (mem_zpowers x')
  have hxH : x ∈ H₀ := by
    have : x = (x * x'⁻¹) * x' := by group
    rw [this]
    exact mul_mem (mem_sup_left hxO) hx'H
  have hord' : orderOf x' = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx'2) hx1'
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hx'O : x' ∉ O := by
    intro h
    have := Subgroup.orderOf_dvd_natCard O h
    rw [hord'] at this
    exact (Nat.not_even_iff_odd.2 hOodd) (even_iff_two_dvd.2 this)
  have hx'inv : x'⁻¹ = x' := inv_eq_of_mul_eq_one_right hx'2
  have hx'norm : x' ∈ normalizer (O : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact hnorm n
    · intro hn
      have h1 := hnorm (x' * n * x'⁻¹) hn
      have h2 : x' * (x' * n * x'⁻¹) * x'⁻¹ = n := by
        calc x' * (x' * n * x'⁻¹) * x'⁻¹ = (x' * x') * n * (x' * x')⁻¹ := by group
          _ = n := by rw [hx'2]; group
      rw [h2] at h1
      exact h1
  have hcov : ∀ b ∈ H₀, b ∈ O ∨ ∃ p ∈ O, b = p * x' := by
    intro b hb
    rcases CFSG.GH74.GLS.Stage1.Thm3.Sec5.mem_or_mul_inv_mem hx'norm
      (by rw [hx'2]; exact one_mem O) hb with h | h
    · exact Or.inl h
    · exact Or.inr ⟨b * x'⁻¹, h, by group⟩
  have hrel : O.relIndex H₀ ≤ 2 := by
    refine relIndex_le_two_of_cover hx'H hcov ?_
    intro p hp
    have h1 := hnorm p hp
    rw [hx'inv] at h1
    rw [hx'inv]
    exact h1
  have hcardmul := Subgroup.relIndex_mul_card (H := O) (K := H₀)
  have hOH : O ⊓ H₀ = O := inf_eq_left.2 le_sup_left
  rw [hOH] at hcardmul
  have hrel1 : O.relIndex H₀ ≠ 1 := fun h => hx'O (Subgroup.relIndex_eq_one.1 h hx'H)
  have hrel0 : O.relIndex H₀ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hcardmul
    exact (Nat.card_pos (α := ↥H₀)).ne' hcardmul.symm
  have hrel2 : O.relIndex H₀ = 2 := by omega
  rw [hrel2] at hcardmul
  have hOpos : 0 < Nat.card ↥O := Nat.card_pos
  have hfac : (Nat.card ↥H₀).factorization 2 = 1 := by
    rw [← hcardmul, Nat.factorization_mul (by norm_num) hOpos.ne']
    simp only [Finsupp.add_apply]
    have : (Nat.card ↥O).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by
        intro h
        exact (Nat.not_even_iff_odd.2 hOodd) (even_iff_two_dvd.2 h))
    rw [this, Nat.Prime.factorization_self Nat.prime_two]
  let xH : ↥H₀ := ⟨x, hxH⟩
  let x'H : ↥H₀ := ⟨x', hx'H⟩
  have hxHo : orderOf xH = 2 := by
    rw [show orderOf xH = orderOf x from Subgroup.orderOf_mk x hxH, hord]
  have hx'Ho : orderOf x'H = 2 := by
    rw [show orderOf x'H = orderOf x' from Subgroup.orderOf_mk x' hx'H, hord']
  have hA : Nat.card ↥(zpowers x'H) = 2 ^ (Nat.card ↥H₀).factorization 2 := by
    rw [Nat.card_zpowers, hx'Ho, hfac, pow_one]
  have hB : Nat.card ↥(zpowers xH) = 2 ^ (Nat.card ↥H₀).factorization 2 := by
    rw [Nat.card_zpowers, hxHo, hfac, pow_one]
  let SA : Sylow 2 ↥H₀ := Sylow.ofCard (zpowers x'H) hA
  let SB : Sylow 2 ↥H₀ := Sylow.ofCard (zpowers xH) hB
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥H₀ SB SA
  have hconj : ∀ y : ↥H₀, y ∈ zpowers x'H ↔ g⁻¹ * y * g ∈ zpowers xH := by
    intro y
    have h := congrArg (fun S : Sylow 2 ↥H₀ => (S : Subgroup ↥H₀)) hg
    simp only [Sylow.coe_subgroup_smul] at h
    show y ∈ (SA : Subgroup ↥H₀) ↔ g⁻¹ * y * g ∈ (SB : Subgroup ↥H₀)
    rw [← h, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  have hmem : g * xH * g⁻¹ ∈ zpowers x'H := by
    rw [hconj]
    simp [mul_assoc]
  refine ⟨(g : G), g.2, ?_⟩
  rcases eq_one_or_of_mem_zpowers_two hx'Ho hmem with h | h
  · exfalso
    have h1 : xH = 1 := by
      have h2 : g⁻¹ * (g * xH * g⁻¹) * g = xH := by group
      rw [h, mul_one, inv_mul_cancel] at h2
      exact h2.symm
    have : x = 1 := congrArg Subtype.val h1
    exact hx1 this
  · exact congrArg Subtype.val h

end SylowLift

section CompStep

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem phi_conj_eq (A : Subgroup G) {c x : G} (hc : c ∈ normalizer (A : Set G))
    (hx : x ∈ normalizer (A : Set G)) :
    phi A (c * x * c⁻¹) (mul_mem (mul_mem hc hx) (inv_mem hc)) =
      phi A c hc * phi A x hx * (phi A c hc)⁻¹ := by
  rw [phi_mul A (mul_mem hc hx) (inv_mem hc), phi_mul A hc hx, phi_inv_aux A hc (inv_mem hc)]

omit [Finite G] in
theorem phi_mem_inn_of_mem_sup {z : G} {S K₁ K₂ : Subgroup G}
    (hM : M.M4 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂) {A : Subgroup G}
    (hAc : A = K₁ ∨ A = K₂) {p : G} (hp : p ∈ K₁ ⊔ K₂) (hpN : p ∈ normalizer (A : Set G)) :
    phi A p hpN ∈ innOf (Hat A) := by
  let I : Subgroup G := ((innOf (Hat A)).comap (phiHom A)).map (normalizer (A : Set G)).subtype
  have hAI : A ≤ I := fun k hk =>
    ⟨⟨k, le_normalizer hk⟩, ⟨hatMk A ⟨k, hk⟩, (phi_of_mem A hk).symm⟩, rfl⟩
  have hBI : ∀ B : Subgroup G, B ≤ cSec A → B ≤ I := by
    intro B hB k hk
    refine ⟨⟨k, (hB hk).1⟩, ?_, rfl⟩
    show phi A k _ ∈ innOf (Hat A)
    rw [(phi_eq_one_iff A _).2 (hB hk)]
    exact one_mem _
  have hK₁I : K₁ ≤ I := by
    rcases hAc with rfl | rfl
    · exact hAI
    · exact hBI K₁ (fun x hx => hM.cs₂ hx)
  have hK₂I : K₂ ≤ I := by
    rcases hAc with rfl | rfl
    · exact hBI K₂ (fun x hx => hM.cs₁ hx)
    · exact hAI
  obtain ⟨n, hn, hnp⟩ := sup_le hK₁I hK₂I hp
  have : n = ⟨p, hpN⟩ := Subtype.ext hnp
  rw [this] at hn
  exact hn

end CompStep

section CompStep2

variable {G : Type} [Group G] [Finite G]

theorem comp_step {A : Subgroup G} {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h3 : 3 < Nat.card F) (e : Hat A ≃* SpecialLinearGroup (Fin 2) F) (hOK : HatOK (Hat A)) {z : G}
    (hzA : z ∈ A) (hzc : hatMk A ⟨z, hzA⟩ ∈ Subgroup.center (Hat A)) (hz2 : orderOf z = 2)
    {w x x' : G} (hwN : w ∈ normalizer (A : Set G)) (hxN : x ∈ normalizer (A : Set G))
    (hx'N : x' ∈ normalizer (A : Set G)) (hxx : x * x = 1) (hx'x' : x' * x' = 1)
    (hαf : (gammaOf hodd h3 (MulAut.congr e (phi A w hwN))).right = 1)
    (hαin : phi A w hwN ∉ innOf (Hat A))
    (hxα : phi A x hxN * (phi A w hwN)⁻¹ ∈ innOf (Hat A))
    (hx'α : phi A x' hx'N * (phi A w hwN)⁻¹ ∈ innOf (Hat A)) :
    (∃ k ∈ A, ∀ hk : k * x * k⁻¹ ∈ normalizer (A : Set G), phi A (k * x * k⁻¹) hk = phi A x' hx'N) ∧
      (∃ d ∈ A, ∃ o ∈ pPrimeCoreOf 2 A, d * x * d⁻¹ = z * o * x) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α := phi A w hwN with hα
  set ξ := phi A x hxN with hξ
  set ξ' := phi A x' hx'N with hξ'
  have hξ2 : ξ * ξ = 1 := phi_mul_self A hxN hxx
  have hξ'2 : ξ' * ξ' = 1 := phi_mul_self A hx'N hx'x'
  have hσinn : ∀ c ∈ innOf (Hat A), (gammaOf hodd h3 (MulAut.congr e c)).right = 1 := by
    rintro c ⟨y, rfl⟩
    rw [congr_conj]
    exact gammaOf_conj_right hodd h3 (e y)
  have hσ : ∀ η : MulAut (Hat A), η * α⁻¹ ∈ innOf (Hat A) →
      (gammaOf hodd h3 (MulAut.congr e η)).right = 1 := by
    intro η hη
    have h1 : η = (η * α⁻¹) * α := by group
    rw [h1, map_mul, gammaOf_mul_right, hσinn _ hη, hαf, one_mul]
  have hnot : ∀ η : MulAut (Hat A), η * α⁻¹ ∈ innOf (Hat A) → η ∉ innOf (Hat A) := by
    intro η hη h
    apply hαin
    have : α = (η * α⁻¹)⁻¹ * η := by group
    rw [this]
    exact mul_mem (inv_mem hη) h
  have hξin : ξ ∉ innOf (Hat A) := hnot ξ hxα
  have hξ'in : ξ' ∉ innOf (Hat A) := hnot ξ' hx'α
  refine ⟨?_, ?_⟩
  · obtain ⟨kb, hkb⟩ := sl_outer_conj hodd h3 e hξ2 hξ'2 hξin hξ'in (hσ ξ hxα) (hσ ξ' hx'α)
    obtain ⟨k, rfl⟩ := hatMk_surjective A kb
    refine ⟨(k : G), k.2, fun hk => ?_⟩
    have hkN : (k : G) ∈ normalizer (A : Set G) := le_normalizer k.2
    rw [phi_conj_eq A hkN hxN, phi_of_mem A k.2, ← hkb]
  · have hξ1 : ξ ≠ 1 := fun h => hξin (h ▸ one_mem _)
    obtain ⟨x₁, hx₁4, hξx₁⟩ := exists_twist_aux hodd h3 e ξ hξ2 hξ1
    obtain ⟨d, rfl⟩ := hatMk_surjective A x₁
    set g : G := (d : G) with hg
    have hgN : g ∈ normalizer (A : Set G) := le_normalizer d.2
    have hxgx : x * g⁻¹ * x⁻¹ ∈ A := (mem_normalizer_iff.mp hxN g⁻¹).mp (inv_mem d.2)
    have hc₀A : g * (x * g⁻¹ * x⁻¹) ∈ A := mul_mem d.2 hxgx
    have hmk1 : hatMk A ⟨x * g⁻¹ * x⁻¹, hxgx⟩ = hatMk A d := by
      have h1 : hatMk A ⟨x * g⁻¹ * x⁻¹, hxgx⟩ = ξ (hatMk A ⟨g⁻¹, inv_mem d.2⟩) := by
        rw [hξ, phi_mk]
      have h2 : hatMk A ⟨g⁻¹, inv_mem d.2⟩ = (hatMk A d)⁻¹ := by
        rw [← map_inv]
        rfl
      rw [h1, h2, map_inv, hξx₁, inv_inv]
    have hzo : orderOf (hatMk A ⟨z, hzA⟩) = 2 := by
      have hzKle : zpowers z ≤ A := zpowers_le.2 hzA
      have hzS : IsPGroup 2 ↥(zpowers z) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2]; norm_num)
      have := orderOf_hatMk hzKle hzS (mem_zpowers z)
      rw [hz2] at this
      exact this
    have hsq : hatMk A d * hatMk A d = hatMk A ⟨z, hzA⟩ := by
      have h1 : orderOf (hatMk A d * hatMk A d) = 2 := by
        rw [← pow_two, orderOf_pow' _ (by norm_num), hx₁4]
        norm_num
      refine noCommInv_of_pRank hOK.rank _ _ h1 hzo ?_
      exact Subgroup.mem_center_iff.1 hzc _
    have hmkc : hatMk A ⟨g * (x * g⁻¹ * x⁻¹), hc₀A⟩ = hatMk A ⟨z, hzA⟩ := by
      have : (⟨g * (x * g⁻¹ * x⁻¹), hc₀A⟩ : ↥A) = d * ⟨x * g⁻¹ * x⁻¹, hxgx⟩ := rfl
      rw [this, map_mul, hmk1, hsq]
    have hozA : z⁻¹ * (g * (x * g⁻¹ * x⁻¹)) ∈ A := mul_mem (inv_mem hzA) hc₀A
    have hoO : z⁻¹ * (g * (x * g⁻¹ * x⁻¹)) ∈ pPrimeCoreOf 2 A := by
      rw [← hatMk_eq_one_iff A ⟨_, hozA⟩]
      have : (⟨z⁻¹ * (g * (x * g⁻¹ * x⁻¹)), hozA⟩ : ↥A) =
          (⟨z, hzA⟩ : ↥A)⁻¹ * ⟨g * (x * g⁻¹ * x⁻¹), hc₀A⟩ := rfl
      rw [this, map_mul, map_inv, hmkc, inv_mul_cancel]
    refine ⟨g, d.2, z⁻¹ * (g * (x * g⁻¹ * x⁻¹)), hoO, ?_⟩
    group

end CompStep2

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem cSec_le_normalizer {K : Subgroup G} : cSec K ≤ normalizer (K : Set G) := by
  intro x hx
  obtain ⟨hn, -, -⟩ := id hx
  exact hn

theorem comp_facts (h44 : II4_44) (hII : II4_4_4_center) {z : G} {S K₁ K₂ : Subgroup G} {t u : G}
    {q : ℕ} {w : G} (hC : Cfg7 G z S K₁ K₂ t u q) (hconcl : Concl72abcf z S K₁ K₂ t q w)
    (hw1 : w ≠ 1) {A : Subgroup G} (hAc : A = K₁ ∨ A = K₂) {x x' : G}
    (hxP : x * w⁻¹ ∈ Pz S z) (hx'P : x' * w⁻¹ ∈ Pz S z) (hxx : x * x = 1) (hx'x' : x' * x' = 1) :
    ∃ (_ : x ∈ normalizer (A : Set G)) (hx'N : x' ∈ normalizer (A : Set G)),
      (∃ k ∈ A, ∀ hk : k * x * k⁻¹ ∈ normalizer (A : Set G),
        phi A (k * x * k⁻¹) hk = phi A x' hx'N) ∧
      (∃ d ∈ A, ∃ o ∈ pPrimeCoreOf 2 A, d * x * d⁻¹ = z * o * x) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hC.std.std
  have hM := m4_of_std hII hstd
  obtain ⟨hwS, hw12, htw, ⟨hPY, hSPY⟩, hS1, hint, hpgl⟩ := hconcl
  have hw2 : orderOf w = 2 := hw12.resolve_left hw1
  have hww : w * w = 1 := mul_self_eq_one_of_orderOf_eq_two hw2
  have hz2 : orderOf z = 2 := hstd.orderOf_z
  have hAmem : A ∈ ({K₁, K₂} : Set (Subgroup G)) := by simpa using hAc
  have hOK := std4_hatOK h44 hstd hAmem
  have hzC : ∀ y ∈ K₁ ⊔ K₂, y ∈ normalizer (A : Set G) := by
    intro y hy
    rcases hAc with rfl | rfl
    · exact (sup_le le_normalizer (fun v hv => cSec_le_normalizer (hM.cs₁ hv))) hy
    · exact (sup_le (fun v hv => cSec_le_normalizer (hM.cs₂ hv)) le_normalizer) hy
  have hwN1 : w ∈ normalizer (K₁ : Set G) := by
    have : w ∈ S1 S K₁ := by
      rw [hS1]
      exact mem_sup_right (mem_zpowers w)
    exact this.2
  have hwNA : w ∈ normalizer (A : Set G) := by
    rcases hAc with rfl | rfl
    · exact hwN1
    · exact (std4_normalizer_swap hstd (hM.S_syl.1 hwS)).1 hwN1
  have hpmem : ∀ v : G, v * w⁻¹ ∈ Pz S z → v * w⁻¹ ∈ K₁ ⊔ K₂ := by
    intro v hv
    have h1 : v * w⁻¹ ∈ rigidProduct z := hv.2
    rwa [hstd.rigidProduct_eq] at h1
  have hxN : x ∈ normalizer (A : Set G) := by
    have : x = (x * w⁻¹) * w := by group
    rw [this]
    exact mul_mem (hzC _ (hpmem x hxP)) hwNA
  have hx'N : x' ∈ normalizer (A : Set G) := by
    have : x' = (x' * w⁻¹) * w := by group
    rw [this]
    exact mul_mem (hzC _ (hpmem x' hx'P)) hwNA
  refine ⟨hxN, hx'N, ?_⟩
  rcases sl_or_a7 hOK.sl2 with ⟨F, hFf, hFin, hodd, h3, ⟨e⟩⟩ | h7
  swap
  · exfalso
    rcases hAc with rfl | rfl
    · exact hC.std.d₁ h7
    · exact hC.std.d₂ h7
  have hKz : A ≤ centralizer ({z} : Set G) := by
    rcases hAc with rfl | rfl
    · exact hM.K₁_le
    · exact hM.K₂_le
  have hzA : z ∈ A := hM.z_mem_comp hAc
  have hzc : hatMk A ⟨z, hzA⟩ ∈ Subgroup.center (Hat A) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := hatMk_surjective A y
    show hatMk A k * hatMk A ⟨z, hzA⟩ = hatMk A ⟨z, hzA⟩ * hatMk A k
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (k : G) * z = z * (k : G)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hKz k.2)
  have hmQA : pRank 2 ↥(Qof S A) = 1 := by
    rcases hAc with rfl | rfl
    · exact hC.std.b₁
    · exact hC.std.b₂
  have hzP : z ∈ Pz S z := by
    rw [CFSG.GH74.GLS.Stage1.Thm3.Sec4.Pz_eq hstd]
    exact hM.z_mem_P
  have hα1 : phi A w hwNA ≠ 1 := by
    intro h1
    have hwc : w ∈ cSec A := (phi_eq_one_iff A hwNA).1 h1
    have hwz : w = z := eq_z_of_mem_Qof hM hAc hmQA hz2 ⟨hwS, hwc⟩ hw2
    have h2 : z ∈ Pz S z ⊓ Ysub t w := ⟨hzP, hwz ▸ mem_sup_right (mem_zpowers w)⟩
    rw [hPY, Subgroup.mem_bot] at h2
    rw [h2, orderOf_one] at hz2
    omega
  have hαf : (gammaOf hodd h3 (MulAut.congr e (phi A w hwNA))).right = 1 := by
    by_contra hσ
    have hφ2 : phi A w hwNA * phi A w hwNA = 1 := phi_mul_self A hwNA hww
    have hα2 : MulAut.congr e (phi A w hwNA) * MulAut.congr e (phi A w hwNA) = 1 := by
      rw [← map_mul, hφ2, map_one]
    have hF : InducesFAut w A := ⟨hwNA, hOK.quasi, hOK.kgrp, hOK.rank, exists_pow_two_orderOf hφ2,
      fixedCond_of_congr e (fixedCond_of_field_part hodd h3 _ hα2 hσ)⟩
    have hwc : w ∈ cSec A := by
      rcases hAc with rfl | rfl
      · exact hC.std.a₁ w hwS hF
      · exact hC.std.a₂ w hwS hF
    exact hα1 ((phi_eq_one_iff A hwNA).2 hwc)
  have hq : HatSL2 A q := by
    rcases hAc with rfl | rfl
    · exact hC.ch.hq₁
    · exact hC.ch.hq₂
  have hαin : phi A w hwNA ∉ innOf (Hat A) :=
    phi_not_inner_of_pglQuot hq hzA hKz hz2 hOK.sl2.2 hwNA (hpgl hw1 A hAmem)
  have hinnx : ∀ v : G, ∀ hv : v ∈ normalizer (A : Set G), v * w⁻¹ ∈ Pz S z →
      phi A v hv * (phi A w hwNA)⁻¹ ∈ innOf (Hat A) := by
    intro v hv hvP
    have hpN : v * w⁻¹ ∈ normalizer (A : Set G) := hzC _ (hpmem v hvP)
    have h1 : phi A v hv = phi A (v * w⁻¹) hpN * phi A w hwNA := by
      rw [← phi_mul A hpN hwNA]
      exact phi_congr A (by group) hv _
    rw [h1, mul_inv_cancel_right]
    exact phi_mem_inn_of_mem_sup hM hAc (hpmem v hvP) hpN
  exact comp_step hodd h3 e hOK hzA hzc hz2 hwNA hxN hx'N hxx hx'x' hαf hαin (hinnx x hxN hxP)
    (hinnx x' hx'N hx'P)

end Main

section MainThm

variable {G : Type} [Group G] [Finite G]

theorem commutes_mod_O_of_gens {z : G} {S K₁ K₂ : Subgroup G} (hstd : Std4 G z S K₁ K₂) {y : G}
    (h1 : ∀ k ∈ K₁, ⁅k, y⁆ ∈ pPrimeCoreOf 2 K₁)
    (h2 : ∀ k ∈ K₂, ⁅k, y⁆ ∈ pPrimeCoreOf 2 K₂) : ∀ k ∈ K₁ ⊔ K₂, ⁅k, y⁆ ∈ Oz z := by
  have hM₁ := hstd.comp_isPCompIn (Or.inl rfl : K₁ = K₁ ∨ K₁ = K₂)
  have hM₂ := hstd.comp_isPCompIn (Or.inr rfl : K₂ = K₁ ∨ K₂ = K₂)
  let T : Subgroup G :=
    { carrier := {k | k ∈ Cz z ∧ ⁅k, y⁆ ∈ Oz z}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨haC, ha⟩ ⟨hbC, hb⟩
        refine ⟨mul_mem haC hbC, ?_⟩
        have h : ⁅a * b, y⁆ = (a * ⁅b, y⁆ * a⁻¹) * ⁅a, y⁆ := by
          simp only [commutatorElement_def]
          group
        rw [h]
        exact mul_mem (Oz_conj haC hb) ha
      inv_mem' := by
        rintro a ⟨haC, ha⟩
        refine ⟨inv_mem haC, ?_⟩
        have h : ⁅a⁻¹, y⁆ = a⁻¹ * (⁅a, y⁆)⁻¹ * a := by
          simp only [commutatorElement_def]
          group
        rw [h]
        have := Oz_conj (inv_mem haC) (inv_mem ha)
        simpa using this }
  have hK₁T : K₁ ≤ T := fun k hk =>
    ⟨hM₁.1 hk, pPrimeCoreOf_le_Oz hM₁ (h1 k hk)⟩
  have hK₂T : K₂ ≤ T := fun k hk =>
    ⟨hM₂.1 hk, pPrimeCoreOf_le_Oz hM₂ (h2 k hk)⟩
  intro k hk
  exact (sup_le hK₁T hK₂T hk).2

theorem ivk_3_1c_lifted_of_II4 (h44 : II4_44) (hII : II4_4_4_center) (hFS : FStar_C) :
    CFSG.GH74.GLS.Stage1.Thm3.Sec7.IVK_3_1c_lifted := by
  intro G _ _ z S K₁ K₂ t u q w hC hconcl hw1 x hxS x' hx'S hxP hx'P hx2 hx'2
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hC.std.std
  have hM := m4_of_std hII hstd
  have hxx : x * x = 1 := mul_self_eq_one_of_orderOf_eq_two hx2
  have hx'x' : x' * x' = 1 := mul_self_eq_one_of_orderOf_eq_two hx'2
  have hx1 : x ≠ 1 := ne_one_of_orderOf_eq_two hx2
  have hx'1 : x' ≠ 1 := ne_one_of_orderOf_eq_two hx'2
  have hzz : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hstd.orderOf_z
  obtain ⟨hxN₁, hx'N₁, ⟨k₁, hk₁, hk₁c⟩, ⟨d₁, hd₁, o₁, ho₁, hd₁x⟩⟩ :=
    comp_facts h44 hII hC hconcl hw1 (A := K₁) (Or.inl rfl) hxP hx'P hxx hx'x'
  obtain ⟨hxN₂, hx'N₂, ⟨k₂, hk₂, hk₂c⟩, -⟩ :=
    comp_facts h44 hII hC hconcl hw1 (A := K₂) (Or.inr rfl) hxP hx'P hxx hx'x'
  have hK₁C : K₁ ≤ Cz z := hM.K₁_le
  have hK₂C : K₂ ≤ Cz z := hM.K₂_le
  have hxC : x ∈ Cz z := hM.S_syl.1 hxS
  have hx'C : x' ∈ Cz z := hM.S_syl.1 hx'S
  have hK₂c : ∀ k ∈ K₂, k ∈ cSec K₁ := fun k hk => hM.cs₁ hk
  have hK₁c : ∀ k ∈ K₁, k ∈ cSec K₂ := fun k hk => hM.cs₂ hk
  have hk₁N₁ : k₁ ∈ normalizer (K₁ : Set G) := le_normalizer hk₁
  have hk₂N₂ : k₂ ∈ normalizer (K₂ : Set G) := le_normalizer hk₂
  have hk₁N₂ : k₁ ∈ normalizer (K₂ : Set G) := cSec_le_normalizer (hK₁c k₁ hk₁)
  have hk₂N₁ : k₂ ∈ normalizer (K₁ : Set G) := cSec_le_normalizer (hK₂c k₂ hk₂)
  obtain ⟨c, hc⟩ : ∃ c : G, c = k₁ * k₂ := ⟨_, rfl⟩
  have hcN₁ : c ∈ normalizer (K₁ : Set G) := by rw [hc]; exact mul_mem hk₁N₁ hk₂N₁
  have hcN₂ : c ∈ normalizer (K₂ : Set G) := by rw [hc]; exact mul_mem hk₁N₂ hk₂N₂
  have hcC : c ∈ Cz z := by rw [hc]; exact mul_mem (hK₁C hk₁) (hK₂C hk₂)
  have hcxN₁ : c * x * c⁻¹ ∈ normalizer (K₁ : Set G) :=
    mul_mem (mul_mem hcN₁ hxN₁) (inv_mem hcN₁)
  have hcxN₂ : c * x * c⁻¹ ∈ normalizer (K₂ : Set G) :=
    mul_mem (mul_mem hcN₂ hxN₂) (inv_mem hcN₂)
  have hphi₁ : phi K₁ (c * x * c⁻¹) hcxN₁ = phi K₁ x' hx'N₁ := by
    have h1 : phi K₁ c hcN₁ = phi K₁ k₁ hk₁N₁ := by
      have h2 : phi K₁ c hcN₁ = phi K₁ (k₁ * k₂) (mul_mem hk₁N₁ hk₂N₁) := phi_congr K₁ hc _ _
      rw [h2, phi_mul K₁ hk₁N₁ hk₂N₁, (phi_eq_one_iff K₁ hk₂N₁).2 (hK₂c k₂ hk₂), mul_one]
    rw [phi_conj_eq K₁ hcN₁ hxN₁, h1, ← phi_conj_eq K₁ hk₁N₁ hxN₁]
    exact hk₁c _
  have hphi₂ : phi K₂ (c * x * c⁻¹) hcxN₂ = phi K₂ x' hx'N₂ := by
    have h1 : phi K₂ c hcN₂ = phi K₂ k₂ hk₂N₂ := by
      have h2 : phi K₂ c hcN₂ = phi K₂ (k₁ * k₂) (mul_mem hk₁N₂ hk₂N₂) := phi_congr K₂ hc _ _
      rw [h2, phi_mul K₂ hk₁N₂ hk₂N₂, (phi_eq_one_iff K₂ hk₁N₂).2 (hK₁c k₁ hk₁), one_mul]
    rw [phi_conj_eq K₂ hcN₂ hxN₂, h1, ← phi_conj_eq K₂ hk₂N₂ hxN₂]
    exact hk₂c _
  have hy1 : c * x * c⁻¹ * x'⁻¹ ∈ cSec K₁ := by
    have hyN : c * x * c⁻¹ * x'⁻¹ ∈ normalizer (K₁ : Set G) := mul_mem hcxN₁ (inv_mem hx'N₁)
    refine (phi_eq_one_iff K₁ hyN).1 ?_
    rw [phi_mul K₁ hcxN₁ (inv_mem hx'N₁), phi_inv_aux K₁ hx'N₁ (inv_mem hx'N₁), hphi₁,
      mul_inv_cancel]
  have hy2 : c * x * c⁻¹ * x'⁻¹ ∈ cSec K₂ := by
    have hyN : c * x * c⁻¹ * x'⁻¹ ∈ normalizer (K₂ : Set G) := mul_mem hcxN₂ (inv_mem hx'N₂)
    refine (phi_eq_one_iff K₂ hyN).1 ?_
    rw [phi_mul K₂ hcxN₂ (inv_mem hx'N₂), phi_inv_aux K₂ hx'N₂ (inv_mem hx'N₂), hphi₂,
      mul_inv_cancel]
  have hyC : c * x * c⁻¹ * x'⁻¹ ∈ Cz z :=
    mul_mem (mul_mem (mul_mem hcC hxC) (inv_mem hcC)) (inv_mem hx'C)
  obtain ⟨-, -, hy1c⟩ := id hy1
  obtain ⟨-, -, hy2c⟩ := id hy2
  have hbr := commutes_mod_O_of_gens hstd hy1c hy2c
  have hFSy : c * x * c⁻¹ * x'⁻¹ ∈ zpowers z ⊔ Oz z := hFS G z S K₁ K₂ hstd hC.std.hQ _ hyC hbr
  rw [sup_comm] at hFSy
  have hzC : z ∈ Cz z := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hzN : z ∈ normalizer ((Oz z : Subgroup G) : Set G) := le_normalizer_Oz le_rfl hzC
  have hex : ∃ e ∈ Cz z, e * x * e⁻¹ * x'⁻¹ ∈ Oz z := by
    rcases CFSG.GH74.GLS.Stage1.Thm3.Sec5.mem_or_mul_inv_mem hzN (by rw [hzz]; exact one_mem _)
      hFSy with hyO | hyO
    · exact ⟨c, hcC, hyO⟩
    · refine ⟨c * d₁, mul_mem hcC (hK₁C hd₁), ?_⟩
      have hcz : c * z * c⁻¹ = z := by
        have := Subgroup.mem_centralizer_singleton_iff.1 hcC
        calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
          _ = z := by group
      have ho₁' : c * o₁ * c⁻¹ ∈ Oz z :=
        Oz_conj hcC (pPrimeCoreOf_le_Oz (hstd.comp_isPCompIn (Or.inl rfl)) ho₁)
      have hey : (c * d₁) * x * (c * d₁)⁻¹ * x'⁻¹ =
          (c * z * c⁻¹) * (c * o₁ * c⁻¹) * (c * x * c⁻¹ * x'⁻¹) := by
        calc (c * d₁) * x * (c * d₁)⁻¹ * x'⁻¹ = c * (d₁ * x * d₁⁻¹) * c⁻¹ * x'⁻¹ := by group
          _ = c * (z * o₁ * x) * c⁻¹ * x'⁻¹ := by rw [hd₁x]
          _ = _ := by group
      rw [hey, hcz]
      set y₀ : G := c * x * c⁻¹ * x'⁻¹ * z⁻¹ with hy₀
      have hy₀O : y₀ ∈ Oz z := hyO
      have hyeq : c * x * c⁻¹ * x'⁻¹ = y₀ * z := by rw [hy₀]; group
      rw [hyeq]
      have hm : z * (c * o₁ * c⁻¹) * (y₀ * z) = (z * ((c * o₁ * c⁻¹) * y₀) * z⁻¹) * (z * z) := by
        group
      rw [hm, hzz, mul_one]
      exact Oz_conj hzC (mul_mem ho₁' hy₀O)
  obtain ⟨e, heC, heO⟩ := hex
  have hx₀2 : (e * x * e⁻¹) * (e * x * e⁻¹) = 1 := by
    calc (e * x * e⁻¹) * (e * x * e⁻¹) = e * (x * x) * e⁻¹ := by group
      _ = 1 := by rw [hxx]; group
  have hx₀1 : e * x * e⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have : x = e⁻¹ * (e * x * e⁻¹) * e := by group
    rw [this, h]
    group
  obtain ⟨g, hg, hgx⟩ := exists_conj_of_mul_mem_odd (O := Oz z) card_Oz_odd hx₀2 hx'x' hx₀1 hx'1
    (fun n hn => Oz_conj hx'C hn) heO
  have hgC : g ∈ Cz z := sup_le (TwoThin.pPrimeCoreOf_le (Cz z)) (zpowers_le.2 hx'C) hg
  refine ⟨g * e, mul_mem hgC heC, ?_⟩
  calc g * e * x * (g * e)⁻¹ = g * (e * x * e⁻¹) * g⁻¹ := by group
    _ = x' := hgx

end MainThm

end CFSG.GH74.GLS.IVK.Lifted
