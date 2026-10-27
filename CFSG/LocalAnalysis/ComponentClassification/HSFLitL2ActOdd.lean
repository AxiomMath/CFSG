module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2ActBase
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallOutChar
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2ActAssembly

public section

namespace CFSG.ComponentClassification.HSFLit.L2Act

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer GorensteinWalter
open CFSG.ComponentClassification.CatFactsSmall

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {F : Type} [Field F] [Finite F]

theorem exists_l2Data_of_odd (h : Config t L) (e : L ⧸ pPrimeCore 2 L ≃* PSL2 F)
    (hodd : IsOddPrimePower (Nat.card F)) (hgal : ∀ σ : F ≃+* F, ∀ k : ℕ, σ ^ 2 ^ k = 1 → σ = 1)
    (hcard : (Nat.card (PGL2 F)).factorization 2 = 4)
    (T : Sylow 2 ↥(centralizer ({t} : Set X))) : ∃ A : L2Data t L, A.syl = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (L : Set X) with hN
  set Φ := l2Act L e with hΦ
  have hright : ∀ g : N, (g : X) ∈ Config.sylowIn T → (Φ g).right = 1 := by
    intro g hg
    obtain ⟨k, hk⟩ := Config.isPGroup_sylowIn T ⟨g, hg⟩
    apply hgal _ k
    have hgk : g ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    have h1 : (Φ g ^ 2 ^ k).right = (Φ g).right ^ 2 ^ k :=
      map_pow (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F)) (Φ g) (2 ^ k)
    rw [← h1, ← map_pow, hgk, map_one]
    rfl
  set Q : Subgroup (PGL2 F) :=
    (((Config.sylowIn T).subgroupOf N).map Φ).comap SemidirectProduct.inl with hQ
  have hQp : IsPGroup 2 Q :=
    (((Config.isPGroup_sylowIn T).comap_of_injective N.subtype (subtype_injective _)).map
      Φ).comap_of_injective _ SemidirectProduct.inl_injective
  obtain ⟨S, hS⟩ := hQp.exists_le_sylow
  obtain ⟨m, -, ⟨φ₀⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model F hodd S
  have hS16 : Nat.card S = 16 := by
    rw [Sylow.card_eq_multiplicity, hcard]
    norm_num
  have hm : m = 3 := by
    have h1 := Nat.card_congr φ₀.toEquiv
    rw [hS16, DihedralGroup.nat_card] at h1
    have h2 : 2 ^ m = 2 ^ 3 := by omega
    exact Nat.pow_right_injective le_rfl h2
  subst hm
  set φ : (S : Subgroup (PGL2 F)) ≃* DihedralGroup 8 := φ₀ with hφ
  set χ : DihedralGroup 8 →* Multiplicative (ZMod 2) :=
    (chiPGL hodd).comp ((S : Subgroup (PGL2 F)).subtype.comp φ.symm.toMonoidHom) with hχ
  have hχr : χ (DihedralGroup.r 1) ≠ 1 := by
    intro h1
    set s : PGL2 F := (φ.symm (DihedralGroup.r 1) : PGL2 F) with hs
    have hsL : s ∈ pslLayer F := (chiPGL_eq_one_iff hodd s).mp h1
    obtain ⟨y, hy⟩ := hsL
    have hord : orderOf s = 8 := by
      rw [hs, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
    have hy8 : orderOf y = 8 := by
      rw [← hord, ← hy, orderOf_injective _
        Matrix.ProjectiveSpecialLinearGroup.toPGL_injective]
    have hy2 : (e.symm y) ^ 2 ^ 3 = 1 := by
      rw [← map_pow, show 2 ^ 3 = orderOf y by rw [hy8]; norm_num, pow_orderOf_eq_one, map_one]
    have h4 := Config.pow_four_eq_one h hy2
    rw [← map_pow, MulEquiv.map_eq_one_iff] at h4
    have := orderOf_dvd_of_pow_eq_one h4
    rw [hy8] at this
    norm_num at this
  obtain ⟨j₀, hj₀, hj₀D, hj₀t, hj₀R⟩ := exists_dih8_embedding χ hχr
  set P : Subgroup (PGammaL2 F) := (S : Subgroup (PGL2 F)).map SemidirectProduct.inl with hP
  set eP : (S : Subgroup (PGL2 F)) ≃* P :=
    (S : Subgroup (PGL2 F)).equivMapOfInjective _ SemidirectProduct.inl_injective with heP
  have heP_coe : ∀ p : P, (p : PGammaL2 F) = SemidirectProduct.inl (eP.symm p : PGL2 F) := by
    intro p
    conv_lhs => rw [← eP.apply_symm_apply p]
    rfl
  set j : P →* Perm (ZMod 8) := j₀.comp (φ.toMonoidHom.comp eP.symm.toMonoidHom) with hj
  have hjinj : Function.Injective j := hj₀.comp (φ.injective.comp eP.symm.injective)
  have hjH : ∀ p, j p ∈ H8 := fun p => by
    obtain ⟨u, b, -, hub⟩ := hj₀D (φ (eP.symm p))
    exact ⟨u, b, hub⟩
  have hjρ : ∀ p : P, pairHom (deltaPGL hodd) 1 p = typeP (j p) := by
    intro p
    rw [hj, MonoidHom.comp_apply, hj₀t, pairHom_apply, heP_coe, deltaPGL_inl]
    simp only [MonoidHom.one_apply, toAdd_one, hχ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, Subgroup.coe_subtype]
  have hTP : ∀ g : N, (g : X) ∈ Config.sylowIn T → Φ g ∈ P := by
    intro g hg
    have hΦg : Φ g = SemidirectProduct.inl (Φ g).left :=
      SemidirectProduct.ext rfl (by rw [SemidirectProduct.right_inl, hright g hg])
    have hmem : (Φ g).left ∈ Q := by
      change SemidirectProduct.inl (Φ g).left ∈ ((Config.sylowIn T).subgroupOf N).map Φ
      rw [← hΦg]
      exact ⟨g, hg, rfl⟩
    rw [hΦg]
    exact ⟨_, hS hmem, rfl⟩
  have hjR : ∀ (g : N) (hg : (g : X) ∈ Config.sylowIn T ⊓ L), j ⟨Φ g, hTP g hg.1⟩ ∈ R8 := by
    intro g hg
    apply hj₀R
    obtain ⟨y, hy⟩ := l2Act_mem_pslRange e g hg.2
    have h1 : (SemidirectProduct.inl (eP.symm ⟨Φ g, hTP g hg.1⟩ : PGL2 F) : PGammaL2 F) =
        SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y) := by
      rw [← heP_coe]
      exact hy.symm
    have h2 := SemidirectProduct.inl_injective h1
    simp only [hχ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_subtype]
    rw [h2, chiPGL_eq_one_iff]
    exact ⟨y, rfl⟩
  exact exists_l2Data_of_embedding h T Φ (l2Act_eq_one_iff e) (pairHom (deltaPGL hodd) 1) P j
    hjinj hjH hjρ hTP hjR

end CFSG.ComponentClassification.HSFLit.L2Act
