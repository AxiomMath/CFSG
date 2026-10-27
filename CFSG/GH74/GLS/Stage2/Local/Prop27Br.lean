module

public import CFSG.GH74.GLS.Stage2.Local.Prop27BrAlg
public import CFSG.GH74.GLS.Stage2.Local.Prop27BrTransfer
public import CFSG.GH74.GLS.Stage2.Local.Prop27Cfg
public import CFSG.GH74.GLS.Stage2.Local.Prop27W
public import CFSG.GH74.GLS.Stage2.Local.P34S5Frat
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrNormalClosure
public import CFSG.GH74.GLS.Stage2.Local.P34S5Clo

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27Br

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P27 CFSG.GH74.GLS.Stage2.Local.P34
open scoped commutatorElement

section Perfect

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem Jx_isPerfect (x : G) : Group.IsPerfect ↥(Jx x) := by
  show Group.IsPerfect ↥(pLayerOf 2 (centralizer ({x} : Set G)))
  rw [pLayerOf_eq_map_P34]
  have : Group.IsPerfect ↥(pLayer ↥(centralizer ({x} : Set G)) 2) :=
    Subgroup.isPerfect_iff.mpr (CFSG.ComponentClassification.UnbalancedCorr.pLayer_two_isPerfect _)
  exact Group.IsPerfect.map _

theorem Jx_normalizes (x : G) :
    centralizer ({x} : Set G) ≤ normalizer ((Jx x : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact Jx_normalized x n hn h hh
  · intro hh
    have := Jx_normalized x n⁻¹ (Subgroup.inv_mem _ hn) _ hh
    simpa [mul_assoc] using this

theorem Jx_sylow {T : Subgroup G} {x : G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({x} : Set G))) :
    CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ Jx x) (Jx x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hT.inf_of_le_normalizer (Jx_le_centralizer x) (Jx_normalizes x)

end Perfect

section Main

variable {G : Type} [Group G] [Finite G]

theorem x_mem_commutator_of_mem_Jx {x : G} {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({x} : Set G))) (hxT : x ∈ T)
    (hxJ : x ∈ Jx x) : x ∈ ⁅T ⊓ Jx x, T ⊓ Jx x⁆ := by
  obtain ⟨P, hP⟩ := Jx_sylow hT
  have hxW : x ∈ (P : Subgroup ↥(Jx x)).map (Jx x).subtype := by
    rw [hP]
    exact ⟨hxT, hxJ⟩
  obtain ⟨y, hy, hyx⟩ := hxW
  have hyu : y = ⟨x, hxJ⟩ := Subtype.ext hyx
  rw [hyu] at hy
  have hu : (⟨x, hxJ⟩ : ↥(Jx x)) ∈ Subgroup.center ↥(Jx x) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 (Jx_le_centralizer x g.2)
  have hcomm' := sylow_center_le_commutator (Jx_isPerfect x) P hu hy
  have h := Subgroup.mem_map_of_mem (Jx x).subtype hcomm'
  rw [Subgroup.map_commutator, hP] at h
  exact h

theorem x_not_mem_Jx {x : G} {T T₁ D₂ : Subgroup G} (hx2 : orderOf x = 2)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({x} : Set G))) (hxT : x ∈ T)
    (hcomm : ∀ a ∈ T₁, ∀ b ∈ D₂, a * b = b * a) (hT₁ : ∀ a ∈ T₁, ∀ a' ∈ T₁, a * a' = a' * a)
    (hint : T₁ ⊓ D₂ = ⊥) (hxT₁ : x ∈ T₁) (S1 : ∀ g ∈ T ⊓ Jx x, g ∈ T₁ ⊔ D₂) : x ∉ Jx x := by
  intro hxJ
  have hxc := x_mem_commutator_of_mem_Jx hT hxT hxJ
  have hD₂ : x ∈ D₂ :=
    commutator_sup_le hcomm hT₁ ((Subgroup.commutator_mono (fun g hg => S1 g hg) (fun g hg => S1 g hg)) hxc)
  have : x ∈ T₁ ⊓ D₂ := ⟨hxT₁, hD₂⟩
  rw [hint, Subgroup.mem_bot] at this
  rw [this, orderOf_one] at hx2
  omega

omit [Finite G] in
theorem inf_Jx_le_of_sep {x : G} {T D₂ M : Subgroup G} (hD₂M : D₂ ≤ M) (hMT : M ≤ T)
    (hD₂J : D₂ ≤ Jx x)
    (hsep : ∀ s ∈ T, orderOf s = 2 → s ∉ M →
      s ∉ ⁅centralizer ({x} : Set G), centralizer ({x} : Set G)⁆)
    (hcos : ∀ w ∈ T, w ∉ M → ∃ d ∈ D₂, orderOf (w * d) = 2) : T ⊓ Jx x ≤ M := by
  have hJH : Jx x ≤ ⁅centralizer ({x} : Set G), centralizer ({x} : Set G)⁆ := by
    have h := Subgroup.isPerfect_iff.mp (Jx_isPerfect x)
    have h' : ⁅Jx x, Jx x⁆ ≤ ⁅centralizer ({x} : Set G), centralizer ({x} : Set G)⁆ :=
      Subgroup.commutator_mono (Jx_le_centralizer x) (Jx_le_centralizer x)
    rw [h] at h'
    exact h'
  rintro a ⟨haT, haJ⟩
  by_contra haM
  obtain ⟨d, hd, hord⟩ := hcos a haT haM
  have hsT : a * d ∈ T := T.mul_mem haT (hMT (hD₂M hd))
  have hsJ : a * d ∈ Jx x := (Jx x).mul_mem haJ (hD₂J hd)
  have hsM : a * d ∉ M := fun h => haM (by
    have := M.mul_mem h (M.inv_mem (hD₂M hd))
    simpa using this)
  exact hsep _ hsT hord hsM (hJH hsJ)

theorem x_not_mem_Jx_of_sep {x : G} {T T₁ D₂ M : Subgroup G} (hx2 : orderOf x = 2)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({x} : Set G))) (hxT : x ∈ T)
    (hxT₁ : x ∈ T₁) (hint : T₁ ⊓ D₂ = ⊥) (hD₂M : D₂ ≤ M) (hMT : M ≤ T) (hD₂J : D₂ ≤ Jx x)
    (hsep : ∀ s ∈ T, orderOf s = 2 → s ∉ M →
      s ∉ ⁅centralizer ({x} : Set G), centralizer ({x} : Set G)⁆)
    (hcos : ∀ w ∈ T, w ∉ M → ∃ d ∈ D₂, orderOf (w * d) = 2)
    (hMcomm : ⁅M, M⁆ ≤ D₂) : x ∉ Jx x := by
  intro hxJ
  have hAM := inf_Jx_le_of_sep hD₂M hMT hD₂J hsep hcos
  have hxc := x_mem_commutator_of_mem_Jx hT hxT hxJ
  have hxM : x ∈ ⁅M, M⁆ := Subgroup.commutator_mono hAM hAM hxc
  have : x ∈ T₁ ⊓ D₂ := ⟨hxT₁, hMcomm hxM⟩
  rw [hint, Subgroup.mem_bot] at this
  rw [this, orderOf_one] at hx2
  omega

theorem T₁_inf_Jx {x : G} {T₁ : Subgroup G} (hx2 : orderOf x = 2) (hxJ : x ∉ Jx x)
    (hcyc : IsCyclic ↥T₁) (h2 : IsPGroup 2 ↥T₁) (hxT₁ : x ∈ T₁) : T₁ ⊓ Jx x = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hg1, hg2⟩
  by_contra hg
  have hg' : g ≠ 1 := fun h => hg (by rw [h]; exact Subgroup.one_mem _)
  have := mem_zpowers_of_cyclic_involution hcyc h2 hxT₁ hx2 hg1 hg'
  exact hxJ (Subgroup.zpowers_le.2 hg2 this)

theorem hasDihedralSylowTwo_Jx {x t : G} {T T₁ D₂ : Subgroup G} {n : ℕ}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({x} : Set G)))
    (hcomm : ∀ a ∈ T₁, ∀ b ∈ D₂, a * b = b * a) (hint : T₁ ⊓ D₂ = ⊥)
    (hD₂ : IVK.IsDihedralTwoGroup ↥D₂ n) (hT₁J : T₁ ⊓ Jx x = ⊥)
    (S1 : ∀ g ∈ T ⊓ Jx x, g ∈ T₁ ⊔ D₂) (htT : t ∈ T) (htJ : t ∈ Jx x) (ht2 : orderOf t = 2) :
    CFSG.GorensteinWalter.HasDihedralSylowTwo ↥(Jx x) := by
  obtain ⟨P, hP⟩ := Jx_sylow hT
  have hW : T ⊓ Jx x ≤ T₁ ⊔ D₂ := fun g hg => S1 g hg
  have hWA : (T ⊓ Jx x) ⊓ T₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨⟨-, hgJ⟩, hgT₁⟩
    have : g ∈ T₁ ⊓ Jx x := ⟨hgT₁, hgJ⟩
    rw [hT₁J] at this
    exact this
  obtain ⟨φ, hφ⟩ := exists_injective_hom_of_le_sup hcomm hint hW hWA
  obtain ⟨hn2, k, hk2, hk, ⟨e₂⟩⟩ := hD₂
  have hkk : k = 2 ^ (n - 1) := by
    have : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  subst hkk
  let eP : ↥(P : Subgroup ↥(Jx x)) ≃* ↥(T ⊓ Jx x) :=
    (Subgroup.equivMapOfInjective _ (Jx x).subtype (Jx x).subtype_injective).trans
      (MulEquiv.subgroupCongr hP)
  let ψ : ↥(P : Subgroup ↥(Jx x)) →* DihedralGroup (2 ^ (n - 1)) :=
    e₂.toMonoidHom.comp (φ.comp eP.toMonoidHom)
  have hψ : Function.Injective ψ := e₂.injective.comp (hφ.comp eP.injective)
  have htW : t ∈ T ⊓ Jx x := ⟨htT, htJ⟩
  have htP : (⟨t, htJ⟩ : ↥(Jx x)) ∈ (P : Subgroup ↥(Jx x)) := by
    have : t ∈ (P : Subgroup ↥(Jx x)).map (Jx x).subtype := by
      rw [hP]
      exact htW
    obtain ⟨y, hy, hyt⟩ := this
    have : y = ⟨t, htJ⟩ := Subtype.ext hyt
    rwa [this] at hy
  have hnc : ¬ IsCyclic ↥(P : Subgroup ↥(Jx x)) := by
    intro hcyc
    refine not_isCyclic_sylow_of_perfect (Jx_isPerfect x) P hcyc htP ?_
    intro h
    have := congrArg Subtype.val h
    simp only [OneMemClass.coe_one] at this
    rw [this, orderOf_one] at ht2
    omega
  exact hasDihedralSylowTwo_of_embedding P (by omega) ψ hψ hnc

theorem fusion_of_dihJ {z x t' : G} (hDih : P34.DihJ (HBar (Jx x))) (ht'J : t' ∈ Jx x)
    (ht'2 : orderOf t' = 2) (hxt' : IsConj z (x * t')) :
    ∀ j ∈ Jx x, orderOf j = 2 → IsConj z (x * j) := by
  intro j hj hj2
  obtain ⟨c, hc, hcj⟩ := P34.exists_conj_of_involutions hDih ht'J hj ht'2 hj2
  have hcx : x * c = c * x := (Subgroup.mem_centralizer_singleton_iff.1 (Jx_le_centralizer x hc)).symm
  have h : x * j = c * (x * t') * c⁻¹ := by
    rw [← hcj]
    calc x * (c * t' * c⁻¹) = (x * c) * t' * c⁻¹ := by group
      _ = (c * x) * t' * c⁻¹ := by rw [hcx]
      _ = c * (x * t') * c⁻¹ := by group
  rw [h]
  exact hxt'.trans (isConj_iff.2 ⟨c, rfl⟩)

omit [Finite G] in
theorem dihJ_of_hat {J : Subgroup G}
    (h : (∃ r : ℕ, Odd r ∧ 3 < r ∧ IVK.IsL2 (↥J ⧸ pPrimeCore 2 ↥J) (fun s => s = r)) ∨
      Nonempty ((↥J ⧸ pPrimeCore 2 ↥J) ≃* alternatingGroup (Fin 7))) : P34.DihJ (HBar J) := by
  rcases h with ⟨r, hr, -, ⟨F, iF, fF, hF, e⟩⟩ | hA
  · exact Or.inl ⟨F, iF, fF, by rw [hF]; exact hr, e⟩
  · exact Or.inr hA

end Main

section Weak

variable {G : Type} [Group G] [Finite G]

theorem s1_of_sep {x z : G} {T T₁ D₁ D₂ M : Subgroup G} (hx2 : orderOf x = 2)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({x} : Set G)))
    (hD₁T : D₁ ≤ T) (hD₁n : ∀ s ∈ T, ∀ d ∈ D₁, s * d * s⁻¹ ∈ D₁)
    (hint : D₁ ⊓ D₂ = ⊥) (hT₁D₁ : T₁ ≤ D₁) (hxT₁ : x ∈ T₁) (hcyc : IsCyclic ↥T₁)
    (hz : z ∈ D₁) (hCTz : ∀ g ∈ T, g * z = z * g → g ∈ D₁ ⊔ D₂)
    (hD₂M : D₂ ≤ M) (hMT : M ≤ T) (hD₂J : D₂ ≤ Jx x)
    (hsep : ∀ s ∈ T, orderOf s = 2 → s ∉ M →
      s ∉ ⁅centralizer ({x} : Set G), centralizer ({x} : Set G)⁆)
    (hcos : ∀ w ∈ T, w ∉ M → ∃ d ∈ D₂, orderOf (w * d) = 2) (hMcomm : ⁅M, M⁆ ≤ D₂)
    (hMD₁ : ∀ g ∈ M, g ∈ D₁ → g ∈ T₁) (hMDD : ∀ g ∈ M, g ∈ D₁ ⊔ D₂ → g ∈ T₁ ⊔ D₂) :
    ∀ g ∈ T ⊓ Jx x, g ∈ T₁ ⊔ D₂ := by
  have hxT : x ∈ T := hD₁T (hT₁D₁ hxT₁)
  have hT₁D₂ : T₁ ⊓ D₂ = ⊥ := le_bot_iff.1 ((inf_le_inf_right D₂ hT₁D₁).trans hint.le)
  have hxJ : x ∉ Jx x :=
    x_not_mem_Jx_of_sep hx2 hT hxT hxT₁ hT₁D₂ hD₂M hMT hD₂J hsep hcos hMcomm
  have hT₁J : T₁ ⊓ Jx x = ⊥ :=
    T₁_inf_Jx hx2 hxJ hcyc (hT.isPGroup.to_le (hT₁D₁.trans hD₁T)) hxT₁
  have hAM := inf_Jx_le_of_sep hD₂M hMT hD₂J hsep hcos
  have hTx : T ≤ centralizer ({x} : Set G) := hT.le
  intro g hg
  obtain ⟨hgT, hgJ⟩ := Subgroup.mem_inf.1 hg
  have hzT : z ∈ T := hD₁T hz
  have hc1 : g * z * g⁻¹ * z⁻¹ ∈ D₁ := D₁.mul_mem (hD₁n g hgT z hz) (D₁.inv_mem hz)
  have hzgJ : z * g⁻¹ * z⁻¹ ∈ Jx x := Jx_normalized x z (hTx hzT) g⁻¹ (Subgroup.inv_mem _ hgJ)
  have hc2 : g * z * g⁻¹ * z⁻¹ ∈ Jx x := by
    have h' : g * (z * g⁻¹ * z⁻¹) ∈ Jx x := (Jx x).mul_mem hgJ hzgJ
    simpa [mul_assoc] using h'
  have hzgT : z * g⁻¹ * z⁻¹ ∈ T := T.mul_mem (T.mul_mem hzT (T.inv_mem hgT)) (T.inv_mem hzT)
  have hc3 : g * z * g⁻¹ * z⁻¹ ∈ M := by
    have h' : g * (z * g⁻¹ * z⁻¹) ∈ M :=
      M.mul_mem (hAM ⟨hgT, hgJ⟩) (hAM ⟨hzgT, hzgJ⟩)
    simpa [mul_assoc] using h'
  have hcT₁ : g * z * g⁻¹ * z⁻¹ ∈ T₁ := hMD₁ _ hc3 hc1
  have hcJ : g * z * g⁻¹ * z⁻¹ ∈ T₁ ⊓ Jx x := ⟨hcT₁, hc2⟩
  rw [hT₁J, Subgroup.mem_bot] at hcJ
  have hcomm_gz : g * z = z * g := by
    have h1 : g * z * g⁻¹ = z := by
      calc g * z * g⁻¹ = (g * z * g⁻¹ * z⁻¹) * z := by group
        _ = z := by rw [hcJ, one_mul]
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [h1]
  exact hMDD g (hAM ⟨hgT, hgJ⟩) (hCTz g hgT hcomm_gz)

theorem tr_of_sep {z x : G} {T D₁ D₂ U T₁ M : Subgroup G} {q n : ℕ} {t' : G}
    (hC : P27.Cfg z x T q) (hS : P27.Syl z x T D₁ D₂ U n t') (hI : Ixz z x ≤ Jx x)
    (hT₁D₁ : T₁ ≤ D₁) (hxT₁ : x ∈ T₁) (hcyc : IsCyclic ↥T₁)
    (hcard : Nat.card ↥T₁ * 2 = Nat.card ↥D₂)
    (hCTz : ∀ g ∈ T, g * z = z * g → g ∈ D₁ ⊔ D₂)
    (hD₂M : D₂ ≤ M) (hMT : M ≤ T) (hD₂J : D₂ ≤ Jx x)
    (hsep : ∀ s ∈ T, orderOf s = 2 → s ∉ M →
      s ∉ ⁅centralizer ({x} : Set G), centralizer ({x} : Set G)⁆)
    (hcos : ∀ w ∈ T, w ∉ M → ∃ d ∈ D₂, orderOf (w * d) = 2) (hMcomm : ⁅M, M⁆ ≤ D₂)
    (hMD₁ : ∀ g ∈ M, g ∈ D₁ → g ∈ T₁) (hMDD : ∀ g ∈ M, g ∈ D₁ ⊔ D₂ → g ∈ T₁ ⊔ D₂) :
    P27.Tr z x T D₁ D₂ U T₁ :=
  { I_le_J := hI
    T₁_cyc := hcyc
    T₁_le := hT₁D₁
    x_mem_T₁ := hxT₁
    T₁_card := hcard
    S1 := s1_of_sep hC.x_nc.1 hC.T_syl hS.D₁_le hS.D₁_normal hS.inter hT₁D₁ hxT₁ hcyc hS.z_mem hCTz
      hD₂M hMT hD₂J hsep hcos hMcomm hMD₁ hMDD }

end Weak

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem prop27WJ_of_datum
    {z x : G} (h : P27.Datum z x) : Ixz z x ≠ ⊥ ∧ Prop27WJ z x := by
  obtain ⟨T, D₁, D₂, U, T₁, q, n, t', hC, hS, hT⟩ := h
  have hx2 : orderOf x = 2 := hC.x_nc.1
  have hxT : x ∈ T := hS.D₁_le hS.x_mem
  have hT₁D₁ : T₁ ≤ D₁ := hT.T₁_le
  have hT₁T : T₁ ≤ T := hT₁D₁.trans hS.D₁_le
  have hcomm : ∀ a ∈ T₁, ∀ b ∈ D₂, a * b = b * a := fun a ha b hb => hS.comm a (hT₁D₁ ha) b hb
  have hT₁c : ∀ a ∈ T₁, ∀ a' ∈ T₁, a * a' = a' * a := by
    intro a ha a' ha'
    have := hT.T₁_cyc
    let _ := IsCyclic.commGroup (α := ↥T₁)
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥T₁) ⟨a', ha'⟩)
  have hint : T₁ ⊓ D₂ = ⊥ := le_bot_iff.1 ((inf_le_inf_right D₂ hT₁D₁).trans hS.inter.le)
  have hxJ : x ∉ Jx x := x_not_mem_Jx hx2 hC.T_syl hxT hcomm hT₁c hint hT.x_mem_T₁ hT.S1
  have hT₁J : T₁ ⊓ Jx x = ⊥ :=
    T₁_inf_Jx hx2 hxJ hT.T₁_cyc (hC.T_syl.isPGroup.to_le hT₁T) hT.x_mem_T₁
  have ht'T : t' ∈ T := hS.D₂_le hS.t'_mem
  have ht'I : t' ∈ Ixz z x := hS.U_syl.le hS.t'_U
  have ht'J : t' ∈ Jx x := hT.I_le_J ht'I
  have ht'2 : orderOf t' = 2 := hS.t'_ord
  have hdih := hasDihedralSylowTwo_Jx hC.T_syl hcomm hint hS.D₂_dih hT₁J hT.S1 ht'T ht'J ht'2
  have ht'2' : orderOf (⟨t', ht'J⟩ : ↥(Jx x)) = 2 := by
    rw [← ht'2]
    exact (Subgroup.orderOf_coe _).symm
  have hhat := dihJ_of_perfect_dihedral (Jx_isPerfect x) ht'2' hdih
  refine ⟨?_, hhat, hxJ, fusion_of_dihJ (dihJ_of_hat hhat) ht'J ht'2 hS.xt'_conj⟩
  intro hbot
  have hmem : t' ∈ (⊥ : Subgroup G) := hbot ▸ ht'I
  rw [Subgroup.mem_bot] at hmem
  rw [hmem, orderOf_one] at ht'2
  omega

theorem prop27W_of_datum
    {z : G} {k : Kind} (hd : P27.P27Datum z k)
    (hm : k = Kind.m12 → ∀ x ∈ Cen z, IsNonCentralInvolution x → Prop27WM12 z x) :
    Prop27W z k := by
  refine ⟨fun hcl hx₀ => ?_, hm⟩
  obtain ⟨x, hx⟩ := hd hcl hx₀
  have h := prop27WJ_of_datum hx
  obtain ⟨T, D₁, D₂, U, T₁, q, n, t', hC, -⟩ := hx
  exact ⟨x, hC.x_mem, hC.x_nc, h.1, h.2⟩

@[expose] def Leaf_Prop27WM12
    (Ctx : ∀ (G : Type) [Group G] [Finite G], G → Kind → Subgroup G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Ctx G z k S →
    k = Kind.m12 → ∀ x ∈ Cen z, IsNonCentralInvolution x → Prop27WM12 z x

theorem leaf_prop27W_of_datum
    {Ctx : ∀ (G : Type) [Group G] [Finite G], G → Kind → Subgroup G → Prop}
    (hD : P27.Leaf_P27Datum Ctx) (hM : Leaf_Prop27WM12 Ctx) : Leaf_Prop27W Ctx :=
  fun G _ _ z k S hctx => prop27W_of_datum (hD G z k S hctx) (hM G z k S hctx)

end Assembly

end CFSG.GH74.GLS.Stage2.Local.P27Br
