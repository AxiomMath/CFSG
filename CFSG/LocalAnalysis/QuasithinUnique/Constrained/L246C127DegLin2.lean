module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127DegAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127DegGamma
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127DegNorm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellAlt3
public import CFSG.Quasithin.Background.C116Two.FixModVec

public section

namespace CFSG.QuasithinUnique.L246C127.Deg

open CFSG.Quasithin.C116Two CFSG.QuasithinUnique CFSG.Quasithin CFSG.Open
open scoped commutatorElement

section

variable {G : Type} [Group G] [Finite G]

theorem exists_nontrivial_offender {T K : Subgroup G} {V : Type} [CommGroup V]
    (D : ModData K V) (hK : IsShort2 K) (hKJ : ⁅K, thompsonJ T⁆ = K)
    (hJN : thompsonJ T ≤ Subgroup.normalizer (K : Set G))
    (hAN : ∀ A, IsMaxElemAbelian T A → A ≤ Subgroup.normalizer (K : Set G))
    (hAle : ∀ A, IsMaxElemAbelian T A → A ≤ thompsonJ T)
    (hconj : ∀ (m : G) (hm : m ∈ Subgroup.normalizer (K : Set G)), gammaAut D hm = 1 →
      ∀ u ∈ blockU K, m * u * m⁻¹ = u) :
    ∃ A, ∃ hA : IsMaxElemAbelian T A, ∃ (a : G) (ha : a ∈ A),
      gammaAut D (hAN A hA ha) ≠ 1 := by
  set J := thompsonJ T with hJdef
  by_contra hcon
  push Not at hcon
  let S : Subgroup G :=
    Subgroup.map (Subgroup.normalizer (K : Set G)).subtype (gammaHom D).ker
  have hS : ∀ g, g ∈ S ↔ ∃ hg : g ∈ Subgroup.normalizer (K : Set G), gammaAut D hg = 1 := by
    intro g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hg, h1⟩
      exact ⟨⟨g, hg⟩, h1, rfl⟩
  have hJS : J ≤ S := iSup₂_le fun A hA a ha => (hS a).2 ⟨hAN A hA ha, hcon A hA a ha⟩
  have hJtriv : ∀ j ∈ J, ∀ u ∈ blockU K, j * u * j⁻¹ = u := by
    intro j hj u hu
    obtain ⟨hjn, hj1⟩ := (hS j).1 (hJS hj)
    exact hconj j hjn hj1 u hu
  have hcomm : ⁅K, J⁆ ≤ Subgroup.centralizer (blockU K : Set G) := by
    rw [Subgroup.commutator_le]
    intro k hk j hj
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu₁ : k⁻¹ * u * k ∈ blockU K := by
      have := (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU K (K.inv_mem hk)) u).mp hu
      simpa using this
    have hj1 : j⁻¹ * u = u * j⁻¹ := by
      have := hJtriv j⁻¹ (J.inv_mem hj) u hu
      calc j⁻¹ * u = (j⁻¹ * u * j⁻¹⁻¹) * j⁻¹ := by group
        _ = u * j⁻¹ := by rw [this]
    have hj2 : j * (k⁻¹ * u * k) = (k⁻¹ * u * k) * j := by
      have := hJtriv j hj _ hu₁
      calc j * (k⁻¹ * u * k) = (j * (k⁻¹ * u * k) * j⁻¹) * j := by group
        _ = (k⁻¹ * u * k) * j := by rw [this]
    symm
    simp only [commutatorElement_def]
    calc (k * j * k⁻¹ * j⁻¹) * u
        = k * j * k⁻¹ * (j⁻¹ * u) := by group
      _ = k * j * k⁻¹ * (u * j⁻¹) := by rw [hj1]
      _ = k * j * ((k⁻¹ * u * k) * k⁻¹) * j⁻¹ := by group
      _ = k * (j * (k⁻¹ * u * k)) * k⁻¹ * j⁻¹ := by group
      _ = k * ((k⁻¹ * u * k) * j) * k⁻¹ * j⁻¹ := by rw [hj2]
      _ = u * (k * j * k⁻¹ * j⁻¹) := by group
  rw [hKJ] at hcomm
  have hZU : blockU K ≤ blockZ K := fun u hu =>
    ⟨hu, Subgroup.mem_centralizer_iff.2 fun h hh => (hcomm hh u hu).symm⟩
  exact lt_irrefl _ (lt_of_lt_of_le hK.2.2.2.2.1 hZU)

theorem exists_normFixed_lin2 {P T K : Subgroup G}
    (hKP : IsChiBlock P K) {n : ℕ} (hn : 2 ≤ n) (hlin : IsLin2Type K n)
    (hT2 : IsPGroup 2 T) (hUT : blockU K ≤ T) (hKJ : ⁅K, thompsonJ T⁆ = K) :
    ∃ u ∈ blockU K, u ∉ blockZ K ∧
      ∀ x ∈ T ⊓ Subgroup.normalizer (K : Set G), x * u * x⁻¹ = u := by
  classical
  have hK : IsShort2 K := hKP.1.1
  obtain ⟨F, _, _, D, hcard, hrange⟩ := modData_of_lin2 hlin
  haveI : CharP F 2 := charP_two_of_card (by omega) hcard
  have hq4 : 4 ≤ Fintype.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set J := thompsonJ T with hJdef
  have hJT : J ≤ T := C1GN.thompsonJ_le T
  have hJN : J ≤ Subgroup.normalizer (K : Set G) := by
    have h := A3.le_normalizer_commutator_left J K
    rwa [Subgroup.commutator_comm, hKJ] at h
  have hUe : IsElemAbelian 2 (blockU K) := C5.isElemAbelian_two_iff.2 (C1.elemAb2_blockU hK)
  have hAle : ∀ A, IsMaxElemAbelian T A → A ≤ J := fun A hA => le_iSup₂_of_le A hA le_rfl
  have hAN : ∀ A, IsMaxElemAbelian T A → A ≤ Subgroup.normalizer (K : Set G) :=
    fun A hA a ha => hJN (hAle A hA ha)
  have hoffA : ∀ A, IsMaxElemAbelian T A →
      Nat.card (blockU K) ≤ (A ⊓ Subgroup.centralizer (blockU K : Set G)).relIndex A *
        Nat.card ↥(blockU K ⊓ Subgroup.centralizer (A : Set G)) :=
    fun A hA => card_le_relIndex_mul_card hUe hUT hA
  have hconj : ∀ (m : G) (hm : m ∈ Subgroup.normalizer (K : Set G)), gammaAut D hm = 1 →
      ∀ u ∈ blockU K, m * u * m⁻¹ = u :=
    fun m hm h => conj_eq_of_gammaAut_eq_one D hK hm h
  have hnontriv := exists_nontrivial_offender D hK hKJ hJN hAN hAle hconj
  obtain ⟨A₀, hA₀, a₀, ha₀, hγ₀⟩ := hnontriv
  have hA₀N := hAN A₀ hA₀
  set B₀ := gamB D A₀ hA₀N with hB₀
  have hB₀ne : B₀ ≠ ⊥ := by
    intro h
    apply hγ₀
    have h1 := gammaAut_mem_gamB D hA₀N ha₀
    rw [← hB₀, h, Subgroup.mem_bot] at h1
    exact h1
  have hB₀el : IsElemAbelian 2 B₀ := gamB_isElemAbelian D hA₀N hA₀.2.1
  obtain ⟨hlin₀, hcard₀, ℓ, hℓcard, hℓ⟩ := offender_classification hq4 B₀ hB₀el
    (gamB_normalizes D hrange hA₀N) hB₀ne (offender_transfer D hA₀N hconj (hoffA A₀ hA₀))
  have hJ2 : IsPGroup 2 J := hT2.to_le hJT
  obtain ⟨u₁, hu₁U, hu₁Z, hu₁J⟩ := C116Two.exists_fixMod_ne hKP hJ2 hJN
  set U₁ : ↥(blockU K) := ⟨u₁, hu₁U⟩ with hU₁
  have hlift : ∀ A, IsMaxElemAbelian T A → ∀ a ∈ A, u₁ * a = a * u₁ := fun A hA =>
    lift_fixed D hKP hA.2.1 (hAN A hA) (hoffA A hA) U₁
      (fun a ha => (fixed_iff_comm_mem_blockZ D hK (hAN A hA ha) U₁).2
        (hu₁J a (hAle A hA ha)))
  have hfixu₁ : ∀ a (ha : a ∈ Subgroup.normalizer (K : Set G)), a ∈ J →
      gammaAut D ha (D.β U₁) = D.β U₁ :=
    fun a ha haJ => (fixed_iff_comm_mem_blockZ D hK ha U₁).2 (hu₁J a haJ)
  have hβu₁ne : D.β U₁ ≠ 1 := by
    intro h
    apply hu₁Z
    have : U₁ ∈ D.β.ker := h
    rw [D.ker, Subgroup.mem_subgroupOf] at this
    exact this
  have hx₁ne : Multiplicative.toAdd (D.β U₁) ≠ 0 := fun h => hβu₁ne h
  have hxfix : ∀ A (hA : IsMaxElemAbelian T A), ∀ b ∈ gamB D A (hAN A hA),
      addMap b (Multiplicative.toAdd (D.β U₁)) = Multiplicative.toAdd (D.β U₁) := by
    intro A hA b hb
    obtain ⟨a', ha', rfl⟩ := (mem_gamB D (hAN A hA)).1 hb
    have := hfixu₁ a' (hAN A hA ha') (hAle A hA ha')
    show Multiplicative.toAdd (gammaAut D _ (D.β U₁)) = _
    rw [this]
  have hKC1 : ∀ A (hA : IsMaxElemAbelian T A), ∀ a (ha : a ∈ A), ∀ x ∈ ℓ,
      addMap (gammaAut D (hAN A hA ha)) x = x := by
    intro A hA a ha x hx
    by_cases hBA : gamB D A (hAN A hA) = ⊥
    · have h1 := gammaAut_mem_gamB D (hAN A hA) ha
      rw [hBA, Subgroup.mem_bot] at h1
      rw [h1, addMap_one]
    · obtain ⟨-, -, ℓA, hℓAcard, hℓA⟩ := offender_classification hq4 (gamB D A (hAN A hA))
        (gamB_isElemAbelian D (hAN A hA) hA.2.1) (gamB_normalizes D hrange (hAN A hA)) hBA
        (offender_transfer D (hAN A hA) hconj (hoffA A hA))
      have hx₁A : Multiplicative.toAdd (D.β U₁) ∈ ℓA := (hℓA _).1 (hxfix A hA)
      have hx₁ℓ : Multiplicative.toAdd (D.β U₁) ∈ ℓ := (hℓ _).1 (hxfix A₀ hA₀)
      have hℓeq : ℓA = ℓ :=
        lines_eq_of_inter ℓA ℓ hℓAcard hℓcard _ hx₁ne hx₁A hx₁ℓ
      have hfixA : ∀ b ∈ gamB D A (hAN A hA), addMap b x = x := (hℓA x).2 (hℓeq ▸ hx)
      exact hfixA _ (gammaAut_mem_gamB D (hAN A hA) ha)
  set N : Subgroup G := T ⊓ Subgroup.normalizer (K : Set G) with hNdef
  have hNT : N ≤ T := inf_le_left
  have hNN : N ≤ Subgroup.normalizer (K : Set G) := inf_le_right
  let F' : Subgroup G := blockU K ⊓ Subgroup.centralizer (J : Set G)
  have hF'U : F' ≤ blockU K := inf_le_left
  have hF'comm : ∀ a ∈ F', ∀ b ∈ F', a * b = b * a :=
    fun a ha b hb => (C1.elemAb2_blockU hK).1 a (hF'U ha) b (hF'U hb)
  have hℓne : ℓ ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := exists_ne_zero_mem ℓ hℓcard
    exact (Submodule.ne_bot_iff ℓ).2 ⟨x, hx, hx0⟩
  have hFℓ : ∀ (u : ↥(blockU K)), (u : G) ∈ F' → Multiplicative.toAdd (D.β u) ∈ ℓ := by
    intro u hu
    rw [← hℓ]
    intro b hb
    obtain ⟨a', ha', rfl⟩ := (mem_gamB D hA₀N).1 hb
    have hc : ⁅(u : G), a'⁆ ∈ blockZ K := by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.1 hu.2 a' (hAle A₀ hA₀ ha')).symm]
      exact (blockZ K).one_mem
    have h1 := (fixed_iff_comm_mem_blockZ D hK (hA₀N ha') u).2 hc
    show Multiplicative.toAdd (gammaAut D (hA₀N ha') (D.β u)) = _
    rw [h1]
  have hℓF : ∀ (u : ↥(blockU K)), Multiplicative.toAdd (D.β u) ∈ ℓ → (u : G) ∈ F' := by
    intro u hu
    refine Subgroup.mem_inf.2 ⟨u.2, ?_⟩
    have hJc : J ≤ Subgroup.centralizer ({(u : G)} : Set G) := iSup₂_le fun A hA a ha => by
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      have h1 : ∀ a ∈ A, (u : G) * a = a * (u : G) :=
        lift_fixed D hKP hA.2.1 (hAN A hA) (hoffA A hA) u (fun a ha =>
          Multiplicative.toAdd.injective (hKC1 A hA a ha _ hu))
      exact (h1 a ha).symm
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact Subgroup.mem_centralizer_singleton_iff.1 (hJc hj)
  have hMF : ∀ m ∈ N, ∀ w ∈ F', m * w * m⁻¹ ∈ F' := by
    intro m hm w hw
    refine Subgroup.mem_inf.2 ⟨conj_mem_blockU (hNN hm) (hF'U hw), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hmJ : m⁻¹ * j * m ∈ J := by
      have hmT : m ∈ T := hNT hm
      have hn : m⁻¹ ∈ Subgroup.normalizer (J : Set G) :=
        normalizer_le_normalizer_thompsonJ T (Subgroup.le_normalizer (T.inv_mem hmT))
      have := (Subgroup.mem_normalizer_iff.mp hn j).mp hj
      simpa using this
    have hw' := Subgroup.mem_centralizer_iff.1 hw.2 _ hmJ
    calc j * (m * w * m⁻¹) = m * ((m⁻¹ * j * m) * w) * m⁻¹ := by group
      _ = m * (w * (m⁻¹ * j * m)) * m⁻¹ := by rw [hw']
      _ = (m * w * m⁻¹) * j := by group
  have hℓinv : ∀ m (hm : m ∈ N), ∀ x ∈ ℓ, addMap (gammaAut D (hNN hm)) x ∈ ℓ := by
    intro m hm x hx
    obtain ⟨u₀, hu₀⟩ := D.surj (Multiplicative.ofAdd x)
    have hu₀F : (u₀ : G) ∈ F' := hℓF u₀ (by rw [hu₀]; exact hx)
    have h1 := hFℓ (cU (hNN hm) u₀) (hMF m hm _ hu₀F)
    rw [← gammaAut_apply, hu₀] at h1
    exact h1
  have hpow2 : ∀ m (hm : m ∈ N), ∃ k : ℕ, (gammaAut D (hNN hm)) ^ (2 ^ k) = 1 := by
    intro m hm
    obtain ⟨k, hk⟩ := hT2 (⟨m, hNT hm⟩ : ↥T)
    refine ⟨k, ?_⟩
    have hmk : m ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h := map_pow (gammaHom D) (⟨m, hNN hm⟩ : ↥(Subgroup.normalizer (K : Set G))) (2 ^ k)
    have h1 : (⟨m, hNN hm⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ (2 ^ k) = 1 :=
      Subtype.ext (by simpa using hmk)
    rw [h1, map_one] at h
    exact h.symm
  have hĤ : ∀ m (hm : m ∈ N), (∀ x ∈ ℓ, addMap (gammaAut D (hNN hm)) x = x) →
      ∀ f ∈ F', m * f * m⁻¹ = f := by
    intro m hm hfix f hf
    have hnorm := hNN hm
    obtain ⟨σ, hσ⟩ := exists_semilinear_of_normalizer (gammaAut D hnorm)
      (gammaAut_normalizes D hrange hnorm)
    have hσ1 := linear_of_fixes_line ℓ hℓne _ σ hσ hfix
    have hlinγ : IsSemilinear (RingEquiv.refl F) (gammaAut D hnorm) := hσ1 ▸ hσ
    obtain ⟨k, hk⟩ := hpow2 m hm
    have hmem : gammaAut D hnorm ∈ B₀ :=
      mem_of_linear_fixes_line B₀ hB₀el hlin₀ hcard₀ ℓ hℓcard hℓ _ hlinγ hfix k hk
    obtain ⟨a, ha, hγa⟩ := (mem_gamB D hA₀N).1 hmem
    have hcm := conj_eq_of_gammaAut_eq D hconj hnorm (hA₀N ha) hγa.symm
    rw [hcm f (hF'U hf)]
    have := Subgroup.mem_centralizer_iff.1 hf.2 a (hAle A₀ hA₀ ha)
    calc a * f * a⁻¹ = (f * a) * a⁻¹ := by rw [this]
      _ = f := by group
  let K₀ : Subgroup G := N ⊓ Subgroup.centralizer (F' : Set G)
  have hK₀N : K₀ ≤ N := inf_le_left
  haveI : Finite ↥N := inferInstance
  letI : Fintype (↥N ⧸ K₀.subgroupOf N) := Fintype.ofFinite _
  choose r hr using fun q : ↥N ⧸ K₀.subgroupOf N => QuotientGroup.mk_surjective q
  let g : (↥N ⧸ K₀.subgroupOf N) → MulAut (Multiplicative (Fin 2 → F)) := fun q =>
    gammaAut D (hNN (r q).2)
  have hsem : ∀ q, ∃ σ : F ≃+* F, IsSemilinear σ (g q) := fun q =>
    exists_semilinear_of_normalizer (g q) (gammaAut_normalizes D hrange (hNN (r q).2))
  choose σ hσ using hsem
  have hσinj : Function.Injective σ := by
    intro q q' hqq
    apply transversal_inj N K₀ r hr q q'
    have hmN : ((r q : ↥N) : G)⁻¹ * ((r q' : ↥N) : G) ∈ N :=
      N.mul_mem (N.inv_mem (r q).2) (r q').2
    have hmn := hNN hmN
    have hγm : gammaAut D hmn = (g q)⁻¹ * g q' := by
      rw [show gammaAut D hmn = gammaAut D ((Subgroup.normalizer (K : Set G)).inv_mem
        (hNN (r q).2)) * gammaAut D (hNN (r q').2) from gammaAut_mul D _ _,
        gammaAut_inv D (hNN (r q).2)]
    have hlinm : IsSemilinear (RingEquiv.refl F) (gammaAut D hmn) := by
      rw [hγm]
      have := isSemilinear_mul (isSemilinear_inv (hσ q)) (hσ q')
      have e : ((σ q').trans (σ q).symm) = RingEquiv.refl F := by
        ext c
        simp [hqq]
      rwa [e] at this
    obtain ⟨k, hk⟩ := hpow2 _ hmN
    have hfixm : ∀ x ∈ ℓ, addMap (gammaAut D hmn) x = x :=
      fixes_line_of_linear_two_power ℓ hℓcard _ hlinm (hℓinv _ hmN) k hk
    have hcen := hĤ _ hmN hfixm
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hmN, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have := hcen f hf
    calc f * (((r q : ↥N) : G)⁻¹ * ((r q' : ↥N) : G))
        = (((r q : ↥N) : G)⁻¹ * ((r q' : ↥N) : G) * f *
            (((r q : ↥N) : G)⁻¹ * ((r q' : ↥N) : G))⁻¹) *
            (((r q : ↥N) : G)⁻¹ * ((r q' : ↥N) : G)) := by rw [this]
      _ = (((r q : ↥N) : G)⁻¹ * ((r q' : ↥N) : G)) * f := by group
  haveI : Nonempty (↥N ⧸ K₀.subgroupOf N) := ⟨QuotientGroup.mk 1⟩
  obtain ⟨x, hxℓ, hxne⟩ := exists_trace_ne_zero ℓ hℓne g σ hσ hσinj
  obtain ⟨u₀, hu₀⟩ := D.surj (Multiplicative.ofAdd x)
  have hu₀F : (u₀ : G) ∈ F' := hℓF u₀ (by rw [hu₀]; exact hxℓ)
  have hK₀fix : ∀ k ∈ K₀, k * (u₀ : G) * k⁻¹ = (u₀ : G) := fun k hk => by
    have := Subgroup.mem_centralizer_iff.1 hk.2 (u₀ : G) hu₀F
    rw [← this]
    group
  obtain ⟨hmem, uF, hinv, -, hψ⟩ :=
    exists_norm_fixed N F' K₀ hF'comm hMF hK₀N r hr (u₀ : G) hu₀F hK₀fix
  have hψ' := hψ (V' := Multiplicative (Fin 2 → F)) ((D.β).comp (Subgroup.inclusion hF'U))
  have hterm : ∀ q, ((D.β).comp (Subgroup.inclusion hF'U))
      ⟨(r q : G) * (u₀ : G) * (r q : G)⁻¹, hmem q⟩ = Multiplicative.ofAdd (addMap (g q) x) := by
    intro q
    show D.β ⟨(r q : G) * (u₀ : G) * (r q : G)⁻¹, _⟩ = _
    have h1 : D.β (cU (hNN (r q).2) u₀) = gammaAut D (hNN (r q).2) (D.β u₀) :=
      (gammaAut_apply D _ u₀).symm
    rw [hu₀] at h1
    exact h1
  have hne : (D.β.comp (Subgroup.inclusion hF'U)) uF ≠ 1 := by
    intro h1
    rw [hψ'] at h1
    have h2 := congrArg Multiplicative.toAdd h1
    rw [toAdd_prod] at h2
    simp only [hterm, toAdd_ofAdd, toAdd_one] at h2
    exact hxne h2
  refine ⟨(uF : G), hF'U uF.2, ?_, fun x hx => hinv x hx⟩
  intro hZ
  apply hne
  show D.β ⟨(uF : G), hF'U uF.2⟩ = 1
  have : (⟨(uF : G), hF'U uF.2⟩ : ↥(blockU K)) ∈ D.β.ker := by
    rw [D.ker, Subgroup.mem_subgroupOf]
    exact hZ
  exact this

end

section

variable {G : Type} [Group G] [Finite G]

theorem blockZ_eq_bot_of_alt3 {K : Subgroup G} (hK : IsShort2 K) (h3 : IsAltType K 3) :
    blockZ K = ⊥ := by
  obtain ⟨α, hα, hαk, -⟩ := h3
  have hcard : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 3 := by
    rw [← hαk, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv,
      Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  exact (Setup.Campbell.short_order_three_is_alternating_four hK hcard).2.2.1

theorem exists_normFixed_of_blockZ_eq_bot {T K : Subgroup G} (hK : IsShort2 K)
    (hZ : blockZ K = ⊥) (hT2 : IsPGroup 2 T) :
    ∃ u ∈ blockU K, u ∉ blockZ K ∧
      ∀ x ∈ T ⊓ Subgroup.normalizer (K : Set G), x * u * x⁻¹ = u := by
  have hN2 : IsPGroup 2 ↥(T ⊓ Subgroup.normalizer (K : Set G)) := hT2.to_le inf_le_left
  have hNN : T ⊓ Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (K : Set G) := inf_le_right
  obtain ⟨u, hu, huZ, hfix⟩ := C116Two.exists_fixedCoset_ne (U := blockU K) (Z := blockZ K)
    (J := T ⊓ Subgroup.normalizer (K : Set G)) (C1.isPGroup_blockU hK) hK.2.2.2.2.1 hN2
    (fun j hj _ hx => C116Two.conj_mem_of_mem_normalizer
      (C1.mem_normalizer_blockU (hNN hj)) hx)
    (fun j hj _ hx => C116Two.conj_mem_of_mem_normalizer
      (C1.mem_normalizer_blockZ (hNN hj)) hx)
  refine ⟨u, hu, huZ, fun x hx => ?_⟩
  have h1 := hfix x hx
  rw [hZ, Subgroup.mem_bot] at h1
  have h2 : u * x = x * u := commutatorElement_eq_one_iff_mul_comm.mp h1
  calc x * u * x⁻¹ = (u * x) * x⁻¹ := by rw [← h2]
    _ = u := by group

end

end CFSG.QuasithinUnique.L246C127.Deg
