module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourEightAltPkg
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteenThree
public import CFSG.CGT.PushingUpLit.CGT6.SixFourEightSwap

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem coreAct_three_surjective : Function.Surjective (coreAct 3) := by
  classical
  have hcard : Nat.card ↥(coreMod 3) = 4 := card_coreMod_three'
  have : Fintype ↥(coreMod 3) := Fintype.ofFinite _
  let S : Set ↥(coreMod 3) := {x | x ≠ 1}
  have hS : Nat.card S = 3 := by
    have h1 := Set.card_ne_eq (1 : ↥(coreMod 3))
    have h2 : Fintype.card ↥(coreMod 3) = 4 := by rw [← Nat.card_eq_fintype_card]; exact hcard
    rw [h2, ← Nat.card_eq_fintype_card] at h1
    exact h1
  let r : MulAut ↥(coreMod 3) → Equiv.Perm S := fun g =>
    { toFun := fun s => ⟨g s, fun h => s.2 (g.injective (by rw [h, map_one]))⟩
      invFun := fun s => ⟨g⁻¹ s, fun h => s.2 (g.symm.injective (by simpa using h))⟩
      left_inv := fun s => Subtype.ext (by simp)
      right_inv := fun s => Subtype.ext (by simp) }
  have hr : Function.Injective r := by
    intro g g' hgg
    refine MulEquiv.ext fun x => ?_
    by_cases hx : x = 1
    · rw [hx, map_one, map_one]
    · have := congrArg (fun p : Equiv.Perm S => (p ⟨x, hx⟩ : S).1) hgg
      exact this
  have hle : Nat.card (MulAut ↥(coreMod 3)) ≤ 6 := by
    calc Nat.card (MulAut ↥(coreMod 3)) ≤ Nat.card (Equiv.Perm S) :=
          Nat.card_le_card_of_injective r hr
      _ = 6 := by
        rw [Nat.card_perm, hS]
        decide
  have hinj : Function.Injective (coreAct 3) := coreAct_injective (le_refl 3)
  have hcardP : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  exact (Function.Injective.bijective_of_nat_card_le hinj (by rw [hcardP]; exact hle)).2

theorem coreAct_surjective_of_eq_three {n : ℕ} (hn : n = 3) : Function.Surjective (coreAct n) := by
  subst hn
  exact coreAct_three_surjective

theorem s3_exists_swap : ∀ π : Equiv.Perm (Fin 3), π * π = 1 → π ≠ 1 →
    ∃ i j : Fin 3, i ≠ j ∧ π = Equiv.swap i j := by
  decide

theorem s3_eq_one_or_eq : ∀ σ τ : Equiv.Perm (Fin 3), σ * σ = 1 → τ * τ = 1 → τ ≠ 1 →
    σ * τ = τ * σ → σ = 1 ∨ σ = τ := by
  decide

theorem exists_altPkg_three {Y R : Subgroup G} {T : Sylow 2 G} (h : EightCtx Y T R)
    {φ : (↥Y ⧸ pCore 2 ↥Y) ≃* alternatingGroup (Fin (2 * 1 + 1))}
    (hnat : IsNaturalAltModuleWith ↥Y 1 φ) {A : Subgroup G}
    (hA : IsMaxElemAbelian (T : Subgroup G) A) (hnot : ¬ A ≤ centralizerModCore Y) :
    ∃ (β : ↥(blockU Y) ≃* ↥(coreMod (2 * 1 + 1)))
      (Φ : ↥(Subgroup.normalizer (Y : Set G)) →* Equiv.Perm (Fin (2 * 1 + 1))),
      (∀ (g : ↥(Subgroup.normalizer (Y : Set G))) (w : ↥(blockU Y))
          (hw : (g : G) * w * (g : G)⁻¹ ∈ blockU Y),
          β ⟨(g : G) * w * (g : G)⁻¹, hw⟩ = coreAct (2 * 1 + 1) (Φ g) (β w)) ∧
      (∀ π ∈ alternatingGroup (Fin (2 * 1 + 1)), ∃ y : ↥Y,
        Φ ⟨y, Subgroup.le_normalizer y.2⟩ = (π : Equiv.Perm (Fin (2 * 1 + 1)))) ∧
      (∃ (t : G) (ht : t ∈ A) (i j : Fin (2 * 1 + 1)), i ≠ j ∧
        Φ ⟨t, h.le_normalizer_of_isMax hA ht⟩ = Equiv.swap i j) ∧
      (blockU Y ⊔ (omegaOneCenterIn R ⊓ Subgroup.centralizer (A : Set G)) = omegaOneCenterIn R) ∧
      Nat.card (omegaOneCenterIn R) = wtG (omegaOneCenterIn R) A := by
  classical
  have hY := h.hY.1
  have h3 : 3 ≤ 2 * 1 + 1 := by norm_num
  have hAN : A ≤ Subgroup.normalizer (Y : Set G) := h.le_normalizer_of_isMax hA
  have hUV : blockU Y ≤ omegaOneCenterIn R := h.blockU_le_V
  have hC : Y ⊓ Subgroup.centralizer (blockU Y : Set G) = oTwoIn Y :=
    inf_centralizer_blockU_eq hY h3 hnat
  have hOff : IsOffG (omegaOneCenterIn R) A := h.isOffG hA hnot
  have hCUV : Subgroup.centralizer (omegaOneCenterIn R : Set G) ≤
      Subgroup.centralizer ((blockU Y) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUV)
  have hcard : Nat.card (↥Y ⧸ pCore 2 ↥Y) = 3 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  have hp3 : Nat.Prime 3 := Nat.prime_three
  obtain ⟨x, hxY, hxo⟩ : ∃ x : G, x ∈ Y ∧ orderOf x = 3 := by
    have h3dvd : 3 ∣ Nat.card ↥Y := by
      rw [← hcard]
      exact Subgroup.card_quotient_dvd_card (pCore 2 ↥Y)
    have : Fact (Nat.Prime 3) := ⟨hp3⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 3 h3dvd
    exact ⟨(u : G), u.2, by rw [Subgroup.orderOf_coe]; exact hu⟩
  have hZ : blockZ Y = ⊥ := blockZ_eq_bot_of_prime hY hp3 hcard hxY hxo
  obtain ⟨φ', ψ', hφ's, -, hψ's, hψ'k, hψ'e⟩ := isNatAlt_blockU hY h3 hnat
  have hψ'inj : Function.Injective ψ' := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : w ∈ ψ'.ker := hw
    rw [hψ'k, Subgroup.mem_subgroupOf] at h1
    have h2 : (w : G) ∈ blockZ Y := h1
    rw [hZ, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  let β : ↥(blockU Y) ≃* ↥(coreMod (2 * 1 + 1)) := MulEquiv.ofBijective ψ' ⟨hψ'inj, hψ's⟩
  have hβ : ∀ w, β w = ψ' w := fun w => rfl
  have hbij : Function.Bijective (coreAct (2 * 1 + 1)) :=
    ⟨coreAct_injective h3, coreAct_surjective_of_eq_three rfl⟩
  let cA : Equiv.Perm (Fin (2 * 1 + 1)) ≃* MulAut ↥(coreMod (2 * 1 + 1)) :=
    MulEquiv.ofBijective (coreAct (2 * 1 + 1)) hbij
  let Φ : ↥(Subgroup.normalizer (Y : Set G)) →* Equiv.Perm (Fin (2 * 1 + 1)) :=
    cA.symm.toMonoidHom.comp ((MulAut.congr β).toMonoidHom.comp
      ((conjAct (blockU Y)).comp (Subgroup.inclusion (normalizer_le_normalizer_blockU Y))))
  have hΦc : ∀ g, coreAct (2 * 1 + 1) (Φ g) = MulAut.congr β (conjAct (blockU Y)
      (Subgroup.inclusion (normalizer_le_normalizer_blockU Y) g)) := fun g =>
    cA.apply_symm_apply _
  have hequiv : ∀ (g : ↥(Subgroup.normalizer (Y : Set G))) (w : ↥(blockU Y))
      (hw : (g : G) * w * (g : G)⁻¹ ∈ blockU Y),
      β ⟨(g : G) * w * (g : G)⁻¹, hw⟩ = coreAct (2 * 1 + 1) (Φ g) (β w) := by
    intro g w hw
    rw [hΦc]
    show β ⟨(g : G) * w * (g : G)⁻¹, hw⟩ = β (conjAct (blockU Y)
      (Subgroup.inclusion (normalizer_le_normalizer_blockU Y) g) (β.symm (β w)))
    rw [MulEquiv.symm_apply_apply]
    congr 1
  have hΦ1 : ∀ g : ↥(Subgroup.normalizer (Y : Set G)), Φ g = 1 →
      (g : G) ∈ Subgroup.centralizer (blockU Y : Set G) := fun g hg =>
    mem_centralizer_blockU_of_eq_one β Φ hequiv hg
  have hΦ1' : ∀ g : ↥(Subgroup.normalizer (Y : Set G)),
      (g : G) ∈ Subgroup.centralizer (blockU Y : Set G) → Φ g = 1 := fun g hg =>
    eq_one_of_mem_centralizer_blockU h3 β Φ hequiv hg
  have hΦY : ∀ π ∈ alternatingGroup (Fin (2 * 1 + 1)), ∃ y : ↥Y,
      Φ ⟨y, Subgroup.le_normalizer y.2⟩ = (π : Equiv.Perm (Fin (2 * 1 + 1))) := by
    intro π hπ
    obtain ⟨y, hy⟩ := hφ's ⟨π, hπ⟩
    refine ⟨y, ?_⟩
    apply coreAct_injective h3
    refine MulEquiv.ext fun v => ?_
    obtain ⟨w, rfl⟩ := β.surjective v
    have hw : (y : G) * w * (y : G)⁻¹ ∈ blockU Y :=
      conj_mem_blockU (Subgroup.le_normalizer y.2) w.2
    rw [← hequiv ⟨y, Subgroup.le_normalizer y.2⟩ w hw]
    have := hψ'e y w hw
    rw [hy] at this
    exact this
  have hAsq : ∀ (a : G) (ha : a ∈ A), Φ ⟨a, hAN ha⟩ * Φ ⟨a, hAN ha⟩ = 1 := by
    intro a ha
    rw [← map_mul]
    apply hΦ1'
    have := hOff.2.2.2.1 a ha
    rw [pow_two] at this
    exact hCUV this
  have hAcomm : ∀ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A),
      Φ ⟨a, hAN ha⟩ * Φ ⟨b, hAN hb⟩ = Φ ⟨b, hAN hb⟩ * Φ ⟨a, hAN ha⟩ := by
    intro a ha b hb
    have h1 : Φ ⁅(⟨a, hAN ha⟩ : ↥(Subgroup.normalizer (Y : Set G))), ⟨b, hAN hb⟩⁆ = 1 :=
      hΦ1' _ (hCUV (hOff.2.2.1 a ha b hb))
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  obtain ⟨t, htA, htΦ⟩ : ∃ t : G, ∃ ht : t ∈ A, Φ ⟨t, hAN ht⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hnot
    intro g hg
    exact EightCtx.mem_centralizerModCore_of_centralizer_blockU hC (hAN hg)
      (mem_centralizer_blockU_of_eq_one β Φ hequiv (hcon g hg))
  obtain ⟨i, j, hij, hswap⟩ := s3_exists_swap (Φ ⟨t, hAN htA⟩) (hAsq t htA) htΦ
  have hAim : ∀ (a : G) (ha : a ∈ A), Φ ⟨a, hAN ha⟩ = 1 ∨ Φ ⟨a, hAN ha⟩ = Φ ⟨t, hAN htA⟩ :=
    fun a ha => s3_eq_one_or_eq _ _ (hAsq a ha) (hAsq t htA) htΦ (hAcomm a ha t htA)
  have hAU_R : A ⊓ Subgroup.centralizer (blockU Y : Set G) = A ⊓ R :=
    h.inf_centralizer_blockU_eq_inf hA hC
  let f : ↥A →* Equiv.Perm (Fin (2 * 1 + 1)) := Φ.comp (Subgroup.inclusion hAN)
  have hfker : f.ker = (A ⊓ R).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hAU_R]
    constructor
    · intro ha
      exact ⟨a.2, hΦ1 _ ha⟩
    · rintro ⟨-, ha⟩
      exact hΦ1' _ ha
  have hrange : f.range = Subgroup.zpowers (Φ ⟨t, hAN htA⟩) := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      rcases hAim a a.2 with h1 | h1
      · have : f a = 1 := h1
        rw [this]
        exact Subgroup.one_mem _
      · have : f a = Φ ⟨t, hAN htA⟩ := h1
        rw [this]
        exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨t, htA⟩, rfl⟩
  have hrel : (A ⊓ R).relIndex A = 2 := by
    have h1 : (A ⊓ R).relIndex A = f.ker.index := by
      rw [hfker]
      rfl
    rw [h1, Subgroup.index_ker, hrange, Nat.card_zpowers]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hAsq t htA) htΦ
  have hfix : blockU Y ⊓ Subgroup.centralizer (A : Set G) =
      blockU Y ⊓ Subgroup.centralizer ({t} : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (Subgroup.centralizer_le (by simpa using htA))
    · intro u hu
      obtain ⟨huU, hut⟩ := Subgroup.mem_inf.mp hu
      refine Subgroup.mem_inf.mpr ⟨huU, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      have haN : a ∈ Subgroup.normalizer (Y : Set G) := hAN ha
      have hw : a * u * a⁻¹ ∈ blockU Y := conj_mem_blockU haN huU
      have hw' : t * u * t⁻¹ ∈ blockU Y := conj_mem_blockU (hAN htA) huU
      have htu : t * u = u * t := Subgroup.mem_centralizer_iff.mp hut t (Set.mem_singleton t)
      have hconj : (⟨t * u * t⁻¹, hw'⟩ : ↥(blockU Y)) = ⟨u, huU⟩ := by
        apply Subtype.ext
        show t * u * t⁻¹ = u
        calc t * u * t⁻¹ = (u * t) * t⁻¹ := by rw [htu]
          _ = u := by group
      have hβt : coreAct (2 * 1 + 1) (Φ ⟨t, hAN htA⟩) (β ⟨u, huU⟩) = β ⟨u, huU⟩ := by
        rw [← hequiv ⟨t, hAN htA⟩ ⟨u, huU⟩ hw', hconj]
      have hβa : β ⟨a * u * a⁻¹, hw⟩ = β ⟨u, huU⟩ := by
        rw [hequiv ⟨a, haN⟩ ⟨u, huU⟩ hw]
        rcases hAim a ha with h1 | h1
        · rw [h1]
          rfl
        · rw [h1]
          exact hβt
      have h2 : (⟨a * u * a⁻¹, hw⟩ : ↥(blockU Y)) = ⟨u, huU⟩ := β.injective hβa
      have h3' : a * u * a⁻¹ = u := congrArg Subtype.val h2
      calc a * u = (a * u * a⁻¹) * a := by group
        _ = u * a := by rw [h3']
  have hUcard : Nat.card ↥(blockU Y) =
      (A ⊓ R).relIndex A * Nat.card ↥(blockU Y ⊓ Subgroup.centralizer (A : Set G)) := by
    rw [hrel, hfix, card_fixU_eq β Φ hequiv ⟨t, hAN htA⟩, hswap, Nat.card_congr β.toEquiv]
    exact card_coreMod_eq_two_mul_fix_swap hij h3
  obtain ⟨hsupV, hwtEq⟩ := eight_vpart h hOff hUcard
  exact ⟨β, Φ, hequiv, hΦY, ⟨t, htA, i, j, hij, hswap⟩, hsupV, hwtEq⟩

theorem exists_altPkg' {Y R : Subgroup G} {T : Sylow 2 G} (h : EightCtx Y T R) {a : ℕ} (ha : 1 ≤ a)
    {φ : (↥Y ⧸ pCore 2 ↥Y) ≃* alternatingGroup (Fin (2 * a + 1))}
    (hnat : IsNaturalAltModuleWith ↥Y a φ) {A : Subgroup G}
    (hA : IsMaxElemAbelian (T : Subgroup G) A) (hnot : ¬ A ≤ centralizerModCore Y) :
    ∃ (β : ↥(blockU Y) ≃* ↥(coreMod (2 * a + 1)))
      (Φ : ↥(Subgroup.normalizer (Y : Set G)) →* Equiv.Perm (Fin (2 * a + 1))),
      (∀ (g : ↥(Subgroup.normalizer (Y : Set G))) (w : ↥(blockU Y))
          (hw : (g : G) * w * (g : G)⁻¹ ∈ blockU Y),
          β ⟨(g : G) * w * (g : G)⁻¹, hw⟩ = coreAct (2 * a + 1) (Φ g) (β w)) ∧
      (∀ π ∈ alternatingGroup (Fin (2 * a + 1)), ∃ y : ↥Y,
        Φ ⟨y, Subgroup.le_normalizer y.2⟩ = (π : Equiv.Perm (Fin (2 * a + 1)))) ∧
      (∃ (t : G) (ht : t ∈ A) (i j : Fin (2 * a + 1)), i ≠ j ∧
        Φ ⟨t, h.le_normalizer_of_isMax hA ht⟩ = Equiv.swap i j) ∧
      (blockU Y ⊔ (omegaOneCenterIn R ⊓ Subgroup.centralizer (A : Set G)) = omegaOneCenterIn R) ∧
      Nat.card (omegaOneCenterIn R) = wtG (omegaOneCenterIn R) A := by
  rcases Nat.lt_or_ge a 2 with h1 | h2
  · obtain rfl : a = 1 := by omega
    exact exists_altPkg_three h hnat hA hnot
  · exact exists_altPkg h h2 hnat hA hnot

end CFSG.CGT.PushingUpLit.CGT6
