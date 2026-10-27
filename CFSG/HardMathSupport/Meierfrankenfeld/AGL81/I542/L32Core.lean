module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.L32Section
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.MS24
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.AutFactsL32
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.ComponentSection

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open Module Polynomial CFSG.QuasithinUnique.Setup.Family CFSG.Quasithin.H13.NQTerm
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.RankThree.FFModules
open scoped commutatorElement IsMulCommutative

variable {G : Type*} [Group G]

theorem eq_of_forall_conj_eq {L : Subgroup G} (eL : ↥L ≃* GL32) {x y : ↥L}
    (h : ∀ k ∈ L, (x : G) * k * (x : G)⁻¹ = (y : G) * k * (y : G)⁻¹) : x = y := by
  have hz : eL (y⁻¹ * x) ∈ Subgroup.center GL32 := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := eL.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have h1 := h k k.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (k : G) * ((y : G)⁻¹ * (x : G))
        = (y : G)⁻¹ * ((y : G) * k * (y : G)⁻¹) * (y : G) * ((y : G)⁻¹ * (x : G)) := by group
      _ = (y : G)⁻¹ * ((x : G) * k * (x : G)⁻¹) * (y : G) * ((y : G)⁻¹ * (x : G)) := by rw [h1]
      _ = (y : G)⁻¹ * (x : G) * k := by group
  rw [center_GL32, Subgroup.mem_bot] at hz
  have h2 : y⁻¹ * x = 1 := eL.injective (by rw [hz, map_one])
  exact (inv_mul_eq_one.mp h2).symm

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem l32_inner [Finite G] [Finite W] (ρ : Representation (ZMod 2) G W)
    (hρ : Function.Injective ρ) {L : Subgroup G} (eL : ↥L ≃* GL32) {A : Subgroup G}
    (hA2 : CFSG.IsElementaryAbelian 2 ↥A) (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hLA : ⁅L, A⁆ = L) (hb : IsBestOffenderOn ρ A ⊤) :
    ∀ g ∈ Subgroup.normalizer (L : Set G), ∃ l ∈ L, ∀ k ∈ L, g * k * g⁻¹ = l * k * l⁻¹ := by
  classical
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hsimpL : IsSimpleGroup ↥L := by
    have := isSimpleGroup_gl32
    exact eL.isSimpleGroup
  have hntL : Nontrivial ↥L := by
    have := nontrivial_GL32
    exact eL.toEquiv.nontrivial
  have hperf : Group.IsPerfect ↥L := by
    have := GL32_isPerfect
    exact Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
  have hZL : ∀ z : ↥L, (∀ k : ↥L, z * k = k * z) → z = 1 := by
    intro z hz
    have h1 := eq_of_forall_conj_eq eL (x := z) (y := 1) fun k hk => by
      have h2 := congrArg Subtype.val (hz ⟨k, hk⟩)
      simp only [Subgroup.coe_mul] at h2
      simp only [Subgroup.coe_one, one_mul, inv_one, mul_one]
      rw [h2]
      group
    exact h1
  have hcenL : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    exact hZL z fun k => (Subgroup.mem_center_iff.mp hz k).symm
  have hLnab : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra h
    push Not at h
    obtain ⟨z, hz⟩ := exists_ne (1 : ↥L)
    exact hz (hZL z fun k => h z k)
  let eQ : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hcenL).trans QuotientGroup.quotientBot
  have hq : CFSG.IsQuasisimple ↥L := by
    refine ⟨hperf, eQ.isSimpleGroup, ?_⟩
    obtain ⟨a, b, hab⟩ := hLnab
    exact ⟨eQ.symm a, eQ.symm b, fun h => hab (by simpa using congrArg eQ h)⟩
  have hLL : ⁅L, L⁆ = L := by
    have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥L) (⊤ : Subgroup ↥L) L.subtype
    have h2 : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := by
      have := hperf.commutator_eq_top
      rwa [commutator_def] at this
    rw [h2] at h1
    simpa [Subgroup.map_top, Subgroup.range_subtype] using h1.symm
  have hKnt : ¬ L ≤ cenOn ρ L ⊤ := by
    intro h
    obtain ⟨a, b, hab⟩ := hLnab
    apply hab
    have h1 : ∀ k : ↥L, k = 1 := fun k => by
      apply Subtype.ext
      apply hρ
      ext v
      rw [Subgroup.coe_one, map_one, Module.End.one_apply]
      exact (h k.2).2 v Submodule.mem_top
    rw [h1 a, h1 b]
  obtain ⟨B, hBA, hUinv, hLU, hBU, hbest, hquad, hmove, -⟩ :=
    exists_strictMin_moving (ρ := ρ) L A hA2 hAN hLA hKnt hb
  set U := commOn ρ L ⊤ with hU
  have hAc : ∀ a ∈ A, ∀ c ∈ A, a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥A) ⟨c, hc⟩)
  have hBc : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a := fun a ha c hc => hAc a (hBA ha) c (hBA hc)
  have hB2 : ∀ b ∈ B, b ^ 2 = 1 := fun b hb =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (A := A) b (hBA hb)
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBA.trans hAN
  have hLB : ⁅L, B⁆ = L := by
    refine commutator_eq_of_ne_bot hq hBN fun hbot => ?_
    obtain ⟨b, hb, hbc⟩ := Set.not_subset.mp hBU
    obtain ⟨k, hk, u, -, hne⟩ := hmove b hb hbc
    apply hne
    have h1 : ⁅k, b⁆ ∈ ⁅L, B⁆ := Subgroup.commutator_mem_commutator hk hb
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    rw [← Module.End.mul_apply, ← map_mul, ← h1, map_mul, Module.End.mul_apply]
  have hUU : commOn ρ L (commOn ρ L ⊤) = commOn ρ L ⊤ := commOn_commOn_eq hA2 hAN hLA
  have hcen := ms24_comm ρ hBN hLB hUU hquad
  have hbudU := two_pow_secCod_le hbest hcen
  have h₀ : GeneralFF.IsInvariant ρ (L ⊔ B) ⊥ := fun _ _ u hu => by
    rw [Submodule.mem_bot] at hu ⊢
    rw [hu, map_zero]
  have hntU : ¬ SecTrivial ρ L ⊥ U := by
    intro ht
    apply hLU
    intro k hk
    refine ⟨hk, fun u hu => ?_⟩
    have h1 := ht k hk u hu
    rw [Submodule.mem_bot, sub_eq_zero] at h1
    exact h1
  have hsec : ∀ Z₀ Z₁ : Submodule (ZMod 2) W, Z₁ ≤ U → IsMinSec ρ (L ⊔ B) Z₀ Z₁ →
      (∀ b ∈ B, (∀ k ∈ L, b * k = k * b) → ∀ v ∈ Z₁, ρ b v = v) ∧
      2 ^ secCod ρ B Z₀ Z₁ * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card B := by
    intro Z₀ Z₁ hZ₁ hmin
    refine ⟨fun b hb hbL v hv => hcen b hb hbL v (hZ₁ hv), ?_⟩
    have hmono : secCod ρ B Z₀ Z₁ ≤ secCod ρ B ⊥ U :=
      secCod_mono_sub bot_le hmin.2.2.1.le hZ₁ (isInvariant_mono le_sup_right hmin.1)
        (isInvariant_mono le_sup_right hmin.2.1)
    calc 2 ^ secCod ρ B Z₀ Z₁ * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G))
        ≤ 2 ^ secCod ρ B ⊥ U * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hmono)
      _ ≤ Nat.card B := hbudU
  obtain ⟨Z₀, Z₁, -, hZ₁, hmin₀, hnt₀⟩ :=
    exists_isMinSec_not_secTrivial hLL h₀ hUinv bot_le hntU
  obtain ⟨hcen₀, hbud₀⟩ := hsec Z₀ Z₁ hZ₁ hmin₀
  obtain ⟨hinner, hcardI, -, -⟩ :=
    l32_section ρ eL hBN hLB hBc hB2 hmin₀ hnt₀ hcen₀ hbud₀
  set Bh := innImg L B eL with hBh
  have hcpos : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
  have hBh0 : Bh ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot, one_mul] at hcardI
    have hle : B ≤ Subgroup.centralizer (L : Set G) := by
      have h1 : B ⊓ Subgroup.centralizer (L : Set G) = B :=
        Subgroup.eq_of_le_of_card_ge inf_le_left hcardI.ge
      rw [← h1]
      exact inf_le_right
    have h2 : ⁅L, B⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hle
    rw [hLB] at h2
    obtain ⟨z, hz⟩ := exists_ne (1 : ↥L)
    apply hz
    have : (z : G) ∈ (⊥ : Subgroup G) := h2 ▸ z.2
    exact Subtype.ext (Subgroup.mem_bot.mp this)
  have hconjmul : ∀ (b₁ b₂ : G) (l₁ l₂ : ↥L), (∀ k ∈ L, b₁ * k * b₁⁻¹ = l₁ * k * (l₁ : G)⁻¹) →
      (∀ k ∈ L, b₂ * k * b₂⁻¹ = l₂ * k * (l₂ : G)⁻¹) →
      ∀ k ∈ L, b₁ * b₂ * k * (b₁ * b₂)⁻¹ = ((l₁ * l₂ : ↥L) : G) * k * ((l₁ * l₂ : ↥L) : G)⁻¹ := by
    intro b₁ b₂ l₁ l₂ h₁ h₂ k hk
    have hk' : (l₂ : G) * k * (l₂ : G)⁻¹ ∈ L := L.mul_mem (L.mul_mem l₂.2 hk) (L.inv_mem l₂.2)
    calc b₁ * b₂ * k * (b₁ * b₂)⁻¹ = b₁ * (b₂ * k * b₂⁻¹) * b₁⁻¹ := by group
      _ = b₁ * ((l₂ : G) * k * (l₂ : G)⁻¹) * b₁⁻¹ := by rw [h₂ k hk]
      _ = (l₁ : G) * ((l₂ : G) * k * (l₂ : G)⁻¹) * (l₁ : G)⁻¹ := h₁ _ hk'
      _ = ((l₁ * l₂ : ↥L) : G) * k * ((l₁ * l₂ : ↥L) : G)⁻¹ := by
          simp only [Subgroup.coe_mul]
          group
  have hBhc : ∀ g ∈ Bh, ∀ h ∈ Bh, g * h = h * g := by
    intro g hg h hh
    obtain ⟨b₁, hb₁, h₁⟩ := mem_innImg_iff.mp hg
    obtain ⟨b₂, hb₂, h₂⟩ := mem_innImg_iff.mp hh
    have e := eq_of_forall_conj_eq eL (x := eL.symm g * eL.symm h) (y := eL.symm h * eL.symm g)
      fun k hk => by
        rw [← hconjmul b₁ b₂ _ _ h₁ h₂ k hk, ← hconjmul b₂ b₁ _ _ h₂ h₁ k hk, hBc _ hb₁ _ hb₂]
    apply eL.symm.injective
    rw [map_mul, map_mul, e]
  have hBhsq : ∀ g ∈ Bh, g ^ 2 = 1 := by
    intro g hg
    obtain ⟨b, hb, h₁⟩ := mem_innImg_iff.mp hg
    have e := eq_of_forall_conj_eq eL (x := eL.symm g * eL.symm g) (y := 1) fun k hk => by
      rw [← hconjmul b b _ _ h₁ h₁ k hk, ← pow_two, hB2 b hb]
      simp
    apply eL.symm.injective
    rw [map_pow, pow_two, e, map_one]
  have hfix := GL3_elementary_abelian_fixed_codimensions hBh0 hBhc hBhsq
  have hsU : 2 ^ secCod ρ B ⊥ U ≤ Nat.card Bh := by
    have h1 : 2 ^ secCod ρ B ⊥ U * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤
        Nat.card Bh * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := by
      rw [hcardI]
      exact hbudU
    exact Nat.le_of_mul_le_mul_right h1 hcpos
  obtain ⟨kV, kD, hkV, hkD, hkV2, hkD2, hγ⟩ : ∃ kV kD : ℕ,
      2 ^ kV = Nat.card (fixVec3 Bh) ∧ 2 ^ kD = Nat.card (fixDual3 Bh) ∧ kV ≤ 2 ∧ kD ≤ 2 ∧
        secCod ρ B ⊥ U < (3 - kV) + (3 - kD) := by
    unfold FixedCodimData at hfix
    rcases hfix with ⟨hB2', hV4, hD4, -⟩ | ⟨hB4, hVD, -⟩
    · refine ⟨2, 2, by rw [hV4]; norm_num, by rw [hD4]; norm_num, le_rfl, le_rfl, ?_⟩
      rw [hB2'] at hsU
      have : secCod ρ B ⊥ U ≤ 1 := by
        by_contra h
        push Not at h
        have : 2 ^ 2 ≤ 2 ^ secCod ρ B ⊥ U := Nat.pow_le_pow_right (by norm_num) h
        omega
      omega
    · rw [hB4] at hsU
      have hs2 : secCod ρ B ⊥ U ≤ 2 := by
        by_contra h
        push Not at h
        have : 2 ^ 3 ≤ 2 ^ secCod ρ B ⊥ U := Nat.pow_le_pow_right (by norm_num) h
        omega
      rcases hVD with ⟨hV2, hD4⟩ | ⟨hV4, hD2⟩
      · exact ⟨1, 2, by rw [hV2]; norm_num, by rw [hD4]; norm_num, by norm_num, le_rfl, by omega⟩
      · exact ⟨2, 1, by rw [hV4]; norm_num, by rw [hD2]; norm_num, le_rfl, by norm_num, by omega⟩
  set x : G := ((eL.symm x0 : ↥L) : G) with hx
  set y : G := ((eL.symm x0⁻¹ : ↥L) : G) with hy
  have hχ : secChi ρ fL x y ⊥ U ≠ 0 := by
    refine secChi_ne_zero ρ L B hLL fL x y 3 (3 - kV) (3 - kD) (by norm_num) h₀ hUinv bot_le hntU
      ?_ hγ (by omega) (by omega)
    intro Z₀ Z₁ _ hZ₁ hmin _
    by_cases ht : SecTrivial ρ L Z₀ Z₁
    · exact .inl ⟨ht, secChi_eq_zero_of_secTrivial ρ le_sup_left hmin.1 hmin.2.1 hmin.2.2.1.le ht
        (eL.symm x0).2 (eL.symm x0⁻¹).2 (x0_coe_pow_seven eL) (x0_inv_coe_pow_seven eL)⟩
    · obtain ⟨hcenZ, hbudZ⟩ := hsec Z₀ Z₁ hZ₁ hmin
      obtain ⟨-, -, hle3, hcase⟩ := l32_section ρ eL hBN hLB hBc hB2 hmin ht hcenZ hbudZ
      rcases hcase with ⟨hχ3, hfixV⟩ | ⟨hχ3, hfixD⟩
      · refine .inr (.inl ⟨by rw [hχ3]; norm_num, ?_⟩)
        rw [← hkV] at hfixV
        have := Nat.pow_right_injective le_rfl hfixV
        omega
      · refine .inr (.inr ⟨by rw [hχ3]; norm_num, ?_⟩)
        rw [← hkD] at hfixD
        have := Nat.pow_right_injective le_rfl hfixD
        omega
  intro g hg
  by_contra hno
  push Not at hno
  set τ : MulAut ↥L := L.normalizerMonoidHom ⟨g, hg⟩ with hτ
  have hτ_apply : ∀ k : ↥L, ((τ k : ↥L) : G) = g * k * g⁻¹ := fun _ => rfl
  set σ : MulAut GL32 := eL.symm.trans (τ.trans eL) with hσ
  rcases mulAut_GL32_cases orderOf_x0 σ with ⟨s, hs⟩ | ⟨s, hs⟩
  · obtain ⟨k, hk, hne⟩ := hno _ (eL.symm s).2
    apply hne
    have h1 : σ (eL ⟨k, hk⟩) = s * eL ⟨k, hk⟩ * s⁻¹ := by rw [hs, MulAut.conj_apply]
    have h2 : τ ⟨k, hk⟩ = eL.symm s * ⟨k, hk⟩ * (eL.symm s)⁻¹ := by
      apply eL.injective
      have h3 : σ (eL ⟨k, hk⟩) = eL (τ ⟨k, hk⟩) := by
        simp [hσ]
      rw [← h3, h1]
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    have h4 := congrArg Subtype.val h2
    rw [hτ_apply] at h4
    simpa using h4
  ·
    have h2 : τ (eL.symm x0) = eL.symm s * eL.symm x0⁻¹ * (eL.symm s)⁻¹ := by
      apply eL.injective
      have h3 : σ x0 = eL (τ (eL.symm x0)) := by
        simp [hσ]
      rw [← h3, hs]
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    have hyx : y = x⁻¹ := by rw [hy, hx, map_inv, Subgroup.coe_inv]
    have h4 : g * x * g⁻¹ = (eL.symm s : G) * y * (eL.symm s : G)⁻¹ := by
      have := congrArg Subtype.val h2
      rw [hτ_apply] at this
      rw [hyx]
      simpa using this
    set h' : G := (eL.symm s : G)⁻¹ * g with hh'
    have hconj : h' * x * h'⁻¹ = y := by
      rw [hh']
      calc (eL.symm s : G)⁻¹ * g * x * ((eL.symm s : G)⁻¹ * g)⁻¹
          = (eL.symm s : G)⁻¹ * (g * x * g⁻¹) * (eL.symm s : G) := by group
        _ = y := by rw [h4]; group
    have hh'N : h' ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer (eL.symm s).2)) hg
    have hUN := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.isInvariant_commOn_top ρ
      (K := L) (B := Subgroup.normalizer (L : Set G)) le_rfl
    have hk := kerDim_conj ρ fL x h' U (fun u hu => hUN h' hh'N u hu)
      (fun u hu => hUN h'⁻¹ (Subgroup.inv_mem _ hh'N) u hu)
    rw [hconj] at hk
    apply hχ
    unfold secChi
    rw [hk, kerDim_bot, kerDim_bot]
    ring

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
