module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.A6Section
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.MS24
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.ComponentSection
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.L32Tools

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open Module Polynomial CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.RankThree.FFModules
open scoped commutatorElement IsMulCommutative

variable {G : Type*} [Group G]

theorem isPerfect_of_isSimpleGroup {K : Type*} [Group K] [IsSimpleGroup K]
    (h : ∃ a b : K, a * b ≠ b * a) : Group.IsPerfect K := by
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator K) with h1 | h1
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    apply hab
    have h2 : ⁅a, b⁆ ∈ commutator K := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2
  · exact h1

theorem isQuasisimple_of_mulEquiv {K : Type*} [Group K] [IsSimpleGroup K]
    (hK : Subgroup.center K = ⊥) (hnab : ∃ a b : K, a * b ≠ b * a) {L : Subgroup G}
    (eL : ↥L ≃* K) :
    CFSG.IsQuasisimple ↥L ∧ ⁅L, L⁆ = L ∧ Subgroup.center ↥L = ⊥ ∧ ∃ a b : ↥L, a * b ≠ b * a := by
  have hsimpL : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hLnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eL.symm a, eL.symm b, fun h => hab (by simpa using congrArg eL h)⟩
  have hperf : Group.IsPerfect ↥L := isPerfect_of_isSimpleGroup hLnab
  have hcenL : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : eL z ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      obtain ⟨k, rfl⟩ := eL.surjective g
      rw [← map_mul, ← map_mul, hz k]
    rw [hK, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact eL.injective (by rw [h1, map_one])
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
  exact ⟨hq, hLL, hcenL, hLnab⟩

theorem center_alt6 : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
  alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)

theorem isSimpleGroup_alt6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)

theorem exists_ne_comm_alt6 : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a :=
  ⟨c3A6, ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    by decide⟩

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem a6_core [Finite G] [Finite W] (ρ : Representation (ZMod 2) G W)
    (hρ : Function.Injective ρ) {L : Subgroup G} (eL : ↥L ≃* alternatingGroup (Fin 6))
    {A : Subgroup G} (hA2 : CFSG.IsElementaryAbelian 2 ↥A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hLA : ⁅L, A⁆ = L)
    (hb : IsBestOffenderOn ρ A ⊤) :
    ∀ g (hg : g ∈ Subgroup.normalizer (L : Set G)),
      eL.symm.trans ((L.normalizerMonoidHom ⟨g, hg⟩).trans eL) ∈ s6Aut := by
  classical
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have := isSimpleGroup_alt6
  obtain ⟨hq, hLL, -, hLnab⟩ := isQuasisimple_of_mulEquiv center_alt6 exists_ne_comm_alt6 eL
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
  obtain ⟨r, hr3, hrcard, -, -⟩ := a6_section ρ eL hBN hLB hBc hB2 hmin₀ hnt₀ hcen₀ hbud₀
  have hcpos : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
  have hsU : secCod ρ B ⊥ U ≤ r := by
    have h1 : 2 ^ secCod ρ B ⊥ U * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤
        2 ^ r * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := by
      rw [hrcard]
      exact hbudU
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_of_mul_le_mul_right h1 hcpos)
  have hr1 : 1 ≤ r := by
    by_contra h
    have hr0 : r = 0 := by omega
    rw [hr0, pow_zero, one_mul] at hrcard
    have h1 : B ⊓ Subgroup.centralizer (L : Set G) = B :=
      Subgroup.eq_of_le_of_card_ge inf_le_left hrcard.ge
    have h2 : ⁅L, B⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer, ← h1]
      exact inf_le_right
    rw [hLB] at h2
    obtain ⟨a, b, hab⟩ := hLnab
    apply hab
    have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.mp (h2 ▸ a.2))
    have hb' : b = 1 := Subtype.ext (Subgroup.mem_bot.mp (h2 ▸ b.2))
    rw [ha, hb']
  set x : G := ((eL.symm c3A6 : ↥L) : G) with hx
  set y : G := ((eL.symm c33A6 : ↥L) : G) with hy
  have hχ : secChi ρ fA x y ⊥ U ≠ 0 := by
    refine secChi_ne_zero ρ L B hLL fA x y 2 (min r 2) (min r 2) (by norm_num) h₀ hUinv bot_le
      hntU ?_ (by omega) ?_ ?_
    · intro Z₀ Z₁ _ hZ₁ hmin _
      by_cases ht : SecTrivial ρ L Z₀ Z₁
      · exact .inl ⟨ht, secChi_fA_eq_zero_of_secTrivial ρ le_sup_left hmin.1 hmin.2.1
          hmin.2.2.1.le ht (eL.symm c3A6).2 (eL.symm c33A6).2
          (by rw [hx, ← Subgroup.coe_pow, ← map_pow, c3A6_pow_three, map_one, Subgroup.coe_one])
          (by rw [hy, ← Subgroup.coe_pow, ← map_pow, c33A6_pow_three, map_one,
            Subgroup.coe_one])⟩
      · obtain ⟨hcenZ, hbudZ⟩ := hsec Z₀ Z₁ hZ₁ hmin
        obtain ⟨r', -, hr'card, h2r, hχ2⟩ := a6_section ρ eL hBN hLB hBc hB2 hmin ht hcenZ hbudZ
        have hrr : r' = r := by
          have h1 : 2 ^ r' * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) =
              2 ^ r * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := by rw [hr'card, hrcard]
          exact Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_right hcpos h1)
        subst hrr
        rcases hχ2 with h | h
        · exact .inr (.inl ⟨by rw [h]; norm_num, by omega⟩)
        · exact .inr (.inr ⟨by rw [h]; norm_num, by omega⟩)
    · omega
    · omega
  intro g hg
  by_contra hno
  set τ : MulAut ↥L := L.normalizerMonoidHom ⟨g, hg⟩ with hτ
  have hτ_apply : ∀ k : ↥L, ((τ k : ↥L) : G) = g * k * g⁻¹ := fun _ => rfl
  obtain ⟨s, hs⟩ := conj_c3_of_not_mem_s6Aut hno
  have h2 : τ (eL.symm c3A6) = eL.symm s * eL.symm c33A6 * (eL.symm s)⁻¹ := by
    apply eL.injective
    have h3 : (eL.symm.trans (τ.trans eL)) c3A6 = eL (τ (eL.symm c3A6)) := rfl
    rw [← h3, hs]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  have h4 : g * x * g⁻¹ = (eL.symm s : G) * y * (eL.symm s : G)⁻¹ := by
    have := congrArg Subtype.val h2
    rw [hτ_apply] at this
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
  have hk := kerDim_conj ρ fA x h' U (fun u hu => hUN h' hh'N u hu)
    (fun u hu => hUN h'⁻¹ (Subgroup.inv_mem _ hh'N) u hu)
  rw [hconj] at hk
  apply hχ
  unfold secChi
  rw [hk, kerDim_bot, kerDim_bot]
  ring

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
