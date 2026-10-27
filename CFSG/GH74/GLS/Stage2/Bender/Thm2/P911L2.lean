module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Stmt
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Layer
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L2Cross
import CFSG.GH74.GLS.Stage2.Local.P27.QIdCore
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.Bender.Thm1
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

namespace L2Aux

theorem isCyclic_of_odd_dihedral {Y : Type} [Group Y] {d : ℕ} (hY : IsDihedralOrder Y d)
    (W : Subgroup Y) (hW : ∀ w ∈ W, Odd (orderOf w)) : IsCyclic ↥W := by
  obtain ⟨k, -, hk2, ⟨φ⟩⟩ := hY
  have : NeZero k := ⟨by omega⟩
  have hmem : ∀ w ∈ W, φ w ∈ Subgroup.zpowers (DihedralGroup.r (1 : ZMod k)) := by
    intro w hw
    rcases hφ : φ w with i | i
    · refine ⟨((i.val : ℕ) : ℤ), ?_⟩
      change DihedralGroup.r (1 : ZMod k) ^ ((i.val : ℕ) : ℤ) = DihedralGroup.r i
      rw [zpow_natCast, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    · exfalso
      have h1 : orderOf (φ w) = orderOf w := MulEquiv.orderOf_eq φ w
      rw [hφ, DihedralGroup.orderOf_sr] at h1
      have := hW w hw
      rw [← h1] at this
      exact absurd this (by decide)
  have hle : W.map φ.toMonoidHom ≤ Subgroup.zpowers (DihedralGroup.r (1 : ZMod k)) := by
    rintro _ ⟨w, hw, rfl⟩
    exact hmem w hw
  have hcyc : IsCyclic ↥(Subgroup.zpowers (DihedralGroup.r (1 : ZMod k))) := inferInstance
  have h2 : IsCyclic ↥((W.map φ.toMonoidHom).subgroupOf
      (Subgroup.zpowers (DihedralGroup.r (1 : ZMod k)))) := Subgroup.isCyclic _
  have h3 : IsCyclic ↥(W.map φ.toMonoidHom) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hle).surjective
  exact isCyclic_of_surjective (W.equivMapOfInjective φ.toMonoidHom φ.injective).symm.toMonoidHom
    (W.equivMapOfInjective φ.toMonoidHom φ.injective).symm.surjective

theorem three_pow_pm_one_not_dvd {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {d : ℕ}
    (hd : d + 1 = 3 ^ ℓ ∨ d = 3 ^ ℓ + 1) (hdvd : ℓ ∣ d) : False := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hfermat : ((3 : ℕ) : ZMod ℓ) ^ ℓ = ((3 : ℕ) : ZMod ℓ) := ZMod.pow_card _
  have hz : ((d : ℕ) : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff d ℓ).mpr hdvd
  have hdiv : ℓ ∣ 2 ∨ ℓ ∣ 4 → False := by
    rintro (h | h)
    · exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h)
    · have h' : ℓ ∣ 2 ^ 2 := by simpa using h
      exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hℓ.dvd_of_dvd_pow h'))
  rcases hd with h | h
  · have h1 : (((d + 1 : ℕ)) : ZMod ℓ) = ((3 ^ ℓ : ℕ) : ZMod ℓ) := by rw [h]
    rw [Nat.cast_add, hz, Nat.cast_pow, hfermat, Nat.cast_one, zero_add] at h1
    have h2 : ((2 : ℕ) : ZMod ℓ) = 0 := by
      have : ((3 : ℕ) : ZMod ℓ) = ((2 : ℕ) : ZMod ℓ) + 1 := by norm_num
      rw [this] at h1
      have := h1
      linear_combination -this
    exact hdiv (Or.inl ((ZMod.natCast_eq_zero_iff 2 ℓ).mp h2))
  · rw [h] at hz
    rw [Nat.cast_add, Nat.cast_pow, hfermat, Nat.cast_one] at hz
    have h4 : ((4 : ℕ) : ZMod ℓ) = 0 := by
      have : ((4 : ℕ) : ZMod ℓ) = ((3 : ℕ) : ZMod ℓ) + 1 := by norm_num
      rw [this]; exact hz
    exact hdiv (Or.inr ((ZMod.natCast_eq_zero_iff 4 ℓ).mp h4))

theorem layer_L2_ne_bot {F₀ : Type} [Field F₀] [Finite F₀] (h4 : 4 ≤ Nat.card F₀) :
    layer (L2 F₀) ≠ ⊥ := by
  intro h
  have hq := Stage2.Local.P27.QId.isQuasisimple_L2 h4
  have hc : IsComponent (⊤ : Subgroup (L2 F₀)) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq,
      Subgroup.IsSubnormal.top⟩
  have hle : (⊤ : Subgroup (L2 F₀)) ≤ layer (L2 F₀) := le_sSup hc
  rw [h] at hle
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hq
  obtain ⟨a, ha⟩ := exists_ne (1 : L2 F₀)
  exact ha (Subgroup.mem_bot.mp (hle (Subgroup.mem_top a)))


section Classify

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem fixedSubgroup_dihedral_or_pgl (hF : L2Field F) (e : K ≃* L2 F) (α : MulAut K)
    (hα : α * α = 1) (hα1 : α ≠ 1) :
    (∃ d : ℕ, IsDihedralOrder ↥(fixedSubgroup K α) d ∧
      (d + 1 = Nat.card F ∨ d = Nat.card F + 1)) ∨
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ * Nat.card F₀ = Nat.card F ∧
      Nonempty (↥(fixedSubgroup K α) ≃* PGL2 F₀) := by
  classical
  set x : PGammaL2 F := (pgammaAut e).symm α with hx
  have hΦx : pgammaAut e x = α := by simp [hx]
  have hα2 : orderOf α = 2 := orderOf_eq_prime (by rw [sq]; exact hα) hα1
  have hord : orderOf x = 2 := by
    have h := MulEquiv.orderOf_eq (pgammaAut e) x
    rw [hΦx, hα2] at h
    exact h.symm
  obtain ⟨d₁, d₂, ε, hε, hmod, hd₁, hd₂, hd₁'', hd₂''⟩ := exists_eps_d (Nat.card F) hF.1 hF.2
  by_cases hσ : x.right = 1
  · left
    obtain ⟨g, hg⟩ : ∃ g, x = SemidirectProduct.inl g :=
      ⟨x.left, SemidirectProduct.ext (by simp) (by simpa using hσ)⟩
    rw [hg, pgammaAut_inl] at hΦx
    have hαD : α ∈ innDiagSub e := ⟨g, hΦx⟩
    by_cases hin : α ∈ innAut K
    · obtain ⟨u, hu⟩ := hin
      have hu2 : u * u = 1 := by
        have h1 : MulAut.conj (u * u) = (1 : MulAut K) := by rw [map_mul, hu]; exact hα
        exact (conj_injective_of_L2 e) (h1.trans (map_one _).symm)
      have hu1 : u ≠ 1 := by
        rintro rfl
        exact hα1 (by rw [← hu]; simp)
      have hordu : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
      have hdih := (ivk_1_3a F hF K e ε hε hmod d₁ hd₁ u hordu).2.1
      refine ⟨d₁, ?_, hd₁''⟩
      rw [← hu, fixedSubgroup_conj_eq_centralizer]
      exact hdih
    · have hαo : orderOf α = 2 := hα2
      have hdih := (ivk_1_3b F hF K e ε hε hmod d₂ hd₂ α hαD hin hαo).2.1
      exact ⟨d₂, hdih, hd₂''⟩
  · right
    set σ : F ≃+* F := x.right with hσdef
    have hσ2 : orderOf σ = 2 := by
      have hdvd : orderOf σ ∣ orderOf x := orderOf_map_dvd (SemidirectProduct.rightHom) x
      rw [hord] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hσ
      · exact h
    obtain ⟨C, hC⟩ := H90.pgammaL2_involution_conj_inr x hord hσ
    have hαconj : (innDiagHom e C)⁻¹ * α * (innDiagHom e C)⁻¹⁻¹ = fieldAutHom e σ := by
      rw [inv_inv, ← hΦx, ← pgammaAut_inl, ← pgammaAut_inr, ← map_inv, ← map_mul, ← map_mul, hC]
    obtain ⟨F₀, _, _, hq₀, ⟨eP⟩⟩ := isPGL2_fixedSubgroup e σ ⟨1, by rw [hσ2]⟩
    rw [hσ2] at hq₀
    exact ⟨F₀, inferInstance, inferInstance, by rw [← hq₀]; ring,
      ⟨(fixedSubgroupEquivOfConj' hαconj).trans eP⟩⟩

end Classify

end L2Aux

open L2Aux

section Main

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem no911_l2 (hF : L2Field F) (e : K ≃* L2 F) : No911 K := by
  rintro ℓ V z ⟨hℓ, hℓodd, hVe, hVc, hz1, hzz, hVz, ⟨O, hOH, hVO, hOodd, hOz, hON⟩, hH2⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have := hVe
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    exact absurd hℓodd (by decide)
  have hinj := conj_injective_of_L2 e
  have hVexp : ∀ v ∈ V, v ^ ℓ = 1 := fun v hv =>
    elemPow_eq_one_of_isElementaryAbelian (p := ℓ) (A := V) v hv
  obtain ⟨c, hcV, hc1, hcI⟩ := exists_ne_one_inn_of_elem hF e hℓ hℓodd hVe hVc
  set Ei : Subgroup K := V.comap (MulAut.conj : K →* MulAut K) with hEi
  have hfix : ∀ k : K, MulAut.conj k * z = z * MulAut.conj k → k ∈ fixedSubgroup K z := by
    intro k hc
    have h1 : z * MulAut.conj k * z⁻¹ = MulAut.conj k := by
      rw [← hc]; group
    show z k = k
    apply hinj
    rw [← mulAut_conj_conj' z k, h1]
  have hEiz : Ei ≤ fixedSubgroup K z := fun k hk => hfix k (hVz _ hk)
  have hEi1 : Ei ≠ ⊥ := by
    obtain ⟨u, rfl⟩ := hcI
    intro hbot
    have hu : u ∈ Ei := hcV
    rw [hbot, Subgroup.mem_bot] at hu
    exact hc1 (by rw [hu, map_one])
  have hEiexp : ∀ k ∈ Ei, k ^ ℓ = 1 := by
    intro k hk
    apply hinj
    rw [map_pow, map_one]
    exact hVexp _ hk
  have hEiodd : ∀ k ∈ Ei, Odd (orderOf k) := by
    intro k hk
    have hd : orderOf k ∣ ℓ := orderOf_dvd_of_pow_eq_one (hEiexp k hk)
    exact Odd.of_dvd_nat hℓodd hd
  rcases fixedSubgroup_dihedral_or_pgl hF e z hzz hz1 with ⟨d, hdih, hd⟩ | ⟨F₀, _, _, hF₀, ⟨ePGL⟩⟩
  ·
    set M : Subgroup K := fixedSubgroup K z with hM
    have hcycW : IsCyclic ↥(Ei.subgroupOf M) :=
      isCyclic_of_odd_dihedral hdih (Ei.subgroupOf M) (fun w hw => by
        rw [← Subgroup.orderOf_coe]
        exact hEiodd _ (Subgroup.mem_subgroupOf.mp hw))
    have hcycE : IsCyclic ↥Ei :=
      isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEiz).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hEiz).surjective
    have hEiCard : Nat.card ↥Ei = ℓ := by
      obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥Ei)
      have h1 : orderOf g ∣ ℓ := by
        apply orderOf_dvd_of_pow_eq_one
        exact Subtype.ext (hEiexp g g.2)
      rw [hg] at h1
      rcases (Nat.dvd_prime hℓ).mp h1 with h | h
      · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hEi1
      · exact h
    have hVnot : ∃ b ∈ V, b ∉ innAut K := by
      by_contra hcon
      push Not at hcon
      have hVmap : Ei.map (MulAut.conj : K →* MulAut K) = V := by
        rw [hEi, Subgroup.map_comap_eq]
        exact inf_eq_right.mpr (fun v hv => hcon v hv)
      have hcard : Nat.card ↥V = Nat.card ↥Ei := by
        rw [← hVmap, Subgroup.card_map_of_injective hinj]
      rw [hVc, hEiCard] at hcard
      have := hℓ.one_lt
      nlinarith
    obtain ⟨b, hbV, hbI⟩ := hVnot
    have hb1 : b ≠ 1 := fun h => hbI (h ▸ Subgroup.one_mem _)
    have hbD : b ∉ innDiagSub e := fun hD =>
      hbI (mem_innAut_of_odd_pow hF e hD hℓodd (hVexp b hbV))
    obtain ⟨σ, δ, hσ, hδD, hbδ⟩ := exists_conj_fieldAut e hℓ (hVexp b hbV) hbD
    have hH2b : layer ↥(fixedSubgroup K b) = ⊥ := hH2 b hbV hb1
    have hconj : δ⁻¹ * b * δ⁻¹⁻¹ = fieldAutHom e σ := by rw [hbδ]; group
    have hlay : layer ↥(fixedSubgroup K (fieldAutHom e σ)) = ⊥ :=
      layer_eq_bot_of_mulEquiv_of_layer_eq_bot (fixedSubgroupEquivOfConj' hconj) hH2b
    have hoddσ : Odd (orderOf σ) := hσ ▸ hℓodd
    have hlayL : layer (L2 ↥(fixedField σ)) = ⊥ :=
      layer_eq_bot_of_mulEquiv_of_layer_eq_bot (fixedSubgroupEquivL2 e σ hoddσ) hlay
    have hF0odd : Odd (Nat.card ↥(fixedField σ)) := odd_card_fixedField σ hF.1
    have hF0gt : 1 < Nat.card ↥(fixedField σ) := one_lt_card_fixedField σ
    have hF03 : Nat.card ↥(fixedField σ) = 3 := by
      by_contra hne
      have h4 : 4 ≤ Nat.card ↥(fixedField σ) := by
        obtain ⟨m, hm⟩ := hF0odd
        omega
      exact layer_L2_ne_bot h4 hlayL
    have hq : Nat.card F = 3 ^ ℓ := by
      rw [← fixedField_card_pow σ, hσ, hF03]
    have hdvd : ℓ ∣ d := by
      have h1 : Nat.card ↥Ei ∣ Nat.card ↥M := Subgroup.card_dvd_of_le hEiz
      rw [hEiCard, card_of_isDihedralOrder hdih] at h1
      exact h1
    rw [hq] at hd
    exact three_pow_pm_one_not_dvd hℓ hℓ2 hd hdvd
  ·
    set M : Subgroup K := fixedSubgroup K z with hM
    set N₀ : Subgroup K := O.comap (MulAut.conj : K →* MulAut K) with hN₀
    have hN₀M : N₀ ≤ M := fun k hk => hfix k (hOz _ hk)
    have hN₀norm : (N₀.subgroupOf M).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hgz : z (g : K) = g := g.2
      have h1 : z * MulAut.conj (g : K) * z⁻¹ = MulAut.conj (g : K) := by
        rw [mulAut_conj_conj', hgz]
      have hcomm : MulAut.conj (g : K) * z = z * MulAut.conj (g : K) := by
        calc MulAut.conj (g : K) * z = (z * MulAut.conj (g : K) * z⁻¹) * z := by rw [h1]
          _ = z * MulAut.conj (g : K) := by group
      have hconjH : MulAut.conj (g : K) ∈ hbar K V z :=
        (le_trans le_sup_left le_sup_left :
          (MulAut.conj : K →* MulAut K).range ≤ hbar K V z) ⟨g, rfl⟩
      have h2 := hON _ hconjH hcomm _ hn
      show MulAut.conj ((g : K) * (n : K) * (g : K)⁻¹) ∈ O
      simpa [map_mul, map_inv] using h2
    have hN₀odd : Odd (Nat.card ↥(N₀.subgroupOf M)) := by
      have h1 : Nat.card ↥(N₀.subgroupOf M) = Nat.card ↥N₀ :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₀M).toEquiv
      have h2 : Nat.card ↥N₀ ∣ Nat.card ↥O := by
        have hmap : Nat.card ↥(N₀.map (MulAut.conj : K →* MulAut K)) = Nat.card ↥N₀ :=
          Subgroup.card_map_of_injective hinj
        rw [← hmap]
        exact Subgroup.card_dvd_of_le (fun x ⟨k, hk, hkx⟩ => hkx ▸ hk)
      rw [h1]
      exact Odd.of_dvd_nat hOodd h2
    have hF₀odd : Odd (Nat.card F₀) := (Nat.odd_mul.mp (hF₀ ▸ hF.1)).1
    have hpp := isOddPrimePower_of_odd_card hF₀odd
    have hbot := CFSG.DihedralBlueprint.normal_odd_eq_bot_of_pgl2_model F₀ hpp ePGL
      (N₀.subgroupOf M) hN₀norm hN₀odd
    apply hEi1
    rw [eq_bot_iff]
    intro k hk
    have hkN : (⟨k, hEiz hk⟩ : ↥M) ∈ N₀.subgroupOf M := Subgroup.mem_subgroupOf.mpr (hVO hk)
    rw [hbot, Subgroup.mem_bot] at hkN
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hkN)

end Main

theorem exists_L2_model' {Y : Type} [Group Y] (hY : FL2 Y) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), L2Field F ∧ Nonempty (Y ≃* L2 F) := by
  obtain ⟨p₀, f, hp₀, hf, hp₀2, hLie⟩ := hY
  obtain ⟨-, -, -, hpf3, F, _, _, hFcard, ⟨e0⟩⟩ :=
    ComponentClassification.AutL2Facts.lieModel_psl2_data hLie
  have hoddF : Odd (Nat.card F) := by
    rw [hFcard]; exact (hp₀.odd_of_ne_two hp₀2).pow
  have hF3 : 3 < Nat.card F := by
    have h1 : p₀ ≤ p₀ ^ f := Nat.le_self_pow (by omega) p₀
    have h2 : 3 ≤ p₀ := by have := hp₀.two_le; omega
    have h3 : Nat.card F ≠ 3 := by rw [hFcard]; exact hpf3
    have : 3 ≤ Nat.card F := by rw [hFcard]; exact h2.trans h1
    omega
  exact ⟨F, inferInstance, inferInstance, ⟨hoddF, hF3⟩, ⟨e0.trans (L2.equivPSL F).symm⟩⟩

theorem core911_l2 : Core911L2 := by
  intro Y _ _ _ _ hY
  obtain ⟨F, _, _, hFL, ⟨e⟩⟩ := exists_L2_model' hY
  exact no911_l2 hFL e

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
