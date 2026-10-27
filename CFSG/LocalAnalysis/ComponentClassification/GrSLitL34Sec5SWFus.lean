module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInvCent
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWNonW

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer

theorem isSylowTwoIn_centralizer {G : Type} [Group G] [Finite G] {a : G} {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hcent : ∀ s ∈ S, s * a = a * s)
    (hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S) :
    IsSylowTwoIn S (centralizer ({a} : Set G)) := by
  obtain ⟨P, hPS⟩ := hSyl
  have hSC : S ≤ centralizer ({a} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.mpr (hcent s hs)
  refine GrS4.isSylowTwoIn_of_not_dvd hSC hS2 fun h => ?_
  rw [← hPS] at h hSC
  exact P.not_dvd_index (h.trans (relIndex_dvd_index_of_le hSC))

theorem exists_conj_of_not_isolated
    {G : Type} [Group G] [Finite G] {a x : G}
    {J S W : Subgroup G} (hset : L34Sec4Setting G a x J S) (hcent : ∀ s ∈ S, s * a = a * s)
    (hWB : ∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W)
    (hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S) {g : G} {E : Subgroup G} (hES : E ≤ S)
    (hE : IsEightGroup E) (hEb : ∀ e ∈ E, e * (g⁻¹ * a * g) = g⁻¹ * a * g * e) {s₀ : G}
    (hs₀S : s₀ ∈ S) (hs₀2 : s₀ * s₀ = 1) (hs₀E : ∀ e ∈ E, s₀ * e = e * s₀) (hs₀n : s₀ ∉ E)
    (hs₀b : s₀ * (g⁻¹ * a * g) = g⁻¹ * a * g * s₀) :
    ∃ m ∈ normalizer (W : Set G), g⁻¹ * a * g = m⁻¹ * a * m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, hS, -, -⟩ := id hset
  have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hS
  set b : G := g⁻¹ * a * g with hbdef
  obtain ⟨hF, -⟩ := GrS4.isElemTwo_sup_zpowers hE.1 hs₀2 hs₀n fun e he => (hs₀E e he).symm
  have hFb : E ⊔ zpowers s₀ ≤ centralizer ({b} : Set G) := sup_le
    (fun e he => mem_centralizer_singleton_iff.mpr (hEb e he))
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hs₀b))
  have hVC : (E ⊔ zpowers s₀).map (MulAut.conj g).toMonoidHom ≤ centralizer ({a} : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    have heb := mem_centralizer_singleton_iff.mp (hFb he)
    rw [mem_centralizer_singleton_iff]
    show g * e * g⁻¹ * a = a * (g * e * g⁻¹)
    have hga : a = g * b * g⁻¹ := by rw [hbdef]; group
    rw [hga, show g * e * g⁻¹ * (g * b * g⁻¹) = g * (e * b) * g⁻¹ by group, heb]
    group
  obtain ⟨c, hcC, hc⟩ := GrS4.exists_conj_mem_of_isSylowTwoIn
    (isSylowTwoIn_centralizer hS2 hcent hSyl) hVC (hF.isPGroup.map _)
  set h : G := g⁻¹ * c with hhdef
  have hFh : ∀ e ∈ E ⊔ zpowers s₀, h⁻¹ * e * h ∈ S := by
    intro e he
    have h1 := hc _ (mem_map_of_mem (MulAut.conj g).toMonoidHom he)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    rw [show h⁻¹ * e * h = c⁻¹ * (g * e * g⁻¹) * c by rw [hhdef]; group]
    exact h1
  have hbh : h⁻¹ * b * h = a := by
    have hca : c⁻¹ * a * c = a := by
      rw [mul_assoc, ← mem_centralizer_singleton_iff.mp hcC, ← mul_assoc, inv_mul_cancel,
        one_mul]
    rw [hhdef, hbdef, show (g⁻¹ * c)⁻¹ * (g⁻¹ * a * g) * (g⁻¹ * c) = c⁻¹ * a * c by group, hca]
  have hEW : wGroup E = W :=
    wGroup_eq_of_not_stronglyIsolated hset hcent hWB hES hE ⟨s₀, hs₀S, hs₀2, hs₀E, hs₀n⟩
  have hE'S : E.map (MulAut.conj h⁻¹).toMonoidHom ≤ S := by
    rintro _ ⟨e, he, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hFh e (mem_sup_left he)
  have hE'8 : IsEightGroup (E.map (MulAut.conj h⁻¹).toMonoidHom) :=
    ⟨hE.1.map_conj _, by rw [card_map_of_injective (MulAut.conj h⁻¹).injective, hE.2]⟩
  have hns : ∃ t ∈ S, t * t = 1 ∧ (∀ e ∈ E.map (MulAut.conj h⁻¹).toMonoidHom, t * e = e * t) ∧
      t ∉ E.map (MulAut.conj h⁻¹).toMonoidHom := by
    refine ⟨h⁻¹ * s₀ * h, hFh s₀ (mem_sup_right (mem_zpowers s₀)), ?_, ?_, ?_⟩
    · rw [show h⁻¹ * s₀ * h * (h⁻¹ * s₀ * h) = h⁻¹ * (s₀ * s₀) * h by group, hs₀2]
      group
    · rintro _ ⟨e, he, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [show h⁻¹ * s₀ * h * (h⁻¹ * e * h) = h⁻¹ * (s₀ * e) * h by group, hs₀E e he]
      group
    · rintro ⟨e, he, hee⟩
      apply hs₀n
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hee
      have : e = s₀ := mul_left_cancel (mul_right_cancel hee)
      rw [← this]
      exact he
  have h1 := wGroup_eq_of_not_stronglyIsolated hset hcent hWB hE'S hE'8 hns
  rw [wGroup_map_conj, hEW] at h1
  refine ⟨h⁻¹, mem_normalizer_iff_map_conj_eq.mpr h1, ?_⟩
  rw [inv_inv, ← hbh]
  group

theorem exists_eight_of_conj
    {G : Type} [Group G] [Finite G] {a x : G} {J S : Subgroup G}
    (hset : L34Sec4Setting G a x J S) (hcent : ∀ s ∈ S, s * a = a * s) {k : G}
    (hkS : k⁻¹ * a * k ∈ S) (hka : k⁻¹ * a * k ≠ a) :
    ∃ c ∈ normalizer (J : Set G) ⊓ centralizer ({a} : Set G), ∃ E : Subgroup G, E ≤ S ∧
      IsEightGroup E ∧ c⁻¹ * (k⁻¹ * a * k) * c ∈ E ∧ a ∈ E ∧
      (k⁻¹ * a * k ∈ withKernel J → E ≤ withKernel J) ∧
      (k⁻¹ * a * k ∉ withKernel J → Nat.card ↥(E ⊓ withKernel J) = 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hU3, hL34, -, hS, -, -⟩ := id hset
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJper : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJa hU3.2.2.2.2.1
  have ha2 : orderOf a = 2 := hU3.1
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  set b : G := k⁻¹ * a * k with hbdef
  have hbb : b * b = 1 := by
    rw [hbdef, show k⁻¹ * a * k * (k⁻¹ * a * k) = k⁻¹ * (a * a) * k by group, haa]
    group
  have hb1 : b ≠ 1 := by
    intro h
    apply ha1
    calc a = k * (k⁻¹ * a * k) * k⁻¹ := by group
      _ = 1 := by rw [← hbdef, h]; group
  obtain ⟨w, hwJ, hww, hwb, hwZ, hwK⟩ :=
    L34Facts.l34InvolutionCentralizerFact G J b hJper hL34 hbb (hS.1 hkS)
  have haK : a ∈ coreActionKernel J := GrS4.mem_coreActionKernel_of_le_centralizer hJa
  have hZJ : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
  have hab : b * a = a * b := hcent b hkS
  have haw : w * a = a * w := mem_centralizer_singleton_iff.mp (hJa hwJ)
  have hE₁ : IsElemTwo (zpowers a) := isElemTwo_zpowers haa
  have hbE₁ : b ∉ zpowers a := fun h => (GrS4.eq_one_or_eq_of_mem_zpowers haa h).elim hb1 hka
  have hcab : ∀ e ∈ zpowers a, e * b = b * e := fun e he => by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp he
    exact Commute.zpow_left hab.symm n
  obtain ⟨hE₂, hE₂c⟩ := GrS4.isElemTwo_sup_zpowers hE₁ hbb hbE₁ hcab
  have hwE₂ : w ∉ zpowers a ⊔ zpowers b := by
    intro hw
    rcases GrS4.mem_or_mul_of_mem_sup_zpowers hbb hcab hw with h | ⟨e, he, rfl⟩
    · rcases GrS4.eq_one_or_eq_of_mem_zpowers haa h with h1 | h1
      · exact hwZ (h1 ▸ one_mem _)
      · apply hwZ
        rw [hZJ, h1]
        exact mem_inf.mpr ⟨h1 ▸ hwJ, haK⟩
    · rcases GrS4.eq_one_or_eq_of_mem_zpowers haa he with h1 | h1
      · apply hwK
        rw [h1, one_mul, inv_mul_cancel]
        exact one_mem _
      · apply hwK
        rw [h1, show (a * b)⁻¹ * b = a⁻¹ by rw [← hab]; group, inv_eq_of_mul_eq_one_right haa]
        exact haK
  have hcw : ∀ e ∈ zpowers a ⊔ zpowers b, e * w = w * e := by
    have hle : zpowers a ⊔ zpowers b ≤ centralizer ({w} : Set G) := sup_le
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr haw.symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hwb.symm))
    exact fun e he => mem_centralizer_singleton_iff.mp (hle he)
  obtain ⟨hE₃, hE₃c⟩ := GrS4.isElemTwo_sup_zpowers hE₂ hww hwE₂ hcw
  set E₀ : Subgroup G := zpowers a ⊔ zpowers b ⊔ zpowers w with hE₀def
  have hcardE₀ : Nat.card E₀ = 8 := by rw [hE₃c, hE₂c, Nat.card_zpowers, ha2]
  have hE₀N : E₀ ≤ normalizer (J : Set G) ⊓ centralizer ({a} : Set G) :=
    sup_le (sup_le (zpowers_le.mpr ⟨GrS4.mem_normalizer_of_le_centralizer hJa,
      mem_centralizer_singleton_iff.mpr rfl⟩)
      (zpowers_le.mpr ⟨hS.1 hkS, mem_centralizer_singleton_iff.mpr hab⟩))
      (zpowers_le.mpr ⟨le_normalizer hwJ, hJa hwJ⟩)
  have hSNa : IsSylowTwoIn S (normalizer (J : Set G) ⊓ centralizer ({a} : Set G)) :=
    GrS4.isSylowTwoIn_of_le hS (le_inf hS.1 fun s hs =>
      mem_centralizer_singleton_iff.mpr (hcent s hs)) inf_le_left
  obtain ⟨c, hc, hcS⟩ := GrS4.exists_conj_mem_of_isSylowTwoIn hSNa hE₀N hE₃.isPGroup
  have hcN : c ∈ normalizer (J : Set G) := (mem_inf.mp hc).1
  have hca : c⁻¹ * a * c = a := by
    have := mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2
    rw [mul_assoc, ← this, inv_mul_cancel_left]
  have hcK : ∀ y ∈ withKernel J, c⁻¹ * y * c ∈ withKernel J := fun y hy => by
    have := GrS4.map_conj_withKernel_le (inv_mem hcN)
      (mem_map_of_mem (MulAut.conj c⁻¹).toMonoidHom hy)
    simpa [MulAut.conj_apply] using this
  have hK0 : zpowers a ⊔ zpowers w ≤ withKernel J :=
    sup_le (zpowers_le.mpr (mem_sup_right haK)) (zpowers_le.mpr (mem_sup_left hwJ))
  set E : Subgroup G := E₀.map (MulAut.conj c⁻¹).toMonoidHom with hEdef
  have hconj : ∀ y, (MulAut.conj c⁻¹).toMonoidHom y = c⁻¹ * y * c := fun y => by simp
  refine ⟨c, hc, E, ?_, ⟨hE₃.map_conj _, ?_⟩, ⟨b, mem_sup_left (mem_sup_right (mem_zpowers b)),
    hconj b⟩, ⟨a, mem_sup_left (mem_sup_left (mem_zpowers a)), by rw [hconj, hca]⟩, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    rw [hconj]
    exact hcS e he
  · rw [hEdef, card_map_of_injective (MulAut.conj c⁻¹).injective, hcardE₀]
  · intro hbK
    rintro _ ⟨e, he, rfl⟩
    rw [hconj]
    exact hcK e ((sup_le (sup_le (zpowers_le.mpr (mem_sup_right haK)) (zpowers_le.mpr hbK))
      (zpowers_le.mpr (mem_sup_left hwJ)) : E₀ ≤ withKernel J) he)
  · intro hbK
    have hw₁ : w ∉ zpowers a := fun h => hwE₂ (mem_sup_left h)
    obtain ⟨-, hF₀c⟩ := GrS4.isElemTwo_sup_zpowers hE₁ hww hw₁ fun e he => by
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp he
      exact Commute.zpow_left haw.symm n
    have hF₀E : (zpowers a ⊔ zpowers w).map (MulAut.conj c⁻¹).toMonoidHom ≤ E ⊓ withKernel J :=
      le_inf (map_mono (sup_le (le_sup_left.trans le_sup_left) le_sup_right)) (by
        rintro _ ⟨e, he, rfl⟩
        rw [hconj]
        exact hcK e (hK0 he))
    have h4 : 4 ≤ Nat.card ↥(E ⊓ withKernel J) := by
      have := Subgroup.card_le_of_le hF₀E
      rw [card_map_of_injective (MulAut.conj c⁻¹).injective, hF₀c, Nat.card_zpowers, ha2] at this
      exact this
    have hdvd : Nat.card ↥(E ⊓ withKernel J) ∣ 8 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : E ⊓ withKernel J ≤ E)
      rwa [hEdef, card_map_of_injective (MulAut.conj c⁻¹).injective, hcardE₀] at this
    have hne : Nat.card ↥(E ⊓ withKernel J) ≠ 8 := fun h8 => hbK (by
      have hEK : E ⊓ withKernel J = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by
        rw [h8, hEdef, card_map_of_injective (MulAut.conj c⁻¹).injective, hcardE₀])
      have hb' : c⁻¹ * b * c ∈ withKernel J := by
        have hbE : c⁻¹ * b * c ∈ E :=
          ⟨b, mem_sup_left (mem_sup_right (mem_zpowers b)), hconj b⟩
        rw [← hEK] at hbE
        exact (mem_inf.mp hbE).2
      have := GrS4.map_conj_withKernel_le hcN (mem_map_of_mem (MulAut.conj c).toMonoidHom hb')
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      rwa [show c * (c⁻¹ * b * c) * c⁻¹ = b by group] at this)
    obtain ⟨n, hn, hn'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card ↥(E ⊓ withKernel J) ∣ 2 ^ 3 by norm_num; exact hdvd)
    interval_cases n <;> simp only [Nat.reducePow] at hn' <;> omega

end CFSG.ComponentClassification.GrSLit.GrS5S
