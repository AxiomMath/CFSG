module

public import CFSG.ClassicalInvolution.Asc77.AscBSE1
public import CFSG.ClassicalInvolution.Asc77.AscBSE5

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC.BSE

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.BSC.BSD
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => CFSG.ClassicalInvolution.Generic.CoreAssembly.conjClass

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}


theorem oddQuotMk_eq_one_of_mem_oddCoreIn_layer (C : XCtx p f (𝒞 K) z) {o : G}
    (ho : o ∈ oddCoreIn (exactLayer (𝒞 K) z)) (hoC : o ∈ Subgroup.centralizer ({z} : Set G)) :
    oddQuotMk z ⟨o, hoC⟩ = 1 := by
  obtain ⟨hoY, hoO⟩ := mem_oddCoreOf_iff.mp ho
  have h1 : (layerToOddQuot (exactFamily (𝒞 K) z) z) ⟨o, hoY⟩ = 1 := by
    rw [← MonoidHom.mem_ker, ker_layerToOddQuot_of_normalizes C.hs.normalizes]
    exact hoO
  rwa [layerToOddQuot_apply] at h1

theorem false_of_d4_four {C : XCtx p f (𝒞 K) z}
    (hno : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) {b : Fin C.D.card}
    (hD4 : C.D.tag b = .POmegaPlus) (hrank : C.D.rank b = 4) (hcard : C.D.card = 4) : False := by
  have hb : ¬ (C.D.tag b = .PSL ∧ C.D.rank b = 2) := fun h => by
    rw [hD4] at h
    exact absurd h.1 (by decide)
  have hbG2 : C.D.tag b ≠ .G2 := by rw [hD4]; decide
  have hbD4 : C.D.tag b ≠ .trialityD4 := by rw [hD4]; decide
  obtain ⟨g, N, hinj, hN, hcomp⟩ := exists_conj_twins_complete hno hb
  obtain ⟨j₀, hj₀, -⟩ := C.exists_A1_of_K
  have hj₀b : j₀ ≠ b := fun h => hb (h ▸ hj₀)
  obtain ⟨c, d, hcd, hcj, hcb, hdj, hdb⟩ :=
    exists_two_ne_of_three_lt (by omega : 3 < C.D.card) j₀ b hj₀b
  let i₀ : {j : Fin C.D.card // j ≠ b} := ⟨j₀, hj₀b⟩
  let i₁ : {j : Fin C.D.card // j ≠ b} := ⟨c, hcb⟩
  let i₂ : {j : Fin C.D.card // j ≠ b} := ⟨d, hdb⟩
  have hall : ∀ j : {j : Fin C.D.card // j ≠ b}, j = i₀ ∨ j = i₁ ∨ j = i₂ := by
    have hT : ({b, j₀, c, d} : Finset (Fin C.D.card)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hj₀b.symm, hcb.symm, hdb.symm]),
        Finset.card_insert_of_notMem (by simp [hcj.symm, hdj.symm]), Finset.card_pair hcd]
    have hS : ({b, j₀, c, d} : Finset (Fin C.D.card)) = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [hT, Fintype.card_fin]; exact hcard.symm)
    intro j
    have hj : j.1 ∈ ({b, j₀, c, d} : Finset (Fin C.D.card)) := by rw [hS]; exact Finset.mem_univ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with h | h | h | h
    · exact absurd h j.2
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  have h01 : N i₀ ≠ N i₁ := fun h => hcj (congrArg Subtype.val (hinj h)).symm
  have h02 : N i₀ ≠ N i₂ := fun h => hdj (congrArg Subtype.val (hinj h)).symm
  have h12 : N i₁ ≠ N i₂ := fun h => hcd (congrArg Subtype.val (hinj h))
  obtain ⟨h0tq, h0cl, R₀, hR₀, himg₀, r₀, hr₀R, hm₀, hr₀⟩ := hN i₀
  obtain ⟨h1tq, h1cl, R₁, hR₁, himg₁, r₁, hr₁R, hm₁, hr₁⟩ := hN i₁
  obtain ⟨h2tq, h2cl, R₂, hR₂, himg₂, r₂, hr₂R, hm₂, hr₂⟩ := hN i₂
  set m : G := g⁻¹ * z * g with hmdef
  have hmsq : m * m = 1 := (isCentralInvolution_of_isClassicalMember h0cl).sq
  have hm1 : m ≠ 1 := (isCentralInvolution_of_isClassicalMember h0cl).ne_one
  have hi₀ := isInvIn_of_psi_eq hb hR₀ hr₀R hm₀ hmsq hm1 hr₀
  have hi₁ := isInvIn_of_psi_eq hb hR₁ hr₁R hm₁ hmsq hm1 hr₁
  have hi₂ := isInvIn_of_psi_eq hb hR₂ hr₂R hm₂ hmsq hm1 hr₂
  have hexp : C.D.exp b = f := C.exp_eq b hbD4
  have hq : 5 ≤ p ^ C.D.exp b := by rw [hexp]; exact C.hq
  have hne₀₁ : R₀ ≠ R₁ := fun h => h01 ((hN i₀).eq_of_fund_eq (hN i₁) himg₀ himg₁ h)
  have hne₀₂ : R₀ ≠ R₂ := fun h => h02 ((hN i₀).eq_of_fund_eq (hN i₂) himg₀ himg₂ h)
  have hne₁₂ : R₁ ≠ R₂ := fun h => h12 ((hN i₁).eq_of_fund_eq (hN i₂) himg₁ himg₂ h)
  obtain ⟨R₃, hR₃, n0, n1, n2, r₃, hi₃, hψ₃⟩ := exists_fourth_fund_plus (p := p) C.hp hq hD4 hrank
    (C.D.admissible b) (C.psi b) (C.psi_ker b) hR₀ hR₁ hR₂ hne₀₁ hne₀₂ hne₁₂ hi₀ hi₁ hi₂
    (hr₀.trans hr₁.symm) (hr₁.trans hr₂.symm)
  obtain ⟨N₃, hN₃, himg₃⟩ := C.exists_member_of_fund b (C.single b hbG2 hbD4) hR₃
  obtain ⟨n₃, hn₃⟩ := C.hΩ.classical N₃ hN₃.1
  have hn₃E : n₃ ∈ exactCore z N₃ := C.involution_mem_exactCore hN₃ hn₃
  have hn₃C : n₃ ∈ Subgroup.centralizer ({z} : Set G) := C.involution_mem_centralizer hN₃ hn₃
  have hn₃2 : n₃ * n₃ = 1 := (isCentralInvolution_of_isClassicalMember hn₃).sq
  have hn₃1 : n₃ ≠ 1 := (isCentralInvolution_of_isClassicalMember hn₃).ne_one
  obtain ⟨x, hxR, hx⟩ : oddQuotMk z ⟨n₃, hn₃C⟩ ∈ R₃.map (C.psi b) :=
    himg₃ ▸ oddQuotMk_mem_modOdd hn₃E hn₃C
  have hxinv := isInvIn_of_psi_eq hb hR₃ hxR hn₃C hn₃2 hn₃1 hx
  have hxr₃ : x = r₃ :=
    inv_unique C.hp hq (C.D.isFundTag b) (C.D.admissible b) hbG2 hbD4 hR₃ hxinv hi₃
  have hn₃m : oddQuotMk z ⟨n₃, hn₃C⟩ = oddQuotMk z ⟨m, hm₀⟩ := by
    rw [← hx, hxr₃, hψ₃, hr₀]
  have hn₃Y : n₃ ∈ exactLayer (𝒞 K) z := exactCore_le_exactLayer hN₃ hn₃E
  have hmE : m ∈ exactCore z (N i₀) := C.involution_mem_exactCore h0tq h0cl
  have hmY : m ∈ exactLayer (𝒞 K) z := exactCore_le_exactLayer h0tq hmE
  obtain ⟨o, ho, hon⟩ := C.exists_conj_of_oddQuotMk_eq hn₃Y hmY hn₃2 hmsq hn₃m
  have hoC : o ∈ Subgroup.centralizer ({z} : Set G) :=
    exactLayer_le_centralizer (𝒞 K) z (Subgroup.map_subtype_le _ ho)
  have ho1 : oddQuotMk z ⟨o, hoC⟩ = 1 := oddQuotMk_eq_one_of_mem_oddCoreIn_layer C ho hoC
  have hoz : o⁻¹ * z * o⁻¹⁻¹ = z := by
    have hc : o * z = z * o := Subgroup.mem_centralizer_singleton_iff.mp hoC
    rw [inv_inv]
    calc o⁻¹ * z * o = o⁻¹ * (z * o) := by group
      _ = z := by rw [← hc]; group
  set N₃' : Subgroup G := conjSub o⁻¹ N₃ with hN₃'def
  have hN₃'Ω : N₃' ∈ 𝒞 K := C.hΩ.conjInvariant o⁻¹ N₃ hN₃.1
  have hN₃'cl : IsClassicalMember p f N₃' m := by
    have h := hn₃.conj o⁻¹
    have e : o⁻¹ * n₃ * o⁻¹⁻¹ = m := by rw [hon]; group
    rwa [e] at h
  have hN₃'img : modOdd z (exactCore z N₃') = R₃.map (C.psi b) := by
    have e1 : exactCore z N₃' = conjSub o⁻¹ (exactCore z N₃) := by
      have := exactCore_conjSub o⁻¹ z N₃
      rwa [hoz] at this
    have hoinv : o⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.inv_mem _ hoC
    have hoO : o⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)) :=
      Subgroup.inv_mem _ ⟨⟨o, hoC⟩, oddQuotMk_eq_one_iff.mp ho1, rfl⟩
    rw [e1, modOdd_conjSub_of_mem_oddCoreIn hoO, himg₃]
  have hT₃Ω : conjSub g N₃' ∈ 𝒞 K := C.hΩ.conjInvariant g N₃' hN₃'Ω
  have hT₃cl : IsClassicalMember p f (conjSub g N₃') z := by
    have h := hN₃'cl.conj g
    have e : g * m * g⁻¹ = z := by rw [hmdef]; group
    rwa [e] at h
  obtain ⟨j, hj⟩ := hcomp _ hT₃Ω hT₃cl
  rw [conjSub_inv_conjSub] at hj
  have hR₃eq : ∀ {R : Subgroup (compModel C.D b).K} (hR : R ∈ fundamentalSubgroups (C.D.tag b)
      (compModel C.D b).D), modOdd z (exactCore z (N j)) = R.map (C.psi b) → R₃ = R := by
    intro R hR himg
    refine Asc77.ih8_eq_of_map_eq (C.psi b) (C.psi_ker b) ?_ ?_ ?_
    · exact ModelFacts.fundPerfect_core (C.D.tag b) (C.D.rank b) p (C.D.exp b) C.hp
        (C.D.isFundTag b) (C.D.admissible b) (C.four_le b hbD4) R₃ hR₃
    · exact ModelFacts.fundPerfect_core (C.D.tag b) (C.D.rank b) p (C.D.exp b) C.hp
        (C.D.isFundTag b) (C.D.admissible b) (C.four_le b hbD4) R hR
    · rw [← himg, ← hj, hN₃'img]
  rcases hall j with rfl | rfl | rfl
  · exact n0 (hR₃eq hR₀ himg₀)
  · exact n1 (hR₃eq hR₁ himg₁)
  · exact n2 (hR₃eq hR₂ himg₂)

end CFSG.ClassicalInvolution.Asc77.BSC.BSE
