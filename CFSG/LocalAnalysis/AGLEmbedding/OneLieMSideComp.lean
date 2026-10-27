module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefs
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeBlockRank
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveComponents
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section CompNotLe

variable {G : Type} [Group G] [Finite G]

theorem barM_le_centralizer_of_commutator_mem {p : ℕ} {P : Sylow p G} {M H R Z L : Subgroup G}
    (h3 : D1PhaseThree p P M H R) (hL2 : IsTwoPrimeComponent M L) (hLH : L ≤ H)
    (hLN : ¬ L ≤ GLBPrimeCore p H) (hZM : Z ≤ M) (hZH : Z ≤ H)
    (hcomm : ∀ z ∈ Z, ∀ l ∈ L, z * l * z⁻¹ * l⁻¹ ∈ GLBPrimeCore p H) :
    barM M Z ≤ Subgroup.centralizer (barM M L : Set _) := by
  set N := GLBPrimeCore p H with hNdef
  have hQN : pCoreOf 2 M ≤ N := h3.twoCore_M_le_glbPrimeCore
  have hNn : H ≤ Subgroup.normalizer (N : Set G) := le_normalizer_glbPrimeCore p H
  have hconjN : ∀ g ∈ H, ∀ a ∈ N, g * a * g⁻¹ ∈ N := fun g hg a ha =>
    (Subgroup.mem_normalizer_iff.mp (hNn hg) a).mp ha
  have hnorm : ∀ z ∈ Z, z ∈ Subgroup.normalizer (L : Set G) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    by_contra hne
    have hcq := (hL2.map_conj (hZM hz)).commutator_le hL2 hne
    apply hLN
    rw [← hL2.perfect, Subgroup.commutator_le]
    intro l₁ hl₁ l₂ hl₂
    set w := z * l₂ * z⁻¹ with hw
    have hwL : w ∈ L.map (MulAut.conj z).toMonoidHom := ⟨l₂, hl₂, by simp [hw]⟩
    have hc₁ : w * l₁ * w⁻¹ * l₁⁻¹ ∈ N :=
      hQN (hcq (Subgroup.commutator_mem_commutator hwL hl₁))
    have hn' : w⁻¹ * l₂ ∈ N := by
      have := hcomm z hz l₂⁻¹ (L.inv_mem hl₂)
      simpa [hw, mul_assoc] using this
    have hwH : w ∈ H := H.mul_mem (H.mul_mem (hZH hz) (hLH hl₂)) (H.inv_mem (hZH hz))
    have hl₁H := hLH hl₁
    have key : l₁ * l₂ * l₁⁻¹ * l₂⁻¹ =
        (w * l₁ * w⁻¹ * l₁⁻¹)⁻¹ *
          (w * (l₁ * (w⁻¹ * l₂) * l₁⁻¹ * (w⁻¹ * l₂)⁻¹) * w⁻¹) := by
      group
    rw [commutatorElement_def, key]
    exact N.mul_mem (N.inv_mem hc₁) (hconjN _ hwH _ (N.mul_mem
      (hconjN l₁ hl₁H _ hn') (N.inv_mem hn')))
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hLM : L ≤ M := hL2.le
  have hcen : ∀ x : M, (x : G) ∈ L → (x : G) ∈ N → ∀ y ∈ barM M L, mk x * y = y * mk x := by
    have hLb := hL2.component
    have hQ := hLb.2.2
    set W : Subgroup ↥(barM M L) := (barM M (L ⊓ N)).subgroupOf (barM M L) with hW
    have hWn : W.Normal := by
      refine ⟨fun w hw g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hw ⊢
      obtain ⟨⟨x, hxM⟩, hx, hxw⟩ := hw
      obtain ⟨⟨l, hlM⟩, hl, hlg⟩ := (g : ↥(barM M L)).2
      have hxL : x ∈ L := (Subgroup.mem_subgroupOf.mp hx).1
      have hxN : x ∈ N := (Subgroup.mem_subgroupOf.mp hx).2
      have hlL : l ∈ L := Subgroup.mem_subgroupOf.mp hl
      refine ⟨⟨l, hlM⟩ * ⟨x, hxM⟩ * (⟨l, hlM⟩)⁻¹, Subgroup.mem_subgroupOf.mpr
        ⟨L.mul_mem (L.mul_mem hlL hxL) (L.inv_mem hlL),
          hconjN l (hLH hlL) x hxN⟩, ?_⟩
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hxw]
      change mk ⟨l, hlM⟩ * _ * (mk ⟨l, hlM⟩)⁻¹ = _
      rw [show mk ⟨l, hlM⟩ = ((g : ↥(barM M L)) : _) from hlg]
    have hWc : W ≤ Subgroup.center ↥(barM M L) := by
      rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hQ W with
        hle | htop
      · exact hle
      · exfalso
        apply hLN
        intro l hl
        have hmem : (⟨mk ⟨l, hLM hl⟩, ⟨⟨l, hLM hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩⟩ :
            ↥(barM M L)) ∈ W := htop ▸ Subgroup.mem_top _
        have h1 : mk ⟨l, hLM hl⟩ ∈ barM M N :=
          barM_mono inf_le_right (Subgroup.mem_subgroupOf.mp hmem)
        exact coe_mem_of_mk_mem_barM hQN ⟨l, hLM hl⟩ h1
    intro x hxL hxN y hy
    have hxW : (⟨mk x, ⟨x, Subgroup.mem_subgroupOf.mpr hxL, rfl⟩⟩ : ↥(barM M L)) ∈ W :=
      Subgroup.mem_subgroupOf.mpr ⟨x, Subgroup.mem_subgroupOf.mpr ⟨hxL, hxN⟩, rfl⟩
    have := Subgroup.mem_center_iff.mp (hWc hxW) ⟨y, hy⟩
    exact (congrArg Subtype.val this).symm
  have hLZ : ⁅barM M L, barM M Z⁆ ≤ Subgroup.centralizer (barM M L : Set _) := by
    rw [Subgroup.commutator_le]
    rintro _ ⟨⟨l, hlM⟩, hl, rfl⟩ _ ⟨⟨z, hzM⟩, hz, rfl⟩
    have hlL : l ∈ L := Subgroup.mem_subgroupOf.mp hl
    have hzZ : z ∈ Z := Subgroup.mem_subgroupOf.mp hz
    set c : M := ⟨l, hlM⟩ * ⟨z, hzM⟩ * (⟨l, hlM⟩)⁻¹ * (⟨z, hzM⟩)⁻¹ with hc
    have hcL : (c : G) ∈ L := by
      have hzl : z * l⁻¹ * z⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hnorm z hzZ) l⁻¹).mp (L.inv_mem hlL)
      have : (c : G) = l * (z * l⁻¹ * z⁻¹) := by simp [hc, mul_assoc]
      rw [this]
      exact L.mul_mem hlL hzl
    have hcN : (c : G) ∈ N := by
      have h1 := hcomm z hzZ l hlL
      have : (c : G) = (z * l * z⁻¹ * l⁻¹)⁻¹ := by simp [hc, mul_assoc]
      rw [this]
      exact N.inv_mem h1
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := hcen c hcL hcN y hy
    rw [commutatorElement_def]
    simp only [hc, map_mul, map_inv] at h
    exact h.symm
  have h1 : ⁅⁅barM M L, barM M Z⁆, barM M L⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hLZ
  have h2 : ⁅⁅barM M Z, barM M L⁆, barM M L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (barM M Z)]
    exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hperf : ⁅barM M L, barM M L⁆ = barM M L := by
    rw [barM, ← Subgroup.map_commutator, ← barM]
    congr 1
    exact hL2.commutator_subgroupOf
  rw [hperf, Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
  exact h3

theorem D1PhaseThree.barM_le_centralizer_of_not_le_glbPrimeCore {p : ℕ} {P : Sylow p G}
    {M H R Np Z : Subgroup G} (h3 : D1PhaseThree p P M H R) (hZR : Z ≤ R)
    (hperf : ∀ L : Subgroup G, L ≤ H ⊓ M → ⁅L, L⁆ = L → L ≤ Np)
    (hcomm : ∀ z ∈ Z, ∀ c ∈ Np, z * c * z⁻¹ * c⁻¹ ∈ GLBPrimeCore p H) {L : Subgroup G}
    (hL2 : IsTwoPrimeComponent M L) (hLK : L ≤ H ⊓ M) (hLN : ¬ L ≤ GLBPrimeCore p H) :
    barM M Z ≤ Subgroup.centralizer (barM M L : Set _) := by
  have hZK : Z ≤ H ⊓ M := hZR.trans h3.le_inf
  have hLNp : L ≤ Np := hperf L hLK hL2.perfect
  exact barM_le_centralizer_of_commutator_mem h3 hL2 (hLK.trans inf_le_left) hLN
    (hZK.trans inf_le_right) (hZK.trans inf_le_left)
    (fun z hz l hl => hcomm z hz l (hLNp hl))

end CompNotLe

theorem stmtOneLieCompNotLe :
    ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {n e : ℕ} {P : Sylow p G}
      {M H R Np Z : Subgroup G}, D1OneLieMData p n e P M H R Np Z →
      ∀ L : Subgroup G, IsTwoPrimeComponent M L → L ≤ H ⊓ M → ¬ L ≤ GLBPrimeCore p H →
        barM M Z ≤ Subgroup.centralizer (barM M L : Set _) := by
  intro G _ _ p _ n e P M H R Np Z h L hL2 hLK hLN
  exact h.ph3.barM_le_centralizer_of_not_le_glbPrimeCore h.le_R h.perfect_le h.comm_le hL2 hLK hLN

section CompFive

variable {G : Type} [Group G] [Finite G]

theorem D1PhaseThree.barM_le_centralizer_of_le_glbPrimeCore (hα : KFactThreeOrFiveDvd)
    (hβ : KFactOutElemRank) {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M H R Z : Subgroup G}
    (h3 : D1PhaseThree p P M H R) (hind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q) (hZR : Z ≤ R)
    (hZ : IsElemAbelian p Z) (hZb : IsElemAbelian p (barM M Z))
    (hcardb : Nat.card (barM M Z) = Nat.card Z) (hcard : p ^ 2 ≤ Nat.card Z)
    (hNK : GLBPrimeCore p H ≤ H ⊓ M)
    (hirr : ∃ (r : ℕ) (t : G), 4 ≤ r ∧ t ∈ H ⊓ M ∧ t ∈ Subgroup.normalizer (Z : Set G) ∧
      ∀ k : ℕ, ¬ r ∣ k → ∀ Y : Subgroup G, Y ≤ Z →
        t ^ k ∈ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = Z)
    (hp5 : 5 ≤ p) {L : Subgroup G} (hL2 : IsTwoPrimeComponent M L) (hLN : L ≤ GLBPrimeCore p H) :
    barM M Z ≤ Subgroup.centralizer (barM M L : Set _) := by
  have hLK : L ≤ H ⊓ M := hLN.trans hNK
  by_contra hZC
  have hpp : p.Prime := h3.prime
  have : Fact p.Prime := ⟨hpp⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLb
  set Kb := barM M (H ⊓ M) with hKb
  have hLbC : IsComponentOf Lb ⊤ := hL2.component
  have hZK : Z ≤ H ⊓ M := hZR.trans h3.le_inf
  have hMtop : M ≠ ⊤ := fun hM => h3.not_le (hM ▸ le_top)
  have hcat : CatalogSimpleSections (↥M ⧸ CFSG.pCore 2 ↥M) :=
    (catalogSimpleSections_of_isKProper h3.glob.kProper M hMtop).quotient _
  have hLcat := hcat.isCatalogGroup_center_quotient hLbC
  have hpL : ¬ p ∣ Nat.card Lb := by
    have hcop : p.Coprime (Nat.card L) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hLN) (glbPrimeCore_coprime p H)
    have hdvd : Nat.card Lb ∣ Nat.card L := by
      have := Subgroup.card_map_dvd (L.subgroupOf M) mk
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL2.le).toEquiv] at this
    intro hpd
    exact (Nat.Prime.coprime_iff_not_dvd hpp).mp hcop (hpd.trans hdvd)
  have hsimple : IsSimpleGroup (↥Lb ⧸ Subgroup.center ↥Lb) := hLbC.2.2.2
  obtain ⟨q, hq, hq2, hqp, hqdvd⟩ : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q < p ∧
      q ∣ Nat.card (↥Lb ⧸ Subgroup.center ↥Lb) := by
    rcases hα _ hsimple (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
      _ hLbC.2.2) hLcat with h3 | h5
    · exact ⟨3, Nat.prime_three, by decide, by omega, h3⟩
    · refine ⟨5, Nat.prime_five, by decide, ?_, h5⟩
      have hdvdL : Nat.card (↥Lb ⧸ Subgroup.center ↥Lb) ∣ Nat.card Lb :=
        Subgroup.card_quotient_dvd_card _
      have hp5' : p ≠ 5 := fun he => hpL (he ▸ h5.trans hdvdL)
      omega
  obtain ⟨y, hyL, hyq, l, hlL, hyl⟩ := exists_qElement_not_central hq hqdvd
  have hLbK : Lb ≤ Kb := Subgroup.map_mono (fun z hz => Subgroup.mem_subgroupOf.mpr
    (hLK (Subgroup.mem_subgroupOf.mp hz)))
  have horbit : ∀ (m : ℕ) (g : Fin m → ↥M ⧸ CFSG.pCore 2 ↥M), (∀ j, g j ∈ Kb) →
      Function.Injective (fun j => Lb.map (MulAut.conj (g j)).toMonoidHom) → m ≤ 3 := by
    intro m g hg hinj
    have hm := le_pRank_of_injective_conj stmtComponentRank stmtBarPRankLift inf_le_right hq
      hq2 hLbC hLbK hyL hyq hlL hyl g hg hinj
    by_contra hm3
    exact h3.false_of_four_le_pRank' hind hq hq2 hqp (by omega)
  by_cases hZN : barM M Z ≤ Subgroup.normalizer (Lb : Set _)
  · obtain ⟨r, t, hr4, htK, htZ, hirr⟩ := hirr
    have htop : Z ⊓ ((Subgroup.centralizer (Lb : Set _)).comap mk).map M.subtype ≠ Z := by
      intro he
      apply hZC
      rintro _ ⟨⟨x, hxM⟩, hxZ, rfl⟩
      have hxCZ : x ∈ Z ⊓ ((Subgroup.centralizer (Lb : Set _)).comap mk).map M.subtype := by
        rw [he]
        exact Subgroup.mem_subgroupOf.mp hxZ
      obtain ⟨m, hm, hmx⟩ := hxCZ.2
      have : m = ⟨x, hxM⟩ := Subtype.ext hmx
      subst this
      exact hm
    have hbot : Z ⊓ ((Subgroup.centralizer (Lb : Set _)).comap mk).map M.subtype ≠ ⊥ := by
      intro hCZbot
      have hinf : barM M Z ⊓ Subgroup.centralizer (Lb : Set _) = ⊥ := by
        rw [eq_bot_iff]
        rintro z ⟨⟨⟨x, hxM⟩, hxZ, rfl⟩, hzC⟩
        have hxCZ : x ∈ Z ⊓ ((Subgroup.centralizer (Lb : Set _)).comap mk).map M.subtype :=
          ⟨Subgroup.mem_subgroupOf.mp hxZ, ⟨⟨x, hxM⟩, hzC, rfl⟩⟩
        rw [hCZbot, Subgroup.mem_bot] at hxCZ
        have : (⟨x, hxM⟩ : M) = 1 := Subtype.ext hxCZ
        rw [Subgroup.mem_bot, this, map_one]
      have hle := hβ _ Lb (barM M Z) hLbC hLcat p hpp hp5 hpL hZN hZb hinf
      rw [hcardb] at hle
      have h2 := hcard
      have : p < p ^ 2 := by
        calc p = p ^ 1 := (pow_one p).symm
          _ < p ^ 2 := Nat.pow_lt_pow_right hpp.one_lt (by norm_num)
      omega
    have hinj := injective_conj_pow_of_inf_preimage_centralizer htK.2 htZ hirr hbot htop
    have := horbit r _ (fun j => Kb.pow_mem
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr htK)) _) hinj
    omega
  · obtain ⟨xb, hxb, hxbN⟩ := Set.not_subset.mp hZN
    obtain ⟨⟨x, hxM⟩, hxZ, rfl⟩ := hxb
    have hxZ' : x ∈ Z := Subgroup.mem_subgroupOf.mp hxZ
    have hxbK : mk ⟨x, hxM⟩ ∈ Kb :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hZK hxZ'))
    have hxp : IsPGroup p (Subgroup.zpowers (mk ⟨x, hxM⟩)) := by
      refine isPGroup_zpowers_of_pow_eq_one (k := 1) ?_
      have hx1 : x ^ p = 1 := hZ.2 x hxZ'
      have : (⟨x, hxM⟩ : M) ^ p = 1 := Subtype.ext (by simpa using hx1)
      rw [pow_one, ← map_pow, this, map_one]
    have hinj := injective_conj_pow_of_not_mem_normalizer hxp hxbN
    have := horbit p (fun j => (mk ⟨x, hxM⟩) ^ (j : ℕ)) (fun j => Kb.pow_mem hxbK _) hinj
    omega

end CompFive

theorem stmtOneLieCompFive :
    ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {n e : ℕ} {P : Sylow p G}
      {M H R Np Z : Subgroup G}, KFactThreeOrFiveDvd → KFactOutElemRank →
      D1OneLieMData p n e P M H R Np Z → 5 ≤ p →
      ∀ L : Subgroup G, IsTwoPrimeComponent M L → L ≤ GLBPrimeCore p H →
        barM M Z ≤ Subgroup.centralizer (barM M L : Set _) := by
  intro G _ _ p _ n e P M H R Np Z hα hβ h hp5 L hL2 hLN
  exact h.ph3.barM_le_centralizer_of_le_glbPrimeCore hα hβ h.ind h.le_R h.isElemAbelian
    h.isElemAbelian_barM' h.card_barM' h.two_le_card (h.core_le.trans h.plus_le) h.exists_irr hp5
    hL2 hLN

end CFSG.AGLEmbedding
