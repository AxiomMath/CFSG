module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefs
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.LemmaUPrime
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveComponents
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Conjugates

variable {G : Type} [Group G]

theorem map_conj_inf_preimage_normalizer_le {M X : Subgroup G}
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} {g : G} (hg : g ∈ M)
    (hgX : g ∈ Subgroup.normalizer (X : Set G))
    (hgL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hg⟩ ∈ Subgroup.normalizer (Lb : Set _)) :
    (X ⊓ ((Subgroup.normalizer (Lb : Set _)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype).map (MulAut.conj g).toMonoidHom ≤
      X ⊓ ((Subgroup.normalizer (Lb : Set _)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  rintro _ ⟨x, ⟨hxX, ⟨m, hm, hmx⟩⟩, rfl⟩
  refine ⟨(Subgroup.mem_normalizer_iff.mp hgX x).mp hxX, ⟨⟨g, hg⟩ * m * (⟨g, hg⟩)⁻¹,
    ?_, by simp [MulAut.conj_apply, ← hmx]⟩⟩
  show mk (⟨g, hg⟩ * m * (⟨g, hg⟩)⁻¹) ∈ Subgroup.normalizer (Lb : Set _)
  rw [map_mul, map_mul, map_inv]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgL hm) (Subgroup.inv_mem _ hgL)

theorem injective_conj_pow_of_inf_preimage_normalizer {M X : Subgroup G}
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} {r : ℕ} {t : G} (htM : t ∈ M)
    (htX : t ∈ Subgroup.normalizer (X : Set G))
    (hirr : ∀ k : ℕ, ¬ r ∣ k → ∀ Y : Subgroup G, Y ≤ X →
      t ^ k ∈ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = X)
    (hbot : X ⊓ ((Subgroup.normalizer (Lb : Set _)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype ≠ ⊥)
    (htop : X ⊓ ((Subgroup.normalizer (Lb : Set _)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype ≠ X) :
    Function.Injective fun j : Fin r => Lb.map
      (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩ ^ (j : ℕ))).toMonoidHom := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set NX := X ⊓ ((Subgroup.normalizer (Lb : Set _)).comap mk).map M.subtype with hNX
  set tb := mk ⟨t, htM⟩ with htb
  have hstep : ∀ i j : ℕ, i < j → j < r →
      Lb.map (MulAut.conj (tb ^ i)).toMonoidHom = Lb.map (MulAut.conj (tb ^ j)).toMonoidHom →
      False := by
    intro i j hij hjr he
    have htbk : tb ^ (j - i) ∈ Subgroup.normalizer (Lb : Set _) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hj : tb ^ j = tb ^ i * tb ^ (j - i) := by rw [← pow_add]; congr 1; omega
      rw [hj, map_conj_mul_eq] at he
      exact (Subgroup.map_injective (MulAut.conj (tb ^ i)).injective he).symm
    have htk : t ^ (j - i) ∈ Subgroup.normalizer (NX : Set G) := by
      have hle : Subgroup.zpowers (t ^ (j - i)) ≤ Subgroup.normalizer (NX : Set G) := by
        refine le_normalizer_of_forall_map_conj_le fun g hg => ?_
        obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        have hgM : (t ^ (j - i)) ^ z ∈ M := M.zpow_mem (M.pow_mem htM _) z
        refine map_conj_inf_preimage_normalizer_le hgM
          (Subgroup.zpow_mem _ (Subgroup.pow_mem _ htX _) z) ?_
        have : mk ⟨(t ^ (j - i)) ^ z, hgM⟩ = (tb ^ (j - i)) ^ z := by
          rw [htb, ← map_pow, ← map_zpow]
          rfl
        rw [this]
        exact Subgroup.zpow_mem _ htbk z
      exact hle (Subgroup.mem_zpowers _)
    have hrk : ¬ r ∣ j - i := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    rcases hirr (j - i) hrk NX inf_le_left htk with h1 | h1
    · exact hbot h1
    · exact htop h1
  intro i j hij
  by_contra hne
  have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
  · exact hstep i j hlt j.2 hij
  · exact hstep j i hlt i.2 hij.symm

theorem card_le_ncard_of_injective_conj [Finite G] {C : Set (Subgroup G)}
    (hC : ∀ g : G, ∀ L ∈ C, L.map (MulAut.conj g).toMonoidHom ∈ C) {L : Subgroup G} (hL : L ∈ C)
    {ι : Type*} (g : ι → G)
    (hinj : Function.Injective fun j => L.map (MulAut.conj (g j)).toMonoidHom) :
    Nat.card ι ≤ C.ncard := by
  rw [← Set.ncard_range_of_injective hinj]
  exact Set.ncard_le_ncard (Set.range_subset_iff.mpr fun j => hC (g j) L hL) (Set.toFinite C)

end Conjugates

section PrimeToThree

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {n e : ℕ} {P : Sylow p G}
  {M H R Np Z : Subgroup G}

theorem D1OneLieMData.preimage_le_plus_of_not_three_dvd (h : D1OneLieMData p n e P M H R Np Z)
    (hBT : StmtBlockThree) {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤)
    (h3 : ¬ 3 ∣ Nat.card Lb) :
    (Lb.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype ≤ Np := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  obtain ⟨L, hL2, rfl, hw | hle⟩ := h.ph3.exists_weakSBlock_or_le_inf hLb
  · exfalso
    obtain ⟨y, ⟨-, hyL⟩, hy3, l, hl, hlQ⟩ := hBT h.ph3 hw
    have hyM : y ∈ M := hL2.le hyL
    have hlM : l ∈ M := hL2.le hl
    have hyb : mk ⟨y, hyM⟩ ∈ barM M L :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyL)
    have hy1 : mk ⟨y, hyM⟩ ≠ 1 := by
      intro hy1
      apply hlQ
      have hc : mk (⟨y, hyM⟩ * ⟨l, hlM⟩ * (⟨y, hyM⟩)⁻¹ * (⟨l, hlM⟩)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy1]
        group
      exact coe_mem_pCoreOf_two_of_mk_eq_one _ hc
    obtain ⟨a, ha⟩ := hy3 ⟨y, Subgroup.mem_zpowers y⟩
    have hya : (⟨y, hyM⟩ : M) ^ 3 ^ a = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val ha)
    have hyba : mk ⟨y, hyM⟩ ^ 3 ^ a = 1 := by rw [← map_pow, hya, map_one]
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hyba)
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hy1 (orderOf_eq_one_iff.mp (by rw [hb, pow_zero]))
    exact h3 ((hb ▸ dvd_pow_self 3 hb0).trans (Subgroup.orderOf_dvd_natCard _ hyb))
  · have hQ : pCoreOf 2 M ≤ Np := h.ph3.twoCore_M_le_glbPrimeCore.trans h.core_le
    have hLNp : L ≤ Np := h.perfect_le L hle hL2.perfect
    rintro _ ⟨m, hm, rfl⟩
    exact coe_mem_of_mk_mem_barM hQ m (barM_mono hLNp hm)

end PrimeToThree

theorem stmtOneLieCompThree : StmtOneLieCompThree := by
  intro G _ _ p _ n e P M H R Np Z hα hβ hBT h hp3 L hL2 hLN
  subst hp3
  by_contra hZC
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLb
  have hLbC : IsComponentOf Lb ⊤ := hL2.component
  have hMtop : M ≠ ⊤ := fun hM => h.ph3.not_le (hM ▸ le_top)
  have hcat : CatalogSimpleSections (↥M ⧸ CFSG.pCore 2 ↥M) :=
    (catalogSimpleSections_of_isKProper h.ph3.glob.kProper M hMtop).quotient _
  have hZM : Z ≤ M := h.le_R.trans h.ph3.le_M
  have h9 : 9 ≤ Nat.card Z := by simpa using h.two_le_card
  have h3L : ¬ 3 ∣ Nat.card Lb := by
    have hcop : (3 : ℕ).Coprime (Nat.card L) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hLN) (glbPrimeCore_coprime 3 H)
    have hdvd : Nat.card Lb ∣ Nat.card L := by
      have := Subgroup.card_map_dvd (L.subgroupOf M) mk
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL2.le).toEquiv] at this
    intro hpd
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop (hpd.trans hdvd)
  set C : Set (Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    {L' | IsComponentOf L' ⊤ ∧ ¬ 3 ∣ Nat.card L'} with hC
  have hLC : Lb ∈ C := ⟨hLbC, h3L⟩
  have hCi : ∀ g : ↥M ⧸ CFSG.pCore 2 ↥M, ∀ L' ∈ C, L'.map (MulAut.conj g).toMonoidHom ∈ C :=
    fun g L' hL' => ⟨(CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g)
      L').mpr hL'.1, by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]; exact hL'.2⟩
  have hC5 : ∀ L' ∈ C, 5 ∣ Nat.card (↥L' ⧸ Subgroup.center ↥L') := by
    intro L' hL'
    rcases hα _ hL'.1.2.2.2
      (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hL'.1.2.2)
      (hcat.isCatalogGroup_center_quotient hL'.1) with h3 | h5
    · exact absurd (h3.trans (Subgroup.card_quotient_dvd_card _)) hL'.2
    · exact h5
  have hC4 : 4 ≤ C.ncard := by
    obtain ⟨r, t, hr4, htK, htZ, hirr⟩ := h.exists_irr
    by_cases hZN : barM M Z ≤ Subgroup.normalizer (Lb : Set _)
    ·
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
        have hle := hβ _ Lb (barM M Z) hLbC (hcat.isCatalogGroup_center_quotient hLbC) 3
          Nat.prime_three (by decide) h3L hZN h.isElemAbelian_barM' hinf
        rw [h.card_barM'] at hle
        omega
      have hinj := injective_conj_pow_of_inf_preimage_centralizer htK.2 htZ hirr hbot htop
      have hle := card_le_ncard_of_injective_conj hCi hLC _ hinj
      rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hle
      omega
    ·
      set NZ := Z ⊓ ((Subgroup.normalizer (Lb : Set _)).comap mk).map M.subtype with hNZ
      have htop : NZ ≠ Z := by
        intro he
        apply hZN
        rintro _ ⟨⟨x, hxM⟩, hxZ, rfl⟩
        have hxNZ : x ∈ NZ := by
          rw [he]
          exact Subgroup.mem_subgroupOf.mp hxZ
        obtain ⟨m, hm, hmx⟩ := hxNZ.2
        have : m = ⟨x, hxM⟩ := Subtype.ext hmx
        subst this
        exact hm
      by_cases hbot : NZ = ⊥
      ·
        have hinj : Function.Injective fun z : Z =>
            Lb.map (MulAut.conj (mk ⟨z, hZM z.2⟩)).toMonoidHom := by
          intro z₁ z₂ he
          simp only at he
          have hg : mk ⟨z₁, hZM z₁.2⟩ =
              mk ⟨z₂, hZM z₂.2⟩ * ((mk ⟨z₂, hZM z₂.2⟩)⁻¹ * mk ⟨z₁, hZM z₁.2⟩) := by group
          rw [hg, map_conj_mul_eq] at he
          have hgN : (mk ⟨z₂, hZM z₂.2⟩)⁻¹ * mk ⟨z₁, hZM z₁.2⟩ ∈
              Subgroup.normalizer (Lb : Set _) := by
            rw [Subgroup.mem_normalizer_iff_map_conj_eq]
            have h1 := Subgroup.map_injective (MulAut.conj (mk ⟨z₂, hZM z₂.2⟩)).injective he
            exact h1
          have hmem : (z₂ : G)⁻¹ * z₁ ∈ NZ := ⟨Z.mul_mem (Z.inv_mem z₂.2) z₁.2,
            ⟨(⟨z₂, hZM z₂.2⟩ : M)⁻¹ * ⟨z₁, hZM z₁.2⟩, by
              rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_inv]
              exact hgN, rfl⟩⟩
          rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
          exact Subtype.ext hmem.symm
        have hle := card_le_ncard_of_injective_conj hCi hLC _ hinj
        omega
      · have hinj := injective_conj_pow_of_inf_preimage_normalizer htK.2 htZ hirr hbot htop
        have hle := card_le_ncard_of_injective_conj hCi hLC _ hinj
        rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hle
        omega
  exact stmtOneLieLemmaUPrime h.ph3 (s := 5) Nat.prime_five (by decide) (by decide) Np
    (h.plus_le.trans inf_le_left) h.plus_normal (h.plus_le.trans inf_le_right) C
    (fun L' hL' => hL'.1) hCi hC5
    (fun L' hL' => h.preimage_le_plus_of_not_three_dvd hBT hL'.1 hL'.2) hC4

end CFSG.AGLEmbedding
