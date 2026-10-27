module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaBlock
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeInner
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeUnique

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1PhaseThree.false_of_u33_three (h : D1PhaseThree p P M H R) (hp3 : p = 3)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK : CitedBlockToralThree)
    (hK9 : CitedBlockThreeAutNine)
    (hperf : ∀ Y : Subgroup G, Y ≤ H ⊓ M → ⁅Y, Y⁆ = Y → Nat.Coprime 3 (Nat.card Y))
    {z : G} (hzR : z ∈ R) (hzo : orderOf z = 3) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hsyl : ∃ S : Sylow 3 ↥(M ⊓ Subgroup.centralizer ({z} : Set G)),
      (S : Subgroup _).map (M ⊓ Subgroup.centralizer ({z} : Set G)).subtype = R)
    {T : Subgroup G} (hRz : ∀ r ∈ R, z * r = r * z) (hexp : ∀ r ∈ R, r ^ 3 = 1)
    (hdec : ∀ r ∈ R, ∃ t ∈ T, ∃ i : ℕ, r = t * z ^ i)
    (hfusZ : ∀ r ∈ R, r ∉ T → (∀ s ∈ R, r * s = s * r) → r ∈ fusionSet R z)
    (hinv : ∀ t ∈ T, t ≠ 1 → ∃ n ∈ M, n * z * n⁻¹ = z ∧ n * t * n⁻¹ = t⁻¹)
    (hPz : ∀ y ∈ (P : Subgroup G), y * z = z * y → y ∈ R)
    (hR81 : Nat.card R = 3 ^ 4) (hP6 : 3 ^ 6 ≤ Nat.card (P : Subgroup G)) : False := by
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hzM : z ∈ M := h.le_M hzR
  set zb := mk ⟨z, hzM⟩ with hzb
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hz : IsPGroup 3 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hz3)
  have hbf := fun (L : Subgroup G) (hL : IsWeakSBlock M S L) =>
    h.blockFacts_u33 hp hp2 h84 h85 h86 h93 hD2 hK hK9 hperf hzM hz hz3 hCz hL
  obtain ⟨L₀, hL₀⟩ := h.exists_weakSBlock h84 hD2
  obtain ⟨L₁, hL₁, r, hrR, hrM, hrL, hrc⟩ :=
    exists_rep_mem_R hzM hz3 hCz hsyl hL₀ (hbf L₀ hL₀).1
  have hzC₁ := h.not_mem_centralizer_block hp hp2 hzM hz hCz hL₁
  have hr1 : r ≠ 1 := by
    rintro rfl
    apply hzC₁
    have e : (mk ⟨1, hrM⟩)⁻¹ * zb = zb := by
      have : (⟨1, hrM⟩ : M) = 1 := rfl
      rw [this, map_one, inv_one, one_mul]
    rwa [e] at hrc
  have hrT : r ∉ T := by
    intro hrT
    obtain ⟨n, hnM, hnz, hnr⟩ := hinv r hrT hr1
    exact h.false_of_rep_inv hp hp2 hzM hz hCz hL₁ hrM (hexp r hrR) hrL hrc hnM hnz hnr
  by_cases hrZ : ∀ s ∈ R, r * s = s * r
  ·
    obtain ⟨-, n, hnN, hrn⟩ := hfusZ r hrR hrT hrZ
    have hnM : n ∈ M := h.toD1Escape.normalizer_le hnN
    have hnzo : orderOf (n * z * n⁻¹) = 3 := by
      rw [← hzo]
      exact orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective z
    have hzr : n * z * n⁻¹ ∈ Subgroup.zpowers r :=
      mem_zpowers_of_mem_zpowers_of_prime hp hnzo hrn hr1
    have hnzM : n * z * n⁻¹ ∈ M := M.mul_mem (M.mul_mem hnM hzM) (M.inv_mem hnM)
    have hnzL : mk ⟨n * z * n⁻¹, hnzM⟩ ∈ barM M L₁ := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzr
      have : (⟨n * z * n⁻¹, hnzM⟩ : M) = (⟨r, hrM⟩ : M) ^ k :=
        Subtype.ext (by simpa using hk.symm)
      rw [this, map_zpow]
      exact Subgroup.zpow_mem _ hrL k
    set A := barM M (L₁.map (MulAut.conj n⁻¹).toMonoidHom) with hA
    have hAc : IsComponentOf A ⊤ :=
      (hL₁.toIsTwoPrimeComponent.map_conj (M.inv_mem hnM)).component
    have hzA : zb ∈ A := by
      rw [hA, barM_map_conj (M.inv_mem hnM) L₁]
      refine ⟨mk ⟨n * z * n⁻¹, hnzM⟩, hnzL, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, hzb]
      congr 1
      exact Subtype.ext (by simp [mul_assoc])
    have hzL₁ : zb ∈ barM M L₁ :=
      (h.barM_eq_of_mem_component hp hp2 hzM hz hCz hAc hzA hL₁) ▸ hzA
    have h1 := h.card_le_of_zbar_mem rfl h84 h85 h86 h93 hD2 hK hK9 hperf hzR hz3 hCz hPz hL₁
      hzL₁
    have h2 := three_mul_card_rPart_le h.le_M h.isPGroup hzR hzC₁
    omega
  ·
    push Not at hrZ
    obtain ⟨s, hsR, hrs⟩ := hrZ
    have hrC₁ : mk ⟨r, hrM⟩ ∉ Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      fun hc => hzC₁ (by
        have := Subgroup.mul_mem _ hc hrc
        rwa [mul_inv_cancel_left] at this)
    have h9 := nine_mul_card_rPart_le h.le_M h.isPGroup hrR hrL hrC₁ hsR (fun he => hrs he.symm)
    obtain ⟨t, htT, i, rfl⟩ := hdec r hrR
    have htR : t ∈ R := by
      have := R.mul_mem hrR (R.pow_mem (R.inv_mem hzR) i)
      simpa [inv_pow] using this
    have hzi : z ^ i = z ^ (i % 3) := by
      conv_lhs => rw [← Nat.mod_add_div i 3, pow_add, pow_mul, hz3, one_pow, mul_one]
    have ht1 : t ≠ 1 := by
      rintro rfl
      apply hrs
      rw [one_mul]
      exact ((Commute.pow_left (hRz s hsR) i).eq)
    obtain ⟨n, hnM, hnz, hnt⟩ := hinv t htT ht1
    have hnC : n ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc n * z = n * z * n⁻¹ * n := by group
        _ = z * n := by rw [hnz]
    have hnS : n ∈ Subgroup.normalizer (S : Set G) :=
      localGroup_le_normalizer_pCoreOf 2 H (hCz hnC)
    have hL₂ := hL₁.map_conj hnM hnS
    set L₂ := L₁.map (MulAut.conj n).toMonoidHom with hL₂def
    set nb := mk ⟨n, hnM⟩ with hnb
    set rb := mk ⟨t * z ^ i, hrM⟩ with hrb
    have hbar₂ : barM M L₂ = (barM M L₁).map (MulAut.conj nb).toMonoidHom := barM_map_conj hnM L₁
    have hnzb : nb * zb * nb⁻¹ = zb := by
      rw [hnb, hzb, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hnz
    have hr'M : t⁻¹ * z ^ i ∈ M := M.mul_mem (M.inv_mem (h.le_M htR)) (M.pow_mem hzM i)
    set rb' := mk ⟨t⁻¹ * z ^ i, hr'M⟩ with hrb'
    have hnrb : nb * rb * nb⁻¹ = rb' := by
      rw [hnb, hrb, hrb', ← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc n * (t * z ^ i) * n⁻¹ = (n * t * n⁻¹) * (n * z * n⁻¹) ^ i := by
            rw [conj_pow]; group
        _ = t⁻¹ * z ^ i := by rw [hnt, hnz]
    have hr'L : rb' ∈ barM M L₂ := by rw [hbar₂, ← hnrb]; exact ⟨rb, hrL, rfl⟩
    have hr'c : rb'⁻¹ * zb ∈ Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      have := conj_mem_centralizer_map_of_mem (g := nb) hrc
      rw [← hbar₂] at this
      have e : nb * (rb⁻¹ * zb) * nb⁻¹ = rb'⁻¹ * zb := by
        calc nb * (rb⁻¹ * zb) * nb⁻¹ = (nb * rb * nb⁻¹)⁻¹ * (nb * zb * nb⁻¹) := by group
          _ = rb'⁻¹ * zb := by rw [hnrb, hnzb]
      rwa [e] at this
    have hzb3 : zb ^ 3 = 1 := by
      rw [hzb, ← map_pow]
      have : (⟨z, hzM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
      rw [this, map_one]
    have hzbmod : ∀ k : ℕ, zb ^ k = zb ^ (k % 3) := fun k => by
      conv_lhs => rw [← Nat.mod_add_div k 3, pow_add, pow_mul, hzb3, one_pow, mul_one]
    have htc : t * z = z * t := (hRz t htR).symm
    have hrbe : rb = mk ⟨t, h.le_M htR⟩ * zb ^ i := by
      rw [hrb, hzb, ← map_pow, ← map_mul]; rfl
    have hrbe' : rb' = (mk ⟨t, h.le_M htR⟩)⁻¹ * zb ^ i := by
      rw [hrb', hzb, ← map_pow, ← map_inv, ← map_mul]; rfl
    have htzb : mk ⟨t, h.le_M htR⟩ * zb = zb * mk ⟨t, h.le_M htR⟩ := by
      rw [hzb, ← map_mul, ← map_mul]; congr 1; exact Subtype.ext htc
    have htzbi : mk ⟨t, h.le_M htR⟩ * zb ^ i = zb ^ i * mk ⟨t, h.le_M htR⟩ :=
      (Commute.pow_right htzb i).eq
    have hprod : rb * rb' = zb ^ (2 * i) := by
      rw [hrbe, hrbe', two_mul, pow_add]
      calc mk ⟨t, h.le_M htR⟩ * zb ^ i * ((mk ⟨t, h.le_M htR⟩)⁻¹ * zb ^ i)
          = mk ⟨t, h.le_M htR⟩ * (zb ^ i * (mk ⟨t, h.le_M htR⟩)⁻¹) * zb ^ i := by group
        _ = mk ⟨t, h.le_M htR⟩ * ((mk ⟨t, h.le_M htR⟩)⁻¹ * zb ^ i) * zb ^ i := by
          rw [(Commute.inv_right (Commute.pow_right htzb i).symm).eq]
        _ = zb ^ i * zb ^ i := by group
    have hi0 : i % 3 ≠ 0 := by
      intro h0
      apply hrT
      rw [hzi, h0, pow_zero, mul_one]
      exact htT
    have hP3 : 3 ^ 6 ≤ Nat.card (P : Subgroup G) := hP6
    by_cases heq : barM M L₂ = barM M L₁
    ·
      have hr'L₁ : rb' ∈ barM M L₁ := heq ▸ hr'L
      have hq : rb⁻¹ * rb' ∈ barM M L₁ := Subgroup.mul_mem _ (Subgroup.inv_mem _ hrL) hr'L₁
      have ht3 : (mk ⟨t, h.le_M htR⟩) ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨t, h.le_M htR⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hexp t htR)
        rw [this, map_one]
      have hqe : rb⁻¹ * rb' = mk ⟨t, h.le_M htR⟩ := by
        rw [hrbe, hrbe']
        calc (mk ⟨t, h.le_M htR⟩ * zb ^ i)⁻¹ * ((mk ⟨t, h.le_M htR⟩)⁻¹ * zb ^ i)
            = (zb ^ i)⁻¹ * ((mk ⟨t, h.le_M htR⟩)⁻¹ * (mk ⟨t, h.le_M htR⟩)⁻¹) * zb ^ i := by
              group
          _ = (zb ^ i)⁻¹ * mk ⟨t, h.le_M htR⟩ * zb ^ i := by
              congr 2
              calc (mk ⟨t, h.le_M htR⟩)⁻¹ * (mk ⟨t, h.le_M htR⟩)⁻¹
                  = (mk ⟨t, h.le_M htR⟩)⁻¹ * (mk ⟨t, h.le_M htR⟩)⁻¹ * (mk ⟨t, h.le_M htR⟩) ^ 3 := by
                    rw [ht3, mul_one]
                _ = mk ⟨t, h.le_M htR⟩ := by group
          _ = mk ⟨t, h.le_M htR⟩ := by rw [mul_assoc, htzbi]; group
      have htL : mk ⟨t, h.le_M htR⟩ ∈ barM M L₁ := hqe ▸ hq
      have hziL : zb ^ i ∈ barM M L₁ := by
        have := Subgroup.mul_mem _ (Subgroup.inv_mem _ htL) hrL
        rwa [hrbe, inv_mul_cancel_left] at this
      have hzL₁ : zb ∈ barM M L₁ := by
        rw [hzbmod] at hziL
        have hlt : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
        interval_cases hi : i % 3
        · exact absurd rfl hi0
        · simpa using hziL
        · have : zb = (zb ^ 2) ^ 2 := by
            rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hzb3, one_mul, pow_one]
          rw [this]
          exact Subgroup.pow_mem _ hziL 2
      have h1 := h.card_le_of_zbar_mem rfl h84 h85 h86 h93 hD2 hK hK9 hperf hzR hz3 hCz hPz hL₁
        hzL₁
      omega
    ·
      have hr'C₁ : rb' ∈ Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
        le_centralizer_of_component_ne hL₂.component hL₁.component heq hr'L
      have hrC₂ : rb ∈ Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
        le_centralizer_of_component_ne hL₁.component hL₂.component (Ne.symm heq) hrL
      have hlt : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
      interval_cases hi : i % 3
      · exact absurd rfl hi0
      ·
        have h2 : rb * rb' = zb ^ 2 := by
          rw [hprod, hzbmod, show 2 * i % 3 = 2 by omega]
        set c := rb⁻¹ * zb with hc
        have hcr : rb * c = c * rb := (Subgroup.mem_centralizer_iff.mp hrc rb hrL)
        have hzrc : zb = rb * c := by rw [hc, mul_inv_cancel_left]
        have h3 : rb' = rb * (c * c) := by
          have : rb * rb' = rb * (rb * (c * c)) := by
            rw [h2, hzrc, pow_two]
            calc rb * c * (rb * c) = rb * (c * rb) * c := by group
              _ = rb * (rb * c) * c := by rw [hcr]
              _ = rb * (rb * (c * c)) := by group
          exact mul_left_cancel this
        apply hrC₁
        have : rb = rb' * (c * c)⁻¹ := by rw [h3, mul_inv_cancel_right]
        rw [this]
        exact Subgroup.mul_mem _ hr'C₁ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hrc hrc))
      ·
        have h2 : zb = rb * rb' := by
          rw [hprod, hzbmod, show 2 * i % 3 = 1 by omega, pow_one]
        have hrb3 : rb ^ 3 = 1 := by
          rw [hrb, ← map_pow]
          have : (⟨t * z ^ i, hrM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hexp _ hrR)
          rw [this, map_one]
        have hr'R : t⁻¹ * z ^ i ∈ R := R.mul_mem (R.inv_mem htR) (R.pow_mem hzR i)
        have hrb'3 : rb' ^ 3 = 1 := by
          rw [hrb', ← map_pow]
          have : (⟨t⁻¹ * z ^ i, hr'M⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hexp _ hr'R)
          rw [this, map_one]
        have hzC₂ := h.not_mem_centralizer_block hp hp2 hzM hz hCz hL₂
        have hr'C₂ : rb' ∉ Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
          fun hc => hzC₂ (show zb ∈ _ from h2 ▸ Subgroup.mul_mem _ hrC₂ hc)
        have hrb1 : rb ≠ 1 := fun h1 => hrC₁ (h1 ▸ Subgroup.one_mem _)
        have hrb'1 : rb' ≠ 1 := fun h1 => hr'C₂ (h1 ▸ Subgroup.one_mem _)
        have h1 := h.card_le_of_two_blocks rfl h84 h85 h86 h93 hD2 hK hK9 hperf hzR hz3 hCz hPz
          hL₁ hL₂ heq hrL hr'L hrb1 hrb3 hrb'1 hrb'3 h2
        have hRp : IsPGroup 3 (rPart M R
            (Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)))) :=
          h.isPGroup.to_le inf_le_left
        have h3 : 3 * Nat.card (rPart M R
            (Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
              Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)))) ≤
            Nat.card (rPart M R
              (Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)))) :=
          three_mul_card_le_of_lt hRp
          (inf_le_inf_left R (Subgroup.map_mono (Subgroup.comap_mono inf_le_left)))
          (fun he => hr'C₂ (by
            have hmem : t⁻¹ * z ^ i ∈ rPart M R
                (Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :=
              (mem_rPart h.le_M hr'R).mpr hr'C₁
            rw [← he] at hmem
            exact ((mem_rPart h.le_M hr'R).mp hmem).2))
        omega

end CFSG.AGLEmbedding
