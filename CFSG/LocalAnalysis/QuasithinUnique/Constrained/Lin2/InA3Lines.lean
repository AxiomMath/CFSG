module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Hall
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Ord2

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped Pointwise

namespace Lin2Hyp

section Lines

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem L_le_normalizer_U : L ≤ Subgroup.normalizer (blockU L : Set G) := by
  rw [← E.OL hcfg]
  exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L

theorem blockZ_le_centerOf_R : blockZ L ≤ centerOf (thompsonJ S) := by
  rw [blockZ_eq_centerOf hcfg.charTwo_L (E.OL hcfg)]
  rcases lin2Z_cases (Z := lin2Z L (thompsonJ S)) rfl with ⟨hc, -⟩ | ⟨hc, hZ⟩
  · rw [hc]; exact bot_le
  · rw [← hZ]; exact lin2Z_le_centerOf E.h16 hcfg rfl

theorem centerOf_R_le_U : centerOf (thompsonJ S) ≤ blockU L := by
  obtain ⟨x, hx, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  rw [← (E.RUU hcfg hx hxS).2]
  exact inf_le_left

theorem exists_mem_centerOf_R_not_mem_blockZ :
    ∃ w ∈ centerOf (thompsonJ S), w ∉ blockZ L := by
  obtain ⟨x, hx, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  have hZne := lin2Z_ne_bot E.h16 hcfg (Z := lin2Z L (thompsonJ S)) rfl
  rcases lin2Z_cases (Z := lin2Z L (thompsonJ S)) rfl with ⟨hc, hZR⟩ | ⟨hc, hZL⟩
  · obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZne
    refine ⟨w, hZR ▸ hw, ?_⟩
    rw [blockZ_eq_centerOf hcfg.charTwo_L (E.OL hcfg), hc, Subgroup.mem_bot]
    exact fun h => hw1 (Subtype.ext h)
  · have hZ' : conjR (lin2Z L (thompsonJ S)) x ≠ ⊥ := fun h =>
      hZne (conjR_eq_bot_iff.1 h)
    obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZ'
    rcases E.Zcases hcfg (Z := lin2Z L (thompsonJ S)) rfl hx hxS with ⟨hc', -⟩ |
      ⟨-, hZR2, hZinf⟩
    · exact absurd hc' hc
    · refine ⟨w, hZR2 ▸ Subgroup.mem_sup_right hw, fun h => ?_⟩
      rw [blockZ_eq_centerOf hcfg.charTwo_L (E.OL hcfg), ← hZL] at h
      have : w ∈ lin2Z L (thompsonJ S) ⊓ conjR (lin2Z L (thompsonJ S)) x := ⟨h, hw⟩
      rw [hZinf, Subgroup.mem_bot] at this
      exact hw1 (Subtype.ext this)

theorem exists_conj_mem_centerOf_R {u : G} (hu : u ∈ blockU L) :
    ∃ ℓ ∈ L, ℓ * u * ℓ⁻¹ ∈ centerOf (thompsonJ S) := by
  by_cases huZ : u ∈ blockZ L
  · exact ⟨1, L.one_mem, by simpa using E.blockZ_le_centerOf_R hcfg huZ⟩
  · obtain ⟨w, hwR, hwZ⟩ := E.exists_mem_centerOf_R_not_mem_blockZ hcfg
    obtain ⟨ℓ, hℓ, hℓw⟩ := lin2_exists_conj_mem_coset hcfg.lin2 (E.L_le_normalizer_U hcfg) hu
      (E.centerOf_R_le_U hcfg hwR) huZ hwZ
    refine ⟨ℓ, hℓ, ?_⟩
    have : ℓ * u * ℓ⁻¹ = (ℓ * u * ℓ⁻¹ * w⁻¹) * w := by group
    rw [this]
    exact Subgroup.mul_mem _ (E.blockZ_le_centerOf_R hcfg hℓw) hwR

theorem conj_Z_le_U {g : G} (hne : conjR (lin2Z L (thompsonJ S)) g ⊓ blockU L ≠ ⊥) :
    conjR (lin2Z L (thompsonJ S)) g ≤ blockU L := by
  set Z := lin2Z L (thompsonJ S) with hZdef
  obtain ⟨x, hx, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  have hTI : fusionIsTI Z := E.ZTI hcfg rfl
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  obtain ⟨ℓ, hℓ, hw'⟩ := E.exists_conj_mem_centerOf_R hcfg hu.2
  have hw'1 : ℓ * u * ℓ⁻¹ ≠ 1 := by
    intro h
    apply hu1'
    have : u = ℓ⁻¹ * (ℓ * u * ℓ⁻¹) * ℓ := by group
    rw [this, h]; group
  have hw'B : ℓ * u * ℓ⁻¹ ∈ conjR Z (g * ℓ⁻¹) := by
    rw [mem_conjR]
    have e : g * ℓ⁻¹ * (ℓ * u * ℓ⁻¹) * (g * ℓ⁻¹)⁻¹ = g * u * g⁻¹ := by group
    rw [e]
    exact mem_conjR.mp hu.1
  have hℓU : conjR (blockU L) ℓ = blockU L :=
    conjR_eq_of_mem_normalizer (E.L_le_normalizer_U hcfg hℓ)
  have hZU : Z ≤ blockU L := (lin2Z_le_centerOf E.h16 hcfg rfl).trans (E.centerOf_R_le_U hcfg)
  have key : conjR Z (g * ℓ⁻¹) ≤ blockU L → conjR Z g ≤ blockU L := fun h => by
    have e : conjR (conjR Z (g * ℓ⁻¹)) ℓ = conjR Z g := by
      rw [conjR_conjR]; congr 1; group
    rw [← e]
    calc conjR (conjR Z (g * ℓ⁻¹)) ℓ ≤ conjR (blockU L) ℓ := conjR_mono h ℓ
      _ = blockU L := hℓU
  refine key ?_
  rcases lin2Z_cases (Z := Z) rfl with ⟨hc, hZR⟩ | ⟨hc, hZL⟩
  ·
    have hwZ : ℓ * u * ℓ⁻¹ ∈ Z := hZR ▸ hw'
    have hne' : Z ⊓ conjR Z (g * ℓ⁻¹) ≠ ⊥ := fun h => hw'1 (by
      have : ℓ * u * ℓ⁻¹ ∈ Z ⊓ conjR Z (g * ℓ⁻¹) := ⟨hwZ, hw'B⟩
      rw [h, Subgroup.mem_bot] at this; exact this)
    rw [conjR_eq_of_inf_ne_bot hTI hne']
    exact hZU
  ·
    rcases E.Zcases hcfg (Z := Z) rfl hx hxS with ⟨hc', -⟩ | ⟨-, hZR2, hZinf⟩
    · exact absurd hc' hc
    · have hw'ZR : ℓ * u * ℓ⁻¹ ∈ Z ⊔ conjR Z x := hZR2 ▸ hw'
      by_cases hwZ : ℓ * u * ℓ⁻¹ ∈ Z
      · have hne' : Z ⊓ conjR Z (g * ℓ⁻¹) ≠ ⊥ := fun h => hw'1 (by
          have : ℓ * u * ℓ⁻¹ ∈ Z ⊓ conjR Z (g * ℓ⁻¹) := ⟨hwZ, hw'B⟩
          rw [h, Subgroup.mem_bot] at this; exact this)
        rw [conjR_eq_of_inf_ne_bot hTI hne']
        exact hZU
      · by_cases hwZx : ℓ * u * ℓ⁻¹ ∈ conjR Z x
        · have hTIx : fusionIsTI (conjR Z x) := fusionIsTI_conjR hTI x
          have hB : conjR Z (g * ℓ⁻¹) = conjR (conjR Z x) (x⁻¹ * (g * ℓ⁻¹)) := by
            rw [conjR_conjR]; congr 1; group
          have hne' : conjR Z x ⊓ conjR (conjR Z x) (x⁻¹ * (g * ℓ⁻¹)) ≠ ⊥ := fun h => hw'1 (by
            have : ℓ * u * ℓ⁻¹ ∈ conjR Z x ⊓ conjR (conjR Z x) (x⁻¹ * (g * ℓ⁻¹)) :=
              ⟨hwZx, hB ▸ hw'B⟩
            rw [h, Subgroup.mem_bot] at this; exact this)
          rw [hB, conjR_eq_of_inf_ne_bot hTIx hne']
          exact (hZR2 ▸ le_sup_right : conjR Z x ≤ centerOf (thompsonJ S)).trans
            (E.centerOf_R_le_U hcfg)
        · exfalso
          have hΔ : ℓ * u * ℓ⁻¹ ∈ lin2Delta (thompsonJ S) Z x := ⟨hw', hwZ, hwZx⟩
          apply E.Delta_not_fused hcfg (Z := Z) rfl hc hx hxS hΔ (ℓ * g⁻¹)
          have := mem_conjR.mp hw'B
          have e : (ℓ * g⁻¹)⁻¹ * (ℓ * u * ℓ⁻¹) * (ℓ * g⁻¹) = g * ℓ⁻¹ * (ℓ * u * ℓ⁻¹) *
              (g * ℓ⁻¹)⁻¹ := by group
          rw [e]
          exact this

theorem card_centerOf_R_mul :
    Nat.card (centerOf (thompsonJ S)) * 2 ^ n = Nat.card (blockU L) := by
  obtain ⟨x, hx, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  obtain ⟨hRU, hUV⟩ := E.RUU hcfg hx hxS
  have hcardR : Nat.card (thompsonJ S) = Nat.card (blockU L) * 2 ^ n := by
    have := lin2_card_sylow hcfg.lin2 (E.Rsyl hcfg)
    rwa [E.OL hcfg] at this
  have hle : conjR (blockU L) x ≤ Subgroup.normalizer (blockU L : Set G) :=
    (hRU ▸ le_sup_right : conjR (blockU L) x ≤ thompsonJ S).trans (E.R_le_normalizer_U hcfg)
  have h1 := card_sup_mul_card_inf hle
  rw [sup_comm, ← hRU, inf_comm, hUV, card_conjR, hcardR] at h1
  have hUpos : 0 < Nat.card (blockU L) := Nat.card_pos
  have : Nat.card (blockU L) * (Nat.card (centerOf (thompsonJ S)) * 2 ^ n) =
      Nat.card (blockU L) * Nat.card (blockU L) := by
    rw [← h1]; ring
  exact Nat.eq_of_mul_eq_mul_left hUpos this

theorem centerOf_mul_conj_eq_U {ℓ : G} (hℓ : ℓ ∈ L)
    (hℓn : ℓ ∉ Subgroup.normalizer ((centerOf (thompsonJ S) : Subgroup G) : Set G)) :
    ((centerOf (thompsonJ S) : Subgroup G) : Set G) *
        ((conjR (centerOf (thompsonJ S)) ℓ : Subgroup G) : Set G) = ((blockU L : Subgroup G) : Set G) := by
  set R := thompsonJ S with hR
  set U := blockU L with hU
  set ZR := centerOf R with hZR
  have hℓU : conjR U ℓ = U := conjR_eq_of_mem_normalizer (E.L_le_normalizer_U hcfg hℓ)
  have hZRU : ZR ≤ U := E.centerOf_R_le_U hcfg
  have hZRℓU : conjR ZR ℓ ≤ U := by
    calc conjR ZR ℓ ≤ conjR U ℓ := conjR_mono hZRU ℓ
      _ = U := hℓU
  have hRL : R ≤ L := (E.Rsyl hcfg).le
  have hRℓL : conjR R ℓ ≤ L := fun y hy => by
    have := hRL (mem_conjR.mp hy)
    have h2 := L.mul_mem (L.mul_mem (L.inv_mem hℓ) this) hℓ
    simpa [mul_assoc] using h2
  have hRne : conjR R ℓ ≠ R := by
    intro h
    apply hℓn
    have h1 : conjR ZR ℓ = ZR := by
      rw [hZR, conjR_centerOf, h]
    exact conjR_eq_self_iff.mp h1
  have hLsup : L ≤ R ⊔ conjR R ℓ := by
    by_contra hL
    have hX := inf_le_normalizer_of_isLin2Type (by have := hcfg.one_lt; omega : 0 < n) hcfg.lin2 (E.Rsyl hcfg)
      (le_sup_left : R ≤ R ⊔ conjR R ℓ) hL
    have hXL : R ⊔ conjR R ℓ ≤ L := sup_le hRL hRℓL
    have hXN : R ⊔ conjR R ℓ ≤ Subgroup.normalizer (R : Set G) :=
      fun y hy => hX ⟨hXL hy, hy⟩
    have hRℓN : conjR R ℓ ≤ Subgroup.normalizer (R : Set G) := le_sup_right.trans hXN
    have hX2 : IsPGroup 2 ↥(R ⊔ conjR R ℓ) :=
      (E.Rsyl hcfg).isPGroup.to_sup_of_normal_left' ((isPGroup_conjR_iff 2).mpr
        (E.Rsyl hcfg).isPGroup) hRℓN
    have hEq := (E.Rsyl hcfg).eq_of_le (le_sup_left : R ≤ R ⊔ conjR R ℓ) hXL hX2
    have hle : conjR R ℓ ≤ R := (le_sup_right : conjR R ℓ ≤ R ⊔ conjR R ℓ).trans hEq.le
    exact hRne (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjR]))
  have hinf : ZR ⊓ conjR ZR ℓ ≤ blockZ L := by
    intro v hv
    have hvC1 : R ≤ Subgroup.centralizer ({v} : Set G) := fun r hr =>
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.mp hv.1.2 r hr)
    have hvC2 : conjR R ℓ ≤ Subgroup.centralizer ({v} : Set G) := by
      have : v ∈ centerOf (conjR R ℓ) := by rw [← conjR_centerOf]; exact hv.2
      exact fun r hr => Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.mp this.2 r hr)
    have hLC : L ≤ Subgroup.centralizer ({v} : Set G) := hLsup.trans (sup_le hvC1 hvC2)
    exact ⟨hZRU hv.1, fun l hl => Subgroup.mem_centralizer_singleton_iff.mp (hLC hl)⟩
  have hbZ : blockZ L ≤ ZR ⊓ conjR ZR ℓ := by
    have hbl : conjR (blockZ L) ℓ = blockZ L := by
      unfold blockZ
      rw [conjR_inf, ← conjR_centralizer, hℓU, conjR_eq_of_mem hℓ]
    refine le_inf (E.blockZ_le_centerOf_R hcfg) ?_
    rw [← hbl]
    exact conjR_mono (E.blockZ_le_centerOf_R hcfg) ℓ
  have hEq : ZR ⊓ conjR ZR ℓ = blockZ L := le_antisymm hinf hbZ
  have h1 := card_mul_set_mul_card_inf ZR (conjR ZR ℓ)
  rw [hEq, card_conjR] at h1
  have hZRc := E.card_centerOf_R_mul hcfg
  have hUc := lin2_card_U hcfg.lin2
  have hpos : 0 < Nat.card (blockZ L) := Nat.card_pos
  have hsub : ((ZR : Set G) * (conjR ZR ℓ : Set G)) ⊆ (U : Set G) := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact U.mul_mem (hZRU ha) (hZRℓU hb)
  apply Set.eq_of_subset_of_ncard_le hsub _ (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  show Nat.card U ≤ Nat.card ((ZR : Set G) * (conjR ZR ℓ : Set G))
  apply Nat.le_of_mul_le_mul_right _ hpos
  calc Nat.card U * Nat.card (blockZ L) = 2 ^ (2 * n) * Nat.card (blockZ L) * Nat.card (blockZ L) := by
        rw [hUc]
    _ = Nat.card ZR * Nat.card ZR := by
        have : Nat.card ZR = 2 ^ n * Nat.card (blockZ L) := by
          apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 ^ n by positivity)
          rw [hZRc, hUc, mul_comm (2 ^ n) _]
          ring
        rw [this]; ring
    _ ≤ _ := by rw [← h1]

theorem not_L_le_normalizer_centerOf_R :
    ¬ L ≤ Subgroup.normalizer ((centerOf (thompsonJ S) : Subgroup G) : Set G) := by
  intro hL
  have hirr := hcfg.short.2.2.2.2.2
  have h := hirr (centerOf (thompsonJ S)) (E.blockZ_le_centerOf_R hcfg)
    (E.centerOf_R_le_U hcfg) hL
  have hZRc := E.card_centerOf_R_mul hcfg
  have hUc := lin2_card_U hcfg.lin2
  have hpos : 0 < Nat.card (blockZ L) := Nat.card_pos
  have h2 : 4 ≤ 2 ^ n := hcfg.four_le_two_pow
  rcases h with h | h
  · rw [h, hUc] at hZRc
    have : Nat.card (blockZ L) * 2 ^ n = Nat.card (blockZ L) * 2 ^ (2 * n) := by
      rw [hZRc]; ring
    have h3 := Nat.eq_of_mul_eq_mul_left hpos this
    have h4 : 2 ^ n < 2 ^ (2 * n) :=
      Nat.pow_lt_pow_right (by norm_num) (by have := hcfg.one_lt; omega)
    omega
  · rw [h] at hZRc
    have hUpos : 0 < Nat.card (blockU L) := Nat.card_pos
    nlinarith

theorem exists_mem_Ls_not_mem_normalizer {s x : G} (hs : s ∈ S) (hsR : s ∉ thompsonJ S)
    (hs2 : s ^ 2 = 1) (hx : x ∈ T) (hxS : x ∉ S)
    (hOs : pCoreOf 2 (L ⊓ Subgroup.centralizer ({s} : Set G)) =
      blockU L ⊓ Subgroup.centralizer ({s} : Set G)) :
    ∃ ℓ ∈ L ⊓ Subgroup.centralizer ({s} : Set G),
      ℓ ∉ Subgroup.normalizer ((centerOf (thompsonJ S) : Subgroup G) : Set G) := by
  set R := thompsonJ S with hR
  set C := Subgroup.centralizer ({s} : Set G) with hC
  by_contra hcon
  have hLs : ∀ ℓ ∈ L ⊓ C, ℓ ∈ Subgroup.normalizer ((centerOf R : Subgroup G) : Set G) := by
    intro ℓ hℓ
    by_contra h
    exact hcon ⟨ℓ, hℓ, h⟩
  have hRL : R ≤ L := (E.Rsyl hcfg).le
  have hRN : R ≤ Subgroup.normalizer ((centerOf R : Subgroup G) : Set G) := fun r hr =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun z hz =>
      (Subgroup.mem_centralizer_iff.mp hz.2 r hr).symm)
  have hnotL := E.not_L_le_normalizer_centerOf_R hcfg
  have hX := inf_le_normalizer_of_isLin2Type (by have := hcfg.one_lt; omega : 0 < n) hcfg.lin2
    (E.Rsyl hcfg) hRN hnotL
  have hLsR : ∀ ℓ ∈ L ⊓ C, ℓ ∈ Subgroup.normalizer (R : Set G) := fun ℓ hℓ =>
    hX ⟨hℓ.1, hLs ℓ hℓ⟩
  have h2sub : ∀ Q' : Subgroup G, Q' ≤ L ⊓ C → IsPGroup 2 Q' → Q' ≤ R ⊓ C := by
    intro Q' hQ'L hQ'2
    have hQN : Q' ≤ Subgroup.normalizer (R : Set G) := fun q hq => hLsR q (hQ'L hq)
    have h2 : IsPGroup 2 ↥(R ⊔ Q') := (E.Rsyl hcfg).isPGroup.to_sup_of_normal_left' hQ'2 hQN
    have hle : R ⊔ Q' ≤ L := sup_le hRL (hQ'L.trans inf_le_left)
    have heq := (E.Rsyl hcfg).eq_of_le le_sup_left hle h2
    exact le_inf (le_sup_right.trans heq.le) (hQ'L.trans inf_le_right)
  have hRs2 : IsPGroup 2 ↥(R ⊓ C) := (E.Rsyl hcfg).isPGroup.to_le inf_le_left
  have hRsL : R ⊓ C ≤ L ⊓ C := inf_le_inf_right _ hRL
  have hnormRs : L ⊓ C ≤ Subgroup.normalizer ((R ⊓ C : Subgroup G) : Set G) := by
    intro g hg
    have hconj : conjR (R ⊓ C) g ≤ R ⊓ C := by
      apply h2sub
      · intro y hy
        have h1 := hRsL (mem_conjR.mp hy)
        have h2 := (L ⊓ C).mul_mem ((L ⊓ C).mul_mem ((L ⊓ C).inv_mem hg) h1) hg
        simpa [mul_assoc] using h2
      · exact (isPGroup_conjR_iff 2).mpr hRs2
    have heq : conjR (R ⊓ C) g = R ⊓ C :=
      Subgroup.eq_of_le_of_card_ge hconj (by rw [card_conjR])
    exact conjR_eq_self_iff.mp heq
  have hle := le_pCoreOf_of_normalizes hRsL hnormRs hRs2
  rw [hOs] at hle
  have hcardle := Subgroup.card_le_of_le hle
  obtain ⟨hA, hB⟩ := E.U_s_values hcfg hs hsR hs2 hx hxS
  have hRc := E.card_R_inf_centralizer hcfg hs hsR hs2
  have h2n : 2 ≤ n := hcfg.one_lt
  by_cases hc : centerOf L = ⊥
  · rw [hRc.1 hc, (hA hc).1] at hcardle
    have : 2 ^ n < 2 ^ (3 * n / 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · rw [hRc.2 hc, (hB hc).1] at hcardle
    have : 2 ^ (3 * n / 2) < 2 ^ (2 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

theorem Ls_le_normalizer_U_s {s : G} :
    L ⊓ Subgroup.centralizer ({s} : Set G) ≤
      Subgroup.normalizer ((blockU L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) : Set G) := by
  intro ℓ ⟨hℓ, hℓs⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hU : y ∈ blockU L ↔ ℓ * y * ℓ⁻¹ ∈ blockU L :=
    Subgroup.mem_normalizer_iff.mp (E.L_le_normalizer_U hcfg hℓ) y
  have hc : ℓ * s = s * ℓ := Subgroup.mem_centralizer_singleton_iff.mp hℓs
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hU, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · have h' : y * s = s * y := h
    calc ℓ * y * ℓ⁻¹ * s = ℓ * y * (ℓ⁻¹ * s) := by group
      _ = ℓ * y * (s * ℓ⁻¹) := by
        have : ℓ⁻¹ * s = s * ℓ⁻¹ := by
          calc ℓ⁻¹ * s = ℓ⁻¹ * s * ℓ * ℓ⁻¹ := by group
            _ = ℓ⁻¹ * (s * ℓ) * ℓ⁻¹ := by group
            _ = ℓ⁻¹ * (ℓ * s) * ℓ⁻¹ := by rw [hc]
            _ = s * ℓ⁻¹ := by group
        rw [this]
      _ = ℓ * (y * s) * ℓ⁻¹ := by group
      _ = ℓ * (s * y) * ℓ⁻¹ := by rw [h']
      _ = s * (ℓ * y * ℓ⁻¹) := by
        calc ℓ * (s * y) * ℓ⁻¹ = (ℓ * s) * y * ℓ⁻¹ := by group
          _ = (s * ℓ) * y * ℓ⁻¹ := by rw [hc]
          _ = s * (ℓ * y * ℓ⁻¹) := by group
  · have h' : ℓ * y * ℓ⁻¹ * s = s * (ℓ * y * ℓ⁻¹) := h
    show y * s = s * y
    have hsl : ℓ⁻¹ * s * ℓ = s := by
      calc ℓ⁻¹ * s * ℓ = ℓ⁻¹ * (s * ℓ) := by group
        _ = ℓ⁻¹ * (ℓ * s) := by rw [hc]
        _ = s := by group
    calc y * s = ℓ⁻¹ * (ℓ * y * ℓ⁻¹ * s) * ℓ := by
          calc y * s = ℓ⁻¹ * (ℓ * y * ℓ⁻¹) * (ℓ * s) := by group
            _ = ℓ⁻¹ * (ℓ * y * ℓ⁻¹) * (s * ℓ) := by rw [hc]
            _ = ℓ⁻¹ * (ℓ * y * ℓ⁻¹ * s) * ℓ := by group
      _ = ℓ⁻¹ * (s * (ℓ * y * ℓ⁻¹)) * ℓ := by rw [h']
      _ = (ℓ⁻¹ * s * ℓ) * y := by group
      _ = s * y := by rw [hsl]

theorem normalizer_U_s_le {s : G} (hs : s ∈ S) (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1)
    (hOs : pCoreOf 2 (L ⊓ Subgroup.centralizer ({s} : Set G)) =
      blockU L ⊓ Subgroup.centralizer ({s} : Set G)) :
    Subgroup.normalizer ((blockU L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (blockU L : Set G) := by
  obtain ⟨x, hx, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  set R := thompsonJ S with hR
  set Z := lin2Z L R with hZdef
  set U := blockU L with hU
  set C := Subgroup.centralizer ({s} : Set G) with hC
  set Us := U ⊓ C with hUs
  have hZU : Z ≤ U := (lin2Z_le_centerOf E.h16 hcfg rfl).trans (E.centerOf_R_le_U hcfg)
  obtain ⟨hs'S, hs'R, hs'2⟩ := E.conj_involution_mem hcfg hs hsR hs2 hx
  obtain ⟨-, -, -, hev, -⟩ := E.exists_f₀ hcfg
  have hn2 : 2 ≤ n := hcfg.one_lt
  have hcZ : Nat.card (Z ⊓ C : Subgroup G) = 2 ^ (n / 2) := E.card_Z_inf_centralizer hcfg rfl hs hsR hs2
  have hcZx : Nat.card (conjR Z x ⊓ C : Subgroup G) = 2 ^ (n / 2) := by
    rw [hC, conjR_inf_centralizer, card_conjR]
    exact E.card_Z_inf_centralizer hcfg rfl hs'S hs'R hs'2
  have hnb : (2 : ℕ) ^ (n / 2) ≠ 1 := by
    have : 1 ≤ n / 2 := by omega
    exact (Nat.one_lt_two_pow (by omega)).ne'
  have hZx_le : conjR Z x ≤ U := by
    rcases E.Zcases hcfg (Z := Z) rfl hx hxS with ⟨-, hZx, -⟩ | ⟨-, hZR2, -⟩
    · rw [hZx]; exact hZU
    · exact (hZR2 ▸ le_sup_right : conjR Z x ≤ centerOf R).trans (E.centerOf_R_le_U hcfg)
  have hnt : ∀ A : Subgroup G, A ≤ U → Nat.card (A ⊓ C : Subgroup G) = 2 ^ (n / 2) →
      A ⊓ Us ≠ ⊥ := by
    intro A hAU hcard h
    have hle : A ⊓ C ≤ A ⊓ Us := le_inf inf_le_left (le_inf (inf_le_left.trans hAU) inf_le_right)
    rw [h] at hle
    have : Nat.card (A ⊓ C : Subgroup G) ≤ 1 := by
      have := Subgroup.card_le_of_le hle
      simpa using this
    have : (2 : ℕ) ^ (n / 2) ≤ 1 := hcard ▸ this
    exact hnb (le_antisymm this (Nat.one_le_two_pow))
  have hZne : Z ⊓ Us ≠ ⊥ := hnt Z hZU hcZ
  have hZxne : conjR Z x ⊓ Us ≠ ⊥ := hnt _ hZx_le hcZx
  let W : Set (Subgroup G) := {A | (∃ g, A = conjR Z g) ∧ A ⊓ Us ≠ ⊥}
  have hWU : ∀ A ∈ W, A ≤ U := by
    rintro A ⟨⟨g, rfl⟩, hne⟩
    refine E.conj_Z_le_U hcfg (fun h => hne ?_)
    rw [eq_bot_iff]
    exact (inf_le_inf_left _ inf_le_left).trans h.le
  have hWconj : ∀ y ∈ Subgroup.normalizer (Us : Set G), ∀ A ∈ W, conjR A y ∈ W := by
    rintro y hy A ⟨⟨g, rfl⟩, hne⟩
    refine ⟨⟨g * y, by rw [conjR_conjR]⟩, fun h => hne ?_⟩
    have e : conjR Us y = Us := conjR_eq_of_mem_normalizer hy
    have : conjR (conjR Z g ⊓ Us) y = ⊥ := by rw [conjR_inf, e]; exact h
    exact conjR_eq_bot_iff.mp this
  have hLs : ∀ ℓ ∈ L ⊓ C, ∀ A : Subgroup G, A ⊓ Us ≠ ⊥ → conjR A ℓ ⊓ Us ≠ ⊥ := by
    intro ℓ hℓ A hA h
    apply hA
    have e : conjR Us ℓ = Us := conjR_eq_of_mem_normalizer (E.Ls_le_normalizer_U_s hcfg hℓ)
    have : conjR (A ⊓ Us) ℓ = ⊥ := by rw [conjR_inf, e]; exact h
    exact conjR_eq_bot_iff.mp this
  set V : Subgroup G := sSup W with hV
  have hVU : V ≤ U := sSup_le hWU
  have hWV : ∀ A ∈ W, A ≤ V := fun A hA => le_sSup hA
  obtain ⟨ℓ, hℓ, hℓn⟩ := E.exists_mem_Ls_not_mem_normalizer hcfg hs hsR hs2 hx hxS hOs
  have hZRV : centerOf R ≤ V ∧ conjR (centerOf R) ℓ ≤ V := by
    rcases lin2Z_cases (Z := Z) rfl with ⟨hc, hZR⟩ | ⟨hc, hZL⟩
    · have hZ1 : Z ∈ W := ⟨⟨1, (conjR_one Z).symm⟩, hZne⟩
      have hZℓ : conjR Z ℓ ∈ W := ⟨⟨ℓ, rfl⟩, hLs ℓ hℓ Z hZne⟩
      rw [← hZR]
      exact ⟨hWV _ hZ1, hWV _ hZℓ⟩
    · rcases E.Zcases hcfg (Z := Z) rfl hx hxS with ⟨hc', -⟩ | ⟨-, hZR2, -⟩
      · exact absurd hc' hc
      · have hZ1 : Z ∈ W := ⟨⟨1, (conjR_one Z).symm⟩, hZne⟩
        have hZx1 : conjR Z x ∈ W := ⟨⟨x, rfl⟩, hZxne⟩
        have hZℓ : conjR Z ℓ ∈ W := ⟨⟨ℓ, rfl⟩, hLs ℓ hℓ Z hZne⟩
        have hZxℓ : conjR (conjR Z x) ℓ ∈ W :=
          ⟨⟨x * ℓ, by rw [conjR_conjR]⟩, hLs ℓ hℓ _ hZxne⟩
        rw [hZR2, conjR_sup]
        exact ⟨sup_le (hWV _ hZ1) (hWV _ hZx1), sup_le (hWV _ hZℓ) (hWV _ hZxℓ)⟩
  have hUV : U ≤ V := by
    have hset := E.centerOf_mul_conj_eq_U hcfg hℓ.1 hℓn
    intro u hu
    have : u ∈ ((centerOf R : Subgroup G) : Set G) * ((conjR (centerOf R) ℓ : Subgroup G) : Set G) := by
      rw [hset]; exact hu
    obtain ⟨a, ha, b, hb, rfl⟩ := this
    exact V.mul_mem (hZRV.1 ha) (hZRV.2 hb)
  have hVeq : V = U := le_antisymm hVU hUV
  intro y hy
  have hle : conjR V y ≤ V := by
    have h1 : conjR V y = ⨆ A : W, conjR (A : Subgroup G) y := by
      rw [hV, sSup_eq_iSup', conjR_def, Subgroup.map_iSup]; rfl
    rw [h1]
    exact iSup_le fun ⟨A, hA⟩ => hWV _ (hWconj y hy A hA)
  have heq : conjR V y = V := Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjR])
  rw [hVeq] at heq
  exact conjR_eq_self_iff.mp heq

end Lines

end Lin2Hyp

end CFSG.QuasithinUnique.Lin2
