module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9End2
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.LocalAnalysis.SignalizerFunctor.NormalizedSylowContainment
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem u3e_inf_le {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {M T R : Subgroup G} {x : G}
    (hT2 : IsPGroup 2 T) (hTM : T ≤ M) (hRT : R ≤ normalizer (T : Set G)) (hRp : IsPGroup p R)
    (hxR : x ∈ R) (hfpf : ∀ t ∈ T, t * x = x * t → t = 1)
    {Y : Subgroup G} (hY0 : Y ≠ ⊥) (hY2 : IsPGroup 2 Y) (hRY : R ≤ normalizer (Y : Set G))
    (hmax : ∀ Y' : Subgroup G, Y' ≠ ⊥ → IsPGroup 2 Y' → R ≤ normalizer (Y' : Set G) →
      ¬ normalizer (Y' : Set G) ≤ M → Nat.card Y' ≤ Nat.card Y)
    (hDM : rankThreePrimeCore p (normalizer (Y : Set G)) ≤ M)
    {X : Subgroup G} (hXH : X ≤ normalizer (Y : Set G))
    (hXn : normalizer (Y : Set G) ≤ normalizer (X : Set G))
    (hXc : ∀ h ∈ X, h * x * h⁻¹ * x⁻¹ ∈ rankThreePrimeCore p (normalizer (Y : Set G)))
    (hXM : ¬ X ≤ M) :
    T ⊓ normalizer (Y : Set G) ≤ Y := by
  set H := normalizer (Y : Set G) with hH
  set D := rankThreePrimeCore p H with hD
  obtain ⟨hDH, hHD, hDcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p H
  set W := T ⊓ H with hW
  have hWH : W ≤ H := inf_le_right
  have hW2 : IsPGroup 2 W := hT2.to_le inf_le_left
  have hWM : W ≤ M := inf_le_left.trans hTM
  have hWD : W ≤ normalizer (D : Set G) := hWH.trans hHD
  have hRW : R ≤ normalizer (W : Set G) := by
    refine le_normalizer_iff.mpr fun r hr w hw => ⟨le_normalizer_iff.mp hRT r hr w hw.1, ?_⟩
    exact H.mul_mem (H.mul_mem (hRY hr) hw.2) (H.inv_mem (hRY hr))
  have hYD : Y ≤ D := gen49e_le_primeCore Subgroup.le_normalizer le_rfl
    (gen49e_coprime_card_two Fact.out hp hY2)
  have hxH : x ∈ H := hRY hxR
  have hcomm : ∀ w ∈ W, ∀ k ∈ X, k * w * k⁻¹ * w⁻¹ ∈ D :=
    gen49e_commutator_mem hHD hXn hxH hXc hWH
      (gen49e_exists_comm (hRW hxR) fun w hw hc => hfpf w hw.1 hc)
  set N := D ⊔ W with hN
  have hXN : X ≤ normalizer (N : Set G) := gen49e_le_normalizer_sup hHD hXH hcomm
  have hNcop : Nat.Coprime p (Nat.card N) :=
    CFSG.LocalAnalysis.RankThreeUC.coprime_card_sup_of_le_normalizer hWD hDcop
      (gen49e_coprime_card_two Fact.out hp hW2)
  have hRN : R ≤ normalizer (N : Set G) :=
    (le_inf (hRY.trans hHD) hRW).trans (Subgroup.inf_normalizer_le_normalizer_sup D W)
  have hNM : N ≤ M := sup_le hDM hWM
  have hYWN : Y ⊔ W ≤ N := sup_le (hYD.trans le_sup_left) le_sup_right
  have hYW2 : IsPGroup 2 (Y ⊔ W : Subgroup G) := hY2.to_sup_of_normal_left' hW2 hWH
  have hRYW : R ≤ normalizer ((Y ⊔ W : Subgroup G) : Set G) :=
    (le_inf hRY hRW).trans (Subgroup.inf_normalizer_le_normalizer_sup Y W)
  obtain ⟨S, hYWS, hRS⟩ := CFSG.SignalizerFunctor.Helpers.normalized_pgroup_actor_sylow_containing
    p 2 Fact.out Nat.prime_two R N (Y ⊔ W) hRp hRN hNcop hYWN hYW2 hRYW
  set S' : Subgroup G := (S : Subgroup N).map N.subtype with hS'
  have hfr : X ≤ N ⊔ normalizer (S' : Set G) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.le_sup_normalizer_of_isSylowOf hXN ⟨S, rfl⟩
  have hS'M : ¬ normalizer (S' : Set G) ≤ M := fun h => hXM (hfr.trans (sup_le hNM h))
  have hYS' : Y ≤ S' := le_sup_left.trans hYWS
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map N.subtype
  have hS'0 : S' ≠ ⊥ := fun h => hY0 (le_bot_iff.mp (h ▸ hYS'))
  have hcard := hmax S' hS'0 hS'2 hRS hS'M
  have hSY : Y = S' := eq_of_le_of_card_ge hYS' hcard
  exact le_sup_right.trans (hYWS.trans hSY.ge)

theorem u3e_T_le {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {M R : Subgroup G} {x : G}
    (hRp : IsPGroup p R) (hxR : x ∈ R)
    (hinv : ∀ F : Subgroup G, ¬ p ∣ Nat.card F → R ≤ normalizer (F : Set G) → F ≤ M)
    (hrk3 : ∀ H : Subgroup G, IsTwoLocal H → R ≤ H → 3 ≤ CFSG.Open.pRank p H → H ≤ M)
    (hproper : ∀ Y : Subgroup G, Y ≠ ⊥ → IsPGroup 2 Y → normalizer (Y : Set G) ≠ ⊤)
    (hcover : Gen49Cover G p M x R)
    {Y : Subgroup G} (hY0 : Y ≠ ⊥) (hY2 : IsPGroup 2 Y) (hRY : R ≤ normalizer (Y : Set G))
    (hYM : ¬ normalizer (Y : Set G) ≤ M)
    (hmax : ∀ Y' : Subgroup G, Y' ≠ ⊥ → IsPGroup 2 Y' → R ≤ normalizer (Y' : Set G) →
      ¬ normalizer (Y' : Set G) ≤ M → Nat.card Y' ≤ Nat.card Y)
    {T : Subgroup G} (hT2 : IsPGroup 2 T) (hTM : T ≤ M) (hRT : R ≤ normalizer (T : Set G))
    (hYT : Y ≤ normalizer (T : Set G)) (hfpf : ∀ t ∈ T, t * x = x * t → t = 1) :
    T ≤ Y := by
  have hp' : p.Prime := Fact.out
  have hYcop : Nat.Coprime p (Nat.card Y) := gen49e_coprime_card_two hp' hp2 hY2
  have hYMle : Y ≤ M := hinv Y ((Nat.Prime.coprime_iff_not_dvd hp').mp hYcop) hRY
  have hHtop : normalizer (Y : Set G) ≠ ⊤ := hproper Y hY0 hY2
  have hrank : CFSG.Open.pRank p (normalizer (Y : Set G)) ≤ 2 := by
    by_contra h
    exact hYM (hrk3 (normalizer (Y : Set G)) ⟨Y, hY0, hY2, rfl⟩ hRY (by omega))
  obtain ⟨hDH, hHD, hDcop⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p (normalizer (Y : Set G))
  have hDM : rankThreePrimeCore p (normalizer (Y : Set G)) ≤ M :=
    hinv _ ((Nat.Prime.coprime_iff_not_dvd hp').mp hDcop) (hRY.trans hHD)
  obtain ⟨X, hXH, -, hXn, hXc, hXM⟩ := hcover (normalizer (Y : Set G)) hHtop hRY hrank hYM hDM
  have hXnorm : normalizer (Y : Set G) ≤ normalizer (X : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hXH).mp hXn
  have he := u3e_inf_le hp2 hT2 hTM hRT hRp hxR hfpf hY0 hY2 hRY hmax hDM hXH hXnorm hXc hXM
  exact gen49e_le_of_inf_le hT2 hY2 hYT he

theorem u3_endgame {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {M R : Subgroup G} {x : G}
    (hRM : R ≤ M) (hRe : IsElemAbelian p R) (hRc : Nat.card R = p ^ 2) (hxR : x ∈ R)
    (hx1 : x ≠ 1)
    (hodd : ∀ X : Subgroup G, IsPGroup 2 X → X ≤ rankThreePrimeCore p M →
      X ≤ Subgroup.centralizer ({x} : Set G) → X = ⊥)
    (hinv : ∀ F : Subgroup G, ¬ p ∣ Nat.card F → R ≤ Subgroup.normalizer (F : Set G) → F ≤ M)
    (hrk3 : ∀ H : Subgroup G, IsTwoLocal H → R ≤ H → 3 ≤ CFSG.Open.pRank p H → H ≤ M)
    (hproper : ∀ Y : Subgroup G, Y ≠ ⊥ → IsPGroup 2 Y → Subgroup.normalizer (Y : Set G) ≠ ⊤)
    (hcover : Gen49Cover G p M x R)
    (hL43 : ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → R ≤ Subgroup.normalizer (Y : Set G) →
      CFSG.ABGLocalTools.IsSylowOf 2 (Y ⊓ rankThreePrimeCore p M) (rankThreePrimeCore p M) →
      Subgroup.normalizer (Y : Set G) ≤ M) :
    ∀ Y : Subgroup G, Y ≠ ⊥ → IsPGroup 2 Y → R ≤ Subgroup.normalizer (Y : Set G) →
      Subgroup.normalizer (Y : Set G) ≤ M := by
  intro Y₀ hY₀0 hY₀2 hRY₀
  by_contra hY₀M
  obtain ⟨Y, ⟨hY0, hY2, hRY, hYM⟩, hmax⟩ := Set.exists_max_image
    {Y : Subgroup G | Y ≠ ⊥ ∧ IsPGroup 2 Y ∧ R ≤ normalizer (Y : Set G) ∧
      ¬ normalizer (Y : Set G) ≤ M}
    (fun Y : Subgroup G => Nat.card Y) (Set.toFinite _) ⟨Y₀, hY₀0, hY₀2, hRY₀, hY₀M⟩
  have hp' : p.Prime := Fact.out
  have hRp : IsPGroup p R := IsPGroup.of_card hRc
  obtain ⟨hO'M, hMO', hO'cop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p M
  have hYcop : Nat.Coprime p (Nat.card Y) := gen49e_coprime_card_two hp' hp2 hY2
  have hYMle : Y ≤ M := hinv Y ((Nat.Prime.coprime_iff_not_dvd hp').mp hYcop) hRY
  have hYN : Y ≤ normalizer (rankThreePrimeCore p M : Set G) := hYMle.trans hMO'
  have hRN0 : R ≤ normalizer (rankThreePrimeCore p M : Set G) := hRM.trans hMO'
  have hKN : rankThreePrimeCore p M ⊔ Y ≤ normalizer (rankThreePrimeCore p M : Set G) :=
    sup_le Subgroup.le_normalizer hYN
  have hRK : R ≤ normalizer ((rankThreePrimeCore p M ⊔ Y : Subgroup G) : Set G) :=
    (le_inf hRN0 hRY).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hKcop : Nat.Coprime p (Nat.card (rankThreePrimeCore p M ⊔ Y : Subgroup G)) :=
    CFSG.LocalAnalysis.RankThreeUC.coprime_card_sup_of_le_normalizer hYN hO'cop hYcop
  obtain ⟨sylowK, hYs, hRs⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_pgroup_actor_sylow_containing p 2 Fact.out
      Nat.prime_two R (rankThreePrimeCore p M ⊔ Y : Subgroup G) Y hRp hRK hKcop le_sup_right hY2 hRY
  obtain ⟨Ssyl, hYSs, hRSs, hSyl⟩ : ∃ S : Subgroup G, Y ≤ S ∧ R ≤ normalizer (S : Set G) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 S (rankThreePrimeCore p M ⊔ Y : Subgroup G) :=
    ⟨_, hYs, hRs, ⟨sylowK, rfl⟩⟩
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 (Ssyl ⊓ rankThreePrimeCore p M)
      (rankThreePrimeCore p M) :=
    hSyl.inf_of_le_normalizer le_sup_left hKN
  have hT2 : IsPGroup 2 (Ssyl ⊓ rankThreePrimeCore p M : Subgroup G) :=
    hSyl.isPGroup.to_le inf_le_left
  have hTM : Ssyl ⊓ rankThreePrimeCore p M ≤ M := inf_le_right.trans hO'M
  have hRT : R ≤ normalizer ((Ssyl ⊓ rankThreePrimeCore p M : Subgroup G) : Set G) :=
    (le_inf hRSs hRN0).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hYT : Y ≤ normalizer ((Ssyl ⊓ rankThreePrimeCore p M : Subgroup G) : Set G) :=
    (le_inf (hYSs.trans Subgroup.le_normalizer) hYN).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hfpf : ∀ t ∈ Ssyl ⊓ rankThreePrimeCore p M, t * x = x * t → t = 1 := by
    intro t ht hc
    have htT : Subgroup.zpowers t ≤ Ssyl ⊓ rankThreePrimeCore p M := Subgroup.zpowers_le.mpr ht
    have htC : Subgroup.zpowers t ≤ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun h hh => by
        rw [Set.mem_singleton_iff.mp hh]; exact hc.symm)
    exact Subgroup.zpowers_eq_bot.mp
      (hodd (Subgroup.zpowers t) (hT2.to_le htT) (htT.trans inf_le_right) htC)
  have hTY : Ssyl ⊓ rankThreePrimeCore p M ≤ Y :=
    u3e_T_le hp2 hRp hxR hinv hrk3 hproper hcover hY0 hY2 hRY hYM
      (fun Y' h0 h2 hR hM => hmax Y' ⟨h0, h2, hR, hM⟩) hT2 hTM hRT hYT hfpf
  have hYO' : Y ⊓ rankThreePrimeCore p M = Ssyl ⊓ rankThreePrimeCore p M :=
    le_antisymm (le_inf (inf_le_left.trans hYSs) inf_le_right) (le_inf hTY inf_le_right)
  exact hYM (hL43 Y hY2 hYMle hRY (by rw [hYO']; exact hTsyl))

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
