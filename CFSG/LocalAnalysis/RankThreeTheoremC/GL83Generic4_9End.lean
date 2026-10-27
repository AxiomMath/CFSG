module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9End2
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9End3
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G]

theorem gen49e_core {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {M T R : Subgroup G} {x : G}
    (hT2 : IsPGroup 2 T) (hNT : normalizer (T : Set G) = M)
    (hRM : R ≤ M) (hRe : IsElemAbelian p R) (hRc : Nat.card R = p ^ 2) (hxR : x ∈ R)
    (hx1 : x ≠ 1)
    (hfpf : ∀ t ∈ T, t * x = x * t → t = 1)
    (hcomm : ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → R ≤ normalizer (Y : Set G) →
      ∀ y ∈ Y, y * x * y⁻¹ * x⁻¹ ∈ T)
    (hinv : ∀ F : Subgroup G, ¬ p ∣ Nat.card F → R ≤ normalizer (F : Set G) → F ≤ M)
    (hrk3 : ∀ H : Subgroup G, IsTwoLocal H → R ≤ H → 3 ≤ CFSG.Open.pRank p H → H ≤ M)
    (hproper : ∀ Y : Subgroup G, Y ≠ ⊥ → IsPGroup 2 Y → normalizer (Y : Set G) ≠ ⊤)
    (hcover : Gen49Cover G p M x R)
    {Y : Subgroup G} (hY0 : Y ≠ ⊥) (hY2 : IsPGroup 2 Y) (hRY : R ≤ normalizer (Y : Set G))
    (hYM : ¬ normalizer (Y : Set G) ≤ M)
    (hmax : ∀ Y' : Subgroup G, Y' ≠ ⊥ → IsPGroup 2 Y' → R ≤ normalizer (Y' : Set G) →
      ¬ normalizer (Y' : Set G) ≤ M → Nat.card Y' ≤ Nat.card Y) : False := by
  have hp' : p.Prime := Fact.out
  set H := normalizer (Y : Set G) with hH
  have hYcop : Nat.Coprime p (Nat.card Y) := gen49e_coprime_card_two hp' hp hY2
  have hYMle : Y ≤ M := hinv Y ((Nat.Prime.coprime_iff_not_dvd hp').mp hYcop) hRY
  have hHtop : H ≠ ⊤ := hproper Y hY0 hY2
  have hrank : CFSG.Open.pRank p H ≤ 2 := by
    by_contra h
    exact hYM (hrk3 H ⟨Y, hY0, hY2, rfl⟩ hRY (by omega))
  obtain ⟨hDH, hHD, hDcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p H
  have hDM : rankThreePrimeCore p H ≤ M :=
    hinv _ ((Nat.Prime.coprime_iff_not_dvd hp').mp hDcop) (hRY.trans hHD)
  obtain ⟨X, hXH, -, hXn, hXc, hXM⟩ := hcover H hHtop hRY hrank hYM hDM
  have hXnorm : H ≤ normalizer (X : Set G) := (normal_subgroupOf_iff_le_normalizer hXH).mp hXn
  have hRp : IsPGroup p R := IsPGroup.of_card hRc
  have he := gen49e_inf_le hp hT2 hNT hRM hRp hxR hfpf hY0 hY2 hRY hmax hDM hXH hXnorm hXc hXM
  have hTY : T ≤ Y := gen49e_le_of_inf_le hT2 hY2 (hNT ▸ hYMle) he
  have hxT : x ∈ normalizer (T : Set G) := hNT ▸ hRM hxR
  have hCH := gen49e_centralizer_le hxT hfpf hTY (hcomm Y hY2 hYMle hRY)
  have hxord : orderOf x = p := orderOf_eq_prime (hRe.2 x hxR) hx1
  apply hXM
  intro k hk
  obtain ⟨o, ho, c, hcH, hcx, rfl⟩ :=
    gen49e_mem_mul_centralizer hp' hDH hHD hDcop (hRY hxR) (hXH hk) hxord (hXc k hk)
  exact M.mul_mem (hDM ho) (hNT ▸ hCH c hcH hcx)

theorem gen49_endgame {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {M T R : Subgroup G} {x : G}
    (hT2 : IsPGroup 2 T) (hNT : normalizer (T : Set G) = M)
    (hRM : R ≤ M) (hRe : IsElemAbelian p R) (hRc : Nat.card R = p ^ 2) (hxR : x ∈ R)
    (hx1 : x ≠ 1)
    (hfpf : ∀ t ∈ T, t * x = x * t → t = 1)
    (hcomm : ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → R ≤ normalizer (Y : Set G) →
      ∀ y ∈ Y, y * x * y⁻¹ * x⁻¹ ∈ T)
    (hinv : ∀ F : Subgroup G, ¬ p ∣ Nat.card F → R ≤ normalizer (F : Set G) → F ≤ M)
    (hrk3 : ∀ H : Subgroup G, IsTwoLocal H → R ≤ H → 3 ≤ CFSG.Open.pRank p H → H ≤ M)
    (hproper : ∀ Y : Subgroup G, Y ≠ ⊥ → IsPGroup 2 Y → normalizer (Y : Set G) ≠ ⊤)
    (hcover : Gen49Cover G p M x R) :
    ∀ Y : Subgroup G, Y ≠ ⊥ → IsPGroup 2 Y → R ≤ normalizer (Y : Set G) →
      normalizer (Y : Set G) ≤ M := by
  intro Y₀ hY₀0 hY₀2 hRY₀
  by_contra hY₀M
  obtain ⟨Y, ⟨hY0, hY2, hRY, hYM⟩, hmax⟩ := Set.exists_max_image
    {Y : Subgroup G | Y ≠ ⊥ ∧ IsPGroup 2 Y ∧ R ≤ normalizer (Y : Set G) ∧
      ¬ normalizer (Y : Set G) ≤ M}
    (fun Y : Subgroup G => Nat.card Y) (Set.toFinite _) ⟨Y₀, hY₀0, hY₀2, hRY₀, hY₀M⟩
  exact gen49e_core hp hT2 hNT hRM hRe hRc hxR hx1 hfpf hcomm hinv hrk3 hproper hcover hY0 hY2
    hRY hYM fun Y' h0 h2 hR hM => hmax Y' ⟨h0, h2, hR, hM⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
