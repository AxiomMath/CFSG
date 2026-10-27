module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.RankThree.PartOne.K1214.Basic
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_rankThreePrimeCore (q : ℕ) (H : Subgroup G) {g : G}
    (hg : g ∈ normalizer (H : Set G)) : g ∈ normalizer (rankThreePrimeCore q H : Set G) := by
  have key : ∀ g ∈ normalizer (H : Set G), ∀ y ∈ rankThreePrimeCore q H,
      g * y * g⁻¹ ∈ rankThreePrimeCore q H := by
    intro g hg y hy
    set O := rankThreePrimeCore q H
    have hOH : O ≤ H := CFSG.AGLEmbedding.glbPrimeCore_le q H
    have hOn : H ≤ normalizer (O : Set G) := CFSG.AGLEmbedding.le_normalizer_glbPrimeCore q H
    have hcop : q.Coprime (Nat.card O) := CFSG.AGLEmbedding.glbPrimeCore_coprime q H
    have h1 : H.map (MulAut.conj g).toMonoidHom = H := mem_normalizer_iff_map_conj_eq.mp hg
    have h2 : (normalizer (O : Set G)).map (MulAut.conj g).toMonoidHom =
        normalizer ((O.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
      Subgroup.map_equiv_normalizer_eq O (MulAut.conj g)
    have hle : O.map (MulAut.conj g).toMonoidHom ≤ O := by
      refine CFSG.AGLEmbedding.le_glbPrimeCore ?_ ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact (mem_normalizer_iff.mp hg y).mp (hOH hy)
      · calc H = H.map (MulAut.conj g).toMonoidHom := h1.symm
          _ ≤ (normalizer (O : Set G)).map (MulAut.conj g).toMonoidHom := map_mono hOn
          _ = _ := h2
      · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) hcop
    exact hle ⟨y, hy, rfl⟩
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun hy => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hy
  simpa [mul_assoc] using this

omit [Finite G] in
theorem isSolvable_sup_of_isSolvable_normalizing {K O : Subgroup G}
    (hK : Group.IsSolvable K) (hO : Group.IsSolvable O) (hKO : K ≤ normalizer (O : Set G)) :
    Group.IsSolvable (K ⊔ O : Subgroup G) := by
  set W := K ⊔ O
  have hWO : W ≤ normalizer (O : Set G) := sup_le hKO Subgroup.le_normalizer
  have hOn : (O.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_right : O ≤ W)).mpr hWO
  have hOW : Group.IsSolvable (O.subgroupOf W) := Group.isSolvable_of_surjective
    (f := (Subgroup.subgroupOfEquivOfLe (le_sup_right : O ≤ W)).symm.toMonoidHom)
    (MulEquiv.surjective _)
  have hq : Group.IsSolvable (W ⧸ O.subgroupOf W) := by
    refine Group.isSolvable_of_surjective
      (f := (QuotientGroup.mk' (O.subgroupOf W)).comp (Subgroup.inclusion le_sup_left)) ?_
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      have hw : (w : G) ∈ (K : Set G) * (O : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right K O hKO]
        exact w.2
      obtain ⟨a, ha, x, hx, hax⟩ := hw
      refine ⟨⟨a, ha⟩, ?_⟩
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      refine Subgroup.mem_subgroupOf.mpr ?_
      change a⁻¹ * (w : G) ∈ O
      rw [← hax, inv_mul_cancel_left]
      exact hx
  exact Group.isSolvable_of_ker_le_range (O.subgroupOf W).subtype
    (QuotientGroup.mk' (O.subgroupOf W)) (by
      intro x hx
      rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
      exact ⟨⟨x, hx⟩, rfl⟩)

theorem odd_relIndex_of_covering {X K O D : Subgroup G} (hO : Odd (Nat.card O)) (hOD : O ≤ D)
    (hDX : D ≤ X) (hKX : K ≤ X) (hXO : X ≤ normalizer (O : Set G))
    (hXD : X ≤ normalizer (D : Set G)) (hcov : X ≤ K ⊔ O) : Odd (K.relIndex D) := by
  have hKO : K ≤ normalizer (O : Set G) := hKX.trans hXO
  have hKD : K ≤ normalizer (D : Set G) := hKX.trans hXD
  have hXO' : O ⊔ K = X :=
    le_antisymm (sup_le (hOD.trans hDX) hKX) (by rw [sup_comm]; exact hcov)
  have hXD' : D ⊔ K = X :=
    le_antisymm (sup_le hDX hKX) (hcov.trans (sup_le_sup_left hOD K |>.trans (by rw [sup_comm])))
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hKO
  have h2 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hKD
  rw [hXO'] at h1
  rw [hXD'] at h2
  have h3 := Subgroup.relIndex_mul_card K X
  rw [inf_eq_left.mpr hKX] at h3
  have h4 := Subgroup.relIndex_mul_card K D
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hKDpos : 0 < Nat.card (K ⊓ D : Subgroup G) := Nat.card_pos
  have h5 : K.relIndex X * Nat.card (O ⊓ K : Subgroup G) = Nat.card O := by
    apply Nat.eq_of_mul_eq_mul_right hKpos
    rw [← h1, ← h3]
    ring
  have h6 : K.relIndex X * Nat.card (D ⊓ K : Subgroup G) = Nat.card D := by
    apply Nat.eq_of_mul_eq_mul_right hKpos
    rw [← h2, ← h3]
    ring
  have h7 : K.relIndex D = K.relIndex X := by
    apply Nat.eq_of_mul_eq_mul_right hKDpos
    rw [h4, inf_comm, h6]
  rw [h7]
  exact Odd.of_dvd_nat hO (Dvd.intro _ h5)

theorem le_of_covering (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hsit : SmallRankSituation G 3 P M) (hsolv : Group.IsSolvable M) {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z)
    (hcov : centralizer ({x} : Set G) ≤ (M ⊓ centralizer ({x} : Set G)) ⊔
      rankThreePrimeCore 2 (rankThreePrimeCore 3 (centralizer ({x} : Set G))))
    {S : Subgroup G} (hS2 : IsPGroup 2 S) (hSC : S ≤ centralizer ({x} : Set G))
    (hSB : zpowers x ⊔ zpowers z ≤ normalizer (S : Set G)) : S ≤ M := by
  set X : Subgroup G := centralizer ({x} : Set G)
  set B : Subgroup G := zpowers x ⊔ zpowers z
  set D : Subgroup G := rankThreePrimeCore 3 X
  set O : Subgroup G := rankThreePrimeCore 2 D
  set K : Subgroup G := M ⊓ X
  have hpl : SmallRankPlane 3 (P : Subgroup G) x z := SmallRankPlane.of_situation hS hsit hx hz
  have hCB : centralizer (B : Set G) ≤ M := centralizer_plane_le hS hsit hx hz
  have hxz : x * z = z * x := mem_centralizer_iff.mp hz.centralizes x hx.mem
  have hBP : B ≤ (P : Subgroup G) := sup_le (zpowers_le.mpr hx.mem) (zpowers_le.mpr hz.mem)
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  have hBX : B ≤ X :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxz.symm))
  have hBK : B ≤ K := le_inf (hBP.trans hPM) hBX
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 2) hpl.card_eq
  have hDX : D ≤ X := CFSG.AGLEmbedding.glbPrimeCore_le 3 X
  have hXD : X ≤ normalizer (D : Set G) := CFSG.AGLEmbedding.le_normalizer_glbPrimeCore 3 X
  have hDcop : Nat.Coprime 3 (Nat.card D) := CFSG.AGLEmbedding.glbPrimeCore_coprime 3 X
  have hOD : O ≤ D := CFSG.AGLEmbedding.glbPrimeCore_le 2 D
  have hOodd : Odd (Nat.card O) :=
    Nat.coprime_two_left.mp (CFSG.AGLEmbedding.glbPrimeCore_coprime 2 D)
  have hXO : X ≤ normalizer (O : Set G) := fun g hg =>
    mem_normalizer_rankThreePrimeCore 2 D (hXD hg)
  have hKX : K ≤ X := inf_le_right
  have hKsolv : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (inf_le_left : K ≤ M)) (Subgroup.inclusion_injective _)
  have hXsolv : Group.IsSolvable X := by
    have hXeq : K ⊔ O = X := le_antisymm (sup_le hKX (hOD.trans hDX)) hcov
    have h := isSolvable_sup_of_isSolvable_normalizing hKsolv
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hOodd) (hKX.trans hXO)
    rwa [hXeq] at h
  have hS3 : Nat.Coprime 3 (Nat.card S) := by
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hSD : S ≤ D := by
    have : Group.IsSolvable X := hXsolv
    exact CFSG.AGLEmbedding.signalizer_le_glbPrimeCore_of_contains Nat.prime_three (by norm_num)
      (solvable_hasPrimeConstraint (G := X) 3 Nat.prime_three) hB3 hBX
      (fun y _ hyB hord => hpl.mem_of_mem_centralizer y hyB (by
        rw [← hord]
        exact pow_orderOf_eq_one y)) hSC hS3 hSB
  have hD3 : ¬ 3 ∣ Nat.card D := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hDcop
  have hBD : B ≤ normalizer (D : Set G) := hBX.trans hXD
  have hBD₀ : B ≤ normalizer ((D ⊓ K : Subgroup G) : Set G) :=
    (le_inf hBD (hBK.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hD₀3 : ¬ 3 ∣ Nat.card (D ⊓ K : Subgroup G) := fun h =>
    hD3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hbot2 : IsPGroup 2 (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  have hbotN : B ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  obtain ⟨R₀, hR₀syl, -, hBR₀⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hB3 hD₀3 hBD₀ bot_le hbot2 hbotN
  have hR₀le : R₀ ≤ D ⊓ K := hR₀syl.1
  have hR₀D : CFSG.Open.fusionIsSylowIn 2 R₀ D := by
    have h1 : CFSG.ABGLocalTools.IsSylowOf 2 R₀ (D ⊓ K) :=
      CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hR₀syl
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at h1
    obtain ⟨-, hR₀2, hdvd⟩ := h1
    have hodd := odd_relIndex_of_covering hOodd hOD hDX hKX hXO hXD hcov
    have h2 : CFSG.ABGLocalTools.IsSylowOf 2 R₀ D := by
      rw [CFSG.ABGLocalTools.isSylowOf_iff]
      refine ⟨hR₀le.trans inf_le_left, hR₀2, ?_⟩
      rw [← Subgroup.relIndex_mul_relIndex R₀ (D ⊓ K) D hR₀le inf_le_left,
        Subgroup.inf_relIndex_left]
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
      · exact hdvd h
      · exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
    exact ⟨h2.le, h2.isPGroup, fun Q hQ hQ2 hle => h2.eq_of_le hle hQ hQ2⟩
  obtain ⟨R, hRsyl, hSR, hBR⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hB3 hD3 hBD hSD hS2 hSB
  obtain ⟨c, hc, hRc⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows
    Nat.prime_three Nat.prime_two hB3 hD3 hBD hR₀D hRsyl hBR₀ hBR
  have hcM : c ∈ M := hCB hc.2
  intro s hs
  have hsR : s ∈ R := hSR hs
  rw [hRc] at hsR
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hsR
  exact M.mul_mem (M.mul_mem hcM (hR₀le hr).2.1) (M.inv_mem hcM)

end CFSG.LocalAnalysis.RankThreeTheoremC
