module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexDefs
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexOrbit
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPOdd
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Bound
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Count
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Dec
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeDiag
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorBarM
import CFSG.LocalAnalysis.AGLEmbedding.ResidualToolsAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}

omit [Finite G] in
theorem eq_of_mk_eq_of_three {M X : Subgroup G} (hX : IsPGroup 3 X) (hXM : X ≤ M) {x y : G}
    (hx : x ∈ X) (hy : y ∈ X)
    (h : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hXM hx⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hXM hy⟩) : x = y := by
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ((⟨x, hXM hx⟩ : M)⁻¹ * ⟨y, hXM hy⟩) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 := eq_one_of_mem_pCoreOf_two Nat.prime_three (by norm_num) hX
    (X.mul_mem (X.inv_mem hx) hy) (coe_mem_pCoreOf_two_of_mk_eq_one _ h1)
  exact inv_mul_eq_one.mp h2

theorem exists_sylow_eq_barM {M : Subgroup G} (hPM : (P : Subgroup G) ≤ M) :
    ∃ S : Sylow 3 (↥M ⧸ CFSG.pCore 2 ↥M),
      (S : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) = barM M (P : Subgroup G) :=
  ⟨(P.subtype hPM).mapSurjective (QuotientGroup.mk'_surjective _), by
    rw [Sylow.coe_mapSurjective, Sylow.coe_subtype]
    rfl⟩

theorem D1PhaseThree.dec_of_threeASix (h : D1PhaseThree 3 P M H R)
    (hThree : KFactBlockThreeASix)
    (hcyc : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q → IsCyclic Q)
    {z : G} (hzM : z ∈ M) (hz3 : z ^ 3 = 1) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hin : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
        barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hrk : ∀ E : Subgroup G, E ≤ Subgroup.centralizer ({z} : Set G) → IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ 3)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hZ : Nat.card (Subgroup.center ↥(barM M L)) = 3)
    (hA6 : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6))) :
    barM M (P : Subgroup G) ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      ∀ y ∈ barM M (P : Subgroup G), ∃ l ∈ barM M (P : Subgroup G) ⊓ barM M L,
        l⁻¹ * y ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPM : (P : Subgroup G) ≤ M := h.toD1Escape.sylow_le
  obtain ⟨ha, -, -⟩ := hThree G M L hL.toIsTwoPrimeComponent hZ hA6
  have hPbN : barM M (P : Subgroup G) ≤
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨g, hg, rfl⟩
    have hgP : (g : G) ∈ (P : Subgroup G) := Subgroup.mem_subgroupOf.mp hg
    have hg3 : IsPGroup 3 (Subgroup.zpowers (g : G)) :=
      P.isPGroup'.to_le ((Subgroup.zpowers_le).mpr hgP)
    exact mem_normalizer_barM g.2 (D1PhaseThree.mem_normalizer_of_threeASix h hThree hcyc
      hzM hz3 hCz hin hrk hL hZ hA6 g.2 hg3)
  have hPb3 : IsPGroup 3 (barM M (P : Subgroup G)) := (P.isPGroup'.comap_subtype (K := M)).map _
  have hPbin : ∀ x ∈ barM M (P : Subgroup G),
      x ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    fun x hx => ha x (hPbN hx) (by
      obtain ⟨k, hk⟩ := hPb3 ⟨x, hx⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩)
  obtain ⟨Pbs, hPbs⟩ := exists_sylow_eq_barM (P := P) hPM
  refine ⟨hPbN, fun y hy => ?_⟩
  have := exists_dec_of_sylow hL.component.2.1 Pbs (hPbs ▸ hPbN) (hPbs ▸ hPbin) (hPbs ▸ hy)
  rwa [hPbs] at this

theorem D1PhaseThree.false_of_threeASix_out (h : D1PhaseThree 3 P M H R)
    (hThree : KFactBlockThreeASix)
    (hcyc : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q → IsCyclic Q)
    {z : G} (hzM : z ∈ M) (hzP : z ∈ (P : Subgroup G)) (hz3 : z ^ 3 = 1)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hin : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
        barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hrk : ∀ E : Subgroup G, E ≤ Subgroup.centralizer ({z} : Set G) → IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ 3)
    (hP4 : 4 ≤ Open.pRank 3 (P : Subgroup G))
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hZ : Nat.card (Subgroup.center ↥(barM M L)) = 3)
    (hA6 : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)))
    (hzL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∉ barM M L)
    {R' : Subgroup G} (hR'P : R' ≤ P) (hR'z : R' ≤ Subgroup.centralizer ({z} : Set G))
    (hCPR : ∀ g ∈ (P : Subgroup G), g * z = z * g → g ∈ R')
    {w : G} (hwR : w ∈ R') (hwo : orderOf w = 3)
    (hΩP : ∀ g ∈ (P : Subgroup G), (∀ h ∈ (P : Subgroup G), Commute g h) → g ^ 3 = 1 →
      g ∈ Subgroup.zpowers w)
    (hstr : (∃ y ∈ R', y ^ 3 = z) ∨ (Nat.card R' = 3 ^ 4 ∧ ∃ a ∈ R',
      a ^ 3 ∈ Subgroup.zpowers w ∧ a ^ 3 ≠ 1 ∧ ∀ r ∈ R', r ^ 3 = 1 →
        r ∉ Subgroup.zpowers w ⊔ Subgroup.zpowers z → a * r ≠ r * a)) : False := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hPM : (P : Subgroup G) ≤ M := h.toD1Escape.sylow_le
  set zb := mk ⟨z, hzM⟩ with hzb
  have hz : IsPGroup 3 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hz3)
  have hzb3 : zb ^ 3 = 1 := by
    have h1 : (⟨z, hzM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [hzb, ← map_pow, h1, map_one]
  have hnC : zb ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    h.not_mem_centralizer_block hp hp2 hzM hz hCz hL
  obtain ⟨-, hb, hc⟩ := hThree G M L hL.toIsTwoPrimeComponent hZ hA6
  obtain ⟨hPbN, hdec⟩ := D1PhaseThree.dec_of_threeASix h hThree hcyc hzM hz3 hCz hin hrk hL hZ
    hA6
  set Pb := barM M (P : Subgroup G) with hPb
  have hmemPb : ∀ g (hg : g ∈ (P : Subgroup G)), mk ⟨g, hPM hg⟩ ∈ Pb := fun g hg =>
    ⟨⟨g, hPM hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hPbmem : ∀ x ∈ Pb, ∃ g, ∃ hg : g ∈ (P : Subgroup G), mk ⟨g, hPM hg⟩ = x := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, Subgroup.mem_subgroupOf.mp hm, rfl⟩
  have hinj : ∀ x y (hx : x ∈ (P : Subgroup G)) (hy : y ∈ (P : Subgroup G)),
      mk ⟨x, hPM hx⟩ = mk ⟨y, hPM hy⟩ → x = y := fun x y hx hy hxy =>
    eq_of_mk_eq_of_three P.isPGroup' hPM hx hy hxy
  have hmkmul : ∀ x y (hx : x ∈ M) (hy : y ∈ M),
      mk ⟨x * y, M.mul_mem hx hy⟩ = mk ⟨x, hx⟩ * mk ⟨y, hy⟩ := fun x y hx hy => by
    rw [← map_mul]; rfl
  have hmkpow : ∀ x (hx : x ∈ (P : Subgroup G)), mk ⟨x, hPM hx⟩ ^ 3 = 1 → x ^ 3 = 1 := by
    intro x hx hx3
    apply hinj _ _ (P.pow_mem hx 3) P.one_mem
    rw [show (⟨x ^ 3, hPM (P.pow_mem hx 3)⟩ : M) = ⟨x, hPM hx⟩ ^ 3 from rfl, map_pow, hx3]
    exact (map_one mk).symm
  have hPb3 : IsPGroup 3 Pb := (P.isPGroup'.comap_subtype (K := M)).map _
  have hzbPb : zb ∈ Pb := hmemPb z hzP
  rcases hstr with ⟨y, hyR, hy3⟩ | ⟨hcard, a, haR, ha3w, ha31, har⟩
  ·
    have hyP := hR'P hyR
    apply hnC
    have hy3' : mk ⟨y, hPM hyP⟩ ^ 3 = zb := by
      rw [hzb, ← map_pow]
      congr 1
      exact Subtype.ext (by simpa using hy3)
    rw [← hy3']
    exact pow_three_mem_centralizer_of_dec hPb3 hdec hb (hmemPb y hyP)
  have hwP : w ∈ (P : Subgroup G) := hR'P hwR
  set wb := mk ⟨w, hPM hwP⟩ with hwb
  have hwo' : orderOf wb = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · have h1 : (⟨w, hPM hwP⟩ : M) ^ 3 = 1 := Subtype.ext (by
        simp [← hwo, pow_orderOf_eq_one])
      rw [hwb, ← map_pow, h1, map_one]
    · intro h1
      have := hinj w 1 hwP P.one_mem (by rw [← hwb, h1]; exact (map_one mk).symm)
      rw [this, orderOf_one] at hwo
      norm_num at hwo
  have hΩ : ∀ x ∈ Pb, (∀ y ∈ Pb, Commute x y) → x ^ 3 = 1 → x ∈ Subgroup.zpowers wb := by
    intro x hx hxc hx3
    obtain ⟨g, hg, rfl⟩ := hPbmem x hx
    have hgc : ∀ h' ∈ (P : Subgroup G), Commute g h' := by
      intro h' hh'
      apply hinj _ _ (P.mul_mem hg hh') (P.mul_mem hh' hg)
      rw [hmkmul _ _ (hPM hg) (hPM hh'), hmkmul _ _ (hPM hh') (hPM hg)]
      exact (hxc _ (hmemPb h' hh')).eq
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hΩP g hg hgc (hmkpow g hg hx3))
    have : (⟨g, hPM hg⟩ : M) = ⟨w, hPM hwP⟩ ^ k := Subtype.ext (by simp [hk])
    rw [this, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ k
  obtain ⟨Pbs, hPbs⟩ := exists_sylow_eq_barM (P := P) hPM
  obtain ⟨hZw, hwbA, hwbC, -, hwbZ⟩ :=
    center_eq_zpowers_of_sylow hZ Pbs (hPbs ▸ hPbN) hwo' (hPbs ▸ hΩ)
  rw [hPbs] at hwbZ
  set Rb := barM M R' with hRb
  have hRbPb : Rb ≤ Pb := barM_mono hR'P
  have hRbc : Nat.card Rb = 3 ^ 4 := by
    rw [card_barM_of_isPGroup hp hp2 (hR'P.trans hPM) (P.isPGroup'.to_le hR'P), hcard]
  have hRbmem : ∀ g (hg : g ∈ R'), mk ⟨g, hPM (hR'P hg)⟩ ∈ Rb := fun g hg =>
    ⟨⟨g, hPM (hR'P hg)⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hRz : ∀ x ∈ Rb, x * zb = zb * x := by
    rintro _ ⟨m, hm, rfl⟩
    rw [hzb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
      (hR'z (Subgroup.mem_subgroupOf.mp hm)))
  have hCR : ∀ x ∈ Pb, x * zb = zb * x → x ∈ Rb := by
    intro x hx hxz
    obtain ⟨g, hg, rfl⟩ := hPbmem x hx
    have hgz : g * z = z * g := hinj _ _ (P.mul_mem hg hzP) (P.mul_mem hzP hg) (by
      rw [hmkmul _ _ (hPM hg) hzM, hmkmul _ _ hzM (hPM hg)]
      exact hxz)
    exact hRbmem g (hCPR g hg hgz)
  have haP := hR'P haR
  set ab := mk ⟨a, hPM haP⟩ with hab
  have hab3w : ab ^ 3 ∈ Subgroup.zpowers wb := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha3w
    have : (⟨a, hPM haP⟩ : M) ^ 3 = ⟨w, hPM hwP⟩ ^ k := Subtype.ext (by simp [hk])
    rw [hab, ← map_pow, this, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ k
  have hab31 : ab ^ 3 ≠ 1 := fun h1 => ha31 (hmkpow a haP h1)
  have habr : ∀ r ∈ Rb, r ^ 3 = 1 → r ∉ Subgroup.zpowers wb ⊔ Subgroup.zpowers zb →
      ab * r ≠ r * ab := by
    rintro _ ⟨m, hm, rfl⟩ hr3 hrn hcomm
    have hgR : (m : G) ∈ R' := Subgroup.mem_subgroupOf.mp hm
    have hgP := hR'P hgR
    refine har m hgR (hmkpow m hgP hr3) (fun hmem => hrn ?_) ?_
    · have hwz : Commute w z := Subgroup.mem_centralizer_singleton_iff.mp (hR'z hwR)
      obtain ⟨u, hu, v, hv, huv⟩ := (mem_zpowers_sup_zpowers_iff hwz).mp hmem
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      have : m = ⟨w, hPM hwP⟩ ^ i * ⟨z, hzM⟩ ^ j := Subtype.ext (by simp [← huv])
      rw [this, map_mul, map_zpow, map_zpow]
      exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers _ i)
        (Subgroup.zpow_mem_zpowers _ j)
    · apply hinj _ _ (P.mul_mem haP hgP) (P.mul_mem hgP haP)
      rw [hmkmul _ _ (hPM haP) (hPM hgP), hmkmul _ _ (hPM hgP) (hPM haP)]
      exact hcomm
  obtain ⟨hD27, hDnab⟩ := card_inf_centralizer_le_of_dec hPb3 hPbN hdec hb hZw hwbA hwbC
    (hmemPb w hwP) hwbZ hwo' hzbPb hzb3 hzL hnC hRbPb hRbc hRz hCR (hRbmem a haR) hab3w hab31
    habr
  obtain ⟨E, hEP, hEe, hEc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3)
    (P : Subgroup G)
  have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hEe.2 x x.2)⟩
  have h81 : 3 ^ 4 ≤ Nat.card (barM M E) := by
    rw [card_barM_of_isPGroup hp hp2 (hEP.trans hPM) hE3, hEc]
    exact Nat.pow_le_pow_right (by norm_num) hP4
  exact false_of_elemAbelian_of_dec hPb3 hPbN hdec hb hc hZw hwbA hwbC hwo' hD27 hDnab
    (barM_mono hEP) (isElemAbelian_barM hEe) h81

end CFSG.AGLEmbedding
