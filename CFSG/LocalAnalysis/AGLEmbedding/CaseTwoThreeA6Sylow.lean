module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPIdent
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPOdd
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPOmega
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Cyclic

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

section Cz

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {z : G}
  {T : Sylow 3 (Subgroup.centralizer ({z} : Set G))} {Pbar : Sylow 3 (D1CzQuot 3 z)}
  {K : Subgroup (D1CzQuot 3 z)}

theorem D1CzReduced.card_le_of_autThree (hc : D1CzReduced 3 M z T Pbar K)
    (h28 : KFactL28AutThree) (hK : IsCaseTwoGroup 3 K) :
    Nat.card (Pbar : Subgroup (D1CzQuot 3 z)) ≤
      27 * Nat.card ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓
        Subgroup.centralizer (K : Set (D1CzQuot 3 z)) : Subgroup (D1CzQuot 3 z)) := by
  have hKn := hc.normal
  set φ : (Pbar : Subgroup (D1CzQuot 3 z)) →* MulAut K :=
    (MulAut.conjNormal (H := K)).comp (Pbar : Subgroup (D1CzQuot 3 z)).subtype with hφ
  have hr : IsPGroup 3 φ.range :=
    Pbar.isPGroup'.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hr27 : Nat.card φ.range ≤ 27 := h28 K hK φ.range hr
  have hkereq : φ.ker = (Subgroup.centralizer (K : Set (D1CzQuot 3 z))).subgroupOf
      (Pbar : Subgroup (D1CzQuot 3 z)) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx k hk
      have h1 := congrArg (fun f : MulAut K => ((f ⟨k, hk⟩ : K) : D1CzQuot 3 z)) hx
      simp only [hφ, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc k * (x : D1CzQuot 3 z) = ((x : D1CzQuot 3 z) * k * (x : D1CzQuot 3 z)⁻¹) * x := by
            rw [h1]
        _ = x * k := by group
    · intro hx
      ext k
      simp only [hφ, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        MulAut.conjNormal_apply, MulAut.one_apply]
      rw [← hx k k.2, mul_inv_cancel_right]
  have hkcard : Nat.card φ.ker = Nat.card ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓
      Subgroup.centralizer (K : Set (D1CzQuot 3 z)) : Subgroup (D1CzQuot 3 z)) := by
    rw [hkereq, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hkcard] at h
  rw [← h, mul_comm]
  exact Nat.mul_le_mul_right _ hr27

theorem D1CzReduced.rstruct (hc : D1CzReduced 3 M z T Pbar K) (hL2 : KFactCaseTwoLocal)
    (hSyl : KFactCaseTwoSylow) (h28 : KFactL28AutThree) (hzK : d1CzElt 3 z ∉ K)
    (hcyc : IsCyclic ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ K : Subgroup (D1CzQuot 3 z)))
    (hK : IsCaseTwoGroup 3 K) {w : D1CzQuot 3 z}
    (hwA : w ∈ (Pbar : Subgroup (D1CzQuot 3 z)) ⊓ K) (hwo : orderOf w = 3) :
    (∃ y ∈ (Pbar : Subgroup (D1CzQuot 3 z)), y ^ 3 = d1CzElt 3 z) ∨
      (Nat.card (Pbar : Subgroup (D1CzQuot 3 z)) = 3 ^ 4 ∧
        ∃ a ∈ (Pbar : Subgroup (D1CzQuot 3 z)), a ^ 3 ∈ Subgroup.zpowers w ∧ a ^ 3 ≠ 1 ∧
          ∀ r ∈ (Pbar : Subgroup (D1CzQuot 3 z)), r ^ 3 = 1 →
            r ∉ Subgroup.zpowers w ⊔ Subgroup.zpowers (d1CzElt 3 z) → a * r ≠ r * a) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKn := hc.normal
  obtain ⟨hZ, -⟩ := hc.red.center_eq_bot_and_rankOne_of_not_mem hc.center hc.order hc.comp hzK
  have hYcyc := hc.red.isCyclic_inf_centralizer_of_not_mem_of_center hc.center hc.order hc.comp
    hKn hzK hZ
  obtain ⟨t, htA, -, -, hΩ⟩ := hc.exists_omega hL2 hzK hcyc hK
  obtain ⟨TK, hTK⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Pbar hKn.isSubnormal
  have hA9 : 9 ≤ Nat.card ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ K : Subgroup (D1CzQuot 3 z)) := by
    have h1 := hSyl 3 K hK TK
    rw [← hTK, Subgroup.card_map_of_injective K.subtype_injective]
    simpa using h1
  have hzY : d1CzElt 3 z ∈ (Pbar : Subgroup (D1CzQuot 3 z)) ⊓
      Subgroup.centralizer (K : Set (D1CzQuot 3 z)) :=
    ⟨mem_sylow_of_mem_center hc.center hc.order Pbar,
      Subgroup.center_le_centralizer _ hc.center⟩
  have hAD : ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ K) ⊓
      ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ Subgroup.centralizer (K : Set (D1CzQuot 3 z))) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxZ : (⟨x, hx.1.2⟩ : K) ∈ Subgroup.center K :=
      Subgroup.mem_center_iff.mpr fun k =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2.2 k k.2)
    rw [hZ, Subgroup.mem_bot] at hxZ
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hxZ)
  have hcomm : ∀ a ∈ (Pbar : Subgroup (D1CzQuot 3 z)) ⊓ K,
      ∀ d ∈ (Pbar : Subgroup (D1CzQuot 3 z)) ⊓ Subgroup.centralizer (K : Set (D1CzQuot 3 z)),
        Commute a d := fun a ha d hd =>
    Subgroup.mem_centralizer_iff.mp hd.2 a ha.2
  have hrk : ∃ E ≤ (Pbar : Subgroup (D1CzQuot 3 z)), IsElemAbelian 3 E ∧ 27 ≤ Nat.card E := by
    obtain ⟨E, hEP, hEe, hEc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3)
      (Pbar : Subgroup (D1CzQuot 3 z))
    refine ⟨E, hEP, hEe, ?_⟩
    rw [hEc]
    exact (Nat.pow_le_pow_right (by norm_num) hc.red.three_le_pRank : 3 ^ 3 ≤ _)
  have hΩ' : ∀ g ∈ (Pbar : Subgroup (D1CzQuot 3 z)),
      (∀ h ∈ (Pbar : Subgroup (D1CzQuot 3 z)), Commute g h) → g ^ 3 = 1 →
        g ∈ ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ K) ⊔
          ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ Subgroup.centralizer (K : Set (D1CzQuot 3 z))) :=
    fun g hg hgc hg3 => (sup_le_sup (Subgroup.zpowers_le.mpr htA)
      (Subgroup.zpowers_le.mpr hzY)) (hΩ g hg hgc hg3)
  exact rstruct_of_cyclic Pbar.isPGroup' inf_le_left inf_le_left hAD hcomm hcyc hYcyc hA9 hzY
    hc.order hwA hwo (fun g _ => Subgroup.mem_center_iff.mp hc.center g |>.symm)
    (D1CzReduced.card_le_of_autThree hc h28 hK) hrk hΩ'

end Cz

variable {G : Type} [Group G] [Finite G]

theorem D1CaseTwoDataAt.rstruct (hAut : KFactCycAut) (hSc : KFactSeitzCyc)
    (hL2 : KFactCaseTwoLocal) (hInv : KFactCaseTwoInvIn G) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (h28 : KFactL28AutThree) {P : Sylow 3 G} {M H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)} (hd : D1CaseTwoDataAt 3 P M H R Rbar)
    {z : H} (hz : D1CaseTwoCand 3 M H R z) (hnSP : ¬ D1CzSP 3 (z : G))
    (hout : D1CzOutside 3 (z : G)) (hB0 : D1CzB0 3 R (z : G))
    {w : G} (hwR : w ∈ R) (hwC : w ∈ Subgroup.centralizer ({(z : G)} : Set G))
    (hwK : ∀ KC : Subgroup (D1CzQuot 3 (z : G)), IsComponentOf KC ⊤ →
      QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({(z : G)} : Set G)) 3)
        ⟨w, hwC⟩ ∈ KC) (hwo : orderOf w = 3) :
    (∃ y ∈ R, y ^ 3 = (z : G)) ∨ (Nat.card R = 3 ^ 4 ∧ ∃ a ∈ R, a ^ 3 ∈ Subgroup.zpowers w ∧
      a ^ 3 ≠ 1 ∧ ∀ r ∈ R, r ^ 3 = 1 → r ∉ Subgroup.zpowers w ⊔ Subgroup.zpowers (z : G) →
        a * r ≠ r * a) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set C := Subgroup.centralizer ({(z : G)} : Set G) with hCdef
  have hcand := hz
  obtain ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩ := hz
  obtain ⟨S₀, hT⟩ := hB0
  obtain ⟨A₀, φ, hφ⟩ := D1CaseTwoDataAt.exists_surjective_czQuot hd hL hzp hzL
  have hiso : IsCaseTwoGroup 3 L :=
    hd.cfg.red.isCaseTwoGroup_of_not_le_of_aut hd.cfg.catalog (hAut _ _ _ _ hd.cfg.red
        hd.cfg.catalog) hSc hd.cyclic hd.rank hL hLX
  have hLp : Group.IsPerfect L := ⟨hL.2.2.1⟩
  have hP1 : (P : Subgroup G).map (MulAut.conj (1 : G)).toMonoidHom = P := by
    ext x
    simp
  obtain ⟨Pbar, K, hc⟩ := D1CaseTwoDataAt.exists_czReduced hd hAut hSc hSyl hcand M.one_mem hT.ge
    (by rw [hT, hP1]; exact hd.cfg.ext.le_P)
  have hzK : d1CzElt 3 (z : G) ∉ K := hout K hc.comp
  obtain ⟨hcyc, hK⟩ := hc.isCyclic_and_isCaseTwoGroup_at hAut hSc hSch hInv hnSP hzK hiso hLp φ hφ
  set π := QuotientGroup.mk' (primeComplementCore (G := C) 3) with hπ
  have hO := primeComplementCore_coprime (G := C) 3
  have hinj : ∀ x ∈ (S₀ : Subgroup C), ∀ y ∈ (S₀ : Subgroup C), π x = π y → x = y :=
    fun x hx y hy hxy => eq_of_mk_eq_of_isPGroup hp _ hO S₀.isPGroup' hx hy hxy
  have hmemP : ∀ x ∈ (S₀ : Subgroup C), π x ∈ (Pbar : Subgroup (D1CzQuot 3 (z : G))) :=
    fun x hx => by
      rw [hc.sylow_eq]
      exact ⟨x, hx, rfl⟩
  have hmemR : ∀ x : C, (x : G) ∈ R → x ∈ (S₀ : Subgroup C) := by
    intro x hx
    rw [← hT] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [show x = y from Subtype.ext hyx.symm]
    exact hy
  set w₀ : C := ⟨w, hwC⟩ with hw₀
  set z₀ : C := ⟨(z : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with hz₀
  have hw₀S : w₀ ∈ (S₀ : Subgroup C) := hmemR w₀ hwR
  have hz₀S : z₀ ∈ (S₀ : Subgroup C) := hmemR z₀ hzR
  have hπz : π z₀ = d1CzElt 3 (z : G) := rfl
  have hwA : π w₀ ∈ (Pbar : Subgroup (D1CzQuot 3 (z : G))) ⊓ K :=
    ⟨hmemP _ hw₀S, hwK K hc.comp⟩
  have hwo' : orderOf (π w₀) = 3 :=
    orderOf_mk_of_coprime hp _ hO (by rw [← Subgroup.orderOf_coe]; exact hwo)
  have hRS : ∀ x ∈ (S₀ : Subgroup C), (x : G) ∈ R := fun x hx => hT ▸ ⟨x, hx, rfl⟩
  rcases D1CzReduced.rstruct hc hL2 hSyl h28 hzK hcyc hK hwA hwo' with
    ⟨y, hyP, hy3⟩ | ⟨hcard, a, haP, ha3w, ha31, har⟩
  ·
    left
    rw [hc.sylow_eq] at hyP
    obtain ⟨y₀, hy₀S, rfl⟩ := hyP
    have h1 : y₀ ^ 3 = z₀ := hinj _ (Subgroup.pow_mem _ hy₀S 3) _ hz₀S (by rw [map_pow, hy3, hπz])
    exact ⟨y₀, hRS y₀ hy₀S, by simpa using congrArg Subtype.val h1⟩
  · right
    have hcardR : Nat.card R = Nat.card (Pbar : Subgroup (D1CzQuot 3 (z : G))) := by
      rw [hc.sylow_eq, card_map_mk_of_isPGroup hp _ hO S₀.isPGroup', ← hT,
        Subgroup.card_map_of_injective C.subtype_injective]
    refine ⟨hcardR.trans hcard, ?_⟩
    rw [hc.sylow_eq] at haP
    obtain ⟨a₀, ha₀S, rfl⟩ := haP
    refine ⟨a₀, hRS a₀ ha₀S, ?_, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha3w
      have h1 : a₀ ^ 3 = w₀ ^ k := hinj _ (Subgroup.pow_mem _ ha₀S 3) _
        (Subgroup.zpow_mem _ hw₀S k) (by rw [map_pow, map_zpow, hk])
      have h2 : (a₀ : G) ^ 3 = w ^ k := by
        have := congrArg Subtype.val h1
        simpa [hw₀] using this
      rw [h2]
      exact Subgroup.zpow_mem_zpowers w k
    · intro h1
      apply ha31
      have h2 : a₀ ^ 3 = 1 := Subtype.ext (by simpa using h1)
      rw [← map_pow, h2, map_one]
    · intro r hr hr3 hrn har'
      set r₀ : C := ⟨r, hRz hr⟩ with hr₀
      have hr₀S : r₀ ∈ (S₀ : Subgroup C) := hmemR r₀ hr
      have hr₀3 : r₀ ^ 3 = 1 := Subtype.ext (by simpa using hr3)
      refine har (π r₀) (hmemP _ hr₀S) (by rw [← map_pow, hr₀3, map_one]) ?_ ?_
      · intro hmem
        have hcz : Commute (π w₀) (d1CzElt 3 (z : G)) :=
          Subgroup.mem_center_iff.mp hc.center (π w₀)
        obtain ⟨u, hu, v, hv, huv⟩ := (mem_zpowers_sup_zpowers_iff hcz).mp hmem
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
        have h1 : r₀ = w₀ ^ i * z₀ ^ j := by
          refine hinj _ hr₀S _ (Subgroup.mul_mem _ (Subgroup.zpow_mem _ hw₀S i)
            (Subgroup.zpow_mem _ hz₀S j)) ?_
          rw [map_mul, map_zpow, map_zpow, hπz, huv]
        have h2 : r = w ^ i * (z : G) ^ j := by
          have := congrArg Subtype.val h1
          simpa [hw₀, hz₀, hr₀] using this
        apply hrn
        rw [h2]
        exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers _ i)
          (Subgroup.zpow_mem_zpowers _ j)
      · have h1 : a₀ * r₀ = r₀ * a₀ := Subtype.ext har'
        rw [← map_mul, ← map_mul, h1]

theorem D1CaseTwoData.rstruct (hβ : KFactBeta) (hSc : KFactSeitzCyc)
    (hL2 : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (h28 : KFactL28AutThree) {P : Sylow 3 G} {M H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)} (hd : D1CaseTwoData 3 P M H R Rbar)
    {z : H} (hz : D1CaseTwoCand 3 M H R z) (hnSP : ¬ D1CzSP 3 (z : G))
    (hout : D1CzOutside 3 (z : G)) (hB0 : D1CzB0 3 R (z : G))
    {w : G} (hwR : w ∈ R) (hwC : w ∈ Subgroup.centralizer ({(z : G)} : Set G))
    (hwK : ∀ KC : Subgroup (D1CzQuot 3 (z : G)), IsComponentOf KC ⊤ →
      QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({(z : G)} : Set G)) 3)
        ⟨w, hwC⟩ ∈ KC) (hwo : orderOf w = 3) :
    (∃ y ∈ R, y ^ 3 = (z : G)) ∨ (Nat.card R = 3 ^ 4 ∧ ∃ a ∈ R, a ^ 3 ∈ Subgroup.zpowers w ∧
      a ^ 3 ≠ 1 ∧ ∀ r ∈ R, r ^ 3 = 1 → r ∉ Subgroup.zpowers w ⊔ Subgroup.zpowers (z : G) →
        a * r ≠ r * a) :=
  D1CaseTwoDataAt.rstruct (hAut := (kFactCycAut_of_kFactBeta hβ)) (hSc := hSc) (hL2 := hL2)
    (hInv := (kFactCaseTwoInvIn_of_kFactCaseTwoInv hInv)) (hSch := hSch) (hSyl := hSyl) (h28 := h28)
    (hd := hd.toAt) (hz := hz) (hnSP := hnSP) (hout := hout) (hB0 := hB0) (hwR := hwR) (hwC := hwC)
    (hwK := hwK) (hwo := hwo)

end CFSG.AGLEmbedding
