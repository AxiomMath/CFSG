module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieOpMbar
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.LocalAnalysis.AGLEmbedding.ZNCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Abstract

variable {Y : Type*} [Group Y] [Finite Y] {p : ℕ}

theorem mem_of_isCyclic_inf_of_ne_bot [Fact p.Prime]
    (hcore : primeComplementCore (G := Y) p = ⊥) {C V : Subgroup Y} [C.Normal] (S : Sylow p Y)
    (hSC : IsCyclic ((S : Subgroup Y) ⊓ C : Subgroup Y)) {z : Y} (hzS : z ∈ (S : Subgroup Y))
    (hzC : z ∈ C) (hzp : orderOf z = p) (hVC : V ≤ C)
    (hCV : C ≤ Subgroup.normalizer (V : Set Y)) (hV : V ≠ ⊥) : z ∈ V := by
  have hp : p.Prime := Fact.out
  have hdvd : p ∣ Nat.card V := by
    by_contra hnd
    have hcop : p.Coprime (Nat.card V) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd
    have hVn : (V.subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hVC).mpr hCV
    have hle : V.subgroupOf C ≤ primeComplementCore (G := C) p :=
      normal_coprime_le_primeComplementCore p _ hVn
        (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVC).toEquiv])
    have : (primeComplementCore (G := C) p).Characteristic := primeComplementCore_characteristic p
    have hle' : (primeComplementCore (G := C) p).map C.subtype ≤
        primeComplementCore (G := Y) p :=
      normal_coprime_le_primeComplementCore p _ inferInstance (by
        rw [Subgroup.card_map_of_injective C.subtype_injective]
        exact primeComplementCore_coprime p)
    apply hV
    rw [← le_bot_iff, ← hcore, ← Subgroup.map_subgroupOf_eq_of_le hVC]
    exact (Subgroup.map_mono hle).trans hle'
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨P₀, hP₀⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S
    (inferInstance : C.Normal).isSubnormal
  set v' : C := ⟨v, hVC v.2⟩ with hv'
  have hv'p : orderOf v' = p := by rw [hv', Subgroup.orderOf_mk, Subgroup.orderOf_coe, hv]
  have hvp : IsPGroup p (Subgroup.zpowers v') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv'p, pow_one])
  obtain ⟨P₁, hP₁⟩ := hvp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C P₁ P₀
  have hcv : c * v' * c⁻¹ ∈ (P₀ : Subgroup C) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    have := Subgroup.smul_mem_pointwise_smul v' (MulAut.conj c) (P₁ : Subgroup C)
      (hP₁ (Subgroup.mem_zpowers v'))
    simpa only [MulAut.smul_def, MulAut.conj_apply] using this
  set w : Y := ((c * v' * c⁻¹ : C) : Y) with hw
  have hwS : w ∈ (S : Subgroup Y) ⊓ C := hP₀ ▸ Subgroup.mem_map_of_mem C.subtype hcv
  have hwV : w ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (hCV c.2) (v : Y)).mp v.2
    simpa only [hw, hv', Subgroup.coe_mul, Subgroup.coe_inv] using this
  have hwp : orderOf w = p := by
    have hsc : SemiconjBy (c : Y) (v : Y) w := by
      simp only [SemiconjBy, hw, hv', Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [← hsc.orderOf_eq, Subgroup.orderOf_coe, hv]
  have := hSC
  have hzSC : z ∈ (S : Subgroup Y) ⊓ C := ⟨hzS, hzC⟩
  have heq : Subgroup.zpowers (⟨z, hzSC⟩ : ((S : Subgroup Y) ⊓ C : Subgroup Y)) =
      Subgroup.zpowers ⟨w, hwS⟩ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hzp, hwp]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (heq ▸ Subgroup.mem_zpowers _ :
    (⟨z, hzSC⟩ : ((S : Subgroup Y) ⊓ C : Subgroup Y)) ∈ Subgroup.zpowers ⟨w, hwS⟩)
  have hk' : w ^ k = z := congrArg Subtype.val hk
  rw [← hk']
  exact V.zpow_mem hwV k

end Abstract

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneLieData.centralizer_d1MapPCore_le (hK : KFactOneLie) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1OneLieData p P M H R Rbar K)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥)
    (hU3 : ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K))) :
    Subgroup.centralizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) ≤
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ⊔
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
  obtain ⟨T₁, hT₁, hF⟩ := hd.oneLieFacts hK
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨-, -, hWn, -, hWiff⟩ := hd.d1MapPCore_facts hK h84 hD2
  have hV := hWiff.mp hY
  have hNV : K ⊓ Subgroup.normalizer (((T₁ : Subgroup K).map K.subtype : Subgroup _) :
      Set (H ⧸ primeComplementCore (G := H) p)) ≤ Subgroup.normalizer ((d1MapPCore p M H ⊓
        ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) : Subgroup _) :
          Set (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hT₁]
    exact (le_inf hWn inf_le_right).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hcent : Subgroup.centralizer ((d1MapPCore p M H ⊓
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) : Subgroup _) :
        Set (H ⧸ primeComplementCore (G := H) p)) ≤
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ⊔
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
    rcases centralizer_le_sup_of_oneLieFacts hd.center T₁ hF (hT₁ ▸ inf_le_right) hV hNV with
      h | h
    · rwa [hT₁] at h
    · exact absurd ⟨h.2, by rw [h.1, hT₁]⟩ hU3
  exact (Subgroup.centralizer_le inf_le_left).trans hcent

theorem D1CompCore.not_mem_pCorePreimage (hd : D1CompCore p P M H R Rbar K)
    (hWK : d1MapPCore p M H ≤ K) {z : G} (hzR : z ∈ R) (hzN : z ∈ d1PlusCore p H K)
    (hzp : orderOf z = p) : z ∉ pCorePreimage p M := by
  intro hzY
  have hp := hd.red.prime
  have hzH : z ∈ H := hd.esc.le_H hzR
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  have hzK : π ⟨z, hzH⟩ ∈ K := hWK ⟨⟨z, hzH⟩, Subgroup.mem_subgroupOf.mpr hzY, rfl⟩
  have hzC : π ⟨z, hzH⟩ ∈
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
    obtain ⟨z', hz', hzz'⟩ := hzN
    rwa [show z' = ⟨z, hzH⟩ from Subtype.ext hzz'] at hz'
  have hcen : (⟨π ⟨z, hzH⟩, hzK⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC k k.2)
  rw [hd.center, Subgroup.mem_bot] at hcen
  have h1 : π ⟨z, hzH⟩ = 1 := congrArg Subtype.val hcen
  have hzN' : z ∈ GLBPrimeCore p H := (mk'_primeComplementCore_eq_one_iff p _).mp h1
  have hdvd : p ∣ Nat.card (GLBPrimeCore p H) := by
    have := Subgroup.orderOf_dvd_natCard (GLBPrimeCore p H) hzN'
    rwa [hzp] at this
  exact (Nat.Prime.coprime_iff_not_dvd hp).mp (glbPrimeCore_coprime p H) hdvd

theorem D1CompCore.inf_le_sup_of_not_mem (h3 : D1PhaseThree p P M H R)
    (hd : D1CompCore p P M H R Rbar K)
    (hCW : Subgroup.centralizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) ≤
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ⊔
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)))
    {E : Subgroup G} (hED : E ≤ pCoreCentralizerPreimage p M)
    (hME : M ≤ Subgroup.normalizer (E : Set G)) {z : G} (hzR : z ∈ R)
    (hzN : z ∈ d1PlusCore p H K) (hzp : orderOf z = p) (hzE : z ∉ E) :
    E ⊓ H ≤ R ⊔ GLBPrimeCore p H := by
  have hp := hd.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hKn : K.Normal := hd.red.normal_of_rankOne hd.comp hd.noncyclic
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set C := Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) with hC
  set W := ((E ⊓ H).subgroupOf H).map π with hW
  set X₀ := ((H ⊓ M).subgroupOf H).map π with hX₀
  obtain ⟨zb, hzbR, hzbK, hzbp, hzbc⟩ := hd.z
  have hCX₀ : C ≤ X₀ := hd.red.centralizer_le_of_rankOne hd.noncyclic hzbR hzbK hzbp hzbc
  obtain ⟨-, hKX₀⟩ := hd.red.rankOne_principle hd.comp hd.noncyclic hzbR hzbK hzbp hzbc
  have hX₀W : X₀ ≤ Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p)) :=
    map_le_normalizer_map π inf_le_right ((le_inf (inf_le_right.trans hME)
      (inf_le_left.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf)
  have hWTC : W ≤ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ⊔ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact hCW (mk_mem_centralizer_d1MapPCore h3.twoCore_M_le_glbPrimeCore (hED hx.1) x.2)
  have hzH : z ∈ H := hd.esc.le_H hzR
  have hzbR' : π ⟨z, hzH⟩ ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hd.rbar]
    exact Subgroup.mem_map_of_mem π hzR
  have hzbC' : π ⟨z, hzH⟩ ∈ C := by
    obtain ⟨z', hz', hz'z⟩ := hzN
    have hz'z' : z' = ⟨z, hzH⟩ := Subtype.ext hz'z
    rw [← hz'z']
    exact hz'
  have hzbp' : orderOf (π ⟨z, hzH⟩) = p := by
    have hdvd : orderOf (π ⟨z, hzH⟩) ∣ p :=
      calc orderOf (π ⟨z, hzH⟩) ∣ orderOf (⟨z, hzH⟩ : H) := orderOf_map_dvd π _
        _ = p := by rw [Subgroup.orderOf_mk, hzp]
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exfalso
      have hzN' : z ∈ GLBPrimeCore p H :=
        (mk'_primeComplementCore_eq_one_iff p ⟨z, hzH⟩).mp (orderOf_eq_one_iff.mp h1)
      have hpN := Subgroup.orderOf_dvd_natCard _ hzN'
      rw [hzp] at hpN
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp (glbPrimeCore_coprime p H) hpN
    · exact h1
  have hV : W ⊓ C = ⊥ := by
    by_contra hV
    have hCV : C ≤ Subgroup.normalizer ((W ⊓ C : Subgroup _) :
        Set (H ⧸ primeComplementCore (G := H) p)) :=
      (le_inf (hCX₀.trans hX₀W) Subgroup.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hcyc : IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ C :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) :=
      hd.red.isCyclic_of_le_centralizer hd.comp hKX₀ (Rbar.isPGroup'.to_le inf_le_left)
        inf_le_right
    obtain ⟨e, he, hez⟩ := (mem_of_isCyclic_inf_of_ne_bot hd.red.core_eq_bot Rbar hcyc hzbR'
      hzbC' hzbp' inf_le_right hCV hV).1
    have hn : (e : G)⁻¹ * z ∈ GLBPrimeCore p H :=
      (mk'_primeComplementCore_eq_one_iff p (e⁻¹ * ⟨z, hzH⟩)).mp
        (by rw [map_mul, map_inv, hez, inv_mul_cancel])
    have hzpg : IsPGroup p (Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzp, pow_one])
    have hze : z * ((e : G)⁻¹ * z)⁻¹ = e := by group
    have hzeE : z * ((e : G)⁻¹ * z)⁻¹ ∈ E := by
      rw [hze]
      exact he.1
    exact hzE (mem_of_mul_mem_of_coprime hzpg (glbPrimeCore_coprime p H).symm
      (h3.primeCore_le.trans hME) ((GLBPrimeCore p H).inv_mem hn) hzeE)
  have hWp : IsPGroup p W := by
    intro w
    have hw : (w : H ⧸ primeComplementCore (G := H) p) ∈
        (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ⊔ C :
          Subgroup (H ⧸ primeComplementCore (G := H) p)) :
            Set (H ⧸ primeComplementCore (G := H) p)) := hWTC w.2
    rw [Subgroup.mul_normal] at hw
    obtain ⟨t, htRK, c, hcC, htc⟩ := hw
    obtain ⟨k, hk⟩ := Rbar.isPGroup' ⟨t, (htRK : t ∈ _ ⊓ K).1⟩
    have hk' : t ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hwC : (w : H ⧸ primeComplementCore (G := H) p) ^ p ^ k ∈ C := by
      have hc1 : QuotientGroup.mk' C c = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
        exact hcC
      have h1 : (w : H ⧸ primeComplementCore (G := H) p) ^ p ^ k ∈ (QuotientGroup.mk' C).ker := by
        rw [MonoidHom.mem_ker, map_pow, ← htc, map_mul, hc1, mul_one, ← map_pow, hk', map_one]
      rwa [QuotientGroup.ker_mk'] at h1
    have hwWC : (w : H ⧸ primeComplementCore (G := H) p) ^ p ^ k ∈ W ⊓ C :=
      ⟨W.pow_mem w.2 _, hwC⟩
    rw [hV, Subgroup.mem_bot] at hwWC
    exact ⟨k, Subtype.ext hwWC⟩
  have hRX₀ : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤ X₀ := by
    rw [hd.rbar]
    exact Subgroup.map_mono (Subgroup.comap_mono h3.le_inf)
  have hWR : W ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    have h2 : IsPGroup p (W ⊔ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) :=
      IsPGroup.to_sup_of_normal_left' hWp Rbar.isPGroup' (hRX₀.trans hX₀W)
    exact le_sup_left.trans (Rbar.is_maximal' h2 le_sup_right).le
  rintro x ⟨hxE, hxH⟩
  have hxW : π ⟨x, hxH⟩ ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) :=
    hWR ⟨⟨x, hxH⟩, ⟨hxE, hxH⟩, rfl⟩
  rw [hd.rbar] at hxW
  obtain ⟨r, hr, hrx⟩ := hxW
  have hn : (r : G)⁻¹ * x ∈ GLBPrimeCore p H :=
    (mk'_primeComplementCore_eq_one_iff p (r⁻¹ * ⟨x, hxH⟩)).mp
      (by rw [map_mul, map_inv, hrx, inv_mul_cancel])
  have e : x = r * ((r : G)⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hr hn

theorem D1CompCore.false_of_not_mem_normal (h3 : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock)
    (hd : D1CompCore p P M H R Rbar K)
    (huniq : D1UniqueOver H R (nclIn H (d1LiftX p H R K)))
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥)
    (hCW : Subgroup.centralizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) ≤
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ⊔
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)))
    {C' : Subgroup G} (hMC' : M ≤ Subgroup.normalizer (C' : Set G))
    (hNJC' : ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆ ≤ C')
    {z : G} (hzR : z ∈ R) (hzN : z ∈ d1PlusCore p H K) (hzp : orderOf z = p) (hzC' : z ∉ C') :
    False := by
  have : Fact p.Prime := ⟨h3.prime⟩
  obtain ⟨hDM, hMD, hQD, -⟩ := pCoreCentralizerPreimage_facts p M
  have hQM : pCoreOf 2 M ≤ M := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M
  have hMQ : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M
  have hME : M ≤ Subgroup.normalizer (((C' ⊔ pCoreOf 2 M) ⊓ pCoreCentralizerPreimage p M :
      Subgroup G) : Set G) :=
    (le_inf ((le_inf hMC' hMQ).trans (Subgroup.inf_normalizer_le_normalizer_sup C' _))
      hMD).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hzE : z ∉ (C' ⊔ pCoreOf 2 M) ⊓ pCoreCentralizerPreimage p M := by
    intro hz
    have hzCQ : z ∈ ((C' ⊔ pCoreOf 2 M : Subgroup G) : Set G) := hz.1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left C' _ (hQM.trans hMC')] at hzCQ
    obtain ⟨c, hc, q, hq, hcq⟩ := hzCQ
    have hQcop : (Nat.card (pCoreOf 2 M)).Coprime p := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
      rw [hk]
      exact Nat.Coprime.pow_left k
        ((Nat.coprime_primes Nat.prime_two h3.prime).mpr (Ne.symm h3.ne_two))
    have hzq : z * q⁻¹ ∈ C' := by
      rw [← hcq, mul_inv_cancel_right]
      exact hc
    exact hzC' (mem_of_mul_mem_of_coprime
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzp, pow_one])) hQcop
      (hQM.trans hMC') ((pCoreOf 2 M).inv_mem hq) hzq)
  have hNJ := hd.commutator_nclIn_le h3 h84 hD2 hY
  have hSN : pCoreOf 2 H ≤ GLBPrimeCore p H := pCoreOf_le_glbPrimeCore Nat.prime_two
    ((Nat.coprime_primes h3.prime Nat.prime_two).mpr h3.ne_two) H
  exact h3.false_of_normal_of_commutator_le (inf_le_right.trans hDM) hME
    (le_inf le_sup_right hQD)
    (le_inf (hNJC'.trans le_sup_left)
      ((hNJ.trans hSN).trans (h3.glbPrimeCore_le_pCoreCentralizerPreimage h84 hD2))) hNJ
    (hd.inf_le_sup_of_not_mem h3 hCW inf_le_right hME hzR hzN hzp hzE) huniq hCGT hD2

end Config

end CFSG.AGLEmbedding
