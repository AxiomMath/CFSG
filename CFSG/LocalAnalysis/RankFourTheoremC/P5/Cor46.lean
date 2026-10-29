module

public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Shape
public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Sylow
public import CFSG.LocalAnalysis.RankFourTheoremC.P5.I205
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9End2
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankFourTheoremC CFSG.Yardstones.Md8ed6d263d89 Subgroup
open scoped MatrixGroups

theorem commute_of_normalizes_unipotent {X : Type} [Group X] [Finite X] {p n : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hn : 1 ≤ n) {K : Subgroup X} [K.Normal]
    (e : Nonempty (K ≃* PSL(2, GaloisField p n))) {k : X} (hkK : k ∈ K) (hkp : orderOf k = p)
    {W : Subgroup X} (hW : ¬ p ∣ Nat.card W) (hkW : k ∈ normalizer (W : Set X)) :
    ∀ w ∈ W, w * k = k * w := by
  have hkN : k ∈ normalizer (K : Set X) := Subgroup.le_normalizer hkK
  have hV : W ⊓ K = ⊥ := by
    refine kFactL2UnipotentCoprimeN p hp5 n hn K e k hkK hkp (W ⊓ K) inf_le_right ?_ ?_
    · intro hdvd
      exact hW (hdvd.trans (Subgroup.card_dvd_of_le inf_le_left))
    · exact mem_normalizer_inf' hkW hkN
  intro w hw
  have h1 : w * k * w⁻¹ * k⁻¹ ∈ W := by
    have h := (Subgroup.mem_normalizer_iff.mp hkW w⁻¹).mp (W.inv_mem hw)
    have e1 : w * k * w⁻¹ * k⁻¹ = w * (k * w⁻¹ * k⁻¹) := by group
    rw [e1]
    exact W.mul_mem hw (by simpa [mul_assoc] using h)
  have h2 : w * k * w⁻¹ * k⁻¹ ∈ K := by
    have hwk : w * k * w⁻¹ ∈ K := by
      have := ‹K.Normal›.conj_mem k hkK w
      simpa [mul_assoc] using this
    exact K.mul_mem hwk (K.inv_mem hkK)
  have h3 : w * k * w⁻¹ * k⁻¹ ∈ W ⊓ K := ⟨h1, h2⟩
  rw [hV, Subgroup.mem_bot] at h3
  have h4 : w * k = k * w := by
    have : w * k * w⁻¹ = k := by
      calc w * k * w⁻¹ = (w * k * w⁻¹ * k⁻¹) * k := by group
        _ = k := by rw [h3, one_mul]
    calc w * k = (w * k * w⁻¹) * w := by group
      _ = k * w := by rw [this]
  exact h4


variable {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G}
  {M : Subgroup G}

theorem le_of_coprime_normalized_p (hp5 : 5 ≤ p) (hK : P5KFacts) (hG : P5Global G)
    (hloc : D1Local p P M) (hType : PTypeHyp p P M) (hab : IsMulCommutative (P : Subgroup G))
    {A : Subgroup G} (hAP : A ≤ (P : Subgroup G)) (hAe : IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) {F : Subgroup G} (hFc : p.Coprime (Nat.card F))
    (hFA : A ≤ normalizer (F : Set G)) : F ≤ M := by
  have hp2 : p ≠ 2 := by omega
  have hFp : ¬ p ∣ Nat.card F := (Nat.Prime.coprime_iff_not_dvd hp.out).mp hFc
  have hPM : (P : Subgroup G) ≤ M := sylow_le_of_core hloc
  have hAM : A ≤ M := hAP.trans hPM
  have hAp : IsPGroup p A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  have hA2 : 2 ≤ Open.pRank p A :=
    CFSG.SectionRank.le_pRank hp.out.one_lt (le_refl A) hAe hAc
  have hNA : normalizer (A : Set G) ≤ M := normalizer_le_of_two_le_pRank hG.fc hloc hAp hAM hA2
  have hgen := RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane p hp.out
    A F (fun u => Subtype.ext (hAe.2 u u.2)) hAc hFp hFA
  have hmain : (⨆ (u : A) (_ : u ≠ 1), F ⊓ centralizer ({(u : G)} : Set G)) ≤ M := by
    refine iSup_le fun u => iSup_le fun hu1 => ?_
    set a : G := (u : G) with ha
    have ha1 : a ≠ 1 := fun h => hu1 (Subtype.ext h)
    have haA : a ∈ A := u.2
    have hap : a ^ p = 1 := hAe.2 a haA
    have hao : orderOf a = p := orderOf_eq_prime hap ha1
    by_cases hC : centralizer ({a} : Set G) ≤ M
    · exact inf_le_right.trans hC
    have hpt : IsPPoint p P M a := isPPoint_of_mem_abelian hloc hab (hAP haA) hao hC
    obtain ⟨R, K, d, n, hf, hn3, hd, hReq, -⟩ := exists_linTwo_p hp5 hK hG hloc hType hpt
    haveI : K.Normal := hf.red.normal
    set C : Subgroup G := centralizer ({a} : Set G) with hCdef
    set O : Subgroup C := primeComplementCore (G := C) p with hO
    set ρ : C →* RedCent p a := QuotientGroup.mk' O with hρ
    have hOcop : p.Coprime (Nat.card O) := primeComplementCore_coprime p
    obtain ⟨b, hbA, hbn⟩ : ∃ b ∈ A, b ∉ zpowers a := by
      by_contra hcon
      push Not at hcon
      have hle : A ≤ zpowers a := fun g hg => hcon g hg
      have h1 := Subgroup.card_le_of_le hle
      rw [hAc, Nat.card_zpowers, hao] at h1
      have h2 := hp.out.two_le
      nlinarith
    have hb1 : b ≠ 1 := fun h => hbn (h ▸ one_mem _)
    have hbp : b ^ p = 1 := hAe.2 b hbA
    have hbo : orderOf b = p := orderOf_eq_prime hbp hb1
    have hab_comm : a * b = b * a := CFSG.Open.IsElemAbelian.comm hAe haA hbA
    have hbC : b ∈ C := mem_centralizer_singleton_iff.mpr hab_comm.symm
    have hApair : A = zpowers a ⊔ zpowers b := by
      have hle : zpowers a ⊔ zpowers b ≤ A := sup_le (zpowers_le.mpr haA) (zpowers_le.mpr hbA)
      have hcard : Nat.card (zpowers a ⊔ zpowers b : Subgroup G) = p ^ 2 := by
        rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp.out (zpowers a) hbp hbn
          (fun e he => ?_), Nat.card_zpowers, hao, pow_two]
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
        exact ((Commute.zpow_left (show Commute a b from hab_comm) k)).eq
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hAc])).symm
    let aC : C := ⟨a, mem_centralizer_singleton_iff.2 rfl⟩
    let bC : C := ⟨b, hbC⟩
    have hbCp : bC ^ p = 1 := Subtype.ext hbp
    have haCp : aC ^ p = 1 := Subtype.ext hap
    obtain ⟨hzc, hzp⟩ := hpt.central_xbar hloc
    have hout : ¬ GL83OuterType24 p (.lie d) := by
      rintro ⟨d', hd', ⟨-, hq'⟩ | ⟨-, hs⟩⟩
      · obtain rfl := TauCeti.CFSGIndex.lie.inj hd'
        obtain ⟨q, hq, hqp, -⟩ := hd
        obtain ⟨q', hq'', hqp', -⟩ := hq'
        rw [hq] at hq''
        cases hq''
        omega
      · obtain rfl := TauCeti.CFSGIndex.lie.inj hd'
        obtain ⟨q, hq, -, -⟩ := hd
        rw [hq] at hs
        cases hs
    have hbR : ρ bC ∈ (R : Subgroup (RedCent p a)) := by
      rw [hReq]
      exact ⟨bC, mem_subgroupOf.mpr ⟨hAP hbA, hbC⟩, rfl⟩
    have hbbp : (ρ bC) ^ p = 1 := by rw [← map_pow, hbCp, map_one]
    have hbmem : ρ bC ∈ K ⊔ centralizer (K : Set (RedCent p a)) := by
      rcases hf.inner with h | h
      · exact absurd h hout
      · exact h _ hbR hbbp
    obtain ⟨k, hkK, d', hd'C, hkd⟩ := mem_sup_of_normal_left.mp hbmem
    have hkd'comm : k * d' = d' * k := (mem_centralizer_iff.mp hd'C) k hkK
    have hcomm : Commute k d' := hkd'comm
    have hmulpow : k ^ p * d' ^ p = 1 := by
      have h := hbbp
      rw [← hkd, hcomm.mul_pow] at h
      exact h
    have hd'pC : d' ^ p ∈ centralizer (K : Set (RedCent p a)) := Subgroup.pow_mem _ hd'C p
    have hkpK : k ^ p ∈ K := Subgroup.pow_mem _ hkK p
    have hkp_eq : k ^ p = (d' ^ p)⁻¹ := eq_inv_of_mul_eq_one_left hmulpow
    have hkpC : k ^ p ∈ centralizer (K : Set (RedCent p a)) := by
      rw [hkp_eq]
      exact Subgroup.inv_mem _ hd'pC
    have hkp1 : k ^ p = 1 := by
      have hcen : (⟨k ^ p, hkpK⟩ : K) ∈ center K := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext ((mem_centralizer_iff.mp hkpC) g g.2)
      rw [hf.center_eq_bot, Subgroup.mem_bot] at hcen
      exact congrArg Subtype.val hcen
    have hd'p : d' ^ p = 1 := by
      rw [hkp1, one_mul] at hmulpow
      exact hmulpow
    haveI : IsCyclic (centralizer (K : Set (RedCent p a))) := hf.isCyclic
    have habarC : (ρ aC) ∈ centralizer (K : Set (RedCent p a)) :=
      mem_centralizer_iff.mpr fun h _ => (Subgroup.mem_center_iff.mp hzc h)
    have hord' : orderOf (⟨ρ aC, habarC⟩ : centralizer (K : Set (RedCent p a))) = p := by
      rw [Subgroup.orderOf_mk]
      exact hzp
    have hd'mem : (⟨d', hd'C⟩ : centralizer (K : Set (RedCent p a))) ∈
        zpowers (⟨ρ aC, habarC⟩ : centralizer (K : Set (RedCent p a))) :=
      PPointP.mem_zpowers_of_pow_prime_of_isCyclic hord' (Subtype.ext hd'p)
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hd'mem
    have hd'eq : d' = (ρ aC) ^ j := by
      have h := congrArg Subtype.val hj
      simpa using h.symm
    have hd'cen : d' ∈ center (RedCent p a) := by
      rw [hd'eq]
      exact Subgroup.zpow_mem _ hzc j
    have hk1 : k ≠ 1 := by
      intro hk1
      have hbd : ρ bC = (ρ aC) ^ j := by rw [← hkd, hk1, one_mul, hd'eq]
      have hbd' : (↑bC : C ⧸ O) = ↑(aC ^ j) := by
        have h := hbd
        rw [← map_zpow] at h
        exact h
      have hmem : bC⁻¹ * aC ^ j ∈ O := QuotientGroup.eq.mp hbd'
      have hc : Commute (bC⁻¹) (aC ^ j) :=
        (Commute.zpow_right (show Commute bC aC from Subtype.ext hab_comm.symm) j).inv_left
      have hgp : (bC⁻¹ * aC ^ j) ^ p = 1 := by
        rw [hc.mul_pow, inv_pow, hbCp, inv_one, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm,
          zpow_mul, zpow_natCast, haCp, one_zpow]
      have hord1 : orderOf (bC⁻¹ * aC ^ j) ∣ Nat.card O := by
        have := Subgroup.orderOf_dvd_natCard O hmem
        exact this
      have hord2 : orderOf (bC⁻¹ * aC ^ j) ∣ p := orderOf_dvd_of_pow_eq_one hgp
      have hord3 : orderOf (bC⁻¹ * aC ^ j) = 1 := by
        have := Nat.dvd_gcd hord2 hord1
        rw [hOcop.gcd_eq_one] at this
        exact Nat.dvd_one.mp this
      have hg1 : bC⁻¹ * aC ^ j = 1 := orderOf_eq_one_iff.mp hord3
      have hbeq : bC = aC ^ j := by
        have := congrArg (bC * ·) hg1
        simpa using this.symm
      apply hbn
      have h2 : b = a ^ j := congrArg Subtype.val hbeq
      rw [h2]
      exact zpow_mem (mem_zpowers a) j
    have hkp : orderOf k = p := orderOf_eq_prime hkp1 hk1
    set F1 : Subgroup C := (F ⊓ C).subgroupOf C with hF1
    set W : Subgroup (RedCent p a) := F1.map ρ with hW
    have hWp : ¬ p ∣ Nat.card W := by
      intro hdvd
      have h1 : Nat.card W ∣ Nat.card F1 := Subgroup.card_map_dvd F1 ρ
      have h2 : Nat.card F1 ∣ Nat.card F := by
        rw [hF1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : F ⊓ C ≤ C)).toEquiv]
        exact Subgroup.card_dvd_of_le inf_le_left
      exact hFp (hdvd.trans (h1.trans h2))
    have hbNF : bC ∈ normalizer (F1 : Set C) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      rw [hF1, mem_subgroupOf, mem_subgroupOf]
      have hbF : b ∈ normalizer (F : Set G) := hFA hbA
      have e1 : ((bC * g * bC⁻¹ : C) : G) = b * (g : G) * b⁻¹ := rfl
      rw [e1]
      constructor
      · intro hg
        exact ⟨(Subgroup.mem_normalizer_iff.mp hbF _).mp hg.1,
          C.mul_mem (C.mul_mem hbC g.2) (C.inv_mem hbC)⟩
      · intro hg
        exact ⟨(Subgroup.mem_normalizer_iff.mp hbF _).mpr hg.1, g.2⟩
    have hbbarN : ρ bC ∈ normalizer (W : Set (RedCent p a)) :=
      Subgroup.le_normalizer_map ρ ⟨bC, hbNF, rfl⟩
    have hd'N : d' ∈ normalizer (W : Set (RedCent p a)) := Subgroup.center_le_normalizer (W : Set (RedCent p a)) hd'cen
    have hkN : k ∈ normalizer (W : Set (RedCent p a)) := by
      have hke : k = ρ bC * d'⁻¹ := by rw [← hkd]; group
      rw [hke]
      exact (normalizer (W : Set (RedCent p a))).mul_mem hbbarN
        ((normalizer (W : Set (RedCent p a))).inv_mem hd'N)
    obtain ⟨eK⟩ := hf.equiv
    obtain ⟨eP⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
    have hcommW := commute_of_normalizes_unipotent hp5 (show 1 ≤ n by omega) ⟨eK.trans eP⟩ hkK hkp
      hWp hkN
    intro f hf'
    have hfC : f ∈ C := hf'.2
    let fC : C := ⟨f, hfC⟩
    have hfW : ρ fC ∈ W := ⟨fC, mem_subgroupOf.mpr hf', rfl⟩
    have hcomm1 : ρ fC * k = k * ρ fC := hcommW _ hfW
    have hcomm2 : ρ fC * ρ bC = ρ bC * ρ fC := by
      rw [← hkd]
      calc ρ fC * (k * d') = (ρ fC * k) * d' := by group
        _ = (k * ρ fC) * d' := by rw [hcomm1]
        _ = k * (ρ fC * d') := by group
        _ = k * (d' * ρ fC) := by rw [(Subgroup.mem_center_iff.mp hd'cen) (ρ fC)]
        _ = (k * d') * ρ fC := by group
    have hcommO : fC * bC * fC⁻¹ * bC⁻¹ ∈ O := by
      refine (QuotientGroup.eq_one_iff _).mp ?_
      show ρ (fC * bC * fC⁻¹ * bC⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm2]
      group
    have hDC : GLBPrimeCore p C ≤ C := glbPrimeCore_le p C
    have hCD : C ≤ normalizer ((GLBPrimeCore p C : Subgroup G) : Set G) :=
      le_normalizer_glbPrimeCore p C
    have hDcop : p.Coprime (Nat.card (GLBPrimeCore p C : Subgroup G)) := glbPrimeCore_coprime p C
    have hcommD : f * b * f⁻¹ * b⁻¹ ∈ GLBPrimeCore p C := by
      have h1 : (fC * bC * fC⁻¹ * bC⁻¹ : C) ∈ (GLBPrimeCore p C).subgroupOf C := by
        rw [glbPrimeCore_subgroupOf]
        exact hcommO
      exact mem_subgroupOf.mp h1
    obtain ⟨o, hoD, c, hcC, hcb, hfoc⟩ :=
      RankThreeTheoremC.gen49e_mem_mul_centralizer hp.out hDC hCD hDcop hbC hfC hbo hcommD
    have hoM : o ∈ M := (IsPPoint.primeCore_le hloc hpt) hoD
    have hca : c * a = a * c := mem_centralizer_singleton_iff.mp hcC
    have hcA : c ∈ normalizer (A : Set G) := by
      have hle : zpowers a ⊔ zpowers b ≤ centralizer ({c} : Set G) :=
        sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hca.symm))
          (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hcb.symm))
      have hcC' : c ∈ centralizer (A : Set G) := by
        rw [mem_centralizer_iff]
        intro g hg
        have hg' := hle (hApair ▸ hg)
        exact mem_centralizer_singleton_iff.mp hg'
      exact Subgroup.centralizer_le_normalizer (A : Set G) hcC'
    rw [← hfoc]
    exact M.mul_mem hoM (hNA hcA)
  exact hgen.le.trans hmain


end CFSG.LocalAnalysis.RankFourTheoremC.P5
