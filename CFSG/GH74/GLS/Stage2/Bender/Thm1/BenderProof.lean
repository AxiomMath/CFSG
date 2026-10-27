module

public import CFSG.Walter.Bender1970.S4.Rank
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
import CFSG.Adapters.GeneralizedFitting

public section

open CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GorensteinWalter
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.BenderProof

universe u

private theorem isNormalIn_sup_of_commutator {G : Type u} [Group G]
    {H K E : Subgroup G} (hHKle : H ≤ K) (hHK : (H.subgroupOf K).Normal)
    (hE : ⁅E, K⁆ = ⊥) : IsNormalIn (H ⊔ E) (K ⊔ E) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact (sup_le_sup hHKle le_rfl) hx
  · have hKleN : K ≤ Subgroup.normalizer (((H ⊔ E) : Subgroup G) : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro k hk y hy
      rw [Subgroup.sup_eq_closure] at hy
      refine (Subgroup.closure_induction''
        (p := fun v _hv => k * v * k⁻¹ ∈ H ⊔ E) ?_ ?_ ?_ ?_) hy
      · intro v hv
        rcases hv with hvH | hvE
        · have hvK : v ∈ K := hHKle hvH
          have hvHK : (⟨v, hvK⟩ : ↥K) ∈ H.subgroupOf K := by
            rw [Subgroup.mem_subgroupOf]
            exact hvH
          have hkv : k * v * k⁻¹ ∈ H := by
            have hz : (⟨k, hk⟩ : ↥K) * (⟨v, hvK⟩ : ↥K) * (⟨k, hk⟩ : ↥K)⁻¹ ∈ H.subgroupOf K :=
              hHK.conj_mem (⟨v, hvK⟩ : ↥K) hvHK (⟨k, hk⟩ : ↥K)
            exact (Subgroup.mem_subgroupOf).1 hz
          exact (le_sup_left : H ≤ H ⊔ E) hkv
        · have hKleC : K ≤ Subgroup.centralizer (E : Set G) := by
            rw [← Subgroup.le_centralizer_iff]
            exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hE
          have hcomm : v * k = k * v :=
            (Subgroup.mem_centralizer_iff (g := k) (s := (E : Set G))).1 (hKleC hk) v hvE
          have hvHE : v ∈ H ⊔ E := (le_sup_right : E ≤ H ⊔ E) hvE
          rw [← hcomm]
          simpa using hvHE
      · intro v hv
        rcases hv with hvH | hvE
        · have hvK : v ∈ K := hHKle hvH
          have hkv : k * v⁻¹ * k⁻¹ ∈ H := by
            have hz : (⟨k, hk⟩ : ↥K) * (⟨v⁻¹, K.inv_mem hvK⟩ : ↥K) * (⟨k, hk⟩ : ↥K)⁻¹ ∈
                H.subgroupOf K :=
              hHK.conj_mem (⟨v⁻¹, K.inv_mem hvK⟩ : ↥K)
                (by rw [Subgroup.mem_subgroupOf]; exact H.inv_mem hvH) (⟨k, hk⟩ : ↥K)
            exact (Subgroup.mem_subgroupOf).1 hz
          exact (le_sup_left : H ≤ H ⊔ E) hkv
        · have hKleC : K ≤ Subgroup.centralizer (E : Set G) := by
            rw [← Subgroup.le_centralizer_iff]
            exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hE
          have hcomm : v⁻¹ * k = k * v⁻¹ :=
            (Subgroup.mem_centralizer_iff (g := k) (s := (E : Set G))).1 (hKleC hk) v⁻¹ (E.inv_mem hvE)
          have hvHE : v⁻¹ ∈ H ⊔ E := (le_sup_right : E ≤ H ⊔ E) (E.inv_mem hvE)
          rw [← hcomm]
          simpa using hvHE
      · simp
      · intro a b _ha _hb hpa hpb
        have h1 : k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
        rw [h1]
        exact (H ⊔ E).mul_mem hpa hpb
    have hEleN : E ≤ Subgroup.normalizer (((H ⊔ E) : Subgroup G) : Set G) :=
      le_sup_right.trans (H ⊔ E).le_normalizer
    exact (Subgroup.le_normalizer_iff (H := (K ⊔ E)) (K := (H ⊔ E))).1
      (sup_le hKleN hEleN)

private theorem subgroupOf_normal_of_isNormalIn {G : Type u} [Group G]
    {H K L : Subgroup G} (hHK : IsNormalIn H K) (_hKL : K ≤ L) :
    ((H.subgroupOf L).subgroupOf (K.subgroupOf L)).Normal := by
  refine ⟨?conj_mem⟩
  intro n hn g
  have hnH : ((n : ↥L) : G) ∈ H :=
    (Subgroup.mem_subgroupOf).mp (Subgroup.mem_subgroupOf.mp hn)
  have hnK : ((n : ↥L) : G) ∈ K := (Subgroup.mem_subgroupOf).mp n.2
  have hgK : ((g : ↥L) : G) ∈ K := (Subgroup.mem_subgroupOf).mp g.2
  have hconj : (g : ↥L).1 * (n : ↥L).1 * (g : ↥L).1⁻¹ ∈ H :=
    hHK.2 (g : ↥L).1 hgK (n : ↥L).1 hnH
  rw [Subgroup.mem_subgroupOf]
  rw [Subgroup.mem_subgroupOf]
  exact hconj

private theorem subgroupOf_normal_of_map {G : Type u} [Group G] {F : Subgroup G}
    {H K : Subgroup (↥F)} (hHKle : H ≤ K) (hHK : (H.subgroupOf K).Normal) :
    ((H.map F.subtype).subgroupOf (K.map F.subtype)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer
    (h := Subgroup.map_mono (f := F.subtype) hHKle)]
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  rcases (Subgroup.mem_map).1 hx with ⟨kx, hkx, rfl⟩
  rcases (Subgroup.mem_map).1 hy with ⟨ky, hky, rfl⟩
  have hkyK : ky ∈ K := hHKle hky
  have hkyHK : (⟨ky, hkyK⟩ : ↥K) ∈ H.subgroupOf K := by
    rw [Subgroup.mem_subgroupOf]
    exact hky
  have hconj : kx * ky * kx⁻¹ ∈ H := by
    have hzc : (⟨kx, hkx⟩ : ↥K) * (⟨ky, hkyK⟩ : ↥K) * (⟨kx, hkx⟩ : ↥K)⁻¹ ∈ H.subgroupOf K :=
      hHK.conj_mem (⟨ky, hkyK⟩ : ↥K) hkyHK (⟨kx, hkx⟩ : ↥K)
    exact (Subgroup.mem_subgroupOf).1 hzc
  exact Subgroup.mem_map.mpr ⟨kx * ky * kx⁻¹, hconj, by simp⟩

theorem isSubnormal_sup_of_centralizing' {G : Type u} [Group G]
    {T F E : Subgroup G} (hTF : T ≤ F) (hT : (T.subgroupOf F).IsSubnormal)
    (hE : ⁅E, F⁆ = ⊥) : ((T ⊔ E).subgroupOf (F ⊔ E)).IsSubnormal := by
  classical
  let P : Subgroup (↥F) → Prop := fun U =>
    ((U.map F.subtype ⊔ E).subgroupOf (F ⊔ E)).IsSubnormal
  have hmain : ∀ U : Subgroup (↥F), U.IsSubnormal → P U := by
    intro U hU
    induction hU with
    | top =>
        have hmap : (⊤ : Subgroup (↥F)).map F.subtype = F := by
          apply le_antisymm
          · intro y hy
            rcases (Subgroup.mem_map).1 hy with ⟨u, _hu, rfl⟩
            exact u.2
          · intro x hx
            exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, by simp, rfl⟩
        simp [P, hmap]
    | step H K h_le hK hN ih =>
        have hmap_le : H.map F.subtype ≤ K.map F.subtype :=
          Subgroup.map_mono (f := F.subtype) h_le
        have hNmap : ((H.map F.subtype).subgroupOf (K.map F.subtype)).Normal :=
          subgroupOf_normal_of_map h_le hN
        have hKmap_le_F : K.map F.subtype ≤ F := by
          intro y hy
          rcases (Subgroup.mem_map).1 hy with ⟨u, _hu, rfl⟩
          exact u.2
        have hEcentral : ⁅E, K.map F.subtype⁆ = ⊥ := by
          have hle : ⁅E, K.map F.subtype⁆ ≤ ⁅E, F⁆ :=
            Subgroup.commutator_mono le_rfl hKmap_le_F
          simpa [hE] using hle
        have hNsup : IsNormalIn (H.map F.subtype ⊔ E) (K.map F.subtype ⊔ E) :=
          isNormalIn_sup_of_commutator hmap_le hNmap hEcentral
        have hKleL : K.map F.subtype ⊔ E ≤ F ⊔ E :=
          sup_le (hKmap_le_F.trans le_sup_left) le_sup_right
        have hN' : (((H.map F.subtype ⊔ E).subgroupOf (F ⊔ E)).subgroupOf
            ((K.map F.subtype ⊔ E).subgroupOf (F ⊔ E))).Normal :=
          subgroupOf_normal_of_isNormalIn hNsup hKleL
        have hle' : (H.map F.subtype ⊔ E).subgroupOf (F ⊔ E) ≤
            (K.map F.subtype ⊔ E).subgroupOf (F ⊔ E) :=
          Subgroup.subgroupOf_mono (F ⊔ E) (sup_le_sup hmap_le le_rfl)
        exact Subgroup.IsSubnormal.step _ _ hle' ih hN'
  have hmap_eq : (T.subgroupOf F).map F.subtype = T := by
    apply le_antisymm
    · intro y hy
      rcases (Subgroup.mem_map).1 hy with ⟨u, hu, rfl⟩
      exact (Subgroup.mem_subgroupOf).1 hu
    · intro x hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hTF hx⟩, by rw [Subgroup.mem_subgroupOf]; exact hx, rfl⟩
  simpa [P, hmap_eq] using hmain (T.subgroupOf F) hT



theorem gfs_top_eq (Y : Type) [Group Y] [Finite Y] :
    generalizedFittingSubgroupOf (⊤ : Subgroup Y) = CFSG.generalizedFitting Y :=
  CFSG.Adapters.generalizedFittingSubgroupOf_top_eq_foundations Y

theorem Fs_eq {G : Type} [Group G] [Finite G] (M : Subgroup G) :
    Fs M = generalizedFittingSubgroupOf M := by
  rw [← generalizedFittingSubgroupOf_subgroup_top_eq M, gfs_top_eq]
  rfl




theorem S_subnormal {G : Type} [Group G] [Finite G] (M Y : Subgroup G)
    (hY : Y ≤ CFSG.fittingSubgroupOf M) :
    ((generalizedFittingSubgroupOf M ⊓ Subgroup.normalizer (Y : Set G)).subgroupOf
      (generalizedFittingSubgroupOf M)).IsSubnormal := by
  classical
  let F : Subgroup G := CFSG.fittingSubgroupOf M
  let E : Subgroup G := componentLayerOf M
  let K : Subgroup G := generalizedFittingSubgroupOf M
  let N : Subgroup G := Subgroup.normalizer (Y : Set G)
  let S : Subgroup G := K ⊓ N
  have hEF : ⁅E, F⁆ = ⊥ := layer_centralizes_fitting M
  have hEFle : E ≤ Subgroup.centralizer (F : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hEF
  have hEN : E ≤ N := by
    exact (hEFle.trans (Subgroup.centralizer_le (show (Y : Set G) ⊆ (F : Set G) from hY))).trans
      (Subgroup.centralizer_le_normalizer (Y : Set G))
  have hmod : (F ⊔ E) ⊓ N = E ⊔ (F ⊓ N) := by
    apply le_antisymm
    · intro x hx
      rcases mem_sup_decompose_of_centralizes hx.1 hEFle with ⟨f, hf, e, he, rfl⟩
      have hfN : f ∈ N := by
        have hxe : (f * e) * e⁻¹ ∈ N := N.mul_mem hx.2 (N.inv_mem (hEN he))
        simpa using hxe
      have hcomm : f * e = e * f :=
        (Subgroup.mem_centralizer_iff (g := e) (s := (F : Set G))).1 (hEFle he) f hf
      have hmem : e * f ∈ E ⊔ (F ⊓ N) :=
        (Subgroup.mul_mem_sup he (show f ∈ F ⊓ N from ⟨hf, hfN⟩))
      simpa [hcomm] using hmem
    · exact
        le_inf
          (sup_le (le_sup_right : E ≤ F ⊔ E)
            ((inf_le_left : F ⊓ N ≤ F).trans (le_sup_left : F ≤ F ⊔ E)))
          (sup_le hEN inf_le_right)
  have hS_eq : S = (F ⊓ N) ⊔ E := by
    calc
      S = (F ⊔ E) ⊓ N := rfl
      _ = E ⊔ (F ⊓ N) := hmod
      _ = (F ⊓ N) ⊔ E := by rw [sup_comm]
  have hFnil : Group.IsNilpotent F := by
    have : Group.IsNilpotent (fittingSubgroup (↥M)) := by infer_instance
    change Group.IsNilpotent ((fittingSubgroup (↥M)).map M.subtype)
    let e : fittingSubgroup (↥M) ≃* (fittingSubgroup (↥M)).map M.subtype :=
      Subgroup.equivMapOfInjective (f := M.subtype) (fittingSubgroup (↥M)) M.subtype_injective
    exact Group.nilpotent_of_mulEquiv e
  have hTsub : ((F ⊓ N).subgroupOf F).IsSubnormal :=
    isSubnormal_of_nilpotent hFnil (F ⊓ N) inf_le_left
  have hTsubE : (((F ⊓ N) ⊔ E).subgroupOf (F ⊔ E)).IsSubnormal :=
    isSubnormal_sup_of_centralizing' inf_le_left hTsub hEF
  show (S.subgroupOf K).IsSubnormal
  rw [hS_eq]
  rw [show K = F ⊔ E from rfl]
  exact hTsubE

theorem S_selfCent {G : Type} [Group G] [Finite G] (M Y : Subgroup G)
    (hY : Y ≤ CFSG.fittingSubgroupOf M) :
    generalizedFittingSubgroupOf M ⊓ Subgroup.centralizer
        ((generalizedFittingSubgroupOf M ⊓ Subgroup.normalizer (Y : Set G) : Subgroup G) : Set G) ≤
      generalizedFittingSubgroupOf M ⊓ Subgroup.normalizer (Y : Set G) := by
  have hYK : Y ≤ generalizedFittingSubgroupOf M :=
    hY.trans (le_sup_left : CFSG.fittingSubgroupOf M ≤ generalizedFittingSubgroupOf M)
  have hYS : Y ≤ generalizedFittingSubgroupOf M ⊓ Subgroup.normalizer (Y : Set G) :=
    le_inf hYK Subgroup.le_normalizer
  intro c hc
  have hcX : c ∈ Subgroup.centralizer (Y : Set G) :=
    (Subgroup.centralizer_le (show (Y : Set G) ⊆ _ from hYS)) hc.2
  exact ⟨hc.1, Subgroup.centralizer_le_normalizer (Y : Set G) hcX⟩


theorem Op_Fm_eq {G : Type} [Group G] [Finite G] (N : Subgroup G) {p : ℕ} (hp : p.Prime) :
    Op p (Fm N) = qCoreOf N p := by
  apply le_antisymm
  · exact qCoreOf_fittingSubgroupOf_le_qCoreOf N p hp
  · exact fstar_qCoreOf_le_qCoreOf_fittingSubgroupOf N p hp

theorem mem_primesOfOrder_Fm {G : Type} [Group G] [Finite G] (M : Subgroup G) {p : ℕ} :
    p ∈ primesOfOrder (CFSG.fittingSubgroupOf M) ↔ p.Prime ∧ p ∣ Nat.card (Fm M) := by
  have h0 : Nat.card (Fm M) ≠ 0 := Nat.card_pos.ne'
  show p ∈ (Nat.card (CFSG.fittingSubgroupOf M)).primeFactors ↔ _
  rw [Nat.mem_primeFactors]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, h0⟩⟩

theorem bender12_thm : CFSG.GH74.GLS.Stage2.Bender.Thm1.Bender12 := by
  unfold CFSG.GH74.GLS.Stage2.Bender.Thm1.Bender12 B_bender_lemma_1_2
  intro G _ _ hG M N hM Y hY hYN
  classical
  have hsimple : IsSimpleGroup G := hG.1
  have hYF : Y ≤ CFSG.fittingSubgroupOf M := hY
  rw [Fs_eq M] at hYN ⊢
  have hasm := bender1970_1_7_residual_commutator_assembly hsimple M hM
    (generalizedFittingSubgroupOf M ⊓ Subgroup.normalizer (Y : Set G)) inf_le_left
    (S_subnormal M Y hYF) (S_selfCent M Y hYF) hYN
  refine ⟨?_, ?_, ?_⟩
  ·
    have hFpi : Fpi {p | p.Prime ∧ ¬ p ∣ Nat.card (Fm M)} N =
        ⨆ p ∈ {p | p.Prime ∧ ¬ p ∣ Nat.card (Fm M)}, qCoreOf N p := by
      unfold Fpi
      refine iSup_congr fun p => iSup_congr fun hp => ?_
      exact Op_Fm_eq N hp.1
    rw [hFpi]
    set σ : Set ℕ := {p | p.Prime ∧ ¬ p ∣ Nat.card (Fm M)} with hσ
    set B : Subgroup G := ⨆ p ∈ σ, qCoreOf N p with hB
    by_contra hne
    have h1 : 1 < Nat.card ↥(B ⊓ M) := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
    have hr : (Nat.card ↥(B ⊓ M)).minFac.Prime := Nat.minFac_prime (by omega)
    set r := (Nat.card ↥(B ⊓ M)).minFac with hrdef
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(B ⊓ M)) r (Nat.minFac_dvd _)
    have hgB : (g : G) ∈ B := g.2.1
    have hgM : (g : G) ∈ M := g.2.2
    have hord : orderOf (g : G) = r := by rw [Subgroup.orderOf_coe]; exact hg
    have hBle : B ≤ piCoreOf N σ := iSup₂_le fun q hq => qCoreOf_le_piCoreOf N σ q hq hq.1
    have hrdvd : r ∣ Nat.card ↥(piCoreOf N σ) := by
      have hmem : (g : G) ∈ piCoreOf N σ := hBle hgB
      have h2 := orderOf_dvd_natCard (⟨(g : G), hmem⟩ : ↥(piCoreOf N σ))
      have h3 : orderOf (⟨(g : G), hmem⟩ : ↥(piCoreOf N σ)) = r := by
        rw [← Subgroup.orderOf_coe]; exact hord
      rwa [h3] at h2
    have hrσ : r ∈ σ := piCoreOf_primeDivisors N σ r
      (Nat.mem_primeFactors.mpr ⟨hr, hrdvd, Nat.card_pos.ne'⟩)
    have hrnot : r ∉ primesOfOrder (CFSG.fittingSubgroupOf M) := by
      intro h; exact hrσ.2 ((mem_primesOfOrder_Fm M).1 h).2
    have hBF : B ≤ CFSG.fittingSubgroupOf N :=
      iSup₂_le fun q hq => qCoreOf_le_fittingSubgroupOf N q hq.1
    have hzp : Subgroup.zpowers (g : G) ≤ qCoreOf N r := by
      refine CFSG.Walter.le_qCoreOf_of_le_fittingSubgroupOf hr ?_ ?_
      · exact Subgroup.zpowers_le.2 (hBF hgB)
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
    have hbot := hasm.1 r hr hrnot
    have hgin : (g : G) ∈ qCoreOf N r ⊓ M := ⟨hzp (Subgroup.mem_zpowers _), hgM⟩
    rw [hbot, Subgroup.mem_bot] at hgin
    have : orderOf (g : G) = 1 := by rw [hgin]; exact orderOf_one
    rw [hord] at this
    exact hr.one_lt.ne' this
  ·
    by_cases h : ∃ q : ℕ, q.Prime ∧ q ∣ Nat.card (Fm M) ∧
        pResidualOf (generalizedFittingSubgroupOf M) q = ⊥
    · obtain ⟨q, hq, -, hres⟩ := h
      exact Or.inl ⟨q, hq, isPGroup_of_pResidualOf_eq_bot _ q hq hres⟩
    · right
      refine iSup₂_le fun q hqσ => ?_
      obtain ⟨hq, hqd⟩ := hqσ
      rw [Op_Fm_eq N hq]
      have hres : pResidualOf (generalizedFittingSubgroupOf M) q ≠ ⊥ :=
        fun hb => h ⟨q, hq, hqd, hb⟩
      have hqmem := (mem_primesOfOrder_Fm M).2 ⟨hq, hqd⟩
      have hcomm := hasm.2 q hq hqmem
      have hRA := pResidualOf_generalizedFitting_isNormalIn M q
      have hN := normalizer_eq_of_nontrivial_normal_in_coatom hsimple hM hRA.1 hres
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hRA.1).mpr (le_normalizer_of_isNormalIn hRA))
      calc qCoreOf N q
          ≤ Subgroup.centralizer (pResidualOf (generalizedFittingSubgroupOf M) q : Set G) :=
            Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
        _ ≤ Subgroup.normalizer (pResidualOf (generalizedFittingSubgroupOf M) q : Set G) :=
            Subgroup.centralizer_le_normalizer _
        _ = M := hN
  ·
    intro p hp hpdvd
    have hpmem : p ∈ primesOfOrder (CFSG.fittingSubgroupOf M) :=
      (mem_primesOfOrder_Fm M).2 ⟨hp, hpdvd⟩
    have hcomm := hasm.2 p hp hpmem
    have hOp : Op p N = qCoreOf N p := rfl
    have hle : inSubgroup (oResidual p)
        (generalizedFittingSubgroupOf M ⊓ Subgroup.normalizer (Y : Set G)) ≤
        pResidualOf (generalizedFittingSubgroupOf M) p := by
      show (oResidual p ↥(generalizedFittingSubgroupOf M ⊓ Subgroup.normalizer (Y : Set G))).map
        (generalizedFittingSubgroupOf M ⊓ Subgroup.normalizer (Y : Set G)).subtype ≤ _
      refine (Subgroup.map_le_iff_le_comap).2 ((Subgroup.closure_le _).2 ?_)
      intro x hx
      have hxK : (x : G) ∈ generalizedFittingSubgroupOf M := x.2.1
      refine mem_pResidualOf_of_order_coprime _ p hp hxK ?_
      show p.Coprime (orderOf (x : G))
      rw [Subgroup.orderOf_coe]
      exact Nat.Coprime.symm hx
    rw [hOp]
    refine eq_bot_iff.2 ((Subgroup.commutator_mono hle le_rfl).trans ?_)
    rw [Subgroup.commutator_comm]
    exact hcomm.le


theorem ne_bot_of_coatom {G : Type} [Group G] (hG : IsKProperSimple G) {M : Subgroup G}
    (hM : IsCoatom M) : M ≠ ⊥ := by
  intro h
  subst h
  obtain ⟨a, b, hab⟩ := hG.2.1
  have ha : a ≠ 1 := by
    rintro rfl
    exact hab (by simp)
  have hlt : (⊥ : Subgroup G) < Subgroup.zpowers a := by
    rw [bot_lt_iff_ne_bot]
    intro h2
    exact ha (by simpa [Subgroup.zpowers_eq_bot] using h2)
  have htop : Subgroup.zpowers a = ⊤ := hM.2 _ hlt
  have hb : b ∈ Subgroup.zpowers a := by rw [htop]; trivial
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  exact hab (Commute.self_zpow a k).eq

theorem bender13_thm : CFSG.GH74.GLS.Stage2.Bender.Thm1.Bender13 := by
  unfold CFSG.GH74.GLS.Stage2.Bender.Thm1.Bender13 B_bender_1_3
  intro G _ _ hG M N hM hN hMN' hNM'
  classical
  have hsimple : IsSimpleGroup G := hG.1
  obtain ⟨Y, hY, hYN⟩ := hMN'
  obtain ⟨Y', hY', hY'M⟩ := hNM'
  by_cases hMN : M = N
  · exact Or.inl hMN
  right
  have hYF : Y ≤ CFSG.fittingSubgroupOf M := hY
  have hYF' : Y' ≤ CFSG.fittingSubgroupOf N := hY'
  rw [Fs_eq M] at hYN ⊢
  rw [Fs_eq N] at hY'M ⊢
  have hS := S_subnormal M Y hYF
  have hS' := S_selfCent M Y hYF
  have hT := S_subnormal N Y' hYF'
  have hT' := S_selfCent N Y' hYF'
  by_cases hpi : 2 ≤ Nat.card ↑(primesOfOrder (generalizedFittingSubgroupOf M)) ∨
      2 ≤ Nat.card ↑(primesOfOrder (generalizedFittingSubgroupOf N))
  · exact absurd (bender1970_1_7_iii_equalityOfMaximal hsimple M hM _ inf_le_left hS hS' hYN hN hpi
      ⟨_, hY'M, inf_le_left, hT, hT'⟩) hMN
  · push Not at hpi
    have hM0 : M ≠ ⊥ := ne_bot_of_coatom hG hM
    have hN0 : N ≠ ⊥ := ne_bot_of_coatom hG hN
    have hFM0 := CFSG.Walter.generalizedFittingSubgroupOf_ne_bot hM0
    have hFN0 := CFSG.Walter.generalizedFittingSubgroupOf_ne_bot hN0
    have hone : ∀ X : Subgroup G, Nat.card ↑(primesOfOrder X) < 2 →
        ∀ a b, a ∈ primesOfOrder X → b ∈ primesOfOrder X → a = b := by
      intro X hX a b ha hb
      have hfin : (primesOfOrder X).Finite := by
        have : primesOfOrder X = ↑((Nat.card ↥X).primeFactors) := by
          ext r; simp [primesOfOrder]
        rw [this]; exact Finset.finite_toSet _
      have h1 : (primesOfOrder X).ncard ≤ 1 := by
        rw [← Nat.card_coe_set_eq]; omega
      exact (Set.ncard_le_one_iff hfin).1 h1 ha hb
    obtain ⟨p, hp⟩ := primesOfOrder_nonempty_of_ne_bot _ hFM0
    obtain ⟨q, hq⟩ := primesOfOrder_nonempty_of_ne_bot _ hFN0
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hFMp : IsPGroup p ↥(generalizedFittingSubgroupOf M) :=
      isPGroup_of_primeFactors_subset_singleton _ hpp
        (fun r hr => hone _ hpi.1 r p hr hp)
    have hFNq : IsPGroup q ↥(generalizedFittingSubgroupOf N) :=
      isPGroup_of_primeFactors_subset_singleton _ hqp
        (fun r hr => hone _ hpi.2 r q hr hq)
    have hpq : q = p := by
      by_contra hne
      have hqnot : q ∉ primesOfOrder (CFSG.fittingSubgroupOf M) := by
        intro hqF
        have := primesOfOrder_subset_of_le
          (le_sup_left : CFSG.fittingSubgroupOf M ≤ generalizedFittingSubgroupOf M) hqF
        exact hne (hone _ hpi.1 q p this hp)
      have hdisj := bender1970_1_7_i_oddCoreDisjoint hsimple M hM _ inf_le_left hS hS' hYN q hqp hqnot
      have hFNle : generalizedFittingSubgroupOf N ≤ qCoreOf N q := by
        have hRA := generalizedFittingSubgroupOf_isNormalIn N
        exact le_qCoreOf_of_normal_isPGroup N _ q hRA.1
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hRA.1).mpr
            (le_normalizer_of_isNormalIn hRA)) hFNq
      have hSbarbot : generalizedFittingSubgroupOf N ⊓ Subgroup.normalizer (Y' : Set G) = ⊥ := by
        rw [eq_bot_iff, ← hdisj]
        exact le_inf (inf_le_left.trans hFNle) hY'M
      apply hFN0
      rw [eq_bot_iff]
      intro x hx
      have hxc : x ∈ Subgroup.centralizer
          ((generalizedFittingSubgroupOf N ⊓ Subgroup.normalizer (Y' : Set G) : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        have : s ∈ (⊥ : Subgroup G) := by rw [← hSbarbot]; exact hs
        rw [Subgroup.mem_bot] at this
        subst this
        simp
      have := hT' ⟨hx, hxc⟩
      rw [hSbarbot] at this
      exact this
    exact ⟨p, hpp, hFMp, hpq ▸ hFNq⟩


theorem Fm_map {G : Type} [Group G] [Finite G] (c : G ≃* G) (M : Subgroup G) :
    Fm (M.map c.toMonoidHom) = (Fm M).map c.toMonoidHom := by
  let e := Subgroup.equivMapOfInjective M c.toMonoidHom c.injective
  have h1 : (fittingSubgroup ↥M).map e.toMonoidHom = fittingSubgroup ↥(M.map c.toMonoidHom) :=
    CFSG.Walter.map_fittingSubgroup_of_mulEquiv' e
  show (fittingSubgroup ↥(M.map c.toMonoidHom)).map (M.map c.toMonoidHom).subtype =
    ((fittingSubgroup ↥M).map M.subtype).map c.toMonoidHom
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem Em_map {G : Type} [Group G] [Finite G] (c : G ≃* G) (M : Subgroup G) :
    Em (M.map c.toMonoidHom) = (Em M).map c.toMonoidHom := by
  let e := Subgroup.equivMapOfInjective M c.toMonoidHom c.injective
  have h1 : (layer ↥M).map e.toMonoidHom = layer ↥(M.map c.toMonoidHom) := by
    rw [← CFSG.Walter.componentLayerOf_top_eq_layer, ← CFSG.Walter.componentLayerOf_top_eq_layer]
    exact CFSG.Walter.componentLayerOf_top_map_of_mulEquiv' e
  show (layer ↥(M.map c.toMonoidHom)).map (M.map c.toMonoidHom).subtype =
    ((layer ↥M).map M.subtype).map c.toMonoidHom
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1


theorem Fpi_compl_bot {G : Type} [Group G] [Finite G] (N : Subgroup G) (n : ℕ)
    (hn : Nat.card ↥(Fm N) = n) :
    Fpi {q | q.Prime ∧ ¬ q ∣ n} N = ⊥ := by
  refine eq_bot_iff.2 (iSup₂_le fun q hq => ?_)
  have : Fact q.Prime := ⟨hq.1⟩
  have hpg : IsPGroup q ↥(Op q (Fm N)) := qCoreOf_isPGroup (Fm N) q
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := q)).1 hpg
  have hle : Op q (Fm N) ≤ Fm N := qCoreOf_le (Fm N) q
  have hdvd : Nat.card ↥(Op q (Fm N)) ∣ Nat.card ↥(Fm N) := Subgroup.card_dvd_of_le hle
  rw [hk, hn] at hdvd
  have hk0 : k = 0 := by
    by_contra hne
    exact hq.2 ((dvd_pow_self q hne).trans hdvd)
  rw [hk0, pow_zero] at hk
  exact (Subgroup.eq_bot_of_card_eq _ hk).le

theorem bender14_thm : CFSG.GH74.GLS.Stage2.Bender.Thm1.Bender14 := by
  unfold CFSG.GH74.GLS.Stage2.Bender.Thm1.Bender14 B_bender_1_4
  intro G _ _ hG M N hM hN hMN' hnot
  classical
  have hA : Links N M → M = N := by
    intro hNM
    rcases bender13_thm G hG M N hM hN hMN' hNM with h | ⟨p, hp, hpM, -⟩
    · exact h
    · exact absurd ⟨p, hp, hpM⟩ hnot
  refine ⟨hA, ?_⟩
  intro g hNg hEm
  set c : G ≃* G := MulAut.conj g⁻¹ with hc
  have hNc : N = M.map c.toMonoidHom := hNg
  obtain ⟨Y, hY, hYN⟩ := hMN'
  have hb12 := (bender12_thm G hG M N hM Y hY hYN).2.1
  have hb12' : Fpi {p | p.Prime ∧ p ∣ Nat.card ↥(Fm M)} N ≤ M := hb12.resolve_left hnot
  have hEmN : Em N = ⊥ := by rw [hNc, Em_map, hEm, Subgroup.map_bot]
  have hFmN : Fm N = (Fm M).map c.toMonoidHom := by rw [hNc, Fm_map]
  have hcard : Nat.card ↥(Fm N) = Nat.card ↥(Fm M) := by
    rw [hFmN]; exact Subgroup.card_map_of_injective c.injective
  have hFsN : Fs N = Fm N := by
    rw [CFSG.GH74.GLS.Stage2.Bender.Thm1.Fs_eq_sup, hEmN, sup_bot_eq]
  have hFsle : Fs N ≤ M := by
    rw [hFsN]
    have h1 := CFSG.GH74.GLS.Stage2.Bender.Thm1.Fm_le_Fpi_sup (fun q => q ∣ Nat.card ↥(Fm M)) N
    rw [Fpi_compl_bot N (Nat.card ↥(Fm M)) hcard, sup_bot_eq] at h1
    exact h1.trans hb12'
  have hlinks : Links N M := ⟨⊥, bot_le, inf_le_left.trans hFsle⟩
  have hMN : M = N := hA hlinks
  have hgN : g ∈ Subgroup.normalizer (M : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have h1 : h ∈ CFSG.conjugate M g ↔ h ∈ N := by rw [← hNg]
    rw [← hMN] at h1
    rw [← h1, CFSG.GH74.GLS.Stage2.Bender.Thm1.mem_conjugate_iff]
  by_contra hgM
  have hlt : M < Subgroup.normalizer (M : Set G) :=
    lt_of_le_of_ne Subgroup.le_normalizer (fun h => hgM (h ▸ hgN))
  have htop : Subgroup.normalizer (M : Set G) = ⊤ := hM.2 _ hlt
  have : M.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases (hG.1 : IsSimpleGroup G).eq_bot_or_eq_top_of_normal M with h | h
  · exact ne_bot_of_coatom hG hM h
  · exact hM.1 h

end CFSG.GH74.GLS.Stage2.Bender.Thm1.BenderProof

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem bender12_thm : Bender12 := BenderProof.bender12_thm

theorem bender13_thm : Bender13 := BenderProof.bender13_thm

theorem bender14_thm : Bender14 := BenderProof.bender14_thm

end CFSG.GH74.GLS.Stage2.Bender.Thm1

