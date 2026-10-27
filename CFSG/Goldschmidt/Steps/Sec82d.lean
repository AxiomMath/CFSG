module

public import CFSG.Goldschmidt.Steps.Sec82a
import CFSG.Goldschmidt.Steps.Sec82c
import CFSG.Goldschmidt.Steps.Sec82PGroup
import CFSG.Goldschmidt.Steps.Sec8Bender
import CFSG.Goldschmidt.Steps.Sec81b
import CFSG.Goldschmidt.Steps.Sec81c
import CFSG.Goldschmidt.Steps.Sec83a
import CFSG.Goldschmidt.Steps.PropHSetup
import CFSG.Walter.Bender1970.S3.FStar
public import CFSG.Goldschmidt.StatementsG3

public section

namespace CFSG.Goldschmidt.Sec82

open CFSG.Open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G} {a : G}
  {H : Subgroup G} {p : ℕ} {M L : Subgroup G}

theorem qCoreOf_facts (c : Ctx S A a H p M L) {q : ℕ} (hq : q.Prime) :
    qCoreOf M q ≤ Subgroup.centralizer (A : Set G) ∧ qCoreOf M q ≤ H ∧
      M ≤ Subgroup.normalizer (qCoreOf M q : Set G) ∧
      L ≤ Subgroup.centralizer (qCoreOf M q : Set G) := by
  have hQF := qCoreOf_le_fittingSubgroupOf M q hq
  have hQA := hQF.trans (fittingSubgroupOf_le_centralizer_A c)
  exact ⟨hQA, hQA.trans c.hCH, le_normalizer_of_isNormalIn (qCoreOf_normal_in M q),
    Subgroup.le_centralizer_iff.mp (hQF.trans (fittingSubgroupOf_le_centralizer c))⟩

theorem centralizer_le_of_mem (h64 : S_G64) (hE : componentLayerOf H = ⊥)
    (c : Ctx S A a H p M L) (hU : UniquenessA a H) {q : ℕ} (hq : q.Prime) {v : G}
    (hvR : v ∈ qCoreOf H q) (hv1 : v ≠ 1)
    (hvC : ⁅qCoreOf H q, qCoreOf H q⁆ ≤ Subgroup.centralizer ({v} : Set G)) :
    Subgroup.centralizer ({v} : Set G) ≤ H := by
  set R := qCoreOf H q with hR
  set F := CFSG.fittingSubgroupOf H with hF
  have hvF : v ∈ F := qCoreOf_le_fittingSubgroupOf H q hq hvR
  have hFstar : generalizedFittingSubgroupOf H = F := by
    rw [generalizedFittingSubgroupOf, hE, sup_bot_eq]
    rfl
  set N' := ⨆ (r : ℕ) (_ : r.Prime) (_ : r ≠ q), qCoreOf H r with hN'
  have hRN : R ≤ Subgroup.centralizer (N' : Set G) :=
    Subgroup.le_centralizer_iff.mp (Sec8.iSup_qCoreOf_le_centralizer H hq)
  have hFF : ⁅F, F⁆ ≤ Subgroup.centralizer ({v} : Set G) := by
    rw [hF, Sec8.fittingSubgroupOf_eq_sup H hq]
    refine (commutator_sup_le_of_le_centralizer hRN).trans (sup_le hvC ?_)
    have hNN : ⁅N', N'⁆ ≤ N' := Subgroup.commutator_le.mpr fun x hx y hy => by
      rw [commutatorElement_def]
      exact N'.mul_mem (N'.mul_mem (N'.mul_mem hx hy) (N'.inv_mem hx)) (N'.inv_mem hy)
    refine hNN.trans ((Subgroup.le_centralizer_iff.mp hRN).trans (Subgroup.centralizer_le ?_))
    exact Set.singleton_subset_iff.mpr hvR
  have hvC' : v ∈ Subgroup.centralizer ((⁅F, F⁆ : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hFF hy)
  have hFF0 : ⁅F, F⁆ ≤ F := Subgroup.commutator_le.mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact F.mul_mem (F.mul_mem (F.mul_mem hx hy) (F.inv_mem hx)) (F.inv_mem hy)
  have hY0 : fstarZero H ≤ F := sup_le hFF0 (inf_le_left.trans hFstar.le)
  have hY : Subgroup.zpowers v ≤ fstarZero H := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_sup_right ⟨hFstar.symm ▸ hvF, hvC'⟩
  have hYsub : ((Subgroup.zpowers v).subgroupOf (fstarZero H)).IsSubnormal :=
    isSubnormal_of_nilpotent (Walter.isNilpotent_of_le (Sec8.isNilpotent_fittingSubgroupOf H) hY0)
      _ hY
  have hva : v ∈ Subgroup.centralizer ({a} : Set G) := c.hHa ▸ qCoreOf_le H q hvR
  have haY : a ∈ Subgroup.normalizer (Subgroup.zpowers v : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Sec8.mem_centralizer_zpowers
      (Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hva).symm))
  have hYA := hU (Subgroup.zpowers v) (fun h => hv1 (Subgroup.zpowers_eq_bot.mp h)) hY hYsub haY
  have hNtop : Subgroup.normalizer (Subgroup.zpowers v : Set G) ≠ ⊤ := by
    intro htop
    have : (Subgroup.zpowers v).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have := c.hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers v) with h | h
    · exact hv1 (Subgroup.zpowers_eq_bot.mp h)
    · exact c.hHco.1 (top_le_iff.mp (h ▸ Subgroup.zpowers_le.mpr (qCoreOf_le H q hvR)))
  obtain ⟨M', hM', hNM'⟩ := (IsCoatomic.eq_top_or_exists_le_coatom
    (Subgroup.normalizer (Subgroup.zpowers v : Set G))).resolve_left hNtop
  have hM'H : M' = H := by
    rcases hYA.2.2.2.2 M' hM' hNM' with h | ⟨r, hr, -, hFr⟩
    · exact h
    · exact absurd hFr (Sec8.not_isPGroup_fstar h64 c.hset c.h4 c.ha c.ha1 c.hH hr)
  intro x hx
  exact hM'H ▸ hNM' (Subgroup.centralizer_le_normalizer _ (Sec8.mem_centralizer_zpowers hx))

theorem isCyclic_qCoreOf_of_three_le (h64 : S_G64) (h51 : S_G51) (h81 : S_G81)
    (hE : componentLayerOf H = ⊥) (c : Ctx S A a H p M L) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hR3 : 3 ≤ CFSG.Open.pRank q (qCoreOf H q)) : IsCyclic (qCoreOf M q) := by
  have : Fact q.Prime := ⟨hq⟩
  set Q := qCoreOf M q with hQ
  set R := qCoreOf H q with hR
  obtain ⟨-, hQH, -, hLQ⟩ := qCoreOf_facts c hq
  have hQp : IsPGroup q Q := qCoreOf_isPGroup M q
  have hRp : IsPGroup q R := qCoreOf_isPGroup H q
  have hU : UniquenessA a H := by
    rcases h51 G S A c.hset a c.ha c.ha1 H c.hH with h | ⟨-, h⟩
    · exact h
    · have h2 := h q hq hq2
      rw [← hR] at h2
      omega
  have hRc : ¬ IsCyclic R := not_isCyclic_of_two_le_pRank hq (by omega)
  have hQR : Q ≤ Subgroup.normalizer (R : Set G) :=
    hQH.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in H q))
  have hT : IsPGroup q (Q ⊔ R : Subgroup G) := IsPGroup.to_sup_of_normal_right' hQp hRp hQR
  have hTR : Q ⊔ R ≤ Subgroup.normalizer (R : Set G) := sup_le hQR Subgroup.le_normalizer
  obtain ⟨V, hVR, hTV, hVc, hVq, -⟩ :=
    exists_normal_plane_le_of_le hq hq2 hT le_sup_right hTR hRc
  obtain ⟨hcomm, hcard⟩ := plane_stability_of_le hq hT (hVR.trans le_sup_right) hTV hVc
  have hRRV : ⁅R, R⁆ ≤ Subgroup.centralizer (V : Set G) := Subgroup.commutator_le.mpr
    fun x hx y hy => by
      rw [commutatorElement_def]
      exact hcomm x (Subgroup.mem_sup_right hx) y (Subgroup.mem_sup_right hy)
  have hVC : ∀ v ∈ V, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ H := fun v hv hv1 =>
    centralizer_le_of_mem h64 hE c hU hq (hVR hv) hv1
      (hRRV.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hv)))
  have hQV : Q ⊓ Subgroup.centralizer (V : Set G) = ⊥ := by
    by_contra hQ1
    set Q₁ := Q ⊓ Subgroup.centralizer (V : Set G) with hQ₁
    have hCtop : Subgroup.centralizer (Q₁ : Set G) ≠ ⊤ := by
      intro htop
      apply hQ1
      have := c.hsimple
      have hZ := PropHSetup.center_eq_bot c.hset.nonabelian
      refine eq_bot_iff.mpr fun x hx => ?_
      have hxZ : x ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g =>
        (Subgroup.mem_centralizer_iff.mp (htop ▸ Subgroup.mem_top g) x hx).symm
      rwa [hZ] at hxZ
    obtain ⟨M', hM', hCM'⟩ := (IsCoatomic.eq_top_or_exists_le_coatom
      (Subgroup.centralizer (Q₁ : Set G))).resolve_left hCtop
    have haQ₁ : Subgroup.zpowers a ≤ Subgroup.centralizer (Q₁ : Set G) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      have hxa : x ∈ Subgroup.centralizer ({a} : Set G) := c.hHa ▸ hQH hx.1
      exact Subgroup.mem_centralizer_singleton_iff.mp hxa
    have hVQ₁ : V ≤ Subgroup.centralizer (Q₁ : Set G) :=
      Subgroup.le_centralizer_iff.mp inf_le_right
    have hVF : V ≤ CFSG.fittingSubgroupOf H := hVR.trans (qCoreOf_le_fittingSubgroupOf H q hq)
    have hM'H := (h81 G S A c.hset c.h4 a c.ha c.ha1 H c.hH).2.2.2 q hq hq2 V hVF
      (hRp.to_le hVR) (not_isCyclic_of_card_sq hq hVc hVq) hVC M' hM'
      ((sup_le haQ₁ hVQ₁).trans hCM')
    exact c.hLH (hM'H ▸ (hLQ.trans (Subgroup.centralizer_le inf_le_left)).trans hCM')
  exact isCyclic_of_card_le hq hQp (hcard Q le_sup_left hQV)

end CFSG.Goldschmidt.Sec82
