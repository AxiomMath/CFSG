module

public import CFSG.LocalAnalysis.AGLEmbedding.A15Components
import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
import CFSG.LocalAnalysis.AGLEmbedding.A15OddCore
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.PrimeBlockGlue
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Block

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R L : Subgroup G}

theorem D1PhaseThree.mem_centralizer_of_mem_sup_of (h : D1PhaseThree p P M H R)
    (_hb : StmtBlockInnerNormalizer) (h84 : Asc81bEightFour) (h86 : Asc81bEightSix)
    (hD2 : D1NoXBlock) (hL : IsWeakSBlock M (pCoreOf 2 H) L) {q : ℕ}
    (hPL : q.Coprime (Nat.card (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L))))
    {x : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hx : x ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hxS : x ∈ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {k : ℕ} (hxq : x ^ q ^ k = 1) :
    x ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  h.mem_centralizer_of_mem_sup h84 h86 hD2 hL hPL hx hxS hxq

end Block

section A15

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M H R : Subgroup G} {c : Fin 3 → G}
  {σ τ : G}

theorem D1A15Data.mk_pow_five_eq_one (h : D1A15Data P M H R c σ τ) {x : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hx : x ∈ barM M R) : x ^ 5 ^ 1 = 1 := by
  rw [pow_one]
  exact h.isElemAbelian_barM.2 x hx

theorem D1A15Data.barM_le_centralizer_block (h : D1A15Data P M H R c σ τ)
    (hB3 : StmtBlockThree) (hb : StmtBlockInnerNormalizer) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (hα : KFactThreeOrFiveDvd)
    (hS : CatalogOuterSolvable) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hLN : (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L ≤ GLBPrimeCore 5 H) :
    barM M R ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have h3 := h.surv.ph3
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  set S := pCoreOf 2 H with hSdef
  have hle : Subgroup.normalizer (S : Set G) ⊓ L ≤ GLBPrimeCore 5 H := by
    refine le_trans (le_inf ?_ ?_) hLN
    · intro x hx
      rw [hKeq]
      exact ⟨hL.le hx.2, hx.1⟩
    · intro x hx
      exact Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem 1
        (Subgroup.mem_iSup_of_mem (H ⊓ M).one_mem ⟨x, hx.2, by simp⟩))
  have hdvd : Nat.card (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ∣
      Nat.card (Subgroup.normalizer (S : Set G) ⊓ L : Subgroup G) := by
    have := Subgroup.card_map_dvd ((Subgroup.normalizer (S : Set G) ⊓ L).subgroupOf M)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hL.le)).toEquiv]
      at this
  have hPL : Nat.Coprime 5 (Nat.card (barM M (Subgroup.normalizer (S : Set G) ⊓ L))) :=
    Nat.Coprime.coprime_dvd_right (hdvd.trans (Subgroup.card_dvd_of_le hle))
      (glbPrimeCore_coprime 5 H)
  have hRS : barM M R ≤ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    barM_le_normalizer_barM ((h3.le_inf.trans hKeq.le).trans inf_le_right)
  intro x hx
  exact h3.mem_centralizer_of_mem_sup_of hb h84 h86 hD2 hL hPL
    (h.le_sup_centralizer_component hB3 hα hS hL.component hx) (hRS hx)
    (h.mk_pow_five_eq_one hx)

theorem D1A15Data.barM_le_centralizer_of_coprime (h : D1A15Data P M H R c σ τ)
    (hB3 : StmtBlockThree) (hα : KFactThreeOrFiveDvd) (hS : CatalogOuterSolvable)
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤)
    (hcop : Nat.Coprime 5 (Nat.card Lb)) :
    barM M R ≤ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  set C := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCdef
  have hLC : Lb ≤ Subgroup.normalizer (C : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.le_normalizer.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  intro x hx
  have hx5 := h.mk_pow_five_eq_one hx
  have hxLC := h.le_sup_centralizer_component hB3 hα hS hLb hx
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Lb C hLC] at hxLC
  obtain ⟨l, hl, c', hc', rfl⟩ := hxLC
  exact mul_mem_centralizer_of_coprime hl le_rfl hc' hcop hx5

theorem D1A15Data.card_center_quotient_eq (h : D1A15Data P M H R c σ τ) {L : Subgroup G}
    (hL2 : IsTwoPrimeComponent M L) (hLK : L ≤ H ⊓ M) (hLN : ¬ L ≤ GLBPrimeCore 5 H) :
    Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) = 60 := by
  have h3 := h.surv.ph3
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLbdef
  have hLb : IsComponentOf Lb ⊤ := hL2.component
  have hLM : L ≤ M := hL2.le
  let f₀ : ↥L →* ↥Lb := (mk.comp (Subgroup.inclusion hLM)).codRestrict Lb fun l =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr l.2)
  have hf₀ : Function.Surjective f₀ := by
    rintro ⟨_, ⟨m, hm, rfl⟩⟩
    exact ⟨⟨m, Subgroup.mem_subgroupOf.mp hm⟩, rfl⟩
  let f : ↥L →* ↥Lb ⧸ Subgroup.center ↥Lb := (QuotientGroup.mk' _).comp f₀
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp hf₀
  let e : ↥L ⧸ f.ker ≃* ↥Lb ⧸ Subgroup.center ↥Lb :=
    QuotientGroup.quotientKerEquivOfSurjective f hf
  have : IsSimpleGroup (↥Lb ⧸ Subgroup.center ↥Lb) := hLb.2.2.2
  have hsimple : IsSimpleGroup (↥L ⧸ f.ker) := e.isSimpleGroup
  obtain ⟨a, b, hab⟩ :=
    ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hLb.2.2
  have hnab : ∃ a b : ↥L ⧸ f.ker, a * b ≠ b * a :=
    ⟨e.symm a, e.symm b, fun he => hab (by simpa using congrArg e he)⟩
  have hNV : (GLBPrimeCore 5 H).subgroupOf L ≤ f.ker := by
    set T := barM M (GLBPrimeCore 5 H ⊓ L) with hT
    have hTL : T ≤ Lb := barM_mono inf_le_right
    have hLT : L ≤ Subgroup.normalizer ((GLBPrimeCore 5 H ⊓ L : Subgroup G) : Set G) :=
      (le_inf ((hLK.trans inf_le_left).trans (le_normalizer_glbPrimeCore 5 H))
        Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hTn : (T.subgroupOf Lb).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hTL).mpr (barM_le_normalizer_barM hLT)
    have hq : CFSG.IsQuasisimple ↥Lb := ⟨⟨hLb.2.2.1⟩, hLb.2.2.2, a, b, hab⟩
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hTn with htop | hle
    · exfalso
      apply hLN
      intro l hl
      have hlT : mk ⟨l, hLM hl⟩ ∈ T := by
        have : (⟨mk ⟨l, hLM hl⟩, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl)⟩ :
            ↥Lb) ∈ T.subgroupOf Lb := htop ▸ Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp this
      obtain ⟨t, ht, hte⟩ := hlT
      have h1 : mk (t⁻¹ * ⟨l, hLM hl⟩) = 1 := by
        rw [map_mul, map_inv, hte, inv_mul_cancel]
      have hqN := h3.twoCore_M_le_glbPrimeCore (coe_mem_pCoreOf_two_of_mk_eq_one _ h1)
      have htN : (t : G) ∈ GLBPrimeCore 5 H := (Subgroup.mem_subgroupOf.mp ht).1
      have e1 : l = (t : G) * ((t⁻¹ * ⟨l, hLM hl⟩ : M) : G) := by simp
      rw [e1]
      exact Subgroup.mul_mem _ htN hqN
    · intro l hl
      rw [MonoidHom.mem_ker]
      change QuotientGroup.mk' _ (f₀ l) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      apply hle
      rw [Subgroup.mem_subgroupOf]
      exact ⟨⟨l, hLM l.2⟩, Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_subgroupOf.mp hl, l.2⟩, rfl⟩
  rw [← h.section_card L hLK f.ker hNV hsimple hnab]
  exact Nat.card_congr e.toEquiv.symm

theorem D1A15Data.relIndex_centralizer_dvd_five (h : D1A15Data P M H R c σ τ)
    (hB3 : StmtBlockThree) (hα : KFactThreeOrFiveDvd) (hS : CatalogOuterSolvable)
    {L : Subgroup G} (hL2 : IsTwoPrimeComponent M L) (hLK : L ≤ H ⊓ M)
    (hLN : ¬ L ≤ GLBPrimeCore 5 H) {U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hUR : U ≤ barM M R) :
    (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex U ∣ 5 := by
  have h1 := relIndex_centralizer_dvd_card
    (hUR.trans (h.le_sup_centralizer_component hB3 hα hS hL2.component))
  rw [h.card_center_quotient_eq hL2 hLK hLN] at h1
  have h2 : (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex U ∣ 5 ^ 3 :=
    (Subgroup.relIndex_dvd_card _ _).trans (h.card_barM ▸ Subgroup.card_dvd_of_le hUR)
  have h3 := Nat.dvd_gcd h1 h2
  norm_num at h3
  exact h3

end A15

end CFSG.AGLEmbedding
