module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeStepsAt
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeStepsRank
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineOneThreeProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111SizeMax
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylowIn_of_isAGLQ {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {B N : Subgroup G} (hB : IsAGLQ p M B) (hBN : B ≤ N) :
    ∃ R : Subgroup G, B ≤ R ∧ R ≤ M ∧ CFSG.Quasithin.IsSylowIn p R N ∧
      Subgroup.normalizer (R : Set G) ≤ M := by
  haveI : Fact p.Prime := ⟨he.prime⟩
  obtain ⟨R, hR, hBR⟩ := CFSG.Quasithin.exists_isSylowIn_ge p (le_inf hBN hB.1) hB.2.1
  have hRM : R ≤ M := hR.le.trans inf_le_right
  have hNR := normalizer_le_of_isAGLQ_escape he (isAGLQ_of_le hB hBR hRM hR.isPGroup)
  exact ⟨R, hBR, hRM, isSylowIn_of_isSylowIn_inf hR hNR, hNR⟩

theorem exists_sylow_d1X0_of_escape {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {B N : Subgroup G} (hB : IsAGLQ p M B) (hBN : B ≤ N) :
    ∃ Rb : Sylow p (N ⧸ primeComplementCore (G := N) p),
      (Rb : Subgroup (N ⧸ primeComplementCore (G := N) p)) ≤ d1X0 p M N ∧
      Subgroup.normalizer ((Rb : Subgroup (N ⧸ primeComplementCore (G := N) p)) :
        Set (N ⧸ primeComplementCore (G := N) p)) ≤ d1X0 p M N ∧
      (∀ A : Subgroup (N ⧸ primeComplementCore (G := N) p),
        A ≤ (Rb : Subgroup (N ⧸ primeComplementCore (G := N) p)) → IsElemAbelian p A →
        Nat.card A = p ^ 2 →
        3 ≤ CFSG.Open.pRank p ((Rb : Subgroup (N ⧸ primeComplementCore (G := N) p)) ⊓
          Subgroup.centralizer (A : Set (N ⧸ primeComplementCore (G := N) p))) →
        Subgroup.centralizer (A : Set (N ⧸ primeComplementCore (G := N) p)) ≤ d1X0 p M N) ∧
      ∀ L : Subgroup (N ⧸ primeComplementCore (G := N) p), IsComponentOf L ⊤ →
        ∃ u ∈ (Rb : Subgroup (N ⧸ primeComplementCore (G := N) p)), u ∈ L ∧ orderOf u = p ∧
          ∃ c ∈ L, u * c ≠ c * u := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set O := primeComplementCore (G := N) p
  set π := QuotientGroup.mk' O with hπ
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  obtain ⟨R, -, hRM, hR, hNR⟩ := exists_isSylowIn_of_isAGLQ he hB hBN
  have hRp : IsPGroup p (R.subgroupOf N) :=
    hR.isPGroup.comap_of_injective N.subtype N.subtype_injective
  set Rb : Sylow p (N ⧸ O) := hR.toSylow.mapSurjective (QuotientGroup.mk'_surjective O) with hRb
  have hRbeq : (Rb : Subgroup (N ⧸ O)) = (R.subgroupOf N).map π := by
    rw [hRb, Sylow.coe_mapSurjective, CFSG.Quasithin.IsSylowIn.coe_toSylow]
  refine ⟨Rb, ?_, ?_, ?_, ?_⟩
  · rw [hRbeq]
    exact Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr ⟨x.2, hRM (Subgroup.mem_subgroupOf.mp hx)⟩
  ·
    rw [hRbeq]
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O x
    have hy : y ∈ ((O ⊔ Subgroup.normalizer ((R.subgroupOf N : Subgroup N) : Set N) :
        Subgroup N) : Set N) := comap_normalizer_map_le_sup hp O hO hRp hx
    rw [Subgroup.normal_mul, Set.mem_mul] at hy
    obtain ⟨o, ho, n, hn, rfl⟩ := hy
    have ho1 : π o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    refine ⟨n, Subgroup.mem_subgroupOf.mpr ⟨n.2, hNR ?_⟩, by rw [map_mul, ho1, one_mul]⟩
    apply Subgroup.mem_normalizer_fintype
    intro r hr
    have := (Subgroup.mem_normalizer_iff.mp hn ⟨r, hR.le hr⟩).mp (Subgroup.mem_subgroupOf.mpr hr)
    exact Subgroup.mem_subgroupOf.mp this
  · rw [hRbeq]
    exact fun A hA hAe hAc h3 =>
      centralizer_le_d1X0_of_escape he hR.le hRM hR.isPGroup A hA hAe hAc h3
  · intro L hL
    obtain ⟨t, ⟨htR, htL⟩, htp, htc⟩ :=
      exists_mem_sylow_inf_component hp he.ne_two (primeComplementCore_quotient_eq_bot p) Rb hL
    refine ⟨t, htR, htL, htp, ?_⟩
    by_contra hall
    push Not at hall
    exact htc (Subgroup.mem_centralizer_iff.mpr fun c hc => (hall c hc).symm)

theorem d1KBar_normal_of_escape {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {B N : Subgroup G} (hB : IsAGLQ p M B) (hBN : B ≤ N)
    (hK : d1KBar p M N ≠ ⊥) : (d1KBar p M N).Normal := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Rb, hRX₀, hNR, hC, hu⟩ := exists_sylow_d1X0_of_escape he hB hBN
  obtain ⟨L₀, hL₀, hL₀X⟩ := exists_component_of_d1KBar_ne_bot hK
  exact normal_sup_components_of_sylow Rb hNR
    (le_normalizer_all_components hp he.ne_two Rb.isPGroup' hRX₀ hC hu hL₀ hL₀X)

theorem pRank_d1PlusCore_le_one_of_escape {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {B N : Subgroup G} (hB : IsAGLQ p M B) (hBN : B ≤ N)
    (hK : d1KBar p M N ≠ ⊥) : CFSG.Open.pRank p (d1PlusCore p N (d1KBar p M N)) ≤ 1 := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set O := primeComplementCore (G := N) p
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  obtain ⟨Rb, -, -, hC, hu⟩ := exists_sylow_d1X0_of_escape he hB hBN
  obtain ⟨L₀, hL₀, hL₀X⟩ := exists_component_of_d1KBar_ne_bot hK
  haveI := d1KBar_normal_of_escape he hB hBN hK
  set C := Subgroup.centralizer ((d1KBar p M N : Subgroup (N ⧸ O)) : Set (N ⧸ O)) with hCdef
  have hCn : C.Normal := inferInstance
  obtain ⟨u, huR, huL, hup, hunc⟩ := hu L₀ hL₀
  have hS7 := pRank_inf_centralizer_component_le_one hp hC hL₀X huR huL hup hunc
  have hCL₀ : C ≤ Subgroup.centralizer (L₀ : Set (N ⧸ O)) :=
    Subgroup.centralizer_le (le_d1KBar hL₀ hL₀X)
  have hCrank : CFSG.Open.pRank p C ≤ 1 := by
    refine CFSG.SectionRank.pRank_le hp.one_lt fun E hEC hE => ?_
    have hEp : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE
    obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (N ⧸ O) Rb Q
    have hSg : ((g • Rb : Sylow p (N ⧸ O)) : Subgroup (N ⧸ O)) =
        (Rb : Subgroup (N ⧸ O)).map (MulAut.conj g).toMonoidHom := by
      rw [Sylow.coe_subgroup_smul]; rfl
    set E' := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'
    have hE'R : E' ≤ Rb := by
      rintro _ ⟨x, hx, rfl⟩
      have hxQ : x ∈ (Q : Subgroup (N ⧸ O)) := hEQ hx
      rw [← hg, hSg] at hxQ
      obtain ⟨y, hy, rfl⟩ := hxQ
      have hy' : y ∈ (Rb : Subgroup (N ⧸ O)) := hy
      simpa [MulAut.conj_apply, mul_assoc] using hy'
    have hE'C : E' ≤ C := by
      rintro _ ⟨x, hx, rfl⟩
      have h := hCn.conj_mem x (hEC hx) g⁻¹
      rw [inv_inv] at h
      simpa [MulAut.conj_apply] using h
    have hcard : Nat.card E' = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
    have hE'e : IsElemAbelian p E' :=
      CFSG.SectionRank.isElemAbelian_map hE (MulAut.conj g⁻¹).toMonoidHom
    have hk1 : k ≤ 1 :=
      (CFSG.SectionRank.le_pRank hp.one_lt (le_inf hE'R (hE'C.trans hCL₀)) hE'e
        (hcard.trans hk)).trans hS7
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos hk1
  have e1 : CFSG.Open.pRank p (d1PlusCore p N (d1KBar p M N)) = CFSG.Open.pRank p C := by
    unfold d1PlusCore
    rw [← pRank_map_mk_eq_pRank_map_subtype hp O hO,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O)]
  rw [e1]
  exact hCrank

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
