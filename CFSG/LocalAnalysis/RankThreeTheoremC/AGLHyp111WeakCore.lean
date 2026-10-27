module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config
import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJ
import CFSG.Goldschmidt.Steps.Sec82e

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

theorem sylow_le_of_glbWeakCore_le {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M D : Subgroup G}
    (hcore : GLBWeakCore p (P : Subgroup G) ≤ M) (h3 : 3 ≤ Open.pRank p D) :
    (P : Subgroup G) ≤ M := by
  have hp := (Fact.out : p.Prime)
  have hPrank : 3 ≤ Open.pRank p (P : Subgroup G) := by
    rw [pRank_sylow_eq_globalRank p hp P]
    exact h3.trans (pRank_mono p hp le_top)
  exact (subgroup_le_weakCore_of_rank p hp _ hPrank).trans hcore

theorem exists_mem_le_smul_sylow {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M A : Subgroup G}
    (hPM : (P : Subgroup G) ≤ M) (hA : IsPGroup p A) (hAM : A ≤ M) :
    ∃ m ∈ M, A ≤ ((m • P : Sylow p G) : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := (hA.comap_subtype (K := M)).exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M (P.subtype hPM) Q
  refine ⟨m, m.2, fun a ha => ?_⟩
  have haQ : (⟨a, hAM ha⟩ : M) ∈ (Q : Subgroup M) := hQ ha
  rw [← hm, Sylow.smul_subtype, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at haQ
  exact haQ

namespace Hyp111

theorem normalizer_le_of_three {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M D : Subgroup G}
    (hcore : GLBWeakCore p (P : Subgroup G) ≤ M) (hDM : D ≤ M) (hD : IsPGroup p D)
    (h3 : 3 ≤ Open.pRank p D) : Subgroup.normalizer (D : Set G) ≤ M := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨m, hm, hDm⟩ :=
    exists_mem_le_smul_sylow (sylow_le_of_glbWeakCore_le hcore h3) hD hDM
  exact (normalizer_le_weakCore p hDm (by omega)
    (h3.trans (pRank_mono p hp le_sup_left))).trans (glbWeakCore_smul_le hp hcore hm)

theorem normalizer_le_of_central {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M D : Subgroup G}
    {z : G} (hcore : GLBWeakCore p (P : Subgroup G) ≤ M) (hDM : D ≤ M) (hD : IsPGroup p D)
    (h2 : 2 ≤ Open.pRank p D) (hzM : z ∈ M) (hz : orderOf z = p) (hzD : z ∉ D)
    (hzc : ∀ d ∈ D, z * d = d * z) : Subgroup.normalizer (D : Set G) ≤ M := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨E, hED, hE, hEc⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank hp h2
  have hzp : z ^ p = 1 := hz ▸ pow_orderOf_eq_one z
  obtain ⟨hEz, hEzc⟩ := CFSG.Goldschmidt.Sec82.isElemAbelian_sup_zpowers hp hEc hE.2 hzp
    (fun h => hzD (hED h)) (fun e he => (hzc e (hED he)).symm)
  have hEz3 : 3 ≤ Open.pRank p (E ⊔ Subgroup.zpowers z) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_rfl hEz hEzc
  have hzC : z ∈ Subgroup.centralizer (D : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun d hd => (hzc d hd).symm
  have hzN : Subgroup.zpowers z ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.zpowers_le).mpr (Subgroup.centralizer_le_normalizer _ hzC)
  have hZp : IsPGroup p (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  have hDZ : IsPGroup p (D ⊔ Subgroup.zpowers z : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hD hZp hzN
  obtain ⟨m, hm, hDZm⟩ := exists_mem_le_smul_sylow
    (sylow_le_of_glbWeakCore_le hcore hEz3) hDZ (sup_le hDM ((Subgroup.zpowers_le).mpr hzM))
  have hDm : D ≤ ((m • P : Sylow p G) : Subgroup G) := le_sup_left.trans hDZm
  have hzm : z ∈ ((m • P : Sylow p G) : Subgroup G) :=
    hDZm (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hle : E ⊔ Subgroup.zpowers z ≤
      D ⊔ (((m • P : Sylow p G) : Subgroup G) ⊓ Subgroup.centralizer (D : Set G)) :=
    sup_le (hED.trans le_sup_left) ((Subgroup.zpowers_le).mpr (Subgroup.mem_sup_right ⟨hzm, hzC⟩))
  exact (normalizer_le_weakCore p hDm h2 (hEz3.trans (pRank_mono p hp hle))).trans
    (glbWeakCore_smul_le hp hcore hm)

theorem conj_mem_centralizer_of_mem_normalizer {D : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (D : Set G)) (hx : x ∈ Subgroup.centralizer (D : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro d hd
  have hd' : g⁻¹ * d * g ∈ D := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) d).mp hd
    simpa using this
  have hc := hx _ hd'
  calc d * (g * x * g⁻¹) = g * ((g⁻¹ * d * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * d * g)) * g⁻¹ := by rw [hc]
    _ = g * x * g⁻¹ * d := by group

theorem normalizer_le_of_centralizer {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M D : Subgroup G}
    (hcore : GLBWeakCore p (P : Subgroup G) ≤ M) (hC : Subgroup.centralizer (D : Set G) ≤ M)
    (h3 : 3 ≤ Open.pRank p (Subgroup.centralizer (D : Set G))) :
    Subgroup.normalizer (D : Set G) ≤ M := by
  have hp := (Fact.out : p.Prime)
  set C := Subgroup.centralizer (D : Set G) with hCdef
  obtain ⟨E, hEC, hE, hEcard⟩ := pRank_attained p hp C
  have hEp : IsPGroup p E := IsPGroup.of_card hEcard
  obtain ⟨S, hS⟩ := (hEp.comap_subtype (K := C)).exists_le_sylow
  set R : Subgroup G := (S : Subgroup C).map C.subtype with hRdef
  have hER : E ≤ R := fun e he => ⟨⟨e, hEC he⟩, hS he, rfl⟩
  have hR3 : 3 ≤ Open.pRank p R :=
    h3.trans ((CFSG.SectionRank.le_pRank hp.one_lt le_rfl hE hEcard).trans (pRank_mono p hp hER))
  have hNR : Subgroup.normalizer (R : Set G) ≤ M :=
    normalizer_le_of_three hcore ((Subgroup.map_subtype_le _).trans hC) (S.isPGroup'.map _) hR3
  intro g hg
  let σ : MulAut C :=
    { toFun := fun c => ⟨g * c * g⁻¹, conj_mem_centralizer_of_mem_normalizer hg c.2⟩
      invFun := fun c => ⟨g⁻¹ * c * g, by
        simpa using conj_mem_centralizer_of_mem_normalizer (Subgroup.inv_mem _ hg) c.2⟩
      left_inv := fun c => Subtype.ext (by simp [mul_assoc])
      right_inv := fun c => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C (σ • S) S
  have hcg : (c : G) * g ∈ Subgroup.normalizer (R : Set G) := by
    apply mem_normalizer_of_conj_mem
    rintro _ ⟨s, hs, rfl⟩
    have h1 : σ • s ∈ ((σ • S : Sylow p C) : Subgroup C) :=
      Subgroup.smul_mem_pointwise_smul s σ _ hs
    have h2 : c * (σ • s) * c⁻¹ ∈ (S : Subgroup C) := by
      rw [← hc, Sylow.coe_subgroup_smul]
      exact ⟨σ • s, h1, rfl⟩
    refine ⟨_, h2, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
    change (c : G) * (g * s * g⁻¹) * (c : G)⁻¹ = (c : G) * g * s * ((c : G) * g)⁻¹
    group
  have := M.mul_mem (M.inv_mem (hC c.2)) (hNR hcg)
  simpa using this

theorem isSylow_of_inter {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M Y : Subgroup G}
    (hcore : GLBWeakCore p (P : Subgroup G) ≤ M)
    (h3 : 3 ≤ Open.pRank p (Y ⊓ M : Subgroup G)) (W : Sylow p ↥(Y ⊓ M : Subgroup G)) :
    ∃ W' : Sylow p ↥Y, (W'.1.map Y.subtype) = W.1.map (Y ⊓ M : Subgroup G).subtype := by
  have hp := (Fact.out : p.Prime)
  set R : Subgroup G := W.1.map (Y ⊓ M : Subgroup G).subtype with hRdef
  have hRYM : R ≤ Y ⊓ M := Subgroup.map_subtype_le _
  have hRp : IsPGroup p R := W.isPGroup'.map _
  have hR3 : 3 ≤ Open.pRank p R := by
    obtain ⟨E, hEYM, hE, hEcard⟩ := pRank_attained p hp (Y ⊓ M)
    have hEtop : Open.pRank p (Y ⊓ M) ≤ Open.pRank p (⊤ : Subgroup ↥(Y ⊓ M : Subgroup G)) := by
      have := hE.1
      refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt
        (fun a b => mul_comm' a b) (fun a => Subtype.ext (hE.2 a a.2)) hEcard
        (Subgroup.inclusion hEYM) (Subgroup.inclusion_injective hEYM) le_top
    have hW := pRank_sylow_eq_globalRank p hp W
    exact h3.trans (hEtop.trans (hW ▸ CFSG.SectionRank.pRank_le_map hp.one_lt _
      (Subgroup.subtype_injective _) _))
  have hNR : Subgroup.normalizer (R : Set G) ≤ M :=
    normalizer_le_of_three hcore (hRYM.trans inf_le_right) hRp hR3
  obtain ⟨T, hT⟩ := (hRp.comap_subtype (K := Y)).exists_le_sylow
  refine ⟨T, le_antisymm ?_ ?_⟩
  · by_contra hne
    have hRT : R ≤ T.1.map Y.subtype := by
      intro r hr
      exact ⟨⟨r, (hRYM hr).1⟩, hT hr, rfl⟩
    have hTp : IsPGroup p (T.1.map Y.subtype) := T.isPGroup'.map _
    obtain ⟨x, hxT, hxR, hxN⟩ := exists_mem_normalizer_not_mem_of_lt_of_isPGroup hTp
      (lt_of_le_of_ne hRT (Ne.symm (fun h => hne h.le)))
    have hxYM : x ∈ Y ⊓ M := ⟨Subgroup.map_subtype_le _ hxT, hNR hxN⟩
    have hRx : IsPGroup p (R ⊔ Subgroup.zpowers x : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hRp (hTp.to_le ((Subgroup.zpowers_le).mpr hxT))
        ((Subgroup.zpowers_le).mpr hxN)
    have hle : R ⊔ Subgroup.zpowers x ≤ Y ⊓ M := sup_le hRYM ((Subgroup.zpowers_le).mpr hxYM)
    have hmax := W.3 (hRx.comap_subtype (K := Y ⊓ M)) (by
      intro w hw
      exact Subgroup.mem_comap.mpr (Subgroup.mem_sup_left ⟨w, hw, rfl⟩))
    apply hxR
    have hx' : (⟨x, hxYM⟩ : ↥(Y ⊓ M : Subgroup G)) ∈ W.1 := by
      rw [← hmax]
      exact Subgroup.mem_comap.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
    exact ⟨_, hx', rfl⟩
  · intro r hr
    exact ⟨⟨r, (hRYM hr).1⟩, hT hr, rfl⟩

theorem gammaOne_le_of_centralizers {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M E : Subgroup G}
    {z : G} (hcore : GLBWeakCore p (P : Subgroup G) ≤ M) (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ 2) (hz : orderOf z = p) (hzE : z ∉ E)
    (hzc : ∀ e ∈ E, z * e = e * z)
    (hcent : ∀ a ∈ E, a ≠ 1 → Subgroup.centralizer ({a} : Set G) ≤ M) :
    rankThreeGamma 1 p E ≤ M := by
  have hp := (Fact.out : p.Prime)
  have hzp : z ^ p = 1 := hz ▸ pow_orderOf_eq_one z
  obtain ⟨hEz, hEzc⟩ := CFSG.Goldschmidt.Sec82.isElemAbelian_sup_zpowers hp hEcard hE.2 hzp hzE
    (fun e he => (hzc e he).symm)
  have hEz3 : 3 ≤ Open.pRank p (E ⊔ Subgroup.zpowers z) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_rfl hEz hEzc
  unfold rankThreeGamma GLBCore
  refine sSup_le ?_
  rintro _ ⟨X, hXE, hX1, rfl⟩
  have hXne : X ≠ ⊥ := by
    rintro rfl
    have h0 : Open.pRank p (⊥ : Subgroup G) ≤ 0 :=
      CFSG.SectionRank.pRank_le hp.one_lt fun F hF _ => by
        rw [le_bot_iff.mp hF, Subgroup.card_bot]
        simp
    omega
  obtain ⟨⟨a, haX⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hCX : Subgroup.centralizer (X : Set G) ≤ M :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haX)).trans (hcent a (hXE haX) ha1')
  have hEzC : E ⊔ Subgroup.zpowers z ≤ Subgroup.centralizer (X : Set G) := by
    refine sup_le (fun e he => Subgroup.mem_centralizer_iff.mpr fun x hx => ?_) ?_
    · exact congrArg Subtype.val (isMulCommutative_iff.mp hE.1 ⟨x, hXE hx⟩ ⟨e, he⟩)
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      exact fun x hx => (hzc x (hXE hx)).symm
  exact normalizer_le_of_centralizer hcore hCX (hEz3.trans (pRank_mono p hp hEzC))

theorem isAGLQ_of_centralizers {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M Q E : Subgroup G}
    {z : G} (hcore : GLBWeakCore p (P : Subgroup G) ≤ M) (hQM : Q ≤ M) (hQ : IsPGroup p Q)
    (hEQ : E ≤ Q) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2) (hz : orderOf z = p)
    (hzE : z ∉ E) (hzc : ∀ e ∈ E, z * e = e * z)
    (hcent : ∀ a ∈ E, a ≠ 1 → Subgroup.centralizer ({a} : Set G) ≤ M) :
    IsAGLQ p M Q :=
  ⟨hQM, hQ, Or.inr ⟨E, hEQ, hE, hEcard,
    gammaOne_le_of_centralizers hcore hE hEcard hz hzE hzc hcent⟩⟩

end Hyp111

end CFSG.LocalAnalysis.RankThreeTheoremC
