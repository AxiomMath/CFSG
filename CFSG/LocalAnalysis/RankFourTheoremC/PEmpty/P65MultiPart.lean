module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62Main
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BStruct
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BTransport
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BMoved
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65MultiLift
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65MultiCoord
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65MultiPair
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplitKer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65M

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.Lemma213 (cjComp conj_mem_layer)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplit (SplitCfg compKer compKer_le_layer
  card_le_sq_of_not_le card_le_comp)

theorem pRank_le_normalizer_of_beta (hβ : KFactBetaStructure) {p f : ℕ} (hf : f.Prime)
    (hfp : f ≠ p) {X : Type} [Group X] [Finite X] {P : Sylow p X} {x z : X}
    (hpl : Plane63 p X P x z)
    (hcomp : ∃ L K : Subgroup (X ⧸ primeComplementCore (G := X) p),
      IsComponentOf L ⊤ ∧ IsComponentOf K ⊤ ∧ L ≠ K)
    {T : Subgroup X} (hT : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) ⊤ T) :
    Open.pRank p (P : Subgroup X) ≤ Open.pRank p (normalizer (T : Set X)) := by
  have hβs := hβ p X P x z hpl hcomp
  have hp := hpl.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set D : Subgroup X := primeComplementCore (G := X) p with hD
  have hD3 : ¬ p ∣ Nat.card D :=
    (Nat.Prime.coprime_iff_not_dvd hp).mp (primeComplementCore_coprime p)
  have hB : IsPGroup p (zpowers x ⊔ zpowers z : Subgroup X) :=
    IsPGroup.of_card (n := 2) hpl.plane.card_eq
  have hxB : x ∈ (zpowers x ⊔ zpowers z : Subgroup X) := Subgroup.mem_sup_left (mem_zpowers x)
  have hzB : z ∈ (zpowers x ⊔ zpowers z : Subgroup X) := Subgroup.mem_sup_right (mem_zpowers z)
  have hxp : x ^ p = 1 := hpl.plane.isElemAbelian.2 x hxB
  have hzp : z ^ p = 1 := hpl.plane.isElemAbelian.2 z hzB
  have hxz : x * z = z * x := by
    have := hpl.plane.isElemAbelian.1.is_comm.comm (⟨x, hxB⟩ : ↥(zpowers x ⊔ zpowers z))
      ⟨z, hzB⟩
    exact congrArg Subtype.val this
  have hz1 : z ≠ 1 := by
    intro h
    have h1 : (zpowers x ⊔ zpowers z : Subgroup X) = zpowers x := by
      rw [h, zpowers_one_eq_bot, sup_bot_eq]
    have h2 : Nat.card (zpowers x) ≤ p := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hxp)
    have h3 := hpl.plane.card_eq
    rw [h1] at h3
    have h4 : p ^ 2 ≤ p := h3 ▸ h2
    have h5 : 1 < p := hp.one_lt
    nlinarith
  have hzb1 : (z : X ⧸ D) ≠ 1 := by
    intro h
    have hzD : z ∈ D := (QuotientGroup.eq_one_iff z).mp h
    have hord : orderOf z = p := orderOf_eq_prime hzp hz1
    apply hD3
    rw [← hord, ← Subgroup.orderOf_mk z hzD]
    exact orderOf_dvd_natCard _
  have hxzb : (x : X ⧸ D) * (z : X ⧸ D) = (z : X ⧸ D) * (x : X ⧸ D) := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxz]
  have hzpb : (z : X ⧸ D) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hzp, QuotientGroup.mk_one]
  have hT' := isMaxFInvariantIn_map hp hf hfp hD3 hB hT
  have hBmap : (zpowers x ⊔ zpowers z : Subgroup X).map (QuotientGroup.mk' D) =
      zpowers (x : X ⧸ D) ⊔ zpowers (z : X ⧸ D) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  rw [hBmap] at hT'
  have hZ := hβs.centreless
  have hzL := hβs.z_mem_layer
  have hne := K62.π_ne_one hZ hxzb hzb1 hzL hβs.transitive
  have hN := zcoord_mem_normalizer hZ hp hf hfp hxzb hzL hβs.card_components hβs.transitive hT'
  obtain ⟨W, hWe, hWc, hWT⟩ := K62.exists_elemAbelian_of_coords hZ hp hzpb hzL hne hN
  rw [hβs.card_components] at hWc
  have hk := le_pRank_normalizer hp hf hfp hD3 hB hT hWe hWc hWT
  exact hβs.pRank_le.trans hk

theorem exists_pair_of_plane63 (h64 : KFactCenterCyclicGeFive) (h610 : GL83.I_6_10_1)
    (h7131 : GL83.I_7_13_1) (hsplit : KFactSylowSplit) {p : ℕ} {X : Type} [Group X] [Finite X]
    {P : Sylow p X} {x z : X} (hpl : Plane63 p X P x z)
    (hcomp : ∃ L K : Subgroup (X ⧸ primeComplementCore (G := X) p),
      IsComponentOf L ⊤ ∧ IsComponentOf K ⊤ ∧ L ≠ K)
    {E : Subgroup X} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ p) :
    ∃ a ∈ E, a ≠ 1 ∧ ∃ b ∈ E, b ≠ 1 ∧ ∀ g : X, g * a * g⁻¹ ∉ zpowers b := by
  have hcfg := cfg_of_plane63 hpl
  have hprime := hpl.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  set D : Subgroup X := primeComplementCore (G := X) p with hD
  set π : X →* X ⧸ D := QuotientGroup.mk' D with hπ
  obtain ⟨L, K, hL, hK, hLK⟩ := hcomp
  have hcomp' : ∃ C C' : ComponentIndex (X ⧸ D), C ≠ C' :=
    ⟨⟨L, (CFSG.isComponent_iff_open L).2 hL⟩, ⟨K, (CFSG.isComponent_iff_open K).2 hK⟩,
      fun h => hLK (congrArg Subtype.val h)⟩
  obtain ⟨-, hcyc, hZ, hcard, htrans, -, hC⟩ :=
    hcfg.struct h64 h610 (fun C hC => hcfg.isCyclic_inf_of_moved h64 hC) hcomp'
  have hSplit : SplitCfg p ((P : Subgroup X).map π) (x : X ⧸ D) :=
    ⟨hprime, hpl.five_le, hcfg.sylow, hcfg.x_mem, hcfg.x_pow,
      fun E hE hEe hxE => hcfg.card_le_of_normalizes hE hEe hxE, hcfg.catalog, hcard, hZ, htrans,
      hcyc, hC, fun C => hcfg.dvd_card_comp C⟩
  have hl := compKer_le_layer hsplit h7131 hSplit
  have hEp : IsPGroup p E := hE.isPGroup
  have hEm : IsElemAbelian p (E.map π) := by
    haveI := hE.1
    refine ⟨inferInstance, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    show (π e) ^ p = 1
    rw [← map_pow, hE.2 e he, map_one]
  have hEmc : Nat.card (E.map π) = p ^ p := by rw [card_map_mk_eq hprime hEp, hEc]
  let Q0 : Sylow p (X ⧸ D) := P.mapSurjective (QuotientGroup.mk'_surjective D)
  have hQ0 : (Q0 : Subgroup (X ⧸ D)) = (P : Subgroup X).map π := Sylow.coe_mapSurjective _ _
  obtain ⟨y, hy⟩ := exists_conj_le_sylow Q0 (E.map π) hEm.isPGroup
  have hy' : (E.map π).map (MulAut.conj y).toMonoidHom ≤ (P : Subgroup X).map π := hQ0 ▸ hy
  have hE₀e : IsElemAbelian p ((E.map π).map (MulAut.conj y).toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hEm _
  have hE₀c : Nat.card ((E.map π).map (MulAut.conj y).toMonoidHom) = p ^ p := by
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, hEmc]
  have hE₀Q : (E.map π).map (MulAut.conj y).toMonoidHom ≤ compKer ((P : Subgroup X).map π) := by
    intro e he
    by_contra hne
    have h1 := card_le_sq_of_not_le hSplit hl hy' hE₀e he hne
    rw [hE₀c] at h1
    have h5 := hpl.five_le
    have h6 : p * p < p ^ p := by
      calc p * p = p ^ 2 := (sq p).symm
        _ < p ^ p := Nat.pow_lt_pow_right hprime.one_lt (by omega)
    omega
  have hEl : E.map π ≤ layer (X ⧸ D) := by
    intro e he
    have he' : y * e * y⁻¹ ∈ (E.map π).map (MulAut.conj y).toMonoidHom := ⟨e, he, rfl⟩
    have h2 := conj_mem_layer y⁻¹ (hl (hE₀Q he'))
    simpa [mul_assoc] using h2
  obtain ⟨u, hu, hu1, v, hv, hv1, hg⟩ := exists_pair_of_layer hprime hZ hcard
    (fun C F hFC hF => card_le_comp hSplit C hFC hF) hEm hEmc hEl
  obtain ⟨a, haE, rfl⟩ := hu
  obtain ⟨b, hbE, rfl⟩ := hv
  refine ⟨a, haE, fun h => hu1 (by rw [h, map_one]), b, hbE, fun h => hv1 (by rw [h, map_one]),
    fun g hgb => hg (π g) ?_⟩
  have := Subgroup.mem_map_of_mem π hgb
  rw [MonoidHom.map_zpowers] at this
  simpa using this

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65M
