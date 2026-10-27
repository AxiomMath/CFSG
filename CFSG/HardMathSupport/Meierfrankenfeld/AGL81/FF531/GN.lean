module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.Component
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710XA1
public import CFSG.Quasithin.Background.A4V

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open scoped commutatorElement

section Quot

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem isKGroup_gnQuot (hGN : GNSetting X T) : CFSG.Open.IsKGroup (X ⧸ gnC T) :=
  CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710.isKGroup_of_surjective
    (QuotientGroup.mk' (gnC T)) (QuotientGroup.mk'_surjective _)
    (fun K L _ _ hsimple _ => hGN.kGroup K (L.subgroupOf K) hsimple)

theorem le_map_sylow_of_normal (hGN : GNSetting X T) {N : Subgroup (X ⧸ gnC T)} [N.Normal]
    (hN : IsPGroup 2 N) : N ≤ T.map (QuotientGroup.mk' (gnC T)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (T.map (QuotientGroup.mk' (gnC T))) := hGN.sylow.2.1.map _
  have hidx : ¬ 2 ∣ (T.map (QuotientGroup.mk' (gnC T))).index := by
    intro h
    apply hGN.sylow.2.2
    rw [Subgroup.index_map, MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _),
      Subgroup.index_top, mul_one] at h
    have h2 : 2 ∣ T.index := h.trans (Subgroup.index_dvd_of_le le_sup_left)
    rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right]
  exact IsPGroup.le_sylow_of_normal hN (hp.toSylow hidx)

theorem pCore_two_gnQuot (hGN : GNSetting X T) : CFSG.pCore 2 (X ⧸ gnC T) = ⊥ := by
  unfold CFSG.pCore
  refine le_bot_iff.mp (sSup_le ?_)
  rintro N ⟨hN, h2⟩
  have := hN
  set P : Subgroup X := N.comap (QuotientGroup.mk' (gnC T)) with hP
  have hPn : P.Normal := Subgroup.normal_comap _
  have hNT := le_map_sylow_of_normal hGN h2
  have hdec : ∀ g ∈ P, ∃ t ∈ T, ∃ c ∈ gnC T, g = t * c := by
    intro g hg
    obtain ⟨t, ht, htg⟩ := Subgroup.mem_map.1 (hNT hg)
    refine ⟨t, ht, t⁻¹ * g, ?_, by group⟩
    rw [← QuotientGroup.eq]
    exact htg
  have hZ : (omegaOneCenterOf T : Set X) ⊆ (Subgroup.centralizer (P : Set X) : Subgroup X) := by
    intro z hz g hg
    obtain ⟨t, ht, c, hc, rfl⟩ := hdec g hg
    have hzV : z ∈ gnV T := Subgroup.subset_normalClosure hz
    have h1 : t * z = z * t :=
      Subgroup.mem_centralizer_iff.1
        (A4.centerOf_le_centralizer T (A4.omegaOneCenterOf_le_centerOf T hz)) t ht
    have h2 : z * c = c * z := Subgroup.mem_centralizer_iff.1 hc z hzV
    calc t * c * z = t * (c * z) := by group
      _ = t * (z * c) := by rw [h2]
      _ = (t * z) * c := by group
      _ = (z * t) * c := by rw [h1]
      _ = z * (t * c) := by group
  have hcn : (Subgroup.centralizer (P : Set X)).Normal := by
    refine ⟨fun n hn g' => ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hn ⊢
    intro h hh
    have := hn (g'⁻¹ * h * g') (by simpa using hPn.conj_mem h hh g'⁻¹)
    calc h * (g' * n * g'⁻¹) = g' * ((g'⁻¹ * h * g') * n) * g'⁻¹ := by group
      _ = g' * (n * (g'⁻¹ * h * g')) * g'⁻¹ := by rw [this]
      _ = (g' * n * g'⁻¹) * h := by group
  have hV : gnV T ≤ Subgroup.centralizer (P : Set X) :=
    Subgroup.normalClosure_le_normal hZ
  intro n hn
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective n
  have hgP : g ∈ P := hn
  have hgC : g ∈ gnC T := by
    unfold gnC
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.1 (hV hv) g hgP).symm
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff g).2 hgC

end Quot

theorem gn_ffConclusion (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem)
    (X : Type) [Group X] [Finite X] (T : Subgroup X) (hGN : GNSetting X T)
    (L : Subgroup (X ⧸ gnC T)) (hL : IsComponentOf L ⊤) (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.FFConclusion (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨W, _, _, _, ρ, hρ, A, hAel, hAbest, -, hLA⟩ := exists_rep_offender X T hGN L hL hJ
  have hLbot : L ≠ ⊥ := by
    intro h
    have hs : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2.2.2
    subst h
    have : Nontrivial (↥(⊥ : Subgroup (X ⧸ gnC T)) ⧸ Subgroup.center ↥(⊥ : Subgroup (X ⧸ gnC T))) :=
      hs.toNontrivial
    obtain ⟨x, y, hxy⟩ := exists_pair_ne
      (↥(⊥ : Subgroup (X ⧸ gnC T)) ⧸ Subgroup.center ↥(⊥ : Subgroup (X ⧸ gnC T)))
    induction x using QuotientGroup.induction_on with
    | _ a =>
      induction y using QuotientGroup.induction_on with
      | _ b => exact hxy (congrArg QuotientGroup.mk (Subsingleton.elim a b))
  exact ffConclusion_of_component hFF (X ⧸ gnC T) W ρ hρ (isKGroup_gnQuot hGN)
    (pCore_two_gnQuot hGN) A hAel hAbest L hL (by rw [hLA]; exact hLbot)

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531
