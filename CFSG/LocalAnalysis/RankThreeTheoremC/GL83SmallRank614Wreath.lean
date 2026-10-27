module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627WreathR

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

local notation "W₃" => Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)

omit [Finite G] in
private theorem wreath614_card_eq_eighty_one {P : Subgroup G} (e : P ≃* W₃) :
    Nat.card P = 81 := by
  rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card, wreath_card_zmod_three]
  norm_num

omit [Finite G] in
private theorem wreath614_exists_isElemAbelian_card_twentySeven {P : Subgroup G}
    (e : P ≃* W₃) : ∃ V : Subgroup G, V ≤ P ∧ IsElemAbelian 3 V ∧ Nat.card V = 27 := by
  let ι : W₃ →* G := P.subtype.comp e.symm.toMonoidHom
  have hιinj : Function.Injective ι := P.subtype_injective.comp e.symm.injective
  have hιP : ∀ w, ι w ∈ P := fun w => (e.symm w).2
  let A₀ : Subgroup W₃ := (RegularWreathProduct.rightHom :
    Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3) →* Multiplicative (ZMod 3)).ker
  have hA₀c : IsMulCommutative A₀ := wreath_ker_isElemAbelian.1
  refine ⟨A₀.map ι, ?_, ⟨Subgroup.map_isMulCommutative A₀ ι, ?_⟩, ?_⟩
  · rintro _ ⟨a, _, rfl⟩
    exact hιP a
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, wreath_ker_isElemAbelian.2 a ha, map_one]
  · exact (Subgroup.card_map_of_injective hιinj).trans wreath_card_ker

private theorem wreath614_centralizer_le (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hsit : SmallRankSituation G 3 P M) {V : Subgroup G} (hVP : V ≤ (P : Subgroup G))
    (hV : IsElemAbelian 3 V) (hVc : Nat.card V = 27) {y : G} (hyV : y ∈ V) (hy1 : y ≠ 1) :
    centralizer ({y} : Set G) ≤ M := by
  have hPM := (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  by_contra hCM
  have hVcomm : IsMulCommutative V := hV.1
  have hVC : V ≤ centralizer ({y} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (setLike_mul_comm ha hyV)
  refine hsit.largeObstruction_empty y ⟨hPM (hVP hyV), hy1, hV.2 y hyV, ?_, hCM⟩
  unfold CFSG.Open.pRank
  exact le_csSup (pRank_set_bddAbove 3 (by norm_num) _) ⟨V, hVC, hV, by rw [hVc]; norm_num⟩

theorem exists_noncyclic_le_of_twentySeven_le_card (hS : Setting G) (hU0 : FullCoreLocal G)
    {P : Sylow 3 G} {M : Subgroup G} (hsit : SmallRankSituation G 3 P M)
    (e : (P : Subgroup G) ≃* W₃) {Y : Subgroup G} (hYP : Y ≤ (P : Subgroup G))
    (hY : 27 ≤ Nat.card Y) :
    ∃ R : Subgroup G, R ≤ Y ∧ IsPGroup 3 R ∧ ¬ IsCyclic R ∧ rankThreeGamma 1 3 R ≤ M := by
  obtain ⟨V, hVP, hV, hVc⟩ := wreath614_exists_isElemAbelian_card_twentySeven e
  have hPc : Nat.card (P : Subgroup G) = 81 := wreath614_card_eq_eighty_one e
  have hYP' := Subgroup.relIndex_mul_card (H := Y) (K := (P : Subgroup G))
  rw [inf_eq_left.mpr hYP, hPc] at hYP'
  have hYr : Y.relIndex P ≤ 3 := by
    by_contra hlt
    push Not at hlt
    nlinarith
  have hVP' := Subgroup.relIndex_mul_card (H := V) (K := (P : Subgroup G))
  rw [inf_eq_left.mpr hVP, hVc, hPc] at hVP'
  have hVr : V.relIndex P = 3 := by omega
  have hRP : V ⊓ Y ≤ P := inf_le_left.trans hVP
  have hRc := Subgroup.relIndex_mul_card (H := V ⊓ Y) (K := (P : Subgroup G))
  rw [inf_eq_left.mpr hRP, hPc] at hRc
  have hRr : (V ⊓ Y).relIndex P ≤ 9 :=
    (Subgroup.relIndex_inf_le (H := V) (K := Y) (L := (P : Subgroup G))).trans
      (by rw [hVr]; omega)
  have hR9 : 9 ≤ Nat.card (V ⊓ Y : Subgroup G) := by
    by_contra hlt
    push Not at hlt
    nlinarith
  refine ⟨V ⊓ Y, inf_le_right, (P.isPGroup').to_le hRP, ?_, ?_⟩
  ·
    intro hcyclic
    obtain ⟨c, hc⟩ := hcyclic.exists_generator
    have hdvd : Nat.card (V ⊓ Y : Subgroup G) ∣ 3 := by
      rw [← orderOf_eq_card_of_forall_mem_zpowers hc]
      exact orderOf_dvd_of_pow_eq_one (Subtype.ext (hV.2 c (mem_inf.mp c.2).1))
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · exact gamma_one_le_of_forall_centralizer_le hS hU0 hsit.mem_sigmaA hsit.isCoreMaxLocal hRP
      fun y hy hy1 _ => wreath614_centralizer_le hS hsit hVP hV hVc (mem_inf.mp hy).1 hy1

end CFSG.LocalAnalysis.RankThreeTheoremC
