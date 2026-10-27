module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81FiveTwentySixStar
public import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Comp
public import CFSG.Quasithin.Vol2.Ch10SecDFrattini

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.FiveTwentySix

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeUC.S15
  CFSG.QuasithinUnique

theorem normalClosure_le_sup_centralizer {G : Type} [Group G] [Finite G] {M : Subgroup G}
    (hM : CFSG.Open.IsComponentOf M ⊤) :
    Subgroup.normalClosure (M : Set G) ≤ M ⊔ Subgroup.centralizer (M : Set G) := by
  rw [Subgroup.normalClosure, Subgroup.closure_le]
  intro x hx
  rw [Group.mem_conjugatesOfSet_iff] at hx
  obtain ⟨b, hb, hconj⟩ := hx
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  rw [← hc]
  set M' : Subgroup G := M.map (MulAut.conj c).toMonoidHom
  have hcomp : CFSG.Open.IsComponentOf M' ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj c) M).mpr hM
  have hmem : c * b * c⁻¹ ∈ M' := ⟨b, hb, MulAut.conj_apply c b⟩
  by_cases hEq : M' = M
  · rw [hEq] at hmem
    exact Subgroup.mem_sup_left hmem
  · refine Subgroup.mem_sup_right ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact CFSG.LocalAnalysis.RankThreeTheoremC.commute_of_isComponentOf_ne hM hcomp
      (Ne.symm hEq) y hy _ hmem

theorem le_inf_sup_centralizer {G : Type} [Group G] [Finite G] {M H S : Subgroup G}
    (hHM : H ≤ M ⊔ Subgroup.centralizer (M : Set G)) (hSH : S ≤ H) (hS : IsSylowTwoOf S M)
    (hN : M ⊓ Subgroup.normalizer (S : Set G) ≤ S ⊔ Subgroup.centralizer (M : Set G)) :
    H ≤ (H ⊓ M) ⊔ Subgroup.centralizer (M : Set G) := by
  intro h hh
  have hMnc : M ≤ Subgroup.normalizer (Subgroup.centralizer (M : Set G)) := by
    have h1 : ⁅Subgroup.centralizer (M : Set G), M⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr le_rfl
    have h2 : ⁅M, Subgroup.centralizer (M : Set G)⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]; exact h1
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2).trans
      (Subgroup.centralizer_le_normalizer _)
  have hS' : IsSylowTwoOf S (H ⊓ M) := by
    refine ⟨le_inf hSH hS.1, hS.2.1, fun h2 => hS.2.2 (h2.trans ?_)⟩
    exact ⟨(H ⊓ M).relIndex M,
      (Subgroup.relIndex_mul_relIndex (H := S) (K := H ⊓ M) (L := M)
        (le_inf hSH hS.1) inf_le_right).symm⟩
  obtain ⟨m, hm, c, hc, rfl⟩ : ∃ m ∈ M, ∃ c ∈ Subgroup.centralizer (M : Set G), h = m * c := by
    have hh' : h ∈ (↑(M ⊔ Subgroup.centralizer (M : Set G)) : Set G) := hHM hh
    rw [Subgroup.coe_mul_of_left_le_normalizer_right M _ hMnc, Set.mem_mul] at hh'
    obtain ⟨m, hm, c, hc, hmc⟩ := hh'
    exact ⟨m, hm, c, hc, hmc.symm⟩
  have hH : m * c ∈ Subgroup.normalizer ((H ⊓ M : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf (H := H) (K := M)
      ⟨Subgroup.le_normalizer hh,
        (Subgroup.normalizer (M : Set G)).mul_mem (Subgroup.le_normalizer hm)
          (Subgroup.centralizer_le_normalizer (M : Set G) hc)⟩
  obtain ⟨n, hn, hnh⟩ := CFSG.Quasithin.Vol2.Ch10.SecD.exists_mul_mem_normalizer
    (R := S) (N := H ⊓ M) hS' hH
  have hcS : c⁻¹ ∈ Subgroup.normalizer (S : Set G) :=
    (Subgroup.normalizer (S : Set G)).inv_mem
      (Subgroup.centralizer_le_normalizer (S : Set G) (Subgroup.centralizer_le hS.1 hc))
  have hnm : n * m ∈ M ⊓ Subgroup.normalizer (S : Set G) := by
    refine ⟨M.mul_mem hn.2 hm, ?_⟩
    rw [show n * m = n * (m * c) * c⁻¹ by group]
    exact (Subgroup.normalizer (S : Set G)).mul_mem hnh hcS
  obtain ⟨s, hs, c', hc', hsc⟩ : ∃ s ∈ S, ∃ c' ∈ Subgroup.centralizer (M : Set G),
      n * m = s * c' := by
    have hnmS : n * m ∈ (↑(S ⊔ Subgroup.centralizer (M : Set G)) : Set G) := hN hnm
    rw [Subgroup.coe_mul_of_left_le_normalizer_right S _ (hS.1.trans hMnc),
      Set.mem_mul] at hnmS
    obtain ⟨s, hs, c', hc', hsc⟩ := hnmS
    exact ⟨s, hs, c', hc', hsc.symm⟩
  have h1 : n⁻¹ * s ∈ (H ⊓ M) ⊔ Subgroup.centralizer (M : Set G) :=
    Subgroup.mem_sup_left (Subgroup.mem_inf.mpr
      ⟨H.mul_mem (H.inv_mem hn.1) (hSH hs), M.mul_mem (M.inv_mem hn.2) (hS.1 hs)⟩)
  have h2 : c' * c ∈ (H ⊓ M) ⊔ Subgroup.centralizer (M : Set G) :=
    Subgroup.mem_sup_right ((Subgroup.centralizer (M : Set G)).mul_mem hc' hc)
  have hkey : (n⁻¹ * s) * (c' * c) = m * c := by
    rw [show (n⁻¹ * s) * (c' * c) = n⁻¹ * (s * c') * c by group, ← hsc]
    group
  rw [← hkey]
  exact Subgroup.mul_mem _ h1 h2

variable {X : Type} [Group X] [Finite X] {T L : Subgroup X}

theorem normalClosure_inf_normalizer_le (hX : GNSetting X T) (hL : IsC2 L)
    (hN : barO2 L ⊓ Subgroup.normalizer (barO2 (T ⊓ L) : Set (X ⧸ CFSG.pCore 2 X)) ≤
      barO2 (T ⊓ L) ⊔ Subgroup.centralizer (barO2 L : Set (X ⧸ CFSG.pCore 2 X)))
    {B : Subgroup X} (hTB : T ≤ Subgroup.normalizer (B : Set X)) :
    Subgroup.normalClosure (L : Set X) ⊓ Subgroup.normalizer (B : Set X) ≤
      (L ⊓ Subgroup.normalizer (B : Set X)) ⊔
        (Subgroup.centralizer (barO2 L : Set (X ⧸ CFSG.pCore 2 X))).comap
          (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
  classical
  set π : X →* (X ⧸ CFSG.pCore 2 X) := QuotientGroup.mk' (CFSG.pCore 2 X) with hπdef
  set M : Subgroup (X ⧸ CFSG.pCore 2 X) := barO2 L with hMdef
  set S : Subgroup (X ⧸ CFSG.pCore 2 X) := barO2 (T ⊓ L) with hSdef
  set NB : Subgroup X := Subgroup.normalizer (B : Set X) with hNBdef
  set K : Subgroup X := Subgroup.normalClosure (L : Set X) with hKdef
  set H : Subgroup X := K ⊓ NB with hHdef
  set C : Subgroup (X ⧸ CFSG.pCore 2 X) :=
    Subgroup.centralizer (M : Set (X ⧸ CFSG.pCore 2 X)) with hCdef
  set W : Subgroup X := C.comap π with hWdef
  have hMnc : M ≤ Subgroup.normalizer (C : Set (X ⧸ CFSG.pCore 2 X)) := by
    have h1 : ⁅C, M⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr le_rfl
    have h2 : ⁅M, C⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact h1
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2).trans
      (Subgroup.centralizer_le_normalizer _)
  have hMcomp : CFSG.Open.IsComponentOf M ⊤ := hL.component
  have hHbar : H.map π ≤ M ⊔ C := by
    refine (Subgroup.map_mono (inf_le_left : K ⊓ NB ≤ K)).trans ?_
    refine (Subgroup.map_normalClosure_le (L : Set X) π).trans ?_
    rw [show Subgroup.normalClosure (π '' (L : Set X)) =
      Subgroup.normalClosure (M : Set (X ⧸ CFSG.pCore 2 X)) from rfl]
    exact normalClosure_le_sup_centralizer hMcomp
  have hSH : S ≤ H.map π :=
    Subgroup.map_mono
      (le_inf (inf_le_right.trans Subgroup.le_normalClosure) (inf_le_left.trans hTB))
  have hSyl : IsSylowTwoOf S M :=
    CFSG.AGLEmbedding.AscEightFive.isSylowTwoOf_map (isSylowTwoOf_inf hX hL) π
  have hmain : H.map π ≤ (H.map π ⊓ M) ⊔ C :=
    le_inf_sup_centralizer (M := M) (H := H.map π) (S := S) hHbar hSH hSyl hN
  intro x hx
  have hx' : x ∈ K ⊓ NB := hHdef ▸ hx
  obtain ⟨hxK, hxN⟩ := Subgroup.mem_inf.mp hx'
  have hxH : x ∈ H := hHdef.symm ▸ Subgroup.mem_inf.mpr ⟨hxK, hxN⟩
  have hxbar : π x ∈ H.map π := Subgroup.mem_map_of_mem π hxH
  have hxbar' : π x ∈ (↑((H.map π ⊓ M) ⊔ C) : Set (X ⧸ CFSG.pCore 2 X)) := hmain hxbar
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (inf_le_right.trans hMnc),
    Set.mem_mul] at hxbar'
  obtain ⟨ybar, hybar, cbar, hcbar, hyc⟩ := hxbar'
  have hybarM : ybar ∈ L.map π := hybar.2
  obtain ⟨y, hyL, hyy⟩ := Subgroup.mem_map.mp hybarM
  obtain ⟨h', hh'H, hh'y⟩ := Subgroup.mem_map.mp hybar.1
  have hπeq : π h' = π y := hh'y.trans hyy.symm
  have hq : h'⁻¹ * y ∈ CFSG.pCore 2 X := QuotientGroup.eq.mp hπeq
  have hqT : h'⁻¹ * y ∈ T := pCore_le_gnC_aux1 hX.sylow hq
  have hh'NB : h' ∈ NB := (hHdef ▸ hh'H).2
  have hyNB : y ∈ NB := by
    have hy' : y = h' * (h'⁻¹ * y) := by group
    rw [hy']
    exact NB.mul_mem hh'NB (hTB hqT)
  have hy : y ∈ L ⊓ NB := Subgroup.mem_inf.mpr ⟨hyL, hyNB⟩
  have hWmem : y⁻¹ * x ∈ W := by
    rw [hWdef, Subgroup.mem_comap]
    have h1 : π (y⁻¹ * x) = ybar⁻¹ * π x := by rw [map_mul, map_inv, hyy]
    have h2 : ybar⁻¹ * π x = cbar := by
      rw [← hyc]; group
    rw [h1, h2]
    exact hcbar
  have hfin : x = y * (y⁻¹ * x) := by group
  rw [hfin]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hWmem)

end CFSG.LocalAnalysis.RankThreeTheoremC.FiveTwentySix
