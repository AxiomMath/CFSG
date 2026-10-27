module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7B_Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Frame
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Block
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Module
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Rank
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Normal
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Three
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Offender
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Split
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Facts
import CFSG.Quasithin.Background.A4V
import CFSG.Quasithin.Background.B2FactorizationBaumannAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup Equiv CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]


omit [Finite G] in
theorem a7main_W_le (H : Subgroup G) : a7W H ≤ pCoreOf 2 H :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1.1

omit [Finite G] in
theorem a7main_W_le_centralizer (H : Subgroup G) : a7W H ≤ centralizer (pCoreOf 2 H : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1.2

omit [Finite G] in
theorem a7main_mem_W_of {H : Subgroup G} {x : G} (hxS : x ∈ pCoreOf 2 H)
    (hxC : x ∈ centralizer (pCoreOf 2 H : Set G)) (hx2 : x ^ 2 = 1) : x ∈ a7W H :=
  Subgroup.subset_closure ⟨⟨hxS, hxC⟩, hx2⟩

section Closure

omit [Finite G] in
theorem a7main_J_le_of_normalizer {H X Z : Subgroup G} (hXZ : X ≤ Z)
    (hZ : H ≤ normalizer (Z : Set G)) : a7J H X ≤ Z := by
  refine iSup₂_le fun h hh => ?_
  have hZ' : Z.map (MulAut.conj h).toMonoidHom = Z := mem_normalizer_iff_map_conj_eq.mp (hZ hh)
  rw [← hZ']
  exact Subgroup.map_mono hXZ

omit [Finite G] in
theorem a7main_map_conj_le_J {H X : Subgroup G} {h : G} (hh : h ∈ H) :
    X.map (MulAut.conj h).toMonoidHom ≤ a7J H X :=
  le_iSup₂_of_le h hh le_rfl

omit [Finite G] in
theorem a7main_le_J {H X : Subgroup G} : X ≤ a7J H X := by
  have h := a7main_map_conj_le_J (X := X) (H.one_mem)
  intro x hx
  exact h ⟨x, hx, by simp⟩

omit [Finite G] in
theorem a7main_J_conj_le {H X : Subgroup G} {h : G} (hh : h ∈ H) :
    (a7J H X).map (MulAut.conj h).toMonoidHom ≤ a7J H X := by
  refine Subgroup.map_le_iff_le_comap.mpr (iSup₂_le fun h' hh' => ?_)
  rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_map]
  have : (MulAut.conj h).toMonoidHom.comp (MulAut.conj h').toMonoidHom =
      (MulAut.conj (h * h')).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [this]
  exact a7main_map_conj_le_J (H.mul_mem hh hh')

omit [Finite G] in
theorem a7main_le_normalizer_J {H X : Subgroup G} : H ≤ normalizer (a7J H X : Set G) := by
  intro h hh
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have := a7main_J_conj_le (X := X) hh ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using this
  · intro hx
    have := a7main_J_conj_le (X := X) (H.inv_mem hh) ⟨_, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using this

end Closure

theorem gl83RelPair2A7Module_proved
    (hS : Setting G) : GL83RelPair2A7Module G := by
  intro p hp P M D R T H V hd hopt hfacts hp3 L hL hLA hcard hn
  obtain ⟨e⟩ := hLA
  obtain ⟨ι, hF⟩ := hopt.exists_a7Frame hS hd hfacts hp3 hL e hcard hn
  obtain ⟨Y, hYI, hYs, hYx, -⟩ := hF.exists_block
  obtain ⟨Y₁, hY₁Y, hY₁n, hperf, hι, hYK, hVY⟩ := hF.exists_perfect_normal hYI hYs hYx
  have hY₁I : Y₁ ≤ a7I H ι := hY₁Y.trans hYI
  obtain ⟨hRW, hR0, hRY⟩ := hF.exists_module hYI hYx hY₁Y hY₁n hperf hι
  obtain ⟨hJH, hHJ, -, hJι, -, hJKS, hDJ, hVJ, hY₁J⟩ := hF.exists_J_core hY₁I hperf hι hYK hVY
  have hthree := hF.exists_J_three hJH hJι hDJ
  obtain ⟨A, hA, hAι⟩ := hF.exists_offender hRW fun a haV ha2 haS =>
    hF.rank_ge_four hY₁I hY₁n hperf hι hVY hRW hR0 hRY haV ha2 haS
  have hbound := hF.card_a7W_le hJH hJι hJKS hVJ hA hAι
  have hWel : IsElemAbelian 2 (a7W H) := B2F.isElemAbelian_omegaOneCenterOf _
  have hWn : H ≤ normalizer (a7W H : Set G) := by
    have := CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf (pCoreOf 2 H)
    rw [hF.H_norm] at this
    exact this
  have hJW : ∀ j ∈ a7J H Y₁, (a7W H).map (MulAut.conj j).toMonoidHom = a7W H := fun j hj =>
    mem_normalizer_iff_map_conj_eq.mp (hWn (hJH hj))
  have hker : ∀ j : ↥H, (j : G) ∈ a7J H Y₁ → ι j = 1 → ∀ w ∈ a7W H,
      (j : G) * w * (j : G)⁻¹ = w := by
    intro j hjJ hj1 w hw
    have hjK : (j : G) ∈ a7K H := by
      have : j ∈ ι.ker := hj1
      rw [hF.ker_eq] at this
      exact ⟨j, this, rfl⟩
    have hjS : (j : G) ∈ pCoreOf 2 H := hJKS ⟨hjJ, hjK⟩
    have hc := Subgroup.mem_centralizer_iff.mp (a7main_W_le_centralizer H hw) j hjS
    rw [hc]
    group
  have hX₀W : a7J H ⁅pCoreOf 2 H, Y₁⁆ ≤ a7W H := a7main_J_le_of_normalizer hRW hWn
  have hX₀J : ∀ j ∈ a7J H Y₁, (a7J H ⁅pCoreOf 2 H, Y₁⁆).map (MulAut.conj j).toMonoidHom =
      a7J H ⁅pCoreOf 2 H, Y₁⁆ := fun j hj =>
    mem_normalizer_iff_map_conj_eq.mp (a7main_le_normalizer_J (hJH hj))
  have hX₀ne : a7J H ⁅pCoreOf 2 H, Y₁⁆ ≠ ⊥ := fun h => hR0 (le_bot_iff.mp (a7main_le_J.trans h.le))
  have hX₀c : ⁅a7J H ⁅pCoreOf 2 H, Y₁⁆, a7J H Y₁⁆ = a7J H ⁅pCoreOf 2 H, Y₁⁆ := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro x hx j hj
      have hjn := a7main_le_normalizer_J (X := ⁅pCoreOf 2 H, Y₁⁆) (hJH hj)
      have h1 : j * x⁻¹ * j⁻¹ ∈ a7J H ⁅pCoreOf 2 H, Y₁⁆ := by
        have := (mem_normalizer_iff.mp hjn x⁻¹).mp ((Subgroup.inv_mem _) hx)
        exact this
      have : x * (j * x⁻¹ * j⁻¹) ∈ a7J H ⁅pCoreOf 2 H, Y₁⁆ := Subgroup.mul_mem _ hx h1
      rw [commutatorElement_def]
      convert this using 1
      group
    · refine iSup₂_le fun h hh => ?_
      have h1 : (⁅pCoreOf 2 H, Y₁⁆ : Subgroup G).map (MulAut.conj h).toMonoidHom =
          ⁅(⁅pCoreOf 2 H, Y₁⁆ : Subgroup G).map (MulAut.conj h).toMonoidHom,
            Y₁.map (MulAut.conj h).toMonoidHom⁆ := by
        conv_lhs => rw [← hRY]
        exact Subgroup.map_commutator _ _ _
      rw [h1]
      exact Subgroup.commutator_mono (a7main_map_conj_le_J hh |>.trans' le_rfl)
        (a7main_map_conj_le_J hh)
  obtain ⟨U, hUW, hU16, hUC, hWU, hUJ, hUc, hUmax⟩ := exists_a7_natural_module (H := H)
    (ι := ι) hJH hJW hWel hJι hker hbound hX₀W hX₀J hX₀ne hX₀c
  have hUn : H ≤ normalizer (U : Set G) := by
    intro h hh
    have hh' : (h⁻¹ : G) ∈ H := H.inv_mem hh
    have hJh : (a7J H Y₁).map (MulAut.conj h).toMonoidHom = a7J H Y₁ :=
      mem_normalizer_iff_map_conj_eq.mp (hHJ hh)
    have hUh : U.map (MulAut.conj h).toMonoidHom ≤ U := by
      refine hUmax _ ?_ ?_ ?_
      · calc U.map (MulAut.conj h).toMonoidHom ≤ (a7W H).map (MulAut.conj h).toMonoidHom :=
            Subgroup.map_mono hUW
          _ = a7W H := mem_normalizer_iff_map_conj_eq.mp (hWn hh)
      · intro j hj
        have hj' : h⁻¹ * j * h ∈ a7J H Y₁ := by
          have := (mem_normalizer_iff.mp (hHJ hh') j).mp hj
          simpa [mul_assoc] using this
        have h1 := hUJ _ hj'
        rw [Subgroup.map_map]
        have : (MulAut.conj j).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
            (MulAut.conj h).toMonoidHom.comp (MulAut.conj (h⁻¹ * j * h)).toMonoidHom := by
          ext x
          simp [MulAut.conj_apply, mul_assoc]
        rw [this, ← Subgroup.map_map, h1]
      · have h1 := Subgroup.map_commutator U (a7J H Y₁) (MulAut.conj h).toMonoidHom
        rw [hJh, hUc] at h1
        exact h1.symm
    have hcard : Nat.card (U.map (MulAut.conj h).toMonoidHom) = Nat.card U :=
      Subgroup.card_map_of_injective (MulAut.conj h).injective
    have hUeq : U.map (MulAut.conj h).toMonoidHom = U :=
      Subgroup.eq_of_le_of_card_ge hUh (by rw [hcard])
    exact mem_normalizer_iff_map_conj_eq.mpr hUeq
  have hUS : U ≤ centralizer (pCoreOf 2 H : Set G) := hUW.trans (a7main_W_le_centralizer H)
  have hUel : IsElemAbelian 2 U := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => hWel.2 x (hUW hx)⟩
    exact Subtype.ext (by
      have := hWel.1.is_comm.comm ⟨x, hUW x.2⟩ ⟨y, hUW y.2⟩
      simp at this ⊢
      exact this)
  have hcomm : ∀ s ∈ pCoreOf 2 H, ∀ j ∈ a7J H Y₁, s * j * s⁻¹ * j⁻¹ ∈ U := by
    let Z₀ : Subgroup G :=
      { carrier := {j | j ∈ H ∧ ∀ s ∈ pCoreOf 2 H, s * j * s⁻¹ * j⁻¹ ∈ U}
        one_mem' := ⟨H.one_mem, fun s _ => by simp⟩
        mul_mem' := fun {a b} ha hb => by
          refine ⟨H.mul_mem ha.1 hb.1, fun s hs => ?_⟩
          have h1 := ha.2 s hs
          have h2 := (mem_normalizer_iff.mp (hUn ha.1) _).mp (hb.2 s hs)
          have := U.mul_mem h1 h2
          convert this using 1
          group
        inv_mem' := fun {a} ha => by
          refine ⟨H.inv_mem ha.1, fun s hs => ?_⟩
          have h1 := (mem_normalizer_iff.mp (hUn (H.inv_mem ha.1)) _).mp
            (U.inv_mem (ha.2 s hs))
          convert h1 using 1
          group }
    have hHS : H ≤ normalizer (pCoreOf 2 H : Set G) := hF.H_norm.ge
    have hY₁Z : Y₁ ≤ Z₀ := by
      intro y hy
      refine ⟨(hY₁I.trans (a7I_le H ι)) hy, fun s hs => ?_⟩
      have h1 : s * y * s⁻¹ * y⁻¹ ∈ ⁅pCoreOf 2 H, Y₁⁆ :=
        Subgroup.commutator_mem_commutator hs hy
      exact hUmax _ hX₀W hX₀J hX₀c (a7main_le_J h1)
    have hconj : ∀ h ∈ H, ∀ z ∈ Z₀, h * z * h⁻¹ ∈ Z₀ := by
      intro h hh z hz
      refine ⟨H.mul_mem (H.mul_mem hh hz.1) (H.inv_mem hh), fun s hs => ?_⟩
      have hs' : h⁻¹ * s * h ∈ pCoreOf 2 H := by
        have := (mem_normalizer_iff.mp (hHS (H.inv_mem hh)) s).mp hs
        simpa [mul_assoc] using this
      have h1 := hz.2 _ hs'
      have h2 := (mem_normalizer_iff.mp (hUn hh) _).mp h1
      convert h2 using 1
      group
    have hZ₀n : H ≤ normalizer (Z₀ : Set G) := by
      intro h hh
      refine mem_normalizer_iff.mpr fun x => ⟨fun hx => hconj h hh x hx, fun hx => ?_⟩
      have := hconj h⁻¹ (H.inv_mem hh) _ hx
      simpa [mul_assoc] using this
    have hJZ : a7J H Y₁ ≤ Z₀ := a7main_J_le_of_normalizer hY₁Z hZ₀n
    exact fun s hs j hj => (hJZ hj).2 s hs
  obtain ⟨hcent, hquad, hidx⟩ := hF.module_facts hJH hJι hUJ hUel hU16 hUC
    (fun j hj h1 u hu => hker j hj h1 u (hUW hu)) hVJ hUS
  refine ⟨a7J H Y₁, U, ?_⟩
  exact
    { U_le := hUW.trans (a7main_W_le H)
      U_central := hUS
      U_exp := fun u hu => hWel.2 u (hUW hu)
      card_U := hU16
      U_normal := hUn
      J₁_le := hJH
      D_le := hDJ
      V_le := hVJ
      comm := hcomm
      split := fun w hwS hwC hw2 =>
        (sup_le_sup_left (inf_le_inf_right _ (a7main_W_le H)) U) (hWU (a7main_mem_W_of hwS hwC hw2))
      inter := hUC
      cent := hcent
      quad := hquad
      idx := hidx
      three := hthree }

end CFSG.LocalAnalysis.RankThreeTheoremC
