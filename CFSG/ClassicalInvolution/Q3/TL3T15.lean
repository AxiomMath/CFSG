module

public import CFSG.ClassicalInvolution.Q3.TL3T14
public import CFSG.ClassicalInvolution.Q3.AE.E29

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem CentX.inv {M : Subgroup G} {x : G} (hx : CentX Ω M x) : CentX Ω M x⁻¹ := by
  intro L hL l hl
  have h1 := hx L hL l hl
  calc x⁻¹ * l = x⁻¹ * (l * x) * x⁻¹ := by group
    _ = x⁻¹ * (x * l) * x⁻¹ := by rw [h1]
    _ = l * x⁻¹ := by group

omit [Finite G] in
theorem CentX.mul {M : Subgroup G} {x y : G} (hx : CentX Ω M x) (hy : CentX Ω M y) :
    CentX Ω M (x * y) := by
  intro L hL l hl
  calc x * y * l = x * (y * l) := by group
    _ = x * (l * y) := by rw [hy L hL l hl]
    _ = (x * l) * y := by group
    _ = (l * x) * y := by rw [hx L hL l hl]
    _ = l * (x * y) := by group

variable {K : Subgroup G} (hS : ThinStd Ω K)
include hS

theorem ThinStd.mem_center_of_centX {M N : Subgroup G} (hN : MaxAdj (nbrAdj Ω) M N) {x : G}
    (hcM : CentX Ω M x) (hcN : CentX Ω N x) : x ∈ Subgroup.center G := by
  have hF := hS.graphFam
  have hNM : MaxAdj (nbrAdj Ω) N M := ⟨hF.graph.symm hN.1, orbOf_mem_maxOrbs hF hN.1 hN.2⟩
  have hle : (⨆ J ∈ Ω, J) ≤ Subgroup.centralizer ({x} : Set G) := by
    refine iSup₂_le fun J hJ => ?_
    refine (le_iSup_of_maxOrb hF hN.1 hN.2 J hJ).trans ?_
    refine iSup₂_le fun L hL => ?_
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hL with hL | hL
    · have hL' : MaxAdj (nbrAdj Ω) M L :=
        ⟨adj_of_mem_orbOf hF.graph hN.1 hL, by rw [orbOf_eq_of_mem hL]; exact hN.2⟩
      exact (hcM L hL' l hl).symm
    · have hL' : MaxAdj (nbrAdj Ω) N L :=
        ⟨adj_of_mem_orbOf hF.graph hNM.1 hL, by rw [orbOf_eq_of_mem hL]; exact hNM.2⟩
      exact (hcN L hL' l hl).symm
  rw [hS.gen] at hle
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))

theorem ThinStd.centX_of_zBar_eq {A : Subgroup G} {n : ℕ} (hn : 5 ≤ n)
    (φ : ↥(pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M}) →* AE.AEQ n)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M}))
    {L L' : Subgroup G} (hL : MaxAdj (nbrAdj Ω) A L) (hL' : MaxAdj (nbrAdj Ω) A L')
    {α β : Finset (Fin n)} {h : α.card = 4} {h' : β.card = 4} {b c : Bool}
    (hlab : (L.subgroupOf (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})).map φ =
      AE.memBar α h b)
    (hlab' : (L'.subgroupOf (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})).map φ =
      AE.memBar β h' c)
    (hz : AE.zBar α h = AE.zBar β h') {u u' : G} (hu : IsUniqueInvolution L u)
    (hu' : IsUniqueInvolution L' u') : CentX Ω A (u * u') := by
  have hPΩ : {M : Subgroup G | MaxAdj (nbrAdj Ω) A M} ⊆ Ω := fun M hM => hM.1.2.1
  have hk : (⟨u, le_pSpan hL hu.mem⟩ * ⟨u', le_pSpan hL' hu'.mem⟩ :
      ↥(pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, phi_map_eq_zBar φ hn hL (hS.card L (hPΩ hL)) hlab hu,
      phi_map_eq_zBar φ hn hL' (hS.card L' (hPΩ hL')) hlab' hu', hz]
    exact AE.zBar_mul_self β h'
  intro M hM m hm
  have := Subgroup.mem_center_iff.mp (hker hk) ⟨m, le_pSpan hM hm⟩
  exact (congrArg Subtype.val this).symm

theorem ThinStd.false_of_e29 (hZ : Subgroup.center G = ⊥) {M N : Subgroup G}
    (hN : MaxAdj (nbrAdj Ω) M N)
    (IM : AEIdentOn {L : Subgroup G | MaxAdj (nbrAdj Ω) M L} 8 AE.e29Sets AE.e29Sub)
    (IN : AEIdentOn {L : Subgroup G | MaxAdj (nbrAdj Ω) N L} 8 AE.e29Sets AE.e29Sub) : False := by
  have hPΩ : {L : Subgroup G | MaxAdj (nbrAdj Ω) M L} ⊆ Ω := fun L hL => hL.1.2.1
  obtain ⟨α, hα, h, b, hlabN⟩ := IM.label N hN
  have hαc : αᶜ ∈ AE.e29Sets := AE.e29Sets_compl hα
  have hc4 : αᶜ.card = 4 := by
    rw [Finset.card_compl, Fintype.card_fin, h]
  obtain ⟨N', hN', hlabN'⟩ := IM.label_surj α hα h (!b)
  obtain ⟨P, hP, hlabP⟩ := IM.label_surj αᶜ hαc hc4 b
  have hdα : Disjoint α αᶜ := disjoint_compl_right
  have hne' : N ≠ N' := by
    rintro rfl
    rw [hlabN] at hlabN'
    cases b
    · exact AE.memBar_true_ne_false (by norm_num) α h hlabN'.symm
    · exact AE.memBar_true_ne_false (by norm_num) α h hlabN'
  have hneP : N' ≠ P := by
    rintro rfl
    exact AE.memBar_ne_of_disjoint hdα (!b) b (hlabN'.symm.trans hlabP)
  have hzc : AE.zBar α h = AE.zBar αᶜ hc4 := AE.zBar_compl α h hc4
  obtain ⟨u, hu⟩ := (hS.hyp.omega1 N hN.1.2.1).1
  obtain ⟨u', hu'⟩ := (hS.hyp.omega1 N' hN'.1.2.1).1
  obtain ⟨w, hw⟩ := (hS.hyp.omega1 P hP.1.2.1).1
  have hcM' : CentX Ω M (u * u') :=
    hS.centX_of_zBar_eq (by norm_num) IM.φ IM.ker_le hN hN' hlabN hlabN' rfl hu hu'
  have hcMP : CentX Ω M (u * w) :=
    hS.centX_of_zBar_eq (by norm_num) IM.φ IM.ker_le hN hP hlabN hlabP hzc hu hw
  have hneNP : N ≠ P := by
    rintro rfl
    exact AE.memBar_ne_of_disjoint hdα b b (hlabN.symm.trans hlabP)
  have hNN' := hS.maxAdj_of_centX_mul hZ hN hN' hne' hu hu' hcM'
  have hNP := hS.maxAdj_of_centX_mul hZ hN hP hneNP hu hw hcMP
  have hNM := hS.maxAdj_symm hN
  obtain ⟨β, hβ, hβ4, c, hlabM⟩ := IN.label M hNM
  obtain ⟨zM, hzM⟩ := (hS.hyp.omega1 M hN.1.1).1
  have hsame : ∀ {L : Subgroup G} {v : G}, MaxAdj (nbrAdj Ω) M L → MaxAdj (nbrAdj Ω) N L →
      L ≠ M → IsUniqueInvolution L v → CentX Ω N (zM * v) := by
    intro L v hML hNL hLM hv
    obtain ⟨γ, hγ, hγ4, d, hlabL⟩ := IN.label L hNL
    have hzz : AE.zBar β hβ4 = AE.zBar γ hγ4 := by
      by_cases hβγ : β = γ
      · subst hβγ
        rfl
      ·
        have hd : Disjoint β γ := by
          refine AE.disjoint_of_zBar_comm (h := hβ4) (h' := hγ4) hβγ (c := d) fun y hy => ?_
          rw [← hlabL] at hy
          obtain ⟨x, hx, rfl⟩ := hy
          have hxL : (x : G) ∈ L := Subgroup.mem_subgroupOf.mp hx
          have hzMmap := phi_map_eq_zBar IN.φ (by norm_num) hNM
            (hS.card M hN.1.1) hlabM hzM
          rw [← hzMmap, ← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (hS.commutes_of_nbrAdj hML.1 zM hzM.mem x hxL)
        have hγc := AE.e29Sets_eq_compl_of_disjoint hβ hγ hd
        subst hγc
        exact AE.zBar_compl β hβ4 hγ4
    exact hS.centX_of_zBar_eq (by norm_num) IN.φ IN.ker_le hNM hNL hlabM hlabL hzz hzM hv
  have hcN' := hsame hN' hNN' (fun h => hN'.1.2.2.1 h) hu'
  have hcNP := hsame hP hNP (fun h => hP.1.2.2.1 h) hw
  have hu'inv : u'⁻¹ = u' := inv_eq_of_mul_eq_one_right hu'.sq
  have hcMe : CentX Ω M (u' * w) := by
    have := (CentX.inv hcM').mul hcMP
    rwa [show (u * u')⁻¹ * (u * w) = u' * w by rw [mul_inv_rev, hu'inv]; group] at this
  have hcNe : CentX Ω N (u' * w) := by
    have := (CentX.inv hcN').mul hcNP
    rwa [show (zM * u')⁻¹ * (zM * w) = u' * w by rw [mul_inv_rev, hu'inv]; group] at this
  have hcen := hS.mem_center_of_centX hN hcMe hcNe
  rw [hZ, Subgroup.mem_bot] at hcen
  have hwu : w = u' := by
    calc w = u'⁻¹ * (u' * w) := by group
      _ = u' := by rw [hcen, mul_one, hu'inv]
  rw [hwu] at hw
  exact hneP (hS.eq_of_uniqueInvolution hN'.1.2.1 hP.1.2.1 hu' hw)

end CFSG.ClassicalInvolution.Q3.TC.Thin

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Cit3


theorem tightCase29Leaf_holds (n : ℕ) : TightCase29Leaf n := by
  intro Y _ _ R S t hL hO hconn hsep hall ⟨I⟩
  have hS := hL.thinStd hO hconn hsep
  have hα0 : ({0, 2, 4, 6} : Finset (Fin 8)) ∈ AE.e29Sets := by
    show _ ∈ AE.affinePlanes
    simp [AE.affinePlanes]
  obtain ⟨N, hN, -⟩ := I.label_surj _ hα0 (by decide) true
  obtain ⟨g, rfl⟩ := hS.trans _ hN.1.2.1
  exact hS.false_of_e29 hL.center hN I
    (TC.Thin.AEIdentOn.ofEq (hS.maxAdjSet_conj _ g).symm (I.conj g))

variable {n : ℕ} in
theorem tightIndepLeaf_of_thmD3'' (hD : TC.Thin.TightThmD3) : TightIndepLeaf n :=
  tightIndepLeaf_of_thmD3' hD (tightCase29Leaf_holds n)

end Cit3

end CFSG.ClassicalInvolution.Q3
