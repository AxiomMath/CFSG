module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf18CrossChart
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf13Pair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf14Ab8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf15N8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf15Ker
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117GenP

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

namespace TwinThin

namespace Cross

theorem aeAut_of_five_le {m : ℕ} (hm : 5 ≤ m) :
    TwinThinPf8.AEAut m := by
  by_cases h8 : m = 8
  · subst h8
    exact TwinThinPf8.aeAut_eight
  · exact TwinThinPf8.aeAut_of_adjInv hm h8 (TL4.Mdl117.adjInv_of_ne_eight hm h8)

end Cross

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem mem_conjClass_of_mem_pi {J : Subgroup G} (hJ : J ∈ π) : J ∈ CoreAssembly.conjClass K₀ :=
  (adj_of_mem_isMaxOrb S.hos.graph S.hπ hJ).2.1

theorem twinLab_of_ne_eight {m : ℕ} (hm : 5 ≤ m) (hm8 : m ≠ 8) : S.TwinLab m :=
  fun J {_ _ _} hlab => S.map_twin_eq hm hm8 J hlab

theorem twin_label_conj_of {m : ℕ} (hm : 5 ≤ m) (htw : S.TwinLab m)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) {a : G} (ha : a ∈ conjSub g (piGen π)) :
    ∃ (β : Finset (Fin m)) (hβ : β.card = 4) (c : Bool),
      ((conjSub a K).subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ =
        AE.memBar β hβ c ∧
      ((conjSub a K').subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ =
        AE.memBar β hβ (!c) := by
  obtain ⟨α, h, b, hlab⟩ := J.label K S.mem_fam_self
  have hlab' := htw J hlab
  have hap : a ∈ pSpan (fam K (conjSub g (piGen π))) := by rw [S.fam_gen]; exact ha
  have e1 := TL4.AECov.map_conjSub_eq J K ⟨a, hap⟩
  have e2 := TL4.AECov.map_conjSub_eq J K' ⟨a, hap⟩
  rw [hlab] at e1
  rw [hlab'] at e2
  have hx : J.φ ⟨a, hap⟩ ∈ TwinThinPf8.Hn m := by
    have : J.φ ⟨a, hap⟩ ∈ J.φ.range := ⟨_, rfl⟩
    rw [J.range_eq] at this
    exact this
  obtain ⟨β, hβ, c, h1, h2⟩ := TwinThinPf15.pairPres_of_mem hm hx α h b
  exact ⟨β, hβ, c, e1.trans h1, e2.trans h2⟩

theorem cent_of_involution_pi {m : ℕ} (hm : 5 ≤ m) (htw : S.TwinLab m)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) {J' : Subgroup G} (hJ' : J' ∈ π) {u : G}
    (hu : IsUniqueInvolution J' u) : u ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by
  have hc := S.Zgrp_pi_comm_of hm htw J u (Subgroup.subset_closure ⟨J', hJ', hu⟩) (g * z * g⁻¹)
    (Subgroup.subset_closure ⟨conjSub g K, S.hg, S.hz.conj g⟩)
  exact Subgroup.mem_centralizer_singleton_iff.mpr hc

theorem mem_normalizer_pSpan_fam {c : G}
    (hc : c ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G)) :
    c ∈ Subgroup.normalizer (pSpan (fam K (conjSub g (piGen π))) : Set G) := by
  rw [S.fam_gen]
  exact S.mem_normalizer_X' hc

theorem perm_fix_of_induced {m : ℕ} (hm : 5 ≤ m) (htw : S.TwinLab m)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) {α : Finset (Fin m)} {h : α.card = 4} {b : Bool}
    (hlab : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h b)
    {u : G} {w : Wr m} (hw : Cross.InducedBy J u w) (huK : ∀ k ∈ K, u * k = k * u)
    (huK' : ∀ k ∈ K', u * k = k * u) : ∀ i ∈ α, w.perm i = i := by
  have hlab' := htw J hlab
  have hfix : ∀ L : Subgroup G, (∀ k ∈ L, u * k = k * u) →
      ∀ x ∈ (L.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ,
        mkQ m w * x * (mkQ m w)⁻¹ = x := by
    intro L hL x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hw.cent (hL _ (Subgroup.mem_subgroupOf.mp hy))
  refine TwinThinPf18.perm_fix_of_cent_memBar hm α h w ?_
  intro c x hx
  by_cases hcb : c = b
  · subst hcb
    rw [← hlab] at hx
    exact hfix K huK x hx
  · have hcb' : c = !b := by cases b <;> cases c <;> simp_all
    subst hcb'
    rw [← hlab'] at hx
    exact hfix K' huK' x hx

theorem exists_induced_fix {m : ℕ} (hm : 5 ≤ m) (hAut : TwinThinPf8.AEAut m) (htw : S.TwinLab m)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) {J' : Subgroup G} (hJ' : J' ∈ π) {u : G}
    (hu : IsUniqueInvolution J' u) {α : Finset (Fin m)} {h : α.card = 4} {b : Bool}
    (hlab : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h b) :
    ∃ w : Wr m, Cross.InducedBy J u w ∧ ∀ i ∈ α, w.perm i = i := by
  have hucent := S.cent_of_involution_pi hm htw J hJ' hu
  obtain ⟨w, hw⟩ := Cross.exists_induced hm hAut J (S.mem_normalizer_pSpan_fam hucent)
    (fun L hL => S.fam_conj_of_cent' hucent hL)
  have huX : u ∈ piGen π := le_piGen hJ' hu.mem
  exact ⟨w, hw, S.perm_fix_of_induced hm htw J hlab hw
    (fun k hk => (Subgroup.mem_centralizer_iff.mp (S.pair_le_cent.1 hk)) u huX)
    (fun k hk => (Subgroup.mem_centralizer_iff.mp (S.pair_le_cent.2 hk)) u huX)⟩

theorem comm_of_perm_one {m : ℕ} (hm : 5 ≤ m) (htw : S.TwinLab m)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) {u : G}
    (hu : u ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G)) {w : Wr m} (hw : Cross.InducedBy J u w)
    (hσ : w.perm = 1) {L : Subgroup G} (hL : L ∈ fam K (conjSub g (piGen π))) {v : G}
    (hv : IsUniqueInvolution L v) : u * v = v * u := by
  have huN := S.mem_normalizer_pSpan_fam hu
  obtain ⟨⟨a, ha⟩, rfl⟩ := hL
  obtain ⟨β, hβ, c, h1, h2⟩ := S.twin_label_conj_of hm htw J ha
  have hL' : conjSub u (conjSub a K) ∈ fam K (conjSub g (piGen π)) :=
    S.fam_conj_of_cent' hu (mem_fam ha)
  have hmap := Cross.map_conjSub_of_induced J huN hw (conjSub a K)
  rw [h1] at hmap
  have hK'a : conjSub a K' ∈ fam K (conjSub g (piGen π)) := fam_inv K' S.twin_mem_fam a ha
  have hvK : a * z * a⁻¹ = v := (S.hz.conj a).eq hv
  have hconj := hv.conj u
  have hcases : u * v * u⁻¹ = v := by
    rcases TwinThinPf18.conj_memBar_of_perm_one hm w hσ β hβ c with h | h
    · rw [h] at hmap
      have e : conjSub u (conjSub a K) = conjSub a K :=
        S.eq_of_map_le hm J hL' (mem_fam ha) (le_of_eq (hmap.trans h1.symm))
      rw [e] at hconj
      exact hconj.eq hv
    · rw [h] at hmap
      have e : conjSub u (conjSub a K) = conjSub a K' :=
        S.eq_of_map_le hm J hL' hK'a (le_of_eq (hmap.trans h2.symm))
      rw [e] at hconj
      have := hconj.eq (S.hz'.conj a)
      rw [this, hvK]
  calc u * v = (u * v * u⁻¹) * u := by group
    _ = v * u := by rw [hcases]

theorem perm_eq_one_of_comm_fam {m : ℕ} (hm : 5 ≤ m)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) {u : G} {w : Wr m} (hw : Cross.InducedBy J u w)
    (hcomm : ∀ L ∈ fam K (conjSub g (piGen π)), ∀ t : G, IsUniqueInvolution L t →
      u * t = t * u) : w.perm = 1 :=
  Cross.perm_eq_one_of_comm hm J (fun L hL => S.card8 L (S.fam_mem hL)) hw hcomm

theorem comm_mem_pCore_fam {m : ℕ} (hm : 5 ≤ m) (hAut : TwinThinPf8.AEAut m) (htw : S.TwinLab m)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) {J' : Subgroup G} (hJ' : J' ∈ π) {u : G}
    (hu : IsUniqueInvolution J' u)
    (hcomm : ∀ L ∈ fam K (conjSub g (piGen π)), ∀ t : G, IsUniqueInvolution L t →
      u * t = t * u) :
    ∀ x ∈ conjSub g (piGen π), u * x * u⁻¹ * x⁻¹ ∈ pCoreOf 2 (conjSub g (piGen π)) := by
  intro x hx
  have hucent := S.cent_of_involution_pi hm htw J hJ' hu
  have huN := S.mem_normalizer_pSpan_fam hucent
  obtain ⟨w, hw⟩ := Cross.exists_induced hm hAut J huN
    (fun L hL => S.fam_conj_of_cent' hucent hL)
  have hσ := S.perm_eq_one_of_comm_fam hm J hw hcomm
  have hk : IsPGroup 2 J.φ.ker := J.isPGroup_ker S.hOdd
  have hxX : x ∈ pSpan (fam K (conjSub g (piGen π))) := by rw [S.fam_gen]; exact hx
  have hc := Cross.comm_mem_pCore_of_perm_one hm J hk huN hw hσ x hxX
  rwa [S.fam_gen] at hc

theorem comm_mem_pCore_pi {m : ℕ} (hm : 5 ≤ m) (hAut : TwinThinPf8.AEAut m) (htw : S.TwinLab m)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) {L : Subgroup G}
    (hL : L ∈ fam K (conjSub g (piGen π))) {v : G} (hv : IsUniqueInvolution L v)
    (hcomm : ∀ J' ∈ π, ∀ t : G, IsUniqueInvolution J' t → v * t = t * v) :
    ∀ x ∈ piGen π, v * x * v⁻¹ * x⁻¹ ∈ pCoreOf 2 (piGen π) := by
  intro x hx
  have hvz : v * z = z * v := S.zfam_comm_z_of hm htw J hL hv
  have hvC : v ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hvz
  have hQπ := S.Q_eq_pi
  have hPQ := S.pSpan_conj_fam
  have hvN : v ∈ Subgroup.normalizer
      (pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π))) : Set G) := by
    rw [hPQ]
    exact S.hos.centralizer_le_normalizer_piGen S.hK S.hπ S.hH1 S.hz hvC
  have hvP : ∀ M ∈ conjSub g⁻¹ '' fam K (conjSub g (piGen π)),
      conjSub v M ∈ conjSub g⁻¹ '' fam K (conjSub g (piGen π)) := by
    intro M hM
    rw [hQπ] at hM ⊢
    exact S.conj_pi_of_cent hvC hM
  obtain ⟨w, hw⟩ := Cross.exists_induced hm hAut (J.conjX g⁻¹) hvN hvP
  have h8 : ∀ M ∈ conjSub g⁻¹ '' fam K (conjSub g (piGen π)), Nat.card ↥M = 8 := by
    intro M hM
    rw [hQπ] at hM
    exact S.card8 M (S.mem_conjClass_of_mem_pi hM)
  have hcomm2 : ∀ M ∈ conjSub g⁻¹ '' fam K (conjSub g (piGen π)), ∀ t : G,
      IsUniqueInvolution M t → v * t = t * v := by
    intro M hM t ht
    rw [hQπ] at hM
    exact hcomm M hM t ht
  have hσ := Cross.perm_eq_one_of_comm hm (J.conjX g⁻¹) h8 hw hcomm2
  have hOX : classicalInvolutionOddCore
      ↥(pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π)))) = ⊥ :=
    classicalInvolutionOddCore_eq_bot_of_mulEquiv (pSpanConj g⁻¹ _) S.hOdd
  have hk : IsPGroup 2 (J.conjX g⁻¹).φ.ker := (J.conjX g⁻¹).isPGroup_ker hOX
  have hxX : x ∈ pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π))) := by
    rw [hPQ]
    exact hx
  have hc := Cross.comm_mem_pCore_of_perm_one hm (J.conjX g⁻¹) hk hvN hw hσ x hxX
  rwa [hPQ] at hc

theorem pCoreOf_le_Dz_of_ker_le {m : ℕ} (hm : 5 ≤ m) (J : AEIdent (fam K (conjSub g (piGen π))) m)
    (hker' : J.φ.ker.map (pSpan (fam K (conjSub g (piGen π)))).subtype ≤ Dz K π g)
    (hker : conjSub g⁻¹ (J.φ.ker.map (pSpan (fam K (conjSub g (piGen π)))).subtype) ≤ Dz K π g) :
    pCoreOf 2 (conjSub g (piGen π)) ≤ Dz K π g ∧ pCoreOf 2 (piGen π) ≤ Dz K π g := by
  constructor
  · intro x hx
    rw [← S.fam_gen] at hx
    have h := Cross.pCoreOf_le_Zgrp_sup_ker hm J (fun L hL => S.card8 L (S.fam_mem hL)) hx
    have h1 : Zgrp (fam K (conjSub g (piGen π))) ≤ Dz K π g := fun y hy =>
      Subgroup.subset_closure (Or.inr hy)
    exact (sup_le h1 hker') h
  · intro x hx
    rw [← S.pSpan_conj_fam] at hx
    have h := Cross.pCoreOf_le_Zgrp_sup_ker hm (J.conjX g⁻¹) (fun L hL => by
      rw [S.Q_eq_pi] at hL
      exact S.card8 L (S.mem_conjClass_of_mem_pi hL)) hx
    have h1 : Zgrp (conjSub g⁻¹ '' fam K (conjSub g (piGen π))) ≤ Dz K π g := by
      intro y hy
      rw [S.Q_eq_pi] at hy
      exact Subgroup.subset_closure (Or.inl hy)
    have h2 : (J.conjX g⁻¹).φ.ker.map
        (pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π)))).subtype ≤ Dz K π g := by
      rintro _ ⟨k, hk, rfl⟩
      apply hker
      have hk1 : J.φ ((pSpanConj g⁻¹ (fam K (conjSub g (piGen π)))).symm k) = 1 := by
        rw [← AEIdent.conjX_φ_apply]
        exact hk
      refine mem_conjSub_iff.mpr ⟨_, hk1, ?_⟩
      show (((pSpanConj g⁻¹ (fam K (conjSub g (piGen π)))).symm k : ↥(pSpan (fam K
        (conjSub g (piGen π))))) : G) = g⁻¹⁻¹ * (k : G) * g⁻¹
      exact pSpanConj_symm_apply g⁻¹ _ k
    exact (sup_le h1 h2) h

theorem pCoreOf_le_Dz_of_ker {m : ℕ} (hm : 5 ≤ m) (J : AEIdent (fam K (conjSub g (piGen π))) m)
    (hker : J.φ.ker = ⊥) :
    pCoreOf 2 (conjSub g (piGen π)) ≤ Dz K π g ∧ pCoreOf 2 (piGen π) ≤ Dz K π g :=
  S.pCoreOf_le_Dz_of_ker_le hm J (by rw [hker, Subgroup.map_bot]; exact bot_le)
    (by
      rw [hker, Subgroup.map_bot]
      exact (le_of_eq (Subgroup.map_bot _)).trans bot_le)

theorem pCoreOf_le_Dz_of_odd {m : ℕ} (hm : 5 ≤ m) (hodd : m % 2 = 1)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) :
    pCoreOf 2 (conjSub g (piGen π)) ≤ Dz K π g ∧ pCoreOf 2 (piGen π) ≤ Dz K π g :=
  S.pCoreOf_le_Dz_of_ker hm J (S.ker_eq_bot_of_odd hm (by omega) hodd J)

theorem thinCrossPair_of_comm {m : ℕ} (hm : 5 ≤ m) (hAut : TwinThinPf8.AEAut m)
    (htw : S.TwinLab m) (J : AEIdent (fam K (conjSub g (piGen π))) m)
    (hO' : pCoreOf 2 (conjSub g (piGen π)) ≤ Dz K π g) (hO : pCoreOf 2 (piGen π) ≤ Dz K π g)
    (h1 : ∀ J' ∈ π, ∀ L ∈ fam K (conjSub g (piGen π)), ∀ u v : G, IsUniqueInvolution J' u →
      IsUniqueInvolution L v → u * v = v * u) : ThinCrossPair K π g := by
  refine ⟨h1, ?_, ?_⟩
  · intro J' hJ' x hx L hL v hv
    have hc := S.comm_mem_pCore_pi hm hAut htw J hL hv
      (fun M hM t ht => (h1 M hM L hL t v ht hv).symm) x (le_piGen hJ' hx)
    have hc' : x * v * x⁻¹ * v⁻¹ ∈ pCoreOf 2 (piGen π) := by
      have e : x * v * x⁻¹ * v⁻¹ = (v * x * v⁻¹ * x⁻¹)⁻¹ := by group
      rw [e]
      exact (pCoreOf 2 (piGen π)).inv_mem hc
    have hv_mem : v ∈ Dz K π g :=
      Subgroup.subset_closure (Or.inr (Subgroup.subset_closure ⟨L, hL, hv⟩))
    have e : x * v * x⁻¹ = (x * v * x⁻¹ * v⁻¹) * v := by group
    rw [e]
    exact (Dz K π g).mul_mem (hO hc') hv_mem
  · intro L hL x hx J' hJ' u hu
    have hxX : x ∈ conjSub g (piGen π) := by
      rw [← S.fam_gen]
      exact le_pSpan hL hx
    have hc := S.comm_mem_pCore_fam hm hAut htw J hJ' hu
      (fun M hM t ht => h1 J' hJ' M hM u t hu ht) x hxX
    have hc' : x * u * x⁻¹ * u⁻¹ ∈ pCoreOf 2 (conjSub g (piGen π)) := by
      have e : x * u * x⁻¹ * u⁻¹ = (u * x * u⁻¹ * x⁻¹)⁻¹ := by group
      rw [e]
      exact (pCoreOf 2 (conjSub g (piGen π))).inv_mem hc
    have hu_mem : u ∈ Dz K π g :=
      Subgroup.subset_closure (Or.inl (Subgroup.subset_closure ⟨J', hJ', hu⟩))
    have e : x * u * x⁻¹ = (x * u * x⁻¹ * u⁻¹) * u := by group
    rw [e]
    exact (Dz K π g).mul_mem (hO' hc') hu_mem

theorem comm_of_vector {m : ℕ} (hm : 5 ≤ m) (htw : S.TwinLab m)
    (J : AEIdent (fam K (conjSub g (piGen π))) m)
    (hvec : ∀ J' ∈ π, ∀ u : G, IsUniqueInvolution J' u →
      ∃ w : Wr m, Cross.InducedBy J u w ∧ w.perm = 1) :
    ∀ J' ∈ π, ∀ L ∈ fam K (conjSub g (piGen π)), ∀ u v : G, IsUniqueInvolution J' u →
      IsUniqueInvolution L v → u * v = v * u := by
  intro J' hJ' L hL u v hu hv
  obtain ⟨w, hw, hσ⟩ := hvec J' hJ' u hu
  exact S.comm_of_perm_one hm htw J (S.cent_of_involution_pi hm htw J hJ' hu) hw hσ hL hv

theorem thinCrossPair_of_vector {m : ℕ} (hm : 5 ≤ m) (hAut : TwinThinPf8.AEAut m)
    (htw : S.TwinLab m) (J : AEIdent (fam K (conjSub g (piGen π))) m)
    (hO' : pCoreOf 2 (conjSub g (piGen π)) ≤ Dz K π g) (hO : pCoreOf 2 (piGen π) ≤ Dz K π g)
    (hvec : ∀ J' ∈ π, ∀ u : G, IsUniqueInvolution J' u →
      ∃ w : Wr m, Cross.InducedBy J u w ∧ w.perm = 1) : ThinCrossPair K π g :=
  S.thinCrossPair_of_comm hm hAut htw J hO' hO (S.comm_of_vector hm htw J hvec)

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
