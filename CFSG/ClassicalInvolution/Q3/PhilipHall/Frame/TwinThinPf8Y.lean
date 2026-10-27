module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8Gen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8Targets
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf7Frat
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8Cent

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

theorem center_eq_bot_of_eq {M : Type*} [Group M] {H H' : Subgroup M} (h : H = H')
    (hc : Subgroup.center ↥H' = ⊥) : Subgroup.center ↥H = ⊥ := by
  subst h; exact hc

theorem center_Hn {n : ℕ} (hn : 5 ≤ n) : Subgroup.center ↥(TwinThinPf8.Hn n) = ⊥ := by
  have e : AE.aeBarOver (⊤ : Subgroup (Equiv.Perm (Fin n))) = TwinThinPf8.Hn n := by
    simp [AE.aeBarOver, AE.aeSubOver, TwinThinPf8.Hn]
  have h := TwinThinPf.center_eq_bot_of_members (A := (⊤ : Subgroup (Equiv.Perm (Fin n))))
    (𝒜 := {β : Finset (Fin n) | β.card = 4}) hn
    (fun x y hxy => by
      have hs : ({x} : Finset (Fin n)) ⊆ Finset.univ.erase y := by
        intro a ha
        rw [Finset.mem_singleton] at ha
        subst ha
        simp [hxy]
      have hc4 : 4 ≤ (Finset.univ.erase y).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ y)]; simp; omega
      obtain ⟨t, hxt, hty, hcard⟩ := Finset.exists_subsuperset_card_eq (n := 4) hs (by simp) hc4
      exact ⟨t, hcard, hxt (Finset.mem_singleton_self x), fun hy => by
        have := hty hy
        simp at this⟩)
    (fun β hβ => hβ)
    (fun v hv x y => by
      obtain ⟨t, hxyt, -, hcard⟩ := Finset.exists_subsuperset_card_eq (n := 4)
        (Finset.subset_univ ({x, y} : Finset (Fin n)))
        (by
          calc ({x, y} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
            _ ≤ 4 := by norm_num)
        (by simp; omega)
      exact hv t hcard x (hxyt (by simp)) y (hxyt (by simp)))
    (fun β _ hβ b => by rw [e]; exact TwinThinPf8.memBar_le_Hn β hβ b)
  rw [e] at h
  exact h

theorem comm_memBar_twin {n : ℕ} (α : Finset (Fin n)) (h : α.card = 4) :
    ∀ x ∈ AE.memBar α h true, ∀ y ∈ AE.memBar α h false, x * y = y * x := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact AE.comm_memK_memKStar (AE.emb α h) a ha b hb

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem nbrAdj_of_comm {J J' : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K₀)
    (hJ' : J' ∈ CoreAssembly.conjClass K₀) (hne : J' ≠ J) (hc : ∀ x ∈ J, ∀ y ∈ J', x * y = y * x) :
    nbrAdj (CoreAssembly.conjClass K₀) J J' := by
  refine ⟨hJ, (mem_omegaNbr_iff S.hs.hyp S.hs.two).mpr ⟨hJ', hne, fun y hy => ?_⟩⟩
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · have h1 : y * x * y⁻¹ = x := by
      rw [← hc x hx y hy, mul_inv_cancel_right]
    rw [h1]
    exact hx
  · have h1 := hc _ hx y hy
    have h2 : x = y * x * y⁻¹ := by
      calc x = y⁻¹ * (y * x * y⁻¹ * y) := by group
        _ = y⁻¹ * (y * (y * x * y⁻¹)) := by rw [h1]
        _ = y * x * y⁻¹ := by group
    rw [h2]
    exact hx


theorem y_mem_cent_X {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8) (hn7 : n ≠ 7)
    (hT : TwinThinPf8.AEThree n) (J : AEIdent (fam K (conjSub g (piGen π))) n)
    {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h b)
    {y : ↥(pSpan (fam K (conjSub g (piGen π))))} (hyφ : J.φ y = AE.yBar α h)
    (hy3 : ∃ a : ℕ, y ^ 3 ^ a = 1) (hyz : (y : G) * z = z * (y : G)) :
    ∀ x ∈ piGen π, (y : G) * x = x * (y : G) := by
  have hQπ := S.Q_eq_pi
  have hPQ : pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π))) = piGen π := S.pSpan_conj_fam
  have hyX' : (y : G) ∈ conjSub g (piGen π) := (SetLike.ext_iff.mp S.fam_gen (y : G)).mp y.2
  have hyC : (y : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyz
  have hyN : (y : G) ∈ Subgroup.normalizer
      (pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π))) : Set G) := by
    rw [hPQ]
    exact S.hos.centralizer_le_normalizer_piGen S.hK S.hπ S.hH1 S.hz hyC
  set J2 := J.conj g⁻¹ with hJ2
  have hOX : classicalInvolutionOddCore
      ↥(pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π)))) = ⊥ :=
    classicalInvolutionOddCore_eq_bot_of_mulEquiv (pSpanConj g⁻¹ _) S.hOdd
  have hk2 : IsPGroup 2 J2.φ.ker := J2.isPGroup_ker hOX
  have hZ : Subgroup.center ↥J2.φ.range = ⊥ :=
    center_eq_bot_of_eq J2.range_eq (center_Hn hn)
  have hker' : ∀ x : ↥(pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π)))), x ∈ J2.φ.ker →
      TwinThinPf.conjOn _ (y : G) hyN x ∈ J2.φ.ker :=
    fun x hx => TwinThinPf.ker_invariant J2.φ hyN J2.ker_le hZ hx
  let σ := TwinThinPf.induced J2.φ hyN hker'
  obtain ⟨a3, hya3⟩ := hy3
  have hYpow : (y : G) ^ 3 ^ a3 = 1 := by
    have := congrArg Subtype.val hya3
    simpa using this
  have hiter : ∃ a : ℕ, ∀ r, (⇑σ)^[3 ^ a] r = r := ⟨a3, fun r => by
    obtain ⟨x, rfl⟩ := J2.φ.rangeRestrict_surjective r
    rw [TwinThinPf.induced_iterate]
    congr 1
    apply Subtype.ext
    rw [TwinThinPf.conjOn_iterate, hYpow]
    simp⟩
  have hPΩ : conjSub g⁻¹ '' fam K (conjSub g (piGen π)) ⊆ CoreAssembly.conjClass K₀ := by
    rw [hQπ]
    intro J hJ
    exact (adj_of_mem_isMaxOrb S.hos.graph S.hπ hJ).2.1
  have hKg : conjSub g K ∈ conjSub g⁻¹ '' fam K (conjSub g (piGen π)) := S.conj_mem_image
  obtain ⟨β0, hβ0, c0, hlab0⟩ := J2.label _ hKg
  have hyL0 : ∀ l ∈ conjSub g K, (y : G) * l = l * (y : G) := by
    intro l hl
    have := (S.hos.conj_le_inf_centralizer S.hπ S.hg hl).2
    exact (Subgroup.mem_centralizer_iff.mp this) (y : G) hyX'
  have hcentM : ∀ (β : Finset (Fin n)) (hβ : β.card = 4) (c : Bool), (Disjoint β0 β ∨ β = β0) →
      ∀ M ∈ conjSub g⁻¹ '' fam K (conjSub g (piGen π)),
        (M.subgroupOf (pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π))))).map J2.φ =
          AE.memBar β hβ c → ∀ l ∈ M, (y : G) * l = l * (y : G) := by
    intro β hβ c hd M hM hMlab
    by_cases hMK : M = conjSub g K
    · subst hMK; exact hyL0
    · have hcomm : ∀ a ∈ conjSub g K, ∀ b ∈ M, a * b = b * a := by
        refine S.commutes_of_map_comm_gen hPΩ J2 hk2 hKg hM (Ne.symm hMK) ?_
        rw [hlab0, hMlab]
        rcases hd with hd | hd
        · exact AE.comm_memBar_of_disjoint hd c0 c
        · rcases hd with rfl
          by_cases hcc : c = c0
          · subst hcc
            exact absurd (S.eq_of_map_le_gen hPΩ hn J2 hk2 hM hKg (le_of_eq (hMlab.trans hlab0.symm)))
              hMK
          · cases c0 <;> cases c
            · exact absurd rfl hcc
            · exact fun x hx y hy => (comm_memBar_twin _ _ y hy x hx).symm
            · exact fun x hx y hy => comm_memBar_twin _ _ x hx y hy
            · exact absurd rfl hcc
      have hadj := S.nbrAdj_of_comm (hPΩ hKg) (hPΩ hM) hMK hcomm
      exact S.y_cent_pi hn hn8 J hlab hyφ ⟨a3, hya3⟩ (by rw [← hQπ]; exact hM) hadj
  have hperm : TwinThinPf8.PermMembers J2.φ.range σ := by
    intro β hβ c
    obtain ⟨M, hM, hMlab⟩ := J2.label_surj β hβ c
    have hMπ : M ∈ π := by rw [← hQπ]; exact hM
    have hM' : conjSub (y : G) M ∈ conjSub g⁻¹ '' fam K (conjSub g (piGen π)) := by
      rw [hQπ]; exact S.conj_pi_of_cent hyC hMπ
    obtain ⟨β', hβ', c', hlab'⟩ := J2.label _ hM'
    refine ⟨β', hβ', c', fun x hx => ?_⟩
    have hx' : (x : AE.AEQ n) ∈ (M.subgroupOf _).map J2.φ := by rw [hMlab]; exact hx
    obtain ⟨m, hm, hmx⟩ := J2.exists_of_mem_map hM hx'
    have hxe : x = J2.φ.rangeRestrict ⟨m, le_pSpan hM hm⟩ := Subtype.ext hmx.symm
    rw [hxe, TwinThinPf.induced_apply, ← hlab']
    exact ⟨TwinThinPf.conjOn _ (y : G) hyN ⟨m, le_pSpan hM hm⟩,
      Subgroup.mem_subgroupOf.mpr (by rw [TwinThinPf.conjOn_apply]; exact conj_mem_conjSub hm), rfl⟩
  have hcent : ∀ (β : Finset (Fin n)) (hβ : β.card = 4) (c : Bool), (Disjoint β0 β ∨ β = β0) →
      ∀ x : ↥J2.φ.range, (x : AE.AEQ n) ∈ AE.memBar β hβ c → σ x = x := by
    intro β hβ c hd x hx
    obtain ⟨M, hM, hMlab⟩ := J2.label_surj β hβ c
    have hx' : (x : AE.AEQ n) ∈ (M.subgroupOf _).map J2.φ := by rw [hMlab]; exact hx
    obtain ⟨m, hm, hmx⟩ := J2.exists_of_mem_map hM hx'
    have hxe : x = J2.φ.rangeRestrict ⟨m, le_pSpan hM hm⟩ := Subtype.ext hmx.symm
    rw [hxe, TwinThinPf.induced_apply]
    congr 1
    apply Subtype.ext
    rw [TwinThinPf.conjOn_apply]
    have := hcentM β hβ c hd M hM hMlab m hm
    show (y : G) * m * (y : G)⁻¹ = m
    rw [this]; group
  have hor := hT β0 hβ0 J2.φ.range J2.range_eq σ hiter hperm hcent
  have hall : ∀ r, σ r = r := by
    rcases hor with h7 | hall
    · exact absurd h7 hn7
    · exact hall
  have htriv : ∀ x : ↥(pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π)))),
      J2.φ (TwinThinPf.conjOn _ (y : G) hyN x) = J2.φ x := by
    intro x
    have := hall (J2.φ.rangeRestrict x)
    rw [TwinThinPf.induced_apply] at this
    exact congrArg Subtype.val this
  have hcen := TwinThinPf.centralizes_of_trivial_mod_ker J2.φ J2.ker_le hyN htriv hyL0
    (le_pSpan hKg) (TwinThinPf.gen_of_trans (S.trans_conj_fam _ hKg))
  rw [hPQ] at hcen
  exact hcen

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
