module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshL7A

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.EvenSporadicStandard.Fin76b
open scoped commutatorElement

theorem l8Check_parts {α k : ℕ} (h : l8Check α k = true) :
    l8Fact (nEnum α k) (nwT α k eWord) = true ∧
      l8ZN (nEnum α k) (nwT α k cWord) (jTab α k [7, 8]) (tenum (wgens α k eWords)).toList =
        true ∧
      l8Chain α k (tenum (wgens α k eWords)).toList = true := by
  unfold l8Check at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

section Lemma8

variable {G : Type} [Group G] {e : G}
variable {e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12}


set_option linter.unusedSectionVars false

variable {d : G} {α k : ℕ}

@[expose] noncomputable def y0G (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)
    (d : G) (α : ℕ) : G :=
  val e₀ d α (jIn α (swN [7, 8]))

@[expose] noncomputable def hElt (E : NEmb e₀ d α k) : G :=
  gen4 e₀ d 4 * ψ E (pw α k hWord) * gen4 e₀ d 4

theorem rep_sTab (D : FusionData α k) (W : List Int) :
    Rep 16 (sTab α k W) (wp α k (jOut α (swN W))) := rep_nT D.hsz D.hnC _

theorem rep_jTab (D : FusionData α k) (W : List Int) :
    Rep 16 (jTab α k W) (wp α k (jIn α (swN W))) := rep_nT D.hsz D.hnC _

theorem hElt_conj (D : FusionData α k) (E : NEmb e₀ d α k) {W W' : List Int}
    (h : chainOK α k (nwT α k hWord) W W' = true) :
    (hElt E)⁻¹ * val e₀ d α (jIn α (swN W)) * hElt E = val e₀ d α (jOut α (swN W')) := by
  have hpm : pw α k hWord ∈ NG α k := pw_mem α k hWord
  have hm : Rep 16 (nwT α k hWord) (pw α k hWord) := rep_pw D hWord
  have hmi : Rep 16 (invT 16 (nwT α k hWord)) (pw α k hWord)⁻¹ :=
    rep_invT_of_rep (by norm_num) hm
  have hconj := rep_conjT (by norm_num) hmi (rep_sTab D W)
  have hconjN : (pw α k hWord)⁻¹ * wp α k (jOut α (swN W)) * ((pw α k hWord)⁻¹)⁻¹ ∈ NG α k :=
    (NG α k).mul_mem ((NG α k).mul_mem ((NG α k).inv_mem hpm) (wp_mem α k _))
      ((NG α k).inv_mem ((NG α k).inv_mem hpm))
  unfold chainOK at h
  have h1 := (tblEq_ψ E hconj (rep_jTab D W') hconjN (wp_mem α k _)).1 h
  rw [ψ_conj E ((NG α k).inv_mem hpm) (wp_mem α k _), ψ_inv E hpm, inv_inv, ψ_wp, ψ_wp] at h1
  have hs := sigma_conj D.hα D.hsig E.hrel (swN W)
  have hs' := sigma_conj D.hα D.hsig E.hrel (swN W')
  calc (hElt E)⁻¹ * val e₀ d α (jIn α (swN W)) * hElt E
      = (gen4 e₀ d 4)⁻¹ * (ψ E (pw α k hWord))⁻¹ *
          ((gen4 e₀ d 4)⁻¹ * val e₀ d α (jIn α (swN W)) * gen4 e₀ d 4) *
          ψ E (pw α k hWord) * gen4 e₀ d 4 := by unfold hElt; group
    _ = (gen4 e₀ d 4)⁻¹ * ((ψ E (pw α k hWord))⁻¹ * val e₀ d α (jOut α (swN W)) *
          ψ E (pw α k hWord)) * gen4 e₀ d 4 := by rw [hs]; group
    _ = (gen4 e₀ d 4)⁻¹ * val e₀ d α (jIn α (swN W')) * gen4 e₀ d 4 := by rw [h1]
    _ = val e₀ d α (jOut α (swN W')) := hs'

structure L8Chain (E : NEmb e₀ d 1 k) : Prop where
  comm_c : hElt E * cG e₀ = cG e₀ * hElt E
  y0 : ⁅y0G e₀ d 1, hElt E⁆ ≠ 1 ∧ ⁅y0G e₀ d 1, hElt E⁆ ≠ cG e₀
  v2 : (hElt E)⁻¹ * v2G E * hElt E ∉ EG E

theorem l8Chain_spec (D : FusionData 1 k) (E : NEmb e₀ d 1 k) (hue : ueCheck 1 k = true)
    (h : l8Chain 1 k (tenum (wgens 1 k eWords)).toList = true) : L8Chain E := by
  obtain ⟨hEs, -⟩ := ueCheck_enum hue
  unfold l8Chain at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have hcmatch : jIn 1 (swN [1]) = swN cWord := by decide
  have hv2match : jIn 1 (swN [3]) = swN [2, 4] := by decide
  have hrc : Rep 16 (nwT 1 k cWord) (pw 1 k cWord) := rep_pw D cWord
  have hpc := pw_mem 1 k cWord
  have hψc : ψ E (pw 1 k cWord) = cG e₀ := ψ_c E
  have e1 := hElt_conj D E h1
  rw [hcmatch, val_c] at e1
  have e2 : val e₀ d 1 (jOut 1 (swN [1, 2])) = cG e₀ := by
    have := (tblEq_ψ E (rep_sTab D [1, 2]) hrc (wp_mem 1 k _) hpc).1 h2
    rw [ψ_wp, hψc] at this
    exact this
  rw [e2] at e1
  have hcomm : hElt E * cG e₀ = cG e₀ * hElt E := by
    calc hElt E * cG e₀ = hElt E * ((hElt E)⁻¹ * cG e₀ * hElt E) := by rw [e1]
      _ = cG e₀ * hElt E := by group
  have e3 := hElt_conj D E h3
  have hy0r := rep_jTab D [7, 8]
  have hy0m := wp_mem 1 k (jIn 1 (swN [7, 8]))
  have hψy0 : ψ E (wp 1 k (jIn 1 (swN [7, 8]))) = y0G e₀ d 1 := ψ_wp E _
  have hne1 : val e₀ d 1 (jOut 1 (swN (hChainWords k).1)) ≠ y0G e₀ d 1 := by
    intro heq
    have := (tblEq_ψ E (rep_sTab D _) hy0r (wp_mem 1 k _) hy0m).2 (by rw [ψ_wp, heq, hψy0])
    rw [h4] at this
    exact Bool.false_ne_true this
  have hne2 : val e₀ d 1 (jOut 1 (swN (hChainWords k).1)) ≠ cG e₀ * y0G e₀ d 1 := by
    intro heq
    have := (tblEq_ψ E (rep_sTab D _) (hrc.compT hy0r) (wp_mem 1 k _)
      ((NG 1 k).mul_mem hpc hy0m)).2 (by
        rw [ψ_wp, heq, ψ_mul E hpc hy0m, hψc, hψy0])
    rw [h5] at this
    exact Bool.false_ne_true this
  have hy0 : ⁅y0G e₀ d 1, hElt E⁆ ≠ 1 ∧ ⁅y0G e₀ d 1, hElt E⁆ ≠ cG e₀ := by
    refine ⟨fun h0 => hne1 ?_, fun h0 => hne2 ?_⟩
    · have hc : y0G e₀ d 1 * hElt E = hElt E * y0G e₀ d 1 :=
        commutatorElement_eq_one_iff_mul_comm.1 h0
      rw [← e3]
      show (hElt E)⁻¹ * y0G e₀ d 1 * hElt E = y0G e₀ d 1
      rw [mul_assoc, hc]
      group
    · have h0' : y0G e₀ d 1 * hElt E * (y0G e₀ d 1)⁻¹ * (hElt E)⁻¹ = cG e₀ := h0
      have hyh : y0G e₀ d 1 * hElt E = cG e₀ * hElt E * y0G e₀ d 1 := by
        calc y0G e₀ d 1 * hElt E
            = (y0G e₀ d 1 * hElt E * (y0G e₀ d 1)⁻¹ * (hElt E)⁻¹) * hElt E * y0G e₀ d 1 := by
              group
          _ = cG e₀ * hElt E * y0G e₀ d 1 := by rw [h0']
      rw [← e3]
      show (hElt E)⁻¹ * y0G e₀ d 1 * hElt E = cG e₀ * y0G e₀ d 1
      calc (hElt E)⁻¹ * y0G e₀ d 1 * hElt E
          = (hElt E)⁻¹ * (cG e₀ * hElt E * y0G e₀ d 1) := by rw [mul_assoc, hyh]
        _ = (hElt E)⁻¹ * (hElt E * cG e₀ * y0G e₀ d 1) := by rw [hcomm]
        _ = cG e₀ * y0G e₀ d 1 := by group
  have e4 := hElt_conj D E h6
  rw [hv2match, show val e₀ d 1 (swN [2, 4]) = v2G E from (ψ_pw E [2, 4]).symm] at e4
  refine ⟨hcomm, hy0, ?_⟩
  rw [e4]
  intro hmem
  rw [← ψ_wp E] at hmem
  have := (memTab_iff_mem_img E hEs (rep_sTab D _) (wp_mem 1 k _)).2 hmem
  rw [this] at h7
  exact absurd h7 (by decide)

theorem l8Fact_spec (D : FusionData α k) (E : NEmb e₀ d α k) (he2 : orderOf e = 2)
    (h : l8Fact (nEnum α k) (nwT α k eWord) = true) :
    ∀ y ∈ HcG e₀, orderOf y = 3 → ∃ z ∈ HcG e₀, z * y * z⁻¹ ∉ Subgroup.zpowers y := by
  intro y hy hy3
  have hre : Rep 16 (nwT α k eWord) (pw α k eWord) := rep_pw D eWord
  have hpe : pw α k eWord ∈ NG α k := pw_mem α k eWord
  have hψe : ψ E (pw α k eWord) = e := ψ_e E he2
  obtain ⟨g, hg, rfl⟩ := exists_ψ E (HcG_le_Nn e₀ hy)
  obtain ⟨T, hT, hrep⟩ := (nEnum_spec D.hnC).exists_entry (g := g)
    (by rw [closure_nGens_eq D.hsz]; exact hg)
  have hyc : ψ E g * e = e * ψ E g := mem_centralizer_singleton_iff.1 hy.1
  have hTcomm : commTT 16 (nwT α k eWord) T = true := by
    refine (commTT_ψ E hre hrep hpe hg).2 ?_
    rw [hψe]
    exact hyc.symm
  have hT3 : tblEq 16 (compT 16 T (compT 16 T T)) (idT 16) = true := by
    refine (tblEq_idT_ψ E (hrep.compT (hrep.compT hrep))
      ((NG α k).mul_mem hg ((NG α k).mul_mem hg hg))).2 ?_
    rw [ψ_mul E hg ((NG α k).mul_mem hg hg), ψ_mul E hg hg]
    have := pow_orderOf_eq_one (ψ E g)
    rw [hy3] at this
    simpa [pow_succ, mul_assoc] using this
  have hT1 : tblEq 16 T (idT 16) = false := by
    rw [Bool.eq_false_iff]
    intro h1
    have := (tblEq_idT_ψ E hrep hg).1 h1
    rw [this, orderOf_one] at hy3
    omega
  unfold l8Fact at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨-, h2⟩ := h
  have hmemH : T ∈ (nEnum α k).toList.filter (commTT 16 (nwT α k eWord)) :=
    List.mem_filter.2 ⟨Array.mem_toList_iff.2 hT, hTcomm⟩
  obtain ⟨z', hz', hz⟩ := List.any_eq_true.1
    (h2 T (List.mem_filter.2 ⟨hmemH, by rw [hT3, hT1]; rfl⟩))
  obtain ⟨hz'L, hz'c⟩ := List.mem_filter.1 hz'
  obtain ⟨hrz, hmz⟩ := (nEnum_spec D.hnC).rep_mem (Array.mem_toList_iff.1 hz'L)
  have hgz : tablePerm 16 z' ∈ NG α k := by
    rw [← closure_nGens_eq D.hsz]
    exact hmz
  have hzHc : ψ E (tablePerm 16 z') ∈ HcG e₀ := by
    rw [← Nn_inf_centralizer]
    refine ⟨ψ_mem_Nn E hgz, mem_centralizer_singleton_iff.2 ?_⟩
    have := (commTT_ψ E hre hrz hpe hgz).1 hz'c
    rw [hψe] at this
    exact this.symm
  refine ⟨ψ E (tablePerm 16 z'), hzHc, fun hmem => ?_⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hn3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  have hpow : ψ E g ^ (n % 3) = ψ E g ^ n := by
    have := zpow_mod_orderOf (ψ E g) n
    rw [hy3] at this
    exact_mod_cast this
  have hconjrep : Rep 16 (conjT 16 z' T) (tablePerm 16 z' * g * (tablePerm 16 z')⁻¹) :=
    rep_conjT (by norm_num) hrz hrep
  have hconjN : tablePerm 16 z' * g * (tablePerm 16 z')⁻¹ ∈ NG α k :=
    (NG α k).mul_mem ((NG α k).mul_mem hgz hg) ((NG α k).inv_mem hgz)
  have hψconj : ψ E (tablePerm 16 z' * g * (tablePerm 16 z')⁻¹) =
      ψ E (tablePerm 16 z') * ψ E g * (ψ E (tablePerm 16 z'))⁻¹ := ψ_conj E hgz hg
  have hmemtab : memTab 16 [idT 16, T, compT 16 T T] (conjT 16 z' T) = true := by
    unfold memTab
    rw [List.any_eq_true]
    rcases hn3 with h0 | h1 | h2
    · refine ⟨idT 16, by simp, ?_⟩
      refine (tblEq_ψ E (Rep.idT (by norm_num)) hconjrep (NG α k).one_mem hconjN).2 ?_
      rw [ψ_one, hψconj, ← hn, ← hpow, h0]
      simp
    · refine ⟨T, by simp, ?_⟩
      refine (tblEq_ψ E hrep hconjrep hg hconjN).2 ?_
      rw [hψconj, ← hn, ← hpow, h1]
      simp
    · refine ⟨compT 16 T T, by simp, ?_⟩
      refine (tblEq_ψ E (hrep.compT hrep) hconjrep ((NG α k).mul_mem hg hg) hconjN).2 ?_
      rw [ψ_mul E hg hg, hψconj, ← hn, ← hpow, h2]
      simp [pow_two]
  rw [hmemtab] at hz
  exact absurd hz (by decide)

theorem l8ZN_spec (D : FusionData α k) (E : NEmb e₀ d α k) (hue : ueCheck α k = true)
    (h : l8ZN (nEnum α k) (nwT α k cWord) (jTab α k [7, 8])
      (tenum (wgens α k eWords)).toList = true) :
    ∀ y ∈ EG E, (∀ n ∈ Nn e₀, ⁅y, n⁆ = 1 ∨ ⁅y, n⁆ = cG e₀) →
      y = 1 ∨ y = cG e₀ ∨ y = y0G e₀ d α ∨ y = y0G e₀ d α * cG e₀ := by
  intro y hy hcomm
  obtain ⟨hEs, -⟩ := ueCheck_enum hue
  have hELe : tsub (wgens α k eWords) ≤ NG α k := tsub_wgens_le D hEs.perm
  obtain ⟨T, hT, rfl, hrepT, hgT⟩ := exists_entry_of_mem_img E hEs hELe hy
  have hrc : Rep 16 (nwT α k cWord) (pw α k cWord) := rep_pw D cWord
  have hpc := pw_mem α k cWord
  have hψc : ψ E (pw α k cWord) = cG e₀ := ψ_c E
  have hy0r := rep_jTab D [7, 8]
  have hy0m := wp_mem α k (jIn α (swN [7, 8]))
  have hψy0 : ψ E (wp α k (jIn α (swN [7, 8]))) = y0G e₀ d α := ψ_wp E _
  unfold l8ZN at h
  have h1 := List.all_eq_true.1 h T (Array.mem_toList_iff.2 hT)
  have hall : (nEnum α k).all (commIn 16 (nwT α k cWord) T) = true := by
    rw [Array.all_eq_true']
    intro T' hT'
    obtain ⟨hrep', hmem'⟩ := (nEnum_spec D.hnC).rep_mem hT'
    have hg' : tablePerm 16 T' ∈ NG α k := by
      rw [← closure_nGens_eq D.hsz]
      exact hmem'
    refine (commIn_ψ E hrc hrepT hrep' hpc hgT hg').2 ?_
    rw [hψc]
    exact hcomm _ (ψ_mem_Nn E hg')
  rw [hall] at h1
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at h1
  rcases h1 with ((h1 | h1) | h1) | h1
  · exact Or.inl ((tblEq_idT_ψ E hrepT hgT).1 h1)
  · exact Or.inr (Or.inl (((tblEq_ψ E hrepT hrc hgT hpc).1 h1).trans hψc))
  · exact Or.inr (Or.inr (Or.inl (((tblEq_ψ E hrepT hy0r hgT hy0m).1 h1).trans hψy0)))
  · refine Or.inr (Or.inr (Or.inr ?_))
    have := (tblEq_ψ E hrepT (hy0r.compT hrc) hgT ((NG α k).mul_mem hy0m hpc)).1 h1
    rw [ψ_mul E hy0m hpc, hψy0, hψc] at this
    exact this

end Lemma8

end CFSG.EvenSporadicStandard.M12Std.Yosh
