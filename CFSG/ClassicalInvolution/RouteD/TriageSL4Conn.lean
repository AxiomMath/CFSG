module

public import CFSG.ClassicalInvolution.RouteD.TriageSL4Closure
public import CFSG.ClassicalInvolution.RouteD.TriageSL4Local

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.Generic.CoreAssembly
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutes_iSup_of_commutes {ι : Type*} (A : Subgroup G) (B : ι → Subgroup G)
    (h : ∀ i, Commutes A (B i)) : Commutes A (⨆ i, B i) := by
  intro a ha y hy
  have hle : (⨆ i, B i) ≤ Subgroup.centralizer ({a} : Set G) := iSup_le fun i b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h i a ha b hb).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm

theorem not_commutes_of_twinSL4 [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    {K : Subgroup G} {z : G} (S : RouteDSetup p f K z)
    (hshape : LocalShapeT p f 2 .PSL 4 (conjClass K) z) {β : Subgroup G}
    (hβ : β ∈ conjClass K) {t : G} (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) (j : Fin 3 → Subgroup G)
    (hjΩ : ∀ a, j a ∈ conjClass K) (hjK : ∀ a, Commutes K (j a))
    (hjβ : ∀ a : Fin 3, 1 ≤ a.val → Commutes β (j a)) (hj12 : Commutes (j 1) (j 2))
    (hp01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W (j 0) (j 1))
    (hp02 : ∃ W, LinearBlockStandardPair (GaloisField p f) W (j 0) (j 2)) :
    ¬ Commutes β (j 0) := by
  intro hβ0
  classical
  have hΩ : InClass p f (conjClass K) := S.inClass
  have hex := S.exact
  have hsingle : ∀ L ∈ conjClass K, ∃ g : G, L = conjSub g K := single_class K
  have hKΩ : K ∈ conjClass K := mem_conjClass_self K
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f S.odd
  have hq4 : 4 ≤ p ^ f := by have := S.five; omega
  obtain ⟨c⟩ := TCtx.nonempty_A3 S.odd S.five hΩ hex hKΩ S.cls S.p1 hshape
  have hD1 : ∀ L ∈ centralizingMembers (conjClass K) {z}, L ≠ K → Commutes K L :=
    fun L hL hLK => c.commutes_K_of_ne hL hLK
  have hne : ∀ {A B : Subgroup G}, A ∈ conjClass K → Commutes A B → A ≠ B := by
    intro A B hA hAB hAeq
    subst hAeq
    exact not_commutes_self_of_mem hΩ hA hAB
  have hjz : ∀ a, j a ∈ centralizingMembers (conjClass K) {z} := fun a =>
    mem_centralizingMembers_of_commutes (hjΩ a) S.cls.mem (hjK a).symm
  have hjKne : ∀ a, j a ≠ K := fun a h => hne hKΩ (hjK a) h.symm
  obtain ⟨W₀₁, hW₀₁⟩ := hp01
  obtain ⟨W₀₂, hW₀₂⟩ := hp02
  have hnc01 : ¬ Commutes (j 0) (j 1) := not_commutes_of_linearBlockStandardPair hW₀₁
  have hnc02 : ¬ Commutes (j 0) (j 2) := not_commutes_of_linearBlockStandardPair hW₀₂
  have hne01 : j 0 ≠ j 1 := ne_of_linearBlockStandardPair hW₀₁
  have hne02 : j 0 ≠ j 2 := ne_of_linearBlockStandardPair hW₀₂
  have hjQ : ∀ a : Fin 3, ¬ locImg (conjClass K) z (j a) ≤ c.d.Q₁ := by
    intro a
    fin_cases a
    · exact fun hQ => hnc01 (c.commutes_T_of_ne (hjz 0) hQ (hjz 1) hne01.symm)
    · exact fun hQ => hnc01 (c.commutes_T_of_ne (hjz 1) hQ (hjz 0) hne01).symm
    · exact fun hQ => hnc02 (c.commutes_T_of_ne (hjz 2) hQ (hjz 0) hne02).symm
  obtain ⟨T, hTz, hTimg⟩ := c.exists_twin
  have hTK : T ≠ K := c.twin_ne hTz hTimg.le
  have hTΩ : T ∈ conjClass K := hTz.1
  have hKT : Commutes K T := c.commutes_K_of_ne hTz hTK
  have hTj : ∀ a, j a ≠ T := fun a h => hjQ a (by rw [h]; exact hTimg.le)
  have hTcomm : ∀ N ∈ centralizingMembers (conjClass K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => c.commutes_T_of_ne hTz hTimg.le hN hNT
  set P : Set (Subgroup G) := commNbhd (conjClass K) K \ {T} with hPdef
  set Q : Set (Subgroup G) := {M | M ∈ conjClass K ∧ ∀ N ∈ P, Commutes N M} with hQdef
  have hPmem : ∀ {N : Subgroup G}, N ∈ P → N ∈ conjClass K ∧ Commutes K N ∧ N ≠ T :=
    fun hN => ⟨hN.1.1, hN.1.2, hN.2⟩
  have hPz : ∀ {N : Subgroup G}, N ∈ P →
      N ∈ centralizingMembers (conjClass K) {z} ∧ N ≠ K ∧ ¬ locImg (conjClass K) z N ≤ c.d.Q₁ := by
    intro N hN
    obtain ⟨hNΩ, hKN, hNT⟩ := hPmem hN
    exact ⟨mem_centralizingMembers_of_commutes hNΩ S.cls.mem hKN.symm,
      fun h => hne hKΩ hKN h.symm,
      fun hQ => hNT (c.eq_of_locImg_le_Q₁ (mem_centralizingMembers_of_commutes hNΩ S.cls.mem
        hKN.symm) hTz hQ hTimg.le)⟩
  have hjP : ∀ a, j a ∈ P := fun a => ⟨⟨hjΩ a, hjK a⟩, hTj a⟩
  have hPne : P.Nonempty := ⟨j 0, hjP 0⟩
  have hPΩ : P ⊆ conjClass K := fun N hN => hN.1.1
  have hQΩ : Q ⊆ conjClass K := fun M hM => hM.1
  have hKQ : K ∈ Q := ⟨hKΩ, fun N hN => (hPmem hN).2.1.symm⟩
  have hPQ : ∀ N ∈ P, ∀ M ∈ Q, Commutes N M := fun N hN M hM => hM.2 N hN
  have hν := ncard_commNbhd_add_one h2 hΩ hex hsingle S.cls hD1 hKΩ
  have hTin : T ∈ commNbhd (conjClass K) K := ⟨hTΩ, hKT⟩
  have hPcard : (centralizingMembers (conjClass K) {z}).ncard ≤ P.ncard + 2 := by
    have := Set.ncard_sdiff_singleton_add_one hTin (Set.toFinite (commNbhd (conjClass K) K))
    rw [← hPdef] at this
    omega
  have hPstruct : ∀ N ∈ P, (∃ N' ∈ P, Commutes N N') ∧ ∃ N'' ∈ P, N'' ≠ N ∧ ¬ Commutes N N'' := by
    intro N hN
    obtain ⟨hNz, hNK, hNQ⟩ := hPz hN
    obtain ⟨R, hR, hNR⟩ := c.exists_fund_of_ne hNz hNK hNQ
    obtain ⟨R', hR', hRR'⟩ := exists_commuting_fund_sl4 hq4 hR
    obtain ⟨N', hN'z, hN'K, hN'Q, hN'R⟩ := c.exists_member_of_fund hR'
    have hN'P : N' ∈ P := ⟨⟨hN'z.1, c.commutes_K_of_ne hN'z hN'K⟩, fun h => hN'Q (by
      rw [h]; exact hTimg.le)⟩
    have hNN' : Commutes N N' := (c.commutes_iff_fund hNz hN'z hR hNR hN'R).mpr hRR'
    refine ⟨⟨N', hN'P, hNN'⟩, ?_⟩
    have hRR'ne : R' ≠ R := by
      intro h
      subst h
      exact not_commutes_self_of_mem hΩ hNz.1
        ((c.commutes_iff_fund hNz hNz hR' hNR hNR).mpr hRR')
    obtain ⟨R_c, hR_c, ⟨W₁, hW₁⟩, -⟩ := exists_centre_sl4 S.odd hq4 hR hR' hRR'ne
      (fun h => not_commutes_self_of_mem hΩ hNz.1 ((c.commutes_iff_fund hNz hNz hR hNR hNR).mpr h))
      hRR'
    obtain ⟨N'', hN''z, hN''K, hN''Q, hN''R⟩ := c.exists_member_of_fund hR_c
    have hN''P : N'' ∈ P := ⟨⟨hN''z.1, c.commutes_K_of_ne hN''z hN''K⟩, fun h => hN''Q (by
      rw [h]; exact hTimg.le)⟩
    obtain ⟨V, hV⟩ := c.stdPair_of_fund hN''z hNz hW₁ hN''R hNR
    exact ⟨N'', hN''P, ne_of_linearBlockStandardPair hV,
      fun h => not_commutes_of_linearBlockStandardPair hV h.symm⟩
  have hβP : ∀ N ∈ P, Commutes β N := by
    intro N hN
    obtain ⟨hNz, hNK, hNQ⟩ := hPz hN
    have hle := c.le_iSup_of_chain (L := ![j 1, j 0, j 2])
      (fun k => by fin_cases k <;> simp [hjz]) (fun k => by fin_cases k <;> simp [hjKne])
      (fun k => by fin_cases k <;> simp [hjQ]) (by simpa using hj12)
      ⟨_, CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_symm hW₀₁⟩ ⟨_, hW₀₂⟩ hNz hNK
      hNQ
    have hc : Commutes β (⨆ k, ![j 1, j 0, j 2] k) :=
      commutes_iSup_of_commutes β _ (fun k => by
        fin_cases k
        · exact hjβ 1 (by decide)
        · exact hβ0
        · exact hjβ 2 (by decide))
    exact fun b hb n hn => hc b hb n (hle hn)
  obtain ⟨x₀, hx₀⟩ := hΩ.classical (j 1) (hjΩ 1)
  have hS0 : commNbhd (conjClass K) (j 1) \ {j 2} ⊆ Q := by
    intro M hM
    obtain ⟨⟨hMΩ, hMj1⟩, hMj2⟩ := hM
    refine ⟨hMΩ, fun N hN => ?_⟩
    obtain ⟨hNz, hNK, hNQ⟩ := hPz hN
    have hMle := layer_le_sup_of_chain S hshape hβ ht hKβ (j₁ := j 1) (j₂ := j 2) (T := T)
      (hjΩ 1) (hjΩ 2) hTΩ (hjK 1) (hjK 2) hKT (hjβ 1 (by decide)) (hjβ 2 (by decide)) hj12
      (hTcomm (j 1) (hjz 1) (hTj 1)) (fun h => hTj 2 h.symm) hx₀ hMΩ hMj1 hMj2
    have hN' : Commutes N (K ⊔ β ⊔ T) :=
      commutes_join_of_commutes (commutes_join_of_commutes (hPmem hN).2.1.symm (hβP N hN).symm)
        (hTcomm N hNz (hPmem hN).2.2).symm
    exact fun a ha m hm => hN' a ha m (hMle hm)
  have hj2in : j 2 ∈ commNbhd (conjClass K) (j 1) := ⟨hjΩ 2, hj12⟩
  have hν1 := ncard_commNbhd_add_one h2 hΩ hex hsingle S.cls hD1 (hjΩ 1)
  have hQcard : (centralizingMembers (conjClass K) {z}).ncard ≤ Q.ncard + 2 := by
    have h1 := Set.ncard_sdiff_singleton_add_one hj2in (Set.toFinite (commNbhd (conjClass K) (j 1)))
    have h3 := Set.ncard_le_ncard hS0 (Set.toFinite Q)
    omega
  have hQpart : ∀ M ∈ Q, ∃ M' ∈ Q, Commutes M M' := by
    intro M hM
    obtain ⟨y, hy⟩ := hΩ.classical M hM.1
    obtain ⟨cx⟩ := Gaps.exists_ctx_member c hsingle hshape hM.1 hy
    obtain ⟨TM, hTMy, hTMimg⟩ := cx.exists_twin
    have hTMM : TM ≠ M := cx.twin_ne hTMy hTMimg.le
    have hMTM : Commutes M TM := cx.commutes_K_of_ne hTMy hTMM
    have hPy : ∀ N ∈ P, N ∈ centralizingMembers (conjClass K) {y} := fun N hN =>
      mem_centralizingMembers_of_commutes (hPmem hN).1 hy.mem (hM.2 N hN)
    have hNTM : ∀ N ∈ P, N ≠ TM := by
      intro N hN hNeq
      obtain ⟨-, N'', hN''P, hN''ne, hN''nc⟩ := hPstruct N hN
      refine hN''nc ?_
      rw [hNeq]
      exact cx.commutes_T_of_ne hTMy hTMimg.le (hPy N'' hN''P) (by rw [← hNeq]; exact hN''ne)
    exact ⟨TM, ⟨hTMy.1, fun N hN =>
      (cx.commutes_T_of_ne hTMy hTMimg.le (hPy N hN) (hNTM N hN)).symm⟩, hMTM⟩
  exact false_of_bipartite hnab h2 hΩ S.conn hex hsingle S.cls hD1 hPΩ hQΩ hPne ⟨K, hKQ⟩ hPQ
    hPcard hQcard (fun N hN => (hPstruct N hN).1) hQpart

end CFSG.ClassicalInvolution.RouteD
