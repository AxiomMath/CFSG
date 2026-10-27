module

public import CFSG.ClassicalInvolution.RouteD.TypeAChain
public import CFSG.ClassicalInvolution.WeakCT.DLDiagrams
public import CFSG.Timmesfeld.RankTwo.LevisExceptional

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

structure IsPartnerE (c : ACtx p f 5 Ω K z) (nd : Nodes c) (β : Subgroup G) : Prop where
  mem : β ∈ Ω
  cl : ∃ wβ : G, IsClassicalMember p f β wβ
  nK : ¬ Commutes K β
  pK : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β
  n0 : ¬ Commutes β (nd.j 0)
  p0 : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (nd.j 0)
  last : Commutes β (nd.j 4)
  mid : ∀ a, 1 ≤ a → a ≤ 2 → Commutes β (nd.j a)

theorem ACtx.exists_partnerE (c : ACtx p f 5 Ω K z) (nd : Nodes c)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) : ∃ β, IsPartnerE c nd β := by
  obtain ⟨β, hβ, hcl, hnK, hpK, hn0, hp0, hlast, hmid⟩ := c.exists_partner nd (by norm_num) hsingle
  exact ⟨β, ⟨hβ, hcl, hnK, hpK, hn0, hp0, hlast, hmid⟩⟩

theorem ACtx.commutes_or_stdpair_end (c : ACtx p f 5 Ω K z) (nd : Nodes c)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {β : Subgroup G} (hβ : IsPartnerE c nd β)
    {wβ : G} (hwβ : IsClassicalMember p f β wβ) (hcomm : Commute wβ (nd.w 3)) :
    Commutes β (nd.j 3) ∨ ∃ W : Subgroup G,
      LinearBlockStandardPair (GaloisField p f) W β (nd.j 3) := by
  obtain ⟨g, hg⟩ := hsingle (nd.j 1) (nd.mem 1 (by norm_num)).1
  have hβZ : Commutes β (nd.j 1) := hβ.mid 1 le_rfl (by norm_num)
  have hβne : β ≠ nd.j 1 := by
    intro h
    exact hβ.nK (h ▸ nd.commK 1 (by norm_num))
  have h3Z : Commutes (nd.j 3) (nd.j 1) := (nd.far 1 (by norm_num) 3 (by norm_num) (by norm_num)).symm
  have h3ne : nd.j 3 ≠ nd.j 1 := nd.inj 3 (by norm_num) 1 (by norm_num) (by norm_num)
  obtain ⟨hβm, hβne', Rb, ib, hRb, hβR, hyb, hib⟩ :=
    c.exists_rootData_conj hg hβ.mem hβZ hβne hwβ
  obtain ⟨h3m, h3ne', R3, i3, hR3, h3R, hy3, hi3⟩ :=
    c.exists_rootData_conj hg (nd.mem 3 (by norm_num)).1 h3Z h3ne (nd.isCl 3 (by norm_num))
  have hne : conjSub g⁻¹ β ≠ conjSub g⁻¹ (nd.j 3) := by
    intro h
    have h' : β = nd.j 3 := conjSub_injective g⁻¹ h
    have h4 : Commutes (nd.j 3) (nd.j 4) := h' ▸ hβ.last
    exact nd.adj 3 (by norm_num) h4
  have hclβ : IsClassicalMember p f (conjSub g⁻¹ β) (g⁻¹ * wβ * g) := by
    have := IsClassicalMember.conj hwβ g⁻¹
    rwa [inv_inv] at this
  have hcl3 : IsClassicalMember p f (conjSub g⁻¹ (nd.j 3)) (g⁻¹ * nd.w 3 * g) := by
    have := IsClassicalMember.conj (nd.isCl 3 (by norm_num)) g⁻¹
    rwa [inv_inv] at this
  have hc : g⁻¹ * wβ * g * (g⁻¹ * nd.w 3 * g) = g⁻¹ * nd.w 3 * g * (g⁻¹ * wβ * g) := by
    calc g⁻¹ * wβ * g * (g⁻¹ * nd.w 3 * g) = g⁻¹ * (wβ * nd.w 3) * g := by group
      _ = g⁻¹ * (nd.w 3 * wβ) * g := by rw [hcomm.eq]
      _ = g⁻¹ * nd.w 3 * g * (g⁻¹ * wβ * g) := by group
  rcases c.rel_dichotomy hβm h3m hβne' h3ne' hne hclβ hcl3 hc with h | ⟨W, hW⟩
  · left
    exact (commutes_conjSub_iff g⁻¹).mp h
  · right
    refine ⟨conjSub g W, ?_⟩
    have := linearBlockStandardPair_conjSub hW g
    rwa [conjSub_conjSub_inv, conjSub_conjSub_inv] at this


omit [Finite G] in
theorem ACtx.chain_A7 (c : ACtx p f 5 Ω K z) (nd : Nodes c) {β : Subgroup G}
    (hβ : IsPartnerE c nd β) (h3 : Commutes β (nd.j 3)) :
    ∃ U : Fin 7 → Subgroup G, (∀ i, U i ∈ Ω) ∧
      (∀ i j : Fin 7, (i : ℕ) + 1 < j → Commutes (U i) (U j)) ∧
      (∀ i j : Fin 7, (j : ℕ) = i + 1 →
        ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) := by
  refine ⟨![K, β, nd.j 0, nd.j 1, nd.j 2, nd.j 3, nd.j 4], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact c.hK
    · exact hβ.mem
    all_goals exact (nd.mem _ (by norm_num)).1
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact nd.commK 0 (by norm_num)
    · exact nd.commK 1 (by norm_num)
    · exact nd.commK 2 (by norm_num)
    · exact nd.commK 3 (by norm_num)
    · exact nd.commK 4 (by norm_num)
    · exact hβ.mid 1 le_rfl (by norm_num)
    · exact hβ.mid 2 (by norm_num) le_rfl
    · exact h3
    · exact hβ.last
    · exact nd.far 0 (by norm_num) 2 (by norm_num) (by norm_num)
    · exact nd.far 0 (by norm_num) 3 (by norm_num) (by norm_num)
    · exact nd.far 0 (by norm_num) 4 (by norm_num) (by norm_num)
    · exact nd.far 1 (by norm_num) 3 (by norm_num) (by norm_num)
    · exact nd.far 1 (by norm_num) 4 (by norm_num) (by norm_num)
    · exact nd.far 2 (by norm_num) 4 (by norm_num) (by norm_num)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact hβ.pK
    · exact hβ.p0
    · exact nd.pair 0 (by norm_num)
    · exact nd.pair 1 (by norm_num)
    · exact nd.pair 2 (by norm_num)
    · exact nd.pair 3 (by norm_num)


omit [Finite G] in
theorem ACtx.chain_E6 (c : ACtx p f 5 Ω K z) (nd : Nodes c) {β : Subgroup G}
    (hβ : IsPartnerE c nd β)
    (h3 : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (nd.j 3)) :
    ∃ U : Fin 6 → Subgroup G, (∀ i, U i ∈ Ω) ∧
      (∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i → Commutes (U i) (U j)) ∧
      (∀ i j : Fin 6, edgeE 6 i j →
        ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) := by
  refine ⟨![nd.j 1, K, nd.j 0, β, nd.j 3, nd.j 4], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact (nd.mem 1 (by norm_num)).1
    · exact c.hK
    · exact (nd.mem 0 (by norm_num)).1
    · exact hβ.mem
    all_goals exact (nd.mem _ (by norm_num)).1
  · intro i j hij h1 h2
    have e0 := nd.commK 0 (by norm_num)
    have e1 := nd.commK 1 (by norm_num)
    have e3 := nd.commK 3 (by norm_num)
    have e4 := nd.commK 4 (by norm_num)
    have b1 := hβ.mid 1 le_rfl (by norm_num)
    have b4 := hβ.last
    have f13 := nd.far 1 (by norm_num) 3 (by norm_num) (by norm_num)
    have f14 := nd.far 1 (by norm_num) 4 (by norm_num) (by norm_num)
    have f03 := nd.far 0 (by norm_num) 3 (by norm_num) (by norm_num)
    have f04 := nd.far 0 (by norm_num) 4 (by norm_num) (by norm_num)
    fin_cases i <;> fin_cases j <;> simp [edgeE] at hij h1 h2 ⊢
    all_goals first
      | exact e0 | exact e0.symm | exact e1 | exact e1.symm | exact e3 | exact e3.symm
      | exact e4 | exact e4.symm | exact b1 | exact b1.symm | exact b4 | exact b4.symm
      | exact f13 | exact f13.symm | exact f14 | exact f14.symm | exact f03 | exact f03.symm
      | exact f04 | exact f04.symm
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [edgeE] at hij ⊢
    all_goals first
      | (obtain ⟨W, hW⟩ := nd.pair 0 (by norm_num); exact ⟨W, hW.symm⟩)
      | exact hβ.pK
      | (obtain ⟨W, hW⟩ := hβ.p0; exact ⟨W, hW.symm⟩)
      | exact h3
      | exact nd.pair 3 (by norm_num)


theorem ACtx.exists_partnerMid {m : ℕ} (c : ACtx p f m Ω K z) (nd : Nodes c) (hm : 4 ≤ m)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) :
    ∃ β : Subgroup G, β ∈ Ω ∧ (∃ wβ : G, IsClassicalMember p f β wβ) ∧ ¬ Commutes K β ∧
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β) ∧
      ¬ Commutes β (nd.j 2) ∧
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (nd.j 2)) ∧
      Commutes β (nd.j 0) ∧ ∀ a, 3 ≤ a → a < m → Commutes β (nd.j a) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hk : 2 ≤ k := by omega
  have h2 := c.two_ne_zero
  have hMΩ : nd.j 0 ∈ Ω := (nd.mem 0 (by omega)).1
  obtain ⟨g, hg⟩ := hsingle _ hMΩ
  obtain ⟨hK'm, hK'ne, R₀, i₀, hR₀, hKR₀, hy₀, hi₀⟩ := c.exists_rootData_conj hg c.hK
    (nd.commK 0 (by omega)) (nd.ne_K 0 (by omega)).symm c.hz
  have hnode : ∀ a, ∃ (R : Subgroup SL(k + 2 + 1, GaloisField p f))
      (i : SL(k + 2 + 1, GaloisField p f)), a < k →
      (conjSub g⁻¹ (nd.j (a + 2)) ∈ centralizingMembers Ω {z} ∧
        conjSub g⁻¹ (nd.j (a + 2)) ≠ K ∧
        IsLongRootSL2 c.hn R i ∧ locImg Ω z (conjSub g⁻¹ (nd.j (a + 2))) = R.map c.d.ψ ∧
        ∃ hy : g⁻¹ * nd.w (a + 2) * g ∈ locLayer Ω z,
          c.d.ψ i = locElt Ω z (g⁻¹ * nd.w (a + 2) * g) hy) := by
    intro a
    by_cases ha : a < k
    · obtain ⟨h1, h2', R, i, h3, h4, h5⟩ := c.exists_rootData_conj hg (nd.mem (a + 2) (by omega)).1
        (nd.far 0 (by omega) (a + 2) (by omega) (by omega)).symm
        (nd.inj (a + 2) (by omega) 0 (by omega) (by omega)) (nd.isCl (a + 2) (by omega))
      exact ⟨R, i, fun _ => ⟨h1, h2', h3, h4, h5⟩⟩
    · exact ⟨⊥, 1, fun h => absurd h ha⟩
  choose R i hRi using hnode
  have hconjne : ∀ a b, a < k → b < k → a ≠ b →
      conjSub g⁻¹ (nd.j (a + 2)) ≠ conjSub g⁻¹ (nd.j (b + 2)) := fun a b ha hb hab h =>
    nd.inj (a + 2) (by omega) (b + 2) (by omega) (by omega) (conjSub_injective g⁻¹ h)
  have hKne : ∀ a, a < k → conjSub g⁻¹ K ≠ conjSub g⁻¹ (nd.j (a + 2)) := fun a ha h =>
    nd.ne_K (a + 2) (by omega) ((conjSub_injective g⁻¹ h).symm)
  have hR : ∀ a < k, IsLongRootSL2 c.hn (R a) (i a) := fun a ha => (hRi a ha).2.2.1
  have hcomm : ∀ a < k, Commute i₀ (i a) := by
    intro a ha
    obtain ⟨hya, hia⟩ := (hRi a ha).2.2.2.2
    refine (c.commute_of_locElt hK'm (hRi a ha).1 (hKne a ha) hR₀ (hR a ha) hKR₀
      (hRi a ha).2.2.2.1 hy₀ hya hi₀ hia ?_).1
    calc g⁻¹ * z * g * (g⁻¹ * nd.w (a + 2) * g) = g⁻¹ * (z * nd.w (a + 2)) * g := by group
      _ = g⁻¹ * (nd.w (a + 2) * z) * g := by rw [(nd.wz (a + 2) (by omega)).symm]
      _ = g⁻¹ * nd.w (a + 2) * g * (g⁻¹ * z * g) := by group
  have hcomm' : ∀ a < k, ∀ b < k, Commute (i a) (i b) := by
    intro a ha b hb
    by_cases hab : a = b
    · subst hab; exact Commute.refl _
    · obtain ⟨hya, hia⟩ := (hRi a ha).2.2.2.2
      obtain ⟨hyb, hib⟩ := (hRi b hb).2.2.2.2
      refine (c.commute_of_locElt (hRi a ha).1 (hRi b hb).1 (hconjne a b ha hb hab) (hR a ha)
        (hR b hb) (hRi a ha).2.2.2.1 (hRi b hb).2.2.2.1 hya hyb hia hib ?_).1
      calc g⁻¹ * nd.w (a + 2) * g * (g⁻¹ * nd.w (b + 2) * g)
          = g⁻¹ * (nd.w (a + 2) * nd.w (b + 2)) * g := by group
        _ = g⁻¹ * (nd.w (b + 2) * nd.w (a + 2)) * g := by
          rw [nd.wcomm (a + 2) (by omega) (b + 2) (by omega)]
        _ = g⁻¹ * nd.w (b + 2) * g * (g⁻¹ * nd.w (a + 2) * g) := by group
  have hinj : ∀ a < k, ∀ b < k, a ≠ b → i a ≠ i b := fun a ha b hb hab =>
    c.ne_of_rootInv (hRi a ha).1 (hRi b hb).1 (hconjne a b ha hb hab) (hR a ha) (hR b hb)
      (hRi a ha).2.2.2.1 (hRi b hb).2.2.2.1
  have h0ne : ∀ a < k, i₀ ≠ i a := fun a ha =>
    c.ne_of_rootInv hK'm (hRi a ha).1 (hKne a ha) hR₀ (hR a ha) hKR₀ (hRi a ha).2.2.2.1
  have hR0 : ∀ a < k, Commutes R₀ (R a) := fun a ha =>
    (c.commutes_iff_root hK'm (hRi a ha).1 hR₀ hKR₀ (hRi a ha).2.2.2.1).mp
      ((commutes_conjSub_iff g⁻¹).mpr (nd.commK (a + 2) (by omega)))
  have hfar : ∀ a < k, ∀ b < k, a + 2 ≤ b → Commutes (R a) (R b) := fun a ha b hb hab =>
    (c.commutes_iff_root (hRi a ha).1 (hRi b hb).1 (hR a ha) (hRi a ha).2.2.2.1
      (hRi b hb).2.2.2.1).mp
      ((commutes_conjSub_iff g⁻¹).mpr (nd.far (a + 2) (by omega) (b + 2) (by omega) (by omega)))
  have hadj : ∀ a, a + 1 < k → ¬ Commutes (R a) (R (a + 1)) := fun a ha hc' =>
    nd.adj (a + 2) (by omega) ((commutes_conjSub_iff g⁻¹).mp
      ((c.commutes_iff_root (hRi a (by omega)).1 (hRi (a + 1) ha).1 (hR a (by omega))
        (hRi a (by omega)).2.2.2.1 (hRi (a + 1) ha).2.2.2.1).mpr hc'))
  obtain ⟨B, iB, hB, hc0, hne0, hnc0, hc1, hne1, hnc1, hrest⟩ :=
    CFSG.ClassicalInvolution.RouteD.exists_partner h2 hk hR₀ hR hcomm hcomm' hinj h0ne hR0 hfar
      hadj
  obtain ⟨β', hβ'm, hβ'K, hβ'img⟩ := exists_member_of_root c.hm c.hodd c.hΩ c.hK c.hz c.hP1 c.d
    (R := B) ⟨iB, hB⟩
  obtain ⟨wb, hwb⟩ := c.hΩ.classical β' hβ'm.1
  have hnK' : ¬ Commutes (conjSub g⁻¹ K) β' := fun h =>
    hnc0 ((c.commutes_iff_root hK'm hβ'm hR₀ hKR₀ hβ'img).mp h).symm
  have hn0' : ¬ Commutes β' (conjSub g⁻¹ (nd.j 2)) := fun h =>
    hnc1 ((c.commutes_iff_root hβ'm (hRi 0 (by omega)).1 hB hβ'img
      (hRi 0 (by omega)).2.2.2.1).mp h)
  obtain ⟨W1, hW1⟩ := c.stdpair_of_root hK'm hβ'm hR₀ hB hKR₀ hβ'img hc0.symm hne0.symm
    (fun h => hnc0 h.symm)
  obtain ⟨W2, hW2⟩ := c.stdpair_of_root hβ'm (hRi 0 (by omega)).1 hB (hR 0 (by omega)) hβ'img
    (hRi 0 (by omega)).2.2.2.1 hc1 hne1 hnc1
  have hKβ'M : Commutes K β' :=
    commutes_K_of_ne c.hm c.hodd c.hΩ c.hex c.hK c.hz c.hP1 c.d hβ'm hβ'K
  refine ⟨conjSub g β', c.hΩ.conjInvariant g β' hβ'm.1, ⟨_, IsClassicalMember.conj hwb g⟩, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro h
    rw [← conjSub_conjSub_inv g K] at h
    exact hnK' ((commutes_conjSub_iff g).mp h)
  · refine ⟨conjSub g W1, ?_⟩
    have := linearBlockStandardPair_conjSub hW1 g
    rwa [conjSub_conjSub_inv] at this
  · intro h
    rw [← conjSub_conjSub_inv g (nd.j 2)] at h
    exact hn0' ((commutes_conjSub_iff g).mp h)
  · refine ⟨conjSub g W2, ?_⟩
    have := linearBlockStandardPair_conjSub hW2 g
    rwa [conjSub_conjSub_inv] at this
  · rw [hg]
    exact (commutes_conjSub_iff g).mpr hKβ'M.symm
  · intro a ha3 ha
    have hc' : Commutes β' (conjSub g⁻¹ (nd.j a)) := by
      have := (c.commutes_iff_root hβ'm (hRi (a - 2) (by omega)).1 hB hβ'img
        (hRi (a - 2) (by omega)).2.2.2.1).mpr (hrest (a - 2) (by omega) (by omega)).2.2
      have e : a - 2 + 2 = a := by omega
      rw [e] at this
      exact this
    have := (commutes_conjSub_iff g).mpr hc'
    rwa [conjSub_conjSub_inv] at this


structure IsMidPartnerE (c : ACtx p f 5 Ω K z) (nd : Nodes c) (β : Subgroup G) : Prop where
  mem : β ∈ Ω
  nK : ¬ Commutes K β
  pK : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β
  n2 : ¬ Commutes β (nd.j 2)
  p2 : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (nd.j 2)
  zero : Commutes β (nd.j 0)
  three : Commutes β (nd.j 3)
  four : Commutes β (nd.j 4)

theorem ACtx.exists_partnerMidE (c : ACtx p f 5 Ω K z) (nd : Nodes c)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) : ∃ β, IsMidPartnerE c nd β := by
  obtain ⟨β, hβ, -, hnK, hpK, hn2, hp2, h0, hrest⟩ := c.exists_partnerMid nd (by norm_num) hsingle
  exact ⟨β, ⟨hβ, hnK, hpK, hn2, hp2, h0, hrest 3 le_rfl (by norm_num),
    hrest 4 (by norm_num) (by norm_num)⟩⟩

end CFSG.ClassicalInvolution.RouteD
