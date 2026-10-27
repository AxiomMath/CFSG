module

public import CFSG.ClassicalInvolution.Q3.Q3WARoot
public import CFSG.ClassicalInvolution.RouteD.TypeAChain

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

section Nodes

variable {m : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

structure Nodes3 (c : ACtx3 m Ω K z) where
  j : ℕ → Subgroup G
  w : ℕ → G
  mem : ∀ a < m, j a ∈ centralizingMembers Ω {z}
  ne_K : ∀ a < m, j a ≠ K
  isCl : ∀ a < m, IsClassicalMember3 (j a) (w a)
  img : ∀ (a) (ha : a < m),
    locImg Ω z (j a) = (Lc (GaloisField 3 1) (nodePair m a ha)).map c.d.ψ
  inj : ∀ a < m, ∀ b < m, a ≠ b → j a ≠ j b
  wcomm : ∀ a < m, ∀ b < m, w a * w b = w b * w a
  wz : ∀ a < m, w a * z = z * w a
  commK : ∀ a < m, Commutes K (j a)
  far : ∀ a < m, ∀ b < m, a + 2 ≤ b → Commutes (j a) (j b)
  adj : ∀ a, a + 1 < m → ¬ Commutes (j a) (j (a + 1))
  pair : ∀ a, a + 1 < m →
    ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W (j a) (j (a + 1))

omit [Finite G] in
theorem mul_self_of_isClassicalMember3 {L : Subgroup G} {w : G} (h : IsClassicalMember3 L w) :
    w * w = 1 := by
  have := pow_orderOf_eq_one w
  rwa [h.orderOf_eq_two, pow_two] at this

theorem ACtx3.nonempty_nodes (c : ACtx3 m Ω K z) : Nonempty (Nodes3 c) := by
  have h2 := two_ne_zero_gf3
  have hroot : ∀ (a) (ha : a < m), IsLongRootSL2 c.hn (Lc (GaloisField 3 1) (nodePair m a ha))
      (zElt (GaloisField 3 1) (nodePair m a ha)) := fun a ha => isLongRootSL2_Lc h2 c.hn _
  have hex : ∀ a, ∃ L : Subgroup G, a < m →
      (L ∈ centralizingMembers Ω {z} ∧ L ≠ K ∧ ∀ ha : a < m,
        locImg Ω z L = (Lc (GaloisField 3 1) (nodePair m a ha)).map c.d.ψ) := by
    intro a
    by_cases ha : a < m
    · obtain ⟨L, hL, hLK, hLR⟩ := exists_member_of_root3 c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.hO3 c.d
        (R := Lc (GaloisField 3 1) (nodePair m a ha)) ⟨_, hroot a ha⟩
      exact ⟨L, fun _ => ⟨hL, hLK, fun _ => hLR⟩⟩
    · exact ⟨⊥, fun h => absurd h ha⟩
  choose j hj using hex
  have hexw : ∀ a, ∃ w : G, a < m → IsClassicalMember3 (j a) w := by
    intro a
    by_cases ha : a < m
    · obtain ⟨w, hw⟩ := c.hΩ.classical (j a) (hj a ha).1.1
      exact ⟨w, fun _ => hw⟩
    · exact ⟨1, fun h => absurd h ha⟩
  choose w hw using hexw
  have hmem : ∀ a < m, j a ∈ centralizingMembers Ω {z} := fun a ha => (hj a ha).1
  have himg : ∀ (a) (ha : a < m), locImg Ω z (j a) =
      (Lc (GaloisField 3 1) (nodePair m a ha)).map c.d.ψ := fun a ha => (hj a ha).2.2 ha
  have hinvimg : ∀ (a) (ha : a < m), c.d.ψ (zElt (GaloisField 3 1) (nodePair m a ha)) =
      locElt Ω z (w a) (le_centralizingLayer (hmem a ha) (hw a ha).mem) := fun a ha =>
    psi_root_inv c.hm odd_gf3 c.d (hroot a ha) (himg a ha) (le_centralizingLayer (hmem a ha))
      (hw a ha).mem (hw a ha).orderOf_eq_two
  have hcomm_iff : ∀ (a) (ha : a < m) (b) (hb : b < m), Commutes (j a) (j b) ↔
      Commutes (Lc (GaloisField 3 1) (nodePair m a ha)) (Lc (GaloisField 3 1) (nodePair m b hb)) :=
    fun a ha b hb => c.commutes_iff_root (hmem a ha) (hmem b hb) (hroot a ha) (himg a ha)
      (himg b hb)
  have hfar : ∀ a < m, ∀ b < m, a + 2 ≤ b → Commutes (j a) (j b) := fun a ha b hb hab =>
    (hcomm_iff a ha b hb).mpr (commutes_Lc_of_disjoint h2 (nodePair_disjoint ha hb hab))
  have hadj : ∀ a, a + 1 < m → ¬ Commutes (j a) (j (a + 1)) := by
    intro a ha hc
    exact not_commutes_Lc_overlap h2 c.hn3 (i := ⟨a, by omega⟩) (j := ⟨a + 1, by omega⟩)
      (k := ⟨a + 2, by omega⟩) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff]) ((hcomm_iff a (by omega) (a + 1) ha).mp hc)
  refine ⟨⟨j, w, hmem, fun a ha => (hj a ha).2.1, hw, himg, ?_, ?_, ?_, ?_, hfar, hadj, ?_⟩⟩
  · intro a ha b hb hab h
    have hi := c.rootInv_eq_of_locImg_eq (hroot a ha) (hroot b hb) (himg a ha) (himg b hb)
      (by rw [h])
    exact hab ((nodePair_eq_iff ha hb).mp (zElt_injective h2 hi))
  · intro a ha b hb
    have hy : ∀ a (ha : a < m), w a ∈ locLayer Ω z := fun a ha =>
      le_centralizingLayer (hmem a ha) (hw a ha).mem
    have hcom : Commute (locElt Ω z (w a) (hy a ha)) (locElt Ω z (w b) (hy b hb)) := by
      rw [← hinvimg a ha, ← hinvimg b hb]
      show c.d.ψ _ * c.d.ψ _ = c.d.ψ _ * c.d.ψ _
      rw [← map_mul, ← map_mul, signGroup_comm (zElt_mem_signGroup _) (zElt_mem_signGroup _)]
    have := commute_of_involutions_of_mk (Y := ↥(locLayer Ω z)) c.hP1
      (a := ⟨w a, hy a ha⟩) (b := ⟨w b, hy b hb⟩)
      (Subtype.ext (mul_self_of_isClassicalMember3 (hw a ha)))
      (Subtype.ext (mul_self_of_isClassicalMember3 (hw b hb))) hcom
    exact congrArg Subtype.val this
  · intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp ((hmem a ha).2 (hw a ha).mem)
  · intro a ha
    exact commutes_K_of_ne3 c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.hO3 c.d (hmem a ha) (hj a ha).2.1
  · intro a ha
    have hc : Commute (zElt (GaloisField 3 1) (nodePair m a (by omega)))
        (zElt (GaloisField 3 1) (nodePair m (a + 1) ha)) :=
      signGroup_comm (zElt_mem_signGroup _) (zElt_mem_signGroup _)
    have hne : zElt (GaloisField 3 1) (nodePair m a (by omega)) ≠
        zElt (GaloisField 3 1) (nodePair m (a + 1) ha) := by
      intro h
      have := (nodePair_eq_iff (by omega) ha).mp (zElt_injective h2 h)
      omega
    have hnc : ¬ Commutes (Lc (GaloisField 3 1) (nodePair m a (by omega)))
        (Lc (GaloisField 3 1) (nodePair m (a + 1) ha)) := fun hc' =>
      not_commutes_Lc_overlap h2 c.hn3 (i := ⟨a, by omega⟩) (j := ⟨a + 1, by omega⟩)
        (k := ⟨a + 2, by omega⟩) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
        (by simp [Fin.ext_iff]) hc'
    exact c.stdpair_of_root (hmem a (by omega)) (hmem (a + 1) ha) (hroot a (by omega))
      (hroot (a + 1) ha) (himg a (by omega)) (himg (a + 1) ha) hc hne hnc

end Nodes

section Transport

variable {m : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem ACtx3.exists_rootData_conj (c : ACtx3 m Ω K z) {g : G} {Z' : Subgroup G}
    (hZ : Z' = conjSub g K) {N : Subgroup G} (hN : N ∈ Ω) (hNZ : Commutes N Z') (hNne : N ≠ Z')
    {w : G} (hcl : IsClassicalMember3 N w) :
    conjSub g⁻¹ N ∈ centralizingMembers Ω {z} ∧ conjSub g⁻¹ N ≠ K ∧
      ∃ (R : Subgroup SL(m + 1, GaloisField 3 1)) (i : SL(m + 1, GaloisField 3 1)),
        IsLongRootSL2 c.hn R i ∧ locImg Ω z (conjSub g⁻¹ N) = R.map c.d.ψ ∧
        ∃ hy : g⁻¹ * w * g ∈ locLayer Ω z, c.d.ψ i = locElt Ω z (g⁻¹ * w * g) hy := by
  have hw : g * z * g⁻¹ ∈ Z' := hZ ▸ conj_mem_conjSub c.hz.mem
  have hL : conjSub g⁻¹ N ∈ centralizingMembers Ω {z} :=
    conjSub_inv_mem_centralizingMembers c.hΩ.conjInvariant hN hw hNZ
  have hne : conjSub g⁻¹ N ≠ K := by
    intro h
    apply hNne
    rw [← conjSub_conjSub_inv g N, h, hZ]
  have hcl' : IsClassicalMember3 (conjSub g⁻¹ N) (g⁻¹ * w * g) := by
    have := IsClassicalMember3.conj hcl g⁻¹
    rwa [inv_inv] at this
  obtain ⟨R, i, hRi, hLR, hi⟩ := c.exists_rootData hL hne hcl'
  exact ⟨hL, hne, R, i, hRi, hLR, le_centralizingLayer hL hcl'.mem, hi⟩

theorem ACtx3.commute_of_locElt (c : ACtx3 m Ω K z) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {z}) (hL' : L' ∈ centralizingMembers Ω {z}) (hne : L ≠ L')
    {R R' : Subgroup SL(m + 1, GaloisField 3 1)} {i i' : SL(m + 1, GaloisField 3 1)}
    (hRi : IsLongRootSL2 c.hn R i) (hRi' : IsLongRootSL2 c.hn R' i')
    (hLR : locImg Ω z L = R.map c.d.ψ) (hLR' : locImg Ω z L' = R'.map c.d.ψ) {y y' : G}
    (hy : y ∈ locLayer Ω z) (hy' : y' ∈ locLayer Ω z) (hi : c.d.ψ i = locElt Ω z y hy)
    (hi' : c.d.ψ i' = locElt Ω z y' hy') (hc : y * y' = y' * y) : Commute i i' ∧ i ≠ i' := by
  have hne' : c.d.ψ i ≠ c.d.ψ i' := by
    intro h
    have hii := Transfer.eq_of_map_eq_of_isLongRootSL2 two_ne_zero_gf3 hRi hRi' c.d.ker_le c.hlift h
    subst hii
    exact hne (c.eq_of_rootInv_eq hL hL' hRi hRi' hLR hLR')
  have hcomm : Commute (c.d.ψ i) (c.d.ψ i') := by
    show c.d.ψ i * c.d.ψ i' = c.d.ψ i' * c.d.ψ i
    rw [hi, hi']
    have : (⟨y, hy⟩ : ↥(locLayer Ω z)) * ⟨y', hy'⟩ = ⟨y', hy'⟩ * ⟨y, hy⟩ := Subtype.ext hc
    unfold locElt
    rw [← map_mul, ← map_mul, this]
  exact Transfer.commute_and_ne_of_map two_ne_zero_gf3 hRi' c.d.ker_le c.hlift hcomm hne'

theorem ACtx3.exists_partner (c : ACtx3 m Ω K z) (nd : Nodes3 c) (hm : 4 ≤ m)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) :
    ∃ β : Subgroup G, β ∈ Ω ∧ (∃ wβ : G, IsClassicalMember3 β wβ) ∧ ¬ Commutes K β ∧
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β) ∧
      ¬ Commutes β (nd.j 0) ∧
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W β (nd.j 0)) ∧
      Commutes β (nd.j (m - 1)) ∧ ∀ a, 1 ≤ a → a ≤ m - 3 → Commutes β (nd.j a) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hk : 2 ≤ k := by omega
  have h2 := two_ne_zero_gf3
  have hMΩ : nd.j (k + 1) ∈ Ω := (nd.mem (k + 1) (by omega)).1
  obtain ⟨g, hg⟩ := hsingle _ hMΩ
  obtain ⟨hK'm, hK'ne, R₀, i₀, hR₀, hKR₀, hy₀, hi₀⟩ := c.exists_rootData_conj hg c.hK
    (nd.commK (k + 1) (by omega)) (nd.ne_K (k + 1) (by omega)).symm c.hz
  have hnode : ∀ a, ∃ (R : Subgroup SL(k + 2 + 1, GaloisField 3 1))
      (i : SL(k + 2 + 1, GaloisField 3 1)), a < k →
      (conjSub g⁻¹ (nd.j a) ∈ centralizingMembers Ω {z} ∧ conjSub g⁻¹ (nd.j a) ≠ K ∧
        IsLongRootSL2 c.hn R i ∧ locImg Ω z (conjSub g⁻¹ (nd.j a)) = R.map c.d.ψ ∧
        ∃ hy : g⁻¹ * nd.w a * g ∈ locLayer Ω z, c.d.ψ i = locElt Ω z (g⁻¹ * nd.w a * g) hy) := by
    intro a
    by_cases ha : a < k
    · obtain ⟨h1, h2', R, i, h3, h4, h5⟩ := c.exists_rootData_conj hg (nd.mem a (by omega)).1
        (nd.far a (by omega) (k + 1) (by omega) (by omega))
        (nd.inj a (by omega) (k + 1) (by omega) (by omega)) (nd.isCl a (by omega))
      exact ⟨R, i, fun _ => ⟨h1, h2', h3, h4, h5⟩⟩
    · exact ⟨⊥, 1, fun h => absurd h ha⟩
  choose R i hRi using hnode
  have hconjne : ∀ a b, a < k → b < k → a ≠ b →
      conjSub g⁻¹ (nd.j a) ≠ conjSub g⁻¹ (nd.j b) := fun a b ha hb hab h =>
    nd.inj a (by omega) b (by omega) hab (conjSub_injective g⁻¹ h)
  have hKne : ∀ a, a < k → conjSub g⁻¹ K ≠ conjSub g⁻¹ (nd.j a) := fun a ha h =>
    nd.ne_K a (by omega) ((conjSub_injective g⁻¹ h).symm)
  have hR : ∀ a < k, IsLongRootSL2 c.hn (R a) (i a) := fun a ha => (hRi a ha).2.2.1
  have hcomm : ∀ a < k, Commute i₀ (i a) := by
    intro a ha
    obtain ⟨hya, hia⟩ := (hRi a ha).2.2.2.2
    refine (c.commute_of_locElt hK'm (hRi a ha).1 (hKne a ha) hR₀ (hR a ha) hKR₀
      (hRi a ha).2.2.2.1 hy₀ hya hi₀ hia ?_).1
    calc g⁻¹ * z * g * (g⁻¹ * nd.w a * g) = g⁻¹ * (z * nd.w a) * g := by group
      _ = g⁻¹ * (nd.w a * z) * g := by rw [(nd.wz a (by omega)).symm]
      _ = g⁻¹ * nd.w a * g * (g⁻¹ * z * g) := by group
  have hcomm' : ∀ a < k, ∀ b < k, Commute (i a) (i b) := by
    intro a ha b hb
    by_cases hab : a = b
    · subst hab; exact Commute.refl _
    · obtain ⟨hya, hia⟩ := (hRi a ha).2.2.2.2
      obtain ⟨hyb, hib⟩ := (hRi b hb).2.2.2.2
      refine (c.commute_of_locElt (hRi a ha).1 (hRi b hb).1 (hconjne a b ha hb hab) (hR a ha)
        (hR b hb) (hRi a ha).2.2.2.1 (hRi b hb).2.2.2.1 hya hyb hia hib ?_).1
      calc g⁻¹ * nd.w a * g * (g⁻¹ * nd.w b * g) = g⁻¹ * (nd.w a * nd.w b) * g := by group
        _ = g⁻¹ * (nd.w b * nd.w a) * g := by rw [nd.wcomm a (by omega) b (by omega)]
        _ = g⁻¹ * nd.w b * g * (g⁻¹ * nd.w a * g) := by group
  have hinj : ∀ a < k, ∀ b < k, a ≠ b → i a ≠ i b := fun a ha b hb hab =>
    c.ne_of_rootInv (hRi a ha).1 (hRi b hb).1 (hconjne a b ha hb hab) (hR a ha) (hR b hb)
      (hRi a ha).2.2.2.1 (hRi b hb).2.2.2.1
  have h0ne : ∀ a < k, i₀ ≠ i a := fun a ha =>
    c.ne_of_rootInv hK'm (hRi a ha).1 (hKne a ha) hR₀ (hR a ha) hKR₀ (hRi a ha).2.2.2.1
  have hR0 : ∀ a < k, Commutes R₀ (R a) := fun a ha =>
    (c.commutes_iff_root hK'm (hRi a ha).1 hR₀ hKR₀ (hRi a ha).2.2.2.1).mp
      ((commutes_conjSub_iff g⁻¹).mpr (nd.commK a (by omega)))
  have hfar : ∀ a < k, ∀ b < k, a + 2 ≤ b → Commutes (R a) (R b) := fun a ha b hb hab =>
    (c.commutes_iff_root (hRi a ha).1 (hRi b hb).1 (hR a ha) (hRi a ha).2.2.2.1
      (hRi b hb).2.2.2.1).mp ((commutes_conjSub_iff g⁻¹).mpr (nd.far a (by omega) b (by omega) hab))
  have hadj : ∀ a, a + 1 < k → ¬ Commutes (R a) (R (a + 1)) := fun a ha hc' =>
    nd.adj a (by omega) ((commutes_conjSub_iff g⁻¹).mp
      ((c.commutes_iff_root (hRi a (by omega)).1 (hRi (a + 1) ha).1 (hR a (by omega))
        (hRi a (by omega)).2.2.2.1 (hRi (a + 1) ha).2.2.2.1).mpr hc'))
  obtain ⟨B, iB, hB, hc0, hne0, hnc0, hc1, hne1, hnc1, hrest⟩ :=
    RouteD.exists_partner h2 hk hR₀ hR hcomm hcomm' hinj h0ne hR0 hfar hadj
  obtain ⟨β', hβ'm, hβ'K, hβ'img⟩ := exists_member_of_root3 c.hm c.hΩ c.hex c.hK c.hz c.hP1
    c.hO3 c.d
    (R := B) ⟨iB, hB⟩
  obtain ⟨wb, hwb⟩ := c.hΩ.classical β' hβ'm.1
  have hnK' : ¬ Commutes (conjSub g⁻¹ K) β' := fun h =>
    hnc0 ((c.commutes_iff_root hK'm hβ'm hR₀ hKR₀ hβ'img).mp h).symm
  have hn0' : ¬ Commutes β' (conjSub g⁻¹ (nd.j 0)) := fun h =>
    hnc1 ((c.commutes_iff_root hβ'm (hRi 0 (by omega)).1 hB hβ'img
      (hRi 0 (by omega)).2.2.2.1).mp h)
  obtain ⟨W1, hW1⟩ := c.stdpair_of_root hK'm hβ'm hR₀ hB hKR₀ hβ'img hc0.symm hne0.symm
    (fun h => hnc0 h.symm)
  obtain ⟨W2, hW2⟩ := c.stdpair_of_root hβ'm (hRi 0 (by omega)).1 hB (hR 0 (by omega)) hβ'img
    (hRi 0 (by omega)).2.2.2.1 hc1 hne1 hnc1
  have hKβ'M : Commutes K β' :=
    commutes_K_of_ne3 c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.hO3 c.d hβ'm hβ'K
  refine ⟨conjSub g β', c.hΩ.conjInvariant g β' hβ'm.1, ⟨_, IsClassicalMember3.conj hwb g⟩, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro h
    rw [← conjSub_conjSub_inv g K] at h
    exact hnK' ((commutes_conjSub_iff g).mp h)
  · refine ⟨conjSub g W1, ?_⟩
    have := linearBlockStandardPair_conjSub hW1 g
    rwa [conjSub_conjSub_inv] at this
  · intro h
    rw [← conjSub_conjSub_inv g (nd.j 0)] at h
    exact hn0' ((commutes_conjSub_iff g).mp h)
  · refine ⟨conjSub g W2, ?_⟩
    have := linearBlockStandardPair_conjSub hW2 g
    rwa [conjSub_conjSub_inv] at this
  · have e : k + 2 - 1 = k + 1 := by omega
    rw [e, hg]
    exact (commutes_conjSub_iff g).mpr hKβ'M.symm
  · intro a ha1 ha
    have hc' : Commutes β' (conjSub g⁻¹ (nd.j a)) :=
      (c.commutes_iff_root hβ'm (hRi a (by omega)).1 hB hβ'img (hRi a (by omega)).2.2.2.1).mpr
        (hrest a ha1 (by omega)).2.2
    have := (commutes_conjSub_iff g).mpr hc'
    rwa [conjSub_conjSub_inv] at this

theorem ACtx3.commutes_beta_second_last (c : ACtx3 m Ω K z) (nd : Nodes3 c) (hm : 6 ≤ m)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {β : Subgroup G} (hβ : β ∈ Ω)
    (hβcl : ∃ wβ : G, IsClassicalMember3 β wβ) (hnK : ¬ Commutes K β)
    (hmid : ∀ a, 1 ≤ a → a ≤ m - 3 → Commutes β (nd.j a)) (hlast : Commutes β (nd.j (m - 1))) :
    Commutes β (nd.j (m - 2)) := by
  obtain ⟨wβ, hwβ⟩ := hβcl
  have hZΩ : nd.j 1 ∈ Ω := (nd.mem 1 (by omega)).1
  obtain ⟨g, hg⟩ := hsingle _ hZΩ
  have hβZ : Commutes β (nd.j 1) := hmid 1 le_rfl (by omega)
  have hβne : β ≠ nd.j 1 := by
    intro h
    exact hnK (h ▸ nd.commK 1 (by omega))
  obtain ⟨hβm, hβne', Rb, ib, hRb, hβR, -⟩ := c.exists_rootData_conj hg hβ hβZ hβne hwβ
  have hnode : ∀ a, a + 3 = m ∨ a + 2 = m ∨ a + 1 = m → ∃ (R : Subgroup SL(m + 1, GaloisField 3 1))
      (i : SL(m + 1, GaloisField 3 1)), conjSub g⁻¹ (nd.j a) ∈ centralizingMembers Ω {z} ∧
        IsLongRootSL2 c.hn R i ∧ locImg Ω z (conjSub g⁻¹ (nd.j a)) = R.map c.d.ψ ∧
        ∃ hy : g⁻¹ * nd.w a * g ∈ locLayer Ω z, c.d.ψ i = locElt Ω z (g⁻¹ * nd.w a * g) hy := by
    intro a ha
    obtain ⟨h1, -, R, i, h3, h4, h5⟩ := c.exists_rootData_conj hg (nd.mem a (by omega)).1
      (nd.far 1 (by omega) a (by omega) (by omega)).symm
      (nd.inj a (by omega) 1 (by omega) (by omega)) (nd.isCl a (by omega))
    exact ⟨R, i, h1, h3, h4, h5⟩
  obtain ⟨R₁, i₁, hm₁, hR₁, hR₁img, hy₁, hi₁⟩ := hnode (m - 3) (by omega)
  obtain ⟨R₂, i₂, hm₂, hR₂, hR₂img, hy₂, hi₂⟩ := hnode (m - 2) (by omega)
  obtain ⟨R₃, i₃, hm₃, hR₃, hR₃img, hy₃, hi₃⟩ := hnode (m - 1) (by omega)
  have hc : ∀ a b : ℕ, a < m → b < m → g⁻¹ * nd.w a * g * (g⁻¹ * nd.w b * g) =
      g⁻¹ * nd.w b * g * (g⁻¹ * nd.w a * g) := by
    intro a b ha hb
    calc g⁻¹ * nd.w a * g * (g⁻¹ * nd.w b * g) = g⁻¹ * (nd.w a * nd.w b) * g := by group
      _ = g⁻¹ * (nd.w b * nd.w a) * g := by rw [nd.wcomm a ha b hb]
      _ = g⁻¹ * nd.w b * g * (g⁻¹ * nd.w a * g) := by group
  have hne : ∀ a b, a < m → b < m → a ≠ b →
      conjSub g⁻¹ (nd.j a) ≠ conjSub g⁻¹ (nd.j b) := fun a b ha hb hab h =>
    nd.inj a ha b hb hab (conjSub_injective g⁻¹ h)
  have hβne2 : ∀ a, a < m → Commutes β (nd.j a) → conjSub g⁻¹ β ≠ conjSub g⁻¹ (nd.j a) := by
    intro a ha hcm h
    have := conjSub_injective g⁻¹ h
    rw [this] at hcm
    exact not_commutes_self3 (nd.isCl a ha) hcm
  have h12 := (c.commute_of_locElt hm₁ hm₂ (hne _ _ (by omega) (by omega) (by omega)) hR₁ hR₂
    hR₁img hR₂img hy₁ hy₂ hi₁ hi₂ (hc _ _ (by omega) (by omega)))
  have h23 := (c.commute_of_locElt hm₂ hm₃ (hne _ _ (by omega) (by omega) (by omega)) hR₂ hR₃
    hR₂img hR₃img hy₂ hy₃ hi₂ hi₃ (hc _ _ (by omega) (by omega)))
  have h13 := (c.commute_of_locElt hm₁ hm₃ (hne _ _ (by omega) (by omega) (by omega)) hR₁ hR₃
    hR₁img hR₃img hy₁ hy₃ hi₁ hi₃ (hc _ _ (by omega) (by omega)))
  have hcomm_root : ∀ {L L' : Subgroup G} {R R' : Subgroup SL(m + 1, GaloisField 3 1)}
      {i : SL(m + 1, GaloisField 3 1)}, L ∈ centralizingMembers Ω {z} →
      L' ∈ centralizingMembers Ω {z} → IsLongRootSL2 c.hn R i → locImg Ω z L = R.map c.d.ψ →
      locImg Ω z L' = R'.map c.d.ψ → (Commutes L L' ↔ Commutes R R') :=
    fun hL hL' hR hLR hLR' => c.commutes_iff_root hL hL' hR hLR hLR'
  have hR13 : Commutes R₁ R₃ := (hcomm_root hm₁ hm₃ hR₁ hR₁img hR₃img).mp
    ((commutes_conjSub_iff g⁻¹).mpr (nd.far (m - 3) (by omega) (m - 1) (by omega) (by omega)))
  have hn12 : ¬ Commutes R₁ R₂ := fun h => nd.adj (m - 3) (by omega)
    (by
      have := (commutes_conjSub_iff g⁻¹).mp ((hcomm_root hm₁ hm₂ hR₁ hR₁img hR₂img).mpr h)
      have e : m - 3 + 1 = m - 2 := by omega
      rw [e]
      exact this)
  have hn23 : ¬ Commutes R₂ R₃ := fun h => nd.adj (m - 2) (by omega)
    (by
      have := (commutes_conjSub_iff g⁻¹).mp ((hcomm_root hm₂ hm₃ hR₂ hR₂img hR₃img).mpr h)
      have e : m - 2 + 1 = m - 1 := by omega
      rw [e]
      exact this)
  have hRb1 : Commutes Rb R₁ := (hcomm_root hβm hm₁ hRb hβR hR₁img).mp
    ((commutes_conjSub_iff g⁻¹).mpr (hmid (m - 3) (by omega) le_rfl))
  have hRb3 : Commutes Rb R₃ := (hcomm_root hβm hm₃ hRb hβR hR₃img).mp
    ((commutes_conjSub_iff g⁻¹).mpr hlast)
  have hRb2 := commutes_middle two_ne_zero_gf3 c.hn3 hR₁ hR₂ hR₃ hRb h12.1 h23.1 h13.1 h13.2
    (c.ne_of_rootInv hβm hm₁ (hβne2 _ (by omega) (hmid _ (by omega) le_rfl)) hRb hR₁ hβR hR₁img)
    (c.ne_of_rootInv hβm hm₃ (hβne2 _ (by omega) hlast) hRb hR₃ hβR hR₃img) hR13 hn12 hn23 hRb1
    hRb3
  have := (commutes_conjSub_iff g⁻¹).mp ((hcomm_root hβm hm₂ hRb hβR hR₂img).mpr hRb2)
  exact this

end Transport

end CFSG.ClassicalInvolution.Q3.Q3W
