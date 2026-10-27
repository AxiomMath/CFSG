module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Core
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Uniform

section Odd

variable {H : Type} [Group H] [Finite H] {N : Subgroup H} [N.Normal]

theorem isSylow2In_sup_of_odd (hN : Odd (Nat.card N)) {P : Subgroup H} (hP : IsPGroup 2 P) :
    IsSylow2In P (P ⊔ N) := by
  set T := P ⊔ N with hT
  obtain ⟨V₀, hV₀, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := T) IsPGroup.of_bot bot_le
  have hTmap : T.map (QuotientGroup.mk' N) = P.map (QuotientGroup.mk' N) := by
    have hNmap : N.map (QuotientGroup.mk' N) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      simpa using hx
    rw [hT, Subgroup.map_sup, hNmap, sup_bot_eq]
  have hV₀N : V₀ ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hV₀.2.1 hV₀.1 (odd_natCard_inf hN T)
  have hPN : P ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hP le_sup_left (odd_natCard_inf hN T)
  have hs := isSylow2In_map_mk hN hV₀
  rw [hTmap] at hs
  have hVeq : V₀.map (QuotientGroup.mk' N) = P.map (QuotientGroup.mk' N) :=
    hs.2.2 _ le_rfl (hP.map _) hs.1 |>.symm
  have hc : Nat.card V₀ = Nat.card P := by
    have e1 : Nat.card V₀ = Nat.card ↥(V₀.map (QuotientGroup.mk' N)) :=
      Nat.card_congr (AscQuot.quotRestrictEquiv hV₀N).toEquiv
    have e2 : Nat.card P = Nat.card ↥(P.map (QuotientGroup.mk' N)) :=
      Nat.card_congr (AscQuot.quotRestrictEquiv hPN).toEquiv
    rw [e1, e2, hVeq]
  exact hV₀.of_natCard_le hP le_sup_left (by rw [hc])

theorem exists_conj_of_isPGroup_map_eq (hN : Odd (Nat.card N)) {P Q : Subgroup H}
    (hP : IsPGroup 2 P) (hQ : IsPGroup 2 Q)
    (h : P.map (QuotientGroup.mk' N) = Q.map (QuotientGroup.mk' N)) :
    ∃ n ∈ P ⊔ N, conjSub n P = Q := by
  have hPQ : P ≤ Q ⊔ N := by
    intro x hx
    have : QuotientGroup.mk' N x ∈ Q.map (QuotientGroup.mk' N) := h ▸ Subgroup.mem_map_of_mem _ hx
    have h2 := (Subgroup.mem_comap).mpr this
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
  have hQP : Q ≤ P ⊔ N := by
    intro x hx
    have : QuotientGroup.mk' N x ∈ P.map (QuotientGroup.mk' N) := h ▸ Subgroup.mem_map_of_mem _ hx
    have h2 := (Subgroup.mem_comap).mpr this
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
  have hT : Q ⊔ N = P ⊔ N :=
    le_antisymm (sup_le hQP le_sup_right) (sup_le hPQ le_sup_right)
  have h1 := isSylow2In_sup_of_odd hN hP
  have h2 := isSylow2In_sup_of_odd hN hQ
  rw [hT] at h2
  obtain ⟨x, hx, hxe⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In h1 h2
  exact ⟨x, hx, hxe⟩

end Odd

section Layer





variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem exists_conj_sylow_of_secImg_conj (hΩ : HypOmegaGen Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {J M : Subgroup G} (hJ : J ∈ tqMembers3 Ω c)
    (hM : M ∈ tqMembers3 Ω c) {P Q : Subgroup G} (hP : IsSylow2In P J) (hQ : IsSylow2In Q M)
    (hPc : P ≤ Subgroup.centralizer ({c} : Set G)) (hQc : Q ≤ Subgroup.centralizer ({c} : Set G))
    :
    ∀ x : ↥(coreHull Ω c), conjSub (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)) x)
      (secImg Ω c J) = secImg Ω c M →
    ∃ g : ↥(coreHull Ω c), conjSub (((g : ↥(Subgroup.centralizer ({c} : Set G))) : G)) P = Q := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set H := coreHull Ω c with hH
  set N := classicalInvolutionOddCore ↥H with hNdef
  have hN : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥H
  intro x hx
  have hPs : IsSylow2In P (TwinADescent.coreAt c J) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hJ.2).mpr ⟨hP, hPc⟩
  have hQs : IsSylow2In Q (TwinADescent.coreAt c M) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hM.2).mpr ⟨hQ, hQc⟩
  set Cj : Subgroup ↥H := ((TwinADescent.coreAt c J).subgroupOf C).subgroupOf H with hCj
  set Cm : Subgroup ↥H := ((TwinADescent.coreAt c M).subgroupOf C).subgroupOf H with hCm
  set P'' : Subgroup ↥H := (P.subgroupOf C).subgroupOf H with hP''
  set Q'' : Subgroup ↥H := (Q.subgroupOf C).subgroupOf H with hQ''
  have hsP : IsSylow2In P'' Cj :=
    (hPs.subgroupOf (TwinADescent.coreAt_le_centralizer c J)).subgroupOf (le_coreHull hJ)
  have hsQ : IsSylow2In Q'' Cm :=
    (hQs.subgroupOf (TwinADescent.coreAt_le_centralizer c M)).subgroupOf (le_coreHull hM)
  have hCjmap : Cj.map (QuotientGroup.mk' N) = secImg Ω c J := rfl
  have hCmmap : Cm.map (QuotientGroup.mk' N) = secImg Ω c M := rfl
  have hxm : (conjSub x Cj).map (QuotientGroup.mk' N) = Cm.map (QuotientGroup.mk' N) := by
    rw [AscQuot.map_conjSub, hCjmap, hCmmap]
    exact hx
  have hs1 : IsSylow2In (conjSub x P'') (conjSub x Cj) := hsP.conj x
  have hs2 := isSylow2In_map_mk hN hs1
  rw [hxm] at hs2
  have hs3 := isSylow2In_map_mk hN hsQ
  obtain ⟨yb, hyb, hybe⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hs2 hs3
  obtain ⟨y, hyCm, rfl⟩ := Subgroup.mem_map.mp hyb
  have hP2 : conjSub (y * x) P'' = conjSub y (conjSub x P'') := by rw [conjSub_mul]
  have hmapeq : (conjSub (y * x) P'').map (QuotientGroup.mk' N) = Q''.map (QuotientGroup.mk' N) := by
    rw [hP2, AscQuot.map_conjSub]
    exact hybe
  have hpg : IsPGroup 2 ↥(conjSub (y * x) P'') := isPGroup_conjSub _ hsP.2.1
  obtain ⟨n, hn, hne⟩ := exists_conj_of_isPGroup_map_eq hN hpg hsQ.2.1 hmapeq
  have hnH : n ∈ N ⊔ conjSub (y * x) P'' := by rwa [sup_comm] at hn
  refine ⟨n * (y * x), ?_⟩
  have hfin : conjSub (n * (y * x)) P'' = Q'' := by rw [conjSub_mul, hne]
  have hPCH : P.subgroupOf C ≤ H := fun a ha =>
    le_coreHull hJ (Subgroup.mem_subgroupOf.mpr (hPs.1 (Subgroup.mem_subgroupOf.mp ha)))
  have hQCH : Q.subgroupOf C ≤ H := fun a ha =>
    le_coreHull hM (Subgroup.mem_subgroupOf.mpr (hQs.1 (Subgroup.mem_subgroupOf.mp ha)))
  have hcg : conjSub ((n * (y * x) : ↥H) : ↥C) (P.subgroupOf C) ≤ H := by
    have := conjSub_mono (n := ((n * (y * x) : ↥H) : ↥C)) hPCH
    rwa [conjSub_eq_self_of_mem (n * (y * x) : ↥H).2] at this
  have e1 : (conjSub (n * (y * x)) P'').map H.subtype =
      conjSub ((n * (y * x) : ↥H) : ↥C) (P.subgroupOf C) := by
    rw [hP'', conjSub_subgroupOf]
    exact Subgroup.map_subgroupOf_eq_of_le hcg
  have e2 : Q''.map H.subtype = Q.subgroupOf C := Subgroup.map_subgroupOf_eq_of_le hQCH
  rw [hfin, e2] at e1
  rw [conjSub_subgroupOf C _ P] at e1
  have hle : conjSub (((n * (y * x) : ↥H) : ↥C) : G) P ≤ C := by
    have := conjSub_mono (n := (((n * (y * x) : ↥H) : ↥C) : G)) hPc
    rwa [conjSub_eq_self_of_mem ((n * (y * x) : ↥H) : ↥C).2] at this
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hQc, inf_eq_left.mpr hle] at e1
  exact e1.symm

end Layer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
