module

public import CFSG.ClassicalInvolution.Q3.Q3EPCtx

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false


section Members

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {tY : StatedLieTag} {nY : ℕ}
  {N : Subgroup G} {x : G}

@[expose] def ETCtx3.IsLayerMember (_ : ETCtx3 tY nY Ω N x) (L : Subgroup G) : Prop :=
  L ∈ centralizingMembers Ω {x} ∧ L ≠ N

theorem ETCtx3.IsLayerMember.of_not_commutes (cx : ETCtx3 tY nY Ω N x) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x}) (hne : L ≠ L')
    (hc : ¬ Commutes L L') : cx.IsLayerMember L := by
  refine ⟨hL, ?_⟩
  rintro rfl
  exact hc (cx.commutes_K_of_ne hL' (fun h => hne h.symm))

theorem ETCtx3.IsLayerMember.exists_fund {cx : ETCtx3 tY nY Ω N x} {L : Subgroup G}
    (hL : cx.IsLayerMember L) :
    ∃ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      locImg Ω x L = R.map cx.d.ψ :=
  cx.exists_fund_of_ne hL.1 hL.2

theorem ETCtx3.exists_involution_of_fund (cx : ETCtx3 tY nY Ω N x) {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x})
    {R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) {w : G} (hw : IsClassicalMember3 L w) :
    ∃ r, Gaps.InvOf R r ∧ cx.d.ψ r = locElt Ω x w (le_centralizingLayer hL hw.mem) := by
  have hwx : w ∈ locLayer Ω x := le_centralizingLayer hL hw.mem
  have hmem : locElt Ω x w hwx ∈ R.map cx.d.ψ :=
    hLR ▸ locElt_mem_locImg (le_centralizingLayer hL) hw.mem
  obtain ⟨r, hrR, hr⟩ := hmem
  have h2 : orderOf (cx.d.ψ r) = 2 := by
    rw [hr]
    exact orderOf_locElt hwx hw.orderOf_eq_two
  have hsq : r * r = 1 := by
    have h1 : cx.d.ψ (r * r) = 1 := by
      rw [map_mul]
      have := pow_orderOf_eq_one (cx.d.ψ r)
      rwa [h2, pow_two] at this
    exact cx.hY.central R hR (r * r) (R.mul_mem hrR hrR) (cx.d.ker_le h1)
  have hr1 : r ≠ 1 := by
    intro h
    rw [h, map_one] at h2
    simp at h2
  exact ⟨r, ⟨hrR, orderOf_eq_prime (by rw [pow_two]; exact hsq) hr1⟩, hr⟩

theorem ETCtx3.modelInvComm_of_commute (cx : ETCtx3 tY nY Ω N x) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hR' : R' ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) (hLR' : locImg Ω x L' = R'.map cx.d.ψ) {w w' : G}
    (hw : IsClassicalMember3 L w) (hw' : IsClassicalMember3 L' w') (hc : Commute w w') :
    ∃ r r', Gaps.InvOf R r ∧ Gaps.InvOf R' r' ∧
      ⁅r, r'⁆ ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K ∧
      cx.d.ψ r = locElt Ω x w (le_centralizingLayer hL hw.mem) ∧
      cx.d.ψ r' = locElt Ω x w' (le_centralizingLayer hL' hw'.mem) := by
  obtain ⟨r, hr, hψr⟩ := cx.exists_involution_of_fund hL hR hLR hw
  obtain ⟨r', hr', hψr'⟩ := cx.exists_involution_of_fund hL' hR' hLR' hw'
  refine ⟨r, r', hr, hr', cx.d.ker_le ?_, hψr, hψr'⟩
  have hcomm : cx.d.ψ r * cx.d.ψ r' = cx.d.ψ r' * cx.d.ψ r := by
    rw [hψr, hψr', locElt_mul, locElt_mul]
    congr 1
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm

omit [Finite G] in
theorem ETCtx3.normalizes_of_conjSub (cx : ETCtx3 tY nY Ω N x) {L : Subgroup G}
    {R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) {w : G} (hwx : w ∈ locLayer Ω x)
    {r : (modelUniv tY nY 3 1 Nat.prime_three).K} (hr : cx.d.ψ r = locElt Ω x w hwx)
    (hN : conjSub w L = L) : ∀ y ∈ R, r * y * r⁻¹ ∈ R := by
  have hle : (conjSub r R).map cx.d.ψ ≤ R.map cx.d.ψ := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have h1 : cx.d.ψ y ∈ locImg Ω x L := by
      rw [hLR]
      exact ⟨y, hy, rfl⟩
    have h2 : cx.d.ψ (r * y * r⁻¹) ∈ locImg Ω x (conjSub w L) := by
      have := Gaps.locImg_conjSub_layer (Ω := Ω) (x := x) L ⟨w, hwx⟩
      rw [this]
      refine ⟨cx.d.ψ y, h1, ?_⟩
      simp only [map_mul, map_inv, hr]
      rfl
    rwa [hN, hLR] at h2
  have hsub := le_of_map_le_of_pow3 cx.d.ψ cx.d.ker_le cx.ker_cop
    (cx.hY.pow3 R hR |>.conjSub r) hle
  exact fun y hy => hsub (conj_mem_conjSub hy)

theorem ETCtx3.modelAdj_of_adj (cx : ETCtx3 tY nY Ω N x) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hR' : R' ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) (hLR' : locImg Ω x L' = R'.map cx.d.ψ) {w w' : G}
    (hw : IsClassicalMember3 L w) (hw' : IsClassicalMember3 L' w') (hne : L ≠ L')
    (hnc : ¬ Commutes L L') (hc : Commute w w') (hN : conjSub w' L = L) :
    Gaps.ModelAdj (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K) R R' := by
  obtain ⟨r, r', hr, hr', hcen, hψr, hψr'⟩ :=
    cx.modelInvComm_of_commute hL hL' hR hR' hLR hLR' hw hw' hc
  refine ⟨fun h => hne (cx.eq_of_locImg_eq hL hL' (by rw [hLR, hLR', h])), ?_, r, r', hr, hr',
    hcen, ?_⟩
  · intro h
    exact hnc ((cx.commutes_iff_fund hL hL' hR hLR hLR').mpr h)
  · exact cx.normalizes_of_conjSub hR hLR (le_centralizingLayer hL' hw'.mem) hψr' hN

end Members

section Witness

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {tY : StatedLieTag} {nY : ℕ}

theorem ETCtx3.sign_config {N : Subgroup G} {x : G} (cx : ETCtx3 tY nY Ω N x)
    (hF : LayerGeom (fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
      (GaloisField 3 1))
    {a b d : Subgroup G} {wa wb wd : G} (ha : a ∈ centralizingMembers Ω {x})
    (hb : b ∈ centralizingMembers Ω {x}) (hd : d ∈ centralizingMembers Ω {x})
    (hwa : IsClassicalMember3 a wa) (hwb : IsClassicalMember3 b wb)
    (hwd : IsClassicalMember3 d wd) (hab : a ≠ b) (hbd : b ≠ d)
    (hpair : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W a b) (hnbd : ¬ Commutes b d)
    (had : Commutes a d) (hcab : Commute wa wb) (hcdb : Commute wd wb)
    (hna : conjSub wb a = a) (hnd : conjSub wb d = d) :
    ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W b d := by
  obtain ⟨W, hW⟩ := hpair
  have hnab : ¬ Commutes a b := not_commutes_of_linearBlockStandardPair hW
  have haL : cx.IsLayerMember a := ETCtx3.IsLayerMember.of_not_commutes cx ha hb hab hnab
  have hbL : cx.IsLayerMember b := ETCtx3.IsLayerMember.of_not_commutes cx hb hd hbd hnbd
  have hdL : cx.IsLayerMember d := ETCtx3.IsLayerMember.of_not_commutes cx hd hb hbd.symm
    (fun h => hnbd (Gaps.commutes_symm h))
  obtain ⟨Ra, hRa, haR⟩ := haL.exists_fund
  obtain ⟨Rb, hRb, hbR⟩ := hbL.exists_fund
  obtain ⟨Rd, hRd, hdR⟩ := hdL.exists_fund
  have hadjab : Gaps.ModelAdj (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K) Ra Rb :=
    cx.modelAdj_of_adj ha hb hRa hRb haR hbR hwa hwb hab hnab hcab hna
  have hadjdb : Gaps.ModelAdj (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K) Rd Rb :=
    cx.modelAdj_of_adj hd hb hRd hRb hdR hbR hwd hwb hbd.symm
      (fun h => hnbd (Gaps.commutes_symm h)) hcdb hnd
  have hcom : Commutes Ra Rd := (cx.commutes_iff_fund ha hd hRa haR hdR).mp had
  obtain ⟨W', hW'⟩ := Gaps.linearBlockStandardPair_locImg_of_members cx.hP1 ha hb hW
  rw [haR, hbR] at hW'
  have hlift := hF.lift cx.d.ψ cx.d.ker_le Ra hRa Rb hRb ⟨W', hW'⟩
  obtain ⟨W₂, hW₂⟩ := hF.sign Ra hRa Rb hRb Rd hRd hadjab hadjdb hcom hlift
  exact cx.stdPair_of_fund hb hd hW₂ hbR hdR

variable {z : G} {K : Subgroup G}

theorem ETCtx3.scenarioC (c : ETCtx3 tY nY Ω K z)
    (hF : LayerGeom (fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
      (GaloisField 3 1))
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    {J M : Subgroup G} (hJ : J ∈ Ω) (hM : M ∈ Ω) {wJ x : G} (hwJ : IsClassicalMember3 J wJ)
    (hwM : IsClassicalMember3 M x) (hKJ : Commutes K J) (hKM : Commutes K M)
    (hβM : Commutes β M) (hJM : Commutes J M) (hβJ : ¬ Commutes β J)
    (hnorm : conjSub t J = J) :
    ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W β J := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle hM hwM
  obtain ⟨W, hW⟩ := hKβ
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    Gaps.standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two
      ht.orderOf_eq_two
  have hβJne : β ≠ J := fun h => hnKβ (h ▸ hKJ)
  have hnormK : conjSub t K = K :=
    Gaps.conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  exact cx.sign_config hF (a := K) (b := β) (d := J) (wa := z) (wb := t) (wd := wJ)
    (mem_centralizingMembers_of_commutes c.hK hwM.mem hKM)
    (mem_centralizingMembers_of_commutes hβ hwM.mem hβM)
    (mem_centralizingMembers_of_commutes hJ hwM.mem hJM)
    c.hz ht hwJ hKne hβJne ⟨W, hW⟩ hβJ hKJ hzt
    (commute_of_conjSub_eq3 hwJ hnorm).symm hnormK hnorm

theorem ETCtx3.exists_moved_layer_member (c : ETCtx3 tY nY Ω K z)
    (hF : LayerGeom (fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
      (GaloisField 3 1))
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) {M : Subgroup G} (hM : M ∈ Ω)
    (hKM : Commutes K M) (hβM : Commutes β M) :
    ∃ N ∈ centralizingMembers Ω {z}, N ≠ K ∧ Commutes K N ∧ ¬ Commutes β N := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  obtain ⟨xM, hxM⟩ := c.hΩ.classical M hM
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle hM hxM
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hKx : K ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes c.hK hxM.mem hKM
  have hβx : β ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes hβ hxM.mem hβM
  have hKL := ETCtx3.IsLayerMember.of_not_commutes cx hKx hβx hKne hnKβ
  have hβL := ETCtx3.IsLayerMember.of_not_commutes cx hβx hKx hKne.symm
    (fun h => hnKβ (Gaps.commutes_symm h))
  obtain ⟨RK, hRK, hKR⟩ := hKL.exists_fund
  obtain ⟨Rβ, hRβ, hβR⟩ := hβL.exists_fund
  have hzt : Commute z t :=
    Gaps.standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two
      ht.orderOf_eq_two
  have hnormK : conjSub t K = K :=
    Gaps.conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hadj : Gaps.ModelAdj (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K) RK Rβ :=
    cx.modelAdj_of_adj hKx hβx hRK hRβ hKR hβR c.hz ht hKne hnKβ hzt hnormK
  obtain ⟨W', hW'⟩ := Gaps.linearBlockStandardPair_locImg_of_members cx.hP1 hKx hβx hW
  rw [hKR, hβR] at hW'
  have hlinR := hF.lift cx.d.ψ cx.d.ker_le RK hRK Rβ hRβ ⟨W', hW'⟩
  obtain ⟨S₁, hS₁, -, -, -, hc₁, -, hn₁, -⟩ := hF.perp2 RK hRK Rβ hRβ hadj hlinR
  obtain ⟨N₁, hN₁, -, hN₁R⟩ := cx.exists_member_of_fund hS₁
  have hKN₁ : Commutes K N₁ := (cx.commutes_iff_fund hKx hN₁ hRK hKR hN₁R).mpr hc₁
  have hβN₁ : ¬ Commutes β N₁ := fun h =>
    hn₁ ((cx.commutes_iff_fund hβx hN₁ hRβ hβR hN₁R).mp h)
  refine ⟨N₁, mem_centralizingMembers_of_commutes hN₁.1 c.hz.mem (Gaps.commutes_symm hKN₁),
    fun h => ?_, hKN₁, hβN₁⟩
  rw [h] at hKN₁
  exact not_commutes_self3 c.hz hKN₁

end Witness

end CFSG.ClassicalInvolution.Q3.Q3W
