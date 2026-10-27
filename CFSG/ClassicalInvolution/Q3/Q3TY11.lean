module

public import CFSG.ClassicalInvolution.RouteD.TWDInv
public import CFSG.ClassicalInvolution.Q3.Q3WASTImg
public import CFSG.ClassicalInvolution.Q3.Q3WASNorm
public import CFSG.ClassicalInvolution.Q3.Q3TCCtx
public import CFSG.ClassicalInvolution.RouteD.TwinYStatements

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.RouteD.TWD
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

section Element

variable {G : Type} [Group G] {K T : Subgroup G} {z : G}

theorem exists_mul_self_eq3 (hz : IsClassicalMember3 K z) (hex : classicalInvolutionOddCore K = ⊥) :
    ∃ a ∈ K, a * a = z := by
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2 hex
  have hodd : Odd (Nat.card (ZMod 3)) := by
    rw [Nat.card_zmod]
    decide
  have hzK : (⟨z, hz.mem⟩ : K) = e.symm (-1) :=
    (orderOf_eq_two_iff_of_equiv_sl2 hodd e ⟨z, hz.mem⟩).mp
      (by rw [Subgroup.orderOf_mk]; exact hz.orderOf_eq_two)
  refine ⟨((e.symm (slW (ZMod 3)) : K) : G), (e.symm (slW (ZMod 3))).2, ?_⟩
  have h : e.symm (slW (ZMod 3)) * e.symm (slW (ZMod 3)) = ⟨z, hz.mem⟩ := by
    rw [hzK, ← map_mul, sl2_w_mul_self]
  exact congrArg Subtype.val h

theorem eq_one_or_eq_of_central3 (hz : IsClassicalMember3 K z)
    (hex : classicalInvolutionOddCore K = ⊥) {x : G} (hx : x ∈ K) (hc : ∀ k ∈ K, k * x = x * k) :
    x = 1 ∨ x = z := by
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2 hex
  have hodd : Odd (Nat.card (ZMod 3)) := by
    rw [Nat.card_zmod]
    decide
  have hzK : (⟨z, hz.mem⟩ : K) = e.symm (-1) :=
    (orderOf_eq_two_iff_of_equiv_sl2 hodd e ⟨z, hz.mem⟩).mp
      (by rw [Subgroup.orderOf_mk]; exact hz.orderOf_eq_two)
  have hcenter : (⟨x, hx⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hc k k.2)
  rcases (mem_center_sl2_iff _).mp ((mem_center_iff_of_equiv_sl2 e _).mp hcenter) with h | h
  · left
    have : (⟨x, hx⟩ : K) = 1 := e.injective (by rw [h, map_one])
    exact congrArg Subtype.val this
  · right
    have : (⟨x, hx⟩ : K) = ⟨z, hz.mem⟩ := by rw [hzK]; exact e.injective (by rw [h]; simp)
    exact congrArg Subtype.val this

theorem exists_twinElt3 (hz : IsClassicalMember3 K z) (hzT : IsClassicalMember3 T z)
    (hexK : classicalInvolutionOddCore K = ⊥) (hexT : classicalInvolutionOddCore T = ⊥) :
    Nonempty (TwinElt K T z) := by
  obtain ⟨a, ha, haa⟩ := exists_mul_self_eq3 hz hexK
  obtain ⟨a', ha', ha'a'⟩ := exists_mul_self_eq3 hzT hexT
  exact ⟨⟨a, a', ha, ha', haa, ha'a'⟩⟩

theorem twinElt_u_not_mem_left3 (e : TwinElt K T z) (hz : IsClassicalMember3 K z)
    (hexK : classicalInvolutionOddCore K = ⊥) (hKT : Commutes K T) : e.u ∉ K := by
  intro h
  have hmem : e.a' ∈ K := by
    have := K.mul_mem (K.inv_mem e.mem_a) h
    simpa [TwinElt.u] using this
  have hc : ∀ k ∈ K, k * e.a' = e.a' * k := fun k hk => hKT k hk _ e.mem_a'
  have hz2 : z * z = 1 := hz.isCentralInvolution.sq
  have hz1 : z ≠ 1 := hz.ne_one
  have hsq := e.mul_self_a'
  rcases eq_one_or_eq_of_central3 hz hexK hmem hc with h1 | h1
  · rw [h1, one_mul] at hsq
    exact hz1 hsq.symm
  · rw [h1, hz2] at hsq
    exact hz1 hsq.symm

theorem twinElt_u_not_mem_right3 (e : TwinElt K T z) (hzT : IsClassicalMember3 T z)
    (hexT : classicalInvolutionOddCore T = ⊥) (hKT : Commutes K T) : e.u ∉ T := by
  intro h
  have hmem : e.a ∈ T := by
    have := T.mul_mem h (T.inv_mem e.mem_a')
    simpa [TwinElt.u] using this
  have hc : ∀ k ∈ T, k * e.a = e.a * k := fun k hk => (hKT _ e.mem_a _ hk).symm
  have hz2 : z * z = 1 := hzT.isCentralInvolution.sq
  have hz1 : z ≠ 1 := hzT.ne_one
  have hsq := e.mul_self_a
  rcases eq_one_or_eq_of_central3 hzT hexT hmem hc with h1 | h1
  · rw [h1, one_mul] at hsq
    exact hz1 hsq.symm
  · rw [h1, hz2] at hsq
    exact hz1 hsq.symm

theorem twinElt_orderOf_u3 (e : TwinElt K T z) (hz : IsClassicalMember3 K z)
    (hexK : classicalInvolutionOddCore K = ⊥) (hKT : Commutes K T) : orderOf e.u = 2 := by
  have hu2 : e.u * e.u = 1 := e.u_mul_self hKT hz.isCentralInvolution.sq
  have hu1 : e.u ≠ 1 := fun h => twinElt_u_not_mem_left3 e hz hexK hKT (h ▸ K.one_mem)
  exact orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1

theorem exists_twinElt_comm3 {β : Subgroup G} {t : G} (hz : IsClassicalMember3 K z)
    (hzT : IsClassicalMember3 T z) (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hTβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W T β) :
    ∃ e : TwinElt K T z, t * e.u = e.u * t := by
  obtain ⟨W, hW⟩ := hKβ
  obtain ⟨W', hW'⟩ := hTβ
  obtain ⟨a, ha, haa, hta⟩ := exists_sq_inverted_of_standardPair two_ne_zero_gf3 hW hz.mem
    hz.orderOf_eq_two ht.mem ht.orderOf_eq_two
  obtain ⟨a', ha', haa', hta'⟩ := exists_sq_inverted_of_standardPair two_ne_zero_gf3 hW' hzT.mem
    hzT.orderOf_eq_two ht.mem ht.orderOf_eq_two
  have hzz : z * z = 1 := hz.isCentralInvolution.sq
  have htt : t * t = 1 := ht.isCentralInvolution.sq
  have hzT' : ∀ x ∈ T, z * x = x * z := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (CFSG.ClassicalInvolution.isSubnormal_le hzT.subnormal hx) z
      (Set.mem_singleton z)
  refine ⟨⟨a, a', ha, ha', haa, haa'⟩, ?_⟩
  have hinv : ∀ {b : G}, b * b = z → b⁻¹ = b * z := fun {b} hb =>
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hb, hzz])
  have h1 : t * (a * a') * t = a⁻¹ * a'⁻¹ := by
    rw [← hta, ← hta']
    calc t * (a * a') * t = t * a * (t * t) * a' * t := by
          rw [htt]; simp only [mul_one, mul_assoc]
      _ = t * a * t * (t * a' * t) := by simp only [mul_assoc]
  have h2' : a⁻¹ * a'⁻¹ = a * a' := by
    rw [hinv haa, hinv haa']
    calc a * z * (a' * z) = a * (z * a') * z := by simp only [mul_assoc]
      _ = a * (a' * z) * z := by rw [hzT' a' ha']
      _ = a * a' * (z * z) := by simp only [mul_assoc]
      _ = a * a' := by rw [hzz, mul_one]
  have h3 : t * (a * a') * t = a * a' := h1.trans h2'
  show t * (a * a') = (a * a') * t
  calc t * (a * a') = t * (a * a') * (t * t) := by rw [htt, mul_one]
    _ = (t * (a * a') * t) * t := by simp only [mul_assoc]
    _ = a * a' * t := by rw [h3]

end Element

end CFSG.ClassicalInvolution.Q3.Q3TY

namespace CFSG.ClassicalInvolution.Q3.Q3TC.TCtx3

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G} (c : TCtx3 tY nY Ω K z)

include c

theorem isTwinAt3 {T : Subgroup G} (hT : T ∈ centralizingMembers Ω {z})
    (hTQ : locImg Ω z T ≤ c.d.Q₁) : IsTwinAt Ω K T z where
  mem := hT
  ne := c.twin_ne hT hTQ
  comm_T := fun _ hN hNT => c.commutes_T_of_ne hT hTQ hN hNT
  comm_K := fun _ hN hNK => c.commutes_K_of_ne hN hNK

theorem exists_isTwinAt3 : ∃ T, IsTwinAt Ω K T z := by
  obtain ⟨T, hT, hTQ⟩ := c.exists_twin
  exact ⟨T, c.isTwinAt3 hT hTQ.le⟩

theorem conjSub_twin_eq3 {t : G} (htz : t * z * t⁻¹ = z) (h2t : t * t = 1)
    (hKt : conjSub t K = K) {T : Subgroup G} (hT : T ∈ centralizingMembers Ω {z})
    (hTQ : locImg Ω z T ≤ c.d.Q₁) : conjSub t T = T := by
  by_contra hne
  have hΩ := c.hΩ.conjInvariant
  have hN₀z : conjSub t T ∈ centralizingMembers Ω {z} :=
    conjSub_mem_centralizingMembers3 hΩ htz hT
  have hTK : T ≠ K := c.twin_ne hT hTQ
  have hN₀K : conjSub t T ≠ K := fun h => hTK (by
    have := congrArg (conjSub t) h
    rwa [Gaps.conjSub_conjSub_self h2t, hKt] at this)
  have hall : ∀ L ∈ centralizingMembers Ω {z}, L ≠ conjSub t T → Commutes (conjSub t T) L := by
    intro L hL hLN
    have hL' : conjSub t L ∈ centralizingMembers Ω {z} :=
      conjSub_mem_centralizingMembers3 hΩ htz hL
    have hne' : conjSub t L ≠ T := fun h => hLN (by
      rw [← Gaps.conjSub_conjSub_self h2t L, h])
    have h1 := (c.commutes_T_of_ne hT hTQ hL' hne').conjSub t
    rwa [Gaps.conjSub_conjSub_self h2t] at h1
  have hN₀Q : ¬ locImg Ω z (conjSub t T) ≤ c.d.Q₁ := fun h =>
    hne (c.eq_of_locImg_le_Q₁ hN₀z hT h hTQ)
  obtain ⟨R₀, hR₀, hR₀eq⟩ := c.exists_fund_of_ne hN₀z hN₀K hN₀Q
  obtain ⟨R', hR', W, hW⟩ := c.hY.std R₀ hR₀
  obtain ⟨N', hN'z, -, -, hN'eq⟩ := c.exists_member_of_fund hR'
  have hnc : ¬ Commutes (conjSub t T) N' := fun h =>
    not_commutes_of_linearBlockStandardPair hW
      ((c.commutes_iff_fund hN₀z hN'z hR₀ hR₀eq hN'eq).mp h)
  have hN'N₀ : N' ≠ conjSub t T := fun h => ne_of_linearBlockStandardPair hW
    (eq_of_map_eq_of_pow3 c.d.ψ c.d.ker_le c.ker_cop (c.hY.pow3 R₀ hR₀) (c.hY.pow3 R' hR')
      (by rw [← hR₀eq, ← hN'eq, h]))
  exact hnc (hall N' hN'z hN'N₀)

theorem ne_and_not_le_Q₁3 {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {z})
    (hL' : L' ∈ centralizingMembers Ω {z}) (hne : L ≠ L') (hnc : ¬ Commutes L L') :
    L ≠ K ∧ ¬ locImg Ω z L ≤ c.d.Q₁ := by
  constructor
  · intro hLK
    exact hnc (hLK ▸ c.commutes_K_of_ne hL' (fun h => hne (hLK.trans h.symm)))
  · intro h
    obtain ⟨T, hT, hTQ⟩ := c.exists_twin
    have hLT : L = T := c.eq_of_locImg_le_Q₁ hL hT h hTQ.le
    exact hnc (hLT ▸ c.commutes_T_of_ne hT hTQ.le hL' (fun h' => hne (hLT.trans h'.symm)))

theorem sign_config3
    (hcls : tY = .PSL ∨ tY = .PSU ∨ tY = .PSp ∨ tY = .POmegaOdd ∨ tY = .POmegaPlus ∨
      tY = .POmegaMinus)
    (hadm : StatedLieAdmissible tY nY 3 1) {a b d : Subgroup G} {za zb : G}
    (ha : a ∈ centralizingMembers Ω {z}) (hb : b ∈ centralizingMembers Ω {z})
    (hd : d ∈ centralizingMembers Ω {z}) (hwa : IsClassicalMember3 a za)
    (hwb : IsClassicalMember3 b zb) (hwd : IsClassicalMember3 d za) (hab : a ≠ b) (hbd : b ≠ d)
    (hpair : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W a b) (hnbd : ¬ Commutes b d)
    (had : Commutes a d) (hna : conjSub zb a = a) :
    ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W b d := by
  obtain ⟨W, hW⟩ := hpair
  have hnab : ¬ Commutes a b := not_commutes_of_linearBlockStandardPair hW
  have hnbd' : ¬ Commutes d b := fun h => hnbd (commutes_symm h)
  obtain ⟨haK, haQ⟩ := c.ne_and_not_le_Q₁3 ha hb hab hnab
  obtain ⟨hbK, hbQ⟩ := c.ne_and_not_le_Q₁3 hb hd hbd hnbd
  obtain ⟨hdK, hdQ⟩ := c.ne_and_not_le_Q₁3 hd hb hbd.symm hnbd'
  obtain ⟨Ra, hRa, haR⟩ := c.exists_fund_of_ne ha haK haQ
  obtain ⟨Rb, hRb, hbR⟩ := c.exists_fund_of_ne hb hbK hbQ
  obtain ⟨Rd, hRd, hdR⟩ := c.exists_fund_of_ne hd hdK hdQ
  have hzbY : zb ∈ locLayer Ω z := le_centralizingLayer hb hwb.mem
  have hu₁ := ConnectedA2.isUniqueInvolution_locImg c.hex ha
    (isUniqueInvolution_of_exact3 (c.hex a ha.1) hwa)
  have hu₂ := ConnectedA2.isUniqueInvolution_locImg c.hex hb
    (isUniqueInvolution_of_exact3 (c.hex b hb.1) hwb)
  have hu₃ := ConnectedA2.isUniqueInvolution_locImg c.hex hd
    (isUniqueInvolution_of_exact3 (c.hex d hd.1) hwd)
  rw [haR] at hu₁
  rw [hbR] at hu₂
  rw [hdR] at hu₃
  have hcen : ∀ y : locQuot Ω z, Gaps.locMk Ω z ⟨za, le_centralizingLayer ha hwa.mem⟩ *
      Gaps.locMk Ω z ⟨za, le_centralizingLayer hd hwd.mem⟩ * y =
      y * (Gaps.locMk Ω z ⟨za, le_centralizingLayer ha hwa.mem⟩ *
        Gaps.locMk Ω z ⟨za, le_centralizingLayer hd hwd.mem⟩) := fun y => by
    rw [hu₁.sq]
    simp
  have hnorm : conjSub (Gaps.locMk Ω z ⟨zb, hzbY⟩) (Ra.map c.d.ψ) = Ra.map c.d.ψ := by
    have h := Gaps.locImg_conjSub_layer (Ω := Ω) (x := z) a ⟨zb, hzbY⟩
    rw [show ((⟨zb, hzbY⟩ : ↥(locLayer Ω z)) : G) = zb from rfl, hna] at h
    rw [← haR]
    exact h.symm
  have key := chainSign_of_lifts3 hcls hadm c.d.ψ c.d.ker_le hRa hRb hRd hu₁ hu₂ hu₃ hcen hnorm
    (by
      rw [← haR, ← hdR]
      exact commutes_locImg_of_commutes had)
    (by
      rw [← haR, ← hbR]
      intro h
      exact hab (locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 ha hb h))
    (by
      rw [← hdR, ← hbR]
      intro h
      exact hbd (locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 hb hd h.symm))
    (by
      rw [← haR, ← hbR]
      exact fun h => hnab (commutes_of_commutes_locImg3 c.hΩ c.hex c.hP1 c.hO3 ha hb h))
    (by
      rw [← hdR, ← hbR]
      exact fun h => hnbd' (commutes_of_commutes_locImg3 c.hΩ c.hex c.hP1 c.hO3 hd hb h))
  rw [← haR, ← hbR, ← hdR] at key
  have h1 := linearBlockStandardPair_locImg_of_members c.hP1 ha hb hW
  rcases key with ⟨-, ⟨W₂, hW₂⟩⟩ | ⟨hu, -⟩
  · exact linearBlockStandardPair_of_locImg3' c.hΩ c.hex c.hP1 c.hO3 hb hd hW₂
  · exact (false_of_linear_of_unitary3 h1 hu).elim

end CFSG.ClassicalInvolution.Q3.Q3TC.TCtx3
