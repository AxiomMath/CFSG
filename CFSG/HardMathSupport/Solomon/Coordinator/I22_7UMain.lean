module

public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7UDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7CmpC
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7MainR
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7TrFi

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs

section Basic

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem i227um_oThreeIn_normal (W : Subgroup K) : (oThreeIn W).Normal :=
  Subgroup.sSup_normal _ fun _ h => h.2.1

omit [Finite K] in
theorem i227um_oThreeIn_isPGroup (W : Subgroup K) : IsPGroup 3 (oThreeIn W) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact Sylow.sSup_of_normal _ (fun _ h => h.2.2) (fun _ h => h.2.1)

theorem i227um_le_of_normal {N P : Subgroup K} [N.Normal] (hN : IsPGroup 3 N)
    (hPc : Nat.card P = 3 ^ (Nat.card K).factorization 3) : N ≤ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact hN.le_sylow_of_normal (Sylow.ofCard P hPc)

omit [Finite K] in
theorem i227um_gLBConj_normal (U : Subgroup K) [U.Normal] (k : K) : GLBConj k U = U := by
  ext y
  rw [mem_gLBConj]
  refine ⟨fun h => ?_, fun h => Subgroup.Normal.conj_mem inferInstance y h k⟩
  simpa [mul_assoc] using Subgroup.Normal.conj_mem inferInstance _ h k⁻¹

omit [Finite K] in
theorem i227um_isElemAbelian_gLBConj {E : Subgroup K} (h : IsElemAbelian 3 E) (k : K) :
    IsElemAbelian 3 (GLBConj k E) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · have ha := mem_gLBConj.1 a.2
    have hb := mem_gLBConj.1 b.2
    have := congrArg (fun z : E => (z : K))
      (h.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
    apply Subtype.ext
    have h2 : k * (a * b : K) * k⁻¹ = k * (b * a : K) * k⁻¹ := by
      simpa [mul_assoc] using this
    simpa using h2
  · have hx' := mem_gLBConj.1 hx
    have := h.2 _ hx'
    have e : (k * x * k⁻¹) ^ 3 = k * x ^ 3 * k⁻¹ := by simp [conj_pow]
    rw [e] at this
    simpa using this

end Basic

section Family

variable {K : Type} [Group K] [Finite K]

@[expose] def i227umF (U : Subgroup K) : Set (Subgroup K) :=
  {Q | Q ≤ U ∧ 2 ≤ CFSG.Open.pRank 3 Q ∧
    ∃ E : Subgroup K, E ≤ U ∧ IsElemAbelian 3 E ∧ Q ≤ E ∧ 3 ≤ CFSG.Open.pRank 3 E}

@[expose] def i227umH (U : Subgroup K) : Subgroup K :=
  ⨆ Q ∈ i227umF U, Subgroup.normalizer (Q : Set K)

theorem i227umF_gLBConj {U : Subgroup K} [U.Normal] {Q : Subgroup K} (hQ : Q ∈ i227umF U)
    (k : K) : GLBConj k Q ∈ i227umF U := by
  obtain ⟨hQU, h2, E, hEU, hE, hQE, h3⟩ := hQ
  have hU : GLBConj k U = U := i227um_gLBConj_normal U k
  refine ⟨hU ▸ gLBConj_mono k hQU, ?_, GLBConj k E, hU ▸ gLBConj_mono k hEU,
    i227um_isElemAbelian_gLBConj hE k, gLBConj_mono k hQE, ?_⟩
  · rwa [pRank_gLBConj Nat.prime_three]
  · rwa [pRank_gLBConj Nat.prime_three]

theorem i227umH_ge {U : Subgroup K} {Q : Subgroup K} (hQ : Q ∈ i227umF U) :
    Subgroup.normalizer (Q : Set K) ≤ i227umH U :=
  le_iSup₂_of_le Q hQ le_rfl

theorem i227umH_normal (U : Subgroup K) [U.Normal] : (i227umH U).Normal := by
  have h1 : ∀ g : K, i227umH U ≤ (i227umH U).comap (MulAut.conj g).toMonoidHom := by
    intro g
    refine iSup₂_le fun Q hQ h hh => ?_
    have hQ' : GLBConj g⁻¹ Q ∈ i227umF U := i227umF_gLBConj hQ g⁻¹
    have hmem : g * h * g⁻¹ ∈ Subgroup.normalizer (GLBConj g⁻¹ Q : Set K) := by
      rw [normalizer_gLBConj, mem_gLBConj]
      simpa [mul_assoc] using hh
    exact i227umH_ge hQ' hmem
  exact ⟨fun n hn g => by simpa using h1 g hn⟩

theorem i227umH_le {U P : Subgroup K} (hUP : U ≤ P) : i227umH U ≤ weakCoreIn 3 P ⊤ := by
  refine iSup₂_le fun Q hQ => ?_
  obtain ⟨hQU, h2, E, hEU, hE, hQE, h3⟩ := hQ
  have hEc : E ≤ Subgroup.centralizer (Q : Set K) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have := congrArg (fun z : E => (z : K))
      (hE.1.is_comm.comm ⟨q, hQE hq⟩ ⟨e, he⟩)
    simpa using this
  have hr3 : 3 ≤ CFSG.Open.pRank 3 (Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set K))) :=
    h3.trans (CFSG.SectionRank.pRank_mono (by norm_num)
      (le_sup_of_le_right (le_inf (hEU.trans hUP) hEc)))
  exact le_iSup₂_of_le Q ⟨hQU.trans hUP, h2, hr3⟩ (top_inf_eq _).ge

omit [Finite K] in
theorem i227um_le_normalizer {P Q : Subgroup K} (hQP : Q ≤ P) (hn : (Q.subgroupOf P).Normal) :
    P ≤ Subgroup.normalizer (Q : Set K) := by
  intro x hx
  have key : ∀ y ∈ P, ∀ h ∈ Q, y * h * y⁻¹ ∈ Q := by
    intro y hy h hh
    have : (⟨y, hy⟩ : P) * ⟨h, hQP hh⟩ * (⟨y, hy⟩ : P)⁻¹ ∈ Q.subgroupOf P :=
      hn.conj_mem ⟨h, hQP hh⟩ (Subgroup.mem_subgroupOf.2 hh) ⟨y, hy⟩
    exact Subgroup.mem_subgroupOf.1 this
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key x hx h, fun h' => ?_⟩
  have := key x⁻¹ (P.inv_mem hx) _ h'
  simpa [mul_assoc] using this

end Family

section Quotient

variable {K : Type} [Group K]

theorem i227um_sup_eq_top {R : Subgroup K} [R.Normal] (hS : IsSimpleGroup (K ⧸ R))
    {H P : Subgroup K} [H.Normal] (hPH : P ≤ H) (hbig : 1 < Nat.card (P.map (QuotientGroup.mk' R))) :
    H ⊔ R = ⊤ := by
  have hmapn : (H.map (QuotientGroup.mk' R)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective R)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hS _ hmapn with h | h
  · exfalso
    have hle : P.map (QuotientGroup.mk' R) ≤ ⊥ := h ▸ Subgroup.map_mono hPH
    rw [le_bot_iff] at hle
    rw [hle, Subgroup.card_bot] at hbig
    exact absurd hbig (lt_irrefl 1)
  · have := Subgroup.comap_map_eq (QuotientGroup.mk' R) H
    rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
    exact this.symm

end Quotient

section Main

theorem i227_threeRankU_of_UQ
    (hUQ : I22_7UQ) : I22_7ThreeRankU := by
  intro K _ _ hK _ W _ _ _ h3 P hP3 hPc _
  have : (oThreeIn W).Normal := i227um_oThreeIn_normal W
  have hUP : oThreeIn W ≤ P := i227um_le_of_normal (i227um_oThreeIn_isPGroup W) hPc
  obtain ⟨Q0, hQ0U, hQ0n, hQ02, E0, hE0U, hE0, hQE0, hE03⟩ :=
    hUQ K P (oThreeIn W) hP3 hUP (Subgroup.Normal.subgroupOf inferInstance P) h3
  have hQ0F : Q0 ∈ i227umF (oThreeIn W) := ⟨hQ0U, hQ02, E0, hE0U, hE0, hQE0, hE03⟩
  have hPH : P ≤ i227umH (oThreeIn W) :=
    (i227um_le_normalizer (hQ0U.trans hUP) hQ0n).trans (i227umH_ge hQ0F)
  have : (i227umH (oThreeIn W)).Normal := i227umH_normal _
  obtain ⟨hS, hnc, h3d⟩ := i227m_fi22_facts hK.fi
  obtain ⟨-, hPcard⟩ := i227m_sylow_map hP3 hPc (GLAPPrimeCore 5 K)
  have hpos := Nat.prime_three.factorization_pos_of_dvd Nat.card_pos.ne' h3d
  have hbig : 1 < Nat.card (P.map (QuotientGroup.mk' (GLAPPrimeCore 5 K))) := by
    rw [hPcard]
    exact Nat.one_lt_pow hpos.ne' (by norm_num)
  have htop : i227umH (oThreeIn W) = ⊤ :=
    i227cmp_cover_eq_top hK hS hnc _ (i227um_sup_eq_top hS hPH hbig)
  exact htop.symm.le.trans (i227umH_le hUP)

end Main

end CFSG.HardMathSupport.Solomon.Coordinator
