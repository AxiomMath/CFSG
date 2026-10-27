module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinReduce
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetDefs

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TwinSet

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {N : Subgroup Y} [N.Normal]

@[expose] def oddCl (B : Subgroup Y) : Subgroup Y :=
  Subgroup.closure {x : Y | x ∈ B ∧ Odd (orderOf x)}

omit [Finite Y] [N.Normal] in
theorem conjSub_oddCl (c : Y) (B : Subgroup Y) : conjSub c (oddCl B) = oddCl (conjSub c B) := by
  unfold conjSub oddCl
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxB, hxo⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · exact conj_mem_conjSub hxB
    · show Odd (orderOf ((MulAut.conj c) x))
      rw [MulAut.conj_apply, orderOf_conj_eq]
      exact hxo
  · rintro ⟨hyB, hyo⟩
    refine ⟨c⁻¹ * y * c, ⟨?_, ?_⟩, ?_⟩
    · exact mem_conjSub_iff.mp hyB
    · have h := orderOf_conj_eq c⁻¹ y
      rw [inv_inv] at h
      rw [h]
      exact hyo
    · show c * (c⁻¹ * y * c) * c⁻¹ = y
      group

omit [Finite Y] in
theorem conjSub_comap (c : Y) (A : Subgroup (Y ⧸ N)) :
    conjSub c (A.comap (QuotientGroup.mk' N)) =
      (conjSub (QuotientGroup.mk' N c) A).comap (QuotientGroup.mk' N) := by
  ext x
  rw [mem_conjSub_iff, Subgroup.mem_comap, Subgroup.mem_comap, mem_conjSub_iff]
  simp

theorem map_mem_twinSet (hd : Q8TwinDatum R S t) (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N)
    {J : Subgroup Y} (hJ : J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    J.map (QuotientGroup.mk' N) ∈ twinSet
      (CoreAssembly.conjClass (tightCore (R.map (QuotientGroup.mk' N))))
      (tightCore (R.map (QuotientGroup.mk' N))) := by
  have hRN := TwinRed.inf_eq_bot hd hN2 htN
  have h0 := TwinRed.core_inf_eq_bot hd hN2 htN
  have hodd : ∀ K ∈ CoreAssembly.conjClass (tightCore R), Odd (Nat.card ↥(N ⊓ K)) :=
    fun K hK => TwinRed.odd_of_inf_eq_bot (TwinRed.inf_conj_eq_bot h0 hK)
  have htU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hd
  obtain ⟨hKΩ, z, hz₀, hz'⟩ := hJ
  have hzt : t = z := htU.eq hz₀
  rw [← hzt] at hz'
  refine ⟨TwistQ.map_mem_conjClass hRN hKΩ, QuotientGroup.mk' N t, ?_, ?_⟩
  · rw [← TwistQ.tightCore_map hRN]
    exact isUniqueInvolution_map_mk_of_odd (hodd _ (CoreAssembly.mem_conjClass_self _)) htU
  · exact isUniqueInvolution_map_mk_of_odd (hodd _ hKΩ) hz'

theorem isUniqueInvolution_of_mem_twinSet (hd : Q8TwinDatum R S t) {J : Subgroup Y}
    (hJ : J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    IsUniqueInvolution J t := by
  have htU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hd
  obtain ⟨-, z, hz₀, hz'⟩ := hJ
  rw [htU.eq hz₀]
  exact hz'

theorem longFundSetE3_of_quot (hd : Q8TwinDatum R S t)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hNc : N ≤ Subgroup.center Y) (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N)
    (hL : LongFundSetE3 (R.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N t)) :
    LongFundSetE3 R t := by
  classical
  obtain ⟨Λb, hΛb, hcommb, heqvb⟩ := hL
  set π := QuotientGroup.mk' N with hπ
  have hRN := TwinRed.inf_eq_bot hd hN2 htN
  have h0 := TwinRed.core_inf_eq_bot hd hN2 htN
  have hodd : ∀ K ∈ CoreAssembly.conjClass (tightCore R), Odd (Nat.card ↥(N ⊓ K)) :=
    fun K hK => TwinRed.odd_of_inf_eq_bot (TwinRed.inf_conj_eq_bot h0 hK)
  have hlift : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∃ M : Subgroup Y, M = oddCl ((Λb (J.map π)).comap π) ∧ J ≤ M ∧
        M ≤ Subgroup.centralizer ({t} : Set Y) ∧ IsClassicalMember3 M t := by
    intro J hJ
    have hmem := map_mem_twinSet hd hN2 htN hJ
    obtain ⟨M, hMdef, -, hKM, hMC, hMcl⟩ := TwinRed.lift_member hΩ hNc hN2 hRN h0 hd.order hJ.1
      (isUniqueInvolution_of_mem_twinSet hd hJ) (hΛb _ hmem).2 (hΛb _ hmem).1
    exact ⟨M, hMdef, hKM, hMC, hMcl⟩
  refine ⟨fun J => oddCl ((Λb (J.map π)).comap π), ?_, ?_, ?_⟩
  · intro J hJ
    obtain ⟨M, hMdef, hKM, -, hMcl⟩ := hlift J hJ
    show J ≤ oddCl ((Λb (J.map π)).comap π) ∧ IsClassicalMember3 (oddCl ((Λb (J.map π)).comap π)) t
    rw [← hMdef]
    exact ⟨hKM, hMcl⟩
  · intro J hJ J' hJ' hne
    have hne' : J.map π ≠ J'.map π := fun h => hne (TwinRed.eq_of_map hΩ hNc hodd hJ.1 hJ'.1 h)
    exact TwinRed.commute_closure_odd hNc hN2
      (hcommb _ (map_mem_twinSet hd hN2 htN hJ) _ (map_mem_twinSet hd hN2 htN hJ') hne')
  · intro J hJ c hc
    have hπc : π c ∈ Subgroup.centralizer ({π t} : Set (Y ⧸ N)) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp hc]
    have h1 := heqvb _ (map_mem_twinSet hd hN2 htN hJ) (π c) hπc
    rw [← TwistQ.conjSub_map] at h1
    show conjSub c (oddCl ((Λb (J.map π)).comap π)) =
      oddCl ((Λb ((conjSub c J).map π)).comap π)
    rw [conjSub_oddCl, conjSub_comap, h1]

end TwinSet

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
