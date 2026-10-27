module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapP3
import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA9P

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace SwapP2

theorem pumpData_type_eleven (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
    {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 11)} {E : Subgroup X} {D : Finset (Fin 11)}
    {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin 11)} {r : X} {N₁ : Subgroup X}
    (hs : Setting t J 11 e E D M) (hd : Data t J 11 e E D M e₀ F DF r)
    (χr : ↥(fixA M e₀ r) ⧸ pPrimeCore 2 ↥(fixA M e₀ r) ≃* alternatingGroup (Fin (11 - 4)))
    (hArle : fixA M e₀ r ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hArpc : IsPComponent 2 ((fixA M e₀ r).subgroupOf
      (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))))
    (hP : PumpData M e₀ r N₁) :
    (conjBy N₁ e₀ = N₁ ∧
        IsPComponent 2 ((fixA M e₀ r).subgroupOf (N₁ ⊓ centralizer ({e₀} : Set X))) ∧
        ∃ m : ℕ, Odd m ∧ 7 ≤ m ∧ m ≤ 11 ∧
          Nonempty (↥N₁ ⧸ pPrimeCore 2 ↥N₁ ≃* alternatingGroup (Fin m))) ∨
      (conjBy N₁ e₀ = N₁ ∧
        Nonempty (↥N₁ ⧸ Open.fusionZStar ↥N₁ ≃* Blueprint.NativeSporadic.He)) ∨
      (conjBy N₁ e₀ ≠ N₁ ∧
        Nonempty (↥N₁ ⧸ Open.fusionZStar ↥N₁ ≃* alternatingGroup (Fin 7))) := by
  classical
  have S := hs.sig
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ hd.e₀E
  have he₀o : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀2) hd.e₀1
  have hr2 : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hd.r2) hd.r1
  have he₀r : e₀ ∈ centralizer ({r} : Set X) := mem_centralizer_singleton_iff.mpr hd.re₀.symm
  have hArle' : fixA M e₀ r ≤ centralizer ({e₀} : Set X) ⊓ centralizer ({r} : Set X) := by
    rw [inf_comm]
    exact hArle
  have hArpc' : IsPComponent 2 ((fixA M e₀ r).subgroupOf
      (centralizer ({e₀} : Set X) ⊓ centralizer ({r} : Set X))) := by
    rw [inf_comm]
    exact hArpc
  obtain ⟨N, hNC, hNpc, hcov, hbr⟩ := exists_pump_data_seven hPump hN1 S.nonab S.kProper S.unbal
    S.notU (by norm_num) S.pair.2.2.2.1 hr2 he₀o he₀r hArle' hArpc' χr
  have hN₁N : N₁ = N ∨ N₁ = conjBy N e₀ := by
    rcases eq_or_eq_of_pumpData he₀r he₀2 hP hNC hNpc hcov with h | h
    · exact Or.inl h.symm
    · right
      rw [h, conjBy_conjBy_of_mul_self N₁ he₀2]
  have hfixN : conjBy N e₀ = N → N₁ = N := fun hfix => by
    rcases hN₁N with h | h
    · exact h
    · rw [h]
      exact hfix
  rcases hbr with ⟨m, hmo, hm7, hm11, ⟨θN⟩, hfix, hpc⟩ | ⟨hfix, hpc, ⟨ψ⟩⟩ | ⟨hne, ⟨ψ⟩⟩
  · obtain rfl := hfixN hfix
    exact Or.inl ⟨hfix, hpc, m, hmo, hm7, hm11, ⟨θN⟩⟩
  · obtain rfl := hfixN hfix
    exact Or.inr (Or.inl ⟨hfix, ⟨ψ⟩⟩)
  · right
    right
    rcases hN₁N with rfl | rfl
    · exact ⟨hne, ⟨ψ⟩⟩
    · refine ⟨?_, ⟨(Sol78.fusionZStarQuotCongr (N.equivMapOfInjective
        (MulAut.conj e₀).toMonoidHom (MulAut.conj e₀).injective)).symm.trans ψ⟩⟩
      rw [conjBy_conjBy_of_mul_self N he₀2]
      exact fun h => hne h.symm

theorem isSolomonMember_of_pump [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
    {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
    {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin n)} {r : X} {N₁ : Subgroup X}
    (hs : Setting t J n e E D M) (hd : Data t J n e E D M e₀ F DF r)
    (he₀H : centralizer ({e₀} : Set X) ≤ Hn E) (hP : PumpData M e₀ r N₁)
    (hfix : conjBy N₁ e₀ = N₁) (hN₁H : N₁ ≤ Hn E) : FooteLit.IsSolomonMember M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMr := fixedLayerComponent_holds X t J n e E D M hs e₀ F DF r hd he₀H N₁ hP hfix hN₁H
  have htH : t ∈ Hn E := hs.cent (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hs.le hs.pc htH
  have hMtK : conjBy M t ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hs.le hMtH hs.pc hMtpc (Ne.symm hs.swap)
  have hr2 : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hd.r2) hd.r1
  have hR2 : IsPGroup 2 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr2, pow_one])
  obtain ⟨-, -, hMq⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M (Hn E) hs.le).mp hs.pc
  have hperf : ⁅M, M⁆ = M := UnbalancedCorr.commutator_eq_of_isPComponent hs.le hs.pc
  refine memberOfFixedLayer_holds X M (zpowers r) hperf hMq
    (fun h => hd.r1 (zpowers_eq_bot.mp h)) hR2 (zpowers_le.mpr (hMtK hd.rM)) ?_
  rwa [centralizer_zpowers_eq' r]

end SwapP2

end CFSG.ComponentClassification.SolMax
