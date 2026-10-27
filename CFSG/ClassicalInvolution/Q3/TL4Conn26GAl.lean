module

public import CFSG.ClassicalInvolution.Q3.TL4Conn26S4B
public import CFSG.ClassicalInvolution.Q3.TL4OddBasic

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Triv

variable {G : Type} [Group G] [Finite G]

@[expose] def actTrivOdd (K : Subgroup G) : Subgroup G where
  carrier := {a | a ∈ Subgroup.normalizer (K : Set G) ∧ ∀ k ∈ K, ⁅a, k⁆ ∈ oddCoreOf K}
  one_mem' := ⟨one_mem _, fun k _ => by
    rw [commutatorElement_def]
    simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(Subgroup.normalizer (K : Set G)).mul_mem ha hb, fun k hk => ?_⟩
    have haO := mem_normalizer_oddCore_of_mem_normalizer ha
    have h1 : a * ⁅b, k⁆ * a⁻¹ ∈ oddCoreOf K :=
      (Subgroup.mem_normalizer_iff.mp haO _).mp (hb' k hk)
    have e : ⁅a * b, k⁆ = a * ⁅b, k⁆ * a⁻¹ * ⁅a, k⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (oddCoreOf K).mul_mem h1 (ha' k hk)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have hai : a⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normalizer (K : Set G)).inv_mem ha
    refine ⟨hai, fun k hk => ?_⟩
    have haO := mem_normalizer_oddCore_of_mem_normalizer hai
    have h1 : a⁻¹ * ⁅a, k⁆⁻¹ * a⁻¹⁻¹ ∈ oddCoreOf K :=
      (Subgroup.mem_normalizer_iff.mp haO _).mp ((oddCoreOf K).inv_mem (ha' k hk))
    have e : ⁅a⁻¹, k⁆ = a⁻¹ * ⁅a, k⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h1

end Triv

section Cit3

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.omegaNbrGen_le_centralizer_of_alpha (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hα : TightSepAlpha Rd z) :
    omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≤
      Subgroup.centralizer ({z} : Set Y) := by
  refine iSup₂_le fun M hM => ?_
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hs.hyp hM.1
  exact edge_le_centralizer_of_alpha hs.large.datum hM hu (hα M hM u hu)

theorem TightStd8R.omegaNbrGen_ne_top_of_alpha (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hα : TightSepAlpha Rd z) :
    omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤ := by
  intro htop
  have hle := hs.omegaNbrGen_le_centralizer_of_alpha hα
  rw [htop] at hle
  have hzc : z ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))
  rw [hs.large.center, Subgroup.mem_bot] at hzc
  exact hs.hz.ne_one hzc

theorem TightStd8R.sup_omegaNbrGen_ne_top_of_alpha (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hα : TightSepAlpha Rd z) :
    tightCore Rd ⊔ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤ := by
  intro htop
  have hle : tightCore Rd ⊔ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≤
      Subgroup.centralizer ({z} : Set Y) :=
    sup_le ((TightLargeHypR.typeRFam hs.large).le_centralizer hs.mem hs.hz)
      (hs.omegaNbrGen_le_centralizer_of_alpha hα)
  rw [htop] at hle
  have hzc : z ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))
  rw [hs.large.center, Subgroup.mem_bot] at hzc
  exact hs.hz.ne_one hzc

theorem TightStd8R.not_le_omegaNbrGen_of_alpha (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hα : TightSepAlpha Rd z) :
    ¬ tightCore Rd ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := by
  intro hKX
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ := hs.hyp
  have hXN : omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≤
      Subgroup.normalizer ((tightCore Rd : Subgroup Y) : Set Y) :=
    (hs.omegaNbrGen_le_centralizer_of_alpha hα).trans hs.large.datum.le_normalizer_core
  have hle : omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≤
      actTrivOdd (tightCore Rd) := by
    refine iSup₂_le fun M hM => ?_
    intro m hm
    have hmN : m ∈ Subgroup.normalizer ((tightCore Rd : Subgroup Y) : Set Y) :=
      hXN (le_omegaNbrGen hM hm)
    refine ⟨hmN, fun k hk => ?_⟩
    obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hΩ hM.1
    have hKN : tightCore Rd ≤ Subgroup.normalizer (M : Set Y) :=
      (tightCore_centralizer_of_alpha hs.large.datum hM hu (hα M hM u hu)).trans
        (h.tight M hM.1 u hu)
    have hmem : ⁅m, k⁆ ∈ tightCore Rd ⊓ M := by
      refine ⟨?_, ?_⟩
      · have h1 : m * k * m⁻¹ ∈ tightCore Rd := (Subgroup.mem_normalizer_iff.mp hmN k).mp hk
        rw [commutatorElement_def]
        exact (tightCore Rd).mul_mem h1 ((tightCore Rd).inv_mem hk)
      · have h1 : k * m⁻¹ * k⁻¹ ∈ M :=
          (Subgroup.mem_normalizer_iff.mp (hKN hk) m⁻¹).mp (M.inv_mem hm)
        rw [commutatorElement_def]
        have e : m * k * m⁻¹ * k⁻¹ = m * (k * m⁻¹ * k⁻¹) := by group
        rw [e]
        exact M.mul_mem hm h1
    obtain ⟨hv, hv1⟩ := hΩ.omega4 _ hs.mem M hM.1 (Ne.symm hM.2.1)
    by_cases hp : padicValNat 2 (Nat.card ↥(tightCore Rd ⊓ M)) = 1
    · have hc : ⁅m, k⁆ ∈ ⁅tightCore Rd, M⁆ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hm hk
      exact (hv1 hp hc).1
    · have h0 : padicValNat 2 (Nat.card ↥(tightCore Rd ⊓ M)) = 0 := by omega
      have hc0 : Nat.card ↥(tightCore Rd ⊓ M) ≠ 0 := Nat.card_pos.ne'
      have hnd : ¬ 2 ∣ Nat.card ↥(tightCore Rd ⊓ M) := by
        rcases padicValNat.eq_zero_iff.mp h0 with h2 | h2 | h2
        · exact absurd h2 (by norm_num)
        · exact absurd h2 hc0
        · exact h2
      have hodd : Odd (Nat.card ↥(tightCore Rd ⊓ M)) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hnd)
      have hnorm : tightCore Rd ≤
          Subgroup.normalizer ((tightCore Rd ⊓ M : Subgroup Y) : Set Y) := by
        intro k' hk'
        have hk'M := hKN hk'
        rw [Subgroup.mem_normalizer_iff] at hk'M ⊢
        intro w
        constructor
        · rintro ⟨hwK, hwM⟩
          exact ⟨(tightCore Rd).mul_mem ((tightCore Rd).mul_mem hk' hwK)
            ((tightCore Rd).inv_mem hk'), (hk'M w).mp hwM⟩
        · rintro ⟨hwK, hwM⟩
          refine ⟨?_, (hk'M w).mpr hwM⟩
          have := (tightCore Rd).mul_mem ((tightCore Rd).mul_mem ((tightCore Rd).inv_mem hk') hwK)
            hk'
          simpa [mul_assoc] using this
      exact le_oddCoreOf_of_normal_odd inf_le_left hnorm hodd hmem
  obtain ⟨-, P, hP, hPnc⟩ := hΩ.omega1 _ hs.mem
  apply hPnc
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have ha : (a : Y) ∈ actTrivOdd (tightCore Rd) := hle (hKX (hP.1 a.2))
  have h1 : ⁅(a : Y), (b : Y)⁆ ∈ oddCoreOf (tightCore Rd) := ha.2 b (hP.1 b.2)
  have h2 : ⁅(a : Y), (b : Y)⁆ ∈ P := by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem a.2 b.2) (P.inv_mem a.2)) (P.inv_mem b.2)
  have h3 : ⁅(a : Y), (b : Y)⁆ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) h1
      (hP.2.1.to_le (Subgroup.zpowers_le.mpr h2))
  exact commutatorElement_eq_one_iff_mul_comm.mp h3

theorem TightStd8R.not_muIsoS4_of_alpha (hD : TightS26DichR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t) (hα : TightSepAlpha Rd z) :
    ¬ MuIsoS4 (CoreAssembly.conjClass (tightCore Rd)) W :=
  hs.not_muIsoS4_of hD (hs.omegaNbrGen_ne_top_of_alpha hα) (hs.not_le_omegaNbrGen_of_alpha hα)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
