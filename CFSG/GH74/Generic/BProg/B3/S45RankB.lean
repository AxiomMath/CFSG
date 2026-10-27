module

public import CFSG.GH74.Generic.BProg.B3.S45RankA
public import CFSG.GH74.Generic.BProg.B3.LocBalJ1

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.Blueprint CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution.Balance Subgroup

theorem center_eq_bot_of_M12 {Jt : Type} [Group Jt] (hJ : NativeSporadic.IsSporadic Jt .M12) :
    ∀ z : Jt, (∀ g : Jt, g * z = z * g) → z = 1 := by
  obtain ⟨e⟩ : Nonempty (Jt ≃* ↥NativeSporadic.M12) := hJ
  intro z hz
  have h1 : e z ∈ Subgroup.center ↥NativeSporadic.M12 := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hz g']
  rw [ComponentClassification.M12Cover.m12_center, Subgroup.mem_bot] at h1
  exact e.injective (by rw [h1, map_one])

section Main


theorem involutionOddCore_eq_bot_of_M12 {Jt : Type} [Group Jt] (hJ : NativeSporadic.IsSporadic Jt .M12)
    {H : Subgroup (MulAut Jt)} (hH : (MulAut.conj : Jt →* MulAut Jt).range ≤ H) {b : ↥H}
    (hb2 : b * b = 1) (hb1 : b ≠ 1) : involutionOddCore b = ⊥ := by
  classical
  have hZ := center_eq_bot_of_M12 hJ
  obtain ⟨e⟩ : Nonempty (Jt ≃* ↥NativeSporadic.M12) := hJ
  have hfin : Finite Jt := Finite.of_injective e e.injective
  have hinj : Function.Injective (MulAut.conj : Jt →* MulAut Jt) := LocBalJ1.conj_injective_of_center hZ
  set S : Subgroup ↥H := (MulAut.conj : Jt →* MulAut Jt).range.subgroupOf H with hSdef
  have hSn : S.Normal := inferInstance
  have eS : ↥S ≃* NativeSporadic.M12 :=
    (Subgroup.subgroupOfEquivOfLe hH).trans ((MonoidHom.ofInjective hinj).symm.trans e)
  have hC : Subgroup.centralizer (S : Set ↥H) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro h hh
    rw [Subgroup.mem_centralizer_iff] at hh
    apply Subtype.ext
    ext g
    have hs : (⟨MulAut.conj g, hH ⟨g, rfl⟩⟩ : ↥H) ∈ S := ⟨g, rfl⟩
    have hcomm := hh _ hs
    have h1 : ∀ x : Jt, g * (h : MulAut Jt) x * g⁻¹ = (h : MulAut Jt) g * (h : MulAut Jt) x * ((h : MulAut Jt) g)⁻¹ := by
      intro x
      have := congrArg (fun f : ↥H => (f : MulAut Jt) x) hcomm
      simp only [Subgroup.coe_mul, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] at this
      exact this
    have hz : ((h : MulAut Jt) g)⁻¹ * g = 1 := by
      apply hZ
      intro y
      obtain ⟨x, rfl⟩ := (h : MulAut Jt).surjective y
      have := h1 x
      calc (h : MulAut Jt) x * (((h : MulAut Jt) g)⁻¹ * g) = ((h : MulAut Jt) g)⁻¹ * (((h : MulAut Jt) g * (h : MulAut Jt) x * ((h : MulAut Jt) g)⁻¹) * g) := by group
        _ = ((h : MulAut Jt) g)⁻¹ * ((g * (h : MulAut Jt) x * g⁻¹) * g) := by rw [this]
        _ = (((h : MulAut Jt) g)⁻¹ * g) * (h : MulAut Jt) x := by group
    have hg : (h : MulAut Jt) g = g := by
      have := hz
      rw [inv_mul_eq_one] at this
      exact this
    simpa using hg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hb2) hb1
  have h0 := CFSG.Sporadic.Schreier.ctuc_mathieu_almost_simple_involution_centralizer_odd_core_trivial
    (X := ↥H) S (Or.inr (Or.inl ⟨eS⟩)) hC b hbo
  unfold involutionOddCore
  have h0' : CFSG.Assembly.oddCore ↥(Subgroup.centralizer ({b} : Set ↥H)) = ⊥ := h0
  rw [h0', Subgroup.map_bot]

theorem deltaCore_eq_bot_of_M12 {Jt : Type} [Group Jt] (hJ : NativeSporadic.IsSporadic Jt .M12)
    {H : Subgroup (MulAut Jt)} (hH : (MulAut.conj : Jt →* MulAut Jt).range ≤ H) {D : Subgroup ↥H}
    (hcard : Nat.card ↥D = 4) (hsq : ∀ d ∈ D, d * d = 1) : deltaCore D = ⊥ := by
  have hne : D ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hcard
    omega
  obtain ⟨⟨d, hd⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  rw [eq_bot_iff]
  exact (deltaCore_le_involutionOddCore hd hd1').trans
    (involutionOddCore_eq_bot_of_M12 hJ hH (hsq d hd) hd1').le

theorem locBal32_M12 {Jt : Type} [Group Jt] (hJ : NativeSporadic.IsSporadic Jt .M12) :
    LocBal32All Jt := by
  intro B hB H hH hBH
  refine ⟨fun b hb hb1 c hc b' _ => ?_, fun D _ hcard hsq => ?_⟩
  · have hb2 : b * b = 1 := Subtype.ext (by simpa using hB _ (Subgroup.mem_subgroupOf.mp hb))
    rw [involutionOddCore_eq_bot_of_M12 hJ hH hb2 hb1, Subgroup.mem_bot] at hc
    rw [hc]
    simp
  · exact deltaCore_eq_bot_of_M12 hJ hH hcard hsq

end Main

end CFSG.GH74.Generic.BProg.B3
