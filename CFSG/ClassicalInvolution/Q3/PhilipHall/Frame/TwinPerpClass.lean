module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm7RCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExact
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmAInner
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPair

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

section Datum

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem commOdd_core (h : QuaternionBridge.Q8TwinDatum R S t) {u a b : Y} (hu : u ∈ tightCore R)
    (hu2 : IsPGroup 2 (Subgroup.zpowers u)) (huu : u * u ≠ 1) (ha : a ∈ tightCore R)
    (hb : b ∈ tightCore R) (hau : a * u = u * a) (hbu : b * u = u * b) :
    a * b * a⁻¹ * b⁻¹ ∈ oddCoreOf (tightCore R) := by
  classical
  obtain ⟨r, hr, ⟨eS⟩⟩ := h.quat
  have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  set S' : Subgroup Y := (S : Subgroup R).map R.subtype with hS'
  have hS'R : S' ≤ R := Subgroup.map_subtype_le _
  have hsyl : IsSylow2In S' R := isSylow2In_map_subtype R S
  let eS' : ↥S' ≃* QuaternionGroup (2 ^ (r - 2)) :=
    (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans eS
  set ι : ↥S' →* R ⧸ oddCore R :=
    (QuotientGroup.mk' (oddCore R)).comp (Subgroup.inclusion hS'R) with hιdef
  have hι : Function.Bijective ι := by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have h1 : (Subgroup.inclusion hS'R x : R) ∈ oddCore R := (QuotientGroup.eq_one_iff _).mp hx
      have h2 : (x : Y) ∈ oddCoreOf R ⊓ S' := ⟨⟨_, h1, rfl⟩, x.2⟩
      rw [TwinExact.inf_oddCoreOf_eq_bot hsyl.2.1, Subgroup.mem_bot] at h2
      exact Subgroup.mem_bot.mpr (Subtype.ext h2)
    · intro q
      obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨s, hs, o, ho, hxe⟩ := TwinExact.mem_mul_oddCore_of_sylow h.twoGroup hsyl x hx
      refine ⟨⟨s, hs⟩, ?_⟩
      show (QuotientGroup.mk (⟨s, hS'R hs⟩ : R) : R ⧸ oddCore R) = QuotientGroup.mk ⟨x, hx⟩
      rw [QuotientGroup.eq]
      obtain ⟨o', ho', rfl⟩ := ho
      have : ((⟨s, hS'R hs⟩ : R)⁻¹ * ⟨x, hx⟩ : R) = o' := by
        apply Subtype.ext
        simp [hxe]
      rw [this]
      exact ho'
  let eQ : (R ⧸ oddCore R) ≃* QuaternionGroup (2 ^ (r - 2)) :=
    (MulEquiv.ofBijective ι hι).symm.trans eS'
  let φ : R →* QuaternionGroup (2 ^ (r - 2)) :=
    eQ.toMonoidHom.comp (QuotientGroup.mk' (oddCore R))
  have hφ1 : ∀ x : R, φ x = 1 → (x : Y) ∈ oddCoreImg R := by
    intro x hx
    have h1 : eQ (QuotientGroup.mk' (oddCore R) x) = 1 := hx
    rw [MulEquiv.map_eq_one_iff] at h1
    exact ⟨x, (QuotientGroup.eq_one_iff x).mp h1, rfl⟩
  have huR : u ∈ R := tightCore_le R hu
  have haR : a ∈ R := tightCore_le R ha
  have hbR : b ∈ R := tightCore_le R hb
  have huu' : φ ⟨u, huR⟩ * φ ⟨u, huR⟩ ≠ 1 := by
    intro h1
    rw [← map_mul] at h1
    have h3 := hφ1 _ h1
    apply huu
    have h2 : IsPGroup 2 (Subgroup.zpowers (u * u)) :=
      hu2.to_le (Subgroup.zpowers_le.mpr (Subgroup.mul_mem _ (Subgroup.mem_zpowers u)
        (Subgroup.mem_zpowers u)))
    exact eq_one_of_isPGroup_of_mem_odd (odd_natCard_oddCoreImg R) h3 h2
  have hau' : φ ⟨a, haR⟩ * φ ⟨u, huR⟩ = φ ⟨u, huR⟩ * φ ⟨a, haR⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext hau)
  have hbu' : φ ⟨b, hbR⟩ * φ ⟨u, huR⟩ = φ ⟨u, huR⟩ * φ ⟨b, hbR⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext hbu)
  have hc := quaternionGroup_comm_of_comm huu' hau' hbu'
  have hc' : φ (⟨a, haR⟩ * ⟨b, hbR⟩ * (⟨a, haR⟩ : R)⁻¹ * (⟨b, hbR⟩ : R)⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hc]
    group
  have hcomm : a * b * a⁻¹ * b⁻¹ ∈ oddCoreImg R := by
    simpa using hφ1 _ hc'
  have hK : a * b * a⁻¹ * b⁻¹ ∈ tightCore R :=
    (tightCore R).mul_mem ((tightCore R).mul_mem ((tightCore R).mul_mem ha hb)
      ((tightCore R).inv_mem ha)) ((tightCore R).inv_mem hb)
  have hN : tightCore R ⊓ oddCoreImg R ≤ oddCoreOf (tightCore R) :=
    AscFusion.le_oddCoreOf_of_normal_odd inf_le_left core_le_normalizer_inf
      (Odd.of_dvd_nat (odd_natCard_oddCoreImg R) (Subgroup.card_dvd_of_le inf_le_right))
  exact hN ⟨hK, hcomm⟩

end Datum

section Core


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem classicalClause (h : TwinCoreHyp n Y R S t) :
    Q3CL.ClassicalClause (CoreAssembly.conjClass (tightCore R)) where
  subnormal := by
    rintro K ⟨g, rfl⟩
    have hz := (Inner.isUniqueInvolution_core h.datum).conj g
    refine ⟨g * t * g⁻¹, hz.mem, ?_, isSubnormal_of_hypOmegaGen h.hyp ⟨g, rfl⟩ hz⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  commOdd := by
    rintro J ⟨g, rfl⟩ u a b hu hu2 huu ha hb hau hbu
    simp only at hu ha hb ⊢
    rw [AscFusion.oddCoreOf_conjSub' g (tightCore R), mem_conjSub_iff]
    have hu' : g⁻¹ * u * g ∈ tightCore R := mem_conjSub_iff.mp hu
    have ha' : g⁻¹ * a * g ∈ tightCore R := mem_conjSub_iff.mp ha
    have hb' : g⁻¹ * b * g ∈ tightCore R := mem_conjSub_iff.mp hb
    have hu2' : IsPGroup 2 (Subgroup.zpowers (g⁻¹ * u * g)) := by
      have e : g⁻¹ * u * g = (MulAut.conj g⁻¹).toMonoidHom u := by simp
      rw [e, ← MonoidHom.map_zpowers]
      exact hu2.map _
    have huu' : (g⁻¹ * u * g) * (g⁻¹ * u * g) ≠ 1 := by
      intro h1
      apply huu
      have : u * u = g * ((g⁻¹ * u * g) * (g⁻¹ * u * g)) * g⁻¹ := by group
      rw [this, h1]; group
    have hau' : (g⁻¹ * a * g) * (g⁻¹ * u * g) = (g⁻¹ * u * g) * (g⁻¹ * a * g) := by
      calc (g⁻¹ * a * g) * (g⁻¹ * u * g) = g⁻¹ * (a * u) * g := by group
        _ = g⁻¹ * (u * a) * g := by rw [hau]
        _ = (g⁻¹ * u * g) * (g⁻¹ * a * g) := by group
    have hbu' : (g⁻¹ * b * g) * (g⁻¹ * u * g) = (g⁻¹ * u * g) * (g⁻¹ * b * g) := by
      calc (g⁻¹ * b * g) * (g⁻¹ * u * g) = g⁻¹ * (b * u) * g := by group
        _ = g⁻¹ * (u * b) * g := by rw [hbu]
        _ = (g⁻¹ * u * g) * (g⁻¹ * b * g) := by group
    have key := commOdd_core h.datum hu' hu2' huu' ha' hb' hau' hbu'
    have e : g⁻¹ * (a * b * a⁻¹ * b⁻¹) * g =
        (g⁻¹ * a * g) * (g⁻¹ * b * g) * (g⁻¹ * a * g)⁻¹ * (g⁻¹ * b * g)⁻¹ := by group
    rw [e]
    exact key

theorem aEmpty_all (h : TwinCoreHyp n Y R S t) :
    ∀ J ∈ CoreAssembly.conjClass (tightCore R), AEmpty (CoreAssembly.conjClass (tightCore R)) J := by
  rintro J ⟨g, rfl⟩
  exact aEmpty_conj h.hyp.conjInvariant h.aEmpty g

theorem partIHypG (h : TwinCoreHyp n Y R S t) :
    Q3CL.PartIHypG (CoreAssembly.conjClass (tightCore R)) :=
  ⟨h.hyp, classicalClause h, aEmpty_all h⟩

end Core

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
