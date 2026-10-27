module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveSym
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveZSplit
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveSection
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveTriple
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5OuterTv
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5SecRed

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.RankThree.Native

theorem five_centralizer_of_equiv_R
    {X : Type*} [Group X] (θ : X ≃* ↥hs100R) {x : X}
    (hx : orderOf x = 5) (h3 : 3 ∣ Nat.card ↥(centralizer ({x} : Set X))) :
    Nonempty (↥(centralizer ({x} : Set X)) ≃* Multiplicative (ZMod 5) × Equiv.Perm (Fin 5)) := by
  have hx' : orderOf (θ x) = 5 := by rw [MulEquiv.orderOf_eq]; exact hx
  have h3' : 3 ∣ Nat.card ↥(centralizer ({θ x} : Set ↥hs100R)) := by
    rwa [← Nat.card_congr (centralizerSingletonEquiv θ x).toEquiv]
  obtain ⟨e⟩ := hs100R_five_centralizer hx' h3'
  exact ⟨(centralizerSingletonEquiv θ x).trans e⟩

theorem five_centralizer_of_outcome
    (M : HS100Model) {X : Type} [Group X]
    (hX : HSOuterOutcomeFive X) {x : X} (hx : orderOf x = 5)
    (h3 : 3 ∣ Nat.card ↥(centralizer ({x} : Set X))) :
    Nonempty (↥(centralizer ({x} : Set X)) ≃* Multiplicative (ZMod 5) × Equiv.Perm (Fin 5)) := by
  rcases hX with ⟨⟨θ⟩⟩ | ⟨⟨θ⟩⟩
  · have hx' : orderOf (θ x) = 5 := by rw [MulEquiv.orderOf_eq]; exact hx
    have h3' : 3 ∣ Nat.card ↥(centralizer ({θ x} : Set (Equiv.Perm (Fin 10)))) := by
      rwa [← Nat.card_congr (centralizerSingletonEquiv θ x).toEquiv]
    obtain ⟨e⟩ := exists_mulEquiv_centralizer_perm_ten hx' h3'
    exact ⟨(centralizerSingletonEquiv θ x).trans e⟩
  · obtain ⟨κ⟩ := mulAut_hs_equiv_R M
    exact five_centralizer_of_equiv_R (θ.trans κ) hx h3

theorem orderOf_eq_two_of_sq {M : Type*} [Group M] {g : M} (h : g * g = 1) (h1 : g ≠ 1) :
    orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact h) h1

theorem mem_zpowers_subtype_iff {M : Type*} [Group M] {T : Subgroup M} (q z : ↥T) :
    q ∈ zpowers z ↔ (q : M) ∈ zpowers (z : M) := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem not_mem_zpowers_of_sq {M : Type*} [Group M] {g a : M} (hg : g * g = 1) (h1 : a ≠ 1)
    (h2 : a ≠ g) : a ∉ zpowers g := by
  rintro ⟨k, hk⟩
  rcases zpow_eq_one_or_self hg k with h | h
  · exact h1 (hk.symm.trans h)
  · exact h2 (hk.symm.trans h)

section Side

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {S : Subgroup G}
  {z n v s : G}

theorem centralizer_five_of_section
    (M : HS100Model)
    (h : HSOuterSetup G L t S z n v s) {r u₁ u₂ : G} (tr : FiveTriple L v r u₁ u₂)
    (hX : HSOuterOutcomeFive (OuterSection v)) :
    Nonempty (↥(centralizer ({v} : Set G) ⊓ centralizer ({r} : Set G)) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 5) × Equiv.Perm (Fin 5)) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hv2 : v * v = 1 := h.ctx.v_sq
  have hv1 : v ≠ 1 := h.v_ne_one
  have hvo : orderOf v = 2 := orderOf_eq_two_of_sq hv2 hv1
  have hzr : r ∈ centralizer ({v} : Set G) := mem_centralizer_singleton_iff.2 tr.r_comm
  have hwc : u₁ * u₂ ∈ centralizer ({v} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc u₁ * u₂ * v = u₁ * (u₂ * v) := by rw [mul_assoc]
      _ = u₁ * (v * u₂) := by rw [tr.u₂_comm]
      _ = (u₁ * v) * u₂ := by rw [mul_assoc]
      _ = (v * u₁) * u₂ := by rw [tr.u₁_comm]
      _ = v * (u₁ * u₂) := by rw [mul_assoc]
  have hword : orderOf (u₁ * u₂) = 3 := orderOf_eq_prime tr.u_cube tr.u_ne
  have hrbar : orderOf (rBar hzr) = 5 := orderOf_sectionMk hv2 (by norm_num) hzr tr.r_ord
  have hwbar := orderOf_sectionMk hv2 (p := 3) (by norm_num) hwc hword
  have hwr : (QuotientGroup.mk (⟨u₁ * u₂, hwc⟩ : ↥(centralizer ({v} : Set G))) :
      OuterSection v) ∈ centralizer ({rBar hzr} : Set (OuterSection v)) := by
    rw [mem_centralizer_singleton_iff]
    change (QuotientGroup.mk _ : OuterSection v) * QuotientGroup.mk (rElem hzr) =
      QuotientGroup.mk (rElem hzr) * QuotientGroup.mk _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    show u₁ * u₂ * r = r * (u₁ * u₂)
    rw [mul_assoc, tr.u₂_r, ← mul_assoc, tr.u₁_r, mul_assoc]
  have h3 : 3 ∣ Nat.card ↥(centralizer ({rBar hzr} : Set (OuterSection v))) := by
    have := orderOf_dvd_natCard (⟨_, hwr⟩ : ↥(centralizer ({rBar hzr} : Set (OuterSection v))))
    rwa [Subgroup.orderOf_mk, hwbar] at this
  obtain ⟨e⟩ := five_centralizer_of_outcome M hX hrbar h3
  obtain ⟨ψ, hψs, hψk⟩ := exists_psi_of_section hv2 hv1 hzr tr.r_ord e
  have htcomm : ∀ x ∈ L, x * t = t * x := fun x hx => mem_centralizer_iff.1 h.t_mem x hx
  have hQmem : ∀ g : G, g * v = v * g → g * r = r * g →
      g ∈ centralizer ({v} : Set G) ⊓ centralizer ({r} : Set G) := fun g h1 h2 =>
    mem_inf.2 ⟨mem_centralizer_singleton_iff.2 h1, mem_centralizer_singleton_iff.2 h2⟩
  have hvQ := hQmem v rfl tr.r_comm.symm
  have hrQ := hQmem r tr.r_comm rfl
  have htQ := hQmem t h.t_comm_v (htcomm r tr.r_mem).symm
  have hu₁Q := hQmem u₁ tr.u₁_comm tr.u₁_r
  have hu₂Q := hQmem u₂ tr.u₂_comm tr.u₂_r
  have hvL : v ∉ L := fun hvL => h.ctx.v_outer (Subgroup.mem_sup_left hvL)
  refine exists_mulEquiv_of_central_five (z := ⟨v, hvQ⟩) (r := ⟨r, hrQ⟩) ?_ ?_ ?_ ?_ ψ hψs
    (fun q => (hψk q).trans (mem_zpowers_subtype_iff q ⟨v, hvQ⟩).symm)
    (x := ⟨t, htQ⟩) (y₁ := ⟨u₁, hu₁Q⟩) (y₂ := ⟨u₂, hu₂Q⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 g.2).1)
  · exact (Subgroup.orderOf_mk v hvQ).trans hvo
  · rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 g.2).2)
  · exact (Subgroup.orderOf_mk r hrQ).trans tr.r_ord
  · exact Subtype.ext h.t_sq
  · rw [mem_zpowers_subtype_iff]
    exact not_mem_zpowers_of_sq hv2 h.t_ne_one h.t_ne_v
  · exact Subtype.ext tr.u₁_sq
  · exact Subtype.ext tr.u₂_sq
  · exact Subtype.ext (by simpa using tr.u_cube)
  · rw [mem_zpowers_subtype_iff]
    refine not_mem_zpowers_of_sq hv2 tr.u_ne ?_
    intro hh
    have hh' : u₁ * u₂ = v := hh
    exact hvL (hh' ▸ L.mul_mem tr.u₁_mem tr.u₂_mem)
  · exact Subtype.ext (htcomm u₁ tr.u₁_mem).symm
  · exact Subtype.ext (htcomm u₂ tr.u₂_mem).symm

end Side

end CFSG.EvenSporadicStandard.HSStd

