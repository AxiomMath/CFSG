module

public import CFSG.ClassicalInvolution.RouteD.GapsOrthTransfer
public import CFSG.ClassicalInvolution.RouteD.GapsOrthModel
public import CFSG.ClassicalInvolution.RouteD.TwinSmallModel

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinSmall

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.Assembly.LowTwoRank

section Local

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem centralizes_iff_locElt (hΩ : InClass p f Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    {u : G} (hu : u ∈ locLayer Ω x) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    {S : Subgroup (locQuot Ω x)} (hLS : locImg Ω x L = S) :
    L ≤ Subgroup.centralizer ({u} : Set G) ↔ ∀ s ∈ S, Commute (locElt Ω x u hu) s := by
  constructor
  · intro h s hs
    rw [← hLS] at hs
    obtain ⟨b, hb, rfl⟩ := hs
    have hbL : (b : G) ∈ L := Subgroup.mem_subgroupOf.mp hb
    have hc : u * (b : G) = (b : G) * u :=
      (Subgroup.mem_centralizer_singleton_iff.mp (h hbL)).symm
    show locMk Ω x ⟨u, hu⟩ * locMk Ω x b = locMk Ω x b * locMk Ω x ⟨u, hu⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hc
  · intro h
    obtain ⟨z₀, hz₀⟩ := hΩ.classical L hL.1
    have hperf := (hz₀.subgroupOf p f (le_centralizingLayer hL)).perfect
    have hperf' : ⁅L.subgroupOf (locLayer Ω x), L.subgroupOf (locLayer Ω x)⁆ =
        L.subgroupOf (locLayer Ω x) := Subgroup.isPerfect_iff.mp hperf
    have key := commute_of_perfect_of_map_commute (locMk Ω x)
      (by rw [QuotientGroup.ker_mk']; exact hP1) hperf' (a := ⟨u, hu⟩) (fun r hr => by
        refine h _ ?_
        rw [← hLS]
        exact ⟨r, hr, rfl⟩)
    intro n hn
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := key ⟨n, le_centralizingLayer hL hn⟩ (Subgroup.mem_subgroupOf.mpr hn)
    exact (congrArg Subtype.val this.eq).symm

theorem commute_w_of_model {tY : StatedLieTag} {nY : ℕ} {N : Subgroup G} {x : G}
    (cx : TCtx p f tY nY Ω N x) {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (hL' : L' ∈ centralizingMembers Ω {x}) {R R' : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) (hLR' : locImg Ω x L' = R'.map cx.d.ψ) {w w' : G}
    (hw : IsClassicalMember p f L w) (hw' : IsClassicalMember p f L' w')
    (hc : ∀ r r', InvOf R r → InvOf R' r' → r * r' = r' * r) : Commute w w' := by
  obtain ⟨r, hr, hψr⟩ := exists_involution_of_fund cx hL hR hLR hw
  obtain ⟨r', hr', hψr'⟩ := exists_involution_of_fund cx hL' hR' hLR' hw'
  have hwx : w ∈ locLayer Ω x := le_centralizingLayer hL hw.mem
  have hwx' : w' ∈ locLayer Ω x := le_centralizingLayer hL' hw'.mem
  have hcomm : locElt Ω x w hwx * locElt Ω x w' hwx' = locElt Ω x w' hwx' * locElt Ω x w hwx := by
    rw [← hψr, ← hψr', ← map_mul, ← map_mul, hc r r' hr hr']
  have hw2 : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw.orderOf_eq_two, pow_two] at this
  have hw2' : w' * w' = 1 := by
    have := pow_orderOf_eq_one w'
    rwa [hw'.orderOf_eq_two, pow_two] at this
  have := commute_of_involutions_of_mk (Y := ↥(locLayer Ω x)) cx.hP1
    (a := ⟨w, hwx⟩) (b := ⟨w', hwx'⟩) (Subtype.ext hw2) (Subtype.ext hw2') hcomm
  exact congrArg Subtype.val this.eq

end Local

section Spin

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  {Q : QuadraticForm F V} {KY : Type} [Group KY] {𝓕 : Set (Subgroup KY)}
  {Z' : Subgroup (V ≃ₗ[F] V)} {π : KY →* (V ≃ₗ[F] V)}

theorem map_invOf_eq (hodd : Odd (Nat.card F)) (cq : CentralQuot π 𝓕 (fundSet Q) Z')
    {R : Subgroup KY} (hR : R ∈ 𝓕) {i : V ≃ₗ[F] V} (hi : IsFundamental Q (R.map π) i) {r : KY}
    (hr : InvOf R r) : π r = i := by
  obtain ⟨hrR, hr2⟩ := hr
  refine hi.eq_of_orderOf_eq_two hodd ⟨r, hrR, rfl⟩ ?_
  have h1 : orderOf (π r) ∣ 2 := by
    rw [← hr2]
    exact orderOf_map_dvd π r
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exfalso
    have h3 : π r = 1 := orderOf_eq_one_iff.mp h
    have := cq.inj R hR r hrR h3
    rw [this, orderOf_one] at hr2
    exact absurd hr2 (by simp)
  · exact h

theorem invs_commute_of_normalizes (hodd : Odd (Nat.card F))
    (cq : CentralQuot π 𝓕 (fundSet Q) Z') {R R' : Subgroup KY} (hR : R ∈ 𝓕) (hR' : R' ∈ 𝓕)
    {i i' : V ≃ₗ[F] V} (hi : IsFundamental Q (R.map π) i) (hi' : IsFundamental Q (R'.map π) i')
    (hN : i' ∈ Subgroup.normalizer ((R.map π : Subgroup (V ≃ₗ[F] V)) : Set (V ≃ₗ[F] V))) :
    ∀ r r', InvOf R r → InvOf R' r' → r * r' = r' * r := by
  intro r r' hr hr'
  have hπr : π r = i := map_invOf_eq hodd cq hR hi hr
  have hπr' : π r' = i' := map_invOf_eq hodd cq hR' hi' hr'
  obtain ⟨hrR, hr2⟩ := hr
  have hrr : r * r = 1 := by
    have := pow_orderOf_eq_one r
    rwa [hr2, pow_two] at this
  have hnorm : ∀ y ∈ R, r' * y * r'⁻¹ ∈ R := by
    refine conj_mem_of_perfect (cq.perf R hR).ge r' fun x hx => ?_
    have hmem : π (r' * x * r'⁻¹) ∈ R.map π := by
      rw [map_mul, map_mul, map_inv, hπr']
      exact (Subgroup.mem_normalizer_iff.mp hN (π x)).mp ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hye⟩ := hmem
    refine ⟨y, hy, y⁻¹ * (r' * x * r'⁻¹), cq.ker_le ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hye, inv_mul_cancel]
  have h1 : r' * r * r'⁻¹ ∈ R := hnorm r hrR
  have hsq : (r' * r * r'⁻¹) * (r' * r * r'⁻¹) = 1 := by
    calc (r' * r * r'⁻¹) * (r' * r * r'⁻¹) = r' * (r * r) * r'⁻¹ := by group
      _ = 1 := by rw [hrr]; group
  have hne : r' * r * r'⁻¹ ≠ 1 := by
    intro h
    have : r = 1 := by
      have h' : r = r'⁻¹ * (r' * r * r'⁻¹) * r' := by group
      rw [h', h]
      group
    rw [this, orderOf_one] at hr2
    exact absurd hr2 (by simp)
  have hord : orderOf (r' * r * r'⁻¹) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hsq) hne
  have h2 : π (r' * r * r'⁻¹) = π r := by
    rw [hπr]
    exact hi.eq_of_orderOf_eq_two hodd ⟨_, h1, rfl⟩ (by
      have h4 : orderOf (π (r' * r * r'⁻¹)) ∣ 2 := by
        rw [← hord]
        exact orderOf_map_dvd π _
      rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h | h
      · exfalso
        have h3 : π (r' * r * r'⁻¹) = 1 := orderOf_eq_one_iff.mp h
        have := cq.inj R hR _ h1 h3
        exact hne this
      · exact h)
  have h3 : r' * r * r'⁻¹ = r := by
    have := cq.inj R hR ((r' * r * r'⁻¹) * r⁻¹) (R.mul_mem h1 (R.inv_mem hrR)) (by
      rw [map_mul, map_inv, h2, mul_inv_cancel])
    exact mul_inv_eq_one.mp this
  calc r * r' = (r' * r * r'⁻¹) * r' := by rw [h3]
    _ = r' * r := by group

end Spin

end CFSG.ClassicalInvolution.RouteD.TwinSmall
