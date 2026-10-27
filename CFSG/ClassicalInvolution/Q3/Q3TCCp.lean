module

public import CFSG.ClassicalInvolution.RouteD.TwinSL4BridgeBase
public import CFSG.ClassicalInvolution.Q3.Generation
public import CFSG.ClassicalInvolution.Q3.Q3TCCtx
public import CFSG.ClassicalInvolution.Q3.Q3WAComp

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TC

open scoped MatrixGroups
open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Generic.CoreAssembly
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

theorem conjClass3_eq_of_mem {G : Type} [Group G] {K β : Subgroup G} (hβ : β ∈ conjClass3 K) :
    conjClass3 β = conjClass3 K := RouteD.conjClass_eq_of_mem hβ


theorem RouteD3Setup.of_mem_conjClass3 {G : Type} [Group G] [Finite G] {K β : Subgroup G}
    {z t : G} (S : RouteD3Setup K z) (hβ : β ∈ conjClass3 K) (ht : IsClassicalMember3 β t) :
    RouteD3Setup β t := by
  have hcl : conjClass3 β = conjClass3 K := conjClass3_eq_of_mem hβ
  obtain ⟨g, hg⟩ := id hβ
  have htg : t = g * z * g⁻¹ := involution_unique3 ht (hg ▸ S.cls.conj g)
  exact
  { cls := ht
    inClass := by rw [hcl]; exact S.inClass
    conn := by
      refine (deltaConnected_iff β).mpr ?_
      have h1 : RouteD.DeltaConnected (CoreAssembly.conjClass K) :=
        (deltaConnected_iff K).mp S.conn
      have h2 : CoreAssembly.conjClass β = CoreAssembly.conjClass K :=
        RouteD.conjClass_eq_of_mem hβ
      rw [h2]
      exact h1
    setup := by
      refine ⟨by rw [hcl]; exact S.setup.1, ?_⟩
      rw [hcl, htg]
      exact Gaps.localOddCentral_conj S.inClass.conjInvariant g z S.setup.2
    ih := by rw [hcl]; exact S.ih
    below := S.below
    rank := S.rank
    large := S.large
    intr := by
      have h1 : Balance.oddCoreIn (Subgroup.centralizer ({t} : Set G)) =
          (Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G))).map
            (MulAut.conj g).toMonoidHom := by
        rw [htg, ← map_conj_centralizer_singleton g z]
        exact Balance.Bootstrap.oddCoreIn_conjSub_eq g (Subgroup.centralizer ({z} : Set G))
      rw [h1, ← hg]
      exact Subgroup.map_mono S.intr }

theorem TCtx3.exists_ctx_member {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
    {tY : StatedLieTag} {nY : ℕ} {K : Subgroup G} (c : TCtx3 tY nY Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {β : Subgroup G} (hβ : β ∈ Ω) {t : G}
    (ht : IsClassicalMember3 β t) : Nonempty (TCtx3 tY nY Ω β t) := by
  obtain ⟨g, hg⟩ := hsingle β hβ
  have htg : t = g * z * g⁻¹ := involution_unique3 ht (hg ▸ c.hz.conj g)
  subst htg
  obtain ⟨d', hQ⟩ := exists_dictT2_of_member3 c.hY hβ ht
    (ShapeDictT2.conj3 c.hΩ.conjInvariant g c.d)
  exact ⟨{
    hΩ := c.hΩ
    hex := c.hex
    hK := hβ
    hz := ht
    hP1 := Gaps.localOddCentral_conj c.hΩ.conjInvariant g z c.hP1
    hO3 := localOddThreeFree3_conj c.hΩ.conjInvariant g z c.hO3
    d := d'
    hQ₀ := hQ
    hY := c.hY }⟩

section CP


theorem cp_at_member3 (h3 : OddThreeFreeInput) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G} (hR : RouteD3Setup K z)
    {N : Subgroup G} (hN : N ∈ conjClass3 K) {y : G} (hy : IsClassicalMember3 N y)
    {L : Subgroup G} (hL : L ∈ centralizingMembers (conjClass3 K) {y}) :
    Commutes N L ∨ L = N := by
  obtain ⟨g, hg⟩ := id hN
  have hyg : y = g * z * g⁻¹ := involution_unique3 hy (hg ▸ hR.cls.conj g)
  have hP1y : LocalOddCentral (conjClass3 K) {y} := by
    rw [hyg]
    exact Gaps.localOddCentral_conj hR.inClass.conjInvariant g z hR.setup.2
  have hO3y : LocalOddThreeFree3 (conjClass3 K) y := by
    rw [hyg]
    exact localOddThreeFree3_conj hR.inClass.conjInvariant g z (h3 G K z hR)
  have hync : ¬ ({y} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    have hyc' : y ∈ Subgroup.center G := hsub rfl
    rw [center_eq_bot hnab, Subgroup.mem_bot] at hyc'
    have h2 := hy.orderOf_eq_two
    rw [hyc', orderOf_one] at h2
    omega
  obtain ⟨ι, hι, ⟨D⟩⟩ := hR.ih {y} hync
  have hNy : N ∈ centralizingMembers (conjClass3 K) {y} := ⟨hN, isSubnormal_le hy.subnormal⟩
  exact commutes_or_eq_of_involution3 (Gaps.fundNoncentral 3) hR.inClass hR.setup.1 hP1y hO3y D
    hNy hL hy

end CP

end CFSG.ClassicalInvolution.Q3.Q3TC
