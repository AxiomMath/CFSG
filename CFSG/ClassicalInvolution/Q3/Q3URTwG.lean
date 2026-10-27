module

public import CFSG.ClassicalInvolution.Q3.Q3URTwF
public import CFSG.ClassicalInvolution.Q3.Q3URTwB
public import CFSG.ClassicalInvolution.Q3.Q3WARow

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.BorelTits
open scoped MatrixGroups

section Iterate

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem locAut_iterate_eq_self (hΩ : ConjInvariant Ω) {t z : G} (ht : t * z * t⁻¹ = z) {n : ℕ}
    (htn : t ^ n = 1) (a : locQuot Ω z) : (locAut hΩ ht)^[n] a = a := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
  have key : ∀ m : ℕ, ∃ y' : ↥(locLayer Ω z), (y' : G) = t ^ m * (y : G) * (t ^ m)⁻¹ ∧
      (locAut hΩ ht)^[m] (QuotientGroup.mk y : locQuot Ω z) = QuotientGroup.mk y' := by
    intro m
    induction m with
    | zero => exact ⟨y, by simp, rfl⟩
    | succ m ih =>
      obtain ⟨y', hy', hm⟩ := ih
      refine ⟨layerAut hΩ ht y', ?_, ?_⟩
      · rw [coe_layerAut, hy', pow_succ' t m]
        group
      · rw [Function.iterate_succ_apply', hm]
        rfl
  obtain ⟨y', hy', hm⟩ := key n
  have : y' = y := by
    apply Subtype.ext
    rw [hy', htn]
    simp
  rw [hm, this]

end Iterate

section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem UCtx3.fixed_layer_of_pow {J : Subgroup G} {w : G} (c : UCtx3 2 Ω J w) {K : Subgroup G}
    {z : G} (hK : K ∈ centralizingMembers Ω {w}) (hKJ : K ≠ J) (hz : IsClassicalMember3 K z)
    {t : G} (ht1 : t * w * t⁻¹ = w) {n : ℕ} (hn : Nat.Coprime n 16) (htn : t ^ n = 1)
    (htK : K ≤ Subgroup.centralizer ({t} : Set G)) :
    ∀ N ∈ centralizingMembers Ω {w}, N ≠ J → N ≤ Subgroup.centralizer ({t} : Set G) := by
  classical
  obtain ⟨R, i, hRi, hKR, -⟩ := c.exists_rootData hK hKJ hz
  obtain ⟨g, hRg, -⟩ := hRi
  obtain ⟨θ, hθ⟩ : ∃ θ : Su (GaloisField 3 2) 3 1 (2 + 1) →* locQuot Ω w,
      θ = c.d.ψ.comp (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
  have hθx : ∀ x, θ x = c.d.ψ (g * x * g⁻¹) := fun x => by rw [hθ]; rfl
  have hθker : θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 (2 + 1)) := by
    rw [hθ]
    exact ker_comp_conj_le_center c.d.ψ c.d.ker_le g
  have hθrange : θ.range = c.d.ψ.range := by
    rw [hθ]
    exact range_comp_conj c.d.ψ g
  have hψθ : ∀ r, c.d.ψ r ∈ θ.range := fun r => by
    rw [hθrange]
    exact ⟨r, rfl⟩
  set σ := locAut c.hΩ.conjInvariant ht1 with hσdef
  obtain ⟨nd⟩ := c.nonempty_nodes
  have hstabψ : ∀ x, σ (c.d.ψ x) ∈ c.d.ψ.range := c.locAut_stab nd ht1
  have hstab : ∀ x, σ (θ x) ∈ θ.range := fun x => by
    rw [hθrange, hθx]
    exact hstabψ _
  have hfix : ∀ A : Su (GaloisField 3 2) 3 1 2,
      σ (θ (blockEmb2 (GaloisField 3 2) 3 1 2 0 A)) =
        θ (blockEmb2 (GaloisField 3 2) 3 1 2 0 A) := by
    intro A
    have hmem : θ (blockEmb2 (GaloisField 3 2) 3 1 2 0 A) ∈ locImg Ω w K := by
      rw [hKR, hθx]
      refine ⟨g * blockEmb2 (GaloisField 3 2) 3 1 2 0 A * g⁻¹, ?_, rfl⟩
      rw [hRg]
      exact ⟨blockEmb2 (GaloisField 3 2) 3 1 2 0 A, ⟨A, rfl⟩, rfl⟩
    exact ((locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 ht1 hK).mp htK) _ hmem
  have hσn : ∀ x, σ^[n] (θ x) = θ x := fun x =>
    locAut_iterate_eq_self c.hΩ.conjInvariant ht1 htn _
  have hall := fixed_of_iterate_su3 θ hθker σ hn hσn hstab hfix
  have hlocal : ∀ N ∈ centralizingMembers Ω {w}, N ≠ J → ∀ a ∈ locImg Ω w N,
      ∃ x, a = θ x := by
    intro N hN hNJ a ha
    obtain ⟨zN, hzN⟩ := c.hΩ.classical N hN.1
    obtain ⟨R', i', -, hR', -⟩ := c.exists_rootData hN hNJ hzN
    rw [hR'] at ha
    obtain ⟨r, -, rfl⟩ := ha
    obtain ⟨x, hx⟩ := hψθ r
    exact ⟨x, hx.symm⟩
  intro N hN hNJ
  refine (locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 ht1 hN).mpr fun a ha => ?_
  obtain ⟨x, rfl⟩ := hlocal N hN hNJ a ha
  exact hall x

end Layer

section Centralizer


theorem centralizer_pow_eq_one (h3 : OddThreeFreeInput) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {K : Subgroup G} {z : G}
    (hR : RouteD3Setup K z)
    (hshape : LocalShapeC3 1 (CompData.model .PSU (2 + 1)) (conjClass3 K) z)
    {A B : Subgroup G} (hA : A ∈ conjClass3 K) (hB : B ∈ conjClass3 K) (hAB : Commutes A B)
    (hne : A ≠ B) {u : G} {n : ℕ} (hn : Nat.Coprime n 16) (hu : u ^ n = 1)
    (hAu : A ≤ Subgroup.centralizer ({u} : Set G))
    (hBu : B ≤ Subgroup.centralizer ({u} : Set G)) : u = 1 := by
  classical
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hΩ := hR.inClass
  have hconn := (CoreAssembly.deltaConnected_iff K).mp hR.conn
  obtain ⟨hex, hP1⟩ := hR.setup
  have hO3 : LocalOddThreeFree3 (conjClass3 K) z := h3 G K z hR
  have key : ∀ L ∈ conjClass3 K, ∀ L₀ ∈ conjClass3 K, L₀ ≠ L → Commutes L₀ L →
      L ≤ Subgroup.centralizer ({u} : Set G) → L₀ ≤ Subgroup.centralizer ({u} : Set G) →
      ∀ L' ∈ conjClass3 K, L' ≠ L → Commutes L L' →
        L' ≤ Subgroup.centralizer ({u} : Set G) := by
    intro L hL L₀ hL₀ hne0 hc0 hLu hL₀u L' hL' hne' hc'
    obtain ⟨zL, hzL⟩ := hΩ.classical L hL
    obtain ⟨c⟩ := exists_uctx3_member hΩ hex hsingle hR.cls hP1 hO3 hshape hL hzL
    have hu_z : u * zL * u⁻¹ = zL := by
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hLu hzL.mem)
      rw [mul_inv_eq_iff_eq_mul]
      exact h1.symm
    have hL₀z : L₀ ∈ centralizingMembers (conjClass3 K) {zL} :=
      ⟨hL₀, le_centralizer_of_commutes3 hc0 hzL.mem⟩
    have hL'z : L' ∈ centralizingMembers (conjClass3 K) {zL} :=
      ⟨hL', le_centralizer_of_commutes3 hc'.symm hzL.mem⟩
    obtain ⟨zL₀, hzL₀⟩ := hΩ.classical L₀ hL₀
    exact c.fixed_layer_of_pow hL₀z hne0 hzL₀ hu_z hn hu hL₀u L' hL'z hne'
  set 𝔖 : Set (Subgroup G) := {L | L ∈ conjClass3 K ∧ L ≤ Subgroup.centralizer ({u} : Set G) ∧
    ∃ L₀ ∈ conjClass3 K, L₀ ≠ L ∧ Commutes L₀ L ∧ L₀ ≤ Subgroup.centralizer ({u} : Set G)}
  have hsub : 𝔖 ⊆ conjClass3 K := fun L hL => hL.1
  have hAS : A ∈ 𝔖 := ⟨hA, hAu, B, hB, hne.symm, Gaps.commutes_symm hAB, hBu⟩
  have hcl : ∀ N ∈ 𝔖, ∀ L ∈ conjClass3 K, L ≠ N → Commutes N L → L ∈ 𝔖 := by
    rintro N ⟨hN, hNu, N₀, hN₀, hne0, hc0, hN₀u⟩ L hL hLN hNL
    exact ⟨hL, key N hN N₀ hN₀ hne0 hc0 hNu hN₀u L hL hLN hNL, N, hN, fun h => hLN h.symm, hNL,
      hNu⟩
  have hΩsub : conjClass3 K ⊆ 𝔖 := subset_of_adj_closed hconn hsub ⟨A, hAS⟩ hcl
  have htop : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [← hΩ.generated]
    exact iSup₂_le fun L hL => (hΩsub hL).2.1
  have hcen : u ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (htop (Subgroup.mem_top g))
  rw [CoreAssembly.center_eq_bot hnab, Subgroup.mem_bot] at hcen
  exact hcen

end Centralizer

end CFSG.ClassicalInvolution.Q3.Q3W
