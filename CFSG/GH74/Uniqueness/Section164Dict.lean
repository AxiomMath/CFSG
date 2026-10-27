module

public import CFSG.GH74.Uniqueness.Bender.Lemma32
public import CFSG.GH74.Uniqueness.Setup

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec164

theorem exists_sylow_borel_eq
    (S : ZDSetup X Z M) {G : Subgroup X} {m i e : ℕ}
    (h : Bender.BenderType ↥G m i e) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) (hzG : z ∈ G)
    (hGM : ¬ G ≤ M) :
    ∃ Q : Sylow 2 ↥G, (⟨z, hzG⟩ : ↥G) ∈ Bender.rootCenter (Q : Subgroup ↥G) ∧
      M.comap G.subtype = Bender.borel (Q : Subgroup ↥G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz'2 : orderOf (⟨z, hzG⟩ : ↥G) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact S.invariant.1 z hz
  have hP : IsPGroup 2 (zpowers (⟨z, hzG⟩ : ↥G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'2, pow_one])
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  have hzQ : (⟨z, hzG⟩ : ↥G) ∈ (Q : Subgroup ↥G) := hQ (mem_zpowers _)
  obtain ⟨t₀, hc⟩ := h.exists_benderCore Q
  have hzR : (⟨z, hzG⟩ : ↥G) ∈ Bender.rootCenter (Q : Subgroup ↥G) :=
    hc.center_of_involution _ (Bender.le_borel _ hzQ) hz'2
  have hborel : Bender.borel (Q : Subgroup ↥G) ≤ M.comap G.subtype := by
    intro g hg
    rw [mem_comap]
    have hg' : g⁻¹ ∈ normalizer ((Q : Subgroup ↥G) : Set ↥G) := inv_mem hg
    have h1 : g⁻¹ * ⟨z, hzG⟩ * g⁻¹⁻¹ ∈ (Q : Subgroup ↥G) := (mem_normalizer_iff.mp hg' _).mp hzQ
    rw [inv_inv] at h1
    have h2 : (g : X)⁻¹ * z * g ∈ M := by
      have hq : g⁻¹ * ⟨z, hzG⟩ * g ∈ Bender.rootCenter (Q : Subgroup ↥G) := by
        have := Bender.conj_mem_rootCenter hg' hzR
        simpa using this
      have hqc := (Bender.mem_rootCenter_iff.mp hq)
      have hQM : ∀ q ∈ (Q : Subgroup ↥G), (q : X) ∈ M := by
        intro q hq'
        apply S.prodDisc.centralizer_le_of_mem hz hzM
        rw [mem_centralizer_singleton_iff]
        exact congrArg Subtype.val ((Bender.mem_rootCenter_iff.mp hzR).2 q hq')
      exact hQM _ hqc.1
    exact S.prodDisc.mem_of_conj_mem hz hzM h2
  have hne : M.comap G.subtype ≠ ⊤ := by
    intro htop
    apply hGM
    intro g hg
    have : (⟨g, hg⟩ : ↥G) ∈ M.comap G.subtype := htop ▸ mem_top _
    exact this
  exact ⟨Q, hzR, le_antisymm (h.le_borel_of_sylow_le Q ((Bender.le_borel _).trans hborel) hne)
    hborel⟩

theorem mem_rootCenter_of_mem
    {G : Subgroup X} {m i e : ℕ} (h : Bender.BenderType ↥G m i e)
    {Q : Sylow 2 ↥G} (hQ : M.comap G.subtype = Bender.borel (Q : Subgroup ↥G)) {y : X}
    (hyG : y ∈ G) (hyM : y ∈ M) (hy2 : orderOf y = 2) :
    (⟨y, hyG⟩ : ↥G) ∈ Bender.rootCenter (Q : Subgroup ↥G) := by
  obtain ⟨t₀, hc⟩ := h.exists_benderCore Q
  refine hc.center_of_involution _ ?_ (by rw [Subgroup.orderOf_mk]; exact hy2)
  rw [← hQ]
  exact hyM

theorem mem_inter_of_mem_rootCenter
    {G : Subgroup X} {m i e : ℕ} (h : Bender.BenderType ↥G m i e)
    {Q : Sylow 2 ↥G} (hQ : M.comap G.subtype = Bender.borel (Q : Subgroup ↥G)) {y : ↥G}
    (hy : y ∈ Bender.rootCenter (Q : Subgroup ↥G)) (hy1 : y ≠ 1) :
    (y : X) ∈ M ∧ orderOf (y : X) = 2 := by
  obtain ⟨t₀, hc⟩ := h.exists_benderCore Q
  obtain ⟨hyB, hyo⟩ := hc.involution_iff.mpr ⟨hy, hy1⟩
  refine ⟨?_, by rw [Subgroup.orderOf_coe]; exact hyo⟩
  rw [← hQ] at hyB
  exact hyB

theorem zHull_inter_eq_map_rootCenter {G : Subgroup X} {m i e : ℕ}
    (h : Bender.BenderType ↥G m i e) {Q : Sylow 2 ↥G}
    (hQ : M.comap G.subtype = Bender.borel (Q : Subgroup ↥G))
    (hinv : ∀ y ∈ G, orderOf y = 2 → y ∈ Z) (hZ : IsInvariantInvolutionSet Z) :
    zHull Z (M ⊓ G) = (Bender.rootCenter (Q : Subgroup ↥G)).map G.subtype := by
  apply le_antisymm
  · refine (closure_le _).mpr ?_
    rintro y ⟨hyZ, hyMG⟩
    obtain ⟨hyM, hyG⟩ := mem_inf.mp hyMG
    exact ⟨⟨y, hyG⟩, mem_rootCenter_of_mem h hQ hyG hyM (hZ.1 y hyZ), rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    by_cases hy1 : y = 1
    · rw [hy1]
      exact one_mem _
    · obtain ⟨hyM, hyo⟩ := mem_inter_of_mem_rootCenter h hQ hy hy1
      exact subset_closure ⟨hinv _ y.2 hyo, mem_inf.mpr ⟨hyM, y.2⟩⟩

theorem card_zHull_inter
    {G : Subgroup X} {m i e : ℕ} (h : Bender.BenderType ↥G m i e)
    {Q : Sylow 2 ↥G} (hQ : M.comap G.subtype = Bender.borel (Q : Subgroup ↥G))
    (hinv : ∀ y ∈ G, orderOf y = 2 → y ∈ Z) (hZ : IsInvariantInvolutionSet Z) :
    Nat.card ↥(zHull Z (M ⊓ G)) = 2 ^ m := by
  obtain ⟨t₀, hc⟩ := h.exists_benderCore Q
  rw [zHull_inter_eq_map_rootCenter h hQ hinv hZ, card_map_of_injective G.subtype_injective,
    hc.card_center]

theorem cartan_eq_comap
    {G : Subgroup X} {m i e : ℕ} (h : Bender.BenderType ↥G m i e)
    {Q : Sylow 2 ↥G} (hQ : M.comap G.subtype = Bender.borel (Q : Subgroup ↥G)) {t : X}
    (htG : t ∈ G) (htM : t ∉ M) (ht2 : t * t = 1) :
    Bender.BenderCore (2 ^ m) i e (Q : Subgroup ↥G) ⟨t, htG⟩ ∧
      Bender.cartan (Q : Subgroup ↥G) ⟨t, htG⟩ = (M ⊓ conjugate M t).comap G.subtype := by
  have ht2' : (⟨t, htG⟩ : ↥G) * ⟨t, htG⟩ = 1 := Subtype.ext ht2
  have htB : (⟨t, htG⟩ : ↥G) ∉ Bender.borel (Q : Subgroup ↥G) := by
    rw [← hQ]
    exact htM
  refine ⟨h.benderCore Q ht2' htB, ?_⟩
  ext x
  rw [Bender.cartan, mem_inf, ← hQ, Bender.mem_conjugate_iff_mul_inv, mem_comap, mem_comap,
    mem_comap, mem_inf, mem_conjugate_iff]
  rfl

end Sec164

end CFSG.GH74.Uniqueness
