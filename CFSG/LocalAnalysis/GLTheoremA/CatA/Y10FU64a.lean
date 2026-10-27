module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem glaPPrimeCore_ne_top {r : ℕ} (hr : r.Prime) {X K : Subgroup G} (hKr : GLAPComponent r X K) :
    GLAPPrimeCore r ↥K ≠ ⊤ := by
  have hQr : CFSG.Open.IsQuasisimple (PQuot r K) := isQuasisimple_pQuot_of_glaPComponent hr hKr
  haveI : Nontrivial (PQuot r K) := isQuasisimple_nontrivial hQr
  intro htop
  haveI : Subsingleton (↥K ⧸ GLAPPrimeCore r ↥K) := by
    rw [htop]; exact QuotientGroup.subsingleton_quotient_top
  exact (not_subsingleton _ ‹Subsingleton (↥K ⧸ GLAPPrimeCore r ↥K)›)

theorem mix_sup_ne_top {p r : ℕ} (hp : p.Prime) (hr : r.Prime) {X K : Subgroup G}
    (hKp : GLAPComponent p X K) (hKr : GLAPComponent r X K) :
    GLAPPrimeCore p ↥K ⊔ GLAPPrimeCore r ↥K ≠ ⊤ := by
  intro hsup
  have hne : GLAPPrimeCore r ↥K ≠ ⊤ := glaPPrimeCore_ne_top hr hKr
  set J : Subgroup G := (GLAPPrimeCore r ↥K).map K.subtype with hJ
  have hJK : J ≤ K := map_subtype_le _
  have hJlt : J < K := by
    refine lt_of_le_of_ne hJK fun heq => hne ?_
    apply Subgroup.map_injective K.subtype_injective
    rw [← hJ, heq, Subgroup.map_top, Subgroup.range_subtype]
  have hJsub : IsSubnormal J K := by
    refine IsSubnormal.step hJK ?_ (IsSubnormal.refl K)
    rw [hJ, map_subtype_subgroupOf]
    infer_instance
  have hJX : IsSubnormal J X := hJsub.trans hKp.2.1
  have hcore : GLAPPrimeCoreOf p K ≤ GLAPPrimeCoreOf p X := by
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hKp.2.1]
    exact inf_le_right
  refine hKp.2.2.2 J hJlt hJX ?_
  show barX p X J = barX p X K
  refine le_antisymm (barX_mono p hJK) ?_
  refine barX_le_of_forall (hJK.trans hKp.1) (fun k hk => ?_)
  have hk' : (⟨k, hk⟩ : ↥K) ∈ GLAPPrimeCore p ↥K ⊔ GLAPPrimeCore r ↥K := by rw [hsup]; trivial
  obtain ⟨n, hn, m, hm, hnm⟩ := Subgroup.mem_sup_of_normal_left.1 hk'
  refine ⟨(m : G), Subgroup.mem_map_of_mem _ hm, ?_⟩
  apply hcore
  have h1 : ((m : G))⁻¹ * k = (((m⁻¹ * n * m : ↥K)) : G) := by
    have : (⟨k, hk⟩ : ↥K) = n * m := hnm.symm
    have h2 := congrArg Subtype.val this
    simp only at h2
    rw [h2]; simp [mul_assoc]
  rw [h1]
  have hmem : m⁻¹ * n * m ∈ GLAPPrimeCore p ↥K := by
    have := (inferInstance : (GLAPPrimeCore p ↥K).Normal).conj_mem n hn m⁻¹
    simpa using this
  exact ⟨m⁻¹ * n * m, hmem, rfl⟩


theorem mix_commutator_le_right {p r : ℕ} (hp : p.Prime) (hr : r.Prime) {X K : Subgroup G}
    (hKp : GLAPComponent p X K) (hKr : GLAPComponent r X K) :
    ⁅GLAPPrimeCore p ↥K, (⊤ : Subgroup ↥K)⁆ ≤ GLAPPrimeCore r ↥K := by
  have hQ : CFSG.Open.IsQuasisimple (PQuot r K) := isQuasisimple_pQuot_of_glaPComponent hr hKr
  set N := GLAPPrimeCore p ↥K
  set M := GLAPPrimeCore r ↥K
  have hnorm : (N.map (QuotientGroup.mk' M)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hne : N.map (QuotientGroup.mk' M) ≠ ⊤ := by
    intro htop
    apply mix_sup_ne_top hp hr hKp hKr
    have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' M) N
    rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
    exact h1.symm
  have hcen := le_center_of_normal_of_isQuasisimple hQ hnorm hne
  rw [Subgroup.commutator_le]
  intro n hn k _
  have h1 := Subgroup.mem_center_iff.1 (hcen (Subgroup.mem_map_of_mem (QuotientGroup.mk' M) hn))
    (QuotientGroup.mk' M k)
  rw [← QuotientGroup.eq_one_iff (N := M)]
  show QuotientGroup.mk' M ⁅n, k⁆ = 1
  rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
  calc QuotientGroup.mk' M n * QuotientGroup.mk' M k * (QuotientGroup.mk' M n)⁻¹ *
        (QuotientGroup.mk' M k)⁻¹ = QuotientGroup.mk' M k * QuotientGroup.mk' M n *
        (QuotientGroup.mk' M n)⁻¹ * (QuotientGroup.mk' M k)⁻¹ := by rw [h1]
    _ = 1 := by group

theorem mix_commutator_le {p r : ℕ} (hp : p.Prime) (hr : r.Prime) {X K : Subgroup G}
    (hKp : GLAPComponent p X K) (hKr : GLAPComponent r X K) :
    ⁅GLAPPrimeCore p ↥K, (⊤ : Subgroup ↥K)⁆ ≤ GLAPPrimeCore p ↥K ⊓ GLAPPrimeCore r ↥K :=
  le_inf (Subgroup.commutator_le_left _ _) (mix_commutator_le_right hp hr hKp hKr)

end CFSG.LocalAnalysis.GLTheoremA.Y10F
