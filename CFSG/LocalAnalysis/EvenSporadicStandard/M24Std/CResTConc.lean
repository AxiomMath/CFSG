module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResNonSplitBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResTLat
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CSideOdd
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Sym6Sign
public import Certificates.Certificate25730

public section

namespace CFSG.EvenSporadicStandard.M24Std

namespace Sym6

open Subgroup CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint

variable {G : Type} [Group G] {L A : Subgroup G} {e : L ≃* S24}
  (hA : ∀ x : L, (x : G) ∈ A ↔ e x ∈ m24E1l)
include hA


theorem tetE_qdIota (hAL : A ≤ L) {s : S24} (hs : QdNorm s) :
    tetE hA ⟨qdIota e s, qdIota_mem_egNL e hAL hA hs⟩ = tetAct s hs := by
  refine Equiv.ext fun i => ?_
  rw [tetE_apply, nlE_mk, tetAct_apply]

theorem exists_nonsplit_pair (hAL : A ≤ L) :
    ∃ x y : egNL L A, tetE hA x ∈ alternatingGroup (Fin 6) ∧
      tetE hA y ∈ alternatingGroup (Fin 6) ∧ tetE hA x * tetE hA y = tetE hA y * tetE hA x ∧
      x * y * x⁻¹ * y⁻¹ ∉ A.subgroupOf (egNL L A) := by
  obtain ⟨hx, hy, hxy⟩ := tet_nonsplit_perm
  have ex : tetE hA ⟨qdIota e nsX, qdIota_mem_egNL e hAL hA qdNorm_nsX⟩ =
      tetAct nsX qdNorm_nsX := tetE_qdIota hA hAL qdNorm_nsX
  have ey : tetE hA ⟨qdIota e nsY, qdIota_mem_egNL e hAL hA qdNorm_nsY⟩ =
      tetAct nsY qdNorm_nsY := tetE_qdIota hA hAL qdNorm_nsY
  refine ⟨⟨qdIota e nsX, qdIota_mem_egNL e hAL hA qdNorm_nsX⟩,
    ⟨qdIota e nsY, qdIota_mem_egNL e hAL hA qdNorm_nsY⟩, ?_, ?_, ?_, ?_⟩
  · rw [ex]; exact hx
  · rw [ey]; exact hy
  · rw [ex, ey]; exact hxy
  · intro hmem
    rw [Subgroup.mem_subgroupOf] at hmem
    have h1 : (((⟨qdIota e nsX, qdIota_mem_egNL e hAL hA qdNorm_nsX⟩ : egNL L A) *
        ⟨qdIota e nsY, qdIota_mem_egNL e hAL hA qdNorm_nsY⟩ *
        (⟨qdIota e nsX, qdIota_mem_egNL e hAL hA qdNorm_nsX⟩ : egNL L A)⁻¹ *
        (⟨qdIota e nsY, qdIota_mem_egNL e hAL hA qdNorm_nsY⟩ : egNL L A)⁻¹ : egNL L A) : G) =
        qdIota e (nsX * nsY * nsX⁻¹ * nsY⁻¹) := by
      simp [map_mul, map_inv]
    rw [h1, qdIota_mem_A e hA] at hmem
    exact Certificates.certificate25730 hmem

end Sym6

namespace CSide

open Sym6 Subgroup CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L A C : Subgroup G} {z : G}

theorem exists_triple_cover
    (h : Setup L A C z) (hty : SextetType L A) :
    ∃ H : Subgroup (egNL L A), H.index = 2 ∧
      (∀ t ∈ H.map (psi h), zt h * t = t * zt h) ∧ commutator ↥(H.map (psi h)) = ⊤ ∧
      Nat.card ↥(H.map (psi h)) = 1080 ∧
      (∃ w ∈ H.map (psi h), orderOf w = 3 ∧ ∀ t ∈ H.map (psi h), t * w = w * t) ∧
      ∀ M : Subgroup (egQD C), (∀ m ∈ M, zt h * m = m * zt h) →
        (∀ g : egQD C, zt h * g = g * zt h → ∀ m ∈ M, g * m * g⁻¹ ∈ M) →
        (∀ t ∈ H.map (psi h), t ∈ M) ∨ ∀ a ∈ M, ∀ b ∈ M, a * b = b * a := by
  obtain ⟨hAL, e, hA⟩ := hty
  set σ : egNL L A →* Equiv.Perm (Fin 6) := tetE hA with hσdef
  have hσs : Function.Surjective σ := tetE_surjective hA hAL
  have hσA : A.subgroupOf (egNL L A) ≤ σ.ker := le_ker_tetE hA
  set H : Subgroup (egNL L A) := (alternatingGroup (Fin 6)).comap σ with hH
  have hHidx : H.index = 2 := (index_two_iff hA hAL H).2 rfl
  refine ⟨H, hHidx, ?_⟩
  set ψ : egNL L A →* egQD C := psi h with hψ
  set K : Subgroup (egQD C) := ψ.range with hK
  let ψK : egNL L A →* K := ψ.rangeRestrict
  have hψKs : Function.Surjective ψK := ψ.rangeRestrict_surjective
  have hψKker : ψK.ker = A.subgroupOf (egNL L A) := by
    rw [MonoidHom.ker_rangeRestrict, hψ, ker_psi h]
  have hker : ψK.ker ≤ σ.ker := hψKker ▸ hσA
  let σK : K →* Equiv.Perm (Fin 6) := ψK.liftOfSurjective hψKs ⟨σ, hker⟩
  have hσK : ∀ n, σK (ψK n) = σ n := fun n =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨σ, hker⟩ n
  have hAle : A ≤ egNL L A := fun a ha => mem_inf.2 ⟨le_normalizer ha, hAL ha⟩
  have hkerψ : Nat.card ψ.ker = 64 := by
    rw [hψ, ker_psi h, ← h.hF.card_A]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv
  have hN : Nat.card (egNL L A) = 138240 := card_egNL_eq hA hAL
  have h6 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hKcard : Nat.card K = 2160 := by
    have := Subgroup.card_ker_mul_card_range ψ
    rw [hkerψ, hN] at this
    change 64 * Nat.card K = 138240 at this
    omega
  have hσKs : Function.Surjective σK := by
    intro p
    obtain ⟨n, hn⟩ := hσs p
    exact ⟨ψK n, by rw [hσK]; exact hn⟩
  have hZ : Nat.card σK.ker = 3 := by
    have := Subgroup.card_ker_mul_card_range σK
    rw [MonoidHom.range_eq_top.2 hσKs, Subgroup.card_top, h6, hKcard] at this
    omega
  obtain ⟨x, y, hx, hy, hxy, hnc⟩ := exists_nonsplit_pair hA hAL
  have hx0 : σK (ψK x) ∈ alternatingGroup (Fin 6) := by rw [hσK]; exact hx
  have hy0 : σK (ψK y) ∈ alternatingGroup (Fin 6) := by rw [hσK]; exact hy
  have hσc : σK (ψK x) * σK (ψK y) = σK (ψK y) * σK (ψK x) := by
    rw [hσK, hσK]
    exact hxy
  have hne : ψK x * ψK y ≠ ψK y * ψK x := by
    intro hc
    apply hnc
    have h1 : ψK (x * y * x⁻¹ * y⁻¹) = ψK x * ψK y * (ψK x)⁻¹ * (ψK y)⁻¹ := by
      simp only [map_mul, map_inv]
    rw [← hψKker, MonoidHom.mem_ker, h1, hc]
    group
  have hperf := commutator_comap_alt_six σK hσKs hZ (ψK x) (ψK y) hx0 hy0 hσc hne
  obtain ⟨w, hwk, hw3, hwc⟩ := exists_central_order_three σK hZ hperf
  set TK : Subgroup K := (alternatingGroup (Fin 6)).comap σK with hTK
  have hTeq : H.map ψ = TK.map K.subtype := by
    ext t
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨ψK n, ?_, rfl⟩
      show σK (ψK n) ∈ alternatingGroup (Fin 6)
      rw [hσK]
      exact hn
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨n, rfl⟩ := hψKs k
      refine ⟨n, ?_, rfl⟩
      have : σK (ψK n) ∈ alternatingGroup (Fin 6) := hk
      rw [hσK] at this
      exact this
  have hKz : ∀ k ∈ K, zt h * k = k * zt h := by
    rintro _ ⟨n, rfl⟩
    exact (psi_comm h n).symm
  have hΓ : ∀ g : egQD C, zt h * g = g * zt h → ∃ k ∈ K, g = k ∨ g = k * zt h := by
    intro g hg
    have hg' : g ∈ centralizer ({zt h} : Set (egQD C)) :=
      mem_centralizer_iff.2 fun c hc => by
        rw [Set.mem_singleton_iff] at hc
        rw [hc]
        exact hg
    rw [centralizer_quot_eq h] at hg'
    have hle : zpowers (zt h) ≤ centralizer (K : Set (egQD C)) := by
      rw [zpowers_le]
      exact mem_centralizer_iff.2 fun y hy => by
        obtain ⟨n, rfl⟩ := hy
        exact psi_comm h n
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_centralizer hle hg'
    rcases mem_zpowers_zt h hb with rfl | rfl
    · exact ⟨a, ha, Or.inl (by simpa using hab)⟩
    · exact ⟨a, ha, Or.inr hab⟩
  rw [hTeq]
  refine ⟨fun t ht => ?_, ?_, ?_, ?_, fun M hMz hMn => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := ht
    exact hKz k k.2
  · have hc : ⁅TK.map K.subtype, TK.map K.subtype⁆ = TK.map K.subtype := by
      rw [← Subgroup.map_commutator, hperf]
    exact ((Subgroup.isPerfect_iff).2 hc).commutator_eq_top
  · rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact card_comap_alt_six σK hσKs hZ
  · have hwT : w ∈ TK := by
      show σK w ∈ alternatingGroup (Fin 6)
      rw [MonoidHom.mem_ker.1 hwk]
      exact one_mem _
    refine ⟨(w : egQD C), ⟨w, hwT, rfl⟩, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe]
      exact hw3
    · rintro _ ⟨k, hk, rfl⟩
      exact congrArg Subtype.val (hwc k hk)
  · exact lattice_of_triple_cover hKz hΓ σK hσKs hZ hperf M hMz hMn

end CSide

end CFSG.EvenSporadicStandard.M24Std
