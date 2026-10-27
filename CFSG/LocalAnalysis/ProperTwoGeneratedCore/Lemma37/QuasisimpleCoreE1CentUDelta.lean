module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentUDeltaBasic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open Equiv CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem conj_mem_sylow_inf {i₀ : Fin 5}
    (hi₀ : ∀ π : Perm (Fin 5), π i₀ = i₀ → ∀ σ ∈ d.fourV, π * σ * π⁻¹ ∈ d.fourV)
    {w : QuasiQuotient u} (hw : d.rho5 w i₀ = i₀) {t : QuasiQuotient u}
    (ht : t ∈ (T : Subgroup (quasiNormalizer u)).map (quasiMk u) ∧
      t ∈ L ⊔ Subgroup.centralizer (L : Set (QuasiQuotient u))) :
    w * t * w⁻¹ ∈ (T : Subgroup (quasiNormalizer u)).map (quasiMk u) ∧
      w * t * w⁻¹ ∈ L ⊔ Subgroup.centralizer (L : Set (QuasiQuotient u)) := by
  have := d.oneComponent.normal
  have := d.oneComponent.centralizer_normal
  have hLKn : (L ⊔ Subgroup.centralizer (L : Set (QuasiQuotient u))).Normal := inferInstance
  obtain ⟨htLK, htV⟩ := d.mem_sylow_inf_iff.mp ht
  refine d.mem_sylow_inf_iff.mpr ⟨hLKn.conj_mem t htLK w, ?_⟩
  rw [map_mul, map_mul, map_inv]
  exact hi₀ _ hw _ htV

theorem exists_mem_quasiImage_iff :
    ∃ j₀ : Fin 5, ∀ g : QuasiQuotient u, g ∈ quasiImage B u ↔ d.rho5 g j₀ = j₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := d.baseConfig
  have hKn := d.oneComponent.centralizer_normal
  obtain ⟨P, hPY, -⟩ := hc.sylow
  set T' := T.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 (quasiNormalizer u)))
  have hT' : (T' : Subgroup (QuasiQuotient u)) =
      (T : Subgroup (quasiNormalizer u)).map (quasiMk u) := Sylow.coe_mapSurjective _ _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (QuasiQuotient u) T' P
  have hmemP : ∀ w, g⁻¹ * w * g ∈ (T : Subgroup (quasiNormalizer u)).map (quasiMk u) →
      w ∈ (P : Subgroup (QuasiQuotient u)) := fun w hw => by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hT']
    simpa [MulAut.smul_def, MulAut.conj_apply] using hw
  have hKY : Subgroup.centralizer (L : Set (QuasiQuotient u)) ≤ quasiImage B u := fun k hk =>
    hPY (hmemP k (d.centralizer_le_sylow (by simpa using hKn.conj_mem k hk g⁻¹)))
  set D := ((T : Subgroup (quasiNormalizer u)).map (quasiMk u) ⊓
    (L ⊔ Subgroup.centralizer (L : Set (QuasiQuotient u)))).comap (MulAut.conj g⁻¹).toMonoidHom
  have hmemD : ∀ w, w ∈ D ↔ (g⁻¹ * w * g ∈ (T : Subgroup (quasiNormalizer u)).map (quasiMk u) ∧
      g⁻¹ * w * g ∈ L ⊔ Subgroup.centralizer (L : Set (QuasiQuotient u))) := fun w => by
    simp [D]
  have hDY : D ≤ quasiImage B u := fun w hw => hPY (hmemP w ((hmemD w).mp hw).1)
  obtain ⟨hvL, -, hvT, -, hvv, -, -⟩ := d.lv_lw_facts
  have huT : quasiBar u ∈ (T : Subgroup (quasiNormalizer u)).map (quasiMk u) :=
    Subgroup.mem_map_of_mem _ d.quasiSelf_mem_sylow
  have heT : quasiCentral u ∈ (T : Subgroup (quasiNormalizer u)).map (quasiMk u) := by
    rw [← d.quasiMk_centralElt]
    exact Subgroup.mem_map_of_mem _ d.centralElt_mem_sylow
  have hulv : quasiBar u * d.lv * (quasiBar u * d.lv) = 1 := by
    rw [show quasiBar u * d.lv * (quasiBar u * d.lv) = quasiBar u * (d.lv * quasiBar u) * d.lv
      by group, Subgroup.mem_centralizer_iff.mp d.quasiBar_mem_centralizer d.lv hvL,
      show quasiBar u * (quasiBar u * d.lv) * d.lv = quasiCentral u * (d.lv * d.lv) by
        simp only [quasiCentral]; group, hvv, d.quasiCentral_mul_self]
  have hulvK : ∀ {ε : QuasiQuotient u}, (ε = 1 ∨ ε = quasiCentral u) →
      quasiBar u * d.lv ≠ ε := by
    rintro ε hε h
    have hK : d.lv ∈ Subgroup.centralizer (L : Set (QuasiQuotient u)) := by
      rw [show d.lv = (quasiBar u)⁻¹ * ε by rw [← h]; group]
      refine Subgroup.mul_mem _ (Subgroup.inv_mem _ d.quasiBar_mem_centralizer) ?_
      rcases hε with rfl | rfl
      exacts [Subgroup.one_mem _, d.quasiCentral_mem_centralizer]
    rcases d.eq_of_mem_of_mem_centralizer hvL hK with h1 | h1 <;> rw [h1] at hvv
    · rw [mul_one] at hvv
      exact d.quasiCentral_ne_one hvv.symm
    · rw [d.quasiCentral_mul_self] at hvv
      exact d.quasiCentral_ne_one hvv.symm
  have hrank : 2 ≤ CFSG.Open.pRank 2 D := by
    refine two_le_pRank_of_commuting_involutions (a := quasiCentral u)
      (b := g * (quasiBar u * d.lv) * g⁻¹) ((hmemD _).mpr ?_) ((hmemD _).mpr ?_) hc.order ?_ ?_
      ((hc.commute_center _).symm)
    · rw [d.commute_quasiCentral, inv_mul_cancel_right]
      exact ⟨heT, Subgroup.mem_sup_left d.quasiCentral_mem⟩
    · rw [show g⁻¹ * (g * (quasiBar u * d.lv) * g⁻¹) * g = quasiBar u * d.lv by group]
      exact ⟨Subgroup.mul_mem _ huT hvT, Subgroup.mul_mem _
        (Subgroup.mem_sup_right d.quasiBar_mem_centralizer) (Subgroup.mem_sup_left hvL)⟩
    · have h1 := MulEquiv.orderOf_eq (MulAut.conj g) (quasiBar u * d.lv)
      rw [MulAut.conj_apply] at h1
      rw [h1]
      exact orderOf_eq_prime (by rw [pow_two]; exact hulv) (hulvK (Or.inl rfl))
    · intro h
      apply hulvK (Or.inr rfl)
      calc quasiBar u * d.lv = g⁻¹ * (g * (quasiBar u * d.lv) * g⁻¹) * g := by group
        _ = quasiCentral u := by rw [← h, d.commute_quasiCentral, inv_mul_cancel_right]
  have hND := hc.normalizer_le D hDY hrank
  obtain ⟨hA, hB⟩ := d.fourGroup_facts
  obtain ⟨i₀, hi₀⟩ := perm5_four_group _ _ hA hB
  have hi₀' : ∀ π : Perm (Fin 5), π i₀ = i₀ → ∀ σ ∈ d.fourV, π * σ * π⁻¹ ∈ d.fourV := hi₀
  refine ⟨d.rho5 g i₀, ?_⟩
  have hstab : ∀ w : QuasiQuotient u, d.rho5 w (d.rho5 g i₀) = d.rho5 g i₀ →
      w ∈ quasiImage B u := by
    intro w hw
    have hw' : d.rho5 (g⁻¹ * w * g) i₀ = i₀ := by
      rw [map_mul, map_mul, map_inv, Perm.mul_apply, Perm.mul_apply, hw, Perm.inv_eq_iff_eq]
    have hw'' : d.rho5 (g⁻¹ * w * g)⁻¹ i₀ = i₀ := by
      rw [map_inv, Perm.inv_eq_iff_eq, hw']
    refine hND (Subgroup.mem_normalizer_iff.mpr fun t => ?_)
    rw [hmemD, hmemD]
    constructor
    · intro ht
      have h1 := d.conj_mem_sylow_inf hi₀' hw' ht
      rwa [show g⁻¹ * w * g * (g⁻¹ * t * g) * (g⁻¹ * w * g)⁻¹ = g⁻¹ * (w * t * w⁻¹) * g by
        group] at h1
    · intro ht
      have h1 := d.conj_mem_sylow_inf hi₀' hw'' ht
      rwa [show (g⁻¹ * w * g)⁻¹ * (g⁻¹ * (w * t * w⁻¹) * g) * (g⁻¹ * w * g)⁻¹⁻¹ =
        g⁻¹ * t * g by group] at h1
  intro w
  refine ⟨fun hw => ?_, hstab w⟩
  by_contra hmove
  apply hc.ne_top
  have htop := eq_top_of_stabilizer_le (M := (quasiImage B u).map d.rho5) (j := d.rho5 g i₀)
    (fun π hπ => by
      obtain ⟨w', rfl⟩ := d.rho5_surjective π
      exact Subgroup.mem_map_of_mem _ (hstab w' hπ))
    (Subgroup.mem_map_of_mem _ hw) hmove
  rw [eq_top_iff]
  intro w₂ _
  obtain ⟨w₃, hw₃, h3⟩ := Subgroup.mem_map.mp (htop ▸ Subgroup.mem_top (d.rho5 w₂))
  have hK : w₃⁻¹ * w₂ ∈ Subgroup.centralizer (L : Set (QuasiQuotient u)) :=
    d.mem_centralizer_of_rho5_eq_one (by rw [map_mul, map_inv, h3, inv_mul_cancel])
  rw [show w₂ = w₃ * (w₃⁻¹ * w₂) by group]
  exact Subgroup.mul_mem _ hw₃ (hKY hK)

theorem exists_mem_map_iff : ∃ j₀ : Fin 5, ∀ c : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)},
    (c : J ⧸ Subgroup.center J) ∈ B.map (QuotientGroup.mk' (Subgroup.center J)) ↔
      d.rho5C c j₀ = j₀ := by
  obtain ⟨j₀, hj₀⟩ := d.exists_mem_quasiImage_iff
  refine ⟨j₀, fun c => ?_⟩
  obtain ⟨g, rfl⟩ := d.toCentralizer_surjective c
  rw [coe_toCentralizer, d.setting.mk_mem_map_iff, ← d.starLift.toEscapingLift.mk_mem_quasiImage_iff
    d.setting d.fourGen d.starLift.rank, hj₀, rho5C, liftC_toCentralizer]

theorem exists_mem_map_iff_phiU : ∃ j₀ : Fin 9, 4 ≤ (j₀ : ℕ) ∧
    ∀ c : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)},
      (c : J ⧸ Subgroup.center J) ∈ B.map (QuotientGroup.mk' (Subgroup.center J)) ↔
        ((d.phiU c : alternatingGroup (Fin 9)) : Perm (Fin 9)) j₀ = j₀ := by
  obtain ⟨j₀, hj₀⟩ := d.exists_mem_map_iff
  refine ⟨Fin.natAdd 4 j₀, by simp, fun c => ?_⟩
  rw [hj₀, coe_phiU, permNine_natAdd]
  exact ⟨fun h => by rw [h], fun h => (Fin.natAdd_inj 4).mp h⟩

theorem exists_smul_eq_smul_iff : ∃ j₀ : Fin 5,
    ∀ c c' : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)},
      c • ((1 : J ⧸ Subgroup.center J) :
          (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J))) =
        c' • ((1 : J ⧸ Subgroup.center J) :
          (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J))) ↔
      d.rho5C c j₀ = d.rho5C c' j₀ := by
  obtain ⟨j₀, hj₀⟩ := d.exists_mem_map_iff
  refine ⟨j₀, fun c c' => ?_⟩
  change (c : J ⧸ Subgroup.center J) • ((1 : J ⧸ Subgroup.center J) :
      (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J))) =
    (c' : J ⧸ Subgroup.center J) • ((1 : J ⧸ Subgroup.center J) :
      (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J))) ↔ _
  rw [MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, smul_eq_mul, smul_eq_mul, mul_one,
    mul_one, QuotientGroup.eq, show (c : J ⧸ Subgroup.center J)⁻¹ * c' =
    ((c⁻¹ * c' : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) : J ⧸ Subgroup.center J)
    from rfl, hj₀, map_mul, map_inv, Perm.mul_apply, Perm.inv_eq_iff_eq, eq_comm]

theorem ncard_orbit : (MulAction.orbit (Subgroup.centralizer {(u : J ⧸ Subgroup.center J)})
    ((1 : J ⧸ Subgroup.center J) :
      (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J)))).ncard = 5 := by
  obtain ⟨j₀, hj₀⟩ := d.exists_smul_eq_smul_iff
  have hstab : MulAction.stabilizer (Subgroup.centralizer {(u : J ⧸ Subgroup.center J)})
      ((1 : J ⧸ Subgroup.center J) :
        (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J))) =
      (MulAction.stabilizer (Perm (Fin 5)) j₀).comap d.rho5C := by
    ext c
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_comap, MulAction.mem_stabilizer_iff,
      Perm.smul_def]
    have h := hj₀ c 1
    rw [one_smul, map_one, Perm.one_apply] at h
    exact h
  rw [← MulAction.index_stabilizer, hstab, Subgroup.index_comap_of_surjective _ d.rho5C_surjective,
    MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin]

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
