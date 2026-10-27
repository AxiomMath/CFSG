module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdL2
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerH

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7Std

open CFSG Subgroup CatFactsSp4
open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem eq_layerOf_of_simple {G : Type*} [Group G] [Finite G] {X L : Subgroup G} (hLX : L ≤ X)
    (hL : IsPComponent 2 (L.subgroupOf X)) (hs : IsSimpleGroup (layerOf X)) : L = layerOf X := by
  have hLE : L ≤ layerOf X := le_layerOf hLX hL
  have hEX : layerOf X ≤ X := sSup_le fun M hM => hM.1
  have hLb : L ≠ ⊥ := CatFactsSp4.ne_bot_of_isPComponent hL
  obtain ⟨-, -, hsn, -, -⟩ := hL
  have hsn' := CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hEX hsn
  rcases hsn'.eq_bot_or_top_of_isSimpleGroup hs with h | h
  · exfalso
    apply hLb
    rw [subgroupOf_eq_bot] at h
    exact le_bot_iff.mp (fun y hy => h.le_bot ⟨hy, hLE hy⟩)
  · rw [subgroupOf_eq_top] at h
    exact le_antisymm hLE h

theorem false_of_central_involution {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    {F : Type} [Field F] [Finite F] (e : L ⧸ pPrimeCore 2 L ≃* GorensteinWalter.PSL2 F) {z : G}
    (hz : z ∈ L) (hzo : orderOf z = 2) (hzc : ∀ y ∈ L, y * z = z * y) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : e (QuotientGroup.mk (⟨z, hz⟩ : L)) ∈ center (GorensteinWalter.PSL2 F) := by
    rw [mem_center_iff]
    intro w
    obtain ⟨v, rfl⟩ := e.surjective w
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 2
    exact Subtype.ext (hzc y y.2)
  rw [GorensteinWalter.psl2_center_eq_bot, mem_bot] at hc
  have h1 : (QuotientGroup.mk (⟨z, hz⟩ : L) : L ⧸ pPrimeCore 2 L) = 1 :=
    e.injective (hc.trans (map_one e).symm)
  rw [QuotientGroup.eq_one_iff] at h1
  have hord : orderOf (⟨⟨z, hz⟩, h1⟩ : pPrimeCore 2 L) = 2 :=
    ((Subgroup.orderOf_coe (⟨⟨z, hz⟩, h1⟩ : pPrimeCore 2 L)).symm.trans
      (Subgroup.orderOf_coe (⟨z, hz⟩ : L)).symm).trans hzo
  have hdvd := orderOf_dvd_natCard (⟨⟨z, hz⟩, h1⟩ : pPrimeCore 2 L)
  rw [hord] at hdvd
  have hcop := (pPrimeCore_coprime_card (p := 2) (G := L)).coprime_dvd_right hdvd
  norm_num at hcop

variable {K : Type} [Field K]

theorem pComponent_P {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) (hs : IsSimpleGroup (StatedProj (StatedSp 2 K)))
    (α : MulAut (StatedProj (StatedSp 2 K))) (hα2 : α * α = 1) (hα1 : α ≠ 1)
    {L : Subgroup (StatedProj (StatedSp 2 K))} (hLX : L ≤ fixOf α)
    (hL : IsPComponent 2 (L.subgroupOf (fixOf α))) :
    (∃ z ∈ L, orderOf z = 2 ∧ ∀ y ∈ L, y * z = z * y) ∨
      (IsSimpleGroup L ∧ (Nat.card L * 2 = p ^ f * ((p ^ f) ^ 2 - 1) ∨
        Nat.card L * 2 = (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) ∨
        ∃ k : ℕ, k ^ 2 = p ^ f ∧ 3 ≤ k ∧
          Nat.card L * 2 = k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)))) := by
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have h2 := two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card K := by omega
  have hchar : ringChar K ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := K)
    rw [h] at this
    exact_mod_cast this
  set E := layerOf (fixOf α) with hEdef
  have hLE : IsSimpleGroup E → L = E := fun hE => eq_layerOf_of_simple hLX hL hE
  have hhalf : ∀ x : ℕ, x * (x ^ 2 - 1) / 2 * 2 = x * (x ^ 2 - 1) := fun x =>
    Nat.div_mul_cancel (two_dvd_mul_sq_sub x)
  obtain ⟨A, σ, hα, hσ2, ⟨d, hd⟩, -, hfield⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      hchar le_rfl).2.2 α hα2 hα1
  by_cases hσ : σ = 1
  · subst hσ
    have hα' : α = conjAut 2 K A := by rw [hα, map_one, mul_one]
    have hAA := mul_self_of_rep A d hd
    have hμ := multiplierUnit_spec A
    by_cases hsq : ∃ l : K, l ^ 2 = (multiplierUnit A : K)
    ·
      obtain ⟨u, hu⟩ := conjAut_mem_range_of_sq A hsq.choose_spec
      have hαu : α = MulAut.conj u := by rw [hα', ← hu]
      have hu1 : u ≠ 1 := fun h => hα1 (by rw [hαu, h, map_one])
      have hu2 : u * u = 1 := by
        have hc : MulAut.conj (u * u) = 1 := by rw [map_mul, ← hαu, hα2]
        apply eq_one_of_mem_center_P h2 h4 hs
        rw [mem_center_iff]
        intro g
        have := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 K)) => φ g) hc
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc g * (u * u) = u * u * g * (u * u)⁻¹ * (u * u) := by rw [this]
          _ = u * u * g := by group
      have huo : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
      obtain ⟨g, hg⟩ := exists_conj_of_orderOf_eq_two hodd huo
      set φ := MulAut.conj g⁻¹ with hφdef
      have hφu : φ u = g⁻¹ * u * g := by rw [hφdef, MulAut.conj_apply, inv_inv]
      have hcomm : ∀ x, φ (α x) = MulAut.conj (φ u) (φ x) := fun x => by
        rw [hαu]
        exact conj_comm φ u x
      rcases hg with h | h
      ·
        left
        have hfix : (fixOf α).map φ.toMonoidHom = centralizer {u1 K} := by
          rw [map_fixOf_of_comm hcomm, hφu, h, fixOf_conj]
        have hL' := (Sp4Rec.isPComponent_subgroupOf_map_iff φ hLX).mp hL
        rw [hfix] at hL'
        have hL'X : L.map φ.toMonoidHom ≤ centralizer {u1 K} := hfix ▸ map_mono hLX
        obtain ⟨hE12, -⟩ := pComponent_centralizer_u1 hodd hL'X hL'
        have hmem : u1 K ∈ L.map φ.toMonoidHom := by
          rcases hE12 with h' | h'
          · rw [h']; exact u1_mem_E1
          · rw [h']; exact u1_mem_E2
        have hX0 : L.map φ.toMonoidHom ≤ X0 K := by
          rcases hE12 with h' | h'
          · rw [h']; exact E1_le_X0 h2
          · rw [h']; exact E2_le_X0 h2
        obtain ⟨z, hz, hzu⟩ := hmem
        refine ⟨z, hz, ?_, fun y hy => ?_⟩
        · have : orderOf (φ z) = 2 := by
            rw [show φ z = u1 K from hzu]
            exact orderOf_eq_prime (by rw [pow_two]; exact u1_mul_u1) (u1_ne_one h2)
          rwa [MulEquiv.orderOf_eq] at this
        · apply φ.injective
          rw [map_mul, map_mul, show φ z = u1 K from hzu]
          exact (u1_comm_of_mem_X0 (hX0 ⟨y, hy, rfl⟩)).symm
      ·
        right
        have hEmap : E.map φ.toMonoidHom = layerOf (fixOf (MulAut.conj (φ u))) := by
          rw [hEdef, map_layerOf, map_fixOf_of_comm hcomm]
        rw [hφu, h, fixOf_conj, layerOf_u2 hodd h4] at hEmap
        have hEL : (Lsub K).map φ.symm.toMonoidHom = E := by
          rw [← hEmap, Subgroup.map_map]
          convert Subgroup.map_id E
          ext x
          simp
        obtain ⟨hE', -⟩ := simple_data_map φ.symm (isSimpleGroup_Lsub h4)
          (exists_mul_ne_of_isQuasisimple (isQuasisimple_Lsub h4))
        rw [hEL] at hE'
        have hLeq := hLE hE'
        refine ⟨hLeq ▸ hE', Or.inl ?_⟩
        rw [hLeq, ← hEL, card_map_equiv, card_Lsub hodd, hK, hhalf]
    · push Not at hsq
      rcases eq_or_eq_neg_multiplier A hAA with hdm | hdm
      ·
        right
        have hdsq : ∀ l : K, l ^ 2 ≠ (d : K) := by rw [hdm]; exact hsq
        have hμd : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
            formJ 2 K * ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
              (d : K) • formJ 2 K := by rw [hdm]; exact hμ
        obtain ⟨hQ, hcard⟩ := fixOf_conjSp_nonsquare hp hp2 hf hK A d.ne_zero hdsq hAA hμd
        have hc := card_center_fixOf_nonsquare hp hp2 hf hK A d.ne_zero hdsq hAA hμd
        have hθα : ∀ g, α (proj 2 K g) = proj 2 K (conjSp 2 K A g) := fun g => by
          rw [hα', conjAut_proj]
        have hZ : ∀ z ∈ spScalars 2 K, conjSp 2 K A z = z := fun z hz => conjSp_scalar A hz
        have h4dvd : 4 ∣ Nat.card (fixOf (conjSp 2 K A)) := by
          rw [hcard]
          have : 4 ∣ ((p ^ f) ^ 2) ^ 2 - 1 := by
            have ho : Odd ((p ^ f) ^ 2) := (hK ▸ hodd).pow
            obtain ⟨r, hr⟩ := ho
            refine ⟨r ^ 2 + r, ?_⟩
            rw [hr]
            have : (2 * r + 1) ^ 2 = 4 * (r ^ 2 + r) + 1 := by ring
            omega
          exact Dvd.dvd.mul_left this _
        have hEN := layerOf_fixOf_eq h2 (conjSp 2 K A) hθα hZ hQ h4dvd
        have hNs := isSimpleGroup_map_fixOf h2 (conjSp 2 K A) hZ hQ hc
        have hNc := card_map_fixOf_mul_two h2 (conjSp 2 K A) hZ
        rw [hcard] at hNc
        rw [← hEN] at hNs hNc
        have hLeq := hLE hNs
        exact ⟨hLeq ▸ hNs, Or.inr (Or.inl (hLeq ▸ hNc))⟩
      ·
        right
        have ha : (d : K) ≠ 0 := d.ne_zero
        have hA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
            formJ 2 K * ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
              (-(d : K)) • formJ 2 K := by
          rw [hμ, hdm, neg_neg]
        obtain ⟨g, hg⟩ := exists_frame_typeI h2 ha hA hAA
        have hGL : (A : GL (Fin 2 ⊕ Fin 2) K) * (g : GL (Fin 2 ⊕ Fin 2) K) =
            (g : GL (Fin 2 ⊕ Fin 2) K) * ((aIgsp ha : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) := by
          apply Units.ext
          rw [Units.val_mul, Units.val_mul, coe_aIgsp]
          exact hg
        set β := (MulAut.conj (proj 2 K g))⁻¹ with hβdef
        have hcomm : ∀ x, β (α x) = alphaI ha (β x) := fun x => by
          rw [hα']
          exact conj_inv_conjAut A (aIgsp ha) g hGL x
        have hEmap : E.map β.toMonoidHom = JI ha := by
          rw [hEdef, map_layerOf, map_fixOf_of_comm hcomm]
          exact layerOf_alphaI ha h2 h4
        have hEJ : (JI ha).map β.symm.toMonoidHom = E := by
          rw [← hEmap, Subgroup.map_map]
          convert Subgroup.map_id E
          ext x
          simp
        obtain ⟨hE', -⟩ := simple_data_map β.symm (isSimpleGroup_JI ha h4)
          (exists_mul_ne_of_isQuasisimple (isQuasisimple_JI ha h4))
        rw [hEJ] at hE'
        have hLeq := hLE hE'
        refine ⟨hLeq ▸ hE', Or.inl ?_⟩
        rw [hLeq, ← hEJ, card_map_equiv, card_JI hodd ha, hK, hhalf]
  ·
    right
    have hθα : ∀ g, α (proj 2 K g) = proj 2 K ((conjSp 2 K A * fieldSp 2 K σ) g) := fun g => by
      rw [hα]
      rfl
    obtain ⟨hQ, hcard⟩ := fixOf_conjSp_fieldSp hodd A σ hσ2 hσ d hd
    have hc := card_center_fixOf_field hodd A σ hσ2 hσ d hd
    have hZ : ∀ z ∈ spScalars 2 K, (conjSp 2 K A * fieldSp 2 K σ) z = z :=
      fun z hz => conjSp_fieldSp_scalar A σ hz
    obtain ⟨hKk, -⟩ := hfield hσ
    have hk : Nat.card {c : K // σ c = c} =
        Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun c =>
        (CatalogueBLinearTwoDescent.mem_fixedSubfield K σ c).symm)
    rw [hk, hK] at hKk
    set k := Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) with hkdef
    have hkodd : Odd k := (Nat.odd_mul.mp (by rw [← sq, ← hKk]; exact hK ▸ hodd)).1
    have hk3 : 3 ≤ k := by
      by_contra hlt
      push Not at hlt
      obtain ⟨r, hr⟩ := hkodd
      have hk1 : k = 1 := by omega
      have hq1 : p ^ f = 1 := by rw [hKk, hk1, one_pow]
      omega
    have h4dvd : 4 ∣ Nat.card (fixOf (conjSp 2 K A * fieldSp 2 K σ)) := by
      rw [hcard]
      have : 4 ∣ k ^ 2 - 1 := by
        obtain ⟨r, hr⟩ := hkodd
        refine ⟨r ^ 2 + r, ?_⟩
        rw [hr]
        have : (2 * r + 1) ^ 2 = 4 * (r ^ 2 + r) + 1 := by ring
        omega
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_right this _) _
    have hEN := layerOf_fixOf_eq h2 _ hθα hZ hQ h4dvd
    have hNs := isSimpleGroup_map_fixOf h2 _ hZ hQ hc
    have hNc := card_map_fixOf_mul_two h2 _ hZ
    rw [hcard] at hNc
    rw [← hEN] at hNs hNc
    have hLeq := hLE hNs
    exact ⟨hLeq ▸ hNs, Or.inr (Or.inr ⟨k, hKk.symm, hk3, hLeq ▸ hNc⟩)⟩

end Catalog7Std

end CFSG.ComponentClassification.GSThmB
