module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerH
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81Aut

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

namespace NoNilp

theorem not_hasNormalPComplement {G : Type*} [Group G] [Finite G] {F X : Subgroup G}
    (hXF : X ≤ F) (hX : ⁅X, X⁆ = X) (heven : 2 ∣ Nat.card X) : ¬ HasNormalPComplement 2 ↥F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨N, hN, hcop, hq⟩
  set X' := X.subgroupOf F with hX'
  have hmap : X'.map F.subtype = X := map_subgroupOf_eq_of_le hXF
  have hX'p : ⁅X', X'⁆ = X' := by
    apply map_injective F.subtype_injective
    rw [Subgroup.map_commutator, hmap, hX]
  set Y := X'.map (QuotientGroup.mk' N) with hY
  have hYp : ⁅Y, Y⁆ = Y := by rw [hY, ← Subgroup.map_commutator, hX'p]
  have : Group.IsNilpotent (↥F ⧸ N) := hq.isNilpotent
  have hle : ∀ n, Y ≤ derivedSeries (↥F ⧸ N) n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ, ← hYp]
      exact commutator_mono ih ih
  obtain ⟨n, hn⟩ := (Group.isSolvable_def (↥F ⧸ N)).mp inferInstance
  have hYbot : Y = ⊥ := le_bot_iff.mp (hn ▸ hle n)
  have hX'N : X' ≤ N := by
    intro x hx
    have h1 : QuotientGroup.mk' N x ∈ Y := mem_map_of_mem _ hx
    rw [hYbot, mem_bot] at h1
    exact (QuotientGroup.eq_one_iff x).mp h1
  have hcard : Nat.card X' = Nat.card X := by
    rw [hX', Nat.card_congr (subgroupOfEquivOfLe hXF).toEquiv]
  have h2 : 2 ∣ Nat.card N := (hcard ▸ heven).trans (Subgroup.card_dvd_of_le hX'N)
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop h2

theorem map_perfect {G G' : Type*} [Group G] [Group G'] (φ : G →* G') {X : Subgroup G}
    (hX : ⁅X, X⁆ = X) : ⁅X.map φ, X.map φ⁆ = X.map φ := by
  rw [← Subgroup.map_commutator, hX]

theorem commutator_self {G : Type*} [Group G] {L : Subgroup G} (hL : Group.IsPerfect L) :
    ⁅L, L⁆ = L := by
  have h := congrArg (Subgroup.map L.subtype) hL.commutator_eq_top
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

open CatFactsSp4 Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag

variable {K : Type} [Field K]

theorem four_dvd_sq_sub_one {k : ℕ} (hk : Odd k) : 4 ∣ k ^ 2 - 1 := by
  obtain ⟨r, hr⟩ := hk
  refine ⟨r ^ 2 + r, ?_⟩
  rw [hr]
  have : (2 * r + 1) ^ 2 = 4 * (r ^ 2 + r) + 1 := by ring
  omega

theorem exists_perfect_even {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) (hs : IsSimpleGroup (StatedProj (StatedSp 2 K)))
    (α : MulAut (StatedProj (StatedSp 2 K))) (hα2 : α * α = 1) :
    ∃ X : Subgroup (StatedProj (StatedSp 2 K)), X ≤ fixOf α ∧ ⁅X, X⁆ = X ∧ 2 ∣ Nat.card X := by
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have h2 := two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card K := by omega
  have hchar : ringChar K ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := K)
    rw [h] at this
    exact_mod_cast this
  have hmove : ∀ (β α₀ : MulAut (StatedProj (StatedSp 2 K))), (∀ x, β (α x) = α₀ (β x)) →
      ∀ X₀ : Subgroup (StatedProj (StatedSp 2 K)), X₀ ≤ fixOf α₀ → ⁅X₀, X₀⁆ = X₀ →
        2 ∣ Nat.card X₀ →
        ∃ X : Subgroup (StatedProj (StatedSp 2 K)), X ≤ fixOf α ∧ ⁅X, X⁆ = X ∧
          2 ∣ Nat.card X := by
    intro β α₀ hcomm X₀ hX₀ hp₀ he₀
    refine ⟨X₀.map β.symm.toMonoidHom, ?_, map_perfect _ hp₀, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      have h1 := hX₀ hx
      rw [mem_fixOf] at h1 ⊢
      apply β.injective
      change β (α (β.symm x)) = β (β.symm x)
      rw [hcomm, MulEquiv.apply_symm_apply, h1]
    · rwa [card_map_of_injective β.symm.injective]
  by_cases hα1 : α = 1
  ·
    subst hα1
    refine ⟨E1 K, by rw [fixOf_one]; exact le_top, commutator_self (isQuasisimple_E1 h2 h4).1, ?_⟩
    exact even_iff_two_dvd.mp (even_card_of_mem u1_mem_E1
      (orderOf_eq_prime (by rw [pow_two]; exact u1_mul_u1) (u1_ne_one h2)))
  obtain ⟨A, σ, hα, hσ2, ⟨d, hd⟩, hlin, hfield⟩ :=
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
      rcases hg with h | h <;> rw [hφu, h] at hcomm
      ·
        refine hmove φ _ hcomm (E1 K) (by rw [fixOf_conj]; exact E1_le_centralizer_u1 h2)
          (commutator_self (isQuasisimple_E1 h2 h4).1) ?_
        exact even_iff_two_dvd.mp (even_card_of_mem u1_mem_E1
          (orderOf_eq_prime (by rw [pow_two]; exact u1_mul_u1) (u1_ne_one h2)))
      ·
        exact hmove φ _ hcomm (Lsub K) (by rw [fixOf_conj]; exact Lsub_le_centralizer)
          (commutator_self (isQuasisimple_Lsub h4).1)
          (even_iff_two_dvd.mp (even_card_of_mem w0_mem_Lsub orderOf_w0))
    · push Not at hsq
      rcases eq_or_eq_neg_multiplier A hAA with hdm | hdm
      ·
        have hdsq : ∀ l : K, l ^ 2 ≠ (d : K) := by rw [hdm]; exact hsq
        have hμd : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
            formJ 2 K * ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
              (d : K) • formJ 2 K := by rw [hdm]; exact hμ
        obtain ⟨hQ, hcard⟩ := fixOf_conjSp_nonsquare hp hp2 hf hK A d.ne_zero hdsq hAA hμd
        have hθα : ∀ g, α (proj 2 K g) = proj 2 K (conjSp 2 K A g) := fun g => by
          rw [hα', conjAut_proj]
        have hZ : ∀ z ∈ spScalars 2 K, conjSp 2 K A z = z := fun z hz => conjSp_scalar A hz
        refine ⟨_, map_fixOf_le _ hθα, map_perfect _ (commutator_self hQ.1), ?_⟩
        have hNc := card_map_fixOf_mul_two h2 (conjSp 2 K A) hZ
        rw [hcard] at hNc
        have h4' : 4 ∣ ((p ^ f) ^ 2) ^ 2 - 1 :=
          four_dvd_sq_sub_one ((hK ▸ hodd : Odd (p ^ f)).pow)
        obtain ⟨m, hm⟩ := h4'
        exact ⟨(p ^ f) ^ 2 * m, by rw [hm] at hNc; nlinarith⟩
      ·
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
        have hJmem : proj 2 K (gI ha J₁SL) ∈ JI ha := ⟨_, ⟨J₁SL, rfl⟩, rfl⟩
        exact hmove β _ hcomm (JI ha) (JI_le_fix ha) (commutator_self (isQuasisimple_JI ha h4).1)
          (even_iff_two_dvd.mp (even_card_of_mem hJmem
            (orderOf_proj_J₁SL (gI ha) (ker_proj_comp_gI ha))))
  ·
    have hθα : ∀ g, α (proj 2 K g) = proj 2 K ((conjSp 2 K A * fieldSp 2 K σ) g) := fun g => by
      rw [hα]
      rfl
    obtain ⟨hQ, hcard⟩ := fixOf_conjSp_fieldSp hodd A σ hσ2 hσ d hd
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
    refine ⟨_, map_fixOf_le _ hθα, map_perfect _ (commutator_self hQ.1), ?_⟩
    have hNc := card_map_fixOf_mul_two h2 _ hZ
    rw [hcard] at hNc
    obtain ⟨m, hm⟩ := four_dvd_sq_sub_one hkodd
    refine ⟨k ^ 4 * (m * (k ^ 4 - 1)), ?_⟩
    rw [hm] at hNc
    nlinarith

theorem noNilp_psp {K₀ : Type} [Group K₀] [Finite K₀] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f) (hK₀ : Blueprint.LieModel K₀ .PSp 2 p f) (α : MulAut K₀)
    (hα2 : α * α = 1) : ¬ HasNormalPComplement 2 ↥(fixSub α) := by
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := GH74.Generic.lieModel_psp_data hK₀
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have h4 : 4 ≤ Nat.card K := by omega
  have hs : IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
      (Or.inl (Or.inr h4))
  set α' : MulAut (StatedProj (StatedSp 2 K)) := e.symm.trans (α.trans e) with hα'def
  have hcomm : ∀ x, e (α x) = α' (e x) := fun x => by
    simp only [hα'def, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hα'2 : α' * α' = 1 := by
    ext x
    have := congrArg (fun φ : MulAut K₀ => φ (e.symm x)) hα2
    simp only [MulAut.mul_apply, MulAut.one_apply] at this
    simp only [hα'def, MulAut.mul_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulAut.one_apply, this, MulEquiv.apply_symm_apply]
  obtain ⟨X', hX'F, hX'p, hX'e⟩ := exists_perfect_even hp hp2 hf hK h5 hs α' hα'2
  have hfixmap := map_fixOf_of_comm hcomm
  refine not_hasNormalPComplement (X := X'.map e.symm.toMonoidHom) ?_ (map_perfect _ hX'p)
    (by rwa [card_map_of_injective e.symm.injective])
  rintro _ ⟨x, hx, rfl⟩
  have h1 := hX'F hx
  rw [← hfixmap] at h1
  obtain ⟨y, hy, rfl⟩ := h1
  change α (e.symm (e y)) = e.symm (e y)
  rw [MulEquiv.symm_apply_apply]
  exact hy

end NoNilp

open NoNilp in
theorem cf81NoNilp :
    CF81NoNilp := by
  intro K₀ _ _ p f hp hp2 hf hK α hα2
  by_cases h5 : 5 ≤ p ^ f
  · rcases hK with hK | ⟨rfl, rfl, -⟩
    · exact noNilp_psp hp hp2 hf h5 hK α hα2
    · norm_num at h5
  ·
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hf1 : f = 1 := by
      by_contra hf1
      have : p ^ 2 ≤ p ^ f := Nat.pow_le_pow_right hp.pos (by omega)
      nlinarith
    subst hf1
    have hp3' : p = 3 := by
      rw [pow_one] at h5
      interval_cases p
      · rfl
      · exact absurd hp (by norm_num)
    subst hp3'
    have hK' : IsSec8Socle K₀ 3 1 := hK
    rintro ⟨N, hN, hcop, hq⟩
    have hfeq : fixSub α = Eight.fixSubgroup α := by
      ext x
      rfl
    apply CatFactsSmall.cfQ3NoNilp K₀ hK' α hα2
    refine ⟨N.map (fixSub α).subtype, hfeq ▸ map_subtype_le _, ?_, ?_, ?_⟩
    · have h1 : (N.map (fixSub α).subtype).subgroupOf (fixSub α) = N :=
        comap_map_eq_self_of_injective (fixSub α).subtype_injective N
      rw [← hfeq, h1]
      exact hN
    · rw [card_map_of_injective (fixSub α).subtype_injective]
      exact (Nat.coprime_two_left.mp hcop)
    · intro y hy
      have hy' : y ∈ fixSub α := hfeq ▸ hy
      obtain ⟨k, hk⟩ := hq (QuotientGroup.mk' N ⟨y, hy'⟩)
      refine ⟨k, ⟨⟨y, hy'⟩ ^ 2 ^ k, ?_, rfl⟩⟩
      rw [← map_pow] at hk
      exact (QuotientGroup.eq_one_iff _).mp hk

end CFSG.ComponentClassification.GSThmB
