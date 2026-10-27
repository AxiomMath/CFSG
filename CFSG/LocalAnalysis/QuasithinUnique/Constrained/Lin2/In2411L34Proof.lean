module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2411L34D
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2411L34

public section

namespace CFSG.QuasithinUnique.Lin2.L34

open Matrix MatrixGroups CFSG.Open

variable {F : Type} [Field F]

section Cards

theorem factorization_20160 : (20160 : ℕ).factorization 2 = 6 := by
  have h : (20160 : ℕ) = 2 ^ 6 * 315 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]
  simp

theorem card_SL3 [Fintype F] (hcard : Fintype.card F = 4) : Nat.card SL(3, F) = 60480 := by
  rw [Matrix.card_SL_field 3]
  simp [Fin.prod_univ_three, hcard]

theorem card_center3 [Fintype F] (hcard : Fintype.card F = 4) :
    Nat.card (Subgroup.center SL(3, F)) = 3 := by
  classical
  have hF := F4.of_card hcard
  have e := (SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 3) (R := F))
  rw [Nat.card_congr e.toEquiv]
  have h3 : max (Fintype.card (Fin 3)) 1 = 3 := by simp
  rw [h3]
  have htop : rootsOfUnity 3 F = ⊤ := by
    rw [eq_top_iff]
    intro u _
    rw [mem_rootsOfUnity]
    ext
    simp
    exact hF.cube u.ne_zero
  rw [htop, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units, hcard]

theorem card_psl3 [Fintype F] (hcard : Fintype.card F = 4) :
    Nat.card (SL(3, F) ⧸ Subgroup.center SL(3, F)) = 20160 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(3, F))
  rw [card_SL3 hcard, card_center3 hcard] at h
  omega

theorem card_UT [Fintype F] (hcard : Fintype.card F = 4) :
    Nat.card (UT : Subgroup SL(3, F)) = 64 := by
  have e : (F × F × F) ≃ (UT : Subgroup SL(3, F)) :=
    Equiv.ofBijective (fun p => ⟨uT p.1 p.2.1 p.2.2, ⟨p.1, p.2.1, p.2.2, rfl⟩⟩)
      ⟨fun p q h => uT_injective (congrArg Subtype.val h), by
        rintro ⟨_, a, b, c, rfl⟩
        exact ⟨(a, b, c), rfl⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card, hcard]

theorem card_Xs [Fintype F] (hcard : Fintype.card F = 4) :
    Nat.card (Xs : Subgroup SL(3, F)) = 16 := by
  have e : (F × F) ≃ (Xs : Subgroup SL(3, F)) :=
    Equiv.ofBijective (fun p => ⟨uT p.1 0 p.2, ⟨p.1, p.2, rfl⟩⟩)
      ⟨fun p q h => by
        have := @uT_injective F _ (p.1, 0, p.2) (q.1, 0, q.2) (congrArg Subtype.val h)
        simpa [Prod.ext_iff] using this, by
        rintro ⟨_, a, c, rfl⟩
        exact ⟨(a, c), rfl⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_eq_fintype_card, hcard]

theorem card_Ys [Fintype F] (hcard : Fintype.card F = 4) :
    Nat.card (Ys : Subgroup SL(3, F)) = 16 := by
  have e : (F × F) ≃ (Ys : Subgroup SL(3, F)) :=
    Equiv.ofBijective (fun p => ⟨uT 0 p.1 p.2, ⟨p.1, p.2, rfl⟩⟩)
      ⟨fun p q h => by
        have := @uT_injective F _ (0, p.1, p.2) (0, q.1, q.2) (congrArg Subtype.val h)
        simpa [Prod.ext_iff] using this, by
        rintro ⟨_, b, c, rfl⟩
        exact ⟨(b, c), rfl⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_eq_fintype_card, hcard]

end Cards

section Sylow

theorem UT_inf_center : (UT : Subgroup SL(3, F)) ⊓ Subgroup.center SL(3, F) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨⟨a, b, c, rfl⟩, hz⟩
  obtain ⟨r, -, h00, h11, h22, h01, h02, h10, h12, h20, h21⟩ := center_entries hz
  simp [uT] at h01 h02 h12
  rw [Subgroup.mem_bot, h01, h02, h12, uT_one]

theorem pi_injOn {u v : SL(3, F)} (hu : u ∈ (UT : Subgroup SL(3, F)))
    (hv : v ∈ (UT : Subgroup SL(3, F)))
    (h : QuotientGroup.mk' (Subgroup.center SL(3, F)) u =
      QuotientGroup.mk' (Subgroup.center SL(3, F)) v) : u = v := by
  have h1 : u⁻¹ * v ∈ Subgroup.center SL(3, F) := (QuotientGroup.eq).1 h
  have h2 : u⁻¹ * v ∈ (UT : Subgroup SL(3, F)) := UT.mul_mem (UT.inv_mem hu) hv
  have h3 : u⁻¹ * v ∈ (UT : Subgroup SL(3, F)) ⊓ Subgroup.center SL(3, F) := ⟨h2, h1⟩
  rw [UT_inf_center, Subgroup.mem_bot] at h3
  exact inv_mul_eq_one.1 h3

@[expose] def Ubar (F : Type) [Field F] : Subgroup (SL(3, F) ⧸ Subgroup.center SL(3, F)) :=
  (UT : Subgroup SL(3, F)).map (QuotientGroup.mk' (Subgroup.center SL(3, F)))

theorem card_map_of_le_UT {A : Subgroup SL(3, F)} (hA : A ≤ UT) :
    Nat.card (A.map (QuotientGroup.mk' (Subgroup.center SL(3, F)))) = Nat.card A := by
  have hinj : Function.Injective ((QuotientGroup.mk' (Subgroup.center SL(3, F))).comp A.subtype) :=
    fun u v h => Subtype.ext (pi_injOn (hA u.2) (hA v.2) h)
  have hr : A.map (QuotientGroup.mk' (Subgroup.center SL(3, F))) =
      ((QuotientGroup.mk' (Subgroup.center SL(3, F))).comp A.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem card_Ubar [Fintype F] (hcard : Fintype.card F = 4) : Nat.card (Ubar F) = 64 := by
  unfold Ubar
  rw [card_map_of_le_UT le_rfl, card_UT hcard]

noncomputable def sylowUbar [Fintype F] (hcard : Fintype.card F = 4) :
    Sylow 2 (SL(3, F) ⧸ Subgroup.center SL(3, F)) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Sylow.ofCard (Ubar F) (by
    rw [card_Ubar hcard, card_psl3 hcard, factorization_20160]
    norm_num)

end Sylow

section Classify

theorem uT_inj {a b c a' b' c' : F} (h : uT a b c = uT a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  have := @uT_injective F _ (a, b, c) (a', b', c') h
  simpa [Prod.ext_iff] using this

variable [Fintype F]

theorem classify (hcard : Fintype.card F = 4)
    (E : Subgroup (SL(3, F) ⧸ Subgroup.center SL(3, F))) (hEU : E ≤ Ubar F)
    (hE : IsElemAbelian 2 E) (hEc : Nat.card E = 16) :
    E = (Xs : Subgroup SL(3, F)).map (QuotientGroup.mk' (Subgroup.center SL(3, F))) ∨
      E = (Ys : Subgroup SL(3, F)).map (QuotientGroup.mk' (Subgroup.center SL(3, F))) := by
  have hF := F4.of_card hcard
  set π := QuotientGroup.mk' (Subgroup.center SL(3, F)) with hπ
  set E0 : Subgroup SL(3, F) := (UT : Subgroup SL(3, F)) ⊓ E.comap π with hE0
  have hE0UT : E0 ≤ UT := inf_le_left
  have hmap : E0.map π = E := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact hu.2
    · intro y hy
      obtain ⟨u, hu, rfl⟩ := hEU hy
      exact ⟨u, ⟨hu, hy⟩, rfl⟩
  have hcard0 : Nat.card E0 = 16 := by
    rw [← card_map_of_le_UT hE0UT, hmap, hEc]
  have key : ∀ u ∈ E0, ∃ a b c, u = uT a b c ∧ a * b = 0 := by
    intro u hu
    obtain ⟨a, b, c, rfl⟩ := hu.1
    refine ⟨a, b, c, rfl, ?_⟩
    have h1 : π (uT a b c * uT a b c) = 1 := by
      rw [map_mul]
      have := hE.2 (π (uT a b c)) hu.2
      rwa [sq] at this
    have h2 : uT a b c * uT a b c ∈ Subgroup.center SL(3, F) := (QuotientGroup.eq_one_iff _).1 h1
    have h3 : uT a b c * uT a b c ∈ (UT : Subgroup SL(3, F)) ⊓ Subgroup.center SL(3, F) :=
      ⟨UT.mul_mem hu.1 hu.1, h2⟩
    rw [UT_inf_center, Subgroup.mem_bot, uT_mul, ← uT_one] at h3
    have h4 := @uT_injective F _ (a + a, b + b, c + c + a * b) (0, 0, 0) h3
    simp only [Prod.mk.injEq] at h4
    have h5 : c + c = 0 := hF.add_self c
    linear_combination h4.2.2 - h5
  have key2 : ∀ a b c a' b' c' : F, uT a b c ∈ E0 → uT a' b' c' ∈ E0 → a * b' = a' * b := by
    intro a b c a' b' c' hu hv
    have h1 : π (uT a b c) * π (uT a' b' c') = π (uT a' b' c') * π (uT a b c) :=
      IsElemAbelian.comm hE hu.2 hv.2
    rw [← map_mul, ← map_mul] at h1
    have h2 := pi_injOn (UT.mul_mem hu.1 hv.1) (UT.mul_mem hv.1 hu.1) h1
    rw [uT_mul, uT_mul] at h2
    have h3 := @uT_injective F _ (a + a', b + b', c + c' + a * b') (a' + a, b' + b, c' + c + a' * b) h2
    simp only [Prod.mk.injEq] at h3
    linear_combination h3.2.2
  by_cases hX : ∃ a b c, uT a b c ∈ E0 ∧ a ≠ 0
  · left
    obtain ⟨a₀, b₀, c₀, hu₀, ha₀⟩ := hX
    have hb₀ : b₀ = 0 := by
      obtain ⟨a, b, c, h, hab⟩ := key _ hu₀
      obtain ⟨rfl, rfl, rfl⟩ := uT_inj h
      rcases mul_eq_zero.1 hab with h0 | h0
      · exact absurd h0 ha₀
      · exact h0
    have hle : E0 ≤ (Xs : Subgroup SL(3, F)) := by
      intro v hv
      obtain ⟨a', b', c', rfl, -⟩ := key v hv
      have h1 := key2 a₀ b₀ c₀ a' b' c' hu₀ hv
      rw [hb₀, mul_zero] at h1
      have hb' : b' = 0 := by
        rcases mul_eq_zero.1 h1 with h0 | h0
        · exact absurd h0 ha₀
        · exact h0
      exact ⟨a', c', by rw [hb']⟩
    have heq : E0 = (Xs : Subgroup SL(3, F)) :=
      eq_of_le_of_card_le' hle (by rw [card_Xs hcard, hcard0])
    rw [← hmap, heq]
  · right
    push Not at hX
    have hle : E0 ≤ (Ys : Subgroup SL(3, F)) := by
      intro v hv
      obtain ⟨a', b', c', rfl, -⟩ := key v hv
      exact ⟨b', c', by rw [hX a' b' c' hv]⟩
    have heq : E0 = (Ys : Subgroup SL(3, F)) :=
      eq_of_le_of_card_le' hle (by rw [card_Ys hcard, hcard0])
    rw [← hmap, heq]

end Classify

section Assembly

theorem L34Props.of_equiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (h : L34Props Y') :
    L34Props Y := by
  refine ⟨?_, fun E hE hEc => ?_⟩
  · rw [Nat.card_congr e.toEquiv]
    exact h.1
  · apply NormProps.of_map e
    have hE' : IsElemAbelian 2 (E.map e.toMonoidHom) := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
      · obtain ⟨a', ha', ha⟩ := a.2
        obtain ⟨b', hb', hb⟩ := b.2
        apply Subtype.ext
        show (a : Y') * b = b * a
        rw [← ha, ← hb]
        have := IsElemAbelian.comm hE ha' hb'
        simpa using congrArg e this
      · rintro _ ⟨x, hx, rfl⟩
        have := hE.2 x hx
        simpa using congrArg e this
    have hc' : Nat.card (E.map e.toMonoidHom) = 16 := by
      rw [← hEc]
      exact Subgroup.card_map_of_injective e.injective
    exact h.2 _ hE' hc'

theorem l34Props_psl [Fintype F] (hcard : Fintype.card F = 4) :
    L34Props (SL(3, F) ⧸ Subgroup.center SL(3, F)) := by
  refine ⟨card_psl3 hcard, ?_⟩
  refine normProps_of_sylow (sylowUbar hcard) (fun E hEU hE hEc => ?_)
  rcases classify hcard E hEU hE hEc with rfl | rfl
  · exact normProps_Xs hcard
  · exact normProps_Ys hcard

theorem l34Fact : L34Fact := by
  intro Y _ _ hY
  obtain ⟨-, F, hField, hFin, hcardF, ⟨e⟩⟩ := hY
  have := Fintype.ofFinite F
  have hc : Fintype.card F = 4 := by
    rw [← Nat.card_eq_fintype_card, hcardF]
    norm_num
  have e' : Y ≃* SL(3, F) ⧸ Subgroup.center SL(3, F) :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm
  exact L34Props.of_equiv e' (l34Props_psl hc)

end Assembly

end CFSG.QuasithinUnique.Lin2.L34
