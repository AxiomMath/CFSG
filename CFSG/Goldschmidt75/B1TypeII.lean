module

public import CFSG.Goldschmidt75.B1TypeI
public import CFSG.Goldschmidt.Steps.G3b35JR

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt CFSG.Walter CFSG.GorensteinWalter Subgroup
open scoped MatrixGroups

variable {Q : Type} [Group Q]

theorem action_eq_one_of_comm {Λ : Type} [Group Λ] [Group.IsPerfect Λ] (Φ : Λ →* MulAut Q)
    (hcomm : ∀ l l', Φ l * Φ l' = Φ l' * Φ l) (l : Λ) : Φ l = 1 := by
  have : IsMulCommutative Φ.range := ⟨⟨by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    exact Subtype.ext (hcomm a b)⟩⟩
  have : Group.IsPerfect Φ.range := Group.IsPerfect.range Φ
  have h := Subsingleton.elim (⟨Φ l, l, rfl⟩ : Φ.range) 1
  exact congrArg Subtype.val h

theorem action_eq_one_L2
    {Λ : Type} [Group Λ] [Group.IsPerfect Λ] [Finite Q]
    (hL : IsTypeL2Odd Q) (T : Sylow 2 Q) (Φ : Λ →* MulAut Q)
    (hfix : ∀ l, ∀ x ∈ Omega1 (T : Subgroup Q), Φ l x = x) (l : Λ) : Φ l = 1 := by
  obtain ⟨p, f, hp, hpodd, hf, h5, h8, ⟨e⟩⟩ := hL
  have : IsKleinFour (T : Subgroup Q) := G3b.sylow_isKleinFour_of_mulEquiv e hpodd hf h8 T
  have hfixT : ∀ l', ∀ x ∈ (T : Subgroup Q), Φ l' x = x := by
    intro l' x hx
    refine hfix l' x (subset_closure ⟨hx, ?_⟩)
    have h := IsKleinFour.mul_self (⟨x, hx⟩ : (T : Subgroup Q))
    rw [pow_two]
    exact congrArg Subtype.val h
  exact action_eq_one_of_comm Φ (fun a b =>
    (G3b.mulAut_fix_props_of_mulEquiv e hpodd hf h5 h8 T).1 _ _ (hfixT a) (hfixT b)) l

theorem action_eq_one_JR
    {Λ : Type} [Group Λ] [Finite Λ] [Group.IsPerfect Λ] [Finite Q]
    (hJR : IsTypeJR Q) (hnonab : ∃ a b : Q, a * b ≠ b * a) (T : Sylow 2 Q) (Φ : Λ →* MulAut Q)
    (hfix : ∀ l, ∀ x ∈ Omega1 (T : Subgroup Q), Φ l x = x) (l : Λ) : Φ l = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup Q := hJR.1
  have h2 : 2 ∣ Nat.card Q := hJR.two_dvd_card hnonab
  obtain ⟨hTel, hTcard⟩ := hJR.sylow_two h2 T
  have hfixT : ∀ l', ∀ x ∈ (T : Subgroup Q), Φ l' x = x := fun l' x hx =>
    hfix l' x (subset_closure ⟨hx, CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩)
  obtain ⟨t0, ht0⟩ := exists_prime_orderOf_dvd_card' (G := (T : Subgroup Q)) 2
    (by rw [hTcard]; norm_num)
  have ht2 : orderOf (t0 : Q) = 2 := by rw [Subgroup.orderOf_coe]; exact ht0
  have htT : (t0 : Q) ∈ (T : Subgroup Q) := t0.2
  obtain ⟨-, p, f, hpf, E, hpodd, hf, h5, hEC, hEn, ⟨eE⟩, hCE⟩ := hJR.2.2 (t0 : Q) ht2
  have h8 := hJR.mod_eight ht2 E hpodd hf h5 hEC hEn eE hCE
  obtain ⟨hVcard, -, -, -⟩ := hJR.sylow_two_of_mem T htT ht2 E hpodd hf h5 hEC hEn eE hCE
  have hE4 : 4 ≤ Nat.card (GaloisField p f) := by rw [GaloisField.card p f hf.ne']; omega
  have : IsSimpleGroup PSL(2, GaloisField p f) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hE4
  have : IsSimpleGroup E := eE.isSimpleGroup
  have hE3 : 2 < Nat.card E := by
    rw [Nat.card_congr eE.toEquiv, psl2_card_formula _
      (isOddPrimePower_of_card (GaloisField.card p f hf.ne') hpodd hf),
      GaloisField.card p f hf.ne']
    have h1 : 24 ≤ (p ^ f) ^ 2 - 1 := by
      have : 25 ≤ (p ^ f) ^ 2 := by nlinarith
      omega
    have h2 : 120 ≤ p ^ f * ((p ^ f) ^ 2 - 1) := by nlinarith
    omega
  set V := (T : Subgroup Q) ⊓ E with hV
  have hVE : V ≤ E := inf_le_right
  have hVEp : IsPGroup 2 (V.subgroupOf E) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVE).toEquiv, hVcard]
    norm_num
  obtain ⟨P0, hP0⟩ := hVEp.exists_le_sylow
  have hP0K := G3b.sylow_isKleinFour_of_mulEquiv eE hpodd hf h8 P0
  have hP0eq : (P0 : Subgroup E) = V.subgroupOf E := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hP0
    rw [hP0K.card_four, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVE).toEquiv, hVcard]
  obtain ⟨hcommE, -, -⟩ := G3b.mulAut_fix_props_of_mulEquiv eE hpodd hf h5 h8 P0
  have hEinv : ∀ β ∈ Φ.range, ∀ x ∈ E, β x ∈ E := by
    rintro _ ⟨l', rfl⟩ x hx
    exact G3b.mem_of_fix_of_mem ht2 hEn hEC hCE hE3 (Φ l') (hfixT l' _ htT) x hx
  set R : Λ →* MulAut E := (G3b.restrictAut E Φ.range hEinv).comp Φ.rangeRestrict with hR
  have hRapp : ∀ l' (x : E), ((R l' x : E) : Q) = Φ l' x := fun _ _ => rfl
  have hRfix : ∀ l', ∀ x ∈ (P0 : Subgroup E), R l' x = x := by
    intro l' x hx
    apply Subtype.ext
    rw [hRapp]
    rw [hP0eq, Subgroup.mem_subgroupOf] at hx
    exact hfixT l' x (Subgroup.mem_inf.mp hx).1
  have hR1 := action_eq_one_of_comm R (fun a b => hcommE _ _ (hRfix a) (hRfix b))
  have hΦE : ∀ l', ∀ x ∈ E, Φ l' x = x := by
    intro l' x hx
    have h := hRapp l' ⟨x, hx⟩
    rw [hR1 l'] at h
    exact h.symm
  have hodd1 : ∀ l', Odd (orderOf (Φ l')) → Φ l' = 1 := by
    intro l' hodd
    have hfixC := G3b.fix_centralizer_of_fix ht2 hEn hEC hCE (Φ l') hodd (hfixT l' _ htT)
      (hΦE l')
    exact hJR.mulAut_eq_one (Φ l') hodd ht2 hfixC
  have : Finite Φ.range := Finite.of_surjective Φ.rangeRestrict Φ.rangeRestrict_surjective
  have hW2 : IsPGroup 2 Φ.range := by
    rintro ⟨_, l', rfl⟩
    refine ⟨Nat.card Λ, Subtype.ext ?_⟩
    have hpos : 0 < orderOf (Φ l') := Nat.pos_of_dvd_of_pos (orderOf_map_dvd Φ l') (orderOf_pos l')
    have hle : orderOf (Φ l') ≤ Nat.card Λ :=
      (Nat.le_of_dvd (orderOf_pos l') (orderOf_map_dvd Φ l')).trans (G3b.orderOf_le_natCard l')
    have h := hodd1 (l' ^ 2 ^ Nat.card Λ) (by
      rw [map_pow]
      exact G3b.odd_orderOf_pow_two_pow hpos hle)
    rw [map_pow] at h
    simpa using h
  have : Group.IsNilpotent Φ.range := hW2.isNilpotent
  have hsol : Group.IsSolvable Φ.range := inferInstance
  have : Group.IsPerfect Φ.range := Group.IsPerfect.range Φ
  have hbot : Subsingleton Φ.range := by
    by_contra hne
    rw [not_subsingleton_iff_nontrivial] at hne
    exact Group.IsPerfect.not_isSolvable Φ.range hsol
  exact congrArg Subtype.val (Subsingleton.elim (⟨Φ l, l, rfl⟩ : Φ.range) 1)

theorem action_eq_one_of_type
    {Λ : Type} [Group Λ] [Finite Λ] [Group.IsPerfect Λ] [Finite Q]
    [IsSimpleGroup Q] (hZ : center Q = ⊥) (htype : IsGoldTypeI Q ∨ IsTypeL2Odd Q ∨ IsTypeJR Q)
    (T : Sylow 2 Q) (Φ : Λ →* MulAut Q)
    (hfix : ∀ l, ∀ x ∈ Omega1 (T : Subgroup Q), Φ l x = x) (l : Λ) : Φ l = 1 := by
  rcases htype with hI | hL | hJR
  · exact action_eq_one_typeI hZ hI T Φ hfix l
  · exact action_eq_one_L2 hL T Φ hfix l
  · refine action_eq_one_JR hJR ?_ T Φ hfix l
    obtain ⟨x, hx⟩ := exists_ne (1 : Q)
    by_contra h
    have hxZ : x ∈ center Q := mem_center_iff.mpr fun g => by
      by_contra hne
      exact h ⟨g, x, hne⟩
    rw [hZ, mem_bot] at hxZ
    exact hx hxZ

end CFSG.Goldschmidt75
