module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathLocal4

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

section Finite

variable {H : Type*} [Group H] [Finite H] {R M V W F : Subgroup H} {r : ℕ} {I : Fin r → Subgroup H}
  {Pm : Subgroup (Equiv.Perm (Fin r))} (h : WreathHyp R M V W F I Pm)

namespace WreathHyp

include h

omit [Finite H] in
theorem exists_moved_eElt {t : ∀ i, MulAut ↥(planesIn W I i)} (ht : h.IsT0 t) (i : Fin r) :
    ∃ z : ↥W, z ∈ planesIn W I i ∧ h.eElt t i z ≠ z := by
  let _ := h.cg
  have h1 := (ht.invol i (Finset.mem_univ i)).1
  obtain ⟨y, hy⟩ : ∃ y : ↥(planesIn W I i), t i y ≠ y := by
    by_contra hcon
    push Not at hcon
    exact h1 (MulEquiv.ext hcon)
  refine ⟨y, y.2, ?_⟩
  rw [h.eElt_apply_self i y.2]
  intro hc
  exact hy (Subtype.ext hc)

theorem commutator_J_I_ne_bot (i : Fin r) : ⁅thompsonJ R, I i⁆ ≠ ⊥ := by
  let _ := h.cg
  obtain ⟨t, ht⟩ := h.exists_t
  have he : h.eElt t i ∈ (thompsonJ R).map h.rho := by
    rw [h.rho_J_eq_T0 ht]
    exact h.eElt_mem_T0 ht i
  obtain ⟨j, hj, hje⟩ := he
  obtain ⟨z, hz, hzne⟩ := h.exists_moved_eElt ht i
  intro hbot
  have hcomm : ⁅j, ((z : ↥W) : H)⁆ ∈ ⁅thompsonJ R, I i⁆ :=
    Subgroup.commutator_mem_commutator hj hz
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hcomm
  apply hzne
  rw [← hje]
  apply Subtype.ext
  rw [h.rho_apply]
  calc j * (z : H) * j⁻¹ = (z : H) * j * j⁻¹ := by rw [hcomm]
    _ = z := by group

variable {h} {i : Fin r} {P : Subgroup H} (hP : h.IsSelected i P)

include hP

theorem IsSelected.exists_odd_acting :
    ∃ p ∈ oddOrderSubgroup P, h.rho p ∈ h.Dat i ∧ ∃ x ∈ planesIn W I i, h.rho p x ≠ x := by
  let _ := h.cg
  obtain ⟨d, hd, hnt⟩ := exists_cubeAt_nontrivial h.planeFamily i
  have hdP : d ∈ P.map h.rho := hP.Dat_le_map hd
  have hd3 : d ^ 3 = 1 :=
    pow_three_of_mem_cubeBase h.planeFamily (cubeAt_le_cubeBase h.planeFamily i hd)
  have hd1 : d ≠ 1 := by
    obtain ⟨x, -, hx⟩ := hnt
    intro h1
    exact hx (by rw [h1]; rfl)
  have hodd : Odd (orderOf d) := by
    rw [orderOf_eq_prime hd3 hd1]
    decide
  obtain ⟨p, hp, hpd⟩ := mem_map_oddOrderSubgroup h.rho P hdP hodd
  obtain ⟨x, hx, hxne⟩ := hnt
  exact ⟨p, hp, hpd ▸ hd, x, hx, by rwa [hpd]⟩

theorem IsSelected.centralizer_I_odd :
    I i ⊓ Subgroup.centralizer ((oddOrderSubgroup P : Subgroup H) : Set H) = ⊥ := by
  let _ := h.cg
  obtain ⟨p, hp, hpD, x0, hx0, hx0ne⟩ := hP.exists_odd_acting
  rw [eq_bot_iff]
  rintro u ⟨huI, huC⟩
  have hc : p * u = u * p := Subgroup.mem_centralizer_iff.mp huC p hp
  have hfix : h.rho p ⟨u, h.I_le i huI⟩ = ⟨u, h.I_le i huI⟩ := by
    apply Subtype.ext
    rw [h.rho_apply]
    show p * u * p⁻¹ = u
    rw [hc]
    group
  have := cubeAt_fixed h.planeFamily hpD ⟨x0, hx0, hx0ne⟩ (x := ⟨u, h.I_le i huI⟩) huI hfix
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

theorem IsSelected.exists_rep :
    ∃ (ρ' : ↥P →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (ψ : ↥(I i) ≃* V4'),
      Function.Surjective ρ' ∧
      (∀ (p : ↥P) (u u' : ↥(I i)), (u' : H) = (p : H) * (u : H) * (p : H)⁻¹ →
        Multiplicative.toAdd (ψ u') =
          (ρ' p : Matrix (Fin 2) (Fin 2) (ZMod 2)).mulVec (Multiplicative.toAdd (ψ u))) ∧
      (∀ p : ↥P, ρ' p = 1 ↔ ∀ u : ↥(I i), (p : H) * u = u * p) ∧
      Nat.card ↥(((oddOrderSubgroup P).subgroupOf P).map ρ') = 3 := by
  have := h.isKleinFour_I i
  obtain ⟨ρ', ψ, hequiv, hker, hsurj⟩ :=
    exists_natural_rep (P := P) (U := I i) (hP.le_normalizer_I i)
  refine ⟨ρ', ψ, hsurj.mpr hP.exists_induce, hequiv, hker, ?_⟩
  obtain ⟨A, hA3, hA⟩ := exists_sl2_cube
  have hle : ((oddOrderSubgroup P).subgroupOf P).map ρ' ≤ A := by
    rw [Subgroup.map_le_iff_le_comap, ← oddOrderSubgroup_top_eq_subgroupOf]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact hA _ (sl2_pow_three_of_odd _ (Odd.of_dvd_nat hx.2 (orderOf_map_dvd ρ' x)))
  have hne : ((oddOrderSubgroup P).subgroupOf P).map ρ' ≠ ⊥ := by
    let _ := h.cg
    obtain ⟨p, hp, hpD, x0, hx0, hx0ne⟩ := hP.exists_odd_acting
    intro hbot
    have hmem : ρ' ⟨p, oddOrderSubgroup_le P hp⟩ ∈
        ((oddOrderSubgroup P).subgroupOf P).map ρ' := ⟨⟨p, oddOrderSubgroup_le P hp⟩, hp, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have hc := (hker _).mp hmem ⟨(x0 : H), hx0⟩
    apply hx0ne
    apply Subtype.ext
    rw [h.rho_apply]
    show p * (x0 : H) * p⁻¹ = x0
    have hc' : p * (x0 : H) = (x0 : H) * p := hc
    rw [hc']
    group
  have hdvd : Nat.card ↥(((oddOrderSubgroup P).subgroupOf P).map ρ') ∣ 3 := by
    rw [← hA3]
    exact Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact absurd (Subgroup.card_eq_one.mp h1) hne
  · exact h3

theorem IsSelected.isTwoReduced : IsTwoReducedIn P (I i) := by
  refine ⟨hP.I_le_P i, hP.le_normalizer_I i, h.isElemAbelian_I i, ?_⟩
  intro D hDP hDn hDpow
  obtain ⟨ρ', ψ, hsurj, -, hker, -⟩ := hP.exists_rep
  have hDnorm : (D.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDP).mpr hDn
  have hDb : ((D.subgroupOf P).map ρ').Normal := hDnorm.map ρ' hsurj
  have hp : IsPGroup 2 ↥((D.subgroupOf P).map ρ') := by
    rintro ⟨g, q, hq, rfl⟩
    obtain ⟨k, hk⟩ := hDpow (q : H) hq
    refine ⟨k, Subtype.ext ?_⟩
    show ρ' q ^ 2 ^ k = 1
    rw [← map_pow]
    refine (hker _).mpr fun u => ?_
    have := Subgroup.mem_centralizer_iff.mp hk (u : H) u.2
    exact this.symm
  have hbot := sl2_normal_two_eq_bot _ hp
  intro d hd
  have h1 : ρ' ⟨d, hDP hd⟩ = 1 := by
    have : ρ' ⟨d, hDP hd⟩ ∈ (D.subgroupOf P).map ρ' := ⟨⟨d, hDP hd⟩, hd, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact ((hker _).mp h1 ⟨u, hu⟩).symm

theorem IsSelected.a3SelHyp (hchar : CharTwo (⊤ : Subgroup H)) (hnoChar : NoCharNormal R ⊤) :
    A3SelHyp (⊤ : Subgroup H) R (oddOrderSubgroup (⊤ : Subgroup H)) (elemBaumannIn 2 R) P := by
  obtain ⟨t, hTC⟩ := internal_S3_wreath_transfer h
  exact
    { T_sylow := h.sylow
      N_le := le_top
      N_norm := normal_le_normalizer' oddOrderSubgroup_top_normal ⊤
      X_eq := h.odd_sup_R
      N_noTwo := hasNoTwoQuotient_oddOrderSubgroup ⊤
      R_le_T := elemBaumannIn_le 2 R
      T_norm_R := le_normalizer_elemBaumannIn R
      R_sylow := hTC.syl_S
      charTwo := h.charTwo_NS hchar
      R_le_P := hP.S_le
      P_le := hP.P_le_NS
      X_eq_P := hP.sup_R
      R_not_normal := hP.not_le_normalizer
      max := ⟨P ⊓ M, le_inf hP.S_le h.S_le_M, hP.PM_lt, hP.max⟩
      noChar := hP.noChar_P hnoChar }

end WreathHyp

structure FactorLocalConclusion {H : Type*} [Group H] {R M V W F : Subgroup H} {r : ℕ}
    {I : Fin r → Subgroup H} {Pm : Subgroup (Equiv.Perm (Fin r))}
    (h : WreathHyp R M V W F I Pm) (i : Fin r) (P : Subgroup H) : Prop where
  S_norm_Y : elemBaumannIn 2 R ≤ Subgroup.normalizer ((h.Yi i : Subgroup H) : Set H)
  Y_le_N : h.Yi i ≤ oddOrderSubgroup (⊤ : Subgroup H)
  Y_not_le_M : ¬ h.Yi i ≤ M
  P_le : P ≤ h.Yi i ⊔ elemBaumannIn 2 R
  S_lt_P : elemBaumannIn 2 R < P
  P_not_le_M : ¬ P ≤ M
  sylow : IsSylowTwoOf (elemBaumannIn 2 R) P
  S_not_normal : ¬ ((elemBaumannIn 2 R).subgroupOf P).Normal
  PM_max : elemBaumannIn 2 R ≤ P ⊓ M ∧ P ⊓ M < P ∧
    ∀ Y : Subgroup H, elemBaumannIn 2 R ≤ Y → Y < P → Y ≤ P ⊓ M
  H_eq : P ⊔ R = ⊤
  noChar : NoCharNormal (elemBaumannIn 2 R) P
  NS_normal : (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R).Normal
  charTwo_NS : CharTwo (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)
  charTwo_P : CharTwo P
  Q0_le_S : blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ≤ elemBaumannIn 2 R
  rho_P : P.map h.rho = h.Dat i ⊔ h.T0
  I_le_S : I i ≤ elemBaumannIn 2 R
  reduced : IsTwoReducedIn P (I i)
  rep : ∃ (ρ' : ↥P →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (ψ : ↥(I i) ≃* V4'),
    Function.Surjective ρ' ∧
    (∀ (p : ↥P) (u u' : ↥(I i)), (u' : H) = (p : H) * (u : H) * (p : H)⁻¹ →
      Multiplicative.toAdd (ψ u') =
        (ρ' p : Matrix (Fin 2) (Fin 2) (ZMod 2)).mulVec (Multiplicative.toAdd (ψ u))) ∧
    (∀ p : ↥P, ρ' p = 1 ↔ ∀ u : ↥(I i), (p : H) * u = u * p) ∧
    Nat.card ↥(((oddOrderSubgroup P).subgroupOf P).map ρ') = 3 ∧
    ψ.toMonoidHom.ker =
      (Subgroup.centralizer ((oddOrderSubgroup P : Subgroup H) : Set H)).subgroupOf (I i)
  C_trivial : I i ⊓ Subgroup.centralizer ((oddOrderSubgroup P : Subgroup H) : Set H) = ⊥
  J_nontrivial : ⁅thompsonJ (elemBaumannIn 2 R), I i⁆ ≠ ⊥
  campbell : A3SelHyp (⊤ : Subgroup H) R (oddOrderSubgroup (⊤ : Subgroup H))
    (elemBaumannIn 2 R) P

namespace WreathHyp

variable {h} {i : Fin r} {P : Subgroup H} (hP : h.IsSelected i P)

include hP

theorem IsSelected.conclusion (hchar : CharTwo (⊤ : Subgroup H)) (hnoChar : NoCharNormal R ⊤) :
    FactorLocalConclusion h i P := by
  have hSP : elemBaumannIn 2 R ≤ P := hP.S_le
  have hker : ∀ ψ : ↥(I i) ≃* V4',
      ψ.toMonoidHom.ker =
        (Subgroup.centralizer ((oddOrderSubgroup P : Subgroup H) : Set H)).subgroupOf (I i) := by
    intro ψ
    rw [(MonoidHom.ker_eq_bot_iff _).mpr ψ.injective]
    symm
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : H) ∈ I i ⊓ Subgroup.centralizer ((oddOrderSubgroup P : Subgroup H) : Set H) :=
      ⟨x.2, hx⟩
    rw [hP.centralizer_I_odd] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hx'))
  obtain ⟨ρ', ψ, hsurj, hequiv, hkerρ, hcard⟩ := hP.exists_rep
  exact
    { S_norm_Y := fun s hs => h.S_normalizes_Yi hs i
      Y_le_N := h.Yi_le_N i
      Y_not_le_M := h.Yi_not_le_M i
      P_le := hP.P_le
      S_lt_P := hP.S_lt
      P_not_le_M := hP.not_le_M
      sylow := hP.sylow_P
      S_not_normal := fun hn =>
        hP.not_le_normalizer ((Subgroup.normal_subgroupOf_iff_le_normalizer hSP).mp hn)
      PM_max := ⟨le_inf hSP h.S_le_M, hP.PM_lt, hP.max⟩
      H_eq := hP.sup_R
      noChar := hP.noChar_P hnoChar
      NS_normal := h.NS_normal
      charTwo_NS := h.charTwo_NS hchar
      charTwo_P := hP.charTwo_P hchar
      Q0_le_S := h.Q0_le_S
      rho_P := hP.map_rho
      I_le_S := (h.I_le i).trans h.W_le_S
      reduced := hP.isTwoReduced
      rep := ⟨ρ', ψ, hsurj, hequiv, hkerρ, hcard, hker ψ⟩
      C_trivial := hP.centralizer_I_odd
      J_nontrivial := by
        rw [thompsonJ_baumann_eq]
        exact h.commutator_J_I_ne_bot i
      campbell := hP.a3SelHyp hchar hnoChar }

end WreathHyp

end Finite

end CFSG.QuasithinUnique.Setup.Wreath
