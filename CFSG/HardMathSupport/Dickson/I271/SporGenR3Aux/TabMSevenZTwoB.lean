module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenTwoB
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenNoComp

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMSeven

open CFSG CFSG.Monster CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Visible
  CFSG.Monster.Existence CFSG.Monster.Griess CFSG.Monster.ScalarKernel
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Dickson.I271.TabMFive
  CFSG.Monster.Existence.Co1Bridge CFSG.Sporadic.Co1Schreier

section TwoB


theorem card_cent_dvd_of_conj_sJ (k : cent xGriess) {c : J24} {m : ℕ} (hm1 : 1 ≤ m)
    (hm6 : m ≤ 6) (hc : c * cosetEquivJ24 (QuotientGroup.mk k) * c⁻¹ = sJ ^ m) :
    Nat.card (Subgroup.centralizer ({k} : Set (cent xGriess))) ∣ 35280 := by
  haveI : Finite (cent xGriess) := finite_cent_xGriess
  haveI : Finite J24 := finite_J24
  set j : J24 := cosetEquivJ24 (QuotientGroup.mk k) with hj
  have hfix : fixCount (((j : J24) : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) ≤
      1 := by
    have h1 : fixCount ((((c * j * c⁻¹ : J24) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2))) =
        fixCount (((j : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2))) :=
      fixCount_conj (c : GL24) (j : GL24)
    rw [← h1, hc, fixCount_pow_of_le_six orderOf_sJ hm1 hm6]
    exact fixCount_sJ_le
  have hcard : Nat.card (Subgroup.centralizer ({j} : Set J24)) = 17640 := by
    rw [← card_centralizer_conj c j, hc, card_centralizer_pow_of_le_six orderOf_sJ hm1 hm6,
      card_centralizer_sJ]
  have h := card_cent_xGriess_dvd_of_fixCount_le_one k hfix
  rw [← hj, hcard] at h
  exact h

theorem exists_conj_pow_of_conj_tJ {k k' : cent xGriess} (hk : orderOf k = 7)
    (hk' : orderOf k' = 7) {c c' : J24} {m m' : ℕ} (hm1' : 1 ≤ m') (hm6' : m' ≤ 6)
    (hc : c * cosetEquivJ24 (QuotientGroup.mk k) * c⁻¹ = tJ ^ m)
    (hc' : c' * cosetEquivJ24 (QuotientGroup.mk k') * c'⁻¹ = tJ ^ m') :
    ∃ g : cent xGriess, ∃ n : ℕ, g * k * g⁻¹ = k' ^ n := by
  haveI : Finite (cent xGriess) := finite_cent_xGriess
  set j : J24 := cosetEquivJ24 (QuotientGroup.mk k) with hj
  set j' : J24 := cosetEquivJ24 (QuotientGroup.mk k') with hj'
  have hcop : Nat.Coprime m' (orderOf tJ) := by
    rw [orderOf_tJ]
    exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)).2 (by omega)).symm
  obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime hcop
  have key : (c'⁻¹ * c) * j * (c'⁻¹ * c)⁻¹ = j' ^ (r * m) := by
    have h1 : c * j * c⁻¹ = c' * j' ^ (r * m) * c'⁻¹ := by
      rw [hc, ← hr, ← hc', ← pow_mul, conj_pow]
    calc (c'⁻¹ * c) * j * (c'⁻¹ * c)⁻¹ = c'⁻¹ * (c * j * c⁻¹) * c' := by group
      _ = j' ^ (r * m) := by rw [h1]; group
  obtain ⟨g0, hg0⟩ := QuotientGroup.mk_surjective (cosetEquivJ24.symm (c'⁻¹ * c))
  have hck : (QuotientGroup.mk (g0 * k * g0⁻¹) : cent xGriess ⧸ pCore 2 (cent xGriess)) =
      (QuotientGroup.mk k' : cent xGriess ⧸ pCore 2 (cent xGriess)) ^ (r * m) := by
    apply cosetEquivJ24.injective
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv, hg0, MulEquiv.apply_symm_apply, map_pow]
    exact key
  have hE : Nat.Coprime (Nat.card (pCore 2 (cent xGriess))) 7 := by
    obtain ⟨a, ha⟩ := (pCore_isPGroup (p := 2) (G := cent xGriess)).exists_card_eq
    rw [ha]
    exact Nat.Coprime.pow_left _ (by norm_num)
  exact tabMSeven_isConj_zpowers_of_quot (by norm_num) hE hk hk' hck

theorem card_dvd_or_conj_tJ (k : cent xGriess) (hk : orderOf k = 7) :
    Nat.card (Subgroup.centralizer ({k} : Set (cent xGriess))) ∣ 35280 ∨
      ∃ c : J24, ∃ m : ℕ, 1 ≤ m ∧ m ≤ 6 ∧
        c * cosetEquivJ24 (QuotientGroup.mk k) * c⁻¹ = tJ ^ m := by
  haveI : Finite (cent xGriess) := finite_cent_xGriess
  have hj := @orderOf_image_prime (cent xGriess) ↥J24 _ (Subgroup.toGroup J24) _ 7
    (by norm_num) (by norm_num) cosetEquivJ24 k hk
  obtain ⟨c, m, hm1, hm6, h | h⟩ := exists_conj_pow_sJ_or_tJ _ hj
  · exact Or.inl (card_cent_dvd_of_conj_sJ k hm1 hm6 h)
  · exact Or.inr ⟨c, m, hm1, hm6, h⟩

theorem card_dvd_or_conj_of_twoB (hE : MonsterExistenceStatement MGriess)
    (hB : Nat.card CFSG.Blueprint.NativeSporadic.B = CFSG.Open.monsterBabyOrder)
    {d u v y : MGriess} (hd : orderOf d = 7) (hu : orderOf u = 2) (hud : u * d = d * u)
    (huc : Nat.card ↥(Subgroup.centralizer ({u} : Set MGriess)) = twoBCentralizerOrder)
    (hud' : 35280 < Nat.card ↥(Subgroup.centralizer ({u} : Set MGriess) ⊓
      Subgroup.centralizer ({d} : Set MGriess)))
    (hv : orderOf v = 2)
    (hvc : Nat.card ↥(Subgroup.centralizer ({v} : Set MGriess)) = twoBCentralizerOrder)
    (hy : orderOf y = 7) (hvy : v * y = y * v) :
    Nat.card ↥(Subgroup.centralizer ({v} : Set MGriess) ⊓
        Subgroup.centralizer ({y} : Set MGriess)) ∣ 35280 ∨
      ∃ g : MGriess, ∃ m : ℕ, g * y * g⁻¹ = d ^ m := by
  obtain ⟨h, hh⟩ := isConj_iff.1 (isConj_xGriess_of_card hE hB hv hvc)
  have hy0 : xGriess * (h⁻¹ * y * h) = (h⁻¹ * y * h) * xGriess := by
    rw [← hh] at hvy
    calc xGriess * (h⁻¹ * y * h) = h⁻¹ * (h * xGriess * h⁻¹ * y) * h := by group
      _ = h⁻¹ * (y * (h * xGriess * h⁻¹)) * h := by rw [hvy]
      _ = h⁻¹ * y * h * xGriess := by group
  set k : cent xGriess := ⟨h⁻¹ * y * h, Subgroup.mem_centralizer_singleton_iff.2 hy0.symm⟩
  have hk : orderOf k = 7 := by
    rw [← Subgroup.orderOf_coe]
    change orderOf (h⁻¹ * y * h) = 7
    have := orderOf_conj_eq h⁻¹ y
    rwa [inv_inv, hy] at this
  have hcard : Nat.card ↥(Subgroup.centralizer ({v} : Set MGriess) ⊓
      Subgroup.centralizer ({y} : Set MGriess)) =
        Nat.card (Subgroup.centralizer ({k} : Set (cent xGriess))) := by
    rw [← hh, natCard_cent_inf_conj, card_centralizer_subtype]
  obtain ⟨h', hh'⟩ := isConj_iff.1 (isConj_xGriess_of_card hE hB hu huc)
  have hw0 : xGriess * (h'⁻¹ * d * h') = (h'⁻¹ * d * h') * xGriess := by
    rw [← hh'] at hud
    calc xGriess * (h'⁻¹ * d * h') = h'⁻¹ * (h' * xGriess * h'⁻¹ * d) * h' := by group
      _ = h'⁻¹ * (d * (h' * xGriess * h'⁻¹)) * h' := by rw [hud]
      _ = h'⁻¹ * d * h' * xGriess := by group
  set k' : cent xGriess := ⟨h'⁻¹ * d * h', Subgroup.mem_centralizer_singleton_iff.2 hw0.symm⟩
  have hk' : orderOf k' = 7 := by
    rw [← Subgroup.orderOf_coe]
    change orderOf (h'⁻¹ * d * h') = 7
    have := orderOf_conj_eq h'⁻¹ d
    rwa [inv_inv, hd] at this
  have hcard' : Nat.card ↥(Subgroup.centralizer ({u} : Set MGriess) ⊓
      Subgroup.centralizer ({d} : Set MGriess)) =
        Nat.card (Subgroup.centralizer ({k'} : Set (cent xGriess))) := by
    rw [← hh', natCard_cent_inf_conj, card_centralizer_subtype]
  rcases card_dvd_or_conj_tJ k hk with h1 | ⟨c, m, -, -, hc⟩
  · exact Or.inl (hcard ▸ h1)
  · right
    rcases card_dvd_or_conj_tJ k' hk' with h2 | ⟨c', m', hm1', hm6', hc'⟩
    · exfalso
      have h3 := Nat.le_of_dvd (by norm_num) h2
      rw [← hcard'] at h3
      omega
    · obtain ⟨g, n, hg⟩ := exists_conj_pow_of_conj_tJ hk hk' hm1' hm6' hc hc'
      have hg' : (g : MGriess) * (h⁻¹ * y * h) * (g : MGriess)⁻¹ = (h'⁻¹ * d * h') ^ n := by
        have := congrArg Subtype.val hg
        simpa using this
      refine ⟨h' * (g : MGriess) * h⁻¹, n, ?_⟩
      calc h' * (g : MGriess) * h⁻¹ * y * (h' * (g : MGriess) * h⁻¹)⁻¹ =
          h' * ((g : MGriess) * (h⁻¹ * y * h) * (g : MGriess)⁻¹) * h'⁻¹ := by group
        _ = h' * (h'⁻¹ * d * h') ^ n * h'⁻¹ := by rw [hg']
        _ = d ^ n := by rw [← conj_pow]; group

end TwoB

end CFSG.HardMathSupport.Dickson.I271.TabMSeven
