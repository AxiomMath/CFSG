module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KEvenSLRed
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KEvenSLTri

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.EvenSL

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem normal_two_subgroup_eq_bot {Γ : Type} [Group Γ] (ρ : Γ →* Module.End F (Fin 3 → F))
    (hρ : Function.Injective ρ)
    (hirr : ∀ W : Submodule F (Fin 3 → F), (∀ g : Γ, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (P : Subgroup Γ) [P.Normal] (hP : IsPGroup 2 P) : P = ⊥ := by
  obtain ⟨v, hv, hfix⟩ := exists_fixed_ne_zero hP (ρ.comp P.subtype)
    (inferInstance : Nontrivial (Fin 3 → F))
  let W : Submodule F (Fin 3 → F) :=
    { carrier := {w | ∀ p ∈ P, ρ p w = w}
      add_mem' := fun {a b} ha hb p hp => by rw [map_add, ha p hp, hb p hp]
      zero_mem' := fun p _ => map_zero _
      smul_mem' := fun c w hw p hp => by rw [map_smul, hw p hp] }
  have hWinv : ∀ g : Γ, ∀ w ∈ W, ρ g w ∈ W := by
    intro g w hw p hp
    have hmem : g⁻¹ * p * g ∈ P := by
      have := Subgroup.Normal.conj_mem ‹P.Normal› p hp g⁻¹
      simpa using this
    calc ρ p (ρ g w) = ρ g (ρ (g⁻¹ * p * g) w) := by
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
          congr 2
          group
      _ = ρ g w := by rw [hw _ hmem]
  have hv' : v ∈ W := fun p hp => hfix ⟨p, hp⟩
  rcases hirr W hWinv with h | h
  · exact absurd (h ▸ hv') (by simpa using hv)
  · rw [eq_bot_iff]
    intro p hp
    have : ρ p = 1 := by
      refine LinearMap.ext fun w => ?_
      have : w ∈ W := h ▸ Submodule.mem_top
      simpa using this p hp
    rw [Subgroup.mem_bot]
    exact hρ (by rw [this, map_one])

theorem ker_le_frattini {Γ X : Type} [Group Γ] [Group X] (π : Γ →* X)
    (hπ : Function.Surjective π)
    (hmin : ∀ L : Subgroup Γ, L ≠ ⊤ → ¬ Function.Surjective (π.comp L.subtype)) :
    π.ker ≤ frattini Γ := by
  unfold frattini Order.radical
  refine le_iInf₂ fun L hL => ?_
  by_contra hle
  have hsup : L ⊔ π.ker = ⊤ := hL.2 _ (left_lt_sup.2 hle)
  apply hmin L hL.1
  intro x
  obtain ⟨g, rfl⟩ := hπ x
  have hg : g ∈ L ⊔ π.ker := hsup ▸ Subgroup.mem_top g
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hg
  exact ⟨⟨y, hy⟩, by simp [MonoidHom.mem_ker.1 hz]⟩

theorem not_two_dvd_card_ker {Γ X : Type} [Group Γ] [Finite Γ] [Group X]
    (ρ : Γ →* Module.End F (Fin 3 → F)) (hρ : Function.Injective ρ) (π : Γ →* X)
    (hirr : ∀ W : Submodule F (Fin 3 → F), (∀ g : Γ, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hfr : π.ker ≤ frattini Γ) : ¬ 2 ∣ Nat.card π.ker := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥π.ker) 2 h2
  have hz : IsPGroup 2 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hx]; norm_num
  obtain ⟨P, hxP⟩ := hz.exists_le_sylow
  have hnorm := Sylow.normalizer_sup_eq_top P
  have htop := frattini_nongenerating
    (top_le_iff.1 ((le_of_eq hnorm.symm).trans (sup_le_sup_left hfr _)))
  have hPn : (P.map π.ker.subtype).Normal := Subgroup.normalizer_eq_top_iff.1 htop
  have hP2 : IsPGroup 2 (P.map π.ker.subtype) := P.isPGroup'.map _
  have hbot := normal_two_subgroup_eq_bot ρ hρ hirr (P.map π.ker.subtype) hP2
  · have hxP' : x ∈ (P : Subgroup ↥π.ker) := hxP (Subgroup.mem_zpowers x)
    have : π.ker.subtype x ∈ P.map π.ker.subtype := Subgroup.mem_map_of_mem _ hxP'
    rw [hbot, Subgroup.mem_bot] at this
    have hx1 : x = 1 := Subtype.ext this
    rw [hx1, orderOf_one] at hx
    omega

theorem core_false {Γ X : Type} [Group Γ] [Finite Γ] [Group X] (hSL : IsSLThreeFour X)
    (ρ : Γ →* Module.End F (Fin 3 → F)) (hρ : Function.Injective ρ) (π : Γ →* X)
    (hπ : Function.Surjective π)
    (hscal : ∀ g : Γ, (∃ c : F, ρ g = c • (1 : Module.End F (Fin 3 → F))) → π g = 1)
    (hmin : ∀ L : Subgroup Γ, L ≠ ⊤ → ¬ Function.Surjective (π.comp L.subtype)) : False := by
  classical
  have hfinX : Finite X := Finite.of_surjective π hπ
  have hirr : ∀ W : Submodule F (Fin 3 → F), (∀ g : Γ, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    by_contra hcon
    push Not at hcon
    exact reducible_false hSL ρ hρ π hπ W hW hcon.1 hcon.2
  have hfr := ker_le_frattini π hπ hmin
  have hodd := not_two_dvd_card_ker ρ hρ π hirr hfr
  obtain ⟨A, hAp, a, ha, b, hb, hab⟩ := exists_nonabelian_isPGroup_two hSL
  obtain ⟨S, hAS⟩ := hAp.exists_le_sylow
  obtain ⟨T, hT⟩ := Sylow.mapSurjective_surjective hπ 2 S
  have hTS : (T : Subgroup Γ).map π = (S : Subgroup X) := by
    rw [← Sylow.coe_mapSurjective hπ T, hT]
  have hTp : IsPGroup 2 (T : Subgroup Γ) := T.isPGroup'
  have haT : a ∈ (T : Subgroup Γ).map π := hTS ▸ hAS ha
  have hbT : b ∈ (T : Subgroup Γ).map π := hTS ▸ hAS hb
  obtain ⟨x, hxT, rfl⟩ := haT
  obtain ⟨y, hyT, rfl⟩ := hbT
  have hxy : ρ x * ρ y ≠ ρ y * ρ x := by
    intro h
    apply hab
    have : x * y = y * x := hρ (by rw [map_mul, map_mul, h])
    rw [← map_mul, ← map_mul, this]
  have hc3 := card_center_slThreeFour hSL
  have : Nontrivial (Subgroup.center X) :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [hc3]; norm_num)
  obtain ⟨⟨z, hzc⟩, hz1⟩ := exists_ne (1 : Subgroup.center X)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hz3 : z ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center X) (x := ⟨z, hzc⟩)
    rw [hc3] at this
    simpa using congrArg Subtype.val this
  have hzord : orderOf z = 3 := by
    have hd : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1'
    · exact h
  have hzcomm : ∀ u : X, u * z = z * u := fun u => Subgroup.mem_center_iff.1 hzc u
  obtain ⟨g0, hg0⟩ := hπ z
  let L := {g : Γ // π g = z}
  have hconj : ∀ (s : (T : Subgroup Γ)) (g : L), π (s.1 * g.1 * s.1⁻¹) = z := by
    intro s g
    rw [map_mul, map_mul, map_inv, g.2, hzcomm, mul_assoc, mul_inv_cancel, mul_one]
  let _ : SMul (T : Subgroup Γ) L := ⟨fun s g => ⟨s.1 * g.1 * s.1⁻¹, hconj s g⟩⟩
  have hsm : ∀ (s : (T : Subgroup Γ)) (g : L), (s • g).1 = s.1 * g.1 * s.1⁻¹ := fun _ _ => rfl
  let _ : MulAction (T : Subgroup Γ) L :=
    { one_smul := fun g => Subtype.ext (by rw [hsm]; simp)
      mul_smul := fun s s' g => Subtype.ext (by
        rw [hsm, hsm, hsm]; simp [mul_assoc]) }
  have hLcard : Nat.card L = Nat.card π.ker := by
    refine Nat.card_congr
      { toFun := fun g => ⟨g0⁻¹ * g.1, by rw [MonoidHom.mem_ker, map_mul, map_inv, hg0, g.2,
          inv_mul_cancel]⟩
        invFun := fun k => ⟨g0 * k.1, by rw [map_mul, hg0, MonoidHom.mem_ker.1 k.2, mul_one]⟩
        left_inv := fun g => Subtype.ext (by simp)
        right_inv := fun k => Subtype.ext (by simp) }
  have hmod := hTp.card_modEq_card_fixedPoints L
  have hfix_pos : 0 < Nat.card (MulAction.fixedPoints (T : Subgroup Γ) L) := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    rw [h0, hLcard] at hmod
    unfold Nat.ModEq at hmod
    apply hodd
    omega
  obtain ⟨⟨⟨g, hgz⟩, hgfix⟩⟩ := Nat.card_pos_iff.1 hfix_pos |>.1
  have hgc : ∀ s ∈ (T : Subgroup Γ), s * g = g * s := by
    intro s hs
    have := MulAction.mem_fixedPoints.1 hgfix ⟨s, hs⟩
    have h2 : s * g * s⁻¹ = g := congrArg Subtype.val this
    calc s * g = (s * g * s⁻¹) * s := by group
      _ = g * s := by rw [h2]
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hpow : (2 : ℕ) ^ k ≠ 0 := by positivity
  have hot : orderOf (g ^ 2 ^ k) = m := by
    rw [orderOf_pow' _ hpow, hkm, Nat.gcd_eq_right (dvd_mul_right _ _), Nat.mul_div_cancel_left _
      (by positivity)]
  have hπt : π (g ^ 2 ^ k) ≠ 1 := by
    rw [map_pow, hgz]
    intro h1
    have : 3 ∣ 2 ^ k := hzord ▸ orderOf_dvd_of_pow_eq_one h1
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
    omega
  obtain ⟨c, hc⟩ := exists_scalar_of_centralizes ρ (T : Subgroup Γ) hTp hxT hyT hxy (g ^ 2 ^ k)
    (hot ▸ hm) (fun s hs => ((Commute.pow_right (hgc s hs) (2 ^ k)) : _))
  exact hπt (hscal _ ⟨c, hc⟩)

theorem sl34_not_quotient {Γ X : Type} [Group Γ] [Finite Γ] [Group X] (hSL : IsSLThreeFour X)
    (ρ : Γ →* Module.End F (Fin 3 → F)) (hρ : Function.Injective ρ) (π : Γ →* X)
    (hπ : Function.Surjective π)
    (hscal : ∀ g : Γ, (∃ c : F, ρ g = c • (1 : Module.End F (Fin 3 → F))) → π g = 1) : False := by
  induction' hn : Nat.card Γ using Nat.strong_induction_on with n ih generalizing Γ
  by_cases hmin : ∀ L : Subgroup Γ, L ≠ ⊤ → ¬ Function.Surjective (π.comp L.subtype)
  · exact core_false hSL ρ hρ π hπ hscal hmin
  · push Not at hmin
    obtain ⟨L, hL, hsurj⟩ := hmin
    have hlt : Nat.card L < n := by
      rw [← hn]
      refine lt_of_le_of_ne (Subgroup.card_le_card_group L) fun h => hL ?_
      exact Subgroup.eq_top_of_card_eq L h
    exact ih _ hlt (ρ.comp L.subtype) (hρ.comp Subtype.val_injective) (π.comp L.subtype) hsurj
      (fun g hg => hscal g.1 hg) rfl

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.EvenSL
