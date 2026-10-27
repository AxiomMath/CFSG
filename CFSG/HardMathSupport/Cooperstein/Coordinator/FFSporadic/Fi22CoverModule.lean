module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi22CoverGroup
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HyperplaneOrbit

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open scoped commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

section Exact

variable {G : Type*} [Group G]

theorem mul_eq_of_comm_eq {p q c : G} (hc : ⁅p, q⁆ = c) (hcp : Commute c p) (hcq : Commute c q) :
    p * q = q * (p * c) := by
  have h1 : p * q = c * (q * p) := by rw [← hc]; group
  rw [h1, ← mul_assoc, hcq.eq, mul_assoc, hcp.eq]

private theorem orderOf_two_zmod_three' : orderOf (2 : ZMod 3) = 2 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m
  decide

end Exact

theorem card_ge_of_exact {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {p₀ p₁ p₂ q₀ q₁ q₂ c ω n : MulAut W} {r : ℕ}
    (h : Fi22CoverStruct p₀ p₁ p₂ q₀ q₁ q₂ c ω n r) (hr : ω ^ r = 1) :
    2 ^ 54 ≤ Nat.card W := by
  have h1 : ⁅p₁, q₁⁆ = c := by rw [h.z₁, hr, mul_one]
  have h2 : ⁅p₂, q₂⁆ = c := by
    rw [h.z₂, mul_comm 2 r, pow_mul, hr, one_pow, mul_one]
  have hheis : HeisCfg 3 3 ![p₀, p₁, p₂] ![q₀, q₁, q₂] c :=
    heisCfg_three_three h.p₀3 h.p₁3 h.p₂3 h.c3 h.cp₀.symm.eq h.cp₁.symm.eq h.cp₂.symm.eq
      h.cq₀.symm.eq h.cq₁.symm.eq h.cq₂.symm.eq
      (mul_eq_of_comm_eq h.z₀ h.cp₀ h.cq₀) (mul_eq_of_comm_eq h1 h.cp₁ h.cq₁)
      (mul_eq_of_comm_eq h2 h.cp₂ h.cq₂)
      h.p₀p₁.eq h.p₀p₂.eq h.p₁p₂.eq h.q₀q₁.eq h.q₀q₂.eq h.q₁q₂.eq
      h.p₀q₁.eq h.p₀q₂.eq h.p₁q₀.eq h.p₁q₂.eq h.p₂q₀.eq h.p₂q₁.eq (by simpa using h.c_ne 0)
  have hb := two_pow_le_card_imgT_of_heisCfg hW (p := 3) (by norm_num) hheis
  rw [orderOf_two_zmod_three'] at hb
  exact (by norm_num : 2 ^ 54 = 2 ^ (3 ^ 3 * 2)) ▸ hb.trans (Subgroup.card_le_card_group _)

section Piece

variable {W : Type} [CommGroup W]

theorem piece_bound [Finite W] (hW : ∀ w : W, w * w = 1) {d ν : MulAut W}
    {x y : Fin 2 → MulAut W} {a : Fin 2 → ℕ} (hν3 : ν ^ 3 = 1)
    (hfix : ∀ w : W, ν w = w → w = 1) (hK : fixV (Subgroup.zpowers d) ≠ ⊥)
    (hxd : ∀ i, Commute (x i) d) (hyd : ∀ i, Commute (y i) d) (hxν : ∀ i, Commute (x i) ν)
    (hyν : ∀ i, Commute (y i) ν) (hdν : Commute d ν) (hx3 : ∀ i, x i ^ 3 = 1)
    (hxy : ∀ i, x i * y i = d ^ a i * ν * (y i * x i))
    (hxx : ∀ i j, x i * x j = x j * x i) (hyy : ∀ i j, i ≠ j → y i * y j = y j * y i)
    (hxy' : ∀ i j, i ≠ j → x i * y j = y j * x i) :
    2 ^ 18 ≤ Nat.card (fixV (Subgroup.zpowers d)) := by
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup W, K = fixV (Subgroup.zpowers d) := ⟨_, rfl⟩
  rw [← hKdef] at hK ⊢
  have hKmem : ∀ v : W, v ∈ K ↔ d v = v := fun v => by rw [hKdef]; exact mem_fixV_zpowers
  let A : Subgroup (MulAut W) := Subgroup.centralizer ({d} : Set (MulAut W))
  have hmemA : ∀ g : MulAut W, Commute g d → g ∈ A := fun g hg => by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hg.symm.eq
  have hKA : ∀ g ∈ A, ∀ k ∈ K, g k ∈ K := by
    intro g hg k hk
    rw [hKmem] at hk ⊢
    have h1 := Subgroup.mem_centralizer_iff.1 hg d rfl
    have h2 := congrArg (fun m : MulAut W => m k) h1
    simp only [MulAut.mul_apply] at h2
    rw [h2, hk]
  let ρ : ↥A →* MulAut ↥K := actOnSub hKA
  let xA : Fin 2 → A := fun i => ⟨x i, hmemA _ (hxd i)⟩
  let yA : Fin 2 → A := fun i => ⟨y i, hmemA _ (hyd i)⟩
  let νA : A := ⟨ν, hmemA _ hdν.symm⟩
  let dA : A := ⟨d, hmemA _ (Commute.refl d)⟩
  have hρd : ρ dA = 1 := by
    refine MulEquiv.ext fun k => Subtype.ext ?_
    show d (k : W) = k
    exact (hKmem _).1 k.2
  have hρxy : ∀ i, (ρ (yA i))⁻¹ * ρ (xA i) * ρ (yA i) = ρ (xA i) * ρ νA := by
    intro i
    have h1 : (yA i)⁻¹ * xA i * yA i = xA i * (dA ^ a i * νA) := by
      refine Subtype.ext ?_
      show (y i)⁻¹ * x i * y i = x i * (d ^ a i * ν)
      have c1 : Commute (y i) (d ^ a i * ν) := ((hyd i).pow_right (a i)).mul_right (hyν i)
      have c2 : Commute (x i) (d ^ a i * ν) := ((hxd i).pow_right (a i)).mul_right (hxν i)
      have e1 : x i * y i = y i * (x i * (d ^ a i * ν)) := by
        rw [hxy i]
        calc d ^ a i * ν * (y i * x i) = y i * x i * (d ^ a i * ν) :=
              (c1.symm.mul_right c2.symm).eq
          _ = y i * (x i * (d ^ a i * ν)) := mul_assoc _ _ _
      rw [mul_assoc, e1, inv_mul_cancel_left]
    have h2 := congrArg ρ h1
    simpa only [map_mul, map_inv, map_pow, hρd, one_pow, one_mul] using h2
  have hheis : HeisCfg 3 2 (fun i => ρ (xA i)) (fun i => ρ (yA i)) (ρ νA) := by
    refine ⟨?_, ?_, ?_, ?_, hρxy, ?_, ?_, ?_, ?_⟩
    · intro i
      rw [← map_pow, show (xA i) ^ 3 = 1 from Subtype.ext (hx3 i), map_one]
    · rw [← map_pow, show νA ^ 3 = 1 from Subtype.ext hν3, map_one]
    · intro i
      rw [← map_mul, ← map_mul]
      exact congrArg ρ (Subtype.ext (hxν i).eq)
    · intro i
      rw [← map_mul, ← map_mul]
      exact congrArg ρ (Subtype.ext (hyν i).eq)
    · intro i j
      rw [← map_mul, ← map_mul]
      exact congrArg ρ (Subtype.ext (hxx i j))
    · intro i j hij
      rw [← map_mul, ← map_mul]
      exact congrArg ρ (Subtype.ext (hyy i j hij))
    · intro i j hij
      rw [← map_mul, ← map_mul]
      exact congrArg ρ (Subtype.ext (hxy' i j hij))
    · intro h1
      obtain ⟨k, hk1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hK
      apply hk1
      apply Subtype.ext
      have h2 : ((ρ νA k : ↥K) : W) = ν k := rfl
      rw [h1] at h2
      exact hfix _ h2.symm
  have hWK : ∀ w : ↥K, w * w = 1 := fun w => Subtype.ext (hW w)
  have hb := two_pow_le_card_imgT_of_heisCfg (W := ↥K) hWK (p := 3) (by norm_num) hheis
  rw [orderOf_two_zmod_three'] at hb
  exact (by norm_num : 2 ^ 18 = 2 ^ (3 ^ 2 * 2)) ▸ hb.trans (Subgroup.card_le_card_group _)

end Piece

section PlaneRel

variable {G : Type*} [Group G]

theorem plane_rel {p q Z d ν : G} {e : ℕ} (he : e = 1 ∨ e = 2) (hν3 : ν ^ 3 = 1)
    (hpq : ⁅p, q⁆ = Z) (hZ : Z = d * ν ^ e) (hdν : Commute d ν) (hZq : Commute Z q) :
    p * q ^ e = d ^ e * ν * (q ^ e * p) := by
  have h1 := Commute.commutatorElement_pow_right (a := p) (b := q) (by rw [hpq]; exact hZq.symm) e
  rw [hpq] at h1
  have h2 : p * q ^ e = Z ^ e * (q ^ e * p) := by
    have : ⁅p, q ^ e⁆ = Z ^ e := h1.symm
    have h3 : p * q ^ e = ⁅p, q ^ e⁆ * (q ^ e * p) := by rw [commutatorElement_def]; group
    rw [h3, this]
  have hνe : ν ^ (e * e) = ν := by
    rcases he with rfl | rfl
    · simp
    · rw [show 2 * 2 = 3 + 1 by norm_num, pow_add, hν3, one_mul, pow_one]
  rw [h2, hZ, Commute.mul_pow (hdν.pow_right e), ← pow_mul, hνe]

end PlaneRel

section Decomp

variable {W : Type} [CommGroup W]

@[expose] def nrm (a : MulAut W) (w : W) : W := w * a w * (a ^ 2) w

theorem nrm_mul (a : MulAut W) (u v : W) : nrm a (u * v) = nrm a u * nrm a v := by
  simp only [nrm, map_mul]
  ac_rfl

theorem nrm_one (a : MulAut W) : nrm a 1 = 1 := by simp [nrm]

theorem nrm_of_fixed (hW : ∀ w : W, w * w = 1) {a : MulAut W} {w : W} (hw : a w = w) :
    nrm a w = w := by
  have h2 : (a ^ 2) w = w := by rw [pow_two, MulAut.mul_apply, hw, hw]
  rw [nrm, hw, h2, hW, one_mul]

theorem apply_nrm {a : MulAut W} (ha3 : a ^ 3 = 1) (w : W) : a (nrm a w) = nrm a w := by
  have h3 : a ((a ^ 2) w) = w := by
    have e : a ^ 3 = a * a ^ 2 := pow_succ' a 2
    have := congrArg (fun m : MulAut W => m w) (e.symm.trans ha3)
    simpa using this
  have h2 : (a ^ 2) w = a (a w) := by rw [pow_two]; rfl
  simp only [nrm, map_mul, h3]
  rw [← h2]
  ac_rfl

theorem nrm_mul_pow_of_fixed {a ν : MulAut W} (hcomm : a * ν = ν * a) (hν3 : ν ^ 3 = 1) {w : W}
    (hw : a w = w) {m : ℕ} (hm : m = 1 ∨ m = 2) : nrm (a * ν ^ m) w = nrm ν w := by
  have hcm : a * ν ^ m = ν ^ m * a := ((show Commute a ν from hcomm).pow_right m).eq
  have h1 : (a * ν ^ m) w = (ν ^ m) w := by
    rw [hcm, MulAut.mul_apply, hw]
  have h2a : (a ^ 2) w = w := by rw [pow_two, MulAut.mul_apply, hw, hw]
  have h2 : ((a * ν ^ m) ^ 2) w = ((ν ^ m) ^ 2) w := by
    have hc2 : a ^ 2 * (ν ^ m) ^ 2 = (ν ^ m) ^ 2 * a ^ 2 :=
      (((show Commute a ν from hcomm).pow_right m).pow_pow 2 2).eq
    rw [Commute.mul_pow ((show Commute a ν from hcomm).pow_right m), hc2, MulAut.mul_apply, h2a]
  rw [nrm, h1, h2]
  rcases hm with rfl | rfl
  · simp [nrm]
  · have e : (ν ^ 2) ^ 2 = ν := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hν3, one_mul, pow_one]
    rw [e, nrm]
    ac_rfl

theorem prod_nrm (hW : ∀ w : W, w * w = 1) {c ν : MulAut W} (hcν : c * ν = ν * c)
    (hν3 : ν ^ 3 = 1) (hfix : ∀ w : W, ν w = w → w = 1) (w : W) :
    nrm c w * nrm (c * ν) w * nrm (c * ν ^ 2) w = w := by
  have e1 : (c * ν) ^ 2 = c ^ 2 * ν ^ 2 := Commute.mul_pow (show Commute c ν from hcν) 2
  have e2 : (c * ν ^ 2) ^ 2 = c ^ 2 * ν := by
    rw [Commute.mul_pow ((show Commute c ν from hcν).pow_right 2), ← pow_mul,
      show 2 * 2 = 3 + 1 by norm_num, pow_add, hν3, one_mul, pow_one]
  have hnν : nrm ν w = 1 := hfix _ (apply_nrm hν3 w)
  have hnν' : w * (ν ^ 2) w * ν w = 1 := by
    rw [← hnν]
    unfold nrm
    ac_rfl
  calc nrm c w * nrm (c * ν) w * nrm (c * ν ^ 2) w
      = (w * w * w) * c (nrm ν w) * (c ^ 2) (w * (ν ^ 2) w * ν w) := by
        simp only [nrm, e1, e2, MulAut.mul_apply, map_mul]
        ac_rfl
    _ = w := by rw [hnν, hnν', map_one, map_one, mul_one, mul_one, hW, one_mul]

end Decomp

section Planes

variable {W : Type} [CommGroup W]

theorem piece_planes [Finite W] (hW : ∀ w : W, w * w = 1) {d ν p p' q q' : MulAut W} {e e' : ℕ}
    (he : e = 1 ∨ e = 2) (he' : e' = 1 ∨ e' = 2) (hν3 : ν ^ 3 = 1)
    (hfix : ∀ w : W, ν w = w → w = 1) (hdν : Commute d ν)
    (hK : fixV (Subgroup.zpowers d) ≠ ⊥)
    (hpd : Commute p d) (hp'd : Commute p' d) (hqd : Commute q d) (hq'd : Commute q' d)
    (hpν : Commute p ν) (hp'ν : Commute p' ν) (hqν : Commute q ν) (hq'ν : Commute q' ν)
    (hp3 : p ^ 3 = 1) (hp'3 : p' ^ 3 = 1)
    (hpq : ⁅p, q⁆ = d * ν ^ e) (hp'q' : ⁅p', q'⁆ = d * ν ^ e')
    (hpp' : Commute p p') (hqq' : Commute q q') (hpq' : Commute p q') (hp'q : Commute p' q) :
    2 ^ 18 ≤ Nat.card (fixV (Subgroup.zpowers d)) := by
  have hZq : Commute (d * ν ^ e) q := (hqd.symm).mul_left ((hqν.symm).pow_left e)
  have hZq' : Commute (d * ν ^ e') q' := (hq'd.symm).mul_left ((hq'ν.symm).pow_left e')
  have hrel := plane_rel (p := p) (q := q) he hν3 hpq rfl hdν hZq
  have hrel' := plane_rel (p := p') (q := q') he' hν3 hp'q' rfl hdν hZq'
  refine piece_bound hW (x := ![p, p']) (y := ![q ^ e, q' ^ e']) (a := ![e, e']) hν3 hfix hK
    ?_ ?_ ?_ ?_ hdν ?_ ?_ ?_ ?_ ?_
  · exact Fin.forall_fin_two.2 ⟨hpd, hp'd⟩
  · exact Fin.forall_fin_two.2 ⟨hqd.pow_left e, hq'd.pow_left e'⟩
  · exact Fin.forall_fin_two.2 ⟨hpν, hp'ν⟩
  · exact Fin.forall_fin_two.2 ⟨hqν.pow_left e, hq'ν.pow_left e'⟩
  · exact Fin.forall_fin_two.2 ⟨hp3, hp'3⟩
  · exact Fin.forall_fin_two.2 ⟨hrel, hrel'⟩
  · exact Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨rfl, hpp'.eq⟩,
      Fin.forall_fin_two.2 ⟨hpp'.symm.eq, rfl⟩⟩
  · exact Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨fun h => absurd rfl h, fun _ =>
      (hqq'.pow_pow e e').eq⟩, Fin.forall_fin_two.2 ⟨fun _ => (hqq'.pow_pow e e').symm.eq,
      fun h => absurd rfl h⟩⟩
  · exact Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨fun h => absurd rfl h, fun _ =>
      (hpq'.pow_right e').eq⟩, Fin.forall_fin_two.2 ⟨fun _ => (hp'q.pow_right e).eq,
      fun h => absurd rfl h⟩⟩

end Planes

theorem card_ge_of_ne {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    (hnt : Nontrivial W) {p₀ p₁ p₂ q₀ q₁ q₂ c ω n : MulAut W} {r : ℕ}
    (h : Fi22CoverStruct p₀ p₁ p₂ q₀ q₁ q₂ c ω n r) (hr : ω ^ r ≠ 1)
    (hfixω : ∀ w : W, ω w = w → w = 1) : 2 ^ 54 ≤ Nat.card W := by
  obtain ⟨ν, hν⟩ : ∃ ν : MulAut W, ν = ω ^ r := ⟨_, rfl⟩
  have hν3 : ν ^ 3 = 1 := by rw [hν, ← pow_mul, mul_comm, pow_mul, h.ω3, one_pow]
  have hfix : ∀ w : W, ν w = w → w = 1 := by
    intro w hw
    apply hfixω
    have hmod : r % 3 = 1 ∨ r % 3 = 2 := by
      by_contra hcon
      push Not at hcon
      have h0 : r % 3 = 0 := by omega
      apply hr
      rw [← Nat.div_add_mod r 3, h0, add_zero, pow_mul, h.ω3, one_pow]
    have hr' : ω ^ r = ω ^ (r % 3) := by
      conv_lhs => rw [← Nat.div_add_mod r 3, pow_add, pow_mul, h.ω3, one_pow, one_mul]
    rw [hν, hr'] at hw
    rcases hmod with h1 | h1
    · rw [h1, pow_one] at hw
      exact hw
    · rw [h1] at hw
      have h3 : (ω ^ 3) w = w := by rw [h.ω3]; rfl
      have : ω ^ 3 = ω * ω ^ 2 := pow_succ' ω 2
      rw [this, MulAut.mul_apply, hw] at h3
      exact h3
  have hz₂ : ⁅p₂, q₂⁆ = c * ν ^ 2 := by rw [h.z₂, hν, ← pow_mul, mul_comm]
  have hz₁ : ⁅p₁, q₁⁆ = c * ν := by rw [h.z₁, hν]
  have hcν : Commute c ν := by rw [hν]; exact h.ωc.symm.pow_right r
  have hνc : ∀ {x : MulAut W}, Commute ω x → Commute ν x := fun hx => by rw [hν]; exact hx.pow_left r
  have hcν' : c * ν = ν * c := hcν.eq
  have hz1_3 : (c * ν) ^ 3 = 1 := by rw [Commute.mul_pow hcν, h.c3, hν3, one_mul]
  have hz2_3 : (c * ν ^ 2) ^ 3 = 1 := by
    rw [Commute.mul_pow (hcν.pow_right 2), h.c3, ← pow_mul, mul_comm 2 3, pow_mul, hν3, one_pow,
      one_mul]
  have hc1ν : Commute (c * ν) ν := hcν.mul_left (Commute.refl ν)
  have hc2ν : Commute (c * ν ^ 2) ν := hcν.mul_left ((Commute.refl ν).pow_left 2)
  have hm0 : ∀ w : W, w ∈ fixV (Subgroup.zpowers c) ↔ c w = w := fun w => mem_fixV_zpowers
  have hm1 : ∀ w : W, w ∈ fixV (Subgroup.zpowers (c * ν)) ↔ (c * ν) w = w :=
    fun w => mem_fixV_zpowers
  have hm2 : ∀ w : W, w ∈ fixV (Subgroup.zpowers (c * ν ^ 2)) ↔ (c * ν ^ 2) w = w :=
    fun w => mem_fixV_zpowers
  have hnν : ∀ w : W, nrm ν w = 1 := fun w => hfix _ (apply_nrm hν3 w)
  have o10 : ∀ w : W, c w = w → nrm (c * ν) w = 1 := fun w hw => by
    have := nrm_mul_pow_of_fixed (a := c) hcν' hν3 hw (m := 1) (Or.inl rfl)
    rw [pow_one] at this
    rw [this, hnν]
  have o20 : ∀ w : W, c w = w → nrm (c * ν ^ 2) w = 1 := fun w hw => by
    rw [nrm_mul_pow_of_fixed (a := c) hcν' hν3 hw (m := 2) (Or.inr rfl), hnν]
  have o01 : ∀ w : W, (c * ν) w = w → nrm c w = 1 := fun w hw => by
    have e : c * ν * ν ^ 2 = c := by
      rw [mul_assoc, ← pow_succ', show 2 + 1 = 3 from rfl, hν3, mul_one]
    have := nrm_mul_pow_of_fixed (a := c * ν) hc1ν.eq hν3 hw (m := 2) (Or.inr rfl)
    rw [e] at this
    rw [this, hnν]
  have o21 : ∀ w : W, (c * ν) w = w → nrm (c * ν ^ 2) w = 1 := fun w hw => by
    have e : c * ν * ν ^ 1 = c * ν ^ 2 := by rw [pow_one, mul_assoc, ← pow_two]
    have := nrm_mul_pow_of_fixed (a := c * ν) hc1ν.eq hν3 hw (m := 1) (Or.inl rfl)
    rw [e] at this
    rw [this, hnν]
  have o02 : ∀ w : W, (c * ν ^ 2) w = w → nrm c w = 1 := fun w hw => by
    have e : c * ν ^ 2 * ν ^ 1 = c := by
      rw [pow_one, mul_assoc, ← pow_succ, show 2 + 1 = 3 from rfl, hν3, mul_one]
    have := nrm_mul_pow_of_fixed (a := c * ν ^ 2) hc2ν.eq hν3 hw (m := 1) (Or.inl rfl)
    rw [e] at this
    rw [this, hnν]
  have o12 : ∀ w : W, (c * ν ^ 2) w = w → nrm (c * ν) w = 1 := fun w hw => by
    have e : c * ν ^ 2 * ν ^ 2 = c * ν := by
      rw [mul_assoc, ← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_add, hν3, one_mul, pow_one]
    have := nrm_mul_pow_of_fixed (a := c * ν ^ 2) hc2ν.eq hν3 hw (m := 2) (Or.inr rfl)
    rw [e] at this
    rw [this, hnν]
  have hprod : Nat.card (fixV (Subgroup.zpowers c)) * Nat.card (fixV (Subgroup.zpowers (c * ν))) *
      Nat.card (fixV (Subgroup.zpowers (c * ν ^ 2))) ≤ Nat.card W := by
    let Ψ : (↥(fixV (Subgroup.zpowers c)) × ↥(fixV (Subgroup.zpowers (c * ν)))) ×
        ↥(fixV (Subgroup.zpowers (c * ν ^ 2))) →* W :=
      { toFun := fun x => ((x.1.1 : W) * (x.1.2 : W)) * (x.2 : W)
        map_one' := by simp
        map_mul' := fun x y => by
          simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
          ac_rfl }
    have hinj : Function.Injective Ψ := by
      rw [injective_iff_map_eq_one]
      rintro ⟨⟨a, b⟩, d⟩ h1
      have h1' : (a : W) * (b : W) * (d : W) = 1 := h1
      have ha := (hm0 a).1 a.2
      have hb := (hm1 b).1 b.2
      have hd := (hm2 d).1 d.2
      have e0 := congrArg (nrm c) h1'
      rw [nrm_one, nrm_mul, nrm_mul, nrm_of_fixed hW ha, o01 _ hb, o02 _ hd, mul_one, mul_one] at e0
      have e1 := congrArg (nrm (c * ν)) h1'
      rw [nrm_one, nrm_mul, nrm_mul, nrm_of_fixed hW hb, o10 _ ha, o12 _ hd, one_mul, mul_one] at e1
      have e2 := congrArg (nrm (c * ν ^ 2)) h1'
      rw [nrm_one, nrm_mul, nrm_mul, nrm_of_fixed hW hd, o20 _ ha, o21 _ hb, one_mul, one_mul] at e2
      exact Prod.ext (Prod.ext (Subtype.ext e0) (Subtype.ext e1)) (Subtype.ext e2)
    have := Nat.card_le_card_of_injective Ψ hinj
    rwa [Nat.card_prod, Nat.card_prod] at this
  have hex : fixV (Subgroup.zpowers c) ≠ ⊥ ∨ fixV (Subgroup.zpowers (c * ν)) ≠ ⊥ ∨
      fixV (Subgroup.zpowers (c * ν ^ 2)) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h0, h1, h2⟩ := hcon
    obtain ⟨w, hw⟩ := exists_ne (1 : W)
    apply hw
    rw [← prod_nrm hW hcν' hν3 hfix w]
    have n0 : nrm c w = 1 := by
      have : nrm c w ∈ fixV (Subgroup.zpowers c) := (hm0 _).2 (apply_nrm h.c3 w)
      rwa [h0, Subgroup.mem_bot] at this
    have n1 : nrm (c * ν) w = 1 := by
      have : nrm (c * ν) w ∈ fixV (Subgroup.zpowers (c * ν)) := (hm1 _).2 (apply_nrm hz1_3 w)
      rwa [h1, Subgroup.mem_bot] at this
    have n2 : nrm (c * ν ^ 2) w = 1 := by
      have : nrm (c * ν ^ 2) w ∈ fixV (Subgroup.zpowers (c * ν ^ 2)) :=
        (hm2 _).2 (apply_nrm hz2_3 w)
      rwa [h2, Subgroup.mem_bot] at this
    rw [n0, n1, n2]
    simp
  have hnν' : n * ν = ν * n := by rw [hν]; exact (h.ωn.pow_left r).symm.eq
  have hn1 : n * (c * ν) = c * ν ^ 2 * n := by
    calc n * (c * ν) = (n * c) * ν := (mul_assoc _ _ _).symm
      _ = c * ν * n * ν := by rw [h.nc, hν]
      _ = c * ν * (n * ν) := by rw [mul_assoc]
      _ = c * ν * (ν * n) := by rw [hnν']
      _ = c * ν ^ 2 * n := by rw [pow_two]; simp only [mul_assoc]
  have hn2 : n * (c * ν ^ 2) = c * n := by
    calc n * (c * ν ^ 2) = (n * c) * ν ^ 2 := (mul_assoc _ _ _).symm
      _ = c * ν * n * ν ^ 2 := by rw [h.nc, hν]
      _ = c * ν * (n * ν ^ 2) := by rw [mul_assoc]
      _ = c * ν * (ν ^ 2 * n) := by rw [((show Commute n ν from hnν').pow_right 2).eq]
      _ = c * (ν * ν ^ 2) * n := by simp only [mul_assoc]
      _ = c * n := by rw [← pow_succ', show 2 + 1 = 3 from rfl, hν3, mul_one]
  have hmap : ∀ {a b : MulAut W}, a * n = n * b → ∀ w : W, b w = w → a (n w) = n w := by
    intro a b hab w hw
    have := congrArg (fun m : MulAut W => m w) hab
    simpa only [MulAut.mul_apply, hw] using this
  have hnne : ∀ w : W, w ≠ 1 → n w ≠ 1 := fun w hw h1 => hw (by simpa using h1)
  have hnonbot : ∀ {a b : MulAut W}, a * n = n * b →
      fixV (Subgroup.zpowers b) ≠ ⊥ → fixV (Subgroup.zpowers a) ≠ ⊥ := by
    intro a b hab hne
    obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    refine (Subgroup.ne_bot_iff_exists_ne_one).2 ⟨⟨n w, mem_fixV_zpowers.2 (hmap hab w
      (mem_fixV_zpowers.1 w.2))⟩, fun h1 => hnne w (fun h2 => hw1 (Subtype.ext h2))
      (congrArg Subtype.val h1)⟩
  have t01 : fixV (Subgroup.zpowers c) ≠ ⊥ → fixV (Subgroup.zpowers (c * ν)) ≠ ⊥ :=
    hnonbot (by rw [h.nc, hν])
  have t12 : fixV (Subgroup.zpowers (c * ν)) ≠ ⊥ → fixV (Subgroup.zpowers (c * ν ^ 2)) ≠ ⊥ :=
    hnonbot hn1.symm
  have t20 : fixV (Subgroup.zpowers (c * ν ^ 2)) ≠ ⊥ → fixV (Subgroup.zpowers c) ≠ ⊥ :=
    hnonbot hn2.symm
  have hall : fixV (Subgroup.zpowers c) ≠ ⊥ ∧ fixV (Subgroup.zpowers (c * ν)) ≠ ⊥ ∧
      fixV (Subgroup.zpowers (c * ν ^ 2)) ≠ ⊥ := by
    rcases hex with h0 | h1 | h2
    · exact ⟨h0, t01 h0, t12 (t01 h0)⟩
    · exact ⟨t20 (t12 h1), h1, t12 h1⟩
    · exact ⟨t20 h2, t01 (t20 h2), h2⟩
  have hνp₀ : Commute ν p₀ := hνc h.ωp₀
  have hνp₁ : Commute ν p₁ := hνc h.ωp₁
  have hνp₂ : Commute ν p₂ := hνc h.ωp₂
  have hνq₀ : Commute ν q₀ := hνc h.ωq₀
  have hνq₁ : Commute ν q₁ := hνc h.ωq₁
  have hνq₂ : Commute ν q₂ := hνc h.ωq₂
  have b0 : 2 ^ 18 ≤ Nat.card (fixV (Subgroup.zpowers c)) :=
    piece_planes hW (d := c) (p := p₁) (p' := p₂) (q := q₁) (q' := q₂) (e := 1) (e' := 2)
      (Or.inl rfl) (Or.inr rfl) hν3 hfix hcν hall.1 h.cp₁.symm h.cp₂.symm h.cq₁.symm h.cq₂.symm
      hνp₁.symm hνp₂.symm hνq₁.symm hνq₂.symm h.p₁3 h.p₂3 (by rw [pow_one]; exact hz₁) hz₂
      h.p₁p₂ h.q₁q₂ h.p₁q₂ h.p₂q₁
  have b1 : 2 ^ 18 ≤ Nat.card (fixV (Subgroup.zpowers (c * ν))) :=
    piece_planes hW (d := c * ν) (p := p₀) (p' := p₂) (q := q₀) (q' := q₂) (e := 2) (e' := 1)
      (Or.inr rfl) (Or.inl rfl) hν3 hfix hc1ν hall.2.1
      (h.cp₀.symm.mul_right hνp₀.symm) (h.cp₂.symm.mul_right hνp₂.symm)
      (h.cq₀.symm.mul_right hνq₀.symm) (h.cq₂.symm.mul_right hνq₂.symm)
      hνp₀.symm hνp₂.symm hνq₀.symm hνq₂.symm h.p₀3 h.p₂3
      (by
        rw [h.z₀]
        rw [mul_assoc, ← pow_succ', show 1 + 2 = 3 from rfl, hν3, mul_one])
      (by rw [hz₂, pow_one, mul_assoc, ← pow_two])
      h.p₀p₂ h.q₀q₂ h.p₀q₂ h.p₂q₀
  have b2 : 2 ^ 18 ≤ Nat.card (fixV (Subgroup.zpowers (c * ν ^ 2))) :=
    piece_planes hW (d := c * ν ^ 2) (p := p₀) (p' := p₁) (q := q₀) (q' := q₁) (e := 1) (e' := 2)
      (Or.inl rfl) (Or.inr rfl) hν3 hfix hc2ν hall.2.2
      (h.cp₀.symm.mul_right (hνp₀.symm.pow_right 2)) (h.cp₁.symm.mul_right (hνp₁.symm.pow_right 2))
      (h.cq₀.symm.mul_right (hνq₀.symm.pow_right 2)) (h.cq₁.symm.mul_right (hνq₁.symm.pow_right 2))
      hνp₀.symm hνp₁.symm hνq₀.symm hνq₁.symm h.p₀3 h.p₁3
      (by
        rw [h.z₀, pow_one, mul_assoc, ← pow_succ, show 2 + 1 = 3 from rfl, hν3, mul_one])
      (by
        rw [hz₁, mul_assoc, ← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_add, hν3, one_mul, pow_one])
      h.p₀p₁ h.q₀q₁ h.p₀q₁ h.p₁q₀
  calc 2 ^ 54 = 2 ^ 18 * 2 ^ 18 * 2 ^ 18 := by norm_num
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul b0 b1) b2
    _ ≤ Nat.card W := hprod

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
