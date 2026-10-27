module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainStart
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1D

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem v6_add_self (v : V6) : v + v = 0 := by
  ext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize v i = c
  fin_cases c <;> rfl

theorem v6_neg (v : V6) : -v = v := by
  ext i
  simp only [Pi.neg_apply]
  generalize v i = c
  fin_cases c <;> rfl

@[expose] def linPart (γ : Equiv.Perm V6) (v : V6) : V6 := γ v + γ 0

section Aff

variable {γ δ : Equiv.Perm V6} (hγ : ∀ x y z : V6, γ (x + y + z) = γ x + γ y + γ z)
include hγ

theorem aff_add (x y : V6) : γ (x + y) = γ x + γ y + γ 0 := by
  have := hγ x y 0
  rwa [add_zero] at this

theorem linPart_add (x y : V6) : linPart γ (x + y) = linPart γ x + linPart γ y := by
  simp only [linPart, aff_add hγ x y]
  have e : γ x + γ 0 + (γ y + γ 0) = γ x + γ y + (γ 0 + γ 0) := by abel
  rw [e, add_assoc (γ x + γ y), v6_add_self, add_zero]

end Aff

@[expose] def linPartHom (Γ : Subgroup (Equiv.Perm V6))
    (hΓ : ∀ γ ∈ Γ, ∀ x y z : V6, γ (x + y + z) = γ x + γ y + γ z) : Γ →* Equiv.Perm V6 where
  toFun γ :=
    { toFun := linPart γ
      invFun := linPart (γ⁻¹ : Γ)
      left_inv := fun v => by
        have h := hΓ _ (γ⁻¹ : Γ).2
        simp only [linPart]
        rw [aff_add h, ← Equiv.Perm.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel,
          Subgroup.coe_one, Equiv.Perm.one_apply, ← Equiv.Perm.mul_apply, ← Subgroup.coe_mul,
          inv_mul_cancel, Subgroup.coe_one, Equiv.Perm.one_apply, add_zero, add_assoc,
          v6_add_self, add_zero]
      right_inv := fun v => by
        have h := hΓ _ γ.2
        simp only [linPart]
        rw [aff_add h, ← Equiv.Perm.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel,
          Subgroup.coe_one, Equiv.Perm.one_apply, ← Equiv.Perm.mul_apply, ← Subgroup.coe_mul,
          mul_inv_cancel, Subgroup.coe_one, Equiv.Perm.one_apply, add_zero, add_assoc,
          v6_add_self, add_zero] }
  map_one' := Equiv.ext fun v => by
    simp only [Equiv.coe_fn_mk, Subgroup.coe_one, linPart, Equiv.Perm.one_apply, add_zero]
  map_mul' γ δ := Equiv.ext fun v => by
    have h := hΓ _ γ.2
    simp only [Equiv.coe_fn_mk, Equiv.Perm.mul_apply, linPart, Subgroup.coe_mul]
    rw [aff_add h, add_assoc _ ((γ : Equiv.Perm V6) 0) ((γ : Equiv.Perm V6) 0), v6_add_self,
      add_zero]

theorem linPartHom_apply {Γ : Subgroup (Equiv.Perm V6)}
    (hΓ : ∀ γ ∈ Γ, ∀ x y z : V6, γ (x + y + z) = γ x + γ y + γ z) (γ : Γ) (v : V6) :
    linPartHom Γ hΓ γ v = (γ : Equiv.Perm V6) v + (γ : Equiv.Perm V6) 0 := rfl

theorem linPartHom_mem_linGroup {Γ : Subgroup (Equiv.Perm V6)}
    (hΓ : ∀ γ ∈ Γ, ∀ x y z : V6, γ (x + y + z) = γ x + γ y + γ z) (γ : Γ) :
    linPartHom Γ hΓ γ ∈ linGroup := fun x y => linPart_add (hΓ _ γ.2) x y

variable {G : Type*} [Group G]

section IrredV

variable {ε : Eps} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p : Fin 6 → G}

theorem eq_top_of_ne_bot_v6 (hR : RadicalData ε L U Q P a ψ p) {W₀ : AddSubgroup V6}
    (hP : ∀ x ∈ P, ∀ w ∈ W₀, lin ψ x w ∈ W₀) (hne : W₀ ≠ ⊥) : W₀ = ⊤ := by
  obtain ⟨⟨v₀, hv₀⟩, hv1⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero.1 hne)
  have hv₀0 : v₀ ≠ 0 := fun h => hv1 (Subtype.ext h)
  have htype : ∀ z < 64, (z = 0 ∨ qfB ε z = qfB ε (vecBits v₀)) → toVec 6 z ∈ W₀ := by
    intro z hz h
    by_cases hz0 : z = 0
    · subst hz0
      rw [show toVec 6 0 = 0 by rw [← vecBits_zero, toVec_vecBits]]
      exact W₀.zero_mem
    have h' := h.resolve_left hz0
    have hw : toVec 6 z ≠ 0 := by
      intro h0
      apply hz0
      rw [← vecBits_toVec hz, h0, vecBits_zero]
    have hq : qfV ε v₀ = qfV ε (toVec 6 z) := by
      rw [qfV, qfV_toVec ε hz, h']
    obtain ⟨x, hx, hxw⟩ := hR.exists_lin_eq hv₀0 hw hq
    rw [← hxw]
    exact hP x hx _ hv₀
  have hb : ∀ j : Fin 6, (Pi.single j 1 : V6) ∈ W₀ := by
    intro j
    obtain ⟨y, hy, h1, h2⟩ := span ε (qfB ε (vecBits v₀)) j j.isLt
    have hxy : 2 ^ (j : ℕ) ^^^ y < 64 := by
      have h2j : 2 ^ (j : ℕ) < 64 := by
        calc 2 ^ (j : ℕ) < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) j.isLt
          _ = 64 := by norm_num
      exact Nat.xor_lt_two_pow (n := 6) (by simpa using h2j) (by simpa using hy)
    have e : (Pi.single j 1 : V6) = toVec 6 y + toVec 6 (2 ^ (j : ℕ) ^^^ y) := by
      rw [← toVec_xor, ← Nat.xor_assoc, Nat.xor_comm y, Nat.xor_assoc, Nat.xor_self,
        Nat.xor_zero, toVec_two_pow']
    rw [e]
    exact W₀.add_mem (htype y hy h1) (htype _ hxy h2)
  rw [eq_top_iff]
  intro v _
  rw [← Finset.univ_sum_single v]
  refine AddSubgroup.sum_mem _ fun j _ => ?_
  generalize v j = c
  fin_cases c
  · show (Pi.single j (0 : ZMod 2) : V6) ∈ W₀
    rw [Pi.single_zero]
    exact W₀.zero_mem
  · exact hb j

end IrredV

theorem ns_card_minus : (Finset.univ.filter fun v : V6 => v = 0 ∨ qfV .minus v = 1).card = 37 := by
  decide

theorem ns_card_plus : (Finset.univ.filter fun v : V6 => v = 0 ∨ qfV .plus v = 1).card = 29 := by
  decide

theorem eq_64_of_dvd (r : ℕ) (hr : r = 29 ∨ r = 37) :
    ∀ d < 65, d ∣ 64 → d % r = 64 % r → d = 64 := by
  rcases hr with rfl | rfl <;> decide

theorem ns_card (ε : Eps) : ∃ r, (r = 29 ∨ r = 37) ∧
    (Finset.univ.filter fun v : V6 => v = 0 ∨ qfV ε v = 1).card = r := by
  cases ε
  · exact ⟨29, Or.inl rfl, ns_card_plus⟩
  · exact ⟨37, Or.inr rfl, ns_card_minus⟩

section Dich

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G}
  {ψ : V6 → G} {p : Fin 6 → G} (hS : Setup ε t L U Q P a ψ p) {Γ : Subgroup (Equiv.Perm V6)}

theorem mem_orbit_iff {v : V6} : v ∈ MulAction.orbit Γ (0 : V6) ↔ ∃ γ ∈ Γ, γ 0 = v := by
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨γ, γ.2, rfl⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨⟨γ, hγ⟩, rfl⟩

theorem perm_mem_orbit {v : V6} (hv : v ∈ MulAction.orbit Γ (0 : V6)) {γ : Equiv.Perm V6}
    (hγ : γ ∈ Γ) : γ v ∈ MulAction.orbit Γ (0 : V6) := by
  obtain ⟨δ, hδ, rfl⟩ := mem_orbit_iff.1 hv
  exact mem_orbit_iff.2 ⟨γ * δ, mul_mem hγ hδ, rfl⟩

theorem linP_zero (σ : hS.linP.range) : (σ : Equiv.Perm V6) 0 = 0 := by
  obtain ⟨x, hx⟩ := σ.2
  rw [← hx]
  exact map_zero_of_mem_linGroup (hS.rad.linHom_mem_linGroup _)

variable (hΓ0 : ∀ γ ∈ Γ, γ 0 = 0 → γ ∈ hS.linP.range) (hPΓ : hS.linP.range ≤ Γ)
include hΓ0 hPΓ

omit hΓ0 in
theorem lin_mem_orbit {v : V6} (hv : v ∈ MulAction.orbit Γ (0 : V6)) {x : G} (hx : x ∈ P) :
    lin ψ x v ∈ MulAction.orbit Γ (0 : V6) :=
  perm_mem_orbit hv (hPΓ ⟨⟨x, hx⟩, rfl⟩)

theorem card_eq [Finite G] :
    Nat.card Γ = Nat.card (MulAction.orbit Γ (0 : V6)) * (oBound ε / 2) := by
  have e := MulAction.orbitProdStabilizerEquivGroup Γ (0 : V6)
  rw [← Nat.card_congr e, Nat.card_prod]
  congr 1
  have hstab : MulAction.stabilizer Γ (0 : V6) ≃ hS.linP.range :=
    { toFun := fun γ => ⟨(γ : Γ), hΓ0 _ (γ : Γ).2 γ.2⟩
      invFun := fun σ => ⟨⟨σ, hPΓ σ.2⟩, linP_zero hS σ⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr hstab]
  have h := hS.card_linP
  rw [hS.rad.card_P] at h
  omega

variable (hΓaff : ∀ γ ∈ Γ, ∀ x y z : V6, γ (x + y + z) = γ x + γ y + γ z)
include hΓaff

theorem false_of_cone_orbit [Finite G]
    (hO : ∀ v, v ∈ MulAction.orbit Γ (0 : V6) ↔ qfV ε v = 0) : False := by
  classical
  have hΓle : Γ ≤ affGroup ε := by
    intro γ hγ
    refine ⟨fun v => ?_, hΓaff γ hγ⟩
    rcases qfV_cases ε v with h0 | h1
    · rw [h0]
      exact (hO _).1 (perm_mem_orbit ((hO v).2 h0) hγ)
    · rw [h1]
      rcases qfV_cases ε (γ v) with h0' | h1'
      · exfalso
        have := perm_mem_orbit ((hO _).2 h0') (inv_mem hγ)
        rw [perm_inv_apply γ v, hO, h1] at this
        exact one_ne_zero this
      · exact h1'
  have hOcard : Nat.card (MulAction.orbit Γ (0 : V6)) = (zeroSet ε).card := by
    have hset : MulAction.orbit Γ (0 : V6) = ↑(zeroSet ε) := by
      ext v
      simp [zeroSet, hO]
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hcard := card_eq hS hΓ0 hPΓ
  rw [hOcard] at hcard
  have h2 := oBound_even ε
  have hidx : Γ.relIndex (affGroup ε) ≤ 2 := by
    have h := Subgroup.relIndex_mul_card (H := Γ) (K := affGroup ε)
    rw [inf_of_le_left hΓle] at h
    have h3 := card_affGroup_le ε
    have hpos : 0 < Nat.card Γ := Nat.card_pos
    nlinarith
  have hidx0 : Γ.relIndex (affGroup ε) ≠ 0 := by
    intro h0
    have h := Subgroup.relIndex_mul_card (H := Γ) (K := affGroup ε)
    rw [h0, zero_mul] at h
    exact (Nat.card_pos (α := affGroup ε)).ne' h.symm
  have hc : coneCommP ε ∈ Γ :=
    commutator_mem_of_relIndex_le_two hidx hidx0 (coneXP_mem ε) (coneYP_mem ε)
  obtain ⟨x, hx⟩ := hΓ0 _ hc (coneComm_zero ε)
  have hfun : (coneCommP ε : V6 → V6) = lin ψ x := funext fun v => by rw [← hx]; rfl
  have hd := hS.rad.dickC_colsF_lin x.2
  rw [← hfun, colsF_coneComm, (coneCheck_spec ε).2.2.2] at hd
  exact Bool.noConfusion hd

theorem false_of_ns_orbit [Finite G]
    (hO : ∀ v, v ∈ MulAction.orbit Γ (0 : V6) ↔ (v = 0 ∨ qfV ε v = 1)) : False := by
  classical
  obtain ⟨r, hr, hrc⟩ := ns_card ε
  have hrp : r.Prime := by rcases hr with rfl | rfl <;> norm_num
  have : Fact r.Prime := ⟨hrp⟩
  have hOcard : Nat.card (MulAction.orbit Γ (0 : V6)) = r := by
    have hset : MulAction.orbit Γ (0 : V6) =
        ↑(Finset.univ.filter fun v : V6 => v = 0 ∨ qfV ε v = 1) := by
      ext v
      simp [hO]
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, hrc]
  have hcard := card_eq hS hΓ0 hPΓ
  rw [hOcard] at hcard
  obtain ⟨γ, hγ⟩ :=
    exists_prime_orderOf_dvd_card' (G := Γ) r (by rw [hcard]; exact dvd_mul_right _ _)
  set Λ := linPartHom Γ hΓaff
  set σ := Λ γ
  have hσr : σ ^ r = 1 := by rw [← map_pow, ← hγ, pow_orderOf_eq_one, map_one]
  set F : AddSubgroup V6 :=
    { carrier := {v | σ v = v}
      zero_mem' := map_zero_of_mem_linGroup (linPartHom_mem_linGroup hΓaff γ)
      add_mem' := fun {v w} hv hw => by
        change σ (v + w) = v + w
        rw [linPartHom_mem_linGroup hΓaff γ v w]
        exact congrArg₂ (· + ·) hv hw
      neg_mem' := fun {v} hv => by
        change σ (-v) = -v
        rw [v6_neg]
        exact hv }
  have hZ : IsPGroup r (zpowers σ) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    rcases (Nat.dvd_prime hrp).1 (orderOf_dvd_of_pow_eq_one hσr) with h | h
    · exfalso
      rw [orderOf_eq_one_iff] at h
      have hγ2 : γ * γ = 1 := by
        apply Subtype.ext
        refine Equiv.ext fun v => ?_
        have h1 : ∀ w, (γ : Equiv.Perm V6) w = w + (γ : Equiv.Perm V6) 0 := fun w => by
          have := congrArg (fun τ : Equiv.Perm V6 => τ w) h
          simp only [σ, Λ, linPartHom_apply, Equiv.Perm.one_apply] at this
          calc (γ : Equiv.Perm V6) w = ((γ : Equiv.Perm V6) w + (γ : Equiv.Perm V6) 0) +
                (γ : Equiv.Perm V6) 0 := by rw [add_assoc, v6_add_self, add_zero]
            _ = w + (γ : Equiv.Perm V6) 0 := by rw [this]
        simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, Subgroup.coe_one, Equiv.Perm.one_apply]
        rw [h1, h1 v, add_assoc, v6_add_self, add_zero]
      have := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hγ2 : γ ^ 2 = 1)
      rw [hγ] at this
      have := Nat.le_of_dvd (by norm_num) this
      rcases hr with rfl | rfl <;> omega
    · exact h
  have hmod := hZ.card_modEq_card_fixedPoints V6
  have hfix : Nat.card (MulAction.fixedPoints (zpowers σ) V6) = Nat.card F := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    change v ∈ MulAction.fixedPoints (zpowers σ) V6 ↔ σ v = v
    simp only [MulAction.mem_fixedPoints, Subtype.forall, mem_zpowers_iff]
    constructor
    · intro h
      exact h σ ⟨1, zpow_one σ⟩
    · rintro hv _ ⟨n, rfl⟩
      change (σ ^ n) v = v
      have hv' : σ v = v := hv
      induction n using Int.induction_on with
      | zero => rfl
      | succ n ih => rw [_root_.zpow_add_one, Equiv.Perm.mul_apply, hv', ih]
      | pred n ih =>
        rw [_root_.zpow_sub_one, Equiv.Perm.mul_apply]
        have : σ⁻¹ v = v := by rw [← hv', perm_inv_apply, hv']
        rw [this, ih]
  rw [hfix] at hmod
  have hV : Nat.card V6 = 64 := by rw [Nat.card_eq_fintype_card]; simp
  rw [hV] at hmod
  have hdvd : Nat.card F ∣ 64 := hV ▸ F.card_addSubgroup_dvd_card
  have hF64 : Nat.card F = 64 :=
    eq_64_of_dvd r hr _ (Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hdvd)) hdvd hmod.symm
  have hFtop : F = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [hF64, hV]
  have hσ1 : σ = 1 := Equiv.ext fun v => by
    have : v ∈ F := hFtop ▸ AddSubgroup.mem_top v
    exact this
  have hγ2 : γ * γ = 1 := by
    apply Subtype.ext
    refine Equiv.ext fun v => ?_
    have h1 : ∀ w, (γ : Equiv.Perm V6) w = w + (γ : Equiv.Perm V6) 0 := fun w => by
      have := congrArg (fun τ : Equiv.Perm V6 => τ w) hσ1
      simp only [σ, Λ, linPartHom_apply, Equiv.Perm.one_apply] at this
      calc (γ : Equiv.Perm V6) w = ((γ : Equiv.Perm V6) w + (γ : Equiv.Perm V6) 0) +
            (γ : Equiv.Perm V6) 0 := by rw [add_assoc, v6_add_self, add_zero]
        _ = w + (γ : Equiv.Perm V6) 0 := by rw [this]
    simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, Subgroup.coe_one, Equiv.Perm.one_apply]
    rw [h1, h1 v, add_assoc, v6_add_self, add_zero]
  have := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hγ2 : γ ^ 2 = 1)
  rw [hγ] at this
  have := Nat.le_of_dvd (by norm_num) this
  rcases hr with rfl | rfl <;> omega

theorem translations_of_full [Finite G] (hO : ∀ v, v ∈ MulAction.orbit Γ (0 : V6)) :
    ∀ w : V6, ∃ γ ∈ Γ, ∀ v, γ v = v + w := by
  classical
  let W₀ : AddSubgroup V6 :=
    { carrier := {w | ∃ γ ∈ Γ, ∀ v, γ v = v + w}
      zero_mem' := ⟨1, one_mem Γ, fun v => by simp⟩
      add_mem' := fun {w w'} ⟨γ, hγ, h1⟩ ⟨δ, hδ, h2⟩ =>
        ⟨γ * δ, mul_mem hγ hδ, fun v => by
          rw [Equiv.Perm.mul_apply, h1, h2]; abel⟩
      neg_mem' := fun {w} hw => by
        change ∃ γ ∈ Γ, ∀ v, γ v = v + -w
        rw [v6_neg]
        exact hw }
  have hW₀P : ∀ x ∈ P, ∀ w ∈ W₀, lin ψ x w ∈ W₀ := by
    rintro x hx w ⟨γ, hγ, h1⟩
    set σ := hS.linP ⟨x, hx⟩
    have hσΓ : σ ∈ Γ := hPΓ ⟨⟨x, hx⟩, rfl⟩
    have hσadd : σ ∈ linGroup := hS.rad.linHom_mem_linGroup _
    refine ⟨σ * γ * σ⁻¹, mul_mem (mul_mem hσΓ hγ) (inv_mem hσΓ), fun v => ?_⟩
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, hσadd, perm_apply_inv]
    rfl
  by_cases htop : W₀ = ⊤
  · intro w
    have : w ∈ W₀ := htop ▸ AddSubgroup.mem_top w
    exact this
  exfalso
  have hbot : W₀ = ⊥ := by
    by_contra hne
    exact htop (eq_top_of_ne_bot_v6 hS.rad hW₀P hne)
  set Λ := linPartHom Γ hΓaff
  have hinj : Function.Injective Λ := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have h1 : ∀ v, (γ : Equiv.Perm V6) v = v + (γ : Equiv.Perm V6) 0 := fun v => by
      have := congrArg (fun τ : Equiv.Perm V6 => τ v) hγ
      simp only [Λ, linPartHom_apply, Equiv.Perm.one_apply] at this
      calc (γ : Equiv.Perm V6) v = ((γ : Equiv.Perm V6) v + (γ : Equiv.Perm V6) 0) +
            (γ : Equiv.Perm V6) 0 := by rw [add_assoc, v6_add_self, add_zero]
        _ = v + (γ : Equiv.Perm V6) 0 := by rw [this]
    have h0 : (γ : Equiv.Perm V6) 0 ∈ W₀ := ⟨γ, γ.2, h1⟩
    rw [hbot, AddSubgroup.mem_bot] at h0
    apply Subtype.ext
    exact Equiv.ext fun v => by rw [h1, h0, add_zero]; rfl
  set X := Λ.range
  have hOcard : Nat.card (MulAction.orbit Γ (0 : V6)) = 64 := by
    have hset : MulAction.orbit Γ (0 : V6) = Set.univ := Set.eq_univ_of_forall hO
    rw [hset, Nat.card_univ, Nat.card_eq_fintype_card]
    simp
  have hcardX : Nat.card X = 32 * oBound ε := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, card_eq hS hΓ0 hPΓ, hOcard]
    have h2 := oBound_even ε
    omega
  have hob : 0 < oBound ε := by cases ε <;> decide
  have hlinP : ∀ x ∈ P, ∃ σ ∈ X, ∀ v, σ v = lin ψ x v := by
    intro x hx
    refine ⟨Λ ⟨hS.linP ⟨x, hx⟩, hPΓ ⟨⟨x, hx⟩, rfl⟩⟩, ⟨_, rfl⟩, fun v => ?_⟩
    simp only [Λ, linPartHom_apply]
    rw [linP_zero hS ⟨_, ⟨⟨x, hx⟩, rfl⟩⟩, add_zero]
    rfl
  have hXlin : ∀ σ ∈ X, σ ∈ linGroup := by
    rintro _ ⟨γ, rfl⟩
    exact linPartHom_mem_linGroup hΓaff γ
  by_cases horth : X ≤ orthGroup ε
  · have := (Subgroup.card_le_of_le horth).trans (card_orthGroup_le ε)
    omega
  obtain ⟨σ, hσX, hσo⟩ := Set.not_subset.1 horth
  have hσlin := hXlin σ hσX
  obtain ⟨v₁, hv₁⟩ : ∃ v, qfV ε (σ v) ≠ qfV ε v := by
    by_contra hcon
    push Not at hcon
    exact hσo ⟨hσlin, hcon⟩
  have he₀ : (Pi.single 0 1 : V6) ≠ 0 := fun h => by
    have := congrFun h 0
    simp at this
  have hte₀ : (Pi.single 0 1 : V6) = toVec 6 1 := by rw [← toVec_two_pow' 0]; rfl
  have hqe₀ : qfV ε (Pi.single 0 1 : V6) = 0 := by
    rw [hte₀, qfV_toVec ε (by norm_num), qfB_one]
    rfl
  have hl0 : σ 0 = 0 := map_zero_of_mem_linGroup hσlin
  have hv0 : v₁ ≠ 0 := fun h => hv₁ (by rw [h, hl0])
  have hu0 : σ v₁ ≠ 0 := fun h => hv0 (σ.injective (h.trans hl0.symm))
  have htrans : ∀ w : V6, w ≠ 0 → ∃ τ ∈ X, τ (Pi.single 0 1) = w := by
    intro w hw0
    rcases qfV_cases ε w with hw | hw
    · obtain ⟨x, hx, hxw⟩ := hS.rad.exists_lin_eq he₀ hw0 (hqe₀.trans hw.symm)
      obtain ⟨τ, hτX, hτ⟩ := hlinP x hx
      exact ⟨τ, hτX, by rw [hτ, hxw]⟩
    · rcases qfV_cases ε v₁ with h0 | h1
      · have hq1 : qfV ε (σ v₁) = 1 :=
          (qfV_cases ε _).resolve_left fun h => hv₁ (h.trans h0.symm)
        obtain ⟨x₁, hx₁, hx₁v⟩ := hS.rad.exists_lin_eq he₀ hv0 (hqe₀.trans h0.symm)
        obtain ⟨x₂, hx₂, hx₂w⟩ := hS.rad.exists_lin_eq hu0 hw0 (hq1.trans hw.symm)
        obtain ⟨τ₁, hτ₁X, hτ₁⟩ := hlinP x₁ hx₁
        obtain ⟨τ₂, hτ₂X, hτ₂⟩ := hlinP x₂ hx₂
        refine ⟨τ₂ * σ * τ₁, mul_mem (mul_mem hτ₂X hσX) hτ₁X, ?_⟩
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτ₁, hx₁v, hτ₂, hx₂w]
      · have hq0 : qfV ε (σ v₁) = 0 :=
          (qfV_cases ε _).resolve_right fun h => hv₁ (h.trans h1.symm)
        obtain ⟨x₁, hx₁, hx₁v⟩ := hS.rad.exists_lin_eq he₀ hu0 (hqe₀.trans hq0.symm)
        obtain ⟨x₂, hx₂, hx₂w⟩ := hS.rad.exists_lin_eq hv0 hw0 (h1.trans hw.symm)
        obtain ⟨τ₁, hτ₁X, hτ₁⟩ := hlinP x₁ hx₁
        obtain ⟨τ₂, hτ₂X, hτ₂⟩ := hlinP x₂ hx₂
        refine ⟨τ₂ * σ⁻¹ * τ₁, mul_mem (mul_mem hτ₂X (inv_mem hσX)) hτ₁X, ?_⟩
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτ₁, hx₁v, perm_inv_apply, hτ₂, hx₂w]
  have horb : Nat.card (MulAction.orbit X (Pi.single 0 1 : V6)) = 63 := by
    have e : MulAction.orbit X (Pi.single 0 1 : V6) ≃ {w : V6 // w ≠ 0} :=
      { toFun := fun w => ⟨w.1, by
          obtain ⟨τ, hτ⟩ := w.2
          intro h
          have hτlin := hXlin τ τ.2
          have h1 : (τ : Equiv.Perm V6) (Pi.single 0 1) = (τ : Equiv.Perm V6) 0 := by
            rw [map_zero_of_mem_linGroup hτlin, ← h]
            exact hτ
          exact he₀ ((τ : Equiv.Perm V6).injective h1)⟩
        invFun := fun w => ⟨w.1, by
          obtain ⟨τ, hτX, hτ⟩ := htrans w.1 w.2
          exact ⟨⟨τ, hτX⟩, hτ⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_ne',
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    simp
  have hos := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup X (Pi.single 0 1 : V6))
  rw [Nat.card_prod, horb, hcardX] at hos
  cases ε
  ·
    have hstab : Nat.card (MulAction.stabilizer X (Pi.single 0 1 : V6)) = 20480 := by
      simp only [oBound] at hos
      omega
    obtain ⟨hcube, hfix, hmove⟩ := Setup.plus_gen0_facts
    obtain ⟨σ₃, hσ₃X, hσ₃⟩ := hlinP (p 0) (hS.rad.p_mem 0)
    have hσ₃' : ∀ w, σ₃ w = genMat .plus 0 *ᵥ w := fun w => by rw [hσ₃, hS.rad.lin_p 0 w]; rfl
    have hσ₃e : σ₃ (Pi.single 0 1) = Pi.single 0 1 := by
      rw [hσ₃', hte₀, genMat, mulVec_toVec, hfix]
    have hσ₃3 : σ₃ ^ 3 = 1 := Equiv.ext fun w => by
      rw [pow_succ, pow_succ, pow_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hσ₃',
        hσ₃', hσ₃', ← toVec_vecBits w, genMat, mulVec_toVec, mulVec_toVec, mulVec_toVec,
        hcube _ (vecBits_lt w)]
      rfl
    have hσ₃1 : σ₃ ≠ 1 := fun h => by
      have h2 := congrArg (fun τ : Equiv.Perm V6 => τ (toVec 6 2)) h
      simp only [hσ₃', genMat, mulVec_toVec, Equiv.Perm.coe_one, id] at h2
      exact hmove (toVec_injective (bmulVec_lt _ _) (by norm_num) h2)
    let s : MulAction.stabilizer X (Pi.single 0 1 : V6) := ⟨⟨σ₃, hσ₃X⟩, hσ₃e⟩
    have hs3 : orderOf s = 3 := by
      refine orderOf_eq_prime ?_ ?_
      · exact Subtype.ext (Subtype.ext hσ₃3)
      · intro h
        exact hσ₃1 (congrArg (fun z : MulAction.stabilizer X (Pi.single 0 1 : V6) =>
          ((z : X) : Equiv.Perm V6)) h)
    have := orderOf_dvd_natCard s
    rw [hs3, hstab] at this
    norm_num at this
  ·
    simp only [oBound] at hos
    omega

theorem affine_dichotomy [Finite G] :
    (∀ γ ∈ Γ, γ 0 = 0) ∨ (∀ w : V6, ∃ γ ∈ Γ, ∀ v, γ v = v + w) := by
  by_cases h0 : ∀ γ ∈ Γ, γ 0 = 0
  · exact Or.inl h0
  right
  push Not at h0
  obtain ⟨γ₀, hγ₀, hne⟩ := h0
  have hv₀ : γ₀ 0 ∈ MulAction.orbit Γ (0 : V6) := mem_orbit_iff.2 ⟨γ₀, hγ₀, rfl⟩
  have hsame : ∀ v ∈ MulAction.orbit Γ (0 : V6), v ≠ 0 → ∀ w, w ≠ 0 → qfV ε w = qfV ε v →
      w ∈ MulAction.orbit Γ (0 : V6) := by
    intro v hv hv0 w hw hq
    obtain ⟨x, hx, hxw⟩ := hS.rad.exists_lin_eq hv0 hw hq.symm
    rw [← hxw]
    exact lin_mem_orbit hS hPΓ hv hx
  have h0O : (0 : V6) ∈ MulAction.orbit Γ (0 : V6) := mem_orbit_iff.2 ⟨1, one_mem _, rfl⟩
  by_cases hboth : ∃ v ∈ MulAction.orbit Γ (0 : V6), v ≠ 0 ∧ qfV ε v ≠ qfV ε (γ₀ 0)
  · obtain ⟨v₁, hv₁, hv₁0, hv₁q⟩ := hboth
    refine translations_of_full hS hΓ0 hPΓ hΓaff fun w => ?_
    by_cases hw0 : w = 0
    · rw [hw0]; exact h0O
    by_cases hq : qfV ε w = qfV ε (γ₀ 0)
    · exact hsame _ hv₀ hne w hw0 hq
    · refine hsame v₁ hv₁ hv₁0 w hw0 ?_
      rcases qfV_cases ε w with h1 | h1 <;> rcases qfV_cases ε v₁ with h2 | h2 <;>
        rcases qfV_cases ε (γ₀ 0) with h3 | h3 <;> simp_all
  · push Not at hboth
    have hO : ∀ v, v ∈ MulAction.orbit Γ (0 : V6) ↔ (v = 0 ∨ qfV ε v = qfV ε (γ₀ 0)) := by
      intro v
      constructor
      · intro hv
        by_cases hv0 : v = 0
        · exact Or.inl hv0
        · exact Or.inr (hboth v hv hv0)
      · rintro (rfl | hq)
        · exact h0O
        · by_cases hv0 : v = 0
          · rw [hv0]; exact h0O
          · exact hsame _ hv₀ hne v hv0 hq
    exfalso
    rcases qfV_cases ε (γ₀ 0) with hq | hq
    · refine false_of_cone_orbit hS hΓ0 hPΓ hΓaff fun v => ?_
      rw [hO, hq]
      constructor
      · rintro (rfl | h)
        · exact qfV_zero ε
        · exact h
      · exact fun h => Or.inr h
    · exact false_of_ns_orbit hS hΓ0 hPΓ hΓaff fun v => by rw [hO, hq]

end Dich

end CFSG.EvenSmallLie.OmegaEight.Chain
