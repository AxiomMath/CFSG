module

public import CFSG.LargeExtraspecial.FS77A3
public import CFSG.LargeExtraspecial.FS77Orth
public import CFSG.LargeExtraspecial.FS77A2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.FS77

open Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

namespace CaseA

variable (D : CaseA S)

theorem three_le_finrank_N : 3 ≤ finrank (ZMod 2) D.N := by
  rw [D.finrank_N]
  have := D.hw
  omega

theorem exists_ρN_eq_eichler (s u : D.N) : ∃ x : D.X, D.ρN x = eichler D.qN s u :=
  D.mem_range_ρN (eichler_mem_omegaGroup D.qN_nondegenerate s u)

theorem eq_bot_or_top (W : Submodule (ZMod 2) D.N)
    (hW : ∀ x : D.X, ∀ v ∈ W, D.ρN x v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  refine eichler_invariant_submodule D.qN_nondegenerate D.three_le_finrank_N W
    fun s u _ _ v hv => ?_
  obtain ⟨x, hx⟩ := D.exists_ρN_eq_eichler s u
  rw [← hx]
  exact hW x v hv

theorem eq_zero_or_id (θ : D.N →ₗ[ZMod 2] D.N) (hθ : ∀ x : D.X, ∀ v, θ (D.ρN x v) = D.ρN x (θ v)) :
    θ = 0 ∨ θ = LinearMap.id := by
  refine eichler_commute_endo D.qN_nondegenerate D.three_le_finrank_N θ fun s u _ _ v => ?_
  obtain ⟨x, hx⟩ := D.exists_ρN_eq_eichler s u
  rw [← hx]
  exact hθ x v

theorem card_N : Nat.card D.N = 2 ^ (2 * S.width - 2) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, D.finrank_N]

@[expose] noncomputable def fixN (R : Subgroup D.X) : Submodule (ZMod 2) D.N where
  carrier := {v | ∀ r ∈ R, D.ρN r v = v}
  add_mem' hv hw r hr := by rw [map_add, hv r hr, hw r hr]
  zero_mem' r _ := map_zero _
  smul_mem' c v hv r hr := by rw [map_smul, hv r hr]

theorem le_K_of_normal (R : Subgroup D.X) (hRn : R.Normal) (hR2 : IsPGroup 2 R) : R ≤ D.K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction R D.N := MulAction.compHom D.N (D.ρN.comp R.subtype)
  have hfix : ∀ v ∈ MulAction.fixedPoints R D.N, v ∈ D.fixN R := fun v hv r hr => hv ⟨r, hr⟩
  have hmod := hR2.card_modEq_card_fixedPoints D.N
  rw [D.card_N] at hmod
  have h2 : 2 ∣ Nat.card (MulAction.fixedPoints R D.N) := by
    have h0 : 2 ^ (2 * S.width - 2) % 2 = 0 := by
      have := D.hw
      exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
    have h3 := hmod.symm
    unfold Nat.ModEq at h3
    exact Nat.dvd_of_mod_eq_zero (by omega)
  have hne : D.fixN R ≠ ⊥ := by
    intro hbot
    have h0 : (0 : D.N) ∈ MulAction.fixedPoints R D.N := fun r =>
      show D.ρN (r : D.X) 0 = 0 from map_zero _
    have hsub : MulAction.fixedPoints R D.N = {0} := by
      ext v
      refine ⟨fun hv => ?_, fun hv => by rw [Set.mem_singleton_iff.mp hv]; exact h0⟩
      have := hfix v hv
      rw [hbot, Submodule.mem_bot] at this
      exact Set.mem_singleton_iff.mpr this
    rw [hsub, Nat.card_unique] at h2
    exact absurd h2 (by norm_num)
  have htop : D.fixN R = ⊤ := by
    refine (D.eq_bot_or_top (D.fixN R) fun x v hv r hr => ?_).resolve_left hne
    have hr' : x⁻¹ * r * x ∈ R := by
      have := hRn.conj_mem r hr x⁻¹
      rwa [inv_inv] at this
    have h1 := hv _ hr'
    calc D.ρN r (D.ρN x v) = D.ρN x (D.ρN (x⁻¹ * r * x) v) := by
          rw [map_mul, map_mul, map_inv]
          simp [LinearEquiv.mul_apply]
      _ = D.ρN x v := by rw [h1]
  intro r hr
  refine D.mem_K.mpr (LinearEquiv.ext fun v => ?_)
  have hv : v ∈ D.fixN R := by rw [htop]; exact Submodule.mem_top
  exact hv r hr

theorem mem_K_of_normal {R : Subgroup G} (hRX : R ≤ D.X)
    (hRn : ∀ x ∈ D.X, ∀ r ∈ R, x * r * x⁻¹ ∈ R) (hR2 : IsPGroup 2 R) {r : G} (hr : r ∈ R) :
    (⟨r, hRX hr⟩ : D.X) ∈ D.K := by
  refine D.le_K_of_normal (R.subgroupOf D.X) ⟨fun n hn x => ?_⟩ ?_ (mem_subgroupOf.mpr hr)
  · rw [mem_subgroupOf] at hn ⊢
    exact hRn x x.2 n hn
  · intro u
    obtain ⟨n, hn⟩ := hR2 ⟨((u : D.X) : G), mem_subgroupOf.mp u.2⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this

@[expose] def IsAorAZ (g' : G) : Prop := g' * S.z * g'⁻¹ = D.a ∨ g' * S.z * g'⁻¹ = D.a * S.z

theorem az_mem_QG : D.a * S.z ∈ S.QG := mul_mem D.a_mem_QG S.z_mem_QG

theorem IsAorAZ.mem_QG {g' : G} (hc : D.IsAorAZ g') : g' * S.z * g'⁻¹ ∈ S.QG := by
  rcases hc with h | h <;> rw [h]
  exacts [D.a_mem_QG, D.az_mem_QG]

theorem IsAorAZ.ne_z {g' : G} (hc : D.IsAorAZ g') : g' * S.z * g'⁻¹ ≠ S.z := by
  rcases hc with h | h <;> rw [h]
  exacts [D.a_ne_z, D.az_ne_z]

theorem mem_X_of_commute {g' : G} (hc : D.IsAorAZ g') {x : G} (hxz : x * S.z = S.z * x)
    (hxc : x * (g' * S.z * g'⁻¹) = (g' * S.z * g'⁻¹) * x) : x ∈ D.X := by
  refine D.mem_X.mpr ⟨hxz, ?_⟩
  rcases hc with h | h
  · rwa [h] at hxc
  · rw [h] at hxc
    calc x * D.a = x * (D.a * S.z) * S.z := by rw [mul_assoc, mul_assoc, S.z_mul_z, mul_one]
      _ = D.a * S.z * x * S.z := by rw [hxc]
      _ = D.a * (S.z * x * S.z) := by simp only [mul_assoc]
      _ = D.a * x := by rw [← hxz, mul_assoc, S.z_mul_z, mul_one]

theorem commute_of_mem_X {g' : G} (hc : D.IsAorAZ g') {x : G} (hx : x ∈ D.X) :
    x * (g' * S.z * g'⁻¹) = (g' * S.z * g'⁻¹) * x := by
  obtain ⟨hxz, hxa⟩ := D.mem_X.mp hx
  rcases hc with h | h <;> rw [h]
  · exact hxa
  · rw [← mul_assoc, hxa, mul_assoc, hxz, mul_assoc]

theorem L0_le_X {g' : G} (hc : D.IsAorAZ g') : S.L0 g' ≤ D.X := by
  intro l hl
  refine D.mem_X_of_commute hc (S.z_comm hl.2) ?_
  exact (S.conjBy g').z_comm_QG hl.1

theorem conj_mem_L0 {g' : G} (hc : D.IsAorAZ g') {x : G} (hx : x ∈ D.X) {l : G}
    (hl : l ∈ S.L0 g') : x * l * x⁻¹ ∈ S.L0 g' := by
  refine ⟨?_, ?_⟩
  · have hxM : x ∈ (S.conjBy g').M := by
      rw [Setting.mem_M_iff]
      exact D.commute_of_mem_X hc hx
    exact (S.conjBy g').conj_mem_QG hxM hl.1
  · exact S.M.mul_mem (S.M.mul_mem (D.X_le_M hx) hl.2) (S.M.inv_mem (D.X_le_M hx))

omit [Finite G] in
theorem isPGroup_L0' [Finite G] (g' : G) : IsPGroup 2 (S.L0 g') := by
  have h : IsPGroup 2 (S.Qa g') := by
    refine IsPGroup.of_card (n := 1 + 2 * S.width) ?_
    rw [S.card_Qa, S.card_QG_eq_card_Q, S.card_Q_eq]
  exact h.to_le (S.L0_le_Qa g')

theorem L0_mem_K {g' : G} (hc : D.IsAorAZ g') {l : G} (hl : l ∈ S.L0 g') :
    (⟨l, D.L0_le_X hc hl⟩ : D.X) ∈ D.K :=
  D.mem_K_of_normal (D.L0_le_X hc) (fun _ hx _ hl => D.conj_mem_L0 hc hx hl)
    (isPGroup_L0' (S := S) g') hl

@[expose] noncomputable def L0toX {g' : G} (hc : D.IsAorAZ g') : S.L0 g' →* D.X :=
  inclusion (D.L0_le_X hc)

theorem L0toX_mem_K {g' : G} (hc : D.IsAorAZ g') (l : S.L0 g') : D.L0toX hc l ∈ D.K :=
  D.L0_mem_K hc l.2

@[expose] noncomputable def ψL0hom {g' : G} (hc : D.IsAorAZ g') :
    S.L0 g' →* Multiplicative D.N where
  toFun l := Multiplicative.ofAdd (D.ψ (D.L0toX hc l))
  map_one' := by rw [map_one, D.ψ_one, ofAdd_zero]
  map_mul' l l' := by
    rw [map_mul, D.ψ_mul (D.L0toX_mem_K hc l) (D.L0toX_mem_K hc l'), ofAdd_add]

theorem ψL0hom_apply {g' : G} (hc : D.IsAorAZ g') (l : S.L0 g') :
    Multiplicative.toAdd (D.ψL0hom hc l) = D.ψ (D.L0toX hc l) := rfl

@[expose] noncomputable def ψL0 {g' : G} (hc : D.IsAorAZ g') : Submodule (ZMod 2) D.N where
  carrier := {v | ∃ l : S.L0 g', D.ψ (D.L0toX hc l) = v}
  add_mem' := by
    rintro _ _ ⟨l, rfl⟩ ⟨l', rfl⟩
    exact ⟨l * l', by rw [map_mul, D.ψ_mul (D.L0toX_mem_K hc l) (D.L0toX_mem_K hc l')]⟩
  zero_mem' := ⟨1, by rw [map_one, D.ψ_one]⟩
  smul_mem' := by
    rintro c _ ⟨l, rfl⟩
    rcases (show c = 0 ∨ c = 1 by revert c; decide) with rfl | rfl
    · exact ⟨1, by rw [map_one, D.ψ_one, zero_smul]⟩
    · exact ⟨l, by rw [one_smul]⟩

theorem ψL0_eq_top {g' : G} (hc : D.IsAorAZ g') : D.ψL0 hc = ⊤ := by
  refine (D.eq_bot_or_top (D.ψL0 hc) ?_).resolve_left ?_
  · rintro x _ ⟨l, rfl⟩
    refine ⟨⟨x * l * (x : G)⁻¹, D.conj_mem_L0 hc x.2 l.2⟩, ?_⟩
    rw [← D.ψ_conj x (D.L0toX_mem_K hc l)]
    rfl
  · intro hbot
    have hle : S.L0 g' ≤ S.QG ⊓ S.Qa g' := by
      intro l hl
      refine ⟨?_, hl.1⟩
      have h1 : D.ψ (D.L0toX hc ⟨l, hl⟩) ∈ D.ψL0 hc := ⟨⟨l, hl⟩, rfl⟩
      rw [hbot, Submodule.mem_bot] at h1
      exact (D.ψ_eq_zero_iff (D.L0toX_mem_K hc ⟨l, hl⟩)).mp h1
    have h1 := Subgroup.card_le_of_le hle
    rw [S.card_L0 hc.mem_QG hc.ne_z] at h1
    have h2 := h1.trans (S.card_QG_inf_Qa_le hc.ne_z)
    have h3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
    have := D.hw
    omega

theorem exists_mem_L0_ψ_eq {g' : G} (hc : D.IsAorAZ g') (v : D.N) :
    ∃ l : S.L0 g', D.ψ (D.L0toX hc l) = v := by
  have hv : v ∈ D.ψL0 hc := by rw [D.ψL0_eq_top hc]; exact Submodule.mem_top
  exact hv

theorem card_QG_inf_Qa {g' : G} (hc : D.IsAorAZ g') :
    Nat.card (S.QG ⊓ S.Qa g' : Subgroup G) = 4 := by
  have hrange : (D.ψL0hom hc).range = ⊤ := by
    refine eq_top_iff.mpr fun v _ => ?_
    obtain ⟨l, hl⟩ := D.exists_mem_L0_ψ_eq hc (Multiplicative.toAdd v)
    refine ⟨l, ?_⟩
    rw [← ofAdd_toAdd v, ← hl]
    rfl
  have hker : (D.ψL0hom hc).ker = S.QG.subgroupOf (S.L0 g') := by
    ext l
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← toAdd_eq_zero, D.ψL0hom_apply]
    exact D.ψ_eq_zero_iff (D.L0toX_mem_K hc l)
  have hinf : S.QG ⊓ S.L0 g' = S.QG ⊓ S.Qa g' := by
    rw [Setting.L0, ← inf_assoc, inf_right_comm, inf_eq_left.mpr S.QG_le_M]
  have h := card_ker_mul_card_range (D.ψL0hom hc)
  rw [hrange, hker, ← inf_subgroupOf_right,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : S.QG ⊓ S.L0 g' ≤ S.L0 g')).toEquiv,
    hinf, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, D.card_N,
    S.card_L0 hc.mem_QG hc.ne_z] at h
  have hw := D.hw
  have h2 : 2 ^ (2 * S.width) = 4 * 2 ^ (2 * S.width - 2) := by
    rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  rw [h2] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

theorem az_ne_one : D.a * S.z ≠ 1 := by
  intro h
  apply D.a_ne_z
  calc D.a = D.a * S.z * S.z := D.a_mul_z_mul_z.symm
    _ = S.z := by rw [h, one_mul]

theorem az_ne_a : D.a * S.z ≠ D.a := by
  intro h
  apply S.z_ne_one
  calc S.z = D.a⁻¹ * (D.a * S.z) := by group
    _ = 1 := by rw [h, inv_mul_cancel]

theorem four_mem_QG_inf_Qa {g' : G} (hc : D.IsAorAZ g') :
    S.z ∈ S.QG ⊓ S.Qa g' ∧ D.a ∈ S.QG ⊓ S.Qa g' ∧ D.a * S.z ∈ S.QG ⊓ S.Qa g' := by
  have hz : S.z ∈ S.Qa g' := S.z_mem_Qa_of_mem_QG rfl hc.mem_QG hc.ne_z
  have hcQ : g' * S.z * g'⁻¹ ∈ S.Qa g' := (S.conjBy g').z_mem_QG
  refine ⟨⟨S.z_mem_QG, hz⟩, ⟨D.a_mem_QG, ?_⟩, ⟨D.az_mem_QG, ?_⟩⟩
  · rcases hc with h | h
    · rwa [h] at hcQ
    · rw [h] at hcQ
      have := mul_mem hcQ hz
      rwa [D.a_mul_z_mul_z] at this
  · rcases hc with h | h
    · rw [h] at hcQ
      exact mul_mem hcQ hz
    · rwa [h] at hcQ

theorem mem_QG_inf_Qa_iff {g' : G} (hc : D.IsAorAZ g') {x : G} :
    x ∈ S.QG ⊓ S.Qa g' ↔ x = 1 ∨ x = S.z ∨ x = D.a ∨ x = D.a * S.z := by
  classical
  obtain ⟨hz, ha, haz⟩ := D.four_mem_QG_inf_Qa hc
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · by_contra hne
    push Not at hne
    obtain ⟨h1, h2, h3, h4⟩ := hne
    set F : Finset G := {x, 1, S.z, D.a, D.a * S.z} with hF
    have hsub : (F : Set G) ⊆ (S.QG ⊓ S.Qa g' : Subgroup G) := by
      intro y hy
      simp only [hF, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      exacts [hx, one_mem _, hz, ha, haz]
    have hcard : F.card = 5 := by
      rw [hF, Finset.card_insert_of_notMem (by simp [h1, h2, h3, h4]),
        Finset.card_insert_of_notMem (by simp [S.z_ne_one.symm, D.a_ne_one.symm,
          D.az_ne_one.symm]),
        Finset.card_insert_of_notMem (by simp [D.a_ne_z.symm, D.az_ne_z.symm]),
        Finset.card_pair D.az_ne_a.symm]
    have h5 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, hcard, ← Nat.card_coe_set_eq] at h5
    have h6 : Nat.card ((S.QG ⊓ S.Qa g' : Subgroup G) : Set G) = 4 := D.card_QG_inf_Qa hc
    omega
  · rcases hx with rfl | rfl | rfl | rfl
    exacts [one_mem _, hz, ha, haz]

end CaseA

end CFSG.LargeExtraspecial.FS77
