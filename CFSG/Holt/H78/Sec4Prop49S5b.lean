module

public import CFSG.Holt.H78.Sec4Prop49S5
import CFSG.Holt.H78.Sec4KnownKV
public import CFSG.Holt.H78.Sec4SEAut

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open scoped Pointwise

namespace P49Config

section Defs

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {α : Ω} {v : G}
  (C : P49Config G Ω α v)

structure P95 [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] : Prop where
  setting : Sec4Setting G Ω
  transitive : IsPretransitive (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β))
    (holtDelta G Ω α C.β)

@[expose] def Γ : Set Ω := orbit (stabilizer G α) C.β

abbrev K (_C : P49Config G Ω α v) : Subgroup G := Subgroup.closure (longInvAt G Ω α)

@[expose] def Ostar : Subgroup G := C.K ⊓ fixingSubgroup G C.Γ

abbrev rootZ : Subgroup (Equiv.Perm (C.D.Ψc C.i)) :=
  CFSG.GH74.Uniqueness.Bender.rootCenter (seRadical (C.D.M C.i) (C.D.coord C.a C.i))

structure P95Data where
  t : G
  u : G
  t_mem : t ∈ longInvAt G Ω α
  u_mem : u ∈ longInvAt G Ω α
  t_ne_u : t ≠ u
  commute : Commute t u
  mul_eq : t * u = v
  E : Subgroup G
  sylow : fusionIsSylowIn 2 E C.K
  t_mem_E : t ∈ E
  u_mem_E : u ∈ E

end Defs

section KLines

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {C : P49Config G Ω α v}

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem K_le_stabilizer (C : P49Config G Ω α v) : C.K ≤ stabilizer G α :=
  closure_longInvAt_le_stabilizer_point α

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem conj_mem_K {g : G} (hg : g ∈ stabilizer G α) {k : G} (hk : k ∈ C.K) :
    g * k * g⁻¹ ∈ C.K := by
  have := conj_mem_closure_longInvAt hk g
  rwa [mem_stabilizer_iff.mp hg] at this

theorem P95.exists_lineActs_rootZ (h : C.P95) {k : G} (hk : k ∈ C.K) :
    ∃ z ∈ C.rootZ, C.LineActs k z := by
  have hαa : (C.lpt (C.D.coord C.a C.i) : Ω) = α := by rw [C.lpt_coord_a, C.coe_a]
  induction hk using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨y, hyM, hy, hsy⟩ := C.exists_lineActs_of_mem_longInvAt h.setting h.transitive
      (ψ₀ := C.D.coord C.a C.i) (hαa ▸ hs)
    exact ⟨y, (C.isNaturalSE C.i).mem_rootCenter_seRadical hyM hy.2
      (mul_self_eq_one_of_mem_longInv hy.1), hsy⟩
  | one => exact ⟨1, Subgroup.one_mem _, C.lineActs_one⟩
  | mul k k' _ _ hk hk' =>
    obtain ⟨z, hz, hkz⟩ := hk
    obtain ⟨z', hz', hkz'⟩ := hk'
    exact ⟨z * z', Subgroup.mul_mem _ hz hz', hkz.mul hkz'⟩
  | inv k _ hk =>
    obtain ⟨z, hz, hkz⟩ := hk
    exact ⟨z⁻¹, Subgroup.inv_mem _ hz, hkz.inv⟩

theorem P95.smul_line_of_mem_K (h : C.P95) {k : G} (hk : k ∈ C.K) : k • C.line = C.line := by
  obtain ⟨z, -, hkz⟩ := h.exists_lineActs_rootZ hk
  exact hkz.smul_line

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem smul_Γ {g : G} (hg : g ∈ stabilizer G α) : g • C.Γ = C.Γ := by
  have := smul_orbit (⟨g, hg⟩ : stabilizer G α) C.β
  exact this

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem β_mem_Γ : C.β ∈ C.Γ := mem_orbit_self C.β

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem K_le_stabilizer_Γ : C.K ≤ stabilizer G C.Γ := fun _ hk =>
  mem_stabilizer_iff.mpr (smul_Γ (K_le_stabilizer C hk))

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_Γ_of_mem_line (C : P49Config G Ω α v) {ω : Ω} (hω : ω ∈ C.line) (hωα : ω ≠ α) :
    ω ∈ C.Γ := by
  obtain ⟨ψ, rfl⟩ := hω
  have hψ : ψ ≠ C.D.coord C.a C.i := by
    rintro rfl
    exact hωα (by simp only [C.lpt_coord_a, C.coe_a])
  obtain ⟨m, hm, hmb, hma⟩ := C.exists_mem_M_fix_apply_eq (Ne.symm C.coord_ne) hψ
  obtain ⟨c, -, hcm⟩ := C.exists_lineActs_of_mem hm
  have hcα : c • α = α := by rw [hcm.smul_α, hma, C.lpt_coord_a, C.coe_a]
  exact ⟨⟨c, hcα⟩, by
    show c • C.β = _
    rw [hcm.smul_β, hmb]⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_of_mem_Γ {γ : Ω} (hγ : γ ∈ C.Γ) :
    ∃ g ∈ stabilizer G α, g • C.β = γ := by
  obtain ⟨⟨g, hg⟩, rfl⟩ := hγ
  exact ⟨g, hg, rfl⟩

theorem P95.smul_mul_comm (h : C.P95) {k k' : G} (hk : k ∈ C.K) (hk' : k' ∈ C.K) {γ : Ω}
    (hγ : γ ∈ C.Γ) : (k * k') • γ = (k' * k) • γ ∧ (k * k) • γ = γ := by
  obtain ⟨g, hg, rfl⟩ := exists_of_mem_Γ hγ
  have hgi : g⁻¹ ∈ stabilizer G α := inv_mem hg
  obtain ⟨z, hz, hkz⟩ := h.exists_lineActs_rootZ (conj_mem_K hgi hk)
  obtain ⟨z', hz', hkz'⟩ := h.exists_lineActs_rootZ (conj_mem_K hgi hk')
  rw [inv_inv] at hkz hkz'
  have hzz : z * z' = z' * z := ((CFSG.GH74.Uniqueness.Bender.mem_rootCenter_iff.mp hz).2 _
    (CFSG.GH74.Uniqueness.Bender.rootCenter_le _ hz')).symm
  have hz2 : z * z = 1 := (C.isNaturalSE C.i).mul_self_eq_one_of_mem_rootCenter hz
  have hβb : C.β = C.lpt (C.D.coord C.b C.i) := by rw [C.lpt_coord_b]
  have e : ∀ x : G, x • g • C.β = g • ((g⁻¹ * x * g) • C.β) := fun x => by
    rw [smul_smul, smul_smul]
    congr 1
    group
  have e1 := (hkz.mul hkz') (C.D.coord C.b C.i)
  have e2 := (hkz'.mul hkz) (C.D.coord C.b C.i)
  have e3 := (hkz.mul hkz) (C.D.coord C.b C.i)
  rw [← hβb] at e1 e2 e3
  refine ⟨?_, ?_⟩
  · rw [e, e, show g⁻¹ * (k * k') * g = (g⁻¹ * k * g) * (g⁻¹ * k' * g) by group,
      show g⁻¹ * (k' * k) * g = (g⁻¹ * k' * g) * (g⁻¹ * k * g) by group, e1, e2, hzz]
  · rw [e, show g⁻¹ * (k * k) * g = (g⁻¹ * k * g) * (g⁻¹ * k * g) by group, e3, hz2,
      Equiv.Perm.one_apply, ← hβb]

end KLines

section Sylow

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {C : P49Config G Ω α v}

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_Ostar {g : G} : g ∈ C.Ostar ↔ g ∈ C.K ∧ ∀ γ ∈ C.Γ, g • γ = γ := by
  rw [Ostar, Subgroup.mem_inf, mem_fixingSubgroup_iff]

theorem P95.odd_card_Ostar (h : C.P95) : Odd (Nat.card C.Ostar) := by
  have hodd := h.setting.odd_fixingSubgroup_orbit (α := α) (Γ := C.Γ)
    ⟨C.β, C.β_mem_Γ, C.ne.symm, rfl⟩
  have hle : C.Ostar ≤ stabilizer G α ⊓ fixingSubgroup G C.Γ :=
    inf_le_inf_right _ (K_le_stabilizer C)
  exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hle)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem conj_mem_Ostar {g : G} (hg : g ∈ stabilizer G α) {o : G} (ho : o ∈ C.Ostar) :
    g * o * g⁻¹ ∈ C.Ostar := by
  rw [mem_Ostar] at ho ⊢
  refine ⟨conj_mem_K hg ho.1, fun γ hγ => ?_⟩
  have hγ' : g⁻¹ • γ ∈ C.Γ := by
    rw [← smul_Γ (inv_mem hg)]
    exact Set.smul_mem_smul_set hγ
  rw [mul_smul, mul_smul, ho.2 _ hγ', smul_inv_smul]

omit [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem nonempty_p95Data (C : P49Config G Ω α v) : Nonempty C.P95Data := by
  obtain ⟨t, ht, u, hu, htu, hc, htuv, -⟩ := C.isTypeL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPt : IsPGroup 2 (Subgroup.zpowers t) := isPGroup_zpowers_of_orderOf_eq_two ht.1.1
  have hPu : IsPGroup 2 (Subgroup.zpowers u) := isPGroup_zpowers_of_orderOf_eq_two hu.1.1
  have hnorm : Subgroup.zpowers u ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (mem_centralizer_zpowers_iff.mpr hc.eq.symm)
  have hP := hPt.to_sup_of_normal_left' hPu hnorm
  have hPK : Subgroup.zpowers t ⊔ Subgroup.zpowers u ≤ C.K :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure ht))
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure hu))
  obtain ⟨E, hPE, hE⟩ := exists_fusionIsSylowIn_ge hP hPK
  exact ⟨⟨t, u, ht, hu, htu, hc, htuv, E, hE,
    hPE (Subgroup.mem_sup_left (Subgroup.mem_zpowers t)),
    hPE (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))⟩⟩

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem rho_mem_rootCenter
    {π : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))}
    (hπ : (π : typeLSection G Ω v) ∈
      longInvAt (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) C.a) (j : C.D.ι) :
    C.D.ρ j π ∈ CFSG.GH74.Uniqueness.Bender.rootCenter
      (seRadical (C.D.M j) (C.D.coord C.a j)) := by
  have hy := C.D.rho_mem_longInvAt hπ j
  exact (C.isNaturalSE j).mem_rootCenter_seRadical
    (C.D.rho_mem_M_of_isNaturalSE (C.isNaturalSE j) _) hy.2 (mul_self_eq_one_of_mem_longInv hy.1)

namespace P95Data

variable (P : C.P95Data)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem E_le_K : P.E ≤ C.K := P.sylow.1

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem isPGroup_E : IsPGroup 2 P.E := P.sylow.2.1

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem E_le_stabilizer : P.E ≤ stabilizer G α := P.E_le_K.trans (K_le_stabilizer C)

theorem eq_one_of_mem_Ostar (h : C.P95) {e : G} (he : e ∈ P.E) (ho : e ∈ C.Ostar) : e = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(P.E ⊓ C.Ostar) := P.isPGroup_E.to_le inf_le_left
  have hodd : Odd (Nat.card ↥(P.E ⊓ C.Ostar)) :=
    Odd.of_dvd_nat h.odd_card_Ostar (Subgroup.card_dvd_of_le inf_le_right)
  have hb : P.E ⊓ C.Ostar = ⊥ := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    rw [hk] at hodd
    rcases k with _ | k
    · exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])
    · exact absurd hodd (by rw [pow_succ]; simp)
  have : e ∈ P.E ⊓ C.Ostar := ⟨he, ho⟩
  rwa [hb, Subgroup.mem_bot] at this

theorem eq_one_of_forall_smul_Γ (h : C.P95) {e : G} (he : e ∈ P.E)
    (hΓ : ∀ γ ∈ C.Γ, e • γ = γ) : e = 1 :=
  P.eq_one_of_mem_Ostar h he (mem_Ostar.mpr ⟨P.E_le_K he, hΓ⟩)

theorem commute_E (h : C.P95) {e e' : G} (he : e ∈ P.E) (he' : e' ∈ P.E) : e * e' = e' * e := by
  have h1 : e * e' * (e' * e)⁻¹ = 1 := P.eq_one_of_forall_smul_Γ h
    (mul_mem (mul_mem he he') (inv_mem (mul_mem he' he))) fun γ hγ => by
      have hK : (e' * e)⁻¹ ∈ C.K := inv_mem (mul_mem (P.E_le_K he') (P.E_le_K he))
      have hδ : (e' * e)⁻¹ • γ ∈ C.Γ := by
        rw [← mem_stabilizer_iff.mp (K_le_stabilizer_Γ hK)]
        exact Set.smul_mem_smul_set hγ
      rw [mul_smul, (h.smul_mul_comm (P.E_le_K he) (P.E_le_K he') hδ).1, smul_inv_smul]
  exact mul_inv_eq_one.mp h1

theorem mul_self_E (h : C.P95) {e : G} (he : e ∈ P.E) : e * e = 1 :=
  P.eq_one_of_forall_smul_Γ h (mul_mem he he) fun _ hγ =>
    (h.smul_mul_comm (P.E_le_K he) (P.E_le_K he) hγ).2

theorem exists_mem_E_eqOn (h : C.P95) {k : G} (hk : k ∈ C.K) :
    ∃ e ∈ P.E, ∀ γ ∈ C.Γ, e • γ = k • γ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKΓ : C.K ≤ stabilizer G C.Γ := K_le_stabilizer_Γ
  have hS := fusionIsSylowIn_inducedPerm (Ψ := C.Γ) (h := hKΓ) P.sylow
  have h2 : IsPGroup 2 (inducedPerm C.K C.Γ hKΓ) := by
    rintro ⟨π, hπ⟩
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨x, hx, hxπ⟩ := mem_inducedPerm.mp hπ
    refine Equiv.ext fun γ => Subtype.ext ?_
    show ((π (π γ) : C.Γ) : Ω) = γ
    rw [hxπ, hxπ]
    rw [smul_smul]
    exact (h.smul_mul_comm hx hx γ.2).2
  have heq : inducedPerm P.E C.Γ (P.sylow.1.trans hKΓ) = inducedPerm C.K C.Γ hKΓ :=
    (hS.2.2 _ le_rfl h2 hS.1).symm
  have hk' : inducedHom C.K C.Γ hKΓ ⟨k, hk⟩ ∈ inducedPerm P.E C.Γ (P.sylow.1.trans hKΓ) := by
    rw [heq]
    exact ⟨⟨k, hk⟩, rfl⟩
  obtain ⟨e, he, heπ⟩ := mem_inducedPerm.mp hk'
  exact ⟨e, he, fun γ hγ => (heπ ⟨γ, hγ⟩).symm⟩

theorem exists_mul_mem_normalizer (h : C.P95) {g : G} (hg : g ∈ stabilizer G α) :
    ∃ o ∈ C.Ostar, o * g ∈ Subgroup.normalizer (P.E : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E' := P.E.map (MulAut.conj g).toMonoidHom
  have hE' : fusionIsSylowIn 2 E' C.K := by
    refine fusionIsSylowIn_of_card_eq ?_ (P.isPGroup_E.map _) ?_
    · rintro _ ⟨e, he, rfl⟩
      exact conj_mem_K hg (P.E_le_K he)
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
        card_eq_of_fusionIsSylowIn P.sylow]
  obtain ⟨k, hk, hkE⟩ := exists_mem_conj_of_fusionIsSylowIn P.sylow hE'
  have hmemE' : ∀ x, x ∈ E' ↔ g⁻¹ * x * g ∈ P.E := fun x => by
    constructor
    · rintro ⟨e, he, rfl⟩
      simpa [mul_assoc] using he
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by simp [mul_assoc]⟩
  have hn : k⁻¹ * g ∈ Subgroup.normalizer (P.E : Set G) := by
    refine mem_normalizer_of_conj (fun e he => ?_) (fun e he => ?_)
    · have h1 : g * e * g⁻¹ ∈ E' := (hmemE' _).mpr (by simpa [mul_assoc] using he)
      have h2 := (hkE _).mp h1
      simpa [mul_assoc] using h2
    · have h1 : k * e * k⁻¹ ∈ E' := (hkE _).mpr (by simpa [mul_assoc] using he)
      have h2 := (hmemE' _).mp h1
      simpa [mul_assoc] using h2
  obtain ⟨e₀, he₀, he₀k⟩ := P.exists_mem_E_eqOn h hk
  have ho₁ : e₀⁻¹ * k ∈ C.Ostar := mem_Ostar.mpr ⟨mul_mem (inv_mem (P.E_le_K he₀)) hk,
    fun γ hγ => by rw [mul_smul, ← he₀k γ hγ, inv_smul_smul]⟩
  refine ⟨e₀ * (e₀⁻¹ * k)⁻¹ * e₀⁻¹,
    conj_mem_Ostar (P.E_le_stabilizer he₀) (inv_mem ho₁), ?_⟩
  have e : e₀ * (e₀⁻¹ * k)⁻¹ * e₀⁻¹ * g = e₀ * (k⁻¹ * g) := by group
  rw [e]
  exact mul_mem (Subgroup.le_normalizer he₀) hn

theorem exists_mem_normalizer_eqOn (h : C.P95) {g : G} (hg : g ∈ stabilizer G α) :
    ∃ n ∈ stabilizer G α, n ∈ Subgroup.normalizer (P.E : Set G) ∧
      (∀ γ ∈ C.Γ, n • γ = g • γ) ∧ ∀ x ∈ P.E, g * x = x * g → n * x = x * n := by
  obtain ⟨o, ho, hon⟩ := P.exists_mul_mem_normalizer h hg
  have hoα : o ∈ stabilizer G α := K_le_stabilizer C (mem_Ostar.mp ho).1
  refine ⟨o * g, mul_mem hoα hg, hon, fun γ hγ => ?_, fun x hx hgx => ?_⟩
  · have hgγ : g • γ ∈ C.Γ := by
      rw [← smul_Γ hg]
      exact Set.smul_mem_smul_set hγ
    rw [mul_smul, (mem_Ostar.mp ho).2 _ hgγ]
  · have hxα := P.E_le_stabilizer hx
    have h1 : (o * g) * x * (o * g)⁻¹ ∈ P.E := (Subgroup.mem_normalizer_iff.mp hon x).mp hx
    have h2 : (o * g) * x * (o * g)⁻¹ * x⁻¹ ∈ C.Ostar := by
      have e : (o * g) * x * (o * g)⁻¹ * x⁻¹ = o * (x * o⁻¹ * x⁻¹) := by
        rw [show (o * g) * x * (o * g)⁻¹ = o * (g * x * g⁻¹) * o⁻¹ by group,
          show g * x * g⁻¹ = x by rw [hgx, mul_inv_cancel_right]]
        group
      rw [e]
      exact mul_mem ho (conj_mem_Ostar hxα (inv_mem ho))
    have h3 := P.eq_one_of_mem_Ostar h (mul_mem h1 (inv_mem hx)) h2
    rw [mul_inv_eq_one] at h3
    calc o * g * x = (o * g) * x * (o * g)⁻¹ * (o * g) := by group
      _ = x * (o * g) := by rw [h3]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem v_mem_E : v ∈ P.E := by
  have h := mul_mem P.t_mem_E P.u_mem_E
  rwa [P.mul_eq] at h

theorem E_le_centralizer (h : C.P95) :
    P.E ≤ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) := fun _ he =>
  mem_centralizer_zpowers_iff.mpr (P.commute_E h he P.v_mem_E)

theorem closure_longInvAt_le (h : C.P95) :
    Subgroup.closure {π : Equiv.Perm (fixSet Ω (Subgroup.zpowers v)) |
      π ∈ typeLSection G Ω v ∧
        π ∈ longInvAt (Equiv.Perm (fixSet Ω (Subgroup.zpowers v))) (fixSet Ω (Subgroup.zpowers v))
          C.a} ≤
      inducedPerm P.E (fixSet Ω (Subgroup.zpowers v))
        ((P.E_le_centralizer h).trans (centralizer_le_stabilizer_fixSet _)) := by
  have hS := h.setting
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Φ := fixSet Ω (Subgroup.zpowers v)
  set S : Set (Equiv.Perm Φ) := {π | π ∈ typeLSection G Ω v ∧
    π ∈ longInvAt (Equiv.Perm Φ) Φ C.a} with hSdef
  set CK : Subgroup G := C.K ⊓ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)
  have hCKΦ : CK ≤ stabilizer G Φ := inf_le_right.trans (centralizer_le_stabilizer_fixSet _)
  have hEC : P.E ≤ CK := fun e he => ⟨P.E_le_K he, P.E_le_centralizer h he⟩
  have hESyl : fusionIsSylowIn 2 P.E CK :=
    ⟨hEC, P.isPGroup_E, fun Q hQ hQp hEQ => P.sylow.2.2 Q (hQ.trans inf_le_left) hQp hEQ⟩
  have hÊ := fusionIsSylowIn_inducedPerm (Ψ := Φ) (h := hCKΦ) hESyl
  have h3 := three_le_card_fixSet_of_isTypeL hS.star C.isTypeL
  have hSC : S ⊆ inducedPerm CK Φ hCKΦ := by
    rintro π ⟨hπK, hπJ⟩
    obtain ⟨c, hc, hcv, hcπ⟩ := (hS.mem_longInvAt_centralizerImage_iff C.isPGroup_zpowers h3
      ⟨π, hπK⟩).mp (mem_longInvAt_subgroup_iff.mpr hπJ)
    exact mem_inducedPerm.mpr ⟨c, ⟨Subgroup.subset_closure (C.coe_a ▸ hc), hcv⟩, hcπ⟩
  have hjH : ∀ {π : Equiv.Perm Φ} (hπ : π ∈ S), (⟨π, hπ.1⟩ : typeLSection G Ω v) ∈
      jHull (typeLSection G Ω v) Φ := fun hπ =>
    mem_jHull_of_mem_longInv (mem_longInvAt_subgroup_iff.mpr hπ.2).1
  have hcomm : ∀ π ∈ S, ∀ π' ∈ S, π * π' = π' * π := by
    intro π hπ π' hπ'
    have e := C.D.eq_of_forall_rho_eq C.jOddCore_eq_bot
      (h := ⟨⟨π, hπ.1⟩, hjH hπ⟩ * ⟨⟨π', hπ'.1⟩, hjH hπ'⟩)
      (h' := ⟨⟨π', hπ'.1⟩, hjH hπ'⟩ * ⟨⟨π, hπ.1⟩, hjH hπ⟩) fun j => by
        rw [map_mul, map_mul]
        have hz := C.rho_mem_rootCenter (π := ⟨⟨π, hπ.1⟩, hjH hπ⟩)
          (mem_longInvAt_subgroup_iff.mpr hπ.2) j
        have hz' := C.rho_mem_rootCenter (π := ⟨⟨π', hπ'.1⟩, hjH hπ'⟩)
          (mem_longInvAt_subgroup_iff.mpr hπ'.2) j
        exact ((CFSG.GH74.Uniqueness.Bender.mem_rootCenter_iff.mp hz).2 _
          (CFSG.GH74.Uniqueness.Bender.rootCenter_le _ hz')).symm
    exact congrArg (fun x : jHull (typeLSection G Ω v) Φ => ((x : typeLSection G Ω v) :
      Equiv.Perm Φ)) e
  have hsq : ∀ x ∈ Subgroup.closure S, x * x = 1 ∧ ∀ y ∈ S, x * y = y * x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact ⟨mul_self_eq_one_of_mem_longInv hx.2.1, fun y hy => hcomm x hx y hy⟩
    | one => exact ⟨mul_one 1, fun y _ => by rw [one_mul, mul_one]⟩
    | mul x y hx hy ihx ihy =>
      have hxy : x * y = y * x := by
        have hle : Subgroup.closure S ≤ Subgroup.centralizer {x} := by
          rw [Subgroup.closure_le]
          intro z hz
          exact Subgroup.mem_centralizer_iff.mpr fun w hw => by
            rw [Set.mem_singleton_iff.mp hw]
            exact ihx.2 z hz
        exact Subgroup.mem_centralizer_iff.mp (hle hy) x rfl
      refine ⟨?_, fun z hz => ?_⟩
      · calc x * y * (x * y) = x * x * (y * y) := by
              rw [mul_assoc, ← mul_assoc y, ← hxy]; group
          _ = 1 := by rw [ihx.1, ihy.1, one_mul]
      · rw [mul_assoc, ihy.2 z hz, ← mul_assoc, ihx.2 z hz, mul_assoc]
    | inv x hx ihx =>
      refine ⟨by rw [← mul_inv_rev, ihx.1, inv_one], fun z hz => ?_⟩
      calc x⁻¹ * z = x⁻¹ * (z * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * z) * x⁻¹ := by rw [ihx.2 z hz]
        _ = z * x⁻¹ := by group
  have hZp : IsPGroup 2 (Subgroup.closure S) := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, sq]; exact (hsq x x.2).1)⟩
  have hconjS : ∀ π' ∈ inducedPerm CK Φ hCKΦ, ∀ π ∈ S, π' * π * π'⁻¹ ∈ S := by
    intro π' hπ' π hπ
    obtain ⟨c, hc, hcπ⟩ := mem_inducedPerm.mp hπ'
    have hπ'K : π' ∈ typeLSection G Ω v := mem_centralizerImage.mpr ⟨c, hc.2, hcπ⟩
    have hπ'a : π' • C.a = C.a := Subtype.ext (by
      rw [Equiv.Perm.smul_def, hcπ, C.coe_a]
      exact K_le_stabilizer C hc.1)
    refine ⟨mul_mem (mul_mem hπ'K hπ.1) (inv_mem hπ'K), ?_⟩
    have := conj_mem_longInvAt hπ.2 π'
    rwa [hπ'a] at this
  have hnorm : inducedPerm CK Φ hCKΦ ≤ Subgroup.normalizer (Subgroup.closure S : Set _) := by
    intro π' hπ'
    have hcl : ∀ g ∈ inducedPerm CK Φ hCKΦ, ∀ z ∈ Subgroup.closure S,
        g * z * g⁻¹ ∈ Subgroup.closure S := by
      intro g hg z hz
      have hle : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj g).toMonoidHom := by
        rw [Subgroup.closure_le]
        intro y hy
        exact Subgroup.subset_closure (hconjS g hg y hy)
      simpa using hle hz
    exact mem_normalizer_of_conj (hcl π' hπ') (hcl π'⁻¹ (inv_mem hπ'))
  have hZC : Subgroup.closure S ≤ inducedPerm CK Φ hCKΦ := (Subgroup.closure_le _).mpr hSC
  have hsup := hZp.to_sup_of_normal_left' hÊ.2.1 (hÊ.1.trans hnorm)
  have heq := hÊ.2.2 _ (sup_le hZC hÊ.1) hsup le_sup_right
  exact heq ▸ le_sup_left

theorem exists_mem_E_coord (h : C.P95) (j : C.D.ι) {z : Equiv.Perm (C.D.Ψc j)}
    (hz : z ∈ CFSG.GH74.Uniqueness.Bender.rootCenter (seRadical (C.D.M j) (C.D.coord C.a j))) :
    ∃ e ∈ P.E, ∀ x x' : fixSet Ω (Subgroup.zpowers v),
      C.D.coord x' = Function.update (C.D.coord x) j (z (C.D.coord x j)) →
        e • (x : Ω) = x' := by
  set R := CFSG.GH74.Uniqueness.Bender.rootCenter (seRadical (C.D.M j) (C.D.coord C.a j))
  have hSE := C.isNaturalSE j
  rcases eq_or_ne z 1 with rfl | hz1
  · refine ⟨1, one_mem _, fun x x' hx => ?_⟩
    rw [one_smul]
    congr 1
    refine C.coord_injective ?_
    rw [hx, Equiv.Perm.one_apply, Function.update_eq_self]
  obtain ⟨n, k, e, hA⟩ := hSE.exists_isBenderAction
  have hcard := hA.card_rootCenter_seRadical (C.D.coord C.a j)
  obtain ⟨y, hy, hy1, hyz⟩ : ∃ y ∈ R, y ≠ 1 ∧ y ≠ z := by
    by_contra hne
    have hsub : (R : Set (Equiv.Perm (C.D.Ψc j))) ⊆ {1, z} := fun y hy => by
      by_cases h1 : y = 1
      · exact Or.inl h1
      · exact Or.inr (by_contra fun h2 => hne ⟨y, hy, h1, h2⟩)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_insert_le (1 : Equiv.Perm (C.D.Ψc j)) {z}
    rw [Set.ncard_singleton] at h2
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hcard] at h1
    have := hA.four_le_q
    omega
  have hinv : ∀ {w}, w ∈ R → w ≠ 1 → w ∈ C.D.M j ∧
      w ∈ longInvAt (Equiv.Perm (C.D.Ψc j)) (C.D.Ψc j) (C.D.coord C.a j) := fun {w} hw hw1 => by
    have hwR := CFSG.GH74.Uniqueness.Bender.rootCenter_le _ hw
    have hwM := seRadical_le hwR
    have hw2 := hSE.mul_self_eq_one_of_mem_rootCenter hw
    exact ⟨hwM, hSE.mem_longInv_perm hwM (orderOf_eq_prime (by rw [sq]; exact hw2) hw1),
      apply_eq_of_mem_seRadical hwR⟩
  have hyz1 : y * z ≠ 1 := fun h1 => hyz (by
    have := eq_inv_of_mul_eq_one_left h1
    rwa [inv_eq_of_mul_eq_one_right (hSE.mul_self_eq_one_of_mem_rootCenter hz)] at this)
  obtain ⟨hyM, hyJ⟩ := hinv hy hy1
  obtain ⟨hwM, hwJ⟩ := hinv (mul_mem hy hz) hyz1
  obtain ⟨t₀, ht₀⟩ := C.D.longInvAt_nonempty C.a
  set t₀H : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
    ⟨t₀, mem_jHull_of_mem_longInv ht₀.1⟩
  have hreal : ∀ w, w ∈ C.D.M j →
      w ∈ longInvAt (Equiv.Perm (C.D.Ψc j)) (C.D.Ψc j) (C.D.coord C.a j) →
      ∃ π : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)),
        (π : typeLSection G Ω v) ∈ longInvAt (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))
          C.a ∧ ∀ k, C.D.ρ k π = Function.update (fun k => C.D.ρ k t₀H) j w k := by
    intro w hwM hwJ
    refine C.D.exists_mem_longInvAt_rho_eq C.a _ (fun k => ?_) (fun k => ?_)
    · rcases eq_or_ne k j with rfl | hk
      · rw [Function.update_self, C.D.range_rho_of_not_isOuterFactor hSE.not_isOuterFactor]
        exact hwM
      · rw [Function.update_of_ne hk]
        exact ⟨t₀H, rfl⟩
    · rcases eq_or_ne k j with rfl | hk
      · rw [Function.update_self]
        exact hwJ
      · rw [Function.update_of_ne hk]
        exact C.D.rho_mem_longInvAt ht₀ k
  obtain ⟨π₁, hπ₁, hρ₁⟩ := hreal y hyM hyJ
  obtain ⟨π₂, hπ₂, hρ₂⟩ := hreal (y * z) hwM hwJ
  have hmem : ((π₁ : typeLSection G Ω v) : Equiv.Perm (fixSet Ω (Subgroup.zpowers v))) *
      ((π₂ : typeLSection G Ω v) : Equiv.Perm _) ∈ inducedPerm P.E (fixSet Ω (Subgroup.zpowers v))
        ((P.E_le_centralizer h).trans (centralizer_le_stabilizer_fixSet _)) :=
    P.closure_longInvAt_le h (mul_mem
      (Subgroup.subset_closure ⟨(π₁ : typeLSection G Ω v).2, mem_longInvAt_subgroup_iff.mp hπ₁⟩)
      (Subgroup.subset_closure ⟨(π₂ : typeLSection G Ω v).2, mem_longInvAt_subgroup_iff.mp hπ₂⟩))
  obtain ⟨e, he, heπ⟩ := mem_inducedPerm.mp hmem
  refine ⟨e, he, fun x x' hx => ?_⟩
  rw [← heπ x]
  congr 1
  refine C.coord_injective (funext fun k => ?_)
  show C.D.coord ((π₁ : typeLSection G Ω v) • (π₂ : typeLSection G Ω v) • x) k = _
  rw [C.D.coord_smul, C.D.coord_smul, hρ₁, hρ₂, hx]
  rcases eq_or_ne k j with rfl | hk
  · rw [Function.update_self, Function.update_self, Function.update_self, ← Equiv.Perm.mul_apply,
      ← mul_assoc, hSE.mul_self_eq_one_of_mem_rootCenter hy, one_mul]
  · rw [Function.update_of_ne hk, Function.update_of_ne hk, Function.update_of_ne hk,
      ← Equiv.Perm.mul_apply, mul_self_eq_one_of_mem_longInv (C.D.rho_mem_longInvAt ht₀ k).1,
      Equiv.Perm.one_apply]

end P95Data

end Sylow

section Lines

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {C : P49Config G Ω α v}

namespace P95Data

variable (P : C.P95Data)

theorem mem_line_of_forall (h : C.P95) {ω : Ω}
    (hω : ∀ e ∈ P.E, (∀ y ∈ C.line, e • y = y) → e • ω = ω) : ω ∈ C.line := by
  have hvω : v • ω = ω := hω v P.v_mem_E fun y hy =>
    mem_fixSet_zpowers_iff.mp (C.line_subset_fixSet hy)
  set x : fixSet Ω (Subgroup.zpowers v) := ⟨ω, mem_fixSet_zpowers_iff.mpr hvω⟩
  by_contra hωL
  have hk : ∃ k, k ≠ C.i ∧ C.D.coord x k ≠ C.D.coord C.a k := by
    by_contra hne
    refine hωL ⟨C.D.coord x C.i, ?_⟩
    simp only
    rw [C.lpt_eq_of_coord fun k hk => by_contra fun h1 => hne ⟨k, hk, h1⟩]
  obtain ⟨k, hki, hxk⟩ := hk
  obtain ⟨n, k', e', hA⟩ := (C.isNaturalSE k).exists_isBenderAction
  have hR := hA.card_rootCenter_seRadical (C.D.coord C.a k)
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    ((Subgroup.one_lt_card_iff_ne_bot _).mp (by rw [hR]; have := hA.four_le_q; omega))
  obtain ⟨e, he, hez⟩ := P.exists_mem_E_coord h k z.2
  obtain ⟨x', hx'⟩ := C.D.coord_surjective
    (Function.update (C.D.coord x) k ((z : Equiv.Perm (C.D.Ψc k)) (C.D.coord x k)))
  have hza : (z : Equiv.Perm (C.D.Ψc k)) (C.D.coord C.a k) = C.D.coord C.a k :=
    apply_eq_of_mem_seRadical (CFSG.GH74.Uniqueness.Bender.rootCenter_le _ z.2)
  have hfixL : ∀ y ∈ C.line, e • y = y := by
    rintro _ ⟨ψ, rfl⟩
    refine hez _ _ (Function.update_eq_self_iff.mpr ?_).symm
    rw [C.coord_lpt_of_ne ψ hki]
    exact hza
  have h1 : e • ω = x' := hez x x' hx'
  rw [hω e he hfixL] at h1
  have h2 : C.D.coord x k = (z : Equiv.Perm (C.D.Ψc k)) (C.D.coord x k) := by
    have := congrFun hx' k
    rwa [Function.update_self, ← show x = x' from Subtype.ext h1] at this
  refine hz1 (Subtype.ext ?_)
  exact (C.isNaturalSE k).eq_one_of_mem_seRadical (CFSG.GH74.Uniqueness.Bender.rootCenter_le _ z.2)
    hxk h2.symm

theorem exists_mem_normalizer_smul_line (h : C.P95) {ℓ : Set Ω}
    (hℓ : ℓ ∈ linesThrough G C.line α) :
    ∃ n ∈ stabilizer G α, n ∈ Subgroup.normalizer (P.E : Set G) ∧ n • C.line = ℓ := by
  obtain ⟨⟨g, rfl⟩, hαℓ⟩ := hℓ
  obtain ⟨ω, ⟨ψ, rfl⟩, hω⟩ := hαℓ
  obtain ⟨m, hm, hma⟩ := C.exists_mem_M_apply_eq' (C.D.coord C.a C.i) ψ
  obtain ⟨c, -, hcm⟩ := C.exists_lineActs_of_mem hm
  have hgc : g * c ∈ stabilizer G α := by
    rw [mem_stabilizer_iff, mul_smul, hcm.smul_α, hma]
    exact hω
  obtain ⟨n, hnα, hnN, hnΓ, -⟩ := P.exists_mem_normalizer_eqOn h hgc
  refine ⟨n, hnα, hnN, ?_⟩
  have hpt : ∀ y ∈ C.line, n • y = (g * c) • y := fun y hy => by
    rcases eq_or_ne y α with rfl | hyα
    · rw [mem_stabilizer_iff.mp hnα, mem_stabilizer_iff.mp hgc]
    · exact hnΓ y (mem_Γ_of_mem_line C hy hyα)
  have e1 : n • C.line = (g * c) • C.line := by
    ext y
    simp only [Set.mem_smul_set]
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact ⟨y', hy', (hpt y' hy').symm⟩
    · rintro ⟨y', hy', rfl⟩
      exact ⟨y', hy', hpt y' hy'⟩
  rw [e1, mul_smul, hcm.smul_line]

theorem mem_of_forall_of_mem_linesThrough (h : C.P95) {ℓ : Set Ω}
    (hℓ : ℓ ∈ linesThrough G C.line α) {ω : Ω}
    (hω : ∀ e ∈ P.E, (∀ y ∈ ℓ, e • y = y) → e • ω = ω) : ω ∈ ℓ := by
  obtain ⟨n, -, hnN, rfl⟩ := P.exists_mem_normalizer_smul_line h hℓ
  refine Set.mem_smul_set_iff_inv_smul_mem.mpr (P.mem_line_of_forall h fun w hw hwL => ?_)
  have h1 : n * w * n⁻¹ ∈ P.E := (Subgroup.mem_normalizer_iff.mp hnN w).mp hw
  have h2 := hω _ h1 fun y hy => by
    obtain ⟨y', hy', rfl⟩ := hy
    rw [mul_smul, mul_smul, inv_smul_smul, hwL y' hy']
  rw [mul_smul, mul_smul, smul_eq_iff_eq_inv_smul] at h2
  exact h2

end P95Data

theorem P95.smul_eq_of_mem_K (h : C.P95) {k : G} (hk : k ∈ C.K) {ℓ : Set Ω}
    (hℓ : ℓ ∈ linesThrough G C.line α) : k • ℓ = ℓ := by
  obtain ⟨⟨g, rfl⟩, hαℓ⟩ := hℓ
  obtain ⟨P⟩ := nonempty_p95Data C
  obtain ⟨n, hnα, -, hn⟩ := P.exists_mem_normalizer_smul_line h ⟨⟨g, rfl⟩, hαℓ⟩
  rw [← hn]
  have hk' := h.smul_line_of_mem_K (conj_mem_K (inv_mem hnα) hk)
  rw [inv_inv] at hk'
  calc k • n • C.line = n • (n⁻¹ * k * n) • C.line := by
        rw [smul_smul, smul_smul]
        congr 1
        group
    _ = n • C.line := by rw [hk']

theorem P95.smul_eq_of_smul_eq (h : C.P95) {k : G} (hk : k ∈ C.K) {ℓ : Set Ω}
    (hℓ : ℓ ∈ linesThrough G C.line α) {x : Ω} (hx : x ∈ ℓ) (hxα : x ≠ α) (hkx : k • x = x)
    {y : Ω} (hy : y ∈ ℓ) : k • y = y := by
  obtain ⟨P⟩ := nonempty_p95Data C
  obtain ⟨n, hnα, -, rfl⟩ := P.exists_mem_normalizer_smul_line h hℓ
  obtain ⟨z, hz, hkz⟩ := h.exists_lineActs_rootZ (conj_mem_K (inv_mem hnα) hk)
  rw [inv_inv] at hkz
  obtain ⟨x', ⟨ψx, rfl⟩, rfl⟩ := hx
  obtain ⟨y', ⟨ψy, rfl⟩, rfl⟩ := hy
  have hψx : ψx ≠ C.D.coord C.a C.i := by
    rintro rfl
    refine hxα ?_
    simp only [C.lpt_coord_a, C.coe_a]
    exact mem_stabilizer_iff.mp hnα
  have h1 : z ψx = ψx := by
    have e := hkz ψx
    have e2 : (n⁻¹ * k * n) • (C.lpt ψx : Ω) = C.lpt ψx := by
      rw [mul_smul, mul_smul, hkx, inv_smul_smul]
    rw [e2] at e
    exact (C.lpt_injective (Subtype.ext e)).symm
  have hz1 : z = 1 := (C.isNaturalSE C.i).eq_one_of_mem_seRadical
    (CFSG.GH74.Uniqueness.Bender.rootCenter_le _ hz) hψx h1
  have e3 := hkz ψy
  rw [hz1, Equiv.Perm.one_apply, mul_smul, mul_smul, inv_smul_eq_iff] at e3
  exact e3

theorem P95.eq_of_mem_of_mem (h : C.P95) {ℓ ℓ' : Set Ω} (hℓ : ℓ ∈ linesThrough G C.line α)
    (hℓ' : ℓ' ∈ linesThrough G C.line α) {x : Ω} (hx : x ∈ ℓ) (hx' : x ∈ ℓ') (hxα : x ≠ α) :
    ℓ = ℓ' := by
  obtain ⟨P⟩ := nonempty_p95Data C
  have key : ∀ {ℓ ℓ' : Set Ω}, ℓ ∈ linesThrough G C.line α → ℓ' ∈ linesThrough G C.line α →
      x ∈ ℓ → x ∈ ℓ' → ℓ ⊆ ℓ' := by
    intro ℓ ℓ' hℓ hℓ' hx hx' ω hω
    refine P.mem_of_forall_of_mem_linesThrough h hℓ' fun e he heℓ' => ?_
    exact h.smul_eq_of_smul_eq (P.E_le_K he) hℓ hx hxα (heℓ' x hx') hω
  exact Set.Subset.antisymm (key hℓ hℓ' hx hx') (key hℓ' hℓ hx' hx)

end Lines

end P49Config

end CFSG.Holt.H78
