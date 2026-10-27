module

public import CFSG.Holt.Fixed
public import CFSG.Open.FusionDefs
public import CFSG.RankThree.PartTwo.Sec21.UniqueFixedPoint

public section

namespace CFSG.Holt

open MulAction CFSG.Open

variable {X : Type*} [Group X] {Ω : Type*} [MulAction X Ω]

theorem exists_fixes_exactly {x : X} (h : ∃! ω : Ω, x • ω = ω) :
    ∃ α : Ω, ∀ ω, x • ω = ω ↔ ω = α := by
  obtain ⟨α, hα, huniq⟩ := h
  exact ⟨α, fun ω => ⟨huniq ω, fun h => h ▸ hα⟩⟩

theorem conj_smul_eq_self_iff {x : X} {α : Ω} (hx : ∀ ω, x • ω = ω ↔ ω = α) (g : X) (ω : Ω) :
    (g * x * g⁻¹) • ω = ω ↔ ω = g • α := by
  rw [mul_smul, mul_smul, smul_eq_iff_eq_inv_smul, hx, inv_smul_eq_iff]

theorem orderOf_eq_of_isConj {x d : X} (h : IsConj x d) : orderOf x = orderOf d := by
  obtain ⟨c, hc⟩ := h
  exact SemiconjBy.orderOf_eq _ hc

theorem existsUnique_fixed_of_isConj {x d : X} (hx : ∃! ω : Ω, x • ω = ω) (hd : IsConj x d) :
    ∃! ω : Ω, d • ω = ω := by
  obtain ⟨α, hα⟩ := exists_fixes_exactly hx
  obtain ⟨g, rfl⟩ := isConj_iff.mp hd
  exact ⟨g • α, (conj_smul_eq_self_iff hα g _).mpr rfl,
    fun ω h => (conj_smul_eq_self_iff hα g ω).mp h⟩

theorem smul_eq_of_commute {d t : X} {α : Ω} (hd : ∀ ω, d • ω = ω ↔ ω = α) (h : Commute t d) :
    t • α = α :=
  (hd (t • α)).mp (by rw [← mul_smul, ← h.eq, mul_smul, (hd α).mpr rfl])

theorem eq_of_commute {d₁ d₂ : X} {α₁ α₂ : Ω} (h₁ : ∀ ω, d₁ • ω = ω ↔ ω = α₁)
    (h₂ : ∀ ω, d₂ • ω = ω ↔ ω = α₂) (h : Commute d₁ d₂) : α₁ = α₂ :=
  (h₂ α₁).mp (smul_eq_of_commute h₁ h.symm)

theorem normalizer_le_stabilizer_of_mem {Y : Subgroup X} {d : X} (hdY : d ∈ Y) {α : Ω}
    (hd : ∀ ω, d • ω = ω ↔ ω = α) (hY : Y ≤ stabilizer X α) :
    Subgroup.normalizer (Y : Set X) ≤ stabilizer X α := fun _ hn =>
  fixSet_subset_singleton_of_mem hdY hd
    (smul_mem_fixSet_of_mem_normalizer hn (mem_fixSet_iff_le_stabilizer.mpr hY))

section Counting

variable [Finite Ω] {z : X}

theorem isPGroup_zpowers_of_orderOf_eq_two {x : X} (hx : orderOf x = 2) :
    IsPGroup 2 (Subgroup.zpowers x) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])

theorem odd_card (hz : orderOf z = 2) (hlong : ∃! ω : Ω, z • ω = ω) : Odd (Nat.card Ω) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, hα⟩ := exists_fixes_exactly hlong
  have hF : fixSet Ω (Subgroup.zpowers z) = {α} := by
    ext ω
    rw [fixSet_zpowers, mem_fixedBy, Set.mem_singleton_iff, hα]
  have hmod := card_modEq_card_fixSet (Ω := Ω) (isPGroup_zpowers_of_orderOf_eq_two hz)
  have h1 : Nat.card ({α} : Set Ω) = 1 := Nat.card_unique
  rw [hF, h1] at hmod
  exact Nat.odd_iff.mpr hmod

end Counting

section Sylow

theorem exists_fusionIsSylowIn_ge [Finite X] {p : ℕ} [Fact p.Prime] {Q K : Subgroup X}
    (hQ : IsPGroup p Q) (hQK : Q ≤ K) : ∃ R : Subgroup X, Q ≤ R ∧ fusionIsSylowIn p R K := by
  obtain ⟨T, hT⟩ := (hQ.comap_of_injective K.subtype K.subtype_injective).exists_le_sylow
  refine ⟨(T : Subgroup K).map K.subtype, fun x hx => ⟨⟨x, hQK hx⟩, hT hx, rfl⟩,
    Subgroup.map_subtype_le _, T.isPGroup'.map K.subtype, fun P hPK hP hle => ?_⟩
  have hTP : (T : Subgroup K) ≤ P.subgroupOf K := fun t ht => hle ⟨t, ht, rfl⟩
  have hPT := T.is_maximal' (hP.comap_of_injective K.subtype K.subtype_injective) hTP
  rw [← hPT]
  exact ((Subgroup.subgroupOf_map_subtype P K).trans (inf_eq_left.mpr hPK)).symm

theorem exists_sylow_map_eq_of_fusionIsSylowIn [Finite X] {p : ℕ} [Fact p.Prime]
    {P K : Subgroup X} (hP : fusionIsSylowIn p P K) :
    ∃ T : Sylow p K, (T : Subgroup K).map K.subtype = P := by
  obtain ⟨hPK, hPp, hmax⟩ := hP
  obtain ⟨T, hT⟩ := (hPp.comap_of_injective K.subtype K.subtype_injective).exists_le_sylow
  exact ⟨T, hmax _ (Subgroup.map_subtype_le _) (T.isPGroup'.map K.subtype)
    fun x hx => ⟨⟨x, hPK hx⟩, hT hx, rfl⟩⟩

theorem exists_sylow_eq_iff_fusionIsSylowIn_top {p : ℕ} {P : Subgroup X} :
    (∃ S : Sylow p X, (S : Subgroup X) = P) ↔ fusionIsSylowIn p P ⊤ := by
  constructor
  · rintro ⟨S, rfl⟩
    exact ⟨le_top, S.isPGroup', fun Q _ hQ hle => S.is_maximal' hQ hle⟩
  · rintro ⟨-, hP, hmax⟩
    exact ⟨⟨P, hP, fun hQ hle => hmax _ le_top hQ hle⟩, rfl⟩

theorem mem_smul_sylow_iff {p : ℕ} {S : Sylow p X} {g x : X} :
    x ∈ ((g • S : Sylow p X) : Subgroup X) ↔ g⁻¹ * x * g ∈ (S : Subgroup X) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    ← map_inv, MulAut.conj_apply, inv_inv]

variable {z : X}

theorem exists_isConj_mem_center_sylow [Finite X] (hlong : ∃! ω : Ω, z • ω = ω)
    (hcent : ∃ S : Sylow 2 X, z ∈ (S : Subgroup X) ∧
      (S : Subgroup X) ≤ Subgroup.centralizer {z}) (S : Sylow 2 X) :
    ∃ d : X, IsConj z d ∧ d ∈ (S : Subgroup X) ∧ (S : Subgroup X) ≤ Subgroup.centralizer {d} ∧
      ∃ α : Ω, (∀ ω, d • ω = ω ↔ ω = α) ∧ fixSet Ω (S : Subgroup X) = {α} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hzS₀, hS₀⟩ := hcent
  obtain ⟨g, rfl⟩ := exists_smul_eq X S₀ S
  obtain ⟨α, hα⟩ := exists_fixes_exactly hlong
  have hdS : g * z * g⁻¹ ∈ ((g • S₀ : Sylow 2 X) : Subgroup X) := by
    rw [mem_smul_sylow_iff, show g⁻¹ * (g * z * g⁻¹) * g = z by group]
    exact hzS₀
  have hSc : ((g • S₀ : Sylow 2 X) : Subgroup X) ≤ Subgroup.centralizer {g * z * g⁻¹} := by
    intro x hx
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (hS₀ (mem_smul_sylow_iff.mp hx))
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc]
      _ = g * z * g⁻¹ * x := by group
  have hd := conj_smul_eq_self_iff hα g
  refine ⟨g * z * g⁻¹, isConj_iff.mpr ⟨g, rfl⟩, hdS, hSc, g • α, hd,
    Set.Subset.antisymm (fixSet_subset_singleton_of_mem hdS hd) ?_⟩
  rintro ω rfl y hy
  exact smul_eq_of_commute hd (Subgroup.mem_centralizer_singleton_iff.mp (hSc hy))

variable [Finite X] [Finite Ω] [IsPretransitive X Ω]

theorem exists_sylow_eq_of_fusionIsSylowIn_stabilizer (hz : orderOf z = 2)
    (hlong : ∃! ω : Ω, z • ω = ω) {ω : Ω} {P : Subgroup X}
    (hP : fusionIsSylowIn 2 P (stabilizer X ω)) : ∃ S : Sylow 2 X, (S : Subgroup X) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, rfl⟩ := exists_sylow_map_eq_of_fusionIsSylowIn hP
  have hidx : Odd (stabilizer X ω).index := by
    rw [index_stabilizer_of_transitive X ω]
    exact odd_card hz hlong
  exact CFSG.RankThree.PartTwo.Sec21.exists_sylow_two_eq_map_of_odd_index hidx T

theorem exists_isConj_mem_center_of_fusionIsSylowIn (hz : orderOf z = 2)
    (hlong : ∃! ω : Ω, z • ω = ω)
    (hcent : ∃ S : Sylow 2 X, z ∈ (S : Subgroup X) ∧
      (S : Subgroup X) ≤ Subgroup.centralizer {z}) {ω : Ω} {P : Subgroup X}
    (hP : fusionIsSylowIn 2 P (stabilizer X ω)) :
    ∃ d : X, IsConj z d ∧ d ∈ P ∧ P ≤ Subgroup.centralizer {d} ∧
      ∀ ω', d • ω' = ω' ↔ ω' = ω := by
  obtain ⟨S, rfl⟩ := exists_sylow_eq_of_fusionIsSylowIn_stabilizer hz hlong hP
  obtain ⟨d, hd, hdS, hSc, α, hα, hF⟩ := exists_isConj_mem_center_sylow hlong hcent S
  have hω : ω ∈ fixSet Ω (S : Subgroup X) := mem_fixSet_iff_le_stabilizer.mpr hP.1
  rw [hF, Set.mem_singleton_iff] at hω
  subst hω
  exact ⟨d, hd, hdS, hSc, hα⟩

theorem exists_isConj_le_centralizer_of_le_stabilizer (hz : orderOf z = 2)
    (hlong : ∃! ω : Ω, z • ω = ω)
    (hcent : ∃ S : Sylow 2 X, z ∈ (S : Subgroup X) ∧
      (S : Subgroup X) ≤ Subgroup.centralizer {z}) {ω : Ω} {Q : Subgroup X}
    (hQ : IsPGroup 2 Q) (hQω : Q ≤ stabilizer X ω) :
    ∃ d : X, IsConj z d ∧ Q ≤ Subgroup.centralizer {d} ∧ ∀ ω', d • ω' = ω' ↔ ω' = ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hQP, hP⟩ := exists_fusionIsSylowIn_ge hQ hQω
  obtain ⟨d, hd, -, hPc, hdω⟩ := exists_isConj_mem_center_of_fusionIsSylowIn hz hlong hcent hP
  exact ⟨d, hd, hQP.trans hPc, hdω⟩

end Sylow

end CFSG.Holt
