module

public import CFSG.Holt.H78.Data
public import CFSG.Holt.H78.SectionsStar
import CFSG.Holt.H78.OddCore
import CFSG.Holt.H78.SEModelFive

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General
open scoped Pointwise

section Below

theorem HoltTheorem1Below.mono {n d n' d' : ℕ} (h : HoltTheorem1Below n d)
    (hle : n' < n ∨ n' = n ∧ d' ≤ d) : HoltTheorem1Below n' d' := by
  intro G _ _ Ω _ _ _ hlt hG
  exact h G Ω (by omega) hG

theorem HoltTheorem1Below.of_le {n d n' d' : ℕ} (h : HoltTheorem1Below n d) (hn : n' ≤ n)
    (hd : d' ≤ d) : HoltTheorem1Below n' d' :=
  h.mono (by omega)

theorem HoltTheorem1Below.holtStructure {G : Type} [Group G] [Finite G] {Ω : Type}
    [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω]
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1)) (hG : IsStarGroup G Ω) :
    HoltStructure G Ω :=
  hB G Ω (Or.inr ⟨rfl, Nat.lt_succ_self _⟩) hG

end Below

section Dihedral

variable {G : Type*} [Group G]

theorem exists_mem_zpowers_conj_eq_of_odd {t u : G} (ht : t * t = 1) (hu : u * u = 1)
    (hodd : Odd (orderOf (t * u))) : ∃ x ∈ Subgroup.zpowers (t * u), x * t * x⁻¹ = u := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨(t * u) ^ k, Subgroup.npow_mem_zpowers _ _, ?_⟩
  have hinv := conj_pow_mul_eq_inv ht hu k
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have h2k : (t * u) ^ (k + k) = u * t := by
    have hpow : (t * u) ^ (k + k) * (t * u) = 1 := by
      rw [← pow_succ, ← two_mul, ← hk, pow_orderOf_eq_one]
    rw [eq_inv_of_mul_eq_one_left hpow, mul_inv_rev, hu', ht']
  calc (t * u) ^ k * t * ((t * u) ^ k)⁻¹
      = (t * u) ^ k * (t * t) * (t * u) ^ k * t⁻¹ := by
        rw [← hinv]; simp only [mul_assoc]
    _ = u := by rw [ht, mul_one, ← pow_add, h2k, mul_inv_cancel_right]

theorem odd_orderOf_of_pow_mem {w : G} {m : ℕ} (hm : Odd m) {M : Subgroup G}
    (hM : Odd (Nat.card M)) (hw : w ^ m ∈ M) : Odd (orderOf w) := by
  have h1 : Odd (orderOf (w ^ m)) := hM.of_dvd_nat (M.orderOf_dvd_natCard hw)
  refine (hm.mul h1).of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)
  rw [pow_mul, pow_orderOf_eq_one]

end Dihedral

section Model

namespace HoltData

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] (D : HoltData G Ω)

theorem exists_mem_iSup_rho_eq (l : D.ι → jHull G Ω) (hl : ∀ i, (l i : G) ∈ D.L i) :
    ∃ h : jHull G Ω, (h : G) ∈ ⨆ i, D.L i ∧ ∀ i, D.ρ i h = D.ρ i (l i) := by
  classical
  suffices H : ∀ s : Finset D.ι, ∃ h : jHull G Ω, (h : G) ∈ ⨆ i, D.L i ∧
      (∀ i ∈ s, D.ρ i h = D.ρ i (l i)) ∧ ∀ i ∉ s, D.ρ i h = 1 by
    obtain ⟨h, hh, hs, -⟩ := H Finset.univ
    exact ⟨h, hh, fun i => hs i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, fun i hi => absurd hi (Finset.notMem_empty i),
      fun i _ => map_one _⟩
  | insert a s has ih =>
    obtain ⟨h, hh, hs, hns⟩ := ih
    refine ⟨h * l a, mul_mem hh (Subgroup.mem_iSup_of_mem a (hl a)), fun i hi => ?_,
      fun i hi => ?_⟩
    · rw [map_mul]
      rcases Finset.mem_insert.mp hi with rfl | hi
      · rw [hns i has, one_mul]
      · rw [hs i hi, rho_eq_one_of_mem_L (i := a) (j := i) (fun hai => has (hai ▸ hi)) (hl a),
          mul_one]
    · rw [map_mul, hns i (fun h' => hi (Finset.mem_insert_of_mem h')),
        rho_eq_one_of_mem_L (i := a) (j := i) (fun hai => hi (hai ▸ Finset.mem_insert_self a s))
          (hl a), one_mul]

variable [Finite G]

theorem exists_mem_M_conj_eq {t u : G} (ht : t ∈ longInv G Ω) (hu : u ∈ longInv G Ω)
    (i : D.ι) : ∃ g ∈ D.M i, g * D.ρ i ⟨t, mem_jHull_of_mem_longInv ht⟩ * g⁻¹ =
      D.ρ i ⟨u, mem_jHull_of_mem_longInv hu⟩ := by
  have ha := D.rho_mem_longInv ht i
  have hb := D.rho_mem_longInv hu i
  by_cases hAlt : D.M i = alternatingGroup (D.Ψc i)
  · obtain ⟨g, hg, hgab⟩ := exists_mem_alternatingGroup_conj_eq ha hb
    exact ⟨g, hAlt ▸ hg, hgab⟩
  have hnout : ¬ IsOuterFactor (D.M i) := fun h => hAlt h.1
  have haM := (D.rho_mem_M_iff ht i).mpr hnout
  have hbM := (D.rho_mem_M_iff hu i).mpr hnout
  have hSE : IsNaturalSE (D.M i) := (D.factor i).resolve_left fun h => hAlt h.1
  obtain ⟨c, hc⟩ := isConj_iff.mp (hSE.isConj (x := ⟨_, haM⟩) (y := ⟨_, hbM⟩)
    (by rw [Subgroup.orderOf_mk]; exact ha.1) (by rw [Subgroup.orderOf_mk]; exact hb.1))
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

theorem exists_mem_iSup_rho_conj_eq {t u : G} (ht : t ∈ longInv G Ω) (hu : u ∈ longInv G Ω) :
    ∃ h : jHull G Ω, (h : G) ∈ ⨆ i, D.L i ∧ ∀ i,
      D.ρ i (h * ⟨t, mem_jHull_of_mem_longInv ht⟩ * h⁻¹) =
        D.ρ i ⟨u, mem_jHull_of_mem_longInv hu⟩ := by
  choose g hgM hg using fun i => D.exists_mem_M_conj_eq ht hu i
  choose l hlL hl using fun i => D.mem_M.mp (hgM i)
  obtain ⟨h, hh, hρ⟩ := D.exists_mem_iSup_rho_eq l hlL
  refine ⟨h, hh, fun i => ?_⟩
  rw [map_mul, map_mul, map_inv, hρ i, hl i, hg i]

theorem exists_mem_iSup_conj_eq [FaithfulSMul G Ω] (hO : jOddCore G Ω = ⊥) {t u : G}
    (ht : t ∈ longInv G Ω) (hu : u ∈ longInv G Ω) : ∃ h ∈ ⨆ i, D.L i, h * t * h⁻¹ = u := by
  obtain ⟨h, hh, hρ⟩ := D.exists_mem_iSup_rho_conj_eq ht hu
  refine ⟨h, hh, ?_⟩
  set x : jHull G Ω := h * ⟨t, mem_jHull_of_mem_longInv ht⟩ * h⁻¹
  have hx : (x : G) = (h : G) * t * (h : G)⁻¹ := rfl
  rw [← hx]
  refine eq_of_smul_eq_smul (α := Ω) fun ω => ?_
  have hc : D.coord ((x : G) • ω) = D.coord (u • ω) := funext fun i => by
    rw [D.coord_smul x, D.coord_smul ⟨u, mem_jHull_of_mem_longInv hu⟩, hρ i]
  have h1 := (D.coord_eq_iff _ _).mp hc
  rw [orbit_jOddCore_eq_singleton hO, Set.mem_singleton_iff] at h1
  exact h1.symm

end HoltData

end Model

section Blocks

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem eq_bot_of_normal_le_stabilizer [FaithfulSMul G Ω] [IsPretransitive G Ω]
    {N : Subgroup G} [hN : N.Normal] {α : Ω} (hNα : N ≤ stabilizer G α) : N = ⊥ := by
  refine eq_bot_iff.mpr fun n hn => Subgroup.mem_bot.mpr (eq_of_smul_eq_smul (α := Ω) ?_)
  intro ω
  obtain ⟨g, rfl⟩ := exists_smul_eq G α ω
  have h : g⁻¹ * n * g ∈ N := by simpa using hN.conj_mem n hn g⁻¹
  have h' : (g⁻¹ * n * g) • α = α := hNα h
  rw [mul_smul, mul_smul, inv_smul_eq_iff] at h'
  rw [h', one_smul]

theorem isPretransitive_of_stabilizer_sup_eq_top [IsPretransitive G Ω] {N : Subgroup G}
    [N.Normal] {α : Ω} (h : stabilizer G α ⊔ N = ⊤) : IsPretransitive N Ω := by
  have hα : ∀ β : Ω, ∃ n : N, (n : G) • α = β := fun β => by
    obtain ⟨g, rfl⟩ := exists_smul_eq G α β
    have hg : g ∈ ((N ⊔ stabilizer G α : Subgroup G) : Set G) := by
      rw [sup_comm, h]; exact Set.mem_univ g
    rw [Subgroup.normal_mul] at hg
    obtain ⟨n, hn, s, hs, rfl⟩ := hg
    exact ⟨⟨n, hn⟩, by rw [mul_smul, mem_stabilizer_iff.mp hs]⟩
  refine ⟨fun β γ => ?_⟩
  obtain ⟨n₁, rfl⟩ := hα β
  obtain ⟨n₂, rfl⟩ := hα γ
  exact ⟨n₂ * n₁⁻¹, by rw [Subgroup.smul_def, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul,
    inv_smul_smul]⟩

theorem isPretransitive_subgroupOf_quotient_sup (A N : Subgroup G) [N.Normal] :
    IsPretransitive (N.subgroupOf (A ⊔ N)) (↥(A ⊔ N) ⧸ A.subgroupOf (A ⊔ N)) := by
  have hc : ∀ c : ↥(A ⊔ N) ⧸ A.subgroupOf (A ⊔ N),
      ∃ n : N.subgroupOf (A ⊔ N), n • ((1 : ↥(A ⊔ N)) : ↥(A ⊔ N) ⧸ A.subgroupOf (A ⊔ N)) = c := by
    intro c
    induction c using QuotientGroup.induction_on with
    | H k =>
      have hk : (k : G) ∈ ((N ⊔ A : Subgroup G) : Set G) := by rw [sup_comm]; exact k.2
      rw [Subgroup.normal_mul] at hk
      obtain ⟨n, hn, a, ha, hna⟩ := hk
      have hnK : n ∈ A ⊔ N := by
        have : n = (k : G) * a⁻¹ := by rw [← hna, mul_inv_cancel_right]
        rw [this]
        exact mul_mem k.2 (inv_mem (Subgroup.mem_sup_left ha))
      refine ⟨⟨⟨n, hnK⟩, Subgroup.mem_subgroupOf.mpr hn⟩, ?_⟩
      rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      simpa [← hna] using ha
  refine ⟨fun x y => ?_⟩
  obtain ⟨n₁, rfl⟩ := hc x
  obtain ⟨n₂, rfl⟩ := hc y
  exact ⟨n₂ * n₁⁻¹, by rw [mul_smul, inv_smul_smul]⟩

theorem isPretransitive_pPrimeCore_range {X : Type*} [Group X] {Δ : Type*} [MulAction X Δ]
    {N : Subgroup X} [hN : N.Normal] (hN2 : Nat.Coprime 2 (Nat.card N))
    (hNΔ : IsPretransitive N Δ) :
    IsPretransitive (CFSG.pPrimeCore 2 (toPermHom X Δ).range) Δ := by
  set f := (toPermHom X Δ).rangeRestrict
  have hle : N.map f ≤ CFSG.pPrimeCore 2 (toPermHom X Δ).range :=
    le_sSup ⟨hN.map f (MonoidHom.rangeRestrict_surjective _),
      Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd N f) hN2⟩
  refine ⟨fun δ ε => ?_⟩
  obtain ⟨n, hn⟩ := hNΔ.exists_smul_eq δ ε
  exact ⟨⟨f n, hle ⟨n, n.2, rfl⟩⟩, hn⟩

variable [Finite G] [Finite Ω] [FaithfulSMul G Ω]

theorem odd_orderOf_mul_of_toPermHom_eq (hG : IsStarGroup G Ω) {α : Ω} {u v : G}
    (hlt : stabilizer G α < stabilizer G α ⊔ CFSG.pPrimeCore 2 G) (hu : u ∈ longInvAt G Ω α)
    (hv : v ∈ longInv G Ω)
    (hvu : toPermHom G (G ⧸ (stabilizer G α ⊔ CFSG.pPrimeCore 2 G)) v =
      toPermHom G (G ⧸ (stabilizer G α ⊔ CFSG.pPrimeCore 2 G)) u) :
    Odd (orderOf (v * u)) := by
  have := hG.isPretransitive
  set N := CFSG.pPrimeCore 2 G
  set K := stabilizer G α ⊔ N
  have hK : stabilizer G α ≤ K := le_sup_left
  have huK : u ∈ K := hK hu.2
  have hvK : v ∈ K := by
    have h1 : v • ((1 : G) : G ⧸ K) = u • ((1 : G) : G ⧸ K) :=
      congrArg (fun π : Equiv.Perm (G ⧸ K) => π ((1 : G) : G ⧸ K)) hvu
    rw [MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, smul_eq_mul, smul_eq_mul, mul_one,
      mul_one, QuotientGroup.eq] at h1
    simpa using K.mul_mem huK (K.inv_mem h1)
  have h1B : 1 < (stabilizer G α).relIndex K := by
    have hne : (stabilizer G α).relIndex K ≠ 1 := fun h =>
      hlt.not_ge (Subgroup.relIndex_eq_one.mp h)
    have hpos : (stabilizer G α).relIndex K ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  set f := (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).rangeRestrict
  have hvB := rangeRestrict_mem_longInv_block hG.odd_card hK h1B hvK hv
  have huB := rangeRestrict_mem_longInv_block hG.odd_card hK h1B huK hu.1
  have hcop : Nat.Coprime 2 (Nat.card (N.subgroupOf K)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : N ≤ K)).toEquiv]
    exact CFSG.pPrimeCore_coprime_card
  have : (N.subgroupOf K).Normal := Subgroup.Normal.subgroupOf CFSG.pPrimeCore_normal K
  have hOB := isPretransitive_pPrimeCore_range hcop
    (isPretransitive_subgroupOf_quotient_sup (stabilizer G α) N)
  obtain ⟨m, hm, hm1⟩ : ∃ m, Odd m ∧ (f ⟨v, hvK⟩ * f ⟨u, huK⟩) ^ m = 1 :=
    ⟨_, odd_orderOf_mul_of_isPretransitive hOB hvB huB, pow_orderOf_eq_one _⟩
  set w : K := ⟨v, hvK⟩ * ⟨u, huK⟩
  have hw1 : toPermHom K (K ⧸ (stabilizer G α).subgroupOf K) (w ^ m) = 1 := by
    have hfw : f (w ^ m) = 1 := by rw [map_pow, map_mul, hm1]
    exact congrArg Subtype.val hfw
  have hwm : ((w ^ m : K) : G) = (v * u) ^ m := by simp [w]
  refine odd_orderOf_of_pow_mem hm (odd_card_fixingSubgroup_inf_kernel hG hK)
    (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · rw [mem_fixingSubgroup_iff]
    rintro _ ⟨k, rfl⟩
    have h2 : (w ^ m) • ((k : K) : K ⧸ (stabilizer G α).subgroupOf K) =
        ((k : K) : K ⧸ (stabilizer G α).subgroupOf K) :=
      congrArg (fun π : Equiv.Perm (K ⧸ (stabilizer G α).subgroupOf K) =>
        π ((k : K) : K ⧸ (stabilizer G α).subgroupOf K)) hw1
    have h3 := (smul_eq_iff_blockPoint _ _).mp h2
    rw [hwm, blockPoint_mk] at h3
    exact h3
  · refine pow_mem ?_ _
    rw [Subgroup.normalCore_eq_ker, MonoidHom.mem_ker, map_mul, hvu, ← map_mul,
      mul_self_eq_one_of_mem_longInv hu.1, map_one]

end Blocks

section Lemma25


private theorem exists_conj_eq_of_not_isPretransitive {G : Type} [Group G] [Finite G] {Ω : Type}
    [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω] (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1)) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (htr : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω)
    (ih : ∀ (G' : Type) [Group G'] [Finite G'] (Ω' : Type) [MulAction G' Ω'] [Finite Ω']
      [FaithfulSMul G' Ω'], Nat.card Ω' < Nat.card Ω → IsStarGroup G' Ω' →
        HoltTheorem1Below (Nat.card G') (Nat.card Ω' + 1) →
          ∀ t ∈ longInv G' Ω', ∀ u ∈ longInv G' Ω', ∃ g : G', g * t * g⁻¹ = u)
    {t u : G} (ht : t ∈ longInv G Ω) (hu : u ∈ longInv G Ω) : ∃ g : G, g * t * g⁻¹ = u := by
  have := hG.isPretransitive
  obtain ⟨α, huα⟩ := exists_mem_longInvAt hu
  set K := stabilizer G α ⊔ CFSG.pPrimeCore 2 G
  have hK : stabilizer G α ≤ K := le_sup_left
  have hlt : stabilizer G α < K := lt_of_le_of_ne hK fun h =>
    hO (eq_bot_of_normal_le_stabilizer (α := α) (h ▸ le_sup_right))
  have h3 : 3 ≤ K.index := by
    have h1 : K.index ≠ 1 := fun h => htr (isPretransitive_of_stabilizer_sup_eq_top
      (N := CFSG.pPrimeCore 2 G) (Subgroup.index_eq_one.mp h))
    obtain ⟨k, hk⟩ := odd_index_of_le hG.odd_card hK
    omega
  have hcard : Nat.card (G ⧸ K) < Nat.card Ω := card_quotient_lt_card hlt
  have hBΨ : HoltTheorem1Below (Nat.card (toPermHom G (G ⧸ K)).range) (Nat.card (G ⧸ K) + 1) :=
    hB.of_le (card_range_toPermHom_le _) (by omega)
  obtain ⟨g', hg'⟩ := ih _ _ hcard (isStarGroup_range_quotient hG hK h3) hBΨ _
    (rangeRestrict_mem_longInv_quotient hG.odd_card hK (by omega) ht) _
    (rangeRestrict_mem_longInv_quotient hG.odd_card hK (by omega) hu)
  obtain ⟨g, rfl⟩ := (toPermHom G (G ⧸ K)).rangeRestrict_surjective g'
  have hv : g * t * g⁻¹ ∈ longInv G Ω := conj_mem_longInv ht g
  have hvu : toPermHom G (G ⧸ K) (g * t * g⁻¹) = toPermHom G (G ⧸ K) u := by
    have h := congrArg Subtype.val hg'
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.coe_rangeRestrict, map_mul,
      map_inv] using h
  obtain ⟨x, -, hx⟩ := exists_mem_zpowers_conj_eq_of_odd (mul_self_eq_one_of_mem_longInv hv)
    (mul_self_eq_one_of_mem_longInv hu) (odd_orderOf_mul_of_toPermHom_eq hG hlt huα hv hvu)
  exact ⟨x * g, by rw [← hx]; group⟩

private theorem exists_conj_eq_aux (d : ℕ) :
    ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω],
      Nat.card Ω = d → IsStarGroup G Ω → HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1) →
        ∀ t ∈ longInv G Ω, ∀ u ∈ longInv G Ω, ∃ g : G, g * t * g⁻¹ = u := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro G _ _ Ω _ _ _ hd hG hB t ht u hu
  by_cases hO : CFSG.pPrimeCore 2 G = ⊥
  · obtain ⟨D⟩ := hB.holtStructure hG
    have hO' : jOddCore G Ω = ⊥ := le_bot_iff.mp (hO ▸ jOddCore_le_pPrimeCore)
    obtain ⟨h, -, hh⟩ := D.exists_mem_iSup_conj_eq hO' ht hu
    exact ⟨h, hh⟩
  by_cases htr : IsPretransitive (CFSG.pPrimeCore 2 G) Ω
  · obtain ⟨x, -, hx⟩ := exists_mem_zpowers_conj_eq_of_odd (mul_self_eq_one_of_mem_longInv ht)
      (mul_self_eq_one_of_mem_longInv hu) (odd_orderOf_mul_of_isPretransitive htr ht hu)
    exact ⟨x, hx⟩
  exact exists_conj_eq_of_not_isPretransitive hG hB hO htr
    (fun G' _ _ Ω' _ _ _ hlt => ih _ (hd ▸ hlt) G' Ω' rfl) ht hu

variable {G : Type} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω]

theorem exists_conj_eq_of_mem_longInv (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1)) {t u : G}
    (ht : t ∈ longInv G Ω) (hu : u ∈ longInv G Ω) : ∃ g : G, g * t * g⁻¹ = u :=
  exists_conj_eq_aux _ G Ω rfl hG hB t ht u hu

theorem exists_mem_jHull_conj_eq (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1)) {t u : G}
    (ht : t ∈ longInv G Ω) (hu : u ∈ longInv G Ω) : ∃ h ∈ jHull G Ω, h * t * h⁻¹ = u := by
  obtain ⟨g, hg⟩ := exists_conj_eq_of_mem_longInv (isStarGroup_jHull hG)
    (hB.of_le (Subgroup.card_le_card_group _) le_rfl)
    (t := ⟨t, mem_jHull_of_mem_longInv ht⟩) (u := ⟨u, mem_jHull_of_mem_longInv hu⟩)
    (mem_longInv_subgroup_iff.mpr ht) (mem_longInv_subgroup_iff.mpr hu)
  exact ⟨g, g.2, congrArg Subtype.val hg⟩

end Lemma25

section WithT

namespace HoltData

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] (D : HoltData G Ω)

private theorem conj_mem_sup_zpowers_of_mem {A : Subgroup G} {h : G}
    (hA : ∀ x ∈ A, h * x * h⁻¹ ∈ A) {x : G} (hx : x ∈ A ⊔ Subgroup.zpowers D.t) :
    h * x * h⁻¹ ∈ A ⊔ Subgroup.zpowers (h * D.t * h⁻¹) := by
  have hle : A ⊔ Subgroup.zpowers D.t ≤
      (A ⊔ Subgroup.zpowers (h * D.t * h⁻¹)).comap (MulAut.conj h).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_sup_left (hA a ha)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  exact hle hx

theorem sup_zpowers_eq_of_conj {u : G} (hconj : ∃ h ∈ jHull G Ω, h * D.t * h⁻¹ = u) :
    jOddCore G Ω ⊔ (⨆ i, D.L i) ⊔ Subgroup.zpowers u = jHull G Ω := by
  obtain ⟨h, hh, rfl⟩ := hconj
  refine le_antisymm (sup_le D.socPre_le_jHull (Subgroup.zpowers_le.mpr
    (mul_mem (mul_mem hh (mem_jHull_of_mem_longInv D.t_mem)) (inv_mem hh)))) fun y hy => ?_
  have hx : h⁻¹ * y * h⁻¹⁻¹ ∈ D.socPre ⊔ Subgroup.zpowers D.t := by
    rw [D.socPre_sup_zpowers]
    exact mul_mem (mul_mem (inv_mem hh) hy) (inv_mem (inv_mem hh))
  have h1 := D.conj_mem_sup_zpowers_of_mem (fun x hx => D.conj_mem_socPre hh hx) hx
  simpa [mul_assoc] using h1

theorem mem_socPre_sup_jOrbitKernel_of_conj {u : G}
    (hconj : ∃ h ∈ jHull G Ω, h * D.t * h⁻¹ = u)
    (ht : D.t ∈ jOddCore G Ω ⊔ (⨆ i, D.L i) ⊔ jOrbitKernel G Ω) :
    u ∈ jOddCore G Ω ⊔ (⨆ i, D.L i) ⊔ jOrbitKernel G Ω := by
  obtain ⟨h, hh, rfl⟩ := hconj
  have hle : D.socPre ⊔ jOrbitKernel G Ω ≤
      (D.socPre ⊔ jOrbitKernel G Ω).comap (MulAut.conj h).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun a ha => ?_)
    · exact Subgroup.mem_sup_left (D.conj_mem_socPre hh ha)
    · exact Subgroup.mem_sup_right ((jOrbitKernel_normal).conj_mem a ha h)
  exact hle ht

variable [Finite G]

@[expose] def withConjT {u : G} (hu : u ∈ longInv G Ω)
    (hconj : ∃ h ∈ jHull G Ω, h * D.t * h⁻¹ = u) : HoltData G Ω :=
  { D with
    t := u
    t_mem := hu
    sup_eq := D.sup_zpowers_eq_of_conj hconj
    inner := fun i hi => (D.rho_mem_M_iff hu i).mpr hi
    ker_inner := fun hi =>
      ⟨D.mem_socPre_sup_jOrbitKernel_of_conj hconj (D.ker_inner hi).1, (D.ker_inner hi).2⟩ }

variable {u : G} (hu : u ∈ longInv G Ω) (hconj : ∃ h ∈ jHull G Ω, h * D.t * h⁻¹ = u)

@[simp] theorem withConjT_t : (D.withConjT hu hconj).t = u := rfl

@[simp] theorem withConjT_L (i : D.ι) : (D.withConjT hu hconj).L i = D.L i := rfl

@[simp] theorem withConjT_coord (ω : Ω) : (D.withConjT hu hconj).coord ω = D.coord ω := rfl

@[simp] theorem withConjT_M (i : D.ι) : (D.withConjT hu hconj).M i = D.M i := rfl

end HoltData

variable {G : Type} [Group G] [Finite G] {Ω : Type}
  [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω]

@[expose] def HoltData.withT (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1)) (D : HoltData G Ω) {u : G}
    (hu : u ∈ longInv G Ω) : HoltData G Ω :=
  D.withConjT hu (exists_mem_jHull_conj_eq hG hB D.t_mem hu)

namespace HoltData

variable (hG : IsStarGroup G Ω) (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1))
  (D : HoltData G Ω) {u : G} (hu : u ∈ longInv G Ω)

@[simp] theorem withT_t : (D.withT hG hB hu).t = u := rfl

@[simp] theorem withT_L (i : D.ι) : (D.withT hG hB hu).L i = D.L i := rfl

@[simp] theorem withT_coord (ω : Ω) : (D.withT hG hB hu).coord ω = D.coord ω := rfl

@[simp] theorem withT_M (i : D.ι) : (D.withT hG hB hu).M i = D.M i := rfl

end HoltData

end WithT

end CFSG.Holt.H78
