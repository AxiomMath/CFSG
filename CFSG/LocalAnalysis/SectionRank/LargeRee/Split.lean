module

public import CFSG.LocalAnalysis.SectionRank.LargeRee.RankOneData
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LieType.CentralExt.CoprimeLift

public section

namespace CFSG.SectionRank.LargeRee

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Simplicity
  CFSG.LieType.CentralExt
open scoped Pointwise

section Dihedral

variable {G : Type*} [Group G]

theorem involution_mul_pow_mul {a b : G} (ha : a * a = 1) (hb : b * b = 1) (k : ℕ) :
    a * (a * b) ^ k * a = ((a * b) ^ k)⁻¹ := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hara : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [hainv, mul_inv_rev, hainv, hbinv, ← mul_assoc, ha, one_mul]
  calc a * (a * b) ^ k * a = a * (a * b) ^ k * a⁻¹ := by rw [hainv]
    _ = (a * (a * b) * a⁻¹) ^ k := conj_pow.symm
    _ = ((a * b) ^ k)⁻¹ := by rw [hara, inv_pow]

theorem exists_eq_of_mem_closure_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1) {m : ℕ}
    (hm : 0 < m) (hab : (a * b) ^ m = 1) {x : G} (hx : x ∈ Subgroup.closure ({a, b} : Set G)) :
    ∃ k : ℕ, x = (a * b) ^ k ∨ x = (a * b) ^ k * a := by
  set r := a * b with hr
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hinvpow : ∀ k : ℕ, (r ^ k)⁻¹ = r ^ (m * k - k) := fun k => by
    rw [eq_comm, ← mul_inv_eq_one, inv_inv, ← pow_add,
      Nat.sub_add_cancel (Nat.le_mul_of_pos_left k hm), pow_mul, hab, one_pow]
  have hconj := involution_mul_pow_mul ha hb
  have hSa : ∀ y : G, (∃ k : ℕ, y = r ^ k ∨ y = r ^ k * a) →
      ∃ k : ℕ, a * y = r ^ k ∨ a * y = r ^ k * a := by
    rintro y ⟨k, rfl | rfl⟩
    · refine ⟨m * k - k, Or.inr ?_⟩
      rw [← hinvpow, ← hconj k, mul_assoc, ha, mul_one]
    · refine ⟨m * k - k, Or.inl ?_⟩
      rw [← hinvpow, ← mul_assoc, hconj k]
  have hSr : ∀ y : G, (∃ k : ℕ, y = r ^ k ∨ y = r ^ k * a) →
      ∃ k : ℕ, r * y = r ^ k ∨ r * y = r ^ k * a := by
    rintro y ⟨k, rfl | rfl⟩
    · exact ⟨k + 1, Or.inl (pow_succ' r k).symm⟩
    · exact ⟨k + 1, Or.inr (by rw [← mul_assoc, ← pow_succ'])⟩
  have hbr : b = a * r := by rw [hr, ← mul_assoc, ha, one_mul]
  have hSb : ∀ y : G, (∃ k : ℕ, y = r ^ k ∨ y = r ^ k * a) →
      ∃ k : ℕ, b * y = r ^ k ∨ b * y = r ^ k * a := by
    intro y hy
    rw [hbr, mul_assoc]
    exact hSa _ (hSr y hy)
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨0, Or.inl (pow_zero r).symm⟩
  | mul_left x hx y _ ih =>
    rcases hx with rfl | rfl
    · exact hSa _ ih
    · exact hSb _ ih
  | inv_mul_cancel x hx y _ ih =>
    rcases hx with rfl | rfl
    · rw [hainv]; exact hSa _ ih
    · rw [hbinv]; exact hSb _ ih

theorem pow_two_mul_eq_one_of_mem_closure_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    {m : ℕ} (hm : 0 < m) (hab : (a * b) ^ m = 1) {x : G}
    (hx : x ∈ Subgroup.closure ({a, b} : Set G)) : x ^ (2 * m) = 1 := by
  obtain ⟨k, rfl | rfl⟩ := exists_eq_of_mem_closure_pair ha hb hm hab hx
  · rw [← pow_mul, show k * (2 * m) = m * (2 * k) by ring, pow_mul, hab, one_pow]
  · have h2 : (a * b) ^ k * a * ((a * b) ^ k * a) = 1 := by
      rw [show (a * b) ^ k * a * ((a * b) ^ k * a) = (a * b) ^ k * (a * (a * b) ^ k * a) by
        group, involution_mul_pow_mul ha hb, mul_inv_cancel]
    rw [pow_mul, sq, h2, one_pow]

end Dihedral

section Split

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem isPGroup_relWeylRee
    : IsPGroup 2 ReeTag.F4.relWeylRee := by
  intro w
  refine ⟨4, ?_⟩
  have hrange : Set.range blockGen = ({blockGen 0, blockGen 1} : Set ReeTag.F4.relWeylRee) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl) <;> exact ⟨_, rfl⟩
  have hw : w ∈ Subgroup.closure ({blockGen 0, blockGen 1} : Set ReeTag.F4.relWeylRee) := by
    rw [← hrange, closure_range_blockGen]
    exact Subgroup.mem_top w
  have := pow_two_mul_eq_one_of_mem_closure_pair (blockGen_mul_self 0) (blockGen_mul_self 1)
    (by norm_num : 0 < 8) blockGen_mul_pow_eight hw
  simpa using this

theorem reeBorelPart_eq_sup :
    reeBorelPart ReeTag.F4 K a = reeUnipPart ReeTag.F4 K a ⊔ reeTorusPart ReeTag.F4 K a := by
  refine le_antisymm (fun b hb => ?_) (sup_le (fun u hu => ?_) (fun h hh => ?_))
  · obtain ⟨s, hs, c, hc, rfl⟩ := exists_mul_of_mem_reeBorelPart a hb
    exact mul_mem (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right hc)
  · exact (nativeData ReeTag.F4.tag K).U_le_B hu
  · exact (nativeData ReeTag.F4.tag K).H_le_B hh

theorem conj_pLift_mem_liftSubgroup {G E : Type*} [Group G] [Group E] [Finite E] {π : E →* G}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hC : ¬ 2 ∣ Nat.card π.ker)
    {U : Subgroup G} (hU : IsPGroup 2 U) {g : G} (hg : g ∈ U) (e : E)
    (h : π e * g * (π e)⁻¹ ∈ U) : e * pLift 2 π g * e⁻¹ ∈ liftSubgroup 2 π U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, k, hk⟩ := (mem_liftSubgroup_iff hcen hU).1 (pLift_mem_liftSubgroup hπ hcen hC hU hg)
  refine (mem_liftSubgroup_iff hcen hU).2 ⟨?_, k, ?_⟩
  · rw [map_mul, map_mul, map_inv, map_pLift hπ hC (exists_orderOf_eq_pow_of_mem hU ⟨g, hg⟩)]
    exact h
  · rw [← hk]
    exact orderOf_injective (MulAut.conj e).toMonoidHom (MulAut.conj e).injective _

variable {E : Type*} [Group E] [Finite E] {π : E →* reeFixed ReeTag.F4 K a}

omit [Finite E] in
theorem isPGroup_reeUnipPart_F4 : IsPGroup 2 (reeUnipPart ReeTag.F4 K a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  exact ((nativeRootSubgroups ReeTag.F4.tag K).isPGroup_U 2).comap_of_injective _
    Subtype.val_injective

theorem rankOne_lift_relation (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1))
    (hcen : π.ker ≤ Subgroup.center E) (hC2 : ¬ 2 ∣ Nat.card π.ker) (i : Fin 2)
    {Th : Subgroup E}
    (hThinv : ∀ y : E, π y ∈ blockT a hK i →
      pLift 2 π (relNrepHom K a (blockGen i)) * y * (pLift 2 π (relNrepHom K a (blockGen i)))⁻¹ =
        y⁻¹ → y ∈ Th)
    (hinvT : ∀ t ∈ blockT a hK i,
      relNrepHom K a (blockGen i) * t * (relNrepHom K a (blockGen i))⁻¹ = t⁻¹)
    (hcells : RankOneCells a i (blockT a hK i)) (hsec : RankOneSection a π i (blockT a hK i))
    {x : reeFixed ReeTag.F4 K a} (hx : x ∈ blockX (K := K) a i) :
    ∃ t₁ ∈ Th, ∃ y₁ ∈ liftSubgroup 2 π (reeUnipPart ReeTag.F4 K a),
      pLift 2 π (relNrepHom K a (blockGen i)) * pLift 2 π x *
          pLift 2 π (relNrepHom K a (blockGen i)) = t₁ * y₁ ∨
        ∃ y₂ ∈ liftSubgroup 2 π (reeUnipPart ReeTag.F4 K a),
          pLift 2 π (relNrepHom K a (blockGen i)) * pLift 2 π x *
            pLift 2 π (relNrepHom K a (blockGen i)) =
              t₁ * y₁ * pLift 2 π (relNrepHom K a (blockGen i)) * y₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := isPGroup_reeUnipPart_F4 (K := K) (a := a)
  set nh := pLift 2 π (relNrepHom K a (blockGen i))
  obtain ⟨R, r, hr, hXR, hTR, hnR⟩ := hsec
  have hr2 : ∀ g : R, (∃ k : ℕ, orderOf (g : reeFixed ReeTag.F4 K a) = 2 ^ k) →
      r g = pLift 2 π g := by
    intro g ⟨k, hk⟩
    refine (pLift_unique hcen hC2 (hr g) ?_).symm
    have hd : orderOf (r g) ∣ 2 ^ k := by
      rw [← hk, Subgroup.orderOf_coe g]
      exact orderOf_map_dvd r g
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    exact ⟨j, hj⟩
  have hXU : ∀ {y : reeFixed ReeTag.F4 K a}, y ∈ blockX (K := K) a i →
      y ∈ reeUnipPart ReeTag.F4 K a := fun hy => UminusFixed_le_reeUnipPart _ hy
  have hrX : ∀ {y : reeFixed ReeTag.F4 K a} (hy : y ∈ blockX (K := K) a i),
      r ⟨y, hXR hy⟩ = pLift 2 π y ∧
        r ⟨y, hXR hy⟩ ∈ liftSubgroup 2 π (reeUnipPart ReeTag.F4 K a) := by
    intro y hy
    obtain ⟨k, hk⟩ := exists_orderOf_eq_pow_of_mem hU ⟨y, hXU hy⟩
    have hyo : orderOf (⟨y, hXR hy⟩ : R) = 2 ^ k := by
      rw [Subgroup.orderOf_mk]
      exact hk
    refine ⟨hr2 _ ⟨k, hk⟩, (mem_liftSubgroup_iff hcen hU).2 ⟨?_,
      exists_orderOf_map_eq_pow r ⟨k, hyo⟩⟩⟩
    rw [hr]
    exact hXU hy
  have hrn : r ⟨_, hnR⟩ = nh := by
    refine hr2 _ ⟨1, ?_⟩
    rw [pow_one]
    apply orderOf_eq_prime
    · rw [sq]; exact relNrepHom_blockGen_mul_self i
    · intro h1
      have := congrArg (fun z : reeFixed ReeTag.F4 K a => (z : adjointGroup ReeTag.F4.tag K)) h1
      simp only [coe_relNrepHom, Subgroup.coe_one] at this
      exact blockGen_ne_one i (Subtype.ext (nrep_injective ReeTag.F4.tag K
        (by rw [this, Subgroup.coe_one, CFSG.LieType.Chevalley.nrep_one])))
  have hrT : ∀ {t : reeFixed ReeTag.F4 K a} (ht : t ∈ blockT a hK i), r ⟨t, hTR ht⟩ ∈ Th := by
    intro t ht
    have hconj : nh * r ⟨t, hTR ht⟩ * nh⁻¹ = (r ⟨t, hTR ht⟩)⁻¹ := by
      rw [← hrn, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
      congr 1
      exact Subtype.ext (hinvT t ht)
    exact hThinv _ (by rw [hr]; exact ht) hconj
  have hmid : nh * pLift 2 π x * nh = r (⟨_, hnR⟩ * ⟨x, hXR hx⟩ * ⟨_, hnR⟩) := by
    rw [map_mul, map_mul, hrn, (hrX hx).1]
  rcases hcells x hx with ⟨t, ht, y, hy, h⟩ | ⟨t, ht, y, hy, y', hy', h⟩
  · have e : (⟨_, hnR⟩ * ⟨x, hXR hx⟩ * ⟨_, hnR⟩ : R) = ⟨t, hTR ht⟩ * ⟨y, hXR hy⟩ :=
      Subtype.ext h
    refine ⟨_, hrT ht, _, (hrX hy).2, Or.inl ?_⟩
    rw [hmid, e, map_mul]
  · have e : (⟨_, hnR⟩ * ⟨x, hXR hx⟩ * ⟨_, hnR⟩ : R) =
        ⟨t, hTR ht⟩ * ⟨y, hXR hy⟩ * ⟨_, hnR⟩ * ⟨y', hXR hy'⟩ := Subtype.ext h
    refine ⟨_, hrT ht, _, (hrX hy).2, Or.inr ⟨_, (hrX hy').2, ?_⟩⟩
    rw [hmid, e, map_mul, map_mul, map_mul, hrn]

theorem exists_section_of_rankOne (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1))
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) (hcells : ∀ i, RankOneCells a i (blockT a hK i))
    (hsec : ∀ i, RankOneSection a π i (blockT a hK i)) :
    ∃ s : reeFixed ReeTag.F4 K a →* E, ∀ x, π (s x) = x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hC2 : ¬ 2 ∣ Nat.card π.ker := fun h =>
    (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)
  have hD : IsPGroup 2 (relNrepHom K a).range :=
    isPGroup_relWeylRee.of_surjective _ (MonoidHom.rangeRestrict_surjective (relNrepHom K a))
  obtain ⟨ν, hνπ, hνpLift'⟩ : ∃ ν : ReeTag.F4.relWeylRee →* E,
      (∀ w, π (ν w) = relNrepHom K a w) ∧ ∀ w, ν w = pLift 2 π (relNrepHom K a w) :=
    ⟨(pLiftHom hπ hcen hC2 hD).comp (relNrepHom K a).rangeRestrict,
      fun w => map_pLiftHom hπ hcen hC2 hD _, fun w => rfl⟩
  have hν2 : ∀ i, ν (blockGen i) * ν (blockGen i) = 1 := fun i => by
    rw [← map_mul, blockGen_mul_self, map_one]
  have hνinv : ∀ i, (ν (blockGen i))⁻¹ = ν (blockGen i) := fun i =>
    inv_eq_of_mul_eq_one_right (hν2 i)
  have hνpLift : ∀ i, ν (blockGen i) = pLift 2 π (relNrepHom K a (blockGen i)) := fun i =>
    hνpLift' _
  set U₀ := reeUnipPart ReeTag.F4 K a with hU₀
  have hU : IsPGroup 2 U₀ :=
    ((nativeRootSubgroups ReeTag.F4.tag K).isPGroup_U 2).comap_of_injective _
      Subtype.val_injective
  obtain ⟨Uh, hUhmem, hUhequiv⟩ : ∃ Uh : Subgroup E,
      (∀ {e : E}, e ∈ Uh ↔ π e ∈ U₀ ∧ ∃ k : ℕ, orderOf e = 2 ^ k) ∧ Uh = liftSubgroup 2 π U₀ :=
    ⟨_, fun {e} => mem_liftSubgroup_iff hcen hU, rfl⟩
  have hUhconj : ∀ {u : E} (e : E), u ∈ Uh → π (e * u * e⁻¹) ∈ U₀ → e * u * e⁻¹ ∈ Uh := by
    intro u e hu h
    obtain ⟨-, k, hk⟩ := hUhmem.1 hu
    refine hUhmem.2 ⟨h, k, ?_⟩
    rw [← hk]
    exact orderOf_injective (MulAut.conj e).toMonoidHom (MulAut.conj e).injective u
  have hUhinj : ∀ u ∈ Uh, π u = 1 → u = 1 := by
    intro u hu h1
    subst hUhequiv
    have h := (liftSubgroupEquiv hπ hcen hC2 hU).injective
      (a₁ := ⟨u, hu⟩) (a₂ := 1) (Subtype.ext (by simpa [liftSubgroupEquiv] using h1))
    exact congrArg Subtype.val h
  have hUheq : ∀ {u u' : E}, u ∈ Uh → u' ∈ Uh → π u = π u' → u = u' := by
    intro u u' hu hu' h
    exact mul_inv_eq_one.1 (hUhinj _ (mul_mem hu (inv_mem hu'))
      (by rw [map_mul, map_inv, h, mul_inv_cancel]))
  have hlift : ∀ {g : reeFixed ReeTag.F4 K a}, g ∈ U₀ →
      pLift 2 π g ∈ Uh ∧ π (pLift 2 π g) = g := fun hg =>
    ⟨hUhequiv ▸ pLift_mem_liftSubgroup hπ hcen hC2 hU hg,
      map_pLift hπ hC2 (exists_orderOf_eq_pow_of_mem hU ⟨_, hg⟩)⟩
  have hUhmap : Uh.map π = U₀ := by
    refine le_antisymm ?_ (fun g hg => ⟨_, (hlift hg).1, (hlift hg).2⟩)
    rintro _ ⟨u, hu, rfl⟩
    exact (hUhmem.1 hu).1
  have hUh_of : ∀ {e : E}, π e ∈ U₀ → (∃ k : ℕ, orderOf e = 2 ^ k) → e ∈ Uh := fun h1 h2 =>
    hUhmem.2 ⟨h1, h2⟩
  have hT0 : IsCyclic (blockT a hK 0) :=
    (inferInstance : IsCyclic (reeTorusSub a hK fi_zero_mem_longSet))
  have hT1 : IsCyclic (blockT a hK 1) :=
    (inferInstance : IsCyclic (reeTorusSub a hK fi_one_mem_longSet))
  have hcomm : ∀ x ∈ blockT a hK 0, ∀ y ∈ blockT a hK 1, Commute x y := fun x hx y hy =>
    commute_of_mem_reeTorusPart (reeTorusSub_le_reeTorusPart hK _ hx)
      (reeTorusSub_le_reeTorusPart hK _ hy)
  have hdisj : blockT a hK 0 ⊓ blockT a hK 1 = ⊥ := reeTorusSub_inf hK
  have hinv := relNrepHom_inv_reeTorusSub (K := K) (a := a) hK
  have hcross := relNrepHom_cross_reeTorusSub (K := K) (a := a) hK
  obtain ⟨Th, hThmap, hThinj, hTh0, hTh1, hThinv0, hThinv1⟩ :=
    exists_torus_lift hπ hcen hodd (T₁ := blockT a hK 0) (T₂ := blockT a hK 1) hcomm hdisj
      (hν2 0) (hν2 1) (fun t ht => by rw [hνπ]; exact hinv.1 t ht)
      (fun t ht => by rw [hνπ]; exact hinv.2 t ht) (fun t ht => by rw [hνπ]; exact hcross.1 t ht)
      (fun t ht => by rw [hνπ]; exact hcross.2 t ht)
  have hThn : ∀ i, ∀ x ∈ Th, ν (blockGen i) * x * (ν (blockGen i))⁻¹ ∈ Th := by
    intro i x hx
    match i with
    | 0 => exact hTh0 x hx
    | 1 => exact hTh1 x hx
  have hnorm : ∀ i, ν (blockGen i) ∈ Subgroup.normalizer (Th : Set E) := by
    intro i
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hThn i x, fun hx => ?_⟩
    have h := hThn i _ hx
    have e : ν (blockGen i) * (ν (blockGen i) * x * (ν (blockGen i))⁻¹) *
        (ν (blockGen i))⁻¹ = x := by
      rw [hνinv i, show ν (blockGen i) * (ν (blockGen i) * x * ν (blockGen i)) * ν (blockGen i) =
        (ν (blockGen i) * ν (blockGen i)) * x * (ν (blockGen i) * ν (blockGen i)) by group,
        hν2, one_mul, mul_one]
    rwa [e] at h
  have hνnorm : ∀ w, ν w ∈ Subgroup.normalizer (Th : Set E) := by
    have hle : ν.range ≤ Subgroup.normalizer (Th : Set E) := by
      rw [MonoidHom.range_eq_map, ← closure_range_blockGen, MonoidHom.map_closure,
        Subgroup.closure_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact hnorm i
    exact fun w => hle ⟨w, rfl⟩
  have hThconj : ∀ w, ∀ x ∈ Th, (ν w)⁻¹ * x * ν w ∈ Th := by
    intro w x hx
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem (hνnorm w)) x).1 hx
    rwa [inv_inv] at this
  have hThH : ∀ t ∈ Th, π t ∈ reeTorusPart ReeTag.F4 K a := by
    intro t ht
    have h : π t ∈ Th.map π := ⟨t, ht, rfl⟩
    rw [hThmap] at h
    rw [reeTorusPart_eq_sup hK]
    exact h
  have hHU : ∀ h ∈ reeTorusPart ReeTag.F4 K a, ∀ g ∈ U₀, h * g * h⁻¹ ∈ U₀ := by
    intro h hh g hg
    have hn := (nativeRootSubgroups ReeTag.F4.tag K).B_le_normalizer_U
      ((nativeData ReeTag.F4.tag K).H_le_B hh)
    exact (Subgroup.mem_normalizer_iff.1 hn _).1 hg
  have hThU : Th ≤ Subgroup.normalizer (Uh : Set E) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      refine hUhconj t hu ?_
      rw [map_mul, map_mul, map_inv]
      exact hHU _ (hThH t ht) _ (hUhmem.1 hu).1
    · intro hu
      have h := hUhconj t⁻¹ hu (by
        rw [map_mul, map_mul, map_inv, map_inv, map_inv, inv_inv]
        have := hHU _ (inv_mem (hThH t ht)) _ (hUhmem.1 hu).1
        rw [inv_inv] at this
        simpa [mul_assoc] using this)
      simpa [mul_assoc] using h
  set Bh := Uh ⊔ Th with hBh
  have hBmem : ∀ {b : E}, b ∈ Bh → ∃ u ∈ Uh, ∃ t ∈ Th, b = u * t := by
    intro b hb
    have hb' : b ∈ ((Uh : Set E) * (Th : Set E)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Uh Th hThU]
      exact hb
    obtain ⟨u, hu, t, ht, rfl⟩ := hb'
    exact ⟨u, hu, t, ht, rfl⟩
  have hBmap : Bh.map π = reeBorelPart ReeTag.F4 K a := by
    rw [hBh, Subgroup.map_sup, hUhmap, hThmap]
    refine (reeBorelPart_eq_sup (K := K) (a := a)).trans ?_ |>.symm
    rw [reeTorusPart_eq_sup hK]
    rfl
  have hBinj : ∀ b ∈ Bh, π b = 1 → b = 1 := by
    intro b hb h1
    obtain ⟨u, hu, t, ht, rfl⟩ := hBmem hb
    rw [map_mul] at h1
    have hut : π u = (π t)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hmem : ((π u : reeFixed ReeTag.F4 K a) : adjointGroup ReeTag.F4.tag K) ∈
        (nativeData ReeTag.F4.tag K).H ⊓ (nativeData ReeTag.F4.tag K).U :=
      ⟨by rw [hut]; exact (reeTorusPart ReeTag.F4 K a).inv_mem (hThH t ht), (hUhmem.1 hu).1⟩
    rw [H_inf_U_eq_bot 2, Subgroup.mem_bot] at hmem
    have hu1 : π u = 1 := Subtype.ext hmem
    have ht1 : π t = 1 := by rw [← inv_inj, ← hut, hu1, inv_one]
    rw [hUhinj u hu hu1, hThinj t ht ht1, one_mul]
  have hdecomp : ∀ i, ∀ b ∈ Bh, ∃ v : reeFixed ReeTag.F4 K a,
      v ∈ UplusFixed ReeTag.F4 K a (blockGen i) ∧ ∃ x ∈ blockX (K := K) a i, ∃ t ∈ Th,
        b = pLift 2 π v * pLift 2 π x * t := by
    intro i b hb
    obtain ⟨u, hu, t, ht, rfl⟩ := hBmem hb
    obtain ⟨v, hv, x, hx, hvx⟩ :=
      exists_mem_UplusFixed_blockGen_mem_UminusFixed (K := K) (a := a) i (hUhmem.1 hu).1
    have hvU := UplusFixed_le_reeUnipPart (t := ReeTag.F4) (K := K) (a := a) _ hv
    have hxU := UminusFixed_le_reeUnipPart (t := ReeTag.F4) (K := K) (a := a) _ hx
    refine ⟨v, hv, x, hx, t, ht, ?_⟩
    rw [hUheq hu (mul_mem (hlift hvU).1 (hlift hxU).1)
      (by rw [map_mul, (hlift hvU).2, (hlift hxU).2, hvx])]
  have hcell : ∀ i w, (coxeterSystem ReeTag.F4.tag).length
      ((blockGen i * w : ReeTag.F4.relWeylRee) : WeylGroup ReeTag.F4.tag) =
        (coxeterSystem ReeTag.F4.tag).length (blockGen i : WeylGroup ReeTag.F4.tag) +
          (coxeterSystem ReeTag.F4.tag).length (w : WeylGroup ReeTag.F4.tag) →
      ∀ b ∈ Bh, ∃ b₁ ∈ Bh, ∃ b₂ ∈ Bh,
        ν (blockGen i) * b * ν w = b₁ * ν (blockGen i * w) * b₂ := by
    intro i w hlen b hb
    obtain ⟨v, hv, x, hx, t, ht, rfl⟩ := hdecomp i b hb
    have hvU : v ∈ U₀ := UplusFixed_le_reeUnipPart (t := ReeTag.F4) (K := K) (a := a) _ hv
    have hxU : x ∈ U₀ := UminusFixed_le_reeUnipPart (t := ReeTag.F4) (K := K) (a := a) _ hx
    have hv' : relNrepHom K a (blockGen i) * v * (relNrepHom K a (blockGen i))⁻¹ ∈ U₀ :=
      UplusFixed_le_reeUnipPart (t := ReeTag.F4) (K := K) (a := a) _
        (relNrepHom_blockGen_conj_mem_UplusFixed i hv)
    have hx' : (relNrepHom K a w)⁻¹ * x * relNrepHom K a w ∈ U₀ :=
      inv_relNrepHom_conj_mem_reeUnipPart i w hlen hx
    have h₁ : ν (blockGen i) * pLift 2 π v * (ν (blockGen i))⁻¹ ∈ Uh := by
      rw [hUhequiv]
      exact conj_pLift_mem_liftSubgroup hπ hcen hC2 hU hvU _ (by rw [hνπ]; exact hv')
    have h₂ : (ν w)⁻¹ * pLift 2 π x * ν w ∈ Uh := by
      have h := conj_pLift_mem_liftSubgroup hπ hcen hC2 hU hxU (ν w)⁻¹
        (by rw [map_inv, hνπ, inv_inv]; exact hx')
      rw [hUhequiv]
      rwa [inv_inv] at h
    refine ⟨_, Subgroup.mem_sup_left h₁, _, mul_mem (Subgroup.mem_sup_left h₂)
      (Subgroup.mem_sup_right (hThconj w t ht)), ?_⟩
    rw [MonoidHom.map_mul ν (blockGen i) w]
    group
  have hrank : ∀ i, ∀ b ∈ Bh, ν (blockGen i) * b * ν (blockGen i) ∈ Bh ∨
      ∃ b₁ ∈ Bh, ∃ b₂ ∈ Bh, ν (blockGen i) * b * ν (blockGen i) = b₁ * ν (blockGen i) * b₂ := by
    intro i b hb
    obtain ⟨v, hv, x, hx, t, ht, rfl⟩ := hdecomp i b hb
    have hvU : v ∈ U₀ := UplusFixed_le_reeUnipPart (t := ReeTag.F4) (K := K) (a := a) _ hv
    have hv' : relNrepHom K a (blockGen i) * v * (relNrepHom K a (blockGen i))⁻¹ ∈ U₀ :=
      UplusFixed_le_reeUnipPart (t := ReeTag.F4) (K := K) (a := a) _
        (relNrepHom_blockGen_conj_mem_UplusFixed i hv)
    have hb₁ : ν (blockGen i) * pLift 2 π v * (ν (blockGen i))⁻¹ ∈ Bh := by
      refine Subgroup.mem_sup_left ?_
      rw [hUhequiv]
      exact conj_pLift_mem_liftSubgroup hπ hcen hC2 hU hvU _ (by rw [hνπ]; exact hv')
    have hb₂ : (ν (blockGen i))⁻¹ * t * ν (blockGen i) ∈ Bh :=
      Subgroup.mem_sup_right (hThconj _ t ht)
    have e : ν (blockGen i) * (pLift 2 π v * pLift 2 π x * t) * ν (blockGen i) =
        (ν (blockGen i) * pLift 2 π v * (ν (blockGen i))⁻¹) *
          (ν (blockGen i) * pLift 2 π x * ν (blockGen i)) *
            ((ν (blockGen i))⁻¹ * t * ν (blockGen i)) := by
      group
    rw [e]
    have hThinv : ∀ y : E, π y ∈ blockT a hK i →
        pLift 2 π (relNrepHom K a (blockGen i)) * y *
          (pLift 2 π (relNrepHom K a (blockGen i)))⁻¹ = y⁻¹ → y ∈ Th := by
      intro y hy hyn
      rw [← hνpLift] at hyn
      match i with
      | 0 => exact hThinv0 y hy hyn
      | 1 => exact hThinv1 y hy hyn
    have hinvT : ∀ t ∈ blockT a hK i,
        relNrepHom K a (blockGen i) * t * (relNrepHom K a (blockGen i))⁻¹ = t⁻¹ := by
      intro t ht
      match i with
      | 0 => exact hinv.1 t ht
      | 1 => exact hinv.2 t ht
    obtain ⟨t₁, ht₁, y₁, hy₁, h | ⟨y₂, hy₂, h⟩⟩ :=
      rankOne_lift_relation hK hcen hC2 i hThinv hinvT (hcells i) (hsec i) hx
    · left
      have h' : ν (blockGen i) * pLift 2 π x * ν (blockGen i) = t₁ * y₁ := by
        rw [hνpLift]; exact h
      rw [h']
      exact mul_mem (mul_mem hb₁ (mul_mem (Subgroup.mem_sup_right ht₁)
        (Subgroup.mem_sup_left (hUhequiv ▸ hy₁)))) hb₂
    · right
      have h' : ν (blockGen i) * pLift 2 π x * ν (blockGen i) =
          t₁ * y₁ * ν (blockGen i) * y₂ := by
        rw [hνpLift]; exact h
      rw [h']
      refine ⟨_ * (t₁ * y₁), mul_mem hb₁ (mul_mem (Subgroup.mem_sup_right ht₁)
        (Subgroup.mem_sup_left (hUhequiv ▸ hy₁))), y₂ * _,
        mul_mem (Subgroup.mem_sup_left (hUhequiv ▸ hy₂)) hb₂, ?_⟩
      group
  have hgen : Subgroup.closure ((reeBorelPart ReeTag.F4 K a : Set (reeFixed ReeTag.F4 K a)) ∪
      Set.range fun i => π (ν (blockGen i))) = ⊤ := by
    have : (fun i => π (ν (blockGen i))) = fun i => relNrepHom K a (blockGen i) :=
      funext fun i => hνπ _
    rw [this]
    exact closure_reeBorelPart_union_blockGen K a
  have hdisj' : ∀ w, ∀ b₁ ∈ reeBorelPart ReeTag.F4 K a, ∀ b₂ ∈ reeBorelPart ReeTag.F4 K a,
      b₁ * π (ν w) * b₂ = 1 → w = 1 := fun w b₁ hb₁ b₂ hb₂ h =>
    eq_one_of_mul_relNrepHom_mul_eq_one w hb₁ hb₂ (by rwa [← hνπ])
  obtain ⟨J, hJmap, hJinj⟩ := exists_lift_subgroup_of_bruhat' π (reeBorelPart ReeTag.F4 K a) Bh
    hBmap hBinj ν (map_one ν) blockGen blockGen_mul_self
    (fun i w => (coxeterSystem ReeTag.F4.tag).length ((blockGen i * w : ReeTag.F4.relWeylRee) :
        WeylGroup ReeTag.F4.tag) =
      (coxeterSystem ReeTag.F4.tag).length (blockGen i : WeylGroup ReeTag.F4.tag) +
        (coxeterSystem ReeTag.F4.tag).length (w : WeylGroup ReeTag.F4.tag))
    length_blockGen_mul_or_mul
    (fun i w _ => MonoidHom.map_mul ν (blockGen i) w) hν2 hgen hdisj' hcell hrank
  exact exists_section_of_lift_subgroup π hJmap hJinj

end Split

end CFSG.SectionRank.LargeRee
