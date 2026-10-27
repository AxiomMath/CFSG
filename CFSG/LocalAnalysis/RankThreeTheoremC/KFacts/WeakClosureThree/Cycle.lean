module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Wreath
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Witness
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SigmaDich
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.AbelianTransfer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne.StrongP (HasNoncommPair)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
open CFSG.GroupTheory.WeirSylow
open scoped commutatorElement

structure CycleData {G : Type*} [Group G] (u v w y : G) : Prop where
  uv : u * v = v * u
  uw : u * w = w * u
  vw : v * w = w * v
  u3 : u ^ 3 = 1
  v3 : v ^ 3 = 1
  w3 : w ^ 3 = 1
  y3 : y ^ 3 = 1
  c1 : y * u * y⁻¹ = v
  c2 : y * v * y⁻¹ = w
  c3 : y * w * y⁻¹ = u
  ne1 : u ≠ v
  ne2 : v ≠ w
  ne3 : u * v⁻¹ ≠ v * w⁻¹
  ne4 : (u * v⁻¹) ^ 2 ≠ v * w⁻¹

@[expose] def CycleWitness (G : Type) [Group G] : Prop :=
  ∃ u v w y : G, CycleData u v w y

@[expose] def ThreeLocal (G : Type) [Group G] [Finite G] : Prop :=
  (∀ S : Sylow 3 G, IsMulCommutative (S : Subgroup G)) ∨ CycleWitness G

section Basic

variable {G : Type} [Group G] {u v w y : G}

theorem CycleData.isPGroup (h : CycleData u v w y) :
    IsPGroup 3 (closure ({u, v, w, y} : Set G)) :=
  isPGroup_closure_cycle h.uv h.uw h.vw h.u3 h.v3 h.w3 h.y3 h.c1 h.c2 h.c3

theorem CycleData.comm_u (h : CycleData u v w y) : ⁅u, y⁆ = u * v⁻¹ := by
  have : y * u⁻¹ * y⁻¹ = v⁻¹ := by
    rw [← h.c1]
    group
  rw [commutatorElement_def, ← this]
  group

theorem CycleData.comm_v (h : CycleData u v w y) : ⁅v, y⁆ = v * w⁻¹ := by
  have : y * v⁻¹ * y⁻¹ = w⁻¹ := by
    rw [← h.c2]
    group
  rw [commutatorElement_def, ← this]
  group

private theorem pow_three_mul_inv {a b : G} (hab : a * b = b * a) (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) : (a * b⁻¹) ^ 3 = 1 := by
  have hc : Commute a b⁻¹ := (show Commute a b from hab).inv_right
  rw [hc.mul_pow, ha, inv_pow, hb, inv_one, one_mul]

theorem CycleData.map_of_injOn {H : Type} [Group H] (h : CycleData u v w y) (φ : G →* H)
    (hφ : Set.InjOn φ (closure ({u, v, w, y} : Set G))) :
    CycleData (φ u) (φ v) (φ w) (φ y) := by
  have hu : u ∈ closure ({u, v, w, y} : Set G) := subset_closure (by simp)
  have hv : v ∈ closure ({u, v, w, y} : Set G) := subset_closure (by simp)
  have hw : w ∈ closure ({u, v, w, y} : Set G) := subset_closure (by simp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, h.uv]
  · rw [← map_mul, ← map_mul, h.uw]
  · rw [← map_mul, ← map_mul, h.vw]
  · rw [← map_pow, h.u3, map_one]
  · rw [← map_pow, h.v3, map_one]
  · rw [← map_pow, h.w3, map_one]
  · rw [← map_pow, h.y3, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, h.c1]
  · rw [← map_inv, ← map_mul, ← map_mul, h.c2]
  · rw [← map_inv, ← map_mul, ← map_mul, h.c3]
  · exact fun he => h.ne1 (hφ hu hv he)
  · exact fun he => h.ne2 (hφ hv hw he)
  · intro he
    rw [← map_inv, ← map_mul, ← map_inv, ← map_mul] at he
    exact h.ne3 (hφ (mul_mem hu (inv_mem hv)) (mul_mem hv (inv_mem hw)) he)
  · intro he
    rw [← map_inv, ← map_mul, ← map_pow, ← map_inv, ← map_mul] at he
    exact h.ne4 (hφ (pow_mem (mul_mem hu (inv_mem hv)) 2) (mul_mem hv (inv_mem hw)) he)

theorem CycleData.of_coe {H : Subgroup G} {a b c d : H}
    (h : CycleData (a : G) (b : G) (c : G) (d : G)) : CycleData a b c d := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact Subtype.ext (by simpa using h.uv) | exact Subtype.ext (by simpa using h.uw)
    | exact Subtype.ext (by simpa using h.vw) | exact Subtype.ext (by simpa using h.u3)
    | exact Subtype.ext (by simpa using h.v3) | exact Subtype.ext (by simpa using h.w3)
    | exact Subtype.ext (by simpa using h.y3) | exact Subtype.ext (by simpa using h.c1)
    | exact Subtype.ext (by simpa using h.c2) | exact Subtype.ext (by simpa using h.c3)
    | exact fun he => h.ne1 (by simpa using congrArg Subtype.val he)
    | exact fun he => h.ne2 (by simpa using congrArg Subtype.val he)
    | exact fun he => h.ne3 (by simpa using congrArg Subtype.val he)
    | exact fun he => h.ne4 (by simpa using congrArg Subtype.val he)

theorem CycleWitness.map {H : Type} [Group H] (φ : G →* H) (hφ : Function.Injective φ)
    (h : CycleWitness G) : CycleWitness H := by
  obtain ⟨u, v, w, y, h⟩ := h
  exact ⟨_, _, _, _, h.map_of_injOn φ (hφ.injOn)⟩

end Basic

section Finite

variable {G : Type} [Group G] [Finite G]

theorem dichThreeLieAt_of_cycleWitness (hw : CycleWitness G) : DichThreeLieAt G := by
  obtain ⟨u, v, w, y, h⟩ := hw
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set U : Subgroup G := closure ({u, v, w, y} : Set G) with hUdef
  have hU : IsPGroup 3 U := h.isPGroup
  have hpair : HasNoncommPair 3 G := by
    refine ⟨u, y, h.u3, h.y3, fun he => h.ne1 ?_, hU.to_le (closure_mono ?_)⟩
    · rw [← h.c1, ← he]
      group
    · intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
      rcases ha with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr rfl))
  refine dichThreeLieAt_of_pair_derived hpair hU ?_
  have hmu : u ∈ U := subset_closure (by simp)
  have hmv : v ∈ U := subset_closure (by simp)
  have hmy : y ∈ U := subset_closure (by simp)
  have hc₁ : ⁅u, y⁆ ∈ ⁅U, U⁆ := commutator_mem_commutator hmu hmy
  have hc₂ : ⁅v, y⁆ ∈ ⁅U, U⁆ := commutator_mem_commutator hmv hmy
  rw [h.comm_u] at hc₁
  rw [h.comm_v] at hc₂
  have g1 : (u * v⁻¹) ^ 3 = 1 := pow_three_mul_inv h.uv h.u3 h.v3
  have g2 : (v * w⁻¹) ^ 3 = 1 := pow_three_mul_inv h.vw h.v3 h.w3
  have n1 : (1 : G) ≠ u * v⁻¹ := fun he => h.ne1 (mul_inv_eq_one.1 he.symm)
  have n2 : (1 : G) ≠ (u * v⁻¹) ^ 2 := by
    intro he
    apply n1
    calc (1 : G) = (u * v⁻¹) ^ 3 * ((u * v⁻¹) ^ 2)⁻¹ := by rw [g1, ← he, inv_one, mul_one]
      _ = u * v⁻¹ := by group
  have n3 : (1 : G) ≠ v * w⁻¹ := fun he => h.ne2 (mul_inv_eq_one.1 he.symm)
  have n4 : u * v⁻¹ ≠ (u * v⁻¹) ^ 2 := by
    intro he
    rw [pow_two] at he
    have h2 : (u * v⁻¹) * (u * v⁻¹) = (u * v⁻¹) * 1 := by rw [mul_one]; exact he.symm
    exact n1 (mul_left_cancel h2).symm
  refine not_isCyclic_of_four_cubes (H := ↥⁅U, U⁆) (a := 1) (b := ⟨u * v⁻¹, hc₁⟩)
    (c := ⟨u * v⁻¹, hc₁⟩ ^ 2) (d := ⟨v * w⁻¹, hc₂⟩) (one_pow 3) (Subtype.ext g1) ?_
    (Subtype.ext g2) ?_ ?_ ?_ ?_ ?_ ?_
  · apply Subtype.ext
    rw [← pow_mul, Subgroup.coe_pow]
    show (u * v⁻¹) ^ (2 * 3) = 1
    rw [pow_mul', g1, one_pow]
  · exact fun he => n1 (congrArg Subtype.val he)
  · exact fun he => n2 (by simpa using congrArg Subtype.val he)
  · exact fun he => n3 (congrArg Subtype.val he)
  · exact fun he => n4 (by simpa using congrArg Subtype.val he)
  · exact fun he => h.ne3 (congrArg Subtype.val he)
  · exact fun he => h.ne4 (by simpa using congrArg Subtype.val he)

theorem dichThreeLieAt_of_threeLocal (h : ThreeLocal G) : DichThreeLieAt G := by
  rcases h with h | h
  · exact ⟨Or.inl h, Or.inl (SylowDichotomyAt.of_sylow_comm h)⟩
  · exact dichThreeLieAt_of_cycleWitness h

theorem mem_of_pow_three_of_not_dvd_index (N : Subgroup G) [N.Normal] (hN : ¬ 3 ∣ N.index)
    {x : G} (hx : x ^ 3 = 1) : x ∈ N := by
  have h1 : (QuotientGroup.mk x : G ⧸ N) ^ 3 = 1 := by rw [← QuotientGroup.mk_pow, hx]; rfl
  have h2 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1)
    (orderOf_dvd_natCard (QuotientGroup.mk x : G ⧸ N))
  have hcop : Nat.Coprime 3 (Nat.card (G ⧸ N)) := by
    rw [← Subgroup.index]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN
  rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one, orderOf_eq_one_iff] at h2
  exact (QuotientGroup.eq_one_iff x).1 h2

theorem CycleWitness.of_normal_coprime_index (N : Subgroup G) [N.Normal] (hN : ¬ 3 ∣ N.index)
    (hw : CycleWitness G) : CycleWitness N := by
  obtain ⟨u, v, w, y, h⟩ := hw
  have hu := mem_of_pow_three_of_not_dvd_index N hN h.u3
  have hv := mem_of_pow_three_of_not_dvd_index N hN h.v3
  have hw' := mem_of_pow_three_of_not_dvd_index N hN h.w3
  have hy := mem_of_pow_three_of_not_dvd_index N hN h.y3
  refine ⟨⟨u, hu⟩, ⟨v, hv⟩, ⟨w, hw'⟩, ⟨y, hy⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  all_goals first
    | exact Subtype.ext (by simpa using h.uv) | exact Subtype.ext (by simpa using h.uw)
    | exact Subtype.ext (by simpa using h.vw) | exact Subtype.ext (by simpa using h.u3)
    | exact Subtype.ext (by simpa using h.v3) | exact Subtype.ext (by simpa using h.w3)
    | exact Subtype.ext (by simpa using h.y3) | exact Subtype.ext (by simpa using h.c1)
    | exact Subtype.ext (by simpa using h.c2) | exact Subtype.ext (by simpa using h.c3)
    | exact fun he => h.ne1 (by simpa using congrArg Subtype.val he)
    | exact fun he => h.ne2 (by simpa using congrArg Subtype.val he)
    | exact fun he => h.ne3 (by simpa using congrArg Subtype.val he)
    | exact fun he => h.ne4 (by simpa using congrArg Subtype.val he)

theorem CycleWitness.of_surjective_coprime_ker {H : Type} [Group H] (π : G →* H)
    (hker : ¬ 3 ∣ Nat.card π.ker) (hw : CycleWitness G) : CycleWitness H := by
  obtain ⟨u, v, w, y, h⟩ := hw
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨_, _, _, _, h.map_of_injOn π ?_⟩
  intro a ha b hb hab
  have hU := h.isPGroup
  set U : Subgroup G := closure ({u, v, w, y} : Set G)
  have hm : a * b⁻¹ ∈ U ⊓ π.ker := by
    refine Subgroup.mem_inf.2 ⟨U.mul_mem ha (U.inv_mem hb), ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
  have hp : IsPGroup 3 ↥(U ⊓ π.ker) := hU.to_le inf_le_left
  have hdvd : Nat.card ↥(U ⊓ π.ker) ∣ Nat.card π.ker := Subgroup.card_dvd_of_le inf_le_right
  have hbot : U ⊓ π.ker = ⊥ := by
    by_contra hne
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne ((Subgroup.card_eq_one).1 (by simpa using hk))
    exact hker ((hk ▸ dvd_pow_self 3 hk0 : 3 ∣ Nat.card ↥(U ⊓ π.ker)).trans hdvd)
  rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hm
  exact hm

theorem ThreeLocal.of_mulEquiv {H : Type} [Group H] [Finite H] (e : G ≃* H) (h : ThreeLocal H) :
    ThreeLocal G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases h with h | h
  · refine Or.inl fun S => ?_
    have hcard : Nat.card (S.map e.toMonoidHom) = 3 ^ (Nat.card H).factorization 3 := by
      rw [Subgroup.card_map_of_injective e.injective, S.card_eq_multiplicity,
        Nat.card_congr e.toEquiv]
    let P' : Sylow 3 H := Sylow.ofCard (S.map e.toMonoidHom) hcard
    have hP' : (P' : Subgroup H) = (S : Subgroup G).map e.toMonoidHom := Sylow.coe_ofCard _ _
    have := h P'
    rw [hP'] at this
    exact (isMulCommutative_map_iff_of_injective _ e.injective _).1 this
  · exact Or.inr (h.map e.symm.toMonoidHom e.symm.injective)

theorem ThreeLocal.of_normal_coprime_index (N : Subgroup G) [N.Normal] (hN : ¬ 3 ∣ N.index)
    (h : ThreeLocal G) : ThreeLocal N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases h with h | h
  · exact Or.inl (sylow_comm_of_subgroup N h)
  · exact Or.inr (h.of_normal_coprime_index N hN)

theorem ThreeLocal.of_surjective_coprime_ker {H : Type} [Group H] [Finite H] (π : G →* H)
    (hπ : Function.Surjective π) (hker : ¬ 3 ∣ Nat.card π.ker) (h : ThreeLocal G) :
    ThreeLocal H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases h with h | h
  · exact Or.inl (sylow_comm_of_surjective π hπ h)
  · exact Or.inr (h.of_surjective_coprime_ker π hker)

end Finite

section Wreath

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {D : Type} [Group D]

@[expose] def wbase (D : Type) [Group D] :
    (Multiplicative (ZMod 3) → D) →* D ≀ᵣ Multiplicative (ZMod 3) where
  toFun f := ⟨f, (1 : Multiplicative (ZMod 3))⟩
  map_one' := rfl
  map_mul' f g := by
    apply RegularWreathProduct.ext
    · rw [RegularWreathProduct.mul_left]
      funext x
      dsimp only
      rw [Pi.mul_apply, Pi.mul_apply, inv_one, one_mul]
    · rw [RegularWreathProduct.mul_right, mul_one]

theorem wbase_injective (D : Type) [Group D] : Function.Injective (wbase D) :=
  fun _ _ h => congrArg RegularWreathProduct.left h

@[simp] theorem wbase_left (f : Multiplicative (ZMod 3) → D) : (wbase D f).left = f := rfl

@[simp] theorem wbase_right (f : Multiplicative (ZMod 3) → D) : (wbase D f).right = 1 := rfl

private theorem c3_rels :
    Multiplicative.ofAdd (0 : ZMod 3) ≠ Multiplicative.ofAdd 1 ∧
      Multiplicative.ofAdd (0 : ZMod 3) ≠ Multiplicative.ofAdd 2 ∧
      Multiplicative.ofAdd (1 : ZMod 3) ≠ Multiplicative.ofAdd 2 ∧
      Multiplicative.ofAdd (1 : ZMod 3) * Multiplicative.ofAdd 0 = Multiplicative.ofAdd 1 ∧
      Multiplicative.ofAdd (1 : ZMod 3) * Multiplicative.ofAdd 1 = Multiplicative.ofAdd 2 ∧
      Multiplicative.ofAdd (1 : ZMod 3) * Multiplicative.ofAdd 2 = Multiplicative.ofAdd 0 ∧
      Multiplicative.ofAdd (1 : ZMod 3) ^ 3 = 1 := by
  decide

private theorem inl_conj_wbase (q x : Multiplicative (ZMod 3)) (g : D) :
    RegularWreathProduct.inl q * wbase D (Pi.mulSingle x g) * (RegularWreathProduct.inl q)⁻¹ =
      wbase D (Pi.mulSingle (q * x) g) := by
  ext i
  · simp only [RegularWreathProduct.mul_left, RegularWreathProduct.inv_left,
      RegularWreathProduct.left_inl, RegularWreathProduct.right_inl,
      RegularWreathProduct.mul_right, wbase_left, wbase_right, Pi.one_apply, one_mul, mul_one,
      Pi.mul_apply, inv_one]
    by_cases h : i = q * x
    · subst h
      simp
    · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne]
      intro h'
      apply h
      rw [← h']
      group
  · simp

theorem cycleWitness_wreath [Finite D] (hdvd : 3 ∣ Nat.card D) :
    CycleWitness (D ≀ᵣ Multiplicative (ZMod 3)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := fun h => by rw [h, orderOf_one] at hg; omega
  have hg2 : g ^ 2 ≠ 1 := by
    intro h
    apply hg1
    calc g = g ^ 3 * (g ^ 2)⁻¹ := by group
      _ = 1 := by rw [hg3, h, inv_one, mul_one]
  obtain ⟨h01, h02, h12, e0, e1, e2, e3⟩ := c3_rels
  have hcomm : ∀ (a b : Multiplicative (ZMod 3)), a ≠ b →
      wbase D (Pi.mulSingle a g) * wbase D (Pi.mulSingle b g) =
        wbase D (Pi.mulSingle b g) * wbase D (Pi.mulSingle a g) := by
    intro a b hab
    rw [← map_mul, ← map_mul]
    congr 1
    exact (Pi.mulSingle_commute (f := fun _ => D) hab g g).eq
  have hpow : ∀ a : Multiplicative (ZMod 3), (wbase D (Pi.mulSingle a g)) ^ 3 = 1 := by
    intro a
    rw [← map_pow, ← Pi.mulSingle_pow, hg3, Pi.mulSingle_one, map_one]
  have ht3 : (RegularWreathProduct.inl (Multiplicative.ofAdd (1 : ZMod 3)) :
      D ≀ᵣ Multiplicative (ZMod 3)) ^ 3 = 1 := by
    rw [← map_pow, e3, map_one]
  refine ⟨wbase D (Pi.mulSingle (Multiplicative.ofAdd 0) g),
    wbase D (Pi.mulSingle (Multiplicative.ofAdd 1) g),
    wbase D (Pi.mulSingle (Multiplicative.ofAdd 2) g),
    RegularWreathProduct.inl (Multiplicative.ofAdd (1 : ZMod 3)), hcomm _ _ h01, hcomm _ _ h02,
    hcomm _ _ h12, hpow _, hpow _, hpow _, ht3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [inl_conj_wbase, e0]
  · rw [inl_conj_wbase, e1]
  · rw [inl_conj_wbase, e2]
  · intro h
    have := congrFun (wbase_injective D h) (Multiplicative.ofAdd 0)
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h01] at this
    exact hg1 this
  · intro h
    have := congrFun (wbase_injective D h) (Multiplicative.ofAdd 1)
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h12] at this
    exact hg1 this
  · intro h
    rw [← map_inv, ← map_mul, ← map_inv, ← map_mul] at h
    have := congrFun (wbase_injective D h) (Multiplicative.ofAdd 0)
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h01,
      Pi.mulSingle_eq_of_ne h02, inv_one, mul_one] at this
    exact hg1 this
  · intro h
    rw [← map_inv, ← map_mul, ← map_pow, ← map_inv, ← map_mul] at h
    have := congrFun (wbase_injective D h) (Multiplicative.ofAdd 0)
    simp only [Pi.pow_apply, Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_of_ne h01, Pi.mulSingle_eq_of_ne h02, inv_one, mul_one] at this
    exact hg2 this

end Wreath

theorem threeLocal_of_sigma {G : Type} [Group G] [Finite G] {e a N : ℕ} (ha : 1 ≤ a)
    (h : ∀ P : Sylow 3 G, Nonempty (P ≃* sigmaModel 3 e a N)) : ThreeLocal G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hm : N / e < 3
  · exact Or.inl (sylow_isMulCommutative_of_sigmaModel_of_lt Nat.prime_three hm h)
  push Not at hm
  refine Or.inr ?_
  have hL : 1 < (Nat.digits 3 (N / e)).length := by
    rw [Nat.lt_digits_length_iff (by norm_num)]
    simpa using hm
  have hne : N / e ≠ 0 := by omega
  set i₁ : Fin (Nat.digits 3 (N / e)).length := ⟨(Nat.digits 3 (N / e)).length - 1, by omega⟩
  have hi₁ : 1 ≤ (i₁ : ℕ) := by
    show 1 ≤ (Nat.digits 3 (N / e)).length - 1
    omega
  have hpos : 0 < (Nat.digits 3 (N / e))[i₁] := by
    have hlast := Nat.getLast_digit_ne_zero 3 hne
    have heq : (Nat.digits 3 (N / e))[i₁] =
        (Nat.digits 3 (N / e)).getLast (Nat.digits_ne_nil_iff_ne_zero.mpr hne) := by
      rw [List.getLast_eq_getElem]
      rfl
    rw [heq]
    exact Nat.pos_of_ne_zero hlast
  set j₁ : Fin (Nat.digits 3 (N / e))[i₁] := ⟨0, hpos⟩
  have hW : CycleWitness (wreathTower 3 (Multiplicative (ZMod (3 ^ a))) i₁) := by
    obtain ⟨n', hn'⟩ : ∃ n', (i₁ : ℕ) = n' + 1 := ⟨(i₁ : ℕ) - 1, by omega⟩
    haveI : NeZero (3 ^ a) := ⟨pow_ne_zero a (by norm_num)⟩
    have hC : Nat.card (Multiplicative (ZMod (3 ^ a))) = 3 ^ a := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    have hD := card_wreathTower 3 (Multiplicative (ZMod (3 ^ a))) hC n'
    have hdvd : 3 ∣ Nat.card (wreathTower 3 (Multiplicative (ZMod (3 ^ a))) n') := by
      rw [hD]
      exact dvd_pow_self 3 (by have := SigmaDich.towerExp_pos (p := 3) ha n'; omega)
    rw [hn']
    exact cycleWitness_wreath (D := wreathTower 3 (Multiplicative (ZMod (3 ^ a))) n') hdvd
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 G))
  obtain ⟨φ⟩ := h S
  let Ψ : wreathTower 3 (Multiplicative (ZMod (3 ^ a))) i₁ →* G :=
    (S : Subgroup G).subtype.comp (φ.symm.toMonoidHom.comp (SigmaDich.sigmaEmbed 3 e a N i₁ j₁))
  have hΨ : Function.Injective Ψ :=
    Subtype.coe_injective.comp
      (φ.symm.injective.comp (SigmaDich.sigmaEmbed_injective 3 e a N i₁ j₁))
  exact hW.map Ψ hΨ

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
