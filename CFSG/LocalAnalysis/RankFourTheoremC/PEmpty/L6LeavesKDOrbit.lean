module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDInputs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD

variable {G : Type} [Group G]

@[expose] def conjPow (z : G) (i : ℕ) (L : Subgroup G) : Subgroup G :=
  L.map (MulAut.conj (z ^ i)).toMonoidHom

@[expose] def diagProd (z a : G) (n : ℕ) : G :=
  ((List.range n).map (fun i => z ^ i * a * (z ^ i)⁻¹)).prod

@[expose] def shiftProd (z a : G) (n : ℕ) : G :=
  ((List.range n).map (fun i => z ^ (i + 1) * a * (z ^ (i + 1))⁻¹)).prod

theorem diagProd_zero (z a : G) : diagProd z a 0 = 1 := by
  simp [diagProd]

theorem shiftProd_zero (z a : G) : shiftProd z a 0 = 1 := by
  simp [shiftProd]

theorem diagProd_succ (z a : G) (n : ℕ) :
    diagProd z a (n + 1) = diagProd z a n * (z ^ n * a * (z ^ n)⁻¹) := by
  simp [diagProd, List.range_succ]

theorem shiftProd_succ (z a : G) (n : ℕ) :
    shiftProd z a (n + 1) = shiftProd z a n * (z ^ (n + 1) * a * (z ^ (n + 1))⁻¹) := by
  simp [shiftProd, List.range_succ]

theorem conj_diagProd (z a : G) (n : ℕ) :
    z * diagProd z a n * z⁻¹ = shiftProd z a n := by
  induction n with
  | zero => simp [diagProd_zero, shiftProd_zero]
  | succ n ih =>
    have hf : z * (z ^ n * a * (z ^ n)⁻¹) * z⁻¹ = z ^ (n + 1) * a * (z ^ (n + 1))⁻¹ := by
      rw [pow_succ']
      group
    rw [diagProd_succ, shiftProd_succ, ← ih, ← hf]
    group

theorem diagProd_cons (z a : G) (n : ℕ) :
    diagProd z a (n + 1) = a * shiftProd z a n := by
  induction n with
  | zero => simp [diagProd_succ, diagProd_zero, shiftProd_zero]
  | succ n ih =>
    rw [diagProd_succ, ih, shiftProd_succ, mul_assoc]

theorem commute_list_prod {x : G} {l : List G} (h : ∀ y ∈ l, x * y = y * x) :
    x * l.prod = l.prod * x := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : x * a = a * x := h a (List.mem_cons_self)
    have ht : x * t.prod = t.prod * x :=
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.prod_cons]
    rw [← mul_assoc, ha, mul_assoc, ht, mul_assoc]

theorem le_of_orbit_length_p (z : G) (p : ℕ) (hp : 0 < p) (hzp : z ^ p = 1)
    (L : Subgroup G) (hL : IsSimpleGroup ↥L) (M T J₀ : Subgroup G)
    (hJ0 : ∀ i : ℕ, i < p → conjPow z i L ≤ J₀)
    (hcomm : ∀ i : ℕ, 0 < i → i < p → ∀ x ∈ L, ∀ y ∈ conjPow z i L, x * y = y * x)
    (hC : ∀ g ∈ J₀, z * g = g * z → g ∈ M) (hT : T ≤ M) (hTL : T ⊓ L ≠ ⊥) : L ≤ M := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.sub_add_cancel (Nat.succ_le_of_lt hp)).symm⟩
  have hmemC : ∀ a ∈ L, ∀ i : ℕ, z ^ i * a * (z ^ i)⁻¹ ∈ conjPow z i L := fun a ha i =>
    Subgroup.mem_map.mpr ⟨a, ha, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have hS : ∀ a ∈ L, ∀ x ∈ L, x * shiftProd z a q = shiftProd z a q * x := by
    intro a ha x hx
    unfold shiftProd
    apply commute_list_prod
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    have hiq : i < q := List.mem_range.mp hi
    exact hcomm (i + 1) (Nat.succ_pos i) (by omega) x hx _ (hmemC a ha (i + 1))
  have hd : ∀ a ∈ L, z * diagProd z a (q + 1) = diagProd z a (q + 1) * z := by
    intro a ha
    have h1 := conj_diagProd z a (q + 1)
    have h2 : shiftProd z a (q + 1) = shiftProd z a q * a := by
      rw [shiftProd_succ, hzp]
      simp
    have h3 : diagProd z a (q + 1) = a * shiftProd z a q := diagProd_cons z a q
    have h4 : shiftProd z a q * a = a * shiftProd z a q := (hS a ha a ha).symm
    rw [h2, h3, h4] at h1
    rw [h3]
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hdx : ∀ a ∈ L, ∀ x ∈ L,
      diagProd z a (q + 1) * x * (diagProd z a (q + 1))⁻¹ = a * x * a⁻¹ := by
    intro a ha x hx
    have h4 : shiftProd z a q * x = x * shiftProd z a q := (hS a ha x hx).symm
    rw [diagProd_cons, mul_inv_rev]
    calc a * shiftProd z a q * x * ((shiftProd z a q)⁻¹ * a⁻¹)
        = a * (shiftProd z a q * x) * (shiftProd z a q)⁻¹ * a⁻¹ := by group
      _ = a * (x * shiftProd z a q) * (shiftProd z a q)⁻¹ * a⁻¹ := by rw [h4]
      _ = a * x * a⁻¹ := by group
  have hdJ : ∀ a ∈ L, diagProd z a (q + 1) ∈ J₀ := by
    intro a ha
    unfold diagProd
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hJ0 i (List.mem_range.mp hi) (hmemC a ha i)
  have hdM : ∀ a ∈ L, diagProd z a (q + 1) ∈ M := fun a ha => hC _ (hdJ a ha) (hd a ha)
  obtain ⟨S₀, hS₀def⟩ : ∃ S : Set G,
      S = {g | ∃ a ∈ L, ∃ y ∈ T ⊓ L, g = a * y * a⁻¹} := ⟨_, rfl⟩
  have memS₀ : ∀ g, g ∈ S₀ ↔ ∃ a ∈ L, ∃ y ∈ T ⊓ L, g = a * y * a⁻¹ := by
    intro g
    rw [hS₀def]
    rfl
  have hS₀M : ∀ g ∈ S₀, g ∈ M := by
    intro g hg
    obtain ⟨a, ha, y, hy, rfl⟩ := (memS₀ g).mp hg
    rw [← hdx a ha y (Subgroup.mem_inf.mp hy).2]
    exact M.mul_mem (M.mul_mem (hdM a ha) (hT (Subgroup.mem_inf.mp hy).1))
      (M.inv_mem (hdM a ha))
  have hS₀conj : ∀ b ∈ L, ∀ g ∈ S₀, b * g * b⁻¹ ∈ S₀ := by
    intro b hb g hg
    obtain ⟨a, ha, y, hy, rfl⟩ := (memS₀ g).mp hg
    refine (memS₀ _).mpr ⟨b * a, L.mul_mem hb ha, y, hy, ?_⟩
    group
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup G, N = Subgroup.closure S₀ := ⟨_, rfl⟩
  have hNM : N ≤ M := by
    rw [hNdef]
    exact (Subgroup.closure_le _).mpr fun g hg => hS₀M g hg
  have hNconj : ∀ b ∈ L, ∀ n ∈ N, b * n * b⁻¹ ∈ N := by
    intro b hb n hn
    have hmap : N.map (MulAut.conj b).toMonoidHom ≤ N := by
      rw [hNdef, _root_.MonoidHom.map_closure]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨g, hg, rfl⟩
      exact Subgroup.subset_closure (hS₀conj b hb g hg)
    have := hmap (Subgroup.mem_map_of_mem _ hn)
    simpa [MulAut.conj_apply] using this
  haveI hNn : (N.subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hNconj (g : G) g.2 (n : G) hn
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this
  obtain ⟨y₀, hy₀, hy₀1⟩ : ∃ y ∈ T ⊓ L, y ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hTL ((Subgroup.eq_bot_iff_forall _).mpr fun y hy => hcon y hy)
  have hy₀N : y₀ ∈ N := by
    rw [hNdef]
    apply Subgroup.subset_closure
    rw [memS₀]
    exact ⟨1, L.one_mem, y₀, hy₀, by simp⟩
  rcases hL.eq_bot_or_eq_top_of_normal (N.subgroupOf L) with hbot | htop
  · exfalso
    have hmem : (⟨y₀, (Subgroup.mem_inf.mp hy₀).2⟩ : L) ∈ N.subgroupOf L :=
      Subgroup.mem_subgroupOf.mpr hy₀N
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hy₀1 (congrArg Subtype.val hmem)
  · intro x hx
    have hmem : (⟨x, hx⟩ : L) ∈ N.subgroupOf L := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hNM (Subgroup.mem_subgroupOf.mp hmem)

@[expose] def conjAutOf (z : G) (L : Subgroup G) (hLz : ∀ g : G, g ∈ L ↔ z * g * z⁻¹ ∈ L) :
    MulAut ↥L where
  toFun g := ⟨z * (g : G) * z⁻¹, (hLz _).mp g.2⟩
  invFun g := ⟨z⁻¹ * (g : G) * z, (hLz _).mpr (by
    have h : z * (z⁻¹ * (g : G) * z) * z⁻¹ = g := by group
    rw [h]
    exact g.2)⟩
  left_inv g := Subtype.ext (by
    show z⁻¹ * (z * (g : G) * z⁻¹) * z = g
    group)
  right_inv g := Subtype.ext (by
    show z * (z⁻¹ * (g : G) * z) * z⁻¹ = g
    group)
  map_mul' g h := Subtype.ext (by
    show z * ((g : G) * (h : G)) * z⁻¹ = (z * (g : G) * z⁻¹) * (z * (h : G) * z⁻¹)
    group)

theorem conjAutOf_pow (z : G) (L : Subgroup G) (hLz : ∀ g : G, g ∈ L ↔ z * g * z⁻¹ ∈ L)
    (n : ℕ) (g : ↥L) : ((conjAutOf z L hLz ^ n) g : G) = z ^ n * (g : G) * (z ^ n)⁻¹ := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih]
    show z ^ n * (z * (g : G) * z⁻¹) * (z ^ n)⁻¹ = z ^ (n + 1) * (g : G) * (z ^ (n + 1))⁻¹
    rw [pow_succ']
    group

theorem conjAutOf_pow_eq_one (z : G) (p : ℕ) (hzp : z ^ p = 1) (L : Subgroup G)
    (hLz : ∀ g : G, g ∈ L ↔ z * g * z⁻¹ ∈ L) : conjAutOf z L hLz ^ p = 1 := by
  ext g
  rw [conjAutOf_pow, hzp]
  simp

theorem conjAutOf_ne_one (z : G) (L : Subgroup G) (hLz : ∀ g : G, g ∈ L ↔ z * g * z⁻¹ ∈ L)
    (g₀ : G) (hg₀ : g₀ ∈ L) (hg₀z : z * g₀ ≠ g₀ * z) : conjAutOf z L hLz ≠ 1 := by
  intro h1
  have h2 : z * g₀ * z⁻¹ = g₀ := by
    have h3 := congrArg (fun φ : MulAut ↥L => ((φ ⟨g₀, hg₀⟩ : ↥L) : G)) h1
    exact h3
  exact hg₀z (mul_inv_eq_iff_eq_mul.mp h2)

theorem normalizer_map_mem {L : Subgroup G} {U : Subgroup ↥L} {x : ↥L}
    (hx : x ∈ Subgroup.normalizer (U : Set ↥L)) :
    (x : G) ∈ Subgroup.normalizer ((U.map L.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro h
  constructor
  · intro hh
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨x * u * x⁻¹, (hx u).mp hu, ?_⟩
    simp
  · intro hh
    obtain ⟨k, hk, hkeq⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨x⁻¹ * k * x, ?_, ?_⟩
    · apply (hx _).mpr
      have h' : x * (x⁻¹ * k * x) * x⁻¹ = k := by group
      rw [h']
      exact hk
    · have hk' : ((k : ↥L) : G) = (x : G) * h * (x : G)⁻¹ := hkeq
      show (x : G)⁻¹ * ((k : ↥L) : G) * (x : G) = h
      rw [hk']
      group

theorem le_of_orbit_length_one [Finite G] (z : G) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hzp : z ^ p = 1) (L : Subgroup G) (hLz : ∀ g : G, g ∈ L ↔ z * g * z⁻¹ ∈ L)
    (hsimp : IsSimpleGroup ↥L) (hnab : ¬ ∀ a b : ↥L, a * b = b * a)
    (hK : CFSG.Open.IsKGroup ↥L) (hpL : ¬ p ∣ Nat.card ↥L)
    (T : Subgroup G) (hTL : CFSG.ABGLocalTools.IsSylowOf 2 T L)
    (hTz : ∀ g ∈ T, z * g * z⁻¹ ∈ T) (M : Subgroup G)
    (hC : ∀ g ∈ L, z * g = g * z → g ∈ M)
    (hN1 : ∀ U : Subgroup G, U ≤ T → U ≠ ⊥ → (∀ g ∈ U, z * g * z⁻¹ ∈ U) →
      Subgroup.normalizer (U : Set G) ⊓ L ≤ M)
    (hN3 : ∀ U : Subgroup G, U ≤ L → IsPGroup 2 U → U ≠ ⊥ → (∀ g ∈ U, z * g = g * z) →
      Subgroup.normalizer (U : Set G) ⊓ L ≤ M)
    (hEven : KFactFieldAutEven) (hOdd : KFactFieldAutOdd) : L ≤ M := by
  by_cases hcent : ∀ g ∈ L, z * g = g * z
  · intro x hx
    exact hC x hx (hcent x hx)
  obtain ⟨g₀, hg₀, hg₀z⟩ : ∃ g ∈ L, z * g ≠ g * z := by
    by_contra h
    push_neg at h
    exact hcent h
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hαord : orderOf (conjAutOf z L hLz) = p :=
    orderOf_eq_prime (conjAutOf_pow_eq_one z p hzp L hLz)
      (conjAutOf_ne_one z L hLz g₀ hg₀ hg₀z)
  have key : (⊤ : Subgroup ↥L) ≤ M.subgroupOf L := by
    by_cases hodd : ∃ U : Subgroup ↥L, CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ ∧
        ∀ g ∈ U, conjAutOf z L hLz g = g
    ·
      obtain ⟨U, hU, hUc⟩ := hodd
      have hgen := hOdd ↥L p (conjAutOf z L hLz) U hp hp5 hαord hpL hsimp hnab hK hU hUc
      rw [← hgen]
      apply (Subgroup.closure_le _).mpr
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨U₀, ⟨hU₀U, hU₀⟩, hxN⟩ := hx
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      have hU2 : IsPGroup 2 ↥U := hU.isPGroup
      have hU₀2 : IsPGroup 2 ↥U₀ := hU2.to_le hU₀U
      have hU₀'2 : IsPGroup 2 ↥(U₀.map L.subtype) := hU₀2.map L.subtype
      have hle : U₀.map L.subtype ≤ L := Subgroup.map_subtype_le U₀
      have hne : U₀.map L.subtype ≠ ⊥ := by
        intro hbot
        apply hU₀
        rw [Subgroup.eq_bot_iff_forall]
        intro u hu
        have hmem : (u : G) ∈ U₀.map L.subtype := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        exact Subtype.ext hmem
      have hcent : ∀ g ∈ U₀.map L.subtype, z * g = g * z := by
        intro g hg
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hg
        have h1 : conjAutOf z L hLz u = u := hUc u (hU₀U hu)
        have h2 : z * (u : G) * z⁻¹ = (u : G) := congrArg Subtype.val h1
        exact mul_inv_eq_iff_eq_mul.mp h2
      exact hN3 (U₀.map L.subtype) hle hU₀'2 hne hcent
        (Subgroup.mem_inf.mpr ⟨normalizer_map_mem hxN, x.2⟩)
    ·
      have hT' : CFSG.ABGLocalTools.IsSylowOf 2 (T.subgroupOf L) ⊤ := by
        apply (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff L).mp
        have htop : (⊤ : Subgroup ↥L).map L.subtype = L := by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
        rw [Subgroup.subgroupOf_map_subtype, htop, inf_eq_left.mpr hTL.le]
        exact hTL
      have hgen := hEven ↥L p (conjAutOf z L hLz) (T.subgroupOf L) hp hp5 hαord hpL hsimp
        hnab hK hT' hodd
      have hTM : T ≤ M := by
        by_cases hT0 : T = ⊥
        · rw [hT0]
          exact bot_le
        · intro t ht
          exact (hN1 T le_rfl hT0 hTz)
            (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer ht, hTL.le ht⟩)
      rw [← hgen]
      apply (Subgroup.closure_le _).mpr
      rintro x (hx | hx)
      · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        apply hC x.1 x.2
        have h2 : z * (x : G) * z⁻¹ = (x : G) := congrArg Subtype.val hx
        exact mul_inv_eq_iff_eq_mul.mp h2
      · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        exact hTM (Subgroup.mem_subgroupOf.mp hx)
  intro x hx
  exact Subgroup.mem_subgroupOf.mp (key (Subgroup.mem_top (⟨x, hx⟩ : ↥L)))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD
