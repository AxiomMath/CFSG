module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.ModelTorusBraces

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair pairedTorusHom f4i nTwo nFour kTwo kFour)

section Basic

variable {K : Type} [Field K] {a : ℕ}

theorem torusH_mul_comm {x y : ModGL F4.tag K} (hx : x ∈ torusH K a) (hy : y ∈ torusH K a) :
    x * y = y * x := by
  obtain ⟨t, rfl⟩ := hx
  obtain ⟨t', rfl⟩ := hy
  rw [← map_mul, ← map_mul, mul_comm]

theorem torusH_le_centralizer_torusHi (i : Idx) :
    torusH K a ≤ Subgroup.centralizer (torusHi K a i : Set (ModGL F4.tag K)) :=
  fun _ hx => Subgroup.mem_centralizer_iff.2 fun _ hy => torusH_mul_comm (torusHi_le_torusH i hy) hx

theorem rootV_le_centralizer_torusHi (i : Idx) :
    rootV K a i ≤ Subgroup.centralizer (torusHi K a i : Set (ModGL F4.tag K)) :=
  fun _ hv => Subgroup.mem_centralizer_iff.2 fun _ hh =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hh).2 _ hv).symm

theorem nTwo_zero_nFour_zero : nTwo K 0 = 1 ∧ nFour K 0 = 1 := by
  have h : F4.fixedRelElt (⟨0, by decide⟩ : Fin F4.fixedWeylOrder) = 1 := rfl
  exact ⟨by rw [nTwo, show kTwo 0 = ⟨0, by decide⟩ from rfl, h, canonicalRep_one],
    by rw [nFour, show kFour 0 = ⟨0, by decide⟩ from rfl, h, canonicalRep_one]⟩

end Basic

section Blocks

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem reeFixedOrbitUnipotent_one_eq (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ = rootV K a .i1 := by
  refine le_antisymm (fun g hg => ?_) ?_
  · obtain ⟨c, d, rfl⟩ := exists_stdFourG_eq hK hg
    have e : stdFourG a c d = fourCoordG a 0 c d := by
      rw [fourCoordG, nTwo_zero_nFour_zero.2, one_mul, inv_one, mul_one]
    have h1 : rootElt K a .i1 c = fourCoordG a 0 c 0 := (rootElt_eq_coord .i1 c).1 rfl
    have h2 : rootElt K a .i2 d = fourCoordG a 0 0 d := (rootElt_eq_coord .i2 d).2.1 rfl
    rw [e, fourCoordG_eq_mul hK, ← h1, ← h2]
    exact mul_mem (rootElt_mem_rootV _ _) ((rootV_center_le hK .i1).1 (rootElt_mem_rootV _ _))
  · rw [rootV, Subgroup.closure_le]
    rintro _ ⟨u, rfl⟩
    exact sylowB_mem_U2 hK u 0

theorem reeFixedOrbitUnipotent_zero_eq (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ = rootV K a .i3 := by
  refine le_antisymm (fun g hg => ?_) ?_
  · obtain ⟨s, rfl⟩ := exists_stdTwoG_eq hK hg
    have e : stdTwoG a s = rootElt K a .i3 s := by
      have h3 : rootElt K a .i3 s = twoCoordG a 0 s := (rootElt_eq_coord .i3 s).2.2 rfl
      rw [h3, twoCoordG, nTwo_zero_nFour_zero.1, one_mul, inv_one, mul_one]
    rw [e]
    exact rootElt_mem_rootV _ _
  · rw [rootV, Subgroup.closure_le]
    rintro _ ⟨u, rfl⟩
    exact sylowA_mem_U1 hK u

end Blocks

section WeylGroup

variable (K : Type) [Field K] [CharP K F4.prime]

@[expose] def weylRepHom : WeylGroup F4.tag →* ModGL F4.tag K where
  toFun := canonicalRep (coxeterSystem F4.tag) K
  map_one' := canonicalRep_one _ _
  map_mul' w v := by
    have : CharP K 2 := ‹CharP K F4.prime›
    exact CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo w v

variable {K}

theorem weylRepHom_injective : Function.Injective (weylRepHom K) := by
  intro w v h
  have hw := weylQuotientHom_eq (g := ⟨_, canonicalRep_mem_monomialSubgroup K w⟩)
    (mapsRootLines_canonicalRep (R := K) w)
  have hv := weylQuotientHom_eq (g := ⟨_, canonicalRep_mem_monomialSubgroup K v⟩)
    (mapsRootLines_canonicalRep (R := K) v)
  have e : (⟨_, canonicalRep_mem_monomialSubgroup K w⟩ : monomialSubgroup F4.tag K) =
      ⟨_, canonicalRep_mem_monomialSubgroup K v⟩ := Subtype.ext h
  rw [← hw, ← hv, e]

theorem map_weylRepHom_relWeylRee :
    F4.relWeylRee.map (weylRepHom K) = Subgroup.closure {weylR K, weylS K} := by
  rw [relWeylRee_eq_closure, MonoidHom.map_closure, ← Set.range_comp]
  congr 1
  ext g
  simp only [Set.mem_range, Function.comp_apply, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro (rfl | rfl)
    · exact ⟨⟨1, by decide⟩, rfl⟩
    · exact ⟨⟨0, by decide⟩, rfl⟩

theorem orderOf_weylS_mul_weylR : orderOf (weylS K * weylR K) = 8 := by
  have e : weylS K * weylR K =
      weylRepHom K (F4.fixedOrbitElement ⟨0, by decide⟩ * F4.fixedOrbitElement ⟨1, by decide⟩) :=
    (map_mul (weylRepHom K) _ _).symm
  rw [e, orderOf_injective _ weylRepHom_injective, orderOf_F4_fixedOrbitElement_mul]

end WeylGroup

section Generation

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conj_mem {H : Subgroup G} {g : G} (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  refine fun x => ⟨h1 x, fun hx => ?_⟩
  have h := h2 _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h

theorem conj_mem_closure_of_forall_mem {S : Set G} {g : G}
    (h : ∀ x ∈ S, g * x * g⁻¹ ∈ Subgroup.closure S)
    {x : G} (hx : x ∈ Subgroup.closure S) : g * x * g⁻¹ ∈ Subgroup.closure S := by
  have hle : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj g).toMonoidHom :=
    (Subgroup.closure_le _).2 fun y hy => h y hy
  exact hle hx

theorem eq_closure_of_isSimpleGroup {N V T : Subgroup G} {n : G}
    (hN : N = Subgroup.closure ((V : Set G) ∪ T ∪ {n})) (hs : IsSimpleGroup N) (hV : V ≠ ⊥)
    (hn : n * n = 1) (hTV : ∀ t ∈ T, ∀ x ∈ V, t * x * t⁻¹ ∈ V)
    (hnT : ∀ t ∈ T, n * t * n⁻¹ = t⁻¹) :
    N = Subgroup.closure ((V : Set G) ∪ {n}) := by
  have hni : n⁻¹ = n := inv_eq_of_mul_eq_one_right hn
  have hVN : V ≤ N := by
    rw [hN]
    exact fun x hx => Subgroup.subset_closure (Or.inl (Or.inl hx))
  have hnN : n ∈ N := by
    rw [hN]
    exact Subgroup.subset_closure (Or.inr rfl)
  set M := Subgroup.closure ((V : Set G) ∪ (V.map (MulAut.conj n).toMonoidHom : Set G)) with hM
  have hVM : ∀ x ∈ V, x ∈ M := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hVnM : ∀ x ∈ V, n * x * n⁻¹ ∈ M := fun x hx => Subgroup.subset_closure (Or.inr ⟨x, hx, rfl⟩)
  have hMle : M ≤ Subgroup.closure ((V : Set G) ∪ {n}) := by
    rw [hM, Subgroup.closure_le]
    rintro _ (hx | ⟨x, hx, rfl⟩)
    · exact Subgroup.subset_closure (Or.inl hx)
    · have hn' : n ∈ Subgroup.closure ((V : Set G) ∪ {n}) := Subgroup.subset_closure (Or.inr rfl)
      exact mul_mem (mul_mem hn' (Subgroup.subset_closure (Or.inl hx))) (inv_mem hn')
  have hMN : M ≤ N := by
    rw [hM, Subgroup.closure_le]
    rintro _ (hx | ⟨x, hx, rfl⟩)
    · exact hVN hx
    · exact mul_mem (mul_mem hnN (hVN hx)) (inv_mem hnN)
  have hT : ∀ t ∈ T, ∀ x ∈ M, t * x * t⁻¹ ∈ M := by
    intro t ht x hx
    refine conj_mem_closure_of_forall_mem (fun y hy => ?_) hx
    rcases hy with hy | ⟨z, hz, rfl⟩
    · exact hVM _ (hTV t ht y hy)
    · have e : t * (MulAut.conj n).toMonoidHom z * t⁻¹ = n * (t⁻¹ * z * t⁻¹⁻¹) * n⁻¹ := by
        have h1 : n⁻¹ * t * n = t⁻¹ := by
          have h := hnT t ht
          rw [hni] at h ⊢
          exact h
        calc t * (MulAut.conj n).toMonoidHom z * t⁻¹ = t * (n * z * n⁻¹) * t⁻¹ := rfl
          _ = n * ((n⁻¹ * t * n) * z * (n⁻¹ * t * n)⁻¹) * n⁻¹ := by group
          _ = n * (t⁻¹ * z * t⁻¹⁻¹) * n⁻¹ := by rw [h1]
      rw [e]
      exact hVnM _ (hTV _ (inv_mem ht) z hz)
  have hnM : ∀ x ∈ M, n * x * n⁻¹ ∈ M := by
    intro x hx
    refine conj_mem_closure_of_forall_mem (fun y hy => ?_) hx
    rcases hy with hy | ⟨z, hz, rfl⟩
    · exact hVnM y hy
    · have e : n * (MulAut.conj n).toMonoidHom z * n⁻¹ = z := by
        change n * (n * z * n⁻¹) * n⁻¹ = z
        rw [hni, ← mul_assoc, ← mul_assoc, hn, one_mul, mul_assoc, hn, mul_one]
      rw [e]
      exact hVM z hz
  have hnorm : N ≤ Subgroup.normalizer (M : Set G) := by
    conv_lhs => rw [hN]
    rw [Subgroup.closure_le]
    rintro x ((hx | hx) | hx)
    · exact Subgroup.le_normalizer (hVM x hx)
    · exact mem_normalizer_of_conj_mem (hT x hx) (fun y hy => by
        simpa using hT _ (inv_mem hx) y hy)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact mem_normalizer_of_conj_mem hnM fun y hy => by
        have h := hnM y hy
        rw [hni] at h ⊢
        exact h
  have hnormal : (M.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff hMN).2 fun h k hh hk => by
      have := (Subgroup.mem_normalizer_iff.1 (hnorm hk) h).1 hh
      exact this
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hnormal with h | h
  · exfalso
    refine hV (eq_bot_iff.2 fun x hx => ?_)
    have hx' : (⟨x, hVN hx⟩ : N) ∈ M.subgroupOf N := Subgroup.mem_subgroupOf.2 (hVM x hx)
    rw [h, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hx')
  · refine le_antisymm (fun x hx => hMle ?_) ?_
    · have hx' : (⟨x, hx⟩ : N) ∈ M.subgroupOf N := by rw [h]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 hx'
    · rw [Subgroup.closure_le]
      rintro _ (hx | rfl)
      · exact hVN hx
      · exact hnN

end Generation

section RankOne

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem rootV_ne_bot (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : Idx) : rootV K a i ≠ ⊥ := by
  intro h
  have h1 := rootElt_mem_rootV (K := K) (a := a) i 1
  rw [h, Subgroup.mem_bot, ← rootElt_zero i] at h1
  exact one_ne_zero (rootElt_injective hK i h1)

theorem leviN_three_eq_closure (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    leviN K a .i3 = Subgroup.closure ((rootV K a .i3 : Set (ModGL F4.tag K)) ∪ {weylS K}) := by
  refine eq_closure_of_isSimpleGroup (T := rankOneTorusOne K a) ?_
    (isSimpleGroup_rankOneGroupOne ha hK).1 (rootV_ne_bot hK .i3) weylS_mul_self ?_ ?_
  · change rankOneGroupOne K a = _
    rw [rankOneGroupOne, reeFixedOrbitUnipotent_zero_eq hK]
  · rintro _ ⟨u, rfl⟩ x hx
    exact (Subgroup.mem_normalizer_iff.1 (torusH_le_normalizer_rootV hK .i3
      (pairedTorusHom_mem_torusH u).1) x).1 hx
  · rintro _ ⟨u, rfl⟩
    exact weylS_conj_torusOne hK u

end RankOne

theorem brace_ofCoord_ne_zero : ∀ (i : Idx) (n : Fin 12), i.isCenter = false → n ∉ i.coords →
    Idx.brace i (Idx.ofCoord n) ≠ 0 := by
  decide

section Fixed

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem torusPair_conj_sylowVec (hK : Nat.card K = 2 ^ (2 * a + 1)) (t : Kˣ × Kˣ)
    (x : Fin 12 → K) :
    torusPair a t * sylowVec a K x * (torusPair a t)⁻¹ =
      sylowVec a K (fun n => (rootChar K a (Idx.ofCoord n) t : K) * x n) := by
  have e : ∀ y, torusPair a t * y * (torusPair a t)⁻¹ = MulAut.conj (torusPair a t) y :=
    fun _ => rfl
  have hc : ∀ (j : Idx) (c : K), MulAut.conj (torusPair a t) (rootElt K a j c) =
      rootElt K a j ((rootChar K a j t : K) * c) := fun j c => by
    rw [← e, torusPair_conj_rootElt hK]
  rw [e, sylowVec_eq_prod_rootElt hK, sylowVec_eq_prod_rootElt hK]
  simp only [map_mul, hc]
  rfl

theorem sylowP_inf_centralizer_torusHi (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {i : Idx} (hi : i.isCenter = false) :
    F4.reeFixedPosUnipotent K a ⊓ Subgroup.centralizer (torusHi K a i : Set (ModGL F4.tag K)) =
      rootV K a i := by
  refine le_antisymm (fun g hg => ?_) (le_inf (rootV_le_sylowP hK i) fun v hv =>
    Subgroup.mem_centralizer_iff.2 fun h hh =>
      (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hh).2 v hv).symm)
  obtain ⟨hgP, hgc⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨x, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hgP
  have hfix : ∀ n, ∀ t : Kˣ × Kˣ, rootChar K a i t = 1 →
      (rootChar K a (Idx.ofCoord n) t : K) * x n = x n := by
    intro n t ht
    have hmem := (mem_torusHi_iff hK i t).2 ht
    have hcomm := Subgroup.mem_centralizer_iff.1 hgc _ hmem
    have h1 : torusPair a t * sylowVec a K x * (torusPair a t)⁻¹ = sylowVec a K x := by
      rw [hcomm, mul_inv_cancel_right]
    rw [torusPair_conj_sylowVec hK] at h1
    exact congrFun ((bijOn_sylowVec hK).2.1 (Set.mem_univ _) (Set.mem_univ _) h1) n
  have hx : ∀ n ∉ i.coords, x n = 0 := fun n hn =>
    eq_zero_of_forall_rootChar_mul_eq ha hK hi (brace_ofCoord_ne_zero i n hi hn) (hfix n)
  have hmem : sylowVec a K x ∈ (rootV K a i : Set (ModGL F4.tag K)) := by
    rw [coe_rootV hK]
    exact ⟨x, hx, rfl⟩
  exact hmem

end Fixed

section Exponents

variable {a : ℕ}

theorem intCast_eq_of_zpow_eq_of_orderOf {G : Type*} [Group G] {g : G}
    (hg : orderOf g = 2 ^ (2 * a + 1) - 1) {A B : ℤ} (h : g ^ A = g ^ B) :
    (A : ZMod (2 ^ (2 * a + 1) - 1)) = B := by
  have h1 : g ^ (A - B) = 1 := by rw [zpow_sub, h, mul_inv_cancel]
  have h2 := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [hg] at h2
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub A B _).2 (by
    rw [show B - A = -(A - B) by ring]
    exact dvd_neg.2 h2)

theorem zmod_two_pow_sub_one_ne_zero (ha : 1 ≤ a) :
    (1 : ZMod (2 ^ (2 * a + 1) - 1)) ≠ 0 ∧ (-1 : ZMod (2 ^ (2 * a + 1) - 1)) ≠ 0 ∧
      (-2 : ZMod (2 ^ (2 * a + 1) - 1)) ≠ 0 := by
  have h8 : 8 ≤ 2 ^ (2 * a + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : Fact (1 < 2 ^ (2 * a + 1) - 1) := ⟨by omega⟩
  have h1 : (1 : ZMod (2 ^ (2 * a + 1) - 1)) ≠ 0 := one_ne_zero
  refine ⟨h1, neg_ne_zero.2 h1, neg_ne_zero.2 ?_⟩
  exact (isUnit_two_zmod (n := 2 * a + 1)).ne_zero

end Exponents

@[expose] def expAct (θ : ℤ) (l : Fin F4.fixedOrbitCount) (p : ℤ × ℤ) : ℤ × ℤ :=
  if l.val = 0 then (-p.1 + p.2, p.2) else (p.1, (2 + 2 * θ) * p.1 - p.2)

@[expose] def expWord (θ : ℤ) (ω : List (Fin F4.fixedOrbitCount)) (p : ℤ × ℤ) : ℤ × ℤ :=
  ω.foldr (expAct θ) p

section WeylTorusAction

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem canonicalRep_conj_torusPair_zpow (hK : Nat.card K = 2 ^ (2 * a + 1))
    (l : Fin F4.fixedOrbitCount) (g : Kˣ) (p : ℤ × ℤ) :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement l) *
        torusPair a (g ^ p.1, g ^ p.2) *
          (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement l))⁻¹ =
      torusPair a (g ^ (expAct (2 ^ a) l p).1, g ^ (expAct (2 ^ a) l p).2) := by
  fin_cases l
  · have h := (weylS_conj_torusOne (K := K) hK (g ^ p.1))
    simp only [expAct, ↓reduceIte]
    rw [rankOneTorusPair_eq_mul, weyl_conj_mul, h, canonicalRep_conj_torusTwo hK,
      (rankOne_commute_pairedTorusHom (a := a) 1 2 0 3 _ _).eq, ← mul_assoc, ← map_inv, ← map_mul,
      rankOneTorusPair_eq_mul, zpow_add, zpow_neg]
  · have h := (weylR_conj_torusTwo (K := K) hK (g ^ p.2))
    simp only [expAct, one_ne_zero, ↓reduceIte]
    rw [rankOneTorusPair_eq_mul, weyl_conj_mul, h, canonicalRep_conj_torusOne hK, mul_assoc,
      ← map_inv, ← map_mul, rankOneTorusPair_eq_mul]
    congr 2
    rw [← zpow_mul, ← zpow_neg, ← zpow_add, sub_eq_add_neg, mul_comm]
    push_cast
    ring_nf

theorem weylRepHom_conj_torusPair_zpow (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ω : List (Fin F4.fixedOrbitCount)) (g : Kˣ) (p : ℤ × ℤ) :
    weylRepHom K (ω.map F4.fixedOrbitElement).prod * torusPair a (g ^ p.1, g ^ p.2) *
        (weylRepHom K (ω.map F4.fixedOrbitElement).prod)⁻¹ =
      torusPair a (g ^ (expWord (2 ^ a) ω p).1, g ^ (expWord (2 ^ a) ω p).2) := by
  induction ω with
  | nil => simp [expWord]
  | cons l ω ih =>
    rw [List.map_cons, List.prod_cons, map_mul]
    set n := weylRepHom K (F4.fixedOrbitElement l)
    set m := weylRepHom K (ω.map F4.fixedOrbitElement).prod
    rw [show n * m * torusPair a (g ^ p.1, g ^ p.2) * (n * m)⁻¹ =
        n * (m * torusPair a (g ^ p.1, g ^ p.2) * m⁻¹) * n⁻¹ by group, ih]
    exact canonicalRep_conj_torusPair_zpow hK l g _

theorem weylRepHom_eq_of_commute_torusHi_one (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (k : Fin F4.fixedWeylOrder)
    (hk : ∀ h ∈ torusHi K a .i1,
      weylRepHom K (F4.fixedRelElt k) * h = h * weylRepHom K (F4.fixedRelElt k)) :
    weylRepHom K (F4.fixedRelElt k) = 1 ∨ weylRepHom K (F4.fixedRelElt k) = weylR K := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = 2 ^ (2 * a + 1) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  obtain ⟨⟨e10, e11⟩, -⟩ := torusExp_leadRoot ((2 : ℤ) ^ a)
  have hmem : torusPair a (g ^ (2 * (2 : ℤ) ^ a - 1), g ^ ((2 : ℤ) ^ a)) ∈ torusHi K a .i1 := by
    rw [← range_torusHiHom hK]
    refine ⟨g, ?_⟩
    simp only [torusHiHom, torusHiParam, MonoidHom.comp_apply, MonoidHom.prod_apply,
      zpowGroupHom_apply, e10, e11, neg_neg]
  have hconj := hk _ hmem
  have h1 : weylRepHom K (F4.fixedRelElt k) *
      torusPair a (g ^ (2 * (2 : ℤ) ^ a - 1), g ^ ((2 : ℤ) ^ a)) *
        (weylRepHom K (F4.fixedRelElt k))⁻¹ =
      torusPair a (g ^ (2 * (2 : ℤ) ^ a - 1), g ^ ((2 : ℤ) ^ a)) := by
    rw [hconj, mul_inv_cancel_right]
  rw [show F4.fixedRelElt k = ((F4.fixedRelWord k).map F4.fixedOrbitElement).prod from rfl,
    weylRepHom_conj_torusPair_zpow hK (F4.fixedRelWord k) g (2 * (2 : ℤ) ^ a - 1, (2 : ℤ) ^ a)]
    at h1
  have hp := Prod.ext_iff.1 (CFSG.RankThree.LargeReeOrder.torusPair_injective hK h1)
  have c1 := intCast_eq_of_zpow_eq_of_orderOf hord hp.1
  have c2 := intCast_eq_of_zpow_eq_of_orderOf hord hp.2
  obtain ⟨t, ht⟩ : ∃ t : ZMod (2 ^ (2 * a + 1) - 1), t = 2 ^ a := ⟨_, rfl⟩
  have hθ : 2 * t ^ 2 = 1 := by rw [ht]; exact two_mul_thetaExp_sq a
  obtain ⟨hp1, hn1, hn2⟩ := zmod_two_pow_sub_one_ne_zero ha
  fin_cases k
  ·
    left
    exact map_one _
  ·
    rw [show F4.fixedRelWord _ = ([0] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, ↓reduceIte] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hn1
    linear_combination (4 + 6 * t) * c1 + (9) * hθ
  ·
    right
    change weylRepHom K (F4.fixedOrbitElement ⟨1, by decide⟩ * 1) = weylR K
    rw [mul_one]
    rfl
  ·
    rw [show F4.fixedRelWord _ = ([0, 1] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hn1
    linear_combination (4 + 6 * t) * c1 + (1 - 12 * t) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([1, 0] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hn1
    linear_combination (4 + 6 * t) * c1 + (9) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([0, 1, 0] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hn1
    linear_combination (1 + 2 * t) * c1 + (3 + 2 * t) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([1, 0, 1] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hn1
    linear_combination (4 + 6 * t) * c1 + (1 - 12 * t) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([0, 1, 0, 1] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hn1
    linear_combination (1 + 2 * t) * c1 + (3 - 2 * t - 8 * t ^ 2) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([1, 0, 1, 0] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hn1
    linear_combination (1 + 2 * t) * c1 + (3 + 2 * t) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([0, 1, 0, 1, 0] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hn1
    linear_combination (2 * t) * c1 + (1 + 4 * t ^ 2) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([1, 0, 1, 0, 1] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hn1
    linear_combination (1 + 2 * t) * c1 + (3 - 2 * t - 8 * t ^ 2) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([0, 1, 0, 1, 0, 1] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hn1
    linear_combination (2 * t) * c1 + (1 + 4 * t + 4 * t ^ 2 - 16 * t ^ 3) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([1, 0, 1, 0, 1, 0] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hn1
    linear_combination (2 * t) * c1 + (1 + 4 * t ^ 2) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([0, 1, 0, 1, 0, 1, 0] : List (Fin 2)) from rfl] at c2
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c2
    push_cast at c2
    rw [← ht] at c2
    refine absurd ?_ hn2
    linear_combination (2 * t) * c2 + (2 - 4 * t + 4 * t ^ 2 + 8 * t ^ 3) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([1, 0, 1, 0, 1, 0, 1] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hn1
    linear_combination (2 * t) * c1 + (1 + 4 * t + 4 * t ^ 2 - 16 * t ^ 3) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([0, 1, 0, 1, 0, 1, 0, 1] : List (Fin 2)) from rfl] at c2
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c2
    push_cast at c2
    rw [← ht] at c2
    refine absurd ?_ hn2
    linear_combination (2 * t) * c2 + (2 + 20 * t ^ 2 - 8 * t ^ 3 - 32 * t ^ 4) * hθ

theorem weylRepHom_eq_of_commute_torusHi_three (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (k : Fin F4.fixedWeylOrder)
    (hk : ∀ h ∈ torusHi K a .i3,
      weylRepHom K (F4.fixedRelElt k) * h = h * weylRepHom K (F4.fixedRelElt k)) :
    weylRepHom K (F4.fixedRelElt k) = 1 ∨ weylRepHom K (F4.fixedRelElt k) = weylS K := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = 2 ^ (2 * a + 1) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  obtain ⟨-, -, ⟨e30, e31⟩, -⟩ := torusExp_leadRoot ((2 : ℤ) ^ a)
  have hmem : torusPair a (g ^ (-(2 : ℤ) ^ a), g ^ (-(2 * (2 : ℤ) ^ a))) ∈ torusHi K a .i3 := by
    rw [← range_torusHiHom hK]
    refine ⟨g, ?_⟩
    simp only [torusHiHom, torusHiParam, MonoidHom.comp_apply, MonoidHom.prod_apply,
      zpowGroupHom_apply, e30, e31]
  have hconj := hk _ hmem
  have h1 : weylRepHom K (F4.fixedRelElt k) *
      torusPair a (g ^ (-(2 : ℤ) ^ a), g ^ (-(2 * (2 : ℤ) ^ a))) *
        (weylRepHom K (F4.fixedRelElt k))⁻¹ =
      torusPair a (g ^ (-(2 : ℤ) ^ a), g ^ (-(2 * (2 : ℤ) ^ a))) := by
    rw [hconj, mul_inv_cancel_right]
  rw [show F4.fixedRelElt k = ((F4.fixedRelWord k).map F4.fixedOrbitElement).prod from rfl,
    weylRepHom_conj_torusPair_zpow hK (F4.fixedRelWord k) g (-(2 : ℤ) ^ a, -(2 * (2 : ℤ) ^ a))]
    at h1
  have hp := Prod.ext_iff.1 (CFSG.RankThree.LargeReeOrder.torusPair_injective hK h1)
  have c1 := intCast_eq_of_zpow_eq_of_orderOf hord hp.1
  have c2 := intCast_eq_of_zpow_eq_of_orderOf hord hp.2
  obtain ⟨t, ht⟩ : ∃ t : ZMod (2 ^ (2 * a + 1) - 1), t = 2 ^ a := ⟨_, rfl⟩
  have hθ : 2 * t ^ 2 = 1 := by rw [ht]; exact two_mul_thetaExp_sq a
  obtain ⟨hp1, hn1, hn2⟩ := zmod_two_pow_sub_one_ne_zero ha
  fin_cases k
  ·
    left
    exact map_one _
  ·
    right
    change weylRepHom K (F4.fixedOrbitElement ⟨0, by decide⟩ * 1) = weylS K
    rw [mul_one]
    rfl
  ·
    rw [show F4.fixedRelWord _ = ([1] : List (Fin 2)) from rfl] at c2
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_one, ↓reduceIte,
      one_ne_zero] at c2
    push_cast at c2
    rw [← ht] at c2
    refine absurd ?_ hn1
    linear_combination (-1 - 2 * t) * c2 + (1 - 2 * t) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([0, 1] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hn1
    linear_combination (-1 - 2 * t) * c1 + (1 - 2 * t) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([1, 0] : List (Fin 2)) from rfl] at c2
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c2
    push_cast at c2
    rw [← ht] at c2
    refine absurd ?_ hn1
    linear_combination (-1 - 2 * t) * c2 + (1 - 2 * t) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([0, 1, 0] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hn1
    linear_combination (-1 - 2 * t) * c1 + (1 - 2 * t) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([1, 0, 1] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hn1
    linear_combination (-1 - 2 * t) * c1 + (1 - 2 * t) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([0, 1, 0, 1] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hp1
    linear_combination (1) * c1 + (-1 + 2 * t) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([1, 0, 1, 0] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hn1
    linear_combination (-1 - 2 * t) * c1 + (1 - 2 * t) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([0, 1, 0, 1, 0] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hp1
    linear_combination (1) * c1 + (-1 + 2 * t) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([1, 0, 1, 0, 1] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hp1
    linear_combination (1) * c1 + (-1 + 2 * t) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([0, 1, 0, 1, 0, 1] : List (Fin 2)) from rfl] at c2
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c2
    push_cast at c2
    rw [← ht] at c2
    refine absurd ?_ hn1
    linear_combination (1 - 2 * t) * c2 + (1 + 2 * t + 4 * t ^ 2 - 8 * t ^ 3) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([1, 0, 1, 0, 1, 0] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hp1
    linear_combination (1) * c1 + (-1 + 2 * t) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([0, 1, 0, 1, 0, 1, 0] : List (Fin 2)) from rfl] at c2
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c2
    push_cast at c2
    rw [← ht] at c2
    refine absurd ?_ hn1
    linear_combination (1 - 2 * t) * c2 + (1 + 2 * t + 4 * t ^ 2 - 8 * t ^ 3) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([1, 0, 1, 0, 1, 0, 1] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hn2
    linear_combination (-2 * t) * c1 + (2 + 4 * t ^ 2 - 8 * t ^ 3) * hθ
  ·
    rw [show F4.fixedRelWord _ = ([0, 1, 0, 1, 0, 1, 0, 1] : List (Fin 2)) from rfl] at c1
    simp only [expWord, expAct, List.foldr, Fin.isValue, Fin.val_zero, Fin.val_one,
      ↓reduceIte, one_ne_zero] at c1
    push_cast at c1
    rw [← ht] at c1
    refine absurd ?_ hn2
    linear_combination (-2 * t) * c1 + (2 + 4 * t ^ 2 + 8 * t ^ 3 - 16 * t ^ 4) * hθ

end WeylTorusAction

end CFSG.LocalAnalysis.EvenBN.TwoF4
