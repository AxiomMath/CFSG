module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.ModelBasic
public import CFSG.RankThree.SteinbergR3ELargeReeOrder
public import CFSG.RankThree.PartOne.Q1327T.Item7D4W
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

section Torus

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

open CFSG.LieType.Ree.LargeReeCover (torusPair pairedTorusHom f4i)

theorem torusH_eq_reeFixedTorus (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    torusH K a = F4.reeFixedTorus K a := by
  refine le_antisymm ?_ fun h hh => ?_
  · rintro _ ⟨⟨u, v⟩, rfl⟩
    exact rankOne_torusPair_mem_reeFixedTorus hK u v
  · obtain ⟨u, v, rfl⟩ := rankOne_exists_torusPair_eq hK hh
    exact ⟨(u, v), rfl⟩

theorem torusH_le_reeGamma (hK : Nat.card K = 2 ^ (2 * a + 1)) : torusH K a ≤ F4.reeGamma K a := by
  rw [torusH_eq_reeFixedTorus hK]
  exact inf_le_right

theorem card_torusH (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (torusH K a) = (2 ^ (2 * a + 1) - 1) ^ 2 := by
  rw [torusH_eq_reeFixedTorus hK, CFSG.RankThree.LargeReeOrder.card_reeFixedTorus hK, hK]

omit [Finite K] [CharP K F4.prime]
  in
theorem torusHi_le_torusH (i : Idx) : torusHi K a i ≤ torusH K a :=
  inf_le_left

theorem torusH_le_normalizer_rootSpan_inf (hK : Nat.card K = 2 ^ (2 * a + 1))
    {S : Set (Fin F4.tag.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot F4.tag α) :
    torusH K a ≤ Subgroup.normalizer
      ((rootSpan F4.tag K S ⊓ F4.reeGamma K a : Subgroup (ModGL F4.tag K)) :
        Set (ModGL F4.tag K)) := by
  intro h hh
  have hT : h ∈ torusGroup F4.tag K := by
    obtain ⟨⟨u, v⟩, rfl⟩ := hh
    exact rankOne_torusPair_mem_torusGroup u v
  exact Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.2
    ⟨torusGroup_le_normalizer_rootSpan hS hT,
      Subgroup.le_normalizer (torusH_le_reeGamma hK hh)⟩)

theorem torusH_le_normalizer_sylowP (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    torusH K a ≤ Subgroup.normalizer
      (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)) :=
  torusH_le_normalizer_rootSpan_inf hK (S := {α | IsRoot F4.tag α ∧ 0 < height α})
    fun _ hα => hα.1

end Torus

section Weyl

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

open CFSG.LieType.Ree.LargeReeCover (torusPair pairedTorusHom f4i)

theorem mem_normalizer_of_mul_self {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g * g = 1) (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have := h _ hx
  rwa [hgi, show g * (g * x * g) * g = (g * g) * x * (g * g) by group, hg, one_mul,
    mul_one] at this

omit [Finite K] in
theorem weylR_mul_self :
    weylR K * weylR K = 1 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [weylR, weylTwo, ← CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo,
    fixedOrbitElement_mul_self, canonicalRep_one]

omit [Finite K] in
theorem weylS_mul_self :
    weylS K * weylS K = 1 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [weylS, weylOne, ← CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo,
    fixedOrbitElement_mul_self, canonicalRep_one]

end Weyl

section WeylConj

variable {K : Type} [Field K] {a : ℕ}
  [CharP K F4.prime]

theorem weylOne_conj_word {r₁ r₁' r₂ r₂' r₃ r₃' r₄ r₄' : ℕ} (h₁ : (r₁, r₁') ∈ weylOnePairs)
    (h₂ : (r₂, r₂') ∈ weylOnePairs) (h₃ : (r₃, r₃') ∈ weylOnePairs)
    (h₄ : (r₄, r₄') ∈ weylOnePairs) (c₁ c₂ c₃ c₄ : K) :
    weylOne K * (sylowX K r₁ c₁ * sylowX K r₂ c₂ * sylowX K r₃ c₃ * sylowX K r₄ c₄) *
        (weylOne K)⁻¹ =
      sylowX K r₁' c₁ * sylowX K r₂' c₂ * sylowX K r₃' c₃ * sylowX K r₄' c₄ := by
  rw [show sylowX K r₁ c₁ * sylowX K r₂ c₂ * sylowX K r₃ c₃ * sylowX K r₄ c₄ =
      (sylowX K r₁ c₁ * sylowX K r₂ c₂) * (sylowX K r₃ c₃ * sylowX K r₄ c₄) by group,
    weyl_conj_mul, weylOne_conj_pair h₁ h₂, weylOne_conj_pair h₃ h₄]
  group

theorem weylTwo_conj_word {r₁ r₁' r₂ r₂' r₃ r₃' r₄ r₄' : ℕ} (h₁ : (r₁, r₁') ∈ weylTwoPairs)
    (h₂ : (r₂, r₂') ∈ weylTwoPairs) (h₃ : (r₃, r₃') ∈ weylTwoPairs)
    (h₄ : (r₄, r₄') ∈ weylTwoPairs) (c₁ c₂ c₃ c₄ : K) :
    weylTwo K * (sylowX K r₁ c₁ * sylowX K r₂ c₂ * sylowX K r₃ c₃ * sylowX K r₄ c₄) *
        (weylTwo K)⁻¹ =
      sylowX K r₁' c₁ * sylowX K r₂' c₂ * sylowX K r₃' c₃ * sylowX K r₄' c₄ := by
  rw [show sylowX K r₁ c₁ * sylowX K r₂ c₂ * sylowX K r₃ c₃ * sylowX K r₄ c₄ =
      (sylowX K r₁ c₁ * sylowX K r₂ c₂) * (sylowX K r₃ c₃ * sylowX K r₄ c₄) by group,
    weyl_conj_mul, weylTwo_conj_pair h₁ h₂, weylTwo_conj_pair h₃ h₄]
  group

theorem weylS_conj_rootElt {i : Idx} (hi : i ≠ .i3) (u : K) :
    weylS K * rootElt K a i u * (weylS K)⁻¹ = rootElt K a i.sPerm u := by
  cases i
  case i3 => exact absurd rfl hi
  case i1 =>
    simp only [rootElt, Idx.sPerm, sylowB, sylowD]
    exact weylOne_conj_word (by decide) (by decide) (by decide) (by decide) _ _ _ _
  case i2 =>
    simp only [rootElt, Idx.sPerm, sylowB, sylowD]
    exact weylOne_conj_word (by decide) (by decide) (by decide) (by decide) _ _ _ _
  case i4 =>
    simp only [rootElt, Idx.sPerm, sylowB, sylowD]
    exact weylOne_conj_word (by decide) (by decide) (by decide) (by decide) _ _ _ _
  case i8 =>
    simp only [rootElt, Idx.sPerm, sylowB, sylowD]
    exact weylOne_conj_word (by decide) (by decide) (by decide) (by decide) _ _ _ _
  case i5 =>
    simp only [rootElt, Idx.sPerm, sylowH, sylowF]
    exact weylOne_conj_word (by decide) (by decide) (by decide) (by decide) _ _ _ _
  case i12 =>
    simp only [rootElt, Idx.sPerm, sylowH, sylowF]
    exact weylOne_conj_word (by decide) (by decide) (by decide) (by decide) _ _ _ _
  case i6 =>
    simp only [rootElt, Idx.sPerm, sylowH, sylowF]
    exact weylOne_conj_word (by decide) (by decide) (by decide) (by decide) _ _ _ _
  case i11 =>
    simp only [rootElt, Idx.sPerm, sylowH, sylowF]
    exact weylOne_conj_word (by decide) (by decide) (by decide) (by decide) _ _ _ _
  case i7 =>
    simp only [rootElt, Idx.sPerm, sylowJ, sylowK]
    exact weylOne_conj_pair (by decide) (by decide) _ _
  case i9 =>
    simp only [rootElt, Idx.sPerm, sylowJ, sylowK]
    exact weylOne_conj_pair (by decide) (by decide) _ _
  case i10 =>
    simp only [rootElt, Idx.sPerm, sylowL]
    exact weylOne_conj_pair (by decide) (by decide) _ _

theorem weylR_conj_rootElt {i : Idx} (hi1 : i ≠ .i1) (hi2 : i ≠ .i2) (u : K) :
    weylR K * rootElt K a i u * (weylR K)⁻¹ = rootElt K a i.rPerm u := by
  cases i
  case i1 => exact absurd rfl hi1
  case i2 => exact absurd rfl hi2
  case i3 =>
    simp only [rootElt, Idx.rPerm, sylowA, sylowJ]
    exact weylTwo_conj_pair (by decide) (by decide) _ _
  case i7 =>
    simp only [rootElt, Idx.rPerm, sylowA, sylowJ]
    exact weylTwo_conj_pair (by decide) (by decide) _ _
  case i4 =>
    simp only [rootElt, Idx.rPerm, sylowD, sylowF]
    exact weylTwo_conj_word (by decide) (by decide) (by decide) (by decide) _ _ _ _
  case i8 =>
    simp only [rootElt, Idx.rPerm, sylowD, sylowF]
    exact weylTwo_conj_word (by decide) (by decide) (by decide) (by decide) _ _ _ _
  case i6 =>
    simp only [rootElt, Idx.rPerm, sylowD, sylowF]
    exact weylTwo_conj_word (by decide) (by decide) (by decide) (by decide) _ _ _ _
  case i11 =>
    simp only [rootElt, Idx.rPerm, sylowD, sylowF]
    exact weylTwo_conj_word (by decide) (by decide) (by decide) (by decide) _ _ _ _
  case i9 =>
    simp only [rootElt, Idx.rPerm, sylowK, sylowL]
    exact weylTwo_conj_pair (by decide) (by decide) _ _
  case i10 =>
    simp only [rootElt, Idx.rPerm, sylowK, sylowL]
    exact weylTwo_conj_pair (by decide) (by decide) _ _
  case i5 =>
    simp only [rootElt, Idx.rPerm, sylowH]
    exact weylTwo_conj_word (by decide) (by decide) (by decide) (by decide) _ _ _ _
  case i12 =>
    simp only [rootElt, Idx.rPerm, sylowH]
    exact weylTwo_conj_word (by decide) (by decide) (by decide) (by decide) _ _ _ _

theorem map_conj_weylS_rootV {i : Idx} (hi : i ≠ .i3) :
    (rootV K a i).map (MulAut.conj (weylS K)).toMonoidHom = rootV K a i.sPerm := by
  rw [rootV, rootV, MonoidHom.map_closure, ← Set.range_comp]
  congr 1
  ext g
  simp only [Set.mem_range, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    weylS_conj_rootElt hi]

theorem map_conj_weylR_rootV {i : Idx} (hi1 : i ≠ .i1) (hi2 : i ≠ .i2) :
    (rootV K a i).map (MulAut.conj (weylR K)).toMonoidHom = rootV K a i.rPerm := by
  rw [rootV, rootV, MonoidHom.map_closure, ← Set.range_comp]
  congr 1
  ext g
  simp only [Set.mem_range, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    weylR_conj_rootElt hi1 hi2]

end WeylConj

section WeylTorus

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

open CFSG.LieType.Ree.LargeReeCover (torusPair pairedTorusHom f4i)

theorem weylR_mem_reeGamma : weylR K ∈ F4.reeGamma K a :=
  (canonicalRep_mem_reeFixedMonomial F4 K a (fixedOrbitElement_mem _)).2

theorem weylS_mem_reeGamma : weylS K ∈ F4.reeGamma K a :=
  (canonicalRep_mem_reeFixedMonomial F4 K a (fixedOrbitElement_mem _)).2

theorem weylR_mem_leviN : weylR K ∈ leviN K a .i1 :=
  Subgroup.subset_closure (Or.inr rfl)

theorem weylS_mem_leviN : weylS K ∈ leviN K a .i3 :=
  Subgroup.subset_closure (Or.inr rfl)

theorem weylS_conj_torusOne (hK : Nat.card K = 2 ^ (2 * a + 1)) (u : Kˣ) :
    weylS K * pairedTorusHom a (f4i 0) (f4i 3) u * (weylS K)⁻¹ =
      (pairedTorusHom a (f4i 0) (f4i 3) u)⁻¹ := by
  have h := congrArg Subtype.val (CFSG.SectionRank.LargeRee.torus_reflections (a := a) hK u).1
  have hn : (nrep F4.tag K (F4.blockElt (CFSG.SectionRank.LargeRee.fi 0)) : ModGL F4.tag K) =
      canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) := by
    change canonicalRep (coxeterSystem F4.tag) K _ = _
    rw [blockElt_eq]
    rfl
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hn] at h
  rw [← rankOneTorusPair_left, LargeReeCover.torusPair_eq_reeTorus]
  simp only [CFSG.SectionRank.LargeRee.reeTorus_one, mul_one]
  exact h

theorem weylR_conj_torusTwo (hK : Nat.card K = 2 ^ (2 * a + 1)) (v : Kˣ) :
    weylR K * pairedTorusHom a (f4i 1) (f4i 2) v * (weylR K)⁻¹ =
      (pairedTorusHom a (f4i 1) (f4i 2) v)⁻¹ := by
  have h := congrArg Subtype.val
    (CFSG.SectionRank.LargeRee.torus_reflections (a := a) hK v).2.2.1
  have hn : (nrep F4.tag K (F4.blockElt (CFSG.SectionRank.LargeRee.fi 1)) : ModGL F4.tag K) =
      canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩) := by
    change canonicalRep (coxeterSystem F4.tag) K _ = _
    rw [blockElt_eq]
    rfl
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hn] at h
  rw [← rankOneTorusPair_right, LargeReeCover.torusPair_eq_reeTorus]
  simp only [CFSG.SectionRank.LargeRee.reeTorus_one, one_mul]
  exact h

omit [Finite K] [CharP K F4.prime]
  in
theorem pairedTorusHom_mem_torusH (u : Kˣ) :
    pairedTorusHom a (f4i 0) (f4i 3) u ∈ torusH K a ∧
      pairedTorusHom a (f4i 1) (f4i 2) u ∈ torusH K a :=
  ⟨⟨(u, 1), rankOneTorusPair_left u⟩, ⟨(1, u), rankOneTorusPair_right u⟩⟩

theorem weylS_mem_normalizer_torusH (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    weylS K ∈ Subgroup.normalizer (torusH K a : Set (ModGL F4.tag K)) := by
  refine mem_normalizer_of_mul_self weylS_mul_self ?_
  rintro _ ⟨⟨u, v⟩, rfl⟩
  rw [rankOneTorusPair_eq_mul, weyl_conj_mul, weylS_conj_torusOne hK, weylS,
    canonicalRep_conj_torusTwo hK]
  exact mul_mem (inv_mem (pairedTorusHom_mem_torusH u).1)
    (mul_mem (pairedTorusHom_mem_torusH v).2 (pairedTorusHom_mem_torusH v).1)

theorem weylR_mem_normalizer_torusH (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    weylR K ∈ Subgroup.normalizer (torusH K a : Set (ModGL F4.tag K)) := by
  refine mem_normalizer_of_mul_self weylR_mul_self ?_
  rintro _ ⟨⟨u, v⟩, rfl⟩
  rw [rankOneTorusPair_eq_mul, weyl_conj_mul, weylR_conj_torusTwo hK, weylR,
    canonicalRep_conj_torusOne hK]
  exact mul_mem (mul_mem (pairedTorusHom_mem_torusH u).1 (pairedTorusHom_mem_torusH _).2)
    (inv_mem (pairedTorusHom_mem_torusH v).2)

end WeylTorus

theorem map_conj_mul {G : Type*} [Group G] (H : Subgroup G) (g h : G) :
    H.map (MulAut.conj (g * h)).toMonoidHom =
      (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  group

section Levi

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem map_conj_le_reeGamma {g : ModGL F4.tag K} {N : Subgroup (ModGL F4.tag K)}
    (hg : g ∈ F4.reeGamma K a) (hN : N ≤ F4.reeGamma K a) :
    N.map (MulAut.conj g).toMonoidHom ≤ F4.reeGamma K a := by
  rintro _ ⟨x, hx, rfl⟩
  exact mul_mem (mul_mem hg (hN hx)) (inv_mem hg)

theorem leviN_le_reeGamma (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : Idx) :
    leviN K a i ≤ F4.reeGamma K a := by
  have h1 := rankOneGroupOne_le_reeGamma (K := K) (a := a) hK
  have h2 := rankOneGroupTwo_le_reeGamma (K := K) (a := a) hK
  have hr := weylR_mem_reeGamma (K := K) (a := a)
  have hs := weylS_mem_reeGamma (K := K) (a := a)
  cases i
  case i1 | i2 => exact h2
  case i3 => exact h1
  case i4 | i8 => exact map_conj_le_reeGamma hs h2
  case i6 | i11 => exact map_conj_le_reeGamma (mul_mem hr hs) h2
  case i5 | i12 => exact map_conj_le_reeGamma (mul_mem (mul_mem hs hr) hs) h2
  case i7 => exact map_conj_le_reeGamma hr h1
  case i9 => exact map_conj_le_reeGamma (mul_mem hs hr) h1
  case i10 => exact map_conj_le_reeGamma (mul_mem (mul_mem hr hs) hr) h1

theorem nonempty_leviN_equiv_SL2 (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx}
    (hi : i.isLin = true) : Nonempty (leviN K a i ≃* SL2 K) := by
  have e := (rankOneEquivSL K a hK).symm
  have key : ∀ g : ModGL F4.tag K, Nonempty
      ((rankOneGroupOne K a).map (MulAut.conj g).toMonoidHom ≃* SL2 K) := fun g =>
    ⟨(Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).symm.trans e⟩
  cases i <;> simp only [Idx.isLin, Bool.false_eq_true] at hi
  case i3 => exact ⟨e⟩
  case i7 => exact key _
  case i9 => exact key _
  case i10 => exact key _

theorem nonempty_leviN_equiv_suzuki (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx}
    (hi : i.isLin = false) : Nonempty (leviN K a i ≃* CFSG.Blueprint.suzukiGroup a K) := by
  have e := rankOneEquivSuzuki K a ha hK
  have key : ∀ g : ModGL F4.tag K, Nonempty
      ((rankOneGroupTwo K a).map (MulAut.conj g).toMonoidHom ≃* CFSG.Blueprint.suzukiGroup a K) :=
    fun g => ⟨(Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).symm.trans e⟩
  cases i <;> simp only [Idx.isLin, Bool.true_eq_false] at hi
  case i1 | i2 => exact ⟨e⟩
  case i4 | i8 => exact key _
  case i6 | i11 => exact key _
  case i5 | i12 => exact key _

theorem card_leviN_of_isLin (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx}
    (hi : i.isLin = true) :
    Nat.card (leviN K a i) = 2 ^ (2 * a + 1) * ((2 ^ (2 * a + 1)) ^ 2 - 1) := by
  obtain ⟨e⟩ := nonempty_leviN_equiv_SL2 hK hi
  rw [Nat.card_congr e.toEquiv, ← card_rankOneGroupOne hK,
    Nat.card_congr (rankOneEquivSL K a hK).toEquiv]

theorem card_leviN_of_not_isLin (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx}
    (hi : i.isLin = false) :
    Nat.card (leviN K a i) =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  obtain ⟨e⟩ := nonempty_leviN_equiv_suzuki ha hK hi
  rw [Nat.card_congr e.toEquiv, ← card_rankOneGroupTwo ha hK,
    Nat.card_congr (rankOneEquivSuzuki K a ha hK).toEquiv]

theorem rootV_le_leviN (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : Idx) :
    rootV K a i ≤ leviN K a i := by
  have h1 : rootV K a .i1 ≤ rankOneGroupTwo K a := by
    rw [rootV, Subgroup.closure_le]
    rintro _ ⟨u, rfl⟩
    exact Subgroup.subset_closure (Or.inl (Or.inl (sylowB_mem_U2 hK u 0)))
  have h2 : rootV K a .i2 ≤ rankOneGroupTwo K a := by
    rw [rootV, Subgroup.closure_le]
    rintro _ ⟨u, rfl⟩
    exact Subgroup.subset_closure (Or.inl (Or.inl (sylowB_mem_U2 hK 0 u)))
  have h3 : rootV K a .i3 ≤ rankOneGroupOne K a := by
    rw [rootV, Subgroup.closure_le]
    rintro _ ⟨u, rfl⟩
    exact Subgroup.subset_closure (Or.inl (Or.inl (sylowA_mem_U1 hK u)))
  have hs : ∀ {j : Idx}, j ≠ .i3 → rootV K a j.sPerm =
      (rootV K a j).map (MulAut.conj (weylS K)).toMonoidHom :=
    fun hj => (map_conj_weylS_rootV hj).symm
  have hr : ∀ {j : Idx}, j ≠ .i1 → j ≠ .i2 → rootV K a j.rPerm =
      (rootV K a j).map (MulAut.conj (weylR K)).toMonoidHom :=
    fun hj1 hj2 => (map_conj_weylR_rootV hj1 hj2).symm
  cases i
  case i1 => exact h1
  case i2 => exact h2
  case i3 => exact h3
  case i4 =>
    rw [show Idx.i4 = Idx.i1.sPerm from rfl, hs (by decide)]
    exact Subgroup.map_mono h1
  case i8 =>
    rw [show Idx.i8 = Idx.i2.sPerm from rfl, hs (by decide)]
    exact Subgroup.map_mono h2
  case i6 =>
    rw [show Idx.i6 = Idx.i1.sPerm.rPerm from rfl, hr (by decide) (by decide), hs (by decide)]
    simp only [leviN, map_conj_mul]
    exact Subgroup.map_mono (Subgroup.map_mono h1)
  case i11 =>
    rw [show Idx.i11 = Idx.i2.sPerm.rPerm from rfl, hr (by decide) (by decide), hs (by decide)]
    simp only [leviN, map_conj_mul]
    exact Subgroup.map_mono (Subgroup.map_mono h2)
  case i5 =>
    rw [show Idx.i5 = Idx.i1.sPerm.rPerm.sPerm from rfl, hs (by decide),
      hr (by decide) (by decide), hs (by decide)]
    simp only [leviN, map_conj_mul]
    exact Subgroup.map_mono (Subgroup.map_mono (Subgroup.map_mono h1))
  case i12 =>
    rw [show Idx.i12 = Idx.i2.sPerm.rPerm.sPerm from rfl, hs (by decide),
      hr (by decide) (by decide), hs (by decide)]
    simp only [leviN, map_conj_mul]
    exact Subgroup.map_mono (Subgroup.map_mono (Subgroup.map_mono h2))
  case i7 =>
    rw [show Idx.i7 = Idx.i3.rPerm from rfl, hr (by decide) (by decide)]
    exact Subgroup.map_mono h3
  case i9 =>
    rw [show Idx.i9 = Idx.i3.rPerm.sPerm from rfl, hs (by decide), hr (by decide) (by decide)]
    simp only [leviN, map_conj_mul]
    exact Subgroup.map_mono (Subgroup.map_mono h3)
  case i10 =>
    rw [show Idx.i10 = Idx.i3.rPerm.sPerm.rPerm from rfl, hr (by decide) (by decide),
      hs (by decide), hr (by decide) (by decide)]
    simp only [leviN, map_conj_mul]
    exact Subgroup.map_mono (Subgroup.map_mono (Subgroup.map_mono h3))

end Levi

section Involutions

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

omit [CharP K F4.prime] in
theorem stdTwoG_add (hK : Nat.card K = 2 ^ (2 * a + 1)) (s s' : K) :
    stdTwoG a (s + s') = stdTwoG a s * stdTwoG a s' := by
  obtain ⟨σ, hσ, -⟩ := exists_sigma (m := a) hK
  rw [stdTwoG_eq_xUnit, stdTwoG_eq_xUnit, stdTwoG_eq_xUnit, ← hσ, ← hσ, ← hσ, map_add, xUnit_add,
    xUnit_add]
  have hc := (largeRee_commute_xx (K := K) (σ s') s).eq
  calc xUnit F4.tag K largeReeI1 (σ s) * xUnit F4.tag K largeReeI1 (σ s') *
        (xUnit F4.tag K largeReeI4 s * xUnit F4.tag K largeReeI4 s') =
      xUnit F4.tag K largeReeI1 (σ s) *
        (xUnit F4.tag K largeReeI1 (σ s') * xUnit F4.tag K largeReeI4 s) *
          xUnit F4.tag K largeReeI4 s' := by group
    _ = xUnit F4.tag K largeReeI1 (σ s) * xUnit F4.tag K largeReeI4 s *
        (xUnit F4.tag K largeReeI1 (σ s') * xUnit F4.tag K largeReeI4 s') := by rw [hc]; group

theorem rootElt_add (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx} (hi : i.isSz = false)
    (u v : K) : rootElt K a i (u + v) = rootElt K a i u * rootElt K a i v := by
  rcases i.isSz_or_isLin_or_isCenter with h | h | h
  · rw [h] at hi
    exact absurd hi (by decide)
  · rw [(rootElt_eq_coord i _).2.2 h, (rootElt_eq_coord i _).2.2 h,
      (rootElt_eq_coord i _).2.2 h, twoCoordG, twoCoordG, twoCoordG, stdTwoG_add hK]
    group
  · exact rootElt_add_of_isCenter hK h u v

theorem rootElt_injective (hK : Nat.card K = 2 ^ (2 * a + 1)) (i : Idx) :
    Function.Injective (rootElt K a i) := by
  intro u v h
  rw [rootElt_eq_sylowVec, rootElt_eq_sylowVec] at h
  have h' := (bijOn_sylowVec hK).2.1 (Set.mem_univ _) (Set.mem_univ _) h
  simpa using congrFun h' i.coord

theorem rootElt_mul_self (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx} (hi : i.isSz = false)
    (u : K) : rootElt K a i u * rootElt K a i u = 1 := by
  rw [← rootElt_add hK hi, CharTwo.add_self_eq_zero, rootElt_zero]

theorem orderOf_rootElt (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx} (hi : i.isSz = false)
    {u : K} (hu : u ≠ 0) : orderOf (rootElt K a i u) = 2 := by
  refine orderOf_eq_prime (by rw [sq, rootElt_mul_self hK hi]) fun h => hu ?_
  exact rootElt_injective hK i (h.trans (rootElt_zero i).symm)

omit [Finite K] [CharP K F4.prime]
  in
theorem invE_eq_centralZ : invE K a = centralZ K a 1 ∧ invF K a = sylowL a K 1 :=
  ⟨sylowH_zero_eq_centralZ 1, rfl⟩

theorem invE_invF_mem (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    invE K a ∈ rootV K a .i12 ∧ invF K a ∈ rootV K a .i10 ∧
      invE K a ∈ F4.reeFixedPosUnipotent K a ∧ invF K a ∈ F4.reeFixedPosUnipotent K a ∧
      orderOf (invE K a) = 2 ∧ orderOf (invF K a) = 2 :=
  ⟨rootElt_mem_rootV _ _, rootElt_mem_rootV _ _,
    rootV_le_sylowP hK _ (rootElt_mem_rootV _ _), rootV_le_sylowP hK _ (rootElt_mem_rootV _ _),
    orderOf_rootElt hK rfl one_ne_zero, orderOf_rootElt hK rfl one_ne_zero⟩

theorem commute_invE (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {u : ModGL F4.tag K}
    (hu : u ∈ F4.reeFixedPosUnipotent K a) : u * invE K a = invE K a * u := by
  rw [invE_eq_centralZ.1]
  exact commute_centralZ ha hK hu 1

theorem reeGamma_inf_centralizer_invE_invF (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeGamma K a ⊓ Subgroup.centralizer {invE K a} = radR K a ⊔ leviN K a .i1 ∧
      radR K a ⊓ leviN K a .i1 = ⊥ ∧
      F4.reeGamma K a ⊓ Subgroup.centralizer {invF K a} = S4 K a ⊔ leviN K a .i3 ∧
      S4 K a ⊓ leviN K a .i3 = ⊥ ∧
      ∀ g ∈ F4.reeGamma K a, g * invE K a * g⁻¹ ≠ invF K a := by
  obtain ⟨hz, hzR, -, -, -, ht, htR, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hconj⟩ :=
    large_Ree_two_involution_centralizers a ha K hK
  rw [invE_eq_centralZ.1, invE_eq_centralZ.2, radR_eq_complement hK, S4_eq_tKernel hK]
  exact ⟨hz, hzR, ht, htR, hconj⟩

end Involutions

end CFSG.LocalAnalysis.EvenBN.TwoF4

