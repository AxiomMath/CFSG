module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerFaith
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15CountBound

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Module

section GLevel

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

theorem quad_apply {B : Subgroup G} {U : Submodule (ZMod 2) V} (hquad : IsQuadraticOn ρ B U)
    {a b : G} (ha : a ∈ B) (hb : b ∈ B) {u : V} (hu : u ∈ U) :
    ρ b (ρ a u - u) = ρ a u - u := by
  have h1 : ρ a u - u ∈ commOn ρ B U := Submodule.subset_span ⟨a, ha, u, hu, rfl⟩
  exact mem_fixSub.mp (hquad h1) b hb

theorem mem_cenOn_of_commute {L B : Subgroup G} {U : Submodule (ZMod 2) V}
    (hmove : ∀ b ∈ B, b ∉ cenOn ρ B U → ∃ k ∈ L, ∃ u ∈ U, ρ b (ρ k u) ≠ ρ k (ρ b u))
    {b : G} (hb : b ∈ B) (hcomm : ∀ k ∈ L, b * k = k * b) : b ∈ cenOn ρ B U := by
  by_contra hc
  obtain ⟨k, hk, u, -, hne⟩ := hmove b hb hc
  apply hne
  calc ρ b (ρ k u) = ρ (b * k) u := by rw [map_mul]; rfl
    _ = ρ (k * b) u := by rw [hcomm k hk]
    _ = ρ k (ρ b u) := by rw [map_mul]; rfl

theorem map_subtype_fixSub_subgroupOf {H B : Subgroup G} (hBH : B ≤ H)
    (SU : Subrepresentation (ρ.comp H.subtype)) :
    (fixSub SU.toRepresentation (B.subgroupOf H)).map SU.toSubmodule.subtype =
      fixOn ρ B SU.toSubmodule := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine mem_fixOn.mpr ⟨x.2, fun a ha => ?_⟩
    have h1 : SU.toRepresentation ⟨a, hBH ha⟩ x = x :=
      (mem_fixSub.mp hx) _ (Subgroup.mem_subgroupOf.mpr ha)
    exact congrArg Subtype.val h1
  · intro hw
    obtain ⟨hw, hfix⟩ := mem_fixOn.mp hw
    refine ⟨⟨w, hw⟩, mem_fixSub.mpr fun a ha => ?_, rfl⟩
    apply Subtype.ext
    exact hfix _ (Subgroup.mem_subgroupOf.mp ha)

theorem finrank_fixSub_subgroupOf {H B : Subgroup G} (hBH : B ≤ H)
    (SU : Subrepresentation (ρ.comp H.subtype)) :
    finrank (ZMod 2) ↥(fixSub SU.toRepresentation (B.subgroupOf H)) =
      finrank (ZMod 2) ↥(fixOn ρ B SU.toSubmodule) := by
  rw [← map_subtype_fixSub_subgroupOf hBH SU]
  exact (Submodule.finrank_map_subtype_eq _ _).symm

end GLevel

section Factor

theorem exists_nontriv_series_factor {K Lg : Type} [Group K] [Group Lg] (α : Lg →* K)
    (hperf : commutator Lg = ⊤) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {ρ : Representation (ZMod 2) K W} {r : ℕ} {Vs : Fin (r + 1) → Subrepresentation ρ}
    (hVs : IsCompositionSeries r Vs) (hnt : ∃ l, ρ (α l) ≠ 1) :
    ∃ i : Fin r, ∃ l, factorRep (Vs i.castSucc) (Vs i.succ) (α l) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hsum := nontrivCount_comp_eq_sum α (fun i => (hVs.covBy i).le) hVs.zero hVs.last
  have h0 : nontrivCount (ρ.comp α) = 0 := by
    rw [hsum]
    refine Finset.sum_eq_zero fun i _ => ?_
    haveI : Finite (↥(Vs i.succ).toSubmodule ⧸ factorSub (Vs i.castSucc) (Vs i.succ)) :=
      factor_finite _ _
    exact nontrivCount_eq_zero_of_trivial _ fun l => hcon i l
  obtain ⟨l, hl⟩ := hnt
  exact hl (trivial_of_nontrivCount_eq_zero hperf (ρ.comp α) h0 l)

end Factor

section Arith

theorem card_mul_le_of_codim {K Z : Type*} [Group K] [AddCommGroup Z] [Module (ZMod 2) Z]
    [Finite Z] (κ : Representation (ZMod 2) K Z) (A : Subgroup K) {n m : ℕ}
    (h : 2 ^ (finrank (ZMod 2) Z - finrank (ZMod 2) ↥(fixSub κ A)) * n ≤ m) :
    Nat.card Z * n ≤ m * Nat.card ↥(fixSub κ A) := by
  have hfin : finrank (ZMod 2) ↥(fixSub κ A) ≤ finrank (ZMod 2) Z := Submodule.finrank_le _
  have hZ : Nat.card Z = 2 ^ finrank (ZMod 2) Z := card_eq_two_pow_finrank'
  have hF : Nat.card ↥(fixSub κ A) = 2 ^ finrank (ZMod 2) ↥(fixSub κ A) :=
    card_eq_two_pow_finrank _
  have h4 : Nat.card Z =
      2 ^ (finrank (ZMod 2) Z - finrank (ZMod 2) ↥(fixSub κ A)) * Nat.card ↥(fixSub κ A) := by
    rw [hZ, hF, ← pow_add]
    congr 1
    omega
  calc Nat.card Z * n
      = (2 ^ (finrank (ZMod 2) Z - finrank (ZMod 2) ↥(fixSub κ A)) * n) *
          Nat.card ↥(fixSub κ A) := by rw [h4]; ring
    _ ≤ m * Nat.card ↥(fixSub κ A) := Nat.mul_le_mul_right _ h

end Arith

section Main

theorem exists_chief_factor {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) G V) (L B : Subgroup G)
    {U : Submodule (ZMod 2) V}
    (hctx : InnerCtx (L.subgroupOf (L ⊔ B)) (B.subgroupOf (L ⊔ B)))
    (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) U) (hLnt : ¬ L ≤ cenOn ρ L U)
    (hbest : IsBestOffenderOn ρ B U) (hquad : IsQuadraticOn ρ B U)
    (hmove : ∀ b ∈ B, b ∉ cenOn ρ B U → ∃ k ∈ L, ∃ u ∈ U, ρ b (ρ k u) ≠ ρ k (ρ b u)) :
    ∃ (Z : Type) (_ : AddCommGroup Z) (_ : Module (ZMod 2) Z) (_ : Finite Z)
      (κ : Representation (ZMod 2) ↥(L ⊔ B) Z),
      ChiefData (L.subgroupOf (L ⊔ B)) (B.subgroupOf (L ⊔ B)) κ := by
  classical
  let LK : Subgroup ↥(L ⊔ B) := L.subgroupOf (L ⊔ B)
  let BK : Subgroup ↥(L ⊔ B) := B.subgroupOf (L ⊔ B)
  let SU : Subrepresentation (ρ.comp (L ⊔ B).subtype) :=
    ⟨U, fun g w hw => hinv (g : G) g.2 w hw⟩
  haveI : Finite ↥SU.toSubmodule := inferInstanceAs (Finite ↥U)
  obtain ⟨r, Vs, hVs⟩ := exists_isCompositionSeries SU.toRepresentation
  have hnt : ∃ l : ↥LK, SU.toRepresentation (LK.subtype l) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hLnt
    intro l hl
    refine mem_cenOn.mpr ⟨hl, fun u hu => ?_⟩
    have h1 := hcon ⟨⟨l, Subgroup.mem_sup_left hl⟩, Subgroup.mem_subgroupOf.mpr hl⟩
    exact congrArg Subtype.val (LinearMap.congr_fun h1 ⟨u, hu⟩)
  obtain ⟨i, l0, hl0⟩ := exists_nontriv_series_factor LK.subtype hctx.quasi.1 hVs hnt
  have hcov : Vs i.castSucc ⋖ Vs i.succ := hVs.covBy i
  haveI hfin : Finite (↥(Vs i.succ).toSubmodule ⧸ factorSub (Vs i.castSucc) (Vs i.succ)) :=
    factor_finite _ _
  refine ⟨_, inferInstance, inferInstance, hfin, factorRep (Vs i.castSucc) (Vs i.succ), ?_⟩
  have hLκ : ∃ l ∈ LK, ∃ z, factorRep (Vs i.castSucc) (Vs i.succ) l z ≠ z := by
    by_contra hcon
    push Not at hcon
    exact hl0 (LinearMap.ext fun z => hcon (LK.subtype l0) l0.2 z)
  refine ⟨factor_nontrivial hcov, fun W hW => factor_invariant_eq_bot_or_top hcov W hW, hLκ,
    ?_, ?_⟩
  · intro a ha b hb z
    refine Submodule.Quotient.induction_on (factorSub (Vs i.castSucc) (Vs i.succ)) z fun x => ?_
    have key : (Vs i.succ).toRepresentation b ((Vs i.succ).toRepresentation a x - x) =
        (Vs i.succ).toRepresentation a x - x := by
      apply Subtype.ext
      apply Subtype.ext
      exact quad_apply (ρ := ρ) hquad (Subgroup.mem_subgroupOf.mp ha)
        (Subgroup.mem_subgroupOf.mp hb) (x : ↥SU.toSubmodule).2
    rw [factorRep_mk, ← Submodule.Quotient.mk_sub, factorRep_mk, key]
  ·
    have h1 : factorCodim Vs BK i ≤ finrank (ZMod 2) ↥U - finrank (ZMod 2) ↥(fixOn ρ B U) := by
      have hsum := sum_factorCodim_le Vs (fun j => (hVs.covBy j).le) hVs.zero hVs.last BK
      rw [finrank_fixSub_subgroupOf le_sup_right SU] at hsum
      exact (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)).trans hsum
    have h2 := two_pow_mul_card_le hbest (D := cenOn ρ B U) le_rfl
    have h3 : 2 ^ (finrank (ZMod 2)
          (↥(Vs i.succ).toSubmodule ⧸ factorSub (Vs i.castSucc) (Vs i.succ)) -
        finrank (ZMod 2) ↥(fixSub (factorRep (Vs i.castSucc) (Vs i.succ)) BK)) *
        Nat.card ↥(cenOn ρ B U) ≤ Nat.card ↥B :=
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) h1)).trans h2
    have hmem : ∀ x : ↥(BK ⊓ MonoidHom.ker (factorRep (Vs i.castSucc) (Vs i.succ))),
        ((x : ↥(L ⊔ B)) : G) ∈ cenOn ρ B U := by
      intro x
      obtain ⟨hxB, hxk⟩ := x.2
      have hxB' : ((x : ↥(L ⊔ B)) : G) ∈ B := Subgroup.mem_subgroupOf.mp hxB
      have hxk' : factorRep (Vs i.castSucc) (Vs i.succ) (x : ↥(L ⊔ B)) = 1 := hxk
      have hcen : (x : ↥(L ⊔ B)) ∈ Subgroup.centralizer (LK : Set ↥(L ⊔ B)) := by
        refine hctx.centralizes_of_fix' (factorRep (Vs i.castSucc) (Vs i.succ)) ⊤
          (fun _ _ _ _ => Submodule.mem_top) ?_ ?_
        · obtain ⟨l, hl, z, hz⟩ := hLκ
          exact ⟨l, hl, z, Submodule.mem_top, hz⟩
        · intro y _
          rw [hxk']
          rfl
      refine mem_cenOn_of_commute hmove hxB' fun k hk => ?_
      have := (Subgroup.mem_centralizer_iff.mp hcen) ⟨k, Subgroup.mem_sup_left hk⟩
        (Subgroup.mem_subgroupOf.mpr hk)
      exact (congrArg Subtype.val this).symm
    have h5 : Nat.card ↥(BK ⊓ MonoidHom.ker (factorRep (Vs i.castSucc) (Vs i.succ))) ≤
        Nat.card ↥(cenOn ρ B U) :=
      Nat.card_le_card_of_injective (fun x => ⟨((x : ↥(L ⊔ B)) : G), hmem x⟩) fun x y hxy =>
        Subtype.ext (Subtype.ext (Subtype.mk.inj hxy))
    have h6 : Nat.card ↥BK = Nat.card ↥B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : B ≤ L ⊔ B)).toEquiv
    have h7 := card_mul_le_of_codim (factorRep (Vs i.castSucc) (Vs i.succ)) BK h3
    have h8 : Nat.card ↥(fixSub (factorRep (Vs i.castSucc) (Vs i.succ)) BK) =
        Nat.card {z : ↥(Vs i.succ).toSubmodule ⧸ factorSub (Vs i.castSucc) (Vs i.succ) //
          ∀ b ∈ BK, factorRep (Vs i.castSucc) (Vs i.succ) b z = z} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun z => mem_fixSub)
    have h9 := congrArg₂ (fun a b : ℕ => a * b) h6.symm h8
    exact (Nat.mul_le_mul_left _ h5).trans (h7.trans h9.le)

end Main

end CFSG.LocalAnalysis.RankThreeUC.S15
