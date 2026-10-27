module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Basic
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TwelveTwoAux1

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


namespace E8TwoD

section Descent

variable {τ : Tag} {K L : Type} [Field K] [Field L] [Algebra K L]

theorem fixedFieldImage_eq_map (σ : L ≃+* L) (hσ : ∀ c : L, σ c = c → c = 0 ∨ c = 1)
    (hK : ∀ s : K, s = 0 ∨ s = 1) :
    fixedFieldImage τ σ = (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
  rw [fixedFieldImage_eq_closure, map_baseChangeGL_adjointGroup]
  congr 1
  ext g
  constructor
  · rintro ⟨i, c, hc, h | h⟩
    · rcases hσ c hc with rfl | rfl
      · exact ⟨i, 0, Or.inl (by rw [h, map_zero])⟩
      · exact ⟨i, 1, Or.inl (by rw [h, map_one])⟩
    · rcases hσ c hc with rfl | rfl
      · exact ⟨i, 0, Or.inr (by rw [h, map_zero])⟩
      · exact ⟨i, 1, Or.inr (by rw [h, map_one])⟩
  · rintro ⟨i, c, h | h⟩
    · refine ⟨i, algebraMap K L c, ?_, Or.inl h⟩
      rcases hK c with rfl | rfl <;> simp
    · refine ⟨i, algebraMap K L c, ?_, Or.inr h⟩
      rcases hK c with rfl | rfl <;> simp

theorem exists_baseChange_of_fixed (σ : L ≃+* L) (hσ : ∀ c : L, σ c = c → c = 0 ∨ c = 1)
    (hK : ∀ s : K, s = 0 ∨ s = 1) {y : ModGL τ L} (hy : y ∈ adjointGroup τ L)
    (hfix : Units.map (entrywiseHom σ.toRingHom) y = y) :
    ∃ x ∈ adjointGroup τ K, baseChangeGL (algebraMap K L) x = y := by
  have hΓ : y ∈ entrywiseFixedGroup τ σ := mem_entrywiseFixedGroup.2 ⟨hy, hfix⟩
  obtain ⟨h, hh, j, hj, hyj⟩ := Set.mem_mul.1 (mem_mul_of_mem_entrywiseFixedGroup hΓ)
  have h1 : h = 1 := by
    obtain ⟨hT, -, hF⟩ := hh
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
    have hF' : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit τ a) = rootDiagUnit τ a := hF
    have h0 : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit τ a) =
        rootDiagUnit τ (fun i => Units.map σ.toRingHom.toMonoidHom (a i)) :=
      Units.ext (entrywise_rootDiag σ.toRingHom a)
    have h1 : rootDiagUnit τ (fun i => Units.map σ.toRingHom.toMonoidHom (a i)) =
        rootDiagUnit τ a := h0.symm.trans hF'
    have hσa : ∀ i, σ (a i : L) = a i := fun i =>
      congrArg Units.val (congrFun (rootDiagUnit_injective h1) i)
    have ha1 : a = 1 := by
      funext i
      rcases hσ _ (hσa i) with h | h
      · exact absurd h (a i).ne_zero
      · exact Units.ext h
    rw [ha1]
    exact Units.ext rootDiag_one
  rw [h1, one_mul] at hyj
  subst hyj
  rw [fixedFieldImage_eq_map σ hσ hK] at hj
  obtain ⟨x, hx, hxj⟩ := hj
  exact ⟨x, hx, hxj⟩

theorem mem_Qθ_of_baseChange_mem (σ : L ≃+* L) (hσ : ∀ c : L, σ c = c → c = 0 ∨ c = 1)
    (hK : ∀ s : K, s = 0 ∨ s = 1) {z : ModGL τ K} (hz : z ∈ adjointGroup τ K)
    (hQ : baseChangeGL (algebraMap K L) z ∈ Qθ τ L) : z ∈ Qθ τ K := by
  classical
  have hfix : Units.map (entrywiseHom σ.toRingHom) (baseChangeGL (algebraMap K L) z) =
      baseChangeGL (algebraMap K L) z := by
    have hmem : baseChangeGL (algebraMap K L) z ∈ fixedFieldImage τ σ := by
      rw [fixedFieldImage_eq_map σ hσ hK]
      exact ⟨z, hz, rfl⟩
    exact (fixedFieldImage_le hmem).2
  set S := parabolicRadicalRoots τ (Jθ τ) with hSdef
  have hSfin : S.Finite := (finite_setOf_isRoot τ).subset fun β hβ => hβ.1.1
  haveI : Finite S := hSfin.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  set α : Fin n → Fin τ.rank → ℤ := fun k => (e.symm k : Fin τ.rank → ℤ) with hαdef
  have hα : Function.Injective α := fun k k' h => e.symm.injective (Subtype.ext h)
  have hrange : Set.range α = S := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact (e.symm k).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [α]⟩
  have hbij := (positive_root_collection τ L).1 S (fun β hβ => parabolicRadicalRoots_pos hβ)
    (fun _ hα _ hβ _ _ ha hb hr =>
      add_mem_parabolicRadicalRoots (parabolicRadicalRoots_pos hα) hβ ha hb hr) α hα hrange
  obtain ⟨d, -, hd⟩ := hbij.2.2 hQ
  have hd' : (List.ofFn fun k => pinnedX τ L (α k) (d k)).prod =
      baseChangeGL (algebraMap K L) z := hd
  have hmap : Units.map (entrywiseHom σ.toRingHom)
      ((List.ofFn fun k => pinnedX τ L (α k) (d k)).prod) =
        (List.ofFn fun k => pinnedX τ L (α k) (σ (d k))).prod := by
    rw [map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    refine Units.ext ?_
    rw [Function.comp_apply, Units.coe_map]
    exact entrywise_pinnedX σ.toRingHom (α k) (d k)
  have hdfix : (fun k => σ (d k)) = d := by
    refine hbij.2.1 (Set.mem_univ _) (Set.mem_univ _) ?_
    show (List.ofFn fun k => pinnedX τ L (α k) (σ (d k))).prod =
      (List.ofFn fun k => pinnedX τ L (α k) (d k)).prod
    rw [← hmap, hd', hfix]
  have hdK : ∀ k, ∃ s : K, algebraMap K L s = d k := by
    intro k
    rcases hσ (d k) (congrFun hdfix k) with h | h
    · exact ⟨0, by rw [h, map_zero]⟩
    · exact ⟨1, by rw [h, map_one]⟩
  choose c hc using hdK
  have hzprod : baseChangeGL (algebraMap K L) z =
      baseChangeGL (algebraMap K L) ((List.ofFn fun k => pinnedX τ K (α k) (c k)).prod) := by
    rw [← hd', map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    rw [Function.comp_apply, baseChangeGL_pinnedX, hc]
  rw [baseChangeGL_injective _ hzprod]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  exact pinnedX_mem_rootSpan (show α k ∈ S from (e.symm k).2) (c k)

end Descent


section Roots

abbrev ρ₂ : Fin Tag.E8.rank → ℤ := reflect Tag.E8 (iθ Tag.E8) (highRoot Tag.E8)

theorem ρ₂_deg : ρ₂ (iθ Tag.E8) = 1 := by decide +kernel

theorem root_facts :
    (ρ₂ ∈ rootFinset Tag.E8) ∧ ((ρ₂ + -highRoot Tag.E8) ∈ rootFinset Tag.E8) ∧
    ((-Pi.single (iθ Tag.E8) 1 : Fin Tag.E8.rank → ℤ) ∈ rootFinset Tag.E8) ∧
    ((-Pi.single (iθ Tag.E8) 1 + ρ₂ : Fin Tag.E8.rank → ℤ) ∉ rootFinset Tag.E8) ∧
    ((-Pi.single (iθ Tag.E8) 1 + -highRoot Tag.E8 : Fin Tag.E8.rank → ℤ) ∉ rootFinset Tag.E8) := by
  decide +kernel

theorem ne_facts :
    (ρ₂ ≠ -highRoot Tag.E8) ∧ (ρ₂ ≠ highRoot Tag.E8) ∧
    ((-Pi.single (iθ Tag.E8) 1 : Fin Tag.E8.rank → ℤ) ≠ ρ₂) ∧
    ((-Pi.single (iθ Tag.E8) 1 : Fin Tag.E8.rank → ℤ) ≠ -ρ₂) ∧
    ((-Pi.single (iθ Tag.E8) 1 : Fin Tag.E8.rank → ℤ) ≠ -highRoot Tag.E8) ∧
    ((-Pi.single (iθ Tag.E8) 1 : Fin Tag.E8.rank → ℤ) ≠ highRoot Tag.E8) := by
  decide +kernel

theorem sum_eq : ρ₂ + -highRoot Tag.E8 = -(Pi.single (iθ Tag.E8) 1 : Fin Tag.E8.rank → ℤ) := by
  decide +kernel

end Roots

section Main

variable {K : Type} [Field K] [Finite K]

theorem eq_one_of_mul_self_eq_one {R : Type} [Field R] [CharP R 2] {ε : R} (h : ε * ε = 1) :
    ε = 1 :=
  CharTwo.sq_injective (show ε ^ 2 = 1 ^ 2 by rw [one_pow, sq, h])

theorem pinnedX_eq_one_iff {τ : Tag} {R : Type} [Field R] (α : Fin τ.rank → ℤ) (c : R) :
    pinnedX τ R α c = 1 ↔ c = 0 :=
  ⟨fun h => pinnedX_injective τ R α (h.trans (pinnedX_zero τ R α).symm), fun h => by
    rw [h, pinnedX_zero]⟩

end Main

section Main2

variable {K : Type} [Field K] [Finite K]

theorem exists_goodC {w : WeylGroup Tag.E8} (D : LangLevi Tag.E8 K w) (hK : Nat.card K = 2)
    (hwj : w • (Pi.single (iθ Tag.E8) 1 : Fin Tag.E8.rank → ℤ) = Pi.single (iθ Tag.E8) 1)
    {S : Set (Fin Tag.E8.rank → ℤ)}
    (hSp : (Pi.single (iθ Tag.E8) 1 : Fin Tag.E8.rank → ℤ) ∈ S)
    (hSm : (-Pi.single (iθ Tag.E8) 1 : Fin Tag.E8.rank → ℤ) ∈ S) :
    E8Two.GoodC (D.frame S) := by
  classical
  have hK2 : ∀ s : K, s = 0 ∨ s = 1 := E8Two.eq_zero_or_one_of_card_two hK
  haveI hcK : CharP K 2 := E8Two.charP_two_of_card_two hK
  haveI hcL : CharP D.L 2 := charP_of_injective_algebraMap (algebraMap K D.L).injective 2
  haveI hAC : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  have hFr2 : ∀ c : D.L, D.Fr c = c ^ 2 := fun c => by rw [D.hFr, hK]
  have hbij : Function.Bijective D.Fr := by
    refine ⟨D.Fr.injective, fun a => ?_⟩
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a (by norm_num : 0 < 2)
    exact ⟨b, by rw [hFr2, hb]⟩
  let σ : D.L ≃+* D.L := RingEquiv.ofBijective D.Fr hbij
  have hσc : σ.toRingHom = D.Fr := by ext x; rfl
  have hσ : ∀ c : D.L, σ c = c → c = 0 ∨ c = 1 := by
    intro c hc
    have h2 : c ^ 2 = c := by rw [← hFr2]; exact hc
    have h3 : c * (c - 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  set j : Fin Tag.E8.rank := iθ Tag.E8 with hj
  set e : Fin Tag.E8.rank → ℤ := Pi.single j 1 with he
  have heR : IsRoot Tag.E8 e := isRoot_single Tag.E8 j
  have hneR : IsRoot Tag.E8 (-e) := isRoot_neg_single Tag.E8 j
  have hθR : IsRoot Tag.E8 (highRoot Tag.E8) := isRoot_highRoot Tag.E8
  have hnθR : IsRoot Tag.E8 (-highRoot Tag.E8) := isRoot_neg_highRoot Tag.E8
  obtain ⟨hρ₂m, hsummem, hnem, hnot1m, hnot2m⟩ := root_facts
  have hρ₂R : IsRoot Tag.E8 ρ₂ := mem_rootFinset.1 hρ₂m
  have hsumR : IsRoot Tag.E8 (ρ₂ + -highRoot Tag.E8) := mem_rootFinset.1 hsummem
  have hnot1 : ¬ IsRoot Tag.E8 (-e + ρ₂) := fun h => hnot1m (mem_rootFinset.2 h)
  have hnot2 : ¬ IsRoot Tag.E8 (-e + -highRoot Tag.E8) := fun h => hnot2m (mem_rootFinset.2 h)
  obtain ⟨hne1, hne2, hne3, hne4, hne5, hne6⟩ := ne_facts
  have hρ₂Deg : ρ₂ ∈ Deg1 Tag.E8 := CoordAux.mem_Deg1.2 ⟨hρ₂R, ρ₂_deg⟩
  have hτE8 : Tag.E8 = Tag.D4 ∨ Tag.E8 = Tag.E6 ∨ Tag.E8 = Tag.E7 ∨ Tag.E8 = Tag.E8 :=
    Or.inr (Or.inr (Or.inr rfl))
  set u : ModGL Tag.E8 D.L := weylElt Tag.E8 D.L j 1 with hu
  have hu_eq : u = pinnedX Tag.E8 D.L e 1 * pinnedX Tag.E8 D.L (-e) (-1) *
      pinnedX Tag.E8 D.L e 1 := by
    rw [hu, CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
    simp only [inv_one, Units.val_one]
    rw [← pinnedX_single, ← pinnedX_neg_single]
  have hN : canonicalRep (coxeterSystem Tag.E8) D.L w * u *
      (canonicalRep (coxeterSystem Tag.E8) D.L w)⁻¹ = u := by
    obtain ⟨ε, hε, hconj⟩ := exists_canonicalRep_mul_pinnedX_mul_inv D.L w heR
    obtain ⟨ε', hε', hconj'⟩ := exists_canonicalRep_mul_pinnedX_mul_inv D.L w hneR
    have h1 : ε = 1 := eq_one_of_mul_self_eq_one hε
    have h1' : ε' = 1 := eq_one_of_mul_self_eq_one hε'
    have hwne : w • (-e) = -e := by rw [smul_neg, hwj]
    set n := canonicalRep (coxeterSystem Tag.E8) D.L w with hn
    calc n * u * n⁻¹ = (n * pinnedX Tag.E8 D.L e 1 * n⁻¹) *
          (n * pinnedX Tag.E8 D.L (-e) (-1) * n⁻¹) * (n * pinnedX Tag.E8 D.L e 1 * n⁻¹) := by
          rw [hu_eq]; group
      _ = u := by
          rw [hconj 1, hconj' (-1), hwj, hwne, h1, h1', one_mul, one_mul, hu_eq]
  set g := D.g with hg
  have hgG : g ∈ adjointGroup Tag.E8 D.L :=
    parabolicLevi_le_adjointGroup Tag.E8 D.L (Jθ Tag.E8) D.g_mem
  have huG : u ∈ adjointGroup Tag.E8 D.L := weylElt_mem_adjointGroup j 1
  set y : ModGL Tag.E8 D.L := g * u * g⁻¹ with hy
  have hyG : y ∈ adjointGroup Tag.E8 D.L := mul_mem (mul_mem hgG huG) (inv_mem hgG)
  have hFu : Units.map (entrywiseHom σ.toRingHom) u = u := entrywise_weylElt_one σ j
  have hyF : Units.map (entrywiseHom σ.toRingHom) y = y := by
    have hlang := D.lang
    rw [← hσc] at hlang
    rw [hy, map_mul, map_mul, map_inv, hlang, hFu]
    calc g * canonicalRep (coxeterSystem Tag.E8) D.L w * u *
          (g * canonicalRep (coxeterSystem Tag.E8) D.L w)⁻¹
        = g * (canonicalRep (coxeterSystem Tag.E8) D.L w * u *
          (canonicalRep (coxeterSystem Tag.E8) D.L w)⁻¹) * g⁻¹ := by group
      _ = g * u * g⁻¹ := by rw [hN]
  obtain ⟨x₀, hx₀G, hx₀y⟩ := E8TwoD.exists_baseChange_of_fixed σ hσ hK2 hyG hyF
  have hrS : u ∈ rootSpan Tag.E8 D.L S := by
    rw [hu_eq]
    exact mul_mem (mul_mem (pinnedX_mem_rootSpan hSp 1) (pinnedX_mem_rootSpan hSm (-1)))
      (pinnedX_mem_rootSpan hSp 1)
  have hx₀X : x₀ ∈ D.frame S := by
    refine (TwBasicAux.mem_frame_iff D S x₀).2 ⟨hx₀G, ?_⟩
    rw [hx₀y, hy]
    have : g⁻¹ * (g * u * g⁻¹) * g = u := by group
    rw [this]
    exact hrS
  have hconjθ : ∀ t : D.L, ∃ t' : D.L, y * pinnedX Tag.E8 D.L (highRoot Tag.E8) t * y⁻¹ =
      g * pinnedX Tag.E8 D.L ρ₂ t' * g⁻¹ ∧ (t ≠ 0 → t' ≠ 0) := by
    intro t
    have hz : g⁻¹ * pinnedX Tag.E8 D.L (highRoot Tag.E8) t * g ∈ Uθ Tag.E8 D.L := by
      have := Lθ_conj_mem_Uθ (inv_mem D.g_mem)
        (mem_rootSubgroup.2 ⟨t, rfl⟩ : pinnedX Tag.E8 D.L (highRoot Tag.E8) t ∈ Uθ Tag.E8 D.L)
      simpa using this
    obtain ⟨t₁, ht₁⟩ := mem_rootSubgroup.1 hz
    have hu_conj : u * pinnedX Tag.E8 D.L (highRoot Tag.E8) t₁ * u⁻¹ ∈
        rootSubgroup Tag.E8 D.L ρ₂ := by
      have h := map_conj_weylElt_rootSubgroup D.L j hθR
      change _ ∈ rootSubgroup Tag.E8 D.L (reflect Tag.E8 j (highRoot Tag.E8))
      rw [← h]
      exact ⟨pinnedX Tag.E8 D.L (highRoot Tag.E8) t₁, mem_rootSubgroup.2 ⟨t₁, rfl⟩, by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rfl⟩
    obtain ⟨t', ht'⟩ := mem_rootSubgroup.1 hu_conj
    refine ⟨t', ?_, fun ht0 ht'0 => ?_⟩
    · calc y * pinnedX Tag.E8 D.L (highRoot Tag.E8) t * y⁻¹
          = g * (u * (g⁻¹ * pinnedX Tag.E8 D.L (highRoot Tag.E8) t * g) * u⁻¹) * g⁻¹ := by
            rw [hy]; group
        _ = g * pinnedX Tag.E8 D.L ρ₂ t' * g⁻¹ := by rw [← ht₁, ← ht']
    · apply ht0
      rw [ht'0, pinnedX_zero] at ht'
      have h1 : pinnedX Tag.E8 D.L (highRoot Tag.E8) t₁ = 1 := by
        calc pinnedX Tag.E8 D.L (highRoot Tag.E8) t₁
            = u⁻¹ * (u * pinnedX Tag.E8 D.L (highRoot Tag.E8) t₁ * u⁻¹) * u := by group
          _ = 1 := by rw [← ht']; group
      have ht10 : t₁ = 0 := (pinnedX_eq_one_iff _ _).1 h1
      rw [ht10, pinnedX_zero] at ht₁
      apply (pinnedX_eq_one_iff (τ := Tag.E8) (highRoot Tag.E8) t).1
      calc pinnedX Tag.E8 D.L (highRoot Tag.E8) t
          = g * (g⁻¹ * pinnedX Tag.E8 D.L (highRoot Tag.E8) t * g) * g⁻¹ := by group
        _ = 1 := by rw [← ht₁]; group
  have hcmem : ∀ c ∈ conjSub x₀ (Uθ Tag.E8 K), ∃ s : K,
      c = x₀ * pinnedX Tag.E8 K (highRoot Tag.E8) s * x₀⁻¹ := by
    intro c hc
    obtain ⟨s, hs⟩ := mem_rootSubgroup.1 (mem_conjSub_iff.1 hc)
    exact ⟨s, by rw [hs]; group⟩
  have hbc : ∀ s : K, baseChangeGL (algebraMap K D.L)
      (x₀ * pinnedX Tag.E8 K (highRoot Tag.E8) s * x₀⁻¹) =
      y * pinnedX Tag.E8 D.L (highRoot Tag.E8) (algebraMap K D.L s) * y⁻¹ := by
    intro s
    rw [map_mul, map_mul, map_inv, hx₀y, baseChangeGL_pinnedX]
  have hQ : conjSub x₀ (Uθ Tag.E8 K) ≤ Qθ Tag.E8 K := by
    intro c hc
    obtain ⟨s, rfl⟩ := hcmem c hc
    have hcG : x₀ * pinnedX Tag.E8 K (highRoot Tag.E8) s * x₀⁻¹ ∈ adjointGroup Tag.E8 K :=
      mul_mem (mul_mem hx₀G (pinnedX_mem_adjointGroup _ _)) (inv_mem hx₀G)
    refine mem_Qθ_of_baseChange_mem σ hσ hK2 hcG ?_
    rw [hbc]
    obtain ⟨t', ht', -⟩ := hconjθ (algebraMap K D.L s)
    rw [ht']
    exact Lθ_conj_mem_Qθ D.g_mem (pinnedX_mem_Qθ_of_mem_Deg1 hρ₂Deg t')
  obtain ⟨t', ht'c, ht'ne⟩ := hconjθ 1
  have ht'0 : t' ≠ 0 := ht'ne one_ne_zero
  have hnegθ : ∃ t₀ : D.L, t₀ ≠ 0 ∧ pinnedX Tag.E8 D.L (-highRoot Tag.E8) 1 =
      g * pinnedX Tag.E8 D.L (-highRoot Tag.E8) t₀ * g⁻¹ := by
    have hmem : pinnedX Tag.E8 D.L (-highRoot Tag.E8) 1 ∈ Heis.Uneg Tag.E8 D.L :=
      mem_rootSubgroup.2 ⟨1, rfl⟩
    have hz : g⁻¹ * pinnedX Tag.E8 D.L (-highRoot Tag.E8) 1 * g ∈ Heis.Uneg Tag.E8 D.L := by
      have hnorm := Lθ_le_normalizer_Uneg Tag.E8 D.L (inv_mem D.g_mem)
      have := (Subgroup.mem_normalizer_iff.1 hnorm _).1 hmem
      simpa using this
    obtain ⟨t₀, ht₀⟩ := mem_rootSubgroup.1 hz
    refine ⟨t₀, ?_, ?_⟩
    · intro h0
      rw [h0, pinnedX_zero] at ht₀
      have : pinnedX Tag.E8 D.L (-highRoot Tag.E8) 1 = 1 := by
        calc pinnedX Tag.E8 D.L (-highRoot Tag.E8) 1
            = g * (g⁻¹ * pinnedX Tag.E8 D.L (-highRoot Tag.E8) 1 * g) * g⁻¹ := by group
          _ = 1 := by rw [← ht₀]; group
      exact one_ne_zero ((pinnedX_eq_one_iff _ _).1 this)
    · calc pinnedX Tag.E8 D.L (-highRoot Tag.E8) 1
          = g * (g⁻¹ * pinnedX Tag.E8 D.L (-highRoot Tag.E8) 1 * g) * g⁻¹ := by group
        _ = g * pinnedX Tag.E8 D.L (-highRoot Tag.E8) t₀ * g⁻¹ := by rw [← ht₀]
  obtain ⟨t₀, ht₀0, ht₀c⟩ := hnegθ
  set A := pinnedX Tag.E8 D.L ρ₂ t' with hA
  set B := pinnedX Tag.E8 D.L (-highRoot Tag.E8) t₀ with hB
  have hne2' : ρ₂ ≠ - -highRoot Tag.E8 := by rwa [neg_neg]
  have hne6' : (-e : Fin Tag.E8.rank → ℤ) ≠ - -highRoot Tag.E8 := by rwa [neg_neg]
  obtain ⟨hAB1, -⟩ := simply_laced_root_commutator_unit.{0} Tag.E8 hτE8 hρ₂R hnθR hne1 hne2'
  obtain ⟨hNunit, hbr⟩ := hAB1 hsumR
  have hbr' := hbr D.L t' t₀
  rw [sum_eq] at hbr'
  have hN0 : ((commConst Tag.E8 ρ₂ (-highRoot Tag.E8) (1, 1) : ℤ) : D.L) ≠ 0 := by
    rcases hNunit with h | h <;> simp [h]
  set Dd := pinnedX Tag.E8 D.L (-e)
    (((commConst Tag.E8 ρ₂ (-highRoot Tag.E8) (1, 1) : ℤ) : D.L) * t' * t₀) with hDd
  have hDA : Commute Dd A :=
    (simply_laced_root_commutator_unit.{0} Tag.E8 hτE8 hneR hρ₂R hne3 hne4).2 hnot1 D.L Dd
      (mem_rootSubgroup.2 ⟨_, rfl⟩) A (mem_rootSubgroup.2 ⟨_, rfl⟩)
  have hDB : Commute Dd B :=
    (simply_laced_root_commutator_unit.{0} Tag.E8 hτE8 hneR hnθR hne5 hne6').2 hnot2 D.L Dd
      (mem_rootSubgroup.2 ⟨_, rfl⟩) B (mem_rootSubgroup.2 ⟨_, rfl⟩)
  have hA2 : A * A = 1 := by
    rw [hA, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
  have hB2 : B * B = 1 := by
    rw [hB, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
  have hD2 : Dd * Dd = 1 := by
    rw [hDd, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
  have hAinv : A⁻¹ = A := inv_eq_of_mul_eq_one_right hA2
  have hBinv : B⁻¹ = B := inv_eq_of_mul_eq_one_right hB2
  have hABcomm : A * B * A⁻¹ * B⁻¹ = Dd := by
    have h1 := hbr D.L t' t₀
    rw [sum_eq, commutatorElement_def] at h1
    exact h1
  have hABsq : (A * B) ^ 2 = Dd := by
    calc (A * B) ^ 2 = A * B * A * B := by rw [sq]; group
      _ = A * B * A⁻¹ * B⁻¹ := by rw [hAinv, hBinv]
      _ = Dd := hABcomm
  have hA4 : A ^ 4 = 1 := by
    have h2 : A ^ 2 = 1 := by rw [sq]; exact hA2
    calc A ^ 4 = (A ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [h2, one_pow]
  have hB4 : B ^ 4 = 1 := by
    have h2 : B ^ 2 = 1 := by rw [sq]; exact hB2
    calc B ^ 4 = (B ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [h2, one_pow]
  have hAB4 : (A * B) ^ 4 = 1 := by
    calc (A * B) ^ 4 = ((A * B) ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [hABsq, sq, hD2]
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ModGL Tag.E8 K,
      c₁ = x₀ * pinnedX Tag.E8 K (highRoot Tag.E8) 1 * x₀⁻¹ := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a' : ModGL Tag.E8 K, a' = pinnedX Tag.E8 K (-highRoot Tag.E8) 1 :=
    ⟨_, rfl⟩
  have hc₁L : baseChangeGL (algebraMap K D.L) c₁ = g * A * g⁻¹ := by
    rw [hc₁, hbc, map_one, ht'c]
  have ha'L : baseChangeGL (algebraMap K D.L) a' = g * B * g⁻¹ := by
    rw [ha', baseChangeGL_pinnedX, map_one, ht₀c]
  have hconj4 : ∀ z : ModGL Tag.E8 D.L, z ^ 4 = 1 → (g * z * g⁻¹) ^ 4 = 1 := by
    intro z hz
    rw [conj_pow, hz]
    group
  have hc₁4 : c₁ ^ 4 = 1 := by
    apply baseChangeGL_injective (algebraMap K D.L)
    rw [map_pow, hc₁L, hconj4 A hA4, map_one]
  have ha'4 : a' ^ 4 = 1 := by
    apply baseChangeGL_injective (algebraMap K D.L)
    rw [map_pow, ha'L, hconj4 B hB4, map_one]
  have hca4 : (c₁ * a') ^ 4 = 1 := by
    apply baseChangeGL_injective (algebraMap K D.L)
    rw [map_pow, map_mul, hc₁L, ha'L]
    have : g * A * g⁻¹ * (g * B * g⁻¹) = g * (A * B) * g⁻¹ := by group
    rw [this, hconj4 _ hAB4, map_one]
  have hnc : c₁ * a' ≠ a' * c₁ := by
    intro h
    have h1 := congrArg (baseChangeGL (algebraMap K D.L)) h
    rw [map_mul, map_mul, hc₁L, ha'L] at h1
    have h2 : A * B = B * A := by
      have : g * (A * B) * g⁻¹ = g * (B * A) * g⁻¹ := by
        calc g * (A * B) * g⁻¹ = g * A * g⁻¹ * (g * B * g⁻¹) := by group
          _ = g * B * g⁻¹ * (g * A * g⁻¹) := h1
          _ = g * (B * A) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel this)
    have h3 : Dd = 1 := by
      rw [← hABcomm, hAinv, hBinv]
      calc A * B * A * B = A * (B * A) * B := by group
        _ = A * (A * B) * B := by rw [← h2]
        _ = (A * A) * (B * B) := by group
        _ = 1 := by rw [hA2, hB2, one_mul]
    have h4 := (pinnedX_eq_one_iff _ _).1 h3
    exact mul_ne_zero (mul_ne_zero hN0 ht'0) ht₀0 h4
  have hc₁mem : c₁ ∈ conjSub x₀ (Uθ Tag.E8 K) := by
    rw [mem_conjSub_iff]
    have : x₀⁻¹ * c₁ * x₀ = pinnedX Tag.E8 K (highRoot Tag.E8) 1 := by rw [hc₁]; group
    rw [this]
    exact mem_rootSubgroup.2 ⟨1, rfl⟩
  have ha'mem : a' ∈ Heis.Uneg Tag.E8 K := by rw [ha']; exact mem_rootSubgroup.2 ⟨1, rfl⟩
  refine ⟨x₀, hx₀X, hQ, ?_, c₁, hc₁mem, a', ha'mem, hnc⟩
  intro c hc a ha
  have hcc : c = 1 ∨ c = c₁ := by
    obtain ⟨s, hs⟩ := hcmem c hc
    rcases hK2 s with h | h
    · left
      rw [hs, h, pinnedX_zero]
      group
    · right
      rw [hs, h]
      exact hc₁.symm
  have haa : a = 1 ∨ a = a' := by
    obtain ⟨s, hs⟩ := mem_rootSubgroup.1 ha
    rcases hK2 s with h | h
    · left
      rw [← hs, h, pinnedX_zero]
    · right
      rw [← hs, h, ha']
  rcases hcc with h | h <;> rcases haa with h' | h'
  · rw [h, h', one_mul]; exact one_pow 4
  · rw [h, h', one_mul]; exact ha'4
  · rw [h, h', mul_one]; exact hc₁4
  · rw [h, h']; exact hca4

end Main2

end E8TwoD

namespace E8TwoL

theorem w_single : TwClass.e8Twelve.w •
    (Pi.single (iθ TwClass.e8Twelve.tag) 1 : Fin TwClass.e8Twelve.tag.rank → ℤ) =
    Pi.single (iθ TwClass.e8Twelve.tag) 1 := by
  change (coxeterSystem Tag.E8).wordProd TwClass.wordE8Twelve •
    (Pi.single (iθ Tag.E8) 1 : Fin Tag.E8.rank → ℤ) = Pi.single (iθ Tag.E8) 1
  rw [CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec]
  decide +kernel

theorem iform_single_J₂ : ∀ j : Fin TwClass.e8Twelve.tag.rank, j.val ∈ TwClass.e8Twelve.J₂ →
    CFSG.LieType.Steinberg.Adjoint.iform
      (Pi.single (iθ TwClass.e8Twelve.tag) 1 : Fin TwClass.e8Twelve.tag.rank → ℤ)
      (Pi.single j 1) = 0 := by
  decide +kernel

theorem iform_single_eq_zero_of_mem_S₂ {α : Fin TwClass.e8Twelve.tag.rank → ℤ}
    (hα : α ∈ TwClass.e8Twelve.S₂) :
    CFSG.LieType.Steinberg.Adjoint.iform
      (Pi.single (iθ TwClass.e8Twelve.tag) 1 : Fin TwClass.e8Twelve.tag.rank → ℤ) α = 0 := by
  rw [Heis.iform_eq_sum_single]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j.val ∈ TwClass.e8Twelve.J₂
  · rw [iform_single_J₂ j hj, zero_mul]
  · rw [hα.2 j hj, mul_zero]

theorem single_mem_S₁ :
    (Pi.single (iθ TwClass.e8Twelve.tag) 1 : Fin TwClass.e8Twelve.tag.rank → ℤ) ∈
      TwClass.e8Twelve.S₁ :=
  ⟨isRoot_single TwClass.e8Twelve.tag (iθ TwClass.e8Twelve.tag),
    fun _ hα => iform_single_eq_zero_of_mem_S₂ hα⟩

theorem neg_single_mem_S₁ :
    (-Pi.single (iθ TwClass.e8Twelve.tag) 1 : Fin TwClass.e8Twelve.tag.rank → ℤ) ∈
      TwClass.e8Twelve.S₁ :=
  ⟨isRoot_neg_single TwClass.e8Twelve.tag (iθ TwClass.e8Twelve.tag), fun _ hα => by
    rw [iform_neg_left, iform_single_eq_zero_of_mem_S₂ hα, neg_zero]⟩

end E8TwoL

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
