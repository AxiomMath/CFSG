module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitTools
public import CFSG.LocalAnalysis.ComponentClassification.TBLitIntrinsicTypes

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint
open scoped commutatorElement Pointwise MatrixGroups

theorem map_center_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (center G).map e.toMonoidHom = center H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ center G := hx
    rw [mem_center_iff] at hx' ⊢
    intro h
    obtain ⟨g, rfl⟩ := e.surjective h
    change e g * e x = e x * e g
    rw [← map_mul, ← map_mul, hx' g]
  · intro hy
    refine ⟨e.symm y, show e.symm y ∈ center G from ?_, by simp⟩
    rw [mem_center_iff] at hy ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy (e g)]

theorem map_mem_center_of_surjective {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Surjective f) {z : G} (hz : z ∈ center G) : f z ∈ center H := by
  rw [mem_center_iff] at hz ⊢
  intro h
  obtain ⟨g, rfl⟩ := hf h
  rw [← map_mul, ← map_mul, hz g]

section Hom

variable {N R : Type*} [Group N] [Group R] [Finite N] [Finite R]

omit [Finite R] in
theorem map_pPrimeCore_le (f : N →* R) (hf : Function.Surjective f) :
    (pPrimeCore 2 N).map f ≤ pPrimeCore 2 R := by
  have hn : ((pPrimeCore 2 N).map f).Normal := (pPrimeCore_normal (p := 2) (G := N)).map f hf
  have hcop : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 N).map f)) :=
    Nat.Coprime.coprime_dvd_right (card_map_dvd (pPrimeCore 2 N) f) pPrimeCore_coprime_card
  exact le_sSup ⟨hn, hcop⟩

omit [Finite N] in
theorem comap_pPrimeCore_le_centralPreimage (f : N →* R) (hker : Group.IsSolvable f.ker)
    (hN : IsQuasisimple (N ⧸ pPrimeCore 2 N)) :
    (pPrimeCore 2 R).comap f ≤ UnbalancingLocal.centralPreimage (pPrimeCore 2 N) := by
  set P := (pPrimeCore 2 R).comap f with hP
  have hPn : P.Normal := (pPrimeCore_normal (p := 2) (G := R)).comap f
  have hO : Group.IsSolvable (pPrimeCore 2 R) :=
    Milestones.odd_order_solvable (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  have hPsolv : Group.IsSolvable P := by
    let g : P →* pPrimeCore 2 R := (f.comp P.subtype).codRestrict _ (fun x => x.2)
    have hkP : f.ker ≤ P := fun x hx => by
      change f x ∈ pPrimeCore 2 R
      rw [MonoidHom.mem_ker.mp hx]
      exact one_mem _
    refine Group.isSolvable_of_ker_le_range (inclusion hkP) g ?_
    intro x hx
    have hx1 : f x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact ⟨⟨x, MonoidHom.mem_ker.mpr hx1⟩, rfl⟩
  set q := QuotientGroup.mk' (pPrimeCore 2 N) with hq
  have hPbar : (P.map q).Normal := hPn.map q (QuotientGroup.mk'_surjective _)
  have hQ := CatalogueBAlternating.quasisimple_iff_native.mp hN
  rcases Quasisimple.normal_le_center_or_eq_top hQ (P.map q) with hc | htop
  · intro x hx
    exact hc (mem_map_of_mem q hx)
  · exfalso
    have : Nontrivial (N ⧸ pPrimeCore 2 N) := Quasisimple.nontrivial hQ
    have : Group.IsPerfect (N ⧸ pPrimeCore 2 N) := hN.1
    have hsurj : Function.Surjective (q.comp P.subtype) := by
      intro y
      obtain ⟨x, hx, rfl⟩ : y ∈ P.map q := htop ▸ mem_top y
      exact ⟨⟨x, hx⟩, rfl⟩
    have : Group.IsSolvable (N ⧸ pPrimeCore 2 N) := Group.isSolvable_of_surjective hsurj
    exact Group.IsPerfect.not_isSolvable _ this

theorem quotient_pPrimeCore_equiv_of_surjective {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) (e : N ⧸ pPrimeCore 2 N ≃* SL(2, F))
    (hN : IsQuasisimple (N ⧸ pPrimeCore 2 N)) (f : N →* R) (hf : Function.Surjective f)
    (hker : Group.IsSolvable f.ker) {δ : N} (hδ : δ ∈ center N)
    (hδ2 : orderOf δ = 2) :
    (f δ = 1 → Nonempty (R ⧸ pPrimeCore 2 R ≃* PSL(2, F))) ∧
      (f δ ≠ 1 → Nonempty (R ⧸ pPrimeCore 2 R ≃* SL(2, F))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := (pPrimeCore 2 R).comap f with hP
  have hPn : P.Normal := (pPrimeCore_normal (p := 2) (G := R)).comap f
  let φ : N →* R ⧸ pPrimeCore 2 R := (QuotientGroup.mk' (pPrimeCore 2 R)).comp f
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hf
  have hφker : φ.ker = P := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  let e₁ : N ⧸ P ≃* R ⧸ pPrimeCore 2 R :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  have hOP : pPrimeCore 2 N ≤ P := fun x hx => map_pPrimeCore_le f hf (mem_map_of_mem f hx)
  have hPZ := comap_pPrimeCore_le_centralPreimage f hker hN
  have hPbarn : (P.map (QuotientGroup.mk' (pPrimeCore 2 N))).Normal :=
    hPn.map _ (QuotientGroup.mk'_surjective _)
  have hPbarZ : P.map (QuotientGroup.mk' (pPrimeCore 2 N)) ≤ center (N ⧸ pPrimeCore 2 N) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hPZ hx
  let e₂ : (N ⧸ pPrimeCore 2 N) ⧸ P.map (QuotientGroup.mk' (pPrimeCore 2 N)) ≃* N ⧸ P :=
    QuotientGroup.quotientQuotientEquivQuotient (pPrimeCore 2 N) P hOP
  have hZcard : Nat.card (center (N ⧸ pPrimeCore 2 N)) = 2 := by
    have h1 : Nat.card ((center (N ⧸ pPrimeCore 2 N)).map e.toMonoidHom) =
        Nat.card (center (N ⧸ pPrimeCore 2 N)) := card_map_of_injective (by exact e.injective)
    rw [map_center_mulEquiv e] at h1
    rw [← h1]
    exact ABGLocalTools.card_center_sl2 hF
  have hqδ : ((δ : N) : N ⧸ pPrimeCore 2 N) ∈ center (N ⧸ pPrimeCore 2 N) :=
    map_mem_center_of_surjective (QuotientGroup.mk'_surjective (pPrimeCore 2 N)) hδ
  have hqδ1 : ((δ : N) : N ⧸ pPrimeCore 2 N) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact not_mem_pPrimeCore_of_orderOf_two hδ2
  have hcases : P.map (QuotientGroup.mk' (pPrimeCore 2 N)) = ⊥ ∨
      P.map (QuotientGroup.mk' (pPrimeCore 2 N)) = center (N ⧸ pPrimeCore 2 N) := by
    have hdvd : Nat.card (P.map (QuotientGroup.mk' (pPrimeCore 2 N))) ∣ 2 := by
      have h0 := card_dvd_of_le hPbarZ
      rwa [hZcard] at h0
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact Or.inl (card_eq_one.mp h1)
    · exact Or.inr (eq_of_le_of_card_ge hPbarZ (by rw [hZcard, h2]))
  constructor
  · intro hfδ
    have hδP : δ ∈ P := by
      change f δ ∈ pPrimeCore 2 R
      rw [hfδ]
      exact one_mem _
    have hPbar_eq : P.map (QuotientGroup.mk' (pPrimeCore 2 N)) = center (N ⧸ pPrimeCore 2 N) := by
      rcases hcases with h | h
      · exfalso
        apply hqδ1
        have h1 : QuotientGroup.mk' (pPrimeCore 2 N) δ ∈
            P.map (QuotientGroup.mk' (pPrimeCore 2 N)) := mem_map_of_mem _ hδP
        rw [h] at h1
        exact h1
      · exact h
    exact ⟨e₁.symm.trans (e₂.symm.trans ((QuotientGroup.quotientMulEquivOfEq hPbar_eq).trans
      (QuotientGroup.congr _ _ e (map_center_mulEquiv e))))⟩
  · intro hfδ
    have hδP : δ ∉ P := by
      intro h
      apply hfδ
      have h1 : orderOf (f δ) ∣ 2 := hδ2 ▸ orderOf_map_dvd f δ
      have h2 : orderOf (f δ) ∣ Nat.card (pPrimeCore 2 R) := by
        rw [← Subgroup.orderOf_mk (f δ) (show f δ ∈ pPrimeCore 2 R from h)]
        exact orderOf_dvd_natCard _
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left h1 pPrimeCore_coprime_card) h2)
    have hPbar_eq : P.map (QuotientGroup.mk' (pPrimeCore 2 N)) = ⊥ := by
      rcases hcases with h | h
      · exact h
      · exfalso
        apply hδP
        have h1 : QuotientGroup.mk' (pPrimeCore 2 N) δ ∈
            P.map (QuotientGroup.mk' (pPrimeCore 2 N)) := h ▸ hqδ
        obtain ⟨x, hx, hxδ⟩ := h1
        have h2 : x⁻¹ * δ ∈ pPrimeCore 2 N := by
          rw [← QuotientGroup.ker_mk' (pPrimeCore 2 N), MonoidHom.mem_ker, map_mul, map_inv,
            hxδ, inv_mul_cancel]
        have h3 := mul_mem hx (hOP h2)
        rwa [mul_inv_cancel_left] at h3
    exact ⟨e₁.symm.trans (e₂.symm.trans ((QuotientGroup.quotientMulEquivOfEq hPbar_eq).trans
      (QuotientGroup.quotientBot.trans e)))⟩

end Hom

section Map

variable {G B : Type*} [Group G] [Group B] [Finite B]

omit [Finite B] in
theorem isSolvable_ker_subgroupMap (π : G →* B) {M A : Subgroup G} (hA : Group.IsSolvable A)
    (hkerA : M ⊓ π.ker ≤ A) : Group.IsSolvable (π.subgroupMap M).ker := by
  let ι : (π.subgroupMap M).ker →* A :=
    { toFun := fun x => ⟨((x : M) : G), hkerA (mem_inf.mpr ⟨(x : M).2, MonoidHom.mem_ker.mpr
        (congrArg Subtype.val (MonoidHom.mem_ker.mp x.2))⟩)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := by
    intro x y h
    have h' := congrArg (Subtype.val : A → G) h
    exact Subtype.ext (Subtype.ext h')
  exact Group.isSolvable_of_isSolvable_injective hι

theorem forall_mem_oddCoreIn_of_map (π : G →* B) {M : Subgroup G}
    (hM : IsQuasisimple (M ⧸ pPrimeCore 2 M)) {A : Subgroup G} (hA : Group.IsSolvable A)
    (hkerA : M ⊓ π.ker ≤ A) {g : G} (hg : g ∈ normalizer (M : Set G))
    (h : ∀ r ∈ M.map π, ⁅r, π g⁆ ∈ oddCoreIn (M.map π)) : ∀ m ∈ M, ⁅m, g⁆ ∈ oddCoreIn M := by
  apply forall_mem_oddCoreIn_of_forall_mem_zStarIn hM hg
  intro m hm
  let f : M →* M.map π := π.subgroupMap M
  have hker : Group.IsSolvable f.ker := isSolvable_ker_subgroupMap π hA hkerA
  have hle := comap_pPrimeCore_le_centralPreimage f hker hM
  have hcM : ⁅m, g⁆ ∈ M := commutator_le_of_le_normalizer (zpowers_le.mpr hg)
    (commutator_mem_commutator hm (mem_zpowers g))
  obtain ⟨o, ho, hoeq⟩ := h (π m) (mem_map_of_mem π hm)
  have hfo : f ⟨⁅m, g⁆, hcM⟩ = o := by
    apply Subtype.ext
    change π ⁅m, g⁆ = (o : B)
    rw [map_commutatorElement]
    exact hoeq.symm
  have h1 : (⟨⁅m, g⁆, hcM⟩ : M) ∈ (pPrimeCore 2 (M.map π)).comap f := by
    change f ⟨⁅m, g⁆, hcM⟩ ∈ pPrimeCore 2 (M.map π)
    rw [hfo]
    exact ho
  exact ⟨⟨⁅m, g⁆, hcM⟩, hle h1, rfl⟩

theorem ActsProperly.map (π : G →* B) {t : G} {E M : Subgroup G}
    (h : ActsProperly t E M (oddCoreIn M)) (hM : IsQuasisimple (M ⧸ pPrimeCore 2 M))
    {A : Subgroup G} (hA : Group.IsSolvable A) (hkerA : M ⊓ π.ker ≤ A) :
    ActsProperly (π t) (E.map π) (M.map π) (oddCoreIn (M.map π)) := by
  obtain ⟨hnorm, htriv, e, he, m, hm, hnt⟩ := h
  have hcl : closure (insert (π t) ((E.map π : Subgroup B) : Set B)) =
      (closure (insert t (E : Set G))).map π := by
    rw [MonoidHom.map_closure, Set.image_insert_eq, coe_map]
  have hnormM : ∀ g ∈ closure (insert t (E : Set G)),
      π g ∈ normalizer ((M.map π : Subgroup B) : Set B) :=
    fun g hg => le_normalizer_map π ⟨g, (hnorm hg).1, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hcl]
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨hnormM g hg, normalizer_le_normalizer_oddCoreIn _ (hnormM g hg)⟩
  · rw [hcl]
    rintro _ ⟨g, hg, rfl⟩ hg'
    exact mem_map_of_mem π
      (htriv g hg (forall_mem_oddCoreIn_of_map π hM hA hkerA (hnorm hg).1 hg'))
  · have heN : e ∈ normalizer (M : Set G) :=
      (hnorm (subset_closure (Set.mem_insert_of_mem t he))).1
    by_contra hall
    apply hnt
    refine forall_mem_oddCoreIn_of_map π hM hA hkerA heN (fun r hr => ?_) m hm
    by_contra hr'
    exact hall ⟨π e, mem_map_of_mem π he, r, hr, hr'⟩

end Map

end CFSG.ComponentClassification.TBLit
