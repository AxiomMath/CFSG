module

public import CFSG.Fischer.Classification.PartIII.R3.MuSets
public import CFSG.Fischer.Classification.Uniqueness.Principle
public import CFSG.Fischer.Classification.Skeleton

public section

namespace CFSG.Fischer.Classification.LocalR3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification F3

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem isIsoPt_cons_zero {z : Fin m → ZMod 3} (hz0 : z ≠ 0) (hzz : f z z = 0) :
    IsIsoPt (extendForm f) (Pi.single 0 1) (Fin.cons 0 z) := by
  refine ⟨fun h => hz0 ?_, ?_, ?_⟩
  · have := congrArg Fin.tail h
    rwa [Fin.tail_cons] at this
  · rw [extendForm_apply, Fin.cons_zero, Fin.tail_cons, hzz]
    ring
  · rw [extendForm_apply, Fin.cons_zero, Fin.tail_cons, tail_single_zero, map_zero, zero_mul,
      add_zero]

theorem image_muSet_extend (hf : IsF3Form f) (hm : 3 ≤ m) {z : Fin m → ZMod 3} (hz0 : z ≠ 0)
    (hzz : f z z = 0) :
    localQuotientExtendEquiv hf hm ''
        (starImage (D3 (extendForm f)) (reflBar (extendForm f) (Pi.single 0 1)) ''
          {g | (g : R3 (extendForm f)) ∈ muSet (D3 (extendForm f))
            (reflBar (extendForm f) (Pi.single 0 1))
            (reflBar (extendForm f) (Pi.single 0 1 + Fin.cons 0 z))}) = sPt f z := by
  have hF := isF3Form_extendForm hf
  have hzc := isIsoPt_cons_zero (f := f) hz0 hzz
  have hu : extendForm f (Pi.single 0 1 + Fin.cons 0 z) (Pi.single 0 1 + Fin.cons 0 z) = 1 := by
    rw [norm_add hF, extendForm_single, hzc.2.1, hF.symm, hzc.2.2]
    ring
  rw [muSet_eq_muPt hF (by omega) extendForm_single hu, add_sub_cancel_left]
  exact localQuotientEquivR3_image_muPt hF (by omega) extendForm_single (tailEquiv f)
    tailEquiv_apply hzc.2.2

end CFSG.Fischer.Classification.LocalR3

namespace CFSG.Fischer.Classification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification.LocalR3 F3 CFSG.Open

theorem classicalConclusion_of_localR3_of_muSet {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hnab : NonabelianCommutator G) {d : G} (hd : d ∈ D) {m : ℕ} (hm : 5 ≤ m)
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hf : IsF3Form f)
    (φ : LocalQuotient D d ≃* R3 f) (hφ : φ '' LocalImages D d = D3 f) {x : G} (hx : x ∈ D)
    (hxd : x * d ≠ d * x) {z : Fin m → ZMod 3} (hz0 : z ≠ 0) (hzz : f z z = 0)
    (hμ : φ '' (starImage D d '' {p | (p : G) ∈ muSet D d x}) = sPt f z) :
    ClassicalConclusion G D := by
  obtain ⟨hP, hZ, hS⟩ := hH
  have hna : ∃ a b : commutator G, a * b ≠ b * a := hnab
  have hF := isF3Form_extendForm hf
  have hm3 : 3 ≤ m := by omega
  have he₀ := extendForm_single (f' := f)
  set Λ := localQuotientExtendEquiv hf hm3 with hΛ
  have hzc := isIsoPt_cons_zero (f := f) hz0 hzz
  have hd' := reflBar_mem_D3 he₀
  have hu : extendForm f (Pi.single 0 1 + Fin.cons 0 z) (Pi.single 0 1 + Fin.cons 0 z) = 1 := by
    rw [norm_add hF, he₀, hzc.2.1, hF.symm, hzc.2.2]
    ring
  have hTL : TripleProperty (LocalImages (D3 (extendForm f))
      (reflBar (extendForm f) (Pi.single 0 1))) :=
    (tripleProperty_congr Λ (localQuotientExtendEquiv_image hf hm3)).2
      (tripleProperty_D3 hf (by omega))
  have hα : (φ.trans Λ.symm) '' LocalImages D d =
      LocalImages (D3 (extendForm f)) (reflBar (extendForm f) (Pi.single 0 1)) := by
    rw [MulEquiv.coe_trans, Set.image_comp, hφ, ← localQuotientExtendEquiv_image hf hm3,
      image_symm_image]
  have hμ' : (φ.trans Λ.symm) '' (starImage D d '' {p | (p : G) ∈ muSet D d x}) =
      starImage (D3 (extendForm f)) (reflBar (extendForm f) (Pi.single 0 1)) ''
        {g | (g : R3 (extendForm f)) ∈ muSet (D3 (extendForm f))
          (reflBar (extendForm f) (Pi.single 0 1))
          (reflBar (extendForm f) (Pi.single 0 1 + Fin.cons 0 z))} := by
    rw [MulEquiv.coe_trans, Set.image_comp, hμ, ← image_muSet_extend hf hm3 hz0 hzz,
      image_symm_image]
  obtain ⟨ψ, hψ, -, -⟩ := Pair.exists_mulEquiv_of_localQuotient hP (pair_R3 hF (by omega)) hZ
    (center_R3_eq_bot hF (by omega)) (Pair.connected_of_nonabelian hP hS hna)
    (tripleProperty_D3 hF (by omega)) hd hd' (Pair.starImage_injective_of_simple hP hZ hS hd)
    (Pair.starImage_injective (pair_R3 hF (by omega)) (exists_not_commute_localClass hF
      (by omega) he₀)) hTL (φ.trans Λ.symm) hα hx hxd (reflBar_mem_D3 hu)
    (reflBar_add_not_commute hF (by omega) he₀ hzc) hμ'
    (Pair.exists_conj_of_transitive hP (Pair.exists_conj_far hP hZ hS hna hd hx hxd))
    (coverRigid_muGraph_D3 hF (by omega) he₀ hzc)
  refine classicalConclusion_of_mulEquiv hF (by omega) ψ fun g => ⟨fun hg => ?_, fun hg => ?_⟩
  · rw [← hψ]
    exact ⟨g, hg, rfl⟩
  · rw [← hψ] at hg
    obtain ⟨g', hg', hgg'⟩ := hg
    rwa [← ψ.injective hgg']

theorem classicalConclusion_of_localR3 {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hnab : NonabelianCommutator G) {d : G} (hd : d ∈ D) {m : ℕ} (hm : 7 ≤ m)
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hf : IsF3Form f)
    (φ : LocalQuotient D d ≃* R3 f) (hφ : φ '' LocalImages D d = D3 f) :
    ClassicalConclusion G D := by
  have hH' := hH
  obtain ⟨hP, hZ, hS⟩ := hH'
  have hna : ∃ a b : commutator G, a * b ≠ b * a := hnab
  obtain ⟨x, hx, hxd⟩ : ∃ x ∈ D, x * d ≠ d * x := by
    by_contra! h
    have hdZ : d ∈ Subgroup.center G := (Pair.mem_center_iff hP).2 h
    rw [hZ, Subgroup.mem_bot] at hdZ
    exact Pair.ne_one hP hd hdZ
  obtain ⟨w, z, -, hz, hμ⟩ := image_muSet_eq_sPt hP hZ hS hna hd hf hm φ hφ hx hxd
  exact classicalConclusion_of_localR3_of_muSet hH hnab hd (by omega) hf φ hφ hx hxd hz.1 hz.2.1 hμ

theorem exists_mulEquiv_R3_of_case5 {H : Type} [Group H] {E : Set H} {k : ℕ}
    (h : ∃ m : ℕ, k ≤ m ∧ ∃ f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3),
      (∀ x y, f x y = f y x) ∧ (∀ x, (∀ y, f x y = 0) → x = 0) ∧
      fischerCentralQuotientModel E
        (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
        (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) :
    ∃ m : ℕ, k ≤ m ∧ ∃ f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3), IsF3Form f ∧
      ∃ φ : H ≃* R3 f, φ '' E = D3 f := by
  obtain ⟨m, hm, f, hsymm, hnd, hmod⟩ := h
  obtain ⟨φ, hφ⟩ := (fischerCentralQuotientModel_iff E).1 hmod
  refine ⟨m, hm, f, ⟨hsymm, hnd⟩, φ, Set.ext fun q => ⟨?_, fun hq => ?_⟩⟩
  · rintro ⟨g, hg, rfl⟩
    exact (hφ g).1 hg
  · exact ⟨φ.symm q, (hφ _).2 (by rwa [MulEquiv.apply_symm_apply]), φ.apply_symm_apply q⟩

theorem classicalConclusion_of_local_case5 {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hnab : NonabelianCommutator G) {d : G} (hd : d ∈ D)
    (h : ∃ m : ℕ, 7 ≤ m ∧ ∃ f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3),
      (∀ x y, f x y = f y x) ∧ (∀ x, (∀ y, f x y = 0) → x = 0) ∧
      fischerCentralQuotientModel (LocalImages D d)
        (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
        (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) :
    ClassicalConclusion G D := by
  obtain ⟨m, hm, f, hf, φ, hφ⟩ := exists_mulEquiv_R3_of_case5 h
  exact classicalConclusion_of_localR3 hH hnab hd hm hf φ hφ

end CFSG.Fischer.Classification
