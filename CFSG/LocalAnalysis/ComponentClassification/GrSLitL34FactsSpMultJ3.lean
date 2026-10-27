module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSpMultCover
public import CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCoverJ3
public import Certificates.Certificate22224
public import CFSG.Certificates.WordPresentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Janko.Three
import all TauCeti.GroupTheory.Presentation.GroupPresentation
import all TauCeti.GroupTheory.Presentation.Relator
public import CFSG.Sporadic.SmallOddCore.J3WordBoundBase

public section

namespace CFSG.ComponentClassification.GSThmB.SpMult

open CFSG Subgroup CFSG.CosetTable TauCeti
open CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCover

theorem j3_mul_self_eq_one
    {E : Type*} [Group E] {ρ : E →* Blueprint.NativeSporadic.J3} (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ center E) (hexp : ∀ v ∈ ρ.ker, v * v = 1) {w : E}
    (hw : ρ w * ρ w = 1) : w * w = 1 := by
  obtain ⟨a₁, a₂, a₃, a₄, n, hd⟩ := j3_e16Datum
  obtain ⟨b₁, -, -, -, hb₁, -, -, -, hb₁2, -⟩ := hd.exists_lift hρ hker
  refine mul_self_eq_one_of_lift hρ hker hexp hb₁ (by rw [← sq]; exact hb₁2) ?_ hw
  intro t ht
  set φ := Sporadic.Schreier.j3PermEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : orderOf (φ t) = 2 := by rw [MulEquiv.orderOf_eq, ht]
  have h2 : orderOf (φ a₁) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hd.sq hd.ne_one
  obtain ⟨g₁, hg₁⟩ := Sporadic.SmallOddCore.j3_involution_conj_a h1
  obtain ⟨g₂, hg₂⟩ := Sporadic.SmallOddCore.j3_involution_conj_a h2
  refine ⟨φ.symm (g₁ * g₂⁻¹), φ.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg₁, hg₂]
  group

private theorem j3Rels_length : j3Rels.length = 8 := by decide

theorem j3Gens_eq : j3Gens = 2 := by decide

theorem j3Rels_mem {i : ℕ} (hi : i < 8) : j3Rels.getD i [] ∈ j3Rels := by
  rw [List.getD_eq_getElem _ _ (by rw [j3Rels_length]; exact hi)]
  exact List.getElem_mem _

theorem lift_j3Rels_eq_one {G : Type*} [Group G] (g : Fin j3Gens → G)
    (hg : ∀ r ∈ j3Rels, FreeGroup.lift g (FreeGroup.mk r) = 1) {i : ℕ} (hi : i < 8) :
    FreeGroup.lift g (FreeGroup.mk (j3Rels.getD i [])) = 1 :=
  hg _ (j3Rels_mem hi)

theorem j3Rels_squares : ∀ i ∈ [0, 4, 5, 7], ∃ u : List (Fin j3Gens × Bool),
    j3Rels.getD i [] = u ++ u := by
  intro i hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact ⟨_, (by decide : j3Rels.getD 0 [] = (j3Rels.getD 0 []).take 1 ++
      (j3Rels.getD 0 []).take 1)⟩
  · exact ⟨_, (by decide : j3Rels.getD 4 [] = (j3Rels.getD 4 []).take 22 ++
      (j3Rels.getD 4 []).take 22)⟩
  · exact ⟨_, (by decide : j3Rels.getD 5 [] = (j3Rels.getD 5 []).take 22 ++
      (j3Rels.getD 5 []).take 22)⟩
  · exact ⟨_, (by decide : j3Rels.getD 7 [] = (j3Rels.getD 7 []).take 28 ++
      (j3Rels.getD 7 []).take 28)⟩

theorem j3Rels_one_three : ∃ i₀ i₁ : Fin j3Gens, i₀.val = 0 ∧ i₁.val = 1 ∧
    j3Rels.getD 1 [] = (List.replicate 3 [(i₁, true)]).flatten ∧
      j3Rels.getD 3 [] = (List.replicate 19 [(i₀, true), (i₁, true)]).flatten :=
  ⟨⟨0, by decide⟩, ⟨1, by decide⟩, rfl, rfl, by decide, by decide⟩

theorem lift_mk_append {m : ℕ} {E : Type*} [Group E] (f : Fin m → E)
    (u v : List (Fin m × Bool)) :
    FreeGroup.lift f (FreeGroup.mk (u ++ v)) =
      FreeGroup.lift f (FreeGroup.mk u) * FreeGroup.lift f (FreeGroup.mk v) := by
  rw [← FreeGroup.mul_mk, map_mul]

theorem lift_mk_replicate {m : ℕ} {E : Type*} [Group E] (f : Fin m → E)
    (w : List (Fin m × Bool)) (k : ℕ) :
    FreeGroup.lift f (FreeGroup.mk (List.replicate k w).flatten) =
      FreeGroup.lift f (FreeGroup.mk w) ^ k := by
  induction k with
  | zero => rw [List.replicate_zero, List.flatten_nil, pow_zero, ← FreeGroup.one_eq_mk, map_one]
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, lift_mk_append, ih, pow_succ']

theorem lift_mk_single {m : ℕ} {E : Type*} [Group E] (f : Fin m → E) (i : Fin m) :
    FreeGroup.lift f (FreeGroup.mk [(i, true)]) = f i :=
  FreeGroup.lift_apply_of

theorem lift_mk_pair {m : ℕ} {E : Type*} [Group E] (f : Fin m → E) (i j : Fin m) :
    FreeGroup.lift f (FreeGroup.mk [(i, true), (j, true)]) = f i * f j := by
  rw [show [(i, true), (j, true)] = [(i, true)] ++ [(j, true)] from rfl, lift_mk_append,
    lift_mk_single, lift_mk_single]

theorem lift_mk_commWord {m : ℕ} {E : Type*} [Group E] (f : Fin m → E) (i : Fin m)
    (r : List (Fin m × Bool)) :
    FreeGroup.lift f (FreeGroup.mk (commWord [(i, true)] r)) =
      (f i)⁻¹ * (FreeGroup.lift f (FreeGroup.mk r))⁻¹ * f i *
        FreeGroup.lift f (FreeGroup.mk r) := by
  simp only [commWord, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk, map_mul, map_inv]
  rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]

theorem lift_centralWords {m : ℕ} {E : Type*} [Group E] (f : Fin m → E)
    (r : List (Fin m × Bool)) (hc : FreeGroup.lift f (FreeGroup.mk r) ∈ center E)
    (h2 : FreeGroup.lift f (FreeGroup.mk r) * FreeGroup.lift f (FreeGroup.mk r) = 1) :
    ∀ w ∈ centralWords r, FreeGroup.lift f (FreeGroup.mk w) = 1 := by
  intro w hw
  simp only [centralWords, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨i, -, rfl⟩ | rfl
  · rw [lift_mk_commWord, mul_assoc _ (f i), mem_center_iff.mp hc (f i)]
    group
  · rw [← FreeGroup.mul_mk, map_mul, h2]

theorem pow_dblOdd_eq_one {E G : Type*} [Group E] [Group G] {ρ : E →* G}
    (hexp : ∀ v ∈ ρ.ker, v * v = 1) (hsq : ∀ w : E, ρ w * ρ w = 1 → w * w = 1) {t : E} {o : ℕ}
    (h : ρ t ^ o = 1) : t ^ dblOdd o = 1 := by
  unfold dblOdd
  split_ifs with ho
  · obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero ho
    have hk := hsq (t ^ k) (by rw [← map_mul, ← pow_add, ← two_mul, map_pow]; exact h)
    rwa [← pow_add, ← two_mul] at hk
  · have hk : t ^ o ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_pow, h]
    have := hexp _ hk
    rwa [← pow_add, ← two_mul] at this

theorem lift_mk_map {m n : ℕ} {E : Type*} [Group E] (k : Fin n → E) (h : Fin m → Fin n)
    (w : List (Fin m × Bool)) :
    FreeGroup.lift k (FreeGroup.mk (w.map fun l => (h l.1, l.2))) =
      FreeGroup.lift (fun i => k (h i)) (FreeGroup.mk w) := by
  rw [CFSG.Certificates.lift_mk_eq_signedProd, CFSG.Certificates.lift_mk_eq_signedProd]
  simp only [CFSG.Certificates.signedProd, List.map_map, Function.comp_def]

theorem map_lift_mk {m : ℕ} {E G F : Type*} [Group E] [Group G] [FunLike F E G]
    [MonoidHomClass F E G] (φ : F) (k : Fin m → E) (w : List (Fin m × Bool)) :
    φ (FreeGroup.lift k (FreeGroup.mk w)) = FreeGroup.lift (fun i => φ (k i)) (FreeGroup.mk w) := by
  rw [CFSG.Certificates.lift_mk_eq_signedProd, CFSG.Certificates.lift_mk_eq_signedProd]
  exact CFSG.Certificates.map_signedProd (MonoidHomClass.toMonoidHom φ) k w

theorem injective_of_surjective_card_le {A B : Type*} [Group A] [Group B] (hA : Finite A)
    (f : A →* B) (hf : Function.Surjective f) (h : Nat.card A ≤ Nat.card B) :
    Function.Injective f :=
  (hf.bijective_of_nat_card_le h).1

theorem exists_injective_J_of
    {P : GroupPresentation} (hP : P = Sporadic.j3Presentation) (hfin : Finite P.Group)
    (hcard : Nat.card P.Group ≤ 50232960) (β : Blueprint.NativeSporadic.J3 ≃* P.Group) :
    ∃ χ : Blueprint.NativeSporadic.J3 → Sporadic.J3.J Sporadic.J3.Native.j3Data,
      Function.Injective χ ∧ (∀ i : Fin P.generatorCount, χ (β.symm (PresentedGroup.of i)) =
        Sporadic.Bridge.TwoGen.img2 (Sporadic.J3.a Sporadic.J3.Native.j3Data)
          (Sporadic.J3.b Sporadic.J3.Native.j3Data) i.val) ∧
      ∀ (k : Fin 2 → Blueprint.NativeSporadic.J3) (w : List (Fin 2 × Bool)),
        χ (FreeGroup.lift k (FreeGroup.mk w)) = FreeGroup.lift (fun i => χ (k i)) (FreeGroup.mk w) := by
  have hrel : ∀ v ∈ P.relatorLetters, Sporadic.Bridge.wordProd
      (Sporadic.Bridge.TwoGen.img2 (Sporadic.J3.a Sporadic.J3.Native.j3Data)
        (Sporadic.J3.b Sporadic.J3.Native.j3Data)) v = 1 := by
    rw [hP]
    exact Sporadic.Bridge.J3.relators_eval
  have hgc : P.generatorCount = 2 := by
    rw [hP]
    exact Sporadic.Bridge.J3.generatorCount_eq
  obtain ⟨ψ, hψ⟩ : ∃ ψ : P.Group →* Sporadic.J3.J Sporadic.J3.Native.j3Data,
      ∀ i : Fin P.generatorCount, ψ (PresentedGroup.of i) =
        Sporadic.Bridge.TwoGen.img2 (Sporadic.J3.a Sporadic.J3.Native.j3Data)
          (Sporadic.J3.b Sporadic.J3.Native.j3Data) i.val :=
    ⟨PresentedGroup.toGroup (Sporadic.Bridge.lift_relator P _ hrel),
      fun i => PresentedGroup.toGroup.of _⟩
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← Sporadic.J3.closure_ab Sporadic.J3.Native.j3Data,
      Subgroup.closure_le]
    rintro g (h | h)
    · exact ⟨PresentedGroup.of ⟨0, by omega⟩, (hψ _).trans h.symm⟩
    · rw [Set.mem_singleton_iff] at h
      exact ⟨PresentedGroup.of ⟨1, by omega⟩, (hψ _).trans h.symm⟩
  have hinj : Function.Injective ψ := injective_of_surjective_card_le hfin ψ hsurj
    (hcard.trans Sporadic.Bridge.J3.le_card_J)
  refine ⟨fun u => ψ (β u), fun u v huv => β.injective (hinj huv), fun i => ?_, fun k w => ?_⟩
  · change ψ (β (β.symm (PresentedGroup.of i))) = _
    rw [MulEquiv.apply_symm_apply]
    exact hψ i
  · change ψ (β (FreeGroup.lift k (FreeGroup.mk w))) = _
    rw [map_lift_mk β, map_lift_mk ψ]

theorem exists_injective_native
    (β : Blueprint.NativeSporadic.J3 ≃* SporadicName.J3.Group) :
    ∃ χ : Blueprint.NativeSporadic.J3 → Sporadic.J3.J Sporadic.J3.Native.j3Data,
      Function.Injective χ ∧ (∀ i : Fin j3Gens, χ (β.symm (PresentedGroup.of i)) =
        Sporadic.Bridge.TwoGen.img2 (Sporadic.J3.a Sporadic.J3.Native.j3Data)
          (Sporadic.J3.b Sporadic.J3.Native.j3Data) i.val) ∧
      ∀ (k : Fin 2 → Blueprint.NativeSporadic.J3) (w : List (Fin 2 × Bool)),
        χ (FreeGroup.lift k (FreeGroup.mk w)) = FreeGroup.lift (fun i => χ (k i)) (FreeGroup.mk w) := by
  obtain ⟨hfin, hcard⟩ := Sporadic.Presentation.J3.finite_card_le
  exact exists_injective_J_of (P := SporadicName.J3.presentation) rfl hfin hcard β

theorem j3_card_le
    (E : Type) [Group E] [Finite E] (ρ : E →* Blueprint.NativeSporadic.J3)
    (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ center E) (hexp : ∀ v ∈ ρ.ker, v * v = 1)
    (hperf : Group.IsPerfect E) : Nat.card E ≤ Nat.card Blueprint.NativeSporadic.J3 := by
  obtain ⟨β⟩ := Sporadic.Bridge.J3.nonempty_mulEquiv
  set g : Fin j3Gens → Blueprint.NativeSporadic.J3 := fun i => β.symm (PresentedGroup.of i)
    with hg
  have hlift : ∀ w : FreeGroup (Fin j3Gens),
      FreeGroup.lift g w = β.symm (PresentedGroup.mk _ w) := by
    intro w
    induction w using FreeGroup.induction_on with
    | one => rw [map_one, map_one, map_one]
    | of i => rw [FreeGroup.lift_apply_of]; rfl
    | inv_of i ih => rw [map_inv, ih, map_inv, map_inv]
    | mul x y hx hy => rw [map_mul, hx, hy, map_mul, map_mul]
  have hgrel : ∀ r ∈ j3Rels, FreeGroup.lift g (FreeGroup.mk r) = 1 := by
    intro r hr
    have hmem : FreeGroup.mk r ∈ SporadicName.J3.presentation.relatorSet := by
      rw [Sporadic.Presentation.relatorSet_eq]
      exact List.mem_map_of_mem hr
    rw [hlift, PresentedGroup.one_of_mem hmem, map_one]
  have hgen : Subgroup.closure (Set.range g) = ⊤ := by
    rw [← FreeGroup.range_lift_eq_closure, MonoidHom.range_eq_top]
    intro t
    obtain ⟨p, rfl⟩ := β.symm.surjective t
    obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective _ p
    exact ⟨w, hlift w⟩
  have hsq : ∀ w : E, ρ w * ρ w = 1 → w * w = 1 := fun w hw =>
    j3_mul_self_eq_one hρ hker hexp hw
  obtain ⟨i₀, i₁, hi₀, hi₁, hR1, hR3⟩ := j3Rels_one_three
  have hb3 : g i₁ ^ 3 = 1 := by
    have := lift_j3Rels_eq_one g hgrel (i := 1) (by norm_num)
    rwa [hR1, lift_mk_replicate, lift_mk_single] at this
  have hab : (g i₀ * g i₁) ^ 19 = 1 := by
    have := lift_j3Rels_eq_one g hgrel (i := 3) (by norm_num)
    rwa [hR3, lift_mk_replicate, lift_mk_pair] at this
  obtain ⟨x₀, hx₀⟩ := hρ (g i₀)
  obtain ⟨y₀, hy₀⟩ := hρ (g i₁)
  have hc₁ : y₀ ^ 3 ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_pow, hy₀, hb3]
  set y := y₀ * y₀ ^ 3 with hydef
  have hy : ρ y = g i₁ := by rw [hydef, map_mul, hc₁, mul_one, hy₀]
  have hy3 : y ^ 3 = 1 := by
    rw [hydef, (show Commute y₀ (y₀ ^ 3) from mem_center_iff.mp (hker hc₁) y₀).mul_pow, ← pow_mul,
      show y₀ ^ 3 * y₀ ^ (3 * 3) = (y₀ ^ 3 * y₀ ^ 3) ^ 2 by group, hexp _ hc₁, one_pow]
  have hc₂ : (x₀ * y) ^ 19 ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_pow, map_mul, hx₀, hy, hab]
  set x := x₀ * (x₀ * y) ^ 19 with hxdef
  have hx : ρ x = g i₀ := by rw [hxdef, map_mul, hc₂, mul_one, hx₀]
  have hxy : (x * y) ^ 19 = 1 := by
    have hcomm := mem_center_iff.mp (hker hc₂)
    rw [hxdef, mul_assoc, ← hcomm y, ← mul_assoc,
      (show Commute (x₀ * y) ((x₀ * y) ^ 19) from hcomm (x₀ * y)).mul_pow, ← pow_mul,
      show (x₀ * y) ^ 19 * (x₀ * y) ^ (19 * 19) = ((x₀ * y) ^ 19 * (x₀ * y) ^ 19) ^ 10 by group,
      hexp _ hc₂, one_pow]
  have hfin : ∀ i : Fin j3Gens, i = i₀ ∨ i = i₁ := by
    intro i
    have h2 : j3Gens = 2 := j3Gens_eq
    have hi : i.val < j3Gens := i.isLt
    rcases Nat.lt_or_ge i.val 1 with h | h
    · exact Or.inl (Fin.ext (by omega))
    · exact Or.inr (Fin.ext (by omega))
  set f : Fin j3Gens → E := fun i => if i.val = 0 then x else y with hf
  have hfx : f i₀ = x := by simp [hf, hi₀]
  have hfy : f i₁ = y := by simp [hf, hi₁]
  have hρf' : ρ ∘ f = g := funext fun i => by
    rcases hfin i with rfl | rfl
    · rw [Function.comp_apply, hfx, hx]
    · rw [Function.comp_apply, hfy, hy]
  have hρf : ρ.comp (FreeGroup.lift f) = FreeGroup.lift g := FreeGroup.ext_hom _ _ fun i => by
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, ← hρf']
    rfl
  have hval : ∀ r ∈ j3Rels, ρ (FreeGroup.lift f (FreeGroup.mk r)) = 1 := fun r hr => by
    rw [← MonoidHom.comp_apply, hρf, hgrel r hr]
  have hsqrel : ∀ i ∈ [0, 4, 5, 7], FreeGroup.lift f (FreeGroup.mk (j3Rels.getD i [])) = 1 := by
    intro i hi
    have hi8 : i < 8 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      omega
    obtain ⟨u, hu⟩ := j3Rels_squares i hi
    have h := hval _ (j3Rels_mem hi8)
    rw [hu, lift_mk_append, map_mul] at h
    rw [hu, lift_mk_append]
    exact hsq _ h
  have hrel : ∀ w ∈ j3CoverRels, FreeGroup.lift f (FreeGroup.mk w) = 1 := by
    intro w hw
    simp only [j3CoverRels, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hw
    rcases hw with (((rfl | rfl | rfl | rfl | rfl | rfl) | hw) | hw)
    · exact hsqrel 0 (by simp)
    · rw [hR1, lift_mk_replicate, lift_mk_single, hfy]
      exact hy3
    · rw [hR3, lift_mk_replicate, lift_mk_pair, hfx, hfy]
      exact hxy
    · exact hsqrel 4 (by simp)
    · exact hsqrel 5 (by simp)
    · exact hsqrel 7 (by simp)
    · exact lift_centralWords f _ (hker (hval _ (j3Rels_mem (i := 2) (by norm_num))))
        (hexp _ (hval _ (j3Rels_mem (i := 2) (by norm_num)))) w hw
    · exact lift_centralWords f _ (hker (hval _ (j3Rels_mem (i := 6) (by norm_num))))
        (hexp _ (hval _ (j3Rels_mem (i := 6) (by norm_num)))) w hw
  have hgenE : (Subgroup.closure (Set.range f) ⊔ ρ.ker : Subgroup E) = ⊤ := by
    rw [← comap_map_eq, MonoidHom.map_closure, ← Set.range_comp]
    rw [show (⇑ρ ∘ f) = g from hρf', hgen, comap_top]
  obtain ⟨⟨hUfi, hUidx⟩, ⟨hΓfin, hΓcard⟩, hab, huc⟩ := Certificates.certificate22224
  obtain ⟨χ, hχi, hχg, hχl⟩ := exists_injective_native β
  have hχ1 : χ 1 = 1 := by
    have h := hχl ![1, 1] []
    rwa [← FreeGroup.one_eq_mk, map_one, map_one] at h
  set f2 : Fin 2 → E := ![x, y] with hf2
  set ab : Fin 2 → Sporadic.J3.J Sporadic.J3.Native.j3Data := fun i =>
    Sporadic.Bridge.TwoGen.img2 (Sporadic.J3.a Sporadic.J3.Native.j3Data)
      (Sporadic.J3.b Sporadic.J3.Native.j3Data) i.val with hab'
  have hχf2 : (fun j : Fin 2 => χ (ρ (f2 j))) = ab := by
    funext j
    fin_cases j
    · change χ (ρ x) = ab 0
      rw [hx]
      simp only [hg]
      rw [hχg, hi₀]
      rfl
    · change χ (ρ y) = ab 1
      rw [hy]
      simp only [hg]
      rw [hχg, hi₁]
      rfl
  have hwab : ∀ w ∈ ucABWords, ρ (FreeGroup.lift f2 (FreeGroup.mk w)) = 1 := by
    intro w hw
    apply hχi
    rw [hχ1, map_lift_mk ρ, hχl]
    exact (congrArg (fun k => FreeGroup.lift k (FreeGroup.mk w)) hχf2).trans (hab w hw)
  set U2 := FreeGroup.lift f2 (FreeGroup.mk ucU) with hU2
  set C2 := FreeGroup.lift f2 (FreeGroup.mk ucC) with hC2
  have hχUC : (fun j : Fin 2 => χ (ρ (![U2, C2] j))) =
      ![FreeGroup.lift ab (FreeGroup.mk ucU), FreeGroup.lift ab (FreeGroup.mk ucC)] := by
    funext j
    fin_cases j
    · change χ (ρ U2) = FreeGroup.lift ab (FreeGroup.mk ucU)
      rw [hU2, map_lift_mk ρ, hχl]
      exact congrArg (fun k => FreeGroup.lift k (FreeGroup.mk ucU)) hχf2
    · change χ (ρ C2) = FreeGroup.lift ab (FreeGroup.mk ucC)
      rw [hC2, map_lift_mk ρ, hχl]
      exact congrArg (fun k => FreeGroup.lift k (FreeGroup.mk ucC)) hχf2
  have hwuc : ∀ w ∈ gammaJ3Words, ρ (FreeGroup.lift ![U2, C2] (FreeGroup.mk w)) = 1 := by
    intro w hw
    apply hχi
    rw [hχ1, map_lift_mk ρ, hχl]
    exact (congrArg (fun k => FreeGroup.lift k (FreeGroup.mk w)) hχUC).trans (huc w hw)
  have hff : (fun i : Fin j3Gens => f2 (Fin.ofNat 2 i.val)) = f := by
    funext i
    rcases hfin i with rfl | rfl
    · rw [hfx, hi₀]
      rfl
    · rw [hfy, hi₁]
      rfl
  have hucrel : ∀ w ∈ ucRels, FreeGroup.lift f2 (FreeGroup.mk w) = 1 := by
    intro w hw
    rcases List.mem_append.1 hw with hw | hw
    · obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw
      rw [toFin2]
      exact (lift_mk_map f2 (fun i : Fin j3Gens => Fin.ofNat 2 i.val) w').trans
        ((congrArg (fun k => FreeGroup.lift k (FreeGroup.mk w')) hff).trans (hrel w' hw'))
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
      rw [powW, lift_mk_replicate]
      refine pow_dblOdd_eq_one hexp hsq ?_
      rw [← map_pow, ← lift_mk_replicate]
      exact hwab _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨p, hp, rfl⟩))
  have hucrel' : ∀ r ∈ {r : FreeGroup (Fin 2) | r ∈ ucRels.map FreeGroup.mk},
      FreeGroup.lift f2 r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact hucrel w hw
  set φ : PG 2 ucRels →* E := PresentedGroup.toGroup hucrel' with hφ
  have hφmk : ∀ z, φ (PresentedGroup.mk _ z) = FreeGroup.lift f2 z := by
    intro z
    induction z using FreeGroup.induction_on with
    | one => rw [map_one, map_one, map_one]
    | of i => rw [FreeGroup.lift_apply_of]; exact PresentedGroup.toGroup.of hucrel'
    | inv_of i ih => rw [map_inv, map_inv, map_inv, ih]
    | mul p q hp hq => rw [map_mul, map_mul, map_mul, hp, hq]
  have hφsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    refine eq_top_of_sup_center hker (eq_top_iff.mpr ?_)
    rw [← hgenE]
    refine sup_le_sup_right ?_ _
    rw [closure_le]
    rintro _ ⟨i, rfl⟩
    rcases hfin i with rfl | rfl
    · exact ⟨PresentedGroup.of 0, by rw [PresentedGroup.toGroup.of, hfx]; rfl⟩
    · exact ⟨PresentedGroup.of 1, by rw [PresentedGroup.toGroup.of, hfy]; rfl⟩
  set K := (Subgroup.closure ({ucUe, ucCe} : Set (PG 2 ucRels))).map φ with hK
  have hKidx : K.index ≤ 6156 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hUfi.index_ne_zero)
      (Subgroup.index_map_dvd (H := Subgroup.closure ({ucUe, ucCe} : Set (PG 2 ucRels)))
        hφsurj)).trans hUidx
  have hv6 : FreeGroup.lift f2 (FreeGroup.mk ((0, true) :: ucC)) ^ 6 = 1 := by
    have h := pow_dblOdd_eq_one hexp hsq (o := 6)
      (t := FreeGroup.lift f2 (FreeGroup.mk ((0, true) :: ucC)))
      (by rw [← map_pow, ← lift_mk_replicate]; exact hwab _ List.mem_cons_self)
    exact h
  have hU3 : U2 ^ 3 = 1 := by
    rw [hU2, ucU, ← FreeGroup.inv_mk, map_inv, powW, lift_mk_replicate, inv_pow, ← pow_mul,
      show 4 * 3 = 6 * 2 from rfl, pow_mul, hv6, one_pow, inv_one]
  have hγrel : ∀ w ∈ gammaRels, FreeGroup.lift ![U2, C2] (FreeGroup.mk w) = 1 := by
    intro w hw
    unfold gammaRels at hw
    rcases List.mem_append.1 hw with hw | hw
    · rcases List.mem_append.1 hw with hw | hw
      · rcases List.mem_cons.1 hw with rfl | hw
        · rw [powW, lift_mk_replicate, lift_mk_single]
          exact hU3
        · rw [List.mem_singleton] at hw
          subst hw
          rw [powW, lift_mk_replicate, lift_mk_single]
          have h := hwuc (powW [(1, true)] 4) (by simp [gammaJ3Words])
          rw [powW, lift_mk_replicate, lift_mk_single, map_pow] at h
          exact pow_dblOdd_eq_one hexp hsq (o := 4) h
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
        rw [powW, lift_mk_replicate]
        refine pow_dblOdd_eq_one hexp hsq ?_
        have h := hwuc (powW p.1 p.2) (List.mem_append_left _
          (List.mem_append_right _ (List.mem_map.2 ⟨p, hp, rfl⟩)))
        rwa [powW, lift_mk_replicate, map_pow] at h
    · obtain ⟨r, hr, hw⟩ := List.mem_flatMap.1 hw
      have h1 := hwuc r (List.mem_append_right _ hr)
      exact lift_centralWords ![U2, C2] r (hker (MonoidHom.mem_ker.2 h1))
        (hexp _ (MonoidHom.mem_ker.2 h1)) w hw
  have hγrel' : ∀ r ∈ {r : FreeGroup (Fin 2) | r ∈ gammaRels.map FreeGroup.mk},
      FreeGroup.lift ![U2, C2] r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact hγrel w hw
  set θ : PG 2 gammaRels →* E := PresentedGroup.toGroup hγrel' with hθ
  have hKθ : K ≤ θ.range := by
    rw [hK, MonoidHom.map_closure, closure_le]
    rintro _ ⟨s, hs, rfl⟩
    rcases hs with rfl | rfl
    · exact ⟨PresentedGroup.of 0, by rw [PresentedGroup.toGroup.of, ucUe, hφmk]; rfl⟩
    · exact ⟨PresentedGroup.of 1, by rw [PresentedGroup.toGroup.of, ucCe, hφmk]; rfl⟩
  have hKcard : Nat.card K ≤ 8160 :=
    (Subgroup.card_le_of_le hKθ).trans
      ((Nat.card_le_card_of_surjective θ.rangeRestrict θ.rangeRestrict_surjective).trans hΓcard)
  rw [Sporadic.J3.card_J3, ← Subgroup.card_mul_index K]
  calc Nat.card K * K.index ≤ 8160 * 6156 := Nat.mul_le_mul hKcard hKidx
    _ = 50232960 := by norm_num

theorem j3_odd_card_center
    (Q : Type) [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    (he : Nonempty (Q ⧸ center Q ≃* Blueprint.NativeSporadic.J3)) :
    Odd (Nat.card (center Q)) :=
  odd_card_center_of_card_le (fun E _ _ ρ hρ hker hexp hperf => j3_card_le E ρ hρ hker hexp hperf)
    Q hQ he

end CFSG.ComponentClassification.GSThmB.SpMult
