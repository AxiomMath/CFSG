module

public import CFSG.LieType.Chevalley.E7Levi.Sign
public import CFSG.LieType.Chevalley.E7Levi.Roots
public import CFSG.RankThree.PartOne.KD4T.Inj

public noncomputable section

namespace CFSG.LieType.Chevalley.E7Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KD4T
open scoped Pointwise

@[expose] def e7Set (τ : Tag) : Set (Fin τ.rank) := {i | i.val < Tag.E7.rank}

section Support

variable {τ : Tag} [hτ : E7Sub τ]

theorem height_e7Lat (β : Fin Tag.E7.rank → ℤ) : height (e7Lat τ β) = height β := by
  rw [height, height, sum_eq_sum_e7Idx _ (fun i hi => e7Lat_apply_of_le hi)]
  exact Finset.sum_congr rfl fun k _ => e7Lat_apply_e7Idx β k

end Support

section Roots

variable {τ : Tag} [hτ : E7Sub τ]

theorem mem_parabolicRoots_e7Set_iff {γ : Fin τ.rank → ℤ} :
    γ ∈ parabolicRoots τ (e7Set τ) ↔ ∃ γ' ∈ parabolicRoots Tag.E7 Set.univ, e7Lat τ γ' = γ := by
  constructor
  · rintro ⟨hγ, hz⟩
    have h7 : ∀ i : Fin τ.rank, Tag.E7.rank ≤ i.val → γ i = 0 := fun i hi =>
      hz i (by simp [e7Set, hi])
    have hlat : e7Lat τ (fun k => γ (e7Idx k)) = γ := e7Lat_comp_e7Idx h7
    exact ⟨fun k => γ (e7Idx k),
      ⟨isRoot_e7Lat_iff.1 (hlat ▸ hγ), fun i hi => absurd (Set.mem_univ i) hi⟩, hlat⟩
  · rintro ⟨γ', ⟨hγ', -⟩, rfl⟩
    exact ⟨isRoot_e7Lat_iff.2 hγ', fun i hi => e7Lat_apply_of_le (by simpa [e7Set] using hi)⟩

theorem range_e7Lat_e7PosRoot :
    Set.range (fun k => e7Lat τ (e7PosRoot k)) = parabolicPosRoots τ (e7Set τ) := by
  ext γ
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨hΦ, hroot, hpos⟩ : e7PosRoot k ∈ parabolicPosRoots Tag.E7 Set.univ :=
      range_e7PosRoot ▸ Set.mem_range_self k
    exact ⟨mem_parabolicRoots_e7Set_iff.2 ⟨_, hΦ, rfl⟩, isRoot_e7Lat_iff.2 hroot,
      by rw [height_e7Lat]; exact hpos⟩
  · rintro ⟨hΦ, -, hpos⟩
    obtain ⟨γ', hγ', rfl⟩ := mem_parabolicRoots_e7Set_iff.1 hΦ
    have hmem : γ' ∈ parabolicPosRoots Tag.E7 Set.univ :=
      ⟨hγ', hγ'.1, by rw [← height_e7Lat (τ := τ)]; exact hpos⟩
    rw [← range_e7PosRoot] at hmem
    obtain ⟨k, rfl⟩ := hmem
    exact ⟨k, rfl⟩

end Roots

section Torus

variable {τ : Tag} [hτ : E7Sub τ] {K : Type} [Field K]

private def e7Equiv : Fin Tag.E7.rank ≃ e7Set τ where
  toFun k := ⟨e7Idx k, k.2⟩
  invFun j := ⟨j.val.val, j.2⟩
  left_inv k := Fin.ext rfl
  right_inv j := Subtype.ext (Fin.ext rfl)

private theorem prod_e7Set_eq_prod_fin [Fintype (e7Set τ)] {M : Type*} [CommMonoid M]
    (g : e7Set τ → M) :
    ∏ j : e7Set τ, g j = ∏ k : Fin Tag.E7.rank, g (e7Equiv (τ := τ) k) :=
  (Equiv.prod_comp (e7Equiv (τ := τ)) g).symm

private theorem eq_one_of_supportedTorus_e7 [CharP K 2] {h : ModGL τ K}
    (hh : h ∈ supportedTorus τ K (e7Set τ))
    (h1 : ∀ i : Fin τ.rank, i.val < Tag.E7.rank → torusRootChar h (Pi.single i 1) = 1) :
    h = 1 := by
  classical
  letI : Fintype (e7Set τ) := Fintype.ofFinite _
  obtain ⟨a, rfl⟩ := mem_supportedTorus.1 hh
  let b : Fin Tag.E7.rank → Kˣ := fun k => a (e7Equiv (τ := τ) k)
  have hb1 : ∀ i : Fin Tag.E7.rank, ∏ k, b k ^ Tag.E7.cartan k i = 1 := by
    intro i
    have h2 := h1 (e7Idx i) i.2
    rw [torusRootChar_supportedTorusHom (e7Set τ) a (isRoot_single τ (e7Idx i))] at h2
    have he : ∀ j : e7Set τ,
        (∑ l, τ.cartan j l * (Pi.single (e7Idx i) 1 : Fin τ.rank → ℤ) l) =
          τ.cartan j (e7Idx i) := fun j => by simp [Pi.single_apply]
    simp only [he] at h2
    have h2' : (∏ j : e7Set τ, a j ^ τ.cartan j (e7Idx i) : Kˣ) = 1 :=
      Units.ext (by simpa using h2)
    rw [prod_e7Set_eq_prod_fin (fun j => a j ^ τ.cartan j (e7Idx i))] at h2'
    have h2'' : ∏ k : Fin Tag.E7.rank, b k ^ Tag.E7.cartan k i = 1 := by
      have hprod : (∏ k : Fin Tag.E7.rank, b k ^ Tag.E7.cartan k i) =
          ∏ k : Fin Tag.E7.rank,
            a (e7Equiv (τ := τ) k) ^ τ.cartan (↑(e7Equiv (τ := τ) k)) (e7Idx i) := by
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [show (↑(e7Equiv (τ := τ) k) : Fin τ.rank) = e7Idx k from rfl, cartan_e7Idx]
      rw [hprod]
      exact h2'
    exact h2''
  have hb_one : b = 1 := eq_one_of_prod_zpow_cartan_E7 b hb1
  have ha : a = 1 := by
    funext j
    have hj := congrFun hb_one ⟨j.val.val, j.2⟩
    change a (e7Equiv (τ := τ) ⟨j.val.val, j.2⟩) = 1 at hj
    rwa [show e7Equiv (τ := τ) ⟨j.val.val, j.2⟩ = j from Subtype.ext (Fin.ext rfl)] at hj
  rw [ha, map_one]

end Torus

section Unipotent

variable {τ : Tag} [hτ : E7Sub τ] {K : Type} [Field K]

theorem pinnedX_e7Lat_mem_subsystemGroup {β : Fin Tag.E7.rank → ℤ}
    (hβ : β ∈ parabolicRoots Tag.E7 Set.univ) (c : K) :
    pinnedX τ K (e7Lat τ β) c ∈ subsystemGroup τ K (e7Set τ) :=
  rootSubgroup_le_subsystemGroup (mem_parabolicRoots_e7Set_iff.2 ⟨β, hβ, rfl⟩)
    (Subgroup.subset_closure ⟨c, rfl⟩)

theorem exists_sign_e7Res_pinnedX {β : Fin Tag.E7.rank → ℤ}
    (hβ : β ∈ parabolicRoots Tag.E7 Set.univ) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (L : Type) [Field L] (c : L),
      e7Res (A := e7Set τ) L (fun _ hi => hi)
        ⟨pinnedX τ L (e7Lat τ β) c, pinnedX_e7Lat_mem_subsystemGroup hβ c⟩ =
        pinnedX Tag.E7 L β ((ε : L) * c) := by
  obtain ⟨ε, hε, h⟩ := exists_sign_pinnedX_comp_e7Emb (τ := τ) hβ.1
  exact ⟨ε, hε, fun L _ c => e7Res_eq _ fun v => LinearMap.congr_fun (h L c) v⟩

theorem eq_one_of_mem_parabolicLeviUnipotent_e7Res {u : subsystemGroup τ K (e7Set τ)}
    (hu : (u : ModGL τ K) ∈ parabolicLeviUnipotent τ K (e7Set τ))
    (h1 : e7Res (A := e7Set τ) K (fun _ hi => hi) u = 1) : u = 1 := by
  have hinj : Function.Injective (fun k => e7Lat τ (e7PosRoot k)) := fun i j h =>
    e7PosRoot_injective (e7Lat_injective h)
  have hβ : ∀ k, e7PosRoot k ∈ parabolicRoots Tag.E7 Set.univ := fun k =>
    ((range_e7PosRoot ▸ Set.mem_range_self k :
      e7PosRoot k ∈ parabolicPosRoots Tag.E7 Set.univ)).1
  obtain ⟨c, -, hc⟩ := (bijOn_prod_pinnedX_parabolicPosRoots (K := K) _ hinj
    range_e7Lat_e7PosRoot).surjOn hu
  choose ε hε hεeq using fun k => exists_sign_e7Res_pinnedX (τ := τ) (hβ k)
  set l : List (subsystemGroup τ K (e7Set τ)) := List.ofFn fun k =>
    ⟨pinnedX τ K (e7Lat τ (e7PosRoot k)) (c k),
      pinnedX_e7Lat_mem_subsystemGroup (hβ k) (c k)⟩
  have hul : u = l.prod := by
    apply Subtype.ext
    rw [Subgroup.val_list_prod, List.map_ofFn]
    exact hc.symm
  have hr_l : e7Res (A := e7Set τ) K (fun _ hi => hi) l.prod = (List.ofFn fun k =>
      pinnedX Tag.E7 K (e7PosRoot k) ((ε k : K) * c k)).prod := by
    rw [map_list_prod (M := subsystemGroup τ K (e7Set τ)) (N := ModGL Tag.E7 K)
      (e7Res (A := e7Set τ) K (fun _ hi => hi)) l, List.map_ofFn]
    exact congrArg (fun f => (List.ofFn f).prod) (funext fun k => hεeq k K (c k))
  have hr : e7Res (A := e7Set τ) K (fun _ hi => hi) u = (List.ofFn fun k =>
      pinnedX Tag.E7 K (e7PosRoot k) ((ε k : K) * c k)).prod := by
    rw [hul]
    exact hr_l
  have h0 : (List.ofFn fun k => pinnedX Tag.E7 K (e7PosRoot k) ((ε k : K) * c k)).prod =
      (List.ofFn fun k => pinnedX Tag.E7 K (e7PosRoot k) ((fun _ => (0 : K)) k)).prod := by
    rw [← hr, h1]
    simp [pinnedX_zero]
  have hz := (bijOn_prod_pinnedX_parabolicPosRoots (τ := Tag.E7) (K := K) (J := Set.univ)
    e7PosRoot e7PosRoot_injective range_e7PosRoot).injOn (Set.mem_univ _)
    (Set.mem_univ (fun _ => (0 : K))) h0
  have hc0 : c = 0 := funext fun k => by
    have := congrFun hz k
    rcases hε k with he | he <;> simp [he] at this <;> exact this
  rw [hul]
  apply Subtype.ext
  rw [Subgroup.val_list_prod, List.map_ofFn, Subgroup.coe_one]
  simp [hc0, pinnedX_zero]

end Unipotent

section Kernel

variable {τ : Tag} [hτ : E7Sub τ]
  {K : Type} [Field K]

variable (τ K) in
@[expose] def nuE7 : subsystemGroup τ K (e7Set τ) →* ModGL Tag.E7 K :=
  e7Res (A := e7Set τ) K (fun _ hi => hi)

theorem nuE7_apply (g : subsystemGroup τ K (e7Set τ)) (v : RootModule Tag.E7 K) :
    ((g : ModGL τ K) : Module.End K (RootModule τ K)) (e7Emb τ K v) =
      e7Emb τ K ((nuE7 τ K g : Module.End K (RootModule Tag.E7 K)) v) :=
  e7Res_apply (A := e7Set τ) (fun _ hi => hi) g v

end Kernel

section Injective

variable {τ : Tag} [hτ : E7Sub τ] {K : Type} [Field K]

theorem nuE7_injective [CharP K 2] : Function.Injective (nuE7 τ K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgfix : ∀ v, ((g : ModGL τ K) : Module.End K (RootModule τ K)) (e7Emb τ K v) =
      e7Emb τ K v := by
    intro v
    rw [nuE7_apply g v, hg, Units.val_one, Module.End.one_apply]
  obtain ⟨⟨v, h, u, u'⟩, ⟨hv, hh, hu, hu', hgeq⟩, -⟩ := existsUnique_supportedCell_factors g.2
  simp only at hv hh hu hu' hgeq
  have hhQ : h ∈ subsystemGroup τ K (e7Set τ) := supportedTorus_le_subsystemGroup _ hh
  have huQ : u ∈ subsystemGroup τ K (e7Set τ) := parabolicLeviUnipotent_le_subsystemGroup hu
  have hu'Q : u' ∈ subsystemGroup τ K (e7Set τ) := by
    rw [subsystemGroup_eq_rootSpan]
    exact rootSpan_mono Set.inter_subset_left hu'
  have hhB : h ∈ borelGroup τ K :=
    torusGroup_le_borelGroup (supportedTorus_le_torusGroup _ hh)
  have huB : u ∈ borelGroup τ K :=
    Subgroup.mem_sup_right (parabolicLeviUnipotent_le_posUnipotent _ hu)
  have hu'B : u' ∈ borelGroup τ K :=
    Subgroup.mem_sup_right (rootSpan_le_posUnipotent (fun _ hα => ⟨hα.2.1, hα.2.2.1⟩) hu')
  have hb : (h * u)⁻¹ * u'⁻¹ ∈ borelGroup τ K :=
    mul_mem (inv_mem (mul_mem hhB huB)) (inv_mem hu'B)
  have hn : canonicalRep (coxeterSystem τ) K v = (h * u)⁻¹ * (g : ModGL τ K) * u'⁻¹ := by
    rw [← hgeq]
    group
  have hfix : ∀ γ ∈ parabolicRoots τ (e7Set τ),
      (canonicalRep (coxeterSystem τ) K v : Module.End K (RootModule τ K)) (rootVec τ K γ) =
        (((h * u)⁻¹ * u'⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K γ) := by
    intro γ hγ
    obtain ⟨γ', -, rfl⟩ := mem_parabolicRoots_e7Set_iff.1 hγ
    have e1 : ((u'⁻¹ : ModGL τ K) : Module.End K (RootModule τ K))
        (rootVec τ K (e7Lat τ γ')) =
        e7Emb τ K ((nuE7 τ K ⟨u'⁻¹, inv_mem hu'Q⟩ : Module.End K (RootModule Tag.E7 K))
          (rootVec Tag.E7 K γ')) := by
      rw [← e7Emb_rootVec, ← nuE7_apply ⟨u'⁻¹, inv_mem hu'Q⟩]
    have e2 : ((g : ModGL τ K) : Module.End K (RootModule τ K))
        (((u'⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K (e7Lat τ γ'))) =
        ((u'⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K (e7Lat τ γ')) := by
      rw [e1, hgfix]
    rw [hn, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, e2,
      Units.val_mul, Module.End.mul_apply]
  have hvγ : ∀ γ ∈ parabolicRoots τ (e7Set τ), v • γ = γ := by
    intro γ hγ
    have hmaps := mapsRootLines_canonicalRep (R := K) v
    have hγneg : -γ ∈ parabolicRoots τ (e7Set τ) := neg_mem_parabolicRoots hγ
    have n1 := not_precedes_of_apply_eq_borel hb hmaps hγ.1 (hfix γ hγ)
    have n2 := not_precedes_of_apply_eq_borel hb hmaps hγneg.1 (hfix (-γ) hγneg)
    exact eq_of_not_precedes_of_not_precedes_neg _ _ _ _ rfl (by rw [smul_neg]) n1 n2
  have hv1 : v = 1 := eq_one_of_fix_of_mem_parabolicWeylGroup hv fun j hj =>
    hvγ _ (single_mem_parabolicRoots hj)
  subst hv1
  have hu'1 : u' = 1 := by
    rw [inversionSet_one, Set.inter_empty] at hu'
    simpa [rootSpan] using hu'
  rw [hu'1, canonicalRep_one, mul_one, mul_one] at hgeq
  have hhT : h ∈ torusGroup τ K := supportedTorus_le_torusGroup _ hh
  have huU : IsUpperUnitriangular (u : Module.End K (RootModule τ K)) :=
    (positive_root_triangularity.{0, 0} τ).1 K |>.1 u
      (parabolicLeviUnipotent_le_posUnipotent _ hu)
  have hχ : ∀ i : Fin τ.rank, i.val < Tag.E7.rank → torusRootChar h (Pi.single i 1) = 1 := by
    intro i hi
    obtain ⟨k, rfl⟩ := exists_e7Idx_eq hi
    have hα : IsRoot τ (Pi.single (e7Idx k) 1) := isRoot_single τ _
    rw [← coeff_torus_mul_unitriangular hhT huU hα, hgeq]
    have hv : rootVec τ K (Pi.single (e7Idx k) 1) =
        e7Emb τ K (rootVec Tag.E7 K (Pi.single k 1)) := by
      rw [e7Emb_rootVec, e7Lat_single]
    rw [hv, hgfix, ← hv, rootVec_eq_single_of_isRoot hα, Finsupp.single_eq_same]
  have hh1 : h = 1 := eq_one_of_supportedTorus_e7 hh hχ
  subst hh1
  rw [one_mul] at hgeq
  have hgu : g = ⟨u, huQ⟩ := Subtype.ext hgeq.symm
  rw [hgu] at hg ⊢
  exact eq_one_of_mem_parabolicLeviUnipotent_e7Res hu hg

end Injective

end CFSG.LieType.Chevalley.E7Levi
