module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLevi
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCShortRoot

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.ClassicalInvolution.WeakCT (torusHom LinearBlockStandardPair B12 B23)
open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ} {i j k : Fin n}

section Weyl

theorem planeWeyl_mul_planeTorusElt_left (hij : i ≠ j) (a b : Kˣ) :
    planeWeyl K n i * planeTorusElt K i j a b = planeTorusElt K i j a⁻¹ b * planeWeyl K n i := by
  simp only [planeWeyl, planeTorusElt]
  calc longBlock K n i (weylMat K) *
        (longBlock K n i (torusHom K a) * longBlock K n j (torusHom K b))
      = longBlock K n i (weylMat K * torusHom K a) * longBlock K n j (torusHom K b) := by
        rw [map_mul, mul_assoc]
    _ = longBlock K n i (torusHom K a⁻¹ * weylMat K) * longBlock K n j (torusHom K b) := by
        rw [weylMat_mul_torusHom]
    _ = longBlock K n i (torusHom K a⁻¹) *
          (longBlock K n i (weylMat K) * longBlock K n j (torusHom K b)) := by
        rw [map_mul, mul_assoc]
    _ = longBlock K n i (torusHom K a⁻¹) *
          (longBlock K n j (torusHom K b) * longBlock K n i (weylMat K)) := by
        rw [(commute_longBlock_longBlock hij (weylMat K) (torusHom K b)).eq]
    _ = longBlock K n i (torusHom K a⁻¹) * longBlock K n j (torusHom K b) *
          longBlock K n i (weylMat K) := by rw [mul_assoc]

theorem conj_planeWeyl_planeTorusElt_left (hij : i ≠ j) (a b : Kˣ) :
    planeWeyl K n i * planeTorusElt K i j a b * (planeWeyl K n i)⁻¹ =
      planeTorusElt K i j a⁻¹ b := by
  rw [planeWeyl_mul_planeTorusElt_left hij, mul_assoc, mul_inv_cancel, mul_one]

theorem planeWeyl_mem_left : planeWeyl K n i ∈ suppGroup (coords i ∪ coords j) :=
  suppGroup_mono Set.subset_union_left (isSupp_longBlock i _)

theorem shortGroupNeg_eq_conj_left (hij : i ≠ j)
    (hex : ∃ a : Kˣ, (a : K) ≠ ((a⁻¹ : Kˣ) : K)) :
    shortGroupNeg K hij =
      (shortBlock K hij).range.map (MulAut.conj (planeWeyl K n i)).toMonoidHom := by
  obtain ⟨a, ha⟩ := hex
  have ha' : ((a⁻¹ : Kˣ) : K) ≠ (((a⁻¹)⁻¹ : Kˣ) : K) := fun h => ha (by
    rw [inv_inv] at h
    exact h.symm)
  have h1 := commutator_planeTorusCent_neg hij ha'
  rw [inv_inv] at h1
  rw [← h1, ← commutator_leviCent hij ha, Subgroup.map_commutator]
  have := map_conj_inf_centralizer (suppGroup (coords i ∪ coords j)) planeWeyl_mem_left
    (planeTorusElt K i j a a)
  rw [conj_planeWeyl_planeTorusElt_left hij a a] at this
  unfold leviCent
  rw [this]

theorem commute_planeWeyl_shortBlock {k l m : Fin n} (hlm : l ≠ m) (hk : k ≠ l) (hkm : k ≠ m)
    (A : SL(2, K)) : Commute (planeWeyl K n k) (shortBlock K hlm A) :=
  (commute_shortBlock_longBlock hlm hk hkm A _).symm

theorem commute_planeWeyl_planeWeyl (hij : i ≠ j) : Commute (planeWeyl K n i) (planeWeyl K n j) :=
  commute_longBlock_longBlock hij _ _

theorem commute_planeWeyl_shortGroupNeg (hjk : j ≠ k) (hij : i ≠ j) (hik : i ≠ k) :
    ∀ y ∈ shortGroupNeg K hjk, Commute (planeWeyl K n i) y := by
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact ((commute_planeWeyl_planeWeyl hik).mul_right
    (commute_planeWeyl_shortBlock hjk hij hik A)).mul_right
      (commute_planeWeyl_planeWeyl hik).inv_right

end Weyl

theorem map_conj_eq_of_forall_commute {G : Type*} [Group G] (H : Subgroup G) {w : G}
    (hw : ∀ y ∈ H, Commute w y) : H.map (MulAut.conj w).toMonoidHom = H := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [(hw y hy).eq, mul_inv_cancel_right]
    exact hy
  · intro hx
    exact ⟨x, hx, by rw [(hw x hx).eq, mul_inv_cancel_right]⟩

section LinearPairs

@[expose] def IsLeviPair (K : Type) [Field K] {X : Type*} [Group X] (S T : Subgroup X) : Prop :=
  ∃ θ : SL(3, K) →* X, Function.Injective θ ∧ (B12 K).map θ = S ∧ (B23 K).map θ = T

theorem IsLeviPair.conj {X : Type*} [Group X] {S T : Subgroup X} (h : IsLeviPair K S T) (w : X) :
    IsLeviPair K (S.map (MulAut.conj w).toMonoidHom) (T.map (MulAut.conj w).toMonoidHom) := by
  obtain ⟨θ, hθ, hS, hT⟩ := h
  refine ⟨(MulAut.conj w).toMonoidHom.comp θ, (MulAut.conj w).injective.comp hθ, ?_, ?_⟩
  · rw [← hS, Subgroup.map_map]
  · rw [← hT, Subgroup.map_map]

theorem IsLeviPair.exists_linearBlockStandardPair_map {X Y : Type} [Group X] [Group Y]
    {S T : Subgroup X} (h : IsLeviPair K S T) (φ : X →* Y) (hφ : φ.ker ≤ Subgroup.center X) :
    ∃ W, LinearBlockStandardPair K W (S.map φ) (T.map φ) := by
  obtain ⟨θ, hθ, hS, hT⟩ := h
  refine ⟨(φ.comp θ).range, φ.comp θ, 1, rfl, ?_, Or.inl ⟨?_, ?_⟩⟩
  · intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx' : θ x ∈ Subgroup.center X := hφ (by simpa using hx)
    apply hθ
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hx' (θ y)
  · rw [map_conj_one, ← hS, Subgroup.map_map]
  · rw [map_conj_one, ← hT, Subgroup.map_map]

theorem isLeviPair_shortBlock (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    IsLeviPair K (shortBlock K hij).range (shortBlock K hjk).range := by
  refine ⟨leviSL3 K hij hjk hik, leviSL3_injective hij hjk hik, ?_, ?_⟩
  · rw [B12, ← MonoidHom.range_comp, leviSL3_comp_blockSL_zero]
  · rw [B23, ← MonoidHom.range_comp, leviSL3_comp_blockSL_one]

theorem exists_isLeviPair_short (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hex : ∃ a : Kˣ, (a : K) ≠ ((a⁻¹ : Kˣ) : K)) {S T : Subgroup (StatedSp n K)}
    (hS : S = (shortBlock K hij).range ∨ S = shortGroupNeg K hij)
    (hT : T = (shortBlock K hjk).range ∨ T = shortGroupNeg K hjk) : IsLeviPair K S T := by
  have base := isLeviPair_shortBlock (K := K) hij hjk hik
  have hwi : ∀ y ∈ (shortBlock K hjk).range, Commute (planeWeyl K n i) y := by
    rintro _ ⟨A, rfl⟩
    exact commute_planeWeyl_shortBlock hjk hij hik A
  have hwk : ∀ y ∈ (shortBlock K hij).range, Commute (planeWeyl K n k) y := by
    rintro _ ⟨A, rfl⟩
    exact commute_planeWeyl_shortBlock hij hik.symm hjk.symm A
  rcases hS with rfl | rfl <;> rcases hT with rfl | rfl
  · exact base
  · have h := base.conj (planeWeyl K n k)
    rw [map_conj_eq_of_forall_commute _ hwk] at h
    exact h
  · have h := base.conj (planeWeyl K n i)
    rw [map_conj_eq_of_forall_commute _ hwi, ← shortGroupNeg_eq_conj_left hij hex] at h
    exact h
  · have h1 := base.conj (planeWeyl K n k)
    rw [map_conj_eq_of_forall_commute _ hwk] at h1
    have h := h1.conj (planeWeyl K n i)
    have e : ((shortBlock K hjk).range.map (MulAut.conj (planeWeyl K n k)).toMonoidHom).map
        (MulAut.conj (planeWeyl K n i)).toMonoidHom = shortGroupNeg K hjk :=
      map_conj_eq_of_forall_commute (shortGroupNeg K hjk)
        (commute_planeWeyl_shortGroupNeg hjk hij hik)
    rw [e, ← shortGroupNeg_eq_conj_left hij hex] at h
    exact h

theorem exists_linearBlockStandardPair_short (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hex : ∃ a : Kˣ, (a : K) ≠ ((a⁻¹ : Kˣ) : K)) {S T : Subgroup (StatedSp n K)}
    (hS : S = (shortBlock K hij).range ∨ S = shortGroupNeg K hij)
    (hT : T = (shortBlock K hjk).range ∨ T = shortGroupNeg K hjk) :
    ∃ W, LinearBlockStandardPair K W S T := by
  have h := exists_isLeviPair_short hij hjk hik hex hS hT
  obtain ⟨W, hW⟩ := h.exists_linearBlockStandardPair_map (MonoidHom.id _) (by simp)
  rw [Subgroup.map_id, Subgroup.map_id] at hW
  exact ⟨W, hW⟩

theorem exists_linearBlockStandardPair_short_map {Y : Type} [Group Y] (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (hex : ∃ a : Kˣ, (a : K) ≠ ((a⁻¹ : Kˣ) : K))
    (φ : StatedSp n K →* Y) (hφ : φ.ker ≤ Subgroup.center (StatedSp n K))
    {S T : Subgroup (StatedSp n K)}
    (hS : S = (shortBlock K hij).range ∨ S = shortGroupNeg K hij)
    (hT : T = (shortBlock K hjk).range ∨ T = shortGroupNeg K hjk) :
    ∃ W, LinearBlockStandardPair K W (S.map φ) (T.map φ) :=
  (exists_isLeviPair_short hij hjk hik hex hS hT).exists_linearBlockStandardPair_map φ hφ

end LinearPairs

section SymplecticPairs

theorem map_conj_eq_of_mem {G : Type*} [Group G] {H : Subgroup G} {w : G} (hw : w ∈ H) :
    H.map (MulAut.conj w).toMonoidHom = H := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hw hy) (inv_mem hw)
  · intro hx
    exact ⟨w⁻¹ * x * w, mul_mem (mul_mem (inv_mem hw) hx) hw, by group⟩

theorem symplecticBlockStandardPair_shortGroupNeg (hij : i ≠ j) :
    SymplecticBlockStandardPair K ((longBlock K n j).range ⊔ shortGroupNeg K hij)
      (longBlock K n j).range (shortGroupNeg K hij) := by
  have h := symplecticBlockStandardPair_conj (K := K) hij (planeWeyl K n j)
  have hw : planeWeyl K n j ∈ (longBlock K n j).range := ⟨weylMat K, rfl⟩
  rw [Subgroup.map_sup, map_conj_eq_of_mem hw] at h
  exact h

theorem exists_symplecticBlockStandardPair_short (hij : i ≠ j) {S : Subgroup (StatedSp n K)}
    (hS : S = (shortBlock K hij).range ∨ S = shortGroupNeg K hij) :
    ∃ W, SymplecticBlockStandardPair K W (longBlock K n j).range S := by
  rcases hS with rfl | rfl
  · exact ⟨_, symplecticBlockStandardPair_longShort hij⟩
  · exact ⟨_, symplecticBlockStandardPair_shortGroupNeg hij⟩

end SymplecticPairs

section Restrict

variable {X : Type} [Group X]

theorem map_codRestrict_eq {G : Type*} [Group G] (θ : G →* X) (J : Subgroup X) (hJ : ∀ g, θ g ∈ J)
    (A : Subgroup G) : A.map (θ.codRestrict J hJ) = (A.map θ).subgroupOf J := by
  ext x
  simp only [Subgroup.mem_map, MonoidHom.codRestrict_apply, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, Subtype.ext h⟩

theorem linearBlockStandardPair_subgroupOf {W U V J : Subgroup X} (hW : W ≤ J)
    (h : LinearBlockStandardPair K W U V) :
    LinearBlockStandardPair K (W.subgroupOf J) (U.subgroupOf J) (V.subgroupOf J) := by
  obtain ⟨θ, c, hrange, hker, hUV⟩ := h
  have hJ : ∀ g, θ g ∈ J := fun g => hW (hrange ▸ ⟨g, rfl⟩)
  refine ⟨θ.codRestrict J hJ, c, ?_, ?_, ?_⟩
  · rw [← hrange]
    ext x
    simp only [MonoidHom.mem_range, MonoidHom.codRestrict_apply, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, h⟩
      exact ⟨a, Subtype.ext h⟩
  · intro x hx
    apply hker
    simpa [MonoidHom.mem_ker, Subtype.ext_iff] using hx
  · rcases hUV with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [map_codRestrict_eq, map_codRestrict_eq, h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [map_codRestrict_eq, map_codRestrict_eq, h1, h2]
      exact ⟨rfl, rfl⟩

theorem symplecticBlockStandardPair_subgroupOf {W U V J : Subgroup X} (hW : W ≤ J)
    (h : SymplecticBlockStandardPair K W U V) :
    SymplecticBlockStandardPair K (W.subgroupOf J) (U.subgroupOf J) (V.subgroupOf J) := by
  obtain ⟨θ, c, hrange, hker, hinjL, hinjS, hU, hV⟩ := h
  have hJ : ∀ g, θ g ∈ J := fun g => hW (hrange ▸ ⟨g, rfl⟩)
  refine ⟨θ.codRestrict J hJ, c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hrange]
    ext x
    simp only [MonoidHom.mem_range, MonoidHom.codRestrict_apply, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, h⟩
      exact ⟨a, Subtype.ext h⟩
  · intro x hx
    apply hker
    simpa [MonoidHom.mem_ker, Subtype.ext_iff] using hx
  · intro x y hxy
    apply hinjL
    have := congrArg Subtype.val hxy
    simpa using this
  · intro x y hxy
    apply hinjS
    have := congrArg Subtype.val hxy
    simpa using this
  · rw [map_codRestrict_eq, hU]
  · rw [map_codRestrict_eq, hV]

end Restrict

end CFSG.ClassicalInvolution.Models.SymplecticPairs
