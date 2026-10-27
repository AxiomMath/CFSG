module

public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.Blocks

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup MulAction

variable {α : Type} [Fintype α] [DecidableEq α]

@[expose] def fixOutside (S : Set α) : Subgroup (Perm α) where
  carrier := {g | ∀ y, y ∉ S → g y = y}
  mul_mem' {a b} ha hb y hy := by
    simp only [Set.mem_setOf_eq, Perm.mul_apply] at *
    rw [hb y hy, ha y hy]
  one_mem' _ _ := rfl
  inv_mem' {a} ha y hy := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha y hy]
    exact a.symm_apply_apply y

@[expose] def localBase (E : Subgroup (Perm α)) (x₀ : α) : Subgroup (Perm α) :=
  blockBase E ⊓ fixOutside (orbit E x₀)

section Orbit

omit [Fintype α] [DecidableEq α]

private theorem mem_orbit_iff' {E : Subgroup (Perm α)} {x y : α} :
    y ∈ orbit E x ↔ ∃ e ∈ E, e x = y := by
  constructor
  · rintro ⟨⟨e, he⟩, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨⟨e, he⟩, rfl⟩

private theorem apply_mem_orbit {E : Subgroup (Perm α)} {e : Perm α} (he : e ∈ E) {x y : α}
    (hy : y ∈ orbit E x) : e y ∈ orbit E x := by
  obtain ⟨f, hf, rfl⟩ := mem_orbit_iff'.mp hy
  exact mem_orbit_iff'.mpr ⟨e * f, E.mul_mem he hf, rfl⟩

private theorem apply_mem_orbit_iff_self {E : Subgroup (Perm α)} {e : Perm α} (he : e ∈ E)
    {x z : α} : e z ∈ orbit E x ↔ z ∈ orbit E x :=
  ⟨fun h => by simpa using apply_mem_orbit (E.inv_mem he) h, apply_mem_orbit he⟩

private theorem not_mem_of_mem_orbit {E : Subgroup (Perm α)} {x y z : α} (hx : x ∉ orbit E z)
    (hy : y ∈ orbit E x) : y ∉ orbit E z := by
  intro h
  apply hx
  rw [← orbit_eq_iff.mpr h, orbit_eq_iff.mpr hy]
  exact mem_orbit_self x

private theorem eq_on_orbit {E : Subgroup (Perm α)} (hEab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e)
    {e f : Perm α} (he : e ∈ E) (hf : f ∈ E) {x : α} (h : e x = f x) {y : α}
    (hy : y ∈ orbit E x) : e y = f y := by
  obtain ⟨g, hg, rfl⟩ := mem_orbit_iff'.mp hy
  have h1 : e (g x) = g (e x) := by
    simpa using congrArg (fun m : Perm α => m x) (hEab e he g hg)
  have h2 : f (g x) = g (f x) := by
    simpa using congrArg (fun m : Perm α => m x) (hEab f hf g hg)
  rw [h1, h2, h]

private theorem apply_mem_orbit_map_iff {E : Subgroup (Perm α)} {m : Perm α}
    (hm : ∀ e ∈ E, e * m = m * e) {x y : α} : m y ∈ orbit E (m x) ↔ y ∈ orbit E x := by
  simp only [mem_orbit_iff']
  refine exists_congr fun e => and_congr_right fun he => ?_
  have h : e (m x) = m (e x) := by simpa using congrArg (fun f : Perm α => f x) (hm e he)
  rw [h]
  exact m.injective.eq_iff

private theorem apply_mem_orbit_of_mem_normalizer {E : Subgroup (Perm α)} {n : Perm α}
    (hn : n ∈ normalizer (E : Set (Perm α))) {x y : α} (hy : y ∈ orbit E x) :
    n y ∈ orbit E (n x) := by
  obtain ⟨e, he, rfl⟩ := mem_orbit_iff'.mp hy
  refine mem_orbit_iff'.mpr ⟨n * e * n⁻¹, (mem_normalizer_iff.mp hn e).mp he, ?_⟩
  simp [Perm.mul_apply]

private noncomputable def onOrbit {E : Subgroup (Perm α)} (x₀ : α) {e : Perm α} (he : e ∈ E) :
    Perm α :=
  open Classical in
  ofSubtype (p := (· ∈ orbit E x₀))
    (e.subtypePerm (p := (· ∈ orbit E x₀)) fun _ => apply_mem_orbit_iff_self he)

private theorem onOrbit_apply_of_mem {E : Subgroup (Perm α)} {x₀ : α} {e : Perm α} (he : e ∈ E)
    {y : α} (hy : y ∈ orbit E x₀) : onOrbit x₀ he y = e y := by
  classical
  unfold onOrbit
  rw [ofSubtype_apply_of_mem _ hy]
  rfl

private theorem onOrbit_apply_of_not_mem {E : Subgroup (Perm α)} {x₀ : α} {e : Perm α}
    (he : e ∈ E) {y : α} (hy : y ∉ orbit E x₀) : onOrbit x₀ he y = y := by
  classical
  unfold onOrbit
  exact ofSubtype_apply_of_not_mem _ hy

end Orbit

omit [Fintype α] [DecidableEq α] in
private theorem mem_localBase_iff {E : Subgroup (Perm α)} {x₀ : α} {u : Perm α} :
    u ∈ localBase E x₀ ↔ u ∈ blockBase E ∧ ∀ y, y ∉ orbit E x₀ → u y = y := Iff.rfl

omit [Fintype α] [DecidableEq α] in
private theorem localBase_actsAs {E : Subgroup (Perm α)} {x₀ : α} {u : Perm α}
    (hu : u ∈ localBase E x₀) : ∃ e ∈ E, ∀ y ∈ orbit E x₀, u y = e y :=
  (mem_localBase_iff.mp hu).1 x₀

omit [Fintype α] [DecidableEq α] in
private theorem localBase_apply_mem {E : Subgroup (Perm α)} {x₀ : α} {u : Perm α}
    (hu : u ∈ localBase E x₀) {y : α} (hy : y ∈ orbit E x₀) : u y ∈ orbit E x₀ := by
  obtain ⟨e, he, hue⟩ := localBase_actsAs hu
  rw [hue y hy]
  exact apply_mem_orbit he hy

omit [Fintype α] [DecidableEq α] in
private theorem onOrbit_mem_localBase {E : Subgroup (Perm α)} {x₀ : α} {e : Perm α}
    (he : e ∈ E) : onOrbit x₀ he ∈ localBase E x₀ := by
  refine mem_localBase_iff.mpr ⟨fun x => ?_, fun y hy => onOrbit_apply_of_not_mem he hy⟩
  by_cases hx : x ∈ orbit E x₀
  · refine ⟨e, he, fun y hy => onOrbit_apply_of_mem he ?_⟩
    rwa [orbit_eq_iff.mpr hx] at hy
  · exact ⟨1, E.one_mem, fun y hy => onOrbit_apply_of_not_mem he (not_mem_of_mem_orbit hx hy)⟩

omit [Fintype α] [DecidableEq α] in
private theorem localBase_ext {E : Subgroup (Perm α)} (hEab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e)
    {x₀ : α} {u v : Perm α} (hu : u ∈ localBase E x₀) (hv : v ∈ localBase E x₀)
    (h : u x₀ = v x₀) : u = v := by
  ext z
  by_cases hz : z ∈ orbit E x₀
  · obtain ⟨f, hf, hfu⟩ := localBase_actsAs hu
    obtain ⟨g, hg, hgv⟩ := localBase_actsAs hv
    have hfg : f x₀ = g x₀ := by
      rw [← hfu x₀ (mem_orbit_self x₀), ← hgv x₀ (mem_orbit_self x₀), h]
    rw [hfu z hz, hgv z hz]
    exact eq_on_orbit hEab hf hg hfg hz
  · rw [(mem_localBase_iff.mp hu).2 z hz, (mem_localBase_iff.mp hv).2 z hz]

omit [Fintype α] [DecidableEq α] in
theorem localBase_regular {E : Subgroup (Perm α)} (hEab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e)
    (x₀ : α) {y : α} (hy : y ∈ orbit E x₀) :
    ∃! u : localBase E x₀, (u : Perm α) x₀ = y := by
  obtain ⟨e, he, rfl⟩ := mem_orbit_iff'.mp hy
  refine ⟨⟨onOrbit x₀ he, onOrbit_mem_localBase he⟩,
    onOrbit_apply_of_mem he (mem_orbit_self x₀), fun v hv => ?_⟩
  exact Subtype.ext (localBase_ext hEab v.2 (onOrbit_mem_localBase he)
    (hv.trans (onOrbit_apply_of_mem he (mem_orbit_self x₀)).symm))

omit [Fintype α] [DecidableEq α] in
theorem localBase_comm {E : Subgroup (Perm α)} (hEab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e)
    (x₀ : α) (u v : localBase E x₀) : u * v = v * u := by
  refine Subtype.ext (Equiv.ext fun z => ?_)
  by_cases hz : z ∈ orbit E x₀
  · obtain ⟨f, hf, hfu⟩ := localBase_actsAs u.2
    obtain ⟨g, hg, hgv⟩ := localBase_actsAs v.2
    have hvz : (v : Perm α) z ∈ orbit E x₀ := localBase_apply_mem v.2 hz
    have huz : (u : Perm α) z ∈ orbit E x₀ := localBase_apply_mem u.2 hz
    simp only [Subgroup.coe_mul, Perm.mul_apply]
    rw [hgv z hz, hfu _ (by rwa [← hgv z hz]), hfu z hz, hgv _ (by rwa [← hfu z hz])]
    simpa using congrArg (fun m : Perm α => m z) (hEab f hf g hg)
  · have hv := (mem_localBase_iff.mp v.2).2 z hz
    have hu := (mem_localBase_iff.mp u.2).2 z hz
    simp only [Subgroup.coe_mul, Perm.mul_apply, hu, hv]

omit [Fintype α] [DecidableEq α] in
theorem localBase_sq {E : Subgroup (Perm α)} (hE : ∀ e ∈ E, e ^ 2 = 1) (x₀ : α)
    (u : localBase E x₀) : u ^ 2 = 1 :=
  Subtype.ext (by simpa using blockBase_sq hE (mem_localBase_iff.mp u.2).1)

private noncomputable def localBaseEquiv {E : Subgroup (Perm α)}
    (hEab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e) (x₀ : α) : localBase E x₀ ≃ orbit E x₀ :=
  Equiv.ofBijective
    (fun u => ⟨(u : Perm α) x₀, localBase_apply_mem u.2 (mem_orbit_self x₀)⟩)
    ⟨fun u v h => Subtype.ext (localBase_ext hEab u.2 v.2 (congrArg Subtype.val h)),
      fun y => by
        obtain ⟨u, hu, -⟩ := localBase_regular hEab x₀ y.2
        exact ⟨u, Subtype.ext hu⟩⟩

omit [Fintype α] [DecidableEq α] in
theorem card_localBase {E : Subgroup (Perm α)} (hEab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e)
    (x₀ : α) : Nat.card (localBase E x₀) = Nat.card (orbit E x₀) :=
  Nat.card_congr (localBaseEquiv hEab x₀)

omit [Fintype α] [DecidableEq α] in
theorem conj_mem_localBase {E : Subgroup (Perm α)} {x₀ : α} {m : Perm α}
    (hm : m ∈ normalizer (E : Set (Perm α))) (hmx : m x₀ ∈ orbit E x₀) {u : Perm α}
    (hu : u ∈ localBase E x₀) : m * u * m⁻¹ ∈ localBase E x₀ := by
  refine mem_localBase_iff.mpr ⟨?_, fun y hy => ?_⟩
  · exact (mem_normalizer_iff.mp (normalizer_le_normalizer_blockBase E hm) u).mp
      (mem_localBase_iff.mp hu).1
  · have hy' : m⁻¹ y ∉ orbit E x₀ := fun h => hy (by
      have h1 := apply_mem_orbit_of_mem_normalizer hm h
      rw [orbit_eq_iff.mpr hmx] at h1
      simpa using h1)
    rw [Perm.mul_apply, Perm.mul_apply, (mem_localBase_iff.mp hu).2 _ hy']
    simp

section Affine

variable {E : Subgroup (Perm α)} (hEab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e) (x₀ : α)
  (φ : MulAut (localBase E x₀))

private noncomputable def diagBase : Perm α :=
  open Classical in
  ofSubtype (p := (· ∈ orbit E x₀))
    ((localBaseEquiv hEab x₀).symm.trans (φ.toEquiv.trans (localBaseEquiv hEab x₀)))

omit [Fintype α] [DecidableEq α] in
private theorem diagBase_apply_of_not_mem {y : α} (hy : y ∉ orbit E x₀) :
    diagBase hEab x₀ φ y = y := by
  classical
  unfold diagBase
  exact ofSubtype_apply_of_not_mem _ hy

omit [Fintype α] [DecidableEq α] in
private theorem diagBase_apply_mem {y : α} (hy : y ∈ orbit E x₀) :
    diagBase hEab x₀ φ y ∈ orbit E x₀ := by
  classical
  unfold diagBase
  rw [ofSubtype_apply_of_mem _ hy]
  exact Subtype.property _

omit [Fintype α] [DecidableEq α] in
private theorem diagBase_apply_eval (v : localBase E x₀) :
    diagBase hEab x₀ φ ((v : Perm α) x₀) = ((φ v : localBase E x₀) : Perm α) x₀ := by
  classical
  have hy : (v : Perm α) x₀ ∈ orbit E x₀ := localBase_apply_mem v.2 (mem_orbit_self x₀)
  unfold diagBase
  rw [ofSubtype_apply_of_mem _ hy]
  have h : (localBaseEquiv hEab x₀).symm ⟨(v : Perm α) x₀, hy⟩ = v :=
    (Equiv.symm_apply_eq _).mpr rfl
  simp only [Equiv.trans_apply, h]
  rfl

omit [Fintype α] [DecidableEq α] in
private theorem diagBase_mul_apply (u : localBase E x₀) (y : α) :
    diagBase hEab x₀ φ ((u : Perm α) y) =
      ((φ u : localBase E x₀) : Perm α) (diagBase hEab x₀ φ y) := by
  by_cases hy : y ∈ orbit E x₀
  · obtain ⟨v, hv, -⟩ := localBase_regular hEab x₀ hy
    rw [← hv]
    have h1 : (u : Perm α) ((v : Perm α) x₀) = ((u * v : localBase E x₀) : Perm α) x₀ := rfl
    rw [h1, diagBase_apply_eval, diagBase_apply_eval, map_mul]
    rfl
  · rw [(mem_localBase_iff.mp u.2).2 y hy, diagBase_apply_of_not_mem hEab x₀ φ hy]
    exact ((mem_localBase_iff.mp (φ u).2).2 y hy).symm

omit [Fintype α] [DecidableEq α] in
private theorem diagBase_normal {e : Perm α} (he : e ∈ E) :
    ∃ e' ∈ E, ∀ v ∈ orbit E x₀, diagBase hEab x₀ φ (e v) = e' (diagBase hEab x₀ φ v) := by
  let u : localBase E x₀ := ⟨onOrbit x₀ he, onOrbit_mem_localBase he⟩
  obtain ⟨e', he', hφ⟩ := localBase_actsAs (φ u).2
  refine ⟨e', he', fun v hv => ?_⟩
  have h1 := diagBase_mul_apply hEab x₀ φ u v
  have h2 : (u : Perm α) v = e v := onOrbit_apply_of_mem he hv
  rw [h2] at h1
  rw [h1]
  exact hφ _ (diagBase_apply_mem hEab x₀ φ hv)

end Affine

private def Reach (E K : Subgroup (Perm α)) (x₀ z : α) : Prop :=
  ∃ k ∈ K, k x₀ ∈ orbit E z

open Classical in
private noncomputable def transporter (E K : Subgroup (Perm α)) (x₀ : α) (S : Set α) : Perm α :=
  if S = orbit E x₀ then 1 else if h : ∃ k ∈ K, k x₀ ∈ S then h.choose else 1

private theorem transporter_spec {E K : Subgroup (Perm α)} {x₀ : α} {S : Set α}
    (h : ∃ k ∈ K, k x₀ ∈ S) : transporter E K x₀ S ∈ K ∧ transporter E K x₀ S x₀ ∈ S := by
  by_cases h1 : S = orbit E x₀
  · subst h1
    simp only [transporter, if_true]
    exact ⟨K.one_mem, mem_orbit_self x₀⟩
  · simp only [transporter, h1, if_false, dif_pos h]
    exact h.choose_spec

private noncomputable abbrev blockShift (E K : Subgroup (Perm α)) (x₀ z : α) : Perm α :=
  transporter E K x₀ (orbit E z)

private theorem blockShift_self (E K : Subgroup (Perm α)) (x₀ : α) : blockShift E K x₀ x₀ = 1 := by
  simp [blockShift, transporter]

open Classical in
private noncomputable def dFun (E K : Subgroup (Perm α)) (x₀ : α) (p : Perm α) (z : α) : α :=
  if Reach E K x₀ z then blockShift E K x₀ z (p ((blockShift E K x₀ z)⁻¹ z)) else z

private structure DiagData (E K : Subgroup (Perm α)) (x₀ : α) (p : Perm α) : Prop where
  ab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e
  central : ∀ e ∈ E, ∀ k ∈ K, e * k = k * e
  maps : ∀ v ∈ orbit E x₀, p v ∈ orbit E x₀
  normal : ∀ e ∈ E, ∃ e' ∈ E, ∀ v ∈ orbit E x₀, p (e v) = e' (p v)

section Generic

omit [Fintype α] [DecidableEq α]

variable {E K : Subgroup (Perm α)} {x₀ : α} {p : Perm α}

private theorem DiagData.apply_mem_orbit_iff (hD : DiagData E K x₀ p) {k : Perm α} (hk : k ∈ K)
    {x y : α} : k y ∈ orbit E (k x) ↔ y ∈ orbit E x :=
  apply_mem_orbit_map_iff fun e he => hD.central e he k hk

private theorem DiagData.inv_apply_mem_orbit_iff (hD : DiagData E K x₀ p) {k : Perm α}
    (hk : k ∈ K) {x y : α} : k⁻¹ y ∈ orbit E x ↔ y ∈ orbit E (k x) := by
  simpa using (hD.apply_mem_orbit_iff hk (x := x) (y := k⁻¹ y)).symm

private theorem DiagData.comm_apply (hD : DiagData E K x₀ p) {e k : Perm α} (he : e ∈ E)
    (hk : k ∈ K) (z : α) : k (e z) = e (k z) := by
  simpa using (congrArg (fun f : Perm α => f z) (hD.central e he k hk)).symm

private theorem DiagData.exists_actsAs (hD : DiagData E K x₀ p) {t : Perm α} (ht : t ∈ K)
    (htx : t x₀ ∈ orbit E x₀) : ∃ e ∈ E, ∀ v ∈ orbit E x₀, t v = e v := by
  obtain ⟨e₀, he₀, h₀⟩ := mem_orbit_iff'.mp htx
  refine ⟨e₀, he₀, fun v hv => ?_⟩
  obtain ⟨e, he, rfl⟩ := mem_orbit_iff'.mp hv
  rw [hD.comm_apply he ht, ← h₀]
  simpa using congrArg (fun f : Perm α => f x₀) (hD.ab e he e₀ he₀)

private theorem reach_of_orbit_eq {z z' : α} (h : orbit E z' = orbit E z) :
    Reach E K x₀ z' ↔ Reach E K x₀ z := by
  unfold Reach
  rw [h]

private theorem DiagData.reach_apply (hD : DiagData E K x₀ p) {k : Perm α} (hk : k ∈ K)
    {z : α} : Reach E K x₀ (k z) ↔ Reach E K x₀ z := by
  constructor
  · rintro ⟨k', hk', h'⟩
    refine ⟨k⁻¹ * k', K.mul_mem (K.inv_mem hk) hk', ?_⟩
    simpa [Perm.mul_apply] using (hD.inv_apply_mem_orbit_iff hk).mpr h'
  · rintro ⟨k', hk', h'⟩
    exact ⟨k * k', K.mul_mem hk hk', (hD.apply_mem_orbit_iff hk).mpr h'⟩

private theorem DiagData.comm_block_aux (hD : DiagData E K x₀ p) {k κ₁ κ₂ : Perm α} (hk : k ∈ K)
    (hκ₁ : κ₁ ∈ K) (hκ₂ : κ₂ ∈ K) (htx : (κ₂⁻¹ * k * κ₁) x₀ ∈ orbit E x₀) :
    ∃ e ∈ E, ∀ v ∈ orbit E x₀, κ₂ (p (κ₂⁻¹ (k (κ₁ v)))) = e (k (κ₁ (p v))) := by
  obtain ⟨et, het, hte⟩ := hD.exists_actsAs (K.mul_mem (K.mul_mem (K.inv_mem hκ₂) hk) hκ₁) htx
  obtain ⟨e', he', hpe⟩ := hD.normal et het
  refine ⟨e' * et⁻¹, E.mul_mem he' (E.inv_mem het), fun v hv => ?_⟩
  have h1 : κ₂⁻¹ (k (κ₁ v)) = et v := hte v hv
  have h2 : k (κ₁ (p v)) = κ₂ (et (p v)) := by
    rw [← hte _ (hD.maps v hv)]
    simp [Perm.mul_apply]
  rw [h1, hpe v hv, h2, hD.comm_apply het hκ₂, hD.comm_apply he' hκ₂]
  simp [Perm.mul_apply]

end Generic

section Transport

variable {E K : Subgroup (Perm α)} {x₀ : α} {p : Perm α}

private theorem blockShift_mem {z : α} (hz : Reach E K x₀ z) : blockShift E K x₀ z ∈ K :=
  (transporter_spec hz).1

private theorem blockShift_apply_mem {z : α} (hz : Reach E K x₀ z) :
    blockShift E K x₀ z x₀ ∈ orbit E z :=
  (transporter_spec hz).2

private theorem blockShift_congr {z z' : α} (h : orbit E z = orbit E z') :
    blockShift E K x₀ z = blockShift E K x₀ z' := by
  unfold blockShift
  rw [h]

private theorem DiagData.mem_orbit_iff_blockShift (hD : DiagData E K x₀ p) {z : α}
    (hz : Reach E K x₀ z) {y : α} : y ∈ orbit E z ↔ (blockShift E K x₀ z)⁻¹ y ∈ orbit E x₀ := by
  rw [← orbit_eq_iff.mpr (blockShift_apply_mem hz)]
  exact (hD.inv_apply_mem_orbit_iff (blockShift_mem hz)).symm

private theorem dFun_of_not_reach {z : α} (hz : ¬ Reach E K x₀ z) : dFun E K x₀ p z = z := by
  unfold dFun
  rw [if_neg hz]

private theorem dFun_of_reach {z : α} (hz : Reach E K x₀ z) :
    dFun E K x₀ p z = blockShift E K x₀ z (p ((blockShift E K x₀ z)⁻¹ z)) := by
  unfold dFun
  rw [if_pos hz]

private theorem DiagData.dFun_mem_orbit (hD : DiagData E K x₀ p) (z : α) :
    dFun E K x₀ p z ∈ orbit E z := by
  by_cases hz : Reach E K x₀ z
  · rw [dFun_of_reach hz, hD.mem_orbit_iff_blockShift hz]
    simpa using hD.maps _ ((hD.mem_orbit_iff_blockShift hz).mp (mem_orbit_self z))
  · rw [dFun_of_not_reach hz]
    exact mem_orbit_self z

private theorem DiagData.dFun_injective (hD : DiagData E K x₀ p) :
    Function.Injective (dFun E K x₀ p) := by
  intro z z' h
  have h1 : orbit E z = orbit E z' := by
    have a := hD.dFun_mem_orbit z
    rw [h] at a
    exact (orbit_eq_iff.mpr a).symm.trans (orbit_eq_iff.mpr (hD.dFun_mem_orbit z'))
  by_cases hz : Reach E K x₀ z
  · have hz' : Reach E K x₀ z' := (reach_of_orbit_eq h1.symm).mpr hz
    rw [dFun_of_reach hz, dFun_of_reach hz', blockShift_congr h1] at h
    exact ((blockShift E K x₀ z')⁻¹).injective (p.injective ((blockShift E K x₀ z').injective h))
  · have hz' : ¬ Reach E K x₀ z' := fun h' => hz ((reach_of_orbit_eq h1.symm).mp h')
    rwa [dFun_of_not_reach hz, dFun_of_not_reach hz'] at h

end Transport

section Lift

variable {E K : Subgroup (Perm α)} {x₀ : α} {p : Perm α}

private noncomputable def dPerm (hD : DiagData E K x₀ p) : Perm α :=
  Equiv.ofBijective (dFun E K x₀ p) (Finite.injective_iff_bijective.mp hD.dFun_injective)

private theorem dPerm_apply (hD : DiagData E K x₀ p) (z : α) :
    dPerm hD z = dFun E K x₀ p z := rfl

private theorem DiagData.dPerm_mem_blockKer (hD : DiagData E K x₀ p) : dPerm hD ∈ blockKer E :=
  fun x => hD.dFun_mem_orbit x

private theorem DiagData.dPerm_apply_of_orbit (hD : DiagData E K x₀ p) {x : α}
    (hx : Reach E K x₀ x) {u : α} (hu : u ∈ orbit E x) :
    dPerm hD u = blockShift E K x₀ x (p ((blockShift E K x₀ x)⁻¹ u)) := by
  have h1 : orbit E u = orbit E x := orbit_eq_iff.mpr hu
  rw [dPerm_apply, dFun_of_reach ((reach_of_orbit_eq h1).mpr hx), blockShift_congr h1]

private theorem DiagData.dPerm_apply_of_base (hD : DiagData E K x₀ p) {y : α}
    (hy : y ∈ orbit E x₀) : dPerm hD y = p y := by
  have h1 : orbit E y = orbit E x₀ := orbit_eq_iff.mpr hy
  have hreach : Reach E K x₀ y := ⟨1, K.one_mem, by rw [h1]; exact mem_orbit_self x₀⟩
  rw [dPerm_apply, dFun_of_reach hreach, blockShift_congr h1, blockShift_self]
  simp

private theorem DiagData.dPerm_comm_block_reach (hD : DiagData E K x₀ p) {k : Perm α}
    (hk : k ∈ K) {x : α} (hx : Reach E K x₀ x) :
    ∃ e ∈ E, ∀ u ∈ orbit E x, dPerm hD (k u) = e (k (dPerm hD u)) := by
  have hkx : Reach E K x₀ (k x) := (hD.reach_apply hk).mpr hx
  have htx : ((blockShift E K x₀ (k x))⁻¹ * k * blockShift E K x₀ x) x₀ ∈ orbit E x₀ := by
    have h2 : k (blockShift E K x₀ x x₀) ∈ orbit E (k x) :=
      (hD.apply_mem_orbit_iff hk).mpr (blockShift_apply_mem hx)
    simpa [Perm.mul_apply] using (hD.mem_orbit_iff_blockShift hkx).mp h2
  obtain ⟨e, he, hev⟩ := hD.comm_block_aux hk (blockShift_mem hx) (blockShift_mem hkx) htx
  refine ⟨e, he, fun u hu => ?_⟩
  have hv : (blockShift E K x₀ x)⁻¹ u ∈ orbit E x₀ := (hD.mem_orbit_iff_blockShift hx).mp hu
  have hku : k u ∈ orbit E (k x) := (hD.apply_mem_orbit_iff hk).mpr hu
  rw [hD.dPerm_apply_of_orbit hkx hku, hD.dPerm_apply_of_orbit hx hu]
  simpa using hev _ hv

private theorem DiagData.dPerm_comm_block (hD : DiagData E K x₀ p) {k : Perm α} (hk : k ∈ K)
    (x : α) : ∃ e ∈ E, ∀ u ∈ orbit E x, dPerm hD (k u) = e (k (dPerm hD u)) := by
  by_cases hx : Reach E K x₀ x
  · exact hD.dPerm_comm_block_reach hk hx
  · refine ⟨1, E.one_mem, fun u hu => ?_⟩
    have hu' : ¬ Reach E K x₀ u := fun h => hx ((reach_of_orbit_eq (orbit_eq_iff.mpr hu)).mp h)
    have hku : ¬ Reach E K x₀ (k u) := fun h => hu' ((hD.reach_apply hk).mp h)
    rw [dPerm_apply, dPerm_apply, dFun_of_not_reach hu', dFun_of_not_reach hku]
    rfl

private theorem DiagData.comm_mem_blockBase (hD : DiagData E K x₀ p) {k : Perm α} (hk : k ∈ K) :
    dPerm hD * k * (dPerm hD)⁻¹ * k⁻¹ ∈ blockBase E := by
  intro x
  obtain ⟨e, he, h⟩ := hD.dPerm_comm_block hk (k⁻¹ x)
  refine ⟨e, he, fun y hy => ?_⟩
  have hy1 : k⁻¹ y ∈ orbit E (k⁻¹ x) := (hD.apply_mem_orbit_iff (K.inv_mem hk)).mpr hy
  have hu : (dPerm hD)⁻¹ (k⁻¹ y) ∈ orbit E (k⁻¹ x) := by
    have h2 : (dPerm hD)⁻¹ (k⁻¹ y) ∈ orbit E (k⁻¹ y) :=
      (blockKer E).inv_mem hD.dPerm_mem_blockKer (k⁻¹ y)
    rwa [orbit_eq_iff.mpr hy1] at h2
  simpa [Perm.mul_apply] using h _ hu

private theorem DiagData.dPerm_mem_normalizer (hD : DiagData E K x₀ p) (hBK : blockBase E ≤ K) :
    dPerm hD ∈ normalizer (K : Set (Perm α)) := by
  refine mem_normalizer_fintype fun n hn => ?_
  have h := K.mul_mem (hBK (hD.comm_mem_blockBase hn)) hn
  simpa [mul_assoc] using h

private theorem DiagData.dPerm_localBase (hD : DiagData E K x₀ p) {u v : Perm α}
    (hu : u ∈ localBase E x₀) (hv : v ∈ localBase E x₀) (huv : ∀ y, p (u y) = v (p y))
    (y : α) : dPerm hD (u y) = v (dPerm hD y) := by
  by_cases hy : y ∈ orbit E x₀
  · rw [hD.dPerm_apply_of_base (localBase_apply_mem hu hy), hD.dPerm_apply_of_base hy, huv]
  · have hd : dPerm hD y ∈ orbit E y := hD.dFun_mem_orbit y
    rw [(mem_localBase_iff.mp hu).2 y hy,
      (mem_localBase_iff.mp hv).2 _ (not_mem_of_mem_orbit hy hd)]

end Lift

theorem exists_diag {E K : Subgroup (Perm α)} (hEab : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e)
    (hEK : ∀ e ∈ E, ∀ k ∈ K, e * k = k * e) (hEleK : E ≤ K) (hBK : blockBase E ≤ K)
    (x₀ : α) (φ : MulAut (localBase E x₀)) :
    ∃ d : Perm α, d ∈ blockKer E ∧ d ∈ normalizer (K : Set (Perm α)) ∧
      (∀ u : localBase E x₀, d * (u : Perm α) * d⁻¹ = (φ u : Perm α)) ∧
      (∀ y, (∀ k ∈ K, k x₀ ∉ orbit E y) → d y = y) := by
  have _ := hEleK
  have hD : DiagData E K x₀ (diagBase hEab x₀ φ) :=
    ⟨hEab, hEK, fun v hv => diagBase_apply_mem hEab x₀ φ hv, fun e he =>
      diagBase_normal hEab x₀ φ he⟩
  refine ⟨dPerm hD, hD.dPerm_mem_blockKer, hD.dPerm_mem_normalizer hBK, fun u => ?_,
    fun y hy => ?_⟩
  · rw [mul_inv_eq_iff_eq_mul]
    exact Equiv.ext fun y =>
      hD.dPerm_localBase u.2 (φ u).2 (diagBase_mul_apply hEab x₀ φ u) y
  · have hy' : ¬ Reach E K x₀ y := fun ⟨k, hk, h⟩ => hy k hk h
    exact (dPerm_apply hD y).trans (dFun_of_not_reach hy')

end CFSG.GroupTheory.AltCore
