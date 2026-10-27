module

public import CFSG.Fischer.Uniq.TauIso

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X : Type} [Group X] {E : Set X}

section Conj

theorem conj_mul_conj (g a b : X) : g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by
  group

theorem conj_commute_iff (g a b : X) :
    g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹) ↔ a * b = b * a := by
  rw [conj_mul_conj, conj_mul_conj, mul_left_inj, mul_right_inj]

theorem conj_injective (g : X) : Function.Injective fun a : X => g * a * g⁻¹ := fun a b h => by
  simpa using h

theorem Pair.conj_mem_iff (hP : Pair X E) (g : X) {a : X} : g * a * g⁻¹ ∈ E ↔ a ∈ E := by
  refine ⟨fun h => ?_, fun h => Pair.conj_mem hP h g⟩
  simpa [mul_assoc] using Pair.conj_mem hP h g⁻¹

theorem mem_localClass {e f : X} : f ∈ LocalClass E e ↔ f ∈ E ∧ f ≠ e ∧ f * e = e * f :=
  Iff.rfl

theorem Pair.conj_mem_localClass_iff (hP : Pair X E) (g : X) {e f : X} :
    g * f * g⁻¹ ∈ LocalClass E (g * e * g⁻¹) ↔ f ∈ LocalClass E e := by
  simp only [mem_localClass, Pair.conj_mem_iff hP, (conj_injective g).ne_iff, conj_commute_iff]

theorem Pair.image_conj_localClass (hP : Pair X E) (g e : X) :
    (fun f => g * f * g⁻¹) '' LocalClass E e = LocalClass E (g * e * g⁻¹) := by
  ext f
  refine ⟨?_, fun hf => ⟨g⁻¹ * f * g, ?_, by group⟩⟩
  · rintro ⟨f, hf, rfl⟩
    exact (Pair.conj_mem_localClass_iff hP g).2 hf
  · rw [← Pair.conj_mem_localClass_iff hP g]
    simpa [mul_assoc] using hf

theorem Pair.mul_mul_eq_conj (hP : Pair X E) {e : X} (he : e ∈ E) (f : X) :
    e * f * e = e * f * e⁻¹ := by
  rw [Pair.inv_eq hP he]

theorem Pair.mul_mul_mul_mul (hP : Pair X E) {e : X} (he : e ∈ E) (f : X) :
    e * (e * f * e) * e = f := by
  simp only [← mul_assoc, Pair.mul_self hP he, one_mul]
  rw [mul_assoc, Pair.mul_self hP he, mul_one]

theorem Pair.mul_mul_eq_self_iff (hP : Pair X E) {e : X} (he : e ∈ E) (f : X) :
    e * f * e = f ↔ e * f = f * e := by
  constructor
  · intro h
    calc e * f = e * f * e * e := by rw [mul_assoc (e * f), Pair.mul_self hP he, mul_one]
      _ = f * e := by rw [h]
  · intro h
    rw [h, mul_assoc, Pair.mul_self hP he, mul_one]

end Conj

section Line

theorem Pair.mul_mul_ne_left (hP : Pair X E) {e x : X} (he : e ∈ E) (hex : e * x ≠ x * e) :
    e * x * e ≠ e := by
  intro h
  apply hex
  have hxe : x = e := by rw [← Pair.mul_mul_mul_mul hP he x, h, Pair.mul_self hP he, one_mul]
  rw [hxe]

theorem Pair.mul_mul_ne_right (hP : Pair X E) {e x : X} (he : e ∈ E) (hex : e * x ≠ x * e) :
    e * x * e ≠ x :=
  fun h => hex ((Pair.mul_mul_eq_self_iff hP he x).1 h)

theorem Pair.mul_mul_not_commute_left (hP : Pair X E) {e x : X} (he : e ∈ E)
    (hex : e * x ≠ x * e) : e * x * e * e ≠ e * (e * x * e) := by
  rwa [mul_assoc (e * x), Pair.mul_self hP he, mul_one, ← mul_assoc, ← mul_assoc,
    Pair.mul_self hP he, one_mul]

theorem Pair.mul_mul_not_commute_right (hP : Pair X E) {e x : X} (he : e ∈ E) (hx : x ∈ E)
    (hex : e * x ≠ x * e) : e * x * e * x ≠ x * (e * x * e) := by
  rw [Pair.mul_mul_eq hP he hx hex, mul_assoc (x * e), Pair.mul_self hP hx, mul_one, ← mul_assoc,
    ← mul_assoc, Pair.mul_self hP hx, one_mul]
  exact fun h => hex h.symm

theorem Pair.mul_mul_conj_eq (hP : Pair X E) {e x : X} (he : e ∈ E) (hx : x ∈ E)
    (hex : e * x ≠ x * e) : x * (e * x * e) * x = e := by
  rw [Pair.mul_mul_eq hP he hx hex, Pair.mul_mul_mul_mul hP hx]

end Line

section Graph

@[expose] def commGraph (E : Set X) : SimpleGraph E where
  Adj a b := a ≠ b ∧ (a : X) * b = b * a
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp]
theorem commGraph_adj {a b : E} : (commGraph E).Adj a b ↔ a ≠ b ∧ (a : X) * b = b * a :=
  Iff.rfl

theorem commGraph_adj_iff {a b : E} :
    (commGraph E).Adj a b ↔ (a : X) ≠ b ∧ (a : X) * b = b * a := by
  rw [commGraph_adj, ne_eq, ne_eq, Subtype.ext_iff]

theorem mem_localClass_iff_adj {a b : E} : (a : X) ∈ LocalClass E b ↔ (commGraph E).Adj a b := by
  rw [commGraph_adj_iff, mem_localClass]
  exact and_iff_right a.2

theorem image_neighborSet (b : E) :
    Subtype.val '' (commGraph E).neighborSet b = LocalClass E b := by
  ext f
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact mem_localClass_iff_adj.2 ((commGraph E).adj_symm ha)
  · intro hf
    exact ⟨⟨f, hf.1⟩, (commGraph E).adj_symm (mem_localClass_iff_adj.1 hf), rfl⟩

theorem commGraph_eq_or_adj {a b : E} (h : (a : X) * b = b * a) : a = b ∨ (commGraph E).Adj a b :=
  or_iff_not_imp_left.2 fun hne => ⟨hne, h⟩

theorem commGraph_reachable_of_commute {a b : E} (h : (a : X) * b = b * a) :
    (commGraph E).Reachable a b := by
  rcases commGraph_eq_or_adj h with rfl | hab
  · rfl
  · exact hab.reachable

theorem mul_ne_mul_of_not_reachable {a b : E} (h : ¬(commGraph E).Reachable a b) :
    (a : X) * b ≠ b * a :=
  fun hab => h (commGraph_reachable_of_commute hab)

@[expose] def Pair.conjAut (hP : Pair X E) (g : X) : commGraph E ≃g commGraph E where
  toEquiv := Pair.conjPerm hP g
  map_rel_iff' {a b} := by
    change (_ ≠ _ ∧ _) ↔ (_ ≠ _ ∧ _)
    rw [(Pair.conjPerm hP g).injective.ne_iff, Pair.conjPerm_apply, Pair.conjPerm_apply,
      conj_commute_iff]

@[simp]
theorem Pair.conjAut_apply (hP : Pair X E) (g : X) (a : E) :
    (Pair.conjAut hP g a : X) = g * a * g⁻¹ :=
  rfl

theorem Pair.conjAut_toEquiv (hP : Pair X E) (g : X) :
    (Pair.conjAut hP g).toEquiv = Pair.conjPerm hP g :=
  rfl

@[simp]
theorem tauE_coe (hP : Pair X E) (e f : E) : (tauE hP e f : X) = e * f * e :=
  rfl

@[expose] def Pair.tauAut (hP : Pair X E) (e : E) : commGraph E ≃g commGraph E :=
  Pair.conjAut hP e

theorem Pair.tauAut_apply (hP : Pair X E) (e f : E) : Pair.tauAut hP e f = tauE hP e f :=
  conjPerm_eq_tau hP e f

theorem Pair.tau_adj_iff (hP : Pair X E) (e : E) {f g : E} :
    (commGraph E).Adj (tauE hP e f) (tauE hP e g) ↔ (commGraph E).Adj f g := by
  rw [← Pair.tauAut_apply, ← Pair.tauAut_apply]
  exact (Pair.tauAut hP e).map_adj_iff

@[simp]
theorem Pair.tauE_tauE (hP : Pair X E) (e f : E) : tauE hP e (tauE hP e f) = f :=
  Subtype.ext (Pair.mul_mul_mul_mul hP e.2 f)

theorem Pair.tauE_involutive (hP : Pair X E) (e : E) : Function.Involutive (tauE hP e) :=
  Pair.tauE_tauE hP e

theorem Pair.tauE_eq_self_iff (hP : Pair X E) (e f : E) :
    tauE hP e f = f ↔ (e : X) * f = f * e := by
  rw [Subtype.ext_iff, tauE_coe, Pair.mul_mul_eq_self_iff hP e.2]

@[simp]
theorem Pair.tauE_self (hP : Pair X E) (e : E) : tauE hP e e = e :=
  (Pair.tauE_eq_self_iff hP e e).2 rfl

theorem Pair.conjPerm_tauE (hP : Pair X E) (g : X) (a b : E) :
    Pair.conjPerm hP g (tauE hP a b) =
      tauE hP (Pair.conjPerm hP g a) (Pair.conjPerm hP g b) :=
  Subtype.ext (by simp only [Pair.conjPerm_apply, tauE_coe]; group)

theorem Pair.tauE_tauE_eq_conjPerm (hP : Pair X E) (e f y : E) :
    tauE hP e (tauE hP f y) = Pair.conjPerm hP ((e : X) * f) y := by
  rw [← conjPerm_eq_tau, ← conjPerm_eq_tau, ← Equiv.Perm.mul_apply, ← map_mul]

end Graph

section Triality

theorem Pair.triality_adj (hP : Pair X E) {e f y : X} (he : e ∈ E) (hf : f ∈ E) (hy : y ∈ E)
    (hef : e * f = f * e) (hne : e ≠ f) (hye : y * e ≠ e * y) (hyf : y * f ≠ f * y) :
    e * f * y * (e * f)⁻¹ ∈ LocalClass E y := by
  have hw : e * f * y * (e * f)⁻¹ = e * y * f * (e * y)⁻¹ := by
    have h := Pair.mul_mul_eq hP hf hy fun h => hyf h.symm
    rw [mul_inv_rev, mul_inv_rev, Pair.inv_eq hP he, Pair.inv_eq hP hf, Pair.inv_eq hP hy]
    calc e * f * y * (f * e) = e * (f * y * f) * e := by group
      _ = e * (y * f * y) * e := by rw [h]
      _ = e * y * f * (y * e) := by group
  have hy' : e * y * e * (e * y)⁻¹ = y := by
    rw [mul_inv_rev, Pair.inv_eq hP he, Pair.inv_eq hP hy]
    calc e * y * e * (y * e) = e * (y * e * y) * e := by group
      _ = e * (e * y * e) * e := by rw [Pair.mul_mul_eq hP he hy fun h => hye h.symm]
      _ = y := Pair.mul_mul_mul_mul hP he y
  have h := (Pair.conj_mem_localClass_iff hP (e * y)).2 ⟨hf, hne.symm, hef.symm⟩
  rwa [hy', ← hw] at h

theorem Pair.tau_tau_adj (hP : Pair X E) {e f y : E} (hef : (commGraph E).Adj e f)
    (hye : (y : X) * e ≠ e * y) (hyf : (y : X) * f ≠ f * y) :
    (commGraph E).Adj (tauE hP e (tauE hP f y)) y := by
  rw [← mem_localClass_iff_adj, Pair.tauE_tauE_eq_conjPerm, Pair.conjPerm_apply]
  exact Pair.triality_adj hP e.2 f.2 y.2 hef.2 (commGraph_adj_iff.1 hef).1 hye hyf

theorem Pair.mul_mul_commute (hP : Pair X E) {f f' y : X} (hf : f ∈ E) (hf' : f' ∈ E)
    (hy : y ∈ E) (hff' : f * f' = f' * f) (hyf : y * f ≠ f * y) (hyf' : y * f' ≠ f' * y) :
    f * y * f * (f' * y * f') = f' * y * f' * (f * y * f) := by
  rw [Pair.mul_mul_eq hP hf hy fun h => hyf h.symm, Pair.mul_mul_eq hP hf' hy fun h => hyf' h.symm]
  have h1 : ∀ a b : X, y * a * y * (y * b * y) = y * (a * b) * y := fun a b => by
    calc y * a * y * (y * b * y) = y * a * (y * y) * b * y := by group
      _ = y * (a * b) * y := by rw [Pair.mul_self hP hy, mul_one]; group
  rw [h1, h1, hff']

theorem Pair.mul_mul_mem_localClass (hP : Pair X E) {f f' y : X} (hf : f ∈ E) (hf' : f' ∈ E)
    (hy : y ∈ E) (hff' : f * f' = f' * f) (hne : f ≠ f') (hyf : y * f ≠ f * y)
    (hyf' : y * f' ≠ f' * y) : f * y * f ∈ LocalClass E (f' * y * f') := by
  refine ⟨Pair.mul_mul_mem hP hf hy, fun h => hne ?_,
    Pair.mul_mul_commute hP hf hf' hy hff' hyf hyf'⟩
  rw [Pair.mul_mul_eq hP hf hy fun h => hyf h.symm,
    Pair.mul_mul_eq hP hf' hy fun h => hyf' h.symm] at h
  simpa using h

theorem Pair.tau_adj_tau (hP : Pair X E) {f f' y : E} (hff' : (commGraph E).Adj f f')
    (hyf : (y : X) * f ≠ f * y) (hyf' : (y : X) * f' ≠ f' * y) :
    (commGraph E).Adj (tauE hP f y) (tauE hP f' y) := by
  rw [← mem_localClass_iff_adj]
  exact Pair.mul_mul_mem_localClass hP f.2 f'.2 y.2 hff'.2 (commGraph_adj_iff.1 hff').1 hyf hyf'

end Triality

end CFSG.Fischer
