module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCBShearAxis
public import CFSG.LocalAnalysis.ComponentInitial.PerfectFixedCentralQuotient

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.Assembly

variable {G : Type*} [Group G]

structure CyclicFourInversionConfig (Q : Sylow 2 G) (A : Subgroup G) (x t v : G) : Prop where
  le_Q : A ≤ (Q : Subgroup G)
  x_mem : x ∈ (Q : Subgroup G)
  x_not_mem : x ∉ A
  x_mul_x : x * x = 1
  mem_cases : ∀ q ∈ (Q : Subgroup G), q ∈ A ∨ ∃ b ∈ A, q = b * x
  comm : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b
  conj_mem : ∀ b ∈ A, x * b * x⁻¹ ∈ A
  fixed_iff : ∀ b ∈ A, x * b * x⁻¹ = b ↔ b ∈ ({1, t, v, t * v} : Set G)
  t_mem : t ∈ A
  v_mem : v ∈ A
  t_mul_t : t * t = 1
  v_mul_v : v * v = 1
  t_comm_v : t * v = v * t
  t_ne_one : t ≠ 1
  v_ne_one : v ≠ 1
  v_ne_t : v ≠ t
  sq_eq_t : ∀ b ∈ A, b * b ≠ 1 → b * b * (b * b) = 1 → b * b = t
  exists_sqrt : ∃ r ∈ A, r * r = t ∧ x * r * x⁻¹ = r⁻¹
  exists_shift : ∃ p ∈ A, x * p * x⁻¹ = v * p
  outside_sq : ∀ b ∈ A, b * x * (b * x) = 1 ∨ b * x * (b * x) = v
  normalizer_le : Subgroup.normalizer ((Q : Subgroup G) : Set G) ≤
    Subgroup.centralizer ({t} : Set G)

theorem nonempty_mulEquiv_zmod_prod_of_commute [Finite G] {D : Subgroup G} {y u : G} {m k : ℕ}
    (hy : orderOf y = m) (hu : orderOf u = k) (hyu : Commute y u)
    (hdisj : Subgroup.zpowers y ⊓ Subgroup.zpowers u = ⊥) (hyD : y ∈ D) (huD : u ∈ D)
    (hD : Nat.card D ≤ m * k) :
    Nonempty (D ≃* Multiplicative (ZMod m) × Multiplicative (ZMod k)) := by
  let f : Subgroup.zpowers y × Subgroup.zpowers u →* G :=
    MonoidHom.noncommCoprod (Subgroup.zpowers y).subtype (Subgroup.zpowers u).subtype
      (by
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact hyu.zpow_zpow i j)
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ hab
    change a * b = 1 at hab
    have hab' : a = b⁻¹ := eq_inv_of_mul_eq_one_left hab
    have hmem : a ∈ Subgroup.zpowers y ⊓ Subgroup.zpowers u :=
      ⟨ha, hab' ▸ (Subgroup.zpowers u).inv_mem hb⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    have hb1 : b = 1 := by
      have := hab' ▸ hmem
      exact inv_eq_one.mp this
    ext <;> simp [hmem, hb1]
  have hfrange : f.range ≤ D := by
    rintro _ ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩
    change a * b ∈ D
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact D.mul_mem (D.zpow_mem hyD i) (D.zpow_mem huD j)
  have hcardprod : Nat.card (Subgroup.zpowers y × Subgroup.zpowers u) = m * k := by
    rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, hy, hu]
  have hrangeEq : f.range = D :=
    Subgroup.eq_of_le_of_card_ge hfrange (by
      rw [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv, hcardprod]
      exact hD)
  have hcyc : ∀ (z : G) (n : ℕ), orderOf z = n →
      Nonempty (Subgroup.zpowers z ≃* Multiplicative (ZMod n)) := by
    intro z n hz
    have hcard : Nat.card (Subgroup.zpowers z) = n := by rw [Nat.card_zpowers, hz]
    exact ⟨((zmodCyclicMulEquiv inferInstance).symm).trans
      (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hcard).toAddEquiv)⟩
  obtain ⟨ey⟩ := hcyc y m hy
  obtain ⟨eu⟩ := hcyc u k hu
  exact ⟨((MulEquiv.subgroupCongr hrangeEq).symm.trans
    (MonoidHom.ofInjective hfinj).symm).trans (MulEquiv.prodCongr ey eu)⟩

namespace CyclicFourInversionConfig

variable {Q : Sylow 2 G} {A : Subgroup G} {x t v : G}

section

variable (h : CyclicFourInversionConfig Q A x t v)
include h

theorem inv_x : x⁻¹ = x := inv_eq_of_mul_eq_one_right h.x_mul_x

theorem conj_inv_eq (b : G) : x⁻¹ * b * x = x * b * x⁻¹ := by
  rw [h.inv_x]

theorem F_mem_A {f : G} (hf : f ∈ ({1, t, v, t * v} : Set G)) : f ∈ A := by
  rcases hf with rfl | rfl | rfl | rfl
  · exact A.one_mem
  · exact h.t_mem
  · exact h.v_mem
  · exact A.mul_mem h.t_mem h.v_mem

theorem fixed_of_mem_F {f : G} (hf : f ∈ ({1, t, v, t * v} : Set G)) : x * f * x⁻¹ = f :=
  (h.fixed_iff f (h.F_mem_A hf)).2 hf

theorem mul_mem_F {f f' : G} (hf : f ∈ ({1, t, v, t * v} : Set G))
    (hf' : f' ∈ ({1, t, v, t * v} : Set G)) : f * f' ∈ ({1, t, v, t * v} : Set G) := by
  refine (h.fixed_iff _ (A.mul_mem (h.F_mem_A hf) (h.F_mem_A hf'))).1 ?_
  calc x * (f * f') * x⁻¹ = (x * f * x⁻¹) * (x * f' * x⁻¹) := by group
    _ = f * f' := by rw [h.fixed_of_mem_F hf, h.fixed_of_mem_F hf']

theorem inv_mem_F {f : G} (hf : f ∈ ({1, t, v, t * v} : Set G)) :
    f⁻¹ ∈ ({1, t, v, t * v} : Set G) := by
  refine (h.fixed_iff _ (A.inv_mem (h.F_mem_A hf))).1 ?_
  calc x * f⁻¹ * x⁻¹ = (x * f * x⁻¹)⁻¹ := by group
    _ = f⁻¹ := by rw [h.fixed_of_mem_F hf]

theorem mul_self_of_mem_F {f : G} (hf : f ∈ ({1, t, v, t * v} : Set G)) : f * f = 1 := by
  rcases hf with rfl | rfl | rfl | rfl
  · exact mul_one 1
  · exact h.t_mul_t
  · exact h.v_mul_v
  · calc t * v * (t * v) = t * (v * t) * v := by group
      _ = 1 := by rw [← h.t_comm_v, ← mul_assoc, h.t_mul_t, one_mul, h.v_mul_v]

omit h in
theorem t_mem_F (_h : CyclicFourInversionConfig Q A x t v) : t ∈ ({1, t, v, t * v} : Set G) := by
  simp

omit h in
theorem v_mem_F (_h : CyclicFourInversionConfig Q A x t v) : v ∈ ({1, t, v, t * v} : Set G) := by
  simp

theorem closure_eq_F :
    ((Subgroup.closure {t, v} : Subgroup G) : Set G) = {1, t, v, t * v} := by
  ext f
  constructor
  · intro hf
    change f ∈ Subgroup.closure _ at hf
    induction hf using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact h.t_mem_F
      · exact h.v_mem_F
    | one => exact Set.mem_insert _ _
    | mul a b _ _ ha hb => exact h.mul_mem_F ha hb
    | inv a _ ha => exact h.inv_mem_F ha
  · intro hf
    change f ∈ Subgroup.closure _
    have ht : t ∈ Subgroup.closure ({t, v} : Set G) := Subgroup.subset_closure (by simp)
    have hv : v ∈ Subgroup.closure ({t, v} : Set G) := Subgroup.subset_closure (by simp)
    rcases hf with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact ht
    · exact hv
    · exact Subgroup.mul_mem _ ht hv

theorem ncard_F : ({1, t, v, t * v} : Set G).ncard = 4 := by
  have htv1 : t * v ≠ 1 := fun e => h.v_ne_t (by
    calc v = t * (t * v) := by rw [← mul_assoc, h.t_mul_t, one_mul]
      _ = t := by rw [e, mul_one])
  have htvt : t * v ≠ t := fun e => h.v_ne_one (by simpa using e)
  have htvv : t * v ≠ v := fun e => h.t_ne_one (by simpa using e)
  rw [Set.ncard_insert_of_notMem (by simp [h.t_ne_one.symm, h.v_ne_one.symm, htv1.symm]),
    Set.ncard_insert_of_notMem (by simp [h.v_ne_t.symm, htvt.symm]),
    Set.ncard_insert_of_notMem (by simp [htvv.symm]), Set.ncard_singleton]

theorem conj_outside {q : G} (hq : q ∈ (Q : Subgroup G)) (hqA : q ∉ A) {b : G} (hb : b ∈ A) :
    q * b * q⁻¹ = x * b * x⁻¹ := by
  rcases h.mem_cases q hq with hqA' | ⟨c, hc, rfl⟩
  · exact absurd hqA' hqA
  · calc c * x * b * (c * x)⁻¹ = c * (x * b * x⁻¹) * c⁻¹ := by group
      _ = x * b * x⁻¹ := by rw [h.comm c hc _ (h.conj_mem b hb), mul_inv_cancel_right]

theorem inv_mul_mem {q q' : G} (hq : q ∈ (Q : Subgroup G)) (hqA : q ∉ A)
    (hq' : q' ∈ (Q : Subgroup G)) (hq'A : q' ∉ A) : q⁻¹ * q' ∈ A := by
  rcases h.mem_cases q hq with h1 | ⟨c, hc, rfl⟩
  · exact absurd h1 hqA
  rcases h.mem_cases q' hq' with h2 | ⟨c', hc', rfl⟩
  · exact absurd h2 hq'A
  have e : (c * x)⁻¹ * (c' * x) = x⁻¹ * (c⁻¹ * c') * x := by group
  rw [e, h.conj_inv_eq]
  exact h.conj_mem _ (A.mul_mem (A.inv_mem hc) hc')

theorem F_comm {f : G} (hf : f ∈ ({1, t, v, t * v} : Set G)) {q : G}
    (hq : q ∈ (Q : Subgroup G)) : q * f = f * q := by
  have hfA := h.F_mem_A hf
  rcases h.mem_cases q hq with hqA | ⟨c, hc, rfl⟩
  · exact h.comm q hqA f hfA
  · calc c * x * f = c * (x * f * x⁻¹) * x := by group
      _ = c * f * x := by rw [h.fixed_of_mem_F hf]
      _ = f * (c * x) := by rw [h.comm c hc f hfA, mul_assoc]

theorem conj_of_mem_A {y : G} (hy : y ∈ (Q : Subgroup G)) (hyA : y ∉ A) {q : G} (hq : q ∈ A) :
    q * y * q⁻¹ = q * (x * q * x⁻¹)⁻¹ * y := by
  have e := h.conj_outside hy hyA (A.inv_mem hq)
  calc q * y * q⁻¹ = q * (y * q⁻¹ * y⁻¹) * y := by group
    _ = q * (x * q⁻¹ * x⁻¹) * y := by rw [e]
    _ = q * (x * q * x⁻¹)⁻¹ * y := by group

theorem central_fusion [Finite G] {g : G} (hg : g⁻¹ * t * g ∈ ({1, t, v, t * v} : Set G)) :
    g⁻¹ * t * g = t := by
  set z := g⁻¹ * t * g with hz
  set C := Subgroup.centralizer ({z} : Set G) with hC
  have hQC : (Q : Subgroup G) ≤ C := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.2 (h.F_comm hg hq)
  have hQ'C : ((g⁻¹ • Q : Sylow 2 G) : Subgroup G) ≤ C := by
    intro u hu
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply, inv_inv] at hu
    have hcomm := h.F_comm h.t_mem_F hu
    rw [Subgroup.mem_centralizer_singleton_iff, hz]
    calc u * (g⁻¹ * t * g) = g⁻¹ * ((g * u * g⁻¹) * t) * g := by group
      _ = g⁻¹ * (t * (g * u * g⁻¹)) * g := by rw [hcomm]
      _ = g⁻¹ * t * g * u := by group
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C ((g⁻¹ • Q).subtype hQ'C) (Q.subtype hQC)
  have hk : (c : G) * g⁻¹ ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) := by
    refine mem_normalizer_of_forall_conj_mem fun q hq => ?_
    have hq' : g⁻¹ * q * g ∈ ((g⁻¹ • Q : Sylow 2 G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        MulAut.smul_def, MulAut.conj_inv_apply, inv_inv]
      simpa [mul_assoc] using hq
    have h1 : (⟨g⁻¹ * q * g, hQ'C hq'⟩ : C) ∈
        (((g⁻¹ • Q).subtype hQ'C : Sylow 2 C) : Subgroup C) := by
      rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
      exact hq'
    have h2 : MulAut.conj c • (⟨g⁻¹ * q * g, hQ'C hq'⟩ : C) ∈
        ((Q.subtype hQC : Sylow 2 C) : Subgroup C) := by
      rw [← hc, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf, MulAut.smul_def, MulAut.conj_apply] at h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    have e : (c : G) * g⁻¹ * q * ((c : G) * g⁻¹)⁻¹ = (c : G) * (g⁻¹ * q * g) * (c : G)⁻¹ := by
      group
    rw [e]
    exact h2
  have hkt := Subgroup.mem_centralizer_singleton_iff.1 (h.normalizer_le hk)
  have hcz : (c : G) * z = z * c := Subgroup.mem_centralizer_singleton_iff.1 c.2
  calc z = (c : G) * z * (c : G)⁻¹ := by rw [hcz, mul_inv_cancel_right]
    _ = (c : G) * g⁻¹ * t * g * (c : G)⁻¹ := by rw [hz]; group
    _ = t * ((c : G) * g⁻¹) * g * (c : G)⁻¹ := by rw [hkt]
    _ = t := by group

theorem central_fusion' [Finite G] {n : G} (hn : n * t * n⁻¹ ∈ ({1, t, v, t * v} : Set G)) :
    n * t * n⁻¹ = t := by
  have := h.central_fusion (g := n⁻¹) (by rwa [inv_inv])
  rwa [inv_inv] at this

variable {D : Subgroup G}

theorem F_le (hDQ : D ≤ (Q : Subgroup G))
    (hcen : (Q : Subgroup G) ⊓ Subgroup.centralizer (D : Set G) ≤ D) {f : G}
    (hf : f ∈ ({1, t, v, t * v} : Set G)) : f ∈ D :=
  hcen ⟨h.le_Q (h.F_mem_A hf), Subgroup.mem_centralizer_iff.2 fun _ hd => h.F_comm hf (hDQ hd)⟩

theorem eq_A_of_le (hcen : (Q : Subgroup G) ⊓ Subgroup.centralizer (D : Set G) ≤ D)
    (hDA : D ≤ A) : D = A :=
  le_antisymm hDA fun b hb => hcen ⟨h.le_Q hb,
    Subgroup.mem_centralizer_iff.2 fun d hd => h.comm d (hDA hd) b hb⟩

theorem conj_t_of_mem_normalizer_A {n : G} (hn : n ∈ Subgroup.normalizer (A : Set G)) :
    n * t * n⁻¹ = t := by
  obtain ⟨r, hrA, hrt, -⟩ := h.exists_sqrt
  have hb : n * r * n⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hn r).1 hrA
  have hbb : n * r * n⁻¹ * (n * r * n⁻¹) = n * t * n⁻¹ := by rw [← hrt]; group
  have h1 : n * r * n⁻¹ * (n * r * n⁻¹) ≠ 1 := by
    rw [hbb]
    intro e
    apply h.t_ne_one
    calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
      _ = 1 := by rw [e]; group
  have h2 : n * r * n⁻¹ * (n * r * n⁻¹) * (n * r * n⁻¹ * (n * r * n⁻¹)) = 1 := by
    rw [hbb]
    calc n * t * n⁻¹ * (n * t * n⁻¹) = n * (t * t) * n⁻¹ := by group
      _ = 1 := by rw [h.t_mul_t]; group
  rw [← hbb]
  exact h.sq_eq_t _ hb h1 h2

theorem center_iff_of_big (hDQ : D ≤ (Q : Subgroup G))
    (hcen : (Q : Subgroup G) ⊓ Subgroup.centralizer (D : Set G) ≤ D) {y : G} (hyD : y ∈ D)
    (hyA : y ∉ A) {b₀ : G} (hb₀D : b₀ ∈ D) (hb₀A : b₀ ∈ A)
    (hb₀F : b₀ ∉ ({1, t, v, t * v} : Set G)) {z : G} :
    (z ∈ D ∧ ∀ d ∈ D, d * z = z * d) ↔ z ∈ ({1, t, v, t * v} : Set G) := by
  constructor
  · rintro ⟨hzD, hz⟩
    have hzA : z ∈ A := by
      by_contra hzA
      apply hb₀F
      refine (h.fixed_iff b₀ hb₀A).1 ?_
      rw [← h.conj_outside (hDQ hzD) hzA hb₀A, ← hz b₀ hb₀D, mul_inv_cancel_right]
    refine (h.fixed_iff z hzA).1 ?_
    rw [← h.conj_outside (hDQ hyD) hyA hzA, hz y hyD, mul_inv_cancel_right]
  · intro hzF
    exact ⟨h.F_le hDQ hcen hzF, fun d hd => h.F_comm hzF (hDQ hd)⟩

theorem mem_cases_of_small (hDQ : D ≤ (Q : Subgroup G)) {y : G} (hyD : y ∈ D) (hyA : y ∉ A)
    (hB : ∀ b ∈ D, b ∈ A → b ∈ ({1, t, v, t * v} : Set G)) {d : G} (hd : d ∈ D) :
    d ∈ ({1, t, v, t * v} : Set G) ∨ ∃ f ∈ ({1, t, v, t * v} : Set G), d = y * f := by
  by_cases hdA : d ∈ A
  · exact Or.inl (hB d hd hdA)
  · exact Or.inr ⟨y⁻¹ * d, hB _ (D.mul_mem (D.inv_mem hyD) hd)
      (h.inv_mul_mem (hDQ hyD) hyA (hDQ hd) hdA), by group⟩

theorem comm_of_small (hDQ : D ≤ (Q : Subgroup G)) {y : G} (hyD : y ∈ D) (hyA : y ∉ A)
    (hB : ∀ b ∈ D, b ∈ A → b ∈ ({1, t, v, t * v} : Set G)) {d₁ d₂ : G} (hd₁ : d₁ ∈ D)
    (hd₂ : d₂ ∈ D) : d₁ * d₂ = d₂ * d₁ := by
  have hy : ∀ d ∈ D, y * d = d * y := fun d hd => by
    rcases h.mem_cases_of_small hDQ hyD hyA hB hd with hdF | ⟨f, hf, rfl⟩
    · exact h.F_comm hdF (hDQ hyD)
    · rw [mul_assoc, h.F_comm hf (hDQ hyD)]
  rcases h.mem_cases_of_small hDQ hyD hyA hB hd₁ with hdF | ⟨f, hf, rfl⟩
  · exact (h.F_comm hdF (hDQ hd₂)).symm
  · rw [mul_assoc, (h.F_comm hf (hDQ hd₂)).symm, ← mul_assoc, hy d₂ hd₂, mul_assoc]

theorem card_of_small (hDQ : D ≤ (Q : Subgroup G))
    (hcen : (Q : Subgroup G) ⊓ Subgroup.centralizer (D : Set G) ≤ D) {y : G} (hyD : y ∈ D)
    (hyA : y ∉ A) (hB : ∀ b ∈ D, b ∈ A → b ∈ ({1, t, v, t * v} : Set G)) :
    Nat.card D = 8 := by
  have hset : (D : Set G) = {1, t, v, t * v} ∪ (fun f => y * f) '' {1, t, v, t * v} := by
    ext d
    constructor
    · intro hd
      rcases h.mem_cases_of_small hDQ hyD hyA hB hd with hdF | ⟨f, hf, rfl⟩
      · exact Or.inl hdF
      · exact Or.inr ⟨f, hf, rfl⟩
    · rintro (hdF | ⟨f, hf, rfl⟩)
      · exact h.F_le hDQ hcen hdF
      · exact D.mul_mem hyD (h.F_le hDQ hcen hf)
  have hdisj : Disjoint ({1, t, v, t * v} : Set G) ((fun f => y * f) '' {1, t, v, t * v}) := by
    rw [Set.disjoint_left]
    rintro _ hdF ⟨f, hf, rfl⟩
    apply hyA
    have := A.mul_mem (h.F_mem_A hdF) (A.inv_mem (h.F_mem_A hf))
    rwa [mul_inv_cancel_right] at this
  have hfin : ({1, t, v, t * v} : Set G).Finite := Set.toFinite _
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset,
    Set.ncard_union_eq hdisj hfin (hfin.image _),
    Set.ncard_image_of_injective _ (mul_right_injective y), h.ncard_F]

theorem outside_sq' {y : G} (hy : y ∈ (Q : Subgroup G)) (hyA : y ∉ A) :
    y * y = 1 ∨ y * y = v := by
  rcases h.mem_cases y hy with h1 | ⟨b, hb, rfl⟩
  · exact absurd h1 hyA
  · exact h.outside_sq b hb

theorem translations (hDQ : D ≤ (Q : Subgroup G)) {y : G} (hyD : y ∈ D) (hyA : y ∉ A)
    {f₁ : G} (hf₁ : f₁ ∈ ({1, t, v, t * v} : Set G)) :
    ∃ k ∈ A, ∀ f ∈ ({1, t, v, t * v} : Set G), k * (y * f) * k⁻¹ = y * (f₁ * f) := by
  have hyQ := hDQ hyD
  obtain ⟨r, hrA, hrt, hrx⟩ := h.exists_sqrt
  obtain ⟨p, hpA, hpx⟩ := h.exists_shift
  have hr : ∀ f ∈ ({1, t, v, t * v} : Set G), r * (y * f) * r⁻¹ = y * (t * f) := fun f hf => by
    have e := h.conj_of_mem_A hyQ hyA hrA
    rw [hrx, inv_inv, hrt] at e
    have hrf : r * f = f * r := h.comm r hrA f (h.F_mem_A hf)
    calc r * (y * f) * r⁻¹ = (r * y * r⁻¹) * (r * f * r⁻¹) := by group
      _ = t * y * f := by rw [e, hrf, mul_inv_cancel_right]
      _ = y * (t * f) := by rw [← h.F_comm h.t_mem_F hyQ, mul_assoc]
  have hp : ∀ f ∈ ({1, t, v, t * v} : Set G), p * (y * f) * p⁻¹ = y * (v * f) := fun f hf => by
    have e := h.conj_of_mem_A hyQ hyA hpA
    rw [hpx, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul,
      inv_eq_of_mul_eq_one_right h.v_mul_v] at e
    have hpf : p * f = f * p := h.comm p hpA f (h.F_mem_A hf)
    calc p * (y * f) * p⁻¹ = (p * y * p⁻¹) * (p * f * p⁻¹) := by group
      _ = v * y * f := by rw [e, hpf, mul_inv_cancel_right]
      _ = y * (v * f) := by rw [← h.F_comm h.v_mem_F hyQ, mul_assoc]
  rcases hf₁ with rfl | rfl | rfl | rfl
  · exact ⟨1, A.one_mem, fun f _ => by group⟩
  · exact ⟨r, hrA, hr⟩
  · exact ⟨p, hpA, hp⟩
  · refine ⟨p * r, A.mul_mem hpA hrA, fun f hf => ?_⟩
    have e : p * r * (y * f) * (p * r)⁻¹ = p * (r * (y * f) * r⁻¹) * p⁻¹ := by group
    rw [e, hr f hf, hp _ (h.mul_mem_F h.t_mem_F hf), ← mul_assoc v t f, ← h.t_comm_v]

theorem mem_normalizer_of_translation [Finite G] (hDQ : D ≤ (Q : Subgroup G))
    (hcen : (Q : Subgroup G) ⊓ Subgroup.centralizer (D : Set G) ≤ D) {y : G} (hyD : y ∈ D)
    (hyA : y ∉ A) (hB : ∀ b ∈ D, b ∈ A → b ∈ ({1, t, v, t * v} : Set G)) {k f₁ : G}
    (hkA : k ∈ A) (hf₁ : f₁ ∈ ({1, t, v, t * v} : Set G))
    (hk : ∀ f ∈ ({1, t, v, t * v} : Set G), k * (y * f) * k⁻¹ = y * (f₁ * f)) :
    k ∈ Subgroup.normalizer (D : Set G) := by
  refine mem_normalizer_of_forall_conj_mem fun d hd => ?_
  rcases h.mem_cases_of_small hDQ hyD hyA hB hd with hdF | ⟨f, hf, rfl⟩
  · rw [h.comm k hkA d (h.F_mem_A hdF), mul_inv_cancel_right]
    exact hd
  · rw [hk f hf]
    exact D.mul_mem hyD (h.F_le hDQ hcen (h.mul_mem_F hf₁ hf))

theorem conj_t_of_elementary [Finite G] (hDQ : D ≤ (Q : Subgroup G))
    (hcen : (Q : Subgroup G) ⊓ Subgroup.centralizer (D : Set G) ≤ D) {y : G} (hyD : y ∈ D)
    (hyA : y ∉ A) (hB : ∀ b ∈ D, b ∈ A → b ∈ ({1, t, v, t * v} : Set G)) {n : G}
    (hn : n ∈ Subgroup.normalizer (D : Set G)) : n * t * n⁻¹ = t := by
  set N := Subgroup.normalizer (D : Set G) with hN
  have hconjD : ∀ m ∈ N, ∀ d ∈ D, m * d * m⁻¹ ∈ D := fun m hm d hd =>
    (Subgroup.mem_normalizer_iff.1 hm d).1 hd
  have htD : t ∈ D := h.F_le hDQ hcen h.t_mem_F
  by_contra hnt
  obtain ⟨f₀, hf₀, he₀⟩ : ∃ f₀ ∈ ({1, t, v, t * v} : Set G), n * t * n⁻¹ = y * f₀ := by
    rcases h.mem_cases_of_small hDQ hyD hyA hB (hconjD n hn t htD) with hF | hyf
    · exact absurd (h.central_fusion' hF) hnt
    · exact hyf
  have horbit : ∀ f ∈ ({1, t, v, t * v} : Set G), ∃ m ∈ N, m * t * m⁻¹ = y * f := by
    intro f hf
    have hf₁ : f * f₀ ∈ ({1, t, v, t * v} : Set G) := h.mul_mem_F hf hf₀
    obtain ⟨k, hkA, hk⟩ := h.translations hDQ hyD hyA hf₁
    have hkN := h.mem_normalizer_of_translation hDQ hcen hyD hyA hB hkA hf₁ hk
    refine ⟨k * n, N.mul_mem hkN hn, ?_⟩
    calc k * n * t * (k * n)⁻¹ = k * (n * t * n⁻¹) * k⁻¹ := by group
      _ = y * (f * f₀ * f₀) := by rw [he₀, hk f₀ hf₀]
      _ = y * f := by rw [mul_assoc f, h.mul_self_of_mem_F hf₀, mul_one]
  have hpair : ∀ m ∈ N, ∀ w ∈ ({v, t * v} : Set G),
      m * w * m⁻¹ = v ∨ m * w * m⁻¹ = t * v := by
    intro m hm w hw
    have hwF : w ∈ ({1, t, v, t * v} : Set G) := by
      rcases hw with rfl | rfl <;> simp
    have hwt : w ≠ t := by
      rcases hw with rfl | rfl
      · exact h.v_ne_t
      · exact fun e => h.v_ne_one (by simpa using e)
    have hw1 : w ≠ 1 := by
      rcases hw with rfl | rfl
      · exact h.v_ne_one
      · intro e
        apply h.v_ne_t
        calc v = t * (t * v) := by rw [← mul_assoc, h.t_mul_t, one_mul]
          _ = t := by rw [e, mul_one]
    rcases h.mem_cases_of_small hDQ hyD hyA hB (hconjD m hm w (h.F_le hDQ hcen hwF)) with
      hF | ⟨f, hf, hfe⟩
    · rcases hF with e | e | e | e
      · exact absurd (by
          calc w = m⁻¹ * (m * w * m⁻¹) * m := by group
            _ = 1 := by rw [e]; group) hw1
      · refine absurd ?_ hwt
        have := h.central_fusion (g := m) (by
          rw [show m⁻¹ * t * m = w by rw [← e]; group]; exact hwF)
        rw [← this, ← e]; group
      · exact Or.inl e
      · exact Or.inr e
    · obtain ⟨m', hm', hm'e⟩ := horbit f hf
      refine absurd ?_ hwt
      have hw' : w = (m'⁻¹ * m)⁻¹ * t * (m'⁻¹ * m) := by
        calc w = m⁻¹ * (m * w * m⁻¹) * m := by group
          _ = m⁻¹ * (m' * t * m'⁻¹) * m := by rw [hfe, hm'e]
          _ = (m'⁻¹ * m)⁻¹ * t * (m'⁻¹ * m) := by group
      rw [hw']
      exact h.central_fusion (by rw [← hw']; exact hwF)
  have hv := hpair n hn v (by simp)
  have htv := hpair n hn (t * v) (by simp)
  have hinj : n * v * n⁻¹ ≠ n * (t * v) * n⁻¹ := fun e => h.t_ne_one (by
    have e' : v = t * v := by simpa using e
    simpa using e'.symm)
  have hprod : n * t * n⁻¹ = n * v * n⁻¹ * (n * (t * v) * n⁻¹) := by
    calc n * t * n⁻¹ = n * (v * (t * v)) * n⁻¹ := by
          rw [show v * (t * v) = t by rw [h.t_comm_v, ← mul_assoc, h.v_mul_v, one_mul]]
      _ = n * v * n⁻¹ * (n * (t * v) * n⁻¹) := by group
  apply hnt
  rw [hprod]
  rcases hv with hv | hv <;> rcases htv with htv | htv
  · exact absurd (hv.trans htv.symm) hinj
  · rw [hv, htv, ← mul_assoc, ← h.t_comm_v, mul_assoc, h.v_mul_v, mul_one]
  · rw [hv, htv, mul_assoc, h.v_mul_v, mul_one]
  · exact absurd (hv.trans htv.symm) hinj

end

variable (h : CyclicFourInversionConfig Q A x t v)
include h

theorem centric_conclusions [Finite G] {D : Subgroup G} (hDQ : D ≤ (Q : Subgroup G))
    (hcen : (Q : Subgroup G) ⊓ Subgroup.centralizer (D : Set G) ≤ D) :
    Subgroup.normalizer (D : Set G) ≤ Subgroup.centralizer ({t} : Set G) ∧
      (¬ IsMulCommutative D →
        (Subgroup.center D).map D.subtype = Subgroup.closure {t, v}) ∧
      (IsMulCommutative D → D = A ∨
        ∃ y ∈ (Q : Subgroup G), y ∉ A ∧ D = Subgroup.closure {t, v} ⊔ Subgroup.zpowers y ∧
          ((Nonempty (D ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 2)) ∧
              Subgroup.closure {d : G | d ∈ D ∧ orderOf d = 2} = Subgroup.closure {t, v}) ∨
            (IsElemAbelian 2 D ∧ Nat.card D = 8))) := by
  have hcentral : ∀ n ∈ Subgroup.normalizer (D : Set G), n * t * n⁻¹ = t →
      n ∈ Subgroup.centralizer ({t} : Set G) := fun n _ e =>
    Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 e)
  have hFset := h.closure_eq_F
  by_cases hDA : D ≤ A
  ·
    have hDeq := h.eq_A_of_le hcen hDA
    refine ⟨fun n hn => hcentral n hn (h.conj_t_of_mem_normalizer_A (hDeq ▸ hn)), ?_,
      fun _ => Or.inl hDeq⟩
    intro hnc
    exact absurd ⟨⟨fun a b => Subtype.ext (h.comm _ (hDA a.2) _ (hDA b.2))⟩⟩ hnc
  obtain ⟨y, hyD, hyA⟩ := Set.not_subset.1 hDA
  have hyQ := hDQ hyD
  by_cases hB : ∀ b ∈ D, b ∈ A → b ∈ ({1, t, v, t * v} : Set G)
  ·
    have hcomm := fun d₁ (hd₁ : d₁ ∈ D) d₂ (hd₂ : d₂ ∈ D) =>
      h.comm_of_small hDQ hyD hyA hB hd₁ hd₂
    have hab : IsMulCommutative D := ⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩
    have hcard := h.card_of_small hDQ hcen hyD hyA hB
    have hDsup : D = Subgroup.closure {t, v} ⊔ Subgroup.zpowers y := by
      refine le_antisymm (fun d hd => ?_) (sup_le ?_ (Subgroup.zpowers_le.2 hyD))
      · rcases h.mem_cases_of_small hDQ hyD hyA hB hd with hdF | ⟨f, hf, rfl⟩
        · refine Subgroup.mem_sup_left ?_
          rw [← SetLike.mem_coe, hFset]
          exact hdF
        · rw [h.F_comm hf hyQ]
          refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_)
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
          rw [← SetLike.mem_coe, hFset]
          exact hf
      · rw [Subgroup.closure_le]
        rintro _ (rfl | rfl)
        · exact h.F_le hDQ hcen h.t_mem_F
        · exact h.F_le hDQ hcen h.v_mem_F
    rcases h.outside_sq' hyQ hyA with hy2 | hy2
    ·
      refine ⟨fun n hn => hcentral n hn (h.conj_t_of_elementary hDQ hcen hyD hyA hB hn),
        fun hnc => absurd hab hnc, fun _ => Or.inr ⟨y, hyQ, hyA, hDsup, Or.inr ⟨⟨hab, ?_⟩,
          hcard⟩⟩⟩
      intro d hd
      rw [sq]
      rcases h.mem_cases_of_small hDQ hyD hyA hB hd with hdF | ⟨f, hf, rfl⟩
      · exact h.mul_self_of_mem_F hdF
      · calc y * f * (y * f) = y * (f * y) * f := by group
          _ = y * y * (f * f) := by rw [← h.F_comm hf hyQ]; group
          _ = 1 := by rw [hy2, h.mul_self_of_mem_F hf, one_mul]
    ·
      have hinvol : ∀ d ∈ D, d * d = 1 → d ∈ ({1, t, v, t * v} : Set G) := by
        intro d hd hdd
        rcases h.mem_cases_of_small hDQ hyD hyA hB hd with hdF | ⟨f, hf, rfl⟩
        · exact hdF
        · exfalso
          apply h.v_ne_one
          calc v = y * y * (f * f) := by rw [hy2, h.mul_self_of_mem_F hf, mul_one]
            _ = y * (f * y) * f := by rw [← h.F_comm hf hyQ]; group
            _ = y * f * (y * f) := by group
            _ = 1 := hdd
      refine ⟨fun n hn => hcentral n hn (h.central_fusion' (hinvol _ ?_ ?_)),
        fun hnc => absurd hab hnc, fun _ => Or.inr ⟨y, hyQ, hyA, hDsup, Or.inl ⟨?_, ?_⟩⟩⟩
      · exact (Subgroup.mem_normalizer_iff.1 hn t).1 (h.F_le hDQ hcen h.t_mem_F)
      · calc n * t * n⁻¹ * (n * t * n⁻¹) = n * (t * t) * n⁻¹ := by group
          _ = 1 := by rw [h.t_mul_t]; group
      ·
        have hy4 : orderOf y = 4 := by
          have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := y)
            (by rw [pow_one, sq, hy2]; exact h.v_ne_one)
            (by rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 by norm_num, pow_mul,
              show y ^ 2 = v by rw [sq, hy2], sq, h.v_mul_v])
          simpa using this
        have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [sq, h.t_mul_t]) h.t_ne_one
        have hdisj : Subgroup.zpowers y ⊓ Subgroup.zpowers t = ⊥ := by
          rw [eq_bot_iff]
          rintro u ⟨hu₁, hu₂⟩
          rw [Subgroup.mem_bot]
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu₂
          obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hu₁
          have htj : t ^ j = t ^ (j % 2) := by rw [← zpow_mod_orderOf t j, ht2]; norm_num
          have hyi : y ^ i = y ^ (i % 4) := by rw [← zpow_mod_orderOf y i, hy4]; norm_num
          rw [htj] at hi ⊢
          rw [hyi] at hi
          have hj : j % 2 = 0 ∨ j % 2 = 1 := by omega
          rcases hj with hj | hj
          · rw [hj, zpow_zero]
          · exfalso
            rw [hj, zpow_one] at hi
            have hi4 : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
            rcases hi4 with e | e | e | e <;> rw [e] at hi
            · rw [zpow_zero] at hi
              exact h.t_ne_one hi.symm
            · rw [zpow_one] at hi
              exact hyA (hi ▸ h.t_mem)
            · rw [zpow_two, hy2] at hi
              exact h.v_ne_t hi
            · have e3 : y ^ (3 : ℤ) = y * v := by
                rw [show (3 : ℤ) = 1 + 2 by norm_num, zpow_add, zpow_one, zpow_two, hy2]
              rw [e3] at hi
              apply hyA
              have := A.mul_mem (hi ▸ h.t_mem : y * v ∈ A) (A.inv_mem h.v_mem)
              rwa [mul_inv_cancel_right] at this
        exact nonempty_mulEquiv_zmod_prod_of_commute hy4 ht2
          (hcomm y hyD t (h.F_le hDQ hcen h.t_mem_F)) hdisj hyD (h.F_le hDQ hcen h.t_mem_F)
          (by rw [hcard])
      ·
        apply le_antisymm
        · rw [Subgroup.closure_le]
          rintro d ⟨hd, hd2⟩
          rw [hFset]
          exact hinvol d hd (by rw [← sq, ← hd2, pow_orderOf_eq_one])
        · rw [Subgroup.closure_le]
          rintro _ (rfl | rfl)
          · exact Subgroup.subset_closure ⟨h.F_le hDQ hcen h.t_mem_F,
              orderOf_eq_prime (by rw [sq, h.t_mul_t]) h.t_ne_one⟩
          · exact Subgroup.subset_closure ⟨h.F_le hDQ hcen h.v_mem_F,
              orderOf_eq_prime (by rw [sq, h.v_mul_v]) h.v_ne_one⟩
  ·
    push Not at hB
    obtain ⟨b₀, hb₀D, hb₀A, hb₀F⟩ := hB
    have hcenter : ∀ z, (z ∈ D ∧ ∀ d ∈ D, d * z = z * d) ↔ z ∈ ({1, t, v, t * v} : Set G) :=
      fun z => h.center_iff_of_big hDQ hcen hyD hyA hb₀D hb₀A hb₀F
    have hnab : ¬ IsMulCommutative D := by
      intro hab
      have hyF := (hcenter y).1 ⟨hyD, fun d hd =>
        congrArg Subtype.val (hab.is_comm.comm ⟨d, hd⟩ ⟨y, hyD⟩)⟩
      exact hyA (h.F_mem_A hyF)
    refine ⟨fun n hn => hcentral n hn (h.central_fusion' ((hcenter _).1 ⟨?_, ?_⟩)),
      fun _ => ?_, fun hab => absurd hab hnab⟩
    · exact (Subgroup.mem_normalizer_iff.1 hn t).1 (h.F_le hDQ hcen h.t_mem_F)
    · intro d hd
      have hd' : n⁻¹ * d * n ∈ D := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) d).1 hd
        simpa using this
      have hcomm := ((hcenter t).2 h.t_mem_F).2 _ hd'
      calc d * (n * t * n⁻¹) = n * ((n⁻¹ * d * n) * t) * n⁻¹ := by group
        _ = n * (t * (n⁻¹ * d * n)) * n⁻¹ := by rw [hcomm]
        _ = n * t * n⁻¹ * d := by group
    · ext z
      rw [mem_map_center_iff, hcenter, ← SetLike.mem_coe, hFset]

end CyclicFourInversionConfig

end CFSG.LocalAnalysis.ComponentInitial
