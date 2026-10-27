module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourExactModel
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open Subgroup Matrix
open CFSG.ComponentClassification.PSL3Four CFSG.ComponentClassification.PSL3Four.F4

section Central

variable {E P : Type*} [Group E] [Group P]

theorem commutator_mul_central {a b z w : E} (hz : ∀ g : E, z * g = g * z)
    (hw : ∀ g : E, w * g = g * w) :
    a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (z * (b * w * z⁻¹)) * a⁻¹ * (w⁻¹ * b⁻¹) := by group
    _ = a * (b * w * z⁻¹ * z) * a⁻¹ * (w⁻¹ * b⁻¹) := by rw [hz (b * w * z⁻¹)]
    _ = a * (b * (w * (a⁻¹ * w⁻¹))) * b⁻¹ := by group
    _ = a * (b * (a⁻¹ * w⁻¹ * w)) * b⁻¹ := by rw [hw (a⁻¹ * w⁻¹)]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem central_of_map_commute {π : E →* P} (hK : π.ker ≤ center E) {c y : E}
    (hc : π c * π y = π y * π c) : ∀ g : E, c⁻¹ * y⁻¹ * c * y * g = g * (c⁻¹ * y⁻¹ * c * y) := by
  have hm : c⁻¹ * y⁻¹ * c * y ∈ center E := hK (by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_assoc _ (π c), hc]
    group)
  exact fun g => (mem_center_iff.mp hm g).symm

theorem commute_commutator_of_map {π : E →* P} (hK : π.ker ≤ center E) {a b y : E}
    (ha : π a * π y = π y * π a) (hb : π b * π y = π y * π b) :
    a * b * a⁻¹ * b⁻¹ * y = y * (a * b * a⁻¹ * b⁻¹) := by
  have key : y⁻¹ * (a * b * a⁻¹ * b⁻¹) * y = a * b * a⁻¹ * b⁻¹ := by
    have h1 : y⁻¹ * (a * b * a⁻¹ * b⁻¹) * y =
        a * (a⁻¹ * y⁻¹ * a * y) * (b * (b⁻¹ * y⁻¹ * b * y)) * (a * (a⁻¹ * y⁻¹ * a * y))⁻¹ *
          (b * (b⁻¹ * y⁻¹ * b * y))⁻¹ := by group
    rw [h1, commutator_mul_central (central_of_map_commute hK ha)
      (central_of_map_commute hK hb)]
  calc a * b * a⁻¹ * b⁻¹ * y = y * (y⁻¹ * (a * b * a⁻¹ * b⁻¹) * y) := by group
    _ = y * (a * b * a⁻¹ * b⁻¹) := by rw [key]

theorem comap_comm_of_commutators {π : E →* P} (hπ : Function.Surjective π)
    (hK : π.ker ≤ center E) {V : Subgroup P}
    (hV : ∀ v ∈ V, ∃ p q : P, (∀ w ∈ V, p * w = w * p) ∧ (∀ w ∈ V, q * w = w * q) ∧
      v = p * q * p⁻¹ * q⁻¹) :
    ∀ x ∈ V.comap π, ∀ y ∈ V.comap π, x * y = y * x := by
  intro x hx y hy
  obtain ⟨p, q, hp, hq, hpq⟩ := hV (π x) hx
  obtain ⟨a, rfl⟩ := hπ p
  obtain ⟨b, rfl⟩ := hπ q
  have hk : (a * b * a⁻¹ * b⁻¹)⁻¹ * x ∈ center E := hK (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpq]
    simp only [map_mul, map_inv, inv_mul_cancel])
  have hcomm := commute_commutator_of_map hK (hp (π y) hy) (hq (π y) hy)
  have hx' : x = a * b * a⁻¹ * b⁻¹ * ((a * b * a⁻¹ * b⁻¹)⁻¹ * x) := by group
  rw [hx']
  calc a * b * a⁻¹ * b⁻¹ * ((a * b * a⁻¹ * b⁻¹)⁻¹ * x) * y
      = a * b * a⁻¹ * b⁻¹ * (((a * b * a⁻¹ * b⁻¹)⁻¹ * x) * y) := mul_assoc _ _ _
    _ = a * b * a⁻¹ * b⁻¹ * (y * ((a * b * a⁻¹ * b⁻¹)⁻¹ * x)) := by
      rw [(mem_center_iff.mp hk y)]
    _ = a * b * a⁻¹ * b⁻¹ * y * ((a * b * a⁻¹ * b⁻¹)⁻¹ * x) := (mul_assoc _ _ _).symm
    _ = y * (a * b * a⁻¹ * b⁻¹) * ((a * b * a⁻¹ * b⁻¹)⁻¹ * x) := by rw [hcomm]
    _ = y * (a * b * a⁻¹ * b⁻¹ * ((a * b * a⁻¹ * b⁻¹)⁻¹ * x)) := mul_assoc _ _ _

theorem mul_rearrange_six {a b c d e f : E} (hbc : b * c = c * b) (hbe : b * e = e * b)
    (hde : d * e = e * d) : a * b * (c * d) * (e * f) = a * c * e * (b * d * f) := by
  calc a * b * (c * d) * (e * f) = a * (b * c) * d * e * f := by group
    _ = a * (c * b) * d * e * f := by rw [hbc]
    _ = a * c * b * (d * e) * f := by group
    _ = a * c * b * (e * d) * f := by rw [hde]
    _ = a * c * (b * e) * d * f := by group
    _ = a * c * (e * b) * d * f := by rw [hbe]
    _ = a * c * e * (b * d * f) := by group

theorem exists_cube [Finite E] (K : Subgroup E) (hcomm : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x)
    (h3 : ∀ z ∈ K, z ^ 3 = 1 → z = 1) : ∀ z ∈ K, ∃ c ∈ K, c ^ 3 = z := by
  let f : K → K := fun c => c ^ 3
  have hinj : Function.Injective f := by
    intro c d hcd
    have hcd' : (c : E) ^ 3 = (d : E) ^ 3 := congrArg Subtype.val hcd
    have hc : Commute (c : E) (d : E)⁻¹ :=
      (hcomm c c.2 (d : E)⁻¹ (inv_mem d.2))
    have h1 : ((c : E) * (d : E)⁻¹) ^ 3 = 1 := by
      rw [hc.mul_pow, inv_pow, hcd', mul_inv_cancel]
    have h2 := h3 _ (mul_mem c.2 (inv_mem d.2)) h1
    exact Subtype.ext (mul_inv_eq_one.mp h2)
  intro z hz
  obtain ⟨c, hc⟩ := Finite.surjective_of_injective hinj ⟨z, hz⟩
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

theorem exists_split [Finite E] {π : E →* P} (hπ : Function.Surjective π)
    (hK : π.ker ≤ center E) (h3 : ∀ z ∈ π.ker, z ^ 3 = 1 → z = 1) {V : Subgroup P}
    (hV : ∀ v ∈ V, ∃ p q : P, (∀ w ∈ V, p * w = w * p) ∧ (∀ w ∈ V, q * w = w * q) ∧
      v = p * q * p⁻¹ * q⁻¹)
    {h : P} (hhV : ∀ v ∈ V, h * v * h⁻¹ ∈ V)
    (hN : ∀ v ∈ V, v * (h * v * h⁻¹) * (h * (h * v * h⁻¹) * h⁻¹) = 1) :
    ∃ Y : Subgroup E, Y ⊓ π.ker = ⊥ ∧ Y.map π = V ∧ ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := by
  obtain ⟨k, hk⟩ := hπ h
  have hab := comap_comm_of_commutators hπ hK hV
  have hσV : ∀ x ∈ V.comap π, k * x * k⁻¹ ∈ V.comap π := by
    intro x hx
    rw [mem_comap, map_mul, map_mul, map_inv, hk]
    exact hhV _ hx
  set N : E → E := fun x => x * (k * x * k⁻¹) * (k * (k * x * k⁻¹) * k⁻¹) with hNdef
  have hNmul : ∀ x ∈ V.comap π, ∀ y ∈ V.comap π, N (x * y) = N x * N y := by
    intro x hx y hy
    have e1 : k * (x * y) * k⁻¹ = k * x * k⁻¹ * (k * y * k⁻¹) := by group
    have e2 : k * (k * x * k⁻¹ * (k * y * k⁻¹)) * k⁻¹ =
        k * (k * x * k⁻¹) * k⁻¹ * (k * (k * y * k⁻¹) * k⁻¹) := by group
    simp only [hNdef]
    rw [e1, e2]
    exact mul_rearrange_six (hab _ hy _ (hσV _ hx)) (hab _ hy _ (hσV _ (hσV _ hx)))
      (hab _ (hσV _ hy) _ (hσV _ (hσV _ hx)))
  have hNker : ∀ x ∈ V.comap π, N x ∈ π.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    simp only [hNdef, map_mul, map_inv, hk]
    exact hN _ hx
  have hNcen : ∀ z ∈ π.ker, N z = z ^ 3 := by
    intro z hz
    have hc := mem_center_iff.mp (hK hz)
    have hkz : k * z * k⁻¹ = z := by rw [hc k, mul_inv_cancel_right]
    simp only [hNdef]
    rw [hkz, hkz, pow_three, mul_assoc]
  have hkerV : π.ker ≤ V.comap π := fun z hz => by
    rw [mem_comap, (MonoidHom.mem_ker).mp hz]
    exact one_mem V
  have hN1 : N 1 = 1 := by simp only [hNdef]; group
  let Y : Subgroup E :=
    { carrier := {x | x ∈ V.comap π ∧ N x = 1}
      one_mem' := ⟨one_mem _, hN1⟩
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
        rw [hNmul _ hx.1 _ hy.1, hx.2, hy.2, one_mul]⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by
        have h := hNmul _ (inv_mem hx.1) _ hx.1
        rw [inv_mul_cancel, hN1, hx.2, mul_one] at h
        exact h.symm⟩ }
  refine ⟨Y, ?_, ?_, fun x hx y hy => hab x hx.1 y hy.1⟩
  · rw [eq_bot_iff]
    rintro z ⟨⟨-, hzN⟩, hz⟩
    rw [hNcen z hz] at hzN
    exact h3 z hz hzN
  · refine le_antisymm (map_le_iff_le_comap.mpr fun x hx => hx.1) fun v hv => ?_
    obtain ⟨x, rfl⟩ := hπ v
    have hx : x ∈ V.comap π := hv
    have hcomm : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a * b = b * a := fun a ha b _ =>
      (mem_center_iff.mp (hK ha) b).symm
    have h3' : ∀ z ∈ π.ker, z ^ 3 = 1 → z = 1 := h3
    obtain ⟨c, hc, hc3⟩ := exists_cube π.ker hcomm h3' (N x) (hNker x hx)
    refine ⟨x * c⁻¹, ⟨mul_mem hx (hkerV (inv_mem hc)), ?_⟩, ?_⟩
    · rw [hNmul _ hx _ (hkerV (inv_mem hc)), hNcen _ (inv_mem hc), inv_pow, hc3,
        mul_inv_cancel]
    · rw [map_mul, map_inv, (MonoidHom.mem_ker).mp hc, inv_one, mul_one]

end Central

@[expose] def x01M (c : F4) : Matrix (Fin 3) (Fin 3) F4 := 1 + Matrix.single 0 1 c

@[expose] def x02M (c : F4) : Matrix (Fin 3) (Fin 3) F4 := 1 + Matrix.single 0 2 c

@[expose] def x21M (c : F4) : Matrix (Fin 3) (Fin 3) F4 := 1 + Matrix.single 2 1 c

@[expose] def hM : Matrix (Fin 3) (Fin 3) F4 := Matrix.diagonal ![ω, ω * ω, 1]

@[expose] def hiM : Matrix (Fin 3) (Fin 3) F4 := Matrix.diagonal ![ω * ω, ω, 1]

theorem det_x01M : ∀ c : F4, (x01M c).det = 1 := by
  intro c
  rw [Matrix.det_fin_three]
  revert c
  decide

theorem det_x02M : ∀ c : F4, (x02M c).det = 1 := by
  intro c
  rw [Matrix.det_fin_three]
  revert c
  decide

theorem det_x21M : ∀ c : F4, (x21M c).det = 1 := by
  intro c
  rw [Matrix.det_fin_three]
  revert c
  decide

theorem det_hM : hM.det = 1 := by
  rw [Matrix.det_fin_three]
  decide

theorem det_hiM : hiM.det = 1 := by
  rw [Matrix.det_fin_three]
  decide

theorem root_matrix_facts :
    (∀ c d : F4, x01M c * x01M d = x01M (c + d)) ∧
      (∀ c : F4, x02M 1 * x21M c * x02M 1 * x21M c = x01M c) ∧
      (∀ c : F4, x02M c * x02M c = 1) ∧ (∀ c : F4, x21M c * x21M c = 1) ∧
      (∀ d : F4, x02M 1 * x01M d = x01M d * x02M 1) ∧
      (∀ c d : F4, x21M c * x01M d = x01M d * x21M c) ∧
      (∀ c : F4, hM * x01M c * hiM = x01M (ω * ω * c)) ∧ hM * hiM = 1 ∧ hiM * hM = 1 ∧
      x01M 0 = 1 := by
  decide

theorem norm_F4 : ∀ c : F4, c + ω * ω * c + ω * ω * (ω * ω * c) = 0 := by decide

theorem x01M_ne_scalar : ∀ c : F4, c ≠ 0 → ∀ d : F4, x01M c ≠ Matrix.scalar (Fin 3) d := by
  intro c hc d h
  have h1 := congrFun (congrFun h 0) 1
  simp only [x01M, Matrix.add_apply, Matrix.one_apply_ne (show (0 : Fin 3) ≠ 1 by decide),
    Matrix.single_apply_same, zero_add, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ (show (0 : Fin 3) ≠ 1 by decide)] at h1
  exact hc h1

@[expose] def x01S (c : F4) : SpecialLinearGroup (Fin 3) F4 := ⟨x01M c, det_x01M c⟩

@[expose] def x02S (c : F4) : SpecialLinearGroup (Fin 3) F4 := ⟨x02M c, det_x02M c⟩

@[expose] def x21S (c : F4) : SpecialLinearGroup (Fin 3) F4 := ⟨x21M c, det_x21M c⟩

@[expose] def hS : SpecialLinearGroup (Fin 3) F4 := ⟨hM, det_hM⟩

@[expose] def hiS : SpecialLinearGroup (Fin 3) F4 := ⟨hiM, det_hiM⟩

theorem x01S_mul (c d : F4) : x01S c * x01S d = x01S (c + d) :=
  Subtype.ext (root_matrix_facts.1 c d)

theorem x01S_zero : x01S 0 = 1 := Subtype.ext root_matrix_facts.2.2.2.2.2.2.2.2.2

theorem x02S_inv (c : F4) : (x02S c)⁻¹ = x02S c :=
  inv_eq_of_mul_eq_one_right (Subtype.ext (root_matrix_facts.2.2.1 c))

theorem x21S_inv (c : F4) : (x21S c)⁻¹ = x21S c :=
  inv_eq_of_mul_eq_one_right (Subtype.ext (root_matrix_facts.2.2.2.1 c))

theorem hS_inv : hS⁻¹ = hiS :=
  inv_eq_of_mul_eq_one_right (Subtype.ext root_matrix_facts.2.2.2.2.2.2.2.1)

theorem x01S_eq_commutator (c : F4) :
    x01S c = x02S 1 * x21S c * (x02S 1)⁻¹ * (x21S c)⁻¹ := by
  rw [x02S_inv, x21S_inv]
  exact Subtype.ext (root_matrix_facts.2.1 c).symm

theorem x02S_comm (d : F4) : x02S 1 * x01S d = x01S d * x02S 1 :=
  Subtype.ext (root_matrix_facts.2.2.2.2.1 d)

theorem x21S_comm (c d : F4) : x21S c * x01S d = x01S d * x21S c :=
  Subtype.ext (root_matrix_facts.2.2.2.2.2.1 c d)

theorem hS_conj (c : F4) : hS * x01S c * hS⁻¹ = x01S (ω * ω * c) := by
  rw [hS_inv]
  exact Subtype.ext (root_matrix_facts.2.2.2.2.2.2.1 c)

@[expose] def rhoS : SpecialLinearGroup (Fin 3) F4 →* S :=
  rhoSL.codRestrict S fun A => by
    rw [← range_rhoSL.1]
    exact ⟨A, rfl⟩

theorem rhoS_x01_mul (c d : F4) : rhoS (x01S c) * rhoS (x01S d) = rhoS (x01S (c + d)) := by
  rw [← map_mul, x01S_mul]

theorem rhoS_x01_zero : rhoS (x01S 0) = 1 := by
  rw [x01S_zero, map_one]

theorem rhoS_x01_ne_one {c : F4} (hc : c ≠ 0) : rhoS (x01S c) ≠ 1 := by
  intro h
  have hker : x01S c ∈ rhoSL.ker := by
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val h
  rw [range_rhoSL.2, mem_scalars_iff] at hker
  obtain ⟨d, hd⟩ := hker
  exact x01M_ne_scalar c hc d hd

@[expose] def rootX01 : Subgroup S where
  carrier := Set.range fun c => rhoS (x01S c)
  one_mem' := ⟨0, rhoS_x01_zero⟩
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
    exact ⟨c + d, (rhoS_x01_mul c d).symm⟩
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    show rhoS (x01S c) = (rhoS (x01S c))⁻¹
    rw [← map_inv, inv_eq_of_mul_eq_one_right (a := x01S c) (b := x01S c)
      (by rw [x01S_mul, CharTwo.add_self_eq_zero c, x01S_zero])]

theorem mem_rootX01 {v : S} : v ∈ rootX01 ↔ ∃ c : F4, rhoS (x01S c) = v := Iff.rfl

theorem rootX01_commutators :
    ∀ v ∈ rootX01, ∃ p q : S, (∀ w ∈ rootX01, p * w = w * p) ∧
      (∀ w ∈ rootX01, q * w = w * q) ∧ v = p * q * p⁻¹ * q⁻¹ := by
  intro v hv
  obtain ⟨c, rfl⟩ := mem_rootX01.mp hv
  refine ⟨rhoS (x02S 1), rhoS (x21S c), fun w hw => ?_, fun w hw => ?_, ?_⟩
  · obtain ⟨d, rfl⟩ := mem_rootX01.mp hw
    rw [← map_mul, ← map_mul, x02S_comm]
  · obtain ⟨d, rfl⟩ := mem_rootX01.mp hw
    rw [← map_mul, ← map_mul, x21S_comm]
  · rw [x01S_eq_commutator, map_mul, map_mul, map_mul, map_inv, map_inv]

theorem rootX01_conj_h (c : F4) :
    rhoS hS * rhoS (x01S c) * (rhoS hS)⁻¹ = rhoS (x01S (ω * ω * c)) := by
  rw [← map_inv, ← map_mul, ← map_mul, hS_conj]

theorem rootX01_norm :
    ∀ v ∈ rootX01, v * (rhoS hS * v * (rhoS hS)⁻¹) *
      (rhoS hS * (rhoS hS * v * (rhoS hS)⁻¹) * (rhoS hS)⁻¹) = 1 := by
  intro v hv
  obtain ⟨c, rfl⟩ := mem_rootX01.mp hv
  rw [rootX01_conj_h, rootX01_conj_h, rhoS_x01_mul, rhoS_x01_mul, norm_F4, rhoS_x01_zero]

theorem exists_four_of_central {E : Type*} [Group E] [Finite E] {π : E →* S}
    (hπ : Function.Surjective π) (hK : π.ker ≤ center E) (h3 : ∀ z ∈ π.ker, z ^ 3 = 1 → z = 1) :
    ∃ Y : Subgroup E, Y ⊓ π.ker = ⊥ ∧ (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) ∧
      ∃ y₁ ∈ Y, ∃ y₂ ∈ Y, y₁ * y₁ = 1 ∧ y₂ * y₂ = 1 ∧ y₁ ≠ 1 ∧ y₂ ≠ 1 ∧ y₁ ≠ y₂ := by
  obtain ⟨Y, hYK, hYV, hYab⟩ := exists_split hπ hK h3 rootX01_commutators
    (h := rhoS hS) (fun v hv => by
      obtain ⟨c, rfl⟩ := mem_rootX01.mp hv
      rw [rootX01_conj_h]
      exact ⟨_, rfl⟩) rootX01_norm
  have hinvY : ∀ y ∈ Y, π y * π y = 1 → y * y = 1 := by
    intro y hy h
    have hm : y * y ∈ Y ⊓ π.ker :=
      Subgroup.mem_inf.mpr ⟨mul_mem hy hy, by rw [MonoidHom.mem_ker, map_mul, h]⟩
    rw [hYK] at hm
    exact (mem_bot.mp hm)
  have hmem : ∀ c : F4, ∃ y ∈ Y, π y = rhoS (x01S c) := by
    intro c
    have : rhoS (x01S c) ∈ Y.map π := hYV ▸ mem_rootX01.mpr ⟨c, rfl⟩
    obtain ⟨y, hy, hyc⟩ := this
    exact ⟨y, hy, hyc⟩
  have hsq : ∀ c : F4, rhoS (x01S c) * rhoS (x01S c) = 1 := fun c => by
    rw [rhoS_x01_mul, CharTwo.add_self_eq_zero c, rhoS_x01_zero]
  obtain ⟨y₁, hy₁, h₁⟩ := hmem 1
  obtain ⟨y₂, hy₂, h₂⟩ := hmem ω
  refine ⟨Y, hYK, hYab, y₁, hy₁, y₂, hy₂, hinvY _ hy₁ (by rw [h₁]; exact hsq 1),
    hinvY _ hy₂ (by rw [h₂]; exact hsq ω), ?_, ?_, ?_⟩
  · rintro rfl
    exact rhoS_x01_ne_one (show (1 : F4) ≠ 0 by decide) (by rw [← h₁, map_one])
  · rintro rfl
    exact rhoS_x01_ne_one (show ω ≠ 0 by decide) (by rw [← h₂, map_one])
  · rintro rfl
    have h12 : rhoS (x01S 1) = rhoS (x01S ω) := h₁.symm.trans h₂
    have h0 : rhoS (x01S (1 + ω)) = 1 := by
      rw [← rhoS_x01_mul, h12, hsq]
    exact rhoS_x01_ne_one (show (1 + ω : F4) ≠ 0 by decide) h0

end CFSG.ComponentClassification.GrSLit.GrS5
