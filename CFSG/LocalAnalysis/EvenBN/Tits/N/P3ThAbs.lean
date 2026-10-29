module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Frob
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3ThCount
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Gen

public section

set_option linter.unusedSectionVars false

universe u

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup

structure ThData (V : Type*) [CommGroup V] [Finite V] where
  hsq : ∀ a : V, a * a = 1
  hV : Nat.card V = 2 ^ 10
  E : Subgroup V
  hE : Nat.card E = 2 ^ 5
  z : V
  z₀ : V
  hzE : z ∈ E
  hz1 : z ≠ 1
  hz₀E : z₀ ∉ E
  τ : MulAut V
  x : MulAut V
  y : MulAut V
  hτ2 : τ * τ = 1
  hτE : ∀ v, τ v = v ↔ v ∈ E
  hτc : ∀ v, τ v * v⁻¹ ∈ E
  hτz₀ : τ z₀ = z₀ * z
  hx5 : x ^ 5 = 1
  hxfix : ∀ v, x v = v ↔ (v = 1 ∨ v = z ∨ v = z₀ ∨ v = z * z₀)
  hxE : ∀ e ∈ E, x e ∈ E
  hxτ : x * τ = τ * x
  hyx : y * x * y⁻¹ = x ^ 3
  hy4 : y ^ 4 = 1
  hyτ : y * τ = τ * y
  hyz : y z = z
  hyz₀ : y z₀ = z₀
  hyE : ∀ e ∈ E, y e ∈ E

namespace ThData

variable {V : Type*} [CommGroup V] [Finite V]

theorem inv_eq (D : ThData V) (a : V) : a⁻¹ = a := inv_eq_of_mul_eq_one_right (D.hsq a)

theorem z_sq (D : ThData V) : D.z * D.z = 1 := D.hsq D.z

theorem z₀_ne_one (D : ThData V) : D.z₀ ≠ 1 := fun h => D.hz₀E (h ▸ one_mem _)

theorem z₀_ne_z (D : ThData V) : D.z₀ ≠ D.z := fun h => D.hz₀E (h ▸ D.hzE)

theorem zz₀_not_mem (D : ThData V) : D.z * D.z₀ ∉ D.E := fun h =>
  D.hz₀E (by
    have := mul_mem (inv_mem D.hzE) h
    simpa using this)

theorem y_x_comm_pow (D : ThData V) : D.y * D.x = D.x ^ 3 * D.y := by
  have := D.hyx
  calc D.y * D.x = (D.y * D.x * D.y⁻¹) * D.y := by group
    _ = D.x ^ 3 * D.y := by rw [this]

theorem x_pow_apply_succ (D : ThData V) (n : ℕ) (v : V) : (D.x ^ (n + 1)) v = D.x ((D.x ^ n) v) := by
  rw [pow_succ', MulAut.mul_apply]

@[expose] def xm1 (D : ThData V) : V →* V :=
  MonoidHom.mk' (fun a => D.x a * a⁻¹) (fun a b => by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _)

theorem xm1_apply (D : ThData V) (a : V) : D.xm1 a = D.x a * a⁻¹ := rfl

theorem xm1_eq_one_iff (D : ThData V) (a : V) : D.xm1 a = 1 ↔ D.x a = a := by
  rw [xm1_apply, mul_inv_eq_one]

@[expose] def Fx (D : ThData V) : Subgroup V := fixSub D.x

theorem mem_Fx_iff (D : ThData V) (v : V) : v ∈ D.Fx ↔ v = 1 ∨ v = D.z ∨ v = D.z₀ ∨ v = D.z * D.z₀ :=
  (D.hxfix v)

theorem ker_xm1 (D : ThData V) : D.xm1.ker = D.Fx := by
  ext v
  rw [MonoidHom.mem_ker, xm1_eq_one_iff]
  rfl

theorem zz₀_ne_one (D : ThData V) : D.z * D.z₀ ≠ 1 := fun h => D.zz₀_not_mem (h ▸ one_mem _)

theorem card_Fx (D : ThData V) : Nat.card D.Fx = 4 := by
  classical
  have h : (D.Fx : Set V) = ↑({1, D.z, D.z₀, D.z * D.z₀} : Finset V) := by
    ext v
    simp only [SetLike.mem_coe, mem_Fx_iff, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
  have h1 : (1 : V) ∉ ({D.z, D.z₀, D.z * D.z₀} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨D.hz1.symm, D.z₀_ne_one.symm, D.zz₀_ne_one.symm⟩
  have h2 : D.z ∉ ({D.z₀, D.z * D.z₀} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨D.z₀_ne_z.symm, fun hh => D.z₀_ne_one ?_⟩
    have := congrArg (fun w => D.z⁻¹ * w) hh
    simpa using this.symm
  have h3 : D.z₀ ∉ ({D.z * D.z₀} : Finset V) := by
    simp only [Finset.mem_singleton]
    intro hh
    apply D.hz1
    have := congrArg (fun w => w * D.z₀⁻¹) hh
    simpa using this.symm
  have hc : Nat.card D.Fx = Nat.card (D.Fx : Set V) := rfl
  rw [hc, Nat.card_coe_set_eq, h, Set.ncard_coe_finset, Finset.card_insert_of_notMem h1,
    Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h3, Finset.card_singleton]

@[expose] def V₁ (D : ThData V) : Subgroup V := D.xm1.range

theorem card_V₁ (D : ThData V) : Nat.card D.V₁ = 256 := by
  have h := Subgroup.card_ker_mul_card_range D.xm1
  rw [ker_xm1, card_Fx, D.hV] at h
  have : 4 * Nat.card D.xm1.range = 4 * 256 := by
    rw [h]
    norm_num
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) this

theorem xm1_mem_V₁ (D : ThData V) (a : V) : D.x a * a⁻¹ ∈ D.V₁ := ⟨a, rfl⟩

theorem xpow_mul_inv_mem_V₁ (D : ThData V) (n : ℕ) (v : V) : (D.x ^ n) v * v⁻¹ ∈ D.V₁ := by
  induction n with
  | zero => simpa using one_mem D.V₁
  | succ n ih =>
    have e : (D.x ^ (n + 1)) v * v⁻¹ =
        (D.x ((D.x ^ n) v) * ((D.x ^ n) v)⁻¹) * ((D.x ^ n) v * v⁻¹) := by
      rw [D.x_pow_apply_succ]
      group
    rw [e]
    exact mul_mem (D.xm1_mem_V₁ _) ih

theorem x_mem_V₁ (D : ThData V) {v : V} (hv : v ∈ D.V₁) : D.x v ∈ D.V₁ := by
  obtain ⟨a, rfl⟩ := hv
  refine ⟨D.x a, ?_⟩
  rw [xm1_apply, xm1_apply, map_mul, map_inv]

theorem y_mem_V₁ (D : ThData V) {v : V} (hv : v ∈ D.V₁) : D.y v ∈ D.V₁ := by
  obtain ⟨a, rfl⟩ := hv
  have h1 : D.y (D.xm1 a) = (D.x ^ 3) (D.y a) * (D.y a)⁻¹ := by
    have : D.y (D.x a) = (D.x ^ 3) (D.y a) := by
      have := congrArg (fun φ : MulAut V => φ a) D.y_x_comm_pow
      simpa [MulAut.mul_apply] using this
    rw [xm1_apply, map_mul, map_inv, this]
  rw [h1]
  exact D.xpow_mul_inv_mem_V₁ 3 _

theorem V₁_inf_Fx (D : ThData V) : D.V₁ ⊓ D.Fx = ⊥ := by
  have h : Nat.card D.V₁ ≡ Nat.card ↥(D.V₁ ⊓ D.Fx) [MOD 5] :=
    card_modEq_x D.x D.hx5 D.V₁ (fun u hu => D.x_mem_V₁ hu)
  have hdvd : Nat.card ↥(D.V₁ ⊓ D.Fx) ∣ 4 := by
    rw [← D.card_Fx]
    exact Subgroup.card_dvd_of_le inf_le_right
  rw [D.card_V₁] at h
  have hpos : 0 < Nat.card ↥(D.V₁ ⊓ D.Fx) := Nat.card_pos
  have h1 : Nat.card ↥(D.V₁ ⊓ D.Fx) = 1 := by
    have hle : Nat.card ↥(D.V₁ ⊓ D.Fx) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    unfold Nat.ModEq at h
    interval_cases hc : Nat.card ↥(D.V₁ ⊓ D.Fx) <;> first | rfl | omega | (exfalso; omega)
  exact Subgroup.eq_bot_of_card_eq _ h1

theorem fpf_V₁ (D : ThData V) {v : V} (hv : v ∈ D.V₁) (hx : D.x v = v) : v = 1 := by
  have : v ∈ D.V₁ ⊓ D.Fx := ⟨hv, hx⟩
  rw [D.V₁_inf_Fx] at this
  exact this

theorem Fx_sup_V₁ (D : ThData V) : D.Fx ⊔ D.V₁ = ⊤ := by
  have hnorm : D.Fx ≤ normalizer (D.V₁ : Set V) := fun g _ => by
    rw [mem_normalizer_iff]
    intro h
    simp [mul_comm]
  have h := card_sup_mul_card_inf' hnorm
  rw [inf_comm, D.V₁_inf_Fx, Subgroup.card_bot, D.card_Fx, D.card_V₁] at h
  apply Subgroup.eq_top_of_card_eq
  rw [D.hV]
  omega

@[expose] def eps (D : ThData V) : V →* V :=
  MonoidHom.mk' (fun v => D.τ v * v⁻¹) (fun a b => by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _)

theorem eps_apply (D : ThData V) (v : V) : D.eps v = D.τ v * v⁻¹ := rfl

theorem eps_mem_E (D : ThData V) (v : V) : D.eps v ∈ D.E := D.hτc v

theorem eps_eq_one_iff (D : ThData V) (v : V) : D.eps v = 1 ↔ v ∈ D.E := by
  rw [eps_apply, mul_inv_eq_one]
  exact D.hτE v

theorem ker_eps (D : ThData V) : D.eps.ker = D.E := by
  ext v
  rw [MonoidHom.mem_ker, eps_eq_one_iff]

theorem τ_x_apply (D : ThData V) (v : V) : D.τ (D.x v) = D.x (D.τ v) := by
  have := congrArg (fun φ : MulAut V => φ v) D.hxτ
  simpa [MulAut.mul_apply] using this.symm

theorem τ_y_apply (D : ThData V) (v : V) : D.τ (D.y v) = D.y (D.τ v) := by
  have := congrArg (fun φ : MulAut V => φ v) D.hyτ
  simpa [MulAut.mul_apply] using this.symm

theorem eps_x (D : ThData V) (v : V) : D.eps (D.x v) = D.x (D.eps v) := by
  rw [eps_apply, eps_apply, D.τ_x_apply, map_mul, map_inv]

theorem eps_y (D : ThData V) (v : V) : D.eps (D.y v) = D.y (D.eps v) := by
  rw [eps_apply, eps_apply, D.τ_y_apply, map_mul, map_inv]

@[expose] def C (D : ThData V) : Subgroup V := D.E ⊓ D.V₁

theorem x_mem_C (D : ThData V) {v : V} (hv : v ∈ D.C) : D.x v ∈ D.C :=
  ⟨D.hxE v hv.1, D.x_mem_V₁ hv.2⟩

theorem y_mem_C (D : ThData V) {v : V} (hv : v ∈ D.C) : D.y v ∈ D.C :=
  ⟨D.hyE v hv.1, D.y_mem_V₁ hv.2⟩

theorem E_inf_Fx (D : ThData V) : D.E ⊓ D.Fx = zpowers D.z := by
  have hzfix : D.x D.z = D.z := (D.hxfix D.z).2 (Or.inr (Or.inl rfl))
  refine le_antisymm (fun v hv => ?_) (fun v hv => ?_)
  · obtain ⟨hvE, hvF⟩ := hv
    rcases (D.mem_Fx_iff v).1 hvF with h | h | h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact mem_zpowers _
    · exact absurd (h ▸ hvE) D.hz₀E
    · exact absurd (h ▸ hvE) D.zz₀_not_mem
  · obtain ⟨n, rfl⟩ := hv
    refine ⟨zpow_mem D.hzE n, ?_⟩
    show D.x (D.z ^ n) = D.z ^ n
    rw [map_zpow, hzfix]

theorem card_zpowers_z (D : ThData V) : Nat.card (zpowers D.z) = 2 := by
  rw [Nat.card_zpowers]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact D.z_sq) D.hz1

theorem card_E_inf_Fx (D : ThData V) : Nat.card ↥(D.E ⊓ D.Fx) = 2 := by
  rw [D.E_inf_Fx, D.card_zpowers_z]

theorem card_C (D : ThData V) : Nat.card D.C = 16 := by
  have h := card_inf_ker_mul_card_map D.xm1 D.E
  rw [ker_xm1, inf_comm, D.card_E_inf_Fx, D.hE] at h
  have hmap : Nat.card ↥(D.E.map D.xm1) = 16 := by
    have : 2 * Nat.card ↥(D.E.map D.xm1) = 2 * 16 := by
      rw [h]
      norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have hle : D.E.map D.xm1 ≤ D.C := by
    rintro _ ⟨e, he, rfl⟩
    refine ⟨?_, D.xm1_mem_V₁ e⟩
    rw [xm1_apply]
    exact D.E.mul_mem (D.hxE e he) (D.E.inv_mem he)
  have h1 : 16 ≤ Nat.card D.C := hmap ▸ Subgroup.card_le_of_le hle
  have hmod : Nat.card D.C % 5 = 1 :=
    card_mod_five_of_fpf D.x D.hx5 D.C (fun u hu => D.x_mem_C hu)
      (fun u hu hx => D.fpf_V₁ hu.2 hx)
  have hdvd : Nat.card D.C ∣ 2 ^ 5 := by
    rw [← D.hE]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hle2 : Nat.card D.C ≤ 32 := Nat.le_of_dvd (by norm_num) hdvd
  obtain ⟨k, hk, hkC⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  interval_cases k <;> simp_all

theorem E_eq_sup (D : ThData V) : D.E = zpowers D.z ⊔ D.C := by
  have hnorm : zpowers D.z ≤ normalizer (D.C : Set V) := fun g _ => by
    rw [mem_normalizer_iff]
    intro h
    simp [mul_comm]
  have hbot : zpowers D.z ⊓ D.C = ⊥ := by
    refine eq_bot_iff.2 fun v hv => ?_
    obtain ⟨hvz, hvC⟩ := hv
    rcases eq_one_or_of_mem_zpowers D.z_sq hvz with h | h
    · rw [h]; exact one_mem _
    · exfalso
      have hz1 : D.z ∈ D.V₁ ⊓ D.Fx := ⟨h ▸ hvC.2, (D.mem_Fx_iff D.z).2 (Or.inr (Or.inl rfl))⟩
      rw [D.V₁_inf_Fx] at hz1
      exact D.hz1 hz1
  have hcard := card_sup_mul_card_inf' hnorm
  rw [hbot, Subgroup.card_bot, D.card_zpowers_z, D.card_C] at hcard
  have hle : zpowers D.z ⊔ D.C ≤ D.E :=
    sup_le (zpowers_le.2 D.hzE) inf_le_left
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [D.hE]
  omega

theorem map_eps_V₁ (D : ThData V) : D.V₁.map D.eps = D.C := by
  have h := card_inf_ker_mul_card_map D.eps D.V₁
  have h' : Nat.card D.C * Nat.card ↥(D.V₁.map D.eps) = Nat.card D.V₁ := by
    rw [ker_eps] at h
    exact h
  rw [D.card_C, D.card_V₁] at h'
  have hmap : Nat.card ↥(D.V₁.map D.eps) = 16 := by
    have : 16 * Nat.card ↥(D.V₁.map D.eps) = 16 * 16 := by
      rw [h']
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have hle : D.V₁.map D.eps ≤ D.C := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨a, rfl⟩ := hv
    have e : D.eps (D.xm1 a) = D.x (D.eps a) * (D.eps a)⁻¹ := by
      rw [xm1_apply, map_mul, map_inv, D.eps_x]
    rw [e]
    exact ⟨D.E.mul_mem (D.hxE _ (D.eps_mem_E a)) (D.E.inv_mem (D.eps_mem_E a)), D.xm1_mem_V₁ _⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hmap, D.card_C])

theorem exists_eps_eq (D : ThData V) {c : V} (hc : c ∈ D.C) : ∃ v ∈ D.V₁, D.eps v = c := by
  have : c ∈ D.V₁.map D.eps := by rw [D.map_eps_V₁]; exact hc
  obtain ⟨v, hv, rfl⟩ := this
  exact ⟨v, hv, rfl⟩

theorem exists_w₀ (D : ThData V) : ∃ w₀ ∈ D.C, w₀ ≠ 1 ∧ D.y w₀ = w₀ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG : IsPGroup 2 (zpowers D.y) := by
    intro g
    refine ⟨2, ?_⟩
    apply Subtype.ext
    obtain ⟨g, n, rfl⟩ := g
    show (D.y ^ n) ^ (2 ^ 2) = 1
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, D.hy4, one_zpow]
  have hys : D.y ∈ stabSubgroup D.C := fun u => mem_iff_of_forall_mem D.y D.C
    (fun u hu => D.y_mem_C hu) u
  have hinv : ∀ g ∈ zpowers D.y, ∀ u ∈ D.C, g u ∈ D.C := fun g hg u hu =>
    ((zpowers_le.2 hys hg) u).1 hu
  have h2 : 2 ∣ Nat.card D.C := by rw [D.card_C]; norm_num
  obtain ⟨u, hu, hu1, hfix⟩ := exists_ne_one_fixed (p := 2) (zpowers D.y) hG D.C hinv h2
  exact ⟨u, hu, hu1, hfix D.y (mem_zpowers D.y)⟩

structure IsHK (D : ThData V) (δ : V →* V) : Prop where
  mem : ∀ v, δ v ∈ D.E
  triv : ∀ e ∈ D.E, δ e = 1
  x_eq : ∀ v, δ (D.x v) = D.x (δ v)
  y_eq : ∀ v, δ (D.y v) = D.y (δ v)

theorem IsHK.apply_z₀ {D : ThData V} {δ : V →* V} (h : IsHK D δ) :
    δ D.z₀ = 1 ∨ δ D.z₀ = D.z := by
  have hz₀ : D.x D.z₀ = D.z₀ := (D.hxfix D.z₀).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hx : D.x (δ D.z₀) = δ D.z₀ := by rw [← h.x_eq, hz₀]
  have hmem : δ D.z₀ ∈ D.E ⊓ D.Fx := ⟨h.mem _, hx⟩
  rw [D.E_inf_Fx] at hmem
  exact eq_one_or_of_mem_zpowers D.z_sq hmem

theorem IsHK.apply_V₁ {D : ThData V} {δ : V →* V} (h : IsHK D δ) {v : V} (hv : v ∈ D.V₁) :
    δ v ∈ D.C := by
  obtain ⟨a, rfl⟩ := hv
  have e : δ (D.xm1 a) = D.x (δ a) * (δ a)⁻¹ := by
    rw [xm1_apply, map_mul, map_inv, h.x_eq]
  rw [e]
  exact ⟨D.E.mul_mem (D.hxE _ (h.mem a)) (D.E.inv_mem (h.mem a)), D.xm1_mem_V₁ _⟩

theorem IsHK.y_apply_w₁ {D : ThData V} {δ : V →* V} (h : IsHK D δ) {w₀ w₁ : V}
    (hw₁ : w₁ ∈ D.V₁) (hε : D.eps w₁ = w₀) (hy : D.y w₀ = w₀) : D.y (δ w₁) = δ w₁ := by
  have hc : D.y w₁ * w₁⁻¹ ∈ D.E := by
    rw [← D.eps_eq_one_iff, map_mul, map_inv, D.eps_y, hε, hy, mul_inv_cancel]
  have hc1 : δ (D.y w₁ * w₁⁻¹) = 1 := h.triv _ hc
  rw [map_mul, map_inv, mul_inv_eq_one] at hc1
  rw [← h.y_eq, hc1]

theorem IsHK.eq_on_V₁ {D : ThData V} {δ δ' : V →* V} (h : IsHK D δ) (h' : IsHK D δ') {w₀ w₁ : V}
    (hw₀ : w₀ ≠ 1) (hw₁ : w₁ ∈ D.V₁) (hε : D.eps w₁ = w₀) (h₁ : δ w₁ = δ' w₁) :
    ∀ v ∈ D.V₁, δ v = δ' v := by
  set Q : Subgroup V := MonoidHom.eqLocus δ δ' with hQ
  have hmemQ : ∀ v, v ∈ Q ↔ δ v = δ' v := fun v => Iff.rfl
  set Q₁ : Subgroup V := Q ⊓ D.V₁ with hQ₁
  have hxQ : ∀ u ∈ Q₁, D.x u ∈ Q₁ := by
    rintro u ⟨hu, hu1⟩
    refine ⟨(hmemQ _).2 ?_, D.x_mem_V₁ hu1⟩
    rw [h.x_eq, h'.x_eq, (hmemQ u).1 hu]
  have hmod : Nat.card Q₁ % 5 = 1 :=
    card_mod_five_of_fpf D.x D.hx5 Q₁ hxQ (fun u hu hx => D.fpf_V₁ hu.2 hx)
  have hCQ : D.C ≤ Q₁ := fun c hc => ⟨(hmemQ c).2 (by rw [h.triv c hc.1, h'.triv c hc.1]), hc.2⟩
  have hw₁Q : w₁ ∈ Q₁ := ⟨(hmemQ w₁).2 h₁, hw₁⟩
  have hw₁C : w₁ ∉ D.C := by
    intro hc
    apply hw₀
    rw [← hε, D.eps_eq_one_iff]
    exact hc.1
  have hne : Q₁ ≠ D.C := fun heq => hw₁C (heq ▸ hw₁Q)
  have hcdvd : Nat.card D.C ∣ Nat.card Q₁ := Subgroup.card_dvd_of_le hCQ
  have hcne : Nat.card Q₁ ≠ Nat.card D.C := fun heq =>
    hne (Subgroup.eq_of_le_of_card_ge hCQ heq.le).symm
  have hdvd256 : Nat.card Q₁ ∣ 256 := by
    rw [← D.card_V₁]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hQ₁card : Nat.card Q₁ = 256 := by
    rw [D.card_C] at hcdvd hcne
    obtain ⟨k, hk, hkQ⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.card Q₁ ∣ 2 ^ 8 by
      simpa using hdvd256)
    interval_cases k <;> simp_all <;> omega
  have hQ₁V : Q₁ = D.V₁ :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hQ₁card, D.card_V₁])
  intro v hv
  have : v ∈ Q₁ := by rw [hQ₁V]; exact hv
  exact (hmemQ v).1 this.1

theorem IsHK.ext_of {D : ThData V} {δ δ' : V →* V} (h : IsHK D δ) (h' : IsHK D δ') {w₀ w₁ : V}
    (hw₀ : w₀ ≠ 1) (hw₁ : w₁ ∈ D.V₁) (hε : D.eps w₁ = w₀) (h₀ : δ D.z₀ = δ' D.z₀)
    (h₁ : δ w₁ = δ' w₁) : δ = δ' := by
  have hV₁ := h.eq_on_V₁ h' hw₀ hw₁ hε h₁
  have hEz : ∀ e ∈ D.E, δ e = δ' e := fun e he => by rw [h.triv e he, h'.triv e he]
  have hFx : ∀ f ∈ D.Fx, δ f = δ' f := by
    intro f hf
    rcases (D.mem_Fx_iff f).1 hf with rfl | rfl | rfl | rfl
    · simp
    · exact hEz _ D.hzE
    · exact h₀
    · rw [map_mul, map_mul, hEz _ D.hzE, h₀]
  ext v
  have hv : v ∈ D.Fx ⊔ D.V₁ := by rw [D.Fx_sup_V₁]; exact mem_top v
  obtain ⟨f, hf, v₁, hv₁, rfl⟩ := Subgroup.mem_sup.1 hv
  rw [map_mul, map_mul, hFx f hf, hV₁ v₁ hv₁]

@[expose] def dm (s : MulAut V) : V →* V :=
  MonoidHom.mk' (fun v => s v * v⁻¹) (fun a b => by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _)

theorem dm_apply (s : MulAut V) (v : V) : dm s v = s v * v⁻¹ := rfl

theorem dm_eq_one_iff (s : MulAut V) (v : V) : dm s v = 1 ↔ s v = v := by
  rw [dm_apply, mul_inv_eq_one]

structure SOK (D : ThData V) (S : Subgroup (MulAut V)) : Prop where
  pgroup : IsPGroup 2 S
  hx : ∀ s ∈ S, s * D.x = D.x * s
  hy : ∀ s ∈ S, s * D.y = D.y * s
  tau : D.τ ∈ S

namespace SOK

variable {D : ThData V} {S : Subgroup (MulAut V)}

theorem apply_x (h : SOK D S) {s : MulAut V} (hs : s ∈ S) (v : V) : s (D.x v) = D.x (s v) := by
  have := congrArg (fun φ : MulAut V => φ v) (h.hx s hs)
  simpa [MulAut.mul_apply] using this

theorem apply_y (h : SOK D S) {s : MulAut V} (hs : s ∈ S) (v : V) : s (D.y v) = D.y (s v) := by
  have := congrArg (fun φ : MulAut V => φ v) (h.hy s hs)
  simpa [MulAut.mul_apply] using this

theorem mem_Fx (h : SOK D S) {s : MulAut V} (hs : s ∈ S) {v : V} (hv : v ∈ D.Fx) : s v ∈ D.Fx := by
  show D.x (s v) = s v
  rw [← h.apply_x hs, (show D.x v = v from hv)]

theorem mem_V₁ (h : SOK D S) {s : MulAut V} (hs : s ∈ S) {v : V} (hv : v ∈ D.V₁) : s v ∈ D.V₁ := by
  obtain ⟨a, rfl⟩ := hv
  refine ⟨s a, ?_⟩
  rw [xm1_apply, xm1_apply, map_mul, map_inv, h.apply_x hs]

theorem fix_z (h : SOK D S) {s : MulAut V} (hs : s ∈ S) : s D.z = D.z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinv : ∀ g ∈ S, ∀ u ∈ D.Fx, g u ∈ D.Fx := fun g hg u hu => h.mem_Fx hg hu
  have h2 : 2 ∣ Nat.card D.Fx := by rw [D.card_Fx]; norm_num
  obtain ⟨u, hu, hu1, hfix⟩ := exists_ne_one_fixed (p := 2) S h.pgroup D.Fx hinv h2
  have hτu : D.τ u = u := hfix D.τ h.tau
  have huz : u = D.z := by
    rcases (D.mem_Fx_iff u).1 hu with h1 | h1 | h1 | h1
    · exact absurd h1 hu1
    · exact h1
    · exfalso
      rw [h1, D.hτz₀] at hτu
      apply D.hz1
      have := congrArg (fun w => w * D.z₀⁻¹) hτu
      simpa using this
    · exfalso
      rw [h1, map_mul, D.hτz₀, (D.hτE D.z).2 D.hzE] at hτu
      apply D.hz1
      have e : D.z * (D.z₀ * D.z) = D.z₀ := by
        calc D.z * (D.z₀ * D.z) = (D.z * D.z) * D.z₀ := by ac_rfl
          _ = D.z₀ := by rw [D.z_sq, one_mul]
      rw [e] at hτu
      have := congrArg (fun w => D.z⁻¹ * w) hτu
      simpa using this.symm
  rw [← huz]
  exact hfix s hs

theorem fix_C (h : SOK D S) {s : MulAut V} (hs : s ∈ S) {c : V} (hc : c ∈ D.C) : s c = c := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let CS : Subgroup V :=
    { carrier := {v | v ∈ D.V₁ ∧ ∀ g ∈ S, g v = v}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun g hg => by
        rw [map_mul, ha.2 g hg, hb.2 g hg]⟩
      one_mem' := ⟨one_mem _, fun g hg => map_one g⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun g hg => by rw [map_inv, ha.2 g hg]⟩ }
  have hCSle : CS ≤ D.C := fun v hv =>
    ⟨(D.hτE v).1 (hv.2 D.τ h.tau), hv.1⟩
  have hx : ∀ u ∈ CS, D.x u ∈ CS := fun u hu =>
    ⟨D.x_mem_V₁ hu.1, fun g hg => by rw [h.apply_x hg, hu.2 g hg]⟩
  have hmod : Nat.card CS % 5 = 1 :=
    card_mod_five_of_fpf D.x D.hx5 CS hx (fun u hu hx => D.fpf_V₁ hu.1 hx)
  have hdvd : Nat.card CS ∣ 16 := by
    rw [← D.card_C]
    exact Subgroup.card_dvd_of_le hCSle
  have hinvV₁ : ∀ g ∈ S, ∀ u ∈ D.V₁, g u ∈ D.V₁ := fun g hg u hu => h.mem_V₁ hg hu
  have h2 : 2 ∣ Nat.card D.V₁ := by rw [D.card_V₁]; norm_num
  obtain ⟨u, hu, hu1, hfix⟩ := exists_ne_one_fixed (p := 2) S h.pgroup D.V₁ hinvV₁ h2
  have hnt : 1 < Nat.card CS := by
    have hmem : u ∈ CS := ⟨hu, hfix⟩
    have hpos : 0 < Nat.card CS := Nat.card_pos
    by_contra hle
    have hcs : Nat.card CS = 1 := by omega
    have := Subgroup.eq_bot_of_card_eq CS hcs
    rw [this] at hmem
    exact hu1 (mem_bot.1 hmem)
  have hCS16 : Nat.card CS = 16 := by
    obtain ⟨k, hk, hkQ⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.card CS ∣ 2 ^ 4 by
      simpa using hdvd)
    interval_cases k <;> simp_all <;> omega
  have hCSC : CS = D.C := Subgroup.eq_of_le_of_card_ge hCSle (by rw [hCS16, D.card_C])
  have : c ∈ CS := by rw [hCSC]; exact hc
  exact this.2 s hs

theorem fix_E (h : SOK D S) {s : MulAut V} (hs : s ∈ S) {e : V} (he : e ∈ D.E) : s e = e := by
  rw [D.E_eq_sup] at he
  obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.1 he
  obtain ⟨n, rfl⟩ := ha
  rw [map_mul, h.fix_C hs hc]
  show s (D.z ^ n) * c = D.z ^ n * c
  rw [map_zpow, h.fix_z hs]

theorem delta_V₁ (h : SOK D S) {s : MulAut V} (hs : s ∈ S) {v : V} (hv : v ∈ D.V₁) :
    s v * v⁻¹ ∈ D.C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup V := D.V₁ ⊓ fixSub s with hK
  set I : Subgroup V := D.V₁.map (dm s) with hI
  have hCK : D.C ≤ K := fun c hc => ⟨hc.2, h.fix_C hs hc⟩
  have hcard := card_inf_ker_mul_card_map (dm s) D.V₁
  have hker : (dm s).ker = fixSub s := by
    ext w
    rw [MonoidHom.mem_ker, dm_eq_one_iff]
    rfl
  rw [hker, inf_comm] at hcard
  have hKI : Nat.card K * Nat.card I = 256 := by
    rw [← D.card_V₁]; exact hcard
  have hK16 : 16 ≤ Nat.card K := by
    have := Subgroup.card_le_of_le hCK
    rwa [D.card_C] at this
  have hIle : Nat.card I ≤ 16 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hIV : I ≤ D.V₁ := by
    rintro _ ⟨w, hw, rfl⟩
    rw [dm_apply]
    exact mul_mem (h.mem_V₁ hs hw) (inv_mem hw)
  have hIx : ∀ u ∈ I, D.x u ∈ I := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨D.x w, D.x_mem_V₁ hw, ?_⟩
    rw [dm_apply, dm_apply, map_mul, map_inv, h.apply_x hs]
  have hImod : Nat.card I % 5 = 1 :=
    card_mod_five_of_fpf D.x D.hx5 I hIx (fun u hu hx => D.fpf_V₁ (hIV hu) hx)
  have hIdvd : Nat.card I ∣ 2 ^ 8 := by
    have : Nat.card I ∣ 256 := Dvd.intro_left _ hKI
    simpa using this
  have hI116 : Nat.card I = 1 ∨ Nat.card I = 16 := by
    obtain ⟨k, hk, hkI⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hIdvd
    have hk' : 2 ^ k % 5 = 1 := by rw [← hkI]; exact hImod
    rcases two_pow_mod_five_one (by omega) hk' with rfl | rfl | rfl
    · left; simpa using hkI
    · right; simpa using hkI
    · exfalso
      have : Nat.card I = 256 := by simpa using hkI
      omega
  have hmem : s v * v⁻¹ ∈ I := ⟨v, hv, rfl⟩
  rcases hI116 with h1 | h16
  · have hbot := Subgroup.eq_bot_of_card_eq I h1
    rw [hbot, mem_bot] at hmem
    rw [hmem]
    exact one_mem _
  ·
    have hK16' : Nat.card K = 16 := by
      rw [h16] at hKI
      omega
    have hKC : D.C = K :=
      Subgroup.eq_of_le_of_card_ge hCK (by rw [hK16', D.card_C])
    have hsS : IsPGroup 2 (zpowers s) := h.pgroup.to_le (zpowers_le.2 hs)
    have hIinv : ∀ g ∈ zpowers s, ∀ u ∈ I, g u ∈ I := by
      have hsI : s ∈ stabSubgroup I := by
        refine fun u => mem_iff_of_forall_mem s I (fun u hu => ?_) u
        obtain ⟨w, hw, rfl⟩ := hu
        refine ⟨s w, h.mem_V₁ hs hw, ?_⟩
        rw [dm_apply, dm_apply, map_mul, map_inv]
      exact fun g hg u hu => ((zpowers_le.2 hsI hg) u).1 hu
    have h2I : 2 ∣ Nat.card I := by rw [h16]; norm_num
    obtain ⟨i, hi, hi1, hfix⟩ := exists_ne_one_fixed (p := 2) (zpowers s) hsS I hIinv h2I
    have hsi : s i = i := hfix s (mem_zpowers s)
    have hKIx : ∀ u ∈ K ⊓ I, D.x u ∈ K ⊓ I := by
      rintro u ⟨huK, huI⟩
      have huC : u ∈ D.C := by rw [hKC]; exact huK
      have hxC : D.x u ∈ D.C := D.x_mem_C huC
      rw [hKC] at hxC
      exact ⟨hxC, hIx u huI⟩
    have hmod2 : Nat.card ↥(K ⊓ I) % 5 = 1 :=
      card_mod_five_of_fpf D.x D.hx5 (K ⊓ I) hKIx (fun u hu hx => D.fpf_V₁ (hIV hu.2) hx)
    have hdvd16 : Nat.card ↥(K ⊓ I) ∣ 16 := by
      rw [← h16]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hnt : 1 < Nat.card ↥(K ⊓ I) := by
      have hmemKI : i ∈ K ⊓ I := ⟨⟨hIV hi, hsi⟩, hi⟩
      have hpos : 0 < Nat.card ↥(K ⊓ I) := Nat.card_pos
      by_contra hle
      have hcs : Nat.card ↥(K ⊓ I) = 1 := by omega
      have := Subgroup.eq_bot_of_card_eq _ hcs
      rw [this] at hmemKI
      exact hi1 (mem_bot.1 hmemKI)
    have hKI16 : Nat.card ↥(K ⊓ I) = 16 := by
      obtain ⟨k, hk, hkI⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.card ↥(K ⊓ I) ∣ 2 ^ 4 by
        simpa using hdvd16)
      have hk' : 2 ^ k % 5 = 1 := by rw [← hkI]; exact hmod2
      rcases two_pow_mod_five_one (by omega) hk' with rfl | rfl | rfl
      · exfalso
        have : Nat.card ↥(K ⊓ I) = 1 := by simpa using hkI
        omega
      · simpa using hkI
      · omega
    have hIeq : K ⊓ I = I := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hKI16, h16])
    have : s v * v⁻¹ ∈ K ⊓ I := by rw [hIeq]; exact hmem
    rw [hKC]
    exact this.1

theorem delta_z₀ (h : SOK D S) {s : MulAut V} (hs : s ∈ S) :
    s D.z₀ * D.z₀⁻¹ = 1 ∨ s D.z₀ * D.z₀⁻¹ = D.z := by
  have hz₀ : D.z₀ ∈ D.Fx := (D.hxfix D.z₀).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hmem := h.mem_Fx hs hz₀
  rcases (D.mem_Fx_iff _).1 hmem with h1 | h1 | h1 | h1
  · exfalso
    exact D.z₀_ne_one (s.injective (by rw [h1, map_one]))
  · exfalso
    have : s D.z₀ = s D.z := by rw [h1, h.fix_z hs]
    exact D.z₀_ne_z (s.injective this)
  · left
    rw [h1, mul_inv_cancel]
  · right
    rw [h1]
    calc D.z * D.z₀ * D.z₀⁻¹ = D.z := by group

theorem dm_isHK (h : SOK D S) {s : MulAut V} (hs : s ∈ S) : IsHK D (dm s) := by
  refine ⟨fun v => ?_, fun e he => ?_, fun v => ?_, fun v => ?_⟩
  · have hv : v ∈ D.Fx ⊔ D.V₁ := by rw [D.Fx_sup_V₁]; exact mem_top v
    obtain ⟨f, hf, v₁, hv₁, rfl⟩ := Subgroup.mem_sup.1 hv
    rw [map_mul]
    refine D.E.mul_mem ?_ (((h.delta_V₁ hs hv₁ : s v₁ * v₁⁻¹ ∈ D.C)).1)
    rcases (D.mem_Fx_iff f).1 hf with rfl | rfl | rfl | rfl
    · simpa using one_mem D.E
    · rw [dm_apply, h.fix_z hs, mul_inv_cancel]
      exact one_mem _
    · rcases h.delta_z₀ hs with h1 | h1
      · rw [dm_apply, h1]; exact one_mem _
      · rw [dm_apply, h1]; exact D.hzE
    · rw [map_mul]
      refine D.E.mul_mem ?_ ?_
      · rw [dm_apply, h.fix_z hs, mul_inv_cancel]; exact one_mem _
      · rcases h.delta_z₀ hs with h1 | h1
        · rw [dm_apply, h1]; exact one_mem _
        · rw [dm_apply, h1]; exact D.hzE
  · rw [dm_apply, h.fix_E hs he, mul_inv_cancel]
  · rw [dm_apply, dm_apply, h.apply_x hs, map_mul, map_inv]
  · rw [dm_apply, dm_apply, h.apply_y hs, map_mul, map_inv]

theorem dm_injective (h : SOK D S) {s s' : MulAut V} (hs : s ∈ S) (hs' : s' ∈ S)
    (hss : dm s = dm s') : s = s' := by
  ext v
  have := congrArg (fun δ : V →* V => δ v) hss
  simpa [dm_apply] using this

theorem dm_mul (h : SOK D S) {s s' : MulAut V} (hs : s ∈ S) (hs' : s' ∈ S) (v : V) :
    dm (s * s') v = dm s v * dm s' v := by
  have h1 : s (dm s' v) = dm s' v := h.fix_E hs ((h.dm_isHK hs').mem v)
  have e : s' v = dm s' v * v := by rw [dm_apply]; group
  calc dm (s * s') v = s (s' v) * v⁻¹ := by rw [dm_apply, MulAut.mul_apply]
    _ = s (dm s' v * v) * v⁻¹ := by rw [← e]
    _ = (dm s' v * s v) * v⁻¹ := by rw [map_mul, h1]
    _ = dm s v * dm s' v := by rw [dm_apply s v]; ac_rfl

end SOK

@[expose] def F5Stmt : Prop :=
  ∀ {V : Type u} [CommGroup V] [Finite V], (∀ a : V, a * a = 1) → ∀ (W : Subgroup V),
    Nat.card W = 16 → ∀ (x y : MulAut V), x ^ 5 = 1 → (∀ w ∈ W, x w ∈ W) → (∀ w ∈ W, y w ∈ W) →
    (∀ w ∈ W, x w = w → w = 1) → y * x * y⁻¹ = x ^ 3 → ∀ w₀ : V, w₀ ∈ W → w₀ ≠ 1 → y w₀ = w₀ →
    ∀ w ∈ W, y w = w → w = 1 ∨ w = w₀

theorem mem_E_sup_iff (D : ThData V) (v : V) :
    v ∈ D.E ⊔ zpowers D.z₀ ↔ v ∈ D.E ∨ ∃ e ∈ D.E, v = D.z₀ * e := by
  rw [Subgroup.mem_sup]
  constructor
  · rintro ⟨e, he, w, hw, rfl⟩
    rcases eq_one_or_of_mem_zpowers (D.hsq D.z₀) hw with rfl | rfl
    · left; simpa using he
    · right; exact ⟨e, he, mul_comm _ _⟩
  · rintro (hv | ⟨e, he, rfl⟩)
    · exact ⟨v, hv, 1, one_mem _, mul_one v⟩
    · exact ⟨e, he, D.z₀, mem_zpowers _, mul_comm _ _⟩

theorem eps_z₀ (D : ThData V) : D.eps D.z₀ = D.z := by
  rw [eps_apply, D.hτz₀, mul_comm D.z₀ D.z, mul_assoc, mul_inv_cancel, mul_one]

theorem two_vals {p a b : V} (ha : a = 1 ∨ a = p) (hb : b = 1 ∨ b = p) (hp : p ≠ 1)
    (hiff : a = 1 ↔ b = 1) : a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exact absurd (hiff.1 rfl) hp
  · exact absurd (hiff.2 rfl) hp
  · rfl

instance finite_mulAut : Finite (MulAut V) :=
  Finite.of_injective (fun φ : MulAut V => (φ : V → V)) (fun a b h => MulEquiv.ext (congrFun h))

theorem thompson68_of_F5 (hF5 : F5Stmt.{u}) {V : Type u} [CommGroup V] [Finite V] (D : ThData V)
    {S : Subgroup (MulAut V)} (h : SOK D S) :
    S = zpowers D.τ ∨ ∃ β ∈ S, S = Subgroup.closure ({D.τ, β} : Set (MulAut V)) ∧
      (∀ v : V, β v = v ∨ β v = v * D.z) ∧
      (∀ v : V, β v = v ↔ ∃ a : V, v = D.x a * a⁻¹ ∨ v = D.x a * a⁻¹ * D.z) ∧
      (∃ v : V, ¬ ∃ a : V, v = D.x a * a⁻¹ ∨ v = D.x a * a⁻¹ * D.z) ∧
      (∀ v : V, (D.τ * β) v = v ↔ v ∈ D.E ⊔ zpowers D.z₀) := by
  classical
  obtain ⟨w₀, hw₀C, hw₀1, hw₀y⟩ := D.exists_w₀
  obtain ⟨w₁, hw₁V, hw₁ε⟩ := D.exists_eps_eq hw₀C
  have hCy : ∀ w ∈ D.C, D.y w = w → w = 1 ∨ w = w₀ :=
    hF5 D.hsq D.C D.card_C D.x D.y D.hx5 (fun w hw => D.x_mem_C hw) (fun w hw => D.y_mem_C hw)
      (fun w hw hx => D.fpf_V₁ hw.2 hx) D.hyx w₀ hw₀C hw₀1 hw₀y
  have hz₀vals : ∀ s ∈ S, dm s D.z₀ = 1 ∨ dm s D.z₀ = D.z := fun s hs =>
    (h.dm_isHK hs).apply_z₀
  have hw₁vals : ∀ s ∈ S, dm s w₁ = 1 ∨ dm s w₁ = w₀ := by
    intro s hs
    have hHK := h.dm_isHK hs
    exact hCy _ (hHK.apply_V₁ hw₁V) (hHK.y_apply_w₁ hw₁V hw₁ε hw₀y)
  have hext : ∀ s ∈ S, ∀ s' ∈ S, dm s D.z₀ = dm s' D.z₀ → dm s w₁ = dm s' w₁ → s = s' := by
    intro s hs s' hs' h1 h2
    exact h.dm_injective hs hs'
      ((h.dm_isHK hs).ext_of (h.dm_isHK hs') hw₀1 hw₁V hw₁ε h1 h2)
  have hcard4 : Nat.card S ≤ 4 := by
    let key : S → Bool × Bool := fun s => (decide (dm s.1 D.z₀ = 1), decide (dm s.1 w₁ = 1))
    have hinj : Function.Injective key := by
      intro a b hab
      apply Subtype.ext
      obtain ⟨hab1, hab2⟩ := Prod.mk.inj hab
      refine hext a.1 a.2 b.1 b.2 ?_ ?_
      · exact two_vals (hz₀vals a.1 a.2) (hz₀vals b.1 b.2) D.hz1 (by simpa using hab1)
      · exact two_vals (hw₁vals a.1 a.2) (hw₁vals b.1 b.2) hw₀1 (by simpa using hab2)
    have := Nat.card_le_card_of_injective key hinj
    simpa using this
  have hτ1 : D.τ ≠ 1 := by
    intro h1
    have := D.hτz₀
    rw [h1] at this
    apply D.hz1
    have h2 : D.z₀ = D.z₀ * D.z := by simpa using this
    have := congrArg (fun w => D.z₀⁻¹ * w) h2
    simpa using this.symm
  have hτcard : Nat.card (zpowers D.τ) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact D.hτ2) hτ1
  have hzτ : zpowers D.τ ≤ S := zpowers_le.2 h.tau
  have hSpow : ∃ n, Nat.card S = 2 ^ n := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (IsPGroup.iff_card).1 h.pgroup
  have hS2 : 2 ≤ Nat.card S := hτcard ▸ Subgroup.card_le_of_le hzτ
  have hSc : Nat.card S = 2 ∨ Nat.card S = 4 := by
    obtain ⟨n, hn⟩ := hSpow
    have hn2 : n ≤ 2 := by
      by_contra hcon
      push Not at hcon
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hcon
      rw [hn] at hcard4
      omega
    rw [hn] at hS2 ⊢
    interval_cases n <;> simp_all
  rcases hSc with h2 | h4
  · left
    exact (Subgroup.eq_of_le_of_card_ge hzτ (by rw [h2, hτcard])).symm
  · right
    obtain ⟨s, hsS, hsτ⟩ : ∃ s ∈ S, s ∉ zpowers D.τ := by
      by_contra hcon
      push Not at hcon
      have hle : S ≤ zpowers D.τ := hcon
      have := Subgroup.card_le_of_le hle
      rw [h4, hτcard] at this
      omega
    have hs1 : s ≠ 1 := fun e => hsτ (e ▸ one_mem _)
    have hsτ' : s ≠ D.τ := fun e => hsτ (e ▸ mem_zpowers _)
    have hd1 : ∀ v : V, dm (1 : MulAut V) v = 1 := fun v => by simp [dm_apply]
    have hdτ : ∀ v, dm D.τ v = D.eps v := fun v => rfl
    have hpair1 : ¬ (dm s D.z₀ = 1 ∧ dm s w₁ = 1) := by
      rintro ⟨h1, h2⟩
      exact hs1 (h.dm_injective hsS (one_mem S)
        ((h.dm_isHK hsS).ext_of (h.dm_isHK (one_mem S)) hw₀1 hw₁V hw₁ε
          (h1.trans (hd1 _).symm) (h2.trans (hd1 _).symm)))
    have hpairτ : ¬ (dm s D.z₀ = D.z ∧ dm s w₁ = w₀) := by
      rintro ⟨h1, h2⟩
      exact hsτ' (h.dm_injective hsS h.tau
        ((h.dm_isHK hsS).ext_of (h.dm_isHK h.tau) hw₀1 hw₁V hw₁ε
          (by rw [h1, hdτ, D.eps_z₀]) (by rw [h2, hdτ, hw₁ε])))
    obtain ⟨β, hβS, hβτ, hβz₀, hβw₁⟩ : ∃ β ∈ S, β ∉ zpowers D.τ ∧ dm β D.z₀ = D.z ∧
        dm β w₁ = 1 := by
      rcases hz₀vals s hsS with h1 | h1 <;> rcases hw₁vals s hsS with h2 | h2
      · exact absurd ⟨h1, h2⟩ hpair1
      · refine ⟨D.τ * s, mul_mem h.tau hsS, fun hmem => hsτ ?_, ?_, ?_⟩
        · have := (zpowers D.τ).mul_mem ((zpowers D.τ).inv_mem (mem_zpowers D.τ)) hmem
          rwa [inv_mul_cancel_left] at this
        · rw [h.dm_mul h.tau hsS, hdτ, D.eps_z₀, h1, mul_one]
        · rw [h.dm_mul h.tau hsS, hdτ, hw₁ε, h2, D.hsq]
      · exact ⟨s, hsS, hsτ, h1, h2⟩
      · exact absurd ⟨h1, h2⟩ hpairτ
    have hHK := h.dm_isHK hβS
    have hHK1 : IsHK D (1 : V →* V) :=
      ⟨fun v => by simpa using one_mem D.E, fun e he => rfl, fun v => by simp, fun v => by simp⟩
    have hδV₁ : ∀ v ∈ D.V₁, dm β v = 1 := fun v hv => by
      have := hHK.eq_on_V₁ hHK1 hw₀1 hw₁V hw₁ε (by rw [hβw₁]; rfl) v hv
      simpa using this
    have hdec : ∀ v : V, ∃ f ∈ D.Fx, ∃ v₁ ∈ D.V₁, v = f * v₁ := fun v => by
      have hv : v ∈ D.Fx ⊔ D.V₁ := by rw [D.Fx_sup_V₁]; exact mem_top v
      obtain ⟨f, hf, v₁, hv₁, e⟩ := Subgroup.mem_sup.1 hv
      exact ⟨f, hf, v₁, hv₁, e.symm⟩
    have hδFx : ∀ f ∈ D.Fx, (dm β f = 1 ↔ f = 1 ∨ f = D.z) ∧ (dm β f = 1 ∨ dm β f = D.z) := by
      intro f hf
      have hz1 : dm β D.z = 1 := hHK.triv _ D.hzE
      rcases (D.mem_Fx_iff f).1 hf with rfl | rfl | rfl | rfl
      · simp
      · simp [hz1]
      · refine ⟨?_, Or.inr hβz₀⟩
        rw [hβz₀]
        constructor
        · intro e; exact absurd e D.hz1
        · rintro (e | e)
          · exact absurd e D.z₀_ne_one
          · exact absurd e D.z₀_ne_z
      · have e : dm β (D.z * D.z₀) = D.z := by rw [map_mul, hz1, hβz₀, one_mul]
        refine ⟨?_, Or.inr e⟩
        rw [e]
        constructor
        · intro e'; exact absurd e' D.hz1
        · rintro (e' | e')
          · exact absurd e' D.zz₀_ne_one
          · exact absurd (mul_eq_left.1 e') D.z₀_ne_one
    have hδv : ∀ v, dm β v = 1 ∨ dm β v = D.z := fun v => by
      obtain ⟨f, hf, v₁, hv₁, rfl⟩ := hdec v
      rw [map_mul, hδV₁ v₁ hv₁, mul_one]
      exact (hδFx f hf).2
    have hβv : ∀ v, β v = dm β v * v := fun v => by rw [dm_apply]; group
    refine ⟨β, hβS, ?_, ?_, ?_, ?_, ?_⟩
    ·
      have hcl : Subgroup.closure ({D.τ, β} : Set (MulAut V)) ≤ S := by
        rw [Subgroup.closure_le]
        rintro g (rfl | rfl)
        · exact h.tau
        · exact hβS
      have hzcl : zpowers D.τ ≤ Subgroup.closure ({D.τ, β} : Set (MulAut V)) :=
        zpowers_le.2 (Subgroup.subset_closure (by simp))
      have hβcl : β ∈ Subgroup.closure ({D.τ, β} : Set (MulAut V)) :=
        Subgroup.subset_closure (by simp)
      have hgt : 2 < Nat.card (Subgroup.closure ({D.τ, β} : Set (MulAut V))) := by
        have hle := Subgroup.card_le_of_le hzcl
        rw [hτcard] at hle
        by_contra hcon
        have heq : Nat.card (Subgroup.closure ({D.τ, β} : Set (MulAut V))) = 2 := by omega
        have := Subgroup.eq_of_le_of_card_ge hzcl (by rw [heq, hτcard])
        exact hβτ (this ▸ hβcl)
      have hdvd : Nat.card (Subgroup.closure ({D.τ, β} : Set (MulAut V))) ∣ 4 := by
        rw [← h4]
        exact Subgroup.card_dvd_of_le hcl
      have h4' : Nat.card (Subgroup.closure ({D.τ, β} : Set (MulAut V))) = 4 := by
        have hle : Nat.card (Subgroup.closure ({D.τ, β} : Set (MulAut V))) ≤ 4 :=
          Nat.le_of_dvd (by norm_num) hdvd
        generalize Nat.card (Subgroup.closure ({D.τ, β} : Set (MulAut V))) = m at hgt hdvd hle ⊢
        interval_cases m <;> simp_all
      exact (Subgroup.eq_of_le_of_card_ge hcl (by rw [h4, h4'])).symm
    · intro v
      rcases hδv v with e | e
      · left; rw [hβv, e, one_mul]
      · right; rw [hβv, e, mul_comm]
    · intro v
      constructor
      · intro hv
        have h1 : dm β v = 1 := by rw [dm_eq_one_iff]; exact hv
        obtain ⟨f, hf, v₁, hv₁, rfl⟩ := hdec v
        rw [map_mul, hδV₁ v₁ hv₁, mul_one] at h1
        obtain ⟨a, rfl⟩ := hv₁
        rcases (hδFx f hf).1.1 h1 with rfl | rfl
        · exact ⟨a, Or.inl (by rw [one_mul]; rfl)⟩
        · exact ⟨a, Or.inr (by rw [mul_comm]; rfl)⟩
      · rintro ⟨a, rfl | rfl⟩
        · rw [← dm_eq_one_iff]
          exact hδV₁ _ (D.xm1_mem_V₁ a)
        · rw [← dm_eq_one_iff, map_mul, hδV₁ _ (D.xm1_mem_V₁ a), hHK.triv _ D.hzE, mul_one]
    · refine ⟨D.z₀, ?_⟩
      rintro ⟨a, ha⟩
      have hfix : β D.z₀ = D.z₀ := by
        rw [← dm_eq_one_iff]
        rcases ha with e | e
        · rw [e]; exact hδV₁ _ (D.xm1_mem_V₁ a)
        · rw [e, map_mul, hδV₁ _ (D.xm1_mem_V₁ a), hHK.triv _ D.hzE, mul_one]
      rw [← dm_eq_one_iff, hβz₀] at hfix
      exact D.hz1 hfix
    · intro v
      have hτβ : (D.τ * β) v = (dm β v * D.eps v) * v := by
        rw [MulAut.mul_apply, hβv, map_mul, (D.hτE _).2 (hHK.mem v), eps_apply]
        group
      rw [hτβ, mul_eq_right, mem_E_sup_iff]
      constructor
      · intro hv
        have hδ := hδv v
        rcases hδ with e | e
        · rw [e, one_mul] at hv
          left
          exact (D.eps_eq_one_iff v).1 hv
        · rw [e] at hv
          right
          have hev : D.eps v = D.z := by
            have := eq_inv_of_mul_eq_one_right hv
            rwa [D.inv_eq] at this
          refine ⟨v * D.z₀⁻¹, ?_, by rw [mul_comm v (D.z₀⁻¹), mul_inv_cancel_left]⟩
          rw [← D.eps_eq_one_iff, map_mul, map_inv, D.eps_z₀, hev, mul_inv_cancel]
      · rintro (hv | ⟨e, he, rfl⟩)
        · rw [hHK.triv v hv, (D.eps_eq_one_iff v).2 hv, one_mul]
        · rw [map_mul, hβz₀, hHK.triv e he, mul_one, map_mul, D.eps_z₀, (D.eps_eq_one_iff e).2 he,
            mul_one]
          exact D.z_sq

end ThData

end CFSG.LocalAnalysis.EvenBN.Tits.N
