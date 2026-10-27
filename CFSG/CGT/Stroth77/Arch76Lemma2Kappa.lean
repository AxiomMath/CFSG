module

public import CFSG.CGT.Stroth77.Arch76Lemma2Coord
import Mathlib.Tactic.Abel

public section

namespace CFSG.CGT.Stroth77.Arch76

@[expose] def dl (r : Co × Co) (v : Co) : Co := v.2.1.val • r.1 + v.2.2.val • r.2

@[expose] def kmap (r : Co × Co) (v : Co) : Co := v + dl r v

@[expose] def X0 : Co := (0, 1, 0)

@[expose] def Y0 : Co := (0, 0, 1)

@[expose] def Lof (f g : Co → Co) (r : Co × Co) : Co × Co := (f (dl r (g X0)), f (dl r (g Y0)))

@[expose] def Luv : Co × Co → Co × Co := Lof fuv fuv

@[expose] def Lt : Co × Co → Co × Co := Lof ft ft

@[expose] def Lu : Co × Co → Co × Co := Lof fu fu

@[expose] def Lρ : Co × Co → Co × Co := Lof fρ (fun v => fρ (fρ v))

theorem lin_basis (v : Co) : lin (1, 0, 0) (0, 1, 0) (0, 0, 1) v = v := by
  revert v; decide

theorem lin_basis' (v : Co) : lin (1, 0, 0) X0 Y0 v = v := lin_basis v

theorem fρ_fρ_fρ (v : Co) : fρ (fρ (fρ v)) = v := by
  revert v; decide

theorem fuv_fuv (v : Co) : fuv (fuv v) = v := by revert v; decide
theorem ft_ft (v : Co) : ft (ft v) = v := by revert v; decide
theorem fu_fu (v : Co) : fu (fu v) = v := by revert v; decide

namespace Config

section

variable {X : Type*} [Group X] (C : Config X)

@[expose] def Om : Set X := {a | ∃ v : Co, 2 • v = 0 ∧ C.ev v = a}

@[expose] def K : Subgroup X := Subgroup.centralizer C.Om

end

variable {X : Type*} [Group X] (C : Config X) [hN : C.A.Normal]

theorem conj_mem_A {g a : X} (ha : a ∈ C.A) : g⁻¹ * a * g ∈ C.A := by
  have h := hN.conj_mem a ha g⁻¹
  rwa [inv_inv] at h

noncomputable def act (g : X) (v : Co) : Co :=
  Classical.choose (C.exists_ev (C.conj_mem_A (g := g) (C.ev_mem v)))

theorem ev_act (g : X) (v : Co) : C.ev (C.act g v) = g⁻¹ * C.ev v * g :=
  Classical.choose_spec (C.exists_ev (C.conj_mem_A (g := g) (C.ev_mem v)))

theorem act_eq_of {g : X} {v w : Co} (h : C.ev w = g⁻¹ * C.ev v * g) : C.act g v = w :=
  C.ev_injective (by rw [ev_act, h])

theorem act_mul (g h : X) (v : Co) : C.act (g * h) v = C.act h (C.act g v) :=
  C.act_eq_of (by rw [ev_act, ev_act]; group)

theorem act_one (v : Co) : C.act 1 v = v := C.act_eq_of (by group)

theorem act_add (g : X) (v v' : Co) : C.act g (v + v') = C.act g v + C.act g v' :=
  C.act_eq_of (by rw [ev_add, ev_add, ev_act, ev_act]; group)

theorem act_zero (g : X) : C.act g 0 = 0 := C.act_eq_of (by simp)

theorem act_nsmul (g : X) (n : ℕ) (v : Co) : C.act g (n • v) = n • C.act g v := by
  induction n with
  | zero => simp [act_zero]
  | succ n ih => rw [succ_nsmul, act_add, ih, succ_nsmul]

theorem act_lin (g : X) (a b c v : Co) :
    C.act g (lin a b c v) = lin (C.act g a) (C.act g b) (C.act g c) v := by
  simp only [lin, act_add, act_nsmul]

theorem act_uv (v : Co) : C.act C.uv v = fuv v := C.act_eq_of (C.conj_uv_ev v).symm
theorem act_t (v : Co) : C.act C.t v = ft v := C.act_eq_of (C.conj_t_ev v).symm
theorem act_u (v : Co) : C.act C.u v = fu v := C.act_eq_of (C.conj_u_ev v).symm
theorem act_ρ (v : Co) : C.act C.ρ v = fρ v := C.act_eq_of (C.conj_ρ_ev v).symm

theorem act_inv_of {g : X} {f : Co → Co} (hg : ∀ v, C.act g v = f v) {f' : Co → Co}
    (hf : ∀ v, f (f' v) = v) (v : Co) : C.act g⁻¹ v = f' v := by
  apply C.ev_injective
  have h := C.ev_act g (f' v)
  rw [hg, hf] at h
  rw [ev_act, h]
  group

theorem act_uv_inv (v : Co) : C.act C.uv⁻¹ v = fuv v := C.act_inv_of C.act_uv fuv_fuv v
theorem act_t_inv (v : Co) : C.act C.t⁻¹ v = ft v := C.act_inv_of C.act_t ft_ft v
theorem act_u_inv (v : Co) : C.act C.u⁻¹ v = fu v := C.act_inv_of C.act_u fu_fu v
theorem act_ρ_inv (v : Co) : C.act C.ρ⁻¹ v = fρ (fρ v) := C.act_inv_of C.act_ρ fρ_fρ_fρ v

theorem act_two_nsmul {g : X} {v : Co} (hv : 2 • v = 0) : 2 • C.act g v = 0 := by
  rw [← act_nsmul, hv, act_zero]

theorem mem_K_iff {k : X} : k ∈ C.K ↔ ∀ v : Co, 2 • v = 0 → C.act k v = v := by
  constructor
  · intro hk v hv
    apply C.act_eq_of
    have h := Subgroup.mem_centralizer_iff.mp hk (C.ev v) ⟨v, hv, rfl⟩
    rw [mul_assoc, h, inv_mul_cancel_left]
  · intro h
    rw [K, Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have h2 := C.ev_act k v
    rw [h v hv] at h2
    calc C.ev v * k = k * (k⁻¹ * C.ev v * k) := by group
      _ = k * C.ev v := by rw [← h2]

@[expose] noncomputable def kap (k : X) : Co × Co := (C.act k X0 - X0, C.act k Y0 - Y0)

theorem kap_two_nsmul {k : X} (hk : k ∈ C.K) : 2 • (C.kap k).1 = 0 ∧ 2 • (C.kap k).2 = 0 := by
  have hX : C.act k (2 • X0) = 2 • X0 := (C.mem_K_iff.mp hk) _ (by decide)
  have hY : C.act k (2 • Y0) = 2 • Y0 := (C.mem_K_iff.mp hk) _ (by decide)
  rw [act_nsmul] at hX hY
  refine ⟨?_, ?_⟩
  · simp only [kap, nsmul_sub, hX, sub_self]
  · simp only [kap, nsmul_sub, hY, sub_self]

theorem kap_fst (k : X) : (C.kap k).1 = C.act k X0 - X0 := rfl
theorem kap_snd (k : X) : (C.kap k).2 = C.act k Y0 - Y0 := rfl

theorem act_X0 (k : X) : C.act k X0 = X0 + (C.kap k).1 := by rw [kap_fst]; abel
theorem act_Y0 (k : X) : C.act k Y0 = Y0 + (C.kap k).2 := by rw [kap_snd]; abel

theorem act_of_mem_K {k : X} (hk : k ∈ C.K) (v : Co) : C.act k v = kmap (C.kap k) v := by
  have hW : C.act k (1, 0, 0) = (1, 0, 0) := (C.mem_K_iff.mp hk) _ (by decide)
  calc C.act k v = C.act k (lin (1, 0, 0) X0 Y0 v) := by rw [lin_basis']
    _ = lin (1, 0, 0) (X0 + (C.kap k).1) (Y0 + (C.kap k).2) v := by
      rw [act_lin, hW, act_X0, act_Y0]
    _ = lin (1, 0, 0) X0 Y0 v + dl (C.kap k) v := by simp only [lin, dl, nsmul_add]; abel
    _ = kmap (C.kap k) v := by rw [lin_basis']; rfl

theorem kap_mul {k₁ k₂ : X} (h₁ : k₁ ∈ C.K) (h₂ : k₂ ∈ C.K) :
    C.kap (k₁ * k₂) = C.kap k₁ + C.kap k₂ := by
  obtain ⟨hx₁, hy₁⟩ := C.kap_two_nsmul h₁
  have f1 : C.act k₂ (C.kap k₁).1 = (C.kap k₁).1 := (C.mem_K_iff.mp h₂) _ hx₁
  have f2 : C.act k₂ (C.kap k₁).2 = (C.kap k₁).2 := (C.mem_K_iff.mp h₂) _ hy₁
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_add, C.kap_fst (k₁ * k₂), act_mul, C.act_X0 k₁, act_add, f1, C.act_X0 k₂]
    abel
  · rw [Prod.snd_add, C.kap_snd (k₁ * k₂), act_mul, C.act_Y0 k₁, act_add, f2, C.act_Y0 k₂]
    abel

theorem act_of_mem_A {a : X} (ha : a ∈ C.A) (v : Co) : C.act a v = v :=
  C.act_eq_of (by
    rw [C.comm (inv_mem ha) (C.ev_mem v), mul_assoc, inv_mul_cancel, mul_one])

theorem A_le_K : C.A ≤ C.K := fun a ha => C.mem_K_iff.mpr fun v _ => C.act_of_mem_A ha v

theorem kap_of_mem_A {a : X} (ha : a ∈ C.A) : C.kap a = 0 := by
  simp [kap, C.act_of_mem_A ha]

theorem kap_eq_zero_iff (hCA : Subgroup.centralizer (C.A : Set X) = C.A) {k : X}
    (hk : k ∈ C.K) : C.kap k = 0 ↔ k ∈ C.A := by
  refine ⟨fun h => ?_, C.kap_of_mem_A⟩
  rw [← hCA, Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨v, rfl⟩ := C.exists_ev ha
  have h1 := C.ev_act k v
  rw [C.act_of_mem_K hk, h] at h1
  have h2 : kmap 0 v = v := by simp [kmap, dl]
  rw [h2] at h1
  calc C.ev v * k = k * (k⁻¹ * C.ev v * k) := by group
    _ = k * C.ev v := by rw [← h1]

theorem conj_mem_K {k : X} (hk : k ∈ C.K) (g : X) : g⁻¹ * k * g ∈ C.K := by
  rw [mem_K_iff]
  intro v hv
  rw [act_mul, act_mul]
  rw [(C.mem_K_iff.mp hk) _ (C.act_two_nsmul hv), ← act_mul, inv_mul_cancel, act_one]

theorem kap_conj {k : X} (hk : k ∈ C.K) {g : X} {f f' : Co → Co} (hf : ∀ v, C.act g v = f v)
    (hf' : ∀ v, C.act g⁻¹ v = f' v) : C.kap (g⁻¹ * k * g) = Lof f f' (C.kap k) := by
  have hadd : ∀ v v', f (v + v') = f v + f v' := fun v v' => by
    rw [← hf, ← hf, ← hf, act_add]
  have hinv : ∀ v, f (f' v) = v := fun v => by
    rw [← hf, ← hf', ← act_mul, inv_mul_cancel, act_one]
  refine Prod.ext ?_ ?_
  · rw [C.kap_fst, act_mul, act_mul, hf', C.act_of_mem_K hk, kmap, hf, hadd, hinv]
    exact add_sub_cancel_left _ _
  · rw [C.kap_snd, act_mul, act_mul, hf', C.act_of_mem_K hk, kmap, hf, hadd, hinv]
    exact add_sub_cancel_left _ _

theorem kap_conj_uv {k : X} (hk : k ∈ C.K) : C.kap (C.uv⁻¹ * k * C.uv) = Luv (C.kap k) :=
  C.kap_conj hk C.act_uv C.act_uv_inv
theorem kap_conj_t {k : X} (hk : k ∈ C.K) : C.kap (C.t⁻¹ * k * C.t) = Lt (C.kap k) :=
  C.kap_conj hk C.act_t C.act_t_inv
theorem kap_conj_u {k : X} (hk : k ∈ C.K) : C.kap (C.u⁻¹ * k * C.u) = Lu (C.kap k) :=
  C.kap_conj hk C.act_u C.act_u_inv
theorem kap_conj_ρ {k : X} (hk : k ∈ C.K) : C.kap (C.ρ⁻¹ * k * C.ρ) = Lρ (C.kap k) :=
  C.kap_conj hk C.act_ρ C.act_ρ_inv

end Config

end CFSG.CGT.Stroth77.Arch76
