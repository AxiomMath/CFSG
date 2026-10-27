module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S7A
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S10Fin
public import Certificates.Certificate17027
public import Certificates.Certificate5952

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

namespace StdCfg

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

@[expose] noncomputable def zp (C : StdCfg T M H S L) (t : ZMod 2) : G :=
  if t = 0 then 1 else C.zU

theorem zp_add (C : StdCfg T M H S L) (s t : ZMod 2) : C.zp (s + t) = C.zp s * C.zp t := by
  have hzz : C.zU * C.zU = 1 := C.zU_mul_self
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl <;>
    simp [zp, hzz, h11]

theorem zp_eq_aux (C : StdCfg T M H S L) {c : G} (hc : c = 1 ∨ c = C.zU) (a b d : ZMod 2)
    (h : C.zp (a + b + d) = c * C.zp b * C.zp a) : c = C.zp d := by
  have hzz : C.zU * C.zU = 1 := C.zU_mul_self
  have hz1 : C.zU ≠ 1 := C.zU_ne_one
  have hz1' : (1 : G) ≠ C.zU := hz1.symm
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases hc with rfl | rfl <;> rcases zmod2_cases a with rfl | rfl <;>
    rcases zmod2_cases b with rfl | rfl <;> rcases zmod2_cases d with rfl | rfl <;>
    simp_all [zp]

theorem P_le_M (C : StdCfg T M H S L) : borelP M L ≤ M :=
  (borelP_le_M1 T M L).trans C.M1_le_M

end StdCfg

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

theorem zU_comm_M {m : G} (hm : m ∈ M) : C.zU * m = m * C.zU :=
  Subgroup.mem_centralizer_iff.mp (X.M_le_GZ hm) C.zU rfl

theorem zp_comm_M
    (t : ZMod 2) {m : G} (hm : m ∈ M) : C.zp t * m = m * C.zp t := by
  rcases zmod2_cases t with rfl | rfl
  · simp [StdCfg.zp]
  · simpa [StdCfg.zp] using X.zU_comm_M hm

open Classical in
@[expose] noncomputable def th (g : G) : V4 :=
  if h : g ∈ borelP M L then Multiplicative.toAdd (X.thG ⟨g, h⟩) else 0

theorem th_of_mem {p : G} (hp : p ∈ borelP M L) :
    X.th p = Multiplicative.toAdd (X.thG ⟨p, hp⟩) := by simp [th, hp]

theorem th_one : X.th 1 = 0 := by
  rw [X.th_of_mem (one_mem _)]
  exact congrArg Multiplicative.toAdd (map_one X.thG)

theorem th_mul
    {p q : G} (hp : p ∈ borelP M L) (hq : q ∈ borelP M L) :
    X.th (p * q) = X.th p + X.th q := by
  rw [X.th_of_mem (mul_mem hp hq), X.th_of_mem hp, X.th_of_mem hq]
  exact congrArg Multiplicative.toAdd (map_mul X.thG ⟨p, hp⟩ ⟨q, hq⟩)

theorem th_inv
    {p : G} (hp : p ∈ borelP M L) : X.th p⁻¹ = X.th p := by
  rw [X.th_of_mem (inv_mem hp), X.th_of_mem hp]
  have : X.thG ⟨p⁻¹, inv_mem hp⟩ = (X.thG ⟨p, hp⟩)⁻¹ := map_inv X.thG ⟨p, hp⟩
  rw [this, toAdd_inv]
  exact V4_neg _

theorem th_exists (v : V4) : ∃ p ∈ borelP M L, X.th p = v := by
  obtain ⟨p, hp⟩ := X.thG_surj (Multiplicative.ofAdd v)
  refine ⟨p, p.2, ?_⟩
  rw [X.th_of_mem p.2]
  exact congrArg Multiplicative.toAdd hp

theorem th_eq_zero_iff
    {p : G} (hp : p ∈ borelP M L) : X.th p = 0 ↔ p = 1 ∨ p = C.zU := by
  rw [← X.centerOf_P_iff, X.th_of_mem hp]
  constructor
  · intro h
    have h1 : X.thG ⟨p, hp⟩ = 1 := Multiplicative.toAdd.injective (by rw [toAdd_one]; exact h)
    have : (⟨p, hp⟩ : ↥(borelP M L)) ∈ X.thG.ker := h1
    rw [X.thG_ker] at this
    exact this
  · intro h
    have : (⟨p, hp⟩ : ↥(borelP M L)) ∈ (centerOf (borelP M L)).subgroupOf (borelP M L) := h
    rw [← X.thG_ker] at this
    have h1 : X.thG ⟨p, hp⟩ = 1 := this
    have := congrArg Multiplicative.toAdd h1
    rwa [toAdd_one] at this

theorem th_zU
    : X.th C.zU = 0 := (X.th_eq_zero_iff X.zU_mem_P).mpr (Or.inr rfl)

theorem th_fiber
    {p q : G} (hp : p ∈ borelP M L) (hq : q ∈ borelP M L) (h : X.th p = X.th q) :
    p = q ∨ p = q * C.zU := by
  have hpq : p * q⁻¹ ∈ borelP M L := mul_mem hp (inv_mem hq)
  have h0 : X.th (p * q⁻¹) = 0 := by
    rw [X.th_mul hp (inv_mem hq), X.th_inv hq, h]
    exact V4_add_self _
  rcases (X.th_eq_zero_iff hpq).mp h0 with h1 | h1
  · left
    calc p = (p * q⁻¹) * q := by group
      _ = q := by rw [h1, one_mul]
  · right
    have hqM : q ∈ M := C.P_le_M hq
    calc p = (p * q⁻¹) * q := by group
      _ = C.zU * q := by rw [h1]
      _ = q * C.zU := X.zU_comm_M hqM

theorem sq_th {p : G} (hp : p ∈ borelP M L) :
    (p * p = 1 ∧ quadHyp (X.th p) = 0) ∨ (p * p = C.zU ∧ quadHyp (X.th p) = 1) := by
  rw [X.th_of_mem hp]
  exact X.sq_cases ⟨p, hp⟩

theorem sq_eq_zp
    {p : G} (hp : p ∈ borelP M L) : p * p = C.zp (quadHyp (X.th p)) := by
  rcases X.sq_th hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    simp [StdCfg.zp]
  · rw [h1, h2]
    simp [StdCfg.zp]

theorem comm_th
    {p q : G} (hp : p ∈ borelP M L) (hq : q ∈ borelP M L) :
    p * q * p⁻¹ * q⁻¹ = C.zp (Bf (X.th p) (X.th q)) := by
  set c : G := p * q * p⁻¹ * q⁻¹ with hc
  have hcP : c ∈ borelP M L := mul_mem (mul_mem (mul_mem hp hq) (inv_mem hp)) (inv_mem hq)
  have hc0 : X.th c = 0 := by
    rw [hc, X.th_mul (mul_mem (mul_mem hp hq) (inv_mem hp)) (inv_mem hq),
      X.th_mul (mul_mem hp hq) (inv_mem hp), X.th_mul hp hq, X.th_inv hp, X.th_inv hq]
    exact V4_four _ _
  have hqM : q ∈ M := C.P_le_M hq
  have hpqP : p * q ∈ borelP M L := mul_mem hp hq
  have e1 : p * q = c * (q * p) := by rw [hc]; group
  have e2 : p * q * (p * q) = c * (q * q) * (p * p) := by
    calc p * q * (p * q) = (c * (q * p)) * (p * q) := by rw [← e1]
      _ = c * (q * (p * p) * q) := by group
      _ = c * (q * (C.zp (quadHyp (X.th p)) * q)) := by rw [X.sq_eq_zp hp]; group
      _ = c * (q * (q * C.zp (quadHyp (X.th p)))) := by rw [X.zp_comm_M (quadHyp (X.th p)) hqM]
      _ = c * (q * q) * C.zp (quadHyp (X.th p)) := by group
      _ = c * (q * q) * (p * p) := by rw [X.sq_eq_zp hp]
  rw [X.sq_eq_zp hpqP, X.sq_eq_zp hq, X.sq_eq_zp hp, X.th_mul hp hq, quad_add] at e2
  exact C.zp_eq_aux ((X.th_eq_zero_iff hcP).mp hc0) _ _ _ e2

open Classical in
@[expose] noncomputable def rg (m : G) : GL (Fin 4) (ZMod 2) :=
  if h : m ∈ M then X.rho' ⟨m, h⟩ else 1

theorem rg_of_mem
    {m : G} (hm : m ∈ M) : X.rg m = X.rho' ⟨m, hm⟩ := by simp [rg, hm]

theorem rg_mul
    {m n : G} (hm : m ∈ M) (hn : n ∈ M) : X.rg (m * n) = X.rg m * X.rg n := by
  rw [X.rg_of_mem (mul_mem hm hn), X.rg_of_mem hm, X.rg_of_mem hn]
  exact map_mul X.rho' ⟨m, hm⟩ ⟨n, hn⟩

theorem rg_one : X.rg 1 = 1 := by
  rw [X.rg_of_mem (one_mem _)]
  exact map_one X.rho'

theorem rg_inv {m : G} (hm : m ∈ M) : X.rg m⁻¹ = (X.rg m)⁻¹ := by
  rw [X.rg_of_mem (inv_mem hm), X.rg_of_mem hm]
  exact map_inv X.rho' ⟨m, hm⟩

theorem rg_pow
    {m : G} (hm : m ∈ M) (k : ℕ) : X.rg (m ^ k) = X.rg m ^ k := by
  rw [X.rg_of_mem (pow_mem hm k), X.rg_of_mem hm]
  exact map_pow X.rho' ⟨m, hm⟩ k

theorem rg_mem_O4
    {m : G} (hm : m ∈ M) : X.rg m ∈ O4PlusTwo := by
  rw [X.rg_of_mem hm, ← X.rho'_range]
  exact ⟨_, rfl⟩

theorem rg_eq_one_iff
    {m : G} (hm : m ∈ M) : X.rg m = 1 ↔ m ∈ borelP M L := by
  rw [X.rg_of_mem hm]
  have h := X.rho'_ker
  constructor
  · intro h1
    have : (⟨m, hm⟩ : ↥M) ∈ X.rho'.ker := h1
    rw [h] at this
    exact this
  · intro h1
    have : (⟨m, hm⟩ : ↥M) ∈ (borelP M L).subgroupOf M := h1
    rw [← h] at this
    exact this

theorem exists_of_mem_O4
    {g : GL (Fin 4) (ZMod 2)} (hg : g ∈ O4PlusTwo) :
    ∃ m ∈ M, X.rg m = g := by
  rw [← X.rho'_range] at hg
  obtain ⟨m, rfl⟩ := hg
  exact ⟨m, m.2, X.rg_of_mem m.2⟩

theorem th_conj {m : G} (hm : m ∈ M) {p : G} (hp : p ∈ borelP M L) :
    m * p * m⁻¹ ∈ borelP M L ∧ X.th (m * p * m⁻¹) = ((X.rg m : GL (Fin 4) (ZMod 2)) : Mat4).mulVec
      (X.th p) := by
  have hmn : m ∈ Subgroup.normalizer (borelP M L : Set G) := X.M_le_normalizer_P hm
  have hy : m * p * m⁻¹ ∈ borelP M L := (Subgroup.mem_normalizer_iff.mp hmn p).mp hp
  refine ⟨hy, ?_⟩
  rw [X.th_of_mem hy, X.th_of_mem hp, X.rg_of_mem hm]
  exact X.rho'_spec ⟨m, hm⟩ ⟨p, hp⟩ ⟨m * p * m⁻¹, hy⟩ rfl

@[expose] def Qsub
    (Pr : V4 → Prop) (h0 : Pr 0) (hadd : ∀ x y, Pr x → Pr y → Pr (x + y)) :
    Subgroup G where
  carrier := {p | p ∈ borelP M L ∧ Pr (X.th p)}
  mul_mem' := fun {a b} ha hb =>
    ⟨mul_mem ha.1 hb.1, by rw [X.th_mul ha.1 hb.1]; exact hadd _ _ ha.2 hb.2⟩
  one_mem' := ⟨one_mem _, by rw [X.th_one]; exact h0⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [X.th_inv ha.1]; exact ha.2⟩

end Sec

end CFSG.QuasithinUnique.A5
