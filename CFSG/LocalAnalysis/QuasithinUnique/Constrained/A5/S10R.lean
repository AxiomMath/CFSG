module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S10Th

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

@[expose] def IsRefl (i : G) (w : V4) : Prop :=
  i ∈ M ∧ i * i = 1 ∧
    ∀ x : V4, ((X.rg i : GL (Fin 4) (ZMod 2)) : Mat4).mulVec x = x + Bf x w • w

@[expose] noncomputable def QPl
    (w : V4) (hw : quadHyp w = 1) : Subgroup G :=
  X.Qsub (inPl w) (Or.inl rfl) (fun x y => pl_add w x y hw)

@[expose] noncomputable def QPl'
    (w : V4) (hw : quadHyp w = 1) : Subgroup G :=
  X.Qsub (inPl' w) (Or.inl rfl) (fun x y => pl'_add w x y hw)

variable {X} {i : G} {w : V4}

theorem IsRefl.inv_eq
    (h : X.IsRefl i w) : i⁻¹ = i := inv_eq_of_mul_eq_one_right h.2.1

theorem IsRefl.th_conj
    (h : X.IsRefl i w) {p : G} (hp : p ∈ borelP M L) :
    i * p * i⁻¹ ∈ borelP M L ∧ X.th (i * p * i⁻¹) = X.th p + Bf (X.th p) w • w := by
  obtain ⟨h1, h2⟩ := X.th_conj h.1 hp
  refine ⟨h1, ?_⟩
  rw [h2, h.2.2]

theorem IsRefl.conj_fix
    (h : X.IsRefl i w) {p : G} (hp : p ∈ borelP M L)
    (hB : Bf (X.th p) w = 0) : i * p * i⁻¹ = p ∨ i * p * i⁻¹ = p * C.zU := by
  obtain ⟨h1, h2⟩ := h.th_conj hp
  rw [hB, zero_smul, add_zero] at h2
  exact X.th_fiber h1 hp h2

theorem zU_conj_M {m : G} (hm : m ∈ M) : m * C.zU * m⁻¹ = C.zU := by
  have h := X.zU_comm_M hm
  calc m * C.zU * m⁻¹ = (C.zU * m) * m⁻¹ := by rw [h]
    _ = C.zU := by group

theorem IsRefl.exists_cent (h : X.IsRefl i w) (hw : quadHyp w = 1)
    (hno : ∀ p ∈ borelP M L, p ∉ centerOf (borelP M L) → p ^ 2 = 1 → i * p * i⁻¹ ≠ p)
    {a : V4} (ha : inPl w a) : ∃ p ∈ borelP M L, X.th p = a ∧ i * p * i⁻¹ = p := by
  by_cases ha0 : a = 0
  · exact ⟨1, one_mem _, by rw [X.th_one, ha0], by simp⟩
  · obtain ⟨x, hxy, hx0, hy0, hqx, hqy, hBx, hBy⟩ := pl_split w a hw ha ha0
    have key : ∀ z' : V4, z' ≠ 0 → quadHyp z' = 0 → Bf z' w = 0 →
        ∃ p ∈ borelP M L, X.th p = z' ∧ i * p * i⁻¹ = p * C.zU := by
      intro z' hz0 hq hB
      obtain ⟨p, hp, hpz⟩ := X.th_exists z'
      refine ⟨p, hp, hpz, ?_⟩
      rcases h.conj_fix hp (by rw [hpz]; exact hB) with h1 | h1
      · exfalso
        refine hno p hp ?_ ?_ h1
        · intro hpZ
          apply hz0
          rw [← hpz]
          exact (X.th_eq_zero_iff hp).mpr ((X.centerOf_P_iff p).mp hpZ)
        · rcases X.sq_th hp with ⟨h2, -⟩ | ⟨-, h2⟩
          · rw [pow_two]
            exact h2
          · rw [hpz, hq] at h2
            exact absurd h2 (by decide)
      · exact h1
    obtain ⟨px, hpx, hthx, hix⟩ := key x hx0 hqx hBx
    obtain ⟨py, hpy, hthy, hiy⟩ := key (x + a) hy0 hqy hBy
    refine ⟨px * py, mul_mem hpx hpy, ?_, ?_⟩
    · rw [X.th_mul hpx hpy, hthx, hthy, ← add_assoc, V4_add_self, zero_add]
    · have hpyM : py ∈ M := C.P_le_M hpy
      calc i * (px * py) * i⁻¹ = (i * px * i⁻¹) * (i * py * i⁻¹) := by group
        _ = (px * C.zU) * (py * C.zU) := by rw [hix, hiy]
        _ = px * (C.zU * py) * C.zU := by group
        _ = px * (py * C.zU) * C.zU := by rw [X.zU_comm_M hpyM]
        _ = px * py * (C.zU * C.zU) := by group
        _ = px * py := by rw [C.zU_mul_self, mul_one]

theorem IsRefl.cent_QPl (h : X.IsRefl i w) (hw : quadHyp w = 1)
    (hno : ∀ p ∈ borelP M L, p ∉ centerOf (borelP M L) → p ^ 2 = 1 → i * p * i⁻¹ ≠ p)
    {q : G} (hq : q ∈ X.QPl w hw) : i * q * i⁻¹ = q := by
  have hq' : q ∈ borelP M L ∧ inPl w (X.th q) := hq
  obtain ⟨hqP, hqpl⟩ := hq'
  have hzi : i * C.zU * i⁻¹ = C.zU := X.zU_conj_M h.1
  by_cases hq0 : X.th q = 0
  · rcases (X.th_eq_zero_iff hqP).mp hq0 with rfl | rfl
    · simp
    · exact hzi
  · obtain ⟨p, hp, hpth, hpi⟩ := h.exists_cent hw hno hqpl
    rcases X.th_fiber hqP hp (by rw [hpth]) with h1 | h1
    · rw [h1]
      exact hpi
    · rw [h1]
      calc i * (p * C.zU) * i⁻¹ = (i * p * i⁻¹) * (i * C.zU * i⁻¹) := by group
        _ = p * C.zU := by rw [hpi, hzi]

theorem centralizes_QPl'
    {e : G} (heM : e ∈ M) (he3 : e ^ 3 = 1) {c : GL (Fin 4) (ZMod 2)}
    (hec : X.rg e = c) (hcfix : ∀ x, inPl' w x → (c : Mat4).mulVec x = x) {q : G}
    (hq : q ∈ borelP M L) (hqpl : inPl' w (X.th q)) : e * q * e⁻¹ = q := by
  obtain ⟨h1, h2⟩ := X.th_conj heM hq
  rw [hec, hcfix _ hqpl] at h2
  rcases X.th_fiber h1 hq h2 with h | h
  · exact h
  · exfalso
    have hzE : e * C.zU * e⁻¹ = C.zU := X.zU_conj_M heM
    have h2' : e * (q * C.zU) * e⁻¹ = q := by
      calc e * (q * C.zU) * e⁻¹ = (e * q * e⁻¹) * (e * C.zU * e⁻¹) := by group
        _ = (q * C.zU) * C.zU := by rw [h, hzE]
        _ = q := by rw [mul_assoc, C.zU_mul_self, mul_one]
    have h3 : e * (e * q * e⁻¹) * e⁻¹ = q := by rw [h]; exact h2'
    have h4 : e * (e * (e * q * e⁻¹) * e⁻¹) * e⁻¹ = q * C.zU := by rw [h3]; exact h
    have h5 : e * (e * (e * q * e⁻¹) * e⁻¹) * e⁻¹ = q := by
      have : e * (e * (e * q * e⁻¹) * e⁻¹) * e⁻¹ = (e * e * e) * q * (e * e * e)⁻¹ := by group
      rw [this, ← pow_three', he3]
      group
    have h6 : q * C.zU = q := h4.symm.trans h5
    exact C.zU_ne_one (by simpa using h6)

end Sec

end CFSG.QuasithinUnique.A5
