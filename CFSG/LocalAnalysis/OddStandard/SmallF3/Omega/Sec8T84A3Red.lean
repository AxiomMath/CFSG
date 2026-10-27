module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSign

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped Pointwise

namespace RedAct

variable {G : Type} [Group G]

structure Setup (N O V : Subgroup G) : Prop where
  O_le : O ≤ N
  V_le : V ≤ N
  O_norm : ∀ n ∈ N, ∀ o ∈ O, n * o * n⁻¹ ∈ O
  inf : ∀ v ∈ V, v ∈ O → v = 1
  inv : ∀ n ∈ N, ∀ v ∈ V, n * v * n⁻¹ ∈ V ⊔ O

variable {N O V : Subgroup G}

theorem inf_of_card_two_pow {k : ℕ} (hV : Nat.card V = 2 ^ k) (hO : Odd (Nat.card O)) :
    ∀ v ∈ V, v ∈ O → v = 1 := by
  intro v hvV hvO
  have h1 : orderOf v ∣ 2 ^ k := by
    rw [← hV, ← Subgroup.orderOf_mk v hvV]
    exact orderOf_dvd_natCard _
  have h2 : orderOf v ∣ Nat.card O := by
    rw [← Subgroup.orderOf_mk v hvO]
    exact orderOf_dvd_natCard _
  have h3 : orderOf v ∣ Nat.gcd (2 ^ k) (Nat.card O) := Nat.dvd_gcd h1 h2
  have hcop : Nat.Coprime (2 ^ k) (Nat.card O) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hO)
  rw [hcop.gcd_eq_one] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem V_le_normalizer (S : Setup N O V) : V ≤ normalizer (O : Set G) := by
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro o
  refine ⟨fun ho => S.O_norm v (S.V_le hv) o ho, fun ho => ?_⟩
  have h := S.O_norm v⁻¹ (N.inv_mem (S.V_le hv)) _ ho
  simpa [mul_assoc] using h

theorem mem_sup_iff (S : Setup N O V) {x : G} :
    x ∈ V ⊔ O ↔ ∃ v ∈ V, ∃ o ∈ O, x = v * o := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right V O (V_le_normalizer S)
  have hx : x ∈ V ⊔ O ↔ x ∈ ((V : Set G) * (O : Set G)) := by
    rw [← h]; rfl
  rw [hx, Set.mem_mul]
  constructor
  · rintro ⟨v, hv, o, ho, rfl⟩
    exact ⟨v, hv, o, ho, rfl⟩
  · rintro ⟨v, hv, o, ho, rfl⟩
    exact ⟨v, hv, o, ho, rfl⟩

theorem decomp_unique (S : Setup N O V) {v v' o o' : G} (hv : v ∈ V) (hv' : v' ∈ V)
    (ho : o ∈ O) (ho' : o' ∈ O) (h : v * o = v' * o') : v = v' := by
  have h1 : v'⁻¹ * v ∈ V := V.mul_mem (V.inv_mem hv') hv
  have h2 : v'⁻¹ * v = o' * o⁻¹ := by
    have : v = v' * (o' * o⁻¹) := by
      calc v = v * o * o⁻¹ := by group
        _ = v' * o' * o⁻¹ := by rw [h]
        _ = v' * (o' * o⁻¹) := by group
    rw [this]; group
  have h3 : v'⁻¹ * v ∈ O := by rw [h2]; exact O.mul_mem ho' (O.inv_mem ho)
  have h4 : v'⁻¹ * v = 1 := S.inf _ h1 h3
  exact (inv_mul_eq_one.mp h4).symm

open Classical in
@[expose] noncomputable def act (N O V : Subgroup G) (n v : G) : G :=
  if h : ∃ v' ∈ V, ∃ o ∈ O, n * v * n⁻¹ = v' * o then h.choose else 1

theorem act_spec (S : Setup N O V) {n v : G} (hn : n ∈ N) (hv : v ∈ V) :
    act N O V n v ∈ V ∧ ∃ o ∈ O, n * v * n⁻¹ = act N O V n v * o := by
  have hex : ∃ v' ∈ V, ∃ o ∈ O, n * v * n⁻¹ = v' * o :=
    (mem_sup_iff S).mp (S.inv n hn v hv)
  unfold act
  rw [dif_pos hex]
  exact ⟨hex.choose_spec.1, hex.choose_spec.2⟩

theorem act_mem (S : Setup N O V) {n v : G} (hn : n ∈ N) (hv : v ∈ V) : act N O V n v ∈ V :=
  (act_spec S hn hv).1

theorem act_eq (S : Setup N O V) {n v v' o : G} (hn : n ∈ N) (hv : v ∈ V) (hv' : v' ∈ V)
    (ho : o ∈ O) (h : n * v * n⁻¹ = v' * o) : act N O V n v = v' := by
  obtain ⟨h1, o₁, ho₁, h2⟩ := act_spec S hn hv
  exact decomp_unique S h1 hv' ho₁ ho (h2.symm.trans h)

theorem act_one (S : Setup N O V) {v : G} (hv : v ∈ V) : act N O V 1 v = v :=
  act_eq S N.one_mem hv hv O.one_mem (by simp)

theorem act_mul_right (S : Setup N O V) {n v w : G} (hn : n ∈ N) (hv : v ∈ V) (hw : w ∈ V) :
    act N O V n (v * w) = act N O V n v * act N O V n w := by
  obtain ⟨hv1, o₁, ho₁, h1⟩ := act_spec S hn hv
  obtain ⟨hw1, o₂, ho₂, h2⟩ := act_spec S hn hw
  refine act_eq S hn (V.mul_mem hv hw) (V.mul_mem hv1 hw1)
    (O.mul_mem (S.O_norm _ (S.V_le (V.inv_mem hw1)) _ ho₁) ho₂) ?_
  have e1 : n * (v * w) * n⁻¹ = (n * v * n⁻¹) * (n * w * n⁻¹) := by group
  rw [e1, h1, h2]
  group

theorem act_mul_left (S : Setup N O V) {n m v : G} (hn : n ∈ N) (hm : m ∈ N) (hv : v ∈ V) :
    act N O V (n * m) v = act N O V n (act N O V m v) := by
  obtain ⟨hv1, o₁, ho₁, h1⟩ := act_spec S hm hv
  obtain ⟨hv2, o₂, ho₂, h2⟩ := act_spec S hn hv1
  refine act_eq S (N.mul_mem hn hm) hv hv2
    (O.mul_mem ho₂ (S.O_norm n hn _ ho₁)) ?_
  have e1 : n * m * v * (n * m)⁻¹ = n * (m * v * m⁻¹) * n⁻¹ := by group
  rw [e1, h1]
  have e2 : n * (act N O V m v * o₁) * n⁻¹ =
      (n * act N O V m v * n⁻¹) * (n * o₁ * n⁻¹) := by group
  rw [e2, h2]
  group

theorem act_of_mem_O (S : Setup N O V) {n v : G} (hn : n ∈ O) (hv : v ∈ V) :
    act N O V n v = v := by
  have h1 : v⁻¹ * n * v⁻¹⁻¹ ∈ O := S.O_norm v⁻¹ (N.inv_mem (S.V_le hv)) n hn
  refine act_eq S (S.O_le hn) hv hv (o := v⁻¹ * n * v * n⁻¹) ?_ ?_
  · rw [inv_inv] at h1
    exact O.mul_mem h1 (O.inv_mem hn)
  · group

theorem act_of_mem_normalizer (S : Setup N O V) {n v : G} (hn : n ∈ N)
    (hnV : n ∈ normalizer (V : Set G)) (hv : v ∈ V) : act N O V n v = n * v * n⁻¹ := by
  have hmem : n * v * n⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hnV v).mp hv
  exact act_eq S hn hv hmem O.one_mem (by simp)

@[expose] noncomputable def actAut (S : Setup N O V) (n : N) : MulAut ↥V where
  toFun v := ⟨act N O V n v, act_mem S n.2 v.2⟩
  invFun v := ⟨act N O V (n : G)⁻¹ v, act_mem S (N.inv_mem n.2) v.2⟩
  left_inv v := by
    apply Subtype.ext
    simp only
    rw [← act_mul_left S (N.inv_mem n.2) n.2 v.2]
    simpa using act_one S v.2
  right_inv v := by
    apply Subtype.ext
    simp only
    rw [← act_mul_left S n.2 (N.inv_mem n.2) v.2]
    simpa using act_one S v.2
  map_mul' v w := by
    apply Subtype.ext
    exact act_mul_right S n.2 v.2 w.2

@[expose] noncomputable def redHom (S : Setup N O V) : ↥N →* MulAut ↥V where
  toFun := actAut S
  map_one' := by
    ext v
    exact act_one S v.2
  map_mul' n m := by
    ext v
    exact act_mul_left S n.2 m.2 v.2

theorem redHom_spec (S : Setup N O V) (n : N) (v : V) :
    ∃ o ∈ O, (n : G) * v * (n : G)⁻¹ = ((redHom S n v : ↥V) : G) * o :=
  (act_spec S n.2 v.2).2

theorem redHom_eq_of (S : Setup N O V) (n : N) (v v' : V) {o : G} (ho : o ∈ O)
    (h : (n : G) * v * (n : G)⁻¹ = v' * o) : redHom S n v = v' :=
  Subtype.ext (act_eq S n.2 v.2 v'.2 ho h)

theorem redHom_of_mem_O (S : Setup N O V) (n : N) (hn : (n : G) ∈ O) : redHom S n = 1 := by
  ext v
  exact act_of_mem_O S hn v.2

theorem redHom_of_mem_normalizer (S : Setup N O V) (n : N)
    (hn : (n : G) ∈ normalizer (V : Set G)) (v : V) :
    ((redHom S n v : ↥V) : G) = (n : G) * v * (n : G)⁻¹ :=
  act_of_mem_normalizer S n.2 hn v.2

theorem redHom_of_mem_V (S : Setup N O V) (n : N) (hn : (n : G) ∈ V) (v : V) :
    ((redHom S n v : ↥V) : G) = (n : G) * v * (n : G)⁻¹ :=
  redHom_of_mem_normalizer S n (Subgroup.le_normalizer hn) v

end RedAct

end CFSG.OddStandard.SmallF3.Omega
