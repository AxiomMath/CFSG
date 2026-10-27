module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Dihedral

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

abbrev SectRank4 (X : Type) [Group X] : Prop :=
  ∀ P : Subgroup X, IsPGroup 2 P → ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = P

theorem rho0_mem_R0 : rho0 ∈ R0 := by
  rw [show rho0 = (a0 * b0) * (c0 * b0) by decide]
  exact mul_mem a0_b0_mem_R0 c0_b0_mem_R0

section Generic

variable {X : Type} [Group X]

@[expose] def ConjTo (a b : X) : Prop := ∃ g : X, g * a * g⁻¹ = b

@[expose] def SubConj (P Q : Subgroup X) : Prop :=
  ∃ g : X, P.map (MulAut.conj g).toMonoidHom = Q

@[expose] def CenterEq (Q Z : Subgroup X) : Prop :=
  ∀ a ∈ Q, (∀ b ∈ Q, a * b = b * a) ↔ a ∈ Z

end Generic

inductive ActType
  | one
  | two

inductive Q0Type
  | elem
  | homocyclic
  | e4q8
  | exceptional
  | extraspecial

namespace A7Data

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} (A : A7Data t L)

@[expose] noncomputable def xR : X := Classical.choose (A.exists_mem_R_ψ_eq rho0_mem_R0)

@[expose] noncomputable def yR : X := Classical.choose (A.exists_mem_R_ψ_eq c0_b0_mem_R0)

@[expose] noncomputable def ER (k yi : X) : Subgroup X := closure {A.xR ^ 2, yi, t, k}

end A7Data

structure A7Sigma {X : Type} [Group X] [Finite X] (t : X) (L : Subgroup X) (data : A7Data t L)
    where
  iso : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)
  Ψ : normalizer (L : Set X) →* Perm (Fin 7)
  Ψ_eq_one_iff : ∀ g, Ψ g = 1 ↔ (g : X) ∈ coreActionKernel L
  Ψ_of_mem : ∀ l : L, Ψ ⟨l, le_normalizer l.2⟩ = (iso (QuotientGroup.mk l) : Perm (Fin 7))
  Ψ_T : ∀ g : data.T, data.ψ g = Ψ ⟨g, data.T_le_normalizer g.2⟩

structure A7Facts {X : Type} [Group X] [Finite X] (t : X) (L : Subgroup X) (data : A7Data t L)
    (k : X) : Prop where
  d_xy : ∃ d ∈ centralizer ({t} : Set X),
    d ∈ normalizer (data.ER k (data.xR * data.yR) : Set X) ∧
      d * data.xR ^ 2 * d⁻¹ = data.xR * data.yR ∧
      d * (data.xR * data.yR) * d⁻¹ = data.xR ^ 2 * (data.xR * data.yR) ∧ d * k * d⁻¹ = k
  d_y : ∃ d ∈ centralizer ({t} : Set X),
    d ∈ normalizer (data.ER k data.yR : Set X) ∧ d * data.xR ^ 2 * d⁻¹ = data.xR ^ 2 * data.yR ∧
      d * data.yR * d⁻¹ = data.xR ^ 2 ∧ d * (data.xR ^ 2 * k) * d⁻¹ = data.xR ^ 2 * k
  k_fixed : ∀ {n : X},
    n ∈ normalizer (data.ER k (data.xR * data.yR) : Set X) ⊓ centralizer ({t} : Set X) →
      n * k * n⁻¹ = k
  zk_fixed : ∀ {n : X},
    n ∈ normalizer (data.ER k data.yR : Set X) ⊓ centralizer ({t} : Set X) →
      n * (data.xR ^ 2 * k) * n⁻¹ = data.xR ^ 2 * k
  not_conj : ∀ {g : X}, g ∈ centralizer ({t} : Set X) →
    (∀ e ∈ data.ER k data.yR, g * e * g⁻¹ ∈ data.ER k (data.xR * data.yR)) → False
  card_conj_z : (∀ g ∈ centralizer ({t} : Set X), g * data.xR ^ 2 * g⁻¹ ≠ t * data.xR ^ 2) →
    {b | ∃ g ∈ centralizer ({t} : Set X), g * data.xR ^ 2 * g⁻¹ = b}.ncard ≡ 1 [MOD 4]

structure A7Base (X : Type) [Group X] [Finite X] where
  t : X
  L : Subgroup X
  data : A7Data t L
  card_K : Nat.card data.K = 2
  k : X
  k_mem : k ∈ data.T
  k_sq : k ^ 2 = 1
  ψ_k : data.ψ ⟨k, k_mem⟩ = c0
  facts : A7Facts t L data k ∨ Nonempty (A7Sigma t L data)

namespace A7Facts

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {data : A7Data t L} {k : X}

omit [Finite X] in
theorem closure_tk (a b : X) : closure {a, b, t, t * k} = closure ({a, b, t, k} : Set X) := by
  apply le_antisymm
  · rw [closure_le]
    rintro g (rfl | rfl | rfl | rfl)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  · rw [closure_le]
    rintro g (rfl | rfl | rfl | rfl)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · have h1 : t⁻¹ * (t * g) = g := by group
      rw [← h1]
      exact mul_mem (inv_mem (subset_closure (by simp))) (subset_closure (by simp))

omit [Finite X] in
theorem ER_tk (yi : X) : data.ER (t * k) yi = data.ER k yi := closure_tk _ _

theorem tk (h : A7Facts t L data k) : A7Facts t L data (t * k) := by
  have hxT : data.xR ∈ data.T := (Classical.choose_spec (data.exists_mem_R_ψ_eq rho0_mem_R0)).1.1
  have hzt : data.xR ^ 2 * t = t * data.xR ^ 2 := data.commute_t (pow_mem hxT 2)
  have hconj : ∀ {d : X}, d ∈ centralizer ({t} : Set X) → d * t * d⁻¹ = t := by
    intro d hd
    rw [mem_centralizer_singleton_iff.mp hd, mul_inv_cancel_right]
  have htk : ∀ {d : X}, d ∈ centralizer ({t} : Set X) → d * k * d⁻¹ = k →
      d * (t * k) * d⁻¹ = t * k := by
    intro d hd hdk
    calc d * (t * k) * d⁻¹ = d * t * d⁻¹ * (d * k * d⁻¹) := by group
      _ = t * k := by rw [hconj hd, hdk]
  have hztk : ∀ {d : X}, d ∈ centralizer ({t} : Set X) →
      d * (data.xR ^ 2 * k) * d⁻¹ = data.xR ^ 2 * k →
      d * (data.xR ^ 2 * (t * k)) * d⁻¹ = data.xR ^ 2 * (t * k) := by
    intro d hd hdk
    have e : data.xR ^ 2 * (t * k) = t * (data.xR ^ 2 * k) := by
      rw [← mul_assoc, hzt, mul_assoc]
    rw [e]
    calc d * (t * (data.xR ^ 2 * k)) * d⁻¹ = d * t * d⁻¹ * (d * (data.xR ^ 2 * k) * d⁻¹) := by
          group
      _ = t * (data.xR ^ 2 * k) := by rw [hconj hd, hdk]
  refine ⟨?_, ?_, ?_, ?_, ?_, h.card_conj_z⟩
  · obtain ⟨d, hd, hdN, h1, h2, h3⟩ := h.d_xy
    exact ⟨d, hd, by rw [ER_tk]; exact hdN, h1, h2, htk hd h3⟩
  · obtain ⟨d, hd, hdN, h1, h2, h3⟩ := h.d_y
    exact ⟨d, hd, by rw [ER_tk]; exact hdN, h1, h2, hztk hd h3⟩
  · intro n hn
    rw [ER_tk] at hn
    exact htk hn.2 (h.k_fixed hn)
  · intro n hn
    rw [ER_tk] at hn
    exact hztk hn.2 (h.zk_fixed hn)
  · intro g hg hE
    rw [ER_tk, ER_tk] at hE
    exact h.not_conj hg hE

end A7Facts

namespace A7Base

variable {X : Type} [Group X] [Finite X] (S : A7Base X)

@[expose] noncomputable def x : X := Classical.choose (S.data.exists_mem_R_ψ_eq rho0_mem_R0)

theorem x_mem : S.x ∈ S.data.R :=
  (Classical.choose_spec (S.data.exists_mem_R_ψ_eq rho0_mem_R0)).1

theorem ψ_x : S.data.ψ ⟨S.x, S.x_mem.1⟩ = rho0 :=
  (Classical.choose_spec (S.data.exists_mem_R_ψ_eq rho0_mem_R0)).2

@[expose] noncomputable def y : X := Classical.choose (S.data.exists_mem_R_ψ_eq c0_b0_mem_R0)

theorem y_mem : S.y ∈ S.data.R :=
  (Classical.choose_spec (S.data.exists_mem_R_ψ_eq c0_b0_mem_R0)).1

theorem ψ_y : S.data.ψ ⟨S.y, S.y_mem.1⟩ = c0 * b0 :=
  (Classical.choose_spec (S.data.exists_mem_R_ψ_eq c0_b0_mem_R0)).2

@[expose] noncomputable def z : X := S.x ^ 2

@[expose] noncomputable def B : Subgroup X := closure {S.z, S.t, S.k}

@[expose] noncomputable def E (yi : X) : Subgroup X := closure {S.z, yi, S.t, S.k}

@[expose] noncomputable def E0 (yi ki : X) : Subgroup X := closure {S.z, yi, ki}

@[expose] def withK (c : X) (hc : c = S.k ∨ c = S.t * S.k) : A7Base X where
  t := S.t
  L := S.L
  data := S.data
  card_K := S.card_K
  k := c
  k_mem := by
    rcases hc with rfl | rfl
    · exact S.k_mem
    · exact mul_mem S.data.t_mem_T S.k_mem
  k_sq := by
    rcases hc with rfl | rfl
    · exact S.k_sq
    · have ht : S.t ^ 2 = 1 := by rw [← S.data.orderOf_t, pow_orderOf_eq_one]
      rw [(Commute.mul_pow (S.data.commute_t S.k_mem).symm 2), ht, S.k_sq, one_mul]
  ψ_k := by
    rcases hc with rfl | rfl
    · exact S.ψ_k
    · have ht : S.data.ψ ⟨S.t, S.data.t_mem_T⟩ = 1 :=
        (S.data.mem_K_iff S.data.t_mem_T).mp S.data.t_mem_K
      have : (⟨S.t * S.k, mul_mem S.data.t_mem_T S.k_mem⟩ : S.data.T) =
          ⟨S.t, S.data.t_mem_T⟩ * ⟨S.k, S.k_mem⟩ := rfl
      rw [this, map_mul, ht, S.ψ_k, one_mul]
  facts := by
    rcases hc with rfl | rfl
    · exact S.facts
    · rcases S.facts with h | h
      · exact Or.inl h.tk
      · exact Or.inr h

section withK

variable {c : X} (hc : c = S.k ∨ c = S.t * S.k)

theorem withK_t : (S.withK c hc).t = S.t := rfl

theorem withK_data : (S.withK c hc).data = S.data := rfl

theorem withK_k : (S.withK c hc).k = c := rfl

theorem withK_x : (S.withK c hc).x = S.x := rfl

theorem withK_y : (S.withK c hc).y = S.y := rfl

theorem withK_z : (S.withK c hc).z = S.z := rfl

end withK

structure Frame where
  xF : X
  yF : X
  kF : X
  xF_mem : xF ∈ S.data.R
  yF_mem : yF ∈ S.data.R
  xF_sq : xF ^ 2 = S.z
  yF_sq : yF ^ 2 = 1
  yF_inv : yF * xF * yF⁻¹ = xF⁻¹
  kF_mem : kF ∈ S.data.T
  kF_sq : kF ^ 2 = 1
  kF_comm : ∀ r ∈ S.data.R, kF * r = r * kF
  kF_not_mem : kF ∉ S.data.R ⊔ S.data.K
  kF_fixed : ∀ n ∈ normalizer (S.E yF : Set X) ⊓ centralizer ({S.t} : Set X),
    n * kF * n⁻¹ = kF

namespace Frame

variable {S} (F : S.Frame)

@[expose] noncomputable def E₁ : Subgroup X := S.E F.yF

@[expose] noncomputable def E₂ : Subgroup X := S.E (F.xF * F.yF)

@[expose] def Normal : Prop := F.xF = S.x⁻¹ ∧ F.yF = S.x * S.y ∧ F.kF = S.k

end Frame

structure Sec4 (F : S.Frame) (T₁ : Subgroup X) : Prop where
  isPGroup : IsPGroup 2 T₁
  le : S.data.T ≤ T₁
  le_normalizer : T₁ ≤ normalizer (S.data.T : Set X)
  maximal : ∀ Q : Subgroup X, IsPGroup 2 Q → T₁ ≤ Q → Q ≤ normalizer (S.data.T : Set X) →
    Q = T₁
  card : Nat.card T₁ = 4 * Nat.card S.data.T
  fusion : ∀ b ∈ S.B, ConjTo S.t b ↔
    b = S.t ∨ b = S.t * S.z ∨ b = S.t * F.kF ∨ b = S.t * S.z * F.kF

@[expose] def ActHolds (yi ki : X) (v w₁ w₂ : X) : ActType → Prop
  | .one => (∀ e ∈ S.E0 yi ki, v * e * v⁻¹ = e ∧ w₁ * e * w₁⁻¹ = e ∧ w₂ * e * w₂⁻¹ = e) ∧
      v * S.t * v⁻¹ = S.t * ki ∧ w₁ * S.t * w₁⁻¹ = S.t * S.z ∧
      w₂ * S.t * w₂⁻¹ = S.t * yi
  | .two => (∀ e ∈ S.E0 yi ki, v * e * v⁻¹ = e) ∧ v * S.t * v⁻¹ = S.t * ki ∧
      w₁ * S.t * w₁⁻¹ = S.t * S.z * ki ∧ w₂ * S.t * w₂⁻¹ = S.t * yi * ki ∧
      w₁ * S.z * w₁⁻¹ = S.z ∧ w₂ * yi * w₂⁻¹ = yi ∧ w₂ * S.z * w₂⁻¹ = S.z * ki ∧
      w₁ * yi * w₁⁻¹ = yi * ki ∧ w₁ * ki * w₁⁻¹ = ki ∧ w₂ * ki * w₂⁻¹ = ki

@[expose] noncomputable def Q0 (yi ki w₁ w₂ : X) : Subgroup X :=
  S.E0 yi ki ⊔ zpowers w₁ ⊔ zpowers w₂

@[expose] def Q0Holds (yi ki v w₁ w₂ : X) : Q0Type → Prop
  | .elem => (∀ a ∈ S.Q0 yi ki w₁ w₂, ∀ b ∈ S.Q0 yi ki w₁ w₂, a * b = b * a) ∧
      (∀ a ∈ S.Q0 yi ki w₁ w₂, a ^ 2 = 1) ∧ Nat.card (S.Q0 yi ki w₁ w₂) = 32
  | .homocyclic => w₁ ^ 2 = S.z ∧ w₂ ^ 2 = yi ∧
      (∀ a ∈ S.Q0 yi ki w₁ w₂, ∀ b ∈ S.Q0 yi ki w₁ w₂, a * b = b * a) ∧
      Nat.card (S.Q0 yi ki w₁ w₂) = 32
  | .e4q8 => w₁ ^ 2 = ki ∧ w₂ ^ 2 = ki ∧ CenterEq (S.Q0 yi ki w₁ w₂) (S.E0 yi ki) ∧
      Nat.card (S.Q0 yi ki w₁ w₂) = 32
  | .exceptional => w₁ ^ 2 = S.z * ki ∧ w₂ ^ 2 = yi * ki ∧ w₁ * w₂ * w₁⁻¹ * w₂⁻¹ = ki ∧
      CenterEq (S.Q0 yi ki w₁ w₂) (S.E0 yi ki) ∧ Nat.card (S.Q0 yi ki w₁ w₂) = 32
  | .extraspecial => w₁ ^ 2 = 1 ∧ w₂ ^ 2 = 1 ∧ S.ActHolds yi ki v w₁ w₂ .two ∧
      CenterEq (S.Q0 yi ki w₁ w₂) (closure {ki}) ∧ Nat.card (S.Q0 yi ki w₁ w₂) = 32

@[expose] noncomputable def oddTwoCoreIn (N : Subgroup X) : Subgroup X :=
  ((CFSG.pCore 2 (N ⧸ CFSG.oddCore N)).comap (QuotientGroup.mk' (CFSG.oddCore N))).map
    N.subtype

@[expose] noncomputable def oddCoreIn (N : Subgroup X) : Subgroup X :=
  (CFSG.oddCore N).map N.subtype

structure Sec6 (T₁ : Subgroup X) (yi ki ui : X) where
  S₁ : Subgroup X
  Q₁ : Subgroup X
  D₁₁ : Subgroup X
  C₁ : Subgroup X
  v : X
  w₁ : X
  w₂ : X
  u : X
  d : X
  act : ActType
  q0 : Q0Type
  automizer : Nonempty (normalizer (S.E yi : Set X) ⧸
    (centralizer (S.E yi : Set X)).subgroupOf (normalizer (S.E yi : Set X)) ≃*
      Equiv.Perm (Fin 4) × Multiplicative (ZMod 2))
  controls : ∀ e ∈ S.E yi, ConjTo S.t e →
    ∃ n ∈ normalizer (S.E yi : Set X), n * S.t * n⁻¹ = e
  card_conj : Nat.card {e : S.E yi // ConjTo S.t e} = 8
  isPGroup_S₁ : IsPGroup 2 S₁
  S₁_le : S₁ ≤ normalizer (S.E yi : Set X)
  S₁_maximal : ∀ Q : Subgroup X, IsPGroup 2 Q → S₁ ≤ Q → Q ≤ normalizer (S.E yi : Set X) →
    Q = S₁
  S₁_eq : S₁ = S.E yi ⊔ zpowers v ⊔ zpowers w₁ ⊔ zpowers w₂ ⊔ zpowers u
  v_central : ∀ n ∈ normalizer (S.E yi : Set X), n * v * n⁻¹ * v⁻¹ ∈
    centralizer (S.E yi : Set X)
  d_mem : d ∈ normalizer (S.E yi : Set X) ⊓ centralizer ({S.t} : Set X)
  d_cube : d ^ 3 ∈ centralizer (S.E yi : Set X)
  d_not_mem : d ∉ centralizer (S.E yi : Set X)
  u_inv_d : u * d * u⁻¹ * d ∈ centralizer (S.E yi : Set X)
  u_comm_w₁ : u * w₁ * u⁻¹ * w₁⁻¹ ∈ centralizer (S.E yi : Set X)
  normalizer_inf_centralizer : normalizer (S.E yi : Set X) ⊓ centralizer ({S.t} : Set X) =
    centralizer (S.E yi : Set X) ⊔ zpowers d ⊔ zpowers u
  act_holds : S.ActHolds yi ki v w₁ w₂ act
  k_fixed : ∀ n ∈ normalizer (S.E yi : Set X), n * ki * n⁻¹ = ki
  T₁_eq : T₁ = S.data.T ⊔ zpowers v ⊔ zpowers w₁
  T₁_le : T₁ ≤ S₁
  Q₁_eq : Q₁ = S₁ ⊓ oddTwoCoreIn (normalizer (S.E yi : Set X))
  Q0_le : S.Q0 yi ki w₁ w₂ ≤ Q₁
  Q0_invariant : ∀ n ∈ normalizer (S.E yi : Set X) ⊓ normalizer (Q₁ : Set X),
    (S.Q0 yi ki w₁ w₂).map (MulAut.conj n).toMonoidHom = S.Q0 yi ki w₁ w₂
  q0_holds : S.Q0Holds yi ki v w₁ w₂ q0
  isPGroup_D₁₁ : IsPGroup 3 D₁₁
  D₁₁_le : D₁₁ ≤ normalizer (S.E yi : Set X) ⊓ normalizer (Q₁ : Set X) ⊓
    centralizer ({S.t} : Set X)
  C_eq : Q₁ ⊓ centralizer (D₁₁ : Set X) = closure {S.t, ki, v}
  w₁_comm_C : ∀ c ∈ Q₁ ⊓ centralizer (D₁₁ : Set X), w₁ * c * w₁⁻¹ * c⁻¹ ∈
    (match act with
      | .one => closure {S.z}
      | .two => closure {S.z * ki})
  w₁_comm_t : w₁ * S.t * w₁⁻¹ * S.t⁻¹ ≠ 1
  C₁_le : C₁ ≤ Q₁ ⊓ centralizer (D₁₁ : Set X)
  C₁_sup : C₁ ⊔ zpowers S.t = Q₁ ⊓ centralizer (D₁₁ : Set X)
  card_C₁ : Nat.card C₁ = 4
  card_C : Nat.card (Q₁ ⊓ centralizer (D₁₁ : Set X) : Subgroup X) = 8
  C₁_comm : ∀ c ∈ C₁, ∀ q ∈ S.Q0 yi ki w₁ w₂, c * q = q * c
  u_eq : u = ui ∨ u = S.t * ui
  u_comm_C : ∀ c ∈ Q₁ ⊓ centralizer (D₁₁ : Set X), u * c = c * u
  u_inv_D₁₁ : ∀ δ ∈ D₁₁, u * δ * u⁻¹ * δ ∈ oddCoreIn (centralizer (S.E yi : Set X))
  S₁_commutator_mem : ∀ a ∈ S₁, ∀ b ∈ S₁, a * b * a⁻¹ * b⁻¹ ∈ S.E0 yi ki ⊔ zpowers w₁
  Q₁_char : (q0 = .homocyclic ∨ q0 = .e4q8 ∨ q0 = .exceptional) →
    ∀ n ∈ normalizer (S₁ : Set X), Q₁.map (MulAut.conj n).toMonoidHom = Q₁
  no_conj_extraspecial : q0 = .extraspecial → ∀ q ∈ S.Q0 yi ki w₁ w₂, ¬ ConjTo S.t q
  no_conj_of : (q0 = .elem ∨ q0 = .homocyclic) → ∀ q ∈ S.Q0 yi ki w₁ w₂ ⊔ C₁, ¬ ConjTo S.t q

end A7Base

@[expose] def FritzA7Sections4to8 : Prop :=
  HaradaInput →
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ∀ _S : A7Base X, SectRank4 X

@[expose] def FritzA7Section4 : Prop :=
  HaradaInput →
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ¬ SectRank4 X → ∀ _S : A7Base X, ∃ (S : A7Base X) (F : S.Frame) (T₁ : Subgroup X),
      S.Sec4 F T₁ ∧ F.Normal ∧
        (¬ SubConj F.E₁ F.E₂ ∨ ∃ g ∈ T₁, F.E₁.map (MulAut.conj g).toMonoidHom = F.E₂)

@[expose] def FritzA7Section5 : Prop :=
  HaradaInput →
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ¬ SectRank4 X → ∀ (S : A7Base X) (F : S.Frame) (T₁ : Subgroup X), S.Sec4 F T₁ →
      F.Normal → (∃ g ∈ T₁, F.E₁.map (MulAut.conj g).toMonoidHom = F.E₂) → False

@[expose] def FritzA7Section6 : Prop :=
  HaradaInput →
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ¬ SectRank4 X → ∀ (S : A7Base X) (F : S.Frame) (T₁ : Subgroup X), S.Sec4 F T₁ →
      F.Normal → ¬ SubConj F.E₁ F.E₂ →
      Nonempty (S.Sec6 T₁ F.yF F.kF (F.xF * F.yF)) ∧
        Nonempty (S.Sec6 T₁ (F.xF * F.yF) (S.z * F.kF) (S.z * F.yF))

@[expose] def FritzA7Section7 : Prop :=
  HaradaInput →
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ¬ SectRank4 X → ∀ (S : A7Base X) (F : S.Frame) (T₁ : Subgroup X), S.Sec4 F T₁ →
      ¬ SubConj F.E₁ F.E₂ →
      ∀ (D₁ : S.Sec6 T₁ F.yF F.kF (F.xF * F.yF))
        (D₂ : S.Sec6 T₁ (F.xF * F.yF) (S.z * F.kF) (S.z * F.yF)),
      (D₁.q0 = .e4q8 ∨ D₁.q0 = .exceptional ∨ D₂.q0 = .e4q8 ∨ D₂.q0 = .exceptional) → False

@[expose] def FritzA7Section8 : Prop :=
  HaradaInput →
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ¬ SectRank4 X → ∀ (S : A7Base X) (F : S.Frame) (T₁ : Subgroup X), S.Sec4 F T₁ →
      ¬ SubConj F.E₁ F.E₂ →
      ∀ (D₁ : S.Sec6 T₁ F.yF F.kF (F.xF * F.yF))
        (D₂ : S.Sec6 T₁ (F.xF * F.yF) (S.z * F.kF) (S.z * F.yF)),
      (D₁.q0 = .elem ∨ D₁.q0 = .homocyclic ∨ D₁.q0 = .extraspecial) →
      (D₂.q0 = .elem ∨ D₂.q0 = .homocyclic ∨ D₂.q0 = .extraspecial) → False

theorem fritzA7Sections4to8_of_parts (h4 : FritzA7Section4) (h5 : FritzA7Section5)
    (h6 : FritzA7Section6) (h7 : FritzA7Section7) (h8 : FritzA7Section8) :
    FritzA7Sections4to8 := by
  intro hH X _ _ _ hnonab S₀
  by_contra hnot
  obtain ⟨S, F, T₁, h4T, hF, hcase⟩ := h4 hH X hnonab hnot S₀
  rcases hcase with hnc | hc
  · obtain ⟨⟨D₁⟩, ⟨D₂⟩⟩ := h6 hH X hnonab hnot S F T₁ h4T hF hnc
    by_cases h78 : D₁.q0 = .e4q8 ∨ D₁.q0 = .exceptional ∨ D₂.q0 = .e4q8 ∨
        D₂.q0 = .exceptional
    · exact h7 hH X hnonab hnot S F T₁ h4T hnc D₁ D₂ h78
    · push Not at h78
      obtain ⟨h1, h2, h3, h4'⟩ := h78
      refine h8 hH X hnonab hnot S F T₁ h4T hnc D₁ D₂ ?_ ?_
      · cases hq : D₁.q0 <;> simp_all
      · cases hq : D₂.q0 <;> simp_all
  · exact h5 hH X hnonab hnot S F T₁ h4T hF hc

end CFSG.ComponentClassification.HSFLit
