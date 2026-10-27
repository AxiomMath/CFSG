module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open Subgroup

structure LowerData (p : ℕ) (S : Type*) [Group S] where
  X : Fin 4 → S
  Sw : Fin 4 → S
  T : S
  comm : ∀ i j, Commute (X i) (X j)
  pow : ∀ i, X i ^ p = 1
  sw_self : ∀ k, Sw k * X k * (Sw k)⁻¹ = (X k)⁻¹
  sw_other : ∀ j k, j ≠ k → Sw k * X j * (Sw k)⁻¹ = (X k)⁻¹ * X j
  T_ne : T ≠ 1
  T_two : ∃ e : ℕ, T ^ (2 ^ e) = 1
  T_comm : ∀ i, Commute T (X i)
  T_sw : ∀ k, Commute T (Sw k)
  card : p ^ 4 ≤ Nat.card (closure (Set.range X))

section Helpers

variable {Lb : Type*} [Group Lb]

theorem pairing_eq_one {Zk : Subgroup Lb} (hc : ∀ z ∈ Zk, ∀ g : Lb, z * g = g * z)
    (hodd : ∀ w ∈ Zk, w ^ 2 = 1 → w = 1) {u v s z : Lb} (hz : z ∈ Zk)
    (hsu : s * u * s⁻¹ = u⁻¹ * z) (hv : u * v * u⁻¹ * v⁻¹ ∈ Zk)
    (hv' : u * (s * v * s⁻¹) * u⁻¹ * (s * v * s⁻¹)⁻¹ ∈ Zk)
    (hcomm : u * (v * (s * v * s⁻¹)⁻¹) = (v * (s * v * s⁻¹)⁻¹) * u) :
    u * v * u⁻¹ * v⁻¹ = 1 := by
  set v' := s * v * s⁻¹ with hv'def
  set c := u * v * u⁻¹ * v⁻¹ with hcdef
  set c' := u * v' * u⁻¹ * v'⁻¹ with hc'def
  have h1 : s * c * s⁻¹ = c := by
    have := hc c hv s
    calc s * c * s⁻¹ = (s * c) * s⁻¹ := rfl
      _ = (c * s) * s⁻¹ := by rw [this]
      _ = c := by group
  have h2 : s * c * s⁻¹ = (s * u * s⁻¹) * v' * (s * u * s⁻¹)⁻¹ * v'⁻¹ := by
    rw [hcdef, hv'def]; group
  rw [hsu] at h2
  have hzc : z * v' = v' * z := hc z hz v'
  have h3 : (u⁻¹ * z) * v' * (u⁻¹ * z)⁻¹ * v'⁻¹ = u⁻¹ * v' * u * v'⁻¹ := by
    calc (u⁻¹ * z) * v' * (u⁻¹ * z)⁻¹ * v'⁻¹ = u⁻¹ * (z * v') * z⁻¹ * u * v'⁻¹ := by group
      _ = u⁻¹ * (v' * z) * z⁻¹ * u * v'⁻¹ := by rw [hzc]
      _ = u⁻¹ * v' * u * v'⁻¹ := by group
  have h4 : c = c'⁻¹ := by
    have e1 : c = u⁻¹ * v' * u * v'⁻¹ := by rw [← h1, h2, h3]
    have e2 : c'⁻¹ = v' * u * v'⁻¹ * u⁻¹ := by rw [hc'def]; group
    have e3 : u⁻¹ * c'⁻¹ * u = c'⁻¹ := by
      have := hc c' hv' u
      have h' : c'⁻¹ * u = u * c'⁻¹ := by
        have := (hc _ (Subgroup.inv_mem _ hv') u)
        exact this
      calc u⁻¹ * c'⁻¹ * u = u⁻¹ * (c'⁻¹ * u) := by group
        _ = u⁻¹ * (u * c'⁻¹) := by rw [h']
        _ = c'⁻¹ := by group
    rw [e1, ← e3, e2]; group
  have h5 : c = c' := by
    have e1 : u * v * u⁻¹ = c * v := by rw [hcdef]; group
    have e2 : u * v' * u⁻¹ = c' * v' := by rw [hc'def]; group
    have e3 : u * (v * v'⁻¹) * u⁻¹ = c * c'⁻¹ * (v * v'⁻¹) := by
      have hcc' : c'⁻¹ * (v * v'⁻¹) = (v * v'⁻¹) * c'⁻¹ := hc _ (Subgroup.inv_mem _ hv') _
      calc u * (v * v'⁻¹) * u⁻¹ = (u * v * u⁻¹) * (u * v' * u⁻¹)⁻¹ := by group
        _ = (c * v) * (c' * v')⁻¹ := by rw [e1, e2]
        _ = c * ((v * v'⁻¹) * c'⁻¹) := by group
        _ = c * (c'⁻¹ * (v * v'⁻¹)) := by rw [hcc']
        _ = c * c'⁻¹ * (v * v'⁻¹) := by group
    have e4 : u * (v * v'⁻¹) * u⁻¹ = v * v'⁻¹ := by rw [hcomm]; group
    have e5 : c * c'⁻¹ = 1 := by
      have := e3.symm.trans e4
      have h6 : c * c'⁻¹ * (v * v'⁻¹) = 1 * (v * v'⁻¹) := by rw [this, one_mul]
      exact mul_right_cancel h6
    exact mul_inv_eq_one.1 e5
  have h6 : c ^ 2 = 1 := by
    rw [pow_two]
    calc c * c = c' * c'⁻¹ := congrArg₂ (· * ·) h5 h4
      _ = 1 := mul_inv_cancel c'
  exact hodd c hv h6


theorem commutator_t_eq_one {Zk : Subgroup Lb} (hc : ∀ z ∈ Zk, ∀ g : Lb, z * g = g * z)
    (hodd : ∀ w ∈ Zk, w ^ 2 = 1 → w = 1) {u t s z z' : Lb} (hz : z ∈ Zk) (hz' : z' ∈ Zk)
    (hsu : s * u * s⁻¹ = u⁻¹ * z) (hst : s⁻¹ * t * s = t * z')
    (hut : u * t * u⁻¹ * t⁻¹ ∈ Zk) : u * t * u⁻¹ * t⁻¹ = 1 := by
  set c := u * t * u⁻¹ * t⁻¹ with hcdef
  have h1 : (s * u * s⁻¹) * t * (s * u * s⁻¹)⁻¹ * t⁻¹ = s * c * s⁻¹ := by
    have e : t = s * (s⁻¹ * t * s) * s⁻¹ := by group
    have e2 : (s * u * s⁻¹) * t * (s * u * s⁻¹)⁻¹ * t⁻¹ =
        s * (u * (s⁻¹ * t * s) * u⁻¹ * (s⁻¹ * t * s)⁻¹) * s⁻¹ := by group
    rw [e2, hst]
    have e3 : u * (t * z') * u⁻¹ * (t * z')⁻¹ = c := by
      have hzt : z' * t⁻¹ = t⁻¹ * z' := hc z' hz' t⁻¹
      calc u * (t * z') * u⁻¹ * (t * z')⁻¹ = u * t * (z' * u⁻¹) * z'⁻¹ * t⁻¹ := by group
        _ = u * t * (u⁻¹ * z') * z'⁻¹ * t⁻¹ := by rw [hc z' hz' u⁻¹]
        _ = c := by rw [hcdef]; group
    rw [e3]
  have h2 : s * c * s⁻¹ = c := by
    have := hc c hut s
    calc s * c * s⁻¹ = (s * c) * s⁻¹ := rfl
      _ = (c * s) * s⁻¹ := by rw [this]
      _ = c := by group
  rw [hsu] at h1
  have h3 : (u⁻¹ * z) * t * (u⁻¹ * z)⁻¹ * t⁻¹ = c⁻¹ := by
    have hzt : z * t = t * z := hc z hz t
    have hcinv : c⁻¹ * u = u * c⁻¹ := hc _ (Subgroup.inv_mem _ hut) u
    calc (u⁻¹ * z) * t * (u⁻¹ * z)⁻¹ * t⁻¹ = u⁻¹ * (z * t) * z⁻¹ * u * t⁻¹ := by group
      _ = u⁻¹ * (t * z) * z⁻¹ * u * t⁻¹ := by rw [hzt]
      _ = u⁻¹ * (t * u * t⁻¹ * u⁻¹) * u := by group
      _ = u⁻¹ * c⁻¹ * u := by rw [hcdef]; group
      _ = u⁻¹ * (c⁻¹ * u) := by group
      _ = u⁻¹ * (u * c⁻¹) := by rw [hcinv]
      _ = c⁻¹ := by group
  have h4 : c = c⁻¹ := h2.symm.trans (h1.symm.trans h3)
  have h5 : c ^ 2 = 1 := by
    rw [pow_two]
    calc c * c = c⁻¹ * c := by rw [← h4]
      _ = 1 := inv_mul_cancel c
  exact hodd c hut h5

theorem exists_lift_pow_eq_one {Zk : Subgroup Lb} (hc : ∀ z ∈ Zk, ∀ g : Lb, z * g = g * z)
    {m : ℕ} (hm : ∀ w ∈ Zk, w ^ (2 * m + 1) = 1) {p : ℕ} {u s z : Lb} (hz : z ∈ Zk)
    (hsu : s * u * s⁻¹ = u⁻¹ * z) (hup : u ^ p ∈ Zk) :
    ∃ g ∈ Zk, (u * g⁻¹) ^ p = 1 := by
  have hcz : Commute z u⁻¹ := (hc z hz u⁻¹)
  have h1 : (s * u * s⁻¹) ^ p = u ^ p := by
    rw [conj_pow]
    have := hc _ hup s
    calc s * u ^ p * s⁻¹ = (s * u ^ p) * s⁻¹ := rfl
      _ = (u ^ p * s) * s⁻¹ := by rw [this]
      _ = u ^ p := by group
  rw [hsu] at h1
  have h2 : (u⁻¹ * z) ^ p = (u⁻¹) ^ p * z ^ p := by
    exact (Commute.mul_pow (hcz.symm) p)
  rw [h2, inv_pow] at h1
  have h3 : (u ^ p) ^ 2 = z ^ p := by
    have : (u ^ p) * (u ^ p) = z ^ p := by
      calc u ^ p * u ^ p = u ^ p * ((u ^ p)⁻¹ * z ^ p) := by rw [h1]
        _ = z ^ p := by group
    rwa [← pow_two] at this
  refine ⟨z ^ (m + 1), Subgroup.pow_mem _ hz _, ?_⟩
  have hgc : Commute u (z ^ (m + 1))⁻¹ := ((hc _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hz _)) u).symm)
  rw [hgc.mul_pow, inv_pow, ← pow_mul, mul_comm (m + 1) p, pow_mul]
  have h4 : (z ^ p) ^ (m + 1) = u ^ p := by
    rw [← h3, ← pow_mul]
    have h5 := hm (u ^ p) hup
    calc (u ^ p) ^ (2 * (m + 1)) = (u ^ p) ^ (2 * m + 1) * u ^ p := by rw [← pow_succ]; congr 1
      _ = u ^ p := by rw [h5, one_mul]
  rw [h4]
  exact mul_inv_cancel _


section Complement

theorem exists_complement_comm {A : Type*} [CommGroup A] [Finite A] {p : ℕ} (hp : p.Prime)
    (hexp : ∀ a : A, a ^ p = 1) (Z : Subgroup A) :
    ∃ E : Subgroup A, E ⊓ Z = ⊥ ∧ E ⊔ Z = ⊤ := by
  classical
  have hne : Nonempty {E : Subgroup A // E ⊓ Z = ⊥} := ⟨⟨⊥, by simp⟩⟩
  obtain ⟨⟨E, hE⟩, hmax⟩ := Finite.exists_max (fun E : {E : Subgroup A // E ⊓ Z = ⊥} =>
    Nat.card E.1)
  refine ⟨E, hE, ?_⟩
  by_contra hne'
  obtain ⟨g, hg⟩ : ∃ g : A, g ∉ E ⊔ Z := by
    by_contra h
    push Not at h
    exact hne' (eq_top_iff.2 fun x _ => h x)
  have hg1 : g ≠ 1 := fun h => hg (h ▸ one_mem _)
  have hord : orderOf g = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one (hexp g)) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hg1
    · exact h
  have hK : zpowers g ⊓ (E ⊔ Z) = ⊥ := by
    set K := zpowers g ⊓ (E ⊔ Z) with hKdef
    have hdvd : Nat.card K ∣ Nat.card (zpowers g) := Subgroup.card_dvd_of_le inf_le_left
    rw [Nat.card_zpowers, hord] at hdvd
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact Subgroup.card_eq_one.1 h
    · exfalso
      have hK' : K = zpowers g := Subgroup.eq_of_le_of_card_ge inf_le_left (by
        rw [Nat.card_zpowers, hord, h])
      have : g ∈ K := hK' ▸ Subgroup.mem_zpowers g
      exact hg this.2
  have hE' : (E ⊔ zpowers g) ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨e, he, w, hw, rfl⟩ := Subgroup.mem_sup.1 hx.1
    have hw' : w ∈ zpowers g ⊓ (E ⊔ Z) := by
      refine ⟨hw, ?_⟩
      have : w = e⁻¹ * (e * w) := by group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left (inv_mem he)) (Subgroup.mem_sup_right hx.2)
    rw [hK, Subgroup.mem_bot] at hw'
    rw [hw', mul_one] at hx ⊢
    have : e ∈ E ⊓ Z := ⟨he, hx.2⟩
    rw [hE] at this
    exact this
  have hle : E ≤ E ⊔ zpowers g := le_sup_left
  have hcard := hmax ⟨E ⊔ zpowers g, hE'⟩
  have heq : E = E ⊔ zpowers g := Subgroup.eq_of_le_of_card_ge hle hcard
  have hgE : g ∈ E := by
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  exact hg (Subgroup.mem_sup_left hgE)

theorem exists_sub_complement {Lb : Type*} [Group Lb] [Finite Lb] {p : ℕ} (hp : p.Prime)
    (Ω Zk : Subgroup Lb) (hcomm : ∀ a ∈ Ω, ∀ b ∈ Ω, a * b = b * a)
    (hexp : ∀ a ∈ Ω, a ^ p = 1) :
    ∃ E : Subgroup Lb, E ≤ Ω ∧ E ⊓ Zk = ⊥ ∧ ∀ g ∈ Ω, ∃ e ∈ E, ∃ z ∈ Zk, g = e * z := by
  classical
  let _ : CommGroup Ω := { (inferInstance : Group Ω) with
    mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  obtain ⟨E', hE1, hE2⟩ := exists_complement_comm hp
    (fun a : Ω => Subtype.ext (by simpa using hexp a a.2)) (Zk.subgroupOf Ω)
  refine ⟨E'.map Ω.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [eq_bot_iff]
    intro y hy
    obtain ⟨hym, hyZ⟩ := hy
    obtain ⟨e, he, rfl⟩ := hym
    have : e ∈ E' ⊓ Zk.subgroupOf Ω := ⟨he, hyZ⟩
    rw [hE1, Subgroup.mem_bot] at this
    rw [this]
    exact one_mem _
  · intro g hg
    have hmem : (⟨g, hg⟩ : Ω) ∈ E' ⊔ Zk.subgroupOf Ω := by rw [hE2]; trivial
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.1 hmem
    refine ⟨(y : Lb), ⟨y, hy, rfl⟩, (z : Lb), hz, ?_⟩
    exact (congrArg Subtype.val hyz).symm

end Complement
end Helpers


section Main

variable {S : Type*} [Group S]

theorem LowerData.comm_W {p : ℕ} (D : LowerData p S) :
    ∀ a ∈ closure (Set.range D.X), ∀ b ∈ closure (Set.range D.X), Commute a b := by
  have h1 : ∀ i, ∀ b ∈ closure (Set.range D.X), Commute (D.X i) b := by
    intro i b hb
    induction hb using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact D.comm i j
    | one => exact Commute.one_right _
    | mul x y _ _ hx hy => exact hx.mul_right hy
    | inv x _ hx => exact hx.inv_right
  intro a ha b hb
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact h1 j b hb
  | one => exact Commute.one_left _
  | mul x y _ _ hx hy => exact hx.mul_left hy
  | inv x _ hx => exact hx.inv_left


theorem comm_aux_mul {W : Subgroup S} (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) {a b c d : S}
    (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W) (hd : d ∈ W) :
    a * b * (c * d)⁻¹ = (a * c⁻¹) * (b * d⁻¹) := by
  let _ : CommGroup W := { (inferInstance : Group W) with
    mul_comm := fun a b => Subtype.ext (hW a a.2 b b.2) }
  have := congrArg Subtype.val (show (⟨a, ha⟩ : W) * ⟨b, hb⟩ * (⟨c, hc⟩ * ⟨d, hd⟩)⁻¹ =
    (⟨a, ha⟩ * ⟨c, hc⟩⁻¹) * (⟨b, hb⟩ * ⟨d, hd⟩⁻¹) by
      rw [mul_inv]; ac_rfl)
  simpa using this

theorem comm_aux_inv {W : Subgroup S} (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) {a c : S}
    (ha : a ∈ W) (hc : c ∈ W) : a⁻¹ * c = (a * c⁻¹)⁻¹ := by
  have := hW a⁻¹ (inv_mem ha) c hc
  calc a⁻¹ * c = c * a⁻¹ := this
    _ = (a * c⁻¹)⁻¹ := by group

theorem LowerData.swap_W {p : ℕ} (D : LowerData p S) (k : Fin 4) :
    ∀ y ∈ closure (Set.range D.X), (D.Sw k * y * (D.Sw k)⁻¹ ∈ closure (Set.range D.X)) ∧
      y * (D.Sw k * y * (D.Sw k)⁻¹)⁻¹ ∈ zpowers (D.X k) := by
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    by_cases hjk : j = k
    · subst hjk
      rw [D.sw_self]
      refine ⟨inv_mem (subset_closure ⟨j, rfl⟩), ?_⟩
      rw [inv_inv]
      exact mul_mem (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
    · rw [D.sw_other j k hjk]
      refine ⟨mul_mem (inv_mem (subset_closure ⟨k, rfl⟩)) (subset_closure ⟨j, rfl⟩), ?_⟩
      have : D.X j * ((D.X k)⁻¹ * D.X j)⁻¹ = D.X k := by group
      rw [this]
      exact Subgroup.mem_zpowers _
  | one => simp
  | mul x y hx hy ihx ihy =>
    obtain ⟨hx1, hx2⟩ := ihx
    obtain ⟨hy1, hy2⟩ := ihy
    have e : D.Sw k * (x * y) * (D.Sw k)⁻¹ =
        (D.Sw k * x * (D.Sw k)⁻¹) * (D.Sw k * y * (D.Sw k)⁻¹) := by group
    rw [e]
    refine ⟨mul_mem hx1 hy1, ?_⟩
    have hWc : ∀ a ∈ closure (Set.range D.X), ∀ b ∈ closure (Set.range D.X), a * b = b * a :=
      fun a ha b hb => (D.comm_W a ha b hb).eq
    have e2 : x * y * ((D.Sw k * x * (D.Sw k)⁻¹) * (D.Sw k * y * (D.Sw k)⁻¹))⁻¹ =
        (x * (D.Sw k * x * (D.Sw k)⁻¹)⁻¹) * (y * (D.Sw k * y * (D.Sw k)⁻¹)⁻¹) :=
      comm_aux_mul hWc hx hy hx1 hy1
    rw [e2]
    exact mul_mem hx2 hy2
  | inv x hx ih =>
    obtain ⟨h1, h2⟩ := ih
    have e : D.Sw k * x⁻¹ * (D.Sw k)⁻¹ = (D.Sw k * x * (D.Sw k)⁻¹)⁻¹ := by group
    rw [e]
    refine ⟨inv_mem h1, ?_⟩
    rw [inv_inv]
    have hWc : ∀ a ∈ closure (Set.range D.X), ∀ b ∈ closure (Set.range D.X), a * b = b * a :=
      fun a ha b hb => (D.comm_W a ha b hb).eq
    have : x⁻¹ * (D.Sw k * x * (D.Sw k)⁻¹) = (x * (D.Sw k * x * (D.Sw k)⁻¹)⁻¹)⁻¹ :=
      comm_aux_inv hWc hx h1
    rw [this]
    exact inv_mem h2

theorem exists_cover_lower {p : ℕ} (hp : p.Prime) {Lb : Type*} [Group Lb] [Finite Lb]
    (D : LowerData p S) (Γ : Lb →* S) (hΓ : Function.Surjective Γ)
    (hZ : Γ.ker ≤ Subgroup.center Lb) (hodd : Odd (Nat.card Γ.ker)) :
    ∃ E T : Subgroup Lb, CFSG.Open.IsElemAbelian p E ∧ (∃ r, 4 ≤ r ∧ Nat.card E = p ^ r) ∧
      E ⊓ Γ.ker = ⊥ ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ Subgroup.centralizer (T : Set Lb) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set Zk := Γ.ker with hZk
  have hc : ∀ z ∈ Zk, ∀ g : Lb, z * g = g * z := fun z hz g =>
    (Subgroup.mem_center_iff.1 (hZ hz) g).symm
  obtain ⟨m, hmN⟩ := hodd
  have hm : ∀ w ∈ Zk, w ^ (2 * m + 1) = 1 := by
    intro w hw
    have := pow_card_eq_one' (G := Zk) (x := ⟨w, hw⟩)
    rw [hmN] at this
    exact congrArg Subtype.val this
  have hodd2 : ∀ w ∈ Zk, w ^ 2 = 1 → w = 1 := by
    intro w hw h2
    calc w = w ^ (2 * m + 1) * w := by rw [hm w hw, one_mul]
      _ = w ^ (2 * m + 1 + 1) := (pow_succ w _).symm
      _ = (w ^ 2) ^ (m + 1) := by rw [← pow_mul]; congr 1
      _ = 1 := by rw [h2, one_pow]
  choose xh hxh using fun k => hΓ (D.X k)
  choose sh hsh using fun k => hΓ (D.Sw k)
  have hsu : ∀ k u, Γ u = D.X k → ∃ z ∈ Zk, sh k * u * (sh k)⁻¹ = u⁻¹ * z := by
    intro k u hu
    refine ⟨u * (sh k * u * (sh k)⁻¹), ?_, by group⟩
    rw [hZk, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hsh, hu, D.sw_self]
    exact mul_inv_cancel _
  set W := closure (Set.range D.X) with hW
  have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb => (D.comm_W a ha b hb).eq
  set Wt : Subgroup Lb := W.comap Γ with hWt
  set R : Set Lb := {u | Γ u ∈ Set.range D.X} with hR
  have hRmem : ∀ k u, Γ u = D.X k → u ∈ R := fun k u hu => ⟨k, hu.symm⟩
  have hker_le : Zk ≤ closure R := by
    intro z hz
    have h1 : xh 0 * z ∈ R := by
      refine ⟨0, ?_⟩
      rw [map_mul, hxh, (MonoidHom.mem_ker.1 hz), mul_one]
    have h2 : xh 0 ∈ R := hRmem 0 _ (hxh 0)
    have := mul_mem (subset_closure h1) (inv_mem (subset_closure h2))
    have e : xh 0 * z * (xh 0)⁻¹ = z := by
      calc xh 0 * z * (xh 0)⁻¹ = z * xh 0 * (xh 0)⁻¹ := by rw [← hc z hz (xh 0)]
        _ = z := by group
    rwa [e] at this
  have hWt_le : Wt ≤ closure R := by
    have h2 : (closure R).map Γ = W := by
      rw [MonoidHom.map_closure, hW]
      congr 1
      ext w
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact hu
      · intro hw
        obtain ⟨u, rfl⟩ := hΓ w
        exact ⟨u, hw, rfl⟩
    calc Wt = W.comap Γ := rfl
      _ = ((closure R).map Γ).comap Γ := by rw [h2]
      _ = closure R ⊔ Γ.ker := Subgroup.comap_map_eq _ _
      _ = closure R := sup_eq_left.2 hker_le
      _ ≤ closure R := le_rfl
  have hXW : ∀ k, D.X k ∈ W := fun k => subset_closure ⟨k, rfl⟩
  have hA : ∀ k u, Γ u = D.X k → ∀ v ∈ Wt, u * v = v * u := by
    intro k u hu v hv
    obtain ⟨z, hz, hsu'⟩ := hsu k u hu
    have hvW : Γ v ∈ W := hv
    have hv'W : Γ (sh k * v * (sh k)⁻¹) ∈ W := by
      rw [map_mul, map_mul, map_inv, hsh]
      exact (D.swap_W k _ hvW).1
    have h1 : u * v * u⁻¹ * v⁻¹ ∈ Zk := by
      rw [hZk, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hu]
      rw [hWc _ (hXW k) _ hvW]
      group
    have h2 : u * (sh k * v * (sh k)⁻¹) * u⁻¹ * (sh k * v * (sh k)⁻¹)⁻¹ ∈ Zk := by
      rw [hZk, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hu]
      rw [hWc _ (hXW k) _ hv'W]
      group
    have h3 : u * (v * (sh k * v * (sh k)⁻¹)⁻¹) = (v * (sh k * v * (sh k)⁻¹)⁻¹) * u := by
      obtain ⟨i, hi⟩ := (D.swap_W k _ hvW).2
      have hi' : D.X k ^ i = Γ v * (D.Sw k * Γ v * (D.Sw k)⁻¹)⁻¹ := hi
      have hG : Γ (v * (sh k * v * (sh k)⁻¹)⁻¹) = Γ v * (D.Sw k * Γ v * (D.Sw k)⁻¹)⁻¹ := by
        simp [hsh]
      have hz'' : (u ^ i)⁻¹ * (v * (sh k * v * (sh k)⁻¹)⁻¹) ∈ Zk := by
        rw [hZk, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hu, hG, hi']
        group
      set z'' := (u ^ i)⁻¹ * (v * (sh k * v * (sh k)⁻¹)⁻¹) with hz''def
      have e : v * (sh k * v * (sh k)⁻¹)⁻¹ = u ^ i * z'' := by rw [hz''def]; group
      rw [e]
      have hu1 : Commute u (u ^ i) := Commute.self_zpow u i
      have hu2 : Commute u z'' := (hc z'' hz'' u).symm
      exact (hu1.mul_right hu2).eq
    have := pairing_eq_one hc hodd2 hz hsu' h1 h2 h3
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  have hWtcomm : ∀ a ∈ Wt, ∀ b ∈ Wt, a * b = b * a := by
    have h1 : closure R ≤ Subgroup.centralizer (Wt : Set Lb) := by
      rw [Subgroup.closure_le]
      intro u hu
      obtain ⟨k, hk⟩ := hu
      exact Subgroup.mem_centralizer_iff.2 fun v hv => (hA k u hk.symm v hv).symm
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.1 (h1 (hWt_le ha)) b hb).symm
  let Ω : Subgroup Lb :=
    { carrier := {y | y ∈ Wt ∧ y ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [(show Commute a b from hWtcomm a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow _⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hΩmem : ∀ y, y ∈ Ω ↔ y ∈ Wt ∧ y ^ p = 1 := fun y => Iff.rfl
  have hlift : ∀ k, ∃ y ∈ Ω, Γ y = D.X k := by
    intro k
    obtain ⟨z, hz, hsz⟩ := hsu k (xh k) (hxh k)
    have hup : (xh k) ^ p ∈ Zk := by
      rw [hZk, MonoidHom.mem_ker, map_pow, hxh, D.pow]
    obtain ⟨g, hg, hgp⟩ := exists_lift_pow_eq_one hc hm hz hsz hup
    have hgΓ : Γ g = 1 := by rw [hZk] at hg; exact MonoidHom.mem_ker.1 hg
    have hΓy : Γ (xh k * g⁻¹) = D.X k := by rw [map_mul, map_inv, hgΓ, hxh, inv_one, mul_one]
    exact ⟨xh k * g⁻¹, ⟨by rw [hWt]; exact (Subgroup.mem_comap.2 (by rw [hΓy]; exact hXW k)), hgp⟩,
      hΓy⟩
  have hΩW : Ω.map Γ = W := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.1
    · rw [hW, Subgroup.closure_le]
      rintro _ ⟨k, rfl⟩
      obtain ⟨y, hy, hyk⟩ := hlift k
      exact ⟨y, hy, hyk⟩
  obtain ⟨E, hEΩ, hEZ, hEcover⟩ := exists_sub_complement hp Ω Zk
    (fun a ha b hb => hWtcomm a ha.1 b hb.1) (fun a ha => ha.2)
  have hEmap : E.map Γ = W := by
    refine le_antisymm ?_ ?_
    · rw [← hΩW]
      exact Subgroup.map_mono hEΩ
    · intro w hw
      rw [← hΩW] at hw
      obtain ⟨g, hg, rfl⟩ := hw
      obtain ⟨e, he, z, hz, rfl⟩ := hEcover g hg
      have hzΓ : Γ z = 1 := by rw [hZk] at hz; exact MonoidHom.mem_ker.1 hz
      refine ⟨e, he, ?_⟩
      rw [map_mul, hzΓ, mul_one]
  have hEinj : Function.Injective (Γ.domRestrict E) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (x : Lb) ∈ E ⊓ Zk := ⟨x.2, by rw [hZk]; exact MonoidHom.mem_ker.2 hx⟩
    rw [hEZ, Subgroup.mem_bot] at hx'
    exact Subtype.ext hx'
  have hEcard : Nat.card E = Nat.card W := by
    rw [← hEmap, ← MonoidHom.domRestrict_range]
    exact (Nat.card_congr (MonoidHom.ofInjective hEinj).toEquiv)
  have hEel : CFSG.Open.IsElemAbelian p E :=
    ⟨⟨⟨fun a b => Subtype.ext (hWtcomm a (hEΩ a.2).1 b (hEΩ b.2).1)⟩⟩, fun x hx => (hEΩ hx).2⟩
  have hEp : IsPGroup p E := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hEel.2 g g.2)⟩
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.1 hEp
  have hr4 : 4 ≤ r := by
    have h1 : p ^ 4 ≤ p ^ r := by rw [← hr, hEcard]; exact D.card
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
  obtain ⟨u0, hu0⟩ := hΓ D.T
  obtain ⟨e2, he2⟩ := D.T_two
  have hcop : Nat.Coprime (2 * m + 1) (orderOf D.T) := by
    have h1 : Nat.Coprime (2 * m + 1) (2 ^ e2) :=
      Nat.Coprime.pow_right _ (Odd.coprime_two_right ⟨m, rfl⟩)
    exact h1.coprime_dvd_right (orderOf_dvd_of_pow_eq_one he2)
  obtain ⟨c, hcT⟩ := exists_pow_eq_self_of_coprime hcop
  set that : Lb := u0 ^ ((2 * m + 1) * c) with hthat
  have hΓt : Γ that = D.T := by rw [hthat, map_pow, hu0, pow_mul, hcT]
  have hthat2 : that ^ (2 ^ e2) = 1 := by
    have h1 : u0 ^ (2 ^ e2) ∈ Zk := by
      rw [hZk, MonoidHom.mem_ker, map_pow, hu0, he2]
    calc that ^ (2 ^ e2) = u0 ^ ((2 * m + 1) * c * 2 ^ e2) := by rw [hthat, ← pow_mul]
      _ = (u0 ^ (2 ^ e2)) ^ ((2 * m + 1) * c) := by rw [← pow_mul]; congr 1; ring
      _ = ((u0 ^ (2 ^ e2)) ^ (2 * m + 1)) ^ c := by rw [pow_mul]
      _ = 1 := by rw [hm _ h1, one_pow]
  have hthat1 : that ≠ 1 := fun h => D.T_ne (by rw [← hΓt, h, map_one])
  have hC : ∀ k u, Γ u = D.X k → u * that = that * u := by
    intro k u hu
    obtain ⟨z, hz, hsu'⟩ := hsu k u hu
    have e : (D.Sw k)⁻¹ * D.T * D.Sw k = D.T := by
      rw [mul_assoc, (D.T_sw k).eq, inv_mul_cancel_left]
    have hz' : that⁻¹ * ((sh k)⁻¹ * that * sh k) ∈ Zk := by
      rw [hZk, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hsh, hΓt, e]
      exact inv_mul_cancel _
    have hst : (sh k)⁻¹ * that * sh k = that * (that⁻¹ * ((sh k)⁻¹ * that * sh k)) := by group
    have hut : u * that * u⁻¹ * that⁻¹ ∈ Zk := by
      rw [hZk, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hu, hΓt,
        ← (D.T_comm k).eq]
      group
    have := commutator_t_eq_one hc hodd2 hz hz' hsu' hst hut
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  have hCt : ∀ a ∈ Wt, a * that = that * a := by
    have h1 : closure R ≤ Subgroup.centralizer ({that} : Set Lb) := by
      rw [Subgroup.closure_le]
      intro u hu
      obtain ⟨k, hk⟩ := hu
      exact Subgroup.mem_centralizer_iff.2 fun v hv => by
        rw [Set.mem_singleton_iff.1 hv]
        exact (hC k u hk.symm).symm
    intro a ha
    exact (Subgroup.mem_centralizer_iff.1 (h1 (hWt_le ha)) that rfl).symm
  refine ⟨E, Subgroup.zpowers that, hEel, ⟨r, hr4, hr⟩, hEZ, ?_, ?_, ?_⟩
  · exact fun h => hthat1 (Subgroup.zpowers_eq_bot.1 h)
  · have hord : orderOf that ∣ 2 ^ e2 := orderOf_dvd_of_pow_eq_one hthat2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  · intro x hx
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hx' : x ∈ Wt := (hEΩ hx).1
    have hcm : Commute that x := (hCt x hx').symm
    exact (hcm.zpow_left i).eq

end Main

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
