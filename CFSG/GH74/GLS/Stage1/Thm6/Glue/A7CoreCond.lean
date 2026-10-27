module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.A7Core

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue.A7

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

local notation "S₇" => Equiv.Perm (Fin 7)
local notation "A₇" => alternatingGroup (Fin 7)

section Generic

variable {G : Type*} [Group G]

theorem zpowers_sq_one {x : G} (hx : x * x = 1) : ∀ b ∈ Subgroup.zpowers x, b * b = 1 := by
  intro b hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hx, one_zpow]

theorem isEA_subgroupOf' {X : Type*} [Group X] {H V : Subgroup X} (hV : Dihedral.IsEA V) :
    Dihedral.IsEA (V.subgroupOf H) := by
  intro a ha
  have ha' : (a : X) ∈ V := ha
  refine ⟨Subtype.ext ((hV _ ha').1), fun b hb => Subtype.ext ((hV _ ha').2 _ hb)⟩

end Generic

variable {G : Type*} [Group G]

namespace Abs

variable {C T P Q Rd : Subgroup G} {ρ : G → S₇} {Tp : Subgroup S₇} {f : S₇}

noncomputable def rhoC (h : Abs C T P Q Rd ρ Tp f) : ↥C →* S₇ where
  toFun g := ρ g
  map_one' := h.rho_one
  map_mul' a b := h.rho_mul a a.2 b b.2

noncomputable def img (h : Abs C T P Q Rd ρ Tp f) (S : Subgroup G) (hS : S ≤ C) : Subgroup S₇ :=
  ((h.rhoC).comp (Subgroup.inclusion hS)).range

theorem mem_img (h : Abs C T P Q Rd ρ Tp f) {S : Subgroup G} (hS : S ≤ C) {a : S₇} :
    a ∈ h.img S hS ↔ ∃ g ∈ S, ρ g = a := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.1, g.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

theorem isEA_img (h : Abs C T P Q Rd ρ Tp f) {S : Subgroup G} (hS : S ≤ C) (hEA : IsElemAb2 S) :
    Dihedral.IsEA (h.img S hS) := by
  intro a ha
  obtain ⟨g, hg, rfl⟩ := (h.mem_img hS).1 ha
  refine ⟨?_, fun b hb => ?_⟩
  · rw [← h.rho_mul g (hS hg) g (hS hg), (hEA g hg).1, h.rho_one]
  · obtain ⟨g', hg', rfl⟩ := (h.mem_img hS).1 hb
    rw [← h.rho_mul g (hS hg) g' (hS hg'), ← h.rho_mul g' (hS hg') g (hS hg), (hEA g hg).2 g' hg']

theorem card_img (h : Abs C T P Q Rd ρ Tp f) {V : Subgroup G} (hVP : V ≤ P) (hS : V ≤ C) :
    Nat.card (h.img V hS) = Nat.card V := by
  have hinj : Function.Injective ((h.rhoC).comp (Subgroup.inclusion hS)) := by
    intro a b hab
    apply Subtype.ext
    exact h.P_inj a (hVP a.2) b (hVP b.2) hab
  exact Nat.card_range_of_injective hinj

theorem img_le_Pbar (h : Abs C T P Q Rd ρ Tp f) {S : Subgroup G} (hS : S ≤ C) (hSRd : S ≤ Rd) :
    h.img S hS ≤ Tp ⊓ A₇ := by
  intro a ha
  obtain ⟨g, hg, rfl⟩ := (h.mem_img hS).1 ha
  exact ⟨h.rho_T g (h.Rd_le_T (hSRd hg)), ((h.mem_Rd g).1 (hSRd hg)).2⟩

theorem Rd_dihedral (h : Abs C T P Q Rd ρ Tp f) {x : G} (hQ : Q = zpowers x)
    (hxC : ∀ c ∈ C, c * x = x * c) :
    ∀ P' : Subgroup G, P' ≤ Rd → P' ⊓ zpowers x = ⊥ → P' ⊔ zpowers x = Rd →
      ∃ ρ' s : G, ρ' ∈ P' ∧ s ∈ P' ∧ s * s = 1 ∧ s * ρ' * s⁻¹ = ρ'⁻¹ ∧
        ∀ d ∈ P', ∃ i : ℤ, d = ρ' ^ i ∨ d = s * ρ' ^ i := by
  intro P' hP'Rd hP'x hP'sup
  have hP'C : ∀ g ∈ P', g ∈ C := fun g hg => h.T_le_C (h.Rd_le_T (hP'Rd hg))
  have hρA : ∀ g ∈ P', ρ g ∈ Tp ⊓ A₇ := fun g hg =>
    ⟨h.rho_T g (h.Rd_le_T (hP'Rd hg)), ((h.mem_Rd g).1 (hP'Rd hg)).2⟩
  let Φ : ↥P' →* ↥(Tp ⊓ A₇) :=
    { toFun := fun g => ⟨ρ g, hρA g g.2⟩
      map_one' := Subtype.ext h.rho_one
      map_mul' := fun a b => Subtype.ext (h.rho_mul a (hP'C a a.2) b (hP'C b b.2)) }
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : ρ g = 1 := congrArg Subtype.val hg
    have h2 : (g : G) ∈ Q := (h.mem_Q g).2 ⟨h.Rd_le_T (hP'Rd g.2), h1⟩
    rw [hQ] at h2
    have h3 : (g : G) ∈ P' ⊓ zpowers x := ⟨g.2, h2⟩
    rw [hP'x, mem_bot] at h3
    exact Subtype.ext h3
  have hsurj : Function.Surjective Φ := by
    rintro ⟨a, ha⟩
    obtain ⟨p, hp, hpa⟩ := (h.rho_P a).1 ha
    have hpRd : p ∈ P' ⊔ zpowers x := by rw [hP'sup]; exact h.P_le_Rd hp
    have hcomm : ∀ a ∈ P', ∀ b ∈ zpowers x, a * b = b * a := by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
      exact (Commute.zpow_right (show Commute a x from hxC a (hP'C a ha)) k).eq
    obtain ⟨p', hp', b, hb, rfl⟩ := (mem_sup_iff_of_comm hcomm).1 hpRd
    have hbQ : b ∈ Q := by rw [hQ]; exact hb
    refine ⟨⟨p', hp'⟩, Subtype.ext ?_⟩
    show ρ p' = a
    rw [← hpa, h.rho_mul p' (hP'C p' hp') b (h.T_le_C (h.Q_le_T hbQ)), h.rho_Q hbQ, mul_one]
  have e₃ : ↥P' ≃* DihedralGroup 4 := (MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩).trans h.sp.eB
  exact Dihedral.isDihedral2_of_equiv e₃

theorem Rd_fuse (h : Abs C T P Q Rd ρ Tp f) {x : G} (hQ : Q = zpowers x) :
    P ⊔ zpowers x ≠ Rd → ∀ E E' : Subgroup G, E ≤ P ⊔ zpowers x → E' ≤ P ⊔ zpowers x →
      IsElemAb2 E → IsElemAb2 E' → Nat.card E = 8 → Nat.card E' = 8 →
      ∃ r ∈ Rd, E' = Hconj r E := fun hne => by
  exfalso
  apply hne
  rw [h.Rd_eq, hQ]

theorem elemAb8_data [Finite G] (h : Abs C T P Q Rd ρ Tp f) {x : G} (hQ : Q = zpowers x) (hrk : Rank2Le C 3)
    (hx : x * x = 1) (hx1 : x ≠ 1) (hxC : ∀ c ∈ C, c * x = x * c) (hxT : x ∈ T)
    {E : Subgroup G} (hET : E ≤ T) (hE : IsElemAb2 E) (hc : Nat.card E = 8) :
    x ∈ E ∧ (∀ t ∈ T, t ∈ E ↔ ρ t ∈ h.img E (hET.trans h.T_le_C)) ∧
      Dihedral.IsEA (h.img E (hET.trans h.T_le_C)) ∧
      Nat.card (h.img E (hET.trans h.T_le_C)) = 4 := by
  have hEC : E ≤ C := hET.trans h.T_le_C
  have hxC' : x ∈ C := h.T_le_C hxT
  have hxE : x ∈ E := by
    have hcomm : ∀ a ∈ E, ∀ b ∈ zpowers x, a * b = b * a := by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
      exact (Commute.zpow_right (show Commute a x from hxC a (hEC ha)) k).eq
    have hE₁C : E ⊔ zpowers x ≤ C := sup_le hEC (zpowers_le.2 hxC')
    have hE₁ : IsElemAb2 (E ⊔ zpowers x) := by
      intro g hg
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hcomm).1 hg
      have hbb := zpowers_sq_one hx b hb
      have haa := (hE a ha).1
      have hab := hcomm a ha b hb
      refine ⟨?_, ?_⟩
      · calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
          _ = a * (a * b) * b := by rw [← hab]
          _ = (a * a) * (b * b) := by simp only [mul_assoc]
          _ = 1 := by rw [haa, hbb, mul_one]
      · intro g' hg'
        obtain ⟨a', ha', b', hb', rfl⟩ := (mem_sup_iff_of_comm hcomm).1 hg'
        have h1 : a * a' = a' * a := (hE a ha).2 a' ha'
        have h2 : b * b' = b' * b := by
          obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
          obtain ⟨l, rfl⟩ := mem_zpowers_iff.1 hb'
          rw [← zpow_add, ← zpow_add, add_comm]
        have h3 : a * b' = b' * a := hcomm a ha b' hb'
        have h4 : a' * b = b * a' := hcomm a' ha' b hb
        calc a * b * (a' * b') = a * (b * a') * b' := by simp only [mul_assoc]
          _ = a * (a' * b) * b' := by rw [h4]
          _ = (a * a') * (b * b') := by simp only [mul_assoc]
          _ = (a' * a) * (b' * b) := by rw [h1, h2]
          _ = a' * (a * b') * b := by simp only [mul_assoc]
          _ = a' * (b' * a) * b := by rw [h3]
          _ = a' * b' * (a * b) := by simp only [mul_assoc]
    have hcard := hrk _ hE₁C hE₁
    have heq : E = E ⊔ zpowers x :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hc]; simpa using hcard)
    rw [heq]
    exact mem_sup_right (mem_zpowers x)
  have hchar : ∀ t ∈ T, t ∈ E ↔ ρ t ∈ h.img E hEC := by
    intro t ht
    constructor
    · intro htE; exact (h.mem_img hEC).2 ⟨t, htE, rfl⟩
    · intro ha
      obtain ⟨g, hg, hgt⟩ := (h.mem_img hEC).1 ha
      have hgC := hEC hg
      have htC := h.T_le_C ht
      have hq : g⁻¹ * t ∈ Q := (h.mem_Q _).2 ⟨T.mul_mem (T.inv_mem (hET hg)) ht, by
        rw [h.rho_mul g⁻¹ (inv_mem hgC) t htC, h.rho_inv g hgC, hgt, inv_mul_cancel]⟩
      rw [hQ] at hq
      have hqE : g⁻¹ * t ∈ E := zpowers_le.2 hxE hq
      have : t = g * (g⁻¹ * t) := by group
      rw [this]
      exact E.mul_mem hg hqE
  refine ⟨hxE, hchar, h.isEA_img hEC hE, ?_⟩
  let Φ : ↥E →* S₇ := (h.rhoC).comp (Subgroup.inclusion hEC)
  have hΦ : ∀ g : ↥E, Φ g = ρ g := fun g => rfl
  have hker : Φ.ker = (zpowers x).subgroupOf E := by
    ext g
    rw [MonoidHom.mem_ker, hΦ, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have : (g : G) ∈ Q := (h.mem_Q g).2 ⟨hET g.2, h1⟩
      rwa [hQ] at this
    · intro h1
      have : (g : G) ∈ Q := by rw [hQ]; exact h1
      exact h.rho_Q this
  have hxorder : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
  have hkercard : Nat.card Φ.ker = 2 := by
    rw [hker, card_subgroupOf (zpowers_le.2 hxE), Nat.card_zpowers, hxorder]
  have h1 := Subgroup.card_mul_index Φ.ker
  rw [Subgroup.index_ker, hkercard, hc] at h1
  show Nat.card Φ.range = 4
  omega

theorem E8_two [Finite G] (h : Abs C T P Q Rd ρ Tp f) {x : G} (hQ : Q = zpowers x) (hΩ : omega1 T ≤ Rd)
    (hrk : Rank2Le C 3) (hx : x * x = 1) (hx1 : x ≠ 1) (hxC : ∀ c ∈ C, c * x = x * c)
    (hxT : x ∈ T) :
    ∀ E₁ E₂ E₃ : Subgroup G, E₁ ≤ T → E₂ ≤ T → E₃ ≤ T → IsElemAb2 E₁ → IsElemAb2 E₂ →
      IsElemAb2 E₃ → Nat.card E₁ = 8 → Nat.card E₂ = 8 → Nat.card E₃ = 8 →
      E₁ = E₂ ∨ E₁ = E₃ ∨ E₂ = E₃ := by
  intro E₁ E₂ E₃ hT₁ hT₂ hT₃ h₁ h₂ h₃ c₁ c₂ c₃
  have hRd : ∀ E : Subgroup G, E ≤ T → IsElemAb2 E → E ≤ Rd := fun E hET hE g hg =>
    hΩ (Subgroup.subset_closure ⟨hET hg, (hE g hg).1⟩)
  have data : ∀ E : Subgroup G, ∀ hET : E ≤ T, IsElemAb2 E → Nat.card E = 8 →
      ∃ hEC : E ≤ C, (∀ t ∈ T, t ∈ E ↔ ρ t ∈ h.img E hEC) ∧
        Dihedral.IsEA ((h.img E hEC).subgroupOf (Tp ⊓ A₇)) ∧
        Nat.card ((h.img E hEC).subgroupOf (Tp ⊓ A₇)) = 4 := by
    intro E hET hE hc
    obtain ⟨-, hchar, hEA, hcard⟩ := h.elemAb8_data hQ hrk hx hx1 hxC hxT hET hE hc
    have hEC := hET.trans h.T_le_C
    have hle : h.img E hEC ≤ Tp ⊓ A₇ := h.img_le_Pbar hEC (hRd E hET hE)
    exact ⟨hEC, hchar, isEA_subgroupOf' hEA, by rw [card_subgroupOf hle]; exact hcard⟩
  obtain ⟨hC₁, hch₁, hEA₁, hcard₁⟩ := data E₁ hT₁ h₁ c₁
  obtain ⟨hC₂, hch₂, hEA₂, hcard₂⟩ := data E₂ hT₂ h₂ c₂
  obtain ⟨hC₃, hch₃, hEA₃, hcard₃⟩ := data E₃ hT₃ h₃ c₃
  have key : ∀ (E E' : Subgroup G) (hEC : E ≤ C) (hE'C : E' ≤ C), E ≤ T → E' ≤ T →
      E ≤ Rd → E' ≤ Rd →
      (∀ t ∈ T, t ∈ E ↔ ρ t ∈ h.img E hEC) →
      (∀ t ∈ T, t ∈ E' ↔ ρ t ∈ h.img E' hE'C) →
      ((h.img E hEC).subgroupOf (Tp ⊓ A₇) = (h.img E' hE'C).subgroupOf (Tp ⊓ A₇)) → E = E' := by
    intro E E' hEC hE'C hET hE'T hERd hE'Rd hchE hchE' heq
    have h1 := Subgroup.subgroupOf_inj.1 heq
    rw [inf_eq_left.2 (h.img_le_Pbar hEC hERd), inf_eq_left.2 (h.img_le_Pbar hE'C hE'Rd)] at h1
    ext t
    constructor
    · intro ht
      rw [hchE' t (hET ht), ← h1]
      exact (h.mem_img hEC).2 ⟨t, ht, rfl⟩
    · intro ht
      rw [hchE t (hE'T ht), h1]
      exact (h.mem_img hE'C).2 ⟨t, ht, rfl⟩
  rcases Dihedral.four_subgroups_pigeon_of_equiv h.sp.eB (Or.inr rfl) hEA₁ hcard₁ hEA₂ hcard₂
    hEA₃ hcard₃ with h12 | h13 | h23
  · exact Or.inl (key E₁ E₂ hC₁ hC₂ hT₁ hT₂ (hRd E₁ hT₁ h₁) (hRd E₂ hT₂ h₂) hch₁ hch₂ h12)
  · exact Or.inr (Or.inl (key E₁ E₃ hC₁ hC₃ hT₁ hT₃ (hRd E₁ hT₁ h₁) (hRd E₃ hT₃ h₃) hch₁ hch₃ h13))
  · exact Or.inr (Or.inr (key E₂ E₃ hC₂ hC₃ hT₂ hT₃ (hRd E₂ hT₂ h₂) (hRd E₃ hT₃ h₃) hch₂ hch₃ h23))

theorem comm_rho_one (h : Abs C T P Q Rd ρ Tp f) {w b : G} (hwT : w ∈ T) (hbT : b ∈ T)
    (hwf : ρ w ∈ zpowers f) (hbA : ρ b ∈ Tp ⊓ A₇) : ρ (w * b * w⁻¹ * b⁻¹) = 1 := by
  have hwC := h.T_le_C hwT
  have hbC := h.T_le_C hbT
  have hc : ρ b * ρ w = ρ w * ρ b := h.sp.comm_zpowers _ hbA _ hwf
  rw [h.rho_mul (w * b * w⁻¹) (mul_mem (mul_mem hwC hbC) (inv_mem hwC)) b⁻¹ (inv_mem hbC),
    h.rho_mul (w * b) (mul_mem hwC hbC) w⁻¹ (inv_mem hwC), h.rho_mul w hwC b hbC,
    h.rho_inv w hwC, h.rho_inv b hbC, ← hc]
  group

theorem comm_P (h : Abs C T P Q Rd ρ Tp f) {w p : G} (hwT : w ∈ T) (hwf : ρ w ∈ zpowers f)
    (hp : p ∈ P) : w * p = p * w := by
  have hmem : w * p * w⁻¹ * p⁻¹ ∈ P := P.mul_mem (h.P_normal w hwT p hp) (P.inv_mem hp)
  have h1 := h.comm_rho_one hwT (h.P_le_T hp) hwf (h.rho_mem_Pbar hp)
  have h2 : w * p * w⁻¹ * p⁻¹ = 1 := h.P_inj _ hmem 1 P.one_mem (by rw [h1, h.rho_one])
  calc w * p = (w * p * w⁻¹ * p⁻¹) * (p * w) := by group
    _ = p * w := by rw [h2, one_mul]

theorem cent_Rd_mem (h : Abs C T P Q Rd ρ Tp f) {x z : G} (hz : HZ T P z) (hQ : Q = zpowers x)
    (hxC : ∀ c ∈ C, c * x = x * c) {u : G} (hu : u ∈ Rd) (hcent : ∀ p ∈ P, u * p = p * u) :
    u ∈ zpowers x ⊔ zpowers z := by
  have huPQ : u ∈ P ⊔ zpowers x := by rw [← hQ, ← h.Rd_eq]; exact hu
  have hcomm : ∀ a ∈ P, ∀ b ∈ zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (show Commute a x from hxC a (h.P_le_C ha)) k).eq
  obtain ⟨p, hp, b, hb, rfl⟩ := (mem_sup_iff_of_comm hcomm).1 huPQ
  have hpc : ∀ q ∈ P, p * q = q * p := by
    intro q hq
    have h1 := hcent q hq
    have hbq : b * q = q * b := (hcomm q hq b hb).symm
    have : p * q * b = q * p * b := by
      calc p * q * b = p * (q * b) := by rw [mul_assoc]
        _ = p * (b * q) := by rw [hbq]
        _ = p * b * q := by rw [mul_assoc]
        _ = q * (p * b) := h1
        _ = q * p * b := by rw [mul_assoc]
    exact mul_right_cancel this
  have hb' : b ∈ zpowers x ⊔ zpowers z := mem_sup_left hb
  rcases h.central_eq hz hp hpc with h1 | h1
  · rw [h1, one_mul]; exact hb'
  · rw [h1]; exact mul_mem (mem_sup_right (mem_zpowers z)) hb'

theorem T_normal (h : Abs C T P Q Rd ρ Tp f) {x z : G} (hz : HZ T P z) (hQ : Q = zpowers x)
    (hΩ : omega1 T ≤ Rd) (hx : x * x = 1) (hxT : x ∈ T) (hxC : ∀ c ∈ C, c * x = x * c) :
    (∀ E E' : Subgroup G, E ≤ Rd → E' ≤ Rd → IsElemAb2 E → IsElemAb2 E' → Nat.card E = 8 →
      Nat.card E' = 8 → ∃ t ∈ T, E' = Hconj t E) ∨
    ∃ F' : Subgroup G, F' ≤ T ∧ zpowers x ≤ F' ∧ IsCyclic ↥F' ∧ F' ⊓ Rd = zpowers x ∧
      Rd ⊔ F' = T ∧
      (∀ w ∈ F', w ^ 4 = 1 → (∀ p ∈ P, w * p = p * w) ∧
        ∀ b ∈ Rd, w * b * w⁻¹ * b⁻¹ ∈ zpowers x ⊔ zpowers z) ∧
      (Nat.card P = 4 → F' = zpowers x) ∧
      (8 ≤ Nat.card P → ∀ t ∈ T, (∀ p ∈ P, t * p = p * t) →
        ∃ u ∈ zpowers x ⊔ zpowers z, ∃ w ∈ F', w ^ 4 = 1 ∧ t = u * w) := by
  right
  have hxQ : x ∈ Q := by rw [hQ]; exact mem_zpowers x
  have hρx : ρ x = 1 := h.rho_Q hxQ
  have hx_Rd : x ∈ Rd := h.Q_le_Rd hxQ
  have hP8 : Nat.card P = 8 := h.card_P
  have hnot4 : ¬ Nat.card P = 4 := by rw [hP8]; norm_num
  by_cases hcase : ∀ t ∈ T, ρ t ∈ A₇
  ·
    have hRdT : Rd = T := le_antisymm h.Rd_le_T (fun t ht => (h.mem_Rd t).2 ⟨ht, hcase t ht⟩)
    refine ⟨zpowers x, zpowers_le.2 hxT, le_rfl, inferInstance, ?_, ?_, ?_,
      fun h4 => absurd h4 hnot4, ?_⟩
    · exact inf_eq_left.2 (zpowers_le.2 hx_Rd)
    · rw [hRdT]; exact sup_eq_left.2 (zpowers_le.2 hxT)
    · intro w hw _
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
      refine ⟨fun p hp => ?_, fun b hb => ?_⟩
      · exact (Commute.zpow_right (show Commute p x from hxC p (h.P_le_C hp)) k).eq.symm
      · have hbC := h.T_le_C (h.Rd_le_T hb)
        have hcomm : x ^ k * b = b * x ^ k :=
          (Commute.zpow_right (show Commute b x from hxC b hbC) k).eq.symm
        have : x ^ k * b * (x ^ k)⁻¹ * b⁻¹ = 1 := by rw [hcomm]; group
        rw [this]; exact one_mem _
    · intro _ t ht hcent
      have htRd : t ∈ Rd := by rw [hRdT]; exact ht
      exact ⟨t, h.cent_Rd_mem hz hQ hxC htRd hcent, 1, one_mem _, one_pow _, (mul_one t).symm⟩
  ·
    push Not at hcase
    obtain ⟨t₀, ht₀T, ht₀A⟩ := hcase
    obtain ⟨pb, hpb, hcases⟩ := h.sp.mem_cases (h.rho_T t₀ ht₀T)
    have hρt₀ : ρ t₀ = pb * f := by
      rcases hcases with h1 | h1
      · exact absurd (by rw [h1]; exact hpb.2) ht₀A
      · exact h1
    obtain ⟨p₁, hp₁P, hp₁⟩ := (h.rho_P pb).1 hpb
    have hp₁T := h.P_le_T hp₁P
    have hp₁C := h.T_le_C hp₁T
    have hft : ∃ ft ∈ T, ρ ft = f := by
      refine ⟨p₁⁻¹ * t₀, T.mul_mem (T.inv_mem hp₁T) ht₀T, ?_⟩
      rw [h.rho_mul p₁⁻¹ (inv_mem hp₁C) t₀ (h.T_le_C ht₀T), h.rho_inv p₁ hp₁C, hp₁, hρt₀]
      group
    obtain ⟨ft, hftT, hρft⟩ := hft
    have hftC := h.T_le_C hftT
    have hfsq : ft * ft ∈ Q := (h.mem_Q _).2 ⟨T.mul_mem hftT hftT, by
      rw [h.rho_mul ft hftC ft hftC, hρft, h.sp.f_sq]⟩
    have hftx : ft * ft = x := by
      have hfsq' : ft * ft ∈ zpowers x := by rw [← hQ]; exact hfsq
      rcases zpowers_cases hx hfsq' with h1 | h1
      · exfalso
        have hmem : ft ∈ omega1 T := Subgroup.subset_closure ⟨hftT, h1⟩
        have := ((h.mem_Rd ft).1 (hΩ hmem)).2
        rw [hρft] at this
        exact h.sp.f_not_mem_A this
      · exact h1
    have hxft : x ∈ zpowers ft := by
      rw [← hftx]; exact mul_mem (mem_zpowers ft) (mem_zpowers ft)
    have hft4 : ft ^ (4 : ℤ) = 1 := by
      have : ft ^ (4 : ℤ) = ft ^ (2 : ℤ) * ft ^ (2 : ℤ) := by rw [← zpow_add]; norm_num
      rw [this, zpow_two, hftx, hx]
    have hft4' : ft ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, hftx, hx]
    have hcases4 : ∀ w ∈ zpowers ft, w = 1 ∨ w = x ∨ w = ft ∨ w = ft * x := by
      intro w hw
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
      have hk : ft ^ k = ft ^ (k % 4) := by
        conv_lhs => rw [← Int.mul_ediv_add_emod k 4]
        rw [zpow_add, zpow_mul, hft4, one_zpow, one_mul]
      rw [hk]
      have hk4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
      rcases hk4 with h0 | h0 | h0 | h0 <;> rw [h0]
      · left; exact zpow_zero _
      · right; right; left; exact zpow_one _
      · right; left; rw [zpow_two, hftx]
      · right; right; right
        rw [show (3 : ℤ) = 1 + 2 by norm_num, zpow_add, zpow_one, zpow_two, hftx]
    have hρcases : ∀ w ∈ zpowers ft, ρ w = 1 ∨ ρ w = f := by
      intro w hw
      rcases hcases4 w hw with h1 | h1 | h1 | h1
      · left; rw [h1]; exact h.rho_one
      · left; rw [h1]; exact hρx
      · right; rw [h1]; exact hρft
      · right; rw [h1, h.rho_mul ft hftC x (h.T_le_C hxT), hρft, hρx, mul_one]
    have hwT : ∀ w ∈ zpowers ft, w ∈ T := fun w hw => (zpowers_le.2 hftT) hw
    have hwf : ∀ w ∈ zpowers ft, ρ w ∈ zpowers f := fun w hw => by
      rcases hρcases w hw with h1 | h1
      · rw [h1]; exact one_mem _
      · rw [h1]; exact mem_zpowers f
    have hdecomp : ∀ t ∈ T, t ∈ Rd ∨ t * ft⁻¹ ∈ Rd := by
      intro t ht
      by_cases htA : ρ t ∈ A₇
      · exact Or.inl ((h.mem_Rd t).2 ⟨ht, htA⟩)
      · right
        obtain ⟨pb₂, hpb₂, hc2⟩ := h.sp.mem_cases (h.rho_T t ht)
        have h2 : ρ t = pb₂ * f := by
          rcases hc2 with h1 | h1
          · exact absurd (by rw [h1]; exact hpb₂.2) htA
          · exact h1
        refine (h.mem_Rd _).2 ⟨T.mul_mem ht (T.inv_mem hftT), ?_⟩
        rw [h.rho_mul t (h.T_le_C ht) ft⁻¹ (inv_mem hftC), h.rho_inv ft hftC, hρft, h2]
        have : pb₂ * f * f⁻¹ = pb₂ := by group
        rw [this]; exact hpb₂.2
    refine ⟨zpowers ft, zpowers_le.2 hftT, zpowers_le.2 hxft, inferInstance, ?_, ?_, ?_,
      fun h4 => absurd h4 hnot4, ?_⟩
    · apply le_antisymm
      · rintro w ⟨hwF, hwRd⟩
        have hwA := ((h.mem_Rd w).1 hwRd).2
        rcases hcases4 w hwF with h1 | h1 | h1 | h1
        · rw [h1]; exact one_mem _
        · rw [h1]; exact mem_zpowers x
        · exfalso
          rw [h1, hρft] at hwA
          exact h.sp.f_not_mem_A hwA
        · exfalso
          rw [h1, h.rho_mul ft hftC x (h.T_le_C hxT), hρft, hρx, mul_one] at hwA
          exact h.sp.f_not_mem_A hwA
      · exact le_inf (zpowers_le.2 hxft) (zpowers_le.2 hx_Rd)
    · apply le_antisymm (sup_le h.Rd_le_T (zpowers_le.2 hftT))
      intro t ht
      rcases hdecomp t ht with h1 | h1
      · exact mem_sup_left h1
      · have : t = (t * ft⁻¹) * ft := by group
        rw [this]
        exact mul_mem (mem_sup_left h1) (mem_sup_right (mem_zpowers ft))
    · intro w hw _
      have hwT' := hwT w hw
      have hwf' := hwf w hw
      refine ⟨fun p hp => h.comm_P hwT' hwf' hp, fun b hb => ?_⟩
      have hbT := h.Rd_le_T hb
      have hbA : ρ b ∈ Tp ⊓ A₇ := ⟨h.rho_T b hbT, ((h.mem_Rd b).1 hb).2⟩
      have hcomm := h.comm_rho_one hwT' hbT hwf' hbA
      have hQmem : w * b * w⁻¹ * b⁻¹ ∈ Q := (h.mem_Q _).2
        ⟨T.mul_mem (T.mul_mem (T.mul_mem hwT' hbT) (T.inv_mem hwT')) (T.inv_mem hbT), hcomm⟩
      rw [hQ] at hQmem
      exact mem_sup_left hQmem
    · intro _ t ht hcent
      rcases hdecomp t ht with h1 | h1
      · exact ⟨t, h.cent_Rd_mem hz hQ hxC h1 hcent, 1, one_mem _, one_pow _, (mul_one t).symm⟩
      · have hcentF : ∀ p ∈ P, (t * ft⁻¹) * p = p * (t * ft⁻¹) := by
          intro p hp
          have hftp : ft * p = p * ft := h.comm_P hftT (by rw [hρft]; exact mem_zpowers f) hp
          have hftp' : ft⁻¹ * p = p * ft⁻¹ := (Commute.inv_left (show Commute ft p from hftp)).eq
          calc t * ft⁻¹ * p = t * (ft⁻¹ * p) := by rw [mul_assoc]
            _ = t * (p * ft⁻¹) := by rw [hftp']
            _ = (t * p) * ft⁻¹ := by rw [mul_assoc]
            _ = (p * t) * ft⁻¹ := by rw [hcent p hp]
            _ = p * (t * ft⁻¹) := by rw [mul_assoc]
        exact ⟨t * ft⁻¹, h.cent_Rd_mem hz hQ hxC h1 hcentF, ft, mem_zpowers ft, hft4', by group⟩

end Abs

end CFSG.GH74.GLS.Stage1.Thm6.Glue.A7
