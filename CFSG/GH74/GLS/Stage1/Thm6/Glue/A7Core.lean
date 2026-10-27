module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.Dihedral
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Setting
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue.A7

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

local notation "S₇" => Equiv.Perm (Fin 7)
local notation "A₇" => alternatingGroup (Fin 7)

section Generic

variable {G : Type*} [Group G]

theorem mem_sup_iff_of_comm {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G} :
    g ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  constructor
  · intro hg
    let S : Subgroup G :=
      { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
        one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
          refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
          calc a * b * (a' * b') = a * (b * a') * b' := by simp only [mul_assoc]
            _ = a * (a' * b) * b' := by rw [← h a' ha' b hb]
            _ = a * a' * (b * b') := by simp only [mul_assoc]
        inv_mem' := by
          rintro _ ⟨a, ha, b, hb, rfl⟩
          refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
          rw [mul_inv_rev]
          have : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := by
            have := h a ha b hb
            calc b⁻¹ * a⁻¹ = (a * b)⁻¹ := by rw [mul_inv_rev]
              _ = (b * a)⁻¹ := by rw [this]
              _ = a⁻¹ * b⁻¹ := by rw [mul_inv_rev]
          exact this }
    have hAS : A ≤ S := fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩
    have hBS : B ≤ S := fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩
    exact (sup_le hAS hBS) hg
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)

theorem zpowers_cases {a w : G} (ha : a * a = 1) (hw : w ∈ Subgroup.zpowers a) :
    w = 1 ∨ w = a := by
  obtain ⟨k, hk⟩ := hw
  have hk' : a ^ k = w := hk
  have ha2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ha
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [← hk', zpow_mul, ha2, one_zpow]
  · right
    rw [← hk', zpow_add, zpow_mul, ha2, one_zpow, one_mul, zpow_one]

theorem isEA_subgroupOf {H V : Subgroup G} (hV : IsElemAb2 V) : Dihedral.IsEA (V.subgroupOf H) := by
  intro a ha
  have ha' : (a : G) ∈ V := ha
  refine ⟨Subtype.ext ((hV _ ha').1), fun b hb => Subtype.ext ((hV _ ha').2 _ hb)⟩

theorem card_subgroupOf {H V : Subgroup G} (hVH : V ≤ H) :
    Nat.card (V.subgroupOf H) = Nat.card V :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv

theorem isFour_map_subtype {H : Subgroup G} {V₀ : Subgroup ↥H} (hV : Dihedral.IsEA V₀)
    (hc : Nat.card V₀ = 4) : IsFour (V₀.map H.subtype) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨?_, ?_⟩
    · have := congrArg Subtype.val (hV a ha).1
      simpa using this
    · rintro _ ⟨b, hb, rfl⟩
      have := congrArg Subtype.val ((hV a ha).2 b hb)
      simpa using this
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hc

end Generic

theorem D4_cent_cases : ∀ (g : DihedralGroup 4) (i : ZMod 4),
    g * DihedralGroup.r 2 = DihedralGroup.r 2 * g → g * DihedralGroup.sr i = DihedralGroup.sr i * g →
      g = 1 ∨ g = DihedralGroup.r 2 ∨ g = DihedralGroup.sr i ∨
        g = DihedralGroup.sr i * DihedralGroup.r 2 := by decide

theorem cent_four_of_equiv {Y : Type*} [Group Y] (e : Y ≃* DihedralGroup 4) {V : Subgroup Y}
    (hV : Dihedral.IsEA V) (hc : Nat.card V = 4) {d : Y} (hd : ∀ v ∈ V, d * v = v * d) :
    d ∈ V := by
  have hVe := Dihedral.isEA_map hV e
  have hce : Nat.card (V.map e.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective e.injective]; exact hc
  have hz := Dihedral.z₀_mem_four (by norm_num : 2 ∣ 4) hVe hce
  obtain ⟨i, hi⟩ := Dihedral.exists_refl_mem_four (by norm_num : 2 ∣ 4) hVe hce
  have hcomm : ∀ w ∈ V.map e.toMonoidHom, e d * w = w * e d := by
    rintro _ ⟨v, hv, rfl⟩
    have := congrArg e (hd v hv)
    simpa using this
  have h2 : Dihedral.z₀ 4 = DihedralGroup.r 2 := by decide
  rw [h2] at hz
  have hcases := D4_cent_cases (e d) i (hcomm _ hz) (hcomm _ hi)
  have hmem : e d ∈ V.map e.toMonoidHom := by
    rcases hcases with h1 | h1 | h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact hz
    · rw [h1]; exact hi
    · rw [h1]; exact mul_mem hi hz
  obtain ⟨v, hv, hve⟩ := hmem
  have : v = d := e.injective hve
  rw [← this]; exact hv

structure SylowSplit (Tp : Subgroup S₇) (f : S₇) : Prop where
  f_sq : f * f = 1
  f_ne : f ≠ 1
  f_mem : f ∈ Tp
  inf_bot : Tp ⊓ A₇ ⊓ zpowers f = ⊥
  comm : ∀ a ∈ Tp ⊓ A₇, a * f = f * a
  sup_eq : Tp ⊓ A₇ ⊔ zpowers f = Tp
  dih : Nonempty (↥(Tp ⊓ A₇) ≃* DihedralGroup 4)

namespace SylowSplit

variable {Tp : Subgroup S₇} {f : S₇}

theorem f_not_mem_A (h : SylowSplit Tp f) : f ∉ A₇ := by
  intro hA
  have : f ∈ Tp ⊓ A₇ ⊓ zpowers f := ⟨⟨h.f_mem, hA⟩, mem_zpowers f⟩
  rw [h.inf_bot, mem_bot] at this
  exact h.f_ne this

theorem comm_zpowers (h : SylowSplit Tp f) : ∀ a ∈ Tp ⊓ A₇, ∀ b ∈ zpowers f, a * b = b * a := by
  intro a ha b hb
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
  exact (Commute.zpow_right (show Commute a f from h.comm a ha) k).eq

theorem mem_cases (h : SylowSplit Tp f) {a : S₇} (ha : a ∈ Tp) :
    ∃ p ∈ Tp ⊓ A₇, a = p ∨ a = p * f := by
  rw [← h.sup_eq, mem_sup_iff_of_comm h.comm_zpowers] at ha
  obtain ⟨p, hp, b, hb, rfl⟩ := ha
  refine ⟨p, hp, ?_⟩
  rcases zpowers_cases h.f_sq hb with h1 | h1
  · left; rw [h1, mul_one]
  · right; rw [h1]

noncomputable def eB (h : SylowSplit Tp f) : ↥(Tp ⊓ A₇) ≃* DihedralGroup 4 := Classical.choice h.dih

theorem central_sq (h : SylowSplit Tp f) {p : S₇} (hp : p ∈ Tp ⊓ A₇)
    (hpc : ∀ a ∈ Tp ⊓ A₇, p * a = a * p) : p * p = 1 := by
  have := Dihedral.central_sq_of_equiv h.eB (by norm_num : 2 ∣ 4) (z := ⟨p, hp⟩)
    (fun y => Subtype.ext (hpc y y.2))
  simpa using congrArg Subtype.val this

end SylowSplit

variable {G : Type*} [Group G]

structure Abs (C T P Q Rd : Subgroup G) (ρ : G → S₇) (Tp : Subgroup S₇) (f : S₇) : Prop where
  sp : SylowSplit Tp f
  T_le_C : T ≤ C
  rho_mul : ∀ g ∈ C, ∀ h ∈ C, ρ (g * h) = ρ g * ρ h
  rho_one : ρ 1 = 1
  rho_inv : ∀ g ∈ C, ρ g⁻¹ = (ρ g)⁻¹
  P_le_T : P ≤ T
  rho_T : ∀ g ∈ T, ρ g ∈ Tp
  rho_P : ∀ a : S₇, a ∈ Tp ⊓ A₇ ↔ ∃ g ∈ P, ρ g = a
  P_inj : ∀ p₁ ∈ P, ∀ p₂ ∈ P, ρ p₁ = ρ p₂ → p₁ = p₂
  P_normal : ∀ t ∈ T, ∀ p ∈ P, t * p * t⁻¹ ∈ P
  mem_Q : ∀ g, g ∈ Q ↔ g ∈ T ∧ ρ g = 1
  mem_Rd : ∀ g, g ∈ Rd ↔ g ∈ T ∧ ρ g ∈ A₇

namespace Abs

variable {C T P Q Rd : Subgroup G} {ρ : G → S₇} {Tp : Subgroup S₇} {f : S₇}

theorem P_le_C (h : Abs C T P Q Rd ρ Tp f) : P ≤ C := h.P_le_T.trans h.T_le_C

theorem Q_le_T (h : Abs C T P Q Rd ρ Tp f) : Q ≤ T := fun g hg => ((h.mem_Q g).1 hg).1

theorem Rd_le_T (h : Abs C T P Q Rd ρ Tp f) : Rd ≤ T := fun g hg => ((h.mem_Rd g).1 hg).1

theorem rho_mem_Pbar (h : Abs C T P Q Rd ρ Tp f) {p : G} (hp : p ∈ P) : ρ p ∈ Tp ⊓ A₇ :=
  (h.rho_P _).2 ⟨p, hp, rfl⟩

theorem rho_Q (h : Abs C T P Q Rd ρ Tp f) {q : G} (hq : q ∈ Q) : ρ q = 1 := ((h.mem_Q q).1 hq).2

theorem P_le_Rd (h : Abs C T P Q Rd ρ Tp f) : P ≤ Rd := fun p hp =>
  (h.mem_Rd p).2 ⟨h.P_le_T hp, (h.rho_mem_Pbar hp).2⟩

theorem Q_le_Rd (h : Abs C T P Q Rd ρ Tp f) : Q ≤ Rd := fun q hq =>
  (h.mem_Rd q).2 ⟨h.Q_le_T hq, by rw [h.rho_Q hq]; exact one_mem _⟩

theorem mem_PQ_of_even (h : Abs C T P Q Rd ρ Tp f) {g : G} (hg : g ∈ T) (hA : ρ g ∈ A₇) :
    g ∈ P ⊔ Q := by
  obtain ⟨p, hp, hpg⟩ := (h.rho_P _).1 ⟨h.rho_T g hg, hA⟩
  have hpT := h.P_le_T hp
  have hq : p⁻¹ * g ∈ Q := (h.mem_Q _).2 ⟨T.mul_mem (T.inv_mem hpT) hg, by
    rw [h.rho_mul p⁻¹ (inv_mem (h.T_le_C hpT)) g (h.T_le_C hg), h.rho_inv p (h.T_le_C hpT), hpg,
      inv_mul_cancel]⟩
  have : g = p * (p⁻¹ * g) := by group
  rw [this]
  exact mul_mem (mem_sup_left hp) (mem_sup_right hq)

theorem Rd_eq (h : Abs C T P Q Rd ρ Tp f) : Rd = P ⊔ Q :=
  le_antisymm (fun g hg => h.mem_PQ_of_even ((h.mem_Rd g).1 hg).1 ((h.mem_Rd g).1 hg).2)
    (sup_le h.P_le_Rd h.Q_le_Rd)

noncomputable def PHom (h : Abs C T P Q Rd ρ Tp f) : ↥P →* ↥(Tp ⊓ A₇) where
  toFun p := ⟨ρ p, h.rho_mem_Pbar p.2⟩
  map_one' := Subtype.ext h.rho_one
  map_mul' p q := Subtype.ext (h.rho_mul p (h.P_le_C p.2) q (h.P_le_C q.2))

noncomputable def PEquiv (h : Abs C T P Q Rd ρ Tp f) : ↥P ≃* ↥(Tp ⊓ A₇) :=
  MulEquiv.ofBijective h.PHom ⟨by
    intro a b hab
    apply Subtype.ext
    apply h.P_inj a.1 a.2 b.1 b.2
    exact congrArg Subtype.val hab, by
    rintro ⟨a, ha⟩
    obtain ⟨g, hg, hga⟩ := (h.rho_P a).1 ha
    exact ⟨⟨g, hg⟩, Subtype.ext hga⟩⟩

noncomputable def eP (h : Abs C T P Q Rd ρ Tp f) : ↥P ≃* DihedralGroup 4 :=
  h.PEquiv.trans h.sp.eB

theorem card_P (h : Abs C T P Q Rd ρ Tp f) : Nat.card P = 8 := by
  rw [Nat.card_congr h.eP.toEquiv, DihedralGroup.nat_card]

theorem central_eq (h : Abs C T P Q Rd ρ Tp f) {z : G} (hz : HZ T P z)
    {p : G} (hp : p ∈ P) (hpc : ∀ q ∈ P, p * q = q * p) : p = 1 ∨ p = z := by
  have hzP := hz.z_mem_P
  have hy2 : (⟨p, hp⟩ : ↥P) * ⟨p, hp⟩ = 1 :=
    Dihedral.central_sq_of_equiv h.eP (by norm_num : 2 ∣ 4) (z := ⟨p, hp⟩)
      (fun y => Subtype.ext (hpc y y.2))
  by_cases hp1 : p = 1
  · exact Or.inl hp1
  · right
    have hc : ∀ w : DihedralGroup 4, h.eP ⟨p, hp⟩ * w = w * h.eP ⟨p, hp⟩ := fun w => by
      have := congrArg h.eP (Subtype.ext (hpc _ (h.eP.symm w).2) :
        (⟨p, hp⟩ : ↥P) * h.eP.symm w = h.eP.symm w * ⟨p, hp⟩)
      simpa using this
    have hzc : ∀ w : DihedralGroup 4, h.eP ⟨z, hzP⟩ * w = w * h.eP ⟨z, hzP⟩ := fun w => by
      have := congrArg h.eP (Subtype.ext (hz.z_central _ (h.P_le_T (h.eP.symm w).2)) :
        (⟨z, hzP⟩ : ↥P) * h.eP.symm w = h.eP.symm w * ⟨z, hzP⟩)
      simpa using this
    have hzz : (⟨z, hzP⟩ : ↥P) * ⟨z, hzP⟩ = 1 := Subtype.ext hz.z_sq
    have e1 : h.eP ⟨p, hp⟩ = Dihedral.z₀ 4 := by
      refine Dihedral.eq_z₀_of_central (by norm_num : 2 ∣ 4) (by norm_num : 4 ≠ 2) ?_ ?_ hc
      · rw [← map_mul, hy2, map_one]
      · intro h1
        have h2 : (⟨p, hp⟩ : ↥P) = 1 := h.eP.injective (by rw [h1, map_one])
        exact hp1 (congrArg Subtype.val h2)
    have e2 : h.eP ⟨z, hzP⟩ = Dihedral.z₀ 4 := by
      refine Dihedral.eq_z₀_of_central (by norm_num : 2 ∣ 4) (by norm_num : 4 ≠ 2) ?_ ?_ hzc
      · rw [← map_mul, hzz, map_one]
      · intro h1
        have h2 : (⟨z, hzP⟩ : ↥P) = 1 := h.eP.injective (by rw [h1, map_one])
        exact hz.z_ne_one (congrArg Subtype.val h2)
    exact congrArg Subtype.val (h.eP.injective (e1.trans e2.symm))

theorem P_four (h : Abs C T P Q Rd ρ Tp f) : ∃ V : Subgroup G, V ≤ P ∧ IsFour V := by
  obtain ⟨V₀, hV₀, hc₀⟩ := Dihedral.exists_four_of_equiv h.eP (by norm_num : 2 ∣ 4)
    (by norm_num : 2 ≤ 4)
  exact ⟨V₀.map P.subtype, Subgroup.map_subtype_le _, isFour_map_subtype hV₀ hc₀⟩

theorem z_V (h : Abs C T P Q Rd ρ Tp f) {z : G} (hz : HZ T P z) :
    ∀ V : Subgroup G, V ≤ P → IsFour V → z ∈ V := by
  intro V hVP hV
  have hzP := hz.z_mem_P
  exact Dihedral.central_mem_four_of_equiv h.eP (by norm_num : 2 ∣ 4)
    (isEA_subgroupOf (H := P) hV.1) (by rw [card_subgroupOf hVP]; exact hV.2)
    (z := ⟨z, hzP⟩) (Subtype.ext hz.z_sq) (fun h1 => hz.z_ne_one (congrArg Subtype.val h1))
    (fun y => Subtype.ext (hz.z_central _ (h.P_le_T y.2)))

theorem cent_Rd (h : Abs C T P Q Rd ρ Tp f) :
    ∀ d ∈ Rd, (∀ p ∈ P, d * p = p * d) → d ∈ P ⊔ Q := fun d hd _ => by
  rw [← h.Rd_eq]; exact hd

theorem P_trans (h : Abs C T P Q Rd ρ Tp f) :
    ∀ u ∈ Rd, u ∉ P ⊔ Q → u * u = 1 → ∀ a ∈ P, ∀ b ∈ P, (a * u) * (a * u) = 1 →
      (b * u) * (b * u) = 1 → ∃ p ∈ P, p * (a * u) * p⁻¹ = b * u := fun u hu huPQ => by
  exact absurd (by rw [← h.Rd_eq]; exact hu) huPQ

theorem Rd_factor (h : Abs C T P Q Rd ρ Tp f) :
    ∃ B : Subgroup G, B ≤ T ∧ B ⊓ Rd = P ⊔ Q ∧ B ⊔ Rd = T :=
  ⟨T, le_rfl, by rw [inf_eq_right.2 h.Rd_le_T, h.Rd_eq], sup_eq_left.2 h.Rd_le_T⟩

theorem cent_P_exp (h : Abs C T P Q Rd ρ Tp f) :
    ∀ t ∈ T, (∀ p ∈ P, t * p = p * t) → t * t ∈ Q := by
  intro t ht hcent
  have htC := h.T_le_C ht
  obtain ⟨p, hp, hcase⟩ := h.sp.mem_cases (h.rho_T t ht)
  have hρcomm : ∀ q ∈ P, ρ t * ρ q = ρ q * ρ t := fun q hq => by
    rw [← h.rho_mul t htC q (h.P_le_C hq), ← h.rho_mul q (h.P_le_C hq) t htC, hcent q hq]
  have hpf : p * f = f * p := h.sp.comm p hp
  have hpc : ∀ a ∈ Tp ⊓ A₇, p * a = a * p := by
    intro a ha
    obtain ⟨q, hq, rfl⟩ := (h.rho_P a).1 ha
    have haf : ρ q * f = f * ρ q := h.sp.comm _ ha
    rcases hcase with h1 | h1
    · have := hρcomm q hq
      rwa [h1] at this
    · have h2 := hρcomm q hq
      rw [h1] at h2
      have h3 : p * ρ q * f = ρ q * p * f := by
        calc p * ρ q * f = p * (ρ q * f) := by rw [mul_assoc]
          _ = p * (f * ρ q) := by rw [haf]
          _ = p * f * ρ q := by rw [mul_assoc]
          _ = ρ q * (p * f) := h2
          _ = ρ q * p * f := by rw [mul_assoc]
      exact mul_right_cancel h3
  have hpp : p * p = 1 := h.sp.central_sq hp hpc
  have hsq : ρ t * ρ t = 1 := by
    rcases hcase with h1 | h1
    · rw [h1]; exact hpp
    · rw [h1]
      calc p * f * (p * f) = p * (f * p) * f := by simp only [mul_assoc]
        _ = p * (p * f) * f := by rw [hpf]
        _ = (p * p) * (f * f) := by simp only [mul_assoc]
        _ = 1 := by rw [hpp, h.sp.f_sq, mul_one]
  exact (h.mem_Q _).2 ⟨T.mul_mem ht ht, by rw [h.rho_mul t htC t htC]; exact hsq⟩

theorem Rd_cyclic (h : Abs C T P Q Rd ρ Tp f) :
    ∃ b ∈ T, ∀ t ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ Rd := by
  by_cases hex : ∃ b ∈ T, ρ b ∉ A₇
  · obtain ⟨b, hbT, hb⟩ := hex
    refine ⟨b, hbT, fun t ht => ?_⟩
    by_cases htA : ρ t ∈ A₇
    · exact ⟨0, by rw [zpow_zero, inv_one, one_mul]; exact (h.mem_Rd t).2 ⟨ht, htA⟩⟩
    · refine ⟨1, ?_⟩
      rw [zpow_one]
      refine (h.mem_Rd _).2 ⟨T.mul_mem (T.inv_mem hbT) ht, ?_⟩
      rw [h.rho_mul b⁻¹ (inv_mem (h.T_le_C hbT)) t (h.T_le_C ht), h.rho_inv b (h.T_le_C hbT)]
      rw [Equiv.Perm.mem_alternatingGroup] at hb htA ⊢
      have hb' : Equiv.Perm.sign (ρ b) = -1 := (Int.units_eq_one_or _).resolve_left hb
      have ht' : Equiv.Perm.sign (ρ t) = -1 := (Int.units_eq_one_or _).resolve_left htA
      simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, hb', ht']
  · push Not at hex
    refine ⟨1, one_mem _, fun t ht => ⟨0, ?_⟩⟩
    rw [zpow_zero, inv_one, one_mul]
    exact (h.mem_Rd t).2 ⟨ht, hex t ht⟩

theorem cent_four (h : Abs C T P Q Rd ρ Tp f) :
    ∀ V : Subgroup G, V ≤ P → IsFour V → ∃ W : Subgroup G, W ≤ T ∧ W ⊓ Rd = Q ∧
      (∀ v ∈ V, ∀ w ∈ W, v * w * v⁻¹ ∈ W) ∧
      ∀ d ∈ T, (∀ v ∈ V, d * v = v * d) → ∃ v ∈ V, ∃ w ∈ W, d = v * w := by
  intro V hVP hV
  let W : Subgroup G :=
    { carrier := {t | t ∈ T ∧ ρ t ∈ zpowers f}
      one_mem' := ⟨T.one_mem, by rw [h.rho_one]; exact one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, haf⟩ ⟨hb, hbf⟩
        exact ⟨T.mul_mem ha hb, by
          rw [h.rho_mul a (h.T_le_C ha) b (h.T_le_C hb)]; exact mul_mem haf hbf⟩
      inv_mem' := by
        rintro a ⟨ha, haf⟩
        exact ⟨T.inv_mem ha, by rw [h.rho_inv a (h.T_le_C ha)]; exact inv_mem haf⟩ }
  refine ⟨W, fun t ht => ht.1, ?_, ?_, ?_⟩
  ·
    ext g
    constructor
    · rintro ⟨⟨hgT, hgf⟩, hgRd⟩
      have hgA := ((h.mem_Rd g).1 hgRd).2
      have hmem : ρ g ∈ Tp ⊓ A₇ ⊓ zpowers f := ⟨⟨h.rho_T g hgT, hgA⟩, hgf⟩
      rw [h.sp.inf_bot, mem_bot] at hmem
      exact (h.mem_Q g).2 ⟨hgT, hmem⟩
    · intro hg
      refine ⟨⟨h.Q_le_T hg, by rw [h.rho_Q hg]; exact one_mem _⟩, h.Q_le_Rd hg⟩
  ·
    intro v hv w hw
    obtain ⟨hwT, hwf⟩ := hw
    have hvP := hVP hv
    have hvT := h.P_le_T hvP
    have hvC := h.T_le_C hvT
    have hwC := h.T_le_C hwT
    refine ⟨T.mul_mem (T.mul_mem hvT hwT) (T.inv_mem hvT), ?_⟩
    rw [h.rho_mul (v * w) (mul_mem hvC hwC) v⁻¹ (inv_mem hvC), h.rho_mul v hvC w hwC,
      h.rho_inv v hvC]
    have hc := h.sp.comm_zpowers _ (h.rho_mem_Pbar hvP) _ hwf
    rw [hc, mul_inv_cancel_right]
    exact hwf
  ·
    intro d hdT hcent
    have hdC := h.T_le_C hdT
    have hρd : ρ d ∈ Tp ⊓ A₇ ⊔ zpowers f := by rw [h.sp.sup_eq]; exact h.rho_T d hdT
    obtain ⟨p, hp, b, hb, hdb⟩ := (mem_sup_iff_of_comm h.sp.comm_zpowers).1 hρd
    obtain ⟨p₀, hp₀P, hp₀⟩ := (h.rho_P p).1 hp
    have hp₀T := h.P_le_T hp₀P
    have hp₀C := h.T_le_C hp₀T
    have hp₀V : ∀ v ∈ V, p₀ * v = v * p₀ := by
      intro v hv
      have hvP := hVP hv
      have hvC := h.T_le_C (h.P_le_T hvP)
      have hρv := h.rho_mem_Pbar hvP
      have hbc : ρ v * b = b * ρ v := h.sp.comm_zpowers _ hρv b hb
      have hdv : ρ d * ρ v = ρ v * ρ d := by
        rw [← h.rho_mul d hdC v hvC, ← h.rho_mul v hvC d hdC, hcent v hv]
      have hpv : p * ρ v = ρ v * p := by
        have hp' : p = ρ d * b⁻¹ := by rw [hdb]; group
        have hbc' : b⁻¹ * ρ v = ρ v * b⁻¹ :=
          (Commute.inv_right (show Commute (ρ v) b from hbc)).eq.symm
        rw [hp']
        calc ρ d * b⁻¹ * ρ v = ρ d * (b⁻¹ * ρ v) := by rw [mul_assoc]
          _ = ρ d * (ρ v * b⁻¹) := by rw [hbc']
          _ = (ρ d * ρ v) * b⁻¹ := by rw [mul_assoc]
          _ = (ρ v * ρ d) * b⁻¹ := by rw [hdv]
          _ = ρ v * (ρ d * b⁻¹) := by rw [mul_assoc]
      apply h.P_inj (p₀ * v) (P.mul_mem hp₀P hvP) (v * p₀) (P.mul_mem hvP hp₀P)
      rw [h.rho_mul p₀ hp₀C v hvC, h.rho_mul v hvC p₀ hp₀C, hp₀]
      exact hpv
    have hp₀mem : p₀ ∈ V := by
      have := cent_four_of_equiv h.eP (V := V.subgroupOf P) (isEA_subgroupOf (H := P) hV.1)
        (by rw [card_subgroupOf hVP]; exact hV.2) (d := ⟨p₀, hp₀P⟩) (fun v hv => by
          have hv' : (v : G) ∈ V := hv
          exact Subtype.ext (hp₀V v hv'))
      exact this
    refine ⟨p₀, hp₀mem, p₀⁻¹ * d, ⟨T.mul_mem (T.inv_mem hp₀T) hdT, ?_⟩, by group⟩
    rw [h.rho_mul p₀⁻¹ (inv_mem hp₀C) d hdC, h.rho_inv p₀ hp₀C, hp₀, hdb]
    have : p⁻¹ * (p * b) = b := by group
    rw [this]
    exact hb

end Abs

end CFSG.GH74.GLS.Stage1.Thm6.Glue.A7
