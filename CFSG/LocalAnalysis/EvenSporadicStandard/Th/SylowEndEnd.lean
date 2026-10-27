module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndRho
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndProj

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

omit [Finite G] in
theorem sq_eq_one_of_conj_eq_inv {v x : G} (h : v * x * v⁻¹ = x⁻¹) (hc : x * v = v * x) :
    x ^ 2 = 1 := by
  have h1 : v * x * v⁻¹ = x := by rw [← hc]; group
  have h3 : x = x⁻¹ := h1.symm.trans h
  calc x ^ 2 = x * x := sq x
    _ = x * x⁻¹ := by rw [← h3]
    _ = 1 := mul_inv_cancel x

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)

include H W W2

theorem ThCyc.exists_conj_b_mul_t : ∃ c : G, c⁻¹ * t * c = b * t := by
  obtain ⟨-, g, -, -, -, -, hgt⟩ := H.exists_fusing_z W
  have hbL : b ∈ L := W.B_le W2.b_mem
  have hzL : z ∈ L := W.S_le W.z_mem
  have hbo : orderOf (⟨b, hbL⟩ : L) = 2 := by
    refine orderOf_eq_prime (Subtype.ext (by simpa using W2.b_sq)) fun h => W2.b_not_mem ?_
    have : b = 1 := by simpa using congrArg Subtype.val h
    rw [this]
    exact Aa.one_mem
  have hzo : orderOf (⟨z, hzL⟩ : L) = 2 := by
    refine orderOf_eq_prime (Subtype.ext (by simpa using W.z_sq)) fun h => W.z_ne_one ?_
    simpa using congrArg Subtype.val h
  obtain ⟨c, hc⟩ := isConj_iff.1 (H.data.invConj _ _ hbo hzo)
  have hcb : (c : G) * b * (c : G)⁻¹ = z := by simpa using congrArg Subtype.val hc
  have hct : t * (c : G) = (c : G) * t := H.comm_of_mem_L c.2
  have h1 : (c : G)⁻¹ * z * c = b := by
    calc (c : G)⁻¹ * z * c = (c : G)⁻¹ * ((c : G) * b * (c : G)⁻¹) * c := by rw [hcb]
      _ = b := by group
  have h2 : (c : G)⁻¹ * t * c = t := by
    calc (c : G)⁻¹ * t * c = (c : G)⁻¹ * (t * c) := by group
      _ = (c : G)⁻¹ * (c * t) := by rw [hct]
      _ = t := by group
  refine ⟨g⁻¹ * c, ?_⟩
  calc (g⁻¹ * (c : G))⁻¹ * t * (g⁻¹ * c) = (c : G)⁻¹ * (g * t * g⁻¹) * c := by group
    _ = (c : G)⁻¹ * (z * t) * c := by rw [hgt]
    _ = ((c : G)⁻¹ * z * c) * ((c : G)⁻¹ * t * c) := by group
    _ = b * t := by rw [h1, h2]

variable (hD : DHyp A Aa t D)

include hD

theorem ThCyc.D_sq_mem_A_of_fourth (h : ∀ d ∈ D, d ^ 4 = 1) {d : G} (hd : d ∈ D) : d ^ 2 ∈ A := by
  refine W2.mem_A_of_sq_eq_one W (H.D_sq_mem_Aa W W2 hD hd) ?_
  rw [← pow_mul]
  exact h d hd

@[expose] def sqD (hsq : ∀ d ∈ D, d ^ 2 ∈ A) : ↥D →* ↥A :=
  MonoidHom.mk' (fun d => ⟨(d : G) ^ 2, hsq d d.2⟩) (fun d d' =>
    Subtype.ext (by
      show ((d : G) * d') ^ 2 = (d : G) ^ 2 * (d' : G) ^ 2
      exact (show Commute (d : G) d' from hD.comm _ d.2 _ d'.2).mul_pow 2))

theorem ThCyc.card_ker_sqD (hsq : ∀ d ∈ D, d ^ 2 ∈ A) :
    Nat.card (sqD hD hsq).ker = 2 ^ 8 := by
  set σ := sqD hD hsq with hσ
  have h1 := Subgroup.card_ker_mul_card_range σ
  have hrange : σ.range = ⊤ := by
    rw [eq_top_iff]
    intro a _
    obtain ⟨x, hx, hxa⟩ := (W2.A_eq_sq a).1 a.2
    exact ⟨⟨x, hD.Aa_le hx⟩, Subtype.ext hxa⟩
  rw [hrange, Subgroup.card_top, W.A_card, hD.card] at h1
  omega

theorem ThCyc.card_inf_centralizer_of_inverts (hsq : ∀ d ∈ D, d ^ 2 ∈ A) {v : G}
    (hv : ∀ d ∈ D, v * d * v⁻¹ = d⁻¹) :
    Nat.card ↥(D ⊓ centralizer ({v} : Set G)) = 2 ^ 8 := by
  have hiff : ∀ d ∈ D, d ∈ centralizer ({v} : Set G) ↔ d ^ 2 = 1 := by
    intro d hd
    have h3 := hv d hd
    rw [mem_centralizer_singleton_iff]
    constructor
    · exact sq_eq_one_of_conj_eq_inv h3
    · intro h4
      have h5 : d⁻¹ = d := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h4)
      calc d * v = (v * d * v⁻¹) * v := by rw [h3, h5]
        _ = v * d := by group
  have hker : (D ⊓ centralizer ({v} : Set G)).subgroupOf D = (sqD hD hsq).ker := by
    ext d
    rw [mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · rintro ⟨-, hd2⟩
      exact Subtype.ext ((hiff d d.2).1 hd2)
    · intro h
      exact ⟨d.2, (hiff d d.2).2 (congrArg (fun x : ↥A => (x : G)) h)⟩
  rw [← H.card_ker_sqD W W2 hD hsq, ← hker]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
    D ⊓ centralizer ({v} : Set G) ≤ D)).toEquiv).symm

theorem ThCyc.bt_inverts (h2 : ∀ d ∈ D, d * (b * d * b⁻¹) = theta t d) {d : G} (hd : d ∈ D) :
    (b * t) * d * (b * t)⁻¹ = d⁻¹ := by
  have hdBp := H.D_le_Bp W W2 hD hd
  have hθA : theta t d ∈ A := H.theta_mem_A W hdBp
  have hθ2 : theta t d * theta t d = 1 := by rw [← sq]; exact W.A_sq _ hθA
  have hθinv : (theta t d)⁻¹ = theta t d := inv_eq_of_mul_eq_one_right hθ2
  have e1 : t * d * t⁻¹ = (theta t d)⁻¹ * d := by
    simp only [theta]
    group
  have e2 : b * d * b⁻¹ = d⁻¹ * theta t d := by
    have := h2 d hd
    calc b * d * b⁻¹ = d⁻¹ * (d * (b * d * b⁻¹)) := by group
      _ = d⁻¹ * theta t d := by rw [this]
  have e3 : b * theta t d * b⁻¹ = theta t d := by
    rw [W2.b_inv _ (W2.A_le hθA), hθinv]
  have e4 : theta t d * d⁻¹ = d⁻¹ * theta t d :=
    (show Commute (theta t d) d from mem_centralizer_iff.1 hdBp.1 _ hθA).inv_right.eq
  calc (b * t) * d * (b * t)⁻¹ = b * (t * d * t⁻¹) * b⁻¹ := by group
    _ = b * ((theta t d)⁻¹ * d) * b⁻¹ := by rw [e1]
    _ = (b * (theta t d)⁻¹ * b⁻¹) * (b * d * b⁻¹) := by group
    _ = theta t d * (d⁻¹ * theta t d) := by rw [hθinv, e3, e2]
    _ = theta t d * (theta t d * d⁻¹) := by rw [← e4]
    _ = (theta t d * theta t d) * d⁻¹ := by group
    _ = d⁻¹ := by rw [hθ2, one_mul]

theorem ThCyc.D_trichotomy :
    (∀ d ∈ D, d ^ 4 = theta t d) ∨
      ((∀ d ∈ D, d ^ 4 = 1) ∧ ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) ∨
      ((∀ d ∈ D, d ^ 4 = 1) ∧ ∀ d ∈ D, (b * t) * d * (b * t)⁻¹ = d⁻¹) := by
  rcases H.D_fourth_dichotomy W W2 hD with h4 | h4
  · right
    rcases H.D_rho_dichotomy W W2 hD with h1 | h2
    · exact Or.inl ⟨h4, fun d hd => eq_inv_of_mul_eq_one_right (h1 d hd)⟩
    · exact Or.inr ⟨h4, fun d hd => H.bt_inverts W W2 hD h2 hd⟩
  · exact Or.inl h4

theorem ThCyc.inf_centralizer_b_eq_A (h4 : ∀ d ∈ D, d ^ 4 = theta t d) :
    D ⊓ centralizer ({b} : Set G) = A := by
  have hb2 : ∀ x ∈ A, b * x * b⁻¹ = x := fun x hx => by
    have h1 := W2.b_inv x (W2.A_le hx)
    have h2 : x * x = 1 := by rw [← sq]; exact W.A_sq _ hx
    rw [h1]
    exact inv_eq_of_mul_eq_one_right h2
  ext x
  constructor
  · rintro ⟨hx, hxc⟩
    have hxb : x * b = b * x := mem_centralizer_singleton_iff.1 hxc
    have hbx : b * x * b⁻¹ = x := by rw [← hxb]; group
    have h1 : x ^ 2 ∈ A := by
      have := H.D_rho_mem_A W W2 hD hx
      rwa [hbx, ← sq] at this
    have h2 : x ^ 4 = 1 := by
      have h3 := W.A_sq _ h1
      rw [← pow_mul] at h3
      exact h3
    have h5 : x ∈ Aa := (H.D_theta_eq_one_iff W W2 hD hx).1 (by rw [← h4 x hx]; exact h2)
    have h6 : x ^ 2 = 1 := sq_eq_one_of_conj_eq_inv (W2.b_inv x h5) hxb
    exact W2.mem_A_of_sq_eq_one W h5 h6
  · intro hx
    refine ⟨hD.Aa_le (W2.A_le hx), mem_centralizer_singleton_iff.2 ?_⟩
    have := hb2 x hx
    calc x * b = (b * x * b⁻¹) * b := by rw [this]
      _ = b * x := by group

theorem ThCyc.not_bt_inverts_D
    (hEl : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → (∀ y ∈ Y, y ^ 2 = 1) → Nat.card Y ≤ 2 ^ 7)
    (hsq : ∀ d ∈ D, d ^ 2 ∈ A) : ¬ ∀ d ∈ D, (b * t) * d * (b * t)⁻¹ = d⁻¹ := by
  intro hinv
  obtain ⟨c, hc⟩ := H.exists_conj_b_mul_t W W2
  have hcard := H.card_inf_centralizer_of_inverts W W2 hD hsq hinv
  have hbtD : b * t ∉ D := fun h => H.t_not_mem_sup W W2 hD (by
    have : t = b⁻¹ * (b * t) := by group
    rw [this]
    exact mul_mem (mem_sup_right (S.inv_mem (W.B_le_S W2.b_mem))) (mem_sup_left h))
  have hle : D ⊓ centralizer ({b * t} : Set G) ≤ centralizer ({c⁻¹ * t * c} : Set G) := by
    rw [hc]
    exact inf_le_right
  have hvE : c⁻¹ * t * c ∉ D ⊓ centralizer ({b * t} : Set G) := by
    rw [hc]
    exact fun h => hbtD h.1
  have := H.card_lt_of_elementary hEl hle (fun x hx y hy => hD.comm x hx.1 y hy.1)
    (fun x hx => sq_eq_one_of_conj_eq_inv (hinv x hx.1) (mem_centralizer_singleton_iff.1 hx.2))
    hvE
  omega

theorem ThCyc.false_of_card_eq
    (hEl : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → (∀ y ∈ Y, y ^ 2 = 1) → Nat.card Y ≤ 2 ^ 7)
    {g : G} (hle : D ⊓ centralizer ({b} : Set G) ≤ centralizer ({g⁻¹ * t * g} : Set G))
    (hu : g⁻¹ * t * g ∉ D) (hcard8 : Nat.card ↥(D ⊓ centralizer ({b} : Set G)) = 2 ^ 8) :
    False := by
  rcases H.D_trichotomy W W2 hD with h4 | ⟨h4, hinv⟩ | ⟨h4, hinv⟩
  · have h := H.inf_centralizer_b_eq_A W W2 hD h4
    rw [h, W.A_card] at hcard8
    norm_num at hcard8
  · have := H.card_lt_of_elementary hEl hle (fun x hx y hy => hD.comm x hx.1 y hy.1)
      (fun x hx => sq_eq_one_of_conj_eq_inv (hinv x hx.1) (mem_centralizer_singleton_iff.1 hx.2))
      (fun h => hu h.1)
    omega
  · exact H.not_bt_inverts_D W W2 hD hEl (fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd) hinv

end

end CFSG.EvenSporadicStandard.ThStd
