module

public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.SecTwoSetup

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open
open scoped Pointwise

variable {X : Type*} [Group X] {t u : X} {h : SecTwoHyp X t u} {Q : Subgroup X}

theorem SecTwoHyp.conj_z (h : SecTwoHyp X t u) : t * u ^ 2 * t⁻¹ = u ^ 2 := by
  rw [(h.commute_tu.pow_right 2).eq, mul_assoc, mul_inv_cancel, mul_one]

theorem SecTwoHyp.card_R_le (h : SecTwoHyp X t u) : Nat.card (secTwoR t u) ≤ 8 := by
  let f : Fin 2 × Fin 4 → secTwoR t u := fun p =>
    ⟨t ^ p.1.val * u ^ p.2.val, mul_mem (pow_mem SecTwoHyp.t_mem_R _)
      (pow_mem SecTwoHyp.u_mem_R _)⟩
  have hf : Function.Surjective f := by
    rintro ⟨r, hr⟩
    obtain ⟨a, b, rfl⟩ := h.exists_pow_of_mem_R hr
    refine ⟨(⟨a % 2, Nat.mod_lt _ (by norm_num)⟩, ⟨b % 4, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    apply Subtype.ext
    change t ^ (a % 2) * u ^ (b % 4) = t ^ a * u ^ b
    rw [← h.orderOf_t, ← h.orderOf_u, pow_mod_orderOf, pow_mod_orderOf]
  calc Nat.card (secTwoR t u) ≤ Nat.card (Fin 2 × Fin 4) := Nat.card_le_card_of_surjective f hf
    _ = 8 := by simp

namespace SecTwoCData

variable (d : SecTwoCData h Q)

theorem isPGroup_W : IsPGroup 2 (secTwoOmegaZ Q) :=
  SecTwoHyp.isPGroup_of_sq_eq_one fun _ ha => secTwoOmegaZ_sq ha

theorem htw_ne : t * d.w * t⁻¹ ≠ d.w := by
  rw [d.htw]
  intro h1
  apply h.z_ne_one
  calc u ^ 2 = d.w⁻¹ * (d.w * u ^ 2) := by group
    _ = 1 := by rw [h1, inv_mul_cancel]

theorem fix_x [Finite X] (hQn : Q.Normal) (hQ2 : IsPGroup 2 Q) :
    ∀ q ∈ Q, d.x * q * d.x⁻¹ = q → q = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup X := Q ⊓ centralizer ({d.x} : Set X)
  have hK2 : IsPGroup 2 K := hQ2.to_inf_left
  have htxinv : t * d.x⁻¹ * t⁻¹ = d.x := by
    rw [show t * d.x⁻¹ * t⁻¹ = (t * d.x * t⁻¹)⁻¹ by group, d.htx, inv_inv]
  have htK : t ∈ normalizer (K : Set X) := by
    rw [mem_normalizer_iff]
    intro k
    have key : ∀ k : X, k ∈ K → t * k * t⁻¹ ∈ K := by
      intro k hk
      refine Subgroup.mem_inf.mpr ⟨hQn.conj_mem k hk.1 t, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have hk' := mem_centralizer_singleton_iff.mp hk.2
      have hkinv : k * d.x⁻¹ = d.x⁻¹ * k := by
        calc k * d.x⁻¹ = d.x⁻¹ * (d.x * k) * d.x⁻¹ := by group
          _ = d.x⁻¹ * (k * d.x) * d.x⁻¹ := by rw [hk']
          _ = d.x⁻¹ * k := by group
      calc t * k * t⁻¹ * d.x = t * k * (t⁻¹ * d.x * t) * t⁻¹ := by group
        _ = t * k * d.x⁻¹ * t⁻¹ := by
          rw [show t⁻¹ * d.x * t = d.x⁻¹ by
            rw [h.t_inv]; rw [h.t_inv] at htxinv
            calc t * d.x * t = t * (t * d.x⁻¹ * t) * t := by rw [htxinv]
              _ = (t * t) * d.x⁻¹ * (t * t) := by group
              _ = d.x⁻¹ := by rw [h.t_mul_t]; group]
        _ = t * d.x⁻¹ * k * t⁻¹ := by rw [mul_assoc t k, hkinv, ← mul_assoc]
        _ = (t * d.x⁻¹ * t⁻¹) * (t * k * t⁻¹) := by group
        _ = d.x * (t * k * t⁻¹) := by rw [htxinv]
    constructor
    · exact key k
    · intro hk
      have := key _ hk
      rw [h.t_inv, show t * (t * k * t) * t = (t * t) * k * (t * t) by group, h.t_mul_t] at this
      simpa using this
  have ht2 : IsPGroup 2 (zpowers t) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, h.orderOf_t]; exact ⟨1, rfl⟩
  by_contra hne
  push Not at hne
  obtain ⟨q, hqQ, hqx, hq1⟩ := hne
  have hKne : K ≠ ⊥ := by
    intro hK
    apply hq1
    have : q ∈ K := ⟨hqQ, mem_centralizer_singleton_iff.mpr (by
      calc q * d.x = d.x * q * d.x⁻¹ * d.x := by rw [hqx]
        _ = d.x * q := by group)⟩
    rw [hK] at this
    exact this
  obtain ⟨c, hcK, hc1, htc⟩ := secTwo_exists_fixed_of_two hK2 hKne ht2 htK
  have hct : c * t = t * c := by
    calc c * t = t * c * t⁻¹ * t := by rw [htc]
      _ = t * c := by group
  have hcx : c * d.x = d.x * c := mem_centralizer_singleton_iff.mp hcK.2
  have hzx : d.x * u ^ 2 * d.x⁻¹ = u ^ 2 := by
    have hsq : c ^ 2 = u ^ 2 ∨ c = u ^ 2 := by
      rcases d.hCQt c hcK.1 hct with h1 | h1 | h1 | h1
      · exact absurd h1 hc1
      · left; rw [h1, d.hvsq]
      · right; exact h1
      · left
        have hvz : d.v * u ^ 2 = u ^ 2 * d.v :=
          h.mul_comm_of_mem_R d.hvR (pow_mem SecTwoHyp.u_mem_R 2)
        rw [h1, (Commute.mul_pow hvz 2 : (d.v * u ^ 2) ^ 2 = d.v ^ 2 * (u ^ 2) ^ 2), d.hvsq,
          h.z_sq, mul_one]
    have hcxc : d.x * c * d.x⁻¹ = c := by rw [← hcx]; group
    rcases hsq with h1 | h1
    · rw [← h1, ← conj_pow, hcxc]
    · rw [← h1, hcxc]
  exact h.z_ne_one (d.hxW _ d.hzW hzx)

theorem mem_W_of_x [Finite X] (hQn : Q.Normal) (hQ2 : IsPGroup 2 Q) {q : X} (hq : q ∈ Q)
    (hqx : q⁻¹ * (d.x * q * d.x⁻¹) ∈ secTwoOmegaZ Q) : q ∈ secTwoOmegaZ Q := by
  have hxW : d.x ∈ normalizer ((secTwoOmegaZ Q : Subgroup X) : Set X) := by
    rw [mem_normalizer_iff]
    intro a
    constructor
    · exact fun ha => secTwoOmegaZ_conj hQn ha d.x
    · intro ha
      have := secTwoOmegaZ_conj hQn ha d.x⁻¹
      simpa [mul_assoc] using this
  exact secTwo_mem_of_conj_mem_coset (secTwoOmegaZ_le Q) isPGroup_W d.hx3 hxW
    (d.fix_x hQn hQ2) hq hqx

theorem commute_of_t {q : X} (hqt : q⁻¹ * (t * q * t⁻¹) ∈ secTwoOmegaZ Q) :
    q * t = t * q ∨ (q * d.w) * t = t * (q * d.w) := by
  have hcc : ∀ y : X, t * (t * y * t⁻¹) * t⁻¹ = y := fun y => by
    calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by group
      _ = y := by rw [h.t_mul_t]; group
  set a := q⁻¹ * (t * q * t⁻¹) with hadef
  have hta : t * a * t⁻¹ = a := by
    have h1 : t * a * t⁻¹ = a⁻¹ := by
      calc t * a * t⁻¹ = (t * q * t⁻¹)⁻¹ * (t * (t * q * t⁻¹) * t⁻¹) := by rw [hadef]; group
        _ = (t * q * t⁻¹)⁻¹ * q := by rw [hcc]
        _ = a⁻¹ := by rw [hadef]; group
    rw [h1, inv_eq_of_mul_eq_one_right (by rw [← sq]; exact secTwoOmegaZ_sq hqt)]
  have hcomm : ∀ y : X, t * y * t⁻¹ = y → y * t = t * y := fun y hy => by
    calc y * t = t * y * t⁻¹ * t := by rw [hy]
      _ = t * y := by group
  have hzw : u ^ 2 * d.w = d.w * u ^ 2 := secTwoOmegaZ_comm d.hwW (secTwoOmegaZ_le Q d.hzW)
  rcases d.hW a hqt with h1 | h1 | h1 | h1
  · left
    apply hcomm
    calc t * q * t⁻¹ = q * a := by rw [hadef]; group
      _ = q := by rw [h1, mul_one]
  · right
    apply hcomm
    calc t * (q * d.w) * t⁻¹ = (t * q * t⁻¹) * (t * d.w * t⁻¹) := by group
      _ = q * a * (d.w * u ^ 2) := by rw [d.htw, hadef]; group
      _ = q * d.w * (u ^ 2 * u ^ 2) := by rw [h1, ← mul_assoc, mul_assoc q, hzw]; group
      _ = q * d.w := by rw [← sq, h.z_sq, mul_one]
  · exfalso; apply d.htw_ne; rw [← h1, hta]
  · exfalso
    have : t * d.w * t⁻¹ = d.w := by
      have h2 : t * (d.w * u ^ 2) * t⁻¹ = d.w * u ^ 2 := h1 ▸ hta
      calc t * d.w * t⁻¹ = t * (d.w * u ^ 2) * t⁻¹ * (t * u ^ 2 * t⁻¹)⁻¹ := by group
        _ = d.w * u ^ 2 * (u ^ 2)⁻¹ := by rw [h2, h.conj_z]
        _ = d.w := by group
    exact d.htw_ne this

include d in
theorem exists_not_mem_W (hCQ : centralizer (Q : Set X) ≤ Q) :
    ∃ a ∈ Q, a ∉ secTwoOmegaZ Q := by
  by_contra hne
  push Not at hne
  have hvC : d.v ∈ centralizer (Q : Set X) := by
    rw [mem_centralizer_iff]
    intro q hq
    have hqW := hne q hq
    rcases d.hW q hqW with h1 | h1 | h1 | h1
    · rw [h1]; group
    · rw [h1]; exact (h.mul_comm_of_mem_R d.hvR (pow_mem SecTwoHyp.u_mem_R 2)).symm
    · rw [h1]; exact d.hvw.symm
    · rw [h1]
      have hvz := h.mul_comm_of_mem_R d.hvR (pow_mem SecTwoHyp.u_mem_R 2)
      calc d.w * u ^ 2 * d.v = d.w * (u ^ 2 * d.v) := by group
        _ = d.w * (d.v * u ^ 2) := by rw [hvz]
        _ = (d.w * d.v) * u ^ 2 := by group
        _ = (d.v * d.w) * u ^ 2 := by rw [d.hvw]
        _ = d.v * (d.w * u ^ 2) := by group
  have hvW := hne _ (hCQ hvC)
  apply h.z_ne_one
  rw [← d.hvsq]
  exact secTwoOmegaZ_sq hvW

theorem odd_orderOf_map {Y : Type*} [Group Y] (f : X →* Y) : Odd (orderOf (f d.x)) := by
  have h3 := (IsPGroup.iff_orderOf.mp d.hx3) ⟨d.x, mem_zpowers _⟩
  obtain ⟨k, hk⟩ := h3
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : orderOf (f d.x) ∣ 3 ^ k := hk ▸ orderOf_map_dvd f d.x
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  rw [hj]
  exact Odd.pow (by decide)

include d in
theorem card_map_le_four [Finite X] [hQn : Q.Normal] (hQ2 : IsPGroup 2 Q) :
    Nat.card (Q.map (QuotientGroup.mk' (secTwoOmegaZ Q) :
      X →* X ⧸ secTwoOmegaZ Q)) ≤ 4 := by
  set π : X →* X ⧸ secTwoOmegaZ Q := QuotientGroup.mk' (secTwoOmegaZ Q) with hπ
  have hπW : ∀ a : X, π a = 1 ↔ a ∈ secTwoOmegaZ Q := fun a => QuotientGroup.eq_one_iff a
  have hπeq : ∀ a b : X, π a = π b ↔ a⁻¹ * b ∈ secTwoOmegaZ Q := fun a b => QuotientGroup.eq
  have hzW1 : π (u ^ 2) = 1 := (hπW _).mpr d.hzW
  have hwW1 : π d.w = 1 := (hπW _).mpr d.hwW
  refine card_le_four_of_dihedral (t := π t) (x := π d.x) ?_ ?_ (d.odd_orderOf_map π) ?_ ?_ ?_ ?_
  · rw [← map_mul, h.t_mul_t, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, d.htx, map_inv]
  · rintro _ ⟨q, hq, rfl⟩
    exact ⟨d.x * q * d.x⁻¹, hQn.conj_mem q hq d.x, by simp [π]⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact ⟨t * q * t⁻¹, hQn.conj_mem q hq t, by simp [π]⟩
  · rintro _ ⟨q, hq, rfl⟩ hqx
    have h1 : π q = π (d.x * q * d.x⁻¹) := by
      rw [map_mul, map_mul, map_inv, hqx]; group
    have := d.mem_W_of_x hQn hQ2 hq ((hπeq _ _).mp h1)
    exact (hπW q).mpr this
  · rintro _ ⟨q₁, hq₁, rfl⟩ _ ⟨q₂, hq₂, rfl⟩ h1 h2 hne1 hne2
    have key : ∀ q ∈ Q, π q * π t = π t * π q → π q ≠ 1 → π q = π d.v := by
      intro q hq hqt hq1
      have hfix : q⁻¹ * (t * q * t⁻¹) ∈ secTwoOmegaZ Q := by
        rw [← hπeq]
        rw [map_mul, map_mul, map_inv, ← hqt]; group
      have hv : ∀ c ∈ Q, c * t = t * c → π c = 1 ∨ π c = π d.v := by
        intro c hc hct
        rcases d.hCQt c hc hct with h' | h' | h' | h'
        · left; rw [h', map_one]
        · right; rw [h']
        · left; rw [h', hzW1]
        · right; rw [h', map_mul, hzW1, mul_one]
      rcases d.commute_of_t hfix with h' | h'
      · rcases hv q hq h' with h'' | h''
        · exact absurd h'' hq1
        · exact h''
      · rcases hv (q * d.w) (mul_mem hq (secTwoOmegaZ_le Q d.hwW)) h' with h'' | h'' <;>
          rw [map_mul, hwW1, mul_one] at h''
        · exact absurd h'' hq1
        · exact h''
    exact (key q₁ hq₁ h1 hne1).trans (key q₂ hq₂ h2 hne2).symm

theorem four_le_card {Y : Type*} [Group Y] [Finite Y] {V : Subgroup Y} {a b c e : Y} (ha : a ∈ V)
    (hb : b ∈ V) (hc : c ∈ V) (he : e ∈ V) (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e)
    (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) : 4 ≤ Nat.card V := by
  classical
  let F : Finset Y := {a, b, c, e}
  have hF : F.card = 4 := by
    simp only [F]
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, hae]),
      Finset.card_insert_of_notMem (by simp [hbc, hbe]),
      Finset.card_insert_of_notMem (by simp [hce]), Finset.card_singleton]
  have hinj : Function.Injective (fun f : F => (⟨f.1, by
      rcases Finset.mem_insert.mp f.2 with h | h
      · rw [h]; exact ha
      rcases Finset.mem_insert.mp h with h | h
      · rw [h]; exact hb
      rcases Finset.mem_insert.mp h with h | h
      · rw [h]; exact hc
      rw [Finset.mem_singleton.mp h]; exact he⟩ : V)) := by
    intro f₁ f₂ hf
    have h1 := congrArg Subtype.val hf
    exact Subtype.ext h1
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_finsetCard, hF] at this

include d in
theorem four_cosets [Finite X] [hQn : Q.Normal] (hQ2 : IsPGroup 2 Q)
    (hCQ : centralizer (Q : Set X) ≤ Q) :
    ∃ a ∈ Q, a ∉ secTwoOmegaZ Q ∧ a ^ 2 ∈ secTwoOmegaZ Q ∧
      d.x * a * d.x⁻¹ ∉ secTwoOmegaZ Q ∧ a⁻¹ * (d.x * a * d.x⁻¹) ∉ secTwoOmegaZ Q ∧
      a * (d.x * a * d.x⁻¹) ∉ secTwoOmegaZ Q ∧
      (a * (d.x * a * d.x⁻¹))⁻¹ * ((d.x * a * d.x⁻¹) * a) ∈ secTwoOmegaZ Q ∧
      (∀ q ∈ Q, q ∈ secTwoOmegaZ Q ∨ a⁻¹ * q ∈ secTwoOmegaZ Q ∨
        (d.x * a * d.x⁻¹)⁻¹ * q ∈ secTwoOmegaZ Q ∨
        (a * (d.x * a * d.x⁻¹))⁻¹ * q ∈ secTwoOmegaZ Q) ∧
      Nat.card (Q.map (QuotientGroup.mk' (secTwoOmegaZ Q) : X →* X ⧸ secTwoOmegaZ Q)) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : X →* X ⧸ secTwoOmegaZ Q := QuotientGroup.mk' (secTwoOmegaZ Q) with hπ
  have hπW : ∀ a : X, π a = 1 ↔ a ∈ secTwoOmegaZ Q := fun a => QuotientGroup.eq_one_iff a
  have hπeq : ∀ a b : X, π a = π b ↔ a⁻¹ * b ∈ secTwoOmegaZ Q := fun a b => QuotientGroup.eq
  have hcard := d.card_map_le_four hQ2
  set Qb := Q.map π with hQb
  obtain ⟨a₀, ha₀Q, ha₀W⟩ := d.exists_not_mem_W hCQ
  have hQb2 : IsPGroup 2 Qb := hQ2.map π
  have hQbne : Nontrivial Qb := ⟨⟨1, ⟨π a₀, a₀, ha₀Q, rfl⟩, fun h' => ha₀W
    ((hπW a₀).mp (congrArg Subtype.val h').symm)⟩⟩
  obtain ⟨n, hn, hcardQb⟩ := hQb2.nontrivial_iff_card.mp hQbne
  obtain ⟨ab, hab⟩ := exists_prime_orderOf_dvd_card' (G := Qb) 2 (by
    rw [hcardQb]; exact dvd_pow_self 2 (by omega))
  obtain ⟨a, haQ, hπa⟩ := ab.2
  have hoa : orderOf (π a) = 2 := by rw [hπa, Subgroup.orderOf_coe, hab]
  have hπa1 : π a ≠ 1 := fun h' => by rw [h', orderOf_one] at hoa; omega
  have hπa2 : π a * π a = 1 := by rw [← sq, ← hoa, pow_orderOf_eq_one]
  have haW : a ∉ secTwoOmegaZ Q := fun h' => hπa1 ((hπW a).mpr h')
  have ha2W : a ^ 2 ∈ secTwoOmegaZ Q := (hπW _).mp (by rw [map_pow, sq, hπa2])
  set b := d.x * a * d.x⁻¹ with hbdef
  have hbQ : b ∈ Q := hQn.conj_mem a haQ d.x
  have hπb : π b = π d.x * π a * (π d.x)⁻¹ := by rw [hbdef, map_mul, map_mul, map_inv]
  have hπb1 : π b ≠ 1 := by
    rw [hπb]; intro h'; apply hπa1
    calc π a = (π d.x)⁻¹ * (π d.x * π a * (π d.x)⁻¹) * π d.x := by group
      _ = 1 := by rw [h']; group
  have hπb2 : π b * π b = 1 := by
    rw [hπb, show π d.x * π a * (π d.x)⁻¹ * (π d.x * π a * (π d.x)⁻¹) =
      π d.x * (π a * π a) * (π d.x)⁻¹ by group, hπa2]; group
  have hπab : π a ≠ π b := by
    intro h'
    exact haW (d.mem_W_of_x hQn hQ2 haQ ((hπeq _ _).mp h'))
  have hπainv : (π a)⁻¹ = π a := inv_eq_of_mul_eq_one_right hπa2
  have hπbinv : (π b)⁻¹ = π b := inv_eq_of_mul_eq_one_right hπb2
  have hd3 : (1 : X ⧸ secTwoOmegaZ Q) ≠ π a * π b := by
    intro h'; apply hπab
    calc π a = (π b)⁻¹ := by rw [eq_inv_iff_mul_eq_one, h']
      _ = π b := hπbinv
  have hd5 : π a ≠ π a * π b := by
    intro h'; apply hπb1
    calc π b = (π a)⁻¹ * (π a * π b) := by group
      _ = 1 := by rw [← h', inv_mul_cancel]
  have hd6 : π b ≠ π a * π b := by
    intro h'; apply hπa1
    calc π a = π a * π b * (π b)⁻¹ := by group
      _ = 1 := by rw [← h', mul_inv_cancel]
  have hmem : ∀ q ∈ Q, π q ∈ Qb := fun q hq => ⟨q, hq, rfl⟩
  have hcases : ∀ q ∈ Q, π q = 1 ∨ π q = π a ∨ π q = π b ∨ π q = π a * π b := fun q hq =>
    secTwo_eq_of_card_le_four hcard (one_mem _) (hmem a haQ) (hmem b hbQ)
      (mul_mem (hmem a haQ) (hmem b hbQ)) hπa1.symm (Ne.symm hπb1) hd3 hπab hd5 hd6
      (hmem q hq)
  have hba : π (b * a) = π (a * b) := by
    rw [map_mul, map_mul]
    rcases hcases (b * a) (mul_mem hbQ haQ) with h' | h' | h' | h' <;> rw [map_mul] at h'
    · exfalso; apply hπab
      calc π a = (π b)⁻¹ := eq_inv_of_mul_eq_one_right h'
        _ = π b := hπbinv
    · exfalso; apply hπb1
      calc π b = π b * π a * (π a)⁻¹ := by group
        _ = 1 := by rw [h', mul_inv_cancel]
    · exfalso; apply hπa1
      calc π a = (π b)⁻¹ * (π b * π a) := by group
        _ = 1 := by rw [h', inv_mul_cancel]
    · exact h'
  have hcard4 : Nat.card Qb = 4 := le_antisymm hcard (four_le_card (one_mem _) (hmem a haQ)
    (hmem b hbQ) (mul_mem (hmem a haQ) (hmem b hbQ)) hπa1.symm (Ne.symm hπb1) hd3 hπab hd5 hd6)
  refine ⟨a, haQ, haW, ha2W, fun h' => hπb1 ((hπW b).mpr h'),
    fun h' => hπab ((hπeq _ _).mpr h'), fun h' => hd3 (by rw [← map_mul]; exact
      ((hπW _).mpr h').symm), (hπeq _ _).mp hba.symm, fun q hq => ?_, hcard4⟩
  rcases hcases q hq with h' | h' | h' | h'
  · exact Or.inl ((hπW q).mp h')
  · exact Or.inr (Or.inl ((hπeq _ _).mp h'.symm))
  · exact Or.inr (Or.inr (Or.inl ((hπeq _ _).mp h'.symm)))
  · exact Or.inr (Or.inr (Or.inr ((hπeq _ _).mp (by rw [map_mul]; exact h'.symm))))

include d in
theorem commute_of_mem [Finite X] [hQn : Q.Normal] (hQ2 : IsPGroup 2 Q)
    (hCQ : centralizer (Q : Set X) ≤ Q)
    {p q : X} (hp : p ∈ Q) (hq : q ∈ Q) : p * q = q * p := by
  obtain ⟨a, haQ, -, -, -, -, -, hk, hcos, -⟩ := d.four_cosets hQ2 hCQ
  set b := d.x * a * d.x⁻¹ with hbdef
  have hbQ : b ∈ Q := hQn.conj_mem a haQ d.x
  set k := (a * b)⁻¹ * (b * a) with hkdef
  have hcent : ∀ w ∈ secTwoOmegaZ Q, ∀ y ∈ Q, y * w = w * y := fun w hw y hy =>
    secTwoOmegaZ_comm hw hy
  have hkinv : k⁻¹ = k := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact secTwoOmegaZ_sq hk)
  have hba : b * a = a * b * k := by rw [hkdef]; group
  set b' := d.x * b * d.x⁻¹ with hb'def
  have hb'Q : b' ∈ Q := hQn.conj_mem b hbQ d.x
  have hxk : d.x * k * d.x⁻¹ = (b * b')⁻¹ * (b' * b) := by
    calc d.x * k * d.x⁻¹ = (d.x * a * d.x⁻¹ * (d.x * b * d.x⁻¹))⁻¹ *
          ((d.x * b * d.x⁻¹) * (d.x * a * d.x⁻¹)) := by rw [hkdef]; group
      _ = (b * b')⁻¹ * (b' * b) := by rw [← hbdef, ← hb'def]
  have hxk' : d.x * k * d.x⁻¹ = 1 ∨ d.x * k * d.x⁻¹ = k := by
    rw [hxk]
    have hβ : ∀ β : X, β ∈ Q → β⁻¹ * b' ∈ secTwoOmegaZ Q →
        (b * b')⁻¹ * (b' * b) = β⁻¹ * b⁻¹ * β * b := by
      intro β hβQ hβ
      set w' := β⁻¹ * b' with hw'
      have hb'eq : b' = β * w' := by rw [hw']; group
      rw [hb'eq]
      have h1 := hcent w' hβ b hbQ
      calc (b * (β * w'))⁻¹ * (β * w' * b) = w'⁻¹ * (β⁻¹ * b⁻¹ * β) * (w' * b) := by group
        _ = w'⁻¹ * (β⁻¹ * b⁻¹ * β) * (b * w') := by rw [h1]
        _ = w'⁻¹ * (β⁻¹ * b⁻¹ * β * b) * w' := by group
        _ = β⁻¹ * b⁻¹ * β * b := by
          have h2 := hcent w' hβ (β⁻¹ * b⁻¹ * β * b) (mul_mem (mul_mem (mul_mem
            (inv_mem hβQ) (inv_mem hbQ)) hβQ) hbQ)
          rw [mul_assoc, h2, ← mul_assoc, inv_mul_cancel, one_mul]
    rcases hcos b' hb'Q with h1 | h1 | h1 | h1
    · left
      rw [hβ 1 (one_mem _) (by simpa using h1)]; group
    · right
      rw [hβ a haQ h1]
      calc a⁻¹ * b⁻¹ * a * b = (b * a)⁻¹ * (a * b) := by group
        _ = k := by rw [hba]; rw [show (a * b * k)⁻¹ * (a * b) = k⁻¹ by group, hkinv]
    · left
      rw [hβ b hbQ h1]; group
    · right
      rw [hβ (a * b) (mul_mem haQ hbQ) h1]
      calc (a * b)⁻¹ * b⁻¹ * (a * b) * b = b⁻¹ * ((b * a)⁻¹ * (a * b)) * b := by group
        _ = b⁻¹ * k * b := by
          rw [hba, show (a * b * k)⁻¹ * (a * b) = k⁻¹ by group, hkinv]
        _ = k := by rw [mul_assoc, ← hcent k hk b hbQ]; group
  have hk1 : k = 1 := by
    rcases hxk' with h1 | h1
    · calc k = d.x⁻¹ * (d.x * k * d.x⁻¹) * d.x := by group
        _ = 1 := by rw [h1]; group
    · exact d.hxW k hk h1
  have hab : a * b = b * a := by rw [hba, hk1, mul_one]
  have hdec : ∀ y ∈ Q, ∃ α : X, (α = 1 ∨ α = a ∨ α = b ∨ α = a * b) ∧
      α⁻¹ * y ∈ secTwoOmegaZ Q := by
    intro y hy
    rcases hcos y hy with h1 | h1 | h1 | h1
    · exact ⟨1, Or.inl rfl, by simpa using h1⟩
    · exact ⟨a, Or.inr (Or.inl rfl), h1⟩
    · exact ⟨b, Or.inr (Or.inr (Or.inl rfl)), h1⟩
    · exact ⟨a * b, Or.inr (Or.inr (Or.inr rfl)), h1⟩
  have hαQ : ∀ α : X, (α = 1 ∨ α = a ∨ α = b ∨ α = a * b) → α ∈ Q := by
    rintro α (h' | h' | h' | h')
    · exact h' ▸ one_mem _
    · exact h' ▸ haQ
    · exact h' ▸ hbQ
    · exact h' ▸ mul_mem haQ hbQ
  have hca : Commute a b := hab
  have hcomm_a : ∀ β : X, (β = 1 ∨ β = a ∨ β = b ∨ β = a * b) → Commute a β := by
    rintro β (h' | h' | h' | h')
    · exact h' ▸ Commute.one_right a
    · exact h' ▸ Commute.refl a
    · exact h' ▸ hca
    · exact h' ▸ (Commute.refl a).mul_right hca
  have hcomm_b : ∀ β : X, (β = 1 ∨ β = a ∨ β = b ∨ β = a * b) → Commute b β := by
    rintro β (h' | h' | h' | h')
    · exact h' ▸ Commute.one_right b
    · exact h' ▸ hca.symm
    · exact h' ▸ Commute.refl b
    · exact h' ▸ hca.symm.mul_right (Commute.refl b)
  have hαβ : ∀ α β : X, (α = 1 ∨ α = a ∨ α = b ∨ α = a * b) →
      (β = 1 ∨ β = a ∨ β = b ∨ β = a * b) → α * β = β * α := by
    rintro α β (h' | h' | h' | h') hβ
    · exact h' ▸ (Commute.one_left β).eq
    · exact h' ▸ (hcomm_a β hβ).eq
    · exact h' ▸ (hcomm_b β hβ).eq
    · exact h' ▸ ((hcomm_a β hβ).mul_left (hcomm_b β hβ)).eq
  obtain ⟨α, hα, hαp⟩ := hdec p hp
  obtain ⟨β, hβ, hβq⟩ := hdec q hq
  have hp' : p = α * (α⁻¹ * p) := by group
  have hq' : q = β * (β⁻¹ * q) := by group
  rw [hp', hq']
  have e1 := hcent _ hαp β (hαQ β hβ)
  have e2 := hcent _ hβq α (hαQ α hα)
  have e3 := hcent _ hαp _ (secTwoOmegaZ_le Q hβq)
  calc α * (α⁻¹ * p) * (β * (β⁻¹ * q)) = α * ((α⁻¹ * p) * β) * (β⁻¹ * q) := by group
    _ = α * (β * (α⁻¹ * p)) * (β⁻¹ * q) := by rw [e1]
    _ = (α * β) * ((α⁻¹ * p) * (β⁻¹ * q)) := by group
    _ = (β * α) * ((β⁻¹ * q) * (α⁻¹ * p)) := by rw [hαβ α β hα hβ, e3]
    _ = β * (α * (β⁻¹ * q)) * (α⁻¹ * p) := by group
    _ = β * ((β⁻¹ * q) * α) * (α⁻¹ * p) := by rw [e2]
    _ = β * (β⁻¹ * q) * (α * (α⁻¹ * p)) := by group

include d in
theorem card_W [Finite X] (hQn : Q.Normal) : Nat.card (secTwoOmegaZ Q) = 4 := by
  have hzinv := h.z_inv
  have hzw : u ^ 2 * d.w = d.w * u ^ 2 := secTwoOmegaZ_comm d.hwW (secTwoOmegaZ_le Q d.hzW)
  have hd3 : (1 : X) ≠ d.w * u ^ 2 := by
    intro h'; apply d.hwz
    calc d.w = d.w * u ^ 2 * (u ^ 2)⁻¹ := by group
      _ = u ^ 2 := by rw [← h', one_mul, hzinv]
  have hd5 : u ^ 2 ≠ d.w * u ^ 2 := by
    intro h'; apply d.hw1
    calc d.w = d.w * u ^ 2 * (u ^ 2)⁻¹ := by group
      _ = 1 := by rw [← h', mul_inv_cancel]
  have hd6 : d.w ≠ d.w * u ^ 2 := by
    intro h'; apply h.z_ne_one
    calc u ^ 2 = d.w⁻¹ * (d.w * u ^ 2) := by group
      _ = 1 := by rw [← h', inv_mul_cancel]
  refine le_antisymm (h.card_le_four (fun a ha => secTwoOmegaZ_sq ha)
    (fun a ha => secTwoOmegaZ_conj hQn ha t)) (four_le_card (one_mem _) d.hzW d.hwW
    (mul_mem d.hwW d.hzW) h.z_ne_one.symm d.hw1.symm hd3 d.hwz.symm hd5 hd6)

include d in
theorem mem_W_of_sq [Finite X] [hQn : Q.Normal] (hQ2 : IsPGroup 2 Q)
    (hCQ : centralizer (Q : Set X) ≤ Q)
    {q : X} (hq : q ∈ Q) (hq2 : q ^ 2 = 1) : q ∈ secTwoOmegaZ Q := by
  have hcomm : ∀ p ∈ Q, ∀ r ∈ Q, p * r = r * p := fun p hp r hr =>
    d.commute_of_mem hQ2 hCQ hp hr
  let E : Subgroup X :=
    { carrier := {p | p ∈ Q ∧ p ^ 2 = 1}
      mul_mem' := fun {p r} hp hr => ⟨mul_mem hp.1 hr.1, by
        rw [sq, show p * r * (p * r) = p * (r * p) * r by group, ← hcomm p hp.1 r hr.1,
          show p * (p * r) * r = p ^ 2 * r ^ 2 by rw [sq, sq]; group, hp.2, hr.2, one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow 2⟩
      inv_mem' := fun {p} hp => ⟨inv_mem hp.1, by rw [inv_pow, hp.2, inv_one]⟩ }
  have hEcard : Nat.card E ≤ 4 := h.card_le_four (fun p hp => hp.2) (fun p hp =>
    ⟨hQn.conj_mem p hp.1 t, by rw [conj_pow, hp.2]; group⟩)
  have hWE : ∀ p ∈ secTwoOmegaZ Q, p ∈ E := fun p hp =>
    ⟨secTwoOmegaZ_le Q hp, secTwoOmegaZ_sq hp⟩
  have hzinv := h.z_inv
  have hd3 : (1 : X) ≠ d.w * u ^ 2 := by
    intro h'; apply d.hwz
    calc d.w = d.w * u ^ 2 * (u ^ 2)⁻¹ := by group
      _ = u ^ 2 := by rw [← h', one_mul, hzinv]
  have hd5 : u ^ 2 ≠ d.w * u ^ 2 := by
    intro h'; apply d.hw1
    calc d.w = d.w * u ^ 2 * (u ^ 2)⁻¹ := by group
      _ = 1 := by rw [← h', mul_inv_cancel]
  have hd6 : d.w ≠ d.w * u ^ 2 := by
    intro h'; apply h.z_ne_one
    calc u ^ 2 = d.w⁻¹ * (d.w * u ^ 2) := by group
      _ = 1 := by rw [← h', inv_mul_cancel]
  rcases secTwo_eq_of_card_le_four hEcard (one_mem _) (hWE _ d.hzW) (hWE _ d.hwW)
      (hWE _ (mul_mem d.hwW d.hzW)) h.z_ne_one.symm d.hw1.symm hd3 d.hwz.symm hd5 hd6
      (show q ∈ E from ⟨hq, hq2⟩) with h1 | h1 | h1 | h1
  · rw [h1]; exact one_mem _
  · rw [h1]; exact d.hzW
  · rw [h1]; exact d.hwW
  · rw [h1]; exact mul_mem d.hwW d.hzW

include d in
theorem sq_mem_W [Finite X] [hQn : Q.Normal] (hQ2 : IsPGroup 2 Q)
    (hCQ : centralizer (Q : Set X) ≤ Q) :
    (∀ q ∈ Q, q ^ 2 ∈ secTwoOmegaZ Q) ∧ Nat.card Q = 16 ∧ ∃ a₀ ∈ Q, a₀ ^ 2 = d.w := by
  obtain ⟨a, haQ, haW, ha2, hbW, habW, habW', -, hcos, hcard⟩ := d.four_cosets hQ2 hCQ
  set b := d.x * a * d.x⁻¹ with hbdef
  have hbQ : b ∈ Q := hQn.conj_mem a haQ d.x
  have hcomm : ∀ p ∈ Q, ∀ r ∈ Q, p * r = r * p := fun p hp r hr =>
    d.commute_of_mem hQ2 hCQ hp hr
  have hb2 : b ^ 2 ∈ secTwoOmegaZ Q := by
    rw [hbdef, conj_pow]; exact secTwoOmegaZ_conj hQn ha2 d.x
  have hab2 : (a * b) ^ 2 = a ^ 2 * b ^ 2 := (Commute.mul_pow (hcomm a haQ b hbQ) 2)
  have hsq : ∀ q ∈ Q, q ^ 2 ∈ secTwoOmegaZ Q := by
    intro q hq
    have key : ∀ α ∈ Q, α ^ 2 ∈ secTwoOmegaZ Q → α⁻¹ * q ∈ secTwoOmegaZ Q →
        q ^ 2 ∈ secTwoOmegaZ Q := by
      intro α hαQ hα2 hαq
      have hq' : q = α * (α⁻¹ * q) := by group
      rw [hq', Commute.mul_pow (hcomm α hαQ _ (secTwoOmegaZ_le Q hαq)) 2,
        secTwoOmegaZ_sq hαq, mul_one]
      exact hα2
    rcases hcos q hq with h1 | h1 | h1 | h1
    · rw [secTwoOmegaZ_sq h1]; exact one_mem _
    · exact key a haQ ha2 h1
    · exact key b hbQ hb2 h1
    · exact key (a * b) (mul_mem haQ hbQ) (by rw [hab2]; exact mul_mem ha2 hb2) h1
  refine ⟨hsq, ?_, ?_⟩
  ·
    set π : X →* X ⧸ secTwoOmegaZ Q := QuotientGroup.mk' (secTwoOmegaZ Q)
    let f : Q →* X ⧸ secTwoOmegaZ Q := π.comp Q.subtype
    have hrange : f.range = Q.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hker : Nat.card f.ker = Nat.card (secTwoOmegaZ Q) := by
      refine Nat.card_congr
        { toFun := fun q => ⟨q.1.1, (QuotientGroup.eq_one_iff _).mp q.2⟩
          invFun := fun w => ⟨⟨w.1, secTwoOmegaZ_le Q w.2⟩,
            (QuotientGroup.eq_one_iff _).mpr w.2⟩
          left_inv := fun q => rfl
          right_inv := fun w => rfl }
    have := Subgroup.card_ker_mul_card_range f
    rw [hker, hrange, hcard, d.card_W hQn] at this
    omega
  ·
    have hne : ∀ q ∈ Q, q ∉ secTwoOmegaZ Q → q ^ 2 ≠ 1 := fun q hq hqW h2 =>
      hqW (d.mem_W_of_sq hQ2 hCQ hq h2)
    have hW' : ∀ q ∈ Q, q ∉ secTwoOmegaZ Q → q ^ 2 = u ^ 2 ∨ q ^ 2 = d.w ∨
        q ^ 2 = d.w * u ^ 2 := by
      intro q hq hqW
      rcases d.hW _ (hsq q hq) with h1 | h1 | h1 | h1
      · exact absurd h1 (hne q hq hqW)
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
    have ha2' := hW' a haQ haW
    have hb2' := hW' b hbQ hbW
    have hab2' := hW' (a * b) (mul_mem haQ hbQ) habW'
    rw [hab2] at hab2'
    have hzw : u ^ 2 * d.w = d.w * u ^ 2 := secTwoOmegaZ_comm d.hwW (secTwoOmegaZ_le Q d.hzW)
    have hz2 := h.z_sq
    have hw2 : d.w ^ 2 = 1 := secTwoOmegaZ_sq d.hwW
    by_contra hcon
    push Not at hcon
    have hna := hcon a haQ
    have hnb := hcon b hbQ
    have hnab := hcon (a * b) (mul_mem haQ hbQ)
    rw [hab2] at hnab
    have e1 : u ^ 2 * u ^ 2 = 1 := by rw [← sq, hz2]
    have e2 : u ^ 2 * (d.w * u ^ 2) = d.w := by
      rw [← mul_assoc, hzw, mul_assoc, ← sq, hz2, mul_one]
    have e3 : d.w * u ^ 2 * u ^ 2 = d.w := by rw [mul_assoc, ← sq, hz2, mul_one]
    have e4 : d.w * u ^ 2 * (d.w * u ^ 2) = 1 := by
      rw [show d.w * u ^ 2 * (d.w * u ^ 2) = d.w * (u ^ 2 * d.w) * u ^ 2 by group, hzw,
        show d.w * (d.w * u ^ 2) * u ^ 2 = (d.w * d.w) * (u ^ 2 * u ^ 2) by group, ← sq d.w,
        hw2, e1, mul_one]
    have hzinv := h.z_inv
    have hd3 : (1 : X) ≠ d.w * u ^ 2 := by
      intro h'; apply d.hwz
      calc d.w = d.w * u ^ 2 * (u ^ 2)⁻¹ := by group
        _ = u ^ 2 := by rw [← h', one_mul, hzinv]
    have hone : ∀ y : X, y = 1 → (y = u ^ 2 ∨ y = d.w ∨ y = d.w * u ^ 2) → False := by
      rintro y rfl (h' | h' | h')
      · exact h.z_ne_one h'.symm
      · exact d.hw1 h'.symm
      · exact hd3 h'
    rcases ha2' with h1 | h1 | h1
    · rcases hb2' with h2 | h2 | h2
      · rw [h1, h2] at hab2'; exact hone _ e1 hab2'
      · exact hnb h2
      · rw [h1, h2, e2] at hnab; exact hnab rfl
    · exact hna h1
    · rcases hb2' with h2 | h2 | h2
      · rw [h1, h2, e3] at hnab; exact hnab rfl
      · exact hnb h2
      · rw [h1, h2] at hab2'; exact hone _ e4 hab2'

include d in
theorem card_inverted_le_four [Finite X] [hQn : Q.Normal] (hQ2 : IsPGroup 2 Q)
    (hCQ : centralizer (Q : Set X) ≤ Q) (F : Finset X)
    (hF : ∀ q ∈ F, q ∈ Q ∧ t * q * t⁻¹ = q⁻¹) : F.card ≤ 4 := by
  obtain ⟨-, hcard16, a₀, ha₀Q, ha₀⟩ := d.sq_mem_W hQ2 hCQ
  have hcomm : ∀ p ∈ Q, ∀ r ∈ Q, p * r = r * p := fun p hp r hr =>
    d.commute_of_mem hQ2 hCQ hp hr
  have htQ : ∀ e ∈ Q, t * e * t⁻¹ ∈ Q := fun e he => hQn.conj_mem e he t
  let nm : Q →* Q :=
    { toFun := fun e => ⟨e * (t * e * t⁻¹), mul_mem e.2 (htQ e e.2)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun e f => by
        apply Subtype.ext
        change (e : X) * f * (t * (e * f) * t⁻¹) =
          (e : X) * (t * e * t⁻¹) * ((f : X) * (t * f * t⁻¹))
        have h1 := hcomm _ f.2 _ (htQ e e.2)
        calc (e : X) * f * (t * (e * f) * t⁻¹) = (e : X) * (f * (t * e * t⁻¹)) *
            (t * f * t⁻¹) := by group
          _ = (e : X) * ((t * e * t⁻¹) * f) * (t * f * t⁻¹) := by rw [h1]
          _ = (e : X) * (t * e * t⁻¹) * ((f : X) * (t * f * t⁻¹)) := by group }
  have hcomm₀ := hcomm _ ha₀Q _ (htQ _ ha₀Q)
  set a₀' : Q := ⟨a₀, ha₀Q⟩
  set b₀ : X := a₀ * (t * a₀ * t⁻¹) with hb₀
  have hb₀2 : b₀ ^ 2 = u ^ 2 := by
    rw [hb₀, (Commute.mul_pow hcomm₀ 2), conj_pow, ha₀, d.htw,
      show d.w * (d.w * u ^ 2) = (d.w * d.w) * u ^ 2 by group, ← sq, secTwoOmegaZ_sq d.hwW,
      one_mul]
  have hnm1 : ((nm a₀' : Q) : X) = b₀ := rfl
  have hnm2 : ((nm (a₀' ^ 2) : Q) : X) = u ^ 2 := by rw [map_pow, Subgroup.coe_pow, hnm1, hb₀2]
  have hnm3 : ((nm (a₀' ^ 3) : Q) : X) = b₀ * u ^ 2 := by
    rw [map_pow, Subgroup.coe_pow, hnm1, pow_succ', ← hb₀2]
  have hb₀1 : b₀ ≠ 1 := fun h' => h.z_ne_one (by rw [← hb₀2, h', one_pow])
  have hz1 := h.z_ne_one
  have hrange : 4 ≤ Nat.card nm.range := by
    have hne : ∀ p r : Q, (p : X) ≠ r → p ≠ r := fun p r h' h'' => h' (congrArg _ h'')
    refine four_le_card (one_mem _) ⟨a₀', rfl⟩ ⟨a₀' ^ 2, rfl⟩ ⟨a₀' ^ 3, rfl⟩
      (hne _ _ ?_) (hne _ _ ?_) (hne _ _ ?_) (hne _ _ ?_) (hne _ _ ?_) (hne _ _ ?_)
    · rw [hnm1]; exact hb₀1.symm
    · rw [hnm2]; exact hz1.symm
    · rw [hnm3]; intro h'
      apply hz1
      rw [← hb₀2, sq, show b₀ = (u ^ 2)⁻¹ by rw [eq_inv_iff_mul_eq_one]; exact h'.symm, h.z_inv,
        ← sq, h.z_sq]
    · rw [hnm1, hnm2]; intro h'; apply hz1
      rw [← hb₀2, h', h.z_sq]
    · rw [hnm1, hnm3]; intro h'; apply hz1
      calc u ^ 2 = b₀⁻¹ * (b₀ * u ^ 2) := by group
        _ = 1 := by rw [← h', inv_mul_cancel]
    · rw [hnm2, hnm3]; intro h'; apply hb₀1
      calc b₀ = b₀ * u ^ 2 * (u ^ 2)⁻¹ := by group
        _ = 1 := by rw [← h', mul_inv_cancel]
  have hk1 := Subgroup.card_ker_mul_card_range nm
  rw [hcard16] at hk1
  have hkn : Nat.card nm.ker ≤ 4 := by
    by_contra hlt; push Not at hlt
    have : 5 * 4 ≤ Nat.card nm.ker * Nat.card nm.range := Nat.mul_le_mul hlt hrange
    omega
  have hmem : ∀ q : F, (⟨q.1, (hF q.1 q.2).1⟩ : Q) ∈ nm.ker := by
    intro q
    apply Subtype.ext
    change q.1 * (t * q.1 * t⁻¹) = 1
    rw [(hF q.1 q.2).2, mul_inv_cancel]
  have hinj : Function.Injective (fun q : F => (⟨⟨q.1, (hF q.1 q.2).1⟩, hmem q⟩ : nm.ker)) := by
    intro q₁ q₂ hq
    have h1 := congrArg (fun e : nm.ker => ((e : Q) : X)) hq
    exact Subtype.ext h1
  calc F.card = Nat.card F := (Nat.card_eq_finsetCard F).symm
    _ ≤ Nat.card nm.ker := Nat.card_le_card_of_injective _ hinj
    _ ≤ 4 := hkn

include d in
theorem t_not_mem_Q : t ∉ Q := by
  intro htQ
  apply d.htw_ne
  rw [secTwoOmegaZ_comm d.hwW htQ]; group

theorem two_mul_card_le {H K : Subgroup X} [Finite K] (hHK : H ≤ K) (hne : ¬ K ≤ H) :
    2 * Nat.card H ≤ Nat.card K := by
  have h1 := Subgroup.relIndex_mul_card H K
  rw [inf_eq_left.mpr hHK] at h1
  have h2 : H.relIndex K ≠ 1 := fun h' => hne (Subgroup.relIndex_eq_one.mp h')
  have h3 : H.relIndex K ≠ 0 := by
    intro h'; rw [h', zero_mul] at h1; exact Nat.card_pos.ne' h1.symm
  rw [← h1]
  exact Nat.mul_le_mul_right _ (by omega)

include d in
theorem card_sylow [Finite X] [hQn : Q.Normal] (hQ2 : IsPGroup 2 Q)
    (hCQ : centralizer (Q : Set X) ≤ Q)
    (P : Sylow 2 X) : Nat.card P = 32 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype X := Fintype.ofFinite X
  obtain ⟨-, hcard16, -⟩ := d.sq_mem_W hQ2 hCQ
  set S := d.S with hSdef
  have hS2 : IsPGroup 2 (S : Subgroup X) := S.isPGroup'
  have hQS : Q ≤ S := hQ2.le_sylow_of_normal S
  have htS : t ∈ (S : Subgroup X) := d.hRS SecTwoHyp.t_mem_R
  have htQ := d.t_not_mem_Q
  set T : Subgroup X := Q ⊔ zpowers t with hTdef
  have hTS : T ≤ S := sup_le hQS (zpowers_le.mpr htS)
  have hQT : Q ≤ T := le_sup_left
  have htT : t ∈ T := (le_sup_right : zpowers t ≤ T) (mem_zpowers t)
  have hTcases : ∀ y ∈ T, y ∈ Q ∨ t⁻¹ * y ∈ Q := by
    intro y hy
    have hy' : y ∈ ((Q : Set X) * (zpowers t : Set X)) := by
      rw [← Subgroup.normal_mul]; exact hy
    obtain ⟨q, hq, k, hk, rfl⟩ := hy'
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hk
    have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, h.t_mul_t]
    rcases Int.even_or_odd' n with ⟨j, rfl | rfl⟩
    · left
      change q * t ^ (2 * j) ∈ Q
      rw [zpow_mul, ht2, one_zpow, mul_one]; exact hq
    · right
      change t⁻¹ * (q * t ^ (2 * j + 1)) ∈ Q
      rw [zpow_add, zpow_mul, ht2, one_zpow, one_mul, zpow_one]
      exact hQn.conj_mem q hq t⁻¹ |> fun h' => by simpa [mul_assoc] using h'
  have hTle : Nat.card T ≤ 32 := by
    let g : T → Q ⊕ Q := fun y => if hy : (y : X) ∈ Q then Sum.inl ⟨y, hy⟩ else
      Sum.inr ⟨t⁻¹ * y, (hTcases y y.2).resolve_left hy⟩
    have hg : Function.Injective g := by
      intro y₁ y₂ hy
      by_cases h₁ : (y₁ : X) ∈ Q <;> by_cases h₂ : (y₂ : X) ∈ Q
      · simp only [g, h₁, h₂, ↓reduceDIte] at hy
        have h' : (⟨y₁, h₁⟩ : Q) = ⟨y₂, h₂⟩ := Sum.inl.inj hy
        have h'' : (y₁ : X) = y₂ := congrArg (fun q : Q => (q : X)) h'
        exact Subtype.ext h''
      · simp only [g, h₁, h₂, ↓reduceDIte] at hy
        exact absurd hy Sum.inl_ne_inr
      · simp only [g, h₁, h₂, ↓reduceDIte] at hy
        exact absurd hy Sum.inr_ne_inl
      · simp only [g, h₁, h₂, ↓reduceDIte] at hy
        have h' : (⟨t⁻¹ * y₁, (hTcases y₁ y₁.2).resolve_left h₁⟩ : Q) =
          ⟨t⁻¹ * y₂, (hTcases y₂ y₂.2).resolve_left h₂⟩ := Sum.inr.inj hy
        have h'' : t⁻¹ * (y₁ : X) = t⁻¹ * y₂ := congrArg (fun q : Q => (q : X)) h'
        exact Subtype.ext (mul_left_cancel h'')
    calc Nat.card T ≤ Nat.card (Q ⊕ Q) := Nat.card_le_card_of_injective g hg
      _ = 32 := by rw [Nat.card_sum, hcard16]
  have hTge : 32 ≤ Nat.card T := by
    have := two_mul_card_le hQT (fun h' => htQ (h' htT))
    rw [hcard16] at this; exact this
  have hTeq : T = S := by
    by_contra hne
    obtain ⟨s, hsS, hsT, hsN⟩ := secTwo_exists_mem_normalizer hS2 hTS hne
    set N : Subgroup X := (S : Subgroup X) ⊓ normalizer (T : Set X) with hNdef
    have hTN : T ≤ N := le_inf hTS (le_normalizer)
    have hNge : 64 ≤ Nat.card N := by
      have := two_mul_card_le hTN (fun h' => hsT (h' ⟨hsS, hsN⟩))
      omega
    have hconj : ∀ n ∈ N, t⁻¹ * (n * t * n⁻¹) ∈ Q ∧
        t * (t⁻¹ * (n * t * n⁻¹)) * t⁻¹ = (t⁻¹ * (n * t * n⁻¹))⁻¹ := by
      intro n hn
      have hmem : n * t * n⁻¹ ∈ T := (mem_normalizer_iff.mp hn.2 t).mp htT
      have hnQ : n * t * n⁻¹ ∉ Q := fun h' => htQ (by
        have := hQn.conj_mem _ h' n⁻¹
        simpa [mul_assoc] using this)
      refine ⟨(hTcases _ hmem).resolve_left hnQ, ?_⟩
      have hinv : (n * t * n⁻¹) * (n * t * n⁻¹) = 1 := by
        rw [show n * t * n⁻¹ * (n * t * n⁻¹) = n * (t * t) * n⁻¹ by group, h.t_mul_t]; group
      have hti := h.t_inv
      have hcinv : (n * t * n⁻¹)⁻¹ = n * t * n⁻¹ := inv_eq_of_mul_eq_one_right hinv
      calc t * (t⁻¹ * (n * t * n⁻¹)) * t⁻¹ = (n * t * n⁻¹) * t⁻¹ := by group
        _ = (n * t * n⁻¹)⁻¹ * t := by rw [hcinv, hti]
        _ = (t⁻¹ * (n * t * n⁻¹))⁻¹ := by group
    let NF : Finset X := Finset.univ.filter (· ∈ N)
    let IF : Finset X := Finset.univ.filter (fun q => q ∈ Q ∧ t * q * t⁻¹ = q⁻¹)
    let f : X → X := fun n => t⁻¹ * (n * t * n⁻¹)
    have hIF : IF.card ≤ 4 := d.card_inverted_le_four hQ2 hCQ IF (fun q hq =>
      (Finset.mem_filter.mp hq).2)
    have hfib : ∀ b ∈ IF, (NF.filter (fun n => f n = b)).card ≤ 8 := by
      intro b _
      by_cases hne : (NF.filter (fun n => f n = b)).Nonempty
      · obtain ⟨n₀, hn₀⟩ := hne
        rw [Finset.mem_filter] at hn₀
        have hn₀N : n₀ ∈ N := (Finset.mem_filter.mp hn₀.1).2
        let RF : Finset X := Finset.univ.filter (· ∈ secTwoR t u)
        have hRF : RF.card ≤ 8 := by
          have := h.card_R_le
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
          exact this
        refine le_trans (Finset.card_le_card_of_injOn (fun n => n₀⁻¹ * n) ?_ ?_) hRF
        · intro n hn
          rw [Finset.mem_coe, Finset.mem_filter] at hn
          have hnN : n ∈ N := (Finset.mem_filter.mp hn.1).2
          have hfn : f n = f n₀ := hn.2.trans hn₀.2.symm
          simp only [f] at hfn
          have hct : n₀⁻¹ * n * t = t * (n₀⁻¹ * n) := by
            have h1 : n * t * n⁻¹ = n₀ * t * n₀⁻¹ := mul_left_cancel hfn
            calc n₀⁻¹ * n * t = n₀⁻¹ * (n * t * n⁻¹) * n := by group
              _ = n₀⁻¹ * (n₀ * t * n₀⁻¹) * n := by rw [h1]
              _ = t * (n₀⁻¹ * n) := by group
          rw [Finset.mem_coe, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [← h.inf_centralizer_eq hS2 d.hRS]
          exact Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (Subgroup.mem_inf.mp hn₀N).1)
            (Subgroup.mem_inf.mp hnN).1, mem_centralizer_singleton_iff.mpr hct⟩
        · intro n₁ _ n₂ _ h12
          exact mul_left_cancel h12
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]; omega
    have hmaps : ∀ n ∈ NF, f n ∈ IF := by
      intro n hn
      have hnN : n ∈ N := (Finset.mem_filter.mp hn).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hconj n hnN⟩
    have hNF : NF.card ≤ 8 * IF.card := Finset.card_le_mul_card_image_of_maps_to hmaps 8 hfib
    have hNcard : Nat.card N = NF.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    omega
  have hS32 : Nat.card (S : Subgroup X) = 32 := by
    rw [← hTeq]; omega
  rw [Sylow.card_eq_multiplicity P, ← Sylow.card_eq_multiplicity S, hS32]

end SecTwoCData

theorem SecTwoHyp.center_or_wreathS3 [Finite X] (h : SecTwoHyp X t u) {Q : Subgroup X}
    [hQn : Q.Normal]
    (hQ2 : IsPGroup 2 Q) (hCQ : centralizer (Q : Set X) ≤ Q) :
    u ^ 2 ∈ center X ∨ WreathS3CaseIn X (u ^ 2) := by
  rcases h.constrained_setup hQn hQ2 hCQ with hz | hd
  · exact Or.inl hz
  right
  obtain ⟨d⟩ := hd
  obtain ⟨hsq, hcard16, -⟩ := d.sq_mem_W hQ2 hCQ
  refine ⟨Q, hQn, ⟨⟨fun a b => Subtype.ext (d.commute_of_mem hQ2 hCQ a.2 b.2)⟩⟩, hcard16,
    fun a ha => ?_, hCQ, secTwoOmegaZ_le Q d.hzW, fun a ha ha2 ha1 => ?_, d.card_sylow hQ2 hCQ⟩
  · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, secTwoOmegaZ_sq (hsq a ha)]
  · rcases d.hW a (d.mem_W_of_sq hQ2 hCQ ha ha2) with h1 | h1 | h1 | h1
    · exact absurd h1 ha1
    · exact ⟨1, by rw [h1]; group⟩
    · exact ⟨d.g, by rw [h1, d.hg]⟩
    · exact ⟨d.g₂, by rw [h1, d.hg₂]⟩

end CFSG.LocalAnalysis.EvenBN.Tits
