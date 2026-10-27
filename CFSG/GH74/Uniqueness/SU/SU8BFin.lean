module

public import CFSG.GH74.Uniqueness.SU.SU8BCnt
public import CFSG.GH74.Uniqueness.SU.SU8Glob
public import CFSG.GH74.Uniqueness.SU.SU8UAbs

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.Bender CFSG.GH74.Uniqueness.SU.SU4
  CFSG.GH74.Uniqueness.SU.SU8.Setup CFSG.GH74.Uniqueness.SU.SU8.Burn
open scoped Pointwise

namespace CaseBCnt

variable {G : Type} [Group G] {z : G} {L A V₀ : Subgroup G}

theorem pow_mul_seven_acts {g₀ : G} (h7 : ∀ a ∈ A, g₀ ^ 7 * a * (g₀ ^ 7)⁻¹ = a)
    (hN : ∀ a ∈ A, g₀ * a * g₀⁻¹ ∈ A) (q : ℕ) :
    ∀ a ∈ A, g₀ ^ (7 * q) * a * (g₀ ^ (7 * q))⁻¹ = a := by
  induction q with
  | zero => intro a _; simp
  | succ q ih =>
    intro a ha
    have e : g₀ ^ (7 * (q + 1)) = g₀ ^ 7 * g₀ ^ (7 * q) := by
      rw [Nat.mul_succ, pow_add]
      exact (Commute.pow_pow_self g₀ (7 * q) 7).eq
    have hA : g₀ ^ (7 * q) * a * (g₀ ^ (7 * q))⁻¹ ∈ A := pow_conj_mem hN _ a ha
    rw [e]
    calc g₀ ^ 7 * g₀ ^ (7 * q) * a * (g₀ ^ 7 * g₀ ^ (7 * q))⁻¹
        = g₀ ^ 7 * (g₀ ^ (7 * q) * a * (g₀ ^ (7 * q))⁻¹) * (g₀ ^ 7)⁻¹ := by group
      _ = g₀ ^ (7 * q) * a * (g₀ ^ (7 * q))⁻¹ := h7 _ hA
      _ = a := ih a ha

theorem triv_mod {g₀ : G} (hg₀N : g₀ ∈ normalizer (A : Set G))
    (h7 : ∀ a ∈ A, g₀ ^ 7 * a * (g₀ ^ 7)⁻¹ = a)
    (hfpf : ∀ a ∈ A, a ∉ V₀ → ∀ j : ℕ, 0 < j → j < 7 → g₀ ^ j * a * (g₀ ^ j)⁻¹ * a⁻¹ ∉ V₀)
    {m : G} (hmV : ∀ c ∈ V₀, m * c * m⁻¹ ∈ V₀)
    (hj : ∃ j : ℕ, ∀ a ∈ A, m * a * m⁻¹ * (g₀ ^ j * a * (g₀ ^ j)⁻¹)⁻¹ ∈ V₀)
    (k : ℕ) (hk : m ^ (2 ^ k) = 1) (hAV : ∃ a ∈ A, a ∉ V₀) :
    ∀ a ∈ A, m * a * m⁻¹ * a⁻¹ ∈ V₀ := by
  obtain ⟨j, hj⟩ := hj
  have hN' : ∀ a ∈ A, g₀ * a * g₀⁻¹ ∈ A := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp hg₀N a).mp ha
  have hgA : ∀ (i : ℕ), ∀ b ∈ A, g₀ ^ i * b * (g₀ ^ i)⁻¹ ∈ A := pow_conj_mem hN'
  have key : ∀ r : ℕ, ∀ a ∈ A,
      m ^ r * a * (m ^ r)⁻¹ * (g₀ ^ (j * r) * a * (g₀ ^ (j * r))⁻¹)⁻¹ ∈ V₀ := by
    intro r
    induction r with
    | zero => intro a ha; simp
    | succ r ih =>
      intro a ha
      have hd₁ := ih a ha
      have ha' : g₀ ^ (j * r) * a * (g₀ ^ (j * r))⁻¹ ∈ A := hgA _ a ha
      have hd₂ := hj _ ha'
      have h3 := V₀.mul_mem (hmV _ hd₁) hd₂
      have e : m ^ (r + 1) * a * (m ^ (r + 1))⁻¹ *
            (g₀ ^ (j * (r + 1)) * a * (g₀ ^ (j * (r + 1)))⁻¹)⁻¹
          = m * (m ^ r * a * (m ^ r)⁻¹ * (g₀ ^ (j * r) * a * (g₀ ^ (j * r))⁻¹)⁻¹) * m⁻¹ *
            (m * (g₀ ^ (j * r) * a * (g₀ ^ (j * r))⁻¹) * m⁻¹ *
              (g₀ ^ j * (g₀ ^ (j * r) * a * (g₀ ^ (j * r))⁻¹) * (g₀ ^ j)⁻¹)⁻¹) := by
        have e1 : g₀ ^ (j * (r + 1)) = g₀ ^ j * g₀ ^ (j * r) := by
          rw [Nat.mul_succ, pow_add]
          exact (Commute.pow_pow_self g₀ (j * r) j).eq
        rw [e1, pow_succ']
        group
      rw [e]; exact h3
  have hall : ∀ a ∈ A, a * (g₀ ^ (j * 2 ^ k) * a * (g₀ ^ (j * 2 ^ k))⁻¹)⁻¹ ∈ V₀ := by
    intro a ha
    have := key (2 ^ k) a ha
    rwa [hk, one_mul, inv_one, mul_one] at this
  have h7j : 7 ∣ j := by
    by_contra hnd
    obtain ⟨a₁, ha₁, ha₁V⟩ := hAV
    have hnd2 : ¬ 7 ∣ j * 2 ^ k := by
      intro h
      have hp : Nat.Prime 7 := by norm_num
      rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
      · exact hnd h1
      · have := hp.dvd_of_dvd_pow h1
        omega
    have hj' : 0 < (j * 2 ^ k) % 7 := by
      rcases Nat.eq_zero_or_pos ((j * 2 ^ k) % 7) with h0 | h0
      · exact absurd (Nat.dvd_of_mod_eq_zero h0) hnd2
      · exact h0
    have hlt : (j * 2 ^ k) % 7 < 7 := Nat.mod_lt _ (by norm_num)
    have hdm := Nat.div_add_mod (j * 2 ^ k) 7
    have hpow : g₀ ^ (j * 2 ^ k) * a₁ * (g₀ ^ (j * 2 ^ k))⁻¹ =
        g₀ ^ ((j * 2 ^ k) % 7) * a₁ * (g₀ ^ ((j * 2 ^ k) % 7))⁻¹ := by
      have hA1 : g₀ ^ ((j * 2 ^ k) % 7) * a₁ * (g₀ ^ ((j * 2 ^ k) % 7))⁻¹ ∈ A := hgA _ a₁ ha₁
      have h1 := pow_mul_seven_acts h7 hN' ((j * 2 ^ k) / 7) _ hA1
      calc g₀ ^ (j * 2 ^ k) * a₁ * (g₀ ^ (j * 2 ^ k))⁻¹
          = g₀ ^ (7 * ((j * 2 ^ k) / 7)) * (g₀ ^ ((j * 2 ^ k) % 7) * a₁ *
              (g₀ ^ ((j * 2 ^ k) % 7))⁻¹) * (g₀ ^ (7 * ((j * 2 ^ k) / 7)))⁻¹ := by
            conv_lhs => rw [← hdm, pow_add]
            group
        _ = _ := h1
    have h2 := hall a₁ ha₁
    rw [hpow] at h2
    apply hfpf a₁ ha₁ ha₁V _ hj' hlt
    have := V₀.inv_mem h2
    simpa using this
  obtain ⟨q, hq⟩ := h7j
  have hj1 := key 1
  intro a ha
  have h1 := hj1 a ha
  have h2 : g₀ ^ (j * 1) * a * (g₀ ^ (j * 1))⁻¹ = a := by
    rw [mul_one, hq]
    exact pow_mul_seven_acts h7 hN' q a ha
  rwa [pow_one, h2] at h1

section Final

variable [Finite G]

theorem final_false (cb : CaseB L A V₀ z)
    (hTI : ∀ g v : G, v ∈ V₀ → v ≠ 1 → g * v * g⁻¹ ∈ V₀ → g ∈ normalizer (L : Set G))
    (hirr : ¬ normalizer (A : Set G) ≤ normalizer (V₀ : Set G))
    (hodd : Odd ((normalizer (V₀ : Set G)).relIndex (normalizer (A : Set G)))) : False := by
  classical
  obtain ⟨hv, hA16, htrans⟩ := count_main cb hTI hirr hodd
  have hV₀ : ∀ w ∈ V₀, w = 1 ∨ w = z := by
    intro w hw
    by_contra hcon
    push Not at hcon
    have hsub : ({1, z, w} : Set G) ⊆ (V₀ : Set G) := by
      intro y hy
      rcases hy with rfl | rfl | rfl
      · exact V₀.one_mem
      · exact cb.z_mem
      · exact hw
    have h3 : ({1, z, w} : Set G).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨1, z, w, (Ne.symm cb.z_ne), (Ne.symm hcon.1), (Ne.symm hcon.2), rfl⟩
    have h4 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h5 : Nat.card V₀ = (V₀ : Set G).ncard := Nat.card_coe_set_eq (V₀ : Set G)
    omega
  obtain ⟨t, htmem, ⟨k, htk⟩, a₀, ha₀, hta₀⟩ := cb.two_elt hv
  obtain ⟨g₀, hg₀, -, h7, hfpf, htr, hact⟩ := cb.gen
  have hg₀N : g₀ ∈ normalizer (A : Set G) := hg₀.2
  have hAV : ∃ a ∈ A, a ∉ V₀ := by
    by_contra hcon
    push Not at hcon
    have hle : A ≤ V₀ := hcon
    have := Subgroup.card_le_of_le hle
    have h1 := cb.card_A
    have : 0 < Nat.card V₀ := Nat.card_pos
    omega
  have htV : ∀ c ∈ V₀, t * c * t⁻¹ ∈ V₀ := fun c hc => by
    rw [cb.act_C t htmem c hc]; exact hc
  have htriv := triv_mod hg₀N h7 hfpf htV (hact t htmem) k htk hAV
  have hc₀ : t * a₀ * t⁻¹ * a₀⁻¹ = z := by
    rcases hV₀ _ (htriv a₀ ha₀) with h | h
    · exact absurd (mul_inv_eq_one.mp h) hta₀
    · exact h
  have htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp htmem.2 a).mp ha
  let φ : ↥A →* ↥A := MonoidHom.mk' (fun a => ⟨t * a * t⁻¹ * a⁻¹,
      A.mul_mem (htA a a.2) (A.inv_mem a.2)⟩) (by
    intro a b
    apply Subtype.ext
    have hcomm := cb.A_comm (t * (b : G) * t⁻¹ * (b : G)⁻¹)
      (A.mul_mem (htA b b.2) (A.inv_mem b.2)) ((a : G)⁻¹) (A.inv_mem a.2)
    show t * ((a : G) * b) * t⁻¹ * ((a : G) * b)⁻¹ =
      (t * (a : G) * t⁻¹ * (a : G)⁻¹) * (t * (b : G) * t⁻¹ * (b : G)⁻¹)
    calc t * ((a : G) * b) * t⁻¹ * ((a : G) * b)⁻¹
        = (t * (a : G) * t⁻¹) * ((t * (b : G) * t⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
      _ = (t * (a : G) * t⁻¹) * ((a : G)⁻¹ * (t * (b : G) * t⁻¹ * (b : G)⁻¹)) := by rw [hcomm]
      _ = _ := by group)
  have hrange : φ.range ≤ V₀.subgroupOf A := by
    rintro _ ⟨a, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (htriv a a.2)
  have hrcard : Nat.card φ.range ≤ 2 := by
    have h1 := Subgroup.card_le_of_le hrange
    have h2 : Nat.card (V₀.subgroupOf A) = Nat.card V₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe cb.V₀_le).toEquiv
    omega
  have hkcard : 8 ≤ Nat.card φ.ker := by
    have h1 := UAbs.card_eq_range_mul_ker φ
    have h2 : Nat.card ↥A = 16 := hA16
    have hrpos : 0 < Nat.card φ.range := Nat.card_pos
    have hkpos : 0 < Nat.card φ.ker := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : Nat.card φ.range * Nat.card φ.ker ≤ 2 * 7 := Nat.mul_le_mul hrcard (by omega)
    omega
  obtain ⟨u, hu, hu1, huz⟩ := Glob.exists_mem_ne_of_three_le (W := φ.ker) (by omega) 1
    (⟨z, cb.V₀_le cb.z_mem⟩ : ↥A)
  have hu' : t * (u : G) * t⁻¹ = (u : G) := by
    have := congrArg Subtype.val (MonoidHom.mem_ker.mp hu)
    simp only [φ, MonoidHom.mk'_apply, OneMemClass.coe_one] at this
    exact mul_inv_eq_one.mp this
  have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have huz' : (u : G) ≠ z := fun h => huz (Subtype.ext h)
  obtain ⟨x, hxN, hx⟩ := htrans (u : G) u.2 hu1'
  have hgN : x⁻¹ * t * x ∈ normalizer (A : Set G) :=
    (normalizer (A : Set G)).mul_mem
      ((normalizer (A : Set G)).mul_mem ((normalizer (A : Set G)).inv_mem hxN) htmem.2) hxN
  have hgz : (x⁻¹ * t * x) * z = z * (x⁻¹ * t * x) := by
    have h1 : (x⁻¹ * t * x) * z * (x⁻¹ * t * x)⁻¹ = z := by
      calc (x⁻¹ * t * x) * z * (x⁻¹ * t * x)⁻¹
          = x⁻¹ * (t * (x * z * x⁻¹) * t⁻¹) * x := by group
        _ = x⁻¹ * (t * (u : G) * t⁻¹) * x := by rw [hx]
        _ = x⁻¹ * (u : G) * x := by rw [hu']
        _ = z := by rw [← hx]; group
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1
  obtain ⟨m, hm, hmact⟩ := cb.cent hv _ hgN hgz
  obtain ⟨j, hj⟩ := hact m hm
  have hgV : ∀ c ∈ V₀, (x⁻¹ * t * x) * c * (x⁻¹ * t * x)⁻¹ ∈ V₀ := by
    intro c hc
    rw [hmact c (cb.V₀_le hc), cb.act_C m hm c hc]; exact hc
  have hgk : (x⁻¹ * t * x) ^ (2 ^ k) = 1 := by
    rw [pow_conj_eq, htk]; group
  have hgj : ∃ j : ℕ, ∀ a ∈ A, (x⁻¹ * t * x) * a * (x⁻¹ * t * x)⁻¹ *
      (g₀ ^ j * a * (g₀ ^ j)⁻¹)⁻¹ ∈ V₀ := ⟨j, fun a ha => by rw [hmact a ha]; exact hj a ha⟩
  have hgtriv := triv_mod hg₀N h7 hfpf hgV hgj k hgk hAV
  have hxA : x⁻¹ * a₀ * x ∈ A := by
    have h := (Subgroup.mem_normalizer_iff.mp ((normalizer (A : Set G)).inv_mem hxN) a₀).mp ha₀
    simpa using h
  have h1 := hgtriv _ hxA
  have h2 : (x⁻¹ * t * x) * (x⁻¹ * a₀ * x) * (x⁻¹ * t * x)⁻¹ * (x⁻¹ * a₀ * x)⁻¹ = x⁻¹ * z * x := by
    calc (x⁻¹ * t * x) * (x⁻¹ * a₀ * x) * (x⁻¹ * t * x)⁻¹ * (x⁻¹ * a₀ * x)⁻¹
        = x⁻¹ * (t * a₀ * t⁻¹ * a₀⁻¹) * x := by group
      _ = x⁻¹ * z * x := by rw [hc₀]
  rw [h2] at h1
  rcases hV₀ _ h1 with h3 | h3
  · apply cb.z_ne
    calc z = x * (x⁻¹ * z * x) * x⁻¹ := by group
      _ = 1 := by rw [h3]; group
  · have h4 : z * x = x * z := by
      calc z * x = x * (x⁻¹ * z * x) := by group
        _ = x * z := by rw [h3]
    have h5 : x * z * x⁻¹ = z := by rw [← h4]; group
    exact huz' (hx.symm.trans h5)

end Final

end CaseBCnt

end CFSG.GH74.Uniqueness.SU.SU8
