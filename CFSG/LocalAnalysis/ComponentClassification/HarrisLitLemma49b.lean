module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma49

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped Pointwise

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

namespace Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem conj_t_subset [Finite X] (hσ : Setup42 h hS w z) :
    {y : X | ∃ m ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X),
      m * t * m⁻¹ = y} ⊆ ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) \ {1, z} ∧
    (((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) \ {1, z}).ncard ≤ 6 := by
  have hMX := hσ.normalizer_T_le_normalizer_X
  have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have hzX : z ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have ht1 : t ≠ 1 := by
    intro ht
    have := h.config.orderOf_eq
    rw [ht, orderOf_one] at this
    exact absurd this (by norm_num)
  have hz1 : z ≠ 1 := by
    intro hz
    have := hσ.z_order
    rw [hz, orderOf_one] at this
    exact absurd this (by norm_num)
  refine ⟨?_, ?_⟩
  · rintro _ ⟨m, hm, rfl⟩
    refine ⟨(mem_normalizer_iff.mp (hMX hm) t).mp htX, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨fun h1 => ht1 ?_, hσ.conj_t_ne_z m⟩
    calc t = m⁻¹ * (m * t * m⁻¹) * m := by group
      _ = 1 := by rw [h1]; group
  · have hsub : ({1, z} : Set X) ⊆
        ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) := by
      rintro y (rfl | rfl)
      · exact one_mem _
      · exact hzX
    rw [Set.ncard_sdiff hsub, Set.ncard_pair hz1.symm,
      ← Nat.card_coe_set_eq ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X)]
    have := hσ.card_X_le
    have hde : Nat.card ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) =
        Nat.card (closure {t, w ^ (orderOf w / 2), z} : Subgroup X) := rfl
    omega

theorem relIndex_ne_six [Finite X] (hKF : AutPSL2FusionInput) (hσ : Setup42 h hS w z) :
    (centralizer ({t} : Set X)).relIndex
      (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)) ≠ 6 := by
  classical
  intro hk
  have htT : t ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := mem_sup_left (mem_sup_left (mem_zpowers t))
  have htM : t ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) :=
    Subgroup.le_normalizer htT
  have hMX := hσ.normalizer_T_le_normalizer_X
  have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have hDT : S ⊓ L ≤ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := le_sup_left.trans' le_sup_right
  have hz1 : z ≠ 1 := by
    intro hz
    have := hσ.z_order
    rw [hz, orderOf_one] at this
    exact absurd this (by norm_num)
  obtain ⟨hOMX, hX6⟩ := hσ.conj_t_subset
  set OM := {y : X | ∃ m ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X),
    m * t * m⁻¹ = y} with hOM
  have hOMcard : OM.ncard = 6 := by rw [hOM, ncard_conj_orbit _ htM, hk]
  have hOMeq := Set.eq_of_subset_of_ncard_le hOMX (by omega)
  have hall : ∀ x ∈ closure {t, w ^ (orderOf w / 2), z}, x ≠ 1 → x ≠ z →
      ∃ m ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X),
        m * t * m⁻¹ = x := by
    intro x hx h1 hxz
    have : x ∈ OM := by
      rw [hOMeq]
      refine ⟨hx, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h1, hxz⟩
    exact this
  have hzT : ∀ τ ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w, τ ^ 2 = 1 → ∀ g : X, g * τ * g⁻¹ = z →
      τ ∈ S ⊓ L := by
    intro τ hτ hτ2 g hg
    obtain ⟨h₁, hh₁H, hh₁X⟩ := hσ.exists_conj_mem_X hKF hτ hτ2
    by_cases hx1 : h₁ * τ * h₁⁻¹ = 1
    · exfalso
      have hτ1 : τ = 1 := by
        calc τ = h₁⁻¹ * (h₁ * τ * h₁⁻¹) * h₁ := by group
          _ = 1 := by rw [hx1]; group
      apply hz1
      rw [← hg, hτ1]
      group
    by_cases hxz : h₁ * τ * h₁⁻¹ = z
    · refine ⟨hσ.T_le hτ, ?_⟩
      have hτz : τ = h₁⁻¹ * z * h₁ := by rw [← hxz]; group
      rw [hτz]
      have := (mem_normalizer_iff.mp (inv_mem (h.centralizer_le_normalizer hh₁H)) z).mp
        hσ.z_mem.2
      simpa using this
    · exfalso
      obtain ⟨m, -, hmx⟩ := hall _ hh₁X hx1 hxz
      apply hσ.conj_t_ne_z (g * h₁⁻¹ * m)
      calc g * h₁⁻¹ * m * t * (g * h₁⁻¹ * m)⁻¹ = g * h₁⁻¹ * (m * t * m⁻¹) * h₁ * g⁻¹ := by
            group
        _ = g * h₁⁻¹ * (h₁ * τ * h₁⁻¹) * h₁ * g⁻¹ := by rw [hmx]
        _ = g * τ * g⁻¹ := by group
        _ = z := hg
  have hDM : ∀ m ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X),
      ∀ d ∈ S ⊓ L, m * d * m⁻¹ ∈ S ⊓ L := by
    intro m hm d hd
    have key : ∀ y ∈ S ⊓ L, y ^ 2 = 1 → m * y * m⁻¹ ∈ S ⊓ L := by
      intro y hy hy2
      by_cases hy1 : y = 1
      · rw [hy1, mul_one, mul_inv_cancel]
        exact one_mem _
      obtain ⟨g, -, hg⟩ := hσ.exists_conj_eq_z hKF hy hy2 hy1
      refine hzT _ ((mem_normalizer_iff.mp hm y).mp (hDT hy)) ?_ (g * m⁻¹) ?_
      · rw [show (m * y * m⁻¹) ^ 2 = m * y ^ 2 * m⁻¹ by rw [sq, sq]; group, hy2]
        group
      · rw [show g * m⁻¹ * (m * y * m⁻¹) * (g * m⁻¹)⁻¹ = g * y * g⁻¹ by group, hg]
    obtain ⟨y₁, hy₁, y₂, hy₂, hy₁2, hy₂2, rfl⟩ := hσ.exists_mul_of_sq_eq_one hd
    rw [show m * (y₁ * y₂) * m⁻¹ = (m * y₁ * m⁻¹) * (m * y₂ * m⁻¹) by group]
    exact mul_mem (key y₁ hy₁ hy₁2) (key y₂ hy₂ hy₂2)
  set N := normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) ⊓
    centralizer ((S ⊓ L : Subgroup X) : Set X) with hN
  have hoddN : ∀ g ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X),
      Odd (orderOf g) → g ∈ N := fun g hg ho =>
    Subgroup.mem_inf.mpr ⟨hg, mem_centralizer_iff.mpr fun d hd =>
      (hσ.comm_of_odd ho (hDM g hg) hd).symm⟩
  have hNM : ∀ m ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X),
      ∀ n ∈ N, m * n * m⁻¹ ∈ N := by
    intro m hm n hn
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hm (Subgroup.mem_inf.mp hn).1) (inv_mem hm),
      mem_centralizer_iff.mpr fun d hd => ?_⟩
    have hd' : m⁻¹ * d * m ∈ S ⊓ L := by simpa using hDM m⁻¹ (inv_mem hm) d hd
    have hc := mem_centralizer_iff.mp (Subgroup.mem_inf.mp hn).2 _ hd'
    calc d * (m * n * m⁻¹) = m * ((m⁻¹ * d * m) * n) * m⁻¹ := by group
      _ = m * (n * (m⁻¹ * d * m)) * m⁻¹ := by rw [hc]
      _ = m * n * m⁻¹ * d := by group
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₃, hP₃⟩ := exists_isSylowOf 3
    (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X))
  have hP₃t : ∃ g ∈ P₃, g * t * g⁻¹ ≠ t := by
    by_contra hcon
    push Not at hcon
    have hle : P₃ ≤ centralizer ({t} : Set X) ⊓
        normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) := fun g hg =>
      Subgroup.mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (by
        calc g * t = (g * t * g⁻¹) * g := by group
          _ = t * g := by rw [hcon g hg]), hP₃.le hg⟩
    have h1 := Subgroup.relIndex_mul_card (H := centralizer ({t} : Set X))
      (K := normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X))
    rw [hk] at h1
    have h2 := Subgroup.card_dvd_of_le hle
    rw [hP₃.card_eq] at h2
    have h3 : 3 ^ ((Nat.card (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) :
        Set X))).factorization 3 + 1) ∣
        Nat.card (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)) := by
      rw [pow_succ, mul_comm]
      calc _ ∣ 6 * Nat.card (centralizer ({t} : Set X) ⊓
            normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) :
              Subgroup X) := Nat.mul_dvd_mul (by norm_num : 3 ∣ 6) h2
        _ = _ := h1
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' Nat.prime_three h3
  obtain ⟨g, hgP, hgt⟩ := hP₃t
  have hgM := hP₃.le hgP
  obtain ⟨c, hc⟩ : ∃ c : ℕ, orderOf g = 3 ^ c := by
    obtain ⟨c, hc⟩ := IsPGroup.iff_orderOf.mp hP₃.isPGroup ⟨g, hgP⟩
    exact ⟨c, by rwa [Subgroup.orderOf_mk] at hc⟩
  have hgodd : Odd (orderOf g) := by
    rw [hc]
    exact Odd.pow (by decide)
  have hgN := hoddN g hgM hgodd
  have hNt : ∀ n ∈ N, n ∈ centralizer ({t} : Set X) →
      n ∈ centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) := by
    intro n hn hnt
    have hnM := (Subgroup.mem_inf.mp hn).1
    have hSMt : IsSylowOf 2 S (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) :
        Set X) ⊓ centralizer ({t} : Set X)) :=
      hS.of_le (le_inf hσ.S_le_normalizer_T hS.le) inf_le_right
    have hconjNt : ∀ m ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) :
        Set X) ⊓ centralizer ({t} : Set X), ∀ x ∈ N ⊓ centralizer ({t} : Set X),
          m * x * m⁻¹ ∈ N ⊓ centralizer ({t} : Set X) := fun m hm x hx =>
      Subgroup.mem_inf.mpr ⟨hNM m (Subgroup.mem_inf.mp hm).1 x (Subgroup.mem_inf.mp hx).1,
        mul_mem (mul_mem (Subgroup.mem_inf.mp hm).2 (Subgroup.mem_inf.mp hx).2)
          (inv_mem (Subgroup.mem_inf.mp hm).2)⟩
    have hXsyl := hSMt.inf_of_le_normalizer (N := N ⊓ centralizer ({t} : Set X))
      (le_inf (fun x hx => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1)
        (fun x hx => (Subgroup.mem_inf.mp hx).2))
      (fun m hm => by
        rw [mem_normalizer_iff]
        intro x
        refine ⟨hconjNt m hm x, fun hx => ?_⟩
        have := hconjNt m⁻¹ (inv_mem hm) _ hx
        simpa [mul_assoc] using this)
    have hSX : S ⊓ (N ⊓ centralizer ({t} : Set X)) = closure {t, w ^ (orderOf w / 2), z} := by
      rw [← hσ.centralizer_D]
      ext x
      simp only [Subgroup.mem_inf, hN]
      constructor
      · rintro ⟨hxS, ⟨-, hxD⟩, -⟩
        exact ⟨hxS, hxD⟩
      · rintro ⟨hxS, hxD⟩
        exact ⟨hxS, ⟨hσ.S_le_normalizer_T hxS, hxD⟩, hS.le hxS⟩
    rw [hSX] at hXsyl
    obtain ⟨a, b, i, j, hb, hord, hne⟩ := exists_odd_two_parts n (orderOf_pos n)
    rw [hne]
    refine mul_mem (zpow_mem ?_ i) (zpow_mem ?_ j)
    ·
      refine hσ.mem_centralizer_X_of_odd (pow_mem hnM _) (pow_mem hnt _) ?_
      have hdvd : orderOf (n ^ 2 ^ a) ∣ b :=
        orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, ← hord, pow_orderOf_eq_one])
      exact Odd.of_dvd_nat hb hdvd
    ·
      have hn2 : (n ^ b) ^ 2 ^ a = 1 := by rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
      have hz2 : IsPGroup 2 (zpowers (n ^ b)) := by
        obtain ⟨k, -, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hn2)
        exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk'])
      have hnbN : n ^ b ∈ normalizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) :
          Set X) := hMX (pow_mem hnM b)
      have hP := hz2.to_sup_of_normal_right' hXsyl.isPGroup (zpowers_le.mpr hnbN)
      have hle : zpowers (n ^ b) ⊔ closure {t, w ^ (orderOf w / 2), z} ≤
          N ⊓ centralizer ({t} : Set X) :=
        sup_le (zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨pow_mem hn _, pow_mem hnt _⟩))
          (hSX ▸ inf_le_right)
      have heq := hXsyl.eq_of_le le_sup_right hle hP
      have hmem : n ^ b ∈ closure {t, w ^ (orderOf w / 2), z} := by
        rw [← heq]
        exact mem_sup_left (mem_zpowers _)
      exact mem_centralizer_iff.mpr fun x hx => hσ.X_comm hx hmem
  have hNX : N ≤ normalizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) :=
    fun n hn => hMX (Subgroup.mem_inf.mp hn).1
  let φ : ↥N →* MulAut ↥(closure {t, w ^ (orderOf w / 2), z}) :=
    (normalizerConj (closure {t, w ^ (orderOf w / 2), z})).comp (Subgroup.inclusion hNX)
  have hφ : ∀ (n : ↥N) (x : ↥(closure {t, w ^ (orderOf w / 2), z})),
      ((φ n x : ↥(closure {t, w ^ (orderOf w / 2), z})) : X) = (n : X) * x * (n : X)⁻¹ :=
    fun _ _ => rfl
  have hker : ∀ n : ↥N, n ∈ φ.ker ↔ (n : X) ∈ centralizer ({t} : Set X) := by
    intro n
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1
      have h2 := congrArg (fun ψ : MulAut ↥(closure {t, w ^ (orderOf w / 2), z}) =>
        ((ψ ⟨t, htX⟩ : ↥(closure {t, w ^ (orderOf w / 2), z})) : X)) h1
      simp only [hφ, MulAut.one_apply] at h2
      rw [mem_centralizer_singleton_iff]
      calc (n : X) * t = ((n : X) * t * (n : X)⁻¹) * n := by group
        _ = t * n := by rw [h2]
    · intro hnt
      have hnX := hNt n n.2 hnt
      ext x
      rw [hφ, MulAut.one_apply]
      have hc := mem_centralizer_iff.mp hnX x x.2
      calc (n : X) * x * (n : X)⁻¹ = (x * n) * (n : X)⁻¹ := by rw [hc]
        _ = x := by group
  have htN : t ∈ N := Subgroup.mem_inf.mpr ⟨htM, mem_centralizer_iff.mpr fun d hd =>
    mem_centralizer_singleton_iff.mp (h.config.le_centralizer hd.2)⟩
  have hcardR : Nat.card φ.range = (centralizer ({t} : Set X)).relIndex N := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    have h2 := Subgroup.relIndex_mul_card (H := centralizer ({t} : Set X)) (K := N)
    have h3 : Nat.card φ.ker = Nat.card (centralizer ({t} : Set X) ⊓ N : Subgroup X) := by
      have hk' : φ.ker = (centralizer ({t} : Set X)).subgroupOf N := by
        ext n
        rw [hker]
        rfl
      rw [hk', ← Subgroup.card_map_of_injective N.subtype_injective, subgroupOf_map_subtype]
    rw [h3] at h1
    have hpos : 0 < Nat.card (centralizer ({t} : Set X) ⊓ N : Subgroup X) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [h1, mul_comm, h2]
  have hcard6 : Nat.card φ.range ≤ 6 := by
    rw [hcardR, ← ncard_conj_orbit N htN, ← hOMcard]
    exact Set.ncard_le_ncard fun y ⟨n, hn, hny⟩ => ⟨n, (Subgroup.mem_inf.mp hn).1, hny⟩
  have hord : ∀ m ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X),
      ∀ hg' : m * g * m⁻¹ ∈ N, orderOf (φ ⟨m * g * m⁻¹, hg'⟩) = 3 := by
    intro m hm hg'
    have hne1 : φ ⟨m * g * m⁻¹, hg'⟩ ≠ 1 := by
      intro h1
      have h2 := (hker ⟨m * g * m⁻¹, hg'⟩).mp (MonoidHom.mem_ker.mpr h1)
      have hX' : m * g * m⁻¹ ∈ centralizer ((closure {t, w ^ (orderOf w / 2), z} :
          Subgroup X) : Set X) := hNt _ hg' h2
      apply hgt
      have hmt : m * t * m⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} :=
        (mem_normalizer_iff.mp (hMX hm) t).mp htX
      have hc := mem_centralizer_iff.mp hX' _ hmt
      have htg : t * g = g * t := by
        calc t * g = m⁻¹ * ((m * t * m⁻¹) * (m * g * m⁻¹)) * m := by group
          _ = m⁻¹ * ((m * g * m⁻¹) * (m * t * m⁻¹)) * m := by rw [hc]
          _ = g * t := by group
      calc g * t * g⁻¹ = t * g * g⁻¹ := by rw [htg]
        _ = t := by group
    have hdvd1 : orderOf (φ ⟨m * g * m⁻¹, hg'⟩) ∣ 3 ^ c := by
      have h1 := orderOf_map_dvd φ ⟨m * g * m⁻¹, hg'⟩
      rw [Subgroup.orderOf_mk] at h1
      have h2 : orderOf (m * g * m⁻¹) = orderOf g := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      rwa [h2, hc] at h1
    obtain ⟨c', -, hc'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd1
    have hdvd2 : orderOf (φ ⟨m * g * m⁻¹, hg'⟩) ∣ Nat.card φ.range := by
      have h1 := orderOf_dvd_natCard (⟨φ ⟨m * g * m⁻¹, hg'⟩, ⟨_, rfl⟩⟩ : φ.range)
      rw [← Subgroup.orderOf_coe] at h1
      exact h1
    rw [hc'] at hdvd2 ⊢
    have hle : 3 ^ c' ≤ 6 := (Nat.le_of_dvd Nat.card_pos hdvd2).trans hcard6
    rcases c' with _ | _ | c'
    · exfalso
      rw [pow_zero, orderOf_eq_one_iff] at hc'
      exact hne1 hc'
    · rfl
    · exfalso
      have : 9 ≤ 3 ^ (c' + 2) := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ (c' + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have hφg : orderOf (φ ⟨g, hgN⟩) = 3 := by
    have h1 := hord 1 (one_mem _) (by simpa using hgN)
    rwa [show (⟨1 * g * 1⁻¹, by simpa using hgN⟩ : ↥N) = ⟨g, hgN⟩ from
      Subtype.ext (by group)] at h1
  have hcard36 : Nat.card φ.range = 3 ∨ Nat.card φ.range = 6 := by
    have hdvd : 3 ∣ Nat.card φ.range := by
      have h1 := orderOf_dvd_natCard (⟨φ ⟨g, hgN⟩, ⟨_, rfl⟩⟩ : φ.range)
      rw [← Subgroup.orderOf_coe] at h1
      rw [← hφg]
      exact h1
    have hpos : 0 < Nat.card φ.range := Nat.card_pos
    omega
  have hzp : ∀ y ∈ φ.range, orderOf y = 3 → y ∈ zpowers (φ ⟨g, hgN⟩) := by
    intro y hy hy3
    have hK : zpowers (φ ⟨g, hgN⟩) ≤ φ.range := zpowers_le.mpr ⟨_, rfl⟩
    have hKc : Nat.card (zpowers (φ ⟨g, hgN⟩)) = 3 := by rw [Nat.card_zpowers, hφg]
    rcases hcard36 with h3 | h6
    · have heq : zpowers (φ ⟨g, hgN⟩) = φ.range :=
        Subgroup.eq_of_le_of_card_ge hK (by rw [h3, hKc])
      rw [heq]
      exact hy
    · have hidx : ((zpowers (φ ⟨g, hgN⟩)).subgroupOf φ.range).index = 2 := by
        have h1 := ((zpowers (φ ⟨g, hgN⟩)).subgroupOf φ.range).index_mul_card
        have h2 : Nat.card ((zpowers (φ ⟨g, hgN⟩)).subgroupOf φ.range) = 3 := by
          rw [← hKc]
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
        rw [h2, h6] at h1
        omega
      have hsq := Subgroup.sq_mem_of_index_two hidx ⟨y, hy⟩
      have hsq' : y ^ 2 ∈ zpowers (φ ⟨g, hgN⟩) := hsq
      have hy3' : y ^ 3 = 1 := by rw [← hy3, pow_orderOf_eq_one]
      have : y = (y ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hy3', one_mul]
      rw [this]
      exact pow_mem hsq' 2
  have hconj : ∀ m ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X),
      ∃ j : ℕ, ∀ x ∈ closure {t, w ^ (orderOf w / 2), z},
        (m * g * m⁻¹) * x * (m * g * m⁻¹)⁻¹ = g ^ j * x * (g ^ j)⁻¹ := by
    intro m hm
    have hg' := hNM m hm g hgN
    have hmem := hzp _ ⟨_, rfl⟩ (hord m hm hg')
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hmem)
    refine ⟨j, fun x hx => ?_⟩
    have h1 := congrArg (fun ψ : MulAut ↥(closure {t, w ^ (orderOf w / 2), z}) =>
      ((ψ ⟨x, hx⟩ : ↥(closure {t, w ^ (orderOf w / 2), z})) : X)) hj
    rw [← map_pow, hφ, hφ] at h1
    exact h1.symm
  have h4 := hσ.ncard_conj_t_le_four hgM hgt hgodd hconj
  rw [← hOM] at h4
  omega

theorem exists_conj_V [Finite X] (hKF : AutPSL2FusionInput) (hσ : Setup42 h hS w z)
    {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) {n : X}
    (hn : n ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)) :
    ∃ v ∈ V, v * t * v⁻¹ = n * t * n⁻¹ := by
  classical
  have htT : t ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := mem_sup_left (mem_sup_left (mem_zpowers t))
  have htM : t ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) :=
    Subgroup.le_normalizer htT
  have htV : t ∈ V := hSV (h.t_mem hS)
  obtain ⟨hOMX, hX6⟩ := hσ.conj_t_subset
  set OM := {y : X | ∃ m ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X),
    m * t * m⁻¹ = y} with hOM
  set OV := {y : X | ∃ v ∈ V, v * t * v⁻¹ = y} with hOV
  have hOVM : OV ⊆ OM := fun y ⟨v, hv, hvy⟩ => ⟨v, hV.le hv, hvy⟩
  have hkM : OM.ncard = (centralizer ({t} : Set X)).relIndex
      (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)) :=
    ncard_conj_orbit _ htM
  have hkV : OV.ncard = S.relIndex V := by
    rw [hOV, ncard_conj_orbit V htV, ← inf_relIndex_right, inf_comm, hσ.inf_centralizer_t hV hSV]
  have hk6 : OM.ncard ≤ 6 := (Set.ncard_le_ncard hOMX).trans hX6
  have hSMt : IsSylowOf 2 S (centralizer ({t} : Set X) ⊓
      normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)) :=
    hS.of_le (le_inf hS.le hσ.S_le_normalizer_T) inf_le_left
  have h1 := Subgroup.relIndex_mul_card (H := centralizer ({t} : Set X))
    (K := normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X))
  have h2 := Subgroup.relIndex_mul_card (H := S) (K := V)
  rw [inf_of_le_left hSV] at h2
  set k := (centralizer ({t} : Set X)).relIndex
    (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)) with hkdef
  set kV := S.relIndex V with hkVdef
  have hSc := hSMt.card_eq
  have hVc := hV.card_eq
  set A := Nat.card (centralizer ({t} : Set X) ⊓
    normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) : Subgroup X) with hA
  set B := Nat.card (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X))
    with hB
  have hA0 : A ≠ 0 := Nat.card_pos.ne'
  have hB0 : B ≠ 0 := Nat.card_pos.ne'
  have hAe := Nat.ordProj_mul_ordCompl_eq_self A 2
  have hBe := Nat.ordProj_mul_ordCompl_eq_self B 2
  have hAodd : ¬ 2 ∣ ordCompl[2] A := Nat.not_dvd_ordCompl Nat.prime_two hA0
  have hBodd : ¬ 2 ∣ ordCompl[2] B := Nat.not_dvd_ordCompl Nat.prime_two hB0
  have hpos : 0 < 2 ^ A.factorization 2 := by positivity
  have key : k * ordCompl[2] A = kV * ordCompl[2] B := by
    have e1 : k * (2 ^ A.factorization 2 * ordCompl[2] A) = 2 ^ B.factorization 2 *
        ordCompl[2] B := by rw [hAe, hBe, h1]
    have e2 : kV * 2 ^ A.factorization 2 = 2 ^ B.factorization 2 := by rw [← hSc, ← hVc, h2]
    have e3 : 2 ^ B.factorization 2 * ordCompl[2] B =
        kV * 2 ^ A.factorization 2 * ordCompl[2] B := by rw [e2]
    have e4 := e1.trans e3
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc 2 ^ A.factorization 2 * (k * ordCompl[2] A) =
        k * (2 ^ A.factorization 2 * ordCompl[2] A) := by ring
      _ = kV * 2 ^ A.factorization 2 * ordCompl[2] B := e4
      _ = 2 ^ A.factorization 2 * (kV * ordCompl[2] B) := by ring
  have hkVdvd : kV ∣ 2 ^ B.factorization 2 := by
    rw [← hVc, ← h2]
    exact Dvd.intro _ rfl
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hkVdvd
  have hkVpos : 0 < kV := by
    rcases Nat.eq_zero_or_pos kV with h0 | h0
    · rw [h0, zero_mul] at h2
      exact absurd h2.symm Nat.card_pos.ne'
    · exact h0
  have hkV1 : kV ≠ 1 := by
    intro h1'
    exact hσ.ne_of_isSylowOf_normalizer hV hSV
      (le_antisymm hSV (Subgroup.relIndex_eq_one.mp h1'))
  have hcop : Nat.Coprime kV (ordCompl[2] A) := by
    rw [he]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hAodd)
  have hkVk : kV ∣ k := hcop.dvd_of_dvd_mul_right ⟨_, key⟩
  obtain ⟨cc, hcc⟩ := hkVk
  have hccodd : ¬ 2 ∣ cc := by
    intro h2c
    apply hBodd
    have : cc * ordCompl[2] A = ordCompl[2] B := by
      apply Nat.eq_of_mul_eq_mul_left hkVpos
      rw [← key, hcc]
      ring
    rw [← this]
    exact Dvd.dvd.mul_right h2c _
  have hcc1 : cc = 1 := by
    by_contra hne
    have hcc3 : 3 ≤ cc := by
      rcases cc with _ | _ | _ | cc
      · exact absurd (dvd_zero 2) hccodd
      · exact absurd rfl hne
      · exact absurd (dvd_refl 2) hccodd
      · omega
    have hk' : k = 6 := by
      have : kV * 3 ≤ kV * cc := Nat.mul_le_mul_left _ hcc3
      have hkV2 : 2 ≤ kV := by omega
      rw [← hkM] at hcc
      omega
    exact hσ.relIndex_ne_six hKF hk'
  have hOVeq : OV = OM := by
    refine Set.eq_of_subset_of_ncard_le hOVM ?_
    rw [hkM, hkV, hcc, hcc1, mul_one]
  have hmem : n * t * n⁻¹ ∈ OM := ⟨n, hn, rfl⟩
  rw [← hOVeq] at hmem
  exact hmem

end Setup42

end Standing

end CFSG.ComponentClassification.HarrisLit
