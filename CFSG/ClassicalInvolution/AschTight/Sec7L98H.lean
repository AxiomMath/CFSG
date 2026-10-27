module

public import CFSG.ClassicalInvolution.AschTight.Sec7L98F

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_coset_stab {N₀ O : Subgroup G} (hN : N₀ ≤ Subgroup.normalizer (O : Set G))
    (b : G) : ∃ A : Subgroup G, ∀ g : G, g ∈ A ↔ g ∈ N₀ ∧ b⁻¹ * (g * b * g⁻¹) ∈ O := by
  refine ⟨{ carrier := {g | g ∈ N₀ ∧ b⁻¹ * (g * b * g⁻¹) ∈ O}
            mul_mem' := ?_
            one_mem' := ⟨N₀.one_mem, by simp⟩
            inv_mem' := ?_ }, fun g => Iff.rfl⟩
  · rintro g h ⟨hg, hgO⟩ ⟨hh, hhO⟩
    refine ⟨N₀.mul_mem hg hh, ?_⟩
    have h1 : g * (b⁻¹ * (h * b * h⁻¹)) * g⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hN hg) _).mp hhO
    have e : b⁻¹ * (g * h * b * (g * h)⁻¹) =
        (b⁻¹ * (g * b * g⁻¹)) * (g * (b⁻¹ * (h * b * h⁻¹)) * g⁻¹) := by group
    rw [e]
    exact O.mul_mem hgO h1
  · rintro g ⟨hg, hgO⟩
    refine ⟨N₀.inv_mem hg, ?_⟩
    have h1 : g⁻¹ * (b⁻¹ * (g * b * g⁻¹)) * g⁻¹⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hN (N₀.inv_mem hg)) _).mp hgO
    have e : b⁻¹ * (g⁻¹ * b * g⁻¹⁻¹) = (g⁻¹ * (b⁻¹ * (g * b * g⁻¹)) * g⁻¹⁻¹)⁻¹ := by group
    rw [e]
    exact O.inv_mem h1

theorem inf_eq_bot_of_odd_of_isPGroup [Finite G] {O A : Subgroup G} (hO : Odd (Nat.card O))
    (hA : IsPGroup 2 A) : O ⊓ A = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have h1 : orderOf x ∣ Nat.card O := by
    rw [← Subgroup.orderOf_mk x hx.1]
    exact orderOf_dvd_natCard _
  obtain ⟨n, hn⟩ := hA ⟨x, hx.2⟩
  have h2 : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  exact eq_one_of_odd_of_pow_two_pow (Odd.of_dvd_nat hO h1) h2

theorem commutator_mem_oddCoreOf_of_fixed [Finite G] {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    {M U₀ A O : Subgroup G} {w g : G} (hM : M ∈ Ω) (hw : IsUniqueInvolution M w)
    (hU₀ : U₀ ∈ USet Ω) (hU₀M : U₀ ≤ M) (hgM : g ∈ M) (hgU : ∀ y ∈ U₀, g * y * g⁻¹ = y⁻¹)
    {y₀ : G} (hy₀ : y₀ ∈ U₀) (hy₀2 : y₀ * y₀ ≠ 1) (hA2 : IsPGroup 2 A)
    (hAM : ∀ a ∈ A, conjSub a M = M) (hAU : ∀ a ∈ A, ∀ y ∈ U₀, a * y * a⁻¹ = y)
    (hO : Odd (Nat.card O)) (hOU : O ≤ Subgroup.centralizer (U₀ : Set G))
    (hAO : A ≤ Subgroup.normalizer ((O ⊓ M : Subgroup G) : Set G))
    (hgO : g ∈ Subgroup.normalizer ((O ⊓ M : Subgroup G) : Set G))
    (hcomm : ∀ a ∈ A, a * g * a⁻¹ * g⁻¹ ∈ O ⊓ M) :
    ∀ k ∈ M, ∀ a ∈ A, ⁅a, k⁆ ∈ oddCoreOf M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOM : Odd (Nat.card ↥(O ⊓ M)) :=
    Odd.of_dvd_nat hO (Subgroup.card_dvd_of_le inf_le_left)
  have hb : ∀ h ∈ A, g⁻¹ * (h * g * h⁻¹) ∈ O ⊓ M := by
    intro h hh
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgO) _).mp (hcomm h hh)
    rw [inv_inv] at h1
    rw [show g⁻¹ * (h * g * h⁻¹) = g⁻¹ * (h * g * h⁻¹ * g⁻¹) * g by group]
    exact h1
  obtain ⟨o₂, ho₂, hfix⟩ := exists_fixed_mul_of_odd hA2 hOM hAO hb
  set g₂ := g * o₂ with hg₂
  have hg₂M : g₂ ∈ M := M.mul_mem hgM ho₂.2
  have hg₂U : ∀ y ∈ U₀, g₂ * y * g₂⁻¹ = y⁻¹ := by
    intro y hy
    have h1 : o₂ * y * o₂⁻¹ = y := by
      have := Subgroup.mem_centralizer_iff.mp (hOU ho₂.1) y hy
      calc o₂ * y * o₂⁻¹ = y * o₂ * o₂⁻¹ := by rw [this]
        _ = y := by group
    calc g₂ * y * g₂⁻¹ = g * (o₂ * y * o₂⁻¹) * g⁻¹ := by rw [hg₂]; group
      _ = y⁻¹ := by rw [h1, hgU y hy]
  obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g₂).ne'
  set g₃ := g₂ ^ m with hg₃
  have hg₃M : g₃ ∈ M := M.pow_mem hg₂M m
  have hsq : ∀ y ∈ U₀, (g₂ * g₂) * y * (g₂ * g₂)⁻¹ = y := by
    intro y hy
    have hyi : y⁻¹ ∈ U₀ := U₀.inv_mem hy
    calc (g₂ * g₂) * y * (g₂ * g₂)⁻¹ = g₂ * (g₂ * y * g₂⁻¹) * g₂⁻¹ := by group
      _ = y := by rw [hg₂U y hy, hg₂U _ hyi, inv_inv]
  have hpow2 : ∀ n : ℕ, ∀ y ∈ U₀, (g₂ * g₂) ^ n * y * ((g₂ * g₂) ^ n)⁻¹ = y := by
    intro n
    induction n with
    | zero => intro y _; simp
    | succ n ih =>
      intro y hy
      rw [pow_succ]
      calc (g₂ * g₂) ^ n * (g₂ * g₂) * y * ((g₂ * g₂) ^ n * (g₂ * g₂))⁻¹
          = (g₂ * g₂) ^ n * ((g₂ * g₂) * y * (g₂ * g₂)⁻¹) * ((g₂ * g₂) ^ n)⁻¹ := by group
        _ = y := by rw [hsq y hy, ih y hy]
  have hg₃U : ∀ y ∈ U₀, g₃ * y * g₃⁻¹ = y⁻¹ := by
    intro y hy
    obtain ⟨k, rfl⟩ := hm
    have e : g₃ = (g₂ * g₂) ^ k * g₂ := by
      rw [hg₃, pow_succ, pow_mul, pow_two]
    have hyi : y⁻¹ ∈ U₀ := U₀.inv_mem hy
    calc g₃ * y * g₃⁻¹ = (g₂ * g₂) ^ k * (g₂ * y * g₂⁻¹) * ((g₂ * g₂) ^ k)⁻¹ := by rw [e]; group
      _ = y⁻¹ := by rw [hg₂U y hy, hpow2 k _ hyi]
  have hg₃2 : IsPGroup 2 (Subgroup.zpowers g₃) := by
    have h1 : g₃ ^ 2 ^ e = 1 := by
      rw [hg₃, ← pow_mul, mul_comm, ← he, pow_orderOf_eq_one]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hAg₃ : ∀ a ∈ A, a * g₃ * a⁻¹ = g₃ := by
    intro a ha
    rw [hg₃, ← conj_pow, hfix a ha]
  have hg₃N : g₃ ∈ Subgroup.normalizer (U₀ : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [natCard_conjSub])
    rintro _ ⟨y, hy, rfl⟩
    change g₃ * y * g₃⁻¹ ∈ U₀
    rw [hg₃U y hy]
    exact U₀.inv_mem hy
  have hU₀2 : IsPGroup 2 U₀ := Sec6Gen.isPGroup_of_mem_USet hΩ hU₀
  have hQ₃2 : IsPGroup 2 ↥(U₀ ⊔ Subgroup.zpowers g₃) :=
    IsPGroup.to_sup_of_normal_left' hU₀2 hg₃2 (Subgroup.zpowers_le.mpr hg₃N)
  have hQ₃M : U₀ ⊔ Subgroup.zpowers g₃ ≤ M := sup_le hU₀M (Subgroup.zpowers_le.mpr hg₃M)
  obtain ⟨R₀, -, M₀, hM₀, hR₀, hU₀R₀, hU₀c, hcard, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU₀
  have hMM : M₀ = M := Sec6Gen.eq_of_le_of_le hΩ hM₀ hM hU₀2 h4 (hU₀R₀.trans hR₀.1) hU₀M
  subst hMM
  have hg₃U₀ : g₃ ∉ U₀ := by
    intro h
    apply hy₀2
    have hc : g₃ * y₀ = y₀ * g₃ := by
      obtain ⟨gen, hgen⟩ := hU₀c.exists_generator
      obtain ⟨m₁, hm₁⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨g₃, h⟩)
      obtain ⟨m₂, hm₂⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨y₀, hy₀⟩)
      have e1 : g₃ = (gen : G) ^ m₁ := by simpa using (congrArg Subtype.val hm₁).symm
      have e2 : y₀ = (gen : G) ^ m₂ := by simpa using (congrArg Subtype.val hm₂).symm
      rw [e1, e2]
      exact (Commute.zpow_zpow_self (gen : G) m₁ m₂).eq
    have h1 := hg₃U y₀ hy₀
    rw [show g₃ * y₀ * g₃⁻¹ = y₀ by rw [hc]; group] at h1
    calc y₀ * y₀ = y₀ * y₀⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel y₀
  have hlt : U₀ < U₀ ⊔ Subgroup.zpowers g₃ :=
    lt_of_le_of_ne le_sup_left fun h => hg₃U₀ (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers g₃))
  have hcardQ : 2 * Nat.card U₀ ≤ Nat.card ↥(U₀ ⊔ Subgroup.zpowers g₃) := by
    have h1 : Nat.card U₀ < Nat.card ↥(U₀ ⊔ Subgroup.zpowers g₃) :=
      Subgroup.card_lt_of_lt hlt
    obtain ⟨q, hq⟩ := Subgroup.card_dvd_of_le hlt.le
    have h0 : 0 < Nat.card U₀ := Nat.card_pos
    rw [hq] at h1 ⊢
    have hq2 : 2 ≤ q := by
      by_contra h
      interval_cases q <;> simp at h1
    nlinarith
  have hQ₃syl : IsSylow2In (U₀ ⊔ Subgroup.zpowers g₃) M₀ :=
    hR₀.of_natCard_le hQ₃2 hQ₃M (by rw [hcard]; exact hcardQ)
  have hcomm' : ∀ q ∈ U₀ ⊔ Subgroup.zpowers g₃, ∀ a ∈ A, q * a = a * q := by
    intro q hq a ha
    have hle : U₀ ⊔ Subgroup.zpowers g₃ ≤ Subgroup.centralizer ({a} : Set G) := by
      refine sup_le (fun y hy => ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have := hAU a ha y hy
        calc y * a = a * y * a⁻¹ * a := by rw [this]
          _ = a * y := by group
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have := hAg₃ a ha
        calc g₃ * a = a * g₃ * a⁻¹ * a := by rw [this]
          _ = a * g₃ := by group
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hq)
  exact Sec6Gen.commutator_mem_oddCoreOf_of_centralizes hw hQ₃syl hA2 hAM hcomm'

namespace Cfg98

variable {Ω : Set (Subgroup G)} {K J K' X P : Subgroup G} {z j : G} {S : Sylow 2 G}
  {W : Subgroup G} (c : Cfg98 Ω K J K' X P z j S W)
include c

theorem UV_le_L [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T) :
    Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤
      L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j :=
  sup_le (t.huR.trans (c.R_le_L t)) (t.hvT.trans (c.T_le_L t))

theorem CL_decomp [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T)
    (hu : Subgroup.zpowers u = K ⊓ W) (hv : Subgroup.zpowers v = J ⊓ W) {g : G}
    (hgL : g ∈ L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j)
    (hgC : g ∈ Subgroup.centralizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G)) :
    ∃ o ∈ oddCoreOf (L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j ⊓
      Subgroup.centralizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G)),
      ∃ w ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v, g = o * w := by
  set C := L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j ⊓
    Subgroup.centralizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) with hC
  set X6 := (J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G))
    with hX6
  have hCX : C ≤ X6 := fun y hy => t.hf ⟨c.L_le_Y t hu hv hy.1, hy.2⟩
  have hON : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤
      Subgroup.normalizer ((oddCoreOf X6 : Subgroup G) : Set G) := fun w hw =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer (t.UV_le_X hw))
  have hg' : g ∈ oddCoreOf X6 ⊔ (Subgroup.zpowers u ⊔ Subgroup.zpowers v) := t.hXeq ▸ hCX ⟨hgL, hgC⟩
  obtain ⟨o, ho, w, hw, rfl⟩ := Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer hON hg'
  refine ⟨o, ?_, w, hw, rfl⟩
  have hwC : w ∈ C := ⟨c.UV_le_L t hw, Subgroup.mem_centralizer_iff.mpr fun y hy =>
    t.UV_comm y hy w hw⟩
  have hoC : o ∈ C := by
    have : o = (o * w) * w⁻¹ := by group
    rw [this]
    exact C.mul_mem ⟨hgL, hgC⟩ (C.inv_mem hwC)
  have hle : C ⊓ oddCoreOf X6 ≤ oddCoreOf C := by
    refine Sec6Gen.le_oddCoreOf_of_normal inf_le_left ?_ ?_
    · intro y hy
      exact mem_normalizer_inf (Subgroup.le_normalizer hy)
        (mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer (hCX hy)))
    · have h1 := Subgroup.card_dvd_of_le (inf_le_right : C ⊓ oddCoreOf X6 ≤ oddCoreOf X6)
      exact Odd.of_dvd_nat (oddCoreOf_odd_natCard _) h1
  exact hle ⟨hoC, ho⟩

theorem comm_mem_O [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T)
    (hu : Subgroup.zpowers u = K ⊓ W) (hv : Subgroup.zpowers v = J ⊓ W) {a g b₂ : G}
    (haC : ∀ w ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v, a * w * a⁻¹ = w)
    (haL : a ∈ Subgroup.normalizer
      ((L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j : Subgroup G) : Set G))
    (hab : a * b₂ * a⁻¹ = b₂) (hgL : g ∈ L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j)
    (hb₂L : b₂ ∈ L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j)
    (hb₂fp : ∀ w ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v, b₂ * w * b₂⁻¹ = w → w = 1)
    (hc₁ : g * b₂ * g⁻¹ * b₂ ∈ Subgroup.centralizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G)) :
    a * g * a⁻¹ * g⁻¹ ∈ oddCoreOf (L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j ⊓
      Subgroup.centralizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G)) := by
  set L := L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j with hL
  set UV := Subgroup.zpowers u ⊔ Subgroup.zpowers v with hUV
  set O₁ := oddCoreOf (L ⊓ Subgroup.centralizer (UV : Set G)) with hO₁
  have hgN := L98_le_normalizer Ω UV z j hgL
  have hb₂N := L98_le_normalizer Ω UV z j hb₂L
  have hO₁C : O₁ ≤ Subgroup.centralizer (UV : Set G) := (oddCoreOf_le_self _).trans inf_le_right
  have hdL : a * g * a⁻¹ * g⁻¹ ∈ L := by
    have h1 : a * g * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp haL g).mp hgL
    exact L.mul_mem h1 (L.inv_mem hgL)
  have hdC : a * g * a⁻¹ * g⁻¹ ∈ Subgroup.centralizer (UV : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : g⁻¹ * w * g ∈ UV := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) w).mp hw
      rwa [inv_inv] at this
    have h1 : a⁻¹ * (g⁻¹ * w * g) * a = g⁻¹ * w * g := by
      have := haC _ hw'
      calc a⁻¹ * (g⁻¹ * w * g) * a = a⁻¹ * (a * (g⁻¹ * w * g) * a⁻¹) * a := by rw [this]
        _ = g⁻¹ * w * g := by group
    calc w * (a * g * a⁻¹ * g⁻¹) = a * g * (g⁻¹ * w * g) * a⁻¹ * g⁻¹ := by
          rw [show a * g * (g⁻¹ * w * g) * a⁻¹ * g⁻¹ = a * w * g * a⁻¹ * g⁻¹ by group]
          rw [show a * w = w * a by
            have := haC w hw
            calc a * w = a * w * a⁻¹ * a := by group
              _ = w * a := by rw [this]]
          group
      _ = a * g * (a⁻¹ * (g⁻¹ * w * g) * a) * a⁻¹ * g⁻¹ := by rw [h1]
      _ = (a * g * a⁻¹ * g⁻¹) * w := by group
  obtain ⟨od, hod, wd, hwd, hd⟩ := c.CL_decomp t hu hv hdL hdC
  obtain ⟨oc, hoc, wc, hwc, hc⟩ := c.CL_decomp t hu hv
    (L.mul_mem (L.mul_mem (L.mul_mem hgL hb₂L) (L.inv_mem hgL)) hb₂L) hc₁
  have hkey : a * (g * b₂ * g⁻¹ * b₂) * a⁻¹ =
      (a * g * a⁻¹ * g⁻¹) * (g * b₂ * g⁻¹ * b₂) * (b₂⁻¹ * (a * g * a⁻¹ * g⁻¹)⁻¹ * b₂) := by
    have hab' : a * b₂⁻¹ * a⁻¹ = b₂⁻¹ := by
      calc a * b₂⁻¹ * a⁻¹ = (a * b₂ * a⁻¹)⁻¹ := by group
        _ = b₂⁻¹ := by rw [hab]
    calc a * (g * b₂ * g⁻¹ * b₂) * a⁻¹
        = (a * g * a⁻¹) * (a * b₂ * a⁻¹) * (a * g * a⁻¹)⁻¹ * (a * b₂ * a⁻¹) := by group
      _ = (a * g * a⁻¹) * b₂ * (a * g * a⁻¹)⁻¹ * b₂ := by rw [hab]
      _ = (a * g * a⁻¹ * g⁻¹) * (g * b₂ * g⁻¹ * b₂) * (b₂⁻¹ * (a * g * a⁻¹ * g⁻¹)⁻¹ * b₂) := by
          group
  have hb₂O : b₂ ∈ Subgroup.normalizer ((O₁ : Subgroup G) : Set G) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer (mem_normalizer_inf (L.le_normalizer hb₂L)
      (normalizer_le_normalizer_centralizer UV hb₂N))
  have haCUV : a ∈ Subgroup.centralizer (UV : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun w hw => by
      have := haC w hw
      calc w * a = a * w * a⁻¹ * a := by rw [this]
        _ = a * w := by group
  have haO : a ∈ Subgroup.normalizer ((O₁ : Subgroup G) : Set G) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer (mem_normalizer_inf haL
      (normalizer_le_normalizer_centralizer UV
        (Subgroup.centralizer_le_normalizer (UV : Set G) haCUV)))
  have hO1UV : O₁ ⊓ UV = ⊥ :=
    inf_eq_bot_of_odd_of_isPGroup (oddCoreOf_odd_natCard _) t.UV_isPGroup
  have hOW : ∀ o ∈ O₁, ∀ w ∈ UV, o * w = w * o := fun o ho w hw =>
    (Subgroup.mem_centralizer_iff.mp (hO₁C ho) w hw).symm
  have hx1 : b₂⁻¹ * wd⁻¹ * b₂ ∈ UV := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hb₂N) wd⁻¹).mp (UV.inv_mem hwd)
    rwa [inv_inv] at this
  have hy1 : b₂⁻¹ * od⁻¹ * b₂ ∈ O₁ := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hb₂O) od⁻¹).mp (O₁.inv_mem hod)
    rwa [inv_inv] at this
  have haoc : a * oc * a⁻¹ ∈ O₁ := (Subgroup.mem_normalizer_iff.mp haO oc).mp hoc
  have hw3 : wd * wc * (b₂⁻¹ * wd⁻¹ * b₂) ∈ UV := UV.mul_mem (UV.mul_mem hwd hwc) hx1
  have heq : (a * oc * a⁻¹) * wc =
      (od * oc * (b₂⁻¹ * od⁻¹ * b₂)) * (wd * wc * (b₂⁻¹ * wd⁻¹ * b₂)) := by
    have hL' : a * (g * b₂ * g⁻¹ * b₂) * a⁻¹ = (a * oc * a⁻¹) * wc := by
      rw [hc, show a * (oc * wc) * a⁻¹ = (a * oc * a⁻¹) * (a * wc * a⁻¹) by group,
        haC wc hwc]
    rw [← hL', hkey, hd, hc]
    calc od * wd * (oc * wc) * (b₂⁻¹ * (od * wd)⁻¹ * b₂)
        = od * (wd * oc) * wc * (b₂⁻¹ * wd⁻¹ * b₂) * (b₂⁻¹ * od⁻¹ * b₂) := by group
      _ = od * (oc * wd) * wc * (b₂⁻¹ * wd⁻¹ * b₂) * (b₂⁻¹ * od⁻¹ * b₂) := by
          rw [← hOW oc hoc wd hwd]
      _ = od * oc * ((wd * wc * (b₂⁻¹ * wd⁻¹ * b₂)) * (b₂⁻¹ * od⁻¹ * b₂)) := by group
      _ = od * oc * ((b₂⁻¹ * od⁻¹ * b₂) * (wd * wc * (b₂⁻¹ * wd⁻¹ * b₂))) := by
          rw [hOW _ hy1 _ hw3]
      _ = od * oc * (b₂⁻¹ * od⁻¹ * b₂) * (wd * wc * (b₂⁻¹ * wd⁻¹ * b₂)) := by group
  have hO' : od * oc * (b₂⁻¹ * od⁻¹ * b₂) ∈ O₁ := O₁.mul_mem (O₁.mul_mem hod hoc) hy1
  have h1 : (od * oc * (b₂⁻¹ * od⁻¹ * b₂))⁻¹ * (a * oc * a⁻¹) =
      (wd * wc * (b₂⁻¹ * wd⁻¹ * b₂)) * wc⁻¹ := by
    calc (od * oc * (b₂⁻¹ * od⁻¹ * b₂))⁻¹ * (a * oc * a⁻¹)
        = (od * oc * (b₂⁻¹ * od⁻¹ * b₂))⁻¹ * ((a * oc * a⁻¹) * wc) * wc⁻¹ := by group
      _ = (wd * wc * (b₂⁻¹ * wd⁻¹ * b₂)) * wc⁻¹ := by rw [heq]; group
  have h2 : (wd * wc * (b₂⁻¹ * wd⁻¹ * b₂)) * wc⁻¹ ∈ O₁ ⊓ UV :=
    ⟨h1 ▸ O₁.mul_mem (O₁.inv_mem hO') haoc, UV.mul_mem hw3 (UV.inv_mem hwc)⟩
  rw [hO1UV, Subgroup.mem_bot] at h2
  have h3 : wd * (b₂⁻¹ * wd⁻¹ * b₂) = 1 := by
    have hc' : wc * (b₂⁻¹ * wd⁻¹ * b₂) = (b₂⁻¹ * wd⁻¹ * b₂) * wc := t.UV_comm _ hwc _ hx1
    calc wd * (b₂⁻¹ * wd⁻¹ * b₂) = (wd * wc * (b₂⁻¹ * wd⁻¹ * b₂)) * wc⁻¹ := by
          rw [mul_assoc wd wc, hc']; group
      _ = 1 := h2
  have h4 : b₂ * wd * b₂⁻¹ = wd := by
    have h5 : b₂⁻¹ * wd⁻¹ * b₂ = wd⁻¹ := eq_inv_of_mul_eq_one_right h3
    calc b₂ * wd * b₂⁻¹ = (b₂ * wd⁻¹ * b₂⁻¹)⁻¹ := by group
      _ = (b₂ * (b₂⁻¹ * wd⁻¹ * b₂) * b₂⁻¹)⁻¹ := by rw [h5]
      _ = wd := by group
  have h6 := hb₂fp wd hwd h4
  rw [hd, h6, mul_one]
  exact hod

end Cfg98

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
