module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7.MS

variable {G : Type} [Group G]

theorem sq_one_of_inv {z : G} (hzz : z * z = 1) : z⁻¹ = z :=
  inv_eq_of_mul_eq_one_right hzz

theorem ca_of_fix {M H : Subgroup G} {z σ : G} (hzz : z * z = 1)
    (hzσ : z * σ = σ * z) (hσ3 : σ ^ 3 = 1)
    (hzH : ∀ g : G, g * z = z * g → g ∈ H) (hMH : M ⊓ H = Subgroup.zpowers σ)
    {m : G} (hm : m ∈ M) (hp : z * m * z⁻¹ * m⁻¹ ∈ Subgroup.zpowers σ) :
    m ∈ Subgroup.zpowers σ := by
  have hz' : z⁻¹ = z := sq_one_of_inv hzz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
  have hzk : z * σ ^ k = σ ^ k * z := (Commute.zpow_right hzσ k).eq
  have hzp : z * σ ^ k * z⁻¹ = σ ^ k := by
    rw [hz', hzk, mul_assoc, hzz, mul_one]
  have hpcube : (σ ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ3, one_zpow]
  have hzm : z * m * z⁻¹ = σ ^ k * m := by
    rw [hk, inv_mul_cancel_right]
  have hz2 : ∀ x : G, z * (z * x * z⁻¹) * z⁻¹ = x := fun x => by
    rw [hz']
    calc z * (z * x * z) * z = (z * z) * x * (z * z) := by group
      _ = x := by rw [hzz, one_mul, mul_one]
  have hm2 : m = σ ^ k * (σ ^ k * m) := by
    calc m = z * (z * m * z⁻¹) * z⁻¹ := (hz2 m).symm
      _ = z * (σ ^ k * m) * z⁻¹ := by rw [hzm]
      _ = (z * σ ^ k * z⁻¹) * (z * m * z⁻¹) := by group
      _ = σ ^ k * (σ ^ k * m) := by rw [hzp, hzm]
  have hpp : σ ^ k * σ ^ k = 1 := by
    have h : (σ ^ k * σ ^ k) * m = 1 * m := by
      rw [one_mul, mul_assoc, ← hm2]
    exact mul_right_cancel h
  have hp1 : σ ^ k = 1 := by
    have h3 : (σ ^ k) ^ 3 = σ ^ k := by
      rw [pow_succ, pow_two, hpp, one_mul]
    rw [← h3, hpcube]
  have hcm : z * m * z⁻¹ = m := by rw [hzm, hp1, one_mul]
  have hmz : m * z = z * m := by
    calc m * z = (z * m * z⁻¹) * z := by rw [hcm]
      _ = z * m := by group
  have hmH : m ∈ H := hzH m hmz
  have : m ∈ M ⊓ H := ⟨hm, hmH⟩
  rw [hMH] at this
  exact this

theorem comm_of_inv {N M : Subgroup G} {z : G}
    (hNc : ∀ n ∈ N, ∀ m ∈ M, n * m = m * n)
    (hΦ : ∀ m ∈ M, z * m * z⁻¹ * m ∈ N) :
    ∀ x ∈ M, ∀ y ∈ M, x⁻¹ * y⁻¹ * x * y ∈ N := by
  intro x hx y hy
  have hxy : x * y ∈ M := mul_mem hx hy
  have hvx := hΦ x hx
  have hvy := hΦ y hy
  have hvxy := hΦ (x * y) hxy
  have hcomm : x⁻¹ * (z * y * z⁻¹ * y) = (z * y * z⁻¹ * y) * x⁻¹ :=
    (hNc _ hvy x⁻¹ (inv_mem hx)).symm
  have key : z * (x * y) * z⁻¹ * (x * y)
      = (z * x * z⁻¹ * x) * (z * y * z⁻¹ * y) * (x⁻¹ * y⁻¹ * x * y) := by
    calc z * (x * y) * z⁻¹ * (x * y)
        = (z * x * z⁻¹ * x) * (x⁻¹ * (z * y * z⁻¹ * y)) * (y⁻¹ * x * y) := by group
      _ = (z * x * z⁻¹ * x) * ((z * y * z⁻¹ * y) * x⁻¹) * (y⁻¹ * x * y) := by rw [hcomm]
      _ = (z * x * z⁻¹ * x) * (z * y * z⁻¹ * y) * (x⁻¹ * y⁻¹ * x * y) := by group
  have h2 : (z * x * z⁻¹ * x) * (z * y * z⁻¹ * y) ∈ N := mul_mem hvx hvy
  have h3 : x⁻¹ * y⁻¹ * x * y = ((z * x * z⁻¹ * x) * (z * y * z⁻¹ * y))⁻¹ * (z * (x * y) * z⁻¹ * (x * y)) := by
    rw [key, inv_mul_cancel_left]
  rw [h3]
  exact mul_mem (inv_mem h2) hvxy

theorem inj_aux {N M : Subgroup G} {z : G} (hzz : z * z = 1)
    (hNc : ∀ n ∈ N, ∀ m ∈ M, n * m = m * n)
    (hCA : ∀ m ∈ M, z * m * z⁻¹ * m⁻¹ ∈ N → m ∈ N)
    (hzM : ∀ m ∈ M, z * m * z⁻¹ ∈ M)
    {a b : G} (ha : a ∈ M) (hb : b ∈ M)
    (h : (a⁻¹ * (z * a * z⁻¹))⁻¹ * (b⁻¹ * (z * b * z⁻¹)) ∈ N) : a⁻¹ * b ∈ N := by
  have hA : z * a * z⁻¹ ∈ M := hzM a ha
  set A := z * a * z⁻¹ with hAdef
  set n := (a⁻¹ * A)⁻¹ * (b⁻¹ * (z * b * z⁻¹)) with hndef
  have hB : z * b * z⁻¹ = b * (a⁻¹ * A * n) := by
    rw [hndef]; group
  have hw : b * a⁻¹ ∈ M := mul_mem hb (inv_mem ha)
  have hAn : A * n * A⁻¹ = n := by
    have := hNc n h A hA
    rw [← this]; group
  have hzw : z * (b * a⁻¹) * z⁻¹ = b * a⁻¹ * n := by
    calc z * (b * a⁻¹) * z⁻¹ = (z * b * z⁻¹) * A⁻¹ := by rw [hAdef]; group
      _ = b * (a⁻¹ * A * n) * A⁻¹ := by rw [hB]
      _ = b * a⁻¹ * (A * n * A⁻¹) := by group
      _ = b * a⁻¹ * n := by rw [hAn]
  have hwn : n * (b * a⁻¹) = (b * a⁻¹) * n := hNc n h _ hw
  have hcalc : z * (b * a⁻¹) * z⁻¹ * (b * a⁻¹)⁻¹ = n := by
    rw [hzw, ← hwn]; group
  have hwN : b * a⁻¹ ∈ N := hCA _ hw (by rw [hcalc]; exact h)
  have hwa : (b * a⁻¹) * a = a * (b * a⁻¹) := hNc (b * a⁻¹) hwN a ha
  have e : a⁻¹ * b = b * a⁻¹ := by
    calc a⁻¹ * b = a⁻¹ * (b * a⁻¹) * a := by group
      _ = a⁻¹ * (a * (b * a⁻¹)) := by rw [mul_assoc, hwa]
      _ = b * a⁻¹ := by group
  rw [e]
  exact hwN

theorem gm_coset {N M : Subgroup G} {z : G}
    (hNc : ∀ n ∈ N, ∀ m ∈ M, n * m = m * n)
    (hzN : ∀ n ∈ N, z * n * z⁻¹ = n) (hzM : ∀ m ∈ M, z * m * z⁻¹ ∈ M)
    {a n : G} (ha : a ∈ M) (hn : n ∈ N) :
    (a * n)⁻¹ * (z * (a * n) * z⁻¹) = a⁻¹ * (z * a * z⁻¹) := by
  have e : z * (a * n) * z⁻¹ = (z * a * z⁻¹) * n := by
    rw [show z * (a * n) * z⁻¹ = (z * a * z⁻¹) * (z * n * z⁻¹) by group, hzN n hn]
  rw [e]
  have hX : a⁻¹ * (z * a * z⁻¹) ∈ M := mul_mem (inv_mem ha) (hzM a ha)
  have hc := hNc n hn _ hX
  calc (a * n)⁻¹ * ((z * a * z⁻¹) * n) = n⁻¹ * (a⁻¹ * (z * a * z⁻¹) * n) := by group
    _ = n⁻¹ * ((a⁻¹ * (z * a * z⁻¹)) * n) := by rw [mul_assoc]
    _ = n⁻¹ * (n * (a⁻¹ * (z * a * z⁻¹))) := by rw [← hc]
    _ = a⁻¹ * (z * a * z⁻¹) := by group

theorem zinv_of_ca [Finite G] {M H : Subgroup G} {z σ : G} (hzz : z * z = 1)
    (hzσ : z * σ = σ * z) (hσ3 : σ ^ 3 = 1)
    (hzH : ∀ g : G, g * z = z * g → g ∈ H) (hMH : M ⊓ H = Subgroup.zpowers σ)
    (hzM : ∀ m ∈ M, z * m * z⁻¹ ∈ M) (hσc : ∀ m ∈ M, σ * m = m * σ) :
    ∀ x ∈ M, z * x * z⁻¹ * x ∈ Subgroup.zpowers σ := by
  have hz' : z⁻¹ = z := sq_one_of_inv hzz
  set N : Subgroup G := Subgroup.zpowers σ with hNdef
  have hNc : ∀ n ∈ N, ∀ m ∈ M, n * m = m * n := by
    intro n hn m hm
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    exact ((show Commute σ m from hσc m hm).zpow_left k).eq
  have hzN : ∀ n ∈ N, z * n * z⁻¹ = n := by
    intro n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [hz', (Commute.zpow_right hzσ k).eq, mul_assoc, hzz, mul_one]
  have hCA : ∀ m ∈ M, z * m * z⁻¹ * m⁻¹ ∈ N → m ∈ N :=
    fun m hm hp => ca_of_fix hzz hzσ hσ3 hzH hMH hm hp
  set N' : Subgroup M := N.subgroupOf M with hN'def
  haveI : N'.Normal := ⟨fun n hn g => by
    rw [hN'def, Subgroup.mem_subgroupOf] at hn ⊢
    have hc : (g : G) * n = n * g := (hNc n hn g g.2).symm
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ N
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    exact hn⟩
  let gm : M → M := fun y => ⟨(y : G)⁻¹ * (z * (y : G) * z⁻¹), mul_mem (inv_mem y.2) (hzM _ y.2)⟩
  have hgm : ∀ y : M, (gm y : G) = (y : G)⁻¹ * (z * (y : G) * z⁻¹) := fun y => rfl
  have hrespect : ∀ a b : M, a⁻¹ * b ∈ N' → gm a = gm b := by
    intro a b hab
    have hab' : (a : G)⁻¹ * (b : G) ∈ N := by
      rw [hN'def, Subgroup.mem_subgroupOf] at hab
      simpa using hab
    apply Subtype.ext
    rw [hgm, hgm]
    have := gm_coset hNc hzN hzM a.2 hab'
    rw [mul_inv_cancel_left] at this
    exact this.symm
  let ghat : M ⧸ N' → M ⧸ N' := Quotient.lift
    (fun y : M => (QuotientGroup.mk (gm y) : M ⧸ N'))
    (fun a b hab => congrArg (fun c : M => (QuotientGroup.mk c : M ⧸ N'))
      (hrespect a b (QuotientGroup.leftRel_apply.mp hab)))
  have hghat : ∀ y : M, ghat (QuotientGroup.mk y) = QuotientGroup.mk (gm y) := fun y => rfl
  have hinj : Function.Injective ghat := by
    intro q₁ q₂ hq
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q₂
    rw [hghat, hghat, QuotientGroup.eq] at hq
    rw [hN'def, Subgroup.mem_subgroupOf] at hq
    have hq' : (gm y : G)⁻¹ * (gm x : G) ∈ N := by simpa using hq
    rw [hgm, hgm] at hq'
    have h2 := inj_aux hzz hNc hCA hzM y.2 x.2 hq'
    rw [QuotientGroup.eq, hN'def, Subgroup.mem_subgroupOf]
    simpa using h2
  haveI : Finite (M ⧸ N') := Finite.of_surjective (QuotientGroup.mk : M → M ⧸ N') QuotientGroup.mk_surjective
  have hsurj : Function.Surjective ghat := Finite.injective_iff_surjective.mp hinj
  intro x hx
  obtain ⟨q, hq⟩ := hsurj (QuotientGroup.mk ⟨x, hx⟩)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  rw [hghat, QuotientGroup.eq, hN'def, Subgroup.mem_subgroupOf] at hq
  have hn₀ : (gm y : G)⁻¹ * x ∈ N := by simpa using hq
  rw [hgm] at hn₀
  have hyM : (y : G) ∈ M := y.2
  have hAM : z * (y : G) * z⁻¹ ∈ M := hzM _ y.2
  obtain ⟨n₀, hn₀def⟩ : ∃ n₀ : G, n₀ = ((y : G)⁻¹ * (z * (y : G) * z⁻¹))⁻¹ * x := ⟨_, rfl⟩
  rw [← hn₀def] at hn₀
  have hx_eq : x = ((y : G)⁻¹ * (z * (y : G) * z⁻¹)) * n₀ := by rw [hn₀def]; group
  have hc1 : n₀ * (y : G) = (y : G) * n₀ := hNc n₀ hn₀ _ hyM
  have hc2 : n₀ * (z * (y : G) * z⁻¹) = (z * (y : G) * z⁻¹) * n₀ := hNc n₀ hn₀ _ hAM
  have hz2 : z * (z * (y : G) * z⁻¹) * z⁻¹ = (y : G) := by
    rw [hz']
    calc z * (z * (y : G) * z) * z = (z * z) * (y : G) * (z * z) := by group
      _ = (y : G) := by rw [hzz, one_mul, mul_one]
  have e1 : z * x * z⁻¹ = (z * (y : G) * z⁻¹)⁻¹ * (y : G) * n₀ := by
    rw [hx_eq]
    calc z * ((y : G)⁻¹ * (z * (y : G) * z⁻¹) * n₀) * z⁻¹
        = (z * (y : G)⁻¹ * z⁻¹) * (z * (z * (y : G) * z⁻¹) * z⁻¹) * (z * n₀ * z⁻¹) := by group
      _ = (z * (y : G) * z⁻¹)⁻¹ * (y : G) * n₀ := by
        rw [hz2, hzN n₀ hn₀]
        congr 1
        group
  have e2 : z * x * z⁻¹ * x = n₀ * n₀ := by
    rw [e1, hx_eq]
    calc (z * (y : G) * z⁻¹)⁻¹ * (y : G) * n₀ * ((y : G)⁻¹ * (z * (y : G) * z⁻¹) * n₀)
        = (z * (y : G) * z⁻¹)⁻¹ * ((y : G) * n₀ * (y : G)⁻¹) * (z * (y : G) * z⁻¹) * n₀ := by group
      _ = (z * (y : G) * z⁻¹)⁻¹ * n₀ * (z * (y : G) * z⁻¹) * n₀ := by
        rw [← hc1]; group
      _ = (z * (y : G) * z⁻¹)⁻¹ * ((z * (y : G) * z⁻¹) * n₀) * n₀ := by
        rw [← hc2]; group
      _ = n₀ * n₀ := by group
  rw [e2]
  exact mul_mem hn₀ hn₀

theorem conjP_of_odd [Finite G] {H P B : Subgroup G} {z t c : G}
    (hzC : ∀ g : G, g * z = z * g → g ∈ H)
    (hodd : ∀ S : Subgroup G, S ≤ H → Odd (Nat.card S) →
      Nat.card S ∣ 9 ∧ (Nat.card S = 9 → ∃ h ∈ H, ∀ x ∈ P, h * x * h⁻¹ ∈ S))
    (hP9 : Nat.card P = 9) (hc : c * z * c⁻¹ = t) (hB9 : Nat.card B = 9)
    (hBt : ∀ b ∈ B, t * b = b * t) :
    ∃ w : G, ∀ x : G, x ∈ B ↔ ∃ p ∈ P, w * p * w⁻¹ = x := by
  set S₀ : Subgroup G := B.map (MulAut.conj c⁻¹).toMonoidHom with hS₀
  have hS₀mem : ∀ x : G, x ∈ S₀ ↔ ∃ b ∈ B, c⁻¹ * b * c = x := by
    intro x
    rw [hS₀, Subgroup.mem_map]
    simp [MulAut.conj_apply, mul_assoc]
  have hS₀card : Nat.card S₀ = 9 := by
    rw [hS₀, Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hB9]
  have hS₀H : S₀ ≤ H := by
    intro x hx
    apply hzC
    obtain ⟨b, hb, hbx⟩ := (hS₀mem x).mp hx
    have h1 := hBt b hb
    rw [← hc] at h1
    have hbx' : b = c * x * c⁻¹ := by
      rw [← hbx]; group
    rw [hbx'] at h1
    have h2 : c * (x * z) * c⁻¹ = c * (z * x) * c⁻¹ := by
      calc c * (x * z) * c⁻¹ = (c * x * c⁻¹) * (c * z * c⁻¹) * c * c⁻¹ * c * c⁻¹ := by group
        _ = (c * x * c⁻¹) * (c * z * c⁻¹) := by group
        _ = (c * z * c⁻¹) * (c * x * c⁻¹) := by rw [← h1]
        _ = c * (z * x) * c⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  obtain ⟨h, hhH, hh⟩ := (hodd S₀ hS₀H (by rw [hS₀card]; decide)).2 hS₀card
  set Q : Subgroup G := P.map (MulAut.conj h).toMonoidHom with hQ
  have hQcard : Nat.card Q = 9 := by
    rw [hQ, Subgroup.card_map_of_injective (MulAut.conj h).injective, hP9]
  have hQS : Q = S₀ := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      rw [hQ, Subgroup.mem_map] at hy
      obtain ⟨p, hp, rfl⟩ := hy
      exact hh p hp
    · rw [hQcard, hS₀card]
  refine ⟨c * h, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  ·
    have hy : c⁻¹ * x * c ∈ S₀ := (hS₀mem _).mpr ⟨x, hx, by group⟩
    rw [← hQS, hQ, Subgroup.mem_map] at hy
    obtain ⟨p, hp, hpy⟩ := hy
    refine ⟨p, hp, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hpy
    calc c * h * p * (c * h)⁻¹ = c * (h * p * h⁻¹) * c⁻¹ := by group
      _ = x := by rw [hpy]; group
  · obtain ⟨p, hp, rfl⟩ := hx
    have hy : c⁻¹ * (c * h * p * (c * h)⁻¹) * c ∈ S₀ := by
      rw [← hQS, hQ, Subgroup.mem_map]
      exact ⟨p, hp, by simp [MulAut.conj_apply]; group⟩
    obtain ⟨b, hb, hbx⟩ := (hS₀mem _).mp hy
    have : b = c * h * p * (c * h)⁻¹ := mul_left_cancel (mul_right_cancel hbx)
    rw [← this]; exact hb

theorem conjP_exp_comm {P B : Subgroup G} {w : G} (hPexp : ∀ p ∈ P, p ^ 3 = 1)
    (hPcomm : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p)
    (hiff : ∀ x : G, x ∈ B ↔ ∃ p ∈ P, w * p * w⁻¹ = x) :
    (∀ b ∈ B, b ^ 3 = 1) ∧ (∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) := by
  constructor
  · intro b hb
    obtain ⟨p, hp, rfl⟩ := (hiff b).mp hb
    calc (w * p * w⁻¹) ^ 3 = w * p ^ 3 * w⁻¹ := conj_pow
      _ = 1 := by rw [hPexp p hp]; group
  · intro b hb b' hb'
    obtain ⟨p, hp, rfl⟩ := (hiff b).mp hb
    obtain ⟨q, hq, rfl⟩ := (hiff b').mp hb'
    calc w * p * w⁻¹ * (w * q * w⁻¹) = w * (p * q) * w⁻¹ := by group
      _ = w * (q * p) * w⁻¹ := by rw [hPcomm p hp q hq]
      _ = w * q * w⁻¹ * (w * p * w⁻¹) := by group

theorem card_cent_of_conjP [Finite G] {P B : Subgroup G} {w : G}
    (hiff : ∀ x : G, x ∈ B ↔ ∃ p ∈ P, w * p * w⁻¹ = x) :
    Nat.card (Subgroup.centralizer (B : Set G)) = Nat.card (Subgroup.centralizer (P : Set G)) := by
  have hmap : Subgroup.centralizer (B : Set G) =
      (Subgroup.centralizer (P : Set G)).map (MulAut.conj w).toMonoidHom := by
    ext g
    rw [Subgroup.mem_map]
    constructor
    · intro hg
      refine ⟨w⁻¹ * g * w, ?_, by simp [MulAut.conj_apply]; group⟩
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hpB : w * p * w⁻¹ ∈ B := (hiff _).mpr ⟨p, hp, rfl⟩
      have := (Subgroup.mem_centralizer_iff.mp hg) _ hpB
      calc p * (w⁻¹ * g * w) = w⁻¹ * (w * p * w⁻¹) * g * w := by group
        _ = w⁻¹ * (g * (w * p * w⁻¹)) * w := by rw [← this]; group
        _ = w⁻¹ * g * w * p := by group
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro b hb
      obtain ⟨p, hp, rfl⟩ := (hiff b).mp hb
      have := hy p hp
      show w * p * w⁻¹ * (w * y * w⁻¹) = w * y * w⁻¹ * (w * p * w⁻¹)
      calc w * p * w⁻¹ * (w * y * w⁻¹) = w * (p * y) * w⁻¹ := by group
        _ = w * (y * p) * w⁻¹ := by rw [this]
        _ = w * y * w⁻¹ * (w * p * w⁻¹) := by group
  rw [hmap, Subgroup.card_map_of_injective (MulAut.conj w).injective]

theorem not_le_centralizer_of_card [Finite G] {K B : Subgroup G} {n : ℕ}
    (hcent : ∀ g ∈ K, ∀ b ∈ B, g * b = b * g) (hK : Nat.card K = n)
    (hn : ¬ n ∣ Nat.card (Subgroup.centralizer (B : Set G))) : False := by
  have hle : K ≤ Subgroup.centralizer (B : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hcent g hg b hb).symm
  apply hn
  rw [← hK]
  exact Subgroup.card_dvd_of_le hle

structure VxData (H : Subgroup G) (z t σ τ : G) (M M' P : Subgroup G) : Prop where
  zz : z * z = 1
  zC : ∀ g : G, g * z = z * g → g ∈ H
  zH : ∀ h ∈ H, h * z = z * h
  tH : t ∈ H
  σH : σ ∈ H
  τH : τ ∈ H
  σ3 : σ ^ 3 = 1
  σ1 : σ ≠ 1
  τ3 : τ ^ 3 = 1
  τ1 : τ ≠ 1
  στ : σ * τ = τ * σ
  t2 : t * t = 1
  tσ : t * σ * t⁻¹ = σ⁻¹
  tτ : t * τ * t⁻¹ = τ⁻¹
  ct : ∃ c : G, c * z * c⁻¹ = t
  ctz : ∃ c : G, c * z * c⁻¹ = t * z
  nc : ¬ IsConj σ τ
  P9 : Nat.card P = 9
  Pexp : ∀ p ∈ P, p ^ 3 = 1
  Pcomm : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p
  σP : σ ∈ P
  τP : τ ∈ P
  Pgen : ∀ p ∈ P, ∃ a b : ℤ, σ ^ a * τ ^ b = p
  odd : ∀ S : Subgroup G, S ≤ H → Odd (Nat.card S) →
    Nat.card S ∣ 9 ∧ (Nat.card S = 9 → ∃ h ∈ H, ∀ x ∈ P, h * x * h⁻¹ ∈ S)
  CP : Nat.card (Subgroup.centralizer (P : Set G)) = 162
  Cσ : Nat.card (Subgroup.centralizer {σ}) = 243 * 24
  Nσ : Subgroup.normalizer (Subgroup.zpowers σ : Set G) = Subgroup.centralizer {σ} ⊔ Subgroup.zpowers t
  MC : M ≤ Subgroup.centralizer {σ}
  Mnorm : ∀ g ∈ Subgroup.centralizer {σ}, ∀ m ∈ M, g * m * g⁻¹ ∈ M
  Mt : ∀ m ∈ M, t * m * t⁻¹ ∈ M
  MH : M ⊓ H = Subgroup.zpowers σ
  M243 : Nat.card M = 243
  MB : Nat.card ↥(M ⊓ Subgroup.centralizer {t}) = 9
  MBz : Nat.card ↥(M ⊓ Subgroup.centralizer {t * z}) = 9
  Mτ : Nat.card ↥(M ⊓ Subgroup.centralizer {τ}) = 27
  M'C : M' ≤ Subgroup.centralizer {τ}
  M'norm : ∀ g ∈ Subgroup.centralizer {τ}, ∀ m ∈ M', g * m * g⁻¹ ∈ M'
  M'243 : Nat.card M' = 243
  M'H : M' ⊓ H = Subgroup.zpowers τ

namespace VxData

variable {H M M' P : Subgroup G} {z t σ τ : G}

theorem zσ (d : VxData H z t σ τ M M' P) : z * σ = σ * z := (d.zH σ d.σH).symm

theorem zt (d : VxData H z t σ τ M M' P) : z * t = t * z := (d.zH t d.tH).symm

theorem zinv [Finite G] (d : VxData H z t σ τ M M' P) :
    ∀ x ∈ M, z * x * z⁻¹ * x ∈ Subgroup.zpowers σ := by
  have hzM : ∀ m ∈ M, z * m * z⁻¹ ∈ M := by
    intro m hm
    apply d.Mnorm z _ m hm
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact (d.zσ).symm
  have hσc : ∀ m ∈ M, σ * m = m * σ := by
    intro m hm
    exact Subgroup.mem_centralizer_iff.mp (d.MC hm) σ (Set.mem_singleton σ)
  exact zinv_of_ca d.zz d.zσ d.σ3 d.zC d.MH hzM hσc

end VxData

theorem eq_one_of_inv_comm {σ u n : G} (σ3 : σ ^ 3 = 1)
    (hu : ∀ m ∈ Subgroup.zpowers σ, u * m * u⁻¹ = m⁻¹) (hn : n ∈ Subgroup.zpowers σ)
    (hcomm : u * n = n * u) : n = 1 := by
  have h1 := hu n hn
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one] at h1
  have hnn : n * n = 1 := by
    calc n * n = n * n⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel n
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  have h3 : (σ ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, σ3, one_zpow]
  calc σ ^ k = (σ ^ k) ^ 3 * ((σ ^ k) * (σ ^ k))⁻¹ := by group
    _ = 1 := by rw [h3, hnn]; group

namespace VxData

variable {H M M' P : Subgroup G} {z t σ τ : G}

theorem Ncent [Finite G] (d : VxData H z t σ τ M M' P) :
    ∀ n ∈ Subgroup.zpowers σ, ∀ m ∈ M, n * m = m * n := by
  intro n hn m hm
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  have hσc : Commute σ m := Subgroup.mem_centralizer_iff.mp (d.MC hm) σ (Set.mem_singleton σ)
  exact (hσc.zpow_left k).eq

theorem comm [Finite G] (d : VxData H z t σ τ M M' P) :
    ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers σ := by
  intro x hx y hy
  have := comm_of_inv (z := z) d.Ncent d.zinv x⁻¹ (inv_mem hx) y⁻¹ (inv_mem hy)
  have e : x⁻¹⁻¹ * y⁻¹⁻¹ * x⁻¹ * y⁻¹ = x * y * x⁻¹ * y⁻¹ := by group
  rw [e] at this
  exact this

end VxData

theorem mem_cent_iff {u x : G} : x ∈ Subgroup.centralizer {u} ↔ u * x = x * u := by
  rw [Subgroup.mem_centralizer_iff]
  exact ⟨fun h => (h u (Set.mem_singleton u)), fun h g hg => by
    rw [Set.mem_singleton_iff.mp hg]; exact h⟩

theorem eq_one_of_sq_cube {x : G} (h2 : x * x = 1) (h3 : x ^ 3 = 1) : x = 1 := by
  calc x = x ^ 3 * (x * x)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; group

theorem inv_of_conj_zpowers {u σ : G} (hu : u * σ * u⁻¹ = σ⁻¹) :
    ∀ m ∈ Subgroup.zpowers σ, u * m * u⁻¹ = m⁻¹ := by
  intro m hm
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
  rw [← conj_zpow, hu, inv_zpow]

namespace VxData

variable {H M M' P : Subgroup G} {z t σ τ : G}

theorem conjB [Finite G] (d : VxData H z t σ τ M M' P) {u : G} (hu : ∃ c : G, c * z * c⁻¹ = u)
    (hB9 : Nat.card ↥(M ⊓ Subgroup.centralizer {u}) = 9) :
    ∃ w : G, ∀ x : G, x ∈ M ⊓ Subgroup.centralizer {u} ↔ ∃ p ∈ P, w * p * w⁻¹ = x := by
  obtain ⟨c, hc⟩ := hu
  exact conjP_of_odd d.zC d.odd d.P9 hc hB9 (fun b hb => mem_cent_iff.mp (Subgroup.mem_inf.mp hb).2)

theorem B_facts [Finite G] (d : VxData H z t σ τ M M' P) {u : G}
    (hu : ∃ c : G, c * z * c⁻¹ = u) (hB9 : Nat.card ↥(M ⊓ Subgroup.centralizer {u}) = 9) :
    (∀ b ∈ M ⊓ Subgroup.centralizer {u}, b ^ 3 = 1) ∧
    (∀ b ∈ M ⊓ Subgroup.centralizer {u}, ∀ b' ∈ M ⊓ Subgroup.centralizer {u}, b * b' = b' * b) ∧
    Nat.card (Subgroup.centralizer ((M ⊓ Subgroup.centralizer {u} : Subgroup G) : Set G)) = 162 := by
  obtain ⟨w, hw⟩ := d.conjB hu hB9
  obtain ⟨h1, h2⟩ := conjP_exp_comm d.Pexp d.Pcomm hw
  exact ⟨h1, h2, by rw [card_cent_of_conjP hw]; exact d.CP⟩

theorem zN (d : VxData H z t σ τ M M' P) : ∀ n ∈ Subgroup.zpowers σ, z * n * z⁻¹ = n := by
  intro n hn
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  have hzk : z * σ ^ k = σ ^ k * z := (Commute.zpow_right (d.zσ) k).eq
  rw [hzk, mul_assoc, mul_inv_cancel, mul_one]

theorem zinv_B2 [Finite G] (d : VxData H z t σ τ M M' P) {b : G}
    (hb : b ∈ M ⊓ Subgroup.centralizer {t * z}) : z * b * z⁻¹ = b⁻¹ := by
  have hbM : b ∈ M := (Subgroup.mem_inf.mp hb).1
  have hbu : t * z * b = b * (t * z) := mem_cent_iff.mp (Subgroup.mem_inf.mp hb).2
  have hnN : z * b * z⁻¹ * b ∈ Subgroup.zpowers σ := d.zinv b hbM
  have htzz : Commute (t * z) z := (show Commute t z from d.zt.symm).mul_left (Commute.refl z)
  have hcomm : (t * z) * (z * b * z⁻¹ * b) = (z * b * z⁻¹ * b) * (t * z) :=
    ((((htzz.mul_right hbu).mul_right htzz.inv_right).mul_right hbu)).eq
  have hu : ∀ m ∈ Subgroup.zpowers σ, (t * z) * m * (t * z)⁻¹ = m⁻¹ := by
    intro m hm
    calc (t * z) * m * (t * z)⁻¹ = t * (z * m * z⁻¹) * t⁻¹ := by group
      _ = t * m * t⁻¹ := by rw [d.zN m hm]
      _ = m⁻¹ := inv_of_conj_zpowers d.tσ m hm
  have hn1 : z * b * z⁻¹ * b = 1 := eq_one_of_inv_comm d.σ3 hu hnN hcomm
  calc z * b * z⁻¹ = (z * b * z⁻¹ * b) * b⁻¹ := by group
    _ = b⁻¹ := by rw [hn1, one_mul]

theorem tinv_B2 [Finite G] (d : VxData H z t σ τ M M' P) {b : G}
    (hb : b ∈ M ⊓ Subgroup.centralizer {t * z}) : t * b * t⁻¹ = b⁻¹ := by
  have hbu : t * z * b = b * (t * z) := mem_cent_iff.mp (Subgroup.mem_inf.mp hb).2
  have h1 : t * (z * b * z⁻¹) * t⁻¹ = b := by
    calc t * (z * b * z⁻¹) * t⁻¹ = (t * z) * b * (t * z)⁻¹ := by group
      _ = b := by rw [hbu]; group
  rw [d.zinv_B2 hb] at h1
  calc t * b * t⁻¹ = (t * b⁻¹ * t⁻¹)⁻¹ := by group
    _ = b⁻¹ := by rw [h1]

end VxData

namespace VxData

variable {H M M' P : Subgroup G} {z t σ τ : G}

theorem pow3_zpowers (d : VxData H z t σ τ M M' P) : ∀ n ∈ Subgroup.zpowers σ, n ^ 3 = 1 := by
  intro n hn
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, d.σ3, one_zpow]

theorem N_le_M (d : VxData H z t σ τ M M' P) : Subgroup.zpowers σ ≤ M := by
  rw [Subgroup.zpowers_le]
  exact (Subgroup.mem_inf.mp (d.MH ▸ Subgroup.mem_zpowers σ : σ ∈ M ⊓ H)).1

theorem uv_zero [Finite G] (d : VxData H z t σ τ M M' P) {u v p : G}
    (hu : u ∈ M ⊓ Subgroup.centralizer {t}) (hv : v ∈ M ⊓ Subgroup.centralizer {t * z})
    (hu3 : u ^ 3 = 1) (hp : p ∈ Subgroup.zpowers σ) (huv : u * v = p) : u = 1 ∧ v = 1 := by
  have huM := (Subgroup.mem_inf.mp hu).1
  have hut : t * u = u * t := mem_cent_iff.mp (Subgroup.mem_inf.mp hu).2
  have hvt : t * v * t⁻¹ = v⁻¹ := d.tinv_B2 hv
  have hpc : p * u = u * p := d.Ncent p hp u huM
  have huv_comm : u * v = v * u := by
    have h1 : u * (v * u) = u * (u * v) := by
      calc u * (v * u) = (u * v) * u := by group
        _ = p * u := by rw [huv]
        _ = u * p := hpc
        _ = u * (u * v) := by rw [huv]
    exact (mul_left_cancel h1).symm
  have htu : t * u * t⁻¹ = u := by rw [hut]; group
  have htp : t * p * t⁻¹ = p⁻¹ := inv_of_conj_zpowers d.tσ p hp
  have h2 : u * v⁻¹ = v⁻¹ * u⁻¹ := by
    calc u * v⁻¹ = (t * u * t⁻¹) * (t * v * t⁻¹) := by rw [htu, hvt]
      _ = t * (u * v) * t⁻¹ := by group
      _ = t * p * t⁻¹ := by rw [huv]
      _ = p⁻¹ := htp
      _ = (u * v)⁻¹ := by rw [huv]
      _ = v⁻¹ * u⁻¹ := by group
  have hcomm' : v⁻¹ * u⁻¹ = u⁻¹ * v⁻¹ := by
    calc v⁻¹ * u⁻¹ = (u * v)⁻¹ := by group
      _ = (v * u)⁻¹ := by rw [huv_comm]
      _ = u⁻¹ * v⁻¹ := by group
  have huinv : u = u⁻¹ := mul_right_cancel (h2.trans hcomm')
  have huu : u * u = 1 := by
    have := mul_inv_cancel u
    rw [← huinv] at this
    exact this
  have hu1 : u = 1 := eq_one_of_sq_cube huu hu3
  subst hu1
  have hv_eq : v = p := by rw [one_mul] at huv; exact huv.symm ▸ rfl
  have hvN : v ∈ Subgroup.zpowers σ := by rw [hv_eq]; exact hp
  have hvz : z * v * z⁻¹ = v := d.zN v hvN
  have hvz' : z * v * z⁻¹ = v⁻¹ := d.zinv_B2 hv
  have hvv : v * v = 1 := by
    have h := hvz.symm.trans hvz'
    calc v * v = v * v⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel v
  exact ⟨rfl, eq_one_of_sq_cube hvv (d.pow3_zpowers v hvN)⟩

end VxData

namespace VxData

variable {H M M' P : Subgroup G} {z t σ τ : G}

theorem decomp [Finite G] (d : VxData H z t σ τ M M' P)
    (hB1exp : ∀ b ∈ M ⊓ Subgroup.centralizer {t}, b ^ 3 = 1) :
    ∀ x ∈ M, ∃ b ∈ M ⊓ Subgroup.centralizer {t}, ∃ b' ∈ M ⊓ Subgroup.centralizer {t * z},
      ∃ n ∈ Subgroup.zpowers σ, b * b' * n = x := by
  have hN := d.N_le_M
  let B₁ : Subgroup G := M ⊓ Subgroup.centralizer {t}
  let B₂ : Subgroup G := M ⊓ Subgroup.centralizer {t * z}
  let N : Subgroup G := Subgroup.zpowers σ
  have hmem : ∀ b ∈ B₁, ∀ b' ∈ B₂, ∀ n ∈ N, b * b' * n ∈ M := fun b hb b' hb' n hn =>
    mul_mem (mul_mem (Subgroup.mem_inf.mp hb).1 (Subgroup.mem_inf.mp hb').1) (hN hn)
  let Ψ : ↥B₁ × ↥B₂ × ↥N → ↥M := fun x =>
    ⟨(x.1 : G) * (x.2.1 : G) * (x.2.2 : G), hmem _ x.1.2 _ x.2.1.2 _ x.2.2.2⟩
  have hinj : Function.Injective Ψ := by
    rintro ⟨⟨b, hb⟩, ⟨b', hb'⟩, ⟨n, hn⟩⟩ ⟨⟨c, hc⟩, ⟨c', hc'⟩, ⟨m, hm⟩⟩ h
    have h' : b * b' * n = c * c' * m := congrArg Subtype.val h
    have hcM : c ∈ M := (Subgroup.mem_inf.mp hc).1
    have hc'M : c' ∈ M := (Subgroup.mem_inf.mp hc').1
    have hmn : m * n⁻¹ ∈ N := N.mul_mem hm (N.inv_mem hn)
    have hcen : (m * n⁻¹) * c' = c' * (m * n⁻¹) := d.Ncent _ hmn c' hc'M
    have huv : (c⁻¹ * b) * (b' * c'⁻¹) = m * n⁻¹ := by
      calc (c⁻¹ * b) * (b' * c'⁻¹) = c⁻¹ * (b * b' * n) * n⁻¹ * c'⁻¹ := by group
        _ = c⁻¹ * (c * c' * m) * n⁻¹ * c'⁻¹ := by rw [h']
        _ = c' * m * n⁻¹ * c'⁻¹ := by group
        _ = c' * (m * n⁻¹) * c'⁻¹ := by group
        _ = (m * n⁻¹) * c' * c'⁻¹ := by rw [hcen]
        _ = m * n⁻¹ := by group
    have hu : c⁻¹ * b ∈ M ⊓ Subgroup.centralizer {t} :=
      (M ⊓ Subgroup.centralizer {t}).mul_mem ((M ⊓ Subgroup.centralizer {t}).inv_mem hc) hb
    have hv : b' * c'⁻¹ ∈ M ⊓ Subgroup.centralizer {t * z} :=
      (M ⊓ Subgroup.centralizer {t * z}).mul_mem hb' ((M ⊓ Subgroup.centralizer {t * z}).inv_mem hc')
    obtain ⟨h1, h2⟩ := d.uv_zero hu hv (hB1exp _ hu) hmn huv
    have hbc : b = c := (inv_mul_eq_one.mp h1).symm
    have hbc' : b' = c' := mul_inv_eq_one.mp h2
    subst hbc
    subst hbc'
    have hnm : n = m := mul_left_cancel h'
    subst hnm
    rfl
  have hN3 : Nat.card N = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime d.σ3 d.σ1
  have hcard : Nat.card ↥M ≤ Nat.card (↥B₁ × ↥B₂ × ↥N) := by
    rw [Nat.card_prod, Nat.card_prod, d.M243, hN3, d.MB, d.MBz]
  have hbij := hinj.bijective_of_nat_card_le hcard
  intro x hx
  obtain ⟨⟨⟨b, hb⟩, ⟨b', hb'⟩, ⟨n, hn⟩⟩, hbx⟩ := hbij.2 ⟨x, hx⟩
  exact ⟨b, hb, b', hb', n, hn, congrArg Subtype.val hbx⟩

end VxData

theorem cube_formula {x y c : G} (hyx : y * x = c * (x * y)) (hcx : c * x = x * c)
    (hcy : c * y = y * c) : (x * y) ^ 3 = c ^ 3 * x ^ 3 * y ^ 3 := by
  have hxc : x * c = c * x := hcx.symm
  have hyc : y * c = c * y := hcy.symm
  have m1 : x * x * y * c = c * (x * x * y) := by
    calc x * x * y * c = x * x * (y * c) := by group
      _ = x * x * (c * y) := by rw [hyc]
      _ = x * (x * c) * y := by group
      _ = x * (c * x) * y := by rw [hxc]
      _ = (x * c) * x * y := by group
      _ = (c * x) * x * y := by rw [hxc]
      _ = c * (x * x * y) := by group
  have m2 : x * c * y = c * x * y := by rw [hxc]
  have E : x * x * y * y * x * y = c * (x * x * y * x * y * y) := by
    calc x * x * y * y * x * y = x * x * y * (y * x) * y := by group
      _ = x * x * y * (c * (x * y)) * y := by rw [hyx]
      _ = (x * x * y * c) * (x * y) * y := by group
      _ = (c * (x * x * y)) * (x * y) * y := by rw [m1]
      _ = c * (x * x * y * (x * y) * y) := by group
      _ = c * (x * x * y * x * y * y) := by group
  have F : x * x * y * x * y * y = c * (x * x * x * y * y * y) := by
    calc x * x * y * x * y * y = x * x * (y * x) * y * y := by group
      _ = x * x * (c * (x * y)) * y * y := by rw [hyx]
      _ = (x * x * c) * x * y * y * y := by group
      _ = (x * (x * c)) * x * y * y * y := by group
      _ = (x * (c * x)) * x * y * y * y := by rw [hxc]
      _ = ((x * c) * x) * x * y * y * y := by group
      _ = ((c * x) * x) * x * y * y * y := by rw [hxc]
      _ = c * (x * x * x * y * y * y) := by group
  calc (x * y) ^ 3 = x * (y * x) * y * (x * y) := by rw [pow_three]; group
    _ = x * (c * (x * y)) * y * (x * y) := by rw [hyx]
    _ = c * (x * x * y * y * x * y) := by
      calc x * (c * (x * y)) * y * (x * y) = (x * c) * (x * y) * y * (x * y) := by group
        _ = (c * x) * (x * y) * y * (x * y) := by rw [hxc]
        _ = c * (x * x * y * y * x * y) := by group
    _ = c * (c * (c * (x * x * x * y * y * y))) := by rw [E, F]
    _ = c ^ 3 * x ^ 3 * y ^ 3 := by simp only [pow_three]; group

namespace VxData

variable {H M M' P : Subgroup G} {z t σ τ : G}

theorem exp3_M [Finite G] (d : VxData H z t σ τ M M' P)
    (hB1exp : ∀ b ∈ M ⊓ Subgroup.centralizer {t}, b ^ 3 = 1)
    (hB2exp : ∀ b ∈ M ⊓ Subgroup.centralizer {t * z}, b ^ 3 = 1) :
    ∀ x ∈ M, x ^ 3 = 1 := by
  intro x hx
  obtain ⟨b, hb, b', hb', n, hn, rfl⟩ := d.decomp hB1exp x hx
  have hbM : b ∈ M := (Subgroup.mem_inf.mp hb).1
  have hb'M : b' ∈ M := (Subgroup.mem_inf.mp hb').1
  have hcN : b' * b * b'⁻¹ * b⁻¹ ∈ Subgroup.zpowers σ := d.comm b' hb'M b hbM
  have hyx : b' * b = (b' * b * b'⁻¹ * b⁻¹) * (b * b') := by group
  have hcb : (b' * b * b'⁻¹ * b⁻¹) * b = b * (b' * b * b'⁻¹ * b⁻¹) :=
    d.Ncent _ hcN b hbM
  have hcb' : (b' * b * b'⁻¹ * b⁻¹) * b' = b' * (b' * b * b'⁻¹ * b⁻¹) :=
    d.Ncent _ hcN b' hb'M
  have hcube := cube_formula hyx hcb hcb'
  have hc3 : (b' * b * b'⁻¹ * b⁻¹) ^ 3 = 1 := d.pow3_zpowers _ hcN
  have hbb : b * b' ∈ M := mul_mem hbM hb'M
  have hcomm : Commute (b * b') n := (d.Ncent n hn (b * b') hbb).symm
  rw [hcomm.mul_pow, hcube, hc3, hB1exp b hb, hB2exp b' hb', d.pow3_zpowers n hn]
  simp

theorem nonab [Finite G] (d : VxData H z t σ τ M M' P) :
    ∃ x ∈ M, ∃ y ∈ M, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have hB := d.B_facts (u := t) d.ct d.MB
  apply not_le_centralizer_of_card (K := M) (B := M ⊓ Subgroup.centralizer {t}) (n := 243)
    _ d.M243 _
  · intro g hg b hb
    exact hcon g hg b (Subgroup.mem_inf.mp hb).1
  · rw [hB.2.2]; norm_num

end VxData

theorem comm_prod_central {M A₁ A₂ N : Subgroup G}
    (hNc : ∀ n ∈ N, ∀ m ∈ M, n * m = m * n)
    (hA₁M : A₁ ≤ M) (hA₂M : A₂ ≤ M) (hNM : N ≤ M)
    {a b n a₁ b₁ n₁ : G} (ha : a ∈ A₁) (hb : b ∈ A₂)
    (hbA₁ : ∀ c ∈ A₁, b * c = c * b) (haA₂ : ∀ c ∈ A₂, a * c = c * a)
    (hA₁ : ∀ c ∈ A₁, a * c = c * a) (hA₂ : ∀ c ∈ A₂, b * c = c * b)
    (hn : n ∈ N) (ha₁ : a₁ ∈ A₁) (hb₁ : b₁ ∈ A₂) (hn₁ : n₁ ∈ N) :
    (a * b * n) * (a₁ * b₁ * n₁) = (a₁ * b₁ * n₁) * (a * b * n) := by
  have hab : a * b ∈ M := mul_mem (hA₁M ha) (hA₂M hb)
  have ha₁M : a₁ * b₁ ∈ M := mul_mem (hA₁M ha₁) (hA₂M hb₁)
  have c1 : Commute a a₁ := hA₁ a₁ ha₁
  have c2 : Commute a b₁ := haA₂ b₁ hb₁
  have c3 : Commute b a₁ := hbA₁ a₁ ha₁
  have c4 : Commute b b₁ := hA₂ b₁ hb₁
  have cab : Commute (a * b) (a₁ * b₁) := Commute.mul_right (Commute.mul_left c1 c3) (Commute.mul_left c2 c4)
  have cn1 : Commute n (a₁ * b₁) := hNc n hn _ ha₁M
  have cn2 : Commute (a * b) n₁ := (hNc n₁ hn₁ _ hab).symm
  have cnn : Commute n n₁ := hNc n hn n₁ (hNM hn₁)
  have cx : Commute (a * b * n) (a₁ * b₁) := Commute.mul_left cab cn1
  have cy : Commute (a * b * n) n₁ := Commute.mul_left cn2 cnn
  exact (Commute.mul_right cx cy).eq

theorem Z_card_eq [Finite G] {M A₁ A₂ N : Subgroup G}
    (hNc : ∀ n ∈ N, ∀ m ∈ M, n * m = m * n)
    (hA₁ : ∀ a ∈ A₁, ∀ a' ∈ A₁, a * a' = a' * a) (hA₂ : ∀ b ∈ A₂, ∀ b' ∈ A₂, b * b' = b' * b)
    (hA₁M : A₁ ≤ M) (hA₂M : A₂ ≤ M) (hNM : N ≤ M)
    (hdec : ∀ x ∈ M, ∃ a ∈ A₁, ∃ b ∈ A₂, ∃ n ∈ N, a * b * n = x)
    (hinj : ∀ a ∈ A₁, ∀ b ∈ A₂, ∀ n ∈ N, ∀ a₁ ∈ A₁, ∀ b₁ ∈ A₂, ∀ n₁ ∈ N,
      a * b * n = a₁ * b₁ * n₁ → a = a₁ ∧ b = b₁ ∧ n = n₁) :
    Nat.card ↥(M ⊓ Subgroup.centralizer (M : Set G)) =
      Nat.card ↥(A₁ ⊓ Subgroup.centralizer (A₂ : Set G)) *
        Nat.card ↥(A₂ ⊓ Subgroup.centralizer (A₁ : Set G)) * Nat.card ↥N := by
  set R₁ : Subgroup G := A₁ ⊓ Subgroup.centralizer (A₂ : Set G) with hR₁
  set R₂ : Subgroup G := A₂ ⊓ Subgroup.centralizer (A₁ : Set G) with hR₂
  have hR₁c : ∀ a ∈ R₁, ∀ c ∈ A₂, a * c = c * a := fun a ha c hc =>
    ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ha).2) c hc).symm
  have hR₂c : ∀ b ∈ R₂, ∀ c ∈ A₁, b * c = c * b := fun b hb c hc =>
    ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb).2) c hc).symm
  have hmemZ : ∀ a ∈ R₁, ∀ b ∈ R₂, ∀ n ∈ N, a * b * n ∈ M ⊓ Subgroup.centralizer (M : Set G) := by
    intro a ha b hb n hn
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (hA₁M (Subgroup.mem_inf.mp ha).1)
      (hA₂M (Subgroup.mem_inf.mp hb).1)) (hNM hn), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨a₁, ha₁, b₁, hb₁, n₁, hn₁, rfl⟩ := hdec y hy
    exact (comm_prod_central hNc hA₁M hA₂M hNM (Subgroup.mem_inf.mp ha).1
      (Subgroup.mem_inf.mp hb).1 (hR₂c b hb) (hR₁c a ha) (fun c hc => hA₁ _ (Subgroup.mem_inf.mp ha).1 c hc)
      (fun c hc => hA₂ _ (Subgroup.mem_inf.mp hb).1 c hc) hn ha₁ hb₁ hn₁).symm
  let f : ↥R₁ × ↥R₂ × ↥N → ↥(M ⊓ Subgroup.centralizer (M : Set G)) := fun x =>
    ⟨(x.1 : G) * (x.2.1 : G) * (x.2.2 : G), hmemZ _ x.1.2 _ x.2.1.2 _ x.2.2.2⟩
  have hfinj : Function.Injective f := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨n, hn⟩⟩ ⟨⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩, ⟨n₁, hn₁⟩⟩ h
    have h' : a * b * n = a₁ * b₁ * n₁ := congrArg Subtype.val h
    obtain ⟨e1, e2, e3⟩ := hinj a (Subgroup.mem_inf.mp ha).1 b (Subgroup.mem_inf.mp hb).1 n hn
      a₁ (Subgroup.mem_inf.mp ha₁).1 b₁ (Subgroup.mem_inf.mp hb₁).1 n₁ hn₁ h'
    subst e1; subst e2; subst e3
    rfl
  have hfsurj : Function.Surjective f := by
    rintro ⟨z₀, hz₀⟩
    obtain ⟨hzM, hzC⟩ := Subgroup.mem_inf.mp hz₀
    obtain ⟨a₁, ha₁, b₁, hb₁, n₁, hn₁, hz⟩ := hdec z₀ hzM
    have hcen : ∀ y ∈ M, y * z₀ = z₀ * y := fun y hy => Subgroup.mem_centralizer_iff.mp hzC y hy
    have hA1c : ∀ c ∈ A₂, a₁ * c = c * a₁ := by
      intro c hc
      have hcM : c ∈ M := hA₂M hc
      have hcz := hcen c hcM
      rw [← hz] at hcz
      have h1 : (a₁ * c) * (b₁ * n₁) = (c * a₁) * (b₁ * n₁) := by
        calc (a₁ * c) * (b₁ * n₁) = a₁ * (c * b₁) * n₁ := by group
          _ = a₁ * (b₁ * c) * n₁ := by rw [hA₂ c hc b₁ hb₁]
          _ = a₁ * b₁ * (c * n₁) := by group
          _ = a₁ * b₁ * (n₁ * c) := by rw [hNc n₁ hn₁ c hcM]
          _ = (a₁ * b₁ * n₁) * c := by group
          _ = c * (a₁ * b₁ * n₁) := hcz.symm
          _ = (c * a₁) * (b₁ * n₁) := by group
      exact mul_right_cancel h1
    have hB1c : ∀ c ∈ A₁, b₁ * c = c * b₁ := by
      intro c hc
      have hcM : c ∈ M := hA₁M hc
      have hcz := hcen c hcM
      rw [← hz] at hcz
      have h1 : a₁ * ((b₁ * c) * n₁) = a₁ * ((c * b₁) * n₁) := by
        calc a₁ * ((b₁ * c) * n₁) = a₁ * b₁ * (c * n₁) := by group
          _ = a₁ * b₁ * (n₁ * c) := by rw [hNc n₁ hn₁ c hcM]
          _ = (a₁ * b₁ * n₁) * c := by group
          _ = c * (a₁ * b₁ * n₁) := hcz.symm
          _ = (c * a₁) * (b₁ * n₁) := by group
          _ = (a₁ * c) * (b₁ * n₁) := by rw [← hA₁ a₁ ha₁ c hc]
          _ = a₁ * ((c * b₁) * n₁) := by group
      exact mul_right_cancel (mul_left_cancel h1)
    have hmem1 : a₁ ∈ R₁ := Subgroup.mem_inf.mpr ⟨ha₁,
      Subgroup.mem_centralizer_iff.mpr (fun c hc => (hA1c c hc).symm)⟩
    have hmem2 : b₁ ∈ R₂ := Subgroup.mem_inf.mpr ⟨hb₁,
      Subgroup.mem_centralizer_iff.mpr (fun c hc => (hB1c c hc).symm)⟩
    exact ⟨⟨⟨a₁, hmem1⟩, ⟨b₁, hmem2⟩, ⟨n₁, hn₁⟩⟩, Subtype.ext hz⟩
  have hbij : Function.Bijective f := ⟨hfinj, hfsurj⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_prod, Nat.card_prod, mul_assoc]

theorem prod_surj_of [Finite G] {K A C : Subgroup G} (hA : A ≤ K) (hC : C ≤ K)
    (hinf : A ⊓ C = ⊥) (hcard : Nat.card ↥A * Nat.card ↥C = Nat.card ↥K) :
    ∀ k ∈ K, ∃ a ∈ A, ∃ c ∈ C, a * c = k := by
  let f : ↥A × ↥C → ↥K := fun x => ⟨(x.1 : G) * (x.2 : G), mul_mem (hA x.1.2) (hC x.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ ⟨⟨a', ha'⟩, ⟨c', hc'⟩⟩ h
    have h1 : a * c = a' * c' := congrArg Subtype.val h
    have h2 : a'⁻¹ * a = c' * c⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * c) * c⁻¹ := by group
        _ = a'⁻¹ * (a' * c') * c⁻¹ := by rw [h1]
        _ = c' * c⁻¹ := by group
    have h3 : a'⁻¹ * a ∈ A ⊓ C := by
      refine Subgroup.mem_inf.mpr ⟨A.mul_mem (A.inv_mem ha') ha, ?_⟩
      rw [h2]; exact C.mul_mem hc' (C.inv_mem hc)
    rw [hinf, Subgroup.mem_bot] at h3
    have hae : a = a' := (inv_mul_eq_one.mp h3).symm
    have h4 : c' * c⁻¹ = 1 := by rw [← h2, h3]
    have hce : c = c' := (mul_inv_eq_one.mp h4).symm
    subst hae; subst hce; rfl
  have hsurj : Function.Surjective f :=
    (hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, hcard])).2
  intro k hk
  obtain ⟨⟨⟨a, ha⟩, ⟨c, hc⟩⟩, h⟩ := hsurj ⟨k, hk⟩
  exact ⟨a, ha, c, hc, congrArg Subtype.val h⟩

theorem rad_card_ge [Finite G] {M N A₁ A₂ : Subgroup G}
    (hNc : ∀ n ∈ N, ∀ m ∈ M, n * m = m * n)
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N)
    (hNM : N ≤ M) (hA₁M : A₁ ≤ M) (hA₂M : A₂ ≤ M)
    (hA₂exp : ∀ b ∈ A₂, b ^ 3 = 1)
    (hA₁card : Nat.card ↥A₁ = 9) (hA₂card : Nat.card ↥A₂ = 9) (hNcard : Nat.card ↥N = 3)
    (hR : Nat.card ↥(A₂ ⊓ Subgroup.centralizer (A₁ : Set G)) = 3) :
    3 ≤ Nat.card ↥(A₁ ⊓ Subgroup.centralizer (A₂ : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R₂ : Subgroup G := A₂ ⊓ Subgroup.centralizer (A₁ : Set G) with hR₂def
  have hR₂A₂ : R₂ ≤ A₂ := inf_le_left
  have hR₂c : ∀ r ∈ R₂, ∀ b ∈ A₁, b * r = r * b := fun r hr b hb =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hr).2 b hb
  obtain ⟨c₁, hc₁A₂, hc₁R⟩ : ∃ c₁ ∈ A₂, c₁ ∉ R₂ := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show A₂ ≤ R₂ from fun c hc => hcon c hc)
    omega
  have hc₁ne : c₁ ≠ 1 := fun h => hc₁R (h ▸ R₂.one_mem)
  have hc₁3 : c₁ ^ 3 = 1 := hA₂exp c₁ hc₁A₂
  have hord : orderOf c₁ = 3 := orderOf_eq_prime hc₁3 hc₁ne
  set A : Subgroup G := Subgroup.zpowers c₁ with hAdef
  have hAcard : Nat.card ↥A = 3 := by rw [hAdef, Nat.card_zpowers, hord]
  have hAA₂ : A ≤ A₂ := (Subgroup.zpowers_le).mpr hc₁A₂
  have hAinf : A ⊓ R₂ = ⊥ := by
    have hdvd : Nat.card ↥(A ⊓ R₂) ∣ 3 := by
      rw [← hAcard]; exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      apply hc₁R
      have heq : A ⊓ R₂ = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hAcard])
      have hmem : c₁ ∈ A ⊓ R₂ := by rw [heq]; exact Subgroup.mem_zpowers c₁
      exact (Subgroup.mem_inf.mp hmem).2
  have hfac := prod_surj_of (K := A₂) (A := A) (C := R₂) hAA₂ hR₂A₂ hAinf
    (by rw [hAcard, hR, hA₂card])
  have hall : ∀ b ∈ A₁, b * c₁ = c₁ * b → ∀ c ∈ A₂, b * c = c * b := by
    intro b hb hbc c hc
    obtain ⟨a, ha, r, hr, hcar⟩ := hfac c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hbk : b * c₁ ^ k = c₁ ^ k * b := (Commute.zpow_right (show Commute b c₁ from hbc) k).eq
    rw [← hcar]
    calc b * (c₁ ^ k * r) = (b * c₁ ^ k) * r := by group
      _ = (c₁ ^ k * b) * r := by rw [hbk]
      _ = c₁ ^ k * (b * r) := by group
      _ = c₁ ^ k * (r * b) := by rw [hR₂c r hr b hb]
      _ = (c₁ ^ k * r) * b := by group
  let Φ : ↥A₁ →* ↥N :=
    { toFun := fun b => ⟨(b : G) * c₁ * (b : G)⁻¹ * c₁⁻¹, hcomm _ (hA₁M b.2) _ (hA₂M hc₁A₂)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := by
        intro x y
        apply Subtype.ext
        show ((x : G) * (y : G)) * c₁ * ((x : G) * (y : G))⁻¹ * c₁⁻¹
          = ((x : G) * c₁ * (x : G)⁻¹ * c₁⁻¹) * ((y : G) * c₁ * (y : G)⁻¹ * c₁⁻¹)
        have hP := hcomm (y : G) (hA₁M y.2) c₁ (hA₂M hc₁A₂)
        have hQ := hcomm (x : G) (hA₁M x.2) c₁ (hA₂M hc₁A₂)
        have hxP : (x : G) * ((y : G) * c₁ * (y : G)⁻¹ * c₁⁻¹)
            = ((y : G) * c₁ * (y : G)⁻¹ * c₁⁻¹) * (x : G) := (hNc _ hP x (hA₁M x.2)).symm
        have hQP : ((x : G) * c₁ * (x : G)⁻¹ * c₁⁻¹) * ((y : G) * c₁ * (y : G)⁻¹ * c₁⁻¹)
            = ((y : G) * c₁ * (y : G)⁻¹ * c₁⁻¹) * ((x : G) * c₁ * (x : G)⁻¹ * c₁⁻¹) :=
          hNc _ hQ _ (hNM hP)
        calc ((x : G) * (y : G)) * c₁ * ((x : G) * (y : G))⁻¹ * c₁⁻¹
            = (x : G) * ((y : G) * c₁ * (y : G)⁻¹ * c₁⁻¹) * (x : G)⁻¹
              * ((x : G) * c₁ * (x : G)⁻¹ * c₁⁻¹) := by group
          _ = ((y : G) * c₁ * (y : G)⁻¹ * c₁⁻¹) * ((x : G) * c₁ * (x : G)⁻¹ * c₁⁻¹) := by
            rw [hxP]; group
          _ = ((x : G) * c₁ * (x : G)⁻¹ * c₁⁻¹) * ((y : G) * c₁ * (y : G)⁻¹ * c₁⁻¹) :=
            hQP.symm }
  have hmap : (Φ.ker).map A₁.subtype = A₁ ⊓ Subgroup.centralizer (A₂ : Set G) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : Φ x = 1 := hx
      have h1 : (x : G) * c₁ * (x : G)⁻¹ * c₁⁻¹ = 1 := congrArg Subtype.val hx'
      have h2 : (x : G) * c₁ * (x : G)⁻¹ = c₁ := by
        calc (x : G) * c₁ * (x : G)⁻¹ = ((x : G) * c₁ * (x : G)⁻¹ * c₁⁻¹) * c₁ := by group
          _ = c₁ := by rw [h1, one_mul]
      have h3 : (x : G) * c₁ = c₁ * (x : G) := by
        calc (x : G) * c₁ = ((x : G) * c₁ * (x : G)⁻¹) * (x : G) := by group
          _ = c₁ * (x : G) := by rw [h2]
      refine Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro c hc
      exact (hall x x.2 h3 c hc).symm
    · intro hg
      obtain ⟨hgA₁, hgC⟩ := Subgroup.mem_inf.mp hg
      refine ⟨⟨g, hgA₁⟩, ?_, rfl⟩
      show Φ ⟨g, hgA₁⟩ = 1
      have hgc : c₁ * g = g * c₁ := Subgroup.mem_centralizer_iff.mp hgC c₁ hc₁A₂
      apply Subtype.ext
      show (g : G) * c₁ * (g : G)⁻¹ * c₁⁻¹ = 1
      calc (g : G) * c₁ * (g : G)⁻¹ * c₁⁻¹ = ((c₁ * g) * (g : G)⁻¹) * c₁⁻¹ := by rw [← hgc]
        _ = 1 := by group
  have hkerc : Nat.card ↥(A₁ ⊓ Subgroup.centralizer (A₂ : Set G)) = Nat.card ↥(Φ.ker) := by
    rw [← hmap, Subgroup.card_map_of_injective (f := A₁.subtype) (fun x y h => Subtype.ext h)]
  have hidx := Subgroup.card_mul_index Φ.ker
  have hind := Subgroup.index_ker Φ
  have hrange : Nat.card ↥Φ.range ≤ 3 := by
    rw [← hNcard]; exact Subgroup.card_le_card_group _
  rw [hkerc]
  rw [hA₁card, hind] at hidx
  nlinarith

namespace VxData

variable {H M M' P : Subgroup G} {z t σ τ : G}

theorem decomp_inj [Finite G] (d : VxData H z t σ τ M M' P)
    (hB1exp : ∀ b ∈ M ⊓ Subgroup.centralizer {t}, b ^ 3 = 1) :
    ∀ b ∈ M ⊓ Subgroup.centralizer {t}, ∀ b' ∈ M ⊓ Subgroup.centralizer {t * z},
      ∀ n ∈ Subgroup.zpowers σ, ∀ c ∈ M ⊓ Subgroup.centralizer {t},
      ∀ c' ∈ M ⊓ Subgroup.centralizer {t * z}, ∀ m ∈ Subgroup.zpowers σ,
      b * b' * n = c * c' * m → b = c ∧ b' = c' ∧ n = m := by
  intro b hb b' hb' n hn c hc c' hc' m hm h'
  have hcM : c ∈ M := (Subgroup.mem_inf.mp hc).1
  have hc'M : c' ∈ M := (Subgroup.mem_inf.mp hc').1
  have hmn : m * n⁻¹ ∈ Subgroup.zpowers σ := (Subgroup.zpowers σ).mul_mem hm ((Subgroup.zpowers σ).inv_mem hn)
  have hcen : (m * n⁻¹) * c' = c' * (m * n⁻¹) := d.Ncent _ hmn c' hc'M
  have huv : (c⁻¹ * b) * (b' * c'⁻¹) = m * n⁻¹ := by
    calc (c⁻¹ * b) * (b' * c'⁻¹) = c⁻¹ * (b * b' * n) * n⁻¹ * c'⁻¹ := by group
      _ = c⁻¹ * (c * c' * m) * n⁻¹ * c'⁻¹ := by rw [h']
      _ = c' * m * n⁻¹ * c'⁻¹ := by group
      _ = c' * (m * n⁻¹) * c'⁻¹ := by group
      _ = (m * n⁻¹) * c' * c'⁻¹ := by rw [hcen]
      _ = m * n⁻¹ := by group
  have hu : c⁻¹ * b ∈ M ⊓ Subgroup.centralizer {t} :=
    (M ⊓ Subgroup.centralizer {t}).mul_mem ((M ⊓ Subgroup.centralizer {t}).inv_mem hc) hb
  have hv : b' * c'⁻¹ ∈ M ⊓ Subgroup.centralizer {t * z} :=
    (M ⊓ Subgroup.centralizer {t * z}).mul_mem hb' ((M ⊓ Subgroup.centralizer {t * z}).inv_mem hc')
  obtain ⟨h1, h2⟩ := d.uv_zero hu hv (hB1exp _ hu) hmn huv
  have hbc : b = c := (inv_mul_eq_one.mp h1).symm
  have hbc' : b' = c' := mul_inv_eq_one.mp h2
  subst hbc
  subst hbc'
  have hnm : n = m := mul_left_cancel h'
  exact ⟨rfl, rfl, hnm⟩

theorem central_decomp [Finite G] {M A₁ A₂ N : Subgroup G}
    (hNc : ∀ n ∈ N, ∀ m ∈ M, n * m = m * n)
    (hA₁ : ∀ a ∈ A₁, ∀ a' ∈ A₁, a * a' = a' * a) (hA₂ : ∀ b ∈ A₂, ∀ b' ∈ A₂, b * b' = b' * b)
    (hA₁M : A₁ ≤ M) (hA₂M : A₂ ≤ M) (hNM : N ≤ M)
    (hdec : ∀ x ∈ M, ∃ a ∈ A₁, ∃ b ∈ A₂, ∃ n ∈ N, a * b * n = x)
    {x : G} (hx : x ∈ M ⊓ Subgroup.centralizer (M : Set G)) :
    ∃ a ∈ A₁ ⊓ Subgroup.centralizer (A₂ : Set G), ∃ b ∈ A₂ ⊓ Subgroup.centralizer (A₁ : Set G),
      ∃ n ∈ N, a * b * n = x := by
  obtain ⟨hzM, hzC⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨a₁, ha₁, b₁, hb₁, n₁, hn₁, hz⟩ := hdec x hzM
  have hcen : ∀ y ∈ M, y * x = x * y := fun y hy => Subgroup.mem_centralizer_iff.mp hzC y hy
  have hA1c : ∀ c ∈ A₂, a₁ * c = c * a₁ := by
    intro c hc
    have hcM : c ∈ M := hA₂M hc
    have hcz := hcen c hcM
    rw [← hz] at hcz
    have h1 : (a₁ * c) * (b₁ * n₁) = (c * a₁) * (b₁ * n₁) := by
      calc (a₁ * c) * (b₁ * n₁) = a₁ * (c * b₁) * n₁ := by group
        _ = a₁ * (b₁ * c) * n₁ := by rw [hA₂ c hc b₁ hb₁]
        _ = a₁ * b₁ * (c * n₁) := by group
        _ = a₁ * b₁ * (n₁ * c) := by rw [hNc n₁ hn₁ c hcM]
        _ = (a₁ * b₁ * n₁) * c := by group
        _ = c * (a₁ * b₁ * n₁) := hcz.symm
        _ = (c * a₁) * (b₁ * n₁) := by group
    exact mul_right_cancel h1
  have hB1c : ∀ c ∈ A₁, b₁ * c = c * b₁ := by
    intro c hc
    have hcM : c ∈ M := hA₁M hc
    have hcz := hcen c hcM
    rw [← hz] at hcz
    have h1 : a₁ * ((b₁ * c) * n₁) = a₁ * ((c * b₁) * n₁) := by
      calc a₁ * ((b₁ * c) * n₁) = a₁ * b₁ * (c * n₁) := by group
        _ = a₁ * b₁ * (n₁ * c) := by rw [hNc n₁ hn₁ c hcM]
        _ = (a₁ * b₁ * n₁) * c := by group
        _ = c * (a₁ * b₁ * n₁) := hcz.symm
        _ = (c * a₁) * (b₁ * n₁) := by group
        _ = (a₁ * c) * (b₁ * n₁) := by rw [← hA₁ a₁ ha₁ c hc]
        _ = a₁ * ((c * b₁) * n₁) := by group
    exact mul_right_cancel (mul_left_cancel h1)
  have hmem1 : a₁ ∈ A₁ ⊓ Subgroup.centralizer (A₂ : Set G) := Subgroup.mem_inf.mpr ⟨ha₁,
    Subgroup.mem_centralizer_iff.mpr (fun c hc => (hA1c c hc).symm)⟩
  have hmem2 : b₁ ∈ A₂ ⊓ Subgroup.centralizer (A₁ : Set G) := Subgroup.mem_inf.mpr ⟨hb₁,
    Subgroup.mem_centralizer_iff.mpr (fun c hc => (hB1c c hc).symm)⟩
  exact ⟨a₁, hmem1, b₁, hmem2, n₁, hn₁, hz⟩

end VxData

namespace VxData

variable {H M M' P : Subgroup G} {z t σ τ : G}

theorem cases_dvd9 {r : ℕ} (h : r ∣ 9) : r = 1 ∨ r = 3 ∨ r = 9 := by
  have hle : r ≤ 9 := Nat.le_of_dvd (by norm_num) h
  interval_cases r <;> simp_all

theorem card_Z [Finite G] (d : VxData H z t σ τ M M' P)
    (hSyl : (∀ x ∈ M, (∀ y ∈ M, x * y = y * x) → x ∈ Subgroup.zpowers σ) → False) :
    Nat.card ↥(M ⊓ Subgroup.centralizer (M : Set G)) = 27 := by
  have hB1 := d.B_facts (u := t) d.ct d.MB
  have hB2 := d.B_facts (u := t * z) d.ctz d.MBz
  have hdec := d.decomp hB1.1
  have hinj := d.decomp_inj hB1.1
  have hNM := d.N_le_M
  have hN3 : Nat.card ↥(Subgroup.zpowers σ) = 3 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime d.σ3 d.σ1
  have hA₁M : M ⊓ Subgroup.centralizer {t} ≤ M := inf_le_left
  have hA₂M : M ⊓ Subgroup.centralizer {t * z} ≤ M := inf_le_left
  have hZ := Z_card_eq d.Ncent hB1.2.1 hB2.2.1 hA₁M hA₂M hNM hdec hinj
  rw [hZ, hN3]
  set R₁ : Subgroup G := (M ⊓ Subgroup.centralizer {t}) ⊓ Subgroup.centralizer ((M ⊓ Subgroup.centralizer {t * z} : Subgroup G) : Set G) with hR₁
  set R₂ : Subgroup G := (M ⊓ Subgroup.centralizer {t * z}) ⊓ Subgroup.centralizer ((M ⊓ Subgroup.centralizer {t} : Subgroup G) : Set G) with hR₂
  have hR₁le : R₁ ≤ M ⊓ Subgroup.centralizer {t} := inf_le_left
  have hR₂le : R₂ ≤ M ⊓ Subgroup.centralizer {t * z} := inf_le_left
  have hdvd1 : Nat.card ↥R₁ ∣ 9 := by
    rw [← d.MB]; exact Subgroup.card_dvd_of_le hR₁le
  have hdvd2 : Nat.card ↥R₂ ∣ 9 := by
    rw [← d.MBz]; exact Subgroup.card_dvd_of_le hR₂le
  have hr1 : Nat.card ↥R₁ ≠ 9 := by
    intro h9
    have heq : R₁ = M ⊓ Subgroup.centralizer {t} :=
      Subgroup.eq_of_le_of_card_ge hR₁le (le_of_eq (by rw [d.MB, h9]))
    have hcent : ∀ g ∈ M, ∀ b ∈ M ⊓ Subgroup.centralizer {t}, g * b = b * g := by
      intro g hg b hb
      obtain ⟨b₁, hb₁, b₂, hb₂, n, hn, rfl⟩ := hdec g hg
      have hbR : b ∈ R₁ := by rw [heq]; exact hb
      have hbb₂ : b * b₂ = b₂ * b :=
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hbR).2 b₂ hb₂).symm
      have hbb₁ : b * b₁ = b₁ * b := hB1.2.1 b hb b₁ hb₁
      have hnb : n * b = b * n := d.Ncent n hn b (hA₁M hb)
      calc (b₁ * b₂ * n) * b = b₁ * b₂ * (n * b) := by group
        _ = b₁ * b₂ * (b * n) := by rw [hnb]
        _ = b₁ * (b₂ * b) * n := by group
        _ = b₁ * (b * b₂) * n := by rw [← hbb₂]
        _ = (b₁ * b) * b₂ * n := by group
        _ = (b * b₁) * b₂ * n := by rw [← hbb₁]
        _ = b * (b₁ * b₂ * n) := by group
    exact not_le_centralizer_of_card (K := M) (B := M ⊓ Subgroup.centralizer {t}) (n := 243)
      hcent d.M243 (by rw [hB1.2.2]; norm_num)
  have hr2 : Nat.card ↥R₂ ≠ 9 := by
    intro h9
    have heq : R₂ = M ⊓ Subgroup.centralizer {t * z} :=
      Subgroup.eq_of_le_of_card_ge hR₂le (le_of_eq (by rw [d.MBz, h9]))
    have hcent : ∀ g ∈ M, ∀ b ∈ M ⊓ Subgroup.centralizer {t * z}, g * b = b * g := by
      intro g hg b hb
      obtain ⟨b₁, hb₁, b₂, hb₂, n, hn, rfl⟩ := hdec g hg
      have hbR : b ∈ R₂ := by rw [heq]; exact hb
      have hbb₁ : b * b₁ = b₁ * b :=
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hbR).2 b₁ hb₁).symm
      have hbb₂ : b * b₂ = b₂ * b := hB2.2.1 b hb b₂ hb₂
      have hnb : n * b = b * n := d.Ncent n hn b (hA₂M hb)
      calc (b₁ * b₂ * n) * b = b₁ * b₂ * (n * b) := by group
        _ = b₁ * b₂ * (b * n) := by rw [hnb]
        _ = b₁ * (b₂ * b) * n := by group
        _ = b₁ * (b * b₂) * n := by rw [← hbb₂]
        _ = (b₁ * b) * b₂ * n := by group
        _ = (b * b₁) * b₂ * n := by rw [← hbb₁]
        _ = b * (b₁ * b₂ * n) := by group
    exact not_le_centralizer_of_card (K := M) (B := M ⊓ Subgroup.centralizer {t * z}) (n := 243)
      hcent d.M243 (by rw [hB2.2.2]; norm_num)
  have hc1 := cases_dvd9 hdvd1
  have hc2 := cases_dvd9 hdvd2
  have h11 : ¬ (Nat.card ↥R₁ = 1 ∧ Nat.card ↥R₂ = 1) := by
    rintro ⟨e1, e2⟩
    apply hSyl
    intro x hxM hxc
    have hxcen : x ∈ M ⊓ Subgroup.centralizer (M : Set G) :=
      Subgroup.mem_inf.mpr ⟨hxM, Subgroup.mem_centralizer_iff.mpr (fun y hy => (hxc y hy).symm)⟩
    obtain ⟨a, ha, b, hb, n, hn, hab⟩ :=
      central_decomp d.Ncent hB1.2.1 hB2.2.1 hA₁M hA₂M hNM hdec hxcen
    have ha1 : a = 1 := by
      have ha' : a ∈ R₁ := ha
      rw [Subgroup.eq_bot_of_card_eq _ e1] at ha'
      exact Subgroup.mem_bot.mp ha'
    have hb1 : b = 1 := by
      have hb' : b ∈ R₂ := hb
      rw [Subgroup.eq_bot_of_card_eq _ e2] at hb'
      exact Subgroup.mem_bot.mp hb'
    rw [← hab, ha1, hb1]
    simpa using hn
  have hmixed1 : Nat.card ↥R₁ = 1 → Nat.card ↥R₂ = 3 → False := by
    intro e1 e2
    have h := rad_card_ge (A₁ := M ⊓ Subgroup.centralizer {t}) (A₂ := M ⊓ Subgroup.centralizer {t * z})
      d.Ncent d.comm hNM hA₁M hA₂M hB2.1 d.MB d.MBz hN3 e2
    have h' : 3 ≤ Nat.card ↥R₁ := h
    omega
  have hmixed2 : Nat.card ↥R₁ = 3 → Nat.card ↥R₂ = 1 → False := by
    intro e1 e2
    have h := rad_card_ge (A₁ := M ⊓ Subgroup.centralizer {t * z}) (A₂ := M ⊓ Subgroup.centralizer {t})
      d.Ncent d.comm hNM hA₂M hA₁M hB1.1 d.MBz d.MB hN3 e1
    have h' : 3 ≤ Nat.card ↥R₂ := h
    omega
  rcases hc1 with e1 | e1 | e1 <;> rcases hc2 with e2 | e2 | e2
  all_goals first
    | exact (hr1 e1).elim
    | exact (hr2 e2).elim
    | exact (h11 ⟨e1, e2⟩).elim
    | exact (hmixed1 e1 e2).elim
    | exact (hmixed2 e1 e2).elim
    | (rw [e1, e2])

end VxData

def mkSS (M : Subgroup G) (σ y : G) (hM : M ≤ Subgroup.centralizer {σ})
    (hnorm : ∀ g ∈ Subgroup.centralizer {σ}, ∀ m ∈ M, g * m * g⁻¹ ∈ M)
    (hy : y ∈ Subgroup.centralizer {σ}) : Subgroup G where
  carrier := {x | ∃ m ∈ M, ∃ k : ℤ, m * y ^ k = x}
  mul_mem' := by
    rintro _ _ ⟨m, hm, k, rfl⟩ ⟨m', hm', k', rfl⟩
    refine ⟨m * (y ^ k * m' * (y ^ k)⁻¹), M.mul_mem hm (hnorm _ (Subgroup.zpow_mem _ hy k) m' hm'),
      k + k', ?_⟩
    rw [zpow_add]
    group
  one_mem' := ⟨1, M.one_mem, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨m, hm, k, rfl⟩
    refine ⟨y ^ (-k) * m⁻¹ * (y ^ (-k))⁻¹,
      hnorm _ (Subgroup.zpow_mem _ hy (-k)) m⁻¹ (M.inv_mem hm), -k, ?_⟩
    group

theorem mem_mkSS {M : Subgroup G} {σ y : G} {hM hnorm hy} {x : G} :
    x ∈ mkSS M σ y hM hnorm hy ↔ ∃ m ∈ M, ∃ k : ℤ, m * y ^ k = x := Iff.rfl

theorem card_mkSS [Finite G] {M : Subgroup G} {σ y : G} {hM hnorm hy}
    (hMy : M ⊓ Subgroup.zpowers y = ⊥) (hM243 : Nat.card ↥M = 243) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    Nat.card ↥(mkSS M σ y hM hnorm hy) = 729 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hyc : Nat.card ↥(Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime hy3 hy1
  let F : ↥M × ↥(Subgroup.zpowers y) → ↥(mkSS M σ y hM hnorm hy) := fun x =>
    ⟨(x.1 : G) * (x.2 : G), by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2.2
      exact ⟨x.1, x.1.2, k, by rw [hk]⟩⟩
  have hinj : Function.Injective F := by
    rintro ⟨⟨m, hm⟩, ⟨x, hx⟩⟩ ⟨⟨m', hm'⟩, ⟨x', hx'⟩⟩ h
    have h' : m * x = m' * x' := congrArg Subtype.val h
    have hquot : m'⁻¹ * m = x' * x⁻¹ := by
      calc m'⁻¹ * m = m'⁻¹ * (m * x) * x⁻¹ := by group
        _ = m'⁻¹ * (m' * x') * x⁻¹ := by rw [h']
        _ = x' * x⁻¹ := by group
    have hmem : m'⁻¹ * m ∈ M ⊓ Subgroup.zpowers y := by
      refine Subgroup.mem_inf.mpr ⟨M.mul_mem (M.inv_mem hm') hm, ?_⟩
      rw [hquot]
      exact (Subgroup.zpowers y).mul_mem hx' ((Subgroup.zpowers y).inv_mem hx)
    rw [hMy, Subgroup.mem_bot] at hmem
    have hmm : m = m' := (inv_mul_eq_one.mp hmem).symm
    have h2 : x' * x⁻¹ = 1 := by rw [← hquot]; exact hmem
    have hxx : x = x' := (mul_inv_eq_one.mp h2).symm
    subst hmm
    subst hxx
    rfl
  have hsurj : Function.Surjective F := by
    rintro ⟨w, m, hm, k, rfl⟩
    exact ⟨⟨⟨m, hm⟩, ⟨y ^ k, Subgroup.zpow_mem_zpowers y k⟩⟩, rfl⟩
  have hcard : Nat.card (↥M × ↥(Subgroup.zpowers y)) = 729 := by
    rw [Nat.card_prod, hM243, hyc]
  rw [← hcard]
  exact (Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)).symm

theorem comm_of_pow_comm {y g u : G} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hg : g ∈ Subgroup.zpowers y)
    (hg1 : g ≠ 1) (hu : u * g = g * u) : u * y = y * u := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hkr : y ^ k = y ^ (k % 3) := by
    have := zpow_mod_orderOf y k
    rw [hord] at this
    exact this.symm
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  have h4 : y ^ 4 = y := by
    calc y ^ 4 = y ^ 3 * y := by group
      _ = y := by rw [hy3, one_mul]
  rcases hr with h0 | h1 | h2
  · exfalso; apply hg1; rw [hkr, h0]; simp
  · rw [hkr, h1, zpow_one] at hu
    exact hu
  · rw [hkr, h2] at hu
    have hu' : u * y ^ 2 = y ^ 2 * u := by exact_mod_cast hu
    have hu4 : u * y ^ 4 = y ^ 4 * u := by
      calc u * y ^ 4 = (u * y ^ 2) * y ^ 2 := by group
        _ = (y ^ 2 * u) * y ^ 2 := by rw [hu']
        _ = y ^ 2 * (u * y ^ 2) := by group
        _ = y ^ 2 * (y ^ 2 * u) := by rw [hu']
        _ = y ^ 4 * u := by group
    rw [h4] at hu4
    exact hu4

theorem center_mkSS [Finite G] {M : Subgroup G} {σ y : G}
    {hM : M ≤ Subgroup.centralizer {σ}}
    {hnorm : ∀ g ∈ Subgroup.centralizer {σ}, ∀ m ∈ M, g * m * g⁻¹ ∈ M}
    {hy : y ∈ Subgroup.centralizer {σ}}
    (hZM : ∀ x ∈ M, (∀ y' ∈ M, x * y' = y' * x) → x ∈ Subgroup.zpowers σ)
    (hNc : ∀ n ∈ Subgroup.zpowers σ, ∀ u ∈ M, n * u = u * n)
    (hcomm : ∀ x ∈ M, ∀ y' ∈ M, x * y' * x⁻¹ * y'⁻¹ ∈ Subgroup.zpowers σ)
    (hNM : Subgroup.zpowers σ ≤ M) (hN3 : Nat.card ↥(Subgroup.zpowers σ) = 3)
    (hM243 : Nat.card ↥M = 243) (hyM : Nat.card ↥(M ⊓ Subgroup.centralizer {y}) = 27)
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    ∀ x ∈ mkSS M σ y hM hnorm hy, (∀ s ∈ mkSS M σ y hM hnorm hy, x * s = s * x) →
      x ∈ Subgroup.zpowers σ := by
  intro x hx hcx
  obtain ⟨m, hm, k, rfl⟩ := (mem_mkSS).mp hx
  have hcentral : ∀ u ∈ M, u * (m * y ^ k) = (m * y ^ k) * u := by
    intro u hu
    exact (hcx u ⟨u, hu, 0, by simp⟩).symm
  by_cases hg1 : y ^ k = 1
  · rw [hg1, mul_one]
    apply hZM m hm
    intro u hu
    rw [hg1, mul_one] at hcentral
    exact (hcentral u hu).symm
  set g := y ^ k with hgdef
  have hgy : g ∈ Subgroup.zpowers y := Subgroup.zpow_mem_zpowers y k
  have hρmem : ∀ u ∈ M, g * u * g⁻¹ * u⁻¹ ∈ Subgroup.zpowers σ := by
    intro u hu
    have e1 : g * u = m⁻¹ * u * m * g := by
      calc g * u = m⁻¹ * (m * g * u) := by group
        _ = m⁻¹ * (u * (m * g)) := by rw [(hcentral u hu).symm]
        _ = m⁻¹ * u * m * g := by group
    have e2 : g * u * g⁻¹ * u⁻¹ = m⁻¹ * u * m * u⁻¹ := by
      rw [e1]; group
    have hc := hcomm m⁻¹ (M.inv_mem hm) u hu
    rw [e2]
    convert hc using 1
    group
  let ρ : ↥M →* ↥(Subgroup.zpowers σ) :=
    { toFun := fun u => ⟨g * (u : G) * g⁻¹ * (u : G)⁻¹, hρmem u u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := by
        intro u v
        apply Subtype.ext
        have hPN : g * (v : G) * g⁻¹ * (v : G)⁻¹ ∈ Subgroup.zpowers σ := hρmem v v.2
        have hc : (u : G) * (g * (v : G) * g⁻¹ * (v : G)⁻¹)
            = (g * (v : G) * g⁻¹ * (v : G)⁻¹) * (u : G) :=
          (hNc _ hPN u u.2).symm
        have hgu : g * (u : G) * g⁻¹ = (g * (u : G) * g⁻¹ * (u : G)⁻¹) * (u : G) := by group
        have hgv : g * (v : G) * g⁻¹ = (g * (v : G) * g⁻¹ * (v : G)⁻¹) * (v : G) := by group
        show g * ((u : G) * (v : G)) * g⁻¹ * ((u : G) * (v : G))⁻¹
          = (g * (u : G) * g⁻¹ * (u : G)⁻¹) * (g * (v : G) * g⁻¹ * (v : G)⁻¹)
        calc g * ((u : G) * (v : G)) * g⁻¹ * ((u : G) * (v : G))⁻¹
            = (g * (u : G) * g⁻¹) * (g * (v : G) * g⁻¹) * (v : G)⁻¹ * (u : G)⁻¹ := by group
          _ = ((g * (u : G) * g⁻¹ * (u : G)⁻¹) * (u : G)) * ((g * (v : G) * g⁻¹ * (v : G)⁻¹) * (v : G))
                * (v : G)⁻¹ * (u : G)⁻¹ := by rw [← hgu, ← hgv]
          _ = (g * (u : G) * g⁻¹ * (u : G)⁻¹) * ((u : G) * (g * (v : G) * g⁻¹ * (v : G)⁻¹))
                * (u : G)⁻¹ := by group
          _ = (g * (u : G) * g⁻¹ * (u : G)⁻¹) * ((g * (v : G) * g⁻¹ * (v : G)⁻¹) * (u : G))
                * (u : G)⁻¹ := by rw [hc]
          _ = (g * (u : G) * g⁻¹ * (u : G)⁻¹) * (g * (v : G) * g⁻¹ * (v : G)⁻¹) := by group }
  exfalso
  have hker_le : (ρ.ker).map M.subtype ≤ M ⊓ Subgroup.centralizer {y} := by
    rintro _ ⟨u, hu, rfl⟩
    have hu1 : ρ u = 1 := hu
    have h1 : g * (u : G) * g⁻¹ * (u : G)⁻¹ = 1 := congrArg Subtype.val hu1
    have hgu : g * (u : G) = (u : G) * g := by
      calc g * (u : G) = (g * (u : G) * g⁻¹ * (u : G)⁻¹) * (u : G) * g := by group
        _ = (u : G) * g := by rw [h1]; group
    refine Subgroup.mem_inf.mpr ⟨u.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact (comm_of_pow_comm hy3 hy1 hgy hg1 hgu.symm).symm
  have hcard_ker : Nat.card ↥((ρ.ker).map M.subtype) = Nat.card ↥ρ.ker :=
    Subgroup.card_map_of_injective (f := M.subtype) (fun a b h => Subtype.ext h)
  have hle27 : Nat.card ↥((ρ.ker).map M.subtype) ≤ 27 := by
    rw [← hyM]; exact Subgroup.card_le_of_le hker_le
  have hidx := Subgroup.card_mul_index ρ.ker
  have hind := Subgroup.index_ker ρ
  have hrange : Nat.card ↥ρ.range ≤ 3 := by
    rw [← hN3]; exact Subgroup.card_le_card_group _
  rw [hM243, hind] at hidx
  nlinarith

theorem zpow_inter_bot [Finite G] {σ τ : G} {P : Subgroup G}
    (hPgen : ∀ p ∈ P, ∃ a b : ℤ, σ ^ a * τ ^ b = p) (hP9 : Nat.card ↥P = 9)
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    Subgroup.zpowers σ ⊓ Subgroup.zpowers τ = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσo : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hτo : orderOf τ = 3 := orderOf_eq_prime hτ3 hτ1
  have hσc : Nat.card ↥(Subgroup.zpowers σ) = 3 := by rw [Nat.card_zpowers, hσo]
  have hdvd : Nat.card ↥(Subgroup.zpowers σ ⊓ Subgroup.zpowers τ) ∣ 3 := by
    rw [← hσc]; exact Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have heq : Subgroup.zpowers σ ⊓ Subgroup.zpowers τ = Subgroup.zpowers σ :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hσc])
    have hστ : σ ∈ Subgroup.zpowers τ := by
      have : σ ∈ Subgroup.zpowers σ ⊓ Subgroup.zpowers τ := by
        rw [heq]; exact Subgroup.mem_zpowers σ
      exact (Subgroup.mem_inf.mp this).2
    have hPle : P ≤ Subgroup.zpowers τ := by
      intro p hp
      obtain ⟨a, b, rfl⟩ := hPgen p hp
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hστ
      rw [← hk, ← zpow_mul]
      exact (Subgroup.zpowers τ).mul_mem (Subgroup.zpow_mem_zpowers τ _)
        (Subgroup.zpow_mem_zpowers τ _)
    have h9 : Nat.card ↥P ≤ Nat.card ↥(Subgroup.zpowers τ) := Subgroup.card_le_of_le hPle
    rw [hP9, Nat.card_zpowers, hτo] at h9
    omega

theorem normalizer_cases {σ t x : G} (σ3 : σ ^ 3 = 1) (σ1 : σ ≠ 1) (tσ : t * σ * t⁻¹ = σ⁻¹)
    (hx : x ∈ Subgroup.normalizer (Subgroup.zpowers σ : Set G)) :
    x ∈ Subgroup.centralizer {σ} ∨ t * x ∈ Subgroup.centralizer {σ} := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxσ : x * σ * x⁻¹ ∈ Subgroup.zpowers σ := by
    have := (Subgroup.mem_normalizer_iff.mp hx) σ
    exact this.mp (Subgroup.mem_zpowers σ)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxσ
  have hord : orderOf σ = 3 := orderOf_eq_prime σ3 σ1
  have hjm : σ ^ (j % 3) = σ ^ j := by
    have := zpow_mod_orderOf σ j
    rw [hord] at this
    exact this
  have hr : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  have hsq : σ * σ = σ⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc σ * σ * σ = σ ^ 3 := by rw [pow_three, mul_assoc]
      _ = 1 := σ3
  have hcent : ∀ w : G, w * σ * w⁻¹ = σ → w ∈ Subgroup.centralizer {σ} := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    calc σ * w = (w * σ * w⁻¹) * w := by rw [hw]
      _ = w * σ := by group
  rcases hr with h0 | h1 | h2
  · exfalso
    have h1' : x * σ * x⁻¹ = 1 := by rw [← hj, ← hjm, h0, zpow_zero]
    apply σ1
    calc σ = x⁻¹ * (x * σ * x⁻¹) * x := by group
      _ = 1 := by rw [h1']; group
  · left
    have h1' : x * σ * x⁻¹ = σ := by rw [← hj, ← hjm, h1, zpow_one]
    exact hcent x h1'
  · right
    have h1' : x * σ * x⁻¹ = σ⁻¹ := by
      rw [← hj, ← hjm, h2, zpow_two, hsq]
    apply hcent
    calc (t * x) * σ * (t * x)⁻¹ = t * (x * σ * x⁻¹) * t⁻¹ := by group
      _ = t * σ⁻¹ * t⁻¹ := by rw [h1']
      _ = (t * σ * t⁻¹)⁻¹ := by group
      _ = σ := by rw [tσ]; group

theorem card_normalizer_dvd [Finite G] {σ t : G} (σ3 : σ ^ 3 = 1) (σ1 : σ ≠ 1)
    (tσ : t * σ * t⁻¹ = σ⁻¹) (ht : t ∈ Subgroup.normalizer (Subgroup.zpowers σ : Set G))
    (t2 : t * t = 1) :
    Nat.card ↥(Subgroup.normalizer (Subgroup.zpowers σ : Set G)) ∣
      2 * Nat.card ↥(Subgroup.centralizer {σ}) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X : Subgroup G := Subgroup.normalizer (Subgroup.zpowers σ : Set G) with hXdef
  set C : Subgroup G := Subgroup.centralizer {σ} with hCdef
  have hCX : C ≤ X := by
    intro c hc
    have hc' : c * σ = σ * c := (Subgroup.mem_centralizer_iff.mp hc σ (Set.mem_singleton σ)).symm
    have hconj : ∀ k : ℤ, c * σ ^ k * c⁻¹ = σ ^ k := by
      intro k
      have hcomm : Commute c (σ ^ k) := (show Commute c σ from hc').zpow_right k
      calc c * σ ^ k * c⁻¹ = σ ^ k * c * c⁻¹ := by rw [hcomm.eq]
        _ = σ ^ k := by group
    rw [hXdef, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      rw [hconj k]
      exact Subgroup.zpow_mem_zpowers σ k
    · intro hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hconjinv : c⁻¹ * σ ^ k * c = σ ^ k := by
        calc c⁻¹ * σ ^ k * c = c⁻¹ * (c * σ ^ k * c⁻¹) * c := by rw [hconj k]
          _ = σ ^ k := by group
      have : h = σ ^ k := by
        calc h = c⁻¹ * (c * h * c⁻¹) * c := by group
          _ = c⁻¹ * σ ^ k * c := by rw [← hk]
          _ = σ ^ k := hconjinv
      rw [this]
      exact Subgroup.zpow_mem_zpowers σ k
  have hK : Nat.card ↥(C.subgroupOf X) = Nat.card ↥C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCX).toEquiv
  have hidx : (C.subgroupOf X).index ≤ 2 := by
    let f : Bool → ↥X ⧸ C.subgroupOf X := fun b =>
      QuotientGroup.mk (if b then (⟨t, ht⟩ : ↥X) else 1)
    have hf : Function.Surjective f := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      rcases normalizer_cases σ3 σ1 tσ x.2 with hxC | htxC
      · refine ⟨false, ?_⟩
        show QuotientGroup.mk (1 : ↥X) = QuotientGroup.mk x
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa using hxC
      · refine ⟨true, ?_⟩
        show QuotientGroup.mk (⟨t, ht⟩ : ↥X) = QuotientGroup.mk x
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right t2
        show t⁻¹ * (x : G) ∈ C
        rw [hti]
        exact htxC
    have := Nat.card_le_card_of_surjective f hf
    simpa [Subgroup.index] using this
  have hidx0 : (C.subgroupOf X).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hdiv : (C.subgroupOf X).index ∣ 2 := by
    have : (C.subgroupOf X).index = 1 ∨ (C.subgroupOf X).index = 2 := by omega
    rcases this with h1 | h1 <;> rw [h1] <;> norm_num
  have hcm := Subgroup.card_mul_index (C.subgroupOf X)
  rw [hK] at hcm
  rw [← hcm]
  calc Nat.card ↥C * (C.subgroupOf X).index ∣ Nat.card ↥C * 2 := mul_dvd_mul_left _ hdiv
    _ = 2 * Nat.card ↥C := mul_comm _ _

theorem normS_le [Finite G] {M : Subgroup G} {σ y : G} {hM : M ≤ Subgroup.centralizer {σ}}
    {hnorm : ∀ g ∈ Subgroup.centralizer {σ}, ∀ m ∈ M, g * m * g⁻¹ ∈ M}
    {hy : y ∈ Subgroup.centralizer {σ}}
    (hNc : ∀ n ∈ Subgroup.zpowers σ, ∀ u ∈ M, n * u = u * n)
    (hNM : Subgroup.zpowers σ ≤ M) (hyσ : σ * y = y * σ)
    (hZS : ∀ x ∈ mkSS M σ y hM hnorm hy, (∀ s ∈ mkSS M σ y hM hnorm hy, x * s = s * x) →
      x ∈ Subgroup.zpowers σ) :
    Subgroup.normalizer ((mkSS M σ y hM hnorm hy : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers σ : Set G) := by
  set S : Subgroup G := mkSS M σ y hM hnorm hy with hSdef
  have hNS : ∀ n ∈ Subgroup.zpowers σ, n ∈ S := fun n hn =>
    ⟨n, hNM hn, 0, by simp⟩
  have hNy : ∀ n ∈ Subgroup.zpowers σ, n * y = y * n := by
    intro n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have : Commute σ y := hyσ
    exact (this.zpow_left k).eq
  have key : ∀ g ∈ Subgroup.normalizer (S : Set G), ∀ n ∈ Subgroup.zpowers σ,
      g * n * g⁻¹ ∈ Subgroup.zpowers σ := by
    intro g hg n hn
    have hgS : ∀ s ∈ S, g * s * g⁻¹ ∈ S := fun s hs => (Subgroup.mem_normalizer_iff.mp hg s).mp hs
    have hginv : ∀ s ∈ S, g⁻¹ * s * g ∈ S := by
      intro s hs
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) s).mp hs
      simpa using this
    have hgn : g * n * g⁻¹ ∈ S := hgS n (hNS n hn)
    apply hZS _ hgn
    intro s hs
    have hs' := hginv s hs
    have hcomm_s : ∀ t ∈ S, n * t = t * n := by
      intro t ht
      obtain ⟨m, hm, k, rfl⟩ := ht
      have h1 : n * m = m * n := hNc n hn m hm
      have h2 : n * y ^ k = y ^ k * n := by
        have : Commute n y := hNy n hn
        exact (this.zpow_right k).eq
      calc n * (m * y ^ k) = (n * m) * y ^ k := by group
        _ = (m * n) * y ^ k := by rw [h1]
        _ = m * (n * y ^ k) := by group
        _ = m * (y ^ k * n) := by rw [h2]
        _ = (m * y ^ k) * n := by group
    have hcs := hcomm_s _ hs'
    calc (g * n * g⁻¹) * s = g * n * (g⁻¹ * s * g) * g⁻¹ := by group
      _ = g * ((g⁻¹ * s * g) * n) * g⁻¹ := by rw [← hcs]; group
      _ = g * (g⁻¹ * s * g) * n * g⁻¹ := by group
      _ = s * (g * n * g⁻¹) := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact key g hg h hh
  · intro hh
    have h2 := key g⁻¹ (inv_mem hg) _ hh
    have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rw [e] at h2
    exact h2

theorem zpow3_cases {σ : G} (σ3 : σ ^ 3 = 1) (σ1 : σ ≠ 1) (k : ℤ) :
    σ ^ k = 1 ∨ σ ^ k = σ ∨ σ ^ k = σ⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf σ = 3 := orderOf_eq_prime σ3 σ1
  have hjm : σ ^ (k % 3) = σ ^ k := by
    have := zpow_mod_orderOf σ k
    rw [hord] at this
    exact this
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  have hsq : σ * σ = σ⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc σ * σ * σ = σ ^ 3 := by rw [pow_three, mul_assoc]
      _ = 1 := σ3
  rcases hr with h0 | h1 | h2
  · left; rw [← hjm, h0, zpow_zero]
  · right; left; rw [← hjm, h1, zpow_one]
  · right; right; rw [← hjm, h2, zpow_two, hsq]

namespace VxData

variable {H M M' P : Subgroup G} {z t σ τ : G}

open scoped Pointwise in
theorem sylow_contra [Finite G] (d : VxData H z t σ τ M M' P)
    (hZM : ∀ x ∈ M, (∀ y ∈ M, x * y = y * x) → x ∈ Subgroup.zpowers σ) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hτC : τ ∈ Subgroup.centralizer {σ} :=
    Subgroup.mem_centralizer_iff.mpr (fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]; exact d.στ)
  have hσC' : σ ∈ Subgroup.centralizer {τ} :=
    Subgroup.mem_centralizer_iff.mpr (fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]; exact d.στ.symm)
  set S : Subgroup G := mkSS M σ τ d.MC d.Mnorm hτC with hSdef
  set S₂ : Subgroup G := mkSS M' τ σ d.M'C d.M'norm hσC' with hS₂def
  have hτH : Subgroup.zpowers τ ≤ H := (Subgroup.zpowers_le).mpr d.τH
  have hσH : Subgroup.zpowers σ ≤ H := (Subgroup.zpowers_le).mpr d.σH
  have hMy : M ⊓ Subgroup.zpowers τ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxM, hxτ⟩ := Subgroup.mem_inf.mp hx
    have hxH : x ∈ M ⊓ H := Subgroup.mem_inf.mpr ⟨hxM, hτH hxτ⟩
    rw [d.MH] at hxH
    have hb := zpow_inter_bot d.Pgen d.P9 d.σ3 d.σ1 d.τ3 d.τ1
    have hmem : x ∈ Subgroup.zpowers σ ⊓ Subgroup.zpowers τ := Subgroup.mem_inf.mpr ⟨hxH, hxτ⟩
    rw [hb, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact hmem
  have hM'y : M' ⊓ Subgroup.zpowers σ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxM, hxσ⟩ := Subgroup.mem_inf.mp hx
    have hxH : x ∈ M' ⊓ H := Subgroup.mem_inf.mpr ⟨hxM, hσH hxσ⟩
    rw [d.M'H] at hxH
    have hPswap : ∀ p ∈ P, ∃ a b : ℤ, τ ^ a * σ ^ b = p := by
      intro p hp
      obtain ⟨a, b, hab⟩ := d.Pgen p hp
      exact ⟨b, a, by
        rw [← hab]
        exact (((show Commute τ σ from d.στ.symm).zpow_left b).zpow_right a).eq⟩
    have hb := zpow_inter_bot hPswap d.P9 d.τ3 d.τ1 d.σ3 d.σ1
    have hmem : x ∈ Subgroup.zpowers τ ⊓ Subgroup.zpowers σ := Subgroup.mem_inf.mpr ⟨hxH, hxσ⟩
    rw [hb, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact hmem
  have hN3 : Nat.card ↥(Subgroup.zpowers σ) = 3 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime d.σ3 d.σ1
  have hS729 : Nat.card ↥S = 729 := card_mkSS hMy d.M243 d.τ3 d.τ1
  have hS₂729 : Nat.card ↥S₂ = 729 := card_mkSS hM'y d.M'243 d.σ3 d.σ1
  have hZS := fun hyy : (τ ^ 3 = 1) => center_mkSS (hM := d.MC) (hnorm := d.Mnorm) (hy := hτC)
    hZM d.Ncent d.comm d.N_le_M hN3 d.M243 d.Mτ hyy d.τ1
  have hNS := normS_le (hM := d.MC) (hnorm := d.Mnorm) (hy := hτC) d.Ncent d.N_le_M d.στ
    (hZS d.τ3)
  have ht : t ∈ Subgroup.normalizer (Subgroup.zpowers σ : Set G) := by
    rw [d.Nσ]; exact (le_sup_right : Subgroup.zpowers t ≤ _ ⊔ _) (Subgroup.mem_zpowers t)
  have hsyl : ¬ (3 ^ 7 ∣ Nat.card G) := by
    intro hdvd
    have hS6 : Nat.card ↥S = 3 ^ 6 := by rw [hS729]; norm_num
    have hdvd' : 3 ^ (6 + 1) ∣ Nat.card G := by norm_num; exact hdvd
    have h1 := Sylow.prime_pow_dvd_card_normalizer hdvd' hS6
    have h2 : Nat.card ↥(Subgroup.normalizer ((S : Subgroup G) : Set G)) ∣
        Nat.card ↥(Subgroup.normalizer (Subgroup.zpowers σ : Set G)) :=
      Subgroup.card_dvd_of_le hNS
    have h3 := card_normalizer_dvd d.σ3 d.σ1 d.tσ ht d.t2
    rw [d.Cσ] at h3
    have h4 := dvd_trans h1 (dvd_trans h2 h3)
    norm_num at h4
  have hcopS : ¬ 3 ∣ S.index := by
    intro h3ind
    apply hsyl
    have hcm := Subgroup.card_mul_index S
    rw [← hcm, hS729]
    have e7 : (3 : ℕ) ^ 7 = 729 * 3 := by norm_num
    rw [e7]
    exact mul_dvd_mul_left 729 h3ind
  have hcopS₂ : ¬ 3 ∣ S₂.index := by
    intro h3ind
    apply hsyl
    have hcm := Subgroup.card_mul_index S₂
    rw [← hcm, hS₂729]
    have e7 : (3 : ℕ) ^ 7 = 729 * 3 := by norm_num
    rw [e7]
    exact mul_dvd_mul_left 729 h3ind
  have hP1 : IsPGroup 3 S := IsPGroup.of_card (show Nat.card ↥S = 3 ^ 6 by rw [hS729]; norm_num)
  have hP2 : IsPGroup 3 S₂ :=
    IsPGroup.of_card (show Nat.card ↥S₂ = 3 ^ 6 by rw [hS₂729]; norm_num)
  let Ssyl : Sylow 3 G := hP1.toSylow hcopS
  let S₂syl : Sylow 3 G := hP2.toSylow hcopS₂
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Ssyl S₂syl
  have hset : (S₂ : Set G) = MulAut.conj g • (S : Set G) := by
    have := congrArg (fun Q : Sylow 3 G => (Q : Set G)) hg
    exact this.symm.trans Sylow.coe_smul
  have hfwd : ∀ s ∈ S, g * s * g⁻¹ ∈ S₂ := by
    intro s hs
    have : g * s * g⁻¹ ∈ (S₂ : Set G) := by
      rw [hset]
      exact ⟨s, hs, rfl⟩
    exact this
  have hbwd : ∀ x ∈ S₂, g⁻¹ * x * g ∈ S := by
    intro x hx
    have : x ∈ (S₂ : Set G) := hx
    rw [hset] at this
    obtain ⟨s, hs, hsx⟩ := this
    have e : g⁻¹ * x * g = s := by
      rw [← hsx]
      show g⁻¹ * (g * s * g⁻¹) * g = s
      group
    rw [e]
    exact hs
  have hτM' : τ ∈ M' ⊓ H := by rw [d.M'H]; exact Subgroup.mem_zpowers τ
  have hτS₂ : τ ∈ S₂ := ⟨τ, (Subgroup.mem_inf.mp hτM').1, 0, by simp⟩
  have hcenS₂ : ∀ x ∈ S₂, τ * x = x * τ := by
    intro x hx
    obtain ⟨m', hm', k, rfl⟩ := hx
    have h1 : τ * m' = m' * τ :=
      Subgroup.mem_centralizer_iff.mp (d.M'C hm') τ (Set.mem_singleton τ)
    have h2 : τ * σ ^ k = σ ^ k * τ :=
      (Commute.zpow_right (show Commute τ σ from d.στ.symm) k).eq
    calc τ * (m' * σ ^ k) = (τ * m') * σ ^ k := by group
      _ = (m' * τ) * σ ^ k := by rw [h1]
      _ = m' * (τ * σ ^ k) := by group
      _ = m' * (σ ^ k * τ) := by rw [h2]
      _ = (m' * σ ^ k) * τ := by group
  set u : G := g⁻¹ * τ * g with hudef
  have huS : u ∈ S := hbwd τ hτS₂
  have hucen : ∀ s ∈ S, u * s = s * u := by
    intro s hs
    have hs₂ := hfwd s hs
    have hc := hcenS₂ _ hs₂
    calc u * s = g⁻¹ * (τ * (g * s * g⁻¹)) * g := by rw [hudef]; group
      _ = g⁻¹ * ((g * s * g⁻¹) * τ) * g := by rw [hc]
      _ = s * u := by rw [hudef]; group
  have hu_mem : u ∈ Subgroup.zpowers σ := hZS d.τ3 u huS hucen
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu_mem
  have hτ_eq : τ = g * u * g⁻¹ := by rw [hudef]; group
  rcases zpow3_cases d.σ3 d.σ1 k with h0 | h1 | h2
  · apply d.τ1
    rw [hτ_eq, ← hk, h0]
    group
  · apply d.nc
    refine isConj_iff.mpr ⟨g, ?_⟩
    rw [hτ_eq, ← hk, h1]
  · apply d.nc
    refine isConj_iff.mpr ⟨g * t, ?_⟩
    rw [hτ_eq, ← hk, h2]
    calc g * t * σ * (g * t)⁻¹ = g * (t * σ * t⁻¹) * g⁻¹ := by group
      _ = g * σ⁻¹ * g⁻¹ := by rw [d.tσ]

end VxData

open scoped Pointwise in
theorem card_of_centComplement [Finite G] {C L N : Subgroup G}
    (h : IsCentComplement C L N) : Nat.card ↥C = Nat.card ↥N * Nat.card ↥L := by
  have hNnorm : (N.subgroupOf C).Normal := by
    refine ⟨fun n hn c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact h.conj_mem c.1 c.2 n.1 hn
  have hdisj : Disjoint (N.subgroupOf C) (L.subgroupOf C) := by
    rw [Subgroup.disjoint_def]
    intro x hxN hxL
    have hx1 : (x : G) ∈ N ⊓ L :=
      ⟨Subgroup.mem_subgroupOf.mp hxN, Subgroup.mem_subgroupOf.mp hxL⟩
    rw [h.disjoint, Subgroup.mem_bot] at hx1
    exact Subtype.ext hx1
  have hLE : L ≤ Subgroup.normalizer (N : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact h.conj_mem l (h.right_le hl) x hx
    · intro hx
      have h2 := h.conj_mem l⁻¹ (C.inv_mem (h.right_le hl)) _ hx
      have e : l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ = x := by group
      rw [e] at h2
      exact h2
  have hmul : (N.subgroupOf C : Set ↥C) * (L.subgroupOf C : Set ↥C) = Set.univ := by
    ext c
    simp only [Set.mem_mul, SetLike.mem_coe, Set.mem_univ, iff_true]
    have hc : (c : G) ∈ N ⊔ L := by rw [h.sup_eq]; exact c.2
    have hc' : (c : G) ∈ ((N ⊔ L : Subgroup G) : Set G) := hc
    rw [Subgroup.coe_mul_of_right_le_normalizer_left N L hLE] at hc'
    obtain ⟨n, hn, l, hl, hnl⟩ := Set.mem_mul.mp hc'
    refine ⟨⟨n, h.left_le hn⟩, Subgroup.mem_subgroupOf.mpr hn, ⟨l, h.right_le hl⟩,
      Subgroup.mem_subgroupOf.mpr hl, Subtype.ext ?_⟩
    exact hnl
  have hcomp := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
  have h1 := hcomp.card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.left_le).toEquiv] at h1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.right_le).toEquiv] at h1
  exact h1.symm

namespace VxData

variable {H M M' P : Subgroup G} {z t σ τ : G}

theorem vertex [Finite G] (d : VxData H z t σ τ M M' P) :
    (∀ m ∈ M, m ^ 3 = 1) ∧ (∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers σ) ∧
    (∃ x ∈ M, ∃ y ∈ M, x * y ≠ y * x) ∧
    Nat.card ↥(M ⊓ Subgroup.centralizer (M : Set G)) = 27 ∧
    (∀ m ∈ M, z * m * z⁻¹ * m ∈ Subgroup.zpowers σ) := by
  have hB1exp := (d.B_facts (u := t) d.ct d.MB).1
  have hB2exp := (d.B_facts (u := t * z) d.ctz d.MBz).1
  exact ⟨d.exp3_M hB1exp hB2exp, d.comm, d.nonab, d.card_Z (fun h => sylow_contra d h), d.zinv⟩

end VxData

end CFSG.GH74.QTGen4.Recog.G23.P7.MS
