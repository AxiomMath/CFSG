module

public import CFSG.GH74.M12.T1Syl
public import CFSG.GH74.M12.T1GL
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.GH74.M12.Thm1

open Subgroup CFSG.Quasithin
open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

theorem isSimpleGroup_GL3_two : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  let e₁ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.ProjGenLinGroup (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
      ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL_injective,
        Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots fun r =>
          ⟨1, Subsingleton.elim _ _⟩⟩
  have hZ : Subgroup.center (GL (Fin 3) (ZMod 2)) = ⊥ := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
    rintro _ ⟨r, rfl⟩
    rw [Subsingleton.elim r 1, map_one]
    exact Subgroup.one_mem _
  let e₂ : Matrix.ProjGenLinGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact (e₁.trans e₂).symm.isSimpleGroup

theorem z_mem_of_normal_of_mem [Finite G] (hyp : Asc03Hyp G z) {X : Subgroup G} (hX : X.Normal)
    {q : G} (hqX : q ∈ X) (hqQ : q ∈ ascQ z) (hq1 : q ≠ 1) : z ∈ X := by
  have hE := extraspecialAt_ascQ hyp
  by_cases hqz : q = z
  · rw [← hqz]; exact hqX
  · have hnc : ¬ ∀ r ∈ ascQ z, q * r = r * q := fun h =>
      (hE.center_le q hqQ h).elim hq1 hqz
    push Not at hnc
    obtain ⟨r, hrQ, hqr⟩ := hnc
    rcases hE.comm_mem r hrQ q hqQ with h | h
    · exfalso; apply hqr
      calc q * r = (r * q * r⁻¹ * q⁻¹)⁻¹ * (r * q) := by group
        _ = r * q := by rw [h]; group
    · rw [← h]
      exact X.mul_mem (hX.conj_mem q hqX r) (X.inv_mem hqX)

theorem z_mem_of_normal [Finite G] (hyp : Asc03Hyp G z) {X : Subgroup G} (hX : X.Normal)
    (hX1 : X ≠ ⊥) : z ∈ X := by
  have hE := extraspecialAt_ascQ hyp
  by_contra hz
  have hXQ : ∀ q ∈ X, q ∈ ascQ z → q = 1 := by
    intro q hqX hqQ
    by_contra hq1
    exact hz (z_mem_of_normal_of_mem hyp hX hqX hqQ hq1)
  have hXH : ∀ n ∈ X, n ∈ ascH z → n = 1 := by
    intro n hnX hnH
    have hcomm : ∀ q ∈ ascQ z, n * q = q * n := by
      intro q hq
      have h1 : n * q * n⁻¹ * q⁻¹ ∈ X := by
        have := X.mul_mem hnX (hX.conj_mem n⁻¹ (X.inv_mem hnX) q)
        simpa [mul_assoc] using this
      have h2 : n * q * n⁻¹ * q⁻¹ ∈ ascQ z :=
        (ascQ z).mul_mem (conj_mem_ascQ hnH hq) ((ascQ z).inv_mem hq)
      have := hXQ _ h1 h2
      calc n * q = (n * q * n⁻¹ * q⁻¹) * (q * n) := by group
        _ = q * n := by rw [this, one_mul]
    rcases eq_of_cent_ascQ hyp hnH hcomm with h | h
    · exact h
    · exact absurd (h ▸ hnX) hz
  have hinv : ∀ t : G, t * t = 1 → (∀ n ∈ X, n * t = t * n → n = 1) →
      ∀ n ∈ X, t * n * t⁻¹ = n⁻¹ := by
    intro t ht2 htc
    let φ : ↥X →* ↥X :=
      { toFun := fun n => ⟨t * n * t⁻¹, hX.conj_mem n n.2 t⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have hfpf : MonoidHom.FixedPointFree ⇑φ := by
      intro n hn
      have h1 : t * (n : G) * t⁻¹ = n := congrArg Subtype.val hn
      apply Subtype.ext
      apply htc n n.2
      calc (n : G) * t = (t * n * t⁻¹) * t := by rw [h1]
        _ = t * n := by group
    have hinvol : Function.Involutive ⇑φ := by
      intro n
      apply Subtype.ext
      show t * (t * (n : G) * t⁻¹) * t⁻¹ = n
      calc t * (t * (n : G) * t⁻¹) * t⁻¹ = (t * t) * n * (t * t)⁻¹ := by group
        _ = n := by rw [ht2]; group
    have heq := MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hfpf hinvol
    intro n hn
    have := congrFun heq ⟨n, hn⟩
    exact congrArg Subtype.val this
  have hzinv := hinv z hE.sq_eq (fun n hnX hnz => hXH n hnX
    (Subgroup.mem_centralizer_singleton_iff.2 hnz))
  obtain ⟨g, hgz, q0, hq0P, hq0⟩ := hyp.not_weakly_closed
  have hsQ' : g * z * g⁻¹ ∈ ascQ z := by
    rw [← hq0]; exact (mem_ascQ_iff z _).2 ⟨q0.2, hq0P⟩
  have hs2' : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := by
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hE.sq_eq]; group
  set s := g * z * g⁻¹ with hs
  have hsQ : s ∈ ascQ z := hsQ'
  have hs2 : s * s = 1 := hs2'
  have hsinv := hinv s hs2 (fun n hnX hns => by
    have h1 : g⁻¹ * n * g ∈ X := by simpa using hX.conj_mem n hnX g⁻¹
    have h2 : g⁻¹ * n * g ∈ ascH z := by
      rw [ascH, Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * n * g * z = g⁻¹ * (n * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * z * g⁻¹) * n) * g := by rw [← hs, hns]
        _ = z * (g⁻¹ * n * g) := by group
    have := hXH _ h1 h2
    calc n = g * (g⁻¹ * n * g) * g⁻¹ := by group
      _ = 1 := by rw [this]; group)
  have hzs : ∀ n ∈ X, n * (z * s) = (z * s) * n := by
    intro n hn
    have h1 := hsinv n hn
    have h2 := hzinv n⁻¹ (X.inv_mem hn)
    have : (z * s) * n * (z * s)⁻¹ = n := by
      calc (z * s) * n * (z * s)⁻¹ = z * (s * n * s⁻¹) * z⁻¹ := by group
        _ = z * n⁻¹ * z⁻¹ := by rw [h1]
        _ = n := by rw [h2, inv_inv]
    calc n * (z * s) = ((z * s) * n * (z * s)⁻¹) * (z * s) := by rw [this]
      _ = (z * s) * n := by group
  set Y := Subgroup.centralizer (X : Set G) with hY
  have hYn : Y.Normal := by
    refine ⟨fun c hc h => ?_⟩
    rw [hY, Subgroup.mem_centralizer_iff] at hc ⊢
    intro n hn
    have hn' : h⁻¹ * n * h ∈ X := by simpa using hX.conj_mem n hn h⁻¹
    have := hc _ hn'
    calc n * (h * c * h⁻¹) = h * ((h⁻¹ * n * h) * c) * h⁻¹ := by group
      _ = h * (c * (h⁻¹ * n * h)) * h⁻¹ := by rw [this]
      _ = h * c * h⁻¹ * n := by group
  have hzsY : z * s ∈ Y := by
    rw [hY, Subgroup.mem_centralizer_iff]
    exact hzs
  have hzs1 : z * s ≠ 1 := by
    intro h
    apply hgz
    have : s = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, inv_eq_of_mul_eq_one_right hE.sq_eq]
  have hzY := z_mem_of_normal_of_mem hyp hYn hzsY ((ascQ z).mul_mem hE.mem hsQ) hzs1
  apply hX1
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  apply hXH n hn
  rw [ascH, Subgroup.mem_centralizer_singleton_iff]
  exact ((Subgroup.mem_centralizer_iff.1 hzY) n hn)

theorem eq_ascQ_of_comm [Finite G] (hyp : Asc03Hyp G z) {y : G} (hy : y ∈ ascH z)
    (hy3 : orderOf y = 3) {U : Subgroup G} (hUQ : U ≤ ascQ z) (hzU : z ∈ U)
    (hUy : ∀ u ∈ U, y * u * y⁻¹ ∈ U) (hcomm : ∀ q ∈ ascQ z, q * y * q⁻¹ * y⁻¹ ∈ U) :
    U = ascQ z := by
  have hcard := card_of_inv hyp hy hy3 hUQ hzU hUy
  rcases hcard with h | h | h
  rotate_right
  · exact Subgroup.eq_of_le_of_card_ge hUQ (by rw [h, card_ascQ hyp])
  all_goals
    exfalso
    have hne : ¬ ascQ z ≤ U := by
      intro hle
      have := Subgroup.card_le_of_le hle
      rw [card_ascQ hyp] at this
      omega
    obtain ⟨q, hqQ, hqU⟩ := IsConcreteLE.not_le_iff_exists.1 hne
    set C : Set G := {x | x ∈ ascQ z ∧ q⁻¹ * x ∈ U} with hC
    have hyC : ∀ x ∈ C, y * x * y⁻¹ ∈ C := by
      rintro x ⟨hxQ, hxU⟩
      refine ⟨conj_mem_ascQ hy hxQ, ?_⟩
      have h1 := hcomm q⁻¹ ((ascQ z).inv_mem hqQ)
      have h2 := hUy _ hxU
      have : q⁻¹ * (y * x * y⁻¹) = (q⁻¹ * y * q⁻¹⁻¹ * y⁻¹) * (y * (q⁻¹ * x) * y⁻¹) := by group
      rw [this]
      exact U.mul_mem h1 h2
    have hyC' : ∀ x ∈ C, y⁻¹ * x * y ∈ C := by
      intro x hx
      have hyyy := mul_self_mul_self_eq_one hy3
      have : y⁻¹ * x * y = y * (y * x * y⁻¹) * y⁻¹ := by
        calc y⁻¹ * x * y = (y * y * y) * (y⁻¹ * x * y) * (y * y * y)⁻¹ := by rw [hyyy]; group
          _ = y * (y * x * y⁻¹) * y⁻¹ := by group
      rw [this]; exact hyC _ (hyC x hx)
    let σ : Equiv.Perm ↥C :=
      { toFun := fun x => ⟨y * x * y⁻¹, hyC x x.2⟩
        invFun := fun x => ⟨y⁻¹ * x * y, hyC' x x.2⟩
        left_inv := fun x => Subtype.ext (by simp [mul_assoc])
        right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
    have hyyy := mul_self_mul_self_eq_one hy3
    have hσ3 : σ ^ 3 = 1 := by
      ext x
      show y * (y * (y * x * y⁻¹) * y⁻¹) * y⁻¹ = x
      calc y * (y * (y * (x : G) * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * x * (y * y * y)⁻¹ := by
            group
        _ = x := by rw [hyyy]; group
    have hCcard : Nat.card ↥C = Nat.card ↥U := by
      refine Nat.card_congr
        { toFun := fun x => ⟨q⁻¹ * x, x.2.2⟩
          invFun := fun u => ⟨q * u, (ascQ z).mul_mem hqQ (hUQ u.2), by simp⟩
          left_inv := fun x => Subtype.ext (by simp)
          right_inv := fun u => Subtype.ext (by simp) }
    by_cases hfix : ∀ x, σ x ≠ x
    · have h3 := three_dvd_card_of_fpf σ hσ3 hfix
      rw [hCcard] at h3
      omega
    · push Not at hfix
      obtain ⟨x, hx⟩ := hfix
      have hx' : y * (x : G) * y⁻¹ = x := congrArg Subtype.val hx
      have hxQ : (x : G) ∈ ascQ z := x.2.1
      rcases eq_of_conj_mem hyp hy hy3 hxQ (Or.inl hx') with h1 | h1
      · apply hqU
        have := x.2.2
        rw [h1, mul_one] at this
        simpa using U.inv_mem this
      · apply hqU
        have := x.2.2
        rw [h1] at this
        have h2 := U.mul_mem hzU (U.inv_mem this)
        simpa [mul_assoc] using h2

theorem false_of_cent_le_conj [Finite G] (hyp : Asc03Hyp G z) {g : G} (hgz : g * z * g⁻¹ ≠ z)
    (hsQ : g * z * g⁻¹ ∈ ascQ z)
    (h : ∀ x ∈ ascQ z, x * (g * z * g⁻¹) = (g * z * g⁻¹) * x → g⁻¹ * x * g ∈ ascQ z) : False := by
  have hE := extraspecialAt_ascQ hyp
  obtain ⟨-, hE8, -, -, -⟩ := config_of_conj hyp hgz hsQ
  have hs1 : g * z * g⁻¹ ≠ 1 := asc_conj_ne_one hyp g
  obtain ⟨h16, -⟩ := hE.exists_sq_eq_of_noncentral hsQ hs1 hgz
  have hle : ascQ z ⊓ Subgroup.centralizer ({g * z * g⁻¹} : Set G) ≤
      ascQ z ⊓ (ascQ z).map (MulAut.conj g).toMonoidHom := by
    intro x hx
    refine ⟨hx.1, (mem_map_conj_iff _ g x).2 (h x hx.1 ?_)⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 hx.2
  have := Subgroup.card_le_of_le hle
  rw [h16, hE8] at this
  omega

theorem nonsimple_conclusion [Finite G] (hyp : Asc03Hyp G z) (hns : ¬ IsSimpleGroup G) :
    ∃ (V : Subgroup G) (_ : V.Normal), IsElementaryAbelian 2 ↥V ∧ Nat.card ↥V = 8 ∧
      Nonempty (G ⧸ V ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := by
  classical
  have hE := extraspecialAt_ascQ hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial G := ⟨⟨z, 1, hE.ne_one⟩⟩
  obtain ⟨N, hN, hN1, hNtop⟩ : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
    by_contra h
    push Not at h
    exact hns (IsSimpleGroup.mk fun N hNn => by
      by_cases h1 : N = ⊥
      · exact Or.inl h1
      · exact Or.inr (h N hNn h1))
  have hzN : z ∈ N := z_mem_of_normal hyp hN hN1
  obtain ⟨g, hgz, q0, hq0P, hq0⟩ := hyp.not_weakly_closed
  have hsQ : g * z * g⁻¹ ∈ ascQ z := by
    rw [← hq0]; exact (mem_ascQ_iff z _).2 ⟨q0.2, hq0P⟩
  have hsN : g * z * g⁻¹ ∈ N := hN.conj_mem z hzN g
  have hsH : g * z * g⁻¹ ∈ ascH z := ascQ_le_ascH z hsQ
  have hs1 : g * z * g⁻¹ ≠ 1 := asc_conj_ne_one hyp g
  have hs2 : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := asc_conj_sq hyp g
  have hback : ∀ x : G, x * (g * z * g⁻¹) = (g * z * g⁻¹) * x → g⁻¹ * x * g ∈ ascH z := by
    intro x hx
    rw [ascH, Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [hx]
      _ = z * (g⁻¹ * x * g) := by group
  have hgN : ∀ x ∈ N, g⁻¹ * x * g ∈ N := fun x hx => by simpa using hN.conj_mem x hx g⁻¹
  obtain ⟨P, hQP, hPH, hP64, hNP⟩ := exists_sylow_le hyp
  by_cases h3 : ∃ y ∈ N, y ∈ ascH z ∧ orderOf y = 3
  ·
    exfalso
    obtain ⟨y, hyN, hyH, hy3⟩ := h3
    have hQN : ascQ z ≤ N := by
      have hcomm : ∀ q ∈ ascQ z, q * y * q⁻¹ * y⁻¹ ∈ N ⊓ ascQ z := by
        intro q hq
        refine ⟨N.mul_mem (hN.conj_mem y hyN q) (N.inv_mem hyN), ?_⟩
        have : q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) := by group
        rw [this]
        exact (ascQ z).mul_mem hq (conj_mem_ascQ hyH ((ascQ z).inv_mem hq))
      have heq := eq_ascQ_of_comm hyp hyH hy3 (U := N ⊓ ascQ z) inf_le_right ⟨hzN, hE.mem⟩
        (fun u hu => ⟨hN.conj_mem u hu.1 y, conj_mem_ascQ hyH hu.2⟩) hcomm
      rw [← heq]; exact inf_le_left
    by_cases hHN : ascH z ≤ N
    ·
      apply hNtop
      have hF := Sylow.normalizer_sup_eq_top' P (hPH.trans hHN)
      rw [eq_top_iff, ← hF]
      exact sup_le (hNP.trans hHN) le_rfl
    ·
      have h2el : ∀ x ∈ N, x ∈ ascH z → (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ ascQ z := by
        set R := (N.subgroupOf (ascH z)).map (rho hyp) with hR
        have hyR : rho hyp ⟨y, hyH⟩ ∈ R :=
          Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hyN)
        have hy1 : rho hyp ⟨y, hyH⟩ ≠ 1 := by
          rw [Ne, rho_eq_one_iff]; exact not_mem_ascQ_of_order_three hyp hy3
        have hy3' : orderOf (rho hyp ⟨y, hyH⟩) = 3 := by
          refine orderOf_eq_prime ?_ hy1
          rw [← map_pow]
          have : (⟨y, hyH⟩ : ↥(ascH z)) ^ 3 = 1 := by
            apply Subtype.ext; simp [← hy3, pow_orderOf_eq_one]
          rw [this, map_one]
        have hS3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
          rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
        have hR3 : 3 ∣ Nat.card ↥R := by
          have := orderOf_dvd_natCard (⟨_, hyR⟩ : ↥R)
          rwa [Subgroup.orderOf_mk, hy3'] at this
        have hRne : Nat.card ↥R ≠ 6 := by
          intro h6
          apply hHN
          have hRtop : R = ⊤ := Subgroup.eq_top_of_card_eq R (by rw [h6, hS3])
          intro h hh
          have : rho hyp ⟨h, hh⟩ ∈ R := by rw [hRtop]; exact Subgroup.mem_top _
          obtain ⟨n, hn, hne⟩ := Subgroup.mem_map.1 this
          have hq : ((n⁻¹ * ⟨h, hh⟩ : ↥(ascH z)) : G) ∈ ascQ z := by
            rw [← rho_eq_one_iff hyp, map_mul, map_inv, hne, inv_mul_cancel]
          have : h = (n : G) * ((n⁻¹ * ⟨h, hh⟩ : ↥(ascH z)) : G) := by simp
          rw [this]
          exact N.mul_mem (Subgroup.mem_subgroupOf.1 hn) (hQN hq)
        have hRdvd : Nat.card ↥R ∣ 6 := by rw [← hS3]; exact Subgroup.card_subgroup_dvd_card R
        have hR3' : Nat.card ↥R = 3 := by
          have hd : Nat.divisors 6 = {1, 2, 3, 6} := by decide
          have hmem : Nat.card ↥R ∈ Nat.divisors 6 := Nat.mem_divisors.2 ⟨hRdvd, by norm_num⟩
          rw [hd] at hmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          omega
        intro x hxN hxH ⟨k, hk⟩
        have hxR : rho hyp ⟨x, hxH⟩ ∈ R :=
          Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hxN)
        have h1 : orderOf (rho hyp ⟨x, hxH⟩) ∣ 3 := by
          have := orderOf_dvd_natCard (⟨_, hxR⟩ : ↥R)
          rwa [Subgroup.orderOf_mk, hR3'] at this
        have h2 : orderOf (rho hyp ⟨x, hxH⟩) ∣ 2 ^ k := by
          apply orderOf_dvd_of_pow_eq_one
          rw [← map_pow]
          have : (⟨x, hxH⟩ : ↥(ascH z)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
          rw [this, map_one]
        have h3' : orderOf (rho hyp ⟨x, hxH⟩) = 1 := by
          have hc : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
          exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hc) h2
        rw [orderOf_eq_one_iff, rho_eq_one_iff] at h3'
        exact h3'
      apply false_of_cent_le_conj hyp hgz hsQ
      intro x hxQ hxs
      refine h2el _ (hgN x (hQN hxQ)) (hback x hxs) ?_
      obtain ⟨k, hk⟩ := isPGroup_ascQ hyp ⟨x, hxQ⟩
      refine ⟨k, ?_⟩
      have : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hc : (g⁻¹ * x * g⁻¹⁻¹) ^ 2 ^ k = g⁻¹ * x ^ 2 ^ k * g⁻¹⁻¹ := conj_pow
      rw [inv_inv] at hc
      rw [hc, this]; group
  ·
    push Not at h3
    set D := N ⊓ ascH z with hD
    have hDH : D ≤ ascH z := inf_le_right
    have hDn : ∀ h ∈ ascH z, ∀ d ∈ D, h * d * h⁻¹ ∈ D := fun h hh d hd =>
      ⟨hN.conj_mem d hd.1 h, (ascH z).mul_mem ((ascH z).mul_mem hh hd.2) ((ascH z).inv_mem hh)⟩
    have hDQ : D ≤ ascQ z :=
      le_ascQ_of_normal hDH hDn (isPGroup_of_not_three hyp hDH fun y hy => h3 y hy.1 hy.2)
    obtain ⟨y, hyH, hy3⟩ := exists_order_three hyp
    have hzD : z ∈ D := ⟨hzN, z_mem_ascH z⟩
    have hsD : g * z * g⁻¹ ∈ D := ⟨hsN, hsH⟩
    rcases card_of_inv hyp hyH hy3 hDQ hzD (fun u hu => hDn y hyH u hu) with h2 | h8 | h32
    ·
      exfalso
      have hzs : z * (g * z * g⁻¹) = (g * z * g⁻¹) * z := (hE.central _ hsQ).symm
      have hVle : fourGroup z (g * z * g⁻¹) hE.sq_eq hs2 hzs ≤ D := by
        intro x hx
        rcases mem_fourGroup.1 hx with rfl | rfl | rfl | rfl
        · exact D.one_mem
        · exact hzD
        · exact hsD
        · exact D.mul_mem hzD hsD
      have := Subgroup.card_le_of_le hVle
      rw [card_fourGroup hE.ne_one hs1 hgz, h2] at this
      omega
    rotate_left
    ·
      exfalso
      have hDeq : D = ascQ z := Subgroup.eq_of_le_of_card_ge hDQ (by rw [h32, card_ascQ hyp])
      apply false_of_cent_le_conj hyp hgz hsQ
      intro x hxQ hxs
      have hxD : x ∈ D := by rw [hDeq]; exact hxQ
      have : g⁻¹ * x * g ∈ D := ⟨hgN x hxD.1, hback x hxs⟩
      rw [hDeq] at this
      exact this
    obtain ⟨hLQ, hL8, hLe, hzL, hsL, -, -⟩ :=
      lineOf_facts hyp hyH hy3 hsQ hs2 hs1 hgz
    have hLD : lineOf z (g * z * g⁻¹) y ≤ D := by
      refine (Subgroup.closure_le _).2 ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hzD
      · exact hsD
      · exact hDn y hyH _ hsD
    have hDL : lineOf z (g * z * g⁻¹) y = D := Subgroup.eq_of_le_of_card_ge hLD (by rw [h8, hL8])
    have hDe : ∀ a ∈ D, ∀ b ∈ D, a * a = 1 ∧ a * b = b * a := by rw [← hDL]; exact hLe
    have hC := cent_le_of_E8 hyp hDQ h8 hDe hzD hDn
    have hgD : g ∈ normalizer (D : Set G) := by
      have hginv : g⁻¹ ∈ normalizer (D : Set G) := mem_normalizer_of_conj fun d hd => by
        rw [inv_inv]
        exact ⟨hgN d hd.1, hback d (hDe d hd _ hsD).2⟩
      simpa using inv_mem hginv
    set M := normalizer (D : Set G) with hM
    have hHM : ascH z ≤ M := fun h hh => mem_normalizer_of_conj (hDn h hh)
    have hgH : g ∉ ascH z := by
      intro h
      apply hgz
      have := Subgroup.mem_centralizer_singleton_iff.1 h
      calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [this]
        _ = z := by group
    have hMcard : Nat.card ↥M = 1344 := by
      have hdvd := card_normalizer_dvd h8 hDe hC
      have h192 : 192 ∣ Nat.card ↥M := by
        rw [← card_ascH' hyp]; exact Subgroup.card_dvd_of_le hHM
      have hne : Nat.card ↥M ≠ 192 := by
        intro h
        have : ascH z = M := Subgroup.eq_of_le_of_card_ge hHM (by rw [h, card_ascH' hyp])
        exact hgH (this ▸ hgD)
      obtain ⟨k, hk⟩ := h192
      obtain ⟨m, hm⟩ := hdvd
      rw [hk] at hm hne
      have hkm : k * m = 7 := by nlinarith
      have hk7 : k ∣ 7 := ⟨m, hkm.symm⟩
      have hd : Nat.divisors 7 = {1, 7} := by decide
      have hmem : k ∈ Nat.divisors 7 := Nat.mem_divisors.2 ⟨hk7, by norm_num⟩
      rw [hd] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rw [hk]
      omega
    obtain ⟨f⟩ := exists_coords8 h8 hDe
    set ρ := actGL f with hρ
    have hker : ρ.ker = D.subgroupOf M := by
      ext m
      rw [MonoidHom.mem_ker, hρ, actGL_eq_one_iff, Subgroup.mem_subgroupOf]
      constructor
      · exact hC m
      · intro hm d hd
        exact (hDe _ hm d hd).2
    have hsurj : Function.Surjective ρ := by
      have h1 := Subgroup.card_mul_index ρ.ker
      rw [Subgroup.index_ker, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.le_normalizer : D ≤ M)).toEquiv, h8, hMcard] at h1
      rw [← MonoidHom.range_eq_top]
      apply Subgroup.eq_top_of_card_eq
      rw [card_GL3_two]
      omega
    have hNMn : (N.subgroupOf M).Normal := Subgroup.Normal.subgroupOf hN M
    have hRn := hNMn.map ρ hsurj
    have hsimp := isSimpleGroup_GL3_two
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (G := GL (Fin 3) (ZMod 2))
      ((N.subgroupOf M).map ρ) with hbot | htop
    ·
      have hNM : ∀ x ∈ N, x ∈ M → x ∈ D := by
        intro x hxN hxM
        have hx : ρ ⟨x, hxM⟩ ∈ (N.subgroupOf M).map ρ :=
          Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hxN)
        rw [hbot, Subgroup.mem_bot] at hx
        have : (⟨x, hxM⟩ : ↥M) ∈ D.subgroupOf M := by rw [← hker]; exact hx
        exact Subgroup.mem_subgroupOf.1 this
      by_cases hND : N ≤ ascH z
      ·
        have hNeq : N = D := le_antisymm (le_inf le_rfl hND) inf_le_left
        have hDnorm : D.Normal := hNeq ▸ hN
        have hMtop : M = ⊤ := Subgroup.normalizer_eq_top D
        have hG : Nat.card G = 1344 := by
          rw [← hMcard, hMtop, Subgroup.card_top]
        have := hDnorm
        exact ⟨D, hDnorm, isElementaryAbelian_of hDe, h8, nonempty_quotient_equiv_GL3 h8 hDe hC hG⟩
      ·
        exfalso
        have hDN : D ≤ N := inf_le_left
        have hD'p : IsPGroup 2 ↥(D.subgroupOf N) :=
          IsPGroup.of_card (n := 3) (by
            rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv, h8]; norm_num)
        obtain ⟨P', hP'⟩ := hD'p.exists_le_sylow
        set P'' := (P' : Subgroup ↥N).map N.subtype with hP''
        have hP''p : IsPGroup 2 ↥P'' := P'.isPGroup'.map N.subtype
        have hDP'' : D ≤ P'' := by
          intro x hx
          exact ⟨⟨x, hDN hx⟩, hP' (Subgroup.mem_subgroupOf.2 hx), rfl⟩
        have hP''N : P'' ≤ N := Subgroup.map_subtype_le _
        have hDeq : D = P'' := by
          by_contra hne
          obtain ⟨x, hxP, hxD, hxN⟩ := exists_mem_normalizer_not_mem hP''p hDP'' hne
          exact hxD (hNM x (hP''N hxP) hxN)
        have hP'eq : (P' : Subgroup ↥N) = D.subgroupOf N := by
          ext x
          rw [Subgroup.mem_subgroupOf]
          constructor
          · intro hx; rw [hDeq]; exact ⟨x, hx, rfl⟩
          · intro hx; exact hP' (Subgroup.mem_subgroupOf.2 hx)
        have hP'card : Nat.card ↥(P' : Subgroup ↥N) = 8 := by
          rw [hP'eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv, h8]
        have hPnc : normalizer ((P' : Subgroup ↥N) : Set ↥N) ≤
            centralizer ((P' : Subgroup ↥N) : Set ↥N) := by
          intro n hn
          have hnM : (n : G) ∈ M := by
            refine mem_normalizer_of_conj fun d hd => ?_
            have h1 : (⟨d, hDN hd⟩ : ↥N) ∈ (P' : Subgroup ↥N) := by
              rw [hP'eq]; exact Subgroup.mem_subgroupOf.2 hd
            have h2 := (Subgroup.mem_normalizer_iff.1 hn _).1 h1
            rw [hP'eq, Subgroup.mem_subgroupOf] at h2
            exact h2
          have hnD : (n : G) ∈ D := hNM n n.2 hnM
          rw [Subgroup.mem_centralizer_iff]
          intro p hp
          have hp' : p ∈ (P' : Subgroup ↥N) := hp
          rw [hP'eq] at hp'
          exact Subtype.ext (hDe _ (Subgroup.mem_subgroupOf.1 hp') _ hnD).2
        set K := (MonoidHom.transferSylow P' hPnc).ker with hK
        have hcompl := MonoidHom.ker_transferSylow_isComplement' P' hPnc
        rw [← hK] at hcompl
        have hKcard := hcompl.card_mul_card
        rw [hP'card] at hKcard
        have hKodd : Odd (Nat.card ↥K) := by
          have h1 := Sylow.card_eq_multiplicity P'
          rw [hP'card] at h1
          have hNpos : Nat.card ↥N ≠ 0 := Nat.card_pos.ne'
          have hcop := Nat.coprime_ordCompl Nat.prime_two hNpos
          rw [← h1, ← hKcard, Nat.mul_div_cancel _ (by norm_num)] at hcop
          exact Nat.odd_iff.2 (by
            have := (Nat.coprime_comm.1 hcop)
            rcases Nat.even_or_odd (Nat.card ↥K) with he | ho
            · exfalso
              have h2 : 2 ∣ Nat.card ↥K := even_iff_two_dvd.1 he
              have := Nat.Coprime.eq_one_of_dvd (Nat.coprime_comm.1 this) h2
              omega
            · exact Nat.odd_iff.1 ho)
        have hKne : K ≠ ⊥ := by
          intro hbotK
          rw [hbotK, Subgroup.card_bot, one_mul] at hKcard
          apply hND
          have : D = N := Subgroup.eq_of_le_of_card_ge hDN (by rw [← hKcard, h8])
          rw [← this]; exact hDH
        set K' := K.map N.subtype with hK'
        have hK'odd : ∀ x ∈ N, Odd (orderOf x) → x ∈ K' := by
          intro x hxN hxo
          have h1 := orderOf_map_dvd (MonoidHom.transferSylow P' hPnc) ⟨x, hxN⟩
          have h2 : orderOf (MonoidHom.transferSylow P' hPnc ⟨x, hxN⟩) ∣ 8 := by
            rw [← hP'card]; exact orderOf_dvd_natCard _
          have h3 : orderOf (MonoidHom.transferSylow P' hPnc ⟨x, hxN⟩) = 1 := by
            have hx' : orderOf (⟨x, hxN⟩ : ↥N) = orderOf x := Subgroup.orderOf_mk _ _
            rw [hx'] at h1
            have h2c : Nat.Coprime 2 (orderOf x) :=
              (Nat.prime_two.coprime_iff_not_dvd).2 (by rw [Nat.two_dvd_ne_zero]; exact Nat.odd_iff.1 hxo)
            have hc : Nat.Coprime (orderOf x) 8 := by
              simpa using (Nat.Coprime.pow_left 3 h2c).symm
            exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hc) h2
          rw [orderOf_eq_one_iff] at h3
          exact ⟨⟨x, hxN⟩, h3, rfl⟩
        have hK'sub : ∀ x ∈ K', x ∈ N ∧ Odd (orderOf x) := by
          rintro _ ⟨k, hk, rfl⟩
          refine ⟨k.2, ?_⟩
          have : orderOf ((N.subtype : ↥N →* G) k) = orderOf k :=
            orderOf_injective N.subtype N.subtype_injective k
          rw [this]
          have h1 : orderOf k = orderOf (⟨k, hk⟩ : ↥K) := (Subgroup.orderOf_mk k hk).symm
          rw [h1]
          exact Odd.of_dvd_nat hKodd (orderOf_dvd_natCard _)
        have hK'n : K'.Normal := by
          refine ⟨fun x hx c => ?_⟩
          obtain ⟨hxN, hxo⟩ := hK'sub x hx
          apply hK'odd _ (hN.conj_mem x hxN c)
          have : orderOf (c * x * c⁻¹) = orderOf x :=
            orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
          rw [this]; exact hxo
        have hK'ne : K' ≠ ⊥ := by
          intro h
          apply hKne
          rw [eq_bot_iff]
          intro k hk
          have : (k : G) ∈ K' := ⟨k, hk, rfl⟩
          rw [h, Subgroup.mem_bot] at this
          exact (Subgroup.mem_bot).2 (Subtype.ext this)
        have hzK' := z_mem_of_normal hyp hK'n hK'ne
        obtain ⟨-, hzo⟩ := hK'sub z hzK'
        rw [hyp.orderTwo] at hzo
        exact (Nat.not_odd_iff_even.2 even_two) hzo
    ·
      exfalso
      have hMN : ∀ m ∈ M, m ∈ N := by
        intro m hm
        have hm' : ρ ⟨m, hm⟩ ∈ (N.subgroupOf M).map ρ := by rw [htop]; exact Subgroup.mem_top _
        obtain ⟨n, hn, hne⟩ := Subgroup.mem_map.1 hm'
        have hk : n⁻¹ * ⟨m, hm⟩ ∈ ρ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hne, inv_mul_cancel]
        rw [hker, Subgroup.mem_subgroupOf] at hk
        have : m = (n : G) * ((n⁻¹ * ⟨m, hm⟩ : ↥M) : G) := by simp
        rw [this]
        exact N.mul_mem (Subgroup.mem_subgroupOf.1 hn) hk.1
      have : ascH z ≤ D := fun h hh => ⟨hMN h (hHM hh), hh⟩
      have := Subgroup.card_le_of_le this
      rw [card_ascH' hyp, h8] at this
      omega

end CFSG.GH74.M12.Thm1
