module

public import CFSG.GH74.GLS.Stage1.Thm6.M12Facts.Classes
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Group
public import CFSG.GH74.GLS.Bg.Local.Transfer1515

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec14

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec13
  CFSG.GH74.GLS.Stage1.Thm6.M12Facts

variable {G : Type*} [Group G] {x : G} {T V S : Subgroup G} {a b y : G}

theorem eq_top_of_cyclic_quotient (hs : IsSimpleGroup G) (hna : ∃ a b : G, a * b ≠ b * a)
    (N : Subgroup G) [N.Normal] (hN : IsCyclic (G ⧸ N)) : N = ⊤ := by
  rcases hs.eq_bot_or_eq_top_of_normal N with h | h
  · exfalso
    subst h
    have : IsCyclic G :=
      isCyclic_of_surjective (QuotientGroup.quotientBot (G := G)).toMonoidHom
        (QuotientGroup.quotientBot (G := G)).surjective
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
    obtain ⟨a, b, hab⟩ := hna
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
    exact hab (zpow_mul_comm g m n)
  · exact h

theorem commute_of_sq_commute {f u : G} {k : ℕ} (hf : f ^ 3 ^ k = 1) (hc : Commute (f ^ 2) u) :
    Commute f u := by
  obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  have : f = (f ^ 2) ^ (m + 1) := by
    rw [← pow_mul]
    have h1 : f ^ (2 * (m + 1)) = f ^ (3 ^ k) * f := by
      rw [← pow_succ]; congr 1; omega
    rw [h1, hf, one_mul]
  rw [this]
  exact hc.pow_left _

theorem sylow_S (o : Out13 G x T V S a b y) : IsPGroup 2 ↥S ∧ ¬ 2 ∣ S.index := by
  obtain ⟨_, hp, hidx⟩ := o.sylow
  exact ⟨hp, by simpa [Subgroup.relIndex_top_right] using hidx⟩

theorem x_not_conj_z [Finite G] (o : Out13 G x T V S a b y) (g : G) :
    g * (a ^ 2 * b ^ 2) * g⁻¹ ≠ x := by
  intro hg
  have h := o.data
  have hS2 := (sylow_S o).1
  have hSz : S ≤ centralizer ({a ^ 2 * b ^ 2} : Set G) := by
    intro s hs
    rw [mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact (z_central h hs).symm
  have hT : IsSylow2In T (centralizer ({x} : Set G)) := o.out12.T_sylow
  have hT' := Sec12.sylow2_conj hT g
  have hC : Sec12.Hconj g (centralizer ({x} : Set G)) =
      centralizer ({a ^ 2 * b ^ 2} : Set G) := by
    rw [Sec12.Hconj_centralizer]
    have : g⁻¹ * x * g = a ^ 2 * b ^ 2 := by rw [← hg]; group
    rw [this]
  rw [hC] at hT'
  obtain ⟨P, hP, hSP⟩ := Sec12.exists_sylow2_ge hS2 hSz
  have hcard := Sec12.sylow2_card_eq hT' hP
  have h1 : Nat.card ↥(Sec12.Hconj g T) = Nat.card ↥T := Sec12.Hconj_card g T
  have h2 : Nat.card ↥S ≤ Nat.card ↥P := Subgroup.card_le_of_le hSP
  have h3 := o.out12.T_card
  rw [h.card] at h2
  omega

theorem x_conj_yx [Finite G] (o : Out13 G x T V S a b y) : ∃ g : G, g * x * g⁻¹ = y * x := by
  have h := o.data
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS2, hSidx⟩ := sylow_S o
  have hxdef : x = nu a b y x xNF := by simp [nu, xNF]
  have hyx : y * x = nu a b y x xyNF := by simp [nu, xyNF]
  have hxQ : x ∉ nfSub h pQ1 closed_pQ1 := by
    intro hm
    obtain ⟨p, hp, hpx⟩ := hm
    have := nu_injective h (hpx.symm.trans hxdef)
    subst this
    exact not_pQ1_x hp
  have hcyc := exists_cyc_nfSub h closed_pQ1 yNF cyc_Q1
  have hres := CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) hS2 hSidx
    (conj_mem_nfSub h closed_pQ1 conj_pQ1) ⟨_, hcyc⟩ (x_mem h) hxQ
    (fun g k _ => by
      rw [pow_mul, x_sq h, one_pow, mul_one, inv_mul_cancel]
      exact one_mem _)
    (fun g hgS _ => by
      obtain ⟨r, hr⟩ := exists_nf h hgS
      by_cases hQr : pQ1 r
      · exact Or.inl (by rw [hr]; exact (nu_mem_nfSub h closed_pQ1 r).2 hQr)
      · refine Or.inr ?_
        have hr' := (cosets_Q1 xNF r not_pQ1_x).resolve_left hQr
        have : x⁻¹ * (g⁻¹ * x * g) = nu a b y x (nfMul (nfInv xNF) r) := by
          rw [hr, ← nu_mul h, ← nu_inv h, ← hxdef]
        rw [this]
        exact (nu_mem_nfSub h closed_pQ1 _).2 hr')
  rcases hres with ⟨N, hN, hcycN, _, hxN⟩ | ⟨g, hgQ, _, _⟩
  · exfalso
    have := hN
    have := eq_top_of_cyclic_quotient o.out12.simple o.out12.nonabelian N hcycN
    exact hxN (this ▸ Subgroup.mem_top x)
  · obtain ⟨p, hp, hpe⟩ := hgQ
    have hH0 : ¬ pH0 p := by
      intro hp0
      have := o.fusion g⁻¹
      rw [inv_inv, H0_eq h, hpe] at this
      exact this ((nu_mem_nfSub h closed_pH0 p).2 hp0)
    have hsq : nfMul p p = (0, 0, 0, 0) := by
      have h1 : nu a b y x p * nu a b y x p = 1 := by
        rw [← hpe]
        calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
          _ = 1 := by rw [h.hx]; group
      rw [nu_mul h] at h1
      exact nu_injective h (h1.trans nu_zero.symm)
    have key : ∀ k l : Fin 2, k = l → ¬ (k = 0 ∧ l = 0) → k = 1 ∧ l = 1 := by decide
    have hkl := key _ _ hp hH0
    obtain ⟨r, _, hrp⟩ := inv_class_xy p ⟨hsq, hkl.1, hkl.2⟩
    have hnup : nu a b y x p = nu a b y x r * (y * x) * (nu a b y x r)⁻¹ := by
      rw [← hrp, hyx, nu_inv h, ← nu_mul h, ← nu_mul h]
    refine ⟨(g * nu a b y x r)⁻¹, ?_⟩
    calc (g * nu a b y x r)⁻¹ * x * ((g * nu a b y x r)⁻¹)⁻¹
        = (nu a b y x r)⁻¹ * (g⁻¹ * x * g) * nu a b y x r := by group
      _ = (nu a b y x r)⁻¹ * nu a b y x p * nu a b y x r := by rw [hpe]
      _ = y * x := by rw [hnup]; group

theorem involutions_conj_x [Finite G] (o : Out13 G x T V S a b y) {v : G} (hv : v ∈ S) (hv2 : v * v = 1)
    (hvP : v ∉ nfSub o.data pQ0 closed_pQ0) : ∃ g : G, g * x * g⁻¹ = v := by
  have h := o.data
  obtain ⟨p, rfl⟩ := exists_nf h hv
  have hsq : nfMul p p = (0, 0, 0, 0) := by
    rw [nu_mul h] at hv2
    exact nu_injective h (hv2.trans nu_zero.symm)
  have hk : p.2.2.1 = 1 := by
    have hnot : ¬ pQ0 p := fun hp => hvP ((nu_mem_nfSub h closed_pQ0 p).2 hp)
    have key : ∀ k : Fin 2, ¬ k = 0 → k = 1 := by decide
    exact key _ hnot
  obtain ⟨c, hc⟩ := o.y_conj
  have hyx := x_conj_yx o
  rcases (show p.2.2.2 = 0 ∨ p.2.2.2 = 1 by
    have key : ∀ l : Fin 2, l = 0 ∨ l = 1 := by decide
    exact key _) with hl | hl
  · obtain ⟨r, _, hrp⟩ := inv_class_y p ⟨hsq, hk, hl⟩
    have hnup : nu a b y x p = nu a b y x r * y * (nu a b y x r)⁻¹ := by
      have hy : y = nu a b y x yNF := by simp [nu, yNF]
      rw [← hrp, nu_inv h, ← nu_mul h, ← nu_mul h, ← hy]
    refine ⟨nu a b y x r * c, ?_⟩
    calc nu a b y x r * c * x * (nu a b y x r * c)⁻¹
        = nu a b y x r * (c * x * c⁻¹) * (nu a b y x r)⁻¹ := by group
      _ = _ := by rw [← hc, hnup]
  · obtain ⟨r, _, hrp⟩ := inv_class_xy p ⟨hsq, hk, hl⟩
    obtain ⟨c', hc'⟩ := hyx
    have hyx' : y * x = nu a b y x xyNF := by simp [nu, xyNF]
    have hnup : nu a b y x p = nu a b y x r * (y * x) * (nu a b y x r)⁻¹ := by
      rw [← hrp, hyx', nu_inv h, ← nu_mul h, ← nu_mul h]
    refine ⟨nu a b y x r * c', ?_⟩
    calc nu a b y x r * c' * x * (nu a b y x r * c')⁻¹
        = nu a b y x r * (c' * x * c'⁻¹) * (nu a b y x r)⁻¹ := by group
      _ = _ := by rw [hc', hnup]

theorem conj_z_mem_P0 [Finite G] (o : Out13 G x T V S a b y) {g : G} (hg : g⁻¹ * (a ^ 2 * b ^ 2) * g ∈ S) :
    g⁻¹ * (a ^ 2 * b ^ 2) * g ∈ nfSub o.data pQ0 closed_pQ0 := by
  have h := o.data
  by_contra hnot
  have hsq : (g⁻¹ * (a ^ 2 * b ^ 2) * g) * (g⁻¹ * (a ^ 2 * b ^ 2) * g) = 1 := by
    calc _ = g⁻¹ * ((a ^ 2 * b ^ 2) * (a ^ 2 * b ^ 2)) * g := by group
      _ = 1 := by rw [z_sq h]; group
  obtain ⟨g', hg'⟩ := involutions_conj_x o hg hsq hnot
  apply x_not_conj_z o ((g * g')⁻¹)
  calc (g * g')⁻¹ * (a ^ 2 * b ^ 2) * ((g * g')⁻¹)⁻¹
      = g'⁻¹ * (g⁻¹ * (a ^ 2 * b ^ 2) * g) * g' := by group
    _ = x := by rw [← hg']; group

theorem conj_inj_aux {f u w : G} (e : f * u * f⁻¹ = f * w * f⁻¹) : u = w :=
  mul_left_cancel (mul_right_cancel e)

section Fusing

variable (o : Out13 G x T V S a b y)
include o

theorem mem_normalizer_H0 {s : G} (hs : s ∈ S) :
    s ∈ normalizer ((closure ({a, b} : Set G) : Subgroup G) : Set G) := by
  have h := o.data
  rw [Subgroup.mem_normalizer_iff]
  intro r
  rw [H0_eq h]
  constructor
  · exact fun hr => conj_mem_nfSub h closed_pH0 conj_pH0 s hs r hr
  · intro hr
    have := conj_mem_nfSub h closed_pH0 conj_pH0 s⁻¹ (S.inv_mem hs) _ hr
    have e : r = s⁻¹ * (s * r * s⁻¹) * s⁻¹⁻¹ := by group
    rw [e]
    exact this

theorem f_norm_U {f : G}
    (hf : f ∈ normalizer ((closure ({a, b} : Set G) : Subgroup G) : Set G)) {u : G}
    (hu : u ∈ nfSub o.data pU closed_pU) : f * u * f⁻¹ ∈ nfSub o.data pU closed_pU := by
  have h := o.data
  obtain ⟨p, hp, rfl⟩ := hu
  obtain ⟨q, hq, hqq⟩ := pU_square p hp
  have hnu : nu a b y x p = nu a b y x q * nu a b y x q := by rw [nu_mul h, hqq]
  have hqH : nu a b y x q ∈ closure ({a, b} : Set G) := by
    rw [H0_eq h]; exact (nu_mem_nfSub h closed_pH0 q).2 hq
  have h1 : f * nu a b y x q * f⁻¹ ∈ closure ({a, b} : Set G) :=
    (Subgroup.mem_normalizer_iff.1 hf _).1 hqH
  rw [H0_eq h] at h1
  obtain ⟨q', hq', hq'e⟩ := h1
  rw [hnu]
  have : f * (nu a b y x q * nu a b y x q) * f⁻¹ = nu a b y x (nfMul q' q') := by
    rw [← nu_mul h, ← hq'e]; group
  rw [this]
  exact (nu_mem_nfSub h closed_pU _).2 (pU_sq q' hq')

theorem f_moves_z {f : G} (hf3 : Is3Element f)
    (hf : f ∈ normalizer ((closure ({a, b} : Set G) : Subgroup G) : Set G)) {v : G}
    (hv : v ∈ nfSub o.data pU closed_pU) (hfv : f * v * f⁻¹ ≠ v) :
    f * (a ^ 2 * b ^ 2) * f⁻¹ ≠ a ^ 2 * b ^ 2 := by
  have h := o.data
  intro hz
  obtain ⟨k, hk⟩ := hf3
  have hZ : a ^ 2 * b ^ 2 = nu a b y x zNF := zG_eq
  have hA : nu a b y x (2, 0, 0, 0) ∈ nfSub h pU closed_pU :=
    (nu_mem_nfSub h closed_pU _).2 (by decide)
  have hB : nu a b y x (0, 2, 0, 0) ∈ nfSub h pU closed_pU :=
    (nu_mem_nfSub h closed_pU _).2 (by decide)
  have hZ' : nu a b y x zNF ∈ nfSub h pU closed_pU :=
    (nu_mem_nfSub h closed_pU _).2 (by decide)
  have hZA : nu a b y x zNF * nu a b y x (2, 0, 0, 0) = nu a b y x (0, 2, 0, 0) := by
    rw [nu_mul h]; congr 1
  have hZB : nu a b y x zNF * nu a b y x (0, 2, 0, 0) = nu a b y x (2, 0, 0, 0) := by
    rw [nu_mul h]; congr 1
  rw [hZ] at hz
  have hall : ∀ u ∈ nfSub h pU closed_pU, u = 1 ∨ u = nu a b y x zNF ∨
      u = nu a b y x (2, 0, 0, 0) ∨ u = nu a b y x (0, 2, 0, 0) := by
    rintro u ⟨p, hp, rfl⟩
    rcases pU_cases p hp with rfl | rfl | rfl | rfl
    · exact Or.inl nu_zero
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hne : ∀ p q : NF, p ≠ q → nu a b y x p ≠ nu a b y x q := fun p q hpq e =>
    hpq (nu_injective h e)
  have hA1 : nu a b y x (2, 0, 0, 0) ≠ 1 := by
    rw [← nu_zero (a := a) (b := b) (y := y) (x := x)]; exact hne _ _ (by decide)
  obtain ⟨hfA, hfAU⟩ : f * nu a b y x (2, 0, 0, 0) * f⁻¹ ∈ nfSub h pU closed_pU ∧ True :=
    ⟨f_norm_U o hf hA, trivial⟩
  rcases hall _ hfA with e | e | e | e
  · exact hA1 (conj_inj_aux (by rw [e]; group))
  · have : f * nu a b y x (2, 0, 0, 0) * f⁻¹ = f * nu a b y x zNF * f⁻¹ := by rw [e, hz]
    exact hne _ _ (by decide) (conj_inj_aux this)
  ·
    have hfB : f * nu a b y x (0, 2, 0, 0) * f⁻¹ = nu a b y x (0, 2, 0, 0) := by
      rw [← hZA]
      calc f * (nu a b y x zNF * nu a b y x (2, 0, 0, 0)) * f⁻¹
          = (f * nu a b y x zNF * f⁻¹) * (f * nu a b y x (2, 0, 0, 0) * f⁻¹) := by group
        _ = _ := by rw [hz, e]
    apply hfv
    rcases hall v hv with rfl | rfl | rfl | rfl
    · group
    · exact hz
    · exact e
    · exact hfB
  ·
    have hfB : f * nu a b y x (0, 2, 0, 0) * f⁻¹ = nu a b y x (2, 0, 0, 0) := by
      rw [← hZA]
      calc f * (nu a b y x zNF * nu a b y x (2, 0, 0, 0)) * f⁻¹
          = (f * nu a b y x zNF * f⁻¹) * (f * nu a b y x (2, 0, 0, 0) * f⁻¹) := by group
        _ = nu a b y x zNF * nu a b y x (0, 2, 0, 0) := by rw [hz, e]
        _ = _ := hZB
    have hsq : ∀ u ∈ nfSub h pU closed_pU, Commute (f ^ 2) u := by
      intro u hu
      have e2 : f * (f * u * f⁻¹) * f⁻¹ = u := by
        rcases hall u hu with rfl | rfl | rfl | rfl
        · group
        · rw [hz, hz]
        · rw [e, hfB]
        · rw [hfB, e]
      show f ^ 2 * u = u * f ^ 2
      rw [pow_two]
      calc f * f * u = (f * (f * u * f⁻¹) * f⁻¹) * (f * f) := by group
        _ = u * (f * f) := by rw [e2]
    apply hfv
    have hc := commute_of_sq_commute hk (hsq v hv)
    calc f * v * f⁻¹ = v * f * f⁻¹ := by rw [hc.eq]
      _ = v := by group

theorem exists_conj_U_to_z {f : G} (hf3 : Is3Element f)
    (hf : f ∈ normalizer ((closure ({a, b} : Set G) : Subgroup G) : Set G)) {v : G}
    (hv : v ∈ nfSub o.data pU closed_pU) (hfv : f * v * f⁻¹ ≠ v) {u : G}
    (hu : u ∈ nfSub o.data pU closed_pU) (hu1 : u ≠ 1) :
    ∃ n ∈ normalizer ((closure ({a, b} : Set G) : Subgroup G) : Set G),
      n * u * n⁻¹ = a ^ 2 * b ^ 2 := by
  have h := o.data
  have hmoves := f_moves_z o hf3 hf hv hfv
  have hZ : a ^ 2 * b ^ 2 = nu a b y x zNF := zG_eq
  have hZU : nu a b y x zNF ∈ nfSub h pU closed_pU :=
    (nu_mem_nfSub h closed_pU _).2 (by decide)
  have hyN := mem_normalizer_H0 o (y_mem h)
  have hfinvN : f⁻¹ ∈ normalizer ((closure ({a, b} : Set G) : Subgroup G) : Set G) :=
    Subgroup.inv_mem _ hf
  have hy' : nu a b y x yNF = y := by simp [nu, yNF]
  have swapA : y * nu a b y x (2, 0, 0, 0) * y⁻¹ = nu a b y x (0, 2, 0, 0) := by
    calc y * nu a b y x (2, 0, 0, 0) * y⁻¹
        = nu a b y x yNF * nu a b y x (2, 0, 0, 0) * (nu a b y x yNF)⁻¹ := by rw [hy']
      _ = nu a b y x (nfMul (nfMul yNF (2, 0, 0, 0)) (nfInv yNF)) := by
        rw [nu_inv h, nu_mul h, nu_mul h]
      _ = _ := by rw [U_swap_a]
  have swapB : y * nu a b y x (0, 2, 0, 0) * y⁻¹ = nu a b y x (2, 0, 0, 0) := by
    calc y * nu a b y x (0, 2, 0, 0) * y⁻¹
        = nu a b y x yNF * nu a b y x (0, 2, 0, 0) * (nu a b y x yNF)⁻¹ := by rw [hy']
      _ = nu a b y x (nfMul (nfMul yNF (0, 2, 0, 0)) (nfInv yNF)) := by
        rw [nu_inv h, nu_mul h, nu_mul h]
      _ = _ := by rw [U_swap_b]
  obtain ⟨pw, hpw, hwdef⟩ := f_norm_U o hf hZU
  have hwZ : f * nu a b y x zNF * f⁻¹ = nu a b y x pw := hwdef
  have hpwAB : pw = (2, 0, 0, 0) ∨ pw = (0, 2, 0, 0) := by
    rcases pU_cases pw hpw with rfl | rfl | h1 | h2
    · exfalso
      apply z_ne_one h
      have e : f * nu a b y x zNF * f⁻¹ = 1 := by rw [hwZ, nu_zero]
      rw [hZ]
      exact conj_inj_aux (f := f) (u := nu a b y x zNF) (w := 1) (by rw [e]; group)
    · exfalso
      apply hmoves
      rw [hZ]; exact hwZ
    · exact Or.inl h1
    · exact Or.inr h2
  obtain ⟨pu, hpu, rfl⟩ := hu
  rcases pU_cases pu hpu with rfl | rfl | rfl | rfl
  · exact absurd nu_zero hu1
  · exact ⟨1, one_mem _, by rw [hZ]; group⟩
  · rcases hpwAB with rfl | rfl
    · refine ⟨f⁻¹, hfinvN, ?_⟩
      calc f⁻¹ * nu a b y x (2, 0, 0, 0) * f⁻¹⁻¹
          = f⁻¹ * (f * nu a b y x zNF * f⁻¹) * f := by rw [hwZ]; simp
        _ = a ^ 2 * b ^ 2 := by rw [hZ]; group
    · refine ⟨f⁻¹ * y, Subgroup.mul_mem _ hfinvN hyN, ?_⟩
      calc f⁻¹ * y * nu a b y x (2, 0, 0, 0) * (f⁻¹ * y)⁻¹
          = f⁻¹ * (y * nu a b y x (2, 0, 0, 0) * y⁻¹) * f := by group
        _ = f⁻¹ * (f * nu a b y x zNF * f⁻¹) * f := by rw [swapA, hwZ]
        _ = a ^ 2 * b ^ 2 := by rw [hZ]; group
  · rcases hpwAB with rfl | rfl
    · refine ⟨f⁻¹ * y, Subgroup.mul_mem _ hfinvN hyN, ?_⟩
      calc f⁻¹ * y * nu a b y x (0, 2, 0, 0) * (f⁻¹ * y)⁻¹
          = f⁻¹ * (y * nu a b y x (0, 2, 0, 0) * y⁻¹) * f := by group
        _ = f⁻¹ * (f * nu a b y x zNF * f⁻¹) * f := by rw [swapB, hwZ]
        _ = a ^ 2 * b ^ 2 := by rw [hZ]; group
    · refine ⟨f⁻¹, hfinvN, ?_⟩
      calc f⁻¹ * nu a b y x (0, 2, 0, 0) * f⁻¹⁻¹
          = f⁻¹ * (f * nu a b y x zNF * f⁻¹) * f := by rw [hwZ]; simp
        _ = a ^ 2 * b ^ 2 := by rw [hZ]; group

theorem lemma14_2c [Finite G] {f : G} (hf3 : Is3Element f)
    (hf : f ∈ normalizer ((closure ({a, b} : Set G) : Subgroup G) : Set G)) {v : G}
    (hv : v ∈ nfSub o.data pU closed_pU) (hfv : f * v * f⁻¹ ≠ v) {c : G} (hc : c ∈ S)
    (hcz : c * c = a ^ 2 * b ^ 2) :
    ∃ g : G, g * (a ^ 2 * b ^ 2) * g⁻¹ = a ^ 2 * b ^ 2 ∧
      g * c * g⁻¹ ∈ closure ({a, b} : Set G) ∧
      (g * c * g⁻¹) * (g * c * g⁻¹) = a ^ 2 * b ^ 2 := by
  have h := o.data
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS2, hSidx⟩ := sylow_S o
  have hZ : a ^ 2 * b ^ 2 = nu a b y x zNF := zG_eq
  obtain ⟨p, rfl⟩ := exists_nf h hc
  have hsqp : nfMul p p = zNF := by
    rw [nu_mul h, hZ] at hcz
    exact nu_injective h hcz
  by_cases hQ : pQ0 p
  · have hH : pH0 p := pH0_of_sq_ne p hQ (by rw [hsqp]; decide)
    refine ⟨1, by group, ?_, by simpa using hcz⟩
    rw [one_mul, inv_one, mul_one, H0_eq h]
    exact (nu_mem_nfSub h closed_pH0 p).2 hH
  · have hcQ : nu a b y x p ∉ nfSub h pQ0 closed_pQ0 :=
      fun hm => hQ ((nu_mem_nfSub h closed_pQ0 p).1 hm)
    have hcyc := exists_cyc_nfSub h closed_pQ0 yNF cyc_Q0
    have hzpow : ∀ k : ℕ, (a ^ 2 * b ^ 2) ^ k = 1 ∨ (a ^ 2 * b ^ 2) ^ k = a ^ 2 * b ^ 2 := by
      intro k
      rw [pow_eq_pow_mod k (show (a ^ 2 * b ^ 2) ^ 2 = 1 by rw [pow_two]; exact z_sq h)]
      rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
      · simp [h0]
      · simp [h1]
    have hres := CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) hS2 hSidx
      (conj_mem_nfSub h closed_pQ0 conj_pQ0) ⟨_, hcyc⟩ (nu_mem h p) hcQ
      (fun g k hgS => by
        have e : (nu a b y x p) ^ (2 * k) = (a ^ 2 * b ^ 2) ^ k := by
          rw [pow_mul, pow_two, hcz]
        rw [e] at hgS ⊢
        rcases hzpow k with hz | hz
        · rw [hz]; simp
        · rw [hz] at hgS ⊢
          exact conj_z_mem_P0 o hgS)
      (fun g hgS _ => by
        obtain ⟨r, hr⟩ := exists_nf h hgS
        by_cases hQr : pQ0 r
        · exact Or.inl (by rw [hr]; exact (nu_mem_nfSub h closed_pQ0 r).2 hQr)
        · refine Or.inr ?_
          have hr' := (cosets_Q0 p r hQ).resolve_left hQr
          have : (nu a b y x p)⁻¹ * (g⁻¹ * nu a b y x p * g) =
              nu a b y x (nfMul (nfInv p) r) := by
            rw [hr, ← nu_mul h, ← nu_inv h]
          rw [this]
          exact (nu_mem_nfSub h closed_pQ0 _).2 hr')
    rcases hres with ⟨N, hN, hcycN, _, hcN⟩ | ⟨g, hgQ, _, _⟩
    · exfalso
      have := hN
      have := eq_top_of_cyclic_quotient o.out12.simple o.out12.nonabelian N hcycN
      exact hcN (this ▸ Subgroup.mem_top _)
    · obtain ⟨r, hr, hre⟩ := hgQ
      have hz1 : g⁻¹ * (a ^ 2 * b ^ 2) * g ≠ 1 := by
        intro e
        apply z_ne_one h
        have := congrArg (fun t => g * t * g⁻¹) e
        simpa [mul_assoc] using this
      have hsqr : nu a b y x r * nu a b y x r = g⁻¹ * (a ^ 2 * b ^ 2) * g := by
        rw [← hre, ← hcz]; group
      have hrne : nfMul r r ≠ (0, 0, 0, 0) := by
        intro e
        apply hz1
        rw [← hsqr, nu_mul h, e, nu_zero]
      have hrH : pH0 r := pH0_of_sq_ne r hr hrne
      have hz'U : g⁻¹ * (a ^ 2 * b ^ 2) * g ∈ nfSub h pU closed_pU := by
        rw [← hsqr, nu_mul h]
        exact (nu_mem_nfSub h closed_pU _).2 (pU_sq r hrH)
      obtain ⟨n, hnN, hn⟩ := exists_conj_U_to_z o hf3 hf hv hfv hz'U hz1
      have hrmem : nu a b y x r ∈ (closure ({a, b} : Set G) : Subgroup G) := by
        rw [H0_eq h]; exact (nu_mem_nfSub h closed_pH0 r).2 hrH
      refine ⟨n * g⁻¹, ?_, ?_, ?_⟩
      · calc n * g⁻¹ * (a ^ 2 * b ^ 2) * (n * g⁻¹)⁻¹
            = n * (g⁻¹ * (a ^ 2 * b ^ 2) * g) * n⁻¹ := by group
          _ = _ := hn
      · have : n * g⁻¹ * nu a b y x p * (n * g⁻¹)⁻¹ = n * nu a b y x r * n⁻¹ := by
          rw [← hre]; group
        rw [this]
        exact (Subgroup.mem_normalizer_iff.1 hnN _).1 hrmem
      · have : n * g⁻¹ * nu a b y x p * (n * g⁻¹)⁻¹ = n * nu a b y x r * n⁻¹ := by
          rw [← hre]; group
        rw [this]
        calc n * nu a b y x r * n⁻¹ * (n * nu a b y x r * n⁻¹)
            = n * (nu a b y x r * nu a b y x r) * n⁻¹ := by group
          _ = n * (g⁻¹ * (a ^ 2 * b ^ 2) * g) * n⁻¹ := by rw [hsqr]
          _ = _ := hn

end Fusing

end CFSG.GH74.GLS.Stage1.Thm6.Sec14
