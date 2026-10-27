module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.Uniqueness.SU.SU13TB3Card

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] [Finite G] {z : G}

theorem W_inf_centralizer_leF (e : Elts G z) (f : FPart z e) :
    oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({z} : Set G) ≤ zpowers e.s₁ := by
  intro x hx
  obtain ⟨hxW, hxz⟩ := mem_inf.mp hx
  have hxX : x ∈ centralizer ({e.s₁} : Set G) := oc_le _ hxW
  have hxXH : x ∈ centralizer ({e.s₁} : Set G) ⊓ centralizer ({z} : Set G) := mem_inf.mpr ⟨hxX, hxz⟩
  rw [f.cent] at hxXH
  obtain ⟨p, hp, a, ha, rfl⟩ := SU1.mem_sup_of_commute (A := zpowers e.s₁) (B := f.F)
    (fun p hp a ha => zpowers_comm_of_mem_centralizer
      (mem_centralizer_singleton_iff.mpr (f.F_s₁ a ha)) hp) hxXH
  have hpW : p ∈ oc (centralizer ({e.s₁} : Set G)) := by
    refine le_oc_of_normal_odd ?_ ?_ ?_ hp
    · exact (zpowers_le).mpr (mem_centralizer_singleton_iff.mpr rfl)
    · intro g hg n hn
      have := zpowers_comm_of_mem_centralizer hg hn
      rw [← this]; simpa using hn
    · rw [Nat.card_zpowers, e.s₁_ord]; decide
  have haW : a ∈ oc (centralizer ({e.s₁} : Set G)) := by
    have := (oc (centralizer ({e.s₁} : Set G))).mul_mem (inv_mem hpW) hxW
    simpa using this
  have hN : (oc (centralizer ({e.s₁} : Set G)) ⊓ f.F) = ⊥ := by
    refine f.F_noOdd _ inf_le_right ?_ ?_
    · intro g hg n hn
      obtain ⟨hnW, hnF⟩ := mem_inf.mp hn
      have hgX : g ∈ centralizer ({e.s₁} : Set G) := mem_centralizer_singleton_iff.mpr (f.F_s₁ g hg)
      exact mem_inf.mpr ⟨conj_mem_oc hgX hnW, f.F.mul_mem (f.F.mul_mem hg hnF) (f.F.inv_mem hg)⟩
    · exact Odd.of_dvd_nat (odd_card_oc _) (Subgroup.card_dvd_of_le inf_le_left)
  have ha1 : a = 1 := by
    have : a ∈ oc (centralizer ({e.s₁} : Set G)) ⊓ f.F := mem_inf.mpr ⟨haW, ha⟩
    rw [hN] at this
    exact mem_bot.mp this
  rw [ha1, mul_one]
  exact hp

omit [Finite G] in
theorem z_mem_centralizerF (e : Elts G z) (f : FPart z e) :
    z ∈ centralizer ({e.s₁} : Set G) := mem_centralizer_singleton_iff.mpr (f.F_s₁ z f.z_mem)

theorem z_inv_modF (hz : orderOf z = 2) (e : Elts G z) (f : FPart z e) {w : G}
    (hw : w ∈ oc (centralizer ({e.s₁} : Set G))) :
    ∃ c ∈ zpowers e.s₁, z * w * z⁻¹ = c * c * w⁻¹ := by
  have hzX := z_mem_centralizerF e f
  have hzN : z ∈ normalizer ((oc (centralizer ({e.s₁} : Set G)) : Subgroup G) : Set G) :=
    le_normalizer_oc _ hzX
  obtain ⟨hbij, -⟩ := CFSG.OddInversion.odd_involution_product_decomposition
    (odd_card_oc (centralizer ({e.s₁} : Set G))) hz hzN
  obtain ⟨⟨c, j⟩, ⟨hc, hj⟩, hcj⟩ := hbij.surjOn hw
  obtain ⟨hcW, hcz⟩ := mem_inf.mp hc
  have hcP : c ∈ zpowers e.s₁ := W_inf_centralizer_leF e f (mem_inf.mpr ⟨hcW, hcz⟩)
  have hjW := hj.1
  have hjz : z * j * z⁻¹ = j⁻¹ := hj.2
  have hczz : c * z = z * c := mem_centralizer_singleton_iff.mp hcz
  have hcomm : c * j = j * c := zpowers_comm_of_mem_centralizer (oc_le _ hjW) hcP
  have hcomm' : c * j⁻¹ = j⁻¹ * c := (Commute.inv_right (show Commute c j from hcomm)).eq
  refine ⟨c, hcP, ?_⟩
  have hcjw : c * j = w := hcj
  rw [← hcjw]
  calc z * (c * j) * z⁻¹ = (z * c * z⁻¹) * (z * j * z⁻¹) := by group
    _ = c * j⁻¹ := by rw [hjz, show z * c * z⁻¹ = c by rw [← hczz]; group]
    _ = c * (j⁻¹ * c) * c⁻¹ := by group
    _ = c * (c * j⁻¹) * c⁻¹ := by rw [hcomm']
    _ = c * c * (c * j)⁻¹ := by rw [mul_inv_rev]; group

theorem comm_mem_PF (hz : orderOf z = 2) (e : Elts G z) (f : FPart z e) {w w' : G}
    (hw : w ∈ oc (centralizer ({e.s₁} : Set G))) (hw' : w' ∈ oc (centralizer ({e.s₁} : Set G))) :
    w * w' * w⁻¹ * w'⁻¹ ∈ zpowers e.s₁ := by
  set W := oc (centralizer ({e.s₁} : Set G)) with hW
  have key : ∀ {w w' : G}, w ∈ W → w' ∈ W → w⁻¹ * w'⁻¹ * w * w' ∈ zpowers e.s₁ := by
    intro w w' hw hw'
    obtain ⟨c, hc, h1⟩ := z_inv_modF hz e f hw
    obtain ⟨c', hc', h2⟩ := z_inv_modF hz e f hw'
    obtain ⟨c'', hc'', h3⟩ := z_inv_modF hz e f (W.mul_mem hw hw')
    have hwX : w⁻¹ ∈ centralizer ({e.s₁} : Set G) := (centralizer ({e.s₁} : Set G)).inv_mem (oc_le _ hw)
    have hc'w : Commute c' w⁻¹ := zpowers_comm_of_mem_centralizer hwX hc'
    have heq : c * c * (c' * c') * (w⁻¹ * w'⁻¹) = c'' * c'' * (w'⁻¹ * w⁻¹) := by
      have e1 : z * (w * w') * z⁻¹ = (z * w * z⁻¹) * (z * w' * z⁻¹) := by group
      rw [h3, h1, h2] at e1
      calc c * c * (c' * c') * (w⁻¹ * w'⁻¹) = c * c * ((c' * c') * w⁻¹) * w'⁻¹ := by group
        _ = c * c * (w⁻¹ * (c' * c')) * w'⁻¹ := by rw [(hc'w.mul_left hc'w).eq]
        _ = c * c * w⁻¹ * (c' * c' * w'⁻¹) := by group
        _ = c'' * c'' * (w * w')⁻¹ := e1.symm
        _ = c'' * c'' * (w'⁻¹ * w⁻¹) := by rw [mul_inv_rev]
    have hq : w⁻¹ * w'⁻¹ = (c * c * (c' * c'))⁻¹ * (c'' * c'') * (w'⁻¹ * w⁻¹) := by
      rw [mul_assoc, ← heq]; group
    have hqP : (c * c * (c' * c'))⁻¹ * (c'' * c'') ∈ zpowers e.s₁ :=
      (zpowers e.s₁).mul_mem ((zpowers e.s₁).inv_mem
        ((zpowers e.s₁).mul_mem ((zpowers e.s₁).mul_mem hc hc) ((zpowers e.s₁).mul_mem hc' hc')))
        ((zpowers e.s₁).mul_mem hc'' hc'')
    have hfin : w⁻¹ * w'⁻¹ * w * w' = (c * c * (c' * c'))⁻¹ * (c'' * c'') := by
      calc w⁻¹ * w'⁻¹ * w * w' = ((c * c * (c' * c'))⁻¹ * (c'' * c'') * (w'⁻¹ * w⁻¹)) * w * w' := by
            rw [← hq]
        _ = (c * c * (c' * c'))⁻¹ * (c'' * c'') := by group
    rw [hfin]; exact hqP
  have := key (W.inv_mem hw) (W.inv_mem hw')
  simpa using this

theorem card_WF (hz : orderOf z = 2) (e : Elts G z) (f : FPart z e) :
    Nat.card (oc (centralizer ({e.s₁} : Set G))) =
      3 * Nat.card (oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({e.t} : Set G) : Subgroup G) *
        Nat.card (oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({e.t * z} : Set G) : Subgroup G) := by
  set X := centralizer ({e.s₁} : Set G) with hX
  set W := oc X with hW
  have hz1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hz; exact absurd hz (by norm_num)
  have ht1 : e.t ≠ 1 := by
    intro h; have := e.t_ord; rw [h, orderOf_one] at this; exact absurd this (by norm_num)
  have ht_sq : e.t * e.t = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two e.t_ord
  have hz_sq : z * z = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two hz
  have hcomm : Commute e.t z := e.t_comm
  let T : Subgroup G := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions e.t z ht_sq hz_sq hcomm
  have hTk : IsKleinFour T :=
    CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions e.t z ht_sq hz_sq ht1 hz1
      e.t_ne hcomm
  have hTmem : ∀ x ∈ T, x = e.t * z ∨ x = e.t ∨ x = z ∨ x = 1 := by
    intro x hx
    have : x ∈ ({e.t * z, e.t, z, 1} : Set G) := hx
    simpa using this
  have htT : e.t ∈ T := by
    show e.t ∈ ({e.t * z, e.t, z, 1} : Set G)
    simp
  have hzT : z ∈ T := by
    show z ∈ ({e.t * z, e.t, z, 1} : Set G)
    simp
  have hzN : z ∈ normalizer (W : Set G) := le_normalizer_oc X (z_mem_centralizerF e f)
  have htN : e.t ∈ normalizer (W : Set G) := t_mem_normalizer_oc e
  have hTn : T ≤ normalizer (W : Set G) := by
    intro x hx
    rcases hTmem x hx with rfl | rfl | rfl | rfl
    · exact mul_mem htN hzN
    · exact htN
    · exact hzN
    · exact one_mem _
  have hBW := CFSG.ABGLocalTools.card_mul_card_centralizer_four_sq (T := T) (K := W)
    (odd_card_oc X) hTn (a := e.t) (b := z) htT hzT ht1 hz1 e.t_ne
  have hPle : zpowers e.s₁ ≤ W := zpowers_le_oc e
  have hWz : W ⊓ centralizer ({z} : Set G) = zpowers e.s₁ := by
    refine le_antisymm (W_inf_centralizer_leF e f) (le_inf hPle ?_)
    refine (zpowers_le).mpr ?_
    exact mem_centralizer_singleton_iff.mpr e.s₁_comm
  have hWzcard : Nat.card (W ⊓ centralizer ({z} : Set G) : Subgroup G) = 3 := by
    rw [hWz, Nat.card_zpowers, e.s₁_ord]
  have hWT : W ⊓ centralizer (T : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxT⟩ := mem_inf.mp hx
    have hxz : x * z = z * x := (mem_centralizer_iff.mp hxT z hzT).symm
    have hxt : e.t * x = x * e.t := mem_centralizer_iff.mp hxT e.t htT
    have hxP : x ∈ zpowers e.s₁ := by
      rw [← hWz]
      exact mem_inf.mpr ⟨hxW, mem_centralizer_singleton_iff.mpr hxz⟩
    have hinv := conj_inv_of_mem_zpowers e.t_s₁ hxP
    have hx2 : x * x = 1 := by
      have h1 : e.t * x * e.t⁻¹ = x := by rw [hxt]; group
      have h2 : x = x⁻¹ := h1.symm.trans hinv
      calc x * x = x * x⁻¹ := by rw [← h2]
        _ = 1 := mul_inv_cancel x
    exact mem_bot.mpr (eq_one_of_mem_oc_of_sq (hPle hxP) hx2)
  have hWTcard : Nat.card (W ⊓ centralizer (T : Set G) : Subgroup G) = 1 := by
    rw [hWT]; exact Subgroup.card_bot
  rw [hWzcard, hWTcard] at hBW
  simp only [one_pow, mul_one] at hBW
  rw [hBW]
  ring

theorem inverted_by_zF (hz : orderOf z = 2) (e : Elts G z) (f : FPart z e) {u : G}
    (hus : u * e.s₁ * u⁻¹ = e.s₁⁻¹) (huz : u * z = z * u) {x : G}
    (hx : x ∈ oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({u} : Set G)) :
    z * x * z⁻¹ = x⁻¹ := by
  obtain ⟨hxW, hxu⟩ := mem_inf.mp hx
  have hxu' : x * u = u * x := mem_centralizer_singleton_iff.mp hxu
  obtain ⟨c, hc, h1⟩ := z_inv_modF hz e f hxW
  have hp : c * c ∈ zpowers e.s₁ := mul_mem hc hc
  have hpc : c * c = (z * x * z⁻¹) * x := by rw [h1]; group
  have hzu : Commute z u := huz.symm
  have hzxu : (z * x * z⁻¹) * u = u * (z * x * z⁻¹) := by
    calc z * x * z⁻¹ * u = z * x * (z⁻¹ * u) := by group
      _ = z * x * (u * z⁻¹) := by rw [(Commute.inv_left hzu).eq]
      _ = z * (x * u) * z⁻¹ := by group
      _ = z * (u * x) * z⁻¹ := by rw [hxu']
      _ = (z * u) * x * z⁻¹ := by group
      _ = (u * z) * x * z⁻¹ := by rw [hzu.eq]
      _ = u * (z * x * z⁻¹) := by group
  have hpu : u * (c * c) = (c * c) * u := by
    rw [hpc]
    calc u * (z * x * z⁻¹ * x) = (u * (z * x * z⁻¹)) * x := by group
      _ = (z * x * z⁻¹ * u) * x := by rw [hzxu]
      _ = z * x * z⁻¹ * (u * x) := by group
      _ = z * x * z⁻¹ * (x * u) := by rw [hxu']
      _ = (z * x * z⁻¹ * x) * u := by group
  have hinv := conj_inv_of_mem_zpowers hus hp
  have hp1 : (c * c) * (c * c) = 1 := by
    have h2 : u * (c * c) * u⁻¹ = c * c := by rw [hpu]; group
    have h3 : c * c = (c * c)⁻¹ := h2.symm.trans hinv
    calc c * c * (c * c) = c * c * (c * c)⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel _
  have hpW : c * c ∈ oc (centralizer ({e.s₁} : Set G)) := zpowers_le_oc e hp
  have := eq_one_of_mem_oc_of_sq hpW hp1
  rw [h1, this, one_mul]

omit [Finite G] in
theorem F_le_centralizerF (e : Elts G z) (f : FPart z e) {g : G} (hg : g ∈ f.F) :
    g ∈ centralizer ({e.s₁} : Set G) := mem_centralizer_singleton_iff.mpr (f.F_s₁ g hg)

theorem sup_invariantF (hz : orderOf z = 2) (e : Elts G z) (f : FPart z e) {p : ℕ} [Fact p.Prime]
    {V : Subgroup G} (hVW : V ≤ oc (centralizer ({e.s₁} : Set G))) (hVp : IsPGroup p V)
    (hVidx : ¬ p ∣ V.relIndex (oc (centralizer ({e.s₁} : Set G)))) :
    ∀ g ∈ f.F, ∀ u ∈ zpowers e.s₁ ⊔ V, g * u * g⁻¹ ∈ zpowers e.s₁ ⊔ V := by
  set W := oc (centralizer ({e.s₁} : Set G)) with hW
  intro g hg u hu
  have hgX := F_le_centralizerF e f hg
  obtain ⟨c, hc, v, hv, rfl⟩ := SU1.mem_sup_of_commute (A := zpowers e.s₁) (B := V)
    (fun a ha b hb => zpowers_comm_of_mem_centralizer (oc_le _ (hVW hb)) ha) hu
  have hKW : V.map (MulAut.conj g).toMonoidHom ≤ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_oc hgX (hVW hx)
  obtain ⟨w, hwW, hw⟩ := CFSG.GH74.GLS.Bg.Thompson.exists_conj_into_sylow (p := p) hKW
    (hVp.map _) hVW hVp hVidx
  have hv' := hw (g * v * g⁻¹) ⟨v, hv, by simp [MulAut.conj_apply]⟩
  set v' := w⁻¹ * (g * v * g⁻¹) * w with hv'def
  have hgv : g * v * g⁻¹ = (w * v' * w⁻¹ * v'⁻¹) * v' := by rw [hv'def]; group
  have hcomm := comm_mem_PF hz e f hwW (hVW hv')
  have hgc : g * c * g⁻¹ = c := by
    have := zpowers_comm_of_mem_centralizer hgX hc
    rw [← this]; group
  have heq : g * (c * v) * g⁻¹ = (c * (w * v' * w⁻¹ * v'⁻¹)) * v' := by
    calc g * (c * v) * g⁻¹ = (g * c * g⁻¹) * (g * v * g⁻¹) := by group
      _ = c * ((w * v' * w⁻¹ * v'⁻¹) * v') := by rw [hgc, hgv]
      _ = (c * (w * v' * w⁻¹ * v'⁻¹)) * v' := by group
  rw [heq]
  exact mul_mem (mem_sup_left (mul_mem hc hcomm)) (mem_sup_right hv')

theorem U_le_PF (hz : orderOf z = 2) (e : Elts G z) (f : FPart z e) {U : Subgroup G}
    (hUW : U ≤ oc (centralizer ({e.s₁} : Set G)))
    (hUinv : ∀ g ∈ f.F, ∀ u ∈ U, g * u * g⁻¹ ∈ U) {q : G} (hq : q ∈ f.F) (hq1 : q ≠ 1)
    (hqU : ∀ u ∈ U, q * u = u * q) : U ≤ zpowers e.s₁ := by
  set K : Subgroup G := f.F ⊓ centralizer (U : Set G) with hK
  have hqK : q ∈ K := mem_inf.mpr ⟨hq, mem_centralizer_iff.mpr fun u hu => (hqU u hu).symm⟩
  have hKne : K ≠ ⊥ := fun h => hq1 (mem_bot.mp (h ▸ hqK))
  have hnorm : ∀ g ∈ f.F, ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro g hg k hk
    obtain ⟨hkF, hkc⟩ := mem_inf.mp hk
    refine mem_inf.mpr ⟨f.F.mul_mem (f.F.mul_mem hg hkF) (f.F.inv_mem hg), mem_centralizer_iff.mpr ?_⟩
    intro u hu
    have hu' : g⁻¹ * u * g ∈ U := by
      have := hUinv g⁻¹ (f.F.inv_mem hg) u hu
      simpa using this
    have := mem_centralizer_iff.mp hkc _ hu'
    calc u * (g * k * g⁻¹) = g * ((g⁻¹ * u * g) * k) * g⁻¹ := by group
      _ = g * (k * (g⁻¹ * u * g)) * g⁻¹ := by rw [this]
      _ = g * k * g⁻¹ * u := by group
  have hzK : z ∈ K := f.F_socle K inf_le_left hnorm hKne
  have hzU : ∀ u ∈ U, u * z = z * u := fun u hu => mem_centralizer_iff.mp (mem_inf.mp hzK).2 u hu
  intro u hu
  obtain ⟨c, hc, h1⟩ := z_inv_modF hz e f (hUW hu)
  have h2 : z * u * z⁻¹ = u := by rw [← hzU u hu]; group
  have h3 : u * u = c * c := by
    have : u = c * c * u⁻¹ := by rw [← h1, h2]
    calc u * u = (c * c * u⁻¹) * u := by rw [← this]
      _ = c * c := by group
  have hodd : Odd (orderOf u) :=
    Odd.of_dvd_nat (odd_card_oc _) (Subgroup.orderOf_dvd_natCard _ (hUW hu))
  obtain ⟨m, hm⟩ := hodd
  have hu1 : u = (u * u) ^ (m + 1) := by
    have : (u * u) ^ (m + 1) = u := by
      rw [← pow_two, ← pow_mul, show 2 * (m + 1) = orderOf u + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    exact this.symm
  rw [hu1, h3]
  exact pow_mem (mul_mem hc hc) _

theorem orbit_stepF (hz : orderOf z = 2) (e : Elts G z) (f : FPart z e) {p q r m : ℕ}
    [Fact p.Prime] [Fact q.Prime] {U : Subgroup G} (hPU : zpowers e.s₁ ≤ U)
    (hUW : U ≤ oc (centralizer ({e.s₁} : Set G)))
    (hUinv : ∀ g ∈ f.F, ∀ u ∈ U, g * u * g⁻¹ ∈ U) {g : G} (hg : g ∈ f.F) (hgq : orderOf g = q)
    (hUcard : Nat.card U = r * p ^ m) (hr : r ∣ 3) (hqr : ¬ q ∣ r) (hqp : ¬ q ∣ p)
    (hord : ∀ k : ℕ, 0 < k → k ≤ m → ¬ q ∣ p ^ k - 1) : U ≤ zpowers e.s₁ := by
  have hgn : g ∈ normalizer (U : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hUinv g hg x, fun hx => ?_⟩
    have := hUinv g⁻¹ (f.F.inv_mem hg) _ hx
    simpa [mul_assoc] using this
  have h3 : 3 ∣ Nat.card (U ⊓ centralizer ({g} : Set G) : Subgroup G) := by
    have hle : zpowers e.s₁ ≤ U ⊓ centralizer ({g} : Set G) :=
      le_inf hPU ((zpowers_le).mpr (mem_centralizer_singleton_iff.mpr (f.F_s₁ g hg).symm))
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, e.s₁_ord] at this
  have hcen := le_centralizer_of_card hgq hgn hUcard hqr hqp (hr.trans h3) hord
  have hg1 : g ≠ 1 := by
    intro h; rw [h, orderOf_one] at hgq
    have := (Fact.out : q.Prime).one_lt
    omega
  exact U_le_PF hz e f hUW hUinv hg hg1
    (fun u hu => (mem_centralizer_singleton_iff.mp (hcen hu)).symm)

omit [Finite G] in
theorem dvd_315 {a : ℕ} (hodd : Odd a)
    (h : ∀ p k : ℕ, p.Prime → p ≠ 2 → p ^ k ∣ a → p ^ k ∣ 5 ∨ p ^ k ∣ 7 ∨ p ^ k ∣ 9) :
    a ∣ 315 := by
  refine (Nat.dvd_iff_prime_pow_dvd_dvd 315 a).mpr fun p k hp hpk => ?_
  by_cases hp2 : p = 2
  · subst hp2
    rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hk]; simp
    · exfalso
      have h2 : 2 ∣ a := (dvd_pow_self 2 hk.ne').trans hpk
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  · rcases h p k hp hp2 hpk with h5 | h7 | h9
    · exact h5.trans (by norm_num)
    · exact h7.trans (by norm_num)
    · exact h9.trans (by norm_num)

theorem sylow_bound9 (hKI7d : K.KI7d) (hH : K.IsTwoAlt ↥(centralizer ({z} : Set G)) 9)
    (hz : orderOf z = 2) (e : Elts G z) (f : FPart z e) {u : G} (hus : u * e.s₁ * u⁻¹ = e.s₁⁻¹)
    (huz : u * z = z * u) (hk : ∃ k : G, k * z * k⁻¹ = u) {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ^ k ∣ Nat.card (oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({u} : Set G) : Subgroup G)) :
    p ^ k ∣ 5 ∨ p ^ k ∣ 7 ∨ p ^ k ∣ 9 := by
  obtain ⟨kk, hkk⟩ := hk
  have hTwo : K.IsTwoAlt ↥(centralizer ({u} : Set G)) 9 := by
    have := isTwoAlt_centralizer_conj (k := kk) hH
    rw [hkk] at this
    exact this
  set A : Subgroup G := oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({u} : Set G) with hA
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Kp, hKp⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥A) p hdvd
  have hKA : Kp.map A.subtype ≤ centralizer ({u} : Set G) := by
    rintro _ ⟨y, -, rfl⟩
    exact (mem_inf.mp y.2).2
  set Y' : Subgroup ↥(centralizer ({u} : Set G)) := (Kp.map A.subtype).subgroupOf (centralizer ({u} : Set G))
    with hY'
  have hYcard : Nat.card Y' = p ^ k := by
    rw [hY', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv,
      Subgroup.card_map_of_injective A.subtype_injective, hKp]
  have hYp : IsPGroup p Y' := IsPGroup.of_card hYcard
  have hzu : z ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.mpr huz.symm
  let a : ↥(centralizer ({u} : Set G)) := ⟨z, hzu⟩
  have ha2 : orderOf a = 2 := by rw [← hz]; exact Subgroup.orderOf_mk z hzu
  have hinv : ∀ y ∈ Y', a * y * a⁻¹ = y⁻¹ := by
    intro y hy
    obtain ⟨y0, hy0, hy0e⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hy)
    apply Subtype.ext
    have hyA : (y : G) ∈ A := by rw [← hy0e]; exact y0.2
    show z * (y : G) * z⁻¹ = (y : G)⁻¹
    exact inverted_by_zF hz e f hus huz hyA
  have := hKI7d 9 (Or.inl rfl) ↥(centralizer ({u} : Set G)) hTwo a ha2 p hp hp2 Y' hYp hinv
  rw [hYcard] at this
  simpa using this

theorem W_dvd9 (hKI7d : K.KI7d) (hH : K.IsTwoAlt ↥(centralizer ({z} : Set G)) 9)
    (hz : orderOf z = 2) (e : Elts G z) (f : FPart z e) (l : Lem232 z e) :
    Nat.card (oc (centralizer ({e.s₁} : Set G))) ∣ 3 ^ 5 * 5 ^ 2 * 7 ^ 2 := by
  rw [card_WF hz e f]
  have hodd : ∀ u : G, Odd (Nat.card (oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({u} : Set G) : Subgroup G)) :=
    fun u => Odd.of_dvd_nat (odd_card_oc _) (Subgroup.card_dvd_of_le inf_le_left)
  obtain ⟨k₁, -, hk₁⟩ := l.k₁
  obtain ⟨k₂, -, hk₂⟩ := l.k₂
  have ha : Nat.card (oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({e.t} : Set G) : Subgroup G) ∣ 315 :=
    dvd_315 (hodd _) fun p k hp hp2 hpk =>
      sylow_bound9 hKI7d hH hz e f e.t_s₁ e.t_comm ⟨k₁, hk₁⟩ hp hp2 hpk
  have hb : Nat.card (oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({e.t * z} : Set G) : Subgroup G) ∣ 315 :=
    dvd_315 (hodd _) fun p k hp hp2 hpk =>
      sylow_bound9 hKI7d hH hz e f (tz_facts hz e).1 (tz_facts hz e).2 ⟨k₂, hk₂⟩ hp hp2 hpk
  calc 3 * Nat.card (oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({e.t} : Set G) : Subgroup G) *
        Nat.card (oc (centralizer ({e.s₁} : Set G)) ⊓ centralizer ({e.t * z} : Set G) : Subgroup G)
      ∣ 3 * 315 * 315 := mul_dvd_mul (mul_dvd_mul dvd_rfl ha) hb
    _ = 3 ^ 5 * 5 ^ 2 * 7 ^ 2 := by norm_num

end CFSG.GH74.Uniqueness.SU.SU13
