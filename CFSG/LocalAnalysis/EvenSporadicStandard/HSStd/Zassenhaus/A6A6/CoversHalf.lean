module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.CoversAux
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.Lift
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47FldLift

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

open Subgroup

theorem mem_centralizer_singleton_iff' {G : Type*} [Group G] {a g : G} :
    g ∈ Subgroup.centralizer ({a} : Set G) ↔ a * g = g * a := by
  simp [Subgroup.mem_centralizer_iff]

theorem exists_perfect_cover_centralizer {G : Type} [Group G] [Finite G] {N : Subgroup G}
    [N.Normal] (hN5 : ¬ 5 ∣ Nat.card N) {a : G} (ha5 : orderOf a = 5)
    {Y : Subgroup (G ⧸ N)} (hY : ⁅Y, Y⁆ = Y)
    (hYa : ∀ y ∈ Y, y * QuotientGroup.mk' N a = QuotientGroup.mk' N a * y) :
    ∃ D : Subgroup G, D.map (QuotientGroup.mk' N) = Y ∧ ⁅D, D⁆ = D ∧ ∀ x ∈ D, a * x = x * a := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 : a ^ (5 ^ 1) = 1 := by
    rw [pow_one, ← ha5]
    exact pow_orderOf_eq_one a
  let M : Subgroup G := Subgroup.centralizer ({a} : Set G) ⊓ Y.comap (QuotientGroup.mk' N)
  have hM : M.map (QuotientGroup.mk' N) = Y := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      have hcomm : QuotientGroup.mk' N g * QuotientGroup.mk' N a =
          QuotientGroup.mk' N a * QuotientGroup.mk' N g := hYa _ hy
      have hmem : g⁻¹ * (a * g * a⁻¹) ∈ N := by
        rw [← QuotientGroup.eq_one_iff]
        have e : (QuotientGroup.mk' N) (g⁻¹ * (a * g * a⁻¹)) = 1 := by
          simp only [map_mul, map_inv]
          change (QuotientGroup.mk' N g)⁻¹ *
            (QuotientGroup.mk' N a * QuotientGroup.mk' N g * (QuotientGroup.mk' N a)⁻¹) = 1
          rw [← hcomm]
          group
        exact e
      obtain ⟨n, hn, hcn⟩ := exists_mul_comm_of_coprime hN5 h5 hmem
      have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).2 hn
      refine ⟨g * n, ⟨mem_centralizer_singleton_iff'.2 hcn, ?_⟩, ?_⟩
      · change (QuotientGroup.mk' N) (g * n) ∈ Y
        rw [map_mul, hn1, mul_one]
        exact hy
      · change (QuotientGroup.mk' N) (g * n) = (QuotientGroup.mk' N) g
        rw [map_mul, hn1, mul_one]
  obtain ⟨D, hDM, hDp, hDY⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P47Fld.exists_perfect_cover (QuotientGroup.mk' N) hY hM
  exact ⟨D, hDY, hDp, fun x hx => mem_centralizer_singleton_iff'.1 (hDM hx).1⟩

theorem trivial_on_of_perfect {V : Type} [Group V] [Finite V] {G : Type} [Group G]
    {ρ : G →* MulAut V} {a : G} (ha5 : orderOf a = 5) {Ua Ub : Subgroup V}
    (hUb : Nat.card Ub = 16) (hinf : Ua ⊓ Ub = ⊥) (hfix : ∀ v : V, ρ a v = v ↔ v ∈ Ua)
    (hmem : ∀ g : G, a * g = g * a → ∀ v ∈ Ub, ρ g v ∈ Ub) {D : Subgroup G} [Finite D]
    (hD : ⁅D, D⁆ = D) (hDa : ∀ x ∈ D, a * x = x * a) : ∀ x ∈ D, ∀ u ∈ Ub, ρ x u = u := by
  have hcen : ∀ h : Subgroup.centralizer ({a} : Set G), ∀ u ∈ Ub,
      (ρ.comp (Subgroup.centralizer ({a} : Set G)).subtype) h u ∈ Ub :=
    fun h u hu => hmem h (mem_centralizer_singleton_iff'.1 h.2) u hu
  have hac : a ∈ Subgroup.centralizer ({a} : Set G) := mem_centralizer_singleton_iff'.2 rfl
  let ψc := restrictAut (ρ.comp (Subgroup.centralizer ({a} : Set G)).subtype) Ub hcen
  have ha5' : a ^ 5 = 1 := by
    rw [← ha5]
    exact pow_orderOf_eq_one a
  have hα5 : ψc ⟨a, hac⟩ ^ 5 = 1 := by
    rw [← map_pow]
    have : (⟨a, hac⟩ : Subgroup.centralizer ({a} : Set G)) ^ 5 = 1 := Subtype.ext (by simpa using ha5')
    rw [this, map_one]
  have hα1 : ψc ⟨a, hac⟩ ≠ 1 := by
    intro h
    have hUa : ∀ u ∈ Ub, ρ a u = u := fun u hu =>
      congrArg (fun f : MulAut Ub => ((f ⟨u, hu⟩ : Ub) : V)) h
    have hbot : Ub = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have : u ∈ Ua ⊓ Ub := ⟨(hfix u).1 (hUa u hu), hu⟩
      rwa [hinf] at this
    have := Subgroup.card_eq_one.2 hbot
    omega
  have hDcen : D ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff'.2 (hDa x hx)
  have hDtop : commutator D = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hD)
  have key := eq_one_of_perfect_of_comm hUb hα5 hα1 hDtop (ψc.comp (Subgroup.inclusion hDcen))
    (fun h => by
      change ψc ⟨a, hac⟩ * ψc (Subgroup.inclusion hDcen h) =
        ψc (Subgroup.inclusion hDcen h) * ψc ⟨a, hac⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hDa h h.2))
  intro x hx u hu
  exact congrArg (fun f : MulAut Ub => ((f ⟨u, hu⟩ : Ub) : V)) (key ⟨x, hx⟩)

theorem eq_one_of_fixed_of_dvd {V : Type} [Group V] [Finite V] {G : Type} [Group G]
    {ρ : G →* MulAut V} (hρ : Function.Injective ρ) {Ua Ub : Subgroup V}
    (hUa : Nat.card Ua = 16) (hdec : ∀ v : V, ∃ a ∈ Ua, ∃ b ∈ Ub, v = a * b)
    {D : Subgroup G} [Finite D] (h5 : 5 ∣ Nat.card D) (hDmem : ∀ x ∈ D, ∀ v ∈ Ua, ρ x v ∈ Ua)
    (hDtriv : ∀ x ∈ D, ∀ u ∈ Ub, ρ x u = u) :
    ∀ w ∈ Ua, (∀ x ∈ D, ρ x w = w) → w = 1 := by
  intro w hw hfixD
  by_contra hne
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hx5 : x ^ 5 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hxn : actOn ρ D Ua hDmem x ^ 5 = 1 := by rw [← map_pow, hx5, map_one]
  have hinj := actOn_injective hρ hdec hDmem hDtriv
  rcases card_fixSub_five_16 hUa hxn with h1 | h16
  · have hbot := Subgroup.card_eq_one.1 h1
    have hmem : (⟨w, hw⟩ : Ua) ∈ fixSub (actOn ρ D Ua hDmem x) := by
      rw [mem_fixSub]
      exact Subtype.ext (hfixD x x.2)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hne (congrArg Subtype.val hmem)
  · have h1 : actOn ρ D Ua hDmem x = 1 := eq_one_of_card_fixSub (by rw [h16, hUa])
    have hx1 : x = 1 := hinj (by rw [h1, map_one])
    rw [hx1, orderOf_one] at hx
    omega

theorem odd_dvd_fiftysix {k : ℕ} (hk : Odd k) (h : k ∣ 56) : k = 1 ∨ k = 7 := by
  have hle : k ≤ 56 := Nat.le_of_dvd (by norm_num) h
  revert hk h
  interval_cases k <;> decide

theorem inf_eq_bot_of_cover {V : Type} [Group V] (hc : ∀ x y : V, x * y = y * x)
    (hs : ∀ x : V, x * x = 1) (hV : Nat.card V = 256) {G : Type} [Group G] [Finite G]
    {ρ : G →* MulAut V} (hρ : Function.Injective ρ) {N : Subgroup G} [N.Normal]
    (hNodd : Odd (Nat.card N)) {Ua Ub : Subgroup V} (hUa : Nat.card Ua = 16)
    (hUb : Nat.card Ub = 16) (hinf : Ua ⊓ Ub = ⊥) {Y : Subgroup (G ⧸ N)}
    (hYc : Nat.card Y = 360) {D : Subgroup G} (hDY : D.map (QuotientGroup.mk' N) = Y)
    (hDmem : ∀ x ∈ D, ∀ v ∈ Ua, ρ x v ∈ Ua) (hDtriv : ∀ x ∈ D, ∀ u ∈ Ub, ρ x u = u) :
    D ⊓ N = ⊥ := by
  classical
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; norm_num)
  have hdec := exists_mul_of_card_sixteen hc hV hUa hUb hinf
  have hinj := actOn_injective hρ hdec hDmem hDtriv
  have hcUa : ∀ x y : Ua, x * y = y * x := fun x y => Subtype.ext (hc x y)
  have hsUa : ∀ x : Ua, x * x = 1 := fun x => Subtype.ext (hs x)
  have hdvdD : Nat.card D ∣ 20160 := by
    have := Subgroup.card_dvd_of_injective _ hinj
    rwa [card_mulAut_sixteen hcUa hsUa hUa] at this
  obtain ⟨k, hk⟩ : ∃ k, k = Nat.card ↥(D ⊓ N) := ⟨_, rfl⟩
  have hcard : Nat.card D = 360 * k := by
    have := card_eq_card_map_mul_card_inf (QuotientGroup.mk' N) D
    rwa [hDY, hYc, QuotientGroup.ker_mk', ← hk] at this
  have hkodd : Odd k := by
    rw [hk]
    exact Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le inf_le_right)
  have hk56 : k ∣ 56 := by
    rw [hcard] at hdvdD
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 360) (by simpa using hdvdD)
  have hfixnone := eq_one_of_fixed_of_dvd hρ hUa hdec (D := D)
    (by rw [hcard]; exact Dvd.dvd.mul_right (by norm_num) k) hDmem hDtriv
  rcases odd_dvd_fiftysix hkodd hk56 with h1 | h7
  · exact Subgroup.card_eq_one.1 (by rw [← hk, h1])
  · exfalso
    have hk7 : Nat.card ↥(D ⊓ N) = 7 := by rw [← hk, h7]
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨q', hq'⟩ := exists_prime_orderOf_dvd_card' 7 (hk7 ▸ dvd_rfl : 7 ∣ Nat.card ↥(D ⊓ N))
    have hqDN : (q' : G) ∈ D ⊓ N := q'.2
    have hqD : (q' : G) ∈ D := hqDN.1
    have hq7 : orderOf (q' : G) = 7 := by rw [Subgroup.orderOf_coe, hq']
    have hq77 : (q' : G) ^ 7 = 1 := by
      rw [← hq7]
      exact pow_orderOf_eq_one _
    have hz : zpowers (q' : G) = D ⊓ N :=
      Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hqDN) (by rw [Nat.card_zpowers, hq7, hk7])
    have hconj : ∀ x ∈ D, x⁻¹ * (q' : G) * x ∈ zpowers (q' : G) := by
      intro x hx
      rw [hz]
      refine ⟨D.mul_mem (D.mul_mem (D.inv_mem hx) hqD) hx, ?_⟩
      have := ‹N.Normal›.conj_mem (q' : G) hqDN.2 x⁻¹
      simpa using this
    have hα7 : actOn ρ D Ua hDmem ⟨q', hqD⟩ ^ 7 = 1 := by
      rw [← map_pow]
      have : (⟨(q' : G), hqD⟩ : D) ^ 7 = 1 := Subtype.ext (by simpa using hq77)
      rw [this, map_one]
    rcases card_fixSub_seven_16 hUa hα7 with h2 | h16
    · obtain ⟨w₀, hw₀F, hw₀ne⟩ : ∃ w ∈ fixSub (actOn ρ D Ua hDmem ⟨q', hqD⟩), w ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have hbot : fixSub (actOn ρ D Ua hDmem ⟨q', hqD⟩) = ⊥ :=
          (Subgroup.eq_bot_iff_forall _).2 hcon
        have := Subgroup.card_eq_one.2 hbot
        omega
      obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff'
        (1 : ↥(fixSub (actOn ρ D Ua hDmem ⟨q', hqD⟩)))).1 h2
      have hw₀q : ρ q' (w₀ : V) = w₀ := congrArg Subtype.val (mem_fixSub.1 hw₀F)
      have hstab : (q' : G) ∈ vecStab ρ (w₀ : V) := hw₀q
      have hfix : ∀ x ∈ D, ρ x (w₀ : V) = w₀ := by
        intro x hx
        have hxq : x⁻¹ * (q' : G) * x ∈ vecStab ρ (w₀ : V) :=
          zpowers_le.2 hstab (hconj x hx)
        have hq_x : ρ q' (ρ x (w₀ : V)) = ρ x (w₀ : V) := by
          have e : (q' : G) * x = x * (x⁻¹ * (q' : G) * x) := by group
          calc ρ q' (ρ x (w₀ : V)) = ρ ((q' : G) * x) (w₀ : V) := by
                rw [map_mul, MulAut.mul_apply]
            _ = ρ (x * (x⁻¹ * (q' : G) * x)) (w₀ : V) := by rw [← e]
            _ = ρ x (ρ (x⁻¹ * (q' : G) * x) (w₀ : V)) := by
                rw [map_mul, MulAut.mul_apply]
            _ = ρ x (w₀ : V) := by rw [mem_vecStab.1 hxq]
        have hzF : actOn ρ D Ua hDmem ⟨x, hx⟩ w₀ ∈ fixSub (actOn ρ D Ua hDmem ⟨q', hqD⟩) := by
          rw [mem_fixSub]
          exact Subtype.ext hq_x
        have hz1 : actOn ρ D Ua hDmem ⟨x, hx⟩ w₀ ≠ 1 := fun h =>
          hw₀ne ((MulEquiv.map_eq_one_iff _).1 h)
        have hne1 : (⟨_, hzF⟩ : ↥(fixSub (actOn ρ D Ua hDmem ⟨q', hqD⟩))) ≠ 1 := fun h =>
          hz1 (congrArg Subtype.val h)
        have hne2 : (⟨w₀, hw₀F⟩ : ↥(fixSub (actOn ρ D Ua hDmem ⟨q', hqD⟩))) ≠ 1 := fun h =>
          hw₀ne (congrArg Subtype.val h)
        have heq := (huniq _ hne1).trans (huniq _ hne2).symm
        exact congrArg (fun t : ↥(fixSub (actOn ρ D Ua hDmem ⟨q', hqD⟩)) => ((t : Ua) : V)) heq
      exact hw₀ne (Subtype.ext (hfixnone w₀.1 w₀.2 hfix))
    · have h1 : actOn ρ D Ua hDmem ⟨q', hqD⟩ = 1 := eq_one_of_card_fixSub (by rw [h16, hUa])
      have hq1 : (⟨(q' : G), hqD⟩ : D) = 1 := hinj (by rw [h1, map_one])
      have : (q' : G) = 1 := congrArg Subtype.val hq1
      rw [this, orderOf_one] at hq7
      omega


theorem exists_cover_half {V : Type} [Group V] (hc : ∀ x y : V, x * y = y * x)
    (hs : ∀ x : V, x * x = 1) (hV : Nat.card V = 256) {G : Type} [Group G] [Finite G]
    (ρ : G →* MulAut V) (hρ : Function.Injective ρ) {N : Subgroup G} [N.Normal]
    (hNodd : Odd (Nat.card N)) (hN5 : ¬ 5 ∣ Nat.card N) {a : G} (ha5 : orderOf a = 5)
    {Ua Ub : Subgroup V} (hUa : Nat.card Ua = 16) (hUb : Nat.card Ub = 16)
    (hinf : Ua ⊓ Ub = ⊥) (hfix : ∀ v : V, ρ a v = v ↔ v ∈ Ua)
    (hmem : ∀ g : G, a * g = g * a → ∀ v ∈ Ub, ρ g v ∈ Ub) {Y : Subgroup (G ⧸ N)}
    (hY : ⁅Y, Y⁆ = Y) (hYc : Nat.card Y = 360)
    (hYa : ∀ y ∈ Y, y * QuotientGroup.mk' N a = QuotientGroup.mk' N a * y) :
    ∃ D : Subgroup G, D.map (QuotientGroup.mk' N) = Y ∧ D ⊓ N = ⊥ ∧
      (∀ x ∈ D, ∀ u ∈ Ub, ρ x u = u) ∧ (∀ x ∈ D, ∀ v ∈ Ua, ρ x v ∈ Ua) ∧
      (∀ v, (∀ x ∈ D, ρ x v = v) ↔ v ∈ Ub) := by
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; norm_num)
  obtain ⟨D, hDY, hDp, hDa⟩ := exists_perfect_cover_centralizer hN5 ha5 hY hYa
  have htriv := trivial_on_of_perfect ha5 hUb hinf hfix hmem hDp hDa
  have hmema : ∀ x ∈ D, ∀ v ∈ Ua, ρ x v ∈ Ua := by
    intro x hx v hv
    rw [← hfix] at hv ⊢
    rw [← MulAut.mul_apply, ← map_mul, hDa x hx, map_mul, MulAut.mul_apply, hv]
  have hInf := inf_eq_bot_of_cover hc hs hV hρ hNodd hUa hUb hinf hYc hDY hmema htriv
  have hdec := exists_mul_of_card_sixteen hc hV hUa hUb hinf
  have hcardD : Nat.card D = 360 := by
    have := card_eq_card_map_mul_card_inf (QuotientGroup.mk' N) D
    rw [hDY, hYc, QuotientGroup.ker_mk', hInf, Subgroup.card_bot, mul_one] at this
    exact this
  have hfixnone := eq_one_of_fixed_of_dvd hρ hUa hdec (D := D)
    (by rw [hcardD]; norm_num) hmema htriv
  refine ⟨D, hDY, hInf, htriv, hmema, fun v => ⟨fun h => ?_, fun hv x hx => htriv x hx v hv⟩⟩
  obtain ⟨u, hu, u', hu', rfl⟩ := hdec v
  have hu1 : u = 1 := by
    refine hfixnone u hu (fun x hx => ?_)
    have h1 := h x hx
    rw [map_mul, htriv x hx u' hu'] at h1
    exact mul_right_cancel h1
  rw [hu1, one_mul]
  exact hu'


end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6
