module

public import CFSG.GH74.Generic.S3.NoOutCent
public import CFSG.GH74.Generic.S3.NoOutFix
public import CFSG.GH74.Generic.S3.NoOutAct

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.QuasithinUnique.Setup.X5 (normalizerAct normalizerAct_of_mem normalizerAct_apply_mk coe_conjOn conjOn
  mem_centralizer_of_normalizerAct_eq_one eq_one_of_involution_mem_odd)

section Inner

variable {G : Type} [Group G] [Finite G]

theorem inner_case_false {x : G} {K : Subgroup (CentralizerBar x)} (hset : S3Setup G x K)
    (honly : OnlyInvX x K) (hfus : NoFusionAt x K) {t : StatedLieTag} {p f : ℕ} {y : G} {Iw Iv : Subgroup G}
    (hnd : NbrData G t p f x y Iw Iv) (himg : imgBar x Iw = K)
    (H0 : IsComponent (S45.barSub (y * x) Iv)) {a e : G} (hax : a * x = x * a) (hex : e * x = x * e)
    (ha2 : a * a = 1) (he2 : e * e = 1) (hae : a * e = e * a) (hex_ne : e ≠ x) (he1 : e ≠ 1)
    (hconja : IsConj x a) (hane : a ≠ x) (hinn : ∃ m ∈ Iw, ∀ n ∈ Iw, e * n * e⁻¹ = m * n * m⁻¹)
    {O : Subgroup G} (hOodd : Odd (Nat.card O))
    (hOnorm : ∀ c ∈ centralizer ({e} : Set G), ∀ o ∈ O, c * o * c⁻¹ ∈ O)
    (hZ : ∀ h ∈ centralizer ({e} : Set G), h * a * h⁻¹ * a⁻¹ ∈ O) : False := by
  classical
  have hperf : Group.IsPerfect ↥Iw := hnd.Iw_quasisimple.1
  have hx2 := hnd.x_sq
  have haC : a ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hax
  have heC : e ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hex
  have haN : a ∈ normalizer (Iw : Set G) := hnd.comp_w.le_normalizer haC
  have heN : e ∈ normalizer (Iw : Set G) := hnd.comp_w.le_normalizer heC
  obtain ⟨m, hm, hact⟩ := hinn
  obtain ⟨a₂, ha₂M, c₂, hc₂I, ha₂2, hc₂2, hec⟩ := exists_split_of_inner hnd.odd_w he2 hm hact
  have hxIw : ∀ i ∈ Iw, i * x = x * i := fun i hi => mem_centralizer_singleton_iff.1 (hnd.Iw_le hi)
  have hc₂x : c₂ * x = x * c₂ := by
    have h1 : c₂ = a₂⁻¹ * e := by rw [hec]; group
    rw [h1]
    calc a₂⁻¹ * e * x = a₂⁻¹ * (e * x) := by rw [mul_assoc]
      _ = a₂⁻¹ * (x * e) := by rw [hex]
      _ = (a₂⁻¹ * x) * e := by rw [mul_assoc]
      _ = (x * a₂⁻¹) * e := by
          congr 1
          have := hxIw (a₂⁻¹) (Iw.inv_mem ha₂M)
          exact this
      _ = x * (a₂⁻¹ * e) := by rw [mul_assoc]
  have hc₂Cx : c₂ ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hc₂x
  have hc₂cases := hnd.involution_cent_Iw honly himg hc₂Cx hc₂I hc₂2
  by_cases ha₂1 : a₂ = 1
  ·
    rw [ha₂1, one_mul] at hec
    rcases hc₂cases with h | h
    · exact he1 (hec.trans h)
    · exact hex_ne (hec.trans h)
  · have ha₂mk : (QuotientGroup.mk ⟨a₂, ha₂M⟩ : ↥Iw ⧸ center ↥Iw) ≠ 1 := by
      intro h
      have hz : (⟨a₂, ha₂M⟩ : ↥Iw) ∈ center ↥Iw := (QuotientGroup.eq_one_iff _).1 h
      exact ha₂1 (congrArg Subtype.val (eq_one_of_involution_mem_odd (C := center ↥Iw) hnd.odd_w hz
        (Subtype.ext ha₂2)))
    obtain ⟨S, hS⟩ := hnd.exists_S_B4_at (w := ⟨a₂, ha₂M⟩) (Subtype.ext ha₂2) ha₂mk
    have hact_e : normalizerAct Iw ⟨e, heN⟩ =
        MulAut.conj (QuotientGroup.mk ⟨a₂, ha₂M⟩ : ↥Iw ⧸ center ↥Iw) := by
      have hN : a₂ * c₂ ∈ normalizer (Iw : Set G) := hec ▸ heN
      have := normalizerAct_mul_centralizer ha₂M hc₂I hN
      simpa [hec] using this
    obtain ⟨R, hRodd, hRnorm, hRfix⟩ := exists_R_of_zStar hnd.odd_w haN he2 heN hOodd hOnorm hZ
    have hSfix : ∀ s ∈ S, normalizerAct Iw ⟨e, heN⟩ s = s := by
      intro s hs
      rw [hact_e, MulAut.conj_apply]
      have := Subgroup.mem_centralizer_singleton_iff.1 (hS.le_centralizer hs)
      calc (QuotientGroup.mk (⟨a₂, ha₂M⟩ : ↥Iw) : ↥Iw ⧸ center ↥Iw) * s * (QuotientGroup.mk ⟨a₂, ha₂M⟩)⁻¹ =
          (s * (QuotientGroup.mk ⟨a₂, ha₂M⟩)) * (QuotientGroup.mk ⟨a₂, ha₂M⟩)⁻¹ := by rw [this]
        _ = s := by group
    have hza : a * a₂ = a₂ * a := by
      rcases hc₂cases with h | h
      · have : a₂ = e := by rw [hec, h, mul_one]
        rw [this]; exact hae
      · have : a₂ = e * x := by
          rw [hec, h, mul_assoc, hx2, mul_one]
        rw [this]
        calc a * (e * x) = (a * e) * x := by rw [mul_assoc]
          _ = (e * a) * x := by rw [hae]
          _ = e * (a * x) := by rw [mul_assoc]
          _ = e * (x * a) := by rw [hax]
          _ = (e * x) * a := by rw [mul_assoc]
    obtain ⟨m', hm', hact'⟩ := b4_inner (M := Iw) ha₂M ha₂mk ha₂2 hS haN ha2 hza R hRodd
      (fun s hs r hr => hRnorm s (hSfix s hs) r hr) (fun s hs => hRfix s (hSfix s hs))
    exact inner_false_of_isConj hset honly hfus hnd himg H0 hconja hane hax ⟨m', hm', hact'⟩

theorem noOuter_core {x : G} {K : Subgroup (CentralizerBar x)} (hset : S3Setup G x K)
    (honly : OnlyInvX x K) (hfus : NoFusionAt x K) (hLy : LyAt x K) {t : StatedLieTag} {p f : ℕ} {y : G}
    {Iw Iv : Subgroup G} (hnd : NbrData G t p f x y Iw Iv) (himg : imgBar x Iw = K)
    (H0 : IsComponent (S45.barSub (y * x) Iv)) {g : G} (hne : g * x * g⁻¹ ≠ x)
    (hcx : (g * x * g⁻¹) * x = x * (g * x * g⁻¹)) (hcy : (g * x * g⁻¹) * y = y * (g * x * g⁻¹))
    (hout : ¬ ∃ a ∈ Iw, ∀ m ∈ Iw, (g * x * g⁻¹) * m * (g * x * g⁻¹)⁻¹ = a * m * a⁻¹)
    {P : Subgroup G} (hPc : P ≤ centralizer ({g * x * g⁻¹} : Set G))
    (hPperf : ⁅P, P⁆ = P) (hyP : y ∈ P) : False := by
  classical
  have hx2 := hnd.x_sq
  have hy2 := hnd.y_sq
  have hy1 := hnd.y_ne_one
  have hxy : x * y = y * x := hnd.comm.symm
  have hperf : Group.IsPerfect ↥Iw := hnd.Iw_quasisimple.1
  have hxIw : ∀ i ∈ Iw, i * x = x * i := fun i hi => mem_centralizer_singleton_iff.1 (hnd.Iw_le hi)
  obtain ⟨a, ha⟩ : ∃ a : G, a = g⁻¹ * x * g := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : G, b = g⁻¹ * y * g := ⟨_, rfl⟩
  have ha2 : a * a = 1 := by
    rw [ha]
    calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [hx2]; group
  have hb2 : b * b = 1 := by
    rw [hb]
    calc g⁻¹ * y * g * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
      _ = 1 := by rw [hy2]; group
  have hax : a * x = x * a := by
    have h1 : g * x * g⁻¹ * x = x * (g * x * g⁻¹) := hcx
    rw [ha]
    calc g⁻¹ * x * g * x = g⁻¹ * (x * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * x) * g := by rw [h1]
      _ = x * (g⁻¹ * x * g) := by group
  have hbx : b * x = x * b := by
    have h1 : g * x * g⁻¹ * y = y * (g * x * g⁻¹) := hcy
    rw [hb]
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * y) * g := by rw [h1]
      _ = x * (g⁻¹ * y * g) := by group
  have hab : a * b = b * a := by
    rw [ha, hb]
    calc g⁻¹ * x * g * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by group
      _ = g⁻¹ * (y * x) * g := by rw [hxy]
      _ = g⁻¹ * y * g * (g⁻¹ * x * g) := by group
  have hane : a ≠ x := by
    intro h
    apply hne
    rw [ha] at h
    calc g * x * g⁻¹ = g * (g⁻¹ * x * g) * g⁻¹ := by rw [h]
      _ = x := by group
  have hconja : IsConj x a := isConj_iff.2 ⟨g⁻¹, by rw [ha]; simp⟩
  have hb_ne : b ≠ x := by
    intro h
    apply hout
    refine ⟨y, hnd.y_Iw, fun m hm => ?_⟩
    have h1 : g * x * g⁻¹ = y := by
      rw [hb] at h
      calc g * x * g⁻¹ = g * (g⁻¹ * y * g) * g⁻¹ := by rw [h]
        _ = y := by group
    rw [h1]
  have hb1 : b ≠ 1 := by
    intro h
    apply hy1
    rw [hb] at h
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  set P' : Subgroup G := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'
  have hbP' : b ∈ P' := ⟨y, hyP, by rw [hb]; simp⟩
  have hP'perf : ⁅P', P'⁆ = P' := by
    rw [hP', ← Subgroup.map_commutator, hPperf]
  have hP'C : P' ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : p * (g * x * g⁻¹) = (g * x * g⁻¹) * p := Subgroup.mem_centralizer_singleton_iff.1 (hPc hp)
    simp only [MulEquiv.coe_toMonoidHom]
    calc g⁻¹ * p * g⁻¹⁻¹ * x = g⁻¹ * (p * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * p) * g := by rw [h1]
      _ = x * (g⁻¹ * p * g⁻¹⁻¹) := by group
  have hP'N : P' ≤ normalizer (Iw : Set G) := fun j hj => hnd.comp_w.le_normalizer (hP'C hj)
  have hPI : PerfectInInn (↥Iw ⧸ center ↥Iw) := perfectInInn_of_lieModel hnd.tag hnd.prime.2.2 hnd.model_w
  have hP'IsPerf : Group.IsPerfect ↥P' := Subgroup.isPerfect_iff.mpr hP'perf
  obtain ⟨m, hmI, hmc⟩ := exists_mul_centralizer_of_perfect Iw hPI hP'N hP'IsPerf b hbP'
  have hinn : ∃ m ∈ Iw, ∀ n ∈ Iw, b * n * b⁻¹ = m * n * m⁻¹ := by
    refine ⟨m, hmI, fun n hn => ?_⟩
    have hn' : m * n * m⁻¹ ∈ Iw := Iw.mul_mem (Iw.mul_mem hmI hn) (Iw.inv_mem hmI)
    have h3 := Subgroup.mem_centralizer_iff.1 hmc _ hn'
    calc b * n * b⁻¹ = (b * m⁻¹) * (m * n * m⁻¹) * (b * m⁻¹)⁻¹ := by group
      _ = ((m * n * m⁻¹) * (b * m⁻¹)) * (b * m⁻¹)⁻¹ := by rw [← h3]
      _ = m * n * m⁻¹ := by group
  obtain ⟨Oy, -, hOynorm, hOyodd, hOyZ⟩ :=
    zStar_at_u hset honly hfus hnd himg H0 (u := y) (Or.inl rfl) (hLy t p f y Iw Iv hnd himg)
  obtain ⟨Ob, hObodd, hObnorm, hObZ⟩ := zStar_conj g hOyodd hOynorm hOyZ
  have e_b : g⁻¹ * y * g = b := hb.symm
  have e_a : g⁻¹ * x * g = a := ha.symm
  rw [e_b] at hObnorm
  rw [e_b, e_a] at hObZ
  exact inner_case_false hset honly hfus hnd himg H0 hax hbx ha2 hb2 hab hb_ne hb1 hconja hane hinn
    hObodd hObnorm hObZ

theorem noOuterAt_proved {x : G} {K : Subgroup (CentralizerBar x)} (hset : S3Setup G x K)
    (honly : OnlyInvX x K) (hfus : NoFusionAt x K) (hLy : LyAt x K) : NoOuterAt x K := by
  intro t p f y Iw Iv hnd himg H0 g hne hcx hcy hout
  classical
  have hx2 := hnd.x_sq
  have hperf : Group.IsPerfect ↥Iw := hnd.Iw_quasisimple.1
  have hxIw : ∀ i ∈ Iw, i * x = x * i := fun i hi => mem_centralizer_singleton_iff.1 (hnd.Iw_le hi)
  obtain ⟨x', hx'⟩ : ∃ x' : G, x' = g * x * g⁻¹ := ⟨_, rfl⟩
  rw [← hx'] at hne hcx hcy hout
  have hx'2 : x' * x' = 1 := by
    rw [hx']
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hx'C : x' ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 hcx
  have hx'N : x' ∈ normalizer (Iw : Set G) := hnd.comp_w.le_normalizer hx'C
  have hσ2 : normalizerAct Iw ⟨x', hx'N⟩ * normalizerAct Iw ⟨x', hx'N⟩ = 1 := by
    rw [← map_mul]
    have : (⟨x', hx'N⟩ : normalizer (Iw : Set G)) * ⟨x', hx'N⟩ = 1 := Subtype.ext hx'2
    rw [this, map_one]
  have hσout : normalizerAct Iw ⟨x', hx'N⟩ ∉
      (inner (↥Iw ⧸ center ↥Iw) : Subgroup (MulAut (↥Iw ⧸ center ↥Iw))) := fun h =>
    hout (exists_inner_of_actMemInner hx'N h)
  obtain ⟨PK, hPK1, hPKperf, hPKfix⟩ := hnd.outerFixPerfect _ hσ2 hσout
  set π : ↥Iw →* ↥Iw ⧸ center ↥Iw := QuotientGroup.mk' (center ↥Iw) with hπ
  set E₁ : Subgroup ↥Iw := PK.comap π ⊓ (centralizer ({x'} : Set G)).subgroupOf Iw with hE₁
  have hmapE : E₁.map π = PK := by
    apply le_antisymm
    · rintro _ ⟨j, hj, rfl⟩
      exact hj.1
    · intro s hs
      obtain ⟨j, hj, hjs⟩ := KGroups.Bal.lift_fixed hnd.odd_w hx'2 hx'N (hPKfix s hs)
      refine ⟨j, ⟨?_, ?_⟩, hjs⟩
      · show π j ∈ PK
        rw [show π j = s from hjs]
        exact hs
      · have : (j : G) ∈ centralizer ({x'} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc (j : G) * x' = (x' * (j : G) * x'⁻¹) * x' := by rw [hj]
            _ = x' * j := by group
        exact this
  set P₀ : Subgroup ↥Iw := CFSG.Quasithin.perfectCore E₁ with hP₀
  have hP₀perf : ⁅P₀, P₀⁆ = P₀ := CFSG.Quasithin.perfectCore_perfect E₁
  have hP₀E : P₀ ≤ E₁ := CFSG.Quasithin.perfectCore_le E₁
  have hP₀map : P₀.map π = PK := by
    rw [hP₀, CFSG.Quasithin.map_perfectCore, hmapE]
    exact CFSG.Quasithin.perfectCore_eq_self_of_perfect hPKperf
  have hP₀1 : P₀ ≠ ⊥ := by
    intro h
    apply hPK1
    rw [← hP₀map, h, Subgroup.map_bot]
  have hP₀even : 2 ∣ Nat.card ↥P₀ := by
    by_contra hodd
    have hodd' : Odd (Nat.card ↥P₀) := Nat.odd_iff.2 (by omega)
    have hsolv : Group.IsSolvable ↥P₀ := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'
    have h1 := (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot P₀).1 hsolv
    rw [CFSG.Quasithin.perfectCore_eq_self_of_perfect hP₀perf] at h1
    exact hP₀1 h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥P₀) 2 hP₀even
  set y₂ : G := (((c : ↥P₀) : ↥Iw) : G) with hy₂
  have hy₂I : y₂ ∈ Iw := ((c : ↥P₀) : ↥Iw).2
  have hy₂2 : y₂ * y₂ = 1 := by
    have h1 : c * c = 1 := by
      have := pow_orderOf_eq_one c
      rwa [hc, pow_two] at this
    have := congrArg (fun z : ↥P₀ => (((z : ↥Iw)) : G)) h1
    simpa using this
  have hy₂1 : y₂ ≠ 1 := by
    intro h
    have h1 : c = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa [hy₂] using h
    rw [h1, orderOf_one] at hc
    omega
  have hy₂c : y₂ * x' = x' * y₂ := by
    have h1 : (((c : ↥P₀) : ↥Iw) : G) ∈ centralizer ({x'} : Set G) := (hP₀E c.2).2
    exact Subgroup.mem_centralizer_singleton_iff.1 h1
  obtain ⟨m, hmI, hmy⟩ := hnd.exists_conj_of_involution hy₂I hy₂2 hy₂1
  have hmx : m * x = x * m := hxIw m hmI
  have hmx' : m⁻¹ * x = x * m⁻¹ := by
    calc m⁻¹ * x = m⁻¹ * (x * m) * m⁻¹ := by group
      _ = m⁻¹ * (m * x) * m⁻¹ := by rw [hmx]
      _ = x * m⁻¹ := by group
  have hg' : (m⁻¹ * g) * x * (m⁻¹ * g)⁻¹ = m⁻¹ * x' * m := by
    rw [hx']; group
  refine noOuter_core hset honly hfus hLy hnd himg H0 (g := m⁻¹ * g) ?_ ?_ ?_ ?_
    (P := (P₀.map Iw.subtype).map (MulAut.conj m⁻¹).toMonoidHom) ?_ ?_ ?_
  · rw [hg']
    intro h
    apply hne
    calc x' = m * (m⁻¹ * x' * m) * m⁻¹ := by group
      _ = m * x * m⁻¹ := by rw [h]
      _ = x := by rw [hmx]; group
  · rw [hg']
    have h1 : x' * x = x * x' := hcx
    calc m⁻¹ * x' * m * x = m⁻¹ * x' * (m * x) := by group
      _ = m⁻¹ * x' * (x * m) := by rw [hmx]
      _ = m⁻¹ * (x' * x) * m := by group
      _ = m⁻¹ * (x * x') * m := by rw [h1]
      _ = (m⁻¹ * x) * x' * m := by group
      _ = (x * m⁻¹) * x' * m := by rw [hmx']
      _ = x * (m⁻¹ * x' * m) := by group
  · rw [hg']
    have h1 : x' * y₂ = y₂ * x' := hy₂c.symm
    have hy : y = m⁻¹ * y₂ * m := by rw [← hmy]; group
    rw [hy]
    calc m⁻¹ * x' * m * (m⁻¹ * y₂ * m) = m⁻¹ * (x' * y₂) * m := by group
      _ = m⁻¹ * (y₂ * x') * m := by rw [h1]
      _ = m⁻¹ * y₂ * m * (m⁻¹ * x' * m) := by group
  · rw [hg']
    rintro ⟨a, haI, hact⟩
    apply hout
    refine ⟨m * a * m⁻¹, Iw.mul_mem (Iw.mul_mem hmI haI) (Iw.inv_mem hmI), fun n hn => ?_⟩
    have hn' : m⁻¹ * n * m ∈ Iw := Iw.mul_mem (Iw.mul_mem (Iw.inv_mem hmI) hn) hmI
    have h1 := hact _ hn'
    calc x' * n * x'⁻¹ = m * ((m⁻¹ * x' * m) * (m⁻¹ * n * m) * (m⁻¹ * x' * m)⁻¹) * m⁻¹ := by group
      _ = m * (a * (m⁻¹ * n * m) * a⁻¹) * m⁻¹ := by rw [h1]
      _ = (m * a * m⁻¹) * n * (m * a * m⁻¹)⁻¹ := by group
  · rw [hg']
    rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : (((q : ↥Iw)) : G) * x' = x' * (((q : ↥Iw)) : G) :=
      Subgroup.mem_centralizer_singleton_iff.1 (show (((q : ↥Iw)) : G) ∈ centralizer ({x'} : Set G) from (hP₀E hq).2)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
    calc m⁻¹ * (q : G) * m⁻¹⁻¹ * (m⁻¹ * x' * m) = m⁻¹ * ((q : G) * x') * m := by group
      _ = m⁻¹ * (x' * (q : G)) * m := by rw [h1]
      _ = (m⁻¹ * x' * m) * (m⁻¹ * (q : G) * m⁻¹⁻¹) := by group
  · rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hP₀perf]
  · refine ⟨y₂, ⟨(c : ↥Iw), c.2, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hmy]
    group

end Inner

section Leaf

theorem b_S3_noOuterJNT_of_noFusion (h1 : B_S3_noFusionJNT) : B_S3_noOuterJNT :=
  fun G _ _ x K hset hmax hthin honly hLy =>
    noOuterAt_proved hset honly (h1 G x K hset hmax hthin honly hLy) hLy

end Leaf

end CFSG.GH74.Generic.S3
