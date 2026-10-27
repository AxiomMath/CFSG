module

public import Certificates.Data.Kernel.G2Three.Prim
public import CFSG.Certificates.Kernel.G2Three.Tables
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2ThreeCrit

public section

namespace CFSG.KC.G2Three

open CFSG.KC.Ord CFSG.KC.Loop CFSG.KD.G2Three CFSG.GH74.GLS.Stage2.Signalizer.Odd87.G2ThreeCert

theorem ltK_decW : ∀ L c, ltK (decW L c) = true
  | 0, _ => rfl
  | L + 1, c => by
    have e : decW (L + 1) c = Nat.mod c 8 :: decW L (Nat.div c 8) := rfl
    have ih := ltK_decW L (Nat.div c 8)
    unfold ltK at ih ⊢
    rw [e, List.all_cons, Bool.and_eq_true]
    exact ⟨Nat.blt_eq.mpr (Nat.mod_lt _ (by decide)), ih⟩

theorem chunk_at {S nc N i : ℕ} (hN : N ≤ nc * S) (hi : i < N) :
    0 < S ∧ i / S < nc ∧ Nat.add (Nat.mul (i / S) S) (i % S) = i := by
  have hS : 0 < S := by
    rcases Nat.eq_zero_or_pos S with h | h
    · subst h
      omega
    · exact h
  refine ⟨hS, (Nat.div_lt_iff_lt_mul hS).2 (by omega), Nat.div_add_mod' i S⟩

theorem primBeq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.mpr fun e => h (Nat.eq_of_beq_eq_true e)

theorem closK_sound {X CA CB IMG : ℕ → ℕ} {N S hi nc : ℕ}
    (h : ∀ c < nc, closK X CA CB IMG N c S hi = true) (hS : S ≤ 64 * hi) (hN : N ≤ nc * S) :
    ∀ i < N, ∀ k < 4,
      IMG (4 * i + k) < N ∧ X (IMG (4 * i + k)) = actK (CA k) (CB k) (X i) := by
  intro i hi k hk
  obtain ⟨hS0, hc, e⟩ := chunk_at hN hi
  have h1 := allBelow_g2 (h _ hc) hS (i % S) (Nat.mod_lt _ hS0)
  dsimp only at h1
  rw [e, Nat.blt_eq.mpr hi, cond_true] at h1
  simp only [clStep, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
  obtain ⟨⟨⟨⟨a0, b0⟩, a1, b1⟩, a2, b2⟩, a3, b3⟩ := h1
  interval_cases k
  · exact ⟨a0, b0⟩
  · exact ⟨a1, b1⟩
  · exact ⟨a2, b2⟩
  · exact ⟨a3, b3⟩

theorem forK_sound {X HA HB LAB HP HS ROOTS : ℕ → ℕ} {N nh m S hi nc : ℕ}
    (h : ∀ c < nc, forK X HA HB LAB HP HS ROOTS N nh m c S hi = true) (hS : S ≤ 64 * hi)
    (hN : N ≤ nc * S) :
    ∀ i < N, canK (X i) = true ∧ LAB i < m ∧ (ROOTS (LAB i) = i ∨ (HP i < i ∧ HS i < nh ∧
      LAB (HP i) = LAB i ∧ X i = actK (HA (HS i)) (HB (HS i)) (X (HP i)))) := by
  intro i hi
  obtain ⟨hS0, hc, e⟩ := chunk_at hN hi
  have h1 := allBelow_g2 (h _ hc) hS (i % S) (Nat.mod_lt _ hS0)
  dsimp only at h1
  rw [e, Nat.blt_eq.mpr hi, cond_true] at h1
  unfold forStep at h1
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq] at h1
  obtain ⟨⟨hcan, hl⟩, hr⟩ := h1
  refine ⟨hcan, hl, ?_⟩
  by_cases hroot : ROOTS (LAB i) = i
  · exact Or.inl hroot
  · rw [primBeq_false hroot, cond_false] at hr
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hr
    obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := hr
    exact Or.inr ⟨a, b, c, d⟩

theorem hK_sound {X0 : ℕ} {GA GB HA HB : ℕ → ℕ} {W : ℕ → List ℕ} {nh : ℕ}
    (h : hK X0 GA GB HA HB W nh = true) (hn : nh ≤ 64) :
    ∀ s < nh, ltK (W s) = true ∧ HA s = wA GA (W s) ∧ HB s = wB GB (W s) ∧
      actK (HA s) (HB s) X0 = X0 := by
  intro s hs
  have h1 := allBelow_g2 h (by omega) s hs
  simp only [Bool.and_eq_true, Nat.beq_eq] at h1
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h1
  exact ⟨a, b, c, d⟩

theorem rootK_sound {X GA GB RA RB RL RC ROOTS : ℕ → ℕ} {N m hi : ℕ}
    (h : rootK X GA GB RA RB RL RC ROOTS N m hi = true) (hm : m ≤ 64 * hi) :
    ROOTS 0 = 0 ∧ ∀ q < m, 0 < q → ROOTS q < N ∧ RA q = wA GA (decW (RL q) (RC q)) ∧
      RB q = wB GB (decW (RL q) (RC q)) ∧ actK (RA q) (RB q) (X 0) = X (ROOTS q) := by
  unfold rootK at h
  rw [Bool.and_eq_true, Nat.beq_eq] at h
  refine ⟨h.1, fun q hq hq0 => ?_⟩
  have h1 := allBelow_g2 h.2 hm q hq
  rw [primBeq_false (by omega : q ≠ 0), cond_false] at h1
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h1
  exact ⟨a, b, c, d⟩

theorem trK_sound {X RA RB LAB TP TD EU EV : ℕ → ℕ} {N m hi : ℕ}
    (h : trK X RA RB LAB TP TD EU EV N m hi = true) (hm : m * m ≤ 64 * hi) :
    ∀ j < m, ∀ q < m, 0 < j → 0 < q → TP (j * m + q) < m ∧
      TD (j * m + TP (j * m + q)) < TD (j * m + q) ∧ EU (j * m + q) < N ∧ EV (j * m + q) < N ∧
      LAB (EU (j * m + q)) = TP (j * m + q) ∧ LAB (EV (j * m + q)) = q ∧
      X (EV (j * m + q)) = actK (RA j) (RB j) (X (EU (j * m + q))) := by
  intro j hj q hq hj0 hq0
  have ht : j * m + q < m * m := by nlinarith
  have h1 := allBelow_g2 h hm _ ht
  unfold trStep at h1
  have ed : Nat.div (j * m + q) m = j := by
    change (j * m + q) / m = j
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hq, Nat.zero_add]
  have em : Nat.mod (j * m + q) m = q := by
    change (j * m + q) % m = q
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]
  dsimp only at h1
  rw [ed, em, primBeq_false (by omega : j ≠ 0), primBeq_false (by omega : q ≠ 0), Bool.or_false,
    cond_false] at h1
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
  obtain ⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩ := h1
  exact ⟨a, b, c, d, e, f, g⟩

theorem ntK_sound {X CA CB : ℕ → ℕ} (h : ntK X CA CB = true) :
    ∃ k < 4, actK (CA k) (CB k) (X 0) ≠ X 0 := by
  by_contra hc
  push Not at hc
  unfold ntK at h
  rw [hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide), Nat.beq_refl] at h
  simp at h

section Group

variable {G Y : Type*} [Group G] [MulAction G Y]

theorem forest_mem {dec : ℕ → Y} {V : ℕ → Prop} {Hs : Subgroup G}
    {X HA HB LAB HP HS ROOTS : ℕ → ℕ} {N nh : ℕ}
    (hH : ∀ s < nh, ∀ P, V P → ∃ h ∈ Hs, dec (actK (HA s) (HB s) P) = h • dec P)
    (hfo : ∀ i < N, V (X i) ∧ (ROOTS (LAB i) = i ∨ (HP i < i ∧ HS i < nh ∧
      LAB (HP i) = LAB i ∧ X i = actK (HA (HS i)) (HB (HS i)) (X (HP i))))) :
    ∀ i < N, ∃ h ∈ Hs, dec (X i) = h • dec (X (ROOTS (LAB i))) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases (hfo i hi).2 with hr | ⟨hp, hs, hl, hx⟩
    · exact ⟨1, Hs.one_mem, by rw [hr, one_smul]⟩
    · obtain ⟨h', hh', e'⟩ := ih (HP i) hp (by omega)
      obtain ⟨h, hh, e⟩ := hH (HS i) hs (X (HP i)) (hfo (HP i) (by omega)).1
      refine ⟨h * h', Hs.mul_mem hh hh', ?_⟩
      rw [hx, e, e', hl, mul_smul]

theorem orbit_sub {dec : ℕ → Y} {V : ℕ → Prop} {gc : ℕ → G}
    (hgc : Subgroup.closure (gc '' {k | k < 4}) = ⊤) {CA CB X IMG : ℕ → ℕ} {N : ℕ}
    (hc : ∀ k < 4, ∀ P, V P → dec (actK (CA k) (CB k) P) = gc k • dec P)
    (hV : ∀ i < N, V (X i))
    (hcl : ∀ i < N, ∀ k < 4,
      IMG (4 * i + k) < N ∧ X (IMG (4 * i + k)) = actK (CA k) (CB k) (X i))
    (g : G) : ∀ i < N, ∃ j < N, g • dec (X i) = dec (X j) := by
  classical
  let Ys : Set Y := (fun i => dec (X i)) '' Set.Iio N
  have hfin : Ys.Finite := (Set.finite_Iio N).image _
  have key : ∀ g : G, Set.MapsTo (g • ·) Ys Ys → Set.MapsTo (g⁻¹ • ·) Ys Ys := by
    intro g hg y hy
    have hinj : Set.InjOn (g • ·) Ys := fun a _ b _ hab => smul_left_cancel g hab
    obtain ⟨y', hy', e⟩ := ((hfin.injOn_iff_bijOn_of_mapsTo hg).1 hinj).surjOn hy
    have e2 : g⁻¹ • y = y' := by
      rw [← e]
      exact inv_smul_smul g y'
    simp only
    rw [e2]
    exact hy'
  have hall : ∀ g ∈ Subgroup.closure (gc '' {k | k < 4}), Set.MapsTo (g • ·) Ys Ys := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      rintro _ ⟨i, hi, rfl⟩
      obtain ⟨h1, h2⟩ := hcl i hi k hk
      refine ⟨IMG (4 * i + k), h1, ?_⟩
      simp only
      rw [h2, hc k hk _ (hV i hi)]
    | one =>
      intro y hy
      simpa using hy
    | mul x y _ _ hx hy =>
      intro z hz
      simpa [mul_smul] using hx (hy hz)
    | inv x _ hx => exact key x hx
  intro i hi
  have hg : g ∈ Subgroup.closure (gc '' {k | k < 4}) := by
    rw [hgc]
    exact Subgroup.mem_top g
  obtain ⟨j, hj, e⟩ := hall g hg ⟨i, hi, rfl⟩
  exact ⟨j, hj, e.symm⟩

theorem reach_roots {dec : ℕ → Y} {K : Subgroup G} {r : G} (hr : r ∈ K)
    {X LAB ROOTS TP TD EU EV : ℕ → ℕ} {N m j : ℕ}
    (hfor : ∀ i < N, ∃ h ∈ K, dec (X i) = h • dec (X (ROOTS (LAB i))))
    (hR0 : ROOTS 0 = 0)
    (he : ∀ q < m, 0 < q → TP (j * m + q) < m ∧
      TD (j * m + TP (j * m + q)) < TD (j * m + q) ∧ EU (j * m + q) < N ∧ EV (j * m + q) < N ∧
      LAB (EU (j * m + q)) = TP (j * m + q) ∧ LAB (EV (j * m + q)) = q ∧
      dec (X (EV (j * m + q))) = r • dec (X (EU (j * m + q)))) :
    ∀ q < m, ∃ k ∈ K, dec (X (ROOTS q)) = k • dec (X 0) := by
  suffices H : ∀ d q, q < m → TD (j * m + q) ≤ d →
      ∃ k ∈ K, dec (X (ROOTS q)) = k • dec (X 0) from
    fun q hq => H _ q hq le_rfl
  intro d
  induction d with
  | zero =>
    intro q hq hd
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · exact ⟨1, K.one_mem, by rw [hR0, one_smul]⟩
    · have := (he q hq hq0).2.1
      omega
  | succ d ih =>
    intro q hq hd
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · exact ⟨1, K.one_mem, by rw [hR0, one_smul]⟩
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := he q hq hq0
      obtain ⟨k', hk', ek'⟩ := ih _ h1 (by omega)
      obtain ⟨hu, hhu, eu⟩ := hfor _ h3
      obtain ⟨hv, hhv, ev⟩ := hfor _ h4
      refine ⟨hv⁻¹ * (r * (hu * k')),
        K.mul_mem (K.inv_mem hhv) (K.mul_mem hr (K.mul_mem hhu hk')), ?_⟩
      have e1 : dec (X (ROOTS q)) = hv⁻¹ • dec (X (EV (j * m + q))) := by
        rw [ev, h6, inv_smul_smul]
      rw [e1, h7, eu, h5, ek', mul_smul, mul_smul, mul_smul]

theorem coatom_of_facts {dec : ℕ → Y} {V : ℕ → Prop} {gc : ℕ → G} {gw : List ℕ → G}
    (hgc : Subgroup.closure (gc '' {k | k < 4}) = ⊤)
    {CA CB GA GB X IMG LAB HP HS ROOTS HA HB RA RB RL RC TP TD EU EV : ℕ → ℕ}
    {W : ℕ → List ℕ} {N nh m : ℕ}
    (hc : ∀ k < 4, ∀ P, V P → dec (actK (CA k) (CB k) P) = gc k • dec P)
    (hw : ∀ w, ltK w = true → ∀ P, V P → dec (actK (wA GA w) (wB GB w) P) = gw w • dec P)
    (hinj : ∀ P Q, V P → V Q → dec P = dec Q → P = Q)
    (hN : 0 < N)
    (hcl : ∀ i < N, ∀ k < 4,
      IMG (4 * i + k) < N ∧ X (IMG (4 * i + k)) = actK (CA k) (CB k) (X i))
    (hfo : ∀ i < N, V (X i) ∧ LAB i < m ∧ (ROOTS (LAB i) = i ∨ (HP i < i ∧ HS i < nh ∧
      LAB (HP i) = LAB i ∧ X i = actK (HA (HS i)) (HB (HS i)) (X (HP i)))))
    (hh : ∀ s < nh, ltK (W s) = true ∧ HA s = wA GA (W s) ∧ HB s = wB GB (W s) ∧
      actK (HA s) (HB s) (X 0) = X 0)
    (hR0 : ROOTS 0 = 0)
    (hr : ∀ q < m, 0 < q → ROOTS q < N ∧ RA q = wA GA (decW (RL q) (RC q)) ∧
      RB q = wB GB (decW (RL q) (RC q)) ∧ actK (RA q) (RB q) (X 0) = X (ROOTS q))
    (ht : ∀ j < m, ∀ q < m, 0 < j → 0 < q → TP (j * m + q) < m ∧
      TD (j * m + TP (j * m + q)) < TD (j * m + q) ∧ EU (j * m + q) < N ∧ EV (j * m + q) < N ∧
      LAB (EU (j * m + q)) = TP (j * m + q) ∧ LAB (EV (j * m + q)) = q ∧
      X (EV (j * m + q)) = actK (RA j) (RB j) (X (EU (j * m + q))))
    (hnt : ∃ k < 4, actK (CA k) (CB k) (X 0) ≠ X 0) :
    IsCoatom (MulAction.stabilizer G (dec (X 0))) := by
  classical
  have hV : ∀ i < N, V (X i) := fun i hi => (hfo i hi).1
  let Hs := Subgroup.closure ((fun s => gw (W s)) '' {s | s < nh})
  have hHact : ∀ s < nh, ∀ P, V P → ∃ h ∈ Hs, dec (actK (HA s) (HB s) P) = h • dec P := by
    intro s hs P hP
    obtain ⟨hl, ha, hb, -⟩ := hh s hs
    exact ⟨gw (W s), Subgroup.subset_closure ⟨s, hs, rfl⟩, by rw [ha, hb, hw _ hl P hP]⟩
  have hfor : ∀ i < N, ∃ h ∈ Hs, dec (X i) = h • dec (X (ROOTS (LAB i))) :=
    forest_mem hHact fun i hi => ⟨(hfo i hi).1, (hfo i hi).2.2⟩
  have hHs0 : Hs ≤ MulAction.stabilizer G (dec (X 0)) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨hl, ha, hb, hfix⟩ := hh s hs
    change gw (W s) • dec (X 0) = dec (X 0)
    rw [← hw _ hl _ (hV 0 hN), ← ha, ← hb, hfix]
  have hroot : ∀ q < m, 0 < q → dec (X (ROOTS q)) = gw (decW (RL q) (RC q)) • dec (X 0) := by
    intro q hq hq0
    obtain ⟨-, ha, hb, hx⟩ := hr q hq hq0
    rw [← hx, ha, hb, hw _ (ltK_decW _ _) _ (hV 0 hN)]
  refine isCoatom_stabilizer_of_cover (dec (X 0)) ?_ Hs hHs0
    ((fun q => gw (decW (RL q) (RC q))) '' {q | 0 < q ∧ q < m}) ?_ ?_
  · obtain ⟨k, hk, hne⟩ := hnt
    refine ⟨gc k, fun h => hne ?_⟩
    obtain ⟨h1, h2⟩ := hcl 0 hN k hk
    rw [← h2]
    refine hinj _ _ (hV _ h1) (hV 0 hN) ?_
    rw [h2, hc k hk _ (hV 0 hN)]
    exact h
  · intro g hg
    obtain ⟨i, hi, e⟩ := orbit_sub hgc hc hV hcl g 0 hN
    obtain ⟨h, hh', eh⟩ := hfor i hi
    have hq := (hfo i hi).2.1
    rcases Nat.eq_zero_or_pos (LAB i) with h0 | h0
    · have hfix : g • dec (X 0) = dec (X 0) := by
        rw [e, eh, h0, hR0]
        exact hHs0 hh'
      exact absurd hfix hg
    · exact ⟨_, ⟨LAB i, ⟨h0, hq⟩, rfl⟩, h, hh', by rw [e, eh, hroot _ hq h0, mul_smul]⟩
  · rintro _ ⟨j, ⟨hj0, hj⟩, rfl⟩ g
    let K := Subgroup.closure ((Hs : Set G) ∪ {gw (decW (RL j) (RC j))})
    have hHK : Hs ≤ K := fun x hx => Subgroup.subset_closure (Or.inl hx)
    have hrK : gw (decW (RL j) (RC j)) ∈ K := Subgroup.subset_closure (Or.inr rfl)
    have hreach := reach_roots (X := X) (j := j) (N := N) hrK
      (fun i hi => by
        obtain ⟨h, hh', eh⟩ := hfor i hi
        exact ⟨h, hHK hh', eh⟩) hR0
      (fun q hq hq0 => by
        obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := ht j hj q hq hj0 hq0
        obtain ⟨-, ha, hb, -⟩ := hr j hj hj0
        exact ⟨a1, a2, a3, a4, a5, a6, by rw [a7, ha, hb, hw _ (ltK_decW _ _) _ (hV _ a3)]⟩)
    obtain ⟨i, hi, e⟩ := orbit_sub hgc hc hV hcl g 0 hN
    obtain ⟨h, hh', eh⟩ := hfor i hi
    obtain ⟨k, hk, ek⟩ := hreach (LAB i) (hfo i hi).2.1
    exact ⟨h * k, K.mul_mem (hHK hh') hk, by rw [e, eh, ek, mul_smul]⟩

theorem prim_coatom {dec : ℕ → Y} {gc : ℕ → G} {gw : List ℕ → G}
    (hgc : Subgroup.closure (gc '' {k | k < 4}) = ⊤)
    {CA CB GA GB X IMG LAB HP HS ROOTS HA HB RA RB RL RC TP TD EU EV : ℕ → ℕ}
    {W : ℕ → List ℕ} {N nh m S nc hiS hiR hiT : ℕ}
    (hc : ∀ k < 4, ∀ P, canK P = true → dec (actK (CA k) (CB k) P) = gc k • dec P)
    (hw : ∀ w, ltK w = true → ∀ P, canK P = true →
      dec (actK (wA GA w) (wB GB w) P) = gw w • dec P)
    (hinj : ∀ P Q, canK P = true → canK Q = true → dec P = dec Q → P = Q)
    (hN : 0 < N) (hNS : N ≤ nc * S) (hS : S ≤ 64 * hiS) (hnh : nh ≤ 64) (hm : m ≤ 64 * hiR)
    (hmm : m * m ≤ 64 * hiT)
    (hcl : ∀ c < nc, closK X CA CB IMG N c S hiS = true)
    (hfo : ∀ c < nc, forK X HA HB LAB HP HS ROOTS N nh m c S hiS = true)
    (hh : hK (X 0) GA GB HA HB W nh = true)
    (hr : rootK X GA GB RA RB RL RC ROOTS N m hiR = true)
    (ht : trK X RA RB LAB TP TD EU EV N m hiT = true)
    (hnt : ntK X CA CB = true) :
    IsCoatom (MulAction.stabilizer G (dec (X 0))) :=
  coatom_of_facts (V := fun P => canK P = true) hgc hc hw hinj hN (closK_sound hcl hS hNS)
    (forK_sound hfo hS hNS) (hK_sound hh hnh) (rootK_sound hr hm).1 (rootK_sound hr hm).2
    (trK_sound ht hmm) (ntK_sound hnt)

end Group

end CFSG.KC.G2Three

end
