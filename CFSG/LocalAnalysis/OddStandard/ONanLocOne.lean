module

public import CFSG.LocalAnalysis.OddStandard.ONanFusAC
public import CFSG.Goldschmidt.OddCore

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris

set_option maxRecDepth 100000 in
theorem comm_st_W : ∀ w : AlpE, w.d = 0 → w * w = 1 →
    w⁻¹ * (invE 4 * w * (invE 4)⁻¹) = 1 ∨ w⁻¹ * (invE 4 * w * (invE 4)⁻¹) = invE 1 := by
  decide +kernel

theorem comm_st_v1sq : (gen 0 ^ 2)⁻¹ * (invE 4 * gen 0 ^ 2 * (invE 4)⁻¹) = invE 1 := by decide

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

theorem mem_W_of_inClass {i : Fin 7} {x : G} (hi : D.InClass i x) (h2 : i.val ≤ 2) :
    x ∈ alpW v1 v2 v3 := by
  refine D.mem_W_iff.2 ⟨?_, hi.sq⟩
  obtain ⟨c, hc, rfl⟩ := hi
  have h := AlpEmb.alpV_normal D.E (inv_mem hc) (D.rep_mem_V h2)
  rwa [inv_inv] at h

@[expose] def CommIn (_D : FusCtx G v1 v2 v3 s t) (g u : G) : Prop :=
  ∀ w ∈ alpW v1 v2 v3, w⁻¹ * (g * w * g⁻¹) = 1 ∨ w⁻¹ * (g * w * g⁻¹) = u

theorem CommIn.conj {g u n : G} (h : D.CommIn g u)
    (hn : n ∈ normalizer (alpW v1 v2 v3 : Set G)) : D.CommIn (n * g * n⁻¹) (n * u * n⁻¹) := by
  intro w hw
  have hw' : n⁻¹ * w * n ∈ alpW v1 v2 v3 := by
    have := (mem_normalizer_iff.1 (inv_mem hn) w).1 hw
    rwa [inv_inv] at this
  have e : w⁻¹ * (n * g * n⁻¹ * w * (n * g * n⁻¹)⁻¹) =
      n * ((n⁻¹ * w * n)⁻¹ * (g * (n⁻¹ * w * n) * g⁻¹)) * n⁻¹ := by group
  rw [e]
  rcases h _ hw' with h1 | h1
  · left
    rw [h1]
    group
  · right
    rw [h1]

omit [Finite G] D in
theorem conj_mem_centralizer_W {m x : G} (hm : m ∈ normalizer (alpW v1 v2 v3 : Set G))
    (hx : x ∈ centralizer (alpW v1 v2 v3 : Set G)) :
    m * x * m⁻¹ ∈ centralizer (alpW v1 v2 v3 : Set G) := by
  rw [mem_centralizer_iff] at hx ⊢
  intro w hw
  have hw' : m⁻¹ * w * m ∈ alpW v1 v2 v3 := by
    have := (mem_normalizer_iff.1 (inv_mem hm) w).1 hw
    rwa [inv_inv] at this
  have h := hx _ hw'
  calc w * (m * x * m⁻¹) = m * ((m⁻¹ * w * m) * x) * m⁻¹ := by group
    _ = m * (x * (m⁻¹ * w * m)) * m⁻¹ := by rw [h]
    _ = m * x * m⁻¹ * w := by group

theorem commIn_st : D.CommIn (s * t) (invRep v1 v2 v3 s t 1) := by
  intro w hw
  obtain ⟨hwV, hw2⟩ := D.mem_W_iff.1 hw
  rw [AlpEmb.alpV_eq_map D.E] at hwV
  obtain ⟨w', hw'V, rfl⟩ := Subgroup.mem_map.1 hwV
  have hw'2 : w' * w' = 1 := D.E.inj (by rw [map_mul, hw2, map_one])
  have hst : s * t = D.E.φ (invE 4) := (AlpEmb.φ_invE D.E 4).symm
  have e : (D.E.φ w')⁻¹ * (D.E.φ (invE 4) * D.E.φ w' * (D.E.φ (invE 4))⁻¹) =
      D.E.φ (w'⁻¹ * (invE 4 * w' * (invE 4)⁻¹)) := by simp only [map_mul, map_inv]
  rw [hst, e]
  rcases comm_st_W w' (mem_Vsub.1 hw'V) hw'2 with h | h
  · exact Or.inl (by rw [h, map_one])
  · exact Or.inr (by rw [h, AlpEmb.φ_invE])

theorem comm_st_v1sq_G :
    (v1 ^ 2)⁻¹ * (s * t * v1 ^ 2 * (s * t)⁻¹) = invRep v1 v2 v3 s t 1 := by
  have h := congrArg D.E.φ comm_st_v1sq
  simp only [map_mul, map_inv, map_pow, AlpEmb.φ_invE, AlpEmb.φ_v1] at h
  exact h

theorem fus_E_DFG (hAB : D.Fus 0 1) : D.Fus 4 3 ∨ D.Fus 4 5 ∨ D.Fus 4 6 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set z := invRep v1 v2 v3 s t 0 with hz
  set b := invRep v1 v2 v3 s t 1 with hb
  obtain ⟨n, hnN, hn⟩ : ∃ n ∈ normalizer (alpV v1 v2 v3 : Set G), n * b * n⁻¹ = z := by
    obtain ⟨g, hg⟩ := hAB
    obtain ⟨n, hn, hnb⟩ := D.fuse_V (x := b) (y := z) (D.V_le_centralizer_V D.b_mem_V)
      (D.V_le_centralizer_V D.z_mem_V') ⟨g, by rw [hb, hz, ← hg]; group⟩
    exact ⟨n⁻¹, inv_mem hn, by rw [inv_inv]; exact hnb⟩
  have hnW : n ∈ normalizer (alpW v1 v2 v3 : Set G) := D.normalizer_V_le_W hnN
  have hstP : s * t ∈ alpP v1 v2 v3 s t := AlpEmb.invRep_mem D.E 4
  have hst2 : s * t * (s * t) = 1 := D.rep_sq 4
  have hstW : s * t ∉ centralizer (alpW v1 v2 v3 : Set G) := by
    intro h
    have hV : s * t ∈ alpV v1 v2 v3 := by
      rw [← D.P_inf_centralizer_W]
      exact ⟨hstP, h⟩
    exact absurd (D.le_two_of_invRep_mem_V (i := 4) hV) (by decide)
  set u := n * (s * t) * n⁻¹ with hu
  have hcu : D.CommIn u z := by
    have h := CommIn.conj D D.commIn_st hnW
    rwa [hn] at h
  have huW : u ∉ centralizer (alpW v1 v2 v3 : Set G) := by
    intro h
    apply hstW
    have h' := conj_mem_centralizer_W (inv_mem hnW) h
    rwa [hu, show n⁻¹ * (n * (s * t) * n⁻¹) * n⁻¹⁻¹ = s * t by group] at h'
  have hzW : z ∈ alpW v1 v2 v3 := sq_mul_sq_mem_alpW v1 v2 v3
  have huz : u * z = z * u := by
    rcases hcu z hzW with h | h
    · have h' : u * z * u⁻¹ = z := by
        calc u * z * u⁻¹ = z * (z⁻¹ * (u * z * u⁻¹)) := by group
          _ = z := by rw [h, mul_one]
      calc u * z = u * z * u⁻¹ * u := by group
        _ = z * u := by rw [h']
    · exfalso
      have h' : u * z * u⁻¹ = 1 := by
        calc u * z * u⁻¹ = z * (z⁻¹ * (u * z * u⁻¹)) := by group
          _ = z * z := by rw [h]
          _ = 1 := D.rep_sq 0
      apply D.rep_ne_one 0
      calc z = u⁻¹ * (u * z * u⁻¹) * u := by group
        _ = 1 := by rw [h']; group
  set Nz := normalizer (alpW v1 v2 v3 : Set G) ⊓ centralizer ({z} : Set G) with hNz
  have hzc : ∀ c ∈ alpP v1 v2 v3 s t, c * z = z * c :=
    (AlpEmb.centre_alpP D.E D.hF D.z_mem_P).2 (Or.inr rfl)
  have hPNz : alpP v1 v2 v3 s t ≤ Nz := fun p hp =>
    ⟨D.P_le_normalizer_W hp, mem_centralizer_singleton_iff.2 (hzc p hp)⟩
  have hSyl : IsSylowOf 2 (alpP v1 v2 v3 s t) Nz := D.isSylowOf_P.of_le hPNz le_top
  have hu2 : u * u = 1 := by
    calc u * u = n * (s * t * (s * t)) * n⁻¹ := by rw [hu]; group
      _ = 1 := by rw [hst2]; group
  have hu1 : u ≠ 1 := fun h => huW (by rw [h]; exact Subgroup.one_mem _)
  have huNz : zpowers u ≤ Nz := by
    rw [zpowers_le]
    have hun : n * (s * t) * n⁻¹ ∈ normalizer (alpW v1 v2 v3 : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hnW (D.P_le_normalizer_W hstP))
        (Subgroup.inv_mem _ hnW)
    exact Subgroup.mem_inf.2 ⟨hun, mem_centralizer_singleton_iff.2 huz⟩
  have hup : IsPGroup 2 (zpowers u) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [pow_two, hu2]) hu1
  obtain ⟨m, hmNz, hm⟩ := exists_conj_le_of_isSylowOf hSyl huNz hup
  have hmW : m ∈ normalizer (alpW v1 v2 v3 : Set G) := hmNz.1
  have hmz : m * z * m⁻¹ = z := by
    have h := mem_centralizer_singleton_iff.1 hmNz.2
    rw [h, mul_inv_cancel_right]
  set y := m * u * m⁻¹ with hy
  have hyP : y ∈ alpP v1 v2 v3 s t := hm u (mem_zpowers u)
  have hy2 : y * y = 1 := by
    calc y * y = m * (u * u) * m⁻¹ := by rw [hy]; group
      _ = 1 := by rw [hu2]; group
  have hyV : y ∉ alpV v1 v2 v3 := by
    intro h
    apply huW
    have h' := conj_mem_centralizer_W (inv_mem hmW) (D.V_le_centralizer_W h)
    rwa [hy, show m⁻¹ * (m * u * m⁻¹) * m⁻¹⁻¹ = u by group] at h'
  have hy1 : y ≠ 1 := fun h => hyV (by rw [h]; exact Subgroup.one_mem _)
  obtain ⟨j, hj⟩ := D.exists_inClass hyP hy2 hy1
  have hfus : D.Fus 4 j := D.inClass_fus (D.inClass_rep 4) hj (m * n)⁻¹ (by
    show (m * n)⁻¹⁻¹ * (s * t) * (m * n)⁻¹ = y
    rw [hy, hu]
    group)
  have hj3 : 3 ≤ j.val := by
    by_contra hlt
    exact hyV (D.W_le_V (D.mem_W_of_inClass hj (by omega)))
  have hcy : D.CommIn y z := by
    have h := CommIn.conj D hcu hmW
    rwa [hmz] at h
  have hj4 : j ≠ 4 := by
    rintro rfl
    obtain ⟨c, hc, hcy'⟩ := hj
    have hcy'' : c⁻¹ * (s * t) * c = y := hcy'
    have hv1W : v1 ^ 2 ∈ alpW v1 v2 v3 := subset_closure (by simp)
    have hw : c⁻¹ * v1 ^ 2 * c ∈ alpW v1 v2 v3 := by
      have h := AlpEmb.alpW_normal D.E D.hF (inv_mem hc) hv1W
      rwa [inv_inv] at h
    have hval : (c⁻¹ * v1 ^ 2 * c)⁻¹ * (y * (c⁻¹ * v1 ^ 2 * c) * y⁻¹) = c⁻¹ * b * c := by
      rw [← hcy'', hb, ← D.comm_st_v1sq_G]
      group
    have hbz : b ≠ z := fun h => by
      have h' : invRep v1 v2 v3 s t 1 = invRep v1 v2 v3 s t 0 := h
      exact absurd (InClass.unique D (h' ▸ D.inClass_rep 1) (D.inClass_rep 0)) (by decide)
    rcases hcy _ hw with h | h
    · rw [hval] at h
      apply D.rep_ne_one 1
      calc b = c * (c⁻¹ * b * c) * c⁻¹ := by group
        _ = 1 := by rw [h]; group
    · rw [hval] at h
      apply hbz
      calc b = c * (c⁻¹ * b * c) * c⁻¹ := by group
        _ = c * z * c⁻¹ := by rw [h]
        _ = z := by rw [hzc c hc, mul_inv_cancel_right]
  have : j = 3 ∨ j = 5 ∨ j = 6 := by omega
  rcases this with rfl | rfl | rfl
  · exact Or.inl hfus
  · exact Or.inr (Or.inl hfus)
  · exact Or.inr (Or.inr hfus)

theorem exists_fusABC_out [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a)
    (hgold : CFSG.Goldschmidt.CoreStatement) : ∃ j : Fin 7, 3 ≤ j.val ∧ D.FusABC j := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  have hcl : CFSG.Open.fusionStronglyClosed (alpW v1 v2 v3 : Set G) (D.P : Subgroup G) := by
    intro a ha g hg
    rw [D.hP] at hg
    have haW : a ∈ alpW v1 v2 v3 := ha
    show g⁻¹ * a * g ∈ alpW v1 v2 v3
    by_cases ha1 : a = 1
    · rw [ha1, mul_one, inv_mul_cancel]
      exact one_mem _
    obtain ⟨haV, ha2⟩ := D.mem_W_iff.1 haW
    obtain ⟨i, hi⟩ := D.exists_inClass (D.V_le_P haV) ha2 ha1
    have hi2 := D.le_two_of_inClass_mem_V hi haV
    have hy2 : g⁻¹ * a * g * (g⁻¹ * a * g) = 1 := by
      calc g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
        _ = 1 := by rw [ha2]; group
    have hy1 : g⁻¹ * a * g ≠ 1 := by
      intro h1
      apply ha1
      calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨j, hj⟩ := D.exists_inClass hg hy2 hy1
    by_cases hj2 : j.val ≤ 2
    · exact D.mem_W_of_inClass hj hj2
    · exact absurd (D.fusABC_of_le_two hi2 (Fus.symm D (D.inClass_fus hi hj g rfl)))
        (hcon j (by omega))
  have hle : alpW v1 v2 v3 ≤ (D.P : Subgroup G) := by
    rw [D.hP]
    exact D.W_le_P
  have hab : IsMulCommutative (alpW v1 v2 v3) := ⟨⟨fun a b => Subtype.ext
    (mem_centralizer_iff.1 (D.V_le_centralizer_V (D.W_le_V b.2)) a (D.W_le_V a.2))⟩⟩
  have hzW : invRep v1 v2 v3 s t 0 ∈ alpW v1 v2 v3 := sq_mul_sq_mem_alpW v1 v2 v3
  have hW1 : alpW v1 v2 v3 ≠ ⊥ := fun h => D.rep_ne_one 0 (by
    rw [h] at hzW
    exact (mem_bot.1 hzW))
  have hnc : normalClosure (alpW v1 v2 v3 : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (normalClosure (alpW v1 v2 v3 : Set G))
      with h | h
    · exact absurd (eq_bot_iff.2 (h ▸ le_normalClosure)) hW1
    · exact h
  have h2 : Even (Nat.card G) :=
    even_iff_two_dvd.2 (D.orderOf_rep 0 ▸ orderOf_dvd_natCard (invRep v1 v2 v3 s t 0))
  have hO : CFSG.Open.goldschmidtOddCore G = ⊥ := by
    rw [CFSG.Open.goldschmidtOddCore, sSup_eq_bot]
    rintro N ⟨hN, hodd⟩
    have := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · rw [h, Subgroup.card_top] at hodd
      exact absurd h2 (Nat.not_even_iff_odd.mpr hodd)
  have hO2 : CFSG.Open.pCore 2 G = ⊥ := by
    rw [CFSG.pCore_eq_iSup, eq_bot_iff]
    refine iSup_le fun N => iSup_le fun hN => iSup_le fun hp => ?_
    have := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h.le
    · exfalso
      subst h
      have hX : IsPGroup 2 G := hp.of_equiv Subgroup.topEquiv
      obtain ⟨a, b, hab⟩ := hna
      have : Nontrivial G := ⟨⟨a * b, b * a, hab⟩⟩
      have hc := hX.center_nontrivial
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
      · rw [h] at hc
        exact (Subgroup.nontrivial_iff_ne_bot _).1 hc rfl
      · exact hab ((Subgroup.mem_center_iff.1 (h ▸ mem_top b)) a)
  obtain ⟨h1, h2, -⟩ := hgold G D.P (alpW v1 v2 v3) hle hab hcl hnc hO
  rw [hO2, bot_sup_eq] at h1 h2
  rw [h1] at h2
  have ht : t ∈ alpW v1 v2 v3 := by
    rw [h2]
    refine subset_closure ⟨mem_inf.2 ⟨?_, mem_top t⟩, ?_⟩
    · rw [D.hP]
      exact AlpEmb.invRep_mem D.E 5
    · exact D.fr.t_two
  exact absurd (D.le_two_of_invRep_mem_V (i := 5) (D.W_le_V ht)) (by decide)

theorem fus_all [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a)
    (hgold : CFSG.Goldschmidt.CoreStatement) : ∀ i : Fin 7, D.Fus 0 i := by
  have hAB := D.fus_AB
  have hAC := D.fus_AC hAB
  obtain ⟨j0, hj0, hABC0⟩ := D.exists_fusABC_out hna hgold
  have hE := D.fus_E_DFG hAB
  have hno : ∀ {i j : Fin 7}, D.Fus i j → ¬ D.FusABC j → ¬ D.FusABC i :=
    fun hij hj hi => hj (FusABC.of_fus D (Fus.symm D hij) hi)
  have hall : ∀ k : Fin 7, 3 ≤ k.val → D.FusABC k := by
    by_contra hcon
    push Not at hcon
    obtain ⟨k, hk, hnk⟩ := hcon
    have h356 : ¬ D.FusABC 3 ∧ ¬ D.FusABC 5 ∧ ¬ D.FusABC 6 := by
      have : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · obtain ⟨h5, h6⟩ := D.fus_D hnk
        exact ⟨hnk, hno (Fus.symm D h5) hnk, hno (Fus.symm D h6) hnk⟩
      · obtain ⟨h3, h5, h6⟩ := D.fus_E hnk
        exact ⟨hno (Fus.symm D h3) hnk, hno (Fus.symm D h5) hnk, hno (Fus.symm D h6) hnk⟩
      · obtain ⟨h3, h6⟩ := D.fus_F hnk
        exact ⟨hno (Fus.symm D h3) hnk, hnk, hno (Fus.symm D h6) hnk⟩
      · obtain ⟨h3, h5⟩ := D.fus_G hnk
        exact ⟨hno (Fus.symm D h3) hnk, hno (Fus.symm D h5) hnk, hnk⟩
    obtain ⟨h3, h5, h6⟩ := h356
    have h4 : ¬ D.FusABC 4 := by
      rcases hE with h | h | h
      · exact hno h h3
      · exact hno h h5
      · exact hno h h6
    have : j0 = 3 ∨ j0 = 4 ∨ j0 = 5 ∨ j0 = 6 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact h3 hABC0
    · exact h4 hABC0
    · exact h5 hABC0
    · exact h6 hABC0
  intro i
  by_cases hi : i.val ≤ 2
  · have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact Fus.refl D 0
    · exact hAB
    · exact hAC
  · rcases hall i (by omega) with h | h | h
    · exact Fus.symm D h
    · exact hAB.trans D (Fus.symm D h)
    · exact hAC.trans D (Fus.symm D h)

theorem oneClass [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a)
    (hgold : CFSG.Goldschmidt.CoreStatement) :
    ∀ u w : G, orderOf u = 2 → orderOf w = 2 → IsConj u w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hall := D.fus_all hna hgold
  have key : ∀ u : G, orderOf u = 2 → ∃ g : G, g * u * g⁻¹ = invRep v1 v2 v3 s t 0 := by
    intro u hu
    have hu2 : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
    have hu1 : u ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hu
      exact absurd hu (by decide)
    have hup : IsPGroup 2 (zpowers u) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, hu, pow_one])
    obtain ⟨c, -, hc⟩ := exists_conj_le_of_isSylowOf D.isSylowOf_P le_top hup
    have hcuP : c * u * c⁻¹ ∈ alpP v1 v2 v3 s t := hc u (mem_zpowers u)
    have hcu2 : c * u * c⁻¹ * (c * u * c⁻¹) = 1 := by
      calc c * u * c⁻¹ * (c * u * c⁻¹) = c * (u * u) * c⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    have hcu1 : c * u * c⁻¹ ≠ 1 := by
      intro h1
      apply hu1
      calc u = c⁻¹ * (c * u * c⁻¹) * c := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨i, d, -, hd⟩ := D.exists_inClass hcuP hcu2 hcu1
    obtain ⟨g, hg⟩ := hall i
    refine ⟨g * d * c, ?_⟩
    calc g * d * c * u * (g * d * c)⁻¹ = g * (d * (c * u * c⁻¹) * d⁻¹) * g⁻¹ := by group
      _ = g * (d * (d⁻¹ * invRep v1 v2 v3 s t i * d) * d⁻¹) * g⁻¹ := by rw [hd]
      _ = g * invRep v1 v2 v3 s t i * g⁻¹ := by group
      _ = g * (g⁻¹ * invRep v1 v2 v3 s t 0 * g) * g⁻¹ := by rw [hg]
      _ = invRep v1 v2 v3 s t 0 := by group
  intro u w hu hw
  obtain ⟨g1, h1⟩ := key u hu
  obtain ⟨g2, h2⟩ := key w hw
  rw [isConj_iff]
  refine ⟨g2⁻¹ * g1, ?_⟩
  calc g2⁻¹ * g1 * u * (g2⁻¹ * g1)⁻¹ = g2⁻¹ * (g1 * u * g1⁻¹) * g2 := by group
    _ = g2⁻¹ * (g2 * w * g2⁻¹) * g2 := by rw [h1, h2]
    _ = w := by group

end FusCtx

end CFSG.OddStandard.ONanRec
