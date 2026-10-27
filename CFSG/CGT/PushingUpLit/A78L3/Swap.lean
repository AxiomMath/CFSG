module

public import CFSG.CGT.PushingUpLit.A78L3.FieldT
public import CFSG.CGT.PushingUpLit.A78L3.Base

public section

namespace CFSG.CGT.PushingUpLit.A78L3

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.QuasithinUnique.Setup.Offender (card_eq_sq_of_involution)
open Matrix
open scoped commutatorElement

namespace L3Side

variable {G : Type} [Group G] [Finite G] {L V W T : Subgroup G} {e : ℕ} (h : L3Side G L V W T e)

include h in
theorem card_J : Nat.card ↥(V ⊔ W) = 2 ^ (3 * e) := by
  have h1 := Subgroup.relIndex_mul_card V (V ⊔ W)
  rw [inf_eq_left.2 le_sup_left, h.card_V] at h1
  have hN : W ≤ Subgroup.normalizer (V : Set G) := fun w hw =>
    mem_normalizer_of_conj_le fun v hv => h.jst.conj_V w (Subgroup.mem_sup_right hw) v hv
  have h2 := relIndex_sup_of_le_normalizer (A := V) (B := W) hN
  rw [sup_comm W V] at h2
  have h3 : V.relIndex W = 2 ^ e := by
    rw [← Subgroup.inf_relIndex_left, inf_comm]
    exact h.jst.index_V₂
  rw [← h1, h2, h3, ← pow_add]
  ring_nf

include h in
theorem sq_mem_Z {x : G} (hx : x ∈ V ⊔ W) : x * x ∈ V ⊓ W := by
  obtain ⟨v, hv, w, hw, rfl⟩ := (h.jst.mem_sup_iff).1 hx
  rw [h.jst.sq_mul hv hw]
  exact h.jst.commutator_mem hv hw

end L3Side

namespace L3Pair

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W T : Subgroup G} {e : ℕ}
  (P : L3Pair G L₁ L₂ V W T e) {D : NatCoord G L₁ V (GaloisField 2 e)}
  (fr : L3Side.Frame P.side₁ D) {s : G} (hsV : cj s V = W) (hsW : cj s W = V)
  (hss : s * s = 1)

omit [Finite G] in
include hsV in
theorem swap_V {v : G} (hv : v ∈ V) : s * v * s⁻¹ ∈ W := hsV ▸ mul_mem_cj s hv

omit [Finite G] in
include hsW in
theorem swap_W {w : G} (hw : w ∈ W) : s * w * s⁻¹ ∈ V := hsW ▸ mul_mem_cj s hw

include P hsV hsW in
theorem swap_J {j : G} (hj : j ∈ V ⊔ W) : s * j * s⁻¹ ∈ V ⊔ W := by
  obtain ⟨v, hv, w, hw, rfl⟩ := (P.side₁.jst.mem_sup_iff).1 hj
  have e1 : s * (v * w) * s⁻¹ = (s * v * s⁻¹) * (s * w * s⁻¹) := by group
  rw [e1]
  exact mul_mem (Subgroup.mem_sup_right (swap_V hsV hv))
    (Subgroup.mem_sup_left (swap_W hsW hw))

omit [Finite G] in
include hsV hsW in
theorem swap_Z {z : G} (hz : z ∈ V ⊓ W) : s * z * s⁻¹ ∈ V ⊓ W :=
  ⟨swap_W hsW hz.2, swap_V hsV hz.1⟩

include P fr hsV hsW hss in
theorem card_CJ_swap : 2 ^ e ≤ Nat.card ↥((V ⊔ W) ⊓ Subgroup.centralizer ({s} : Set G)) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hJ := P.side₁.jst
  set J := V ⊔ W with hJdef
  set C := J ⊓ Subgroup.centralizer ({s} : Set G) with hC
  set I : Finset G := Finset.univ.filter (fun y => y ∈ J ∧ s * y * s⁻¹ = y⁻¹) with hI
  have hIcard : I.card ≤ 2 ^ e * 2 ^ e := by
    have hfib : ∀ r ∈ I.image fr.b, (I.filter (fun y => fr.b y = r)).card ≤ 2 ^ e := by
      intro r hr
      obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.1 hr
      have hy₀' := (Finset.mem_filter.1 hy₀).2
      have hinj : ∀ y ∈ I.filter (fun y => fr.b y = fr.b y₀), y₀⁻¹ * y ∈ V ⊓ W := by
        intro y hy
        obtain ⟨hyI, hyb⟩ := Finset.mem_filter.1 hy
        have hy' := (Finset.mem_filter.1 hyI).2
        have hdJ : y₀⁻¹ * y ∈ J := mul_mem (inv_mem hy₀'.1) hy'.1
        have hdV : y₀⁻¹ * y ∈ V := by
          rw [fr.mem_V_iff_b hdJ, fr.b_mul (inv_mem hy₀'.1) hy'.1, fr.b_inv hy₀'.1, hyb,
            CharTwo.add_self_eq_zero]
        have hsd : s * (y₀⁻¹ * y) * s⁻¹ = y₀ * y⁻¹ := by
          calc s * (y₀⁻¹ * y) * s⁻¹ = (s * y₀ * s⁻¹)⁻¹ * (s * y * s⁻¹) := by group
            _ = y₀ * y⁻¹ := by rw [hy₀'.2, hy'.2, inv_inv]
        have hq : (y₀⁻¹ * y)⁻¹ * (y₀ * y⁻¹) ∈ V ⊓ W := by
          have hsq₀ := P.side₁.sq_mem_Z hy₀'.1
          have hsq := P.side₁.sq_mem_Z (inv_mem hy'.1)
          have hc : y⁻¹ * (y₀ * y₀) = (y₀ * y₀) * y⁻¹ :=
            (hJ.commute_of_mem_inf hsq₀ (inv_mem hy'.1)).eq.symm
          have e1 : (y₀⁻¹ * y)⁻¹ * (y₀ * y⁻¹) = (y⁻¹ * (y₀ * y₀)) * y⁻¹ := by group
          rw [e1, hc, mul_assoc]
          exact mul_mem hsq₀ hsq
        have hsdV : s * (y₀⁻¹ * y) * s⁻¹ ∈ V := by
          rw [hsd]
          have e1 : y₀ * y⁻¹ = (y₀⁻¹ * y) * ((y₀⁻¹ * y)⁻¹ * (y₀ * y⁻¹)) := by group
          rw [e1]
          exact mul_mem hdV hq.1
        have hsdW := swap_V hsV hdV
        have hsdZ : s * (y₀⁻¹ * y) * s⁻¹ ∈ V ⊓ W := ⟨hsdV, hsdW⟩
        have := swap_Z hsV hsW hsdZ
        rwa [show s * (s * (y₀⁻¹ * y) * s⁻¹) * s⁻¹ = (s * s) * (y₀⁻¹ * y) * (s * s)⁻¹ by group,
          hss, one_mul, inv_one, mul_one] at this
      have hcard : (I.filter (fun y => fr.b y = fr.b y₀)).card ≤ Nat.card ↥(V ⊓ W) := by
        rw [← Nat.card_eq_finsetCard]
        refine Nat.card_le_card_of_injective (fun y => ⟨y₀⁻¹ * y, hinj y y.2⟩) fun y y' hyy => ?_
        have := congrArg (fun z : ↥(V ⊓ W) => (z : G)) hyy
        exact Subtype.ext (mul_left_cancel this)
      rw [P.side₁.card_Z] at hcard
      exact hcard
    have h1 := Finset.card_le_mul_card_image I (2 ^ e) hfib
    have h2 : (I.image fr.b).card ≤ 2 ^ e := by
      have : Fintype (GaloisField 2 e) := Fintype.ofFinite _
      rw [← GaloisField.card 2 e P.side₁.e_ne_zero, Nat.card_eq_fintype_card]
      exact Finset.card_le_univ _
    calc I.card ≤ 2 ^ e * (I.image fr.b).card := h1
      _ ≤ 2 ^ e * 2 ^ e := Nat.mul_le_mul_left _ h2
  set Jf : Finset G := Finset.univ.filter (fun y => y ∈ J) with hJf
  let μ : G → G := fun x => x * s * x⁻¹ * s⁻¹
  have hμI : ∀ x ∈ Jf, μ x ∈ I := by
    intro x hx
    have hxJ := (Finset.mem_filter.1 hx).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩
    · have : μ x = x * (s * x⁻¹ * s⁻¹) := by simp only [μ]; group
      rw [this]
      exact mul_mem hxJ (P.swap_J hsV hsW (inv_mem hxJ))
    · simp only [μ]
      rw [hsi]
      calc s * (x * s * x⁻¹ * s) * s = s * x * s * x⁻¹ * (s * s) := by group
        _ = (x * s * x⁻¹ * s)⁻¹ := by
            rw [hss, mul_one, _root_.mul_inv_rev, _root_.mul_inv_rev, _root_.mul_inv_rev,
              inv_inv, hsi]
            group
  have hμfib : ∀ y ∈ Jf.image μ, (Jf.filter (fun x => μ x = y)).card ≤ Nat.card C := by
    intro y hy
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hy
    have hx₀J := (Finset.mem_filter.1 hx₀).2
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective (fun x => ⟨x₀⁻¹ * (x : G), ?_⟩) fun x x' hxx => ?_
    · obtain ⟨hxJf, hxμ⟩ := Finset.mem_filter.1 x.2
      have hxJ := (Finset.mem_filter.1 hxJf).2
      refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hx₀J) hxJ,
        Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      simp only [μ] at hxμ
      have e1 : x₀⁻¹ * (x : G) * s * (x₀⁻¹ * (x : G))⁻¹ = s := by
        calc x₀⁻¹ * (x : G) * s * (x₀⁻¹ * (x : G))⁻¹ =
            x₀⁻¹ * ((x : G) * s * (x : G)⁻¹ * s⁻¹) * s * x₀ := by group
          _ = x₀⁻¹ * (x₀ * s * x₀⁻¹ * s⁻¹) * s * x₀ := by rw [hxμ]
          _ = s := by group
      calc x₀⁻¹ * (x : G) * s = x₀⁻¹ * (x : G) * s * (x₀⁻¹ * (x : G))⁻¹ * (x₀⁻¹ * (x : G)) := by
            group
        _ = s * (x₀⁻¹ * (x : G)) := by rw [e1]
    · have := congrArg (fun z : ↥C => (z : G)) hxx
      exact Subtype.ext (mul_left_cancel this)
  have h3 := Finset.card_le_mul_card_image Jf (Nat.card C) hμfib
  have h4 : (Jf.image μ).card ≤ I.card := Finset.card_le_card fun y hy => by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact hμI x hx
  have hJcard : Jf.card = 2 ^ (3 * e) := by
    rw [← P.side₁.card_J, ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [hJf, hJdef])
  have h5 : 2 ^ (3 * e) ≤ Nat.card C * (2 ^ e * 2 ^ e) := by
    rw [← hJcard]
    exact h3.trans (Nat.mul_le_mul_left _ (h4.trans hIcard))
  by_contra hlt
  push Not at hlt
  have h6 : Nat.card C * (2 ^ e * 2 ^ e) < 2 ^ e * (2 ^ e * 2 ^ e) :=
    Nat.mul_lt_mul_of_pos_right hlt (by positivity)
  have h7 : 2 ^ e * (2 ^ e * 2 ^ e) = 2 ^ (3 * e) := by rw [← pow_add, ← pow_add]; ring_nf
  omega

omit [Finite G] in
theorem eq_two_pow_half {n e : ℕ} (hn : 2 ^ e = n ^ 2) : n = 2 ^ (e / 2) := by
  have hdvd : n ∣ 2 ^ e := ⟨n, by rw [hn, pow_two]⟩
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [← pow_mul] at hn
  have h1 := Nat.pow_right_injective le_rfl hn
  rw [h1]
  congr 1
  omega

include P fr hsV hsW hss in
theorem types_swap :
    (V ⊔ W) ⊓ Subgroup.centralizer ({s} : Set G) = V ⊓ W ∨
      ((∀ x ∈ (V ⊔ W) ⊓ Subgroup.centralizer ({s} : Set G), x * x = 1 → x ∈ V ⊓ W) ∧
        Nat.card ↥((V ⊓ W) ⊓ Subgroup.centralizer ({s} : Set G)) ≤ 2 ^ (e / 2)) := by
  classical
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hJ := P.side₁.jst
  choose xa hxa using fun u : GaloisField 2 e => fr.surj_ab u 0
  choose xb hxb using fun r : GaloisField 2 e => fr.surj_ab 0 r
  choose zc hzc using fun r : GaloisField 2 e => fr.c_surj r
  have hxaV : ∀ u, xa u ∈ V := fun u => (fr.mem_V_iff_b (hxa u).1).2 (hxa u).2.2
  have hxbW : ∀ r, xb r ∈ W := fun r => (fr.mem_W_iff_a (hxb r).1).2 (hxb r).2.1
  let g : GaloisField 2 e → GaloisField 2 e := fun r => fr.a (s * xb r * s⁻¹)
  let g' : GaloisField 2 e → GaloisField 2 e := fun u => fr.b (s * xa u * s⁻¹)
  let Γ : GaloisField 2 e → GaloisField 2 e := fun r => fr.c (s * zc r * s⁻¹)
  have ha1 : fr.a 1 = 0 := (fr.mem_W_iff_a (Subgroup.one_mem _)).1 (Subgroup.one_mem _)
  have hb1 : fr.b 1 = 0 := fr.b_of_mem_V (Subgroup.one_mem _)
  have ha_inv : ∀ {x : G}, x ∈ V ⊔ W → fr.a x⁻¹ = -fr.a x := fun {x} hx => by
    have := fr.a_mul hx (inv_mem hx)
    rw [mul_inv_cancel, ha1] at this
    linear_combination -this
  have hb_inv : ∀ {x : G}, x ∈ V ⊔ W → fr.b x⁻¹ = -fr.b x := fun {x} hx => by
    have := fr.b_mul hx (inv_mem hx)
    rw [mul_inv_cancel, hb1] at this
    linear_combination -this
  have hsa : ∀ x ∈ V ⊔ W, fr.a (s * x * s⁻¹) = g (fr.b x) := by
    intro x hx
    have hy : x * (xb (fr.b x))⁻¹ ∈ V ⊔ W := mul_mem hx (inv_mem (hxb _).1)
    have hyV : x * (xb (fr.b x))⁻¹ ∈ V := by
      rw [fr.mem_V_iff_b hy, fr.b_mul hx (inv_mem (hxb _).1), hb_inv (hxb _).1, (hxb _).2.2,
        add_neg_cancel]
    have e1 : s * x * s⁻¹ = (s * (x * (xb (fr.b x))⁻¹) * s⁻¹) * (s * xb (fr.b x) * s⁻¹) := by
      group
    rw [e1, fr.a_mul (Subgroup.mem_sup_right (swap_V hsV hyV))
      (P.swap_J hsV hsW (hxb _).1),
      (fr.mem_W_iff_a (Subgroup.mem_sup_right (swap_V hsV hyV))).1 (swap_V hsV hyV), zero_add]
  have hsb : ∀ x ∈ V ⊔ W, fr.b (s * x * s⁻¹) = g' (fr.a x) := by
    intro x hx
    have hy : x * (xa (fr.a x))⁻¹ ∈ V ⊔ W := mul_mem hx (inv_mem (hxa _).1)
    have hyW : x * (xa (fr.a x))⁻¹ ∈ W := by
      rw [fr.mem_W_iff_a hy, fr.a_mul hx (inv_mem (hxa _).1), ha_inv (hxa _).1, (hxa _).2.1,
        add_neg_cancel]
    have e1 : s * x * s⁻¹ = (s * (x * (xa (fr.a x))⁻¹) * s⁻¹) * (s * xa (fr.a x) * s⁻¹) := by
      group
    rw [e1, fr.b_mul (Subgroup.mem_sup_left (swap_W hsW hyW))
      (P.swap_J hsV hsW (hxa _).1), fr.b_of_mem_V (swap_W hsW hyW), zero_add]
  have hsc : ∀ z ∈ V ⊓ W, fr.c (s * z * s⁻¹) = Γ (fr.c z) := by
    intro z hz
    have : zc (fr.c z) = z := fr.c_inj (hzc _).1 hz (hzc _).2
    show fr.c (s * z * s⁻¹) = fr.c (s * zc (fr.c z) * s⁻¹)
    rw [this]
  have hg0 : g 0 = 0 := by
    have hz : xb 0 ∈ V ⊓ W := ⟨(fr.mem_V_iff_b (hxb 0).1).2 (hxb 0).2.2, hxbW 0⟩
    exact (fr.mem_W_iff_a (Subgroup.mem_sup_right (swap_Z hsV hsW hz).2)).1
      (swap_Z hsV hsW hz).2
  have hg'0 : g' 0 = 0 := by
    have hz : xa 0 ∈ V ⊓ W := ⟨hxaV 0, (fr.mem_W_iff_a (hxa 0).1).2 (hxa 0).2.1⟩
    exact fr.b_of_mem_V (swap_Z hsV hsW hz).1
  have hΓadd : ∀ x y, Γ (x + y) = Γ x + Γ y := by
    intro x y
    have h1 : zc (x + y) = zc x * zc y :=
      fr.c_inj (hzc (x + y)).1 (mul_mem (hzc x).1 (hzc y).1)
        (by rw [fr.c_mul (hzc x).1 (hzc y).1, (hzc x).2, (hzc y).2, (hzc (x + y)).2])
    show fr.c (s * zc (x + y) * s⁻¹) = fr.c (s * zc x * s⁻¹) + fr.c (s * zc y * s⁻¹)
    rw [h1, show s * (zc x * zc y) * s⁻¹ = (s * zc x * s⁻¹) * (s * zc y * s⁻¹) by group,
      fr.c_mul (swap_Z hsV hsW (hzc x).1) (swap_Z hsV hsW (hzc y).1)]
  have hΓinj : Function.Injective Γ := by
    intro x y hxy
    have h1 := fr.c_inj (swap_Z hsV hsW (hzc x).1) (swap_Z hsV hsW (hzc y).1) hxy
    have h2 : zc x = zc y := by
      have := congrArg (fun z => s⁻¹ * z * s) h1
      simpa [mul_assoc] using this
    rw [← (hzc x).2, ← (hzc y).2, h2]
  have hmul : ∀ u r, Γ (u * r) = g' u * g r := by
    intro u r
    have hy := (hxa u).1
    have hx := (hxb r).1
    have hcz : ⁅xa u, xb r⁆ ∈ V ⊓ W := hJ.commutator_mem (hxaV u) (hxbW r)
    have h1 := fr.c_comm_J hy hx
    rw [(hxa u).2.1, (hxa u).2.2, (hxb r).2.1, (hxb r).2.2, mul_zero, add_zero] at h1
    have e1 : s * ⁅xa u, xb r⁆ * s⁻¹ = ⁅s * xa u * s⁻¹, s * xb r * s⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    have h2 := fr.c_comm_J (P.swap_J hsV hsW hy) (P.swap_J hsV hsW hx)
    rw [hsa _ hy, hsb _ hx, hsa _ hx, hsb _ hy, (hxa u).2.2, (hxb r).2.1, hg0, zero_mul,
      zero_add, (hxb r).2.2, (hxa u).2.1] at h2
    rw [← h1, ← hsc _ hcz, e1, h2, mul_comm]
  obtain ⟨τ, hτg', hτg, hτΓ, hg'1, hg1⟩ := exists_ringEquiv_of_mul hΓadd hΓinj hmul
  have hgg : ∀ u, g (g' u) = u := by
    intro u
    have h1 := hsa _ (P.swap_J hsV hsW (hxa u).1)
    rw [hsb _ (hxa u).1, (hxa u).2.1,
      show s * (s * xa u * s⁻¹) * s⁻¹ = (s * s) * xa u * (s * s)⁻¹ by group, hss, one_mul,
      inv_one, mul_one, (hxa u).2.1] at h1
    exact h1.symm
  have hk : g 1 * τ (g' 1) = 1 := by
    have := hgg 1
    rw [hτg (g' 1), hτg' 1, map_mul] at this
    simpa only [map_one, mul_one] using this
  have hττ : ∀ u, τ (τ u) = u := by
    intro u
    have h1 := hgg u
    rw [hτg (g' u), hτg' u, map_mul, ← mul_assoc, hk, one_mul] at h1
    exact h1
  have hCb : ∀ x ∈ (V ⊔ W) ⊓ Subgroup.centralizer ({s} : Set G), fr.b x = g' (fr.a x) := by
    intro x hx
    have hxs : s * x * s⁻¹ = x := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hx.2
      calc s * x * s⁻¹ = x * s * s⁻¹ := by rw [this]
        _ = x := by group
    have := hsb x hx.1
    rwa [hxs] at this
  by_cases hτ1 : τ = 1
  ·
    left
    have hτid : ∀ u, τ u = u := fun u => by rw [hτ1]; rfl
    have hg'g : g' 1 * g 1 = 1 := by
      have := hk
      rw [hτid] at this
      rw [mul_comm]
      exact this
    have hsZ : ∀ z ∈ V ⊓ W, s * z * s⁻¹ = z := by
      intro z hz
      refine fr.c_inj (swap_Z hsV hsW hz) hz ?_
      rw [hsc z hz, hτΓ, hg'g, one_mul, hτid]
    apply le_antisymm
    · intro x hx
      have hxJ := hx.1
      have hxs : s * x * s⁻¹ = x := by
        have := Subgroup.mem_centralizer_singleton_iff.1 hx.2
        calc s * x * s⁻¹ = x * s * s⁻¹ := by rw [this]
          _ = x := by group
      set v := xa (fr.a x) with hv
      have hvV := hxaV (fr.a x)
      have hsv := swap_V hsV hvV
      have hvJ : v ∈ V ⊔ W := Subgroup.mem_sup_left hvV
      have hsvJ : s * v * s⁻¹ ∈ V ⊔ W := Subgroup.mem_sup_right hsv
      set z' := (v * (s * v * s⁻¹))⁻¹ * x with hz'
      have hz'J : z' ∈ V ⊔ W := mul_mem (inv_mem (mul_mem hvJ hsvJ)) hxJ
      have hz'Z : z' ∈ V ⊓ W := by
        have ha' : fr.a z' = 0 := by
          rw [hz', fr.a_mul (inv_mem (mul_mem hvJ hsvJ)) hxJ, ha_inv (mul_mem hvJ hsvJ),
            fr.a_mul hvJ hsvJ, (fr.mem_W_iff_a hsvJ).1 hsv, (hxa _).2.1]
          ring
        have hb' : fr.b z' = 0 := by
          rw [hz', fr.b_mul (inv_mem (mul_mem hvJ hsvJ)) hxJ, hb_inv (mul_mem hvJ hsvJ),
            fr.b_mul hvJ hsvJ, fr.b_of_mem_V hvV, hsb _ hvJ, (hxa _).2.1, hCb x hx]
          ring
        exact ⟨(fr.mem_V_iff_b hz'J).2 hb', (fr.mem_W_iff_a hz'J).2 ha'⟩
      have hxdec : x = v * (s * v * s⁻¹) * z' := by rw [hz']; group
      have hcomm : v * (s * v * s⁻¹) = (s * v * s⁻¹) * v := by
        have h1 : s * x * s⁻¹ = (s * v * s⁻¹) * v * z' := by
          rw [hxdec]
          calc s * (v * (s * v * s⁻¹) * z') * s⁻¹ =
              (s * v * s⁻¹) * ((s * s) * v * (s * s)⁻¹) * (s * z' * s⁻¹) := by
                group
            _ = (s * v * s⁻¹) * v * z' := by rw [hss, one_mul, inv_one, mul_one, hsZ z' hz'Z]
        rw [hxs, hxdec] at h1
        exact mul_right_cancel h1
      have hc : fr.c ⁅v, s * v * s⁻¹⁆ = 0 := by
        rw [commutatorElement_eq_one_iff_mul_comm.2 hcomm, fr.c_one]
      rw [fr.c_comm_J hvJ hsvJ, (fr.mem_W_iff_a hsvJ).1 hsv, zero_mul, add_zero, hsb _ hvJ,
        hτg', hτid] at hc
      have ha0 : fr.a v = 0 := by
        have : fr.a v * (g' 1 * fr.a v) = 0 := hc
        rcases mul_eq_zero.1 this with h0 | h0
        · exact h0
        · rcases mul_eq_zero.1 h0 with h0 | h0
          · exact absurd h0 hg'1
          · exact h0
      have hvZ : v ∈ V ⊓ W := ⟨hvV, (fr.mem_W_iff_a hvJ).2 ha0⟩
      rw [hxdec]
      exact mul_mem (mul_mem hvZ (swap_Z hsV hsW hvZ)) hz'Z
    · intro z hz
      refine ⟨Subgroup.mem_sup_left hz.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have := hsZ z hz
      calc z * s = s * z * s⁻¹ * s := by rw [this]
        _ = s * z := by group
  ·
    right
    refine ⟨fun x hx hxx => ?_, ?_⟩
    · have h1 := fr.c_sq hx.1
      rw [hxx, fr.c_one, hCb x hx, hτg'] at h1
      have ha0 : fr.a x = 0 := by
        rcases mul_eq_zero.1 h1.symm with h0 | h0
        · exact h0
        · rcases mul_eq_zero.1 h0 with h0 | h0
          · exact absurd h0 hg'1
          · exact (map_eq_zero_iff τ τ.injective).1 h0
      have hb0 : fr.b x = 0 := by rw [hCb x hx, ha0, hg'0]
      exact ⟨(fr.mem_V_iff_b hx.1).2 hb0, (fr.mem_W_iff_a hx.1).2 ha0⟩
    ·
      have hτ2 : τ * τ = 1 := RingEquiv.ext fun u => hττ u
      obtain ⟨n, hn, -, hfix⟩ := card_eq_sq_of_involution τ hτ1 hτ2
      rw [GaloisField.card 2 e P.side₁.e_ne_zero] at hn
      have hn' := eq_two_pow_half hn
      calc Nat.card ↥((V ⊓ W) ⊓ Subgroup.centralizer ({s} : Set G))
          ≤ Nat.card {r : GaloisField 2 e // (g' 1 * g 1) * τ r = r} := by
            refine Nat.card_le_card_of_injective (fun z => ⟨fr.c z, ?_⟩) fun z z' hzz => ?_
            · have hz := z.2
              have hzs : s * z * s⁻¹ = z := by
                have := Subgroup.mem_centralizer_singleton_iff.1 hz.2
                calc s * (z : G) * s⁻¹ = z * s * s⁻¹ := by rw [this]
                  _ = z := by group
              rw [← hτΓ, ← hsc _ hz.1, hzs]
            · have := congrArg (fun r : {r : GaloisField 2 e // (g' 1 * g 1) * τ r = r} => r.1) hzz
              exact Subtype.ext (fr.c_inj z.2.1 z'.2.1 this)
        _ ≤ Nat.card {c : GaloisField 2 e // τ c = c} := card_fix_le τ _
        _ = 2 ^ (e / 2) := by rw [hfix, hn']

end L3Pair

end CFSG.CGT.PushingUpLit.A78L3
