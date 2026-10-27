module

public import CFSG.HardMathSupport.Lang.E6Descent.MaxClassAbelian

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Walter.W67
open scoped commutatorElement

universe u

theorem comm_delta_eq_one {G : Type*} [Group G] (a : G) (A : Subgroup G) [A.Normal]
    (hZ : ∀ p ∈ A, ∀ q ∈ A, ⁅p, q⁆ ∈ Subgroup.center G)
    (hN : ∀ w ∈ A, (a * (a * w * a⁻¹) * a⁻¹) * (a * w * a⁻¹) * w = 1) :
    ∀ u ∈ A, ∀ v ∈ A, ⁅⁅a, v⁆, u⁆ = 1 := by
  intro u hu v hv
  have cen : ∀ z ∈ Subgroup.center G, ∀ g : G, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.mp hz g
  have hconj : ∀ z ∈ Subgroup.center G, ∀ g : G, g * z * g⁻¹ = z := by
    intro z hz g; rw [cen z hz g]; group
  have hprod : ∀ (g1 g2 g3 h1 h2 h3 c1 c2 : G), (∀ g, g * c1 = c1 * g) → (∀ g, g * c2 = c2 * g) →
      c1 = ⁅h1, g2⁆ → c2 = ⁅h1 * h2, g3⁆ →
      (g1 * h1) * (g2 * h2) * (g3 * h3) = c1 * c2 * ((g1 * g2 * g3) * (h1 * h2 * h3)) := by
    intro g1 g2 g3 h1 h2 h3 c1 c2 hc1 hc2 e1 e2
    have e1' : h1 * g2 = c1 * (g2 * h1) := by rw [e1, commutatorElement_def]; group
    have e2' : h1 * h2 * g3 = c2 * (g3 * (h1 * h2)) := by rw [e2, commutatorElement_def]; group
    calc (g1 * h1) * (g2 * h2) * (g3 * h3)
        = g1 * (h1 * g2) * h2 * g3 * h3 := by group
      _ = g1 * (c1 * (g2 * h1)) * h2 * g3 * h3 := by rw [e1']
      _ = c1 * (g1 * g2 * (h1 * h2 * g3) * h3) := by
          have := hc1 g1
          calc g1 * (c1 * (g2 * h1)) * h2 * g3 * h3 = (g1 * c1) * (g2 * h1) * h2 * g3 * h3 := by group
            _ = (c1 * g1) * (g2 * h1) * h2 * g3 * h3 := by rw [this]
            _ = c1 * (g1 * g2 * (h1 * h2 * g3) * h3) := by group
      _ = c1 * (g1 * g2 * (c2 * (g3 * (h1 * h2))) * h3) := by rw [e2']
      _ = c1 * c2 * ((g1 * g2 * g3) * (h1 * h2 * h3)) := by
          have := hc2 (g1 * g2)
          calc c1 * (g1 * g2 * (c2 * (g3 * (h1 * h2))) * h3)
              = c1 * ((g1 * g2) * c2 * (g3 * (h1 * h2)) * h3) := by group
            _ = c1 * (c2 * (g1 * g2) * (g3 * (h1 * h2)) * h3) := by rw [this]
            _ = c1 * c2 * ((g1 * g2 * g3) * (h1 * h2 * h3)) := by group
  obtain ⟨u1, hu1⟩ : ∃ u1, u1 = a * u * a⁻¹ := ⟨_, rfl⟩
  obtain ⟨u2, hu2⟩ : ∃ u2, u2 = a * u1 * a⁻¹ := ⟨_, rfl⟩
  obtain ⟨v1, hv1⟩ : ∃ v1, v1 = a * v * a⁻¹ := ⟨_, rfl⟩
  obtain ⟨v2, hv2⟩ : ∃ v2, v2 = a * v1 * a⁻¹ := ⟨_, rfl⟩
  have hu1A : u1 ∈ A := by rw [hu1]; exact Subgroup.Normal.conj_mem inferInstance u hu a
  have hv1A : v1 ∈ A := by rw [hv1]; exact Subgroup.Normal.conj_mem inferInstance v hv a
  have hu2A : u2 ∈ A := by rw [hu2]; exact Subgroup.Normal.conj_mem inferInstance u1 hu1A a
  have hv2A : v2 ∈ A := by rw [hv2]; exact Subgroup.Normal.conj_mem inferInstance v1 hv1A a
  have hNu : u2 * u1 * u = 1 := by rw [hu2, hu1]; exact hN u hu
  have hNv : v2 * v1 * v = 1 := by rw [hv2, hv1]; exact hN v hv
  have huv : u * v ∈ A := A.mul_mem hu hv
  have hS : (u2 * v2) * (u1 * v1) * (u * v) = 1 := by
    have := hN _ huv
    rw [← this, hu2, hu1, hv2, hv1]; group
  have hc1 := hZ v2 hv2A u1 hu1A
  have hc2 := hZ (v2 * v1) (A.mul_mem hv2A hv1A) u hu
  rw [hprod u2 u1 u v2 v1 v ⁅v2, u1⁆ ⁅v2 * v1, u⁆ (cen _ hc1) (cen _ hc2) rfl rfl, hNu, hNv,
    mul_one, mul_one] at hS
  have hv21 : v2 * v1 = v⁻¹ := eq_inv_of_mul_eq_one_left hNv
  rw [hv21] at hS hc2
  have hc1' : ⁅v2, u1⁆ = ⁅v1, u⁆ := by
    have h : ⁅v2, u1⁆ = a * ⁅v1, u⁆ * a⁻¹ := by
      rw [hv2, hu1]; simp only [commutatorElement_def]; group
    rw [h]; exact hconj _ (hZ v1 hv1A u hu) a
  rw [hc1'] at hS
  have hzz := hZ v⁻¹ (A.inv_mem hv) u hu
  have hz1 := hZ v1 hv1A u hu
  have hid : ⁅a, v⁆ = v1 * v⁻¹ := by rw [hv1, commutatorElement_def]
  rw [hid]
  have hmulc : ⁅v1 * v⁻¹, u⁆ = v1 * ⁅v⁻¹, u⁆ * v1⁻¹ * ⁅v1, u⁆ := by
    simp only [commutatorElement_def]; group
  rw [hmulc, hconj _ hzz v1]
  rw [← hS]
  exact (cen _ hz1 _).symm ▸ rfl

theorem surj_comm {G : Type*} [Group G] [Finite G] (a : G) (B T : Subgroup G)
    (hT : ∀ b ∈ B, ⁅a, b⁆ ∈ T)
    (hcard : Nat.card T * Nat.card (B ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) ≤
      Nat.card B) :
    ∀ t ∈ T, ∃ b ∈ B, ⁅a, b⁆ = t := by
  set C : Subgroup G := B ⊓ Subgroup.centralizer ({a} : Set G) with hC
  have hCB : C ≤ B := inf_le_left
  let C' : Subgroup B := C.subgroupOf B
  have hC'card : Nat.card C' = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCB).toEquiv
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup C'
  have key : ∀ b b' : B, b⁻¹ * b' ∈ C' → ⁅a, (b : G)⁆ = ⁅a, (b' : G)⁆ := by
    intro b b' h
    have h' : (b : G)⁻¹ * (b' : G) ∈ C := h
    have hcomm : (b : G)⁻¹ * b' ∈ Subgroup.centralizer ({a} : Set G) := h'.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hcomm
    set c : G := (b : G)⁻¹ * b' with hc
    have hca : c * a = a * c := hcomm
    have h1 : a⁻¹ * c = c * a⁻¹ := by
      calc a⁻¹ * c = a⁻¹ * c * a * a⁻¹ := by group
        _ = a⁻¹ * (c * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * c) * a⁻¹ := by rw [hca]
        _ = c * a⁻¹ := by group
    have e : (b' : G) = b * c := by rw [hc]; group
    rw [e]
    simp only [commutatorElement_def]
    calc a * (b : G) * a⁻¹ * (b : G)⁻¹ = a * b * (a⁻¹ * c) * c⁻¹ * (b : G)⁻¹ := by group
      _ = a * b * (c * a⁻¹) * c⁻¹ * (b : G)⁻¹ := by rw [h1]
      _ = a * (b * c) * a⁻¹ * (b * c)⁻¹ := by group
  let F : B ⧸ C' → T := fun q => Quotient.liftOn' q
    (fun b => (⟨⁅a, (b : G)⁆, hT b b.2⟩ : T)) (fun b b' h => by
      apply Subtype.ext
      apply key
      exact (QuotientGroup.leftRel_apply.mp h))
  have hFinj : Function.Injective F := by
    intro q q' hq
    induction q using Quotient.inductionOn' with | _ b =>
    induction q' using Quotient.inductionOn' with | _ b' =>
    have hE : ⁅a, (b : G)⁆ = ⁅a, (b' : G)⁆ := congrArg Subtype.val hq
    apply Quotient.sound'
    apply QuotientGroup.leftRel_apply.mpr
    show (b : G)⁻¹ * b' ∈ C
    refine ⟨(b⁻¹ * b').2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    simp only [commutatorElement_def] at hE
    have E' : a * ((b : G) * a⁻¹ * (b : G)⁻¹) = a * ((b' : G) * a⁻¹ * (b' : G)⁻¹) := by
      calc a * ((b : G) * a⁻¹ * (b : G)⁻¹) = a * (b : G) * a⁻¹ * (b : G)⁻¹ := by group
        _ = a * (b' : G) * a⁻¹ * (b' : G)⁻¹ := hE
        _ = a * ((b' : G) * a⁻¹ * (b' : G)⁻¹) := by group
    have E'' := mul_left_cancel E'
    have E3 : (b : G) * a * (b : G)⁻¹ = (b' : G) * a * (b' : G)⁻¹ := by
      have := congrArg (fun x => x⁻¹) E''
      simpa [mul_assoc] using this
    calc ((b : G)⁻¹ * b') * a = (b : G)⁻¹ * ((b' : G) * a * (b' : G)⁻¹) * b' := by group
      _ = (b : G)⁻¹ * ((b : G) * a * (b : G)⁻¹) * b' := by rw [E3]
      _ = a * ((b : G)⁻¹ * b') := by group
  have hTle : Nat.card T ≤ Nat.card (B ⧸ C') := by
    have hpos : 0 < Nat.card C := Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Nat.card T * Nat.card C ≤ Nat.card B := hcard
      _ = Nat.card (B ⧸ C') * Nat.card C' := hmul
      _ = Nat.card (B ⧸ C') * Nat.card C := by rw [hC'card]
  have hbij := hFinj.bijective_of_nat_card_le hTle
  intro t ht
  obtain ⟨q, hq⟩ := hbij.2 ⟨t, ht⟩
  induction q using Quotient.inductionOn' with | _ b =>
  exact ⟨b, b.2, congrArg Subtype.val hq⟩

theorem exists_decomp_grp {G : Type*} [Group G] [Finite G] {H₁ H₂ : Subgroup G} [H₂.Normal]
    (hle : H₂ ≤ H₁) (hcard : Nat.card H₁ = 3 * Nat.card H₂) {z : G} (hz1 : z ∈ H₁)
    (hz2 : z ∉ H₂) : ∀ u ∈ H₁, ∃ k : ℤ, ∃ h ∈ H₂, u = z ^ k * h := by
  set K : Subgroup G := Subgroup.zpowers z ⊔ H₂ with hK
  have hKle : K ≤ H₁ := sup_le (Subgroup.zpowers_le.mpr hz1) hle
  have hH₂K : H₂ ≤ K := le_sup_right
  have hd1 : Nat.card H₂ ∣ Nat.card K := Subgroup.card_dvd_of_le hH₂K
  have hd2 : Nat.card K ∣ Nat.card H₁ := Subgroup.card_dvd_of_le hKle
  have hpos : 0 < Nat.card H₂ := Nat.card_pos
  obtain ⟨t, ht⟩ := hd1
  rw [ht, hcard] at hd2
  have ht3 : t ∣ 3 := by
    exact Nat.dvd_of_mul_dvd_mul_left hpos (by simpa [mul_comm] using hd2 : Nat.card H₂ * t ∣
      Nat.card H₂ * 3)
  have hKne : K ≠ H₂ := by
    intro h
    apply hz2
    rw [← h]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
  have ht1 : t ≠ 1 := by
    intro h1
    apply hKne
    refine (Subgroup.eq_of_le_of_card_ge hH₂K ?_).symm
    rw [ht, h1]; simp
  have ht3' : t = 3 := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd t ht3 with h | h
    · exact absurd h ht1
    · exact h
  have hKH : K = H₁ := Subgroup.eq_of_le_of_card_ge hKle (by rw [ht, ht3', hcard, mul_comm])
  intro u hu
  rw [← hKH, hK, Subgroup.mem_sup_of_normal_right] at hu
  obtain ⟨a, ha, b, hb, rfl⟩ := hu
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  exact ⟨k, b, hb, rfl⟩

namespace MB

variable {P : Type u} [Group P] [Finite P] (d : MB P)

include d

theorem L_le_normal_gen {N : Subgroup P} [N.Normal] {r : ℕ} (hr2 : 2 ≤ r) (hrm : r ≤ d.m - 2)
    (hN : Nat.card N = 3 ^ r) : d.L (d.m - r - 1) ≤ N := by
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hQ : Nat.card (P ⧸ N) = 3 ^ (d.m - r) := by
    have : 3 ^ d.m = 3 ^ (d.m - r) * 3 ^ r := by
      rw [← pow_add]; congr 1; omega
    rw [hN, d.hcard, this] at hmul
    exact (Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) _) hmul).symm
  have h1 := lcs_eq_bot_of_card (p := 3) (d.m - r) (P ⧸ N) (d.hP.to_quotient N) hQ (by omega)
  exact lcs_le_of_quotient_eq_bot N h1

theorem comm_mem_center_iff (x g : P) :
    ⁅x, g⁆ ∈ Subgroup.center P ↔ (x : P ⧸ Subgroup.center P) * (g : P ⧸ Subgroup.center P) =
      (g : P ⧸ Subgroup.center P) * (x : P ⧸ Subgroup.center P) := by
  rw [← QuotientGroup.eq_one_iff]
  have h1 : ((⁅x, g⁆ : P) : P ⧸ Subgroup.center P) =
      ⁅(x : P ⧸ Subgroup.center P), (g : P ⧸ Subgroup.center P)⁆ := by
    have := map_commutatorElement (QuotientGroup.mk' (Subgroup.center P)) x g
    simpa only [QuotientGroup.mk'_apply] using this
  rw [h1, commutatorElement_eq_one_iff_mul_comm]

def Dp : Subgroup P :=
  (Subgroup.centralizer (((d.L (d.m - 4)).map (QuotientGroup.mk' (Subgroup.center P)) :
    Subgroup (P ⧸ Subgroup.center P)) : Set (P ⧸ Subgroup.center P))).comap
    (QuotientGroup.mk' (Subgroup.center P))

theorem mem_Dp {g : P} : g ∈ d.Dp ↔ ∀ w ∈ d.L (d.m - 4), ⁅g, w⁆ ∈ Subgroup.center P := by
  rw [Dp, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  constructor
  · intro h w hw
    rw [d.comm_mem_center_iff]
    have := h _ (Subgroup.mem_map_of_mem _ hw)
    simpa only [QuotientGroup.mk'_apply] using this.symm
  · rintro h _ ⟨w, hw, rfl⟩
    have := (d.comm_mem_center_iff g w).mp (h w hw)
    simpa only [QuotientGroup.mk'_apply] using this.symm

theorem Dp_ne_top : d.Dp ≠ ⊤ := by
  intro htop
  have hm := d.hm
  have hle : d.L (d.m - 3) ≤ Subgroup.center P := by
    show (⊤ : Subgroup P).lowerCentralSeries (d.m - 3) ≤ _
    rw [show d.m - 3 = d.m - 4 + 1 by omega, Subgroup.lowerCentralSeries_succ, Subgroup.commutator_le]
    intro w hw g _
    have hg : g ∈ d.Dp := by rw [htop]; trivial
    rw [d.mem_Dp] at hg
    have := hg w hw
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ this
  have hd := Subgroup.card_dvd_of_le hle
  rw [d.card_H, d.card_center] at hd
  omega

variable (hAZ : ∀ p ∈ d.L 1, ∀ q ∈ d.L 1, ⁅p, q⁆ ∈ Subgroup.center P)

include hAZ

theorem not_mem_L1_of_not_mem_Dp {a : P} (ha : a ∉ d.Dp) : a ∉ d.L 1 := by
  intro h
  apply ha
  rw [d.mem_Dp]
  intro w hw
  exact hAZ a h w (d.L_anti (by have := d.hm; omega) hw)

omit hAZ in
def Kp (a : P) : Subgroup P :=
  d.L 1 ⊓ (Subgroup.centralizer ({(a : P ⧸ Subgroup.center P)} : Set (P ⧸ Subgroup.center P))).comap
    (QuotientGroup.mk' (Subgroup.center P))

omit hAZ in
theorem mem_Kp {a u : P} : u ∈ d.Kp a ↔ u ∈ d.L 1 ∧ ⁅a, u⁆ ∈ Subgroup.center P := by
  rw [Kp, Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
    d.comm_mem_center_iff]
  simp only [QuotientGroup.mk'_apply]
  exact and_congr_right fun _ => eq_comm

theorem Kp_normal (a : P) : (d.Kp a).Normal := by
  constructor
  intro u hu g
  rw [d.mem_Kp] at hu ⊢
  obtain ⟨huA, huz⟩ := hu
  refine ⟨(d.L_normal 1).conj_mem u huA g, ?_⟩
  have hc : ⁅g⁻¹, a⁆ ∈ d.L 1 := d.comm_mem_L1 _ _
  have hcen : ∀ z ∈ Subgroup.center P, ∀ h : P, h * z * h⁻¹ = z := by
    intro z hz h; rw [Subgroup.mem_center_iff.mp hz h]; group
  have key : ⁅a, g * u * g⁻¹⁆ =
      g * (⁅g⁻¹, a⁆ * ⁅a, u⁆ * ⁅g⁻¹, a⁆⁻¹ * ⁅⁅g⁻¹, a⁆, u⁆) * g⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [key]
  have h1 : ⁅g⁻¹, a⁆ * ⁅a, u⁆ * ⁅g⁻¹, a⁆⁻¹ = ⁅a, u⁆ := hcen _ huz _
  rw [h1]
  have h2 := hAZ _ hc u huA
  have hz := (Subgroup.center P).mul_mem huz h2
  rw [hcen _ hz g]
  exact hz

theorem Kp_eq_H {a : P} (haD : ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a) (haD' : a ∉ d.Dp) :
    d.Kp a = d.L (d.m - 3) := by
  have hm := d.hm
  haveI : (d.Kp a).Normal := d.Kp_normal hAZ a
  have hHK : d.L (d.m - 3) ≤ d.Kp a := by
    intro w hw
    rw [d.mem_Kp]
    refine ⟨d.L_anti (by omega) hw, ?_⟩
    have h1 := d.comm_mem_L hw a
    rw [show d.m - 3 + 1 = d.m - 2 by omega, d.L_center] at h1
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ h1
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp (d.hP.to_subgroup (d.Kp a))
  have hKA : d.Kp a ≤ d.L 1 := inf_le_left
  have hdvd := Subgroup.card_dvd_of_le hKA
  rw [hr, d.card_L (j := 1) le_rfl (by omega)] at hdvd
  have hrm : r ≤ d.m - 1 - 1 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  have hr2 : r ≤ 2 := by
    by_contra h3
    push Not at h3
    have hle := d.L_le_normal_gen (N := d.Kp a) (r := r) (by omega) (by omega) hr
    apply haD'
    rw [d.mem_Dp]
    intro w hw
    have hw' : w ∈ d.Kp a := hle (d.L_anti (by omega) hw)
    exact ((d.mem_Kp).mp hw').2
  refine (Subgroup.eq_of_le_of_card_ge hHK ?_).symm
  rw [hr, d.card_H]
  calc 3 ^ r ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hr2
    _ = 9 := by norm_num

theorem fixed_center {a : P} (haD : ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a) (haD' : a ∉ d.Dp) :
    ∀ u ∈ d.L 1, a * u * a⁻¹ = u → u ∈ Subgroup.center P := by
  have hm := d.hm
  intro u hu hau
  have huK : u ∈ d.Kp a := by
    rw [d.mem_Kp]
    refine ⟨hu, ?_⟩
    have : ⁅a, u⁆ = 1 := by rw [commutatorElement_def, hau]; group
    rw [this]; exact (Subgroup.center P).one_mem
  rw [d.Kp_eq_H hAZ haD haD'] at huK
  set C : Subgroup P := d.L (d.m - 3) ⊓ Subgroup.centralizer ({a} : Set P) with hC
  have hZC : Subgroup.center P ≤ C := by
    refine le_inf ?_ ?_
    · rw [← d.L_center]; exact d.L_anti (by omega)
    · intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_center_iff.mp hz a).symm
  have hCH : C ≤ d.L (d.m - 3) := inf_le_left
  have hd := Subgroup.card_dvd_of_le hCH
  rw [d.card_H] at hd
  have hne9 : Nat.card C ≠ 9 := by
    intro h9
    obtain ⟨w, hw, hne⟩ := haD
    have hCeq : C = d.L (d.m - 3) :=
      Subgroup.eq_of_le_of_card_ge hCH (by rw [h9, d.card_H])
    have : w ∈ C := by rw [hCeq]; exact hw
    exact hne (Subgroup.mem_centralizer_singleton_iff.mp this.2).symm
  have hcard3 : Nat.card C ≤ 3 := by
    have : Nat.card C ∣ 3 ^ 2 := by simpa using hd
    rcases (Nat.dvd_prime_pow Nat.prime_three).mp this with ⟨k, hk, hk'⟩
    interval_cases k
    · rw [hk']; norm_num
    · rw [hk']; norm_num
    · exact absurd (by rw [hk']; norm_num) hne9
  have hCZ : C = Subgroup.center P := (Subgroup.eq_of_le_of_card_ge hZC (by
    rw [d.card_center]; exact hcard3)).symm
  have huC : u ∈ C := by
    refine ⟨huK, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc u * a = (a * u * a⁻¹) * a := by rw [hau]
      _ = a * u := by group
  rw [hCZ] at huC
  exact huC

theorem cube_center {a : P} (haD : ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a) (haD' : a ∉ d.Dp) :
    a ^ 3 ∈ Subgroup.center P :=
  d.fixed_center hAZ haD haD' _ (d.pow_three_mem_L1 a) (by group)

theorem card_L1_inf_cent_le {a : P} (haD : ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a) (haD' : a ∉ d.Dp) :
    Nat.card (d.L 1 ⊓ Subgroup.centralizer ({a} : Set P) : Subgroup P) ≤ 3 := by
  have hle : (d.L 1 ⊓ Subgroup.centralizer ({a} : Set P) : Subgroup P) ≤ Subgroup.center P := by
    intro u hu
    refine d.fixed_center hAZ haD haD' u hu.1 ?_
    have := Subgroup.mem_centralizer_singleton_iff.mp hu.2
    calc a * u * a⁻¹ = u * a * a⁻¹ := by rw [← this]
      _ = u := by group
  have hd := Subgroup.card_dvd_of_le hle
  rw [d.card_center] at hd
  exact Nat.le_of_dvd (by norm_num) hd

theorem comm_onto_L2 {a : P} (haD : ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a) (haD' : a ∉ d.Dp) :
    ∀ l ∈ d.L 2, ∃ u ∈ d.L 1, ⁅a, u⁆ = l := by
  have hm := d.hm
  refine surj_comm a (d.L 1) (d.L 2) ?_ ?_
  · intro b hb
    have := d.comm_mem_L (j := 1) hb a
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ this
  · have h1 := d.card_L (j := 1) le_rfl (by omega)
    have h2 := d.card_L (j := 2) (by omega) (by omega)
    have hC := d.card_L1_inf_cent_le hAZ haD haD'
    have hexp : 3 ^ (d.m - 1 - 1) = 3 ^ (d.m - 1 - 2) * 3 := by
      rw [← pow_succ]; congr 1; omega
    rw [h1, h2, hexp]
    exact Nat.mul_le_mul_left _ hC

omit hAZ in
def Ta (a : P) : Subgroup P :=
  (Subgroup.centralizer ({(a : P ⧸ d.L 2)} : Set (P ⧸ d.L 2))).comap (QuotientGroup.mk' (d.L 2))

omit hAZ in
theorem mem_Ta {a g : P} : g ∈ d.Ta a ↔ ⁅a, g⁆ ∈ d.L 2 := by
  rw [Ta, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, d.comm_mem_L2_iff]
  simp only [QuotientGroup.mk'_apply]
  exact eq_comm

omit hAZ in
theorem Ta_ne_top {a : P} (ha : a ∉ d.L 1) : d.Ta a ≠ ⊤ := by
  intro h
  apply ha
  apply d.mem_L1_of_comm_L2
  intro g
  exact (d.mem_Ta).mp (by rw [h]; trivial)

theorem card_cent_le_nine {a : P} (haD : ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a) (haD' : a ∉ d.Dp) :
    Nat.card (Subgroup.centralizer ({a} : Set P)) ≤ 9 := by
  have haL1 := d.not_mem_L1_of_not_mem_Dp hAZ haD'
  set C : Subgroup P := Subgroup.centralizer ({a} : Set P) with hC
  let ψ : C →* P ⧸ d.L 1 := (QuotientGroup.mk' (d.L 1)).comp C.subtype
  have hmul := Subgroup.card_ker_mul_card_range ψ
  have hker : Nat.card ψ.ker ≤ 3 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun u => (⟨(u : C).1, ?_, (u : C).2⟩ : (d.L 1 ⊓ C : Subgroup P))) ?_)
      (d.card_L1_inf_cent_le hAZ haD haD')
    · have := u.2
      rw [MonoidHom.mem_ker] at this
      exact (QuotientGroup.eq_one_iff _).mp this
    · intro x y hxy
      have := congrArg (fun z : (d.L 1 ⊓ C : Subgroup P) => (z : P)) hxy
      exact Subtype.ext (Subtype.ext this)
  have hdvd : Nat.card ψ.range ∣ 9 := by
    rw [← d.card_quot_L1]; exact Subgroup.card_subgroup_dvd_card _
  have hr3 : Nat.card ψ.range ≤ 3 := by
    by_contra hgt
    push Not at hgt
    have h9 : Nat.card ψ.range = 9 := by
      have : Nat.card ψ.range ∣ 3 ^ 2 := by simpa using hdvd
      rcases (Nat.dvd_prime_pow Nat.prime_three).mp this with ⟨k, hk, hk'⟩
      interval_cases k
      · rw [hk'] at hgt; simp at hgt
      · rw [hk'] at hgt; simp at hgt
      · rw [hk']; norm_num
    have htop : ψ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h9, d.card_quot_L1])
    apply d.Ta_ne_top haL1
    rw [eq_top_iff]
    intro g _
    have : ((g : P) : P ⧸ d.L 1) ∈ ψ.range := by rw [htop]; trivial
    obtain ⟨c, hc⟩ := this
    have hc' : ((c.1 : P) : P ⧸ d.L 1) = (g : P ⧸ d.L 1) := hc
    rw [QuotientGroup.eq] at hc'
    have hcT : c.1 ∈ d.Ta a := by
      rw [d.mem_Ta]
      have := Subgroup.mem_centralizer_singleton_iff.mp c.2
      have e : ⁅a, c.1⁆ = 1 := by
        rw [commutatorElement_def]
        calc a * c.1 * a⁻¹ * c.1⁻¹ = c.1 * a * a⁻¹ * c.1⁻¹ := by rw [← this]
          _ = 1 := by group
      rw [e]; exact (d.L 2).one_mem
    have hT1 : c.1⁻¹ * g ∈ d.Ta a := by
      rw [d.mem_Ta]
      have hmem : ⁅a, c.1⁻¹ * g⁆ ∈ d.L 2 := by
        have := d.comm_mem_L (j := 1) hc' a
        rw [← commutatorElement_inv]
        exact (d.L 2).inv_mem this
      exact hmem
    have : g = c.1 * (c.1⁻¹ * g) := by group
    rw [this]
    exact (d.Ta a).mul_mem hcT hT1
  calc Nat.card C = Nat.card ψ.ker * Nat.card ψ.range := hmul.symm
    _ ≤ 3 * 3 := Nat.mul_le_mul hker hr3
    _ = 9 := by norm_num

theorem comm_onto_L1 {a : P} (haD : ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a) (haD' : a ∉ d.Dp) :
    ∀ w ∈ d.L 1, ∃ k : P, ⁅a, k⁆ = w := by
  have hm := d.hm
  have := surj_comm a (⊤ : Subgroup P) (d.L 1) (fun b _ => d.comm_mem_L1 a b) (by
    have h1 := d.card_L (j := 1) le_rfl (by omega)
    have hC := d.card_cent_le_nine hAZ haD haD'
    rw [top_inf_eq, Subgroup.card_top, h1, d.hcard]
    calc 3 ^ (d.m - 1 - 1) * Nat.card (Subgroup.centralizer ({a} : Set P))
        ≤ 3 ^ (d.m - 1 - 1) * 9 := Nat.mul_le_mul_left _ hC
      _ = 3 ^ d.m := by
        rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_add]; congr 1; omega)
  intro w hw
  obtain ⟨b, -, hb⟩ := this w hw
  exact ⟨b, hb⟩

theorem abelian_of_AZ : ∀ p ∈ d.L 1, ∀ q ∈ d.L 1, p * q = q * p := by
  have hm := d.hm
  set D : Subgroup P := Subgroup.centralizer (d.L (d.m - 3) : Set P) with hD
  have hDtop : D ≠ ⊤ := by
    obtain ⟨a, w, hw, hne⟩ := d.exists_not_centralizes
    intro h
    have : a ∈ D := by rw [h]; trivial
    rw [hD, Subgroup.mem_centralizer_iff] at this
    exact hne (this w hw).symm
  obtain ⟨a, haD0, haD'⟩ := d.exists_not_mem_both D d.Dp hDtop d.Dp_ne_top
  have haD : ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a := by
    rw [hD, Subgroup.mem_centralizer_iff] at haD0
    push Not at haD0
    obtain ⟨w, hw, hne⟩ := haD0
    exact ⟨w, hw, fun h => hne h.symm⟩
  have hc3 := d.cube_center hAZ haD haD'
  have h3 : a ^ 3 = a * a * a := by rw [pow_succ, pow_succ, pow_one]
  have hN : ∀ w ∈ d.L 1, (a * (a * w * a⁻¹) * a⁻¹) * (a * w * a⁻¹) * w = 1 := by
    intro w hw
    obtain ⟨k, rfl⟩ := d.comm_onto_L1 hAZ haD haD' w hw
    have e : (a * (a * ⁅a, k⁆ * a⁻¹) * a⁻¹) * (a * ⁅a, k⁆ * a⁻¹) * ⁅a, k⁆ =
        (a * a * a) * k * (a * a * a)⁻¹ * k⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    have hk : k * (a * a * a) = (a * a * a) * k := by
      have := Subgroup.mem_center_iff.mp hc3 k
      rwa [h3] at this
    calc (a * a * a) * k * (a * a * a)⁻¹ * k⁻¹ = (k * (a * a * a)) * (a * a * a)⁻¹ * k⁻¹ := by
          rw [hk]
      _ = 1 := by group
  have hcomm := comm_delta_eq_one a (d.L 1) hAZ hN
  have hL2c : ∀ l ∈ d.L 2, ∀ u ∈ d.L 1, l * u = u * l := by
    intro l hl u hu
    obtain ⟨v, hv, rfl⟩ := d.comm_onto_L2 hAZ haD haD' l hl
    exact commutatorElement_eq_one_iff_mul_comm.mp (hcomm u hu v hv)
  have haL1 := d.not_mem_L1_of_not_mem_Dp hAZ haD'
  obtain ⟨x, hx⟩ : ∃ x : P, ⁅a, x⁆ ∉ d.L 2 := by
    by_contra h
    push Not at h
    exact haL1 (d.mem_L1_of_comm_L2 h)
  have hcard : Nat.card (d.L 1) = 3 * Nat.card (d.L 2) := by
    rw [d.card_L (j := 1) le_rfl (by omega), d.card_L (j := 2) (by omega) (by omega),
      ← pow_succ']
    congr 1; omega
  have hdec := exists_decomp_grp (H₁ := d.L 1) (H₂ := d.L 2) (d.L_anti (by omega)) hcard
    (d.comm_mem_L1 a x) hx
  intro p hp q hq
  obtain ⟨i, h, hh, rfl⟩ := hdec p hp
  obtain ⟨j, h', hh', rfl⟩ := hdec q hq
  have hyL1 : ⁅a, x⁆ ∈ d.L 1 := d.comm_mem_L1 a x
  have hyi : ⁅a, x⁆ ^ j ∈ d.L 1 := (d.L 1).zpow_mem hyL1 j
  have hyi' : ⁅a, x⁆ ^ i ∈ d.L 1 := (d.L 1).zpow_mem hyL1 i
  have h1 : h * ⁅a, x⁆ ^ j = ⁅a, x⁆ ^ j * h := hL2c h hh _ hyi
  have h2 : h' * ⁅a, x⁆ ^ i = ⁅a, x⁆ ^ i * h' := hL2c h' hh' _ hyi'
  have h3' : h * h' = h' * h := hL2c h hh h' (d.L_anti (by omega) hh')
  have h4 : ⁅a, x⁆ ^ i * ⁅a, x⁆ ^ j = ⁅a, x⁆ ^ j * ⁅a, x⁆ ^ i := by
    rw [← zpow_add, ← zpow_add, add_comm]
  calc ⁅a, x⁆ ^ i * h * (⁅a, x⁆ ^ j * h') = ⁅a, x⁆ ^ i * (h * ⁅a, x⁆ ^ j) * h' := by group
    _ = ⁅a, x⁆ ^ i * (⁅a, x⁆ ^ j * h) * h' := by rw [h1]
    _ = (⁅a, x⁆ ^ i * ⁅a, x⁆ ^ j) * (h * h') := by group
    _ = (⁅a, x⁆ ^ j * ⁅a, x⁆ ^ i) * (h' * h) := by rw [h4, h3']
    _ = ⁅a, x⁆ ^ j * (⁅a, x⁆ ^ i * h') * h := by group
    _ = ⁅a, x⁆ ^ j * (h' * ⁅a, x⁆ ^ i) * h := by rw [← h2]
    _ = ⁅a, x⁆ ^ j * h' * (⁅a, x⁆ ^ i * h) := by group

end MB

theorem derived_abelian : ∀ m : ℕ, 4 ≤ m → ∀ (P : Type u) [Group P] [Finite P], IsPGroup 3 P →
    Nat.card P = 3 ^ m → (⊤ : Subgroup P).lowerCentralSeries (m - 2) ≠ ⊥ →
    ∀ a ∈ (⊤ : Subgroup P).lowerCentralSeries 1, ∀ b ∈ (⊤ : Subgroup P).lowerCentralSeries 1,
      a * b = b * a := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm P _ _ hP hcard hne
  rcases (show m = 4 ∨ 5 ≤ m by omega) with h4 | h5
  · subst h4
    have hc := card_lcs_of_maxClass (p := 3) 4 P hP hcard hne (by norm_num) 1 le_rfl (by norm_num)
    have hcomm : IsMulCommutative ((⊤ : Subgroup P).lowerCentralSeries 1) :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hc])
    intro a ha b hb
    have := hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  · let d : MB P := ⟨m, h5, hP, hcard, hne⟩
    have hmax : IsMaximalClass 3 P := ⟨m, by omega, hcard, hne⟩
    have hmaxQ := isMaximalClass_quotient_center hP hmax (by
      rw [hcard]; exact Nat.pow_le_pow_right (by norm_num) (by omega))
    obtain ⟨m', hm'2, hm'card, hm'ne⟩ := hmaxQ
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)
    have hZ := d.card_center
    have hQ : Nat.card (P ⧸ Subgroup.center P) = 3 ^ (m - 1) := by
      have : 3 ^ m = 3 ^ (m - 1) * 3 := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [hZ, hcard, this] at hmul
      exact (Nat.eq_of_mul_eq_mul_right (by norm_num) hmul).symm
    have hm'eq : m' = m - 1 := by
      rw [hQ] at hm'card
      exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) hm'card).symm
    subst hm'eq
    have ihQ := ih (m - 1) (by omega) (by omega) (P ⧸ Subgroup.center P)
      (hP.to_quotient _) hQ hm'ne
    have hAZ : ∀ p ∈ d.L 1, ∀ q ∈ d.L 1, ⁅p, q⁆ ∈ Subgroup.center P := by
      intro p hp q hq
      have hmap := Subgroup.map_lowerCentralSeries (⊤ : Subgroup P)
        (QuotientGroup.mk' (Subgroup.center P)) 1
      rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hmap
      have hp' : (p : P ⧸ Subgroup.center P) ∈
          (⊤ : Subgroup (P ⧸ Subgroup.center P)).lowerCentralSeries 1 := by
        rw [← hmap]; exact Subgroup.mem_map_of_mem _ hp
      have hq' : (q : P ⧸ Subgroup.center P) ∈
          (⊤ : Subgroup (P ⧸ Subgroup.center P)).lowerCentralSeries 1 := by
        rw [← hmap]; exact Subgroup.mem_map_of_mem _ hq
      exact (d.comm_mem_center_iff p q).mpr (ihQ _ hp' _ hq')
    exact d.abelian_of_AZ hAZ

end CFSG.HardMathSupport.Lang.E6Descent
