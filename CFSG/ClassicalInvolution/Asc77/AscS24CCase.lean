module

public import CFSG.ClassicalInvolution.Asc77.AscS24CW1
public import CFSG.ClassicalInvolution.Asc77.AscS24BIV
public import CFSG.ClassicalInvolution.Asc77.AscS24CGraph

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped Pointwise

namespace S24

section General

variable {G : Type} [Group G]

theorem eq_sq_of_mem_zpowers {x v : G} (hx : orderOf x = 4) (hv : v ∈ Subgroup.zpowers x)
    (h2 : v * v = 1) (h1 : v ≠ 1) : v = x ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hmod : ∀ c : ℤ, x ^ c = x ^ (c % 4) := fun c => by
    have e := zpow_mod_orderOf x c
    rw [hx] at e
    exact_mod_cast e.symm
  have e : x ^ (k + k) = 1 := by rw [zpow_add]; exact h2
  have h4 := orderOf_dvd_iff_zpow_eq_one.mpr e
  rw [hx] at h4
  have h4' : (4 : ℤ) ∣ k + k := by exact_mod_cast h4
  have hk : k % 4 = 0 ∨ k % 4 = 2 := by omega
  rw [hmod k]
  rcases hk with hk | hk <;> rw [hk]
  · exact absurd (by rw [hmod k, hk, zpow_zero]) h1
  · rw [zpow_two, pow_two]

theorem eq_of_inj_zpowers {H : Subgroup G} {x : G} (hx : orderOf x = 4)
    {μ : ↥H →* ↥(Subgroup.zpowers x)} (hμ : Function.Injective μ) {a b : ↥H}
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (hb2 : b * b = 1) (hb1 : b ≠ 1) : a = b := by
  have key : ∀ c : ↥H, c * c = 1 → c ≠ 1 → ((μ c : ↥(Subgroup.zpowers x)) : G) = x ^ 2 := by
    intro c hc2 hc1
    refine eq_sq_of_mem_zpowers hx (μ c).2 ?_ ?_
    · have := congrArg (fun y : ↥(Subgroup.zpowers x) => (y : G)) (congrArg μ hc2)
      simpa [map_mul] using this
    · intro h
      apply hc1
      apply hμ
      rw [map_one]
      exact Subtype.ext h
  exact hμ (Subtype.ext ((key a ha2 ha1).trans (key b hb2 hb1).symm))

theorem conj_mul_zpow_cases {s x y : G} (hys : y * s * y⁻¹ = s)
    (hyx : y * x * y⁻¹ = x ∨ y * x * y⁻¹ = x⁻¹) (j : ℤ) :
    ∃ k : ℤ, (Even k ↔ Even j) ∧ y * (s * x ^ j) * y⁻¹ = s * x ^ k := by
  have e : y * (s * x ^ j) * y⁻¹ = (y * s * y⁻¹) * (y * x * y⁻¹) ^ j := by
    rw [conj_zpow]; group
  rcases hyx with h | h
  · exact ⟨j, Iff.rfl, by rw [e, hys, h]⟩
  · refine ⟨-j, even_neg, ?_⟩
    rw [e, hys, h, inv_zpow']

theorem centralizes_conj_z {S₁ : Subgroup G} {z : G} (hz : ∀ s ∈ S₁, s * z = z * s) {c g : G}
    (hg : ∀ y ∈ S₁ ⊓ Subgroup.centralizer {c}, g⁻¹ * y * g ∈ S₁) {v : G} (hvS : v ∈ S₁)
    (hvc : v * c = c * v) : v * (g * z * g⁻¹) = (g * z * g⁻¹) * v := by
  have h := hz _ (hg v ⟨hvS, Subgroup.mem_centralizer_singleton_iff.mpr hvc⟩)
  calc v * (g * z * g⁻¹) = g * ((g⁻¹ * v * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * v * g)) * g⁻¹ := by rw [h]
    _ = (g * z * g⁻¹) * v := by group

theorem card_conjSub (n : G) (H : Subgroup G) : Nat.card ↥(conjSub n H) = Nat.card ↥H :=
  Nat.card_congr (Subgroup.equivMapOfInjective H (MulAut.conj n).toMonoidHom
    (MulAut.conj n).injective).symm.toEquiv

end General

section Ctx

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : S24B.Ctx8 p f Ω K K' W S R R' z u)

theorem conj_t_zpow (n : ℤ) :
    C.D.x₃ ^ n * C.D.F.ρ'.r * (C.D.x₃ ^ n)⁻¹ = C.D.x₂ ^ (-n) * C.D.F.ρ'.r := by
  have h1 : C.D.F.ρ'.r * C.D.x₃ ^ (-n) * C.D.F.ρ'.r⁻¹ = C.D.x₃ ^ (-n) * C.D.x₂ ^ (-n) := by
    rw [← conj_zpow, C.D.t₃, C.D.comm23.symm.mul_zpow]
  calc C.D.x₃ ^ n * C.D.F.ρ'.r * (C.D.x₃ ^ n)⁻¹
      = C.D.x₃ ^ n * (C.D.F.ρ'.r * C.D.x₃ ^ (-n) * C.D.F.ρ'.r⁻¹) * C.D.F.ρ'.r := by group
    _ = C.D.x₂ ^ (-n) * C.D.F.ρ'.r := by rw [h1]; group

theorem t_mul_x₂_zpow (k : ℤ) : C.D.F.ρ'.r * C.D.x₂ ^ k = C.D.x₂ ^ (-k) * C.D.F.ρ'.r := by
  have h : C.D.F.ρ'.r * C.D.x₂ ^ k * C.D.F.ρ'.r⁻¹ = C.D.x₂ ^ (-k) := by
    rw [← conj_zpow, C.D.t₂, inv_zpow, zpow_neg]
  calc C.D.F.ρ'.r * C.D.x₂ ^ k = C.D.F.ρ'.r * C.D.x₂ ^ k * C.D.F.ρ'.r⁻¹ * C.D.F.ρ'.r := by
        group
    _ = C.D.x₂ ^ (-k) * C.D.F.ρ'.r := by rw [h]

theorem conj_W_r_t {v : G} (hv : v ∈ W) : ∃ a b : ℤ,
    v * C.D.F.ρ.r * v⁻¹ = C.D.F.ρ.r * C.D.x₁ ^ (b - 2 * a) ∧
      v * C.D.F.ρ'.r * v⁻¹ = C.D.F.ρ'.r * C.D.x₂ ^ b := by
  obtain ⟨a, b, rfl⟩ := C.exists_nf hv
  refine ⟨a, b, ?_, ?_⟩
  · have h1 := C.conj_x₃_zpow_r b
    have h2 : C.D.F.ρ.r * C.D.x₁ ^ (-a) = C.D.x₁ ^ a * C.D.F.ρ.r := by
      have := C.r_mul_x₁_zpow (-a)
      rwa [neg_neg] at this
    have h3 : C.D.x₁ ^ (2 * a - b) * C.D.F.ρ.r = C.D.F.ρ.r * C.D.x₁ ^ (b - 2 * a) := by
      have := C.r_mul_x₁_zpow (b - 2 * a)
      rw [show -(b - 2 * a) = 2 * a - b by ring] at this
      exact this.symm
    calc C.D.x₁ ^ a * C.D.x₃ ^ b * C.D.F.ρ.r * (C.D.x₁ ^ a * C.D.x₃ ^ b)⁻¹
        = C.D.x₁ ^ a * (C.D.x₃ ^ b * C.D.F.ρ.r * (C.D.x₃ ^ b)⁻¹) * C.D.x₁ ^ (-a) := by
          rw [zpow_neg]; group
      _ = C.D.x₁ ^ a * C.D.x₁ ^ (-b) * (C.D.F.ρ.r * C.D.x₁ ^ (-a)) := by rw [h1]; group
      _ = C.D.x₁ ^ a * C.D.x₁ ^ (-b) * (C.D.x₁ ^ a * C.D.F.ρ.r) := by rw [h2]
      _ = C.D.x₁ ^ (2 * a - b) * C.D.F.ρ.r := by
          rw [← mul_assoc, ← zpow_add, ← zpow_add]; ring_nf
      _ = C.D.F.ρ.r * C.D.x₁ ^ (b - 2 * a) := h3
  · have h1 := conj_t_zpow C b
    have hx₁t : C.D.x₁ * C.D.F.ρ'.r = C.D.F.ρ'.r * C.D.x₁ :=
      C.commutes_R_R' _ C.x₁_mem_R _ C.t_mem_R'
    have hct : ∀ i : ℤ, C.D.x₁ ^ i * C.D.F.ρ'.r = C.D.F.ρ'.r * C.D.x₁ ^ i := fun i =>
      (Commute.zpow_left hx₁t i).eq
    have hc2 : ∀ i j : ℤ, C.D.x₁ ^ i * C.D.x₂ ^ j = C.D.x₂ ^ j * C.D.x₁ ^ i := fun i j =>
      (C.D.comm12.zpow_zpow i j).eq
    have h2 : C.D.x₂ ^ (-b) * C.D.F.ρ'.r = C.D.F.ρ'.r * C.D.x₂ ^ b := by
      have := t_mul_x₂_zpow C b
      exact this.symm
    calc C.D.x₁ ^ a * C.D.x₃ ^ b * C.D.F.ρ'.r * (C.D.x₁ ^ a * C.D.x₃ ^ b)⁻¹
        = C.D.x₁ ^ a * (C.D.x₃ ^ b * C.D.F.ρ'.r * (C.D.x₃ ^ b)⁻¹) * (C.D.x₁ ^ a)⁻¹ := by group
      _ = C.D.x₁ ^ a * C.D.x₂ ^ (-b) * C.D.F.ρ'.r * (C.D.x₁ ^ a)⁻¹ := by rw [h1]; group
      _ = C.D.x₂ ^ (-b) * (C.D.x₁ ^ a * C.D.F.ρ'.r) * (C.D.x₁ ^ a)⁻¹ := by rw [hc2]; group
      _ = C.D.x₂ ^ (-b) * C.D.F.ρ'.r := by rw [hct]; group
      _ = C.D.F.ρ'.r * C.D.x₂ ^ b := h2

theorem frame_fix {n : G}
    (hn : n = 1 ∨ n = C.D.F.ρ.r ∨ n = C.D.F.ρ'.r ∨ n = C.D.F.ρ.r * C.D.F.ρ'.r) :
    n * C.D.F.ρ.r * n⁻¹ = C.D.F.ρ.r ∧ n * C.D.F.ρ'.r * n⁻¹ = C.D.F.ρ'.r := by
  have hrt := C.commute_r_t.eq
  rcases hn with rfl | rfl | rfl | rfl
  · constructor <;> group
  · constructor
    · group
    · rw [hrt]; group
  · constructor
    · rw [← hrt]; group
    · group
  · constructor
    · calc C.D.F.ρ.r * C.D.F.ρ'.r * C.D.F.ρ.r * (C.D.F.ρ.r * C.D.F.ρ'.r)⁻¹
          = C.D.F.ρ.r * (C.D.F.ρ'.r * C.D.F.ρ.r) * C.D.F.ρ'.r⁻¹ * C.D.F.ρ.r⁻¹ := by group
        _ = C.D.F.ρ.r := by rw [← hrt]; group
    · calc C.D.F.ρ.r * C.D.F.ρ'.r * C.D.F.ρ'.r * (C.D.F.ρ.r * C.D.F.ρ'.r)⁻¹
          = C.D.F.ρ.r * C.D.F.ρ'.r * C.D.F.ρ.r⁻¹ := by group
        _ = C.D.F.ρ'.r := by rw [hrt]; group

include C in
theorem frame_cases {m : G} (hm : m ∈ MGrp Ω W ⊔ OCW W) (hK : conjSub m K = K) :
    ∃ n : G, (n = 1 ∨ n = C.D.F.ρ.r ∨ n = C.D.F.ρ'.r ∨ n = C.D.F.ρ.r * C.D.F.ρ'.r) ∧
      Thompson.piG W m = Thompson.piG W n := by
  have hmN : m ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_sup_le_normalizer Ω W hm
  set q : ↥(muGroup Ω W) := ⟨Thompson.piG W m, Thompson.piG_mem_muGroup hm⟩ with hq
  have hrN := C.D.F.ρ.r_mem_normalizer
  have htN := C.D.F.ρ'.r_mem_normalizer
  have h1 : Thompson.piG W m * C.D.F.ρ.img * (Thompson.piG W m)⁻¹ = C.D.F.ρ.img :=
    C.img_conj_eq_of_fix hmN C.D.F.ρ (by rw [C.hK]; exact hK)
  have hcomm : q * T7D.imgQ C.D.F.ρ = T7D.imgQ C.D.F.ρ * q := by
    apply Subtype.ext
    change Thompson.piG W m * C.D.F.ρ.img = C.D.F.ρ.img * Thompson.piG W m
    calc Thompson.piG W m * C.D.F.ρ.img
        = Thompson.piG W m * C.D.F.ρ.img * (Thompson.piG W m)⁻¹ * Thompson.piG W m := by group
      _ = C.D.F.ρ.img * Thompson.piG W m := by rw [h1]
  set a := C.D.φ (T7D.imgQ C.D.F.ρ)
  set b := C.D.φ (T7D.imgQ C.D.F.ρ')
  have hab : a ≠ b := fun h => C.D.hab (C.D.φ.injective h)
  have hab' : a * b = b * a := by simp only [a, b, ← map_mul, C.D.hcomm]
  have hxa : C.D.φ q * a = a * C.D.φ q := by simp only [a, ← map_mul, hcomm]
  have hcases := S24B.perm4_cent_swap _ a (C.φ_imgQ_mem _) b (C.φ_imgQ_mem _) hab hab' hxa
  have hval : ∀ y : ↥(muGroup Ω W), C.D.φ q = C.D.φ y →
      Thompson.piG W m = (y : NQuot (W ⊔ OCW W)) := fun y h =>
    congrArg Subtype.val (C.D.φ.injective h)
  rcases hcases with h | h | h | h
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [hval 1 (h.trans (map_one C.D.φ).symm), Thompson.piG_of_mem_sup (Subgroup.one_mem _)]
    rfl
  · exact ⟨_, Or.inr (Or.inl rfl), hval _ h⟩
  · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), hval _ h⟩
  · refine ⟨_, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
    rw [hval (T7D.imgQ C.D.F.ρ * T7D.imgQ C.D.F.ρ') (by rw [h, map_mul]),
      Thompson.piG_mul hrN htN]
    rfl

include C in
theorem frame_mem_P {n : G}
    (hn : n = 1 ∨ n = C.D.F.ρ.r ∨ n = C.D.F.ρ'.r ∨ n = C.D.F.ρ.r * C.D.F.ρ'.r) :
    n ∈ (S : Subgroup G) ⊓ MGrp Ω W := by
  have hr : C.D.F.ρ.r ∈ (S : Subgroup G) ⊓ MGrp Ω W :=
    ⟨C.hd.hR.2.2 C.r_mem_R, Thompson.le_MGrp_of_mem_D C.D.F.ρ.hR C.D.F.ρ.hr⟩
  have ht : C.D.F.ρ'.r ∈ (S : Subgroup G) ⊓ MGrp Ω W :=
    ⟨C.hd.hR'.2.2 C.t_mem_R', Thompson.le_MGrp_of_mem_D C.D.F.ρ'.hR C.D.F.ρ'.hr⟩
  rcases hn with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact hr
  · exact ht
  · exact Subgroup.mul_mem _ hr ht

include C in
theorem trivMu_of_mem_A {a : G} (ha : a ∈ C.A) : S24B.TrivMu Ω W a := by
  obtain ⟨-, haW, haR, haK', haJ⟩ := (C.mem_A).mp ha
  have haN : a ∈ Subgroup.normalizer (W : Set G) := Subgroup.centralizer_le_normalizer _ haW
  have haK : conjSub a C.D.F.ρ.K = C.D.F.ρ.K := by
    rw [C.hK]
    exact S24B.conjSub_eq_of_commute C.hs.stand.hyp C.hs.stand.mem C.x₁_mem_K C.orderOf_x₁
      (Subgroup.mem_centralizer_iff.mp haR _ C.x₁_mem_R).symm
  exact C.trivMu_of_fix haN haK (by rw [C.hK']; exact mem_normalizer_iff_conjSub_eq.mp haK')
    (mem_normalizer_iff_conjSub_eq.mp haJ)

include C in
theorem exists_frame_mul {x : G} (hx : x ∈ sZero Ω W S) (hxK : conjSub x K = K) :
    ∃ n : G, (n = 1 ∨ n = C.D.F.ρ.r ∨ n = C.D.F.ρ'.r ∨ n = C.D.F.ρ.r * C.D.F.ρ'.r) ∧
      ∃ w ∈ W, ∃ a ∈ C.A, x = n * w * a := by
  obtain ⟨p, hpP, t, htS, hT, rfl⟩ := C.exists_decomp hx.1
  have htS₀ : t ∈ sZero Ω W S := by
    have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ (inf_le_sZero hpP)) hx
    rwa [inv_mul_cancel_left] at h
  have htN := C.le_normalizer_W htS
  have htW : t ∈ Subgroup.centralizer (W : Set G) := by
    rcases acts_pm C htS hT with h | h
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have := h w hw
      calc w * t = t * w * t⁻¹ * t := by rw [this]
        _ = t * w := by group
    · exact absurd htS₀ (not_mem_sZero C h)
  have hK : conjSub t K = K := by
    have h := C.fix_of_trivMu htN hT C.D.F.ρ
    rwa [C.hK] at h
  have hK' : conjSub t K' = K' := by
    have h := C.fix_of_trivMu htN hT C.D.F.ρ'
    rwa [C.hK'] at h
  have hJ := C.fix_of_trivMu htN hT C.D.F.ρ₃
  obtain ⟨w, hw, hwt⟩ := C.exists_W_mul_mem_centralizer htS htW hK
  have hwtA : w * t ∈ C.A := by
    refine (C.mem_A).mpr ⟨S.mul_mem (C.hd.hWS hw) htS, ?_, hwt, ?_, ?_⟩
    · refine Subgroup.mul_mem _ ?_ htW
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Thompson.commutes_of_mem_WSet C.D.c.hp C.D.c.hq C.D.c.hΩ C.D.c.hW v hv w hw
    · exact Subgroup.mul_mem _ (C.W_le_normalizer K' C.hs.hK'.1 ⟨C.x₂_mem_K', C.D.x₂_mem⟩
        C.orderOf_x₂ hw) (mem_normalizer_iff_conjSub_eq.mpr hK')
    · exact Subgroup.mul_mem _ (C.W_le_normalizer C.D.F.ρ₃.K C.D.F.ρ₃.hK
        ⟨C.x₃_mem_J, C.D.x₃_mem⟩ C.orderOf_x₃ hw) (mem_normalizer_iff_conjSub_eq.mpr hJ)
  have hwN : conjSub w K = K := by
    have := C.W_le_normalizer K C.hs.stand.mem ⟨C.x₁_mem_K, C.D.x₁_mem⟩ C.orderOf_x₁ hw
    exact mem_normalizer_iff_conjSub_eq.mp this
  have hp₁K : conjSub (p * w⁻¹) K = K := by
    have e : p * w⁻¹ = (p * t) * (w * t)⁻¹ := by group
    have h2 : conjSub (w * t) K = K := by rw [conjSub_mul, hK, hwN]
    have h3 : conjSub (w * t)⁻¹ K = K := by
      calc conjSub (w * t)⁻¹ K = conjSub (w * t)⁻¹ (conjSub (w * t) K) := by rw [h2]
        _ = K := conjSub_inv_conjSub _ _
    rw [e, conjSub_mul, h3, hxK]
  have hp₁P : p * w⁻¹ ∈ (S : Subgroup G) ⊓ MGrp Ω W :=
    Subgroup.mul_mem _ hpP (Subgroup.inv_mem _ (C.W_le_P hw))
  obtain ⟨n, hn, hpn⟩ := frame_cases C (Subgroup.mem_sup_left hp₁P.2) hp₁K
  have hnP := frame_mem_P C hn
  have hnN : n ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W hnP.2
  have hp₁N : p * w⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
    Thompson.MGrp_le_normalizer Ω W hp₁P.2
  have hmem : n⁻¹ * (p * w⁻¹) ∈ W ⊔ OCW W := (Thompson.piG_eq_iff hnN hp₁N).mp hpn.symm
  have hw₁ : n⁻¹ * (p * w⁻¹) ∈ W := by
    refine Thompson.mem_of_isPGroup_of_mem_sup_OCW (Thompson.isPGroup_of_mem_WSet C.hd.hW)
      (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr ?_)) hmem
    exact S.mul_mem (S.inv_mem hnP.1) hp₁P.1
  refine ⟨n, hn, n⁻¹ * (p * w⁻¹), hw₁, w * t, hwtA, by group⟩

theorem conj_x₂_cases {y : G} (hyN : y ∈ Subgroup.normalizer (W : Set G))
    (hyK : conjSub y K' = K') :
    y * C.D.x₂ * y⁻¹ = C.D.x₂ ∨ y * C.D.x₂ * y⁻¹ = C.D.x₂⁻¹ := by
  refine eq_or_eq_inv_of_conj_mem C.orderOf_x₂ ?_
  rw [← inf_W_eq_x₂ C]
  refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hyN _).mp C.D.x₂_mem⟩
  have h := conj_mem_conjSub (n := y) C.x₂_mem_K'
  rwa [hyK] at h

include C in
theorem conj_mem_R {y : G} (hyS : y ∈ (S : Subgroup G)) (hyK : conjSub y K = K) :
    ∀ q ∈ R, y * q * y⁻¹ ∈ R := fun q hq => by
  refine (le_of_eq C.inf_S_eq_R) ⟨?_, S.mul_mem (S.mul_mem hyS (C.hd.hR.2.2 hq))
    (S.inv_mem hyS)⟩
  have h := conj_mem_conjSub (n := y) (C.hd.hR.2.1 hq)
  rwa [hyK] at h

include C in
theorem conj_mem_R' {y : G} (hyS : y ∈ (S : Subgroup G)) (hyK : conjSub y K' = K') :
    ∀ q ∈ R', y * q * y⁻¹ ∈ R' := fun q hq => by
  refine (le_of_eq C.inf_S_eq_R') ⟨?_, S.mul_mem (S.mul_mem hyS (C.hd.hR'.2.2 hq))
    (S.inv_mem hyS)⟩
  have h := conj_mem_conjSub (n := y) (C.hd.hR'.2.1 hq)
  rwa [hyK] at h

include C in
theorem innerOn_R_iff {y : G} (hyS : y ∈ (S : Subgroup G)) (hyK : conjSub y K = K) {k : ℤ}
    (hk : y * C.D.F.ρ.r * y⁻¹ = C.D.F.ρ.r * C.D.x₁ ^ k) : InnerOn y R ↔ Even k :=
  innerOn_iff_even (Subgroup.zpowers_le.mpr C.x₁_mem_R) C.card_R C.orderOf_x₁ C.r_mem_R
    C.r_not_mem_zpowers C.D.r₁ (conj_x₁_cases C (C.le_normalizer_W hyS) hyK) hk

include C in
theorem innerOn_R'_iff {y : G} (hyS : y ∈ (S : Subgroup G)) (hyK : conjSub y K' = K') {k : ℤ}
    (hk : y * C.D.F.ρ'.r * y⁻¹ = C.D.F.ρ'.r * C.D.x₂ ^ k) : InnerOn y R' ↔ Even k :=
  innerOn_iff_even (Subgroup.zpowers_le.mpr C.x₂_mem_R') C.card_R' C.orderOf_x₂ C.t_mem_R'
    C.t_not_mem_zpowers C.D.t₂ (conj_x₂_cases C (C.le_normalizer_W hyS) hyK) hk

include C in
theorem parity_eq (hA : ∀ a ∈ C.A, InnerOn a R') {x : G} (hx : x ∈ sZero Ω W S)
    (hxK : conjSub x K = K) : InnerOn x R ↔ InnerOn x R' := by
  have hxK' : conjSub x K' = K' := C.conjSub_K'_of_K hxK
  obtain ⟨n, hn, w, hw, a, ha, hxe⟩ := exists_frame_mul C hx hxK
  obtain ⟨haS, haW, haR, haK', -⟩ := (C.mem_A).mp ha
  have haK'' : conjSub a K' = K' := mem_normalizer_iff_conjSub_eq.mp haK'
  have hax₂ : a * C.D.x₂ * a⁻¹ = C.D.x₂ := conj_eq_of_mem_centralizer haW C.D.x₂_mem
  obtain ⟨κ, hκ⟩ := exists_conj_s (Subgroup.zpowers_le.mpr C.x₂_mem_R') C.card_R' C.t_mem_R'
    C.t_not_mem_zpowers (conj_mem_R' C haS haK'') (Or.inl hax₂)
  have hκe : Even κ := (innerOn_R'_iff C haS haK'' hκ).mp (hA a ha)
  have har : a * C.D.F.ρ.r * a⁻¹ = C.D.F.ρ.r := by
    rw [← Subgroup.mem_centralizer_iff.mp haR _ C.r_mem_R]
    group
  obtain ⟨a', b, hwr, hwt⟩ := conj_W_r_t C hw
  have hwx₂ : ∀ i : ℤ, w * C.D.x₂ ^ i * w⁻¹ = C.D.x₂ ^ i := fun i => by
    rw [← conj_zpow, conj_eq_of_mem_centralizer (Subgroup.mem_centralizer_iff.mpr fun v hv =>
      Thompson.commutes_of_mem_WSet C.D.c.hp C.D.c.hq C.D.c.hΩ C.D.c.hW v hv w hw) C.D.x₂_mem]
  obtain ⟨hnr, hnt⟩ := frame_fix C hn
  have hnP := frame_mem_P C hn
  have hnN : n ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W hnP.2
  have hnK : conjSub n K = K := by
    rcases hn with rfl | rfl | rfl | rfl
    · exact conjSub_one K
    · exact conjSub_eq_self_of_mem C.r_mem_K
    · exact mem_normalizer_iff_conjSub_eq.mp (C.mem_normalizer_K_of_mem_K' C.t_mem_K')
    · rw [conjSub_mul, mem_normalizer_iff_conjSub_eq.mp (C.mem_normalizer_K_of_mem_K' C.t_mem_K'),
        conjSub_eq_self_of_mem C.r_mem_K]
  have hnK' : conjSub n K' = K' := C.conjSub_K'_of_K hnK
  obtain ⟨k₁, hk₁e, hk₁⟩ := conj_mul_zpow_cases hnr (conj_x₁_cases C hnN hnK) (b - 2 * a')
  obtain ⟨k₂, hk₂e, hk₂⟩ := conj_mul_zpow_cases hnt (conj_x₂_cases C hnN hnK') (b + κ)
  have hxS : x ∈ (S : Subgroup G) := hx.1
  have e₁ : x * C.D.F.ρ.r * x⁻¹ = C.D.F.ρ.r * C.D.x₁ ^ k₁ := by
    rw [hxe, ← hk₁, ← hwr]
    calc n * w * a * C.D.F.ρ.r * (n * w * a)⁻¹
        = n * (w * (a * C.D.F.ρ.r * a⁻¹) * w⁻¹) * n⁻¹ := by group
      _ = n * (w * C.D.F.ρ.r * w⁻¹) * n⁻¹ := by rw [har]
  have e₂ : x * C.D.F.ρ'.r * x⁻¹ = C.D.F.ρ'.r * C.D.x₂ ^ k₂ := by
    rw [hxe, ← hk₂]
    calc n * w * a * C.D.F.ρ'.r * (n * w * a)⁻¹
        = n * (w * (a * C.D.F.ρ'.r * a⁻¹) * w⁻¹) * n⁻¹ := by group
      _ = n * (w * (C.D.F.ρ'.r * C.D.x₂ ^ κ) * w⁻¹) * n⁻¹ := by rw [hκ]
      _ = n * ((w * C.D.F.ρ'.r * w⁻¹) * (w * C.D.x₂ ^ κ * w⁻¹)) * n⁻¹ := by group
      _ = n * (C.D.F.ρ'.r * C.D.x₂ ^ (b + κ)) * n⁻¹ := by
          rw [hwt, hwx₂, mul_assoc C.D.F.ρ'.r, ← zpow_add]
  rw [innerOn_R_iff C hxS hxK e₁, innerOn_R'_iff C hxS hxK' e₂, hk₁e, hk₂e]
  have h1 : Even (b - 2 * a') ↔ Even b := by
    rw [Int.even_sub]
    simp
  have h2 : Even (b + κ) ↔ Even b := by
    rw [Int.even_add]
    simp [hκe]
  rw [h1, h2]

include C in
theorem z_mem_S : ∀ s ∈ (S : Subgroup G), s * z = z * s := fun _ hs =>
  Subgroup.mem_centralizer_singleton_iff.mp (C.le_centralizer_z hs)

include C in
theorem mem_centralizer_W_of_sZero {x : G} (hx : x ∈ sZero Ω W S)
    (h1 : x * C.D.x₁ * x⁻¹ = C.D.x₁) (h2 : x * C.D.x₂ * x⁻¹ = C.D.x₂) :
    x ∈ Subgroup.centralizer (W : Set G) := by
  obtain ⟨-, m, hm, hxm⟩ := hx
  have hm1 : m * C.D.x₁ * m⁻¹ = C.D.x₁ := (hxm _ C.D.x₁_mem).symm.trans h1
  have hm2 : m * C.D.x₂ * m⁻¹ = C.D.x₂ := (hxm _ C.D.x₂_mem).symm.trans h2
  have hmK : conjSub m K = K := by
    refine conjSub_eq_of_conj C C.hs.stand.mem C.x₁_mem_K C.orderOf_x₁ (Or.inl ?_)
    calc m⁻¹ * C.D.x₁ * m = m⁻¹ * (m * C.D.x₁ * m⁻¹) * m := by rw [hm1]
      _ = C.D.x₁ := by group
  obtain ⟨n, hn, hpn⟩ := frame_cases C (Subgroup.mem_sup_left hm) hmK
  have hmN := Thompson.MGrp_le_normalizer Ω W hm
  have hnN : n ∈ Subgroup.normalizer (W : Set G) :=
    Thompson.MGrp_le_normalizer Ω W (frame_mem_P C hn).2
  have hact : ∀ v ∈ W, m * v * m⁻¹ = n * v * n⁻¹ := fun v hv =>
    Thompson.conj_eq_of_piG_eq C.D.c.hp C.D.c.hq C.D.c.hΩ C.D.c.hW hnN hmN hpn.symm hv
  have hx₁2 : C.D.x₁⁻¹ ≠ C.D.x₁ := by
    intro e
    have e3 : C.D.x₁ ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← e]
      exact inv_mul_cancel _
    have := orderOf_dvd_of_pow_eq_one e3
    rw [C.orderOf_x₁] at this
    omega
  have hx₂2 : C.D.x₂⁻¹ ≠ C.D.x₂ := by
    intro e
    have e3 : C.D.x₂ ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← e]
      exact inv_mul_cancel _
    have := orderOf_dvd_of_pow_eq_one e3
    rw [C.orderOf_x₂] at this
    omega
  have htx₁ : C.D.F.ρ'.r * C.D.x₁ * C.D.F.ρ'.r⁻¹ = C.D.x₁ := by
    rw [(C.commutes_R_R' _ C.x₁_mem_R _ C.t_mem_R').symm]
    group
  rcases hn with rfl | rfl | rfl | rfl
  · rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have e := (hxm v hv).trans (hact v hv)
    calc v * x = x * v * x⁻¹ * x := by rw [e]; group
      _ = x * v := by group
  · exact absurd (hm1.symm.trans ((hact _ C.D.x₁_mem).trans C.D.r₁)).symm hx₁2
  · exact absurd (hm2.symm.trans ((hact _ C.D.x₂_mem).trans C.D.t₂)).symm hx₂2
  · have e : C.D.F.ρ.r * C.D.F.ρ'.r * C.D.x₁ * (C.D.F.ρ.r * C.D.F.ρ'.r)⁻¹ = C.D.x₁⁻¹ := by
      calc C.D.F.ρ.r * C.D.F.ρ'.r * C.D.x₁ * (C.D.F.ρ.r * C.D.F.ρ'.r)⁻¹
          = C.D.F.ρ.r * (C.D.F.ρ'.r * C.D.x₁ * C.D.F.ρ'.r⁻¹) * C.D.F.ρ.r⁻¹ := by group
        _ = C.D.x₁⁻¹ := by rw [htx₁, C.D.r₁]
    exact absurd (hm1.symm.trans ((hact _ C.D.x₁_mem).trans e)).symm hx₁2

include C in
theorem conj_R_cases {h : G} (hh : h ∈ Subgroup.centralizer ({z} : Set G))
    (hR : conjSub h R ≤ (S : Subgroup G)) (hR' : conjSub h R' ≤ (S : Subgroup G)) :
    (conjSub h R = R ∧ conjSub h R' = R') ∨ (conjSub h R = R' ∧ conjSub h R' = R) := by
  have h8R : Nat.card ↥(conjSub h R) = 8 := by rw [card_conjSub, C.h8]
  have h8R' : Nat.card ↥(conjSub h R') = 8 := by
    rw [card_conjSub, C.card_R', Nat.card_zpowers, C.orderOf_x₂]
  rcases twin_cases C hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have hRK : conjSub h R ≤ K := h1 ▸ conjSub_mono C.hd.hR.2.1
    have hR'K : conjSub h R' ≤ K' := h2 ▸ conjSub_mono C.hd.hR'.2.1
    constructor
    · have hle : conjSub h R ≤ R := (le_inf hRK hR).trans (le_of_eq C.inf_S_eq_R)
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [h8R, C.h8])
    · have hle : conjSub h R' ≤ R' := (le_inf hR'K hR').trans (le_of_eq C.inf_S_eq_R')
      exact Subgroup.eq_of_le_of_card_ge hle (by
        rw [h8R', C.card_R', Nat.card_zpowers, C.orderOf_x₂])
  · right
    have hRK : conjSub h R ≤ K' := h1 ▸ conjSub_mono C.hd.hR.2.1
    have hR'K : conjSub h R' ≤ K := h2 ▸ conjSub_mono C.hd.hR'.2.1
    constructor
    · have hle : conjSub h R ≤ R' := (le_inf hRK hR).trans (le_of_eq C.inf_S_eq_R')
      exact Subgroup.eq_of_le_of_card_ge hle (by
        rw [h8R, C.card_R', Nat.card_zpowers, C.orderOf_x₂])
    · have hle : conjSub h R' ≤ R := (le_inf hR'K hR').trans (le_of_eq C.inf_S_eq_R)
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [h8R', C.h8])

include C in
theorem hfus_I [IsSimpleGroup G] (h3 : S24B.H3 p f) {e : G} (heS₀ : e ∉ sZero Ω W S)
    (he2 : e * e = 1) (heR : ∀ v ∈ R, v * e = e * v) (heR' : ∀ v ∈ R', v * e = e * v) (g : G)
    (hg : ∀ y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer {e}, g⁻¹ * y * g ∈ (S : Subgroup G)) :
    g⁻¹ * e * g ∉ sZero Ω W S := by
  intro hx
  have hst := C.hs.stand
  have hzR : R ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set G) := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (centralizes_conj_z (z_mem_S C) hg (C.hd.hR.2.2 hv) (heR v hv))
  have hzh : g * z * g⁻¹ = z := by
    by_contra hne
    exact C.ne_conj_z hst.mem C.hRsyl C.hzK hzR hne g rfl
  have hgz : g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [hzh]
  have hgz' : g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.inv_mem _ hgz
  have hRS : conjSub g⁻¹ R ≤ (S : Subgroup G) := by
    rintro _ ⟨v, hv, rfl⟩
    have := hg v ⟨C.hd.hR.2.2 hv, Subgroup.mem_centralizer_singleton_iff.mpr (heR v hv)⟩
    simpa using this
  have hR'S : conjSub g⁻¹ R' ≤ (S : Subgroup G) := by
    rintro _ ⟨v, hv, rfl⟩
    have := hg v ⟨C.hd.hR'.2.2 hv, Subgroup.mem_centralizer_singleton_iff.mpr (heR' v hv)⟩
    simpa using this
  set x := g⁻¹ * e * g with hxdef
  have hxc : ∀ v, (v ∈ R ∨ v ∈ R') → v * x = x * v := by
    intro v hv
    have hv' : g * v * g⁻¹ ∈ R ∨ g * v * g⁻¹ ∈ R' := by
      rcases conj_R_cases C hgz' hRS hR'S with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases hv with hv | hv
        · left
          rw [← h1, mem_conjSub_iff] at hv
          simpa using hv
        · right
          rw [← h2, mem_conjSub_iff] at hv
          simpa using hv
      · rcases hv with hv | hv
        · right
          rw [← h2, mem_conjSub_iff] at hv
          simpa using hv
        · left
          rw [← h1, mem_conjSub_iff] at hv
          simpa using hv
    have hc : (g * v * g⁻¹) * e = e * (g * v * g⁻¹) := by
      rcases hv' with h | h
      · exact heR _ h
      · exact heR' _ h
    calc v * x = g⁻¹ * ((g * v * g⁻¹) * e) * g := by rw [hxdef]; group
      _ = g⁻¹ * (e * (g * v * g⁻¹)) * g := by rw [hc]
      _ = x * v := by rw [hxdef]; group
  have hx1 : x * C.D.x₁ * x⁻¹ = C.D.x₁ := by
    rw [← hxc _ (Or.inl C.x₁_mem_R)]; group
  have hx2 : x * C.D.x₂ * x⁻¹ = C.D.x₂ := by
    rw [← hxc _ (Or.inr C.x₂_mem_R')]; group
  have hxW := mem_centralizer_W_of_sZero C hx hx1 hx2
  have hxS : x ∈ (S : Subgroup G) := hx.1
  have hxA : x ∈ C.A := by
    refine (C.mem_A).mpr ⟨hxS, hxW, ?_, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact hxc v (Or.inl hv)
    · exact mem_normalizer_iff_conjSub_eq.mpr (S24B.conjSub_eq_of_commute hst.hyp C.hs.hK'.1
        C.x₂_mem_K' C.orderOf_x₂ (hxc _ (Or.inr C.x₂_mem_R')).symm)
    · exact mem_normalizer_iff_conjSub_eq.mpr (S24B.conjSub_eq_of_commute hst.hyp
        C.D.F.ρ₃.hK C.x₃_mem_J C.orderOf_x₃
        (Subgroup.mem_centralizer_iff.mp hxW _ C.D.x₃_mem).symm)
  have hxD : x ∈ C.Dg := ⟨hxA, by
    show x ∈ Subgroup.centralizer (R' : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hxc v (Or.inr hv)⟩
  obtain ⟨μ, hμ⟩ := C.exists_inj_D h3
  have hx2' : x * x = 1 := by
    rw [hxdef]
    calc g⁻¹ * e * g * (g⁻¹ * e * g) = g⁻¹ * (e * e) * g := by group
      _ = 1 := by rw [he2]; group
  have he1 : e ≠ 1 := fun h => heS₀ (h ▸ Subgroup.one_mem _)
  have hx1' : x ≠ 1 := by
    intro h
    apply he1
    calc e = g * x * g⁻¹ := by rw [hxdef]; group
      _ = 1 := by rw [h]; group
  have hxz : (⟨x, hxD⟩ : ↥C.Dg) = ⟨z, C.z_mem_Dg⟩ :=
    eq_of_inj_zpowers C.orderOf_x₃ hμ (Subtype.ext hx2') (fun h => hx1' (congrArg Subtype.val h))
      (Subtype.ext C.hzK.sq) (fun h => C.hzK.ne_one (congrArg Subtype.val h))
  have hxz' : x = z := congrArg Subtype.val hxz
  apply heS₀
  have he : e = z := by
    calc e = g * x * g⁻¹ := by rw [hxdef]; group
      _ = z := by rw [hxz', hzh]
  rw [he]
  exact inf_le_sZero (C.W_le_P C.hd.hzW)

include C in
theorem card_R'_eq : Nat.card ↥R' = 8 := by
  rw [C.card_R', Nat.card_zpowers, C.orderOf_x₂]

include C in
theorem hR'syl : IsSylow2In R' K' :=
  T7C.isSylow2In_of_mem_RSet_of_le C.hs.stand.odd C.hs.stand.hyp C.hs.hK'.1 C.hd.hR'.1
    C.hd.hR'.2.1

include C in
theorem innerOn_R'_of_commute {y : G} (hyS : y ∈ (S : Subgroup G)) (hyK : conjSub y K' = K')
    (hyy : y * y = 1) {b : G} (hbK : b ∈ K') (hb : orderOf b = 4) (hyb : y * b = b * y) :
    InnerOn y R' :=
  innerOn_of_commute (hR'syl C) (card_R'_eq C)
    (inv_of_member C.hs.stand.odd C.hs.stand.hyp C.hs.hK'.1 C.hzK' (hR'syl C) (card_R'_eq C))
    (mem_normalizer_iff_conjSub_eq.mpr hyK) (conj_mem_R' C hyS hyK) hyy hbK hb hyb

include C in
theorem innerOn_R_of_commute {y : G} (hyS : y ∈ (S : Subgroup G)) (hyK : conjSub y K = K)
    (hyy : y * y = 1) {b : G} (hbK : b ∈ K) (hb : orderOf b = 4) (hyb : y * b = b * y) :
    InnerOn y R :=
  innerOn_of_commute C.hRsyl C.h8
    (inv_of_member C.hs.stand.odd C.hs.stand.hyp C.hs.stand.mem C.hzK C.hRsyl C.h8)
    (mem_normalizer_iff_conjSub_eq.mpr hyK) (conj_mem_R C hyS hyK) hyy hbK hb hyb

include C in
theorem exists_fix_R {y : G} (h : InnerOn y R) :
    ∃ b ∈ R, orderOf b = 4 ∧ y * b * y⁻¹ = b :=
  exists_fix_of_innerOn (Subgroup.zpowers_le.mpr C.x₁_mem_R) C.orderOf_x₁
    (orderOf_of_member C.hs.stand.odd C.hs.stand.hyp C.hs.stand.mem C.hzK C.hRsyl C.x₁_mem_R
      C.card_R) h

include C in
theorem exists_fix_R' {y : G} (h : InnerOn y R') :
    ∃ b ∈ R', orderOf b = 4 ∧ y * b * y⁻¹ = b :=
  exists_fix_of_innerOn (Subgroup.zpowers_le.mpr C.x₂_mem_R') C.orderOf_x₂
    (orderOf_of_member C.hs.stand.odd C.hs.stand.hyp C.hs.hK'.1 C.hzK' (hR'syl C) C.x₂_mem_R'
      C.card_R') h

include C in
theorem eq_one_or_z_of_mem_inf {v : G} (hvK : v ∈ K) (hvK' : v ∈ K')
    (hv2 : IsPGroup 2 ↥(Subgroup.zpowers v)) : v = 1 ∨ v = z := by
  have hst := C.hs.stand
  have hcard := hst.hyp.card_le_two_of_le_inf hst.mem C.hs.hK'.1 C.hs.hne.symm hv2
    (Subgroup.zpowers_le.mpr hvK) (Subgroup.zpowers_le.mpr hvK')
  rw [Nat.card_zpowers] at hcard
  have hvv : v * v = 1 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hv2) ⟨v, Subgroup.mem_zpowers v⟩
    rw [Subgroup.orderOf_mk] at hk
    have h2 : orderOf v ∣ 2 := by
      rcases k with _ | _ | k
      · rw [hk]; norm_num
      · rw [hk]; norm_num
      · exfalso
        rw [hk] at hcard
        have h4 : (4 : ℕ) ≤ 2 ^ (k + 1 + 1) := by
          calc (4 : ℕ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    have := orderOf_dvd_iff_pow_eq_one.mp h2
    rwa [pow_two] at this
  exact C.hzK'.unique v hvK' hvv

include C in
theorem innerOn_R'_of_conj_z {c : G} (hcS : c ∈ (S : Subgroup G)) (hcK' : conjSub c K' = K')
    (hc2 : c * c = 1) (hcr : c * C.D.F.ρ.r = C.D.F.ρ.r * c) {g : G}
    (hne : g * z * g⁻¹ ≠ z) (hzr : (g * z * g⁻¹) * C.D.F.ρ.r = C.D.F.ρ.r * (g * z * g⁻¹))
    (hzc : c * (g * z * g⁻¹) = (g * z * g⁻¹) * c) : InnerOn c R' := by
  have hst := C.hs.stand
  have hp : p ≠ 2 := hst.odd
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hzhK := mem_sup_of_conj_z C hne hzr
  have hzh2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [C.hzK.sq]; group
  have hzh1 : g * z * g⁻¹ ≠ 1 := by
    intro h
    apply C.hzK.ne_one
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  generalize g * z * g⁻¹ = zh at hne hzr hzc hzhK hzh2 hzh1
  have hor : orderOf C.D.F.ρ.r = 4 :=
    orderOf_of_member hp hΩ hst.mem C.hzK C.hRsyl C.x₁_mem_R C.card_R C.D.F.ρ.r C.r_mem_R
      C.r_not_mem_zpowers
  have hr2 : IsPGroup 2 ↥(Subgroup.zpowers C.D.F.ρ.r) := T7A.isPGroup_zpowers_of_orderOf_four hor
  have hzh2' : IsPGroup 2 ↥(Subgroup.zpowers zh) := isPGroup_zpowers_of_mul_self hzh2
  have hN : Subgroup.zpowers C.D.F.ρ.r ≤
      Subgroup.normalizer ((Subgroup.zpowers zh : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_left hzr i).eq
  have hY := hr2.to_sup_of_normal_right' hzh2' hN
  have hYK : Subgroup.zpowers C.D.F.ρ.r ⊔ Subgroup.zpowers zh ≤ K ⊔ K' :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left C.r_mem_K))
      (Subgroup.zpowers_le.mpr hzhK)
  obtain ⟨R₂, R₂', hR₂, hR₂', hc₂, hYR⟩ := exists_sylow_pair_of_le C hY hYK
  have hle : R₂ ≤ Subgroup.normalizer ((R₂' : Subgroup G) : Set G) := by
    intro v hv
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (hc₂ v hv w hw).symm
  have hcoe : ((R₂ ⊔ R₂' : Subgroup G) : Set G) = (R₂ : Set G) * (R₂' : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right R₂ R₂' hle
  have hdec : ∀ v ∈ R₂ ⊔ R₂', ∃ a ∈ R₂, ∃ b ∈ R₂', v = a * b := by
    intro v hv
    have hv' : v ∈ ((R₂ ⊔ R₂' : Subgroup G) : Set G) := hv
    rw [hcoe] at hv'
    obtain ⟨a, ha, b, hb, rfl⟩ := hv'
    exact ⟨a, ha, b, hb, rfl⟩
  have hzR₂ : z ∈ R₂ := T7C.mem_of_isSylow2In hp hΩ hst.mem hR₂ C.hzK
  have h8R₂ : Nat.card ↥R₂ = 8 := by rw [hR₂.natCard_eq C.hRsyl, C.h8]
  have hrR₂ : C.D.F.ρ.r ∈ R₂ := by
    obtain ⟨a₀, ha₀, b₀, hb₀, he₀⟩ :=
      hdec _ (hYR (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
    have hb₀K : b₀ ∈ K := by
      have e : b₀ = a₀⁻¹ * C.D.F.ρ.r := by rw [he₀]; group
      rw [e]
      exact K.mul_mem (K.inv_mem (hR₂.1 ha₀)) C.r_mem_K
    have hb₀2 : IsPGroup 2 ↥(Subgroup.zpowers b₀) := hR₂'.2.1.to_le (Subgroup.zpowers_le.mpr hb₀)
    rcases eq_one_or_z_of_mem_inf C hb₀K (hR₂'.1 hb₀) hb₀2 with h | h
    · rw [he₀, h, mul_one]; exact ha₀
    · rw [he₀, h]; exact R₂.mul_mem ha₀ hzR₂
  obtain ⟨a, ha, b, hb, hab⟩ := hdec _ (hYR (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
  have hcab : a * b = b * a := hc₂ a ha b hb
  have hbr : b * C.D.F.ρ.r = C.D.F.ρ.r * b := (hc₂ _ hrR₂ b hb).symm
  have har : a * C.D.F.ρ.r = C.D.F.ρ.r * a := by
    have e : a * b * C.D.F.ρ.r = C.D.F.ρ.r * (a * b) := by rw [← hab]; exact hzr
    have e2 : a * C.D.F.ρ.r * b = C.D.F.ρ.r * a * b := by
      calc a * C.D.F.ρ.r * b = a * (b * C.D.F.ρ.r) := by rw [mul_assoc, hbr]
        _ = C.D.F.ρ.r * a * b := by rw [← mul_assoc, e, mul_assoc]
    exact mul_right_cancel e2
  have haa : a * a * (b * b) = 1 := by
    calc a * a * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hcab]
      _ = (a * b) * (a * b) := by group
      _ = 1 := by rw [← hab]; exact hzh2
  have ha2K' : a * a ∈ K' := by
    have e : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left haa
    rw [e]
    exact K'.inv_mem (K'.mul_mem (hR₂'.1 hb) (hR₂'.1 hb))
  have ha22 : IsPGroup 2 ↥(Subgroup.zpowers (a * a)) :=
    hR₂.2.1.to_le (Subgroup.zpowers_le.mpr (R₂.mul_mem ha ha))
  have haz : a * a = z := by
    rcases eq_one_or_z_of_mem_inf C (hR₂.1 (R₂.mul_mem ha ha)) ha2K' ha22 with h | h
    · exfalso
      rcases C.hzK.unique a (hR₂.1 ha) h with h1 | h1
      · apply hne
        have hbK' : zh ∈ K' := by rw [hab, h1, one_mul]; exact hR₂'.1 hb
        rcases C.hzK'.unique zh hbK' hzh2 with h2 | h2
        · exact absurd h2 hzh1
        · exact h2
      · apply hne
        have hbK' : zh ∈ K' := by rw [hab, h1]; exact K'.mul_mem C.hzK'.mem (hR₂'.1 hb)
        rcases C.hzK'.unique zh hbK' hzh2 with h2 | h2
        · exact absurd h2 hzh1
        · exact h2
    · exact h
  have hbb : b * b = z := by
    have e : b * b = (a * a)⁻¹ := eq_inv_of_mul_eq_one_right haa
    rw [e, haz]
    exact inv_eq_of_mul_eq_one_right C.hzK.sq
  have hU : Subgroup.zpowers C.D.F.ρ.r ≤ R₂ := Subgroup.zpowers_le.mpr hrR₂
  have haU : a ∈ Subgroup.zpowers C.D.F.ρ.r := by
    by_contra haU
    have e := inv_of_member hp hΩ hst.mem C.hzK C.hRsyl C.h8 R₂ hR₂ C.D.F.ρ.r hrR₂ hor a ha haU
    rw [har, mul_inv_cancel_right] at e
    have e2 : C.D.F.ρ.r ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [e]
      exact mul_inv_cancel _
    have := orderOf_dvd_of_pow_eq_one e2
    rw [hor] at this
    omega
  have hca : c * a = a * c := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp haU
    exact (Commute.zpow_right hcr i).eq
  have hcb : c * b = b * c := by
    have e : b = a⁻¹ * zh := by rw [hab]; group
    rw [e]
    have hca' : c * a⁻¹ = a⁻¹ * c := by
      calc c * a⁻¹ = a⁻¹ * (a * c) * a⁻¹ := by group
        _ = a⁻¹ * (c * a) * a⁻¹ := by rw [hca]
        _ = a⁻¹ * c := by group
    calc c * (a⁻¹ * zh) = a⁻¹ * (c * zh) := by rw [← mul_assoc, hca', mul_assoc]
      _ = a⁻¹ * zh * c := by rw [hzc, mul_assoc]
  have hbo : orderOf b = 4 := by
    have h4 : orderOf b = 2 ^ (1 + 1) := by
      refine orderOf_eq_prime_pow ?_ ?_
      · rw [pow_one, pow_two, hbb]
        exact C.hzK.ne_one
      · rw [show (2 : ℕ) ^ (1 + 1) = 2 + 2 by norm_num, pow_add, pow_two, hbb]
        exact C.hzK.sq
    rw [h4]
    norm_num
  exact innerOn_R'_of_commute C hcS hcK' hc2 (hR₂'.1 hb) hbo hcb

include C in
theorem hfus_II {c : G} (hcS : c ∈ (S : Subgroup G)) (hc2 : c * c = 1)
    (hcr : c * C.D.F.ρ.r = C.D.F.ρ.r * c) (hcK : conjSub c K = K)
    (hcout : ¬ InnerOn c R') (hA : ∀ a ∈ C.A, InnerOn a R') (g : G)
    (hg : ∀ y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer {c}, g⁻¹ * y * g ∈ (S : Subgroup G)) :
    g⁻¹ * c * g ∉ sZero Ω W S := by
  intro hx
  have hst := C.hs.stand
  have hcK' : conjSub c K' = K' := C.conjSub_K'_of_K hcK
  have hcK'4 : ∀ b ∈ K', orderOf b = 4 → c * b ≠ b * c := fun b hb hb4 hcb =>
    hcout (innerOn_R'_of_commute C hcS hcK' hc2 hb hb4 hcb)
  have hrS : C.D.F.ρ.r ∈ (S : Subgroup G) := C.hd.hR.2.2 C.r_mem_R
  have hzr := centralizes_conj_z (z_mem_S C) hg hrS hcr.symm
  have hzc := centralizes_conj_z (z_mem_S C) hg hcS rfl
  have hzh : g * z * g⁻¹ = z := by
    by_contra hne
    exact hcout (innerOn_R'_of_conj_z C hcS hcK' hc2 hcr hne hzr.symm hzc)
  have hgz : g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [hzh]
  have hgz' : g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.inv_mem _ hgz
  set x := g⁻¹ * c * g with hxdef
  have hxS : x ∈ (S : Subgroup G) := hx.1
  have hx2 : x * x = 1 := by
    rw [hxdef]
    calc g⁻¹ * c * g * (g⁻¹ * c * g) = g⁻¹ * (c * c) * g := by group
      _ = 1 := by rw [hc2]; group
  set r' := g⁻¹ * C.D.F.ρ.r * g with hr'def
  have hr'S : r' ∈ (S : Subgroup G) :=
    hg _ ⟨hrS, Subgroup.mem_centralizer_singleton_iff.mpr hcr.symm⟩
  have hxr' : x * r' = r' * x := by
    rw [hxdef, hr'def]
    calc g⁻¹ * c * g * (g⁻¹ * C.D.F.ρ.r * g) = g⁻¹ * (c * C.D.F.ρ.r) * g := by group
      _ = g⁻¹ * (C.D.F.ρ.r * c) * g := by rw [hcr]
      _ = g⁻¹ * C.D.F.ρ.r * g * (g⁻¹ * c * g) := by group
  have hor : orderOf C.D.F.ρ.r = 4 :=
    orderOf_of_member hst.odd hst.hyp hst.mem C.hzK C.hRsyl C.x₁_mem_R C.card_R C.D.F.ρ.r
      C.r_mem_R C.r_not_mem_zpowers
  have hor' : orderOf r' = 4 := by
    rw [hr'def, show g⁻¹ * C.D.F.ρ.r * g = g⁻¹ * C.D.F.ρ.r * g⁻¹⁻¹ by rw [inv_inv],
      orderOf_conj', hor]
  have hr'K : r' ∈ conjSub g⁻¹ K := by
    rw [hr'def, show g⁻¹ * C.D.F.ρ.r * g = g⁻¹ * C.D.F.ρ.r * g⁻¹⁻¹ by rw [inv_inv]]
    exact conj_mem_conjSub C.r_mem_K
  have hxno : ∀ b ∈ conjSub g⁻¹ K', orderOf b = 4 → x * b ≠ b * x := by
    intro b hb hb4 hxb
    rw [mem_conjSub_iff, inv_inv] at hb
    refine hcK'4 _ hb (by rw [orderOf_conj', hb4]) ?_
    calc c * (g * b * g⁻¹) = g * (x * b) * g⁻¹ := by rw [hxdef]; group
      _ = g * (b * x) * g⁻¹ := by rw [hxb]
      _ = g * b * g⁻¹ * c := by rw [hxdef]; group
  have hxinv : x * r' * x⁻¹ = r' := by rw [hxr', mul_inv_cancel_right]
  rcases twin_cases C hgz' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    have hr'K' : r' ∈ K := h1 ▸ hr'K
    have hr'R : r' ∈ R := (le_of_eq C.inf_S_eq_R) ⟨hr'K', hr'S⟩
    have hxK : conjSub x K = K :=
      S24B.conjSub_eq_of_commute hst.hyp hst.mem hr'K' hor' hxr'
    have hxK' : conjSub x K' = K' := C.conjSub_K'_of_K hxK
    have hin : InnerOn x R :=
      innerOn_R_of_commute C hxS hxK hx2 hr'K' hor' hxr'
    have hout : ¬ InnerOn x R' := by
      intro h
      obtain ⟨b, hbR', hb4, hxb⟩ := exists_fix_R' C h
      apply hxno b (by rw [h2]; exact C.hd.hR'.2.1 hbR') hb4
      calc x * b = x * b * x⁻¹ * x := by group
        _ = b * x := by rw [hxb]
    exact hout ((parity_eq C hA hx hxK).mp hin)
  ·
    have hr'K' : r' ∈ K' := h1 ▸ hr'K
    have hr'R' : r' ∈ R' := (le_of_eq C.inf_S_eq_R') ⟨hr'K', hr'S⟩
    have hxK' : conjSub x K' = K' :=
      S24B.conjSub_eq_of_commute hst.hyp C.hs.hK'.1 hr'K' hor' hxr'
    have hxK : conjSub x K = K := by
      rcases S24B.Ctx8.conjSub_K_mem C hxS with h | h
      · exact h
      · exfalso
        apply C.hs.hne
        have e : conjSub x K = conjSub x K' := by rw [h, hxK']
        exact ((conjSub_inj x).mp e).symm
    have hin : InnerOn x R' :=
      innerOn_R'_of_commute C hxS hxK' hx2 hr'K' hor' hxr'
    have hout : ¬ InnerOn x R := by
      intro h
      obtain ⟨b, hbR, hb4, hxb⟩ := exists_fix_R C h
      apply hxno b (by rw [h2]; exact C.hd.hR.2.1 hbR) hb4
      calc x * b = x * b * x⁻¹ * x := by group
        _ = b * x := by rw [hxb]
    exact hout ((parity_eq C hA hx hxK).mpr hin)

end Ctx

end S24

end CFSG.ClassicalInvolution.Asc77
