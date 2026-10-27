module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Delta
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Iii630Facts
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Iii630Group
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Main

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

section R10D2

open CFSG.Open CFSG.ABGLocalTools CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem r10a32_comm_zpowers {a b : G} (hab : Commute a b) :
    ∀ h ∈ Subgroup.zpowers b, h * a = a * h := by
  intro h hh
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact ((hab.zpow_right m).symm).eq

theorem centralizer_le_of_prop614 {M : Subgroup G} {x z y : G} {T : Subgroup G}
    (hyS : y ∈ smallRankS x T) (hy1 : y ≠ 1) (hzy : z * y = y * z)
    (hP614 : ∀ S₀ : Subgroup G, S₀ ≤ smallRankS x T → S₀ ≠ ⊥ →
      zpowers z ≤ normalizer (S₀ : Set G) → normalizer (S₀ : Set G) ≤ M) :
    centralizer ({y} : Set G) ≤ M := by
  have hS : zpowers y ≤ smallRankS x T := Subgroup.zpowers_le.mpr hyS
  have hne : zpowers y ≠ ⊥ := by
    intro h
    have hy : y ∈ zpowers y := Subgroup.mem_zpowers y
    rw [h] at hy
    exact hy1 (Subgroup.mem_bot.mp hy)
  have hzc : z ∈ centralizer ((zpowers y : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (r10a32_comm_zpowers (hzy : Commute z y))
  have hzN : zpowers z ≤ normalizer ((zpowers y : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hzc)
  have hM := hP614 (zpowers y) hS hne hzN
  intro g hg
  have hyg : y * g = g * y := Subgroup.mem_centralizer_iff.mp hg y (Set.mem_singleton y)
  have hgc : g ∈ centralizer ((zpowers y : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (r10a32_comm_zpowers (hyg.symm : Commute g y))
  exact hM (Subgroup.centralizer_le_normalizer _ hgc)

end R10D2

section R10D1

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem r10a31_norm_C {F : Subgroup G} {n c : G}
    (hn : n ∈ normalizer (F : Set G)) (hc : c ∈ centralizer (F : Set G)) :
    n * c * n⁻¹ ∈ centralizer (F : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro h hh
  have hk : n⁻¹ * h * n ∈ F := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) h).mp hh
    rwa [inv_inv] at h1
  have hck := hc _ hk
  calc h * (n * c * n⁻¹) = n * ((n⁻¹ * h * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * h * n)) * n⁻¹ := by rw [hck]
    _ = n * c * n⁻¹ * h := by group

private theorem r10a31_pow_eq_one {r : ℕ} {g : G} (hP : IsPGroup r (zpowers g)) :
    ∃ e : ℕ, g ^ (r ^ e) = 1 := by
  obtain ⟨e, he⟩ := hP ⟨g, Subgroup.mem_zpowers g⟩
  exact ⟨e, by simpa using congrArg Subtype.val he⟩

private theorem r10a31_pow_eq_one_of_mem {V : Subgroup G} {r : ℕ} (hV : IsPGroup r V)
    {u : G} (hu : u ∈ V) : ∃ e : ℕ, u ^ (r ^ e) = 1 := by
  obtain ⟨e, he⟩ := hV ⟨u, hu⟩
  exact ⟨e, by simpa using congrArg Subtype.val he⟩

private theorem r10a31_coprime_six {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) :
    Nat.Coprime r 6 := by
  have h2 : Nat.Coprime r 2 := (Nat.coprime_primes hr Nat.prime_two).mpr hr2
  have h3 : Nat.Coprime r 3 := (Nat.coprime_primes hr Nat.prime_three).mpr hr3
  exact Nat.Coprime.mul_right h2 h3

private theorem r10a31_orderOf_coprime {g : G} {r e : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) (hg : g ^ (r ^ e) = 1) : Nat.Coprime (orderOf g) 6 :=
  Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hg)
    (Nat.Coprime.pow_left e (r10a31_coprime_six hr hr2 hr3))

private theorem r10a31_not_three_dvd {n : ℕ} (h : Nat.Coprime n 6) : ¬ 3 ∣ n := by
  have h3 : Nat.Coprime n 3 := Nat.Coprime.coprime_dvd_right (by norm_num) h
  exact (Nat.prime_three.coprime_iff_not_dvd).mp h3.symm

private theorem r10a31_orderOf_conj (b h : G) : orderOf (b * h * b⁻¹) = orderOf h := by
  have := MulEquiv.orderOf_eq (MulAut.conj b) h
  simpa only [MulAut.conj_apply] using this

private theorem r10a31_normalizer_zpowers {u b : G} (hb : Commute b u) :
    b ∈ normalizer (zpowers u : Set G) := by
  have key : ∀ c : G, Commute c u → ∀ k : ℤ, c * u ^ k * c⁻¹ = u ^ k := by
    intro c hc k
    rw [mul_inv_eq_iff_eq_mul]
    exact (hc.zpow_right k).eq
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← hk, key b hb k]
    exact Subgroup.zpow_mem_zpowers u k
  · intro hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    have h2 : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = u ^ k := by
      rw [← hk]
      exact key b⁻¹ hb.inv_left k
    have h3 : h = b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ := by group
    rw [h3, h2]
    exact Subgroup.zpow_mem_zpowers u k

private theorem r10a31_threeComplement {M S₀ : Subgroup G} {x z : G}
    (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hz3 : z ^ 3 = 1) (hxz : x * z = z * x)
    (hxM : x ∈ M) (hBM : zpowers x ⊔ zpowers z ≤ M)
    (hCxB : IsSylowOf 3 (zpowers x ⊔ zpowers z) (centralizer ({x} : Set G)))
    (hS0N : ∀ g ∈ M ⊓ centralizer ({x} : Set G), g ∈ normalizer (S₀ : Set G))
    (hxS0 : x ∈ centralizer (S₀ : Set G)) (hzS0 : z ∉ centralizer (S₀ : Set G)) :
    ∃ W : Subgroup G,
      (∀ g : G, g ∈ W ↔ (g ∈ M ⊓ centralizer ({x} : Set G) ⊓ centralizer (S₀ : Set G) ∧
        ¬ 3 ∣ orderOf g)) ∧ ¬ 3 ∣ Nat.card W ∧
      zpowers x ⊔ zpowers z ≤ normalizer (W : Set G) := by
  have hxCx : x ∈ centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun h hh => by rw [Set.mem_singleton_iff.mp hh])
  have hzCx : z ∈ centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]
      exact hxz)
  have hBCx : zpowers x ⊔ zpowers z ≤ centralizer ({x} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hxCx) (Subgroup.zpowers_le.mpr hzCx)
  have hBY : zpowers x ⊔ zpowers z ≤ M ⊓ centralizer ({x} : Set G) := le_inf hBM hBCx
  have hsyl : IsSylowOf 3 (zpowers x ⊔ zpowers z) (M ⊓ centralizer ({x} : Set G)) :=
    isSylowOf_of_le_of_le hCxB hBY inf_le_right
  have hxY : x ∈ M ⊓ centralizer ({x} : Set G) := Subgroup.mem_inf.mpr ⟨hxM, hxCx⟩
  have hzB : z ∈ zpowers x ⊔ zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hzY : z ∈ M ⊓ centralizer ({x} : Set G) := hBY hzB
  have hxY0 : x ∈ M ⊓ centralizer ({x} : Set G) ⊓ centralizer (S₀ : Set G) :=
    Subgroup.mem_inf.mpr ⟨hxY, hxS0⟩
  have hxc : ∀ g ∈ M ⊓ centralizer ({x} : Set G) ⊓ centralizer (S₀ : Set G),
      g * x = x * g := by
    intro g hg
    exact (Subgroup.mem_centralizer_iff.mp hg.1.2 x (Set.mem_singleton x)).symm
  have hnorm : ∀ g ∈ M ⊓ centralizer ({x} : Set G), ∀ w ∈ M ⊓ centralizer ({x} : Set G) ⊓
      centralizer (S₀ : Set G), g * w * g⁻¹ ∈ M ⊓ centralizer ({x} : Set G) ⊓
      centralizer (S₀ : Set G) := by
    intro g hg w hw
    have hgM : g ∈ M := hg.1
    have hgC : g ∈ centralizer ({x} : Set G) := hg.2
    have hwM : w ∈ M := hw.1.1
    have hwC : w ∈ centralizer ({x} : Set G) := hw.1.2
    have hwS : w ∈ centralizer (S₀ : Set G) := hw.2
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · exact mul_mem (mul_mem hgM hwM) (inv_mem hgM)
    · exact mul_mem (mul_mem hgC hwC) (inv_mem hgC)
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hgs : g⁻¹ * s * g ∈ S₀ := ((Subgroup.mem_normalizer_iff''.mp (hS0N g hg)) s).mp hs
    have hcomm := Subgroup.mem_centralizer_iff.mp hwS (g⁻¹ * s * g) hgs
    calc s * (g * w * g⁻¹) = g * ((g⁻¹ * s * g) * w) * g⁻¹ := by group
      _ = g * (w * (g⁻¹ * s * g)) * g⁻¹ := by rw [hcomm]
      _ = g * w * g⁻¹ * s := by group
  have hBY0 : (zpowers x ⊔ zpowers z) ⊓ (M ⊓ centralizer ({x} : Set G) ⊓
      centralizer (S₀ : Set G)) ≤ zpowers x := by
    intro b hb
    exact mem_zpowers_of_mem_plane_of_mem_centralizer hxz hxS0 hz3 hzS0 hb.1 hb.2.2
  have hY0Y : M ⊓ centralizer ({x} : Set G) ⊓ centralizer (S₀ : Set G) ≤
      M ⊓ centralizer ({x} : Set G) := inf_le_left
  have hsylQ := card_dvd_three_of_le_normal hx1 hx3 hY0Y hnorm hsyl hBY0
  obtain ⟨W, hWmem, hW3⟩ := exists_threeComplement hx1 hx3 hxY0 hxc hsylQ
  have hconj : ∀ b ∈ M ⊓ centralizer ({x} : Set G), ∀ h : G,
      (h ∈ M ⊓ centralizer ({x} : Set G) ⊓ centralizer (S₀ : Set G) ∧ ¬ 3 ∣ orderOf h) →
      (b * h * b⁻¹ ∈ M ⊓ centralizer ({x} : Set G) ⊓ centralizer (S₀ : Set G) ∧
        ¬ 3 ∣ orderOf (b * h * b⁻¹)) := by
    intro b hb h hh
    refine ⟨hnorm b hb h hh.1, ?_⟩
    rw [r10a31_orderOf_conj]
    exact hh.2
  have hnW : ∀ b ∈ M ⊓ centralizer ({x} : Set G), b ∈ normalizer (W : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact (hWmem _).mpr (hconj b hb h ((hWmem h).mp hh))
    · intro hh
      have h' := hconj b⁻¹ (inv_mem hb) (b * h * b⁻¹) ((hWmem _).mp hh)
      have e : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = h := by group
      rw [e] at h'
      exact (hWmem h).mpr h'
  exact ⟨W, hWmem, hW3, sup_le (Subgroup.zpowers_le.mpr (hnW x hxY))
    (Subgroup.zpowers_le.mpr (hnW z hzY))⟩

private theorem r10a31_reduce {M F S₀ : Subgroup G} {x z y : G} {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hz3 : z ^ 3 = 1) (hxz : x * z = z * x)
    (hxM : x ∈ M) (hBM : zpowers x ⊔ zpowers z ≤ M)
    (hxC : x ∈ centralizer (F : Set G))
    (hCxN : centralizer ({x} : Set G) ≤ normalizer (F : Set G))
    (hCodd : ¬ 2 ∣ Nat.card (centralizer (F : Set G)))
    (hxS : IsSylowOf 3 (zpowers x) (centralizer (F : Set G)))
    (hy1 : y ≠ 1) (hy2 : y * y = 1) (hyinv : ∀ a ∈ F, y * a * y⁻¹ = a⁻¹)
    (hyM : centralizer ({y} : Set G) ≤ M)
    (hNB : IsSylowOf 3 (zpowers x ⊔ zpowers z) (normalizer (F : Set G)))
    (hCxB : IsSylowOf 3 (zpowers x ⊔ zpowers z) (centralizer ({x} : Set G)))
    (hS0 : ∀ g ∈ M ⊓ centralizer ({x} : Set G), Nat.Coprime (orderOf g) 6 →
      g ∈ centralizer (S₀ : Set G))
    (hS0N : ∀ g ∈ M ⊓ centralizer ({x} : Set G), g ∈ normalizer (S₀ : Set G))
    (hxS0 : x ∈ centralizer (S₀ : Set G)) (hzS0 : z ∉ centralizer (S₀ : Set G))
    {a : G} (haF : a ∈ F) (ha1 : a ≠ 1) {g₂ : G} (hg₂N : g₂ ∈ normalizer (F : Set G))
    (hg₂P : IsPGroup r (zpowers g₂)) (hg₂C : g₂ ∉ centralizer (F : Set G))
    (hg₂a : g₂ * a * g₂⁻¹ = a) (hodd₂ : ¬ 2 ∣ orderOf g₂) :
    ∃ V : Subgroup G, V ≤ M ⊓ centralizer ({x} : Set G) ∧ IsPGroup r V ∧
      zpowers x ⊔ zpowers z ≤ normalizer (V : Set G) ∧
      ∃ m : G, m ∈ V ∧ m ∉ centralizer (F : Set G) ∧
        ∃ a' : G, a' ∈ F ∧ a' ≠ 1 ∧ m * a' * m⁻¹ = a' := by
  obtain ⟨c, hc, hcY⟩ := exists_inv_mul_mem_of_odd hy1 hy2 hyinv hCodd hyM hx1 hx3 hxM hxC
    hxS g₂ hg₂N hodd₂
  obtain ⟨m, hm⟩ : ∃ m : G, m = c⁻¹ * g₂ := ⟨_, rfl⟩
  rw [← hm] at hcY
  have hmY : m ∈ M ⊓ centralizer ({x} : Set G) := hcY
  have hmN : m ∈ normalizer (F : Set G) := by
    rw [hm]
    exact mul_mem (Subgroup.centralizer_le_normalizer (F : Set G) (inv_mem hc)) hg₂N
  have hmC : m ∉ centralizer (F : Set G) := by
    intro h
    apply hg₂C
    have hg : g₂ = c * m := by rw [hm, mul_inv_cancel_left]
    rw [hg]
    exact mul_mem hc h
  have hcomm_g : g₂ * a = a * g₂ := mul_inv_eq_iff_eq_mul.mp hg₂a
  have hcinv : a * c⁻¹ = c⁻¹ * a := Subgroup.mem_centralizer_iff.mp (inv_mem hc) a haF
  have hma' : m * a = a * m := by
    rw [hm]
    calc c⁻¹ * g₂ * a = c⁻¹ * (g₂ * a) := mul_assoc _ _ _
      _ = c⁻¹ * (a * g₂) := by rw [hcomm_g]
      _ = (c⁻¹ * a) * g₂ := (mul_assoc _ _ _).symm
      _ = (a * c⁻¹) * g₂ := by rw [hcinv]
      _ = a * (c⁻¹ * g₂) := mul_assoc _ _ _
  have hmCom : Commute m a := hma'
  obtain ⟨e, he⟩ := r10a31_pow_eq_one hg₂P
  have hmod : m ^ (r ^ e) ∈ centralizer (F : Set G) := by
    obtain ⟨c', hc', hpow⟩ := exists_pow_inv_mul_eq (Subgroup.centralizer_le_normalizer
      (F : Set G)) (fun n hn c₁ hc₁ => r10a31_norm_C hn hc₁) hc hg₂N (r ^ e)
    rw [← hm, he, mul_one] at hpow
    rw [hpow]
    exact hc'
  obtain ⟨i, hiP, hiC⟩ := exists_pow_isPGroup_not_mem_of_pow_mem hr hmod hmC
  obtain ⟨m', hm'⟩ : ∃ m' : G, m' = m ^ i := ⟨_, rfl⟩
  rw [← hm'] at hiP hiC
  have hm'Y : m' ∈ M ⊓ centralizer ({x} : Set G) := by
    rw [hm']
    exact pow_mem hmY i
  have hm'a : m' * a * m'⁻¹ = a := by
    rw [hm']
    exact mul_inv_eq_iff_eq_mul.mpr ((hmCom.pow_left i).eq)
  obtain ⟨e', he'⟩ := r10a31_pow_eq_one hiP
  have hcop : Nat.Coprime (orderOf m') 6 := r10a31_orderOf_coprime hr hr2 hr3 he'
  have hm'W0 : m' ∈ M ⊓ centralizer ({x} : Set G) ⊓ centralizer (S₀ : Set G) :=
    Subgroup.mem_inf.mpr ⟨hm'Y, hS0 m' hm'Y hcop⟩
  obtain ⟨W, hWmem, hW3, hBW⟩ :=
    r10a31_threeComplement hx1 hx3 hz3 hxz hxM hBM hCxB hS0N hxS0 hzS0
  have hm'W : m' ∈ W := (hWmem m').mpr ⟨hm'W0, r10a31_not_three_dvd hcop⟩
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨V, hVW, hVr, hBV, w, hwW, hwV⟩ :=
    exists_invariant_sylow_conj hNB.isPGroup hBW hW3 hm'W hiP
  obtain ⟨m'', hm''⟩ : ∃ m'' : G, m'' = w⁻¹ * m' * w := ⟨_, rfl⟩
  rw [← hm''] at hwV
  have hwY0 := (hWmem w).mp hwW
  have hwN : w ∈ normalizer (F : Set G) := hCxN hwY0.1.1.2
  have hVY : V ≤ M ⊓ centralizer ({x} : Set G) := fun v hv => ((hWmem v).mp (hVW hv)).1.1
  have hm''C : m'' ∉ centralizer (F : Set G) := by
    intro h
    apply hiC
    have h1 := r10a31_norm_C hwN h
    have h2 : w * m'' * w⁻¹ = m' := by
      rw [hm'']
      group
    rwa [h2] at h1
  have hwa : w⁻¹ * a * w ∈ F := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hwN) a).mp haF
    rwa [inv_inv] at h1
  have hwa1 : w⁻¹ * a * w ≠ 1 := by
    intro h1
    apply ha1
    calc a = w * (w⁻¹ * a * w) * w⁻¹ := by group
      _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
  have hfix : m'' * (w⁻¹ * a * w) * m''⁻¹ = w⁻¹ * a * w := by
    rw [hm'']
    calc w⁻¹ * m' * w * (w⁻¹ * a * w) * (w⁻¹ * m' * w)⁻¹
        = w⁻¹ * (m' * a * m'⁻¹) * w := by group
      _ = w⁻¹ * a * w := by rw [hm'a]
  exact ⟨V, hVY, hVr, hBV, m'', hwV, hm''C, w⁻¹ * a * w, hwa, hwa1, hfix⟩

private theorem r10a31_case_f {M F V : Subgroup G} {x z m : G} {f : ℕ}
    (hfp : f.Prime) (hf5 : 5 ≤ f) (hFe : IsElemAbelian f F) (hFne : F ≠ ⊥) (hFM : F ⊓ M = ⊥)
    (hP65 : ∀ W : Subgroup G, W ≤ M → W ≠ ⊥ → Nat.Coprime (Nat.card W) 6 →
      zpowers x ⊔ zpowers z ≤ normalizer (W : Set G) → normalizer (W : Set G) ≤ M)
    (hVY : V ≤ M ⊓ centralizer ({x} : Set G)) (hVf : IsPGroup f V)
    (hVN : V ≤ normalizer (F : Set G)) (hBV : zpowers x ⊔ zpowers z ≤ normalizer (V : Set G))
    (hmV : m ∈ V) (hmC : m ∉ centralizer (F : Set G)) : False := by
  have hF : IsPGroup f F := fun g => ⟨1, Subtype.ext (by simpa using hFe.2 g.1 g.2)⟩
  obtain ⟨a, haF, ha1, hfix⟩ := exists_fixed_ne_one_of_isPGroup hfp hVf hF hFne hVN
  have hV1 : V ≠ ⊥ := by
    intro h
    apply hmC
    rw [h, Subgroup.mem_bot] at hmV
    rw [hmV]
    exact one_mem _
  have hcop : Nat.Coprime (Nat.card V) 6 := by
    haveI : Fact f.Prime := ⟨hfp⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hVf
    rw [hn]
    exact Nat.Coprime.pow_left n (r10a31_coprime_six hfp (by omega) (by omega))
  exact false_of_fixed_vector hP65 hFM (le_trans hVY inf_le_left) hV1 hcop hBV haF ha1 hfix

private theorem r10a31_case_ne {M F V : Subgroup G} {x z m a : G} {f r : ℕ}
    (hHH : KFactHallHigmanOdd) (hfp : f.Prime) (hr : r.Prime) (hrf : r ≠ f) (hr5 : 5 ≤ r)
    (hFe : IsElemAbelian f F) (hFM : F ⊓ M = ⊥)
    (hP65 : ∀ W : Subgroup G, W ≤ M → W ≠ ⊥ → Nat.Coprime (Nat.card W) 6 →
      zpowers x ⊔ zpowers z ≤ normalizer (W : Set G) → normalizer (W : Set G) ≤ M)
    (hz3 : z ^ 3 = 1) (hzN : z ∈ normalizer (F : Set G))
    (hzF : ∀ a ∈ F, z * a * z⁻¹ = a → a = 1)
    (hVr : IsPGroup r V) (hVY : V ≤ M ⊓ centralizer ({x} : Set G))
    (hVN : V ≤ normalizer (F : Set G)) (hBV : zpowers x ⊔ zpowers z ≤ normalizer (V : Set G))
    (hmV : m ∈ V) (hmC : m ∉ centralizer (F : Set G))
    (haF : a ∈ F) (ha1 : a ≠ 1) (hfix : m * a * m⁻¹ = a) : False := by
  have hr2 : r ≠ 2 := by omega
  have hr3 : r ≠ 3 := by omega
  have hzB : z ∈ zpowers x ⊔ zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hzV : z ∈ normalizer (V : Set G) := hBV hzB
  have hcomm := hHH G F V z f r hfp hr hrf hr5 hFe hVr hVN hzN hz3 hzV hzF
  obtain ⟨u, huV, hum, hzu⟩ := exists_fixed_mem_coset hr hr3 hVr hz3 hzV hcomm m hmV
  have huY := hVY huV
  have hxu : x * u = u * x := Subgroup.mem_centralizer_iff.mp huY.2 x (Set.mem_singleton x)
  have huC : u ∉ centralizer (F : Set G) := by
    intro h
    apply hmC
    have h1 := mul_mem (inv_mem h) hum
    rw [← mul_assoc, inv_mul_cancel, one_mul] at h1
    simpa using inv_mem h1
  have hu1 : u ≠ 1 := by
    intro h
    apply huC
    rw [h]
    exact one_mem _
  have hc0 : a * (u * m⁻¹) = u * m⁻¹ * a := Subgroup.mem_centralizer_iff.mp hum a haF
  have hua : u * a * u⁻¹ = a := by
    have e1 : u * a * u⁻¹ = (u * m⁻¹) * (m * a * m⁻¹) * (u * m⁻¹)⁻¹ := by group
    rw [e1, hfix, ← hc0, mul_inv_cancel_right]
  have hcom : Commute u a := mul_inv_eq_iff_eq_mul.mp hua
  have hfix0 : ∀ v ∈ zpowers u, v * a * v⁻¹ = a := by
    intro v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact mul_inv_eq_iff_eq_mul.mpr ((hcom.zpow_left k).eq)
  have hcx : Commute x u := hxu
  have hcz : Commute z u := hzu
  have hBu : zpowers x ⊔ zpowers z ≤ normalizer ((zpowers u : Subgroup G) : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (r10a31_normalizer_zpowers hcx))
      (Subgroup.zpowers_le.mpr (r10a31_normalizer_zpowers hcz))
  have hV₀M : zpowers u ≤ M := Subgroup.zpowers_le.mpr huY.1
  have hV₀1 : zpowers u ≠ ⊥ := fun h => hu1 (Subgroup.zpowers_eq_bot.mp h)
  have hcop₀ : Nat.Coprime (Nat.card (zpowers u)) 6 := by
    rw [Nat.card_zpowers]
    obtain ⟨e, he⟩ := r10a31_pow_eq_one_of_mem hVr huV
    exact r10a31_orderOf_coprime hr hr2 hr3 he
  exact false_of_fixed_vector hP65 hFM hV₀M hV₀1 hcop₀ hBu haF ha1 hfix0

theorem iii_assembly (hHH : KFactHallHigmanOdd)
    {M F S₀ : Subgroup G} {x z y : G} {f : ℕ}
    (hfp : f.Prime) (hf5 : 5 ≤ f) (hFe : IsElemAbelian f F) (hFne : F ≠ ⊥) (hFM : F ⊓ M = ⊥)
    (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hz3 : z ^ 3 = 1) (hxz : x * z = z * x) (hxM : x ∈ M)
    (hBM : zpowers x ⊔ zpowers z ≤ M)
    (hFCx : F ≤ centralizer ({x} : Set G))
    (hCxN : centralizer ({x} : Set G) ≤ normalizer (F : Set G))
    (hxC : x ∈ centralizer (F : Set G)) (hzN : z ∈ normalizer (F : Set G))
    (hzC : z ∉ centralizer (F : Set G)) (hCodd : ¬ 2 ∣ Nat.card (centralizer (F : Set G)))
    (hxS : IsSylowOf 3 (zpowers x) (centralizer (F : Set G)))
    (hzF : ∀ a ∈ F, z * a * z⁻¹ = a → a = 1)
    (hy1 : y ≠ 1) (hy2 : y * y = 1) (hyinv : ∀ a ∈ F, y * a * y⁻¹ = a⁻¹)
    (hyM : centralizer ({y} : Set G) ≤ M)
    (hNB : IsSylowOf 3 (zpowers x ⊔ zpowers z) (normalizer (F : Set G)))
    (hCxB : IsSylowOf 3 (zpowers x ⊔ zpowers z) (centralizer ({x} : Set G)))
    (hS0 : ∀ g ∈ M ⊓ centralizer ({x} : Set G), Nat.Coprime (orderOf g) 6 →
      g ∈ centralizer (S₀ : Set G))
    (hS0N : ∀ g ∈ M ⊓ centralizer ({x} : Set G), g ∈ normalizer (S₀ : Set G))
    (hxS0 : x ∈ centralizer (S₀ : Set G)) (hzS0 : z ∉ centralizer (S₀ : Set G))
    (hP65 : ∀ W : Subgroup G, W ≤ M → W ≠ ⊥ → Nat.Coprime (Nat.card W) 6 →
      zpowers x ⊔ zpowers z ≤ normalizer (W : Set G) → normalizer (W : Set G) ≤ M) :
    ∀ a ∈ F, a ≠ 1 → ∀ g ∈ normalizer (F : Set G) ⊓ centralizer ({a} : Set G),
      ∃ n : ℕ, g ^ (2 ^ n) ∈ centralizer (F : Set G) := by
  intro a haF ha1 g hg
  obtain ⟨hgN, hgA⟩ := hg
  obtain ⟨k, m, hmodd, ho⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨k, ?_⟩
  have hk0 : (2 : ℕ) ^ k ≠ 0 := pow_ne_zero k two_ne_zero
  have hpos : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) k
  have hdvd : 2 ^ k ∣ orderOf g := ⟨m, ho⟩
  have hord1 : orderOf (g ^ (2 ^ k)) = m := by
    rw [orderOf_pow_of_dvd hk0 hdvd, ho, Nat.mul_div_cancel_left m hpos]
  have hcg : Commute g a := (Subgroup.mem_centralizer_iff.mp hgA a (Set.mem_singleton a)).symm
  have hg₁com : Commute (g ^ (2 ^ k)) a := hcg.pow_left (2 ^ k)
  have hg₁N : g ^ (2 ^ k) ∈ normalizer (F : Set G) := pow_mem hgN _
  have hodd₁ : ¬ 2 ∣ orderOf (g ^ (2 ^ k)) := by
    rw [hord1]
    exact hmodd.not_two_dvd_nat
  by_contra hC
  obtain ⟨r, hr, hrdvd, i, hiP, hiC⟩ := exists_isPGroup_pow_not_mem hC
  obtain ⟨g₂, hg₂⟩ : ∃ g₂ : G, g₂ = (g ^ (2 ^ k)) ^ i := ⟨_, rfl⟩
  rw [← hg₂] at hiP hiC
  have hg₂N : g₂ ∈ normalizer (F : Set G) := by
    rw [hg₂]
    exact pow_mem hg₁N i
  have hg₂a : g₂ * a * g₂⁻¹ = a := by
    rw [hg₂]
    exact mul_inv_eq_iff_eq_mul.mpr ((hg₁com.pow_left i).eq)
  have hg₂odd : ¬ 2 ∣ orderOf g₂ := by
    rw [hg₂]
    exact fun h2 => hodd₁ (h2.trans (orderOf_pow_dvd i))
  have hr2 : r ≠ 2 := by
    intro h2
    rw [h2] at hrdvd
    exact hodd₁ hrdvd
  by_cases hr3 : r = 3
  · subst hr3
    exact ha1 (eq_one_of_fixes_of_isPGroup_three hNB hxC hzC hz3 hxz hzF g₂ hg₂N hiP hiC a haF
      hg₂a)
  · have hr5 : 5 ≤ r := by
      have h2 := hr.two_le
      have hr4 : r ≠ 4 := by
        intro h4
        rw [h4] at hr
        norm_num at hr
      omega
    obtain ⟨V, hVY, hVr, hBV, m'', hm''V, hm''C, a'', ha''F, ha''1, hfix''⟩ :=
      r10a31_reduce hr hr2 hr3 hx1 hx3 hz3 hxz hxM hBM hxC hCxN hCodd hxS hy1 hy2 hyinv hyM
        hNB hCxB hS0 hS0N hxS0 hzS0 haF ha1 hg₂N hiP hiC hg₂a hg₂odd
    have hVN : V ≤ normalizer (F : Set G) := le_trans hVY (le_trans inf_le_right hCxN)
    by_cases hrf : r = f
    · subst hrf
      exact r10a31_case_f hfp hf5 hFe hFne hFM hP65 hVY hVr hVN hBV hm''V hm''C
    · exact r10a31_case_ne hHH hfp hr hrf hr5 hFe hFM hP65 hz3 hzN hzF hVr hVY hVN hBV hm''V
        hm''C ha''F ha''1 hfix''

end R10D1

section R10Post

open CFSG.Open CFSG.ABGLocalTools CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem lemma630_iii_core (hS : Setting G) (hOut : KFactOutQ8Quaternion)
    (hHH : KFactHallHigmanOdd) {P : Sylow 3 G} {M : Subgroup G} {x z : G} {T : Subgroup G}
    {f : ℕ} (hyp : Lemma630Hyp G 3 P M x z T f)
    (hP614 : ∀ S₀ : Subgroup G, S₀ ≤ smallRankS x T → S₀ ≠ ⊥ →
      zpowers z ≤ normalizer (S₀ : Set G) → normalizer (S₀ : Set G) ≤ M)
    (hP65 : ∀ W : Subgroup G, W ≤ M → W ≠ ⊥ → Nat.Coprime (Nat.card W) 6 →
      zpowers x ⊔ zpowers z ≤ normalizer (W : Set G) → normalizer (W : Set G) ≤ M) :
    Lemma630Iii 3 f x := by
  have hF := facts630 hS hyp
  obtain ⟨y, hyS, hy1, hy2, hzy, hxy, hyinv⟩ := exists_y630 hS hyp
  obtain ⟨hf, hcov, h28, hfp, hf2, hfD, h29⟩ := hyp
  have hyM : centralizer ({y} : Set G) ≤ M := centralizer_le_of_prop614 hyS hy1 hzy hP614
  have hNB := isSylowOf_plane_normalizer hS ⟨hf, hcov, h28, hfp, hf2, hfD, h29⟩
  have hPlane := sylow_inf_centralizer_eq_plane hS hf (h28.2.1 rfl)
  have hPx : IsSylowOf 3 ((P : Subgroup G) ⊓ centralizer ({x} : Set G))
      (centralizer ({x} : Set G)) :=
    isSylowOf_iff.mpr ⟨inf_le_right, P.isPGroup'.to_inf_left, hf.point.sylow_centralizer⟩
  have hCxB : IsSylowOf 3 (zpowers x ⊔ zpowers z) (centralizer ({x} : Set G)) := by
    rw [← hPlane]
    exact hPx
  exact iii_assembly hHH hF.prime hF.five_le hF.elem hF.ne_bot hF.inf_M hF.x_ne hF.x_three
    hF.z_three hF.xz hF.x_M hF.B_le_M hF.F_le_Cx hF.Cx_le_N hF.x_C hF.z_N hF.z_not_C hF.C_odd
    hF.x_sylow hF.z_fpf hy1 hy2 hyinv hyM hNB hCxB
    (mem_centralizer_S0_of_coprime hS hOut ⟨hf, hcov, h28, hfp, hf2, hfD, h29⟩)
    (mem_normalizer_S0 hf) x_mem_centralizer_S0
    (z_not_mem_centralizer_S0 hS ⟨hf, hcov, h28, hfp, hf2, hfD, h29⟩) hP65

theorem lemma630_iii_three (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactRankTwoUniqueness) (hK2 : KFactRankThreeStructure)
    (hL62 : GL83SmallRankLemma62At3 G) (hOut : KFactOutQ8Quaternion)
    (hHH : KFactHallHigmanOdd) {P : Sylow 3 G} {M : Subgroup G} {x z : G} {T : Subgroup G}
    {f : ℕ} (hyp : Lemma630Hyp G 3 P M x z T f)
    (hP614 : ∀ S₀ : Subgroup G, S₀ ≤ smallRankS x T → S₀ ≠ ⊥ →
      zpowers z ≤ normalizer (S₀ : Set G) → normalizer (S₀ : Set G) ≤ M) :
    Lemma630Iii 3 f x := by
  obtain ⟨hf, hcov, h28, hfp, hf2, hfD, h29⟩ := hyp
  have hR : Nonempty (↥(smallRankR x z T) ≃* QuaternionGroup 2) := h28.2.1 rfl
  have hα : HasPrimeConstraint (G := M) 3 :=
    (hL62 hS hU0 P M hf.situation x z hf.point hf.central).resolve_right
      (lemma628_ii_three hS hU0 hf hR)
  refine lemma630_iii_core hS hOut hHH ⟨hf, hcov, h28, hfp, hf2, hfD, h29⟩ hP614 ?_
  intro W hWM hW1 hW6 hBW
  exact prop65Alpha_of_kfacts hS hU0 hK1 hK2 P M hf.situation hα x z hf.point hf.central
    W hWM hW1 hW6 hBW

end R10Post

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
