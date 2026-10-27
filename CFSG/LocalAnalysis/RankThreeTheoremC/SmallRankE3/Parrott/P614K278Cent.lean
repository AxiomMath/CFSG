module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K278

open CFSG.Open Subgroup

variable {G : Type*} [Group G]

theorem commute_of_isMulCommutative {U : Subgroup G} (hU : IsMulCommutative U) {a b : G}
    (ha : a ∈ U) (hb : b ∈ U) : a * b = b * a :=
  congrArg Subtype.val (isMulCommutative_iff.mp hU ⟨a, ha⟩ ⟨b, hb⟩)

theorem commute_of_mem_zpowers {g z c : G} (hgz : g * z = z * g) (hc : c ∈ zpowers z) :
    g * c = c * g := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
  exact ((Commute.zpow_right hgz k)).eq

theorem commute_of_mem_closure_pair {g v z w : G} (hgv : g * v = v * g) (hgz : g * z = z * g)
    (hw : w ∈ closure ({v, z} : Set G)) : g * w = w * g := by
  have hle : closure ({v, z} : Set G) ≤ centralizer ({g} : Set G) := by
    rw [closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact mem_centralizer_singleton_iff.mpr hgv.symm
    · exact mem_centralizer_singleton_iff.mpr hgz.symm
  exact (mem_centralizer_singleton_iff.mp (hle hw)).symm

section Finite

variable [Finite G]

theorem closure_pair_eq {U : Subgroup G} (hU9 : Nat.card U = 9) {v z : G} (hv : v ∈ U)
    (hz : z ∈ U) (hz3 : orderOf z = 3) (hvz : v ∉ zpowers z) :
    closure ({v, z} : Set G) = U := by
  have hle : closure ({v, z} : Set G) ≤ U := by
    rw [closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hv
    · exact hz
  have hZle : zpowers z ≤ closure ({v, z} : Set G) :=
    zpowers_le.mpr (subset_closure (Set.mem_insert_of_mem _ rfl))
  have hZ3 : Nat.card (zpowers z) = 3 := by rw [Nat.card_zpowers, hz3]
  have h1 : Nat.card (closure ({v, z} : Set G)) ∣ 9 := hU9 ▸ card_dvd_of_le hle
  have h2 : 3 ∣ Nat.card (closure ({v, z} : Set G)) := hZ3 ▸ card_dvd_of_le hZle
  have h3 : Nat.card (closure ({v, z} : Set G)) ≠ 3 := by
    intro h
    apply hvz
    have : zpowers z = closure ({v, z} : Set G) :=
      eq_of_le_of_card_ge hZle (by rw [h, hZ3])
    rw [this]
    exact subset_closure (Set.mem_insert _ _)
  have h9 : Nat.card (closure ({v, z} : Set G)) = 9 := by
    have : Nat.card (closure ({v, z} : Set G)) ∈ Nat.divisors 9 :=
      Nat.mem_divisors.mpr ⟨h1, by norm_num⟩
    have hd : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hd] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h
    · rw [h] at h2
      norm_num at h2
    · exact absurd h h3
    · exact h
  exact eq_of_le_of_card_ge hle (by rw [h9, hU9])

end Finite

theorem exists_zpow_mul_of_mem_closure {U : Subgroup G} (hU : IsMulCommutative U) {v z : G}
    (hv : v ∈ U) (hz : z ∈ U) {w : G} (hw : w ∈ closure ({v, z} : Set G)) :
    ∃ k : ℤ, ∃ c ∈ zpowers z, w = v ^ k * c := by
  have hZU : zpowers z ≤ U := zpowers_le.mpr hz
  induction hw using closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, 1, one_mem _, by simp⟩
    · exact ⟨0, x, mem_zpowers x, by simp⟩
  | one => exact ⟨0, 1, one_mem _, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k, c, hc, rfl⟩ := hx
    obtain ⟨l, d, hd, rfl⟩ := hy
    refine ⟨k + l, c * d, mul_mem hc hd, ?_⟩
    have hcv : c * v ^ l = v ^ l * c :=
      commute_of_isMulCommutative hU (hZU hc) (zpow_mem hv l)
    calc v ^ k * c * (v ^ l * d) = v ^ k * (c * v ^ l) * d := by group
      _ = v ^ k * (v ^ l * c) * d := by rw [hcv]
      _ = v ^ (k + l) * (c * d) := by rw [zpow_add]; group
  | inv x _ hx =>
    obtain ⟨k, c, hc, rfl⟩ := hx
    refine ⟨-k, c⁻¹, inv_mem hc, ?_⟩
    have hcv : c⁻¹ * v ^ (-k) = v ^ (-k) * c⁻¹ :=
      commute_of_isMulCommutative hU (hZU (inv_mem hc)) (zpow_mem hv (-k))
    rw [mul_inv_rev, zpow_neg, ← zpow_neg, hcv]

theorem mem_coset_or_inv_coset {U : Subgroup G} (hU : IsMulCommutative U) {v z : G}
    (hv : v ∈ U) (hz : z ∈ U) (hv3 : v ^ 3 = 1) {w : G}
    (hw : w ∈ closure ({v, z} : Set G)) (hwz : w ∉ zpowers z) :
    (∃ c ∈ zpowers z, w = v * c) ∨ ∃ c ∈ zpowers z, w = v⁻¹ * c := by
  obtain ⟨k, c, hc, rfl⟩ := exists_zpow_mul_of_mem_closure hU hv hz hw
  have hv3' : v ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hv3
  rw [zpow_eq_zpow_emod k hv3'] at hwz ⊢
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
  · rw [h, zpow_zero, one_mul] at hwz
    exact absurd hc hwz
  · left
    rw [h, zpow_one]
    exact ⟨c, hc, rfl⟩
  · right
    refine ⟨c, hc, ?_⟩
    rw [h]
    congr 1
    have : v ^ (2 : ℤ) * v = 1 := by
      rw [← zpow_add_one]
      exact hv3'
    exact eq_inv_of_mul_eq_one_left this

theorem eq_one_of_conj_eq_mul {s v z c : G} (hs : ∃ m : ℕ, s ^ 2 ^ m = 1)
    (hsz : s * z = z * s) (hz3 : z ^ 3 = 1) (hc : c ∈ zpowers z) (h : s * v * s⁻¹ = v * c) :
    c = 1 := by
  obtain ⟨m, hm⟩ := hs
  have hsc : ∀ n : ℕ, s * c ^ n = c ^ n * s := fun n =>
    commute_of_mem_zpowers hsz (pow_mem hc n)
  have key : ∀ n : ℕ, s ^ n * v * (s ^ n)⁻¹ = v * c ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc s ^ (n + 1) * v * (s ^ (n + 1))⁻¹ = s * (s ^ n * v * (s ^ n)⁻¹) * s⁻¹ := by
            rw [pow_succ']; group
        _ = s * (v * c ^ n) * s⁻¹ := by rw [ih]
        _ = (s * v * s⁻¹) * (s * c ^ n * s⁻¹) := by group
        _ = v * c * c ^ n := by rw [h, hsc n]; group
        _ = v * c ^ (n + 1) := by rw [pow_succ']; group
  have h1 := key (2 ^ m)
  rw [hm, one_mul, inv_one, mul_one] at h1
  have h2 : c ^ 2 ^ m = 1 := by
    have := congrArg (v⁻¹ * ·) h1
    simpa using this.symm
  have hc3 : c ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  have hcop : Nat.gcd (2 ^ m) 3 = 1 :=
    Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 3)
  have : c ^ Nat.gcd (2 ^ m) 3 = 1 := pow_gcd_eq_one.mpr ⟨h2, hc3⟩
  rwa [hcop, pow_one] at this

variable [Finite G]

theorem commute_of_transvection {U S : Subgroup G} {z b : G} (hU : IsElemAbelian 3 U)
    (hU9 : Nat.card U = 9) (hzU : z ∈ U) (hz1 : z ≠ 1) (hbU : b ∈ normalizer (U : Set G))
    (hbz : b * z = z * b) (hb3 : b ^ 3 = 1) (hbnc : ∃ u ∈ U, b * u ≠ u * b)
    (hS : IsPGroup 2 S) (hSU : S ≤ normalizer (U : Set G)) (hSz : ∀ s ∈ S, s * z = z * s)
    (hbS : b ∈ normalizer (S : Set G)) :
    ∀ s ∈ S, ∀ u ∈ U, s * u = u * s := by
  have hcomm : ∀ a ∈ U, ∀ c ∈ U, a * c = c * a := fun a ha c hc =>
    commute_of_isMulCommutative hU.1 ha hc
  have hz3 : z ^ 3 = 1 := hU.2 z hzU
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hZU : zpowers z ≤ U := zpowers_le.mpr hzU
  obtain ⟨v, hvU, hvz⟩ : ∃ v ∈ U, v ∉ zpowers z := by
    by_contra hno
    push Not at hno
    have h1 : Nat.card U ≤ Nat.card (zpowers z) := card_le_of_le hno
    rw [hU9, Nat.card_zpowers, hzo] at h1
    norm_num at h1
  have hv3 : v ^ 3 = 1 := hU.2 v hvU
  have hC := closure_pair_eq hU9 hvU hzU hzo hvz
  have hgen : ∀ g : G, g * v = v * g → g * z = z * g → ∀ u ∈ U, g * u = u * g := by
    intro g hgv hgz u hu
    rw [← hC] at hu
    exact commute_of_mem_closure_pair hgv hgz hu
  have hcls : ∀ w ∈ U, w ∉ zpowers z →
      (∃ c ∈ zpowers z, w = v * c) ∨ ∃ c ∈ zpowers z, w = v⁻¹ * c := fun w hw hwz =>
    mem_coset_or_inv_coset hU.1 hvU hzU hv3 (hC ▸ hw) hwz
  have hout : ∀ g : G, g ∈ normalizer (U : Set G) → g * z = z * g →
      g * v * g⁻¹ ∈ U ∧ g * v * g⁻¹ ∉ zpowers z := by
    intro g hgU hgz
    refine ⟨(mem_normalizer_iff.mp hgU v).mp hvU, fun h => hvz ?_⟩
    have hgc : g * (g * v * g⁻¹) = (g * v * g⁻¹) * g := commute_of_mem_zpowers hgz h
    have : v = g * v * g⁻¹ := by
      calc v = g⁻¹ * ((g * v * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * v * g⁻¹)) := by rw [hgc]
        _ = g * v * g⁻¹ := by group
    rw [this]
    exact h
  obtain ⟨d, hd, hbv⟩ : ∃ d ∈ zpowers z, b * v * b⁻¹ = v * d := by
    obtain ⟨h1, h2⟩ := hout b hbU hbz
    rcases hcls _ h1 h2 with h | ⟨d, hd, hbv⟩
    · exact h
    · exfalso
      have hbd : b * d = d * b := commute_of_mem_zpowers hbz hd
      have hdv : d * v = v * d := hcomm d (hZU hd) v hvU
      have hb2 : (b * b) * v * (b * b)⁻¹ = v := by
        calc (b * b) * v * (b * b)⁻¹ = b * (b * v * b⁻¹) * b⁻¹ := by group
          _ = b * (v⁻¹ * d) * b⁻¹ := by rw [hbv]
          _ = (b * v * b⁻¹)⁻¹ * (b * d * b⁻¹) := by group
          _ = (v⁻¹ * d)⁻¹ * d := by rw [hbv, hbd, mul_inv_cancel_right]
          _ = d⁻¹ * v * d := by group
          _ = v := by rw [mul_assoc, ← hdv]; group
      have hb3m : b * (b * b) = 1 := by rw [← pow_three]; exact hb3
      have hb3' : b * v * b⁻¹ = v := by
        calc b * v * b⁻¹ = b * ((b * b) * v * (b * b)⁻¹) * b⁻¹ := by rw [hb2]
          _ = (b * (b * b)) * v * (b * (b * b))⁻¹ := by group
          _ = v := by rw [hb3m]; group
      rw [hbv] at hb3'
      apply hvz
      have hv2 : v * v = d := by
        calc v * v = v * (v⁻¹ * d) := by rw [hb3']
          _ = d := by group
      have hv3m : v * (v * v) = 1 := by rw [← pow_three]; exact hv3
      have : v = d * d := by
        calc v = (v * (v * v)) * v := by rw [hv3m, one_mul]
          _ = (v * v) * (v * v) := by group
          _ = d * d := by rw [hv2]
      rw [this]
      exact mul_mem hd hd
  have hbd : b * d = d * b := commute_of_mem_zpowers hbz hd
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [mul_one] at hbv
    have hbv' : b * v = v * b := by
      calc b * v = b * v * b⁻¹ * b := by group
        _ = v * b := by rw [hbv]
    obtain ⟨u, hu, hbu⟩ := hbnc
    exact hbu (hgen b hbv' hbz u hu)
  have hcase1 : ∀ s ∈ S, ∀ c ∈ zpowers z, s * v * s⁻¹ = v * c → c = 1 := by
    intro s hs c hc h
    obtain ⟨m, hm⟩ := hS ⟨s, hs⟩
    have hm' : s ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    exact eq_one_of_conj_eq_mul ⟨m, hm'⟩ (hSz s hs) hz3 hc h
  intro s hs
  obtain ⟨h1, h2⟩ := hout s (hSU hs) (hSz s hs)
  rcases hcls _ h1 h2 with ⟨c, hc, hsv⟩ | ⟨c, hc, hsv⟩
  ·
    have hc1 := hcase1 s hs c hc hsv
    rw [hc1, mul_one] at hsv
    have hsv' : s * v = v * s := by
      calc s * v = s * v * s⁻¹ * s := by group
        _ = v * s := by rw [hsv]
    exact hgen s hsv' (hSz s hs)
  ·
    exfalso
    set t := b * s * b⁻¹ with ht
    have htS : t ∈ S := (mem_normalizer_iff.mp hbS s).mp hs
    have hts : t * s ∈ S := mul_mem htS hs
    have hsc : s * c = c * s := commute_of_mem_zpowers (hSz s hs) hc
    have hsd : s * d = d * s := commute_of_mem_zpowers (hSz s hs) hd
    have htc : t * c = c * t := commute_of_mem_zpowers (hSz t htS) hc
    have hbc : b * c = c * b := commute_of_mem_zpowers hbz hc
    have hdv : d * v = v * d := hcomm d (hZU hd) v hvU
    have hcv : c * v = v * c := hcomm c (hZU hc) v hvU
    have hcd : c * d = d * c := hcomm c (hZU hc) d (hZU hd)
    have hbinv : b⁻¹ * v * b = v * d⁻¹ := by
      calc b⁻¹ * v * b = b⁻¹ * (v * d * d⁻¹) * b := by group
        _ = b⁻¹ * (b * v * b⁻¹ * d⁻¹) * b := by rw [hbv]
        _ = v * (b⁻¹ * d⁻¹ * b) := by group
        _ = v * d⁻¹ := by
            congr 1
            have : b⁻¹ * d * b = d := by
              calc b⁻¹ * d * b = b⁻¹ * (d * b) := by group
                _ = b⁻¹ * (b * d) := by rw [hbd]
                _ = d := by group
            calc b⁻¹ * d⁻¹ * b = (b⁻¹ * d * b)⁻¹ := by group
              _ = d⁻¹ := by rw [this]
    have htv : t * v * t⁻¹ = d⁻¹ * v⁻¹ * c * d⁻¹ := by
      have hsvd : s * (v * d⁻¹) * s⁻¹ = v⁻¹ * c * d⁻¹ := by
        have hsdi : s * d⁻¹ * s⁻¹ = d⁻¹ := by
          calc s * d⁻¹ * s⁻¹ = (s * d * s⁻¹)⁻¹ := by group
            _ = d⁻¹ := by rw [hsd]; group
        calc s * (v * d⁻¹) * s⁻¹ = (s * v * s⁻¹) * (s * d⁻¹ * s⁻¹) := by group
          _ = v⁻¹ * c * d⁻¹ := by rw [hsv, hsdi]
      have hbvi : b * v⁻¹ * b⁻¹ = d⁻¹ * v⁻¹ := by
        calc b * v⁻¹ * b⁻¹ = (b * v * b⁻¹)⁻¹ := by group
          _ = (v * d)⁻¹ := by rw [hbv]
          _ = d⁻¹ * v⁻¹ := by group
      have hbci : b * (c * d⁻¹) * b⁻¹ = c * d⁻¹ := by
        have hbdi : b * d⁻¹ = d⁻¹ * b := by
          calc b * d⁻¹ = d⁻¹ * (d * b) * d⁻¹ := by group
            _ = d⁻¹ * (b * d) * d⁻¹ := by rw [hbd]
            _ = d⁻¹ * b := by group
        calc b * (c * d⁻¹) * b⁻¹ = (b * c) * d⁻¹ * b⁻¹ := by group
          _ = c * (b * d⁻¹) * b⁻¹ := by rw [hbc]; group
          _ = c * (d⁻¹ * b) * b⁻¹ := by rw [hbdi]
          _ = c * d⁻¹ := by group
      calc t * v * t⁻¹ = b * (s * (b⁻¹ * v * b) * s⁻¹) * b⁻¹ := by rw [ht]; group
        _ = b * (s * (v * d⁻¹) * s⁻¹) * b⁻¹ := by rw [hbinv]
        _ = b * (v⁻¹ * c * d⁻¹) * b⁻¹ := by rw [hsvd]
        _ = (b * v⁻¹ * b⁻¹) * (b * (c * d⁻¹) * b⁻¹) := by group
        _ = d⁻¹ * v⁻¹ * (c * d⁻¹) := by rw [hbvi, hbci]
        _ = d⁻¹ * v⁻¹ * c * d⁻¹ := by group
    have htsv : (t * s) * v * (t * s)⁻¹ = v * (d * d) := by
      have htci : t * c * t⁻¹ = c := by
        calc t * c * t⁻¹ = c * t * t⁻¹ := by rw [htc]
          _ = c := by group
      calc (t * s) * v * (t * s)⁻¹ = t * (s * v * s⁻¹) * t⁻¹ := by group
        _ = t * (v⁻¹ * c) * t⁻¹ := by rw [hsv]
        _ = (t * v * t⁻¹)⁻¹ * (t * c * t⁻¹) := by group
        _ = (d⁻¹ * v⁻¹ * c * d⁻¹)⁻¹ * c := by rw [htv, htci]
        _ = d * c⁻¹ * v * d * c := by group
        _ = v * (d * d) := by
            have hvd : v * d = d * v := hdv.symm
            have hci : c⁻¹ * v = v * c⁻¹ := by
              calc c⁻¹ * v = c⁻¹ * (v * c) * c⁻¹ := by group
                _ = c⁻¹ * (c * v) * c⁻¹ := by rw [hcv]
                _ = v * c⁻¹ := by group
            have hcid : c⁻¹ * d = d * c⁻¹ := by
              calc c⁻¹ * d = c⁻¹ * (d * c) * c⁻¹ := by group
                _ = c⁻¹ * (c * d) * c⁻¹ := by rw [hcd]
                _ = d * c⁻¹ := by group
            calc d * c⁻¹ * v * d * c = d * (c⁻¹ * v) * d * c := by group
              _ = d * (v * c⁻¹) * d * c := by rw [hci]
              _ = d * v * (c⁻¹ * d) * c := by group
              _ = d * v * (d * c⁻¹) * c := by rw [hcid]
              _ = (d * v) * d := by group
              _ = v * (d * d) := by rw [← hvd]; group
    have hdd := hcase1 (t * s) hts (d * d) (mul_mem hd hd) htsv
    apply hd1
    have hd3 : d ^ 3 = 1 := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hd
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
    have hd3m : d * (d * d) = 1 := by rw [← pow_three]; exact hd3
    calc d = (d * (d * d)) * (d * d)⁻¹ := by group
      _ = 1 := by rw [hd3m, hdd]; group

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K278
