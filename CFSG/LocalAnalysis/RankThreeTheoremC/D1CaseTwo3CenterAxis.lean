module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

theorem conj_eq_of_mem_zpowers_of_three_pow {Y : Type*} [Group Y] {x ζ : Y} {k : ℕ}
    (hx : x ^ (3 ^ k) = 1) (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)
    (hmem : x * ζ * x⁻¹ ∈ Subgroup.zpowers ζ) : x * ζ * x⁻¹ = ζ := by
  have hord : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζ1
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hc1 : x * ζ * x⁻¹ ≠ 1 := fun h => hζ1 (by
    have := congrArg (fun y => x⁻¹ * y * x) h
    simpa [mul_assoc] using this)
  have hmod : ζ ^ a = ζ ^ (a % 3) := by
    have := zpow_mod_orderOf ζ a
    rw [hord] at this
    exact_mod_cast this.symm
  have h3 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases h3 with h0 | h1 | h2
  · exfalso
    apply hc1
    rw [← ha, hmod, h0]
    simp
  · rw [← ha, hmod, h1]
    simp
  · exfalso
    have hinv : x * ζ * x⁻¹ = ζ⁻¹ := by
      rw [← ha, hmod, h2]
      have : ζ ^ (2 : ℤ) * ζ = 1 := by
        rw [zpow_two]
        calc ζ * ζ * ζ = ζ ^ 3 := by rw [pow_succ, pow_two]
          _ = 1 := hζ3
      exact eq_inv_of_mul_eq_one_left this
    have hx2 : x ^ 2 * ζ * (x ^ 2)⁻¹ = ζ := by
      calc x ^ 2 * ζ * (x ^ 2)⁻¹ = x * (x * ζ * x⁻¹) * x⁻¹ := by rw [pow_two]; group
        _ = x * ζ⁻¹ * x⁻¹ := by rw [hinv]
        _ = (x * ζ * x⁻¹)⁻¹ := by group
        _ = ζ := by rw [hinv, inv_inv]
    have hxpow : x = (x ^ 2) ^ ((3 ^ k + 1) / 2) := by
      have h2 : 2 ∣ 3 ^ k + 1 := by
        have : Odd (3 ^ k) := Odd.pow (by decide)
        exact even_iff_two_dvd.mp (this.add_one)
      obtain ⟨m, hm⟩ := h2
      rw [hm, Nat.mul_div_cancel_left _ (by norm_num), ← pow_mul, ← hm, pow_succ, hx, one_mul]
    have hcomm : x * ζ * x⁻¹ = ζ := by
      have hcomm' : ∀ n : ℕ, (x ^ 2) ^ n * ζ * ((x ^ 2) ^ n)⁻¹ = ζ := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          calc (x ^ 2) ^ (n + 1) * ζ * ((x ^ 2) ^ (n + 1))⁻¹
              = (x ^ 2) ^ n * (x ^ 2 * ζ * (x ^ 2)⁻¹) * ((x ^ 2) ^ n)⁻¹ := by group
            _ = (x ^ 2) ^ n * ζ * ((x ^ 2) ^ n)⁻¹ := by rw [hx2]
            _ = ζ := ih
      rw [hxpow]
      exact hcomm' _
    rw [hcomm] at hinv
    have : ζ ^ 2 = 1 := by
      calc ζ ^ 2 = ζ * ζ := pow_two ζ
        _ = ζ * ζ⁻¹ := by rw [← hinv]
        _ = 1 := mul_inv_cancel ζ
    have hdvd : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one this
    rw [hord] at hdvd
    omega

theorem eq_of_mk_pCore_two_eq_of_isPGroup_three {Y : Type*} [Group Y] {T : Subgroup Y}
    (hT : IsPGroup 3 T) {a b : Y} (ha : a ∈ T) (hb : b ∈ T)
    (hab : QuotientGroup.mk' (CFSG.pCore 2 Y) a = QuotientGroup.mk' (CFSG.pCore 2 Y) b) :
    a = b := by
  have hdisj : Disjoint T (CFSG.pCore 2 Y) :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) T (CFSG.pCore 2 Y) hT CFSG.pCore_isPGroup
  exact inv_mul_eq_one.mp (Subgroup.disjoint_def.mp hdisj (T.mul_mem (T.inv_mem ha) hb)
    (QuotientGroup.eq.mp hab))

variable {G : Type} [Group G] [Finite G]

theorem zeta_mem_zpowers_mk_axis {P : Sylow 3 G} {M : Subgroup G} (hPM : (P : Subgroup G) ≤ M)
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hPN : ∀ (g : G) (hg : g ∈ (P : Subgroup G)),
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hPM hg⟩ ∈
        Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {ζ : ↥M ⧸ CFSG.pCore 2 ↥M} (hζL : ζ ∈ Lb)
    (hζC : ζ ∈ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)
    (hZ : ∀ x ∈ Lb, x ∈ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      x ∈ Subgroup.zpowers ζ)
    {w : G} (hwP : w ∈ (P : Subgroup G)) (_hwo : orderOf w = 3)
    (_hwc : ∀ g ∈ (P : Subgroup G), Commute w g)
    (hΩ : ∀ g ∈ (P : Subgroup G), (∀ h ∈ (P : Subgroup G), Commute g h) → g ^ 3 = 1 →
      g ∈ Subgroup.zpowers w) :
    ζ ∈ Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨w, hPM hwP⟩) := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set T : Subgroup ↥M := (P : Subgroup G).subgroupOf M
  have hT : IsPGroup 3 T := P.isPGroup'.comap_subtype
  have hinj : ∀ a ∈ T, ∀ b ∈ T, mk a = mk b → a = b := fun a ha b hb hab =>
    eq_of_mk_pCore_two_eq_of_isPGroup_three hT ha hb hab
  have hcomm : ∀ a ∈ T, mk a * ζ = ζ * mk a := by
    intro a ha
    have hx : mk a ∈ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      hPN (a : G) (Subgroup.mem_subgroupOf.mp ha)
    have hxL : mk a * ζ * (mk a)⁻¹ ∈ Lb := (Subgroup.mem_set_normalizer_iff.mp hx ζ).mp hζL
    have hxC : mk a * ζ * (mk a)⁻¹ ∈
        Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : (mk a)⁻¹ * y * mk a ∈ Lb := (Subgroup.mem_set_normalizer_iff''.mp hx y).mp hy
      have h1 := Subgroup.mem_centralizer_iff.mp hζC _ hy'
      calc y * (mk a * ζ * (mk a)⁻¹)
          = mk a * ((mk a)⁻¹ * y * mk a * ζ) * (mk a)⁻¹ := by group
        _ = mk a * (ζ * ((mk a)⁻¹ * y * mk a)) * (mk a)⁻¹ := by rw [h1]
        _ = mk a * ζ * (mk a)⁻¹ * y := by group
    have hxZ : mk a * ζ * (mk a)⁻¹ ∈ Subgroup.zpowers ζ := hZ _ hxL hxC
    obtain ⟨k, hk⟩ := hT ⟨a, ha⟩
    have hak : (mk a) ^ 3 ^ k = 1 := by
      have h2 : a ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [← map_pow, h2, map_one]
    have hfix := conj_eq_of_mem_zpowers_of_three_pow hak hζ3 hζ1 hxZ
    calc mk a * ζ = mk a * ζ * (mk a)⁻¹ * mk a := by group
      _ = ζ * mk a := by rw [hfix]
  let Pbar : Sylow 3 (↥M ⧸ CFSG.pCore 2 ↥M) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M)) (P.subtype hPM)
  have hPbar : ∀ y, y ∈ (Pbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ↔ ∃ a ∈ T, mk a = y :=
    fun y => Iff.rfl
  have hζP : ζ ∈ (Pbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    have hζcent : ζ ∈ Subgroup.centralizer
        ((Pbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨a, ha, rfl⟩ := (hPbar y).mp hy
      exact hcomm a ha
    have hζn := Subgroup.centralizer_le_normalizer _ hζcent
    have hZp : IsPGroup 3 (Subgroup.zpowers ζ) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hζ3 hζ1, pow_one])
    have hsup : IsPGroup 3 ((Pbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ⊔ Subgroup.zpowers ζ :
        Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      Pbar.isPGroup'.to_sup_of_normal_left' hZp (by rwa [Subgroup.zpowers_le])
    have heq := Pbar.is_maximal' hsup le_sup_left
    have hmem : ζ ∈ (Pbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ⊔ Subgroup.zpowers ζ :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers ζ)
    rwa [heq] at hmem
  obtain ⟨g, hgT, hgζ⟩ := (hPbar ζ).mp hζP
  have hg3 : g ^ 3 = 1 := by
    have h1 : mk (g ^ 3) = mk 1 := by rw [map_pow, hgζ, hζ3, map_one]
    exact hinj _ (T.pow_mem hgT 3) _ T.one_mem h1
  have hgc : ∀ h ∈ (P : Subgroup G), Commute (g : G) h := by
    intro h hh
    have hh' : (⟨h, hPM hh⟩ : ↥M) ∈ T := hh
    have h1 : g * ⟨h, hPM hh⟩ = ⟨h, hPM hh⟩ * g :=
      hinj _ (T.mul_mem hgT hh') _ (T.mul_mem hh' hgT)
        (by rw [map_mul, map_mul, hgζ]; exact (hcomm _ hh').symm)
    exact congrArg Subtype.val h1
  have hgw := hΩ (g : G) (Subgroup.mem_subgroupOf.mp hgT) hgc
    (by simpa using congrArg Subtype.val hg3)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hgw
  rw [← hgζ]
  refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
  rw [← map_zpow]
  congr 1
  exact Subtype.ext (by simpa using hi)

end CFSG.LocalAnalysis.RankThreeTheoremC
