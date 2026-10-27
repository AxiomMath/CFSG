module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction629.TwoGroups

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem ext2Decomp_zpowers_eq {t : K} (ht : t ^ 2 = 1) {g : K} (hg : g ∈ zpowers t) :
    g = 1 ∨ g = t := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have ht' : t ^ (2 : ℤ) = 1 := by simpa [zpow_two, pow_two] using ht
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left
    have hn : n = 2 * (n / 2) := by omega
    rw [hn, zpow_mul, ht', one_zpow]
  · right
    have hn : n = 2 * (n / 2) + 1 := by omega
    rw [hn, zpow_add, zpow_mul, ht', one_zpow, one_mul, zpow_one]

theorem ext2Decomp_comm_zpowers {R : Subgroup K} {t : K} (hR : IsExt2 R t) {r g : K} (hr : r ∈ R)
    (hg : g ∈ zpowers t) : r * g = g * r := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hc : Commute r t := hR.t_comm r hr
  exact (hc.zpow_right n).eq

theorem ext2Decomp_comm_mul {R : Subgroup K} {t : K} (hR : IsExt2 R t) {a b h : K} (ha : a ∈ R)
    (hb : b ∈ R) (hh : h ∈ R) : ⁅a * b, h⁆ = ⁅a, h⁆ * ⁅b, h⁆ := by
  have hbh : ⁅b, h⁆ ∈ zpowers t := hR.comm_mem b hb h hh
  have hah : ⁅a, h⁆ ∈ zpowers t := hR.comm_mem a ha h hh
  have h1 : a * ⁅b, h⁆ = ⁅b, h⁆ * a := ext2Decomp_comm_zpowers hR ha hbh
  have h2 : ⁅b, h⁆ * ⁅a, h⁆ = ⁅a, h⁆ * ⁅b, h⁆ := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hah
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hbh
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  calc ⁅a * b, h⁆ = a * ⁅b, h⁆ * a⁻¹ * ⁅a, h⁆ := by
        simp only [commutatorElement_def]; group
    _ = ⁅b, h⁆ * ⁅a, h⁆ := by rw [h1, mul_inv_cancel_right]
    _ = ⁅a, h⁆ * ⁅b, h⁆ := h2

@[expose] def ext2Decomp_commHom {R : Subgroup K} {t : K} (hR : IsExt2 R t) {h : K} (hh : h ∈ R) :
    ↥R →* ↥(zpowers t) where
  toFun r := ⟨⁅(r : K), h⁆, hR.comm_mem _ r.2 _ hh⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    show ⁅((a * b : ↥R) : K), h⁆ = ⁅(a : K), h⁆ * ⁅(b : K), h⁆
    exact ext2Decomp_comm_mul hR a.2 b.2 hh)

@[expose] def ext2Decomp_phi {R : Subgroup K} {t : K} (hR : IsExt2 R t) {x y : K} (hx : x ∈ R)
    (hy : y ∈ R) : ↥R →* ↥(zpowers t) × ↥(zpowers t) :=
  (ext2Decomp_commHom hR hx).prod (ext2Decomp_commHom hR hy)

theorem ext2Decomp_phi_eq_iff {R : Subgroup K} {t : K} (hR : IsExt2 R t) {x y : K} (hx : x ∈ R)
    (hy : y ∈ R) (r s : ↥R) :
    ext2Decomp_phi hR hx hy r = ext2Decomp_phi hR hx hy s ↔ ⁅(r : K), x⁆ = ⁅(s : K), x⁆ ∧
      ⁅(r : K), y⁆ = ⁅(s : K), y⁆ := by
  rw [Prod.ext_iff, Subtype.ext_iff, Subtype.ext_iff]
  rfl

theorem ext2Decomp_phi_eq_one {R : Subgroup K} {t : K} (hR : IsExt2 R t) {x y : K} (hx : x ∈ R)
    (hy : y ∈ R) (r : ↥R) :
    ext2Decomp_phi hR hx hy r = 1 ↔ (r : K) ∈ centralizer ({x, y} : Set K) := by
  have h1 : ext2Decomp_phi hR hx hy r = ext2Decomp_phi hR hx hy 1 ↔ _ :=
    ext2Decomp_phi_eq_iff hR hx hy r 1
  rw [map_one] at h1
  rw [h1, Subgroup.mem_centralizer_iff]
  simp only [OneMemClass.coe_one, commutatorElement_one_left, commutatorElement_eq_one_iff_mul_comm,
    Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩

theorem ext2Decomp_commutator_swap {t : K} (ht : t ^ 2 = 1) {x y : K} (hxy : ⁅x, y⁆ = t) :
    ⁅y, x⁆ = t := by
  rw [← commutatorElement_inv, hxy]
  exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ht)

theorem ext2Decomp_rep {R : Subgroup K} {t : K} (hR : IsExt2 R t) {x y : K} (hx : x ∈ R)
    (hy : y ∈ R) (hxy : ⁅x, y⁆ = t) (a b : ↥(zpowers t)) :
    ∃ q : ↥R, ((q : K) = 1 ∨ (q : K) = x ∨ (q : K) = y ∨ (q : K) = x * y) ∧
      ext2Decomp_phi hR hx hy q = (a, b) := by
  have hyx : ⁅y, x⁆ = t := ext2Decomp_commutator_swap hR.t_sq hxy
  have key : ∀ q : ↥R, (⁅(q : K), x⁆ = (a : K) ∧ ⁅(q : K), y⁆ = (b : K)) →
      ext2Decomp_phi hR hx hy q = (a, b) := by
    intro q hq
    exact Prod.ext (Subtype.ext hq.1) (Subtype.ext hq.2)
  rcases ext2Decomp_zpowers_eq hR.t_sq a.2 with ha | ha <;>
    rcases ext2Decomp_zpowers_eq hR.t_sq b.2 with hb | hb
  · refine ⟨1, Or.inl rfl, key _ ?_⟩
    simp [ha, hb]
  · refine ⟨⟨x, hx⟩, Or.inr (Or.inl rfl), key _ ?_⟩
    simp [ha, hb, hxy]
  · refine ⟨⟨y, hy⟩, Or.inr (Or.inr (Or.inl rfl)), key _ ?_⟩
    simp [ha, hb, hyx]
  · refine ⟨⟨x * y, R.mul_mem hx hy⟩, Or.inr (Or.inr (Or.inr rfl)), key _ ?_⟩
    show ⁅x * y, x⁆ = (a : K) ∧ ⁅x * y, y⁆ = (b : K)
    rw [ext2Decomp_comm_mul hR hx hy hx, ext2Decomp_comm_mul hR hx hy hy, ha, hb]
    simp [hxy, hyx]

theorem ext2Decomp_phi_surjective {R : Subgroup K} {t : K} (hR : IsExt2 R t) {x y : K} (hx : x ∈ R)
    (hy : y ∈ R) (hxy : ⁅x, y⁆ = t) : Function.Surjective (ext2Decomp_phi hR hx hy) := by
  rintro ⟨a, b⟩
  obtain ⟨q, -, hq⟩ := ext2Decomp_rep hR hx hy hxy a b
  exact ⟨q, hq⟩

theorem ext2Decomp_card_ker {R : Subgroup K} {t : K} (hR : IsExt2 R t) {x y : K} (hx : x ∈ R)
    (hy : y ∈ R) :
    Nat.card (ext2Decomp_phi hR hx hy).ker = Nat.card ↥(R ⊓ centralizer ({x, y} : Set K)) :=
  Nat.card_congr
    { toFun := fun r => ⟨(r.1 : K), Subgroup.mem_inf.mpr ⟨r.1.2,
        (ext2Decomp_phi_eq_one hR hx hy r.1).mp (MonoidHom.mem_ker.mp r.2)⟩⟩
      invFun := fun s => ⟨⟨(s : K), (Subgroup.mem_inf.mp s.2).1⟩, MonoidHom.mem_ker.mpr
        ((ext2Decomp_phi_eq_one hR hx hy _).mpr (Subgroup.mem_inf.mp s.2).2)⟩
      left_inv := fun r => rfl
      right_inv := fun s => rfl }

theorem ext2Decomp_decomp_card {R : Subgroup K} {t : K} (hR : IsExt2 R t) {x y : K} (hx : x ∈ R)
    (hy : y ∈ R) (hxy : ⁅x, y⁆ = t) :
    4 * Nat.card ↥(R ⊓ centralizer ({x, y} : Set K)) = Nat.card R := by
  have h1 := Subgroup.card_ker_mul_card_of_surjective (ext2Decomp_phi_surjective hR hx hy hxy)
  rw [ext2Decomp_card_ker hR hx hy] at h1
  have h2 : Nat.card (↥(zpowers t) × ↥(zpowers t)) = 4 := by
    rw [Nat.card_prod, Nat.card_zpowers, orderOf_eq_prime hR.t_sq hR.t_ne]
  rw [h2] at h1
  omega

theorem ext2Decomp_split {R : Subgroup K} {t : K} (hR : IsExt2 R t) {x y : K} (hx : x ∈ R)
    (hy : y ∈ R) (hxy : ⁅x, y⁆ = t) {r : K} (hr : r ∈ R) :
    ∃ q c : K, (q = 1 ∨ q = x ∨ q = y ∨ q = x * y) ∧
      c ∈ R ⊓ centralizer ({x, y} : Set K) ∧ r = q * c := by
  obtain ⟨q, hq, hφ⟩ := ext2Decomp_rep hR hx hy hxy (ext2Decomp_phi hR hx hy ⟨r, hr⟩).1
    (ext2Decomp_phi hR hx hy ⟨r, hr⟩).2
  rw [Prod.mk.eta] at hφ
  have hc : q⁻¹ * ⟨r, hr⟩ ∈ (ext2Decomp_phi hR hx hy).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, inv_mul_cancel]
  refine ⟨q, ((q⁻¹ * ⟨r, hr⟩ : ↥R) : K), hq, Subgroup.mem_inf.mpr ⟨(q⁻¹ * ⟨r, hr⟩ : ↥R).2,
    (ext2Decomp_phi_eq_one hR hx hy _).mp hc⟩, ?_⟩
  simp

theorem IsExt2.decomp {R : Subgroup K} {t : K} (hR : IsExt2 R t) {x y : K} (hx : x ∈ R)
    (hy : y ∈ R) (hxy : ⁅x, y⁆ = t) :
    IsExt2 (R ⊓ centralizer ({x, y} : Set K)) t ∧
      4 * Nat.card ↥(R ⊓ centralizer ({x, y} : Set K)) = Nat.card R := by
  refine ⟨?_, ext2Decomp_decomp_card hR hx hy hxy⟩
  have hcent : ∀ g : K, g ∈ centralizer ({x, y} : Set K) ↔ x * g = g * x ∧ y * g = g * y := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  refine ⟨Subgroup.mem_inf.mpr ⟨hR.t_mem, (hcent t).mpr
    ⟨hR.t_comm x hx, hR.t_comm y hy⟩⟩, hR.t_sq, hR.t_ne, ?_, ?_, ?_, ?_⟩
  · intro r hr
    exact hR.t_comm r (Subgroup.mem_inf.mp hr).1
  · intro y' hy' hcomm
    have hy'R : y' ∈ R := (Subgroup.mem_inf.mp hy').1
    obtain ⟨hy'x, hy'y⟩ := (hcent y').mp (Subgroup.mem_inf.mp hy').2
    apply hR.center_le y' hy'R
    intro r hr
    obtain ⟨q, c, hq, hc, rfl⟩ := ext2Decomp_split hR hx hy hxy hr
    have hyq : Commute y' q := by
      rcases hq with rfl | rfl | rfl | rfl
      · exact Commute.one_right y'
      · exact hy'x.symm
      · exact hy'y.symm
      · have h1 : Commute y' x := hy'x.symm
        have h2 : Commute y' y := hy'y.symm
        exact h1.mul_right h2
    have hyc : Commute y' c := hcomm c hc
    exact (hyq.mul_right hyc).eq
  · intro r hr
    exact hR.sq_mem r (Subgroup.mem_inf.mp hr).1
  · intro r hr s hs
    exact hR.comm_mem r (Subgroup.mem_inf.mp hr).1 s (Subgroup.mem_inf.mp hs).1

theorem ext2Decomp_card_aux {t : K} (n : ℕ) :
    ∀ R : Subgroup K, Nat.card R = n → IsExt2 R t → ∃ k : ℕ, Nat.card R = 2 ^ (1 + 2 * k) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro R hn hR
    by_cases hall : ∀ x ∈ R, x ∈ zpowers t
    · refine ⟨0, ?_⟩
      have hRt : R = zpowers t := le_antisymm hall (Subgroup.zpowers_le.mpr hR.t_mem)
      rw [hRt, Nat.card_zpowers, orderOf_eq_prime hR.t_sq hR.t_ne]
      norm_num
    · push Not at hall
      obtain ⟨x, hx, hxt⟩ := hall
      have hnc : ∃ y ∈ R, x * y ≠ y * x := by
        by_contra hcon
        push Not at hcon
        exact hxt (hR.center_le x hx hcon)
      obtain ⟨y, hy, hxy⟩ := hnc
      have hne : ⁅x, y⁆ ≠ 1 := fun h => hxy (commutatorElement_eq_one_iff_mul_comm.mp h)
      have hxyt : ⁅x, y⁆ = t :=
        (ext2Decomp_zpowers_eq hR.t_sq (hR.comm_mem x hx y hy)).resolve_left hne
      obtain ⟨hR', hcard⟩ := IsExt2.decomp hR hx hy hxyt
      have hpos : 0 < Nat.card ↥(R ⊓ centralizer ({x, y} : Set K)) := Nat.card_pos
      obtain ⟨k, hk⟩ := ih (Nat.card ↥(R ⊓ centralizer ({x, y} : Set K))) (by omega)
        (R ⊓ centralizer ({x, y} : Set K)) rfl hR'
      refine ⟨k + 1, ?_⟩
      rw [← hcard, hk]
      ring

theorem IsExt2.card_eq {R : Subgroup K} {t : K} (hR : IsExt2 R t) :
    ∃ k : ℕ, Nat.card R = 2 ^ (1 + 2 * k) :=
  ext2Decomp_card_aux (Nat.card R) R rfl hR
end

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem noncentral_mem_zpowers_iff {t : K} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (x : K) :
    x ∈ Subgroup.zpowers t ↔ x = 1 ∨ x = t := by
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  constructor
  · intro hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h1 : t ^ (n % 2) = t ^ n := by
      simpa [hord] using zpow_mod_orderOf t n
    rcases Int.emod_two_eq_zero_or_one n with h2 | h2
    · left
      rw [← h1, h2, zpow_zero]
    · right
      rw [← h1, h2, zpow_one]
  · rintro (h | h)
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers t

theorem IsExt2.exists_noncentral_involution {R : Subgroup K} {t : K} (hR : IsExt2 R t) {k : ℕ}
    (hk : Nat.card R = 2 ^ (1 + 2 * k)) (hk2 : 2 ≤ k) :
    ∃ y ∈ R, y ^ 2 = 1 ∧ y ∉ zpowers t := by
  by_contra hcon
  have hsq : ∀ y ∈ R, y ^ 2 = 1 → y ∈ Subgroup.zpowers t := fun y hy h2 => by
    by_contra hy'
    exact hcon ⟨y, hy, h2, hy'⟩
  have hnot : ∀ y ∈ R, y ∉ Subgroup.zpowers t → y ^ 2 = t := by
    intro y hy hyt
    rcases (noncentral_mem_zpowers_iff hR.t_sq hR.t_ne _).mp (hR.sq_mem y hy) with h1 | h1
    · exact absurd (hsq y hy h1) hyt
    · exact h1
  have h4 : ∀ g ∈ R, g ^ 4 = 1 := by
    intro g hg
    by_cases hgt : g ∈ Subgroup.zpowers t
    · rcases (noncentral_mem_zpowers_iff hR.t_sq hR.t_ne _).mp hgt with h1 | h1
      · rw [h1, one_pow]
      · rw [h1, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hR.t_sq, one_pow]
    · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hnot g hg hgt, hR.t_sq]
  have h32 : 32 ≤ Nat.card R := by
    rw [hk]
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ (1 + 2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcardt : Nat.card (Subgroup.zpowers t) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hR.t_sq hR.t_ne]
  obtain ⟨a, ha, hat⟩ : ∃ a ∈ R, a ∉ Subgroup.zpowers t := by
    by_contra hno
    have hle : R ≤ Subgroup.zpowers t := fun x hx => by
      by_contra hx'
      exact hno ⟨x, hx, hx'⟩
    have := Subgroup.card_le_of_le hle
    omega
  have ha2 : a ^ 2 = t := hnot a ha hat
  have ha4 : a ^ 4 = 1 := h4 a ha
  have hcardA : Nat.card (Subgroup.zpowers a) ≤ 4 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) ha4
  obtain ⟨y, hy, hyA⟩ : ∃ y ∈ R, y ∉ Subgroup.zpowers a := by
    by_contra hno
    have hle : R ≤ Subgroup.zpowers a := fun x hx => by
      by_contra hx'
      exact hno ⟨x, hx, hx'⟩
    have := Subgroup.card_le_of_le hle
    omega
  have hyt : y ∉ Subgroup.zpowers t := by
    intro h
    apply hyA
    have hta : t ∈ Subgroup.zpowers a := by
      rw [← ha2]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 2
    exact (Subgroup.zpowers_le.mpr hta) h
  have hy2 : y ^ 2 = t := hnot y hy hyt
  have hcov := cover_of_exponent_four
    (G := R) (t := (⟨t, hR.t_mem⟩ : R)) (a := (⟨a, ha⟩ : R)) (y := (⟨y, hy⟩ : R))
    (by
      intro h
      apply hR.t_ne
      simpa using congrArg Subtype.val h)
    (Subtype.ext hR.t_sq)
    (fun g => Subtype.ext (hR.t_comm g.1 g.2))
    (fun e he => by
      rcases (noncentral_mem_zpowers_iff hR.t_sq hR.t_ne _).mp
          (hsq e.1 e.2 (congrArg Subtype.val he)) with h1 | h1
      · exact Or.inl (Subtype.ext h1)
      · exact Or.inr (Subtype.ext h1))
    (fun g => Subtype.ext (h4 g.1 g.2))
    (Subtype.ext ha2)
    (Subtype.ext hy2)
    (by
      intro hmem
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      apply hyA
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      have := congrArg Subtype.val hn
      simpa using this)
  have hsurj : Function.Surjective (fun p : Bool × Subgroup.zpowers (⟨a, ha⟩ : R) =>
      cond p.1 ((⟨y, hy⟩ : R) * (p.2 : R)) (p.2 : R)) := by
    intro g
    rcases hcov g with hg | hg
    · exact ⟨(false, ⟨g, hg⟩), rfl⟩
    · exact ⟨(true, ⟨(⟨y, hy⟩ : R)⁻¹ * g, hg⟩), by simp⟩
  have hcard := Nat.card_le_card_of_surjective _ hsurj
  have hB : Nat.card Bool = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  rw [Nat.card_prod, Nat.card_zpowers, hB] at hcard
  have hord4 : orderOf (⟨a, ha⟩ : R) ≤ 4 :=
    orderOf_le_of_pow_eq_one (by norm_num) (Subtype.ext ha4)
  omega
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628
