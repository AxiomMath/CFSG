module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction629.TwoGroups

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

def dihedral_phi {G : Type} [Group G] (ρ σ : G) (n : ℕ) : DihedralGroup n → G
  | DihedralGroup.r i => quatEquiv_pw ρ i
  | DihedralGroup.sr i => σ * quatEquiv_pw ρ i

theorem dihedral_phi_mul {G : Type} [Group G] {ρ σ : G} {n : ℕ} [NeZero n] (hρ : orderOf ρ = n)
    (hσ2 : σ ^ 2 = 1) (hσρ : σ * ρ * σ⁻¹ = ρ⁻¹) (u v : DihedralGroup n) :
    dihedral_phi ρ σ n (u * v) = dihedral_phi ρ σ n u * dihedral_phi ρ σ n v := by
  cases u <;> cases v
  · simp only [dihedral_phi, DihedralGroup.r_mul_r]
    exact quatEquiv_pw_add hρ _ _
  · simp only [dihedral_phi, DihedralGroup.r_mul_sr]
    rw [quatEquiv_pw_sub hρ, ← mul_assoc (quatEquiv_pw ρ _) σ, quatEquiv_pw_mul_y hσρ, mul_assoc]
  · simp only [dihedral_phi, DihedralGroup.sr_mul_r]
    rw [quatEquiv_pw_add hρ, mul_assoc]
  · simp only [dihedral_phi, DihedralGroup.sr_mul_sr]
    rw [quatEquiv_pw_sub hρ, quatEquiv_xx_aux σ _ _ (quatEquiv_pw_mul_y hσρ _), hσ2, one_mul]

theorem dihedral_phi_inj {G : Type} [Group G] {ρ σ : G} {n : ℕ} [NeZero n] (hρ : orderOf ρ = n)
    (hσ : σ ∉ Subgroup.zpowers ρ) : Function.Injective (dihedral_phi ρ σ n) := by
  rintro (i | i) (j | j) h
  · simp only [dihedral_phi] at h
    rw [quatEquiv_pw_inj hρ h]
  · exfalso
    simp only [dihedral_phi] at h
    apply hσ
    have hy : σ = quatEquiv_pw ρ i * (quatEquiv_pw ρ j)⁻¹ := eq_mul_inv_of_mul_eq h.symm
    rw [hy]
    exact mul_mem (quatEquiv_pw_mem i) (inv_mem (quatEquiv_pw_mem j))
  · exfalso
    simp only [dihedral_phi] at h
    apply hσ
    have hy : σ = quatEquiv_pw ρ j * (quatEquiv_pw ρ i)⁻¹ := eq_mul_inv_of_mul_eq h
    rw [hy]
    exact mul_mem (quatEquiv_pw_mem j) (inv_mem (quatEquiv_pw_mem i))
  · simp only [dihedral_phi] at h
    have h2 : quatEquiv_pw ρ i = quatEquiv_pw ρ j := mul_left_cancel h
    rw [quatEquiv_pw_inj hρ h2]

theorem dihedral_phi_surj {G : Type} [Group G] {ρ σ : G} {n : ℕ} [NeZero n] (hρ : orderOf ρ = n)
    (hcover : ∀ g : G, g ∈ Subgroup.zpowers ρ ∨ σ⁻¹ * g ∈ Subgroup.zpowers ρ) :
    Function.Surjective (dihedral_phi ρ σ n) := by
  intro g
  rcases hcover g with hg | hg
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨DihedralGroup.r (k : ZMod n), ?_⟩
    simp only [dihedral_phi]
    rw [quatEquiv_pw_cast hρ k, hk]
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨DihedralGroup.sr (k : ZMod n), ?_⟩
    simp only [dihedral_phi]
    rw [quatEquiv_pw_cast hρ k, hk, mul_inv_cancel_left]

theorem dihedral_equiv_of_cover {G : Type} [Group G] [Finite G] {ρ σ : G} {n : ℕ} (hn : 1 ≤ n)
    (hρ : orderOf ρ = n) (hσ2 : σ ^ 2 = 1) (hσρ : σ * ρ * σ⁻¹ = ρ⁻¹)
    (hσ : σ ∉ Subgroup.zpowers ρ)
    (hcover : ∀ g : G, g ∈ Subgroup.zpowers ρ ∨ σ⁻¹ * g ∈ Subgroup.zpowers ρ) :
    Nonempty (G ≃* DihedralGroup n) ∧ Nat.card G = 2 * n := by
  haveI : NeZero n := ⟨by omega⟩
  let f : DihedralGroup n →* G :=
    MonoidHom.mk' (dihedral_phi ρ σ n) (dihedral_phi_mul hρ hσ2 hσρ)
  have hf : Function.Bijective f := ⟨dihedral_phi_inj hρ hσ, dihedral_phi_surj hρ hcover⟩
  let e : G ≃* DihedralGroup n := (MulEquiv.ofBijective f hf).symm
  refine ⟨⟨e⟩, ?_⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
end

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem smallSub_mem_zpowers_sub {G : Type} [Group G] {H : Subgroup G} (a g : H) :
    g ∈ zpowers a ↔ (g : G) ∈ zpowers (a : G) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
    exact mem_zpowers_iff.mpr ⟨k, by rw [← hk]; simp⟩
  · intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
    exact mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩

theorem smallSub_cover_sub {G : Type} [Group G] {H : Subgroup G} (a y : H)
    (hcover : ∀ g ∈ H, (g ∈ zpowers (a : G)) ∨ (y : G)⁻¹ * g ∈ zpowers (a : G)) :
    ∀ g : H, g ∈ zpowers a ∨ y⁻¹ * g ∈ zpowers a := by
  intro g
  rcases hcover g g.2 with h | h
  · exact Or.inl ((smallSub_mem_zpowers_sub a g).mpr h)
  · exact Or.inr ((smallSub_mem_zpowers_sub a (y⁻¹ * g)).mpr (by simpa using h))

theorem smallSub_conj_mem {G : Type} [Group G] {a y : G} (h1 : y⁻¹ * a * y ∈ zpowers a) :
    ∀ x ∈ zpowers a, y⁻¹ * x * y ∈ zpowers a := by
  intro x hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have h : (y⁻¹ * a * y) ^ k = y⁻¹ * a ^ k * y := by
    simpa using conj_zpow (a := y⁻¹) (b := a) (i := k)
  rw [← h]
  exact zpow_mem h1 k

theorem smallSub_cover_mul_mem {G : Type} [Group G] {a y x z : G}
    (hconj : ∀ x ∈ zpowers a, y⁻¹ * x * y ∈ zpowers a) (hx : x ∈ zpowers a)
    (hz : z ∈ zpowers a ∨ y⁻¹ * z ∈ zpowers a) :
    x * z ∈ zpowers a ∨ y⁻¹ * (x * z) ∈ zpowers a := by
  rcases hz with hz | hz
  · exact Or.inl (mul_mem hx hz)
  · right
    have : y⁻¹ * (x * z) = (y⁻¹ * x * y) * (y⁻¹ * z) := by group
    rw [this]
    exact mul_mem (hconj x hx) hz

theorem smallSub_cover_mul_y {G : Type} [Group G] {a y z : G} (hy2 : y ^ 2 ∈ zpowers a)
    (hz : z ∈ zpowers a ∨ y⁻¹ * z ∈ zpowers a) :
    y * z ∈ zpowers a ∨ y⁻¹ * (y * z) ∈ zpowers a := by
  rcases hz with hz | hz
  · right
    rw [inv_mul_cancel_left]
    exact hz
  · left
    have : y * z = y ^ 2 * (y⁻¹ * z) := by group
    rw [this]
    exact mul_mem hy2 hz

theorem smallSub_cover_mul_yinv {G : Type} [Group G] {a y z : G} (hy2 : y ^ 2 ∈ zpowers a)
    (hz : z ∈ zpowers a ∨ y⁻¹ * z ∈ zpowers a) :
    y⁻¹ * z ∈ zpowers a ∨ y⁻¹ * (y⁻¹ * z) ∈ zpowers a := by
  rcases hz with hz | hz
  · right
    have : y⁻¹ * (y⁻¹ * z) = (y ^ 2)⁻¹ * z := by group
    rw [this]
    exact mul_mem (inv_mem hy2) hz
  · exact Or.inl hz

theorem smallSub_cover_closure {G : Type} [Group G] {a y : G}
    (h1 : y⁻¹ * a * y ∈ zpowers a) (hy2 : y ^ 2 ∈ zpowers a) {g : G}
    (hg : g ∈ Subgroup.closure ({a, y} : Set G)) :
    g ∈ zpowers a ∨ y⁻¹ * g ∈ zpowers a := by
  have hconj := smallSub_conj_mem h1
  refine Subgroup.closure_induction_left
    (p := fun g _ => g ∈ zpowers a ∨ y⁻¹ * g ∈ zpowers a) (Or.inl (one_mem _)) ?_ ?_ hg
  · intro x hx z _ hz
    have hx' : x = a ∨ x = y := by simpa using hx
    rcases hx' with hxa | hxy
    · rw [hxa]
      exact smallSub_cover_mul_mem hconj (mem_zpowers a) hz
    · rw [hxy]
      exact smallSub_cover_mul_y hy2 hz
  · intro x hx z _ hz
    have hx' : x = a ∨ x = y := by simpa using hx
    rcases hx' with hxa | hxy
    · rw [hxa]
      exact smallSub_cover_mul_mem hconj (inv_mem (mem_zpowers a)) hz
    · rw [hxy]
      exact smallSub_cover_mul_yinv hy2 hz

theorem smallSub_orderOf_four {G : Type} [Group G] {x : G} (h2 : x ^ 2 ≠ 1) (h4 : x ^ 4 = 1) :
    orderOf x = 4 := by
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x) (by simpa using h2) (by simpa using h4)
  simpa using this

theorem smallSub_not_mem_of_inv {G : Type} [Group G] {ρ σ : G} (hσρ : σ * ρ * σ⁻¹ = ρ⁻¹)
    (hρ2 : ρ ^ 2 ≠ 1) : σ ∉ zpowers ρ := by
  intro h
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp h
  have hc : ρ ^ k * ρ = ρ * ρ ^ k := (Commute.zpow_self ρ k).eq
  have h1 : ρ ^ k * ρ * (ρ ^ k)⁻¹ = ρ := by rw [hc]; group
  rw [h1] at hσρ
  apply hρ2
  rw [sq]
  exact mul_eq_one_iff_eq_inv.mpr hσρ

theorem smallSub_Q8_conj {G : Type} [Group G] {a b t : G} (ha : a ^ 2 = t) (hab : ⁅a, b⁆ = t)
    (ht2 : t ^ 2 = 1) : b * a * b⁻¹ = a⁻¹ := by
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ht2)
  have ha4 : a ^ 3 * a = 1 := by
    calc a ^ 3 * a = (a ^ 2) ^ 2 := by group
      _ = 1 := by rw [ha, ht2]
  have hba : ⁅b, a⁆ = t := by rw [← commutatorElement_inv, hab, ht]
  calc b * a * b⁻¹ = ⁅b, a⁆ * a := by rw [commutatorElement_def]; group
    _ = a ^ 3 := by rw [hba, ← ha]; group
    _ = a⁻¹ := eq_inv_of_mul_eq_one_left ha4

theorem smallSub_Q8_center {G : Type} [Group G] {a b t g : G} (ha : a ^ 2 = t) (hab : ⁅a, b⁆ = t)
    (ht1 : t ≠ 1) (hbab : b * a * b⁻¹ = a⁻¹) (hord : orderOf a = 4)
    (hg : g ∈ zpowers a ∨ b⁻¹ * g ∈ zpowers a) (hga : g * a = a * g) (hgb : g * b = b * g) :
    g ∈ zpowers t := by
  rcases hg with hg | hg
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    have h1 : b * a ^ k * b⁻¹ = a ^ (-k) := quatEquiv_conj_zpow hbab k
    have h2 : b * a ^ k * b⁻¹ = a ^ k := by
      rw [← hgb]
      group
    have h : a ^ k = a ^ (-k) := h2.symm.trans h1
    have h3 : a ^ (2 * k) = 1 := by
      calc a ^ (2 * k) = a ^ k * a ^ k := by rw [two_mul, zpow_add]
        _ = a ^ (-k) * a ^ k := by rw [← h]
        _ = 1 := by rw [← zpow_add, neg_add_cancel, zpow_zero]
    have h4 : ((4 : ℕ) : ℤ) ∣ 2 * k := hord ▸ orderOf_dvd_iff_zpow_eq_one.mpr h3
    have h5 : ∃ j : ℤ, k = 2 * j := by
      push_cast at h4
      exact ⟨k / 2, by omega⟩
    obtain ⟨j, rfl⟩ := h5
    have hat : a ^ (2 : ℤ) = t := by
      rw [zpow_two, ← sq]
      exact ha
    exact mem_zpowers_iff.mpr ⟨j, by rw [zpow_mul, hat]⟩
  · exfalso
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hg
    have hgk : g = b * a ^ k := by
      rw [hk]
      group
    have hab2 : a * b * a⁻¹ * b⁻¹ = t := hab
    have hab' : a * b = t * b * a := by
      calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
        _ = t * b * a := by rw [hab2]
    have hc : a ^ k * a = a * a ^ k := (Commute.zpow_self a k).eq
    have key : t * b * a * a ^ k = b * a * a ^ k := by
      calc t * b * a * a ^ k = (a * b) * a ^ k := by rw [hab']
        _ = a * (b * a ^ k) := by rw [mul_assoc]
        _ = a * g := by rw [hgk]
        _ = g * a := hga.symm
        _ = b * a ^ k * a := by rw [hgk]
        _ = b * (a ^ k * a) := by rw [mul_assoc]
        _ = b * (a * a ^ k) := by rw [hc]
        _ = b * a * a ^ k := by rw [mul_assoc]
    have key2 : t * b = b := mul_right_cancel (mul_right_cancel key)
    exact ht1 (mul_eq_right.mp key2)

theorem exists_Q8_subgroup {a b t : K} (ha : a ^ 2 = t) (hb : b ^ 2 = t) (hab : ⁅a, b⁆ = t)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    Nonempty (↥(Subgroup.closure ({a, b} : Set K)) ≃* QuaternionGroup 2) ∧
      Nat.card ↥(Subgroup.closure ({a, b} : Set K)) = 8 ∧
      ∀ g ∈ Subgroup.closure ({a, b} : Set K),
        (∀ h ∈ Subgroup.closure ({a, b} : Set K), g * h = h * g) → g ∈ zpowers t := by
  have hbab : b * a * b⁻¹ = a⁻¹ := smallSub_Q8_conj ha hab ht2
  have ha4 : a ^ 4 = 1 := by
    calc a ^ 4 = (a ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [ha, ht2]
  have hord : orderOf a = 4 := smallSub_orderOf_four (by rw [ha]; exact ht1) ha4
  have hba' : b * a = a⁻¹ * b := mul_inv_eq_iff_eq_mul.mp hbab
  have hinv : b⁻¹ * a * b = a⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc b⁻¹ * a * b * a = b⁻¹ * a * (b * a) := by rw [mul_assoc (b⁻¹ * a)]
      _ = b⁻¹ * a * (a⁻¹ * b) := by rw [hba']
      _ = 1 := by group
  have hcoverK : ∀ g ∈ Subgroup.closure ({a, b} : Set K),
      g ∈ zpowers a ∨ b⁻¹ * g ∈ zpowers a := by
    intro g hg
    refine smallSub_cover_closure ?_ ?_ hg
    · rw [hinv]
      exact inv_mem (mem_zpowers a)
    · rw [hb, ← ha]
      exact pow_mem (mem_zpowers a) 2
  set H := Subgroup.closure ({a, b} : Set K) with hH
  have haH : a ∈ H := subset_closure (by simp)
  have hbH : b ∈ H := subset_closure (by simp)
  obtain ⟨a', ha'⟩ : ∃ a' : H, (a' : K) = a := ⟨⟨a, haH⟩, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : H, (b' : K) = b := ⟨⟨b, hbH⟩, rfl⟩
  have hord' : orderOf a' = 2 * 2 ^ 1 := by
    rw [← Subgroup.orderOf_coe, ha', hord]
    norm_num
  have hyinv' : b' * a' * b'⁻¹ = a'⁻¹ :=
    Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, ha', hb']; exact hbab)
  have hy2' : b' ^ 2 = a' ^ (2 ^ 1) :=
    Subtype.ext (by simp [ha', hb', ha, hb])
  have hyA' : b' ∉ zpowers a' := by
    refine smallSub_not_mem_of_inv hyinv' ?_
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hord'] at this
    norm_num at this
  have hcov' := smallSub_cover_sub a' b' (by
    intro g hg
    rw [ha', hb']
    exact hcoverK g hg)
  obtain ⟨⟨e⟩, hcard⟩ := quaternion_equiv_of_cover hord' hyinv' hy2' hyA' hcov'
  refine ⟨⟨e⟩, hcard, ?_⟩
  intro g hg hcomm
  exact smallSub_Q8_center ha hab ht1 hbab hord (hcoverK g hg) (hcomm a haH) (hcomm b hbH)

theorem exists_D8_subgroup {s s' t : K} (hs : s ^ 2 = 1) (hs' : s' ^ 2 = 1) (hss' : ⁅s, s'⁆ = t)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    Nonempty (↥(Subgroup.closure ({s, s'} : Set K)) ≃* DihedralGroup 4) ∧
      Nat.card ↥(Subgroup.closure ({s, s'} : Set K)) = 8 := by
  have hss : s * s = 1 := by rw [← sq]; exact hs
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hs'inv : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hs')
  have hρ2 : (s * s') ^ 2 = t := by
    rw [← hss', commutatorElement_def, hsinv, hs'inv, sq]
    simp only [mul_assoc]
  have hρ4 : (s * s') ^ 4 = 1 := by
    calc (s * s') ^ 4 = ((s * s') ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [hρ2, ht2]
  have hρord : orderOf (s * s') = 4 := smallSub_orderOf_four (by rw [hρ2]; exact ht1) hρ4
  have hσρ : s * (s * s') * s⁻¹ = (s * s')⁻¹ := by
    calc s * (s * s') * s⁻¹ = (s * s) * s' * s := by rw [hsinv]; simp only [mul_assoc]
      _ = s' * s := by rw [hss, one_mul]
      _ = (s * s')⁻¹ := by rw [mul_inv_rev, hsinv, hs'inv]
  set H := Subgroup.closure ({s, s'} : Set K) with hH
  have hsH : s ∈ H := subset_closure (by simp)
  have hs'H : s' ∈ H := subset_closure (by simp)
  have hcoverK : ∀ g ∈ H, g ∈ zpowers (s * s') ∨ s⁻¹ * g ∈ zpowers (s * s') := by
    intro g hg
    have hsC : s ∈ Subgroup.closure ({s * s', s} : Set K) := subset_closure (by simp)
    have hρC : s * s' ∈ Subgroup.closure ({s * s', s} : Set K) := subset_closure (by simp)
    have hle : H ≤ Subgroup.closure ({s * s', s} : Set K) := by
      rw [hH, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hsC, by simpa using mul_mem (inv_mem hsC) hρC⟩
    refine smallSub_cover_closure (a := s * s') (y := s) ?_ ?_ (hle hg)
    · rw [hsinv] at hσρ ⊢
      rw [hσρ]
      exact inv_mem (mem_zpowers _)
    · rw [hs]
      exact one_mem _
  obtain ⟨ρ, hρ⟩ : ∃ ρ : H, (ρ : K) = s * s' := ⟨⟨s * s', mul_mem hsH hs'H⟩, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : H, (σ : K) = s := ⟨⟨s, hsH⟩, rfl⟩
  have hρord' : orderOf ρ = 4 := by
    rw [← Subgroup.orderOf_coe, hρ, hρord]
  have hσ2 : σ ^ 2 = 1 := Subtype.ext (by simpa [hσ] using hs)
  have hσρ' : σ * ρ * σ⁻¹ = ρ⁻¹ :=
    Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, hρ, hσ]; exact hσρ)
  have hσnot : σ ∉ zpowers ρ := by
    refine smallSub_not_mem_of_inv hσρ' ?_
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hρord'] at this
    norm_num at this
  have hcov' := smallSub_cover_sub ρ σ (by
    intro g hg
    rw [hρ, hσ]
    exact hcoverK g hg)
  obtain ⟨⟨e⟩, hcard⟩ := dihedral_equiv_of_cover (by norm_num) hρord' hσ2 hσρ' hσnot hcov'
  exact ⟨⟨e⟩, hcard⟩
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628
