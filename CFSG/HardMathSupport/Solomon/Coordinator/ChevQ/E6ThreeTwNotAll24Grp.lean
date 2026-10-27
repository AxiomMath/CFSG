module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.Coprime.Lemmas
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSNotAll24

open scoped commutatorElement

theorem card_zpowers_sup_zpowers {G : Type*} [Group G] {a b : G} (hab : Commute a b)
    (ha : a ≠ 1) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hb : b ∉ Subgroup.zpowers a) :
    Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) = 3 ^ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hb (by simp)
  have ho_a : orderOf a = 3 := orderOf_eq_prime ha3 ha
  have ho_b : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  haveI : Finite (Subgroup.zpowers b) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, ho_b]; norm_num)
  have hbC : b ∈ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [SetLike.mem_coe] at hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact (hab.zpow_left k).eq
  have hnormal : Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer (Subgroup.zpowers a : Set G) hbC
  have hdisj : Disjoint (Subgroup.zpowers a) (Subgroup.zpowers b) := by
    rw [disjoint_iff]
    have hdvd : Nat.card ↥(Subgroup.zpowers a ⊓ Subgroup.zpowers b) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le
        (inf_le_right : Subgroup.zpowers a ⊓ Subgroup.zpowers b ≤ Subgroup.zpowers b)
      rwa [Nat.card_zpowers, ho_b] at h
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      have heq : Subgroup.zpowers a ⊓ Subgroup.zpowers b = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, Nat.card_zpowers, ho_b])
      have hbmem : b ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b := by
        rw [heq]
        exact Subgroup.mem_zpowers b
      exact hb (Subgroup.mem_inf.1 hbmem).1
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (Subgroup.zpowers a) (Subgroup.zpowers b) hnormal hdisj, Nat.card_zpowers,
    Nat.card_zpowers, ho_a, ho_b, pow_two]

theorem relIndex_eq_three {H : Type*} [Group H] {E F : Subgroup H} (hFE : F ≤ E)
    (hE : Nat.card E = 3 ^ 3) (hF : Nat.card F = 3 ^ 2) : F.relIndex E = 3 := by
  have h := Subgroup.relIndex_mul_card (H := F) (K := E)
  rw [inf_of_le_left hFE, hF, hE] at h
  norm_num at h
  omega

theorem mulAut_eq_one_of_central_diff {J : Type*} [Group J] (hJ : commutator J = ⊤)
    (φ : MulAut J) (h : ∀ x : J, φ x * x⁻¹ ∈ Subgroup.center J) : φ = 1 := by
  let lam : J →* Subgroup.center J :=
    { toFun := fun x => ⟨φ x * x⁻¹, h x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have hb := Subgroup.mem_center_iff.1 (h b)
        show φ (a * b) * (a * b)⁻¹ = (φ a * a⁻¹) * (φ b * b⁻¹)
        calc φ (a * b) * (a * b)⁻¹ = φ a * ((φ b * b⁻¹) * a⁻¹) := by rw [map_mul]; group
          _ = φ a * (a⁻¹ * (φ b * b⁻¹)) := by rw [← hb a⁻¹]
          _ = (φ a * a⁻¹) * (φ b * b⁻¹) := by group }
  have hker : commutator J ≤ lam.ker := Abelianization.commutator_subset_ker lam
  rw [hJ] at hker
  ext x
  have h1 : lam x = 1 := hker (Subgroup.mem_top x)
  have h2 : φ x * x⁻¹ = 1 := congrArg Subtype.val h1
  show φ x = x
  exact mul_inv_eq_one.1 h2

noncomputable def quotCenterHom (J : Type*) [Group J] :
    MulAut J →* MulAut (J ⧸ Subgroup.center J) where
  toFun φ := QuotientGroup.congr (Subgroup.center J) (Subgroup.center J) φ
    (Subgroup.map_center_eq φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with | H a => ?_
    simp [QuotientGroup.congr_mk]
  map_mul' := by
    intro φ ψ
    ext x
    induction x using QuotientGroup.induction_on with | H a => ?_
    simp [QuotientGroup.congr_mk]

theorem quotCenterHom_mk {J : Type*} [Group J] (φ : MulAut J) (a : J) :
    quotCenterHom J φ (a : J ⧸ Subgroup.center J) = ((φ a : J) : J ⧸ Subgroup.center J) := by
  simp [quotCenterHom, QuotientGroup.congr_mk]

theorem quotCenterHom_injective {J : Type*} [Group J] (hJ : commutator J = ⊤) :
    Function.Injective (quotCenterHom J) := by
  rw [injective_iff_map_eq_one]
  intro φ hφ
  refine mulAut_eq_one_of_central_diff hJ φ (fun x => ?_)
  have h1 : quotCenterHom J φ (x : J ⧸ Subgroup.center J) = (x : J ⧸ Subgroup.center J) := by
    simp [hφ]
  rw [quotCenterHom_mk] at h1
  have hc : (φ x)⁻¹ * x ∈ Subgroup.center J := QuotientGroup.eq.1 h1
  have hgx : φ x * x = x * φ x := by
    have h3 := Subgroup.mem_center_iff.1 hc (φ x)
    rw [mul_inv_cancel_left] at h3
    calc φ x * x = φ x * ((φ x)⁻¹ * x * φ x) := by rw [← h3]
      _ = x * φ x := by group
  have key : φ x * x⁻¹ = x⁻¹ * φ x := by
    calc φ x * x⁻¹ = x⁻¹ * (x * φ x) * x⁻¹ := by group
      _ = x⁻¹ * (φ x * x) * x⁻¹ := by rw [hgx]
      _ = x⁻¹ * φ x := by group
  have hfin : φ x * x⁻¹ = ((φ x)⁻¹ * x)⁻¹ := by
    rw [mul_inv_rev, inv_inv, key]
  rw [hfin]
  exact Subgroup.inv_mem _ hc

theorem commutatorElement_mul_central_left {J : Type*} [Group J] (g k z : J)
    (hz : z ∈ Subgroup.center J) : ⁅g * z, k⁆ = ⁅g, k⁆ := by
  have hk : z * k * z⁻¹ = k := by
    rw [← Subgroup.mem_center_iff.1 hz k, mul_inv_cancel_right]
  have e : ⁅g * z, k⁆ = g * (z * k * z⁻¹) * g⁻¹ * k⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e, hk, commutatorElement_def]

theorem commutatorElement_mul_central_right {J : Type*} [Group J] (g k z : J)
    (hz : z ∈ Subgroup.center J) : ⁅g, k * z⁆ = ⁅g, k⁆ := by
  have hg : z * g⁻¹ * z⁻¹ = g⁻¹ := by
    rw [← Subgroup.mem_center_iff.1 hz g⁻¹, mul_inv_cancel_right]
  have e : ⁅g, k * z⁆ = g * k * (z * g⁻¹ * z⁻¹) * k⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e, hg, commutatorElement_def]

theorem eq_top_of_mul_center {J : Type*} [Group J] (hJ : commutator J = ⊤) {H : Subgroup J}
    (hH : ∀ x : J, ∃ h ∈ H, ∃ z ∈ Subgroup.center J, x = h * z) : H = ⊤ := by
  have hcomm : commutator J ≤ H := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    obtain ⟨h₁, hh₁, z₁, hz₁, rfl⟩ := hH g₁
    obtain ⟨h₂, hh₂, z₂, hz₂, rfl⟩ := hH g₂
    rw [commutatorElement_mul_central_left h₁ (h₂ * z₂) z₁ hz₁,
      commutatorElement_mul_central_right h₁ h₂ z₂ hz₂, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hh₁ hh₂) (H.inv_mem hh₁)) (H.inv_mem hh₂)
  rw [hJ] at hcomm
  exact top_le_iff.1 hcomm

theorem exists_fixed_mul_center {J : Type*} [Group J] [Finite J] (δ : MulAut J)
    (hδ : δ ^ 3 = 1) (hZ : ¬ 3 ∣ Nat.card (Subgroup.center J)) (x : J)
    (hx : (δ x)⁻¹ * x ∈ Subgroup.center J) :
    ∃ w ∈ Subgroup.center J, δ (x * w) = x * w := by
  have hZc : ∀ g z : J, z ∈ Subgroup.center J → g * z = z * g :=
    fun g z hz => Subgroup.mem_center_iff.mp hz g
  have hδc : ∀ z ∈ Subgroup.center J, δ z ∈ Subgroup.center J := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨h, rfl⟩ := MulEquiv.surjective δ g
    rw [← map_mul, ← map_mul, hZc h z hz]
  have h3 : ∀ g, δ (δ (δ g)) = g := by
    intro g
    have h := congrArg (fun φ : MulAut J => φ g) hδ
    simpa only [pow_three', MulAut.mul_apply, MulAut.one_apply] using h
  have hn : ∀ g ∈ Subgroup.center J, g ^ Nat.card (Subgroup.center J) = 1 := by
    intro g hg
    have h := congrArg Subtype.val
      (pow_card_eq_one' (G := Subgroup.center J) (x := ⟨g, hg⟩))
    exact h
  obtain ⟨a, ha_def⟩ : ∃ a : J, a = x⁻¹ * δ x := ⟨_, rfl⟩
  have ha : a ∈ Subgroup.center J := by
    have h : a = ((δ x)⁻¹ * x)⁻¹ := by rw [ha_def, mul_inv_rev, inv_inv]
    rw [h]
    exact Subgroup.inv_mem _ hx
  have e1 : δ x = x * a := by rw [ha_def, mul_inv_cancel_left]
  obtain ⟨b, hb_def⟩ : ∃ b : J, b = δ a := ⟨_, rfl⟩
  obtain ⟨c, hc_def⟩ : ∃ c : J, c = δ b := ⟨_, rfl⟩
  have hb : b ∈ Subgroup.center J := by rw [hb_def]; exact hδc a ha
  have hc : c ∈ Subgroup.center J := by rw [hc_def]; exact hδc b hb
  have e2 : δ (δ x) = x * a * b := by rw [e1, map_mul, e1, ← hb_def]
  have e3 : δ (δ (δ x)) = x * a * b * c := by
    rw [e2, map_mul, map_mul, e1, ← hb_def, ← hc_def]
  have hx3 : x * a * b * c = x := e3.symm.trans (h3 x)
  have key : a * b * c = 1 := by
    apply mul_left_cancel (a := x)
    rw [mul_one]
    simpa only [mul_assoc] using hx3
  have hc' : c = b⁻¹ * a⁻¹ := by
    rw [eq_inv_of_mul_eq_one_right key, mul_inv_rev]
  have hab : a * b = b * a := hZc a b hb
  have hid : a ^ 3 * (b ^ 2 * c) = a ^ 2 * b := by
    rw [hc']
    calc a ^ 3 * (b ^ 2 * (b⁻¹ * a⁻¹)) = a ^ 2 * (a * b) * a⁻¹ := by group
      _ = a ^ 2 * (b * a) * a⁻¹ := by rw [hab]
      _ = a ^ 2 * b := by group
  have hδP : δ (a ^ 2 * b) = b ^ 2 * c := by
    rw [map_mul, map_pow, ← hb_def, ← hc_def]
  have hQ : b ^ 2 * c ∈ Subgroup.center J :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ hb 2) hc
  have hP : a ^ 2 * b ∈ Subgroup.center J :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ ha 2) hb
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.center J)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have huv' : (3 : ℤ) * u + v * (Nat.card (Subgroup.center J) : ℤ) = 1 := by
    push_cast at huv
    linear_combination huv
  have hapow : a ^ ((3 : ℤ) * u) = a := by
    have h1 : a ^ ((3 : ℤ) * u) * a ^ (v * (Nat.card (Subgroup.center J) : ℤ)) = a := by
      rw [← zpow_add, huv', zpow_one]
    have h2 : a ^ (v * (Nat.card (Subgroup.center J) : ℤ)) = 1 := by
      rw [zpow_mul', zpow_natCast, hn a ha, one_zpow]
    rwa [h2, mul_one] at h1
  have hcube : (a ^ 3) ^ u = a := by
    rw [← zpow_natCast, ← zpow_mul]
    push_cast
    exact hapow
  have hcomm : Commute (a ^ 3) (b ^ 2 * c) := hZc (a ^ 3) (b ^ 2 * c) hQ
  have hfix : (a ^ 2 * b) ^ u = a * (b ^ 2 * c) ^ u := by
    rw [← hid, hcomm.mul_zpow, hcube]
  refine ⟨(a ^ 2 * b) ^ u, Subgroup.zpow_mem _ hP u, ?_⟩
  rw [map_mul, e1, map_zpow, hδP, hfix, mul_assoc]

end KSNotAll24

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
