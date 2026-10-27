module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.LeafBal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectSubnormal
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAut
public import CFSG.CharacterTheory.Semidihedral.ProjectiveSL2Cover

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec7
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.Leaf

section Fixed

variable {G : Type} [Group G]

theorem exists_fixed_of_involutive_odd {α : Type} [Finite α] (hα : Odd (Nat.card α)) {f : α → α}
    (hf : Function.Involutive f) : ∃ x, f x = x := by
  classical
  have := Fintype.ofFinite α
  by_contra hcon
  push Not at hcon
  let σ : Equiv.Perm α := hf.toPerm f
  have hσ2 : σ ^ 2 = 1 := by
    ext x
    show f (f x) = x
    exact hf x
  have hdvd := Equiv.Perm.two_dvd_card_support hσ2
  have hsupp : σ.support = Finset.univ := by
    ext x
    simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
    exact hcon x
  rw [hsupp, Finset.card_univ] at hdvd
  rw [Nat.card_eq_fintype_card] at hα
  exact (Nat.not_even_iff_odd.2 hα) (even_iff_two_dvd.2 hdvd)

theorem exists_centralized_in_coset [Finite G] {O : Subgroup G} (hO : Odd (Nat.card ↥O)) {z x : G}
    (hz : z * z = 1) (hzO : ∀ o ∈ O, z * o * z⁻¹ ∈ O) (hx : x⁻¹ * (z * x * z⁻¹) ∈ O) :
    ∃ o ∈ O, z * (x * o) * z⁻¹ = x * o := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  set y := x⁻¹ * (z * x * z⁻¹) with hy
  have hyz : y * (z * y * z⁻¹) = 1 := by
    have h1 : z * (z * x * z⁻¹) * z⁻¹ = x := by
      calc z * (z * x * z⁻¹) * z⁻¹ = (z * z) * x * (z * z)⁻¹ := by group
        _ = x := by rw [hz]; group
    calc y * (z * y * z⁻¹) = x⁻¹ * (z * x * z⁻¹) * (z * (x⁻¹ * (z * x * z⁻¹)) * z⁻¹) := by rw [hy]
      _ = x⁻¹ * (z * (z * x * z⁻¹) * z⁻¹) := by group
      _ = 1 := by rw [h1]; group
  let f : ↥O → ↥O := fun o => ⟨y * (z * (o : G) * z⁻¹), O.mul_mem hx (hzO o o.2)⟩
  have hf : Function.Involutive f := by
    intro o
    apply Subtype.ext
    show y * (z * (y * (z * (o : G) * z⁻¹)) * z⁻¹) = o
    calc y * (z * (y * (z * (o : G) * z⁻¹)) * z⁻¹)
        = (y * (z * y * z⁻¹)) * ((z * z) * (o : G) * (z * z)⁻¹) := by group
      _ = o := by rw [hyz, hz]; group
  obtain ⟨o, ho⟩ := exists_fixed_of_involutive_odd (by simpa using hO) hf
  have ho' : y * (z * (o : G) * z⁻¹) = o := congrArg Subtype.val ho
  refine ⟨o, o.2, ?_⟩
  calc z * (x * o) * z⁻¹ = (z * x * z⁻¹) * (z * (o : G) * z⁻¹) := by group
    _ = x * (y * (z * (o : G) * z⁻¹)) := by rw [hy]; group
    _ = x * o := by rw [ho']

end Fixed

section PSL

variable {Q : Type} [Group Q] {F : Type} [Field F]

theorem exists_innEquiv (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    Nonempty (↥(innOf Q) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  have hker : (MulAut.conj : Q →* MulAut Q).ker = Subgroup.center Q := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h x
      have := congrArg (fun ρ : MulAut Q => ρ x) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc x * y = (y * x * y⁻¹) * y := by rw [this]
        _ = y * x := by group
    · intro h
      ext x
      rw [MulAut.conj_apply, MulAut.one_apply]
      calc y * x * y⁻¹ = (x * y) * y⁻¹ := by rw [h x]
        _ = x := by group
  have hmap : (Subgroup.center Q).map e.toMonoidHom =
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := Subgroup.map_center_eq e
  exact ⟨(QuotientGroup.quotientKerEquivRange (MulAut.conj : Q →* MulAut Q)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.congr (Subgroup.center Q)
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) e hmap))⟩

theorem inn_perfect_subnormal_eq_top [Finite F] (hodd : Odd (Nat.card F))
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F) (J : Subgroup ↥(innOf Q)) (hJne : J ≠ ⊥)
    (hJperf : ⁅J, J⁆ = J) (hJsn : J.IsSubnormal) : J = ⊤ := by
  obtain ⟨τ⟩ := exists_innEquiv e
  have hK := CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hodd
  have hne : J.map τ.toMonoidHom ≠ ⊥ := by
    intro h
    exact hJne ((Subgroup.map_eq_bot_iff_of_injective _ (show Function.Injective τ.toMonoidHom from τ.injective)).1 h)
  have hperf : Group.IsPerfect ↥(J.map τ.toMonoidHom) := by
    refine Subgroup.isPerfect_iff.2 ?_
    rw [← Subgroup.map_commutator, hJperf]
  have hsn : (J.map τ.toMonoidHom).IsSubnormal := hJsn.map τ.surjective
  obtain ⟨-, htop⟩ := CFSG.GorensteinWalter.psl2_perfect_subnormal_eq_top F hK _ hne hperf hsn
  have := Subgroup.comap_map_eq_self_of_injective (show Function.Injective τ.toMonoidHom from τ.injective) J
  rw [htop, Subgroup.comap_top] at this
  exact this.symm

end PSL

section Hats

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem hatMk_mul_inv_eq_one {K : Subgroup G} {a b : G} (ha : a ∈ K) (hb : b ∈ K)
    (h : hatMk K ⟨a, ha⟩ = hatMk K ⟨b, hb⟩) : a⁻¹ * b ∈ pPrimeCoreOf 2 K := by
  have h1 : hatMk K ⟨a⁻¹ * b, K.mul_mem (K.inv_mem ha) hb⟩ = 1 := by
    have : (⟨a⁻¹ * b, K.mul_mem (K.inv_mem ha) hb⟩ : ↥K) = ⟨a, ha⟩⁻¹ * ⟨b, hb⟩ := Subtype.ext rfl
    rw [this, map_mul, map_inv, h, inv_mul_cancel]
  exact (hatMk_eq_one_iff K _).1 h1

theorem center_hat {K : Subgroup G} {F : Type} [Field F]
    (e : Hat K ≃* Matrix.SpecialLinearGroup (Fin 2) F) {t : G} (ht : t ∈ K) (ht2 : t * t = 1)
    (ht1 : t ≠ 1) (htc : ∀ x ∈ K, t * x = x * t) :
    ∀ x ∈ Subgroup.center (Hat K), x = 1 ∨ x = hatMk K ⟨t, ht⟩ := by
  have hne : hatMk K ⟨t, ht⟩ ≠ 1 := by
    intro h
    have hmem : t ∈ pPrimeCoreOf 2 K := (hatMk_eq_one_iff K ⟨t, ht⟩).1 h
    have hodd := TwoThin.card_pPrimeCoreOf_odd K
    have hord : orderOf t = 2 := orderOf_eq_prime (by simpa [pow_two] using ht2) ht1
    have := Subgroup.orderOf_dvd_natCard (pPrimeCoreOf 2 K) hmem
    rw [hord] at this
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 this)
  have hcen : hatMk K ⟨t, ht⟩ ∈ Subgroup.center (Hat K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := hatMk_surjective K y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (htc k k.2).symm
  have hcenSL : ∀ x ∈ Subgroup.center (Hat K),
      e x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    intro x hx
    rw [← Subgroup.map_center_eq e]
    exact Subgroup.mem_map_of_mem _ hx
  have het : e (hatMk K ⟨t, ht⟩) = CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F := by
    rcases (CFSG.Semidihedral.ProjectiveSL2Cover.mem_center_iff_eq_one_or_minusIdentity F _).1 (hcenSL _ hcen) with h | h
    · exact absurd (e.injective (h.trans (map_one e).symm)) hne
    · exact h
  intro x hx
  rcases (CFSG.Semidihedral.ProjectiveSL2Cover.mem_center_iff_eq_one_or_minusIdentity F _).1 (hcenSL x hx) with h | h
  · left; exact e.injective (h.trans (map_one e).symm)
  · right; exact e.injective (h.trans het.symm)

omit [Finite G] in
theorem mem_center_of_conj_eq_one' {Q : Type} [Group Q] {c : Q} (h : MulAut.conj c = 1) :
    c ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff]
  intro x
  have := congrArg (fun ρ : MulAut Q => ρ x) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc x * c = (c * x * c⁻¹) * c := by rw [this]
    _ = c * x := by group

theorem split_center {K : Subgroup G} {F : Type} [Field F]
    (e : Hat K ≃* Matrix.SpecialLinearGroup (Fin 2) F) {t : G} (ht : t ∈ K) (ht2 : t * t = 1)
    (ht1 : t ≠ 1) (htc : ∀ x ∈ K, t * x = x * t) {a : G} (ha : a ∈ K)
    (hc : MulAut.conj (hatMk K ⟨a, ha⟩) = 1) :
    ∃ ε ∈ zpowers t, ∃ o ∈ pPrimeCoreOf 2 K, a = ε * o := by
  rcases center_hat e ht ht2 ht1 htc _ (mem_center_of_conj_eq_one' hc) with hh | hh
  · exact ⟨1, one_mem _, a, (hatMk_eq_one_iff K ⟨a, ha⟩).1 hh, by simp⟩
  · refine ⟨t, mem_zpowers t, t⁻¹ * a, ?_, by group⟩
    exact hatMk_mul_inv_eq_one ht ha hh.symm

section Diag

variable {z t : G} {A₁ A₂ O : Subgroup G}

structure Diag31 (z t : G) (A₁ A₂ O : Subgroup G) : Prop where
  z_sq : z * z = 1
  t_sq : t * t = 1
  t_ne : t ≠ 1
  tA₁ : t ∈ A₁
  tA₂ : t ∈ A₂
  tcomm : ∀ x ∈ A₁ ⊔ A₂, t * x = x * t
  cz₁ : cmap z A₁ = A₂
  cs₁ : A₁ ≤ cSec A₂
  cs₂ : A₂ ≤ cSec A₁
  Oodd : Odd (Nat.card ↥O)
  OK : O ≤ A₁ ⊔ A₂
  Oz : ∀ o ∈ O, z * o * z⁻¹ ∈ O
  Ocs₁ : O ≤ cSec A₁
  Ohat₁ : pPrimeCoreOf 2 A₁ ≤ O
  Ohat₂ : pPrimeCoreOf 2 A₂ ≤ O

namespace Diag31

variable (h : Diag31 z t A₁ A₂ O)

include h

omit [Finite G] in
theorem A₂_le_N₁ : A₂ ≤ normalizer (A₁ : Set G) := fun _ hx => (h.cs₂ hx).1

omit [Finite G] in
theorem A₁_le_N₂ : A₁ ≤ normalizer (A₂ : Set G) := fun _ hx => (h.cs₁ hx).1

omit [Finite G] in
theorem K_le_N₁ : A₁ ⊔ A₂ ≤ normalizer (A₁ : Set G) := sup_le le_normalizer h.A₂_le_N₁

omit [Finite G] in
theorem K_le_N₂ : A₁ ⊔ A₂ ≤ normalizer (A₂ : Set G) := sup_le h.A₁_le_N₂ le_normalizer

omit [Finite G] in
theorem decomp {k : G} (hk : k ∈ A₁ ⊔ A₂) : ∃ a₁ ∈ A₁, ∃ a₂ ∈ A₂, k = a₁ * a₂ :=
  A.mem_sup_of_le_normalizer h.A₁_le_N₂ hk

omit [Finite G] in
theorem swap₁ {x : G} (hx : x ∈ A₁) : z * x * z⁻¹ ∈ A₂ := by
  rw [← h.cz₁, mem_cmap]
  have : z⁻¹ * (z * x * z⁻¹) * z = x := by group
  rw [this]; exact hx

omit [Finite G] in
theorem phi₁_prod {a₁ a₂ : G} (ha₁ : a₁ ∈ A₁) (ha₂ : a₂ ∈ A₂) :
    phi A₁ (a₁ * a₂) (h.K_le_N₁ (mul_mem_sup ha₁ ha₂)) = MulAut.conj (hatMk A₁ ⟨a₁, ha₁⟩) := by
  rw [phi_mul A₁ (le_normalizer ha₁) (h.A₂_le_N₁ ha₂), phi_of_mem A₁ ha₁,
    (phi_eq_one_iff A₁ (h.A₂_le_N₁ ha₂)).2 (h.cs₂ ha₂), mul_one]

omit [Finite G] in
theorem phi₂_prod {a₁ a₂ : G} (ha₁ : a₁ ∈ A₁) (ha₂ : a₂ ∈ A₂) :
    phi A₂ (a₁ * a₂) (h.K_le_N₂ (mul_mem_sup ha₁ ha₂)) = MulAut.conj (hatMk A₂ ⟨a₂, ha₂⟩) := by
  rw [phi_mul A₂ (h.A₁_le_N₂ ha₁) (le_normalizer ha₂), phi_of_mem A₂ ha₂,
    (phi_eq_one_iff A₂ (h.A₁_le_N₂ ha₁)).2 (h.cs₁ ha₁), one_mul]

omit [Finite G] in
theorem cSec_swap {y : G} (hy : y ∈ cSec A₁) : z * y * z⁻¹ ∈ cSec A₂ := by
  have := cmap_mem_centralizerSection hy z
  rw [h.cz₁, ← pPrimeCoreOf_cmap, h.cz₁] at this
  exact this

omit [Finite G] in
theorem phi_mem_inn {y : G} (hy : y ∈ A₁ ⊔ A₂) : phi A₁ y (h.K_le_N₁ hy) ∈ innOf (Hat A₁) := by
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := h.decomp hy
  rw [h.phi₁_prod ha₁ ha₂]
  exact ⟨_, rfl⟩

theorem exists_lift {a : G} (ha : a ∈ A₁) :
    ∃ y : G, ∃ hy : y ∈ A₁ ⊔ A₂, y ∈ centralizer ({z} : Set G) ∧
      phi A₁ y (h.K_le_N₁ hy) = MulAut.conj (hatMk A₁ ⟨a, ha⟩) := by
  have hbA₂ : z * a * z⁻¹ ∈ A₂ := h.swap₁ ha
  have hnK : a * (z * a * z⁻¹) ∈ A₁ ⊔ A₂ := mul_mem_sup ha hbA₂
  have hzn : z * (a * (z * a * z⁻¹)) * z⁻¹ = (z * a * z⁻¹) * a := by
    have h1 : z * (z * a * z⁻¹) * z⁻¹ = a := by
      calc z * (z * a * z⁻¹) * z⁻¹ = (z * z) * a * (z * z)⁻¹ := by group
        _ = a := by rw [h.z_sq]; group
    calc z * (a * (z * a * z⁻¹)) * z⁻¹ = (z * a * z⁻¹) * (z * (z * a * z⁻¹) * z⁻¹) := by group
      _ = (z * a * z⁻¹) * a := by rw [h1]
  have hy : (a * (z * a * z⁻¹))⁻¹ * (z * (a * (z * a * z⁻¹)) * z⁻¹) ∈ O := by
    rw [hzn]
    have hc : ⁅a⁻¹, (z * a * z⁻¹)⁻¹⁆ ∈ pPrimeCoreOf 2 A₁ :=
      (h.cs₂ (A₂.inv_mem hbA₂)).2.2 a⁻¹ (A₁.inv_mem ha)
    have : (a * (z * a * z⁻¹))⁻¹ * ((z * a * z⁻¹) * a) = ⁅a⁻¹, (z * a * z⁻¹)⁻¹⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact O.inv_mem (h.Ohat₁ hc)
  obtain ⟨o, hoO, hzo⟩ := exists_centralized_in_coset h.Oodd h.z_sq h.Oz hy
  have hyK : a * (z * a * z⁻¹) * o ∈ A₁ ⊔ A₂ := mul_mem hnK (h.OK hoO)
  refine ⟨a * (z * a * z⁻¹) * o, hyK, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc a * (z * a * z⁻¹) * o * z = (z * (a * (z * a * z⁻¹) * o) * z⁻¹) * z := by rw [hzo]
      _ = z * (a * (z * a * z⁻¹) * o) := by group
  · rw [phi_mul A₁ (h.K_le_N₁ hnK) (h.K_le_N₁ (h.OK hoO))]
    have h1 : phi A₁ (a * (z * a * z⁻¹)) (h.K_le_N₁ hnK) = MulAut.conj (hatMk A₁ ⟨a, ha⟩) :=
      h.phi₁_prod ha hbA₂
    have h2 : phi A₁ o (h.K_le_N₁ (h.OK hoO)) = 1 := (phi_eq_one_iff A₁ _).2 (h.Ocs₁ hoO)
    rw [h1, h2, mul_one]

theorem ker_form {F₁ F₂ : Type} [Field F₁] [Field F₂] (e₁ : Hat A₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₁)
    (e₂ : Hat A₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F₂) {y : G} (hy : y ∈ A₁ ⊔ A₂)
    (hyz : z * y * z⁻¹ = y) (hy1 : y ∈ cSec A₁) : ∃ ε ∈ zpowers t, ∃ o ∈ O, y = ε * o := by
  have hy2 : y ∈ cSec A₂ := by
    have := h.cSec_swap hy1
    rwa [hyz] at this
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := h.decomp hy
  have h1 : MulAut.conj (hatMk A₁ ⟨a₁, ha₁⟩) = 1 := by
    rw [← h.phi₁_prod ha₁ ha₂]; exact (phi_eq_one_iff A₁ _).2 hy1
  have h2 : MulAut.conj (hatMk A₂ ⟨a₂, ha₂⟩) = 1 := by
    rw [← h.phi₂_prod ha₁ ha₂]; exact (phi_eq_one_iff A₂ _).2 hy2
  have htc₁ : ∀ x ∈ A₁, t * x = x * t := fun x hx => h.tcomm x (mem_sup_left hx)
  have htc₂ : ∀ x ∈ A₂, t * x = x * t := fun x hx => h.tcomm x (mem_sup_right hx)
  obtain ⟨ε₁, hε₁, o₁, ho₁, rfl⟩ := split_center e₁ h.tA₁ h.t_sq h.t_ne htc₁ ha₁ h1
  obtain ⟨ε₂, hε₂, o₂, ho₂, rfl⟩ := split_center e₂ h.tA₂ h.t_sq h.t_ne htc₂ ha₂ h2
  refine ⟨ε₁ * ε₂, mul_mem hε₁ hε₂, o₁ * o₂, mul_mem (h.Ohat₁ ho₁) (h.Ohat₂ ho₂), ?_⟩
  have hεo : o₁ * ε₂ = ε₂ * o₁ := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hε₂
    have ho₁K : o₁ ∈ A₁ ⊔ A₂ := h.OK (h.Ohat₁ ho₁)
    have : Commute t o₁ := h.tcomm o₁ ho₁K
    exact ((this.zpow_left k).symm).eq
  calc ε₁ * o₁ * (ε₂ * o₂) = ε₁ * (o₁ * ε₂) * o₂ := by group
    _ = ε₁ * (ε₂ * o₁) * o₂ := by rw [hεo]
    _ = ε₁ * ε₂ * (o₁ * o₂) := by group

end Diag31

omit [Finite G] in
theorem comm_le_of_central {c : G} {N L : Subgroup G} (hcN : ∀ n ∈ N, c * n = n * c)
    (hnorm : c ∈ normalizer (N : Set G)) (hLM : L ≤ zpowers c ⊔ N) : ⁅L, L⁆ ≤ N := by
  have hnorm' : zpowers c ≤ normalizer (N : Set G) := zpowers_le.2 hnorm
  have hsplit : ∀ a ∈ L, ∃ u ∈ zpowers c, ∃ n ∈ N, a = u * n := fun a ha =>
    A.mem_sup_of_le_normalizer hnorm' (hLM ha)
  have hcen : ∀ u ∈ zpowers c, ∀ x ∈ zpowers c ⊔ N, u * x = x * u := by
    intro u hu x hx
    have hle : zpowers c ⊔ N ≤ centralizer ({u} : Set G) := by
      refine sup_le ?_ ?_
      · intro w hw
        rw [Subgroup.mem_centralizer_singleton_iff]
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hw
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hu
        exact ((Commute.refl c).zpow_zpow i j).eq
      · intro n hn
        rw [Subgroup.mem_centralizer_singleton_iff]
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hu
        exact ((show Commute c n from hcN n hn).zpow_left j).eq.symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm
  rw [Subgroup.commutator_def]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  obtain ⟨u, hu, n, hn, rfl⟩ := hsplit a ha
  obtain ⟨v, hv, m, hm, rfl⟩ := hsplit b hb
  have hvm : v * m ∈ zpowers c ⊔ N := mul_mem_sup hv hm
  rw [comm_mul_left_central (hcen u hu n (mem_sup_right hn)) (hcen u hu _ hvm),
    comm_mul_right_central (hcen v hv n (mem_sup_right hn)) (hcen v hv m (mem_sup_right hm))]
  have : ⁅n, m⁆ = n * m * n⁻¹ * m⁻¹ := rfl
  show ⁅n, m⁆ ∈ N
  rw [this]
  exact N.mul_mem (N.mul_mem (N.mul_mem hn hm) (N.inv_mem hn)) (N.inv_mem hm)

omit [Finite G] in
theorem subgroupOf_perfect {I Y : Subgroup G} (hIY : I ≤ Y) (h : ⁅I, I⁆ = I) :
    ⁅I.subgroupOf Y, I.subgroupOf Y⁆ = I.subgroupOf Y := by
  apply Subgroup.map_injective Y.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hIY, h]

namespace Diag31

variable (h : Diag31 z t A₁ A₂ O)

include h

abbrev Yz (z : G) (A₁ A₂ : Subgroup G) : Subgroup G := (A₁ ⊔ A₂) ⊓ centralizer ({z} : Set G)

omit [Finite G] in
@[expose] noncomputable def psiHom : ↥(Yz z A₁ A₂) →* ↥(innOf (Hat A₁)) where
  toFun y := ⟨phi A₁ y (h.K_le_N₁ y.2.1), h.phi_mem_inn y.2.1⟩
  map_one' := by
    apply Subtype.ext
    show phi A₁ 1 (h.K_le_N₁ (one_mem _)) = 1
    ext x
    obtain ⟨k, rfl⟩ := hatMk_surjective A₁ x
    rw [phi_mk]
    simp
  map_mul' x y := Subtype.ext (phi_mul A₁ (h.K_le_N₁ x.2.1) (h.K_le_N₁ y.2.1))

omit [Finite G] in
theorem psiHom_apply (y : ↥(Yz z A₁ A₂)) :
    ((h.psiHom y : ↥(innOf (Hat A₁))) : MulAut (Hat A₁)) = phi A₁ y (h.K_le_N₁ y.2.1) := rfl

theorem psiHom_surjective : Function.Surjective h.psiHom := by
  rintro ⟨x, hx⟩
  obtain ⟨ā, rfl⟩ := hx
  obtain ⟨a, rfl⟩ := hatMk_surjective A₁ ā
  obtain ⟨y, hyK, hyC, hphi⟩ := h.exists_lift a.2
  refine ⟨⟨y, hyK, hyC⟩, Subtype.ext ?_⟩
  rw [psiHom_apply]
  exact hphi

theorem psiHom_ker {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (e₁ : Hat A₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₁)
    (e₂ : Hat A₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F₂) (y : ↥(Yz z A₁ A₂))
    (hy1 : h.psiHom y = 1) : ∃ ε ∈ zpowers t, ∃ o ∈ O, (y : G) = ε * o := by
  have hphi : phi A₁ y (h.K_le_N₁ y.2.1) = 1 := by
    rw [← h.psiHom_apply y, hy1]; rfl
  have hyz : z * (y : G) * z⁻¹ = y := by
    have := Subgroup.mem_centralizer_singleton_iff.1 y.2.2
    rw [← this]; group
  exact h.ker_form e₁ e₂ y.2.1 hyz ((phi_eq_one_iff A₁ (h.K_le_N₁ y.2.1)).1 hphi)

omit [Finite G] in
theorem t_normalizes_O : t ∈ normalizer (O : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hcomm : ∀ x ∈ O, t * x * t⁻¹ = x := by
    intro x hx
    have := h.tcomm x (h.OK hx)
    rw [this]; group
  constructor
  · intro hx; rw [hcomm x hx]; exact hx
  · intro hx
    have hxK : t * x * t⁻¹ ∈ A₁ ⊔ A₂ := h.OK hx
    have htK : t ∈ A₁ ⊔ A₂ := mem_sup_left h.tA₁
    have hx' : x ∈ A₁ ⊔ A₂ := by
      have : x = t⁻¹ * (t * x * t⁻¹) * t := by group
      rw [this]
      exact mul_mem (mul_mem (inv_mem htK) hxK) htK
    have := h.tcomm x hx'
    have e : t * x * t⁻¹ = x := by rw [this]; group
    rw [e] at hx; exact hx

theorem psi_image_ne_bot {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (e₁ : Hat A₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₁)
    (e₂ : Hat A₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F₂) {I : Subgroup G}
    (hIY : I ≤ Yz z A₁ A₂) (hIperf : ⁅I, I⁆ = I) (hIne : I ≠ ⊥) :
    (I.subgroupOf (Yz z A₁ A₂)).map h.psiHom ≠ ⊥ := by
  intro hbot
  have hIle : I ≤ zpowers t ⊔ O := by
    intro x hx
    have hxY : x ∈ Yz z A₁ A₂ := hIY hx
    have h1 : h.psiHom ⟨x, hxY⟩ = 1 := by
      have hmem : h.psiHom ⟨x, hxY⟩ ∈ (I.subgroupOf (Yz z A₁ A₂)).map h.psiHom :=
        Subgroup.mem_map_of_mem _ hx
      rw [hbot] at hmem
      exact hmem
    obtain ⟨ε, hε, o, ho, hxe⟩ := h.psiHom_ker e₁ e₂ ⟨x, hxY⟩ h1
    rw [show x = ε * o from hxe]
    exact mul_mem_sup hε ho
  have hIO : I ≤ O := by
    have := comm_le_of_central (c := t) (N := O) (L := I)
      (fun n hn => h.tcomm n (h.OK hn)) h.t_normalizes_O hIle
    rw [hIperf] at this
    exact this
  have hodd' : Odd (Nat.card ↥I) := Odd.of_dvd_nat h.Oodd (Subgroup.card_dvd_of_le hIO)
  have hsolv : Group.IsSolvable ↥I := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'
  have : Nontrivial ↥I := (Subgroup.nontrivial_iff_ne_bot I).2 hIne
  have : Group.IsPerfect ↥I := Subgroup.isPerfect_iff.2 hIperf
  exact Group.IsPerfect.not_isSolvable ↥I hsolv

theorem main {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] (hodd : Odd (Nat.card F₁))
    (e₁ : Hat A₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₁)
    (e₂ : Hat A₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F₂) {I : Subgroup G}
    (hIY : I ≤ Yz z A₁ A₂) (hIperf : ⁅I, I⁆ = I) (hIne : I ≠ ⊥)
    (hIsn : (I.subgroupOf (Yz z A₁ A₂)).IsSubnormal) {k : G} (hk : k ∈ Yz z A₁ A₂) :
    ∃ ε ∈ zpowers t, ∃ j ∈ I, ∃ o ∈ O, k = ε * j * o := by
  have hJ₀perf : ⁅(I.subgroupOf (Yz z A₁ A₂)).map h.psiHom, (I.subgroupOf (Yz z A₁ A₂)).map h.psiHom⁆ =
      (I.subgroupOf (Yz z A₁ A₂)).map h.psiHom := by
    rw [← Subgroup.map_commutator, subgroupOf_perfect hIY hIperf]
  have hJ₀sn : ((I.subgroupOf (Yz z A₁ A₂)).map h.psiHom).IsSubnormal :=
    hIsn.map h.psiHom_surjective
  have htop : (I.subgroupOf (Yz z A₁ A₂)).map h.psiHom = ⊤ :=
    inn_perfect_subnormal_eq_top hodd e₁ _ (h.psi_image_ne_bot e₁ e₂ hIY hIperf hIne) hJ₀perf hJ₀sn
  have hkJ : h.psiHom ⟨k, hk⟩ ∈ (I.subgroupOf (Yz z A₁ A₂)).map h.psiHom := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨j₀, hj₀, hjk⟩ := Subgroup.mem_map.1 hkJ
  have hj₀I : (j₀ : G) ∈ I := hj₀
  have h1 : h.psiHom (j₀⁻¹ * ⟨k, hk⟩) = 1 := by rw [map_mul, map_inv, hjk, inv_mul_cancel]
  obtain ⟨ε, hε, o, ho, hyeo⟩ := h.psiHom_ker e₁ e₂ _ h1
  refine ⟨ε, hε, j₀, hj₀I, o, ho, ?_⟩
  have hjK : (j₀ : G) ∈ A₁ ⊔ A₂ := j₀.2.1
  have hεj : ε * (j₀ : G) = (j₀ : G) * ε := by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hε
    exact (((show Commute t (j₀ : G) from h.tcomm _ hjK).zpow_left n).eq)
  have hk' : k = (j₀ : G) * (ε * o) := by
    have : ((j₀⁻¹ * ⟨k, hk⟩ : ↥(Yz z A₁ A₂)) : G) = (j₀ : G)⁻¹ * k := rfl
    rw [this] at hyeo
    calc k = (j₀ : G) * ((j₀ : G)⁻¹ * k) := by group
      _ = (j₀ : G) * (ε * o) := by rw [hyeo]
  calc k = (j₀ : G) * (ε * o) := hk'
    _ = (j₀ : G) * ε * o := by group
    _ = ε * (j₀ : G) * o := by rw [← hεj]

end Diag31

end Diag

end Hats

section Inst

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pLayerOf_le_self (X : Subgroup G) : pLayerOf 2 X ≤ X := sSup_le fun _ hL => hL.1

theorem ivk_3_1b_diag (hII : II4_4_4_center) (h327 : IG_3_27) (h41 : Prop4_1) : IVK_3_1b_diag := by
  intro G _ _ z S K₁ K₂ h q hq hq5 hK₁ hK₂ t₁ ht₁C ht₁o hconj hswap g hg k hk
  have hM := m4_of_std hII h
  have hz2 := h.orderOf_z
  have hzsq : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz2
  have ht₁sq : t₁ * t₁ = 1 := mul_self_eq_one_of_orderOf_eq_two ht₁o
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzsq
  have hint₁ : IsIntrinsic t₁ (conjugate K₁ g) := by
    have := isIntrinsic_cj hg (intrinsic_of_comp hM h (Or.inl rfl))
    rwa [cj_eq_conjugate] at this
  have hint₂ : IsIntrinsic t₁ (conjugate K₂ g) := by
    have := isIntrinsic_cj hg (intrinsic_of_comp hM h (Or.inr rfl))
    rwa [cj_eq_conjugate] at this
  have hA₁ := hint₁.1
  have hA₂ := hint₂.1
  have hAne : conjugate K₁ g ≠ conjugate K₂ g := fun he => h.ne (conjugate_inj he)
  have hcs₁ : conjugate K₁ g ≤ cSec (conjugate K₂ g) := le_cSec_of_ne hA₁ hA₂ hAne
  have hcs₂ : conjugate K₂ g ≤ cSec (conjugate K₁ g) := le_cSec_of_ne hA₂ hA₁ hAne.symm
  obtain ⟨hQ, -, hc⟩ := h41 G z S K₁ K₂ h
  have hzint := hc t₁ ht₁C hconj hswap g hg
  have hcz₁ : cmap z (conjugate K₁ g) = conjugate K₂ g := by
    have := hzint.1
    unfold conjugate at this ⊢
    rw [hzi] at this
    exact this
  have hcz₂ : cmap z (conjugate K₂ g) = conjugate K₁ g := by
    have := hzint.2
    unfold conjugate at this ⊢
    rw [hzi] at this
    exact this
  have hKz : cmap z (conjugate K₁ g ⊔ conjugate K₂ g) = conjugate K₁ g ⊔ conjugate K₂ g := by
    show (conjugate K₁ g ⊔ conjugate K₂ g).map (MulAut.conj z).toMonoidHom = _
    rw [Subgroup.map_sup]
    show cmap z (conjugate K₁ g) ⊔ cmap z (conjugate K₂ g) = _
    rw [hcz₁, hcz₂, sup_comm]
  have hK'N₁ : conjugate K₁ g ⊔ conjugate K₂ g ≤ normalizer (conjugate K₁ g : Set G) :=
    sup_le le_normalizer (fun x hx => (hcs₂ hx).1)
  have hoddO := TwoThin.card_pPrimeCoreOf_odd (conjugate K₁ g ⊔ conjugate K₂ g)
  have hD : Diag31 z t₁ (conjugate K₁ g) (conjugate K₂ g)
      (pPrimeCoreOf 2 (conjugate K₁ g ⊔ conjugate K₂ g)) :=
    { z_sq := hzsq
      t_sq := ht₁sq
      t_ne := ne_one_of_orderOf_eq_two ht₁o
      tA₁ := hint₁.2.2
      tA₂ := hint₂.2.2
      tcomm := fun x hx =>
        (Subgroup.mem_centralizer_singleton_iff.1 ((sup_le hA₁.1 hA₂.1 : conjugate K₁ g ⊔ conjugate K₂ g ≤
          centralizer ({t₁} : Set G)) hx)).symm
      cz₁ := hcz₁
      cs₁ := hcs₁
      cs₂ := hcs₂
      Oodd := hoddO
      OK := TwoThin.pPrimeCoreOf_le _
      Oz := by
        intro o ho
        have h1 := pPrimeCoreOf_cmap z (conjugate K₁ g ⊔ conjugate K₂ g)
        rw [hKz] at h1
        have h2 : z * o * z⁻¹ ∈ cmap z (pPrimeCoreOf 2 (conjugate K₁ g ⊔ conjugate K₂ g)) := by
          rw [mem_cmap]
          have : z⁻¹ * (z * o * z⁻¹) * z = o := by group
          rw [this]; exact ho
        rw [← h1] at h2
        exact h2
      Ocs₁ := by
        intro o ho
        have hoK : o ∈ conjugate K₁ g ⊔ conjugate K₂ g := TwoThin.pPrimeCoreOf_le _ ho
        have hoN : o ∈ normalizer (conjugate K₁ g : Set G) := hK'N₁ hoK
        refine ⟨hoN, TwoThin.mem_normalizer_pPrimeCoreOf hoN, fun k hk => ?_⟩
        have hkK : k ∈ conjugate K₁ g ⊔ conjugate K₂ g := mem_sup_left hk
        have h1 : ⁅k, o⁆ ∈ pPrimeCoreOf 2 (conjugate K₁ g ⊔ conjugate K₂ g) := by
          have : ⁅k, o⁆ = (k * o * k⁻¹) * o⁻¹ := rfl
          rw [this]
          exact mul_mem (TwoThin.pPrimeCoreOf_normalized _ hkK ho) (inv_mem ho)
        have h2 : ⁅k, o⁆ ∈ conjugate K₁ g := by
          have : ⁅k, o⁆ = k * (o * k⁻¹ * o⁻¹) := by simp [commutatorElement_def, mul_assoc]
          rw [this]
          exact mul_mem hk ((Subgroup.mem_normalizer_iff.1 hoN k⁻¹).1 (inv_mem hk))
        have hNle : conjugate K₁ g ⊓ pPrimeCoreOf 2 (conjugate K₁ g ⊔ conjugate K₂ g) ≤
            pPrimeCoreOf 2 (conjugate K₁ g) :=
          le_pPrimeCoreOf' inf_le_left
            (fun x hx n hn => ⟨(conjugate K₁ g).mul_mem ((conjugate K₁ g).mul_mem hx hn.1)
              ((conjugate K₁ g).inv_mem hx), TwoThin.pPrimeCoreOf_normalized _ (mem_sup_left hx) hn.2⟩)
            (Odd.of_dvd_nat hoddO (Subgroup.card_dvd_of_le inf_le_right))
        exact hNle ⟨h2, h1⟩
      Ohat₁ := by
        have hN : ((conjugate K₁ g).subgroupOf (conjugate K₁ g ⊔ conjugate K₂ g)).Normal := by
          rw [sup_comm]
          exact Subgroup.normal_subgroupOf_sup_of_le_normalizer (fun x hx => (hcs₂ hx).1)
        exact pPrimeCoreOf_le_of_normal 2 le_sup_left hN
      Ohat₂ := by
        have hN : ((conjugate K₂ g).subgroupOf (conjugate K₁ g ⊔ conjugate K₂ g)).Normal :=
          Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := conjugate K₁ g) (N := conjugate K₂ g)
            (fun x hx => (hcs₁ hx).1)
        exact pPrimeCoreOf_le_of_normal 2 le_sup_right hN }
  obtain ⟨F₁, _, _, hF₁q, ⟨e₁₀⟩⟩ := hK₁
  obtain ⟨F₂, _, _, hF₂q, ⟨e₂₀⟩⟩ := hK₂
  obtain ⟨c₁⟩ := nonempty_quot_cmap g⁻¹ K₁
  obtain ⟨c₂⟩ := nonempty_quot_cmap g⁻¹ K₂
  let e₁ : Hat (conjugate K₁ g) ≃* Matrix.SpecialLinearGroup (Fin 2) F₁ :=
    (c₁.trans e₁₀).trans (specialLinearGroupEquivStatedSL 2 F₁).symm
  let e₂ : Hat (conjugate K₂ g) ≃* Matrix.SpecialLinearGroup (Fin 2) F₂ :=
    (c₂.trans e₂₀).trans (specialLinearGroupEquivStatedSL 2 F₂).symm
  have hodd₁ : Odd (Nat.card F₁) := by rw [hF₁q]; exact hq
  have hcomm : Commute t₁ z := Subgroup.mem_centralizer_singleton_iff.1 ht₁C
  have hzn : z ∉ normalizer (conjugate K₁ g : Set G) := by
    intro hzn
    have h1 : conjugate (conjugate K₁ g) z = conjugate K₁ g := by
      rw [← cj_eq_conjugate]; exact M.cj_eq_iff_normalizer.2 hzn
    exact h.ne (conjugate_inj (h1.symm.trans hzint.1))
  obtain ⟨hI, -⟩ := h327 G h.simple t₁ z ht₁o hz2 hcomm (conjugate K₁ g) hint₁ hzn
  obtain ⟨hIY', hI2⟩ := TwoThin.isPCompIn_two_iff.1 hI
  have hIperf : ⁅IDiag z (conjugate K₁ g), IDiag z (conjugate K₁ g)⁆ = IDiag z (conjugate K₁ g) :=
    TwoThin.commutator_self_of_isTwoComponent hIY' hI2
  have hIne : IDiag z (conjugate K₁ g) ≠ ⊥ := TwoThin.ne_bot_of_isTwoComponent hI2
  have hIY : IDiag z (conjugate K₁ g) ≤ Diag31.Yz z (conjugate K₁ g) (conjugate K₂ g) := by
    unfold IDiag
    rw [hzint.1]
    exact (pLayerOf_le_self _).trans (le_of_eq (inf_comm _ _))
  have hYY' : Diag31.Yz z (conjugate K₁ g) (conjugate K₂ g) ≤
      centralizer ({t₁} : Set G) ⊓ centralizer ({z} : Set G) := fun x hx =>
    ⟨Subgroup.mem_centralizer_singleton_iff.2 (hD.tcomm x hx.1).symm, hx.2⟩
  have hIsn : ((IDiag z (conjugate K₁ g)).subgroupOf (Diag31.Yz z (conjugate K₁ g) (conjugate K₂ g))).IsSubnormal := by
    obtain ⟨-, -, hsub, -, -⟩ := hI.2
    have := hsub.comap (Subgroup.inclusion hYY')
    convert this using 1
    ext x
    simp [Subgroup.mem_subgroupOf]
  have hcsup : conjugate (K₁ ⊔ K₂) g = conjugate K₁ g ⊔ conjugate K₂ g := Subgroup.map_sup _ _ _
  rw [hcsup] at hk ⊢
  exact hD.main hodd₁ e₁ e₂ hIY hIperf hIne hIsn hk

theorem l77_no_conj_final (hII : II4_4_4_center) (h73 : Lemma7_3) (h327 : IG_3_27) (h41 : Prop4_1)
    (hF : FStar_C) : L77_no_conj :=
  l77_no_conj_of_closed hII h73 h327 h41 hF (ivk_3_1b_diag hII h327 h41)

end Inst

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.Leaf
