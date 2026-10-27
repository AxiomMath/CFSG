module

public import CFSG.LieType.Ree.SmallReeInvolutionComponents
public import CFSG.LieType.Ree.SuzukiReeOuterTwoPart
public import CFSG.GH74.GLS.C3.Layer1.Th2Conn
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvCent

public noncomputable section

namespace CFSG.GH74.GLS.IVK.GHInv

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Walter.Ree.Model
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.CatalogueBSmallRee CFSG.LieType.Ree
  CFSG.LieType.Ree.SuzukiReeOuterTwoPart Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem card_inf_centralizer_smallRee
    (a : ℕ) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1))
    {t : ModGL ReeTag.G2.tag K} (ht : t ∈ ReeTag.G2.reeGamma K a) (ht2 : orderOf t = 2) :
    Nat.card ↥(ReeTag.G2.reeGamma K a ⊓ Subgroup.centralizer {t}) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  set Γ := ReeTag.G2.reeGamma K a with hΓ
  set h := smallReeH a K (-1) with hh
  obtain ⟨g, hgΓ, hgt⟩ :=
    (small_Ree_prime_field_involution_fusion a K hK w₀ hw₀).2.2.2.2.2 t ht ht2
  set C := smallReeInvCentralizer a K with hCdef
  have hCmap : (Γ ⊓ Subgroup.centralizer {t}).map (MulAut.conj g).toMonoidHom = C := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective,
      CFSG.LocalAnalysis.ComponentInitial.map_conj_eq_of_mem_normalizer
        (Subgroup.le_normalizer hgΓ), map_centralizer_singleton,
      MulAut.conj_apply, hgt]
    rfl
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,
    hCmap]
  have hh2 : orderOf h = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g) t
    rw [MulAut.conj_apply, hgt, ht2] at this
    exact this
  obtain ⟨ψ, hψC, -, -, -, hψone, -, ⟨hsup, hdisj, hcent⟩, e, -⟩ :=
    small_Ree_involution_centralizer_PSL2_structure a K hK w₀ hw₀
  rw [← hh, ← hCdef] at hsup
  rw [← hh] at hcent
  have hcd : CFSG.GH74.GLS.Th2.CommDisj (Subgroup.zpowers h) ψ.range :=
    ⟨fun p hp q hq => ((Subgroup.mem_centralizer_iff.1 (hcent hp)) q hq).symm,
      disjoint_iff.1 hdisj⟩
  have hC : Nat.card C = Nat.card (Subgroup.zpowers h) * Nat.card ψ.range := by
    rw [← hsup]
    exact hcd.card_sup le_rfl le_rfl
  have hneg : (-1 : CFSG.LieType.Chevalley.SL2 K) ≠ 1 := by
    intro hc
    have h2 := congrArg (fun A : CFSG.LieType.Chevalley.SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) hc
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h2
    have h3 : (2 : K) = 0 := by linear_combination -h2
    have : ringChar K = 3 := ringChar.eq K 3
    exact absurd (CharP.cast_eq_zero_iff K 3 2 |>.1 (by exact_mod_cast h3)) (by norm_num)
  have hker : Nat.card ψ.ker = 2 := by
    have hset : (ψ.ker : Set (CFSG.LieType.Chevalley.SL2 K)) = {1, -1} := by
      ext x
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff,
        Set.mem_singleton_iff, hψone]
    show Nat.card (ψ.ker : Set (CFSG.LieType.Chevalley.SL2 K)) = 2
    rw [Nat.card_coe_set_eq, hset, Set.ncard_pair hneg.symm]
  have h3 := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker, hker, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K] at h3
  rw [hC, Nat.card_zpowers, hh2]
  exact h3

theorem ordProj_two_card_inf_centralizer_smallRee
    (a : ℕ) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1))
    {t : ModGL ReeTag.G2.tag K} (ht : t ∈ ReeTag.G2.reeGamma K a) (ht2 : orderOf t = 2) :
    ordProj[2] (Nat.card ↥(ReeTag.G2.reeGamma K a ⊓ Subgroup.centralizer {t})) = 8 := by
  rw [card_inf_centralizer_smallRee a K hK ht ht2, hK]
  have hq0 : 3 ^ (2 * a + 1) * ((3 ^ (2 * a + 1)) ^ 2 - 1) / 2 ≠ 0 := by
    have h4 := ordProj_two_small_Ree_PSL2 a
    intro h0
    rw [h0] at h4
    simp at h4
  have hev : 2 ∣ 3 ^ (2 * a + 1) * ((3 ^ (2 * a + 1)) ^ 2 - 1) := by
    have hq : Odd (3 ^ (2 * a + 1)) := Odd.pow (by decide)
    have h1 : 2 ∣ (3 ^ (2 * a + 1)) ^ 2 - 1 := by
      have h2 : Odd ((3 ^ (2 * a + 1)) ^ 2) := hq.pow
      have h3 : 1 ≤ (3 ^ (2 * a + 1)) ^ 2 := Nat.one_le_iff_ne_zero.2 (by positivity)
      obtain ⟨m, hm⟩ := h2
      exact ⟨m, by omega⟩
    exact Dvd.dvd.mul_left h1 _
  have hmul : 3 ^ (2 * a + 1) * ((3 ^ (2 * a + 1)) ^ 2 - 1) =
      2 * (3 ^ (2 * a + 1) * ((3 ^ (2 * a + 1)) ^ 2 - 1) / 2) := by
    rw [Nat.mul_div_cancel' hev]
  rw [hmul, CFSG.LieType.Chevalley.ordProj_two_two_mul hq0, ordProj_two_small_Ree_PSL2 a]


theorem mul_comm_of_sq_eq_one {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * (a * b) = 1) : a * b = b * a := by
  have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have h2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab
  rw [mul_inv_rev, h1, h2] at h3
  exact h3.symm

theorem exists_card_eq_two_pow_of_sq_eq_one' {X : Type*} [Group X] [Finite X] (E : Subgroup X)
    (hE : ∀ e ∈ E, e * e = 1) : ∃ d : ℕ, Nat.card E = 2 ^ d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 E := fun g => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (hE g g.2)⟩
  exact (IsPGroup.iff_card).1 hp

theorem ree_model_data
    {T : Type} [Group T] {f : ℕ} (h : ReeTitsModel T .twistedG2 3 f) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.G2.prime),
      Nat.card K = 3 ^ (2 * a + 1) ∧ Nonempty (T ≃* ↥(ReeTag.G2.reeGamma K a)) := by
  obtain ⟨-, -, -, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier T 3 f h
  obtain ⟨-, a', hfa', K, _, _, hK, hw⟩ := h
  have ha' : a' = a := by omega
  subst ha'
  have : CharP K ReeTag.G2.prime :=
    finite_field_prime_power_characteristic Nat.prime_three (by omega) hK
  obtain ⟨E⟩ := hiso a' K hfa hK hw
  exact ⟨a', K, inferInstance, inferInstance, this, by rw [hK, hfa], ⟨E⟩⟩

theorem ordProj_two_card_centralizer_ree
    {T : Type} [Group T] {f : ℕ} (h : ReeTitsModel T .twistedG2 3 f) {t : T} (ht : orderOf t = 2) :
    ordProj[2] (Nat.card ↥(Subgroup.centralizer ({t} : Set T))) = 8 := by
  obtain ⟨a, K, _, _, _, hK, ⟨e⟩⟩ := ree_model_data h
  rw [card_centralizer_eq_of_mulEquiv e t]
  have h1 := card_centralizer_subtype (ReeTag.G2.reeGamma K a) (e t)
  rw [h1]
  have hord : orderOf ((e t : ↥(ReeTag.G2.reeGamma K a)) : ModGL ReeTag.G2.tag K) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact ht
  exact ordProj_two_card_inf_centralizer_smallRee a K hK (e t).2 hord

theorem ree_card_elementary_le
    {T : Type} [Group T] [Finite T] {f : ℕ} (h : ReeTitsModel T .twistedG2 3 f) (E : Subgroup T)
    (hE : ∀ e ∈ E, e * e = 1) : Nat.card E ≤ 2 ^ 3 := by
  by_cases hE1 : ∀ e ∈ E, e = 1
  · have : Nat.card E = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((hE1 a a.2).trans (hE1 b b.2).symm)⟩, ⟨1⟩⟩
    rw [this]
    norm_num
  · push Not at hE1
    obtain ⟨t, htE, ht1⟩ := hE1
    have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact hE t htE) ht1
    have hle : E ≤ Subgroup.centralizer ({t} : Set T) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact mul_comm_of_sq_eq_one (hE x hx) (hE t htE) (hE _ (E.mul_mem hx htE))
    obtain ⟨d, hd⟩ := exists_card_eq_two_pow_of_sq_eq_one' E hE
    have hdvd : 2 ^ d ∣ Nat.card ↥(Subgroup.centralizer ({t} : Set T)) := by
      rw [← hd]
      exact Subgroup.card_dvd_of_le hle
    have hne : Nat.card ↥(Subgroup.centralizer ({t} : Set T)) ≠ 0 := Nat.card_pos.ne'
    have h8 := (Nat.prime_two.pow_dvd_iff_dvd_ordProj hne).1 hdvd
    rw [ordProj_two_card_centralizer_ree h ht2] at h8
    rw [hd]
    exact Nat.le_of_dvd (by norm_num) h8

theorem ree_card_outer_elementary
    {T : Type} [Group T] [Finite T] {f : ℕ} (h : ReeTitsModel T .twistedG2 3 f)
    (E : Subgroup (Outer T)) (hE : ∀ e ∈ E, e * e = 1) : Nat.card E ≤ 2 ^ 0 := by
  have ho := (small_Ree_case h).1
  obtain ⟨d, hd⟩ := exists_card_eq_two_pow_of_sq_eq_one' E hE
  have hne : Nat.card (Outer T) ≠ 0 := Nat.card_pos.ne'
  have hdvd : 2 ^ d ∣ Nat.card (Outer T) := by
    rw [← hd]
    exact Subgroup.card_subgroup_dvd_card E
  have h1 := (Nat.prime_two.pow_dvd_iff_dvd_ordProj hne).1 hdvd
  rw [ho] at h1
  have := Nat.le_of_dvd one_pos h1
  rw [hd]
  simpa using this

end CFSG.GH74.GLS.IVK.GHInv
