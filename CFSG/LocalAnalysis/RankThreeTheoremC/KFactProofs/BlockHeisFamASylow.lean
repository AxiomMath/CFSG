module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisKer
public import CFSG.GroupTheory.WeirSylow.GL
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.Open.StatedAPI CFSG.GroupTheory.WeirSylow Matrix

@[expose] def HeisSylGood (p : ℕ) (A : Prop) (T : Type*) [Group T] : Prop :=
  (∀ a b : T, a * b = b * a) ∧ (A → ∀ x : T, x ^ p = 1 → ∃ y : T, y ^ p = x)

theorem HeisSylGood.of_mulEquiv {p : ℕ} {A : Prop} {T T' : Type*} [Group T] [Group T']
    (e : T ≃* T') (h : HeisSylGood p A T) : HeisSylGood p A T' := by
  refine ⟨fun a b => ?_, fun hA x hx => ?_⟩
  · apply e.symm.injective
    rw [map_mul, map_mul]
    exact h.1 _ _
  · obtain ⟨y, hy⟩ := h.2 hA (e.symm x) (by rw [← map_pow, hx, map_one])
    exact ⟨e y, by rw [← map_pow, hy, MulEquiv.apply_symm_apply]⟩

theorem HeisSylGood.mem {p : ℕ} {A : Prop} {X : Type*} [Group X] {S : Subgroup X}
    (h : HeisSylGood p A S) :
    (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) ∧ (A → ∀ x ∈ S, x ^ p = 1 → ∃ y ∈ S, y ^ p = x) := by
  refine ⟨fun x hx y hy => congrArg Subtype.val (h.1 ⟨x, hx⟩ ⟨y, hy⟩), fun hA x hx hxp => ?_⟩
  obtain ⟨y, hy⟩ := h.2 hA ⟨x, hx⟩ (Subtype.ext hxp)
  exact ⟨y, y.2, congrArg Subtype.val hy⟩

theorem heisSylGood_of_mem {p : ℕ} {A : Prop} {X : Type*} [Group X] {S : Subgroup X}
    (h1 : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (h2 : A → ∀ x ∈ S, x ^ p = 1 → ∃ y ∈ S, y ^ p = x) : HeisSylGood p A S := by
  refine ⟨fun a b => Subtype.ext (h1 a a.2 b b.2), fun hA x hx => ?_⟩
  obtain ⟨y, hyS, hy⟩ := h2 hA x x.2 (congrArg Subtype.val hx)
  exact ⟨⟨y, hyS⟩, Subtype.ext hy⟩

theorem heisSylGood_homC {p a r : ℕ} (hp : p.Prime) : HeisSylGood p (2 ≤ a) (HomC p a r) :=
  ⟨fun x y => mul_comm x y, fun ha x hx => homC_pth_power hp ha x hx⟩

theorem heisSylGood_sylow_of_shape {p : ℕ} {A : Prop} {G M : Type*} [Group G] [Group M]
    (hM : HeisSylGood p A M) (h : ∀ S : Sylow p G, Nonempty (↥S ≃* M)) :
    ∀ S : Sylow p G, HeisSylGood p A S := fun S => by
  obtain ⟨e⟩ := h S
  exact hM.of_mulEquiv e.symm

theorem heisSylGood_sylow_of_mulEquiv {p : ℕ} [Fact p.Prime] {A : Prop} {G H : Type*} [Group G]
    [Group H] [Finite H] (e : G ≃* H) (h : ∀ S : Sylow p H, HeisSylGood p A S) :
    ∀ S : Sylow p G, HeisSylGood p A S := fun S => by
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow p H))
  obtain ⟨φ⟩ := nonempty_sylow_mulEquiv_sylow_of_mulEquiv e T S
  exact (h T).of_mulEquiv φ

section Linear

variable {K : Type} [Field K] [Finite K]

theorem heisFamA_index_statedSL_dvd (n : ℕ) : (StatedSL n K).index ∣ Nat.card K - 1 := by
  rw [statedSL_eq_ker_det, Subgroup.index_ker, ← Nat.card_units]
  exact Subgroup.card_subgroup_dvd_card _

theorem heisFamA_factorization_statedSL {n p : ℕ} (h : ¬ p ∣ Nat.card K - 1) :
    (Nat.card (StatedSL n K)).factorization p = (Nat.card (GL (Fin n) K)).factorization p := by
  have h1 := (StatedSL n K).card_mul_index
  have hidx : ¬ p ∣ (StatedSL n K).index := fun hd => h (hd.trans (heisFamA_index_statedSL_dvd n))
  have hG : Nat.card (GL (Fin n) K) ≠ 0 := Nat.card_pos.ne'
  rw [← h1] at hG ⊢
  obtain ⟨ha, hb⟩ := mul_ne_zero_iff.1 hG
  rw [Nat.factorization_mul ha hb, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hidx,
    add_zero]

theorem heisFamA_not_dvd_card_scalars {n p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.gcd n (Nat.card K - 1)) :
    ¬ p ∣ Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) := by
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hxS : ((x : StatedSL n K) : GL (Fin n) K) ∈ StatedScalars (Fin n) K :=
    Subgroup.mem_subgroupOf.1 x.2
  obtain ⟨c, hc⟩ : ∃ c : Kˣ,
      GeneralLinearGroup.scalar (Fin n) c = ((x : StatedSL n K) : GL (Fin n) K) := hxS
  have hg : orderOf ((x : StatedSL n K) : GL (Fin n) K) = p := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  have hdet : (((x : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 :=
    det_of_mem_statedSL (x : StatedSL n K).2
  have hcn : c ^ n = 1 := by
    apply Units.ext
    rw [← hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    rw [Units.val_pow_eq_pow_val, hdet, Units.val_one]
  have h1 : p ∣ n := by
    rw [← hg]
    apply orderOf_dvd_of_pow_eq_one
    rw [← hc, ← map_pow, hcn, map_one]
  have h2 : p ∣ Nat.card K - 1 := by
    rw [← hg, ← Nat.card_units]
    apply orderOf_dvd_of_pow_eq_one
    rw [← hc, ← map_pow, pow_card_eq_one', map_one]
  exact h (Nat.dvd_gcd h1 h2)

theorem heisFamA_not_dvd_card_ker_mk {n p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.gcd n (Nat.card K - 1)) :
    ¬ p ∣ Nat.card
      (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))).ker := by
  rw [QuotientGroup.ker_mk']
  exact heisFamA_not_dvd_card_scalars hp h

theorem heisFamA_orderOf_eq_one {p : ℕ} (h : p ∣ Nat.card K - 1) :
    orderOf (Nat.card K : ZMod p) = 1 := by
  rw [orderOf_eq_one_iff]
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have : ((Nat.card K - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
  rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at this
  exact this

theorem heisFamA_sylow_GL {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K)
    (hlt : n / orderOf (Nat.card K : ZMod p) < p) :
    ∀ P : Sylow p (GL (Fin n) K), Nonempty (↥P ≃* HomC p
      (padicValNat p (Nat.card K ^ orderOf (Nat.card K : ZMod p) - 1))
      (n / orderOf (Nat.card K : ZMod p))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Nat.card K := Nat.card_eq_fintype_card.symm
  have hpK' : ¬ p ∣ Fintype.card K := by rwa [hc]
  have h := fun P => sylow_GL (hp.odd_of_ne_two hp2) K hpK' n P
  rw [hc] at h
  exact sylow_equiv_homC_of_sigmaModel hp hlt h

end Linear

section Projective

variable {K : Type} [Field K] [Finite K]

theorem heisFamA_sylow_psl_of_ne_one {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : ¬ p ∣ Nat.card K) (he : orderOf (Nat.card K : ZMod p) ≠ 1)
    (hgcd : ¬ p ∣ Nat.gcd n (Nat.card K - 1))
    (hlt : n / orderOf (Nat.card K : ZMod p) < p) :
    ∀ S : Sylow p (StatedProj (StatedSL n K)),
      HeisSylGood p (2 ≤ padicValNat p (Nat.card K ^ orderOf (Nat.card K : ZMod p) - 1)) S := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq1 : ¬ p ∣ Nat.card K - 1 := fun hd => he (heisFamA_orderOf_eq_one hd)
  have hSL := sylowShape_of_injective (StatedSL n K).subtype (StatedSL n K).subtype_injective
    (heisFamA_factorization_statedSL hq1) (heisFamA_sylow_GL hp hp2 hpK hlt)
  exact heisSylGood_sylow_of_shape (heisSylGood_homC hp)
    (sylowShape_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      (heisFamA_not_dvd_card_ker_mk hp hgcd) hSL)

theorem heisFamA_sylow_psl_of_ker {n p : ℕ} (hp : p.Prime) {A : Prop}
    (hgcd : ¬ p ∣ Nat.gcd n (Nat.card K - 1))
    (hker : ∀ T : Sylow p (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker,
      HeisSylGood p A T) :
    ∀ S : Sylow p (StatedProj (StatedSL n K)), HeisSylGood p A S := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hSL : ∀ S : Sylow p (StatedSL n K), HeisSylGood p A S :=
    heisSylGood_sylow_of_mulEquiv (MulEquiv.subgroupCongr (statedSL_eq_ker_det n K)) hker
  obtain ⟨T₁⟩ := (inferInstance : Nonempty (Sylow p (StatedSL n K)))
  exact heisSylGood_sylow_of_shape (hSL T₁)
    (sylowShape_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      (heisFamA_not_dvd_card_ker_mk hp hgcd) fun P => ⟨Sylow.equiv P T₁⟩)

theorem heisFamA_sylow_psl_of_eq_one {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : ¬ p ∣ Nat.card K) (he : orderOf (Nat.card K : ZMod p) = 1) (hn : 1 ≤ n)
    (hgcd : ¬ p ∣ Nat.gcd n (Nat.card K - 1))
    (hlt : n / orderOf (Nat.card K : ZMod p) < p) :
    ∀ S : Sylow p (StatedProj (StatedSL n K)),
      HeisSylGood p (2 ≤ padicValNat p (Nat.card K ^ orderOf (Nat.card K : ZMod p) - 1)) S := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hGL := heisFamA_sylow_GL hp hp2 hpK hlt
  rw [he, Nat.div_one, pow_one] at hGL
  rw [he, pow_one]
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq1 : p ∣ Nat.card K - 1 := by
    have h1 : (Nat.card K : ZMod p) ^ 1 = 1 := by rw [← he]; exact pow_orderOf_eq_one _
    rw [pow_one] at h1
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (by omega), h1, Nat.cast_one, sub_self]
  have ha : 1 ≤ padicValNat p (Nat.card K - 1) := one_le_padicValNat_of_dvd (by omega) hq1
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let δ : GL (Fin n) K →* Kˣ := GeneralLinearGroup.det
  have hrange : (Nat.card δ.range).factorization p = padicValNat p (Nat.card K - 1) := by
    rw [MonoidHom.range_eq_top.mpr GeneralLinearGroup.det_surjective, Subgroup.card_top,
      Nat.card_units, Nat.factorization_def _ hp]
  have hdata := heis_sylow_ker_data p ha hGL δ inferInstance hrange
  exact heisFamA_sylow_psl_of_ker hp hgcd fun T =>
    heisSylGood_of_mem (hdata T).1 (hdata T).2.2

theorem heisFamA_sylow_psl {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K)
    (hn : 1 ≤ n) (hgcd : ¬ p ∣ Nat.gcd n (Nat.card K - 1))
    (hlt : n / orderOf (Nat.card K : ZMod p) < p) :
    ∀ S : Sylow p (StatedProj (StatedSL n K)),
      HeisSylGood p (2 ≤ padicValNat p (Nat.card K ^ orderOf (Nat.card K : ZMod p) - 1)) S := by
  by_cases he : orderOf (Nat.card K : ZMod p) = 1
  · exact heisFamA_sylow_psl_of_eq_one hp hp2 hpK he hn hgcd hlt
  · exact heisFamA_sylow_psl_of_ne_one hp hp2 hpK he hgcd hlt

end Projective

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
