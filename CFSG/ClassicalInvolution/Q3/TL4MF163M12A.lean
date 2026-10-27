module

public import CFSG.ClassicalInvolution.Q3.TL4MF163M12
public import CFSG.ClassicalInvolution.Q3.TL4MF163L2
public import CFSG.ClassicalInvolution.Q3.TA3SmallCriteria
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint CFSG.Sporadic.Schreier
open CFSG.Sporadic.Mathieu CFSG.ComponentClassification.M12Cover

namespace MF163

variable {X : Type} [Group X]

theorem tightOddCent_of_equiv {Y : Type} [Group Y] (e : X ≃* Y) (z : X)
    (h : CFSG.oddCore (Subgroup.centralizer ({e z} : Set Y)) = ⊥) : TightOddCent z := by
  have h1 := CFSG.ComponentClassification.OddCore.equiv_invariant (centralizerEquiv e z)
  have h2 : CFSG.oddCore (Subgroup.centralizer ({z} : Set X)) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (f := (centralizerEquiv e z).toMonoidHom) _
      (centralizerEquiv e z).injective).1 (h1.trans h)
  show (CFSG.oddCore _).map (Subgroup.centralizer ({z} : Set X)).subtype = ⊥
  rw [h2, Subgroup.map_bot]

theorem acts3_of_equiv
    [Finite X]
    {R : Subgroup X} {S : Sylow 2 R} {z : X} (hm : EdgelessMember3 R S z)
    (e : X ≃* NativeSporadic.M12) : TightActs3 R z := by
  obtain ⟨ι, hι, hιK, hιz⟩ := exists_quat_of_member hm
  have hO := tightOddCent_of_equiv e z
    (m12_inner_oddCore (e z) (by rw [MulEquiv.orderOf_eq]; exact hm.datum.order))
  have hR := hm.datum.oddCoreImg_eq_bot hO
  obtain ⟨m, hmz, hm3, q, hq⟩ :=
    exists_three_not_comm (e.toMonoidHom.comp ι) (e.injective.comp hι)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hιz] at hmz hq
  refine ⟨e.symm m, 1, ?_, ?_, ι q, tightCore_le R (hιK q), ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hmz
  · show e.symm m ^ 3 = 1
    rw [← map_pow, ← hm3, pow_orderOf_eq_one, map_one]
  · rw [hR, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    intro h
    apply hq
    have h1 := congrArg e h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1

theorem exists_four_mem_of_index_two {N : Subgroup X} (hN : N.index = 2)
    (ι : QuaternionGroup 2 →* X) : ∃ q : QuaternionGroup 2, orderOf q = 4 ∧ ι q ∈ N := by
  by_cases h1 : ι (QuaternionGroup.a 1) ∈ N
  · exact ⟨_, QuaternionGroup.orderOf_a_one.trans (by norm_num), h1⟩
  by_cases h2 : ι (QuaternionGroup.xa 0) ∈ N
  · exact ⟨_, QuaternionGroup.orderOf_xa 0, h2⟩
  refine ⟨QuaternionGroup.a 1 * QuaternionGroup.xa 0, ?_, ?_⟩
  · rw [QuaternionGroup.a_mul_xa]
    exact QuaternionGroup.orderOf_xa _
  · rw [map_mul]
    exact (Subgroup.mul_mem_iff_of_index_two hN).2 (iff_of_false h1 h2)

theorem false_of_index_two [Finite X] {R : Subgroup X} {S : Sylow 2 R} {z : X}
    (hm : EdgelessMember3 R S z) (hF : FourClassesLarge (Subgroup.centralizer ({z} : Set X)))
    (hO : TightOddCent z) {N : Subgroup X} (hNn : N.Normal) (hN2 : N.index = 2)
    (hSN : ¬ (S : Subgroup R).map R.subtype ≤ N) : False := by
  have hd := hm.datum
  obtain ⟨eQ⟩ := hm.cls.1
  have hS : (S : Subgroup R) = ⊤ :=
    (S.is_maximal' ((hd.isPGroup_of_oddCent hO).to_subgroup ⊤) le_top).symm
  have hcard : Nat.card R = 8 := by
    rw [← Subgroup.card_top (G := R), ← hS, Nat.card_congr eQ.toEquiv]
    simp [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hRN : ¬ R ≤ N := fun h => hSN ((Subgroup.map_subtype_le _).trans h)
  let ι : QuaternionGroup 2 →* X :=
    R.subtype.comp ((S : Subgroup R).subtype.comp eQ.symm.toMonoidHom)
  have hι : Function.Injective ι := fun g h hgh =>
    eQ.symm.injective (Subtype.ext (Subtype.ext hgh))
  obtain ⟨q, hq4, hqN⟩ := exists_four_mem_of_index_two hN2 ι
  have hle : R ⊓ N ≤ Subgroup.centralizer ({z} : Set X) := inf_le_left.trans hd.cent
  have hN' : ((R ⊓ N).subgroupOf (Subgroup.centralizer ({z} : Set X))).Normal := by
    refine ⟨fun n hn c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnR, hnN⟩ := Subgroup.mem_inf.1 hn
    refine Subgroup.mem_inf.2 ⟨?_, hNn.conj_mem _ hnN _⟩
    exact (Subgroup.mem_normalizer_iff.1 (hd.le_normalizer c.2) _).1 hnR
  have hRN4 : Nat.card ↥(R ⊓ N) ≤ 4 := by
    have hdvd : Nat.card ↥(R ⊓ N) ∣ 8 := hcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have hne : Nat.card ↥(R ⊓ N) ≠ 8 := fun h => hRN fun r hr => by
      rw [← Subgroup.eq_of_le_of_card_ge (inf_le_left : R ⊓ N ≤ R) (by rw [h, hcard])] at hr
      exact hr.2
    have h8 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card ↥(R ⊓ N) = d at hdvd hne h8 ⊢
    interval_cases d <;> omega
  have hq2 : q ^ 2 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [hq4] at this
    norm_num at this
  let t₀ : ↥(R ⊓ N) := ⟨ι q, Subgroup.mem_inf.2 ⟨(eQ.symm q : (S : Subgroup R)).1.2, hqN⟩⟩
  have ht4 : t₀ ^ 4 = 1 := Subtype.ext (by
    show ι q ^ 4 = 1
    rw [← map_pow, ← hq4, pow_orderOf_eq_one, map_one])
  have ht2 : t₀ ^ 2 ≠ 1 := fun h => hq2 (hι (by
    have h' : ι q ^ 2 = 1 := congrArg Subtype.val h
    rw [map_pow, h', map_one]))
  exact (isEmpty_of_fourClassesLarge hF _ t₀ ht4 ht2
    ((Finite.card_subtype_le _).trans hRN4)).false (Subgroup.subgroupOfEquivOfLe hle)

end MF163

theorem modelM12Acts3_proved :
    ModelM12Acts3 := by
  intro X _ _ R S z hm hs hidx hX
  obtain ⟨e₀⟩ := hX
  let e₁ : TL4.FStarQuot X ≃* NativeSporadic.M12 := e₀
  set N := genFittingFStar X with hNdef
  have hNn : N.Normal := genFittingFStar_normal X
  have hZ : Subgroup.center N = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center N) with h | h
    · exact h
    · refine absurd (e₁.symm.injective ?_) m12_gens_not_comm
      have h1 : ∀ q : TL4.FStarQuot X, q = 1 := fun q => by
        obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
        exact (QuotientGroup.eq_one_iff n).2 (h ▸ Subgroup.mem_top n)
      rw [map_mul, map_mul, h1 (e₁.symm m12a), h1 (e₁.symm m12b)]
  let ψ : ↥N ≃* NativeSporadic.M12 :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e₁
  have hi0 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (show N.index = 1 ∨ N.index = 2 by omega) with h1 | h2
  · exact MF163.acts3_of_equiv hm ((Subgroup.topEquiv.symm.trans
      (MulEquiv.subgroupCongr (Subgroup.index_eq_one.1 h1).symm)).trans ψ)
  exfalso
  have hnab : ∃ a b : N, a * b ≠ b * a := ⟨ψ.symm m12a, ψ.symm m12b, fun h =>
    m12_gens_not_comm (by simpa using congrArg ψ h)⟩
  have hC : Subgroup.centralizer (N : Set X) = ⊥ := centralizer_genFittingFStar_eq_bot hnab
  let Φ : X →* MulAut NativeSporadic.M12 :=
    (MulAut.congr ψ).toMonoidHom.comp (MulAut.conjNormal (H := N))
  have hΦ : ∀ (x : X) (n : N), Φ x (ψ n) = ψ (MulAut.conjNormal x n) := fun x n => by
    simp [Φ, MulAut.congr_apply]
  have hΦi : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [← hC, Subgroup.mem_centralizer_iff]
    intro n hn
    have h1 := hΦ x ⟨n, hn⟩
    rw [hx, MulAut.one_apply] at h1
    have h3 := congrArg Subtype.val (ψ.injective h1)
    rw [MulAut.conjNormal_apply] at h3
    calc n * x = (x * n * x⁻¹) * x := by rw [← h3]
      _ = x * n := by group
  have hJ : ComponentClassification.OuterAutomorphisms.inner NativeSporadic.M12 ≤ Φ.range := by
    rintro _ ⟨m, rfl⟩
    refine ⟨ψ.symm m, MulEquiv.ext fun w => ?_⟩
    obtain ⟨n, rfl⟩ := ψ.surjective w
    have h1 : (MulAut.conjNormal (ψ.symm m : X) n : N) = ψ.symm m * n * (ψ.symm m)⁻¹ :=
      Subtype.ext (by rw [MulAut.conjNormal_apply]; rfl)
    rw [hΦ, MulAut.conj_apply, h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  let E : X ≃* Φ.range := MonoidHom.ofInjective hΦi
  have hu : orderOf (E z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hm.datum.order
  have hF := (fourClassesLarge_centralizer _ hJ (E z) hu).of_mulEquiv (centralizerEquiv E z)
  have hO := MF163.tightOddCent_of_equiv E z (oddCore_centralizer _ hJ (E z) hu)
  refine MF163.false_of_index_two hm hF hO hNn h2 fun h => ?_
  have h3 := TA3.TightDatum.genFittingFStar_eq_top_of_le hm.datum hm.cls.2.1 h
  rw [hNdef, h3, Subgroup.index_top] at h2
  exact absurd h2 (by norm_num)

end CFSG.ClassicalInvolution.Q3.TL4
