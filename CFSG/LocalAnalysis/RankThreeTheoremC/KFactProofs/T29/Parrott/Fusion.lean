module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.Assembly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup TauCeti
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (NoE27)
open CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev (NoE27.of_injective noE27_projSL
  noE27_projSU orderOf_card_zmod_three)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
  (sylow_isMulCommutative_of_sigmaModel_of_lt sylow_comm_of_subgroup sylow_comm_of_surjective)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure (statedSU_le_statedGU)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
  (I294Cross.orderOf_neg_natCast_one)

@[expose] def IsRankTwoExcIndex : LieTypeIndex → Prop
  | .G2 _ | .trialityD4 _ | .reeF4 _ => True
  | _ => False

@[expose] def InnerFusionE9Exc : Prop :=
  ∀ d : ValidLieTypeIndex, d.1.characteristic ≠ 3 → IsRankTwoExcIndex d.1 →
    ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* (CFSGIndex.lie d).Group) →
      ∀ α : MulAut K, α ^ 3 = 1 → α ∉ (MulAut.conj : K →* MulAut K).range →
        ∀ x : K, orderOf x = 3 → ∃ (g : K) (E : Subgroup K), IsElemAbelian 3 E ∧
          Nat.card E = 9 ∧ g * x * g⁻¹ ∈ E ∧ ∀ e ∈ E, α e = e

section Generic

theorem exists_conj_mem_of_sylow_comm {K : Type} [Group K] [Finite K]
    (hcomm : ∀ S : Sylow 3 K, IsMulCommutative (S : Subgroup K)) (hno : NoE27 K)
    {E : Subgroup K} (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) {x : K}
    (hx : orderOf x = 3) : ∃ g : K, g * x * g⁻¹ ∈ E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := fun e => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 e e.2)⟩
  obtain ⟨S, hES⟩ := hEp.exists_le_sylow
  have hxp : IsPGroup 3 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨T, hxT⟩ := hxp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K T S
  have hyS : g * x * g⁻¹ ∈ (S : Subgroup K) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨x, hxT (Subgroup.mem_zpowers x), rfl⟩
  refine ⟨g, ?_⟩
  by_contra hyE
  set y := g * x * g⁻¹ with hydef
  have hy3 : y ^ 3 = 1 := by
    rw [hydef, conj_pow, ← hx, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  have hcy : ∀ a ∈ E, a * y = y * a := fun a ha =>
    congrArg Subtype.val ((hcomm S).is_comm.comm ⟨a, hES ha⟩ ⟨y, hyS⟩)
  have hZ : IsElemAbelian 3 (zpowers y) := by
    rw [Subgroup.zpowers_eq_closure]
    refine IsElemAbelian.closure_of_commute (fun a ha b hb => ?_) (fun a ha => ?_)
    · rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]
    · rw [Set.mem_singleton_iff] at ha
      rw [ha, hy3]
  have hcomm' : ∀ a ∈ E, ∀ b ∈ zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (hcy a ha) k).eq
  refine hno ⟨E ⊔ zpowers y, hE.sup_of_commute hZ hcomm', ?_⟩
  rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three E hy3 hyE hcy, hE9]

end Generic

section Classical

theorem sylow_comm_projSL {F : Type} [Field F] [Finite F] (hF : ¬ 3 ∣ Nat.card F) {n : ℕ}
    (hlt : n / orderOf (Nat.card F : ZMod 3) < 3) :
    ∀ S : Sylow 3 (StatedProj (StatedSL n F)),
      IsMulCommutative (S : Subgroup (StatedProj (StatedSL n F))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hF' : ¬ 3 ∣ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  have hGL := sylow_isMulCommutative_of_sigmaModel_of_lt Nat.prime_three
    (by rwa [← Nat.card_eq_fintype_card])
    (fun P => CFSG.GroupTheory.WeirSylow.sylow_GL (by decide) F hF' n P)
  exact sylow_comm_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (sylow_comm_of_subgroup (StatedSL n F) hGL)

theorem sylow_comm_projSU {L : Type} [Field L] [Finite L] {q n : ℕ} (hL : Nat.card L = q ^ 2)
    (hq3 : ¬ 3 ∣ q) (hn : 1 ≤ n) (hlt : n / orderOf (-(q : ZMod 3)) < 3) :
    ∀ S : Sylow 3 (StatedProj (StatedSU n q L)),
      IsMulCommutative (S : Subgroup (StatedProj (StatedSU n q L))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype L := Fintype.ofFinite L
  have hL' : Fintype.card L = q ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hL
  have hGU := sylow_isMulCommutative_of_sigmaModel_of_lt Nat.prime_three hlt
    (fun P => CFSG.GroupTheory.WeirSylow.sylow_GU (by decide) L hL' hq3 hn P)
  have hle := statedSU_le_statedGU (L := L) (q := q) (n := n)
  have hSU := sylow_comm_of_surjective (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
    (MulEquiv.surjective _) (sylow_comm_of_subgroup _ hGU)
  exact sylow_comm_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) hSU

theorem sylow_comm_projSp_two {F : Type} [Field F] [Finite F] (hF : ¬ 3 ∣ Nat.card F) :
    ∀ S : Sylow 3 (StatedProj (StatedSp 2 F)),
      IsMulCommutative (S : Subgroup (StatedProj (StatedSp 2 F))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hF' : ¬ 3 ∣ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  have hmod : Fintype.card F % 3 = 1 ∨ Fintype.card F % 3 = 2 := by omega
  have hSp : ∀ S : Sylow 3 (StatedSp 2 F), IsMulCommutative (S : Subgroup (StatedSp 2 F)) := by
    refine sylow_isMulCommutative_of_sigmaModel_of_lt Nat.prime_three ?_
      fun P => CFSG.GroupTheory.WeirSylow.sylow_Sp (by decide) F hF' 2 P
    rcases hmod with h | h
    · rw [orderOf_card_zmod_three_one h]
      simp
    · rw [orderOf_card_zmod_three h]
      simp
  exact sylow_comm_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) hSp

theorem sylow_comm_and_noE27 (d : ValidLieTypeIndex) (hch : d.1.characteristic ≠ 3)
    (hd : IsRankTwoIndex d.1) (hexc : ¬ IsRankTwoExcIndex d.1) (K : Type) [Group K] [Finite K]
    (e : K ≃* (CFSGIndex.lie d).Group) :
    (∀ S : Sylow 3 K, IsMulCommutative (S : Subgroup K)) ∧ NoE27 K := by
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | A r q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_A] using hch
    obtain ⟨hr, hq⟩ := hd
    obtain ⟨-, F, _, _, hF, ⟨f⟩⟩ :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    have hF3 : ¬ 3 ∣ Nat.card F := by
      rw [hF]; exact not_three_dvd_prime_pow q.prime_p hp3
    have hFq : Nat.card F % 3 = 2 := by rw [hF, ← PrimePower.card_def]; exact hq
    have hlt : (r + 1) / orderOf (Nat.card F : ZMod 3) < 3 := by
      rw [orderOf_card_zmod_three hFq]
      rcases hr with rfl | rfl <;> norm_num
    refine ⟨sylow_comm_of_surjective f.symm.toMonoidHom f.symm.surjective
      (sylow_comm_projSL hF3 hlt), NoE27.of_injective (φ := f.toMonoidHom) f.injective
        (noE27_projSL hF3 ?_ hlt)⟩
    rcases hr with rfl | rfl <;> norm_num
  | twistedA r q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_twistedA] using hch
    obtain ⟨hr, hq⟩ := hd
    obtain ⟨-, F, _, _, hF, ⟨f⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    have hq3 : ¬ 3 ∣ q.p ^ q.exponent := not_three_dvd_prime_pow q.prime_p hp3
    have hq1 : q.p ^ q.exponent % 3 = 1 := by rw [← PrimePower.card_def]; exact hq
    have hlt : (r + 1) / orderOf (-((q.p ^ q.exponent : ℕ) : ZMod 3)) < 3 := by
      rw [I294Cross.orderOf_neg_natCast_one hq1]
      rcases hr with rfl | rfl <;> norm_num
    refine ⟨sylow_comm_of_surjective f.symm.toMonoidHom f.symm.surjective
      (sylow_comm_projSU hF hq3 (by omega) hlt), NoE27.of_injective (φ := f.toMonoidHom)
        f.injective (noE27_projSU hF hq3 (by omega) ?_ hlt)⟩
    rcases hr with rfl | rfl <;> norm_num
  | B r q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_B] using hch
    obtain rfl : r = 2 := hd
    obtain ⟨-, F, _, _, hF, ⟨f⟩⟩ := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
    have hF3 : ¬ 3 ∣ Nat.card F := by
      rw [hF]; exact not_three_dvd_prime_pow q.prime_p hp3
    exact ⟨sylow_comm_of_surjective f.symm.toMonoidHom f.symm.surjective
      (sylow_comm_projSp_two hF3), NoE27.of_injective (φ := f.toMonoidHom) f.injective
        (noE27_projSp_two hF3)⟩
  | G2 q => exact absurd trivial hexc
  | trialityD4 q => exact absurd trivial hexc
  | reeF4 m => exact absurd trivial hexc
  | C r q => exact hd.elim
  | D r q => exact hd.elim
  | twistedD r q => exact hd.elim
  | E6 q => exact hd.elim
  | E7 q => exact hd.elim
  | E8 q => exact hd.elim
  | F4 q => exact hd.elim
  | twistedE6 q => exact hd.elim
  | suzuki k => exact hd.elim
  | reeG2 k => exact hd.elim
  | tits => exact hd.elim

end Classical

theorem innerFusionE9_of_exc (h2a : OuterFixedE9) (h2b : InnerFusionE9Exc) : InnerFusionE9 := by
  intro d hch hd K _ _ he α hα3 hαo x hx
  by_cases hexc : IsRankTwoExcIndex d.1
  · exact h2b d hch hexc K he α hα3 hαo x hx
  · obtain ⟨E, hE, hE9, hfix⟩ := h2a d hch (Or.inl hd) K he α hα3 hαo
    obtain ⟨e⟩ := he
    obtain ⟨hcomm, hno⟩ := sylow_comm_and_noE27 d hch hd hexc K e
    obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow_comm hcomm hno hE hE9 hx
    exact ⟨g, E, hE, hE9, hg, hfix⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
