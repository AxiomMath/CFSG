module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SimpleCfg
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTTits
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Suzuki
import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.YS08
  CFSG.Yardstones.Md42047359a2a
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer congr_conj)

open scoped commutatorElement

private theorem normal_eq_top_or_le_center' {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hp, hs⟩ := hQ
  have := hN.map (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hZ : ⁅Subgroup.center Q, Subgroup.center Q⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
    have hmap : (⊤ : Subgroup Q).map (QuotientGroup.mk' N) =
        (Subgroup.center Q).map (QuotientGroup.mk' N) := by
      rw [← hsup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    have hcomm : commutator Q ≤ N := by
      rw [_root_.commutator_def, ← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
        Subgroup.map_commutator, hmap, ← Subgroup.map_commutator, hZ, Subgroup.map_bot]
    rw [hp] at hcomm
    exact eq_top_iff.mpr hcomm

theorem eq_or_commute_of_isSubnormal {S : Type*} [Group S] {M C : Subgroup S}
    (h : CFSG.Open.IsSubnormal M C) (hC : CFSG.Open.IsQuasisimple ↥C) :
    M = C ∨ ∀ m ∈ M, ∀ c ∈ C, m * c = c * m := by
  induction h with
  | refl => exact Or.inl rfl
  | @step H M K hle hnormal _ ih =>
    rcases ih hC with rfl | hcent
    · rcases normal_eq_top_or_le_center' hC hnormal with htop | hZ
      · left
        exact le_antisymm hle fun k hk => by
          have : (⟨k, hk⟩ : ↥M) ∈ H.subgroupOf M := htop ▸ Subgroup.mem_top _
          exact Subgroup.mem_subgroupOf.1 this
      · right
        intro m hm c hc
        have hz := hZ (Subgroup.mem_subgroupOf.2 (show ((⟨m, hle hm⟩ : ↥M) : S) ∈ H from hm))
        have := (Subgroup.mem_center_iff.1 hz) ⟨c, hc⟩
        exact (congrArg Subtype.val this).symm
    · exact Or.inr fun m hm c hc => hcent m (hle hm) c hc

variable {S : Type} [Group S] [Finite S] {Q : Subgroup (MulAut S)} {x : S} {J : Subgroup S}
  {q : ℕ}

theorem conj_injective_of_center_eq_bot {S : Type*} [Group S] (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hgZ : g ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun s => by
    have h1 := congrArg (fun φ : MulAut S => φ s) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc s * g = g * s * g⁻¹ * g := by rw [h1]
      _ = g * s := by group
  rw [hZ] at hgZ
  exact hgZ

theorem I1433SCfg.ne_one (c : I1433SCfg Q x J q) : x ≠ 1 := by
  intro h
  have := c.order
  rw [h, orderOf_one] at this
  omega

theorem I1433SCfg.commute_conj (c : I1433SCfg Q x J q) {α : MulAut S} (hα : α ∈ Q) :
    α * MulAut.conj x = MulAut.conj x * α := by
  have hx : MulAut.conj x ∈ (Subgroup.center ↥Q).map Q.subtype := by
    rw [c.center]
    exact Subgroup.mem_zpowers _
  obtain ⟨z, hz, hzx⟩ := hx
  have := (Subgroup.mem_center_iff.1 hz) ⟨α, hα⟩
  have h2 := congrArg Subtype.val this
  simp only [Subgroup.coe_mul] at h2
  rw [← hzx]
  exact h2

theorem I1433SCfg.false_of_inner (c : I1433SCfg Q x J q) (hZ : Subgroup.center S = ⊥)
    (hin : ∀ α ∈ Q, ∃ g : S, α = MulAut.conj g)
    (hq : CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({x} : Set S))) : False := by
  obtain ⟨a, ha, b, hb, hab⟩ := c.nonabelian
  have hinj := conj_injective_of_center_eq_bot hZ
  have hmem : ∀ {g : S}, MulAut.conj g ∈ Q → g ∈ Subgroup.centralizer ({x} : Set S) := by
    intro g hg
    have h1 := c.commute_conj hg
    rw [← map_mul, ← map_mul] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hinj h1
  obtain ⟨g, rfl⟩ := hin a ha
  obtain ⟨h, rfl⟩ := hin b hb
  have hcomp := c.comp
  have hJC : J = Subgroup.centralizer ({x} : Set S) := by
    rcases eq_or_commute_of_isSubnormal hcomp.2.1 hq with hJ | hcent
    · exact hJ
    · exfalso
      have hperf : ⁅J, J⁆ = J := glaPComponent_perfect hcomp
      have hbot : ⁅J, J⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro m hm
        rw [Subgroup.mem_centralizer_iff]
        intro n hn
        exact (hcent m hm n (hcomp.1 hn)).symm
      have hx : x ∈ (⊥ : Subgroup S) := by
        rw [← hbot, hperf]
        exact c.mem
      exact c.ne_one (Subgroup.mem_bot.1 hx)
  have hhJ : h ∈ J := hJC ▸ hmem hb
  have hgh := c.centralizes J hcomp (MulAut.conj g) ha h hhJ
  rw [MulAut.conj_apply] at hgh
  apply hab
  rw [← map_mul, ← map_mul]
  congr 1
  calc g * h = (g * h * g⁻¹) * g := by group
    _ = h * g := by rw [hgh]

theorem I1433SCfg.false_of_isSolvable (c : I1433SCfg Q x J q)
    (h : Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set S))) : False := by
  have hcomp := c.comp
  haveI : Group.IsSolvable ↥J :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hcomp.1)
      (Subgroup.inclusion_injective hcomp.1)
  haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr (glaPComponent_perfect hcomp)
  haveI : Nontrivial ↥J := ⟨⟨⟨x, c.mem⟩, 1, fun h1 => c.ne_one (congrArg Subtype.val h1)⟩⟩
  exact Group.IsPerfect.not_isSolvable ↥J inferInstance

section Families

set_option linter.unusedSectionVars false


open CFSG.LieType.Ree in
theorem reeF4_commutator_le_inner {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    commutator (MulAut (ReeTag.F4.reeGamma K a)) ≤ inner (ReeTag.F4.reeGamma K a) := by
  obtain ⟨-, -, -, hcyc, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_full_inner_field_automorphism_normal_form
      a ha K hK
  letI : CommGroup (Outer (ReeTag.F4.reeGamma K a)) := IsCyclic.commGroup
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [← QuotientGroup.eq_one_iff]
  change QuotientGroup.mk' (inner (ReeTag.F4.reeGamma K a)) ⁅g₁, g₂⁆ = 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

theorem exists_conj_of_mem_commutator {S Γ : Type} [Group S] [Group Γ] (e : S ≃* Γ)
    (h : commutator (MulAut Γ) ≤ inner Γ) {α : MulAut S} (hα : α ∈ commutator (MulAut S)) :
    ∃ g : S, α = MulAut.conj g := by
  have hmap : (commutator (MulAut S)).map (MulAut.congr e).toMonoidHom = commutator (MulAut Γ) := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (MulAut.congr e).surjective]
  have h1 : MulAut.congr e α ∈ inner Γ := h (hmap ▸ Subgroup.mem_map_of_mem _ hα)
  obtain ⟨γ, hγ⟩ := h1
  refine ⟨e.symm γ, ?_⟩
  rw [← congr_conj e.symm γ, hγ]
  ext s
  simp [MulAut.congr_apply]

open CFSG.LieType.Ree in
theorem reeF4_centralizer_isQuasisimple {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {S : Type} [Group S]
    (e : S ≃* ReeTag.F4.reeGamma K a) {x : S} (hx : orderOf x = 3) :
    CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({x} : Set S)) := by
  classical
  haveI : Finite (CFSG.Blueprint.Chevalley.ModGL ReeTag.F4.tag K) :=
    CFSG.LieType.Chevalley.finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hex : orderOf (e x) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact hx
  obtain ⟨E⟩ := CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU a K hK
    (e x) hex
  have hF'card : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]
  have hq := (CFSG.RankThree.PartTwo.Sec8.Item87Proof.isQuasisimple_statedSU_three
    (F := GaloisField 2 (2 * (2 * a + 1))) (f := 2 * a + 1) hF'card (by omega)).1
  have hmap : (Subgroup.centralizer ({x} : Set S)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set (ReeTag.F4.reeGamma K a)) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [← map_mul, ← map_mul, hg]
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy
  let E₀ : ↥(Subgroup.centralizer ({x} : Set S)) ≃*
      ↥(Subgroup.centralizer ({e x} : Set (ReeTag.F4.reeGamma K a))) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
  exact LieSemisimple.open_isQuasisimple (CFSG.IsQuasisimple.of_mulEquiv (E₀.trans E) hq)

theorem nonD4LieContraS_suzukiReeTits : NonD4LieContraS .suzukiReeTits := by
  intro S _ _ hs hna p hp hp3 idx hF hidx he hD Q x J q c
  haveI := hs
  have hZ : Subgroup.center S = ⊥ := b3Lie_center_eq_bot hna
  obtain ⟨d, hv⟩ := idx
  have hx3 : MulAut.conj x ^ 3 = 1 := by
    rw [← map_pow, ← c.order, pow_orderOf_eq_one, map_one]
  have hx1 : MulAut.conj x ≠ 1 := fun h1 =>
    c.ne_one (conj_injective_of_center_eq_bot hZ (h1.trans (map_one _).symm))
  have hfix : fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set S) :=
    CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj x
  cases d with
  | suzuki m =>
    exact LieComp.noThreeComponents_suzuki m hv he (MulAut.conj x) J (by
      show GLAPComponent 3 (fixSubgroup (MulAut.conj x)) J
      rw [hfix]
      exact c.comp)
  | reeG2 m => exact hp3 hidx.symm
  | tits =>
    refine c.false_of_isSolvable ?_
    rw [← hfix]
    exact LieComp.isSolvable_fixSubgroup_tits hv hna he Nat.prime_three (by norm_num) hx3 hx1
  | reeF4 m =>
    obtain ⟨e0⟩ := he
    have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index m hv e0
    obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hR
    exact c.false_of_inner hZ
      (fun α hα => exists_conj_of_mem_commutator e (reeF4_commutator_le_inner ha hK) (c.derived hα))
      (reeF4_centralizer_isQuasisimple ha hK e c.order)
  | _ => simp [lieFamily] at hF

end Families

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
