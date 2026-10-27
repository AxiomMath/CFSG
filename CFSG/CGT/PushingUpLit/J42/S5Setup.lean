module

public import CFSG.CGT.PushingUpLit.SolK.FourD
public import CFSG.CGT.PushingUpLit.SolK.GenFourA8
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import Certificates.Data.A5

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.GH74 CFSG.CGT.PushingUpLit.BHS
  CFSG.Quasithin CFSG.Quasithin.G6 Equiv Equiv.Perm

@[expose] def xI : ↥(coreMod 5) := mkEven ![1, 1, 1, 1, 0] (by decide)

@[expose] def tau0 : Perm (Fin 5) := swap 0 1 * swap 2 3

@[expose] def d8 : Subgroup (Perm (Fin 5)) where
  carrier := {σ | tau0 * σ = σ * tau0}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    have ha' : tau0 * a = a * tau0 := ha
    have hb' : tau0 * b = b * tau0 := hb
    show tau0 * (a * b) = a * b * tau0
    rw [← mul_assoc, ha', mul_assoc, hb', mul_assoc]
  inv_mem' := fun {a} ha => by
    have ha' : tau0 * a = a * tau0 := ha
    show tau0 * a⁻¹ = a⁻¹ * tau0
    calc tau0 * a⁻¹ = a⁻¹ * (a * tau0) * a⁻¹ := by group
      _ = a⁻¹ * (tau0 * a) * a⁻¹ := by rw [ha']
      _ = a⁻¹ * tau0 := by group

instance : DecidablePred (· ∈ d8) := fun σ => inferInstanceAs (Decidable (tau0 * σ = σ * tau0))

theorem card_d8 : Nat.card d8 = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem isPGroup_d8 : IsPGroup 2 d8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (n := 3) (by rw [card_d8]; norm_num)

theorem eq_of_fixed_d8 {v : ↥(coreMod 5)} (h : ∀ σ ∈ d8, coreAct 5 σ v = v) :
    v = 1 ∨ v = xI := by
  have h1 := congrArg (fun u => vcoord u 0) (h (swap 0 1) (by decide))
  have h2 := congrArg (fun u => vcoord u 2) (h (swap 2 3) (by decide))
  have h3 := congrArg (fun u => vcoord u 0) (h (swap 0 2 * swap 1 3) (by decide))
  simp only [vcoord_coreAct] at h1 h2 h3
  have e1 : vcoord v 1 = vcoord v 0 := by
    have : (swap 0 1 : Perm (Fin 5))⁻¹ 0 = 1 := by decide
    rw [this] at h1; exact h1
  have e3 : vcoord v 3 = vcoord v 2 := by
    have : (swap 2 3 : Perm (Fin 5))⁻¹ 2 = 3 := by decide
    rw [this] at h2; exact h2
  have e2 : vcoord v 2 = vcoord v 0 := by
    have : (swap 0 2 * swap 1 3 : Perm (Fin 5))⁻¹ 0 = 2 := by decide
    rw [this] at h3; exact h3
  have hs := sum_vcoord v
  simp only [Fin.sum_univ_five] at hs
  have e4 : vcoord v 4 = 0 := by
    rw [e1, e3, e2] at hs
    have : ∀ a b : ZMod 2, a + a + a + a + b = 0 → b = 0 := by decide
    exact this _ _ hs
  have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hcases (vcoord v 0) with h0 | h0
  · left
    refine vcoord_ext fun i => ?_
    fin_cases i <;> simp [vcoord_one, h0, e1, e2, e3, e4]
  · right
    refine vcoord_ext fun i => ?_
    fin_cases i <;> simp [xI, vcoord_mkEven, h0, e1, e2, e3, e4]

theorem gen4_of_sylow_le {G : Type} [Group G] [Finite G] {K : Subgroup G} (T : Sylow 2 G)
    (hTK : (T : Subgroup G) ≤ K) (h : SectionalTwoRankLE ↥K 4) : SectionalTwoRankLE G 4 :=
  SectionalTwoRankLE.of_sylow T
    (SectionalTwoRankLE.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hTK)
      (SectionalTwoRankLE.subgroup ((T : Subgroup G).subgroupOf K) h))

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (S : SolCfg G M X 2)

namespace SolCfg

include S

theorem theta_surjective (hA : ∃ m : ↥M, sign (S.θ m) = -1) : Function.Surjective S.θ := by
  obtain ⟨m₀, hm₀⟩ := hA
  intro σ
  have hX : ∀ τ ∈ alternatingGroup (Fin (2 * 2 + 1)), ∃ m : ↥M, S.θ m = τ := by
    intro τ hτ
    obtain ⟨c, hc⟩ := S.D.ρ_surj τ hτ
    exact ⟨⟨(c : G), S.hyp.le c.2⟩, by rw [S.θ_X c, hc]⟩
  by_cases hs : sign σ = 1
  · exact hX σ (Equiv.Perm.mem_alternatingGroup.2 hs)
  · have hs' : sign σ = -1 := (Int.units_eq_one_or _).resolve_left hs
    have : σ * (S.θ m₀)⁻¹ ∈ alternatingGroup (Fin (2 * 2 + 1)) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hs', hm₀]; decide
    obtain ⟨m₁, hm₁⟩ := hX _ this
    exact ⟨m₁ * m₀, by rw [map_mul, hm₁, inv_mul_cancel_right]⟩

@[expose] noncomputable def S0 : Subgroup G := (d8.comap S.θ).map M.subtype

theorem mem_S0 {g : G} : g ∈ S.S0 ↔ ∃ hg : g ∈ M, S.θ ⟨g, hg⟩ ∈ d8 := by
  unfold S0
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem Q_le_S0 : pCoreOf 2 M ≤ S.S0 := fun q hq =>
  S.mem_S0.2 ⟨pCoreOf_le_self M hq, by rw [S.theta_eq_one_of_mem_Q hq]; exact d8.one_mem⟩

theorem isPGroup_S0 (hR : RSmall S) : IsPGroup 2 S.S0 := by
  have hker : IsPGroup 2 S.θ.ker := by
    let f : S.θ.ker →* ↥(pCoreOf 2 M) :=
      { toFun := fun m => ⟨(m : ↥M).1, S.mem_Q_of_theta_eq_one hR (m : ↥M).2 m.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine (isPGroup_pCoreOf' M).of_injective f fun a b h => ?_
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : ↥(pCoreOf 2 M) => (y : G)) h
  exact (isPGroup_d8.comap_of_ker_isPGroup S.θ hker).map M.subtype

@[expose] noncomputable def x0 : G := ((S.D.β.symm xI : ↥S.D.W) : G)

theorem x0_mem_W : S.x0 ∈ S.D.W := (S.D.β.symm xI).2

theorem β_x0 : S.D.β ⟨S.x0, S.x0_mem_W⟩ = xI := S.D.β.apply_symm_apply xI

theorem le_centralizer_x0 (hR : RSmall S) (hrbot : rOf M X = ⊥)
    (hA : ∃ m : ↥M, sign (S.θ m) = -1) (T : Sylow 2 G) (hST : S.S0 ≤ (T : Subgroup G)) :
    (T : Subgroup G) ≤ CGOf S.x0 := by
  classical
  have hsurj := S.theta_surjective hA
  have hWT : S.D.W ≤ (T : Subgroup G) := S.W_le_Q.trans (S.Q_le_S0.trans hST)
  have hnt : Nontrivial ↥(T : Subgroup G) := by
    obtain ⟨w, hw, hw1⟩ : ∃ w ∈ S.D.W, w ≠ 1 := by
      by_contra h
      push Not at h
      exact S.W_ne_bot (eq_bot_iff.2 fun w hw => Subgroup.mem_bot.2 (h w hw))
    exact ⟨⟨⟨w, hWT hw⟩, 1, fun h => hw1 (congrArg Subtype.val h)⟩⟩
  have hcen := T.isPGroup'.center_nontrivial
  obtain ⟨⟨z, hzc⟩, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥(T : Subgroup G)))
  have hzcomm : ∀ t ∈ (T : Subgroup G), (z : G) * t = t * z := fun t ht => by
    have := Subgroup.mem_center_iff.1 hzc ⟨t, ht⟩
    exact congrArg Subtype.val this.symm
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  have hzQ : ∀ q ∈ pCoreOf 2 M, (z : G) * q * (z : G)⁻¹ = q := fun q hq => by
    rw [hzcomm q (hST (S.Q_le_S0 hq))]
    group
  have hzM : (z : G) ∈ M := by
    rw [← S.normalizer_Q_eq, Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      show (z : G) * q * (z : G)⁻¹ ∈ pCoreOf 2 M
      rw [hzQ q hq]
      exact hq
    · intro hq
      have hq' : (z : G) * q * (z : G)⁻¹ ∈ pCoreOf 2 M := hq
      have h1 := hzQ _ hq'
      have h2 : (z : G) * q * (z : G)⁻¹ = q := by
        have := congrArg (fun t => (z : G)⁻¹ * t * z) h1
        simpa [mul_assoc] using this
      show q ∈ pCoreOf 2 M
      rw [← h2]
      exact hq'
  have hθz : S.θ ⟨(z : G), hzM⟩ = 1 := by
    refine (theta_eq_one_iff S.D S.xnorm S.hyp.two_le ⟨(z : G), hzM⟩).2 fun w hw => ?_
    exact hzQ w (S.W_le_Q hw)
  have hzQ' : (z : G) ∈ pCoreOf 2 M := S.mem_Q_of_theta_eq_one hR hzM hθz
  have hzW : (z : G) ∈ S.D.W := S.mem_W_of_rOf_bot hrbot hzQ'
  have hfix : ∀ σ ∈ d8, coreAct 5 σ (S.D.β ⟨(z : G), hzW⟩) = S.D.β ⟨(z : G), hzW⟩ := by
    intro σ hσ
    obtain ⟨m, hm⟩ := hsurj σ
    have hmS : (m : G) ∈ S.S0 := S.mem_S0.2 ⟨m.2, by
      rw [show (⟨(m : G), m.2⟩ : ↥M) = m from rfl, hm]
      exact hσ⟩
    have hc : (z : G) * m = m * z := hzcomm m (hST hmS)
    have hW' : (m : G) * (z : G) * (m : G)⁻¹ ∈ S.D.W := S.W_normalized m.2 hzW
    have h1 := S.θ_spec m ⟨(z : G), hzW⟩ hW'
    have e : (⟨(m : G) * (z : G) * (m : G)⁻¹, hW'⟩ : ↥S.D.W) = ⟨(z : G), hzW⟩ :=
      Subtype.ext (by
        show (m : G) * (z : G) * (m : G)⁻¹ = (z : G)
        rw [← hc]
        group)
    rw [e, hm] at h1
    exact h1.symm
  have hz0 : (z : G) = S.x0 := by
    rcases eq_of_fixed_d8 hfix with h1 | h2
    · exfalso
      apply hz1'
      have := S.D.β.injective (h1.trans (map_one _).symm)
      exact congrArg Subtype.val this
    · have : (⟨(z : G), hzW⟩ : ↥S.D.W) = S.D.β.symm xI := by rw [← h2]; simp
      exact congrArg Subtype.val this
  intro t ht
  refine mem_centralizer_zpowers_iff.2 ?_
  rw [← hz0]
  calc t * (z : G) * t⁻¹ = (z * t) * t⁻¹ := by rw [hzcomm t ht]
    _ = z := by group

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
