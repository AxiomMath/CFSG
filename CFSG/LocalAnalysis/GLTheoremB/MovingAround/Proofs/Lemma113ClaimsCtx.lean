module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113d
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113f
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113g
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113ClaimsL2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)
open scoped MatrixGroups Pointwise commutatorElement

namespace Lemma113Claims

variable {G : Type} [Group G] [Finite G]

structure Ctx (E A : Subgroup G) (e : G) (K Q : Subgroup G) : Prop where
  he3 : e ^ 3 = 1
  he1 : e ≠ 1
  heE : e ∈ E
  heA : e ∈ A
  hKX : K ≤ Cg e
  hXN : Cg e ≤ Subgroup.normalizer (K : Set G)
  hKI : IsLTwoTwentySeven (barOf 3 K)
  hQ : IsSylowIn 3 (Cg e) Q
  hQ1 : Q ≠ ⊥
  heQ : e ∈ Q
  hEQ : E ≤ Q
  hAQ : A ≤ Q
  hEel : IsElemAbelian 3 E
  hEcard : Nat.card E = 3 ^ 4
  hAel : IsElemAbelian 3 A
  hAcard : Nat.card A = 3 ^ 3
  hcyc : IsCyclic ↥(centBar 3 Q K)
  hEeq : E = (Q ⊓ K : Subgroup G) ⊔ Subgroup.zpowers e
  hAmax : ∀ F : Subgroup G, F ≤ ⊤ → IsElemAbelian 3 F → A ≤ F → F = A
  hAnE : ¬ A ≤ E

theorem hC113 : Lemma113d.Input113dCentralizer27 := L2.input113dCentralizer27_holds

theorem hF2' :
    ∀ (Y : Type) [Group Y] (_ : Y ≃* PSL(2, GaloisField 3 3)) (U : Subgroup (MulAut Y)),
      U ≤ (MulAut.conj : Y →* MulAut Y).range → Nat.card U = 27 →
      ∀ σ : MulAut Y, (∀ u ∈ U, σ * u = u * σ) → σ ∈ U := fun Y _ e U hUi hU σ hσ =>
  L2.centralizer_mulAut_sylow_le e U hUi hU σ hσ

theorem Ctx.of_cfg {m : ℕ} {B M E A : Subgroup G}
    {a e : G} {K Q : Subgroup G} (h : Cfg113 G m B M E A a e K Q)
    (hA : Claim113A (M := M) E A e K Q) : Ctx E A e K Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDD : IsDDpStar 3 M E A := h.pair
  have hEmax : IsSCp 3 ⊤ E := (lemma104_ii_holds h.toSec10Fails hDD).1
  have hAmax : IsSCp 3 ⊤ A := (lemma104_ii_holds h.toSec10Fails hDD).2
  obtain ⟨_, hQM, hCeN, hcyc, _, _, _⟩ := hA
  have hEQ : E ≤ Q := le_trans le_sup_left h.hQ.2
  have hAQ : A ≤ Q := le_trans le_sup_right h.hQ.2
  have heA : e ∈ A := (Subgroup.mem_inf.1 h.he.1).2
  have heE : e ∈ E := (Subgroup.mem_inf.1 h.he.1).1
  have he3 : e ^ 3 = 1 := hAmax.2.1.2 e heA
  have he1 : e ≠ 1 := h.he.2
  have heQ : e ∈ Q := hAQ heA
  have haQ : a ∈ Q := hAQ h.ha.1
  have hQ1 : Q ≠ ⊥ := by
    intro hbot
    rw [hbot] at haQ
    exact h.ha.2 (Subgroup.mem_bot.1 haQ)
  have hKX : K ≤ Cg e := h.hK.1.1
  have hKI : IsLTwoTwentySeven (barOf 3 K) := h.hK.2
  have hXe : ∀ x ∈ Cg e, e * x = x * e := fun x hx =>
    Subgroup.mem_centralizer_iff.1 hx e (Set.mem_singleton e)
  have hKe : ∀ k ∈ K, e * k = k * e := fun k hk => hXe k (hKX hk)
  have hEel : IsElemAbelian 3 E := hEmax.2.1
  have hEcard : Nat.card ↥E = 3 ^ 4 := by
    rw [l113_card_eq_pow_pRank hEmax.2.1, h.h4]
  have hAel : IsElemAbelian 3 A := hAmax.2.1
  have hAcard : Nat.card ↥A = 3 ^ 3 := by
    rw [l113_card_eq_pow_pRank hAmax.2.1, h.h3]
  have hQsyl : IsSylowIn 3 (Cg e) Q := h.hQ.1
  have hQp : IsPGroup 3 ↥Q := hQsyl.2.1
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := hQsyl.1.trans hCeN
  have hU := Lemma113d.Ubar_elemAbelian hQsyl hQ1 hCeN hKX hKI
  have hU27 := Lemma113d.Ubar_card hQsyl hQ1 hCeN hKX hKI
  obtain ⟨e0⟩ := hKI
  have hEle := Lemma113d.le_sup_of_elemAbelian_card_ge hC113 e0 hQp hQK hcyc hU hU27 hEQ hEel
    (by rw [hEcard]; norm_num)
  have hEeq := Lemma113d.eq_sup_zpowers_of_le hQsyl hQ1 hCeN hKX ⟨e0⟩ hcyc hKe he3 he1 heQ hEel
    (by rw [hEcard]; norm_num) hEle
  have hAnE : ¬ A ≤ E := by
    intro hAE
    have hEA : E = A := hAmax.2.2 E le_top hEel hAE
    have h4 := h.h4
    rw [hEA] at h4
    have h3 := h.h3
    omega
  exact ⟨he3, he1, heE, heA, hKX, hCeN, ⟨e0⟩, hQsyl, hQ1, heQ, hEQ, hAQ, hEel, hEcard, hAel,
    hAcard, hcyc, hEeq, hAmax.2.2, hAnE⟩

namespace Ctx

variable {E A : Subgroup G} {e : G} {K Q : Subgroup G}

theorem hQK (c : Ctx E A e K Q) : Q ≤ Subgroup.normalizer (K : Set G) := c.hQ.1.trans c.hXN

theorem hQp (c : Ctx E A e K Q) : IsPGroup 3 ↥Q := c.hQ.2.1

theorem hKe (c : Ctx E A e K Q) : ∀ k ∈ K, e * k = k * e := fun k hk =>
  Subgroup.mem_centralizer_iff.1 (c.hKX hk) e (Set.mem_singleton e)

theorem hQe (c : Ctx E A e K Q) : ∀ q ∈ Q, e * q = q * e := fun q hq =>
  Subgroup.mem_centralizer_iff.1 (c.hQ.1 hq) e (Set.mem_singleton e)

theorem Q0_le_E (c : Ctx E A e K Q) : (Q ⊓ K : Subgroup G) ≤ E := by
  rw [c.hEeq]
  exact le_sup_left

theorem e_mem_centBar (c : Ctx E A e K Q) : e ∈ centBar 3 Q K :=
  Lemma113d.e_mem_centBar c.hQ c.hXN c.hKe c.heQ

theorem centBar_le (c : Ctx E A e K Q) : centBar 3 Q K ≤ Q := fun g hg =>
  (Lemma113d.mem_centBar_iff.1 hg).1

theorem card_Q0 (c : Ctx E A e K Q) : Nat.card ↥(Q ⊓ K : Subgroup G) = 27 :=
  Lemma113d.card_inf_eq_27 c.hQ c.hQ1 c.hXN c.hKX c.hKI

theorem Q0_elemAbelian (c : Ctx E A e K Q) : IsElemAbelian 3 (Q ⊓ K : Subgroup G) :=
  Lemma113d.isElemAbelian_inf c.hQ c.hQ1 c.hXN c.hKX c.hKI

theorem comm_centBar_Q0 (c : Ctx E A e K Q) {u q : G} (hu : u ∈ centBar 3 Q K)
    (hq : q ∈ (Q ⊓ K : Subgroup G)) : u * q = q * u :=
  Lemma113d.commute_of_mem_centBar c.hQ hu hq

theorem Q0_inf_centBar (c : Ctx E A e K Q) : (Q ⊓ K : Subgroup G) ⊓ centBar 3 Q K = ⊥ :=
  Lemma113d.inf_centBar_eq_bot c.hQ c.hXN c.hKI

theorem inf_centralizer_eq (c : Ctx E A e K Q) :
    Q ⊓ Subgroup.centralizer (E : Set G) = (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K := by
  apply le_antisymm
  · rintro q ⟨hqQ, hqC⟩
    obtain ⟨e0⟩ := c.hKI
    have hU27 := Lemma113d.Ubar_card c.hQ c.hQ1 c.hXN c.hKX c.hKI
    have hcent : ∀ u ∈ Lemma113d.Ubar c.hQK,
        Lemma113d.rhoQ c.hQK ⟨q, hqQ⟩ * u = u * Lemma113d.rhoQ c.hQK ⟨q, hqQ⟩ := by
      rintro _ ⟨d, rfl⟩
      have hdK : ((d : ↥((Q ⊓ K : Subgroup G).subgroupOf Q)) : G) ∈ (Q ⊓ K : Subgroup G) :=
        Subgroup.mem_subgroupOf.1 d.2
      have hdE : ((d : ↥((Q ⊓ K : Subgroup G).subgroupOf Q)) : G) ∈ E := c.Q0_le_E hdK
      have hcomm : q * ((d : ↥((Q ⊓ K : Subgroup G).subgroupOf Q)) : G) =
          ((d : ↥((Q ⊓ K : Subgroup G).subgroupOf Q)) : G) * q :=
        (Subgroup.mem_centralizer_iff.1 hqC _ hdE).symm
      have hmul : (⟨q, hqQ⟩ : ↥Q) * (d : ↥((Q ⊓ K : Subgroup G).subgroupOf Q)).1 =
          (d : ↥((Q ⊓ K : Subgroup G).subgroupOf Q)).1 * ⟨q, hqQ⟩ := Subtype.ext hcomm
      simp only [MonoidHom.comp_apply, Subgroup.subtype_apply]
      rw [← map_mul, ← map_mul, hmul]
    have hin : Lemma113d.rhoQ c.hQK ⟨q, hqQ⟩ ∈ Lemma113d.Ubar c.hQK :=
      hF2' (barOf 3 K) e0 (Lemma113d.Ubar c.hQK) (Lemma113d.Ubar_le_inner c.hQK) hU27 _ hcent
    exact Lemma113d.mem_sup_of_rho_inner e0 c.hQp c.hQK hU27 ⟨q, hqQ⟩
      (Lemma113d.Ubar_le_inner c.hQK hin)
  · apply sup_le
    · intro x hx
      refine Subgroup.mem_inf.2 ⟨hx.1, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro y hy
      exact congrArg Subtype.val (c.hEel.1.is_comm.comm ⟨y, hy⟩ ⟨x, c.Q0_le_E hx⟩)
    · intro u hu
      refine Subgroup.mem_inf.2 ⟨c.centBar_le hu, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro y hy
      have hyE : y ∈ (Q ⊓ K : Subgroup G) ⊔ Subgroup.zpowers e := c.hEeq ▸ hy
      have hle : (Q ⊓ K : Subgroup G) ⊔ Subgroup.zpowers e ≤ Subgroup.centralizer ({u} : Set G) := by
        apply sup_le
        · intro q hq
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          rw [Set.mem_singleton_iff.1 hw]
          exact c.comm_centBar_Q0 hu hq
        · apply Subgroup.zpowers_le.2
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          rw [Set.mem_singleton_iff.1 hw]
          exact (c.hQe u (c.centBar_le hu)).symm ▸ rfl
      have := Subgroup.mem_centralizer_iff.1 (hle hyE) u (Set.mem_singleton u)
      exact this.symm

theorem eq_of_elemAbelian_card81 (c : Ctx E A e K Q)
    {F : Subgroup G} (hFQ : F ≤ Q) (hF : IsElemAbelian 3 F) (hF81 : Nat.card ↥F = 81) :
    F = E := by
  obtain ⟨e0⟩ := c.hKI
  have hU := Lemma113d.Ubar_elemAbelian c.hQ c.hQ1 c.hXN c.hKX c.hKI
  have hU27 := Lemma113d.Ubar_card c.hQ c.hQ1 c.hXN c.hKX c.hKI
  have hFle := Lemma113d.le_sup_of_elemAbelian_card_ge hC113 e0 c.hQp c.hQK c.hcyc hU hU27 hFQ hF
    (by rw [hF81])
  rw [c.hEeq]
  exact Lemma113d.eq_sup_zpowers_of_le c.hQ c.hQ1 c.hXN c.hKX ⟨e0⟩ c.hcyc c.hKe c.he3 c.he1
    c.heQ hF hF81 hFle

theorem E_le_P (c : Ctx E A e K Q) : E ≤ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K := by
  rw [c.hEeq]
  exact sup_le_sup_left (Subgroup.zpowers_le.2 c.e_mem_centBar) _

theorem sylow_centralizer (c : Ctx E A e K Q) :
    IsSylowIn 3 (Subgroup.centralizer (E : Set G)) ((Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPeq := c.inf_centralizer_eq
  have hPQ : (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K ≤ Q := hPeq ▸ inf_le_left
  have hPC : (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K ≤ Subgroup.centralizer (E : Set G) :=
    hPeq ▸ inf_le_right
  refine ⟨hPC, c.hQp.to_le hPQ, ?_⟩
  intro R' hR'C hR'p hPR'
  have hR'X : R' ≤ Cg e := by
    intro x hx
    exact Subgroup.mem_centralizer_iff.2 (fun y hy => by
      rw [Set.mem_singleton_iff.1 hy]
      exact Subgroup.mem_centralizer_iff.1 (hR'C hx) e c.heE)
  obtain ⟨c0, -, hc0⟩ := Lemma113b.exists_conj_mem_of_isSylowIn c.hQ hR'X hR'p
  have hE'Q : E.map (MulAut.conj c0).toMonoidHom ≤ Q := by
    rintro _ ⟨x, hx, rfl⟩
    exact hc0 x (hPR' (c.E_le_P hx))
  have hE'el : IsElemAbelian 3 (E.map (MulAut.conj c0).toMonoidHom) :=
    Lemma113d.isElemAbelian_map_any _ c.hEel
  have hE'card : Nat.card ↥(E.map (MulAut.conj c0).toMonoidHom) = 81 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c0).injective, c.hEcard]
    norm_num
  have hE'E := c.eq_of_elemAbelian_card81 hE'Q hE'el hE'card
  have hmap : R'.map (MulAut.conj c0).toMonoidHom ≤
      (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K := by
    rintro _ ⟨s, hs, rfl⟩
    have hsQ : c0 * s * c0⁻¹ ∈ Q := hc0 s hs
    have hsC : c0 * s * c0⁻¹ ∈ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : y ∈ E.map (MulAut.conj c0).toMonoidHom := by rw [hE'E]; exact hy
      obtain ⟨y', hy'E, rfl⟩ := hy'
      have hsy : s * y' = y' * s := (Subgroup.mem_centralizer_iff.1 (hR'C hs) y' hy'E).symm
      show (MulAut.conj c0 y') * (c0 * s * c0⁻¹) = (c0 * s * c0⁻¹) * (MulAut.conj c0 y')
      simp only [MulAut.conj_apply]
      calc c0 * y' * c0⁻¹ * (c0 * s * c0⁻¹) = c0 * (y' * s) * c0⁻¹ := by group
        _ = c0 * (s * y') * c0⁻¹ := by rw [hsy]
        _ = c0 * s * c0⁻¹ * (c0 * y' * c0⁻¹) := by group
    rw [← hPeq]
    exact ⟨hsQ, hsC⟩
  have hcard : Nat.card ↥R' ≤ Nat.card ↥((Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K) := by
    have hcm : Nat.card ↥(R'.map (MulAut.conj c0).toMonoidHom) = Nat.card ↥R' :=
      Subgroup.card_map_of_injective (MulAut.conj c0).injective
    rw [← hcm]
    exact Subgroup.card_le_of_le hmap
  exact (Subgroup.eq_of_le_of_card_ge hPR' hcard).symm

theorem exists_cube_eq_e (c : Ctx E A e K Q) (hgt : 3 < Nat.card ↥(centBar 3 Q K)) :
    ∃ γ ∈ centBar 3 Q K, γ ^ 3 = e := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hC3 : IsPGroup 3 ↥(centBar 3 Q K) := c.hQp.to_le c.centBar_le
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).1 hC3
  have hk2 : 2 ≤ k := by
    by_contra h
    have h1 : k ≤ 1 := by omega
    have h2 : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
    norm_num at h2
    omega
  haveI := c.hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(centBar 3 Q K))
  have hord : orderOf g = 3 ^ k := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hk]
  set g0 : G := (g : G) with hg0
  have hg0C : g0 ∈ centBar 3 Q K := g.2
  have hord0 : orderOf g0 = 3 ^ k := (Subgroup.orderOf_coe g).trans hord
  have hk1 : 3 ^ (k - 1) ∣ orderOf g0 := by
    rw [hord0]; exact pow_dvd_pow 3 (by omega)
  have ht3 : orderOf (g0 ^ 3 ^ (k - 1)) = 3 := by
    rw [orderOf_pow_of_dvd (by positivity) hk1, hord0, Nat.pow_div (by omega) (by norm_num)]
    have : k - (k - 1) = 1 := by omega
    rw [this]
  have htC : g0 ^ 3 ^ (k - 1) ∈ centBar 3 Q K := (centBar 3 Q K).pow_mem hg0C _
  have htpow : (g0 ^ 3 ^ (k - 1)) ^ 3 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, ht3]
  have hte : g0 ^ 3 ^ (k - 1) ∈ Subgroup.zpowers e :=
    Lemma113d.mem_zpowers_of_pow_three_of_cyclic c.hcyc c.e_mem_centBar c.he3 c.he1 htC htpow
  have hcardz : Nat.card ↥(Subgroup.zpowers (g0 ^ 3 ^ (k - 1))) = 3 := by
    rw [Nat.card_zpowers, ht3]
  have hcardze : Nat.card ↥(Subgroup.zpowers e) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime c.he3 c.he1]
  have heq : Subgroup.zpowers (g0 ^ 3 ^ (k - 1)) = Subgroup.zpowers e :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hte) (by rw [hcardz, hcardze])
  have hemem : e ∈ Subgroup.zpowers (g0 ^ 3 ^ (k - 1)) := by
    rw [heq]; exact Subgroup.mem_zpowers e
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hemem
  refine ⟨(g0 ^ 3 ^ (k - 2)) ^ j, (centBar 3 Q K).zpow_mem ((centBar 3 Q K).pow_mem hg0C _) _, ?_⟩
  have h1 : ((g0 ^ 3 ^ (k - 2)) ^ j) ^ 3 = ((g0 ^ 3 ^ (k - 2)) ^ 3) ^ j := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  have h2 : (g0 ^ 3 ^ (k - 2)) ^ 3 = g0 ^ 3 ^ (k - 1) := by
    rw [← pow_mul, ← pow_succ]
    congr 2
    omega
  rw [h1, h2, hj]

theorem centBar_card_le_three (c : Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)) :
    Nat.card ↥(centBar 3 Q K) ≤ 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hgt
  push Not at hgt
  obtain ⟨γ, hγ, hγe⟩ := c.exists_cube_eq_e hgt
  apply hB
  intro n hn
  set P : Subgroup G := (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K with hPdef
  have hP : IsSylowIn 3 (Subgroup.centralizer (E : Set G)) P := c.sylow_centralizer
  have hPQ : P ≤ Q := sup_le inf_le_left c.centBar_le
  have hn' : n⁻¹ ∈ Subgroup.normalizer (E : Set G) := inv_mem hn
  have hPn : P.map (MulAut.conj n).toMonoidHom ≤ Subgroup.centralizer (E : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : n⁻¹ * y * n ∈ E := by
      have := (Subgroup.mem_normalizer_iff.1 hn' y).1 hy
      simpa using this
    have hxc : (n⁻¹ * y * n) * x = x * (n⁻¹ * y * n) :=
      Subgroup.mem_centralizer_iff.1 (hP.1 hx) _ hy'
    show y * (n * x * n⁻¹) = (n * x * n⁻¹) * y
    calc y * (n * x * n⁻¹) = n * ((n⁻¹ * y * n) * x) * n⁻¹ := by group
      _ = n * (x * (n⁻¹ * y * n)) * n⁻¹ := by rw [hxc]
      _ = n * x * n⁻¹ * y := by group
  have hPnp : IsPGroup 3 ↥(P.map (MulAut.conj n).toMonoidHom) := hP.2.1.map _
  obtain ⟨c1, hc1C, hc1⟩ := Lemma113b.exists_conj_mem_of_isSylowIn hP hPn hPnp
  have hm : ∀ x ∈ P, (c1 * n) * x * (c1 * n)⁻¹ ∈ P := by
    intro x hx
    have := hc1 (n * x * n⁻¹) (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
    have e1 : (c1 * n) * x * (c1 * n)⁻¹ = c1 * (n * x * n⁻¹) * c1⁻¹ := by group
    rw [e1]
    exact this
  have hγP : γ ∈ P := hPdef ▸ Subgroup.mem_sup_right hγ
  have hmγ := hm γ hγP
  have hcent : (Q ⊓ K : Subgroup G) ≤ Subgroup.centralizer (centBar 3 Q K : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact c.comm_centBar_Q0 hu ha
  obtain ⟨a, ha, u, hu, hau⟩ := exists_mul_of_mem_sup hcent hmγ
  have hcomm : a * u = u * a := (c.comm_centBar_Q0 hu ha).symm
  have ha3 : a ^ 3 = 1 := c.Q0_elemAbelian.2 a ha
  have hmeq : (c1 * n) * e * (c1 * n)⁻¹ = u ^ 3 := by
    have e1 : (c1 * n) * e * (c1 * n)⁻¹ = ((c1 * n) * γ * (c1 * n)⁻¹) ^ 3 := by
      rw [← hγe]
      simp only [pow_three]
      group
    rw [e1, hau, (show Commute a u from hcomm).mul_pow, ha3, one_mul]
  have hu3 : u ^ 3 ∈ centBar 3 Q K := (centBar 3 Q K).pow_mem hu 3
  have h1 : ((c1 * n) * e * (c1 * n)⁻¹) ^ 3 = 1 := by
    have : ((c1 * n) * e * (c1 * n)⁻¹) ^ 3 = (c1 * n) * e ^ 3 * (c1 * n)⁻¹ := by
      simp only [pow_three]; group
    rw [this, c.he3]; group
  have hmeC : (c1 * n) * e * (c1 * n)⁻¹ ∈ Subgroup.zpowers e := by
    rw [hmeq]
    apply Lemma113d.mem_zpowers_of_pow_three_of_cyclic c.hcyc c.e_mem_centBar c.he3 c.he1 hu3
    rw [← hmeq]
    exact h1
  have hmN : c1 * n ∈ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
    apply mem_normalizer_of_conj_le
    intro k hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have e1 : (c1 * n) * e ^ j * (c1 * n)⁻¹ = ((c1 * n) * e * (c1 * n)⁻¹) ^ j :=
      conj_zpow.symm
    rw [e1]
    exact (Subgroup.zpowers e).zpow_mem hmeC j
  have hc1N : c1 ∈ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
    apply Lemma113b.centralizer_le_normalizer_zpowers' e
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact Subgroup.mem_centralizer_iff.1 hc1C e c.heE
  have : n = c1⁻¹ * (c1 * n) := by group
  rw [this]
  exact (Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)).mul_mem
    ((Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)).inv_mem hc1N) hmN

theorem centBar_eq_zpowers (c : Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)) :
    centBar 3 Q K = Subgroup.zpowers e := by
  have hle : Subgroup.zpowers e ≤ centBar 3 Q K := Subgroup.zpowers_le.2 c.e_mem_centBar
  have hcard : Nat.card ↥(centBar 3 Q K) ≤ Nat.card ↥(Subgroup.zpowers e) := by
    rw [Nat.card_zpowers, orderOf_eq_prime c.he3 c.he1]
    exact c.centBar_card_le_three hB
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem sylow_centralizer_E (c : Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)) :
    IsSylowIn 3 (Subgroup.centralizer (E : Set G)) E := by
  have h := c.sylow_centralizer
  rw [c.centBar_eq_zpowers hB, ← c.hEeq] at h
  exact h

end Ctx

section Lift

theorem three_group_inf_eq_bot {H : Type} [Group H] [Finite H] {O P : Subgroup H}
    (hO : ¬ 3 ∣ Nat.card O) (hP : IsPGroup 3 ↥P) : O ⊓ P = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 ↥(O ⊓ P) := hP.to_le inf_le_right
  obtain ⟨t, ht⟩ := (IsPGroup.iff_card (p := 3)).1 hp
  have hdvd : Nat.card ↥(O ⊓ P) ∣ Nat.card ↥O := Subgroup.card_dvd_of_le inf_le_left
  rw [ht] at hdvd
  have ht0 : t = 0 := by
    by_contra h
    exact hO ((dvd_pow_self 3 h).trans hdvd)
  rw [ht0, pow_zero] at ht
  exact Subgroup.card_eq_one.1 ht

theorem card_map_mk_of_isPGroup {H : Type} [Group H] [Finite H] {O : Subgroup H} [O.Normal]
    (hO : ¬ 3 ∣ Nat.card O) {R : Subgroup H} (hR : IsPGroup 3 ↥R) :
    Nat.card ↥(R.map (QuotientGroup.mk' O)) = Nat.card ↥R := by
  have hinj : Function.Injective ((QuotientGroup.mk' O).comp R.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : (QuotientGroup.mk' O) (x : H) = 1 := hx
    have hxO : (x : H) ∈ O := (QuotientGroup.eq_one_iff (x : H)).1 hx1
    have hmem : (x : H) ∈ O ⊓ R := ⟨hxO, x.2⟩
    rw [three_group_inf_eq_bot hO hR, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hrange : ((QuotientGroup.mk' O).comp R.subtype).range = R.map (QuotientGroup.mk' O) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem exists_mul_mem_normalizer_of_map {H : Type} [Group H] [Finite H] {O : Subgroup H}
    [O.Normal] (hO : ¬ 3 ∣ Nat.card O) {P : Subgroup H} (hP : IsPGroup 3 ↥P) {k : H}
    (hk : (QuotientGroup.mk k : H ⧸ O) ∈
      Subgroup.normalizer ((P.map (QuotientGroup.mk' O) : Subgroup (H ⧸ O)) : Set (H ⧸ O))) :
    ∃ p ∈ (P.map (QuotientGroup.mk' O)).comap (QuotientGroup.mk' O),
      p * k ∈ Subgroup.normalizer (P : Set H) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' O with hπ
  set Ŵ : Subgroup (H ⧸ O) := P.map π with hŴ
  set P' : Subgroup H := Ŵ.comap π with hP'
  have hPP' : P ≤ P' := fun x hx => Subgroup.mem_map_of_mem π hx
  have hsyl : IsSylowIn 3 P' P := by
    refine ⟨hPP', hP, fun R' hR'P' hR'p hPR' => ?_⟩
    have h1 : Nat.card ↥(R'.map π) ≤ Nat.card ↥Ŵ :=
      Subgroup.card_le_of_le (fun y ⟨x, hx, hxy⟩ => hxy ▸ hR'P' hx)
    rw [card_map_mk_of_isPGroup hO hR'p, hŴ, card_map_mk_of_isPGroup hO hP] at h1
    exact (Subgroup.eq_of_le_of_card_ge hPR' h1).symm
  have hkP' : ∀ y : H, y ∈ P' ↔ k * y * k⁻¹ ∈ P' := by
    intro y
    have := Subgroup.mem_normalizer_iff.1 hk (π y)
    simp only [hP', Subgroup.mem_comap, map_mul, map_inv]
    exact this
  have hPk : P.map (MulAut.conj k).toMonoidHom ≤ P' := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hkP' x).1 (hPP' hx)
  have hPkp : IsPGroup 3 ↥(P.map (MulAut.conj k).toMonoidHom) := hP.map _
  obtain ⟨p, hpP', hp⟩ := Lemma113b.exists_conj_mem_of_isSylowIn hsyl hPk hPkp
  refine ⟨p, hpP', ?_⟩
  apply mem_normalizer_of_conj_le
  intro x hx
  have := hp (k * x * k⁻¹) (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
  have e1 : p * k * x * (p * k)⁻¹ = p * (k * x * k⁻¹) * p⁻¹ := by group
  rw [e1]
  exact this

open scoped Classical in
noncomputable def pi0 (K : Subgroup G) (q : G) : barOf 3 K :=
  if hq : q ∈ K then (QuotientGroup.mk ⟨q, hq⟩ : barOf 3 K) else 1

theorem pi0_of_mem {K : Subgroup G} {q : G} (hq : q ∈ K) :
    pi0 K q = (QuotientGroup.mk ⟨q, hq⟩ : barOf 3 K) := by
  simp [pi0, hq]

theorem pi0_mul {K : Subgroup G} {a b : G} (ha : a ∈ K) (hb : b ∈ K) :
    pi0 K (a * b) = pi0 K a * pi0 K b := by
  rw [pi0_of_mem (K.mul_mem ha hb), pi0_of_mem ha, pi0_of_mem hb]
  rfl

theorem pi0_inv {K : Subgroup G} {a : G} (ha : a ∈ K) : pi0 K a⁻¹ = (pi0 K a)⁻¹ := by
  rw [pi0_of_mem (K.inv_mem ha), pi0_of_mem ha]
  rfl

noncomputable def W0 (K Q : Subgroup G) : Subgroup (barOf 3 K) :=
  ((Q ⊓ K : Subgroup G).subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K))

theorem mem_W0_iff {K Q : Subgroup G} {w : barOf 3 K} :
    w ∈ W0 K Q ↔ ∃ q ∈ (Q ⊓ K : Subgroup G), pi0 K q = w := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ (Q ⊓ K : Subgroup G) := Subgroup.mem_subgroupOf.1 hx
    exact ⟨x, hx', by rw [pi0_of_mem x.2]; rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨q, hq.2⟩, Subgroup.mem_subgroupOf.2 hq, by rw [pi0_of_mem hq.2]; rfl⟩

theorem pi0_mem_W0 {K Q : Subgroup G} {q : G} (hq : q ∈ (Q ⊓ K : Subgroup G)) :
    pi0 K q ∈ W0 K Q := mem_W0_iff.2 ⟨q, hq, rfl⟩

section Counting

theorem ncard_orbit_modEq_one {M X : Type} [Group M] [MulAction M X] {S₀ : X}
    [Finite (MulAction.orbit M S₀)] {p : ℕ} [Fact p.Prime] (x : M) (hx : ∃ a : ℕ, x ^ p ^ a = 1)
    (hfix₀ : x • S₀ = S₀) (hfix : ∀ S ∈ MulAction.orbit M S₀, x • S = S → S = S₀) :
    (MulAction.orbit M S₀).ncard ≡ 1 [MOD p] := by
  classical
  obtain ⟨a, ha⟩ := hx
  have hP : IsPGroup p ↥(Subgroup.zpowers x) := by
    intro g
    refine ⟨a, ?_⟩
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 g.2
    apply Subtype.ext
    show (g : M) ^ p ^ a = 1
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]
  have hmod := IsPGroup.card_modEq_card_fixedPoints hP (MulAction.orbit M S₀)
  have hfp : MulAction.fixedPoints (↥(Subgroup.zpowers x)) (MulAction.orbit M S₀) =
      {⟨S₀, MulAction.mem_orbit_self S₀⟩} := by
    ext ⟨S, hS⟩
    rw [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro h
      have h1 := h ⟨x, Subgroup.mem_zpowers x⟩
      have h2 : x • S = S := congrArg Subtype.val h1
      exact Subtype.ext (hfix S hS h2)
    · intro h m
      have hS0 : S = S₀ := congrArg Subtype.val h
      subst hS0
      apply Subtype.ext
      show (m : M) • S = S
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 m.2
      rw [← hi]
      have : ∀ i : ℤ, x ^ i • S = S := by
        intro i
        have hx' : x ∈ MulAction.stabilizer M S := hfix₀
        exact (zpow_mem hx' i : x ^ i ∈ MulAction.stabilizer M S)
      exact this i
  rw [hfp] at hmod
  have h1 : Nat.card (↥({⟨S₀, MulAction.mem_orbit_self S₀⟩} :
      Set ↥(MulAction.orbit M S₀))) = 1 := by
    rw [Nat.card_coe_set_eq, Set.ncard_singleton]
  rw [h1, Nat.card_coe_set_eq] at hmod
  exact hmod

noncomputable scoped instance connAct (N : Subgroup G) : MulAction ↥N (Subgroup G) :=
  MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp N.subtype)

theorem connAct_mem_smul_iff (N : Subgroup G) (n : ↥N) (S : Subgroup G) (x : G) :
    x ∈ (n • S) ↔ (n : G)⁻¹ * x * n ∈ S := by
  show x ∈ (MulAut.conj (n : G)) • S ↔ _
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.conj_apply]

theorem card_eq_ncard_orbit_mul (N S₀ : Subgroup G) :
    Nat.card ↥N = (MulAction.orbit ↥N S₀).ncard *
      Nat.card ↥(N ⊓ Subgroup.normalizer (S₀ : Set G)) := by
  have h1 := MulAction.index_stabilizer ↥N S₀
  have h2 := Subgroup.card_mul_index (MulAction.stabilizer ↥N S₀)
  have h3 : Nat.card ↥(MulAction.stabilizer ↥N S₀) =
      Nat.card ↥(N ⊓ Subgroup.normalizer (S₀ : Set G)) := by
    apply Nat.card_congr
    refine
      { toFun := fun n => ⟨(n.1 : G), n.1.2, ?_⟩
        invFun := fun g => ⟨⟨g.1, g.2.1⟩, ?_⟩
        left_inv := fun n => rfl
        right_inv := fun g => rfl }
    ·
      have hn := n.2
      rw [MulAction.mem_stabilizer_iff] at hn
      show (n.1 : G) ∈ Subgroup.normalizer (S₀ : Set G)
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have h := connAct_mem_smul_iff N n.1 S₀ ((n.1 : G) * y * (n.1 : G)⁻¹)
      rw [hn] at h
      have e1 : (n.1 : G)⁻¹ * ((n.1 : G) * y * (n.1 : G)⁻¹) * (n.1 : G) = y := by group
      rw [e1] at h
      exact h.symm
    · rw [MulAction.mem_stabilizer_iff]
      ext y
      rw [connAct_mem_smul_iff]
      have := Subgroup.mem_normalizer_iff.1 g.2.2 ((g.1 : G)⁻¹ * y * g.1)
      have e1 : (g.1 : G) * ((g.1 : G)⁻¹ * y * g.1) * (g.1 : G)⁻¹ = y := by group
      rw [e1] at this
      exact this
  rw [h3, h1] at h2
  exact h2.symm.trans (mul_comm _ _)

end Counting

section IndexClaim

theorem zmod3_pow_odd (k : ZMod 3) (hk : k ≠ 0) {m : ℕ} (hm : Odd m) : k ^ m = k := by
  obtain ⟨t, rfl⟩ := hm
  have h2 : k ^ 2 = 1 := by revert k; decide
  rw [pow_succ, pow_mul, h2, one_pow, one_mul]

theorem commute_of_odd_pow_mem_normalizer {n y : G}
    (hn : n ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G)) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    {m : ℕ} (hm : Odd m) (hnm : n ^ m = 1) : Commute n y := by
  obtain ⟨k, hk, hnk⟩ := Lemma113d.conj_eq_zpow_of_mem_normalizer hn hy3 hy1
  have hpow : ∀ j : ℕ, n ^ j * y * (n ^ j)⁻¹ = y ^ (k ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : n ^ (j + 1) * y * (n ^ (j + 1))⁻¹ = n * (n ^ j * y * (n ^ j)⁻¹) * n⁻¹ := by
        rw [pow_succ']
        group
      rw [h1, ih]
      have h2 : n * y ^ (k ^ j) * n⁻¹ = (n * y * n⁻¹) ^ (k ^ j) := conj_zpow.symm
      rw [h2, hnk, ← zpow_mul, pow_succ, mul_comm (k ^ j) k]
  have hfix : y ^ (k ^ m) = y := by
    rw [← hpow, hnm]
    group
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hdvd : (orderOf y : ℤ) ∣ k ^ m - 1 := by
    apply orderOf_dvd_iff_zpow_eq_one.2
    rw [zpow_sub, zpow_one, hfix, mul_inv_cancel]
  rw [hord] at hdvd
  have hz : ((k ^ m - 1 : ℤ) : ZMod 3) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hdvd
  have hk0 : (k : ZMod 3) ≠ 0 := by
    intro h0
    exact hk ((ZMod.intCast_zmod_eq_zero_iff_dvd k 3).1 h0)
  rw [Int.cast_sub, Int.cast_one, sub_eq_zero, Int.cast_pow, zmod3_pow_odd _ hk0 hm] at hz
  have hk1 : ((3 : ℕ) : ℤ) ∣ k - 1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (k - 1) 3).1 (by rw [Int.cast_sub, Int.cast_one, hz, sub_self])
  rw [← hord] at hk1
  have hek : y ^ k = y := by
    have h1 : y ^ (k - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.1 hk1
    calc y ^ k = y ^ (k - 1 + 1) := by rw [sub_add_cancel]
      _ = y ^ (k - 1) * y := zpow_add_one y (k - 1)
      _ = y := by rw [h1, one_mul]
  have hcomm : n * y * n⁻¹ = y := by rw [hnk, hek]
  show n * y = y * n
  calc n * y = (n * y * n⁻¹) * n := by group
    _ = y * n := by rw [hcomm]

theorem connAct_smul_eq_iff (N : Subgroup G) (n : ↥N) (S : Subgroup G) :
    n • S = S ↔ (n : G) ∈ Subgroup.normalizer (S : Set G) := by
  constructor
  · intro hn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h := connAct_mem_smul_iff N n S ((n : G) * y * (n : G)⁻¹)
    rw [hn] at h
    have e1 : (n : G)⁻¹ * ((n : G) * y * (n : G)⁻¹) * (n : G) = y := by group
    rw [e1] at h
    exact h.symm
  · intro hn
    ext y
    rw [connAct_mem_smul_iff]
    have := Subgroup.mem_normalizer_iff.1 hn ((n : G)⁻¹ * y * n)
    have e1 : (n : G) * ((n : G)⁻¹ * y * (n : G)) * (n : G)⁻¹ = y := by group
    rw [e1] at this
    exact this

theorem mem_zpowers_cases {e b : G} (he3 : e ^ 3 = 1) (hb : b ∈ Subgroup.zpowers e) :
    b = 1 ∨ b = e ∨ b = e⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have e3z : e ^ (3 : ℤ) = 1 := by simpa using he3
  have hk : k = 3 * (k / 3) + k % 3 := by omega
  have hk' : e ^ k = e ^ (k % 3) := by
    conv_lhs => rw [hk]
    rw [zpow_add, zpow_mul, e3z, one_zpow, one_mul]
  rw [hk']
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
  · left; rw [h, zpow_zero]
  · right; left; rw [h, zpow_one]
  · right; right
    rw [h, zpow_two]
    apply eq_inv_of_mul_eq_one_left
    calc e * e * e = e ^ 3 := by simp only [pow_succ, pow_zero, one_mul]
      _ = 1 := he3

end IndexClaim

namespace Ctx

variable {E A : Subgroup G} {e : G} {K Q : Subgroup G}

theorem pi0_injOn (c : Ctx E A e K Q) {a b : G} (ha : a ∈ (Q ⊓ K : Subgroup G))
    (hb : b ∈ (Q ⊓ K : Subgroup G)) (h : pi0 K a = pi0 K b) : a = b := by
  have hinj := Lemma113c.quot_injective (X := K) (Q := (Q ⊓ K : Subgroup G)) inf_le_right
    (c.hQp.to_le inf_le_left)
  have := @hinj ⟨⟨a, ha.2⟩, Subgroup.mem_subgroupOf.2 ha⟩ ⟨⟨b, hb.2⟩, Subgroup.mem_subgroupOf.2 hb⟩ (by
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, QuotientGroup.mk'_apply]
    rw [← pi0_of_mem ha.2, ← pi0_of_mem hb.2]
    exact h)
  have h2 := congrArg (fun z => ((z : ↥(Subgroup.subgroupOf (Q ⊓ K) K)) : ↥K).1) this
  exact h2

theorem card_W0 (c : Ctx E A e K Q) : Nat.card ↥(W0 K Q) = 27 := by
  have hp : IsPGroup 3 ↥((Q ⊓ K : Subgroup G).subgroupOf K) :=
    Lemma113d.isPGroup_subgroupOf_inf c.hQp
  have hO : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥K) := by
    have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥K)) :=
      CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥K
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop
  unfold W0
  rw [card_map_mk_of_isPGroup hO hp,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Q ⊓ K ≤ K)).toEquiv]
  exact c.card_Q0

theorem W0_comm (c : Ctx E A e K Q) : ∀ a ∈ W0 K Q, ∀ b ∈ W0 K Q, a * b = b * a := by
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := mem_W0_iff.1 ha
  obtain ⟨y, hy, rfl⟩ := mem_W0_iff.1 hb
  rw [← pi0_mul hx.2 hy.2, ← pi0_mul hy.2 hx.2]
  have hxy : x * y = y * x :=
    congrArg Subtype.val (c.Q0_elemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  rw [hxy]

theorem exists_lift (c : Ctx E A e K Q) {t : barOf 3 K}
    (ht : t ∈ Subgroup.normalizer ((W0 K Q : Subgroup (barOf 3 K)) : Set (barOf 3 K))) :
    ∃ h ∈ K, (∀ q ∈ (Q ⊓ K : Subgroup G), h * q * h⁻¹ ∈ (Q ⊓ K : Subgroup G)) ∧
      ∃ w ∈ W0 K Q, pi0 K h = t * w := by
  have hp : IsPGroup 3 ↥((Q ⊓ K : Subgroup G).subgroupOf K) :=
    Lemma113d.isPGroup_subgroupOf_inf c.hQp
  have hO : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥K) := by
    have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥K)) :=
      CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥K
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop
  obtain ⟨k, hkt⟩ := QuotientGroup.mk_surjective t
  have hkn : (QuotientGroup.mk k : barOf 3 K) ∈
      Subgroup.normalizer ((W0 K Q : Subgroup (barOf 3 K)) : Set (barOf 3 K)) := by
    rw [hkt]; exact ht
  obtain ⟨p, hp1, hp2⟩ := exists_mul_mem_normalizer_of_map hO hp hkn
  refine ⟨((p * k : ↥K) : G), (p * k).2, ?_, ?_⟩
  · intro q hq
    have hz : (⟨q, hq.2⟩ : ↥K) ∈ (Q ⊓ K : Subgroup G).subgroupOf K := Subgroup.mem_subgroupOf.2 hq
    have := (Subgroup.mem_normalizer_iff.1 hp2 ⟨q, hq.2⟩).1 hz
    exact Subgroup.mem_subgroupOf.1 this
  · have hpW : (QuotientGroup.mk p : barOf 3 K) ∈ W0 K Q := hp1
    refine ⟨t⁻¹ * (QuotientGroup.mk p) * t, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (inv_mem ht) (QuotientGroup.mk p)).1 hpW
      simpa using this
    · rw [pi0_of_mem (p * k).2]
      show (QuotientGroup.mk (p * k) : barOf 3 K) = _
      rw [QuotientGroup.mk_mul, hkt]
      group

theorem lift_pow (c : Ctx E A e K Q) {t : barOf 3 K} {h : G} (hhK : h ∈ K)
    (hn : ∀ q ∈ (Q ⊓ K : Subgroup G), h * q * h⁻¹ ∈ (Q ⊓ K : Subgroup G)) {w : barOf 3 K}
    (hw : w ∈ W0 K Q) (hh : pi0 K h = t * w) (j : ℕ) :
    ∀ q ∈ (Q ⊓ K : Subgroup G), h ^ j * q * (h ^ j)⁻¹ ∈ (Q ⊓ K : Subgroup G) ∧
      pi0 K (h ^ j * q * (h ^ j)⁻¹) = t ^ j * pi0 K q * (t ^ j)⁻¹ := by
  induction j with
  | zero =>
    intro q hq
    refine ⟨by simpa using hq, ?_⟩
    simp
  | succ j ih =>
    intro q hq
    obtain ⟨hqj, hpi⟩ := ih q hq
    have hqjK : h ^ j * q * (h ^ j)⁻¹ ∈ K := hqj.2
    have e1 : h ^ (j + 1) * q * (h ^ (j + 1))⁻¹ = h * (h ^ j * q * (h ^ j)⁻¹) * h⁻¹ := by
      rw [pow_succ']; group
    rw [e1]
    refine ⟨hn _ hqj, ?_⟩
    rw [pi0_mul (K.mul_mem hhK hqjK) (K.inv_mem hhK), pi0_mul hhK hqjK, pi0_inv hhK, hh, hpi]
    have hW : pi0 K (h ^ j * q * (h ^ j)⁻¹) ∈ W0 K Q := pi0_mem_W0 hqj
    rw [hpi] at hW
    have hcomm := c.W0_comm w hw _ hW
    calc t * w * (t ^ j * pi0 K q * (t ^ j)⁻¹) * (t * w)⁻¹
        = t * (w * (t ^ j * pi0 K q * (t ^ j)⁻¹)) * w⁻¹ * t⁻¹ := by group
      _ = t * ((t ^ j * pi0 K q * (t ^ j)⁻¹) * w) * w⁻¹ * t⁻¹ := by rw [hcomm]
      _ = t ^ (j + 1) * pi0 K q * (t ^ (j + 1))⁻¹ := by
        rw [pow_succ']; group

theorem exists_x (c : Ctx E A e K Q) :
    ∃ x : G, x ∈ K ∧ (∀ q ∈ (Q ⊓ K : Subgroup G), x * q * x⁻¹ ∈ (Q ⊓ K : Subgroup G)) ∧
      (∃ a : ℕ, x ^ 13 ^ a = 1) ∧
      ∀ q ∈ (Q ⊓ K : Subgroup G), x * q * x⁻¹ = q → q = 1 := by
  classical
  obtain ⟨e0⟩ := c.hKI
  obtain ⟨t, htN, ht13, htfree⟩ := L2.exists_torus_element e0 (W0 K Q) c.card_W0
  obtain ⟨h, hhK, hhn, w, hw, hh⟩ := c.exists_lift (inv_mem htN)
  have hpow := c.lift_pow hhK hhn hw hh
  have h13 : ∀ q ∈ (Q ⊓ K : Subgroup G), h ^ 13 * q * (h ^ 13)⁻¹ = q := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := hpow 13 q hq
    apply c.pi0_injOn hq1 hq
    rw [hq2]
    have := ht13 (pi0 K q) (pi0_mem_W0 hq)
    simp only [inv_pow, inv_inv]
    exact this
  have h13s : ∀ s : ℕ, ∀ q ∈ (Q ⊓ K : Subgroup G), h ^ (13 * s) * q * (h ^ (13 * s))⁻¹ = q := by
    intro s
    induction s with
    | zero => intro q _; simp
    | succ s ih =>
      intro q hq
      have e1 : h ^ (13 * (s + 1)) * q * (h ^ (13 * (s + 1)))⁻¹ =
          h ^ 13 * (h ^ (13 * s) * q * (h ^ (13 * s))⁻¹) * (h ^ 13)⁻¹ := by
        rw [show 13 * (s + 1) = 13 + 13 * s by ring, pow_add]; group
      rw [e1, ih q hq]
      exact h13 q hq
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos h).ne' 13 (by norm_num)
  have hordh : orderOf h = 13 ^ a * b := hab
  refine ⟨h ^ b, K.pow_mem hhK b, fun q hq => (hpow b q hq).1, ⟨a, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, ← hordh, pow_orderOf_eq_one]
  · intro q hq hfix
    have hr0 : b % 13 ≠ 0 := fun h0 => hb (Nat.dvd_of_mod_eq_zero h0)
    have hrlt : b % 13 < 13 := Nat.mod_lt _ (by norm_num)
    have hb' : b = 13 * (b / 13) + b % 13 := (Nat.div_add_mod b 13).symm
    obtain ⟨hq1, hq2⟩ := hpow (b % 13) q hq
    have e1 : h ^ b * q * (h ^ b)⁻¹ =
        h ^ (b % 13) * (h ^ (13 * (b / 13)) * q * (h ^ (13 * (b / 13)))⁻¹) * (h ^ (b % 13))⁻¹ := by
      conv_lhs => rw [hb', pow_add]
      group
    rw [e1, h13s _ q hq] at hfix
    have hpi := congrArg (pi0 K) hfix
    rw [hq2] at hpi
    have hfree := htfree (b % 13) (Nat.pos_of_ne_zero hr0) hrlt (pi0 K q) (pi0_mem_W0 hq) (by
      rw [← inv_pow] at hpi
      simpa [inv_pow] using hpi)
    have h1 : pi0 K 1 = 1 := by
      rw [pi0_of_mem K.one_mem]
      exact QuotientGroup.mk_one _
    apply c.pi0_injOn hq (one_mem _)
    rw [hfree, h1]

theorem pi0_one {K : Subgroup G} : pi0 K 1 = 1 := by
  rw [pi0_of_mem K.one_mem]
  exact QuotientGroup.mk_one _

theorem card_Q_ge (c : Ctx E A e K Q) : 3 ^ 5 ≤ Nat.card ↥Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEA_le : E ⊔ A ≤ Q := sup_le c.hEQ c.hAQ
  have hne : E ⊔ A ≠ E := fun h => c.hAnE (h ▸ le_sup_right)
  have hsup3 : IsPGroup 3 ↥(E ⊔ A) := c.hQp.to_le hEA_le
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 3)).1 hsup3
  have hle : Nat.card ↥E ≤ Nat.card ↥(E ⊔ A) := Subgroup.card_le_of_le le_sup_left
  have hne' : Nat.card ↥E ≠ Nat.card ↥(E ⊔ A) := by
    intro hc
    apply hne
    exact (Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq hc.symm)).symm
  have hlt : 3 ^ 4 < 3 ^ j := by
    rw [← c.hEcard, ← hj]
    exact lt_of_le_of_ne hle hne'
  have h4 : 4 < j := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
  calc 3 ^ 5 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = Nat.card ↥(E ⊔ A) := hj.symm
    _ ≤ Nat.card ↥Q := Subgroup.card_le_of_le hEA_le

theorem card_Q (c : Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)) :
    Nat.card ↥Q = 3 ^ 5 := by
  obtain ⟨e0⟩ := c.hKI
  have h1 := Lemma113d.card_le_81_mul_centBar e0 c.hQp c.hQK
  have h2 := c.centBar_card_le_three hB
  have h3 := c.card_Q_ge
  have h4 : 81 * Nat.card ↥(centBar 3 Q K) ≤ 81 * 3 := Nat.mul_le_mul_left 81 h2
  have h5 : Nat.card ↥Q ≤ 3 ^ 5 := by norm_num at h4 ⊢; omega
  exact le_antisymm h5 h3

theorem Q0_normal_in_Q (c : Ctx E A e K Q) {q : G} (hq : q ∈ Q) {y : G} :
    y ∈ (Q ⊓ K : Subgroup G) ↔ q * y * q⁻¹ ∈ (Q ⊓ K : Subgroup G) :=
  Subgroup.mem_normalizer_iff.1 (Lemma113d.mem_normalizer_inf hq (c.hQK hq)) y

theorem comm_mem_Q0 (c : Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)) :
    ∀ a ∈ Q, ∀ b ∈ Q, a * b * a⁻¹ * b⁻¹ ∈ (Q ⊓ K : Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N0 : Subgroup ↥Q := (Q ⊓ K : Subgroup G).subgroupOf Q with hN0
  haveI : N0.Normal := ⟨fun n hn g => by
    rw [hN0, Subgroup.mem_subgroupOf] at hn ⊢
    have := (c.Q0_normal_in_Q g.2).1 hn
    simpa using this⟩
  have hcardN0 : Nat.card ↥N0 = 27 := by
    rw [hN0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Q ⊓ K ≤ Q)).toEquiv]
    exact c.card_Q0
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup N0
  rw [hcardN0, c.card_Q hB] at hsplit
  have hq9 : Nat.card (↥Q ⧸ N0) = 3 ^ 2 := by
    have : Nat.card (↥Q ⧸ N0) * 27 = 3 ^ 5 := hsplit.symm
    omega
  haveI := IsPGroup.isMulCommutative_of_card_eq_prime_sq hq9
  intro a ha b hb
  have hcomm : (QuotientGroup.mk (⟨a, ha⟩ * ⟨b, hb⟩ : ↥Q) : ↥Q ⧸ N0) =
      QuotientGroup.mk (⟨b, hb⟩ * ⟨a, ha⟩ : ↥Q) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact IsMulCommutative.is_comm.comm (QuotientGroup.mk (⟨a, ha⟩ : ↥Q) : ↥Q ⧸ N0)
      (QuotientGroup.mk (⟨b, hb⟩ : ↥Q))
  have h := Lemma113d.mul_inv_mem_of_mk_eq hcomm
  have h' : (⟨a, ha⟩ * ⟨b, hb⟩ * (⟨b, hb⟩ * ⟨a, ha⟩)⁻¹ : ↥Q) ∈ N0 := h
  rw [hN0, Subgroup.mem_subgroupOf] at h'
  simpa [mul_assoc] using h'

theorem commutator_le_Q0 (c : Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)) :
    ⁅Q, Q⁆ ≤ (Q ⊓ K : Subgroup G) :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact c.comm_mem_Q0 hB a ha b hb

theorem e_not_mem_commutator (c : Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)) : e ∉ ⁅Q, Q⁆ := by
  intro h
  have heQ0 : e ∈ (Q ⊓ K : Subgroup G) := c.commutator_le_Q0 hB h
  have hmem : e ∈ (Q ⊓ K : Subgroup G) ⊓ centBar 3 Q K := ⟨heQ0, c.e_mem_centBar⟩
  rw [c.Q0_inf_centBar, Subgroup.mem_bot] at hmem
  exact c.he1 hmem

theorem pi0_ne_one (c : Ctx E A e K Q) {y : G} (hy : y ∈ (Q ⊓ K : Subgroup G)) (hy1 : y ≠ 1) :
    pi0 K y ≠ 1 := by
  intro h
  exact hy1 (c.pi0_injOn hy (one_mem _) (h.trans pi0_one.symm))

theorem exists_trans (c : Ctx E A e K Q) {y z : G} (hy : y ∈ (Q ⊓ K : Subgroup G))
    (hz : z ∈ (Q ⊓ K : Subgroup G)) (hy1 : y ≠ 1) (hz1 : z ≠ 1) :
    ∃ n ∈ K, (∀ q ∈ (Q ⊓ K : Subgroup G), n * q * n⁻¹ ∈ (Q ⊓ K : Subgroup G)) ∧
      (n * y * n⁻¹ = z ∨ n * y * n⁻¹ = z⁻¹) := by
  obtain ⟨e0⟩ := c.hKI
  obtain ⟨t, htN, ht⟩ := L2.exists_normalizer_conj_subgroup e0 (W0 K Q) c.card_W0
    (pi0_mem_W0 hy) (pi0_mem_W0 hz) (c.pi0_ne_one hy hy1) (c.pi0_ne_one hz hz1)
  obtain ⟨h, hhK, hhn, w, hw, hh⟩ := c.exists_lift htN
  refine ⟨h, hhK, hhn, ?_⟩
  have hyh : h * y * h⁻¹ ∈ (Q ⊓ K : Subgroup G) := hhn y hy
  have hpi : pi0 K (h * y * h⁻¹) = t * pi0 K y * t⁻¹ := by
    rw [pi0_mul (K.mul_mem hhK hy.2) (K.inv_mem hhK), pi0_mul hhK hy.2, pi0_inv hhK, hh]
    have hcomm := c.W0_comm w hw _ (pi0_mem_W0 hy)
    calc t * w * pi0 K y * (t * w)⁻¹ = t * (w * pi0 K y) * w⁻¹ * t⁻¹ := by group
      _ = t * (pi0 K y * w) * w⁻¹ * t⁻¹ := by rw [hcomm]
      _ = t * pi0 K y * t⁻¹ := by group
  rcases ht with ht | ht
  · left
    apply c.pi0_injOn hyh hz
    rw [hpi, ht]
  · right
    apply c.pi0_injOn hyh ((Q ⊓ K : Subgroup G).inv_mem hz)
    rw [hpi, ht, pi0_inv hz.2]

theorem comm_Q0_Q_le (c : Ctx E A e K Q) : ⁅(Q ⊓ K : Subgroup G), Q⁆ ≤ (Q ⊓ K : Subgroup G) :=
  Subgroup.commutator_le.2 fun d hd q hq => by
    rw [commutatorElement_def]
    have h1 : q * d⁻¹ * q⁻¹ ∈ (Q ⊓ K : Subgroup G) :=
      (c.Q0_normal_in_Q hq).1 ((Q ⊓ K : Subgroup G).inv_mem hd)
    have := (Q ⊓ K : Subgroup G).mul_mem hd h1
    simpa [mul_assoc] using this

theorem conj_mem_comm_Q0_Q (c : Ctx E A e K Q) {q : G} (hq : q ∈ Q) {w : G}
    (hw : w ∈ ⁅(Q ⊓ K : Subgroup G), Q⁆) : q * w * q⁻¹ ∈ ⁅(Q ⊓ K : Subgroup G), Q⁆ := by
  have h1 : (Q ⊓ K : Subgroup G).map (MulAut.conj q).toMonoidHom = (Q ⊓ K : Subgroup G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Lemma113d.mem_normalizer_inf hq (c.hQK hq))
  have h2 : Q.map (MulAut.conj q).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hq)
  have h3 := Subgroup.map_commutator (H₁ := (Q ⊓ K : Subgroup G)) (H₂ := Q)
    (MulAut.conj q).toMonoidHom
  rw [h1, h2] at h3
  have : (MulAut.conj q).toMonoidHom w ∈ ⁅(Q ⊓ K : Subgroup G), Q⁆.map (MulAut.conj q).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hw
  rw [h3] at this
  simpa [MulAut.conj_apply] using this

theorem exists_z0 (c : Ctx E A e K Q) :
    ∃ z ∈ ⁅(Q ⊓ K : Subgroup G), Q⁆, z ^ 3 = 1 ∧ z ≠ 1 ∧ ∀ q ∈ Q, q * z = z * q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPQ : ⁅(Q ⊓ K : Subgroup G), Q⁆ ≤ Q := fun w hw => (c.comm_Q0_Q_le hw).1
  have hbot : ⁅(Q ⊓ K : Subgroup G), Q⁆ ≠ ⊥ := by
    obtain ⟨x, hxA, hxN⟩ := Lemma113d.exists_mem_not_mem_sup c.hQ c.hQ1 c.hXN c.hKX c.hKI
      c.hcyc c.hKe c.he3 c.he1 c.heQ c.hAmax c.hAel (by rw [c.hAcard]; norm_num)
    have hxQ : x ∈ Q := c.hAQ hxA
    have hxC : x ∉ Subgroup.centralizer (E : Set G) := by
      intro hxC
      apply hxN
      rw [← c.inf_centralizer_eq]
      exact ⟨hxQ, hxC⟩
    obtain ⟨d, hd, hdx⟩ : ∃ d ∈ (Q ⊓ K : Subgroup G), d * x ≠ x * d := by
      by_contra hcon
      push Not at hcon
      apply hxC
      have hle : E ≤ Subgroup.centralizer ({x} : Set G) := by
        rw [c.hEeq]
        apply sup_le
        · intro q hq
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          rw [Set.mem_singleton_iff.1 hw]
          exact (hcon q hq).symm
        · apply Subgroup.zpowers_le.2
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          rw [Set.mem_singleton_iff.1 hw]
          exact (c.hQe x hxQ).symm
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.1 (hle hy) x (Set.mem_singleton x)).symm
    have hmem : ⁅d, x⁆ ∈ ⁅(Q ⊓ K : Subgroup G), Q⁆ := Subgroup.commutator_mem_commutator hd hxQ
    intro hP
    rw [hP, Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hmem
    exact hdx (by simpa [mul_assoc] using hmem)
  exact Lemma113c.exists_central_order_three c.hQp hPQ (fun q hq w hw => c.conj_mem_comm_Q0_Q hq hw)
    hbot

theorem not_conj_e_into_Q0 (c : Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)) (g : G)
    (hg : g * e * g⁻¹ ∈ (Q ⊓ K : Subgroup G)) : False := by
  obtain ⟨z0, hz0P, hz03, hz01, hz0c⟩ := c.exists_z0
  have hz0Q0 : z0 ∈ (Q ⊓ K : Subgroup G) := c.comm_Q0_Q_le hz0P
  have hy1 : g * e * g⁻¹ ≠ 1 := by
    intro h
    apply c.he1
    calc e = g⁻¹ * (g * e * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  obtain ⟨n1, hn1K, hn1N, hn1⟩ := c.exists_trans hg hz0Q0 hy1 hz01
  have hz0inv : z0⁻¹ ∈ ⁅(Q ⊓ K : Subgroup G), Q⁆ := inv_mem hz0P
  obtain ⟨z', hz'P, hz'c, hmz⟩ : ∃ z' ∈ ⁅(Q ⊓ K : Subgroup G), Q⁆, (∀ q ∈ Q, q * z' = z' * q) ∧
      (n1 * g) * e * (n1 * g)⁻¹ = z' := by
    have e1 : (n1 * g) * e * (n1 * g)⁻¹ = n1 * (g * e * g⁻¹) * n1⁻¹ := by group
    rcases hn1 with h | h
    · exact ⟨z0, hz0P, hz0c, by rw [e1, h]⟩
    · refine ⟨z0⁻¹, hz0inv, fun q hq => ?_, by rw [e1, h]⟩
      have := hz0c q hq
      calc q * z0⁻¹ = z0⁻¹ * (z0 * q) * z0⁻¹ := by group
        _ = z0⁻¹ * (q * z0) * z0⁻¹ := by rw [this]
        _ = z0⁻¹ * q := by group
  set m : G := n1 * g with hm
  have hS : Q.map (MulAut.conj m⁻¹).toMonoidHom ≤ Cg e := by
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    have h1 := hz'c q hq
    rw [← hmz] at h1
    show e * (m⁻¹ * q * m⁻¹⁻¹) = (m⁻¹ * q * m⁻¹⁻¹) * e
    calc e * (m⁻¹ * q * m⁻¹⁻¹) = m⁻¹ * ((m * e * m⁻¹) * q) * m := by group
      _ = m⁻¹ * (q * (m * e * m⁻¹)) * m := by rw [← h1]
      _ = (m⁻¹ * q * m⁻¹⁻¹) * e := by group
  have hSp : IsPGroup 3 ↥(Q.map (MulAut.conj m⁻¹).toMonoidHom) := c.hQp.map _
  obtain ⟨c1, hc1X, hc1⟩ := Lemma113b.exists_conj_mem_of_isSylowIn c.hQ hS hSp
  have hdN : c1 * m⁻¹ ∈ Subgroup.normalizer (Q : Set G) := by
    apply mem_normalizer_of_conj_le
    intro q hq
    have := hc1 (m⁻¹ * q * m⁻¹⁻¹) (Subgroup.mem_map.2 ⟨q, hq, rfl⟩)
    have e1 : c1 * m⁻¹ * q * (c1 * m⁻¹)⁻¹ = c1 * (m⁻¹ * q * m⁻¹⁻¹) * c1⁻¹ := by group
    rw [e1]
    exact this
  have hce : c1 * e = e * c1 := (Subgroup.mem_centralizer_iff.1 hc1X e (Set.mem_singleton e)).symm
  have hde : (c1 * m⁻¹) * z' * (c1 * m⁻¹)⁻¹ = e := by
    rw [← hmz]
    calc (c1 * m⁻¹) * (m * e * m⁻¹) * (c1 * m⁻¹)⁻¹ = c1 * e * c1⁻¹ := by group
      _ = e := by rw [hce]; group
  have hz'QQ : z' ∈ ⁅Q, Q⁆ := Subgroup.commutator_mono_left inf_le_left hz'P
  have hQmap : Q.map (MulAut.conj (c1 * m⁻¹)).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 hdN
  have h3 := Subgroup.map_commutator (H₁ := Q) (H₂ := Q) (MulAut.conj (c1 * m⁻¹)).toMonoidHom
  rw [hQmap] at h3
  have h4 : (MulAut.conj (c1 * m⁻¹)).toMonoidHom z' ∈
      ⁅Q, Q⁆.map (MulAut.conj (c1 * m⁻¹)).toMonoidHom := Subgroup.mem_map_of_mem _ hz'QQ
  rw [h3] at h4
  apply c.e_not_mem_commutator hB
  have : (MulAut.conj (c1 * m⁻¹)).toMonoidHom z' = e := by
    show (c1 * m⁻¹) * z' * (c1 * m⁻¹)⁻¹ = e
    exact hde
  rw [this] at h4
  exact h4

end Ctx

namespace Ctx

variable {E A : Subgroup G} {e : G} {K Q : Subgroup G}

theorem mem_orbit_form (c : Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))
    {S : Subgroup G}
    (hS : S ∈ MulAction.orbit ↥(Subgroup.normalizer (E : Set G))
      (Subgroup.zpowers e : Subgroup G)) :
    ∃ q ∈ (Q ⊓ K : Subgroup G), S = Subgroup.zpowers (e * q) := by
  obtain ⟨n, hn⟩ := MulAction.mem_orbit_iff.1 hS
  subst hn
  set y : G := (n : G) * e * (n : G)⁻¹ with hy
  have hSy : (n • (Subgroup.zpowers e : Subgroup G)) = Subgroup.zpowers y := by
    ext w
    rw [connAct_mem_smul_iff]
    constructor
    · intro hw
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hw
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      have : w = (n : G) * (e ^ k) * (n : G)⁻¹ := by rw [hk]; group
      rw [this, hy, conj_zpow]
    · intro hw
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hw
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      rw [← hk, hy, conj_zpow]
      group
  have hyE : y ∈ E := (Subgroup.mem_normalizer_iff.1 n.2 e).1 c.heE
  have hyQ0 : y ∉ (Q ⊓ K : Subgroup G) := fun h => c.not_conj_e_into_Q0 hB n h
  have hyE' : y ∈ (Q ⊓ K : Subgroup G) ⊔ Subgroup.zpowers e := c.hEeq ▸ hyE
  have hcent : (Q ⊓ K : Subgroup G) ≤ Subgroup.centralizer (Subgroup.zpowers e : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact ((Commute.zpow_left (show Commute e q from c.hKe q hq.2) k).eq)
  obtain ⟨q', hq', b, hb, hqb⟩ := exists_mul_of_mem_sup hcent hyE'
  rw [hSy]
  rcases mem_zpowers_cases c.he3 hb with h1 | h1 | h1
  · exfalso
    apply hyQ0
    rw [hqb, h1, mul_one]
    exact hq'
  · refine ⟨q', hq', ?_⟩
    rw [hqb, h1]
    have : q' * e = e * q' := (c.hKe q' hq'.2).symm
    rw [this]
  · refine ⟨q'⁻¹, (Q ⊓ K : Subgroup G).inv_mem hq', ?_⟩
    have : y⁻¹ = e * q'⁻¹ := by
      rw [hqb, h1]
      group
    rw [← this]
    exact Subgroup.zpowers_inv.symm

theorem card_mulAut_E (c : Ctx E A e K Q) : Nat.card (MulAut ↥E) = 24261120 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ a b : ↥E, a * b = b * a := fun a b =>
    Subtype.ext (congrArg Subtype.val (c.hEel.1.is_comm.comm a b))
  have hpow : ∀ a : ↥E, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using c.hEel.2 a a.2)
  obtain ⟨eE⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 3) hcomm hpow
    (n := 4) c.hEcard
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL eE,
    CFSG.SectionRank.Ccomm.card_GL_zmod (p := 3) 4]
  simp [Fin.prod_univ_four]

theorem mem_normalizer_E (c : Ctx E A e K Q) {x : G} (hxK : x ∈ K)
    (hx : ∀ q ∈ (Q ⊓ K : Subgroup G), x * q * x⁻¹ ∈ (Q ⊓ K : Subgroup G)) :
    x ∈ Subgroup.normalizer (E : Set G) := by
  rw [c.hEeq]
  apply Lemma113d.mem_normalizer_sup (mem_normalizer_of_conj_le hx)
  apply Lemma113b.centralizer_le_normalizer_zpowers' e
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff.1 hy]
  exact c.hKe x hxK

theorem index_eq (c : Ctx E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)) :
    Nat.card ↥(Subgroup.normalizer (E : Set G)) =
      27 * Nat.card ↥(Subgroup.normalizer (E : Set G) ⊓
        Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)) := by
  classical
  set N : Subgroup G := Subgroup.normalizer (E : Set G) with hN
  set S₀ : Subgroup G := Subgroup.zpowers e with hS₀
  have hmain := card_eq_ncard_orbit_mul N S₀
  set Y : Set (Subgroup G) := MulAction.orbit ↥N S₀ with hY
  have hA : Y.ncard ≤ 27 := by
    have hsub : Y ⊆ (fun q : G => Subgroup.zpowers (e * q)) '' ((Q ⊓ K : Subgroup G) : Set G) := by
      intro S hS
      obtain ⟨q, hq, rfl⟩ := c.mem_orbit_form hB hS
      exact ⟨q, hq, rfl⟩
    calc Y.ncard ≤ ((fun q : G => Subgroup.zpowers (e * q)) ''
          ((Q ⊓ K : Subgroup G) : Set G)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ((Q ⊓ K : Subgroup G) : Set G).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = 27 := by rw [← Nat.card_coe_set_eq]; exact c.card_Q0
  have hB13 : Y.ncard ≡ 1 [MOD 13] := by
    haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    obtain ⟨x, hxK, hxn, ⟨a, hxa⟩, hxfree⟩ := c.exists_x
    have hxN : x ∈ N := c.mem_normalizer_E hxK hxn
    have hxe : Commute x e := (c.hKe x hxK).symm
    have hxS₀ : (⟨x, hxN⟩ : ↥N) • S₀ = S₀ := by
      rw [connAct_smul_eq_iff]
      exact Lemma113b.centralizer_le_normalizer_zpowers' e
        (Subgroup.mem_centralizer_iff.2 fun y hy => by
          rw [Set.mem_singleton_iff.1 hy]; exact c.hKe x hxK)
    refine ncard_orbit_modEq_one (p := 13) (⟨x, hxN⟩ : ↥N) ⟨a, Subtype.ext (by simpa using hxa)⟩
      hxS₀ ?_
    intro S hS hfix
    obtain ⟨q, hq, rfl⟩ := c.mem_orbit_form hB hS
    have hnorm := (connAct_smul_eq_iff N ⟨x, hxN⟩ _).1 hfix
    have hy3 : (e * q) ^ 3 = 1 := by
      have hqe : Commute e q := c.hKe q hq.2
      rw [hqe.mul_pow, c.he3, c.Q0_elemAbelian.2 q hq, one_mul]
    have hy1 : e * q ≠ 1 := by
      intro h
      have : e = q⁻¹ := eq_inv_of_mul_eq_one_left h
      have heQ0 : e ∈ (Q ⊓ K : Subgroup G) := by
        rw [this]; exact (Q ⊓ K : Subgroup G).inv_mem hq
      have hmem : e ∈ (Q ⊓ K : Subgroup G) ⊓ centBar 3 Q K := ⟨heQ0, c.e_mem_centBar⟩
      rw [c.Q0_inf_centBar, Subgroup.mem_bot] at hmem
      exact c.he1 hmem
    have hodd : Odd (13 ^ a) := Odd.pow (by decide)
    have hcomm := commute_of_odd_pow_mem_normalizer hnorm hy3 hy1 hodd hxa
    have hqfix : x * q * x⁻¹ = q := by
      have h1 : x * (e * q) * x⁻¹ = e * q := by
        have := hcomm.eq
        calc x * (e * q) * x⁻¹ = (x * (e * q)) * x⁻¹ := rfl
          _ = (e * q * x) * x⁻¹ := by rw [this]
          _ = e * q := by group
      have h2 : x * (e * q) * x⁻¹ = (x * e * x⁻¹) * (x * q * x⁻¹) := by group
      have h3 : x * e * x⁻¹ = e := by
        have := hxe.eq
        calc x * e * x⁻¹ = (e * x) * x⁻¹ := by rw [this]
          _ = e := by group
      rw [h2, h3] at h1
      exact mul_left_cancel h1
    have hq1 : q = 1 := hxfree q hq hqfix
    rw [hq1, mul_one]
  have hC : Y.ncard ∣ 24261120 := by
    have hidx : (MulAction.stabilizer ↥N S₀).index = Y.ncard := MulAction.index_stabilizer _ _
    have hker : (Subgroup.normalizerMonoidHom E).ker ≤ MulAction.stabilizer ↥N S₀ := by
      intro n hn
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hn
      rw [MulAction.mem_stabilizer_iff, connAct_smul_eq_iff]
      apply Lemma113b.centralizer_le_normalizer_zpowers' e
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact Subgroup.mem_centralizer_iff.1 hn e c.heE
    have h1 := Subgroup.index_dvd_of_le hker
    rw [hidx, Subgroup.index_ker] at h1
    have h2 : Nat.card (Subgroup.normalizerMonoidHom E).range ∣ Nat.card (MulAut ↥E) :=
      Subgroup.card_subgroup_dvd_card _
    rw [c.card_mulAut_E] at h2
    exact h1.trans h2
  have hD : Y.ncard ≠ 1 := by
    intro h1
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
    have hS₀a : S₀ = a := by
      have : S₀ ∈ Y := MulAction.mem_orbit_self S₀
      rw [ha] at this
      exact this
    apply hB
    intro n hn
    have hmem : (⟨n, hn⟩ : ↥N) • S₀ ∈ Y := MulAction.mem_orbit _ _
    rw [ha, Set.mem_singleton_iff, ← hS₀a] at hmem
    exact (connAct_smul_eq_iff N ⟨n, hn⟩ S₀).1 hmem
  have h27 : Y.ncard = 27 := by
    have hmod : Y.ncard % 13 = 1 := hB13
    have hle := hA
    have hdvd := hC
    have hne := hD
    interval_cases hY27 : Y.ncard <;> simp_all <;> omega
  rw [h27] at hmain
  exact hmain

end Ctx

end Lift

end Lemma113Claims

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
