module

public import CFSG.GH74.GLS.Stage2.Signalizer.L46EDefs
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.Adapters.RankTwoModelTransports
import CFSG.Dihedral.Glauberman.DicksonMaxCases
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L46E

open Equiv Equiv.Perm CFSG.Assembly.LowTwoRank
open CFSG.Adapters.RankTwoModelTransports
open scoped MatrixGroups

theorem l46e_orderOf_dvd_six {c π : Perm (Fin 5)} (hc : orderOf c = 3) (hπ : π * c * π⁻¹ = c) :
    orderOf π ∣ 6 := by
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := c) (by rw [hc]; exact Nat.prime_three)
  rw [hc] at hn
  have hsum : c.cycleType.sum ≤ 5 := by
    simpa using Equiv.Perm.sum_cycleType_le c
  rw [hn, Multiset.sum_replicate] at hsum
  have hn0 : n = 0 := by simp at hsum; omega
  subst hn0
  have hcard := Equiv.Perm.nat_card_centralizer c
  rw [hn] at hcard
  have hmem : π ∈ Subgroup.centralizer {c} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.1 hπ
  have h6 : Nat.card (Subgroup.centralizer {c}) = 6 := by
    rw [hcard]
    decide
  have := orderOf_dvd_natCard (⟨π, hmem⟩ : Subgroup.centralizer {c})
  rwa [h6, Subgroup.orderOf_mk] at this

theorem l46e_eq_of_div_mem_center {K : Type*} [Group K] (hK : Group.IsPerfect K) (Θ : K →* K)
    (h : ∀ k, Θ k * k⁻¹ ∈ Subgroup.center K) (k : K) : Θ k = k := by
  let lam : K →* K := MonoidHom.mk' (fun k => Θ k * k⁻¹) (by
    intro a b
    have hc : Commute a⁻¹ (Θ b * b⁻¹) :=
      Commute.inv_left (Subgroup.mem_center_iff.mp (h b) a : Commute a (Θ b * b⁻¹))
    calc Θ (a * b) * (a * b)⁻¹ = Θ a * ((Θ b * b⁻¹) * a⁻¹) := by
          simp only [map_mul, mul_inv_rev, mul_assoc]
      _ = Θ a * (a⁻¹ * (Θ b * b⁻¹)) := by rw [hc.eq.symm]
      _ = (Θ a * a⁻¹) * (Θ b * b⁻¹) := by rw [mul_assoc])
  have hker : commutator K ≤ lam.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact (Subgroup.mem_center_iff.mp (h a) (lam b) : _).symm
  have hk := hker (by rw [Group.isPerfect_def.mp hK]; trivial : k ∈ commutator K)
  rw [MonoidHom.mem_ker] at hk
  exact mul_inv_eq_one.mp hk

theorem l46e_sl2five_psi {K : Type} [Group K] (h : CFSG.GH74.GLS.HasSL2Model K (fun q => q = 5)) :
    Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  have hcard5 : Nat.card F = 5 := hcard
  let e' : K ≃* SL(2, F) := e.trans (specialLinearGroupEquivStatedSL 2 F).symm
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨ψ⟩ := CFSG.Glauberman.Dickson.MaxCases.nonempty_psl2_galoisField_five
  have := Fintype.ofFinite F
  have := Fintype.ofFinite (GaloisField 5 1)
  have hc : Fintype.card F = Fintype.card (GaloisField 5 1) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard5,
      GaloisField.card 5 1 one_ne_zero, pow_one]
  exact ⟨(QuotientGroup.congr _ _ e' (Subgroup.map_center_eq e')).trans
    ((projectiveSpecialLinearGroupCongr (Fin 2) (FiniteField.ringEquivOfCardEq hc)).trans ψ)⟩

theorem l46e_sl2five_perfect {K : Type} [Group K]
    (h : CFSG.GH74.GLS.HasSL2Model K (fun q => q = 5)) : Group.IsPerfect K := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  have hcard5 : Nat.card F = 5 := hcard
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have := Fintype.ofFinite F
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard5]; norm_num)
    exact ⟨s, hs⟩
  have hSL : Group.IsPerfect SL(2, F) := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
  let e' : SL(2, F) ≃* K := (specialLinearGroupEquivStatedSL 2 F).trans e.symm
  exact Group.IsPerfect.ofSurjective (f := e'.toMonoidHom) e'.surjective

theorem l46e_sl2five_center_sq {K : Type} [Group K]
    (h : CFSG.GH74.GLS.HasSL2Model K (fun q => q = 5)) : ∀ z ∈ Subgroup.center K, z * z = 1 := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  let e' : K ≃* SL(2, F) := e.trans (specialLinearGroupEquivStatedSL 2 F).symm
  intro z hz
  have hz' : e' z ∈ Subgroup.center SL(2, F) := by
    rw [← Subgroup.map_center_eq e']
    exact Subgroup.mem_map_of_mem _ hz
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz'
  apply e'.injective
  rw [map_mul, map_one]
  have hrr : r * r = 1 := by simpa [sq] using hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, ← hrz, Matrix.SpecialLinearGroup.coe_one, ← map_mul, hrr,
    map_one]

theorem l46e_exists_perm {K : Type} [Group K]
    (ψ : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 5)) (Θ : MulAut K) :
    ∃ π : Perm (Fin 5), ∀ k : K,
      ((ψ (QuotientGroup.mk (Θ k)) : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
        π * ((ψ (QuotientGroup.mk k) : alternatingGroup (Fin 5)) : Perm (Fin 5)) * π⁻¹ := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by norm_num) (by norm_num)
  let Θ' : MulAut (K ⧸ Subgroup.center K) :=
    QuotientGroup.congr (Subgroup.center K) (Subgroup.center K) Θ (Subgroup.map_center_eq Θ)
  obtain ⟨π, hπ⟩ := hbij.2 (MulAut.congr ψ Θ')
  refine ⟨π, fun k => ?_⟩
  have h1 : ψ (QuotientGroup.mk (Θ k)) = MulAut.congr ψ Θ' (ψ (QuotientGroup.mk k)) := by
    rw [MulAut.congr_apply]
    simp [Θ', QuotientGroup.congr_mk]
  rw [h1, ← hπ, MulAut.conjNormal_apply]

theorem l46e_data {K : Type} [Group K] (h : CFSG.GH74.GLS.HasSL2Model K (fun q => q = 5)) :
    ∃ q : K →* alternatingGroup (Fin 5), Function.Surjective q ∧
      (∀ k, q k = 1 ↔ k ∈ Subgroup.center K) ∧
      (∀ Θ : MulAut K, ∃ π : Perm (Fin 5), ∀ k : K,
        ((q (Θ k) : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
          π * (q k : Perm (Fin 5)) * π⁻¹) ∧
      Group.IsPerfect K ∧ ∀ z ∈ Subgroup.center K, z * z = 1 := by
  obtain ⟨ψ⟩ := l46e_sl2five_psi h
  refine ⟨ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)),
    ψ.surjective.comp (QuotientGroup.mk_surjective), fun k => ?_, fun Θ => l46e_exists_perm ψ Θ,
    l46e_sl2five_perfect h, l46e_sl2five_center_sq h⟩
  change ψ (QuotientGroup.mk k) = 1 ↔ k ∈ Subgroup.center K
  rw [map_eq_one_iff ψ ψ.injective, QuotientGroup.eq_one_iff]

theorem l46e_aut_eq_one {K : Type} [Group K] (q : K →* alternatingGroup (Fin 5))
    (hqs : Function.Surjective q) (hqk : ∀ k, q k = 1 ↔ k ∈ Subgroup.center K)
    (hperf : Group.IsPerfect K) (hsq : ∀ z ∈ Subgroup.center K, z * z = 1) (Θ : MulAut K)
    (π : Perm (Fin 5))
    (hπ : ∀ k : K, ((q (Θ k) : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
      π * (q k : Perm (Fin 5)) * π⁻¹)
    {x : K} (hx3 : orderOf x = 3) (hΘx : Θ x = x) {n : ℕ} (hn : Θ ^ n = 1) (hodd : Odd n)
    (hcop : Nat.Coprime n 3) (k : K) : Θ k = k := by
  have hpow : ∀ (m : ℕ) (k : K), ((q ((Θ ^ m) k) : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
      π ^ m * (q k : Perm (Fin 5)) * (π ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro k; simp
    | succ m ih =>
      intro k
      rw [pow_succ, MulAut.mul_apply, ih, hπ]
      group
  have hπn : π ^ n = 1 := by
    have h1 : ∀ k, ((q k : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
        π ^ n * (q k : Perm (Fin 5)) * (π ^ n)⁻¹ := by
      intro k
      have := hpow n k
      rwa [hn, MulAut.one_apply] at this
    apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 5 (by norm_num)
    rw [map_one]
    refine MulEquiv.ext fun a => ?_
    obtain ⟨k, rfl⟩ := hqs a
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, MulAut.one_apply]
    exact (h1 k).symm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hc1 : q x ≠ 1 := by
    intro h
    have hx2 : x ^ 2 = 1 := by rw [sq]; exact hsq x ((hqk x).1 h)
    have := orderOf_dvd_of_pow_eq_one hx2
    rw [hx3] at this
    omega
  have hc3 : orderOf ((q x : alternatingGroup (Fin 5)) : Perm (Fin 5)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [← map_pow, hx3', map_one]) hc1
  have hconj : π * (q x : Perm (Fin 5)) * π⁻¹ = (q x : Perm (Fin 5)) := by
    have := hπ x
    rw [hΘx] at this
    exact this.symm
  have h6 := l46e_orderOf_dvd_six hc3 hconj
  have hdn : orderOf π ∣ n := orderOf_dvd_of_pow_eq_one hπn
  have hgcd : Nat.Coprime n 6 := by
    have h2 : Nat.Coprime n 2 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      obtain ⟨m, hm⟩ := hodd
      omega
    exact Nat.Coprime.mul_right h2 hcop
  have hπ1 : π = 1 := by
    have h1 : orderOf π ∣ Nat.gcd n 6 := Nat.dvd_gcd hdn h6
    rw [hgcd] at h1
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)
  subst hπ1
  have key : ∀ k : K, Θ k * k⁻¹ ∈ Subgroup.center K := by
    intro k
    rw [← hqk, map_mul, map_inv]
    have : q (Θ k) = q k := Subtype.ext (by simpa using hπ k)
    rw [this, mul_inv_cancel]
  exact l46e_eq_of_div_mem_center hperf Θ.toMonoidHom key k

theorem autFactE : AutFactE := by
  intro Y _ _ X hX y hyX hodd hcop
  obtain ⟨hsl, hX3⟩ := hX
  have hKn : (ncl X).Normal := Subgroup.normalClosure_normal
  obtain ⟨q, hqs, hqk, hperm, hperf, hsq⟩ := l46e_data hsl
  let Θ : MulAut (ncl X) := MulAut.conjNormal y
  obtain ⟨π, hπ⟩ := hperm Θ
  obtain ⟨g, hg1⟩ : ∃ g : X, g ≠ 1 := by
    have : 1 < Nat.card X := by rw [hX3]; norm_num
    have := Finite.one_lt_card_iff_nontrivial.1 this
    exact exists_ne (1 : X)
  have hg3 : orderOf g = 3 := by
    have hd : orderOf g ∣ 3 := hX3 ▸ orderOf_dvd_natCard g
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hg1
    · exact h
  let x : ncl X := ⟨g, Subgroup.subset_normalClosure g.2⟩
  have hx3 : orderOf x = 3 := by
    rw [← Subgroup.orderOf_coe, ← hg3, ← Subgroup.orderOf_coe g]
  have hΘx : Θ x = x := by
    apply Subtype.ext
    change y * (g : Y) * y⁻¹ = g
    exact mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_centralizer_iff.1 hyX g g.2).symm
  have hn : Θ ^ orderOf y = 1 := by
    change (MulAut.conjNormal y : MulAut (ncl X)) ^ orderOf y = 1
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hall := l46e_aut_eq_one q hqs hqk hperf hsq Θ π hπ hx3 hΘx hn hodd hcop
  refine Subgroup.mem_centralizer_iff.2 fun k hk => ?_
  have hk' := congrArg Subtype.val (hall ⟨k, hk⟩)
  change y * k * y⁻¹ = k at hk'
  exact (mul_inv_eq_iff_eq_mul.1 hk').symm

end CFSG.GH74.GLS.Stage2.Signalizer.L46E
