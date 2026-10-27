module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Complement
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Thompson
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1Slim
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSQuasi
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Fusion

public section

namespace CFSG.EvenSporadicStandard.Induction.Closing

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

section Perfect

variable {H : Type} [Group H] [Finite H] {L : Subgroup H}

omit [Finite H] in
theorem mem_commutator_of_perfect (hodd : Odd (Nat.card ↥(center ↥L)))
    (hperf : PerfectInvolutions (↥L ⧸ center ↥L)) {a : H} (haL : a ∈ L) (haa : a * a = 1)
    (ha1 : (⟨a, haL⟩ : ↥L) ∉ center ↥L) :
    a ∈ ⁅L ⊓ centralizer ({a} : Set H), L ⊓ centralizer ({a} : Set H)⁆ := by
  have haN : a ∈ normalizer (L : Set H) := Subgroup.le_normalizer haL
  have ha₀ : (⟨a, haL⟩ : ↥L) * ⟨a, haL⟩ = 1 := Subtype.ext haa
  have hā2 : orderOf ((⟨a, haL⟩ : ↥L) : ↥L ⧸ center ↥L) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← QuotientGroup.mk_mul, ha₀]
      rfl
    · intro h1
      exact ha1 ((QuotientGroup.eq_one_iff _).1 h1)
  have hcomm := hperf _ hā2
  set D : Subgroup ↥L := (L ⊓ centralizer ({a} : Set H)).subgroupOf L with hD
  set a' : ↥L := ⟨a, haL⟩ with ha'
  have hle : centralizer ({(a' : ↥L ⧸ center ↥L)} : Set (↥L ⧸ center ↥L)) ≤
      D.map (QuotientGroup.mk' (center ↥L)) := by
    intro y hy
    have hy' := mem_centralizer_singleton_iff.1 hy
    have hfix : normalizerAction L ⟨a, haN⟩ y = y := by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      rw [act_mk haN]
      have e : (⟨a * (x : H) * a⁻¹, (mem_normalizer_iff.1 haN x).1 x.2⟩ : ↥L) = a' * x * a'⁻¹ :=
        Subtype.ext rfl
      rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [mul_inv_eq_iff_eq_mul]
      exact hy'.symm
    obtain ⟨y', rfl, hy'a⟩ := exists_fixed_lift hodd haN haa hfix
    refine ⟨y', ?_, rfl⟩
    refine mem_subgroupOf.2 ⟨y'.2, mem_centralizer_singleton_iff.2 ?_⟩
    calc (y' : H) * a = (a * (y' : H) * a⁻¹) * a := by rw [hy'a]
      _ = a * y' := by group
  have h1 : (a' : ↥L ⧸ center ↥L) ∈ (⁅D, D⁆).map (QuotientGroup.mk' (center ↥L)) := by
    rw [map_commutator]
    exact commutator_mono hle hle hcomm
  obtain ⟨w, hw, hwa⟩ := h1
  have hz : w⁻¹ * a' ∈ center ↥L := QuotientGroup.eq.1 hwa
  obtain ⟨z, hzdef⟩ : ∃ z : ↥L, z = w⁻¹ * a' := ⟨_, rfl⟩
  rw [← hzdef] at hz
  have haz : a' = w * z := by rw [hzdef]; group
  obtain ⟨j, hj⟩ := hodd
  have hzn : z ^ (2 * j + 1) = 1 := by
    have := pow_card_eq_one' (G := ↥(center ↥L)) (x := ⟨z, hz⟩)
    rw [hj] at this
    exact congrArg Subtype.val this
  have hcz : Commute w z := mem_center_iff.1 hz w
  have ha'mem : a' ∈ ⁅D, D⁆ := by
    have e1 : a' ^ (2 * j + 1) = a' := by
      rw [pow_succ, pow_mul, pow_two, ha₀, one_pow, one_mul]
    have e2 : a' ^ (2 * j + 1) = w ^ (2 * j + 1) := by
      rw [haz, hcz.mul_pow, hzn, mul_one]
    have e3 : a' = w ^ (2 * j + 1) := e1.symm.trans e2
    rw [e3]
    exact pow_mem hw _
  have hfinal : L.subtype a' ∈ map L.subtype ⁅D, D⁆ := Subgroup.mem_map_of_mem _ ha'mem
  rw [map_commutator, hD, Subgroup.map_subgroupOf_eq_of_le inf_le_left] at hfinal
  exact hfinal

end Perfect

namespace ClosingSetup

variable {H : Type} [Group H] [Finite H] {N L : Subgroup H} {t u : H}
  (S : ClosingSetup H N L t u)
include S

theorem exists_index_two (hS2 : ∀ P : Sylow 2 (centralizer (L : Set H)), Nat.card P = 2)
    (hinn : centralizer ({t} : Set H) ≤ L ⊔ centralizer (L : Set H)) :
    ∃ R : Subgroup H, R ≤ centralizer ({t} : Set H) ∧
      (∀ b ∈ centralizer ({t} : Set H), b ∈ R ∨ b * t ∈ R) ∧ t ∉ R ∧
      ∀ x ∈ R, ∃ ℓ ∈ L, ∃ k : H, k ∈ centralizer (L : Set H) ∧ Odd (orderOf k) ∧ x = ℓ * k := by
  classical
  obtain ⟨K₀', hK₀'C, hK₀'odd, htK, hmul, -⟩ := exists_K₀ hS2 S.t_mem S.t_order
  set C : Subgroup H := centralizer (L : Set H) with hC
  have htM : t ∈ centralizer ({t} : Set H) := mem_centralizer_singleton_iff.2 rfl
  have hdec : ∀ x ∈ L ⊔ K₀', ∃ ℓ ∈ L, ∃ k : H, k ∈ C ∧ Odd (orderOf k) ∧ x = ℓ * k := by
    intro x hx
    obtain ⟨ℓ, hℓ, k, hk, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hK₀'C hx
    exact ⟨ℓ, hℓ, k, hK₀'C hk, hK₀'odd k hk, rfl⟩
  have htR : t ∉ (L ⊔ K₀') ⊓ centralizer ({t} : Set H) := fun h =>
    S.t_not_mem_sup hK₀'C hK₀'odd h.1
  have hsplit : ∀ b ∈ centralizer ({t} : Set H),
      b ∈ (L ⊔ K₀') ⊓ centralizer ({t} : Set H) ∨
        b * t ∈ (L ⊔ K₀') ⊓ centralizer ({t} : Set H) := by
    intro b hb
    obtain ⟨ℓ, hℓ, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (le_rfl : C ≤ centralizer (L : Set H)) (hinn hb)
    by_cases hcK : c ∈ K₀'
    · left
      exact ⟨mul_mem_sup hℓ hcK, hb⟩
    · right
      have hct : c * t ∈ K₀' := (hmul c hc t S.t_mem).2 (iff_of_false hcK htK)
      refine ⟨?_, (centralizer ({t} : Set H)).mul_mem hb htM⟩
      have : ℓ * c * t = ℓ * (c * t) := mul_assoc ℓ c t
      rw [this]
      exact mul_mem_sup hℓ hct
  exact ⟨(L ⊔ K₀') ⊓ centralizer ({t} : Set H), inf_le_right, hsplit, htR, fun x hx => hdec x hx.1⟩

end ClosingSetup

section Rest

variable {H : Type} [Group H] [Finite H] {L : Subgroup H}

omit [Finite H] in
theorem commutator_le_of_relIndex_eq_two {M R : Subgroup H} (hRM : R.relIndex M = 2) :
    ⁅M, M⁆ ≤ R := by
  have hN : (R.subgroupOf M).index = 2 := hRM
  have h3 := commutator_le_of_index_eq_two hN
  intro x hx
  rw [← map_subtype_commutator] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact mem_subgroupOf.1 (h3 hy)

omit [Finite H] in
theorem mem_of_two_power_order {b ℓ k : H} (hℓ : ℓ ∈ L) (hk : Odd (orderOf k))
    (hc : Commute ℓ k) (hb : b = ℓ * k) {j : ℕ} (hj : orderOf b = 2 ^ j) : b ∈ L := by
  have hbn : b ^ orderOf k = ℓ ^ orderOf k := by
    rw [hb, hc.mul_pow, pow_orderOf_eq_one, mul_one]
  have hgcd : (orderOf k).gcd (orderOf b) = 1 := by
    rw [hj]
    exact (Nat.coprime_two_right.2 hk).pow_right j
  have hmem : b ∈ zpowers (b ^ orderOf k) := mem_zpowers_pow_iff.2 hgcd
  have hL : b ^ orderOf k ∈ L := by
    rw [hbn]
    exact pow_mem hℓ _
  exact (zpowers_le.2 hL) hmem

namespace ClosingSetup

variable {N : Subgroup H} {t u : H} (S : ClosingSetup H N L t u)
include S

theorem sylow_split (hS2 : ∀ P : Sylow 2 (centralizer (L : Set H)), Nat.card P = 2)
    (hinn : centralizer ({t} : Set H) ≤ L ⊔ centralizer (L : Set H)) {P : Subgroup H}
    (hP : IsPGroup 2 P) (htP : t ∈ P) (hPM : P ≤ centralizer ({t} : Set H)) :
    ∀ b ∈ P, b ∈ L ∨ b * t ∈ L := by
  obtain ⟨R, hRM, hsplit, htR, hdec⟩ := S.exists_index_two hS2 hinn
  have key : ∀ b' ∈ P, b' ∈ R → b' ∈ L := by
    intro b' hb'P hb'R
    obtain ⟨ℓ, hℓ, k, hk, hko, hb'⟩ := hdec b' hb'R
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.1 hP (⟨b', hb'P⟩ : ↥P)
    rw [Subgroup.orderOf_mk] at hj
    exact mem_of_two_power_order hℓ hko (mem_centralizer_iff.1 hk ℓ hℓ) hb' hj
  intro b hb
  rcases hsplit b (hPM hb) with h | h
  · exact Or.inl (key b hb h)
  · exact Or.inr (key (b * t) (P.mul_mem hb htP) h)

theorem not_isConj_of_perfect (hperf : PerfectInvolutions (↥L ⧸ center ↥L))
    (hS2 : ∀ P : Sylow 2 (centralizer (L : Set H)), Nat.card P = 2)
    (hinn : centralizer ({t} : Set H) ≤ L ⊔ centralizer (L : Set H)) {a : H} (haL : a ∈ L)
    (ha2 : orderOf a = 2) : ¬ IsConj t a := by
  intro hconj
  obtain ⟨R, hRM, hsplit, htR, -⟩ := S.exists_index_two hS2 hinn
  have htM : t ∈ centralizer ({t} : Set H) := mem_centralizer_singleton_iff.2 rfl
  have hRidx : R.relIndex (centralizer ({t} : Set H)) = 2 := relIndex_eq_two htM htR hsplit
  have haa : a * a = 1 := mul_self_eq_one_of_orderOf_eq_two ha2
  have ha1 : (⟨a, haL⟩ : ↥L) ∉ center ↥L := fun hz =>
    not_odd_card_center_of_mem (M := L) haL ha2
      (fun x hx => congrArg Subtype.val (mem_center_iff.1 hz ⟨x, hx⟩)) S.centre_odd
  have hcomm := mem_commutator_of_perfect S.centre_odd hperf haL haa ha1
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  set f : H →* H := (MulAut.conj c⁻¹).toMonoidHom with hf
  have hfa : f a = t := by
    show c⁻¹ * a * c⁻¹⁻¹ = t
    rw [← hc]
    group
  have hmap : (L ⊓ centralizer ({a} : Set H)).map f ≤ centralizer ({t} : Set H) := by
    rintro _ ⟨y, ⟨-, hy⟩, rfl⟩
    refine mem_centralizer_singleton_iff.2 ?_
    have hy' : y * a = a * y := mem_centralizer_singleton_iff.1 hy
    show c⁻¹ * y * c⁻¹⁻¹ * t = t * (c⁻¹ * y * c⁻¹⁻¹)
    have e1 : c⁻¹ * y * c⁻¹⁻¹ * t = c⁻¹ * (y * a) * c := by rw [← hc]; group
    have e2 : t * (c⁻¹ * y * c⁻¹⁻¹) = c⁻¹ * (a * y) * c := by rw [← hc]; group
    rw [e1, e2, hy']
  have h1 : t ∈ ⁅centralizer ({t} : Set H), centralizer ({t} : Set H)⁆ := by
    have h2 := Subgroup.mem_map_of_mem f hcomm
    rw [hfa, map_commutator] at h2
    exact commutator_mono hmap hmap h2
  exact htR (commutator_le_of_relIndex_eq_two hRidx h1)

theorem false_of_perfect (hacc : AutCenterCondExc (↥L ⧸ center ↥L) (fun _ => False))
    (hoc : AutOddCoreTrivial (↥L ⧸ center ↥L))
    (hinn : ∀ α : MulAut (↥L ⧸ center ↥L), ∃ g, α = MulAut.conj g)
    (hperf : PerfectInvolutions (↥L ⧸ center ↥L))
    (hS2 : ∀ P : Sylow 2 (centralizer (L : Set H)), Nat.card P = 2) (htN : t ∈ N) : False := by
  classical
  have hf : Sol78Fusion u t := S.sol78Fusion_of_data hacc hoc (fun _ _ _ _ _ h => h)
  have hiso : ∀ t' ∈ fusedSet u t, t' = t := fun t' ht' => S.fusedSet_eq hf ht'
  obtain ⟨P, htP, huP, hPM⟩ := exists_sylow_le_centralizer S.t_order S.u_order S.u_comm_t hiso
  have hLinn : ∀ α : MulAut ↥L, ∃ l : ↥L, α = MulAut.conj l :=
    mulAut_inner_of_inner_centerQuotient S.perfect hinn
  have hinn' : centralizer ({t} : Set H) ≤ L ⊔ centralizer (L : Set H) :=
    S.centralizer_t_le.trans (normalizer_le_sup_centralizer_of_mulAut_inner hLinn)
  have hsplit := S.sylow_split hS2 hinn' P.isPGroup' htP hPM
  have hLP : L.relIndex P = 2 := relIndex_eq_two htP S.t_not_mem hsplit
  have hU : (↑P ⊓ L : Subgroup H).relIndex P = 2 := by
    rw [inf_relIndex_left]
    exact hLP
  have htU : t ∉ (↑P ⊓ L : Subgroup H) := fun h => S.t_not_mem h.2
  have hmin : ∀ y ∈ (P : Subgroup H), y ∉ (↑P ⊓ L : Subgroup H) → orderOf t ≤ orderOf y := by
    intro y _ hyU
    have hy : orderOf y ≠ 1 := fun h => hyU (by rw [orderOf_eq_one_iff.1 h]; exact one_mem _)
    have := orderOf_pos y
    rw [S.t_order]
    omega
  have hconj : ∀ g : H, g⁻¹ * t * g ∉ (↑P ⊓ L : Subgroup H) := by
    intro g hg
    have ha2 : orderOf (g⁻¹ * t * g) = 2 := by
      have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective t
      simpa [MulAut.conj_apply] using this.trans S.t_order
    exact S.not_isConj_of_perfect hperf hS2 hinn' hg.2 ha2 (isConj_iff.2 ⟨g⁻¹, by simp⟩)
  obtain ⟨N', hN', hcyc, hp2, htN'⟩ := exists_normal_cyclic_two_quotient_of_thompson
    P.isPGroup' (Sylow.not_dvd_index P) inf_le_left hU htP htU hmin hconj
  have hNle : N ≤ N' := by
    have : IsSimpleGroup ↥N := S.fstar.isSimpleGroup
    have hcommN : commutator ↥N = ⊤ :=
      (isQuasisimple_of_simple S.fstar.isSimpleGroup S.fstar.nonabelian).1
    intro n hn
    let f : ↥N →* H ⧸ N' := (QuotientGroup.mk' N').comp N.subtype
    have hker : commutator ↥N ≤ f.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2
        (IsCyclic.isMulCommutative.is_comm.comm _ _)
    have hn' : (⟨n, hn⟩ : ↥N) ∈ f.ker := hker (hcommN ▸ mem_top _)
    exact (QuotientGroup.eq_one_iff n).1 hn'
  exact htN' (hNle htN)

end ClosingSetup

end Rest

end CFSG.EvenSporadicStandard.Induction.Closing

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Closing

theorem solomonCoreP_of_perfect :
    ∀ (s : TauCeti.SporadicName) (Q : PairClass), Q.InL → Q.TwoSylow → PerfectRowData s →
      TMemFStar s Q → SolomonCoreP s Q := by
  intro s Q hQ hTS D hT H _ _ N L K t u hcov hhyp hQu
  have huL := hQ H L K u hQu
  have S := ClosingSetup.of_hypQ hhyp huL
  have hY : IsSporadic (↥L ⧸ center ↥L) s := hcov.2.2
  have : IsSimpleGroup (↥L ⧸ center ↥L) := S.quasisimple.2.1
  have hZ : center (↥L ⧸ center ↥L) = ⊥ := center_eq_bot_of_simple_nonabelian S.quasisimple.2.2
  have hacc := autCenterCond_of_inner (D.allInner _ hY) hZ (D.center _ hY)
  exact S.false_of_perfect hacc.toExc (D.oddCore _ hY) (D.allInner _ hY) (D.perfect _ hY)
    (hTS H L K u hQu) (hT H N L K t u hcov hhyp hQu)

end CFSG.EvenSporadicStandard.Induction
