module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporCMon13Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.Heisenberg

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13

open Subgroup
open scoped commutatorElement

theorem balance_at_central {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {c : G} (hc : orderOf c = p)
    {S : Subgroup G} (hSp : IsPGroup p S)
    (hSmax : ∀ T : Subgroup G, IsPGroup p T → S ≤ T → T = S)
    (hS3 : Nat.card S = p ^ 3) (hSnab : ∃ a b : S, a * b ≠ b * a) (hcS : c ∈ S)
    (hcSc : ∀ s ∈ S, c * s = s * c)
    (hsolv : Group.IsSolvable ↥(centralizer ({c} : Set G)))
    (hcore : CFSG.pPrimeCore p ↥(centralizer ({c} : Set G)) = ⊥) :
    ∀ R Y : Subgroup G, CFSG.Open.IsElemAbelian p R → Nat.card R = p ^ 2 → c ∈ R →
      Y ≤ centralizer ({c} : Set G) → ¬ p ∣ Nat.card Y → R ≤ normalizer (Y : Set G) →
      Y = ⊥ := by
  intro R Y hR hR2 hcR hYC hY hRY
  set H : Subgroup G := centralizer ({c} : Set G) with hHdef
  have hSH : S ≤ H := fun s hs => Subgroup.mem_centralizer_singleton_iff.2 (hcSc s hs).symm
  have hRH : R ≤ H := by
    intro r hr
    rw [hHdef, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hR.1.is_comm.comm (⟨r, hr⟩ : R) ⟨c, hcR⟩)
  let cH : H := ⟨c, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hcH1 : cH ≠ 1 := by
    intro h
    have h1 : c = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hc
    exact hp.out.ne_one hc.symm
  have hcHp : cH ^ p = 1 := Subtype.ext (by
    show c ^ p = 1
    rw [← hc, pow_orderOf_eq_one])
  have hcH : orderOf cH = p := orderOf_eq_prime hcHp hcH1
  have hczH : cH ∈ Subgroup.center H := Subgroup.mem_center_iff.2 fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  have hSpH : IsPGroup p (S.subgroupOf H) := hSp.comap_of_injective H.subtype Subtype.coe_injective
  have hSmaxH : ∀ T : Subgroup H, IsPGroup p T → S.subgroupOf H ≤ T → T = S.subgroupOf H := by
    intro T hT hST
    have hT' : IsPGroup p (T.map H.subtype) := hT.map H.subtype
    have hS' : S ≤ T.map H.subtype := by
      intro s hs
      exact ⟨⟨s, hSH hs⟩, hST (Subgroup.mem_subgroupOf.2 hs), rfl⟩
    have heq := hSmax _ hT' hS'
    ext t
    constructor
    · intro ht
      have hmem : (t : G) ∈ T.map H.subtype := ⟨t, ht, rfl⟩
      rw [heq] at hmem
      exact Subgroup.mem_subgroupOf.2 hmem
    · intro ht
      exact hST ht
  have hS3H : Nat.card (S.subgroupOf H) = p ^ 3 := (card_subgroupOf_of_le' hSH).trans hS3
  have hSnabH : ∃ a b : S.subgroupOf H, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hSnab
    refine ⟨⟨⟨a, hSH a.2⟩, a.2⟩, ⟨⟨b, hSH b.2⟩, b.2⟩, fun h => hab (Subtype.ext ?_)⟩
    have h2 := congrArg (fun t : S.subgroupOf H => (t : H) : _ → H) h
    have h3 := congrArg Subtype.val h2
    exact h3
  have hcSH : cH ∈ S.subgroupOf H := Subgroup.mem_subgroupOf.2 hcS
  obtain ⟨hSN, hCS⟩ := sylow_normal_of_core hsolv hcore hcH hczH hSpH hSmaxH hS3H hSnabH hcSH
  have hR_H : CFSG.Open.IsElemAbelian p (R.subgroupOf H) := hR.subgroupOf H
  have hR2H : Nat.card (R.subgroupOf H) = p ^ 2 := (card_subgroupOf_of_le' hRH).trans hR2
  have hcR_H : cH ∈ R.subgroupOf H := Subgroup.mem_subgroupOf.2 hcR
  have hY_H : ¬ p ∣ Nat.card (Y.subgroupOf H) := by
    rw [card_subgroupOf_of_le' hYC]
    exact hY
  have hRY_H : R.subgroupOf H ≤ normalizer ((Y.subgroupOf H : Subgroup H) : Set H) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hr' : (r : G) ∈ R := Subgroup.mem_subgroupOf.1 hr
    have h1 := Subgroup.mem_normalizer_iff.1 (hRY hr') (h : G)
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact h1
  have hYH := balance_of_sylow_core hcH hczH hSpH hSmaxH hS3H hSnabH hcSH hSN hCS hR_H hR2H
    hcR_H hY_H hRY_H
  rw [eq_bot_iff]
  intro y hy
  have hyH : (⟨y, hYC hy⟩ : H) ∈ Y.subgroupOf H := Subgroup.mem_subgroupOf.2 hy
  rw [hYH, Subgroup.mem_bot] at hyH
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hyH

theorem closure_sylow_of_central {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hG : (Nat.card G).factorization p = 3) {g d c : G} (hg : g ^ p = 1) (hd : d ^ p = 1)
    (hc : orderOf c = p) (hcg : c * g = g * c) (hcd : c * d = d * c)
    (hdg : d * g = g * (d * c ^ 4)) (hp4 : ¬ p ∣ 4) :
    IsPGroup p (closure ({g, d} : Set G)) ∧
      (∀ T : Subgroup G, IsPGroup p T → closure ({g, d} : Set G) ≤ T →
        T = closure ({g, d} : Set G)) ∧
      Nat.card (closure ({g, d} : Set G)) = p ^ 3 ∧
      (∃ a b : closure ({g, d} : Set G), a * b ≠ b * a) ∧
      c ∈ closure ({g, d} : Set G) ∧ (∀ s ∈ closure ({g, d} : Set G), c * s = s * c) := by
  have h1 : d * g = c ^ 4 * (g * d) := by
    have hdc : d * c ^ 4 = c ^ 4 * d := ((show Commute d c from hcd.symm).pow_right 4).eq
    have hgc : g * c ^ 4 = c ^ 4 * g := ((show Commute g c from hcg.symm).pow_right 4).eq
    calc d * g = g * (d * c ^ 4) := hdg
      _ = g * (c ^ 4 * d) := by rw [hdc]
      _ = (g * c ^ 4) * d := by group
      _ = (c ^ 4 * g) * d := by rw [hgc]
      _ = c ^ 4 * (g * d) := by group
  have hz : ⁅g, d⁆ = (c ^ 4)⁻¹ := by
    rw [commutatorElement_def]
    have h2 : g * d = (c ^ 4)⁻¹ * (d * g) := by rw [h1]; group
    calc g * d * g⁻¹ * d⁻¹ = (c ^ 4)⁻¹ * (d * g) * g⁻¹ * d⁻¹ := by rw [h2]
      _ = (c ^ 4)⁻¹ := by group
  have hc4 : c ^ 4 ≠ 1 := by
    intro h
    have hdvd : orderOf c ∣ 4 := orderOf_dvd_of_pow_eq_one h
    rw [hc] at hdvd
    exact hp4 hdvd
  have hnc : ∃ a b : closure ({g, d} : Set G), a * b ≠ b * a := by
    refine ⟨⟨g, Subgroup.subset_closure (by simp)⟩, ⟨d, Subgroup.subset_closure (by simp)⟩,
      fun h => ?_⟩
    have h' : g * d = d * g := congrArg Subtype.val h
    have h1' : ⁅g, d⁆ = 1 := by
      rw [commutatorElement_def]
      calc g * d * g⁻¹ * d⁻¹ = d * g * g⁻¹ * d⁻¹ := by rw [h']
        _ = 1 := by group
    rw [hz] at h1'
    exact hc4 (inv_eq_one.1 h1')
  have hle : closure ({g, d} : Set G) ≤ centralizer ({c} : Set G) := by
    rw [Subgroup.closure_le]
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.2 hcg.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 hcd.symm
  have hcs : ∀ s ∈ closure ({g, d} : Set G), c * s = s * c := fun s hs =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hle hs)).symm
  have hcop : Nat.Coprime 4 p := (Nat.Prime.coprime_iff_not_dvd hp.out).2 hp4 |>.symm
  obtain ⟨j, -, hj⟩ : ∃ j < p, 4 * j % p = 1 :=
    Nat.exists_mul_mod_eq_one_of_coprime hcop hp.out.one_lt
  have hc4mem : c ^ 4 ∈ closure ({g, d} : Set G) := by
    have hcom : ⁅g, d⁆ ∈ closure ({g, d} : Set G) :=
      mul_mem (mul_mem (mul_mem (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))) (inv_mem (Subgroup.subset_closure (by simp))))
        (inv_mem (Subgroup.subset_closure (by simp)))
    rw [hz] at hcom
    simpa using inv_mem hcom
  have hcmem : c ∈ closure ({g, d} : Set G) := by
    have e : c = (c ^ 4) ^ j := by
      rw [← pow_mul]
      calc c = c ^ (4 * j % orderOf c) := by rw [hc, hj, pow_one]
        _ = c ^ (4 * j) := pow_mod_orderOf c _
    rw [e]
    exact pow_mem hc4mem j
  have hzx : Commute ⁅g, d⁆ g := by
    rw [hz]
    exact ((show Commute c g from hcg).pow_left 4).inv_left
  have hzy : Commute ⁅g, d⁆ d := by
    rw [hz]
    exact ((show Commute c d from hcd).pow_left 4).inv_left
  have hpG : IsPGroup p (closure ({g, d} : Set G)) :=
    CFSG.AGLEmbedding.Norton.MON11_13.isPGroup_closure_of_central_commutator hp.out hg hd hzx hzy
  have hsmall : ∀ T : Subgroup G, IsPGroup p T → ∃ m ≤ 3, Nat.card T = p ^ m := by
    intro T hT
    obtain ⟨n, hn⟩ := (isPGroup_iff_card_dvd_pow (p := p) (G := ↥T)).1 hT
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp.out).1 hn
    have hdvd : p ^ m ∣ Nat.card G := hm ▸ Subgroup.card_subgroup_dvd_card T
    refine ⟨m, ?_, hm⟩
    rw [← hG]
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp.out (Nat.card_pos).ne').1 hdvd
  obtain ⟨k, hk3, hkcard⟩ := hsmall _ hpG
  have hk3' : 3 ≤ k := by
    by_contra hlt
    obtain ⟨a, b, hab⟩ := hnc
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
    · have hsub : Subsingleton ↥(closure ({g, d} : Set G)) :=
        (Nat.card_eq_one_iff_unique.1 (by rw [hkcard, pow_zero])).1
      exact hab (Subsingleton.elim _ _)
    · haveI := isCyclic_of_prime_card (p := p) (by rw [hkcard, pow_one])
      exact hab (IsMulCommutative.is_comm.comm a b)
    · exact hab ((IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p)
        (G := ↥(closure ({g, d} : Set G))) (by rw [hkcard])).is_comm.comm a b)
  obtain rfl : k = 3 := by omega
  have hmax : ∀ T : Subgroup G, IsPGroup p T → closure ({g, d} : Set G) ≤ T →
      T = closure ({g, d} : Set G) := by
    intro T hT hle'
    obtain ⟨m, hm3, hmT⟩ := hsmall T hT
    exact (Subgroup.eq_of_le_of_card_ge hle'
      (by rw [hmT, hkcard]; exact Nat.pow_le_pow_right hp.out.pos hm3)).symm
  exact ⟨hpG, hmax, hkcard, hnc, hcmem, hcs⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13
