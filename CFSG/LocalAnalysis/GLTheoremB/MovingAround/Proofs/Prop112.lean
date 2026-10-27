module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec11Small
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma104b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma104c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input31
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf IsCompLocallyBalanced)
open scoped MatrixGroups Pointwise

section GroupLemmas

variable {G : Type} [Group G] [Finite G]

theorem factorization_card_eq_of_mul_pow {p j n : ℕ} (hp : p.Prime) (hn : Nat.Coprime p n) :
    (n * p ^ j).factorization p = j := by
  have hc : Nat.Coprime n (p ^ j) := Nat.Coprime.pow_right j hn.symm
  rw [Nat.factorization_mul_apply_of_coprime hc, Nat.Prime.factorization_pow hp]
  have h0 : n.factorization p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hn hd
  simp [h0]

theorem sylow_card_of_card_eq {p : ℕ} [hp : Fact p.Prime] {H N : Subgroup G} {j : ℕ}
    (hH : Nat.card H = Nat.card N * p ^ j) (hpN : Nat.Coprime p (Nat.card N))
    (Q : Sylow p H) : Nat.card Q = p ^ j := by
  rw [Sylow.card_eq_multiplicity, hH, factorization_card_eq_of_mul_pow hp.out hpN]

theorem mul_normal_cover {p : ℕ} (hp : p.Prime) {H N Q : Subgroup G}
    (hNH : N ≤ H) (hNn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hpN : Nat.Coprime p (Nat.card N))
    (hQH : Q ≤ H) (hQp : IsPGroup p Q) (hcard : Nat.card H = Nat.card N * Nat.card Q) :
    ∀ h ∈ H, ∃ q ∈ Q, ∃ n ∈ N, h = q * n := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hQp.exists_card_eq
  have hcop : Nat.Coprime (Nat.card Q) (Nat.card N) := by
    rw [hk]
    exact Nat.Coprime.pow_left k hpN
  have hdisj : Disjoint Q N := Subgroup.disjoint_of_coprime_natCard hcop
  let F : Q × N → H := fun x => ⟨(x.1 : G) * (x.2 : G),
    H.mul_mem (hQH x.1.2) (hNH x.2.2)⟩
  have hinj : Function.Injective F := by
    rintro ⟨q, n⟩ ⟨q', n'⟩ h
    have h' : (q : G) * (n : G) = (q' : G) * (n' : G) := congrArg Subtype.val h
    have e : (q' : G)⁻¹ * (q : G) = (n' : G) * (n : G)⁻¹ := by
      calc (q' : G)⁻¹ * (q : G) = ((q' : G)⁻¹ * ((q : G) * (n : G))) * (n : G)⁻¹ := by group
        _ = ((q' : G)⁻¹ * ((q' : G) * (n' : G))) * (n : G)⁻¹ := by rw [h']
        _ = (n' : G) * (n : G)⁻¹ := by group
    have hQ : (q' : G)⁻¹ * (q : G) ∈ Q ⊓ N := by
      refine ⟨Q.mul_mem (Q.inv_mem q'.2) q.2, ?_⟩
      rw [e]
      exact N.mul_mem n'.2 (N.inv_mem n.2)
    rw [hdisj.eq_bot, Subgroup.mem_bot] at hQ
    have hqq : (q : G) = q' := (inv_mul_eq_one.1 hQ).symm
    have hnn : (n : G) = n' := by
      have h2 : (n' : G) * (n : G)⁻¹ = 1 := by rw [← e, hQ]
      exact (mul_inv_eq_one.1 h2).symm
    exact Prod.ext (Subtype.ext hqq) (Subtype.ext hnn)
  have hcardQN : Nat.card (Q × N) = Nat.card H := by
    rw [Nat.card_prod, hcard, mul_comm]
  have hbij : Function.Bijective F :=
    hinj.bijective_of_nat_card_le (by rw [hcardQN])
  intro h hh
  obtain ⟨⟨q, n⟩, hqn⟩ := hbij.2 ⟨h, hh⟩
  refine ⟨q, q.2, n, n.2, ?_⟩
  exact (congrArg Subtype.val hqn).symm

theorem sylow_conj_of_normal {p : ℕ} [hp : Fact p.Prime] {H N : Subgroup G} {j : ℕ}
    (hNH : N ≤ H) (hNn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hpN : Nat.Coprime p (Nat.card N))
    (hH : Nat.card H = Nat.card N * p ^ j) (Q₁ Q₂ : Sylow p H) :
    ∃ n ∈ N, GLBConj n ((Q₂ : Subgroup H).map H.subtype) =
      (Q₁ : Subgroup H).map H.subtype := by
  have hall : MulAction.orbit H Q₁ = ⊤ := Sylow.orbit_eq_top Q₁
  have hmem : Q₂ ∈ MulAction.orbit H Q₁ := by rw [hall]; trivial
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 hmem
  have hQ₁card : Nat.card (Q₁ : Subgroup H) = p ^ j := sylow_card_of_card_eq hH hpN Q₁
  have hQ₁G : Nat.card ((Q₁ : Subgroup H).map H.subtype) = p ^ j := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hQ₁card]
  have hQ₁H : (Q₁ : Subgroup H).map H.subtype ≤ H := Subgroup.map_subtype_le _
  have hQ₁p : IsPGroup p ((Q₁ : Subgroup H).map H.subtype) := Q₁.isPGroup'.map H.subtype
  obtain ⟨q, hq, n, hn, hgqn⟩ := mul_normal_cover hp.out hNH hNn hpN hQ₁H hQ₁p
    (by rw [hH, hQ₁G]) (g : G) g.2
  have hn' : q * n * q⁻¹ ∈ N := hNn q (hQ₁H hq) n hn
  have hgeq : (g : G) = (q * n * q⁻¹) * q := by rw [hgqn]; group
  have hQ2 : (Q₂ : Subgroup H).map H.subtype =
      GLBConj (g : G)⁻¹ ((Q₁ : Subgroup H).map H.subtype) := by
    have h1 : (Q₂ : Subgroup H) = MulAut.conj g • (Q₁ : Subgroup H) := by
      rw [← hg, Sylow.coe_subgroup_smul]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [h1, SetLike.mem_coe, Subgroup.mem_smul_pointwise_iff_exists] at hz
      obtain ⟨s, hs, hsz⟩ := hz
      have hzG : ((z : H) : G) = (g : G) * (s : G) * (g : G)⁻¹ := by
        rw [← hsz]
        rfl
      show ((z : H) : G) ∈ _
      rw [mem_gLBConj, hzG]
      have e1 : (g : G)⁻¹ * ((g : G) * (s : G) * (g : G)⁻¹) * (g : G)⁻¹⁻¹ = (s : G) := by group
      rw [e1]
      exact Subgroup.mem_map.2 ⟨s, hs, rfl⟩
    · intro hy
      rw [mem_gLBConj] at hy
      obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.1 hy
      have hyeq : y = (g : G) * (s : G) * (g : G)⁻¹ := by
        rw [Subgroup.coe_subtype] at hsy
        calc y = (g : G) * ((g : G)⁻¹ * y * (g : G)⁻¹⁻¹) * (g : G)⁻¹ := by group
          _ = (g : G) * (s : G) * (g : G)⁻¹ := by rw [hsy]
      have hyH : y ∈ H := by
        rw [hyeq]
        exact H.mul_mem (H.mul_mem g.2 s.2) (H.inv_mem g.2)
      refine ⟨⟨y, hyH⟩, ?_, rfl⟩
      rw [h1, SetLike.mem_coe, Subgroup.mem_smul_pointwise_iff_exists]
      refine ⟨s, hs, ?_⟩
      apply Subtype.ext
      show (g : G) * (s : G) * (g : G)⁻¹ = y
      exact hyeq.symm
  refine ⟨q * n * q⁻¹, hn', ?_⟩
  rw [hQ2, gLBConj_gLBConj]
  have hinv : (g : G)⁻¹ * (q * n * q⁻¹) = q⁻¹ := by rw [hgeq]; group
  rw [hinv]
  exact gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (((Q₁ : Subgroup H).map H.subtype).inv_mem hq))

end GroupLemmas

section BarLemmas

variable {G : Type} [Group G] [Finite G]

theorem mem_glaPPrimeCoreOf_iff' {p : ℕ} {C : Subgroup G} {x : G} (hx : x ∈ C) :
    x ∈ GLAPPrimeCoreOf p C ↔ (⟨x, hx⟩ : ↥C) ∈ GLAPPrimeCore p ↥C := by
  constructor
  · intro h
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rw [← this]
    exact hy
  · intro h
    exact Subgroup.mem_map.2 ⟨⟨x, hx⟩, h, rfl⟩

theorem mem_glaPPrimeCoreOf_iff {p : ℕ} {C : Subgroup G} {x : G} (hx : x ∈ C) :
    x ∈ GLAPPrimeCoreOf p C ↔ QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hx⟩ = 1 := by
  rw [mem_glaPPrimeCoreOf_iff', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem mk_eq_mk_iff_mem {p : ℕ} {C : Subgroup G} {c d : G} (hc : c ∈ C) (hd : d ∈ C) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨c, hc⟩ : ↥C) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨d, hd⟩ ↔ c⁻¹ * d ∈ GLAPPrimeCoreOf p C := by
  have hcd : c⁻¹ * d ∈ C := C.mul_mem (C.inv_mem hc) hd
  have e : (⟨c, hc⟩ : ↥C)⁻¹ * ⟨d, hd⟩ = ⟨c⁻¹ * d, hcd⟩ := Subtype.ext (by simp)
  rw [mem_glaPPrimeCoreOf_iff' hcd, ← e, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq]

theorem barX_mono {p : ℕ} {C K K' : Subgroup G} (h : K ≤ K') : barX p C K ≤ barX p C K' := by
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨c, Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hc)), rfl⟩

theorem card_eq_card_inter_mul_card_barX {p : ℕ} (hp : p.Prime) {C H : Subgroup G} (hHC : H ≤ C) :
    Nat.card H = Nat.card (GLAPPrimeCoreOf p C ⊓ H : Subgroup G) * Nat.card (barX p C H) := by
  let f : H →* (↥C ⧸ GLAPPrimeCore p ↥C) :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (Subgroup.inclusion hHC)
  have hrange : f.range = barX p C H := by
    ext z
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨⟨(h : G), hHC h.2⟩, (Subgroup.mem_subgroupOf).2 h.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨(c : G), (Subgroup.mem_subgroupOf).1 hc⟩, rfl⟩
  have hker : (f.ker.map H.subtype : Subgroup G) = GLAPPrimeCoreOf p C ⊓ H := by
    ext x
    constructor
    · rintro ⟨h, hh, rfl⟩
      have hh1 : QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨(h : G), hHC h.2⟩ : ↥C) = 1 := hh
      exact ⟨(mem_glaPPrimeCoreOf_iff (hHC h.2)).2 hh1, h.2⟩
    · rintro ⟨hxO, hxH⟩
      refine ⟨⟨x, hxH⟩, ?_, rfl⟩
      exact (mem_glaPPrimeCoreOf_iff (hHC hxH)).1 hxO
  have h1 : Nat.card (f.ker) = Nat.card (GLAPPrimeCoreOf p C ⊓ H : Subgroup G) := by
    rw [← hker, Subgroup.card_map_of_injective H.subtype_injective]
  have h2 : Nat.card (H ⧸ f.ker) = Nat.card (barX p C H) := by
    rw [← hrange]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker, h1, h2]
  ring

theorem coprime_inter_O {p : ℕ} [Fact p.Prime] (C H : Subgroup G) :
    Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p C ⊓ H : Subgroup G)) :=
  Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
    (sec11_glaPPrimeCoreOf_coprime C)

theorem sylow_barX_cover {p : ℕ} [hp : Fact p.Prime] {C H : Subgroup G} (hHC : H ≤ C)
    (hH : IsPGroup p ↥(barX p C H)) (Q : Sylow p H) :
    ∀ h ∈ H, ∃ q ∈ (Q : Subgroup H).map H.subtype, ∃ n ∈ GLAPPrimeCoreOf p C, h = q * n := by
  obtain ⟨j, hj⟩ := hH.exists_card_eq
  have hcardH := card_eq_card_inter_mul_card_barX hp.out hHC
  have hcop := coprime_inter_O (p := p) C H
  have hH' : Nat.card H = Nat.card (GLAPPrimeCoreOf p C ⊓ H : Subgroup G) * p ^ j := by
    rw [hcardH, hj]
  have hQcard : Nat.card (Q : Subgroup H) = p ^ j := sylow_card_of_card_eq hH' hcop Q
  have hQ'card : Nat.card ((Q : Subgroup H).map H.subtype) = p ^ j := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hQcard]
  have hNH : (GLAPPrimeCoreOf p C ⊓ H : Subgroup G) ≤ H := inf_le_right
  have hNn : ∀ h ∈ H, ∀ n ∈ (GLAPPrimeCoreOf p C ⊓ H : Subgroup G),
      h * n * h⁻¹ ∈ (GLAPPrimeCoreOf p C ⊓ H : Subgroup G) := by
    intro h hh n hn
    exact Subgroup.mem_inf.2 ⟨sec11_glaPPrimeCoreOf_conj_mem (hHC hh) (Subgroup.mem_inf.1 hn).1,
      H.mul_mem (H.mul_mem hh (Subgroup.mem_inf.1 hn).2) (H.inv_mem hh)⟩
  have hQH : (Q : Subgroup H).map H.subtype ≤ H := Subgroup.map_subtype_le _
  have hQp : IsPGroup p ((Q : Subgroup H).map H.subtype) := Q.isPGroup'.map H.subtype
  intro h hh
  obtain ⟨q, hq, n, hn, hqn⟩ := mul_normal_cover hp.out hNH hNn hcop hQH hQp
    (by rw [hH', hQ'card]) h hh
  exact ⟨q, hq, n, (Subgroup.mem_inf.1 hn).1, hqn⟩

theorem barX_sylow_eq {p : ℕ} [hp : Fact p.Prime] {C H : Subgroup G} (hHC : H ≤ C)
    (hH : IsPGroup p ↥(barX p C H)) (Q : Sylow p H) :
    barX p C ((Q : Subgroup H).map H.subtype) = barX p C H := by
  apply le_antisymm
  · exact barX_mono (Subgroup.map_subtype_le _)
  · rintro z ⟨c, hc, rfl⟩
    have hcH : (c : G) ∈ H := Subgroup.mem_subgroupOf.1 hc
    obtain ⟨q, hq, n, hn, hqn⟩ := sylow_barX_cover hHC hH Q (c : G) hcH
    have hqC : (q : G) ∈ C := hHC (Subgroup.map_subtype_le _ hq)
    refine ⟨⟨q, hqC⟩, Subgroup.mem_subgroupOf.2 hq, ?_⟩
    show QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨(q : G), hqC⟩ : ↥C) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥C) (c : ↥C)
    rw [mk_eq_mk_iff_mem hqC (c : ↥C).2]
    have : (q : G)⁻¹ * (c : G) = n := by rw [hqn]; group
    rw [this]
    exact hn

end BarLemmas

section Lifting

variable {G : Type} [Group G] [Finite G]

def preimOf {p : ℕ} (C : Subgroup G) (W : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) : Subgroup G :=
  ((W.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥C))).map C.subtype)

theorem barX_preimOf {p : ℕ} (C : Subgroup G) (W : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) :
    barX p C (preimOf (p := p) C W) = W := by
  apply le_antisymm
  · rintro z ⟨c, hc, rfl⟩
    obtain ⟨d, hd, hdc⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hc)
    have hdc' : d = c := Subtype.ext hdc
    rw [← hdc']
    exact Subgroup.mem_comap.1 hd
  · intro w hw
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥C) w
    exact ⟨c, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨c, Subgroup.mem_comap.2 hw, rfl⟩), rfl⟩

theorem exists_sylow_above {p : ℕ} [Fact p.Prime] {H U : Subgroup G} (hUH : U ≤ H)
    (hU : IsPGroup p U) : ∃ Q : Sylow p H, U ≤ (Q : Subgroup H).map H.subtype := by
  have hUH' : IsPGroup p ↥(U.subgroupOf H) := hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUH).symm
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hUH'
  refine ⟨Q, fun u hu => ?_⟩
  exact Subgroup.mem_map.2 ⟨⟨u, hUH hu⟩, hQ (Subgroup.mem_subgroupOf.2 hu), rfl⟩

theorem isPGroup_barX_of_le {p : ℕ} {C S : Subgroup G} (hSC : S ≤ C) (hS : IsPGroup p S) :
    IsPGroup p ↥(barX p C S) := by
  unfold barX
  exact (hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSC).symm).map _

theorem card_barX_of_le {p : ℕ} (hp : p.Prime) {C S : Subgroup G} (hSC : S ≤ C)
    (hS : IsPGroup p S) : Nat.card (barX p C S) = Nat.card S := by
  set f := (QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (S.subgroupOf C).subtype with hf
  have hfi := injective_barX_comp hp hS hSC
  have hrange : barX p C S = (⊤ : Subgroup ↥(S.subgroupOf C)).map f := by
    rw [hf, ← Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype]
    rfl
  rw [hrange, Subgroup.card_map_of_injective hfi, Subgroup.card_top]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv

theorem exists_conj_commute {p : ℕ} [hp : Fact p.Prime] {C U V : Subgroup G} (hUC : U ≤ C)
    (hVC : V ≤ C) (hU : IsPGroup p U) (hV : IsPGroup p V)
    (hcomm : barX p C U ≤ Subgroup.centralizer ((barX p C V : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) :
      Set (↥C ⧸ GLAPPrimeCore p ↥C))) :
    ∃ x ∈ GLAPPrimeCoreOf p C, ∀ u ∈ U, ∀ w ∈ GLBConj x V, u * w = w * u := by
  set W := barX p C U ⊔ barX p C V with hW
  set H := preimOf (p := p) C W with hH
  have hHC : H ≤ C := Subgroup.map_subtype_le _
  have hbarH : barX p C H = W := barX_preimOf C W
  have hWp : IsPGroup p ↥W :=
    isPGroup_sup_of_commute (isPGroup_barX_of_le hUC hU) (isPGroup_barX_of_le hVC hV) hcomm
  have hHp : IsPGroup p ↥(barX p C H) := by rw [hbarH]; exact hWp
  have hUH : U ≤ H := by
    intro u hu
    refine Subgroup.mem_map.2 ⟨⟨u, hUC hu⟩, ?_, rfl⟩
    exact Subgroup.mem_comap.2 (Subgroup.mem_sup_left ⟨⟨u, hUC hu⟩, Subgroup.mem_subgroupOf.2 hu, rfl⟩)
  have hVH : V ≤ H := by
    intro v hv
    refine Subgroup.mem_map.2 ⟨⟨v, hVC hv⟩, ?_, rfl⟩
    exact Subgroup.mem_comap.2 (Subgroup.mem_sup_right ⟨⟨v, hVC hv⟩, Subgroup.mem_subgroupOf.2 hv, rfl⟩)
  obtain ⟨Q₁, hQ₁⟩ := exists_sylow_above hUH hU
  obtain ⟨Q₂, hQ₂⟩ := exists_sylow_above hVH hV
  obtain ⟨j, hj⟩ := hHp.exists_card_eq
  have hcardH : Nat.card H = Nat.card (GLAPPrimeCoreOf p C ⊓ H : Subgroup G) * p ^ j := by
    rw [card_eq_card_inter_mul_card_barX hp.out hHC, hj]
  have hNH : (GLAPPrimeCoreOf p C ⊓ H : Subgroup G) ≤ H := inf_le_right
  have hNn : ∀ h ∈ H, ∀ n ∈ (GLAPPrimeCoreOf p C ⊓ H : Subgroup G),
      h * n * h⁻¹ ∈ (GLAPPrimeCoreOf p C ⊓ H : Subgroup G) := by
    intro h hh n hn
    exact Subgroup.mem_inf.2 ⟨sec11_glaPPrimeCoreOf_conj_mem (hHC hh) (Subgroup.mem_inf.1 hn).1,
      H.mul_mem (H.mul_mem hh (Subgroup.mem_inf.1 hn).2) (H.inv_mem hh)⟩
  obtain ⟨n, hn, hconj⟩ := sylow_conj_of_normal hNH hNn (coprime_inter_O C H) hcardH Q₁ Q₂
  have hnO : n ∈ GLAPPrimeCoreOf p C := (Subgroup.mem_inf.1 hn).1
  refine ⟨n, hnO, ?_⟩
  intro u hu w hw
  set Q₁' := (Q₁ : Subgroup H).map H.subtype with hQ₁'
  have hQ1C : Q₁' ≤ C := (Subgroup.map_subtype_le _).trans hHC
  have hQ1p : IsPGroup p Q₁' := Q₁.isPGroup'.map H.subtype
  have hwQ1 : w ∈ Q₁' := by
    have hle : GLBConj n V ≤ GLBConj n ((Q₂ : Subgroup H).map H.subtype) :=
      gLBConj_mono n hQ₂
    rw [hconj] at hle
    exact hle hw
  have huQ1 : u ∈ Q₁' := hQ₁ hu
  have hwC : w ∈ C := hQ1C hwQ1
  have huC : u ∈ C := hUC hu
  have hwbar : QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨w, hwC⟩ : ↥C) ∈ barX p C V := by
    have hmem : (⟨w, hwC⟩ : ↥C) ∈ (GLBConj n V).subgroupOf C := Subgroup.mem_subgroupOf.2 hw
    have hmem' : QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨w, hwC⟩ : ↥C) ∈
        barX p C (GLBConj n V) := Subgroup.mem_map.2 ⟨⟨w, hwC⟩, hmem, rfl⟩
    rw [barX_gLBConj_of_mem p hnO V] at hmem'
    exact hmem'
  have hubar : QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨u, huC⟩ : ↥C) ∈ barX p C U :=
    Subgroup.mem_map.2 ⟨⟨u, huC⟩, Subgroup.mem_subgroupOf.2 hu, rfl⟩
  have hcomm' := Subgroup.mem_centralizer_iff.1 (hcomm hubar)
    (QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨w, hwC⟩ : ↥C)) hwbar
  have key := injective_barX_comp hp.out hQ1p hQ1C
  have hfeq : (QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (Q₁'.subgroupOf C).subtype
      ⟨⟨u * w, C.mul_mem huC hwC⟩, Subgroup.mem_subgroupOf.2 (Q₁'.mul_mem huQ1 hwQ1)⟩ =
    (QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (Q₁'.subgroupOf C).subtype
      ⟨⟨w * u, C.mul_mem hwC huC⟩, Subgroup.mem_subgroupOf.2 (Q₁'.mul_mem hwQ1 huQ1)⟩ := by
    show QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨u * w, C.mul_mem huC hwC⟩ : ↥C) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨w * u, C.mul_mem hwC huC⟩ : ↥C)
    rw [show (⟨u * w, C.mul_mem huC hwC⟩ : ↥C) = ⟨u, huC⟩ * ⟨w, hwC⟩ from rfl,
      show (⟨w * u, C.mul_mem hwC huC⟩ : ↥C) = ⟨w, hwC⟩ * ⟨u, huC⟩ from rfl, map_mul, map_mul]
    exact hcomm'.symm
  have hx := key hfeq
  exact congrArg (fun x : Q₁'.subgroupOf C => ((x : ↥C) : G)) hx

theorem exists_conj_of_barX_eq {p : ℕ} [hp : Fact p.Prime] {C S T : Subgroup G} (hSC : S ≤ C)
    (hTC : T ≤ C) (hS : IsPGroup p S) (hT : IsPGroup p T) (hST : barX p C S = barX p C T) :
    ∃ x ∈ GLAPPrimeCoreOf p C, GLBConj x S = T := by
  set W := barX p C S with hWdef
  set H := preimOf (p := p) C W with hH
  have hHC : H ≤ C := Subgroup.map_subtype_le _
  have hbarH : barX p C H = W := barX_preimOf C W
  have hSH : S ≤ H := by
    intro s hs
    exact Subgroup.mem_map.2 ⟨⟨s, hSC hs⟩, Subgroup.mem_comap.2
      (Subgroup.mem_map.2 ⟨⟨s, hSC hs⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩), rfl⟩
  have hTH : T ≤ H := by
    intro t ht
    refine Subgroup.mem_map.2 ⟨⟨t, hTC ht⟩, Subgroup.mem_comap.2 ?_, rfl⟩
    rw [hST]
    exact Subgroup.mem_map.2 ⟨⟨t, hTC ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
  have hHp : IsPGroup p ↥(barX p C H) := by rw [hbarH]; exact isPGroup_barX_of_le hSC hS
  obtain ⟨Q₁, hQ₁⟩ := exists_sylow_above hSH hS
  obtain ⟨Q₂, hQ₂⟩ := exists_sylow_above hTH hT
  obtain ⟨j, hj⟩ := hHp.exists_card_eq
  have hcardH : Nat.card H = Nat.card (GLAPPrimeCoreOf p C ⊓ H : Subgroup G) * p ^ j := by
    rw [card_eq_card_inter_mul_card_barX hp.out hHC, hj]
  have hNH : (GLAPPrimeCoreOf p C ⊓ H : Subgroup G) ≤ H := inf_le_right
  have hNn : ∀ h ∈ H, ∀ n ∈ (GLAPPrimeCoreOf p C ⊓ H : Subgroup G),
      h * n * h⁻¹ ∈ (GLAPPrimeCoreOf p C ⊓ H : Subgroup G) := by
    intro h hh n hn
    exact Subgroup.mem_inf.2 ⟨sec11_glaPPrimeCoreOf_conj_mem (hHC hh) (Subgroup.mem_inf.1 hn).1,
      H.mul_mem (H.mul_mem hh (Subgroup.mem_inf.1 hn).2) (H.inv_mem hh)⟩
  obtain ⟨n, hn, hconj⟩ := sylow_conj_of_normal hNH hNn (coprime_inter_O C H) hcardH Q₁ Q₂
  have hQ1C : (Q₁ : Subgroup H).map H.subtype ≤ C := (Subgroup.map_subtype_le _).trans hHC
  have hQ2C : (Q₂ : Subgroup H).map H.subtype ≤ C := (Subgroup.map_subtype_le _).trans hHC
  have hQ1p : IsPGroup p ((Q₁ : Subgroup H).map H.subtype) := Q₁.isPGroup'.map H.subtype
  have hQ2p : IsPGroup p ((Q₂ : Subgroup H).map H.subtype) := Q₂.isPGroup'.map H.subtype
  have hQ1bar : barX p C ((Q₁ : Subgroup H).map H.subtype) = W :=
    (barX_sylow_eq hHC hHp Q₁).trans hbarH
  have hQ2bar : barX p C ((Q₂ : Subgroup H).map H.subtype) = W :=
    (barX_sylow_eq hHC hHp Q₂).trans hbarH
  have hSeq : S = (Q₁ : Subgroup H).map H.subtype := by
    apply Subgroup.eq_of_le_of_card_ge hQ₁
    rw [← card_barX_of_le hp.out hQ1C hQ1p, hQ1bar, ← card_barX_of_le hp.out hSC hS, hWdef]
  have hTeq : T = (Q₂ : Subgroup H).map H.subtype := by
    apply Subgroup.eq_of_le_of_card_ge hQ₂
    rw [← card_barX_of_le hp.out hQ2C hQ2p, hQ2bar, hST, ← card_barX_of_le hp.out hTC hT]
  have hnO : n ∈ GLAPPrimeCoreOf p C := (Subgroup.mem_inf.1 hn).1
  refine ⟨n⁻¹, (GLAPPrimeCoreOf p C).inv_mem hnO, ?_⟩
  rw [hSeq, ← hconj, gLBConj_gLBConj, mul_inv_cancel, gLBConj_one, hTeq]

theorem exists_lift_elemAbelian {p : ℕ} [hp : Fact p.Prime] {C : Subgroup G}
    {W : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)} (hW : CFSG.Open.IsElemAbelian p W) :
    ∃ S : Subgroup G, S ≤ C ∧ CFSG.Open.IsElemAbelian p S ∧ barX p C S = W ∧
      Nat.card S = Nat.card W := by
  have hN : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥C) := by
    have h1 : Nat.card (GLAPPrimeCore p ↥C) = Nat.card (GLAPPrimeCoreOf p C : Subgroup G) := by
      unfold GLAPPrimeCoreOf
      rw [Subgroup.card_map_of_injective C.subtype_injective]
    rw [h1]
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 (sec11_glaPPrimeCoreOf_coprime C)
  obtain ⟨S', hS'el, hS'map, hS'card⟩ := exists_elemAbelian_lift (GLAPPrimeCore p ↥C) hN hW
  refine ⟨S'.map C.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · exact CFSG.SectionRank.isElemAbelian_map hS'el _
  · have h1 : (S'.map C.subtype).subgroupOf C = S' := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = x := Subtype.ext hyx
        rw [← this]
        exact hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    unfold barX
    rw [h1, hS'map]
  · rw [Subgroup.card_map_of_injective C.subtype_injective, hS'card]

end Lifting



section Connected

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_gLBConj {p : ℕ} {S : Subgroup G} (x : G)
    (hS : CFSG.Open.IsElemAbelian p S) : CFSG.Open.IsElemAbelian p (GLBConj x S) :=
  CFSG.SectionRank.isElemAbelian_map hS _

theorem card_gLBConj (x : G) (S : Subgroup G) : Nat.card (GLBConj x S) = Nat.card S := by
  unfold GLBConj
  exact Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective

theorem isEkIn_top_gLBConj {p : ℕ} {S : Subgroup G} (x : G) (hS : IsEkIn p 3 ⊤ S) :
    IsEkIn p 3 ⊤ (GLBConj x S) :=
  ⟨le_top, isElemAbelian_gLBConj x hS.2.1, by rw [card_gLBConj, hS.2.2]⟩

theorem exists_isEkIn_three_le {p : ℕ} [hp : Fact p.Prime] {B : Subgroup G}
    (hB : CFSG.Open.IsElemAbelian p B) (hB3 : p ^ 3 ≤ Nat.card B) :
    ∃ W : Subgroup G, W ≤ B ∧ IsEkIn p 3 ⊤ W := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card B = p ^ k :=
    exists_card_eq_pow (fun x => ⟨1, Subtype.ext (by simpa using hB.2 x x.2)⟩)
  have h3 : 3 ≤ k := by
    rw [hk] at hB3
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hB3
  obtain ⟨W, hWB, hWel, hWcard⟩ :=
    exists_elemAbelian_card_pow_of_le_pRank' (p := p) (H := B) (k := 3)
      (h3.trans (CFSG.SectionRank.le_pRank hp.out.one_lt le_rfl hB hk))
  exact ⟨W, hWB, le_top, hWel, hWcard⟩

theorem gLBConj_le_of_mem {C S : Subgroup G} {x : G} (hx : x ∈ C) (hS : S ≤ C) :
    GLBConj x S ≤ C := by
  have h1 : GLBConj x S ≤ GLBConj x C := gLBConj_mono x hS
  rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hx)] at h1

theorem isKConnStep_symm {p k : ℕ} {X U V : Subgroup G} (h : IsKConnStep p k X U V) :
    IsKConnStep p k X V U :=
  ⟨h.2.1, h.1, fun v hv => Subgroup.mem_centralizer_iff.2 fun u hu =>
    (Subgroup.mem_centralizer_iff.1 (h.2.2 hu) v hv).symm⟩

theorem le_centralizer_of_forall {S T : Subgroup G} (h : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    S ≤ Subgroup.centralizer (T : Set G) :=
  fun s hs => Subgroup.mem_centralizer_iff.2 fun t ht => (h s hs t ht).symm

theorem isKConnectedIn_symm' {p k : ℕ} {A B : Subgroup G} (h : IsKConnectedIn p k ⊤ A B) :
    IsKConnectedIn p k ⊤ B A := by
  obtain ⟨hA, hAel, hAc, hB, hBel, hBc, hcases⟩ := h
  refine ⟨hB, hBel, hBc, hA, hAel, hAc, ?_⟩
  rcases hcases with h1 | ⟨U, V, hU, hV, hAU, hr, hVB⟩
  · exact Or.inl (le_centralizer_of_forall fun b hb a ha =>
      (Subgroup.mem_centralizer_iff.1 (h1 ha)) b hb)
  · refine Or.inr ⟨V, U, hV, hU, ?_, input31_reflTransGen_symm
      (fun a b hab => isKConnStep_symm hab) hr, ?_⟩
    · exact le_centralizer_of_forall fun b hb v hv =>
        (Subgroup.mem_centralizer_iff.1 (hVB hv)) b hb
    · exact le_centralizer_of_forall fun u hu a ha =>
        (Subgroup.mem_centralizer_iff.1 (hAU ha)) u hu

theorem isKConnectedIn_extend {p : ℕ} [hp : Fact p.Prime] {A B B' : Subgroup G}
    (h : IsKConnectedIn p 3 ⊤ A B) (hBB' : B ≤ B') (hB' : CFSG.Open.IsElemAbelian p B') :
    IsKConnectedIn p 3 ⊤ A B' := by
  obtain ⟨hA, hAel, hAc, hB, hBel, hBc, hcases⟩ := h
  obtain ⟨W, hWB, hW⟩ := exists_isEkIn_three_le hBel hBc
  have hcommB : ∀ x ∈ B, ∀ y ∈ B', x * y = y * x := fun x hx y hy =>
    elemAbelian_comm hB' (hBB' hx) hy
  refine ⟨hA, hAel, hAc, le_top, hB', ?_, ?_⟩
  · exact le_trans hBc (Subgroup.card_le_of_le hBB')
  · rcases hcases with h1 | ⟨U, V, hU, hV, hAU, hr, hVB⟩
    · have h3A : p ^ 3 ≤ Nat.card A := hAc
      obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card A = p ^ k :=
        exists_card_eq_pow (fun x => ⟨1, Subtype.ext (by simpa using hAel.2 x x.2)⟩)
      have h3 : 3 ≤ k := by
        rw [hk] at h3A
        exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 h3A
      obtain ⟨U₁, hU₁A, hU₁el, hU₁c⟩ :=
        exists_elemAbelian_card_pow_of_le_pRank' (p := p) (H := A) (k := 3)
          (h3.trans (CFSG.SectionRank.le_pRank hp.out.one_lt le_rfl hAel hk))
      have hU₁ : IsEkIn p 3 ⊤ U₁ := ⟨le_top, hU₁el, hU₁c⟩
      refine Or.inr ⟨U₁, W, hU₁, hW, ?_, Relation.ReflTransGen.single ⟨hU₁, hW, ?_⟩, ?_⟩
      · exact le_centralizer_of_forall fun a ha u hu => elemAbelian_comm hAel ha (hU₁A hu)
      · exact le_centralizer_of_forall fun u hu w hw =>
          (Subgroup.mem_centralizer_iff.1 (h1 (hU₁A hu)) w (hWB hw)).symm
      · exact le_centralizer_of_forall fun w hw b' hb' => hcommB w (hWB hw) b' hb'
    · refine Or.inr ⟨U, W, hU, hW, hAU, hr.tail ⟨hV, hW, ?_⟩, ?_⟩
      · exact le_centralizer_of_forall fun v hv w hw =>
          (Subgroup.mem_centralizer_iff.1 (hVB hv) w (hWB hw)).symm
      · exact le_centralizer_of_forall fun w hw b' hb' => hcommB w (hWB hw) b' hb'

theorem chain_lift {p : ℕ} [hp : Fact p.Prime] {C : Subgroup G}
    {Ub Vb : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)}
    (h : Relation.ReflTransGen (IsKConnStep p 3 ⊤) Ub Vb) :
    ∀ Ut : Subgroup G, Ut ≤ C → IsEkIn p 3 ⊤ Ut → barX p C Ut = Ub →
      ∃ Vt : Subgroup G, Vt ≤ C ∧ IsEkIn p 3 ⊤ Vt ∧ barX p C Vt = Vb ∧
        Relation.ReflTransGen (IsKConnStep p 3 ⊤) Ut Vt := by
  induction h with
  | refl =>
    intro Ut hC hE hb
    exact ⟨Ut, hC, hE, hb, Relation.ReflTransGen.refl⟩
  | @tail X Y hXY hstep ih =>
    intro Ut hC hE hb
    obtain ⟨Vt', hC', hE', hb', hr'⟩ := ih Ut hC hE hb
    obtain ⟨S₀, hS₀C, hS₀el, hS₀bar, hS₀card⟩ :=
      exists_lift_elemAbelian (C := C) (W := Y) hstep.2.1.2.1
    have hS₀E : IsEkIn p 3 ⊤ S₀ := ⟨le_top, hS₀el, by rw [hS₀card, hstep.2.1.2.2]⟩
    have hcomm : barX p C Vt' ≤ Subgroup.centralizer ((barX p C S₀ : Subgroup _) : Set _) := by
      rw [hb', hS₀bar]
      exact hstep.2.2
    have hp1 : IsPGroup p Vt' := isPGroup_of_isElemAbelian' hE'.2.1
    have hp2 : IsPGroup p S₀ := isPGroup_of_isElemAbelian' hS₀el
    obtain ⟨x, hx, hxcomm⟩ := exists_conj_commute hC' hS₀C hp1 hp2 hcomm
    have hxC : x ∈ C := (sec11_glaPPrimeCoreOf_le C) hx
    refine ⟨GLBConj x S₀, gLBConj_le_of_mem hxC hS₀C, isEkIn_top_gLBConj x hS₀E,
      ?_, ?_⟩
    · rw [barX_gLBConj_of_mem p hx S₀, hS₀bar]
    · apply Relation.ReflTransGen.tail hr'
      refine ⟨hE', isEkIn_top_gLBConj x hS₀E, ?_⟩
      exact le_centralizer_of_forall fun u hu w hw => hxcomm u hu w hw

theorem kconn_lift {p : ℕ} [hp : Fact p.Prime] {C E : Subgroup G}
    {Eb Es : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)} (hEC : E ≤ C) (hEbar : barX p C E = Eb)
    (hE : CFSG.Open.IsElemAbelian p E) (hconn : IsKConnectedIn p 3 ⊤ Eb Es) :
    ∃ Ets : Subgroup G, Ets ≤ C ∧ barX p C Ets = Es ∧ CFSG.Open.IsElemAbelian p Ets ∧
      Nat.card Ets = Nat.card Es ∧ IsKConnectedIn p 3 ⊤ E Ets := by
  obtain ⟨-, -, hEbc, -, hEsel, hEsc, hcases⟩ := hconn
  have hEp : IsPGroup p E := isPGroup_of_isElemAbelian' hE
  have hEc : p ^ 3 ≤ Nat.card E := by
    rw [← card_barX_of_le hp.out hEC hEp, hEbar]
    exact hEbc
  obtain ⟨Es₀, hEs₀C, hEs₀el, hEs₀bar, hEs₀card⟩ :=
    exists_lift_elemAbelian (C := C) (W := Es) hEsel
  have hEs₀p : IsPGroup p Es₀ := isPGroup_of_isElemAbelian' hEs₀el
  rcases hcases with h1 | ⟨U, V, hU, hV, hEbU, hUV, hVEs⟩
  · have hcomm : barX p C E ≤ Subgroup.centralizer ((barX p C Es₀ : Subgroup _) : Set _) := by
      rw [hEbar, hEs₀bar]
      exact h1
    obtain ⟨x, hx, hxc⟩ := exists_conj_commute hEC hEs₀C hEp hEs₀p hcomm
    have hxC : x ∈ C := (sec11_glaPPrimeCoreOf_le C) hx
    refine ⟨GLBConj x Es₀, gLBConj_le_of_mem hxC hEs₀C, ?_, isElemAbelian_gLBConj x hEs₀el,
      ?_, ?_⟩
    · rw [barX_gLBConj_of_mem p hx Es₀, hEs₀bar]
    · rw [card_gLBConj, hEs₀card]
    · refine ⟨le_top, hE, hEc, le_top, isElemAbelian_gLBConj x hEs₀el, ?_, Or.inl ?_⟩
      · rw [card_gLBConj, hEs₀card]
        exact hEsc
      · exact le_centralizer_of_forall fun e he w hw => hxc e he w hw
  · obtain ⟨U₀, hU₀C, hU₀el, hU₀bar, hU₀card⟩ :=
      exists_lift_elemAbelian (C := C) (W := U) hU.2.1
    have hU₀p : IsPGroup p U₀ := isPGroup_of_isElemAbelian' hU₀el
    have hcomm1 : barX p C E ≤ Subgroup.centralizer ((barX p C U₀ : Subgroup _) : Set _) := by
      rw [hEbar, hU₀bar]
      exact hEbU
    obtain ⟨x₁, hx₁, hx₁c⟩ := exists_conj_commute hEC hU₀C hEp hU₀p hcomm1
    have hx₁C : x₁ ∈ C := (sec11_glaPPrimeCoreOf_le C) hx₁
    have hUtE : IsEkIn p 3 ⊤ (GLBConj x₁ U₀) :=
      isEkIn_top_gLBConj x₁ ⟨le_top, hU₀el, by rw [hU₀card, hU.2.2]⟩
    have hUtC : GLBConj x₁ U₀ ≤ C := gLBConj_le_of_mem hx₁C hU₀C
    have hUtbar : barX p C (GLBConj x₁ U₀) = U := by
      rw [barX_gLBConj_of_mem p hx₁ U₀, hU₀bar]
    obtain ⟨Vt, hVtC, hVtE, hVtbar, hr⟩ := chain_lift hUV (GLBConj x₁ U₀) hUtC hUtE hUtbar
    have hcomm2 : barX p C Vt ≤ Subgroup.centralizer ((barX p C Es₀ : Subgroup _) : Set _) := by
      rw [hVtbar, hEs₀bar]
      exact hVEs
    obtain ⟨x₂, hx₂, hx₂c⟩ :=
      exists_conj_commute hVtC hEs₀C (isPGroup_of_isElemAbelian' hVtE.2.1) hEs₀p hcomm2
    have hx₂C : x₂ ∈ C := (sec11_glaPPrimeCoreOf_le C) hx₂
    refine ⟨GLBConj x₂ Es₀, gLBConj_le_of_mem hx₂C hEs₀C, ?_, isElemAbelian_gLBConj x₂ hEs₀el,
      ?_, ?_⟩
    · rw [barX_gLBConj_of_mem p hx₂ Es₀, hEs₀bar]
    · rw [card_gLBConj, hEs₀card]
    · refine ⟨le_top, hE, hEc, le_top, isElemAbelian_gLBConj x₂ hEs₀el, ?_, ?_⟩
      · rw [card_gLBConj, hEs₀card]
        exact hEsc
      · refine Or.inr ⟨GLBConj x₁ U₀, Vt, hUtE, hVtE, ?_, hr, ?_⟩
        · exact le_centralizer_of_forall fun e he w hw => hx₁c e he w hw
        · exact le_centralizer_of_forall fun v hv w hw => hx₂c v hv w hw

end Connected

@[expose] def Input27_3 : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    GLAPPrimeCore p X = ⊥ → ∀ K : Subgroup X, GLAPComponent p ⊤ K →
    CFSG.LocalAnalysis.GLTheoremA.IsKHat ↥K →
    ∀ E A : Subgroup X, IsSCp p ⊤ E → IsSCp p ⊤ A → E ≠ A → IsPGroup p ↥(E ⊔ A) →
      2 ≤ CFSG.Open.pRank p (E ⊓ A) →
      Subgroup.centralizer ((GLALayer (⊤ : Subgroup X) : Subgroup X) : Set X) ⊓ (E ⊓ A) ≠ ⊥ →
      (∃ Es : Subgroup X, IsSCp p ⊤ Es ∧ 3 ≤ CFSG.Open.pRank p Es ∧
          IsKConnectedIn p 3 ⊤ E Es ∧ K ≤ GLBCore p 2 Es) ∨
      IsKConnectedIn p 3 ⊤ E A ∨
      (∃ y ∈ GLBCore p 2 E, GLBConj y E = A) ∨
      (CFSG.Open.pRank p E = 3 ∧ 3 < CFSG.Open.pRank p A) ∨
      (p = 3 ∧ CFSG.Open.pRank p E = 3) ∨
      (p = 3 ∧ Nat.card E = 3 ^ 4 ∧ Nat.card A = 3 ^ 3 ∧ IsLTwoTwentySeven ↥K) ∨
      IsCompLocallyBalanced p 1 A K

@[expose] def Input19_1_3Gen : Prop :=
  ∀ (p k : ℕ), p.Prime → 1 ≤ k → ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    GLAPPrimeCore p X = ⊥ → ∀ B D : Subgroup X, IsElemAbelian p B → IsEkIn p k B D → D ≤ B →
    ∀ K : Subgroup X, GLAPComponent p ⊤ K → IsCompLocallyBalanced p k B K →
    ∀ d ∈ GLADelta p D, ∀ x ∈ K, d * x = x * d

@[expose] def Lemma113_iiClosed : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G}, Sec11 G m 3 B M E A →
    ∀ {a : G}, a ∈ A → a ≠ 1 → (¬ ∃ A1 : Subgroup G, inD 3 M A1 ∧ a ∈ A1) →
    CFSG.Open.pRank 3 E = 4 → CFSG.Open.pRank 3 A = 3 →
    ∀ e ∈ E ⊓ A, e ≠ 1 → ∀ K : Subgroup G, GLAPComponent 3 (Cg e) K →
      ¬ IsLTwoTwentySeven (barOf 3 K)

section SmallFacts

variable {G : Type} [Group G] [Finite G]

theorem pRank_eq_of_card {p : ℕ} [hp : Fact p.Prime] {E : Subgroup G} {k : ℕ}
    (hE : IsElemAbelian p E) (hk : Nat.card E = p ^ k) : CFSG.Open.pRank p E = k := by
  apply le_antisymm
  · unfold CFSG.Open.pRank
    apply csSup_le (Set.nonempty_of_mem (show k ∈ {k' : ℕ | ∃ F : Subgroup G, F ≤ E ∧
      CFSG.Open.IsElemAbelian p F ∧ Nat.card F = p ^ k'} from ⟨E, le_rfl, hE, hk⟩))
    rintro k' ⟨F, hFE, hF, hFk⟩
    have hle : p ^ k' ≤ p ^ k := by
      rw [← hFk, ← hk]
      exact Subgroup.card_le_of_le hFE
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hle
  · exact CFSG.SectionRank.le_pRank hp.out.one_lt le_rfl hE hk

theorem normalizer_le_glbCore {p : ℕ} [Finite G] {Q P : Subgroup G} (hQP : Q ≤ P)
    (hQ : 2 ≤ CFSG.Open.pRank p Q) : Subgroup.normalizer (Q : Set G) ≤ GLBCore p 2 P := by
  unfold GLBCore
  exact le_sSup ⟨Q, hQP, hQ, rfl⟩

theorem inf_O_eq_bot {p : ℕ} [hp : Fact p.Prime] {C S : Subgroup G} (hS : IsPGroup p S) :
    S ⊓ GLAPPrimeCoreOf p C = ⊥ := by
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hcop : Nat.Coprime (Nat.card S) (Nat.card (GLAPPrimeCoreOf p C)) := by
    rw [hk]
    exact Nat.Coprime.pow_left k (sec11_glaPPrimeCoreOf_coprime C)
  exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot

end SmallFacts

section QuotientFacts

theorem isoInvariant_isCatalogGroup :
    CFSG.KCore.IsoInvariant (@CFSG.Open.IsCatalogGroup) := by
  intro X Y _ _ e h
  obtain ⟨i, ⟨f⟩⟩ := h
  exact ⟨i, ⟨e.trans f⟩⟩

theorem isKGroup_barX_quotient {G : Type} [Group G] [Finite G] {p : ℕ} {C : Subgroup G}
    (hC : CFSG.Open.IsKGroup ↥C) : CFSG.Open.IsKGroup (↥C ⧸ GLAPPrimeCore p ↥C) :=
  CFSG.KCore.KGroupNonab.quotient isoInvariant_isCatalogGroup hC (GLAPPrimeCore p ↥C)

theorem isKHat_of_component {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsKGroup Y)
    {K : Subgroup Y} (hK : IsComponentOf K ⊤) :
    CFSG.LocalAnalysis.GLTheoremA.IsKHat ↥K := by
  refine ⟨hK.2.2, ?_⟩
  have hsimple : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.2.2.2
  have hperf : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := hK.2.2.1
  set L : Subgroup Y := (Subgroup.center ↥K).map K.subtype with hLdef
  have hLK : L ≤ K := Subgroup.map_subtype_le _
  have hLsub : L.subgroupOf K = Subgroup.center ↥K := by
    ext x
    rw [Subgroup.mem_subgroupOf, hLdef, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  haveI hnorm : (L.subgroupOf K).Normal := by
    rw [hLsub]
    infer_instance
  let e : (↥K ⧸ L.subgroupOf K) ≃* (↥K ⧸ Subgroup.center ↥K) :=
    QuotientGroup.quotientMulEquivOfEq hLsub
  have hNon0 : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have hperfQ : ⁅(⊤ : Subgroup (↥K ⧸ Subgroup.center ↥K)),
        (⊤ : Subgroup (↥K ⧸ Subgroup.center ↥K))⁆ = ⊤ := by
      have h1 := congrArg (Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥K))) hperf
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective _)] at h1
      exact h1
    have hle : ⁅(⊤ : Subgroup (↥K ⧸ Subgroup.center ↥K)),
        (⊤ : Subgroup (↥K ⧸ Subgroup.center ↥K))⁆ ≤ ⊥ := by
      refine Subgroup.commutator_le.2 (fun a _ b _ => ?_)
      exact Subgroup.mem_bot.2 (commutatorElement_eq_one_iff_mul_comm.2 (hcomm a b))
    rw [hperfQ] at hle
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥K ⧸ Subgroup.center ↥K)
    exact hx (Subgroup.mem_bot.1 (hle (Subgroup.mem_top x)))
  have hSim : IsSimpleGroup (↥K ⧸ L.subgroupOf K) := e.isSimpleGroup
  have hNon : ∃ a b : ↥K ⧸ L.subgroupOf K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hNon0
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  obtain ⟨i, ⟨f⟩⟩ := hY K L hLK hSim hNon
  exact ⟨i, ⟨e.symm.trans f⟩⟩

theorem coprime_card_glaPPrimeCore {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (C : Subgroup G) : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥C)) := by
  have h1 : Nat.card (GLAPPrimeCore p ↥C) = Nat.card (GLAPPrimeCoreOf p C : Subgroup G) := by
    unfold GLAPPrimeCoreOf
    rw [Subgroup.card_map_of_injective C.subtype_injective]
  rw [h1]
  exact sec11_glaPPrimeCoreOf_coprime C

theorem glaPComponent_barX_top {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {C K : Subgroup G} (hK : GLAPComponent p C K) :
    GLAPComponent p (⊤ : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) (barX p C K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 := glaPComponent_top hK
  have hker : Nat.Coprime p (Nat.card ↥(⊤ ⊓ (QuotientGroup.mk' (GLAPPrimeCore p ↥C)).ker)) := by
    rw [top_inf_eq, QuotientGroup.ker_mk']
    exact coprime_card_glaPPrimeCore C
  have h2 := glaPComponent_map hp (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) hker h1
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  exact h2

theorem barX_inf_eq {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {C E A : Subgroup G}
    (hEC : E ≤ C) (hAC : A ≤ C) (hS : IsPGroup p ↥(E ⊔ A)) :
    barX p C E ⊓ barX p C A = barX p C (E ⊓ A) := by
  apply le_antisymm
  · rintro z ⟨⟨e, he, rfl⟩, ⟨a, ha, hea⟩⟩
    have hmem_e : (e : G) ∈ E ⊔ A := (le_sup_left : E ≤ E ⊔ A) (Subgroup.mem_subgroupOf.1 he)
    have hmem_a : (a : G) ∈ E ⊔ A := (le_sup_right : A ≤ E ⊔ A) (Subgroup.mem_subgroupOf.1 ha)
    have hinj := injective_barX_comp hp hS (sup_le hEC hAC)
    have hEqa : (⟨e, Subgroup.mem_subgroupOf.2 hmem_e⟩ : ↥((E ⊔ A).subgroupOf C)) =
        ⟨a, Subgroup.mem_subgroupOf.2 hmem_a⟩ := hinj hea.symm
    have hea' : (e : G) = (a : G) :=
      congrArg (fun x : ↥((E ⊔ A).subgroupOf C) => ((x : ↥C) : G)) hEqa
    refine ⟨e, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 he, ?_⟩), rfl⟩
    rw [hea']
    exact Subgroup.mem_subgroupOf.1 ha
  · exact le_inf (barX_mono inf_le_left) (barX_mono inf_le_right)

end QuotientFacts



section Centralizers

theorem centralizer_eq_of_mem_zpowers {G : Type} [Group G] {p : ℕ} [hp : Fact p.Prime] {g d : G}
    (hg : g ^ p = 1) (hd : d ∈ Subgroup.zpowers g) (hd1 : d ≠ 1) :
    Subgroup.centralizer ({d} : Set G) = Subgroup.centralizer ({g} : Set G) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
  have hndvd : ¬ (p : ℤ) ∣ k := by
    intro hdvd
    obtain ⟨t, rfl⟩ := hdvd
    apply hd1
    rw [zpow_mul, zpow_natCast, hg, one_zpow]
  have hcop : IsCoprime (p : ℤ) k :=
    ((Nat.prime_iff_prime_int.mp hp.out).irreducible.coprime_iff_not_dvd).2 hndvd
  obtain ⟨u, v, huv⟩ := hcop
  have hgv : (g ^ k) ^ v = g := by
    rw [← zpow_mul]
    have hkv : k * v = 1 - (p : ℤ) * u := by linarith
    rw [hkv, zpow_sub, zpow_one, zpow_mul, zpow_natCast, hg, one_zpow, inv_one, mul_one]
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx h hh
    rw [Set.mem_singleton_iff.1 hh]
    have hcom : Commute (g ^ k) x := hx (g ^ k) (Set.mem_singleton _)
    have := Commute.zpow_left hcom v
    rw [hgv] at this
    exact this
  · intro hx h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact Commute.zpow_left (hx g (Set.mem_singleton g)) k

theorem centralizer_bar_eq {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {C : Subgroup G} {a : G} (haC : a ∈ C) (ha : IsPGroup p (Subgroup.zpowers a)) :
    Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨a, haC⟩ : ↥C)} :
      Set (↥C ⧸ GLAPPrimeCore p ↥C)) = barX p C (Subgroup.centralizer ({a} : Set G)) := by
  ext z
  constructor
  · intro hz
    obtain ⟨⟨c, hcC⟩, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥C) z
    have hcomm' := Subgroup.mem_centralizer_iff.1 hz _ (Set.mem_singleton _)
    have hxC : a * c * a⁻¹ * c⁻¹ ∈ C := C.mul_mem (C.mul_mem (C.mul_mem haC hcC) (C.inv_mem haC))
      (C.inv_mem hcC)
    have hx : a * c * a⁻¹ * c⁻¹ ∈ GLAPPrimeCoreOf p C := by
      rw [mem_glaPPrimeCoreOf_iff hxC]
      have e1 : (⟨a * c * a⁻¹ * c⁻¹, hxC⟩ : ↥C) =
          ⟨a, haC⟩ * ⟨c, hcC⟩ * ⟨a, haC⟩⁻¹ * ⟨c, hcC⟩⁻¹ := rfl
      rw [e1]
      simp only [map_mul, map_inv]
      rw [hcomm']
      group
    have hVp : ¬ p ∣ Nat.card ↥(GLAPPrimeCoreOf p C) :=
      (Nat.Prime.coprime_iff_not_dvd hp.out).1 (sec11_glaPPrimeCoreOf_coprime C)
    obtain ⟨v, hv, hcv⟩ := exists_mul_mem_centralizer (p := p) (d := a) (x := c)
      (V := GLAPPrimeCoreOf p C) ha hVp
      (sec11_le_normalizer_glaPPrimeCoreOf (p := p) C haC)
      (sec11_le_normalizer_glaPPrimeCoreOf (p := p) C hcC) hx
    have hcvC : c * v ∈ C := C.mul_mem hcC (sec11_glaPPrimeCoreOf_le C hv)
    refine ⟨⟨c * v, hcvC⟩, Subgroup.mem_subgroupOf.2 hcv, ?_⟩
    show QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨c * v, hcvC⟩ : ↥C) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨c, hcC⟩ : ↥C)
    have hinv : (c * v)⁻¹ * c = v⁻¹ := by group
    rw [mk_eq_mk_iff_mem hcvC hcC, hinv]
    exact (GLAPPrimeCoreOf p C).inv_mem hv
  · rintro ⟨d, hd, rfl⟩
    have hdC : (d : G) ∈ Subgroup.centralizer ({a} : Set G) := Subgroup.mem_subgroupOf.1 hd
    have hcomm : a * (d : G) = (d : G) * a := Subgroup.mem_centralizer_iff.1 hdC a (Set.mem_singleton a)
    refine Subgroup.mem_centralizer_iff.2 ?_
    intro h hh
    rw [Set.mem_singleton_iff.1 hh, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm

end Centralizers

section CaseFacts

variable {G : Type} [Group G] [Finite G]

theorem glbCore_barX_le {p : ℕ} [hp : Fact p.Prime] {C B M' : Subgroup G} (k : ℕ)
    (hB : IsPGroup p B) (hBC : B ≤ C)
    (hnorm : ∀ E : Subgroup G, E ≤ B → k ≤ CFSG.Open.pRank p E → Subgroup.normalizer (E : Set G) ≤ M')
    (hcore : GLAPPrimeCoreOf p C ≤ M') :
    GLBCore p k (barX p C B) ≤ barX p C M' := by
  refine sSup_le ?_
  rintro _ ⟨Q, hQB, hQk, rfl⟩
  obtain ⟨E, hEB, hEQ, hEr⟩ := exists_le_barX_eq hp.out hB hBC hQB
  have hEp : IsPGroup p E := hB.to_le hEB
  have hEC : E ≤ C := hEB.trans hBC
  rw [← hEQ]
  refine (normalizer_barX_le hp.out hEp hEC).trans ?_
  refine barX_mono (fun y hy => ?_)
  exact hnorm E hEB (by rw [hEr]; exact hQk) hy

theorem barX_gLBConj_mem {p : ℕ} {C K : Subgroup G} {m : G} (hm : m ∈ C) (hK : K ≤ C) :
    barX p C (GLBConj m K) =
      GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨m, hm⟩ : ↥C)) (barX p C K) := by
  ext z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥C) z
  constructor
  · rintro ⟨y, hy, hyeq⟩
    have hyK : (y : G) ∈ GLBConj m K := Subgroup.mem_subgroupOf.1 hy
    rw [mem_gLBConj] at hyK
    rw [mem_gLBConj, ← hyeq]
    have e : QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨m, hm⟩ : ↥C) *
        QuotientGroup.mk' (GLAPPrimeCore p ↥C) y *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨m, hm⟩ : ↥C))⁻¹ =
        QuotientGroup.mk' (GLAPPrimeCore p ↥C)
          (⟨m * (y : G) * m⁻¹, C.mul_mem (C.mul_mem hm y.2) (C.inv_mem hm)⟩ : ↥C) := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    rw [e]
    exact Subgroup.mem_map.2 ⟨⟨m * (y : G) * m⁻¹, C.mul_mem (C.mul_mem hm y.2) (C.inv_mem hm)⟩,
      Subgroup.mem_subgroupOf.2 hyK, rfl⟩
  · intro hz
    rw [mem_gLBConj] at hz
    obtain ⟨k, hk, hkeq⟩ := Subgroup.mem_map.1 hz
    have hkC : (m⁻¹ * (k : G) * m) ∈ C := C.mul_mem (C.mul_mem (C.inv_mem hm) k.2) hm
    refine ⟨⟨m⁻¹ * (k : G) * m, hkC⟩, ?_, ?_⟩
    · apply Subgroup.mem_subgroupOf.2
      rw [mem_gLBConj]
      have e1 : m * (m⁻¹ * (k : G) * m) * m⁻¹ = (k : G) := by group
      rw [e1]
      exact Subgroup.mem_subgroupOf.1 hk
    · have e2 : (⟨m⁻¹ * (k : G) * m, hkC⟩ : ↥C) =
          (⟨m, hm⟩ : ↥C)⁻¹ * k * ⟨m, hm⟩ := Subtype.ext (by simp [mul_assoc])
      rw [e2, map_mul, map_mul, map_inv, hkeq]
      group

theorem isElemAbelian_zpowers_of_mem {p : ℕ} {A : Subgroup G} {a : G}
    (hA : CFSG.Open.IsElemAbelian p A) (ha : a ∈ A) :
    CFSG.Open.IsElemAbelian p (Subgroup.zpowers a) :=
  isElemAbelian_mono hA (Subgroup.zpowers_le.2 ha)

theorem barX_cg2_le_glaDelta {p : ℕ} [hp : Fact p.Prime] {e a : G}
    (haC : a ∈ Subgroup.centralizer ({e} : Set G)) (ha : IsPGroup p (Subgroup.zpowers a))
    (hord : a ^ p = 1) (ha1 : a ≠ 1) :
    barX p (Subgroup.centralizer ({e} : Set G))
        (GLAPPrimeCoreOf p (Subgroup.centralizer ({e, a} : Set G))) ≤
      GLADelta p (Subgroup.zpowers (QuotientGroup.mk'
        (GLAPPrimeCore p ↥(Subgroup.centralizer ({e} : Set G)))
        (⟨a, haC⟩ : ↥(Subgroup.centralizer ({e} : Set G))))) := by
  set C : Subgroup G := Subgroup.centralizer ({e} : Set G) with hCdef
  set X₀ : Subgroup G := GLAPPrimeCoreOf p (Subgroup.centralizer ({e, a} : Set G)) with hX₀def
  have hC2 : Subgroup.centralizer ({e, a} : Set G) ≤ C :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Set.mem_insert _ _))
  have hC2a : Subgroup.centralizer ({e, a} : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Set.mem_insert_of_mem _ rfl))
  have hX₀C : X₀ ≤ C := (sec11_glaPPrimeCoreOf_le _).trans hC2
  have hX₀a : X₀ ≤ Subgroup.centralizer ({a} : Set G) :=
    (sec11_glaPPrimeCoreOf_le _).trans hC2a
  set g := QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨a, haC⟩ : ↥C) with hgdef
  have hg : g ^ p = 1 := by
    rw [hgdef, ← map_pow, show (⟨a, haC⟩ : ↥C) ^ p = 1 from Subtype.ext (by simpa using hord),
      map_one]
  have hsub : barX p C X₀ ≤ Subgroup.centralizer ({g} : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
    rw [hgdef, centralizer_bar_eq haC ha]
    exact barX_mono hX₀a
  have hcop : Nat.Coprime p (Nat.card (barX p C X₀)) := by
    have h1 := Subgroup.card_map_dvd (H := X₀.subgroupOf C)
      (QuotientGroup.mk' (GLAPPrimeCore p ↥C))
    have h2 : Nat.card (X₀.subgroupOf C) = Nat.card X₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₀C).toEquiv
    rw [h2] at h1
    exact Nat.Coprime.coprime_dvd_right h1 (sec11_glaPPrimeCoreOf_coprime _)
  unfold GLADelta
  refine le_iInf fun d => le_iInf fun hd => le_iInf fun hd1 => ?_
  rw [centralizer_eq_of_mem_zpowers hg hd hd1]
  refine sec11_le_glaPPrimeCoreOf hsub ?_ hcop
  intro h hh n hn
  rw [hgdef, centralizer_bar_eq haC ha] at hh
  obtain ⟨c, hc, rfl⟩ := hh
  obtain ⟨x, hx, rfl⟩ := hn
  have hcC : (c : G) ∈ C := c.2
  have hcaC : (c : G) ∈ Subgroup.centralizer ({a} : Set G) := Subgroup.mem_subgroupOf.1 hc
  have hcC2 : (c : G) ∈ Subgroup.centralizer ({e, a} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rcases Set.mem_insert_iff.1 hk with rfl | hk'
    · exact Subgroup.mem_centralizer_iff.1 hcC k (Set.mem_singleton k)
    · rw [Set.mem_singleton_iff.1 hk']
      exact Subgroup.mem_centralizer_iff.1 hcaC a (Set.mem_singleton a)
  have hxX : (x : G) ∈ X₀ := Subgroup.mem_subgroupOf.1 hx
  have hcx : (c : G) * (x : G) * (c : G)⁻¹ ∈ X₀ :=
    sec11_glaPPrimeCoreOf_conj_mem hcC2 hxX
  have hcxC : (c : G) * (x : G) * (c : G)⁻¹ ∈ C :=
    C.mul_mem (C.mul_mem hcC (hX₀C hxX)) (C.inv_mem hcC)
  have e1 : QuotientGroup.mk' (GLAPPrimeCore p ↥C) c *
      QuotientGroup.mk' (GLAPPrimeCore p ↥C) x *
      (QuotientGroup.mk' (GLAPPrimeCore p ↥C) c)⁻¹ =
      QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨(c : G) * (x : G) * (c : G)⁻¹, hcxC⟩ : ↥C) := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  rw [e1]
  exact Subgroup.mem_map.2 ⟨⟨(c : G) * (x : G) * (c : G)⁻¹, hcxC⟩, Subgroup.mem_subgroupOf.2 hcx, rfl⟩

end CaseFacts

theorem contra_of_conj {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G}
    (h : Sec10Fails G m p B M) {y : G} (hy : y ∈ M) (hE : inD p M E) (hA : inDp p M A)
    (hyE : GLBConj y E = A) : False := by
  have h1 := (lemma101_i_holds h hy hE hA).1
  rw [hyE] at h1
  exact hA.2 h1.2

theorem barX_pow_eq_one {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {C : Subgroup G}
    {a : G} (haC : a ∈ C) (hord : a ^ p = 1) :
    (QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨a, haC⟩ : ↥C)) ^ p = 1 := by
  rw [← map_pow, show (⟨a, haC⟩ : ↥C) ^ p = 1 from Subtype.ext (by simpa using hord), map_one]

theorem barX_ne_one {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {C : Subgroup G}
    {a : G} (haC : a ∈ C) (ha : IsPGroup p (Subgroup.zpowers a)) (ha1 : a ≠ 1) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨a, haC⟩ : ↥C) ≠ 1 := by
  intro h1
  have haO : a ∈ GLAPPrimeCoreOf p C := (mem_glaPPrimeCoreOf_iff haC).2 h1
  have hmem : a ∈ Subgroup.zpowers a ⊓ GLAPPrimeCoreOf p C := ⟨Subgroup.mem_zpowers a, haO⟩
  rw [inf_O_eq_bot (C := C) ha] at hmem
  exact ha1 (Subgroup.mem_bot.1 hmem)

theorem prop112_of_inputs (hI273 : Input27_3) (hI1913 : Input19_1_3Gen)
    (h114 : Lemma114Statement) (h113 : Lemma113_iiClosed) : Prop112Statement := by
  intro G _ _ m p B M E A h a e ha ha1 he he1
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnot_i, hnot_ii⟩ := hcon
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup G := hS.simple
  have hp2 : p ≠ 2 := hS.ne_two
  obtain ⟨hO, hrank, K, hK, hcomm, hnotcov⟩ :=
    h114 ⟨h, ⟨ha, ha1⟩, ⟨he, he1⟩, hnot_i, hnot_ii⟩
  have hE𝒟 : inD p M E := h.pair.1.1
  have hA𝒟 : inDp p M A := h.pair.1.2.1
  obtain ⟨hEsc, hAsc⟩ := lemma104_ii_holds h.toSec10Fails h.pair
  have hEel : CFSG.Open.IsElemAbelian p E := hEsc.2.1
  have hAel : CFSG.Open.IsElemAbelian p A := hAsc.2.1
  have hEp : IsPGroup p E := isPGroup_of_isElemAbelian' hEel
  have hAp : IsPGroup p A := isPGroup_of_isElemAbelian' hAel
  have hEAp4 : IsPGroup p ↥(E ⊔ A) := lemma104_i_holds h.toSec10Fails h.pair
  have heE : e ∈ E := (Subgroup.mem_inf.1 he).1
  have heA : e ∈ A := (Subgroup.mem_inf.1 he).2
  have hEC : E ≤ Cg e := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun g hg => by
      rw [Set.mem_singleton_iff.1 hg]
      exact elemAbelian_comm hEel heE hx
  have hAC : A ≤ Cg e := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun g hg => by
      rw [Set.mem_singleton_iff.1 hg]
      exact elemAbelian_comm hAel heA hx
  have hGz : Subgroup.center G = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨a', b', hab⟩ := hS.nonabelian
      apply hab
      have hz : a' ∈ Subgroup.center G := by rw [h1]; exact Subgroup.mem_top a'
      exact ((Subgroup.mem_center_iff.1 hz) b').symm
  have hCne : Cg e ≠ ⊤ := by
    intro htop
    have hez : e ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Cg e := by rw [htop]; exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.1 hg e (Set.mem_singleton e)).symm
    rw [hGz, Subgroup.mem_bot] at hez
    exact he1 hez
  have hIsKC : CFSG.Open.IsKGroup ↥(Cg e) := isKGroup_of_isKProper hS.kProper hCne
  have hIsKY := isKGroup_barX_quotient (p := p) hIsKC
  have hOY : GLAPPrimeCore p (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e)) = ⊥ :=
    glaPPrimeCore_quotient_eq_bot hp
  have hKY : GLAPComponent p ⊤ (barX p (Cg e) K) := glaPComponent_barX_top hp hK
  have hKhat : CFSG.LocalAnalysis.GLTheoremA.IsKHat ↥(barX p (Cg e) K) :=
    isKHat_of_component hIsKY hK.2.2.1
  have hNC : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥(Cg e)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 (coprime_card_glaPPrimeCore (Cg e))
  have hĒsc : IsSCp p ⊤ (barX p (Cg e) E) :=
    isSCp_map_quotient (GLAPPrimeCore p ↥(Cg e)) hNC (isSCp_subgroupOf hEsc hEC)
  have hĀsc : IsSCp p ⊤ (barX p (Cg e) A) :=
    isSCp_map_quotient (GLAPPrimeCore p ↥(Cg e)) hNC (isSCp_subgroupOf hAsc hAC)
  have hĒel : CFSG.Open.IsElemAbelian p (barX p (Cg e) E) := isElemAbelian_barX hEel
  have hĀel : CFSG.Open.IsElemAbelian p (barX p (Cg e) A) := isElemAbelian_barX hAel
  have hEAbar : barX p (Cg e) E ⊔ barX p (Cg e) A ≤ barX p (Cg e) (E ⊔ A) :=
    sup_le (barX_mono le_sup_left) (barX_mono le_sup_right)
  have hEAp' : IsPGroup p ↥(barX p (Cg e) E ⊔ barX p (Cg e) A) :=
    (isPGroup_barX_of_le (sup_le hEC hAC) hEAp4).to_le hEAbar
  have hEinfp : IsPGroup p ↥(E ⊓ A) := hEp.to_le inf_le_left
  have hEArank : CFSG.Open.pRank p (barX p (Cg e) E ⊓ barX p (Cg e) A) = 2 := by
    rw [barX_inf_eq hp (hEC) hAC hEAp4, rank_barX_of_isPGroup hp hEinfp (inf_le_left.trans hEC)]
    exact hrank
  have hEneA : barX p (Cg e) E ≠ barX p (Cg e) A := by
    intro heq
    obtain ⟨x, hx, hxE⟩ := exists_conj_of_barX_eq hEC hAC hEp hAp heq
    exact contra_of_conj h.toSec10Fails (hO hx) hE𝒟 hA𝒟 hxE
  have he_Cg : e ∈ Cg e := Subgroup.mem_centralizer_iff.2 fun g hg => by
    rw [Set.mem_singleton_iff.1 hg]
  have heB : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e, he_Cg⟩ : ↥(Cg e)) ≠ 1 := by
    intro h1
    have heO : e ∈ GLAPPrimeCoreOf p (Cg e) := (mem_glaPPrimeCoreOf_iff he_Cg).2 h1
    have hmem : e ∈ E ⊓ GLAPPrimeCoreOf p (Cg e) := ⟨heE, heO⟩
    rw [inf_O_eq_bot (C := Cg e) hEp] at hmem
    exact he1 (Subgroup.mem_bot.1 hmem)
  have hlayer : Subgroup.centralizer
      ((GLALayer (⊤ : Subgroup (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e))) :
        Subgroup (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e))) : Set (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e))) ⊓
      (barX p (Cg e) E ⊓ barX p (Cg e) A) ≠ ⊥ := by
    intro h0
    have hmemE : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e, he_Cg⟩ : ↥(Cg e)) ∈
        barX p (Cg e) E ⊓ barX p (Cg e) A :=
      ⟨Subgroup.mem_map.2 ⟨⟨e, he_Cg⟩, Subgroup.mem_subgroupOf.2 heE, rfl⟩,
        Subgroup.mem_map.2 ⟨⟨e, he_Cg⟩, Subgroup.mem_subgroupOf.2 heA, rfl⟩⟩
    have hcen : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e, he_Cg⟩ : ↥(Cg e)) ∈
        Subgroup.centralizer ((GLALayer (⊤ : Subgroup (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e))) :
          Subgroup (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e))) : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g _
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥(Cg e)) g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 x.2 e (Set.mem_singleton e)).symm
    have hmem := Subgroup.mem_inf.2 ⟨hcen, hmemE⟩
    rw [h0, Subgroup.mem_bot] at hmem
    exact heB hmem
  have hdisj := hI273 p hp hp2 (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e)) hIsKY hOY
    (barX p (Cg e) K) hKY hKhat (barX p (Cg e) E) (barX p (Cg e) A) hĒsc hĀsc hEneA hEAp'
    (le_of_eq hEArank.symm) hlayer
  have haC : a ∈ Cg e := hAC ha
  have hord : a ^ p = 1 := hAel.2 a ha
  have ha_pg : IsPGroup p (Subgroup.zpowers a) :=
    isPGroup_of_isElemAbelian' (isElemAbelian_zpowers_of_mem hAel ha)
  rcases hdisj with ⟨Es, hEsSC, hEsrank, hEsConn, hKEs⟩ | hdisj
  ·
    obtain ⟨Ets, hEtsC, hEtsbar, hEtsel, hEtscard, hEtsConn⟩ :=
      kconn_lift (C := Cg e) hEC rfl hEel hEsConn
    obtain ⟨H, hHSC, hEtsH⟩ := sec11_exists_isSCp_above (p := p) le_top hEtsel
    have hEH : IsKConnectedIn p 3 ⊤ E H := isKConnectedIn_extend hEtsConn hEtsH hHSC.2.1
    have hHD : inD p M H := lemma104_iii_holds h.toSec10Fails h.pair hHSC hE𝒟
      (by rw [hrank]; exact isKConnectedIn_symm' hEH)
    have hHM : GLBCore p 2 H ≤ M := hHD.2.clause_d
    have hKM : K ≤ M := by
      refine le_of_barX_le_glbCore hp 2 (isPGroup_of_isElemAbelian' hEtsel) hEtsC hK.1 ?_ hO ?_
      · intro E' hE' hr'
        exact (normalizer_le_glbCore (hE'.trans hEtsH) hr').trans hHM
      · rw [hEtsbar]
        exact hKEs
    exact hnotcov (barX_mono (le_inf hKM hK.1))
  rcases hdisj with hEAconn | hdisj
  ·
    obtain ⟨Ets, hEtsC, hEtsbar, hEtsel, hEtscard, hEtsConn⟩ :=
      kconn_lift (C := Cg e) hEC rfl hEel hEAconn
    have hEtsp : IsPGroup p Ets := isPGroup_of_isElemAbelian' hEtsel
    obtain ⟨y, hyO, hyconj⟩ := exists_conj_of_barX_eq hAC hEtsC hAp hEtsp hEtsbar.symm
    have hEtsSC : IsSCp p ⊤ Ets := by
      rw [← hyconj]
      exact isSCp_gLBConj_of_mem (Subgroup.mem_top y) hAsc
    have hD : inD p M Ets := lemma104_iii_holds h.toSec10Fails h.pair hEtsSC hE𝒟
      (by rw [hrank]; exact isKConnectedIn_symm' hEtsConn)
    rw [← hyconj] at hD
    have h1 := (lemma101_i_holds h.toSec10Fails (M.inv_mem (hO hyO)) hD hA𝒟).1
    rw [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] at h1
    exact hA𝒟.2 h1.2
  rcases hdisj with ⟨y, hyG, hyconj⟩ | hdisj
  ·
    have hEM : GLBCore p 2 E ≤ M := hE𝒟.2.clause_d
    have hnorm : ∀ E' : Subgroup G, E' ≤ E → 2 ≤ CFSG.Open.pRank p E' →
        Subgroup.normalizer (E' : Set G) ≤ M :=
      fun E' hE' hr' => (normalizer_le_glbCore hE' hr').trans hEM
    have hyM : y ∈ barX p (Cg e) M := glbCore_barX_le 2 hEp hEC hnorm hO hyG
    obtain ⟨mm, hmmM, hmmy⟩ := Subgroup.mem_map.1 hyM
    have hmmM' : (mm : G) ∈ M := Subgroup.mem_subgroupOf.1 hmmM
    have hmmy' : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨(mm : G), mm.2⟩ : ↥(Cg e)) = y :=
      hmmy
    have hconjbar : barX p (Cg e) (GLBConj (mm : G) E) = barX p (Cg e) A := by
      rw [barX_gLBConj_mem mm.2 hEC, hmmy', hyconj]
    obtain ⟨x, hxO, hxconj⟩ := exists_conj_of_barX_eq hAC (gLBConj_le_of_mem mm.2 hEC) hAp
      (isPGroup_of_isElemAbelian' (isElemAbelian_gLBConj _ hEel)) hconjbar.symm
    have hAeq : GLBConj ((mm : G) * x⁻¹) E = A := by
      calc GLBConj ((mm : G) * x⁻¹) E = GLBConj x⁻¹ (GLBConj (mm : G) E) :=
            (gLBConj_gLBConj _ _ _).symm
        _ = GLBConj x⁻¹ (GLBConj x A) := by rw [hxconj]
        _ = A := by rw [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one]
    exact contra_of_conj h.toSec10Fails (M.mul_mem hmmM' (M.inv_mem (hO hxO))) hE𝒟 hA𝒟 hAeq
  rcases hdisj with ⟨hEr3, hAr3⟩ | hdisj
  ·
    have hEr3' : CFSG.Open.pRank p E = 3 := by
      rwa [rank_barX_of_isPGroup hp hEp hEC] at hEr3
    have hAr : CFSG.Open.pRank p A = 3 :=
      lemma104_vi_of_lemma104_v (lemma104_v_of_input31_8 input31_8_holds) h.toSec10Fails h.pair
        hEr3'
    rw [rank_barX_of_isPGroup hp hAp hAC] at hAr3
    omega
  rcases hdisj with ⟨hp3, hEr3⟩ | hdisj
  ·
    subst hp3
    have hEr3' : CFSG.Open.pRank 3 E = 3 := by
      rwa [rank_barX_of_isPGroup hp hEp hEC] at hEr3
    have h4 := lemma113_i_of_104v (lemma104_v_of_input31_8 input31_8_holds) h ha ha1 hnot_ii
    omega
  rcases hdisj with ⟨hp3, hEcard, hAcard, hK2727⟩ | hg
  ·
    subst hp3
    have hEk : Nat.card E = 3 ^ 4 := by
      rw [← card_barX_of_le hp hEC hEp]
      exact hEcard
    have hAk : Nat.card A = 3 ^ 3 := by
      rw [← card_barX_of_le hp hAC hAp]
      exact hAcard
    have hE4 : CFSG.Open.pRank 3 E = 4 := pRank_eq_of_card hEel hEk
    have hA3 : CFSG.Open.pRank 3 A = 3 := pRank_eq_of_card hAel hAk
    have hbar : IsLTwoTwentySeven (barOf 3 K) := by
      obtain ⟨f⟩ := hK2727
      exact ⟨(quotEquivBarX hp hK.1 hK.2.1).trans f⟩
    exact h113 h ha ha1 hnot_ii hE4 hA3 e he he1 K hK hbar
  ·
    have hgpow := barX_pow_eq_one haC hord
    have hgne := barX_ne_one haC ha_pg ha1
    have hDle : Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e))
        (⟨a, haC⟩ : ↥(Cg e))) ≤ barX p (Cg e) A :=
      Subgroup.zpowers_le.2 (Subgroup.mem_map.2 ⟨⟨a, haC⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩)
    have hDel : CFSG.Open.IsElemAbelian p (Subgroup.zpowers (QuotientGroup.mk'
        (GLAPPrimeCore p ↥(Cg e)) (⟨a, haC⟩ : ↥(Cg e)))) :=
      isElemAbelian_mono (isElemAbelian_barX (C := Cg e) hAel) hDle
    have hDcard : Nat.card (Subgroup.zpowers (QuotientGroup.mk'
        (GLAPPrimeCore p ↥(Cg e)) (⟨a, haC⟩ : ↥(Cg e)))) = p ^ 1 := by
      rw [pow_one, Nat.card_zpowers, orderOf_eq_prime hgpow hgne]
    have hD : IsEkIn p 1 (barX p (Cg e) A) (Subgroup.zpowers (QuotientGroup.mk'
        (GLAPPrimeCore p ↥(Cg e)) (⟨a, haC⟩ : ↥(Cg e)))) := ⟨hDle, hDel, hDcard⟩
    have hdelta := hI1913 p 1 hp le_rfl (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e)) hIsKY hOY
      (barX p (Cg e) A) _ hĀel hD hDle (barX p (Cg e) K) hKY hg
    have hXD := barX_cg2_le_glaDelta haC ha_pg hord ha1
    have hcomm0 : ⁅barX p (Cg e) K, barX p (Cg e) (GLAPPrimeCoreOf p (Cg2 e a))⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 (fun k hk =>
        Subgroup.mem_centralizer_iff.2 (fun s hs => hdelta s (hXD hs) k hk))
    exact hcomm hcomm0


end CFSG.LocalAnalysis.GLTheoremB.MovingAround
