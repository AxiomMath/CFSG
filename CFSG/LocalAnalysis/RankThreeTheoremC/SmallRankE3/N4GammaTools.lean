module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Defs
public import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQHallHigman
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Main

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open Subgroup CFSG.HallHigman CFSG.LocalAnalysis.RankFourTheoremC.PEmpty CFSG.Open
open CFSG.LocalAnalysis.RankThreeTheoremC.InnerQ.HallHigman (IsPSolvable.quotient' IsPSolvable.subgroup')

variable {G : Type} [Group G] [Finite G]

theorem n4_exists_fixed_of_pow_eq_one_aux {α : Type} [Finite α] {p : ℕ} [hp : Fact p.Prime]
    (hcop : Nat.Coprime p (Nat.card α)) (σ : Equiv.Perm α) (hσ : σ ^ p = 1) :
    ∃ x, σ x = x := by
  classical
  haveI := Fintype.ofFinite α
  have hmod := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1) (σ := σ)
    (by rw [pow_one]; exact hσ)
  rw [Nat.card_eq_fintype_card] at hcop
  have hne : σ.supportᶜ.card ≠ 0 := by
    intro h0
    rw [h0] at hmod
    have hdvd : p ∣ Fintype.card α := Nat.modEq_zero_iff_dvd.mp hmod.symm
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).mp hcop hdvd
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
  rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hx
  exact ⟨x, hx⟩

theorem n4_exists_mul_centralizer {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {D H : Subgroup G}
    (hDH : D ≤ H) (hN : H ≤ normalizer (D : Set G)) (hD : IsPGroup 2 D) {b : G} (hbH : b ∈ H)
    (hbp : orderOf b = p) {l : G} (hlH : l ∈ H) (hcomm : b * l * b⁻¹ * l⁻¹ ∈ D) :
    ∃ d ∈ D, ∃ c ∈ centralizer ({b} : Set G), l = d * c := by
  clear hDH hlH
  classical
  have hconj : ∀ g ∈ H, ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun g hg x hx =>
    (Subgroup.mem_set_normalizer_iff.mp (hN hg) x).mp hx
  have hbinv : b⁻¹ ∈ H := H.inv_mem hbH
  generalize hδdef : b * l * b⁻¹ * l⁻¹ = δ at hcomm
  have hδinv : δ⁻¹ ∈ D := D.inv_mem hcomm
  have hf : l * b * l⁻¹ = δ⁻¹ * b := by
    rw [← hδdef]
    group
  have hbpow : b ^ p = 1 := by
    rw [← hbp]
    exact pow_orderOf_eq_one b
  have hfpow : (δ⁻¹ * b) ^ p = 1 := by
    rw [← hf, conj_pow, hbpow, mul_one, mul_inv_cancel]
  have hbinvpow : b⁻¹ ^ p = 1 := by
    rw [inv_pow, hbpow, inv_one]
  have hcop : Nat.Coprime p (Nat.card D) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hD
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).mpr hp2)
  have hσmem : ∀ x : ↥D, δ⁻¹ * (b * (x : G) * b⁻¹) ∈ D := fun x =>
    D.mul_mem hδinv (hconj b hbH _ x.2)
  have hτmem : ∀ x : ↥D, b⁻¹ * (δ * (x : G)) * b ∈ D := fun x => by
    have h := hconj b⁻¹ hbinv _ (D.mul_mem hcomm x.2)
    rwa [inv_inv] at h
  obtain ⟨σ, hσapp⟩ : ∃ σ : Equiv.Perm ↥D,
      ∀ x : ↥D, ((σ x : ↥D) : G) = δ⁻¹ * b * (x : G) * b⁻¹ := by
    refine ⟨⟨fun x => ⟨δ⁻¹ * (b * (x : G) * b⁻¹), hσmem x⟩,
      fun x => ⟨b⁻¹ * (δ * (x : G)) * b, hτmem x⟩, ?_, ?_⟩, ?_⟩
    · intro x
      refine Subtype.ext ?_
      show b⁻¹ * (δ * (δ⁻¹ * (b * (x : G) * b⁻¹))) * b = (x : G)
      group
    · intro x
      refine Subtype.ext ?_
      show δ⁻¹ * (b * (b⁻¹ * (δ * (x : G)) * b) * b⁻¹) = (x : G)
      group
    · intro x
      show δ⁻¹ * (b * (x : G) * b⁻¹) = δ⁻¹ * b * (x : G) * b⁻¹
      simp only [mul_assoc]
  have hσpow : ∀ (k : ℕ) (x : ↥D), ((σ ^ k) x : G) = (δ⁻¹ * b) ^ k * (x : G) * b⁻¹ ^ k := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ' σ k, Equiv.Perm.mul_apply, hσapp, ih x, pow_succ' (δ⁻¹ * b) k,
        pow_succ b⁻¹ k]
      simp only [mul_assoc]
  have hσp : σ ^ p = 1 := by
    refine Equiv.ext fun x => Subtype.ext ?_
    simp only [hσpow, hfpow, hbinvpow, one_mul, mul_one, Equiv.Perm.one_apply]
  obtain ⟨x₀, hx₀⟩ := n4_exists_fixed_of_pow_eq_one_aux hcop σ hσp
  have hfix : δ⁻¹ * b * (x₀ : G) * b⁻¹ = (x₀ : G) := by
    have h := hσapp x₀
    rw [hx₀] at h
    exact h.symm
  have hlx : l * b * l⁻¹ = (x₀ : G) * b * (x₀ : G)⁻¹ := by
    rw [hf]
    calc δ⁻¹ * b = δ⁻¹ * b * (x₀ : G) * b⁻¹ * b * (x₀ : G)⁻¹ := by group
      _ = (x₀ : G) * b * (x₀ : G)⁻¹ := by rw [hfix]
  have hlb : l * b = (x₀ : G) * b * (x₀ : G)⁻¹ * l := by
    rw [← hlx]
    group
  have hc : b * ((x₀ : G)⁻¹ * l) = (x₀ : G)⁻¹ * l * b := by
    calc b * ((x₀ : G)⁻¹ * l) = (x₀ : G)⁻¹ * ((x₀ : G) * b * (x₀ : G)⁻¹ * l) := by group
      _ = (x₀ : G)⁻¹ * (l * b) := by rw [hlb]
      _ = (x₀ : G)⁻¹ * l * b := by rw [mul_assoc]
  refine ⟨(x₀ : G), x₀.2, (x₀ : G)⁻¹ * l, ?_, (mul_inv_cancel_left _ _).symm⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  exact hc

theorem n4_mem_sup_iff {D C H : Subgroup G} (hDH : D ≤ H) (hCH : C ≤ H)
    (hN : H ≤ normalizer (D : Set G)) {w : G} :
    w ∈ D ⊔ C ↔ ∃ d ∈ D, ∃ c ∈ C, w = d * c := by
  constructor
  · intro hw
    have hconj : ∀ x ∈ H, ∀ d ∈ D, x * d * x⁻¹ ∈ D := fun x hx d hd =>
      (Subgroup.mem_normalizer_iff.mp (hN hx) d).mp hd
    let P : Subgroup G :=
      { carrier := {w | ∃ d ∈ D, ∃ c ∈ C, w = d * c}
        mul_mem' := by
          rintro _ _ ⟨d₁, hd₁, c₁, hc₁, rfl⟩ ⟨d₂, hd₂, c₂, hc₂, rfl⟩
          refine ⟨d₁ * (c₁ * d₂ * c₁⁻¹), D.mul_mem hd₁ (hconj c₁ (hCH hc₁) d₂ hd₂), c₁ * c₂,
            C.mul_mem hc₁ hc₂, ?_⟩
          group
        one_mem' := ⟨1, D.one_mem, 1, C.one_mem, by simp⟩
        inv_mem' := by
          rintro _ ⟨d, hd, c, hc, rfl⟩
          refine ⟨c⁻¹ * d⁻¹ * c⁻¹⁻¹, hconj c⁻¹ (H.inv_mem (hCH hc)) d⁻¹ (D.inv_mem hd), c⁻¹,
            C.inv_mem hc, ?_⟩
          group }
    have hDP : D ≤ P := fun d hd => ⟨d, hd, 1, C.one_mem, by simp⟩
    have hCP : C ≤ P := fun c hc => ⟨1, D.one_mem, c, hc, by simp⟩
    have hle : D ⊔ C ≤ P := sup_le hDP hCP
    exact hle hw
  · rintro ⟨d, hd, c, hc, rfl⟩
    have hd' : d ∈ D ⊔ C := (le_sup_left : D ≤ D ⊔ C) hd
    have hc' : c ∈ D ⊔ C := (le_sup_right : C ≤ D ⊔ C) hc
    exact (D ⊔ C).mul_mem hd' hc'

theorem n4_pSolvable_subgroupOf {p : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X]
    {Gs K E : Subgroup X} (hEK : E ≤ K) (hEG : E ≤ Gs) (hK : IsPSolvable p ↥K) :
    IsPSolvable p ↥(E.subgroupOf Gs) := by
  have hsub : IsPSolvable p ↥(E.subgroupOf K) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.InnerQ.HallHigman.IsPSolvable.subgroup' hK (E.subgroupOf K)
  exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
    ((Subgroup.subgroupOfEquivOfLe hEK).trans (Subgroup.subgroupOfEquivOfLe hEG).symm) hsub

theorem n4_pSolvable_range {p : ℕ} [Fact p.Prime] {A X : Type} [Group A] [Finite A] [Group X]
    [Finite X] (f : A →* X) (hA : IsPSolvable p A) : IsPSolvable p ↥f.range := by
  have hQ : IsPSolvable p (A ⧸ f.ker) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.InnerQ.HallHigman.IsPSolvable.quotient' hA f.ker
  exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
    (QuotientGroup.quotientKerEquivRange f) hQ

theorem n4_card_eq_or_coprime_of_isPSolvable {p : ℕ} {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hQ : CFSG.HallHigman.IsPSolvable p Q) : Nat.card Q = p ∨ Nat.Coprime p (Nat.card Q) := by
  have e : (↥(⊤ : Subgroup Q) ⧸ (⊥ : Subgroup ↥(⊤ : Subgroup Q))) ≃* Q :=
    (QuotientGroup.quotientBot (G := ↥(⊤ : Subgroup Q))).trans Subgroup.topEquiv
  have hs : IsSimpleGroup (↥(⊤ : Subgroup Q) ⧸ (⊥ : Subgroup ↥(⊤ : Subgroup Q))) :=
    e.isSimpleGroup
  have key := hQ ⊤ Subgroup.IsSubnormal.top ⊥ hs
  rwa [Subgroup.index_bot, Subgroup.card_top] at key

theorem n4_false_of_hom_pSolvable {p : ℕ} [Fact p.Prime] {A : Type} [Group A] [Finite A]
    {X : Type} [Group X] [Finite X] {Y N : Subgroup A} {z : A} (hsec : S622IsSimpleSection Y N)
    (hz : z ∈ Y) (hzN : z ∉ N) (hzp : z ^ p = 1) (ψ : ↥Y →* X)
    (hker : ∀ y : ↥Y, ψ y = 1 → (y : A) ∈ N) (hX : IsPSolvable p X) : False := by
  haveI hNn : (N.subgroupOf Y).Normal := hsec.2.1
  have hsimpleQ : IsSimpleGroup (↥Y ⧸ N.subgroupOf Y) :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613.isSimpleGroup_quotient_of_section hsec
  have hnab : ¬ ∀ a ∈ Y, ∀ b ∈ Y, a * b * a⁻¹ * b⁻¹ ∈ N := hsec.2.2.2.2
  have hR : IsPSolvable p ↥ψ.range := IsPSolvable.subgroup' hX ψ.range
  have hYψ : IsPSolvable p (↥Y ⧸ ψ.ker) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (QuotientGroup.quotientKerEquivRange ψ).symm hR
  have hkerle : ψ.ker ≤ (QuotientGroup.mk' (N.subgroupOf Y)).ker := by
    intro n hn
    rw [QuotientGroup.ker_mk']
    exact Subgroup.mem_subgroupOf.2 (hker n (MonoidHom.mem_ker.1 hn))
  obtain ⟨L, hLdef⟩ : ∃ L : (↥Y ⧸ ψ.ker) →* (↥Y ⧸ N.subgroupOf Y),
      ∀ y : ↥Y, L (y : ↥Y ⧸ ψ.ker) = (y : ↥Y ⧸ N.subgroupOf Y) :=
    ⟨QuotientGroup.lift ψ.ker (QuotientGroup.mk' (N.subgroupOf Y)) hkerle, fun y => rfl⟩
  have hL : Function.Surjective L := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf Y) q
    exact ⟨(y : ↥Y ⧸ ψ.ker), hLdef y⟩
  have hQ : IsPSolvable p (↥Y ⧸ N.subgroupOf Y) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (QuotientGroup.quotientKerEquivOfSurjective L hL) (IsPSolvable.quotient' hYψ L.ker)
  have hdich : Nat.card (↥Y ⧸ N.subgroupOf Y) = p ∨
      Nat.Coprime p (Nat.card (↥Y ⧸ N.subgroupOf Y)) :=
    n4_card_eq_or_coprime_of_isPSolvable hQ
  obtain ⟨x, hxz⟩ : ∃ x : ↥Y, (x : A) = z := ⟨⟨z, hz⟩, rfl⟩
  have hxp : x ^ p = 1 := Subtype.ext (by simp [hxz, hzp])
  have hgp : (QuotientGroup.mk' (N.subgroupOf Y) x) ^ p = 1 := by
    rw [← map_pow, hxp, map_one]
  have hg1 : QuotientGroup.mk' (N.subgroupOf Y) x ≠ 1 := by
    intro h
    rw [QuotientGroup.mk'_apply] at h
    have h2 : x ∈ N.subgroupOf Y := (QuotientGroup.eq_one_iff (N := N.subgroupOf Y) x).1 h
    have h3 : (x : A) ∈ N := Subgroup.mem_subgroupOf.1 h2
    rw [hxz] at h3
    exact hzN h3
  have hord : orderOf (QuotientGroup.mk' (N.subgroupOf Y) x) = p := orderOf_eq_prime hgp hg1
  have hpdvd : p ∣ Nat.card (↥Y ⧸ N.subgroupOf Y) := by
    have h := orderOf_dvd_natCard (QuotientGroup.mk' (N.subgroupOf Y) x)
    rwa [hord] at h
  rcases hdich with hcard | hcop
  ·
    haveI : IsCyclic (↥Y ⧸ N.subgroupOf Y) := isCyclic_of_prime_card hcard
    apply hnab
    intro a ha b hb
    obtain ⟨u, hua⟩ : ∃ u : ↥Y, (u : A) = a := ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨v, hvb⟩ : ∃ v : ↥Y, (v : A) = b := ⟨⟨b, hb⟩, rfl⟩
    have huv : QuotientGroup.mk' (N.subgroupOf Y) u * QuotientGroup.mk' (N.subgroupOf Y) v =
        QuotientGroup.mk' (N.subgroupOf Y) v * QuotientGroup.mk' (N.subgroupOf Y) u :=
      IsCyclic.commGroup.mul_comm _ _
    have h1 : QuotientGroup.mk' (N.subgroupOf Y) (u * v * u⁻¹ * v⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, huv]
      group
    rw [QuotientGroup.mk'_apply] at h1
    have h2 : u * v * u⁻¹ * v⁻¹ ∈ N.subgroupOf Y :=
      (QuotientGroup.eq_one_iff (N := N.subgroupOf Y) _).1 h1
    have h3 := Subgroup.mem_subgroupOf.1 h2
    simpa [hua, hvb] using h3
  ·
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).1 hcop hpdvd

theorem n4_coprime_card_of_le_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Type} [Group X]
    [Finite X] {D K : Subgroup X} (hD : IsPGroup 2 D) (hK : K ≤ D) :
    Nat.Coprime p (Nat.card K) := by
  obtain ⟨k, hk⟩ := hD.exists_card_eq
  have hpc : Nat.Coprime p 2 :=
    (Nat.coprime_primes (Fact.out : Nat.Prime p) Nat.prime_two).mpr hp2
  exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hK)
    (by rw [hk]; exact Nat.Coprime.pow_right k hpc)

theorem n4_not_mem_of_coprime {p : ℕ} [Fact p.Prime] {X : Type} [Group X] {N : Subgroup X}
    {z : X} (hN : Nat.Coprime p (Nat.card N)) (hzN : z ∈ N) (hzp : orderOf z = p) : False := by
  have h1 : orderOf (⟨z, hzN⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hzp] at h1
  have h2 : p = 1 := hN.eq_one_of_dvd h1
  have h3 := (Fact.out : Nat.Prime p).two_le
  omega

theorem n4_no_simple_section {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Type} [Group X] [Finite X]
    {D C Y : Subgroup X} [D.Normal] (hD : IsPGroup 2 D) (hC : IsPSolvable p ↥C)
    (hY : ∀ y ∈ Y, ∃ d ∈ D, ∃ c ∈ C, y = d * c) {z : X} (hz : z ∈ Y) (hzp : orderOf z = p)
    (hsec : S622IsSimpleSection Y (rankThreePrimeCore p Y)) : False := by
  have hT : IsPSolvable p ↥(((QuotientGroup.mk' D).comp C.subtype).range) :=
    n4_pSolvable_range ((QuotientGroup.mk' D).comp C.subtype) hC
  have hK : D ⊓ Y ≤ rankThreePrimeCore p Y := by
    have hKn : ((D ⊓ Y).subgroupOf Y).Normal := by
      rw [normal_subgroupOf_iff (inf_le_right : D ⊓ Y ≤ Y)]
      intro h k hh hk
      obtain ⟨hhD, hhY⟩ := Subgroup.mem_inf.mp hh
      exact Subgroup.mem_inf.mpr
        ⟨Subgroup.Normal.conj_mem inferInstance h hhD k,
          Y.mul_mem (Y.mul_mem hk hhY) (Y.inv_mem hk)⟩
    have hKc : Nat.Coprime p (Nat.card (D ⊓ Y : Subgroup X)) :=
      n4_coprime_card_of_le_two hp2 hD inf_le_left
    unfold rankThreePrimeCore relPPrimeCore
    exact le_sSup ⟨inf_le_right, hKn, hKc⟩
  have hzN : z ∉ rankThreePrimeCore p Y := fun h =>
    n4_not_mem_of_coprime (CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p Y).2.2 h hzp
  have hzp' : z ^ p = 1 := by
    rw [← hzp]
    exact pow_orderOf_eq_one z
  have hmem : ∀ y : X, y ∈ Y →
      QuotientGroup.mk' D y ∈ ((QuotientGroup.mk' D).comp C.subtype).range := by
    intro y hy
    obtain ⟨d, hd, c, hc, rfl⟩ := hY y hy
    refine MonoidHom.mem_range.mpr ⟨⟨c, hc⟩, ?_⟩
    have hd1 : QuotientGroup.mk' D d = 1 := (QuotientGroup.eq_one_iff d).mpr hd
    show QuotientGroup.mk' D c = QuotientGroup.mk' D (d * c)
    rw [map_mul, hd1, one_mul]
  let ψ : Y →* ((QuotientGroup.mk' D).comp C.subtype).range :=
    { toFun := fun y => ⟨QuotientGroup.mk' D (y : X), hmem (y : X) y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hker : ∀ y : Y, ψ y = 1 → (y : X) ∈ rankThreePrimeCore p Y := by
    intro y hy
    have h1 : QuotientGroup.mk' D (y : X) = 1 := congrArg Subtype.val hy
    exact hK (Subgroup.mem_inf.mpr ⟨(QuotientGroup.eq_one_iff (y : X)).mp h1, y.2⟩)
  exact n4_false_of_hom_pSolvable hsec hz hzN hzp' ψ hker hT

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
