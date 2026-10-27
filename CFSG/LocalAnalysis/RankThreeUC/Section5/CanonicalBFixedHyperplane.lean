module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.InvariantPrimeComplement
public import CFSG.LocalAnalysis.RankThreeUC.Section5.BFixedHyperplaneComplementCentralized
public import CFSG.LocalAnalysis.RankThreeUC.Section5.OrbitHasBFixedMember
public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.CanonicalBFixedHyperplane

open CFSG.LocalAnalysis.RankThreeUC.Section5

variable {G : Type} [Group G] [Finite G]

theorem le_commutator {P B E : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hexp : ∀ x ∈ P, x ^ p = 1)
    (hcop : (Nat.card B).Coprime p)
    (hBP : B ≤ Subgroup.normalizer (P : Set G))
    (hEP : E ≤ P) (hBE : B ≤ Subgroup.normalizer (E : Set G))
    (hCE : P ⊓ Subgroup.centralizer (B : Set G) ⊓ E = ⊥) :
    E ≤ ⁅B, P⁆ := by
  classical
  haveI : Fintype B := Fintype.ofFinite B
  letI : CommGroup P :=
    { (inferInstance : Group P) with
      mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  have hnP : ∀ b ∈ B, ∀ x ∈ P, b * x * b⁻¹ ∈ P := fun b hb x hx =>
    (Subgroup.mem_normalizer_iff.1 (hBP hb) x).1 hx
  have hnE : ∀ b ∈ B, ∀ x ∈ E, b * x * b⁻¹ ∈ E := fun b hb x hx =>
    (Subgroup.mem_normalizer_iff.1 (hBE hb) x).1 hx
  intro x hxE
  have hxP : x ∈ P := hEP hxE
  let X : P := ⟨x, hxP⟩
  let φ : B → P → P := fun b y => ⟨b * y * b⁻¹, hnP b b.2 y y.2⟩
  let K : Subgroup P := (⁅B, P⁆).subgroupOf P
  let c : B → P := fun b => φ b X * X⁻¹
  have hφ : ∀ (b : B) (y : P), ((φ b y : P) : G) = (b : G) * y * (b : G)⁻¹ := fun b y => rfl
  have hcK : ∀ b, c b ∈ K := by
    intro b
    show ((c b : P) : G) ∈ ⁅B, P⁆
    have h : (b : G) * x * (b : G)⁻¹ * x⁻¹ ∈ ⁅B, P⁆ := Subgroup.commutator_mem_commutator b.2 hxP
    have : ((c b : P) : G) = (b : G) * x * (b : G)⁻¹ * x⁻¹ := by
      show ((φ b X : P) : G) * ((X : P) : G)⁻¹ = _
      rw [hφ]
    rw [this]; exact h
  have hsplit : ∀ b, φ b X = c b * X := fun b => by simp [c]
  let Nn : P := ∏ b : B, φ b X
  have hprod : Nn = (∏ b : B, c b) * X ^ Nat.card B := by
    show ∏ b : B, φ b X = _
    simp_rw [hsplit]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  let ψ : B → P →* P := fun b => MonoidHom.mk' (φ b) (fun y z => by
    apply Subtype.ext
    simp only [hφ, Subgroup.coe_mul]
    group)
  have hψφ : ∀ (b b' : B) (y : P), ψ b (φ b' y) = φ (b * b') y := by
    intro b b' y
    apply Subtype.ext
    change (b : G) * ((b' : G) * y * (b' : G)⁻¹) * (b : G)⁻¹ = ((b * b' : B) : G) * y * ((b * b' : B) : G)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group
  have hNfix : ∀ b : B, ψ b Nn = Nn := by
    intro b
    show ψ b (∏ b' : B, φ b' X) = ∏ b' : B, φ b' X
    rw [map_prod]
    simp_rw [hψφ]
    exact Fintype.prod_equiv (Equiv.mulLeft b) _ _ (fun _ => rfl)
  have hNE : Nn ∈ E.subgroupOf P := by
    refine Subgroup.prod_mem _ (fun b _ => ?_)
    show ((φ b X : P) : G) ∈ E
    rw [hφ]; exact hnE b b.2 x hxE
  have hNmem : ((Nn : P) : G) ∈ P ⊓ Subgroup.centralizer (B : Set G) ⊓ E := by
    refine ⟨⟨Nn.2, ?_⟩, hNE⟩
    show (Nn : G) ∈ Subgroup.centralizer (B : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h : (b : G) * (Nn : G) * (b : G)⁻¹ = (Nn : G) := congrArg Subtype.val (hNfix ⟨b, hb⟩)
    calc (b : G) * (Nn : G) = ((b : G) * (Nn : G) * (b : G)⁻¹) * b := by group
      _ = (Nn : G) * b := by rw [h]
  rw [hCE, Subgroup.mem_bot] at hNmem
  have hN1 : Nn = 1 := Subtype.ext hNmem
  have hKX : X ^ Nat.card B ∈ K := by
    have h1 : X ^ Nat.card B = (∏ b : B, c b)⁻¹ := by
      rw [hN1] at hprod
      exact eq_inv_of_mul_eq_one_right hprod.symm
    rw [h1]
    exact K.inv_mem (Subgroup.prod_mem _ (fun b _ => hcK b))
  have hXp : X ^ p = 1 := Subtype.ext (hexp x hxP)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hXm : X = (X ^ Nat.card B) ^ m := by
    rw [← pow_mul]
    have h2 := Nat.div_add_mod (Nat.card B * m) p
    rw [hm] at h2
    calc X = X ^ (p * (Nat.card B * m / p) + 1) := by
          rw [pow_add, pow_mul, hXp, one_pow, one_mul, pow_one]
      _ = X ^ (Nat.card B * m) := by rw [h2]
  have : X ∈ K := by rw [hXm]; exact K.pow_mem hKX m
  exact this

theorem canonical {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    ⁅B, P⁆ ∈ Delta p P ρ ∧
    (P ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ ∧
      ∀ b ∈ B, b ≠ 1 →
        P ⊓ Subgroup.centralizer ({b} : Set G) = P ⊓ Subgroup.centralizer (B : Set G)) ∧
    ∀ E ∈ Delta p P ρ, B ≤ Subgroup.normalizer (E : Set G) → E = ⁅B, P⁆ := by
  classical
  have hS := hc.oddPrimeClassTwoAction.setting
  have hP : P.Normal := hc.faithfulBinaryIrreducibleAction.normal
  have hel := isElemAbelian_of_binary_rank_counterexample hc
  have hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hexp : ∀ x ∈ P, x ^ p = 1 := fun x hx => by
    have := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : P)
    rw [hS.exponent] at this
    exact congrArg Subtype.val this
  have hcop : (Nat.card B).Coprime p := by
    have h19 := (three_lt_pRank_and_prime_not_dvd_card_actor hc).2
    by_contra h
    apply h19
    refine ⟨hS.prime, ?_⟩
    by_contra hd
    exact h ((Nat.Prime.coprime_iff_not_dvd hS.prime).2 hd).symm
  have hBP : B ≤ Subgroup.normalizer (P : Set G) := hS.normB
  have hCb : ∀ b ∈ B, b ≠ 1 → Nat.card ↥(P ⊓ Subgroup.centralizer ({b} : Set G)) ≤ p := by
    intro b hb hb1
    obtain ⟨g, hg⟩ := (hc.oddPrimeClassTwoAction.cyclic_centralizer b hb hb1).exists_generator
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    refine Nat.le_of_dvd hS.prime.pos (orderOf_dvd_of_pow_eq_one ?_)
    apply Subtype.ext
    exact hexp g.1 (Subgroup.mem_inf.1 g.2).1
  have key : ∀ E ∈ Delta p P ρ, B ≤ Subgroup.normalizer (E : Set G) →
      ∃ R : Subgroup G, R ≤ P ∧ Nat.card R = p ∧ P ⊓ Subgroup.centralizer (B : Set G) = R ∧
        (∀ b ∈ B, b ≠ 1 → P ⊓ Subgroup.centralizer ({b} : Set G) = R) ∧ E = ⁅B, P⁆ := by
    intro E hE hBN
    obtain ⟨R, hRP, hRE, hRsup, hRcard, hUR, hBR⟩ :=
      InvariantPrimeComplement.exists_complement hc E hE hBN
    have hBC := BFixedHyperplaneComplementCentralized.centralizes hc E hE hBN R hRP hRE
      hRsup hRcard hUR hBR
    have hEP : E ≤ P := hE.1
    have hRC : R ≤ P ⊓ Subgroup.centralizer (B : Set G) := by
      intro r hr
      refine ⟨hRP hr, ?_⟩
      show r ∈ Subgroup.centralizer (B : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (Subgroup.mem_centralizer_iff.1 (hBC hb) r hr).symm
    obtain ⟨b0, hb0, hb01⟩ : ∃ b ∈ B, b ≠ 1 := by
      obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc.oddPrimeClassTwoAction.actor_ne_bot
      exact ⟨b, b.2, fun h => hb (Subtype.ext h)⟩
    have hsingle : ∀ b ∈ B, b ≠ 1 → P ⊓ Subgroup.centralizer ({b} : Set G) = R := by
      intro b hb hb1
      have hle : R ≤ P ⊓ Subgroup.centralizer ({b} : Set G) := by
        intro r hr
        refine ⟨hRP hr, ?_⟩
        show r ∈ Subgroup.centralizer ({b} : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ((Subgroup.mem_centralizer_iff.1 (hBC hb) r hr)).symm
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hRcard]; exact hCb b hb hb1)).symm
    have hCeq : P ⊓ Subgroup.centralizer (B : Set G) = R := by
      refine le_antisymm ?_ hRC
      rw [← hsingle b0 hb0 hb01]
      exact inf_le_inf_left _ (Subgroup.centralizer_le (by simpa using hb0))
    refine ⟨R, hRP, hRcard, hCeq, hsingle, ?_⟩
    have h1 : E ≤ ⁅B, P⁆ :=
      le_commutator hS.prime hcomm hexp hcop hBP hEP hBN (by rw [hCeq, hRE])
    have h2 : ⁅B, P⁆ ≤ E := by
      rw [Subgroup.commutator_le]
      intro b hb x hx
      have hx' : x ∈ Subgroup.closure ((R : Set G) ∪ (E : Set G)) := by
        rw [← Subgroup.sup_eq_closure, hRsup]; exact hx
      have hmain : x ∈ P ∧ ∀ b ∈ B, b * x * b⁻¹ * x⁻¹ ∈ E := by
        refine Subgroup.closure_induction (p := fun x _ => x ∈ P ∧ ∀ b ∈ B, b * x * b⁻¹ * x⁻¹ ∈ E)
          ?_ ?_ ?_ ?_ hx'
        · rintro y (hy | hy)
          · refine ⟨hRP hy, fun b hb => ?_⟩
            have := (Subgroup.mem_centralizer_iff.1 (hBC hb) y hy)
            have h3 : b * y * b⁻¹ * y⁻¹ = 1 := by
              rw [← this]; group
            rw [h3]; exact E.one_mem
          · refine ⟨hEP hy, fun b hb => ?_⟩
            exact E.mul_mem ((Subgroup.mem_normalizer_iff.1 (hBN hb) y).1 hy) (E.inv_mem hy)
        · exact ⟨P.one_mem, fun b hb => by simpa using E.one_mem⟩
        · rintro y z _ _ ⟨hyP, hy⟩ ⟨hzP, hz⟩
          refine ⟨P.mul_mem hyP hzP, fun b hb => ?_⟩
          have hyb : b * y * b⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 (hBP hb) y).1 hyP
          have hzb : b * z * b⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 (hBP hb) z).1 hzP
          have : b * (y * z) * b⁻¹ * (y * z)⁻¹ =
              (b * y * b⁻¹ * y⁻¹) * (b * z * b⁻¹ * z⁻¹) := by
            calc b * (y * z) * b⁻¹ * (y * z)⁻¹
                = (b * y * b⁻¹) * (((b * z * b⁻¹) * z⁻¹) * y⁻¹) := by group
              _ = (b * y * b⁻¹) * (y⁻¹ * ((b * z * b⁻¹) * z⁻¹)) := by
                  rw [hcomm _ (P.mul_mem hzb (P.inv_mem hzP)) _ (P.inv_mem hyP)]
              _ = _ := by group
          rw [this]; exact E.mul_mem (hy b hb) (hz b hb)
        · rintro y _ ⟨hyP, hy⟩
          refine ⟨P.inv_mem hyP, fun b hb => ?_⟩
          have hyb : b * y * b⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 (hBP hb) y).1 hyP
          have : b * y⁻¹ * b⁻¹ * (y⁻¹)⁻¹ = (b * y * b⁻¹ * y⁻¹)⁻¹ := by
            calc b * y⁻¹ * b⁻¹ * (y⁻¹)⁻¹ = (b * y * b⁻¹)⁻¹ * y := by group
              _ = y * (b * y * b⁻¹)⁻¹ := hcomm _ (P.inv_mem hyb) _ hyP
              _ = _ := by group
          rw [this]; exact E.inv_mem (hy b hb)
      exact hmain.2 b hb
    exact le_antisymm h1 h2
  obtain ⟨b0, hb0, hb01⟩ : ∃ b ∈ B, b ≠ 1 := by
    obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc.oddPrimeClassTwoAction.actor_ne_bot
    exact ⟨b, b.2, fun h => hb (Subtype.ext h)⟩
  have hne : ∃ D, D ∈ Delta p P ρ := by
    by_contra hno
    push Not at hno
    have hint := isInternal_hyperplane_fixedSubmodule_of_binary_rank_counterexample hc
    have htop := hint.submodule_iSup_eq_top
    haveI : IsEmpty ↥(Delta p P ρ) := ⟨fun D => hno D.1 D.2⟩
    rw [iSup_of_empty] at htop
    have hzero : ∀ v : V, v = 0 := fun v => by
      have : v ∈ (⊤ : Submodule (ZMod 2) V) := Submodule.mem_top
      rw [← htop] at this
      exact (Submodule.mem_bot _).1 this
    apply hb01
    apply hc.faithfulBinaryIrreducibleAction.faithful
    rw [map_one]
    ext v
    simp [hzero v]
  obtain ⟨D, hD⟩ := hne
  obtain ⟨s, -, hs⟩ := OrbitHasBFixedMember.exists_member hc hD
  have hE := DeltaConjugationAction.map_mem (p := p) hP ρ s hD
  obtain ⟨R, hRP, hRcard, hC, hsing, hEq⟩ := key _ hE (fun b hb => hs b hb)
  have hall : ∀ E ∈ Delta p P ρ, B ≤ Subgroup.normalizer (E : Set G) → E = ⁅B, P⁆ := by
    intro E hE' hBN'
    obtain ⟨_, _, _, _, _, h⟩ := key E hE' hBN'
    exact h
  refine ⟨hEq ▸ hE, ⟨?_, fun b hb hb1 => by rw [hC, hsing b hb hb1]⟩, hall⟩
  rw [hC]
  intro h
  rw [h, Subgroup.card_bot] at hRcard
  exact hS.prime.one_lt.ne hRcard

end CFSG.LocalAnalysis.RankThreeUC.Section5.CanonicalBFixedHyperplane
end
