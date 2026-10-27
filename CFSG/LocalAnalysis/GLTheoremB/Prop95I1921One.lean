module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Asm
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921AutPerm
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1921

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open Equiv Equiv.Perm
open scoped commutatorElement

section Main1

variable {X : Type} [Group X] [Finite X] {K : Subgroup X}

theorem input19_21_1_core (hH : HatSevenOddInverts)
    (hK : IsComponentOf K ⊤) (hO3 : GLAPPrimeCore 3 ↥K = ⊥)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 7))) {x : X} (hx : orderOf x = 3)
    {T : Subgroup X} (hT : T ≤ pCoreOf 2 (Subgroup.centralizer ({x} : Set X)))
    (hTK : ¬ T ≤ Subgroup.centralizer (K : Set X)) :
    x ∈ Subgroup.normalizer (K : Set X) ∧ T ≤ Subgroup.normalizer (K : Set X) ∧
      (∃ c : ↥(alternatingGroup (Fin 7)), (c : Perm (Fin 7)).IsThreeCycle ∧
          ConjActsAs x K e c) ∧
      IsRootFour (((pCoreOf 2 (K ⊓ Subgroup.centralizer ({x} : Set X))).subgroupOf K).map
        (QuotientGroup.mk' (Subgroup.center ↥K)) |>.map e.toMonoidHom) ∧
      inducedAutGroup T K ≤
        ((pCoreOf 2 (K ⊓ Subgroup.centralizer ({x} : Set X))).subgroupOf K).map
          (MulAut.conj : ↥K →* MulAut ↥K) := by
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hxN : x ∈ Subgroup.normalizer (K : Set X) := by
    by_contra hxn
    exact hTK (le_centralizer_of_not_mem_normalizer Nat.prime_three (by norm_num) hK hO3 hx3
      hxn hT)
  set T₀ := pCoreOf 2 (Subgroup.centralizer ({x} : Set X)) with hT₀def
  have hT₀N : T₀ ≤ Subgroup.normalizer (K : Set X) :=
    pCoreOf_centralizer_singleton_le_normalizer Nat.prime_three (by norm_num) hK hO3 hx3
  have hTN : T ≤ Subgroup.normalizer (K : Set X) := hT.trans hT₀N
  refine ⟨hxN, hTN, ?_⟩
  have hKq := isQuasisimple_of_comp hK
  have hodd := center_no_two_elements Nat.prime_three (by norm_num) hO3
  obtain ⟨θ, hθinj, hθind, hθinn⟩ := exists_autToPerm_of_perfect hK.2.2.1
    (by norm_num : 5 ≤ 7) (by norm_num : (7 : ℕ) ≠ 6) e
  let D : APD K e := ⟨θ, hθinj, hθind, hθinn⟩
  set σ := D.θ (K.normalizerMonoidHom ⟨x, hxN⟩) with hσdef
  have hσ3 : σ ^ 3 = 1 := by
    have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 := Subtype.ext hx3
    rw [hσdef, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hσev : sign σ = 1 := by
    rcases Int.units_eq_one_or (sign σ) with h | h
    · exact h
    · have h1 : (-1 : ℤˣ) ^ 3 = 1 := by simpa [map_pow, h] using congrArg sign hσ3
      exact absurd h1 (by decide)
  have hT₀2 : ∀ t ∈ T₀, ∃ n : ℕ, t ^ (2 ^ n) = 1 := by
    intro t ht
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
      (Subgroup.centralizer ({x} : Set X))) ⟨t, ht⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hρ1 : K.normalizerMonoidHom ⟨x, hxN⟩ = 1 := D.inj (by rw [← hσdef, h1, map_one])
    have hxC : x ∈ Subgroup.centralizer (K : Set X) :=
      (normalizerMonoidHom_eq_one_iff hxN).1 hρ1
    have hKC : K ≤ Subgroup.centralizer ({x} : Set X) := by
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hxC k hk
    have hT₀C : T₀ ≤ Subgroup.centralizer (K : Set X) :=
      le_centralizer_of_normalized_by hK hT₀2 hT₀N (fun k hk s hs =>
        (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ (hKC hk)) s).1 hs)
    exact hTK (hT.trans hT₀C)
  have hdata := perm_data_seven hH hK hO3 D hx3 hxN hσ1
  obtain ⟨t, htT, htnc⟩ : ∃ t ∈ T, t ∉ Subgroup.centralizer (K : Set X) := by
    by_contra hcon
    push Not at hcon
    exact hTK hcon
  have htN : t ∈ Subgroup.normalizer (K : Set X) := hTN htT
  have hsne : D.θ (K.normalizerMonoidHom ⟨t, htN⟩) ≠ 1 := by
    intro h1
    apply htnc
    exact (normalizerMonoidHom_eq_one_iff htN).1 (D.inj (by rw [h1, map_one]))
  have hsmem : D.θ (K.normalizerMonoidHom ⟨t, htN⟩) ∈ (inducedAutGroup T₀ K).map D.θ :=
    (mem_sig_iff D.θ T₀).2 ⟨t, htN, hT htT, rfl⟩
  have hc4 : (fixF σ).card = 4 := by
    rcases (hdata _ hsmem).2 with h | ⟨h4, -⟩
    · exact absurd h hsne
    · exact h4
  have hthree : σ.IsThreeCycle := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hct := cycleType_of_pow_prime_eq_one hσ3
    have hsum : σ.cycleType.sum = σ.support.card := sum_cycleType σ
    have hsupp : σ.support.card = 3 := by
      have : σ.support = (fixF σ)ᶜ := by
        ext y; simp [fixF, Perm.mem_support]
      rw [this, Finset.card_compl, hc4]; simp
    rw [hct] at hsum
    simp only [Multiset.sum_replicate, smul_eq_mul] at hsum
    have hm : σ.cycleType.card = 1 := by omega
    show σ.cycleType = {3}
    rw [hct, hm]; rfl
  set c : ↥(alternatingGroup (Fin 7)) := ⟨σ, Perm.mem_alternatingGroup.2 hσev⟩ with hc
  have hconj : ConjActsAs x K e c := by
    intro k k' hk'
    have h1 := D.ind (K.normalizerMonoidHom ⟨x, hxN⟩) k
    have hk'eq : K.normalizerMonoidHom ⟨x, hxN⟩ k = k' := Subtype.ext hk'.symm
    rw [hk'eq] at h1
    rw [h1]
    apply Subtype.ext
    rfl
  refine ⟨⟨c, hthree, hconj⟩, ?_⟩
  set Vq : Subgroup ↥(alternatingGroup (Fin 7)) :=
    (((pCoreOf 2 (K ⊓ Subgroup.centralizer ({x} : Set X))).subgroupOf K).map
      (QuotientGroup.mk' (Subgroup.center ↥K)) |>.map e.toMonoidHom) with hVq
  have hVchar : ∀ g : ↥(alternatingGroup (Fin 7)),
      g ∈ Vq ↔ (g : Perm (Fin 7)) ∈ V4 (fixF σ) hc4 := by
    intro g
    constructor
    · intro hg
      obtain ⟨u, hu, hug⟩ := Subgroup.mem_map.1 hg
      obtain ⟨q, hq, hqu⟩ := Subgroup.mem_map.1 hu
      have hq' : (q : X) ∈ pCoreOf 2 (K ⊓ Subgroup.centralizer ({x} : Set X)) := hq
      have hqKC : (q : X) ∈ K ⊓ Subgroup.centralizer ({x} : Set X) :=
        CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq'
      have hqC : (q : X) ∈ Subgroup.centralizer ({x} : Set X) := hqKC.2
      obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
        (K ⊓ Subgroup.centralizer ({x} : Set X))) ⟨(q : X), hq'⟩
      have hqn : q ^ (2 ^ n) = 1 := by
        apply Subtype.ext
        have := congrArg Subtype.val hn
        simpa using this
      have hgq : g = e (QuotientGroup.mk q) := by rw [← hug, ← hqu]; rfl
      have hgeven : sign (g : Perm (Fin 7)) = 1 := Perm.mem_alternatingGroup.1 g.2
      have hg2 : (g : Perm (Fin 7)) ^ (2 ^ n) = 1 := by
        have h1 : g ^ (2 ^ n) = 1 := by
          rw [hgq, ← map_pow, ← QuotientGroup.mk_pow, hqn, QuotientGroup.mk_one, map_one]
        simpa using congrArg Subtype.val h1
      have hρq : K.normalizerMonoidHom ⟨x, hxN⟩ q = q := by
        apply Subtype.ext
        show x * (q : X) * x⁻¹ = q
        have := Subgroup.mem_centralizer_singleton_iff.1 hqC
        calc x * (q : X) * x⁻¹ = (q * x) * x⁻¹ := by rw [this]
          _ = q := by group
      have hcomm : (g : Perm (Fin 7)) * σ = σ * (g : Perm (Fin 7)) := by
        have h1 := D.ind (K.normalizerMonoidHom ⟨x, hxN⟩) q
        rw [hρq] at h1
        have h2 : (e (QuotientGroup.mk q) : Perm (Fin 7)) =
            σ * (e (QuotientGroup.mk q) : Perm (Fin 7)) * σ⁻¹ := congrArg Subtype.val h1
        rw [← hgq] at h2
        calc (g : Perm (Fin 7)) * σ = (σ * (g : Perm (Fin 7)) * σ⁻¹) * σ := by rw [← h2]
          _ = σ * (g : Perm (Fin 7)) := by group
      rcases (locB7 hσ3 hσ1 hcomm hgeven
        (pow_four_of_two_power_seven _ ⟨n, hg2⟩)).2 with h | ⟨-, h⟩
      · exact (mem_V4 hc4).2 (Or.inl h)
      · exact (mem_V4 hc4).2 (Or.inr h)
    · intro hg4
      let E : Subgroup (↥K ⧸ Subgroup.center ↥K) :=
        (V4 (fixF σ) hc4).comap ((alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom)
      have hE : ∀ ε, ε ∈ E ↔ ((e ε : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) ∈
          V4 (fixF σ) hc4 := fun ε => Iff.rfl
      have hE2 : ∀ ε ∈ E, ∃ n : ℕ, ε ^ (2 ^ n) = 1 := by
        intro ε hε
        refine ⟨1, ?_⟩
        have h1 := (mem_V4 hc4).1 ((hE ε).1 hε)
        apply e.injective
        rw [map_pow, map_one]
        apply Subtype.ext
        rcases h1 with h | h
        · simp [h]
        · simpa [sq] using h.2.1
      have hEx : ∀ a : ↥K, (QuotientGroup.mk a : ↥K ⧸ Subgroup.center ↥K) ∈ E →
          (QuotientGroup.mk (K.normalizerMonoidHom ⟨x, hxN⟩ a) : ↥K ⧸ Subgroup.center ↥K) =
            QuotientGroup.mk a := by
        intro a ha
        have h1 := D.ind (K.normalizerMonoidHom ⟨x, hxN⟩) a
        have hcomm := V4_commute hc4 ((hE _).1 ha)
        apply e.injective
        rw [h1]
        apply Subtype.ext
        show σ * (e (QuotientGroup.mk a) : Perm (Fin 7)) * σ⁻¹ =
          (e (QuotientGroup.mk a) : Perm (Fin 7))
        rw [← hcomm]; group
      have hEn : ∀ c' : ↥K, (c' : X) ∈ Subgroup.centralizer ({x} : Set X) → ∀ ε ∈ E,
          (QuotientGroup.mk c' : ↥K ⧸ Subgroup.center ↥K) * ε * (QuotientGroup.mk c')⁻¹ ∈ E := by
        intro c' hc'C ε hε
        have hcx : (c' : X) * x = x * c' := Subgroup.mem_centralizer_singleton_iff.1 hc'C
        have hρc : MulAut.conj c' * K.normalizerMonoidHom ⟨x, hxN⟩ =
            K.normalizerMonoidHom ⟨x, hxN⟩ * MulAut.conj c' := by
          ext y
          show (c' : X) * (x * (y : X) * x⁻¹) * (c' : X)⁻¹ =
            x * ((c' : X) * (y : X) * (c' : X)⁻¹) * x⁻¹
          have hcx' : x⁻¹ * (c' : X)⁻¹ = (c' : X)⁻¹ * x⁻¹ := by
            rw [← mul_inv_rev, ← mul_inv_rev, hcx]
          calc (c' : X) * (x * (y : X) * x⁻¹) * (c' : X)⁻¹
              = ((c' : X) * x) * (y : X) * (x⁻¹ * (c' : X)⁻¹) := by group
            _ = (x * (c' : X)) * (y : X) * ((c' : X)⁻¹ * x⁻¹) := by rw [hcx, hcx']
            _ = x * ((c' : X) * (y : X) * (c' : X)⁻¹) * x⁻¹ := by group
        have hcomm : (e (QuotientGroup.mk c') : Perm (Fin 7)) * σ =
            σ * (e (QuotientGroup.mk c') : Perm (Fin 7)) := by
          rw [← D.inner c', hσdef, ← map_mul, ← map_mul, hρc]
        show ((e (QuotientGroup.mk c' * ε * (QuotientGroup.mk c')⁻¹) :
          ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) ∈ V4 (fixF σ) hc4
        rw [map_mul, map_mul, map_inv]
        exact V4_conj hc4 ((hE ε).1 hε) hcomm
      obtain ⟨Q, hQK, hQC, hQ2, hQn, hQE⟩ := exists_normal_two_lift hxN hodd E hE2 hEx hEn
      have hQle : Q ≤ pCoreOf 2 (K ⊓ Subgroup.centralizer ({x} : Set X)) :=
        Prop95Parts.Input18.le_pCoreOf_of_normal (fun q hq => ⟨hQK hq, hQC hq⟩) hQn
          (fun ⟨q, hq⟩ => by
            obtain ⟨n, hn⟩ := hQ2 q hq
            exact ⟨n, Subtype.ext hn⟩)
      obtain ⟨q, hqQ, hqk⟩ := hQE (e.symm g) (by rw [hE]; simpa using hg4)
      refine Subgroup.mem_map.2 ⟨QuotientGroup.mk' _ q, Subgroup.mem_map.2 ⟨q, hQle hqQ, rfl⟩, ?_⟩
      show e (QuotientGroup.mk q) = g
      rw [hqk]; simp
  refine ⟨isRootFour_of_V4 hc4 Vq hVchar, ?_⟩
  intro φ hφ
  obtain ⟨t', ht', ht'T, rfl⟩ := mem_inducedAutGroup.1 hφ
  have hs := (mem_sig_iff D.θ T₀).2 ⟨t', ht', hT ht'T, rfl⟩
  have hs' := hdata _ hs
  have hs4 : D.θ (K.normalizerMonoidHom ⟨t', ht'⟩) ∈ V4 (fixF σ) hc4 := by
    rcases hs'.2 with h | ⟨-, h⟩
    · exact (mem_V4 hc4).2 (Or.inl h)
    · exact (mem_V4 hc4).2 (Or.inr h)
  have hsev : sign (D.θ (K.normalizerMonoidHom ⟨t', ht'⟩)) = 1 := V4_sign hc4 hs4
  have hgV : (⟨_, Perm.mem_alternatingGroup.2 hsev⟩ : ↥(alternatingGroup (Fin 7))) ∈ Vq :=
    (hVchar _).2 hs4
  obtain ⟨u, hu, hug⟩ := Subgroup.mem_map.1 hgV
  obtain ⟨q, hq, hqu⟩ := Subgroup.mem_map.1 hu
  refine Subgroup.mem_map.2 ⟨q, hq, ?_⟩
  apply D.inj
  rw [D.inner]
  have h1 : e (QuotientGroup.mk q) = (⟨_, Perm.mem_alternatingGroup.2 hsev⟩ :
      ↥(alternatingGroup (Fin 7))) := by rw [← hug, ← hqu]; rfl
  rw [h1]

theorem input19_21_1_holds (hH : HatSevenOddInverts) :
    Input19_21_1 := by
  intro X _ _ p hp hp2 K hK hO e x hx T hT hTK
  have hKq : CFSG.IsQuasisimple ↥K := isQuasisimple_of_comp hK
  have hO3 : GLAPPrimeCore 3 ↥K = ⊥ := glaPPrimeCore_three_of_alt7 hKq hp hp2 hO e
  exact input19_21_1_core hH hK hO3 e hx hT hTK

end Main1

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1921
