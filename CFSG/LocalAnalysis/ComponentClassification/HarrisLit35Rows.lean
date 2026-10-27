module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35Inputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36Rows
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma21

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup

structure Config (G : Type) [Group G] [Finite G] (p : ℕ) (w v : G) (L K : Subgroup G) :
    Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  kProper : Assembly.KProper Blueprint.Catalog G
  not_catalog : ¬ Blueprint.Catalog G
  prime : p.Prime
  ne_two : p ≠ 2
  orderOf_w : orderOf w = 2
  v_sq : v * v = 1
  v_not_mem : v ∉ zpowers w
  v_mem : v ∈ centralizer {w}
  compL : IsTwoComponentIn L (centralizer {w} ⊓ centralizer {v})
  mTypeL : IsMTypeSchur p ↥L
  slTwo : ∃ k : ℕ, 1 ≤ k ∧ 5 ≤ p ^ k ∧ IsSLTwoOver (p ^ k) (↥L ⧸ pPrimeCore 2 ↥L)
  w_mem_L : w ∈ L
  K_eq : K = GSThmB.conjClosure L (GSThmB.layerIn (centralizer {w}))
  L_le : L ≤ K
  compK : IsTwoComponentIn K (centralizer {w})
  w_mem_K : w ∈ K
  not_mType : ¬ IsMTypeSchur p ↥K
  K_v : K.map (MulAut.conj v).toMonoidHom = K

@[expose] def Concl {G : Type} [Group G] (p : ℕ) (v : G) (L K : Subgroup G) : Prop :=
  L = GSThmB.layerIn (K ⊓ centralizer {v}) ∧
    ((p = 7 ∧ IsSLTwoOver 7 (↥L ⧸ pPrimeCore 2 ↥L) ∧
        IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) ∧
        Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) = 16 ∧
        GrSLit.IsL34Type ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K))) ∨
      (p = 5 ∧ IsSLTwoOver 5 (↥L ⧸ pPrimeCore 2 ↥L) ∧ ∃ n : ℕ, 4 ≤ n ∧
        IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) ∧
        Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) = 2 ∧
        Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃*
          alternatingGroup (Fin (2 * n + 1)))) ∨
      (p = 3 ∧ IsSLTwoOver 9 (↥L ⧸ pPrimeCore 2 ↥L) ∧ ∃ n : ℕ, 4 ≤ n ∧
        IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) ∧
        Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) = 2 ∧
        Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃*
          alternatingGroup (Fin (2 * n)))))

@[expose] def RowFor (C : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (w v : G) (L K : Subgroup G),
    Config G p w v L K → C (↥K ⧸ Open.fusionZStar ↥K) → Concl p v L K

theorem nonempty_fusionZStar_quotient_equiv (X : Type*) [Group X] :
    Nonempty (X ⧸ Open.fusionZStar X ≃*
      (X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)) := by
  set Q := X ⧸ pPrimeCore 2 X
  let ψ : X →* Q ⧸ center Q :=
    (QuotientGroup.mk' (center Q)).comp (QuotientGroup.mk' (pPrimeCore 2 X))
  have hs : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hk : Open.fusionZStar X = ψ.ker := by
    ext x
    rw [MonoidHom.mem_ker, FooteLit.mem_fusionZStar_iff_forall, ← FooteLit.mk_mem_center_iff]
    change _ ↔ QuotientGroup.mk' (center Q) (QuotientGroup.mk' (pPrimeCore 2 X) x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  exact ⟨QuotientGroup.liftEquiv _ hs hk⟩

namespace Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {w v : G} {L K : Subgroup G}

theorem quasisimple_quot (h : Config G p w v L K) : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
  h.compK.2.2.2

theorem nonempty_bar_equiv (_h : Config G p w v L K) :
    Nonempty (↥K ⧸ Open.fusionZStar ↥K ≃*
      (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) :=
  nonempty_fusionZStar_quotient_equiv ↥K

theorem simple_bar (h : Config G p w v L K) : IsSimpleGroup (↥K ⧸ Open.fusionZStar ↥K) := by
  obtain ⟨e⟩ := h.nonempty_bar_equiv
  have := h.quasisimple_quot.2.1
  exact e.isSimpleGroup

theorem nonabelian_bar (h : Config G p w v L K) :
    ∃ a b : ↥K ⧸ Open.fusionZStar ↥K, a * b ≠ b * a := by
  obtain ⟨e⟩ := h.nonempty_bar_equiv
  obtain ⟨a, b, hab⟩ := h.quasisimple_quot.2.2
  refine ⟨e.symm a, e.symm b, fun hc => hab (e.symm.injective ?_)⟩
  rw [map_mul, map_mul, hc]

theorem ne_top (h : Config G p w v L K) : K ≠ ⊤ := by
  intro hK
  have := h.simple
  have hZ : center G = ⊥ := CatLeaf.center_eq_bot_of_simple h.nonabelian
  have hw : w ∈ center G := by
    rw [mem_center_iff]
    intro g
    have hg : g ∈ centralizer ({w} : Set G) := h.compK.1 (hK ▸ mem_top g)
    exact mem_centralizer_singleton_iff.mp hg
  rw [hZ, mem_bot] at hw
  have h2 := h.orderOf_w
  rw [hw, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem catalog_bar (h : Config G p w v L K) :
    Blueprint.Catalog (↥K ⧸ Open.fusionZStar ↥K) := by
  have := h.simple_bar
  exact QuasithinUnique.catalog_of_kProper_of_surjective h.kProper K h.ne_top _
    h.nonabelian_bar (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)

end Config

theorem identFact_of_rows (hAlt : RowFor N36.IsAlt) (hCl : RowFor Milestones.ClassicalRep)
    (hEx : RowFor Blueprint.ExceptionalRep) (hSp : RowFor Blueprint.NativeSporadic.SporadicRep) :
    Harris81Lemma35IdentFact := by
  intro G _ _ hs hnonab hK hcat p hp hp2 w v hw hv2 hvw hvM L hL hM k hk hs5 hLsl hwL K hKeq hLK
    hKc hwK hKM hKv
  have hc : Config G p w v L K :=
    ⟨hs, hnonab, hK, hcat, hp, hp2, hw, hv2, hvw, hvM, hL, hM, ⟨k, hk, hs5, hLsl⟩, hwL, hKeq, hLK,
      hKc, hwK, hKM, hKv⟩
  rcases hc.catalog_bar with ⟨q, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | hcl | hex | hsp
  · exfalso
    obtain ⟨a, b, hab⟩ := hc.nonabelian_bar
    apply hab
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  · exact hAlt G p w v L K hc ⟨n, hn, ⟨e⟩⟩
  · exact hCl G p w v L K hc hcl
  · exact hEx G p w v L K hc hex
  · exact hSp G p w v L K hc hsp

end CFSG.ComponentClassification.HarrisLit.L35
