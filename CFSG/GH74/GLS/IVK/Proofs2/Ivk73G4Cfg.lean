module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Defs
public import CFSG.GH74.GLS.C3.Layer1.BkIvk73G
public import CFSG.GH74.GLS.LU.Local.Transport

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint

structure Ivk73Cfg (N : Type) [Group N] [Finite N] (L K Q : Subgroup N) : Prop where
  gen4 : Gen4 N
  ghList : GHList ↥L
  kgroup : IsKGroupNative N
  normal : L.Normal
  simple : IsSimpleGroup ↥L
  cent_trivial : ∀ n : N, (∀ l ∈ L, n * l = l * n) → n = 1
  K_le : K ≤ L
  K_quasi : IsQuasisimple ↥K
  K_u2 : InU2 (↥K ⧸ pPrimeCore 2 ↥K)
  Q_sylow : IsSylowOf 2 Q (centralizer (K : Set N))
  Q_rank : 2 ≤ pRank 2 ↥Q
  terminal : ∀ y : N, orderOf y = 2 → y ∈ centralizer (K : Set N) →
    IsCompIn (centralizer ({y} : Set N)) K

@[expose] def Ivk73Concl (N : Type) [Group N] [Finite N] (L K Q : Subgroup N) : Prop :=
  IsElementaryAbelian 2 ↥Q ∧ Nat.card ↥Q = 4 ∧
    ((Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 5)) ∧
        NativeSporadic.IsSporadic ↥L .M12 ∧ Nat.card N = 2 * Nat.card ↥L) ∨
      (Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 5)) ∧
        NativeSporadic.IsSporadic ↥L .J2 ∧ (L = ⊤ ∨ Nat.card N = 2 * Nat.card ↥L)) ∨
      (L = ⊤ ∧ ∃ n ∈ ({5, 6, 7} : Finset ℕ),
        Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin n)) ∧
        Nonempty (↥L ≃* alternatingGroup (Fin (n + 4)))))

section Transfer

variable {G : Type} [Group G] [Finite G] {N L K Q : Subgroup G}

theorem ivk73Cfg_of_subgroup (hgen : Gen4 ↥N) (hGH : GHList ↥L) (hN : IsKGroupNative ↥N)
    (hsoc : L ≤ N ∧ (∀ n ∈ N, ∀ l ∈ L, n * l * n⁻¹ ∈ L) ∧ IsSimpleGroup ↥L ∧
      ∀ n ∈ N, (∀ l ∈ L, n * l = l * n) → n = 1)
    (hKL : K ≤ L) (hKq : IsQuasisimple ↥K) (hU2 : InU2 (↥K ⧸ pPrimeCore 2 ↥K))
    (hQ : IsSylowOf 2 Q (centralizer (K : Set G) ⊓ N)) (hrank : 2 ≤ pRank 2 ↥Q)
    (hterm : ∀ y ∈ N, orderOf y = 2 → y ∈ centralizer (K : Set G) →
      IsCompIn (centralizer ({y} : Set G) ⊓ N) K) :
    Ivk73Cfg ↥N (L.subgroupOf N) (K.subgroupOf N) (Q.subgroupOf N) := by
  obtain ⟨hLN, hnorm, hLs, hcent⟩ := hsoc
  have hKN : K ≤ N := hKL.trans hLN
  have hQle : Q ≤ centralizer (K : Set G) ⊓ N := hQ.le
  have hQN : Q ≤ N := hQle.trans inf_le_right
  let ψ : ↥(K.subgroupOf N) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKN
  let e2 : (↥(K.subgroupOf N) ⧸ pPrimeCore 2 ↥(K.subgroupOf N)) ≃* (↥K ⧸ pPrimeCore 2 ↥K) :=
    QuotientGroup.congr _ _ ψ (pPrimeCore_map_iso 2 ψ)
  refine
    { gen4 := hgen
      ghList := GHList.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLN).symm hGH
      kgroup := hN
      normal := ⟨fun l hl n => ?_⟩
      simple := ((Subgroup.subgroupOfEquivOfLe hLN).isSimpleGroup_congr).2 hLs
      cent_trivial := fun n hn => ?_
      K_le := fun k hk => hKL hk
      K_quasi := CFSG.LocalCores.isQuasisimple_of_mulEquiv ψ.symm hKq
      K_u2 := inU2_of_mulEquiv e2.symm hU2
      Q_sylow := ?_
      Q_rank := ?_
      terminal := ?_ }
  · rw [Subgroup.mem_subgroupOf] at hl ⊢
    exact hnorm n n.2 l hl
  · apply Subtype.ext
    apply hcent n n.2
    intro l hl
    have := hn ⟨l, hLN hl⟩ (show (⟨l, hLN hl⟩ : ↥N) ∈ L.subgroupOf N from hl)
    exact congrArg Subtype.val this
  · rw [C3.Layer1.Bk.centralizer_subgroupOf_eq hKN]
    exact C3.Layer1.Bk.isSylowOf_subgroupOf_of_le hQle inf_le_right hQ
  · rw [Stage1.Thm2.Recip.pRank_eq_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hQN)]
    exact hrank
  · intro y' hy2 hyc
    have hyG : (y' : G) ∈ N := y'.2
    have hy2G : orderOf (y' : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hy2
    have hycG : (y' : G) ∈ centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have := Subgroup.mem_centralizer_iff.1 hyc ⟨k, hKN hk⟩
        (show (⟨k, hKN hk⟩ : ↥N) ∈ K.subgroupOf N from hk)
      exact congrArg Subtype.val this
    have h1 := hterm (y' : G) hyG hy2G hycG
    have hcen : centralizer ({y'} : Set ↥N) = (centralizer ({(y' : G)} : Set G) ⊓ N).subgroupOf N := by
      rw [Subgroup.inf_subgroupOf_right]
      exact EvenCore.centralizer_singleton_mk_eq (N := N) (y' : G) hyG
    refine ⟨?_, ?_⟩
    · rw [hcen]
      intro k hk
      exact h1.1 hk
    · rw [hcen]
      exact (LU.Local.isComponent_subgroupOf_iff' (K := K) (M := centralizer ({(y' : G)} : Set G) ⊓ N)
        (H := N) inf_le_right).2 h1.2

omit [Finite G] in
theorem ivk73Concl_to_subgroup [Finite G] (hLN : L ≤ N) (hKL : K ≤ L) (hQN : Q ≤ N)
    (h : Ivk73Concl ↥N (L.subgroupOf N) (K.subgroupOf N) (Q.subgroupOf N)) :
    IsElementaryAbelian 2 ↥Q ∧ Nat.card ↥Q = 4 ∧
      ((Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 5)) ∧
          NativeSporadic.IsSporadic ↥L .M12 ∧ Nat.card ↥N = 2 * Nat.card ↥L) ∨
        (Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 5)) ∧
          NativeSporadic.IsSporadic ↥L .J2 ∧ (N = L ∨ Nat.card ↥N = 2 * Nat.card ↥L)) ∨
        (N = L ∧ ∃ n ∈ ({5, 6, 7} : Finset ℕ),
          Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin n)) ∧
          Nonempty (↥L ≃* alternatingGroup (Fin (n + 4)))) ∨
        (IsL34Quotient (↥K ⧸ pPrimeCore 2 ↥K) ∧ center (↥K ⧸ pPrimeCore 2 ↥K) = ⊥ ∧
          NativeSporadic.IsSporadic ↥L .Suz) ∨
        (IsL34Quotient (↥K ⧸ pPrimeCore 2 ↥K) ∧
          IsElementaryAbelian 2 ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) ∧
          Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) = 4 ∧ NativeSporadic.IsSporadic ↥L .He)) := by
  have hKN : K ≤ N := hKL.trans hLN
  let ψ : ↥(K.subgroupOf N) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKN
  let e2 : (↥(K.subgroupOf N) ⧸ pPrimeCore 2 ↥(K.subgroupOf N)) ≃* (↥K ⧸ pPrimeCore 2 ↥K) :=
    QuotientGroup.congr _ _ ψ (pPrimeCore_map_iso 2 ψ)
  let eL : ↥(L.subgroupOf N) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLN
  let eQ : ↥(Q.subgroupOf N) ≃* ↥Q := Subgroup.subgroupOfEquivOfLe hQN
  obtain ⟨hel, hcard, hrows⟩ := h
  have hcardL : Nat.card ↥(L.subgroupOf N) = Nat.card ↥L := Nat.card_congr eL.toEquiv
  have hNL : L.subgroupOf N = ⊤ → N = L := fun htop =>
    le_antisymm (Subgroup.subgroupOf_eq_top.1 htop) hLN
  refine ⟨isElementaryAbelian_two_of_mulEquiv eQ hel, (Nat.card_congr eQ.toEquiv).symm.trans hcard, ?_⟩
  rcases hrows with ⟨⟨e5⟩, hM, hc⟩ | ⟨⟨e5⟩, hJ, hc⟩ | ⟨htop, n, hn, ⟨eA⟩, ⟨eAL⟩⟩
  · exact Or.inl ⟨⟨e2.symm.trans e5⟩, CFSG.GH74.isSporadic_of_mulEquiv eL hM, by rw [← hcardL]; exact hc⟩
  · refine Or.inr (Or.inl ⟨⟨e2.symm.trans e5⟩, CFSG.GH74.isSporadic_of_mulEquiv eL hJ, ?_⟩)
    rcases hc with hc | hc
    · exact Or.inl (hNL hc)
    · exact Or.inr (by rw [← hcardL]; exact hc)
  · exact Or.inr (Or.inr (Or.inl ⟨hNL htop, n, hn, ⟨e2.symm.trans eA⟩, ⟨eL.symm.trans eAL⟩⟩))

theorem ivk_7_3_g4_of_core
    (h : ∀ (N : Type) [Group N] [Finite N] (L K Q : Subgroup N), Ivk73Cfg N L K Q →
      Ivk73Concl N L K Q) : IVK_7_3_g4 := by
  intro G _ _ N L K Q hgen hGH hN hsoc hKL hKq hU2 hQ hrank hterm
  have hcfg := ivk73Cfg_of_subgroup hgen hGH hN hsoc hKL hKq hU2 hQ hrank hterm
  exact ivk73Concl_to_subgroup hsoc.1 hKL (hQ.le.trans inf_le_right)
    (h ↥N (L.subgroupOf N) (K.subgroupOf N) (Q.subgroupOf N) hcfg)

end Transfer

end CFSG.GH74.GLS.IVK
