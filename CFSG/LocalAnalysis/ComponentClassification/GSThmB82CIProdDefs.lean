module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7NPLift

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped MatrixGroups

@[expose] def CFL4U4Prod : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f → ¬ (p = 3 ∧ f = 1) →
    (Blueprint.LieModel Y .PSL 4 p f ∧ p ^ f % 4 = 3 ∨
      Blueprint.LieModel Y .PSU 4 p f ∧ p ^ f % 4 = 1) →
    ∀ t w : Y, orderOf t = 2 → orderOf w = 2 → w ≠ t →
    ∀ M : Subgroup Y, M ≤ centralizer ({t} : Set Y) →
      IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set Y))) →
      Blueprint.LieModel (↥M ⧸ pPrimeCore 2 ↥M) .PSL 2 p (2 * f) → w ∈ M →
      ∃ N : Subgroup Y, N ≤ centralizer ({t * w} : Set Y) ∧
        IsPComponent 2 (N.subgroupOf (centralizer ({t * w} : Set Y))) ∧ t * w ∈ N ∧
        ∃ p' n : ℕ, ∃ _ : Fact p'.Prime, p' ≠ 2 ∧ 0 < n ∧
          Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, GaloisField p' n))

@[expose] def CFL4U4ProdCard : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f → ¬ (p = 3 ∧ f = 1) →
    (Blueprint.LieModel Y .PSL 4 p f ∧ p ^ f % 4 = 3 ∨
      Blueprint.LieModel Y .PSU 4 p f ∧ p ^ f % 4 = 1) →
    ∀ t w : Y, orderOf t = 2 → orderOf w = 2 → w ≠ t →
    ∀ M : Subgroup Y, M ≤ centralizer ({t} : Set Y) →
      IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set Y))) →
      Blueprint.LieModel (↥M ⧸ pPrimeCore 2 ↥M) .PSL 2 p (2 * f) → w ∈ M →
      ∃ N : Subgroup Y, N ≤ centralizer ({t * w} : Set Y) ∧
        IsPComponent 2 (N.subgroupOf (centralizer ({t * w} : Set Y))) ∧ t * w ∈ N ∧
        ∃ p' n : ℕ, ∃ _ : Fact p'.Prime, p' ≠ 2 ∧ 0 < n ∧
          Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, GaloisField p' n)) ∧ p' ^ n = p ^ f

theorem cfL4U4Prod_of_card (h : CFL4U4ProdCard) : CFL4U4Prod := by
  intro Y _ _ p f hp hp2 hf hq3 hY t w ht hw hwt M hMt hM hMLie hwM
  obtain ⟨N, hNt, hN, htwN, p', n, hp', hp'2, hn, he, -⟩ :=
    h Y p f hp hp2 hf hq3 hY t w ht hw hwt M hMt hM hMLie hwM
  exact ⟨N, hNt, hN, htwN, p', n, hp', hp'2, hn, he⟩

namespace Seven

variable {X : Type} [Group X] [Finite X]

theorem exists_sl2_of_cfL4U4_of_pred {p f : ℕ} (P : ℕ → ℕ → Prop)
    (hCF : ∀ (Y : Type) [Group Y] [Finite Y],
      (Blueprint.LieModel Y .PSL 4 p f ∧ p ^ f % 4 = 3 ∨
        Blueprint.LieModel Y .PSU 4 p f ∧ p ^ f % 4 = 1) →
      ∀ t w : Y, orderOf t = 2 → orderOf w = 2 → w ≠ t →
      ∀ M : Subgroup Y, M ≤ centralizer ({t} : Set Y) →
        IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set Y))) →
        Blueprint.LieModel (↥M ⧸ pPrimeCore 2 ↥M) .PSL 2 p (2 * f) → w ∈ M →
        ∃ N : Subgroup Y, N ≤ centralizer ({t * w} : Set Y) ∧
          IsPComponent 2 (N.subgroupOf (centralizer ({t * w} : Set Y))) ∧ t * w ∈ N ∧
          ∃ p' n : ℕ, ∃ _ : Fact p'.Prime, p' ≠ 2 ∧ 0 < n ∧
            Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, GaloisField p' n)) ∧ P p' n)
    {L J₀ Y : Subgroup X}
    (hLie : Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSL 4 p f ∧ p ^ f % 4 = 3 ∨
      Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSU 4 p f ∧ p ^ f % 4 = 1)
    {t w : X} (htL : t ∈ L) (ht : t * t = 1) (ht1 : t ≠ 1) (hw : w * w = 1) (hw1 : w ≠ 1)
    (htw : t * w = w * t) (hwt : w ≠ t) (hJ0L : J₀ ≤ L) (hJ0t : J₀ ≤ centralizer ({t} : Set X))
    (hYt : L ⊓ centralizer ({t} : Set X) ≤ Y) (hJ0pc : IsPComponent 2 (J₀.subgroupOf Y))
    (hJ0Lie : Blueprint.LieModel (↥J₀ ⧸ pPrimeCore 2 ↥J₀) .PSL 2 p (2 * f)) (hwJ0 : w ∈ J₀) :
    ∃ N : Subgroup X, N ≤ L ⊓ centralizer ({t * w} : Set X) ∧
      IsPComponent 2 (N.subgroupOf (L ⊓ centralizer ({t * w} : Set X))) ∧ t * w ∈ N ∧
      ∃ p' n : ℕ, ∃ _ : Fact p'.Prime, p' ≠ 2 ∧ 0 < n ∧
        Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, GaloisField p' n)) ∧ P p' n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hπ
  set t' : ↥L := ⟨t, htL⟩ with ht'
  set w' : ↥L := ⟨w, hJ0L hwJ0⟩ with hw'
  have ht'2 : t' * t' = 1 := Subtype.ext ht
  have hw'2 : w' * w' = 1 := Subtype.ext hw
  have ht'1 : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have hw'1 : w' ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
  have htw' : t' * w' = w' * t' := Subtype.ext htw
  have hJ0Lt : J₀ ≤ L ⊓ centralizer ({t} : Set X) := le_inf hJ0L hJ0t
  have hpc1 : IsPComponent 2 (J₀.subgroupOf (L ⊓ centralizer ({t} : Set X))) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_le hJ0Lt hYt hJ0pc
  have hpc2 : IsPComponent 2 ((J₀.subgroupOf L).subgroupOf (centralizer ({t'} : Set ↥L))) := by
    rw [← inf_centralizer_subgroupOf htL]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two).mpr hpc1
  have hMt : J₀.subgroupOf L ≤ centralizer ({t'} : Set ↥L) := by
    rw [← inf_centralizer_subgroupOf htL]
    intro v hv
    exact mem_subgroupOf.mpr (hJ0Lt (mem_subgroupOf.mp hv))
  obtain ⟨hMbt, hMbpc⟩ := isPComponent_centralizer_map ht'2 hMt hpc2
  have hMbLie : Blueprint.LieModel (↥((J₀.subgroupOf L).map π) ⧸
      pPrimeCore 2 ↥((J₀.subgroupOf L).map π)) .PSL 2 p (2 * f) := by
    obtain ⟨e₁⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv π OddQuot.not_two_dvd_card_ker
      (J₀.subgroupOf L)
    let e₂ := UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe hJ0L)
    exact LieType.CurtisTits.lieModel_of_mulEquiv (e₁.symm.trans e₂).symm hJ0Lie
  have hne : π w' ≠ π t' := by
    intro h
    have hinj := OddQuot.injOn_of_isPGroup (H := ↥L) (isPGroup_closure_pair hw'2 ht'2 htw'.symm)
    have := hinj (subset_closure (by simp)) (subset_closure (by simp)) h
    exact hwt (congrArg Subtype.val this)
  obtain ⟨Nb, hNbt, hNbpc, htwNb, p', n, hp', hp'2, hn, ⟨eNb⟩, hP⟩ := hCF _ hLie
    _ _ (orderOf_mk_eq_two ht'2 ht'1) (orderOf_mk_eq_two hw'2 hw'1) hne _ hMbt hMbpc hMbLie
    (mem_map_of_mem _ (mem_subgroupOf.mpr hwJ0))
  have htw'2 : t' * w' * (t' * w') = 1 := by
    rw [show t' * w' * (t' * w') = t' * (w' * t') * w' by group, ← htw',
      show t' * (t' * w') * w' = (t' * t') * (w' * w') by group, ht'2, hw'2, one_mul]
  have hπtw : π t' * π w' = π (t' * w') := (map_mul π t' w').symm
  rw [hπtw] at hNbt hNbpc htwNb
  have hcen := OddQuot.centralizer_singleton_map_eq (H := ↥L) htw'2
  rw [hcen] at hNbt hNbpc
  obtain ⟨N₁, hN₁X, hN₁pc, hN₁map, ⟨eN₁⟩⟩ := exists_isPComponent_map_eq π
    OddQuot.not_two_dvd_card_ker hNbt hNbpc
  have htwN₁ : t' * w' ∈ N₁ := mem_of_mk_mem hN₁X htw'2 (by rw [hN₁map]; exact htwNb)
  set N := N₁.map L.subtype with hNdef
  have htwL : t * w ∈ L := mul_mem htL (hJ0L hwJ0)
  have hsub : N.subgroupOf L = N₁ := comap_map_eq_self_of_injective L.subtype_injective N₁
  have hcenL : (L ⊓ centralizer ({t * w} : Set X)).subgroupOf L =
      centralizer ({t' * w'} : Set ↥L) := inf_centralizer_subgroupOf htwL
  have hNX : N ≤ L ⊓ centralizer ({t * w} : Set X) := by
    rintro _ ⟨v, hv, rfl⟩
    have h1 : v ∈ (L ⊓ centralizer ({t * w} : Set X)).subgroupOf L := by
      rw [hcenL]
      exact hN₁X hv
    exact mem_subgroupOf.mp h1
  refine ⟨N, hNX, ?_, ⟨t' * w', htwN₁, rfl⟩, p', n, hp', hp'2, hn, ?_⟩
  · have h1 : IsPComponent 2 ((N.subgroupOf L).subgroupOf
        ((L ⊓ centralizer ({t * w} : Set X)).subgroupOf L)) := by
      rw [hsub, hcenL]
      exact hN₁pc
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two).mp h1
  · let e₀ : ↥N ≃* ↥N₁ := (N₁.equivMapOfInjective L.subtype L.subtype_injective).symm
    exact ⟨⟨(UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e₀).trans
      (eN₁.trans eNb)⟩, hP⟩

theorem exists_sl2_of_cfL4U4 (hCF : CFL4U4Prod) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hq3 : ¬ (p = 3 ∧ f = 1)) {L J₀ Y : Subgroup X}
    (hLie : Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSL 4 p f ∧ p ^ f % 4 = 3 ∨
      Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSU 4 p f ∧ p ^ f % 4 = 1)
    {t w : X} (htL : t ∈ L) (ht : t * t = 1) (ht1 : t ≠ 1) (hw : w * w = 1) (hw1 : w ≠ 1)
    (htw : t * w = w * t) (hwt : w ≠ t) (hJ0L : J₀ ≤ L) (hJ0t : J₀ ≤ centralizer ({t} : Set X))
    (hYt : L ⊓ centralizer ({t} : Set X) ≤ Y) (hJ0pc : IsPComponent 2 (J₀.subgroupOf Y))
    (hJ0Lie : Blueprint.LieModel (↥J₀ ⧸ pPrimeCore 2 ↥J₀) .PSL 2 p (2 * f)) (hwJ0 : w ∈ J₀) :
    ∃ N : Subgroup X, N ≤ L ⊓ centralizer ({t * w} : Set X) ∧
      IsPComponent 2 (N.subgroupOf (L ⊓ centralizer ({t * w} : Set X))) ∧ t * w ∈ N ∧
      ∃ p' n : ℕ, ∃ _ : Fact p'.Prime, p' ≠ 2 ∧ 0 < n ∧
        Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, GaloisField p' n)) := by
  obtain ⟨N, hNX, hN, htwN, p', n, hp', hp'2, hn, he, -⟩ :=
    exists_sl2_of_cfL4U4_of_pred (fun _ _ => True) (by
      intro Y' _ _ hY t' w' ht' hw' hwt' M hMt hM hMLie hwM
      obtain ⟨N, hNt, hN, htwN, p', n, hp', hp'2, hn, he⟩ :=
        hCF Y' p f hp hp2 hf hq3 hY t' w' ht' hw' hwt' M hMt hM hMLie hwM
      exact ⟨N, hNt, hN, htwN, p', n, hp', hp'2, hn, he, trivial⟩)
      hLie htL ht ht1 hw hw1 htw hwt hJ0L hJ0t hYt hJ0pc hJ0Lie hwJ0
  exact ⟨N, hNX, hN, htwN, p', n, hp', hp'2, hn, he⟩

theorem exists_sl2_of_cfL4U4Card (hCF : CFL4U4ProdCard) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hq3 : ¬ (p = 3 ∧ f = 1)) {L J₀ Y : Subgroup X}
    (hLie : Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSL 4 p f ∧ p ^ f % 4 = 3 ∨
      Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSU 4 p f ∧ p ^ f % 4 = 1)
    {t w : X} (htL : t ∈ L) (ht : t * t = 1) (ht1 : t ≠ 1) (hw : w * w = 1) (hw1 : w ≠ 1)
    (htw : t * w = w * t) (hwt : w ≠ t) (hJ0L : J₀ ≤ L) (hJ0t : J₀ ≤ centralizer ({t} : Set X))
    (hYt : L ⊓ centralizer ({t} : Set X) ≤ Y) (hJ0pc : IsPComponent 2 (J₀.subgroupOf Y))
    (hJ0Lie : Blueprint.LieModel (↥J₀ ⧸ pPrimeCore 2 ↥J₀) .PSL 2 p (2 * f)) (hwJ0 : w ∈ J₀) :
    ∃ N : Subgroup X, N ≤ L ⊓ centralizer ({t * w} : Set X) ∧
      IsPComponent 2 (N.subgroupOf (L ⊓ centralizer ({t * w} : Set X))) ∧ t * w ∈ N ∧
      ∃ p' n : ℕ, ∃ _ : Fact p'.Prime, p' ≠ 2 ∧ 0 < n ∧
        Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, GaloisField p' n)) ∧ p' ^ n = p ^ f :=
  exists_sl2_of_cfL4U4_of_pred (fun p' n => p' ^ n = p ^ f)
    (fun Y _ _ => hCF Y p f hp hp2 hf hq3) hLie htL ht ht1 hw hw1 htw hwt hJ0L hJ0t hYt hJ0pc
    hJ0Lie hwJ0

end Seven

end CFSG.ComponentClassification.GSThmB
