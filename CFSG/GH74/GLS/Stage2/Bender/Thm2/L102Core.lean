module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L102Cover
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Der10C2

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L102

open Subgroup
open scoped commutatorElement

section NormAux

variable {G : Type*} [Group G]

theorem normalizer_inf_of {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA h, hB h]

theorem normalizer_sup_of {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem exists_mem_normalizer_not_mem [Finite G] {p : ℕ} (hpp : p.Prime) {R₁ R₂ : Subgroup G}
    (hp : IsPGroup p R₂) (h : R₁ ≤ R₂) (hne : R₁ ≠ R₂) :
    ∃ x ∈ R₂, x ∈ normalizer (R₁ : Set G) ∧ x ∉ R₁ := by
  have : Fact p.Prime := ⟨hpp⟩
  have : Group.IsNilpotent ↥R₂ := hp.isNilpotent
  have hlt : R₁.subgroupOf R₂ < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hne ?_
    have : R₂ ≤ R₁ := by
      intro x hx
      have : (⟨x, hx⟩ : ↥R₂) ∈ R₁.subgroupOf R₂ := htop ▸ Subgroup.mem_top _
      exact this
    exact le_antisymm h this
  have hlt' := Group.normalizerCondition_of_isNilpotent (R₁.subgroupOf R₂) hlt
  obtain ⟨x, hxN, hx⟩ := IsConcreteLE.exists_of_lt hlt'
  refine ⟨x, x.2, ?_, fun hx1 => hx hx1⟩
  rw [Subgroup.mem_normalizer_iff] at hxN ⊢
  intro g
  constructor
  · intro hg
    have := (hxN ⟨g, h hg⟩).mp hg
    exact this
  · intro hg
    have hgR₂ : g ∈ R₂ := by
      have h1 : (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * (x : G) ∈ R₂ :=
        R₂.mul_mem (R₂.mul_mem (R₂.inv_mem x.2) (h hg)) x.2
      simpa [mul_assoc] using h1
    exact (hxN ⟨g, hgR₂⟩).mpr hg

end NormAux


section Core

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_pPrimeCoreOf {X : Subgroup G} {g : G} (hg : g ∈ normalizer (X : Set G)) :
    g ∈ normalizer ((pPrimeCoreOf 2 X : Subgroup G) : Set G) := by
  have key : ∀ g : G, g ∈ normalizer (X : Set G) →
      ∀ h ∈ pPrimeCoreOf 2 X, g * h * g⁻¹ ∈ pPrimeCoreOf 2 X := by
    intro g hg h hh
    have hOX : (pPrimeCoreOf 2 X).map (MulAut.conj g).toMonoidHom ≤ X := by
      rintro _ ⟨o, ho, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg o).mp (TwoThin.pPrimeCoreOf_le X ho)
    have hnorm : ∀ x ∈ X, ∀ n ∈ (pPrimeCoreOf 2 X).map (MulAut.conj g).toMonoidHom,
        x * n * x⁻¹ ∈ (pPrimeCoreOf 2 X).map (MulAut.conj g).toMonoidHom := by
      intro x hx n hn
      obtain ⟨o, ho, rfl⟩ := hn
      have hy : g⁻¹ * x * g ∈ X := (Subgroup.mem_normalizer_iff''.mp hg x).mp hx
      refine ⟨(g⁻¹ * x * g) * o * (g⁻¹ * x * g)⁻¹, TwoThin.pPrimeCoreOf_normalized X hy ho, ?_⟩
      show g * ((g⁻¹ * x * g) * o * (g⁻¹ * x * g)⁻¹) * g⁻¹ = x * (g * o * g⁻¹) * x⁻¹
      group
    have hodd : Odd (Nat.card ↥((pPrimeCoreOf 2 X).map (MulAut.conj g).toMonoidHom)) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact TwoThin.card_pPrimeCoreOf_odd X
    have hle := le_pPrimeCoreOf_of_normal_odd hOX hnorm hodd
    exact hle ⟨h, hh, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact key g hg h
  · intro hh
    have := key g⁻¹ (inv_mem hg) _ hh
    simpa [mul_assoc] using this


theorem core {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H T U I K N R₁ R₂ : Subgroup G}
    (hT2 : IsPGroup 2 T) (hUT : U ≤ T)
    (hTH : T ≤ normalizer (H : Set G)) (hTI : T ≤ normalizer (I : Set G))
    (hTN : T ≤ normalizer (N : Set G)) (hTR₁ : T ≤ normalizer (R₁ : Set G))
    (hTR₂ : T ≤ normalizer (R₂ : Set G))
    (hIU : I ≤ centralizer (U : Set G)) (hIperf : ⁅I, I⁆ = I)
    (hCI : ∀ c ∈ centralizer (U : Set G), c ∈ normalizer (I : Set G))
    (hKI : K ≤ I) (hKn : I ≤ normalizer (K : Set G)) (hKodd : Odd (Nat.card K))
    (hKmax : ∀ L : Subgroup G, L ≤ I → I ≤ normalizer (L : Set G) → Odd (Nat.card L) → L ≤ K)
    (hNH : N ≤ H) (hHN : H ≤ normalizer (N : Set G)) (hNodd : Odd (Nat.card N))
    (hR₁R₂ : R₁ ≤ R₂) (hR₂H : R₂ ≤ H) (hR₂p : IsPGroup p R₂)
    (hR₁ne : R₁ ≠ ⊥)
    (hcov₁ : I ≤ (H ⊓ normalizer (R₁ : Set G) ⊓ I) ⊔ K)
    (hcov₂ : I ≤ (H ⊓ normalizer (R₂ : Set G) ⊓ I) ⊔ K)
    (hkey : ∀ P₁ P₂ : Subgroup G, P₁ ≤ H ⊓ I → P₂ ≤ H ⊓ I → ⁅P₁, P₁⁆ = P₁ → ⁅P₂, P₂⁆ = P₂ →
      I ≤ P₁ ⊔ K → I ≤ P₂ ⊔ K → P₁ ≤ P₂ ⊔ N)
    (hmax : ∀ V : Subgroup G, V ≠ ⊥ → IsPGroup p V → V ≤ H ⊓ normalizer (R₁ : Set G) →
      T ≤ normalizer (V : Set G) →
      I ≤ (H ⊓ normalizer (R₁ : Set G) ⊓ normalizer (V : Set G) ⊓ I) ⊔ K → R₁ ≤ V → V = R₁) :
    R₂ ≤ R₁ := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  have hne' : R₁ ≠ R₂ := fun h => hne (h ▸ le_rfl)
  obtain ⟨x, hxR₂, hxN, hxR₁⟩ := exists_mem_normalizer_not_mem hp hR₂p hR₁R₂ hne'
  have hB₁I : H ⊓ normalizer (R₁ : Set G) ⊓ I ≤ I := inf_le_right
  have hB₂I : H ⊓ normalizer (R₂ : Set G) ⊓ I ≤ I := inf_le_right
  have hI₁perf := dres_perfect (H ⊓ normalizer (R₁ : Set G) ⊓ I)
  have hI₂perf := dres_perfect (H ⊓ normalizer (R₂ : Set G) ⊓ I)
  have hI₁B := dres_le (H ⊓ normalizer (R₁ : Set G) ⊓ I)
  have hI₂B := dres_le (H ⊓ normalizer (R₂ : Set G) ⊓ I)
  have hcI₁ : I ≤ dres (H ⊓ normalizer (R₁ : Set G) ⊓ I) ⊔ K := cover_dres hIperf hKI hKn hB₁I hcov₁
  have hcI₂ : I ≤ dres (H ⊓ normalizer (R₂ : Set G) ⊓ I) ⊔ K := cover_dres hIperf hKI hKn hB₂I hcov₂
  have hTB₁ : T ≤ normalizer ((H ⊓ normalizer (R₁ : Set G) ⊓ I : Subgroup G) : Set G) := fun g hg =>
    normalizer_inf_of (normalizer_inf_of (hTH hg) (le_normalizer (hTR₁ hg))) (hTI hg)
  have hTI₁ : T ≤ normalizer ((dres (H ⊓ normalizer (R₁ : Set G) ⊓ I) : Subgroup G) : Set G) :=
    fun g hg => normalizer_le_normalizer_dres _ (hTB₁ hg)
  have hI₁HI : dres (H ⊓ normalizer (R₁ : Set G) ⊓ I) ≤ H ⊓ I :=
    hI₁B.trans (inf_le_inf_right _ inf_le_left)
  have hI₂HI : dres (H ⊓ normalizer (R₂ : Set G) ⊓ I) ≤ H ⊓ I :=
    hI₂B.trans (inf_le_inf_right _ inf_le_left)
  have hI₁I₂N := hkey _ _ hI₁HI hI₂HI hI₁perf hI₂perf hcI₁ hcI₂
  generalize dres (H ⊓ normalizer (R₁ : Set G) ⊓ I) = I₁ at *
  generalize dres (H ⊓ normalizer (R₂ : Set G) ⊓ I) = I₂ at *
  have hR₂N : R₂ ≤ normalizer (N : Set G) := hR₂H.trans hHN
  have hRodd : Odd (Nat.card R₂) := by
    obtain ⟨n, hn⟩ := hR₂p.exists_card_eq
    rw [hn]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hQodd : Odd (Nat.card ↥(R₂ ⊔ N)) := odd_card_sup_of_normalizes hRodd hNodd hR₂N
  have hQH : R₂ ⊔ N ≤ H := sup_le hR₂H hNH
  have hI₂Q : I₂ ≤ normalizer ((R₂ ⊔ N : Subgroup G) : Set G) := fun g hg =>
    normalizer_sup_of (hI₂B hg).1.2 (hHN (hI₂B hg).1.1)
  have hI₁Q : I₁ ≤ normalizer ((R₂ ⊔ N : Subgroup G) : Set G) :=
    hI₁I₂N.trans (sup_le hI₂Q (le_sup_right.trans le_normalizer))
  have hM₂odd : Odd (Nat.card ↥((R₂ ⊔ N) ⊓ normalizer (R₁ : Set G))) :=
    hQodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hI₁M₂ : I₁ ≤ normalizer ((((R₂ ⊔ N) ⊓ normalizer (R₁ : Set G) : Subgroup G)) : Set G) :=
    fun g hg => normalizer_inf_of (hI₁Q hg) (le_normalizer (hI₁B hg).1.2)
  have hTM₂ : T ≤ normalizer ((((R₂ ⊔ N) ⊓ normalizer (R₁ : Set G) : Subgroup G)) : Set G) :=
    fun g hg => normalizer_inf_of (normalizer_sup_of (hTR₂ hg) (hTN hg)) (le_normalizer (hTR₁ hg))
  have hXn : (R₂ ⊔ N) ⊓ normalizer (R₁ : Set G) ⊔ I₁ ≤
      normalizer ((((R₂ ⊔ N) ⊓ normalizer (R₁ : Set G) : Subgroup G)) : Set G) :=
    sup_le le_normalizer hI₁M₂
  have hTX : T ≤ normalizer ((((R₂ ⊔ N) ⊓ normalizer (R₁ : Set G) ⊔ I₁ : Subgroup G)) : Set G) :=
    fun g hg => normalizer_sup_of (hTM₂ hg) (hTI₁ hg)
  have hXH : (R₂ ⊔ N) ⊓ normalizer (R₁ : Set G) ⊔ I₁ ≤ H ⊓ normalizer (R₁ : Set G) :=
    sup_le (le_inf (inf_le_left.trans hQH) inf_le_right)
      (fun g hg => ⟨(hI₁B hg).1.1, (hI₁B hg).1.2⟩)
  generalize hMdef : (R₂ ⊔ N) ⊓ normalizer (R₁ : Set G) = M₂ at *
  generalize hXdef : M₂ ⊔ I₁ = X at *
  have hM₂X : M₂ ≤ X := hXdef ▸ le_sup_left
  have hI₁X : I₁ ≤ X := hXdef ▸ le_sup_right
  have hM₂O : M₂ ≤ pPrimeCoreOf 2 X := le_pPrimeCoreOf_of_normal_odd hM₂X
    (fun x hx n hn => (Subgroup.mem_normalizer_iff.mp (hXn hx) n).mp hn) hM₂odd
  have hOX : pPrimeCoreOf 2 X ≤ X := TwoThin.pPrimeCoreOf_le X
  have hOodd : Odd (Nat.card ↥(pPrimeCoreOf 2 X)) := TwoThin.card_pPrimeCoreOf_odd X
  have hXO : X ≤ normalizer ((pPrimeCoreOf 2 X : Subgroup G) : Set G) := fun g hg => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact TwoThin.pPrimeCoreOf_normalized X hg
    · intro hh
      have := TwoThin.pPrimeCoreOf_normalized X (inv_mem hg) hh
      simpa [mul_assoc] using this
  have hTO : T ≤ normalizer ((pPrimeCoreOf 2 X : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_pPrimeCoreOf (hTX hg)
  have hR₁R : R₁ ≤ R₂ ⊓ normalizer (R₁ : Set G) := le_inf hR₁R₂ le_normalizer
  have hRM₂ : R₂ ⊓ normalizer (R₁ : Set G) ≤ M₂ :=
    hMdef ▸ le_inf (inf_le_left.trans le_sup_left) inf_le_right
  have hTR : T ≤ normalizer ((R₂ ⊓ normalizer (R₁ : Set G) : Subgroup G) : Set G) :=
    fun g hg => normalizer_inf_of (hTR₂ hg) (le_normalizer (hTR₁ hg))
  obtain ⟨V, hVO, hVp, hRV, hTV, hVmax⟩ := exists_invariant_sylow_ge hp hOodd hT2 hTO
    (hRM₂.trans hM₂O) (hR₂p.to_le inf_le_left) hTR
  have hR₁V : R₁ ≤ V := hR₁R.trans hRV
  have hV0 : V ≠ ⊥ := fun h => hR₁ne (le_bot_iff.mp (h ▸ hR₁V))
  have hVHN : V ≤ H ⊓ normalizer (R₁ : Set G) := hVO.trans (hOX.trans (hXdef ▸ hXH))
  have hI₁U : I₁ ≤ centralizer (U : Set G) := (hI₁B.trans inf_le_right).trans hIU
  have hXdec : ∀ w ∈ X ⊓ centralizer (U : Set G),
      ∃ m ∈ pPrimeCoreOf 2 X ⊓ centralizer (U : Set G), ∃ i ∈ I₁, w = m * i := by
    rintro w ⟨hwX, hwU⟩
    have hw' : w⁻¹ ∈ M₂ ⊔ I₁ := hXdef ▸ inv_mem hwX
    obtain ⟨z, hz, hzm⟩ := exists_mem_inv_mul_mem (fun g hg => hI₁M₂ hg) hw'
    have hwz : w * z ∈ M₂ := by
      have : (z⁻¹ * w⁻¹)⁻¹ ∈ M₂ := inv_mem hzm
      simpa using this
    exact ⟨w * z, ⟨hM₂O hwz, mul_mem hwU (hI₁U hz)⟩, z⁻¹, inv_mem hz, by group⟩
  have hcovV : I ≤ (X ⊓ normalizer (V : Set G) ⊓ I) ⊔ K :=
    cover_normalizer hp (hT2.to_le hUT) (hUT.trans hTO) hOX hXO hOodd hVO hVp hVmax
      (hUT.trans hTV) hI₁X hI₁U hI₁perf hXdec
      (hI₁B.trans inf_le_right) hCI hKI hKn hKodd hKmax hcI₁
  have hVR : V = R₁ := hmax V hV0 hVp hVHN hTV
    (hcovV.trans (sup_le_sup_right (inf_le_inf_right _ (inf_le_inf_right _ (hXdef ▸ hXH))) _)) hR₁V
  exact hxR₁ (hVR ▸ hRV ⟨hxR₂, hxN⟩)

end Core
