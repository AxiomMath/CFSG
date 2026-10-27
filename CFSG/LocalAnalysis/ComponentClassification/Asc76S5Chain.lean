module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Core

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G]

@[expose] def ncIn (K₀ H : Subgroup G) : Subgroup G :=
  closure {x | ∃ h ∈ H, ∃ k ∈ K₀, x = h * k * h⁻¹}

@[expose] def ncChain (K₀ : Subgroup G) : ℕ → Subgroup G
  | 0 => ⊤
  | n + 1 => ncIn K₀ (ncChain K₀ n)

@[simp] theorem ncChain_zero (K₀ : Subgroup G) : ncChain K₀ 0 = ⊤ := rfl

theorem le_ncIn (K₀ H : Subgroup G) : K₀ ≤ ncIn K₀ H := fun k hk =>
  subset_closure ⟨1, one_mem H, k, hk, by group⟩

theorem ncIn_le {K₀ H : Subgroup G} (hK : K₀ ≤ H) : ncIn K₀ H ≤ H := by
  refine (closure_le _).mpr ?_
  rintro _ ⟨h, hh, k, hk, rfl⟩
  exact H.mul_mem (H.mul_mem hh (hK hk)) (H.inv_mem hh)

theorem map_conj_ncIn_le {K₀ H : Subgroup G} {w : G}
    (hH : ∀ h ∈ H, w * h * w⁻¹ ∈ H) (hK : ∀ k ∈ K₀, w * k * w⁻¹ ∈ K₀) :
    (ncIn K₀ H).map (MulAut.conj w).toMonoidHom ≤ ncIn K₀ H := by
  rw [ncIn, MonoidHom.map_closure, closure_le]
  rintro _ ⟨_, ⟨h, hh, k, hk, rfl⟩, rfl⟩
  refine subset_closure ⟨w * h * w⁻¹, hH h hh, w * k * w⁻¹, hK k hk, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem map_conj_ncIn_le_of_mem {K₀ H : Subgroup G} {w : G} (hw : w ∈ H) :
    (ncIn K₀ H).map (MulAut.conj w).toMonoidHom ≤ ncIn K₀ H := by
  rw [ncIn, MonoidHom.map_closure, closure_le]
  rintro _ ⟨_, ⟨h, hh, k, hk, rfl⟩, rfl⟩
  refine subset_closure ⟨w * h, H.mul_mem hw hh, k, hk, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem le_ncChain (K₀ : Subgroup G) : ∀ n, K₀ ≤ ncChain K₀ n
  | 0 => le_top
  | n + 1 => le_ncIn K₀ (ncChain K₀ n)

theorem ncChain_succ_le (K₀ : Subgroup G) (n : ℕ) : ncChain K₀ (n + 1) ≤ ncChain K₀ n :=
  ncIn_le (le_ncChain K₀ n)

variable [Finite G]

theorem le_normalizer_ncIn (K₀ H : Subgroup G) : H ≤ normalizer (ncIn K₀ H : Set G) :=
  fun _ hw => mem_normalizer_of_map_conj_le (map_conj_ncIn_le_of_mem hw)

theorem ncChain_le_normalizer_succ (K₀ : Subgroup G) (n : ℕ) :
    ncChain K₀ n ≤ normalizer (ncChain K₀ (n + 1) : Set G) :=
  le_normalizer_ncIn K₀ (ncChain K₀ n)

theorem normalizer_le_normalizer_ncChain (K₀ : Subgroup G) :
    ∀ n, normalizer (K₀ : Set G) ≤ normalizer (ncChain K₀ n : Set G)
  | 0 => fun _ _ => by rw [ncChain_zero]; exact mem_normalizer_iff.mpr fun _ => by simp
  | n + 1 => fun w hw => by
    have hH := normalizer_le_normalizer_ncChain K₀ n hw
    refine mem_normalizer_of_map_conj_le (map_conj_ncIn_le
      (fun h hh => (mem_normalizer_iff.mp hH h).mp hh)
      fun k hk => (mem_normalizer_iff.mp hw k).mp hk)

omit [Finite G] in
theorem le_oddCoreIn {N L : Subgroup G} (hNL : N ≤ L) (hLN : L ≤ normalizer (N : Set G))
    (hodd : Odd (Nat.card N)) : N ≤ oddCoreIn L := by
  have hn : (N.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer hNL).mpr hLN
  have hodd' : Odd (Nat.card (N.subgroupOf L)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hNL).toEquiv]
  have h := le_assemblyOddCore hn hodd'
  intro x hx
  exact ⟨⟨x, hNL hx⟩, h hx, rfl⟩

theorem eq_bot_of_odd_of_le_ncChain (K₀ : Subgroup G) (hO : standardComponentOddCore G = ⊥) :
    ∀ n (N : Subgroup G), N ≤ ncChain K₀ n → ncChain K₀ n ≤ normalizer (N : Set G) →
      Odd (Nat.card N) → N = ⊥
  | 0, N, _, hN, hodd => by
    have hn : N.Normal := ⟨fun x hx g => (mem_normalizer_iff.mp (hN (mem_top g)) x).mp hx⟩
    rw [eq_bot_iff, ← hO]
    exact le_sSup ⟨hn, hodd⟩
  | n + 1, N, hNL, hLN, hodd => by
    set L := ncChain K₀ (n + 1)
    have hNO : N ≤ oddCoreIn L := le_oddCoreIn hNL hLN hodd
    have hO' : oddCoreIn L = ⊥ :=
      eq_bot_of_odd_of_le_ncChain K₀ hO n (oddCoreIn L)
        ((oddCoreIn_le L).trans (ncChain_succ_le K₀ n))
        ((ncChain_le_normalizer_succ K₀ n).trans (normalizer_le_normalizer_oddCoreIn L))
        (odd_card_oddCoreIn L)
    exact le_bot_iff.mp (hO' ▸ hNO)

theorem exists_ncChain_succ_eq (K₀ : Subgroup G) : ∃ n, ncChain K₀ (n + 1) = ncChain K₀ n := by
  by_contra hcon
  push Not at hcon
  have key : ∀ n, Nat.card (ncChain K₀ n) + n ≤ Nat.card G := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hlt : ncChain K₀ (n + 1) < ncChain K₀ n :=
        lt_of_le_of_ne (ncChain_succ_le K₀ n) (hcon n)
      have := card_lt_of_lt hlt
      omega
  have h := key (Nat.card G)
  have hpos : 0 < Nat.card (ncChain K₀ (Nat.card G)) := Nat.card_pos
  omega

theorem false_of_ncChain_le_normalizer {A K₀ : Subgroup G} (hA : standardComponentIsStandard A)
    (hO : standardComponentOddCore G = ⊥) (hK₀K : K₀ ≤ centralizer (A : Set G))
    (hK₀ : Even (Nat.card K₀))
    (hNK : normalizer (centralizer (A : Set G) : Set G) ≤ normalizer (K₀ : Set G))
    {g : G} (hg : g ∉ normalizer (A : Set G)) :
    ∀ n, ¬ ncChain K₀ n ≤ normalizer (K₀ : Set G) := by
  have hK : TightlyEmbedded (centralizer (A : Set G)) := tightlyEmbedded_centralizer hA
  have hK₀N : normalizer (K₀ : Set G) ≤ normalizer (A : Set G) := by
    rw [← normalizer_centralizer_eq hA]
    exact normalizer_le_normalizer_of_tightlyEmbedded hK hK₀K hK₀
  have hAK₀ : A ≤ normalizer (K₀ : Set G) := by
    refine le_trans ?_ hNK
    rw [normalizer_centralizer_eq hA]
    exact le_normalizer
  intro n
  induction n with
  | zero => exact fun h => hg (hK₀N (h (mem_top g)))
  | succ n ih =>
    intro hle
    apply ih
    have h := normalizer_le_normalizer_of_normal hA hK₀K hK₀ hNK (le_ncChain K₀ (n + 1)) hle
      (hAK₀.trans (normalizer_le_normalizer_ncChain K₀ (n + 1)))
      (eq_bot_of_odd_of_le_ncChain K₀ hO (n + 1))
    exact (ncChain_le_normalizer_succ K₀ n).trans h

end CFSG.ComponentClassification.Asc76.Sec5
