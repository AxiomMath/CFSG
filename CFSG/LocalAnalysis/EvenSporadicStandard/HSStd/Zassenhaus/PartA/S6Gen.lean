module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
import CFSG.GroupTheory.PCore.OpenTransport

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

section PCore

variable {G : Type*} [Group G]

theorem s6_pCoreOf_eq (P : Subgroup G) :
    Open.pCoreOf 2 P = (CFSG.pCore 2 ↥P).map P.subtype := CFSG.openPCoreOf_eq_map_pCore 2 P

theorem s6_pCoreOf_le (P : Subgroup G) : Open.pCoreOf 2 P ≤ P := by
  rw [s6_pCoreOf_eq]
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem s6_pCoreOf_conj {P : Subgroup G} {g f : G} (hg : g ∈ P) (hf : f ∈ Open.pCoreOf 2 P) :
    g * f * g⁻¹ ∈ Open.pCoreOf 2 P := by
  rw [s6_pCoreOf_eq] at hf ⊢
  obtain ⟨f', hf', rfl⟩ := hf
  have : (CFSG.pCore 2 ↥P).Normal := CFSG.pCore_normal
  exact ⟨⟨g, hg⟩ * f' * ⟨g, hg⟩⁻¹, this.conj_mem _ hf' _, rfl⟩

theorem s6_pCoreOf_two {P : Subgroup G} {f : G} (hf : f ∈ Open.pCoreOf 2 P) :
    ∃ k : ℕ, f ^ (2 ^ k) = 1 := by
  rw [s6_pCoreOf_eq] at hf
  obtain ⟨f', hf', rfl⟩ := hf
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥P)) ⟨f', hf'⟩
  refine ⟨k, ?_⟩
  have := congrArg (fun x : CFSG.pCore 2 ↥P => ((x : ↥P) : G)) hk
  simpa using this

theorem s6_le_pCoreOf {P N : Subgroup G} (hNP : N ≤ P) (hN : ∀ g ∈ P, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (h2 : ∀ n ∈ N, ∃ k : ℕ, n ^ (2 ^ k) = 1) : N ≤ Open.pCoreOf 2 P := by
  rw [s6_pCoreOf_eq]
  have hnorm : (N.subgroupOf P).Normal :=
    ⟨fun n hn g => show ((g * n * g⁻¹ : P) : G) ∈ N from hN g g.2 n hn⟩
  have hp : IsPGroup 2 (N.subgroupOf P) := fun x => by
    obtain ⟨k, hk⟩ := h2 x.1.1 x.2
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using hk))⟩
  have hle : N.subgroupOf P ≤ CFSG.pCore 2 ↥P := le_sSup ⟨hnorm, hp⟩
  intro x hx
  exact ⟨⟨x, hNP hx⟩, hle (show (⟨x, hNP hx⟩ : P) ∈ N.subgroupOf P from hx), rfl⟩

end PCore

section Action

theorem s6_card_modEq {G : Type*} [Group G] (X : Subgroup G) [Finite X] (w : G) (hw3 : w ^ 3 = 1)
    (hn : ∀ x ∈ X, w * x * w⁻¹ ∈ X) :
    Nat.card X ≡ Nat.card (X ⊓ centralizer ({w} : Set G) : Subgroup G) [MOD 3] := by
  have hwN : w ∈ normalizer (X : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hn x hx, fun hx => ?_⟩
    have h2 := hn _ (hn _ hx)
    have hw3' : w * w * w = 1 := by simpa [pow_succ] using hw3
    have : w * (w * (w * x * w⁻¹) * w⁻¹) * w⁻¹ = x := by
      calc w * (w * (w * x * w⁻¹) * w⁻¹) * w⁻¹ = (w * w * w) * x * (w * w * w)⁻¹ := by group
        _ = x := by rw [hw3']; group
    rwa [this] at h2
  have hBN : zpowers w ≤ normalizer (X : Set G) := zpowers_le.2 hwN
  have hcl : ∀ b ∈ zpowers w, ∀ x ∈ X, b * x * b⁻¹ ∈ X := fun b hb x hx =>
    (mem_normalizer_iff.1 (hBN hb) x).1 hx
  let : MulAction (zpowers w) X :=
    { smul := fun b x => ⟨b * x * b⁻¹, hcl b b.2 x x.2⟩
      one_smul := fun x => Subtype.ext (show ((1 : zpowers w) : G) * (x : G) *
        ((1 : zpowers w) : G)⁻¹ = x by simp)
      mul_smul := fun a b x => Subtype.ext (show ((a * b : zpowers w) : G) * (x : G) *
        ((a * b : zpowers w) : G)⁻¹ = (a : G) * ((b : G) * (x : G) * (b : G)⁻¹) * (a : G)⁻¹ by
          simp [mul_assoc]) }
  have hp : IsPGroup 3 (zpowers w) := by
    intro b
    obtain ⟨m, hm⟩ := mem_zpowers_iff.1 b.2
    refine ⟨1, Subtype.ext ?_⟩
    show (b : G) ^ (3 ^ 1) = 1
    rw [← hm, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw3, one_zpow]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := hp.card_modEq_card_fixedPoints (α := X)
  have heq : Nat.card (MulAction.fixedPoints (zpowers w) X) =
      Nat.card (X ⊓ centralizer ({w} : Set G) : Subgroup G) := by
    apply Nat.card_congr
    refine
      { toFun := fun x => ⟨(x.1 : X).1, (x.1 : X).2, ?_⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    · show (x.1 : X).1 ∈ centralizer ({w} : Set G)
      rw [mem_centralizer_singleton_iff]
      have h := x.2 ⟨w, mem_zpowers w⟩
      have h' := congrArg Subtype.val h
      change w * (x.1 : G) * w⁻¹ = x.1 at h'
      rw [mul_inv_eq_iff_eq_mul] at h'
      exact h'.symm
    · intro b
      apply Subtype.ext
      obtain ⟨m, hm⟩ := mem_zpowers_iff.1 b.2
      have hc : Commute (w ^ m) x.1 := by
        have := (mem_centralizer_singleton_iff.1 x.2.2)
        exact (Commute.zpow_left (show Commute w x.1 from this.symm) m)
      show (b : G) * x.1 * (b : G)⁻¹ = x.1
      rw [← hm]
      rw [hc.eq, mul_inv_cancel_right]
  rw [heq] at hmod
  exact hmod

end Action

section Trivial

variable {G : Type*} [Group G] [Finite G]

theorem s6_isPGroup_two {X : Subgroup G} (h2 : ∀ x ∈ X, ∃ k : ℕ, x ^ (2 ^ k) = 1) :
    IsPGroup 2 X := fun x => by
  obtain ⟨k, hk⟩ := h2 x.1 x.2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem s6_card_two_pow {X : Subgroup G} (h2 : ∀ x ∈ X, ∃ k : ℕ, x ^ (2 ^ k) = 1) :
    ∃ n : ℕ, Nat.card X = 2 ^ n := (s6_isPGroup_two h2).exists_card_eq

theorem s6_not_three_dvd {X : Subgroup G} (h2 : ∀ x ∈ X, ∃ k : ℕ, x ^ (2 ^ k) = 1) :
    ¬ 3 ∣ Nat.card X := by
  obtain ⟨n, hn⟩ := s6_card_two_pow h2
  rw [hn]
  intro h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

theorem s6_centralizes_of_gen {F A : Subgroup G} (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hAc : Nat.card A = 3 ^ 2) (hF3 : ¬ 3 ∣ Nat.card F) (hAn : A ≤ normalizer (F : Set G))
    (hfix : ∀ a ∈ A, a ≠ 1 → F ⊓ centralizer ({a} : Set G) ≤ centralizer (A : Set G)) :
    F ≤ centralizer (A : Set G) := by
  have h := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 3
    Nat.prime_three A F (fun m => Subtype.ext (by simpa using hA3 m m.2)) hAc hF3 hAn
  calc F = _ := h
    _ ≤ _ := iSup_le fun m => iSup_le fun hm =>
      hfix m m.2 (fun h' => hm (Subtype.ext h'))

theorem s6_exists_gen {A : Subgroup G} (hAc : Nat.card A = 3 ^ 2) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) : ∃ w ∈ A, zpowers a ⊔ zpowers w = A := by
  have hord : orderOf a = 3 := by
    have h1 : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one (hA3 a ha)
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) ha1
    · exact h
  have hza : Nat.card (zpowers a) = 3 := by rw [Nat.card_zpowers, hord]
  have hlt : ¬ A ≤ zpowers a := by
    intro hle
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨w, hwA, hwn⟩ := Set.not_subset.1 hlt
  refine ⟨w, hwA, ?_⟩
  set B := zpowers a ⊔ zpowers w with hB
  have hBA : B ≤ A := sup_le (zpowers_le.2 ha) (zpowers_le.2 hwA)
  have hdvd : Nat.card B ∣ 3 ^ 2 := hAc ▸ Subgroup.card_dvd_of_le hBA
  have h3 : 3 ∣ Nat.card B := hza ▸ Subgroup.card_dvd_of_le (le_sup_left : zpowers a ≤ B)
  have hne : Nat.card B ≠ 3 := by
    intro h
    have hle : zpowers a ≤ B := le_sup_left
    have heq : zpowers a = B := Subgroup.eq_of_le_of_card_ge hle (by omega)
    apply hwn
    rw [heq]
    exact le_sup_right (a := zpowers a) (b := zpowers w) (mem_zpowers w)
  have hcard : Nat.card B = 9 := by
    have := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    obtain ⟨k, hk, hk'⟩ := this
    interval_cases k
    · omega
    · omega
    · simpa using hk'
  exact Subgroup.eq_of_le_of_card_ge hBA (by omega)

theorem s6_fixed_eq {F A : Subgroup G} (hF2 : ∀ f ∈ F, ∃ k : ℕ, f ^ (2 ^ k) = 1)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hAc : Nat.card A = 3 ^ 2) (hAn : A ≤ normalizer (F : Set G)) {u : G} (huF : u ∈ F)
    (hu1 : u ≠ 1) (huA : u ∈ centralizer (A : Set G))
    (hc : ∀ a ∈ A, a ≠ 1 → Nat.card ↥(F ⊓ centralizer ({a} : Set G)) ≤ 4)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    F ⊓ centralizer ({a} : Set G) ≤ centralizer (A : Set G) := by
  obtain ⟨w, hwA, hgen⟩ := s6_exists_gen hAc hA3 ha ha1
  set X := F ⊓ centralizer ({a} : Set G) with hX
  set X0 := F ⊓ centralizer (A : Set G) with hX0
  have hX2 : ∀ x ∈ X, ∃ k : ℕ, x ^ (2 ^ k) = 1 := fun x hx => hF2 x hx.1
  have hX02 : ∀ x ∈ X0, ∃ k : ℕ, x ^ (2 ^ k) = 1 := fun x hx => hF2 x hx.1
  have hX0X : X0 ≤ X := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    show x ∈ centralizer ({a} : Set G)
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 hx.2 a ha).symm
  have hwa : w * a = a * w := hAab w hwA a ha
  have hn : ∀ x ∈ X, w * x * w⁻¹ ∈ X := by
    intro x hx
    refine ⟨(mem_normalizer_iff.1 (hAn hwA) x).1 hx.1, ?_⟩
    show w * x * w⁻¹ ∈ centralizer ({a} : Set G)
    rw [mem_centralizer_singleton_iff]
    have hxa : x * a = a * x := mem_centralizer_singleton_iff.1 hx.2
    have hwi : w⁻¹ * a = a * w⁻¹ := (Commute.inv_left (show Commute w a from hwa)).eq
    calc w * x * w⁻¹ * a = w * x * (w⁻¹ * a) := by rw [mul_assoc]
      _ = w * x * (a * w⁻¹) := by rw [hwi]
      _ = w * (x * a) * w⁻¹ := by group
      _ = w * (a * x) * w⁻¹ := by rw [hxa]
      _ = (w * a) * x * w⁻¹ := by group
      _ = (a * w) * x * w⁻¹ := by rw [hwa]
      _ = a * (w * x * w⁻¹) := by group
  have hmod := s6_card_modEq X w (hA3 w hwA) hn
  have heq : X ⊓ centralizer ({w} : Set G) = X0 := by
    apply le_antisymm
    · intro x hx
      refine ⟨hx.1.1, ?_⟩
      have hxa : x * a = a * x := mem_centralizer_singleton_iff.1 hx.1.2
      have hxw : x * w = w * x := mem_centralizer_singleton_iff.1 hx.2
      have hle : A ≤ centralizer ({x} : Set G) := by
        rw [← hgen]
        refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
        · exact mem_centralizer_singleton_iff.2 hxa.symm
        · exact mem_centralizer_singleton_iff.2 hxw.symm
      show x ∈ centralizer (A : Set G)
      rw [mem_centralizer_iff]
      intro b hb
      exact mem_centralizer_singleton_iff.1 (hle hb)
    · intro x hx
      refine ⟨hX0X hx, ?_⟩
      show x ∈ centralizer ({w} : Set G)
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.1 hx.2 w hwA).symm
  rw [heq] at hmod
  obtain ⟨m, hm⟩ := s6_card_two_pow hX2
  obtain ⟨m0, hm0⟩ := s6_card_two_pow hX02
  have hX0ne : X0 ≠ ⊥ := by
    intro h
    have : u ∈ X0 := ⟨huF, huA⟩
    rw [h] at this
    exact hu1 (by simpa using this)
  have hlt0 : 1 < Nat.card X0 := (Subgroup.one_lt_card_iff_ne_bot X0).2 hX0ne
  have hle := Subgroup.card_le_of_le hX0X
  have h4 := hc a ha ha1
  rw [hm0] at hmod hle hlt0
  rw [hm] at hmod hle h4
  have hm4 : m ≤ 2 := by
    by_contra hcon
    have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hm0m : m0 ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
  have hm01 : 1 ≤ m0 := by
    by_contra hcon
    have : m0 = 0 := by omega
    subst this
    simp at hlt0
  have hmm : m = m0 := by
    interval_cases m <;> interval_cases m0 <;> first | rfl | (exfalso; simp [Nat.ModEq] at hmod)
  subst hmm
  have hcard : Nat.card X ≤ Nat.card X0 := by rw [hm, hm0]
  have := Subgroup.eq_of_le_of_card_ge hX0X hcard
  rw [← this]
  exact inf_le_right

theorem s6_trivial_action {F A : Subgroup G} (hF2 : ∀ f ∈ F, ∃ k : ℕ, f ^ (2 ^ k) = 1)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hAc : Nat.card A = 3 ^ 2) (hAn : A ≤ normalizer (F : Set G)) {u : G} (huF : u ∈ F)
    (hu1 : u ≠ 1) (huA : u ∈ centralizer (A : Set G))
    (hc : ∀ a ∈ A, a ≠ 1 → Nat.card ↥(F ⊓ centralizer ({a} : Set G)) ≤ 4) :
    F ≤ centralizer (A : Set G) :=
  s6_centralizes_of_gen hA3 hAc (s6_not_three_dvd hF2) hAn fun _ ha ha1 =>
    s6_fixed_eq hF2 hAab hA3 hAc hAn huF hu1 huA hc ha ha1


end Trivial


end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
