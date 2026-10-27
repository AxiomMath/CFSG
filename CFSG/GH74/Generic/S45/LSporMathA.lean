module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM11
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24

public section

namespace CFSG.GH74.Generic.S45.LAlt

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.OuterAutomorphisms

theorem fixed_card_of_inner_top {G : Type*} [Group G] (hZ : Subgroup.center G = ⊥)
    (hin : inner G = ⊤) (α : MulAut G) (hα : α * α = 1) (hα1 : α ≠ 1) :
    ∃ x : G, orderOf x = 2 ∧
      Nat.card {y : G // α y = y} = Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  have hmem : α ∈ inner G := by
    rw [hin]
    exact Subgroup.mem_top α
  obtain ⟨x, hx⟩ := hmem
  have hxx : x * x = 1 := by
    have h1 : MulAut.conj (x * x) = 1 := by rw [map_mul, hx, hα]
    have hc : x * x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro z
      have := congrArg (fun a : MulAut G => a z) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc z * (x * x) = (x * x * z * (x * x)⁻¹) * (x * x) := by rw [this]
        _ = x * x * z := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hα1 (by rw [← hx, map_one])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨x, orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1, ?_⟩
  refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
  rw [← hx, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc y * x = (x * y * x⁻¹) * x := by rw [h]
      _ = x * y := by group
  · intro h
    calc x * y * x⁻¹ = (y * x) * x⁻¹ := by rw [h]
      _ = y := by group

theorem fixed_card_eq_centralizerIn {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
    (hZ : Subgroup.center H = ⊥) (hin : inner H = ⊤) (α : MulAut H) (hα : α * α = 1)
    (hα1 : α ≠ 1) :
    ∃ u ∈ H, orderOf u = 2 ∧ Nat.card {y : H // α y = y} = Nat.card (centralizerIn H u) := by
  obtain ⟨t, ht, hcard⟩ := fixed_card_of_inner_top hZ hin α hα hα1
  refine ⟨(t : Equiv.Perm (Fin n)), t.2, by rw [Subgroup.orderOf_coe]; exact ht, ?_⟩
  rw [hcard, ← map_centralizer_subtype H t, Subgroup.card_map_of_injective H.subtype_injective]

theorem fixed_card_of_classes {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {P : ℕ → Prop}
    (hZ : Subgroup.center H = ⊥) (hin : inner H = ⊤)
    (hcls : ∀ u ∈ H, orderOf u = 2 → P (Nat.card (centralizerIn H u))) (α : MulAut H)
    (hα : α * α = 1) (hα1 : α ≠ 1) : P (Nat.card {y : H // α y = y}) := by
  obtain ⟨u, hu, ho, hcard⟩ := fixed_card_eq_centralizerIn hZ hin α hα hα1
  rw [hcard]
  exact hcls u hu ho

theorem card_centralizerIn_of_reps {n : ℕ} (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size,
      Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ Q.originalSubgroup)
    (g₀ : Equiv.Perm (Fin n))
    (hg₀ : ∀ h ∈ Q.originalSubgroup, g₀⁻¹ * h * g₀ ∈ Q.originalSubgroup)
    (data : List (Equiv.Perm (Fin n) × Subgroup (Equiv.Perm (Fin n))))
    (hreps : ∀ d ∈ data, g₀⁻¹ * d.1 ∈ Q.originalSubgroup ∧ orderOf d.1 = 2) (cap : ℕ)
    (hok : repsOK n gens gensInv (cosetOrderTables Q g₀ 2) (data.map fun d => toTable d.1) cap =
      true)
    (hK : ∀ d ∈ data, d.2 ≤ centralizerIn Q.originalSubgroup d.1 ∧
      (conjClosure n gens gensInv (toTable d.1) cap).1.size * Nat.card d.2 =
        Nat.card Q.originalSubgroup) :
    ∀ u, g₀⁻¹ * u ∈ Q.originalSubgroup → orderOf u = 2 → ∃ d ∈ data,
      Nat.card (centralizerIn Q.originalSubgroup u) = Nat.card d.2 := by
  have hok' : repsOK n gens gensInv (cosetOrderTables Q g₀ 2) ((data.map Prod.fst).map toTable)
      cap = true := by
    rw [List.map_map]
    exact hok
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn Q hQ hg g₀ hg₀ (by norm_num)
    (data.map Prod.fst) (fun r hr => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hr
      exact hreps d hd) cap hok'
  intro u hu ho
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u hu ho
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hr
  obtain ⟨hKle, hKcard⟩ := hK d hd
  have hcent := centralizerIn_eq_of_le Q.originalSubgroup d.1 hKle (hsize _ hr) hKcard
  refine ⟨d, hd, ?_⟩
  rw [centralizerIn_conj _ hc, hcent, Subgroup.card_map_of_injective (MulAut.conj c).injective]

theorem m11_class_card :
    ∀ u ∈ NativeSporadic.M11, orderOf u = 2 →
    Nat.card (centralizerIn NativeSporadic.M11 u) = 48 := by
  have hn : (11 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m11Certificate := m11Certificate_check.1
  obtain ⟨hok, hsz, -⟩ := m11_oddcore_cover
  obtain ⟨hr, hro, hK, hKc, -⟩ := m11_rep_data
  have hA : m11gA ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]; exact m11a.2
  have hB : m11gB ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]; exact m11b.2
  simp only [repSizes, m11InvReps, m11InvRepWords, List.map_cons, List.map_nil,
    List.cons.injEq, and_true] at hsz
  rw [← m11Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨d, hd, hcard⟩ := card_centralizerIn_of_reps hn m11Certificate hQ
    (pairTables_spec hn hA hB) 1 (fun h hh => by simpa using hh)
    [(evalCodes [m11gA, m11gB] [1], m11CentQ1.originalSubgroup)] (by simpa using ⟨hr, hro⟩) 400
    hok (by
      simp only [List.mem_singleton, forall_eq]
      refine ⟨hK, ?_⟩
      rw [hsz, hKc, m11Certificate_originalSubgroup, m11_card]) u (by simpa using hu) ho
  simp only [List.mem_singleton] at hd
  subst hd
  rw [hcard, hKc]

theorem m11_fixed_card
    (α : MulAut NativeSporadic.M11) (hα : α * α = 1) (hα1 : α ≠ 1) :
    Nat.card {x : NativeSporadic.M11 // α x = x} = 48 :=
  fixed_card_of_classes (P := fun c => c = 48) m11_center_eq_bot'
    (inner_eq_top_of_card_le m11_center_eq_bot' m11_mulAut_card) m11_class_card α hα hα1

theorem m23_class_card :
    ∀ u ∈ NativeSporadic.M23, orderOf u = 2 →
    Nat.card (centralizerIn NativeSporadic.M23 u) = 2688 := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m23Certificate := m23Certificate_check
  obtain ⟨hok, hsz, -⟩ := m23_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m23_rep_data1
  have hA : m23PermA ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have hB : m23PermB ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  rw [m23InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m23Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨d, hd, hcard⟩ := card_centralizerIn_of_reps hn m23Certificate hQ
    (pairTables_spec hn hA hB) 1 (fun h hh => by simpa using hh)
    [(m23Rep1, m23CentQ1.originalSubgroup)] (by
      intro d hd
      simp only [List.mem_singleton] at hd
      subst hd
      exact ⟨by simpa using hr1, hro1⟩) 4000 hok (by
      intro d hd
      simp only [List.mem_singleton] at hd
      subst hd
      refine ⟨hK1, ?_⟩
      rw [hsz, hKc1, m23Certificate_originalSubgroup, m23_card]) u (by simpa using hu) ho
  simp only [List.mem_singleton] at hd
  subst hd
  rw [hcard, hKc1]

theorem m23_fixed_card
    (α : MulAut NativeSporadic.M23) (hα : α * α = 1) (hα1 : α ≠ 1) :
    Nat.card {x : NativeSporadic.M23 // α x = x} = 2688 :=
  fixed_card_of_classes (P := fun c => c = 2688) m23_center_eq_bot'
    (inner_eq_top_of_card_le m23_center_eq_bot' m23_mulAut_card) m23_class_card α hα hα1

theorem m24_class_card :
    ∀ u ∈ NativeSporadic.M24, orderOf u = 2 →
    Nat.card (centralizerIn NativeSporadic.M24 u) = 21504 ∨
      Nat.card (centralizerIn NativeSporadic.M24 u) = 7680 := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m24Certificate := m24Certificate_check
  obtain ⟨hok, hsz, -⟩ := m24_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m24_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, -⟩ := m24_rep_data2
  have hA : m24gA ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  have hB : m24gB ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  rw [m24InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m24Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨d, hd, hcard⟩ := card_centralizerIn_of_reps hn m24Certificate hQ
    (pairTables_spec hn hA hB) 1 (fun h hh => by simpa using hh)
    [(m24Rep1, m24CentQ1.originalSubgroup), (m24Rep2, m24CentQ2.originalSubgroup)] (by
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact ⟨by simpa using hr1, hro1⟩
      · exact ⟨by simpa using hr2, hro2⟩) 40000 hok (by
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · refine ⟨hK1, ?_⟩
        rw [hsz.1, hKc1, m24Certificate_originalSubgroup, m24_card]
      · refine ⟨hK2, ?_⟩
        rw [hsz.2, hKc2, m24Certificate_originalSubgroup, m24_card]) u (by simpa using hu) ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact Or.inr (hcard.trans hKc1)
  · exact Or.inl (hcard.trans hKc2)

theorem m24_fixed_card
    (α : MulAut NativeSporadic.M24) (hα : α * α = 1) (hα1 : α ≠ 1) :
    Nat.card {x : NativeSporadic.M24 // α x = x} = 21504 ∨
      Nat.card {x : NativeSporadic.M24 // α x = x} = 7680 :=
  fixed_card_of_classes (P := fun c => c = 21504 ∨ c = 7680) m24_center_eq_bot'
    (inner_eq_top_of_card_le m24_center_eq_bot' m24_mulAut_card) m24_class_card α hα hα1

end CFSG.GH74.Generic.S45.LAlt
