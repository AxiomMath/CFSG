module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Outer

public section

namespace CFSG.GH74.Generic.S45.LSporB

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.OuterAutomorphisms

theorem centralizer_card_of_reps {n : ℕ} (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
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
    ∀ u, g₀⁻¹ * u ∈ Q.originalSubgroup → orderOf u = 2 →
      ∃ d ∈ data, Nat.card (centralizerIn Q.originalSubgroup u) = Nat.card d.2 := by
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

theorem m22_inner_centralizer_card :
    ∀ u ∈ NativeSporadic.M22, orderOf u = 2 →
      Nat.card (centralizerIn NativeSporadic.M22 u) = 384 := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, hsz, -⟩ := m22_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m22_rep_data1
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m22Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨d, hd, hcard⟩ := centralizer_card_of_reps hn m22Certificate hQ
    (pairTables_spec hn hA hB) 1 (fun h hh => by simpa using hh)
    [(m22Rep1, m22CentQ1.originalSubgroup)]
    (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      exact ⟨by simpa using hr1, hro1⟩) 2000 hok
    (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      refine ⟨hK1, ?_⟩
      rw [hsz, hKc1, m22Certificate_originalSubgroup, m22_card]) u (by simpa using hu) ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  rw [hcard, hKc1]

theorem m22_outer_centralizer_card :
    ∀ u, m22Delta⁻¹ * u ∈ NativeSporadic.M22 → orderOf u = 2 →
      Nat.card (centralizerIn NativeSporadic.M22 u) = 320 ∨
        Nat.card (centralizerIn NativeSporadic.M22 u) = 1344 := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, hsz, -⟩ := m22_outer_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m22_out_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, -⟩ := m22_out_rep_data2
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22OutReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  have hg₀ : ∀ h ∈ m22Certificate.originalSubgroup,
      m22Delta⁻¹ * h * m22Delta ∈ m22Certificate.originalSubgroup := by
    rw [m22Certificate_originalSubgroup]
    exact inv_conj_mem _ m22_delta_normalizes m22_delta_sq
  rw [← m22Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨d, hd, hcard⟩ := centralizer_card_of_reps hn m22Certificate hQ
    (pairTables_spec hn hA hB) m22Delta hg₀
    [(m22OutRep1, m22OutCentQ1.originalSubgroup), (m22OutRep2, m22OutCentQ2.originalSubgroup)]
    (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact ⟨hr1, hro1⟩
      · exact ⟨hr2, hro2⟩) 2000 hok
    (fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · refine ⟨hK1, ?_⟩
        rw [hsz.1, hKc1, m22Certificate_originalSubgroup, m22_card]
      · refine ⟨hK2, ?_⟩
        rw [hsz.2, hKc2, m22Certificate_originalSubgroup, m22_card]) u hu ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact Or.inl (by rw [hcard, hKc1])
  · exact Or.inr (by rw [hcard, hKc2])

section Fixed

variable {M : Type*} [Group M]

theorem card_fixSub_of_conjOn (N : Subgroup M) (α : MulAut N) (u : M)
    (hα : ∀ h : N, (α h : M) = u * h * u⁻¹) :
    Nat.card (fixSub α) = Nat.card (centralizerIn N u) := by
  rw [← map_fixSub_conjOn N α u hα, Subgroup.card_map_of_injective N.subtype_injective]

theorem inner_fixSub_card (N : Subgroup M) (hcenter : Subgroup.center N = ⊥) {P : ℕ → Prop}
    (hw : ∀ u ∈ N, orderOf u = 2 → P (Nat.card (centralizerIn N u))) (α : MulAut N)
    (hα2 : α * α = 1) (hα1 : α ≠ 1) (hin : α ∈ inner N) : P (Nat.card (fixSub α)) := by
  obtain ⟨g, hg⟩ := hin
  have hgg : g * g = 1 := by
    have h1 : MulAut.conj (g * g) = 1 := by rw [map_mul, hg, hα2]
    have hc : g * g ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro x
      have := congrArg (fun a : MulAut N => a x) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc x * (g * g) = (g * g * x * (g * g)⁻¹) * (g * g) := by rw [this]
        _ = g * g * x := by group
    rw [hcenter, Subgroup.mem_bot] at hc
    exact hc
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hα1 (by rw [← hg, map_one])
  have hgord : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hgg) hg1
  have hαg : ∀ h : N, (α h : M) = (g : M) * h * (g : M)⁻¹ := by
    intro h
    rw [← hg, MulAut.conj_apply]
    rfl
  rw [card_fixSub_of_conjOn N α (g : M) hαg]
  exact hw (g : M) g.2 (by rw [Subgroup.orderOf_coe]; exact hgord)

theorem outer_fixSub_card (N : Subgroup M) [Finite N] (δ : M)
    (hδ : ∀ h ∈ N, δ * h * δ⁻¹ ∈ N) (hδ2 : δ * δ ∈ N) (hcenter : Subgroup.center N = ⊥)
    (houter : ∀ g ∈ N, ¬∀ h ∈ N, δ * g * h = h * (δ * g))
    (hcard : Nat.card (MulAut N) ≤ 2 * Nat.card N) {P : ℕ → Prop}
    (hw : ∀ u, δ⁻¹ * u ∈ N → orderOf u = 2 → P (Nat.card (centralizerIn N u)))
    (α : MulAut N) (hα2 : α * α = 1) (hα : α ∉ inner N) : P (Nat.card (fixSub α)) := by
  have hδ' := inv_conj_mem N hδ hδ2
  obtain ⟨g, hg, hαg⟩ := exists_eq_conj_of_outer N δ hδ hδ2 hcenter houter hcard α hα
  set u := g * δ
  have hu : δ⁻¹ * u ∈ N := by
    simpa [u, mul_assoc] using hδ' g hg
  have hu2N : u * u ∈ N := by
    have : u * u = g * (δ * g * δ⁻¹) * (δ * δ) := by simp only [u]; group
    rw [this]
    exact N.mul_mem (N.mul_mem hg (hδ g hg)) hδ2
  have hu2 : u * u = 1 := by
    have hc : (⟨u * u, hu2N⟩ : N) ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := congrArg (fun φ : MulAut N => (φ z : M)) hα2
      simp only [MulAut.mul_apply, MulAut.one_apply] at hz
      rw [hαg, hαg] at hz
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (z : M) * (u * u) = u * (u * z * u⁻¹) * u⁻¹ * (u * u) := by rw [hz]
        _ = u * u * z := by group
    rw [hcenter, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hu1 : u ≠ 1 := by
    intro h1
    apply hα
    refine ⟨1, MulEquiv.ext fun z => Subtype.ext ?_⟩
    rw [hαg, h1]
    simp
  have ho : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  rw [card_fixSub_of_conjOn N α u hαg]
  exact hw u hu ho

end Fixed

end CFSG.GH74.Generic.S45.LSporB

namespace CFSG.GH74.Generic.S45

open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms

theorem m22_inner_fixed_card
    (α : MulAut NativeSporadic.M22) (hα : α * α = 1) (hα1 : α ≠ 1)
    (hin : α ∈ inner NativeSporadic.M22) : Nat.card {x : NativeSporadic.M22 // α x = x} = 384 := by
  have hcongr : Nat.card {x : NativeSporadic.M22 // α x = x} = Nat.card (fixSub α) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => mem_fixSub.symm)
  rw [hcongr]
  exact LSporB.inner_fixSub_card (P := fun k => k = 384) NativeSporadic.M22 m22_center_eq_bot'
    (fun u hu ho => LSporB.m22_inner_centralizer_card u hu ho) α hα hα1 hin

theorem m22_outer_fixed_card
    (α : MulAut NativeSporadic.M22) (hα : α * α = 1) (hout : α ∉ inner NativeSporadic.M22) :
    Nat.card {x : NativeSporadic.M22 // α x = x} = 320 ∨
      Nat.card {x : NativeSporadic.M22 // α x = x} = 1344 := by
  have hcongr : Nat.card {x : NativeSporadic.M22 // α x = x} = Nat.card (fixSub α) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => mem_fixSub.symm)
  rw [hcongr]
  exact LSporB.outer_fixSub_card (P := fun k => k = 320 ∨ k = 1344) NativeSporadic.M22 m22Delta
    m22_delta_normalizes m22_delta_sq m22_center_eq_bot' m22_delta_outer m22_mulAut_card
    (fun u hu ho => LSporB.m22_outer_centralizer_card u hu ho) α hα hout

theorem m22_fixed_card
    (α : MulAut NativeSporadic.M22) (hα : α * α = 1) (hα1 : α ≠ 1) :
    Nat.card {x : NativeSporadic.M22 // α x = x} = 384 ∨
      Nat.card {x : NativeSporadic.M22 // α x = x} = 320 ∨
        Nat.card {x : NativeSporadic.M22 // α x = x} = 1344 := by
  by_cases hin : α ∈ inner NativeSporadic.M22
  · exact Or.inl (m22_inner_fixed_card α hα hα1 hin)
  · exact Or.inr (m22_outer_fixed_card α hα hin)

end CFSG.GH74.Generic.S45
