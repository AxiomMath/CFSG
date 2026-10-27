module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingIsolated
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Conj
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Map
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Swap

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace Lemma34

open CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

@[expose] noncomputable def conjSylow (S : Sylow 2 G) (g : G) : Sylow 2 G :=
  S.mapSurjective (show Function.Surjective (MulAut.conj g⁻¹).toMonoidHom from
    (MulAut.conj g⁻¹).surjective)

theorem coe_conjSylow (S : Sylow 2 G) (g : G) :
    (conjSylow S g : Subgroup G) = rightConjugate S g := rfl

theorem Hyp.conj (h : Hyp S A₁ A₂) (g : G) :
    Hyp (conjSylow S g) (rightConjugate A₁ g) (rightConjugate A₂ g) :=
  h.map_mulEquiv (MulAut.conj g⁻¹)

omit [Finite G] in
theorem overlapClosure_conj (A₁ A₂ : Subgroup G) (g : G) :
    overlapClosure (rightConjugate A₁ g) (rightConjugate A₂ g) =
      rightConjugate (overlapClosure A₁ A₂) g :=
  overlapClosure_map (MulAut.conj g⁻¹) A₁ A₂

omit [Finite G] in
theorem rightConjugate_le_rightConjugate_iff {X Y : Subgroup G} (g : G) :
    rightConjugate X g ≤ rightConjugate Y g ↔ X ≤ Y :=
  Subgroup.map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective

omit [Finite G] in
theorem mem_rightConjugate_conj {X : Subgroup G} {g x : G} (hx : x ∈ X) :
    g⁻¹ * x * g ∈ rightConjugate X g := by
  rw [mem_rightConjugate_iff]
  simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using hx

theorem Hyp.swap_of_conj (h : Hyp S A₁ A₂) (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁) {a g : G}
    (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha1 : a ≠ 1) (hg : g ∉ overlapClosure A₁ A₂)
    (hS : g⁻¹ * a * g ∈ (S : Subgroup G)) :
    rightConjugate A₁ (g⁻¹ * a * g) = A₂ ∧ rightConjugate A₂ (g⁻¹ * a * g) = A₁ := by
  rcases h.sylow_le_pairStabilizer h12 h21 hS with ⟨h₁, -⟩ | hswap
  · exfalso
    apply hg
    exact mem_overlapClosure_of_union ha ha1 (h.conj_mem_of_mem_normalizer ha hS
      (Or.inl ((rightConjugate_eq_self_iff A₁ _).mp h₁)))
  · exact hswap

omit [Finite G] in
theorem conj_mem_two_of_swap {t v : G} (ht : t * t = 1) (hswap : rightConjugate A₁ t = A₂)
    (hv : v ∈ A₁) : t * v * t ∈ A₂ := by
  rw [← hswap, mem_rightConjugate_iff]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
  have heq : t * (t * v * t) * t⁻¹ = v := by
    calc t * (t * v * t) * t⁻¹ = (t * t) * v * (t * t) := by rw [htinv]; group
      _ = v := by rw [ht, one_mul, mul_one]
  rw [heq]
  exact hv

omit [Finite G] in
theorem commute_conj_of_swap (hc : ⁅A₁, A₂⁆ = ⊥) {t v : G} (ht : t * t = 1) (hv2 : v * v = 1)
    (hswap : rightConjugate A₁ t = A₂) (hv : v ∈ A₁) : Commute t (v⁻¹ * t * v) := by
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left hv2
  have hw : t * v * t ∈ A₂ := conj_mem_two_of_swap ht hswap hv
  have hwv : Commute v (t * v * t) := commute_of_comm hc hv hw
  rw [hvinv]
  change t * (v * t * v) = v * t * v * t
  calc t * (v * t * v) = (t * v * t) * v := by
        rw [show (t * v * t) * v = t * v * t * v by rfl]
        calc t * (v * t * v) = t * v * t * v := by group
          _ = (t * v * t) * v := rfl
    _ = v * (t * v * t) := hwv.eq.symm
    _ = v * t * v * t := by group

theorem Hyp.false_of_inf_eq_bot (h : Hyp S A₁ A₂) (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁)
    (hI : A₁ ⊓ A₂ = ⊥) {a g : G} (ha : a ∈ A₁) (ha2 : orderOf a = 2)
    (hCa : Subgroup.centralizer ({a} : Set G) ≤ overlapClosure A₁ A₂)
    (hg : g ∉ overlapClosure A₁ A₂) (hS : g⁻¹ * a * g ∈ (S : Subgroup G)) : False := by
  set H := overlapClosure A₁ A₂ with hHdef
  set t := g⁻¹ * a * g with htdef
  have ha1 : a ≠ 1 := (orderOf_eq_prime_iff.mp ha2).2
  have haa : a * a = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp ha2).1
  have htt : t * t = 1 := by
    calc t * t = g⁻¹ * (a * a) * g := by rw [htdef]; group
      _ = 1 := by rw [haa]; group
  have ht1 : t ≠ 1 := by
    intro h1
    apply ha1
    calc a = g * t * g⁻¹ := by rw [htdef]; group
      _ = 1 := by rw [h1]; group
  obtain ⟨hswap, -⟩ := h.swap_of_conj h12 h21 (Or.inl ha) ha1 hg hS
  have hB := h.conj g
  have hB12 : ¬ rightConjugate A₁ g ≤ rightConjugate A₂ g := by
    rwa [rightConjugate_le_rightConjugate_iff]
  have hB21 : ¬ rightConjugate A₂ g ≤ rightConjugate A₁ g := by
    rwa [rightConjugate_le_rightConjugate_iff]
  have hHB := overlapClosure_conj A₁ A₂ g
  have htB : t ∈ rightConjugate A₁ g := mem_rightConjugate_conj ha
  have hBI : rightConjugate A₁ g ⊓ rightConjugate A₂ g = ⊥ := by
    change A₁.map (MulAut.conj g⁻¹).toMonoidHom ⊓ A₂.map (MulAut.conj g⁻¹).toMonoidHom = ⊥
    rw [← Subgroup.map_inf A₁ A₂ (MulAut.conj g⁻¹).toMonoidHom
      (fun x y hxy => (MulAut.conj g⁻¹).injective hxy), hI, Subgroup.map_bot]
  have hCt : Subgroup.centralizer ({t} : Set G) ≤ rightConjugate H g := by
    rw [htdef, centralizer_conj_eq a g]
    exact Subgroup.map_mono hCa
  have hTH : (conjSylow S g : Subgroup G) ≤ rightConjugate H g :=
    Subgroup.map_mono (h.sylow_le_overlapClosure h12 h21)
  have key : ∀ v ∈ A₁, v * v = 1 → v ∈ rightConjugate H g := by
    intro v hv hv2
    set s := v⁻¹ * t * v with hsdef
    have hts : Commute t s := commute_conj_of_swap h.comm htt hv2 hswap hv
    have hss : s * s = 1 := by
      calc s * s = v⁻¹ * (t * t) * v := by rw [hsdef]; group
        _ = 1 := by rw [htt]; group
    let P := commutingPairSubgroup t s htt hss hts
    have hPC : P ≤ Subgroup.centralizer ({t} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases mem_commutingPairSubgroup.mp hx with rfl | rfl | rfl | rfl
      · simp
      · rfl
      · exact hts.eq.symm
      · exact ((Commute.refl t).mul_left hts.symm).eq
    have hP2 : IsPGroup 2 P := fun x =>
      ⟨1, by rw [pow_one]; exact Subtype.ext (commutingPairSubgroup_sq x.property)⟩
    obtain ⟨c, hc, hcT⟩ := exists_conj_le_sylow (S := conjSylow S g) hTH (hPC.trans hCt) hP2
    have htP : t ∈ P := mem_commutingPairSubgroup.mpr (Or.inr (Or.inl rfl))
    have hsP : s ∈ P := mem_commutingPairSubgroup.mpr (Or.inr (Or.inr (Or.inl rfl)))
    have hcB : c ∈ overlapClosure (rightConjugate A₁ g) (rightConjugate A₂ g) := hHB ▸ hc
    have htc : c⁻¹ * t * c ∈ (rightConjugate A₁ g : Set G) ∪ rightConjugate A₂ g :=
      hB.conj_mem_of_mem_overlapClosure (Or.inl htB) hcB (hcT t htP)
    have hscT := hcT s hsP
    have hcomm : Commute (c⁻¹ * t * c) (c⁻¹ * s * c) := by
      have := hts.map (MulAut.conj c⁻¹).toMonoidHom
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using this
    have hsc : c⁻¹ * s * c = (v * c)⁻¹ * t * (v * c) := by rw [hsdef]; group
    have hperm := hB.sylow_le_pairStabilizer hB12 hB21 hscT
    have hstay : ∀ {X Y : Subgroup G}, c⁻¹ * t * c ∈ X →
        rightConjugate X (c⁻¹ * s * c) = Y → c⁻¹ * t * c ∈ Y := by
      intro X Y hX hXY
      rw [← hXY]
      have := mem_rightConjugate_conj (g := c⁻¹ * s * c) hX
      rwa [show (c⁻¹ * s * c)⁻¹ * (c⁻¹ * t * c) * (c⁻¹ * s * c) = c⁻¹ * t * c by
        rw [mul_assoc, hcomm.eq, inv_mul_cancel_left]] at this
    have hBI' : ∀ y, y ∈ rightConjugate A₁ g → y ∈ rightConjugate A₂ g → y = 1 := by
      intro y h1 h2
      have : y ∈ rightConjugate A₁ g ⊓ rightConjugate A₂ g := ⟨h1, h2⟩
      rw [hBI, Subgroup.mem_bot] at this
      exact this
    have htc1 : c⁻¹ * t * c ≠ 1 := by
      intro h1
      apply ht1
      calc t = c * (c⁻¹ * t * c) * c⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have hnorm : c⁻¹ * s * c ∈ Subgroup.normalizer (rightConjugate A₁ g : Set G) ∨
        c⁻¹ * s * c ∈ Subgroup.normalizer (rightConjugate A₂ g : Set G) := by
      rcases hperm with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ((rightConjugate_eq_self_iff _ _).mp h₁)
      · exfalso
        rcases htc with htc | htc
        · exact htc1 (hBI' _ htc (hstay htc h₁))
        · exact htc1 (hBI' _ (hstay htc h₂) htc)
    have hsU := hB.conj_mem_of_mem_normalizer (a := t) (g := v * c) (Or.inl htB)
      (hsc ▸ hscT) (hsc ▸ hnorm)
    have hvc : v * c ∈ overlapClosure (rightConjugate A₁ g) (rightConjugate A₂ g) :=
      mem_overlapClosure_of_union (Or.inl htB) ht1 hsU
    rw [hHB] at hvc
    have := (rightConjugate H g).mul_mem hvc ((rightConjugate H g).inv_mem hc)
    rwa [mul_inv_cancel_right] at this
  obtain ⟨E, hEA, ⟨-, hEsq⟩, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) A₁
  have hE4 : 4 ≤ Nat.card E := by
    rw [hEcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 A₁ := Nat.pow_le_pow_right (by norm_num) h.rank_one
  have hEfix := h.fixesOnly_of_card h12 h21 (fun x hx => Or.inl (hEA hx)) hE4
  apply hg
  have hginv : g⁻¹ ∈ H := by
    refine hEfix g⁻¹ fun x hx => ?_
    have hxH := key x (hEA hx) (by rw [← pow_two]; exact hEsq x hx)
    rw [mem_rightConjugate_iff] at hxH
    simpa only [inv_inv] using hxH
  exact H.inv_mem_iff.mp hginv

end Lemma34

end CFSG.ComponentClassification.AschbacherStrongEmbedding
