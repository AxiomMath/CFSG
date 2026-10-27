module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import Certificates.Certificate9567
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreStar
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveGen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveMaxOrbits
public import CFSG.Sporadic.Bridge.Fi22Surj

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Five

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Fischer CFSG.Open
open scoped Pointwise

theorem isElemAbelian_card_closure_two {G : Type*} [Group G] {a b : G}
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hcomm : a * b = b * a)
    (hnt : ∀ i j : ℕ, i < 3 → j < 3 → (i ≠ 0 ∨ j ≠ 0) → a ^ i * b ^ j ≠ 1) :
    IsElemAbelian 3 (Subgroup.closure ({a, b} : Set G)) ∧
      Nat.card (Subgroup.closure ({a, b} : Set G)) = 9 := by
  have hrc : ({a, b} : Set G).Pairwise Commute := by
    rintro x (rfl | rfl) y (rfl | rfl) hxy
    · exact absurd rfl hxy
    · exact hcomm
    · exact hcomm.symm
    · exact absurd rfl hxy
  have hadd : ∀ x : G, x ^ 3 = 1 → ∀ p q : ZMod 3, x ^ (p + q).val = x ^ p.val * x ^ q.val := by
    intro x hx p q
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]
  let φ : (Fin 2 → ZMod 3) → G := fun v => a ^ (v 0).val * b ^ (v 1).val
  have hφ : ∀ v w, φ (v + w) = φ v * φ w := by
    intro v w
    simp only [φ, Pi.add_apply, hadd a ha, hadd b hb]
    simp only [mul_assoc]
    rw [(Commute.pow_pow hcomm _ _).left_comm]
  let Φ : Multiplicative (Fin 2 → ZMod 3) →* G :=
    MonoidHom.mk' (fun v => φ (Multiplicative.toAdd v)) fun v w => hφ _ _
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    by_contra hne
    have hv' : a ^ (Multiplicative.toAdd v 0).val * b ^ (Multiplicative.toAdd v 1).val = 1 := by
      simpa [Φ, φ] using hv
    have hne' : (Multiplicative.toAdd v 0).val ≠ 0 ∨ (Multiplicative.toAdd v 1).val ≠ 0 := by
      by_contra h
      push Not at h
      apply hne
      apply Multiplicative.toAdd.injective
      funext k
      fin_cases k
      · simpa using (ZMod.val_eq_zero _).1 h.1
      · simpa using (ZMod.val_eq_zero _).1 h.2
    exact hnt _ _ (ZMod.val_lt _) (ZMod.val_lt _) hne' hv'
  have hrange : Φ.range = Subgroup.closure ({a, b} : Set G) := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      show φ (Multiplicative.toAdd v) ∈ _
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · refine ⟨Multiplicative.ofAdd (Pi.single 0 1), ?_⟩
        have h1 : (1 : ZMod 3).val = 1 := rfl
        simp [Φ, φ, h1]
      · refine ⟨Multiplicative.ofAdd (Pi.single 1 1), ?_⟩
        have h1 : (1 : ZMod 3).val = 1 := rfl
        simp [Φ, φ, h1]
  refine ⟨⟨Subgroup.isMulCommutative_closure hrc, pow_eq_one_of_mem_closure hrc ?_⟩, ?_⟩
  · rintro s (rfl | rfl)
    exacts [ha, hb]
  · rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr Multiplicative.toAdd]
    norm_num

structure E9Elements (G₁ G₂ : fi22P) : Prop where
  out : ∃ (a b : fi22P), a ∈ Subgroup.closure ({G₁, G₂} : Set fi22P) ∧
    b ∈ Subgroup.closure ({G₁, G₂} : Set fi22P) ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * b = b * a ∧
      ∀ i j : ℕ, i < 3 → j < 3 → (i ≠ 0 ∨ j ≠ 0) → a ^ i * b ^ j ≠ 1

theorem e9Elements_exists {G₁ G₂ : fi22P}
    (h₁ : Rep 3510 g1A G₁.1) (h₂ : Rep 3510 g2A G₂.1) : E9Elements G₁ G₂ := by
  obtain ⟨a, ha, b, hb, ha3, hb3, hab, hnt⟩ := Certificates.certificate9567 G₁.1 G₂.1 h₁ h₂
  have hmap : Subgroup.closure ({G₁.1, G₂.1} : Set (Equiv.Perm (Fin 3510))) =
      (Subgroup.closure ({G₁, G₂} : Set fi22P)).map fi22P.subtype := by
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
    rfl
  rw [hmap] at ha hb
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
  obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
  refine ⟨⟨a', b', ha', hb', Subtype.ext (by simpa using ha3), Subtype.ext (by simpa using hb3),
    Subtype.ext (by simpa using hab), fun i j hi hj hij h => hnt i j hi hj hij ?_⟩⟩
  simpa using congrArg Subtype.val h

theorem exists_e9 {G₁ G₂ : fi22P}
    (h₁ : Rep 3510 g1A G₁.1) (h₂ : Rep 3510 g2A G₂.1) :
    ∃ R : Subgroup fi22P, R ≤ Subgroup.closure ({G₁, G₂} : Set fi22P) ∧
      IsElemAbelian 3 R ∧ Nat.card R = 9 := by
  obtain ⟨a, b, ha, hb, ha3, hb3, hcomm, hnt⟩ := (e9Elements_exists h₁ h₂).out
  have hR := isElemAbelian_card_closure_two ha3 hb3 hcomm hnt
  refine ⟨Subgroup.closure ({a, b} : Set fi22P), ?_, hR.1, hR.2⟩
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  exacts [ha, hb]

theorem sum_ncard_le_orbit_ncard {G α : Type*} [Group G] [MulAction G α] [Finite G]
    (s₀ : α) (E : Fin 4 → Set α) (hE : ∀ j, E j ⊆ MulAction.orbit G s₀)
    (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j)) (hfin : ∀ j, (E j).Finite) :
    ∑ j, (E j).ncard ≤ (MulAction.orbit G s₀).ncard := by
  classical
  let Ef : Fin 4 → Finset α := fun j => (hfin j).toFinset
  have hEf : ∀ j, ((Ef j : Finset α) : Set α) = E j := fun j => (hfin j).coe_toFinset
  have hdisjf : ∀ i j, i ≠ j → Disjoint (Ef i) (Ef j) := fun i j hij => by
    rw [← Finset.disjoint_coe, hEf, hEf]
    exact hdisj i j hij
  have hsub : ((Finset.univ.biUnion Ef : Finset α) : Set α) ⊆ MulAction.orbit G s₀ := by
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
    obtain ⟨j, hj⟩ := hx
    exact hE j (by rwa [← hEf j])
  have hcard : (Finset.univ.biUnion Ef).card = ∑ j, (E j).ncard := by
    rw [Finset.card_biUnion (fun i _ j _ hij => hdisjf i j hij)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hEf j, Set.ncard_coe_finset]
  have := Set.ncard_le_ncard hsub (Set.finite_range _)
  rwa [Set.ncard_coe_finset, hcard] at this

theorem orbit_subgroup_le (Γ : Subgroup fi22P) (T : Set (Fin 3510)) :
    MulAction.orbit Γ T ⊆ MulAction.orbit fi22P T := by
  rintro _ ⟨g, rfl⟩
  exact ⟨↑g, rfl⟩

theorem orbit_subset_of_map {Γ : Subgroup fi22P} {T : Set (Fin 3510)}
    {E : Set (Set (Fin 3510))}
    (h : E ⊆ {S | ∃ g ∈ Γ.map fi22P.subtype, S = g • T}) :
    E ⊆ MulAction.orbit Γ T := by
  intro S hS
  obtain ⟨g, hg, rfl⟩ := h hS
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hg
  exact ⟨⟨m, hm⟩, rfl⟩

structure OrbitPieces (Γ : Subgroup fi22P) : Prop where
  out : ∃ (A B C : Equiv.Perm (Fin 3510)), A ∈ fi22P ∧ B ∈ fi22P ∧ C ∈ fi22P ∧
    ∃ E : Fin 4 → Set (Set (Fin 3510)),
      (∀ j, (E j).Finite) ∧ (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
      (E 0 ⊆ {S | ∃ g ∈ Γ.map fi22P.subtype, S = g • finSet 3510 s0Arr.toList}) ∧
      (E 1 ⊆ {S | ∃ g ∈ Γ.map fi22P.subtype, S = g • (A • finSet 3510 s0Arr.toList)}) ∧
      (E 2 ⊆ {S | ∃ g ∈ Γ.map fi22P.subtype, S = g • (B • finSet 3510 s0Arr.toList)}) ∧
      (E 3 ⊆ {S | ∃ g ∈ Γ.map fi22P.subtype, S = g • (C • finSet 3510 s0Arr.toList)}) ∧
      (E 0).ncard = 1 ∧ (E 1).ncard = 1575 ∧ (E 2).ncard = 22400 ∧ (E 3).ncard = 37800

theorem orbitPieces_exists
    {G₁ G₂ : fi22P}
    (h₁ : Rep 3510 g1A G₁.1) (h₂ : Rep 3510 g2A G₂.1) :
    OrbitPieces (Subgroup.closure ({G₁, G₂} : Set fi22P)) := by
  obtain ⟨A, B, C, hAP, hBP, hCP, E, hfin, hdisj, hE, hcard⟩ := orbit_pieces h₁ h₂
  have hmap : ∀ T : Set (Fin 3510), MulAction.orbit (Subgroup.closure ({G₁, G₂} : Set fi22P)) T ⊆
      {S | ∃ g ∈ (Subgroup.closure ({G₁, G₂} : Set fi22P)).map fi22P.subtype, S = g • T} := by
    rintro T _ ⟨g, rfl⟩
    exact ⟨g.1.1, ⟨g.1, g.2, rfl⟩, rfl⟩
  refine ⟨⟨A, B, C, hAP, hBP, hCP, E, hfin, hdisj, ?_, (hE 1).trans (hmap _),
    (hE 2).trans (hmap _), (hE 3).trans (hmap _), hcard 0, hcard 1, hcard 2, hcard 3⟩⟩
  have h0 := (hE 0).trans (hmap _)
  simpa using h0

theorem OrbitPieces.orbit_ncard_ge {Γ : Subgroup fi22P} (h : OrbitPieces Γ) :
    61776 ≤ (MulAction.orbit fi22P (finSet 3510 s0Arr.toList)).ncard := by
  obtain ⟨A, B, C, hA, hB, hC, E, hfin, hdisj, h0, h1, h2, h3, hc0, hc1, hc2, hc3⟩ := h.out
  have hA' : (⟨A, hA⟩ : fi22P) • finSet 3510 s0Arr.toList =
      A • finSet 3510 s0Arr.toList := rfl
  have hB' : (⟨B, hB⟩ : fi22P) • finSet 3510 s0Arr.toList =
      B • finSet 3510 s0Arr.toList := rfl
  have hC' : (⟨C, hC⟩ : fi22P) • finSet 3510 s0Arr.toList =
      C • finSet 3510 s0Arr.toList := rfl
  have hAeq : MulAction.orbit fi22P (A • finSet 3510 s0Arr.toList) =
      MulAction.orbit fi22P (finSet 3510 s0Arr.toList) := by
    rw [← hA', MulAction.orbit_smul]
  have hBeq : MulAction.orbit fi22P (B • finSet 3510 s0Arr.toList) =
      MulAction.orbit fi22P (finSet 3510 s0Arr.toList) := by
    rw [← hB', MulAction.orbit_smul]
  have hCeq : MulAction.orbit fi22P (C • finSet 3510 s0Arr.toList) =
      MulAction.orbit fi22P (finSet 3510 s0Arr.toList) := by
    rw [← hC', MulAction.orbit_smul]
  have hE : ∀ j, E j ⊆ MulAction.orbit fi22P (finSet 3510 s0Arr.toList) := by
    intro j
    fin_cases j
    · exact (orbit_subset_of_map h0).trans (orbit_subgroup_le Γ _)
    · rw [← hAeq]
      exact (orbit_subset_of_map h1).trans (orbit_subgroup_le Γ _)
    · rw [← hBeq]
      exact (orbit_subset_of_map h2).trans (orbit_subgroup_le Γ _)
    · rw [← hCeq]
      exact (orbit_subset_of_map h3).trans (orbit_subgroup_le Γ _)
  have hle := sum_ncard_le_orbit_ncard (G := fi22P) (finSet 3510 s0Arr.toList) E hE hdisj hfin
  simpa [hc0, hc1, hc2, hc3, Fin.sum_univ_four] using hle

theorem stabilizer_card_le_of_orbit_ncard
    (h : 61776 ≤ (MulAction.orbit fi22P (finSet 3510 s0Arr.toList)).ncard) :
    Nat.card (MulAction.stabilizer fi22P (finSet 3510 s0Arr.toList)) ≤ 1045094400 := by
  have hcard := card_eq_ncard_orbit_mul (G := fi22P) (finSet 3510 s0Arr.toList)
  rw [card_fi22P] at hcard
  have hmul : 61776 * Nat.card (MulAction.stabilizer fi22P (finSet 3510 s0Arr.toList)) ≤
      (MulAction.orbit fi22P (finSet 3510 s0Arr.toList)).ncard *
        Nat.card (MulAction.stabilizer fi22P (finSet 3510 s0Arr.toList)) :=
    Nat.mul_le_mul_right _ h
  rw [← hcard] at hmul
  have hnum : (64561751654400 : ℕ) = 61776 * 1045094400 := by norm_num
  rw [hnum] at hmul
  exact Nat.le_of_mul_le_mul_left hmul (by norm_num)

theorem closure_le_stabilizer {G₁ G₂ : fi22P}
    (h₁ : Rep 3510 g1A G₁.1) (h₂ : Rep 3510 g2A G₂.1) :
    Subgroup.closure ({G₁, G₂} : Set fi22P) ≤
      MulAction.stabilizer fi22P (finSet 3510 s0Arr.toList) :=
  closure_le_stab h₁ h₂

theorem closure_card_eq
    {G₁ G₂ : fi22P}
    (h₁ : Rep 3510 g1A G₁.1) (h₂ : Rep 3510 g2A G₂.1) :
    Nat.card (Subgroup.closure ({G₁, G₂} : Set fi22P)) = 1045094400 := by
  have hP := orbitPieces_exists h₁ h₂
  have hsum := hP.orbit_ncard_ge
  have hMle := stabilizer_card_le_of_orbit_ncard hsum
  have hΓstab := closure_le_stabilizer h₁ h₂
  set Γ : Subgroup fi22P := Subgroup.closure ({G₁, G₂} : Set fi22P) with hΓ
  rcases closure_maximal h₁ h₂ (MulAction.stabilizer fi22P (finSet 3510 s0Arr.toList))
    hΓstab with hM | hM
  · have hupper : Nat.card Γ ≤ 1045094400 := by rw [hΓ, ← hM]; exact hMle
    have hlower : 1045094400 ≤ Nat.card Γ := by
      have h1 := card_closure_ge h₁ h₂
      have h2 : Γ.map fi22P.subtype =
          Subgroup.closure ({G₁.1, G₂.1} : Set (Equiv.Perm (Fin 3510))) := by
        rw [hΓ, MonoidHom.map_closure, Set.image_pair]; rfl
      rw [← h2, Subgroup.card_map_of_injective fi22P.subtype_injective] at h1
      exact h1
    exact le_antisymm hupper hlower
  · exfalso
    have hcard := card_eq_ncard_orbit_mul (G := fi22P) (finSet 3510 s0Arr.toList)
    rw [hM, Subgroup.card_top] at hcard
    have hpos : 0 < Nat.card fi22P := Nat.card_pos
    have hone : (MulAction.orbit fi22P (finSet 3510 s0Arr.toList)).ncard = 1 := by
      have hEq : (1 : ℕ) * Nat.card fi22P =
          (MulAction.orbit fi22P (finSet 3510 s0Arr.toList)).ncard * Nat.card fi22P := by
        rw [one_mul]; exact hcard
      exact (Nat.eq_of_mul_eq_mul_right hpos hEq).symm
    omega

structure CoreThreeData (G : Type) [Group G] [Finite G] : Prop where
  out : ∃ (x y : G) (m : ℕ) (M R : Subgroup G),
    CoreFacts x y M ∧ Nat.card G = 5 ^ 2 * m ∧ ¬ 5 ∣ m ∧
      Nat.card M = 1045094400 ∧ R ≤ M ∧ IsElemAbelian 3 R ∧ Nat.card R = 9

theorem CoreThreeData.of_mulEquiv {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (hG : CoreThreeData G) (φ : G ≃* H) : CoreThreeData H := by
  obtain ⟨x, y, m, M, R, hF, hm, hm5, hMcard, hRM, hRabel, hRcard⟩ := hG.out
  refine ⟨⟨φ x, φ y, m, M.map φ.toMonoidHom, R.map φ.toMonoidHom, hF.map φ,
    by rw [← hm]; exact Nat.card_congr φ.toEquiv.symm, hm5,
    by rw [Subgroup.card_map_of_injective φ.injective]; exact hMcard,
    Subgroup.map_mono hRM, CFSG.Open.IsElemAbelian.map hRabel φ.toMonoidHom,
    by rw [Subgroup.card_map_of_injective φ.injective]; exact hRcard⟩⟩

theorem CoreFacts.uPrime_eq {G : Type} [Group G] [Finite G] {x y : G} {M : Subgroup G}
    (h : CoreFacts x y M)
    (hT : GLBCore 5 1 (Subgroup.closure ({x, y} : Set G)) ≠ ⊤) :
    GLBCore 5 1 (Subgroup.closure ({x, y} : Set G)) = M := by
  rcases h.max _ h.le with h1 | h1
  · exact h1
  · exact absurd h1 hT

theorem CoreThreeData.uPrime {G : Type} [Group G] [Finite G] (hG : CoreThreeData G)
    (T : Sylow 5 G) (hT : GLBCore 5 1 (T : Subgroup G) ≠ ⊤) :
    (∀ Y : Subgroup G, GLBCore 5 1 (T : Subgroup G) ≤ Y →
        Y = GLBCore 5 1 (T : Subgroup G) ∨ Y = ⊤) ∧
      (∀ N : Subgroup G, N ≤ GLBCore 5 1 (T : Subgroup G) →
        (N.subgroupOf (GLBCore 5 1 (T : Subgroup G))).Normal →
          Nat.Coprime 5 (Nat.card N) → N = ⊥) ∧
      Nat.card (GLBCore 5 1 (T : Subgroup G)) = 1045094400 ∧
      ∃ R : Subgroup G, R ≤ GLBCore 5 1 (T : Subgroup G) ∧
        IsElemAbelian 3 R ∧ Nat.card R = 9 := by
  obtain ⟨x, y, m, M, R, hF, hm, hm5, hMcard, hRM, hRabel, hRcard⟩ := hG.out
  obtain ⟨g, hg⟩ := hF.plane.exists_conj_closure hm hm5 T
  have h1 : g * x * g⁻¹ = MulAut.conj g x := rfl
  have h2 : g * y * g⁻¹ = MulAut.conj g y := rfl
  rw [h1, h2] at hg
  rw [← hg] at hT ⊢
  have hF' : CoreFacts (MulAut.conj g x) (MulAut.conj g y)
      (M.map (MulAut.conj g).toMonoidHom) := hF.map (MulAut.conj g)
  have hΓM : GLBCore 5 1 (Subgroup.closure ({MulAut.conj g x, MulAut.conj g y} : Set G)) =
      M.map (MulAut.conj g).toMonoidHom := hF'.uPrime_eq hT
  obtain ⟨hmax, hcore⟩ := hF'.uPrime hT
  refine ⟨hmax, hcore, ?_, ?_⟩
  · rw [hΓM, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hMcard
  · refine ⟨R.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_⟩
    · rw [hΓM]
      exact Subgroup.map_mono hRM
    · exact CFSG.Open.IsElemAbelian.map hRabel _
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hRcard

theorem coreDataThree_fi22P :
    CoreThreeData fi22P := by
  obtain ⟨x, y, hx, hy, hD, hN⟩ := orbit_part
  obtain ⟨G₁, G₂, h₁, h₂, hG₁, hG₂⟩ := gen_part hx hy hD
  obtain ⟨R, hRle, hRabel, hRcard⟩ := exists_e9 h₁ h₂
  refine ⟨⟨x, y, 2582470066176, Subgroup.closure ({G₁, G₂} : Set fi22P), R,
    ⟨hD, hN, star5_part hx hy hD, closure_maximal h₁ h₂, ?_⟩, ?_, by norm_num,
    closure_card_eq h₁ h₂, hRle, hRabel, hRcard⟩⟩
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    exacts [hG₁, hG₂]
  · rw [card_fi22P]
    norm_num

end CFSG.AGLEmbedding.KFactProofs.Fi22Five

namespace CFSG.AGLEmbedding

open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.Open CFSG.Monster.B.Fischer

theorem fi22_gammaOne_three
    {K : Type} [Group K] [Finite K] (hK : IsFi22 K) (T : Sylow 5 K) {Y : Subgroup K}
    (hTY : GLBCore 5 1 (T : Subgroup K) ≤ Y) (hY : Y ≠ ⊤) :
    ¬ 3 ^ 7 ∣ Nat.card Y ∧
      ∃ R : Subgroup K, R ≤ Y ∧ IsElemAbelian 3 R ∧ Nat.card R = 9 := by
  obtain ⟨φ⟩ := hK
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have hdata : CoreThreeData K := coreDataThree_fi22P.of_mulEquiv
    ((φ.trans β.symm).trans CFSG.Monster.B.Fischer.fi22PermEquiv).symm
  have hTne : GLBCore 5 1 (T : Subgroup K) ≠ ⊤ := fun htop =>
    hY (top_le_iff.1 (htop ▸ hTY))
  obtain ⟨hmax, -, hcard, hE9⟩ := hdata.uPrime T hTne
  have hYeq : Y = GLBCore 5 1 (T : Subgroup K) := by
    rcases hmax Y hTY with h | h
    · exact h
    · exact absurd h hY
  refine ⟨?_, ?_⟩
  · rw [hYeq, hcard]
    norm_num
  · obtain ⟨R, hRΓ, hRabel, hRcard⟩ := hE9
    exact ⟨R, hYeq ▸ hRΓ, hRabel, hRcard⟩

theorem three_pow_nine_dvd_card_of_isFi22
    {K : Type} [Group K] [Finite K]
    (hK : IsFi22 K) :
    3 ^ 9 ∣ Nat.card K := by
  obtain ⟨φ⟩ := hK
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have e : K ≃* fi22P := (φ.trans β.symm).trans CFSG.Monster.B.Fischer.fi22PermEquiv
  rw [Nat.card_congr e.toEquiv, card_fi22P]
  norm_num

end CFSG.AGLEmbedding
