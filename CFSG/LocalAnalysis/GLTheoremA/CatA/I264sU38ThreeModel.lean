module

public import Certificates.Certificate810201
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS07AutRankU38

public section

namespace CFSG.LocalAnalysis.GLTheoremA.U38ThreeModel

open CFSG.Open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
  CFSG.RankThree.Native CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.RankThree.PartOne U38Sylow U38Three
open CFSG.LocalAnalysis.GLTheoremA.CatB

section TwoPoint

variable {n : ℕ}

@[expose] def stab2 (G : Subgroup (Equiv.Perm (Fin n))) (P Q : Fin n) : Subgroup (Equiv.Perm (Fin n)) :=
  G ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) P ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) Q

theorem mem_stab2 {G : Subgroup (Equiv.Perm (Fin n))} {P Q : Fin n} {g : Equiv.Perm (Fin n)} :
    g ∈ stab2 G P Q ↔ g ∈ G ∧ g P = P ∧ g Q = Q := by
  simp only [stab2, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, and_assoc]

theorem card_stab2_mul {G : Subgroup (Equiv.Perm (Fin n))}
    (h2 : ∀ a b a' b' : Fin n, a ≠ b → a' ≠ b' → ∃ g ∈ G, g a = a' ∧ g b = b') {P Q : Fin n}
    (hPQ : P ≠ Q) : n * (n - 1) * Nat.card (stab2 G P Q) = Nat.card G := by
  classical
  have horb : MulAction.orbit G (P, Q) = {x : Fin n × Fin n | x.1 ≠ x.2} := by
    ext ⟨a, b⟩
    simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq, Prod.smul_mk, Prod.mk.injEq, Subgroup.smul_def,
      Equiv.Perm.smul_def]
    constructor
    · rintro ⟨g, rfl, rfl⟩ h
      exact hPQ ((g : Equiv.Perm (Fin n)).injective h)
    · intro hab
      obtain ⟨g, hg, h1, h2'⟩ := h2 P Q a b hPQ hab
      exact ⟨⟨g, hg⟩, h1, h2'⟩
  have horbc : Nat.card (MulAction.orbit G (P, Q)) = n * (n - 1) := by
    rw [horb]
    change Nat.card {x : Fin n × Fin n // x.1 ≠ x.2} = _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hoff : (Finset.univ.filter fun x : Fin n × Fin n => x.1 ≠ x.2) =
        (Finset.univ : Finset (Fin n)).offDiag := by
      ext x
      simp [Finset.mem_offDiag]
    rw [hoff, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin, Nat.mul_sub_one]
  have hmap : (MulAction.stabilizer G (P, Q)).map G.subtype = stab2 G P Q := by
    ext g
    rw [mem_stab2]
    constructor
    · rintro ⟨h, hh, rfl⟩
      rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hh
      simp only [Prod.smul_mk, Prod.mk.injEq, Subgroup.smul_def, Equiv.Perm.smul_def] at hh
      exact ⟨h.2, hh⟩
    · rintro ⟨hg, h1, h2'⟩
      refine ⟨⟨g, hg⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
      simp only [Prod.smul_mk, Prod.mk.injEq, Subgroup.smul_def, Equiv.Perm.smul_def]
      exact ⟨h1, h2'⟩
  have hstab : Nat.card (MulAction.stabilizer G (P, Q)) = Nat.card (stab2 G P Q) := by
    rw [← hmap, Subgroup.card_map_of_injective G.subtype_injective]
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G (P, Q))
  rw [Nat.card_prod, horbc, hstab] at h
  exact h

theorem card_stab2 {G : Subgroup (Equiv.Perm (Fin n))}
    (h2 : ∀ a b a' b' : Fin n, a ≠ b → a' ≠ b' → ∃ g ∈ G, g a = a' ∧ g b = b') {m : ℕ}
    (hG : Nat.card G = n * (n - 1) * m) (hn : 2 ≤ n) {P Q : Fin n} (hPQ : P ≠ Q) :
    Nat.card (stab2 G P Q) = m := by
  have hc := card_stab2_mul h2 hPQ
  rw [hG] at hc
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (by omega) (by omega)) hc

end TwoPoint

section M1

theorem card_stab2_U38G {P Q : Fin 513} (hPQ : P ≠ Q) :
    Nat.card (stab2 U38G P Q) = 378 :=
  card_stab2 U38G_twoTransitive (card_U38G.trans (by norm_num)) (by norm_num) hPQ

section X'

theorem card_stab2_X' {P Q : Fin 513} (hPQ : P ≠ Q) : Nat.card (stab2 X' P Q) = 21 :=
  card_stab2 X'_twoTransitive (card_X'.trans (by norm_num)) (by norm_num) hPQ

theorem eq_of_fix_two {T : Subgroup (Equiv.Perm (Fin 513))} (hTX : T ≤ X') (hT2 : IsPGroup 2 T)
    (hT1 : T ≠ ⊥) {P Q : Fin 513} (hP : ∀ t ∈ T, t P = P) (hQ : ∀ t ∈ T, t Q = Q) : P = Q := by
  by_contra hPQ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd : Nat.card T ∣ 21 := by
    rw [← card_stab2_X' hPQ]
    exact Subgroup.card_dvd_of_le fun t ht => mem_stab2.2 ⟨hTX ht, hP t ht, hQ t ht⟩
  rcases hT2.card_eq_or_dvd with h1 | h2
  · exact hT1 (Subgroup.eq_bot_of_card_eq T h1)
  · have := h2.trans hd
    norm_num at this

end X'

theorem exists_fix_of_two {T : Subgroup (Equiv.Perm (Fin 513))} (hT2 : IsPGroup 2 T) :
    ∃ P : Fin 513, ∀ t ∈ T, t P = P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hT2.card_modEq_card_fixedPoints (Fin 513)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  by_contra hno
  push Not at hno
  have hemp : MulAction.fixedPoints T (Fin 513) = ∅ := by
    ext x
    simp only [MulAction.mem_fixedPoints, Set.mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨t, ht, hx⟩ := hno x
    exact ⟨⟨t, ht⟩, hx⟩
  rw [hemp, Nat.card_coe_set_eq, Set.ncard_empty] at h
  norm_num [Nat.ModEq] at h

theorem exists_fix_ne_of_three {A : Subgroup (Equiv.Perm (Fin 513))} (hA3 : IsPGroup 3 A) {P : Fin 513}
    (hP : ∀ a ∈ A, a P = P) : ∃ P', P' ≠ P ∧ ∀ a ∈ A, a P' = P' := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hA3.card_modEq_card_fixedPoints (Fin 513)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  by_contra hno
  push Not at hno
  have hfix : MulAction.fixedPoints A (Fin 513) = {P} := by
    ext x
    simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hxP
      obtain ⟨a, ha, hax⟩ := hno x hxP
      exact hax (hx ⟨a, ha⟩)
    · rintro rfl ⟨a, ha⟩
      exact hP a ha
  rw [hfix, Nat.card_coe_set_eq, Set.ncard_singleton] at h
  norm_num [Nat.ModEq] at h

theorem exists_conj_fix01
    {T A : Subgroup (Equiv.Perm (Fin 513))} (hTX : T ≤ X') (hT2 : IsPGroup 2 T)
    (hT1 : T ≠ ⊥) (hA3 : IsPGroup 3 A) (hAN : A ≤ Subgroup.normalizer (T : Set (Equiv.Perm (Fin 513)))) :
    ∃ g ∈ U38G, ∀ a ∈ A, (g * a * g⁻¹) 0 = 0 ∧ (g * a * g⁻¹) 1 = 1 := by
  obtain ⟨P, hP⟩ := exists_fix_of_two hT2
  have hAP : ∀ a ∈ A, a P = P := by
    intro a ha
    refine eq_of_fix_two hTX hT2 hT1 (fun t ht => ?_) hP
    have hc : a⁻¹ * t * a ∈ T := by
      refine (Subgroup.mem_normalizer_iff.1 (hAN ha) _).2 ?_
      have : a * (a⁻¹ * t * a) * a⁻¹ = t := by group
      rw [this]
      exact ht
    have h1 := hP _ hc
    simp only [Equiv.Perm.mul_apply] at h1
    calc t (a P) = a (a⁻¹ (t (a P))) := by simp
      _ = a P := by rw [h1]
  obtain ⟨P', hP'P, hAP'⟩ := exists_fix_ne_of_three hA3 hAP
  obtain ⟨g, hg, hg0, hg1⟩ := U38G_twoTransitive P P' 0 1 (Ne.symm hP'P) (by decide)
  have hi0 : g⁻¹ 0 = P := by rw [← hg0]; simp
  have hi1 : g⁻¹ 1 = P' := by rw [← hg1]; simp
  refine ⟨g, hg, fun a ha => ⟨?_, ?_⟩⟩
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hi0, hAP a ha, hg0]
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hi1, hAP' a ha, hg1]

end M1

@[expose] noncomputable def D0 : Equiv.Perm (Fin 513) := permOfArr 513 d0

section Cert810201

theorem D0_fix01 : D0 0 = 0 ∧ D0 1 = 1 := Certificates.certificate810201.1

theorem D0_cube : D0 ^ 3 = 1 := Certificates.certificate810201.2.1

theorem D0_ne_one : D0 ≠ 1 := Certificates.certificate810201.2.2.1

@[expose] noncomputable def H01 : Subgroup (Equiv.Perm (Fin 513)) := Subgroup.closure (permsA 513 hGens)

section Gamma

theorem D0_mem : D0 ∈ U38G := Certificates.certificate810201.2.2.2.1

theorem H01_eq : H01 = stab2 U38G 0 1 :=
  Subgroup.eq_of_le_of_card_ge Certificates.certificate810201.2.2.2.2.1 (le_of_eq (by
    rw [card_stab2_U38G (P := 0) (Q := 1) (by decide), H01, Certificates.certificate810201.2.2.2.2.2.1]))

theorem elemAb_fix01 {E : Subgroup (Equiv.Perm (Fin 513))} (hEG : E ≤ U38G)
    (hfix : ∀ e ∈ E, e 0 = 0 ∧ e 1 = 1) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 9 ∧ (Nat.card E = 9 → D0 ∈ E) := by
  classical
  have hck := Certificates.certificate810201.2.2.2.2.2.2.1
  have hEH : E ≤ H01 := by
    rw [H01_eq]
    intro e he
    exact mem_stab2.2 ⟨hEG he, hfix e he⟩
  have hD0H : D0 ∈ H01 := by
    rw [H01_eq]
    exact mem_stab2.2 ⟨D0_mem, D0_fix01⟩
  have hcardE : Nat.card E = (E : Set (Equiv.Perm (Fin 513))).ncard := (Nat.card_coe_set_eq _).symm
  by_cases hsmall : ∀ x ∈ E, x = 1 ∨ x = D0 ∨ x = D0 * D0
  · have hle : Nat.card E ≤ 3 := by
      rw [hcardE]
      calc (E : Set (Equiv.Perm (Fin 513))).ncard
          ≤ ((({1, D0, D0 * D0} : Finset (Equiv.Perm (Fin 513))) : Set (Equiv.Perm (Fin 513)))).ncard := by
            refine Set.ncard_le_ncard (fun y hy => ?_) (Finset.finite_toSet _)
            rw [Finset.mem_coe]
            rcases hsmall y hy with rfl | rfl | rfl
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        _ = ({1, D0, D0 * D0} : Finset (Equiv.Perm (Fin 513))).card := Set.ncard_coe_finset _
        _ ≤ 3 := Finset.card_le_three
    exact ⟨by omega, fun h9 => by omega⟩
  push Not at hsmall
  obtain ⟨x, hxE, hx1, hx2, hx3⟩ := hsmall
  obtain ⟨hcd, hlen⟩ := hck x (hEH hxE) (hE.2 _ hxE) hx1 hx2 hx3
  set Sf : Set (Equiv.Perm (Fin 513)) := {y | y ∈ H01 ∧ y ^ 3 = 1 ∧ x * y = y * x} with hSf
  have hESf : (E : Set (Equiv.Perm (Fin 513))) ⊆ Sf :=
    fun y hy => ⟨hEH hy, hE.2 y hy, ys07_comm_of_elemAb hE hxE hy⟩
  have hEle : Nat.card E ≤ Sf.ncard := by
    rw [hcardE]
    exact Set.ncard_le_ncard hESf (Set.toFinite _)
  refine ⟨hEle.trans hlen, fun h9 => ?_⟩
  have hD0Sf : D0 ∈ Sf := ⟨hD0H, D0_cube, hcd⟩
  have heq : (E : Set (Equiv.Perm (Fin 513))) = Sf :=
    Set.eq_of_subset_of_ncard_le hESf (by rw [← hcardE, h9]; exact hlen) (Set.toFinite _)
  have hD0E : D0 ∈ (E : Set (Equiv.Perm (Fin 513))) := by
    rw [heq]
    exact hD0Sf
  exact hD0E

end Gamma

@[expose] noncomputable def L28 : Subgroup (Equiv.Perm (Fin 513)) := Subgroup.closure (permsA 513 #[la, lb])

theorem L28_card : Nat.card L28 = 504 := Certificates.certificate810201.2.2.2.2.2.2.2.2.1

theorem L28_simple : IsSimpleGroup L28 := Certificates.certificate810201.2.2.2.2.2.2.2.2.2.1

theorem L28_nonabelian : ∃ a b : L28, a * b ≠ b * a := by
  haveI := L28_simple
  by_contra h
  push Not at h
  letI : CommGroup L28 := { (inferInstance : Group L28) with mul_comm := h }
  have hp : (Nat.card L28).Prime := IsSimpleGroup.prime_card
  rw [L28_card] at hp
  norm_num at hp

section CentralizerD0

theorem L28_le : L28 ≤ Subgroup.centralizer ({D0} : Set (Equiv.Perm (Fin 513))) ⊓ X' :=
  Certificates.certificate810201.2.2.2.2.2.2.2.1

theorem le_normalizer_L28 :
    Subgroup.centralizer ({D0} : Set (Equiv.Perm (Fin 513))) ⊓ X' ≤ Subgroup.normalizer (L28 : Set _) :=
  Certificates.certificate810201.2.2.2.2.2.2.2.2.2.2.1

theorem glaPLayer_centralizer_D0 :
    GLAPLayer 3 (Subgroup.centralizer ({D0} : Set (Equiv.Perm (Fin 513))) ⊓ X') ≠ ⊥ := by
  haveI := L28_simple
  have hn : (L28.subgroupOf (Subgroup.centralizer ({D0} : Set (Equiv.Perm (Fin 513))) ⊓ X')).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer L28_le).2 le_normalizer_L28
  have hle := CFSG.HardMathSupport.Solomon.Coordinator.le_glaPLayer_of_normal_simple Nat.prime_three L28_le hn
    L28_nonabelian (by rw [L28_card]; norm_num)
  intro hbot
  rw [hbot] at hle
  have := Subgroup.card_le_of_le hle
  rw [L28_card, Subgroup.card_bot] at this
  omega

end CentralizerD0

end Cert810201

end CFSG.LocalAnalysis.GLTheoremA.U38ThreeModel
