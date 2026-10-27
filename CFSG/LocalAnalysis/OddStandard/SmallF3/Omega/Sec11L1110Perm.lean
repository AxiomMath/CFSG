module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110Q8

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {E : Type} [Group E] {z : E} {Q1 Q2 : Subgroup E}

private lemma conj_sq {n x : E} (hnz : n * z * n⁻¹ = z) (hx : x * x = z) :
    (n * x * n⁻¹) * (n * x * n⁻¹) = z := by
  calc (n * x * n⁻¹) * (n * x * n⁻¹) = n * (x * x) * n⁻¹ := by group
    _ = n * z * n⁻¹ := by rw [hx]
    _ = z := hnz

private lemma sq_mem (P : Sec11Q8Pair z Q1 Q2) {x : E} (hx : x ∈ Q1 ⊔ Q2)
    (hxx : x * x = z) : x ∈ Q1 ∨ x ∈ Q2 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := P.exists_mul_of_mem_sup hx
  have haa : a * a ∈ zpowers z := (P.elem1 a ha a ha).2
  have hbb : b * b ∈ zpowers z := (P.elem2 b hb b hb).2
  have hmul : (a * a) * (b * b) = z := by
    have h : (a * b) * (a * b) = (a * a) * (b * b) := by
      calc (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [P.comm a ha b hb]
        _ = (a * a) * (b * b) := by group
    rw [← h]; exact hxx
  rcases P.mem_zpowers_iff.mp haa with ha1 | haz
  · rcases P.mem_zpowers_iff.mp hbb with hb1 | hbz
    · exfalso
      rw [ha1, hb1, one_mul] at hmul
      exact P.z_ne hmul.symm
    · right
      exact mul_mem ((Subgroup.zpowers_le.mpr P.z_mem2) (P.invol1 a ha ha1)) hb
  · rcases P.mem_zpowers_iff.mp hbb with hb1 | hbz
    · left
      exact mul_mem ha ((Subgroup.zpowers_le.mpr P.z_mem1) (P.invol2 b hb hb1))
    · exfalso
      rw [haz, hbz] at hmul
      rw [P.z_sq] at hmul
      exact P.z_ne hmul.symm

private lemma conj_le_of_gen {H Qj : Subgroup E} {s : Set E} (f : E →* E)
    (hgen : H = Subgroup.closure s) (hs : ∀ y ∈ s, f y ∈ Qj) :
    ∀ x ∈ H, f x ∈ Qj := by
  have hle : Subgroup.closure s ≤ Qj.comap f := by
    rw [Subgroup.closure_le]
    intro y hy
    exact hs y hy
  intro x hx
  rw [hgen] at hx
  exact hle hx

private lemma same_side (P : Sec11Q8Pair z Q1 Q2) {u v : E}
    (hu : u ∈ Q1 ∨ u ∈ Q2) (hv : v ∈ Q1 ∨ v ∈ Q2) (hne : u * v ≠ v * u) :
    (u ∈ Q1 ∧ v ∈ Q1) ∨ (u ∈ Q2 ∧ v ∈ Q2) := by
  rcases hu with hu1 | hu2
  · rcases hv with hv1 | hv2
    · exact Or.inl ⟨hu1, hv1⟩
    · exact absurd (P.comm u hu1 v hv2) hne
  · rcases hv with hv1 | hv2
    · exact absurd (P.comm v hv1 u hu2).symm hne
    · exact Or.inr ⟨hu2, hv2⟩

private lemma false_of_conj_le_same (P : Sec11Q8Pair z Q1 Q2) {n : E} {Qj : Subgroup E}
    (hj : Qj = Q1 ∨ Qj = Q2)
    (h1 : ∀ x ∈ Q1, n * x * n⁻¹ ∈ Qj) (h2 : ∀ x ∈ Q2, n * x * n⁻¹ ∈ Qj) : False := by
  have hcardj : Nat.card ↥Qj = 8 := by
    rcases hj with rfl | rfl
    · exact P.card1
    · exact P.card2
  haveI hfinj : Finite ↥Qj := Nat.finite_of_card_ne_zero (by rw [hcardj]; norm_num)
  have hinj : Function.Injective (MulAut.conj n).toMonoidHom := (MulAut.conj n).injective
  have hmap1 : Q1.map (MulAut.conj n).toMonoidHom ≤ Qj := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact h1 y hy
  have hmap2 : Q2.map (MulAut.conj n).toMonoidHom ≤ Qj := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact h2 y hy
  have hcard1 : Nat.card ↥(Q1.map (MulAut.conj n).toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj n).toMonoidHom) hinj, P.card1]
  have hcard2 : Nat.card ↥(Q2.map (MulAut.conj n).toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj n).toMonoidHom) hinj, P.card2]
  have heq1 : Q1.map (MulAut.conj n).toMonoidHom = Qj :=
    Subgroup.eq_of_le_of_card_ge hmap1 (by rw [hcardj, hcard1])
  have heq2 : Q2.map (MulAut.conj n).toMonoidHom = Qj :=
    Subgroup.eq_of_le_of_card_ge hmap2 (by rw [hcardj, hcard2])
  have hmap_eq : Q1.map (MulAut.conj n).toMonoidHom =
      Q2.map (MulAut.conj n).toMonoidHom := heq1.trans heq2.symm
  have hQ : Q1 = Q2 := Subgroup.map_injective hinj hmap_eq
  obtain ⟨a0, ha0, hna0⟩ := P.exists_outside1
  exact hna0 (P.inf a0 ha0 ((le_of_eq hQ) ha0))

theorem Sec11Q8Pair.perm (P : Sec11Q8Pair z Q1 Q2) {n : E} (hnz : n * z * n⁻¹ = z)
    (hn : ∀ x ∈ Q1 ⊔ Q2, n * x * n⁻¹ ∈ Q1 ⊔ Q2) :
    ((∀ a ∈ Q1, n * a * n⁻¹ ∈ Q1) ∧ ∀ a ∈ Q2, n * a * n⁻¹ ∈ Q2) ∨
      ((∀ a ∈ Q1, n * a * n⁻¹ ∈ Q2) ∧ ∀ a ∈ Q2, n * a * n⁻¹ ∈ Q1) := by
  obtain ⟨a, ha, b, hb, hab, hQ1⟩ := P.exists_gen1
  obtain ⟨a', ha', b', hb', hab', hQ2⟩ := (P.symm).exists_gen1
  have hne1 : a * b ≠ b * a := P.comm_ne_of_commutator_eq_z ha hb hab
  have hne2 : a' * b' ≠ b' * a' := P.symm.comm_ne_of_commutator_eq_z ha' hb' hab'
  have ha_z : a ∉ zpowers z := (P.not_mem_zpowers_of_comm_ne ha hb hne1).1
  have hb_z : b ∉ zpowers z := (P.not_mem_zpowers_of_comm_ne ha hb hne1).2
  have ha'_z : a' ∉ zpowers z := (P.symm.not_mem_zpowers_of_comm_ne ha' hb' hne2).1
  have hb'_z : b' ∉ zpowers z := (P.symm.not_mem_zpowers_of_comm_ne ha' hb' hne2).2
  have haa : a * a = z := P.sq_eq1 ha ha_z
  have hbb : b * b = z := P.sq_eq1 hb hb_z
  have haa' : a' * a' = z := (P.symm).sq_eq1 ha' ha'_z
  have hbb' : b' * b' = z := (P.symm).sq_eq1 hb' hb'_z
  have ha_in : n * a * n⁻¹ ∈ Q1 ∨ n * a * n⁻¹ ∈ Q2 :=
    sq_mem P (hn a (Subgroup.mem_sup_left ha)) (conj_sq hnz haa)
  have hb_in : n * b * n⁻¹ ∈ Q1 ∨ n * b * n⁻¹ ∈ Q2 :=
    sq_mem P (hn b (Subgroup.mem_sup_left hb)) (conj_sq hnz hbb)
  have ha'_in : n * a' * n⁻¹ ∈ Q1 ∨ n * a' * n⁻¹ ∈ Q2 :=
    sq_mem P (hn a' (Subgroup.mem_sup_right ha')) (conj_sq hnz haa')
  have hb'_in : n * b' * n⁻¹ ∈ Q1 ∨ n * b' * n⁻¹ ∈ Q2 :=
    sq_mem P (hn b' (Subgroup.mem_sup_right hb')) (conj_sq hnz hbb')
  have hne1' : (n * a * n⁻¹) * (n * b * n⁻¹) ≠ (n * b * n⁻¹) * (n * a * n⁻¹) := by
    intro hc
    apply hne1
    have h1 : a * b = n⁻¹ * ((n * a * n⁻¹) * (n * b * n⁻¹)) * n := by group
    rw [h1, hc]
    group
  have hne2' : (n * a' * n⁻¹) * (n * b' * n⁻¹) ≠ (n * b' * n⁻¹) * (n * a' * n⁻¹) := by
    intro hc
    apply hne2
    have h1 : a' * b' = n⁻¹ * ((n * a' * n⁻¹) * (n * b' * n⁻¹)) * n := by group
    rw [h1, hc]
    group
  have hside1 := same_side P ha_in hb_in hne1'
  have hside2 := same_side P ha'_in hb'_in hne2'
  rcases hside1 with ⟨haQ1, hbQ1⟩ | ⟨haQ2, hbQ2⟩
  · have h1map : ∀ x ∈ Q1, n * x * n⁻¹ ∈ Q1 :=
      conj_le_of_gen (s := ({a, b} : Set E)) (MulAut.conj n).toMonoidHom hQ1 (by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact haQ1
        · exact hbQ1)
    rcases hside2 with ⟨ha'Q1, hb'Q1⟩ | ⟨ha'Q2, hb'Q2⟩
    · have h2map : ∀ x ∈ Q2, n * x * n⁻¹ ∈ Q1 :=
        conj_le_of_gen (s := ({a', b'} : Set E)) (MulAut.conj n).toMonoidHom hQ2 (by
          intro y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl
          · exact ha'Q1
          · exact hb'Q1)
      exact (false_of_conj_le_same P (Or.inl rfl) h1map h2map).elim
    · have h2map : ∀ x ∈ Q2, n * x * n⁻¹ ∈ Q2 :=
        conj_le_of_gen (s := ({a', b'} : Set E)) (MulAut.conj n).toMonoidHom hQ2 (by
          intro y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl
          · exact ha'Q2
          · exact hb'Q2)
      exact Or.inl ⟨h1map, h2map⟩
  · have h1map : ∀ x ∈ Q1, n * x * n⁻¹ ∈ Q2 :=
      conj_le_of_gen (s := ({a, b} : Set E)) (MulAut.conj n).toMonoidHom hQ1 (by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact haQ2
        · exact hbQ2)
    rcases hside2 with ⟨ha'Q1, hb'Q1⟩ | ⟨ha'Q2, hb'Q2⟩
    · have h2map : ∀ x ∈ Q2, n * x * n⁻¹ ∈ Q1 :=
        conj_le_of_gen (s := ({a', b'} : Set E)) (MulAut.conj n).toMonoidHom hQ2 (by
          intro y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl
          · exact ha'Q1
          · exact hb'Q1)
      exact Or.inr ⟨h1map, h2map⟩
    · have h2map : ∀ x ∈ Q2, n * x * n⁻¹ ∈ Q2 :=
        conj_le_of_gen (s := ({a', b'} : Set E)) (MulAut.conj n).toMonoidHom hQ2 (by
          intro y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl
          · exact ha'Q2
          · exact hb'Q2)
      exact (false_of_conj_le_same P (Or.inr rfl) h1map h2map).elim

end CFSG.OddStandard.SmallF3.Omega
