module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.ConjFacts

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Open Subgroup
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

lemma conjSub_mul (a b : Γ) (H : Subgroup Γ) :
    conjSub a (conjSub b H) = conjSub (a * b) H := by
  have hf : (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
      (MulAut.conj (a * b)).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [conjSub, conjSub, conjSub, Subgroup.map_map, hf]

private lemma mem_normalizer_self {H : Subgroup Γ} {g : Γ} (hg : g ∈ H) :
    g ∈ normalizer (H : Set Γ) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)
  · intro hx
    have := H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg
    simpa [mul_assoc] using this

private lemma mem_normalizer_inf {A B : Subgroup Γ} {g : Γ}
    (hA : g ∈ normalizer (A : Set Γ)) (hB : g ∈ normalizer (B : Set Γ)) :
    g ∈ normalizer ((A ⊓ B : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_set_normalizer_iff] at hA hB ⊢
  intro x
  constructor
  · intro hx
    exact ⟨(hA x).mp hx.1, (hB x).mp hx.2⟩
  · intro hx
    exact ⟨(hA x).mpr hx.1, (hB x).mpr hx.2⟩

private lemma mem_normalizer_centralizer {X : Subgroup Γ} {g : Γ}
    (hg : g ∈ normalizer (X : Set Γ)) :
    g ∈ normalizer ((Subgroup.centralizer (X : Set Γ) : Subgroup Γ) : Set Γ) := by
  have fwd : ∀ {h x : Γ}, h ∈ normalizer (X : Set Γ) →
      x ∈ Subgroup.centralizer (X : Set Γ) →
      h * x * h⁻¹ ∈ Subgroup.centralizer (X : Set Γ) := by
    intro h x hh hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    have hy' : h⁻¹ * y * h ∈ X := (Subgroup.mem_set_normalizer_iff.mp hh (h⁻¹ * y * h)).mpr (by
      show h * (h⁻¹ * y * h) * h⁻¹ ∈ X
      simpa [mul_assoc] using hy)
    have hcomm := hx (h⁻¹ * y * h) hy'
    calc y * (h * x * h⁻¹) = h * ((h⁻¹ * y * h) * x) * h⁻¹ := by group
      _ = h * (x * (h⁻¹ * y * h)) * h⁻¹ := by rw [hcomm]
      _ = (h * x * h⁻¹) * y := by group
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · exact fwd hg
  · intro hx
    have hginv : g⁻¹ ∈ normalizer (X : Set Γ) := inv_mem hg
    have := fwd hginv hx
    simpa [mul_assoc] using this

theorem card_invols_mul {L : Subgroup Γ} {u : Γ} (hu : u ∈ invols L)
    (hconj : ∀ v ∈ invols L, ∃ l ∈ L, v = l * u * l⁻¹) :
    Nat.card (invols L) * Nat.card (centEl L u) = Nat.card L := by
  classical
  letI : MulAction ↥L Γ := MulAction.compHom Γ (MulAut.conj.comp L.subtype)
  have hsmul : ∀ (l : ↥L) (x : Γ), l • x = (l : Γ) * x * (l : Γ)⁻¹ := by
    intro l x
    change (MulAut.conj (l : Γ)) x = _
    rw [MulAut.conj_apply]
  have horbit : MulAction.orbit ↥L u = invols L := by
    ext v
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨l, rfl⟩
      rw [hsmul]
      refine ⟨L.mul_mem (L.mul_mem l.2 hu.1) (L.inv_mem l.2), ?_⟩
      have hord := SemiconjBy.orderOf_eq (l : Γ)
        (show SemiconjBy (l : Γ) u ((l : Γ) * u * (l : Γ)⁻¹) from by
          show (l : Γ) * u = ((l : Γ) * u * (l : Γ)⁻¹) * (l : Γ)
          group)
      rw [← hord]
      exact hu.2
    · intro hv
      obtain ⟨l, hl, hvl⟩ := hconj v hv
      exact ⟨⟨l, hl⟩, by rw [hsmul]; exact hvl.symm⟩
  have hstab : MulAction.stabilizer ↥L u = (centEl L u).subgroupOf L := by
    ext l
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    change l • u = u ↔ (l : Γ) ∈ centEl L u
    rw [hsmul, centEl, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨l.2, ?_⟩
      calc (l : Γ) * u = ((l : Γ) * u * (l : Γ)⁻¹) * (l : Γ) := by group
        _ = u * (l : Γ) := by rw [h]
    · rintro ⟨-, hcomm⟩
      calc (l : Γ) * u * (l : Γ)⁻¹ = (u * (l : Γ)) * (l : Γ)⁻¹ := by rw [hcomm]
        _ = u := by group
  have hstabcard : Nat.card (MulAction.stabilizer ↥L u) = Nat.card (centEl L u) := by
    rw [hstab]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show centEl L u ≤ L from inf_le_left)).toEquiv
  have horbitcard : (MulAction.orbit ↥L u).ncard = Nat.card (invols L) := by
    rw [horbit, ← Nat.card_coe_set_eq]
  have hidx := MulAction.index_stabilizer ↥L u
  have hcard := Subgroup.card_mul_index (H := MulAction.stabilizer ↥L u)
  rw [hidx] at hcard
  rw [hstabcard, horbitcard] at hcard
  exact (mul_comm (Nat.card (invols L)) (Nat.card (centEl L u))).trans hcard

theorem eq_of_card_two_mul {L C T : Subgroup Γ} (hΓ : Nat.card Γ = 2 * Nat.card L)
    (hT : T ≤ C) (hcard : Nat.card T = 2 * Nat.card (L ⊓ C : Subgroup Γ)) : T = C := by
  have hLindex : L.index = 2 := by
    rw [Subgroup.index_eq_card_div, hΓ, mul_comm 2 (Nat.card L),
      Nat.mul_div_cancel_left _ Nat.card_pos]
  refine Subgroup.eq_of_le_of_card_ge hT ?_
  rw [hcard]
  have hne : L.relIndex (⊤ : Subgroup Γ) ≠ 0 := by
    rw [Subgroup.relIndex_top_right]
    intro h0
    have h := Subgroup.card_mul_index (H := L)
    rw [h0, mul_zero] at h
    exact Nat.card_pos.ne' h.symm
  have hle : L.relIndex C ≤ 2 := by
    calc L.relIndex C ≤ L.relIndex (⊤ : Subgroup Γ) :=
          Subgroup.relIndex_le_of_le_right le_top hne
      _ = L.index := Subgroup.relIndex_top_right L
      _ = 2 := hLindex
  calc Nat.card C = L.relIndex C * Nat.card (L ⊓ C : Subgroup Γ) :=
        (Subgroup.relIndex_mul_card (H := L) (K := C)).symm
    _ ≤ 2 * Nat.card (L ⊓ C : Subgroup Γ) := Nat.mul_le_mul_right _ hle

theorem sup_closure_eq_top {L : Subgroup Γ} {σ : Γ} (hΓ : Nat.card Γ = 2 * Nat.card L)
    (hσ : σ ∉ L) : L ⊔ closure {σ} = ⊤ := by
  have hLindex : L.index = 2 := by
    rw [Subgroup.index_eq_card_div, hΓ, mul_comm 2 (Nat.card L),
      Nat.mul_div_cancel_left _ Nat.card_pos]
  have hmem : σ ∈ L ⊔ closure {σ} :=
    Subgroup.mem_sup_right (S := L) (T := closure {σ})
      (Subgroup.subset_closure (Set.mem_singleton σ))
  have hne : L ⊔ closure {σ} ≠ L := by
    intro h
    exact hσ (h ▸ hmem)
  have hdvd : (L ⊔ closure {σ}).index ∣ L.index := Subgroup.index_dvd_of_le le_sup_left
  have hpos : (L ⊔ closure {σ}).index ≠ 0 := by
    intro h0
    have h := Subgroup.card_mul_index (H := (L ⊔ closure {σ} : Subgroup Γ))
    rw [h0, mul_zero] at h
    exact Nat.card_pos.ne' h.symm
  have hidx2 : (L ⊔ closure {σ}).index ≠ 2 := by
    intro h2
    have hcard : Nat.card (L ⊔ closure {σ} : Subgroup Γ) = Nat.card L := by
      have h := Subgroup.card_mul_index (H := (L ⊔ closure {σ} : Subgroup Γ))
      rw [h2, hΓ] at h
      omega
    have heq : L = L ⊔ closure {σ} :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq hcard)
    exact hne heq.symm
  have hle : (L ⊔ closure {σ}).index ≤ 2 := by
    rw [hLindex] at hdvd
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hidx1 : (L ⊔ closure {σ}).index = 1 := by omega
  simpa only [Subgroup.index_eq_one] using hidx1

theorem centIn_eq_centIn_centEl {L X : Subgroup Γ} {z : Γ} (hz : z ∈ X) :
    centIn L X = centIn (centEl L z) X := by
  rw [centIn, centIn, centEl]
  have hle : Subgroup.centralizer (X : Set Γ) ≤ Subgroup.centralizer ({z} : Set Γ) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hz)
  apply le_antisymm
  · exact le_inf (inf_le_inf_left L hle) inf_le_right
  · exact le_inf (le_trans inf_le_left inf_le_left) inf_le_right

theorem normIn_eq_normIn_centEl {L X : Subgroup Γ} {z : Γ} (hcen : cen X = zpowers z)
    (h1 : z ≠ 1) (h2 : z * z = 1) : normIn L X = normIn (centEl L z) X := by
  apply le_antisymm
  · intro g hg
    exact ⟨normIn_le_centEl_of_cen hcen h1 h2 hg, hg.2⟩
  · intro g hg
    exact ⟨hg.1.1, hg.2⟩

theorem centEl_inf_eq {L N : Subgroup Γ} (z : Γ) (hN : N ≤ L) : centEl L z ⊓ N = centEl N z := by
  rw [centEl, centEl, inf_assoc, inf_left_comm, inf_eq_right.mpr hN, inf_comm]

theorem mem_normalizer_cen {T : Subgroup Γ} {g : Γ} (hg : g ∈ normalizer (T : Set Γ)) :
    g ∈ normalizer ((cen T : Subgroup Γ) : Set Γ) := by
  have h2 : g ∈ normalizer ((Subgroup.centralizer (T : Set Γ) : Subgroup Γ) : Set Γ) :=
    mem_normalizer_centralizer hg
  have hcen : cen T = T ⊓ Subgroup.centralizer (T : Set Γ) := rfl
  rw [hcen]
  exact mem_normalizer_inf hg h2

theorem normIn_cen_le {L B : Subgroup Γ} (hcen : centIn L (cen B) = B) :
    normIn L (cen B) ≤ normIn L B := by
  intro g hg
  obtain ⟨hgL, hgN⟩ := hg
  refine ⟨hgL, ?_⟩
  have hgLnorm : g ∈ normalizer (L : Set Γ) := mem_normalizer_self hgL
  have hgCnorm : g ∈ normalizer
      ((Subgroup.centralizer (cen B : Set Γ) : Subgroup Γ) : Set Γ) :=
    mem_normalizer_centralizer hgN
  have hB : B = L ⊓ Subgroup.centralizer (cen B : Set Γ) := hcen.symm
  rw [hB]
  exact mem_normalizer_inf hgLnorm hgCnorm

theorem normIn_le_normIn_cen {L B : Subgroup Γ} : normIn L B ≤ normIn L (cen B) := by
  intro g hg
  exact ⟨hg.1, mem_normalizer_cen hg.2⟩

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof
