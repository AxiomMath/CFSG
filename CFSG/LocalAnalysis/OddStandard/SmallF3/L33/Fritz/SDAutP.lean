module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsAutData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDPresent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDH8

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SDAutP

open CFSG Subgroup Equiv CFSG.ComponentClassification.HSFLit CFSG.OddStandard.SmallF3.L33
open CFSG.OddStandard.SmallF3.L33.KD.SDPresent

variable {L : Type} [Group L]

@[expose] def inn (L : Type) [Group L] : Subgroup (MulAut L) :=
  (MulAut.conj : L →* MulAut L).range

@[expose] def Pin (F : FritzData L) : Subgroup (MulAut L) :=
  closure ({MulAut.conj F.x, MulAut.conj F.y} : Set (MulAut L))

@[expose] def P (F : FritzData L) : Subgroup (MulAut L) :=
  closure ({MulAut.conj F.x, MulAut.conj F.y, F.k} : Set (MulAut L))

private lemma mulAut_conj_mul (φ : MulAut L) (a : L) :
    φ * MulAut.conj a * φ⁻¹ = MulAut.conj (φ a) := by
  ext u
  simp [MulAut.conj_apply, map_mul, map_inv]

private lemma card_S16 : Nat.card (SD.S16 : Set (Perm (ZMod 8))) = 16 := by
  have hset : (SD.S16 : Set (Perm (ZMod 8))) =
      (fun p : (ZMod 8)ˣ × ZMod 8 => aff8 p.1 p.2) ''
        {p : (ZMod 8)ˣ × ZMod 8 | dbit8 p.2 = fbit8 p.1} := by
    ext g
    constructor
    · rintro ⟨u, b, rfl, h⟩
      exact ⟨(u, b), h, rfl⟩
    · rintro ⟨⟨u, b⟩, h, rfl⟩
      exact ⟨u, b, rfl, h⟩
  have hcard : Nat.card (SD.S16 : Set (Perm (ZMod 8))) =
      Nat.card {p : (ZMod 8)ˣ × ZMod 8 | dbit8 p.2 = fbit8 p.1} := by
    rw [hset]
    exact Nat.card_image_of_injective
      (f := fun p : (ZMod 8)ˣ × ZMod 8 => aff8 p.1 p.2)
      (fun p q h => by
        obtain ⟨h1, h2⟩ := aff8_injective h
        exact Prod.ext h1 h2) _
  rw [hcard, Nat.card_eq_fintype_card]
  decide

theorem Pin_le_P (F : FritzData L) : Pin F ≤ P F := by
  exact Subgroup.closure_mono (by rintro x (rfl | rfl) <;> simp)

theorem card_P (F : FritzData L) : Nat.card (P F) = 32 :=
  F.card_T

theorem rel (F : FritzData L) : Rel (MulAut.conj F.x) (MulAut.conj F.y) F.k := by
  have hk : ∀ a : L, F.k * MulAut.conj a * F.k⁻¹ = MulAut.conj (F.k a) :=
    fun a => mulAut_conj_mul F.k a
  have hx5 : F.x * F.x ^ 4 = F.x ^ 5 := by
    rw [show (5 : ℕ) = 1 + 4 by norm_num, pow_add, pow_one]
  refine ⟨?_, ?_, F.k_sq, ?_, ?_, ?_⟩
  · rw [← map_pow, F.x_pow_eight, map_one]
  · rw [← map_pow, F.y_sq, map_one]
  · simp only [← map_mul, ← map_inv, F.y_conj, map_pow]
  · rw [hk, F.k_x, hx5, map_pow]
  · have h := hk F.y
    rw [F.k_y] at h
    have h' := congrArg (fun x => x * F.k) h
    simpa [mul_assoc] using h'

theorem exists_phi (F : FritzData L) : ∃ Φ : ↥(P F) ≃* ↥H8,
    (Φ (genA (MulAut.conj F.x) (MulAut.conj F.y) F.k) : Perm (ZMod 8)) = aff8 u5 1 ∧
      (Φ (genB (MulAut.conj F.x) (MulAut.conj F.y) F.k) : Perm (ZMod 8)) = y8 ∧
        (Φ (genC (MulAut.conj F.x) (MulAut.conj F.y) F.k) : Perm (ZMod 8)) = k8 :=
  exists_mulEquiv_H8 (rel F) F.card_T

@[expose] noncomputable def phi (F : FritzData L) : ↥(P F) ≃* ↥H8 :=
  (exists_phi F).choose

theorem phi_genA (F : FritzData L) :
    (phi F (genA (MulAut.conj F.x) (MulAut.conj F.y) F.k) : Perm (ZMod 8)) = aff8 u5 1 :=
  (exists_phi F).choose_spec.1

theorem phi_genB (F : FritzData L) :
    (phi F (genB (MulAut.conj F.x) (MulAut.conj F.y) F.k) : Perm (ZMod 8)) = y8 :=
  (exists_phi F).choose_spec.2.1

theorem phi_genC (F : FritzData L) :
    (phi F (genC (MulAut.conj F.x) (MulAut.conj F.y) F.k) : Perm (ZMod 8)) = k8 :=
  (exists_phi F).choose_spec.2.2

theorem card_Pin (F : FritzData L) (hinj : Function.Injective (MulAut.conj : L →* MulAut L)) :
    Nat.card (Pin F) = 16 := by
  have hmap : Pin F = (closure ({F.x, F.y} : Set L)).map (MulAut.conj : L →* MulAut L) := by
    simp only [Pin, MonoidHom.map_closure, Set.image_pair]
  rw [hmap, Subgroup.card_map_of_injective hinj, F.card_xy]

theorem Pin_eq_inf (F : FritzData L) (hinj : Function.Injective (MulAut.conj : L →* MulAut L)) :
    Pin F = P F ⊓ inn L := by
  have hforward : Pin F ≤ P F ⊓ inn L := by
    refine le_inf (Pin_le_P F) ?_
    rw [Pin]
    apply (Subgroup.closure_le (inn L)).2
    rintro x (rfl | rfl)
    · exact MonoidHom.mem_range.2 ⟨F.x, rfl⟩
    · exact MonoidHom.mem_range.2 ⟨F.y, rfl⟩
  haveI hfin : Finite ↥(P F) :=
    Nat.finite_of_card_ne_zero (by rw [card_P F]; norm_num)
  have hdvd : Nat.card ↥(P F ⊓ inn L) ∣ Nat.card (P F) := by
    have h := Subgroup.card_subgroup_dvd_card ((P F ⊓ inn L).subgroupOf (P F))
    rwa [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : P F ⊓ inn L ≤ P F)).toEquiv] at h
  have hne : Nat.card ↥(P F ⊓ inn L) ≠ Nat.card (P F) := by
    intro hcard
    have heq : P F ⊓ inn L = P F :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq hcard.symm)
    have hkP : F.k ∈ P F := Subgroup.subset_closure (by simp)
    have hkin : F.k ∈ inn L := by
      have : F.k ∈ P F ⊓ inn L := by rw [heq]; exact hkP
      exact this.2
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 hkin
    exact F.k_outer ⟨a, fun u => by
      have h2 := congrArg (fun f : MulAut L => f u) ha
      simp only [MulAut.conj_apply] at h2
      exact h2.symm⟩
  have hle16 : Nat.card ↥(P F ⊓ inn L) ≤ 16 := by
    rw [card_P F] at hne
    rcases hdvd with ⟨c, hc⟩
    rw [card_P F] at hc
    have hcne : c ≠ 1 := by
      intro hc1
      rw [hc1, mul_one] at hc
      exact hne hc.symm
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · rw [h, mul_zero] at hc
        exact absurd hc (by norm_num)
      · exact h
    have hc2 : 2 ≤ c := by omega
    have hmul : Nat.card ↥(P F ⊓ inn L) * 2 ≤ Nat.card ↥(P F ⊓ inn L) * c :=
      Nat.mul_le_mul_left _ hc2
    rw [← hc] at hmul
    omega
  have hcardle : Nat.card ↥(P F ⊓ inn L) ≤ Nat.card (Pin F) := by
    rw [card_Pin F hinj]
    exact hle16
  apply le_antisymm hforward
  have hle_Q : (Pin F).subgroupOf (P F) ≤ (P F ⊓ inn L).subgroupOf (P F) :=
    Subgroup.subgroupOf_mono (P F) hforward
  have hcardQ : Nat.card ((P F ⊓ inn L).subgroupOf (P F)) ≤
      Nat.card ((Pin F).subgroupOf (P F)) := by
    rw [Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (inf_le_left : P F ⊓ inn L ≤ P F)).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Pin_le_P F)).toEquiv]
    exact hcardle
  have heq : (Pin F).subgroupOf (P F) = (P F ⊓ inn L).subgroupOf (P F) :=
    Subgroup.eq_of_le_of_card_ge hle_Q hcardQ
  intro g hg
  have hgm : (⟨g, hg.1⟩ : ↥(P F)) ∈ (Pin F).subgroupOf (P F) := by
    rw [heq]
    exact Subgroup.mem_subgroupOf.2 hg
  exact Subgroup.mem_subgroupOf.1 hgm

private theorem subgroupOf_Pin_eq_comap (F : FritzData L)
    (hinj : Function.Injective (MulAut.conj : L →* MulAut L)) :
    (Pin F).subgroupOf (P F) =
      SD.S16.comap (H8.subtype.comp (phi F).toMonoidHom : ↥(P F) →* Perm (ZMod 8)) := by
  let ψ : ↥(P F) →* Perm (ZMod 8) := H8.subtype.comp (phi F).toMonoidHom
  change (Pin F).subgroupOf (P F) = SD.S16.comap ψ
  haveI hfin : Finite ↥(P F) :=
    Nat.finite_of_card_ne_zero (by rw [card_P F]; norm_num)
  have hmain : ∀ y (hy : y ∈ closure ({MulAut.conj F.x, MulAut.conj F.y} : Set (MulAut L)))
      (hyP : y ∈ P F), (⟨y, hyP⟩ : ↥(P F)) ∈ SD.S16.comap ψ := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      intro hzP
      rcases hz with rfl | rfl
      · rw [Subgroup.mem_comap]
        change (phi F (⟨MulAut.conj F.x, hzP⟩ : ↥(P F)) : Perm (ZMod 8)) ∈ SD.S16
        have hz : (⟨MulAut.conj F.x, hzP⟩ : ↥(P F)) =
            genA (MulAut.conj F.x) (MulAut.conj F.y) F.k := Subtype.ext rfl
        rw [hz, phi_genA]
        exact ⟨u5, 1, rfl, by decide⟩
      · rw [Subgroup.mem_comap]
        change (phi F (⟨MulAut.conj F.y, hzP⟩ : ↥(P F)) : Perm (ZMod 8)) ∈ SD.S16
        have hz : (⟨MulAut.conj F.y, hzP⟩ : ↥(P F)) =
            genB (MulAut.conj F.x) (MulAut.conj F.y) F.k := Subtype.ext rfl
        rw [hz, phi_genB]
        exact ⟨-1, 0, rfl, by decide⟩
    | one =>
      intro h1P
      have h1 : (⟨1, h1P⟩ : ↥(P F)) = 1 := Subtype.ext rfl
      rw [h1]
      exact (SD.S16.comap ψ).one_mem
    | mul x y hx hy ihx ihy =>
      intro hxyP
      have hxP : x ∈ P F := Pin_le_P F hx
      have hyP : y ∈ P F := Pin_le_P F hy
      have h : (⟨x, hxP⟩ * ⟨y, hyP⟩ : ↥(P F)) ∈ SD.S16.comap ψ :=
        (SD.S16.comap ψ).mul_mem (ihx hxP) (ihy hyP)
      have he : (⟨x, hxP⟩ * ⟨y, hyP⟩ : ↥(P F)) = ⟨x * y, hxyP⟩ := Subtype.ext (by simp)
      rwa [he] at h
    | inv x hx ih =>
      intro hxP
      have hxP' : x ∈ P F := Pin_le_P F hx
      have h : (⟨x, hxP'⟩ : ↥(P F))⁻¹ ∈ SD.S16.comap ψ :=
        (SD.S16.comap ψ).inv_mem (ih hxP')
      have he : (⟨x, hxP'⟩ : ↥(P F))⁻¹ = ⟨x⁻¹, hxP⟩ := Subtype.ext (by simp)
      rwa [he] at h
  have hcardT : Nat.card (SD.S16.comap ψ) = 16 := by
    have hψ : Function.Injective ψ := by
      intro a b h
      exact (phi F).injective (Subtype.ext h)
    have hsub : (SD.S16 : Set (Perm (ZMod 8))) ⊆ Set.range ψ := by
      intro σ hσ
      exact ⟨(phi F).symm ⟨σ, SD.S16_le_H8 hσ⟩, by
        change ((phi F ((phi F).symm ⟨σ, SD.S16_le_H8 hσ⟩) : ↥H8) : Perm _) = σ
        rw [MulEquiv.apply_symm_apply]⟩
    have hco : (SD.S16.comap ψ : Set ↥(P F)) = ψ ⁻¹' (SD.S16 : Set (Perm (ZMod 8))) := rfl
    have hpre := Nat.card_preimage_of_injective hψ hsub
    rw [← hco] at hpre
    exact hpre.trans card_S16
  have hcardQ : Nat.card ((Pin F).subgroupOf (P F)) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Pin_le_P F)).toEquiv, card_Pin F hinj]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro g hg
    exact hmain g (Subgroup.mem_subgroupOf.1 hg) g.2
  · rw [hcardT, hcardQ]

theorem phi_inner_iff (F : FritzData L)
    (hinj : Function.Injective (MulAut.conj : L →* MulAut L)) (g : ↥(P F)) :
    (g : MulAut L) ∈ inn L ↔ (phi F g : Perm (ZMod 8)) ∈ SD.S16 := by
  have h1 : (g : MulAut L) ∈ inn L ↔ g ∈ (Pin F).subgroupOf (P F) := by
    rw [Subgroup.mem_subgroupOf, Pin_eq_inf F hinj]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  have h2 : g ∈ (Pin F).subgroupOf (P F) ↔ (phi F g : Perm (ZMod 8)) ∈ SD.S16 := by
    rw [subgroupOf_Pin_eq_comap F hinj, Subgroup.mem_comap]
    rfl
  exact h1.trans h2

theorem exists_mem_Pin_phi_eq (F : FritzData L)
    (hinj : Function.Injective (MulAut.conj : L →* MulAut L)) {σ : Perm (ZMod 8)}
    (hσ : σ ∈ SD.S16) : ∃ g : ↥(P F), (g : MulAut L) ∈ Pin F ∧ (phi F g : Perm (ZMod 8)) = σ := by
  have hrange : σ ∈ Set.range
      (H8.subtype.comp (phi F).toMonoidHom : ↥(P F) →* Perm (ZMod 8)) := by
    refine ⟨(phi F).symm ⟨σ, SD.S16_le_H8 hσ⟩, ?_⟩
    change ((phi F ((phi F).symm ⟨σ, SD.S16_le_H8 hσ⟩) : ↥H8) : Perm (ZMod 8)) = σ
    rw [MulEquiv.apply_symm_apply]
  obtain ⟨g, hg⟩ := hrange
  refine ⟨g, ?_, hg⟩
  have hgT : g ∈ SD.S16.comap
      (H8.subtype.comp (phi F).toMonoidHom : ↥(P F) →* Perm (ZMod 8)) := by
    rw [Subgroup.mem_comap, hg]
    exact hσ
  rw [← subgroupOf_Pin_eq_comap F hinj] at hgT
  exact Subgroup.mem_subgroupOf.1 hgT

end CFSG.OddStandard.SmallF3.L33.KD.SDAutP
