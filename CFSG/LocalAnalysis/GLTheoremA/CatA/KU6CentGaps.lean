module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.KU6CentPGU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KU6Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KU6L2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KU6Cent

open CFSG.Open CFSG.Fischer CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA

theorem elemAbelian_comm {G : Type} [Group G] {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E)
    {a b : G} (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := by
  obtain ⟨hc⟩ := hE.1
  exact congrArg Subtype.val (hc.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)

theorem isElemAbelian_of (p : ℕ) {G : Type} [Group G] (E : Subgroup G)
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hp : ∀ x ∈ E, x ^ p = 1) : IsElemAbelian p E :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a.1 a.2 b.1 b.2)⟩⟩, hp⟩

theorem isElemAbelian_map {G H : Type} [Group G] [Group H] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) (f : G →* H) : IsElemAbelian p (E.map f) := by
  refine isElemAbelian_of p (E.map f) ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, elemAbelian_comm hE ha hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]

theorem isElemAbelian_comap {G H : Type} [Group G] [Group H] {p : ℕ} {E : Subgroup H}
    (hE : IsElemAbelian p E) {f : G →* H} (hf : Function.Injective f) :
    IsElemAbelian p (E.comap f) := by
  refine isElemAbelian_of p (E.comap f) ?_ ?_
  · intro a ha b hb
    apply hf
    rw [map_mul, map_mul]
    exact elemAbelian_comm hE (a := f a) (b := f b) ha hb
  · intro a ha
    apply hf
    rw [map_pow, map_one]
    exact hE.2 (f a) ha

@[expose] def KU6CentGapOne : Prop :=
  ∀ B : Gu, (B : GL (Fin 6) F4) ^ 3 = 1 → (QuotientGroup.mk B : PGU6) ≠ 1 →
    ¬ 7 ∣ Nat.card (Subgroup.centralizer ({(QuotientGroup.mk B : PGU6)} : Set PGU6))

@[expose] def KU6CentGapNine : Prop :=
  ∀ (B : Gu) (c : F4ˣ), c ≠ 1 → (B : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c →
    ∀ E : Subgroup PGU6, IsElemAbelian 3 E →
      E ≤ Subgroup.centralizer ({(QuotientGroup.mk B : PGU6)} : Set PGU6) → Nat.card E ≤ 3 ^ 3

theorem s6_bound (hA : KU6CentGapOne) (hB : KU6CentGapNine) (β : MulAut S6) (hβ3 : β ^ 3 = 1)
    (hβ1 : β ≠ 1) (N : Subgroup S6) (hN : N ≤ fixSubgroup β) (h7 : 7 ∣ Nat.card N)
    (E : Subgroup (MulAut S6)) (hE : IsElemAbelian 3 E)
    (hEC : E ≤ Subgroup.centralizer ({β} : Set (MulAut S6))) : Nat.card E ≤ 3 ^ 3 := by
  obtain ⟨B, hBU, ⟨c, hBc⟩, hβB⟩ := exists_unitary_of_pow_three β hβ3
  set g : Gu := ⟨B, hBU⟩ with hgdef
  have hβg : Psi (QuotientGroup.mk g) = β := by
    rw [Psi_mk]
    exact Psi0_eq_of β g hβB
  by_cases hc1 : c = 1
  · exfalso
    subst hc1
    rw [map_one] at hBc
    have hgne : (QuotientGroup.mk g : PGU6) ≠ 1 := by
      intro h1
      apply hβ1
      rw [← hβg, h1, map_one]
    apply hA g hBc hgne
    have hle : N.map iota ≤ Subgroup.centralizer ({(QuotientGroup.mk g : PGU6)} : Set PGU6) := by
      rintro _ ⟨y, hy, rfl⟩
      apply iota_mem_centralizer g y
      have hfix := mem_fixSubgroup.1 (hN hy)
      rw [← hβg, Psi_mk] at hfix
      exact hfix
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective iota_injective] at hdvd
    exact dvd_trans h7 hdvd
  · have hBc' : (g : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c := hBc
    have hsurj : E ≤ Psi.range := by
      intro x hx
      obtain ⟨y, hy⟩ := exists_Psi_of_pow_three x (hE.2 x hx)
      exact ⟨y, hy⟩
    have hmap : (E.comap Psi).map Psi = E := by
      rw [Subgroup.map_comap_eq, inf_eq_right.2 hsurj]
    have hcard : Nat.card (E.comap Psi) = Nat.card E := by
      have h := Subgroup.card_map_of_injective (K := E.comap Psi) Psi_injective
      rw [hmap] at h
      exact h.symm
    have hab : IsElemAbelian 3 (E.comap Psi) := isElemAbelian_comap hE Psi_injective
    have hcent : E.comap Psi ≤ Subgroup.centralizer ({(QuotientGroup.mk g : PGU6)} : Set PGU6) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Psi_injective
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hEC hx)
      rw [map_mul, map_mul, hβg]
      exact h1
    rw [← hcard]
    exact hB g c hc1 hBc' (E.comap Psi) hab hcent

theorem kU6CentL2eightFact_of_gaps (hA : KU6CentGapOne) (hB : KU6CentGapNine) :
    CFSG.LocalAnalysis.GLTheoremA.KU6CentL2eightFact := by
  unfold CFSG.LocalAnalysis.GLTheoremA.KU6CentL2eightFact
  intro S _ _ hS α hα3 hα1 N hN M _ hM E hE hEC
  obtain ⟨e⟩ := HSubT.nonempty_S6_of_isU6two hS
  obtain ⟨-, hcard⟩ := catL2eight_simple_card hM
  have h504 : 504 ∣ Nat.card N := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup M, hcard]
    exact dvd_mul_right _ _
  set β : MulAut S6 := autTr e α with hβdef
  have hβ3 : β ^ 3 = 1 := by
    rw [hβdef, ← map_pow, hα3, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hα1
    apply autTr_injective e
    rw [← hβdef, h, map_one]
  set N6 : Subgroup S6 := N.map e.toMonoidHom with hN6def
  have hN6 : N6 ≤ fixSubgroup β := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : α y = y := mem_fixSubgroup.1 (hN hy)
    show β (e y) = e y
    rw [hβdef, autTr_apply, MulEquiv.symm_apply_apply, hy']
  have h7 : 7 ∣ Nat.card N6 := by
    rw [hN6def, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact dvd_trans (by norm_num) h504
  have hE6C : E.map (autTr e) ≤ Subgroup.centralizer ({β} : Set (MulAut S6)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxα : x * α = α * x := Subgroup.mem_centralizer_singleton_iff.1 (hEC hx)
    rw [Subgroup.mem_centralizer_singleton_iff, hβdef, ← map_mul, ← map_mul, hxα]
  have hcardE6 : Nat.card (E.map (autTr e)) = Nat.card E :=
    Subgroup.card_map_of_injective (autTr_injective e)
  rw [← hcardE6]
  exact s6_bound hA hB β hβ3 hβ1 N6 hN6 h7 (E.map (autTr e)) (isElemAbelian_map hE _) hE6C

end CFSG.LocalAnalysis.GLTheoremA.KU6Cent

end
