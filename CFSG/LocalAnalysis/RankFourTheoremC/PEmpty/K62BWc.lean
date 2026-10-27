module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BComp

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B

open CFSG CFSG.Open CFSG.LocalCores Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.Lemma213 (cjComp mem_cjComp_iff)

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x z : Y}

@[expose] def omega1 (p : ℕ) (P : Subgroup Y) (C : ComponentIndex Y) : Subgroup Y :=
  Subgroup.closure {a : Y | a ∈ P ⊓ C.1 ∧ a ^ p = 1}

theorem omega1_le (p : ℕ) (P : Subgroup Y) (C : ComponentIndex Y) : omega1 p P C ≤ P ⊓ C.1 :=
  (Subgroup.closure_le _).2 fun _ ha => ha.1

theorem map_conj_omega1 (p : ℕ) {g : Y} (hg : g ∈ P) (C : ComponentIndex Y) :
    (omega1 p P C).map (MulAut.conj g).toMonoidHom = omega1 p P (cjComp g C) := by
  unfold omega1
  rw [MonoidHom.map_closure]
  congr 1
  ext a'
  constructor
  · rintro ⟨a, ⟨⟨haP, haC⟩, hap⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact P.mul_mem (P.mul_mem hg haP) (P.inv_mem hg)
    · exact Lemma213.mem_cjComp_of_mem g C haC
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [conj_pow, hap]
      group
  · rintro ⟨⟨ha'P, ha'C⟩, ha'p⟩
    have haC : g⁻¹ * a' * g ∈ C.1 := (mem_cjComp_iff g C).1 ha'C
    refine ⟨g⁻¹ * a' * g, ⟨⟨?_, haC⟩, ?_⟩, ?_⟩
    · exact P.mul_mem (P.mul_mem (P.inv_mem hg) ha'P) hg
    · have := conj_pow (a := g⁻¹) (b := a') (i := p)
      rw [inv_inv] at this
      rw [this, ha'p]
      group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem fixed_cjComp_iff {g : Y} (hg : g ∈ P) (C : ComponentIndex Y) :
    Fixed P (cjComp g C) ↔ Fixed P C := by
  have key : ∀ (D : ComponentIndex Y) (k : Y), k ∈ P → Fixed P D → Fixed P (cjComp k D) := by
    intro D k hk hD h hh
    rw [mem_normalizer_iff]
    intro c
    have h1 := hD (k⁻¹ * h * k) (P.mul_mem (P.mul_mem (P.inv_mem hk) hh) hk)
    rw [mem_normalizer_iff] at h1
    rw [Lemma213.mem_cjComp_iff, Lemma213.mem_cjComp_iff]
    have := h1 (k⁻¹ * c * k)
    simpa [mul_assoc] using this
  refine ⟨fun hF => ?_, fun hF => key C g hg hF⟩
  have h2 := key (cjComp g C) g⁻¹ (P.inv_mem hg) hF
  rwa [← Lemma213.cjComp_mul, inv_mul_cancel, Lemma213.cjComp_one] at h2

theorem Cfg.omega1_eq_zpowers (h : Cfg p P x z) {C : ComponentIndex Y}
    (hcyc : IsCyclic ↥(P ⊓ C.1)) :
    ∃ a₀ : Y, a₀ ∈ P ⊓ C.1 ∧ orderOf a₀ = p ∧ omega1 p P C = zpowers a₀ := by
  classical
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set A : Subgroup Y := P ⊓ C.1 with hA
  have hAp : IsPGroup p A := h.isPGroup.to_le inf_le_left
  have hAne : A ≠ ⊥ := h.inf_comp_ne_bot C
  haveI : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).2 hAne
  obtain ⟨m, hm, hmcard⟩ := hAp.nontrivial_iff_card.mp inferInstance
  have hdvd : p ∣ Nat.card A := hmcard ▸ dvd_pow_self p hm.ne'
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := A) p hdvd
  set a₀ : Y := (w : Y) with ha₀
  have hord : orderOf a₀ = p := (Subgroup.orderOf_coe w).trans hw
  have ha₀A : a₀ ∈ A := w.2
  haveI : Fintype ↥A := Fintype.ofFinite _
  have hle := IsCyclic.card_pow_eq_one_le (α := ↥A) (n := p) hp.pos
  have hwp : w ^ p = 1 := hw ▸ pow_orderOf_eq_one w
  have hsub : (Set.range fun k : Fin p => w ^ (k : ℕ)) ⊆ {a : ↥A | a ^ p = 1} := by
    rintro _ ⟨k, rfl⟩
    show (w ^ (k : ℕ)) ^ p = 1
    rw [← pow_mul, mul_comm, pow_mul, hwp, one_pow]
  have hinj : Function.Injective fun k : Fin p => w ^ (k : ℕ) := by
    intro i j hij
    exact Fin.ext (pow_injOn_Iio_orderOf (by rw [Set.mem_Iio, hw]; exact i.2)
      (by rw [Set.mem_Iio, hw]; exact j.2) hij)
  have hcardset : p ≤ (Finset.univ.filter fun a : ↥A => a ^ p = 1).card := by
    have : (Finset.univ.image fun k : Fin p => w ^ (k : ℕ)) ⊆
        Finset.univ.filter fun a : ↥A => a ^ p = 1 := by
      intro a ha
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub ⟨k, rfl⟩⟩
    calc p = (Finset.univ.image fun k : Fin p => w ^ (k : ℕ)).card := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Finset.card_le_card this
  have heq : (Finset.univ.image fun k : Fin p => w ^ (k : ℕ)) =
      Finset.univ.filter fun a : ↥A => a ^ p = 1 := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro a ha
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub ⟨k, rfl⟩⟩
    · calc (Finset.univ.filter fun a : ↥A => a ^ p = 1).card ≤ p := hle
        _ = (Finset.univ.image fun k : Fin p => w ^ (k : ℕ)).card := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hpow : ∀ a : Y, a ∈ A → a ^ p = 1 → a ∈ zpowers a₀ := by
    intro a haA hap
    have hmem : (⟨a, haA⟩ : ↥A) ∈ Finset.univ.filter fun a : ↥A => a ^ p = 1 :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subtype.ext (by simpa using hap)⟩
    rw [← heq] at hmem
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hmem
    refine mem_zpowers_iff.mpr ⟨(k : ℕ), ?_⟩
    have := congrArg Subtype.val hk
    simpa [zpow_natCast, ha₀] using this
  refine ⟨a₀, ha₀A, hord, ?_⟩
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 fun a ha => hpow a ha.1 ha.2
  · refine zpowers_le.2 (Subgroup.subset_closure ⟨ha₀A, ?_⟩)
    rw [← hord]
    exact pow_orderOf_eq_one a₀

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B
