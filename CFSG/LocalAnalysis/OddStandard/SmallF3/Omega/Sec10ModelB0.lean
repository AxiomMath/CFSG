module

public import Certificates.Certificate442002
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelT0

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ComponentClassification.GSThmB

local notation "P45" => Equiv.Perm (Fin 45)

local notation "bl0" => Certificates.OmegaB0.bl ()

local notation "Φ0" => Certificates.OmegaB0.phiTable (Certificates.OmegaB0.bl ())

local notation "V0" => Certificates.OmegaB0.allVecs ()

local notation "Bl0" => Certificates.OmegaB0.bElems Φ0 V0

local notation "S0" => Certificates.OmegaB0.s5l ()

@[expose] def phiB (v : Fin 5 → ZMod 2) : P45 := Certificates.OmegaB0.phi0 Φ0 v

@[expose] def B0 : Subgroup P45 := Subgroup.closure {g | ∃ v, IsEvenVec v ∧ phiB v = g}

theorem b0Check_parts :
    Certificates.OmegaB0.closedChk Bl0 = true ∧
    Certificates.OmegaB0.sylowChk (elemsT QT0) Bl0 = true ∧
    Certificates.OmegaB0.centChk (elemsT QA45) Bl0 = true ∧
    Certificates.OmegaB0.vecChk V0 S0 = true ∧
    Certificates.OmegaB0.homChk Φ0 V0 = true ∧
    Certificates.OmegaB0.actChk (elemsT QP45) (elemsT QA45) bl0 Φ0 Bl0 V0 S0 = true ∧
    Certificates.OmegaB0.classChk (elemsT QP45) Φ0 V0 = true := by
  have h := Certificates.certificate442002
  simp only [Certificates.OmegaB0.check, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem mem_allVecs (v : Fin 5 → ZMod 2) : v ∈ V0 := by
  have h := b0Check_parts.2.2.2.1
  simp only [Certificates.OmegaB0.vecChk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1 v

theorem mem_s5l (σ : Equiv.Perm (Fin 5)) : σ ∈ S0 := by
  have h := b0Check_parts.2.2.2.1
  simp only [Certificates.OmegaB0.vecChk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2 σ

theorem mem_bElems {g : P45} :
    g ∈ Bl0 ↔ ∃ v, IsEvenVec v ∧ phiB v = g := by
  simp only [Certificates.OmegaB0.bElems, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨v, ⟨-, hv⟩, rfl⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, ⟨mem_allVecs v, hv⟩, rfl⟩

theorem bl0_closed :
    ((Bl0).length = 16 ∧ (Bl0).Nodup) ∧ (1 : P45) ∈ Bl0 ∧
      ∀ a ∈ Bl0, a⁻¹ ∈ Bl0 ∧ a * a = 1 ∧ ∀ b ∈ Bl0, a * b ∈ Bl0 ∧ a * b = b * a := by
  have h := b0Check_parts.1
  simp only [Certificates.OmegaB0.closedChk, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨hlen, h1⟩, hall⟩ := h
  refine ⟨hlen, h1, fun a ha => ?_⟩
  obtain ⟨⟨hinv, hsq⟩, hb⟩ := hall a ha
  exact ⟨hinv, hsq, hb⟩

theorem mem_B0_iff {g : P45} : g ∈ B0 ↔ g ∈ Bl0 := by
  have hc := bl0_closed
  constructor
  · intro hg
    let S : Subgroup P45 :=
      { carrier := {g | g ∈ Bl0}
        mul_mem' := fun {a b} ha hb => ((hc.2.2 a ha).2.2 b hb).1
        one_mem' := hc.2.1
        inv_mem' := fun {a} ha => (hc.2.2 a ha).1 }
    have hle : B0 ≤ S := (Subgroup.closure_le S).2 fun x ⟨v, hv, hx⟩ =>
      (mem_bElems.2 ⟨v, hv, hx⟩ : x ∈ Bl0)
    exact hle hg
  · intro hg
    obtain ⟨v, hv, rfl⟩ := mem_bElems.1 hg
    exact Subgroup.subset_closure ⟨v, hv, rfl⟩

theorem mem_B0_iff_phiB {g : P45} :
    g ∈ B0 ↔ ∃ v, IsEvenVec v ∧ phiB v = g :=
  mem_B0_iff.trans mem_bElems

theorem phiB_mem_B0 {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    phiB v ∈ B0 :=
  mem_B0_iff_phiB.2 ⟨v, hv, rfl⟩

theorem card_B0 : Nat.card B0 = 2 ^ 4 := by
  have hc := bl0_closed
  have h := card_eq_length (fun g : P45 => g ∈ B0) id Function.injective_id Bl0 hc.1.2
    (fun b => ⟨fun hb => ⟨b, mem_B0_iff.2 hb, rfl⟩, fun ⟨a, ha, hab⟩ => hab ▸ mem_B0_iff.1 ha⟩)
  rw [show Nat.card B0 = Nat.card {a // a ∈ B0} from rfl, h, hc.1.1]
  norm_num

theorem B0_comm {a b : P45} (ha : a ∈ B0) (hb : b ∈ B0) :
    a * b = b * a :=
  ((bl0_closed.2.2 a (mem_B0_iff.1 ha)).2.2 b (mem_B0_iff.1 hb)).2

theorem B0_sq {a : P45} (ha : a ∈ B0) : a * a = 1 :=
  (bl0_closed.2.2 a (mem_B0_iff.1 ha)).2.1

theorem homChk_spec (v w : Fin 5 → ZMod 2) :
    phiB (v + w) = phiB v * phiB w ∧ (IsEvenVec v → IsEvenVec w → phiB v = phiB w → v = w) := by
  have h := b0Check_parts.2.2.2.2.1
  simp [Certificates.OmegaB0.homChk, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h v (mem_allVecs v) w (mem_allVecs w)
  refine ⟨h1, fun hv hw hvw => ?_⟩
  rcases h2 with ((h2 | h2) | h2) | h2
  · exact absurd hv h2
  · exact absurd hw h2
  · exact absurd hvw h2
  · exact h2

theorem phiB_add (v w : Fin 5 → ZMod 2) :
    phiB (v + w) = phiB v * phiB w :=
  (homChk_spec v w).1

theorem phiB_inj {v w : Fin 5 → ZMod 2} (hv : IsEvenVec v)
    (hw : IsEvenVec w) (h : phiB v = phiB w) : v = w :=
  (homChk_spec v w).2 hv hw h

theorem sylowChk_at {a : P45}
    (haT : a ∈ QT0.originalSubgroup) (haB : a ∉ B0) :
    Nat.card ↥(QT0.originalSubgroup ⊓ centralizer ({a} : Set P45)) ≤ 16 ∧
      (Nat.card ↥(QT0.originalSubgroup ⊓ centralizer ({a} : Set P45)) < 16 ∨
        ∃ x ∈ QT0.originalSubgroup ⊓ centralizer ({a} : Set P45),
          ∃ y ∈ QT0.originalSubgroup ⊓ centralizer ({a} : Set P45), x * y ≠ y * x) := by
  have h := b0Check_parts.2.1
  simp only [Certificates.OmegaB0.sylowChk, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, List.any_eq_true] at h
  have h2 := h.2 a ((mem_elemsT QT0 QT0_valid.1 a).2 haT)
  rcases h2 with h2 | ⟨h3, h4⟩
  · exact absurd (mem_B0_iff.2 h2) haB
  · rw [card_inf_centralizer QT0 QT0_valid.1 a]
    refine ⟨h3, ?_⟩
    rcases h4 with h4 | ⟨x, hx, y, hy, hxy⟩
    · exact Or.inl h4
    · right
      simp only [List.mem_filter, decide_eq_true_eq, mem_elemsT QT0 QT0_valid.1] at hx hy
      exact ⟨x, Subgroup.mem_inf.2 ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.2 hx.2⟩,
        y, Subgroup.mem_inf.2 ⟨hy.1, Subgroup.mem_centralizer_singleton_iff.2 hy.2⟩, hxy⟩

theorem B0_le_T0 :
    B0 ≤ QT0.originalSubgroup := by
  intro g hg
  have h := b0Check_parts.2.1
  simp only [Certificates.OmegaB0.sylowChk, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h
  exact (mem_elemsT QT0 QT0_valid.1 g).1 (h.1 g (mem_B0_iff.1 hg))

theorem eq_B0_of_abelian
    {A : Subgroup P45} (hA : A ≤ QT0.originalSubgroup) (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hcard : Nat.card A = 2 ^ 4) : A = B0 := by
  by_cases hAB : A ≤ B0
  · exact Subgroup.eq_of_le_of_card_ge hAB (by rw [card_B0, hcard])
  · exfalso
    obtain ⟨a, haA, haB⟩ := SetLike.not_le_iff_exists.1 hAB
    obtain ⟨hle16, hcases⟩ := sylowChk_at (hA haA) haB
    have hAle : A ≤ QT0.originalSubgroup ⊓ centralizer ({a} : Set P45) := fun x hx =>
      Subgroup.mem_inf.2 ⟨hA hx, Subgroup.mem_centralizer_singleton_iff.2 (hc x hx a haA)⟩
    have hge := Subgroup.card_le_of_le hAle
    rcases hcases with hlt | ⟨x, hx, y, hy, hxy⟩
    · omega
    · have hAeq : A = QT0.originalSubgroup ⊓ centralizer ({a} : Set P45) :=
        Subgroup.eq_of_le_of_card_ge hAle (by omega)
      rw [← hAeq] at hx hy
      exact hxy (hc x hx y hy)

theorem card_le_of_abelian
    {A : Subgroup P45} (hA : A ≤ QT0.originalSubgroup) (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    Nat.card A ≤ 2 ^ 4 := by
  by_cases hAB : A ≤ B0
  · have := Subgroup.card_le_of_le hAB
    rwa [card_B0] at this
  · obtain ⟨a, haA, haB⟩ := SetLike.not_le_iff_exists.1 hAB
    obtain ⟨hle16, -⟩ := sylowChk_at (hA haA) haB
    have hAle : A ≤ QT0.originalSubgroup ⊓ centralizer ({a} : Set P45) := fun x hx =>
      Subgroup.mem_inf.2 ⟨hA hx, Subgroup.mem_centralizer_singleton_iff.2 (hc x hx a haA)⟩
    have hge := Subgroup.card_le_of_le hAle
    omega

theorem B0_le_P :
    B0 ≤ QP45.originalSubgroup :=
  B0_le_T0.trans X11.QT0_le

theorem isElemAbelian_B0 : CFSG.Open.IsElemAbelian 2 B0 := by
  refine ⟨isMulCommutative_iff_of_setLike.2 fun a ha b hb => B0_comm ha hb, fun x hx => ?_⟩
  rw [pow_two]
  exact B0_sq hx

theorem centralizer_B0_le
    {a : P45} (ha : a ∈ QA45.originalSubgroup) (h : ∀ b ∈ B0, a * b = b * a) : a ∈ B0 := by
  have hs := b0Check_parts.2.2.1
  simp only [Certificates.OmegaB0.centChk, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at hs
  rcases hs a ((mem_elemsT QA45 QA45_ok a).2 ha) with hn | hy
  · exfalso
    have : (Bl0).all (fun b => decide (a * b = b * a)) = true := by
      rw [List.all_eq_true]
      intro b hb
      exact decide_eq_true (h b (mem_B0_iff.2 hb))
    rw [this] at hn
    exact absurd hn (by decide)
  · exact mem_B0_iff.2 hy

theorem mem_normalizer_B0 {n : P45} (h1 : ∀ b ∈ B0, n * b * n⁻¹ ∈ B0)
    (h2 : ∀ b ∈ B0, n⁻¹ * b * n ∈ B0) : n ∈ normalizer (B0 : Set P45) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h1 x hx, fun hx => ?_⟩
  have h3 := h2 _ hx
  have h4 : n⁻¹ * (n * x * n⁻¹) * n = x := by group
  rwa [h4] at h3

theorem normB_iff {n : P45} :
    Certificates.OmegaB0.normB Bl0 n = true ↔
      (∀ b ∈ B0, n * b * n⁻¹ ∈ B0) ∧ ∀ b ∈ B0, n⁻¹ * b * n ∈ B0 := by
  simp only [Certificates.OmegaB0.normB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    mem_B0_iff]
  constructor
  · intro h
    exact ⟨fun b hb => (h b hb).1, fun b hb => (h b hb).2⟩
  · rintro ⟨h1, h2⟩ b hb
    exact ⟨h1 b hb, h2 b hb⟩

theorem actEq_iff {n : P45} {σ : Equiv.Perm (Fin 5)} :
    Certificates.OmegaB0.actEq Φ0 V0 n σ = true ↔
      ∀ v, n * phiB v * n⁻¹ = phiB (permVec σ v) := by
  simp only [Certificates.OmegaB0.actEq, List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun h v => h v (mem_allVecs v), fun h v _ => h v⟩

theorem phiB_act_P {n : P45}
    (hn : n ∈ QP45.originalSubgroup) (h1 : ∀ b ∈ B0, n * b * n⁻¹ ∈ B0)
    (h2 : ∀ b ∈ B0, n⁻¹ * b * n ∈ B0) :
    ∃ σ ∈ alternatingGroup (Fin 5), ∀ v, n * phiB v * n⁻¹ = phiB (permVec σ v) := by
  have hs := b0Check_parts.2.2.2.2.2.1
  simp only [Certificates.OmegaB0.actChk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    List.mem_filter, decide_eq_true_eq] at hs
  obtain ⟨⟨hA, -⟩, -⟩ := hs
  obtain ⟨σ, -, ⟨-, hsign⟩, hact⟩ :=
    hA n ⟨(mem_elemsT QP45 QP45_ok n).2 hn, normB_iff.2 ⟨h1, h2⟩⟩
  exact ⟨σ, Equiv.Perm.mem_alternatingGroup.2 hsign, actEq_iff.1 hact⟩

theorem phiB_act_A {n : P45}
    (hn : n ∈ QA45.originalSubgroup) (h1 : ∀ b ∈ B0, n * b * n⁻¹ ∈ B0)
    (h2 : ∀ b ∈ B0, n⁻¹ * b * n ∈ B0) :
    ∃ σ : Equiv.Perm (Fin 5), ∀ v, n * phiB v * n⁻¹ = phiB (permVec σ v) := by
  have hs := b0Check_parts.2.2.2.2.2.1
  simp only [Certificates.OmegaB0.actChk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    List.mem_filter, decide_eq_true_eq] at hs
  obtain ⟨⟨-, hA⟩, -⟩ := hs
  obtain ⟨σ, -, -, hact⟩ := hA n ⟨(mem_elemsT QA45 QA45_ok n).2 hn, normB_iff.2 ⟨h1, h2⟩⟩
  exact ⟨σ, actEq_iff.1 hact⟩

theorem exists_phiB_act
    {σ : Equiv.Perm (Fin 5)} (hσ : σ ∈ alternatingGroup (Fin 5)) :
    ∃ n ∈ QP45.originalSubgroup, ((∀ b ∈ B0, n * b * n⁻¹ ∈ B0) ∧ ∀ b ∈ B0, n⁻¹ * b * n ∈ B0) ∧
      ∀ v, n * phiB v * n⁻¹ = phiB (permVec σ v) := by
  have hs := b0Check_parts.2.2.2.2.2.1
  simp only [Certificates.OmegaB0.actChk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    List.mem_filter, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hs
  obtain ⟨-, hS⟩ := hs
  rcases hS σ (mem_s5l σ) with hn | ⟨n, ⟨hnL, hnN⟩, -, hact⟩
  · exact absurd (Equiv.Perm.mem_alternatingGroup.1 hσ) hn
  · exact ⟨n, (mem_elemsT QP45 QP45_ok n).1 hnL, normB_iff.1 hnN, actEq_iff.1 hact⟩

end CFSG.OddStandard.SmallF3.Omega
