module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

variable {X : Type} [Group X] [Finite X]

private theorem card_sup_mul_card_inf_of_commute {H : Type*} [Group H] [Finite H]
    (L R : Subgroup H) (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup H) * Nat.card (L ⊓ R : Subgroup H) =
      Nat.card L * Nat.card R := by
  let μ : L × R →* H := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : H) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup H) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : H), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : H)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  rw [mul_comm]; exact this

theorem gold_commutator_step {A : Subgroup X} (hA : IsElemAbelian 2 A) {t : X}
    (ht2 : t * t = 1) (htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A) {B₁ : Subgroup X} (hB₁A : B₁ ≤ A)
    (hB₁t : ∀ b ∈ B₁, t * b = b * t) :
    ∃ B₂ : Subgroup X, B₂ ≤ A ∧ B₁ ≤ B₂ ∧
      (∀ a, a ∈ B₂ ↔ a ∈ A ∧ a * t * a⁻¹ * t⁻¹ ∈ B₁) ∧
      Nat.card A * Nat.card B₁ ≤ Nat.card ↥(A ⊓ centralizer ({t} : Set X)) * Nat.card B₂ := by
  classical
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA2 : ∀ x ∈ A, x * x = 1 := fun x hx => by
    simpa [pow_two] using hA.2 x hx
  have hinvA : ∀ x ∈ A, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (hA2 x hx)
  have htt : ∀ u : X, t * (t * u * t⁻¹) * t⁻¹ = u := by
    intro u
    have e : t * (t * u * t⁻¹) * t⁻¹ = (t * t) * u * (t * t)⁻¹ := by group
    rw [e, ht2, one_mul, inv_one, mul_one]
  let ψ : ↥A →* ↥A :=
    { toFun := fun a => ⟨(a : X) * (t * (a : X) * t⁻¹), A.mul_mem a.2 (htA a a.2)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        show ((a : X) * (b : X)) * (t * ((a : X) * (b : X)) * t⁻¹)
            = ((a : X) * (t * (a : X) * t⁻¹)) * ((b : X) * (t * (b : X) * t⁻¹))
        have h1 : (b : X) * (t * (a : X) * t⁻¹) = (t * (a : X) * t⁻¹) * (b : X) :=
          hcomm b b.2 (t * (a : X) * t⁻¹) (htA a a.2)
        calc ((a : X) * (b : X)) * (t * ((a : X) * (b : X)) * t⁻¹)
            = (a : X) * ((b : X) * (t * (a : X) * t⁻¹)) * (t * (b : X) * t⁻¹) := by group
          _ = ((a : X) * (t * (a : X) * t⁻¹)) * ((b : X) * (t * (b : X) * t⁻¹)) := by
                rw [h1]; group }
  have hψ_apply : ∀ a : ↥A, ((ψ a : ↥A) : X) = (a : X) * (t * (a : X) * t⁻¹) := fun _ => rfl
  have hψ_comm : ∀ a : ↥A, ((ψ a : ↥A) : X) = (a : X) * t * (a : X)⁻¹ * t⁻¹ := by
    intro a
    rw [hψ_apply a]
    have h3 : (a : X)⁻¹ = (a : X) := hinvA (a : X) a.2
    rw [h3]
    group
  have hψ_eq_one : ∀ a : ↥A, ψ a = 1 ↔ (a : X) * t = t * (a : X) := by
    intro a
    constructor
    · intro h
      have h1 : (a : X) * (t * (a : X) * t⁻¹) = 1 := congrArg Subtype.val h
      have h2 : t * (a : X) * t⁻¹ = (a : X)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [hinvA (a : X) a.2] at h2
      have h3 : t * (a : X) = (a : X) * t := by
        calc t * (a : X) = t * (a : X) * t⁻¹ * t := by group
          _ = (a : X) * t := by rw [h2]
      exact h3.symm
    · intro h
      apply Subtype.ext
      show (a : X) * (t * (a : X) * t⁻¹) = 1
      have h2 : t * (a : X) * t⁻¹ = (a : X) := by
        calc t * (a : X) * t⁻¹ = ((a : X) * t) * t⁻¹ := by rw [h]
          _ = (a : X) := by group
      rw [h2]
      simpa [pow_two] using hA.2 (a : X) a.2
  set B₁' : Subgroup ↥A := B₁.subgroupOf A with hB₁'def
  set D : Subgroup ↥A := B₁'.comap ψ with hDdef
  set B₂ : Subgroup X := D.map A.subtype with hB₂def
  set K : Subgroup ↥A := ψ.ker with hKdef
  have hK_eq : K = (A ⊓ centralizer ({t} : Set X)).subgroupOf A := by
    ext a
    rw [hKdef, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      hψ_eq_one a, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
  set I : Subgroup ↥A := ψ.range with hIdef
  have hmemK : ∀ w : ↥A, t * (w : X) * t⁻¹ = (w : X) → w ∈ K := by
    intro w hw
    rw [hKdef, MonoidHom.mem_ker]
    apply Subtype.ext
    show (w : X) * (t * (w : X) * t⁻¹) = 1
    rw [hw]
    simpa [pow_two] using hA.2 (w : X) w.2
  have hI_le_K : I ≤ K := by
    intro y hy
    rw [hIdef] at hy
    rcases hy with ⟨a, rfl⟩
    apply hmemK
    show t * ((a : X) * (t * (a : X) * t⁻¹)) * t⁻¹ = (a : X) * (t * (a : X) * t⁻¹)
    calc t * ((a : X) * (t * (a : X) * t⁻¹)) * t⁻¹
        = (t * (a : X) * t⁻¹) * (t * (t * (a : X) * t⁻¹) * t⁻¹) := by group
      _ = (t * (a : X) * t⁻¹) * (a : X) := by rw [htt]
      _ = (a : X) * (t * (a : X) * t⁻¹) :=
            (hcomm (a : X) a.2 (t * (a : X) * t⁻¹) (htA a a.2)).symm
  have hB₁'_le_K : B₁' ≤ K := by
    intro b hb
    rw [hB₁'def, Subgroup.mem_subgroupOf] at hb
    apply hmemK
    have ht : t * (b : X) * t⁻¹ = (b : X) := by
      have h := hB₁t (b : X) hb
      calc t * (b : X) * t⁻¹ = ((b : X) * t) * t⁻¹ := by rw [h]
        _ = (b : X) := by group
    exact ht
  have hKD : K ≤ D := by
    intro k hk
    rw [hKdef, MonoidHom.mem_ker] at hk
    rw [hDdef, Subgroup.mem_comap, hk]
    exact B₁'.one_mem
  have hB₂le : B₂ ≤ A := by
    rw [hB₂def]
    exact Subgroup.map_subtype_le D
  have hB₁_le_B₂ : B₁ ≤ B₂ := by
    intro b hb
    have hψ1 : ψ ⟨b, hB₁A hb⟩ = 1 := by
      apply Subtype.ext
      show (b : X) * (t * (b : X) * t⁻¹) = 1
      have ht : t * (b : X) * t⁻¹ = (b : X) := by
        have h := hB₁t (b : X) hb
        calc t * (b : X) * t⁻¹ = ((b : X) * t) * t⁻¹ := by rw [h]
          _ = (b : X) := by group
      rw [ht]
      simpa [pow_two] using hA.2 (b : X) (hB₁A hb)
    rw [hB₂def, Subgroup.mem_map]
    refine ⟨⟨b, hB₁A hb⟩, ?_, rfl⟩
    rw [hDdef, Subgroup.mem_comap, hψ1]
    exact B₁'.one_mem
  have hB₂_char : ∀ a, a ∈ B₂ ↔ a ∈ A ∧ a * t * a⁻¹ * t⁻¹ ∈ B₁ := by
    intro a
    rw [hB₂def, Subgroup.mem_map]
    constructor
    · rintro ⟨d, hd, rfl⟩
      have hd' : ψ d ∈ B₁' := by
        have h := hd
        rwa [hDdef, Subgroup.mem_comap] at h
      have hdB : ((ψ d : ↥A) : X) ∈ B₁ := by
        have h := hd'
        rwa [hB₁'def, Subgroup.mem_subgroupOf] at h
      exact ⟨d.2, by
        change (d : X) * t * (d : X)⁻¹ * t⁻¹ ∈ B₁
        rw [← hψ_comm d]
        exact hdB⟩
    · rintro ⟨haA, hB⟩
      refine ⟨⟨a, haA⟩, ?_, rfl⟩
      rw [hDdef, Subgroup.mem_comap, hB₁'def, Subgroup.mem_subgroupOf]
      rw [hψ_comm ⟨a, haA⟩]
      exact hB
  have hcardA : Nat.card A = Nat.card K * Nat.card I := by
    have h1 : K.index = Nat.card I := by
      rw [hKdef, hIdef]
      exact Subgroup.index_ker ψ
    have h2 := Subgroup.card_mul_index K
    rw [h1] at h2
    exact h2.symm
  have hcardB₁ : Nat.card B₁ = Nat.card B₁' := by
    rw [hB₁'def]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₁A).toEquiv).symm
  have hcardC : Nat.card ↥(A ⊓ centralizer ({t} : Set X)) = Nat.card K := by
    have h1 : Nat.card K = Nat.card ((A ⊓ centralizer ({t} : Set X)).subgroupOf A) := by
      rw [hK_eq]
    have h2 : Nat.card ((A ⊓ centralizer ({t} : Set X)).subgroupOf A) =
        Nat.card ↥(A ⊓ centralizer ({t} : Set X)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : A ⊓ centralizer ({t} : Set X) ≤ A)).toEquiv
    exact (h1.trans h2).symm
  have hcardB₂ : Nat.card B₂ = Nat.card D := by
    rw [hB₂def]
    exact Subgroup.card_map_of_injective A.subtype_injective
  have hD_card : Nat.card D = Nat.card K * Nat.card (I ⊓ B₁' : Subgroup ↥A) := by
    let f : ↥D →* ↥A := ψ.comp D.subtype
    have hker : Nat.card f.ker = Nat.card K := by
      have heq : f.ker = K.subgroupOf D := by
        ext d
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hKdef, MonoidHom.mem_ker]
        rfl
      rw [heq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKD).toEquiv
    have hrange : Nat.card f.range = Nat.card (I ⊓ B₁' : Subgroup ↥A) := by
      have heq : f.range = I ⊓ B₁' := by
        ext y
        rw [Subgroup.mem_inf]
        constructor
        · intro hy
          rw [MonoidHom.mem_range] at hy
          rcases hy with ⟨d, rfl⟩
          refine ⟨?_, ?_⟩
          · rw [hIdef, MonoidHom.mem_range]
            exact ⟨(d : ↥A), rfl⟩
          · have hd' : ψ (d : ↥A) ∈ B₁' := Subgroup.mem_comap.1 (hDdef ▸ d.2)
            exact hd'
        · rintro ⟨hyI, hyB⟩
          rw [hIdef, MonoidHom.mem_range] at hyI
          rcases hyI with ⟨a, rfl⟩
          rw [MonoidHom.mem_range]
          have haD : a ∈ D := by
            rw [hDdef, Subgroup.mem_comap]
            exact hyB
          exact ⟨⟨a, haD⟩, rfl⟩
      rw [heq]
    have h := Subgroup.card_ker_mul_card_range f
    rw [hker, hrange] at h
    exact h.symm
  have hprod : Nat.card I * Nat.card B₁' =
      Nat.card (I ⊔ B₁' : Subgroup ↥A) * Nat.card (I ⊓ B₁' : Subgroup ↥A) := by
    have hc : ∀ x ∈ I, ∀ y ∈ B₁', x * y = y * x := fun x _ y _ => hA.1.is_comm.comm x y
    exact (card_sup_mul_card_inf_of_commute I B₁' hc).symm
  have hB₂card : Nat.card B₂ = Nat.card K * Nat.card (I ⊓ B₁' : Subgroup ↥A) := by
    rw [hcardB₂, hD_card]
  have hsup_le : I ⊔ B₁' ≤ K := sup_le hI_le_K hB₁'_le_K
  have hcard_sup_le : Nat.card (I ⊔ B₁' : Subgroup ↥A) ≤ Nat.card K :=
    Subgroup.card_le_of_le hsup_le
  refine ⟨B₂, hB₂le, hB₁_le_B₂, hB₂_char, ?_⟩
  rw [hcardC, hB₂card]
  calc Nat.card A * Nat.card B₁
      = (Nat.card K * Nat.card I) * Nat.card B₁' := by rw [hcardA, hcardB₁]
    _ = Nat.card K * (Nat.card I * Nat.card B₁') := by rw [Nat.mul_assoc]
    _ = Nat.card K *
          (Nat.card (I ⊔ B₁' : Subgroup ↥A) * Nat.card (I ⊓ B₁' : Subgroup ↥A)) := by
        rw [hprod]
    _ ≤ Nat.card K * (Nat.card K * Nat.card (I ⊓ B₁' : Subgroup ↥A)) :=
        mul_le_mul_right
          (mul_le_mul_left hcard_sup_le (Nat.card (I ⊓ B₁' : Subgroup ↥A)))
          (Nat.card K)

theorem gold_H1_normalizes {A B₁ B₂ : Subgroup X} {t : X} (hA : IsElemAbelian 2 A)
    (hB₁A : B₁ ≤ A) (hB₂A : B₂ ≤ A)
    (hB₂ : ∀ a, a ∈ B₂ ↔ a ∈ A ∧ a * t * a⁻¹ * t⁻¹ ∈ B₁) :
    B₂ ≤ normalizer ((B₁ ⊔ zpowers t : Subgroup X) : Set X) := by
  classical
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA2 : ∀ x ∈ A, x * x = 1 := fun x hx => by
    simpa [pow_two] using hA.2 x hx
  have hinvA : ∀ x ∈ A, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (hA2 x hx)
  have hconj : ∀ a ∈ B₂, ∀ h ∈ (B₁ ⊔ zpowers t : Subgroup X),
      a * h * a⁻¹ ∈ B₁ ⊔ zpowers t := by
    intro a ha h hh
    have haA : a ∈ A := hB₂A ha
    have hle : (B₁ ⊔ zpowers t : Subgroup X) ≤
        (B₁ ⊔ zpowers t : Subgroup X).comap (MulAut.conj a).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro b hb
        rw [Subgroup.mem_comap]
        change a * b * a⁻¹ ∈ (B₁ ⊔ zpowers t : Subgroup X)
        have hba : b ∈ A := hB₁A hb
        have h1 : a * b = b * a := hcomm a haA b hba
        have hb' : a * b * a⁻¹ = b := by
          calc a * b * a⁻¹ = b * a * a⁻¹ := by rw [h1]
            _ = b * (a * a⁻¹) := by rw [mul_assoc]
            _ = b := by rw [mul_inv_cancel, mul_one]
        rw [hb']
        exact Subgroup.mem_sup_left hb
      · refine Subgroup.zpowers_le.2 ?_
        rw [Subgroup.mem_comap]
        change a * t * a⁻¹ ∈ (B₁ ⊔ zpowers t : Subgroup X)
        have hB : a * t * a⁻¹ * t⁻¹ ∈ B₁ := (hB₂ a).1 ha |>.2
        have ht : a * t * a⁻¹ = (a * t * a⁻¹ * t⁻¹) * t := by group
        rw [ht]
        exact mul_mem (Subgroup.mem_sup_left hB)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    have hh' : h ∈ (B₁ ⊔ zpowers t : Subgroup X).comap (MulAut.conj a).toMonoidHom :=
      hle hh
    rw [Subgroup.mem_comap] at hh'
    change a * h * a⁻¹ ∈ (B₁ ⊔ zpowers t : Subgroup X) at hh'
    exact hh'
  intro a ha
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hconj a ha h hh
  · intro hh
    have h2 := hconj a⁻¹ (B₂.inv_mem ha) (a * h * a⁻¹) hh
    have e : a⁻¹ * (a * h * a⁻¹) * (a⁻¹)⁻¹ = h := by group
    rwa [e] at h2

end CFSG.EvenSporadicStandard.HNRecog.Harada
