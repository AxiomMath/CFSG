module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS28Elem

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

namespace GMS43

variable {D : Type} [Group D] [Finite D]

theorem card_commutator_mul_card_inf_centralizer_le {E : Subgroup D}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {w : D} (hwE : w ∈ normalizer (E : Set D)) :
    Nat.card (⁅E, zpowers w⁆ : Subgroup D) *
      Nat.card (E ⊓ centralizer ({w} : Set D) : Subgroup D) ≤ Nat.card E := by
  classical
  have hc : ∀ v ∈ E, w * v * w⁻¹ ∈ E := fun v hv => (mem_normalizer_iff.mp hwE v).mp hv
  let φ : E →* E :=
    { toFun := fun v => ⟨v * (w * v * w⁻¹)⁻¹, mul_mem v.2 (inv_mem (hc v v.2))⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        have ha := inv_mem (hc x x.2)
        have hb := inv_mem (hc y y.2)
        have h1 : (w * ((x : D) * y) * w⁻¹)⁻¹ = (w * y * w⁻¹)⁻¹ * (w * x * w⁻¹)⁻¹ := by group
        show (x : D) * y * (w * ((x : D) * y) * w⁻¹)⁻¹ =
          (x : D) * (w * x * w⁻¹)⁻¹ * ((y : D) * (w * y * w⁻¹)⁻¹)
        rw [h1]
        set a := (w * (x : D) * w⁻¹)⁻¹
        set b := (w * (y : D) * w⁻¹)⁻¹
        have hab : b * a = a * b := hcomm b hb a ha
        have hya : (y : D) * a = a * y := hcomm _ y.2 a ha
        calc (x : D) * y * (b * a) = x * y * (a * b) := by rw [hab]
          _ = x * (y * a) * b := by simp only [mul_assoc]
          _ = x * (a * y) * b := by rw [hya]
          _ = x * a * (y * b) := by simp only [mul_assoc]) }
  have hφ : ∀ v : E, (φ v : D) = ⁅(v : D), w⁆ := fun v => by
    show (v : D) * (w * v * w⁻¹)⁻¹ = _
    rw [commutatorElement_def]
    group
  set R : Subgroup D := φ.range.map E.subtype with hRdef
  have hR : ∀ v ∈ E, ⁅v, w⁆ ∈ R := fun v hv => ⟨φ ⟨v, hv⟩, ⟨⟨v, hv⟩, rfl⟩, hφ _⟩
  have hpow : ∀ e ∈ E, ∀ n : ℕ, ⁅e, w ^ n⁆ ∈ R := by
    intro e he n
    induction n with
    | zero => simp [one_mem]
    | succ n ih =>
      have hwn : w ^ n * e * (w ^ n)⁻¹ ∈ E := (mem_normalizer_iff.mp (pow_mem hwE n) e).mp he
      have key : ⁅e, w ^ (n + 1)⁆ = ⁅e, w ^ n⁆ * ⁅w ^ n * e * (w ^ n)⁻¹, w⁆ := by
        simp only [commutatorElement_def, pow_succ]
        group
      rw [key]
      exact mul_mem ih (hR _ hwn)
  have hle : (⁅E, zpowers w⁆ : Subgroup D) ≤ R := by
    rw [commutator_le]
    intro e he z hz
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hz)
    exact hpow e he n
  have h1 := card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h1
  have h2 : Nat.card (⁅E, zpowers w⁆ : Subgroup D) ≤ Nat.card φ.range := by
    refine (card_le_of_le hle).trans ?_
    rw [hRdef, card_map_of_injective E.subtype_injective]
  have h3 : Nat.card (E ⊓ centralizer ({w} : Set D) : Subgroup D) ≤ Nat.card φ.ker := by
    refine Nat.card_le_card_of_injective
      (fun v => ⟨⟨v.1, (mem_inf.mp v.2).1⟩, ?_⟩) ?_
    · rw [MonoidHom.mem_ker]
      apply Subtype.ext
      have hv := mem_centralizer_singleton_iff.mp (mem_inf.mp v.2).2
      show (v : D) * (w * v * w⁻¹)⁻¹ = 1
      rw [← hv]
      group
    · intro v v' hvv
      have h := congrArg (fun x => ((x : E) : D)) (congrArg Subtype.val hvv)
      exact Subtype.ext h
  calc Nat.card (⁅E, zpowers w⁆ : Subgroup D) *
        Nat.card (E ⊓ centralizer ({w} : Set D) : Subgroup D)
      ≤ Nat.card φ.range * Nat.card φ.ker := Nat.mul_le_mul h2 h3
    _ = Nat.card E := h1.symm

omit [Finite D] in
theorem rightConjugate_comm {E : Subgroup D} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (g : D) : ∀ x ∈ rightConjugate E g, ∀ y ∈ rightConjugate E g, x * y = y * x := by
  intro x hx y hy
  rw [mem_rightConjugate_iff] at hx hy
  have h := hcomm _ hx _ hy
  calc x * y = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by rw [h]
    _ = y * x := by group

theorem card_commutator_le_relIndex_rightConjugate {E : Subgroup D}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {g : D}
    (hFN : rightConjugate E g ≤ normalizer (E : Set D)) :
    ∀ w ∈ rightConjugate E g,
      Nat.card (⁅E, zpowers w⁆ : Subgroup D) ≤ E.relIndex (rightConjugate E g) := by
  intro w hw
  have hFcomm := rightConjugate_comm hcomm g
  have hsub : E ⊓ rightConjugate E g ≤ E ⊓ centralizer ({w} : Set D) := fun v hv =>
    mem_inf.mpr ⟨(mem_inf.mp hv).1,
      mem_centralizer_singleton_iff.mpr (hFcomm _ (mem_inf.mp hv).2 _ hw)⟩
  have h1 := card_commutator_mul_card_inf_centralizer_le hcomm (hFN hw)
  have h2 := card_le_of_le hsub
  have h3 := relIndex_mul_card E (rightConjugate E g)
  rw [rightConjugate_card] at h3
  have hpos : 0 < Nat.card (E ⊓ rightConjugate E g : Subgroup D) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card (⁅E, zpowers w⁆ : Subgroup D) * Nat.card (E ⊓ rightConjugate E g : Subgroup D)
      ≤ Nat.card (⁅E, zpowers w⁆ : Subgroup D) *
          Nat.card (E ⊓ centralizer ({w} : Set D) : Subgroup D) := Nat.mul_le_mul_left _ h2
    _ ≤ Nat.card E := h1
    _ = _ := h3.symm

theorem exists_sylow_stronglyClosed_of_commutator_bound {S E : Subgroup D} (hES : E ≤ S)
    (hEel : ∀ e ∈ E, e * e = 1) (hsyl : IsSylowOf 2 S (normalizer (E : Set D)))
    (hX : ∀ U ≤ E, ∀ h : D, rightConjugate U h ≤ S → ¬ rightConjugate U h ≤ E →
      ∃ w ∈ rightConjugate U h,
        E.relIndex (rightConjugate U h) < Nat.card (⁅E, zpowers w⁆ : Subgroup D)) :
    ∃ P : Sylow 2 D, (P : Subgroup D) = S ∧
      ∀ e ∈ E, ∀ g : D, g⁻¹ * e * g ∈ S → g⁻¹ * e * g ∈ E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSN : S ≤ normalizer (E : Set D) := hsyl.le
  have hSp : IsPGroup 2 S := hsyl.isPGroup
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hEel a ha)
    have h2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hEel b hb)
    have h3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hEel _ (mul_mem ha hb))
    rw [mul_inv_rev, h1, h2] at h3
    exact h3.symm
  have hwc : ∀ g : D, rightConjugate E g ≤ S → rightConjugate E g = E := by
    intro g hgS
    by_contra hne
    have hnle : ¬ rightConjugate E g ≤ E := fun hle =>
      hne (Subgroup.eq_of_le_of_card_ge hle (rightConjugate_card E g).symm.le)
    obtain ⟨w, hw, hlt⟩ := hX E le_rfl g hgS hnle
    have := card_commutator_le_relIndex_rightConjugate hEcomm (hgS.trans hSN) w hw
    omega
  have hSyl : IsSylowOf 2 S ⊤ := by
    by_contra htop
    obtain ⟨P, hSP, z, hzP, hzN, hzS⟩ := GMS28.exists_mem_normalizer_of_not_isSylowOf hSp htop
    have hconj : rightConjugate E z ≤ S := by
      intro x hx
      rw [mem_rightConjugate_iff] at hx
      have h1 := (mem_normalizer_iff.mp (inv_mem hzN) (z * x * z⁻¹)).mp (hES hx)
      rwa [show z⁻¹ * (z * x * z⁻¹) * z⁻¹⁻¹ = x by group] at h1
    have hzE : z ∈ normalizer (E : Set D) := (rightConjugate_eq_self_iff E z).mp (hwc z hconj)
    have hle : S ⊔ zpowers z ≤ normalizer (E : Set D) := sup_le hSN (zpowers_le.mpr hzE)
    have hp : IsPGroup 2 (S ⊔ zpowers z : Subgroup D) :=
      P.isPGroup'.to_le (sup_le hSP (zpowers_le.mpr hzP))
    have heq := hsyl.eq_of_le le_sup_left hle hp
    exact hzS (heq ▸ mem_sup_right (mem_zpowers z))
  obtain ⟨-, hp, hidx⟩ := isSylowOf_iff.mp hSyl
  rw [relIndex_top_right] at hidx
  set P : Sylow 2 D := hp.toSylow hidx with hPdef
  have hPS : (P : Subgroup D) = S := IsPGroup.toSylow_coe hp hidx
  refine ⟨P, hPS, ?_⟩
  intro e he g hg
  by_contra hgE
  have hEA : CFSG.Open.IsElemAbelian 2 E :=
    ⟨⟨⟨fun a b => Subtype.ext (hEcomm _ a.2 _ b.2)⟩⟩, fun x hx => by rw [sq]; exact hEel x hx⟩
  obtain ⟨U, hUE, h, hUP, hUnle, hcard⟩ :=
    CFSG.ComponentClassification.GoldschmidtFour.goldschmidt_theorem_four_holds D P E
      (hPS ▸ hES) hEA (fun h hh => hwc h (hPS ▸ hh)) ⟨e, he, g, hPS ▸ hg, hgE⟩
  obtain ⟨w, hw, hlt⟩ := hX U hUE h (hPS ▸ hUP) hUnle
  have := hcard w hw
  omega

theorem lt_card_commutator_of_mul_lt {E : Subgroup D} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    {w : D} (hwE : w ∈ normalizer (E : Set D)) {n : ℕ}
    (hlt : Nat.card (E ⊓ centralizer ({w} : Set D) : Subgroup D) * n < Nat.card E) :
    n < Nat.card (⁅E, zpowers w⁆ : Subgroup D) := by
  have h := GMS28.card_le_card_inf_centralizer_mul hcomm hwE
  by_contra hle
  push Not at hle
  have := Nat.mul_le_mul_left (Nat.card (E ⊓ centralizer ({w} : Set D) : Subgroup D)) hle
  omega

end GMS43

end CFSG.SeitzReduction.RankOne
