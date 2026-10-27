module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalancePow
public import CFSG.ClassicalInvolution.Asc77.WP3L52Comp

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance.StrongBalance
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance (deltaCore)
open scoped commutatorElement

namespace FrameVertex

section Abstract

variable {S H : Type} [Group S] [Group H]

theorem eq_one_of_perfect_center {K G : Type*} [Group K] [Group.IsPerfect K] [Group G]
    (f : K →* Subgroup.center G) : f = 1 := by
  have hp : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hs : Subsingleton f.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  ext x
  have h1 : (⟨f x, x, rfl⟩ : f.range) = 1 := Subsingleton.elim _ _
  simpa using congrArg Subtype.val h1

theorem mem_center_of_commutators_central [Group.IsPerfect S] {s : S}
    (h : ∀ t : S, ⁅s, t⁆ ∈ Subgroup.center S) : s ∈ Subgroup.center S := by
  have h1 : (QuotientGroup.mk' (Subgroup.center S) s) ∈
      Subgroup.center (S ⧸ Subgroup.center S) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center S) y
    have e1 : s * t = ⁅s, t⁆ * (t * s) := by simp only [commutatorElement_def]; group
    have e2 : QuotientGroup.mk' (Subgroup.center S) ⁅s, t⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (h t)
    have h3 : QuotientGroup.mk' (Subgroup.center S) (s * t) =
        QuotientGroup.mk' (Subgroup.center S) (t * s) := by
      rw [e1, map_mul, e2, one_mul]
    calc QuotientGroup.mk' (Subgroup.center S) t * QuotientGroup.mk' (Subgroup.center S) s
        = QuotientGroup.mk' (Subgroup.center S) (t * s) := (map_mul _ _ _).symm
      _ = QuotientGroup.mk' (Subgroup.center S) (s * t) := h3.symm
      _ = QuotientGroup.mk' (Subgroup.center S) s * QuotientGroup.mk' (Subgroup.center S) t :=
        map_mul _ _ _
  rw [Group.IsPerfect.center_quotient_center_eq_bot S, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff s).mp h1

theorem mem_normalizer_range (ψ : S →* H) (s : S) :
    ψ s ∈ Subgroup.normalizer (ψ.range : Set H) :=
  Subgroup.le_normalizer (⟨s, rfl⟩ : ψ s ∈ ψ.range)

@[expose] noncomputable def innerHom (ψ : S →* H) : S →* ↥(inducedAutOn ψ.range) :=
  (toInducedAutOn ψ.range).comp (ψ.codRestrict (Subgroup.normalizer (ψ.range : Set H))
    (fun s => mem_normalizer_range ψ s))

theorem innerHom_apply (ψ : S →* H) (s : S) :
    innerHom ψ s = toInducedAutOn ψ.range ⟨ψ s, mem_normalizer_range ψ s⟩ := rfl

theorem innerHom_spec [Group.IsPerfect S] (ψ : S →* H) (hψ : ψ.ker ≤ Subgroup.center S) :
    (∀ g, innerHom ψ g = 1 → g ∈ Subgroup.center S) ∧ (innerHom ψ).range.Normal ∧
      ∀ x : ↥(inducedAutOn ψ.range), (∀ y ∈ (innerHom ψ).range, x * y = y * x) → x = 1 := by
  classical
  set L : Subgroup H := ψ.range with hL
  set ε : S →* ↥(inducedAutOn L) := innerHom ψ with hε
  have hεapply : ∀ s, ε s = toInducedAutOn L ⟨ψ s, mem_normalizer_range ψ s⟩ := fun s => rfl
  refine ⟨?_, ?_, ?_⟩
  ·
    intro g hg
    rw [hεapply] at hg
    have hcomm := Lemma52Proof.commute_of_toInducedAutOn_eq_one L (mem_normalizer_range ψ g) hg
    refine mem_center_of_commutators_central fun t => hψ ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm (ψ t) ⟨t, rfl⟩)
  ·
    refine ⟨fun y hy x => ?_⟩
    obtain ⟨s, rfl⟩ := hy
    obtain ⟨n, rfl⟩ := MonoidHom.rangeRestrict_surjective (conjOnNormalizer L) x
    have hmem : (n : H) * ψ s * (n : H)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp n.2 (ψ s)).mp ⟨s, rfl⟩
    obtain ⟨s', hs'⟩ := hmem
    refine ⟨s', ?_⟩
    have : (⟨ψ s', mem_normalizer_range ψ s'⟩ : ↥(Subgroup.normalizer (L : Set H))) =
        n * ⟨ψ s, mem_normalizer_range ψ s⟩ * n⁻¹ := Subtype.ext hs'
    rw [hεapply s', this, hεapply s]
    simp only [map_mul, map_inv]
    rfl
  ·
    intro x hx
    obtain ⟨n, rfl⟩ := MonoidHom.rangeRestrict_surjective (conjOnNormalizer L) x
    have hmemL : ∀ s, (n : H) * ψ s * (n : H)⁻¹ * (ψ s)⁻¹ ∈ L := fun s =>
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp n.2 (ψ s)).mp ⟨s, rfl⟩) (L.inv_mem ⟨s, rfl⟩)
    have hcent : ∀ s, (⟨(n : H) * ψ s * (n : H)⁻¹ * (ψ s)⁻¹, hmemL s⟩ : ↥L) ∈
        Subgroup.center ↥L := by
      intro s
      set m : ↥(Subgroup.normalizer (L : Set H)) := ⟨ψ s, mem_normalizer_range ψ s⟩ with hm
      have hxc := hx (ε s) ⟨s, rfl⟩
      rw [hεapply] at hxc
      have hcomm : toInducedAutOn L n * toInducedAutOn L m =
          toInducedAutOn L m * toInducedAutOn L n :=
        hxc
      have h1 : toInducedAutOn L (n * m * n⁻¹ * m⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [hcomm]
        group
      have hc := Lemma52Proof.commute_of_toInducedAutOn_eq_one L (n * m * n⁻¹ * m⁻¹).2 h1
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g.1 g.2).symm
    have hct : ∀ s t : S, ψ s * ((n : H) * ψ t * (n : H)⁻¹ * (ψ t)⁻¹) =
        ((n : H) * ψ t * (n : H)⁻¹ * (ψ t)⁻¹) * ψ s := fun s t => by
      have := Subgroup.mem_center_iff.mp (hcent t) ⟨ψ s, ⟨s, rfl⟩⟩
      exact congrArg Subtype.val this
    let f : S →* ↥(Subgroup.center ↥L) :=
      { toFun := fun s => ⟨⟨(n : H) * ψ s * (n : H)⁻¹ * (ψ s)⁻¹, hmemL s⟩, hcent s⟩
        map_one' := Subtype.ext (Subtype.ext (by simp))
        map_mul' := fun s t => Subtype.ext (Subtype.ext (by
          show (n : H) * ψ (s * t) * (n : H)⁻¹ * (ψ (s * t))⁻¹ =
            ((n : H) * ψ s * (n : H)⁻¹ * (ψ s)⁻¹) * ((n : H) * ψ t * (n : H)⁻¹ * (ψ t)⁻¹)
          calc (n : H) * ψ (s * t) * (n : H)⁻¹ * (ψ (s * t))⁻¹
              = ((n : H) * ψ s * (n : H)⁻¹ * (ψ s)⁻¹) *
                (ψ s * ((n : H) * ψ t * (n : H)⁻¹ * (ψ t)⁻¹) * (ψ s)⁻¹) := by
                simp only [map_mul, mul_inv_rev]; group
            _ = _ := by rw [hct s t, mul_inv_cancel_right])) }
    have hf : f = 1 := eq_one_of_perfect_center f
    have hcommn : ∀ y ∈ L, (n : H) * y = y * (n : H) := by
      rintro _ ⟨s, rfl⟩
      have := congrArg
        (fun φ : S →* ↥(Subgroup.center ↥L) => ((φ s : ↥(Subgroup.center ↥L)) : ↥L)) hf
      have h2 : (n : H) * ψ s * (n : H)⁻¹ * (ψ s)⁻¹ = 1 := congrArg Subtype.val (this)
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
      exact h2
    exact Lemma52Proof.toInducedAutOn_eq_one_of_commute L n.2 hcommn

end Abstract

section Alpha

variable {Q : Type} [Group Q] [Finite Q]

theorem alphaOf_inducedImage_eq_bot_of_toral {t : StatedLieTag} {n p e : ℕ} (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e)
    (hSB : StrongLocalTwoBalanceToralPowOn 2 t fun _ _ _ => True)
    [Group.IsPerfect (modelUniv t n p e hp).K] (ψ : (modelUniv t n p e hp).K →* Q)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K) {B : Subgroup Q}
    (hB2 : ∀ x ∈ B, x * x = 1) (hBcard : Nat.card B = 8)
    (hBN : B ≤ Subgroup.normalizer (ψ.range : Set Q)) {Z : Subgroup Q} (hZcard : Nat.card Z = 2)
    (hZB : Z ≤ B) (hZ : ∀ z ∈ Z, ∀ y ∈ ψ.range, z * y = y * z)
    (hZ' : ∀ b ∈ B, (∀ y ∈ ψ.range, b * y = y * b) → b ∈ Z)
    (htoral : ∃ P : Subgroup (modelUniv t n p e hp).K, (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
      ∀ b ∈ B, ∃ x ∈ P, x * x = 1 ∧
        ∀ y ∈ ψ.range, b * y * b⁻¹ = ψ x * y * (ψ x)⁻¹) :
    alphaOf (inducedImage ψ.range B) = ⊥ := by
  classical
  obtain ⟨hcen, hnorm, hfaith⟩ := innerHom_spec ψ hker
  set L : Subgroup Q := ψ.range with hL
  set πB : ↥B →* ↥(inducedAutOn L) := (toInducedAutOn L).comp (Subgroup.inclusion hBN) with hπB
  have hπB_apply : ∀ b : ↥B, πB b = toInducedAutOn L ⟨b, hBN b.2⟩ := fun b => rfl
  have hF : inducedImage L B = πB.range := by
    ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨⟨b, hBN b.2⟩, b.2, rfl⟩
  have hker_iff : ∀ b : ↥B, πB b = 1 ↔ (b : Q) ∈ Z := by
    intro b
    rw [hπB_apply]
    constructor
    · intro h1
      exact hZ' b b.2 (Lemma52Proof.commute_of_toInducedAutOn_eq_one L (hBN b.2) h1)
    · intro h1
      exact Lemma52Proof.toInducedAutOn_eq_one_of_commute L (hBN b.2) (hZ _ h1)
  have hkerEq : πB.ker = Z.subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker_iff]
  have hcardker : Nat.card πB.ker = 2 := by
    rw [hkerEq]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZB).toEquiv).trans hZcard
  have hcardF : Nat.card (inducedImage L B) = 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup πB.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange πB).toEquiv, hcardker, hBcard] at h1
    rw [hF]
    omega
  have hFsq : ∀ f ∈ inducedImage L B, f * f = 1 := by
    intro f hf
    rw [hF] at hf
    obtain ⟨b, rfl⟩ := hf
    rw [← map_mul]
    have : b * b = 1 := Subtype.ext (hB2 b b.2)
    rw [this, map_one]
  have hFfaith : ∀ f ∈ inducedImage L B, f ≠ 1 → ¬ ∀ x ∈ (innerHom ψ).range, f * x = x * f :=
    fun f _ hf1 hall => hf1 (hfaith f hall)
  obtain ⟨P, hPc, hPact⟩ := htoral
  have htor : ToralActionPow 2 (innerHom ψ) (inducedImage L B) := by
    refine ⟨P, hPc, fun f hf => ?_⟩
    rw [hF] at hf
    obtain ⟨b, rfl⟩ := hf
    obtain ⟨x, hxP, hx2, hxact⟩ := hPact b b.2
    refine ⟨x, hxP, by rw [pow_two]; exact hx2, fun y => ?_⟩
    rw [innerHom_apply, innerHom_apply, hπB_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have := hxact (ψ y) ⟨y, rfl⟩
    show (b : Q) * ψ y * (b : Q)⁻¹ = ψ (x * y * x⁻¹)
    rw [map_mul, map_mul, map_inv]
    exact this
  have hSC := hSB n p e hp trivial hfund hadm hp2 h5 ↥(inducedAutOn L) (innerHom ψ)
    (fun g hg => hcen g (MonoidHom.mem_ker.mp hg)) hnorm (inducedImage L B) hcardF hFsq hFfaith htor
  rw [alphaOf_eq_bot_iff]
  refine ⟨fun a ha ha1 => ?_, ?_⟩
  · rw [eq_bot_iff, Subgroup.commutator_le]
    intro d hd g hg
    have hc := hSC.2 a ha ha1 d hd g hg
    have hu : ((g * d)⁻¹ * (d * g)) = 1 := by
      apply hfaith
      intro y hy
      have h1 := hc y hy
      calc (g * d)⁻¹ * (d * g) * y = (g * d)⁻¹ * ((d * g) * y * (d * g)⁻¹) * (d * g) := by group
        _ = (g * d)⁻¹ * ((g * d) * y * (g * d)⁻¹) * (d * g) := by
          rw [show (d * g) * y * (d * g)⁻¹ = d * g * y * (d * g)⁻¹ from rfl, h1]
        _ = y * ((g * d)⁻¹ * (d * g)) := by group
    have hdg : d * g = g * d := by
      have := congrArg (fun w => (g * d) * w) hu
      simpa [mul_assoc] using this
    rw [Subgroup.mem_bot, commutatorElement_def]
    calc d * g * d⁻¹ * g⁻¹ = (g * d) * d⁻¹ * g⁻¹ := by rw [hdg]
      _ = 1 := by group
  · rw [eq_bot_iff]
    intro d hd
    have hd' : d ∈ deltaCore (inducedImage L B) := hd
    rw [Subgroup.mem_bot]
    exact hfaith d fun y hy => hSC.1 d hd' y hy

end Alpha

end FrameVertex

end CFSG.ClassicalInvolution.Asc77
