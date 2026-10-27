module

public import CFSG.FeitThompson.Representations.FeitOneCharacterExtension
public import CFSG.FeitThompson.Representations.SmallerDegreeBlocksStrictFeit
public import CFSG.FeitThompson.Representations.CentralLayerDegreeSquareDivisor
public import CFSG.FeitThompson.Representations.CentralFrobeniusLayerDegreeSquareSum
public import CFSG.FeitThompson.Representations.CentralFrobeniusFamilyDescription
public import CFSG.FeitThompson.Representations.AbelianFrobeniusKernelTICoherence
public import CFSG.FeitThompson.Representations.InductionIntegerIsometryTISupport
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexOrder ComplexConjugate

section Restrict

variable {L G : Type*} [Group L] [Group G] [Fintype L] [Fintype G]

noncomputable def tauRestrict {S T : Set (L → ℂ)} (hTS : T ⊆ S)
    (τ : charSpanZero S →+ virtualChars G) : charSpanZero T →+ virtualChars G :=
  τ.comp (Submodule.inclusion (FeitExtension.charSpanZero_mono hTS)).toAddMonoidHom

omit [Fintype L] [Fintype G] in
theorem tauRestrict_apply {S T : Set (L → ℂ)} (hTS : T ⊆ S)
    (τ : charSpanZero S →+ virtualChars G) (f : charSpanZero T) :
    tauRestrict hTS τ f
      = τ (Submodule.inclusion (FeitExtension.charSpanZero_mono hTS) f) := (rfl)

omit [Fintype L] [Fintype G] in
theorem coe_tauRestrict_eq_coe_apply {S T : Set (L → ℂ)} (hTS : T ⊆ S)
    (τ : charSpanZero S →+ virtualChars G) (f : charSpanZero T) (g : charSpanZero S)
    (hfg : (f : L → ℂ) = (g : L → ℂ)) :
    ((tauRestrict hTS τ f : virtualChars G) : G → ℂ) = ((τ g : virtualChars G) : G → ℂ) := by
  rw [tauRestrict_apply]
  exact congrArg (fun z : virtualChars G => (z : G → ℂ)) (congrArg τ (Subtype.ext hfg))

omit [Fintype L] [Fintype G] in
theorem coe_tauRestrict_eq_coe_tauRestrict {S T U : Set (L → ℂ)} (hTS : T ⊆ S) (hUS : U ⊆ S)
    (τ : charSpanZero S →+ virtualChars G) (f : charSpanZero T) (g : charSpanZero U)
    (hfg : (f : L → ℂ) = (g : L → ℂ)) :
    ((tauRestrict hTS τ f : virtualChars G) : G → ℂ)
      = ((tauRestrict hUS τ g : virtualChars G) : G → ℂ) := by
  rw [coe_tauRestrict_eq_coe_apply hTS τ f
      (⟨(f : L → ℂ), FeitExtension.charSpanZero_mono hTS f.2⟩ : charSpanZero S) rfl,
    coe_tauRestrict_eq_coe_apply hUS τ g
      (⟨(g : L → ℂ), FeitExtension.charSpanZero_mono hUS g.2⟩ : charSpanZero S) rfl]
  exact congrArg (fun z : virtualChars G => (z : G → ℂ)) (congrArg τ (Subtype.ext hfg))

theorem cfInner_tauRestrict {S T : Set (L → ℂ)} (hTS : T ⊆ S)
    {τ : charSpanZero S →+ virtualChars G}
    (hτiso : ∀ f g : charSpanZero S,
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (f g : charSpanZero T) :
    cfInner (tauRestrict hTS τ f : G → ℂ) (tauRestrict hTS τ g : G → ℂ)
      = cfInner (f : L → ℂ) (g : L → ℂ) := by
  rw [tauRestrict_apply, tauRestrict_apply, hτiso]; rfl

omit [Fintype L] [Fintype G] in
theorem tauRestrict_apply_one {S T : Set (L → ℂ)} (hTS : T ⊆ S)
    {τ : charSpanZero S →+ virtualChars G}
    (hτ1 : ∀ f : charSpanZero S, (τ f : G → ℂ) 1 = 0) (f : charSpanZero T) :
    (tauRestrict hTS τ f : G → ℂ) 1 = 0 := by
  rw [tauRestrict_apply]; exact hτ1 _

theorem IsCoherent.congr_tau {S : Set (L → ℂ)} {τ₁ τ₂ : charSpanZero S →+ virtualChars G}
    (h : ∀ f, ((τ₁ f : virtualChars G) : G → ℂ) = ((τ₂ f : virtualChars G) : G → ℂ))
    (hc : IsCoherent S τ₁) : IsCoherent S τ₂ := by
  obtain ⟨ν, hν⟩ := isCoherent_iff.1 hc
  refine isCoherent_iff.2 ⟨ν, hν.inner_eq, fun f => ?_⟩
  exact Subtype.ext ((congrArg (fun z : virtualChars G => (z : G → ℂ)) (hν.eq_on_zero f)).trans
    (h f))

theorem isCoherent_tauRestrict_congr {X S T : Set (L → ℂ)} (hST : S = T)
    (hSX : S ⊆ X) (hTX : T ⊆ X) (τ : charSpanZero X →+ virtualChars G)
    (h : IsCoherent S (tauRestrict hSX τ)) : IsCoherent T (tauRestrict hTX τ) := by
  obtain ⟨ν, hν⟩ := isCoherent_iff.1 h
  have hspan : Submodule.span ℤ T ≤ Submodule.span ℤ S := by rw [hST]
  refine isCoherent_iff.2 ⟨ν.comp (Submodule.inclusion hspan).toAddMonoidHom, fun f g => ?_,
    fun f => ?_⟩
  · exact hν.inner_eq _ _
  · apply Subtype.ext
    have h1 : (Submodule.inclusion hspan) (Submodule.inclusion (charSpanZero_le T) f)
        = Submodule.inclusion (charSpanZero_le S)
          (⟨(f : L → ℂ), by rw [hST]; exact f.2⟩ : charSpanZero S) := Subtype.ext rfl
    change ((ν ((Submodule.inclusion hspan) (Submodule.inclusion (charSpanZero_le T) f)) :
        virtualChars G) : G → ℂ) = _
    rw [h1, hν.eq_on_zero]
    exact coe_tauRestrict_eq_coe_tauRestrict _ _ τ _ _ rfl

theorem isCoherent_of_isCoherent_tauRestrict_self {S : Set (L → ℂ)}
    (τ : charSpanZero S →+ virtualChars G)
    (h : IsCoherent S (tauRestrict (subset_refl S) τ)) : IsCoherent S τ :=
  IsCoherent.congr_tau (fun f => coe_tauRestrict_eq_coe_apply _ τ f f rfl) h

end Restrict

section OneStep

variable {L G : Type*} [Group L] [Group G] [Fintype L] [Fintype G]

theorem isCoherent_insert_of_subset {X : Set (L → ℂ)} (τ : charSpanZero X →+ virtualChars G)
    (hτiso : ∀ f g : charSpanZero X,
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (hτ1 : ∀ f : charSpanZero X, (τ f : G → ℂ) 1 = 0)
    {ι : Type*} [Fintype ι] {γ : ι → (L → ℂ)} (hinj : Function.Injective γ)
    (hIrr : ∀ k, γ k ∈ Irr L) {χ : L → ℂ} (hχIrr : χ ∈ Irr L) (hχnot : χ ∉ Set.range γ)
    (h2 : 2 ≤ Fintype.card ι) (k₀ : ι) {dd : ℤ} (hdd : 0 < dd)
    (hdegχ : χ 1 = (dd : ℂ) * γ k₀ 1)
    (hsub : insert χ (Set.range γ) ⊆ X)
    (hcoh : IsCoherent (Set.range γ) (tauRestrict ((Set.subset_insert _ _).trans hsub) τ))
    (hW : 2 * γ k₀ 1 * χ 1 < FeitExtension.degreeSqSum γ) :
    IsCoherent (insert χ (Set.range γ)) (tauRestrict hsub τ) := by
  classical
  obtain ⟨ν, hν⟩ := isCoherent_iff.1 hcoh
  let toSpan : virtualChars G →+ Submodule.span ℤ (Irr G) :=
    (Submodule.inclusion virtualChars_le_span_Irr).toAddMonoidHom
  have hcoeToSpan : ∀ z : virtualChars G, ((toSpan z : Submodule.span ℤ (Irr G)) : G → ℂ)
      = (z : G → ℂ) := fun _ => rfl
  let E : FeitExtension.OneCharExtension G γ χ dd k₀ :=
    { injective := hinj
      mem_Irr := hIrr
      chi_mem_Irr := hχIrr
      chi_notMem := hχnot
      two_le_card := h2
      tau := toSpan.comp (tauRestrict hsub τ)
      nu := toSpan.comp ν
      tau_isometry := fun f h => by
        rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hcoeToSpan, hcoeToSpan]
        exact cfInner_tauRestrict hsub hτiso f h
      tau_apply_one := fun f => by
        rw [AddMonoidHom.comp_apply, hcoeToSpan]
        exact tauRestrict_apply_one hsub hτ1 f
      nu_isometry := fun f h => by
        rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hcoeToSpan, hcoeToSpan]
        exact hν.inner_eq f h
      nu_eq_tau := fun f => by
        apply Subtype.ext
        rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hcoeToSpan, hcoeToSpan,
          hν.eq_on_zero f]
        exact coe_tauRestrict_eq_coe_tauRestrict _ _ τ _ _ rfl
      chi_apply_one := hdegχ
      d_pos := hdd }
  refine IsCoherent.congr_tau (τ₁ := E.tauVirt) (fun f => ?_)
    (E.isCoherent_tauVirt_of_lt_degreeSqSum hW)
  rw [FeitExtension.OneCharExtension.coe_tauVirt]
  exact hcoeToSpan (tauRestrict hsub τ f)

end OneStep

section DegreeOrdered

variable {L G : Type*} [Group L] [Group G] [Fintype L] [Fintype G]

theorem isCoherent_of_degree_ordered {XF : Finset (L → ℂ)}
    (hXIrr : (↑XF : Set (L → ℂ)) ⊆ Irr L) {deg : (L → ℂ) → ℕ}
    (hdeg : ∀ χ ∈ XF, χ 1 = (deg χ : ℂ)) {dmin : ℕ} (hdminpos : 0 < dmin)
    (hdminle : ∀ χ ∈ XF, dmin ≤ deg χ) (hdvd : ∀ χ ∈ XF, dmin ∣ deg χ)
    (h2 : ∃ χ ∈ XF, ∃ ψ ∈ XF, χ ≠ ψ ∧ deg χ = dmin ∧ deg ψ = dmin)
    (hFeit : ∀ χ ∈ XF, dmin < deg χ →
      2 * dmin * deg χ < ∑ ψ ∈ XF.filter (fun ψ => deg ψ < deg χ), deg ψ ^ 2)
    (τ : charSpanZero (↑XF : Set (L → ℂ)) →+ virtualChars G)
    (hτiso : ∀ f g : charSpanZero (↑XF : Set (L → ℂ)),
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (hτ1 : ∀ f : charSpanZero (↑XF : Set (L → ℂ)), (τ f : G → ℂ) 1 = 0) :
    IsCoherent (↑XF : Set (L → ℂ)) τ := by
  classical
  set B := XF.filter (fun ψ => deg ψ = dmin) with hB
  have hB2 : 2 ≤ B.card := by
    obtain ⟨χ, hχ, ψ, hψ, hne, hχd, hψd⟩ := h2
    exact Finset.one_lt_card.2 ⟨χ, Finset.mem_filter.2 ⟨hχ, hχd⟩, ψ,
      Finset.mem_filter.2 ⟨hψ, hψd⟩, hne⟩
  have hBXF : B ⊆ XF := Finset.filter_subset _ _
  have main : ∀ n : ℕ, ∀ T : Finset (L → ℂ), T.card = n → T ⊆ XF → B ⊆ T →
      (∀ φ ∈ T, ∀ ψ ∈ XF, deg ψ < deg φ → ψ ∈ T) →
      ∀ hTX : (↑T : Set (L → ℂ)) ⊆ (↑XF : Set (L → ℂ)),
        IsCoherent (↑T : Set (L → ℂ)) (tauRestrict hTX τ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro T hcard hTXF hBT hinit hTX
      by_cases huni : ∀ φ ∈ T, deg φ = dmin
      ·
        refine isCoherent_of_forall_apply_one_eq (d := (dmin : ℂ)) T.finite_toSet
          (fun φ hφ => hXIrr (hTX hφ)) (fun φ hφ => ?_) _
          (fun f g => cfInner_tauRestrict hTX hτiso f g)
          (fun f => tauRestrict_apply_one hTX hτ1 f)
        have hφT : φ ∈ T := hφ
        rw [hdeg φ (hTXF hφT), huni φ hφT]
      ·
        push Not at huni
        obtain ⟨χ, hχT, hχne⟩ := huni
        obtain ⟨χm, hχmT, hmax⟩ := T.exists_max_image deg ⟨χ, hχT⟩
        have hχmgt : dmin < deg χm :=
          lt_of_lt_of_le (lt_of_le_of_ne (hdminle χ (hTXF hχT)) (Ne.symm hχne)) (hmax χ hχT)
        set T' := T.erase χm with hT'def
        have hT'sub : T' ⊆ T := Finset.erase_subset _ _
        have hT'XF : T' ⊆ XF := hT'sub.trans hTXF
        have hχmnot : χm ∉ T' := Finset.notMem_erase _ _
        have hBT' : B ⊆ T' := by
          intro ψ hψ
          have hψd : deg ψ = dmin := (Finset.mem_filter.1 hψ).2
          refine Finset.mem_erase.2 ⟨fun h => ?_, hBT hψ⟩
          have hcontra : deg χm = dmin := by rw [← h]; exact hψd
          omega
        have hinit' : ∀ φ ∈ T', ∀ ψ ∈ XF, deg ψ < deg φ → ψ ∈ T' := by
          intro φ hφ ψ hψ hlt
          have hφT : φ ∈ T := hT'sub hφ
          refine Finset.mem_erase.2 ⟨fun h => ?_, hinit φ hφT ψ hψ hlt⟩
          have h1 : deg φ ≤ deg χm := hmax φ hφT
          have h2' : deg ψ = deg χm := by rw [h]
          omega
        have hT'card : T'.card = T.card - 1 := Finset.card_erase_of_mem hχmT
        have hTcardpos : 0 < T.card := Finset.card_pos.2 ⟨χm, hχmT⟩
        have hT'lt : T'.card < n := by omega
        set γ : ↥T' → (L → ℂ) := fun k => (k : L → ℂ) with hγ
        have hrange : Set.range γ = (↑T' : Set (L → ℂ)) := by
          ext x; simp [hγ]
        have hinsert : insert χm (Set.range γ) = (↑T : Set (L → ℂ)) := by
          rw [hrange, ← Finset.coe_insert, Finset.insert_erase hχmT]
        have hT'X : (↑T' : Set (L → ℂ)) ⊆ (↑XF : Set (L → ℂ)) :=
          fun x hx => hT'XF hx
        have hsub : insert χm (Set.range γ) ⊆ (↑XF : Set (L → ℂ)) := by
          rw [hinsert]; exact hTX
        have hcohT' : IsCoherent (↑T' : Set (L → ℂ)) (tauRestrict hT'X τ) :=
          ih T'.card hT'lt T' rfl hT'XF hBT' hinit' hT'X
        have hcohγ : IsCoherent (Set.range γ)
            (tauRestrict ((Set.subset_insert _ _).trans hsub) τ) :=
          isCoherent_tauRestrict_congr hrange.symm hT'X _ τ hcohT'
        obtain ⟨ψ₀, hψ₀B⟩ : B.Nonempty := Finset.card_pos.1 (by omega)
        have hψ₀T' : ψ₀ ∈ T' := hBT' hψ₀B
        have hψ₀deg : deg ψ₀ = dmin := (Finset.mem_filter.1 hψ₀B).2
        set k₀ : ↥T' := ⟨ψ₀, hψ₀T'⟩ with hk₀
        have hγk₀ : γ k₀ 1 = (dmin : ℂ) := by
          rw [hγ]
          simp only [hk₀]
          rw [hdeg ψ₀ (hT'XF hψ₀T'), hψ₀deg]
        obtain ⟨m, hm⟩ := hdvd χm (hTXF hχmT)
        have hmpos : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h0 | h0
          · rw [h0, mul_zero] at hm; omega
          · exact h0
        have hdegχm : χm 1 = ((m : ℤ) : ℂ) * γ k₀ 1 := by
          rw [hdeg χm (hTXF hχmT), hγk₀, hm]
          push_cast
          ring
        have hWnat : 2 * dmin * deg χm < ∑ ψ ∈ T', deg ψ ^ 2 := by
          refine lt_of_lt_of_le (hFeit χm (hTXF hχmT) hχmgt) ?_
          refine Finset.sum_le_sum_of_subset ?_
          intro ψ hψ
          obtain ⟨hψXF, hψlt⟩ := Finset.mem_filter.1 hψ
          refine Finset.mem_erase.2 ⟨fun h => ?_, hinit χm hχmT ψ hψXF hψlt⟩
          rw [h] at hψlt
          omega
        have hdegSq : FeitExtension.degreeSqSum γ = ((∑ ψ ∈ T', deg ψ ^ 2 : ℕ) : ℂ) := by
          rw [FeitExtension.degreeSqSum_eq]
          push_cast
          rw [← Finset.sum_coe_sort T' (fun ψ => ((deg ψ : ℂ)) ^ 2)]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hγ]
          exact congrArg (fun z : ℂ => z ^ 2) (hdeg (k : L → ℂ) (hT'XF k.2))
        have hW : 2 * γ k₀ 1 * χm 1 < FeitExtension.degreeSqSum γ := by
          rw [hdegSq, hγk₀, hdeg χm (hTXF hχmT)]
          have hcast : ((2 * dmin * deg χm : ℕ) : ℂ) < ((∑ ψ ∈ T', deg ψ ^ 2 : ℕ) : ℂ) :=
            Nat.cast_lt.mpr hWnat
          calc 2 * (dmin : ℂ) * (deg χm : ℂ) = ((2 * dmin * deg χm : ℕ) : ℂ) := by push_cast; ring
            _ < _ := hcast
        have hstep : IsCoherent (insert χm (Set.range γ)) (tauRestrict hsub τ) :=
          isCoherent_insert_of_subset τ hτiso hτ1 (γ := γ) Subtype.val_injective
            (fun k => hXIrr (hT'X k.2)) (hXIrr (hTX hχmT))
            (by rw [hrange]; exact hχmnot)
            (by rw [Fintype.card_coe]; exact le_trans hB2 (Finset.card_le_card hBT'))
            k₀ (by exact_mod_cast hmpos) hdegχm hsub hcohγ hW
        exact isCoherent_tauRestrict_congr hinsert hsub hTX τ hstep
  exact isCoherent_of_isCoherent_tauRestrict_self τ
    (main XF.card XF rfl (subset_refl _) hBXF (fun _ _ ψ hψ _ => hψ) (subset_refl _))

end DegreeOrdered

section NatDeg

variable {L : Type*} [One L]

noncomputable def natDeg (χ : L → ℂ) : ℕ := ⌊(χ 1).re⌋₊

theorem natDeg_eq {χ : L → ℂ} {n : ℕ} (h : χ 1 = (n : ℂ)) : natDeg χ = n := by
  rw [natDeg, h]; simp

theorem apply_one_eq_natDeg {χ : L → ℂ} (h : ∃ n : ℕ, χ 1 = (n : ℂ)) :
    χ 1 = (natDeg χ : ℂ) := by
  obtain ⟨n, hn⟩ := h; rw [natDeg_eq hn, hn]

end NatDeg

theorem three_le_of_prime_odd {p : ℕ} (hp : p.Prime) (hpodd : Odd p) : 3 ≤ p := by
  obtain ⟨k, hk⟩ := hpodd
  have h2 := hp.two_le
  omega

section Node

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L] {p a : ℕ}
  {P E Z : Subgroup ↥L} {A : Set G}

theorem isCoherent_of_coe_eq_indClassFun_centralLayer
    (hp : p.Prime) (hpodd : Odd p) (_ha : 1 ≤ a) (hLodd : Odd (Nat.card ↥L))
    [P.Normal] [Z.Normal] (hP : P ≠ ⊥) (_hE : E ≠ ⊥) (hPcard : Nat.card ↥P = p ^ a)
    (hPE : P ⊔ E = ⊤) (hinf : P ⊓ E = ⊥)
    (hC : ∀ u ∈ E, u ≠ 1 → P ⊓ Subgroup.centralizer {u} = ⊥)
    (hZ : Z ≠ ⊥) (hZP : Z ≤ P) (hZc : Z ≤ Subgroup.centralizer (P : Set ↥L))
    (hA : A = ((P.map L.subtype : Subgroup G) : Set G) \ {1})
    (hstab : ∀ g : G, (fun x => g⁻¹ * x * g) '' A = A ↔ g ∈ L)
    (hpair : ∀ g k : G, (fun x => g⁻¹ * x * g) '' A = (fun x => k⁻¹ * x * k) '' A ∨
      ((fun x => g⁻¹ * x * g) '' A) ∩ ((fun x => k⁻¹ * x * k) '' A) = ∅)
    (τ : charSpanZero (indFamDetect P (Z.subgroupOf P)) →+ virtualChars G)
    (hτ : ∀ f, (τ f : G → ℂ) = indClassFun L (f : ↥L → ℂ)) :
    IsCoherent (indFamDetect P (Z.subgroupOf P)) τ := by
  classical
  have hp3 : 3 ≤ p := three_le_of_prime_odd hp hpodd
  have hfreeZ : ∀ u ∈ E, u ≠ 1 → ∀ z ∈ Z, u * z = z * u → z = 1 := by
    intro u hu hu1 z hz hcomm
    have hmem : z ∈ P ⊓ Subgroup.centralizer ({u} : Set ↥L) :=
      Subgroup.mem_inf.2 ⟨hZP hz, Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm⟩
    rw [hC u hu hu1, Subgroup.mem_bot] at hmem
    exact hmem
  have hXeq : indFamDetect P (Z.subgroupOf P) = irrDetect ℂ Z :=
    indFamDetect_eq_irrDetect (E := E) hZP hZc hPE hfreeZ
  have hXIrr : indFamDetect P (Z.subgroupOf P) ⊆ Irr ↥L := by
    intro χ hχ
    rw [hXeq] at hχ
    rw [← irrChar_eq_Irr]
    exact (mem_irrDetect.1 hχ).1
  have hXind : indFamDetect P (Z.subgroupOf P) ⊆ indFam P (Irr ↥P) := by
    have h := indFamDetect_subset_indFam_irrChar P (Z.subgroupOf P)
    rwa [irrChar_eq_Irr] at h
  have hTI : IsTIWithNormalizer A L :=
    isTIWithNormalizer_of_stabilizer_eq_and_pairwise hP hA hstab hpair
  have hle : charSpanZero (indFamDetect P (Z.subgroupOf P)) ≤ dadeZDomain L A :=
    charSpanZero_le_dadeZDomain (H := P) hXind hXIrr hA
  have hτiso : ∀ f g : charSpanZero (indFamDetect P (Z.subgroupOf P)),
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : ↥L → ℂ) (g : ↥L → ℂ) := by
    intro f g
    rw [hτ, hτ]
    exact hTI.cfInner_indClassFun (mem_dadeDomain_of_mem_dadeZDomain (hle f.2))
      (mem_dadeDomain_of_mem_dadeZDomain (hle g.2))
  have hτ1 : ∀ f : charSpanZero (indFamDetect P (Z.subgroupOf P)), (τ f : G → ℂ) 1 = 0 := by
    intro f
    rw [hτ]
    exact hTI.indClassFun_apply_one fun x hx => (mem_dadeZDomain.1 (hle f.2)).2 x hx
  have hXFcoe : (↑(indFamDetectFinset P (Z.subgroupOf P)) : Set (↥L → ℂ))
      = indFamDetect P (Z.subgroupOf P) := coe_indFamDetectFinset P (Z.subgroupOf P)
  have hmemXF : ∀ {χ : ↥L → ℂ},
      χ ∈ indFamDetectFinset P (Z.subgroupOf P) ↔ χ ∈ indFamDetect P (Z.subgroupOf P) :=
    fun {χ} => mem_indFamDetectFinset
  have hepos : 0 < P.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hZPc : Z ≤ P ⊓ Subgroup.centralizer (P : Set ↥L) := le_inf hZP hZc
  have hdegex : ∀ χ ∈ indFamDetectFinset P (Z.subgroupOf P),
      ∃ b : ℕ, χ 1 = ((P.index * p ^ b : ℕ) : ℂ) ∧
        (P.index * p ^ b) ^ 2 ∣ P.index ^ 2 * Z.relIndex P := fun χ hχ =>
    exists_degree_eq_index_mul_pow_and_sq_dvd hp hPcard hZPc (hmemXF.1 hχ)
  have hdeg : ∀ χ ∈ indFamDetectFinset P (Z.subgroupOf P), χ 1 = (natDeg χ : ℂ) := by
    intro χ hχ
    obtain ⟨b, hb, -⟩ := hdegex χ hχ
    exact apply_one_eq_natDeg ⟨P.index * p ^ b, hb⟩
  have hdegpow : ∀ χ ∈ indFamDetectFinset P (Z.subgroupOf P),
      ∃ b : ℕ, natDeg χ = P.index * p ^ b := by
    intro χ hχ
    obtain ⟨b, hb, -⟩ := hdegex χ hχ
    exact ⟨b, natDeg_eq hb⟩
  have hdvdM : ∀ χ ∈ indFamDetectFinset P (Z.subgroupOf P),
      natDeg χ ^ 2 ∣ P.index ^ 2 * Z.relIndex P := by
    intro χ hχ
    obtain ⟨b, hb, hsq⟩ := hdegex χ hχ
    rw [natDeg_eq hb]; exact hsq
  have hMsum : P.index ^ 2 * Z.relIndex P ∣
      ∑ χ ∈ indFamDetectFinset P (Z.subgroupOf P), natDeg χ ^ 2 := by
    obtain ⟨t, ht, hsum⟩ := exists_sum_sq_degree_indFamDetect (E := E) hZP hZc hPE hfreeZ hinf hZ
    have hcast : ((∑ χ ∈ indFamDetectFinset P (Z.subgroupOf P), natDeg χ ^ 2 : ℕ) : ℂ)
        = ((t * (P.index ^ 2 * Z.relIndex P) : ℕ) : ℂ) := by
      push_cast
      rw [show (∑ χ ∈ indFamDetectFinset P (Z.subgroupOf P), (natDeg χ : ℂ) ^ 2)
          = ∑ χ ∈ indFamDetectFinset P (Z.subgroupOf P), χ 1 ^ 2 from
        Finset.sum_congr rfl fun χ hχ => by rw [hdeg χ hχ], hsum]
    have hnat : ∑ χ ∈ indFamDetectFinset P (Z.subgroupOf P), natDeg χ ^ 2
        = t * (P.index ^ 2 * Z.relIndex P) := by exact_mod_cast hcast
    exact ⟨t, by rw [hnat]; ring⟩
  have hXne : (indFamDetect P (Z.subgroupOf P)).Nonempty :=
    indFamDetect_nonempty (E := E) hZP hZc hPE hfreeZ hZ
  have hXFne : (indFamDetectFinset P (Z.subgroupOf P)).Nonempty := by
    obtain ⟨χ, hχ⟩ := hXne; exact ⟨χ, hmemXF.2 hχ⟩
  obtain ⟨χ₀, hχ₀XF, hχ₀min⟩ :=
    (indFamDetectFinset P (Z.subgroupOf P)).exists_min_image natDeg hXFne
  have hdminpos : 0 < natDeg χ₀ := by
    obtain ⟨b, hb⟩ := hdegpow χ₀ hχ₀XF
    rw [hb]
    exact Nat.mul_pos hepos (pow_pos hp.pos b)
  have hdvdmin : ∀ χ ∈ indFamDetectFinset P (Z.subgroupOf P), natDeg χ₀ ∣ natDeg χ := by
    intro χ hχ
    obtain ⟨b, hb⟩ := hdegpow χ hχ
    obtain ⟨b₀, hb₀⟩ := hdegpow χ₀ hχ₀XF
    rw [hb₀, hb]
    exact mul_pow_dvd_mul_pow_of_le hepos hp.one_lt (by rw [← hb₀, ← hb]; exact hχ₀min χ hχ)
  have h2 : ∃ χ ∈ indFamDetectFinset P (Z.subgroupOf P),
      ∃ ψ ∈ indFamDetectFinset P (Z.subgroupOf P),
        χ ≠ ψ ∧ natDeg χ = natDeg χ₀ ∧ natDeg ψ = natDeg χ₀ := by
    have hχ₀X : χ₀ ∈ irrDetect ℂ Z := by rw [← hXeq]; exact hmemXF.1 hχ₀XF
    have hconjXF : (fun x => conj (χ₀ x)) ∈ indFamDetectFinset P (Z.subgroupOf P) :=
      hmemXF.2 (by rw [hXeq]; exact conj_mem_irrDetect hχ₀X)
    have hne : χ₀ ≠ fun x => conj (χ₀ x) := by
      obtain ⟨x, hx⟩ := exists_im_ne_zero_of_mem_irrDetect hLodd hχ₀X
      intro h
      exact hx (Complex.conj_eq_iff_im.1 (congrFun h x).symm)
    have hdegconj : natDeg (fun x => conj (χ₀ x)) = natDeg χ₀ := by
      refine natDeg_eq (n := natDeg χ₀) ?_
      show conj (χ₀ 1) = ((natDeg χ₀ : ℕ) : ℂ)
      rw [hdeg χ₀ hχ₀XF]
      simp
    exact ⟨χ₀, hχ₀XF, (fun x => conj (χ₀ x)), hconjXF, hne, rfl, hdegconj⟩
  have hFeit : ∀ χ ∈ indFamDetectFinset P (Z.subgroupOf P), natDeg χ₀ < natDeg χ →
      2 * natDeg χ₀ * natDeg χ < ∑ ψ ∈ (indFamDetectFinset P (Z.subgroupOf P)).filter
        (fun ψ => natDeg ψ < natDeg χ), natDeg ψ ^ 2 := by
    intro χ hχ hlt
    set XF := indFamDetectFinset P (Z.subgroupOf P) with hXFdef
    have hbex : ∀ i : ↥XF, ∃ b : ℕ, natDeg (i : ↥L → ℂ) = P.index * p ^ b :=
      fun i => hdegpow _ i.2
    have hmin : IsLeast (Set.range (fun i : ↥XF => natDeg (i : ↥L → ℂ))) (natDeg χ₀) := by
      refine ⟨⟨⟨χ₀, hχ₀XF⟩, rfl⟩, ?_⟩
      rintro m ⟨i, rfl⟩
      exact hχ₀min _ i.2
    have hsum : ∑ i : ↥XF, natDeg (i : ↥L → ℂ) ^ 2 = ∑ ψ ∈ XF, natDeg ψ ^ 2 :=
      Finset.sum_coe_sort XF (fun ψ => natDeg ψ ^ 2)
    have key := two_mul_min_mul_lt_sum_sq_filter_lt (I := ↥XF)
      (d := fun i : ↥XF => natDeg (i : ↥L → ℂ)) (b := fun i : ↥XF => (hbex i).choose)
      (M := P.index ^ 2 * Z.relIndex P) hp3 hepos (fun i => (hbex i).choose_spec)
      (fun i => hdvdM _ i.2) (by rw [hsum]; exact hMsum) hmin (j := ⟨χ, hχ⟩) hlt
    have hconv : ∑ i ∈ Finset.univ.filter
          (fun i : ↥XF => natDeg (i : ↥L → ℂ) < natDeg χ), natDeg (i : ↥L → ℂ) ^ 2
        = ∑ ψ ∈ XF.filter (fun ψ => natDeg ψ < natDeg χ), natDeg ψ ^ 2 := by
      rw [Finset.sum_filter, Finset.sum_filter,
        Finset.sum_coe_sort XF (fun ψ => if natDeg ψ < natDeg χ then natDeg ψ ^ 2 else 0)]
    rw [← hconv]
    exact key
  have hXFsub : (↑(indFamDetectFinset P (Z.subgroupOf P)) : Set (↥L → ℂ))
      ⊆ indFamDetect P (Z.subgroupOf P) := by rw [hXFcoe]
  have hmain : IsCoherent (↑(indFamDetectFinset P (Z.subgroupOf P)) : Set (↥L → ℂ))
      (tauRestrict hXFsub τ) :=
    isCoherent_of_degree_ordered (by rw [hXFcoe]; exact hXIrr) hdeg hdminpos
      (fun χ hχ => hχ₀min χ hχ) hdvdmin h2 hFeit _
      (fun f g => cfInner_tauRestrict hXFsub hτiso f g)
      (fun f => tauRestrict_apply_one hXFsub hτ1 f)
  exact isCoherent_of_isCoherent_tauRestrict_self τ
    (isCoherent_tauRestrict_congr hXFcoe hXFsub (subset_refl _) τ hmain)

theorem isCoherent_indCharSpanZeroHom_centralLayer
    (hp : p.Prime) (hpodd : Odd p) (ha : 1 ≤ a) (hLodd : Odd (Nat.card ↥L))
    [P.Normal] [Z.Normal] (hP : P ≠ ⊥) (hE : E ≠ ⊥) (hPcard : Nat.card ↥P = p ^ a)
    (hPE : P ⊔ E = ⊤) (hinf : P ⊓ E = ⊥)
    (hC : ∀ u ∈ E, u ≠ 1 → P ⊓ Subgroup.centralizer {u} = ⊥)
    (hZ : Z ≠ ⊥) (hZP : Z ≤ P) (hZc : Z ≤ Subgroup.centralizer (P : Set ↥L))
    (hA : A = ((P.map L.subtype : Subgroup G) : Set G) \ {1})
    (hstab : ∀ g : G, (fun x => g⁻¹ * x * g) '' A = A ↔ g ∈ L)
    (hpair : ∀ g k : G, (fun x => g⁻¹ * x * g) '' A = (fun x => k⁻¹ * x * k) '' A ∨
      ((fun x => g⁻¹ * x * g) '' A) ∩ ((fun x => k⁻¹ * x * k) '' A) = ∅)
    (hXind : indFamDetect P (Z.subgroupOf P) ⊆ indFam P (Irr ↥P))
    (hXIrr : indFamDetect P (Z.subgroupOf P) ⊆ Irr ↥L) :
    IsCoherent (indFamDetect P (Z.subgroupOf P))
      ((isTIWithNormalizer_of_stabilizer_eq_and_pairwise hP hA hstab hpair).indCharSpanZeroHom
        (charSpanZero_le_dadeZDomain (H := P) hXind hXIrr hA)) :=
  isCoherent_of_coe_eq_indClassFun_centralLayer hp hpodd ha hLodd hP hE hPcard hPE hinf hC hZ
    hZP hZc hA hstab hpair _ (IsTIWithNormalizer.coe_indCharSpanZeroHom _ _)

end Node

end CFSG.FeitThompson

end
