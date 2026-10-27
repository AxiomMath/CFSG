module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemL
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZData
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7E64Facts
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf63E64Aut
import CFSG.ClassicalInvolution.Asc77.AscOddCoreNormalEng
import CFSG.ClassicalInvolution.AschTight.Sec7L714F
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Cover

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

namespace LL1

section Conj

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem conjSub_rLayerSub_le (hΩ : HypOmegaGen Ω) {g : G} {V : Subgroup G}
    (hgV : conjSub g V = V) : conjSub g (rLayerSub Ω V) ≤ rLayerSub Ω V := by
  unfold rLayerSub
  rw [conjSub, Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun Q hQ => iSup_le fun hQC => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have h1 : conjSub g Q ∈ RSet Ω := Q3CL.Thompson.conjSub_mem_RSet hΩ hQ g
  have h2 : conjSub g Q ≤ Subgroup.centralizer (V : Set G) := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : g⁻¹ * v * g ∈ V := by
      rw [← hgV] at hv
      exact mem_conjSub_iff.mp hv
    have := Subgroup.mem_centralizer_iff.mp (hQC hx) _ hv'
    calc v * x = g * ((g⁻¹ * v * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * v * g)) * g⁻¹ := by rw [this]
      _ = x * v := by group
  exact le_iSup₂_of_le (conjSub g Q) h1 (le_iSup_of_le h2 le_rfl)

theorem conjSub_rLayerSub_eq (hΩ : HypOmegaGen Ω) {g : G} {V : Subgroup G}
    (hgV : conjSub g V = V) : conjSub g (rLayerSub Ω V) = rLayerSub Ω V := by
  have hgV' : conjSub g⁻¹ V = V := by
    conv_lhs => rw [← hgV]
    rw [conjSub_inv_conjSub]
  refine le_antisymm (conjSub_rLayerSub_le hΩ hgV) ?_
  have h := conjSub_mono (n := g) (conjSub_rLayerSub_le hΩ hgV')
  rwa [conjSub_conjSub_inv] at h

@[expose] noncomputable def conjAutOf (g : G) {X : Subgroup G} (hX : conjSub g X = X) : MulAut ↥X :=
  (Subgroup.equivMapOfInjective X (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
    (MulEquiv.subgroupCongr hX)

theorem coe_conjAutOf (g : G) {X : Subgroup G} (hX : conjSub g X = X) (x : ↥X) :
    ((conjAutOf g hX x : ↥X) : G) = g * x * g⁻¹ := rfl

@[expose] noncomputable def secConjAut (g : G) {X : Subgroup G} (hX : conjSub g X = X) :
    MulAut (SecQuot X) :=
  QuotientGroup.congr (classicalInvolutionOddCore ↥X) (classicalInvolutionOddCore ↥X)
    (conjAutOf g hX) (CFSG.ComponentClassification.OddCore.equiv_invariant (conjAutOf g hX))

theorem secConjAut_mk (g : G) {X : Subgroup G} (hX : conjSub g X = X) (x : ↥X) :
    secConjAut g hX (QuotientGroup.mk' (classicalInvolutionOddCore ↥X) x) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) (conjAutOf g hX x) :=
  QuotientGroup.congr_mk _ _ _ _ x

theorem secConjAut_mul (g g' : G) {X : Subgroup G} (hX : conjSub (g * g') X = X)
    (hg : conjSub g X = X) (hg' : conjSub g' X = X) (x : SecQuot X) :
    secConjAut (g * g') hX x = secConjAut g hg (secConjAut g' hg' x) := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥X) x
  rw [secConjAut_mk, secConjAut_mk, secConjAut_mk]
  congr 1
  apply Subtype.ext
  rw [coe_conjAutOf, coe_conjAutOf, coe_conjAutOf]
  group

theorem secConjAut_one {X : Subgroup G} (hX : conjSub (1 : G) X = X) (x : SecQuot X) :
    secConjAut 1 hX x = x := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥X) x
  rw [secConjAut_mk]
  congr 1
  apply Subtype.ext
  rw [coe_conjAutOf]
  group

theorem mem_normalizer_of_conjSub_eq {g : G} {H : Subgroup G} (h : conjSub g H = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact conj_mem_conjSub hx
  · intro hx
    rw [← h, mem_conjSub_iff] at hx
    simpa [mul_assoc] using hx

theorem conjSub_eq_of_le {g : G} {H : Subgroup G} (h : conjSub g H ≤ H) : conjSub g H = H :=
  Subgroup.eq_of_le_of_card_ge h (by
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective])

theorem mem_normalizer_sup {g : G} {A B : Subgroup G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conjSub_eq ?_
  rw [conjSub, Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) (conjSub_eq_of_mem_normalizer hA) (conjSub_eq_of_mem_normalizer hB)

theorem mem_normalizer_inf {g : G} {A B : Subgroup G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA y, hB y]

end Conj

section Ident

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem toHom_of_aeIdentOn {n : ℕ} {𝒜 : Set (Finset (Fin n))} {H : Subgroup (AE.AEQ n)}
    (hgen : TC.Thin.pSpan Φ = ⊤) (I : TC.Thin.AEIdentOn Φ n 𝒜 H) :
    ∃ f : X →* AE.AEQ n, f.range = H ∧ f.ker ≤ Subgroup.center X ∧
      ∀ L ∈ Φ, (L.subgroupOf (TC.Thin.pSpan Φ)).map I.φ = L.map f := by
  have hmem : ∀ x : X, x ∈ TC.Thin.pSpan Φ := fun x => hgen ▸ Subgroup.mem_top x
  let ε : X →* ↥(TC.Thin.pSpan Φ) :=
    { toFun := fun x => ⟨x, hmem x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hεinj : Function.Injective ε := fun x y h => congrArg Subtype.val h
  have hεsurj : Function.Surjective ε := fun z => ⟨z.1, Subtype.ext rfl⟩
  refine ⟨I.φ.comp ε, ?_, ?_, fun L hL => ?_⟩
  · refine Eq.trans ?_ I.range_eq
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨ε x, rfl⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := hεsurj z
      exact ⟨x, rfl⟩
  · intro x hx
    have hx' : ε x ∈ I.φ.ker := hx
    have hc := I.ker_le hx'
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    exact hεinj (by rw [map_mul, map_mul]; exact hc (ε g))
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.1, Subgroup.mem_subgroupOf.mp hz, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ε x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

theorem exists_induced_aut_center {H : Type} [Group H] (f : X →* H) (hf : Function.Surjective f)
    (hNc : f.ker ≤ Subgroup.center X) (hZ : Subgroup.center H = ⊥) (α : MulAut X) :
    ∃ β : MulAut H, ∀ x : X, β (f x) = f (α x) := by
  have hle : f.ker.map α.toMonoidHom ≤ f.ker := by
    rintro _ ⟨m, hm, rfl⟩
    have hcen : α m ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := Subgroup.mem_center_iff.mp (hNc hm) (α.symm g)
      calc g * α m = α (α.symm g * m) := by simp
        _ = α (m * α.symm g) := by rw [h1]
        _ = α m * g := by simp
    have hc2 : f (α m) ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro g'
      obtain ⟨g, rfl⟩ := hf g'
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcen g]
    rw [hZ, Subgroup.mem_bot] at hc2
    exact hc2
  have heq : f.ker.map α.toMonoidHom = f.ker :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective α.injective])
  have heq' : f.ker.map (α : X →* X) = f.ker := heq
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  refine ⟨e.symm.trans ((QuotientGroup.congr f.ker f.ker α heq').trans e), fun x => ?_⟩
  have h1 : e.symm (f x) = (x : X ⧸ f.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  have h2 := QuotientGroup.congr_mk f.ker f.ker α heq' x
  calc (e.symm.trans ((QuotientGroup.congr f.ker f.ker α heq').trans e)) (f x)
      = e (QuotientGroup.congr f.ker f.ker α heq' (e.symm (f x))) := rfl
    _ = e (QuotientGroup.congr f.ker f.ker α heq' (x : X ⧸ f.ker)) := by rw [h1]
    _ = e (((α x : X)) : X ⧸ f.ker) := by rw [h2]
    _ = f (α x) := rfl

end Ident

theorem bool_eq_of_ne {a b c : Bool} (h1 : b ≠ c) (h2 : a ≠ b) : a = c := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem twin_of_commute {α β : Finset (Fin 7)} {h : α.card = 4} {h' : β.card = 4} {b b' : Bool}
    (hc : ∀ x ∈ AE.memBar α h b, ∀ y ∈ AE.memBar β h' b', x * y = y * x) : α = β ∧ b ≠ b' := by
  classical
  have hab : α = β := by
    by_contra hne
    have hd := AE.disjoint_of_zBar_comm hne (c := b') (h := h)
      (fun y hy => hc _ (AE.zBar_mem_memBar α h b) y hy)
    have h1 := Finset.card_union_of_disjoint hd
    have h2 := Finset.card_le_univ (α ∪ β)
    rw [h1, h, h', Fintype.card_fin] at h2
    omega
  subst hab
  refine ⟨rfl, fun hbb => ?_⟩
  subst hbb
  obtain ⟨x, hx, x', hx', hxx'⟩ := AE.exists_not_comm_memBar (by norm_num) α h b
  exact hxx' (hc x hx x' hx')

section Syl

variable {G : Type} [Group G] [Finite G]

theorem isSylow2In_inf_sup {K O H T : Subgroup G} (hOodd : Odd (Nat.card O))
    (hKO : K ≤ Subgroup.normalizer (O : Set G)) (hOK : O ≤ Subgroup.normalizer (K : Set G))
    (hT : IsSylow2In T H) (hMH : K ⊔ O ≤ H)
    (hHN : H ≤ Subgroup.normalizer ((K ⊔ O : Subgroup G) : Set G)) :
    IsSylow2In (T ⊓ (K ⊔ O)) K := by
  set M := K ⊔ O with hMdef
  have hT₀ : IsSylow2In (T ⊓ M) M := isSylow2In_inf_of_le_normalizer hT hMH hHN
  obtain ⟨R₀, hR₀, -⟩ := IsSylow2In.exists_ge (P := K) (T := ⊥) IsPGroup.of_bot bot_le
  have hMO : M ≤ Subgroup.normalizer (O : Set G) := sup_le hKO Subgroup.le_normalizer
  have hOle : O ≤ oddCoreOf M := AscFusion.le_oddCoreOf_of_normal_odd_gen le_sup_right hMO hOodd
  have hM : M = K ⊔ oddCoreOf M :=
    le_antisymm (sup_le le_sup_left (hOle.trans le_sup_right))
      (sup_le le_sup_left (oddCoreOf_le_self M))
  have hR₀M : IsSylow2In R₀ M := T8R.isSylow2In_of_eq_sup_oddCoreOf le_sup_left hM hR₀
  obtain ⟨y, hyM, hle⟩ := exists_conj_of_isSylow2In hR₀M hT₀.2.1 hT₀.1
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hOK
  have hyK : conjSub y K = K := conjSub_eq_of_mem_normalizer (hMK hyM)
  have hTK : T ⊓ M ≤ K := hle.trans (by rw [← hyK]; exact conjSub_mono hR₀.1)
  exact T8.isSylow2In_of_le_of_le hT₀ hTK le_sup_left

end Syl

section Twins


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y} {Z : Subgroup Y}

theorem conjSub_twins_of_odd (hc : P23Cfg n Y R S t K' W u e g) {o : Y}
    (hoC : o ∈ Subgroup.centralizer ({t} : Set Y)) (ho : Odd (orderOf o)) :
    conjSub o (tightCore R) = tightCore R ∧ conjSub o K' = K' := by
  rcases p23_conj_twins hc hoC with h | ⟨h1, h2⟩
  · exact h
  · exfalso
    have hsq : conjSub (o * o) (tightCore R) = tightCore R := by
      rw [conjSub_mul, h1, h2]
    obtain ⟨k, hk⟩ := ho
    have h1o : o ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one o
    have hpow : (o * o) ^ (k + 1) = o := by
      rw [← sq, ← pow_mul, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ, h1o, one_mul]
    have hfix : ∀ m : ℕ, conjSub ((o * o) ^ m) (tightCore R) = tightCore R := by
      intro m
      induction m with
      | zero => rw [pow_zero, conjSub_one]
      | succ m ih => rw [pow_succ, conjSub_mul, hsq, ih]
    have := hfix (k + 1)
    rw [hpow, h1] at this
    exact hc.std.hne this

theorem exists_cent_twin_sylows (hc : P23Cfg n Y R S t K' W u e g) (hZ : P23ZData t u e Z) :
    ∃ R₁ R₁' : Subgroup Y, IsSylow2In R₁ (tightCore R) ∧ IsSylow2In R₁' K' ∧ Commutes R₁ R₁' ∧
      (∀ z ∈ Z, ∀ r ∈ R₁, z * r = r * z) ∧ ∀ z ∈ Z, ∀ r ∈ R₁', z * r = r * z := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hK' : K' ∈ Om R := hc.std.hK'.1
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  set O := oddCoreOf C with hOdef
  set K₀ := tightCore R with hK₀def
  have hKC : K₀ ≤ C := le_centralizer_of_unique hz
  have hK'C : K' ≤ C := le_centralizer_of_unique hz'
  have hOC : O ≤ C := oddCoreOf_le_self C
  have hCO : C ≤ Subgroup.normalizer (O : Set Y) := Sec7.le_normalizer_oddCoreOf C
  have hOodd : Odd (Nat.card O) := oddCoreOf_odd_natCard C
  have hZC : Z ≤ C := hZ.le_t
  have hZ2 : IsPGroup 2 Z := hZ.isPGroup
  have hoddK : ∀ o ∈ O, conjSub o K₀ = K₀ ∧ conjSub o K' = K' := fun o ho =>
    conjSub_twins_of_odd hc (hOC ho)
      (Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard O ho))
  have hON : O ≤ Subgroup.normalizer (K₀ : Set Y) := fun o ho =>
    mem_normalizer_of_conjSub_eq (hoddK o ho).1
  have hON' : O ≤ Subgroup.normalizer (K' : Set Y) := fun o ho =>
    mem_normalizer_of_conjSub_eq (hoddK o ho).2
  have hK'K : K' ≤ Subgroup.normalizer (K₀ : Set Y) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK' hK hc.std.hne hz' hz
  have hKK' : K₀ ≤ Subgroup.normalizer (K' : Set Y) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK hK' (Ne.symm hc.std.hne) hz hz'
  have hZN : ∀ {L : Subgroup Y}, L ≤ K₀ ⊔ K' →
      Z ≤ Subgroup.normalizer ((L ⊔ O : Subgroup Y) : Set Y) := by
    intro L hL z hz
    refine mem_normalizer_of_conjSub_eq (conjSub_eq_of_le ?_)
    rw [conjSub, Subgroup.map_sup]
    refine sup_le (fun x hx => ?_) ?_
    · obtain ⟨l, hl, rfl⟩ := hx
      have hcO := p23_zdata_comm_twins hc hZ hz (hL hl)
      have : (MulAut.conj z).toMonoidHom l = (z * l * z⁻¹ * l⁻¹) * l := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcO) (Subgroup.mem_sup_left hl)
    · have := conjSub_eq_of_mem_normalizer (hCO (hZC hz))
      exact (le_of_eq this).trans le_sup_right
  set H := (K₀ ⊔ K') ⊔ (Z ⊔ O) with hHdef
  have hNsup : ∀ {L : Subgroup Y}, L ≤ K₀ ⊔ K' → L ≤ Subgroup.normalizer (O : Set Y) →
      K₀ ≤ Subgroup.normalizer ((L ⊔ O : Subgroup Y) : Set Y) →
      K' ≤ Subgroup.normalizer ((L ⊔ O : Subgroup Y) : Set Y) →
      H ≤ Subgroup.normalizer ((L ⊔ O : Subgroup Y) : Set Y) := by
    intro L hL _ h1 h2
    refine sup_le (sup_le h1 h2) (sup_le (hZN hL) ?_)
    intro o ho
    exact (le_sup_right : O ≤ L ⊔ O).trans Subgroup.le_normalizer ho
  have hHN₀ : H ≤ Subgroup.normalizer ((K₀ ⊔ O : Subgroup Y) : Set Y) :=
    hNsup le_sup_left (hKC.trans hCO) (le_sup_left.trans Subgroup.le_normalizer)
      (fun k hk => mem_normalizer_sup (hK'K hk) (hCO (hK'C hk)))
  have hHN₁ : H ≤ Subgroup.normalizer ((K' ⊔ O : Subgroup Y) : Set Y) :=
    hNsup le_sup_right (hK'C.trans hCO) (fun k hk => mem_normalizer_sup (hKK' hk) (hCO (hKC hk)))
      (le_sup_left.trans Subgroup.le_normalizer)
  have hM₀H : K₀ ⊔ O ≤ H :=
    sup_le (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_right)
  have hM₁H : K' ⊔ O ≤ H :=
    sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right)
  obtain ⟨T, hT, hZT⟩ := IsSylow2In.exists_ge hZ2 (le_sup_left.trans le_sup_right : Z ≤ H)
  have hR₁ := isSylow2In_inf_sup hOodd (hKC.trans hCO) hON hT hM₀H hHN₀
  have hR₁' := isSylow2In_inf_sup hOodd (hK'C.trans hCO) hON' hT hM₁H hHN₁
  have hcomm : Commutes (T ⊓ (K₀ ⊔ O)) (T ⊓ (K' ⊔ O)) :=
    Sec6Gen.commutes_of_twin_of_isPGroup hΩ hK hK' (Ne.symm hc.std.hne) hz hz' hR₁.1 hR₁'.1
      (hT.2.1.to_le (sup_le inf_le_left inf_le_left))
  have hcent : ∀ {L : Subgroup Y}, L ≤ K₀ ⊔ K' → ∀ z ∈ Z, ∀ r ∈ T ⊓ L, z * r = r * z := by
    intro L hL z hz r hr
    have hcO := p23_zdata_comm_twins hc hZ hz (hL hr.2)
    have hcT : z * r * z⁻¹ * r⁻¹ ∈ T :=
      T.mul_mem (T.mul_mem (T.mul_mem (hZT hz) hr.1) (T.inv_mem (hZT hz))) (T.inv_mem hr.1)
    have h1 := eq_one_of_isPGroup_of_mem_odd hOodd hcO (hT.2.1.to_le (Subgroup.zpowers_le.mpr hcT))
    calc z * r = (z * r * z⁻¹ * r⁻¹) * (r * z) := by group
      _ = r * z := by rw [h1, one_mul]
  refine ⟨T ⊓ (K₀ ⊔ O), T ⊓ (K' ⊔ O), hR₁, hR₁', hcomm, fun z hz r hr => ?_, fun z hz r hr => ?_⟩
  · exact hcent le_sup_left z hz r ⟨hr.1, hR₁.1 hr⟩
  · exact hcent le_sup_right z hz r ⟨hr.1, hR₁'.1 hr⟩

end Twins

end LL1

open LL1

section Main


variable {n : ℕ}

theorem p23E7LL1_of_lemLId (hL : P23E7LemLId n) : P23E7LL1 n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hE hZu Z hZ f hf hfe hV1
  set V := aSub R Z e ⊓ aSub R Z f with hVdef
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hK' : K' ∈ Om R := hc.std.hK'.1
  have heO : e ∈ p23Orb Z t e := ⟨1, Subgroup.one_mem _, by group⟩
  have hVZ : V ≤ Z := inf_le_left.trans (aSub_le R Z e)
  have hV2 : IsPGroup 2 V := hZ.isPGroup.to_le hVZ
  obtain ⟨hgen, ⟨I⟩, ha⟩ := hL hcit hP Y R S t K' W u e g hc hno hE hZu Z hZ V hVZ hV1 e heO f hf
    (Ne.symm hfe) inf_le_left inf_le_right
  have hzV : ∀ z ∈ Z, conjSub z V = V := fun z hz =>
    conjSub_eq_of_mem_of_commutes hz (fun a ha b hb => hZ.comm a ha b (hVZ hb))
  have hzX : ∀ z ∈ Z, conjSub z (rLayerSub (Om R) V) = rLayerSub (Om R) V := fun z hz =>
    conjSub_rLayerSub_eq hΩ (hzV z hz)
  obtain ⟨F, hFrange, hFker, hFmap⟩ := toHom_of_aeIdentOn hgen I
  have hFmem : ∀ x, F x ∈ AE.e64Sub := fun x => hFrange ▸ ⟨x, rfl⟩
  let f₀ : SecQuot (rLayerSub (Om R) V) →* ↥AE.e64Sub := F.codRestrict AE.e64Sub hFmem
  have hf₀s : Function.Surjective f₀ := by
    rintro ⟨y, hy⟩
    rw [← hFrange] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have hf₀c : f₀.ker ≤ Subgroup.center (SecQuot (rLayerSub (Om R) V)) := fun x hx =>
    hFker (by
      rw [MonoidHom.mem_ker] at hx ⊢
      exact congrArg Subtype.val hx)
  have hcen : Subgroup.center ↥AE.e64Sub = ⊥ := TwinDisc.E64Aut.center_e64Sub_eq_bot
  obtain ⟨R₁, R₁', hR₁, hR₁', hcomm, hzR₁, hzR₁'⟩ := exists_cent_twin_sylows hc hZ
  have hcV : ∀ {L : Subgroup Y}, (∀ z ∈ Z, ∀ r ∈ L, z * r = r * z) →
      L ≤ Subgroup.centralizer (V : Set Y) := fun hL' r hr =>
    Subgroup.mem_centralizer_iff.mpr fun v hv => hL' v (hVZ hv) r hr
  have hR₁P : secImage (rLayerSub (Om R) V) R₁ ∈ p23SecFamV R V :=
    ⟨R₁, mem_RSet_of_isSylow2In hK hR₁, hcV hzR₁, rfl⟩
  have hR₁'P : secImage (rLayerSub (Om R) V) R₁' ∈ p23SecFamV R V :=
    ⟨R₁', mem_RSet_of_isSylow2In hK' hR₁', hcV hzR₁', rfl⟩
  obtain ⟨α, hα, h, b, hlab⟩ := I.label _ hR₁P
  obtain ⟨α', -, h', b', hlab'⟩ := I.label _ hR₁'P
  rw [hFmap _ hR₁P] at hlab
  rw [hFmap _ hR₁'P] at hlab'
  have hcommF : ∀ x ∈ AE.memBar α h b, ∀ y ∈ AE.memBar α' h' b', x * y = y * x := by
    rw [← hlab, ← hlab']
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    have hxy : x₀ * y₀ = y₀ * x₀ :=
      Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.mp hx₀) _ (Subgroup.mem_subgroupOf.mp hy₀))
    rw [← map_mul F, ← map_mul F, ← map_mul (QuotientGroup.mk' _), ← map_mul (QuotientGroup.mk' _),
      hxy]
  obtain ⟨rfl, hbb⟩ := twin_of_commute hcommF
  have hlab'' : (secImage (rLayerSub (Om R) V) R₁').map F = AE.memBar α h b' := hlab'
  have hfixσ : ∀ z (hz : z ∈ Z) {L : Subgroup Y}, (∀ z ∈ Z, ∀ r ∈ L, z * r = r * z) →
      ∀ x ∈ secImage (rLayerSub (Om R) V) L, secConjAut z (hzX z hz) x = x := by
    intro z hz L hL x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    rw [secConjAut_mk]
    congr 1
    apply Subtype.ext
    rw [coe_conjAutOf, hL z hz _ (Subgroup.mem_subgroupOf.mp hx₀), mul_inv_cancel_right]
  have hmemE : ∀ c : Bool, ∀ x ∈ AE.memBar α h c, x ∈ AE.e64Sub := by
    intro c x hx
    by_cases hcb : c = b
    · subst hcb
      rw [← hlab] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact hFmem y
    · have hcb' : c = b' := bool_eq_of_ne hbb hcb
      subst hcb'
      rw [← hlab''] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact hFmem y
  let Q : ↥Z → ↥AE.e64Sub → Prop := fun z c => ∀ x : SecQuot (rLayerSub (Om R) V),
    f₀ (secConjAut (z : Y) (hzX z z.2) x) = c * f₀ x * c⁻¹
  have hexist : ∀ z : ↥Z, ∃ c : ↥AE.e64Sub, c ∈ E64F.centPairSub α h ∧ Q z c := by
    intro z
    obtain ⟨θ, hθ⟩ := exists_induced_aut_center f₀ hf₀s hf₀c hcen (secConjAut (z : Y) (hzX z z.2))
    have hfixθ : ∀ {L : Subgroup Y} {c : Bool}, (∀ z ∈ Z, ∀ r ∈ L, z * r = r * z) →
        (secImage (rLayerSub (Om R) V) L).map F = AE.memBar α h c →
        ∀ y : ↥AE.e64Sub, (y : AE.AEQ 7) ∈ AE.memBar α h c → θ y = y := by
      intro L c hL hl y hy
      rw [← hl] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      have hy' : y = f₀ x := Subtype.ext hxy.symm
      rw [hy', hθ x, hfixσ z z.2 hL x hx]
    have key : ∀ c : Bool, ∀ y : ↥AE.e64Sub, (y : AE.AEQ 7) ∈ AE.memBar α h c → θ y = y := by
      intro c
      by_cases hcb : c = b
      · subst hcb
        exact hfixθ hzR₁ hlab
      · have hcb' : c = b' := bool_eq_of_ne hbb hcb
        subst hcb'
        exact hfixθ hzR₁' hlab''
    obtain ⟨c, -, hconj⟩ := TwinDisc.E64Aut.e64_aut_eq_conj θ hα h (key true) (key false)
    have hall : ∀ x : SecQuot (rLayerSub (Om R) V), θ (f₀ x) = c * f₀ x * c⁻¹ := by
      have hle : TC.Thin.pSpan (p23SecFamV R V) ≤
          MonoidHom.eqLocus (θ.toMonoidHom.comp f₀) ((MulAut.conj c).toMonoidHom.comp f₀) := by
        refine iSup₂_le fun L hL l hl => ?_
        obtain ⟨α₂, hα₂, h₂, b₂, hl₂⟩ := I.label L hL
        rw [hFmap L hL] at hl₂
        have hfl : ((f₀ l : ↥AE.e64Sub) : AE.AEQ 7) ∈ AE.memBar α₂ h₂ b₂ := by
          rw [← hl₂]
          exact ⟨l, hl, rfl⟩
        have h3 := hconj (f₀ l) ⟨α₂, hα₂, h₂, b₂, hfl⟩
        show θ (f₀ l) = (MulAut.conj c) (f₀ l)
        rw [h3, MulAut.conj_apply]
      intro x
      have hx : x ∈ TC.Thin.pSpan (p23SecFamV R V) := hgen ▸ Subgroup.mem_top x
      exact hle hx
    refine ⟨c, ⟨?_, ?_⟩, fun x => by rw [← hθ x, hall x]⟩
    all_goals
      intro x hx
      have hxe := hmemE _ x hx
      have h1 := key _ ⟨x, hxe⟩ hx
      have h3 := hconj ⟨x, hxe⟩ ⟨α, hα, h, _, hx⟩
      rw [h1] at h3
      have h4 := congrArg Subtype.val h3
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h4
      calc (c : AE.AEQ 7) * x = ((c : AE.AEQ 7) * x * (c : AE.AEQ 7)⁻¹) * c := by group
        _ = x * c := by rw [← h4]
  have huniq : ∀ z : ↥Z, ∀ c c' : ↥AE.e64Sub, Q z c → Q z c' → c = c' := by
    intro z c c' hc hc'
    have hmc : c'⁻¹ * c ∈ Subgroup.center ↥AE.e64Sub := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := hf₀s y
      have e := (hc x).symm.trans (hc' x)
      calc f₀ x * (c'⁻¹ * c) = c'⁻¹ * (c' * f₀ x * c'⁻¹) * c := by group
        _ = c'⁻¹ * (c * f₀ x * c⁻¹) * c := by rw [e]
        _ = c'⁻¹ * c * f₀ x := by group
    rw [hcen, Subgroup.mem_bot] at hmc
    exact (inv_mul_eq_one.mp hmc).symm
  have hQ1 : Q 1 1 := fun x => by
    rw [show secConjAut ((1 : ↥Z) : Y) (hzX _ (1 : ↥Z).2) x = x from secConjAut_one _ x]
    group
  have hQmul : ∀ z z' : ↥Z, ∀ c c', Q z c → Q z' c' → Q (z * z') (c * c') := by
    intro z z' c c' hc hc' x
    have hσ : secConjAut ((z * z' : ↥Z) : Y) (hzX _ (z * z').2) x =
        secConjAut (z : Y) (hzX z z.2) (secConjAut (z' : Y) (hzX z' z'.2) x) :=
      secConjAut_mul (z : Y) (z' : Y) _ _ _ x
    rw [hσ, hc, hc']
    group
  choose cf hcf using hexist
  let ρ : ↥Z →* ↥(E64F.centPairSub α h) :=
    { toFun := fun z => ⟨cf z, (hcf z).1⟩
      map_one' := Subtype.ext (huniq 1 _ _ (hcf 1).2 hQ1)
      map_mul' := fun z z' => Subtype.ext
        (huniq (z * z') _ _ (hcf (z * z')).2 (hQmul z z' _ _ (hcf z).2 (hcf z').2)) }
  have hker : ∀ z : ↥Z, ρ z = 1 → (z : Y) ∈ V := by
    intro z hz1
    have hc1 : cf z = 1 := congrArg Subtype.val hz1
    have hQ := (hcf z).2
    rw [hc1] at hQ
    have hQ' : ∀ x, f₀ (secConjAut (z : Y) (hzX z z.2) x) = f₀ x := fun x => by
      rw [hQ x]
      group
    have key : ∀ w ∈ p23Orb Z t e, V ≤ aSub R Z w → CentModE R w z := by
      intro w hw hVw
      have hwZ : w ∈ Z := hZ.orb_le hw
      have hZw : Z ≤ Subgroup.centralizer ({w} : Set Y) := hZ.le_cent hwZ
      have hzw : (z : Y) ∈ Subgroup.centralizer ({w} : Set Y) := hZw z.2
      have hVE : ∀ v ∈ V, ∀ a ∈ rLayer (Om R) w,
          v * a * v⁻¹ * a⁻¹ ∈ oddCoreOf (rLayer (Om R) w) := fun v hv =>
        ((mem_aSub_iff hZw).mp (hVw hv)).2
      have hcov : rLayer (Om R) w ≤
          oddCoreOf (rLayer (Om R) w) ⊔ (rLayer (Om R) w ⊓ rLayerSub (Om R) V) :=
        F7C.rLayer_le_cover hΩ hV2 (hVZ.trans hZw) hVE
      have hzXb : ∀ b ∈ rLayer (Om R) w ⊓ rLayerSub (Om R) V,
          (z : Y) * b * (z : Y)⁻¹ * b⁻¹ ∈
            oddCoreOf (rLayerSub (Om R) V) ⊓ (rLayer (Om R) w ⊓ rLayerSub (Om R) V) := by
        intro b hb
        have hbX : b ∈ rLayerSub (Om R) V := hb.2
        have hzb : (z : Y) * b * (z : Y)⁻¹ ∈ rLayerSub (Om R) V := by
          have := conj_mem_conjSub (n := (z : Y)) hbX
          rwa [hzX z z.2] at this
        have hcX : (z : Y) * b * (z : Y)⁻¹ * b⁻¹ ∈ rLayerSub (Om R) V :=
          Subgroup.mul_mem _ hzb (Subgroup.inv_mem _ hbX)
        have hzbE : (z : Y) * b * (z : Y)⁻¹ ∈ rLayer (Om R) w :=
          ((Subgroup.mem_normalizer_iff.mp (F7C.mem_normalizer_rLayer hΩ hzw)) b).mp hb.1
        have hcE : (z : Y) * b * (z : Y)⁻¹ * b⁻¹ ∈ rLayer (Om R) w :=
          Subgroup.mul_mem _ hzbE (Subgroup.inv_mem _ hb.1)
        have hq : QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V))
              (⟨_, hcX⟩ : ↥(rLayerSub (Om R) V)) =
            secConjAut (z : Y) (hzX z z.2)
                (QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨b, hbX⟩) *
              (QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V))
                ⟨b, hbX⟩)⁻¹ := by
          rw [secConjAut_mk, ← map_inv, ← map_mul]
          rfl
        have hker' : QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V))
            (⟨_, hcX⟩ : ↥(rLayerSub (Om R) V)) ∈ f₀.ker := by
          rw [MonoidHom.mem_ker, hq, map_mul, map_inv, hQ', mul_inv_cancel]
        have hmem : QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V))
            (⟨_, hcX⟩ : ↥(rLayerSub (Om R) V)) ∈
              secImage (rLayerSub (Om R) V) (rLayer (Om R) w ⊓ rLayerSub (Om R) V) ⊓
                Subgroup.center (SecQuot (rLayerSub (Om R) V)) :=
          ⟨⟨⟨_, hcX⟩, Subgroup.mem_subgroupOf.mpr ⟨hcE, hcX⟩, rfl⟩, hf₀c hker'⟩
        rw [ha w hw hVw, Subgroup.mem_bot] at hmem
        have hO : (⟨_, hcX⟩ : ↥(rLayerSub (Om R) V)) ∈
            classicalInvolutionOddCore ↥(rLayerSub (Om R) V) :=
          (QuotientGroup.eq_one_iff _).mp hmem
        exact ⟨⟨_, hO, rfl⟩, hcE, hcX⟩
      have hBN : rLayer (Om R) w ⊓ rLayerSub (Om R) V ≤
          Subgroup.normalizer (oddCoreOf (rLayer (Om R) w) : Set Y) :=
        inf_le_left.trans (Sec7.le_normalizer_oddCoreOf _)
      have hAO : oddCoreOf (rLayerSub (Om R) V) ⊓ (rLayer (Om R) w ⊓ rLayerSub (Om R) V) ≤
          oddCoreOf (rLayer (Om R) w) := by
        set A := oddCoreOf (rLayerSub (Om R) V) ⊓ (rLayer (Om R) w ⊓ rLayerSub (Om R) V)
          with hAdef
        set OE := oddCoreOf (rLayer (Om R) w) with hOEdef
        have hAodd : Odd (Nat.card A) :=
          Odd.of_dvd_nat (oddCoreOf_odd_natCard _) (Subgroup.card_dvd_of_le inf_le_left)
        have hAN : A ≤ Subgroup.normalizer (OE : Set Y) := inf_le_right.trans hBN
        have hNodd : Odd (Nat.card (A ⊔ OE : Subgroup Y)) :=
          Sec7.odd_card_sup_of_le_normalizer' hAN hAodd (oddCoreOf_odd_natCard _)
        have hNE : A ⊔ OE ≤ rLayer (Om R) w :=
          sup_le (inf_le_right.trans inf_le_left) (oddCoreOf_le_self _)
        have hEN : rLayer (Om R) w ≤ Subgroup.normalizer ((A ⊔ OE : Subgroup Y) : Set Y) := by
          refine hcov.trans (sup_le ?_ ?_)
          · intro o ho
            refine mem_normalizer_of_conjSub_eq (conjSub_eq_of_le ?_)
            rw [conjSub, Subgroup.map_sup]
            refine sup_le (fun x hx => ?_) ?_
            · obtain ⟨a, haA, rfl⟩ := hx
              have h1 : a⁻¹ * o * a ∈ OE := by
                have := (Subgroup.mem_normalizer_iff.mp (hAN (Subgroup.inv_mem _ haA)) o).mp ho
                simpa [mul_assoc] using this
              have h2 : (MulAut.conj o).toMonoidHom a = a * ((a⁻¹ * o * a) * o⁻¹) := by
                simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
                group
              rw [h2]
              exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haA)
                (Subgroup.mem_sup_right (Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ ho)))
            · exact (le_of_eq (conjSub_eq_self_of_mem ho)).trans le_sup_right
          · intro x hx
            exact mem_normalizer_sup (mem_normalizer_inf (Sec7.le_normalizer_oddCoreOf _ hx.2)
              (Subgroup.le_normalizer hx)) (hBN hx)
        exact le_sup_left.trans (AscFusion.le_oddCoreOf_of_normal_odd_gen hNE hEN hNodd)
      intro b hb
      have hb' : b ∈ ((oddCoreOf (rLayer (Om R) w) ⊔ (rLayer (Om R) w ⊓ rLayerSub (Om R) V) :
          Subgroup Y) : Set Y) := hcov hb
      rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hBN] at hb'
      obtain ⟨o, ho, b₀, hb₀, rfl⟩ := hb'
      have h1 : (z : Y) * o * (z : Y)⁻¹ ∈ oddCoreOf (rLayer (Om R) w) :=
        F7C.conj_mem_oddCoreOf_rLayer hΩ hzw ho
      have h2 := hAO (hzXb b₀ hb₀)
      have h3 : (z : Y) * (o * b₀) * (z : Y)⁻¹ * (o * b₀)⁻¹ =
          ((z : Y) * o * (z : Y)⁻¹) * ((z : Y) * b₀ * (z : Y)⁻¹ * b₀⁻¹) * o⁻¹ := by group
      rw [h3]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) (Subgroup.inv_mem _ ho)
    exact Subgroup.mem_inf.mpr ⟨(mem_aSub_iff (hZ.le_cent hZ.he)).mpr ⟨z.2, key e heO inf_le_left⟩,
      (mem_aSub_iff (hZ.le_cent (hZ.orb_le hf))).mpr ⟨z.2, key f hf inf_le_right⟩⟩
  have hle : ρ.ker ≤ V.subgroupOf Z := fun z hz => Subgroup.mem_subgroupOf.mpr (hker z hz)
  have h8 : Nat.card ρ.range ≤ 8 := by
    rw [← E64F.natCard_centPairSub hα h]
    exact Subgroup.card_le_card_group _
  calc (aSub R Z e ⊓ aSub R Z f).relIndex Z = (V.subgroupOf Z).index := rfl
    _ ≤ ρ.ker.index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le hle)
    _ = Nat.card ρ.range := Subgroup.index_ker ρ
    _ ≤ 8 := h8

theorem p23E7LL1_of_lemL (hL : P23E7LemL n) : P23E7LL1 n :=
  p23E7LL1_of_lemLId (p23E7LemLId_of_lemL hL)

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
