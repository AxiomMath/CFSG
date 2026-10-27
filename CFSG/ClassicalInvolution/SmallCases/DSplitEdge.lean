module

public import CFSG.ClassicalInvolution.SmallCases.DisconnectedQuaternion
public import CFSG.ClassicalInvolution.Asc77.AscL62Aut
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnConj

public section

namespace CFSG.ClassicalInvolution.Disconnected

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

@[expose] noncomputable def sylowOf2In {V P : Subgroup G} (h : IsSylow2In V P) : Sylow 2 ↥P where
  toSubgroup := V.subgroupOf P
  isPGroup' := h.2.1.comap_subtype
  is_maximal' := by
    intro Q hQ hle
    have hVQ : V ≤ Q.map P.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le h.1]
      exact Subgroup.map_mono hle
    have := h.2.2 (Q.map P.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
    rw [← Subgroup.comap_map_eq_self_of_injective P.subtype_injective Q, this]
    rfl

omit [Finite G] in
theorem coe_sylowOf2In {V P : Subgroup G} (h : IsSylow2In V P) :
    (sylowOf2In h : Subgroup ↥P) = V.subgroupOf P :=
  rfl

theorem commutator_mem_oddCoreIn_of_centralizes_sylow (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {N : Subgroup G} {z : G} (hN : IsClassicalMember p f N z) {R : Subgroup G}
    (hR : IsSylow2In R N) {a : G} (haN : a ∈ Subgroup.normalizer (N : Set G))
    (ha2 : a * a = 1) (haR : ∀ r ∈ R, a * r = r * a) :
    ∀ x ∈ N, ⁅a, x⁆ ∈ oddCoreIn N := by
  obtain ⟨e⟩ := hN.nonempty_equiv
  set O : Subgroup ↥N := classicalInvolutionOddCore ↥N with hO
  set α : MulAut ↥N := N.normalizerMonoidHom ⟨a, haN⟩ with hα
  have hαO : O.map α.toMonoidHom = O :=
    CFSG.ComponentClassification.OddCore.char_invariant α
  set ᾱ : MulAut (↥N ⧸ O) := QuotientGroup.congr O O α hαO with hᾱ
  set β : MulAut SL(2, GaloisField p f) := MulAut.congr e ᾱ with hβ
  have hαapp : ∀ y : ↥N, ((α y : ↥N) : G) = a * (y : G) * a⁻¹ := by
    intro y
    rw [hα]
    simp
  have hαα : α * α = 1 := by
    rw [hα, ← map_mul]
    have : (⟨a, haN⟩ * ⟨a, haN⟩ : ↥(Subgroup.normalizer (N : Set G))) = 1 :=
      Subtype.ext ha2
    rw [this, map_one]
  have hkey : ∀ y : ↥N, ᾱ (QuotientGroup.mk y) = QuotientGroup.mk (α y) := fun y => rfl
  have hᾱ2 : ᾱ * ᾱ = 1 := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H y =>
      rw [MulAut.mul_apply, hkey, hkey, MulAut.one_apply]
      have := congrArg (fun γ : MulAut ↥N => γ y) hαα
      simp only [MulAut.mul_apply, MulAut.one_apply] at this
      rw [this]
  have hβ2 : β ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two, hβ, ← map_mul, hᾱ2, map_one]
  let φ : ↥N →* SL(2, GaloisField p f) := e.toMonoidHom.comp (QuotientGroup.mk' O)
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective O)
  let P : Sylow 2 SL(2, GaloisField p f) := Sylow.mapSurjective hφ (sylowOf2In hR)
  have hfix : ∀ x ∈ P, β x = x := by
    intro x hx
    have hx' : x ∈ (sylowOf2In hR : Subgroup ↥N).map φ := by
      have := Sylow.coe_mapSurjective hφ (sylowOf2In hR)
      rw [← this]
      exact hx
    obtain ⟨r, hr, rfl⟩ := hx'
    have hrR : (r : G) ∈ R := hr
    have hαr : α r = r := by
      apply Subtype.ext
      rw [hαapp]
      have := haR r hrR
      calc a * (r : G) * a⁻¹ = (r : G) * a * a⁻¹ := by rw [this]
        _ = r := by group
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    rw [hβ, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hkey, hαr]
  have hβ1 : β = 1 := AscL62.mulAut_eq_one_of_pow_two_pow_eq_one hp2 hq P 1 β hβ2 hfix
  intro x hx
  have h1 : ᾱ (QuotientGroup.mk ⟨x, hx⟩) = QuotientGroup.mk ⟨x, hx⟩ := by
    have h2 : β (e (QuotientGroup.mk ⟨x, hx⟩)) = e (QuotientGroup.mk ⟨x, hx⟩) := by
      rw [hβ1]
      rfl
    rw [hβ, MulAut.congr_apply] at h2
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h2
    exact e.injective h2
  rw [hkey] at h1
  have h4 : α ⟨x, hx⟩ / ⟨x, hx⟩ ∈ O := QuotientGroup.eq_iff_div_mem.mp h1
  refine ⟨α ⟨x, hx⟩ / ⟨x, hx⟩, h4, ?_⟩
  have h5 : N.subtype (α ⟨x, hx⟩ / ⟨x, hx⟩) = ((α ⟨x, hx⟩ : ↥N) : G) / x := by
    rw [map_div]
    rfl
  rw [h5, hαapp, commutatorElement_def]
  simp [div_eq_mul_inv]

private theorem natCard_eq_pow_factorization {V P : Subgroup G} (h : IsSylow2In V P) :
    Nat.card V = 2 ^ (Nat.card P).factorization 2 := by
  have e1 := Sylow.card_eq_multiplicity (sylowOf2In h)
  have c1 : Nat.card ↥(V.subgroupOf P) = Nat.card V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.1).toEquiv
  have e1' : Nat.card ↥(V.subgroupOf P) = 2 ^ (Nat.card P).factorization 2 := e1
  rw [← c1, e1']

theorem factorization_two_card_classical {J : Subgroup G} {z : G}
    (hJ : IsClassicalMember p f J z) :
    (Nat.card J).factorization 2 = (Nat.card SL(2, GaloisField p f)).factorization 2 := by
  obtain ⟨e⟩ := hJ.nonempty_equiv
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore ↥J)
  rw [Nat.card_congr e.toEquiv] at hmul
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥J)) :=
    CFSG.ComponentClassification.OddCore.odd_card J
  have h1 : Nat.card SL(2, GaloisField p f) ≠ 0 := Nat.card_pos.ne'
  have h2 : Nat.card (classicalInvolutionOddCore ↥J) ≠ 0 := Nat.card_pos.ne'
  rw [hmul, Nat.factorization_mul h1 h2, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat, add_zero]

theorem natCard_sylow_eq_of_classical {J J' : Subgroup G} {z z' : G}
    (hJ : IsClassicalMember p f J z) (hJ' : IsClassicalMember p f J' z') {R R' : Subgroup G}
    (hR : IsSylow2In R J) (hR' : IsSylow2In R' J') : Nat.card R = Nat.card R' := by
  rw [natCard_eq_pow_factorization hR, natCard_eq_pow_factorization hR',
    factorization_two_card_classical hJ, factorization_two_card_classical hJ']

theorem exists_noncomm_of_isSylow2In_classical (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {N : Subgroup G}
    {z : G} (hN : IsClassicalMember p f N z) {R : Subgroup G} (hR : IsSylow2In R N) :
    ∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x := by
  obtain ⟨r, hr3, ⟨e⟩⟩ := quaternion_sylow_of_isClassicalMember hp2 hq hN (sylowOf2In hR)
  have hn : 2 ≤ 2 ^ (r - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  have : Fact (2 < 2 * 2 ^ (r - 2)) := ⟨by omega⟩
  set x : QuaternionGroup (2 ^ (r - 2)) := QuaternionGroup.a 1
  set y : QuaternionGroup (2 ^ (r - 2)) := QuaternionGroup.xa 0
  have hxy : x * y ≠ y * x := by
    simp only [x, y, QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a, ne_eq,
      QuaternionGroup.xa.injEq]
    simpa using ZMod.neg_one_ne_one
  have hmem : ∀ X : ↥(sylowOf2In hR : Subgroup ↥N), ((X : ↥N) : G) ∈ R := fun X =>
    Subgroup.mem_subgroupOf.mp X.2
  refine ⟨(((e.symm x : ↥(sylowOf2In hR : Subgroup ↥N)) : ↥N) : G), hmem _,
    (((e.symm y : ↥(sylowOf2In hR : Subgroup ↥N)) : ↥N) : G), hmem _, fun h => hxy ?_⟩
  have h1 : e.symm x * e.symm y = e.symm y * e.symm x := Subtype.ext (Subtype.ext h)
  have h2 := congrArg e h1
  simpa using h2

private theorem eq_one_of_mem_inf_oddCoreIn {X R : Subgroup G} (hR : IsPGroup 2 R)
    {g : G} (hgR : g ∈ R) (hgO : g ∈ oddCoreIn X) : g = 1 := by
  have h2 : IsPGroup 2 ↥(R ⊓ oddCoreIn X) := hR.to_inf_left
  have hodd : Odd (Nat.card ↥(R ⊓ oddCoreIn X)) :=
    (odd_card_oddCoreIn X).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hn0 : n = 0 := by
    by_contra hne
    rw [hn] at hodd
    exact (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨by norm_num, hne⟩)) hodd
  have hbot : R ⊓ oddCoreIn X = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (by rw [hn, hn0, pow_zero])
  have : g ∈ R ⊓ oddCoreIn X := ⟨hgR, hgO⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact this

theorem tq_of_mem_omegaNbr (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hcl : ∀ L ∈ Ω, ∃ z, IsClassicalMember p f L z) {M N : Subgroup G} (hM : M ∈ Ω)
    (hN : N ∈ Asc77.omegaNbr Ω M) :
    ∃ a, IsClassicalMember p f M a ∧ ActsTrivOnQuot N a := by
  obtain ⟨hNΩ, -, R, hR, hRN, hRM⟩ := hN
  obtain ⟨a, ha⟩ := hcl M hM
  obtain ⟨u₀, hu₀⟩ := hcl N hNΩ
  obtain ⟨J', hJ'Ω, hRJ', hR2, hRmax⟩ := Asc77.mem_RSet_iff.mp hR
  obtain ⟨z', hz'⟩ := hcl J' hJ'Ω
  obtain ⟨R₀, hR₀, hRR₀⟩ := IsSylow2In.exists_ge hR2 hRN
  have hcard : Nat.card R₀ = Nat.card R :=
    natCard_sylow_eq_of_classical hu₀ hz' hR₀ ⟨hRJ', hR2, hRmax⟩
  have hRsyl : IsSylow2In R N := hR₀.of_natCard_le hR2 hRN (by rw [hcard])
  have huniqM : IsUniqueInvolution M a :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq ha
  have haR : ∀ r ∈ R, a * r = r * a := by
    intro r hr
    have h1 := huniqM.conj_eq (n := r) (mem_normalizer_iff_conjSub_eq.mp (hRM hr))
    calc a * r = (r * a * r⁻¹) * r := by rw [h1]
      _ = r * a := by group
  have huniqN : IsUniqueInvolution N u₀ :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hu₀
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := exists_noncomm_of_isSylow2In_classical hp2 hq hu₀ hRsyl
  have hR1 : 2 ≤ Nat.card R := by
    by_contra hlt
    have hbot : R = ⊥ := Subgroup.eq_bot_of_card_le R (by omega)
    rw [hbot, Subgroup.mem_bot] at hx₀ hy₀
    exact hxy₀ (by rw [hx₀, hy₀])
  have hu₀R : u₀ ∈ R := Asc77.AscL62.mem_of_uniqueInvolution_of_pGroup huniqN hRN hR2 hR1
  have haN : a ∈ Subgroup.normalizer (N : Set G) := by
    have hau : a * u₀ * a⁻¹ = u₀ := by
      rw [haR u₀ hu₀R]
      group
    have hN' : IsClassicalMember p f (conjSub a N) u₀ := by
      have := hu₀.conj a
      rwa [hau] at this
    rcases canonical_twins_eq_or_nadj hq hu₀ hN' (isCanonical_of_isClassicalMember hu₀)
      (isCanonical_of_isClassicalMember hN') with h | h
    · exact mem_normalizer_iff_conjSub_eq.mpr h.symm
    · exfalso
      have hRN' : R ≤ conjSub a N := fun r hr => by
        rw [mem_conjSub_iff]
        have : a⁻¹ * r * a = r := by
          rw [mul_assoc, ← haR r hr]
          group
        rw [this]
        exact hRN hr
      have hc := h x₀ (hRN hx₀) y₀ (hRN' hy₀)
      have hcR : ⁅x₀, y₀⁆ ∈ R := by
        rw [commutatorElement_def]
        exact R.mul_mem (R.mul_mem (R.mul_mem hx₀ hy₀) (R.inv_mem hx₀)) (R.inv_mem hy₀)
      have h1 := eq_one_of_mem_inf_oddCoreIn (X := Subgroup.centralizer {u₀}) hR2 hcR hc
      exact hxy₀ ((commutatorElement_eq_one_iff_mul_comm).mp h1)
  exact ⟨a, ha, haN, commutator_mem_oddCoreIn_of_centralizes_sylow hp2 hq hu₀ hRsyl haN
    huniqM.sq haR⟩

end CFSG.ClassicalInvolution.Disconnected
