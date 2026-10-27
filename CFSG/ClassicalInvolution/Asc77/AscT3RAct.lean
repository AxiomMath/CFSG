module

public import CFSG.ClassicalInvolution.Asc77.AscT3CII9Aut
public import CFSG.ClassicalInvolution.AschTight.CStar
public import CFSG.ClassicalInvolution.Asc77.AscSixModCent

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII.T3R

open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.GorensteinWalter
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups commutatorElement

section GenericSylow

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSylow2In_map_sylow {P : Subgroup G} (Q : Sylow 2 ↥P) :
    IsSylow2In (Q.map P.subtype) P := by
  refine ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _, fun V' hV'P hV'2 hle => ?_⟩
  have hQV : (Q : Subgroup ↥P) ≤ V'.subgroupOf P := by
    intro x hx
    exact hle ⟨x, hx, rfl⟩
  have hcomap : V'.subgroupOf P = (Q : Subgroup ↥P) :=
    Q.is_maximal' (hV'2.comap_subtype) hQV
  rw [← Subgroup.map_subgroupOf_eq_of_le hV'P, hcomap]

theorem natCard_isSylow2In {V P : Subgroup G} (h : IsSylow2In V P) :
    Nat.card V = 2 ^ (Nat.card P).factorization 2 := by
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 ↥P))
  have h1 := h.natCard_eq (isSylow2In_map_sylow Q)
  rw [h1, Subgroup.card_map_of_injective P.subtype_injective]
  exact Sylow.card_eq_multiplicity Q

end GenericSylow

variable {G : Type} [Group G] {F : Type} [Field F]

@[expose] def eta (L : Subgroup G) (e : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, F)) :
    ↥L →* SL(2, F) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore ↥L))

@[expose] def phi (L : Subgroup G) (e : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, F)) :
    Subgroup.normalizer (L : Set G) →* MulAut SL(2, F) :=
  (MulAut.congr e).toMonoidHom.comp ((oddCoreQuotientAut ↥L).comp (normalizerConj L))

variable (L : Subgroup G) (e : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, F))

theorem eta_surjective : Function.Surjective (eta L e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem eta_eq_one_iff (k : ↥L) : eta L e k = 1 ↔ k ∈ classicalInvolutionOddCore ↥L := by
  simp only [eta, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
  rw [← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]

theorem phi_apply_eta (n : Subgroup.normalizer (L : Set G)) (k : ↥L) :
    phi L e n (eta L e k) = eta L e (normalizerConj L n k) := by
  simp [phi, eta, MulAut.congr_apply, oddCoreQuotientAut_mk]

open Classical in
@[expose] noncomputable def phiG (x : G) : MulAut SL(2, F) :=
  if h : x ∈ Subgroup.normalizer (L : Set G) then phi L e ⟨x, h⟩ else 1

variable {L e}

theorem phiG_of_mem {x : G} (h : x ∈ Subgroup.normalizer (L : Set G)) :
    phiG L e x = phi L e ⟨x, h⟩ := by
  simp [phiG, h]

theorem phiG_mul {x y : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hy : y ∈ Subgroup.normalizer (L : Set G)) : phiG L e (x * y) = phiG L e x * phiG L e y := by
  rw [phiG_of_mem hx, phiG_of_mem hy, phiG_of_mem (Subgroup.mul_mem _ hx hy), ← map_mul]
  rfl

theorem phiG_one : phiG L e 1 = 1 := by
  rw [phiG_of_mem (Subgroup.one_mem _)]
  exact map_one _

theorem phiG_inv {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    phiG L e x⁻¹ = (phiG L e x)⁻¹ := by
  rw [phiG_of_mem hx, phiG_of_mem (Subgroup.inv_mem _ hx), ← map_inv]
  rfl

theorem phiG_apply_eta {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) (k : ↥L) :
    phiG L e x (eta L e k) =
      eta L e ⟨x * k * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx k).mp k.2⟩ := by
  rw [phiG_of_mem hx, phi_apply_eta]
  rfl

theorem phiG_of_mem_L {x : G} (hx : x ∈ L) :
    phiG L e x = MulAut.conj (eta L e ⟨x, hx⟩) := by
  have hN : x ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hx
  ext y
  obtain ⟨k, rfl⟩ := eta_surjective L e y
  rw [phiG_apply_eta hN, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem phiG_eq_one_iff {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    phiG L e x = 1 ↔ x ∈ cStar L := by
  rw [phiG_of_mem hx]
  constructor
  · intro h
    refine ⟨⟨x, hx⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    have h1 : (MulAut.congr e) (((oddCoreQuotientAut ↥L).comp (normalizerConj L)) ⟨x, hx⟩) = 1 := h
    exact (MulAut.congr e).injective (h1.trans (map_one _).symm)
  · rintro ⟨n, hn, hnx⟩
    have hn' : n = ⟨x, hx⟩ := Subtype.ext hnx
    subst hn'
    have h1 : oddCoreQuotientAut ↥L (normalizerConj L ⟨x, hx⟩) = 1 := MonoidHom.mem_ker.mp hn
    show (MulAut.congr e) (oddCoreQuotientAut ↥L (normalizerConj L ⟨x, hx⟩)) = 1
    rw [h1, map_one]

theorem mem_centralizerModOdd_top_iff {x : G} :
    x ∈ centralizerModOdd (⊤ : Subgroup G) L ↔ x ∈ cStar L := by
  constructor
  · rintro ⟨-, hxN, -, hcomm⟩
    refine mem_cStar_iff.mpr ⟨hxN, fun k => ?_⟩
    have h1 : ⁅x, (k : G)⁻¹⁆ ∈ oddCoreOf L := hcomm _ (L.inv_mem k.2)
    obtain ⟨hm, hmem⟩ := mem_oddCoreOf_iff.mp h1
    convert hmem using 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, normalizerConj_apply_coe, commutatorElement_def]
    group
  · intro hx
    have hxN := cStar_le_normalizer L hx
    refine ⟨trivial, hxN, mem_normalizer_oddCore_of_mem_normalizer hxN, fun l hl => ?_⟩
    obtain ⟨hg', h⟩ := mem_cStar_iff.mp hx
    have h1 := h ⟨l⁻¹, L.inv_mem hl⟩
    refine mem_oddCoreOf_iff.mpr ⟨?_, ?_⟩
    · have : ⁅x, l⁆ = x * l * x⁻¹ * l⁻¹ := by simp only [commutatorElement_def]
      rw [this]
      exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN l).mp hl) (L.inv_mem hl)
    · convert h1 using 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, normalizerConj_apply_coe,
        commutatorElement_def]
      group


section Sylow

variable [Finite G] [Finite F]

include e in
theorem natCard_isSylow2In_eq_natCard_sylow (Q : Sylow 2 SL(2, F)) {RL : Subgroup G}
    (hRL : IsSylow2In RL L) : Nat.card RL = Nat.card Q := by
  have hOdd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥L)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥L
  have h1 : Nat.card ↥L = Nat.card (↥L ⧸ classicalInvolutionOddCore ↥L) *
      Nat.card ↥(classicalInvolutionOddCore ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 : Nat.card (↥L ⧸ classicalInvolutionOddCore ↥L) = Nat.card SL(2, F) :=
    Nat.card_congr e.toEquiv
  have hne1 : Nat.card SL(2, F) ≠ 0 := Nat.card_pos.ne'
  have hne2 : Nat.card ↥(classicalInvolutionOddCore ↥L) ≠ 0 := Nat.card_pos.ne'
  have h3 : (Nat.card ↥L).factorization 2 = (Nat.card SL(2, F)).factorization 2 := by
    rw [h1, h2, Nat.factorization_mul hne1 hne2]
    have : (Nat.card ↥(classicalInvolutionOddCore ↥L)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by
        intro hd
        exact (Nat.not_even_iff_odd.mpr hOdd) (even_iff_two_dvd.mpr hd))
    simp [this]
  rw [natCard_isSylow2In hRL, Sylow.card_eq_multiplicity Q, h3]


omit [Finite F] in
theorem natCard_map_eta {RL : Subgroup G} (hRL2 : IsPGroup 2 ↥RL) (hRLL : RL ≤ L) :
    Nat.card ((RL.subgroupOf L).map (eta L e)) = Nat.card RL := by
  set H : Subgroup ↥L := RL.subgroupOf L with hH
  set f : ↥H →* SL(2, F) := (eta L e).comp H.subtype with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : eta L e (x : ↥L) = 1 := hx
    have hxO : (x : ↥L) ∈ classicalInvolutionOddCore ↥L :=
      (eta_eq_one_iff (L := L) (e := e) _).mp hx'
    have hxG : ((x : ↥L) : G) ∈ oddCoreOf L := ⟨x, hxO, rfl⟩
    have hx2 : IsPGroup 2 (Subgroup.zpowers ((x : ↥L) : G)) := by
      have hxRL : ((x : ↥L) : G) ∈ RL := x.2
      exact hRL2.to_le (Subgroup.zpowers_le.mpr hxRL)
    have := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard L) hxG hx2
    apply Subtype.ext
    apply Subtype.ext
    simpa using this
  have hrange : f.range = H.map (eta L e) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRLL).toEquiv


@[expose] def phiImage (L : Subgroup G) (e : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, F))
    (R : Subgroup G) : Subgroup (MulAut SL(2, F)) :=
  (R.subgroupOf (Subgroup.normalizer (L : Set G))).map (phi L e)

omit [Finite G] [Finite F] in
theorem mem_phiImage {R : Subgroup G} {y : MulAut SL(2, F)} :
    y ∈ phiImage L e R ↔ ∃ r ∈ R, r ∈ Subgroup.normalizer (L : Set G) ∧ phiG L e r = y := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, n.2, phiG_of_mem n.2⟩
  · rintro ⟨r, hr, hrN, rfl⟩
    exact ⟨⟨r, hrN⟩, hr, (phiG_of_mem hrN).symm⟩

omit [Finite G] [Finite F] in
theorem phiG_mem_phiImage {R : Subgroup G} {r : G} (hr : r ∈ R)
    (hrN : r ∈ Subgroup.normalizer (L : Set G)) : phiG L e r ∈ phiImage L e R :=
  mem_phiImage.mpr ⟨r, hr, hrN, rfl⟩

omit [Finite G] [Finite F] in
theorem phiImage_eq {RL : Subgroup G} (hRLL : RL ≤ L) :
    phiImage L e RL = ((RL.subgroupOf L).map (eta L e)).map
      (MulAut.conj : SL(2, F) →* MulAut SL(2, F)) := by
  ext y
  constructor
  · intro hy
    obtain ⟨r, hr, hrN, rfl⟩ := mem_phiImage.mp hy
    exact ⟨eta L e ⟨r, hRLL hr⟩, ⟨⟨r, hRLL hr⟩, hr, rfl⟩, (phiG_of_mem_L (hRLL hr)).symm⟩
  · rintro ⟨s, ⟨k, hk, rfl⟩, rfl⟩
    exact mem_phiImage.mpr ⟨(k : G), hk, Subgroup.le_normalizer k.2, phiG_of_mem_L k.2⟩

omit [Finite G] [Finite F] in
theorem phiImage_le_inn {RL : Subgroup G} (hRLL : RL ≤ L) :
    phiImage L e RL ≤ (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range := by
  rw [phiImage_eq hRLL]
  rintro _ ⟨s, _, rfl⟩
  exact ⟨s, rfl⟩

omit [Finite G] [Finite F] in
theorem isPGroup_phiImage {R : Subgroup G} (hR2 : IsPGroup 2 ↥R) :
    IsPGroup 2 (phiImage L e R) := (hR2.comap_subtype (K := Subgroup.normalizer (L : Set G))).map _

theorem two_mul_natCard_phiImage (hF : Odd (Nat.card F)) (Q : Sylow 2 SL(2, F))
    {RL : Subgroup G} (hRL : IsSylow2In RL L) : 2 * Nat.card (phiImage L e RL) = Nat.card Q := by
  have hRL2 : IsPGroup 2 ↥RL := hRL.2.1
  have hRLL : RL ≤ L := hRL.1
  have hRs2 : IsPGroup 2 ((RL.subgroupOf L).map (eta L e)) := (hRL2.comap_subtype (K := L)).map _
  have hRscard : Nat.card ((RL.subgroupOf L).map (eta L e)) = Nat.card Q :=
    (natCard_map_eta (e := e) hRL2 hRLL).trans (natCard_isSylow2In_eq_natCard_sylow (e := e) Q hRL)
  rw [phiImage_eq hRLL]
  exact two_mul_natCard_map_conj hF Q hRs2 hRscard

theorem exists_mem_of_phiG_inner (hF : Odd (Nat.card F)) {T RL : Subgroup G}
    (hT2 : IsPGroup 2 ↥T) (hTN : T ≤ Subgroup.normalizer (L : Set G)) (hRT : RL ≤ T)
    (hRL : IsSylow2In RL L) {x : G} (hx : x ∈ T)
    (hin : phiG L e x ∈ (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range) :
    ∃ r ∈ RL, phiG L e r = phiG L e x := by
  classical
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 SL(2, F)))
  set Inn : Subgroup (MulAut SL(2, F)) := (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range
    with hInn
  set A : Subgroup (MulAut SL(2, F)) := phiImage L e T with hA
  set D : Subgroup (MulAut SL(2, F)) := phiImage L e RL with hD
  have hA2 : IsPGroup 2 A := isPGroup_phiImage hT2
  have hDcard : 2 * Nat.card D = Nat.card Q := two_mul_natCard_phiImage (e := e) hF Q hRL
  have hDle : D ≤ A ⊓ Inn := by
    refine le_inf ?_ (phiImage_le_inn hRL.1)
    exact Subgroup.map_mono (fun n hn => hRT hn)
  have hU2 : IsPGroup 2 ↥(A ⊓ Inn) := hA2.to_le inf_le_left
  have hUcard : 2 * Nat.card ↥(A ⊓ Inn) ≤ Nat.card Q :=
    two_mul_natCard_le_of_le_inn hF Q inf_le_right hU2
  have hDU : D = A ⊓ Inn :=
    Subgroup.eq_of_le_of_card_ge hDle (by omega)
  have hxA : phiG L e x ∈ A := phiG_mem_phiImage hx (hTN hx)
  have hxU : phiG L e x ∈ D := hDU ▸ ⟨hxA, hin⟩
  obtain ⟨r, hr, -, hrx⟩ := mem_phiImage.mp hxU
  exact ⟨r, hr, hrx⟩

end Sylow

end CFSG.ClassicalInvolution.Asc77.T3CII.T3R
