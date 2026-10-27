module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87A7Cent
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L2Card
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SecXProved
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoCent
public import CFSG.GH74.GLS.C3.Layer1.Th2A7Rigid

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P27 CFSG.ABGLocalTools
open scoped commutatorElement

section Abstract

variable {X : Type} [Group X]

theorem actHom_eq_one_of_a7 (K : Subgroup X) [K.Normal]
    (e : (↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 7)) {c : X} (hc2 : c * c = 1)
    (Rb : Subgroup (↥K ⧸ pPrimeCore 2 ↥K)) (hfix : ∀ y ∈ Rb, actHom K c y = y)
    (hcard : 120 < Nat.card ↥Rb) : actHom K c = 1 := by
  let σ : MulAut (alternatingGroup (Fin 7)) := MulAut.congr e (actHom K c)
  have hσ : σ * σ = 1 := by
    have h1 : actHom K c * actHom K c = 1 := by rw [← map_mul, hc2, map_one]
    have h2 : (MulAut.congr e) (actHom K c * actHom K c) = 1 := by rw [h1, map_one]
    rwa [map_mul] at h2
  let H₀ : Subgroup (alternatingGroup (Fin 7)) := Rb.map e.toMonoidHom
  have hH₀card : Nat.card ↥H₀ = Nat.card ↥Rb :=
    (Nat.card_congr (Subgroup.equivMapOfInjective Rb e.toMonoidHom e.injective).toEquiv).symm
  have hfix' : ∀ h ∈ H₀, σ h = h := by
    rintro _ ⟨y, hy, rfl⟩
    show (MulAut.congr e (actHom K c)) (e y) = e y
    simp only [MulAut.congr_apply, MulEquiv.coe_trans, Function.comp_apply, MulEquiv.symm_apply_apply]
    rw [hfix y hy]
  have h1 := a7_aut_eq_one_of_fixes_large (by rw [hH₀card]; exact hcard) hσ hfix'
  exact (MulAut.congr e).injective (by rw [map_one]; exact h1)

end Abstract

section Lift

variable {G : Type} [Group G] [Finite G]

theorem surjective_centralizer_to_Jbar {z : G} {J : Subgroup G} (hz2 : z * z = 1)
    (hzJ : z ∈ normalizer (J : Set G)) (hcomm : ∀ j ∈ J, ⁅j, z⁆ ∈ pPrimeCoreOf 2 J) :
    Function.Surjective ((QuotientGroup.mk' (pPrimeCore 2 ↥J)).comp
      (Subgroup.inclusion (inf_le_left : J ⊓ centralizer ({z} : Set G) ≤ J))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro jb
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective jb
  set N : Subgroup G := pPrimeCoreOf 2 J with hN
  have hNodd : Odd (Nat.card ↥N) := Signalizer.L52Two.odd_card_O J
  have hzp : IsPGroup 2 ↥(zpowers z) := by
    have hord : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz2)
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; simp)
  have hzN : z ∈ normalizer (N : Set G) := TwoThin.mem_normalizer_pPrimeCoreOf hzJ
  have hEN : ∀ e ∈ zpowers z, ∀ n ∈ N, e * n * e⁻¹ ∈ N := fun e he n hn =>
    (Subgroup.mem_normalizer_iff.1 ((Subgroup.zpowers_le).2 hzN he) n).1 hn
  have hx : ∀ e ∈ zpowers z, (j : G)⁻¹ * (e * (j : G) * e⁻¹) ∈ N := by
    intro e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · have : z ^ (2 * m) = 1 := by rw [zpow_mul, zpow_two, hz2, one_zpow]
      rw [this]
      simp
    · have : z ^ (2 * m + 1) = z := by rw [zpow_add_one, zpow_mul, zpow_two, hz2, one_zpow, one_mul]
      rw [this]
      have h1 := hcomm ((j : G)⁻¹) (J.inv_mem j.2)
      rw [commutatorElement_def, inv_inv] at h1
      simpa [mul_assoc] using h1
  obtain ⟨n, hn, hfix⟩ := L52Two.exists_fixed_mem_coset_of_odd hzp hNodd hEN hx
  have hnJ : n ∈ J := TwoThin.pPrimeCoreOf_le J hn
  have hjn : (j : G) * n ∈ J := J.mul_mem j.2 hnJ
  have hjnc : (j : G) * n ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hfix z (Subgroup.mem_zpowers z)
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  refine ⟨⟨(j : G) * n, hjn, hjnc⟩, ?_⟩
  show (QuotientGroup.mk (⟨(j : G) * n, hjn⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) = QuotientGroup.mk j
  symm
  rw [QuotientGroup.eq]
  obtain ⟨n', hn', hnn'⟩ := Subgroup.mem_map.1 hn
  have : (j⁻¹ * ⟨(j : G) * n, hjn⟩ : ↥J) = n' := by
    apply Subtype.ext
    simp [hnn'.symm]
  rw [this]
  exact hn'

end Lift

section Card

theorem card_quot_le_range_of_injective {I K : Type} [Group I] [Group K] [Finite I] [Finite K]
    (f : I →* K) (hf : Function.Injective f) :
    Nat.card (I ⧸ pPrimeCore 2 I) ≤
      Nat.card ((QuotientGroup.mk' (pPrimeCore 2 K)).comp f).range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ : I →* K ⧸ pPrimeCore 2 K := (QuotientGroup.mk' (pPrimeCore 2 K)).comp f with hψ
  have hodd : Odd (Nat.card ↥ψ.ker) := by
    let g : ↥ψ.ker →* ↥(pPrimeCore 2 K) :=
      (f.comp ψ.ker.subtype).codRestrict (pPrimeCore 2 K) (fun y => by
        have h1 : ψ y.1 = 1 := y.2
        exact (QuotientGroup.eq_one_iff _).1 h1)
    have hg : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      apply hf
      exact congrArg Subtype.val hab
    have hdvd : Nat.card ↥ψ.ker ∣ Nat.card ↥(pPrimeCore 2 K) := Subgroup.card_dvd_of_injective g hg
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := K))) hdvd
  have hle : ψ.ker ≤ pPrimeCore 2 I :=
    le_sSup ⟨MonoidHom.normal_ker ψ, Nat.coprime_two_left.mpr hodd⟩
  have h1 : (pPrimeCore 2 I).index ∣ ψ.ker.index := Subgroup.index_dvd_of_le hle
  have h2 : ψ.ker.index = Nat.card ψ.range := Subgroup.index_ker ψ
  rw [← h2]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1

end Card

section Main

variable {G : Type} [Group G] [Finite G]

theorem not_A7_of_datumPlusPsp4 {z x : G} {q : ℕ} {S : Subgroup G}
    (hctx : Stage2Ctx G z Kind.psp4 S) (hDP : DatumPlusPsp4 z x q) :
    ¬ Nonempty ((↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) ≃* alternatingGroup (Fin 7)) := by
  classical
  rintro ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, D₁, U, T₁, n, t', hC, hS, hTr, hEx⟩ := hDP
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hC.z_central.1, pow_two] at this
  have hJC : Jx x ≤ centralizer ({x} : Set G) := P34.Jx_le_centralizer x
  have hUJ : IsSylowOf 2 U (Jx x) := by
    have h := hC.T_syl.inf_of_le_normalizer hJC (fun c hc => S45.mem_normalizer_Jx hc)
    rwa [hEx.T_inf_J] at h
  have hJbar : Nat.card (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) = 2520 := by
    rw [Nat.card_congr e.toEquiv]; exact Th2.A7Inv.card_A7
  have h8J : 2 ^ 3 ∣ Nat.card ↥(Jx x) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥(Jx x)), hJbar]
    exact Dvd.dvd.mul_right (by norm_num) _
  have hU8 : 2 ^ 3 ∣ Nat.card ↥U := by
    rw [hUJ.card_eq]
    exact pow_dvd_pow 2
      ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h8J)
  have hodd_I : Odd (Nat.card ↥(pPrimeCore 2 ↥(Ixz z x))) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥(Ixz z x)))
  have h8I : 2 ^ 3 ∣ Nat.card (↥(Ixz z x) ⧸ pPrimeCore 2 ↥(Ixz z x)) := by
    have h1 : 2 ^ 3 ∣ Nat.card ↥(Ixz z x) := hU8.trans (Subgroup.card_dvd_of_le hS.U_syl.le)
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥(Ixz z x))] at h1
    exact (Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hodd_I)).dvd_of_dvd_mul_right h1
  have h168 : 168 ≤ Nat.card (↥(Ixz z x) ⧸ pPrimeCore 2 ↥(Ixz z x)) :=
    ge_168_of_eight_dvd_isL2 hC.q_odd hC.q_gt hC.I_L2 (by simpa using h8I)
  have hn := Jx_subgroupOf_normal x
  set K : Subgroup ↥(centralizer ({x} : Set G)) :=
    (Jx x).subgroupOf (centralizer ({x} : Set G)) with hK
  let ι : ↥K ≃* ↥(Jx x) := Subgroup.subgroupOfEquivOfLe hJC
  let eK : (↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.congr (pPrimeCore 2 ↥K) (pPrimeCore 2 ↥(Jx x)) ι
      (pPrimeCore_map_iso 2 ι)).trans e
  let f : ↥(Ixz z x) →* ↥K := ι.symm.toMonoidHom.comp (Subgroup.inclusion hTr.I_le_J)
  have hf : Function.Injective f := ι.symm.injective.comp (Subgroup.inclusion_injective _)
  have hIC : Ixz z x ≤ centralizer ({z} : Set G) :=
    (pLayerOf_le_P27 2 (centralizer ({x, z} : Set G))).trans
      (Subgroup.centralizer_le
        (Set.singleton_subset_iff.2 (Set.mem_insert_of_mem _ (Set.mem_singleton z))))
  have hzC : z ∈ centralizer ({x} : Set G) := by
    have h : x ∈ centralizer ({z} : Set G) := hC.x_mem
    rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
    exact h.symm
  let c : ↥(centralizer ({x} : Set G)) := ⟨z, hzC⟩
  have hc2 : c * c = 1 := Subtype.ext hz2
  have hfix : ∀ y ∈ ((QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp f).range, actHom K c y = y := by
    rintro _ ⟨i, rfl⟩
    show actHom K c (QuotientGroup.mk (f i) : ↥K ⧸ pPrimeCore 2 ↥K) = QuotientGroup.mk (f i)
    rw [actHom_mk]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    apply Subtype.ext
    show z * (i : G) * z⁻¹ = (i : G)
    have h1 := Subgroup.mem_centralizer_iff.1 (hIC i.2) z (Set.mem_singleton z)
    rw [mul_inv_eq_iff_eq_mul]
    exact h1
  have hcard : 120 < Nat.card ((QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp f).range :=
    lt_of_lt_of_le (by norm_num) (h168.trans (card_quot_le_range_of_injective f hf))
  have hact : actHom K c = 1 := actHom_eq_one_of_a7 K eK hc2 _ hfix hcard
  have hzK : z ∈ CxK x (Jx x) :=
    ker_actHom_le_CxK x (Subgroup.mem_map.2 ⟨c, MonoidHom.mem_ker.2 hact, rfl⟩)
  obtain ⟨-, hzJ, -, hcomm⟩ := hzK
  have hsurj := surjective_centralizer_to_Jbar hz2 hzJ hcomm
  let φ : ↥(Jx x ⊓ centralizer ({z} : Set G)) →* alternatingGroup (Fin 7) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (pPrimeCore 2 ↥(Jx x))).comp
      (Subgroup.inclusion (inf_le_left : Jx x ⊓ centralizer ({z} : Set G) ≤ Jx x)))
  have hφ : Function.Surjective φ := e.surjective.comp hsurj
  have hsec1 : IsSection (alternatingGroup (Fin 7)) ↥(Jx x ⊓ centralizer ({z} : Set G)) := by
    refine ⟨⊤, φ.comp Subgroup.topEquiv.toMonoidHom, ?_⟩
    exact hφ.comp Subgroup.topEquiv.surjective
  have hsec : IsSection (alternatingGroup (Fin 7)) ↥(Cen z) :=
    IsSection.of_le_le (inf_le_right : Jx x ⊓ centralizer ({z} : Set G) ≤ Cen z) hsec1
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by norm_num)
  exact not_isL2_alt7 (kindFactor_of_section_C hctx Th2.A7Inv.not_isSolvable_A7 hsec)

theorem psp4NotA7_proved : Psp4NotA7 :=
  fun _ _ _ _ _ hctx _ _ hDP => not_A7_of_datumPlusPsp4 hctx hDP

theorem secX_proved
    (hfld : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Stage2Ctx G z k S → Stage1.Main.L4TwoFieldStmt G z k S)
    (hSch : P34.GHSchreier) : SecX :=
  secX_of_ctx hfld hSch psp4NotA7_proved

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
