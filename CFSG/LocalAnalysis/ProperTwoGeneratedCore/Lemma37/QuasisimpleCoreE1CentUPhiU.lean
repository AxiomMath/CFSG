module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentUPhi

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open Equiv CFSG.Sporadic.Th.Max3

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

@[expose] noncomputable def centralizerSelf (u : J) :
    Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} :=
  ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

@[expose] noncomputable def toCentralizer :
    quasiNormalizer u →* Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} :=
  ((QuotientGroup.mk' (Subgroup.center J)).comp (quasiNormalizer u).subtype).codRestrict _
    fun g => Subgroup.mem_centralizer_singleton_iff.mpr
      ((d.starLift.toEscapingLift.mem_quasiNormalizer_iff d.setting).mp g.2).eq

theorem coe_toCentralizer (g : quasiNormalizer u) :
    ((d.toCentralizer g : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) :
      J ⧸ Subgroup.center J) = ((g : J) : J ⧸ Subgroup.center J) := rfl

theorem toCentralizer_surjective : Function.Surjective d.toCentralizer := by
  rintro ⟨c, hc⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  exact ⟨⟨g, (d.starLift.toEscapingLift.mem_quasiNormalizer_iff d.setting).mpr
    (Subgroup.mem_centralizer_singleton_iff.mp hc)⟩, rfl⟩

theorem toCentralizer_eq_one_iff {g : quasiNormalizer u} :
    d.toCentralizer g = 1 ↔ (g : J) = 1 ∨ (g : J) = centralElt J := by
  rw [← Subtype.coe_inj, coe_toCentralizer, OneMemClass.coe_one, QuotientGroup.eq_one_iff,
    d.setting.mem_center_iff]

theorem toCentralizer_quasiSelf : d.toCentralizer (quasiSelf u) = centralizerSelf u := rfl

@[expose] noncomputable def liftC {G : Type*} [Group G] (f : QuasiQuotient u →* G)
    (hf : f (quasiCentral u) = 1) : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} →* G :=
  MonoidHom.liftOfSurjective d.toCentralizer d.toCentralizer_surjective
    ⟨f.comp (quasiMk u), fun g hg => by
      rw [MonoidHom.mem_ker] at hg ⊢
      rcases d.toCentralizer_eq_one_iff.mp hg with h | h
      · rw [show g = 1 from Subtype.ext h, map_one]
      · rw [show g = ⟨centralElt J, d.setting.centralElt_mem_quasiNormalizer u⟩ from Subtype.ext h,
          MonoidHom.comp_apply, d.quasiMk_centralElt, hf]⟩

theorem liftC_toCentralizer {G : Type*} [Group G] (f : QuasiQuotient u →* G)
    (hf : f (quasiCentral u) = 1) (g : quasiNormalizer u) :
    d.liftC f hf (d.toCentralizer g) = f (quasiMk u g) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g

theorem liftC_surjective {G : Type*} [Group G] {f : QuasiQuotient u →* G}
    (hf : f (quasiCentral u) = 1) (hs : Function.Surjective f) :
    Function.Surjective (d.liftC f hf) := fun w => by
  obtain ⟨g, rfl⟩ := hs w
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  exact ⟨d.toCentralizer g', d.liftC_toCentralizer f hf g'⟩

@[expose] noncomputable def rho4C : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} →*
    Perm (Fin 4) :=
  d.liftC d.rho4 (d.rho4_of_mem d.quasiCentral_mem)

@[expose] noncomputable def rho5C : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} →*
    Perm (Fin 5) :=
  d.liftC d.rho5 (d.rho5_of_mem_centralizer d.quasiCentral_mem_centralizer)

@[expose] noncomputable def phiU : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} →*
    alternatingGroup (Fin 9) :=
  d.liftC d.phiBarA (Subtype.ext d.phiBar_quasiCentral)

theorem coe_phiU (c : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) :
    ((d.phiU c : alternatingGroup (Fin 9)) : Perm (Fin 9)) = permNine (d.rho4C c, d.rho5C c) := by
  obtain ⟨g, rfl⟩ := d.toCentralizer_surjective c
  rw [phiU, rho4C, rho5C, liftC_toCentralizer, liftC_toCentralizer, liftC_toCentralizer,
    coe_phiBarA, phiBar_apply]

theorem rho5C_surjective : Function.Surjective d.rho5C :=
  d.liftC_surjective _ d.rho5_surjective

theorem rho4C_self : d.rho4C (centralizerSelf u) = fourRep := by
  rw [← d.toCentralizer_quasiSelf, rho4C, liftC_toCentralizer]
  exact d.rho4_quasiBar

theorem phiU_self : d.phiU (centralizerSelf u) = altRep2A := by
  rw [← d.toCentralizer_quasiSelf, phiU, liftC_toCentralizer]
  exact Subtype.ext d.phiBar_quasiBar

theorem range_phiU : d.phiU.range = Subgroup.centralizer {altRep2A} := by
  rw [← d.range_phiBarA]
  ext a
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨g, rfl⟩ := d.toCentralizer_surjective c
    exact ⟨quasiMk u g, (d.liftC_toCentralizer _ _ g).symm⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    exact ⟨d.toCentralizer g', d.liftC_toCentralizer _ _ g'⟩

theorem ker_phiU :
    d.phiU.ker = CFSG.pPrimeCore 2 (Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}
  set e₀ : quasiNormalizer u := ⟨centralElt J, d.setting.centralElt_mem_quasiNormalizer u⟩
  apply le_antisymm
  ·
    have hle : d.phiU.ker ≤ (pPrimeCore 2 (quasiNormalizer u)).map d.toCentralizer := by
      intro c hc
      obtain ⟨g, rfl⟩ := d.toCentralizer_surjective c
      rw [MonoidHom.mem_ker, phiU, liftC_toCentralizer] at hc
      rcases d.phiBar_eq_one_iff.mp (congrArg Subtype.val hc) with h | h
      · exact Subgroup.mem_map_of_mem _ ((QuotientGroup.eq_one_iff g).mp h)
      · refine ⟨g * e₀⁻¹, (QuotientGroup.eq_one_iff _).mp (by
          change quasiMk u (g * e₀⁻¹) = 1
          rw [map_mul, map_inv, h, d.quasiMk_centralElt, mul_inv_cancel]), ?_⟩
        rw [map_mul, map_inv, (d.toCentralizer_eq_one_iff (g := e₀)).mpr (Or.inr rfl), inv_one,
          mul_one]
    have hodd : Odd (Nat.card d.phiU.ker) := (quasi_oddCore_odd u).of_dvd_nat
      ((Subgroup.card_dvd_of_le hle).trans (Subgroup.card_map_dvd _ _))
    exact le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hodd⟩
  ·
    intro c hc
    have hNodd : Odd (Nat.card (CFSG.pPrimeCore 2 C)) :=
      Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C))
    have hNn : (CFSG.pPrimeCore 2 C).Normal := CFSG.pPrimeCore_normal
    have h5 : d.rho5C c = 1 := by
      have := hNn.map _ d.rho5C_surjective
      have hM := eq_bot_of_normal_of_odd (N := (CFSG.pPrimeCore 2 C).map d.rho5C)
        (hNodd.of_dvd_nat (Subgroup.card_map_dvd _ _))
      have h1 : d.rho5C c ∈ (CFSG.pPrimeCore 2 C).map d.rho5C := Subgroup.mem_map_of_mem _ hc
      rwa [hM, Subgroup.mem_bot] at h1
    have h4 : d.rho4C c = 1 := by
      have hcu : c * centralizerSelf u = centralizerSelf u * c :=
        Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2)
      have hcomm : d.rho4C c * fourRep = fourRep * d.rho4C c := by
        have h1 := congrArg d.rho4C hcu
        rwa [map_mul, map_mul, d.rho4C_self] at h1
      have hdvd4 : orderOf (d.rho4C c) ∣ 4 :=
        orderOf_dvd_of_pow_eq_one (perm4_pow_four_of_commute _ hcomm)
      have hdvd : orderOf (d.rho4C c) ∣ Nat.card (CFSG.pPrimeCore 2 C) :=
        (orderOf_map_dvd _ _).trans (Subgroup.orderOf_dvd_natCard _ hc)
      have hcop : Nat.Coprime 4 (Nat.card (CFSG.pPrimeCore 2 C)) :=
        Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hNodd)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd4 hdvd)
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [coe_phiU, h4, h5, Prod.mk_one_one, map_one]
    rfl

theorem phiU_bijective_of_oddCore_eq_bot
    (hO : CFSG.pPrimeCore 2 (Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) = ⊥) :
    Function.Injective d.phiU ∧
      ∀ a ∈ Subgroup.centralizer {altRep2A}, ∃ c, d.phiU c = a := by
  refine ⟨(MonoidHom.ker_eq_bot_iff _).mp (d.ker_phiU.trans hO), fun a ha => ?_⟩
  rw [← d.range_phiU] at ha
  exact ha

theorem nonempty_mulEquiv_of_oddCore_eq_bot
    (hO : CFSG.pPrimeCore 2 (Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) = ⊥) :
    Nonempty (Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} ≃*
      Subgroup.centralizer {altRep2A}) :=
  ⟨(MonoidHom.ofInjective (d.phiU_bijective_of_oddCore_eq_bot hO).1).trans
    (MulEquiv.subgroupCongr d.range_phiU)⟩

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
