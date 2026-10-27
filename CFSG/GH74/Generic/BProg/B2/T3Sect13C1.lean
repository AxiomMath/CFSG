module

public import CFSG.GH74.Generic.BProg.B2.T3Sect13
public import CFSG.GH74.Generic.BProg.B2.T3Sect13Aux
public import CFSG.GH74.Generic.BProg.B2.FixFourS45
import CFSG.GH74.Generic.BProg.B1.Lift0
import CFSG.GH74.Generic.BProg.B1.PilotS1
import CFSG.GH74.Generic.JMaxCongr
import CFSG.GH74.Generic.OuterInvolution
import CFSG.Walter.AStar.Subnormal
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.GH74.Generic.BProg.B1.PilotS4
public import CFSG.GH74.Generic.S3.LeavesFine
public import CFSG.GH74.Generic.S3.Lem37

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q : Subgroup G}

namespace T3Sect13C1

theorem exists_conj_fixed {Pr : ∀ (Kt : Type) [Group Kt], Prop} (hF : InvolFixFour Pr)
    (hC : FourConj Pr) {X : Type} [Group X] [Finite X] {L : Subgroup X} (hL : L.Normal)
    (hPr : Pr ↥L) {E : Subgroup X} (hEL : E ≤ L) (hEel : IsElementaryAbelian 2 ↥E)
    (hE4 : Nat.card ↥E = 4) {y : X} (hy : orderOf y = 2) :
    ∃ k ∈ L, ∀ e ∈ E, y * (k * e * k⁻¹) = (k * e * k⁻¹) * y := by
  obtain ⟨E', hE'L, hE'el, hE'4, hE'y⟩ := hF X L hL hPr y hy
  have h1 : IsElementaryAbelian 2 ↥(E.subgroupOf L) := IsElementaryAbelian.subgroupOf hEL
  have h2 : Nat.card ↥(E.subgroupOf L) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE4]
  have h1' : IsElementaryAbelian 2 ↥(E'.subgroupOf L) := IsElementaryAbelian.subgroupOf hE'L
  have h2' : Nat.card ↥(E'.subgroupOf L) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'L).toEquiv, hE'4]
  obtain ⟨g, hg⟩ := hC ↥L hPr (E.subgroupOf L) (E'.subgroupOf L) h1 h2 h1' h2'
  refine ⟨(g : X), g.2, fun e he => ?_⟩
  have hmem : (⟨e, hEL he⟩ : ↥L) ∈ E.subgroupOf L := he
  have h3 : (MulAut.conj g).toMonoidHom ⟨e, hEL he⟩ ∈ E'.subgroupOf L := by
    rw [hg]; exact Subgroup.mem_map_of_mem _ hmem
  exact hE'y _ (Subgroup.mem_subgroupOf.1 h3)

theorem qShape345_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : QShape3 A ∨ QShape4 A ∨ QShape5 A) : QShape3 B ∨ QShape4 B ∨ QShape5 B := by
  rcases h with h | h | h
  · obtain ⟨p, f, hp, hp2, hq, h⟩ := h
    refine Or.inl ⟨p, f, hp, hp2, hq, ?_⟩
    rcases h with h | h
    · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h)
    · exact Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h)
  · obtain ⟨f, h⟩ := h
    exact Or.inr (Or.inl ⟨f, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h⟩)
  · obtain ⟨e'⟩ := h
    exact Or.inr (Or.inr ⟨e.symm.trans e'⟩)

theorem ker_le_pPrimeCore {K M : Subgroup G} (hKM : K ≤ M) :
    ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (Subgroup.inclusion hKM)).ker ≤
      pPrimeCore 2 ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := (QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (Subgroup.inclusion hKM) with hf
  have hker : f.ker = (pPrimeCore 2 ↥M).comap (Subgroup.inclusion hKM) := by
    rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hcop : Nat.Coprime 2 (Nat.card f.ker) := by
    rw [hker]
    exact (pPrimeCore_coprime_card (p := 2) (G := ↥M)).coprime_dvd_right
      (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hKM))
  exact le_sSup ⟨MonoidHom.normal_ker f, hcop⟩

theorem exists_odd_quotient_equiv {K L : Type*} [Group K] [Group L] [Finite K] (φ : K →* L)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ pPrimeCore 2 K) :
    ∃ (Z : Subgroup L) (_ : Z.Normal), Odd (Nat.card Z) ∧
      Nonempty ((K ⧸ pPrimeCore 2 K) ≃* (L ⧸ Z)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := pPrimeCore 2 K
  have hNn : N.Normal := pPrimeCore_normal
  have hZn : (N.map φ).Normal := hNn.map φ hφ
  refine ⟨N.map φ, hZn, ?_, ?_⟩
  · exact Odd.of_dvd_nat (Nat.coprime_two_left.1 pPrimeCore_coprime_card) (Subgroup.card_map_dvd _ _)
  · let ψ : K →* L ⧸ N.map φ := (QuotientGroup.mk' (N.map φ)).comp φ
    have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ
    have hψker : ψ.ker = N := by
      ext k
      constructor
      · intro hk
        have hk' : φ k ∈ N.map φ := (QuotientGroup.eq_one_iff _).1 hk
        obtain ⟨n, hn, hnk⟩ := hk'
        have hmem : n⁻¹ * k ∈ φ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hnk, inv_mul_cancel]
        have h2 := hker hmem
        have h3 := N.mul_mem hn h2
        simpa using h3
      · intro hk
        exact (QuotientGroup.eq_one_iff _).2 ⟨k, hk, rfl⟩
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

theorem exists_equiv_barIn {K M : Subgroup G} (hKM : K ≤ M) (hKc : IsComponent (barIn M K)) :
    Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* ↥(barIn M K)) := by
  let φ : ↥K →* ↥(barIn M K) :=
    ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (Subgroup.inclusion hKM)).codRestrict (barIn M K)
      (fun k => ⟨Subgroup.inclusion hKM k, k.2, rfl⟩)
  have hφs : Function.Surjective φ := by
    rintro ⟨y, m, hm, rfl⟩
    exact ⟨⟨m, hm⟩, rfl⟩
  have hker : φ.ker ≤ pPrimeCore 2 ↥K :=
    (MonoidHom.ker_codRestrict _ _ _).le.trans (ker_le_pPrimeCore hKM)
  obtain ⟨Z, hZn, hodd, ⟨e⟩⟩ := exists_odd_quotient_equiv φ hφs hker
  have hcore : pPrimeCore 2 (Mbar M) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hsub : (Z.map (barIn M K).subtype).IsSubnormal := by
    refine Subgroup.IsSubnormal.trans (Subgroup.map_subtype_le Z) ?_ hKc.2
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective (barIn M K).subtype_injective]
    exact hZn.isSubnormal
  have hodd' : Odd (Nat.card ↥(Z.map (barIn M K).subtype)) := by
    rw [Subgroup.card_map_of_injective (barIn M K).subtype_injective]
    exact hodd
  have hbot := CFSG.Walter.eq_bot_of_isSubnormal_of_odd hcore hsub hodd'
  have hZ : Z = ⊥ := (Subgroup.map_eq_bot_iff_of_injective Z (barIn M K).subtype_injective).1 hbot
  subst hZ
  exact ⟨e.trans (QuotientGroup.quotientBot (G := ↥(barIn M K)))⟩

theorem exists_conj_centralized (hF3 : InvolFixFour QShape3) (hF4 : InvolFixFour QShape4)
    (hF5 : InvolFixFour QShape5) (hC3 : FourConj QShape3) (hC4 : FourConj QShape4)
    (hC5 : FourConj QShape5) {x : G} {K A M E : Subgroup G} (hKM : K ≤ M) (hAM : A ≤ M)
    (hKx : K ≤ centralizer ({x} : Set G)) (hxM : x ∈ M)
    (hKc : IsComponent (barIn M K)) (hN : (barIn M K).Normal)
    (hshape : QShape3 (↥K ⧸ pPrimeCore 2 ↥K) ∨ QShape4 (↥K ⧸ pPrimeCore 2 ↥K) ∨
      QShape5 (↥K ⧸ pPrimeCore 2 ↥K))
    (hAel : IsElementaryAbelian 2 ↥A) (hEK : E ≤ K) (hEel : IsElementaryAbelian 2 ↥E)
    (hE4 : Nat.card ↥E = 4) (hAE : A = E ⊔ zpowers x) {y : G} (hyM : y ∈ M) (hy2 : orderOf y = 2)
    (hxy : y * x = x * y) :
    ∃ u ∈ M, ∀ a ∈ A, y * (u * a * u⁻¹) = (u * a * u⁻¹) * y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ : ↥M →* Mbar M := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hρ
  obtain ⟨e⟩ := exists_equiv_barIn hKM hKc
  have hshapeL := qShape345_of_mulEquiv e hshape
  have hEM : E ≤ M := hEK.trans hKM
  set E₀ : Subgroup ↥M := E.subgroupOf M with hE₀
  have hE₀el : IsElementaryAbelian 2 ↥E₀ := IsElementaryAbelian.subgroupOf hEM
  have hE₀2 : IsPGroup 2 ↥E₀ := CFSG.IsElementaryAbelian.isPGroup 2 _
  have hE₀card : Nat.card ↥E₀ = 4 := by
    rw [hE₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv, hE4]
  set Ē : Subgroup (Mbar M) := E₀.map ρ with hĒ
  have hĒel : IsElementaryAbelian 2 ↥Ē := IsElementaryAbelian.map ρ
  have hĒcard : Nat.card ↥Ē = 4 := by
    rw [hĒ, B1.PilotS1.card_map_eq_of_inj ρ E₀ (Thm2Comp.eq_one_of_isPGroup hE₀2), hE₀card]
  have hĒL : Ē ≤ barIn M K := by
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e, Subgroup.mem_subgroupOf.2 (hEK (Subgroup.mem_subgroupOf.1 he)), rfl⟩
  set y' : ↥M := ⟨y, hyM⟩ with hy'
  have hy'2 : orderOf y' = 2 := (Subgroup.orderOf_mk y hyM).trans hy2
  have hy'p : IsPGroup 2 ↥(zpowers y') := B1.isPGroup_two_zpowers_of_orderOf hy'2
  have hyb2 : orderOf (ρ y') = 2 := by
    have hsq : y' ^ 2 = 1 := by rw [← hy'2]; exact pow_orderOf_eq_one y'
    refine orderOf_eq_prime (by rw [← map_pow, hsq, map_one]) ?_
    · intro h1
      have := Thm2Comp.eq_one_of_isPGroup hy'p y' (mem_zpowers y') h1
      rw [this, orderOf_one] at hy'2
      omega
  obtain ⟨kb, hkbL, hkb⟩ : ∃ kb ∈ barIn M K, ∀ e ∈ Ē,
      ρ y' * (kb * e * kb⁻¹) = (kb * e * kb⁻¹) * ρ y' := by
    rcases hshapeL with h3 | h4 | h5
    · exact exists_conj_fixed hF3 hC3 hN h3 hĒL hĒel hĒcard hyb2
    · exact exists_conj_fixed hF4 hC4 hN h4 hĒL hĒel hĒcard hyb2
    · exact exists_conj_fixed hF5 hC5 hN h5 hĒL hĒel hĒcard hyb2
  obtain ⟨k', hk'K, rfl⟩ := hkbL
  have hk'x : (k' : G) * x = x * (k' : G) :=
    Subgroup.mem_centralizer_singleton_iff.1 (hKx (Subgroup.mem_subgroupOf.1 hk'K))
  set x' : ↥M := ⟨x, hxM⟩ with hx'
  have hk'x' : k' * x' = x' * k' := Subtype.ext hk'x
  have hy'x' : y' * x' = x' * y' := Subtype.ext hxy
  set Φ : ↥M →* Mbar M := ρ.comp (MulAut.conj k').toMonoidHom with hΦ
  set Z : Subgroup ↥M := (centralizer ({ρ y'} : Set (Mbar M))).comap Φ with hZ
  have hEZ : E ≤ Z.map M.subtype := by
    intro e he
    have heM : e ∈ M := hEM he
    refine ⟨⟨e, heM⟩, ?_, rfl⟩
    show (⟨e, heM⟩ : ↥M) ∈ Z
    have hmem : ρ ⟨e, heM⟩ ∈ Ē := Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.2 he)
    have h1 := hkb _ hmem
    rw [hZ, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    have h2 : Φ ⟨e, heM⟩ = ρ k' * ρ ⟨e, heM⟩ * (ρ k')⁻¹ := by
      simp [hΦ, MulAut.conj_apply, map_mul, map_inv]
    rw [h2]
    exact h1.symm
  have hxZ : x ∈ Z.map M.subtype := by
    refine ⟨x', ?_, rfl⟩
    show x' ∈ Z
    rw [hZ, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    have h2 : Φ x' = ρ x' := by
      have h3 : k' * x' * k'⁻¹ = x' := by rw [hk'x', mul_assoc, mul_inv_cancel, mul_one]
      show ρ (k' * x' * k'⁻¹) = ρ x'
      rw [h3]
    rw [h2, ← map_mul, ← map_mul, hy'x']
  have hAZ : A ≤ Z.map M.subtype := hAE ▸ sup_le hEZ (Subgroup.zpowers_le.2 hxZ)
  set B : Subgroup ↥M := (A.subgroupOf M).map (MulAut.conj k').toMonoidHom with hB
  have hA2 : IsPGroup 2 ↥(A.subgroupOf M) := (IsElementaryAbelian.isPGroup 2 A).comap_subtype
  have hB2 : IsPGroup 2 ↥B := hA2.map _
  have hcomm : ∀ b ∈ B, ρ y' * ρ b = ρ b * ρ y' := by
    rintro _ ⟨a', ha', rfl⟩
    have haA : (a' : G) ∈ A := Subgroup.mem_subgroupOf.1 ha'
    obtain ⟨a'', haZ, ha''⟩ := hAZ haA
    have haa : a'' = a' := Subtype.ext ha''
    subst haa
    have h1 : Φ a'' ∈ centralizer ({ρ y'} : Set (Mbar M)) := haZ
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    exact h1.symm
  have hOodd : Odd (Nat.card ↥(pPrimeCore 2 ↥M)) :=
    Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card
  have := (pPrimeCore_normal : (pPrimeCore 2 ↥M).Normal)
  obtain ⟨n, hn, hnB⟩ := T3Sect13Aux.exists_conj_commute (pPrimeCore 2 ↥M) hOodd hy'p hB2 hcomm
  refine ⟨((n * k' : ↥M) : G), (n * k' : ↥M).2, fun a ha => ?_⟩
  have haM : a ∈ M := hAM ha
  have h1 := hnB (k' * ⟨a, haM⟩ * k'⁻¹) ⟨⟨a, haM⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩
  have e1 : n * (k' * ⟨a, haM⟩ * k'⁻¹) * n⁻¹ = (n * k') * ⟨a, haM⟩ * (n * k')⁻¹ := by group
  rw [e1] at h1
  exact congrArg Subtype.val h1

end T3Sect13C1

theorem false_of_c1_S345_of (hZ : CenterlessS345) (hF3 : InvolFixFour QShape3)
    (hF4 : InvolFixFour QShape4) (hF5 : InvolFixFour QShape5) (hC3 : FourConj QShape3)
    (hC4 : FourConj QShape4) (hC5 : FourConj QShape5) (hs : Stage2Setup G x K A M P Q)
    (hKM : K ≤ M) (hQM : Q ≤ M) (h2 : Stage2Concl2 M)
    (hnot1 : ¬ QShape1 (↥K ⧸ pPrimeCore 2 ↥K)) {H : Subgroup G} (hH : IsMinSubnormalIn K M H)
    (hc1 : barIn M H = barIn M K) (hr : pRank 2 (CMbar M K) ≤ 1) : False := by
  obtain ⟨hN, T, hQT, hTM, hTx⟩ := sylow_center_of_c1 hs hKM hQM h2 hH hc1 hr
  have hx2 : orderOf x = 2 := hs.pair.1.1.1.1
  have hxT : x ∈ (T : Subgroup G) := hQT (x_mem_Q hs)
  have hxM : x ∈ M := hQM (x_mem_Q hs)
  obtain ⟨g, hgT, hgne⟩ :=
    exists_conj_in_sylow_ne hs.hyp.simple hs.hyp.nonab hx2 T hxT hTx
  have hyM : g⁻¹ * x * g ∈ M := hTM hgT
  have hy2 : orderOf (g⁻¹ * x * g) = 2 := by
    rw [← hx2]
    exact (isConj_iff.2 ⟨g⁻¹, by simp⟩ : IsConj x (g⁻¹ * x * g)).orderOf_eq.symm
  have hxy : (g⁻¹ * x * g) * x = x * (g⁻¹ * x * g) := hTx _ hgT
  have hne : g⁻¹ * x * g⁻¹⁻¹ ≠ x := by simpa using hgne
  have hcomm : (g⁻¹ * x * g⁻¹⁻¹) * x = x * (g⁻¹ * x * g⁻¹⁻¹) := by simpa using hxy
  obtain ⟨-, hAel, -, hcase⟩ := hs.src
  rcases hcase with ⟨-, h1⟩ | ⟨E, hEK, hAE, -, hEel, hE4, hshape⟩
  · exact hnot1 h1
  have hHsub : (barIn M H).IsSubnormal :=
    Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective _) hH.2.1.2
  have hKc : IsComponent (barIn M K) := isComponent_barIn_of_isSubnormal hs hKM (hc1 ▸ hHsub)
  have hAM : A ≤ M := (inU0_A hs).1.1
  have hKx : K ≤ centralizer ({x} : Set G) := hs.pair.1.1.1.2.2.1
  obtain ⟨u, huM, hu⟩ := T3Sect13C1.exists_conj_centralized hF3 hF4 hF5 hC3 hC4 hC5 hKM hAM hKx hxM
    hKc hN hshape hAel hEK hEel hE4 hAE hyM hy2 hxy
  refine not_centralizes_conj_A_of hZ hs hKM hQM h2 hH hc1 hr (h := g⁻¹) hne hcomm huM ?_
  intro a ha
  have := hu a ha
  rwa [inv_inv]

end CFSG.GH74.Generic.BProg.B2
