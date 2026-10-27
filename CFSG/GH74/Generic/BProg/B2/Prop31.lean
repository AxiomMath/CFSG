module

public import CFSG.GH74.Generic.BProg.B2.ShapeSporadic
public import CFSG.GH74.Generic.BProg.B2.GHTrichotomy
public import CFSG.GH74.Generic.BProg.BpGeneral
import CFSG.GH74.Generic.BProg.Stage1Split
public import CFSG.GH74.Generic.BProg.Stage2Frozen

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup

namespace Prop31

theorem orderOf_mk_involution {G : Type} [Group G] [Finite G] {M : Subgroup G} {x : G} (hxM : x ∈ M)
    (hx : orderOf x = 2) : orderOf (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd' : orderOf (⟨x, hxM⟩ : ↥M) = 2 := by rw [Subgroup.orderOf_mk]; exact hx
  have hO : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥M)) := pPrimeCore_coprime_card
  refine orderOf_eq_prime ?_ ?_
  · rw [← QuotientGroup.mk_pow, ← hd', pow_orderOf_eq_one, QuotientGroup.mk_one]
  · intro h
    have hdO : (⟨x, hxM⟩ : ↥M) ∈ pPrimeCore 2 ↥M := (QuotientGroup.eq_one_iff _).1 h
    have h2 : orderOf (⟨x, hxM⟩ : ↥M) ∣ Nat.card (pPrimeCore 2 ↥M) :=
      Subgroup.orderOf_dvd_natCard _ hdO
    rw [hd'] at h2
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hO h2

theorem faithful_of_simple {G : Type} [Group G] [Finite G] {x : G} {K A M P Q H : Subgroup G}
    (hs : Stage2Setup G x K A M P Q) (h3 : Stage3A x A M H) :
    ∀ n : Mbar M, (∀ h ∈ barIn M H, n * h = h * n) → n = 1 := by
  intro n hn
  obtain ⟨hF, hsimple⟩ := h3.H_simple
  have hcent : n ∈ Subgroup.centralizer (generalizedFitting (Mbar M) : Set (Mbar M)) := by
    rw [← hF, Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hn h hh).symm
  have hnF : n ∈ barIn M H := hF ▸ centralizer_generalizedFitting_le (Mbar M) hcent
  have hcen : (⟨n, hnF⟩ : ↥(barIn M H)) ∈ Subgroup.center ↥(barIn M H) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hn g g.2).symm
  rw [GHTrichotomy.center_eq_bot_of_simple_nonab hsimple (barIn_nonabelian hs h3),
    Subgroup.mem_bot] at hcen
  exact congrArg Subtype.val hcen

theorem isPCompIn_barIn_centralizer {G : Type} [Group G] [Finite G] {x : G} {K M : Subgroup G}
    (hxM : x ∈ M) (hCx : centralizer ({x} : Set G) ≤ M) (hx : orderOf x = 2)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) :
    IsPCompIn 2 (centralizer ({(QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M)} : Set (Mbar M)))
      (barIn M K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := isPCompIn_subgroupOf hCx hK
  have h2 : centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M) =
      (centralizer ({x} : Set G)).subgroupOf M := by
    rw [centralizer_singleton_mk_eq_subgroupOf hxM, inf_eq_right.2 hCx]
  rw [← h2] at h1
  have hd : (⟨x, hxM⟩ : ↥M) * ⟨x, hxM⟩ = 1 := by
    have h := pow_orderOf_eq_one (⟨x, hxM⟩ : ↥M)
    rwa [Subgroup.orderOf_mk, hx, pow_two] at h
  exact isPCompIn_map_cenQuot (pPrimeCore 2 ↥M) pPrimeCore_coprime_card hd h1

theorem isCompIn_barIn_centralizer (hB : B_B2_g4) {G : Type} [Group G] [Finite G] {x : G}
    {K A M P Q : Subgroup G} (hs : Stage2Setup G x K A M P Q)
    (hxM : x ∈ M) (hCx : centralizer ({x} : Set G) ≤ M) :
    IsCompIn (centralizer ({(QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M)} : Set (Mbar M)))
      (barIn M K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx : orderOf x = 2 := hs.pair.1.1.1.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hs.pair.1.1.1.2.2
  have hgM : Gen4 ↥M := Gen4.subgroup M hs.hyp.gen4
  have hkM : IsKGroupNative ↥M := isKGroupNative_of_kgh hs.hyp.kgh hs.maxM.1
  exact hB (Mbar M) (Gen4.quotient (pPrimeCore 2 ↥M) hgM)
    (CFSG.SectionRank.IsKGroupCat.quotient hkM (pPrimeCore 2 ↥M))
    (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2) _ (orderOf_mk_involution hxM hx) _
    (isPCompIn_barIn_centralizer hxM hCx hx hK)

theorem isCompIn_of_le {Y : Type*} [Group Y] {C D K : Subgroup Y} (hKD : K ≤ D) (hDC : D ≤ C)
    (hK : IsCompIn C K) : IsCompIn D K := by
  obtain ⟨hKC, hq, hsub⟩ := hK
  refine ⟨hKD, ?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe hKC).trans (Subgroup.subgroupOfEquivOfLe hKD).symm) hq
  · have h1 := hsub.comap (Subgroup.inclusion hDC)
    have h2 : (K.subgroupOf C).comap (Subgroup.inclusion hDC) = K.subgroupOf D := by
      ext z
      simp [Subgroup.mem_subgroupOf]
    rwa [h2] at h1

theorem isQuasisimple_of_isCompIn {Y : Type*} [Group Y] {C K : Subgroup Y} (h : IsCompIn C K) :
    IsQuasisimple ↥K :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1) h.2.1

theorem normal_le_center_of_odd {Q : Type*} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    {Z : Subgroup Q} (hZ : Z.Normal) (hodd : Odd (Nat.card Z)) : Z ≤ center Q := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hZ with h | h
  · exfalso
    have hsolvZ : Group.IsSolvable ↥Z := CFSG.Milestones.odd_order_solvable hodd
    rw [h] at hsolvZ
    have hsolQ : Group.IsSolvable Q := Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.topEquiv (G := Q)).symm.toMonoidHom) (Subgroup.topEquiv (G := Q)).symm.injective
    have := hQ.1
    have := CFSG.LocalCores.isQuasisimple_nontrivial hQ
    exact Group.IsPerfect.not_isSolvable _ hsolQ
  · exact h

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

theorem ker_le_pPrimeCore {G : Type} [Group G] [Finite G] {K M : Subgroup G} (hKM : K ≤ M) :
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

theorem exists_shape {G : Type} [Group G] [Finite G] {x : G} {K A M P Q : Subgroup G}
    (hs : Stage2Setup G x K A M P Q) (hKM : K ≤ M) (hq : IsQuasisimple ↥(barIn M K)) :
    ∃ Z : Subgroup ↥(barIn M K), Z ≤ center ↥(barIn M K) ∧ Odd (Nat.card ↥Z) ∧
      ∃ _ : Z.Normal, QShapeNS (↥(barIn M K) ⧸ Z) := by
  let φ : ↥K →* ↥(barIn M K) :=
    ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (Subgroup.inclusion hKM)).codRestrict (barIn M K)
      (fun k => ⟨Subgroup.inclusion hKM k, k.2, rfl⟩)
  have hφs : Function.Surjective φ := by
    rintro ⟨y, m, hm, rfl⟩
    exact ⟨⟨m, hm⟩, rfl⟩
  have hker : φ.ker ≤ pPrimeCore 2 ↥K :=
    (MonoidHom.ker_codRestrict _ _ _).le.trans (ker_le_pPrimeCore hKM)
  obtain ⟨Z, hZ, hodd, ⟨e⟩⟩ := exists_odd_quotient_equiv φ hφs hker
  exact ⟨Z, normal_le_center_of_odd hq hZ hodd, hodd, hZ,
    QShapeNS.of_mulEquiv e (qShapeNS_of_isSource2 hs.src)⟩

end Prop31

theorem shapeInCent_of_isCompIn {G : Type} [Group G] [Finite G] {x : G} {K A M P Q H : Subgroup G}
    (hs : Stage2Setup G x K A M P Q) (h1 : Stage2Concl1Core x K M Q H) (h3 : Stage3A x A M H)
    (hxM : x ∈ M)
    (hcomp : IsCompIn (centralizer ({(QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M)} : Set (Mbar M)))
      (barIn M K)) :
    ShapeInCent (barIn M H) (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M) (barIn M K) := by
  have hKH : K ≤ H := h1.H_min.1
  have hbarKH : barIn M K ≤ barIn M H := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, hKH hm, rfl⟩
  exact
    { normal := by
        rw [h3.H_simple.1]
        exact (CFSG.LocalCores.generalized_fitting_characteristic).2
      simple := h3.H_simple.2
      faithful := Prop31.faithful_of_simple hs h3
      inv := Prop31.orderOf_mk_involution hxM hs.pair.1.1.1.1
      comp := Prop31.isCompIn_of_le (le_inf hbarKH hcomp.1) inf_le_right hcomp
      shape := Prop31.exists_shape hs h1.K_le (Prop31.isQuasisimple_of_isCompIn hcomp) }

theorem shapeInCent_of_stage3A (hB : B_B2_g4) {G : Type} [Group G] [Finite G] {x : G}
    {K A M P Q H : Subgroup G}
    (hs : Stage2Setup G x K A M P Q) (h1 : Stage2Concl1Core x K M Q H) (h3 : Stage3A x A M H) :
    ∃ (hxM : x ∈ M) (L : Subgroup (Mbar M)),
      ShapeInCent (barIn M H) (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M) L := by
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxM : x ∈ M := h3.Cx_le hxC
  exact ⟨hxM, barIn M K, shapeInCent_of_isCompIn hs h1 h3 hxM
    (Prop31.isCompIn_barIn_centralizer hB hs hxM h3.Cx_le)⟩

theorem stage2Prop31_proved
    (hB : B_B2_g4) : Stage2Prop31 := by
  intro G _ _ x K A M P Q H hs h1 h3 _
  obtain ⟨hxM, L, hL⟩ := shapeInCent_of_stage3A hB hs (Stage2Concl1.toCore h1) h3
  exact ofLieType_of_shapeInCent hL (barIn_trichotomy hs h3)

end CFSG.GH74.Generic.BProg.B2
