module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdBasicZStar
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5DefsModel
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionZStarSylow
import CFSG.LocalAnalysis.OddStandard.GlueAlt
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdDefs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG.Open CFSG.GH74.GLS

section Cyclic

theorem eq_of_orderOf_two_of_isCyclic {P : Type} [Group P] [Finite P] [IsCyclic P] {a b : P}
    (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  classical
  have : Fintype P := Fintype.ofFinite P
  by_contra hab
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha
    omega
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hb
    omega
  have hsq : ∀ x : P, orderOf x = 2 → x ^ 2 = 1 := fun x hx => by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hle := IsCyclic.card_pow_eq_one_le (α := P) (n := 2) (by norm_num)
  have hsub : ({1, a, b} : Finset P) ⊆ Finset.univ.filter (fun x : P => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · simp
    · exact hsq _ ha
    · exact hsq _ hb
  have h3 : ({1, a, b} : Finset P).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
    simp [ha1.symm, hb1.symm]
  have := Finset.card_le_card hsub
  omega

variable {G : Type} [Group G] [Finite G]

theorem eq_of_involution_of_cyclic_sylow {H : Subgroup G}
    (hS : ∃ S : Sylow 2 H, IsCyclic (S : Subgroup H)) {z : G} (hzH : z ∈ H)
    (hzc : ∀ h ∈ H, h * z = z * h) (hz : orderOf z = 2) {x : G} (hxH : x ∈ H)
    (hx : orderOf x = 2) : x = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSc⟩ := hS
  set x' : H := ⟨x, hxH⟩
  set z' : H := ⟨z, hzH⟩
  have hx' : orderOf x' = 2 := by rw [Subgroup.orderOf_mk]; exact hx
  have hz' : orderOf z' = 2 := by rw [Subgroup.orderOf_mk]; exact hz
  have hp : IsPGroup 2 (zpowers x') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx', pow_one])
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hzcen : z' ∈ center H := by
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (hzc h h.2)
  have hz'P : z' ∈ (P : Subgroup H) :=
    CFSG.ComponentClassification.StandardRecognition.mem_sylow_of_mem_center_of_orderOf_eq_two
      hzcen hz' P
  have hx'P : x' ∈ (P : Subgroup H) := hP (Subgroup.mem_zpowers x')
  have hPc : IsCyclic (P : Subgroup H) := by
    have e := P.equiv S
    exact isCyclic_of_surjective (e.symm : (S : Subgroup H) →* (P : Subgroup H)) e.symm.surjective
  have := eq_of_orderOf_two_of_isCyclic (P := (P : Subgroup H)) (a := ⟨x', hx'P⟩)
    (b := ⟨z', hz'P⟩) (by rw [Subgroup.orderOf_mk]; exact hx')
    (by rw [Subgroup.orderOf_mk]; exact hz')
  exact congrArg (fun w : (P : Subgroup H) => ((w : H) : G)) this

theorem isCyclic_of_isPGroup_le {H : Subgroup G}
    (hS : ∃ S : Sylow 2 H, IsCyclic (S : Subgroup H)) {P : Subgroup G} (hPH : P ≤ H)
    (hP : IsPGroup 2 ↥P) : IsCyclic ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSc⟩ := hS
  have hP' : IsPGroup 2 ↥(P.subgroupOf H) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  have hQc : IsCyclic (Q : Subgroup H) := by
    have e := Q.equiv S
    exact isCyclic_of_surjective (e.symm : (S : Subgroup H) →* (Q : Subgroup H)) e.symm.surjective
  have h1 : IsCyclic ↥((P.subgroupOf H).subgroupOf (Q : Subgroup H)) := inferInstance
  have e1 : ↥((P.subgroupOf H).subgroupOf (Q : Subgroup H)) ≃* ↥(P.subgroupOf H) :=
    Subgroup.subgroupOfEquivOfLe hQ
  have e2 : ↥(P.subgroupOf H) ≃* ↥P := Subgroup.subgroupOfEquivOfLe hPH
  have e3 := e1.trans e2
  exact isCyclic_of_surjective (e3 : ↥((P.subgroupOf H).subgroupOf (Q : Subgroup H)) →* ↥P)
    e3.surjective

end Cyclic

section A1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem centralizer_singleton_eq_normalizer (hL : standardComponentIsStandard L) {z : G}
    (hzL : z ∈ L) (hzc : z ∈ centralizer (L : Set G)) (hz : orderOf z = 2)
    (hZ : Nat.card (center L) = 2) :
    centralizer ({z} : Set G) = normalizer (L : Set G) := by
  apply le_antisymm
  · exact (LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hL hzc hz).1
  · intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcz : c * z * c⁻¹ ∈ L := ((Subgroup.mem_normalizer_iff.1 hc) z).1 hzL
    have hz1 : z ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hz
      omega
    have hcen : (⟨c * z * c⁻¹, hcz⟩ : L) ∈ center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      show (l : G) * (c * z * c⁻¹) = c * z * c⁻¹ * l
      have hl' : c⁻¹ * (l : G) * c ∈ L :=
        ((Subgroup.mem_normalizer_iff.1 hc) (c⁻¹ * (l : G) * c)).2 (by simp [mul_assoc])
      have h1 := Subgroup.mem_centralizer_iff.1 hzc _ hl'
      calc (l : G) * (c * z * c⁻¹) = c * ((c⁻¹ * (l : G) * c) * z) * c⁻¹ := by group
        _ = c * (z * (c⁻¹ * (l : G) * c)) * c⁻¹ := by rw [h1]
        _ = c * z * c⁻¹ * l := by group
    have hzcen : (⟨z, hzL⟩ : L) ∈ center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hzc _ l.2)
    obtain ⟨w, -, hw⟩ := (Nat.card_eq_two_iff' (1 : center L)).1 hZ
    have e1 : (⟨⟨c * z * c⁻¹, hcz⟩, hcen⟩ : center L) = w := hw _ (by
      intro h
      have := congrArg (fun y : center L => ((y : L) : G)) h
      apply hz1
      simpa using this)
    have e2 : (⟨⟨z, hzL⟩, hzcen⟩ : center L) = w := hw _ (by
      intro h
      exact hz1 (congrArg (fun y : center L => ((y : L) : G)) h))
    have e3 := congrArg (fun y : center L => ((y : L) : G)) (e1.trans e2.symm)
    simp only at e3
    calc c * z = (c * z * c⁻¹) * c := by group
      _ = z * c := by rw [e3]

end A1

section Assembly

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G}

theorem exists_stdSetup (hL : standardComponentIsStandard L) {n : ℕ} (hn : 8 ≤ n)
    (hθ : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin n))) (hZ : Nat.card (center L) = 2)
    (hS : ∃ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G)))) :
    ∃ z : G, StdSetup G L n z := by
  have hq : CFSG.IsQuasisimple ↥L :=
    (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hL.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2dvd : 2 ∣ Nat.card (center L) := hZ ▸ dvd_rfl
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have hz : orderOf (((a : L)) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ha]
  have hzL : (((a : L)) : G) ∈ L := (a : L).2
  have hzC : (((a : L)) : G) ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val (mem_center_iff.mp a.2 ⟨l, hl⟩)
  have nonab : ∃ a b : G, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨a, b, fun h => hab ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext h
  refine ⟨((a : L) : G), nonab, hL, hn, ⟨hq, hZ, hθ⟩, hz, hzL, hzC,
    centralizer_singleton_eq_normalizer hL hzL hzC hz hZ, exists_commuting_conj nonab hz,
    fun P hPK hP => isCyclic_of_isPGroup_le hS hPK hP, fun x hx hx2 => ?_⟩
  refine eq_of_involution_of_cyclic_sylow hS hzC (fun h hh => ?_) hz hx hx2
  exact (Subgroup.mem_centralizer_iff.1 hh _ hzL).symm

instance AhatModel.instFiniteK {n : ℕ} (M : AhatModel G n L) : Finite M.K :=
  Finite.of_surjective M.e M.e.surjective

namespace StdSetup

variable {n : ℕ} {z : G}

theorem card_center (h : StdSetup G L n z) : Nat.card (center L) = 2 := h.cover.2.1

theorem pPrimeCore_eq_bot (h : StdSetup G L n z) : CFSG.pPrimeCore 2 ↥L = ⊥ :=
  GlueAlt.pPrimeCore_eq_bot_of_card_center_two h.cover.1 h.cover.2.1

theorem oddCoreOf_eq_bot (h : StdSetup G L n z) : oddCoreOf L = ⊥ := by
  rw [oddCoreOf, h.pPrimeCore_eq_bot, Subgroup.map_bot]

noncomputable def quotEquiv (h : StdSetup G L n z) : ↥L ≃* ↥L ⧸ CFSG.pPrimeCore 2 ↥L :=
  MulEquiv.ofBijective (QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥L))
    ⟨(MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk']; exact h.pPrimeCore_eq_bot),
      QuotientGroup.mk'_surjective _⟩

theorem cover_quot (h : StdSetup G L n z) :
    IsDoubleCoverOfAlt (↥L ⧸ CFSG.pPrimeCore 2 ↥L) n :=
  isDoubleCoverOfAlt_congr' h.quotEquiv h.cover

noncomputable def model (h : StdSetup G L n z) : AhatModel G n L :=
  AhatModel.ofCover h.cover_quot

theorem le_centralizer_singleton (h : StdSetup G L n z) : L ≤ centralizer ({z} : Set G) := by
  intro l hl
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.1 h.z_cent l hl

theorem centralizer_le_centralizer_singleton (h : StdSetup G L n z) :
    centralizer (L : Set G) ≤ centralizer ({z} : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.1 hc z h.z_mem).symm

theorem mem_normalizer_of_mem_centralizer (h : StdSetup G L n z) {c : G}
    (hc : c ∈ centralizer ({z} : Set G)) : c ∈ normalizer (L : Set G) :=
  h.cent_eq ▸ hc

theorem perm_eq_one_iff (h : StdSetup G L n z) (M : AhatModel G n L) {c : G}
    (hc : c ∈ normalizer (L : Set G)) : M.perm c hc = 1 ↔ c ∈ centralizer (L : Set G) := by
  rw [M.perm_eq_one_iff h.hn hc, Subgroup.mem_centralizer_iff]
  constructor
  · intro hcm l hl
    have := hcm l hl
    rw [h.oddCoreOf_eq_bot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · intro hcm l hl
    rw [h.oddCoreOf_eq_bot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcm l hl

theorem centralizer_inf_eq (h : StdSetup G L n z) : centralizer (L : Set G) ⊓ L = zpowers z := by
  have hz1 : z ≠ 1 := by
    intro h1
    have := h.hz
    rw [h1, orderOf_one] at this
    omega
  apply le_antisymm
  · rintro x ⟨hxK, hxL⟩
    have hxcen : (⟨x, hxL⟩ : L) ∈ center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxK l l.2)
    have hzcen : (⟨z, h.z_mem⟩ : L) ∈ center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 h.z_cent l l.2)
    obtain ⟨w, -, hw⟩ := (Nat.card_eq_two_iff' (1 : center L)).1 h.card_center
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · have e1 : (⟨⟨x, hxL⟩, hxcen⟩ : center L) = w := hw _ (fun h1 =>
        hx1 (congrArg (fun y : center L => ((y : L) : G)) h1))
      have e2 : (⟨⟨z, h.z_mem⟩, hzcen⟩ : center L) = w := hw _ (fun h1 =>
        hz1 (congrArg (fun y : center L => ((y : L) : G)) h1))
      have e3 := congrArg (fun y : center L => ((y : L) : G)) (e1.trans e2.symm)
      simp only at e3
      rw [e3]
      exact Subgroup.mem_zpowers z
  · rw [Subgroup.zpowers_le]
    exact ⟨h.z_cent, h.z_mem⟩

theorem exists_mem_perm_eq (h : StdSetup G L n z) (M : AhatModel G n L) {σ : Equiv.Perm (Fin n)}
    (hσ : Equiv.Perm.sign σ = 1) :
    ∃ (a : G) (ha : a ∈ L), M.perm a (Subgroup.le_normalizer ha) = σ := by
  obtain ⟨k, hk⟩ := M.C.exists_ρ_eq hσ
  obtain ⟨a, rfl⟩ := M.surj_mk k
  exact ⟨a, a.2, by rw [M.perm_of_mem h.hn a.2]; exact hk⟩

end StdSetup

end Assembly

end CFSG.OddStandard.Solomon75
