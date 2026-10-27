module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51Sylow
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51Comm
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51Tools
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Reduce

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section Cal

theorem exists_le_of_le_iSup_in {G : Type*} [Group G] [Finite G] {C L : Subgroup G}
    (hLC : L ≤ C) (hL : IsPComponent 2 (L.subgroupOf C)) {ι : Type*} [Finite ι]
    (N : ι → Subgroup G) (hNC : ∀ i, N i ≤ C) (hNs : ∀ i, ((N i).subgroupOf C).IsSubnormal)
    (hle : L ≤ ⨆ i, N i) : ∃ i, L ≤ N i := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle' : L.subgroupOf C ≤ ⨆ i, (N i).subgroupOf C := by
    rw [← Subgroup.map_le_map_iff_of_injective C.subtype_injective, Subgroup.map_iSup]
    rw [Subgroup.map_subgroupOf_eq_of_le hLC]
    refine hle.trans (le_of_eq ?_)
    refine iSup_congr fun i => ?_
    exact (Subgroup.map_subgroupOf_eq_of_le (hNC i)).symm
  obtain ⟨i, hi⟩ :=
    exists_le_of_le_iSup 2 (L.subgroupOf C) hL (fun i => (N i).subgroupOf C) hNs hle'
  refine ⟨i, ?_⟩
  have h2 := Subgroup.map_mono (f := C.subtype) hi
  rwa [Subgroup.map_subgroupOf_eq_of_le hLC, Subgroup.map_subgroupOf_eq_of_le (hNC i)] at h2


theorem le_commutator_sup_pPrimeCoreOf {G : Type*} [Group G] {E : Subgroup G}
    (hq : IsTwoGenQuasi ↥E) : E ≤ ⁅E, E⁆ ⊔ pPrimeCoreOf 2 E := by
  let π : ↥E →* ↥E ⧸ pPrimeCore 2 ↥E := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hperf : ⁅(⊤ : Subgroup (↥E ⧸ pPrimeCore 2 ↥E)),
      (⊤ : Subgroup (↥E ⧸ pPrimeCore 2 ↥E))⁆ = ⊤ := by
    have := hq.2.1.1
    rwa [_root_.commutator_def] at this
  intro x hx
  have h1 : π ⟨x, hx⟩ ∈ (⁅(⊤ : Subgroup ↥E), (⊤ : Subgroup ↥E)⁆).map π := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπ, hperf]
    exact Subgroup.mem_top _
  obtain ⟨c, hc, hcx⟩ := h1
  have hcE : (c : G) ∈ ⁅E, E⁆ := by
    have : (⁅(⊤ : Subgroup ↥E), (⊤ : Subgroup ↥E)⁆).map E.subtype = ⁅E, E⁆ := by
      have htop : (⊤ : Subgroup ↥E).map E.subtype = E := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [Subgroup.map_commutator, htop]
    rw [← this]
    exact ⟨c, hc, rfl⟩
  have ho : c⁻¹ * ⟨x, hx⟩ ∈ pPrimeCore 2 ↥E := by
    have := (QuotientGroup.eq (a := c) (b := ⟨x, hx⟩)).1 hcx
    exact this
  have hxe : x = (c : G) * ((c⁻¹ * ⟨x, hx⟩ : ↥E) : G) := by simp
  rw [hxe]
  exact Subgroup.mul_mem_sup hcE ⟨c⁻¹ * ⟨x, hx⟩, ho, rfl⟩


theorem not_le_oddCoreOf_of_isTwoGenQuasi {G : Type} [Group G] [Finite G] {E C : Subgroup G}
    (hq : IsTwoGenQuasi ↥E) : ¬ E ≤ oddCoreOf C := by
  intro hle
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.Coprime 2 (Nat.card (oddCoreOf C)) := by
    have h1 : Nat.card (oddCoreOf C) = Nat.card (pPrimeCore 2 ↥C) :=
      Subgroup.card_map_of_injective C.subtype_injective
    rw [h1]
    exact pPrimeCore_coprime_card
  have hcop : Nat.Coprime 2 (Nat.card ↥E) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle) hcard
  have hbot : primeResidual 2 ↥E = ⊥ := primeResidual_eq_bot_of_coprime_card 2 hcop
  have htop := hq.1
  rw [hbot] at htop
  have hsub : Subsingleton ↥E := by
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ (⊤ : Subgroup ↥E) := Subgroup.mem_top a
    have hb : b ∈ (⊤ : Subgroup ↥E) := Subgroup.mem_top b
    rw [← htop, Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  have hnt : Nontrivial (↥E ⧸ pPrimeCore 2 ↥E) := CFSG.LocalCores.isQuasisimple_nontrivial hq.2
  have : Subsingleton (↥E ⧸ pPrimeCore 2 ↥E) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [Subsingleton.elim a b]
  exact not_subsingleton _ this


theorem exists_isComponent_le_of_isPComponent_centralizer {G : Type} [Group G] [Finite G] {u : G}
    (hu : u ∈ layer G) {E : Subgroup G} (hEC : E ≤ centralizer ({u} : Set G))
    (hEL : E ≤ layer G) (hE : IsPComponent 2 (E.subgroupOf (centralizer ({u} : Set G)))) :
    ∃ K : Subgroup G, IsComponent K ∧ E ≤ K := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({u} : Set G) with hCdef
  have hEsub : (E.subgroupOf C).IsSubnormal := (isPComponent_two_iff.1 hE).1
  have hEq : IsTwoGenQuasi ↥E :=
    (isTwoGenQuasi_subgroupOf_iff hEC).1 (isPComponent_two_iff.1 hE).2
  have hS0fin : {K : Subgroup G | IsComponent K}.Finite := Set.toFinite _
  set S : Finset (Subgroup G) := hS0fin.toFinset with hS
  have hmemS : ∀ K, K ∈ S ↔ IsComponent K := fun K => by simp [hS]
  have hsup : S.sup id = layer G := by
    rw [Finset.sup_id_eq_sSup]
    have : (↑S : Set (Subgroup G)) = {K : Subgroup G | IsComponent K} := hS0fin.coe_toFinset
    rw [this]
    rfl
  have hcomm : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro A hA B hB hAB a ha b hb
    rcases LocalCores.distinct_components_commute ((hmemS A).1 hA) ((hmemS B).1 hB) with h | h
    · exact absurd h hAB
    · have : a ∈ centralizer (B : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha
      exact ((Subgroup.mem_centralizer_iff.mp this) b hb).symm
  have hnorm : ∀ A ∈ S, ∀ g ∈ S.sup id, ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
    intro A hA g hg a ha
    have hle : S.sup id ≤ normalizer (A : Set G) := by
      refine Finset.sup_le fun B hB => ?_
      by_cases hAB : B = A
      · subst hAB
        exact Subgroup.le_normalizer
      · intro b hb
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          have := hcomm B hB A hA hAB b hb y hy
          rwa [this, mul_inv_cancel_right]
        · intro hy
          have h1 := hcomm B hB A hA hAB b⁻¹ (B.inv_mem hb) _ hy
          have h2 : y = b⁻¹ * (b * y * b⁻¹) * b := by group
          have h3 : b⁻¹ * (b * y * b⁻¹) * b = b * y * b⁻¹ := by rw [h1, inv_mul_cancel_right]
          have e : y = b * y * b⁻¹ := h2.trans h3
          rw [e]
          exact hy
    exact (Subgroup.mem_normalizer_iff.1 (hle hg) a).1 ha
  have hEs : E ≤ S.sup id := hsup ▸ hEL
  have hcp : ⁅E, E⁆ ≤ S.sup (fun A => A ⊓ C) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxu : ⁅x, u⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
      (Subgroup.mem_centralizer_singleton_iff.1 (hEC hx))
    have hyu : ⁅y, u⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
      (Subgroup.mem_centralizer_singleton_iff.1 (hEC hy))
    exact comm_mem_sup_inf_centralizer S hcomm (hsup ▸ hu) (hEs hx) (hEs hy)
      (fun g _ => by rw [hxu]; simp) (fun g _ => by rw [hyu]; simp)
  have hOC : pPrimeCoreOf 2 E ≤ oddCoreOf C := pPrimeCoreOf_le_oddCoreOf hEC hEsub
  have hE2 : E ≤ S.sup (fun A => A ⊓ C) ⊔ oddCoreOf C :=
    (le_commutator_sup_pPrimeCoreOf hEq).trans (sup_le_sup hcp hOC)
  let N : Option {K : Subgroup G // K ∈ S} → Subgroup G := fun o =>
    match o with
    | none => oddCoreOf C
    | some K => K.1 ⊓ C
  have hNC : ∀ i, N i ≤ C := by
    intro i
    cases i with
    | none => exact oddCoreOf_le C
    | some K => exact inf_le_right
  have hNs : ∀ i, ((N i).subgroupOf C).IsSubnormal := by
    intro i
    cases i with
    | none =>
      have h : (oddCoreOf C).subgroupOf C = pPrimeCore 2 ↥C := by
        unfold oddCoreOf
        exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
      show ((oddCoreOf C).subgroupOf C).IsSubnormal
      rw [h]
      exact (pPrimeCore_normal).isSubnormal
    | some K =>
      show ((K.1 ⊓ C).subgroupOf C).IsSubnormal
      rw [Subgroup.inf_subgroupOf_right]
      exact ((hmemS K.1).1 K.2).2.subgroupOf
  have hle : E ≤ ⨆ i, N i := by
    rw [iSup_option]
    refine hE2.trans ?_
    rw [sup_comm]
    refine sup_le_sup le_rfl ?_
    exact Finset.sup_le fun A hA => le_iSup (fun K : {K : Subgroup G // K ∈ S} => K.1 ⊓ C) ⟨A, hA⟩
  obtain ⟨i, hi⟩ := exists_le_of_le_iSup_in hEC hE N hNC hNs hle
  cases i with
  | none => exact absurd hi (not_le_oddCoreOf_of_isTwoGenQuasi hEq)
  | some K => exact ⟨K.1, (hmemS K.1).1 K.2, hi.trans inf_le_left⟩


theorem le_of_le_sup_pPrimeCore {D : Type} [Group D] [Finite D] {M E : Subgroup D}
    (hM : IsPComponent 2 M) (hgen : primeResidual 2 ↥E = ⊤) (h : E ≤ M ⊔ pPrimeCore 2 D) :
    E ≤ M := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (pPrimeCore 2 D)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hnorm := pPrimeCore_le_normalizer_of_isPComponent hM
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥E) ∈ primeResidual 2 ↥E := by rw [hgen]; exact Subgroup.mem_top _
  rw [primeResidual_eq_closure] at hy'
  have hcl : Subgroup.closure {x : ↥E | ∃ k : ℕ, orderOf x = 2 ^ k} ≤ M.comap E.subtype := by
    rw [Subgroup.closure_le]
    rintro x ⟨k, hk⟩
    have hxk : (x : D) ^ (2 ^ k) = 1 := by
      have := pow_orderOf_eq_one x
      rw [hk] at this
      exact congrArg Subtype.val this
    obtain ⟨o, ho, a, ha, hak, hxa⟩ := exists_conj_twoElt_of_mem_sup_odd hodd (h x.2) hxk
    show (x : D) ∈ M
    rw [hxa]
    exact (Subgroup.mem_normalizer_iff.1 (hnorm ho) a).1 ha
  exact hcl hy'

theorem exists_isPComponent_le_of_mem_pLayer {D : Type} [Group D] [Finite D] {u : D}
    {E : Subgroup D} (hEC : E ≤ centralizer ({u} : Set D)) (huE : u ∈ E) (hu2 : u ^ 2 = 1)
    (hE : IsPComponent 2 (E.subgroupOf (centralizer ({u} : Set D))))
    (hEL : E ≤ pLayer D 2) : ∃ M : Subgroup D, IsPComponent 2 M ∧ E ≤ M := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup D := pPrimeCore 2 D with hO
  set q : D →* D ⧸ O := QuotientGroup.mk' O with hq
  have hker : ¬ 2 ∣ Nat.card q.ker := by
    rw [hq, QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 pPrimeCore_coprime_card
  have hEq : IsTwoGenQuasi ↥E :=
    (isTwoGenQuasi_subgroupOf_iff hEC).1 (isPComponent_two_iff.1 hE).2
  have hlay : (pLayer D 2).map q = layer (D ⧸ O) :=
    ComponentClassification.LBalance.Quot.map_pLayer_eq_layer_quotient
  have hEL' : E.map q ≤ layer (D ⧸ O) := hlay ▸ Subgroup.map_mono hEL
  have huL : q u ∈ layer (D ⧸ O) := hEL' ⟨u, huE, rfl⟩
  have hcentr : (centralizer ({u} : Set D)).map q = centralizer ({q u} : Set (D ⧸ O)) := by
    have hT : IsPGroup 2 ↥(Subgroup.zpowers u) := by
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
        (by simpa using orderOf_dvd_of_pow_eq_one hu2 : orderOf u ∣ 2 ^ 1)
      exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
    have : Fact (IsPGroup 2 ↥(Subgroup.zpowers u)) := ⟨hT⟩
    have h := centralizer_map_quotient_eq_map_centralizer 2 (Subgroup.zpowers u) O
      pPrimeCore_normal pPrimeCore_coprime_card
    simp only at h
    rw [Subgroup.zpowers_eq_closure, MonoidHom.map_closure, Set.image_singleton] at h
    simp only [Subgroup.centralizer_closure] at h
    exact h.symm
  have hEC' : E.map q ≤ centralizer ({q u} : Set (D ⧸ O)) := hcentr ▸ Subgroup.map_mono hEC
  have hE' : IsPComponent 2 ((E.map q).subgroupOf (centralizer ({q u} : Set (D ⧸ O)))) := by
    have := ComponentClassification.GSThmB.OddQuot.isPComponent_map q hker hEC hE
    rwa [hcentr] at this
  obtain ⟨K, hK, hEK⟩ :=
    exists_isComponent_le_of_isPComponent_centralizer huL hEC' hEL' hE'
  obtain ⟨M, hM, hMK⟩ := LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent 2 hK
  refine ⟨M, hM, ?_⟩
  have h1 : E ≤ M ⊔ O := by
    have : E ≤ (M.map q).comap q := by
      rw [hMK]
      exact Subgroup.map_le_iff_le_comap.1 hEK
    rwa [Subgroup.comap_map_eq, hq, QuotientGroup.ker_mk'] at this
  exact le_of_le_sup_pPrimeCore hM hEq.1 h1

end Cal

end CFSG.OddStandard.Solomon75
