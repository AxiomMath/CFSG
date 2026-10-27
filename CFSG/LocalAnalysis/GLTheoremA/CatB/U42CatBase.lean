module

public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Family
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FCover
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CyclicSylow
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.Lemma44

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Commute

variable {p : ℕ}

theorem mk_eq_one_iff_mem {X : Subgroup G} {z : G} (hz : z ∈ X) :
    (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨z, hz⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) = 1 ↔
      z ∈ GLAPPrimeCoreOf p X := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, chev_mem_glaPPrimeCoreOf_iff hz]

theorem comm_mem_core_of_ne {X L L' : Subgroup G} (hL : GLAPComponent p X L)
    (hL' : GLAPComponent p X L') (hne : L ≠ L') {l y : G} (hl : l ∈ L) (hy : y ∈ L') :
    ⁅l, y⁆ ∈ GLAPPrimeCoreOf p X := by
  have hbar : barX p X L ≠ barX p X L' := fun h => hne (glaPComponent_unique hL hL' h)
  have hcomm : ⁅barX p X L, barX p X L'⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hL.2.2.1 hL'.2.2.1 hbar
  have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hlX : l ∈ X := hL.1 hl
  have hyX : y ∈ X := hL'.1 hy
  have ha : (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) ∈
      barX p X L := ⟨⟨l, hlX⟩, (Subgroup.mem_subgroupOf).2 hl, rfl⟩
  have hb : (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, hyX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) ∈
      barX p X L' := ⟨⟨y, hyX⟩, (Subgroup.mem_subgroupOf).2 hy, rfl⟩
  have hab := Subgroup.mem_centralizer_iff.1 (hcen ha) _ hb
  have hzX : ⁅l, y⁆ ∈ X := by
    rw [commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem hlX hyX) (X.inv_mem hlX)) (X.inv_mem hyX)
  refine (mk_eq_one_iff_mem hzX).1 ?_
  have e : (⟨⁅l, y⁆, hzX⟩ : ↥X) = ⟨l, hlX⟩ * ⟨y, hyX⟩ * ⟨l, hlX⟩⁻¹ * ⟨y, hyX⟩⁻¹ := by
    apply Subtype.ext
    simp [commutatorElement_def]
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
  generalize (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) = a at hab ⊢
  generalize (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, hyX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) = b at hab ⊢
  rw [← hab]
  group

theorem card_gLBConj_eq (g : G) (H : Subgroup G) : Nat.card ↥(GLBConj g H) = Nat.card ↥H := by
  unfold GLBConj
  exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem gLBConj_eq_of_comm (hp : p.Prime) {X L : Subgroup G} (hL : GLAPComponent p X L) {y : G}
    (hyX : y ∈ X) (hyc : ∀ l ∈ L, ⁅l, y⁆ ∈ GLAPPrimeCoreOf p X) : GLBConj y L = L := by
  have hXy : GLBConj y X = X := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hyX)
  have h1 : GLAPComponent p X (GLBConj y L) := by
    have := glaPComponent_gLBConj hL y
    rwa [hXy] at this
  have hle : GLBConj y L ≤ L ⊔ GLAPPrimeCoreOf p X := by
    intro g hg
    rw [mem_gLBConj] at hg
    have hO : y⁻¹ * ⁅y * g * y⁻¹, y⁆ * y ∈ GLAPPrimeCoreOf p X := by
      have := conj_mem_glaPPrimeCoreOf (A := X) (Subgroup.inv_mem _ hyX) (hyc _ hg)
      simpa [mul_assoc] using this
    have e : g = (y⁻¹ * ⁅y * g * y⁻¹, y⁆ * y) * (y * g * y⁻¹)⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hO) (Subgroup.mem_sup_left (L.inv_mem (L.inv_mem hg)))
  have h2 : GLBConj y L ≤ L :=
    i183_le_of_le_sup hp h1 (i183_coprime_card_glaPPrimeCoreOf hp X)
      (i183_glaPPrimeCoreOf_le_normalizer hL) hle
  exact Subgroup.eq_of_le_of_card_ge h2 (card_gLBConj_eq y L ▸ le_rfl)

theorem mem_centMod_of_comm (hp : p.Prime) {X L : Subgroup G} (hL : GLAPComponent p X L) {y : G}
    (hyX : y ∈ X) (hyc : ∀ l ∈ L, ⁅l, y⁆ ∈ GLAPPrimeCoreOf p X) : y ∈ centModSubgroup p L := by
  have hN : y ∈ Subgroup.normalizer (L : Set G) :=
    mem_normalizer_iff_gLBConj_eq.2 (gLBConj_eq_of_comm hp hL hyX hyc)
  rw [mem_centModSubgroup]
  refine ⟨hN, fun l hl => ?_⟩
  have h1 : ⁅l, y⁆ ∈ L := by
    rw [commutatorElement_def]
    have : y * l⁻¹ * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hN _).1 (L.inv_mem hl)
    have e : l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) := by group
    rw [e]
    exact L.mul_mem hl this
  rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hL.2.1]
  exact ⟨h1, hyc l hl⟩

theorem isCyclic_gLBConj_iff (g : G) (Q : Subgroup G) : IsCyclic ↥(GLBConj g Q) ↔ IsCyclic ↥Q :=
  (Subgroup.equivMapOfInjective Q (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).isCyclic.symm

theorem isPGroup_gLBConj' (g : G) {Q : Subgroup G} (hQ : IsPGroup p ↥Q) : IsPGroup p ↥(GLBConj g Q) := by
  unfold GLBConj
  exact hQ.map _

theorem cent_le_normalizer (hp : p.Prime) {X L : Subgroup G} (hL : GLAPComponent p X L)
    (hcyc : CycModSylow p L) (hnc : ∃ Q : Subgroup G, Q ≤ L ∧ IsPGroup p ↥Q ∧ ¬ IsCyclic ↥Q) :
    X ≤ Subgroup.normalizer (L : Set G) := by
  intro c hcX
  by_contra hcn
  rw [mem_normalizer_iff_gLBConj_eq] at hcn
  have hXc : GLBConj c X = X := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hcX)
  have hL' : GLAPComponent p X (GLBConj c L) := by
    have := glaPComponent_gLBConj hL c
    rwa [hXc] at this
  have hcomm : ∀ y ∈ GLBConj c L, y ∈ centModSubgroup p L := fun y hy =>
    mem_centMod_of_comm hp hL (hL'.1 hy) (fun l hl =>
      comm_mem_core_of_ne hL hL' (Ne.symm hcn) hl hy)
  obtain ⟨Q, hQL, hQp, hQnc⟩ := hnc
  have h1 : GLBConj c Q ≤ GLBConj c L := gLBConj_mono (g := c) hQL
  have h2 : IsCyclic ↥(GLBConj c Q) :=
    hcyc _ (fun g hg => centMod_iff.2 (hcomm g (h1 hg))) (isPGroup_gLBConj' c hQp)
  exact hQnc ((isCyclic_gLBConj_iff c Q).1 h2)

end Commute

section Core

variable {x : G} {L : Subgroup G}

@[expose] noncomputable def actC (L : Subgroup G) {C : Subgroup G} (hCN : C ≤ Subgroup.normalizer (L : Set G)) :
    ↥C →* MulAut (PSimple 3 L) :=
  (chevAut 3 L).comp (Subgroup.inclusion hCN)

theorem mem_ker_actC {X : Subgroup G} (hL : GLAPComponent 3 X L) {C : Subgroup G}
    (hCN : C ≤ Subgroup.normalizer (L : Set G)) (c : ↥C) :
    c ∈ (actC L hCN).ker ↔ (c : G) ∈ centModSubgroup 3 L := by
  rw [MonoidHom.mem_ker, ← centMod_iff]
  exact chevAut_eq_one_iff Nat.prime_three hL (hCN c.2)

theorem mem_centMod_of_mem_centralizer (hxL : x ∈ Subgroup.centralizer (L : Set G)) :
    x ∈ centModSubgroup 3 L := by
  rw [mem_centModSubgroup]
  have hx : ∀ l ∈ L, l * x = x * l := fun l hl => Subgroup.mem_centralizer_iff.1 hxL l hl
  refine ⟨?_, fun l hl => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← hx h hh]
      simpa using hh
    · intro hh
      have h1 := hx _ hh
      have h2 : x * h = x * (x * h * x⁻¹) := by
        have : x * h * x⁻¹ * x = x * h := inv_mul_cancel_right _ _
        rw [this] at h1
        exact h1
      have h3 : h = x * h * x⁻¹ := mul_left_cancel h2
      rw [h3]
      exact hh
  · have : ⁅l, x⁆ = 1 := by
      rw [commutatorElement_def, hx l hl]
      group
    rw [this]
    exact (GLAPPrimeCoreOf 3 L).one_mem

theorem isTwoElem_mem_core (hL : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) L)
    (hcyc : CycModSylow 3 L) (hx3 : orderOf x = 3) (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hCN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G))
    {t : G} (ht : t ∈ Subgroup.centralizer ({x} : Set G)) (htm : t ∈ centModSubgroup 3 L)
    {k : ℕ} (htk : t ^ 2 ^ k = 1) :
    t ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({x} : Set G) with hC
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  set N : Subgroup ↥C := (actC L hCN).ker with hN
  have hNn : N.Normal := MonoidHom.normal_ker _
  have hmemN : ∀ c : ↥C, c ∈ N ↔ (c : G) ∈ centModSubgroup 3 L := mem_ker_actC hL hCN
  have hxN : (⟨x, hxC⟩ : ↥C) ∈ N := (hmemN _).2 (mem_centMod_of_mem_centralizer hxL)
  set z : ↥N := ⟨⟨x, hxC⟩, hxN⟩ with hz
  have hz3 : orderOf z = 3 := by
    rw [hz, Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact hx3
  have hzc : ∀ g : ↥N, g * z = z * g := by
    intro g
    apply Subtype.ext
    apply Subtype.ext
    show ((g : ↥C) : G) * x = x * ((g : ↥C) : G)
    exact Subgroup.mem_centralizer_singleton_iff.1 g.1.2
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥N) := inferInstance
  have hzzp : IsPGroup 3 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz3, pow_one])
  have hzP : z ∈ (P : Subgroup ↥N) := by
    have hzn : z ∈ Subgroup.normalizer ((P : Subgroup ↥N) : Set ↥N) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [show z * h * z⁻¹ = h by rw [← hzc h]; group]
    have hmem : z ∈ Subgroup.zpowers z ⊓ Subgroup.normalizer ((P : Subgroup ↥N) : Set ↥N) :=
      ⟨Subgroup.mem_zpowers z, hzn⟩
    have h := hzzp.inf_normalizer_sylow P
    have hmem' : z ∈ Subgroup.zpowers z ⊓ (P : Subgroup ↥N) := by
      rw [← h]
      exact hmem
    exact hmem'.2
  have hPcyc : IsCyclic ↥(P : Subgroup ↥N) := by
    set P₁ : Subgroup G := (((P : Subgroup ↥N).map N.subtype).map C.subtype) with hP₁
    have hP₁c : IsCyclic ↥P₁ := by
      refine hcyc P₁ ?_ ?_
      · rintro g ⟨_, ⟨n, hn, rfl⟩, rfl⟩
        exact centMod_iff.2 ((hmemN _).1 n.2)
      · exact (P.isPGroup'.map _).map _
    rw [hP₁] at hP₁c
    rwa [← (Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective).isCyclic,
      ← (Subgroup.equivMapOfInjective _ N.subtype N.subtype_injective).isCyclic] at hP₁c
  obtain ⟨M, hMn, hMc⟩ :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.exists_normal_complement_of_cyclic_sylow
      P hPcyc hzP hz3 hzc
  have hMcop : ¬ 3 ∣ Nat.card M := by
    have h1 : (P : Subgroup ↥N).index = Nat.card M := hMc.index_eq_card
    rw [← h1]
    exact P.not_dvd_index
  have hpel : ∀ n : ↥N, ¬ 3 ∣ orderOf n → n ∈ M := by
    intro n hn
    have hcard : Nat.card (↥N ⧸ M) = Nat.card (P : Subgroup ↥N) := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup M
      have h2 := hMc.card_mul_card
      have hM0 : 0 < Nat.card M := Nat.card_pos
      have : Nat.card (↥N ⧸ M) * Nat.card M = Nat.card (P : Subgroup ↥N) * Nat.card M := by
        rw [← h1, ← h2, mul_comm]
      exact Nat.eq_of_mul_eq_mul_right hM0 this
    have hq : orderOf (QuotientGroup.mk n : ↥N ⧸ M) ∣ Nat.card (P : Subgroup ↥N) := by
      rw [← hcard]
      exact orderOf_dvd_natCard _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (hq.trans (by
      rw [P.card_eq_multiplicity]))
    have hdvd : orderOf (QuotientGroup.mk n : ↥N ⧸ M) ∣ orderOf n :=
      orderOf_map_dvd (QuotientGroup.mk' M) n
    have hj0 : j = 0 := by
      by_contra hne
      exact hn ((dvd_pow_self 3 hne).trans (hj ▸ hdvd))
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
    exact (QuotientGroup.eq_one_iff n).1 hj
  set M' : Subgroup ↥C := M.map N.subtype with hM'
  have hM'cop : Nat.Coprime 3 (Nat.card M') := by
    rw [hM', Subgroup.card_map_of_injective N.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hMcop
  have hM'n : M'.Normal := by
    refine ⟨fun m hm c => ?_⟩
    obtain ⟨m₀, hm₀, rfl⟩ := hm
    have hcm : c * (m₀ : ↥C) * c⁻¹ ∈ N := hNn.conj_mem _ m₀.2 c
    have hord : orderOf (c * (m₀ : ↥C) * c⁻¹) = orderOf m₀ := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, Subgroup.orderOf_coe]
    have hmem : (⟨c * (m₀ : ↥C) * c⁻¹, hcm⟩ : ↥N) ∈ M := by
      refine hpel _ ?_
      rw [Subgroup.orderOf_mk, hord]
      intro hdvd
      exact hMcop (hdvd.trans (Subgroup.orderOf_dvd_natCard M hm₀))
    exact ⟨_, hmem, rfl⟩
  have hM'le : M' ≤ GLAPPrimeCore 3 ↥C := le_sSup ⟨hM'n, hM'cop⟩
  have htN : (⟨t, ht⟩ : ↥C) ∈ N := (hmemN _).2 htm
  have hord2 : ¬ 3 ∣ orderOf (⟨⟨t, ht⟩, htN⟩ : ↥N) := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    intro hdvd
    have h1 : orderOf t ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one htk
    have h2 : 3 ∣ 2 ^ k := hdvd.trans h1
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2) (by norm_num)
  have htM : (⟨t, ht⟩ : ↥C) ∈ M' := ⟨_, hpel _ hord2, rfl⟩
  exact (chev_mem_glaPPrimeCoreOf_iff ht).2 (hM'le htM)

end Core

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end
