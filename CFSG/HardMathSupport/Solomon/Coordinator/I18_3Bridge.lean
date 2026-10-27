module

public import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssembly
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification

section General

variable {G : Type*} [Group G]

theorem i183_glaPComponent_iff {p : ℕ} {Y L : Subgroup G} :
    GLAPComponent p Y L ↔ L ≤ Y ∧ lBalanceIsPComponent p Y L := by
  constructor
  · rintro ⟨hLY, hsn, hcomp, hmin⟩
    refine ⟨hLY, (LBalance.pComponent_iff_minimal_image p Y L hLY).2 ⟨hsn, hcomp, ?_⟩⟩
    intro J hJL hJ hmap
    by_contra hne
    exact hmin J (lt_of_le_of_ne hJL hne) hJ hmap
  · rintro ⟨hLY, hL⟩
    obtain ⟨hsn, hcomp, hmin⟩ := (LBalance.pComponent_iff_minimal_image p Y L hLY).1 hL
    exact ⟨hLY, hsn, hcomp, fun J hJL hJ hmap => hJL.ne (hmin J hJL.le hJ hmap)⟩

theorem i183_glaPLayer_eq (p : ℕ) (Y : Subgroup G) : GLAPLayer p Y = lBalancePLayer p Y := by
  unfold GLAPLayer lBalancePLayer
  congr 1
  ext L
  exact i183_glaPComponent_iff.trans ⟨fun h => h.2, fun h => ⟨LBalance.subnormal_le h.1, h⟩⟩

theorem i183_glaPLayer_le (p : ℕ) (X : Subgroup G) : GLAPLayer p X ≤ X :=
  sSup_le fun _ hL => hL.1

theorem i183_barX_le_iff {p : ℕ} {X K : Subgroup G} (hKX : K ≤ X)
    {S : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)} :
    barX p X K ≤ S ↔ K ≤ (S.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).map X.subtype := by
  unfold barX
  rw [Subgroup.map_le_iff_le_comap]
  constructor
  · intro h x hx
    exact ⟨⟨x, hKX hx⟩, h (show (⟨x, hKX hx⟩ : ↥X) ∈ K.subgroupOf X from hx), rfl⟩
  · rintro h ⟨x, hxX⟩ hx
    obtain ⟨y, hy, hyx⟩ := h (show x ∈ K from hx)
    have hy' : y = ⟨x, hxX⟩ := Subtype.ext hyx
    rw [← hy']
    exact hy

theorem i183_barX_eq_bot_iff {p : ℕ} {X K : Subgroup G} (hKX : K ≤ X) :
    barX p X K = ⊥ ↔ K ≤ GLAPPrimeCoreOf p X := by
  rw [eq_bot_iff, i183_barX_le_iff hKX, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  rfl

theorem i183_barX_sup {p : ℕ} {X A B : Subgroup G} (hA : A ≤ X) (hB : B ≤ X) :
    barX p X (A ⊔ B) = barX p X A ⊔ barX p X B := by
  unfold barX
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem i183_mem_sup_of_mk_mem {p : ℕ} {X M : Subgroup G} {c : ↥X}
    (h : QuotientGroup.mk' (GLAPPrimeCore p ↥X) c ∈ barX p X M) :
    (c : G) ∈ M ⊔ GLAPPrimeCoreOf p X := by
  obtain ⟨m, hm, hmc⟩ := h
  have hmc' : m⁻¹ * c ∈ GLAPPrimeCore p ↥X := QuotientGroup.eq.1 hmc
  have e : (c : G) = (m : G) * ((m⁻¹ * c : ↥X) : G) := by simp
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (show (m : G) ∈ M from hm))
    (Subgroup.mem_sup_right ⟨_, hmc', rfl⟩)

theorem i183_subgroupOf_inf_centralizer {X E : Subgroup G} (hEX : E ≤ X) :
    (X ⊓ Subgroup.centralizer (E : Set G)).subgroupOf X =
      Subgroup.centralizer ((E.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
  ext z
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe, SetLike.coe_mem, true_and]
  constructor
  · intro h y hy
    exact Subtype.ext (h y hy)
  · intro h y hy
    exact congrArg Subtype.val (h ⟨y, hEX hy⟩ hy)

variable [Finite G]

theorem i183_glaPComponent_iff_isPComponent {p : ℕ} (hp : p.Prime) {Y L : Subgroup G} :
    GLAPComponent p Y L ↔ L ≤ Y ∧ CFSG.IsPComponent p (L.subgroupOf Y) := by
  have := Fact.mk hp
  rw [i183_glaPComponent_iff]
  exact and_congr_right fun hLY =>
    (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p Y L hLY).symm

theorem i183_glaPLayer_eq_map {p : ℕ} (hp : p.Prime) (Y : Subgroup G) :
    GLAPLayer p Y = (CFSG.pLayer ↥Y p).map Y.subtype := by
  have := Fact.mk hp
  rw [i183_glaPLayer_eq, LBalance.Asm.lBalancePLayer_eq_map]

open CFSG.ComponentClassification.CatalogueBPrimeJoin in
theorem i183_le_of_coprime_index {p : ℕ} (hp : p.Prime) {Y J A N : Subgroup G}
    (hJ : GLAPComponent p Y J) (hJA : J ≤ A) [(N.subgroupOf A).Normal]
    (hidx : p.Coprime (N.subgroupOf A).index) : J ≤ N := by
  have := Fact.mk hp
  have hJY : J ≤ Y := hJ.1
  have h1 : CFSG.IsPComponent p (J.subgroupOf Y) :=
    ((i183_glaPComponent_iff_isPComponent hp).1 hJ).2
  have h2 := primeResidual_eq_top_of_pComponent p _ h1
  let ψ : ↥(J.subgroupOf Y) →* ↥A :=
    (Subgroup.inclusion hJA).comp (Subgroup.subgroupOfEquivOfLe hJY).toMonoidHom
  have h3 := primeResidual_map_le p ψ
  have h4 := primeResidual_le_normal_of_coprime_index p (N.subgroupOf A) hidx
  intro x hx
  have hx' : (⟨⟨x, hJY hx⟩, hx⟩ : ↥(J.subgroupOf Y)) ∈ primeResidual p ↥(J.subgroupOf Y) := by
    rw [h2]
    exact Subgroup.mem_top _
  exact h4 (h3 ⟨_, hx', rfl⟩)

theorem i183_le_of_le_sup {p : ℕ} (hp : p.Prime) {Y J N O : Subgroup G}
    (hJ : GLAPComponent p Y J) (hO : p.Coprime (Nat.card O))
    (hON : O ≤ Subgroup.normalizer (N : Set G)) (hJNO : J ≤ N ⊔ O) : J ≤ N := by
  have hNA : N ≤ N ⊔ O := le_sup_left
  have hOA : O ≤ N ⊔ O := le_sup_right
  have hAN : N ⊔ O ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hON
  have : (N.subgroupOf (N ⊔ O)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).2 hAN
  refine i183_le_of_coprime_index hp hJ hJNO ?_
  have htop : O.subgroupOf (N ⊔ O) ⊔ N.subgroupOf (N ⊔ O) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hOA hNA, sup_comm, Subgroup.subgroupOf_self]
  have h1 := Subgroup.relIndex_sup_right (O.subgroupOf (N ⊔ O)) (N.subgroupOf (N ⊔ O))
  rw [htop, Subgroup.relIndex_top_right] at h1
  rw [h1]
  refine Nat.Coprime.coprime_dvd_right (Subgroup.relIndex_dvd_card _ _) ?_
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOA).toEquiv]

theorem i183_coprime_card_glaPPrimeCoreOf {p : ℕ} (hp : p.Prime) (X : Subgroup G) :
    p.Coprime (Nat.card (GLAPPrimeCoreOf p X)) :=
  (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp X)

theorem i183_le_or_commutator_eq_bot {p : ℕ} (hp : p.Prime) {H K N : Subgroup G}
    (hK : GLAPComponent p H K) (hNH : N ≤ H) [hN : (N.subgroupOf H).Normal] :
    K ≤ N ∨ ⁅barX p H K, barX p H N⁆ = ⊥ := by
  have : (barX p H N).Normal := hN.map _ (QuotientGroup.mk'_surjective _)
  rcases LocalComponents.normal_contains_or_commutes (barX p H K) (barX p H N) hK.2.2.1 with
    hle | hcomm
  · left
    refine i183_le_of_le_sup hp hK (i183_coprime_card_glaPPrimeCoreOf hp H) ?_ ?_
    · intro x hx
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).1 hN
        ((Subgroup.map_subtype_le _) hx)
    · intro k hk
      obtain ⟨n, hn, hnk⟩ := exists_of_barX_le hle hk (hK.1 hk)
      have e : k = n * (n⁻¹ * k) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hnk)
  · exact Or.inr hcomm

theorem i183_centralizer_barX_le {p : ℕ} (hp : p.Prime) {X E : Subgroup G} (hEX : E ≤ X)
    (hE : IsPGroup p ↥E) :
    Subgroup.centralizer (barX p X E : Set (↥X ⧸ GLAPPrimeCore p ↥X)) ≤
      barX p X (X ⊓ Subgroup.centralizer (E : Set G)) := by
  have := Fact.mk hp
  have hN : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥X) :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥X))
  have h := Semidihedral.Local.map_centralizer_eq_of_coprime p (GLAPPrimeCore p ↥X) hN
    (E.subgroupOf X) (hE.comap_of_injective X.subtype X.subtype_injective)
  unfold barX
  rw [i183_subgroupOf_inf_centralizer hEX, h]

end General

section LBalance

variable {G : Type} [Group G] [Finite G]

theorem i183_glaPLayer_inf_centralizer_le (hS : CatalogueRelativeB.CatalogueSchreier)
    {X E : Subgroup G} (hK : CFSG.Open.IsKGroup ↥X) {p : ℕ} (hp : p.Prime) (hEX : E ≤ X)
    (hE : IsPGroup p ↥E) :
    GLAPLayer p (X ⊓ Subgroup.centralizer (E : Set G)) ≤ GLAPLayer p X := by
  have hP : IsPGroup p ↥(E.subgroupOf X) := hE.comap_of_injective X.subtype X.subtype_injective
  rw [i183_glaPLayer_eq, i183_glaPLayer_eq,
    ← LBalance.pLayer_nested_map p (X ⊓ Subgroup.centralizer (E : Set G)) X inf_le_left,
    i183_subgroupOf_inf_centralizer hEX, ← LBalance.pLayer_nested_map p X X le_rfl,
    Subgroup.subgroupOf_self]
  exact Subgroup.map_mono (LBalance.l_balance_clauses hS ↥X hK p hp _ hP).2

end LBalance

end CFSG.HardMathSupport.Solomon.Coordinator
