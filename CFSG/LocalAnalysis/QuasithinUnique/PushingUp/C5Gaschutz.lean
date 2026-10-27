module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.QuasithinUnique.C5

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem exists_complement_elemAb2 [Finite G] {E F : Subgroup G} (hE : ElemAb2 E) (hFE : F ≤ E) :
    ∃ C : Subgroup G, C ≤ E ∧ C ⊓ F = ⊥ ∧ C ⊔ F = E := by
  obtain ⟨C, ⟨hCE, hCF⟩, hmax⟩ :=
    exists_max_card (fun C : Subgroup G => C ≤ E ∧ C ⊓ F = ⊥) ⟨bot_le, bot_inf_eq F⟩
  refine ⟨C, hCE, hCF, ?_⟩
  by_contra hne
  obtain ⟨e, heE, heCF⟩ : ∃ e ∈ E, e ∉ C ⊔ F := by
    by_contra h
    push Not at h
    exact hne (le_antisymm (sup_le hCE hFE) h)
  have he2 : e ^ 2 = 1 := hE.sq_eq_one heE
  have hZE : zpowers e ≤ E := Subgroup.zpowers_le.mpr heE
  have hcomm' : ∀ a ∈ C, ∀ b ∈ zpowers e, a * b = b * a := fun a ha b hb =>
    hE.1 a (hCE ha) b (hZE hb)
  have hC'E : C ⊔ zpowers e ≤ E := sup_le hCE hZE
  have hC'F : (C ⊔ zpowers e) ⊓ F = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨c, hc, b, hb, rfl⟩ := mem_sup_of_commute hcomm' hx1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
    · have h1 : e ^ (2 * n) = 1 := by
        rw [zpow_mul]
        have : e ^ (2 : ℤ) = 1 := by simpa using he2
        rw [this, one_zpow]
      rw [h1, mul_one] at hx2 ⊢
      have : c ∈ C ⊓ F := ⟨hc, hx2⟩
      rw [hCF] at this
      exact this
    · exfalso
      have h1 : e ^ (2 * n + 1) = e := by
        rw [zpow_add_one, zpow_mul]
        have : e ^ (2 : ℤ) = 1 := by simpa using he2
        rw [this, one_zpow, one_mul]
      rw [h1] at hx2
      apply heCF
      have : e = c⁻¹ * (c * e) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (mem_sup_left hc)) (mem_sup_right hx2)
  have hcard : Nat.card (C ⊔ zpowers e : Subgroup G) ≤ Nat.card C := hmax _ ⟨hC'E, hC'F⟩
  have hEq : C = C ⊔ zpowers e := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
  apply heCF
  have hmem : e ∈ C ⊔ zpowers e := mem_sup_right (Subgroup.mem_zpowers e)
  rw [← hEq] at hmem
  exact mem_sup_left hmem

theorem exists_complement_of_sylow_split [Finite G] {Q X P C : Subgroup G} (hQX : Q ≤ X)
    (hXQ : X ≤ normalizer (Q : Set G)) (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (hQ2 : IsPGroup 2 Q) (hP : IsSylowTwoOf P X) (hCP : C ≤ P) (hCQ : C ⊓ Q = ⊥)
    (hCsup : C ⊔ Q = P) :
    ∃ X₀ : Subgroup G, X₀ ≤ X ∧ Q ⊓ X₀ = ⊥ ∧ Q ⊔ X₀ = X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V : Subgroup X := Q.subgroupOf X with hV
  have hVn : V.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQX).mpr hXQ
  have : IsMulCommutative V := ⟨⟨fun a b => Subtype.ext (Subtype.ext
    (hQab _ (Subgroup.mem_subgroupOf.mp a.2) _ (Subgroup.mem_subgroupOf.mp b.2)))⟩⟩
  have hVp : IsPGroup 2 V := hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQX).symm
  have hP2 : IsPGroup 2 (P.subgroupOf X) :=
    hP.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hP.le).symm
  let P' : Sylow 2 X := hP2.toSylow hP.2.2
  have hP'eq : (P' : Subgroup X) = P.subgroupOf X := rfl
  have hsplit : ∃ K : Subgroup X, K ≤ (P' : Subgroup X) ∧ V ⊓ K = ⊥ ∧ V ⊔ K = (P' : Subgroup X) := by
    refine ⟨C.subgroupOf X, ?_, ?_, ?_⟩
    · rw [hP'eq]
      exact Subgroup.comap_mono hCP
    · rw [hV, show Q.subgroupOf X ⊓ C.subgroupOf X = (Q ⊓ C).subgroupOf X from
        (Subgroup.comap_inf Q C X.subtype).symm, inf_comm, hCQ, Subgroup.bot_subgroupOf]
    · rw [hP'eq, hV, ← hCsup, sup_comm C Q, Subgroup.subgroupOf_sup hQX (hCP.trans hP.le)]
  obtain ⟨K, hKinf, hKsup⟩ := (gaschutz hVp P').mpr hsplit
  have hVmap : V.map X.subtype = Q := Subgroup.map_subgroupOf_eq_of_le hQX
  refine ⟨K.map X.subtype, Subgroup.map_subtype_le K, ?_, ?_⟩
  · rw [← hVmap, ← Subgroup.map_inf_eq _ _ _ X.subtype_injective, hKinf, Subgroup.map_bot]
  · rw [← hVmap, ← Subgroup.map_sup, hKsup, Subgroup.map_top, Subgroup.range_subtype]

theorem blockQ_le_blockU_of_split [Finite G] {L Q X₀ : Subgroup G} (hL : IsShort2 L)
    (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hQ2 : ∀ q ∈ Q, q ^ 2 = 1)
    (hLQ : L ≤ normalizer (Q : Set G)) (hQc : ∀ q ∈ Q, ∀ u ∈ blockU L, u * q = q * u)
    (hQL : ∀ q ∈ Q, ∀ l ∈ L, q * l * q⁻¹ * l⁻¹ ∈ blockU L) (hLQ' : blockQ L ≤ Q)
    (hinf : Q ⊓ X₀ = ⊥) (hsup : Q ⊔ X₀ = L ⊔ Q) : blockQ L ≤ blockU L := by
  set U := blockU L with hU
  have hUQ : U ≤ Q := (C1.blockU_le_blockQ hL).trans hLQ'
  have hX₀X : X₀ ≤ L ⊔ Q := hsup ▸ le_sup_right
  have hX₁Q : L ⊔ Q ≤ normalizer (Q : Set G) := sup_le hLQ Subgroup.le_normalizer
  have hQN : Q ≤ normalizer (U : Set G) := le_normalizer_of_commute fun q hq u hu =>
    (hQc q hq u hu).symm
  have hX₁U : L ⊔ Q ≤ normalizer (U : Set G) := sup_le (C1.le_normalizer_blockU L) hQN
  have key : ∀ q ∈ Q, ∀ g ∈ L ⊔ Q, q * g * q⁻¹ * g⁻¹ ∈ U := by
    intro q hq g hg
    obtain ⟨l, hl, q', hq', rfl⟩ := mem_sup_of_le_normalizer hLQ hg
    have hcomm : q' * q⁻¹ = q⁻¹ * q' := hQab q' hq' q⁻¹ (inv_mem hq)
    have e : q * (l * q') * q⁻¹ * (l * q')⁻¹ = q * l * q⁻¹ * l⁻¹ := by
      calc q * (l * q') * q⁻¹ * (l * q')⁻¹ = q * l * (q' * q⁻¹) * q'⁻¹ * l⁻¹ := by group
        _ = q * l * (q⁻¹ * q') * q'⁻¹ * l⁻¹ := by rw [hcomm]
        _ = q * l * q⁻¹ * l⁻¹ := by group
    rw [e]
    exact hQL q hq l hl
  have hX₀U : X₀ ≤ normalizer (U : Set G) := fun g hg => hX₁U (hX₀X hg)
  have hN₁Q : ∀ q ∈ Q, ∀ n ∈ U ⊔ X₀, q * n * q⁻¹ ∈ U ⊔ X₀ := by
    intro q hq n hn
    rw [sup_comm] at hn
    obtain ⟨x₀, hx₀, u, hu, rfl⟩ := mem_sup_of_le_normalizer hX₀U hn
    have hc : q * x₀ * q⁻¹ * x₀⁻¹ ∈ U := key q hq x₀ (hX₀X hx₀)
    have hqu : q * u * q⁻¹ = u := by
      have := hQc q hq u hu
      calc q * u * q⁻¹ = q * (u * q⁻¹) := by group
        _ = u := by
            have h2 : q * u = u * q := this.symm
            calc q * (u * q⁻¹) = (q * u) * q⁻¹ := by group
              _ = (u * q) * q⁻¹ := by rw [h2]
              _ = u := by group
    have e : q * (x₀ * u) * q⁻¹ = (q * x₀ * q⁻¹ * x₀⁻¹) * x₀ * u := by
      calc q * (x₀ * u) * q⁻¹ = (q * x₀ * q⁻¹) * (q * u * q⁻¹) := by group
        _ = (q * x₀ * q⁻¹ * x₀⁻¹) * x₀ * u := by rw [hqu]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (mem_sup_left hc) (mem_sup_right hx₀))
      (mem_sup_left hu)
  have hQN₁ : Q ≤ normalizer ((U ⊔ X₀ : Subgroup G) : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨hN₁Q q hq n, fun h => ?_⟩
    have := hN₁Q q⁻¹ (inv_mem hq) _ h
    simpa [mul_assoc] using this
  have hX₀N₁ : X₀ ≤ normalizer ((U ⊔ X₀ : Subgroup G) : Set G) :=
    fun g hg => C1.mem_normalizer_sup (hX₀U hg) (Subgroup.le_normalizer hg)
  have hX₁N₁ : L ⊔ Q ≤ normalizer ((U ⊔ X₀ : Subgroup G) : Set G) := by
    rw [← hsup]
    exact sup_le hQN₁ hX₀N₁
  have hsq : ∀ g ∈ L ⊔ Q, g * g ∈ U ⊔ X₀ := by
    intro g hg
    have hg' : g ∈ X₀ ⊔ Q := by rw [sup_comm, hsup]; exact hg
    obtain ⟨x₀, hx₀, q, hq, rfl⟩ := mem_sup_of_le_normalizer (fun y hy => hX₁Q (hX₀X hy)) hg'
    have hc : q * x₀ * q⁻¹ * x₀⁻¹ ∈ U := key q hq x₀ (hX₀X hx₀)
    have hqq : q * q = 1 := by rw [← pow_two]; exact hQ2 q hq
    have e : x₀ * q * (x₀ * q) = x₀ * (q * x₀ * q⁻¹ * x₀⁻¹) * x₀ * (q * q) := by group
    rw [e, hqq, mul_one]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (mem_sup_right hx₀) (mem_sup_left hc))
      (mem_sup_right hx₀)
  have hLN₁ : L ≤ U ⊔ X₀ := by
    let N' : Subgroup L := (U ⊔ X₀).subgroupOf L
    have hN'n : N'.Normal := ⟨fun n hn g => by
      have hn' : (n : G) ∈ U ⊔ X₀ := hn
      have := (Subgroup.mem_normalizer_iff.mp (hX₁N₁ (Subgroup.mem_sup_left (T := Q) g.2)) _).mp hn'
      exact this⟩
    have hq : IsPGroup 2 (L ⧸ N') := by
      intro g
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
      refine ⟨1, ?_⟩
      rw [pow_one, pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      exact hsq l (Subgroup.mem_sup_left l.2)
    have htop := hL.1 N' hq
    intro l hl
    have : (⟨l, hl⟩ : L) ∈ N' := by rw [htop]; trivial
    exact this
  intro q₀ hq₀
  have hq₀N : q₀ ∈ U ⊔ X₀ := hLN₁ (C1.blockQ_le L hq₀)
  rw [sup_comm] at hq₀N
  obtain ⟨x₀, hx₀, u, hu, hxu⟩ := mem_sup_of_le_normalizer hX₀U hq₀N
  have hxQ : x₀ ∈ Q := by
    have : x₀ = q₀ * u⁻¹ := by rw [hxu]; group
    rw [this]
    exact Subgroup.mul_mem _ (hLQ' hq₀) (Subgroup.inv_mem _ (hUQ hu))
  have hx1 : x₀ = 1 := by
    have : x₀ ∈ Q ⊓ X₀ := ⟨hxQ, hx₀⟩
    rw [hinf] at this
    exact this
  rw [hxu, hx1, one_mul]
  exact hu

end CFSG.QuasithinUnique.C5
