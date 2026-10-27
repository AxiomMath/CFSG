module

public import CFSG.ClassicalInvolution.Asc77.AscT3TypedExactA

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7G23

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed

variable {G : Type} [Group G]

@[expose] def q8Fam (G : Type) [Group G] : Set (Subgroup G) :=
  {T | Nonempty (↥T ≃* QuaternionGroup 2)}

structure G23Data (G : Type) [Group G] where
  t : G
  X : Subgroup G
  K₁ : Subgroup G
  K₂ : Subgroup G
  g : G
  cent : Subgroup.centralizer {t} = X
  census : ∀ T ∈ q8Fam G, ∃ a : G, conjSub a K₁ = T ∨ conjSub a K₂ = T
  censusX : ∀ T ∈ q8Fam G, T ≤ X → T = K₁ ∨ T = K₂
  mem₁ : K₁ ∈ q8Fam G
  mem₂ : K₂ ∈ q8Fam G
  inv₁ : IsUniqueInvolution K₁ t
  inv₂ : IsUniqueInvolution K₂ t
  nor₁ : X ≤ Subgroup.normalizer (K₁ : Set G)
  ne : K₁ ≠ K₂
  edgeIn : ∃ c ∈ K₂, orderOf c = 4 ∧ g * c * g⁻¹ ∈ X
  edgeOut : ∃ k ∈ K₂, g * k * g⁻¹ ∉ X
  gen : ∀ N : Subgroup G, X ≤ N → g ∈ N → N = ⊤

theorem card_of_mem_q8Fam {T : Subgroup G} (hT : T ∈ q8Fam G) : Nat.card T = 8 := by
  obtain ⟨e⟩ := hT
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem isPGroup_of_mem_q8Fam {T : Subgroup G} (hT : T ∈ q8Fam G) : IsPGroup 2 T :=
  IsPGroup.of_card (n := 3) (by rw [card_of_mem_q8Fam hT]; norm_num)

theorem q8Fam_conj : ConjInvariant (q8Fam G) := by
  intro n K hK
  obtain ⟨e⟩ := hK
  exact ⟨(K.equivMapOfInjective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective).symm.trans e⟩

theorem eq_of_mem_RSet [Finite G] {R J : Subgroup G} (hR : R ∈ RSet (q8Fam G))
    (hJ : J ∈ q8Fam G) (hRJ : R ≤ J) : R = J := by
  obtain ⟨M, hM, hRM, -, hmax⟩ := mem_RSet_iff.mp hR
  have hMR : M = R := hmax M le_rfl (isPGroup_of_mem_q8Fam hM) hRM
  have hc : Nat.card R = 8 := by rw [← hMR]; exact card_of_mem_q8Fam hM
  exact Subgroup.eq_of_le_of_card_ge hRJ (by rw [hc, card_of_mem_q8Fam hJ])

theorem mem_RSet_self {J : Subgroup G} (hJ : J ∈ q8Fam G) : J ∈ RSet (q8Fam G) :=
  mem_RSet_iff.mpr ⟨J, hJ, le_rfl, isPGroup_of_mem_q8Fam hJ,
    fun _ hR'J _ hle => le_antisymm hR'J hle⟩

theorem conjSub_eq_of_mem_normalizer {n : G} {K : Subgroup G}
    (hn : n ∈ Subgroup.normalizer (K : Set G)) : conjSub n K = K := by
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro h
    have := (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * x * n)).mp h
    simpa [mul_assoc] using this
  · intro h
    refine (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * x * n)).mpr ?_
    simpa [mul_assoc] using h

theorem normalizer_le_centralizer {K : Subgroup G} {z : G} (hz : IsUniqueInvolution K z) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.centralizer {z} := by
  intro n hn
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hmem : n * z * n⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hn z).mp hz.mem
  have hsq : n * z * n⁻¹ * (n * z * n⁻¹) = 1 := by
    calc n * z * n⁻¹ * (n * z * n⁻¹) = n * (z * z) * n⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  rcases hz.unique _ hmem hsq with h | h
  · exfalso
    apply hz.ne_one
    have := congrArg (fun x => n⁻¹ * x * n) h
    simpa [mul_assoc] using this
  · calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [h]

theorem le_centralizer {K : Subgroup G} {z : G} (hz : IsUniqueInvolution K z) :
    K ≤ Subgroup.centralizer {z} :=
  fun _ hk => normalizer_le_centralizer hz (Subgroup.le_normalizer hk)

namespace G23Data

variable (D : G23Data G)

theorem le_X₁ : D.K₁ ≤ D.X := D.cent ▸ le_centralizer D.inv₁

theorem centralizer_conj (a : G) :
    Subgroup.centralizer {a * D.t * a⁻¹} = conjSub a D.X := by
  ext x
  rw [mem_conjSub_iff, ← D.cent, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc a⁻¹ * x * a * D.t = a⁻¹ * (x * (a * D.t * a⁻¹)) * a := by group
      _ = a⁻¹ * ((a * D.t * a⁻¹) * x) * a := by rw [h]
      _ = D.t * (a⁻¹ * x * a) := by group
  · intro h
    calc x * (a * D.t * a⁻¹) = a * (a⁻¹ * x * a * D.t) * a⁻¹ := by group
      _ = a * (D.t * (a⁻¹ * x * a)) * a⁻¹ := by rw [h]
      _ = a * D.t * a⁻¹ * x := by group

theorem censusX_conj {a : G} {T : Subgroup G} (hT : T ∈ q8Fam G) (hTX : T ≤ conjSub a D.X) :
    T = conjSub a D.K₁ ∨ T = conjSub a D.K₂ := by
  have h1 : conjSub a⁻¹ T ∈ q8Fam G := q8Fam_conj _ _ hT
  have h2 : conjSub a⁻¹ T ≤ D.X := by
    rw [conjSub_le_iff, inv_inv]; exact hTX
  rcases D.censusX _ h1 h2 with h | h
  · left; rw [← h, conjSub_conjSub_inv]
  · right; rw [← h, conjSub_conjSub_inv]

include D in
theorem omegaOfSet_twinSet_eq_empty [Finite G] {K : Subgroup G} (hK : K ∈ q8Fam G) :
    omegaOfSet (q8Fam G) (twinSet (q8Fam G) K) = ∅ := by
  obtain ⟨a, ha⟩ := D.census K hK
  obtain ⟨K', hK'K, hK'tw⟩ : ∃ K', (K = conjSub a D.K₁ ∧ K' = conjSub a D.K₂ ∨
      K = conjSub a D.K₂ ∧ K' = conjSub a D.K₁) ∧ K' ∈ twinSet (q8Fam G) K := by
    rcases ha with ha | ha
    · exact ⟨conjSub a D.K₂, Or.inl ⟨ha.symm, rfl⟩, q8Fam_conj _ _ D.mem₂, a * D.t * a⁻¹,
        ha ▸ D.inv₁.conj a, D.inv₂.conj a⟩
    · exact ⟨conjSub a D.K₁, Or.inr ⟨ha.symm, rfl⟩, q8Fam_conj _ _ D.mem₁, a * D.t * a⁻¹,
        ha ▸ D.inv₂.conj a, D.inv₁.conj a⟩
  have hzK : IsUniqueInvolution K (a * D.t * a⁻¹) := by
    rcases hK'K with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]; exact D.inv₁.conj a
    · rw [h1]; exact D.inv₂.conj a
  rw [Set.eq_empty_iff_forall_notMem]
  rintro J ⟨hJ, hall⟩
  obtain ⟨-, hJK, R, hR, hRJ, hRN⟩ := hall K ⟨hK, a * D.t * a⁻¹, hzK, hzK⟩
  have hRJ' := eq_of_mem_RSet hR hJ hRJ
  have hJX : J ≤ conjSub a D.X := by
    rw [← D.centralizer_conj a, ← hRJ']
    exact hRN.trans (normalizer_le_centralizer hzK)
  obtain ⟨-, hJK', -⟩ := hall K' hK'tw
  rcases D.censusX_conj hJ hJX with h | h <;> rcases hK'K with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hJK (h.trans h1.symm)
  · exact hJK' (h.trans h2.symm)
  · exact hJK' (h.trans h2.symm)
  · exact hJK (h.trans h1.symm)

include D in
theorem vStar_eq [Finite G] {K : Subgroup G} (hK : K ∈ q8Fam G) :
    vStar (q8Fam G) K = q8Fam G := by
  ext J
  refine ⟨fun h => h.1, fun hJ => ⟨hJ, ?_⟩⟩
  rw [D.omegaOfSet_twinSet_eq_empty hK, D.omegaOfSet_twinSet_eq_empty hJ]

theorem mem_aSet [Finite G] : conjSub D.g D.K₂ ∈ aSet (q8Fam G) D.K₁ := by
  obtain ⟨c, hc, hc4, hcX⟩ := D.edgeIn
  obtain ⟨k, hk, hkX⟩ := D.edgeOut
  have hJ : conjSub D.g D.K₂ ∈ q8Fam G := q8Fam_conj _ _ D.mem₂
  have hkJ : D.g * k * D.g⁻¹ ∈ conjSub D.g D.K₂ := conj_mem_conjSub hk
  have hJne : conjSub D.g D.K₂ ≠ D.K₁ := fun e => hkX (D.le_X₁ (e ▸ hkJ))
  have hle : Subgroup.zpowers (D.g * c * D.g⁻¹) ≤ conjSub D.g D.K₂ :=
    (Subgroup.zpowers_le).mpr (conj_mem_conjSub hc)
  have hidx : (Subgroup.zpowers (D.g * c * D.g⁻¹)).relIndex (conjSub D.g D.K₂) = 2 := by
    have h4 : Nat.card (Subgroup.zpowers (D.g * c * D.g⁻¹)) = 4 := by
      rw [Nat.card_zpowers, ← hc4]
      have := orderOf_injective (MulAut.conj D.g).toMonoidHom (MulAut.conj D.g).injective c
      simpa using this
    have h := Subgroup.card_mul_index ((Subgroup.zpowers (D.g * c * D.g⁻¹)).subgroupOf
      (conjSub D.g D.K₂))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, h4,
      card_of_mem_q8Fam hJ] at h
    show ((Subgroup.zpowers (D.g * c * D.g⁻¹)).subgroupOf (conjSub D.g D.K₂)).index = 2
    omega
  refine ⟨D.t, D.g * D.t * D.g⁻¹,
    { star := ⟨hJ, hJne, Subgroup.zpowers (D.g * c * D.g⁻¹),
        ⟨conjSub D.g D.K₂, mem_RSet_self hJ, hle, inferInstance, hidx⟩, hle,
        (Subgroup.zpowers_le).mpr (D.nor₁ hcX)⟩
      not_nbr := ?_
      hzK := D.inv₁
      hzJ := D.inv₂.conj D.g
      no_conj := ?_ }⟩
  ·
    rintro ⟨-, -, R, hR, hRJ, hRN⟩
    rw [eq_of_mem_RSet hR hJ hRJ] at hRN
    exact hkX (D.cent ▸ normalizer_le_centralizer D.inv₁ (hRN hkJ))
  ·
    intro x _ hx
    have hx' : conjSub (D.g⁻¹ * x) D.K₁ = D.K₂ := by
      rw [conjSub_mul, hx, conjSub_inv_conjSub]
    have ht : (D.g⁻¹ * x) * D.t * (D.g⁻¹ * x)⁻¹ = D.t :=
      (D.inv₁.conj (D.g⁻¹ * x)).eq (by rw [hx']; exact D.inv₂)
    have hxX : D.g⁻¹ * x ∈ D.X := by
      rw [← D.cent, Subgroup.mem_centralizer_singleton_iff]
      calc D.g⁻¹ * x * D.t = (D.g⁻¹ * x) * D.t * (D.g⁻¹ * x)⁻¹ * (D.g⁻¹ * x) := by group
        _ = D.t * (D.g⁻¹ * x) := by rw [ht]
    exact D.ne ((conjSub_eq_of_mem_normalizer (D.nor₁ hxX)).symm.trans hx')

theorem conj_mem_aStar [Finite G] {a b : G}
    (ha : conjSub a D.K₁ ∈ aStar (q8Fam G) D.K₁) (hb : conjSub b D.K₁ ∈ aStar (q8Fam G) D.K₁) :
    conjSub (a * b) D.K₁ ∈ aStar (q8Fam G) D.K₁ := by
  have h := aStar_conj (q8Fam_conj (G := G)) hb a
  rw [← conjSub_mul] at h
  exact Relation.ReflTransGen.trans ha h

@[expose] def compStab [Finite G] : Subgroup G where
  carrier := {a | conjSub a D.K₁ ∈ aStar (q8Fam G) D.K₁}
  one_mem' := by
    show conjSub 1 D.K₁ ∈ aStar (q8Fam G) D.K₁
    rw [conjSub_one]; exact Relation.ReflTransGen.refl
  mul_mem' := fun ha hb => D.conj_mem_aStar ha hb
  inv_mem' := by
    intro a ha
    have h := (mem_aStar_symm D.mem₁ ha).2
    have h2 := aStar_conj (q8Fam_conj (G := G)) h a⁻¹
    rwa [conjSub_inv_conjSub] at h2

theorem twin_adj (a : G) :
    aGraphAdj (q8Fam G) (conjSub a D.K₁) (conjSub a D.K₂) :=
  ⟨q8Fam_conj _ _ D.mem₂, Or.inr (Or.inr ⟨⟨q8Fam_conj _ _ D.mem₂, a * D.t * a⁻¹,
    D.inv₁.conj a, D.inv₂.conj a⟩, fun e => D.ne ((conjSub_inj a).mp e).symm⟩)⟩

theorem compStab_eq_top [Finite G] : D.compStab = ⊤ := by
  refine D.gen _ (fun x hx => ?_) ?_
  · show conjSub x D.K₁ ∈ aStar (q8Fam G) D.K₁
    rw [conjSub_eq_of_mem_normalizer (D.nor₁ hx)]
    exact Relation.ReflTransGen.refl
  · show conjSub D.g D.K₁ ∈ aStar (q8Fam G) D.K₁
    have h1 : aGraphAdj (q8Fam G) D.K₁ (conjSub D.g D.K₂) :=
      ⟨q8Fam_conj _ _ D.mem₂, Or.inl D.mem_aSet⟩
    have h2 : aGraphAdj (q8Fam G) (conjSub D.g D.K₂) (conjSub D.g D.K₁) :=
      aGraphAdj_symm (q8Fam_conj _ _ D.mem₁) (D.twin_adj D.g)
    exact (Relation.ReflTransGen.single h1).tail h2

include D in
theorem aStar_eq [Finite G] {K : Subgroup G} (hK : K ∈ q8Fam G) :
    aStar (q8Fam G) K = q8Fam G := by
  have hall : ∀ T ∈ q8Fam G, T ∈ aStar (q8Fam G) D.K₁ := by
    intro T hT
    have h1 : ∀ a : G, conjSub a D.K₁ ∈ aStar (q8Fam G) D.K₁ := fun a => by
      have : a ∈ D.compStab := by rw [D.compStab_eq_top]; trivial
      exact this
    obtain ⟨a, ha | ha⟩ := D.census T hT
    · exact ha ▸ h1 a
    · exact ha ▸ (h1 a).tail (D.twin_adj a)
  ext J
  refine ⟨fun h => (mem_aStar_symm hK h).1, fun hJ => ?_⟩
  exact Relation.ReflTransGen.trans (mem_aStar_symm D.mem₁ (hall K hK)).2 (hall J hJ)

end G23Data

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7G23

