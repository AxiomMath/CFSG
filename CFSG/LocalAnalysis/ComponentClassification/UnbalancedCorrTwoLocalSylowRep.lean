module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalNested

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_forall_conj_mem {K : Subgroup G} {g : G}
    (h : ∀ k ∈ K, g * k * g⁻¹ ∈ K) : g ∈ normalizer (K : Set G) := by
  have hle : conjugate K g⁻¹ ≤ K := fun x hx => by
    rw [UnbalancedLayer.mem_conjugate_iff, inv_inv] at hx
    have h1 := h _ hx
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h1
  have hcard : Nat.card K ≤ Nat.card (conjugate K g⁻¹) :=
    (card_map_of_injective (MulAut.conj g⁻¹⁻¹).injective).ge
  have heq := eq_of_le_of_card_ge hle hcard
  have h1 := UnbalancedLayer.mem_normalizer_of_conjugate_eq heq
  rwa [inv_mem_iff] at h1

omit [Finite G] in
theorem conjugate_normalizer (A : Subgroup G) (g : G) :
    conjugate (normalizer (A : Set G)) g = normalizer (conjugate A g : Set G) :=
  map_equiv_normalizer_eq A (MulAut.conj g⁻¹)

omit [Finite G] in
theorem conjugate_centralizer (A : Subgroup G) (g : G) :
    conjugate (centralizer (A : Set G)) g = centralizer (conjugate A g : Set G) := by
  ext x
  rw [UnbalancedLayer.mem_conjugate_iff, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h y hy
    rw [SetLike.mem_coe, UnbalancedLayer.mem_conjugate_iff] at hy
    have h1 := h _ hy
    calc y * x = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by rw [h1]
      _ = x * y := by group
  · intro h y hy
    have hy' : g⁻¹ * y * g ∈ conjugate A g := by
      rw [UnbalancedLayer.mem_conjugate_iff]
      rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
    have h1 := h _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * y := by group

omit [Finite G] in
theorem conjugate_sup (A B : Subgroup G) (g : G) :
    conjugate (A ⊔ B) g = conjugate A g ⊔ conjugate B g :=
  Subgroup.map_sup A B _

omit [Finite G] in
theorem conjugate_pPrimeCore (K : Subgroup G) (g : G) :
    conjugate ((pPrimeCore 2 ↥K).map K.subtype) g =
      (pPrimeCore 2 ↥(conjugate K g)).map (conjugate K g).subtype := by
  let φ := MulAut.conj g⁻¹
  let e : K ≃* K.map φ.toMonoidHom := K.equivMapOfInjective φ.toMonoidHom φ.injective
  have hcomm : φ.toMonoidHom.comp K.subtype = (K.map φ.toMonoidHom).subtype.comp e.toMonoidHom := by
    ext j
    rfl
  show ((pPrimeCore 2 ↥K).map K.subtype).map φ.toMonoidHom = _
  rw [map_map, hcomm, ← map_map, pPrimeCore_map_iso 2 e]
  rfl

omit [Finite G] in
theorem conjugate_closure_two_elements (X : Subgroup G) (g : G) :
    conjugate (Subgroup.closure {x : G | x ∈ X ∧ ∃ k : ℕ, orderOf x = 2 ^ k}) g =
      Subgroup.closure {x : G | x ∈ conjugate X g ∧ ∃ k : ℕ, orderOf x = 2 ^ k} := by
  show (Subgroup.closure _).map (MulAut.conj g⁻¹).toMonoidHom = _
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨hy, k, hk⟩, rfl⟩
    refine ⟨⟨y, hy, rfl⟩, k, ?_⟩
    rw [orderOf_injective _ (MulAut.conj g⁻¹).injective]
    exact hk
  · rintro ⟨⟨y, hy, rfl⟩, k, hk⟩
    refine ⟨y, ⟨hy, k, ?_⟩, rfl⟩
    rwa [orderOf_injective _ (MulAut.conj g⁻¹).injective] at hk

theorem exists_two_subgroup_of_not_sylow {L Q : Subgroup G} (hQL : Q ≤ L) (hQ : IsPGroup 2 Q)
    (hns : ¬ ∃ P₀ : Sylow 2 ↥L, (P₀ : Subgroup ↥L) = Q.subgroupOf L) :
    ∃ Q₁ : Subgroup G, Q ≤ Q₁ ∧ Q₁ ≤ L ∧ Q₁ ≤ normalizer (Q : Set G) ∧ IsPGroup 2 Q₁ ∧
      Nat.card Q < Nat.card Q₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ' : IsPGroup 2 (Q.subgroupOf L) := hQ.comap_of_injective L.subtype L.subtype_injective
  obtain ⟨Ps, hPs⟩ := hQ'.exists_le_sylow
  have hne : Q.subgroupOf L ≠ (Ps : Subgroup ↥L) := fun h => hns ⟨Ps, h.symm⟩
  have hlt : (Q.subgroupOf L).subgroupOf (Ps : Subgroup ↥L) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    exact hne (le_antisymm hPs (subgroupOf_eq_top.mp h))
  have : Group.IsNilpotent ↥(Ps : Subgroup ↥L) := Ps.isPGroup'.isNilpotent
  have h1 := Group.normalizerCondition_of_isNilpotent _ hlt
  set N := normalizer (((Q.subgroupOf L).subgroupOf (Ps : Subgroup ↥L) :
    Subgroup ↥(Ps : Subgroup ↥L)) : Set ↥(Ps : Subgroup ↥L)) with hNdef
  refine ⟨(N.map (Ps : Subgroup ↥L).subtype).map L.subtype, fun q hq => ?_, ?_, ?_, ?_, ?_⟩
  · have hqL : (⟨q, hQL hq⟩ : L) ∈ (Ps : Subgroup ↥L) := hPs hq
    exact ⟨⟨q, hQL hq⟩, ⟨⟨⟨q, hQL hq⟩, hqL⟩, le_normalizer (show (⟨⟨q, hQL hq⟩, hqL⟩ :
      ↥(Ps : Subgroup ↥L)) ∈ (Q.subgroupOf L).subgroupOf (Ps : Subgroup ↥L) from hq), rfl⟩, rfl⟩
  · exact map_subtype_le _
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have h2 := UnbalancedLayer.mem_normalizer_of_subgroupOf hPs hy
    exact UnbalancedLayer.mem_normalizer_of_subgroupOf hQL h2
  · exact (Ps.isPGroup'.to_subgroup N |>.map _).map _
  · have h2 := card_lt_of_lt h1
    rw [card_map_of_injective L.subtype_injective, card_map_of_injective (subtype_injective _)]
    calc Nat.card Q = Nat.card ↥((Q.subgroupOf L).subgroupOf (Ps : Subgroup ↥L)) := by
          rw [Nat.card_congr (subgroupOfEquivOfLe hPs).toEquiv,
            Nat.card_congr (subgroupOfEquivOfLe hQL).toEquiv]
      _ < Nat.card N := h2

theorem two_local_pair_full_sylow_representative_of_inputs
    (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hK : Assembly.KProper Blueprint.Catalog G) {a : G} (ha : orderOf a = 2) {J : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    {S P : Subgroup G} (hSX : S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G))
    (hSsyl : ∃ P₀ : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G)),
      (P₀ : Subgroup _) = S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G)))
    (hP : P = S ⊓ UnbalancedLayer.coreActionKernel J)
    (H R T X : Subgroup G → Subgroup G) (hH : ∀ B, H B = normalizer (B : Set G))
    (hR : ∀ B, R B = (pPrimeCore 2 ↥(H B)).map (H B).subtype)
    (hT : ∀ B, T B = (pLayer ↥(J ⊓ centralizer (B : Set G)) 2).map
      (J ⊓ centralizer (B : Set G)).subtype)
    (hX : ∀ B, X B = T B ⊔ R B)
    (hz : ∀ z : G, orderOf z = 2 → z ∈ P → z ∈ centralizer (S : Set G) →
      ∃ P₀ : Sylow 2 ↥(centralizer ({z} : Set G) ⊓ normalizer (X (zpowers z) : Set G)),
        (P₀ : Subgroup _) =
          S.subgroupOf (centralizer ({z} : Set G) ⊓ normalizer (X (zpowers z) : Set G))) :
    ∀ B : Subgroup G, B ≠ ⊥ → B ≤ P → ∃ g : G, conjugate B g ≤ P ∧
      conjugate (X B) g = X (conjugate B g) ∧
      Nat.card ↥(S ⊓ normalizer (B : Set G)) ≤
        Nat.card ↥(S ⊓ normalizer (conjugate B g : Set G)) ∧
      S ⊓ normalizer (conjugate B g : Set G) ≤
        normalizer (conjugate B g : Set G) ⊓ normalizer (X (conjugate B g) : Set G) ∧
      ∃ P₀ : Sylow 2 ↥(normalizer (conjugate B g : Set G) ⊓
          normalizer (X (conjugate B g) : Set G)),
        (P₀ : Subgroup _) = (S ⊓ normalizer (conjugate B g : Set G)).subgroupOf
          (normalizer (conjugate B g : Set G) ⊓ normalizer (X (conjugate B g) : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective
  have hS2 : IsPGroup 2 S := by
    obtain ⟨P₀, hP₀⟩ := hSsyl
    have h1 : IsPGroup 2 (S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G))) :=
      hP₀ ▸ P₀.isPGroup'
    exact h1.of_equiv (subgroupOfEquivOfLe hSX)
  obtain ⟨-, hBn, hCn⟩ := nested_two_local_full_core_residual_identities_of_inputs hS hU hheld
    hnonab hK ha hJa hJ hSX hSsyl hP H R T X hH hR hT hX
  have hPS : P ≤ S := hP.le.trans inf_le_left
  have hP2 : IsPGroup 2 P := hS2.to_le hPS
  have hSP : S ≤ normalizer (P : Set G) := by
    intro s hs
    rw [hP]
    exact UnbalancedLayer.normalizer_inf_mem (le_normalizer hs)
      (UnbalancedLayer.normalizer_le_normalizer_coreActionKernel J (hSX hs).2)
  have hRf : ∀ C : Subgroup G, R C = (pPrimeCore 2 ↥(normalizer (C : Set G))).map
      (normalizer (C : Set G)).subtype := fun C => by rw [hR, hH]
  have hRconj : ∀ (C : Subgroup G) (g : G), conjugate (R C) g = R (conjugate C g) := by
    intro C g
    rw [hRf, hRf, conjugate_pPrimeCore, conjugate_normalizer]
  have hact : ∀ C : Subgroup G, C ≠ ⊥ → C ≤ P → ∀ q ∈ S ⊓ normalizer (C : Set G),
      q ∈ normalizer (X C : Set G) ∧
      ((∀ x ∈ X C, x⁻¹ * q⁻¹ * x * q ∈ (pPrimeCore 2 ↥(X C)).map (X C).subtype) ↔
        q ∈ P ⊓ normalizer (C : Set G)) := by
    intro C hC1 hCP q hq
    obtain ⟨-, -, hQ⟩ := two_local_core_facts (X := X C) hS hnonab hK ha hJa hJ hSX hS2 hC1
      (hCP.trans hP.le) (hT C) ((hX C).trans (congrArg (T C ⊔ ·) (hRf C)))
    obtain ⟨h1, -, h2⟩ := hQ q hq
    refine ⟨h1, ?_⟩
    rw [hP]
    exact h2
  suffices key : ∀ n : ℕ, ∀ B : Subgroup G, B ≠ ⊥ → B ≤ P → Nat.card P - Nat.card B = n →
      ∃ g : G, conjugate B g ≤ P ∧ conjugate (X B) g = X (conjugate B g) ∧
        Nat.card ↥(S ⊓ normalizer (B : Set G)) ≤
          Nat.card ↥(S ⊓ normalizer (conjugate B g : Set G)) ∧
        S ⊓ normalizer (conjugate B g : Set G) ≤
          normalizer (conjugate B g : Set G) ⊓ normalizer (X (conjugate B g) : Set G) ∧
        ∃ P₀ : Sylow 2 ↥(normalizer (conjugate B g : Set G) ⊓
            normalizer (X (conjugate B g) : Set G)),
          (P₀ : Subgroup _) = (S ⊓ normalizer (conjugate B g : Set G)).subgroupOf
            (normalizer (conjugate B g : Set G) ⊓ normalizer (X (conjugate B g) : Set G)) by
    intro B hB1 hBP
    exact key _ B hB1 hBP rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B hB1 hBP hn
  set F : Set (Subgroup G) :=
    {C | C ≤ P ∧ ∃ g : G, conjugate B g = C ∧ conjugate (X B) g = X C} with hFdef
  have hBF : B ∈ F :=
    ⟨hBP, 1, UnbalancedLayer.conjugate_one B, UnbalancedLayer.conjugate_one (X B)⟩
  obtain ⟨C, ⟨hCP, g₀, hBC, hXC⟩, hCmax⟩ :=
    Set.exists_max_image F (fun C => Nat.card ↥(S ⊓ normalizer (C : Set G))) (Set.toFinite F)
      ⟨B, hBF⟩
  have hcardBC : Nat.card C = Nat.card B := by
    rw [← hBC]
    exact card_map_of_injective (MulAut.conj g₀⁻¹).injective
  have hC1 : C ≠ ⊥ := by
    intro h
    apply hB1
    rw [← Subgroup.card_eq_one, ← hcardBC, h, Subgroup.card_bot]
  refine ⟨g₀, ?_⟩
  rw [hBC]
  refine ⟨hCP, hXC, hCmax B hBF, ?_⟩
  set L := normalizer (C : Set G) ⊓ normalizer (X C : Set G) with hLdef
  set Q := S ⊓ normalizer (C : Set G) with hQdef
  have hQL : Q ≤ L := fun q hq => mem_inf.mpr ⟨(mem_inf.mp hq).2, (hact C hC1 hCP q hq).1⟩
  refine ⟨hQL, ?_⟩
  by_contra hns
  have hQ2 : IsPGroup 2 Q := hS2.to_le inf_le_left
  obtain ⟨Q1, hQQ1, hQ1L, hQ1N, hQ12, hcardQ⟩ := exists_two_subgroup_of_not_sylow hQL hQ2 hns
  have hQ1C : Q1 ≤ normalizer (C : Set G) := hQ1L.trans inf_le_left
  have hQ1X : Q1 ≤ normalizer (X C : Set G) := hQ1L.trans inf_le_right
  by_cases hCPeq : C = P
  ·
    have hQS : Q = S := inf_eq_left.mpr (hCPeq ▸ hSP)
    have hSQ1 : S ≤ Q1 := hQS ▸ hQQ1
    have hPQ1 : P ≤ Q1 := hPS.trans hSQ1
    have hP1 : P ≠ ⊥ := hCPeq ▸ hC1
    have : Group.IsNilpotent ↥Q1 := hQ12.isNilpotent
    have hPn : (P.subgroupOf Q1).Normal :=
      (normal_subgroupOf_iff_le_normalizer hPQ1).mpr (hCPeq ▸ hQ1C)
    have hP'1 : P.subgroupOf Q1 ≠ ⊥ := by
      intro h
      apply hP1
      have h1 := congrArg (Subgroup.map Q1.subtype) h
      rwa [map_subgroupOf_eq_of_le hPQ1, Subgroup.map_bot] at h1
    have hE := Group.IsNilpotent.inf_center_ne_bot_of_normal hP'1
    set E := P.subgroupOf Q1 ⊓ center ↥Q1 with hEdef
    have hE2 : IsPGroup 2 E := hQ12.to_subgroup E
    have hEnt : Nontrivial E := (nontrivial_iff_ne_bot E).mpr hE
    obtain ⟨k, hk0, hk⟩ := hE2.nontrivial_iff_card.mp hEnt
    have hdvd : 2 ∣ Nat.card E := by
      rw [hk]
      exact dvd_pow_self 2 (by omega)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    set z : G := ((x : Q1) : G) with hzdef
    have hz2 : orderOf z = 2 := by
      rw [hzdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hx
    have hzP : z ∈ P := (mem_inf.mp x.2).1
    have hzc : ∀ y ∈ Q1, y * z = z * y := by
      intro y hy
      have h1 := mem_center_iff.mp (mem_inf.mp x.2).2 ⟨y, hy⟩
      exact congrArg Subtype.val h1
    have hzS : z ∈ centralizer (S : Set G) :=
      mem_centralizer_iff.mpr fun s hs => hzc s (hSQ1 hs)
    have hQ1z : Q1 ≤ centralizer ({z} : Set G) := fun y hy =>
      mem_centralizer_singleton_iff.mpr (hzc y hy)
    have hz1 : zpowers z ≠ ⊥ := by
      rw [Ne, zpowers_eq_bot]
      intro h
      rw [h, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    have hPNz : P ≤ normalizer (zpowers z : Set G) := by
      rw [normalizer_zpowers_eq_centralizer hz2]
      exact hPQ1.trans hQ1z
    have hXz := hBn (zpowers z) P hz1 (zpowers_le.mpr hzP) le_rfl hPNz
    have hQ1Xz : Q1 ≤ normalizer (X (zpowers z) : Set G) := by
      intro q hq
      rw [hXz]
      have hqXP : q ∈ normalizer (X P : Set G) := hCPeq ▸ hQ1X hq
      refine mem_normalizer_sup ?_ ?_
      · rw [← map_primeResidual_eq_closure]
        have := CatalogueBPrimeJoin.primeResidual_characteristic 2 ↥(X P)
        exact UnbalancedGS.normalizer_le_normalizer_map_of_characteristic _ _ hqXP
      · have hqz : q ∈ normalizer (zpowers z : Set G) := by
          rw [normalizer_zpowers_eq_centralizer hz2]
          exact hQ1z hq
        apply UnbalancedLayer.mem_normalizer_of_conjugate_eq
        rw [hRconj, UnbalancedLayer.conjugate_eq_of_mem_normalizer hqz]
    obtain ⟨P₀, hP₀⟩ := hz z hz2 hzP hzS
    have hQ1Y : Q1 ≤ centralizer ({z} : Set G) ⊓ normalizer (X (zpowers z) : Set G) :=
      le_inf hQ1z hQ1Xz
    have hmax := P₀.is_maximal'
      (hQ12.comap_of_injective (Subgroup.subtype _) (Subgroup.subtype_injective _))
      (show (P₀ : Subgroup _) ≤ Q1.subgroupOf
          (centralizer ({z} : Set G) ⊓ normalizer (X (zpowers z) : Set G)) by
        rw [hP₀]
        exact fun y hy => hSQ1 hy)
    rw [hP₀] at hmax
    have hQ1S : Q1 = S := UGSChain.eq_of_subgroupOf_eq hQ1Y (hSQ1.trans hQ1Y) hmax
    rw [hQ1S, ← hQS] at hcardQ
    exact lt_irrefl _ hcardQ
  ·
    set Tn := P ⊓ normalizer (C : Set G) with hTndef
    have hTnP : Tn ≤ P := inf_le_left
    have hCTn' : C ≤ Tn := le_inf hCP le_normalizer
    have hTnN : Tn ≤ normalizer (C : Set G) := inf_le_right
    have hTn1 : Tn ≠ ⊥ := fun h => hC1 (le_bot_iff.mp (h ▸ hCTn'))
    have hCTn : Nat.card C < Nat.card Tn := by
      have : Group.IsNilpotent ↥P := hP2.isNilpotent
      have hlt : C.subgroupOf P < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro h
        exact hCPeq (le_antisymm hCP (subgroupOf_eq_top.mp h))
      have h1 := Group.normalizerCondition_of_isNilpotent (C.subgroupOf P) hlt
      rw [normalizer_subgroupOf_eq hCP, ← inf_subgroupOf_left (normalizer (C : Set G)) P] at h1
      have h2 := card_lt_of_lt h1
      rwa [Nat.card_congr (subgroupOfEquivOfLe hCP).toEquiv,
        Nat.card_congr (subgroupOfEquivOfLe hTnP).toEquiv] at h2
    have hQ1Tn : Q1 ≤ normalizer (Tn : Set G) := by
      intro g hg
      apply mem_normalizer_of_forall_conj_mem
      intro t ht
      have htQ : t ∈ Q := mem_inf.mpr ⟨hPS (mem_inf.mp ht).1, (mem_inf.mp ht).2⟩
      have hgtQ : g * t * g⁻¹ ∈ Q := (mem_normalizer_iff.mp (hQ1N hg) t).mp htQ
      have htriv := ((hact C hC1 hCP t htQ).2).mpr ht
      refine ((hact C hC1 hCP _ hgtQ).2).mp fun x hx => ?_
      have hgX := hQ1X hg
      have hy : g⁻¹ * x * g ∈ X C := by
        have h1 := (mem_normalizer_iff.mp (inv_mem hgX) x).mp hx
        rwa [inv_inv] at h1
      have h1 := htriv _ hy
      have hgO : g ∈ normalizer (((pPrimeCore 2 ↥(X C)).map (X C).subtype : Subgroup G) :
          Set G) := UnbalancedGS.normalizer_le_normalizer_map_of_characteristic _ _ hgX
      have h2 := (mem_normalizer_iff.mp hgO _).mp h1
      rwa [show g * ((g⁻¹ * x * g)⁻¹ * t⁻¹ * (g⁻¹ * x * g) * t) * g⁻¹ =
        x⁻¹ * (g * t * g⁻¹)⁻¹ * x * (g * t * g⁻¹) by group] at h2
    have hQ1XTn : Q1 ≤ normalizer (X Tn : Set G) := by
      intro g hg
      rw [hCn C hC1 hCP]
      have hgTn := hQ1Tn hg
      refine mem_normalizer_sup (UnbalancedLayer.normalizer_inf_mem (hQ1X hg) ?_) ?_
      · apply UnbalancedLayer.mem_normalizer_of_conjugate_eq
        rw [conjugate_centralizer, UnbalancedLayer.conjugate_eq_of_mem_normalizer hgTn]
      · apply UnbalancedLayer.mem_normalizer_of_conjugate_eq
        rw [hRconj, UnbalancedLayer.conjugate_eq_of_mem_normalizer hgTn]
    have hlt : Nat.card P - Nat.card Tn < n := by
      have := Subgroup.card_le_of_le hTnP
      omega
    obtain ⟨h, hT'P, hXT', -, -, hsylT'⟩ := ih _ hlt Tn hTn1 hTnP rfl
    set T' := conjugate Tn h with hT'def
    have hQ1hL : conjugate Q1 h ≤ normalizer (T' : Set G) ⊓ normalizer (X T' : Set G) := by
      refine le_inf ?_ ?_
      · rw [hT'def, ← conjugate_normalizer]
        exact map_mono hQ1Tn
      · rw [← hXT', ← conjugate_normalizer]
        exact map_mono hQ1XTn
    obtain ⟨c, hcL, hcQ⟩ := UnbalancedLayer.exists_conjugate_le_of_sylow hsylT' hQ1hL
      (hQ12.map _)
    set g := h * c with hgdef
    have hcT' : conjugate T' c = T' :=
      UnbalancedLayer.conjugate_eq_of_mem_normalizer (mem_inf.mp hcL).1
    have hcXT' : conjugate (X T') c = X T' :=
      UnbalancedLayer.conjugate_eq_of_mem_normalizer (mem_inf.mp hcL).2
    have hTng : conjugate Tn g = T' := by
      rw [hgdef, ← UnbalancedLayer.conjugate_conjugate, ← hT'def, hcT']
    have hXTng : conjugate (X Tn) g = X T' := by
      rw [hgdef, ← UnbalancedLayer.conjugate_conjugate, hXT', hcXT']
    set C' := conjugate C g with hC'def
    have hC'T' : C' ≤ T' := by
      rw [← hTng]
      exact map_mono hCTn'
    have hC'P : C' ≤ P := hC'T'.trans hT'P
    have hcardC' : Nat.card C' = Nat.card C := by
      show Nat.card ↥(conjugate C g) = Nat.card ↥C
      exact card_map_of_injective (MulAut.conj g⁻¹).injective
    have hC'1 : C' ≠ ⊥ := by
      intro h'
      apply hC1
      rw [← Subgroup.card_eq_one, ← hcardC', h', Subgroup.card_bot]
    have hT'N : T' ≤ normalizer (C' : Set G) := by
      rw [← hTng, hC'def, ← conjugate_normalizer]
      exact map_mono hTnN
    have hXC' : conjugate (X C) g = X C' := by
      rw [hBn C Tn hC1 hCTn' hTnP hTnN, hBn C' T' hC'1 hC'T' hT'P hT'N, conjugate_sup,
        conjugate_closure_two_elements, hXTng, hRconj]
    have hC'F : C' ∈ F := by
      refine ⟨hC'P, g₀ * g, ?_, ?_⟩
      · rw [← UnbalancedLayer.conjugate_conjugate, hBC]
      · rw [← UnbalancedLayer.conjugate_conjugate, hXC, hXC']
    have hQ1g : conjugate Q1 g ≤ S ⊓ normalizer (C' : Set G) := by
      refine le_inf ?_ ?_
      · have h1 : conjugate Q1 g ≤ S ⊓ normalizer (T' : Set G) := by
          rw [hgdef, ← UnbalancedLayer.conjugate_conjugate]
          exact hcQ
        exact h1.trans inf_le_left
      · rw [hC'def, ← conjugate_normalizer]
        exact map_mono hQ1C
    have h1 := Subgroup.card_le_of_le hQ1g
    rw [show Nat.card ↥(conjugate Q1 g) = Nat.card Q1 from
      card_map_of_injective (MulAut.conj g⁻¹).injective] at h1
    have h2 := hCmax C' hC'F
    omega

end CFSG.ComponentClassification.UnbalancedCorr
