module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSylBasic

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag

section TypeFree

variable {G : Type} [Group G]

theorem relIndex_sup_zpowers_eq_two_of_mul_self_mem {R : Subgroup G} {u : G} (huR : u ∉ R)
    (huN : u ∈ normalizer (R : Set G)) (huu : u * u ∈ R) :
    R.relIndex (R ⊔ zpowers u) = 2 := by
  rw [relIndex_eq_two_iff]
  refine ⟨u, mem_sup_right (mem_zpowers u), fun b hb => ?_⟩
  rcases mem_or_mul_mem_of_mem_sup_zpowers_of_mul_self_mem huN huu hb with h | h
  · refine Or.inr ⟨h, fun h' => huR ?_⟩
    have h1 : b⁻¹ * (b * u) = u := by group
    rw [← h1]
    exact mul_mem (inv_mem h) h'
  · refine Or.inl ⟨h, fun h' => huR ?_⟩
    have h1 : u = b⁻¹ * (b * u) := by group
    rw [h1]
    exact mul_mem (inv_mem h') h

theorem card_sup_zpowers_eq_two_mul_of_mul_self_mem {R : Subgroup G} {u : G} (huR : u ∉ R)
    (huN : u ∈ normalizer (R : Set G)) (huu : u * u ∈ R) :
    Nat.card (R ⊔ zpowers u : Subgroup G) = 2 * Nat.card R := by
  have h := Subgroup.relIndex_mul_card (H := R) (K := R ⊔ zpowers u)
  rw [relIndex_sup_zpowers_eq_two_of_mul_self_mem huR huN huu, inf_of_le_left le_sup_left] at h
  exact h.symm

theorem mul_self_mem_of_mem_sup_zpowers {S₀ : Subgroup G} {t : G} (ht2 : t * t = 1)
    (htN : t ∈ normalizer (S₀ : Set G)) {a : G} (ha : a ∈ S₀ ⊔ zpowers t) : a * a ∈ S₀ := by
  rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers ht2 htN ha with h | h
  · exact mul_mem h h
  · have h1 : a * a = (a * t) * (t⁻¹ * (a * t) * t) * (t * t)⁻¹ := by group
    rw [h1, ht2, inv_one, mul_one]
    exact mul_mem h (inv_mul_mul_mem_of_mem_normalizer htN h)

theorem exists_conj_mem_of_maximal [Finite G] {C R : Subgroup G} (hR : IsPGroup 2 R)
    (hRC : R ≤ C) (hmax : ∀ P : Subgroup G, IsPGroup 2 P → R ≤ P → P ≤ C → P = R) {y : G}
    (hyC : y ∈ C) (hy : IsPGroup 2 (zpowers y)) : ∃ c ∈ C, c⁻¹ * y * c ∈ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR' : IsPGroup 2 (R.subgroupOf C) := hR.comap_of_injective _ C.subtype_injective
  let P : Sylow 2 C :=
    { toSubgroup := R.subgroupOf C
      isPGroup' := hR'
      is_maximal' := by
        intro Q hQ hle
        have hQ' : IsPGroup 2 (Q.map C.subtype) := hQ.map _
        have hRQ : R ≤ Q.map C.subtype := by
          intro r hr
          exact ⟨⟨r, hRC hr⟩, hle (mem_subgroupOf.2 hr), rfl⟩
        have heq := hmax _ hQ' hRQ (map_subtype_le _)
        ext x
        constructor
        · intro hx
          have h1 : (x : G) ∈ Q.map C.subtype := ⟨x, hx, rfl⟩
          rw [heq] at h1
          exact mem_subgroupOf.2 h1
        · intro hx
          exact hle hx }
  have hY : IsPGroup 2 ((zpowers y).subgroupOf C) := hy.comap_of_injective _ C.subtype_injective
  obtain ⟨Q, hYQ⟩ := hY.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C P Q
  have hyQ : (⟨y, hyC⟩ : C) ∈ (Q : Subgroup C) := hYQ (mem_subgroupOf.2 (mem_zpowers y))
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyQ
  refine ⟨g, g.2, ?_⟩
  have h1 : ((MulAut.conj g)⁻¹ • (⟨y, hyC⟩ : C) : C) ∈ R.subgroupOf C := hyQ
  rw [mem_subgroupOf] at h1
  have h2 : (((MulAut.conj g)⁻¹ • (⟨y, hyC⟩ : C) : C) : G) = (g : G)⁻¹ * y * g := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
    simp
  rw [← h2]
  exact h1

theorem mem_normalizer_inf_of_mem_normalizer {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact mem_inf.2 ⟨(mem_normalizer_iff.1 hA x).1 (mem_inf.1 hx).1,
      (mem_normalizer_iff.1 hB x).1 (mem_inf.1 hx).2⟩
  · intro hx
    exact mem_inf.2 ⟨(mem_normalizer_iff.1 hA x).2 (mem_inf.1 hx).1,
      (mem_normalizer_iff.1 hB x).2 (mem_inf.1 hx).2⟩

@[expose] def IsLFiveFieldSylow (L : Subgroup G) (t : G) (Nt S₀ : Subgroup G) : Prop :=
  IsPGroup 2 S₀ ∧ S₀ ≤ Nt ∧ ¬ 2 ∣ S₀.relIndex Nt ∧ t ∈ normalizer (S₀ : Set G) ∧
    ∃ Q₀ : Subgroup G, Q₀ ≤ L ∧ Nat.card Q₀ = 2 ^ 10 ∧ Q₀ ≤ S₀

end TypeFree

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_lFiveFieldSylow
    (hset : SeitzSetting G L)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (c : Fin 5) {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G))
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    {Kc : Subgroup (seitzHat W₁)} (hfield : IsFieldTypeComponentAtNOne e t c W₁ htN Kc) :
    ∃ S₀ : Subgroup G, IsLFiveFieldSylow L t (seitzTilde W₁ Kc) S₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hW₁Nt, htNt, htNNt, -⟩ :=
    seitzTilde_fusion_facts hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield
  set Nt := seitzTilde W₁ Kc with hNtdef
  set M := Nt ⊔ zpowers t with hMdef
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨Q₀, hQ₀le, hQ₀c⟩ := exists_two_subgroup_le_pointRadical_sup_levi hK e c
  have hQ₀L : Q₀ ≤ L := hQ₀le.trans (sup_le (modelToG_le e _) (modelToG_le e _))
  have hV₁Nt : modelToG e (pointRadical (K := K) c) ≤ Nt := by
    rw [← hW₁t]
    exact inf_le_left.trans hW₁Nt
  have hQ₀Nt : Q₀ ≤ Nt :=
    hQ₀le.trans (sup_le hV₁Nt (blockSL_le_seitzTilde hK e htC c hW₁c htN hLN hfield))
  have htQ₀ : t ∈ normalizer (Q₀ : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.2 fun q hq => mem_centralizer_iff.1 htC q (hQ₀L hq))
  have hP₀ : IsPGroup 2 (Q₀ ⊔ zpowers t : Subgroup G) :=
    isPGroup_sup_zpowers_of_mem_normalizer (IsPGroup.of_card hQ₀c) htQ₀
      (isPGroup_zpowers_two_of_mul_self ht2)
  have hP₀M : Q₀ ⊔ zpowers t ≤ M := sup_le (hQ₀Nt.trans le_sup_left) le_sup_right
  have hP' : IsPGroup 2 ((Q₀ ⊔ zpowers t).subgroupOf M) :=
    hP₀.comap_of_injective _ M.subtype_injective
  obtain ⟨T, hT⟩ := hP'.exists_le_sylow
  set S₁ : Subgroup G := (T : Subgroup M).map M.subtype with hS₁def
  have hS₁M : S₁ ≤ M := map_subtype_le _
  have hPS₁ : Q₀ ⊔ zpowers t ≤ S₁ := fun x hx =>
    ⟨⟨x, hP₀M hx⟩, hT (mem_subgroupOf.2 hx), rfl⟩
  have htS₁ : t ∈ S₁ := hPS₁ (mem_sup_right (mem_zpowers t))
  have hS₁idx : ¬ 2 ∣ S₁.relIndex M := by
    rw [Subgroup.relIndex, hS₁def, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact T.not_dvd_index
  set S₀ : Subgroup G := S₁ ⊓ Nt with hS₀def
  have htS₀ : t ∈ normalizer (S₀ : Set G) :=
    mem_normalizer_inf_of_mem_normalizer (le_normalizer htS₁) htNNt
  have htS₀' : t ∉ S₀ := fun h => htNt (mem_inf.1 h).2
  have hS₁eq : S₁ = S₀ ⊔ zpowers t := by
    refine le_antisymm (fun h hh => ?_) (sup_le inf_le_left ((zpowers_le).2 htS₁))
    rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers ht2 htNNt (hS₁M hh) with h1 | h1
    · exact mem_sup_left (mem_inf.2 ⟨hh, h1⟩)
    · have h2 : h = h * t * t := by rw [mul_assoc, ht2, mul_one]
      rw [h2]
      exact mul_mem (mem_sup_left (mem_inf.2 ⟨mul_mem hh htS₁, h1⟩))
        (mem_sup_right (mem_zpowers t))
  have hS₁c : Nat.card S₁ = 2 * Nat.card S₀ := by
    rw [hS₁eq]
    exact card_sup_zpowers_eq_two_mul htS₀' htS₀ ht2
  have hMc : Nat.card M = 2 * Nat.card Nt := card_sup_zpowers_eq_two_mul htNt htNNt ht2
  have h₀ : S₀.relIndex Nt * Nat.card S₀ = Nat.card Nt := by
    have h := Subgroup.relIndex_mul_card (H := S₀) (K := Nt)
    rwa [inf_of_le_left inf_le_right] at h
  have h₁ : S₁.relIndex M * Nat.card S₁ = Nat.card M := by
    have h := Subgroup.relIndex_mul_card (H := S₁) (K := M)
    rwa [inf_of_le_left hS₁M] at h
  have hrel : S₁.relIndex M = S₀.relIndex Nt := by
    rw [hS₁c, hMc, ← h₀] at h₁
    have hpos : 0 < Nat.card S₀ := Nat.card_pos
    have h3 : S₁.relIndex M * (2 * Nat.card S₀) = S₀.relIndex Nt * (2 * Nat.card S₀) := by
      rw [h₁]
      ring
    exact Nat.eq_of_mul_eq_mul_right (by omega) h3
  refine ⟨S₀, (T.isPGroup'.map M.subtype).to_le inf_le_left, inf_le_right, hrel ▸ hS₁idx,
    htS₀, Q₀, hQ₀L, hQ₀c, le_inf (le_sup_left.trans hPS₁) hQ₀Nt⟩

theorem sup_inf_centralizer_le_sup (hset : SeitzSetting G L) {K : Type} [Field K] [CharP K 2]
    (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (c : Fin 5) {W₁ : Subgroup G}
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G)) (Kc : Subgroup (seitzHat W₁)) :
    (seitzTilde W₁ Kc ⊔ zpowers t) ⊓ centralizer ({t} : Set G) ≤ L ⊔ zpowers t := by
  rintro y ⟨hyM, hyC⟩
  have hyN : y ∈ normalizer (W₁ : Set G) :=
    sup_le (seitzTilde_le_normalizer W₁ Kc) ((zpowers_le).2 htN) hyM
  have hyV : y ∈ normalizer (modelToG e (pointRadical (K := K) c) : Set G) := by
    rw [← hW₁t]
    exact mem_normalizer_inf_centralizer_singleton_of_mem hyN hyC
  have h1 := lFiveNormalizerPointRadicalInput G L hset K hK e t ht hKt c (mem_inf.2 ⟨hyV, hyC⟩)
  exact (sup_le (sup_le ((modelToG_le e _).trans le_sup_left)
    ((modelToG_le e _).trans le_sup_left)) le_sup_right) h1

theorem inf_eq_of_le_of_card_eq {K : Type} [Field K] (hK : Nat.card K = 2)
    (e : L ≃* projectiveSL 5 K) {Q₀ S : Subgroup G} (hQL : Q₀ ≤ L) (hQc : Nat.card Q₀ = 2 ^ 10)
    (hS : IsPGroup 2 S) (hQS : Q₀ ≤ S) : S ⊓ L = Q₀ := by
  have hL : Nat.card L = 2 ^ 10 * 9765 := by
    rw [Nat.card_congr e.toEquiv, card_projectiveSL_five_of_card_two hK]
    norm_num
  have h1 : Nat.card (S ⊓ L : Subgroup G) ≤ 2 ^ 10 :=
    card_le_two_pow_of_isPGroup_of_dvd (hS.to_le inf_le_left) (by decide)
      (hL ▸ Subgroup.card_dvd_of_le inf_le_right)
  exact (Subgroup.eq_of_le_of_card_ge (le_inf hQS hQL) (by rw [hQc]; exact h1)).symm

theorem exists_graph_element
    (hset : SeitzSetting G L)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hgraph : ∃ g ∈ centralizer ({t} : Set G), ∀ l ∈ L, ∃ x ∈ L, g * x * g⁻¹ ≠ l * x * l⁻¹)
    (c : Fin 5) {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G))
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    {Kc : Subgroup (seitzHat W₁)} (hfield : IsFieldTypeComponentAtNOne e t c W₁ htN Kc)
    {S₀ : Subgroup G} (hS₀p : IsPGroup 2 S₀) (hS₀N : S₀ ≤ seitzTilde W₁ Kc)
    (htS₀ : t ∈ normalizer (S₀ : Set G))
    (hThom : ∀ x ∈ S₀, x * t * (x * t) = 1 → ∃ z ∈ S₀, x * t = z * t * z⁻¹) :
    ∃ d : G, d ∈ centralizer ({t} : Set G) ∧
      d ∈ normalizer ((S₀ ⊔ zpowers t : Subgroup G) : Set G) ∧ d ∉ S₀ ⊔ zpowers t ∧
      d * d ∈ S₀ ⊔ zpowers t ∧ IsPGroup 2 (zpowers d) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  set S₁ : Subgroup G := S₀ ⊔ zpowers t with hS₁def
  have hS₁p : IsPGroup 2 S₁ :=
    isPGroup_sup_zpowers_of_mem_normalizer hS₀p htS₀ (isPGroup_zpowers_two_of_mul_self ht2)
  have htS₁ : t ∈ S₁ := mem_sup_right (mem_zpowers t)
  have h2 := two_dvd_index_of_le_seitzTilde_sup_of_graph hset hK e ht hKt hgraph c hW₁c hW₁2
    hW₁t htN hLN hfield hS₁p (sup_le_sup_right hS₀N _)
  obtain ⟨T, hST⟩ := hS₁p.exists_le_sylow
  have hne : S₁ ≠ (T : Subgroup G) := fun h => T.not_dvd_index (h ▸ h2)
  obtain ⟨d₀, hd₀T, hd₀S, hd₀N, hd₀d⟩ :=
    exists_mem_normalizer_notMem_mul_self_mem T.isPGroup' (lt_of_le_of_ne hST hne)
  set t' := d₀ * t * d₀⁻¹ with ht'
  have ht'S₁ : t' ∈ S₁ := (mem_normalizer_iff.1 hd₀N t).1 htS₁
  have ht'N : t' ∉ seitzTilde W₁ Kc := by
    have h1 := not_conj_mem_seitzTilde hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield d₀⁻¹
    rwa [inv_inv] at h1
  have ht't : t' * t ∈ S₀ := by
    rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers ht2 htS₀ ht'S₁ with h | h
    · exact absurd (hS₀N h) ht'N
    · exact h
  have h3 : t' * t * t = t' := by rw [mul_assoc, ht2, mul_one]
  have ht'2 : t' * t * t * (t' * t * t) = 1 := by
    rw [h3, ht']
    calc d₀ * t * d₀⁻¹ * (d₀ * t * d₀⁻¹) = d₀ * (t * t) * d₀⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  obtain ⟨z, hzS₀, hz⟩ := hThom _ ht't ht'2
  rw [h3] at hz
  have hzS₁ : z ∈ S₁ := mem_sup_left hzS₀
  refine ⟨z⁻¹ * d₀, ?_, mul_mem (inv_mem (le_normalizer hzS₁)) hd₀N, fun h => hd₀S ?_, ?_,
    T.isPGroup'.to_le ((zpowers_le).2 (mul_mem (inv_mem (hST hzS₁)) hd₀T))⟩
  · rw [mem_centralizer_singleton_iff]
    calc z⁻¹ * d₀ * t = z⁻¹ * t' * d₀ := by rw [ht']; group
      _ = z⁻¹ * (z * t * z⁻¹) * d₀ := by rw [hz]
      _ = t * (z⁻¹ * d₀) := by group
  · have h1 : d₀ = z * (z⁻¹ * d₀) := by group
    rw [h1]
    exact mul_mem hzS₁ h
  · have h1 : z⁻¹ * d₀ * (z⁻¹ * d₀) = z⁻¹ * (d₀ * z⁻¹ * d₀⁻¹) * (d₀ * d₀) := by group
    rw [h1]
    exact mul_mem (mul_mem (inv_mem hzS₁) ((mem_normalizer_iff.1 hd₀N _).1 (inv_mem hzS₁))) hd₀d

theorem graph_element_facts (hset : SeitzSetting G L) {K : Type} [Field K] [CharP K 2]
    (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (c : Fin 5) {W₁ : Subgroup G}
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G)) (Kc : Subgroup (seitzHat W₁))
    {S₀ Q₀ : Subgroup G} (hS₀p : IsPGroup 2 S₀) (hS₀N : S₀ ≤ seitzTilde W₁ Kc)
    (htS₀ : t ∈ normalizer (S₀ : Set G)) (hQL : Q₀ ≤ L) (hQc : Nat.card Q₀ = 2 ^ 10)
    (hQS : Q₀ ≤ S₀) {d : G} (hdC : d ∈ centralizer ({t} : Set G))
    (hdN : d ∈ normalizer ((S₀ ⊔ zpowers t : Subgroup G) : Set G)) (hdS : d ∉ S₀ ⊔ zpowers t)
    (hdd : d * d ∈ S₀ ⊔ zpowers t) :
    d ∈ normalizer (Q₀ : Set G) ∧ d ∉ L ⊔ zpowers t ∧ (d * d ∈ Q₀ ∨ d * d * t ∈ Q₀) := by
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  set S₁ : Subgroup G := S₀ ⊔ zpowers t with hS₁def
  have hS₁p : IsPGroup 2 S₁ :=
    isPGroup_sup_zpowers_of_mem_normalizer hS₀p htS₀ (isPGroup_zpowers_two_of_mul_self ht2)
  have htS₁ : t ∈ S₁ := mem_sup_right (mem_zpowers t)
  have hS₁L : S₁ ⊓ L = Q₀ := inf_eq_of_le_of_card_eq hK e hQL hQc hS₁p (hQS.trans le_sup_left)
  have hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht
  have hdQ : d ∈ normalizer (Q₀ : Set G) := by
    rw [← hS₁L]
    exact mem_normalizer_inf_of_mem_normalizer hdN (hCN hdC)
  have htQ : t ∈ normalizer (Q₀ : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.2 fun q hq => mem_centralizer_iff.1 htC q (hQL hq))
  have hLt : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 htC) l hl)
  have htNL : t ∈ normalizer (L : Set G) := cKind_mem_normalizer hLt
  refine ⟨hdQ, fun h => hdS ?_, ?_⟩
  · rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers ht2 htNL h with h1 | h1
    · exact mem_sup_left (hQS (mem_of_mem_normalizer_of_card_eq hK e hQL hQc h1 hdQ))
    · have h2 := mem_of_mem_normalizer_of_card_eq hK e hQL hQc h1 (mul_mem hdQ htQ)
      have h3 : d = d * t * t := by rw [mul_assoc, ht2, mul_one]
      rw [h3]
      exact mul_mem (mem_sup_left (hQS h2)) htS₁
  · have hddC : d * d ∈ centralizer ({t} : Set G) := mul_mem hdC hdC
    have hddL := sup_inf_centralizer_le_sup hset hK e ht hKt c hW₁t htN Kc
      (mem_inf.2 ⟨sup_le_sup_right hS₀N _ hdd, hddC⟩)
    rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers ht2 htNL hddL with h1 | h1
    · left
      rw [← hS₁L]
      exact mem_inf.2 ⟨hdd, h1⟩
    · right
      rw [← hS₁L]
      exact mem_inf.2 ⟨mul_mem hdd htS₁, h1⟩

theorem maximal_inf_centralizer (hset : SeitzSetting G L) {K : Type} [Field K]
    (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {Q₀ S : Subgroup G} (hQL : Q₀ ≤ L) (hQc : Nat.card Q₀ = 2 ^ 10) {d : G}
    (hdC : d ∈ centralizer ({t} : Set G)) (hdQ : d ∈ normalizer (Q₀ : Set G))
    (hdQt : d ∉ Q₀ ⊔ zpowers t) (hdd : d * d ∈ Q₀ ⊔ zpowers t)
    (hle : Q₀ ⊔ zpowers t ⊔ zpowers d ≤ S) :
    ∀ P : Subgroup G, IsPGroup 2 P → S ⊓ centralizer ({t} : Set G) ≤ P →
      P ≤ centralizer ({t} : Set G) → P = S ⊓ centralizer ({t} : Set G) := by
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have htQ : t ∈ normalizer (Q₀ : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.2 fun q hq => mem_centralizer_iff.1 htC q (hQL hq))
  have htL : t ∉ L := by
    intro h
    have h1 : t ∈ L ⊓ zpowers t := mem_inf.2 ⟨h, mem_zpowers t⟩
    rw [inf_zpowers_eq_bot hset.center_eq_bot htC ht, mem_bot] at h1
    rw [h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hR₀ : Nat.card (Q₀ ⊔ zpowers t : Subgroup G) = 2 ^ 11 := by
    rw [card_sup_zpowers_eq_two_mul (fun h => htL (hQL h)) htQ ht2, hQc]
    norm_num
  have hdR₀ : d ∈ normalizer ((Q₀ ⊔ zpowers t : Subgroup G) : Set G) :=
    mem_normalizer_sup_of_mem_of_mem_normalizer hdQ
      (mem_normalizer_zpowers_of_mul_eq_mul (mem_centralizer_singleton_iff.1 hdC).symm)
  have hR₁ : Nat.card (Q₀ ⊔ zpowers t ⊔ zpowers d : Subgroup G) = 2 ^ 12 := by
    rw [card_sup_zpowers_eq_two_mul_of_mul_self_mem hdQt hdR₀ hdd, hR₀]
    norm_num
  have hLt : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 htC) l hl)
  have hR₁C : Q₀ ⊔ zpowers t ⊔ zpowers d ≤ centralizer ({t} : Set G) :=
    sup_le (sup_le (hQL.trans hLt) ((zpowers_le).2 (mem_centralizer_singleton_iff.2 rfl)))
      ((zpowers_le).2 hdC)
  intro P hP hSP hPC
  have h1 := card_le_two_pow_twelve_of_isPGroup_of_le_centralizer hset hK e ht hKt hP hPC
  have h2 : Nat.card (Q₀ ⊔ zpowers t ⊔ zpowers d : Subgroup G) ≤
      Nat.card (S ⊓ centralizer ({t} : Set G) : Subgroup G) :=
    Subgroup.card_le_of_le (le_inf hle hR₁C)
  rw [hR₁] at h2
  exact (Subgroup.eq_of_le_of_card_ge hSP (h1.trans h2)).symm

end Setting

end CFSG.SeitzReduction.LinearPilot
