module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndNormalizer
public import CFSG.GH74.GLS.C3.Layer2.FusionTools

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaEnd

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools

variable {G : Type} [Group G]

theorem conj_mem_normalizer_map {X : Subgroup G} {g n : G} (hn : n ∈ normalizer (X : Set G)) :
    g * n * g⁻¹ ∈ normalizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  refine le_normalizer_of_conj_mem (V := zpowers (g * n * g⁻¹)) (fun v hv r hr => ?_)
    (mem_zpowers _)
  obtain ⟨k, rfl⟩ := hv
  obtain ⟨x, hx, rfl⟩ := hr
  have hnk : n ^ k ∈ normalizer (X : Set G) := zpow_mem hn k
  refine ⟨n ^ k * x * (n ^ k)⁻¹, (mem_normalizer_iff.mp hnk x).mp hx, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have : (g * n * g⁻¹) ^ k = g * n ^ k * g⁻¹ := by
    rw [show g * n * g⁻¹ = MulAut.conj g n from rfl, ← map_zpow]
    rfl
  rw [this]
  group

theorem map_conj_mul (X : Subgroup G) (a b : G) :
    X.map (MulAut.conj (a * b)).toMonoidHom =
      (X.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.coe_comp,
    Function.comp_apply]
  group

theorem map_conj_le_centralizer {Q : Subgroup G} {g t : G}
    (hQ : Q ≤ centralizer ({g⁻¹ * t * g} : Set G)) :
    Q.map (MulAut.conj g).toMonoidHom ≤ centralizer ({t} : Set G) := by
  rintro _ ⟨q, hq, rfl⟩
  have h1 := mem_centralizer_singleton_iff.mp (hQ hq)
  rw [mem_centralizer_singleton_iff]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * q * g⁻¹ * t = g * (q * (g⁻¹ * t * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * t * g) * q) * g⁻¹ := by rw [h1]
    _ = t * (g * q * g⁻¹) := by group

variable [Finite G] {F : Type} [Field F] [Finite F] {L : Subgroup G} {t : G}
  {S A₁ V₁ G₀ : Subgroup G}

theorem exists_sylow_eq
    (h : YamadaG0 F L t S A₁ V₁ G₀) (hA : L64CentralizerInput)
    (hU : U62RankInput) {T : Subgroup G} (hT : IsSylowOf 2 T (normalizer (G₀ : Set G)))
    (htT : t ∈ T) : ∃ P : Sylow 2 G, (P : Subgroup G) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hTQ⟩ := hT.isPGroup.exists_le_sylow
  refine ⟨Q, ?_⟩
  by_contra hne
  have hlt : T.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne (le_antisymm (fun x hx => ?_) hTQ)
    have : (⟨x, hx⟩ : Q) ∈ T.subgroupOf Q := htop ▸ mem_top _
    exact this
  have : Group.IsNilpotent Q := Q.isPGroup'.isNilpotent
  obtain ⟨y, hyN, hyT⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hyN' : ∀ x ∈ T, (y : G)⁻¹ * x * y ∈ T := by
    intro x hx
    have := (mem_normalizer_iff.mp (inv_mem hyN) ⟨x, hTQ hx⟩).mp hx
    rw [mem_subgroupOf] at this
    simpa using this
  have hty : t ∈ normalizer ((G₀.map (MulAut.conj (y : G)).toMonoidHom : Subgroup G) : Set G) := by
    have h1 : (y : G)⁻¹ * t * y ∈ normalizer (G₀ : Set G) := hT.le (hyN' t htT)
    have := conj_mem_normalizer_map (g := (y : G)) h1
    simpa [mul_assoc] using this
  have hyG₀ := yamada_5_5 h hA hU y hty
  have hsub : T ⊔ zpowers (y : G) ≤ Q := sup_le hTQ (by rw [zpowers_le]; exact y.2)
  have hp : IsPGroup 2 (T ⊔ zpowers (y : G) : Subgroup G) :=
    Q.isPGroup'.to_le hsub
  have heq := hT.eq_of_le le_sup_left (sup_le hT.le (by rw [zpowers_le]; exact hyG₀)) hp
  exact hyT (show ((y : G)) ∈ T from heq ▸ mem_sup_right (mem_zpowers _))

theorem exists_sylow_normalizer (h : YamadaG0 F L t S A₁ V₁ G₀) :
    ∃ T : Subgroup G, IsSylowOf 2 T (normalizer (G₀ : Set G)) ∧ t ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.order_t, pow_one])
  obtain ⟨T, hT, htT⟩ := exists_isSylowOf_ge (by rw [zpowers_le]; exact h.t_normalizes) hz
  exact ⟨T, hT, htT (mem_zpowers t)⟩

theorem false_of_linear
    (h : YamadaG0 F L t S A₁ V₁ G₀) (hA : L64CentralizerInput)
    (hE : L64TransferInput) (hU : U62RankInput) (hlin : LinearCase F G₀) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨ψ, hψ, hker⟩, -⟩ := hlin
  obtain ⟨T, hT, htT⟩ := exists_sylow_normalizer h
  obtain ⟨P, hP⟩ := exists_sylow_eq h hA hU hT htT
  have hH2 : ∀ Q ≤ G₀ ⊓ centralizer ({t} : Set G), IsPGroup 2 Q → Nat.card Q ≤ 2 ^ 17 :=
    fun Q hQ hQ2 => card_le_of_isPGroup h.setting.standard h.lie h.order_t h.t_mem h.kernel
      (hQ.trans inf_le_right) hQ2
  obtain ⟨M, hMT, hMidx, hMinv⟩ :=
    hE G F h.card_field G₀ ψ hψ hker h.odd_centralizer T t hT htT h.order_t hH2
  obtain ⟨g, hg⟩ := CFSG.GH74.GLS.C3.Layer2.exists_conj_mem_of_simple h.setting.simple
    h.setting.nonab P (Q := M) (by rw [hP]; exact hMT) (by rw [hP]; exact hMidx) h.order_t
  have hord : orderOf (g⁻¹ * t * g) = 2 := by
    have := (MulAut.conj g⁻¹).orderOf_eq t
    simp only [MulAut.conj_apply, inv_inv] at this
    rw [this, h.order_t]
  obtain ⟨Q, hQ, hQ2, hQc⟩ := hMinv _ hg hord
  have hQ' := map_conj_le_centralizer (hQ.trans inf_le_right)
  have hle := card_le_of_isPGroup h.setting.standard h.lie h.order_t h.t_mem h.kernel hQ'
    (hQ2.map _)
  rw [card_map_of_injective (MulAut.conj g).injective] at hle
  omega

theorem false_of_unitary
    (h : YamadaG0 F L t S A₁ V₁ G₀) (hA : L64CentralizerInput)
    (hU : U62RankInput) (hun : UnitaryCase G₀ t) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨G₁, hG₀, hc, hne, hq, -, -⟩ := hun
  set G₂ := G₁.map (MulAut.conj t).toMonoidHom with hG₂
  have ht2 : t * t = 1 := by rw [← sq, ← h.order_t]; exact pow_orderOf_eq_one t
  have hq₂ : CFSG.Open.IsQuasisimple G₂ :=
    isQuasisimple_of_mulEquiv (G₁.equivMapOfInjective _ (MulAut.conj t).injective) hq
  have hc' : ⁅G₂, G₁⁆ = ⊥ := by rw [commutator_comm]; exact hc
  have hperm : ∀ x ∈ normalizer (G₀ : Set G),
      G₁.map (MulAut.conj x).toMonoidHom = G₁ ∨ G₁.map (MulAut.conj x).toMonoidHom = G₂ :=
    fun x hx => conj_component_eq hq hq₂ hc (hG₀ ▸ hx)
  have hperm₂ : ∀ x ∈ normalizer (G₀ : Set G),
      G₂.map (MulAut.conj x).toMonoidHom = G₂ ∨ G₂.map (MulAut.conj x).toMonoidHom = G₁ :=
    fun x hx => conj_component_eq hq₂ hq hc' (by rw [sup_comm, ← hG₀]; exact hx)
  have htG₁ : t ∉ normalizer (G₁ : Set G) := fun ht => hne (map_conj_eq_of_mem_normalizer ht)
  have hGG : G₂.map (MulAut.conj t).toMonoidHom = G₁ := by
    rw [hG₂, ← map_conj_mul, ht2, map_one]
    ext x
    simp
  obtain ⟨T, hT, htT⟩ := exists_sylow_normalizer h
  obtain ⟨P, hP⟩ := exists_sylow_eq h hA hU hT htT
  set M := T ⊓ normalizer (G₁ : Set G) with hM
  have hMidx : M.relIndex T = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨t, htT⟩, fun b => ?_⟩
    have hbN := hT.le b.2
    rw [mem_subgroupOf, mem_subgroupOf]
    simp only [coe_mul]
    rcases hperm b hbN with hb | hb
    · have hbM : (b : G) ∈ M := ⟨b.2, mem_normalizer_of_map_conj_eq hb⟩
      have hbtM : (b : G) * t ∉ M := fun hbt => htG₁ (by
        have := (normalizer (G₁ : Set G)).mul_mem ((normalizer (G₁ : Set G)).inv_mem hbM.2) hbt.2
        simpa using this)
      exact Or.inr ⟨hbM, hbtM⟩
    · have hbM : (b : G) ∉ M := fun hbM => hne (by
        rw [← hb]
        exact map_conj_eq_of_mem_normalizer hbM.2)
      have hbt : G₁.map (MulAut.conj ((b : G) * t)).toMonoidHom = G₁ := by
        rw [map_conj_mul]
        rcases hperm₂ b hbN with hb₂ | hb₂
        · exfalso
          apply hne
          apply map_injective (f := (MulAut.conj (b : G)).toMonoidHom)
            (MulAut.conj (b : G)).injective
          rw [hb₂, hb]
        · exact hb₂
      exact Or.inl ⟨⟨mul_mem b.2 htT, mem_normalizer_of_map_conj_eq hbt⟩, hbM⟩
  obtain ⟨g, hg⟩ := CFSG.GH74.GLS.C3.Layer2.exists_conj_mem_of_simple h.setting.simple
    h.setting.nonab P (Q := M) (by rw [hP]; exact inf_le_left) (by rw [hP]; exact hMidx)
    h.order_t
  have hgt : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
  have htg : t ∈ normalizer ((G₀.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    have := conj_mem_normalizer_map (g := g) (hT.le hg.1)
    rwa [hgt] at this
  have hgN := yamada_5_5 h hA hU g htg
  have htG : t ∈ normalizer ((G₁.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    have := conj_mem_normalizer_map (g := g) hg.2
    rwa [hgt] at this
  rcases hperm g hgN with h1 | h1
  · rw [h1] at htG
    exact htG₁ htG
  · rw [h1] at htG
    apply hne
    rw [← hGG]
    exact (map_conj_eq_of_mem_normalizer htG).symm

theorem false_of_yamadaG0
    (h : YamadaG0 F L t S A₁ V₁ G₀) (hA : L64CentralizerInput)
    (hE : L64TransferInput) (hU : U62RankInput) : False :=
  h.cases.elim (false_of_linear h hA hE hU) (false_of_unitary h hA hU)

end CFSG.EvenSmallLie.UnitarySix.YamadaEnd
