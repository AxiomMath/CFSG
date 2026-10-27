module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5ModGroup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.NineThreeThreeKill
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltBigVector

@[expose] public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.Open A5Mod

section Group

variable {G : Type} [Group G] [Finite G]

theorem blockU_conj_mem {L : Subgroup G} {ℓ : G} (hℓ : ℓ ∈ L) {u : G} (hu : u ∈ blockU L) :
    ℓ * u * ℓ⁻¹ ∈ blockU L := by
  have hQ : ∀ x ∈ blockQ L, ℓ * x * ℓ⁻¹ ∈ blockQ L := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) L hℓ) x).mp hx
  unfold blockU at hu ⊢
  rw [Subgroup.commutator_def] at hu ⊢
  induction hu using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hg
    refine Subgroup.subset_closure ⟨ℓ * a * ℓ⁻¹, hQ a ha, ℓ * b * ℓ⁻¹,
      L.mul_mem (L.mul_mem hℓ hb) (L.inv_mem hℓ), ?_⟩
    simp only [commutatorElement_def]
    group
  | one => simpa using Subgroup.one_mem _
  | mul a b _ _ ha hb =>
    have : ℓ * (a * b) * ℓ⁻¹ = (ℓ * a * ℓ⁻¹) * (ℓ * b * ℓ⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : ℓ * a⁻¹ * ℓ⁻¹ = (ℓ * a * ℓ⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

set_option maxHeartbeats 4000000 in
theorem isAlt5_or_lin2 {L : Subgroup G} (hshort : IsShort2 L) (hperf : ⁅L, L⁆ = L)
    (α₀ : ↥L →* A5) (hs : Function.Surjective α₀) (hker : α₀.ker = CFSG.pCore 2 ↥L) :
    IsAltType L 5 ∨ IsLin2Type L 2 := by
  classical
  obtain ⟨-, -, ⟨hUQ, hexp⟩, -, hZlt, hirrU⟩ := hshort
  have hcommL : commutator ↥L = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      hperf]
  letI actU : MulDistribMulAction ↥L ↥(blockU L) :=
    { smul := fun ℓ u => ⟨(ℓ : G) * u * (ℓ : G)⁻¹, blockU_conj_mem ℓ.2 u.2⟩
      one_smul := fun u => Subtype.ext (by
        show ((1 : ↥L) : G) * u * ((1 : ↥L) : G)⁻¹ = u
        simp)
      mul_smul := fun ℓ ℓ' u => Subtype.ext (by
        show ((ℓ * ℓ' : ↥L) : G) * u * ((ℓ * ℓ' : ↥L) : G)⁻¹ =
          (ℓ : G) * ((ℓ' : G) * u * (ℓ' : G)⁻¹) * (ℓ : G)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group)
      smul_mul := fun ℓ a b => Subtype.ext (by
        show (ℓ : G) * ((a * b : ↥(blockU L)) : G) * (ℓ : G)⁻¹ =
          ((ℓ : G) * a * (ℓ : G)⁻¹) * ((ℓ : G) * b * (ℓ : G)⁻¹)
        simp only [Subgroup.coe_mul]
        group)
      smul_one := fun ℓ => Subtype.ext (by
        show (ℓ : G) * ((1 : ↥(blockU L)) : G) * (ℓ : G)⁻¹ = 1
        simp) }
  have hsm : ∀ (ℓ : ↥L) (u : ↥(blockU L)), ((ℓ • u : ↥(blockU L)) : G) = ℓ * u * (ℓ : G)⁻¹ :=
    fun _ _ => rfl
  let Z : Subgroup ↥(blockU L) := (blockZ L).subgroupOf (blockU L)
  have hZmem : ∀ u : ↥(blockU L), u ∈ Z ↔ (u : G) ∈ blockZ L := fun u => Iff.rfl
  have hcomm : ∀ a b : ↥(blockU L), a * b = b * a := fun a b => by
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hUQ a.2).2 b (hUQ b.2).1).symm
  have hexp' : ∀ u : ↥(blockU L), u * u = 1 := fun u => by
    apply Subtype.ext
    have := hexp u u.2
    simpa [sq] using this
  have hZc : ∀ z : ↥(blockU L), z ∈ Z → ∀ ℓ : ↥L, ℓ • z = z := fun z hz ℓ => by
    apply Subtype.ext
    rw [hsm]
    have h := Subgroup.mem_centralizer_iff.mp ((hZmem z).mp hz).2 ℓ ℓ.2
    rw [h]; group
  have hZfix : ∀ (ℓ : ↥L), ∀ z ∈ Z, ℓ • z ∈ Z := fun ℓ z hz => by rw [hZc z hz ℓ]; exact hz
  have htriv : ∀ ℓ ∈ α₀.ker, ∀ u : ↥(blockU L), ℓ • u * u⁻¹ ∈ Z := by
    intro ℓ hℓ u
    rw [hker] at hℓ
    have hQ : (ℓ : G) ∈ blockQ L := (CFSG.RankThree.PartTwo.Sec19.Item194Proof.mem_pCore_iff ℓ).mp hℓ
    have h := Subgroup.mem_centralizer_iff.mp (hUQ u.2).2 ℓ hQ
    have : ℓ • u * u⁻¹ = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, hsm, Subgroup.coe_inv, h]
      simp
    rw [this]
    exact Z.one_mem
  have hirr : ∀ K : Subgroup ↥(blockU L), Z ≤ K → (∀ (ℓ : ↥L), ∀ k ∈ K, ℓ • k ∈ K) →
      K = Z ∨ K = ⊤ := by
    intro K hZK hKinv
    have hmemW : ∀ g : G, g ∈ K.map (blockU L).subtype ↔ ∃ k : ↥(blockU L), k ∈ K ∧ (k : G) = g :=
      fun g => Subgroup.mem_map
    have hZW : blockZ L ≤ K.map (blockU L).subtype := fun g hg => by
      have hgU : g ∈ blockU L := hg.1
      exact (hmemW g).mpr ⟨⟨g, hgU⟩, hZK ((hZmem ⟨g, hgU⟩).mpr hg), rfl⟩
    have hWU : K.map (blockU L).subtype ≤ blockU L := fun g hg => by
      obtain ⟨k, -, rfl⟩ := (hmemW g).mp hg
      exact k.2
    have hinvW : ∀ ℓ ∈ L, ∀ g ∈ K.map (blockU L).subtype,
        ℓ * g * ℓ⁻¹ ∈ K.map (blockU L).subtype := fun ℓ hℓ g hg => by
      obtain ⟨k, hk, rfl⟩ := (hmemW g).mp hg
      exact (hmemW _).mpr ⟨(⟨ℓ, hℓ⟩ : ↥L) • k, hKinv _ k hk, rfl⟩
    have hLnorm : L ≤ Subgroup.normalizer ((K.map (blockU L).subtype : Subgroup G) : Set G) :=
      fun ℓ hℓ => by
        rw [Subgroup.mem_normalizer_iff]
        intro g
        constructor
        · exact hinvW ℓ hℓ g
        · intro h
          have := hinvW ℓ⁻¹ (L.inv_mem hℓ) _ h
          simpa [mul_assoc] using this
    rcases hirrU _ hZW hWU hLnorm with h | h
    · left
      apply le_antisymm
      · intro k hk
        have : (k : G) ∈ K.map (blockU L).subtype := (hmemW _).mpr ⟨k, hk, rfl⟩
        rw [h] at this
        exact (hZmem k).mpr this
      · exact hZK
    · right
      rw [eq_top_iff]
      intro u _
      have : (u : G) ∈ K.map (blockU L).subtype := by rw [h]; exact u.2
      obtain ⟨k, hk, hku⟩ := (hmemW _).mp this
      have : k = u := Subtype.ext hku
      rwa [this] at hk
  have hZne : Z ≠ ⊤ := by
    intro htop
    apply hZlt.ne
    refine le_antisymm hZlt.le (fun g hg => ?_)
    have : (⟨g, hg⟩ : ↥(blockU L)) ∈ Z := by rw [htop]; exact Subgroup.mem_top _
    exact (hZmem _).mp this
  have hact : ∃ (ℓ : ↥L) (u : ↥(blockU L)), ℓ • u * u⁻¹ ∉ Z := by
    by_contra hcon
    push Not at hcon
    apply hZne
    rw [eq_top_iff]
    intro u _
    haveI : IsMulCommutative ↥Z := ⟨⟨fun a b => Subtype.ext (hcomm a b)⟩⟩
    let c : ↥L →* ↥Z :=
      { toFun := fun ℓ => ⟨ℓ • u * u⁻¹, hcon ℓ u⟩
        map_one' := by apply Subtype.ext; simp
        map_mul' := fun ℓ ℓ' => by
          apply Subtype.ext
          show (ℓ * ℓ') • u * u⁻¹ = (ℓ • u * u⁻¹) * (ℓ' • u * u⁻¹)
          have e1 : ℓ' • u = (ℓ' • u * u⁻¹) * u := by simp
          calc (ℓ * ℓ') • u * u⁻¹ = ℓ • (ℓ' • u) * u⁻¹ := by rw [mul_smul]
            _ = ℓ • ((ℓ' • u * u⁻¹) * u) * u⁻¹ := by rw [← e1]
            _ = (ℓ • (ℓ' • u * u⁻¹)) * (ℓ • u) * u⁻¹ := by rw [smul_mul']
            _ = (ℓ' • u * u⁻¹) * (ℓ • u) * u⁻¹ := by rw [hZc _ (hcon ℓ' u) ℓ]
            _ = (ℓ' • u * u⁻¹) * (ℓ • u * u⁻¹) := by rw [mul_assoc]
            _ = (ℓ • u * u⁻¹) * (ℓ' • u * u⁻¹) := hcomm _ _ }
    have hk : ∀ ℓ : ↥L, c ℓ = 1 := fun ℓ =>
      Abelianization.commutator_subset_ker c (hcommL ▸ Subgroup.mem_top ℓ)
    have hfix : ∀ ℓ : ↥L, ℓ • u = u := fun ℓ => by
      have h1 : ℓ • u * u⁻¹ = 1 := congrArg Subtype.val (hk ℓ)
      exact mul_inv_eq_one.mp h1
    have hcent : (u : G) ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have := congrArg Subtype.val (hfix ⟨h, hh⟩)
      rw [hsm] at this
      calc h * u = (h * u * h⁻¹) * h := by group
        _ = u * h := by rw [this]
    exact (hZmem u).mpr ⟨u.2, hcent⟩
  rcases plumbing hcomm hexp' Z hZfix α₀ hs htriv hirr hZne hact with
    ⟨β, hβs, hβk, hβe⟩ | ⟨α₂, β, hα₂i, hα₂s, hβs, hβk, hβe⟩
  · left
    refine ⟨α₀, hs, hker, β, hβs, hβk, ?_⟩
    intro ℓ u v hv i
    have : v = ℓ • u := Subtype.ext hv
    rw [this]
    exact hβe ℓ u i
  · right
    refine ⟨F4, inferInstance, inferInstance, by decide, α₂.comp α₀, hα₂s.comp hs, ?_, β, hβs,
      hβk, ?_⟩
    · rw [← hker]
      ext ℓ
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, map_eq_one_iff α₂ hα₂i, MonoidHom.mem_ker]
    · intro ℓ u v hv
      have : v = ℓ • u := Subtype.ext hv
      rw [this]
      exact hβe ℓ u

theorem kFactNineThreeThreeFive_proved : KFactNineThreeThreeFive := by
  intro G _ _ M S L hL h3 ⟨e⟩
  have hshort : IsShort2 L := h3.1
  let α₀ : ↥L →* A5 := (e : ↥(barM M L) →* A5).comp (barMHom hL.le)
  have hs : Function.Surjective α₀ := e.surjective.comp (barMHom_surjective hL.le)
  have hker : α₀.ker = CFSG.pCore 2 ↥L := by
    ext ℓ
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    show e (barMHom hL.le ℓ) = 1 ↔ ℓ ∈ CFSG.pCore 2 ↥L
    rw [map_eq_one_iff e e.injective, Subtype.ext_iff, barMHom_apply]
    show QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨ℓ, hL.le ℓ.2⟩ = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      CFSG.RankThree.PartTwo.Sec19.Item194Proof.mem_pCore_iff,
      CFSG.RankThree.PartTwo.Sec19.Item194Proof.mem_pCore_iff, ← hL.toIsTwoPrimeComponent.inf_twoCore]
    exact ⟨fun h => ⟨ℓ.2, h⟩, fun h => h.2⟩
  rcases isAlt5_or_lin2 hshort hL.perfect α₀ hs hker with h | h
  · exact ⟨hshort, Or.inr ⟨2, by norm_num, h⟩⟩
  · exact ⟨hshort, Or.inl ⟨2, by norm_num, h⟩⟩

end Group

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
