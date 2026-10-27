module

public import CFSG.GroupTheory.ABGLocalTools.ZJFactorization

public section

open Subgroup
open scoped Pointwise commutatorElement

namespace CFSG.ABGLocalTools

variable {H : Type*} [Group H] {p : ℕ}

theorem map_pCore_le_of_surjective {K : Type*} [Group K] (f : H →* K)
    (hf : Function.Surjective f) : (pCore p H).map f ≤ pCore p K :=
  le_sSup ⟨(pCore_normal (G := H) (p := p)).map f hf, (pCore_isPGroup (G := H) (p := p)).map f⟩

theorem mem_normalizerPCoreModCentralizer_iff {P : Subgroup H} {x : H} :
    x ∈ normalizerPCoreModCentralizer p P ↔ ∃ hx : x ∈ normalizer (P : Set H),
      QuotientGroup.mk' ((centralizer (P : Set H)).subgroupOf (normalizer (P : Set H)))
        ⟨x, hx⟩ ∈ pCore p (normalizer (P : Set H) ⧸
          (centralizer (P : Set H)).subgroupOf (normalizer (P : Set H))) := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.2, hn⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem map_normalizerPCoreModCentralizer_le (φ : H ≃* H) (P : Subgroup H) :
    (normalizerPCoreModCentralizer p P).map φ.toMonoidHom ≤
      normalizerPCoreModCentralizer p (P.map φ.toMonoidHom) := by
  set Q : Subgroup H := P.map φ.toMonoidHom with hQ
  have hmemQ : ∀ y : H, y ∈ Q ↔ φ.symm y ∈ P := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro hy
      exact ⟨φ.symm y, hy, by simp⟩
  have hN : ∀ n ∈ normalizer (P : Set H), φ n ∈ normalizer (Q : Set H) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro y
    rw [hmemQ, hmemQ, hn (φ.symm y)]
    simp
  have hNsymm : ∀ n ∈ normalizer (Q : Set H), φ.symm n ∈ normalizer (P : Set H) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro y
    have := hn (φ y)
    rw [hmemQ, hmemQ] at this
    simpa using this
  have hC : ∀ c ∈ centralizer (P : Set H), φ c ∈ centralizer (Q : Set H) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    rw [SetLike.mem_coe, hmemQ] at hy
    have := congrArg φ (hc _ hy)
    simpa using this
  let ψ : normalizer (P : Set H) →* normalizer (Q : Set H) :=
    { toFun := fun n => ⟨φ n, hN n n.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hψ : Function.Surjective ψ := by
    intro n
    refine ⟨⟨φ.symm n, hNsymm n n.2⟩, Subtype.ext ?_⟩
    change φ (φ.symm n) = n
    simp
  set CP := (centralizer (P : Set H)).subgroupOf (normalizer (P : Set H))
  set CQ := (centralizer (Q : Set H)).subgroupOf (normalizer (Q : Set H))
  have hker : CP ≤ CQ.comap ψ := fun c hc => hC c hc
  let ψbar := QuotientGroup.map CP CQ ψ hker
  have hψbar : Function.Surjective ψbar :=
    QuotientGroup.map_surjective_of_surjective CP CQ ψ
      ((QuotientGroup.mk'_surjective CQ).comp hψ) hker
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_normalizerPCoreModCentralizer_iff] at hx
  change φ x ∈ normalizerPCoreModCentralizer p Q
  rw [mem_normalizerPCoreModCentralizer_iff]
  obtain ⟨hxN, hxp⟩ := hx
  refine ⟨hN x hxN, ?_⟩
  have := map_pCore_le_of_surjective (p := p) ψbar hψbar ⟨_, hxp, rfl⟩
  exact this

variable [Finite H] [Fact p.Prime]

theorem le_normalizer_of_sup_normal {P : Subgroup H} (S : Sylow p H) (hPS : P ≤ S)
    (hn : (pPrimeCore p H ⊔ P).Normal) : (S : Subgroup H) ≤ normalizer (P : Set H) := by
  have hPp : IsPGroup p P := S.isPGroup'.to_le hPS
  have hsyl : IsSylowOf p P (pPrimeCore p H ⊔ P) :=
    isSylowOf_sup_of_coprime pPrimeCore_coprime_card hPp
  have heq : (S : Subgroup H) ⊓ (pPrimeCore p H ⊔ P) = P :=
    hsyl.eq_of_le (le_inf hPS le_sup_right) inf_le_right (S.isPGroup'.to_le inf_le_left)
  intro s hs
  rw [← heq]
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs,
    by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top s⟩

theorem isPStableWrt_sylow_iff (S : Sylow p H) :
    IsPStableWrt p H S ↔ IsPStable p H := by
  have hSsyl : IsSylowOf p (S : Subgroup H) ⊤ := by
    rw [isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, S.isPGroup', S.not_dvd_index⟩
  constructor
  · rintro ⟨hOp, -, -, -, hst⟩
    refine ⟨hOp, fun P A hP1 hPp hn hAp hAN hcomm => ?_⟩
    have hAP : IsPGroup p (A ⊔ P : Subgroup H) :=
      IsPGroup.to_sup_of_normal_right' hAp hPp hAN
    obtain ⟨S', hS'⟩ := hAP.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S' S
    set φ : H ≃* H := MulAut.conj g with hφ
    have hmemS : ∀ x ∈ (S' : Subgroup H), φ x ∈ (S : Subgroup H) := by
      intro x hx
      rw [← hg, Sylow.coe_subgroup_smul]
      exact ⟨x, hx, rfl⟩
    set P' : Subgroup H := P.map φ.toMonoidHom
    set A' : Subgroup H := A.map φ.toMonoidHom
    have hP'S : P' ≤ S := by
      rintro _ ⟨x, hx, rfl⟩
      exact hmemS x (hS' (le_sup_right (a := A) hx))
    have hA'S : A' ≤ S := by
      rintro _ ⟨x, hx, rfl⟩
      exact hmemS x (hS' (le_sup_left (b := P) hx))
    have hP'1 : P' ≠ ⊥ := by
      intro h
      apply hP1
      rw [eq_bot_iff]
      intro x hx
      have : φ x ∈ P' := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).mpr (by simpa using this)
    have hMφ : (pPrimeCore p H).map φ.toMonoidHom = pPrimeCore p H :=
      Subgroup.characteristic_iff_map_eq.mp inferInstance φ
    have hn' : (pPrimeCore p H ⊔ P').Normal := by
      have : (pPrimeCore p H ⊔ P') = (pPrimeCore p H ⊔ P).map φ.toMonoidHom := by
        rw [Subgroup.map_sup, hMφ]
      rw [this]
      exact hn.map _ φ.surjective
    have hcomm' : ⁅⁅P', A'⁆, A'⁆ = ⊥ := by
      rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hcomm, Subgroup.map_bot]
    have hA' := hst P' A' hP'1 hP'S hn' hA'S hcomm'
    have hback := map_normalizerPCoreModCentralizer_le (p := p) φ.symm P'
    have hPP : P'.map φ.symm.toMonoidHom = P := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id P
      ext x
      simp
    rw [hPP] at hback
    intro a ha
    apply hback
    refine ⟨φ a, hA' ⟨a, ha, rfl⟩, ?_⟩
    simp
  · intro hst
    refine ⟨hst.1, S.isPGroup', ?_, Or.inl ⟨S, le_rfl, Subgroup.le_normalizer⟩, ?_⟩
    · exact hSsyl.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top])
    · intro P A hP1 hPS hn hAS hcomm
      exact hst.2 P A hP1 (S.isPGroup'.to_le hPS) hn (S.isPGroup'.to_le hAS)
        (hAS.trans (le_normalizer_of_sup_normal S hPS hn)) hcomm

end CFSG.ABGLocalTools
