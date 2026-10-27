module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.E9Q

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.E9Transitive

open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {Q : Type*} [Group Q]

theorem le_normalizer_centralizer (Lb : Subgroup Q) :
    Lb ≤ Subgroup.normalizer (Subgroup.centralizer (Lb : Set Q) : Set Q) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    have e : l * c * l⁻¹ = c := by
      rw [Subgroup.mem_centralizer_iff.mp hc l hl, mul_inv_cancel_right]
    rwa [e]
  · intro hc
    have h1 := Subgroup.mem_centralizer_iff.mp hc l hl
    have h2 : l * (l * c * l⁻¹) = l * c := by
      rw [h1]
      group
    rwa [mul_left_cancel h2] at hc

theorem exists_mul_of_mem_sup_centralizer {Lb : Subgroup Q} {x : Q}
    (hx : x ∈ Lb ⊔ Subgroup.centralizer (Lb : Set Q)) :
    ∃ l ∈ Lb, ∃ c ∈ Subgroup.centralizer (Lb : Set Q), l * c = x := by
  have hx' : x ∈ ((Lb ⊔ Subgroup.centralizer (Lb : Set Q) : Subgroup Q) : Set Q) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (le_normalizer_centralizer Lb)] at hx'
  obtain ⟨l, hl, c, hc, h⟩ := Set.mem_mul.mp hx'
  exact ⟨l, hl, c, hc, h⟩

theorem mem_center_of_mem_centralizer {Lb : Subgroup Q} (z : ↥Lb)
    (hz : (z : Q) ∈ Subgroup.centralizer (Lb : Set Q)) : z ∈ Subgroup.center ↥Lb :=
  Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_centralizer_iff.mp hz g g.2)

theorem mem_centralizer_of_mem_center {Lb : Subgroup Q} {z : ↥Lb}
    (hz : z ∈ Subgroup.center ↥Lb) : (z : Q) ∈ Subgroup.centralizer (Lb : Set Q) :=
  Subgroup.mem_centralizer_iff.mpr fun h hh =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨h, hh⟩)

theorem conj_mem_centralizer {Lb : Subgroup Q} {n c : Q}
    (hn : n ∈ Subgroup.normalizer (Lb : Set Q)) (hc : c ∈ Subgroup.centralizer (Lb : Set Q)) :
    n * c * n⁻¹ ∈ Subgroup.centralizer (Lb : Set Q) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hh' : n⁻¹ * h * n ∈ Lb := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) h).mp hh
    simpa using this
  have hcomm := Subgroup.mem_centralizer_iff.mp hc _ hh'
  calc h * (n * c * n⁻¹) = n * ((n⁻¹ * h * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * h * n)) * n⁻¹ := by rw [hcomm]
    _ = n * c * n⁻¹ * h := by group

theorem mk_eq_of_mul_eq {Lb : Subgroup Q} {l₁ l₂ c₁ c₂ : Q} (hl₁ : l₁ ∈ Lb) (hl₂ : l₂ ∈ Lb)
    (hc₁ : c₁ ∈ Subgroup.centralizer (Lb : Set Q))
    (hc₂ : c₂ ∈ Subgroup.centralizer (Lb : Set Q)) (h : l₁ * c₁ = l₂ * c₂) :
    (QuotientGroup.mk (⟨l₁, hl₁⟩ : ↥Lb) : ↥Lb ⧸ Subgroup.center ↥Lb) =
      QuotientGroup.mk (⟨l₂, hl₂⟩ : ↥Lb) := by
  rw [QuotientGroup.eq]
  apply mem_center_of_mem_centralizer
  have e : l₁⁻¹ * l₂ = c₁ * c₂⁻¹ := by
    calc l₁⁻¹ * l₂ = l₁⁻¹ * (l₂ * c₂) * c₂⁻¹ := by group
      _ = l₁⁻¹ * (l₁ * c₁) * c₂⁻¹ := by rw [h]
      _ = c₁ * c₂⁻¹ := by group
  change l₁⁻¹ * l₂ ∈ Subgroup.centralizer (Lb : Set Q)
  rw [e]
  exact Subgroup.mul_mem _ hc₁ (Subgroup.inv_mem _ hc₂)

variable {Lb E : Subgroup Q}

@[expose] noncomputable def projFun (hEL : E ≤ Lb ⊔ Subgroup.centralizer (Lb : Set Q)) (e : ↥E) :
    ↥Lb ⧸ Subgroup.center ↥Lb :=
  QuotientGroup.mk ⟨Classical.choose (exists_mul_of_mem_sup_centralizer (hEL e.2)),
    (Classical.choose_spec (exists_mul_of_mem_sup_centralizer (hEL e.2))).1⟩

theorem projFun_eq (hEL : E ≤ Lb ⊔ Subgroup.centralizer (Lb : Set Q)) (e : ↥E) {l c : Q}
    (hl : l ∈ Lb) (hc : c ∈ Subgroup.centralizer (Lb : Set Q)) (h : l * c = e) :
    projFun hEL e = QuotientGroup.mk (⟨l, hl⟩ : ↥Lb) := by
  obtain ⟨hl', c', hc', h'⟩ :=
    Classical.choose_spec (exists_mul_of_mem_sup_centralizer (hEL e.2))
  exact mk_eq_of_mul_eq hl' hl hc' hc (h'.trans h.symm)

@[expose] noncomputable def projHom (hEL : E ≤ Lb ⊔ Subgroup.centralizer (Lb : Set Q)) :
    ↥E →* ↥Lb ⧸ Subgroup.center ↥Lb where
  toFun := projFun hEL
  map_one' := by
    rw [projFun_eq hEL 1 Lb.one_mem (Subgroup.one_mem _) (by simp)]
    rfl
  map_mul' a b := by
    obtain ⟨l₁, hl₁, c₁, hc₁, h₁⟩ := exists_mul_of_mem_sup_centralizer (hEL a.2)
    obtain ⟨l₂, hl₂, c₂, hc₂, h₂⟩ := exists_mul_of_mem_sup_centralizer (hEL b.2)
    have hcomm : c₁ * l₂ = l₂ * c₁ := (Subgroup.mem_centralizer_iff.mp hc₁ l₂ hl₂).symm
    have hab : l₁ * l₂ * (c₁ * c₂) = ((a * b : ↥E) : Q) := by
      rw [Subgroup.coe_mul, ← h₁, ← h₂]
      calc l₁ * l₂ * (c₁ * c₂) = l₁ * (l₂ * c₁) * c₂ := by group
        _ = l₁ * (c₁ * l₂) * c₂ := by rw [hcomm]
        _ = l₁ * c₁ * (l₂ * c₂) := by group
    rw [projFun_eq hEL a hl₁ hc₁ h₁, projFun_eq hEL b hl₂ hc₂ h₂,
      projFun_eq hEL (a * b) (Lb.mul_mem hl₁ hl₂) (Subgroup.mul_mem _ hc₁ hc₂) hab]
    rfl

theorem projHom_apply (hEL : E ≤ Lb ⊔ Subgroup.centralizer (Lb : Set Q)) (e : ↥E) :
    projHom hEL e = projFun hEL e := rfl

theorem projHom_injective (hEL : E ≤ Lb ⊔ Subgroup.centralizer (Lb : Set Q))
    (hEC : E ⊓ Subgroup.centralizer (Lb : Set Q) = ⊥) : Function.Injective (projHom hEL) := by
  rw [injective_iff_map_eq_one]
  intro e he
  obtain ⟨l, hl, c, hc, h⟩ := exists_mul_of_mem_sup_centralizer (hEL e.2)
  have h1 : projHom hEL e = QuotientGroup.mk (⟨l, hl⟩ : ↥Lb) := projFun_eq hEL e hl hc h
  rw [he, eq_comm, QuotientGroup.eq_one_iff] at h1
  have hlC : l ∈ Subgroup.centralizer (Lb : Set Q) := mem_centralizer_of_mem_center h1
  have heC : (e : Q) ∈ Subgroup.centralizer (Lb : Set Q) := by
    rw [← h]
    exact Subgroup.mul_mem _ hlC hc
  have hmem : (e : Q) ∈ E ⊓ Subgroup.centralizer (Lb : Set Q) := ⟨e.2, heC⟩
  rw [hEC, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

theorem card_range_projHom (hEL : E ≤ Lb ⊔ Subgroup.centralizer (Lb : Set Q))
    (hEC : E ⊓ Subgroup.centralizer (Lb : Set Q) = ⊥) :
    Nat.card (projHom hEL).range = Nat.card E :=
  (Nat.card_congr (MonoidHom.ofInjective (projHom_injective hEL hEC)).toEquiv).symm

theorem range_projHom_le {P K : Subgroup Q} (hEL : E ≤ Lb ⊔ Subgroup.centralizer (Lb : Set Q))
    (hEK : E ≤ K) (hCK : Subgroup.centralizer (Lb : Set Q) ≤ K) (hKP : K ⊓ Lb ≤ P) :
    (projHom hEL).range ≤ (P.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb)) := by
  rintro _ ⟨e, rfl⟩
  obtain ⟨l, hl, c, hc, h⟩ := exists_mul_of_mem_sup_centralizer (hEL e.2)
  have hlK : l ∈ K := by
    have hle : l = e * c⁻¹ := by
      rw [← h]
      group
    rw [hle]
    exact K.mul_mem (hEK e.2) (K.inv_mem (hCK hc))
  exact ⟨⟨l, hl⟩, Subgroup.mem_subgroupOf.mpr (hKP ⟨hlK, hl⟩), (projFun_eq hEL e hl hc h).symm⟩

theorem not_transitive_of_separated_proj {P N : Subgroup Q} (hPL : P ≤ Lb)
    (hEL : E ≤ Lb ⊔ Subgroup.centralizer (Lb : Set Q))
    (hNLb : N ≤ Subgroup.normalizer (Lb : Set Q)) (hNP : N ≤ Subgroup.normalizer (P : Set Q))
    (hsep : ∃ e₁ e₂ : ↥((P.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb))),
      (e₁ : ↥Lb ⧸ Subgroup.center ↥Lb) ∈ (projHom hEL).range ∧
      (e₂ : ↥Lb ⧸ Subgroup.center ↥Lb) ∈ (projHom hEL).range ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧
      ∀ φ : ↥((P.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb))) ≃*
        ↥((P.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb))), φ e₁ ≠ e₂) :
    ¬ TransitiveOnNonidentity N E := by
  intro htr
  set ρ := QuotientGroup.mk' (Subgroup.center ↥Lb)
  set Jim : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb) := (P.subgroupOf Lb).map ρ
  obtain ⟨e₁, e₂, h₁, h₂, hn₁, hn₂, hφ⟩ := hsep
  obtain ⟨a₁, ha₁⟩ := MonoidHom.mem_range.mp h₁
  obtain ⟨a₂, ha₂⟩ := MonoidHom.mem_range.mp h₂
  have hu₁ : (a₁ : Q) ≠ 1 := fun h => hn₁ (by
    apply Subtype.ext
    rw [← ha₁, show a₁ = 1 from Subtype.ext h, map_one]
    rfl)
  have hu₂ : (a₂ : Q) ≠ 1 := fun h => hn₂ (by
    apply Subtype.ext
    rw [← ha₂, show a₂ = 1 from Subtype.ext h, map_one]
    rfl)
  obtain ⟨n, hn, hn12⟩ := htr _ a₁.2 _ a₂.2 hu₁ hu₂
  have hnLb : n ∈ Subgroup.normalizer (Lb : Set Q) := hNLb hn
  have hnLb' : n⁻¹ ∈ Subgroup.normalizer (Lb : Set Q) := hNLb (N.inv_mem hn)
  obtain ⟨ψ, hψ⟩ := exists_inducedAut hnLb
  obtain ⟨ψ', hψ'⟩ := exists_inducedAut hnLb'
  have hψρ : ∀ y : ↥Lb, ψ (ρ y) = ρ (conjOnNormalizer Lb n hnLb y) := hψ
  have hψρ' : ∀ y : ↥Lb, ψ' (ρ y) = ρ (conjOnNormalizer Lb n⁻¹ hnLb' y) := hψ'
  have hPn : ∀ y : ↥Lb, y ∈ P.subgroupOf Lb → conjOnNormalizer Lb n hnLb y ∈ P.subgroupOf Lb :=
    fun y hy => Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp (hNP hn) y).mp (Subgroup.mem_subgroupOf.mp hy))
  have hPn' : ∀ y : ↥Lb, y ∈ P.subgroupOf Lb →
      conjOnNormalizer Lb n⁻¹ hnLb' y ∈ P.subgroupOf Lb :=
    fun y hy => Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp (hNP (N.inv_mem hn)) y).mp
        (Subgroup.mem_subgroupOf.mp hy))
  have hst1 : ∀ g ∈ Jim, ψ g ∈ Jim := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hψρ]
    exact ⟨_, hPn y hy, rfl⟩
  have hψψ' : ∀ g, ψ (ψ' g) = g := by
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    change ψ (ψ' (ρ y)) = ρ y
    rw [hψρ', hψρ]
    congr 1
    apply Subtype.ext
    show n * (n⁻¹ * (y : Q) * n⁻¹⁻¹) * n⁻¹ = y
    group
  have hψ'symm : ∀ g, ψ.symm g = ψ' g := fun g =>
    (ψ.symm_apply_eq.mpr (hψψ' g).symm)
  have hst2 : ∀ g ∈ Jim, ψ.symm g ∈ Jim := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hψ'symm]
    change ψ' (ρ y) ∈ Jim
    rw [hψρ']
    exact ⟨_, hPn' y hy, rfl⟩
  obtain ⟨l, hl, c, hc, h⟩ := exists_mul_of_mem_sup_centralizer (hEL a₁.2)
  have he₁ : (e₁ : ↥Lb ⧸ Subgroup.center ↥Lb) = ρ ⟨l, hl⟩ := by
    rw [← ha₁, projHom_apply]
    exact projFun_eq hEL a₁ hl hc h
  have he₂ : (e₂ : ↥Lb ⧸ Subgroup.center ↥Lb) = ρ (conjOnNormalizer Lb n hnLb ⟨l, hl⟩) := by
    rw [← ha₂, projHom_apply]
    refine projFun_eq hEL a₂ (conjOnNormalizer Lb n hnLb ⟨l, hl⟩).2
      (conj_mem_centralizer hnLb hc) ?_
    rw [← hn12, ← h]
    show n * l * n⁻¹ * (n * c * n⁻¹) = n * (l * c) * n⁻¹
    group
  refine hφ (autOfStab ψ Jim hst1 hst2) (Subtype.ext ?_)
  rw [autOfStab_apply, he₁, he₂]
  exact hψρ ⟨l, hl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.E9Transitive
