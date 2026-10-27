module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterFusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.TransferFix
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.ABGLocalTools

@[expose] def OutTwo (Y : Type) [Group Y] : Prop :=
  ∀ α β : MulAut Y, (∃ l : Y, α = MulAut.conj l) ∨ (∃ l : Y, β = MulAut.conj l) ∨
    ∃ l : Y, α⁻¹ * β = MulAut.conj l

@[expose] def autTransport {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') :
    MulAut Y' ≃* MulAut Y :=
  MulAut.congr e.symm

theorem autTransport_apply {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (a : MulAut Y')
    (y : Y) : autTransport e a y = e.symm (a (e y)) := rfl

theorem autTransport_conj {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (l : Y) :
    autTransport e (MulAut.conj (e l)) = MulAut.conj l := by
  ext y
  simp [autTransport_apply, MulAut.conj_apply]

theorem OutTwo.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (h : OutTwo Y) :
    OutTwo Y' := by
  intro α β
  have key : ∀ γ : MulAut Y', (∃ l : Y, autTransport e γ = MulAut.conj l) →
      ∃ l : Y', γ = MulAut.conj l := by
    rintro γ ⟨l, hl⟩
    refine ⟨e l, (autTransport e).injective ?_⟩
    rw [hl, autTransport_conj]
  rcases h (autTransport e α) (autTransport e β) with h1 | h1 | h1
  · exact Or.inl (key α h1)
  · exact Or.inr (Or.inl (key β h1))
  · refine Or.inr (Or.inr (key (α⁻¹ * β) ?_))
    rwa [map_mul, map_inv]

@[expose] def TwoCentralAut {Y : Type} [Group Y] (σ : MulAut Y) : Prop :=
  2 ^ (Nat.card Y).factorization 2 ∣ Nat.card (fixSubgroup σ)

theorem card_fixSubgroup_autTransport {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (σ : MulAut Y') : Nat.card (fixSubgroup (autTransport e σ)) = Nat.card (fixSubgroup σ) := by
  refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun y => ?_)
  show autTransport e σ y = y ↔ σ (e y) = e y
  rw [autTransport_apply]
  exact MulEquiv.symm_apply_eq e

theorem twoCentralAut_autTransport_iff {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (σ : MulAut Y') : TwoCentralAut (autTransport e σ) ↔ TwoCentralAut σ := by
  unfold TwoCentralAut
  rw [card_fixSubgroup_autTransport, Nat.card_congr e.toEquiv]

@[expose] def AutCenterCond2 (Y : Type) [Group Y] : Prop :=
  ∀ ν σ : MulAut Y, ν * ν = 1 → σ * σ = 1 → ν * σ = σ * ν → (∀ y : Y, ν y = y → σ y = y) →
    σ = 1 ∨ σ = ν ∨ ¬ TwoCentralAut σ

theorem AutCenterCond2.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : AutCenterCond2 Y) : AutCenterCond2 Y' := by
  intro ν σ hν hσ hνσ hfix
  have h1 := h (autTransport e ν) (autTransport e σ) (by rw [← map_mul, hν, map_one])
    (by rw [← map_mul, hσ, map_one]) (by rw [← map_mul, ← map_mul, hνσ]) (by
      intro y hy
      rw [autTransport_apply] at hy ⊢
      have h2 : ν (e y) = e y := by
        have := congrArg e hy
        rwa [MulEquiv.apply_symm_apply] at this
      rw [hfix _ h2, MulEquiv.symm_apply_apply])
  rcases h1 with h1 | h1 | h1
  · exact Or.inl ((autTransport e).injective (h1.trans (map_one _).symm))
  · exact Or.inr (Or.inl ((autTransport e).injective h1))
  · exact Or.inr (Or.inr fun h' => h1 ((twoCentralAut_autTransport_iff e σ).2 h'))

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {t u : G}

omit [Finite G] in
theorem commutator_mem_of_outTwo (hCt : centralizer (L : Set G) = zpowers t)
    (hMN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) (hout : OutTwo ↥L) :
    ∀ a ∈ centralizer ({t} : Set G), ∀ b ∈ centralizer ({t} : Set G),
      a * b * a⁻¹ * b⁻¹ ∈ L := by
  have hbL : ∀ b ∈ centralizer ({t} : Set G), ∀ x ∈ L, b * x * b⁻¹ ∈ L := fun b hb x hx =>
    (mem_normalizer_iff.1 (hMN hb) x).1 hx
  have key : ∀ a (ha : a ∈ centralizer ({t} : Set G)),
      (∃ l : L, L.normalizerMonoidHom ⟨a, hMN ha⟩ = MulAut.conj l) →
      ∀ b ∈ centralizer ({t} : Set G), a * b * a⁻¹ * b⁻¹ ∈ L := by
    rintro a ha ⟨l, hl⟩ b hb
    have hsup : a ∈ L ⊔ centralizer (L : Set G) :=
      mem_sup_centralizer_iff.2 ⟨l, l.2, (normalizerMonoidHom_eq_conj_iff (hMN ha) l).1 hl⟩
    obtain ⟨l', hl', c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer le_rfl hsup
    rw [hCt] at hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    have hbt : b * t = t * b := mem_centralizer_singleton_iff.1 hb
    have hbk : b * t ^ k = t ^ k * b := (Commute.zpow_right (show Commute b t from hbt) k).eq
    have h1 : l' * t ^ k * b * (l' * t ^ k)⁻¹ * b⁻¹ = l' * (b * l'⁻¹ * b⁻¹) := by
      calc l' * t ^ k * b * (l' * t ^ k)⁻¹ * b⁻¹ = l' * (t ^ k * b * (t ^ k)⁻¹) * l'⁻¹ * b⁻¹ := by
            group
        _ = l' * (b * l'⁻¹ * b⁻¹) := by rw [← hbk]; group
    rw [h1]
    exact L.mul_mem hl' (hbL b hb _ (L.inv_mem hl'))
  intro a ha b hb
  have hab : a⁻¹ * b ∈ centralizer ({t} : Set G) :=
    (centralizer ({t} : Set G)).mul_mem (inv_mem ha) hb
  rcases hout (L.normalizerMonoidHom ⟨a, hMN ha⟩) (L.normalizerMonoidHom ⟨b, hMN hb⟩) with
    h1 | h1 | h1
  · exact key a ha h1 b hb
  · have h2 := L.inv_mem (key b hb h1 a ha)
    have h3 : (b * a * b⁻¹ * a⁻¹)⁻¹ = a * b * a⁻¹ * b⁻¹ := by group
    rwa [h3] at h2
  · obtain ⟨l, hl⟩ := h1
    have h3 : L.normalizerMonoidHom ⟨a⁻¹ * b, hMN hab⟩ = MulAut.conj l := by
      rw [← hl]
      have : (⟨a⁻¹ * b, hMN hab⟩ : normalizer (L : Set G)) =
          (⟨a, hMN ha⟩ : normalizer (L : Set G))⁻¹ * ⟨b, hMN hb⟩ := Subtype.ext rfl
      rw [this, map_mul, map_inv]
    have h4 := hbL a ha _ (key _ hab ⟨l, h3⟩ a ha)
    have h5 : a * ((a⁻¹ * b) * a * (a⁻¹ * b)⁻¹ * a⁻¹) * a⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ := by group
    rw [h5] at h4
    exact (inv_mem_iff).1 h4

theorem refute_of_outTwo (hStd : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (h : SolomonHyp G L K t u) (hacc : AutCenterCond2 ↥L) (hout : OutTwo ↥L)
    (hu : twoAdic (L ⊓ centralizer ({u} : Set G)) < twoAdic L) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  have := h.simpleL
  have ht2 := h.t_order
  have htt := mul_self_eq_one_of_orderOf_eq_two ht2
  have hZ : center L = ⊥ := center_eq_bot_of_simple_nonabelian h.nonabelianL
  have htL : t ∉ L := not_mem_of_center_eq_bot h.t_mem ht2 hZ
  have hCt := centralizer_eq_zpowers_of_hyp38 hStd hS h
  have hMN := hStd.centralizer_le_normalizer h.t_mem ht2
  set M : Subgroup G := centralizer ({t} : Set G) with hM
  have htM : t ∈ M := mem_centralizer_singleton_iff.2 rfl
  have huM : u ∈ M := mem_centralizer_singleton_iff.2 h.u_comm_t
  have hLM : L ≤ M := fun x hx =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 h.t_mem x hx)
  have hcomm := commutator_mem_of_outTwo hCt hMN hout
  have hψ : (Abelianization.of (⟨t, htM⟩ : M)) ≠ 1 := by
    intro h1
    have h2 : (⟨t, htM⟩ : M) ∈ commutator M := by
      rw [← Abelianization.ker_of]
      exact h1
    have h3 : commutator M ≤ L.subgroupOf M := by
      rw [commutator_def]
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      exact hcomm a a.2 b b.2
    exact htL (h3 h2)
  obtain ⟨P, hPS, huP, htP⟩ : ∃ P : Subgroup G, IsSylowOf 2 P M ∧ u ∈ P ∧ t ∈ P := by
    have hu2 : IsPGroup 2 (zpowers (⟨u, huM⟩ : M)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, h.u_order, pow_one]
    have htcen : (⟨t, htM⟩ : M) ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
    have : (zpowers (⟨t, htM⟩ : M)).Normal :=
      Subgroup.normal_of_le_center (zpowers_le.2 htcen)
    have ht2' : IsPGroup 2 (zpowers (⟨t, htM⟩ : M)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht2, pow_one]
    obtain ⟨Q, hQ⟩ := hu2.exists_le_sylow
    have htQ := ht2'.le_sylow_of_normal Q
    exact ⟨Q.map M.subtype, ⟨Q, rfl⟩, ⟨_, hQ (mem_zpowers _), rfl⟩,
      ⟨_, htQ (mem_zpowers _), rfl⟩⟩
  have hPt : ∀ p ∈ P, p * t = t * p := fun p hp => mem_centralizer_singleton_iff.1 (hPS.le hp)
  obtain ⟨g, hgt, hgP⟩ := McLStd.exists_conj_ne_centralizing h.nonabelian htt hPS.isPGroup htP hPt
    (Abelianization.of : M →* Abelianization M) hψ
  have hft : g * t * g⁻¹ ∈ fusedSet u t :=
    ⟨isConj_iff.2 ⟨g, rfl⟩, (hgP u huP).symm, (hgP t htP).symm⟩
  obtain ⟨u₁, hN, ν, σ, hu₁, hu₁₂, hu₁t, hν, hσ, hνν, hσσ, hνσ, hfix, h1, h2⟩ :=
    exists_fusion_pair hStd hS h hft rfl
  rcases hacc ν σ hνν hσσ hνσ hfix with h3 | h3 | h3
  · exact hgt (h1 h3)
  ·
    have h4 : g * t * g⁻¹ = u * t := h2 h3
    have hPu : ∀ p ∈ P, p * u = u * p := by
      intro p hp
      have e1 := hgP p hp
      rw [h4] at e1
      have e2 := hPt p hp
      apply mul_right_cancel (b := t)
      calc p * u * t = p * (u * t) := by group
        _ = (u * t) * p := e1
        _ = u * (t * p) := by group
        _ = u * (p * t) := by rw [e2]
        _ = u * p * t := by group
    have hS' : IsSylowOf 2 (P ⊓ L) L := hPS.inf_of_le_normalizer hLM hMN
    have hle : P ⊓ L ≤ L ⊓ centralizer ({u} : Set G) := fun x hx =>
      ⟨hx.2, mem_centralizer_singleton_iff.2 (hPu x hx.1)⟩
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hS'.card_eq] at hdvd
    have hpos : Nat.card ↥(L ⊓ centralizer ({u} : Set G)) ≠ 0 := Nat.card_pos.ne'
    exact absurd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).1 hdvd)
      (not_le.2 hu)
  ·
    exfalso
    apply h3
    set P₂ : Subgroup G := P.map (MulAut.conj g⁻¹).toMonoidHom with hP₂
    have hP₂mem : ∀ x ∈ P₂, ∃ p ∈ P, x = g⁻¹ * p * g := by
      rintro x ⟨p, hp, rfl⟩
      exact ⟨p, hp, by simp⟩
    have hP₂M : P₂ ≤ M := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := hP₂mem x hx
      refine mem_centralizer_singleton_iff.2 ?_
      have e1 := hgP p hp
      calc g⁻¹ * p * g * t = g⁻¹ * (p * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * p) * g := by rw [e1]
        _ = t * (g⁻¹ * p * g) := by group
    have hP₂S : IsSylowOf 2 P₂ M := by
      refine isSylowOf_of_card hP₂M ?_
      rw [hP₂, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hPS.card_eq]
    have hS₂ : IsSylowOf 2 (P₂ ⊓ L) L := hP₂S.inf_of_le_normalizer hLM hMN
    have hle : (P₂ ⊓ L).subgroupOf L ≤ fixSubgroup σ := by
      intro x hx
      obtain ⟨p, hp, hxp⟩ := hP₂mem x hx.1
      have hx' : ((x : L) : G) = g⁻¹ * p * g := hxp
      show σ x = x
      apply Subtype.ext
      rw [hσ, hx']
      have e1 := hPt p hp
      calc g⁻¹ * t * g * (g⁻¹ * p * g) * (g⁻¹ * t * g)⁻¹ = g⁻¹ * (t * p * t⁻¹) * g := by group
        _ = g⁻¹ * p * g := by rw [← e1]; group
    have hcard : Nat.card ((P₂ ⊓ L).subgroupOf L) = Nat.card (P₂ ⊓ L : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have := Subgroup.card_dvd_of_le hle
    rw [hcard, hS₂.card_eq] at this
    exact this

end CFSG.EvenSporadicStandard.Solomon78
