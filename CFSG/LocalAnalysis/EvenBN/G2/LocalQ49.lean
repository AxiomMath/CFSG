module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalQ46

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Generic

variable {G : Type*} [Group G]

theorem q49_crossed_mem_of_mem_normalizer {t : G} (htt : t * t = 1) {R S : Subgroup G}
    (hR : S ⊔ zpowers t = R) (htS : t ∈ normalizer (S : Set G)) (htnS : t ∉ S) {x : G}
    (hxR : x ∈ normalizer (R : Set G)) (hxS : x ∈ normalizer (S : Set G)) :
    t * x * t * x⁻¹ ∈ S := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htR : t ∈ R := hR ▸ mem_sup_right (mem_zpowers t)
  have h1 : x * t * x⁻¹ ∈ S ⊔ zpowers t := hR ▸ (mem_normalizer_iff.1 hxR t).1 htR
  rcases (mem_sup_zpowers_iff_of htt htS).1 h1 with h2 | ⟨a, ha, e⟩
  · exact absurd ((mem_normalizer_iff.1 hxS t).2 h2) htnS
  · have e2 : t * x * t * x⁻¹ = t * a * t⁻¹ := by
      calc t * x * t * x⁻¹ = t * (x * t * x⁻¹) := by group
        _ = t * (a * t) := by rw [e]
        _ = t * a * t⁻¹ := by rw [htinv]; group
    rw [e2]
    exact (mem_normalizer_iff.1 htS a).1 ha

theorem q49_crossed_mul_mem {t : G} (htt : t * t = 1) {S₅ F₅ : Subgroup G} {x y : G}
    (hx : ∀ s ∈ S₅, x * s * x⁻¹ * s⁻¹ ∈ F₅) (hy : t * y * t * y⁻¹ ∈ S₅) :
    ∃ f ∈ F₅, t * (x * y) * t * (x * y)⁻¹ =
      (t * x * t * x⁻¹) * (t * y * t * y⁻¹) * f := by
  refine ⟨(t * y * t * y⁻¹)⁻¹ * x * (t * y * t * y⁻¹) * x⁻¹, ?_, ?_⟩
  · have := inv_mem (hx _ (inv_mem hy))
    rwa [show (x * (t * y * t * y⁻¹)⁻¹ * x⁻¹ * (t * y * t * y⁻¹)⁻¹⁻¹)⁻¹ =
      (t * y * t * y⁻¹)⁻¹ * x * (t * y * t * y⁻¹) * x⁻¹ by group] at this
  · calc t * (x * y) * t * (x * y)⁻¹ = t * x * (t * t) * y * t * y⁻¹ * x⁻¹ := by
          rw [htt, mul_one]; group
      _ = _ := by group

theorem q49_exists_hom_crossed {V S S₅ F₅ F : Subgroup G} (κ : G → G)
    (hFn : (F.subgroupOf S).Normal) (hSF₅ : S ≤ normalizer (F₅ : Set G))
    (hS₅ : ∀ s ∈ S₅, ∃ σ ∈ S, ∃ f ∈ F₅, s = σ * f) (hinf : S ⊓ F₅ = F)
    (hκ : ∀ x ∈ V, κ x ∈ S₅) (hκ1 : κ 1 = 1)
    (hmul : ∀ x ∈ V, ∀ y ∈ V, ∃ f ∈ F₅, κ (x * y) = κ x * κ y * f) :
    ∃ Ψ : V →* S ⧸ F.subgroupOf S,
      (∀ (x : V) (s : S), ∀ y ∈ F₅, κ x = s * y → Ψ x = QuotientGroup.mk s) ∧
      ∀ (x : V) (s : S), Ψ x = QuotientGroup.mk s → ∃ y ∈ F₅, κ x = s * y := by
  haveI := hFn
  have hdec : ∀ x : V, ∃ σ ∈ S, ∃ f ∈ F₅, κ (x : G) = σ * f := fun x => hS₅ _ (hκ x x.2)
  choose σ hσ f hf hκx using hdec
  have huniq : ∀ {σ₁ σ₂ f₁ f₂ : G}, σ₁ ∈ S → σ₂ ∈ S → f₁ ∈ F₅ → f₂ ∈ F₅ →
      σ₁ * f₁ = σ₂ * f₂ → σ₁⁻¹ * σ₂ ∈ F := by
    intro σ₁ σ₂ f₁ f₂ h1 h2 hf1 hf2 e
    rw [← hinf]
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem h1) h2, ?_⟩
    have : σ₁⁻¹ * σ₂ = f₁ * f₂⁻¹ := by
      calc σ₁⁻¹ * σ₂ = σ₁⁻¹ * (σ₂ * f₂) * f₂⁻¹ := by group
        _ = σ₁⁻¹ * (σ₁ * f₁) * f₂⁻¹ := by rw [e]
        _ = f₁ * f₂⁻¹ := by group
    rw [this]
    exact mul_mem hf1 (inv_mem hf2)
  have hFF₅ : F ≤ F₅ := hinf ▸ inf_le_right
  have hmk : ∀ (a b : S), a⁻¹ * b ∈ F.subgroupOf S →
      (QuotientGroup.mk a : S ⧸ F.subgroupOf S) = QuotientGroup.mk b := fun a b hab =>
    QuotientGroup.eq.2 hab
  refine ⟨{ toFun := fun x => QuotientGroup.mk ⟨σ x, hσ x⟩
            map_one' := ?_
            map_mul' := ?_ }, ?_, ?_⟩
  · show (QuotientGroup.mk ⟨σ 1, hσ 1⟩ : S ⧸ F.subgroupOf S) = 1
    refine (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 ?_)
    have e : σ 1 * f 1 = 1 * 1 := by
      rw [← hκx 1]
      show κ ((1 : V) : G) = 1 * 1
      rw [Subgroup.coe_one, hκ1, mul_one]
    have := huniq (hσ 1) (one_mem S) (hf 1) (one_mem F₅) e
    rw [mul_one] at this
    exact inv_mem_iff.1 this
  · intro x y
    show (QuotientGroup.mk ⟨σ (x * y), hσ (x * y)⟩ : S ⧸ F.subgroupOf S) =
      QuotientGroup.mk ⟨σ x, hσ x⟩ * QuotientGroup.mk ⟨σ y, hσ y⟩
    rw [← QuotientGroup.mk_mul]
    refine hmk _ _ (mem_subgroupOf.2 ?_)
    obtain ⟨f₀, hf₀, e⟩ := hmul x x.2 y y.2
    have hconj : (σ y)⁻¹ * f x * (σ y)⁻¹⁻¹ ∈ F₅ :=
      (mem_normalizer_iff.1 (hSF₅ (inv_mem (hσ y))) (f x)).1 (hf x)
    have e2 : σ (x * y) * f (x * y) = (σ x * σ y) * (((σ y)⁻¹ * f x * (σ y)⁻¹⁻¹) * f y * f₀) := by
      have h1 := hκx (x * y)
      rw [Subgroup.coe_mul, e, hκx x, hκx y] at h1
      rw [← h1]
      group
    have := huniq (hσ (x * y)) (mul_mem (hσ x) (hσ y)) (hf (x * y))
      (mul_mem (mul_mem hconj (hf y)) hf₀) e2
    exact this
  · intro x s y hy e
    refine hmk _ _ (mem_subgroupOf.2 ?_)
    exact huniq (hσ x) s.2 (hf x) hy (by rw [← hκx x, e])
  · intro x s hxs
    have h1 : (σ x)⁻¹ * (s : G) ∈ F := mem_subgroupOf.1 (QuotientGroup.eq.1 hxs)
    refine ⟨(s : G)⁻¹ * σ x * f x, ?_, ?_⟩
    · have h2 : (s : G)⁻¹ * σ x ∈ F := by
        have := inv_mem h1
        rwa [mul_inv_rev, inv_inv] at this
      exact mul_mem (hFF₅ h2) (hf x)
    · rw [hκx x]
      group

theorem q49_crossed_inv_mul_mem {t : G} (htt : t * t = 1) {F₅ : Subgroup G} {v x f : G}
    (hv : v ∈ normalizer (F₅ : Set G)) (hf : f ∈ F₅)
    (e : t * v * t * v⁻¹ = (t * x * t * x⁻¹) * f) :
    t * (v⁻¹ * x) * t * (v⁻¹ * x)⁻¹ ∈ F₅ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have e2 : t * (v⁻¹ * x) * t * (v⁻¹ * x)⁻¹ = v⁻¹ * f⁻¹ * v := by
    have h1 : t * (v⁻¹ * x) * t * (v⁻¹ * x)⁻¹ =
        t * v⁻¹ * t * v⁻¹⁻¹ * (v⁻¹ * (t * x * t * x⁻¹) * v⁻¹⁻¹) := by
      calc t * (v⁻¹ * x) * t * (v⁻¹ * x)⁻¹ = t * v⁻¹ * (t * t) * x * t * x⁻¹ * v := by
            rw [htt, mul_one]; group
        _ = _ := by group
    have h2 : t * v⁻¹ * t * v⁻¹⁻¹ = v⁻¹ * (t * v * t * v⁻¹)⁻¹ * v := by
      calc t * v⁻¹ * t * v⁻¹⁻¹ = t⁻¹ * v⁻¹ * t⁻¹ * v := by rw [htinv, inv_inv]
        _ = _ := by group
    rw [h1, h2, e]
    group
  rw [e2]
  have := (mem_normalizer_iff.1 (inv_mem hv) f⁻¹).1 (inv_mem hf)
  simpa [mul_assoc] using this

theorem q49_inf_sup_zpowers_eq {P R Q : Subgroup G} {t : G} (hR : P ⊔ zpowers t = R)
    (htP : t ∈ normalizer (P : Set G)) (hQR : Q ≤ R) (htQ : t ∈ Q) :
    (P ⊓ Q) ⊔ zpowers t = Q := by
  refine le_antisymm (sup_le inf_le_right ((zpowers_le).2 htQ)) fun x hx => ?_
  obtain ⟨p, hp, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer ((zpowers_le).2 htP) x
    (hR ▸ hQR hx)
  have hpQ : p ∈ Q := by
    have := mul_mem hx (inv_mem ((zpowers_le).2 htQ hτ))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (mem_sup_left (Subgroup.mem_inf.2 ⟨hp, hpQ⟩)) (mem_sup_right hτ)

theorem q49_inf_eq_of_sup_zpowers {P R S : Subgroup G} {t : G} (htt : t * t = 1)
    (hS : S ⊔ zpowers t = R) (htS : t ∈ normalizer (S : Set G)) (hSP : S ≤ P) (htP : t ∉ P) :
    P ⊓ R = S := by
  refine le_antisymm (fun x hx => ?_) (le_inf hSP (hS ▸ le_sup_left))
  obtain ⟨hxP, hxR⟩ := Subgroup.mem_inf.1 hx
  rw [← hS] at hxR
  rcases (mem_sup_zpowers_iff_of htt htS).1 hxR with h1 | ⟨a, ha, rfl⟩
  · exact h1
  · exfalso
    have := mul_mem (inv_mem (hSP ha)) hxP
    rw [inv_mul_cancel_left] at this
    exact htP this

theorem q49_eq_one_or_eq_of_mem_zpowers {t c : G} (htt : t * t = 1) (hc : c ∈ zpowers t) :
    c = 1 ∨ c = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [show m + m = 2 * m by ring, zpow_mul, zpow_two, htt, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, htt, one_zpow, one_mul]

theorem q49_conj_mem {Q : Subgroup G} {a u f₀ j : G} (ha : a ∈ Q) (hf₀ : f₀ ∈ Q)
    (hjf₀ : j * f₀ * j⁻¹ ∈ Q) (hj : j ∈ normalizer (Q : Set G)) (hu : u ∈ normalizer (Q : Set G))
    (hju : j * u = u * j) : (a * u * f₀)⁻¹ * (j * (a * u * f₀) * j⁻¹) ∈ Q := by
  have hju' : j * u * j⁻¹ = u := by rw [hju]; group
  have e : (a * u * f₀)⁻¹ * (j * (a * u * f₀) * j⁻¹) =
      f₀⁻¹ * (u⁻¹ * (a⁻¹ * (j * a * j⁻¹)) * u) * (j * f₀ * j⁻¹) := by
    calc (a * u * f₀)⁻¹ * (j * (a * u * f₀) * j⁻¹) =
        f₀⁻¹ * (u⁻¹ * (a⁻¹ * (j * a * j⁻¹)) * (j * u * j⁻¹)) * (j * f₀ * j⁻¹) := by group
      _ = _ := by rw [hju']
  rw [e]
  have h1 : a⁻¹ * (j * a * j⁻¹) ∈ Q := mul_mem (inv_mem ha) ((mem_normalizer_iff.1 hj a).1 ha)
  have h2 : u⁻¹ * (a⁻¹ * (j * a * j⁻¹)) * u ∈ Q := by
    have := (mem_normalizer_iff.1 (inv_mem hu) _).1 h1
    simpa using this
  exact mul_mem (mul_mem (inv_mem hf₀) h2) hjf₀

theorem q49_crossed_inv_conj {t x j : G} (htt : t * t = 1) (hjt : j * t = t * j) :
    t * (x⁻¹ * (j * x * j⁻¹)) * t * (x⁻¹ * (j * x * j⁻¹))⁻¹ =
      x⁻¹ * ((t * x * t * x⁻¹)⁻¹ * (j * (t * x * t * x⁻¹) * j⁻¹)) * x := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hjt2 : j⁻¹ * t * j = t := by rw [mul_assoc, ← hjt, inv_mul_cancel_left]
  have hjt3 : t * j * t = j := by rw [← hjt, mul_assoc, htt, mul_one]
  have e1 : (t * x * t * x⁻¹)⁻¹ = x * t * x⁻¹ * t := by
    rw [show (t * x * t * x⁻¹)⁻¹ = x * t⁻¹ * x⁻¹ * t⁻¹ by group, htinv]
  have e2 : t * (x⁻¹ * (j * x * j⁻¹)) * t * (x⁻¹ * (j * x * j⁻¹))⁻¹ =
      t * x⁻¹ * j * x * (j⁻¹ * t * j) * x⁻¹ * j⁻¹ * x := by group
  have e3 : x⁻¹ * ((x * t * x⁻¹ * t) * (j * (t * x * t * x⁻¹) * j⁻¹)) * x =
      t * x⁻¹ * (t * j * t) * x * t * x⁻¹ * j⁻¹ * x := by group
  rw [e2, hjt2, e1, e3, hjt3]

end Generic

section GenericChar

variable {G : Type*} [Group G]

theorem q49_normalizer_le_normalizer_of_characteristic_of_le {H E : Subgroup G} (hEH : E ≤ H)
    (hc : (E.subgroupOf H).Characteristic) : normalizer (H : Set G) ≤ normalizer (E : Set G) := by
  have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (E.subgroupOf H)
  rwa [subgroupOf_map_subtype, inf_of_le_left hEH] at h1

end GenericChar

section DefsV

variable
  {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def q49_yamadaV₈ (d : G2Data L K) (t : G) : Subgroup G :=
  normalizer (yamadaR₅ d t : Set G) ⊓ centralizerModulo (yamadaF₅ d t) (yamadaS₅ d t)

end DefsV

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem q49_normalizer_yamadaR₅_le_normalizers (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    normalizer (yamadaR₅ d t : Set G) ≤ normalizer (yamadaF₅ d t : Set G) ∧
      normalizer (yamadaR₅ d t : Set G) ≤ normalizer (yamadaM₅ d t : Set G) ∧
      normalizer (yamadaR₅ d t : Set G) ≤ normalizer (yamadaD₅ d t : Set G) ∧
      normalizer (yamadaR₅ d t : Set G) ≤ normalizer (yamadaS₅ d t : Set G) := by
  obtain ⟨⟨hF, hM, hD, hS⟩, cF, cM, cD, cS⟩ := h.yamada_5_46_4 hW d hK hQ
  exact ⟨q49_normalizer_le_normalizer_of_characteristic_of_le hF cF,
    q49_normalizer_le_normalizer_of_characteristic_of_le hM cM,
    q49_normalizer_le_normalizer_of_characteristic_of_le hD cD,
    q49_normalizer_le_normalizer_of_characteristic_of_le hS cS⟩

theorem q49_normalizer_yamadaR₂_le_normalizer_yamadaR₅ (d : G2Data L K) (t : G) :
    normalizer (yamadaR₂ d t : Set G) ≤ normalizer (yamadaR₅ d t : Set G) :=
  LieType.BorelTits.le_normalizer_pCoreOf 2 _

theorem q49_centralizer_inf_normalizer_S_le_normalizer_yamadaR₅ (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤ normalizer (yamadaR₅ d t : Set G) :=
  (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD).1.trans
    (q49_normalizer_yamadaR₂_le_normalizer_yamadaR₅ d t)

theorem q49_J_le_normalizer_yamadaR₅ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.J ≤ normalizer (yamadaR₅ d t : Set G) :=
  (h.J_le_centralizer_inf_normalizer_S d).trans
    (h.q49_centralizer_inf_normalizer_S_le_normalizer_yamadaR₅ d hK hD)

theorem q49_mem_yamadaV₈ {d : G2Data L K} {x : G} :
    x ∈ q49_yamadaV₈ d t ↔ x ∈ normalizer (yamadaR₅ d t : Set G) ∧
      x ∈ normalizer (yamadaF₅ d t : Set G) ∧
        ∀ s ∈ yamadaS₅ d t, x * s * x⁻¹ * s⁻¹ ∈ yamadaF₅ d t := Iff.rfl

theorem q49_yamadaV₈_le_normalizer (d : G2Data L K) (t : G) :
    q49_yamadaV₈ d t ≤ normalizer (yamadaR₅ d t : Set G) := inf_le_left

theorem q49_normalizer_yamadaR₅_le_normalizer_yamadaV₈ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    normalizer (yamadaR₅ d t : Set G) ≤ normalizer (q49_yamadaV₈ d t : Set G) := by
  obtain ⟨hHF, -, -, hHS⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  intro g hg
  refine mem_normalizer_of_conj_mem fun v hv => ?_
  obtain ⟨hvH, hvF, hvc⟩ := q49_mem_yamadaV₈.1 hv
  refine q49_mem_yamadaV₈.2 ⟨?_, ?_, fun s hs => ?_⟩
  · exact mul_mem (mul_mem hg hvH) (inv_mem hg)
  · exact mul_mem (mul_mem (hHF hg) hvF) (inv_mem (hHF hg))
  · have hs' : g⁻¹ * s * g ∈ yamadaS₅ d t := by
      have := (mem_normalizer_iff.1 (hHS (inv_mem hg)) s).1 hs
      simpa using this
    have h1 := hvc _ hs'
    have h2 := (mem_normalizer_iff.1 (hHF hg) _).1 h1
    rwa [show g * (v * (g⁻¹ * s * g) * v⁻¹ * (g⁻¹ * s * g)⁻¹) * g⁻¹ =
      g * v * g⁻¹ * s * (g * v * g⁻¹)⁻¹ * s⁻¹ by group] at h2

theorem q49_crossed_mem_yamadaS₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ normalizer (yamadaR₅ d t : Set G)) : t * x * t * x⁻¹ ∈ yamadaS₅ d t := by
  obtain ⟨-, -, -, hHS⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  obtain ⟨hR, htS, htnS⟩ := (h.yamada_5_37_2 hW d hK hQ).2.1
  exact q49_crossed_mem_of_mem_normalizer h.t_mul_t hR htS htnS hx (hHS hx)

theorem q49_yamadaF₂_le_yamadaF₅ (d : G2Data L K) (t : G) : yamadaF₂ d t ≤ yamadaF₅ d t :=
  (le_sup_right : yamadaF₂ d t ≤ yamadaF₃ d t).trans le_sup_left

theorem q49_crossed_mem_yamadaF₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x : G}
    (hx : x ∈ yamadaR₅ d t) : t * x * t * x⁻¹ ∈ yamadaF₂ d t := by
  obtain ⟨y, hy, e⟩ := (h.yamada_5_21_3 hW d hK hD).1 x (LieType.BorelTits.pCoreOf_le 2 _ hx)
  rw [h.conj_t_eq_mul_crossed x] at e
  rwa [mul_left_cancel e]

theorem q49_yamadaS₅_facts (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.S ≤ yamadaS₅ d t ∧ d.F ≤ yamadaF₅ d t ∧ yamadaF₅ d t ≤ yamadaM₅ d t ∧
      yamadaF₅ d t ≤ yamadaD₅ d t ∧ d.M ≤ yamadaM₅ d t ∧ d.D ≤ yamadaD₅ d t ∧
      yamadaM₅ d t ≤ yamadaS₅ d t ∧ yamadaD₅ d t ≤ yamadaS₅ d t ∧
      yamadaS₅ d t ≤ yamadaM₅ d t ⊔ yamadaD₅ d t := by
  obtain ⟨⟨hS, hM, hD⟩, hSF, -, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨-, -, -, -, -, hFD, hFM, hDS, hMS, -⟩ := d.inclusions
  have hFF₅ : d.F ≤ yamadaF₅ d t := hSF ▸ inf_le_right
  have hF₅S : yamadaF₅ d t ≤ yamadaS₅ d t := hS ▸ le_sup_right
  have hSS₅ : d.S ≤ yamadaS₅ d t := hS ▸ le_sup_left
  refine ⟨hSS₅, hFF₅, hM ▸ le_sup_right, hD ▸ le_sup_right, hM ▸ le_sup_left, hD ▸ le_sup_left,
    hM ▸ sup_le (hMS.trans hSS₅) hF₅S, hD ▸ sup_le (hDS.trans hSS₅) hF₅S, ?_⟩
  rw [hS, ← (d.yamada_defs).2.2.2.2.2.2.2.2]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact (hD ▸ le_sup_left : d.D ≤ yamadaD₅ d t).trans le_sup_right
  · exact (hM ▸ le_sup_left : d.M ≤ yamadaM₅ d t).trans le_sup_left
  · exact (hM ▸ le_sup_right : yamadaF₅ d t ≤ yamadaM₅ d t).trans le_sup_left

theorem q49_yamadaS₅_le_yamadaR₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaS₅ d t ≤ yamadaR₅ d t :=
  ((h.yamada_5_37_2 hW d hK hQ).2.1).1 ▸ le_sup_left

theorem q49_t_mem_yamadaR₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    t ∈ yamadaR₅ d t :=
  ((h.yamada_5_37_2 hW d hK hQ).2.1).1 ▸ mem_sup_right (mem_zpowers t)

theorem q49_yamadaM₅_eq_rootGroup_sup (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₅ d t = d.rootGroup g2r ⊔ yamadaF₅ d t := by
  obtain ⟨⟨-, hM, -⟩, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨-, hFF₅, -⟩ := h.q49_yamadaS₅_facts hW d hK hQ
  rw [hM, ← (d.yamada_defs).2.2.2.2.2.1, sup_assoc, sup_eq_right.2 hFF₅]

theorem q49_yamadaD₅_eq_rootGroup_sup (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaD₅ d t = d.rootGroup g2a ⊔ yamadaF₅ d t := by
  obtain ⟨⟨-, -, hD⟩, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨-, hFF₅, -⟩ := h.q49_yamadaS₅_facts hW d hK hQ
  rw [hD, ← (d.yamada_defs).2.2.2.2.1, sup_assoc, sup_eq_right.2 hFF₅]

theorem q49_yamadaF₅_ne_yamadaM₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaF₅ d t ≠ yamadaM₅ d t := by
  intro he
  obtain ⟨⟨-, hM, -⟩, -, hMF, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  have hMF' : d.M ≤ d.F := hMF ▸ le_inf le_rfl (he ▸ (hM ▸ le_sup_left : d.M ≤ yamadaM₅ d t))
  have h1 := Subgroup.card_le_of_le hMF'
  rw [d.cards.2.2.2.2.2.2.1, d.cards.2.2.2.2.1] at h1
  have : Nat.card K ^ 4 < Nat.card K ^ 5 := Nat.pow_lt_pow_right hQ.one_lt (by norm_num)
  omega

theorem q49_yamadaF₅_ne_yamadaD₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaF₅ d t ≠ yamadaD₅ d t := by
  intro he
  obtain ⟨⟨-, -, hD⟩, -, -, hDF⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  have hDF' : d.D ≤ d.F := hDF ▸ le_inf le_rfl (he ▸ (hD ▸ le_sup_left : d.D ≤ yamadaD₅ d t))
  have h1 := Subgroup.card_le_of_le hDF'
  rw [d.cards.2.2.2.2.2.1, d.cards.2.2.2.2.1] at h1
  have : Nat.card K ^ 4 < Nat.card K ^ 5 := Nat.pow_lt_pow_right hQ.one_lt (by norm_num)
  omega

theorem q49_eq_or_eq_of_le_yamadaM₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {A : Subgroup G}
    (hFA : yamadaF₅ d t ≤ A) (hAM : A ≤ yamadaM₅ d t) (hJA : d.J ≤ normalizer (A : Set G)) :
    A = yamadaF₅ d t ∨ A = yamadaM₅ d t := by
  have hD := hQ.doubling
  obtain ⟨hHF, -, -, -⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  obtain ⟨hSS₅, -⟩ := h.q49_yamadaS₅_facts hW d hK hQ
  obtain ⟨-, -, -, -, -, -, -, hDS, hMS, -⟩ := d.inclusions
  have hM₅ := h.q49_yamadaM₅_eq_rootGroup_sup hW d hK hQ
  have hJJ : d.Ji 3 ≤ d.J := d.image_mono inf_le_left
  have hJF : d.J ≤ normalizer (yamadaF₅ d t : Set G) :=
    (h.q49_J_le_normalizer_yamadaR₅ d hK hD).trans hHF
  have hAS : d.rootGroup g2r ≤ d.S :=
    (le_sup_left.trans (d.yamada_defs).2.2.2.2.2.1.le).trans hMS
  have hSF : d.S ≤ normalizer (yamadaF₅ d t : Set G) :=
    (hSS₅.trans (h.q49_yamadaS₅_le_yamadaR₅ hW d hK hQ)).trans
      (Subgroup.le_normalizer.trans hHF)
  obtain ⟨-, htr⟩ := (d.yamada_3_9_2_G (i := 3) (k := 2) (by decide)).2 (Or.inr (by decide))
  rw [hM₅] at hAM ⊢
  exact eq_or_eq_of_transitive (fun x hx => hSF (hAS hx))
    (hJJ.trans (J_le_normalizer_rootGroup d isRoot_g2r)) (hJJ.trans hJF) htr hFA hAM
    (hJJ.trans hJA)

theorem q49_eq_or_eq_of_le_yamadaD₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {A : Subgroup G}
    (hFA : yamadaF₅ d t ≤ A) (hAD : A ≤ yamadaD₅ d t) (hJA : d.J ≤ normalizer (A : Set G)) :
    A = yamadaF₅ d t ∨ A = yamadaD₅ d t := by
  have hD := hQ.doubling
  obtain ⟨hHF, -, -, -⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  obtain ⟨hSS₅, -⟩ := h.q49_yamadaS₅_facts hW d hK hQ
  obtain ⟨-, -, -, -, -, -, -, hDS, hMS, -⟩ := d.inclusions
  have hD₅ := h.q49_yamadaD₅_eq_rootGroup_sup hW d hK hQ
  have hJJ : d.Ji 2 ≤ d.J := d.image_mono inf_le_left
  have hJF : d.J ≤ normalizer (yamadaF₅ d t : Set G) :=
    (h.q49_J_le_normalizer_yamadaR₅ d hK hD).trans hHF
  have hAS : d.rootGroup g2a ≤ d.S :=
    (le_sup_left.trans (d.yamada_defs).2.2.2.2.1.le).trans hDS
  have hSF : d.S ≤ normalizer (yamadaF₅ d t : Set G) :=
    (hSS₅.trans (h.q49_yamadaS₅_le_yamadaR₅ hW d hK hQ)).trans
      (Subgroup.le_normalizer.trans hHF)
  obtain ⟨-, htr⟩ := (d.yamada_3_9_2_G (i := 2) (k := 3) (by decide)).2 (Or.inr (by decide))
  rw [hD₅] at hAD ⊢
  exact eq_or_eq_of_transitive (fun x hx => hSF (hAS hx))
    (hJJ.trans (J_le_normalizer_rootGroup d isRoot_g2a)) (hJJ.trans hJF) htr hFA hAD
    (hJJ.trans hJA)

theorem q49_commutator_mem_yamadaF₅_of_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {P : Subgroup G}
    (hP2 : IsPGroup 2 P) (hS₅P : yamadaS₅ d t ≤ P) (hPH : P ≤ normalizer (yamadaR₅ d t : Set G))
    (hJP : d.J ≤ normalizer (P : Set G)) :
    ∀ x ∈ P, ∀ s ∈ yamadaS₅ d t, x * s * x⁻¹ * s⁻¹ ∈ yamadaF₅ d t := by
  have hD := hQ.doubling
  obtain ⟨hHF, hHM, hHD, -⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  obtain ⟨-, -, hF₅M, hF₅D, -, -, hM₅S, hD₅S, hS₅MD⟩ := h.q49_yamadaS₅_facts hW d hK hQ
  have hJH := h.q49_J_le_normalizer_yamadaR₅ d hK hD
  have hM := commutator_le_of_irreducible hP2 hF₅M (hM₅S.trans hS₅P) (hPH.trans hHF)
    (hPH.trans hHM) (le_inf (le_inf hJP (hJH.trans hHM)) (hJH.trans hHF))
    (fun A hFA hAM hJA => h.q49_eq_or_eq_of_le_yamadaM₅ hW d hK hQ hFA hAM hJA)
    (h.q49_yamadaF₅_ne_yamadaM₅ hW d hK hQ)
  have hDD := commutator_le_of_irreducible hP2 hF₅D (hD₅S.trans hS₅P) (hPH.trans hHF)
    (hPH.trans hHD) (le_inf (le_inf hJP (hJH.trans hHD)) (hJH.trans hHF))
    (fun A hFA hAD hJA => h.q49_eq_or_eq_of_le_yamadaD₅ hW d hK hQ hFA hAD hJA)
    (h.q49_yamadaF₅_ne_yamadaD₅ hW d hK hQ)
  have hle : yamadaM₅ d t ⊔ yamadaD₅ d t ≤ centralizerModulo (yamadaF₅ d t) P := by
    refine sup_le (fun m hm => ?_) (fun m hm => ?_)
    · exact ⟨(hPH.trans hHF) (hS₅P (hM₅S hm)), hM m hm⟩
    · exact ⟨(hPH.trans hHF) (hS₅P (hD₅S hm)), hDD m hm⟩
  intro x hx s hs
  have := (hle (hS₅MD hs)).2 x hx
  have h2 := inv_mem this
  rwa [show (s * x * s⁻¹ * x⁻¹)⁻¹ = x * s * x⁻¹ * s⁻¹ by group] at h2

theorem q49_J_le_normalizer_yamadaR₆ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.J ≤ normalizer (yamadaR₆ d t : Set G) := fun _ hj =>
  Common.mem_normalizer_sup
    (le_normalizer_yamadaL₆ d t (h.J_le_normalizer_yamadaL₂ d hK hD hj))
    (h.J_le_centralizer_inf_normalizer_S d hj).2

theorem q49_yamadaR₅_le_yamadaR₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₅ d t ≤ yamadaR₇ d t := by
  rw [h.yamada_5_27_3 hW d hK hD]
  exact inf_le_left

theorem q49_yamadaR₇_le_normalizer_yamadaR₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₇ d t ≤ normalizer (yamadaR₅ d t : Set G) := by
  rw [h.yamada_5_27_3 hW d hK hD]
  exact h.yamadaRstar_le_normalizer_yamadaR₅star d hK hD

theorem q49_isPGroup_yamadaR₇ (h : Setup G L f t) (d : G2Data L K) : IsPGroup 2 (yamadaR₇ d t) :=
  h.isPGroup_yamadaRstar d

theorem q49_centralizer_inf_normalizer_S_le_normalizer_yamadaR₇ (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤ normalizer (yamadaR₇ d t : Set G) :=
  fun _ hc => Common.mem_normalizer_sup (LieType.BorelTits.le_normalizer_pCoreOf 2 _
    ((h.centralizer_inf_normalizer_S_le d hK hD).1 hc)) (Subgroup.mem_inf.1 hc).2

theorem q49_J_le_normalizer_yamadaR₇ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.J ≤ normalizer (yamadaR₇ d t : Set G) :=
  (h.J_le_centralizer_inf_normalizer_S d).trans
    (h.q49_centralizer_inf_normalizer_S_le_normalizer_yamadaR₇ d hK hD)

theorem q49_commutator_mem_yamadaF₂_of_mem_yamadaR₅ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∀ x ∈ yamadaR₅ d t, ∀ y ∈ yamadaR₅ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaF₂ d t := by
  have hD := hQ.doubling
  obtain ⟨hRE, hEF, -⟩ := h.normalizer_yamadaR₂_le d hK hD
  have hR₅F₂N : yamadaR₅ d t ≤ normalizer (yamadaF₂ d t : Set G) :=
    (LieType.BorelTits.pCoreOf_le 2 _).trans (hRE.trans hEF)
  exact comm_mem_of_mul_self_mem hR₅F₂N fun x hx => h.mul_self_mem_yamadaF₂ hW d hK hQ hx

theorem q49_yamadaR₅_le_yamadaV₈ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₅ d t ≤ q49_yamadaV₈ d t := by
  obtain ⟨hHF, -, -, -⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  intro x hx
  exact q49_mem_yamadaV₈.2 ⟨Subgroup.le_normalizer hx, hHF (Subgroup.le_normalizer hx),
    fun s hs => (q49_yamadaF₂_le_yamadaF₅ d t)
      (h.q49_commutator_mem_yamadaF₂_of_mem_yamadaR₅ hW d hK hQ x hx s
        (h.q49_yamadaS₅_le_yamadaR₅ hW d hK hQ hs))⟩

theorem q49_yamadaR₆_le_yamadaV₈ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₆ d t ≤ q49_yamadaV₈ d t := by
  have hD := hQ.doubling
  obtain ⟨hHF, -, -, -⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  have hR₆H := (h.yamada_5_40_1 hW d hK hQ).2
  have hS₅R₆ : yamadaS₅ d t ≤ yamadaR₆ d t :=
    (h.q49_yamadaS₅_le_yamadaR₅ hW d hK hQ).trans (h.yamadaR₅_le_yamadaR₆ hW d hK hQ)
  intro x hx
  exact q49_mem_yamadaV₈.2 ⟨hR₆H hx, hHF (hR₆H hx),
    h.q49_commutator_mem_yamadaF₅_of_le hW d hK hQ (h.isPGroup_yamadaR₆ d) hS₅R₆ hR₆H
      (h.q49_J_le_normalizer_yamadaR₆ d hK hD) x hx⟩

theorem q49_yamadaR₇_le_yamadaV₈ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₇ d t ≤ q49_yamadaV₈ d t := by
  have hD := hQ.doubling
  obtain ⟨hHF, -, -, -⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  have hR₇H := h.q49_yamadaR₇_le_normalizer_yamadaR₅ hW d hK hD
  have hS₅R₇ : yamadaS₅ d t ≤ yamadaR₇ d t :=
    (h.q49_yamadaS₅_le_yamadaR₅ hW d hK hQ).trans (h.q49_yamadaR₅_le_yamadaR₇ hW d hK hD)
  intro x hx
  exact q49_mem_yamadaV₈.2 ⟨hR₇H hx, hHF (hR₇H hx),
    h.q49_commutator_mem_yamadaF₅_of_le hW d hK hQ (h.q49_isPGroup_yamadaR₇ d) hS₅R₇ hR₇H
      (h.q49_J_le_normalizer_yamadaR₇ d hK hD) x hx⟩

theorem q49_yamadaY₂_le_yamadaF₅ (d : G2Data L K) (t : G) : yamadaY₂ d t ≤ yamadaF₅ d t :=
  (le_sup_right : yamadaY₂ d t ≤ yamadaF₂ d t).trans (q49_yamadaF₂_le_yamadaF₅ d t)

theorem q49_yamadaM₂_le_yamadaM₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₂ d t ≤ yamadaM₅ d t := by
  obtain ⟨-, -, hF₅M, -, hMM₅, -⟩ := h.q49_yamadaS₅_facts hW d hK hQ
  exact sup_le hMM₅ ((q49_yamadaY₂_le_yamadaF₅ d t).trans hF₅M)

theorem q49_yamadaD₁_le_yamadaD₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaD₁ d t ≤ yamadaD₅ d t := by
  obtain ⟨-, -, -, hF₅D, -, hDD₅, -⟩ := h.q49_yamadaS₅_facts hW d hK hQ
  rw [hQ.doubling.yamada_5_10_1.1]
  exact sup_le hDD₅ (((yamadaU₁_le_yamadaY₂ d t).trans (q49_yamadaY₂_le_yamadaF₅ d t)).trans hF₅D)

theorem q49_crossed_mem_yamadaM₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ yamadaR₆ d t) : t * x * t * x⁻¹ ∈ yamadaM₅ d t :=
  h.q49_yamadaM₂_le_yamadaM₅ hW d hK hQ
    (h.crossed_mem_yamadaM₂ d hK hQ.doubling
      (h.yamadaR₆_le_normalizer_yamadaL₂ d hx))

theorem q49_crossed_mul_of_commute (h : Setup G L f t) {x s : G} (hst : s * t = t * s) :
    t * (x * s) * t * (x * s)⁻¹ = t * x * t * x⁻¹ := by
  calc t * (x * s) * t * (x * s)⁻¹ = t * x * (s * t * s⁻¹) * x⁻¹ := by group
    _ = t * x * t * x⁻¹ := by rw [hst]; group

theorem q49_crossed_mem_yamadaD₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ yamadaR₇ d t) : t * x * t * x⁻¹ ∈ yamadaD₅ d t := by
  have hD := hQ.doubling
  obtain ⟨c, hc, s, hs, rfl⟩ :=
    Common.exists_mul_of_le_normalizer (h.S_le_normalizer_yamadaCstar d) x hx
  rw [h.q49_crossed_mul_of_commute (mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs))]
  obtain ⟨δ, hδ, e⟩ := (h.yamada_5_19 d hK hD).2.1.1 c hc
  rw [h.conj_t_eq_mul_crossed c] at e
  rw [mul_left_cancel e]
  exact h.q49_yamadaD₁_le_yamadaD₅ hW d hK hQ hδ

theorem q49_exists_mem_yamadaR₆_crossed (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {m : G} (hm : m ∈ d.M) :
    ∃ a ∈ yamadaR₆ d t, ∃ f ∈ yamadaF₅ d t, t * a * t * a⁻¹ = m * f := by
  have hD := hQ.doubling
  obtain ⟨hN₁, hN₂, φ, hcl, -⟩ := h.yamada_5_40_3 hW d hK hQ
  obtain ⟨q, hq⟩ := φ.surjective (QuotientGroup.mk ⟨m, hm⟩)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨m', hm', η, hη, e⟩ := Common.exists_mul_of_le_normalizer
    (h.yamadaY₂_le_normalizer_M d hK hD) _
    (h.crossed_mem_yamadaM₂ d hK hD (h.yamadaR₆_le_normalizer_yamadaL₂ d x.2))
  have hx := hcl x ⟨m', hm'⟩ η hη (by
    rw [h.conj_t_eq_mul_crossed (x : G), e]
    group)
  have h1 : (⟨m, hm⟩ : d.M)⁻¹ * ⟨m', hm'⟩ ∈ d.F.subgroupOf d.M :=
    QuotientGroup.eq.1 (hq.symm.trans hx)
  have h2 : m⁻¹ * m' ∈ d.F := mem_subgroupOf.1 h1
  obtain ⟨-, hFF₅, -⟩ := h.q49_yamadaS₅_facts hW d hK hQ
  refine ⟨x, x.2, m⁻¹ * m' * η, mul_mem (hFF₅ h2) (q49_yamadaY₂_le_yamadaF₅ d t hη), ?_⟩
  rw [e]
  group

theorem q49_exists_mem_yamadaR₇_crossed (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {δ : G} (hδ : δ ∈ d.D) :
    ∃ b ∈ yamadaR₇ d t, ∃ f ∈ yamadaF₅ d t, t * b * t * b⁻¹ = δ * f := by
  have hD := hQ.doubling
  obtain ⟨c, hc, u, hu, e⟩ := (h.yamada_5_19 d hK hD).2.1.2 δ
    ((le_sup_right : d.D ≤ yamadaD₁ d t) hδ)
  have e2 : t * (t * c * t * c⁻¹) = t * (δ * u) := by
    rw [← h.conj_t_eq_mul_crossed c, e, mul_assoc]
  exact ⟨c, (le_sup_left : yamadaCstar d t ≤ yamadaRstar d t) hc, u,
    ((yamadaU₁_le_yamadaY₂ d t).trans (q49_yamadaY₂_le_yamadaF₅ d t)) hu, mul_left_cancel e2⟩

theorem q49_S_le_normalizer_yamadaF₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.S ≤ normalizer (yamadaF₅ d t : Set G) := by
  obtain ⟨hHF, -, -, -⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  obtain ⟨hSS₅, -⟩ := h.q49_yamadaS₅_facts hW d hK hQ
  exact (hSS₅.trans (h.q49_yamadaS₅_le_yamadaR₅ hW d hK hQ)).trans
    (Subgroup.le_normalizer.trans hHF)

theorem q49_crossed_mul_mem_yamadaV₈ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x y : G}
    (hx : x ∈ q49_yamadaV₈ d t) (hy : y ∈ q49_yamadaV₈ d t) :
    ∃ f ∈ yamadaF₅ d t, t * (x * y) * t * (x * y)⁻¹ =
      (t * x * t * x⁻¹) * (t * y * t * y⁻¹) * f :=
  q49_crossed_mul_mem h.t_mul_t (q49_mem_yamadaV₈.1 hx).2.2
    (h.q49_crossed_mem_yamadaS₅ hW d hK hQ (q49_yamadaV₈_le_normalizer d t hy))

theorem q49_exists_mem_yamadaR₇_mul_yamadaR₆_crossed (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {s : G}
    (hs : s ∈ yamadaS₅ d t) :
    ∃ b ∈ yamadaR₇ d t, ∃ a ∈ yamadaR₆ d t, ∃ f ∈ yamadaF₅ d t,
      t * (b * a) * t * (b * a)⁻¹ = s * f := by
  obtain ⟨⟨hS, -, -⟩, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨-, -, -, -, -, hFD, -, hDS, hMS, -⟩ := d.inclusions
  have hSF₅ := h.q49_S_le_normalizer_yamadaF₅ hW d hK hQ
  rw [hS] at hs
  obtain ⟨σ, hσ, f₀, hf₀, rfl⟩ := Common.exists_mul_of_le_normalizer' hSF₅ s hs
  rw [← (d.yamada_defs).2.2.2.2.2.2.2.2] at hσ
  obtain ⟨δ, hδ, m, hm, rfl⟩ := Common.exists_mul_of_le_normalizer'
    (fun x hx => d.S_le_normalizers.2.2.2.2.2.2 (hDS hx)) σ hσ
  obtain ⟨b, hb, f₁, hf₁, eb⟩ := h.q49_exists_mem_yamadaR₇_crossed hW d hK hQ hδ
  obtain ⟨a, ha, f₂, hf₂, ea⟩ := h.q49_exists_mem_yamadaR₆_crossed hW d hK hQ hm
  have hbV := h.q49_yamadaR₇_le_yamadaV₈ hW d hK hQ hb
  have haV := h.q49_yamadaR₆_le_yamadaV₈ hW d hK hQ ha
  obtain ⟨f₃, hf₃, e⟩ := h.q49_crossed_mul_mem_yamadaV₈ hW d hK hQ hbV haV
  have hmF : m⁻¹ * f₁ * m⁻¹⁻¹ ∈ yamadaF₅ d t :=
    (mem_normalizer_iff.1 (hSF₅ (inv_mem (hMS hm))) f₁).1 hf₁
  refine ⟨b, hb, a, ha, f₀⁻¹ * (m⁻¹ * f₁ * m⁻¹⁻¹) * f₂ * f₃,
    mul_mem (mul_mem (mul_mem (inv_mem hf₀) hmF) hf₂) hf₃, ?_⟩
  rw [e, eb, ea]
  group

theorem q49_exists_mem_yamadaV₈_crossed (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {s : G}
    (hs : s ∈ yamadaS₅ d t) :
    ∃ v ∈ q49_yamadaV₈ d t, ∃ f ∈ yamadaF₅ d t, t * v * t * v⁻¹ = s * f := by
  obtain ⟨b, hb, a, ha, f, hf, e⟩ := h.q49_exists_mem_yamadaR₇_mul_yamadaR₆_crossed hW d hK hQ hs
  exact ⟨b * a, mul_mem (h.q49_yamadaR₇_le_yamadaV₈ hW d hK hQ hb)
    (h.q49_yamadaR₆_le_yamadaV₈ hW d hK hQ ha), f, hf, e⟩

theorem q49_mem_yamadaR_of_forall_commutator_mem (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {c : G} (hct : c ∈ centralizer ({t} : Set G)) (hcS : c ∈ normalizer (d.S : Set G))
    (hc : ∀ s ∈ d.S, c * s * c⁻¹ * s⁻¹ ∈ yamadaF₅ d t) : c ∈ yamadaR d t := by
  obtain ⟨-, hSF, -, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  have hcL : c ∈ normalizer (L : Set G) := h.centralizer_le_normalizer hct
  have hsec : ∀ y ∈ d.S, y⁻¹ * (c * y * c⁻¹) ∈ d.F := by
    intro s hs
    have h1 : c * s * c⁻¹ * s⁻¹ ∈ d.F := by
      rw [← hSF]
      exact Subgroup.mem_inf.2 ⟨mul_mem ((mem_normalizer_iff.1 hcS s).1 hs) (inv_mem hs), hc s hs⟩
    have h2 := (mem_normalizer_iff.1 (inv_mem (d.S_le_normalizers.2.2.2.2.1 hs)) _).1 h1
    rwa [show s⁻¹ * (c * s * c⁻¹ * s⁻¹) * s⁻¹⁻¹ = s⁻¹ * (c * s * c⁻¹) by group] at h2
  have hc' := (d.act_sectionCentralizer_eq (Model.F_le_S (K := K))
    (Model.yamada_3_23_S_F hK h.two_le) hcL).1 hsec
  have hZ : centralizer (L : Set G) ≤ normalizer (d.S : Set G) := fun z hz =>
    mem_normalizer_of_conj_mem fun x hx => by
      rw [← mem_centralizer_iff.1 hz x (d.image_le _ hx), mul_inv_cancel_right]
      exact hx
  obtain ⟨s, hs, z, hz, rfl⟩ := Common.exists_mul_of_le_normalizer hZ c hc'
  have hzt : z ∈ centralizer ({t} : Set G) := by
    have := mul_mem (inv_mem (h.S_le_centralizer d hs)) hct
    simpa using this
  exact mul_mem (mem_sup_left hs) (mem_sup_right (Subgroup.mem_inf.2 ⟨hz, hzt⟩))

theorem q49_crossed_mem_yamadaF₅_iff (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ q49_yamadaV₈ d t) : t * x * t * x⁻¹ ∈ yamadaF₅ d t ↔ x ∈ yamadaR₅ d t := by
  have hD := hQ.doubling
  constructor
  · intro hκ
    obtain ⟨hxH, hxF, -⟩ := q49_mem_yamadaV₈.1 hx
    have hE₅ := (h.yamada_5_37_2 hW d hK hQ).2.2.2.2.1
    have hgt : x * t * x⁻¹ ∈ yamadaF₅ d t ⊔ zpowers t := by
      rw [h.conj_t_eq_mul_crossed x]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hκ)
    have hxE := mem_normalizer_sup_zpowers_of_conj_mem hxF hgt
    rw [hE₅] at hxE
    have hxR₂ : x ∈ normalizer (yamadaR₂ d t : Set G) := by
      rw [← h.yamada_5_47 hW d hK hQ]
      exact Subgroup.mem_inf.2 ⟨hxH, hxE⟩
    obtain ⟨-, hset, hRR⟩ := h.yamada_5_27_1 hW d hK hD
    have hx' : x ∈ ((normalizer (yamadaR₂ d t : Set G) : Subgroup G) : Set G) := hxR₂
    rw [hset] at hx'
    obtain ⟨r, hr, c, hc, rfl⟩ := Set.mem_mul.1 hx'
    have hcV : c ∈ q49_yamadaV₈ d t := by
      have := mul_mem (inv_mem (h.q49_yamadaR₅_le_yamadaV₈ hW d hK hQ hr)) hx
      rwa [inv_mul_cancel_left] at this
    obtain ⟨hct, hcS⟩ := Subgroup.mem_inf.1 hc
    obtain ⟨hSS₅, -⟩ := h.q49_yamadaS₅_facts hW d hK hQ
    have hcR := h.q49_mem_yamadaR_of_forall_commutator_mem hW d hK hQ hct hcS
      fun s hs => (q49_mem_yamadaV₈.1 hcV).2.2 s (hSS₅ hs)
    have hR₅ : yamadaR d t ≤ yamadaR₅ d t := hRR.ge.trans inf_le_left
    exact mul_mem hr (hR₅ hcR)
  · intro hx5
    exact q49_yamadaF₂_le_yamadaF₅ d t (h.q49_crossed_mem_yamadaF₂ hW d hK hD hx5)

theorem q49_mem_normalizer_yamadaR₂_of_crossed_mem (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ normalizer (yamadaR₅ d t : Set G)) (hκ : t * x * t * x⁻¹ ∈ yamadaF₅ d t) :
    x ∈ normalizer (yamadaR₂ d t : Set G) := by
  obtain ⟨hHF, -, -, -⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  have hE₅ := (h.yamada_5_37_2 hW d hK hQ).2.2.2.2.1
  have hgt : x * t * x⁻¹ ∈ yamadaF₅ d t ⊔ zpowers t := by
    rw [h.conj_t_eq_mul_crossed x]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hκ)
  have hxE := mem_normalizer_sup_zpowers_of_conj_mem (hHF hx) hgt
  rw [hE₅] at hxE
  rw [← h.yamada_5_47 hW d hK hQ]
  exact Subgroup.mem_inf.2 ⟨hx, hxE⟩

theorem q49_yamadaR₅_le_yamadaR₈ (d : G2Data L K) (t : G) : yamadaR₅ d t ≤ yamadaR₈ d t :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  LieType.BorelTits.le_pCoreOf_normalizer 2 _ (LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem q49_yamadaR₈_inf_normalizer_yamadaR₂ (d : G2Data L K) (t : G) :
    yamadaR₈ d t ⊓ normalizer (yamadaR₂ d t : Set G) = yamadaR₅ d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_inf (q49_yamadaR₅_le_yamadaR₈ d t) (LieType.BorelTits.pCoreOf_le 2 _))
  exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
    (fun g hg => Common.mem_normalizer_inf
      (le_normalizer_yamadaR₈ d t (q49_normalizer_yamadaR₂_le_normalizer_yamadaR₅ d t hg))
      (Subgroup.le_normalizer hg))
    ((LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)

theorem q49_mul_self_mem_F_of_mem_S (d : G2Data L K) (hK4 : 4 ≤ Nat.card K) {s : G} (hs : s ∈ d.S) :
    s * s ∈ d.F := by
  have h1 : s ^ 2 ∈ closure {z | ∃ g ∈ d.S, z = g ^ 2} := subset_closure ⟨s, hs, rfl⟩
  rw [(d.yamada_3_12_mho hK4).2.2, sq] at h1
  exact h1

theorem q49_commutator_mem_F_of_mem_S (d : G2Data L K) (hK4 : 4 ≤ Nat.card K) {s m : G}
    (hs : s ∈ d.S) (hm : m ∈ d.S) : s * m * s⁻¹ * m⁻¹ ∈ d.F := by
  have := Subgroup.commutator_mem_commutator hs hm
  rw [(d.yamada_3_12_commutators hK4).2.2.1] at this
  exact this

theorem q49_exists_hom_yamadaV₈ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∃ _ : (d.F.subgroupOf d.S).Normal, ∃ Ψ : q49_yamadaV₈ d t →* d.S ⧸ d.F.subgroupOf d.S,
      (∀ (x : q49_yamadaV₈ d t) (s : d.S), ∀ y ∈ yamadaF₅ d t,
        t * (x : G) * t * (x : G)⁻¹ = s * y → Ψ x = QuotientGroup.mk s) ∧
      ∀ (x : q49_yamadaV₈ d t) (s : d.S), Ψ x = QuotientGroup.mk s →
        ∃ y ∈ yamadaF₅ d t, t * (x : G) * t * (x : G)⁻¹ = s * y := by
  obtain ⟨⟨hS, -, -⟩, hSF, -, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨-, -, -, -, -, hFD, -, hDS, -⟩ := d.inclusions
  have hSF₅ := h.q49_S_le_normalizer_yamadaF₅ hW d hK hQ
  have hFn : (d.F.subgroupOf d.S).Normal :=
    (normal_subgroupOf_iff_le_normalizer (hFD.trans hDS)).2 d.S_le_normalizers.2.2.2.2.1
  refine ⟨hFn, ?_⟩
  obtain ⟨Ψ, h1, h2⟩ := q49_exists_hom_crossed (V := q49_yamadaV₈ d t) (S := d.S)
    (S₅ := yamadaS₅ d t) (F₅ := yamadaF₅ d t) (F := d.F) (fun x => t * x * t * x⁻¹) hFn hSF₅
    (fun s hs => Common.exists_mul_of_le_normalizer' hSF₅ s (by rw [← hS]; exact hs)) hSF
    (fun x hx => h.q49_crossed_mem_yamadaS₅ hW d hK hQ (q49_yamadaV₈_le_normalizer d t hx))
    (by simp [h.t_mul_t])
    (fun x hx y hy => h.q49_crossed_mul_mem_yamadaV₈ hW d hK hQ hx hy)
  exact ⟨Ψ, h1, h2⟩

theorem q49_elemModulo_yamadaR₅_yamadaV₈ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ElemModulo (yamadaR₅ d t) (q49_yamadaV₈ d t) := by
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨hFn, Ψ, h1, h2⟩ := h.q49_exists_hom_yamadaV₈ hW d hK hQ
  have hsq : ∀ a : d.S ⧸ d.F.subgroupOf d.S, a * a = 1 := fun a =>
    QuotientGroup.induction_on a fun s => by
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact q49_mul_self_mem_F_of_mem_S d hK4 s.2
  have hcomm : ∀ a b : d.S ⧸ d.F.subgroupOf d.S, a * b = b * a := fun a b =>
    QuotientGroup.induction_on a fun s => QuotientGroup.induction_on b fun s' => by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
      have := q49_commutator_mem_F_of_mem_S d hK4 (inv_mem s'.2) (inv_mem s.2)
      rwa [show (s' : G)⁻¹ * (s : G)⁻¹ * (s' : G)⁻¹⁻¹ * (s : G)⁻¹⁻¹ =
        ((s * s' : d.S) : G)⁻¹ * ((s' * s : d.S) : G) by simp [mul_assoc]] at this
  have hker : ∀ x : q49_yamadaV₈ d t, Ψ x = 1 → (x : G) ∈ yamadaR₅ d t := fun x hx => by
    obtain ⟨y, hy, e⟩ := h2 x 1 (by rw [hx, QuotientGroup.mk_one])
    exact (h.q49_crossed_mem_yamadaF₅_iff hW d hK hQ x.2).1 (by
      rw [e, OneMemClass.coe_one, one_mul]
      exact hy)
  have hcom1 : ∀ a b : d.S ⧸ d.F.subgroupOf d.S, a * b * a⁻¹ * b⁻¹ = 1 := fun a b => by
    rw [hcomm a b, mul_inv_cancel_right, mul_inv_cancel]
  intro x hx y hy
  refine ⟨?_, ?_⟩
  · exact hker (⟨x, hx⟩ * ⟨x, hx⟩) (by rw [map_mul, hsq])
  · exact hker (⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹)
      (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcom1])

theorem q49_yamadaV₈_le_yamadaR₈ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    q49_yamadaV₈ d t ≤ yamadaR₈ d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE := h.q49_elemModulo_yamadaR₅_yamadaV₈ hW d hK hQ
  have hR₅p : IsPGroup 2 (yamadaR₅ d t) := LieType.BorelTits.pCoreOf_isPGroup 2 _
  refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (q49_yamadaV₈_le_normalizer d t)
    (h.q49_normalizer_yamadaR₅_le_normalizer_yamadaV₈ hW d hK hQ) fun x => ?_
  obtain ⟨k, hk⟩ := hR₅p ⟨(x : G) * x, (hE x x.2 x x.2).1⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  have hk' : ((x : G) * x) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  rw [Subgroup.coe_pow, Subgroup.coe_one, pow_succ', pow_mul, sq]
  exact hk'

theorem q49_exists_mem_yamadaV₈_inv_mul_mem (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ normalizer (yamadaR₅ d t : Set G)) :
    ∃ v ∈ q49_yamadaV₈ d t, v⁻¹ * x ∈ normalizer (yamadaR₂ d t : Set G) := by
  obtain ⟨hHF, -, -, -⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  obtain ⟨v, hv, f, hf, e⟩ := h.q49_exists_mem_yamadaV₈_crossed hW d hK hQ
    (h.q49_crossed_mem_yamadaS₅ hW d hK hQ hx)
  have hvH := q49_yamadaV₈_le_normalizer d t hv
  exact ⟨v, hv, h.q49_mem_normalizer_yamadaR₂_of_crossed_mem hW d hK hQ (mul_mem (inv_mem hvH) hx)
    (q49_crossed_inv_mul_mem h.t_mul_t (hHF hvH) hf e)⟩

theorem q49_yamadaR₈_le_yamadaV₈ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₈ d t ≤ q49_yamadaV₈ d t := by
  intro x hx
  obtain ⟨v, hv, hc⟩ := h.q49_exists_mem_yamadaV₈_inv_mul_mem hW d hK hQ (yamadaR₈_le d t hx)
  have hcR₅ : v⁻¹ * x ∈ yamadaR₅ d t := by
    rw [← q49_yamadaR₈_inf_normalizer_yamadaR₂ d t]
    exact Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (h.q49_yamadaV₈_le_yamadaR₈ hW d hK hQ hv)) hx, hc⟩
  have := mul_mem hv (h.q49_yamadaR₅_le_yamadaV₈ hW d hK hQ hcR₅)
  rwa [mul_inv_cancel_left] at this

theorem q49_yamadaV₈_eq (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : q49_yamadaV₈ d t = yamadaR₈ d t :=
  le_antisymm (h.q49_yamadaV₈_le_yamadaR₈ hW d hK hQ) (h.q49_yamadaR₈_le_yamadaV₈ hW d hK hQ)

theorem q49_yamadaM₅_inf_yamadaD₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₅ d t ⊓ yamadaD₅ d t = yamadaF₅ d t := by
  obtain ⟨⟨-, hM, hD⟩, hSF, -, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨-, hFF₅, hF₅M, hF₅D, -⟩ := h.q49_yamadaS₅_facts hW d hK hQ
  obtain ⟨-, -, -, -, -, hFD, -, hDS, hMS, -⟩ := d.inclusions
  have hSF₅ := h.q49_S_le_normalizer_yamadaF₅ hW d hK hQ
  refine le_antisymm (fun x hx => ?_) (le_inf hF₅M hF₅D)
  obtain ⟨hxM, hxD⟩ := Subgroup.mem_inf.1 hx
  rw [hM] at hxM
  rw [hD] at hxD
  obtain ⟨m, hm, f, hf, rfl⟩ := Common.exists_mul_of_le_normalizer' (hMS.trans hSF₅) _ hxM
  obtain ⟨δ, hδ, f', hf', e⟩ := Common.exists_mul_of_le_normalizer' (hDS.trans hSF₅) _ hxD
  have h1 : δ⁻¹ * m ∈ d.F := by
    rw [← hSF]
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (hDS hδ)) (hMS hm), ?_⟩
    have : δ⁻¹ * m = f' * f⁻¹ := by
      calc δ⁻¹ * m = δ⁻¹ * (m * f) * f⁻¹ := by group
        _ = δ⁻¹ * (δ * f') * f⁻¹ := by rw [e]
        _ = f' * f⁻¹ := by group
    rw [this]
    exact mul_mem hf' (inv_mem hf)
  have hmD : m ∈ d.D := by
    have := mul_mem hδ (hFD h1)
    rwa [mul_inv_cancel_left] at this
  have hmF : m ∈ d.F := by
    rw [← (d.yamada_defs).2.2.2.2.2.2.2.1]
    exact Subgroup.mem_inf.2 ⟨hmD, hm⟩
  exact mul_mem (hFF₅ hmF) hf

theorem q49_J_le_normalizer_F (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.J ≤ normalizer (d.F : Set G) := fun _ hj =>
  h.centralizer_inf_normalizer_S_le_normalizer_F d hK hD (h.J_le_centralizer_inf_normalizer_S d hj)

theorem q49_J_le_normalizer_D (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.J ≤ normalizer (d.D : Set G) := fun j hj => by
  rw [← (d.yamada_defs).2.2.2.2.1]
  exact Common.mem_normalizer_sup (J_le_normalizer_rootGroup d isRoot_g2a hj)
    (h.q49_J_le_normalizer_F d hK hD hj)

theorem q49_J_le_normalizer_M' (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.J ≤ normalizer (d.M : Set G) := fun j hj => by
  rw [← (d.yamada_defs).2.2.2.2.2.1]
  exact Common.mem_normalizer_sup (J_le_normalizer_rootGroup d isRoot_g2r hj)
    (h.q49_J_le_normalizer_F d hK hD hj)

theorem q49_mem_D_of_forall_J₄ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hQ : h.QFacts d) {s : G} (hs : s ∈ d.S)
    (hfix : ∀ j ∈ d.Ji 3, s⁻¹ * (j * s * j⁻¹) ∈ d.D) : s ∈ d.D := by
  have hD := hQ.doubling
  obtain ⟨-, -, -, -, -, -, -, hDS, -⟩ := d.inclusions
  have hJJ : d.Ji 3 ≤ d.J := d.image_mono inf_le_left
  obtain ⟨c, hc, n, hn, rfl⟩ := exists_centralizer_mul_of_le_J d hJJ hDS
    d.S_le_normalizers.2.2.2.2.2.1 (fun j hj => (h.J_le_centralizer_inf_normalizer_S d (hJJ hj)).2)
    (fun j hj => h.q49_J_le_normalizer_D d hK hD (hJJ hj)) d.isSylowOf_S.isPGroup hs hfix
  exact mul_mem (Q44.S_inf_centralizer_J₄_le_D h d hK hQ hc) hn

theorem q49_mem_M_of_forall_J₃ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hQ : h.QFacts d) {s : G} (hs : s ∈ d.S)
    (hfix : ∀ j ∈ d.Ji 2, s⁻¹ * (j * s * j⁻¹) ∈ d.M) : s ∈ d.M := by
  have hD := hQ.doubling
  obtain ⟨-, -, -, -, -, -, -, -, hMS, -⟩ := d.inclusions
  have hJJ : d.Ji 2 ≤ d.J := d.image_mono inf_le_left
  obtain ⟨c, hc, n, hn, rfl⟩ := exists_centralizer_mul_of_le_J d hJJ hMS
    d.S_le_normalizers.2.2.2.2.2.2 (fun j hj => (h.J_le_centralizer_inf_normalizer_S d (hJJ hj)).2)
    (fun j hj => h.q49_J_le_normalizer_M' d hK hD (hJJ hj)) d.isSylowOf_S.isPGroup hs hfix
  have hc' : c ∈ d.S ⊓ centralizer (d.Ji 2 : Set G) := hc
  rw [S_inf_centralizer_Ji_of_four_le d (hK ▸ h.four_le) 2 (Or.inr (by decide))] at hc'
  exact mul_mem ((le_sup_left.trans (d.yamada_defs).2.2.2.2.2.1.le) hc') hn

theorem q49_mem_F_of_forall_J (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hQ : h.QFacts d) {s : G} (hs : s ∈ d.S)
    (hfix : ∀ j ∈ d.J, s⁻¹ * (j * s * j⁻¹) ∈ d.F) : s ∈ d.F := by
  obtain ⟨-, -, -, -, -, hFD, hFM, -⟩ := d.inclusions
  have hJ₄ : d.Ji 3 ≤ d.J := d.image_mono inf_le_left
  have hJ₃ : d.Ji 2 ≤ d.J := d.image_mono inf_le_left
  rw [← (d.yamada_defs).2.2.2.2.2.2.2.1]
  exact Subgroup.mem_inf.2
    ⟨h.q49_mem_D_of_forall_J₄ d hK hQ hs fun j hj => hFD (hfix j (hJ₄ hj)),
      h.q49_mem_M_of_forall_J₃ d hK hQ hs fun j hj => hFM (hfix j (hJ₃ hj))⟩

theorem q49_S_inf_centralizer_J (d : G2Data L K) (h4 : 4 ≤ Nat.card K) :
    d.S ⊓ centralizer (d.J : Set G) = ⊥ := by
  rw [G2Data.S, G2Data.J, ← d.image_inf_centralizer _ (Model.J_le_adjointGroup K),
    Model.S_inf_centralizer_J h4, d.image_bot]

theorem q49_yamadaS₂_inf_centralizer_J_le (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaS₂ d t ⊓ centralizer (d.J : Set G) ≤ yamadaY₂ d t := fun c hc => by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := hQ.doubling
  obtain ⟨hcS, hcJ⟩ := Subgroup.mem_inf.1 hc
  obtain ⟨hSY₂, -⟩ := h.yamada_5_13_3 d hK hD
  obtain ⟨-, hYX, -, hXF, -, hFD, -, hDS, -⟩ := d.inclusions
  obtain ⟨s, hs, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hSY₂ _ hcS
  have hJC := h.J_le_centralizer_inf_normalizer_S d
  have hJS : d.J ≤ normalizer (d.S : Set G) := fun j hj => (Subgroup.mem_inf.1 (hJC hj)).2
  have hJY : d.J ≤ normalizer (d.Y : Set G) := fun j hj =>
    (h.centralizer_inf_normalizer_S_le d hK hD).2.2 (hJC hj)
  have hJY₂ := h.J_le_normalizer_yamadaY₂ d hK hD
  have hSY : d.S ⊓ yamadaY₂ d t ≤ d.Y := fun x hx => by
    rw [← h.yamadaY₂_inf_centralizer d hK hD]
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2,
      h.L_le_centralizer (d.image_le _ (Subgroup.mem_inf.1 hx).1)⟩
  have hfix : ∀ j ∈ d.J, s⁻¹ * (j * s * j⁻¹) ∈ d.Y := fun j hj => by
    have hjc : j * (s * y) = s * y * j := mem_centralizer_iff.1 hcJ j hj
    refine hSY (Subgroup.mem_inf.2
      ⟨mul_mem (inv_mem hs) ((mem_normalizer_iff.1 (hJS hj) s).1 hs), ?_⟩)
    rw [show s⁻¹ * (j * s * j⁻¹) = y * (j * y * j⁻¹)⁻¹ by
      calc s⁻¹ * (j * s * j⁻¹) = s⁻¹ * (j * (s * y) * j⁻¹) * (j * y * j⁻¹)⁻¹ := by group
        _ = y * (j * y * j⁻¹)⁻¹ := by rw [hjc]; group]
    exact mul_mem hy (inv_mem ((mem_normalizer_iff.1 (hJY₂ hj) y).1 hy))
  have hSp : IsPGroup 2 d.S := d.isSylowOf_S.isPGroup
  have : Group.IsNilpotent d.S := hSp.isNilpotent
  obtain ⟨c', hc', n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime
    (M := d.S) (N := d.Y) (S := d.J) (hYX.trans (hXF.trans (hFD.trans hDS)))
    d.S_le_normalizers.2.1 hJS hJY inferInstance (coprime_card_J d hSp) hs hfix
  have hc'1 : c' = 1 := by
    rw [q49_S_inf_centralizer_J d (hK ▸ h.four_le)] at hc'
    exact Subgroup.mem_bot.1 hc'
  rw [hc'1, one_mul]
  exact mul_mem (h.Y_le_yamadaY₂ d hK hD hn) hy

theorem q49_eq_one_of_mem_yamadaS₂_of_forall_J (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {y : G} (hy : y ∈ yamadaS₂ d t)
    (hfix : ∀ k ∈ d.J, k * y = y * k) : y = 1 :=
  h.eq_one_of_mem_yamadaY₂_of_forall_J d hK hQ.doubling
    (h.q49_yamadaS₂_inf_centralizer_J_le d hK hQ
      (Subgroup.mem_inf.2 ⟨hy, mem_centralizer_iff.2 hfix⟩)) hfix

theorem q49_centralizer_le_normalizer_S (d : G2Data L K) :
    centralizer (L : Set G) ≤ normalizer (d.S : Set G) := fun z hz =>
  mem_normalizer_of_conj_mem fun x hx => by
    rw [← mem_centralizer_iff.1 hz x (d.image_le _ hx), mul_inv_cancel_right]
    exact hx

theorem q49_yamadaR₈_inf_centralizer_J_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₈ d t ⊓ centralizer (d.J : Set G) ≤ zpowers t := by
  have hD := hQ.doubling
  have htt := h.t_mul_t
  obtain ⟨hHF, -, -, -⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  obtain ⟨⟨hS, -, -⟩, hSF, -, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨-, hFF₅, -⟩ := h.q49_yamadaS₅_facts hW d hK hQ
  obtain ⟨-, -, -, -, -, hFD, -, hDS, -⟩ := d.inclusions
  have hSF₅ := h.q49_S_le_normalizer_yamadaF₅ hW d hK hQ
  have hJH := h.q49_J_le_normalizer_yamadaR₅ d hK hD
  have hJC : ∀ j ∈ d.J, j * t = t * j := fun j hj =>
    mem_centralizer_singleton_iff.1 (h.J_le_centralizer_inf_normalizer_S d hj).1
  intro x hx
  obtain ⟨hx8, hxJ⟩ := Subgroup.mem_inf.1 hx
  have hxJ' : ∀ j ∈ d.J, j * x = x * j := fun j hj => mem_centralizer_iff.1 hxJ j hj
  have hxV := h.q49_yamadaR₈_le_yamadaV₈ hW d hK hQ hx8
  have hκfix : ∀ j ∈ d.J, j * (t * x * t * x⁻¹) = (t * x * t * x⁻¹) * j := fun j hj => by
    have c1 : Commute j t := hJC j hj
    have c2 : Commute j x := hxJ' j hj
    exact ((c1.mul_right c2).mul_right c1).mul_right c2.inv_right
  have hκS₅ := h.q49_crossed_mem_yamadaS₅ hW d hK hQ (q49_yamadaV₈_le_normalizer d t hxV)
  rw [hS] at hκS₅
  obtain ⟨σ, hσ, f₀, hf₀, hσf⟩ := Common.exists_mul_of_le_normalizer' hSF₅ _ hκS₅
  have hσfix : ∀ j ∈ d.J, σ⁻¹ * (j * σ * j⁻¹) ∈ d.F := by
    intro j hj
    have hjc : j * (σ * f₀) * j⁻¹ = σ * f₀ := by
      rw [← hσf, hκfix j hj, mul_inv_cancel_right]
    have h1 : σ⁻¹ * (j * σ * j⁻¹) ∈ d.S :=
      mul_mem (inv_mem hσ)
        ((mem_normalizer_iff.1 (h.J_le_centralizer_inf_normalizer_S d hj).2 σ).1 hσ)
    have h2 : σ⁻¹ * (j * σ * j⁻¹) ∈ yamadaF₅ d t := by
      have e : σ⁻¹ * (j * σ * j⁻¹) = f₀ * (j * f₀ * j⁻¹)⁻¹ := by
        calc σ⁻¹ * (j * σ * j⁻¹) = σ⁻¹ * (j * (σ * f₀) * j⁻¹) * (j * f₀ * j⁻¹)⁻¹ := by group
          _ = f₀ * (j * f₀ * j⁻¹)⁻¹ := by rw [hjc]; group
      rw [e]
      exact mul_mem hf₀ (inv_mem ((mem_normalizer_iff.1 (hHF (hJH hj)) f₀).1 hf₀))
    rw [← hSF]
    exact Subgroup.mem_inf.2 ⟨h1, h2⟩
  have hσF := h.q49_mem_F_of_forall_J d hK hQ hσ hσfix
  have hκF₅ : t * x * t * x⁻¹ ∈ yamadaF₅ d t := by
    rw [hσf]
    exact mul_mem (hFF₅ hσF) hf₀
  have hx5 := (h.q49_crossed_mem_yamadaF₅_iff hW d hK hQ hxV).1 hκF₅
  have hκF₂ := h.q49_crossed_mem_yamadaF₂ hW d hK hD hx5
  have hF₂S₂ : yamadaF₂ d t ≤ yamadaS₂ d t := sup_le_sup_right (hFD.trans hDS) _
  have hκ1 : t * x * t * x⁻¹ = 1 :=
    h.q49_eq_one_of_mem_yamadaS₂_of_forall_J d hK hQ (hF₂S₂ hκF₂) hκfix
  have hxt : x * t = t * x := by
    have e : t * x * t = x := mul_inv_eq_one.1 hκ1
    calc x * t = (t * x * t) * t := by rw [e]
      _ = t * x * (t * t) := by group
      _ = t * x := by rw [htt, mul_one]
  have hxR : x ∈ yamadaR d t := by
    obtain ⟨-, -, hRR⟩ := h.yamada_5_27_1 hW d hK hD
    rw [← hRR]
    exact Subgroup.mem_inf.2 ⟨hx5, mem_centralizer_singleton_iff.2 hxt⟩
  obtain ⟨s, hs, z, hz, rfl⟩ := Common.exists_mul_of_le_normalizer
    (inf_le_left.trans (q49_centralizer_le_normalizer_S d)) x hxR
  have hzJ : ∀ j ∈ d.J, j * z = z * j := fun j hj =>
    mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).1 j (d.image_le _ hj)
  have hsfix : ∀ j ∈ d.J, j * s = s * j := by
    intro j hj
    have e : j * s * z = s * j * z := by
      calc j * s * z = j * (s * z) := by group
        _ = (s * z) * j := hxJ' j hj
        _ = s * (z * j) := by group
        _ = s * (j * z) := by rw [← hzJ j hj]
        _ = s * j * z := by group
    exact mul_right_cancel e
  have hs1 : s = 1 :=
    h.q49_eq_one_of_mem_yamadaS₂_of_forall_J d hK hQ ((le_sup_left : d.S ≤ yamadaS₂ d t) hs) hsfix
  rw [hs1, one_mul, ← h.centralizer_L_inf]
  exact hz

theorem q49_mul_self_mem_yamadaS₅_of_mem_yamadaR₈ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ yamadaR₈ d t) : x * x ∈ yamadaS₅ d t := by
  have hD := hQ.doubling
  have htt := h.t_mul_t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hT : ∀ z : G, t * (t * z) = z := fun z => by rw [← mul_assoc, htt, one_mul]
  obtain ⟨hHF, -, -, hHS⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  obtain ⟨hR, htS, htnS⟩ := (h.yamada_5_37_2 hW d hK hQ).2.1
  obtain ⟨-, -, hF₅M, -, -, -, hM₅S, -⟩ := h.q49_yamadaS₅_facts hW d hK hQ
  have hxV := h.q49_yamadaR₈_le_yamadaV₈ hW d hK hQ hx
  have hxx : x * x ∈ yamadaR₅ d t := (h.q49_elemModulo_yamadaR₅_yamadaV₈ hW d hK hQ x hxV x hxV).1
  rw [← hR] at hxx
  rcases (mem_sup_zpowers_iff_of htt htS).1 hxx with h1 | ⟨a, ha, e⟩
  · exact h1
  · exfalso
    have hs' : t * a * t ∈ yamadaS₅ d t := by
      have := (mem_normalizer_iff.1 htS a).1 ha
      rwa [htinv] at this
    obtain ⟨g, hg, f, hf, hge⟩ := h.q49_exists_mem_yamadaV₈_crossed hW d hK hQ (inv_mem hs')
    obtain ⟨hgH, hgF, hgc⟩ := q49_mem_yamadaV₈.1 hg
    have htF : t ∈ normalizer (yamadaF₅ d t : Set G) :=
      hHF (Subgroup.le_normalizer (h.q49_t_mem_yamadaR₅ hW d hK hQ))
    have hc₁ : g * a * g⁻¹ * a⁻¹ ∈ yamadaF₅ d t := hgc a ha
    have hφ₀ : (t * (g * a * g⁻¹ * a⁻¹) * t) * f ∈ yamadaF₅ d t := by
      have := (mem_normalizer_iff.1 htF _).1 hc₁
      rw [htinv] at this
      exact mul_mem this hf
    obtain ⟨y, hy⟩ : ∃ y : G, y = g * x * g⁻¹ := ⟨_, rfl⟩
    have hyV : y ∈ q49_yamadaV₈ d t := hy ▸ mul_mem (mul_mem hg hxV) (inv_mem hg)
    have hinv3 : (t * a * t)⁻¹ = t * a⁻¹ * t := by
      rw [mul_inv_rev, mul_inv_rev, htinv]
      group
    have hyy : y * y = t * ((t * (g * a * g⁻¹ * a⁻¹) * t) * f) := by
      calc y * y = g * (x * x) * g⁻¹ := by rw [hy]; group
        _ = g * (a * t) * g⁻¹ := by rw [e]
        _ = (g * a * g⁻¹) * (g * t * g⁻¹) := by group
        _ = (g * a * g⁻¹) * (t * (t * g * t * g⁻¹)) := by rw [h.conj_t_eq_mul_crossed g]
        _ = (g * a * g⁻¹) * (t * ((t * a * t)⁻¹ * f)) := by rw [hge]
        _ = t * ((t * (g * a * g⁻¹ * a⁻¹) * t) * f) := by
          rw [hinv3]
          simp only [mul_assoc, hT]
    generalize (t * (g * a * g⁻¹ * a⁻¹) * t) * f = φ₀ at hφ₀ hyy
    have hφ₀' : φ₀ = t * (y * y) := by rw [hyy, hT]
    have hκy : t * y * t * y⁻¹ = φ₀ * (y * φ₀⁻¹ * y⁻¹) := by
      rw [hφ₀', mul_inv_rev, htinv]
      group
    have hκyF : t * y * t * y⁻¹ ∈ yamadaF₅ d t := by
      rw [hκy]
      exact mul_mem hφ₀ ((mem_normalizer_iff.1 (hHF (q49_yamadaV₈_le_normalizer d t hyV)) φ₀⁻¹).1
        (inv_mem hφ₀))
    have hy5 : y ∈ yamadaR₅ d t := (h.q49_crossed_mem_yamadaF₅_iff hW d hK hQ hyV).1 hκyF
    have hyyF₂ := h.mul_self_mem_yamadaF₂ hW d hK hQ hy5
    rw [hyy] at hyyF₂
    have htF₅ : t ∈ yamadaF₅ d t := by
      have := mul_mem (q49_yamadaF₂_le_yamadaF₅ d t hyyF₂) (inv_mem hφ₀)
      rwa [mul_inv_cancel_right] at this
    exact htnS (hM₅S (hF₅M htF₅))

theorem q49_J_le_normalizer_yamadaR₈ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.J ≤ normalizer (yamadaR₈ d t : Set G) :=
  (h.q49_J_le_normalizer_yamadaR₅ d hK hD).trans (le_normalizer_yamadaR₈ d t)

theorem q49_yamadaP_le_yamadaR₈ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaP d t ≤ yamadaR₈ d t :=
  Subgroup.commutator_le.2 fun x hx j hj => by
    rw [commutatorElement_def, show x * j * x⁻¹ * j⁻¹ = x * (j * x⁻¹ * j⁻¹) by group]
    exact mul_mem hx ((mem_normalizer_iff.1 (h.q49_J_le_normalizer_yamadaR₈ d hK hD hj) x⁻¹).1
      (inv_mem hx))

theorem q49_yamadaR₈_le_normalizer_yamadaP (d : G2Data L K) (t : G) :
    yamadaR₈ d t ≤ normalizer (yamadaP d t : Set G) :=
  le_normalizer_commutator_left _ _

theorem q49_J_le_normalizer_yamadaP (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.J ≤ normalizer (yamadaP d t : Set G) := fun _ hj =>
  mem_normalizer_commutator (h.q49_J_le_normalizer_yamadaR₈ d hK hD hj) (Subgroup.le_normalizer hj)

theorem q49_isPGroup_yamadaR₈ (d : G2Data L K) (t : G) : IsPGroup 2 (yamadaR₈ d t) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  LieType.BorelTits.pCoreOf_isPGroup 2 _

theorem q49_t_not_mem_yamadaP (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : t ∉ yamadaP d t := by
  have hD := hQ.doubling
  obtain ⟨-, -, -, hHS⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  obtain ⟨-, htS, htnS⟩ := (h.yamada_5_37_2 hW d hK hQ).2.1
  intro htP
  refine htnS (mem_of_mem_commutator_of_forall (V := yamadaR₈ d t) (N := yamadaS₅ d t)
    (J := d.J) ((h.q49_yamadaS₅_le_yamadaR₅ hW d hK hQ).trans (q49_yamadaR₅_le_yamadaR₈ d t))
    (fun x hx => hHS (yamadaR₈_le d t hx))
    (comm_mem_of_mul_self_mem (fun x hx => hHS (yamadaR₈_le d t hx))
      fun x hx => h.q49_mul_self_mem_yamadaS₅_of_mem_yamadaR₈ hW d hK hQ hx)
    (h.q49_J_le_normalizer_yamadaR₈ d hK hD) ((h.q49_J_le_normalizer_yamadaR₅ d hK hD).trans hHS)
    (coprime_card_J d (q49_isPGroup_yamadaR₈ d t)) htP fun j hj => ?_)
  have hjt : j * t = t * j :=
    mem_centralizer_singleton_iff.1 (h.J_le_centralizer_inf_normalizer_S d hj).1
  rw [show j * t * j⁻¹ = t by rw [hjt]; group, inv_mul_cancel]
  exact one_mem _

theorem q49_yamadaP_sup_zpowers (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaP d t ⊔ zpowers t = yamadaR₈ d t := by
  have hD := hQ.doubling
  refine le_antisymm (sup_le (h.q49_yamadaP_le_yamadaR₈ d hK hD) ((zpowers_le).2
    (q49_yamadaR₅_le_yamadaR₈ d t (h.q49_t_mem_yamadaR₅ hW d hK hQ)))) fun x hx => ?_
  obtain ⟨c, hc, n, hn, rfl⟩ := exists_centralizer_mul_of_le_J d (le_refl d.J)
    (h.q49_yamadaP_le_yamadaR₈ d hK hD) (q49_yamadaR₈_le_normalizer_yamadaP d t)
    (h.q49_J_le_normalizer_yamadaR₈ d hK hD) (h.q49_J_le_normalizer_yamadaP d hK hD)
    (q49_isPGroup_yamadaR₈ d t) hx fun j hj => by
      rw [show x⁻¹ * (j * x * j⁻¹) = ⁅x⁻¹, j⁆ by simp only [commutatorElement_def]; group]
      exact Subgroup.commutator_mem_commutator (inv_mem hx) hj
  exact mul_mem (mem_sup_right (h.q49_yamadaR₈_inf_centralizer_J_le hW d hK hQ hc))
    (mem_sup_left hn)

theorem q49_t_mem_yamadaC₇ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : t ∈ yamadaC₇ d t := by
  have : t ∈ yamadaCstar d t :=
    (h.yamadaCstar_eq d hK hD) ▸ h.yamadaC₁_le_yamadaV d hK hD (h.t_mem_yamadaC₁ d hK)
  exact this

theorem q49_J_le_normalizer_yamadaM₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.J ≤ normalizer (yamadaM₆ d t : Set G) := fun j hj => by
  have hD := hQ.doubling
  obtain ⟨-, hHM, -, -⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  have hJM₅ : ∀ j ∈ d.J, j ∈ normalizer (yamadaM₅ d t : Set G) := fun j hj =>
    hHM (h.q49_J_le_normalizer_yamadaR₅ d hK hD hj)
  refine Common.mem_normalizer_sup (hJM₅ j hj) ?_
  have hwJ := h.wb_mem_normalizer_J d hK
  have hj' : d.wb⁻¹ * j * d.wb ∈ d.J := by
    have := (mem_normalizer_iff.1 (inv_mem hwJ) j).1 hj
    rwa [inv_inv] at this
  rw [mem_normalizer_iff]
  intro y
  rw [mem_map_conj_iff, mem_map_conj_iff]
  have e : d.wb⁻¹ * (j * y * j⁻¹) * d.wb =
      (d.wb⁻¹ * j * d.wb) * (d.wb⁻¹ * y * d.wb) * (d.wb⁻¹ * j * d.wb)⁻¹ := by group
  rw [e]
  exact mem_normalizer_iff.1 (hJM₅ _ hj') (d.wb⁻¹ * y * d.wb)

theorem q49_J_le_normalizer_yamadaS₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.J ≤ normalizer (yamadaS₆ d t : Set G) := fun _ hj =>
  Common.mem_normalizer_sup (h.q49_J_le_normalizer_yamadaM₆ hW d hK hQ hj)
    (h.J_le_centralizer_inf_normalizer_S d hj).2

theorem q49_yamadaS₆_le_yamadaR₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaS₆ d t ≤ yamadaR₆ d t :=
  sup_le (((h.yamada_5_44_1 hW d hK hQ).1.1 ▸ le_sup_left : yamadaM₆ d t ≤ yamadaL₆ d t).trans
    le_sup_left) le_sup_right

theorem q49_yamadaS₅_le_yamadaS₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaS₅ d t ≤ yamadaS₆ d t := by
  obtain ⟨⟨hS, -, -⟩, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨-, -, hF₅M, -⟩ := h.q49_yamadaS₅_facts hW d hK hQ
  rw [hS]
  exact sup_le (S_le_yamadaS₆ d t) (hF₅M.trans ((yamadaM₅_le_yamadaM₆ d t).trans
    (yamadaM₆_le_yamadaS₆ d t)))

theorem q49_le_yamadaP_of_forall (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {Q : Subgroup G}
    (hQR : Q ≤ yamadaR₈ d t) (hJQ : d.J ≤ normalizer (Q : Set G)) (htQ : t ∉ Q) :
    Q ≤ yamadaP d t := by
  have hD := hQ.doubling
  intro σ hσ
  obtain ⟨c, hc, n, hn, rfl⟩ := exists_centralizer_mul_of_le_J d (A := d.J) (M := Q)
    (N := yamadaP d t ⊓ Q) (le_refl d.J) inf_le_right
    (fun x hx => Common.mem_normalizer_inf (q49_yamadaR₈_le_normalizer_yamadaP d t (hQR hx))
      (Subgroup.le_normalizer hx))
    hJQ (fun j hj => Common.mem_normalizer_inf (h.q49_J_le_normalizer_yamadaP d hK hD hj) (hJQ hj))
    ((q49_isPGroup_yamadaR₈ d t).to_le hQR) hσ fun j hj => by
      refine Subgroup.mem_inf.2 ⟨?_, mul_mem (inv_mem hσ) ((mem_normalizer_iff.1 (hJQ hj) σ).1 hσ)⟩
      rw [show σ⁻¹ * (j * σ * j⁻¹) = ⁅σ⁻¹, j⁆ by simp only [commutatorElement_def]; group]
      exact Subgroup.commutator_mem_commutator (hQR (inv_mem hσ)) hj
  obtain ⟨hcQ, hcJ⟩ := Subgroup.mem_inf.1 hc
  have hct := h.q49_yamadaR₈_inf_centralizer_J_le hW d hK hQ (Subgroup.mem_inf.2 ⟨hQR hcQ, hcJ⟩)
  rcases q49_eq_one_or_eq_of_mem_zpowers h.t_mul_t hct with h1 | h1
  · rw [h1, one_mul]
    exact (Subgroup.mem_inf.1 hn).1
  · exact absurd (h1 ▸ hcQ) htQ

theorem q49_yamadaS₅_le_yamadaP (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaS₅ d t ≤ yamadaP d t := by
  have hD := hQ.doubling
  obtain ⟨-, -, -, hHS⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  exact h.q49_le_yamadaP_of_forall hW d hK hQ
    ((h.q49_yamadaS₅_le_yamadaR₅ hW d hK hQ).trans (q49_yamadaR₅_le_yamadaR₈ d t))
    ((h.q49_J_le_normalizer_yamadaR₅ d hK hD).trans hHS)
    ((h.yamada_5_37_2 hW d hK hQ).2.1.2.2)

theorem q49_yamadaS₆_le_yamadaP (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaS₆ d t ≤ yamadaP d t :=
  h.q49_le_yamadaP_of_forall hW d hK hQ
    ((h.q49_yamadaS₆_le_yamadaR₆ hW d hK hQ).trans
      ((h.q49_yamadaV₈_eq hW d hK hQ) ▸ h.q49_yamadaR₆_le_yamadaV₈ hW d hK hQ))
    (h.q49_J_le_normalizer_yamadaS₆ hW d hK hQ) (h.yamada_5_44_1 hW d hK hQ).2.2.2

theorem q49_yamadaR₂_eq_sup_yamadaS₂_yamadaC₁ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₂ d t = yamadaS₂ d t ⊔ yamadaC₁ d t := by
  obtain ⟨-, -, -, -, -, -, -, -, hMS, -⟩ := d.inclusions
  have hS₂R₂ : yamadaS₂ d t ≤ yamadaR₂ d t :=
    sup_le le_sup_right (h.yamadaY₂_le_yamadaR₂ d hK hD)
  refine le_antisymm ?_ (sup_le hS₂R₂ (h.yamadaC₁_le_yamadaR₂ d hK))
  rw [(h.yamada_5_6_1 d hK).2.2.2.1, h.yamadaL₂_eq_sup d hK hD]
  exact sup_le (sup_le ((sup_le_sup_right hMS _).trans le_sup_left)
    (((zpowers_le).2 (h.t_mem_yamadaC₁ d hK)).trans le_sup_right)) le_sup_right

theorem q49_yamadaR₇_inf_normalizer_yamadaS₂_le (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₇ d t ⊓ normalizer (yamadaS₂ d t : Set G) ≤ yamadaR₅ d t := fun x hx => by
  have hD := hQ.doubling
  obtain ⟨hx7, hxS₂⟩ := Subgroup.mem_inf.1 hx
  have hxR₈ : x ∈ yamadaR₈ d t :=
    ((h.q49_yamadaV₈_eq hW d hK hQ) ▸ h.q49_yamadaR₇_le_yamadaV₈ hW d hK hQ) hx7
  have hxR₂ : x ∈ normalizer (yamadaR₂ d t : Set G) := by
    rw [h.q49_yamadaR₂_eq_sup_yamadaS₂_yamadaC₁ d hK hD]
    exact Common.mem_normalizer_sup hxS₂ (h.yamadaRstar_le_normalizer d hx7)
  rw [← q49_yamadaR₈_inf_normalizer_yamadaR₂ d t]
  exact Subgroup.mem_inf.2 ⟨hxR₈, hxR₂⟩

theorem q49_mem_yamadaR₆_of_crossed_mem (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {y : G}
    (hy : y ∈ q49_yamadaV₈ d t) (hκ : t * y * t * y⁻¹ ∈ yamadaM₅ d t) : y ∈ yamadaR₆ d t := by
  obtain ⟨⟨-, hM, -⟩, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨hHF, -, -, -⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  obtain ⟨-, -, -, -, -, -, -, -, hMS, -⟩ := d.inclusions
  have hSF₅ := h.q49_S_le_normalizer_yamadaF₅ hW d hK hQ
  rw [hM] at hκ
  obtain ⟨m, hm, f, hf, e⟩ := Common.exists_mul_of_le_normalizer' (hMS.trans hSF₅) _ hκ
  obtain ⟨a, ha, f', hf', ea⟩ := h.q49_exists_mem_yamadaR₆_crossed hW d hK hQ hm
  have e2 : t * a * t * a⁻¹ = (t * y * t * y⁻¹) * (f⁻¹ * f') := by
    rw [ea, e]
    group
  have haV := h.q49_yamadaR₆_le_yamadaV₈ hW d hK hQ ha
  have hκ' := q49_crossed_inv_mul_mem h.t_mul_t (hHF (q49_yamadaV₈_le_normalizer d t haV))
    (mul_mem (inv_mem hf) hf') e2
  have hr := (h.q49_crossed_mem_yamadaF₅_iff hW d hK hQ (mul_mem (inv_mem haV) hy)).1 hκ'
  have hyy : y = a * (a⁻¹ * y) := by group
  rw [hyy]
  exact mul_mem ha (h.yamadaR₅_le_yamadaR₆ hW d hK hQ hr)

theorem q49_mem_yamadaR₇_of_crossed_mem (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {y : G}
    (hy : y ∈ q49_yamadaV₈ d t) (hκ : t * y * t * y⁻¹ ∈ yamadaD₅ d t) : y ∈ yamadaR₇ d t := by
  have hD := hQ.doubling
  obtain ⟨⟨-, -, hDD⟩, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨hHF, -, -, -⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  obtain ⟨-, -, -, -, -, -, -, hDS, -⟩ := d.inclusions
  have hSF₅ := h.q49_S_le_normalizer_yamadaF₅ hW d hK hQ
  rw [hDD] at hκ
  obtain ⟨δ, hδ, f, hf, e⟩ := Common.exists_mul_of_le_normalizer' (hDS.trans hSF₅) _ hκ
  obtain ⟨a, ha, f', hf', ea⟩ := h.q49_exists_mem_yamadaR₇_crossed hW d hK hQ hδ
  have e2 : t * a * t * a⁻¹ = (t * y * t * y⁻¹) * (f⁻¹ * f') := by
    rw [ea, e]
    group
  have haV := h.q49_yamadaR₇_le_yamadaV₈ hW d hK hQ ha
  have hκ' := q49_crossed_inv_mul_mem h.t_mul_t (hHF (q49_yamadaV₈_le_normalizer d t haV))
    (mul_mem (inv_mem hf) hf') e2
  have hr := (h.q49_crossed_mem_yamadaF₅_iff hW d hK hQ (mul_mem (inv_mem haV) hy)).1 hκ'
  have hyy : y = a * (a⁻¹ * y) := by group
  rw [hyy]
  exact mul_mem ha (h.q49_yamadaR₅_le_yamadaR₇ hW d hK hD hr)

theorem q49_J₄_conj_mem_yamadaM₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {j σ : G}
    (hj : j ∈ d.Ji 3) (hσ : σ ∈ yamadaS₅ d t) : σ⁻¹ * (j * σ * j⁻¹) ∈ yamadaM₅ d t := by
  have hD := hQ.doubling
  obtain ⟨⟨hS, -, -⟩, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨hSS₅, -, hF₅M, -, hMM₅, -⟩ := h.q49_yamadaS₅_facts hW d hK hQ
  obtain ⟨-, -, -, -, -, hFD, hFM, hDS, hMS, -⟩ := d.inclusions
  obtain ⟨-, -, -, -, haD, -, -, -, hDMS⟩ := d.yamada_defs
  have hSF₅ := h.q49_S_le_normalizer_yamadaF₅ hW d hK hQ
  have hJJ : d.Ji 3 ≤ d.J := d.image_mono inf_le_left
  obtain ⟨hHF, hHM, -, -⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  have hjH := h.q49_J_le_normalizer_yamadaR₅ d hK hD (hJJ hj)
  rw [hS] at hσ
  obtain ⟨s, hs, f₀, hf₀, rfl⟩ := Common.exists_mul_of_le_normalizer' hSF₅ σ hσ
  have hSsup : d.S ≤ d.M ⊔ d.rootGroup g2a :=
    hDMS.ge.trans (sup_le (haD.ge.trans (sup_le le_sup_right (hFM.trans le_sup_left))) le_sup_left)
  have hSb : d.rootGroup g2a ≤ d.S := (le_sup_left.trans haD.le).trans hDS
  obtain ⟨m, hm, u, hu, rfl⟩ := Common.exists_mul_of_le_normalizer
    (fun x hx => d.S_le_normalizers.2.2.2.2.2.2 (hSb hx)) s (hSsup hs)
  have huC : j * u = u * j :=
    mem_centralizer_iff.1 (Q44.rootGroup_yamadaRoot_le_centralizer_Ji d 3 hu) j hj
  have huM₅ : u ∈ normalizer (yamadaM₅ d t : Set G) :=
    hHM (Subgroup.le_normalizer ((hSS₅.trans (h.q49_yamadaS₅_le_yamadaR₅ hW d hK hQ)) (hSb hu)))
  exact q49_conj_mem (hMM₅ hm) (hF₅M hf₀) (hF₅M ((mem_normalizer_iff.1 (hHF hjH) f₀).1 hf₀))
    (hHM hjH) huM₅ huC

theorem q49_J₃_conj_mem_yamadaD₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {j σ : G}
    (hj : j ∈ d.Ji 2) (hσ : σ ∈ yamadaS₅ d t) : σ⁻¹ * (j * σ * j⁻¹) ∈ yamadaD₅ d t := by
  have hD := hQ.doubling
  obtain ⟨⟨hS, -, -⟩, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨hSS₅, -, -, hF₅D, -, hDD₅, -⟩ := h.q49_yamadaS₅_facts hW d hK hQ
  obtain ⟨-, -, -, -, -, hFD, hFM, hDS, hMS, -⟩ := d.inclusions
  obtain ⟨-, -, -, -, -, hrM, -, -, hDMS⟩ := d.yamada_defs
  have hSF₅ := h.q49_S_le_normalizer_yamadaF₅ hW d hK hQ
  have hJJ : d.Ji 2 ≤ d.J := d.image_mono inf_le_left
  obtain ⟨hHF, -, hHD, -⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  have hjH := h.q49_J_le_normalizer_yamadaR₅ d hK hD (hJJ hj)
  rw [hS] at hσ
  obtain ⟨s, hs, f₀, hf₀, rfl⟩ := Common.exists_mul_of_le_normalizer' hSF₅ σ hσ
  have hSsup : d.S ≤ d.D ⊔ d.rootGroup g2r :=
    hDMS.ge.trans (sup_le le_sup_left (hrM.ge.trans (sup_le le_sup_right (hFD.trans le_sup_left))))
  have hSa : d.rootGroup g2r ≤ d.S := (le_sup_left.trans hrM.le).trans hMS
  obtain ⟨δ, hδ, v, hv, rfl⟩ := Common.exists_mul_of_le_normalizer
    (fun x hx => d.S_le_normalizers.2.2.2.2.2.1 (hSa hx)) s (hSsup hs)
  have hvC : j * v = v * j := by
    have : v ∈ d.S ⊓ centralizer (d.Ji 2 : Set G) := by
      rw [S_inf_centralizer_Ji_of_four_le d (hK ▸ h.four_le) 2 (Or.inr (by decide))]
      exact hv
    exact mem_centralizer_iff.1 (Subgroup.mem_inf.1 this).2 j hj
  have hvD₅ : v ∈ normalizer (yamadaD₅ d t : Set G) :=
    hHD (Subgroup.le_normalizer ((hSS₅.trans (h.q49_yamadaS₅_le_yamadaR₅ hW d hK hQ)) (hSa hv)))
  exact q49_conj_mem (hDD₅ hδ) (hF₅D hf₀) (hF₅D ((mem_normalizer_iff.1 (hHF hjH) f₀).1 hf₀))
    (hHD hjH) hvD₅ hvC

theorem q49_crossed_conj_mem_yamadaF₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ yamadaR₈ d t ⊓ normalizer (yamadaS₂ d t : Set G)) {Q Q₅ A : Subgroup G}
    (hAJ : A ≤ d.J)
    (hQV : ∀ y ∈ q49_yamadaV₈ d t, t * y * t * y⁻¹ ∈ Q₅ → y ∈ Q)
    (hQS₂ : Q ⊓ normalizer (yamadaS₂ d t : Set G) ≤ yamadaR₅ d t)
    (hAQ₅ : ∀ j ∈ A, ∀ σ ∈ yamadaS₅ d t, σ⁻¹ * (j * σ * j⁻¹) ∈ Q₅)
    (hxQ₅ : x ∈ normalizer (Q₅ : Set G)) :
    ∀ j ∈ A, (t * x * t * x⁻¹)⁻¹ * (j * (t * x * t * x⁻¹) * j⁻¹) ∈ yamadaF₅ d t := by
  have hD := hQ.doubling
  obtain ⟨hHF, -, -, -⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  obtain ⟨hx8, hxS₂⟩ := Subgroup.mem_inf.1 hx
  have hxV := h.q49_yamadaR₈_le_yamadaV₈ hW d hK hQ hx8
  have hxH : x ∈ normalizer (yamadaR₅ d t : Set G) := yamadaR₈_le d t hx8
  have hσ := h.q49_crossed_mem_yamadaS₅ hW d hK hQ hxH
  intro j hj
  have hjJ := hAJ hj
  have hjt : j * t = t * j :=
    mem_centralizer_singleton_iff.1 (h.J_le_centralizer_inf_normalizer_S d hjJ).1
  have hjx : j * x * j⁻¹ ∈ yamadaR₈ d t :=
    (mem_normalizer_iff.1 (h.q49_J_le_normalizer_yamadaR₈ d hK hD hjJ) x).1 hx8
  have hjS₂ : j ∈ normalizer (yamadaS₂ d t : Set G) := h.J_le_normalizer_yamadaS₂ d hK hD hjJ
  have hy8 : x⁻¹ * (j * x * j⁻¹) ∈ yamadaR₈ d t := mul_mem (inv_mem hx8) hjx
  have hyS₂ : x⁻¹ * (j * x * j⁻¹) ∈ normalizer (yamadaS₂ d t : Set G) :=
    mul_mem (inv_mem hxS₂) (mul_mem (mul_mem hjS₂ hxS₂) (inv_mem hjS₂))
  have hyV := h.q49_yamadaR₈_le_yamadaV₈ hW d hK hQ hy8
  have hκy := q49_crossed_inv_conj (x := x) h.t_mul_t hjt
  have hQ₅mem : x⁻¹ * ((t * x * t * x⁻¹)⁻¹ * (j * (t * x * t * x⁻¹) * j⁻¹)) * x ∈ Q₅ := by
    have h1 := hAQ₅ j hj _ hσ
    have := (mem_normalizer_iff.1 (inv_mem hxQ₅) _).1 h1
    simpa [mul_assoc] using this
  have hyQ : x⁻¹ * (j * x * j⁻¹) ∈ Q := hQV _ hyV (hκy ▸ hQ₅mem)
  have hy5 : x⁻¹ * (j * x * j⁻¹) ∈ yamadaR₅ d t := hQS₂ (Subgroup.mem_inf.2 ⟨hyQ, hyS₂⟩)
  have hκF₅ := (h.q49_crossed_mem_yamadaF₅_iff hW d hK hQ hyV).2 hy5
  rw [hκy] at hκF₅
  have := (mem_normalizer_iff.1 (hHF hxH) _).1 hκF₅
  simpa [mul_assoc] using this

theorem q49_yamadaR₈_inf_normalizer_yamadaS₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₈ d t ⊓ normalizer (yamadaS₂ d t : Set G) = yamadaR₅ d t := by
  have hD := hQ.doubling
  obtain ⟨hHF, hHM, hHD, -⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  obtain ⟨⟨hS, -, -⟩, hSF, -, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨-, hFF₅, -⟩ := h.q49_yamadaS₅_facts hW d hK hQ
  obtain ⟨-, -, -, -, -, hFD, hFM, -⟩ := d.inclusions
  obtain ⟨h42, h42S, -⟩ := h.yamada_5_42 hW d hK hQ
  refine le_antisymm (fun x hx => ?_)
    (le_inf (q49_yamadaR₅_le_yamadaR₈ d t) (h42S.ge.trans inf_le_right))
  obtain ⟨hx8, hxS₂⟩ := Subgroup.mem_inf.1 hx
  have hxV := h.q49_yamadaR₈_le_yamadaV₈ hW d hK hQ hx8
  have hxH : x ∈ normalizer (yamadaR₅ d t : Set G) := yamadaR₈_le d t hx8
  have hJ₄J : d.Ji 3 ≤ d.J := d.image_mono inf_le_left
  have hJ₃J : d.Ji 2 ≤ d.J := d.image_mono inf_le_left
  have h4 := h.q49_crossed_conj_mem_yamadaF₅ hW d hK hQ hx hJ₄J
    (fun y hy hκ => h.q49_mem_yamadaR₆_of_crossed_mem hW d hK hQ hy hκ) h42S.le
    (fun j hj σ hσ => h.q49_J₄_conj_mem_yamadaM₅ hW d hK hQ hj hσ) (hHM hxH)
  have h3 := h.q49_crossed_conj_mem_yamadaF₅ hW d hK hQ hx hJ₃J
    (fun y hy hκ => h.q49_mem_yamadaR₇_of_crossed_mem hW d hK hQ hy hκ)
    (h.q49_yamadaR₇_inf_normalizer_yamadaS₂_le hW d hK hQ)
    (fun j hj σ hσ => h.q49_J₃_conj_mem_yamadaD₅ hW d hK hQ hj hσ) (hHD hxH)
  have hSF₅ := h.q49_S_le_normalizer_yamadaF₅ hW d hK hQ
  have hκS₅ := h.q49_crossed_mem_yamadaS₅ hW d hK hQ hxH
  rw [hS] at hκS₅
  obtain ⟨s, hs, f₀, hf₀, hσf⟩ := Common.exists_mul_of_le_normalizer' hSF₅ _ hκS₅
  have key : ∀ j ∈ d.J, (t * x * t * x⁻¹)⁻¹ * (j * (t * x * t * x⁻¹) * j⁻¹) ∈ yamadaF₅ d t →
      s⁻¹ * (j * s * j⁻¹) ∈ d.F := by
    intro j hj hjF
    have hjH := h.q49_J_le_normalizer_yamadaR₅ d hK hD hj
    rw [hσf] at hjF
    have e : s⁻¹ * (j * s * j⁻¹) =
        f₀ * ((s * f₀)⁻¹ * (j * (s * f₀) * j⁻¹)) * (j * f₀ * j⁻¹)⁻¹ := by group
    rw [← hSF]
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hs)
      ((mem_normalizer_iff.1 (h.J_le_centralizer_inf_normalizer_S d hj).2 s).1 hs), ?_⟩
    rw [e]
    exact mul_mem (mul_mem hf₀ hjF) (inv_mem ((mem_normalizer_iff.1 (hHF hjH) f₀).1 hf₀))
  have hsD : s ∈ d.D := h.q49_mem_D_of_forall_J₄ d hK hQ hs fun j hj =>
    hFD (key j (hJ₄J hj) (h4 j hj))
  have hsM : s ∈ d.M := h.q49_mem_M_of_forall_J₃ d hK hQ hs fun j hj =>
    hFM (key j (hJ₃J hj) (h3 j hj))
  have hsF : s ∈ d.F := by
    rw [← (d.yamada_defs).2.2.2.2.2.2.2.1]
    exact Subgroup.mem_inf.2 ⟨hsD, hsM⟩
  have hκF₅ : t * x * t * x⁻¹ ∈ yamadaF₅ d t := by
    rw [hσf]
    exact mul_mem (hFF₅ hsF) hf₀
  exact (h.q49_crossed_mem_yamadaF₅_iff hW d hK hQ hxV).1 hκF₅

theorem yamadaP_facts (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.J ≤ normalizer (yamadaR₈ d t : Set G) ∧ yamadaP d t ≤ yamadaR₈ d t ∧
      yamadaR₈ d t ≤ normalizer (yamadaP d t : Set G) ∧ yamadaS₅ d t ≤ yamadaS₆ d t ∧
      yamadaS₆ d t ≤ yamadaP d t ∧ yamadaP d t ⊓ yamadaR₅ d t = yamadaS₅ d t ∧
      yamadaP d t ⊓ yamadaR₆ d t = yamadaS₆ d t := by
  have hD := hQ.doubling
  obtain ⟨hR₅, htS₅, -⟩ := (h.yamada_5_37_2 hW d hK hQ).2.1
  obtain ⟨hR₆, htS₆, -⟩ := (h.yamada_5_44_1 hW d hK hQ).2
  exact ⟨h.q49_J_le_normalizer_yamadaR₈ d hK hD, h.q49_yamadaP_le_yamadaR₈ d hK hD,
    q49_yamadaR₈_le_normalizer_yamadaP d t, h.q49_yamadaS₅_le_yamadaS₆ hW d hK hQ,
    h.q49_yamadaS₆_le_yamadaP hW d hK hQ,
    q49_inf_eq_of_sup_zpowers h.t_mul_t hR₅ htS₅ (h.q49_yamadaS₅_le_yamadaP hW d hK hQ)
      (h.q49_t_not_mem_yamadaP hW d hK hQ),
    q49_inf_eq_of_sup_zpowers h.t_mul_t hR₆ htS₆ (h.q49_yamadaS₆_le_yamadaP hW d hK hQ)
      (h.q49_t_not_mem_yamadaP hW d hK hQ)⟩

theorem normalizer_inf_yamadaR₈ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₈ d t ⊓ normalizer (yamadaR₂ d t : Set G) = yamadaR₅ d t ∧
      yamadaR₈ d t ⊓ normalizer (yamadaS₂ d t : Set G) = yamadaR₅ d t :=
  ⟨q49_yamadaR₈_inf_normalizer_yamadaR₂ d t, h.q49_yamadaR₈_inf_normalizer_yamadaS₂ hW d hK hQ⟩

theorem yamada_5_49_1 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    normalizer (yamadaR₅ d t : Set G) =
        yamadaR₈ d t ⊔ (centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G)) ∧
      ((normalizer (yamadaR₅ d t : Set G) : Subgroup G) : Set G) = (yamadaR₈ d t : Set G) *
        ((centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) : Subgroup G) : Set G) ∧
      yamadaR₈ d t ⊓ centralizer ({t} : Set G) = yamadaR d t := by
  have hD := hQ.doubling
  obtain ⟨-, hset, hRR⟩ := h.yamada_5_27_1 hW d hK hD
  have hNC := h.q49_centralizer_inf_normalizer_S_le_normalizer_yamadaR₅ d hK hD
  have hmul : ((normalizer (yamadaR₅ d t : Set G) : Subgroup G) : Set G) =
      (yamadaR₈ d t : Set G) *
        ((centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) : Subgroup G) : Set G) := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, hv, hc⟩ := h.q49_exists_mem_yamadaV₈_inv_mul_mem hW d hK hQ hx
      have hc' : v⁻¹ * x ∈ ((normalizer (yamadaR₂ d t : Set G) : Subgroup G) : Set G) := hc
      rw [hset] at hc'
      obtain ⟨r, hr, c, hcc, e⟩ := Set.mem_mul.1 hc'
      refine Set.mem_mul.2 ⟨v * r, ?_, c, hcc, ?_⟩
      · exact (h.q49_yamadaV₈_le_yamadaR₈ hW d hK hQ)
          (mul_mem hv (h.q49_yamadaR₅_le_yamadaV₈ hW d hK hQ hr))
      · rw [mul_assoc, e, mul_inv_cancel_left]
    · rintro ⟨r, hr, c, hcc, rfl⟩
      exact mul_mem (yamadaR₈_le d t hr) (hNC hcc)
  refine ⟨le_antisymm (fun x hx => ?_) (sup_le (yamadaR₈_le d t) hNC), hmul, ?_⟩
  · have hx' : x ∈ ((normalizer (yamadaR₅ d t : Set G) : Subgroup G) : Set G) := hx
    rw [hmul] at hx'
    obtain ⟨r, hr, c, hcc, rfl⟩ := Set.mem_mul.1 hx'
    exact mul_mem (mem_sup_left hr) (mem_sup_right hcc)
  · refine le_antisymm (fun x hx => ?_) (le_inf ((hRR.ge.trans inf_le_left).trans
      (q49_yamadaR₅_le_yamadaR₈ d t)) (h.yamadaR_le_centralizer d))
    obtain ⟨hx8, hxC⟩ := Subgroup.mem_inf.1 hx
    have hxV := (h.q49_yamadaR₈_le_yamadaV₈ hW d hK hQ) hx8
    have hκ : t * x * t * x⁻¹ ∈ yamadaF₅ d t := by
      rw [show t * x * t * x⁻¹ = t * (x * t) * x⁻¹ by group,
        mem_centralizer_singleton_iff.1 hxC, show t * (t * x) * x⁻¹ = t * t by group,
        h.t_mul_t]
      exact one_mem _
    have hx5 := (h.q49_crossed_mem_yamadaF₅_iff hW d hK hQ hxV).1 hκ
    rw [← hRR]
    exact Subgroup.mem_inf.2 ⟨hx5, hxC⟩

theorem yamada_5_49_2 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₅ d t ≤ yamadaR₆ d t ∧ yamadaR₅ d t ≤ yamadaR₇ d t ∧
      yamadaR₆ d t ≤ yamadaR₈ d t ∧ yamadaR₇ d t ≤ yamadaR₈ d t ∧
      yamadaR₈ d t = yamadaR₆ d t ⊔ yamadaR₇ d t ∧
      yamadaR₆ d t ⊓ yamadaR₇ d t = yamadaR₅ d t ∧
      ElemModulo (yamadaR₅ d t) (yamadaR₈ d t) := by
  have hD := hQ.doubling
  have hVR := h.q49_yamadaV₈_eq hW d hK hQ
  have hR₅R₆ := h.yamadaR₅_le_yamadaR₆ hW d hK hQ
  have hR₅R₇ := h.q49_yamadaR₅_le_yamadaR₇ hW d hK hD
  have hR₆R₈ : yamadaR₆ d t ≤ yamadaR₈ d t := hVR ▸ h.q49_yamadaR₆_le_yamadaV₈ hW d hK hQ
  have hR₇R₈ : yamadaR₇ d t ≤ yamadaR₈ d t := hVR ▸ h.q49_yamadaR₇_le_yamadaV₈ hW d hK hQ
  refine ⟨hR₅R₆, hR₅R₇, hR₆R₈, hR₇R₈, le_antisymm (fun x hx => ?_) (sup_le hR₆R₈ hR₇R₈),
    le_antisymm (fun x hx => ?_) (le_inf hR₅R₆ hR₅R₇),
    hVR ▸ h.q49_elemModulo_yamadaR₅_yamadaV₈ hW d hK hQ⟩
  · have hxV : x ∈ q49_yamadaV₈ d t := hVR ▸ hx
    obtain ⟨b, hb, a, ha, f, hf, e⟩ := h.q49_exists_mem_yamadaR₇_mul_yamadaR₆_crossed hW d hK hQ
      (h.q49_crossed_mem_yamadaS₅ hW d hK hQ (q49_yamadaV₈_le_normalizer d t hxV))
    have hbaV : b * a ∈ q49_yamadaV₈ d t := mul_mem (h.q49_yamadaR₇_le_yamadaV₈ hW d hK hQ hb)
      (h.q49_yamadaR₆_le_yamadaV₈ hW d hK hQ ha)
    obtain ⟨hHF, -, -, -⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
    have hκ := q49_crossed_inv_mul_mem h.t_mul_t (hHF (q49_yamadaV₈_le_normalizer d t hbaV)) hf e
    have hr := (h.q49_crossed_mem_yamadaF₅_iff hW d hK hQ (mul_mem (inv_mem hbaV) hxV)).1 hκ
    have : x = (b * a) * ((b * a)⁻¹ * x) := by group
    rw [this]
    exact mul_mem (mul_mem (mem_sup_right hb) (mem_sup_left ha)) (mem_sup_left (hR₅R₆ hr))
  · obtain ⟨hx6, hx7⟩ := Subgroup.mem_inf.1 hx
    have hκ : t * x * t * x⁻¹ ∈ yamadaM₅ d t ⊓ yamadaD₅ d t :=
      Subgroup.mem_inf.2 ⟨h.q49_crossed_mem_yamadaM₅ hW d hK hQ hx6,
        h.q49_crossed_mem_yamadaD₅ hW d hK hQ hx7⟩
    rw [h.q49_yamadaM₅_inf_yamadaD₅ hW d hK hQ] at hκ
    exact (h.q49_crossed_mem_yamadaF₅_iff hW d hK hQ
      (h.q49_yamadaR₆_le_yamadaV₈ hW d hK hQ hx6)).1 hκ

theorem yamada_5_49_3 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∃ _ : ((yamadaR₅ d t).subgroupOf (yamadaR₈ d t)).Normal,
      ∃ _ : (d.F.subgroupOf d.S).Normal,
        ∃ φ : yamadaR₈ d t ⧸ (yamadaR₅ d t).subgroupOf (yamadaR₈ d t) ≃*
          d.S ⧸ d.F.subgroupOf d.S,
        (∀ (x : yamadaR₈ d t) (s : d.S), ∀ y ∈ yamadaF₅ d t,
          (x : G) * t * (x : G)⁻¹ = t * s * y → φ (QuotientGroup.mk x) = QuotientGroup.mk s) ∧
        ∀ c ∈ centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G),
          ∀ (x : yamadaR₈ d t) (s : d.S), φ (QuotientGroup.mk x) = QuotientGroup.mk s →
            ∃ (hx : c * x * c⁻¹ ∈ yamadaR₈ d t) (hs : c * s * c⁻¹ ∈ d.S),
              φ (QuotientGroup.mk ⟨_, hx⟩) = QuotientGroup.mk ⟨_, hs⟩ := by
  have hD := hQ.doubling
  obtain ⟨hFn, Ψ, h1, h2⟩ := h.q49_exists_hom_yamadaV₈ hW d hK hQ
  have hVR : yamadaR₈ d t ≤ q49_yamadaV₈ d t := h.q49_yamadaR₈_le_yamadaV₈ hW d hK hQ
  obtain ⟨hHF, -, -, -⟩ := h.q49_normalizer_yamadaR₅_le_normalizers hW d hK hQ
  obtain ⟨hSS₅, -⟩ := h.q49_yamadaS₅_facts hW d hK hQ
  let Ψ' : yamadaR₈ d t →* d.S ⧸ d.F.subgroupOf d.S := Ψ.comp (Subgroup.inclusion hVR)
  have hΨ' : ∀ x : yamadaR₈ d t, Ψ' x = Ψ ⟨x, hVR x.2⟩ := fun _ => rfl
  have hker : Ψ'.ker = (yamadaR₅ d t).subgroupOf (yamadaR₈ d t) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, hΨ']
    constructor
    · intro hx
      obtain ⟨y, hy, e⟩ := h2 ⟨x, hVR x.2⟩ 1 (by rw [hx, QuotientGroup.mk_one])
      exact (h.q49_crossed_mem_yamadaF₅_iff hW d hK hQ (hVR x.2)).1 (by
        rw [e, OneMemClass.coe_one, one_mul]
        exact hy)
    · intro hx
      have hκ := (h.q49_crossed_mem_yamadaF₅_iff hW d hK hQ (hVR x.2)).2 hx
      have := h1 ⟨x, hVR x.2⟩ 1 _ hκ (by rw [OneMemClass.coe_one, one_mul])
      rwa [QuotientGroup.mk_one] at this
  have hsurj : Function.Surjective Ψ' := by
    intro q
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨v, hv, f, hf, e⟩ := h.q49_exists_mem_yamadaV₈_crossed hW d hK hQ (hSS₅ s.2)
    exact ⟨⟨v, (h.q49_yamadaV₈_eq hW d hK hQ) ▸ hv⟩, by rw [hΨ']; exact h1 ⟨v, hv⟩ s f hf e⟩
  have hN : ((yamadaR₅ d t).subgroupOf (yamadaR₈ d t)).Normal := hker ▸ Ψ'.normal_ker
  set φ := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective Ψ' hsurj) with hφdef
  have hφ : ∀ x : yamadaR₈ d t, φ (QuotientGroup.mk x) = Ψ' x := fun _ => rfl
  refine ⟨hN, hFn, φ, fun x s y hy e => ?_, fun c hc x s hxs => ?_⟩
  · rw [hφ, hΨ']
    refine h1 ⟨x, hVR x.2⟩ s y hy ?_
    have e2 : t * (t * (x : G) * t * (x : G)⁻¹) = t * ((s : G) * y) := by
      rw [← h.conj_t_eq_mul_crossed (x : G), e, mul_assoc]
    exact mul_left_cancel e2
  · rw [hφ, hΨ'] at hxs
    obtain ⟨y, hy, hκ⟩ := h2 ⟨x, hVR x.2⟩ s hxs
    obtain ⟨hct, hcS⟩ := Subgroup.mem_inf.1 hc
    have hcH := h.q49_centralizer_inf_normalizer_S_le_normalizer_yamadaR₅ d hK hD hc
    have hx' : c * (x : G) * c⁻¹ ∈ yamadaR₈ d t :=
      (mem_normalizer_iff.1 (le_normalizer_yamadaR₈ d t hcH) x).1 x.2
    have hs' : c * (s : G) * c⁻¹ ∈ d.S := (mem_normalizer_iff.1 hcS s).1 s.2
    refine ⟨hx', hs', ?_⟩
    rw [hφ, hΨ']
    refine h1 ⟨c * x * c⁻¹, hVR hx'⟩ ⟨c * s * c⁻¹, hs'⟩ (c * y * c⁻¹)
      ((mem_normalizer_iff.1 (hHF hcH) y).1 hy) ?_
    have hct' : c * t = t * c := mem_centralizer_singleton_iff.1 hct
    have hct2 : c⁻¹ * t * c = t := by rw [mul_assoc, ← hct', inv_mul_cancel_left]
    show t * (c * (x : G) * c⁻¹) * t * (c * (x : G) * c⁻¹)⁻¹ = (c * (s : G) * c⁻¹) * (c * y * c⁻¹)
    calc t * (c * (x : G) * c⁻¹) * t * (c * (x : G) * c⁻¹)⁻¹ =
          (t * c) * x * (c⁻¹ * t * c) * (x : G)⁻¹ * c⁻¹ := by group
      _ = c * (t * (x : G) * t * (x : G)⁻¹) * c⁻¹ := by rw [← hct', hct2]; group
      _ = c * (s * y) * c⁻¹ := by rw [hκ]
      _ = (c * (s : G) * c⁻¹) * (c * y * c⁻¹) := by group

theorem yamada_5_51 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (yamadaP d t ⊔ zpowers t = yamadaR₈ d t ∧ t ∈ normalizer (yamadaP d t : Set G) ∧
      t ∉ yamadaP d t) ∧
    (yamadaS₇ d t ⊔ zpowers t = yamadaR₇ d t ∧ t ∈ normalizer (yamadaS₇ d t : Set G) ∧
      t ∉ yamadaS₇ d t) ∧
    (yamadaD₇ d t ⊔ zpowers t = yamadaC₇ d t ∧ t ∈ normalizer (yamadaD₇ d t : Set G) ∧
      t ∉ yamadaD₇ d t) := by
  have hD := hQ.doubling
  have hR := h.q49_yamadaP_sup_zpowers hW d hK hQ
  have htR₅ := h.q49_t_mem_yamadaR₅ hW d hK hQ
  have htP : t ∈ normalizer (yamadaP d t : Set G) :=
    q49_yamadaR₈_le_normalizer_yamadaP d t (q49_yamadaR₅_le_yamadaR₈ d t htR₅)
  have htnP := h.q49_t_not_mem_yamadaP hW d hK hQ
  have htR₇ : t ∈ yamadaR₇ d t := h.q49_yamadaR₅_le_yamadaR₇ hW d hK hD htR₅
  have htC₇ := h.q49_t_mem_yamadaC₇ d hK hD
  have hR₇R₈ : yamadaR₇ d t ≤ yamadaR₈ d t :=
    (h.q49_yamadaV₈_eq hW d hK hQ) ▸ h.q49_yamadaR₇_le_yamadaV₈ hW d hK hQ
  have hC₇R₇ : yamadaC₇ d t ≤ yamadaR₇ d t := le_sup_left
  refine ⟨⟨hR, htP, htnP⟩, ⟨q49_inf_sup_zpowers_eq hR htP hR₇R₈ htR₇,
    Common.mem_normalizer_inf htP (Subgroup.le_normalizer htR₇), fun ht => htnP ht.1⟩,
    ⟨q49_inf_sup_zpowers_eq hR htP (hC₇R₇.trans hR₇R₈) htC₇,
    Common.mem_normalizer_inf htP (Subgroup.le_normalizer htC₇), fun ht => htnP ht.1⟩⟩

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
