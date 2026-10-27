module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYEleven

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Defs

variable {G : Type*} [Group G]
  {L : Subgroup G} {K : Type} [Field K]

@[expose] noncomputable def yamadaCstar (d : G2Data L K) (t : G) : Subgroup G :=
  pCoreOf 2 (normalizer (yamadaC₁ d t : Set G))

@[expose] noncomputable def yamadaRstar (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaCstar d t ⊔ d.S

end Defs

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

@[expose] noncomputable def yamadaV (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : Subgroup G :=
  Common.centralizerMod (normalizer (yamadaC₁ d t : Set G)) (yamadaD₁ d t) (yamadaU₁ d t)
    (fun _ hg y hy => (mem_normalizer_iff.1 ((h.normalizer_yamadaC₁_le d hK hD).1 hg) y).1 hy)
    (fun _ hg b hb => (mem_normalizer_iff.1 ((h.normalizer_yamadaC₁_le d hK hD).2
      ((h.normalizer_yamadaC₁_le d hK hD).1 hg)) b).1 hb)

theorem mem_yamadaV (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x : G} :
    x ∈ h.yamadaV d hK hD ↔ x ∈ normalizer (yamadaC₁ d t : Set G) ∧
      ∀ y ∈ yamadaD₁ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaU₁ d t := Iff.rfl

theorem yamadaC₁_le_yamadaV (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaC₁ d t ≤ h.yamadaV d hK hD := by
  obtain ⟨-, hUU₁, -⟩ := hD.spec
  intro c hc
  refine (h.mem_yamadaV d hK hD).2 ⟨le_normalizer hc, fun y hy => hUU₁ ?_⟩
  have := ((h.elemModulo_U_yamadaC₁ d hK) c hc y (h.yamadaD₁_le_yamadaC₁ d hK hy)).2
  rwa [commutatorElement_def] at this

theorem crossed_mem_yamadaD₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x : G} (hx : x ∈ normalizer (yamadaC₁ d t : Set G)) :
    t * x * t * x⁻¹ ∈ yamadaD₁ d t := by
  obtain ⟨δ, hδ, e⟩ := h.exists_conj_t_eq d hK hD hx
  have htt := h.t_mul_t
  rw [show t * x * t * x⁻¹ = t * (x * t * x⁻¹) by group, e, ← mul_assoc, htt, one_mul]
  exact hδ

theorem crossed_mul_mem (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x y : G} (hx : x ∈ h.yamadaV d hK hD)
    (hy : y ∈ normalizer (yamadaC₁ d t : Set G)) :
    (t * x * t * x⁻¹ * (t * y * t * y⁻¹))⁻¹ * (t * (x * y) * t * (x * y)⁻¹) ∈ yamadaU₁ d t := by
  obtain ⟨-, hxc⟩ := (h.mem_yamadaV d hK hD).1 hx
  have hδy := h.crossed_mem_yamadaD₁ d hK hD hy
  have hD₁U₁ := (h.normalizer_yamadaC₁_le d hK hD).2
  have hδyN : t * y * t * y⁻¹ ∈ normalizer (yamadaU₁ d t : Set G) :=
    hD₁U₁ (le_normalizer hδy)
  have h1 := hxc _ hδy
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  have e : (t * x * t * x⁻¹ * (t * y * t * y⁻¹))⁻¹ * (t * (x * y) * t * (x * y)⁻¹) =
      (t * y * t * y⁻¹)⁻¹ * (x * (t⁻¹ * y * t * y⁻¹) * x⁻¹ * (t * y * t * y⁻¹)⁻¹) *
        (t * y * t * y⁻¹)⁻¹⁻¹ := by group
  rw [e, htinv]
  exact (mem_normalizer_iff.1 (inv_mem hδyN) _).1 h1

theorem yamadaV_inf_normalizer_tU (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x : G} (hxV : x ∈ h.yamadaV d hK hD)
    (hxN : x ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G)) : x ∈ yamadaC₁ d t := by
  obtain ⟨-, -, -, h4⟩ := h.two_core_C₁ d hK
  obtain ⟨c, hc, y, hy, rfl⟩ := h4 x hxN
  have hcV : c ∈ h.yamadaV d hK hD := by
    have := mul_mem hxV (inv_mem (h.yamadaC₁_le_yamadaV d hK hD hy))
    rwa [mul_inv_cancel_right] at this
  obtain ⟨-, hcc⟩ := (h.mem_yamadaV d hK hD).1 hcV
  have hcL : c ∈ normalizer (L : Set G) := h.centralizer_le_normalizer hc.1
  have hD₁N : yamadaD₁ d t ≤ normalizer (yamadaU₁ d t : Set G) :=
    le_normalizer.trans (h.normalizer_yamadaC₁_le d hK hD).2
  have hDD₁ : d.D ≤ yamadaD₁ d t := le_sup_right
  have hsec : ∀ z ∈ d.image (Model.D K), z⁻¹ * (c * z * c⁻¹) ∈ d.image (Model.U K) := by
    intro z hz
    have hzD₁ := hDD₁ hz
    have h1 : z⁻¹ * (c * z * c⁻¹) ∈ yamadaU₁ d t := by
      have := (mem_normalizer_iff.1 (hD₁N (inv_mem hzD₁)) _).1 (hcc z hzD₁)
      rwa [show z⁻¹ * (c * z * c⁻¹ * z⁻¹) * z⁻¹⁻¹ = z⁻¹ * (c * z * c⁻¹) by group] at this
    have h2 : z⁻¹ * (c * z * c⁻¹) ∈ L :=
      mul_mem (inv_mem (d.image_le _ hz)) ((mem_normalizer_iff.1 hcL z).1 (d.image_le _ hz))
    show z⁻¹ * (c * z * c⁻¹) ∈ d.U
    rw [← hD.inf_centralizer]
    exact ⟨h1, h.L_le_centralizer h2⟩
  have hcD := (d.act_sectionCentralizer_eq Model.U_le_D
    (Model.yamada_3_23_D_U hK h.two_le) hcL).1 hsec
  have hCLN : centralizer (L : Set G) ≤ normalizer (d.D : Set G) :=
    le_normalizer_of_conj_mem fun z hz w hw => by
      rw [← mem_centralizer_iff.1 hz w (d.image_le _ hw), mul_inv_cancel_right]
      exact hw
  obtain ⟨δ, hδ, z, hz, rfl⟩ := Common.exists_mul_of_le_normalizer hCLN c hcD
  have hzT : z ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
    refine Subgroup.mem_inf.2 ⟨hz, ?_⟩
    rw [show z = δ⁻¹ * (δ * z) by group]
    exact mul_mem (inv_mem (h.L_le_centralizer (d.image_le _ hδ))) hc.1
  rw [h.centralizer_L_inf] at hzT
  exact mul_mem (h.tD_le_yamadaC₁ d hK (mul_mem (mem_sup_left hδ) (mem_sup_right hzT))) hy

theorem mem_yamadaC₁_of_crossed_mem (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x : G} (hxV : x ∈ h.yamadaV d hK hD)
    (hx : t * x * t * x⁻¹ ∈ yamadaU₁ d t) : x ∈ yamadaC₁ d t := by
  obtain ⟨hxN, -⟩ := (h.mem_yamadaV d hK hD).1 hxV
  have hxU₁ := (h.normalizer_yamadaC₁_le d hK hD).2 ((h.normalizer_yamadaC₁_le d hK hD).1 hxN)
  obtain ⟨htN, -⟩ := h.t_mem_normalizer_yamadaU₁ d hK hD
  have htt := h.t_mul_t
  have hxT : x ∈ normalizer ((yamadaU₁ d t ⊔ zpowers t : Subgroup G) : Set G) := by
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    obtain ⟨u, hu, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer ((zpowers_le).2 htN) y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    have hxt : x * t * x⁻¹ = t * (t * x * t * x⁻¹) := by
      rw [show t * (t * x * t * x⁻¹) = (t * t) * x * t * x⁻¹ by group, htt, one_mul]
    rw [show x * (u * t ^ k) * x⁻¹ = x * u * x⁻¹ * (x * t * x⁻¹) ^ k by rw [conj_zpow]; group,
      hxt]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 hxU₁ u).1 hu))
      (zpow_mem (mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hx)) k)
  rw [h.yamada_5_17_1 d hK hD] at hxT
  exact h.yamadaV_inf_normalizer_tU d hK hD hxV hxT

theorem isPGroup_yamadaV (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : IsPGroup 2 (h.yamadaV d hK hD) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := h.yamadaV d hK hD with hVdef
  have hVN : ∀ x : V, (x : G) ∈ normalizer (yamadaC₁ d t : Set G) := fun x =>
    ((h.mem_yamadaV d hK hD).1 x.2).1
  have hU₁n : ((yamadaU₁ d t).subgroupOf (yamadaD₁ d t)).Normal :=
    normal_subgroupOf_iff_le_normalizer (hD.spec).1 |>.2
      (le_normalizer.trans (h.normalizer_yamadaC₁_le d hK hD).2)
  let δf : V → yamadaD₁ d t := fun x =>
    ⟨t * x * t * (x : G)⁻¹, h.crossed_mem_yamadaD₁ d hK hD (hVN x)⟩
  let ψ : V →* yamadaD₁ d t ⧸ (yamadaU₁ d t).subgroupOf (yamadaD₁ d t) :=
    { toFun := fun x => QuotientGroup.mk (δf x)
      map_one' := by
        apply (QuotientGroup.eq_one_iff _).2
        rw [mem_subgroupOf]
        change t * ((1 : V) : G) * t * ((1 : V) : G)⁻¹ ∈ yamadaU₁ d t
        rw [coe_one, mul_one, inv_one, mul_one, h.t_mul_t]
        exact one_mem _
      map_mul' := fun x y => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
        have h1 := inv_mem (h.crossed_mul_mem d hK hD x.2 (hVN y))
        rw [mul_inv_rev, inv_inv] at h1
        change (t * ((x * y : V) : G) * t * ((x * y : V) : G)⁻¹)⁻¹ *
          (t * (x : G) * t * (x : G)⁻¹ * (t * (y : G) * t * (y : G)⁻¹)) ∈ yamadaU₁ d t
        rw [coe_mul]
        exact h1 }
  have hC₁V : IsPGroup 2 ((yamadaC₁ d t).subgroupOf V) :=
    (LieType.BorelTits.pCoreOf_isPGroup 2 _).comap_of_injective V.subtype V.subtype_injective
  have hker : IsPGroup 2 ψ.ker := hC₁V.to_le fun x hx => by
    rw [mem_subgroupOf]
    refine h.mem_yamadaC₁_of_crossed_mem d hK hD x.2 ?_
    have h1 : QuotientGroup.mk (δf x) =
        (1 : yamadaD₁ d t ⧸ (yamadaU₁ d t).subgroupOf (yamadaD₁ d t)) := hx
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    exact h1
  have hQ : IsPGroup 2 (⊤ : Subgroup (yamadaD₁ d t ⧸ (yamadaU₁ d t).subgroupOf (yamadaD₁ d t))) :=
    ((h.isPGroup_yamadaD₁ d hK).to_quotient _).to_subgroup ⊤
  have hV := hQ.comap_of_ker_isPGroup ψ hker
  rw [comap_top] at hV
  exact hV.of_equiv Subgroup.topEquiv

theorem yamadaV_le_yamadaCstar (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : h.yamadaV d hK hD ≤ yamadaCstar d t :=
  LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (fun _ hx => ((h.mem_yamadaV d hK hD).1 hx).1)
    (le_normalizer_of_conj_mem fun _ hg _ hz => Common.conj_mem_centralizerMod hg hz)
    (h.isPGroup_yamadaV d hK hD)

theorem exists_mem_yamadaV_conj (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {δ : G} (hδ : δ ∈ yamadaD₁ d t) :
    ∃ x ∈ h.yamadaV d hK hD, ∃ u ∈ yamadaU₁ d t, x * t * x⁻¹ = t * δ * u := by
  have hU₁N : yamadaU₁ d t ≤ normalizer (d.D : Set G) :=
    (h.yamadaU₁_le_yamadaC₁ d hK hD).trans (h.yamadaC₁_le_normalizer_D d hK)
  rw [hD.D₁_eq] at hδ
  obtain ⟨a, ha, b, hb, rfl⟩ := Common.exists_mul_of_le_normalizer hU₁N δ hδ
  obtain ⟨x, hxN, hxc, w, hw, hxt⟩ := h.exists_conj_t_eq_mul_of_mem_D d hK hD ha
  refine ⟨x, (h.mem_yamadaV d hK hD).2 ⟨hxN, hxc⟩, b⁻¹ * w, mul_mem (inv_mem hb) hw, ?_⟩
  rw [hxt]
  group

theorem exists_mul_of_mem_normalizer_yamadaC₁ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {g : G}
    (hg : g ∈ normalizer (yamadaC₁ d t : Set G)) :
    ∃ x ∈ h.yamadaV d hK hD, ∃ y ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G),
      g = x * y := by
  have htt := h.t_mul_t
  obtain ⟨δ, hδ, hgt⟩ := h.exists_conj_t_eq d hK hD hg
  obtain ⟨x, hxV, u, hu, hxt⟩ := h.exists_mem_yamadaV_conj d hK hD hδ
  obtain ⟨hxN, -⟩ := (h.mem_yamadaV d hK hD).1 hxV
  have hNU₁ : ∀ {z : G}, z ∈ normalizer (yamadaC₁ d t : Set G) →
      z ∈ normalizer (yamadaU₁ d t : Set G) := fun hz =>
    (h.normalizer_yamadaC₁_le d hK hD).2 ((h.normalizer_yamadaC₁_le d hK hD).1 hz)
  obtain ⟨htN, -⟩ := h.t_mem_normalizer_yamadaU₁ d hK hD
  have hy : x⁻¹ * g ∈ normalizer ((yamadaU₁ d t ⊔ zpowers t : Subgroup G) : Set G) := by
    have hyN : x⁻¹ * g ∈ normalizer (yamadaC₁ d t : Set G) := mul_mem (inv_mem hxN) hg
    have hyt : x⁻¹ * g * t * (x⁻¹ * g)⁻¹ = t * (x⁻¹ * u⁻¹ * x) := by
      calc x⁻¹ * g * t * (x⁻¹ * g)⁻¹ = x⁻¹ * (g * t * g⁻¹) * x := by group
        _ = x⁻¹ * (t * δ * u) * u⁻¹ * x := by rw [hgt]; group
        _ = x⁻¹ * (x * t * x⁻¹) * u⁻¹ * x := by rw [hxt]
        _ = t * (x⁻¹ * u⁻¹ * x) := by group
    have hu' : x⁻¹ * u⁻¹ * x ∈ yamadaU₁ d t := by
      have := (mem_normalizer_iff.1 (inv_mem (hNU₁ hxN)) u⁻¹).1 (inv_mem hu)
      rwa [inv_inv] at this
    refine mem_normalizer_of_conj_mem fun z hz => ?_
    obtain ⟨v, hv, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer ((zpowers_le).2 htN) z hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    rw [show x⁻¹ * g * (v * t ^ k) * (x⁻¹ * g)⁻¹ =
      x⁻¹ * g * v * (x⁻¹ * g)⁻¹ * (x⁻¹ * g * t * (x⁻¹ * g)⁻¹) ^ k by rw [conj_zpow]; group, hyt]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 (hNU₁ hyN) v).1 hv))
      (zpow_mem (mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hu')) k)
  rw [h.yamada_5_17_1 d hK hD] at hy
  exact ⟨x, hxV, x⁻¹ * g, hy, by group⟩

theorem yamadaCstar_eq (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaCstar d t = h.yamadaV d hK hD := by
  refine le_antisymm (fun x hx => ?_) (h.yamadaV_le_yamadaCstar d hK hD)
  have hxN : x ∈ normalizer (yamadaC₁ d t : Set G) := LieType.BorelTits.pCoreOf_le 2 _ hx
  obtain ⟨v, hv, y, hy, rfl⟩ := h.exists_mul_of_mem_normalizer_yamadaC₁ d hK hD hxN
  have hyC : y ∈ yamadaCstar d t := by
    have := mul_mem (inv_mem (h.yamadaV_le_yamadaCstar d hK hD hv)) hx
    rwa [inv_mul_cancel_left] at this
  have hle : yamadaCstar d t ⊓ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ≤
      yamadaC₁ d t := by
    refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
    intro n hn
    exact Common.mem_normalizer_inf (LieType.BorelTits.le_normalizer_pCoreOf 2 _
      (le_normalizer_yamadaC₁ d t hn)) (le_normalizer hn)
  exact mul_mem hv (h.yamadaC₁_le_yamadaV d hK hD (hle ⟨hyC, hy⟩))

omit [Finite K] in
theorem inv_mul_mem_U_of_conj_eq (h : Setup G L f t) (d : G2Data L K) (hD : h.DoublingFacts d)
    {x δ δ' u u' : G} (hδ : δ ∈ d.D) (hδ' : δ' ∈ d.D) (hu : u ∈ yamadaU₁ d t)
    (hu' : u' ∈ yamadaU₁ d t) (e : x * t * x⁻¹ = t * δ * u) (e' : x * t * x⁻¹ = t * δ' * u') :
    δ⁻¹ * δ' ∈ d.U := by
  obtain ⟨-, -, hU₁D⟩ := hD.spec
  have h1 : δ⁻¹ * δ' = u * u'⁻¹ := by
    have h2 : t * δ * u = t * δ' * u' := e.symm.trans e'
    calc δ⁻¹ * δ' = δ⁻¹ * (t⁻¹ * (t * δ' * u')) * u'⁻¹ := by group
      _ = δ⁻¹ * (t⁻¹ * (t * δ * u)) * u'⁻¹ := by rw [h2]
      _ = u * u'⁻¹ := by group
  rw [← hU₁D]
  exact Subgroup.mem_inf.2 ⟨h1 ▸ mul_mem hu (inv_mem hu'), mul_mem (inv_mem hδ) hδ'⟩

theorem conj_mul_eq_of_mem_yamadaV (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x y δ δ' u u' : G} (hx : x ∈ h.yamadaV d hK hD) (hδ' : δ' ∈ d.D)
    (hu : u ∈ yamadaU₁ d t) (hu' : u' ∈ yamadaU₁ d t) (e : x * t * x⁻¹ = t * δ * u)
    (e' : y * t * y⁻¹ = t * δ' * u') :
    ∃ v ∈ yamadaU₁ d t, x * y * t * (x * y)⁻¹ = t * (δ * δ') * v := by
  obtain ⟨hxN, hxc⟩ := (h.mem_yamadaV d hK hD).1 hx
  have hDD₁ : d.D ≤ yamadaD₁ d t := le_sup_right
  have hU₁N := (h.normalizer_yamadaC₁_le d hK hD).2 ((h.normalizer_yamadaC₁_le d hK hD).1 hxN)
  have hD₁N : yamadaD₁ d t ≤ normalizer (yamadaU₁ d t : Set G) :=
    le_normalizer.trans (h.normalizer_yamadaC₁_le d hK hD).2
  have hc := hxc δ' (hDD₁ hδ')
  have hxu' : x * u' * x⁻¹ ∈ yamadaU₁ d t := (mem_normalizer_iff.1 hU₁N u').1 hu'
  refine ⟨δ'⁻¹ * (u * (x * δ' * x⁻¹ * δ'⁻¹)) * δ'⁻¹⁻¹ * (x * u' * x⁻¹),
    mul_mem ((mem_normalizer_iff.1 (hD₁N (inv_mem (hDD₁ hδ'))) _).1 (mul_mem hu hc)) hxu', ?_⟩
  calc x * y * t * (x * y)⁻¹ = x * (y * t * y⁻¹) * x⁻¹ := by group
    _ = x * t * x⁻¹ * (x * δ' * x⁻¹) * (x * u' * x⁻¹) := by rw [e']; group
    _ = t * δ * u * (x * δ' * x⁻¹) * (x * u' * x⁻¹) := by rw [e]
    _ = t * (δ * δ') * (δ'⁻¹ * (u * (x * δ' * x⁻¹ * δ'⁻¹)) * δ'⁻¹⁻¹ * (x * u' * x⁻¹)) := by
        group


theorem yamada_5_19_4 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    ∃ _ : ((yamadaC₁ d t).subgroupOf (yamadaCstar d t)).Normal,
      ∃ _ : (d.U.subgroupOf d.D).Normal, ∃ φ : yamadaCstar d t ⧸ (yamadaC₁ d t).subgroupOf
          (yamadaCstar d t) ≃* d.D ⧸ d.U.subgroupOf d.D,
        (∀ (x : yamadaCstar d t) (δ : d.D), (∃ u ∈ yamadaU₁ d t,
            (x : G) * t * (x : G)⁻¹ = t * δ * u) → φ (QuotientGroup.mk x) = QuotientGroup.mk δ) ∧
        ∀ n ∈ centralizer ({t} : Set G) ⊓ normalizer (d.U : Set G),
          ∀ (x : yamadaCstar d t) (δ : d.D), φ (QuotientGroup.mk x) = QuotientGroup.mk δ →
            ∃ (hx : n * x * n⁻¹ ∈ yamadaCstar d t) (hδ : n * δ * n⁻¹ ∈ d.D),
              φ (QuotientGroup.mk ⟨_, hx⟩) = QuotientGroup.mk ⟨_, hδ⟩ := by
  have hCV := h.yamadaCstar_eq d hK hD
  obtain ⟨-, hUU₁, -⟩ := hD.spec
  obtain ⟨hUY, hYX, -, hXF, -, hFD, -⟩ := d.inclusions
  have hUD : d.U ≤ d.D := hUY.trans (hYX.trans (hXF.trans hFD))
  have hDU : d.D ≤ normalizer (d.U : Set G) := fun x hx => by
    have : x ∈ L ⊓ normalizer (d.U : Set G) := by
      rw [(d.yamada_3_13_2_G).1]
      exact mem_sup_left hx
    exact this.2
  have hUDn : (d.U.subgroupOf d.D).Normal := (normal_subgroupOf_iff_le_normalizer hUD).2 hDU
  have hU₁N : yamadaU₁ d t ≤ normalizer (d.D : Set G) :=
    (h.yamadaU₁_le_yamadaC₁ d hK hD).trans (h.yamadaC₁_le_normalizer_D d hK)
  have hrel : ∀ x : yamadaCstar d t, ∃ δ ∈ d.D, ∃ u ∈ yamadaU₁ d t,
      (x : G) * t * (x : G)⁻¹ = t * δ * u := fun x => by
    obtain ⟨δ₁, hδ₁, e⟩ := h.exists_conj_t_eq d hK hD (LieType.BorelTits.pCoreOf_le 2 _ x.2)
    rw [hD.D₁_eq] at hδ₁
    obtain ⟨a, ha, b, hb, rfl⟩ := Common.exists_mul_of_le_normalizer hU₁N δ₁ hδ₁
    exact ⟨a, ha, b, hb, by rw [e, mul_assoc]⟩
  choose δf hδf uf huf hfe using hrel
  have hV : ∀ x : yamadaCstar d t, (x : G) ∈ h.yamadaV d hK hD := fun x => hCV ▸ x.2
  let ψ : yamadaCstar d t →* d.D ⧸ d.U.subgroupOf d.D :=
    { toFun := fun x => QuotientGroup.mk ⟨δf x, hδf x⟩
      map_one' := by
        apply (QuotientGroup.eq_one_iff _).2
        rw [mem_subgroupOf]
        have := h.inv_mul_mem_U_of_conj_eq d hD (hδf 1) (one_mem _) (huf 1) (one_mem _) (hfe 1)
          (by simp)
        rw [mul_one] at this
        exact (inv_mem_iff).1 this
      map_mul' := fun x y => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
        obtain ⟨v, hv, hxy⟩ := h.conj_mul_eq_of_mem_yamadaV d hK hD (hV x) (hδf y) (huf x)
          (huf y) (hfe x) (hfe y)
        exact h.inv_mul_mem_U_of_conj_eq d hD (hδf (x * y)) (mul_mem (hδf x) (hδf y))
          (huf (x * y)) hv (hfe (x * y)) (by rw [coe_mul]; exact hxy) }
  have hψ : ∀ x : yamadaCstar d t, ψ x = QuotientGroup.mk ⟨δf x, hδf x⟩ := fun _ => rfl
  have hform : ∀ (x : yamadaCstar d t) (δ : d.D), (∃ u ∈ yamadaU₁ d t,
      (x : G) * t * (x : G)⁻¹ = t * δ * u) → ψ x = QuotientGroup.mk δ := by
    rintro x δ ⟨u, hu, e⟩
    rw [hψ, QuotientGroup.eq, mem_subgroupOf]
    exact h.inv_mul_mem_U_of_conj_eq d hD (hδf x) δ.2 (huf x) hu (hfe x) e
  have hker : ψ.ker = (yamadaC₁ d t).subgroupOf (yamadaCstar d t) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, hψ, QuotientGroup.eq_one_iff, mem_subgroupOf]
    constructor
    · intro hx
      refine h.mem_yamadaC₁_of_crossed_mem d hK hD (hV x) ?_
      have htt := h.t_mul_t
      rw [show t * (x : G) * t * (x : G)⁻¹ = t * ((x : G) * t * (x : G)⁻¹) by group, hfe x,
        ← mul_assoc, ← mul_assoc, htt, one_mul]
      exact mul_mem (hUU₁ hx) (huf x)
    · intro hx
      have hw := (h.cosetData_tU d hK).crossed_mem (x : G)⁻¹ (yamadaC₁_le d t (inv_mem hx))
      rw [inv_inv] at hw
      have hwt : ((x : G) * t * (x : G)⁻¹ * t) * t = t * ((x : G) * t * (x : G)⁻¹ * t) :=
        mem_centralizer_singleton_iff.1 (((d.image_le _).trans h.L_le_centralizer) hw)
      have e : (x : G) * t * (x : G)⁻¹ = t * 1 * ((x : G) * t * (x : G)⁻¹ * t) := by
        have htt := h.t_mul_t
        rw [mul_one, ← hwt, mul_assoc _ t t, htt, mul_one]
      have := h.inv_mul_mem_U_of_conj_eq d hD (hδf x) (one_mem _) (huf x) (hUU₁ hw) (hfe x) e
      rw [mul_one] at this
      exact (inv_mem_iff).1 this
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨δ, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, hxN, hxc, u, hu, e⟩ := h.exists_conj_t_eq_mul_of_mem_D d hK hD δ.2
    have hx : x ∈ yamadaCstar d t := by
      rw [hCV]
      exact (h.mem_yamadaV d hK hD).2 ⟨hxN, hxc⟩
    exact ⟨⟨x, hx⟩, hform ⟨x, hx⟩ δ ⟨u, hu, e⟩⟩
  have hC₁n : ((yamadaC₁ d t).subgroupOf (yamadaCstar d t)).Normal := hker ▸ ψ.normal_ker
  set φ := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj) with hφdef
  have hφ : ∀ x : yamadaCstar d t, φ (QuotientGroup.mk x) = ψ x := fun _ => rfl
  refine ⟨hC₁n, hUDn, φ, fun x δ hxδ => (hφ x).trans (hform x δ hxδ), ?_⟩
  · intro n hn x δ hxδ
    rw [hφ, hψ, QuotientGroup.eq, mem_subgroupOf] at hxδ
    have hnN := h.centralizer_inf_normalizer_U_le d hn
    have hnC₁ := le_normalizer_yamadaC₁ d t hnN
    have hnU₁ := (h.normalizer_yamadaC₁_le d hK hD).2 ((h.normalizer_yamadaC₁_le d hK hD).1 hnC₁)
    have hx : n * x * n⁻¹ ∈ yamadaCstar d t :=
      (mem_normalizer_iff.1 (LieType.BorelTits.le_normalizer_pCoreOf 2 _ hnC₁) x).1 x.2
    have hδ : n * δ * n⁻¹ ∈ d.D :=
      (mem_normalizer_iff.1 (h.centralizer_inf_normalizer_U_le_normalizer_D d hK hn) δ).1 δ.2
    refine ⟨hx, hδ, ?_⟩
    rw [hφ]
    refine hform ⟨_, hx⟩ ⟨_, hδ⟩ ?_
    have hnt : n * t = t * n := mem_centralizer_singleton_iff.1 hn.1
    have hnt' : n⁻¹ * t * n = t := by rw [mul_assoc, ← hnt, inv_mul_cancel_left]
    set v := (δ : G)⁻¹ * δf x with hvdef
    have hv : v ∈ d.U := by
      have := inv_mem hxδ
      rw [coe_mul, coe_inv, mul_inv_rev, inv_inv] at this
      exact this
    refine ⟨n * (v * uf x) * n⁻¹, (mem_normalizer_iff.1 hnU₁ _).1
      (mul_mem (hUU₁ hv) (huf x)), ?_⟩
    calc n * x * n⁻¹ * t * (n * x * n⁻¹)⁻¹ = n * x * (n⁻¹ * t * n) * (x : G)⁻¹ * n⁻¹ := by group
      _ = n * ((x : G) * t * (x : G)⁻¹) * n⁻¹ := by rw [hnt']; group
      _ = n * (t * δf x * uf x) * n⁻¹ := by rw [hfe x]
      _ = n * t * n⁻¹ * (n * (δ : G) * n⁻¹) * (n * (v * uf x) * n⁻¹) := by rw [hvdef]; group
      _ = t * (n * (δ : G) * n⁻¹) * (n * (v * uf x) * n⁻¹) := by rw [hnt, mul_inv_cancel_right]

theorem yamada_5_19 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    (normalizer (yamadaC₁ d t : Set G) =
        yamadaCstar d t ⊔ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ∧
      ((normalizer (yamadaC₁ d t : Set G) : Subgroup G) : Set G) =
        (yamadaCstar d t : Set G) *
          ((normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) : Subgroup G) : Set G) ∧
      yamadaCstar d t ⊓ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) = yamadaC₁ d t) ∧
    ((∀ x ∈ yamadaCstar d t, ∃ δ ∈ yamadaD₁ d t, x * t * x⁻¹ = t * δ) ∧
      ∀ δ ∈ yamadaD₁ d t, ∃ x ∈ yamadaCstar d t, ∃ u ∈ yamadaU₁ d t,
        x * t * x⁻¹ = t * δ * u) ∧
    (∀ x ∈ yamadaCstar d t, ∀ y ∈ yamadaD₁ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaU₁ d t) ∧
    (∃ _ : ((yamadaC₁ d t).subgroupOf (yamadaCstar d t)).Normal,
      ∃ _ : (d.U.subgroupOf d.D).Normal,
        ∃ φ : yamadaCstar d t ⧸ (yamadaC₁ d t).subgroupOf (yamadaCstar d t) ≃*
          d.D ⧸ d.U.subgroupOf d.D,
        (∀ (x : yamadaCstar d t) (δ : d.D), (∃ u ∈ yamadaU₁ d t,
            (x : G) * t * (x : G)⁻¹ = t * δ * u) → φ (QuotientGroup.mk x) = QuotientGroup.mk δ) ∧
        ∀ n ∈ centralizer ({t} : Set G) ⊓ normalizer (d.U : Set G),
          ∀ (x : yamadaCstar d t) (δ : d.D), φ (QuotientGroup.mk x) = QuotientGroup.mk δ →
            ∃ (hx : n * x * n⁻¹ ∈ yamadaCstar d t) (hδ : n * δ * n⁻¹ ∈ d.D),
              φ (QuotientGroup.mk ⟨_, hx⟩) = QuotientGroup.mk ⟨_, hδ⟩) ∧
    yamadaC₂ d t = yamadaCstar d t ⊓ yamadaR₂ d t ∧
    (standardComponentOddCore (centralizer ({t} : Set G))).map
        (centralizer ({t} : Set G)).subtype ≤ centralizer (yamadaCstar d t : Set G) := by
  have hCV := h.yamadaCstar_eq d hK hD
  have hCN : yamadaCstar d t ≤ normalizer (yamadaC₁ d t : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _
  have hNtU : normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (yamadaCstar d t : Set G) :=
    (le_normalizer_yamadaC₁ d t).trans (LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hC₁C : yamadaC₁ d t ≤ yamadaCstar d t := hCV ▸ h.yamadaC₁_le_yamadaV d hK hD
  have hinf : yamadaCstar d t ⊓ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) =
      yamadaC₁ d t := by
    refine le_antisymm (fun x hx => ?_) (le_inf hC₁C (yamadaC₁_le d t))
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
    exact h.yamadaV_inf_normalizer_tU d hK hD (hCV ▸ hx₁) hx₂
  have hN : normalizer (yamadaC₁ d t : Set G) =
      yamadaCstar d t ⊔ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) := by
    refine le_antisymm (fun g hg => ?_) (sup_le hCN (le_normalizer_yamadaC₁ d t))
    obtain ⟨x, hx, y, hy, rfl⟩ := h.exists_mul_of_mem_normalizer_yamadaC₁ d hK hD hg
    exact mul_mem (mem_sup_left (hCV ▸ hx)) (mem_sup_right hy)
  have hY₂C : yamadaY₂ d t ≤ yamadaCstar d t := by
    rw [hCV]
    intro y hy
    exact (h.mem_yamadaV d hK hD).2 ⟨h.yamadaR₂_le_normalizer_yamadaC₁ d hK hD
      (h.yamadaY₂_le_yamadaR₂ d hK hD hy),
      fun δ hδ => h.commutator_mem_yamadaU₁_of_mem_yamadaY₂ d hK hD hy hδ⟩
  refine ⟨⟨hN, ?_, hinf⟩, ⟨fun x hx => h.exists_conj_t_eq d hK hD (hCN hx), fun δ hδ => ?_⟩,
    fun x hx => ((h.mem_yamadaV d hK hD).1 (hCV ▸ hx)).2, h.yamada_5_19_4 d hK hD, ?_, ?_⟩
  · rw [hN]
    exact coe_mul_of_right_le_normalizer_left _ _ hNtU
  · obtain ⟨x, hx, u, hu, e⟩ := h.exists_mem_yamadaV_conj d hK hD hδ
    exact ⟨x, hCV ▸ hx, u, hu, e⟩
  ·
    obtain ⟨hC₂, -⟩ := h.yamadaC₂_eq_sup d hK hD
    obtain ⟨hR₂, hR₁Y₂⟩ := h.yamadaR₂_eq_yamadaR₁_sup d hK hD
    refine le_antisymm (le_inf ?_ ?_) fun x hx => ?_
    · rw [hC₂]
      exact sup_le hC₁C hY₂C
    · rw [hC₂]
      exact sup_le (h.yamadaC₁_le_yamadaR₂ d hK) (h.yamadaY₂_le_yamadaR₂ d hK hD)
    obtain ⟨hxC, hxR₂⟩ := Subgroup.mem_inf.1 hx
    rw [hR₂] at hxR₂
    obtain ⟨r, hr, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hR₁Y₂ x hxR₂
    have hrC : r ∈ yamadaCstar d t := by
      have := mul_mem hxC (inv_mem (hY₂C hy))
      rwa [mul_inv_cancel_right] at this
    have hSN : d.S ≤ normalizer (yamadaC₁ d t : Set G) := fun s hs =>
      le_normalizer_yamadaC₁ d t (h.centralizer_inf_normalizer_U_le d
        ⟨h.L_le_centralizer (d.image_le _ hs), mem_normalizer_of_conj_mem fun u hu => by
          have hu' : u ∈ d.S ⊓ centralizer (d.S : Set G) := by
            rw [(d.yamada_3_12_centers).1]
            exact hu
          rw [mem_centralizer_iff.1 hu'.2 s hs, mul_inv_cancel_right]
          exact hu⟩)
    obtain ⟨c, hc, s', hs', rfl⟩ := Common.exists_mul_of_le_normalizer hSN r hr
    have hs'C : s' ∈ yamadaCstar d t := by
      have := mul_mem (inv_mem (hC₁C hc)) hrC
      rwa [inv_mul_cancel_left] at this
    have hs'N : s' ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) :=
      h.centralizer_inf_normalizer_U_le d ⟨h.L_le_centralizer (d.image_le _ hs'),
        mem_normalizer_of_conj_mem fun u hu => by
          have hu' : u ∈ d.S ⊓ centralizer (d.S : Set G) := by
            rw [(d.yamada_3_12_centers).1]
            exact hu
          rw [mem_centralizer_iff.1 hu'.2 s' hs', mul_inv_cancel_right]
          exact hu⟩
    have hs'C₁ : s' ∈ yamadaC₁ d t := by
      rw [← hinf]
      exact ⟨hs'C, hs'N⟩
    rw [hC₂]
    exact mul_mem (mem_sup_left (mul_mem hc hs'C₁)) (mem_sup_right hy)
  ·
    rw [h.core t h.ht, Subgroup.map_bot]
    exact bot_le

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
