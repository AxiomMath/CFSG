
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma66

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

namespace Lemma68Aux

variable {G : Type*} [Group G]

theorem conj_toMonoidHom_apply (g k : G) : (MulAut.conj g).toMonoidHom k = g * k * g⁻¹ := rfl

theorem mem_map_conj_iff {K : Subgroup G} {g y : G} :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have : g⁻¹ * (MulAut.conj g).toMonoidHom k * g = k := by
      rw [conj_toMonoidHom_apply]; group
    rw [this]
    exact hk
  · intro h
    exact ⟨g⁻¹ * y * g, h, by rw [conj_toMonoidHom_apply]; group⟩

theorem card_sup_zpowers_of_comm {w : G} (hw : w * w = 1) {X : Subgroup G}
    (hwX : w ∉ X) (hc : ∀ x ∈ X, w * x = x * w) :
    Nat.card (X ⊔ zpowers w : Subgroup G) = 2 * Nat.card X := by
  have hw2 : orderOf w = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hw) (fun h1 => hwX (h1 ▸ X.one_mem))
  have hd : Disjoint X (zpowers w) := by
    rw [Subgroup.disjoint_def]
    intro y hyX hyw
    rcases mem_zpowers_sq_eq_one hw hyw with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hyX) hwX
  have e := mulEquivProdSup (A := X) (B := zpowers w)
    (zpowers_le.2 (mem_centralizer_iff.2 fun x hx => (hc x hx).symm)) hd
  rw [Nat.card_congr e.toEquiv.symm, Nat.card_prod, Nat.card_zpowers, hw2]
  ring

theorem exists_conj_map_of_maximal [Finite G] {C S P : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSC : S ≤ C) (hP2 : IsPGroup 2 P) (hPC : P ≤ C)
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ C → S ≤ R → R = S)
    (hcard : Nat.card S ≤ Nat.card P) :
    ∃ h ∈ C, P = S.map (MulAut.conj h).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSp : IsPGroup 2 (S.subgroupOf C) := hS2.comap_subtype
  obtain ⟨Q₁, hQ₁⟩ := hSp.exists_le_sylow
  have hQ₁S : (Q₁ : Subgroup C) = S.subgroupOf C := by
    have hmap : IsPGroup 2 ((Q₁ : Subgroup C).map C.subtype) := Q₁.isPGroup'.map _
    have hle : S ≤ (Q₁ : Subgroup C).map C.subtype := fun s hs =>
      ⟨⟨s, hSC hs⟩, hQ₁ (mem_subgroupOf.2 hs), rfl⟩
    have heq := hSmax _ hmap (by rintro _ ⟨y, -, rfl⟩; exact y.2) hle
    ext y
    constructor
    · intro hy
      have : (y : G) ∈ (Q₁ : Subgroup C).map C.subtype := ⟨y, hy, rfl⟩
      rw [heq] at this
      exact mem_subgroupOf.2 this
    · exact fun hy => hQ₁ hy
  have hPp : IsPGroup 2 (P.subgroupOf C) := hP2.comap_subtype
  obtain ⟨Q₂, hQ₂⟩ := hPp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq C Q₁ Q₂
  refine ⟨(h : G), h.2, ?_⟩
  have hPle : P ≤ S.map (MulAut.conj (h : G)).toMonoidHom := by
    intro p hp
    have hpQ : (⟨p, hPC hp⟩ : C) ∈ (Q₂ : Subgroup C) := hQ₂ (mem_subgroupOf.2 hp)
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, hQ₁S] at hpQ
    obtain ⟨s, hs, hsp⟩ := hpQ
    have e1 : (⟨p, hPC hp⟩ : C) = h * s * h⁻¹ := by
      rw [← hsp, MulAut.smul_def, MulAut.conj_apply]
    have e2 := congrArg Subtype.val e1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e2
    exact ⟨(s : G), mem_subgroupOf.1 hs, by rw [conj_toMonoidHom_apply, e2]⟩
  refine Subgroup.eq_of_le_of_card_ge hPle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj (h : G)).injective]
  exact hcard

end Lemma68Aux

open Lemma68Aux

section InnerAux

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} {z t : G} {T₀ : Subgroup G}

theorem InnerConfig.exists_conj_le_T (h : InnerConfig G A z t T₀) {Y : Subgroup G}
    (hY : IsPGroup 2 Y) (hYz : Y ≤ centralizer ({z} : Set G)) :
    ∃ c ∈ centralizer ({z} : Set G), ∀ p ∈ Y, c⁻¹ * p * c ∈ T₀ ⊔ zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H, hH⟩ : ∃ H : Subgroup G, H = centralizer ({z} : Set G) := ⟨_, rfl⟩
  rw [← hH] at hYz ⊢
  have hTH : T₀ ⊔ zpowers z ≤ H := by
    rw [hH, h.cent_eq]
    exact sup_le_sup_right h.T₀_le _
  have hcardH : Nat.card H = 2 * Nat.card A := by
    have e := mulEquivProdSup (A := A) (B := zpowers z) (zpowers_le.2 h.z_cent) h.disjoint
    rw [hH, h.cent_eq, Nat.card_congr e.toEquiv.symm, Nat.card_prod, Nat.card_zpowers, h.z_order]
    ring
  obtain ⟨m, hm, hAm⟩ := h.T₀_odd
  have hidx : ¬ 2 ∣ ((T₀ ⊔ zpowers z).subgroupOf H).index := by
    have h1 := Subgroup.index_mul_card (H := (T₀ ⊔ zpowers z).subgroupOf H)
    rw [Nat.card_congr (subgroupOfEquivOfLe hTH).toEquiv, h.T_card, hcardH, hAm] at h1
    have hpos : 0 < 2 * Nat.card T₀ := by
      have : 0 < Nat.card T₀ := Nat.card_pos
      omega
    have : ((T₀ ⊔ zpowers z).subgroupOf H).index = m :=
      Nat.eq_of_mul_eq_mul_right hpos (h1.trans (by ring))
    rw [this]
    exact fun hd => (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 hd)
  have hTp : IsPGroup 2 ((T₀ ⊔ zpowers z).subgroupOf H) := h.T_pgroup.comap_subtype
  let TS : Sylow 2 H := hTp.toSylow hidx
  have hYp : IsPGroup 2 (Y.subgroupOf H) := hY.comap_subtype
  obtain ⟨Q', hQ'⟩ := hYp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H TS Q'
  refine ⟨(c : G), c.2, fun p hp => ?_⟩
  have hpQ : (⟨p, hYz hp⟩ : H) ∈ (Q' : Subgroup H) := hQ' (mem_subgroupOf.2 hp)
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hpQ
  obtain ⟨s, hs, hsp⟩ := hpQ
  have hs' : (s : G) ∈ T₀ ⊔ zpowers z := mem_subgroupOf.1 hs
  have e1 : c⁻¹ * ⟨p, hYz hp⟩ * c = s := by
    rw [← hsp, MulAut.smul_def, MulAut.conj_apply]
    group
  have e2 := congrArg Subtype.val e1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e2
  rw [e2]
  exact hs'

end InnerAux

@[expose] def Fin76bUCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B : Subgroup G), Rest6Config L z t T₀ E Q x β B →
    WFacts L t E → ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (E : Set G) →
    (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) →
    z ∈ S → Nonempty (S ≃* DihedralGroup 4) → (∀ b ∈ B, ∀ s ∈ S, b * s = s * b) →
    ∀ u ∈ S ⊔ E, u * u = 1 → u ∉ zpowers t →
      ∃ X : Subgroup G, X ≤ S ⊔ E ∧ Nonempty (E ≃* X) ∧ u ∉ X ∧ ∀ x ∈ X, u * x = x * u

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B : Subgroup G}

theorem exists_conj_z_eq_zt (hconf : Rest6Config L z t T₀ E Q x β B) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSC : S ≤ centralizer (E : Set G)) (hzS : z ∈ S)
    (hD8 : Nonempty (S ≃* DihedralGroup 4))
    (h67 : ∀ g : G, g * z * g⁻¹ ∈ S → g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z * t) :
    ∃ s ∈ S, s * z * s⁻¹ = z * t := by
  classical
  by_contra hcon
  have hcomm : ∀ s ∈ S, s * z = z * s := by
    intro s hs
    rcases h67 s (mul_mem (mul_mem hs hzS) (inv_mem hs)) with h | h
    · calc s * z = (s * z * s⁻¹) * s := by group
        _ = z * s := by rw [h]
    · exact absurd ⟨s, hs, h⟩ hcon
  have hsub : (S : Set G) ⊆ ↑({1, z, t, z * t} : Finset G) := by
    intro s hs
    have := mem_klein_of_comm hconf.cfg hconf.econfig hS2 hSC hzS hs (hcomm s hs)
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    tauto
  have hle : Nat.card S ≤ 4 := by
    have h1 : Nat.card S = (S : Set G).ncard := Nat.card_coe_set_eq _
    have h2 : (S : Set G).ncard ≤ (↑({1, z, t, z * t} : Finset G) : Set G).ncard :=
      Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h2
    have h3 : ({1, z, t, z * t} : Finset G).card ≤ 4 := Finset.card_le_four
    omega
  have h8 : Nat.card S = 8 := by
    rw [Nat.card_congr hD8.some.toEquiv, DihedralGroup.nat_card]
  omega

theorem lemma68 (hX : Fin76bUCent) (hconf : Rest6Config L z t T₀ E Q x β B) (hW : WFacts L t E)
    {S : Subgroup G} (hS2 : IsPGroup 2 S) (hSC : S ≤ centralizer (E : Set G))
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S)
    (hzS : z ∈ S) (hD8 : Nonempty (S ≃* DihedralGroup 4))
    (hBS : ∀ b ∈ B, ∀ s ∈ S, b * s = s * b)
    (hC : ∀ E₀ : Subgroup G, E₀ ≤ S ⊔ E → Nonempty (E ≃* E₀) →
      8 ≤ Nat.card ↥((S ⊔ E) ⊓ centralizer (E₀ : Set G)))
    (h67 : ∀ g : G, g * z * g⁻¹ ∈ S → g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z * t) :
    ∀ g : G, g * z * g⁻¹ ∈ S ⊔ E →
      ∃ m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G), m * z * m⁻¹ = g * z * g⁻¹ := by
  intro g hgU
  have hcfg := hconf.cfg
  have hE := hconf.econfig
  have hE2 : IsPGroup 2 E := hcfg.T₀_pgroup.to_le hE.le
  have hU2 : IsPGroup 2 (S ⊔ E : Subgroup G) :=
    hS2.to_sup_of_normal_right' hE2 (hSC.trans (centralizer_le_normalizer E))
  have hzE : ∀ e ∈ E, e * z = z * e := fun e he =>
    hcfg.z_comm_of_mem_A (hcfg.T₀_le (hE.le he))
  have hzE' : z ∉ E := fun hz => hcfg.z_not_mem_A (hcfg.T₀_le (hE.le hz))
  have hS8 : Nat.card S = 8 := by
    rw [Nat.card_congr hD8.some.toEquiv, DihedralGroup.nat_card]
  have hE32 : Nat.card E = 32 := hW.card_E
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, z₀ = g * z * g⁻¹ := ⟨_, rfl⟩
  rw [← hz₀] at hgU ⊢
  have hz₀2 : z₀ * z₀ = 1 := by
    rw [hz₀]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hcfg.z_sq]; group
  have hz₀1 : z₀ ≠ 1 := by
    intro h1
    apply hcfg.z_ne
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [← hz₀, h1]; group
  have hz₀t : z₀ ≠ t := fun h1 => hcfg.conj_z_ne_t g (hz₀ ▸ h1)
  have hz₀nt : z₀ ∉ zpowers t := fun hm => by
    rcases mem_zpowers_sq_eq_one hcfg.t_sq hm with h1 | h1
    exacts [hz₀1 h1, hz₀t h1]
  obtain ⟨X, hXU, ⟨eEX⟩, hz₀X, hXc⟩ :=
    hX G L z t T₀ E Q x β B hconf hW S hS2 hSC hSmax hzS hD8 hBS z₀ hgU hz₀2 hz₀nt
  have hX32 : Nat.card X = 32 := (Nat.card_congr eEX.toEquiv).symm.trans hE32
  obtain ⟨X₁, hX₁⟩ : ∃ X₁ : Subgroup G, X₁ = X ⊔ zpowers z₀ := ⟨_, rfl⟩
  have hX₁card : Nat.card X₁ = 64 := by
    rw [hX₁, card_sup_zpowers_of_comm hz₀2 hz₀X hXc, hX32]
  have hzU : zpowers z₀ ≤ S ⊔ E := zpowers_le.2 hgU
  have hX₁U : X₁ ≤ S ⊔ E := hX₁ ▸ sup_le hXU hzU
  have hX₁c : X₁ ≤ centralizer ({z₀} : Set G) := by
    rw [hX₁]
    refine sup_le (fun y hy => mem_centralizer_singleton_iff.2 (hXc y hy).symm) ?_
    rw [zpowers_le]
    exact mem_centralizer_singleton_iff.2 rfl
  have hY2 : IsPGroup 2 (X₁.map (MulAut.conj g⁻¹).toMonoidHom) := (hU2.to_le hX₁U).map _
  have hYz : X₁.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({z} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff, conj_toMonoidHom_apply]
    have hyc := mem_centralizer_singleton_iff.1 (hX₁c hy)
    calc g⁻¹ * y * g⁻¹⁻¹ * z = g⁻¹ * (y * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * (y * z₀) * g := by rw [hz₀]
      _ = g⁻¹ * (z₀ * y) * g := by rw [hyc]
      _ = z * (g⁻¹ * y * g⁻¹⁻¹) := by rw [hz₀]; group
  obtain ⟨c, hcz, hcT⟩ := hcfg.exists_conj_le_T hY2 hYz
  have hcz' : c * z = z * c := mem_centralizer_singleton_iff.1 hcz
  obtain ⟨g', hg'⟩ : ∃ g', g' = g * c := ⟨_, rfl⟩
  have hg'z : g' * z * g'⁻¹ = z₀ := by
    rw [hg', hz₀]
    calc g * c * z * (g * c)⁻¹ = g * (c * z) * c⁻¹ * g⁻¹ := by group
      _ = g * (z * c) * c⁻¹ * g⁻¹ := by rw [hcz']
      _ = g * z * g⁻¹ := by group
  have hg'T : ∀ y ∈ X₁, g'⁻¹ * y * g' ∈ T₀ ⊔ zpowers z := by
    intro y hy
    have h1 := hcT _ ⟨y, hy, rfl⟩
    rw [conj_toMonoidHom_apply] at h1
    have e : g'⁻¹ * y * g' = c⁻¹ * (g⁻¹ * y * g⁻¹⁻¹) * c := by rw [hg']; group
    rw [e]
    exact h1
  obtain ⟨P, hP⟩ : ∃ P : Subgroup G, P = X.map (MulAut.conj g'⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hPT : P ≤ T₀ ⊔ zpowers z := by
    rw [hP]
    rintro _ ⟨y, hy, rfl⟩
    rw [conj_toMonoidHom_apply]
    have := hg'T y (hX₁ ▸ mem_sup_left hy)
    simpa using this
  have hPiso : Nonempty (E ≃* P) := by
    rw [hP]
    exact ⟨eEX.trans (X.equivMapOfInjective (MulAut.conj g'⁻¹).toMonoidHom
      (MulAut.conj g'⁻¹).injective)⟩
  have hPle : P ≤ E ⊔ zpowers z := EConfig.le_sup_of_equiv hcfg hE hPT hPiso
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : Subgroup G, E₀ = E.map (MulAut.conj g').toMonoidHom := ⟨_, rfl⟩
  have hKeq : (E ⊔ zpowers z).map (MulAut.conj g').toMonoidHom = E₀ ⊔ zpowers z₀ := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, conj_toMonoidHom_apply, hg'z, hE₀]
  have hKcard : Nat.card (E₀ ⊔ zpowers z₀ : Subgroup G) = 64 := by
    rw [← hKeq, Subgroup.card_map_of_injective (MulAut.conj g').injective,
      card_sup_zpowers_of_comm hcfg.z_sq hzE' (fun e he => (hzE e he).symm), hE32]
  have hXK : X ≤ E₀ ⊔ zpowers z₀ := by
    intro y hy
    rw [← hKeq, mem_map_conj_iff]
    have hyP : (MulAut.conj g'⁻¹).toMonoidHom y ∈ P := by
      rw [hP]
      exact ⟨y, hy, rfl⟩
    have := hPle hyP
    rw [conj_toMonoidHom_apply] at this
    simpa using this
  have hX₁K : X₁ = E₀ ⊔ zpowers z₀ := by
    refine Subgroup.eq_of_le_of_card_ge (hX₁ ▸ sup_le hXK le_sup_right) ?_
    rw [hKcard, hX₁card]
  have hE₀U : E₀ ≤ S ⊔ E := le_sup_left.trans (hX₁K ▸ hX₁U)
  have hE₀iso : Nonempty (E ≃* E₀) := by
    rw [hE₀]
    exact ⟨E.equivMapOfInjective (MulAut.conj g').toMonoidHom (MulAut.conj g').injective⟩
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Subgroup G, S₀ = (S ⊔ E) ⊓ centralizer (E₀ : Set G) := ⟨_, rfl⟩
  have hS₀2 : IsPGroup 2 S₀ := hS₀ ▸ hU2.to_le inf_le_left
  have hS₀card : 8 ≤ Nat.card S₀ := hS₀ ▸ hC E₀ hE₀U hE₀iso
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : Subgroup G, P₀ = S₀.map (MulAut.conj g'⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hP₀mem : ∀ y, y ∈ P₀ ↔ g' * y * g'⁻¹ ∈ S₀ := by
    intro y
    rw [hP₀, mem_map_conj_iff, inv_inv]
  have hP₀2 : IsPGroup 2 P₀ := hP₀ ▸ hS₀2.map _
  have hP₀C : P₀ ≤ centralizer (E : Set G) := by
    intro s hs
    rw [mem_centralizer_iff]
    intro e he
    have hs' : g' * s * g'⁻¹ ∈ centralizer (E₀ : Set G) := (hS₀ ▸ (hP₀mem s).1 hs).2
    have hs'' := mem_centralizer_iff.1 hs' (g' * e * g'⁻¹) (hE₀ ▸ ⟨e, he, rfl⟩)
    calc e * s = g'⁻¹ * ((g' * e * g'⁻¹) * (g' * s * g'⁻¹)) * g' := by group
      _ = g'⁻¹ * ((g' * s * g'⁻¹) * (g' * e * g'⁻¹)) * g' := by rw [hs'']
      _ = s * e := by group
  have hP₀card : 8 ≤ Nat.card P₀ := by
    rw [hP₀, Subgroup.card_map_of_injective (MulAut.conj g'⁻¹).injective]
    exact hS₀card
  obtain ⟨h', hh'C, hh'⟩ := exists_conj_map_of_maximal hS2 hSC hP₀2 hP₀C hSmax (by omega)
  have hh'E : ∀ e ∈ E, h' * e = e * h' := fun e he => (mem_centralizer_iff.1 hh'C e he).symm
  have hSmem : ∀ s ∈ S, g' * (h' * s * h'⁻¹) * g'⁻¹ ∈ S₀ := by
    intro s hs
    have : h' * s * h'⁻¹ ∈ P₀ := by
      rw [hh']
      exact ⟨s, hs, by rw [conj_toMonoidHom_apply]⟩
    exact (hP₀mem _).1 this
  obtain ⟨m, hm⟩ : ∃ m, m = g' * h' := ⟨_, rfl⟩
  have hmle : (S ⊔ E).map (MulAut.conj m).toMonoidHom ≤ S ⊔ E := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      rw [conj_toMonoidHom_apply]
      have e : m * s * m⁻¹ = g' * (h' * s * h'⁻¹) * g'⁻¹ := by rw [hm]; group
      rw [e]
      exact (hS₀ ▸ hSmem s hs : _ ∈ (S ⊔ E) ⊓ centralizer (E₀ : Set G)).1
    · rintro _ ⟨e, he, rfl⟩
      rw [conj_toMonoidHom_apply]
      have e' : m * e * m⁻¹ = g' * e * g'⁻¹ := by
        rw [hm]
        calc g' * h' * e * (g' * h')⁻¹ = g' * (h' * e) * h'⁻¹ * g'⁻¹ := by group
          _ = g' * (e * h') * h'⁻¹ * g'⁻¹ := by rw [hh'E e he]
          _ = g' * e * g'⁻¹ := by group
      rw [e']
      exact hE₀U (hE₀ ▸ ⟨e, he, rfl⟩)
  have hmeq : (S ⊔ E).map (MulAut.conj m).toMonoidHom = S ⊔ E :=
    Subgroup.eq_of_le_of_card_ge hmle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj m).injective])
  have hmN : m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      exact hmle ⟨u, hu, rfl⟩
    · intro hu
      rw [← hmeq] at hu
      obtain ⟨u', hu', hu'e⟩ := hu
      have : u' = u := by
        have h2 : m * u' * m⁻¹ = m * u * m⁻¹ := hu'e
        exact mul_left_cancel (mul_right_cancel h2)
      rwa [← this]
  have hz₀S₀ : z₀ ∈ S₀ := by
    rw [hS₀]
    refine ⟨hgU, mem_centralizer_iff.2 fun y hy => ?_⟩
    obtain ⟨e, he, rfl⟩ := (hE₀ ▸ hy : y ∈ E.map (MulAut.conj g').toMonoidHom)
    rw [conj_toMonoidHom_apply, ← hg'z]
    calc g' * e * g'⁻¹ * (g' * z * g'⁻¹) = g' * (e * z) * g'⁻¹ := by group
      _ = g' * (z * e) * g'⁻¹ := by rw [hzE e he]
      _ = g' * z * g'⁻¹ * (g' * e * g'⁻¹) := by group
  have hzP₀ : z ∈ P₀ := (hP₀mem z).2 (by rw [hg'z]; exact hz₀S₀)
  rw [hh'] at hzP₀
  obtain ⟨s₁, hs₁S, hs₁⟩ := hzP₀
  rw [conj_toMonoidHom_apply] at hs₁
  have hconjS : h'⁻¹ * z * h'⁻¹⁻¹ ∈ S := by
    have : h'⁻¹ * z * h'⁻¹⁻¹ = s₁ := by rw [← hs₁]; group
    rw [this]
    exact hs₁S
  rcases h67 h'⁻¹ hconjS with hz | hzt
  · have hz'' : h'⁻¹ * z * h' = z := by simpa using hz
    have hz' : h' * z * h'⁻¹ = z := by
      calc h' * z * h'⁻¹ = h' * (h'⁻¹ * z * h') * h'⁻¹ := by rw [hz'']
        _ = z := by group
    refine ⟨m, hmN, ?_⟩
    calc m * z * m⁻¹ = g' * (h' * z * h'⁻¹) * g'⁻¹ := by rw [hm]; group
      _ = g' * z * g'⁻¹ := by rw [hz']
      _ = z₀ := hg'z
  · obtain ⟨s, hsS, hs⟩ := exists_conj_z_eq_zt hconf hS2 hSC hzS hD8 h67
    have hzt' : h'⁻¹ * z * h' = z * t := by simpa using hzt
    have hz' : h' * (z * t) * h'⁻¹ = z := by
      calc h' * (z * t) * h'⁻¹ = h' * (h'⁻¹ * z * h') * h'⁻¹ := by rw [hzt']
        _ = z := by group
    refine ⟨m * s, mul_mem hmN (le_normalizer (mem_sup_left hsS)), ?_⟩
    calc m * s * z * (m * s)⁻¹ = m * (s * z * s⁻¹) * m⁻¹ := by group
      _ = m * (z * t) * m⁻¹ := by rw [hs]
      _ = g' * (h' * (z * t) * h'⁻¹) * g'⁻¹ := by rw [hm]; group
      _ = g' * z * g'⁻¹ := by rw [hz']
      _ = z₀ := hg'z

end Main

@[expose] def Fin76bUCard : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B : Subgroup G), Rest6Config L z t T₀ E Q x β B →
    WFacts L t E → ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (E : Set G) →
    (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) →
    z ∈ S → Nonempty (S ≃* DihedralGroup 4) → (∀ b ∈ B, ∀ s ∈ S, b * s = s * b) →
    ∀ E₀ : Subgroup G, E₀ ≤ S ⊔ E → Nonempty (E ≃* E₀) →
      8 ≤ Nat.card ↥((S ⊔ E) ⊓ centralizer (E₀ : Set G))

theorem fin76bLemma68 (hX : Fin76bUCent) (hC : Fin76bUCard) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
      (Q : Sylow 2 G) (x β : G) (B : Subgroup G), Rest6Config L z t T₀ E Q x β B →
      WFacts L t E → ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (E : Set G) →
      (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) →
      z ∈ S → Nonempty (S ≃* DihedralGroup 4) → (∀ b ∈ B, ∀ s ∈ S, b * s = s * b) →
      (∀ g : G, g * z * g⁻¹ ∈ S → g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z * t) →
      ∀ g : G, g * z * g⁻¹ ∈ S ⊔ E →
        ∃ m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G), m * z * m⁻¹ = g * z * g⁻¹ := by
  intro G _ _ L z t T₀ E Q x β B hconf hW S hS2 hSC hSmax hzS hD8 hBS h67
  exact lemma68 hX hconf hW hS2 hSC hSmax hzS hD8 hBS
    (hC G L z t T₀ E Q x β B hconf hW S hS2 hSC hSmax hzS hD8 hBS) h67

end CFSG.EvenSporadicStandard.Fin76b
