module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.HSCoverCert
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.HSCoverGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs3

public section

namespace CFSG.QuasithinUnique.Ch1.HSCover

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519 CFSG.QuasithinUnique.Id2519.UHS
open CFSG.QuasithinUnique.Ch1.M22Cover
open CFSG.Sporadic.Schreier

theorem hs_no_involution_over_c
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (X : CentralExt E (Equiv.Perm (Fin 3850)))
    (hrange : ∀ y ∈ PP, ∃ e : E, X.φ e = y) (hφmem : ∀ e, X.φ e ∈ PP)
    (u : E) (hu : u * u = 1) (huc : X.φ u = cElt) : False := by
  classical
  have hxmem : ∀ i, covData.x i ∈ PP := fun i => wordP_mem _
  choose xt hxt using fun i => hrange _ (hxmem i)
  have hlift : ∀ r ∈ covData.pairs ++ covData.anchors, ∃ gt : E, X.φ gt = r.g :=
    fun r _ => hrange _ r.g_mem
  have hT := covCheck_good covCheck_covData
  have hzero := covCheck_vanish covData covCheck_covData X xt hxt hlift u hu huc
  obtain ⟨s, hs⟩ := exists_section X xt hT hxt hzero
  let Sg := covData.tab.sub covData.x hT
  have hSgD : Sg ≤ PP := by
    rintro g ⟨v, -, rfl⟩
    exact Subgroup.list_prod_mem _ fun y hy => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
      exact hxmem i
  have hcardSg : Nat.card Sg = 512 := by
    rw [CayTab.card_sub hT]
    exact covData_nV
  have hP : Nat.card PP = 44352000 := by
    have := card_hsP
    rw [hsP_eq_original] at this
    exact this
  have hidx : (Sg.subgroupOf PP).index = 86625 := by
    have h1 := Subgroup.card_mul_index (Sg.subgroupOf PP)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSgD).toEquiv, hcardSg, hP] at h1
    omega
  exact false_of_section X hrange hφmem (by rw [hidx]; decide) s hs

end CFSG.QuasithinUnique.Ch1.HSCover

namespace CFSG.QuasithinUnique.Ch1

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519 CFSG.QuasithinUnique.Id2519.UHS
open CFSG.QuasithinUnique.Ch1.HSCover
open CFSG.Sporadic.Schreier

theorem tabHSCover
    : TabHSCover := by
  classical
  intro G _ _ X K t hXq hZ2 hiso hZne htX htt hK hA6
  obtain ⟨e⟩ := hiso
  have : Finite ↥X := inferInstance
  have hperf : Group.IsPerfect ↥X := hXq.1
  let ψ : ↥X ⧸ Subgroup.center ↥X ≃* PP :=
    (e.trans hsPermEquiv).trans (MulEquiv.subgroupCongr hsP_eq_original)
  let π' : ↥X →* PP := ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))
  let π : ↥X →* Equiv.Perm (Fin 3850) := PP.subtype.comp π'
  have hπ : ∀ x, π x = ((ψ (x : ↥X ⧸ Subgroup.center ↥X) : PP) : Equiv.Perm (Fin 3850)) :=
    fun x => rfl
  have hπ1 : ∀ x, π x = 1 ↔ x ∈ Subgroup.center ↥X := by
    intro x
    rw [hπ]
    constructor
    · intro h
      have h1 : ψ (x : ↥X ⧸ Subgroup.center ↥X) = 1 := Subtype.ext h
      rw [map_eq_one_iff ψ ψ.injective] at h1
      exact (QuotientGroup.eq_one_iff x).1 h1
    · intro h
      rw [(QuotientGroup.eq_one_iff x).2 h]
      simp
  have hπmem : ∀ x, π x ∈ PP := fun x => (π' x).2
  have hπsurj : ∀ y ∈ PP, ∃ x, π x = y := by
    intro y hy
    obtain ⟨q, hq⟩ := ψ.surjective ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨x, by rw [hπ, hq]⟩
  have hP : Nat.card PP = 44352000 := by
    have := card_hsP
    rw [hsP_eq_original] at this
    exact this
  have hcardX : 360 < Nat.card ↥X := by
    have h1 : Nat.card (↥X ⧸ Subgroup.center ↥X) = 44352000 := by
      rw [Nat.card_congr ψ.toEquiv, hP]
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥X)
    have h3 : 0 < Nat.card (Subgroup.center ↥X) := Nat.card_pos
    rw [h1] at h2
    omega
  let t' : ↥X := ⟨t, htX⟩
  have ht'2 : t' * t' = 1 := Subtype.ext htt
  have ht'Z : t' ∉ Subgroup.center ↥X := t_not_central htX hXq hK hA6 hcardX
  let s : PP := π' t'
  have hsπ : (s : Equiv.Perm (Fin 3850)) = π t' := rfl
  have hs2 : s * s = 1 := by
    show π' t' * π' t' = 1
    rw [← map_mul, ht'2, map_one]
  have hs1 : s ≠ 1 := fun h => ht'Z ((hπ1 t').1 (hsπ.symm.trans (congrArg Subtype.val h)))
  have hKXC : K ≤ X ⊓ Subgroup.centralizer ({t} : Set G) := hK.1
  have hKX : K ≤ X := hKXC.trans inf_le_left
  obtain ⟨hKs, hKnc, hK360⟩ := isA6_facts hA6
  have hK'simple : IsSimpleGroup ↥(K.subgroupOf X) :=
    (Subgroup.subgroupOfEquivOfLe hKX).isSimpleGroup
  have hK'card : Nat.card ↥(K.subgroupOf X) = 360 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv]
    exact hK360
  have hK'c : ∀ k ∈ K.subgroupOf X, k * t' = t' * k := by
    intro k hk
    have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.1 hk
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hKXC hkK).2
    exact Subtype.ext h1
  let ρ : ↥(K.subgroupOf X) →* PP := π'.comp (K.subgroupOf X).subtype
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hK'simple.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exact h
    · exfalso
      have hZ : ∀ k ∈ K.subgroupOf X, k ∈ Subgroup.center ↥X := by
        intro k hk
        have h1 : (⟨k, hk⟩ : ↥(K.subgroupOf X)) ∈ ρ.ker := by rw [h]; exact Subgroup.mem_top _
        have h2 : ρ ⟨k, hk⟩ = 1 := h1
        have h3 : π k = ((ρ ⟨k, hk⟩ : PP) : Equiv.Perm (Fin 3850)) := rfl
        exact (hπ1 k).1 (h3.trans (congrArg Subtype.val h2))
      obtain ⟨a, b, hab⟩ := hKnc
      apply hab
      have h1 := Subgroup.mem_center_iff.1
        (hZ ⟨a.1, hKX a.2⟩ (Subgroup.mem_subgroupOf.2 a.2)) ⟨b.1, hKX b.2⟩
      have h2 := congrArg Subtype.val h1
      exact Subtype.ext h2.symm
  have hK''card : Nat.card ρ.range = 360 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv]
    exact hK'card
  have hK''c : ∀ k ∈ ρ.range, k * s = s * k := by
    rintro _ ⟨k', rfl⟩
    have h1 := hK'c k'.1 k'.2
    have h2 := congrArg π' h1
    rw [map_mul, map_mul] at h2
    exact h2
  obtain ⟨d, hd, hdc⟩ := exists_conj_hsC s hs2 hs1 ρ.range hK''card hK''c
  obtain ⟨H, n, hHZ, hnZ, hnH, hnn, hcover⟩ :=
    exists_halving_of_pgroup (le_refl (Subgroup.center ↥X)) hZ2 hZne
  have : H.Normal := Subgroup.normal_of_le_center hHZ
  have hHπ : ∀ h ∈ H, π h = 1 := fun h hh => (hπ1 h).2 (hHZ hh)
  have hnπ : π n = 1 := (hπ1 n).2 hnZ
  have hnc : ∀ k : ↥X, n * k = k * n := fun k => (Subgroup.mem_center_iff.1 hnZ k).symm
  have hker : ∀ k, π k = 1 → k ∈ H ∨ n * k ∈ H := fun k hk => hcover k ((hπ1 k).1 hk)
  obtain ⟨X', hX'⟩ := exists_quotExt' π H n hHπ hnπ hnH hnn hnc hker
  have : Finite (↥X ⧸ H) := inferInstance
  have : Group.IsPerfect (↥X ⧸ H) := inferInstance
  have hrange : ∀ y ∈ PP, ∃ e : ↥X ⧸ H, X'.φ e = y := by
    intro y hy
    obtain ⟨x, hx⟩ := hπsurj y hy
    exact ⟨(x : ↥X ⧸ H), by rw [hX', hx]⟩
  have hφmem : ∀ e, X'.φ e ∈ PP := by
    intro e
    induction e using QuotientGroup.induction_on with
    | _ k => rw [hX' k]; exact hπmem k
  obtain ⟨dt, hdt⟩ := hrange d hd
  have hmk : (t' : ↥X ⧸ H) * (t' : ↥X ⧸ H) = 1 := by
    rw [← QuotientGroup.mk_mul, ht'2, QuotientGroup.mk_one]
  have hu : (dt⁻¹ * (t' : ↥X ⧸ H) * dt) * (dt⁻¹ * (t' : ↥X ⧸ H) * dt) = 1 := by
    calc (dt⁻¹ * (t' : ↥X ⧸ H) * dt) * (dt⁻¹ * (t' : ↥X ⧸ H) * dt)
        = dt⁻¹ * ((t' : ↥X ⧸ H) * (t' : ↥X ⧸ H)) * dt := by group
      _ = 1 := by rw [hmk]; group
  have hcc : UHS.hsC = cElt := by rw [cElt_eq]; rfl
  have huc : X'.φ (dt⁻¹ * (t' : ↥X ⧸ H) * dt) = cElt := by
    rw [map_mul, map_mul, map_inv, hdt, hX' t', ← hsπ, hdc, ← hcc]
    group
  exact hs_no_involution_over_c X' hrange hφmem _ hu huc

end CFSG.QuasithinUnique.Ch1
