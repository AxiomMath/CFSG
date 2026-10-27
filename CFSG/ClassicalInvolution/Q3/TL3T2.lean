module

public import CFSG.ClassicalInvolution.Q3.TL3T1

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G]

@[expose] def Indep (Ω : Set (Subgroup G)) (M : Subgroup G) : Prop :=
  ∀ N N' : Subgroup G, MaxAdj (nbrAdj Ω) M N → MaxAdj (nbrAdj Ω) M N' → N ≠ N' →
    ¬ nbrAdj Ω N N'

@[expose] def ThinAtM (Ω : Set (Subgroup G)) (M : Subgroup G) : Prop :=
  ∀ N : Subgroup G, MaxAdj (nbrAdj Ω) M N → ThinAt Ω M N

variable {Ω : Set (Subgroup G)} {K : Subgroup G} (hS : ThinStd Ω K)
include hS

omit [Finite G] hS in
theorem mem_Qz_of_maxAdj {M N : Subgroup G} (hth : ThinAtM Ω M)
    (h : MaxAdj (nbrAdj Ω) M N) {z u : G} (hz : IsUniqueInvolution M z)
    (hu : IsUniqueInvolution N u) : u ∈ Qz z :=
  mem_Qz_of_twoIn ((hth N h).1 z u hz hu)

theorem ThinStd.commute_inv {M N N' : Subgroup G} (hth : ThinAtM Ω M) (hind : Indep Ω M)
    (h : MaxAdj (nbrAdj Ω) M N) (h' : MaxAdj (nbrAdj Ω) M N') {z u u' : G}
    (hz : IsUniqueInvolution M z) (hu : IsUniqueInvolution N u)
    (hu' : IsUniqueInvolution N' u') : u * u' = u' * u := by
  have hu'Q := mem_Qz_of_maxAdj hth h' hz hu'
  by_cases heq : conjSub u' N = N
  ·
    have h1 := hu.conj_eq heq
    calc u * u' = (u' * u * u'⁻¹) * u' := by rw [h1]
      _ = u' * u := by group
  · exfalso
    have hcomm := (hS.conj_eq_or_commutes h hz hu'Q).resolve_left heq
    have hN := h.1.2.1
    have hu'C : u' ∈ Subgroup.centralizer ({z} : Set G) := (isNormalTwoIn_Qz z).1 hu'Q
    have hmax := hS.maxAdj_conj_of_mem h hz hu'C
    have hN' : conjSub u' N ∈ Ω := hS.hyp.conjInvariant u' N hN
    have hadj : nbrAdj Ω N (conjSub u' N) := by
      refine ⟨hN, (mem_omegaNbr_iff hS.hyp hS.two).mpr ⟨hN', heq, fun x hx => ?_⟩⟩
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have h1 := hcomm y hy x hx
        have : x * y * x⁻¹ = y := by
          calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [← h1]
            _ = y := by group
        rw [this]
        exact hy
      · intro hy
        have h1 := hcomm _ hy x hx
        have e : y = x * y * x⁻¹ := by
          have h2 : x * y = x * (x * y * x⁻¹) := by
            calc x * y = x * y * x⁻¹ * x := by group
              _ = x * (x * y * x⁻¹) := h1
          exact mul_left_cancel h2
        rw [e]
        exact hy
    exact hind N _ h hmax (Ne.symm heq) hadj

theorem ThinStd.comm_mem_of_mem_Qz {M L : Subgroup G} (hth : ThinAtM Ω M)
    (h : MaxAdj (nbrAdj Ω) M L) {z u : G} (hz : IsUniqueInvolution M z)
    (hu : IsUniqueInvolution L u) {x : G} (hxQ : x ∈ Qz z) (hxu : x * u = u * x) {l : G}
    (hl : l ∈ L) : l * x * l⁻¹ * x⁻¹ = 1 ∨ l * x * l⁻¹ * x⁻¹ = u := by
  have hL := h.1.2.1
  have hLz : L ≤ Subgroup.centralizer ({z} : Set G) := hS.le_centralizer_of_nbrAdj h.1 hz
  have hQ := isNormalTwoIn_Qz z
  have hxN : x ∈ Subgroup.normalizer (L : Set G) :=
    hS.tight L hL u hu (Subgroup.mem_centralizer_singleton_iff.mpr hxu)
  have hmemL : l * x * l⁻¹ * x⁻¹ ∈ L := by
    have h1 : x * l⁻¹ * x⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hxN _).mp (L.inv_mem hl)
    have e : l * x * l⁻¹ * x⁻¹ = l * (x * l⁻¹ * x⁻¹) := by group
    rw [e]
    exact L.mul_mem hl h1
  have hmemQ : l * x * l⁻¹ * x⁻¹ ∈ Qz z :=
    (Qz z).mul_mem (hQ.2.2 l (hLz hl) x hxQ) ((Qz z).inv_mem hxQ)
  exact hS.eq_of_mem_Qz h.1 (hth L h) hz hu hmemL hmemQ

theorem ThinStd.not_centralizes {M L L' : Subgroup G} (hind : Indep Ω M)
    (h : MaxAdj (nbrAdj Ω) M L) (h' : MaxAdj (nbrAdj Ω) M L') (hne : L ≠ L') {u' : G}
    (hu' : IsUniqueInvolution L' u') : ¬ ∀ l ∈ L, l * u' = u' * l := by
  intro hc
  have hL := h.1.2.1
  have hL' := h'.1.2.1
  have hLN : L ≤ Subgroup.normalizer (L' : Set G) := fun l hl =>
    hS.tight L' hL' u' hu' (Subgroup.mem_centralizer_singleton_iff.mpr (hc l hl))
  have hadj : nbrAdj Ω L' L :=
    ⟨hL', (mem_omegaNbr_iff hS.hyp hS.two).mpr ⟨hL, hne, hLN⟩⟩
  exact hind L' L h' h (Ne.symm hne) hadj

theorem ThinStd.centralizer_mem_USet {M L L' : Subgroup G} (hth : ThinAtM Ω M)
    (hind : Indep Ω M) (h : MaxAdj (nbrAdj Ω) M L) (h' : MaxAdj (nbrAdj Ω) M L') (hne : L ≠ L')
    {z u u' : G} (hz : IsUniqueInvolution M z) (hu : IsUniqueInvolution L u)
    (hu' : IsUniqueInvolution L' u') :
    L' ⊓ Subgroup.centralizer ({u} : Set G) ∈ USet Ω := by
  classical
  have hL' := h'.1.2.1
  have h8 := hS.card L' hL'
  have h2 := hS.two L' hL'
  set C := L' ⊓ Subgroup.centralizer ({u} : Set G) with hC
  have huQ := mem_Qz_of_maxAdj hth h hz hu
  have hcomm := hS.commute_inv hth hind h h' hz hu hu'
  have hnc := hS.not_centralizes hind h' h (Ne.symm hne) hu
  push Not at hnc
  obtain ⟨l₀, hl₀, hl₀u⟩ := hnc
  have hcm : ∀ l ∈ L', l * u * l⁻¹ * u⁻¹ = 1 ∨ l * u * l⁻¹ * u⁻¹ = u' :=
    fun l hl => hS.comm_mem_of_mem_Qz hth h' hz hu' huQ hcomm hl
  have hl₀' : l₀ * u * l₀⁻¹ * u⁻¹ = u' := by
    rcases hcm l₀ hl₀ with h1 | h1
    · exfalso
      apply hl₀u
      calc l₀ * u = (l₀ * u * l₀⁻¹ * u⁻¹) * u * l₀ := by group
        _ = u * l₀ := by rw [h1]; group
    · exact h1
  have hcover : (L' : Set G) ⊆ (C : Set G) ∪ (fun x => l₀ * x) '' (C : Set G) := by
    intro l hl
    by_cases hlC : l * u = u * l
    · exact Or.inl ⟨hl, Subgroup.mem_centralizer_singleton_iff.mpr hlC⟩
    · right
      refine ⟨l₀⁻¹ * l, ⟨L'.mul_mem (L'.inv_mem hl₀) hl, ?_⟩, by group⟩
      have h1 : l * u * l⁻¹ * u⁻¹ = u' := by
        rcases hcm l hl with h1 | h1
        · exfalso
          apply hlC
          calc l * u = (l * u * l⁻¹ * u⁻¹) * u * l := by group
            _ = u * l := by rw [h1]; group
        · exact h1
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have e : l * u * l⁻¹ = l₀ * u * l₀⁻¹ := by
        have := h1.trans hl₀'.symm
        calc l * u * l⁻¹ = l * u * l⁻¹ * u⁻¹ * u := by group
          _ = l₀ * u * l₀⁻¹ * u⁻¹ * u := by rw [this]
          _ = l₀ * u * l₀⁻¹ := by group
      calc l₀⁻¹ * l * u = l₀⁻¹ * (l * u * l⁻¹) * l := by group
        _ = l₀⁻¹ * (l₀ * u * l₀⁻¹) * l := by rw [e]
        _ = u * (l₀⁻¹ * l) := by group
  have hcardC : 4 ≤ Nat.card C := by
    have h1 : Nat.card L' ≤ Nat.card C + Nat.card C := by
      have e1 : Nat.card ↥L' = (L' : Set G).ncard := Nat.card_coe_set_eq (L' : Set G)
      have e2 : Nat.card ↥C = (C : Set G).ncard := Nat.card_coe_set_eq (C : Set G)
      rw [e1, e2]
      calc (L' : Set G).ncard ≤ ((C : Set G) ∪ (fun x => l₀ * x) '' (C : Set G)).ncard :=
            Set.ncard_le_ncard hcover (Set.toFinite _)
        _ ≤ (C : Set G).ncard + ((fun x => l₀ * x) '' (C : Set G)).ncard :=
            Set.ncard_union_le _ _
        _ = (C : Set G).ncard + (C : Set G).ncard := by
            rw [Set.ncard_image_of_injective _ (mul_right_injective l₀)]
    omega
  have hCL : C ≤ L' := inf_le_left
  have hCne : Nat.card C ≠ 8 := by
    intro h4
    have : C = L' := Subgroup.eq_of_le_of_card_ge hCL (by rw [h4, h8])
    have hl₀C : l₀ ∈ C := this ▸ hl₀
    exact hl₀u (Subgroup.mem_centralizer_singleton_iff.mp hl₀C.2)
  have hdvd : Nat.card C ∣ 8 := h8 ▸ Subgroup.card_dvd_of_le hCL
  have hC4 : Nat.card C = 4 := by
    have : Nat.card C ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hdiv] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have hcyc : IsCyclic C := by
    have hex : ∃ x : C, (x : G) ≠ 1 ∧ (x : G) ≠ u' := by
      by_contra hno
      push Not at hno
      have hsub : ∀ x : C, (x : G) ∈ ({1, u'} : Set G) := by
        intro x
        by_cases hx1 : (x : G) = 1
        · exact Or.inl hx1
        · exact Or.inr (hno x hx1)
      have hinj : Function.Injective (fun x : C => (⟨x, hsub x⟩ : ({1, u'} : Set G))) := by
        intro a b hab
        have := congrArg (fun y : ({1, u'} : Set G) => (y : G)) hab
        exact Subtype.ext this
      have h1 := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_coe_set_eq] at h1
      have h2 : ({1, u'} : Set G).ncard ≤ 2 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        rw [Set.ncard_singleton]
      omega
    obtain ⟨x, hx1, hx2⟩ := hex
    have hx8 : orderOf (x : G) ∣ 4 := by
      rw [← hC4, Subgroup.orderOf_coe]
      exact orderOf_dvd_natCard x
    have hxx : (x : G) * x ≠ 1 := by
      intro hsq
      rcases hu'.unique x (hCL x.2) hsq with h1 | h1
      · exact hx1 h1
      · exact hx2 h1
    have hord : orderOf x = 4 := by
      rw [← Subgroup.orderOf_coe]
      have : orderOf (x : G) ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hx8, by norm_num⟩
      have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
      rw [hdiv] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h1 | h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hx1
      · exact absurd (by rw [← pow_two, ← h1, pow_orderOf_eq_one]) hxx
      · exact h1
    exact isCyclic_of_orderOf_eq_card x (by rw [hord, hC4])
  refine ⟨L', mem_RSet_of_isPGroup hL' h2, hCL, hcyc, ?_⟩
  have h1 := Subgroup.relIndex_mul_card C L'
  rw [inf_eq_left.mpr hCL, hC4, h8] at h1
  omega

theorem ThinStd.exists_third {M L L' : Subgroup G} (hth : ThinAtM Ω M) (hind : Indep Ω M)
    (h : MaxAdj (nbrAdj Ω) M L) (h' : MaxAdj (nbrAdj Ω) M L') (hne : L ≠ L')
    {z u u' : G} (hz : IsUniqueInvolution M z) (hu : IsUniqueInvolution L u)
    (hu' : IsUniqueInvolution L' u') :
    ∃ x ∈ L ⊔ L', MaxAdj (nbrAdj Ω) M (conjSub x L) ∧
      IsUniqueInvolution (conjSub x L) (u * u') := by
  have hL := h.1.2.1
  have hL' := h'.1.2.1
  have hCU := hS.centralizer_mem_USet hth hind h h' hne hz hu hu'
  have hstar : L' ∈ omegaStarNbr Ω L :=
    ⟨hL', Ne.symm hne, _, hCU, inf_le_left, fun c hc => hS.tight L hL u hu hc.2⟩
  have hnot : L' ∉ omegaNbr Ω L := by
    intro hJ
    have hN := ((mem_omegaNbr_iff hS.hyp hS.two).mp hJ).2.2
    apply hS.not_centralizes hind h' h (Ne.symm hne) hu
    intro l hl
    have h1 := hu.conj_eq (conjSub_eq_of_mem_normalizer (hN hl))
    calc l * u = (l * u * l⁻¹) * l := by group
      _ = u * l := by rw [h1]
  obtain ⟨g, hg, hgL⟩ := hS.aEmpty L hL L' hstar hnot u u' hu hu'
  have hgle : pairNormalizers L L' u u' ≤ L ⊔ L' := sup_le_sup inf_le_left inf_le_left
  have hgu : g * u * g⁻¹ = u' := by
    have h1 := hu.conj g
    rw [hgL] at h1
    exact h1.eq hu'
  have hu'Q := mem_Qz_of_maxAdj hth h' hz hu'
  have hcomm := hS.commute_inv hth hind h h' hz hu hu'
  have hnc := hS.not_centralizes hind h h' hne hu'
  push Not at hnc
  obtain ⟨k, hk, hku⟩ := hnc
  have hk' : k * u' * k⁻¹ * u'⁻¹ = u := by
    rcases hS.comm_mem_of_mem_Qz hth h hz hu hu'Q hcomm.symm hk with h1 | h1
    · exfalso
      apply hku
      calc k * u' = (k * u' * k⁻¹ * u'⁻¹) * u' * k := by group
        _ = u' * k := by rw [h1]; group
    · exact h1
  have hmem : k * g ∈ L ⊔ L' := (L ⊔ L').mul_mem (le_sup_left (α := Subgroup G) hk) (hgle hg)
  refine ⟨k * g, hmem, ?_, ?_⟩
  · have hLz := hS.le_centralizer_of_nbrAdj h.1 hz
    have hL'z := hS.le_centralizer_of_nbrAdj h'.1 hz
    exact hS.maxAdj_conj_of_mem h hz ((sup_le hLz hL'z) hmem)
  · have h1 := hu.conj (k * g)
    have e : k * g * u * (k * g)⁻¹ = u * u' := by
      calc k * g * u * (k * g)⁻¹ = k * (g * u * g⁻¹) * k⁻¹ := by group
        _ = k * u' * k⁻¹ := by rw [hgu]
        _ = (k * u' * k⁻¹ * u'⁻¹) * u' := by group
        _ = u * u' := by rw [hk']
    rwa [e] at h1

end CFSG.ClassicalInvolution.Q3.TC.Thin
