module

public import CFSG.LocalAnalysis.Asc75.Central
public import CFSG.LocalAnalysis.Asc75.Restrict
public import CFSG.LocalAnalysis.Asc75.Interface

public section

namespace CFSG.Asc75

open CFSG CFSG.Open

@[expose] def DisjointLemma (G : Type) [Group G] [Finite G] : Prop :=
  ∀ S A₁ A₂ H : Subgroup G, Hyp S A₁ A₂ H → A₁ ⊓ A₂ = ⊥ → H = ⊤

@[expose] def IndHyp (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (G' : Type) [Group G'] [Finite G'], Nat.card G' < Nat.card G → DisjointLemma G'

section Induction

variable {G : Type} [Group G] [Finite G] {S A₁ A₂ H : Subgroup G}

theorem Hyp.centralizer_diag_le_normalized (IH : IndHyp G) (h : Hyp S A₁ A₂ H)
    (hdisj : A₁ ⊓ A₂ = ⊥) {b₁ b₂ : G} (hb₁ : b₁ ∈ A₁) (hb₂ : b₂ ∈ A₂) (hb₁1 : b₁ ≠ 1)
    (hb₂1 : b₂ ≠ 1) (hb₁2 : b₁ * b₁ = 1) (hb₂2 : b₂ * b₂ = 1)
    (hnc : ¬ ∀ g : G, g * (b₁ * b₂) = (b₁ * b₂) * g)
    (hsyl : ¬ 2 ∣ (S ⊓ Subgroup.centralizer ({b₁ * b₂} : Set G)).relIndex
      (Subgroup.centralizer ({b₁ * b₂} : Set G))) :
    Subgroup.centralizer ({b₁ * b₂} : Set G) ≤ H := by
  set K : Subgroup G := Subgroup.centralizer ({b₁ * b₂} : Set G) with hKdef
  have hrank₁ : 2 ≤ CFSG.Open.pRank 2 (A₁ ⊓ K) := by
    have := two_le_pRank_inf_centralizer (h.pgroup.to_le h.le₁)
      (by have := h.rank₁; omega) hb₁ hb₁1 hb₁2
    refine this.trans (CFSG.SectionRank.pRank_mono one_lt_two ?_)
    intro x hx
    refine ⟨hx.1, ?_⟩
    show x ∈ Subgroup.centralizer ({b₁ * b₂} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxb₁ : x * b₁ = b₁ * x := Subgroup.mem_centralizer_singleton_iff.1 hx.2
    have hxb₂ : x * b₂ = b₂ * x := h.comm x hx.1 b₂ hb₂
    calc x * (b₁ * b₂) = (x * b₁) * b₂ := by group
      _ = (b₁ * x) * b₂ := by rw [hxb₁]
      _ = b₁ * (x * b₂) := by group
      _ = b₁ * (b₂ * x) := by rw [hxb₂]
      _ = (b₁ * b₂) * x := by group
  have hrank₂ : 2 ≤ CFSG.Open.pRank 2 (A₂ ⊓ K) := by
    have := two_le_pRank_inf_centralizer (h.pgroup.to_le h.le₂)
      (by have := h.rank₂; omega) hb₂ hb₂1 hb₂2
    refine this.trans (CFSG.SectionRank.pRank_mono one_lt_two ?_)
    intro x hx
    refine ⟨hx.1, ?_⟩
    show x ∈ Subgroup.centralizer ({b₁ * b₂} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxb₂ : x * b₂ = b₂ * x := Subgroup.mem_centralizer_singleton_iff.1 hx.2
    have hxb₁ : b₁ * x = x * b₁ := h.comm b₁ hb₁ x hx.1
    calc x * (b₁ * b₂) = (x * b₁) * b₂ := by group
      _ = (b₁ * x) * b₂ := by rw [hxb₁]
      _ = b₁ * (x * b₂) := by group
      _ = b₁ * (b₂ * x) := by rw [hxb₂]
      _ = (b₁ * b₂) * x := by group
  have hlt : Nat.card ↥K < Nat.card G := by
    refine lt_of_le_of_ne (Subgroup.card_le_card_group K) ?_
    intro heq
    apply hnc
    have htop : K = ⊤ := (Subgroup.card_eq_iff_eq_top K).1 heq
    intro g
    have : g ∈ K := by rw [htop]; trivial
    exact Subgroup.mem_centralizer_singleton_iff.1 this
  have hdisjK : ((A₁ ⊓ K).subgroupOf K) ⊓ ((A₂ ⊓ K).subgroupOf K) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    have h1 := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx1)).1
    have h2 := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx2)).1
    have hm : (x : G) ∈ A₁ ⊓ A₂ := ⟨h1, h2⟩
    rw [hdisj, Subgroup.mem_bot] at hm
    rw [Subgroup.mem_bot]
    exact Subtype.ext hm
  have hK := h.restrict hdisj K hsyl hrank₁ hrank₂
  have htop := IH ↥K hlt _ _ _ _ hK hdisjK
  intro x hx
  have hxc : (⟨x, hx⟩ : ↥K) ∈ Subgroup.closure
      (genSet ((A₁ ⊓ K).subgroupOf K) ((A₂ ⊓ K).subgroupOf K)) := by
    rw [htop]; trivial
  exact h.closure_genSet_le K hxc

theorem Hyp.centralizer_diag_le (IH : IndHyp G) (h : Hyp S A₁ A₂ H) (hdisj : A₁ ⊓ A₂ = ⊥)
    (hne : H ≠ ⊤) {a₁ a₂ : G} (ha₁ : a₁ ∈ A₁) (ha₂ : a₂ ∈ A₂) (ha₁1 : a₁ ≠ 1) (ha₂1 : a₂ ≠ 1)
    (ha₁2 : a₁ * a₁ = 1) (ha₂2 : a₂ * a₂ = 1) :
    Subgroup.centralizer ({a₁ * a₂} : Set G) ≤ H := by
  have hnc : ¬ ∀ g : G, g * (a₁ * a₂) = (a₁ * a₂) * g := fun hc =>
    hne (h.eq_top_of_central_diag hdisj ha₁ ha₂ ha₁1 ha₂1 ha₁2 ha₂2 hc)
  have hint : ∀ x, x ∈ A₁ → x ∈ A₂ → x = 1 := fun x hx1 hx2 => by
    have : x ∈ A₁ ⊓ A₂ := ⟨hx1, hx2⟩
    rw [hdisj, Subgroup.mem_bot] at this
    exact this
  have hc12 : a₁ * a₂ = a₂ * a₁ := h.comm a₁ ha₁ a₂ ha₂
  have hne12 : a₁ ≠ a₂ := fun e => ha₁1 (hint a₁ ha₁ (e ▸ ha₂))
  obtain ⟨u, hu⟩ : ∃ u : G, u = a₁ * a₂ := ⟨_, rfl⟩
  rw [← hu] at hnc ⊢
  set K : Subgroup G := Subgroup.centralizer ({u} : Set G) with hKdef
  have ha₁K : a₁ ∈ K := by
    rw [hKdef, Subgroup.mem_centralizer_singleton_iff, hu]
    calc a₁ * (a₁ * a₂) = a₁ * (a₂ * a₁) := by rw [hc12]
      _ = (a₁ * a₂) * a₁ := by group
  have ha₂K : a₂ ∈ K := by
    rw [hKdef, Subgroup.mem_centralizer_singleton_iff, hu]
    calc a₂ * (a₁ * a₂) = (a₂ * a₁) * a₂ := by group
      _ = (a₁ * a₂) * a₂ := by rw [hc12]
  have hWS : Subgroup.closure ({a₁, a₂} : Set G) ≤ S := (Subgroup.closure_le _).2 (by
    intro x hx
    rcases hx with rfl | hx
    · exact h.le₁ ha₁
    · rw [Set.mem_singleton_iff.mp hx]; exact h.le₂ ha₂)
  have hWK : Subgroup.closure ({a₁, a₂} : Set G) ≤ K := (Subgroup.closure_le _).2 (by
    intro x hx
    rcases hx with rfl | hx
    · exact ha₁K
    · rw [Set.mem_singleton_iff.mp hx]; exact ha₂K)
  obtain ⟨P, hPK, hWP, hP2, hPsyl⟩ := exists_sylow_le_of_isPGroup K _ hWK (h.pgroup.to_le hWS)
  have ha₁P : a₁ ∈ P := hWP (Subgroup.subset_closure (by simp))
  have ha₂P : a₂ ∈ P := hWP (Subgroup.subset_closure (by simp))
  have hfa₁ : FixedOnlyElt H a₁ := h.fixedOnlyElt hdisj (Or.inl ha₁) ha₁1
  have hPH : P ≤ H := isPGroup_le_of_fixedOnlyElt hP2 ha₁P hfa₁
  obtain ⟨c, hcH, hc⟩ := exists_conj_mem_sylow H h.sylowG h.S_le_H P hPH hP2
  have hb₁S : c⁻¹ * a₁ * c ∈ S := hc a₁ ha₁P
  have hb₂S : c⁻¹ * a₂ * c ∈ S := hc a₂ ha₂P
  have hb₁U : c⁻¹ * a₁ * c ∈ uSet A₁ A₂ := h.closed_G hdisj (Or.inl ha₁) hb₁S
  have hb₂U : c⁻¹ * a₂ * c ∈ uSet A₁ A₂ := h.closed_G hdisj (Or.inr ha₂) hb₂S
  have hb₁2 : (c⁻¹ * a₁ * c) * (c⁻¹ * a₁ * c) = 1 := by
    calc (c⁻¹ * a₁ * c) * (c⁻¹ * a₁ * c) = c⁻¹ * (a₁ * a₁) * c := by group
      _ = 1 := by rw [ha₁2]; group
  have hb₂2 : (c⁻¹ * a₂ * c) * (c⁻¹ * a₂ * c) = 1 := by
    calc (c⁻¹ * a₂ * c) * (c⁻¹ * a₂ * c) = c⁻¹ * (a₂ * a₂) * c := by group
      _ = 1 := by rw [ha₂2]; group
  have hconj_ne : ∀ x : G, x ≠ 1 → c⁻¹ * x * c ≠ 1 := fun x hx e => hx (by
    calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
      _ = 1 := by rw [e]; group)
  have hb₁1 : c⁻¹ * a₁ * c ≠ 1 := hconj_ne a₁ ha₁1
  have hb₂1 : c⁻¹ * a₂ * c ≠ 1 := hconj_ne a₂ ha₂1
  have hbcomm : (c⁻¹ * a₁ * c) * (c⁻¹ * a₂ * c) = (c⁻¹ * a₂ * c) * (c⁻¹ * a₁ * c) := by
    calc (c⁻¹ * a₁ * c) * (c⁻¹ * a₂ * c) = c⁻¹ * (a₁ * a₂) * c := by group
      _ = c⁻¹ * (a₂ * a₁) * c := by rw [hc12]
      _ = (c⁻¹ * a₂ * c) * (c⁻¹ * a₁ * c) := by group
  have hbne : c⁻¹ * a₁ * c ≠ c⁻¹ * a₂ * c := by
    intro e
    apply hne12
    calc a₁ = c * (c⁻¹ * a₁ * c) * c⁻¹ := by group
      _ = c * (c⁻¹ * a₂ * c) * c⁻¹ := by rw [e]
      _ = a₂ := by group
  have hu' : c⁻¹ * u * c = (c⁻¹ * a₁ * c) * (c⁻¹ * a₂ * c) := by rw [hu]; group
  have hKconj : Subgroup.centralizer ({c⁻¹ * u * c} : Set G) = conjugate K c :=
    centralizer_singleton_conj u c
  have hreduce : Subgroup.centralizer ({c⁻¹ * u * c} : Set G) ≤ H → K ≤ H := by
    intro hK' x hx
    have hxc : c⁻¹ * x * c ∈ Subgroup.centralizer ({c⁻¹ * u * c} : Set G) := by
      rw [hKconj, mem_conjugate_iff]
      rwa [show c * (c⁻¹ * x * c) * c⁻¹ = x by group]
    have := hK' hxc
    have e : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem hcH this) (H.inv_mem hcH)
  have hnc' : ¬ ∀ g : G, g * (c⁻¹ * u * c) = (c⁻¹ * u * c) * g := by
    intro hcen
    apply hnc
    intro g
    have := hcen (c⁻¹ * g * c)
    calc g * u = c * (c⁻¹ * g * c * (c⁻¹ * u * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * u * c) * (c⁻¹ * g * c)) * c⁻¹ := by rw [this]
      _ = u * g := by group
  have hsyl' : ¬ 2 ∣ (S ⊓ Subgroup.centralizer ({c⁻¹ * u * c} : Set G)).relIndex
      (Subgroup.centralizer ({c⁻¹ * u * c} : Set G)) := by
    rw [hKconj]
    exact not_two_dvd_relIndex_inf_conjugate hPK hc hPsyl
  have key : ∀ b₁ b₂ : G, b₁ ∈ A₁ → b₂ ∈ A₂ → b₁ ≠ 1 → b₂ ≠ 1 → b₁ * b₁ = 1 → b₂ * b₂ = 1 →
      b₁ * b₂ = c⁻¹ * u * c → K ≤ H := by
    intro b₁ b₂ hb₁A hb₂A hb₁1' hb₂1' hb₁2' hb₂2' hbu
    apply hreduce
    rw [← hbu] at hnc' hsyl' ⊢
    exact h.centralizer_diag_le_normalized IH hdisj hb₁A hb₂A hb₁1' hb₂1' hb₁2' hb₂2' hnc' hsyl'
  have hKH : K ≤ H := by
    rcases hb₁U with hb₁A | hb₁A <;> rcases hb₂U with hb₂A | hb₂A
    ·
      have hprod : (c⁻¹ * a₁ * c) * (c⁻¹ * a₂ * c) ∈ uSet A₁ A₂ :=
        Or.inl (A₁.mul_mem hb₁A hb₂A)
      have hprod1 : (c⁻¹ * a₁ * c) * (c⁻¹ * a₂ * c) ≠ 1 := by
        intro e
        apply hbne
        have : c⁻¹ * a₁ * c = (c⁻¹ * a₂ * c)⁻¹ := eq_inv_of_mul_eq_one_left e
        rw [this]
        exact inv_eq_of_mul_eq_one_right hb₂2
      have hf := h.fixedOnlyElt hdisj hprod hprod1
      exact hreduce (by rw [hu']; exact hf.centralizer_le)
    · exact key _ _ hb₁A hb₂A hb₁1 hb₂1 hb₁2 hb₂2 hu'.symm
    · refine key (c⁻¹ * a₂ * c) (c⁻¹ * a₁ * c) hb₂A hb₁A hb₂1 hb₁1 hb₂2 hb₁2 ?_
      rw [hu', hbcomm]
    ·
      have hprod : (c⁻¹ * a₁ * c) * (c⁻¹ * a₂ * c) ∈ uSet A₁ A₂ :=
        Or.inr (A₂.mul_mem hb₁A hb₂A)
      have hprod1 : (c⁻¹ * a₁ * c) * (c⁻¹ * a₂ * c) ≠ 1 := by
        intro e
        apply hbne
        have : c⁻¹ * a₁ * c = (c⁻¹ * a₂ * c)⁻¹ := eq_inv_of_mul_eq_one_left e
        rw [this]
        exact inv_eq_of_mul_eq_one_right hb₂2
      have hf := h.fixedOnlyElt hdisj hprod hprod1
      exact hreduce (by rw [hu']; exact hf.centralizer_le)
  exact hKH

theorem Hyp.mem_of_diag_conj_mem (IH : IndHyp G) (h : Hyp S A₁ A₂ H) (hdisj : A₁ ⊓ A₂ = ⊥)
    (hne : H ≠ ⊤) {a₁ a₂ : G} (ha₁ : a₁ ∈ A₁) (ha₂ : a₂ ∈ A₂) (ha₁1 : a₁ ≠ 1) (ha₂1 : a₂ ≠ 1)
    (ha₁2 : a₁ * a₁ = 1) (ha₂2 : a₂ * a₂ = 1) {g : G} (hg : g⁻¹ * (a₁ * a₂) * g ∈ S) :
    g ∈ H := by
  by_contra hgH
  have hC := h.centralizer_diag_le IH hdisj hne ha₁ ha₂ ha₁1 ha₂1 ha₁2 ha₂2
  have hint : ∀ x, x ∈ A₁ → x ∈ A₂ → x = 1 := fun x hx1 hx2 => by
    have : x ∈ A₁ ⊓ A₂ := ⟨hx1, hx2⟩
    rw [hdisj, Subgroup.mem_bot] at this
    exact this
  have hc12 : a₁ * a₂ = a₂ * a₁ := h.comm a₁ ha₁ a₂ ha₂
  have hne12 : a₁ ≠ a₂ := fun e => ha₁1 (hint a₁ ha₁ (e ▸ ha₂))
  obtain ⟨u, hu⟩ : ∃ u : G, u = a₁ * a₂ := ⟨_, rfl⟩
  rw [← hu] at hC hg
  have hu2 : u * u = 1 := by
    rw [hu]
    calc a₁ * a₂ * (a₁ * a₂) = a₁ * (a₂ * a₁) * a₂ := by group
      _ = a₁ * (a₁ * a₂) * a₂ := by rw [hc12]
      _ = (a₁ * a₁) * (a₂ * a₂) := by group
      _ = 1 := by rw [ha₁2, ha₂2, one_mul]
  obtain ⟨t, ht⟩ : ∃ t : G, t = g⁻¹ * u * g := ⟨_, rfl⟩
  rw [← ht] at hg
  have ht2 : t * t = 1 := by
    rw [ht]
    calc g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g := by group
      _ = 1 := by rw [hu2]; group
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htt' : t⁻¹ * t⁻¹ = 1 := by rw [htinv, ht2]
  have hcent : ∀ x : G, x * t = t * x → x ∈ conjugate H g := by
    intro x hx
    rw [mem_conjugate_iff]
    apply hC
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * x * g⁻¹ * u = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by group
      _ = g * (x * t) * g⁻¹ := by rw [← ht]
      _ = g * (t * x) * g⁻¹ := by rw [hx]
      _ = u * (g * x * g⁻¹) := by rw [ht]; group
  have hC₁ : ∀ a ∈ A₁, a * t = t * a → a = 1 := by
    intro a haA hat
    by_contra ha1
    have hfa : FixedOnlyElt H a := h.fixedOnlyElt hdisj (Or.inl haA) ha1
    have hconj : g * a * g⁻¹ ∈ H := mem_conjugate_iff.1 (hcent a hat)
    have hginv : g⁻¹ ∈ H := hfa.2 g⁻¹ (by simpa using hconj)
    exact hgH (by simpa using H.inv_mem hginv)
  have htS : t ∈ S := hg
  have hswap : conjugate A₁ t = A₂ ∧ conjugate A₂ t = A₁ := by
    rcases swap_dichotomy_disjoint hdisj h.ne_bot₁ h.ne_bot₂ (h.S_le_stab htS) with
      ⟨hn1, -⟩ | hs
    · exfalso
      have hQ : IsPGroup 2 (Subgroup.zpowers t ⊔ A₁ : Subgroup G) :=
        h.pgroup.to_le (sup_le ((Subgroup.zpowers_le).2 htS) h.le₁)
      obtain ⟨a, haA, ha1, hat⟩ := exists_comm_of_normalizes h.ne_bot₁ hn1 hQ
      exact ha1 (hC₁ a haA hat)
    · exact hs
  have hdA : ∀ a ∈ A₁, t⁻¹ * a * t ∈ A₂ := by
    intro a ha
    have := conj_mem_conjugate ha t
    rwa [hswap.1] at this
  have hdd_comm : ∀ a ∈ A₁, t⁻¹ * (a * (t⁻¹ * a * t)) * t = a * (t⁻¹ * a * t) := by
    intro a haA
    have hc := h.comm a haA (t⁻¹ * a * t) (hdA a haA)
    calc t⁻¹ * (a * (t⁻¹ * a * t)) * t = (t⁻¹ * a * t) * (t⁻¹ * (t⁻¹ * a * t) * t) := by group
      _ = (t⁻¹ * a * t) * a := by
        congr 1
        calc t⁻¹ * (t⁻¹ * a * t) * t = (t⁻¹ * t⁻¹) * a * (t * t) := by group
          _ = a := by rw [htt', ht2, one_mul, mul_one]
      _ = a * (t⁻¹ * a * t) := hc.symm
  have hdd_mul : ∀ a ∈ A₁, ∀ a' ∈ A₁, (a * a') * (t⁻¹ * (a * a') * t) =
      (a * (t⁻¹ * a * t)) * (a' * (t⁻¹ * a' * t)) := by
    intro a ha a' ha'
    have hc := h.comm a' ha' (t⁻¹ * a * t) (hdA a ha)
    calc (a * a') * (t⁻¹ * (a * a') * t) = a * (a' * (t⁻¹ * a * t)) * (t⁻¹ * a' * t) := by group
      _ = a * ((t⁻¹ * a * t) * a') * (t⁻¹ * a' * t) := by rw [hc]
      _ = (a * (t⁻¹ * a * t)) * (a' * (t⁻¹ * a' * t)) := by group
  have hddS : ∀ a ∈ A₁, a * (t⁻¹ * a * t) ∈ S := fun a ha =>
    S.mul_mem (h.le₁ ha) (S.mul_mem (S.mul_mem (S.inv_mem htS) (h.le₁ ha)) htS)
  have hdd_ne : ∀ a ∈ A₁, a ≠ 1 → a * (t⁻¹ * a * t) ≠ 1 := by
    intro a ha ha1 e
    apply ha1
    apply hint a ha
    have : a = (t⁻¹ * a * t)⁻¹ := eq_inv_of_mul_eq_one_left e
    rw [this]
    exact A₂.inv_mem (hdA a ha)
  have hdd_sq : ∀ a ∈ A₁, a * a = 1 → (a * (t⁻¹ * a * t)) * (a * (t⁻¹ * a * t)) = 1 := by
    intro a ha haa
    rw [← hdd_mul a ha a ha, haa]
    group
  have hdA_sq : ∀ a, a * a = 1 → (t⁻¹ * a * t) * (t⁻¹ * a * t) = 1 := by
    intro a haa
    calc (t⁻¹ * a * t) * (t⁻¹ * a * t) = t⁻¹ * (a * a) * t := by group
      _ = 1 := by rw [haa]; group
  have hdA_ne : ∀ a, a ≠ 1 → t⁻¹ * a * t ≠ 1 := fun a ha e => ha (by
    calc a = t * (t⁻¹ * a * t) * t⁻¹ := by group
      _ = 1 := by rw [e]; group)
  obtain ⟨E, hEA, hE, hEcard⟩ := exists_card_four (A := A₁) (by have := h.rank₁; omega)
  obtain ⟨a, haE, a', ha'E, ha1, ha'1, haa'⟩ := exists_two_ne_one (E := E) (by omega)
  have haA : a ∈ A₁ := hEA haE
  have ha'A : a' ∈ A₁ := hEA ha'E
  have haa : a * a = 1 := by rw [← sq]; exact hE.2 a haE
  have ha'a' : a' * a' = 1 := by rw [← sq]; exact hE.2 a' ha'E
  have hcomm_aa' : a * a' = a' * a := by
    have h1 := hE.1.is_comm.comm (⟨a, haE⟩ : E) ⟨a', ha'E⟩
    exact congrArg Subtype.val h1
  set x : G := a * (t⁻¹ * a * t) with hx
  set y : G := a' * (t⁻¹ * a' * t) with hy
  have hxt : x * t = t * x := by
    have := hdd_comm a haA
    calc x * t = t * (t⁻¹ * x * t) := by group
      _ = t * x := by rw [hx, this]
  have hyt : y * t = t * y := by
    have := hdd_comm a' ha'A
    calc y * t = t * (t⁻¹ * y * t) := by group
      _ = t * y := by rw [hy, this]
  have hxy : x * y = y * x := by
    rw [hx, hy, ← hdd_mul a haA a' ha'A, ← hdd_mul a' ha'A a haA, hcomm_aa']
  have hxS : x ∈ S := hddS a haA
  have hyS : y ∈ S := hddS a' ha'A
  have hxK : x ∈ conjugate H g := hcent x hxt
  have hyK : y ∈ conjugate H g := hcent y hyt
  have hK := h.conj g
  have hB : conjugate A₁ g ⊓ conjugate A₂ g = ⊥ := by
    rw [← conjugate_inf, hdisj, conjugate_bot]
  have hWS : Subgroup.closure ({x, y} : Set G) ≤ S := (Subgroup.closure_le _).2 (by
    intro z hz
    rcases hz with rfl | hz
    · exact hxS
    · rw [Set.mem_singleton_iff.mp hz]; exact hyS)
  have hWK : Subgroup.closure ({x, y} : Set G) ≤ conjugate H g := (Subgroup.closure_le _).2 (by
    intro z hz
    rcases hz with rfl | hz
    · exact hxK
    · rw [Set.mem_singleton_iff.mp hz]; exact hyK)
  obtain ⟨k, hkK, hk⟩ := exists_conj_mem_sylow (conjugate H g) hK.sylowG hK.S_le_H _ hWK
    (h.pgroup.to_le hWS)
  have hxW : x ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hyW : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hxyW : x * y ∈ Subgroup.closure ({x, y} : Set G) :=
    Subgroup.mul_mem _ hxW hyW
  have hxT : k⁻¹ * x * k ∈ conjugate S g := hk x hxW
  have hyT : k⁻¹ * y * k ∈ conjugate S g := hk y hyW
  have hv : ∃ a'' ∈ A₁, a'' ≠ 1 ∧ a'' * a'' = 1 ∧ k⁻¹ * (a'' * (t⁻¹ * a'' * t)) * k ∈ conjugate S g ∧
      k⁻¹ * (a'' * (t⁻¹ * a'' * t)) * k ∈ Subgroup.normalizer ((conjugate A₁ g : Subgroup G) : Set G) := by
    rcases swap_dichotomy_disjoint hB hK.ne_bot₁ hK.ne_bot₂ (hK.S_le_stab hxT) with
      ⟨hn1, -⟩ | ⟨hs1, hs2⟩
    · exact ⟨a, haA, ha1, haa, hxT, hn1⟩
    · rcases swap_dichotomy_disjoint hB hK.ne_bot₁ hK.ne_bot₂ (hK.S_le_stab hyT) with
        ⟨hn1', -⟩ | ⟨hs1', hs2'⟩
      · exact ⟨a', ha'A, ha'1, ha'a', hyT, hn1'⟩
      · refine ⟨a * a', A₁.mul_mem haA ha'A, ?_, ?_, ?_, ?_⟩
        · intro e
          apply haa'
          have : a = a'⁻¹ := eq_inv_of_mul_eq_one_left e
          rw [this]
          exact inv_eq_of_mul_eq_one_right ha'a'
        · calc a * a' * (a * a') = a * (a' * a) * a' := by group
            _ = a * (a * a') * a' := by rw [hcomm_aa']
            _ = (a * a) * (a' * a') := by group
            _ = 1 := by rw [haa, ha'a', one_mul]
        · rw [hdd_mul a haA a' ha'A]
          exact hk (x * y) hxyW
        · rw [hdd_mul a haA a' ha'A]
          have e : k⁻¹ * (x * y) * k = (k⁻¹ * x * k) * (k⁻¹ * y * k) := by group
          show k⁻¹ * (x * y) * k ∈ Subgroup.normalizer ((conjugate A₁ g : Subgroup G) : Set G)
          rw [e]
          refine mem_normalizer_of_conjugate_eq ?_
          rw [conjugate_mul, hs1, hs2']
  obtain ⟨a'', ha''A, ha''1, ha''2, hvT, hvN⟩ := hv
  have hQ : IsPGroup 2 (Subgroup.zpowers (k⁻¹ * (a'' * (t⁻¹ * a'' * t)) * k) ⊔ conjugate A₁ g :
      Subgroup G) := hK.pgroup.to_le (sup_le ((Subgroup.zpowers_le).2 hvT) hK.le₁)
  obtain ⟨b, hbB, hb1, hbv⟩ := exists_comm_of_normalizes hK.ne_bot₁ hvN hQ
  have hCd := h.centralizer_diag_le IH hdisj hne ha''A (hdA a'' ha''A) ha''1 (hdA_ne a'' ha''1)
    ha''2 (hdA_sq a'' ha''2)
  have hkb : k * b * k⁻¹ ∈ H := by
    apply hCd
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc k * b * k⁻¹ * (a'' * (t⁻¹ * a'' * t))
        = k * (b * (k⁻¹ * (a'' * (t⁻¹ * a'' * t)) * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * (a'' * (t⁻¹ * a'' * t)) * k) * b) * k⁻¹ := by rw [hbv]
      _ = (a'' * (t⁻¹ * a'' * t)) * (k * b * k⁻¹) := by group
  have hab : g * b * g⁻¹ ∈ A₁ := mem_conjugate_iff.1 hbB
  have hab1 : g * b * g⁻¹ ≠ 1 := fun e => hb1 (by
    calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group)
  have hfab : FixedOnlyElt H (g * b * g⁻¹) := h.fixedOnlyElt hdisj (Or.inl hab) hab1
  have hσ : g * k⁻¹ ∈ H := by
    apply hfab.2
    have e : (g * k⁻¹)⁻¹ * (g * b * g⁻¹) * (g * k⁻¹) = k * b * k⁻¹ := by group
    rw [e]
    exact hkb
  have hgk : g * k * g⁻¹ ∈ H := mem_conjugate_iff.1 hkK
  apply hgH
  have e : g = (g * k * g⁻¹) * (g * k⁻¹) := by group
  rw [e]
  exact H.mul_mem hgk hσ

theorem Hyp.fixedOnlyElt_diag (IH : IndHyp G) (h : Hyp S A₁ A₂ H) (hdisj : A₁ ⊓ A₂ = ⊥)
    (hne : H ≠ ⊤) {a₁ a₂ : G} (ha₁ : a₁ ∈ A₁) (ha₂ : a₂ ∈ A₂) (ha₁1 : a₁ ≠ 1) (ha₂1 : a₂ ≠ 1)
    (ha₁2 : a₁ * a₁ = 1) (ha₂2 : a₂ * a₂ = 1) : FixedOnlyElt H (a₁ * a₂) := by
  have hint : ∀ x, x ∈ A₁ → x ∈ A₂ → x = 1 := fun x hx1 hx2 => by
    have : x ∈ A₁ ⊓ A₂ := ⟨hx1, hx2⟩
    rw [hdisj, Subgroup.mem_bot] at this
    exact this
  have hc12 : a₁ * a₂ = a₂ * a₁ := h.comm a₁ ha₁ a₂ ha₂
  have hu2 : (a₁ * a₂) * (a₁ * a₂) = 1 := by
    calc a₁ * a₂ * (a₁ * a₂) = a₁ * (a₂ * a₁) * a₂ := by group
      _ = a₁ * (a₁ * a₂) * a₂ := by rw [hc12]
      _ = (a₁ * a₁) * (a₂ * a₂) := by group
      _ = 1 := by rw [ha₁2, ha₂2, one_mul]
  have hu1 : a₁ * a₂ ≠ 1 := by
    intro e
    have : a₁ = a₂⁻¹ := eq_inv_of_mul_eq_one_left e
    apply ha₁1
    apply hint a₁ ha₁
    rw [this]
    exact A₂.inv_mem ha₂
  refine ⟨h.S_le_H (S.mul_mem (h.le₁ ha₁) (h.le₂ ha₂)), fun g hg => ?_⟩
  obtain ⟨b, hb⟩ : ∃ b : G, b = g⁻¹ * (a₁ * a₂) * g := ⟨_, rfl⟩
  rw [← hb] at hg
  have hb1 : b ≠ 1 := by
    intro e
    apply hu1
    calc a₁ * a₂ = g * (g⁻¹ * (a₁ * a₂) * g) * g⁻¹ := by group
      _ = 1 := by rw [← hb, e]; group
  have hb2 : b * b = 1 := by
    rw [hb]
    calc g⁻¹ * (a₁ * a₂) * g * (g⁻¹ * (a₁ * a₂) * g) = g⁻¹ * ((a₁ * a₂) * (a₁ * a₂)) * g := by group
      _ = 1 := by rw [hu2]; group
  obtain ⟨k, hkH, hk⟩ := exists_conj_mem_sylow H h.sylowG h.S_le_H (Subgroup.zpowers b)
    ((Subgroup.zpowers_le).2 hg)
    (isPGroup_zpowers_of_orderOf_eq_two (orderOf_eq_two_of_mul_self_eq_one hb2 hb1))
  have hbk : k⁻¹ * b * k ∈ S := hk b (Subgroup.mem_zpowers b)
  have hgk : (g * k)⁻¹ * (a₁ * a₂) * (g * k) = k⁻¹ * b * k := by rw [hb]; group
  have hgkH : g * k ∈ H :=
    h.mem_of_diag_conj_mem IH hdisj hne ha₁ ha₂ ha₁1 ha₂1 ha₁2 ha₂2 (by rw [hgk]; exact hbk)
  have e : g = (g * k) * k⁻¹ := by group
  rw [e]
  exact H.mul_mem hgkH (H.inv_mem hkH)

theorem disjointLemma_of_endgame (hE : Asc75Endgame) (G : Type) [Group G] [Finite G] :
    DisjointLemma G := by
  suffices key : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → DisjointLemma G from
    key _ G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hn S A₁ A₂ H hHyp hdisj
    by_contra hne
    have IH : IndHyp G := fun G' _ _ hlt => ih (Nat.card G') (hn ▸ hlt) G' rfl
    exact hE G S A₁ A₂ H hHyp hdisj hne
      (fun a ha ha1 => hHyp.fixedOnlyElt hdisj ha ha1)
      (fun a₁ ha₁ a₂ ha₂ ha₁1 ha₂1 ha₁2 ha₂2 =>
        hHyp.fixedOnlyElt_diag IH hdisj hne ha₁ ha₂ ha₁1 ha₂1 ha₁2 ha₂2)

end Induction

end CFSG.Asc75
