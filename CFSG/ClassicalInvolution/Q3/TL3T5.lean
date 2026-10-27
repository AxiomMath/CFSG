module

public import CFSG.ClassicalInvolution.Q3.TL3T4

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G]

@[expose] def CentX (Ω : Set (Subgroup G)) (M : Subgroup G) (x : G) : Prop :=
  ∀ L : Subgroup G, MaxAdj (nbrAdj Ω) M L → ∀ l ∈ L, x * l = l * x

omit [Finite G] in
theorem conj_conj_of_comm {w n : G} (h : w * n = n * w) (v : G) :
    n * (w * v * w⁻¹) * n⁻¹ = w * (n * v * n⁻¹) * w⁻¹ := by
  calc n * (w * v * w⁻¹) * n⁻¹ = (n * w) * v * (n * w)⁻¹ := by group
    _ = (w * n) * v * (w * n)⁻¹ := by rw [h]
    _ = w * (n * v * n⁻¹) * w⁻¹ := by group

omit [Finite G] in
theorem comm_of_conj_eq {x v : G} (h : x * v * x⁻¹ = v) : x * v = v * x := by
  calc x * v = (x * v * x⁻¹) * x := by group
    _ = v * x := by rw [h]

omit [Finite G] in
theorem conj_eq_of_comm {x v : G} (h : x * v = v * x) : x * v * x⁻¹ = v := by
  rw [h]
  group

omit [Finite G] in
theorem pow_four_eq (w : G) : w ^ 4 = w * w * (w * w) := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]

omit [Finite G] in
theorem comm_mul_of_transv {L : Subgroup G} {u v₁ v₂ : G} (hu : u * u = 1)
    (huL : ∀ l ∈ L, l * u = u * l) (hu₁ : u * v₁ = v₁ * u)
    (h₁ : ∀ l ∈ L, l * v₁ * l⁻¹ = v₁ ∨ l * v₁ * l⁻¹ = u * v₁)
    (h₂ : ∀ l ∈ L, l * v₂ * l⁻¹ = v₂ ∨ l * v₂ * l⁻¹ = u * v₂)
    (hne : ∃ l ∈ L, l * v₂ ≠ v₂ * l) (hno : ∀ l ∈ L, l * v₁ = v₁ * l → l * v₂ = v₂ * l) :
    ∀ l ∈ L, l * (v₁ * v₂) = v₁ * v₂ * l := by
  have key : ∀ l : G, ∀ v : G, (l * v * l⁻¹ = v ∨ l * v * l⁻¹ = u * v) → l * v ≠ v * l →
      l * v * l⁻¹ = u * v := fun l v h hne =>
    h.resolve_left fun h' => hne (comm_of_conj_eq h')
  obtain ⟨l₀, hl₀, hl₀₂⟩ := hne
  have hl₀₁ : l₀ * v₁ ≠ v₁ * l₀ := fun h => hl₀₂ (hno l₀ hl₀ h)
  have e₁ := key l₀ v₁ (h₁ l₀ hl₀) hl₀₁
  have e₂ := key l₀ v₂ (h₂ l₀ hl₀) hl₀₂
  have hul₀ : l₀⁻¹ * u * l₀ = u := by
    calc l₀⁻¹ * u * l₀ = l₀⁻¹ * (u * l₀) := by group
      _ = l₀⁻¹ * (l₀ * u) := by rw [huL l₀ hl₀]
      _ = u := by group
  have g₁ : l₀⁻¹ * v₁ * l₀ = u * v₁ := by
    calc l₀⁻¹ * v₁ * l₀ = l₀⁻¹ * (u * (u * v₁)) * l₀ := by rw [← mul_assoc u u v₁, hu, one_mul]
      _ = l₀⁻¹ * (u * (l₀ * v₁ * l₀⁻¹)) * l₀ := by rw [e₁]
      _ = (l₀⁻¹ * u * l₀) * v₁ := by group
      _ = u * v₁ := by rw [hul₀]
  intro l hl
  by_cases hl₁ : l * v₁ = v₁ * l
  · have hl₂ := hno l hl hl₁
    calc l * (v₁ * v₂) = (l * v₁) * v₂ := by group
      _ = (v₁ * l) * v₂ := by rw [hl₁]
      _ = v₁ * (l * v₂) := by group
      _ = v₁ * (v₂ * l) := by rw [hl₂]
      _ = v₁ * v₂ * l := by group
  · have f₁ := key l v₁ (h₁ l hl) hl₁
    have hm : l₀⁻¹ * l ∈ L := L.mul_mem (L.inv_mem hl₀) hl
    have hm₁ : (l₀⁻¹ * l) * v₁ = v₁ * (l₀⁻¹ * l) := by
      refine comm_of_conj_eq ?_
      calc (l₀⁻¹ * l) * v₁ * (l₀⁻¹ * l)⁻¹ = l₀⁻¹ * (l * v₁ * l⁻¹) * l₀ := by group
        _ = l₀⁻¹ * (u * v₁) * l₀ := by rw [f₁]
        _ = (l₀⁻¹ * u * l₀) * (l₀⁻¹ * v₁ * l₀) := by group
        _ = u * (u * v₁) := by rw [hul₀, g₁]
        _ = v₁ := by rw [← mul_assoc, hu, one_mul]
    have hm₂ := conj_eq_of_comm (hno _ hm hm₁)
    have f₂ : l * v₂ * l⁻¹ = u * v₂ := by
      calc l * v₂ * l⁻¹ = l₀ * ((l₀⁻¹ * l) * v₂ * (l₀⁻¹ * l)⁻¹) * l₀⁻¹ := by group
        _ = l₀ * v₂ * l₀⁻¹ := by rw [hm₂]
        _ = u * v₂ := e₂
    refine comm_of_conj_eq ?_
    calc l * (v₁ * v₂) * l⁻¹ = (l * v₁ * l⁻¹) * (l * v₂ * l⁻¹) := by group
      _ = (u * v₁) * (u * v₂) := by rw [f₁, f₂]
      _ = u * (v₁ * u) * v₂ := by group
      _ = u * (u * v₁) * v₂ := by rw [← hu₁]
      _ = (u * u) * (v₁ * v₂) := by group
      _ = v₁ * v₂ := by rw [hu, one_mul]

variable {Ω : Set (Subgroup G)} {K : Subgroup G} (hS : ThinStd Ω K)
include hS

variable {M : Subgroup G} (hth : ThinAtM Ω M) (hind : Indep Ω M) {z : G}
  (hz : IsUniqueInvolution M z)
include hth hind hz

omit hth hind in
theorem ThinStd.centX_conj {c : G} (hc : c ∈ Subgroup.centralizer ({z} : Set G)) {x : G}
    (hx : CentX Ω M x) : CentX Ω M (c * x * c⁻¹) := by
  intro L hL l hl
  have hc' : c⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := (Subgroup.centralizer _).inv_mem hc
  have hmax := hS.maxAdj_conj_of_mem hL hz hc'
  have hl' : c⁻¹ * l * c⁻¹⁻¹ ∈ conjSub c⁻¹ L := conj_mem_conjSub hl
  have h1 := hx _ hmax _ hl'
  rw [inv_inv] at h1
  calc c * x * c⁻¹ * l = c * (x * (c⁻¹ * l * c)) * c⁻¹ := by group
    _ = c * ((c⁻¹ * l * c) * x) * c⁻¹ := by rw [h1]
    _ = l * (c * x * c⁻¹) := by group

theorem ThinStd.conj_vM {L : Subgroup G} (hL : MaxAdj (nbrAdj Ω) M L) {u : G}
    (hu : IsUniqueInvolution L u) {v : G} (hv : v ∈ vM Ω M) {l : G} (hl : l ∈ L) :
    l * v * l⁻¹ = v ∨ l * v * l⁻¹ = u * v := by
  rcases hS.comm_vM hth hind hz hL hu hv hl with h | h
  · left
    calc l * v * l⁻¹ = (l * v * l⁻¹ * v⁻¹) * v := by group
      _ = v := by rw [h, one_mul]
  · right
    calc l * v * l⁻¹ = (l * v * l⁻¹ * v⁻¹) * v := by group
      _ = u * v := by rw [h]

theorem ThinStd.centX_pow_four {N : Subgroup G} (hN : MaxAdj (nbrAdj Ω) M N) {w : G}
    (hwz : w * z = z * w) (hwN : ∀ n ∈ N, w * n = n * w) : CentX Ω M (w ^ 4) := by
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hS.hyp hN.1.2.1
  have hwC : w ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hwz
  have hcV := hS.vM_comm hth hind hz
  have huV : u ∈ vM Ω M := Subgroup.subset_closure ⟨N, hN, hu⟩
  have hwu : w * u = u * w := hwN u hu.mem
  have hwV : ∀ v ∈ vM Ω M, w * v * w⁻¹ ∈ vM Ω M := by
    intro v hv
    have h1 : w * v * w⁻¹ ∈ conjSub w (vM Ω M) := conj_mem_conjSub hv
    rwa [hS.conjSub_vM hz hwC] at h1
  have h1 : ∀ v ∈ vM Ω M, w * v * w⁻¹ = v ∨ w * v * w⁻¹ = u * v := by
    intro v hv
    have hv' := hwV v hv
    have hx : w * v * w⁻¹ * v⁻¹ ∈ vM Ω M := (vM Ω M).mul_mem hv' ((vM Ω M).inv_mem hv)
    have hc : ∀ n ∈ N, n * (w * v * w⁻¹ * v⁻¹) = (w * v * w⁻¹ * v⁻¹) * n := by
      intro n hn
      have e := conj_conj_of_comm (hwN n hn) v
      rcases hS.conj_vM hth hind hz hN hu hv hn with h | h
      · have hnv' : n * (w * v * w⁻¹) * n⁻¹ = w * v * w⁻¹ := by rw [e, h]
        calc n * (w * v * w⁻¹ * v⁻¹)
            = (n * (w * v * w⁻¹) * n⁻¹) * (n * v * n⁻¹)⁻¹ * n := by group
          _ = (w * v * w⁻¹ * v⁻¹) * n := by rw [hnv', h]
      · have hnv' : n * (w * v * w⁻¹) * n⁻¹ = u * (w * v * w⁻¹) := by
          rw [e, h]
          calc w * (u * v) * w⁻¹ = (w * u) * v * w⁻¹ := by group
            _ = (u * w) * v * w⁻¹ := by rw [hwu]
            _ = u * (w * v * w⁻¹) := by group
        have h2 : u * (w * v * w⁻¹) = (w * v * w⁻¹) * u := hcV u huV _ hv'
        have h3 : u * v = v * u := hcV u huV v hv
        calc n * (w * v * w⁻¹ * v⁻¹)
            = (n * (w * v * w⁻¹) * n⁻¹) * (n * v * n⁻¹)⁻¹ * n := by group
          _ = (u * (w * v * w⁻¹)) * (u * v)⁻¹ * n := by rw [hnv', h]
          _ = ((w * v * w⁻¹) * u) * (v * u)⁻¹ * n := by rw [h2, h3]
          _ = (w * v * w⁻¹ * v⁻¹) * n := by group
    rcases hS.eq_of_centralizes hth hind hz hN hu hx hc with h | h
    · left
      calc w * v * w⁻¹ = (w * v * w⁻¹ * v⁻¹) * v := by group
        _ = v := by rw [h, one_mul]
    · right
      calc w * v * w⁻¹ = (w * v * w⁻¹ * v⁻¹) * v := by group
        _ = u * v := by rw [h]
  have h2 : ∀ v ∈ vM Ω M, (w * w) * v * (w * w)⁻¹ = v := by
    intro v hv
    have e : (w * w) * v * (w * w)⁻¹ = w * (w * v * w⁻¹) * w⁻¹ := by group
    rw [e]
    rcases h1 v hv with h | h
    · rw [h, h]
    · rw [h]
      calc w * (u * v) * w⁻¹ = (w * u * w⁻¹) * (w * v * w⁻¹) := by group
        _ = u * (u * v) := by rw [conj_eq_of_comm hwu, h]
        _ = v := by rw [← mul_assoc, hu.sq, one_mul]
  intro L hL l hl
  obtain ⟨uL, huL⟩ := Sec6Gen.exists_uniqueInvolution hS.hyp hL.1.2.1
  have huLV : uL ∈ vM Ω M := Subgroup.subset_closure ⟨L, hL, huL⟩
  have hw2C : w * w ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.mul_mem _ hwC hwC
  have hL2 : conjSub ((w * w)) L = L := by
    have hmax := hS.maxAdj_conj_of_mem hL hz hw2C
    have hinv := huL.conj ((w * w))
    rw [h2 uL huLV] at hinv
    exact hS.eq_of_uniqueInvolution hmax.1.2.1 hL.1.2.1 hinv huL
  have h3 : ∀ l ∈ L, (w * w) * l * (w * w)⁻¹ = l ∨ (w * w) * l * (w * w)⁻¹ = l * uL := by
    intro l hl
    have hl' : (w * w) * l * (w * w)⁻¹ ∈ L := by
      have h4 : (w * w) * l * (w * w)⁻¹ ∈ conjSub ((w * w)) L := conj_mem_conjSub hl
      rwa [hL2] at h4
    have hm : l⁻¹ * ((w * w) * l * (w * w)⁻¹) ∈ L := L.mul_mem (L.inv_mem hl) hl'
    have hc : ∀ v ∈ vM Ω M, l⁻¹ * ((w * w) * l * (w * w)⁻¹) * v =
        v * (l⁻¹ * ((w * w) * l * (w * w)⁻¹)) := by
      intro v hv
      have hv2 : (w * w)⁻¹ * v * (w * w) = v := by
        calc (w * w)⁻¹ * v * (w * w) = (w * w)⁻¹ * ((w * w) * v * (w * w)⁻¹) * (w * w) := by
              rw [h2 v hv]
          _ = v := by group
      have hlv : l * v * l⁻¹ ∈ vM Ω M := by
        rcases hS.conj_vM hth hind hz hL huL hv hl with h | h
        · rw [h]
          exact hv
        · rw [h]
          exact (vM Ω M).mul_mem huLV hv
      have key : ((w * w) * l * (w * w)⁻¹) * v * ((w * w) * l * (w * w)⁻¹)⁻¹ = l * v * l⁻¹ := by
        calc ((w * w) * l * (w * w)⁻¹) * v * ((w * w) * l * (w * w)⁻¹)⁻¹
            = (w * w) * (l * ((w * w)⁻¹ * v * (w * w)) * l⁻¹) * (w * w)⁻¹ := by
              generalize w * w = y
              group
          _ = (w * w) * (l * v * l⁻¹) * (w * w)⁻¹ := by rw [hv2]
          _ = l * v * l⁻¹ := h2 _ hlv
      calc l⁻¹ * ((w * w) * l * (w * w)⁻¹) * v
          = l⁻¹ * (((w * w) * l * (w * w)⁻¹) * v * ((w * w) * l * (w * w)⁻¹)⁻¹) *
              ((w * w) * l * (w * w)⁻¹) := by group
        _ = l⁻¹ * (l * v * l⁻¹) * ((w * w) * l * (w * w)⁻¹) := by rw [key]
        _ = v * (l⁻¹ * ((w * w) * l * (w * w)⁻¹)) := by group
    rcases hS.mem_of_centralizes_vM hth hz hind hL huL hm hc with h | h
    · left
      calc (w * w) * l * (w * w)⁻¹ = l * (l⁻¹ * ((w * w) * l * (w * w)⁻¹)) := by group
        _ = l := by rw [h, mul_one]
    · right
      calc (w * w) * l * (w * w)⁻¹ = l * (l⁻¹ * ((w * w) * l * (w * w)⁻¹)) := by group
        _ = l * uL := by rw [h]
  have hfix : (w * w * (w * w)) * l * (w * w * (w * w))⁻¹ = l := by
    have e4 : (w * w * (w * w)) * l * (w * w * (w * w))⁻¹ =
        (w * w) * ((w * w) * l * (w * w)⁻¹) * (w * w)⁻¹ := by group
    rw [e4]
    rcases h3 l hl with h | h
    · rw [h, h]
    · rw [h]
      calc (w * w) * (l * uL) * (w * w)⁻¹
          = ((w * w) * l * (w * w)⁻¹) * ((w * w) * uL * (w * w)⁻¹) := by group
        _ = l * uL * uL := by rw [h, h2 uL huLV]
        _ = l := by rw [mul_assoc, huL.sq, mul_one]
  rw [pow_four_eq]
  exact comm_of_conj_eq hfix

theorem ThinStd.exists_comm_not_comm {L : Subgroup G} (hL : MaxAdj (nbrAdj Ω) M L) {u : G}
    (hu : IsUniqueInvolution L u) {v₁ v₂ : G} (hv₁ : v₁ ∈ vM Ω M) (hv₂ : v₂ ∈ vM Ω M)
    (h₂ : ¬ (v₂ = 1 ∨ v₂ = u)) (h₁₂ : ¬ (v₁ * v₂ = 1 ∨ v₁ * v₂ = u)) :
    ∃ l ∈ L, l * v₁ = v₁ * l ∧ l * v₂ ≠ v₂ * l := by
  by_contra hno
  push Not at hno
  have hcV := hS.vM_comm hth hind hz
  have huV : u ∈ vM Ω M := Subgroup.subset_closure ⟨L, hL, hu⟩
  have hne : ∃ l ∈ L, l * v₂ ≠ v₂ * l := by
    by_contra hall
    push Not at hall
    exact h₂ (hS.eq_of_centralizes hth hind hz hL hu hv₂ hall)
  have huL : ∀ l ∈ L, l * u = u * l := fun l hl =>
    comm_of_conj_eq (hu.conj_eq (conjSub_eq_self_of_mem hl))
  have hc := comm_mul_of_transv hu.sq huL (hcV u huV v₁ hv₁)
    (fun l hl => hS.conj_vM hth hind hz hL hu hv₁ hl)
    (fun l hl => hS.conj_vM hth hind hz hL hu hv₂ hl) hne hno
  exact h₁₂ (hS.eq_of_centralizes hth hind hz hL hu ((vM Ω M).mul_mem hv₁ hv₂) hc)

omit hth hind hz in
theorem ThinStd.comm_of_centX_inv {N : Subgroup G} (hN : MaxAdj (nbrAdj Ω) M N)
    (hindN : Indep Ω N) {L : Subgroup G} (hL : MaxAdj (nbrAdj Ω) N L) {c : G}
    (hc : IsUniqueInvolution L c) (hcX : CentX Ω M c) :
    ∀ L' : Subgroup G, MaxAdj (nbrAdj Ω) M L' → ∀ l ∈ L, ∀ l' ∈ L', l * l' = l' * l := by
  intro L' hL' l hl l' hl'
  have hLΩ := hL.1.2.1
  have hL'Ω := hL'.1.2.1
  have hL'N : L' ≤ Subgroup.normalizer (L : Set G) := fun x hx =>
    hS.tight L hLΩ c hc (Subgroup.mem_centralizer_singleton_iff.mpr (hcX L' hL' x hx).symm)
  have hNM : MaxAdj (nbrAdj Ω) N M :=
    ⟨hS.graphFam.graph.symm hN.1, orbOf_mem_maxOrbs hS.graphFam hN.1 hN.2⟩
  have hne : L' ≠ L := by
    intro heq
    rw [heq] at hL'
    have hML : M ≠ L := by
      intro h
      subst h
      exact hS.graphFam.graph.irrefl _ hL'.1
    exact hindN M L hNM hL hML hL'.1
  have hadj : nbrAdj Ω L L' := ⟨hLΩ, (mem_omegaNbr_iff hS.hyp hS.two).mpr ⟨hL'Ω, hne, hL'N⟩⟩
  exact hS.commutes_of_nbrAdj hadj l hl l' hl'

theorem ThinStd.centX_inv {N : Subgroup G} (hN : MaxAdj (nbrAdj Ω) M N) (hthN : ThinAtM Ω N)
    (hindN : Indep Ω N) {w : G} (hw : IsUniqueInvolution N w) {L : Subgroup G}
    (hL : MaxAdj (nbrAdj Ω) N L) {c : G} (hc : IsUniqueInvolution L c) (hcz : c ≠ z) :
    CentX Ω M c := by
  classical
  have hNM : MaxAdj (nbrAdj Ω) N M :=
    ⟨hS.graphFam.graph.symm hN.1, orbOf_mem_maxOrbs hS.graphFam hN.1 hN.2⟩
  have hcVN := hS.vM_comm hthN hindN hw
  have hzV : z ∈ vM Ω N := Subgroup.subset_closure ⟨M, hNM, hz⟩
  have hcV : c ∈ vM Ω N := Subgroup.subset_closure ⟨L, hL, hc⟩
  have h8 := hS.card_vM_eq hthN hw hindN hNM
  obtain ⟨b, hbV, hb⟩ : ∃ b ∈ vM Ω N, b ∉ ({1, c, z, c * z} : Set G) := by
    by_contra hno
    push Not at hno
    have hsub : (vM Ω N : Set G) ⊆ ({1, c, z, c * z} : Set G) := fun x hx => hno x hx
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have e1 := Set.ncard_insert_le (1 : G) ({c, z, c * z} : Set G)
    have e2 := Set.ncard_insert_le c ({z, c * z} : Set G)
    have e3 := Set.ncard_insert_le z ({c * z} : Set G)
    rw [Set.ncard_singleton] at e3
    have e : (vM Ω N : Set G).ncard = Nat.card ↥(vM Ω N) := (Nat.card_coe_set_eq _).symm
    rw [e, h8] at h1
    omega
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hb
  obtain ⟨hb1, hbc, hbz, hbcz⟩ := hb
  obtain ⟨Lb, hLb, hbu⟩ : b ∈ invs Ω N :=
    ((hS.mem_vM_iff hthN hindN hw).mp hbV).resolve_left hb1
  have hbcc : b * c = c * b := hcVN b hbV c hcV
  have hcn : ¬ (c = 1 ∨ c = b) := by
    rintro (h | h)
    · exact hc.ne_one h
    · exact hbc h.symm
  have hzc : ¬ (z * c = 1 ∨ z * c = b) := by
    rintro (h | h)
    · apply hcz
      calc c = z * (z * c) := by rw [← mul_assoc, hz.sq, one_mul]
        _ = z := by rw [h, mul_one]
    · apply hbcz
      rw [← h]
      exact hcVN z hzV c hcV
  obtain ⟨l₁, hl₁, hl₁z, hl₁c⟩ := hS.exists_comm_not_comm hthN hindN hw hLb hbu hzV hcV hcn hzc
  have hl₁c' : l₁ * c * l₁⁻¹ = b * c :=
    (hS.conj_vM hthN hindN hw hLb hbu hcV hl₁).resolve_left fun h => hl₁c (comm_of_conj_eq h)
  have hbn : ¬ (b = 1 ∨ b = c) := by
    rintro (h | h)
    · exact hb1 h
    · exact hbc h
  have hzb : ¬ (z * b = 1 ∨ z * b = c) := by
    rintro (h | h)
    · apply hbz
      calc b = z * (z * b) := by rw [← mul_assoc, hz.sq, one_mul]
        _ = z := by rw [h, mul_one]
    · apply hbcz
      calc b = z * (z * b) := by rw [← mul_assoc, hz.sq, one_mul]
        _ = z * c := by rw [h]
        _ = c * z := hcVN z hzV c hcV
  obtain ⟨l₂, hl₂, hl₂z, hl₂b⟩ := hS.exists_comm_not_comm hthN hindN hw hL hc hzV hbV hbn hzb
  have hl₂b' : l₂ * b * l₂⁻¹ = c * b :=
    (hS.conj_vM hthN hindN hw hL hc hbV hl₂).resolve_left fun h => hl₂b (comm_of_conj_eq h)
  have hl₂c : l₂ * c * l₂⁻¹ = c := hc.conj_eq (conjSub_eq_self_of_mem hl₂)
  have hl₁b : l₁ * b * l₁⁻¹ = b := hbu.conj_eq (conjSub_eq_self_of_mem hl₁)
  have hhz : (l₂ * l₁) * z = z * (l₂ * l₁) := by
    calc l₂ * l₁ * z = l₂ * (l₁ * z) := by group
      _ = l₂ * (z * l₁) := by rw [hl₁z]
      _ = (l₂ * z) * l₁ := by group
      _ = (z * l₂) * l₁ := by rw [hl₂z]
      _ = z * (l₂ * l₁) := by group
  have hhN : ∀ n ∈ N, (l₂ * l₁) * n = n * (l₂ * l₁) := by
    intro n hn
    have h1 := hS.commutes_of_nbrAdj (hS.graphFam.graph.symm hLb.1) l₁ hl₁ n hn
    have h2 := hS.commutes_of_nbrAdj (hS.graphFam.graph.symm hL.1) l₂ hl₂ n hn
    calc l₂ * l₁ * n = l₂ * (l₁ * n) := by group
      _ = l₂ * (n * l₁) := by rw [h1]
      _ = (l₂ * n) * l₁ := by group
      _ = (n * l₂) * l₁ := by rw [h2]
      _ = n * (l₂ * l₁) := by group
  have hX := hS.centX_pow_four hth hind hz hN hhz hhN
  have hc1 : (l₂ * l₁) * c * (l₂ * l₁)⁻¹ = b := by
    calc (l₂ * l₁) * c * (l₂ * l₁)⁻¹ = l₂ * (l₁ * c * l₁⁻¹) * l₂⁻¹ := by group
      _ = l₂ * (b * c) * l₂⁻¹ := by rw [hl₁c']
      _ = (l₂ * b * l₂⁻¹) * (l₂ * c * l₂⁻¹) := by group
      _ = (c * b) * c := by rw [hl₂b', hl₂c]
      _ = b := by rw [← hbcc, mul_assoc, hc.sq, mul_one]
  have hb1' : (l₂ * l₁) * b * (l₂ * l₁)⁻¹ = c * b := by
    calc (l₂ * l₁) * b * (l₂ * l₁)⁻¹ = l₂ * (l₁ * b * l₁⁻¹) * l₂⁻¹ := by group
      _ = l₂ * b * l₂⁻¹ := by rw [hl₁b]
      _ = c * b := hl₂b'
  have hcb1 : (l₂ * l₁) * (c * b) * (l₂ * l₁)⁻¹ = c := by
    calc (l₂ * l₁) * (c * b) * (l₂ * l₁)⁻¹
        = ((l₂ * l₁) * c * (l₂ * l₁)⁻¹) * ((l₂ * l₁) * b * (l₂ * l₁)⁻¹) := by group
      _ = b * (c * b) := by rw [hc1, hb1']
      _ = c := by rw [← hbcc, ← mul_assoc, hbu.sq, one_mul]
  have e4 : ∀ x y : G, x ^ 4 * y * (x ^ 4)⁻¹ = x * (x * (x * (x * y * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹ := by
    intro x y
    rw [pow_four_eq]
    group
  have hy : (l₂ * l₁) ^ 4 * b * ((l₂ * l₁) ^ 4)⁻¹ = c * b := by
    rw [e4, hb1', hcb1, hc1, hb1']
  have e5 : ∀ y : G, b * y * b⁻¹ * y⁻¹ = b * (y * b * y⁻¹)⁻¹ := fun y => by group
  have hcomm : c = b * (l₂ * l₁) ^ 4 * b⁻¹ * ((l₂ * l₁) ^ 4)⁻¹ := by
    rw [e5, hy]
    have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc.sq
    calc c = c⁻¹ := hcinv.symm
      _ = b * (c * b)⁻¹ := by group
  have hbC : b ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcVN b hbV z hzV)
  have hX' := hS.centX_conj hz hbC hX
  intro L' hL' l hl
  rw [hcomm]
  exact Commute.mul_left (hX' L' hL' l hl) (Commute.inv_left (hX L' hL' l hl))

theorem ThinStd.comm_of_maxAdj {N : Subgroup G} (hN : MaxAdj (nbrAdj Ω) M N)
    (hthN : ThinAtM Ω N) (hindN : Indep Ω N) {L : Subgroup G} (hL : MaxAdj (nbrAdj Ω) N L) :
    ∀ L' : Subgroup G, MaxAdj (nbrAdj Ω) M L' → ∀ l ∈ L, ∀ l' ∈ L', l * l' = l' * l := by
  obtain ⟨w, hw⟩ := Sec6Gen.exists_uniqueInvolution hS.hyp hN.1.2.1
  obtain ⟨c, hc⟩ := Sec6Gen.exists_uniqueInvolution hS.hyp hL.1.2.1
  by_cases hcz : c = z
  · have hcM : IsUniqueInvolution M c := by
      rw [hcz]
      exact hz
    have hLM : L = M := hS.eq_of_uniqueInvolution hL.1.2.1 hN.1.1 hc hcM
    intro L' hL' l hl l' hl'
    rw [hLM] at hl
    exact hS.commutes_of_nbrAdj hL'.1 l hl l' hl'
  · exact hS.comm_of_centX_inv hN hindN hL hc
      (hS.centX_inv hth hind hz hN hthN hindN hw hL hc hcz)

omit hth hind hz in
theorem ThinStd.false_of_indep
    (hthin : ∀ M N : Subgroup G, MaxAdj (nbrAdj Ω) M N → ThinAt Ω M N)
    (hind : ∀ M : Subgroup G, M ∈ Ω → Indep Ω M) {M N : Subgroup G}
    (hMN : MaxAdj (nbrAdj Ω) M N) : False := by
  have hF := hS.graphFam
  have hMΩ := hMN.1.1
  have hNΩ := hMN.1.2.1
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hS.hyp hMΩ
  have hthM : ThinAtM Ω M := fun N' h => hthin M N' h
  have hthN : ThinAtM Ω N := fun N' h => hthin N N' h
  have hNM : MaxAdj (nbrAdj Ω) N M := ⟨hF.graph.symm hMN.1, orbOf_mem_maxOrbs hF hMN.1 hMN.2⟩
  set X : Subgroup G := ⨆ L ∈ {L : Subgroup G | MaxAdj (nbrAdj Ω) M L}, L with hX
  have hLX : ∀ L : Subgroup G, MaxAdj (nbrAdj Ω) M L → L ≤ X := fun L hL =>
    le_biSup (fun L : Subgroup G => L) (show L ∈ {L : Subgroup G | MaxAdj (nbrAdj Ω) M L} from hL)
  have hcent : ∀ L : Subgroup G, MaxAdj (nbrAdj Ω) N L → L ≤ Subgroup.centralizer (X : Set G) := by
    intro L hL
    rw [Subgroup.le_centralizer_iff]
    refine iSup₂_le fun L' hL' => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact hS.comm_of_maxAdj hthM (hind M hMΩ) hz hMN hthN (hind N hNΩ) hL L' hL' l hl x hx
  have hnorm : ∀ g : G, g ∈ Subgroup.normalizer (X : Set G) := by
    intro g
    have htop : (⨆ J ∈ Ω, J) ≤ Subgroup.normalizer (X : Set G) := by
      refine iSup₂_le fun J hJ => ?_
      refine (le_iSup_of_maxOrb hF hMN.1 hMN.2 J hJ).trans ?_
      refine iSup₂_le fun L hL => ?_
      rcases hL with hL | hL
      · have hL' : MaxAdj (nbrAdj Ω) M L :=
          ⟨adj_of_mem_orbOf hF.graph hMN.1 hL, by rw [orbOf_eq_of_mem hL]; exact hMN.2⟩
        exact (hLX L hL').trans Subgroup.le_normalizer
      · have hL' : MaxAdj (nbrAdj Ω) N L :=
          ⟨adj_of_mem_orbOf hF.graph hNM.1 hL, by rw [orbOf_eq_of_mem hL]; exact hNM.2⟩
        exact (hcent L hL').trans (Subgroup.centralizer_le_normalizer _)
    rw [hS.gen] at htop
    exact htop (Subgroup.mem_top g)
  obtain ⟨a, ha⟩ := hS.trans M hMΩ
  obtain ⟨b, hb⟩ := hS.trans N hNΩ
  have hMX : M ≤ X := by
    have h1 : conjSub (a * b⁻¹) N = M := by
      rw [← hb, ← conjSub_mul, inv_mul_cancel_right, ha]
    rw [← h1, ← conjSub_eq_of_mem_normalizer (hnorm (a * b⁻¹))]
    exact conjSub_mono (hLX N hMN)
  have hMc := hcent M hNM
  obtain ⟨x, hx, y, hy, hxy⟩ := hS.exists_not_comm hMΩ
  exact hxy (Subgroup.mem_centralizer_iff.mp (hMc hy) x (hMX hx))

end CFSG.ClassicalInvolution.Q3.TC.Thin
