module

public import CFSG.ClassicalInvolution.RouteD.LocalPair

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.S28

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD

variable {G : Type} [Group G]

@[expose] def IsoMem (Ω : Set (Subgroup G)) (x : G) (L : Subgroup G) : Prop :=
  L ∈ centralizingMembers Ω {x} ∧
    ∀ L' ∈ centralizingMembers Ω {x}, L' ≠ L → Commutes L L'

theorem mem_centralizingMembers_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g x : G)
    {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x}) :
    conjSub g L ∈ centralizingMembers Ω {g * x * g⁻¹} := by
  rw [centralizingMembers_conj hΩ]
  exact ⟨L, hL, rfl⟩

theorem IsoMem.conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {x : G} {L : Subgroup G}
    (h : IsoMem Ω x L) (g : G) : IsoMem Ω (g * x * g⁻¹) (conjSub g L) := by
  refine ⟨mem_centralizingMembers_conj hΩ g x h.1, fun L' hL' hne => ?_⟩
  rw [centralizingMembers_conj hΩ] at hL'
  obtain ⟨L₀, hL₀, rfl⟩ := hL'
  have : L₀ ≠ L := fun e => hne (by rw [e])
  exact (h.2 L₀ hL₀ this).conjSub g

structure FalseTwinPure (Ω : Set (Subgroup G)) (K T : Subgroup G) (z w : G) : Prop where
  conj : ConjInvariant Ω
  trans : ∀ M ∈ Ω, ∃ g : G, conjSub g K = M
  hK : K ∈ Ω
  hT : T ∈ Ω
  hz : IsUniqueInvolution K z
  hw : IsUniqueInvolution T w
  hwz : w ≠ z
  hKT : K ≠ T
  hKc : K ≤ Subgroup.centralizer ({z} : Set G)
  hTc : T ≤ Subgroup.centralizer ({w} : Set G)
  hTz : T ≤ Subgroup.centralizer ({z} : Set G)
  commK : ∀ N ∈ centralizingMembers Ω {z}, N ≠ K → Commutes K N
  commT : ∀ N ∈ centralizingMembers Ω {z}, N ≠ T → Commutes T N
  noniso : ∀ L ∈ centralizingMembers Ω {z}, L ≠ K → L ≠ T →
    ∃ L' ∈ centralizingMembers Ω {z}, L' ≠ L ∧ ¬ Commutes L L'

namespace FalseTwinPure

variable {Ω : Set (Subgroup G)} {K T : Subgroup G} {z w : G} (h : FalseTwinPure Ω K T z w)

include h

theorem K_mem : K ∈ centralizingMembers Ω {z} := ⟨h.hK, h.hKc⟩

theorem T_mem : T ∈ centralizingMembers Ω {z} := ⟨h.hT, h.hTz⟩

theorem isoK : IsoMem Ω z K := ⟨h.K_mem, fun L' hL' hne => h.commK L' hL' hne⟩

theorem isoT : IsoMem Ω z T := ⟨h.T_mem, fun L' hL' hne => h.commT L' hL' hne⟩

theorem commutes_KT : Commutes K T := h.commK T h.T_mem (Ne.symm h.hKT)

theorem iso_cases {L : Subgroup G} (hL : IsoMem Ω z L) : L = K ∨ L = T := by
  by_contra hcon
  push Not at hcon
  obtain ⟨L', hL', hne, hnc⟩ := h.noniso L hL.1 hcon.1 hcon.2
  exact hnc (hL.2 L' hL' hne)

theorem iso_conj_of_centralizes {L : Subgroup G} (hL : IsoMem Ω z L) {g : G}
    (hg : g * z * g⁻¹ = z) : IsoMem Ω z (conjSub g L) := by
  have := hL.conj h.conj g
  rwa [hg] at this

theorem conj_K_eq {g : G} (hg : g * z * g⁻¹ = z) : conjSub g K = K := by
  rcases h.iso_cases (h.iso_conj_of_centralizes h.isoK hg) with e | e
  · exact e
  · exfalso
    have h1 : IsUniqueInvolution (conjSub g K) (g * z * g⁻¹) := h.hz.conj g
    rw [e, hg] at h1
    exact h.hwz (h.hw.eq h1)

theorem conj_T_eq {g : G} (hg : g * z * g⁻¹ = z) : conjSub g T = T := by
  rcases h.iso_cases (h.iso_conj_of_centralizes h.isoT hg) with e | e
  · exfalso
    have hg' : g⁻¹ * z * g⁻¹⁻¹ = z := by
      calc g⁻¹ * z * g⁻¹⁻¹ = g⁻¹ * (g * z * g⁻¹) * g := by rw [hg]; group
        _ = z := by group
    have h2 := h.conj_K_eq hg'
    have : T = conjSub g⁻¹ K := by
      rw [← e, conjSub_inv_conjSub]
    rw [h2] at this
    exact h.hKT this.symm
  · exact e

theorem conj_w_eq_of_conj_z_eq {g : G} (hg : g * z * g⁻¹ = z) : g * w * g⁻¹ = w := by
  have h1 : IsUniqueInvolution (conjSub g T) (g * w * g⁻¹) := h.hw.conj g
  rw [h.conj_T_eq hg] at h1
  exact (h.hw.eq h1).symm

theorem exists_conj_T : ∃ s : G, conjSub s K = T ∧ s * z * s⁻¹ = w := by
  obtain ⟨s, hs⟩ := h.trans T h.hT
  refine ⟨s, hs, ?_⟩
  have h1 : IsUniqueInvolution (conjSub s K) (s * z * s⁻¹) := h.hz.conj s
  rw [hs] at h1
  exact (h.hw.eq h1).symm

theorem conj_T_stab {x : G} (hx : conjSub x T = T) (hcw : Subgroup.centralizer ({w} : Set G) =
    Subgroup.centralizer ({z} : Set G)) : x * z * x⁻¹ = z := by
  have h1 : IsUniqueInvolution (conjSub x T) (x * w * x⁻¹) := h.hw.conj x
  rw [hx] at h1
  have hxw : x * w * x⁻¹ = w := (h.hw.eq h1).symm
  have hmem : x ∈ Subgroup.centralizer ({w} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * w = (x * w * x⁻¹) * x := by group
      _ = w * x := by rw [hxw]
  rw [hcw, Subgroup.mem_centralizer_singleton_iff] at hmem
  calc x * z * x⁻¹ = (z * x) * x⁻¹ := by rw [hmem]
    _ = z := by group

theorem conj_K_stab {x : G} (hx : conjSub x K = K) : x * z * x⁻¹ = z := by
  have h1 : IsUniqueInvolution (conjSub x K) (x * z * x⁻¹) := h.hz.conj x
  rw [hx] at h1
  exact (h.hz.eq h1).symm

variable [Finite G]

theorem centralizer_w_eq :
    Subgroup.centralizer ({w} : Set G) = Subgroup.centralizer ({z} : Set G) := by
  obtain ⟨s, hs, hsz⟩ := h.exists_conj_T
  have hle : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer ({w} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    have hgz : g * z * g⁻¹ = z := by rw [hg]; group
    have := h.conj_w_eq_of_conj_z_eq hgz
    calc g * w = (g * w * g⁻¹) * g := by group
      _ = w * g := by rw [this]
  have hcw : Subgroup.centralizer ({w} : Set G) =
      conjSub s (Subgroup.centralizer ({z} : Set G)) := by
    ext x
    rw [mem_conjSub_iff, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, ← hsz]
    constructor
    · intro hx
      calc s⁻¹ * x * s * z = s⁻¹ * (x * (s * z * s⁻¹)) * s := by group
        _ = s⁻¹ * ((s * z * s⁻¹) * x) * s := by rw [hx]
        _ = z * (s⁻¹ * x * s) := by group
    · intro hx
      calc x * (s * z * s⁻¹) = s * ((s⁻¹ * x * s) * z) * s⁻¹ := by group
        _ = s * (z * (s⁻¹ * x * s)) * s⁻¹ := by rw [hx]
        _ = (s * z * s⁻¹) * x := by group
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hcw]
  exact (Subgroup.card_map_of_injective (f := (MulAut.conj s).toMonoidHom)
    (MulAut.conj s).injective).le

theorem centralizingMembers_w_eq :
    centralizingMembers Ω {w} = centralizingMembers Ω {z} := by
  simp only [centralizingMembers, h.centralizer_w_eq]

theorem isoMem_w_iff {L : Subgroup G} : IsoMem Ω w L ↔ IsoMem Ω z L := by
  simp only [IsoMem, h.centralizingMembers_w_eq]

theorem exists_swap :
    ∃ s : G, conjSub s K = T ∧ conjSub s T = K ∧ s * z * s⁻¹ = w ∧ s * w * s⁻¹ = z := by
  obtain ⟨s, hs, hsz⟩ := h.exists_conj_T
  have h1 : IsoMem Ω w (conjSub s T) := by
    have := h.isoT.conj h.conj s
    rwa [hsz] at this
  rcases h.iso_cases (h.isoMem_w_iff.mp h1) with e | e
  · refine ⟨s, hs, e, hsz, ?_⟩
    have h2 : IsUniqueInvolution (conjSub s T) (s * w * s⁻¹) := h.hw.conj s
    rw [e] at h2
    exact (h.hz.eq h2).symm
  · exfalso
    exact h.hKT (conjSub_injective s (hs.trans e.symm))

omit [Finite G] in
theorem conj_zw_eq {g g' : G} (hgg : conjSub g K = conjSub g' K) :
    g * (z * w) * g⁻¹ = g' * (z * w) * g'⁻¹ := by
  have hx : conjSub (g⁻¹ * g') K = K := by
    rw [conjSub_mul, ← hgg, conjSub_inv_conjSub]
  have hxz : (g⁻¹ * g') * z * (g⁻¹ * g')⁻¹ = z := h.conj_K_stab hx
  have hxw := h.conj_w_eq_of_conj_z_eq hxz
  calc g * (z * w) * g⁻¹ = g * (((g⁻¹ * g') * z * (g⁻¹ * g')⁻¹) *
        ((g⁻¹ * g') * w * (g⁻¹ * g')⁻¹)) * g⁻¹ := by rw [hxz, hxw]
    _ = g' * (z * w) * g'⁻¹ := by group

theorem comm_zw : z * w = w * z := h.commutes_KT z h.hz.mem w h.hw.mem

theorem swap_fixes_zw : ∃ s : G, conjSub s K = T ∧ s * (z * w) * s⁻¹ = z * w := by
  obtain ⟨s, hsK, -, hsz, hsw⟩ := h.exists_swap
  refine ⟨s, hsK, ?_⟩
  calc s * (z * w) * s⁻¹ = (s * z * s⁻¹) * (s * w * s⁻¹) := by group
    _ = w * z := by rw [hsz, hsw]
    _ = z * w := h.comm_zw.symm

section Member

variable {g₀ : G}

theorem centralizingMembers_conj_w_eq :
    centralizingMembers Ω {g₀ * w * g₀⁻¹} = centralizingMembers Ω {g₀ * z * g₀⁻¹} := by
  rw [centralizingMembers_conj h.conj, centralizingMembers_conj h.conj,
    h.centralizingMembers_w_eq]

theorem K_mem_conj (hM : conjSub g₀ K ∈ centralizingMembers Ω {z}) (hMK : conjSub g₀ K ≠ K) :
    K ∈ centralizingMembers Ω {g₀ * z * g₀⁻¹} := by
  refine ⟨h.hK, fun k hk => ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hzM : g₀ * z * g₀⁻¹ ∈ conjSub g₀ K := conj_mem_conjSub h.hz.mem
  exact h.commK _ hM hMK k hk _ hzM

theorem M₂_ne_K (hMT : conjSub g₀ K ≠ T) : conjSub g₀ T ≠ K := by
  intro hc
  obtain ⟨s, hsK, hsT, hsz, hsw⟩ := h.exists_swap
  have hx : conjSub (s⁻¹ * g₀) T = T := by
    rw [conjSub_mul, hc, ← hsT, conjSub_inv_conjSub]
  have hxz := h.conj_T_stab hx h.centralizer_w_eq
  have hxK := h.conj_K_eq hxz
  rw [conjSub_mul] at hxK
  apply hMT
  calc conjSub g₀ K = conjSub s (conjSub s⁻¹ (conjSub g₀ K)) :=
        (conjSub_conjSub_inv s (conjSub g₀ K)).symm
    _ = conjSub s K := by rw [hxK]
    _ = T := hsK

theorem M₂_ne_T (hMK : conjSub g₀ K ≠ K) : conjSub g₀ T ≠ T := by
  intro hc
  have hxz := h.conj_T_stab hc h.centralizer_w_eq
  exact hMK (h.conj_K_eq hxz)

theorem M₂_ne_M : conjSub g₀ T ≠ conjSub g₀ K := fun e => h.hKT (conjSub_injective g₀ e).symm

theorem commutes_M_M₂ : Commutes (conjSub g₀ K) (conjSub g₀ T) := h.commutes_KT.conjSub g₀

theorem M₂_commutes_K (hM : conjSub g₀ K ∈ centralizingMembers Ω {z})
    (hMK : conjSub g₀ K ≠ K) (hMT : conjSub g₀ K ≠ T) :
    Commutes (conjSub g₀ T) K := by
  have hiso : IsoMem Ω (g₀ * z * g₀⁻¹) (conjSub g₀ T) := h.isoT.conj h.conj g₀
  exact hiso.2 K (h.K_mem_conj hM hMK) (Ne.symm (h.M₂_ne_K hMT))

theorem M₂_mem (hM : conjSub g₀ K ∈ centralizingMembers Ω {z})
    (hMK : conjSub g₀ K ≠ K) (hMT : conjSub g₀ K ≠ T) :
    conjSub g₀ T ∈ centralizingMembers Ω {z} := by
  refine ⟨h.conj g₀ T h.hT, fun y hy => ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact h.M₂_commutes_K hM hMK hMT y hy z h.hz.mem

theorem graphTwin {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {z}) (hLM : L ≠ conjSub g₀ K) (hLM₂ : L ≠ conjSub g₀ T) :
    Commutes L (conjSub g₀ K) ↔ Commutes L (conjSub g₀ T) := by
  have hisoM : IsoMem Ω (g₀ * z * g₀⁻¹) (conjSub g₀ K) := h.isoK.conj h.conj g₀
  have hisoM₂ : IsoMem Ω (g₀ * z * g₀⁻¹) (conjSub g₀ T) := h.isoT.conj h.conj g₀
  constructor
  · intro hc
    have hLz : L ∈ centralizingMembers Ω {g₀ * z * g₀⁻¹} := by
      refine ⟨hL.1, fun y hy => ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hc y hy _ (conj_mem_conjSub h.hz.mem)
    exact (hisoM₂.2 L hLz hLM₂).symm
  · intro hc
    have hLw : L ∈ centralizingMembers Ω {g₀ * w * g₀⁻¹} := by
      refine ⟨hL.1, fun y hy => ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hc y hy _ (conj_mem_conjSub h.hw.mem)
    rw [h.centralizingMembers_conj_w_eq] at hLw
    exact (hisoM.2 L hLw hLM).symm

end Member

end FalseTwinPure

end CFSG.ClassicalInvolution.Asc77.S28
