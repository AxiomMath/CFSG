module

public import CFSG.ClassicalInvolution.Q3.Sec13EndAE8D
public import CFSG.ClassicalInvolution.Q3.Sec13EndAE8K

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace AE8End

open scoped commutatorElement

variable {Ω : Set (Subgroup G)} {u : G}

@[expose] def Chart.permSub : Subgroup (AE.Wr 6) where
  carrier := {a | a.vec = 0 ∧ a.perm ∈ alternatingGroup (Fin 6)}
  mul_mem' := fun {a b} ha hb => by
    refine ⟨?_, ?_⟩
    · funext i
      rw [AE.Wr.mul_vec, ha.1, hb.1]
      simp
    · rw [AE.Wr.mul_perm]
      exact mul_mem ha.2 hb.2
  one_mem' := ⟨rfl, one_mem _⟩
  inv_mem' := fun {a} ha => by
    refine ⟨?_, ?_⟩
    · funext i
      rw [AE.Wr.inv_vec, ha.1]
      rfl
    · rw [AE.Wr.inv_perm]
      exact inv_mem ha.2

@[expose] def Chart.H0 (c : Chart Ω u) : Subgroup G :=
  (Chart.permSub.comap ((AE.aeSub 6).subtype.comp c.ψ.toMonoidHom)).map
    (pSpan (Generic.centMembers Ω u)).subtype

theorem Chart.mem_H0 (c : Chart Ω u) (g : G) :
    g ∈ c.H0 ↔ ∃ hg : g ∈ pSpan (Generic.centMembers Ω u),
      (c.ψ ⟨g, hg⟩ : AE.Wr 6).vec = 0 ∧
        (c.ψ ⟨g, hg⟩ : AE.Wr 6).perm ∈ alternatingGroup (Fin 6) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hg, hv⟩
    exact ⟨⟨g, hg⟩, hv, rfl⟩

@[expose] noncomputable def Chart.permHomY (c : Chart Ω u) :
    ↥(pSpan (Generic.centMembers Ω u)) →* Equiv.Perm (Fin 6) :=
  (AE.permHom 6).comp ((AE.aeSub 6).subtype.comp c.ψ.toMonoidHom)

theorem Chart.permHomY_apply (c : Chart Ω u) (y : ↥(pSpan (Generic.centMembers Ω u))) :
    c.permHomY y = (c.ψ y : AE.Wr 6).perm := rfl

@[expose] def Chart.H0Y (c : Chart Ω u) : Subgroup ↥(pSpan (Generic.centMembers Ω u)) :=
  Chart.permSub.comap ((AE.aeSub 6).subtype.comp c.ψ.toMonoidHom)

theorem Chart.H0Y_ker (c : Chart Ω u) (x : ↥(pSpan (Generic.centMembers Ω u)))
    (hx : x ∈ c.H0Y) (h1 : c.permHomY x = 1) : x = 1 := by
  have hv : (c.ψ x : AE.Wr 6).vec = 0 := hx.1
  have hp : (c.ψ x : AE.Wr 6).perm = 1 := by
    rw [← Chart.permHomY_apply]
    exact h1
  have hψ : (c.ψ x : AE.Wr 6) = 1 := AE.Wr.ext hv hp
  apply c.ψ.injective
  apply Subtype.ext
  rw [hψ, map_one]
  rfl

theorem Chart.H0Y_surj (c : Chart Ω u) (τ : Equiv.Perm (Fin 6))
    (hτ : τ ∈ alternatingGroup (Fin 6)) : ∃ x ∈ c.H0Y, c.permHomY x = τ := by
  have hmem : (AE.Wr.ofPerm τ : AE.Wr 6) ∈ AE.aeSub 6 := by
    rw [AE.mem_aeSub]
    exact ⟨by simp [AE.Wr.wsum, AE.Wr.ofPerm], Equiv.Perm.mem_alternatingGroup.mp hτ⟩
  refine ⟨c.ψ.symm ⟨AE.Wr.ofPerm τ, hmem⟩, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · show ((c.ψ (c.ψ.symm ⟨AE.Wr.ofPerm τ, hmem⟩) : ↥(AE.aeSub 6)) : AE.Wr 6).vec = 0
      rw [MulEquiv.apply_symm_apply]
      rfl
    · show ((c.ψ (c.ψ.symm ⟨AE.Wr.ofPerm τ, hmem⟩) : ↥(AE.aeSub 6)) : AE.Wr 6).perm ∈
        alternatingGroup (Fin 6)
      rw [MulEquiv.apply_symm_apply]
      exact hτ
  · rw [Chart.permHomY_apply, MulEquiv.apply_symm_apply]
    rfl

theorem ae8j_cyc_mem {i j k : Fin 6} (hij : i ≠ j) (hjk : j ≠ k) :
    Equiv.swap i j * Equiv.swap j k ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hij,
    Equiv.Perm.sign_swap hjk]
  norm_num

theorem ae8j_cycle3_ne_two_pow (k : ℕ) :
    (Equiv.swap (0 : Fin 6) 1 * Equiv.swap (1 : Fin 6) 2) ^ 2 ^ k ≠ 1 := by
  intro h
  have hc3 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap (1 : Fin 6) 2) ^ 3 = 1 := by decide
  have hc1 : Equiv.swap (0 : Fin 6) 1 * Equiv.swap (1 : Fin 6) 2 ≠ 1 := by decide
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord := orderOf_eq_prime hc3 hc1
  have hdvd := orderOf_dvd_of_pow_eq_one h
  rw [hord] at hdvd
  have h3 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  norm_num at h3

theorem ae8j_comm_central {X : Type} [Group X] {k k' : X} (hk : k ∈ Subgroup.center X)
    (hk' : k' ∈ Subgroup.center X) (p q : X) : ⁅k * p, k' * q⁆ = ⁅p, q⁆ := by
  have hk1 : ∀ w : X, k * w * k⁻¹ = w := fun w => by
    rw [← Subgroup.mem_center_iff.mp hk w]
    group
  have hk2 : ∀ w : X, k' * w * k'⁻¹ = w := fun w => by
    rw [← Subgroup.mem_center_iff.mp hk' w]
    group
  have hpk : p * k' = k' * p := Subgroup.mem_center_iff.mp hk' p
  have e1 : (k * p) * (k' * q) * (k * p)⁻¹ = k' * (p * q * p⁻¹) := by
    calc (k * p) * (k' * q) * (k * p)⁻¹ = k * (p * (k' * q) * p⁻¹) * k⁻¹ := by group
      _ = p * (k' * q) * p⁻¹ := hk1 _
      _ = (p * k') * q * p⁻¹ := by group
      _ = (k' * p) * q * p⁻¹ := by rw [hpk]
      _ = k' * (p * q * p⁻¹) := by group
  calc ⁅k * p, k' * q⁆ = (k * p) * (k' * q) * (k * p)⁻¹ * (k' * q)⁻¹ := by
        rw [commutatorElement_def]
    _ = k' * (p * q * p⁻¹) * (k' * q)⁻¹ := by rw [e1]
    _ = k' * (p * q * p⁻¹ * q⁻¹) * k'⁻¹ := by group
    _ = p * q * p⁻¹ * q⁻¹ := hk2 _
    _ = ⁅p, q⁆ := by rw [commutatorElement_def]

theorem Chart.perm_one_of_normal_isPGroup (N : Subgroup ↥(AE.aeSub 6)) [N.Normal]
    (h2 : IsPGroup 2 N) : ∀ n ∈ N, (n : AE.Wr 6).perm = 1 := by
  have hsign : ∀ g : ↥(AE.aeSub 6), Equiv.Perm.sign (g : AE.Wr 6).perm = 1 :=
    fun g => (AE.mem_aeSub.mp g.2).2
  let f : ↥(AE.aeSub 6) →* Equiv.Perm (Fin 6) :=
    { toFun := fun g => (g : AE.Wr 6).perm, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let ρ : ↥(AE.aeSub 6) →* alternatingGroup (Fin 6) :=
    f.codRestrict (alternatingGroup (Fin 6))
      (fun g => Equiv.Perm.mem_alternatingGroup.mpr (hsign g))
  have hρ : Function.Surjective ρ := by
    intro τ
    exact ⟨⟨AE.Wr.ofPerm (τ : Equiv.Perm (Fin 6)),
      ae8b1_ofPerm_mem (Equiv.Perm.mem_alternatingGroup.mp τ.2)⟩, Subtype.ext rfl⟩
  haveI : (N.map ρ).Normal := Subgroup.Normal.map ‹N.Normal› ρ hρ
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (α := Fin 6) (by simp)
      (N := N.map ρ) with h | h
  · intro n hn
    have hmem : ρ n ∈ N.map ρ := Subgroup.mem_map_of_mem _ hn
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    have hσ : Equiv.swap (0 : Fin 6) 1 * Equiv.swap (1 : Fin 6) 2 ∈ alternatingGroup (Fin 6) :=
      ae8j_cyc_mem (by decide) (by decide)
    have hc : (⟨_, hσ⟩ : alternatingGroup (Fin 6)) ∈ N.map ρ := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := (h2.map ρ) ⟨_, hc⟩
    have h4 := congrArg (fun x : ↥(N.map ρ) => ((x : alternatingGroup (Fin 6)) :
      Equiv.Perm (Fin 6))) hk
    simp only [Subgroup.coe_pow, Subgroup.coe_mk, Subgroup.coe_one] at h4
    exact ae8j_cycle3_ne_two_pow k h4

theorem Chart.H0_inf_zGroup (H : End18.Hyp Ω) (c : Chart Ω u) : c.H0 ⊓ zGroup Ω = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hg0, hgD⟩
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg0
  have h1 : c.permHomY y = 1 := by
    rw [c.permHomY_apply]
    exact (c.mem_zGroup_iff H y).mp hgD
  simp [c.H0Y_ker y hy h1]

theorem ae8j_pi_eq_extPerm {c : Chart Ω u} (pt : Points u) (ι : Fin 6 ↪ Fin 8)
    (hι : ∀ y : ↥(pSpan (Generic.centMembers Ω u)),
      (∀ i : Fin 6, pt.π (y : G) (ι i) = ι ((c.ψ y : AE.Wr 6).perm i)) ∧
        ∀ j : Fin 8, j ∉ Set.range ι → pt.π (y : G) j = j)
    (y : ↥(pSpan (Generic.centMembers Ω u))) :
    pt.π (y : G) = Amalg.extPerm ι ((c.ψ y : AE.Wr 6).perm) := by
  ext x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    rw [Amalg.extPerm_apply_mem, (hι y).1 i]
  · rw [Amalg.extPerm_apply_not_mem ι _ hx, (hι y).2 x hx]

theorem Points.map_H0_eq_altOn (H : End18.Hyp Ω) {c : Chart Ω u} {co : Coords c}
    (cl : Classes co) (pt : Points u) :
    ∃ ι : Fin 6 ↪ Fin 8, c.H0.map pt.π = altOn (Finset.univ.image ι) := by
  obtain ⟨ι, hι⟩ := Points.exists_chartLines H cl pt
  refine ⟨ι, ?_⟩
  ext τ
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    show pt.π (y : G) ∈ altOn (Finset.univ.image ι)
    rw [ae8j_pi_eq_extPerm pt ι hι y]
    exact extPerm_mem_altOn ι ⟨(c.ψ y : AE.Wr 6).perm, hy.2⟩
  · intro hτ
    obtain ⟨σ, rfl⟩ := exists_extPerm_of_mem_altOn ι hτ
    obtain ⟨x, hx, hxσ⟩ := c.H0Y_surj (σ : Equiv.Perm (Fin 6)) σ.2
    have hxσ' : (c.ψ x : AE.Wr 6).perm = σ := by
      rw [← c.permHomY_apply]
      exact hxσ
    refine ⟨x.1, Subgroup.mem_map_of_mem _ hx, ?_⟩
    rw [ae8j_pi_eq_extPerm pt ι hι x, hxσ']

theorem Points.ker_eq_centralizer (H : End18.Hyp Ω) {c : Chart Ω u} {co : Coords c}
    (cl : Classes co) (pt : Points u) :
    pt.π.ker = Subgroup.centralizer (zGroup Ω : Set G) := by
  ext g
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    have hΔ : ∀ x ∈ Delta u, g * x = x * g := by
      intro x hx
      have h1 := pt.equivariant g ⟨x, hx⟩ ⟨g * x * g⁻¹, (ae8d_delta_conj u g x).mp hx⟩ rfl
      rw [hg, Equiv.Perm.coe_one, Finset.image_id] at h1
      have h2 : (⟨g * x * g⁻¹, (ae8d_delta_conj u g x).mp hx⟩ : ↥(Delta u)) = ⟨x, hx⟩ :=
        pt.E.injective (Subtype.ext h1)
      have h3 : g * x * g⁻¹ = x := congrArg Subtype.val h2
      calc g * x = (g * x * g⁻¹) * g := by group
        _ = x * g := by rw [h3]
    have hC : Subgroup.closure (Delta u) ≤ Subgroup.centralizer ({g} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hΔ x hx).symm
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (hC (ae8d_zGroup_le_closure cl hh))
  · intro hg
    have h1 : ∀ s : {s : Finset (Fin 8) // s.card = 2},
        ((Equiv.refl _) s : Finset (Fin 8)) = (s : Finset (Fin 8)).image (pt.π g) := by
      intro s
      have hcomm : g * ((pt.E.symm s : ↥(Delta u)) : G) =
          ((pt.E.symm s : ↥(Delta u)) : G) * g :=
        (Subgroup.mem_centralizer_iff.mp hg _ (ae8d_delta_mem_zGroup cl (pt.E.symm s).2)).symm
      have hx : ((pt.E.symm s : ↥(Delta u)) : G) =
          g * ((pt.E.symm s : ↥(Delta u)) : G) * g⁻¹ := by
        rw [hcomm]
        group
      have h2 := pt.equivariant g (pt.E.symm s) (pt.E.symm s) hx
      rw [pt.E.apply_symm_apply] at h2
      exact h2
    have h2 : ∀ s : {s : Finset (Fin 8) // s.card = 2},
        ((Equiv.refl _) s : Finset (Fin 8)) =
          (s : Finset (Fin 8)).image (1 : Equiv.Perm (Fin 8)) := by
      intro s
      rw [Equiv.Perm.coe_one, Finset.image_id]
      rfl
    exact ExistsUnique.unique (T8_exists_perm (Equiv.refl _) (fun _ _ => Iff.rfl)) h1 h2

theorem commutator_eq_top (H : End18.Hyp Ω) (c : Chart Ω u) : commutator G = ⊤ := by
  have hYle : pSpan (Generic.centMembers Ω u) ≤ commutator G := by
    have h1 : (commutator ↥(pSpan (Generic.centMembers Ω u))).map
        (pSpan (Generic.centMembers Ω u)).subtype ≤ commutator G := by
      rw [commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    rw [c.perfect, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    exact h1
  obtain ⟨L₀, hL₀, -⟩ := c.label_surj ({0, 1, 2, 3} : Finset (Fin 6)) (by decide) true
  have hL₀Ω : L₀ ∈ Ω := (Generic.mem_centMembers.mp hL₀).1
  have hL₀G : L₀ ≤ commutator G := le_trans (le_pSpan hL₀) hYle
  have hall : ∀ K ∈ Ω, K ≤ commutator G := by
    intro K hK
    obtain ⟨g, rfl⟩ := H.endHyp.thmD.trans L₀ hL₀Ω K hK
    intro x hx
    unfold conjSub at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.Normal.conj_mem inferInstance y (hL₀G hy) g
  apply eq_top_iff.mpr
  rw [← H.endHyp.thmD.gen]
  exact pSpan_le hall

theorem pCore_eq_zGroup (H : End18.Hyp Ω) {c : Chart Ω u} {co : Coords c}
    (cl : Classes co) (pt : Points u) : pCore 2 G = zGroup Ω := by
  classical
  have hΩ : ConjInvariant Ω := H.endHyp.thmD.hyp.conjInvariant
  haveI hDn : (zGroup Ω).Normal := Chart.ae8b2_zGroup_normal hΩ
  have hQK : pCore 2 G = pt.π.ker := by
    rw [Points.ker_eq_centralizer H cl pt, H.centralizer_zGroup_eq_pCore]
  have hDK : zGroup Ω ≤ pt.π.ker := by
    rw [← hQK]
    exact H.endHyp.zGroup_le_pCore
  let ρ : G ⧸ zGroup Ω →* Equiv.Perm (Fin 8) := QuotientGroup.lift (zGroup Ω) pt.π hDK
  have hρπ : ∀ g : G, ρ (g : G ⧸ zGroup Ω) = pt.π g := fun g => rfl
  have hρrange : ρ.range = alternatingGroup (Fin 8) := by
    rw [← Points.range_eq H cl pt]
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨g, rfl⟩
    · rintro _ ⟨g, rfl⟩
      exact ⟨(g : G ⧸ zGroup Ω), rfl⟩
  have hcent : ρ.ker ≤ Subgroup.center (G ⧸ zGroup Ω) := by
    intro x hx
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    have hqQ : q ∈ pCore 2 G := by
      rw [hQK]
      exact hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : ((g * q * g⁻¹ * q⁻¹ : G) : G ⧸ zGroup Ω) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (H.commutator_pCore_mem_zGroup_all g hqQ)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
  have hkerE : ρ.ker = (pCore 2 G).map (QuotientGroup.mk' (zGroup Ω)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (zGroup Ω) x
      refine ⟨q, ?_, rfl⟩
      rw [hQK]
      exact hx
    · rintro ⟨q, hq, rfl⟩
      rw [hQK] at hq
      exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hq)
  have h2 : IsPGroup 2 ρ.ker := by
    rw [hkerE]
    exact IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := G)) (QuotientGroup.mk' (zGroup Ω))
  let K : Subgroup ↥(pSpan (Generic.centMembers Ω u)) :=
    (pCore 2 G).subgroupOf (pSpan (Generic.centMembers Ω u))
  have hK2 : IsPGroup 2 K := IsPGroup.comap_subtype (CFSG.pCore_isPGroup (p := 2) (G := G))
  haveI hKn : K.Normal := inferInstance
  let N : Subgroup ↥(AE.aeSub 6) := K.map c.ψ.toMonoidHom
  haveI hNn : N.Normal := Subgroup.Normal.map hKn c.ψ.toMonoidHom c.ψ.surjective
  have hN2 : IsPGroup 2 N := hK2.map c.ψ.toMonoidHom
  have hpermN : ∀ n ∈ N, (n : AE.Wr 6).perm = 1 := Chart.perm_one_of_normal_isPGroup N hN2
  obtain ⟨ι, hι⟩ := Points.map_H0_eq_altOn H cl pt
  have hH0' : (c.H0.map (QuotientGroup.mk' (zGroup Ω))) ⊓ ρ.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨h, hh0, rfl⟩ := Subgroup.mem_map.mp hx1
    have hhQ : h ∈ pCore 2 G := by
      rw [hQK]
      exact hx2
    obtain ⟨y, hy, hyh⟩ := Subgroup.mem_map.mp hh0
    have hyh' : (y : G) = h := hyh
    have hyK : y ∈ K := Subgroup.mem_subgroupOf.mpr (hyh' ▸ hhQ)
    have hperm : (c.ψ y : AE.Wr 6).perm = 1 :=
      hpermN (c.ψ y) (Subgroup.mem_map_of_mem _ hyK)
    have hhD : h ∈ zGroup Ω := by
      rw [← hyh']
      exact (c.mem_zGroup_iff H y).mpr hperm
    have hmem : h ∈ c.H0 ⊓ zGroup Ω := ⟨hh0, hhD⟩
    rw [Chart.H0_inf_zGroup H c, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot, hmem, map_one]
  have hH0ρ : (c.H0.map (QuotientGroup.mk' (zGroup Ω))).map ρ = altOn (Finset.univ.image ι) := by
    have hcomp : ρ.comp (QuotientGroup.mk' (zGroup Ω)) = pt.π := MonoidHom.ext fun g => rfl
    rw [Subgroup.map_map, hcomp, hι]
  obtain ⟨f, hf⟩ := Glue8.exists_section_of_central ρ hρrange hcent h2 ι _ hH0' hH0ρ
  have hmapTop : (⊤ : Subgroup G).map (QuotientGroup.mk' (zGroup Ω)) = ⊤ := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  have hXtop : commutator (G ⧸ zGroup Ω) = ⊤ := by
    have key := Subgroup.map_commutator (H₁ := (⊤ : Subgroup G)) (H₂ := (⊤ : Subgroup G))
      (QuotientGroup.mk' (zGroup Ω))
    rw [hmapTop, ← commutator_def G, commutator_eq_top H c, hmapTop] at key
    rw [commutator_def]
    exact key.symm
  have hcommF : commutator (G ⧸ zGroup Ω) ≤ f.range := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    have hxA : ρ x ∈ alternatingGroup (Fin 8) := hρrange ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩
    have hyA : ρ y ∈ alternatingGroup (Fin 8) := hρrange ▸ MonoidHom.mem_range.mpr ⟨y, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a : alternatingGroup (Fin 8), (a : Equiv.Perm (Fin 8)) = ρ x :=
      ⟨⟨ρ x, hxA⟩, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : alternatingGroup (Fin 8), (b : Equiv.Perm (Fin 8)) = ρ y :=
      ⟨⟨ρ y, hyA⟩, rfl⟩
    have hkx : x * (f a)⁻¹ ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hf a, ha]
      exact mul_inv_cancel _
    have hky : y * (f b)⁻¹ ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hf b, hb]
      exact mul_inv_cancel _
    obtain ⟨k, hk⟩ : ∃ k, k = x * (f a)⁻¹ := ⟨_, rfl⟩
    obtain ⟨k', hk'⟩ : ∃ k', k' = y * (f b)⁻¹ := ⟨_, rfl⟩
    have hkc : k ∈ Subgroup.center (G ⧸ zGroup Ω) := hcent (hk ▸ hkx)
    have hkc' : k' ∈ Subgroup.center (G ⧸ zGroup Ω) := hcent (hk' ▸ hky)
    have hxk : x = k * f a := by rw [hk]; group
    have hyk : y = k' * f b := by rw [hk']; group
    rw [hxk, hyk, ae8j_comm_central hkc hkc' (f a) (f b), ← map_commutatorElement]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hkerbot : ρ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    have hkF : k ∈ f.range := by
      have htop : (⊤ : Subgroup (G ⧸ zGroup Ω)) ≤ f.range := by
        rw [← hXtop]
        exact hcommF
      exact htop (Subgroup.mem_top k)
    obtain ⟨a, rfl⟩ := hkF
    rw [MonoidHom.mem_ker, hf a] at hk
    have ha1 : a = 1 := Subtype.ext hk
    rw [Subgroup.mem_bot, ha1, map_one]
  apply le_antisymm
  · intro q hq
    rw [hQK] at hq
    have hmk : (q : G ⧸ zGroup Ω) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, hρπ]
      exact MonoidHom.mem_ker.mp hq
    rw [hkerbot, Subgroup.mem_bot] at hmk
    exact (QuotientGroup.eq_one_iff q).mp hmk
  · exact H.endHyp.zGroup_le_pCore

theorem centralizer_eq_zGroup (H : End18.Hyp Ω) {c : Chart Ω u} {co : Coords c}
    (cl : Classes co) (pt : Points u) :
    Subgroup.centralizer (zGroup Ω : Set G) = zGroup Ω := by
  rw [H.centralizer_zGroup_eq_pCore, pCore_eq_zGroup H cl pt]

theorem Points.ker_eq_zGroup (H : End18.Hyp Ω) {c : Chart Ω u} {co : Coords c}
    (cl : Classes co) (pt : Points u) : pt.π.ker = zGroup Ω := by
  rw [Points.ker_eq_centralizer H cl pt, centralizer_eq_zGroup H cl pt]

end AE8End

end CFSG.ClassicalInvolution.Q3.Sec13
