module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinGraph
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPair

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

set_option linter.unusedSectionVars false

section MaxOrb

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

structure OrbitStd (Ω : Set (Subgroup G)) : Prop where
  hyp : HypOmegaGen Ω
  two : ∀ J ∈ Ω, IsPGroup 2 J
  graph : GraphFam Ω (nbrAdj Ω)

theorem TwinGraphStd.orbitStd {K₀ : Subgroup G} (hs : TwinGraphStd K₀) :
    OrbitStd (CoreAssembly.conjClass K₀) :=
  ⟨hs.hyp, hs.two, hs.graphFam⟩

@[expose] def piGen (π : Set (Subgroup G)) : Subgroup G := ⨆ M ∈ π, M

theorem le_piGen {π : Set (Subgroup G)} {M : Subgroup G} (hM : M ∈ π) : M ≤ piGen π :=
  le_iSup₂_of_le M hM le_rfl

theorem piGen_le {π : Set (Subgroup G)} {H : Subgroup G} (h : ∀ M ∈ π, M ≤ H) : piGen π ≤ H :=
  iSup₂_le h

theorem piGen_conj (π : Set (Subgroup G)) (g : G) :
    piGen (conjSub g '' π) = conjSub g (piGen π) := by
  apply le_antisymm
  · refine piGen_le ?_
    rintro _ ⟨M, hM, rfl⟩
    exact conjSub_mono (le_piGen hM)
  · show (piGen π).map (MulAut.conj g).toMonoidHom ≤ _
    rw [Subgroup.map_le_iff_le_comap]
    refine piGen_le fun M hM => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_piGen ⟨M, hM, rfl⟩

theorem commutes_piGen_of {v : Subgroup G} {π : Set (Subgroup G)}
    (h : ∀ M ∈ π, Commutes v M) : Commutes v (piGen π) := by
  have hle : piGen π ≤ Subgroup.centralizer (v : Set G) :=
    piGen_le fun M hM y hy => Subgroup.mem_centralizer_iff.mpr fun x hx => h M hM x hx y hy
  intro x hx y hy
  exact Subgroup.mem_centralizer_iff.mp (hle hy) x hx

theorem commutes_of_mutual_normalizer (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    {J J' : Subgroup G} (hJ : J ∈ Ω) (hJ' : J' ∈ Ω) (hne : J ≠ J')
    (h1 : J ≤ Subgroup.normalizer (J' : Set G)) (h1' : J' ≤ Subgroup.normalizer (J : Set G)) :
    Commutes J J' := by
  have hle : ⁅J, J'⁆ ≤ J ⊓ J' := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h3 := ((Subgroup.mem_normalizer_iff.mp (h1' hy)) x⁻¹).mp (J.inv_mem hx)
      have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [e]
      exact J.mul_mem hx h3
    · have h3 := ((Subgroup.mem_normalizer_iff.mp (h1 hx)) y).mp hy
      exact J'.mul_mem h3 (J'.inv_mem hy)
  have hbot : ⁅J, J'⁆ = ⊥ := by
    have h2I : IsPGroup 2 ↥(J ⊓ J') := (h2 J hJ).to_le inf_le_left
    obtain ⟨n, hn⟩ := h2I.exists_card_eq
    obtain ⟨hv, hc⟩ := hΩ.omega4 J hJ J' hJ' hne
    have hval : padicValNat 2 (Nat.card ↥(J ⊓ J')) = n := by
      rw [hn, padicValNat.prime_pow]
    rw [hval] at hv hc
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv with h0 | h1
    · rw [h0, pow_zero] at hn
      have hb : J ⊓ J' = ⊥ := Subgroup.eq_bot_of_card_eq _ hn
      rw [hb] at hle
      exact le_bot_iff.mp hle
    · have h3 := hc h1
      exact le_bot_iff.mp
        (h3.trans (inf_le_left.trans (oddCoreOf_eq_bot_of_isPGroup (h2 J hJ)).le))
  intro x hx y hy
  have hmem : ⁅x, y⁆ ∈ ⁅J, J'⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hmem

theorem noncomm_of_mem (hΩ : HypOmegaGen Ω) {M : Subgroup G} (hM : M ∈ Ω) :
    ∃ a ∈ M, ∃ b ∈ M, a * b ≠ b * a := by
  obtain ⟨-, P, ⟨hPM, -, -⟩, hP⟩ := hΩ.omega1 M hM
  by_contra h
  push Not at h
  exact hP ⟨⟨fun a b => Subtype.ext (h a (hPM a.2) b (hPM b.2))⟩⟩

theorem le_closure_noncentral {M : Subgroup G} (hM : ∃ a ∈ M, ∃ b ∈ M, a * b ≠ b * a) :
    M ≤ Subgroup.closure {v : G | v ∈ M ∧ ¬ ∀ w ∈ M, v * w = w * v} := by
  obtain ⟨a, ha, b, hb, hab⟩ := hM
  intro x hx
  by_cases hxc : ∀ w ∈ M, x * w = w * x
  · have hanc : a ∈ {v : G | v ∈ M ∧ ¬ ∀ w ∈ M, v * w = w * v} :=
      ⟨ha, fun h => hab (h b hb)⟩
    have hxanc : x * a ∈ {v : G | v ∈ M ∧ ¬ ∀ w ∈ M, v * w = w * v} := by
      refine ⟨M.mul_mem hx ha, fun hc => hab ?_⟩
      have h1 := hc b hb
      have h2 := hxc b hb
      apply mul_left_cancel (a := x)
      calc x * (a * b) = x * a * b := by group
        _ = b * (x * a) := h1
        _ = (b * x) * a := by group
        _ = (x * b) * a := by rw [h2]
        _ = x * (b * a) := by group
    have e : x = (x * a) * a⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure hxanc)
      (Subgroup.inv_mem _ (Subgroup.subset_closure hanc))
  · exact Subgroup.subset_closure ⟨hx, hxc⟩

@[expose] def NoCentralInv (π : Set (Subgroup G)) : Prop :=
  ∀ J ∈ π, ∀ u : G, IsUniqueInvolution J u → ¬ ∀ x ∈ piGen π, x * u = u * x

theorem NoCentralInv.conj {π : Set (Subgroup G)} (h : NoCentralInv π) (g : G) :
    NoCentralInv (conjSub g '' π) := by
  rintro _ ⟨M, hM, rfl⟩ u hu hc
  have hu' : IsUniqueInvolution M (g⁻¹ * u * g) := by
    have := hu.conj g⁻¹
    rwa [conjSub_inv_conjSub, inv_inv] at this
  refine h M hM _ hu' fun x hx => ?_
  have hx' : g * x * g⁻¹ ∈ piGen (conjSub g '' π) := by
    rw [piGen_conj]
    exact conj_mem_conjSub hx
  have h1 := hc _ hx'
  calc x * (g⁻¹ * u * g) = g⁻¹ * ((g * x * g⁻¹) * u) * g := by group
    _ = g⁻¹ * (u * (g * x * g⁻¹)) * g := by rw [h1]
    _ = (g⁻¹ * u * g) * x := by group

variable (hs : OrbitStd Ω)
include hs

theorem OrbitStd.commutes_of_nbrAdj {J J' : Subgroup G} (h : nbrAdj Ω J J') : Commutes J J' := by
  have h1 := (mem_omegaNbr_iff hs.hyp hs.two).mp h.2
  have h2 := (mem_omegaNbr_iff hs.hyp hs.two).mp (hs.graph.graph.symm h).2
  exact commutes_of_mutual_normalizer hs.hyp hs.two h.1 h1.1 h2.2.1 h2.2.2 h1.2.2

theorem OrbitStd.commutes_piGen {K : Subgroup G} {π : Set (Subgroup G)}
    (hπ : π ∈ maxOrbs (nbrAdj Ω) K) : Commutes K (piGen π) :=
  commutes_piGen_of fun _ hM => hs.commutes_of_nbrAdj (adj_of_mem_isMaxOrb hs.graph hπ hM)

theorem OrbitStd.le_centralizer_piGen {K : Subgroup G} {π : Set (Subgroup G)}
    (hπ : π ∈ maxOrbs (nbrAdj Ω) K) : K ≤ Subgroup.centralizer (piGen π : Set G) :=
  fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => (hs.commutes_piGen hπ x hx y hy).symm

theorem OrbitStd.commute_unique_piGen {K : Subgroup G} {π : Set (Subgroup G)}
    (hπ : π ∈ maxOrbs (nbrAdj Ω) K) {z : G} (hz : IsUniqueInvolution K z) :
    ∀ x ∈ piGen π, x * z = z * x :=
  fun x hx => (hs.commutes_piGen hπ z hz.mem x hx).symm

theorem OrbitStd.piGen_le_centralizer {K : Subgroup G} {π : Set (Subgroup G)}
    (hπ : π ∈ maxOrbs (nbrAdj Ω) K) {z : G} (hz : IsUniqueInvolution K z) :
    piGen π ≤ Subgroup.centralizer ({z} : Set G) :=
  fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hs.commute_unique_piGen hπ hz x hx)

theorem OrbitStd.commutes_beta {π : Set (Subgroup G)} {v : Subgroup G}
    (hv : v ∈ betaOf (nbrAdj Ω) Ω π) : Commutes v (piGen π) :=
  commutes_piGen_of fun _ hM => hs.commutes_of_nbrAdj (hv.2 _ hM)

theorem OrbitStd.beta_le_centralizer {π : Set (Subgroup G)} {v : Subgroup G}
    (hv : v ∈ betaOf (nbrAdj Ω) Ω π) : v ≤ Subgroup.centralizer (piGen π : Set G) :=
  fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => (hs.commutes_beta hv x hx y hy).symm

variable {K : Subgroup G} {π : Set (Subgroup G)}

theorem OrbitStd.mem_beta_of_centralizes (hπ : π ∈ maxOrbs (nbrAdj Ω) K) (hH1 : NoCentralInv π)
    {L : Subgroup G} (hL : L ∈ Ω) {u : G} (hu : IsUniqueInvolution L u)
    (hc : ∀ x ∈ piGen π, x * u = u * x) : L ∈ betaOf (nbrAdj Ω) Ω π := by
  have hLπ : L ∉ π := fun h => hH1 L h u hu hc
  refine ⟨hL, fun M hM => ?_⟩
  have hKM := adj_of_mem_isMaxOrb hs.graph hπ hM
  have hMΩ : M ∈ Ω := hs.graph.mem (hs.graph.graph.symm hKM)
  have hML : M ≠ L := fun h => hLπ (h ▸ hM)
  refine ⟨hL, (mem_omegaNbr_iff hs.hyp hs.two).mpr ⟨hMΩ, hML, ?_⟩⟩
  refine (le_closure_noncentral (noncomm_of_mem hs.hyp hMΩ)).trans
    ((Subgroup.closure_le _).mpr ?_)
  rintro v ⟨hvM, hvnc⟩
  exact hs.hyp.omega5 L hL M hMΩ hML.symm u hu v hvM hvnc
    ((hs.two M hMΩ).to_le (Subgroup.zpowers_le.mpr hvM)) (hc v (le_piGen hM hvM))

theorem OrbitStd.twinSet_subset_beta (hπ : π ∈ maxOrbs (nbrAdj Ω) K) (hH1 : NoCentralInv π) :
    twinSet Ω K ⊆ betaOf (nbrAdj Ω) Ω π := by
  rintro J ⟨hJΩ, z, hzK, hzJ⟩
  exact hs.mem_beta_of_centralizes hπ hH1 hJΩ hzJ (hs.commute_unique_piGen hπ hzK)

theorem OrbitStd.disjoint_twinSet (hπ : π ∈ maxOrbs (nbrAdj Ω) K) (hH1 : NoCentralInv π) :
    Disjoint (twinSet Ω K) π := by
  rw [Set.disjoint_left]
  rintro J ⟨-, z, hzK, hzJ⟩ hJπ
  exact hH1 J hJπ z hzJ (hs.commute_unique_piGen hπ hzK)

theorem OrbitStd.nbr_diff_subset_beta (hπ : π ∈ maxOrbs (nbrAdj Ω) K) {J : Subgroup G}
    (hKJ : nbrAdj Ω K J) (hJπ : J ∉ π) : J ∈ betaOf (nbrAdj Ω) Ω π := by
  refine ⟨hs.graph.mem (hs.graph.graph.symm hKJ), fun M hM => ?_⟩
  have hKM := adj_of_mem_isMaxOrb hs.graph hπ hM
  refine hs.graph.graph.sep hKJ hKM fun hMorb => hJπ ?_
  have h1 := mem_orbOf_comm hMorb
  rwa [orbOf_eq_of_mem_isMaxOrb hπ hM] at h1

theorem OrbitStd.conj_image_eq_of_centralizer (hK : K ∈ Ω) (hπ : π ∈ maxOrbs (nbrAdj Ω) K)
    (hH1 : NoCentralInv π) {z : G} (hz : IsUniqueInvolution K z) {x : G}
    (hx : x ∈ Subgroup.centralizer ({z} : Set G)) : conjSub x '' π = π := by
  have hxz : x * z * x⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    rw [hx, mul_inv_cancel_right]
  have hxz' : IsUniqueInvolution (conjSub x K) z := by
    have := hz.conj x
    rwa [hxz] at this
  have hLΩ : conjSub x K ∈ Ω := hs.graph.conjMem K hK x
  have hβ := hs.twinSet_subset_beta hπ hH1 (show conjSub x K ∈ twinSet Ω K from ⟨hLΩ, z, hz, hxz'⟩)
  have h1 : π ∈ maxOrbs (nbrAdj Ω) (conjSub x K) := (mem_betaOf_iff hs.graph hK hπ).mp hβ
  exact maxOrb_unique hs.graph hLΩ (isMaxOrb_conj hs.graph hπ x) h1

theorem OrbitStd.centralizer_le_normalizer_piGen (hK : K ∈ Ω) (hπ : π ∈ maxOrbs (nbrAdj Ω) K)
    (hH1 : NoCentralInv π) {z : G} (hz : IsUniqueInvolution K z) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (piGen π : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have e : conjSub x (piGen π) = piGen π := by
    rw [← piGen_conj, hs.conj_image_eq_of_centralizer hK hπ hH1 hz hx]
  have h1 : x * h * x⁻¹ ∈ conjSub x (piGen π) ↔ h ∈ piGen π := by
    rw [mem_conjSub_iff, show x⁻¹ * (x * h * x⁻¹) * x = h by group]
  rw [e] at h1
  exact h1.symm

theorem OrbitStd.piGen_normal (hK : K ∈ Ω) (hπ : π ∈ maxOrbs (nbrAdj Ω) K)
    (hH1 : NoCentralInv π) {z : G} (hz : IsUniqueInvolution K z) :
    ((piGen π).subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (hs.piGen_le_centralizer hπ hz)).mpr
    (hs.centralizer_le_normalizer_piGen hK hπ hH1 hz)

theorem OrbitStd.mem_conj_image_of_mem (hπ : π ∈ maxOrbs (nbrAdj Ω) K) {g : G}
    (hg : conjSub g K ∈ π) : K ∈ conjSub g '' π := by
  obtain ⟨hQ, -⟩ := orbOf_eq_conj_of_maxOrb hs.graph hπ hg rfl
  have h1 := mem_orbOf_self (A := nbrAdj Ω) (conjSub g K) K
  rwa [hQ] at h1

theorem OrbitStd.conj_piGen_normal (hK : K ∈ Ω) (hπ : π ∈ maxOrbs (nbrAdj Ω) K)
    (hH1 : NoCentralInv π) {z : G} (hz : IsUniqueInvolution K z) (g : G) :
    ((conjSub g (piGen π)).subgroupOf (Subgroup.centralizer ({g * z * g⁻¹} : Set G))).Normal := by
  rw [← piGen_conj]
  exact hs.piGen_normal (hs.graph.conjMem K hK g) (isMaxOrb_conj hs.graph hπ g) (hH1.conj g)
    (hz.conj g)

theorem OrbitStd.conj_piGen_le_centralizer (hK : K ∈ Ω) (hπ : π ∈ maxOrbs (nbrAdj Ω) K)
    (hH1 : NoCentralInv π) {z : G} (hz : IsUniqueInvolution K z) (g : G) :
    conjSub g (piGen π) ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set G) ∧
      Subgroup.centralizer ({g * z * g⁻¹} : Set G) ≤ Subgroup.normalizer (conjSub g (piGen π) : Set G) := by
  rw [← piGen_conj]
  exact ⟨hs.piGen_le_centralizer (isMaxOrb_conj hs.graph hπ g) (hz.conj g),
    hs.centralizer_le_normalizer_piGen (hs.graph.conjMem K hK g) (isMaxOrb_conj hs.graph hπ g)
      (hH1.conj g) (hz.conj g)⟩

theorem OrbitStd.le_conj_piGen (hπ : π ∈ maxOrbs (nbrAdj Ω) K) {g : G} (hg : conjSub g K ∈ π) :
    K ≤ conjSub g (piGen π) := by
  rw [← piGen_conj]
  exact le_piGen (hs.mem_conj_image_of_mem hπ hg)

theorem OrbitStd.conj_le_inf_centralizer (hπ : π ∈ maxOrbs (nbrAdj Ω) K) {g : G}
    (hg : conjSub g K ∈ π) :
    conjSub g K ≤ piGen π ⊓ Subgroup.centralizer (conjSub g (piGen π) : Set G) := by
  rw [← piGen_conj]
  exact le_inf (le_piGen hg) (hs.le_centralizer_piGen (isMaxOrb_conj hs.graph hπ g))

theorem OrbitStd.beta_subset_conj_image (hK : K ∈ Ω) (hπ : π ∈ maxOrbs (nbrAdj Ω) K)
    {g : G} (hg : conjSub g K ∈ π) : betaOf (nbrAdj Ω) Ω π ⊆ conjSub g '' π := by
  intro v hv
  by_contra hvπ
  have hπg : conjSub g '' π ∈ maxOrbs (nbrAdj Ω) (conjSub g K) := isMaxOrb_conj hs.graph hπ g
  have hgK : conjSub g K ∈ Ω := hs.graph.conjMem K hK g
  have hadj : nbrAdj Ω (conjSub g K) v :=
    hs.graph.graph.symm (hv.2 _ hg)
  have hv2 := hs.nbr_diff_subset_beta hπg hadj hvπ
  have h1 : conjSub g '' π ∈ maxOrbs (nbrAdj Ω) v := (mem_betaOf_iff hs.graph hgK hπg).mp hv2
  have h2 : π ∈ maxOrbs (nbrAdj Ω) v := (mem_betaOf_iff hs.graph hK hπ).mp hv
  have h3 : conjSub g '' π = π := maxOrb_unique hs.graph hv.1 h1 h2
  have h4 := hs.mem_conj_image_of_mem hπ hg
  rw [h3] at h4
  exact not_mem_of_isMaxOrb hs.graph hπ h4

end MaxOrb

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
