module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabL34Check
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdOrders

public section

namespace CFSG.QuasithinUnique.Id2519.Tab.L34

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

theorem eq_one_or_r₂_of_cent
    {x : Equiv.Perm (Fin 42)} (hx : x ∈ R)
    (hc : ∀ c ∈ C₂, c * x = x * c) : x = 1 ∨ x = r₂ := by
  obtain ⟨k, hk, hrep⟩ := enumerates_R.exists_pos hx
  have hscan : allBelow enumR.tabs.size (fun k =>
      !(allBelow (centS r₂T).size fun i =>
        comp 42 enumR.tabs[k]! (centS r₂T)[i]! == comp 42 (centS r₂T)[i]! enumR.tabs[k]!) ||
        enumR.tabs[k]! == idTab 42 || enumR.tabs[k]! == r₂T) = true := cent2Scan_eq
  rw [allBelow_eq_true] at hscan
  have h := hscan k hk
  have hcomm : (allBelow (centS r₂T).size fun i =>
      comp 42 enumR.tabs[k]! (centS r₂T)[i]! == comp 42 (centS r₂T)[i]! enumR.tabs[k]!) =
        true := by
    rw [allBelow_eq_true]
    intro i hi
    obtain ⟨c, hcC, hcrep⟩ := enumerates_C₂.exists_elt hi
    exact ((hrep.comp hcrep).beq_iff (hcrep.comp hrep)).2 (hc c hcC).symm
  simp only [hcomm, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl ((hrep.beq_iff TabRep.idTab).1 h)
  · exact Or.inr ((hrep.beq_iff tabRep_r₂).1 h)

theorem twist_witness
    {u : Equiv.Perm (Fin 42)} (hu : u ∈ C₂) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ s ∈ S, s⁻¹ * r₂ * s = r₂ * u := by
  obtain ⟨j, hj, hrep⟩ := enumerates_C₂.exists_pos hu
  have hscan : allBelow (centS r₂T).size (fun j =>
      (centS r₂T)[j]! == idTab 42 ||
      !(comp 42 (centS r₂T)[j]! (centS r₂T)[j]! == idTab 42) ||
      anyBelow enumS.tabs.size fun k =>
        (invTab 42 enumS.tabs[k]!).size == 42 &&
        comp 42 (invTab 42 enumS.tabs[k]!) enumS.tabs[k]! == idTab 42 &&
        comp 42 (comp 42 (invTab 42 enumS.tabs[k]!) r₂T) enumS.tabs[k]! ==
          comp 42 r₂T (centS r₂T)[j]!) = true := twistScan_eq
  rw [allBelow_eq_true] at hscan
  have h := hscan j hj
  simp only [Bool.or_eq_true, Bool.not_eq_true', anyBelow_eq_true] at h
  rcases h with (h | h) | ⟨k, hk, hk'⟩
  · exact absurd ((hrep.beq_iff TabRep.idTab).1 h) hu1
  · have := ((hrep.comp hrep).beq_iff TabRep.idTab).2 hu2
    rw [this] at h
    exact absurd h (by simp)
  · simp only [Bool.and_eq_true, beq_iff_eq] at hk'
    obtain ⟨⟨hsz, hinv⟩, heq⟩ := hk'
    obtain ⟨g, hgS, hgrep⟩ := enumerates_S.exists_elt hk
    have hgi := hgrep.inv hsz hinv
    refine ⟨g, hgS, ?_⟩
    exact (((hgi.comp tabRep_r₂).comp hgrep).eq_iff (tabRep_r₂.comp hrep)).1 heq

theorem map_conj_cent {c r : Equiv.Perm (Fin 42)} (hc : c ∈ R) :
    (Subgroup.centralizer {r} ⊓ S).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer {c * r * c⁻¹} ⊓ S := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, ⟨hxc, hxS⟩, rfl⟩
    refine ⟨?_, conj_mem_S hc hxS⟩
    calc c * x * c⁻¹ * (c * r * c⁻¹) = c * (x * r) * c⁻¹ := by group
      _ = c * (r * x) * c⁻¹ := by rw [hxc]
      _ = c * r * c⁻¹ * (c * x * c⁻¹) := by group
  · rintro ⟨hy, hyS⟩
    refine ⟨c⁻¹ * y * c, ⟨?_, ?_⟩, by group⟩
    · calc c⁻¹ * y * c * r = c⁻¹ * (y * (c * r * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * r * c⁻¹) * y) * c := by rw [hy]
        _ = r * (c⁻¹ * y * c) := by group
    · have := conj_mem_S (R.inv_mem hc) hyS
      rwa [inv_inv] at this

theorem card_cent_conj {c r : Equiv.Perm (Fin 42)} (hc : c ∈ R) :
    Nat.card ↥(Subgroup.centralizer {c * r * c⁻¹} ⊓ S) =
      Nat.card ↥(Subgroup.centralizer {r} ⊓ S) := by
  rw [← map_conj_cent hc]
  exact Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom)
    (MulAut.conj c).injective

theorem isConj_r₂_of_card
    {τ : R} (hτ : orderOf τ = 2) {B : Subgroup (Equiv.Perm (Fin 42))}
    (hB : B ≤ Subgroup.centralizer {(τ : Equiv.Perm (Fin 42))} ⊓ S) (hcard : 168 ≤ Nat.card B) :
    IsConj τ r₂R := by
  have h1 := Subgroup.card_le_of_le hB
  rcases (orderOf_eq_two_iff τ).1 hτ with h | h | h | h
  · exfalso
    obtain ⟨c, hcR, hc⟩ := eq_conj_of_isConj h
    rw [hc, card_cent_conj hcR] at h1
    have h64 : Nat.card ↥(Subgroup.centralizer {(r₁R : Equiv.Perm (Fin 42))} ⊓ S) = 64 := card_C₁
    omega
  · exact h
  · exfalso
    obtain ⟨c, hcR, hc⟩ := eq_conj_of_isConj h
    rw [hc, card_cent_conj hcR] at h1
    have h60 : Nat.card ↥(Subgroup.centralizer {(r₃R : Equiv.Perm (Fin 42))} ⊓ S) = 60 := card_C₃
    omega
  · exfalso
    obtain ⟨c, hcR, hc⟩ := eq_conj_of_isConj h
    rw [hc, card_cent_conj hcR] at h1
    have h72 : Nat.card ↥(Subgroup.centralizer {(r₄R : Equiv.Perm (Fin 42))} ⊓ S) = 72 := card_C₄
    omega

theorem card_cent_of_isConj {τ : R} (h : IsConj τ r₂R) :
    Nat.card ↥(Subgroup.centralizer {(τ : Equiv.Perm (Fin 42))} ⊓ S) = 168 := by
  obtain ⟨c, hcR, hc⟩ := eq_conj_of_isConj h
  rw [hc, card_cent_conj hcR]
  exact card_C₂

theorem eq_one_or_conj_of_cent
    {c : Equiv.Perm (Fin 42)} (hc : c ∈ R) {x : Equiv.Perm (Fin 42)}
    (hx : x ∈ R) (hcomm : ∀ s ∈ Subgroup.centralizer {c * r₂ * c⁻¹} ⊓ S, x * s = s * x) :
    x = 1 ∨ x = c * r₂ * c⁻¹ := by
  have key : c⁻¹ * x * c = 1 ∨ c⁻¹ * x * c = r₂ := by
    apply eq_one_or_r₂_of_cent (R.mul_mem (R.mul_mem (R.inv_mem hc) hx) hc)
    intro s hs
    have hsS : s ∈ S := hs.2
    have hsr : s * r₂ = r₂ * s := Subgroup.mem_centralizer_singleton_iff.mp hs.1
    have hmem : c * s * c⁻¹ ∈ Subgroup.centralizer {c * r₂ * c⁻¹} ⊓ S := by
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, conj_mem_S hc hsS⟩
      calc c * s * c⁻¹ * (c * r₂ * c⁻¹) = c * (s * r₂) * c⁻¹ := by group
        _ = c * (r₂ * s) * c⁻¹ := by rw [hsr]
        _ = c * r₂ * c⁻¹ * (c * s * c⁻¹) := by group
    have h := hcomm _ hmem
    calc s * (c⁻¹ * x * c) = c⁻¹ * ((c * s * c⁻¹) * x) * c := by group
      _ = c⁻¹ * (x * (c * s * c⁻¹)) * c := by rw [← h]
      _ = (c⁻¹ * x * c) * s := by group
  rcases key with h | h
  · left
    calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
      _ = 1 := by rw [h]; group
  · right
    calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
      _ = c * r₂ * c⁻¹ := by rw [h]

theorem patA_main
    (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G)
    (hXq : CFSG.IsQuasisimple ↥X) (ht : t ∈ Subgroup.normalizer (X : Set G)) (ht2 : t * t = 1)
    (hcomm : ⁅X, Subgroup.zpowers t⁆ = X)
    (hK : K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)))
    (hpat : PatA X K t) :
    (∀ Y : Subgroup G, Y ≤ Subgroup.normalizer (X : Set G) →
        Y ≤ Subgroup.centralizer (K : Set G) →
        (Y ⊓ Subgroup.centralizer (X : Set G)).relIndex Y ≤ 2) ∧
      (Subgroup.center ↥X = ⊥ → ∀ u ∈ K, u * u = 1 → ∃ x ∈ X, x⁻¹ * t * x = t * u) := by
  obtain ⟨hL32, hmodel, -, -⟩ := hpat
  obtain ⟨e0⟩ := nonempty_equiv_of_stated (↥X ⧸ Subgroup.center ↥X) hmodel
  have hπ := quotProj_surjective e0
  have hker := quotProj_ker e0
  have hX : Group.IsPerfect ↥X := hXq.1
  have hKXt : K ≤ X ⊓ Subgroup.centralizer ({t} : Set G) := by
    rw [hK]
    exact perfectResidualOf_le _
  have hKX : K ≤ X := hKXt.trans inf_le_left
  have hα2 := quotAct_mul_self (quotProj e0) hπ hker ht ht2
  have hα1 := quotAct_ne_one (quotProj e0) hπ hker ht hXq hcomm
  obtain ⟨e, he, -⟩ := full_automorphism_action
  obtain ⟨τ, hτe⟩ : ∃ τ : R, e τ = quotAct (quotProj e0) hπ hker ht :=
    ⟨e.symm _, e.apply_symm_apply _⟩
  obtain ⟨τp, hτp⟩ : ∃ τp : Equiv.Perm (Fin 42), τp = (τ : Equiv.Perm (Fin 42)) := ⟨_, rfl⟩
  have hτs : ∀ s : S, ((quotAct (quotProj e0) hπ hker ht s : S) : Equiv.Perm (Fin 42)) =
      τp * s * τp⁻¹ := by
    intro s
    rw [hτp, ← hτe]
    exact he τ s
  have hτ2 : τ * τ = 1 := by
    apply e.injective
    rw [map_mul, hτe, hα2, map_one]
  have hτ2' : τp * τp = 1 := by
    rw [hτp]
    exact congrArg Subtype.val hτ2
  have hτi : τp⁻¹ = τp := inv_eq_of_mul_eq_one_right hτ2'
  have hτ1 : τ ≠ 1 := by
    intro h
    apply hα1
    rw [← hτe, h, map_one]
  have hord : orderOf τ = 2 := orderOf_eq_prime (by rw [sq]; exact hτ2) hτ1
  let ρ : ↥K →* ↥S := (quotProj e0).comp (Subgroup.inclusion hKX)
  have hKcenter : Subgroup.center ↥K = ⊥ := by
    have hf := l2pFacts ↥K (Or.inr hL32)
    exact center_eq_bot_of_simple_nonabelian hf.simple hf.nonabelian
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hz : Subgroup.inclusion hKX k ∈ Subgroup.center ↥X := by
      rw [← hker]
      exact MonoidHom.mem_ker.mpr hk
    have hzk : k ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro k'
      apply Subtype.ext
      exact congrArg (Subtype.val : ↥X → G) (hz (Subgroup.inclusion hKX k'))
    rw [hKcenter] at hzk
    exact Subgroup.mem_bot.mp hzk
  have hKbcard0 : Nat.card ρ.range = 168 := by
    have h := Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv
    rw [← h]
    exact card_of_psl_three_two hL32
  have hρfix : ∀ k : ↥K, quotAct (quotProj e0) hπ hker ht (ρ k) = ρ k := by
    intro k
    have hkt : (k : G) * t = t * k := Subgroup.mem_centralizer_singleton_iff.mp (hKXt k.2).2
    have hy : ((Subgroup.inclusion hKX k : X) : G) =
        t * ((Subgroup.inclusion hKX k : X) : G) * t⁻¹ := by
      rw [Subgroup.coe_inclusion]
      calc (k : G) = (k * t) * t⁻¹ := by group
        _ = (t * k) * t⁻¹ := by rw [hkt]
    exact quotAct_apply (quotProj e0) hπ hker ht _ _ hy
  have hKbcard : Nat.card (ρ.range.map S.subtype) = 168 := by
    rw [Subgroup.card_map_of_injective S.subtype_injective]
    exact hKbcard0
  have hKbC' : ρ.range.map S.subtype ≤ Subgroup.centralizer {τp} ⊓ S := by
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, (ρ k).2⟩
    have h := hτs (ρ k)
    rw [hρfix k] at h
    calc ((ρ k : S) : Equiv.Perm (Fin 42)) * τp =
        (τp * ((ρ k : S) : Equiv.Perm (Fin 42)) * τp⁻¹) * τp := by rw [← h]
      _ = τp * ((ρ k : S) : Equiv.Perm (Fin 42)) := by group
  have hKbC : ρ.range.map S.subtype ≤
      Subgroup.centralizer {(τ : Equiv.Perm (Fin 42))} ⊓ S := by
    rw [← hτp]
    exact hKbC'
  have hconj : IsConj τ r₂R := isConj_r₂_of_card hord hKbC (by rw [hKbcard])
  obtain ⟨c, hcR, hτc⟩ := eq_conj_of_isConj hconj
  have hτc' : τp = c * r₂ * c⁻¹ := by
    rw [hτp]
    exact hτc
  have hKbeq : ρ.range.map S.subtype = Subgroup.centralizer {c * r₂ * c⁻¹} ⊓ S := by
    rw [← hτc', hτp]
    exact Subgroup.eq_of_le_of_card_ge hKbC (by rw [card_cent_of_isConj hconj, hKbcard])
  refine ⟨?_, ?_⟩
  ·
    intro Y hYn hYc
    have hBsub : ∀ β : MulAut ↥S, (∀ k ∈ ρ.range, β k = k) →
        β = 1 ∨ β = quotAct (quotProj e0) hπ hker ht := by
      intro β hβ
      obtain ⟨r, rfl⟩ := e.surjective β
      have hcomm' : ∀ s ∈ Subgroup.centralizer {c * r₂ * c⁻¹} ⊓ S,
          (r : Equiv.Perm (Fin 42)) * s = s * r := by
        intro s hs
        rw [← hKbeq] at hs
        obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := hs
        have h1 : e r (ρ k) = ρ k := hβ (ρ k) ⟨k, rfl⟩
        have h2 : ((ρ k : S) : Equiv.Perm (Fin 42)) =
            (r : Equiv.Perm (Fin 42)) * ((ρ k : S) : Equiv.Perm (Fin 42)) *
              (r : Equiv.Perm (Fin 42))⁻¹ := by
          have h3 := he r (ρ k)
          rw [h1] at h3
          exact h3
        calc (r : Equiv.Perm (Fin 42)) * ((ρ k : S) : Equiv.Perm (Fin 42)) =
            ((r : Equiv.Perm (Fin 42)) * ((ρ k : S) : Equiv.Perm (Fin 42)) *
              (r : Equiv.Perm (Fin 42))⁻¹) * r := by group
          _ = ((ρ k : S) : Equiv.Perm (Fin 42)) * r := by rw [← h2]
      rcases eq_one_or_conj_of_cent hcR r.2 hcomm' with h | h
      · left
        have : r = 1 := Subtype.ext h
        rw [this, map_one]
      · right
        have : r = τ := Subtype.ext (h.trans (hτc'.symm.trans hτp))
        rw [this, hτe]
    have hsub : ((actHom (quotProj e0) hπ hker Y hYn).range : Set (MulAut ↥S)) ⊆
        {1, quotAct (quotProj e0) hπ hker ht} := by
      rintro _ ⟨y, rfl⟩
      have hfix : ∀ k ∈ ρ.range, actHom (quotProj e0) hπ hker Y hYn y k = k := by
        rintro _ ⟨k', rfl⟩
        have hk : ((Subgroup.inclusion hKX k' : X) : G) * (y : G) =
            (y : G) * ((Subgroup.inclusion hKX k' : X) : G) :=
          Subgroup.mem_centralizer_iff.mp (hYc y.2) (k' : G) k'.2
        exact actHom_fix (quotProj e0) hπ hker Y hYn hk
      rcases hBsub _ hfix with h | h
      · exact Set.mem_insert_iff.2 (Or.inl h)
      · exact Set.mem_insert_iff.2 (Or.inr (Set.mem_singleton_iff.2 h))
    have hBcard : Nat.card (actHom (quotProj e0) hπ hker Y hYn).range ≤ 2 := by
      calc Nat.card (actHom (quotProj e0) hπ hker Y hYn).range
          = ((actHom (quotProj e0) hπ hker Y hYn).range : Set (MulAut ↥S)).ncard :=
            Nat.card_coe_set_eq _
        _ ≤ ({1, quotAct (quotProj e0) hπ hker ht} : Set (MulAut ↥S)).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
    rw [relIndex_eq_card_range (quotProj e0) hπ hker Y hYn hX]
    exact hBcard
  ·
    intro hZ u huK hu2
    by_cases hu1 : u = 1
    · exact ⟨1, X.one_mem, by rw [hu1]; simp⟩
    have huX : u ∈ X := hKX huK
    obtain ⟨ub, hubdef⟩ : ∃ ub : ↥S, ub = ρ ⟨u, huK⟩ := ⟨_, rfl⟩
    have hub2 : (ub : Equiv.Perm (Fin 42)) * ub = 1 := by
      have h0 : ρ (⟨u, huK⟩ * ⟨u, huK⟩) = 1 := by
        have : (⟨u, huK⟩ : ↥K) * ⟨u, huK⟩ = 1 := Subtype.ext hu2
        rw [this, map_one]
      rw [map_mul] at h0
      have h2 := congrArg (fun z : ↥S => (z : Equiv.Perm (Fin 42))) h0
      simpa [hubdef] using h2
    have hub1 : (ub : Equiv.Perm (Fin 42)) ≠ 1 := by
      intro h
      apply hu1
      have h1 : ρ ⟨u, huK⟩ = 1 := by
        rw [← hubdef]
        exact Subtype.ext h
      have h2 : (⟨u, huK⟩ : ↥K) = 1 := hρinj (h1.trans (map_one ρ).symm)
      exact congrArg Subtype.val h2
    have hubC : (ub : Equiv.Perm (Fin 42)) ∈ Subgroup.centralizer {τp} ⊓ S := by
      rw [hτp, hubdef]
      exact hKbC ⟨ρ ⟨u, huK⟩, ⟨⟨u, huK⟩, rfl⟩, rfl⟩
    have hubτ : (ub : Equiv.Perm (Fin 42)) * τp = τp * ub :=
      Subgroup.mem_centralizer_singleton_iff.mp hubC.1
    have hu'C : c⁻¹ * (ub : Equiv.Perm (Fin 42)) * c ∈ C₂ := by
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
      · rw [hτc'] at hubτ
        calc c⁻¹ * (ub : Equiv.Perm (Fin 42)) * c * r₂ =
            c⁻¹ * ((ub : Equiv.Perm (Fin 42)) * (c * r₂ * c⁻¹)) * c := by group
          _ = c⁻¹ * ((c * r₂ * c⁻¹) * (ub : Equiv.Perm (Fin 42))) * c := by rw [hubτ]
          _ = r₂ * (c⁻¹ * (ub : Equiv.Perm (Fin 42)) * c) := by group
      · have := conj_mem_S (R.inv_mem hcR) hubC.2
        rwa [inv_inv] at this
    have hu'2 : (c⁻¹ * (ub : Equiv.Perm (Fin 42)) * c) * (c⁻¹ * (ub : Equiv.Perm (Fin 42)) * c) =
        1 := by
      calc (c⁻¹ * (ub : Equiv.Perm (Fin 42)) * c) * (c⁻¹ * (ub : Equiv.Perm (Fin 42)) * c) =
          c⁻¹ * ((ub : Equiv.Perm (Fin 42)) * ub) * c := by group
        _ = 1 := by rw [hub2]; group
    have hu'1 : c⁻¹ * (ub : Equiv.Perm (Fin 42)) * c ≠ 1 := by
      intro h
      apply hub1
      calc (ub : Equiv.Perm (Fin 42)) = c * (c⁻¹ * (ub : Equiv.Perm (Fin 42)) * c) * c⁻¹ := by
            group
        _ = 1 := by rw [h]; group
    obtain ⟨s, hsS, hs⟩ := twist_witness hu'C hu'2 hu'1
    have hxbS : c * s * c⁻¹ ∈ S := conj_mem_S hcR hsS
    have hxb : (c * s * c⁻¹)⁻¹ * τp * (c * s * c⁻¹) = τp * ub := by
      rw [hτc']
      calc (c * s * c⁻¹)⁻¹ * (c * r₂ * c⁻¹) * (c * s * c⁻¹) = c * (s⁻¹ * r₂ * s) * c⁻¹ := by
            group
        _ = c * (r₂ * (c⁻¹ * (ub : Equiv.Perm (Fin 42)) * c)) * c⁻¹ := by rw [hs]
        _ = (c * r₂ * c⁻¹) * (ub : Equiv.Perm (Fin 42)) := by group
    obtain ⟨x₀, hx₀⟩ := hπ ⟨c * s * c⁻¹, hxbS⟩
    obtain ⟨y, hy⟩ : ∃ y : X, (y : G) = t * x₀ * t⁻¹ := ⟨conjAut X t ht x₀, coe_conjAut X ht x₀⟩
    have hαx : quotAct (quotProj e0) hπ hker ht (quotProj e0 x₀) = quotProj e0 y :=
      quotAct_apply (quotProj e0) hπ hker ht x₀ y hy
    have hcompat : ((quotProj e0 y : S) : Equiv.Perm (Fin 42)) =
        τp * ((quotProj e0 x₀ : S) : Equiv.Perm (Fin 42)) * τp⁻¹ := by
      rw [← hαx]
      exact hτs _
    have hkey : quotProj e0 (y⁻¹ * x₀) = ub := by
      apply Subtype.ext
      rw [map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcompat, hx₀]
      have h3 : (τp * (c * s * c⁻¹) * τp⁻¹)⁻¹ * (c * s * c⁻¹) =
          τp * ((c * s * c⁻¹)⁻¹ * τp⁻¹ * (c * s * c⁻¹)) := by group
      show (τp * (c * s * c⁻¹) * τp⁻¹)⁻¹ * (c * s * c⁻¹) = ub
      rw [h3, hτi, hxb]
      calc τp * (τp * (ub : Equiv.Perm (Fin 42))) = (τp * τp) * ub := by group
        _ = ub := by rw [hτ2', one_mul]
    have hmem : (y⁻¹ * x₀) * (Subgroup.inclusion hKX ⟨u, huK⟩)⁻¹ ∈ (quotProj e0).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkey, hubdef]
      exact mul_inv_cancel _
    rw [hker, hZ, Subgroup.mem_bot] at hmem
    have heq : y⁻¹ * x₀ = Subgroup.inclusion hKX ⟨u, huK⟩ := mul_inv_eq_one.mp hmem
    refine ⟨(x₀ : G), x₀.2, ?_⟩
    have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have h3 : (t * (x₀ : G) * t⁻¹)⁻¹ * x₀ = u := by
      have := congrArg Subtype.val heq
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hy, Subgroup.coe_inclusion] at this
      exact this
    have h4 : (x₀ : G)⁻¹ * t⁻¹ * x₀ = t⁻¹ * u := by
      calc (x₀ : G)⁻¹ * t⁻¹ * x₀ = t⁻¹ * ((t * (x₀ : G) * t⁻¹)⁻¹ * x₀) := by group
        _ = t⁻¹ * u := by rw [h3]
    rw [hinv] at h4
    exact h4

theorem tabAutCent_patA
    (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G)
    (hXq : CFSG.IsQuasisimple ↥X) (ht : t ∈ Subgroup.normalizer (X : Set G)) (ht2 : t * t = 1)
    (hcomm : ⁅X, Subgroup.zpowers t⁆ = X)
    (hK : K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)))
    (hpat : PatA X K t) (Y : Subgroup G) (hYn : Y ≤ Subgroup.normalizer (X : Set G))
    (hYc : Y ≤ Subgroup.centralizer (K : Set G)) :
    (Y ⊓ Subgroup.centralizer (X : Set G)).relIndex Y ≤ 2 :=
  (patA_main G X K t hXq ht ht2 hcomm hK hpat).1 Y hYn hYc

theorem tabConj_patA
    (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G)
    (hXq : CFSG.IsQuasisimple ↥X) (ht : t ∈ Subgroup.normalizer (X : Set G)) (ht2 : t * t = 1)
    (hcomm : ⁅X, Subgroup.zpowers t⁆ = X)
    (hK : K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)))
    (hpat : PatA X K t) (hZ : Subgroup.center ↥X = ⊥) :
    ∀ u ∈ K, u * u = 1 → ∃ x ∈ X, x⁻¹ * t * x = t * u :=
  (patA_main G X K t hXq ht ht2 hcomm hK hpat).2 hZ

end CFSG.QuasithinUnique.Id2519.Tab.L34

