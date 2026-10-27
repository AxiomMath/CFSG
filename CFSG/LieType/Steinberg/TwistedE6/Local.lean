module

public import CFSG.LieType.Steinberg.TwistedE6.Roots
public import CFSG.LieType.Steinberg.Minuscule.RankOne
public import CFSG.LieType.Steinberg.Minuscule.Unipotent
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123

public noncomputable section

namespace CFSG.LieType.Steinberg.TwistedE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule

abbrev nd (a : ℕ) (h : a < 6 := by decide) : Fin (Tag.rank .E6) := ⟨a, h⟩

variable {k : Type*} [Field k] (θ : k →+* k)

theorem sigma_xm_single (i : Fin (Tag.rank .E6)) (c : k) :
    sigma k θ (e6Data_valid.xm k (Pi.single i 1) c) =
      e6Data_valid.xm k (Pi.single (rhoPerm i) 1) (θ c) := by
  rw [sigma_xm θ (isRoot_single _ i), twistSign_single, Int.cast_one, one_mul, rho_single]

theorem sigma_xm_neg_single (i : Fin (Tag.rank .E6)) (c : k) :
    sigma k θ (e6Data_valid.xm k (-Pi.single i 1) c) =
      e6Data_valid.xm k (-Pi.single (rhoPerm i) 1) (θ c) := by
  rw [sigma_xm θ (isRoot_neg_single _ i), twistSign_neg_single, Int.cast_one, one_mul,
    rho_neg_single]

theorem sigma_nt (i : Fin (Tag.rank .E6)) (t : kˣ) :
    sigma k θ (e6Data_valid.nt k i t) = e6Data_valid.nt k (rhoPerm i) (Units.map θ t) := by
  simp only [MinData.Valid.nt, map_mul, sigma_xm_single, sigma_xm_neg_single, map_neg,
    Units.coe_map, MonoidHom.coe_ofClass]
  rfl

theorem sigma_nm (i : Fin (Tag.rank .E6)) :
    sigma k θ (e6Data_valid.nm k i) = e6Data_valid.nm k (rhoPerm i) := by
  rw [MinData.Valid.nm, sigma_nt, map_one]
  rfl

theorem sigma_hm (i : Fin (Tag.rank .E6)) (t : kˣ) :
    sigma k θ (e6Data_valid.hm k i t) = e6Data_valid.hm k (rhoPerm i) (Units.map θ t) := by
  rw [MinData.Valid.hm, map_mul, map_inv, sigma_nt, sigma_nt, map_one]
  rfl

theorem sigma_sigma (hθ : ∀ c, θ (θ c) = c) (g : e6Data_valid.minGroup k) :
    sigma k θ (sigma k θ g) = g := by
  have hle : e6Data_valid.minGroup k ≤ (MonoidHom.eqLocus ((sigma k θ).comp (sigma k θ))
      (MonoidHom.id _)).map (e6Data_valid.minGroup k).subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, c, rfl⟩
    refine ⟨e6Data_valid.xm k γ c, ?_, rfl⟩
    change sigma k θ (sigma k θ (e6Data_valid.xm k γ c)) = e6Data_valid.xm k γ c
    rw [sigma_xm θ hγ, sigma_xm θ (isRoot_rho hγ), rho_rho, twistSign_rho hγ, map_mul,
      map_intCast, hθ, ← mul_assoc]
    rcases twistSign_eq_one_or γ with h | h <;> simp [h]
  obtain ⟨g', hg', hgg'⟩ := hle g.2
  have : g' = g := Subtype.ext hgg'
  subst this
  exact hg'

theorem mem_fixedGroup {g : e6Data_valid.minGroup k} : g ∈ fixedGroup k θ ↔ sigma k θ g = g :=
  Iff.rfl

theorem not_isRoot_of_form {γ : Fin (Tag.rank .E6) → ℤ} (h : MinData.toWeight γ ⬝ᵥ γ ≠ 2) :
    ¬ IsRoot .E6 γ :=
  fun hr => h (form_self_root posDef_cartan_E6 hr)

theorem commute_xm {γ δ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (hδ : IsRoot .E6 δ)
    (hne : γ + δ ≠ 0) (hnr : ¬ IsRoot .E6 (γ + δ)) (c d : k) :
    Commute (e6Data_valid.xm k γ c) (e6Data_valid.xm k δ d) :=
  commutatorElement_eq_one_iff_commute.1 ((e6Data_valid.commutator_xm k hγ hδ hne).2 hnr c d)

theorem commute_xm_orbit {a b : Fin (Tag.rank .E6)}
    (hab : (a = (nd 2) ∧ b = (nd 4)) ∨ (a = (nd 0) ∧ b = (nd 5)))
    {s s' : ℤ} (hs : s = 1 ∨ s = -1) (hs' : s' = 1 ∨ s' = -1) (c d : k) :
    Commute (e6Data_valid.xm k (s • Pi.single a 1) c)
      (e6Data_valid.xm k (s' • Pi.single b 1) d) := by
  have hroot : ∀ (x : Fin (Tag.rank .E6)) (t : ℤ), (t = 1 ∨ t = -1) →
      IsRoot .E6 (t • Pi.single x 1) := fun x t ht => by
    rcases ht with rfl | rfl
    · rw [one_smul]; exact .basis x
    · rw [neg_one_smul]; exact isRoot_neg_single _ x
  refine commute_xm (hroot a s hs) (hroot b s' hs') ?_ (not_isRoot_of_form ?_) c d <;>
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hs with rfl | rfl <;>
    rcases hs' with rfl | rfl <;> decide

variable (k) in
@[expose] def nHatE : Fin (Tag.rank .F4) → e6Data_valid.minGroup k :=
  ![e6Data_valid.nm k (nd 1), e6Data_valid.nm k (nd 3),
    e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4),
    e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5)]

theorem nm_comm_24 : e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4) =
    e6Data_valid.nm k (nd 4) * e6Data_valid.nm k (nd 2) :=
  e6Data_valid.nm_comm k (by decide) (by decide)

theorem nm_comm_05 : e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5) =
    e6Data_valid.nm k (nd 5) * e6Data_valid.nm k (nd 0) :=
  e6Data_valid.nm_comm k (by decide) (by decide)

theorem sigma_nHatE (i : Fin (Tag.rank .F4)) : sigma k θ (nHatE k i) = nHatE k i := by
  fin_cases i
  · exact sigma_nm θ (nd 1)
  · exact sigma_nm θ (nd 3)
  · change sigma k θ (e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4)) = _
    rw [map_mul, sigma_nm, sigma_nm]
    exact nm_comm_24.symm
  · change sigma k θ (e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5)) = _
    rw [map_mul, sigma_nm, sigma_nm]
    exact nm_comm_05.symm

@[expose] def nHat (i : Fin (Tag.rank .F4)) : fixedGroup k θ := ⟨nHatE k i, sigma_nHatE θ i⟩

theorem nHat_val (i : Fin (Tag.rank .F4)) : (nHat θ i : e6Data_valid.minGroup k) = nHatE k i :=
  rfl

@[expose] def fixedUnits : Subgroup kˣ := MonoidHom.eqLocus (Units.map θ) (MonoidHom.id kˣ)

theorem mem_fixedUnits {t : kˣ} : t ∈ fixedUnits θ ↔ θ t = t := by
  change Units.map θ t = t ↔ _
  rw [Units.ext_iff, Units.coe_map]
  rfl

theorem hm_commute (a b : Fin (Tag.rank .E6)) (s t : kˣ) :
    Commute (e6Data_valid.hm k a s) (e6Data_valid.hm k b t) :=
  e6Data_valid.torus_commute k a b (e6Data_valid.hm_mem_torus k a s)
    (e6Data_valid.hm_mem_torus k b t)

@[expose] def hPairE (a b : Fin (Tag.rank .E6)) : kˣ →* e6Data_valid.minGroup k where
  toFun t := e6Data_valid.hm k a t * e6Data_valid.hm k b (Units.map θ t)
  map_one' := by rw [map_one, e6Data_valid.hm_one, e6Data_valid.hm_one, mul_one]
  map_mul' s t := by
    rw [map_mul, e6Data_valid.hm_mul, e6Data_valid.hm_mul, mul_assoc, mul_assoc,
      ← mul_assoc (e6Data_valid.hm k a t), (hm_commute a b t _).eq]
    group

@[expose] def hFixE (a : Fin (Tag.rank .E6)) : fixedUnits θ →* e6Data_valid.minGroup k :=
  (e6Data_valid.hHom k a).comp (fixedUnits θ).subtype

theorem units_map_map (hθ : ∀ c, θ (θ c) = c) (t : kˣ) :
    Units.map (θ : k →* k) (Units.map (θ : k →* k) t) = t :=
  Units.ext (by rw [Units.coe_map, Units.coe_map]; exact hθ _)

variable (k) in
@[expose] def hHatE : Fin (Tag.rank .F4) → Subgroup (e6Data_valid.minGroup k) :=
  ![(hFixE θ (nd 1)).range, (hFixE θ (nd 3)).range,
    (hPairE θ (nd 2) (nd 4)).range, (hPairE θ (nd 0) (nd 5)).range]

theorem hHatE_le_fixedGroup (hθ : ∀ c, θ (θ c) = c) (i : Fin (Tag.rank .F4)) :
    hHatE k θ i ≤ fixedGroup k θ := by
  fin_cases i
  · rintro _ ⟨t, rfl⟩
    change sigma k θ (e6Data_valid.hm k (nd 1) t) = e6Data_valid.hm k (nd 1) t
    rw [sigma_hm, show Units.map (θ : k →* k) (t : kˣ) = t from t.2]
    rfl
  · rintro _ ⟨t, rfl⟩
    change sigma k θ (e6Data_valid.hm k (nd 3) t) = e6Data_valid.hm k (nd 3) t
    rw [sigma_hm, show Units.map (θ : k →* k) (t : kˣ) = t from t.2]
    rfl
  · rintro _ ⟨t, rfl⟩
    change sigma k θ (e6Data_valid.hm k (nd 2) t * e6Data_valid.hm k (nd 4) _) = _
    rw [map_mul, sigma_hm, sigma_hm, units_map_map θ hθ]
    exact (hm_commute _ _ _ _).eq
  · rintro _ ⟨t, rfl⟩
    change sigma k θ (e6Data_valid.hm k (nd 0) t * e6Data_valid.hm k (nd 5) _) = _
    rw [map_mul, sigma_hm, sigma_hm, units_map_map θ hθ]
    exact (hm_commute _ _ _ _).eq

variable (k) in
@[expose] def hHat (i : Fin (Tag.rank .F4)) : Subgroup (fixedGroup k θ) :=
  (hHatE k θ i).subgroupOf (fixedGroup k θ)

theorem iSup_fibre {β : Fin (Tag.rank .F4) → ℤ} {α₀ : Fin (Tag.rank .E6) → ℤ}
    (hα₀ : IsRoot .E6 α₀) (hp : proj α₀ = β) :
    (⨆ α ∈ {α : Fin (Tag.rank .E6) → ℤ | IsRoot .E6 α},
      ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum orbitMap α = c • β), e6Data_valid.rootGroup k α) =
      e6Data_valid.rootGroup k α₀ ⊔ e6Data_valid.rootGroup k (rho α₀) := by
  refine le_antisymm (iSup₂_le fun α hα => iSup_le fun ⟨c, hc, hcα⟩ => ?_) (sup_le ?_ ?_)
  · rw [← proj_apply, ← hp] at hcα
    have hc1 := eq_one_of_proj_eq_nsmul hα hα₀ hc hcα
    rw [hc1, one_smul] at hcα
    rcases (proj_eq_proj_iff hα₀ hα).1 hcα.symm with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · exact le_iSup₂_of_le α₀ hα₀ (le_iSup_of_le ⟨1, one_pos, by rw [one_smul, ← hp]; rfl⟩ le_rfl)
  · refine le_iSup₂_of_le (rho α₀) (isRoot_rho hα₀) (le_iSup_of_le ⟨1, one_pos, ?_⟩ le_rfl)
    rw [one_smul, ← hp, ← proj_apply, proj_rho]

theorem mem_twistedRootGroup_iff {β : Fin (Tag.rank .F4) → ℤ} {α₀ : Fin (Tag.rank .E6) → ℤ}
    (hα₀ : IsRoot .E6 α₀) (hp : proj α₀ = β) (g : fixedGroup k θ) :
    g ∈ twistedRootGroup k θ β ↔
      (g : e6Data_valid.minGroup k) ∈ e6Data_valid.rootGroup k α₀ ⊔
        e6Data_valid.rootGroup k (rho α₀) := by
  rw [twistedRootGroup, Subgroup.mem_subgroupOf, twistedRootSubgroup, Subgroup.mem_inf,
    iSup_fibre hα₀ hp]
  exact and_iff_left g.2

theorem mem_sup_rootGroup_of_commute {α γ : Fin (Tag.rank .E6) → ℤ}
    (hcomm : ∀ c d : k, Commute (e6Data_valid.xm k α c) (e6Data_valid.xm k γ d))
    {g : e6Data_valid.minGroup k} :
    g ∈ e6Data_valid.rootGroup k α ⊔ e6Data_valid.rootGroup k γ ↔
      ∃ c d, g = e6Data_valid.xm k α c * e6Data_valid.xm k γ d := by
  constructor
  · intro hg
    let S : Subgroup (e6Data_valid.minGroup k) :=
      { carrier := {g | ∃ c d, g = e6Data_valid.xm k α c * e6Data_valid.xm k γ d}
        mul_mem' := by
          rintro _ _ ⟨c, d, rfl⟩ ⟨c', d', rfl⟩
          refine ⟨c + c', d + d', ?_⟩
          calc e6Data_valid.xm k α c * e6Data_valid.xm k γ d *
                (e6Data_valid.xm k α c' * e6Data_valid.xm k γ d') =
              e6Data_valid.xm k α c * (e6Data_valid.xm k γ d * e6Data_valid.xm k α c') *
                e6Data_valid.xm k γ d' := by group
            _ = e6Data_valid.xm k α c * (e6Data_valid.xm k α c' * e6Data_valid.xm k γ d) *
                e6Data_valid.xm k γ d' := by rw [(hcomm c' d).eq]
            _ = _ := by rw [e6Data_valid.xm_add, e6Data_valid.xm_add]; group
        one_mem' := ⟨0, 0, by rw [e6Data_valid.xm_zero, e6Data_valid.xm_zero, mul_one]⟩
        inv_mem' := by
          rintro _ ⟨c, d, rfl⟩
          refine ⟨-c, -d, ?_⟩
          rw [mul_inv_rev, e6Data_valid.xm_neg, e6Data_valid.xm_neg]
          exact ((hcomm (-c) (-d)).eq).symm }
    have hle : e6Data_valid.rootGroup k α ⊔ e6Data_valid.rootGroup k γ ≤ S := by
      refine sup_le ?_ ?_
      · rintro _ ⟨c, rfl⟩
        exact ⟨c.toAdd, 0, by rw [e6Data_valid.xm_zero, mul_one]; rfl⟩
      · rintro _ ⟨d, rfl⟩
        exact ⟨0, d.toAdd, by rw [e6Data_valid.xm_zero, one_mul]; rfl⟩
    exact hle hg
  · rintro ⟨c, d, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left (e6Data_valid.xm_mem_rootGroup k _ _))
      (Subgroup.mem_sup_right (e6Data_valid.xm_mem_rootGroup k _ _))

theorem xm_mul_xm_rho_inj {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hne : rho α ≠ α)
    {c d c' d' : k}
    (h : e6Data_valid.xm k α c * e6Data_valid.xm k (rho α) d =
      e6Data_valid.xm k α c' * e6Data_valid.xm k (rho α) d') : c = c' ∧ d = d' := by
  classical
  have hht : ht (rho α) = ht α := by rw [← ht_proj, proj_rho, ht_proj]
  have h0 : ht α ≠ 0 := hα.height_ne_zero
  set η : ℤ := if 0 < ht α then 1 else -1 with hη
  have hpos : 0 < η * ht α := by
    simp only [hη]
    split_ifs with h1
    · simpa using h1
    · omega
  have hinj := e6Data_valid.prodInjective posDef_cartan_E6 (k := k) η [α, rho α]
    (by simp [List.nodup_cons, Ne.symm hne])
    (by
      intro γ hγ
      rcases List.mem_pair.1 hγ with rfl | rfl
      · exact ⟨hα, hpos⟩
      · exact ⟨isRoot_rho hα, by rw [hht]; exact hpos⟩)
    (List.pairwise_pair.2 (by rw [hht]))
  let f : (Fin (Tag.rank .E6) → ℤ) → e6Data_valid.minGroup k := fun γ =>
    if γ = α then e6Data_valid.xm k α c else e6Data_valid.xm k (rho α) d
  let f' : (Fin (Tag.rank .E6) → ℤ) → e6Data_valid.minGroup k := fun γ =>
    if γ = α then e6Data_valid.xm k α c' else e6Data_valid.xm k (rho α) d'
  have hmem : ∀ (u v : k), ∀ γ ∈ [α, rho α], (fun γ : Fin (Tag.rank .E6) → ℤ =>
      if γ = α then e6Data_valid.xm k α u else e6Data_valid.xm k (rho α) v) γ ∈
        e6Data_valid.rootGroup k γ := by
    intro u v γ hγ
    rcases List.mem_pair.1 hγ with rfl | rfl
    · simp only [ite_true]
      exact e6Data_valid.xm_mem_rootGroup k _ _
    · simp only [hne, ite_false]
      exact e6Data_valid.xm_mem_rootGroup k _ _
  have hprod : ([α, rho α].map f).prod = ([α, rho α].map f').prod := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, f, f', hne,
      ite_true, ite_false]
    exact h
  have e1 := hinj f f' (hmem c d) (hmem c' d') hprod α (by simp)
  have e2 := hinj f f' (hmem c d) (hmem c' d') hprod (rho α) (by simp)
  simp only [f, f', hne, ite_true, ite_false] at e1 e2
  exact ⟨e6Data_valid.xm_injective k hα e1, e6Data_valid.xm_injective k (isRoot_rho hα) e2⟩

theorem commute_xm_rho {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hne : rho α ≠ α)
    (c d : k) : Commute (e6Data_valid.xm k α c) (e6Data_valid.xm k (rho α) d) :=
  commute_xm hα (isRoot_rho hα) (add_rho_ne_zero hα hne) (not_isRoot_add_rho hα hne) c d

theorem mem_twistedRootGroup_iff_of_fixed {β : Fin (Tag.rank .F4) → ℤ}
    {α₀ : Fin (Tag.rank .E6) → ℤ} (hα₀ : IsRoot .E6 α₀) (hp : proj α₀ = β)
    (hfix : rho α₀ = α₀) (g : fixedGroup k θ) :
    g ∈ twistedRootGroup k θ β ↔
      ∃ c, θ c = c ∧ (g : e6Data_valid.minGroup k) = e6Data_valid.xm k α₀ c := by
  rw [mem_twistedRootGroup_iff θ hα₀ hp, hfix, sup_idem, MinData.Valid.mem_rootGroup]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_, hc.symm⟩
    have h := g.2
    rw [mem_fixedGroup, ← hc, sigma_xm θ hα₀, hfix, twistSign_of_rho_eq hα₀ hfix, Int.cast_one,
      one_mul] at h
    exact e6Data_valid.xm_injective k hα₀ h
  · rintro ⟨c, -, hc⟩
    exact ⟨c, hc.symm⟩

theorem mem_twistedRootGroup_iff_of_pair {β : Fin (Tag.rank .F4) → ℤ}
    {α₀ : Fin (Tag.rank .E6) → ℤ} (hα₀ : IsRoot .E6 α₀) (hp : proj α₀ = β)
    (hne : rho α₀ ≠ α₀) (g : fixedGroup k θ) :
    g ∈ twistedRootGroup k θ β ↔ ∃ c, (g : e6Data_valid.minGroup k) =
      e6Data_valid.xm k α₀ c * e6Data_valid.xm k (rho α₀) ((twistSign α₀ : k) * θ c) := by
  rw [mem_twistedRootGroup_iff θ hα₀ hp, mem_sup_rootGroup_of_commute (commute_xm_rho hα₀ hne)]
  constructor
  · rintro ⟨c, d, hcd⟩
    refine ⟨c, ?_⟩
    have h := g.2
    rw [mem_fixedGroup, hcd, map_mul, sigma_xm θ hα₀, sigma_xm θ (isRoot_rho hα₀), rho_rho,
      twistSign_rho hα₀, ← (commute_xm_rho hα₀ hne _ _).eq] at h
    obtain ⟨-, hd⟩ := xm_mul_xm_rho_inj hα₀ hne h
    rw [hcd, ← hd]
  · rintro ⟨c, hc⟩
    exact ⟨c, _, hc⟩

@[expose] def xFixed {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (hfix : rho γ = γ) (c : k)
    (hc : θ c = c) : fixedGroup k θ :=
  ⟨e6Data_valid.xm k γ c, by
    rw [mem_fixedGroup, sigma_xm θ hγ, hfix, twistSign_of_rho_eq hγ hfix, Int.cast_one, one_mul,
      hc]⟩

@[expose] def xPair (hθ : ∀ c, θ (θ c) = c) {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (hne : rho γ ≠ γ) (c : k) : fixedGroup k θ :=
  ⟨e6Data_valid.xm k γ c * e6Data_valid.xm k (rho γ) ((twistSign γ : k) * θ c), by
    rw [mem_fixedGroup, map_mul, sigma_xm θ hγ, sigma_xm θ (isRoot_rho hγ), rho_rho,
      twistSign_rho hγ, map_mul, map_intCast, hθ, ← mul_assoc,
      ← (commute_xm_rho hγ hne _ _).eq]
    congr 2
    rcases twistSign_eq_one_or γ with h | h <;> simp [h]⟩

theorem xFixed_val {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (hfix : rho γ = γ) (c : k)
    (hc : θ c = c) : (xFixed θ hγ hfix c hc : e6Data_valid.minGroup k) = e6Data_valid.xm k γ c :=
  rfl

theorem xPair_val (hθ : ∀ c, θ (θ c) = c) {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (hne : rho γ ≠ γ) (c : k) : (xPair θ hθ hγ hne c : e6Data_valid.minGroup k) =
      e6Data_valid.xm k γ c * e6Data_valid.xm k (rho γ) ((twistSign γ : k) * θ c) :=
  rfl

theorem xFixed_mem {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (hfix : rho γ = γ) (c : k)
    (hc : θ c = c) : xFixed θ hγ hfix c hc ∈ twistedRootGroup k θ (proj γ) :=
  (mem_twistedRootGroup_iff_of_fixed θ hγ rfl hfix _).2 ⟨c, hc, rfl⟩

theorem xPair_mem (hθ : ∀ c, θ (θ c) = c) {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (hne : rho γ ≠ γ) (c : k) : xPair θ hθ hγ hne c ∈ twistedRootGroup k θ (proj γ) :=
  (mem_twistedRootGroup_iff_of_pair θ hγ rfl hne _).2 ⟨c, rfl⟩

abbrev nf (i : ℕ) (h : i < 4 := by decide) : Fin (Tag.rank .F4) := ⟨i, h⟩

theorem proj_single (a : Fin (Tag.rank .E6)) : proj (Pi.single a 1) = Pi.single (orbitMap a) 1 := by
  revert a
  decide

theorem proj_neg_single (a : Fin (Tag.rank .E6)) :
    proj (-Pi.single a 1) = -Pi.single (orbitMap a) 1 := by
  rw [map_neg, proj_single]

theorem mul_mul_mul_rearrange {G : Type*} [Group G] {p q r p' q' r' : G} (h1 : Commute q p')
    (h2 : Commute r p') (h3 : Commute r q') :
    p * q * r * (p' * q' * r') = p * p' * (q * q') * (r * r') := by
  calc p * q * r * (p' * q' * r') = p * q * (r * p') * q' * r' := by group
    _ = p * q * (p' * r) * q' * r' := by rw [h2.eq]
    _ = p * (q * p') * r * q' * r' := by group
    _ = p * (p' * q) * r * q' * r' := by rw [h1.eq]
    _ = p * p' * q * (r * q') * r' := by group
    _ = p * p' * q * (q' * r) * r' := by rw [h3.eq]
    _ = _ := by group

theorem nt_mul_nt_orbit {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) (t u : kˣ) :
    e6Data_valid.nt k a t * e6Data_valid.nt k b u =
      e6Data_valid.xm k (Pi.single a 1) t * e6Data_valid.xm k (Pi.single b 1) u *
        (e6Data_valid.xm k (-Pi.single a 1) (-((t⁻¹ : kˣ) : k)) *
          e6Data_valid.xm k (-Pi.single b 1) (-((u⁻¹ : kˣ) : k))) *
        (e6Data_valid.xm k (Pi.single a 1) t * e6Data_valid.xm k (Pi.single b 1) u) := by
  have hc := fun (s s' : ℤ) (hs : s = 1 ∨ s = -1) (hs' : s' = 1 ∨ s' = -1) (c d : k) =>
    commute_xm_orbit (k := k) hab hs hs' c d
  have p1 := hc (-1) 1 (Or.inr rfl) (Or.inl rfl) (-((t⁻¹ : kˣ) : k)) u
  have p2 := hc 1 1 (Or.inl rfl) (Or.inl rfl) t u
  have p3 := hc 1 (-1) (Or.inl rfl) (Or.inr rfl) t (-((u⁻¹ : kˣ) : k))
  simp only [neg_one_smul, one_smul] at p1 p2 p3
  exact mul_mul_mul_rearrange p1 p2 p3

theorem commute_nt_orbit {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) (t u : kˣ) :
    Commute (e6Data_valid.nt k a t) (e6Data_valid.nt k b u) := by
  have key := fun (s s' : ℤ) (hs : s = 1 ∨ s = -1) (hs' : s' = 1 ∨ s' = -1) (c d : k) =>
    commute_xm_orbit (k := k) hab hs hs' c d
  have pp := key 1 1 (Or.inl rfl) (Or.inl rfl)
  have pn := key 1 (-1) (Or.inl rfl) (Or.inr rfl)
  have np := key (-1) 1 (Or.inr rfl) (Or.inl rfl)
  have nn := key (-1) (-1) (Or.inr rfl) (Or.inr rfl)
  simp only [one_smul, neg_one_smul] at pp pn np nn
  have hp : ∀ c, Commute (e6Data_valid.xm k (Pi.single a 1) c) (e6Data_valid.nt k b u) :=
    fun c => ((pp c _).mul_right (pn c _)).mul_right (pp c _)
  have hn : ∀ c, Commute (e6Data_valid.xm k (-Pi.single a 1) c) (e6Data_valid.nt k b u) :=
    fun c => ((np c _).mul_right (nn c _)).mul_right (np c _)
  exact ((hp _).mul_left (hn _)).mul_left (hp _)

open CFSG.LieType.CurtisTits in
theorem exists_nt_fixed {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a) {t : kˣ} (ht : θ t = t) :
    ∃ g ∈ rankOne (twistedRootGroup k θ) (orbitMap a),
      (g : e6Data_valid.minGroup k) = e6Data_valid.nt k a t := by
  have h1 : rho (Pi.single a 1) = Pi.single a 1 := by rw [rho_single, ha]
  have h2 : rho (-Pi.single a 1) = -Pi.single a 1 := by rw [rho_neg_single, ha]
  have hc : θ (-((t⁻¹ : kˣ) : k)) = -((t⁻¹ : kˣ) : k) := by
    rw [map_neg, Units.val_inv_eq_inv_val, map_inv₀, ht]
  have hx := xFixed_mem θ (isRoot_single _ a) h1 t ht
  have hy := xFixed_mem θ (isRoot_neg_single _ a) h2 _ hc
  rw [proj_single] at hx
  rw [proj_neg_single] at hy
  exact ⟨_ * _ * _, mul_mem (mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy))
    (Subgroup.mem_sup_left hx), rfl⟩

open CFSG.LieType.CurtisTits in
theorem exists_nt_pair (hθ : ∀ c, θ (θ c) = c) {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) (t : kˣ) :
    ∃ g ∈ rankOne (twistedRootGroup k θ) (orbitMap a),
      (g : e6Data_valid.minGroup k) =
        e6Data_valid.nt k a t * e6Data_valid.nt k b (Units.map θ t) := by
  have hρ : rhoPerm a = b := by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have h1 : rho (Pi.single a 1) ≠ Pi.single a 1 := by
    rw [rho_single, hρ]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have h2 : rho (-Pi.single a 1) ≠ -Pi.single a 1 := by
    rw [rho_neg_single, hρ]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hx := xPair_mem θ hθ (isRoot_single _ a) h1 t
  have hy := xPair_mem θ hθ (isRoot_neg_single _ a) h2 (-((t⁻¹ : kˣ) : k))
  rw [proj_single] at hx
  rw [proj_neg_single] at hy
  refine ⟨_ * _ * _, mul_mem (mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy))
    (Subgroup.mem_sup_left hx), ?_⟩
  simp only [nt_mul_nt_orbit hab, Subgroup.coe_mul, xPair_val, rho_single, rho_neg_single, hρ,
    twistSign_single, twistSign_neg_single, Int.cast_one, one_mul, map_neg, Units.coe_map,
    Units.coe_map_inv, MonoidHom.coe_ofClass]

open CFSG.LieType.CurtisTits in
theorem exists_hm_fixed {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a) {t : kˣ} (ht : θ t = t) :
    ∃ g ∈ rankOne (twistedRootGroup k θ) (orbitMap a),
      (g : e6Data_valid.minGroup k) = e6Data_valid.hm k a t := by
  obtain ⟨g₁, h₁, e₁⟩ := exists_nt_fixed θ ha ht
  obtain ⟨g₂, h₂, e₂⟩ := exists_nt_fixed θ ha (t := 1) (by rw [Units.val_one, map_one])
  exact ⟨g₁ * g₂⁻¹, mul_mem h₁ (inv_mem h₂), by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, e₁, e₂]
    rfl⟩

open CFSG.LieType.CurtisTits in
theorem exists_hm_pair (hθ : ∀ c, θ (θ c) = c) {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) (t : kˣ) :
    ∃ g ∈ rankOne (twistedRootGroup k θ) (orbitMap a),
      (g : e6Data_valid.minGroup k) =
        e6Data_valid.hm k a t * e6Data_valid.hm k b (Units.map θ t) := by
  obtain ⟨g₁, h₁, e₁⟩ := exists_nt_pair θ hθ hab t
  obtain ⟨g₂, h₂, e₂⟩ := exists_nt_pair θ hθ hab 1
  refine ⟨g₁ * g₂⁻¹, mul_mem h₁ (inv_mem h₂), ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv, e₁, e₂, map_one]
  simp only [MinData.Valid.hm]
  have hc : Commute (e6Data_valid.nt k a 1)⁻¹
      (e6Data_valid.nt k b (Units.map θ t) * (e6Data_valid.nt k b 1)⁻¹) :=
    ((commute_nt_orbit hab 1 _).mul_right (commute_nt_orbit hab 1 1).inv_right).inv_left
  calc e6Data_valid.nt k a t * e6Data_valid.nt k b (Units.map θ t) *
        (e6Data_valid.nt k a 1 * e6Data_valid.nt k b 1)⁻¹ =
      e6Data_valid.nt k a t * ((e6Data_valid.nt k b (Units.map θ t) *
        (e6Data_valid.nt k b 1)⁻¹) * (e6Data_valid.nt k a 1)⁻¹) := by group
    _ = _ := by rw [← hc.eq]; group

open CFSG.LieType.CurtisTits in
theorem nHat_mem_rankOne (hθ : ∀ c, θ (θ c) = c) (i : Fin (Tag.rank .F4)) :
    nHat θ i ∈ rankOne (twistedRootGroup k θ) i := by
  have h1 : θ ((1 : kˣ) : k) = ((1 : kˣ) : k) := by rw [Units.val_one, map_one]
  fin_cases i
  · obtain ⟨g, hg, e⟩ := exists_nt_fixed θ (a := nd 1) rfl h1
    have he : nHat θ (nf 0) = g := Subtype.ext e.symm
    rw [← he] at hg
    exact hg
  · obtain ⟨g, hg, e⟩ := exists_nt_fixed θ (a := nd 3) rfl h1
    have he : nHat θ (nf 1) = g := Subtype.ext e.symm
    rw [← he] at hg
    exact hg
  · obtain ⟨g, hg, e⟩ := exists_nt_pair θ hθ (Or.inl ⟨rfl, rfl⟩) 1
    rw [map_one] at e
    have he : nHat θ (nf 2) = g := Subtype.ext e.symm
    rw [← he] at hg
    exact hg
  · obtain ⟨g, hg, e⟩ := exists_nt_pair θ hθ (Or.inr ⟨rfl, rfl⟩) 1
    rw [map_one] at e
    have he : nHat θ (nf 3) = g := Subtype.ext e.symm
    rw [← he] at hg
    exact hg

open CFSG.LieType.CurtisTits in
theorem hHat_le_rankOne (hθ : ∀ c, θ (θ c) = c) (i : Fin (Tag.rank .F4)) :
    hHat k θ i ≤ rankOne (twistedRootGroup k θ) i := by
  intro g hg
  rw [hHat, Subgroup.mem_subgroupOf] at hg
  fin_cases i
  · obtain ⟨t, ht⟩ := hg
    obtain ⟨g', hg', e⟩ := exists_hm_fixed θ (a := nd 1) rfl ((mem_fixedUnits θ).1 t.2)
    rwa [show g' = g from Subtype.ext (e.trans ht)] at hg'
  · obtain ⟨t, ht⟩ := hg
    obtain ⟨g', hg', e⟩ := exists_hm_fixed θ (a := nd 3) rfl ((mem_fixedUnits θ).1 t.2)
    rwa [show g' = g from Subtype.ext (e.trans ht)] at hg'
  · obtain ⟨t, ht⟩ := hg
    obtain ⟨g', hg', e⟩ := exists_hm_pair θ hθ (Or.inl ⟨rfl, rfl⟩) t
    rwa [show g' = g from Subtype.ext (e.trans ht)] at hg'
  · obtain ⟨t, ht⟩ := hg
    obtain ⟨g', hg', e⟩ := exists_hm_pair θ hθ (Or.inr ⟨rfl, rfl⟩) t
    rwa [show g' = g from Subtype.ext (e.trans ht)] at hg'

end CFSG.LieType.Steinberg.TwistedE6
