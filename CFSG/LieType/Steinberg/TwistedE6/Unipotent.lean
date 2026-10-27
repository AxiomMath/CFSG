module

public import CFSG.LieType.Steinberg.TwistedE6.Weyl
public import CFSG.LieType.Steinberg.Extras
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123

public noncomputable section

namespace CFSG.LieType.Steinberg.TwistedE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.CurtisTits

theorem list_prod_flatMap {M α : Type*} [Monoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).prod = (l.map fun a => (f a).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, List.prod_append, ih, List.map_cons, List.prod_cons]

theorem prodInjectiveFor_of_flatMap {K K' : Type*} [Group K] [Group K'] {ι κ : Type*}
    (π : K' →* K) (hπ : Function.Injective π) {X : (ι → ℤ) → Subgroup K}
    {Y : (κ → ℤ) → Subgroup K'} {L : List (κ → ℤ)} {F : (κ → ℤ) → List (ι → ℤ)}
    (hdec : ∀ β ∈ L, ∀ y ∈ Y β, ∃ φ : (ι → ℤ) → K, (∀ α ∈ F β, φ α ∈ X α) ∧
      π y = ((F β).map φ).prod)
    (hnd : (L.flatMap F).Nodup) (hinj : ProdInjectiveFor X (L.flatMap F)) :
    ProdInjectiveFor Y L := by
  classical
  have : Std.Symm (Function.onFun List.Disjoint F) := ⟨fun _ _ h => List.Disjoint.symm h⟩
  have hdisj : ∀ β ∈ L, ∀ β' ∈ L, ∀ α ∈ F β, α ∈ F β' → β = β' := by
    intro β hβ β' hβ' α h h'
    by_contra hne
    exact (List.nodup_flatMap.1 hnd).2.forall hβ hβ' hne h h'
  have key : ∀ f : (κ → ℤ) → K', (∀ β ∈ L, f β ∈ Y β) → ∃ Φ : (ι → ℤ) → K,
      (∀ α ∈ L.flatMap F, Φ α ∈ X α) ∧ ∀ β ∈ L, π (f β) = ((F β).map Φ).prod := by
    intro f hf
    choose φ hφ hφe using fun β (hβ : β ∈ L) => hdec β hβ (f β) (hf β hβ)
    let owner : (ι → ℤ) → (κ → ℤ) := fun α => if h : ∃ β ∈ L, α ∈ F β then h.choose else 0
    have howner : ∀ β ∈ L, ∀ α ∈ F β, owner α = β := by
      intro β hβ α hα
      have h : ∃ β ∈ L, α ∈ F β := ⟨β, hβ, hα⟩
      simp only [owner, dite_eq_left h]
      exact hdisj _ h.choose_spec.1 β hβ α h.choose_spec.2 hα
    let φ' : (κ → ℤ) → (ι → ℤ) → K := fun β α => if hβ : β ∈ L then φ β hβ α else 1
    have hφ' : ∀ β (hβ : β ∈ L) α, φ' β α = φ β hβ α := fun β hβ α => dite_eq_left hβ
    refine ⟨fun α => φ' (owner α) α, fun α hα => ?_, fun β hβ => ?_⟩
    · obtain ⟨β, hβ, hαβ⟩ := List.mem_flatMap.1 hα
      simp only [howner β hβ α hαβ, hφ' β hβ]
      exact hφ β hβ α hαβ
    · rw [hφe β hβ]
      congr 1
      refine List.map_congr_left fun α hα => ?_
      simp only [howner β hβ α hα, hφ' β hβ]
  intro f g hf hg hprod
  obtain ⟨Φ, hΦ, hΦe⟩ := key f hf
  obtain ⟨Ψ, hΨ, hΨe⟩ := key g hg
  have hprod' : ((L.flatMap F).map Φ).prod = ((L.flatMap F).map Ψ).prod := by
    calc ((L.flatMap F).map Φ).prod = (L.map fun β => ((F β).map Φ).prod).prod := by
          rw [List.map_flatMap, list_prod_flatMap]
      _ = (L.map fun β => π (f β)).prod := by
          rw [List.map_congr_left fun β hβ => (hΦe β hβ).symm]
      _ = π (L.map f).prod := by rw [map_list_prod, List.map_map]; rfl
      _ = π (L.map g).prod := by rw [hprod]
      _ = (L.map fun β => π (g β)).prod := by rw [map_list_prod, List.map_map]; rfl
      _ = (L.map fun β => ((F β).map Ψ).prod).prod := by
          rw [List.map_congr_left fun β hβ => hΨe β hβ]
      _ = ((L.flatMap F).map Ψ).prod := by rw [List.map_flatMap, list_prod_flatMap]
  have hall := hinj Φ Ψ hΦ hΨ hprod'
  intro β hβ
  apply hπ
  rw [hΦe β hβ, hΨe β hβ]
  congr 1
  exact List.map_congr_left fun α hα => hall α (List.mem_flatMap.2 ⟨β, hβ, hα⟩)

open _root_.Classical in
@[expose] def liftRoot (β : Fin (Tag.rank .F4) → ℤ) : Fin (Tag.rank .E6) → ℤ :=
  if h : ∃ α, IsRoot .E6 α ∧ proj α = β then h.choose else 0

theorem liftRoot_spec {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β) :
    IsRoot .E6 (liftRoot β) ∧ proj (liftRoot β) = β := by
  classical
  have h := exists_proj_eq hβ
  rw [liftRoot, dite_eq_left h]
  exact h.choose_spec

open _root_.Classical in
@[expose] def fibreList (β : Fin (Tag.rank .F4) → ℤ) : List (Fin (Tag.rank .E6) → ℤ) :=
  if rho (liftRoot β) = liftRoot β then [liftRoot β] else [liftRoot β, rho (liftRoot β)]

theorem mem_fibreList {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β)
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : γ ∈ fibreList β) : IsRoot .E6 γ ∧ proj γ = β := by
  obtain ⟨hα, hp⟩ := liftRoot_spec hβ
  unfold fibreList at hγ
  split_ifs at hγ with h
  · rw [List.mem_singleton] at hγ
    subst hγ
    exact ⟨hα, hp⟩
  · rcases List.mem_pair.1 hγ with rfl | rfl
    · exact ⟨hα, hp⟩
    · exact ⟨isRoot_rho hα, by rw [proj_rho, hp]⟩

theorem nodup_fibreList (β : Fin (Tag.rank .F4) → ℤ) : (fibreList β).Nodup := by
  unfold fibreList
  split_ifs with h
  · exact List.nodup_singleton _
  · simp [List.nodup_cons, Ne.symm h]

variable {k : Type*} [Field k] (θ : k →+* k)

theorem exists_decomp_fibreList {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β)
    {y : fixedGroup k θ} (hy : y ∈ twistedRootGroup k θ β) :
    ∃ φ : (Fin (Tag.rank .E6) → ℤ) → e6Data_valid.minGroup k,
      (∀ α ∈ fibreList β, φ α ∈ e6Data_valid.rootGroup k α) ∧
        (y : e6Data_valid.minGroup k) = ((fibreList β).map φ).prod := by
  obtain ⟨hα, hp⟩ := liftRoot_spec hβ
  unfold fibreList
  split_ifs with h
  · obtain ⟨c, -, hc⟩ := (mem_twistedRootGroup_iff_of_fixed θ hα hp h y).1 hy
    refine ⟨fun _ => e6Data_valid.xm k (liftRoot β) c, fun α hα' => ?_, ?_⟩
    · rw [List.mem_singleton] at hα'
      subst hα'
      exact e6Data_valid.xm_mem_rootGroup k _ _
    · rw [List.map_singleton, List.prod_singleton, hc]
  · obtain ⟨c, hc⟩ := (mem_twistedRootGroup_iff_of_pair θ hα hp h y).1 hy
    refine ⟨fun γ => if γ = liftRoot β then e6Data_valid.xm k (liftRoot β) c
      else e6Data_valid.xm k (rho (liftRoot β)) ((twistSign (liftRoot β) : k) * θ c),
      fun γ hγ => ?_, ?_⟩
    · rcases List.mem_pair.1 hγ with rfl | rfl
      · simp only [ite_true]
        exact e6Data_valid.xm_mem_rootGroup k _ _
      · simp only [h, ite_false]
        exact e6Data_valid.xm_mem_rootGroup k _ _
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ite_true,
        h, ite_false]
      exact hc

theorem prodInjective_twisted (η : ℤ) (L : List (Fin (Tag.rank .F4) → ℤ)) (hnd : L.Nodup)
    (hL : ∀ β ∈ L, IsRoot .F4 β ∧ 0 < η * ht β)
    (hsort : L.Pairwise fun β δ => η * ht β ≤ η * ht δ) :
    ProdInjectiveFor (twistedRootGroup k θ) L := by
  have hmem : ∀ β ∈ L, ∀ γ ∈ fibreList β, IsRoot .E6 γ ∧ proj γ = β :=
    fun β hβ γ hγ => mem_fibreList (hL β hβ).1 hγ
  have hht : ∀ β ∈ L, ∀ γ ∈ fibreList β, ht γ = ht β := fun β hβ γ hγ => by
    rw [← ht_proj, (hmem β hβ γ hγ).2]
  have hnd' : (L.flatMap fibreList).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun β _ => nodup_fibreList β, hnd.imp_of_mem fun {β δ} hβ hδ hne => ?_⟩
    intro γ h1 h2
    exact hne ((hmem β hβ γ h1).2.symm.trans (hmem δ hδ γ h2).2)
  refine prodInjectiveFor_of_flatMap (fixedGroup k θ).subtype Subtype.val_injective
    (fun β hβ y hy => exists_decomp_fibreList θ (hL β hβ).1 hy) hnd' ?_
  refine e6Data_valid.prodInjective posDef_cartan_E6 η _ hnd' (fun γ hγ => ?_) ?_
  · obtain ⟨β, hβ, hγβ⟩ := List.mem_flatMap.1 hγ
    exact ⟨(hmem β hβ γ hγβ).1, by rw [hht β hβ γ hγβ]; exact (hL β hβ).2⟩
  · rw [List.pairwise_flatMap]
    refine ⟨fun β hβ => (nodup_fibreList β).imp_of_mem fun {γ δ} hγ hδ _ => ?_,
      hsort.imp_of_mem fun {β δ} hβ hδ h => fun x hx y hy => ?_⟩
    · rw [hht β hβ γ hγ, hht β hβ δ hδ]
    · rw [hht β hβ x hx, hht δ hδ y hy]
      exact h

theorem iSup_twistedRootGroup_le (P : ℤ → Prop) :
    (⨆ β ∈ {β : Fin (Tag.rank .F4) → ℤ | IsRoot .F4 β ∧ P (ht β)}, twistedRootGroup k θ β) ≤
      (⨆ γ ∈ {γ : Fin (Tag.rank .E6) → ℤ | IsRoot .E6 γ ∧ P (ht γ)},
        e6Data_valid.rootGroup k γ).comap (fixedGroup k θ).subtype := by
  refine iSup₂_le fun β hβ x hx => ?_
  obtain ⟨α, hα, hp⟩ := exists_proj_eq hβ.1
  rw [mem_twistedRootGroup_iff θ hα hp] at hx
  rw [Subgroup.mem_comap, Subgroup.coe_subtype]
  have h1 : P (ht α) := by rw [← ht_proj, hp]; exact hβ.2
  have h2 : P (ht (rho α)) := by rw [← ht_proj, proj_rho, hp]; exact hβ.2
  exact sup_le (le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ : Fin (Tag.rank .E6) → ℤ |
      IsRoot .E6 γ ∧ P (ht γ)}) => e6Data_valid.rootGroup k γ) α ⟨hα, h1⟩ le_rfl)
    (le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ : Fin (Tag.rank .E6) → ℤ |
      IsRoot .E6 γ ∧ P (ht γ)}) => e6Data_valid.rootGroup k γ) (rho α) ⟨isRoot_rho hα, h2⟩
        le_rfl) hx

theorem posPart_inf_negPart_twisted :
    (⨆ β ∈ {β : Fin (Tag.rank .F4) → ℤ | IsRoot .F4 β ∧ 0 < ht β}, twistedRootGroup k θ β) ⊓
      (⨆ β ∈ {β : Fin (Tag.rank .F4) → ℤ | IsRoot .F4 β ∧ ht β < 0}, twistedRootGroup k θ β) =
        ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_inf] at hg
  have h1 : (g : e6Data_valid.minGroup k) ∈
      ⨆ γ ∈ {γ : Fin (Tag.rank .E6) → ℤ | IsRoot .E6 γ ∧ 0 < ht γ}, e6Data_valid.rootGroup k γ :=
    iSup_twistedRootGroup_le θ (fun h => 0 < h) hg.1
  have h2 : (g : e6Data_valid.minGroup k) ∈
      ⨆ γ ∈ {γ : Fin (Tag.rank .E6) → ℤ | IsRoot .E6 γ ∧ ht γ < 0}, e6Data_valid.rootGroup k γ :=
    iSup_twistedRootGroup_le θ (fun h => h < 0) hg.2
  have h := Subgroup.mem_inf.2 ⟨h1, h2⟩
  rw [e6Data_valid.posPart_inf_negPart k, Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.2 (Subtype.ext h)

theorem torus_inf_posPart_twisted :
    (⨆ i, hHat k θ i) ⊓
      (⨆ β ∈ {β : Fin (Tag.rank .F4) → ℤ | IsRoot .F4 β ∧ 0 < ht β}, twistedRootGroup k θ β) =
        ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_inf] at hg
  have hle : (⨆ i, hHat k θ i) ≤
      (⨆ a, e6Data_valid.torus k a).comap (fixedGroup k θ).subtype := iSup_le fun i x hx => by
    rw [hHat, Subgroup.mem_subgroupOf] at hx
    exact hHatE_le_iSup_torus θ i hx
  have h1 : (g : e6Data_valid.minGroup k) ∈ ⨆ a, e6Data_valid.torus k a := hle hg.1
  have h2 : (g : e6Data_valid.minGroup k) ∈
      ⨆ γ ∈ {γ : Fin (Tag.rank .E6) → ℤ | IsRoot .E6 γ ∧ 0 < ht γ}, e6Data_valid.rootGroup k γ :=
    iSup_twistedRootGroup_le θ (fun h => 0 < h) hg.2
  have h := Subgroup.mem_inf.2 ⟨h1, h2⟩
  rw [e6Data_valid.torus_inf_posPart k, Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.2 (Subtype.ext h)

theorem hHat_commute (hθ : ∀ c, θ (θ c) = c) {i j : Fin (Tag.rank .F4)} {h h' : fixedGroup k θ}
    (hh : h ∈ hHat k θ i) (hh' : h' ∈ hHat k θ j) : Commute h h' := by
  rw [hHat, Subgroup.mem_subgroupOf] at hh hh'
  obtain ⟨u, -, hu⟩ := exists_torusHom_of_mem_hHatE θ hθ hh
  obtain ⟨u', -, hu'⟩ := exists_torusHom_of_mem_hHatE θ hθ hh'
  refine Subtype.ext ?_
  change (h : e6Data_valid.minGroup k) * h' = h' * h
  rw [← hu, ← hu', ← map_mul, ← map_mul, mul_comm]

variable (k) in
@[expose] def diagHom : (Fin (Tag.rank .E6) → kˣ) →* Module.End k (Fin e6Data.d →₀ k) where
  toFun u := diagOp fun a => ((Additive.toMul (MinData.Valid.charHom k u (e6Data.wt a)) : kˣ) : k)
  map_one' := by
    rw [← diagOp_one]
    congr 1
    funext a
    simp [MinData.Valid.charHom_apply]
  map_mul' u v := by
    rw [diagOp_mul]
    congr 1
    funext a
    simp [MinData.Valid.charHom_apply, mul_zpow, Finset.prod_mul_distrib]

theorem diagHom_apply (u : Fin (Tag.rank .E6) → kˣ) :
    diagHom k u =
      diagOp fun a => ((Additive.toMul (MinData.Valid.charHom k u (e6Data.wt a)) : kˣ) : k) :=
  rfl

theorem endo_torusHom_mulSingle (c : Fin (Tag.rank .E6)) (t : kˣ) :
    e6Data_valid.endo k (torusHom k (Pi.mulSingle c t)) = diagHom k (Pi.mulSingle c t) := by
  rw [diagHom_apply, torusHom_mulSingle, e6Data_valid.endo_hm, MinData.hDiag]
  congr 1
  funext a
  rw [MinData.Valid.charHom_apply, Finset.prod_eq_single c (fun b _ hb => by
    rw [Pi.mulSingle_eq_of_ne hb, one_zpow]) (by simp), Pi.mulSingle_eq_same]

theorem endo_torusHom (u : Fin (Tag.rank .E6) → kˣ) :
    e6Data_valid.endo k (torusHom k u) = diagHom k u := by
  have h : (Units.coeHom _).comp ((e6Data_valid.minGroup k).subtype.comp (torusHom k)) =
      diagHom k := MonoidHom.pi_ext fun c t => by
    simp only [MonoidHom.comp_apply, Units.coeHom_apply, Subgroup.coe_subtype]
    exact endo_torusHom_mulSingle c t
  have := DFunLike.congr_fun h u
  simp only [MonoidHom.comp_apply, Units.coeHom_apply, Subgroup.coe_subtype] at this
  exact this

theorem eq_one_of_torusHom_mem {u : Fin (Tag.rank .E6) → kˣ} {a : Fin (Tag.rank .E6)}
    (h : torusHom k u ∈ ⨆ (c) (_ : c ≠ a), e6Data_valid.torus k c) : u a = 1 := by
  obtain ⟨u', hu', he⟩ := e6Data_valid.exists_char_of_mem k h
  rw [endo_torusHom, diagHom_apply] at he
  have hval : ∀ x : Fin e6Data.d, MinData.Valid.charHom k u (e6Data.wt x) =
      MinData.Valid.charHom k u' (e6Data.wt x) := fun x =>
    Additive.toMul.injective (Units.ext (congrFun (diagOp_injective he) x))
  rw [e6Data_valid.charHom_eq_of_wt k hval a, hu']

@[expose] def firstNode : Fin (Tag.rank .F4) → Fin (Tag.rank .E6) := ![nd 1, nd 3, nd 2, nd 0]

theorem orbitMap_firstNode (i : Fin (Tag.rank .F4)) : orbitMap (firstNode i) = i := by
  fin_cases i <;> rfl

theorem hHatE_le_iSup_torus_ne (i : Fin (Tag.rank .F4)) {a : Fin (Tag.rank .E6)}
    (ha : orbitMap a ≠ i) : hHatE k θ i ≤ ⨆ (c) (_ : c ≠ a), e6Data_valid.torus k c := by
  have hmem : ∀ c, orbitMap c = i → ∀ t, e6Data_valid.hm k c t ∈
      ⨆ (c) (_ : c ≠ a), e6Data_valid.torus k c := fun c hc t =>
    Subgroup.mem_iSup_of_mem c (Subgroup.mem_iSup_of_mem (fun (h : c = a) => ha (h ▸ hc))
      (e6Data_valid.hm_mem_torus k c t))
  fin_cases i
  · rintro _ ⟨t, rfl⟩
    exact hmem (nd 1) rfl _
  · rintro _ ⟨t, rfl⟩
    exact hmem (nd 3) rfl _
  · rintro _ ⟨t, rfl⟩
    exact mul_mem (hmem (nd 2) rfl _) (hmem (nd 4) rfl _)
  · rintro _ ⟨t, rfl⟩
    exact mul_mem (hmem (nd 0) rfl _) (hmem (nd 5) rfl _)

theorem hHat_iSupIndep : iSupIndep (hHat k θ) := by
  intro i
  rw [Subgroup.disjoint_def]
  intro g hg hg'
  have hle : (⨆ (j) (_ : j ≠ i), hHat k θ j) ≤
      (⨆ (c) (_ : c ≠ firstNode i), e6Data_valid.torus k c).comap (fixedGroup k θ).subtype :=
    iSup₂_le fun j hj x hx => by
      rw [hHat, Subgroup.mem_subgroupOf] at hx
      exact hHatE_le_iSup_torus_ne θ j (by rw [orbitMap_firstNode]; exact Ne.symm hj) hx
  have hamb : (g : e6Data_valid.minGroup k) ∈
      ⨆ (c) (_ : c ≠ firstNode i), e6Data_valid.torus k c := hle hg'
  rw [hHat, Subgroup.mem_subgroupOf] at hg
  refine Subtype.ext ?_
  change (g : e6Data_valid.minGroup k) = 1
  fin_cases i
  · obtain ⟨t, ht⟩ := hg
    rw [← ht] at hamb ⊢
    have h1 := eq_one_of_torusHom_mem (u := Pi.mulSingle (nd 1) (t : kˣ)) (a := nd 1)
      (by rw [torusHom_mulSingle]; exact hamb)
    rw [Pi.mulSingle_eq_same] at h1
    change e6Data_valid.hm k (nd 1) (t : kˣ) = 1
    rw [h1, e6Data_valid.hm_one]
  · obtain ⟨t, ht⟩ := hg
    rw [← ht] at hamb ⊢
    have h1 := eq_one_of_torusHom_mem (u := Pi.mulSingle (nd 3) (t : kˣ)) (a := nd 3)
      (by rw [torusHom_mulSingle]; exact hamb)
    rw [Pi.mulSingle_eq_same] at h1
    change e6Data_valid.hm k (nd 3) (t : kˣ) = 1
    rw [h1, e6Data_valid.hm_one]
  · obtain ⟨t, ht⟩ := hg
    rw [← ht] at hamb ⊢
    have h1 := eq_one_of_torusHom_mem
      (u := Pi.mulSingle (nd 2) t * Pi.mulSingle (nd 4) (Units.map (θ : k →* k) t)) (a := nd 2)
      (by rw [map_mul, torusHom_mulSingle, torusHom_mulSingle]; exact hamb)
    rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide), mul_one] at h1
    change e6Data_valid.hm k (nd 2) t * e6Data_valid.hm k (nd 4) (Units.map (θ : k →* k) t) = 1
    rw [h1, map_one, e6Data_valid.hm_one, e6Data_valid.hm_one, mul_one]
  · obtain ⟨t, ht⟩ := hg
    rw [← ht] at hamb ⊢
    have h1 := eq_one_of_torusHom_mem
      (u := Pi.mulSingle (nd 0) t * Pi.mulSingle (nd 5) (Units.map (θ : k →* k) t)) (a := nd 0)
      (by rw [map_mul, torusHom_mulSingle, torusHom_mulSingle]; exact hamb)
    rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide), mul_one] at h1
    change e6Data_valid.hm k (nd 0) t * e6Data_valid.hm k (nd 5) (Units.map (θ : k →* k) t) = 1
    rw [h1, map_one, e6Data_valid.hm_one, e6Data_valid.hm_one, mul_one]

end CFSG.LieType.Steinberg.TwistedE6
