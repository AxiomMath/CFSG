module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderModule

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender
open scoped commutatorElement

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {X : Type*} [Group X]

@[expose] def IsIrrQuot (ρ : X →* (V ≃ₗ[k] V)) (H : Subgroup X) (I : Submodule k V) : Prop :=
  ¬ I ≤ fixSub ρ H ∧ ∀ U : Submodule k V, Offender.IsInvariant ρ H U → I ⊓ fixSub ρ H ≤ U → U ≤ I →
    U = I ⊓ fixSub ρ H ∨ U = I

structure IsGoodModule (ρ : X →* (V ≃ₗ[k] V)) (H : Subgroup X) (I : Submodule k V) : Prop where
  inv : Offender.IsInvariant ρ H I
  comm : commSub ρ H I = I
  irr : IsIrrQuot ρ H I

theorem conj_mem_of_mem_normalizer {H : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (H : Set X)) {h : X} (hh : h ∈ H) : g * h * g⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.1 hg h).1 hh

theorem conj_inv_mem_of_mem_normalizer {H : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (H : Set X)) {h : X} (hh : h ∈ H) : g⁻¹ * h * g ∈ H := by
  have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) h).1 hh
  simpa using this

theorem mem_fixSub_map_iff (ρ : X →* (V ≃ₗ[k] V)) {H : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (H : Set X)) (x : V) :
    ρ g x ∈ fixSub ρ H ↔ x ∈ fixSub ρ H := by
  constructor
  · intro hx h hh
    have h1 := hx (g * h * g⁻¹) (conj_mem_of_mem_normalizer hg hh)
    have e : g⁻¹ * (g * h * g⁻¹) * g = h := by group
    calc ρ h x = ρ (g⁻¹ * (g * h * g⁻¹) * g) x := by rw [e]
      _ = ρ g⁻¹ (ρ (g * h * g⁻¹) (ρ g x)) := by
          rw [ρ_mul_apply, ρ_mul_apply]
      _ = ρ g⁻¹ (ρ g x) := by rw [h1]
      _ = x := ρ_inv_apply ρ g x
  · intro hx h hh
    have h1 := hx (g⁻¹ * h * g) (conj_inv_mem_of_mem_normalizer hg hh)
    calc ρ h (ρ g x) = ρ g (ρ (g⁻¹ * h * g) x) := by
          rw [← ρ_mul_apply, ← ρ_mul_apply]; congr 1; group
      _ = ρ g x := by rw [h1]

theorem map_fixSub_of_mem_normalizer (ρ : X →* (V ≃ₗ[k] V)) {H : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (H : Set X)) :
    (fixSub ρ H).map (ρ g : V →ₗ[k] V) = fixSub ρ H := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact (mem_fixSub_map_iff ρ hg z).2 hz
  · intro z hz
    refine ⟨ρ g⁻¹ z, ?_, ρ_apply_inv ρ g z⟩
    have : ρ g (ρ g⁻¹ z) ∈ fixSub ρ H := by rw [ρ_apply_inv]; exact hz
    exact (mem_fixSub_map_iff ρ hg _).1 this

theorem isInvariant_map {ρ : X →* (V ≃ₗ[k] V)} {H : Subgroup X} {U : Submodule k V}
    (hU : Offender.IsInvariant ρ H U) {g : X} (hg : g ∈ Subgroup.normalizer (H : Set X)) :
    Offender.IsInvariant ρ H (U.map (ρ g : V →ₗ[k] V)) := by
  rintro h hh _ ⟨u, hu, rfl⟩
  refine ⟨ρ (g⁻¹ * h * g) u, hU _ (conj_inv_mem_of_mem_normalizer hg hh) u hu, ?_⟩
  show ρ g (ρ (g⁻¹ * h * g) u) = ρ h (ρ g u)
  rw [← ρ_mul_apply, ← ρ_mul_apply]; congr 1; group

theorem isInvariant_comap {ρ : X →* (V ≃ₗ[k] V)} {H : Subgroup X} {U : Submodule k V}
    (hU : Offender.IsInvariant ρ H U) {g : X} (hg : g ∈ Subgroup.normalizer (H : Set X)) :
    Offender.IsInvariant ρ H (U.comap (ρ g : V →ₗ[k] V)) := by
  intro h hh u hu
  have hu' : ρ g u ∈ U := hu
  show ρ g (ρ h u) ∈ U
  have : ρ g (ρ h u) = ρ (g * h * g⁻¹) (ρ g u) := by
    rw [← ρ_mul_apply, ← ρ_mul_apply]; congr 1; group
  rw [this]
  exact hU _ (conj_mem_of_mem_normalizer hg hh) _ hu'

theorem commSub_mono_right (ρ : X →* (V ≃ₗ[k] V)) {B : Subgroup X} {U U' : Submodule k V}
    (h : U ≤ U') : commSub ρ B U ≤ commSub ρ B U' :=
  Submodule.span_mono (fun _ ⟨b, hb, u, hu, hw⟩ => ⟨b, hb, u, h hu, hw⟩)

theorem commSub_mono_left (ρ : X →* (V ≃ₗ[k] V)) {B B' : Subgroup X} {U : Submodule k V}
    (h : B ≤ B') : commSub ρ B U ≤ commSub ρ B' U :=
  Submodule.span_mono (fun _ ⟨b, hb, u, hu, hw⟩ => ⟨b, h hb, u, hu, hw⟩)

theorem commSub_le_iff {ρ : X →* (V ≃ₗ[k] V)} {B : Subgroup X} {U Y : Submodule k V} :
    commSub ρ B U ≤ Y ↔ ∀ b ∈ B, ∀ u ∈ U, ρ b u - u ∈ Y := by
  unfold commSub
  rw [Submodule.span_le]
  constructor
  · intro h b hb u hu
    exact h ⟨b, hb, u, hu, rfl⟩
  · rintro h w ⟨b, hb, u, hu, rfl⟩
    exact h b hb u hu

theorem commSub_le_of_isInvariant {ρ : X →* (V ≃ₗ[k] V)} {B : Subgroup X} {U : Submodule k V}
    (h : Offender.IsInvariant ρ B U) : commSub ρ B U ≤ U :=
  commSub_le_iff.2 fun b hb u hu => U.sub_mem (h b hb u hu) hu

theorem commSub_sup (ρ : X →* (V ≃ₗ[k] V)) (B : Subgroup X) (U U' : Submodule k V) :
    commSub ρ B (U ⊔ U') = commSub ρ B U ⊔ commSub ρ B U' := by
  refine le_antisymm ?_
    (sup_le (commSub_mono_right ρ le_sup_left) (commSub_mono_right ρ le_sup_right))
  rw [commSub_le_iff]
  intro b hb u hu
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hu
  have : ρ b (x + y) - (x + y) = (ρ b x - x) + (ρ b y - y) := by rw [map_add]; abel
  rw [this]
  exact Submodule.add_mem_sup (mem_commSub_of hb hx) (mem_commSub_of hb hy)

theorem commSub_sup_of_le_fixSub (ρ : X →* (V ≃ₗ[k] V)) (B : Subgroup X) (U Z : Submodule k V)
    (hZ : Z ≤ fixSub ρ B) : commSub ρ B (U ⊔ Z) = commSub ρ B U := by
  rw [commSub_sup]
  have : commSub ρ B Z = ⊥ := (commSub_eq_bot_iff ρ B Z).2 fun b hb z hz => hZ hz b hb
  rw [this, sup_bot_eq]

theorem commSub_map {ρ : X →* (V ≃ₗ[k] V)} {H : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (H : Set X)) (U : Submodule k V) :
    commSub ρ H (U.map (ρ g : V →ₗ[k] V)) = (commSub ρ H U).map (ρ g : V →ₗ[k] V) := by
  refine le_antisymm ?_ ?_
  · rw [commSub_le_iff]
    rintro h hh _ ⟨u, hu, rfl⟩
    refine ⟨ρ (g⁻¹ * h * g) u - u, mem_commSub_of (conj_inv_mem_of_mem_normalizer hg hh) hu, ?_⟩
    show ρ g (ρ (g⁻¹ * h * g) u - u) = ρ h (ρ g u) - ρ g u
    rw [map_sub, ← ρ_mul_apply, ← ρ_mul_apply]
    congr 2; group
  · rintro _ ⟨w, hw, rfl⟩
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨b, hb, u, hu, rfl⟩ := hw
      have : (ρ g : V →ₗ[k] V) (ρ b u - u) = ρ (g * b * g⁻¹) (ρ g u) - ρ g u := by
        show ρ g (ρ b u - u) = ρ (g * b * g⁻¹) (ρ g u) - ρ g u
        rw [map_sub, ← ρ_mul_apply, ← ρ_mul_apply]
        congr 2; group
      rw [this]
      exact mem_commSub_of (conj_mem_of_mem_normalizer hg hb) ⟨u, hu, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

theorem isIrrQuot_map {ρ : X →* (V ≃ₗ[k] V)} {H : Subgroup X} {I : Submodule k V}
    (hI : IsIrrQuot ρ H I) {g : X} (hg : g ∈ Subgroup.normalizer (H : Set X)) :
    IsIrrQuot ρ H (I.map (ρ g : V →ₗ[k] V)) := by
  obtain ⟨hnz, hirr⟩ := hI
  have hZmap : (fixSub ρ H).map (ρ g : V →ₗ[k] V) = fixSub ρ H :=
    map_fixSub_of_mem_normalizer ρ hg
  refine ⟨?_, fun U' hU' hlo hhi => ?_⟩
  · intro hle
    apply hnz
    intro x hx
    exact (mem_fixSub_map_iff ρ hg x).1 (hle ⟨x, hx, rfl⟩)
  · set U := U'.comap (ρ g : V →ₗ[k] V) with hU
    have hUinv : Offender.IsInvariant ρ H U := isInvariant_comap hU' hg
    have hlo' : I ⊓ fixSub ρ H ≤ U := by
      intro x hx
      have : ρ g x ∈ I.map (ρ g : V →ₗ[k] V) ⊓ fixSub ρ H :=
        ⟨⟨x, hx.1, rfl⟩, (mem_fixSub_map_iff ρ hg x).2 hx.2⟩
      exact hlo this
    have hhi' : U ≤ I := by
      intro u hu
      obtain ⟨x, hx, hxu⟩ := hhi (show ρ g u ∈ U' from hu)
      have : x = u := (ρ g).injective hxu
      rw [← this]; exact hx
    have hUe : U' = U.map (ρ g : V →ₗ[k] V) :=
      (Submodule.map_comap_eq_of_surjective (ρ g).surjective U').symm
    rcases hirr U hUinv hlo' hhi' with h | h
    · left
      rw [hUe, h, Submodule.map_inf _ (ρ g).injective, hZmap]
    · right
      rw [hUe, h]

theorem IsGoodModule.map {ρ : X →* (V ≃ₗ[k] V)} {H : Subgroup X} {I : Submodule k V}
    (hI : IsGoodModule ρ H I) {g : X} (hg : g ∈ Subgroup.normalizer (H : Set X)) :
    IsGoodModule ρ H (I.map (ρ g : V →ₗ[k] V)) :=
  ⟨isInvariant_map hI.inv hg, by rw [commSub_map hg, hI.comm], isIrrQuot_map hI.irr hg⟩

@[expose] def spanOrbit (ρ : X →* (V ≃ₗ[k] V)) (H : Subgroup X) (S : Submodule k V) :
    Submodule k V :=
  Submodule.span k {v | ∃ h ∈ H, ∃ s ∈ S, v = ρ h s}

theorem le_spanOrbit (ρ : X →* (V ≃ₗ[k] V)) (H : Subgroup X) (S : Submodule k V) :
    S ≤ spanOrbit ρ H S := fun s hs =>
  Submodule.subset_span ⟨1, H.one_mem, s, hs, by simp⟩

theorem isInvariant_spanOrbit (ρ : X →* (V ≃ₗ[k] V)) (H : Subgroup X) (S : Submodule k V) :
    Offender.IsInvariant ρ H (spanOrbit ρ H S) := by
  intro g hg u hu
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨h, hh, s, hs, rfl⟩ := hw
    exact Submodule.subset_span ⟨g * h, H.mul_mem hg hh, s, hs, by rw [ρ_mul_apply]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

theorem spanOrbit_le {ρ : X →* (V ≃ₗ[k] V)} {H : Subgroup X} {S U : Submodule k V}
    (hU : Offender.IsInvariant ρ H U) (hSU : S ≤ U) : spanOrbit ρ H S ≤ U := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨h, hh, s, hs, rfl⟩
  exact hU h hh s (hSU hs)

theorem map_eq_of_forall_mem (ρ : X →* (V ≃ₗ[k] V)) (Z : Submodule k V)
    (hZ : ∀ x, ∀ z ∈ Z, ρ x z ∈ Z) (x : X) : Z.map (ρ x : V →ₗ[k] V) = Z := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact hZ x z hz
  · intro z hz
    exact ⟨ρ x⁻¹ z, hZ x⁻¹ z hz, ρ_apply_inv ρ x z⟩

@[expose] noncomputable def quotHom (ρ : X →* (V ≃ₗ[k] V)) (Z : Submodule k V)
    (hZ : ∀ x, ∀ z ∈ Z, ρ x z ∈ Z) : X →* ((V ⧸ Z) ≃ₗ[k] (V ⧸ Z)) where
  toFun x := Submodule.Quotient.equiv Z Z (ρ x) (map_eq_of_forall_mem ρ Z hZ x)
  map_one' := by
    ext v
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective Z v
    simp [Submodule.Quotient.equiv_apply]
  map_mul' a b := by
    ext v
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective Z v
    simp [Submodule.Quotient.equiv_apply]

theorem quotHom_mk (ρ : X →* (V ≃ₗ[k] V)) (Z : Submodule k V) (hZ : ∀ x, ∀ z ∈ Z, ρ x z ∈ Z)
    (x : X) (v : V) :
    quotHom ρ Z hZ x (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ x v) := by
  simp [quotHom, Submodule.Quotient.equiv_apply]

theorem quotHom_mkQ (ρ : X →* (V ≃ₗ[k] V)) (Z : Submodule k V) (hZ : ∀ x, ∀ z ∈ Z, ρ x z ∈ Z)
    (x : X) (v : V) : quotHom ρ Z hZ x (Z.mkQ v) = Z.mkQ (ρ x v) :=
  quotHom_mk ρ Z hZ x v

instance finite_quotient_submodule {Z : Submodule k V} [Finite V] : Finite (V ⧸ Z) :=
  Finite.of_surjective Z.mkQ (Submodule.Quotient.mk_surjective Z)

theorem natCard_map_mkQ_mul_natCard_inf (Z U : Submodule k V) :
    Nat.card ↥(U.map Z.mkQ) * Nat.card ↥(U ⊓ Z) = Nat.card ↥U := by
  let f : U →ₗ[k] (V ⧸ Z) := Z.mkQ ∘ₗ U.subtype
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h2 : Nat.card (↥U ⧸ LinearMap.ker f) = Nat.card ↥(U.map Z.mkQ) := by
    refine (Nat.card_congr (f.quotKerEquivRange).toEquiv).trans ?_
    refine Nat.card_congr (LinearEquiv.ofEq _ _ ?_).toEquiv
    ext x
    simp only [LinearMap.mem_range, Submodule.mem_map]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, u.2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  have h3 : Nat.card ↥(LinearMap.ker f) = Nat.card ↥(U ⊓ Z) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : V), x.1.2, by
          have := x.2
          rwa [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
            Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this⟩
        invFun := fun x => ⟨⟨(x : V), x.2.1⟩, by
          rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
            Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact x.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  rw [h1, h2, h3, mul_comm]

open Finset in
theorem card_partition_of_orbit {M ι : Type*} [AddCommGroup M] [Module k M] [Finite M]
    [Fintype ι] (T : Submodule k M) (S : ι → Submodule k M) (D : Submodule k M) (q : ℕ)
    (hq : 2 ≤ q) (hT : Nat.card T = q * q) (hST : ∀ i, S i ≤ T) (hDT : D ≤ T)
    (hS : ∀ i, Nat.card (S i) = q) (hD : Nat.card D = q)
    (hSS : ∀ i j, i ≠ j → S i ⊓ S j = ⊥) (hSD : ∀ i, S i ⊓ D = ⊥)
    (hN : q ≤ Fintype.card ι) :
    Fintype.card ι = q ∧ ∀ v ∈ T, v ∈ D ∨ ∃ i, v ∈ S i := by
  classical
  have : Fintype M := Fintype.ofFinite M
  have hcardsub : ∀ U : Submodule k M, (univ.filter (fun v : M => v ∈ U)).card = Nat.card U := by
    intro U
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let Tf : Finset M := (univ.filter (fun v : M => v ∈ T)).erase 0
  let Tn : ι → Finset M := fun i => (univ.filter (fun v : M => v ∈ S i)).erase 0
  let TD : Finset M := (univ.filter (fun v : M => v ∈ D)).erase 0
  have hmemTf : ∀ v, v ∈ Tf ↔ v ≠ 0 ∧ v ∈ T := by
    intro v
    simp [Tf]
  have hmemT : ∀ i v, v ∈ Tn i ↔ v ≠ 0 ∧ v ∈ S i := by
    intro i v
    simp [Tn]
  have hmemTD : ∀ v, v ∈ TD ↔ v ≠ 0 ∧ v ∈ D := by
    intro v
    simp [TD]
  have hTfcard : Tf.card = q * q - 1 := by
    show ((univ.filter (fun v : M => v ∈ T)).erase 0).card = q * q - 1
    rw [Finset.card_erase_of_mem (by simp), hcardsub, hT]
  have hTcard : ∀ i, (Tn i).card = q - 1 := by
    intro i
    show ((univ.filter (fun v : M => v ∈ S i)).erase 0).card = q - 1
    rw [Finset.card_erase_of_mem (by simp), hcardsub, hS]
  have hTDcard : TD.card = q - 1 := by
    show ((univ.filter (fun v : M => v ∈ D)).erase 0).card = q - 1
    rw [Finset.card_erase_of_mem (by simp), hcardsub, hD]
  have hdisj : (Set.univ : Set ι).PairwiseDisjoint Tn := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro v hvi hvj
    rw [hmemT] at hvi hvj
    have h1 : v ∈ S i ⊓ S j := ⟨hvi.2, hvj.2⟩
    rw [hSS i j hij] at h1
    exact hvi.1 (by simpa using h1)
  have hdisj2 : Disjoint TD (univ.biUnion Tn) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    rw [Finset.mem_biUnion] at hv'
    obtain ⟨i, -, hi⟩ := hv'
    rw [hmemTD] at hv
    rw [hmemT] at hi
    have h1 : v ∈ S i ⊓ D := ⟨hi.2, hv.2⟩
    rw [hSD i] at h1
    exact hv.1 (by simpa using h1)
  have hbU : (univ.biUnion Tn).card = Fintype.card ι * (q - 1) := by
    rw [Finset.card_biUnion (fun i _ j _ hij => hdisj (Set.mem_univ i) (Set.mem_univ j) hij)]
    simp [hTcard]
  have hunion : (TD ∪ univ.biUnion Tn).card = (q - 1) + Fintype.card ι * (q - 1) := by
    rw [Finset.card_union_of_disjoint hdisj2, hTDcard, hbU]
  have hsub : TD ∪ univ.biUnion Tn ⊆ Tf := by
    intro v hv
    rw [hmemTf]
    rw [Finset.mem_union, hmemTD, Finset.mem_biUnion] at hv
    rcases hv with hv | ⟨i, -, hi⟩
    · exact ⟨hv.1, hDT hv.2⟩
    · have := (hmemT i v).1 hi
      exact ⟨this.1, hST i this.2⟩
  have hle := Finset.card_le_card hsub
  rw [hunion, hTfcard] at hle
  have hN' : Fintype.card ι ≤ q := by
    by_contra hlt
    have hlt := not_le.mp hlt
    have h1 : (q - 1) * (Fintype.card ι + 1) ≤ (q - 1) * (q + 1) := by
      have e1 : (q - 1) + Fintype.card ι * (q - 1) = (q - 1) * (Fintype.card ι + 1) := by ring
      have e2 : q * q - 1 = (q - 1) * (q + 1) := by
        obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring_nf
        omega
      rw [e1, e2] at hle
      exact hle
    have h2 := Nat.le_of_mul_le_mul_left h1 (by omega)
    omega
  have hNq : Fintype.card ι = q := le_antisymm hN' hN
  refine ⟨hNq, fun v hvT => ?_⟩
  have hcard_eq : (TD ∪ univ.biUnion Tn).card = Tf.card := by
    rw [hunion, hTfcard, hNq]
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard_eq.symm)
  by_cases hv0 : v = 0
  · left; rw [hv0]; exact D.zero_mem
  · have : v ∈ Tf := (hmemTf v).2 ⟨hv0, hvT⟩
    rw [← heq, Finset.mem_union, hmemTD, Finset.mem_biUnion] at this
    rcases this with h | ⟨i, -, hi⟩
    · left; exact h.2
    · right; exact ⟨i, ((hmemT i v).1 hi).2⟩

end CFSG.QuasithinUnique.Setup.Layer
