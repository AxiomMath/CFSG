module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
public import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents
public import CFSG.FeitThompson.OddOrderTheorem

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne

open CFSG Subgroup CFSG.ComponentClassification.TBLit
open scoped commutatorElement MatrixGroups

@[expose] def PropAConclusion (X : Type) [Group X] (t : X) (Y : Subgroup X) : Prop :=
  ∃ u : X, orderOf u = 2 ∧ ∃ S : Subgroup X, S ≤ centralizer ({u} : Set X) ∧
    IsPComponent 2 (S.subgroupOf (centralizer ({u} : Set X))) ∧
    (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
      Nonempty (S ≃* SL(2, GaloisField p n))) ∧
    (center S).map S.subtype = zpowers u ∧ ActsProperly t Y S ⊥

theorem burgoynePropA_iff : BurgoynePropA ↔
    ∀ (X : Type) [Group X] [Finite X], IsM4 X → ∀ t : X, orderOf t = 2 →
      ∀ Y : Subgroup X, Y ≠ ⊥ → Y ≤ oddCentralizerCore t → PropAConclusion X t Y :=
  Iff.rfl

section Transport

variable {X X' : Type} [Group X] [Group X']

theorem map_centralizer_singleton (e : X ≃* X') (u : X) :
    (centralizer ({u} : Set X)).map e.toMonoidHom = centralizer ({e u} : Set X') := by
  ext y
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg e h
    rwa [map_mul, map_mul, e.apply_symm_apply] at h'
  · intro h
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact h

theorem ActsProperly.map (e : X ≃* X') {t : X} {Y A B : Subgroup X}
    (h : ActsProperly t Y A B) :
    ActsProperly (e t) (Y.map e.toMonoidHom) (A.map e.toMonoidHom) (B.map e.toMonoidHom) := by
  obtain ⟨h1, h2, y0, hy0, a0, ha0, hab⟩ := h
  have hcl : closure (insert (e t) ((Y.map e.toMonoidHom : Subgroup X') : Set X')) =
      (closure (insert t (Y : Set X))).map e.toMonoidHom := by
    rw [MonoidHom.map_closure, Set.image_insert_eq, coe_map]
    rfl
  refine ⟨?_, ?_, e y0, ⟨y0, hy0, rfl⟩, e a0, ⟨a0, ha0, rfl⟩, ?_⟩
  · rw [hcl, ← map_equiv_normalizer_eq, ← map_equiv_normalizer_eq,
      ← map_inf_eq _ _ _ e.injective]
    exact map_mono h1
  · rw [hcl]
    rintro _ ⟨g, hg, rfl⟩ hcomm
    refine ⟨g, h2 g hg fun a ha => ?_, rfl⟩
    have h3 := hcomm (e a) ⟨a, ha, rfl⟩
    rw [mem_map_equiv] at h3
    change e.symm ⁅e a, e g⁆ ∈ B at h3
    rwa [← map_commutatorElement, MulEquiv.symm_apply_apply] at h3
  · intro hc
    rw [mem_map_equiv] at hc
    change e.symm ⁅e a0, e y0⁆ ∈ B at hc
    rw [← map_commutatorElement, MulEquiv.symm_apply_apply] at hc
    exact hab hc

end Transport

section Ambient

variable {G : Type} [Group G]

abbrev oddCoreIn (B : Subgroup G) (t : G) : Subgroup G :=
  (pPrimeCore 2 ↥(B ⊓ centralizer ({t} : Set G))).map (B ⊓ centralizer ({t} : Set G)).subtype

@[expose] def PropAConclusionIn (B : Subgroup G) (t : G) (Y : Subgroup G) : Prop :=
  ∃ u ∈ B, orderOf u = 2 ∧ ∃ S : Subgroup G, S ≤ B ∧ S ≤ centralizer ({u} : Set G) ∧
    IsPComponent 2 (S.subgroupOf (B ⊓ centralizer ({u} : Set G))) ∧
    (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
      Nonempty (S ≃* SL(2, GaloisField p n))) ∧
    (center S).map S.subtype = zpowers u ∧ ActsProperly t Y S ⊥

theorem commute_of_mem_oddCoreIn {B : Subgroup G} {t y : G} (hy : y ∈ oddCoreIn B t) :
    y * t = t * y := by
  obtain ⟨z, -, rfl⟩ := hy
  exact mem_centralizer_singleton_iff.1 (mem_inf.1 z.2).2

theorem odd_orderOf_of_mem_oddCoreIn [Finite G] {B : Subgroup G} {t y : G}
    (hy : y ∈ oddCoreIn B t) : Odd (orderOf y) := by
  have hcop : Nat.Coprime 2 (Nat.card (oddCoreIn B t)) := by
    rw [card_map_of_injective (subtype_injective _)]
    exact pPrimeCore_coprime_card
  have hdvd : orderOf y ∣ Nat.card (oddCoreIn B t) := Subgroup.orderOf_dvd_natCard _ hy
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have := Nat.Coprime.coprime_dvd_right hdvd hcop
  rw [Nat.coprime_two_left] at this
  exact (Nat.not_even_iff_odd.2 this) (even_iff_two_dvd.2 h2)

theorem mem_or_mul_mem_of_mem_closure_insert {t : G} {Y : Subgroup G} (ht : t * t = 1)
    (hYt : ∀ y ∈ Y, y * t = t * y) {g : G} (hg : g ∈ closure (insert t (Y : Set G))) :
    g ∈ Y ∨ g * t ∈ Y := by
  induction hg using closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact Or.inr (by rw [ht]; exact one_mem Y)
    · exact Or.inl hx
  | one => exact Or.inl (one_mem Y)
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (mul_mem hx hy)
    · exact Or.inr (by rw [mul_assoc]; exact mul_mem hx hy)
    · refine Or.inr ?_
      have : x * y * t = x * t * y := by rw [mul_assoc, hYt y hy, ← mul_assoc]
      rw [this]
      exact mul_mem hx hy
    · refine Or.inl ?_
      have h2 : t * (y * t) = y := by rw [← hYt _ hy, mul_assoc, ht, mul_one]
      have h1 : x * y = x * t * (y * t) := by
        calc x * y = x * (t * (y * t)) := by rw [h2]
          _ = x * t * (y * t) := by rw [mul_assoc]
      rw [h1]
      exact mul_mem hx hy
  | inv x _ hx =>
    rcases hx with hx | hx
    · exact Or.inl (inv_mem hx)
    · refine Or.inr ?_
      have htt : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
      have hc := hYt _ hx
      have hcomm : (x * t)⁻¹ * t = t * (x * t)⁻¹ := by
        calc (x * t)⁻¹ * t = (x * t)⁻¹ * (t * (x * t)) * (x * t)⁻¹ := by group
          _ = (x * t)⁻¹ * ((x * t) * t) * (x * t)⁻¹ := by rw [hc]
          _ = t * (x * t)⁻¹ := by group
      have hxy : x = (x * t) * t := by rw [mul_assoc, ht, mul_one]
      have h1 : x⁻¹ * t = (x * t)⁻¹ := by
        conv_lhs => rw [hxy]
        rw [mul_inv_rev, htt, mul_assoc, hcomm, ← mul_assoc, ht, one_mul]
      rw [h1]
      exact inv_mem hx

theorem propAConclusionIn_of_core [Finite G] {B : Subgroup G} {t u : G} {Y S : Subgroup G}
    (ht : orderOf t = 2) (hY : Y ≠ ⊥) (hYO : Y ≤ oddCoreIn B t) (huB : u ∈ B)
    (hu : orderOf u = 2) (hSB : S ≤ B) (hSu : S ≤ centralizer ({u} : Set G))
    (hSc : IsPComponent 2 (S.subgroupOf (B ⊓ centralizer ({u} : Set G))))
    (hSL : ∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
      Nonempty (S ≃* SL(2, GaloisField p n)))
    (hZ : (center S).map S.subtype = zpowers u) (htN : t ∈ normalizer (S : Set G))
    (htC : ∃ a ∈ S, t * a ≠ a * t) (hON : oddCoreIn B t ≤ normalizer (S : Set G))
    (hOC : ∀ y ∈ oddCoreIn B t, (∀ a ∈ S, y * a = a * y) → y = 1) :
    PropAConclusionIn B t Y := by
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hYt : ∀ y ∈ Y, y * t = t * y := fun y hy => commute_of_mem_oddCoreIn (hYO hy)
  have hbot : ∀ g : G, g ∈ normalizer ((⊥ : Subgroup G) : Set G) := fun g => by
    rw [mem_normalizer_iff]
    intro h
    simp only [mem_bot]
    constructor
    · rintro rfl
      group
    · intro h1
      calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
  refine ⟨u, huB, hu, S, hSB, hSu, hSc, hSL, hZ, ?_, ?_, ?_⟩
  · rw [closure_le]
    intro x hx
    refine ⟨?_, hbot x⟩
    rcases hx with rfl | hx
    · exact htN
    · exact hON (hYO hx)
  · intro g hg hcomm
    have hcen : ∀ a ∈ S, g * a = a * g := fun a ha => by
      have h1 := hcomm a ha
      rw [mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    rcases mem_or_mul_mem_of_mem_closure_insert htt hYt hg with h | h
    · exact h
    · exfalso
      obtain ⟨a, ha, hta⟩ := htC
      set y := g * t with hydef
      have hgy : g = y * t := by rw [hydef, mul_assoc, htt, mul_one]
      obtain ⟨k, hk⟩ := odd_orderOf_of_mem_oddCoreIn (hYO h)
      have hpow : g ^ orderOf y = t := by
        rw [hgy, (Commute.mul_pow (hYt y h) _), pow_orderOf_eq_one, one_mul, hk, pow_succ,
          pow_mul, pow_two, htt, one_pow, one_mul]
      have hgC : g ∈ centralizer (S : Set G) :=
        mem_centralizer_iff.2 fun a ha => (hcen a ha).symm
      have htC' : t ∈ centralizer (S : Set G) := hpow ▸ pow_mem hgC _
      exact hta (mem_centralizer_iff.1 htC' a ha).symm
  · obtain ⟨⟨y, hy⟩, hy1⟩ := (ne_bot_iff_exists_ne_one).1 hY
    by_contra hall
    push Not at hall
    apply hy1
    refine Subtype.ext (hOC y (hYO hy) fun a ha => ?_)
    have h1 := hall y hy a ha
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm

theorem even_card_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q] (hQ : IsQuasisimple Q) :
    Even (Nat.card Q) := by
  by_contra h
  have hs : Group.IsSolvable Q := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.1 h)
  have : Nontrivial Q := LocalCores.isQuasisimple_nontrivial hQ
  have : Group.IsPerfect Q := hQ.1
  exact Group.IsPerfect.not_isSolvable Q hs

theorem isPComponent_two_of_quasisimple [Finite G] {H J : Subgroup G} (hJH : J ≤ H)
    (hJq : IsQuasisimple J) (hJs : (J.subgroupOf H).IsSubnormal) (hJe : Even (Nat.card J)) :
    IsPComponent 2 (J.subgroupOf H) := by
  have hK : IsComponent (J.subgroupOf H) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJH).symm hJq, hJs⟩
  refine LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hK fun hle => ?_
  have hdvd : Nat.card (J.subgroupOf H) ∣ Nat.card (pPrimeCore 2 H) := card_dvd_of_le hle
  rw [Nat.card_congr (subgroupOfEquivOfLe hJH).toEquiv] at hdvd
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 H)) := pPrimeCore_coprime_card
  exact (Nat.not_even_iff_odd.2 (Nat.coprime_two_left.1 (hcop.coprime_dvd_right hdvd))) hJe

theorem commute_of_mem_pPrimeCore [Finite G] {H J : Subgroup G} (hJH : J ≤ H)
    (hJq : IsQuasisimple J) (hJs : (J.subgroupOf H).IsSubnormal) (hJe : Even (Nat.card J))
    {y : G} (hy : y ∈ (pPrimeCore 2 H).map H.subtype) {j : G} (hj : j ∈ J) :
    y * j = j * y := by
  have hK : IsComponent (J.subgroupOf H) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJH).symm hJq, hJs⟩
  rcases LocalCores.component_subnormal_subgroup hK (pPrimeCore_normal (p := 2)).isSubnormal with
    hle | hcomm
  · exfalso
    have hdvd : Nat.card (J.subgroupOf H) ∣ Nat.card (pPrimeCore 2 H) := card_dvd_of_le hle
    rw [Nat.card_congr (subgroupOfEquivOfLe hJH).toEquiv] at hdvd
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 H)) := pPrimeCore_coprime_card
    exact (Nat.not_even_iff_odd.2 (Nat.coprime_two_left.1 (hcop.coprime_dvd_right hdvd))) hJe
  · obtain ⟨y', hy', rfl⟩ := hy
    have h1 : ⁅(⟨j, hJH hj⟩ : H), y'⁆ = 1 := by
      rw [← mem_bot, ← hcomm]
      exact commutator_mem_commutator (mem_subgroupOf.2 hj) hy'
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact (congrArg Subtype.val h1).symm

end Ambient

section Injective

variable {X G : Type} [Group X] [Group G]

theorem isPComponent_subgroupOf_map_iff [Finite X] (p : ℕ) (hp : p.Prime) {f : X →* G}
    (hf : Function.Injective f) {S H : Subgroup X} :
    IsPComponent p (S.subgroupOf H) ↔ IsPComponent p ((S.map f).subgroupOf (H.map f)) := by
  let e : H ≃* H.map f := H.equivMapOfInjective f hf
  have : Finite (H.map f) := Finite.of_equiv _ e.toEquiv
  have hmap : (S.subgroupOf H).map e.toMonoidHom = (S.map f).subgroupOf (H.map f) := by
    ext ⟨y, hy⟩
    rw [mem_subgroupOf, mem_map_equiv]
    constructor
    · intro h
      rw [mem_subgroupOf] at h
      refine ⟨_, h, ?_⟩
      have := congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
      rw [coe_equivMapOfInjective_apply] at this
      exact this
    · rintro ⟨x, hx, rfl⟩
      rw [mem_subgroupOf]
      have hxH : x ∈ H := by
        obtain ⟨x', hx', hx'eq⟩ := hy
        rw [← hf hx'eq]
        exact hx'
      have : e.symm ⟨f x, hy⟩ = ⟨x, hxH⟩ := by
        apply e.injective
        rw [e.apply_symm_apply]
        exact Subtype.ext (coe_equivMapOfInjective_apply H f hf ⟨x, hxH⟩).symm
      rw [this]
      exact hx
  rw [← hmap]
  exact (LocalAnalysis.ComponentInitial.p_component_isomorphism_transport p hp e).1 _

theorem map_centralizer_singleton_of_injective {f : X →* G} (hf : Function.Injective f)
    (u : X) : (centralizer ({u} : Set X)).map f = f.range ⊓ centralizer ({f u} : Set G) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x * u = u * x := mem_centralizer_singleton_iff.1 hx
    refine mem_inf.2 ⟨⟨x, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, hx']
  · intro hy
    obtain ⟨⟨x, rfl⟩, hx⟩ := mem_inf.1 hy
    refine ⟨x, mem_centralizer_singleton_iff.2 ?_, rfl⟩
    have hx' := mem_centralizer_singleton_iff.1 hx
    rw [← map_mul, ← map_mul] at hx'
    exact hf hx'

theorem map_oddCentralizerCore_of_injective [Finite X] {f : X →* G}
    (hf : Function.Injective f) (t : X) :
    (oddCentralizerCore t).map f = oddCoreIn f.range (f t) := by
  set C := centralizer ({t} : Set X) with hC
  set D := f.range ⊓ centralizer ({f t} : Set G) with hD
  have hCD : C.map f = D := map_centralizer_singleton_of_injective hf t
  let e : C ≃* D := (C.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hCD)
  have he : ∀ c : C, ((e c : D) : G) = f c := fun c => rfl
  have hcore := CFSG.pPrimeCore_map_iso 2 e
  rw [oddCentralizerCore, oddCoreIn, map_map, ← hcore, map_map]
  rfl

theorem ActsProperly.of_map {f : X →* G} (hf : Function.Injective f) {t : X}
    {Y A B : Subgroup X} (h : ActsProperly (f t) (Y.map f) (A.map f) (B.map f)) :
    ActsProperly t Y A B := by
  obtain ⟨h1, h2, y0, ⟨y, hy, rfl⟩, a0, ⟨a, ha, rfl⟩, hab⟩ := h
  have hcl : closure (insert (f t) ((Y.map f : Subgroup G) : Set G)) =
      (closure (insert t (Y : Set X))).map f := by
    rw [MonoidHom.map_closure, Set.image_insert_eq, coe_map]
  have hnorm : ∀ K : Subgroup X, (normalizer (K.map f : Set G)).comap f = normalizer (K : Set X) :=
    fun K => by
      rw [comap_normalizer_eq_of_le_range (map_le_range f K), comap_map_eq_self_of_injective hf]
  refine ⟨?_, ?_, y, hy, a, ha, ?_⟩
  · intro g hg
    have := h1 (hcl ▸ mem_map_of_mem f hg)
    rw [mem_inf] at this ⊢
    refine ⟨?_, ?_⟩
    · rw [← hnorm]
      exact this.1
    · rw [← hnorm]
      exact this.2
  · intro g hg hcomm
    obtain ⟨y', hy', hy'eq⟩ := h2 (f g) (hcl ▸ mem_map_of_mem f hg) fun a' ha' => by
      obtain ⟨a, ha, rfl⟩ := ha'
      rw [← map_commutatorElement]
      exact mem_map_of_mem f (hcomm a ha)
    rw [← hf hy'eq]
    exact hy'
  · intro hc
    apply hab
    rw [← map_commutatorElement]
    exact mem_map_of_mem f hc

theorem PropAConclusion.of_injective [Finite X] {f : X →* G} (hf : Function.Injective f)
    {t : X} {Y : Subgroup X} (h : PropAConclusionIn f.range (f t) (Y.map f)) :
    PropAConclusion X t Y := by
  obtain ⟨_, ⟨u, rfl⟩, hu, S, hSB, hSu, hSc, hSL, hZ, hact⟩ := h
  set S₀ := S.comap f with hS₀
  have hS₀map : S₀.map f = S := map_comap_eq_self hSB
  refine ⟨u, ?_, S₀, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [orderOf_injective f hf] at hu
  · intro x hx
    have hfx := mem_centralizer_singleton_iff.1 (hSu hx)
    rw [← map_mul, ← map_mul] at hfx
    exact mem_centralizer_singleton_iff.2 (hf hfx)
  · rw [isPComponent_subgroupOf_map_iff 2 Nat.prime_two hf, hS₀map,
      map_centralizer_singleton_of_injective hf]
    exact hSc
  · obtain ⟨p, n, hp, hp2, hn, ⟨e⟩⟩ := hSL
    exact ⟨p, n, hp, hp2, hn, ⟨((S₀.equivMapOfInjective f hf).trans
      (MulEquiv.subgroupCongr hS₀map)).trans e⟩⟩
  · apply map_injective hf
    rw [MonoidHom.map_zpowers, ← hZ]
    let e : S₀ ≃* S := (S₀.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hS₀map)
    have hcomp : f.comp S₀.subtype = S.subtype.comp (e : S₀ →* S) := by
      ext x
      rfl
    rw [map_map, hcomp, ← map_map, map_center_eq e]
  · refine ActsProperly.of_map hf ?_
    rw [hS₀map, Subgroup.map_bot]
    exact hact

end Injective

section Embedding

variable {X : Type} [Group X]

attribute [local instance] GeneralizedFitting.normal

theorem centralizer_generalizedFitting_eq_bot [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) :
    centralizer (GeneralizedFitting.subgroup X : Set X) = ⊥ := by
  set F := GeneralizedFitting.subgroup X
  have hle : centralizer (F : Set X) ≤ F := GeneralizedFitting.centralizer_le X
  have hcenter : center F = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (center F) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      exact absurd (mem_center_iff.mp (h ▸ mem_top b) a) hab
  refine eq_bot_iff.2 fun x hx => ?_
  have hz : (⟨x, hle hx⟩ : F) ∈ center F := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext ((mem_centralizer_iff.1 hx) y y.2)
  rw [hcenter, mem_bot] at hz
  rw [mem_bot]
  exact congrArg Subtype.val hz

@[expose] def socleAction {T : Type*} [Group T] (θ : GeneralizedFitting.subgroup X ≃* T) :
    X →* MulAut T :=
  (MulAut.congr θ).toMonoidHom.comp MulAut.conjNormal

theorem socleAction_symm {T : Type*} [Group T] (θ : GeneralizedFitting.subgroup X ≃* T) (x : T) :
    socleAction θ (θ.symm x : X) = MulAut.conj x := by
  ext y
  change θ (MulAut.conjNormal (θ.symm x : X) (θ.symm y)) = x * y * x⁻¹
  have : MulAut.conjNormal (θ.symm x : X) (θ.symm y) = θ.symm x * θ.symm y * (θ.symm x)⁻¹ :=
    Subtype.ext (by rw [MulAut.conjNormal_apply]; rfl)
  rw [this, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem socleAction_injective [Finite X] {T : Type*} [Group T]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* T) : Function.Injective (socleAction θ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
    ← centralizer_generalizedFitting_eq_bot hsimple hnab]
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  have h := congrArg (fun α : MulAut T => θ.symm (α (θ ⟨y, hy⟩))) (MonoidHom.mem_ker.1 hx)
  have h' : θ.symm (socleAction θ x (θ ⟨y, hy⟩)) =
      (MulAut.conjNormal x : MulAut (GeneralizedFitting.subgroup X)) ⟨y, hy⟩ := by
    change θ.symm (θ ((MulAut.conjNormal x : MulAut (GeneralizedFitting.subgroup X))
      (θ.symm (θ ⟨y, hy⟩)))) = _
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  simp only [MulAut.one_apply, MulEquiv.symm_apply_apply] at h
  rw [h'] at h
  have h2 := congrArg Subtype.val h
  rw [MulAut.conjNormal_apply] at h2
  calc y * x = x * y * x⁻¹ * x := by rw [h2]
    _ = x * y := by group

theorem conj_mem_range_socleAction {T : Type*} [Group T]
    (θ : GeneralizedFitting.subgroup X ≃* T) (x : T) :
    MulAut.conj x ∈ (socleAction θ).range :=
  ⟨_, socleAction_symm θ x⟩

end Embedding

end CFSG.ComponentClassification.Burgoyne