module

public import CFSG.Fischer.Edge
public import CFSG.Fischer.Aut.Central
public import CFSG.Fischer.Aut.TauGroup
public import CFSG.Fischer.Aut.Generate

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

theorem complete_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : ∀ φ : MulAut G, ∃ g, φ = MulAut.conj g) : ∀ φ : MulAut G', ∃ g, φ = MulAut.conj g := by
  intro φ
  obtain ⟨g, hg⟩ := h ((MulAut.congr e).symm φ)
  refine ⟨e g, ?_⟩
  have := congrArg (MulAut.congr e) hg
  rw [MulEquiv.apply_symm_apply] at this
  rw [this]
  refine MulEquiv.ext fun x => ?_
  show e (g * e.symm x * g⁻¹) = e g * x * (e g)⁻¹
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem OutTwo.of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (h : OutTwo G) :
    OutTwo G' := by
  intro β
  obtain ⟨k, g, hk⟩ := h ((MulAut.congr e).symm β)
  refine ⟨k, e g, ?_⟩
  have := congrArg (MulAut.congr e) hk
  rw [map_pow, MulEquiv.apply_symm_apply] at this
  rw [this]
  refine MulEquiv.ext fun x => ?_
  show e (g * e.symm x * g⁻¹) = e g * x * (e g)⁻¹
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem OutTwo.of_map {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Injective f)
    {K : Subgroup G} {C : Subgroup H} (hKC : K.map f = C) (h : OutTwo C) : OutTwo K :=
  OutTwo.of_mulEquiv ((K.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hKC)).symm h

theorem OutTwo.centralizer_conj {G : Type*} [Group G] (c d : G)
    (h : OutTwo (Subgroup.centralizer ({d} : Set G))) :
    OutTwo (Subgroup.centralizer ({c * d * c⁻¹} : Set G)) :=
  OutTwo.of_mulEquiv (conjCentralizer c d) h

theorem complete_range_of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (h : ∀ φ : MulAut G, ∃ g, φ = MulAut.conj g) :
    ∀ φ : MulAut f.range, ∃ g, φ = MulAut.conj g :=
  complete_of_mulEquiv (MonoidHom.ofInjective hf) h

theorem card_eq_two_mul_of_index {A : Type*} [Group A] {L C : Subgroup A} (hLC : L ≤ C)
    (h : (L.subgroupOf C).index = 2) : Nat.card C = 2 * Nat.card L := by
  have h1 := (L.subgroupOf C).card_mul_index
  rw [h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLC).toEquiv] at h1
  omega

section Index

variable {X : Type} [Group X] {E : Set X} (hE : Pair X E) {a b : X} (ha : a ∈ E) (hb : b ∈ E)
  (hab : a ≠ b) (hc : a * b = b * a)

include hE ha hb hab hc in
theorem index_centralizer_inf_eq_two
    (hW : ∀ w ∈ LocalClass E a ∩ LocalClass E b,
      ∃ w' ∈ LocalClass E a ∩ LocalClass E b, w * w' ≠ w' * w)
    {K : Subgroup X} {g : X} (hgK : g ∈ K) (hg1 : g * a * g⁻¹ = b) (hg2 : g * b * g⁻¹ = a) :
    ((Subgroup.centralizer ({a * b} : Set X) ⊓ K ⊓ Subgroup.centralizer ({a} : Set X)).subgroupOf
      (Subgroup.centralizer ({a * b} : Set X) ⊓ K)).index = 2 := by
  have hgC : g ∈ Subgroup.centralizer ({a * b} : Set X) ⊓ K :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
      (commute_mul_of_conj hc (Or.inr ⟨hg1, hg2⟩)), hgK⟩
  have hfix : ∀ x : X, x * a * x⁻¹ = a ↔ x ∈ Subgroup.centralizer ({a} : Set X) := fun x => by
    rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  have hconj : ∀ x : X, x * g * a * (x * g)⁻¹ = x * (g * a * g⁻¹) * x⁻¹ := fun x => by group
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨g, hgC⟩, fun c => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  show Xor ((c : X) * g ∈ _) ((c : X) ∈ _)
  have hc' := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 c.2).1
  rcases conj_eq_or_of_commute_mul hE ha hb hab hc hW hc' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inr ⟨Subgroup.mem_inf.2 ⟨c.2, (hfix c).1 h1⟩, fun h' => ?_⟩
    have h3 := (hfix _).2 (Subgroup.mem_inf.1 h').2
    rw [hconj, hg1, h2] at h3
    exact hab h3.symm
  · refine Or.inl ⟨Subgroup.mem_inf.2 ⟨(Subgroup.centralizer ({a * b} : Set X) ⊓ K).mul_mem c.2
      hgC, (hfix _).1 ?_⟩, fun h' => ?_⟩
    · rw [hconj, hg1, h2]
    · have h3 := (hfix c).2 (Subgroup.mem_inf.1 h').2
      rw [h1] at h3
      exact hab h3.symm

end Index

theorem center_tauGroup_eq_bot {Y : Type} [Group Y] {F : Set Y} (hF : Pair Y F)
    (hZ : Subgroup.center Y = ⊥) : Subgroup.center (tauGroup hF) = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  exact eq_one_of_commute_innerTau hF hZ fun x => (Subgroup.mem_center_iff.1 hσ _).symm

theorem eq_top_of_index_two {A : Type*} [Group A] {N K : Subgroup A} (hN : N.index = 2)
    (hNK : N ≤ K) {x : A} (hxK : x ∈ K) (hxN : x ∉ N) : K = ⊤ := by
  have hdvd : K.index ∣ N.index := Subgroup.index_dvd_of_le hNK
  rw [hN] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact Subgroup.index_eq_one.1 h
  · exfalso
    apply hxN
    have h1 := Subgroup.relIndex_mul_index hNK
    rw [h, hN] at h1
    have h2 : N.relIndex K = 1 := by omega
    exact Subgroup.relIndex_eq_one.1 h2 hxK

section Edge

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y} (hE : Pair X E)
  (hF : Pair Y F) {a b : X} (ha : a ∈ E) (hb : b ∈ E) (hab : a ≠ b) (hc : a * b = b * a)
  (ψ : ↥(LocalClass E a ∩ LocalClass E b) ≃ F)
  (hψc : ∀ x y : ↥(LocalClass E a ∩ LocalClass E b),
    (x : X) * y = y * x ↔ (ψ x : Y) * ψ y = ψ y * ψ x)
  (hψt : ∀ x y : ↥(LocalClass E a ∩ LocalClass E b),
    ∃ h : (x : X) * y * x ∈ LocalClass E a ∩ LocalClass E b, (ψ ⟨_, h⟩ : Y) = ψ x * ψ y * ψ x)
  (hZF : Subgroup.center Y = ⊥)

include hF hψc hZF in
theorem exists_not_commute_of_edgeEquiv : ∀ w ∈ LocalClass E a ∩ LocalClass E b,
    ∃ w' ∈ LocalClass E a ∩ LocalClass E b, w * w' ≠ w' * w := by
  intro w hw
  obtain ⟨f, hf, hne⟩ := exists_not_commute_of_center hF hZF (ψ ⟨w, hw⟩).2
  refine ⟨ψ.symm ⟨f, hf⟩, (ψ.symm ⟨f, hf⟩).2, fun h => hne ?_⟩
  have := (hψc ⟨w, hw⟩ (ψ.symm ⟨f, hf⟩)).1 h
  rwa [Equiv.apply_symm_apply] at this

include hE ha hb hab hc hF hψc hZF in
theorem conj_mem_edge {g : X} (hg : g * (a * b) = a * b * g) {w : X}
    (hw : w ∈ LocalClass E a ∩ LocalClass E b) :
    g * w * g⁻¹ ∈ LocalClass E a ∩ LocalClass E b := by
  have hW := exists_not_commute_of_edgeEquiv hF ψ hψc hZF
  have e1 := (Pair.conj_mem_localClass_iff hE g (e := a) (f := w)).2 hw.1
  have e2 := (Pair.conj_mem_localClass_iff hE g (e := b) (f := w)).2 hw.2
  rcases conj_eq_or_of_commute_mul hE ha hb hab hc hW hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1] at e1
    rw [h2] at e2
    exact ⟨e1, e2⟩
  · rw [h1] at e1
    rw [h2] at e2
    exact ⟨e2, e1⟩

@[expose] noncomputable def edgeHomW :
    Subgroup.centralizer ({a * b} : Set X) →* Equiv.Perm ↥(LocalClass E a ∩ LocalClass E b) where
  toFun g :=
    { toFun := fun w => ⟨(g : X) * w * (g : X)⁻¹, conj_mem_edge hE hF ha hb hab hc ψ hψc hZF
        (Subgroup.mem_centralizer_singleton_iff.1 g.2) w.2⟩
      invFun := fun w => ⟨(g : X)⁻¹ * w * (g : X), by
        have := conj_mem_edge hE hF ha hb hab hc ψ hψc hZF
          (Subgroup.mem_centralizer_singleton_iff.1 (g⁻¹).2) w.2
        rwa [Subgroup.coe_inv, inv_inv] at this⟩
      left_inv := fun w => Subtype.ext (by
        show (g : X)⁻¹ * ((g : X) * w * (g : X)⁻¹) * g = w
        group)
      right_inv := fun w => Subtype.ext (by
        show (g : X) * ((g : X)⁻¹ * w * g) * (g : X)⁻¹ = w
        group) }
  map_one' := Equiv.ext fun w => Subtype.ext (by
    show ((1 : Subgroup.centralizer ({a * b} : Set X)) : X) * w *
      ((1 : Subgroup.centralizer ({a * b} : Set X)) : X)⁻¹ = w
    rw [Subgroup.coe_one, one_mul, inv_one, mul_one])
  map_mul' g h := Equiv.ext fun w => Subtype.ext (by
    show ((g * h : Subgroup.centralizer ({a * b} : Set X)) : X) * w *
      ((g * h : Subgroup.centralizer ({a * b} : Set X)) : X)⁻¹ =
        (g : X) * ((h : X) * w * (h : X)⁻¹) * (g : X)⁻¹
    rw [Subgroup.coe_mul]
    group)

theorem edgeHomW_val (g : Subgroup.centralizer ({a * b} : Set X))
    (w : ↥(LocalClass E a ∩ LocalClass E b)) :
    ((edgeHomW hE hF ha hb hab hc ψ hψc hZF g w : ↥(LocalClass E a ∩ LocalClass E b)) : X) =
      g * w * (g : X)⁻¹ := rfl

include hψt in
theorem edgeHomW_mem_tauGroup (g : Subgroup.centralizer ({a * b} : Set X)) :
    Equiv.permCongrHom ψ (edgeHomW hE hF ha hb hab hc ψ hψc hZF g) ∈ tauGroup hF := by
  rw [mem_tauGroup]
  intro x y
  obtain ⟨p, rfl⟩ := ψ.surjective x
  obtain ⟨q, rfl⟩ := ψ.surjective y
  set ρ := edgeHomW hE hF ha hb hab hc ψ hψc hZF g
  obtain ⟨hpq, e1⟩ := hψt p q
  have e1' : tauE hF (ψ p) (ψ q) = ψ ⟨_, hpq⟩ := Subtype.ext e1.symm
  obtain ⟨hpq', e2⟩ := hψt (ρ p) (ρ q)
  have e2' : ψ ⟨_, hpq'⟩ = tauE hF (ψ (ρ p)) (ψ (ρ q)) := Subtype.ext e2
  have e3 : ρ ⟨_, hpq⟩ = ⟨_, hpq'⟩ := Subtype.ext (by
    show (g : X) * ((p : X) * q * p) * (g : X)⁻¹ =
      ((g : X) * p * (g : X)⁻¹) * ((g : X) * q * (g : X)⁻¹) * ((g : X) * p * (g : X)⁻¹)
    group)
  show ψ (ρ (ψ.symm (tauE hF (ψ p) (ψ q)))) =
    tauE hF (ψ (ρ (ψ.symm (ψ p)))) (ψ (ρ (ψ.symm (ψ q))))
  rw [e1', Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, e3, e2']

@[expose] noncomputable def edgeHom : Subgroup.centralizer ({a * b} : Set X) →* tauGroup hF :=
  ((Equiv.permCongrHom ψ : Equiv.Perm ↥(LocalClass E a ∩ LocalClass E b) ≃* Equiv.Perm F) :
      Equiv.Perm ↥(LocalClass E a ∩ LocalClass E b) →* Equiv.Perm F).comp
    (edgeHomW hE hF ha hb hab hc ψ hψc hZF) |>.codRestrict (tauGroup hF)
    (edgeHomW_mem_tauGroup hE hF ha hb hab hc ψ hψc hψt hZF)

theorem edgeHom_apply (g : Subgroup.centralizer ({a * b} : Set X))
    (w : ↥(LocalClass E a ∩ LocalClass E b)) :
    ((edgeHom hE hF ha hb hab hc ψ hψc hψt hZF g : Equiv.Perm F) (ψ w)) =
      ψ (edgeHomW hE hF ha hb hab hc ψ hψc hZF g w) := by
  show ψ (edgeHomW hE hF ha hb hab hc ψ hψc hZF g (ψ.symm (ψ w))) = _
  rw [Equiv.symm_apply_apply]

theorem edgeHom_eq_one_iff (g : Subgroup.centralizer ({a * b} : Set X)) :
    edgeHom hE hF ha hb hab hc ψ hψc hψt hZF g = 1 ↔
      ∀ w ∈ LocalClass E a ∩ LocalClass E b, (g : X) * w * (g : X)⁻¹ = w := by
  constructor
  · intro h w hw
    have := edgeHom_apply hE hF ha hb hab hc ψ hψc hψt hZF g ⟨w, hw⟩
    rw [h] at this
    have h' := ψ.injective this.symm
    exact congrArg Subtype.val h'
  · intro h
    apply Subtype.ext
    refine Equiv.ext fun x => ?_
    obtain ⟨w, rfl⟩ := ψ.surjective x
    rw [edgeHom_apply]
    show ψ _ = ψ w
    congr 1
    exact Subtype.ext (h w w.2)

theorem edgeHom_not_mem_range (n : ℕ) {g : Subgroup.centralizer ({a * b} : Set X)}
    (hg2 : g * g = 1)
    (hn : Nat.card {w : ↥(LocalClass E a ∩ LocalClass E b) // (g : X) * w * (g : X)⁻¹ = w} = n)
    (hnF : n ≠ Nat.card F)
    (hfix : ∀ y : Y, y ^ 2 = 1 → y ≠ 1 → Nat.card {x : F // y * (x : Y) * y⁻¹ = x} ≠ n) :
    edgeHom hE hF ha hb hab hc ψ hψc hψt hZF g ∉ (innerTau hF).range := by
  rintro ⟨y, hy⟩
  have hcount : Nat.card {x : F // (edgeHom hE hF ha hb hab hc ψ hψc hψt hZF g :
      Equiv.Perm F) x = x} = n := by
    rw [← hn]
    refine Nat.card_congr (Equiv.subtypeEquiv ψ.symm fun x => ?_)
    obtain ⟨w, rfl⟩ := ψ.surjective x
    rw [Equiv.symm_apply_apply, edgeHom_apply, ψ.injective.eq_iff, Subtype.ext_iff,
      edgeHomW_val]
  have hy2 : y ^ 2 = 1 := by
    apply innerTau_injective hF hZF
    rw [map_pow, hy, ← map_pow, pow_two, hg2, map_one, map_one]
  by_cases hy1 : y = 1
  · subst hy1
    rw [map_one] at hy
    have hall : ∀ x : F,
        (edgeHom hE hF ha hb hab hc ψ hψc hψt hZF g : Equiv.Perm F) x = x := by
      intro x
      rw [← hy]
      rfl
    apply hnF
    rw [← hcount, Nat.card_congr (Equiv.subtypeUnivEquiv hall)]
  · apply hfix y hy2 hy1
    rw [← hcount]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [← hy, Subtype.ext_iff, innerTau_apply]

variable (hidx : (innerTau hF).range.index = 2) {C : Subgroup X}
  (hC : C ≤ Subgroup.centralizer ({a * b} : Set X))

noncomputable abbrev edgeHomC : C →* tauGroup hF :=
  (edgeHom hE hF ha hb hab hc ψ hψc hψt hZF).comp (Subgroup.inclusion hC)

noncomputable abbrev edgeHomL : ↥(C ⊓ Subgroup.centralizer ({a} : Set X)) →* tauGroup hF :=
  (edgeHom hE hF ha hb hab hc ψ hψc hψt hZF).comp (Subgroup.inclusion (inf_le_left.trans hC))

include hidx in
theorem range_edgeHomL_le
    (hLperf : commutator ↥(C ⊓ Subgroup.centralizer ({a} : Set X)) = ⊤) :
    (edgeHomL hE hF ha hb hab hc ψ hψc hψt hZF hC).range ≤ (innerTau hF).range := by
  rw [MonoidHom.range_eq_map, ← hLperf, commutator_def, Subgroup.map_commutator]
  refine le_trans (Subgroup.commutator_mono le_top le_top) ?_
  rw [← commutator_def]
  exact commutator_le_of_index_two hidx

theorem mul_mem_ker_edge (hab' : a * b ∈ C) :
    edgeHomC hE hF ha hb hab hc ψ hψc hψt hZF hC ⟨a * b, hab'⟩ = 1 := by
  rw [MonoidHom.comp_apply, edgeHom_eq_one_iff]
  intro w hw
  have ha' : w * a = a * w := hw.1.2.2
  have hb' : w * b = b * w := hw.2.2.2
  have h1 : a * b * w = w * (a * b) := by
    rw [mul_assoc, ← hb', ← mul_assoc, ← ha', mul_assoc]
  show a * b * w * (a * b)⁻¹ = w
  rw [h1, mul_inv_cancel_right]

include hidx in
theorem range_edgeHomL
    (hLperf : commutator ↥(C ⊓ Subgroup.centralizer ({a} : Set X)) = ⊤)
    (hLcard : Nat.card ↥(C ⊓ Subgroup.centralizer ({a} : Set X)) = Nat.card (tauGroup hF))
    (hker : ∀ ℓ ∈ C ⊓ Subgroup.centralizer ({a} : Set X),
      (∀ w ∈ LocalClass E a ∩ LocalClass E b, ℓ * w * ℓ⁻¹ = w) → ℓ = 1 ∨ ℓ = a * b) :
    (edgeHomL hE hF ha hb hab hc ψ hψc hψt hZF hC).range = (innerTau hF).range := by
  have := Pair.finite hF
  have := Pair.finite hE
  set ρ := edgeHomL hE hF ha hb hab hc ψ hψc hψt hZF hC
  have hle := range_edgeHomL_le hE hF ha hb hab hc ψ hψc hψt hZF hidx hC hLperf
  have hkerle : Nat.card ρ.ker ≤ 2 := by
    have hsub : (ρ.ker : Set ↥(C ⊓ Subgroup.centralizer ({a} : Set X))) ⊆
        {ℓ | (ℓ : X) = 1 ∨ (ℓ : X) = a * b} := by
      intro ℓ hℓ
      apply hker ℓ ℓ.2
      intro w hw
      have h1 : edgeHom hE hF ha hb hab hc ψ hψc hψt hZF
          (Subgroup.inclusion (inf_le_left.trans hC) ℓ) = 1 := hℓ
      exact (edgeHom_eq_one_iff hE hF ha hb hab hc ψ hψc hψt hZF _).1 h1 w hw
    have h2 : ({ℓ | (ℓ : X) = 1 ∨ (ℓ : X) = a * b} :
        Set ↥(C ⊓ Subgroup.centralizer ({a} : Set X))).ncard ≤ 2 := by
      have hinj : Set.InjOn (fun ℓ : ↥(C ⊓ Subgroup.centralizer ({a} : Set X)) => (ℓ : X))
          {ℓ | (ℓ : X) = 1 ∨ (ℓ : X) = a * b} := fun x _ y _ h => Subtype.ext h
      rw [← hinj.ncard_image]
      calc _ ≤ ({1, a * b} : Set X).ncard := Set.ncard_le_ncard (by
              rintro _ ⟨ℓ, hℓ, rfl⟩
              rcases hℓ with h | h
              · exact Or.inl h
              · exact Or.inr h) (Set.toFinite _)
        _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    calc Nat.card ρ.ker = (ρ.ker : Set ↥(C ⊓ Subgroup.centralizer ({a} : Set X))).ncard :=
          (Nat.card_coe_set_eq _).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := h2
  have hcardL : Nat.card ↥(C ⊓ Subgroup.centralizer ({a} : Set X)) =
      Nat.card ρ.ker * Nat.card ρ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, mul_comm,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hinner := (innerTau hF).range.card_mul_index
  rw [hidx] at hinner
  apply Subgroup.eq_of_le_of_card_ge hle
  have hpos : 0 < Nat.card (tauGroup hF) := Nat.card_pos
  nlinarith [Nat.card_pos (α := ρ.range)]

include hidx in
theorem edgeHomC_surjective
    (hLperf : commutator ↥(C ⊓ Subgroup.centralizer ({a} : Set X)) = ⊤)
    (hLcard : Nat.card ↥(C ⊓ Subgroup.centralizer ({a} : Set X)) = Nat.card (tauGroup hF))
    (hker : ∀ ℓ ∈ C ⊓ Subgroup.centralizer ({a} : Set X),
      (∀ w ∈ LocalClass E a ∩ LocalClass E b, ℓ * w * ℓ⁻¹ = w) → ℓ = 1 ∨ ℓ = a * b)
    {e : X} (heC : e ∈ C)
    (hout : edgeHom hE hF ha hb hab hc ψ hψc hψt hZF ⟨e, hC heC⟩ ∉ (innerTau hF).range) :
    Function.Surjective (edgeHomC hE hF ha hb hab hc ψ hψc hψt hZF hC) := by
  rw [← MonoidHom.range_eq_top]
  refine eq_top_of_index_two hidx ?_ ⟨⟨e, heC⟩, rfl⟩ hout
  rw [← range_edgeHomL hE hF ha hb hab hc ψ hψc hψt hZF hidx hC hLperf hLcard hker]
  rintro _ ⟨ℓ, rfl⟩
  exact ⟨⟨ℓ, ℓ.2.1⟩, rfl⟩

include hE hb hab in
theorem mul_ne_one_edge : a * b ≠ 1 := by
  intro h
  apply hab
  calc a = a * b * b⁻¹ := by group
    _ = b := by rw [h, one_mul, Pair.inv_eq hE hb]

theorem edgeHomC_ker (hsurj : Function.Surjective (edgeHomC hE hF ha hb hab hc ψ hψc hψt hZF hC))
    (hcard : Nat.card C = 2 * Nat.card (tauGroup hF)) (hab' : a * b ∈ C) (c : C)
    (h : edgeHomC hE hF ha hb hab hc ψ hψc hψt hZF hC c = 1) :
    (c : X) = 1 ∨ (c : X) = a * b := by
  have := Pair.finite hE
  have := Pair.finite hF
  set ρ := edgeHomC hE hF ha hb hab hc ψ hψc hψt hZF hC
  have hcardC : Nat.card C = Nat.card ρ.ker * Nat.card ρ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, mul_comm,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  rw [MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top, hcard] at hcardC
  have hpos : 0 < Nat.card (tauGroup hF) := Nat.card_pos
  have hk : Nat.card ρ.ker = 2 := by nlinarith
  by_contra hne
  push Not at hne
  have h3 : ({1, ⟨a * b, hab'⟩, c} : Set C) ⊆ ρ.ker := by
    rintro x (rfl | rfl | rfl)
    · exact ρ.ker.one_mem
    · exact mul_mem_ker_edge hE hF ha hb hab hc ψ hψc hψt hZF hC hab'
    · exact h
  have hne1 : (1 : C) ≠ ⟨a * b, hab'⟩ := fun e =>
    mul_ne_one_edge hE hb hab (congrArg Subtype.val e).symm
  have hne2 : (1 : C) ≠ c := fun e => hne.1 (congrArg Subtype.val e).symm
  have hne3 : (⟨a * b, hab'⟩ : C) ≠ c := fun e => hne.2 (congrArg Subtype.val e).symm
  have hc3 : ({1, ⟨a * b, hab'⟩, c} : Set C).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hne1, hne2]), Set.ncard_pair hne3]
  have h4 := Set.ncard_le_ncard h3 (Set.toFinite _)
  have h5 : (ρ.ker : Set C).ncard = 2 := by rw [← Nat.card_coe_set_eq]; exact hk
  omega

theorem center_edgeC (hsurj : Function.Surjective (edgeHomC hE hF ha hb hab hc ψ hψc hψt hZF hC))
    (hcard : Nat.card C = 2 * Nat.card (tauGroup hF)) (hab' : a * b ∈ C) {z : C}
    (hz : z ∈ Subgroup.center C) : (z : X) = 1 ∨ (z : X) = a * b := by
  set ρ := edgeHomC hE hF ha hb hab hc ψ hψc hψt hZF hC
  apply edgeHomC_ker hE hF ha hb hab hc ψ hψc hψt hZF hC hsurj hcard hab' z
  have hcen : ρ z ∈ Subgroup.center (tauGroup hF) := by
    rw [Subgroup.mem_center_iff]
    intro σ
    obtain ⟨c, rfl⟩ := hsurj σ
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz c)]
  rw [center_tauGroup_eq_bot hF hZF, Subgroup.mem_bot] at hcen
  exact hcen

include hC in
theorem mul_mem_center_edgeC (hab' : a * b ∈ C) :
    (⟨a * b, hab'⟩ : C) ∈ Subgroup.center C := by
  rw [Subgroup.mem_center_iff]
  intro c
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.1 (hC c.2)

include hidx in
theorem outTwo_edgeC (hcomp : ∀ φ : MulAut (tauGroup hF), ∃ σ, φ = MulAut.conj σ)
    (hLperf : commutator ↥(C ⊓ Subgroup.centralizer ({a} : Set X)) = ⊤)
    (hLcard : Nat.card ↥(C ⊓ Subgroup.centralizer ({a} : Set X)) = Nat.card (tauGroup hF))
    (hker : ∀ ℓ ∈ C ⊓ Subgroup.centralizer ({a} : Set X),
      (∀ w ∈ LocalClass E a ∩ LocalClass E b, ℓ * w * ℓ⁻¹ = w) → ℓ = 1 ∨ ℓ = a * b)
    (hcard : Nat.card C = 2 * Nat.card (tauGroup hF)) (hab' : a * b ∈ C)
    {e : X} (heC : e ∈ C)
    (hout : edgeHom hE hF ha hb hab hc ψ hψc hψt hZF ⟨e, hC heC⟩ ∉ (innerTau hF).range) :
    OutTwo C := by
  have hsurj := edgeHomC_surjective hE hF ha hb hab hc ψ hψc hψt hZF hidx hC hLperf hLcard hker
    heC hout
  set ρ := edgeHomC hE hF ha hb hab hc ψ hψc hψt hZF hC
  have hab2 : a * b * (a * b) = 1 := by
    rw [show a * b * (a * b) = a * (b * a) * b by group, ← hc,
      show a * (a * b) * b = (a * a) * (b * b) by group, Pair.mul_self hE ha, Pair.mul_self hE hb,
      one_mul]
  have hkerZ : ρ.ker = Subgroup.center C := by
    apply le_antisymm
    · intro c hc'
      rcases edgeHomC_ker hE hF ha hb hab hc ψ hψc hψt hZF hC hsurj hcard hab' c hc' with h | h
      · rw [show c = 1 from Subtype.ext h]
        exact Subgroup.one_mem _
      · rw [show c = ⟨a * b, hab'⟩ from Subtype.ext h]
        exact mul_mem_center_edgeC hC hab'
    · intro z hz
      rcases center_edgeC hE hF ha hb hab hc ψ hψc hψt hZF hC hsurj hcard hab' hz with h | h
      · rw [show z = 1 from Subtype.ext h]
        exact Subgroup.one_mem _
      · rw [show z = ⟨a * b, hab'⟩ from Subtype.ext h]
        exact mul_mem_ker_edge hE hF ha hb hab hc ψ hψc hψt hZF hC hab'
  let eQ : (C ⧸ Subgroup.center C) ≃* tauGroup hF :=
    (QuotientGroup.quotientMulEquivOfEq hkerZ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hsurj)
  refine outTwo_of_complete_quotient (complete_of_mulEquiv eQ.symm hcomp) ?_ ?_
  ·
    intro z hz
    rcases center_edgeC hE hF ha hb hab hc ψ hψc hψt hZF hC hsurj hcard hab' hz with h | h
    · rw [show z = 1 from Subtype.ext h]
      exact Subgroup.one_mem _
    · rw [show z = ⟨a * b, hab'⟩ from Subtype.ext h]
      have habL : a * b ∈ C ⊓ Subgroup.centralizer ({a} : Set X) := ⟨hab',
        Subgroup.mem_centralizer_singleton_iff.2 (by rw [mul_assoc, ← hc])⟩
      have h1 : (⟨a * b, habL⟩ : ↥(C ⊓ Subgroup.centralizer ({a} : Set X))) ∈
          commutator ↥(C ⊓ Subgroup.centralizer ({a} : Set X)) := by
        rw [hLperf]; trivial
      have h2 := Subgroup.mem_map_of_mem (Subgroup.inclusion (inf_le_left :
        C ⊓ Subgroup.centralizer ({a} : Set X) ≤ C)) h1
      rw [commutator_def, Subgroup.map_commutator] at h2
      exact Subgroup.commutator_mono le_top le_top h2
  · intro z hz
    rcases center_edgeC hE hF ha hb hab hc ψ hψc hψt hZF hC hsurj hcard hab' hz with h | h
    · rw [show z = 1 from Subtype.ext h, one_mul]
    · apply Subtype.ext
      rw [Subgroup.coe_mul, h, hab2]
      rfl

end Edge

end CFSG.Fischer
