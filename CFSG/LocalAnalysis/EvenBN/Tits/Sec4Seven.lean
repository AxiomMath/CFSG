module

public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4ClassesTwo
public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.Manning

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits
open CFSG.Quasithin (twoF4H twoF4N)
open scoped commutatorElement

theorem card_eq_ncard_conj_mul {G : Type*} [Group G] [Finite G] (K : Subgroup G) (x : G) :
    Nat.card K = {y | ∃ k ∈ K, k * x * k⁻¹ = y}.ncard *
      Nat.card (K ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  let _ : MulAction K G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp K.subtype)
  have hsmul : ∀ (k : K) (y : G), k • y = (k : G) * y * (k : G)⁻¹ := fun k y => by
    change (MulAut.conj (k : G)) • y = _
    rw [MulAut.smul_def, MulAut.conj_apply]
  have horb : (MulAction.orbit K x : Set G) = {y | ∃ k ∈ K, k * x * k⁻¹ = y} := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, (hsmul k x).symm⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, hsmul _ _⟩
  have e : MulAction.stabilizer K x ≃ (K ⊓ centralizer ({x} : Set G) : Subgroup G) :=
    { toFun := fun k => ⟨k.1.1, mem_inf.2 ⟨k.1.2, mem_centralizer_singleton_iff.2 (by
        have h : (k.1 : G) * x * (k.1 : G)⁻¹ = x := (hsmul k.1 x).symm.trans k.2
        calc (k.1 : G) * x = (k.1 : G) * x * (k.1 : G)⁻¹ * k.1 := by group
          _ = x * k.1 := by rw [h])⟩⟩
      invFun := fun k => ⟨⟨k.1, (mem_inf.1 k.2).1⟩, by
        change (⟨k.1, (mem_inf.1 k.2).1⟩ : K) • x = x
        rw [hsmul]
        have h := mem_centralizer_singleton_iff.1 (mem_inf.1 k.2).2
        change (k : G) * x * (k : G)⁻¹ = x
        rw [h, mul_inv_cancel_right]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← manning_card_orbit_mul_card_stabilizer (M := K) x, Nat.card_congr e, ← horb,
    Nat.card_coe_set_eq]

theorem conj_mem_normalizer_map {G : Type*} [Group G] {X : Subgroup G} {g m : G}
    (hm : m ∈ normalizer (X : Set G)) :
    g * m * g⁻¹ ∈ normalizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  rw [Model.mem_map_conj_iff, Model.mem_map_conj_iff, (mem_normalizer_iff.1 hm) (g⁻¹ * h * g)]
  have e : g⁻¹ * (g * m * g⁻¹ * h * (g * m * g⁻¹)⁻¹) * g = m * (g⁻¹ * h * g) * m⁻¹ := by group
  rw [e]

theorem card_normalizer_map_conj {G : Type*} [Group G] [Finite G] (X : Subgroup G) (g : G) :
    Nat.card (normalizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) =
      Nat.card (normalizer (X : Set G)) := by
  have key : ∀ (Y : Subgroup G) (a : G), Nat.card (normalizer (Y : Set G)) ≤
      Nat.card (normalizer ((Y.map (MulAut.conj a).toMonoidHom : Subgroup G) : Set G)) := by
    intro Y a
    let f : normalizer (Y : Set G) →
        normalizer ((Y.map (MulAut.conj a).toMonoidHom : Subgroup G) : Set G) :=
      fun m => ⟨a * m * a⁻¹, conj_mem_normalizer_map m.2⟩
    refine Nat.card_le_card_of_injective f fun m₁ m₂ h => Subtype.ext ?_
    have h' : a * (m₁ : G) * a⁻¹ = a * m₂ * a⁻¹ := congrArg Subtype.val h
    simpa using h'
  apply le_antisymm _ (key X g)
  have h := key (X.map (MulAut.conj g).toMonoidHom) g⁻¹
  rwa [Model.map_conj_map_conj, inv_mul_cancel, Model.map_conj_one] at h

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

@[expose] def tG (d : Data G) : Set G := {s | ∃ g : G, g * d.t * g⁻¹ = s}

theorem Hyp.card_eq_two_mul_map
    (hd : d.Hyp) {K : Subgroup G} (hK : K ≤ centralizer ({d.t} : Set G)) (htK : d.t ∈ K) :
    Nat.card K = 2 * Nat.card ((K.subgroupOf (centralizer ({d.t} : Set G))).map d.ρ) := by
  set K' := K.subgroupOf (centralizer ({d.t} : Set G)) with hK'
  set φ := d.ρ.domRestrict K' with hφ
  have hrange : φ.range = K'.map d.ρ := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : d.ρ.ker ≤ K' := by
    intro x hx
    have hxG : (x : G) ∈ d.ρ.ker.map (centralizer ({d.t} : Set G)).subtype := ⟨x, hx, rfl⟩
    rw [Model.ker_ρ_eq_zpowers_of_hyp hd, Model.mem_zpowers_of_orderOf_two hd.t_two] at hxG
    rw [mem_subgroupOf]
    rcases hxG with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact htK
  have hker2 : Nat.card d.ρ.ker = 2 := by
    have h := card_map_of_injective (K := d.ρ.ker)
      (subtype_injective (centralizer ({d.t} : Set G)))
    rw [Model.ker_ρ_eq_zpowers_of_hyp hd, Nat.card_zpowers, hd.t_two] at h
    exact h.symm
  have hcard := card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange,
    MonoidHom.ker_domRestrict, Nat.card_congr (subgroupOfEquivOfLe hker).toEquiv, hker2] at hcard
  rw [Nat.card_congr (subgroupOfEquivOfLe hK).symm.toEquiv, hcard, mul_comm]

theorem Hyp.card_normalizer_tSup
    (hd : d.Hyp) {X Y : Subgroup (Equiv.Perm (Fin 1755))} (hXD : X ≤ titsD)
    (hY : titsA ⊓ normalizer (X : Set (Equiv.Perm (Fin 1755))) = Y) :
    Nat.card (normalizer ((d.liftSub X ⊔ zpowers d.t : Subgroup G) : Set G) ⊓
        centralizer ({d.t} : Set G) : Subgroup G) =
      2 * Nat.card (Y.subgroupOf titsA ⊓ d.ρ.range : Subgroup titsA) := by
  have htN : d.t ∈ normalizer ((d.liftSub X ⊔ zpowers d.t : Subgroup G) : Set G) := by
    rw [hd.mem_normalizer_tSup_iff hXD d.t_mem_centralizer, hd.ρ_t]
    exact one_mem _
  have heq : ((normalizer ((d.liftSub X ⊔ zpowers d.t : Subgroup G) : Set G) ⊓
      centralizer ({d.t} : Set G)).subgroupOf (centralizer ({d.t} : Set G))).map d.ρ =
      Y.subgroupOf titsA ⊓ d.ρ.range := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hxN, -⟩ := mem_inf.1 (mem_subgroupOf.1 hx)
      have hρ := (hd.mem_normalizer_tSup_iff hXD x.2).1 hxN
      exact mem_inf.2 ⟨mem_subgroupOf.2 (hY ▸ mem_inf.2 ⟨(d.ρ x).2, hρ⟩), ⟨x, rfl⟩⟩
    · rintro ha
      obtain ⟨haY, ⟨x, rfl⟩⟩ := mem_inf.1 ha
      rw [mem_subgroupOf, ← hY] at haY
      have hxN := (hd.mem_normalizer_tSup_iff hXD x.2).2 (mem_inf.1 haY).2
      exact ⟨x, mem_subgroupOf.2 (mem_inf.2 ⟨hxN, x.2⟩), rfl⟩
  rw [hd.card_eq_two_mul_map inf_le_right (mem_inf.2 ⟨htN, d.t_mem_centralizer⟩), heq]

theorem card_inf_titsD {Y : Subgroup (Equiv.Perm (Fin 1755))}
    (hYA : Y ≤ titsA) :
    Nat.card (Y.subgroupOf titsA ⊓ titsD.subgroupOf titsA : Subgroup titsA) =
      Nat.card (Y ⊓ titsD : Subgroup (Equiv.Perm (Fin 1755))) := by
  have e : Y.subgroupOf titsA ⊓ titsD.subgroupOf titsA = (Y ⊓ titsD).subgroupOf titsA := by
    ext x
    simp [mem_subgroupOf]
  rw [e]
  exact Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hYA)).toEquiv

theorem card_inf_top {Y : Subgroup (Equiv.Perm (Fin 1755))} (hYA : Y ≤ titsA) :
    Nat.card (Y.subgroupOf titsA ⊓ ⊤ : Subgroup titsA) = Nat.card Y := by
  rw [inf_top_eq]
  exact Nat.card_congr (subgroupOfEquivOfLe hYA).toEquiv

theorem Hyp.card_CM_CN
    (hd : d.Hyp) :
    3 * Nat.card (d.M ⊓ centralizer ({d.t} : Set G) : Subgroup G) =
        5 * Nat.card (d.N ⊓ centralizer ({d.t} : Set G) : Subgroup G) ∧
      Nat.card (centralizer ({d.t} : Set G)) =
        1755 * Nat.card (d.M ⊓ centralizer ({d.t} : Set G) : Subgroup G) := by
  have hM : Nat.card (d.M ⊓ centralizer ({d.t} : Set G) : Subgroup G) =
      2 * Nat.card (twoF4H.subgroupOf titsA ⊓ d.ρ.range : Subgroup titsA) :=
    hd.card_normalizer_tSup (Model.hatE_le_titsJ.trans titsJ_le_titsD)
      Model.titsA_inf_normalizer_hatE
  have hN : Nat.card (d.N ⊓ centralizer ({d.t} : Set G) : Subgroup G) =
      2 * Nat.card (twoF4N.subgroupOf titsA ⊓ d.ρ.range : Subgroup titsA) :=
    hd.card_normalizer_tSup Model.parrottF_le_titsD Model.titsA_inf_normalizer_parrottF
  have hC := hd.card_centralizer_eq_two_mul Model.hypothesisOneStar_titsD
  rcases hd.range_ρ with hR | hR
  · rw [hR, card_inf_titsD Model.twoF4H_le_titsA, Model.twoF4H_inf_titsD,
      titsQH_facts.2.2.2] at hM
    rw [hR, card_inf_titsD Model.twoF4N_le_titsA, Model.card_twoF4N.2.1,
      titsQN_facts.2.2.2] at hN
    rw [hR, Nat.card_congr (subgroupOfEquivOfLe titsD_le_titsA).toEquiv, card_titsD] at hC
    rw [hM, hN, hC]
    norm_num
  · rw [hR, card_inf_top Model.twoF4H_le_titsA, Model.card_twoF4H] at hM
    rw [hR, card_inf_top Model.twoF4N_le_titsA, Model.card_twoF4N.1] at hN
    rw [hR, card_top, card_titsA] at hC
    rw [hM, hN, hC]
    norm_num

theorem ncard_of_cover {α : Type*} [Finite α] {O S₀ S₁ S₂ S₃ : Set α}
    (hO : O ⊆ S₀ ∪ S₁ ∪ S₂ ∪ S₃) (d01 : Disjoint S₀ S₁) (d02 : Disjoint S₀ S₂)
    (d03 : Disjoint S₀ S₃) (d12 : Disjoint S₁ S₂) (d13 : Disjoint S₁ S₃) (d23 : Disjoint S₂ S₃)
    (h₀ : S₀ ⊆ O) (h₁ : O ∩ S₁ = ∅ ∨ S₁ ⊆ O) (h₂ : O ∩ S₂ = ∅ ∨ S₂ ⊆ O)
    (h₃ : O ∩ S₃ = ∅ ∨ S₃ ⊆ O) :
    ∃ a b c : ℕ, (a = 0 ∨ a = S₁.ncard) ∧ (b = 0 ∨ b = S₂.ncard) ∧ (c = 0 ∨ c = S₃.ncard) ∧
      (S₁ ⊆ O → a = S₁.ncard) ∧ (S₂ ⊆ O → b = S₂.ncard) ∧ O.ncard = S₀.ncard + a + b + c := by
  have hOeq : O = S₀ ∪ (O ∩ S₁) ∪ (O ∩ S₂) ∪ (O ∩ S₃) := by
    ext x
    constructor
    · intro hx
      rcases hO hx with ((h | h) | h) | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr ⟨hx, h⟩))
      · exact Or.inl (Or.inr ⟨hx, h⟩)
      · exact Or.inr ⟨hx, h⟩
    · rintro (((h | h) | h) | h)
      · exact h₀ h
      · exact h.1
      · exact h.1
      · exact h.1
  have key : ∀ {S : Set α}, (O ∩ S = ∅ ∨ S ⊆ O) → ((O ∩ S).ncard = 0 ∨ (O ∩ S).ncard = S.ncard) :=
    fun {S} h => by
      rcases h with h | h
      · left
        rw [h, Set.ncard_empty]
      · right
        rw [Set.inter_eq_right.2 h]
  refine ⟨(O ∩ S₁).ncard, (O ∩ S₂).ncard, (O ∩ S₃).ncard, key h₁, key h₂, key h₃,
    fun h => by rw [Set.inter_eq_right.2 h], fun h => by rw [Set.inter_eq_right.2 h], ?_⟩
  have e1 : Disjoint S₀ (O ∩ S₁) := d01.mono_right Set.inter_subset_right
  have e2 : Disjoint (S₀ ∪ (O ∩ S₁)) (O ∩ S₂) :=
    Disjoint.union_left (d02.mono_right Set.inter_subset_right)
      ((d12.mono_left Set.inter_subset_right).mono_right Set.inter_subset_right)
  have e3 : Disjoint (S₀ ∪ (O ∩ S₁) ∪ (O ∩ S₂)) (O ∩ S₃) :=
    Disjoint.union_left (Disjoint.union_left (d03.mono_right Set.inter_subset_right)
      ((d13.mono_left Set.inter_subset_right).mono_right Set.inter_subset_right))
      ((d23.mono_left Set.inter_subset_right).mono_right Set.inter_subset_right)
  conv_lhs => rw [hOeq]
  rw [Set.ncard_union_eq e3 (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq e2 (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq e1 (Set.toFinite _) (Set.toFinite _)]

omit [Finite G] in
theorem inter_orbit_eq_empty_or_subset {K : Subgroup G} {t u₀ : G}
    (hKt : ∀ c ∈ K, c * t = t * c) {O : Set G} (hO : ∀ c ∈ K, ∀ s ∈ O, c * s * c⁻¹ ∈ O) :
    O ∩ ((fun u => t * u) '' {y | ∃ c ∈ K, c * u₀ * c⁻¹ = y}) = ∅ ∨
      (fun u => t * u) '' {y | ∃ c ∈ K, c * u₀ * c⁻¹ = y} ⊆ O := by
  by_cases h : ∃ s, s ∈ O ∩ ((fun u => t * u) '' {y | ∃ c ∈ K, c * u₀ * c⁻¹ = y})
  · right
    obtain ⟨_, hsO, ⟨_, ⟨c₀, hc₀, rfl⟩, rfl⟩⟩ := h
    rintro _ ⟨_, ⟨c₁, hc₁, rfl⟩, rfl⟩
    have hk : c₁ * c₀⁻¹ ∈ K := mul_mem hc₁ (inv_mem hc₀)
    have h1 := hO _ hk _ hsO
    have e : c₁ * c₀⁻¹ * (t * (c₀ * u₀ * c₀⁻¹)) * (c₁ * c₀⁻¹)⁻¹ = t * (c₁ * u₀ * c₁⁻¹) := by
      calc c₁ * c₀⁻¹ * (t * (c₀ * u₀ * c₀⁻¹)) * (c₁ * c₀⁻¹)⁻¹ =
          (c₁ * c₀⁻¹ * t) * (c₀ * u₀ * c₀⁻¹) * (c₁ * c₀⁻¹)⁻¹ := by group
        _ = (t * (c₁ * c₀⁻¹)) * (c₀ * u₀ * c₀⁻¹) * (c₁ * c₀⁻¹)⁻¹ := by rw [hKt _ hk]
        _ = t * (c₁ * u₀ * c₁⁻¹) := by group
    rw [e] at h1
    exact h1
  · left
    exact Set.eq_empty_iff_forall_notMem.2 fun s hs => h ⟨s, hs⟩

omit [Finite G] in
theorem zL_vL_disjoint
    (d : Data G) : (1 : G) ∉ d.zL ∧ (1 : G) ∉ d.vL ∧ Disjoint d.zL d.vL := by
  refine ⟨fun h => ?_, fun h => ?_, ?_⟩
  · rw [zL_eq] at h
    obtain ⟨x, ⟨hxD, hxl⟩, hx1⟩ := h
    rw [← d.lift_one] at hx1
    exact hxl.ne_one (d.lift_inj hxD (one_mem _) hx1)
  · rw [vL_eq] at h
    obtain ⟨x, ⟨hxD, hxs⟩, hx1⟩ := h
    rw [← d.lift_one] at hx1
    exact hxs.ne_one (d.lift_inj hxD (one_mem _) hx1)
  · rw [zL_eq, vL_eq, Set.disjoint_left]
    rintro _ ⟨x, ⟨hxD, hxl⟩, rfl⟩ ⟨y, ⟨hyD, hys⟩, hyx⟩
    rw [d.lift_inj hyD hxD hyx] at hys
    exact Model.not_isLong_of_isShort hys hxl

omit [Finite G] in
theorem mem_zL_or_vL (d : Data G)
    {X : Subgroup (Equiv.Perm (Fin 1755))}
    (hX : ∀ x ∈ X, x ≠ 1 → Model.IsLong x ∨ Model.IsShort x) {e : G} (he : e ∈ d.liftSub X)
    (he1 : e ≠ 1) : e ∈ d.zL ∨ e ∈ d.vL := by
  obtain ⟨x, hx, hxD, rfl⟩ := mem_liftSub.1 he
  have hx1 : x ≠ 1 := fun h => he1 (by rw [h, d.lift_one])
  rcases hX x hx hx1 with h | h
  · exact Or.inl (by rw [zL_eq]; exact ⟨x, ⟨hxD, h⟩, rfl⟩)
  · exact Or.inr (by rw [vL_eq]; exact ⟨x, ⟨hxD, h⟩, rfl⟩)

theorem Hyp.t_mul_mem_of_mem_tG
    (hd : d.Hyp) {P : Subgroup G} (hPL : P ≤ d.L) {s : G} (hs : s ∈ d.tG)
    (hsD : s ∈ P ⊔ zpowers d.t) : d.t * s ∈ P := by
  rcases ((hd.tSup_facts hPL).1 s).1 hsD with h | h
  · obtain ⟨g, rfl⟩ := hs
    exact absurd (hPL h) (hd.conj_t_not_mem g)
  · exact h

theorem Hyp.t_mul_mem_tG_of_zL
    (hd : d.Hyp) {u : G} (hu : u ∈ d.zL) : d.t * u ∈ d.tG := by
  obtain ⟨l, hl, rfl⟩ := hu
  obtain ⟨g, hg⟩ := hd.exists_conj_eq_t_mul_z
  refine ⟨l * g, ?_⟩
  have hc := hd.L_comm_t hl
  calc l * g * d.t * (l * g)⁻¹ = l * (g * d.t * g⁻¹) * l⁻¹ := by group
    _ = l * (d.t * d.z) * l⁻¹ := by rw [hg]
    _ = (l * d.t) * d.z * l⁻¹ := by group
    _ = d.t * (l * d.z * l⁻¹) := by rw [hc]; group

theorem Hyp.t_mul_mem_tG_iff_of_vL (hd : d.Hyp) {w : G}
    (hw : w ∈ d.vL) : d.t * w ∈ d.tG ↔ d.t * d.v ∈ d.tG := by
  obtain ⟨l, hl, rfl⟩ := hw
  have hc := hd.L_comm_t hl
  have e : d.t * (l * d.v * l⁻¹) = l * (d.t * d.v) * l⁻¹ := by
    calc d.t * (l * d.v * l⁻¹) = (d.t * l) * d.v * l⁻¹ := by group
      _ = (l * d.t) * d.v * l⁻¹ := by rw [hc]
      _ = l * (d.t * d.v) * l⁻¹ := by group
  rw [e]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨l⁻¹ * g, ?_⟩
    calc l⁻¹ * g * d.t * (l⁻¹ * g)⁻¹ = l⁻¹ * (g * d.t * g⁻¹) * l := by group
      _ = d.t * d.v := by rw [hg]; group
  · rintro ⟨g, hg⟩
    refine ⟨l * g, ?_⟩
    calc l * g * d.t * (l * g)⁻¹ = l * (g * d.t * g⁻¹) * l⁻¹ := by group
      _ = l * (d.t * d.v) * l⁻¹ := by rw [hg]

theorem Hyp.ncard_tG_A
    (hd : d.Hyp) {O : Set G} (hOsub : O ⊆ d.tG ∩ d.A) (htO : d.t ∈ O)
    (hinv : ∀ c ∈ d.M ⊓ centralizer ({d.t} : Set G), ∀ s ∈ O, c * s * c⁻¹ ∈ O) :
    ∃ a b c : ℕ, (a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 10) ∧ (c = 0 ∨ c = 20) ∧
      (d.t * d.z ∈ O → a = 1) ∧ ((∀ u ∈ (d.zL ∩ d.A) \ {d.z}, d.t * u ∈ O) → b = 10) ∧
      O.ncard = 1 + a + b + c := by
  obtain ⟨-, -, h11, h10c, h10, h20c⟩ := hd.orbits_A
  have ht2 := hd.t_mul_self
  have hED : Model.hatE ≤ titsD := Model.hatE_le_titsJ.trans titsJ_le_titsD
  obtain ⟨h1z, h1v, hzv⟩ := d.zL_vL_disjoint
  have hKt : ∀ c ∈ d.M ⊓ centralizer ({d.t} : Set G), c * d.t = d.t * c := fun c hc =>
    mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2
  set S₂ := (fun u => d.t * u) '' {y | ∃ c ∈ d.M ⊓ centralizer ({d.t} : Set G),
    c * d.pv 11 * c⁻¹ = y} with hS₂
  set S₃ := (fun u => d.t * u) '' {y | ∃ c ∈ d.M ⊓ centralizer ({d.t} : Set G),
    c * d.pv 10 * c⁻¹ = y} with hS₃
  have hzA : d.z ∈ d.zL := ⟨1, one_mem _, by group⟩
  have htt : ∀ x : G, d.t * (d.t * x) = x := fun x => by rw [← mul_assoc, ht2, one_mul]
  obtain ⟨a, b, c, ha, hb, hc, hsa, hsb, hcard⟩ := ncard_of_cover (O := O) (S₀ := {d.t})
    (S₁ := {d.t * d.z}) (S₂ := S₂) (S₃ := S₃)
    (by
      intro s hs
      obtain ⟨hsG, hsA⟩ := hOsub hs
      have he := hd.t_mul_mem_of_mem_tG (d.liftSub_le _) hsG hsA
      have hs' : s = d.t * (d.t * s) := (htt s).symm
      by_cases he1 : d.t * s = 1
      · left; left; left
        rw [hs', he1, mul_one]
        rfl
      rcases d.mem_zL_or_vL (fun x hx hx1 => Model.hatE_long_or_short hx hx1) he he1 with
        hz | hv
      · by_cases hez : d.t * s = d.z
        · left; left; right
          rw [hs', hez]
          rfl
        · left; right
          rw [hS₂, h11]
          exact ⟨d.t * s, ⟨⟨hz, mem_sup_left he⟩, hez⟩, (htt s)⟩
      · right
        rw [hS₃, h10]
        exact ⟨d.t * s, ⟨hv, mem_sup_left he⟩, (htt s)⟩)
    (by
      rw [Set.disjoint_singleton]
      intro h
      apply h1z
      rw [show (1 : G) = d.z by
        calc (1 : G) = d.t⁻¹ * d.t := by group
          _ = d.t⁻¹ * (d.t * d.z) := by rw [← h]
          _ = d.z := by group]
      exact hzA)
    (by
      rw [Set.disjoint_singleton_left, hS₂, h11]
      rintro ⟨u, ⟨⟨hu, -⟩, -⟩, hut⟩
      apply h1z
      have : u = 1 := by
        calc u = d.t⁻¹ * (d.t * u) := by group
          _ = 1 := by rw [show d.t * u = d.t from hut]; group
      exact this ▸ hu)
    (by
      rw [Set.disjoint_singleton_left, hS₃, h10]
      rintro ⟨w, ⟨hw, -⟩, hwt⟩
      apply h1v
      have : w = 1 := by
        calc w = d.t⁻¹ * (d.t * w) := by group
          _ = 1 := by rw [show d.t * w = d.t from hwt]; group
      exact this ▸ hw)
    (by
      rw [Set.disjoint_singleton_left, hS₂, h11]
      rintro ⟨u, ⟨⟨-, -⟩, huz⟩, hut⟩
      exact huz (mul_left_cancel hut)
      )
    (by
      rw [Set.disjoint_singleton_left, hS₃, h10]
      rintro ⟨w, ⟨hw, -⟩, hwt⟩
      rw [mul_left_cancel hwt] at hw
      exact Set.disjoint_left.1 hzv hzA hw)
    (by
      rw [hS₂, hS₃, h11, h10, Set.disjoint_left]
      rintro _ ⟨u, ⟨⟨hu, -⟩, -⟩, rfl⟩ ⟨w, ⟨hw, -⟩, hwu⟩
      rw [mul_left_cancel hwu] at hw
      exact Set.disjoint_left.1 hzv hu hw)
    (Set.singleton_subset_iff.2 htO)
    (by
      by_cases h : d.t * d.z ∈ O
      · exact Or.inr (Set.singleton_subset_iff.2 h)
      · left
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨hx, rfl⟩
        exact h hx)
    (inter_orbit_eq_empty_or_subset hKt hinv) (inter_orbit_eq_empty_or_subset hKt hinv)
  have hc2 : S₂.ncard = 10 := by
    rw [hS₂, h11, Set.ncard_image_of_injective _ (mul_right_injective d.t), h10c]
  have hc3 : S₃.ncard = 20 := by
    rw [hS₃, h10, Set.ncard_image_of_injective _ (mul_right_injective d.t), h20c]
  rw [Set.ncard_singleton] at ha hsa hcard
  rw [hc2] at hb hsb
  rw [hc3] at hc
  refine ⟨a, b, c, ha, hb, hc, fun h => hsa (Set.singleton_subset_iff.2 h), fun h => hsb ?_,
    hcard⟩
  rw [hS₂, h11]
  rintro _ ⟨u, hu, rfl⟩
  exact h u hu

theorem Hyp.ncard_tG_B
    (hd : d.Hyp) {O : Set G} (hOsub : O ⊆ d.tG ∩ d.B) (htO : d.t ∈ O)
    (hinv : ∀ c ∈ d.N ⊓ centralizer ({d.t} : Set G), ∀ s ∈ O, c * s * c⁻¹ ∈ O) :
    ∃ a b c : ℕ, (a = 0 ∨ a = 3) ∧ (b = 0 ∨ b = 4) ∧ (c = 0 ∨ c = 24) ∧
      O.ncard = 1 + a + b + c := by
  obtain ⟨hz3, -, hz3c, h109, hdisj, h4, h24⟩ := hd.orbits_B
  have ht2 := hd.t_mul_self
  obtain ⟨h1z, h1v, hzv⟩ := d.zL_vL_disjoint
  have hKt : ∀ c ∈ d.N ⊓ centralizer ({d.t} : Set G), c * d.t = d.t * c := fun c hc =>
    mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2
  have htt : ∀ x : G, d.t * (d.t * x) = x := fun x => by rw [← mul_assoc, ht2, one_mul]
  set O₁ := {y | ∃ c ∈ d.N ⊓ centralizer ({d.t} : Set G), c * d.z * c⁻¹ = y} with hO₁
  set O₂ := {y | ∃ c ∈ d.N ⊓ centralizer ({d.t} : Set G), c * d.pv 10 * c⁻¹ = y} with hO₂
  set O₃ := {y | ∃ c ∈ d.N ⊓ centralizer ({d.t} : Set G), c * d.pv 9 * c⁻¹ = y} with hO₃
  have hO₂v : O₂ ⊆ d.vL := fun y hy => (h109 ▸ Or.inl hy : y ∈ d.vL ∩ d.B).1
  have hO₃v : O₃ ⊆ d.vL := fun y hy => (h109 ▸ Or.inr hy : y ∈ d.vL ∩ d.B).1
  have hO₁z : O₁ ⊆ d.zL := fun y hy => (hz3 ▸ hy : y ∈ d.zL ∩ d.B).1
  have hne1 : ∀ {U : Set G}, (1 : G) ∉ U → Disjoint {d.t} ((fun u => d.t * u) '' U) := by
    intro U hU
    rw [Set.disjoint_singleton_left]
    rintro ⟨u, hu, hut⟩
    have : u = 1 := by
      calc u = d.t⁻¹ * (d.t * u) := by group
        _ = 1 := by rw [show d.t * u = d.t from hut]; group
    exact hU (this ▸ hu)
  have hdis : ∀ {U V : Set G}, Disjoint U V →
      Disjoint ((fun u => d.t * u) '' U) ((fun u => d.t * u) '' V) := fun h =>
    (Set.disjoint_image_iff (mul_right_injective d.t)).2 h
  obtain ⟨a, b, c, ha, hb, hc, -, -, hcard⟩ := ncard_of_cover (O := O) (S₀ := {d.t})
    (S₁ := (fun u => d.t * u) '' O₁) (S₂ := (fun u => d.t * u) '' O₂)
    (S₃ := (fun u => d.t * u) '' O₃)
    (by
      intro s hs
      obtain ⟨hsG, hsB⟩ := hOsub hs
      have he := hd.t_mul_mem_of_mem_tG (d.liftSub_le _) hsG hsB
      by_cases he1 : d.t * s = 1
      · left; left; left
        rw [← htt s, he1, mul_one]
        rfl
      rcases d.mem_zL_or_vL (fun x hx hx1 => Model.parrottF_long_or_short hx hx1) he he1 with
        hz | hv
      · left; left; right
        refine ⟨d.t * s, ?_, htt s⟩
        rw [hz3]
        exact ⟨hz, mem_sup_left he⟩
      · have hvB : d.t * s ∈ d.vL ∩ d.B := ⟨hv, mem_sup_left he⟩
        rw [← h109] at hvB
        rcases hvB with h | h
        · left; right
          exact ⟨d.t * s, h, htt s⟩
        · right
          exact ⟨d.t * s, h, htt s⟩)
    (hne1 fun h => h1z (hO₁z h)) (hne1 fun h => h1v (hO₂v h)) (hne1 fun h => h1v (hO₃v h))
    (hdis (hzv.mono hO₁z hO₂v)) (hdis (hzv.mono hO₁z hO₃v)) (hdis hdisj)
    (Set.singleton_subset_iff.2 htO) (inter_orbit_eq_empty_or_subset hKt hinv)
    (inter_orbit_eq_empty_or_subset hKt hinv) (inter_orbit_eq_empty_or_subset hKt hinv)
  have hc1 : ((fun u => d.t * u) '' O₁).ncard = 3 := by
    rw [Set.ncard_image_of_injective _ (mul_right_injective d.t), hz3, hz3c]
  have hc2 : ((fun u => d.t * u) '' O₂).ncard = 4 := by
    rw [Set.ncard_image_of_injective _ (mul_right_injective d.t), h4]
  have hc3 : ((fun u => d.t * u) '' O₃).ncard = 24 := by
    rw [Set.ncard_image_of_injective _ (mul_right_injective d.t), h24]
  rw [Set.ncard_singleton] at hcard
  rw [hc1] at ha
  rw [hc2] at hb
  rw [hc3] at hc
  exact ⟨a, b, c, ha, hb, hc, hcard⟩

omit [Finite G] in
theorem orbit_t_facts {K : Subgroup G} {D : Subgroup G} (hK : K ≤ normalizer (D : Set G))
    (htD : d.t ∈ D) :
    {y | ∃ k ∈ K, k * d.t * k⁻¹ = y} ⊆ d.tG ∩ D ∧ d.t ∈ {y | ∃ k ∈ K, k * d.t * k⁻¹ = y} ∧
      ∀ c ∈ K, ∀ s ∈ {y | ∃ k ∈ K, k * d.t * k⁻¹ = y}, c * s * c⁻¹ ∈
        {y | ∃ k ∈ K, k * d.t * k⁻¹ = y} := by
  refine ⟨?_, ⟨1, one_mem _, by group⟩, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact ⟨⟨k, rfl⟩, (mem_normalizer_iff.1 (hK hk) _).1 htD⟩
  · rintro c hc _ ⟨k, hk, rfl⟩
    exact ⟨c * k, mul_mem hc hk, by group⟩

theorem Hyp.map_conj_A_ne_B_of_G
    (hd : d.Hyp) (g : G) : d.A.map (MulAut.conj g).toMonoidHom ≠ d.B := by
  intro h
  have hMN : Nat.card d.N = Nat.card d.M := by
    change Nat.card (normalizer (d.B : Set G)) = Nat.card (normalizer (d.A : Set G))
    rw [← h]
    exact card_normalizer_map_conj d.A g
  have htA : d.t ∈ d.A := mem_sup_right (mem_zpowers _)
  have htB : d.t ∈ d.B := mem_sup_right (mem_zpowers _)
  obtain ⟨hOA, htOA, hinvA⟩ := d.orbit_t_facts (K := d.M) le_rfl htA
  obtain ⟨hOB, htOB, hinvB⟩ := d.orbit_t_facts (K := d.N) le_rfl htB
  obtain ⟨a, b, c, ha, hb, hc, -, -, hx⟩ := hd.ncard_tG_A hOA htOA
    (fun k hk => hinvA k (mem_inf.1 hk).1)
  obtain ⟨a', b', c', ha', hb', hc', hy⟩ := hd.ncard_tG_B hOB htOB
    (fun k hk => hinvB k (mem_inf.1 hk).1)
  have h1 := card_eq_ncard_conj_mul d.M d.t
  have h2 := card_eq_ncard_conj_mul d.N d.t
  obtain ⟨h35, -⟩ := hd.card_CM_CN
  rw [hx] at h1
  rw [hy] at h2
  have hpos : 0 < Nat.card (d.N ⊓ centralizer ({d.t} : Set G) : Subgroup G) := Nat.card_pos
  have key : 5 * (1 + a + b + c) = 3 * (1 + a' + b' + c') := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc 5 * (1 + a + b + c) * Nat.card (d.N ⊓ centralizer ({d.t} : Set G) : Subgroup G) =
        (1 + a + b + c) * (5 * Nat.card (d.N ⊓ centralizer ({d.t} : Set G) : Subgroup G)) := by
          ring
      _ = (1 + a + b + c) * (3 * Nat.card (d.M ⊓ centralizer ({d.t} : Set G) : Subgroup G)) := by
          rw [h35]
      _ = 3 * Nat.card d.M := by rw [h1]; ring
      _ = 3 * Nat.card d.N := by rw [hMN]
      _ = 3 * (1 + a' + b' + c') *
          Nat.card (d.N ⊓ centralizer ({d.t} : Set G) : Subgroup G) := by rw [h2]; ring
  omega

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
