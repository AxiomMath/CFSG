module

public import CFSG.SignalizerFunctorTheorem.Nonsolvable.FaithfulSimple.SectionAction
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

variable {G : Type*} [Group G]

theorem inv_mul_mul_mem_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) {h : G} (hh : h ∈ H) : g⁻¹ * h * g ∈ H :=
  (mem_normalizer_iff''.mp hg h).mp hh

section Section

variable {K L : Subgroup G} [(L.subgroupOf K).Normal] {g : G}

@[expose] noncomputable def sectionRightConj (hK : g ∈ normalizer (K : Set G))
    (hL : g ∈ normalizer (L : Set G)) : MulAut (K ⧸ L.subgroupOf K) :=
  CFSG.SignalizerFunctorTheorem.sectionAction (A := zpowers g) (zpowers_le.mpr hK)
    (zpowers_le.mpr hL) ⟨g, mem_zpowers g⟩⁻¹

theorem sectionRightConj_mk (hK : g ∈ normalizer (K : Set G)) (hL : g ∈ normalizer (L : Set G))
    (k k' : K) (hk : (k' : G) = g⁻¹ * k * g) :
    sectionRightConj hK hL (QuotientGroup.mk k) = (QuotientGroup.mk k' : K ⧸ L.subgroupOf K) := by
  unfold sectionRightConj
  rw [CFSG.SignalizerFunctorTheorem.sectionAction_mk]
  congr 1
  apply Subtype.ext
  rw [CFSG.SignalizerFunctorTheorem.coe_sectionConjAut, hk]
  simp

theorem sectionRightConj_mk_eq_iff (hK : g ∈ normalizer (K : Set G))
    (hL : g ∈ normalizer (L : Set G)) (k : K) :
    sectionRightConj hK hL (QuotientGroup.mk k) = (QuotientGroup.mk k : K ⧸ L.subgroupOf K) ↔
      g⁻¹ * (k : G)⁻¹ * g * k ∈ L := by
  let k' : K := ⟨g⁻¹ * k * g, inv_mul_mul_mem_of_mem_normalizer hK k.2⟩
  rw [sectionRightConj_mk hK hL k k' rfl, QuotientGroup.eq, mem_subgroupOf]
  have h : ((k'⁻¹ * k : K) : G) = g⁻¹ * (k : G)⁻¹ * g * k := by
    simp only [k', Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [h]

theorem exists_conj_eq_mul_of_sectionRightConj_fixed (hK : g ∈ normalizer (K : Set G))
    (hL : g ∈ normalizer (L : Set G)) (k : K)
    (h : sectionRightConj hK hL (QuotientGroup.mk k) = (QuotientGroup.mk k : K ⧸ L.subgroupOf K)) :
    ∃ l ∈ L, (k : G)⁻¹ * g * k = g * l :=
  ⟨g⁻¹ * (k : G)⁻¹ * g * k, (sectionRightConj_mk_eq_iff hK hL k).mp h, by group⟩

variable [IsElementaryAbelian 2 (K ⧸ L.subgroupOf K)]

omit [(L.subgroupOf K).Normal] in
theorem mul_self_eq_one_of_isElementaryAbelian_two {E : Type*} [Group E]
    [IsElementaryAbelian 2 E] (x : E) : x * x = 1 := by
  have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 E) x
  rwa [pow_two] at h

theorem conj_mem_coset_of_inv_mul_eq (hK : g ∈ normalizer (K : Set G))
    (hL : g ∈ normalizer (L : Set G)) {k : G} (hk : k ∈ K) (y : K)
    (hy : (QuotientGroup.mk y : K ⧸ L.subgroupOf K)⁻¹ *
        sectionRightConj hK hL (QuotientGroup.mk y) = QuotientGroup.mk (⟨k, hk⟩ : K)) :
    ∃ l ∈ L, (y : G) * (g * k) * (y : G)⁻¹ = g * l := by
  let kK : K := ⟨k, hk⟩
  let ya : K := ⟨g⁻¹ * y * g, inv_mul_mul_mem_of_mem_normalizer hK y.2⟩
  have hya : sectionRightConj hK hL (QuotientGroup.mk y) =
      (QuotientGroup.mk ya : K ⧸ L.subgroupOf K) := sectionRightConj_mk hK hL y ya rfl
  refine ⟨g⁻¹ * y * g * k * (y : G)⁻¹, ?_, by group⟩
  have h1 : (QuotientGroup.mk (ya * kK * y⁻¹) : K ⧸ L.subgroupOf K) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hya]
    change _ * QuotientGroup.mk (⟨k, hk⟩ : K) * _ = _
    rw [← hy]
    set x := sectionRightConj hK hL (QuotientGroup.mk y)
    set w : K ⧸ L.subgroupOf K := QuotientGroup.mk y
    calc x * (w⁻¹ * x) * w⁻¹ = x * (x * w⁻¹) * w⁻¹ := by rw [mul_comm' w⁻¹ x]
      _ = (x * x) * (w⁻¹ * w⁻¹) := by group
      _ = 1 := by
        rw [mul_self_eq_one_of_isElementaryAbelian_two, mul_self_eq_one_of_isElementaryAbelian_two,
          one_mul]
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
  simpa [ya, kK] using h1

theorem sectionRightConj_mk_eq_of_mul_self_eq_one (hK : g ∈ normalizer (K : Set G))
    (hL : g ∈ normalizer (L : Set G)) (hg : g * g = 1) {k : G} (hk : k ∈ K)
    (hsq : g * k * (g * k) = 1) :
    sectionRightConj hK hL (QuotientGroup.mk (⟨k, hk⟩ : K)) =
      (QuotientGroup.mk (⟨k, hk⟩ : K) : K ⧸ L.subgroupOf K) := by
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have hkinv : g⁻¹ * k * g = k⁻¹ := by
    rw [hginv]
    calc g * k * g = g * k * (g * k) * k⁻¹ := by group
      _ = k⁻¹ := by rw [hsq, one_mul]
  rw [sectionRightConj_mk hK hL ⟨k, hk⟩ ⟨k, hk⟩⁻¹ (by simp [hkinv]), QuotientGroup.mk_inv]
  exact inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_isElementaryAbelian_two _)

theorem exists_conj_mem_coset_of_mul_self_eq_one (hK : g ∈ normalizer (K : Set G))
    (hL : g ∈ normalizer (L : Set G)) (hg : g * g = 1)
    (hfix : {q | sectionRightConj hK hL q = q} =
      Set.range fun q : K ⧸ L.subgroupOf K => q⁻¹ * sectionRightConj hK hL q)
    {k : G} (hk : k ∈ K) (hsq : g * k * (g * k) = 1) :
    ∃ y ∈ K, ∃ l ∈ L, y * (g * k) * y⁻¹ = g * l := by
  have hmem : (QuotientGroup.mk (⟨k, hk⟩ : K) : K ⧸ L.subgroupOf K) ∈
      {q | sectionRightConj hK hL q = q} :=
    sectionRightConj_mk_eq_of_mul_self_eq_one hK hL hg hk hsq
  rw [hfix] at hmem
  obtain ⟨p, hp⟩ := hmem
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective p
  obtain ⟨l, hl, hyl⟩ := conj_mem_coset_of_inv_mul_eq hK hL hk y hp
  exact ⟨y, y.2, l, hl, hyl⟩

omit [IsElementaryAbelian 2 (K ⧸ L.subgroupOf K)] in
theorem mk_inv_mul_conj_coset_mul (hLK : L ≤ K) (hK : g ∈ normalizer (K : Set G))
    (hL : g ∈ normalizer (L : Set G)) (y : K) {l : G} (hl : l ∈ L)
    (h : g⁻¹ * ((y : G)⁻¹ * (g * l) * y) ∈ K) :
    (QuotientGroup.mk (⟨g⁻¹ * ((y : G)⁻¹ * (g * l) * y), h⟩ : K) : K ⧸ L.subgroupOf K) =
      (sectionRightConj hK hL (QuotientGroup.mk y))⁻¹ * QuotientGroup.mk y := by
  let ya : K := ⟨g⁻¹ * (y : G)⁻¹ * g, inv_mul_mul_mem_of_mem_normalizer hK (K.inv_mem y.2)⟩
  have hya : sectionRightConj hK hL (QuotientGroup.mk y⁻¹) =
      (QuotientGroup.mk ya : K ⧸ L.subgroupOf K) :=
    sectionRightConj_mk hK hL y⁻¹ ya (by simp [ya])
  have hl1 : (QuotientGroup.mk (⟨l, hLK hl⟩ : K) : K ⧸ L.subgroupOf K) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr hl)
  have he : (⟨g⁻¹ * ((y : G)⁻¹ * (g * l) * y), h⟩ : K) = ya * ⟨l, hLK hl⟩ * y :=
    Subtype.ext (by simp only [ya, Subgroup.coe_mul]; group)
  rw [he, QuotientGroup.mk_mul, QuotientGroup.mk_mul, hl1, mul_one, ← hya, QuotientGroup.mk_inv,
    map_inv]

theorem coset_conj_of_section (hLK : L ≤ K) (hK : g ∈ normalizer (K : Set G))
    (hL : g ∈ normalizer (L : Set G)) (hg : g * g = 1)
    (hfix : {q | sectionRightConj hK hL q = q} =
      Set.range fun q : K ⧸ L.subgroupOf K => q⁻¹ * sectionRightConj hK hL q)
    (hLconj : ∀ l ∈ L, g * l * (g * l) = 1 → ∃ m ∈ L, g * l = m⁻¹ * g * m)
    {k : G} (hk : k ∈ K) (hsq : g * k * (g * k) = 1) : ∃ m ∈ K, g * k = m⁻¹ * g * m := by
  obtain ⟨y, hy, l, hl, hyl⟩ := exists_conj_mem_coset_of_mul_self_eq_one hK hL hg hfix hk hsq
  have hsql : g * l * (g * l) = 1 := by
    rw [← hyl]
    calc y * (g * k) * y⁻¹ * (y * (g * k) * y⁻¹) = y * (g * k * (g * k)) * y⁻¹ := by group
      _ = 1 := by rw [hsq]; group
  obtain ⟨m, hm, hml⟩ := hLconj l hl hsql
  refine ⟨m * y, K.mul_mem (hLK hm) hy, ?_⟩
  calc g * k = y⁻¹ * (y * (g * k) * y⁻¹) * y := by group
    _ = y⁻¹ * (m⁻¹ * g * m) * y := by rw [hyl, hml]
    _ = (m * y)⁻¹ * g * (m * y) := by group

end Section

section Centralizer

variable {K L : Subgroup G} [(L.subgroupOf K).Normal] {g : G}

theorem card_inf_centralizer_eq_mul_card_fixed (hLK : L ≤ K) (hK : g ∈ normalizer (K : Set G))
    (hL : g ∈ normalizer (L : Set G)) (hg : g * g = 1)
    (hLconj : ∀ l ∈ L, g * l * (g * l) = 1 → ∃ m ∈ L, g * l = m⁻¹ * g * m) :
    Nat.card (K ⊓ centralizer {g} : Subgroup G) =
      Nat.card (L ⊓ centralizer {g} : Subgroup G) *
        Nat.card {q | sectionRightConj hK hL q = q} := by
  let φ : (K ⊓ centralizer {g} : Subgroup G) →* K ⧸ L.subgroupOf K :=
    (QuotientGroup.mk' (L.subgroupOf K)).comp (inclusion inf_le_left)
  have hrange : (φ.range : Set (K ⧸ L.subgroupOf K)) = {q | sectionRightConj hK hL q = q} := by
    ext q
    constructor
    · rintro ⟨c, rfl⟩
      change sectionRightConj hK hL (QuotientGroup.mk (inclusion inf_le_left c)) =
        QuotientGroup.mk (inclusion inf_le_left c)
      rw [sectionRightConj_mk_eq_iff]
      have hc : (c : G) * g = g * c := mem_centralizer_singleton_iff.mp (mem_inf.mp c.2).2
      have h1 : g⁻¹ * ((inclusion inf_le_left c : K) : G)⁻¹ * g *
          (inclusion inf_le_left c : K) = 1 := by
        change g⁻¹ * (c : G)⁻¹ * g * c = 1
        calc g⁻¹ * (c : G)⁻¹ * g * c = g⁻¹ * (c : G)⁻¹ * (g * c) := by group
          _ = 1 := by rw [← hc]; group
      rw [h1]
      exact L.one_mem
    · intro hq
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨l, hl, hkl⟩ := exists_conj_eq_mul_of_sectionRightConj_fixed hK hL k hq
      have hsq : g * l * (g * l) = 1 := by
        rw [← hkl]
        calc (k : G)⁻¹ * g * k * ((k : G)⁻¹ * g * k) = (k : G)⁻¹ * (g * g) * k := by group
          _ = 1 := by rw [hg]; group
      obtain ⟨m, hm, hml⟩ := hLconj l hl hsq
      have hcK : (k : G) * m⁻¹ ∈ K := K.mul_mem k.2 (K.inv_mem (hLK hm))
      have hcC : (k : G) * m⁻¹ ∈ centralizer {g} := by
        rw [mem_centralizer_singleton_iff]
        have h1 : (k : G)⁻¹ * g * k = m⁻¹ * g * m := hkl.trans hml
        calc (k : G) * m⁻¹ * g = k * (m⁻¹ * g * m) * m⁻¹ := by group
          _ = k * ((k : G)⁻¹ * g * k) * m⁻¹ := by rw [h1]
          _ = g * (k * m⁻¹) := by group
      refine ⟨⟨(k : G) * m⁻¹, mem_inf.mpr ⟨hcK, hcC⟩⟩, ?_⟩
      change (QuotientGroup.mk (inclusion inf_le_left _) : K ⧸ L.subgroupOf K) = QuotientGroup.mk k
      rw [QuotientGroup.eq, mem_subgroupOf]
      have h2 : (((inclusion inf_le_left ⟨(k : G) * m⁻¹, mem_inf.mpr ⟨hcK, hcC⟩⟩ : K)⁻¹ * k :
          K) : G) = m := by
        change ((k : G) * m⁻¹)⁻¹ * k = m
        group
      rw [h2]
      exact hm
  have hker : Nat.card φ.ker = Nat.card (L ⊓ centralizer {g} : Subgroup G) := by
    have h : φ.ker = (L ⊓ centralizer {g}).subgroupOf (K ⊓ centralizer {g}) := by
      ext c
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      change (QuotientGroup.mk (inclusion inf_le_left c) : K ⧸ L.subgroupOf K) = 1 ↔ _
      rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact ⟨fun h => mem_inf.mpr ⟨h, (mem_inf.mp c.2).2⟩, fun h => (mem_inf.mp h).1⟩
    rw [h]
    exact Nat.card_congr (subgroupOfEquivOfLe (inf_le_inf_right _ hLK)).toEquiv
  calc Nat.card (K ⊓ centralizer {g} : Subgroup G) = Nat.card φ.ker * φ.ker.index :=
        (card_mul_index _).symm
    _ = Nat.card φ.ker * Nat.card φ.range := by rw [index_ker]
    _ = _ := by
        rw [hker, ← hrange]
        rfl

end Centralizer

theorem inv_mul_apply_mul {E : Type*} [Group E] [IsMulCommutative E] (α : MulAut E) (x y : E) :
    (x * y)⁻¹ * α (x * y) = x⁻¹ * α x * (y⁻¹ * α y) := by
  rw [mul_inv_rev, map_mul, mul_comm' y⁻¹ x⁻¹]
  calc x⁻¹ * y⁻¹ * (α x * α y) = x⁻¹ * (y⁻¹ * α x) * α y := by group
    _ = x⁻¹ * (α x * y⁻¹) * α y := by rw [mul_comm' y⁻¹ (α x)]
    _ = x⁻¹ * α x * (y⁻¹ * α y) := by group

theorem coe_closure_range_inv_mul_apply {E : Type*} [Group E] [IsMulCommutative E]
    (α : MulAut E) :
    (closure (Set.range fun x => x⁻¹ * α x) : Set E) = Set.range fun x => x⁻¹ * α x := by
  let β : E →* E := MonoidHom.mk' (fun x => x⁻¹ * α x) (inv_mul_apply_mul α)
  have h : (β.range : Set E) = Set.range fun x => x⁻¹ * α x := MonoidHom.coe_range β
  rw [← h, closure_eq]

theorem card_eq_card_fixed_sq {E : Type*} [Group E] [IsMulCommutative E] (α : MulAut E)
    (h : {x | α x = x} = Set.range fun x => x⁻¹ * α x) :
    Nat.card E = Nat.card {x | α x = x} ^ 2 := by
  let β : E →* E := MonoidHom.mk' (fun x => x⁻¹ * α x) (inv_mul_apply_mul α)
  have hker : (β.ker : Set E) = {x | α x = x} := by
    ext x
    change x⁻¹ * α x = 1 ↔ α x = x
    rw [inv_mul_eq_one, eq_comm]
  have hrange : (β.range : Set E) = {x | α x = x} := by
    rw [h, MonoidHom.coe_range]
    rfl
  calc Nat.card E = Nat.card β.ker * β.ker.index := (card_mul_index _).symm
    _ = Nat.card β.ker * Nat.card β.range := by rw [index_ker]
    _ = _ := by
        rw [sq]
        congr 1
        · rw [← hker]
          rfl
        · rw [← hrange]
          rfl

theorem card_conj_orbit_mul_card_inf_centralizer (W : Subgroup G) (a : G) :
    Nat.card {x | ∃ w ∈ W, x = w⁻¹ * a * w} * Nat.card (W ⊓ centralizer {a} : Subgroup G) =
      Nat.card W := by
  let _ : MulAction W G :=
    MulAction.compHom G ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp W.subtype)
  have hsmul : ∀ (x : W) (y : G), x • y = (x : G) * y * (x : G)⁻¹ := fun x y =>
    ConjAct.toConjAct_smul (x : G) y
  have horb : MulAction.orbit W a = {x | ∃ w ∈ W, x = w⁻¹ * a * w} := by
    ext y
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : G)⁻¹, W.inv_mem x.2, by rw [hsmul, inv_inv]⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w⁻¹, W.inv_mem hw⟩, by rw [hsmul, inv_inv]⟩
  have hstab : MulAction.stabilizer W a = (centralizer {a}).subgroupOf W := by
    ext x
    rw [MulAction.mem_stabilizer_iff, hsmul, mem_subgroupOf, mem_centralizer_singleton_iff,
      mul_inv_eq_iff_eq_mul, eq_comm]
  have hcard : Nat.card ((centralizer {a}).subgroupOf W) =
      Nat.card (W ⊓ centralizer {a} : Subgroup G) := by
    rw [← card_subtype W ((centralizer {a}).subgroupOf W), subgroupOf_map_subtype, inf_comm]
  rw [← horb, Nat.card_coe_set_eq, ← MulAction.index_stabilizer, hstab, ← hcard, mul_comm,
    card_mul_index]

end CFSG.LocalAnalysis.ComponentInitial
