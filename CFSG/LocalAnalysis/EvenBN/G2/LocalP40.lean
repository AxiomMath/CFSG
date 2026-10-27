module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalP37
public import CFSG.LocalAnalysis.EvenBN.G2.LocalP39

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

private theorem normalizer_le_normalizer_of_characteristic_subgroupOf {G : Type*} [Group G]
    {H E : Subgroup G} (hEH : E ≤ H) (hc : (E.subgroupOf H).Characteristic) :
    normalizer (H : Set G) ≤ normalizer (E : Set G) := by
  have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (E.subgroupOf H)
  rwa [subgroupOf_map_subtype, inf_of_le_left hEH] at h1

private theorem exists_hom_sup_of_rel {G Q : Type*} [Group G] [Group Q] {A B : Subgroup G}
    (hBA : B ≤ normalizer (A : Set G)) (R : G → Q → Prop)
    (htot : ∀ a ∈ A, ∃ q, R a q)
    (hmul : ∀ a a' q q', a ∈ A → a' ∈ A → R a q → R a' q' → R (a * a') (q * q'))
    (hfun : ∀ a q q', a ∈ A → R a q → R a q' → q = q')
    (hinv : ∀ a q b, a ∈ A → b ∈ B → R a q → R (b * a * b⁻¹) q)
    (hker : ∀ a ∈ A, a ∈ B → R a 1) :
    ∃ ψ : (A ⊔ B : Subgroup G) →* Q, ∀ (x : ↥(A ⊔ B)) a q b, a ∈ A → b ∈ B →
      (x : G) = a * b → R a q → ψ x = q := by
  classical
  have hdec : ∀ x : ↥(A ⊔ B), ∃ a ∈ A, ∃ b ∈ B, (x : G) = a * b := fun x =>
    Common.exists_mul_of_le_normalizer hBA x x.2
  choose a ha b hb hx using hdec
  have hq : ∀ x : ↥(A ⊔ B), ∃ q, R (a x) q := fun x => htot _ (ha x)
  choose q hq using hq
  have key : ∀ (x : ↥(A ⊔ B)) a' q' b', a' ∈ A → b' ∈ B → (x : G) = a' * b' → R a' q' →
      q x = q' := by
    intro x a' q' b' ha' hb' hxe hR'
    have hβ : b' * (b x)⁻¹ ∈ B := mul_mem hb' (inv_mem (hb x))
    have e1 : a x = a' * (b' * (b x)⁻¹) := by
      have := hx x
      rw [hxe] at this
      calc a x = a x * b x * (b x)⁻¹ := by group
        _ = a' * b' * (b x)⁻¹ := by rw [← this]
        _ = a' * (b' * (b x)⁻¹) := by group
    have hβA : b' * (b x)⁻¹ ∈ A := by
      have := mul_mem (inv_mem ha') (ha x)
      rwa [e1, inv_mul_cancel_left] at this
    have hRβ := hker _ hβA hβ
    have hRa := hmul _ _ _ _ ha' hβA hR' hRβ
    rw [← e1, mul_one] at hRa
    exact hfun _ _ _ (ha x) (hq x) hRa
  refine ⟨{ toFun := q, map_one' := ?_, map_mul' := ?_ }, key⟩
  · exact key 1 1 1 1 (one_mem _) (one_mem _) (by simp) (hker 1 (one_mem _) (one_mem _))
  · intro x y
    have hy' : b x * a y * (b x)⁻¹ ∈ A := (mem_normalizer_iff.1 (hBA (hb x)) _).1 (ha y)
    refine key (x * y) (a x * (b x * a y * (b x)⁻¹)) (q x * q y) (b x * b y)
      (mul_mem (ha x) hy') (mul_mem (hb x) (hb y)) ?_
      (hmul _ _ _ _ (ha x) hy' (hq x) (hinv _ _ _ (ha y) (hb x) (hq y)))
    calc ((x * y : ↥(A ⊔ B)) : G) = (a x * b x) * (a y * b y) := by
          rw [Subgroup.coe_mul, hx x, hx y]
      _ = a x * (b x * a y * (b x)⁻¹) * (b x * b y) := by group

namespace Model

variable
  {K : Type} [Field K] [CharP K 2]

private theorem mem_M_or_mem_F_of_commutator_mem_W {s m : ModGL .G2 K} (hs : s ∈ S K)
    (hm : m ∈ M K) (h : ⁅s, m⁆ ∈ W K) : s ∈ M K ∨ m ∈ Model.F K := by
  obtain ⟨_, B, _, _, _, _, rfl⟩ := mem_S.1 hs
  obtain ⟨a, _, _, _, _, rfl⟩ := mem_M.1 hm
  rw [g2N_commutator_coords, g2N_mem_W_iff] at h
  have h3 : B * a = 0 := by simpa using h.2.2
  rcases mul_eq_zero.1 h3 with hB | ha
  · exact Or.inl (g2N_mem_M_iff.2 hB)
  · exact Or.inr (g2N_mem_F_iff.2 ⟨ha, rfl⟩)

end Model

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

variable
  [Finite K] [CharP K 2]

theorem mem_M_or_mem_F_of_commutator_mem_W (_hK : 4 ≤ Nat.card K) {s m : G} (hs : s ∈ d.S)
    (hm : m ∈ d.M) (h : s * m * s⁻¹ * m⁻¹ ∈ d.W) : s ∈ d.M ∨ m ∈ d.F := by
  obtain ⟨g, hg, rfl⟩ := d.mem_image.1 hs
  obtain ⟨g', hg', rfl⟩ := d.mem_image.1 hm
  have hc : d.emb ⁅g, g'⁆ ∈ d.W := by
    rw [map_commutatorElement, commutatorElement_def]
    exact h
  have := d.emb_mem_image_iff.1 hc
  rcases Model.mem_M_or_mem_F_of_commutator_mem_W hg hg'
    (by simpa [commutatorElement_def] using this) with h1 | h1
  · exact Or.inl (d.emb_mem_image h1)
  · exact Or.inr (d.emb_mem_image h1)

end G2Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

private theorem yamadaL₃_le_yamadaL₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaL₃ d t ≤ yamadaL₆ d t := by
  rw [← (h.yamada_5_39_1 hW d hK hQ).2]
  exact inf_le_left

private theorem yamadaL₂_le_yamadaL₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaL₂ d t ≤ yamadaL₆ d t :=
  (h.yamadaL₃_facts hW d hK hQ.doubling).1.trans
    (h.yamadaL₃_le_yamadaL₆ hW d hK hQ)

omit [Finite K] in
private theorem S_le_normalizer_yamadaL₆ (h : Setup G L f t) (d : G2Data L K) :
    d.S ≤ normalizer (yamadaL₆ d t : Set G) := fun _ hs =>
  le_normalizer_yamadaL₆ d t (h.S_le_normalizer_yamadaL₂ d hs)

omit [Finite K] in
private theorem centralizer_inf_normalizer_Y_le_normalizer_yamadaL₆ (h : Setup G L f t)
    (d : G2Data L K) :
    centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G) ≤ normalizer (yamadaL₆ d t : Set G) :=
  ((h.centralizer_inf_normalizer_Y_le d).trans (le_normalizer_yamadaL₂ d t)).trans
    (le_normalizer_yamadaL₆ d t)

private theorem centralizer_inf_normalizer_S_le_Y (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤
      centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G) := fun x hx =>
  Subgroup.mem_inf.2 ⟨hx.1, (h.centralizer_inf_normalizer_S_le d hK hD).2.2 hx⟩

private theorem isPGroup_yamadaL₆ (d : G2Data L K) (t : G) : IsPGroup 2 (yamadaL₆ d t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact LieType.BorelTits.pCoreOf_isPGroup 2 _

omit [Finite K] in
private theorem yamadaR₆_le_normalizer_yamadaL₂ (h : Setup G L f t) (d : G2Data L K) :
    yamadaR₆ d t ≤ normalizer (yamadaL₂ d t : Set G) :=
  sup_le (yamadaL₆_le d t) (h.S_le_normalizer_yamadaL₂ d)

private theorem yamadaR₆_eq_sup_R₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₆ d t = yamadaL₆ d t ⊔ yamadaR₃ d t :=
  le_antisymm (sup_le le_sup_left ((le_sup_right : d.S ≤ yamadaL₃ d t ⊔ d.S).trans le_sup_right))
    (sup_le le_sup_left (sup_le ((h.yamadaL₃_le_yamadaL₆ hW d hK hQ).trans le_sup_left)
      le_sup_right))

private theorem yamadaR₂_le_yamadaR₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₂ d t ≤ yamadaR₅ d t := by
  have hD := hQ.doubling
  exact (h.yamada_5_21_2 hW d hK hD).2.1.trans (h.yamada_5_27_3 hW d hK hD).ge

private theorem yamadaR_inf_L (h : Setup G L f t) (d : G2Data L K) :
    yamadaR d t ⊓ L = d.S := by
  refine le_antisymm (fun x hx => ?_) (le_inf (by rw [h.yamadaR_eq d]; exact le_sup_left)
    (d.image_le _))
  obtain ⟨hxR, hxL⟩ := Subgroup.mem_inf.1 hx
  rw [h.yamadaR_eq d, h.mem_sup_zpowers_iff (E := d.S) (d.image_le _)] at hxR
  rcases hxR with hxS | hxS
  · exact hxS
  · exfalso
    refine h.t_not_mem_L ?_
    have := mul_mem (d.image_le _ hxS) (inv_mem hxL)
    rwa [mul_inv_cancel_right] at this

private theorem yamadaR_le_yamadaR₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR d t ≤ yamadaR₆ d t := by
  rw [h.yamadaR_eq d]
  exact sup_le le_sup_right ((zpowers_le).2 (mem_sup_left (h.yamadaL₂_le_yamadaL₆ hW d hK hQ
    (h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))))))

private structure L₆Rel (d : G2Data L K) (t : G) (Rel : G → G → Prop) : Prop where
  mem : ∀ l m, Rel l m → l ∈ yamadaL₆ d t ∧ m ∈ d.M
  total : ∀ l ∈ yamadaL₆ d t, ∃ m, Rel l m
  onto : ∀ m ∈ d.M, ∃ l, Rel l m
  mul : ∀ l l' m m', Rel l m → Rel l' m' → Rel (l * l') (m * m')
  inv : ∀ l m, Rel l m → Rel l⁻¹ m⁻¹
  mem_L₃_iff : ∀ l m, Rel l m → (l ∈ yamadaL₃ d t ↔ m ∈ d.W)
  crossed : ∀ l m, ∀ y ∈ yamadaY₂ d t, l ∈ yamadaL₆ d t → m ∈ d.M →
    l * t * l⁻¹ = t * m * y → Rel l m
  conj : ∀ c ∈ centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G), ∀ l m, Rel l m →
    Rel (c * l * c⁻¹) (c * m * c⁻¹)

private theorem exists_rel_yamadaL₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∃ Rel : G → G → Prop, L₆Rel d t Rel := by
  obtain ⟨hN₃, hNW, φ, hφ, hφc⟩ := h.yamada_5_39_2 hW d hK hQ
  refine ⟨fun l m => ∃ (hl : l ∈ yamadaL₆ d t) (hm : m ∈ d.M),
    φ (QuotientGroup.mk ⟨l, hl⟩) = QuotientGroup.mk ⟨m, hm⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro l m ⟨hl, hm, -⟩
    exact ⟨hl, hm⟩
  · intro l hl
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (φ (QuotientGroup.mk ⟨l, hl⟩))
    exact ⟨q, hl, q.2, hq.symm⟩
  · intro m hm
    obtain ⟨y, hy⟩ := φ.surjective (QuotientGroup.mk ⟨m, hm⟩)
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨l, l.2, hm, hy⟩
  · rintro l l' m m' ⟨hl, hm, e⟩ ⟨hl', hm', e'⟩
    refine ⟨mul_mem hl hl', mul_mem hm hm', ?_⟩
    have := congrArg₂ (· * ·) e e'
    simpa [← QuotientGroup.mk_mul, ← map_mul] using this
  · rintro l m ⟨hl, hm, e⟩
    refine ⟨inv_mem hl, inv_mem hm, ?_⟩
    have e1 : (QuotientGroup.mk ⟨l⁻¹, inv_mem hl⟩ : yamadaL₆ d t ⧸
        (yamadaL₃ d t).subgroupOf (yamadaL₆ d t)) = (QuotientGroup.mk ⟨l, hl⟩)⁻¹ := rfl
    have e2 : (QuotientGroup.mk ⟨m⁻¹, inv_mem hm⟩ : d.M ⧸ d.W.subgroupOf d.M) =
        (QuotientGroup.mk ⟨m, hm⟩)⁻¹ := rfl
    rw [e1, e2, map_inv, e]
  · rintro l m ⟨hl, hm, e⟩
    have h1 : l ∈ yamadaL₃ d t ↔ (QuotientGroup.mk ⟨l, hl⟩ : yamadaL₆ d t ⧸
        (yamadaL₃ d t).subgroupOf (yamadaL₆ d t)) = 1 := by
      rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
    have h2 : m ∈ d.W ↔ (QuotientGroup.mk ⟨m, hm⟩ : d.M ⧸ d.W.subgroupOf d.M) = 1 := by
      rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
    rw [h1, h2, ← e, map_eq_one_iff φ φ.injective]
  · intro l m y hy hl hm e
    exact ⟨hl, hm, hφ ⟨l, hl⟩ ⟨m, hm⟩ y hy e⟩
  · rintro c hc l m ⟨hl, hm, e⟩
    obtain ⟨hx, hm', e'⟩ := hφc c hc ⟨l, hl⟩ ⟨m, hm⟩ e
    exact ⟨hx, hm', e'⟩

omit [Finite K] in
private theorem inv_mul_mem_W_of_rel {d : G2Data L K} {Rel : G → G → Prop}
    (hR : L₆Rel d t Rel) {l m m' : G} (hlm : Rel l m) (hlm' : Rel l m') : m⁻¹ * m' ∈ d.W := by
  have := hR.mul _ _ _ _ (hR.inv _ _ hlm) hlm'
  rw [inv_mul_cancel] at this
  exact (hR.mem_L₃_iff _ _ this).1 (one_mem _)

private theorem mem_yamadaL₃_of_mem_yamadaL₆_of_commute (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {l : G}
    (hl : l ∈ yamadaL₆ d t) (hlt : l ∈ centralizer ({t} : Set G)) : l ∈ yamadaL₃ d t := by
  obtain ⟨Rel, hR⟩ := h.exists_rel_yamadaL₆ hW d hK hQ
  have hrel : Rel l 1 := hR.crossed l 1 1 (one_mem _) hl (one_mem _) (by
    rw [mul_one, mul_one, mem_centralizer_singleton_iff.1 hlt, mul_inv_cancel_right])
  exact (hR.mem_L₃_iff l 1 hrel).2 (one_mem _)

theorem yamadaL₆_inf_S (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : yamadaL₆ d t ⊓ d.S = d.M := by
  obtain ⟨-, -, -, -, hL₃S⟩ := h.yamadaL₃_facts hW d hK hQ.doubling
  refine le_antisymm (fun s hs => ?_) (le_inf ?_ d.inclusions.2.2.2.2.2.2.2.2.1)
  · rw [← hL₃S]
    exact ⟨h.mem_yamadaL₃_of_mem_yamadaL₆_of_commute hW d hK hQ hs.1
      (h.S_le_centralizer d hs.2), hs.2⟩
  · rw [← hL₃S]
    exact inf_le_left.trans (h.yamadaL₃_le_yamadaL₆ hW d hK hQ)

theorem yamadaR₆_inf_centralizer (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₆ d t ⊓ centralizer ({t} : Set G) = yamadaR d t := by
  have hD := hQ.doubling
  refine le_antisymm (fun x hx => ?_) (le_inf (h.yamadaR_le_yamadaR₆ hW d hK hQ)
    (h.yamadaR_le_centralizer d))
  obtain ⟨hx₆, hxC⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨l, hl, s, hs, rfl⟩ := Common.exists_mul_of_le_normalizer
    (h.S_le_normalizer_yamadaL₆ d) x hx₆
  have hlC : l ∈ centralizer ({t} : Set G) := by
    have := mul_mem hxC (inv_mem (h.S_le_centralizer d hs))
    rwa [mul_inv_cancel_right] at this
  have hlL₃ := h.mem_yamadaL₃_of_mem_yamadaL₆_of_commute hW d hK hQ hl hlC
  have hR₃R₅ : yamadaR₃ d t ≤ yamadaR₅ d t := by
    rw [(h.yamada_5_27_2 hW d hK hD).1.1]
    exact le_sup_left
  have hx₅ : l * s ∈ yamadaR₅ d t := hR₃R₅ (mul_mem (mem_sup_left hlL₃) (mem_sup_right hs))
  rw [← (h.yamada_5_27_1 hW d hK hD).2.2]
  exact Subgroup.mem_inf.2 ⟨hx₅, hxC⟩

private theorem exists_mul_of_mem_normalizer_yamadaL₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ normalizer (yamadaL₂ d t : Set G)) :
    ∃ l ∈ yamadaL₆ d t, ∃ c ∈ centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G),
      x = l * c := by
  have hD := hQ.doubling
  obtain ⟨⟨-, hset, -⟩, -⟩ := h.yamada_5_39_1 hW d hK hQ
  have hx' : x ∈ ((normalizer (yamadaL₂ d t : Set G) : Subgroup G) : Set G) := hx
  rw [hset] at hx'
  obtain ⟨l, hl, v, hv, rfl⟩ := Set.mem_mul.1 hx'
  have hv' : v ∈ ((normalizer (yamadaV₂ d t : Set G) : Subgroup G) : Set G) := hv
  rw [(h.yamada_5_23_1 hW d hK hD).2.2.1] at hv'
  obtain ⟨l₃, hl₃, g, hg, rfl⟩ := Set.mem_mul.1 hv'
  have hg' : g ∈ ((normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) : Subgroup G) :
      Set G) := hg
  rw [(h.yamada_5_5_1 d hK).2.2.1] at hg'
  obtain ⟨l₂, hl₂, c, hc, rfl⟩ := Set.mem_mul.1 hg'
  exact ⟨l * (l₃ * l₂), mul_mem hl (mul_mem (h.yamadaL₃_le_yamadaL₆ hW d hK hQ hl₃)
    (h.yamadaL₂_le_yamadaL₆ hW d hK hQ hl₂)), c, hc, by group⟩

theorem yamadaR₅_le_yamadaR₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₅ d t ≤ yamadaR₆ d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := hQ.doubling
  have hR₅R₂ : yamadaR₅ d t ≤ normalizer (yamadaR₂ d t : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _
  have hR₅L₂ : yamadaR₅ d t ≤ normalizer (yamadaL₂ d t : Set G) :=
    hR₅R₂.trans (h.normalizer_yamadaR₂_le_normalizer_yamadaL₂ d hK hD)
  have hR₅L₆ : yamadaR₅ d t ≤ normalizer (yamadaL₆ d t : Set G) :=
    hR₅L₂.trans (le_normalizer_yamadaL₆ d t)
  have hR₅R₃ : yamadaR₅ d t ≤ normalizer (yamadaR₃ d t : Set G) :=
    (h.yamada_5_27_2 hW d hK hD).1.2.2.1
  have hR₅R₆ : yamadaR₅ d t ≤ normalizer (yamadaR₆ d t : Set G) := fun x hx => by
    rw [h.yamadaR₆_eq_sup_R₃ hW d hK hQ]
    exact Common.mem_normalizer_sup (hR₅L₆ hx) (hR₅R₃ hx)
  have hNCS : centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤
      normalizer (yamadaL₆ d t : Set G) :=
    (h.centralizer_inf_normalizer_S_le_Y d hK hD).trans
      (h.centralizer_inf_normalizer_Y_le_normalizer_yamadaL₆ d)
  have hR₅p : IsPGroup 2 (yamadaR₅ d t) := LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hP : IsPGroup 2 (yamadaL₆ d t ⊔ yamadaR₅ d t : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (isPGroup_yamadaL₆ d t) hR₅p hR₅L₆
  have hQR : (yamadaL₆ d t ⊔ yamadaR₅ d t) ⊓
      (centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G)) ≤ yamadaR d t := by
    refine h.le_yamadaR_of_normal d hK inf_le_right ?_ (hP.to_le inf_le_left)
    intro c' hc'
    have hNP : c' ∈ normalizer ((yamadaL₆ d t ⊔ yamadaR₅ d t : Subgroup G) : Set G) :=
      Common.mem_normalizer_sup (hNCS hc') (LieType.BorelTits.le_normalizer_pCoreOf 2 _
        ((h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD).1 hc'))
    exact Common.mem_normalizer_inf hNP (Subgroup.le_normalizer hc')
  intro x hx
  obtain ⟨l, hl, c, hc, rfl⟩ := h.exists_mul_of_mem_normalizer_yamadaL₂ hW d hK hQ (hR₅L₂ hx)
  have hl₆ : l ∈ yamadaR₆ d t := mem_sup_left hl
  have hcR₆ : c ∈ normalizer (yamadaR₆ d t : Set G) := by
    have := mul_mem (inv_mem (Subgroup.le_normalizer hl₆)) (hR₅R₆ hx)
    rwa [inv_mul_cancel_left] at this
  have hcR : c ∈ normalizer (yamadaR d t : Set G) := by
    rw [← h.yamadaR₆_inf_centralizer hW d hK hQ]
    exact Common.mem_normalizer_inf hcR₆ (Subgroup.le_normalizer hc.1)
  have hcS : c ∈ normalizer (d.S : Set G) := by
    rw [← h.yamadaR_inf_L d]
    exact Common.mem_normalizer_inf hcR (h.centralizer_le_normalizer hc.1)
  have hcP : c ∈ (yamadaL₆ d t ⊔ yamadaR₅ d t : Subgroup G) := by
    have := mul_mem (inv_mem (mem_sup_left hl : l ∈ yamadaL₆ d t ⊔ yamadaR₅ d t))
      (mem_sup_right hx : l * c ∈ yamadaL₆ d t ⊔ yamadaR₅ d t)
    rwa [inv_mul_cancel_left] at this
  have hcR' : c ∈ yamadaR d t := hQR ⟨hcP, hc.1, hcS⟩
  exact mul_mem hl₆ (h.yamadaR_le_yamadaR₆ hW d hK hQ hcR')

private theorem yamadaR₆_inf_normalizer_yamadaR₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₆ d t ⊓ normalizer (yamadaR₂ d t : Set G) = yamadaR₅ d t := by
  have hD := hQ.doubling
  have hR₅R₆ := h.yamadaR₅_le_yamadaR₆ hW d hK hQ
  refine le_antisymm (fun x hx => ?_) (le_inf hR₅R₆ (LieType.BorelTits.pCoreOf_le 2 _))
  obtain ⟨hx₆, hxN⟩ := Subgroup.mem_inf.1 hx
  have hx' : x ∈ ((normalizer (yamadaR₂ d t : Set G) : Subgroup G) : Set G) := hxN
  rw [(h.yamada_5_27_1 hW d hK hD).2.1] at hx'
  obtain ⟨r, hr, c, hc, rfl⟩ := Set.mem_mul.1 hx'
  have hcR₆ : c ∈ yamadaR₆ d t := by
    have := mul_mem (inv_mem (hR₅R₆ hr)) hx₆
    rwa [inv_mul_cancel_left] at this
  have hcR : c ∈ yamadaR d t := by
    rw [← h.yamadaR₆_inf_centralizer hW d hK hQ]
    exact ⟨hcR₆, hc.1⟩
  exact mul_mem hr ((h.yamadaR₂_le_yamadaR₅ hW d hK hQ)
    ((h.yamadaR₂_inf_centralizer d hK).1 hcR))

private theorem yamadaR₅_eq_inf_normalizer (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₅ d t = yamadaR₆ d t ⊓ normalizer (yamadaR₃ d t : Set G) := by
  have hD := hQ.doubling
  refine le_antisymm (le_inf (h.yamadaR₅_le_yamadaR₆ hW d hK hQ)
    (h.yamada_5_27_2 hW d hK hD).1.2.2.1) (fun x hx => ?_)
  obtain ⟨hx₆, hxN⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨⟨-, -, hE₃R₃, -, -⟩, -, -, hE₃c, -, -⟩ := h.yamada_5_35_4 hW d hK hQ
  have hxE₃ : x ∈ normalizer (yamadaE₃ d t : Set G) :=
    normalizer_le_normalizer_of_characteristic_subgroupOf hE₃R₃ hE₃c hxN
  have hxL₂ : x ∈ normalizer (yamadaL₂ d t : Set G) := h.yamadaR₆_le_normalizer_yamadaL₂ d hx₆
  have hxE₂ : x ∈ normalizer (yamadaE₂ d t : Set G) := by
    rw [← h.yamadaL₂_inf_yamadaE₃ hW d hK hD]
    exact Common.mem_normalizer_inf hxL₂ hxE₃
  have hxR₂ : x ∈ normalizer (yamadaR₂ d t : Set G) := by
    rw [(h.yamada_5_21_4 hW d hK hD).1]
    exact hxE₂
  rw [← h.yamadaR₆_inf_normalizer_yamadaR₂ hW d hK hQ]
  exact Subgroup.mem_inf.2 ⟨hx₆, hxR₂⟩

private theorem mem_yamadaR₅_iff_of_rel (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {Rel : G → G → Prop}
    (hR : L₆Rel d t Rel) {l m : G} (hlm : Rel l m) : l ∈ yamadaR₅ d t ↔ m ∈ d.F := by
  have hD := hQ.doubling
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨-, -, hYW, -, hWF, -, hFM, -, hMS, -⟩ := d.inclusions
  have hSCY : d.S ≤ centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G) := fun s hs =>
    Subgroup.mem_inf.2 ⟨h.S_le_centralizer d hs, d.S_le_normalizers.2.1 hs⟩
  have hl₆ : l ∈ yamadaL₆ d t := (hR.mem l m hlm).1
  have hL₆L₃ : yamadaL₆ d t ≤ normalizer (yamadaL₃ d t : Set G) :=
    (yamadaL₆_le d t).trans (h.yamada_5_39_1 hW d hK hQ).1.2.2
  have hSL₃ : d.S ≤ normalizer (yamadaL₃ d t : Set G) := fun s hs =>
    (h.yamadaL₃_facts hW d hK hD).2.2.1 (mem_sup_right hs)
  constructor
  · intro hl₅
    obtain ⟨f₂, hf₂, e⟩ := (h.yamada_5_21_3 hW d hK hD).1 l
      (LieType.BorelTits.pCoreOf_le 2 _ hl₅)
    obtain ⟨φ, hφ, η, hη, rfl⟩ := Common.exists_mul_of_le_normalizer
      (h.yamadaY₂_le_normalizer_F d hK hD) f₂ hf₂
    have hrel := hR.crossed l φ η hη hl₆ (hFM hφ) (by rw [e]; group)
    have hmW := inv_mul_mem_W_of_rel hR hrel hlm
    have := mul_mem hφ (hWF hmW)
    rwa [mul_inv_cancel_left] at this
  · intro hmF
    have hc : ∀ s ∈ d.S, s * l * s⁻¹ * l⁻¹ ∈ yamadaL₃ d t := by
      intro s hs
      have hsm : s * m * s⁻¹ * m⁻¹ ∈ d.W := by
        have := inv_mem ((d.mem_F_iff_commutator hK4 (hMS (hFM hmF))).1 hmF s hs)
        rw [commutatorElement_inv] at this
        exact hYW this
      have hr1 := hR.conj s (hSCY hs) l m hlm
      have hr2 := hR.mul _ _ _ _ hr1 (hR.inv _ _ hlm)
      exact (hR.mem_L₃_iff _ _ hr2).2 hsm
    have haN : l ∈ normalizer (yamadaR₃ d t : Set G) := by
      refine mem_normalizer_of_conj_mem fun r hr => ?_
      obtain ⟨l₃, hl₃, s, hs, rfl⟩ := Common.exists_mul_of_le_normalizer hSL₃ r hr
      have h1' : l * l₃ * l⁻¹ ∈ yamadaL₃ d t := (mem_normalizer_iff.1 (hL₆L₃ hl₆) l₃).1 hl₃
      have h3' : (s * l * s⁻¹ * l⁻¹)⁻¹ ∈ yamadaL₃ d t := inv_mem (hc s hs)
      rw [show l * (l₃ * s) * l⁻¹ = (l * l₃ * l⁻¹) * ((s * l * s⁻¹ * l⁻¹)⁻¹ * s) by group]
      exact mul_mem (mem_sup_left h1') (mul_mem (mem_sup_left h3') (mem_sup_right hs))
    rw [h.yamadaR₅_eq_inf_normalizer hW d hK hQ]
    exact Subgroup.mem_inf.2 ⟨mem_sup_left hl₆, haN⟩

private theorem commutator_mem_F (d : G2Data L K) (hK : 4 ≤ Nat.card K) {s m : G} (hs : s ∈ d.S)
    (hm : m ∈ d.S) : s * m * s⁻¹ * m⁻¹ ∈ d.F := by
  have := Subgroup.commutator_mem_commutator hs hm
  rw [(d.yamada_3_12_commutators hK).2.2.1] at this
  exact this

private theorem exists_hom_yamadaR₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∃ _ : (d.F.subgroupOf d.M).Normal, ∃ ψ : yamadaR₆ d t →* d.M ⧸ d.F.subgroupOf d.M,
      (∀ (x : yamadaR₆ d t) (m : d.M), ∀ y ∈ yamadaY₂ d t,
        (x : G) * t * (x : G)⁻¹ = t * m * y → ψ x = QuotientGroup.mk m) ∧
      Function.Surjective ψ ∧ ψ.ker = (yamadaR₅ d t).subgroupOf (yamadaR₆ d t) ∧
      ∀ c ∈ centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G),
        ∀ (x : yamadaR₆ d t) (m : d.M), ψ x = QuotientGroup.mk m →
          ∃ (hx : c * x * c⁻¹ ∈ yamadaR₆ d t) (hm : c * m * c⁻¹ ∈ d.M),
            ψ ⟨_, hx⟩ = QuotientGroup.mk ⟨_, hm⟩ := by
  have hD := hQ.doubling
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨-, -, -, -, hWF, -, hFM, -, hMS, -⟩ := d.inclusions
  obtain ⟨Rel, hRel⟩ := h.exists_rel_yamadaL₆ hW d hK hQ
  obtain ⟨hmem, h1, h2, h3, -, h5, h6, h7⟩ := id hRel
  have hNF := h.centralizer_inf_normalizer_S_le_normalizer_F d hK hD
  have hSCY : d.S ≤ centralizer ({t} : Set G) ⊓ normalizer (d.Y : Set G) := fun s hs =>
    Subgroup.mem_inf.2 ⟨h.S_le_centralizer d hs, d.S_le_normalizers.2.1 hs⟩
  have hMF : (d.F.subgroupOf d.M).Normal := by
    refine (normal_subgroupOf_iff_le_normalizer hFM).2 fun m hm => ?_
    exact d.S_le_normalizers.2.2.2.2.1 (hMS hm)
  let RQ : G → d.M ⧸ d.F.subgroupOf d.M → Prop := fun l q =>
    ∃ (m : G) (hm : m ∈ d.M), Rel l m ∧ q = QuotientGroup.mk ⟨m, hm⟩
  have hmkeq : ∀ m m' (hm : m ∈ d.M) (hm' : m' ∈ d.M), m⁻¹ * m' ∈ d.F →
      (QuotientGroup.mk ⟨m, hm⟩ : d.M ⧸ d.F.subgroupOf d.M) = QuotientGroup.mk ⟨m', hm'⟩ :=
    fun m m' hm hm' hF => by
      rw [QuotientGroup.eq, mem_subgroupOf]
      exact hF
  have htot : ∀ a ∈ yamadaL₆ d t, ∃ q, RQ a q := by
    intro a ha
    obtain ⟨m, hm⟩ := h1 a ha
    exact ⟨QuotientGroup.mk ⟨m, (hmem a m hm).2⟩, m, (hmem a m hm).2, hm, rfl⟩
  have hmul : ∀ a a' q q', a ∈ yamadaL₆ d t → a' ∈ yamadaL₆ d t → RQ a q → RQ a' q' →
      RQ (a * a') (q * q') := by
    rintro a a' q q' - - ⟨m, hm, hr, rfl⟩ ⟨m', hm', hr', rfl⟩
    exact ⟨m * m', mul_mem hm hm', h3 _ _ _ _ hr hr', by rw [← QuotientGroup.mk_mul]; rfl⟩
  have hfun : ∀ a q q', a ∈ yamadaL₆ d t → RQ a q → RQ a q' → q = q' := by
    rintro a q q' - ⟨m, hm, hr, rfl⟩ ⟨m', hm', hr', rfl⟩
    exact hmkeq m m' hm hm' (hWF (inv_mul_mem_W_of_rel hRel hr hr'))
  have hinv : ∀ a q b, a ∈ yamadaL₆ d t → b ∈ d.S → RQ a q → RQ (b * a * b⁻¹) q := by
    rintro a q b - hb ⟨m, hm, hr, rfl⟩
    have hr' := h7 b (hSCY hb) a m hr
    refine ⟨b * m * b⁻¹, (hmem _ _ hr').2, hr', hmkeq _ _ hm (hmem _ _ hr').2 ?_⟩
    have := commutator_mem_F d hK4 (hMS (inv_mem hm)) hb
    simpa [mul_assoc] using this
  have hker : ∀ a ∈ yamadaL₆ d t, a ∈ d.S → RQ a 1 := by
    intro a ha has
    have haM : a ∈ d.M := by
      rw [← h.yamadaL₆_inf_S hW d hK hQ]
      exact ⟨ha, has⟩
    obtain ⟨-, -, -, -, hL₃S⟩ := h.yamadaL₃_facts hW d hK hD
    have haL₃ : a ∈ yamadaL₃ d t := by
      rw [← hL₃S] at haM
      exact haM.1
    obtain ⟨m, hm⟩ := h1 a ha
    have hmW := (h5 a m hm).1 haL₃
    refine ⟨m, (hmem _ _ hm).2, hm, ((QuotientGroup.eq_one_iff _).2 ?_).symm⟩
    rw [mem_subgroupOf]
    exact hWF hmW
  obtain ⟨ψ, hψ⟩ : ∃ ψ : yamadaR₆ d t →* d.M ⧸ d.F.subgroupOf d.M,
      ∀ (x : yamadaR₆ d t) a q b, a ∈ yamadaL₆ d t → b ∈ d.S → (x : G) = a * b → RQ a q →
        ψ x = q :=
    exists_hom_sup_of_rel (h.S_le_normalizer_yamadaL₆ d) RQ htot hmul hfun hinv hker
  have hdec : ∀ x : yamadaR₆ d t, ∃ a ∈ yamadaL₆ d t, ∃ b ∈ d.S, (x : G) = a * b := fun x =>
    Common.exists_mul_of_le_normalizer (h.S_le_normalizer_yamadaL₆ d) x x.2
  have hSR₅ : d.S ≤ yamadaR₅ d t :=
    (le_sup_right : d.S ≤ yamadaR₂ d t).trans (h.yamadaR₂_le_yamadaR₅ hW d hK hQ)
  refine ⟨hMF, ψ, ?_, ?_, ?_, ?_⟩
  ·
    intro x m y hy e
    obtain ⟨a, ha, b, hb, hx⟩ := hdec x
    have hbt : b * t = t * b := mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hb)
    have e' : a * t * a⁻¹ = t * m * y := by
      rw [hx] at e
      calc a * t * a⁻¹ = a * (b * t * b⁻¹) * a⁻¹ := by rw [hbt]; group
        _ = (a * b) * t * (a * b)⁻¹ := by group
        _ = _ := e
    exact hψ x a _ b ha hb hx ⟨m, m.2, h6 a m y hy ha m.2 e', rfl⟩
  ·
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨l, hl⟩ := h2 m m.2
    have hl6 : l ∈ yamadaL₆ d t := (hmem _ _ hl).1
    exact ⟨⟨l, mem_sup_left hl6⟩, hψ _ l _ 1 hl6 (one_mem _) (mul_one _).symm
      ⟨m, m.2, hl, rfl⟩⟩
  ·
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    obtain ⟨a, ha, b, hb, hx⟩ := hdec x
    obtain ⟨m, hm⟩ := h1 a ha
    have hψx : ψ x = QuotientGroup.mk ⟨m, (hmem _ _ hm).2⟩ :=
      hψ x a _ b ha hb hx ⟨m, _, hm, rfl⟩
    rw [hψx]
    have hiff := mem_yamadaR₅_iff_of_rel hW h d hK hQ hRel hm
    constructor
    · intro h1'
      have hmF : m ∈ d.F := by
        have := (QuotientGroup.eq_one_iff _).1 h1'
        rwa [mem_subgroupOf] at this
      rw [hx]
      exact mul_mem (hiff.2 hmF) (hSR₅ hb)
    · intro hx₅
      have ha₅ : a ∈ yamadaR₅ d t := by
        have := mul_mem hx₅ (inv_mem (hSR₅ hb))
        rwa [hx, mul_inv_cancel_right] at this
      exact (QuotientGroup.eq_one_iff _).2 (by rw [mem_subgroupOf]; exact hiff.1 ha₅)
  ·
    intro c hc x m hxm
    obtain ⟨a, ha, b, hb, hx⟩ := hdec x
    obtain ⟨m₀, hm₀⟩ := h1 a ha
    have hψx : ψ x = QuotientGroup.mk ⟨m₀, (hmem _ _ hm₀).2⟩ :=
      hψ x a _ b ha hb hx ⟨m₀, _, hm₀, rfl⟩
    have hmm₀ : m₀⁻¹ * m ∈ d.F := by
      rw [hψx] at hxm
      have := QuotientGroup.eq.1 hxm
      rwa [mem_subgroupOf] at this
    have hcY := h.centralizer_inf_normalizer_S_le_Y d hK hD hc
    have hcN : c ∈ normalizer (yamadaR₆ d t : Set G) :=
      Common.mem_normalizer_sup (h.centralizer_inf_normalizer_Y_le_normalizer_yamadaL₆ d hcY) hc.2
    have hr := h7 c hcY a m₀ hm₀
    have hcF : ∀ g ∈ d.F, c * g * c⁻¹ ∈ d.F := fun g hg => (mem_normalizer_iff.1 (hNF hc) g).1 hg
    have hx' : c * (x : G) * c⁻¹ ∈ yamadaR₆ d t := (mem_normalizer_iff.1 hcN x).1 x.2
    have hcm : c * (m : G) * c⁻¹ = (c * m₀ * c⁻¹) * (c * (m₀⁻¹ * m) * c⁻¹) := by group
    have hm' : c * (m : G) * c⁻¹ ∈ d.M := by
      rw [hcm]
      exact mul_mem (hmem _ _ hr).2 (hFM (hcF _ hmm₀))
    refine ⟨hx', hm', ?_⟩
    have hca : c * a * c⁻¹ ∈ yamadaL₆ d t := (hmem _ _ hr).1
    have hcb : c * b * c⁻¹ ∈ d.S := (mem_normalizer_iff.1 hc.2 b).1 hb
    rw [hψ ⟨c * (x : G) * c⁻¹, hx'⟩ (c * a * c⁻¹) _ (c * b * c⁻¹) hca hcb
      (by show c * (x : G) * c⁻¹ = _; rw [hx]; group)
      ⟨c * m₀ * c⁻¹, (hmem _ _ hr).2, hr, rfl⟩]
    refine hmkeq _ _ (hmem _ _ hr).2 hm' ?_
    rw [show (c * m₀ * c⁻¹)⁻¹ * (c * (m : G) * c⁻¹) = c * (m₀⁻¹ * m) * c⁻¹ by group]
    exact hcF _ hmm₀

private theorem mem_yamadaL₆_of_forall_J₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ yamadaR₆ d t)
    (hfix : ∀ j ∈ d.J₆, x⁻¹ * (j * x * j⁻¹) ∈ yamadaL₆ d t) : x ∈ yamadaL₆ d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := hQ.doubling
  obtain ⟨hJ₆J, -, hC, -⟩ := h.J₆_facts d hK
  obtain ⟨-, -, -, hXF, -, -, hFM, -, hMS, -⟩ := d.inclusions
  have hJC := h.J_le_centralizer_inf_normalizer_S d
  have hML₆ : d.M ≤ yamadaL₆ d t := (h.yamadaL₆_inf_S hW d hK hQ).ge.trans inf_le_left
  have hR₆L₆ : yamadaR₆ d t ≤ normalizer (yamadaL₆ d t : Set G) :=
    sup_le Subgroup.le_normalizer (h.S_le_normalizer_yamadaL₆ d)
  have hJL₆ : d.J ≤ normalizer (yamadaL₆ d t : Set G) := fun j hj =>
    h.centralizer_inf_normalizer_Y_le_normalizer_yamadaL₆ d
      (h.centralizer_inf_normalizer_S_le_Y d hK hD (hJC hj))
  have hJM : d.J ≤ normalizer (d.M : Set G) := fun j hj => by
    rw [← h.yamadaL₆_inf_S hW d hK hQ]
    exact Common.mem_normalizer_inf (hJL₆ hj) (Subgroup.mem_inf.1 (hJC hj)).2
  obtain ⟨l, hl, s, hs, rfl⟩ :=
    Common.exists_mul_of_le_normalizer (h.S_le_normalizer_yamadaL₆ d) x hx
  have hfixs : ∀ j ∈ d.J₆, s⁻¹ * (j * s * j⁻¹) ∈ d.M := fun j hj => by
    rw [← h.yamadaL₆_inf_S hW d hK hQ]
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (inv_mem hs)
      ((mem_normalizer_iff.1 (Subgroup.mem_inf.1 (hJC (hJ₆J hj))).2 _).1 hs)⟩
    have h1 : j * l⁻¹ * j⁻¹ ∈ yamadaL₆ d t :=
      (mem_normalizer_iff.1 (hJL₆ (hJ₆J hj)) _).1 (inv_mem hl)
    have h2 : (l * s)⁻¹ * (l * (j * l⁻¹ * j⁻¹)) * (l * s) ∈ yamadaL₆ d t := by
      have := (mem_normalizer_iff.1 (inv_mem (hR₆L₆ hx)) _).1 (mul_mem hl h1)
      rwa [inv_inv] at this
    rw [show s⁻¹ * (j * s * j⁻¹) = (l * s)⁻¹ * (l * (j * l⁻¹ * j⁻¹)) * (l * s) *
      ((l * s)⁻¹ * (j * (l * s) * j⁻¹)) by group]
    exact mul_mem h2 (hfix j hj)
  have hSp : IsPGroup 2 d.S := d.isSylowOf_S.isPGroup
  obtain ⟨c, hc, m, hm, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime
    (M := d.S) (N := d.M) (S := d.J₆) hMS d.S_le_normalizers.2.2.2.2.2.2
    (fun j hj => (Subgroup.mem_inf.1 (hJC (hJ₆J hj))).2)
    (fun j hj => hJM (hJ₆J hj))
    (have : Group.IsNilpotent d.S := hSp.isNilpotent; inferInstance)
    (by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hSp
      rw [hk]
      exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2
        ((odd_card_J d).of_dvd_nat (Subgroup.card_dvd_of_le hJ₆J))))
    hs hfixs
  have hcM : c ∈ d.M := by
    rw [hC] at hc
    exact hFM (hXF ((le_sup_left.trans d.yamada_defs.2.1.le) hc))
  exact mul_mem hl (mul_mem (hML₆ hcM) (hML₆ hm))

theorem yamada_5_40_1 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₅ d t = yamadaR₆ d t ⊓ normalizer (yamadaR₃ d t : Set G) ∧
      yamadaR₆ d t ≤ normalizer (yamadaR₅ d t : Set G) := by
  obtain ⟨_hMF, ψ, -, -, hker, -⟩ := h.exists_hom_yamadaR₆ hW d hK hQ
  have hN : ((yamadaR₅ d t).subgroupOf (yamadaR₆ d t)).Normal := hker ▸ ψ.normal_ker
  exact ⟨h.yamadaR₅_eq_inf_normalizer hW d hK hQ,
    (normal_subgroupOf_iff_le_normalizer (h.yamadaR₅_le_yamadaR₆ hW d hK hQ)).1 hN⟩

theorem yamada_5_40_3 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∃ _ : ((yamadaR₅ d t).subgroupOf (yamadaR₆ d t)).Normal,
      ∃ _ : (d.F.subgroupOf d.M).Normal,
        ∃ φ : yamadaR₆ d t ⧸ (yamadaR₅ d t).subgroupOf (yamadaR₆ d t) ≃*
          d.M ⧸ d.F.subgroupOf d.M,
        (∀ (x : yamadaR₆ d t) (m : d.M), ∀ y ∈ yamadaY₂ d t,
          (x : G) * t * (x : G)⁻¹ = t * m * y → φ (QuotientGroup.mk x) = QuotientGroup.mk m) ∧
        ∀ c ∈ centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G),
          ∀ (x : yamadaR₆ d t) (m : d.M), φ (QuotientGroup.mk x) = QuotientGroup.mk m →
            ∃ (hx : c * x * c⁻¹ ∈ yamadaR₆ d t) (hm : c * m * c⁻¹ ∈ d.M),
              φ (QuotientGroup.mk ⟨_, hx⟩) = QuotientGroup.mk ⟨_, hm⟩ := by
  obtain ⟨hMF, ψ, hψ, hsurj, hker, hequi⟩ := h.exists_hom_yamadaR₆ hW d hK hQ
  have hN : ((yamadaR₅ d t).subgroupOf (yamadaR₆ d t)).Normal := hker ▸ ψ.normal_ker
  set φ := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj) with hφdef
  have hφ : ∀ x : yamadaR₆ d t, φ (QuotientGroup.mk x) = ψ x := fun _ => rfl
  refine ⟨hN, hMF, φ, fun x m y hy e => (hφ x).trans (hψ x m y hy e), fun c hc x m hxm => ?_⟩
  rw [hφ] at hxm
  obtain ⟨hx, hm, e⟩ := hequi c hc x m hxm
  exact ⟨hx, hm, (hφ _).trans e⟩

theorem yamada_5_40_4 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaL₅ d t = yamadaL₆ d t ⊓ yamadaR₅ d t := by
  have hD := hQ.doubling
  have hR₅R₆ := h.yamadaR₅_le_yamadaR₆ hW d hK hQ
  obtain ⟨-, -, hR₅eq, -, hR₅L₅, -⟩ := h.yamada_5_37_1 hW d hK hQ
  have hR₃R₅ : yamadaR₃ d t ≤ yamadaR₅ d t := hR₅eq ▸ le_sup_right
  have hR₄R₅ : yamadaR₄ d t ≤ yamadaR₅ d t := by
    rw [(h.yamada_5_27_2 hW d hK hD).1.1]
    exact le_sup_right
  have hL₃R₃ : yamadaL₃ d t ≤ yamadaR₃ d t := le_sup_left
  have hL₄R₄ : yamadaL₄ d t ≤ yamadaR₄ d t := (h.yamadaL₄_facts hW d hK hD).2.2.2.2.1
  have hL₃L₆ := h.yamadaL₃_le_yamadaL₆ hW d hK hQ
  have hL₄L₆ : yamadaL₄ d t ≤ yamadaL₆ d t := by
    refine sup_le (fun z hz => ?_) (h.yamadaL₂_le_yamadaL₆ hW d hK hQ)
    obtain ⟨hzR₄, hzJ⟩ := Subgroup.mem_inf.1 hz
    refine h.mem_yamadaL₆_of_forall_J₆ hW d hK hQ (hR₅R₆ (hR₄R₅ hzR₄)) fun j hj => ?_
    rw [mem_centralizer_iff.1 hzJ j hj, mul_inv_cancel_right, inv_mul_cancel]
    exact one_mem _
  have hL₅L₆ : yamadaL₅ d t ≤ yamadaL₆ d t := sup_le hL₃L₆ hL₄L₆
  have hL₃L₅ : yamadaL₃ d t ≤ yamadaL₅ d t := le_sup_left
  refine le_antisymm (le_inf hL₅L₆ (sup_le (hL₃R₃.trans hR₃R₅) (hL₄R₄.trans hR₄R₅)))
    (fun x hx => ?_)
  obtain ⟨hx₆, hx₅⟩ := Subgroup.mem_inf.1 hx
  have hR₃L₅ : yamadaR₃ d t ≤ normalizer (yamadaL₅ d t : Set G) := hR₃R₅.trans hR₅L₅
  have hSL₃ : d.S ≤ normalizer (yamadaL₃ d t : Set G) := fun s hs =>
    (h.yamadaL₃_facts hW d hK hD).2.2.1 (mem_sup_right hs)
  rw [hR₅eq] at hx₅
  obtain ⟨a, ha, b, hb, rfl⟩ := Common.exists_mul_of_le_normalizer hR₃L₅ x hx₅
  obtain ⟨l₃, hl₃, s, hs, rfl⟩ := Common.exists_mul_of_le_normalizer hSL₃ b hb
  have hal : a * l₃ ∈ yamadaL₅ d t := mul_mem ha (hL₃L₅ hl₃)
  have hsL₆ : s ∈ yamadaL₆ d t := by
    have := mul_mem (inv_mem (hL₅L₆ hal)) hx₆
    rwa [show (a * l₃)⁻¹ * (a * (l₃ * s)) = s by group] at this
  have hsM : s ∈ d.M := by
    rw [← h.yamadaL₆_inf_S hW d hK hQ]
    exact ⟨hsL₆, hs⟩
  have hsL₃ : s ∈ yamadaL₃ d t := by
    obtain ⟨-, -, -, -, hL₃S⟩ := h.yamadaL₃_facts hW d hK hD
    rw [← hL₃S] at hsM
    exact hsM.1
  rw [← mul_assoc]
  exact mul_mem hal (hL₃L₅ hsL₃)

theorem yamada_5_42 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₆ d t ⊓ normalizer (yamadaR₂ d t : Set G) = yamadaR₅ d t ∧
      yamadaR₆ d t ⊓ normalizer (yamadaS₂ d t : Set G) = yamadaR₅ d t ∧
      yamadaR₆ d t ⊓ normalizer (yamadaC₁ d t : Set G) = yamadaR₅ d t := by
  have hD := hQ.doubling
  have hR₅R₆ := h.yamadaR₅_le_yamadaR₆ hW d hK hQ
  have hR₅N : yamadaR₅ d t ≤ normalizer (yamadaR₂ d t : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _
  have h1 := h.yamadaR₆_inf_normalizer_yamadaR₂ hW d hK hQ
  obtain ⟨-, -, hC₁c, hS₂c⟩ := h.yamada_5_15_6 d hK hD
  have hY₂L₂ : yamadaY₂ d t ≤ yamadaL₂ d t := h.yamadaY₂_le_yamadaL₂ d hK hD
  have hR₂S₂ : yamadaR₂ d t = yamadaL₂ d t ⊔ yamadaS₂ d t :=
    le_antisymm (sup_le le_sup_left (le_sup_left.trans le_sup_right))
      (sup_le le_sup_left (sup_le le_sup_right (hY₂L₂.trans le_sup_left)))
  have hS₂R₂ : yamadaS₂ d t ≤ yamadaR₂ d t := hR₂S₂ ▸ le_sup_right
  have hC₁R₂ : yamadaC₁ d t ≤ yamadaR₂ d t := h.yamadaC₁_le_yamadaR₂ d hK
  have hR₂C₁ : yamadaR₂ d t = yamadaL₂ d t ⊔ yamadaC₁ d t := (h.yamada_5_6_1 d hK).2.2.2.1
  refine ⟨h1, le_antisymm (fun x hx => ?_) (le_inf hR₅R₆ fun y hy =>
    normalizer_le_normalizer_of_characteristic_subgroupOf hS₂R₂ hS₂c (hR₅N hy)),
    le_antisymm (fun x hx => ?_) (le_inf hR₅R₆ fun y hy =>
    normalizer_le_normalizer_of_characteristic_subgroupOf hC₁R₂ hC₁c (hR₅N hy))⟩
  · obtain ⟨hx₆, hxN⟩ := Subgroup.mem_inf.1 hx
    rw [← h1]
    refine Subgroup.mem_inf.2 ⟨hx₆, ?_⟩
    rw [hR₂S₂]
    exact Common.mem_normalizer_sup (h.yamadaR₆_le_normalizer_yamadaL₂ d hx₆) hxN
  · obtain ⟨hx₆, hxN⟩ := Subgroup.mem_inf.1 hx
    rw [← h1]
    refine Subgroup.mem_inf.2 ⟨hx₆, ?_⟩
    rw [hR₂C₁]
    exact Common.mem_normalizer_sup (h.yamadaR₆_le_normalizer_yamadaL₂ d hx₆) hxN

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
