module

public import CFSG.CGT.PushingUpLit.A78G0.Basic
public import CFSG.CGT.PushingUpLit.A78.OppSL2
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.CGT.PushingUpLit.A78G0

section SL2

variable {e : ℕ}

theorem inf_eq_bot_of_card_SL2 (he : 2 ≤ e) {A B : Subgroup (Matrix.SpecialLinearGroup (Fin 2)
    (GaloisField 2 e))} (hA : Nat.card A = 2 ^ e) (hB : Nat.card B = 2 ^ e) (hAB : A ≠ B) :
    A ⊓ B = ⊥ :=
  (CFSG.CGT.PushingUpLit.A78.opposite_of_sylow_sl2 he (K := ⊤) Subgroup.topEquiv le_top le_top
    hA hB hAB).inf_eq_bot

theorem ncard_card_SL2 (he : 2 ≤ e) :
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) |
      Nat.card P = 2 ^ e}.ncard = 2 ^ e + 1 := by
  have := CFSG.CGT.PushingUpLit.A78.ncard_sylow_sl2 he (K := ⊤) Subgroup.topEquiv
  simpa using this

theorem exists_cs_eq_of_card_SL2 (he : 2 ≤ e) {A B : Subgroup (Matrix.SpecialLinearGroup (Fin 2)
    (GaloisField 2 e))} (hA : Nat.card A = 2 ^ e) (hB : Nat.card B = 2 ^ e) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e), B = cs A s := by
  have h := CFSG.CGT.PushingUpLit.A78.isElemAbRankOne_upper_lower (GaloisField 2 e)
  have hU := CFSG.CGT.PushingUpLit.A78.card_upperUnipotent_gf (e := e) (by omega)
  obtain ⟨x, hx⟩ := CFSG.Timmesfeld.ARS.ElemAbRankOne.exists_eq_map_conj h
    (IsPGroup.of_card hA) (hA.trans hU.symm)
  obtain ⟨y, hy⟩ := CFSG.Timmesfeld.ARS.ElemAbRankOne.exists_eq_map_conj h
    (IsPGroup.of_card hB) (hB.trans hU.symm)
  refine ⟨y * x⁻¹, ?_⟩
  rw [cs_mul]
  have e1 : cs A x⁻¹ = CFSG.Timmesfeld.upperUnipotent (GaloisField 2 e) := by
    rw [hx]
    exact cs_cs_inv _ x
  rw [e1]
  exact hy

end SL2

section Counting

variable {G : Type} [Group G]

theorem ncard_conj_class (X H : Subgroup G) :
    {C : Subgroup G | ∃ x ∈ X, C = cs H x}.ncard =
      ((Subgroup.normalizer (H : Set G)).subgroupOf X).index := by
  set N : Subgroup ↥X := (Subgroup.normalizer (H : Set G)).subgroupOf X with hN
  have key : ∀ a b : ↥X, cs H (a : G) = cs H (b : G) ↔ a⁻¹ * b ∈ N := by
    intro a b
    have hb : (b : G) = (a : G) * (((a⁻¹ * b : ↥X)) : G) := by simp
    have e1 : cs H (b : G) = cs (cs H (((a⁻¹ * b : ↥X)) : G)) (a : G) := by
      rw [← cs_mul, ← hb]
    rw [hN, Subgroup.mem_subgroupOf, e1, cs_inj_iff]
    constructor
    · intro h
      exact mem_normalizer_of_cs_eq h.symm
    · intro h
      exact (cs_of_mem_normalizer h).symm
  let f : ↥X ⧸ N → Subgroup G := fun p =>
    Quotient.liftOn' p (fun x : ↥X => cs H (x : G))
      (fun a b hab => (key a b).2 (QuotientGroup.leftRel_apply.1 hab))
  have hinj : Function.Injective f := by
    intro p q hpq
    induction p using Quotient.inductionOn' with | _ a => ?_
    induction q using Quotient.inductionOn' with | _ b => ?_
    exact Quotient.sound' (QuotientGroup.leftRel_apply.2 ((key a b).1 hpq))
  have hrange : Set.range f = {C | ∃ x ∈ X, C = cs H x} := by
    ext C
    constructor
    · rintro ⟨p, rfl⟩
      induction p using Quotient.inductionOn' with | _ a => exact ⟨a, a.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Quotient.mk'' ⟨x, hx⟩, rfl⟩
  rw [← hrange, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj]
  rfl

end Counting

section Images

variable {G : Type} [Group G] {L V J : Subgroup G} {e : ℕ}
  (φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e))

noncomputable def img (C : Subgroup G) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) :=
  (C.subgroupOf L).map φ

theorem mem_img {C : Subgroup G} {y : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)} :
    y ∈ img φ C ↔ ∃ c : ↥L, (c : G) ∈ C ∧ φ c = y := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, Subgroup.mem_subgroupOf.1 hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, Subgroup.mem_subgroupOf.2 hc, rfl⟩

theorem img_cs (C : Subgroup G) (x : ↥L) : img φ (cs C (x : G)) = cs (img φ C) (φ x) := by
  ext y
  rw [mem_img, mem_cs, mem_img]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨x⁻¹ * c * x, ?_, ?_⟩
    · rw [mem_cs] at hc
      exact hc
    · rw [map_mul, map_mul, map_inv]
  · rintro ⟨c, hc, hcy⟩
    refine ⟨x * c * x⁻¹, ?_, ?_⟩
    · rw [mem_cs]
      have : (x : G)⁻¹ * ((x * c * x⁻¹ : ↥L) : G) * x = c := by
        show (x : G)⁻¹ * ((x : G) * c * (x : G)⁻¹) * x = c
        group
      rw [this]
      exact hc
    · rw [map_mul, map_mul, map_inv, hcy]
      group

theorem img_le_of_le {C C' : Subgroup G} (h : C ≤ C') : img φ C ≤ img φ C' := by
  intro y hy
  obtain ⟨c, hc, rfl⟩ := (mem_img φ).1 hy
  exact (mem_img φ).2 ⟨c, h hc, rfl⟩

theorem le_of_img_le (hk : φ.ker = V.subgroupOf L) {C C' : Subgroup G} (hVC' : V ≤ C')
    (hC : C ≤ L) (h : img φ C ≤ img φ C') : C ≤ C' := by
  intro c hc
  have h1 : φ ⟨c, hC hc⟩ ∈ img φ C' := h ((mem_img φ).2 ⟨⟨c, hC hc⟩, hc, rfl⟩)
  obtain ⟨c', hc'C', hcc'⟩ := (mem_img φ).1 h1
  have hker : c'⁻¹ * (⟨c, hC hc⟩ : ↥L) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcc']
    group
  rw [hk, Subgroup.mem_subgroupOf] at hker
  have e1 : c = (c' : G) * ((c'⁻¹ * (⟨c, hC hc⟩ : ↥L) : ↥L) : G) := by
    show c = (c' : G) * ((c' : G)⁻¹ * c)
    group
  rw [e1]
  exact C'.mul_mem hc'C' (hVC' hker)

theorem card_img (hk : φ.ker = V.subgroupOf L) {C : Subgroup G} (hVC : V ≤ C) (hCL : C ≤ L) :
    Nat.card V * Nat.card (img φ C) = Nat.card C := by
  let f : ↥C →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e) :=
    φ.comp (Subgroup.inclusion hCL)
  have hker : f.ker = V.subgroupOf C := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : (φ (Subgroup.inclusion hCL x) = 1) ↔ ((Subgroup.inclusion hCL x : ↥L) ∈ φ.ker) := by
      rw [MonoidHom.mem_ker]
    show φ (Subgroup.inclusion hCL x) = 1 ↔ _
    rw [h1, hk, Subgroup.mem_subgroupOf]
    rfl
  have hrange : f.range = img φ C := by
    ext y
    rw [MonoidHom.mem_range, mem_img]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hCL x, x.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  have := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVC).toEquiv] at this
  exact this

theorem card_img_eq [Finite G] (hk : φ.ker = V.subgroupOf L) {J : Subgroup G} (hVJ : V ≤ J)
    (hJL : J ≤ L) (hJV : Nat.card J = Nat.card V * 2 ^ e) : Nat.card (img φ J) = 2 ^ e := by
  have h1 := card_img φ hk hVJ hJL
  have hpos : 0 < Nat.card V := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans hJV)

theorem conj_mem_V (hk : φ.ker = V.subgroupOf L) (hVL : V ≤ L) {x v : G} (hx : x ∈ L)
    (hv : v ∈ V) : x * v * x⁻¹ ∈ V := by
  have h1 : (⟨v, hVL hv⟩ : ↥L) ∈ φ.ker := by
    rw [hk, Subgroup.mem_subgroupOf]
    exact hv
  have h2 := (MonoidHom.normal_ker φ).conj_mem _ h1 ⟨x, hx⟩
  rw [hk, Subgroup.mem_subgroupOf] at h2
  exact h2

theorem L_le_normalizer_V (hk : φ.ker = V.subgroupOf L) (hVL : V ≤ L) :
    L ≤ Subgroup.normalizer (V : Set G) :=
  le_normalizer_of_conj' fun _ hx _ hv => conj_mem_V φ hk hVL hx hv

theorem V_le_cs (hk : φ.ker = V.subgroupOf L) (hVL : V ≤ L) {J : Subgroup G} (hVJ : V ≤ J)
    {x : G} (hx : x ∈ L) : V ≤ cs J x := by
  have := cs_mono hVJ x
  rwa [cs_of_mem_normalizer (L_le_normalizer_V φ hk hVL hx)] at this

theorem cs_le_L {J : Subgroup G} (hJL : J ≤ L) {x : G} (hx : x ∈ L) : cs J x ≤ L := by
  have := cs_mono hJL x
  rwa [cs_of_mem_normalizer (Subgroup.le_normalizer hx)] at this

theorem card_img_cs (hJq : Nat.card (img φ J) = 2 ^ e) (x : ↥L) :
    Nat.card (img φ (cs J (x : G))) = 2 ^ e := by
  rw [img_cs, card_cs, hJq]

theorem eq_of_img_eq (hk : φ.ker = V.subgroupOf L) {C C' : Subgroup G} (hVC : V ≤ C)
    (hVC' : V ≤ C') (hC : C ≤ L) (hC' : C' ≤ L) (h : img φ C = img φ C') : C = C' :=
  le_antisymm (le_of_img_le φ hk hVC' hC h.le) (le_of_img_le φ hk hVC hC' h.ge)

theorem inf_le_V_of_img_inf (hk : φ.ker = V.subgroupOf L) {C C' : Subgroup G} (hC : C ≤ L)
    (_hC' : C' ≤ L) (h : img φ C ⊓ img φ C' = ⊥) : C ⊓ C' ≤ V := by
  intro y hy
  have h1 : φ ⟨y, hC hy.1⟩ ∈ img φ C ⊓ img φ C' :=
    ⟨(mem_img φ).2 ⟨_, hy.1, rfl⟩, (mem_img φ).2 ⟨_, hy.2, rfl⟩⟩
  rw [h] at h1
  have h2 : (⟨y, hC hy.1⟩ : ↥L) ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    exact Subgroup.mem_bot.1 h1
  rw [hk, Subgroup.mem_subgroupOf] at h2
  exact h2

theorem ncard_conj_class_L (he : 2 ≤ e) (hs : Function.Surjective φ)
    (hk : φ.ker = V.subgroupOf L) (hVL : V ≤ L) {J : Subgroup G} (hVJ : V ≤ J) (hJL : J ≤ L)
    (hJq : Nat.card (img φ J) = 2 ^ e) :
    {C : Subgroup G | ∃ x ∈ L, C = cs J x}.ncard = 2 ^ e + 1 := by
  have himg : img φ '' {C : Subgroup G | ∃ x ∈ L, C = cs J x} =
      {P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) |
        Nat.card P = 2 ^ e} := by
    ext P
    constructor
    · rintro ⟨C, ⟨x, hx, rfl⟩, rfl⟩
      exact card_img_cs φ hJq ⟨x, hx⟩
    · intro hP
      obtain ⟨s, hs'⟩ := exists_cs_eq_of_card_SL2 he hJq hP
      obtain ⟨x, rfl⟩ := hs s
      exact ⟨cs J (x : G), ⟨(x : G), x.2, rfl⟩, by rw [img_cs]; exact hs'.symm⟩
  have hinj : Set.InjOn (img φ) {C : Subgroup G | ∃ x ∈ L, C = cs J x} := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ h
    exact eq_of_img_eq φ hk (V_le_cs φ hk hVL hVJ hx) (V_le_cs φ hk hVL hVJ hx')
      (cs_le_L hJL hx) (cs_le_L hJL hx') h
  rw [← hinj.ncard_image, himg]
  exact ncard_card_SL2 he

theorem inf_cs_le_V (he : 2 ≤ e) (hk : φ.ker = V.subgroupOf L) (hVL : V ≤ L)
    {J : Subgroup G} (hVJ : V ≤ J) (hJL : J ≤ L) (hJq : Nat.card (img φ J) = 2 ^ e) {x x' : G}
    (hx : x ∈ L) (hx' : x' ∈ L) (hne : cs J x ≠ cs J x') : cs J x ⊓ cs J x' ≤ V := by
  apply inf_le_V_of_img_inf φ hk (cs_le_L hJL hx) (cs_le_L hJL hx')
  have hneI : img φ (cs J x) ≠ img φ (cs J x') := fun h =>
    hne (eq_of_img_eq φ hk (V_le_cs φ hk hVL hVJ hx) (V_le_cs φ hk hVL hVJ hx')
      (cs_le_L hJL hx) (cs_le_L hJL hx') h)
  exact inf_eq_bot_of_card_SL2 he (card_img_cs φ hJq ⟨x, hx⟩) (card_img_cs φ hJq ⟨x', hx'⟩) hneI

end Images

end CFSG.CGT.PushingUpLit.A78G0
