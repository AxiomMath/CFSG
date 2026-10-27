module

public import CFSG.CGT.PushingUpLit.CGT6X.End4Perm
public import CFSG.CGT.PushingUpLit.CGT6X.End4Conf
public import CFSG.CGT.PushingUpLit.CGT6X.End4Irr
public import CFSG.CGT.PushingUpLit.CGT6X.End3G23

public section

open scoped commutatorElement

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6X.End3
  CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUp

@[expose] def fixPtwise {V : Type} [CommGroup V] (U : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | ∀ u ∈ U, g u = u}
  one_mem' := fun u _ => rfl
  mul_mem' := by
    intro a b ha hb u hu
    show a (b u) = u
    rw [hb u hu, ha u hu]
  inv_mem' := by
    intro a ha u hu
    show a⁻¹ u = u
    have := ha u hu
    calc a⁻¹ u = a⁻¹ (a u) := by rw [this]
      _ = u := MulAut.inv_apply_self V a u

section Card

variable {V : Type} [CommGroup V] [Finite V]

theorem card_mul_le_card_sup_mul_card_inf (A B : Subgroup V) :
    Nat.card ↥A * Nat.card ↥B ≤ Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) := by
  let φ : ↥A × ↥B →* V :=
    (A.subtype.comp (MonoidHom.fst ↥A ↥B)) * (B.subtype.comp (MonoidHom.snd ↥A ↥B))
  have hrange : φ.range = A ⊔ B := by
    ext x
    rw [MonoidHom.mem_range, Subgroup.mem_sup']
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨a, b, rfl⟩
    · rintro ⟨a, b, rfl⟩
      exact ⟨(a, b), rfl⟩
  have hker : Nat.card ↥φ.ker ≤ Nat.card ↥(A ⊓ B) := by
    refine Nat.card_le_card_of_injective
      (fun z : ↥φ.ker => (⟨((z.1.1 : ↥A) : V), ?_, ?_⟩ : ↥(A ⊓ B))) ?_
    · exact z.1.1.2
    · have h : (z.1.1 : V) * (z.1.2 : V) = 1 := z.2
      have : (z.1.1 : V) = ((z.1.2 : V))⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact B.inv_mem z.1.2.2
    · intro z z' h
      have h1 : (z.1.1 : V) = (z'.1.1 : V) := congrArg (fun w : ↥(A ⊓ B) => (w : V)) h
      have h2 : (z.1.2 : V) = (z'.1.2 : V) := by
        have e1 : (z.1.1 : V) * (z.1.2 : V) = 1 := z.2
        have e2 : (z'.1.1 : V) * (z'.1.2 : V) = 1 := z'.2
        have : (z.1.1 : V) * (z.1.2 : V) = (z'.1.1 : V) * (z'.1.2 : V) := by rw [e1, e2]
        rw [h1] at this
        exact mul_left_cancel this
      exact Subtype.ext (Prod.ext (Subtype.ext h1) (Subtype.ext h2))
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hrange, Nat.card_prod] at h
  calc Nat.card ↥A * Nat.card ↥B = Nat.card ↥φ.ker * Nat.card ↥(A ⊔ B) := h.symm
    _ ≤ Nat.card ↥(A ⊓ B) * Nat.card ↥(A ⊔ B) := Nat.mul_le_mul_right _ hker
    _ = Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) := mul_comm _ _

end Card

section Klein

variable {V : Type} [CommGroup V] {G T Y : Subgroup (MulAut V)}

theorem altStabilizer_anti {m : ℕ} {F F' : Finset (Fin m)} (h : F' ⊆ F) :
    altStabilizer m F ≤ altStabilizer m F' := by
  intro a ha
  rw [mem_altStabilizer_iff] at ha ⊢
  exact fun i hi => ha i (h hi)

theorem exists_klein_in_Y [Finite V] (hY2 : YSL Y 2) (e : LayerQ G Y ≃* alternatingGroup (Fin 7))
    (hH : (Y.subgroupOf (CGT6.conjClosure Y G)).map (piHom e) = altStabilizer 7 {5, 6}) :
    ∃ A : Subgroup (MulAut V), ∃ hAY : A ≤ Y, Nat.card ↥A = 4 ∧
      (∀ a (ha : a ∈ A), piHom e ⟨a, CGT6.le_conjClosure (hAY ha)⟩ ∈ kleinA7) ∧
      (∀ k ∈ kleinA7, ∃ a, ∃ ha : a ∈ A, piHom e ⟨a, CGT6.le_conjClosure (hAY ha)⟩ = k) := by
  have hle : kleinA7 ≤ (Y.subgroupOf (CGT6.conjClosure Y G)).map (piHom e) := by
    rw [hH]
    exact kleinA7_le.trans (altStabilizer_anti (by decide))
  let φ := piYEquiv hY2 e
  let K₁ : Subgroup ↥((Y.subgroupOf (CGT6.conjClosure Y G)).map (piHom e)) :=
    kleinA7.subgroupOf _
  let AY : Subgroup ↥Y := K₁.map φ.toMonoidHom
  refine ⟨AY.map Y.subtype, Subgroup.map_subtype_le AY, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective Y.subtype_injective,
      Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_kleinA7]
  · rintro a ⟨y, ⟨h, hh, rfl⟩, rfl⟩
    have := piYEquiv_symm_coe hY2 e (φ h)
    rw [MulEquiv.symm_apply_apply] at this
    show piHom e ⟨((φ h : ↥Y) : MulAut V), _⟩ ∈ kleinA7
    rw [← this]
    exact hh
  · intro k hk
    refine ⟨((φ ⟨k, hle hk⟩ : ↥Y) : MulAut V), ⟨φ ⟨k, hle hk⟩, ⟨⟨k, hle hk⟩, hk, rfl⟩, rfl⟩, ?_⟩
    have := piYEquiv_symm_coe hY2 e (φ ⟨k, hle hk⟩)
    rw [MulEquiv.symm_apply_apply] at this
    exact this.symm

end Klein

section Gen

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem eq_conjClosure_of_map_eq_top (cfg : EndCfg4 G T Y) {m : ℕ}
    (e : LayerQ G Y ≃* alternatingGroup (Fin m)) {S : Subgroup (MulAut V)}
    (hSL : S ≤ CGT6.conjClosure Y G)
    (hmap : (S.subgroupOf (CGT6.conjClosure Y G)).map (piHom e) = ⊤) :
    S = CGT6.conjClosure Y G := by
  have : Group.IsPerfect ↥(CGT6.conjClosure Y G) := ⟨cfg.quasi.1⟩
  have h := eq_top_of_map_eq_top_central (piHom e) (ker_piHom e ▸ le_rfl) hmap
  refine le_antisymm hSL fun l hl => ?_
  have : (⟨l, hl⟩ : ↥(CGT6.conjClosure Y G)) ∈ S.subgroupOf (CGT6.conjClosure Y G) := by
    rw [h]
    exact Subgroup.mem_top _
  exact this

theorem exists_gen_A (cfg : EndCfg4 G T Y) (e : LayerQ G Y ≃* alternatingGroup (Fin 7))
    {A : Subgroup (MulAut V)} (hAY : A ≤ Y)
    (hA2 : ∀ k ∈ kleinA7, ∃ a, ∃ ha : a ∈ A,
      piHom e ⟨a, CGT6.le_conjClosure (hAY ha)⟩ = k) :
    ∃ g ∈ CGT6.conjClosure Y G,
      A ⊔ A.map (MulAut.conj g).toMonoidHom = CGT6.conjClosure Y G := by
  obtain ⟨g₀, hg₀⟩ := exists_gen_kleinA7
  obtain ⟨gL, hgL⟩ := piHom_surjective e g₀
  have hYL : Y ≤ CGT6.conjClosure Y G := CGT6.le_conjClosure
  have hAL : A ≤ CGT6.conjClosure Y G := hAY.trans hYL
  have hAgL : A.map (MulAut.conj (gL : MulAut V)).toMonoidHom ≤ CGT6.conjClosure Y G := by
    rintro _ ⟨a, ha, rfl⟩
    exact mul_mem (mul_mem gL.2 (hAL ha)) (inv_mem gL.2)
  refine ⟨gL, gL.2, eq_conjClosure_of_map_eq_top cfg e (sup_le hAL hAgL) ?_⟩
  rw [eq_top_iff, ← hg₀, Subgroup.closure_le]
  rintro k (hk | hk)
  · obtain ⟨a, ha, hak⟩ := hA2 k hk
    exact ⟨⟨a, hAL ha⟩, Subgroup.mem_sup_left ha, hak⟩
  · obtain ⟨k₀, hk₀, rfl⟩ := hk
    obtain ⟨a, ha, hak⟩ := hA2 k₀ hk₀
    refine ⟨⟨(gL : MulAut V) * a * (gL : MulAut V)⁻¹, ?_⟩, ?_, ?_⟩
    · exact mul_mem (mul_mem gL.2 (hAL ha)) (inv_mem gL.2)
    · exact Subgroup.mem_sup_right ⟨a, ha, by simp [MulAut.conj_apply]⟩
    · show piHom e (gL * ⟨a, hAL ha⟩ * gL⁻¹) = (MulAut.conj g₀) k₀
      rw [map_mul, map_mul, map_inv, hgL, hak]
      rfl

theorem exists_gen_cycle (cfg : EndCfg4 G T Y) (e : LayerQ G Y ≃* alternatingGroup (Fin 7))
    (hH : (Y.subgroupOf (CGT6.conjClosure Y G)).map (piHom e) = altStabilizer 7 {5, 6})
    {x : MulAut V} (hx : x ∈ CGT6.conjClosure Y G) (hπx : piHom e ⟨x, hx⟩ = c456) :
    Y ⊔ Subgroup.zpowers x = CGT6.conjClosure Y G := by
  have hYL : Y ≤ CGT6.conjClosure Y G := CGT6.le_conjClosure
  have hzL : Subgroup.zpowers x ≤ CGT6.conjClosure Y G := Subgroup.zpowers_le.mpr hx
  refine eq_conjClosure_of_map_eq_top cfg e (sup_le hYL hzL) ?_
  rw [eq_top_iff, ← gen_alt5_cycle, Subgroup.closure_le]
  rintro k (hk | hk)
  · rw [← hH] at hk
    obtain ⟨y, hy, rfl⟩ := hk
    exact ⟨y, (Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hy))), rfl⟩
  · rw [Set.mem_singleton_iff] at hk
    subst hk
    exact ⟨⟨x, hx⟩, Subgroup.mem_sup_right (Subgroup.mem_zpowers x), hπx⟩

end Gen

theorem c456_pow_three : (c456 : alternatingGroup (Fin 7)) ^ 3 = 1 := by
  apply Subtype.ext
  show (Equiv.swap (4 : Fin 7) 5 * Equiv.swap 5 6) ^ 3 = 1
  decide

theorem kleinA7_comm_c456 : ∀ k ∈ kleinA7, k * c456 = c456 * k := by
  intro k hk
  have hk' : k ∈ (kleinA7 : Set (alternatingGroup (Fin 7))) := hk
  rw [coe_kleinA7] at hk'
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hk'
  rcases hk' with rfl | rfl | rfl | rfl
  · simp
  · exact Subtype.ext (by decide)
  · exact Subtype.ext (by decide)
  · exact Subtype.ext (by decide)

section Fix

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem commV_zpowers_le_fixV (hV : ∀ v : V, v ^ 2 = 1) (cfg : EndCfg4 G T Y) {t : MulAut V}
    (htT : t ∈ T) (ht2 : t * t = 1) : commV (Subgroup.zpowers t) ≤ fixV Y := by
  have hS1 : Subgroup.zpowers t ≤ Subgroup.centralizer (Y : Set (MulAut V)) :=
    Subgroup.zpowers_le.mpr (by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (cfg_comm_ty cfg htT hy).symm)
  have hS2 : Subgroup.zpowers t ≤ fixPtwise (commV Y) :=
    Subgroup.zpowers_le.mpr (fun u hu => t_fixes_commV hV cfg htT ht2 u hu)
  exact commV_le_fixV_of_centralizing
    (fun s hs y hy => (Subgroup.mem_centralizer_iff.mp (hS1 hs) y hy).symm)
    (fun s hs u hu => hS2 hs u hu)

end Fix

section TypeS

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem a7_typeS_false (hV : ∀ v : V, v ^ 2 = 1) (cfg : EndCfg4 G T Y) (hY2 : YSL Y 2)
    (e : LayerQ G Y ≃* alternatingGroup (Fin 7)) {t : MulAut V} (htT : t ∈ T) (ht2 : t * t = 1)
    (ht1 : t ≠ 1)
    (hH : (Y.subgroupOf (CGT6.conjClosure Y G)).map (piHom e) = altStabilizer 7 {5, 6})
    (hσ : ∀ (l : MulAut V) (hl : l ∈ CGT6.conjClosure Y G),
      ((piHom e ⟨t * l * t⁻¹, conj_mem_conjClosure (cfg.adm.hTG htT) hl⟩ :
        alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
        Equiv.swap 5 6 * ((piHom e ⟨l, hl⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) *
          (Equiv.swap 5 6)⁻¹)
    (hS : IsNatSectionBy (slAct 2) Y (commV Y) (commV Y ⊓ fixV Y)) : False := by
  have hYL : Y ≤ CGT6.conjClosure Y G := CGT6.le_conjClosure
  have hG : t ∈ G := cfg.adm.hTG htT
  have hN := normalizer_conjClosure (Y := Y) (G := G) hG
  have hperfL : Group.IsPerfect ↥(CGT6.conjClosure Y G) := ⟨cfg.quasi.1⟩
  obtain ⟨A, hAY, hA4, hA1, hA2⟩ := exists_klein_in_Y hY2 e hH
  set τ := conjOn (CGT6.conjClosure Y G) t hN with hτdef
  have hτK : ∀ k ∈ Subgroup.center ↥(CGT6.conjClosure Y G), τ k = k := by
    intro k hk
    have hcomm : t * (k : MulAut V) = (k : MulAut V) * t :=
      t_comm_center hV cfg htT ht2 (fun l hl =>
        (congrArg Subtype.val (Subgroup.mem_center_iff.mp hk ⟨l, hl⟩)).symm)
    apply Subtype.ext
    show t * (k : MulAut V) * t⁻¹ = k
    rw [hcomm]
    group
  obtain ⟨c, hc⟩ := piHom_surjective e c456
  have hτc : piHom e (τ c) = c456⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_inv]
    have := hσ c c.2
    refine this.trans ?_
    rw [hc]
    have h2 := c456_conj_swap
    rw [Equiv.swap_inv]
    exact h2
  have hcτ : c * τ c ∈ Subgroup.center ↥(CGT6.conjClosure Y G) := by
    rw [← piHom_eq_one_iff e, map_mul, hτc, hc]
    exact mul_inv_cancel _
  obtain ⟨x, hxK, hτx⟩ := exists_inverted_lift (K := Subgroup.center ↥(CGT6.conjClosure Y G))
    le_rfl cfg.oddZ τ hτK hcτ
  have hπx : piHom e x = c456 := by
    have h1 : piHom e (x * c⁻¹) = 1 := (piHom_eq_one_iff e _).mpr hxK
    rw [map_mul, map_inv, hc] at h1
    exact (mul_inv_eq_one.mp h1)
  have hxL : (x : MulAut V) ∈ CGT6.conjClosure Y G := x.2
  have hconj : t * (x : MulAut V) * t⁻¹ = (x : MulAut V)⁻¹ := congrArg Subtype.val hτx
  have hxa : ∀ a ∈ A, (x : MulAut V) * a = a * (x : MulAut V) := by
    intro a ha
    have haL : a ∈ CGT6.conjClosure Y G := hYL (hAY ha)
    have hcomm := kleinA7_comm_c456 _ (hA1 a ha)
    have hxa' : ⁅x, (⟨a, haL⟩ : ↥(CGT6.conjClosure Y G))⁆ ∈
        Subgroup.center ↥(CGT6.conjClosure Y G) := by
      rw [← piHom_eq_one_iff e, map_commutatorElement, hπx]
      exact commutatorElement_eq_one_iff_commute.mpr hcomm.symm
    have hτa : τ ⟨a, haL⟩ = ⟨a, haL⟩ := by
      apply Subtype.ext
      show t * a * t⁻¹ = a
      rw [cfg_comm_ty cfg htT (hAY ha)]
      group
    have h1 := commutator_eq_one_of_inverted (K := Subgroup.center ↥(CGT6.conjClosure Y G))
      le_rfl cfg.oddZ τ hτK hxa' hτx hτa
    have h2 := commutatorElement_eq_one_iff_commute.mp h1
    exact congrArg Subtype.val h2
  have hxodd : Odd (orderOf (x : MulAut V)) := by
    have h3 : x ^ 3 ∈ Subgroup.center ↥(CGT6.conjClosure Y G) := by
      rw [← piHom_eq_one_iff e, map_pow, hπx]
      exact c456_pow_three
    have h4 : (⟨x ^ 3, h3⟩ : ↥(Subgroup.center ↥(CGT6.conjClosure Y G))) ^
        Nat.card ↥(Subgroup.center ↥(CGT6.conjClosure Y G)) = 1 := pow_card_eq_one'
    have h5 : x ^ (3 * Nat.card ↥(Subgroup.center ↥(CGT6.conjClosure Y G))) = 1 := by
      rw [pow_mul]
      exact congrArg Subtype.val h4
    have h6 : (orderOf x) ∣ 3 * Nat.card ↥(Subgroup.center ↥(CGT6.conjClosure Y G)) :=
      orderOf_dvd_of_pow_eq_one h5
    have h7 : Odd (3 * Nat.card ↥(Subgroup.center ↥(CGT6.conjClosure Y G))) :=
      Odd.mul (by decide) cfg.oddZ
    rw [Subgroup.orderOf_coe x]
    exact Odd.of_dvd_nat h7 h6
  have hU'A : commV (Subgroup.zpowers (x : MulAut V)) ≤ fixV A := by
    intro u hu n hn
    exact commV_zpowers_fix_of_inv ht2 hconj hxodd (hxa n hn).symm
      (fun w hw => commV_zpowers_le_fixV hV cfg htT ht2 hw n (hAY hn)) u hu
  have hgenx := exists_gen_cycle cfg e hH hxL hπx
  have hVUC : commV Y ⊔ fixV A = ⊤ := by
    have h1 : commV (CGT6.conjClosure Y G) ≤
        commV Y ⊔ commV (Subgroup.zpowers (x : MulAut V)) := by
      have := CGT6.commV_sup_le Y (Subgroup.zpowers (x : MulAut V))
      rwa [hgenx] at this
    rw [commV_conjClosure_eq_top hV cfg] at h1
    rw [eq_top_iff]
    exact h1.trans (sup_le_sup_left hU'A _)
  obtain ⟨g, hgL, hgen⟩ := exists_gen_A cfg e hAY hA2
  set C : Subgroup V := fixV A with hCdef
  set C' : Subgroup V := C.map (g : MulAut V).toMonoidHom with hC'def
  have hCC' : C ⊓ C' = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hv1, w, hw, rfl⟩
    have hstab : A ⊔ A.map (MulAut.conj g).toMonoidHom ≤
        MulAction.stabilizer (MulAut V) (g w) := by
      refine sup_le ?_ ?_
      · intro a ha
        exact hv1 a ha
      · rintro _ ⟨a, ha, rfl⟩
        rw [MulAction.mem_stabilizer_iff]
        show (g * a * g⁻¹) (g w) = g w
        have h1 : a w = w := hw a ha
        simp [MulAut.mul_apply, h1]
    have hfix := fix_conjClosure_trivial hV cfg (g w) (fun y => by
      have : (y : MulAut V) ∈ A ⊔ A.map (MulAut.conj g).toMonoidHom := by
        rw [hgen]
        exact y.2
      exact MulAction.mem_stabilizer_iff.mp (hstab this))
    exact Subgroup.mem_bot.mpr hfix
  have hcard' : Nat.card ↥C' = Nat.card ↥C :=
    Subgroup.card_map_of_injective (g : MulAut V).injective
  have hcc : Nat.card ↥C * Nat.card ↥C ≤ Nat.card V := by
    have h1 := card_mul_le_card_sup_mul_card_inf C C'
    rw [hCC', Subgroup.card_bot, mul_one, hcard'] at h1
    exact h1.trans (Subgroup.card_le_card_group _)
  have hNV : Nat.card V = Nat.card ↥(commV Y ⊔ C) := by
    rw [hVUC, Subgroup.card_top]
  have h2 := card_sup_mul_card_le (A := commV Y) (B := C) (C := commV Y ⊓ C) le_rfl
  have hA4' : Nat.card ↥A = 2 ^ 2 := by rw [hA4]; norm_num
  obtain ⟨-, -, hcommA, -⟩ := emb_two_three_sylow hV Y (n := 2) le_rfl hS hAY hA4'
  have hu4 : Nat.card ↥(commV Y) ≤ Nat.card ↥(commV Y ⊓ C) * 4 := by
    have := card_commV_le_sylow hV (n := 2) le_rfl hS hAY hA4'
    rw [hcommA] at this
    simpa using this
  have hu16 : 16 ≤ Nat.card ↥(commV Y) := by
    rw [card_commV_of_natSection (f := 2) (by norm_num) hS]
    have : 1 ≤ Nat.card ↥(commV Y ⊓ fixV Y) := Nat.card_pos
    calc 16 = 1 * 2 ^ (2 * 2) := by norm_num
      _ ≤ Nat.card ↥(commV Y ⊓ fixV Y) * 2 ^ (2 * 2) := Nat.mul_le_mul_right _ this
  have hcpos : 0 < Nat.card ↥C := Nat.card_pos
  have hdpos : 0 < Nat.card ↥(commV Y ⊓ C) := Nat.card_pos
  have hdc : Nat.card ↥(commV Y ⊓ C) ≤ Nat.card ↥C := Subgroup.card_le_of_le inf_le_right
  have hcd : Nat.card ↥C * Nat.card ↥(commV Y ⊓ C) ≤ Nat.card ↥(commV Y) := by
    refine Nat.le_of_mul_le_mul_left ?_ hcpos
    calc Nat.card ↥C * (Nat.card ↥C * Nat.card ↥(commV Y ⊓ C))
        = (Nat.card ↥C * Nat.card ↥C) * Nat.card ↥(commV Y ⊓ C) := by ring
      _ ≤ Nat.card V * Nat.card ↥(commV Y ⊓ C) := Nat.mul_le_mul_right _ hcc
      _ = Nat.card ↥(commV Y ⊔ C) * Nat.card ↥(commV Y ⊓ C) := by rw [hNV]
      _ ≤ Nat.card ↥(commV Y) * Nat.card ↥C := h2
      _ = Nat.card ↥C * Nat.card ↥(commV Y) := mul_comm _ _
  have hc4 : Nat.card ↥C ≤ 4 := by
    refine Nat.le_of_mul_le_mul_right (c := Nat.card ↥(commV Y ⊓ C)) ?_ hdpos
    calc Nat.card ↥C * Nat.card ↥(commV Y ⊓ C) ≤ Nat.card ↥(commV Y) := hcd
      _ ≤ Nat.card ↥(commV Y ⊓ C) * 4 := hu4
      _ = 4 * Nat.card ↥(commV Y ⊓ C) := mul_comm _ _
  have hd4 : 4 ≤ Nat.card ↥(commV Y ⊓ C) := by omega
  have hUC : commV Y ⊓ C = C :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
  have hCU : C ≤ commV Y := by
    rw [← hUC]
    exact inf_le_left
  have hUtop : commV Y = ⊤ := by
    rw [← hVUC]
    exact (sup_eq_left.mpr hCU).symm
  apply ht1
  ext v
  have hv : v ∈ commV Y := by rw [hUtop]; exact Subgroup.mem_top v
  exact t_fixes_commV hV cfg htT ht2 v hv

end TypeS

end CFSG.CGT.PushingUpLit.CGT6X.End4
