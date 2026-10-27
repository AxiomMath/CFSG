module

public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
public import CFSG.Timmesfeld.LieEmbed.CaseMInputs
public import CFSG.LieType.Chevalley.CLSTwistedE6FieldTwoCover

public section

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup
open scoped commutatorElement MatrixGroups

section Central

variable {G : Type*} [Group G]

theorem commutator_self_le (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  commutator_le.2 fun _ ha _ hb => mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem commute_of_mem_commutator {a : G} {Y : Subgroup G}
    (h : ∀ y ∈ Y, ⁅a, y⁆ ∈ center G) {y : G} (hy : y ∈ ⁅Y, Y⁆) : Commute a y := by
  let f : Y →* G :=
    { toFun := fun y => ⁅a, (y : G)⁆
      map_one' := by simp
      map_mul' := fun y₁ y₂ => by
        have hz := mem_center_iff.1 (h y₂ y₂.2) (y₁ : G)⁻¹
        change ⁅a, (y₁ : G) * y₂⁆ = ⁅a, (y₁ : G)⁆ * ⁅a, (y₂ : G)⁆
        calc ⁅a, (y₁ : G) * y₂⁆ = a * y₁ * a⁻¹ * (⁅a, (y₂ : G)⁆ * (y₁ : G)⁻¹) := by
              rw [commutatorElement_def, commutatorElement_def]; group
          _ = ⁅a, (y₁ : G)⁆ * ⁅a, (y₂ : G)⁆ := by
              rw [← hz, commutatorElement_def a (y₁ : G)]; group }
  have hle : ⁅Y, Y⁆ ≤ centralizer {a} := by
    rw [commutator_le]
    intro y₁ h₁ y₂ h₂
    rw [mem_centralizer_singleton_iff]
    have e : f ⁅(⟨y₁, h₁⟩ : Y), ⟨y₂, h₂⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact mem_center_iff.1 (h y₂ h₂) (f (⟨y₁, h₁⟩ : Y))
    have e' : ⁅a, ⁅y₁, y₂⁆⁆ = 1 := e
    exact (commutatorElement_eq_one_iff_commute.1 e').eq.symm
  exact (mem_centralizer_singleton_iff.1 (hle hy)).symm

theorem mem_center_of_map_mem_center [Group.IsPerfect G] {H : Type*} [Group H] (η : G →* H)
    (hC : η.ker ≤ center G) {x : G} (hx : η x ∈ center H) : x ∈ center G := by
  rw [mem_center_iff]
  intro y
  have hy : y ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := by
    rw [← commutator_def, Group.IsPerfect.commutator_eq_top]
    exact mem_top y
  refine (commute_of_mem_commutator (Y := ⊤) (fun y _ => hC ?_) hy).eq.symm
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
  exact (mem_center_iff.1 hx (η y)).symm

theorem commutator_sup_le_of_le_center
    {A Z : Subgroup G} (hZ : Z ≤ center G) :
    ⁅A ⊔ Z, A ⊔ Z⁆ ≤ ⁅A, A⁆ := by
  have := normal_of_le_center hZ
  rw [commutator_le]
  intro a ha b hb
  rw [← SetLike.mem_coe, mul_normal] at ha hb
  obtain ⟨f, hf, z, hz, rfl⟩ := ha
  obtain ⟨f', hf', z', hz', rfl⟩ := hb
  rw [CFSG.LieType.Steinberg.Isogeny.commutatorElement_mul_mul_of_mem_center f f' (hZ hz)
    (hZ hz')]
  exact commutator_mem_commutator hf hf'

theorem map_inf_comap_of_le {H : Type*} [Group H] (ι : G →* H) {A : Subgroup G}
    {X : Subgroup H} (hX : X ≤ A.map ι) : (A ⊓ X.comap ι).map ι = X := by
  refine le_antisymm ((map_mono inf_le_right).trans (map_comap_le ι X)) fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := hX hx
  exact ⟨a, ⟨ha, hx⟩, rfl⟩

theorem le_commutator_of_injOn {H : Type*} [Group H] (ι : G →* H) {A : Subgroup G}
    (hinj : ∀ x ∈ A, ι x = 1 → x = 1) (hA : ⁅A.map ι, A.map ι⁆ = A.map ι) : A ≤ ⁅A, A⁆ := by
  intro a ha
  rw [← map_commutator] at hA
  obtain ⟨b, hb, hab⟩ : ι a ∈ (⁅A, A⁆).map ι := hA ▸ Subgroup.mem_map_of_mem ι ha
  have h1 : ι (b * a⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
  have h2 := hinj _ (mul_mem (commutator_self_le A hb) (inv_mem ha)) h1
  rwa [← mul_inv_eq_one.1 h2]

theorem injOn_sup_of_commute {H : Type*} [Group H] (ι : G →* H) {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b) (hA : ∀ x ∈ A, ι x = 1 → x = 1)
    (hB : ∀ x ∈ B, ι x = 1 → x = 1) (hinter : A.map ι ⊓ B.map ι = ⊥) :
    ∀ x ∈ A ⊔ B, ι x = 1 → x = 1 := by
  have hc : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b => hAB a a.2 b b.2
  intro x hx hx1
  rw [← A.range_subtype, ← B.range_subtype, ← MonoidHom.noncommCoprod_range _ _ hc] at hx
  obtain ⟨⟨a, b⟩, rfl⟩ := hx
  rw [MonoidHom.noncommCoprod_apply] at hx1 ⊢
  change ι ((a : G) * b) = 1 at hx1
  have hab : ι a = (ι b)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← map_mul]; exact hx1)
  have hb1 : ι b = 1 := by
    have hbA : ι b ∈ A.map ι := by
      rw [← inv_inv (ι b), ← hab]
      exact inv_mem (Subgroup.mem_map_of_mem ι a.2)
    have hmem : ι b ∈ A.map ι ⊓ B.map ι :=
      Subgroup.mem_inf.2 ⟨hbA, Subgroup.mem_map_of_mem ι b.2⟩
    rw [hinter] at hmem
    exact hmem
  have ha1 : ι a = 1 := by rw [hab, hb1, inv_one]
  change (a : G) * b = 1
  rw [hA a a.2 ha1, hB b b.2 hb1, one_mul]

end Central

section OddPart

variable {G : Type*} [Group G]

@[expose] def oddPart (N : Subgroup G) (hN : N ≤ center G) : Subgroup G where
  carrier := {x | x ∈ N ∧ Odd (orderOf x)}
  one_mem' := ⟨one_mem N, by rw [orderOf_one]; exact odd_one⟩
  mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1,
    (hx.2.mul hy.2).of_dvd_nat (Commute.orderOf_mul_dvd_mul_orderOf
      (mem_center_iff.1 (hN hy.1) x))⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [orderOf_inv]; exact hx.2⟩

variable {N : Subgroup G} {hN : N ≤ center G}

theorem mem_oddPart {x : G} : x ∈ oddPart N hN ↔ x ∈ N ∧ Odd (orderOf x) :=
  Iff.rfl

theorem oddPart_le : oddPart N hN ≤ N :=
  fun _ hx => hx.1

instance oddPart_normal : (oddPart N hN).Normal :=
  normal_of_le_center (oddPart_le.trans hN)

theorem eq_one_of_odd_orderOf {x : G} (hx : Odd (orderOf x)) {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    x = 1 :=
  orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hx)) (orderOf_dvd_of_pow_eq_one hk))

theorem lift_oddPart [Finite G] {S : Type*} [Group S] (φ : G →* S) (hφ : Function.Surjective φ)
    (hZ : φ.ker ≤ center G) :
    Function.Surjective (QuotientGroup.lift (oddPart φ.ker hZ) φ oddPart_le) ∧
      (QuotientGroup.lift (oddPart φ.ker hZ) φ oddPart_le).ker ≤
        center (G ⧸ oddPart φ.ker hZ) ∧
      IsPGroup 2 (QuotientGroup.lift (oddPart φ.ker hZ) φ oddPart_le).ker := by
  have hmk : ∀ x : G, QuotientGroup.lift (oddPart φ.ker hZ) φ oddPart_le (x : G ⧸ _) = φ x :=
    fun x => QuotientGroup.lift_mk _ _ _
  refine ⟨fun s => ?_, fun z hz => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := hφ s
    exact ⟨x, hmk x⟩
  · induction z using QuotientGroup.induction_on with
    | H x =>
      rw [MonoidHom.mem_ker, hmk] at hz
      refine mem_center_iff.2 fun g => ?_
      induction g using QuotientGroup.induction_on with
      | H g => rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.1 (hZ hz) g]
  · rintro ⟨z, hz⟩
    induction z using QuotientGroup.induction_on with
    | H x =>
      rw [MonoidHom.mem_ker, hmk] at hz
      obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
      refine ⟨k, Subtype.ext ?_⟩
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      refine ⟨pow_mem hz _, ?_⟩
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hkm⟩, hkm,
        Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
      exact hm

end OddPart

section Split

open CFSG.LieType.Chevalley.C2E6Std.TwistedE6LeviCover

theorem commutator_comap_inf_ker_eq_bot
    {E U S : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    [Group U] [Group S] (η : E →* U) (hη : Function.Surjective η) (hC : η.ker ≤ center E)
    (h2 : IsPGroup 2 η.ker) (β : U →* S) (hβ : Function.Surjective β) (hβZ : β.ker ≤ center U)
    {L : Subgroup U} {L' : Subgroup S} (e : L' ≃* minusGroup) (hLL' : L.map β ≤ L') :
    ⁅L.comap η, L.comap η⁆ ⊓ η.ker = ⊥ := by
  have hNZ : (β.comp η).ker ≤ center E := fun x hx => mem_center_of_map_mem_center η hC (hβZ hx)
  obtain ⟨hsurj, hβ'C, hβ'2⟩ := lift_oddPart (β.comp η) (hβ.comp hη) hNZ
  have hβ'mk : ∀ x : E, QuotientGroup.lift (oddPart (β.comp η).ker hNZ) (β.comp η) oddPart_le
      (x : E ⧸ oddPart (β.comp η).ker hNZ) = β (η x) := fun x => QuotientGroup.lift_mk _ _ _
  obtain ⟨F, -, hFinj, -, hFcomap⟩ := exists_split_of_mulEquiv L' e _ hsurj hβ'C hβ'2
  have hPle : (L.comap η).map (QuotientGroup.mk' (oddPart (β.comp η).ker hNZ)) ≤
      F ⊔ (QuotientGroup.lift (oddPart (β.comp η).ker hNZ) (β.comp η) oddPart_le).ker := by
    rw [← hFcomap]
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_comap, QuotientGroup.mk'_apply, hβ'mk]
    exact hLL' ⟨η x, hx, rfl⟩
  have hle : (⁅L.comap η, L.comap η⁆).map (QuotientGroup.mk' (oddPart (β.comp η).ker hNZ)) ≤
      F := by
    rw [map_commutator]
    exact ((commutator_mono hPle hPle).trans (commutator_sup_le_of_le_center hβ'C)).trans
      (commutator_self_le F)
  rw [eq_bot_iff]
  rintro c ⟨hcP, hcC⟩
  have hcF : (c : E ⧸ oddPart (β.comp η).ker hNZ) ∈ F := hle ⟨c, hcP, rfl⟩
  have h1 : (c : E ⧸ oddPart (β.comp η).ker hNZ) = 1 :=
    hFinj _ hcF (by rw [hβ'mk, show η c = 1 from hcC, map_one])
  rw [QuotientGroup.eq_one_iff, mem_oddPart] at h1
  obtain ⟨k, hk⟩ := h2 ⟨c, hcC⟩
  exact mem_bot.2 (eq_one_of_odd_orderOf h1.2 (by simpa using congrArg Subtype.val hk))

end Split

section Lift

open CFSG.LieType.CurtisTits

theorem ker_eq_bot_of_lifts
    {U : Type} [Group U] {I : Type} [Preorder I] {K : I → Subgroup U}
    (hgen : ⨆ i, K i = ⊤) (hU : IsUniversalCompletion.{0, 0, 0} K)
    {G : Type} [Group G] [Group.IsPerfect G] (ι : G →* U) (hC : ι.ker ≤ center G)
    (H : I → Subgroup G) (hmono : Monotone H) (hinj : ∀ i, ∀ x ∈ H i, ι x = 1 → x = 1)
    (hmap : ∀ i, (H i).map ι = K i) : ι.ker = ⊥ := by
  have key : ∀ i, ∃ φ : K i →* G, ∀ x, φ x ∈ H i ∧ ι (φ x) = x := by
    intro i
    have hmem : ∀ h : H i, ι h ∈ K i := fun h => hmap i ▸ Subgroup.mem_map_of_mem ι h.2
    set r : H i →* K i := (ι.comp (H i).subtype).codRestrict (K i) hmem with hr
    have hrb : Function.Bijective r := by
      refine ⟨fun a b hab => ?_, fun x => ?_⟩
      · have hab' : ι a = ι b := congrArg Subtype.val hab
        have h1 : ι ((a : G) * (b : G)⁻¹) = 1 := by rw [map_mul, map_inv, hab', mul_inv_cancel]
        exact Subtype.ext (mul_inv_eq_one.1 (hinj i _ (mul_mem a.2 (inv_mem b.2)) h1))
      · obtain ⟨h, hh, hx⟩ : (x : U) ∈ (H i).map ι := (hmap i).symm ▸ x.2
        exact ⟨⟨h, hh⟩, Subtype.ext hx⟩
    set e := MulEquiv.ofBijective r hrb
    refine ⟨(H i).subtype.comp e.symm.toMonoidHom, fun x => ⟨(e.symm x).2, ?_⟩⟩
    exact congrArg Subtype.val (e.apply_symm_apply x)
  choose φ hφ using key
  have hcomp : IsCompatible K φ := by
    intro i j hij x y hxy
    have e : ι (φ i x * (φ j y)⁻¹) = 1 := by
      rw [map_mul, map_inv, (hφ i x).2, (hφ j y).2, hxy, mul_inv_cancel]
    exact mul_inv_eq_one.1 (hinj j _ (mul_mem (hmono hij (hφ i x).1) (inv_mem (hφ j y).1)) e)
  obtain ⟨ψ, hψ, -⟩ := hU G φ hcomp
  have hιψ : ∀ u, ι (ψ u) = u := by
    have h : ι.comp ψ = MonoidHom.id U :=
      hom_ext_of_iSup_eq_top hgen fun i x => by
        rw [MonoidHom.comp_apply, hψ, (hφ i x).2, MonoidHom.id_apply]
    exact fun u => DFunLike.congr_fun h u
  have htop : ψ.range ⊔ ι.ker = ⊤ := by
    refine eq_top_iff.2 fun g _ => ?_
    have hk : (ψ (ι g))⁻¹ * g ∈ ι.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hιψ, inv_mul_cancel]
    rw [show g = ψ (ι g) * ((ψ (ι g))⁻¹ * g) by group]
    exact mul_mem_sup ⟨ι g, rfl⟩ hk
  have hrange : ψ.range = ⊤ := by
    refine eq_top_iff.2 ?_
    calc (⊤ : Subgroup G) = ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := by
          rw [← commutator_def, Group.IsPerfect.commutator_eq_top]
      _ = ⁅ψ.range ⊔ ι.ker, ψ.range ⊔ ι.ker⁆ := by rw [htop]
      _ ≤ ⁅ψ.range, ψ.range⁆ := commutator_sup_le_of_le_center hC
      _ ≤ ψ.range := commutator_self_le _
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨u, rfl⟩ : g ∈ ψ.range := hrange ▸ mem_top g
  have hu : u = 1 := by rw [← hιψ u]; exact hg
  rw [hu, map_one]
  exact one_mem _

end Lift

open CFSG.LieType.Steinberg.Exceptional CFSG.LieType.CurtisTits CFSG.Blueprint.Chevalley

local instance :
    NeZero (twistedE6Datum 2 1).rank :=
  ⟨by show (4 : ℕ) ≠ 0; decide⟩

theorem cartan_twistedE6Datum
    : (twistedE6Datum 2 1).cartan =
    !![2, -1, 0, 0; -1, 2, -1, 0; 0, -2, 2, -1; 0, 0, -1, 2] := by
  show (Tag.cartan .F4 : Matrix (Fin 4) (Fin 4) ℤ) = _
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] noncomputable def levi34
    : Finset (Fin (twistedE6Datum 2 1).rank) := {2, 3}

@[expose] noncomputable def levi123
    : Finset (Fin (twistedE6Datum 2 1).rank) := {0, 1, 2}

section Datum

open CFSG.Timmesfeld

theorem exists_rankOne_short
    (j : Fin (twistedE6Datum 2 1).rank) (hj : j = 2 ∨ j = 3) :
    ∃ m : SL(2, GaloisField 2 (2 * 1)) →* twistedE6Group 2 1, Function.Injective m ∧
      m.range = rankOne (twistedE6Datum 2 1).rootGroup j := by
  obtain ⟨l, -, -, -, -, -, -, -, hm⟩ := CFSG.Timmesfeld.LieEmbed.twistedE6EdgeLeviInput 1 le_rfl
  obtain ⟨m, hinj, hp, hn, -⟩ := hm j hj
  refine ⟨m.comp (MonoidHom.inr _ _), hinj.comp fun a b h => (Prod.ext_iff.1 h).2, ?_⟩
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, ← closure_tv_two, MonoidHom.map_closure, closure_le]
    rintro _ ⟨g, ⟨c, rfl⟩ | ⟨c, rfl⟩, rfl⟩
    · have hx : m (1, tv 0 1 c) ∈ ((twistedE6Datum 2 1).rootGroup (Pi.single j 1) : Set _) :=
        hp ▸ ⟨c, rfl⟩
      exact mem_sup_left hx
    · have hx : m (1, tv 1 0 c) ∈ ((twistedE6Datum 2 1).rootGroup (-Pi.single j 1) : Set _) :=
        hn ▸ ⟨c, rfl⟩
      exact mem_sup_right hx
  · refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨c, rfl⟩ : x ∈ Set.range fun c => m (1, tv 0 1 c) := hp ▸ hx
      exact ⟨tv 0 1 c, rfl⟩
    · obtain ⟨c, rfl⟩ : x ∈ Set.range fun c => m (1, tv 1 0 c) := hn ▸ hx
      exact ⟨tv 1 0 c, rfl⟩

theorem isPerfect_sl_two_four
    : Group.IsPerfect SL(2, GaloisField 2 (2 * 1)) :=
  CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _
    (CFSG.LieType.Steinberg.Isogeny.four_le_card_galoisField 2 1 le_rfl)

theorem commutator_range_eq_range {G H : Type*} [Group G] [Group H] [Group.IsPerfect G]
    (f : G →* H) : ⁅f.range, f.range⁆ = f.range := by
  rw [MonoidHom.range_eq_map, ← map_commutator, ← commutator_def,
    Group.IsPerfect.commutator_eq_top]

theorem commutator_rankOne_short
    (j : Fin (twistedE6Datum 2 1).rank) (hj : j = 2 ∨ j = 3) :
    ⁅rankOne (twistedE6Datum 2 1).rootGroup j, rankOne (twistedE6Datum 2 1).rootGroup j⁆ =
      rankOne (twistedE6Datum 2 1).rootGroup j := by
  obtain ⟨m, -, hm⟩ := exists_rankOne_short j hj
  have := isPerfect_sl_two_four
  rw [← hm, commutator_range_eq_range]

theorem eq_one_of_mem_rankOne_short
    {j : Fin (twistedE6Datum 2 1).rank} (hj : j = 2 ∨ j = 3)
    {x : twistedE6Group 2 1}
    (hx : x ∈ rankOne (twistedE6Datum 2 1).rootGroup j)
    (hc : ∀ y ∈ rankOne (twistedE6Datum 2 1).rootGroup j, x * y = y * x) : x = 1 := by
  obtain ⟨m, hinj, hm⟩ := exists_rankOne_short j hj
  obtain ⟨g, rfl⟩ : x ∈ m.range := hm ▸ hx
  have hg : g ∈ center SL(2, GaloisField 2 (2 * 1)) := mem_center_iff.2 fun h => hinj (by
    rw [map_mul, map_mul]
    exact (hc (m h) (hm ▸ ⟨h, rfl⟩)).symm)
  rw [CFSG.Timmesfeld.LevisExtras.eq_one_of_mem_center_sl2 hg, map_one]

theorem commutatorElement_mem {G : Type*} [Group G] (H : Subgroup G) {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) : ⁅a, b⁆ ∈ H :=
  commutator_self_le H (commutator_mem_commutator ha hb)

theorem single_zero_eq : (Pi.single 0 1 : Fin 4 → ℤ) = ![1, 0, 0, 0] := by decide

theorem single_one_eq : (Pi.single 1 1 : Fin 4 → ℤ) = ![0, 1, 0, 0] := by decide

theorem levi_zero_one_le_commutator :
    (twistedE6Datum 2 1).levi {0, 1} ≤
      ⁅(twistedE6Datum 2 1).levi levi123, (twistedE6Datum 2 1).levi levi123⁆ := by
  obtain ⟨l, -, h0, h0', h1, h1', -, -, -⟩ :=
    CFSG.Timmesfeld.LieEmbed.twistedE6EdgeLeviInput 1 le_rfl
  set L := (twistedE6Datum 2 1).levi levi123
  have hr0 : rankOne (twistedE6Datum 2 1).rootGroup 0 ≤ L :=
    rankOne_le_levi _ (by simp [levi123])
  have hr1 : rankOne (twistedE6Datum 2 1).rootGroup 1 ≤ L :=
    rankOne_le_levi _ (by simp [levi123])
  have e01 : ∀ c, l (tv 0 1 c) ∈ L := fun c => hr0 (mem_sup_left (by
    have : l (tv 0 1 c) ∈ ((twistedE6Datum 2 1).rootGroup ![1, 0, 0, 0] : Set _) := h0 ▸ ⟨c, rfl⟩
    rwa [← single_zero_eq] at this))
  have e10 : ∀ c, l (tv 1 0 c) ∈ L := fun c => hr0 (mem_sup_right (by
    have : l (tv 1 0 c) ∈ ((twistedE6Datum 2 1).rootGroup (-![1, 0, 0, 0]) : Set _) :=
      h0' ▸ ⟨c, rfl⟩
    rwa [← single_zero_eq] at this))
  have e12 : ∀ c, l (tv 1 2 c) ∈ L := fun c => hr1 (mem_sup_left (by
    have : l (tv 1 2 c) ∈ ((twistedE6Datum 2 1).rootGroup ![0, 1, 0, 0] : Set _) := h1 ▸ ⟨c, rfl⟩
    rwa [← single_one_eq] at this))
  have e21 : ∀ c, l (tv 2 1 c) ∈ L := fun c => hr1 (mem_sup_right (by
    have : l (tv 2 1 c) ∈ ((twistedE6Datum 2 1).rootGroup (-![0, 1, 0, 0]) : Set _) :=
      h1' ▸ ⟨c, rfl⟩
    rwa [← single_one_eq] at this))
  have hrange : l.range ≤ L := by
    rw [MonoidHom.range_eq_map, ← CFSG.LinearGroups.special_linear_elementary_generation,
      MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨i, j, hij, c, rfl⟩, rfl⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · rw [SetLike.mem_coe, ← tv_of_ne hij]; exact e01 c
    · have e := Matrix.SpecialLinearGroup.commutatorElement_transvection
        (by decide : (0 : Fin 3) ≠ 1) (by decide : (1 : Fin 3) ≠ 2) hij c 1
      rw [mul_one] at e
      rw [SetLike.mem_coe, ← e, map_commutatorElement, ← tv_of_ne, ← tv_of_ne]
      exact commutatorElement_mem L (e01 c) (e12 1)
    · rw [SetLike.mem_coe, ← tv_of_ne hij]; exact e10 c
    · exact absurd rfl hij
    · rw [SetLike.mem_coe, ← tv_of_ne hij]; exact e12 c
    · have e := Matrix.SpecialLinearGroup.commutatorElement_transvection
        (by decide : (2 : Fin 3) ≠ 1) (by decide : (1 : Fin 3) ≠ 0) hij c 1
      rw [mul_one] at e
      rw [SetLike.mem_coe, ← e, map_commutatorElement, ← tv_of_ne, ← tv_of_ne]
      exact commutatorElement_mem L (e21 c) (e10 1)
    · rw [SetLike.mem_coe, ← tv_of_ne hij]; exact e21 c
    · exact absurd rfl hij
  have hle : (twistedE6Datum 2 1).levi {0, 1} ≤ l.range := by
    have hX : ∀ γ, ∀ x ∈ (twistedE6Datum 2 1).rootGroup γ,
        (x ∈ Set.range fun c => l (tv 0 1 c)) ∨ (x ∈ Set.range fun c => l (tv 1 0 c)) ∨
          (x ∈ Set.range fun c => l (tv 1 2 c)) ∨ (x ∈ Set.range fun c => l (tv 2 1 c)) →
        x ∈ l.range := by
      rintro γ x - (⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩) <;> exact ⟨_, rfl⟩
    refine iSup₂_le fun j hj => ?_
    rcases (by simpa using hj : j = 0 ∨ j = 1) with rfl | rfl
    · refine sup_le (fun x hx => hX _ x hx (Or.inl ?_)) (fun x hx => hX _ x hx (Or.inr (Or.inl ?_)))
      · rw [← h0, ← single_zero_eq]; exact hx
      · rw [← h0', ← single_zero_eq]; exact hx
    · refine sup_le (fun x hx => hX _ x hx (Or.inr (Or.inr (Or.inl ?_))))
        (fun x hx => hX _ x hx (Or.inr (Or.inr (Or.inr ?_))))
      · rw [← h1, ← single_one_eq]; exact hx
      · rw [← h1', ← single_one_eq]; exact hx
  have := CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (K := GaloisField 2 1)
    (n := 3) le_rfl
  calc (twistedE6Datum 2 1).levi {0, 1} ≤ l.range := hle
    _ = ⁅l.range, l.range⁆ := (commutator_range_eq_range l).symm
    _ ≤ ⁅L, L⁆ := commutator_mono hrange hrange

theorem commutator_levi123 :
    ⁅(twistedE6Datum 2 1).levi levi123, (twistedE6Datum 2 1).levi levi123⁆ =
      (twistedE6Datum 2 1).levi levi123 := by
  refine le_antisymm (commutator_self_le _) (iSup₂_le fun j hj => ?_)
  rcases (by simpa [levi123] using hj : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · exact (rankOne_le_levi _ (by simp)).trans levi_zero_one_le_commutator
  · exact (rankOne_le_levi _ (by simp)).trans levi_zero_one_le_commutator
  · refine (le_of_eq (commutator_rankOne_short 2 (Or.inl rfl)).symm).trans ?_
    exact commutator_mono (rankOne_le_levi _ (by simp [levi123]))
      (rankOne_le_levi _ (by simp [levi123]))

theorem f4_root_support
    (r : Fin 4 → ℤ) (hr : IsRoot .F4 r) (h2 : r 2 = 0) :
    r 3 = 0 ∨ (r 0 = 0 ∧ r 1 = 0) :=
  (by decide +kernel : ∀ r ∈ rootFinset .F4, r (2 : Fin 4) = 0 →
    r (3 : Fin 4) = 0 ∨ (r (0 : Fin 4) = 0 ∧ r (1 : Fin 4) = 0)) r (mem_rootFinset.2 hr) h2

theorem commute_rankOne_three_aux
    {j : Fin 4} (hj : j = 0 ∨ j = 1) {x y : twistedE6Group 2 1}
    (hx : x ∈ rankOne (twistedE6Datum 2 1).rootGroup j)
    (hy : y ∈ rankOne (twistedE6Datum 2 1).rootGroup (3 : Fin 4)) : Commute x y := by
  have hroots : ∀ v : Fin 4 → ℤ, v ∈ (twistedE6Datum 2 1).roots ↔ IsRoot .F4 v := fun v => by
    rw [CFSG.LieType.Steinberg.TwistedE6.twistedDatum_roots]; rfl
  have key : ∀ γ δ : Fin 4 → ℤ,
      (γ = Pi.single j 1 ∨ γ = -Pi.single j 1) → (δ = Pi.single 3 1 ∨ δ = -Pi.single 3 1) →
      ∀ a ∈ (twistedE6Datum 2 1).rootGroup γ, ∀ b ∈ (twistedE6Datum 2 1).rootGroup δ,
        b * a = a * b := by
    intro γ δ hγ hδ a ha b hb
    have hγr : γ ∈ (twistedE6Datum 2 1).roots := (hroots γ).2 (by
      rcases hγ with rfl | rfl
      exacts [isRoot_single .F4 j, isRoot_neg_single .F4 j])
    have hδr : δ ∈ (twistedE6Datum 2 1).roots := (hroots δ).2 (by
      rcases hδ with rfl | rfl
      exacts [isRoot_single .F4 (3 : Fin 4), isRoot_neg_single .F4 (3 : Fin 4)])
    have hlin : CFSG.LieType.Steinberg.LinIndepPair δ γ := by
      intro p q hpq
      have h3 := congrFun hpq 3
      have hj' := congrFun hpq j
      rcases hj with rfl | rfl <;> rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl <;>
        simp at h3 hj' <;> omega
    have hcone : CFSG.LieType.Steinberg.openCone (twistedE6Datum 2 1).roots δ γ = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 ?_
      rintro _ ⟨hε, p, q, hp, hq, rfl⟩
      have h := f4_root_support (p • δ + q • γ : Fin 4 → ℤ) ((hroots _).1 hε)
      rcases hj with rfl | rfl <;> rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl <;>
        simp at h <;> omega
    have hc := CFSG.LieType.Steinberg.TwistedE6.commutator_mem_twistedDatum δ hδr γ hγr hlin
      b hb a ha
    rw [hcone] at hc
    simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, mem_bot] at hc
    exact (commutatorElement_eq_one_iff_commute.1 hc).eq
  have h1 : ∀ δ : Fin 4 → ℤ, (δ = Pi.single 3 1 ∨ δ = -Pi.single 3 1) →
      rankOne (twistedE6Datum 2 1).rootGroup j ≤
        centralizer ((twistedE6Datum 2 1).rootGroup δ : Set (twistedE6Group 2 1)) :=
    fun δ hδ => sup_le
      (fun a ha => mem_centralizer_iff.2 fun b hb => key _ δ (Or.inl rfl) hδ a ha b hb)
      (fun a ha => mem_centralizer_iff.2 fun b hb => key _ δ (Or.inr rfl) hδ a ha b hb)
  have h2 : rankOne (twistedE6Datum 2 1).rootGroup (3 : Fin 4) ≤
      centralizer (rankOne (twistedE6Datum 2 1).rootGroup j : Set (twistedE6Group 2 1)) :=
    sup_le (le_centralizer_iff.1 (h1 _ (Or.inl rfl))) (le_centralizer_iff.1 (h1 _ (Or.inr rfl)))
  exact mem_centralizer_iff.1 (h2 hy) x hx

theorem commute_rankOne_three
    {j : Fin (twistedE6Datum 2 1).rank} (hj : j = 0 ∨ j = 1)
    {x y : twistedE6Group 2 1} (hx : x ∈ rankOne (twistedE6Datum 2 1).rootGroup j)
    (hy : y ∈ rankOne (twistedE6Datum 2 1).rootGroup 3) : Commute x y := by
  rcases hj with rfl | rfl
  exacts [commute_rankOne_three_aux (j := 0) (Or.inl rfl) hx hy,
    commute_rankOne_three_aux (j := 1) (Or.inr rfl) hx hy]

theorem rankOne_inf_rankOne_three
    {j : Fin (twistedE6Datum 2 1).rank} (hj : j = 0 ∨ j = 1) :
    rankOne (twistedE6Datum 2 1).rootGroup j ⊓ rankOne (twistedE6Datum 2 1).rootGroup 3 = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxj, hx3⟩
  exact mem_bot.2 (eq_one_of_mem_rankOne_short (Or.inr rfl) hx3 fun y hy =>
    (commute_rankOne_three hj hxj hy).eq)

end Datum

section Isogeny

open CFSG.Blueprint CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Minuscule

theorem card_galoisField_eq_card_K :
    @Fintype.card (GaloisField 2 (2 * 1)) (Fintype.ofFinite _) = Fintype.card K := by
  rw [card_K, ← @Nat.card_eq_fintype_card _ (Fintype.ofFinite _),
    GaloisField.card 2 (2 * 1) (by norm_num)]
  norm_num

@[expose] noncomputable def fieldEquiv : GaloisField 2 (2 * 1) ≃+* K :=
  @FiniteField.ringEquivOfCardEq _ _ _ _ (Fintype.ofFinite _) _ card_galoisField_eq_card_K

theorem barHom_fieldEquiv
    (c : GaloisField 2 (2 * 1)) :
    barHom (fieldEquiv.toRingHom c) = fieldEquiv.toRingHom (frobQ 2 1 c) := by
  rw [barHom_apply, bar, frobQ_apply, pow_one, map_pow]

theorem frobQ_two_one_surjective : Function.Surjective (frobQ 2 1) :=
  Finite.surjective_of_injective (frobQ 2 1).injective

theorem commutator_twistedFixedGroup_two :
    ⁅twistedFixedGroup .E6 (GaloisField 2 (2 * 1)) (frobQ 2 1),
        twistedFixedGroup .E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)⁆ =
      graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1) :=
  (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two le_rfl (GaloisField 2 (2 * 1))
    (by rw [GaloisField.card 2 (2 * 1) (by norm_num)]; rfl) (frobQ 2 1) (frobQ_apply 2 1)).2.2.1

theorem e6IsogenyFixed_mem
    (g : twistedE6Group 2 1) :
    baseChangeGL fieldEquiv.toRingHom (e6IsogenyFixed (frobQ 2 1) g) ∈ stdGroup := by
  have h1 : e6IsogenyFixed (frobQ 2 1) g ∈
      graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1) := by
    rw [← commutator_twistedFixedGroup_two, ← range_e6IsogenyFixed_frobQ 2 1 le_rfl]
    exact ⟨g, rfl⟩
  exact map_baseChangeGL_graphFixedRootGroup_le frobQ_two_one_surjective barHom_fieldEquiv
    ⟨_, h1, rfl⟩

@[expose] noncomputable def isogenyStd
    : twistedE6Group 2 1 →* stdGroup :=
  ((baseChangeGL fieldEquiv.toRingHom).comp (e6IsogenyFixed (frobQ 2 1))).codRestrict stdGroup
    e6IsogenyFixed_mem

theorem isogenyStd_surjective
    : Function.Surjective isogenyStd := by
  intro s
  have hpar : ∀ a, ∀ c ∈ orbitField TwistTag.E6 K barHom a,
      ∃ c₀ ∈ orbitField TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1) a,
        fieldEquiv.toRingHom c₀ = c := by
    intro a c hc
    refine ⟨fieldEquiv.symm c, ?_, fieldEquiv.apply_symm_apply c⟩
    rw [mem_orbitField] at hc ⊢
    apply fieldEquiv.injective
    have h := ringHom_pow_apply_comm barHom_fieldEquiv (TwistTag.E6.orbit a).card
      (fieldEquiv.symm c)
    change (barHom ^ _) (fieldEquiv (fieldEquiv.symm c)) = fieldEquiv _ at h
    rw [fieldEquiv.apply_symm_apply, hc] at h
    rw [← h, fieldEquiv.apply_symm_apply]
  obtain ⟨g, hg, hgs⟩ := graphFixedRootGroup_le_map_baseChangeGL barHom_surjective
    barHom_fieldEquiv hpar s.2
  rw [← commutator_twistedFixedGroup_two, ← range_e6IsogenyFixed_frobQ 2 1 le_rfl] at hg
  obtain ⟨u, rfl⟩ := hg
  exact ⟨u, Subtype.ext hgs⟩

theorem ker_isogenyStd_le_center
    : isogenyStd.ker ≤ center (twistedE6Group 2 1) := by
  refine CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.LieType.CurtisTits.isQuasisimple_twistedE6 2 1 le_rfl) ?_
  obtain ⟨g, hg⟩ := twistedE6Isogeny_ne_one 2 1 le_rfl
  refine ⟨g, fun h => hg ?_⟩
  have h1 : baseChangeGL fieldEquiv.toRingHom (e6IsogenyFixed (frobQ 2 1) g) = 1 :=
    congrArg Subtype.val h
  rw [← map_one (baseChangeGL fieldEquiv.toRingHom)] at h1
  exact Subtype.ext (baseChangeGL_injective _ h1)

@[expose] noncomputable def adjointStd :
    ↥(e6Data_valid.minGroup (GaloisField 2 (2 * 1))) →* ModGL Tag.E6 K :=
  (baseChangeGL fieldEquiv.toRingHom).comp
    ((adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * 1))).subtype.comp (e6IsogenyT _))

theorem coe_isogenyStd_eq_adjointStd
    (g : twistedE6Group 2 1) :
    (isogenyStd g : ModGL Tag.E6 K) = adjointStd (g : e6Data_valid.minGroup _) :=
  rfl

theorem adjointStd_apply
    (g : ↥(e6Data_valid.minGroup (GaloisField 2 (2 * 1)))) :
    adjointStd g = baseChangeGL fieldEquiv.toRingHom
      ((e6Isogeny (GaloisField 2 (2 * 1)) g : ↥(adjointGroup .E6 (GaloisField 2 (2 * 1)))) :
        ModGL .E6 (GaloisField 2 (2 * 1))) :=
  rfl

theorem rootGroup_le_comap_groupD
    {a : Fin (Tag.rank .E6)} (ha : a ∈ setD)
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : γ = Pi.single a 1 ∨ γ = -Pi.single a 1) :
    e6Data_valid.rootGroup (GaloisField 2 (2 * 1)) γ ≤ groupD.comap adjointStd := by
  intro x hx
  obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup _).1 hx
  rw [mem_comap, adjointStd_apply]
  rcases hγ with rfl | rfl
  · have h1 : e6Isogeny (GaloisField 2 (2 * 1)) (e6Data_valid.xm _ (Pi.single a 1) c) =
        xElement a c :=
      (e6Isogeny_xm_single _ a c).trans (eltElement_simpleRoot_E6 a c)
    rw [h1]
    change baseChangeGL _ (xUnit _ _ a c) ∈ _
    rw [baseChangeGL_xUnit]
    exact Subgroup.subset_closure ⟨a, ha, _, Or.inl rfl⟩
  · have h1 : e6Isogeny (GaloisField 2 (2 * 1)) (e6Data_valid.xm _ (-Pi.single a 1) c) =
        yElement a c :=
      (e6Isogeny_xm_neg_single _ a c).trans (eltElement_neg_simpleRoot_E6 a c)
    rw [h1]
    change baseChangeGL _ (yUnit _ _ a c) ∈ _
    rw [baseChangeGL_yUnit]
    exact Subgroup.subset_closure ⟨a, ha, _, Or.inr rfl⟩

theorem firstNode_ne : ∀ j : Fin 4, j ≠ 3 →
    (firstNode j).val ≠ 0 ∧ (firstNode j).val ≠ 5 ∧
      (rhoPerm (firstNode j)).val ≠ 0 ∧ (rhoPerm (firstNode j)).val ≠ 5 := by
  decide

theorem mem_setD_of_ne {a : Fin 6} (h0 : a.val ≠ 0) (h5 : a.val ≠ 5) : a ∈ setD := by
  by_contra h
  rcases TwistedE6LeviCover.eq_zero_or_eq_five_of_not_mem_setD h with rfl | rfl
  exacts [h0 rfl, h5 rfl]

theorem map_levi123_isogenyStd_le :
    ((twistedE6Datum 2 1).levi levi123).map isogenyStd ≤ TwistedE6LeviCover.leviG := by
  rw [map_le_iff_le_comap]
  refine iSup₂_le fun j hj => ?_
  have hj3 : j ≠ 3 := by
    have key : ∀ j : Fin 4, j ∈ ({0, 1, 2} : Finset (Fin 4)) → j ≠ 3 := by decide
    exact key j hj
  obtain ⟨h0, h5, h0', h5'⟩ := firstNode_ne j hj3
  have ha := mem_setD_of_ne h0 h5
  have hb := mem_setD_of_ne h0' h5'
  have hmem : ∀ x : twistedE6Group 2 1, (x : e6Data_valid.minGroup _) ∈ groupD.comap adjointStd →
      x ∈ TwistedE6LeviCover.leviG.comap isogenyStd := fun x hx => by
    have hx2 : (isogenyStd x : ModGL Tag.E6 K) ∈ groupD := by
      rw [coe_isogenyStd_eq_adjointStd]
      exact hx
    show (isogenyStd x : ModGL Tag.E6 K) ∈ stdLevi FourthResidue.fourthJ
    rw [FourthResidue.stdLevi_fourthJ]
    exact mem_inf.2 ⟨hx2, graphFixedRootGroup_le TwistTag.E6 K barHom (isogenyStd x).2⟩
  refine sup_le (fun x hx => hmem x ?_) (fun x hx => hmem x ?_)
  · have hx' := (mem_twistedRootGroup_iff (frobQ 2 1) (isRoot_single .E6 (firstNode j))
      ((proj_single _).trans (congrArg (fun i => Pi.single i (1 : ℤ)) (orbitMap_firstNode j)))
      x).1 hx
    rw [rho_single] at hx'
    exact sup_le (rootGroup_le_comap_groupD ha (Or.inl rfl))
      (rootGroup_le_comap_groupD hb (Or.inl rfl)) hx'
  · have hx' := (mem_twistedRootGroup_iff (frobQ 2 1) (isRoot_neg_single .E6 (firstNode j))
      ((proj_neg_single _).trans
        (congrArg (fun i => -Pi.single i (1 : ℤ)) (orbitMap_firstNode j))) x).1 hx
    rw [rho_neg_single] at hx'
    exact sup_le (rootGroup_le_comap_groupD ha (Or.inr rfl))
      (rootGroup_le_comap_groupD hb (Or.inr rfl)) hx'

end Isogeny

theorem commutator_comap_levi123_inf_ker_eq_bot
    {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] (η : E →* twistedE6Group 2 1) (hη : Function.Surjective η)
    (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker) :
    ⁅((twistedE6Datum 2 1).levi levi123).comap η,
        ((twistedE6Datum 2 1).levi levi123).comap η⁆ ⊓ η.ker = ⊥ ∧
      (⁅((twistedE6Datum 2 1).levi levi123).comap η,
        ((twistedE6Datum 2 1).levi levi123).comap η⁆).map η =
          (twistedE6Datum 2 1).levi levi123 := by
  refine ⟨commutator_comap_inf_ker_eq_bot η hη hC h2 isogenyStd isogenyStd_surjective
    ker_isogenyStd_le_center CFSG.LieType.Chevalley.C2E6Std.TwistedE6LeviCover.leviGEquiv
    map_levi123_isogenyStd_le, ?_⟩
  rw [map_commutator, map_comap_eq_self_of_surjective hη, commutator_levi123]

open CFSG.LieType.Chevalley in
theorem sq_eq_one_of_mem_ker
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (η : E →* twistedE6Group 2 1) (hη : Function.Surjective η) (hC : η.ker ≤ center E)
    (h2 : IsPGroup 2 η.ker) {c : E} (hc : c ∈ η.ker) : c ^ 2 = 1 := by
  have hNZ : (isogenyStd.comp η).ker ≤ center E :=
    fun x hx => mem_center_of_map_mem_center η hC (ker_isogenyStd_le_center hx)
  obtain ⟨hsurj, hZ', h2'⟩ :=
    lift_oddPart (isogenyStd.comp η) (isogenyStd_surjective.comp hη) hNZ
  have : Group.IsPerfect (E ⧸ oddPart (isogenyStd.comp η).ker hNZ) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hsq := (TwistedE6FieldTwoCover.twisted_E6_field_two_central_two_kernel_elementary _ hsurj
    hZ' h2').1 (c : E ⧸ oddPart (isogenyStd.comp η).ker hNZ) (by
      rw [MonoidHom.mem_ker, QuotientGroup.lift_mk, MonoidHom.comp_apply,
        show η c = 1 from hc, map_one])
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_oddPart] at hsq
  obtain ⟨k, hk⟩ := h2 ⟨c ^ 2, pow_mem hc 2⟩
  exact eq_one_of_odd_orderOf hsq.2 (by simpa using congrArg Subtype.val hk)

theorem isElementaryAbelian_ker
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (η : E →* twistedE6Group 2 1) (hη : Function.Surjective η) (hC : η.ker ≤ center E)
    (h2 : IsPGroup 2 η.ker) : CFSG.IsElementaryAbelian 2 η.ker :=
  { is_comm := ⟨fun u v => Subtype.ext (mem_center_iff.1 (hC v.2) u)⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact sq_eq_one_of_mem_ker η hη hC h2 x.2) }

theorem levi_singleton_twistedE6
    (i : Fin (twistedE6Datum 2 1).rank) :
    (twistedE6Datum 2 1).levi {i} = rankOne (twistedE6Datum 2 1).rootGroup i :=
  levi_singleton _ i

theorem levi_union
    (A B : Finset (Fin (twistedE6Datum 2 1).rank)) :
    (twistedE6Datum 2 1).levi (A ∪ B) =
      (twistedE6Datum 2 1).levi A ⊔ (twistedE6Datum 2 1).levi B :=
  Finset.iSup_union

theorem commutator_levi_of_subset_levi34
    {S : Finset (Fin (twistedE6Datum 2 1).rank)}
    (hS : S ⊆ levi34) :
    ⁅(twistedE6Datum 2 1).levi S, (twistedE6Datum 2 1).levi S⁆ = (twistedE6Datum 2 1).levi S := by
  refine le_antisymm (commutator_self_le _) (iSup₂_le fun j hj => ?_)
  have hj' : j = 2 ∨ j = 3 := by simpa [levi34] using hS hj
  exact (le_of_eq (commutator_rankOne_short j hj').symm).trans
    (commutator_mono (rankOne_le_levi _ hj) (rankOne_le_levi _ hj))

theorem finset_cases
    : ∀ J : Finset (Fin (twistedE6Datum 2 1).rank), J.card ≤ 2 →
    3 ∉ J ∨ (3 ∈ J ∧ J.erase 3 ⊆ J ∩ levi34) ∨
      ∃ j, (j = 0 ∨ j = 1) ∧ J.erase 3 = {j} ∧ J ∩ levi34 = {3} := by
  have key : ∀ J : Finset (Fin 4), J.card ≤ 2 →
      3 ∉ J ∨ (3 ∈ J ∧ J.erase 3 ⊆ J ∩ ({2, 3} : Finset (Fin 4))) ∨
        ∃ j, (j = 0 ∨ j = 1) ∧ J.erase 3 = {j} ∧ J ∩ ({2, 3} : Finset (Fin 4)) = {3} := by
    decide +kernel
  exact key

theorem ker_eq_bot_of_injOn_levi
    {G : Type} [Group G] [Group.IsPerfect G]
    (ι : G →* twistedE6Group 2 1) (hι : Function.Surjective ι) (hC : ι.ker ≤ center G)
    (hL : ∀ x ∈ ⁅((twistedE6Datum 2 1).levi levi123).comap ι,
      ((twistedE6Datum 2 1).levi levi123).comap ι⁆, ι x = 1 → x = 1)
    (h34 : ∀ x ∈ ⁅((twistedE6Datum 2 1).levi levi34).comap ι,
      ((twistedE6Datum 2 1).levi levi34).comap ι⁆, ι x = 1 → x = 1) :
    ι.ker = ⊥ := by
  classical
  have hat_mono : ∀ {X Y : Subgroup (twistedE6Group 2 1)}, X ≤ Y →
      ⁅X.comap ι, X.comap ι⁆ ≤ ⁅Y.comap ι, Y.comap ι⁆ := fun h =>
    commutator_mono (comap_mono h) (comap_mono h)
  have hat_map : ∀ X : Subgroup (twistedE6Group 2 1), ⁅X, X⁆ = X →
      (⁅X.comap ι, X.comap ι⁆).map ι = X := fun X hX => by
    rw [map_commutator, map_comap_eq_self_of_surjective hι, hX]
  have hmapL : (⁅((twistedE6Datum 2 1).levi levi123).comap ι,
      ((twistedE6Datum 2 1).levi levi123).comap ι⁆).map ι = (twistedE6Datum 2 1).levi levi123 :=
    hat_map _ commutator_levi123
  have h3 : (3 : Fin (twistedE6Datum 2 1).rank) ∈ levi34 := by
    have key : (3 : Fin 4) ∈ ({2, 3} : Finset (Fin 4)) := by decide
    exact key
  have hne3 : ∀ x : Fin (twistedE6Datum 2 1).rank, x ≠ 3 → x ∈ levi123 := by
    have key : ∀ x : Fin 4, x ≠ 3 → x ∈ ({0, 1, 2} : Finset (Fin 4)) := by decide
    exact key
  have herase : ∀ J : Finset (Fin (twistedE6Datum 2 1).rank), J.erase 3 ⊆ levi123 :=
    fun J x hx => hne3 x (Finset.ne_of_mem_erase hx)
  have hAinj : ∀ J : Finset (Fin (twistedE6Datum 2 1).rank),
      ∀ x ∈ ⁅((twistedE6Datum 2 1).levi levi123).comap ι,
        ((twistedE6Datum 2 1).levi levi123).comap ι⁆ ⊓
          ((twistedE6Datum 2 1).levi (J.erase 3)).comap ι, ι x = 1 → x = 1 :=
    fun J x hx => hL x (mem_inf.1 hx).1
  have hBinj : ∀ J : Finset (Fin (twistedE6Datum 2 1).rank),
      ∀ x ∈ ⁅((twistedE6Datum 2 1).levi (J ∩ levi34)).comap ι,
        ((twistedE6Datum 2 1).levi (J ∩ levi34)).comap ι⁆, ι x = 1 → x = 1 :=
    fun J x hx => h34 x (hat_mono (levi_mono _ Finset.inter_subset_right) hx)
  have hAmap : ∀ J : Finset (Fin (twistedE6Datum 2 1).rank),
      (⁅((twistedE6Datum 2 1).levi levi123).comap ι,
        ((twistedE6Datum 2 1).levi levi123).comap ι⁆ ⊓
          ((twistedE6Datum 2 1).levi (J.erase 3)).comap ι).map ι =
        (twistedE6Datum 2 1).levi (J.erase 3) := fun J =>
    map_inf_comap_of_le ι ((levi_mono _ (herase J)).trans hmapL.ge)
  have hBmap : ∀ J : Finset (Fin (twistedE6Datum 2 1).rank),
      (⁅((twistedE6Datum 2 1).levi (J ∩ levi34)).comap ι,
        ((twistedE6Datum 2 1).levi (J ∩ levi34)).comap ι⁆).map ι =
          (twistedE6Datum 2 1).levi (J ∩ levi34) := fun J =>
    hat_map _ (commutator_levi_of_subset_levi34 Finset.inter_subset_right)
  have hCT := curtisTitsConclusion_twistedE6.{0} 2 1 ⟨Nat.prime_two, le_rfl, rfl⟩
  refine ker_eq_bot_of_lifts hCT.1.1 hCT.2.1.1 ι hC (fun J =>
    ⁅((twistedE6Datum 2 1).levi levi123).comap ι, ((twistedE6Datum 2 1).levi levi123).comap ι⁆ ⊓
        ((twistedE6Datum 2 1).levi (J.1.erase 3)).comap ι ⊔
      ⁅((twistedE6Datum 2 1).levi (J.1 ∩ levi34)).comap ι,
        ((twistedE6Datum 2 1).levi (J.1 ∩ levi34)).comap ι⁆) ?_ ?_ ?_
  ·
    intro J J' hJJ'
    exact sup_le_sup
      (inf_le_inf_left _ (comap_mono (levi_mono _ (Finset.erase_subset_erase _ hJJ'))))
      (hat_mono (levi_mono _ (Finset.inter_subset_inter_right hJJ')))
  ·
    intro J
    rcases finset_cases J.1 J.2 with hJ | ⟨hJ, hsub⟩ | ⟨j, hj, hJe, hJi⟩
    ·
      have hBA : ⁅((twistedE6Datum 2 1).levi (J.1 ∩ levi34)).comap ι,
            ((twistedE6Datum 2 1).levi (J.1 ∩ levi34)).comap ι⁆ ≤
          ⁅((twistedE6Datum 2 1).levi levi123).comap ι,
            ((twistedE6Datum 2 1).levi levi123).comap ι⁆ ⊓
              ((twistedE6Datum 2 1).levi (J.1.erase 3)).comap ι := by
        have hsub' : J.1 ∩ levi34 ⊆ J.1.erase 3 := fun x hx => Finset.mem_erase.2
          ⟨fun h => hJ (h ▸ Finset.mem_of_mem_inter_left hx), Finset.mem_of_mem_inter_left hx⟩
        exact le_inf (hat_mono (levi_mono _ (hsub'.trans (herase J.1))))
          ((commutator_self_le _).trans (comap_mono (levi_mono _ hsub')))
      intro x hx
      rw [sup_eq_left.2 hBA] at hx
      exact hAinj J.1 x hx
    ·
      have hAB : ⁅((twistedE6Datum 2 1).levi levi123).comap ι,
            ((twistedE6Datum 2 1).levi levi123).comap ι⁆ ⊓
              ((twistedE6Datum 2 1).levi (J.1.erase 3)).comap ι ≤
          ⁅((twistedE6Datum 2 1).levi (J.1 ∩ levi34)).comap ι,
            ((twistedE6Datum 2 1).levi (J.1 ∩ levi34)).comap ι⁆ := by
        refine (le_commutator_of_injOn ι (hAinj J.1) ?_).trans ?_
        · rw [hAmap]
          exact commutator_levi_of_subset_levi34 (hsub.trans Finset.inter_subset_right)
        · exact (commutator_mono inf_le_right inf_le_right).trans (hat_mono (levi_mono _ hsub))
      intro x hx
      rw [sup_eq_right.2 hAB] at hx
      exact hBinj J.1 x hx
    ·
      refine injOn_sup_of_commute ι (fun a ha b hb => ?_) (hAinj J.1) (hBinj J.1) ?_
      · refine commute_of_mem_commutator
          (Y := ((twistedE6Datum 2 1).levi (J.1 ∩ levi34)).comap ι) (fun y hy => hC ?_) hb
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
        have ha' : ι a ∈ rankOne (twistedE6Datum 2 1).rootGroup j := by
          have h := (mem_inf.1 ha).2
          rwa [mem_comap, hJe, levi_singleton_twistedE6] at h
        have hy' : ι y ∈ rankOne (twistedE6Datum 2 1).rootGroup 3 := by
          rwa [mem_comap, hJi, levi_singleton_twistedE6] at hy
        exact commute_rankOne_three hj ha' hy'
      · rw [hAmap, hBmap, hJe, hJi, levi_singleton_twistedE6, levi_singleton_twistedE6]
        exact rankOne_inf_rankOne_three hj
  ·
    intro J
    have hJ : J.1.erase 3 ∪ J.1 ∩ levi34 = J.1 := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.1 hx with hx | hx
        exacts [Finset.mem_of_mem_erase hx, Finset.mem_of_mem_inter_left hx]
      · intro hx
        by_cases hx3 : x = 3
        · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hx, hx3 ▸ h3⟩)
        · exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hx3, hx⟩)
    change (_ ⊔ _ : Subgroup _).map ι = (twistedE6Datum 2 1).levi J.1
    rw [Subgroup.map_sup, hAmap, hBmap, ← levi_union, hJ]

theorem map_commutator_comap_levi34
    {E : Type*} [Group E] (η : E →* twistedE6Group 2 1)
    (hη : Function.Surjective η) :
    (⁅((twistedE6Datum 2 1).levi levi34).comap η,
      ((twistedE6Datum 2 1).levi levi34).comap η⁆).map η = (twistedE6Datum 2 1).levi levi34 := by
  rw [map_commutator, map_comap_eq_self_of_surjective hη,
    commutator_levi_of_subset_levi34 subset_rfl]

theorem ker_le_commutator_comap_levi34
    {E : Type} [Group E] [Finite E] [Group.IsPerfect E]
    (η : E →* twistedE6Group 2 1) (hη : Function.Surjective η) (hC : η.ker ≤ center E)
    (h2 : IsPGroup 2 η.ker) :
    η.ker ≤ ⁅((twistedE6Datum 2 1).levi levi34).comap η,
      ((twistedE6Datum 2 1).levi levi34).comap η⁆ := by
  obtain ⟨N, hN⟩ : ∃ N : Subgroup E, N = η.ker ⊓ ⁅((twistedE6Datum 2 1).levi levi34).comap η,
      ((twistedE6Datum 2 1).levi levi34).comap η⁆ := ⟨_, rfl⟩
  have hNk : N ≤ η.ker := hN ▸ inf_le_left
  have : N.Normal := normal_of_le_center (hNk.trans hC)
  obtain ⟨ι, hι⟩ : ∃ ι : E ⧸ N →* twistedE6Group 2 1, ι = QuotientGroup.lift N η hNk :=
    ⟨_, rfl⟩
  have hιπ : ∀ x : E, ι (x : E ⧸ N) = η x := fun x => by
    rw [hι]
    exact QuotientGroup.lift_mk _ _ _
  have hπsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  have hιsurj : Function.Surjective ι := fun u => by
    obtain ⟨x, rfl⟩ := hη u
    exact ⟨x, hιπ x⟩
  have hιC : ι.ker ≤ center (E ⧸ N) := by
    intro y hy
    obtain ⟨x, rfl⟩ := hπsurj y
    have hx : x ∈ η.ker := by rw [MonoidHom.mem_ker, ← hιπ]; exact hy
    refine mem_center_iff.2 fun g => ?_
    obtain ⟨g', rfl⟩ := hπsurj g
    rw [← map_mul, ← map_mul, mem_center_iff.1 (hC hx) g']
  have : Group.IsPerfect (E ⧸ N) := Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) hπsurj
  have hcomap : ∀ X : Subgroup (twistedE6Group 2 1),
      X.comap ι = (X.comap η).map (QuotientGroup.mk' N) := by
    intro X
    ext y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := hπsurj y
      exact ⟨x, show η x ∈ X by rw [← hιπ]; exact hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      rw [mem_comap, QuotientGroup.mk'_apply, hιπ]
      exact hx
  have hbot : ι.ker = ⊥ := by
    refine ker_eq_bot_of_injOn_levi ι hιsurj hιC ?_ ?_
    ·
      intro x hx hx1
      rw [hcomap, ← map_commutator] at hx
      obtain ⟨f, hf, rfl⟩ := hx
      have hf1 : f ∈ η.ker := by rw [MonoidHom.mem_ker, ← hιπ]; exact hx1
      have hf' : f ∈ (⊥ : Subgroup E) :=
        (commutator_comap_levi123_inf_ker_eq_bot η hη hC h2).1 ▸ mem_inf.2 ⟨hf, hf1⟩
      rw [mem_bot.1 hf', map_one]
    ·
      intro x hx hx1
      rw [hcomap, ← map_commutator] at hx
      obtain ⟨d, hd, rfl⟩ := hx
      have hd1 : d ∈ η.ker := by rw [MonoidHom.mem_ker, ← hιπ]; exact hx1
      exact (QuotientGroup.eq_one_iff d).2 (hN ▸ mem_inf.2 ⟨hd1, hd⟩)
  intro c hc
  have hc' : (c : E ⧸ N) ∈ ι.ker := by rw [MonoidHom.mem_ker, hιπ]; exact hc
  rw [hbot, mem_bot, QuotientGroup.eq_one_iff, hN] at hc'
  exact (mem_inf.1 hc').2

end CFSG.EvenSmallLie.TwoE6
