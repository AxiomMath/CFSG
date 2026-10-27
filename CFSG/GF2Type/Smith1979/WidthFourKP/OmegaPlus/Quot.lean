module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.LayerData
public import CFSG.GF2Type.Smith1979.CaseI25Layer
public import CFSG.GH74.Uniqueness.Section4Lift
public import CFSG.LargeExtraspecial.S111SJSet
public import CFSG.LargeExtraspecial.S111SJLay
public import CFSG.LargeExtraspecial.S12Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4

section Layer

variable {M : Type} [Group M] [Finite M] {E : Subgroup M} [E.Normal]

theorem exists_fixed_lift_center (hodd : Odd (Nat.card (center E))) {w : M} (hw2 : w * w = 1)
    {x : E ⧸ center E} (hx : S11.barAct E w x = x) :
    ∃ e : E, (QuotientGroup.mk e : E ⧸ center E) = x ∧ MulAut.conjNormal w e = e := by
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective x
  let N : Subgroup M := (center E).map E.subtype
  haveI : N.Normal := ConjAct.normal_of_characteristic_of_normal
  have hNodd : Odd (Nat.card N) := by rwa [card_subtype]
  rw [S11.barAct_mk, QuotientGroup.eq_iff_div_mem] at hx
  have hd : w * d * w⁻¹ * (d : M)⁻¹ ∈ N := by
    refine ⟨_, hx, ?_⟩
    rw [map_div, coe_subtype, MulAut.conjNormal_apply, div_eq_mul_inv]
  obtain ⟨_, ⟨z, hz, rfl⟩, hfix⟩ := GH74.Uniqueness.exists_fixed_mem_coset hNodd hw2
    (by rw [normalizer_eq_top]; exact mem_top w) (by rw [normalizer_eq_top]; exact mem_top _) hd
  refine ⟨d * z, ?_, Subtype.ext ?_⟩
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz, mul_one]
  · rw [MulAut.conjNormal_apply, coe_mul]
    exact hfix

theorem exists_two_lift (hodd : Odd (Nat.card (center E))) {t : M} (ht2 : t * t = 1)
    {T : Subgroup (E ⧸ center E)} (hT2 : IsPGroup 2 T)
    (hTfix : ∀ y ∈ T, S11.barAct E t y = y) :
    ∃ T₀ : Subgroup E, IsPGroup 2 T₀ ∧ T₀.map (QuotientGroup.mk' (center E)) = T ∧
      (∀ e ∈ T₀, (e : M) * t = t * e) ∧
      ∀ m : M, m * t = t * m → (∀ y ∈ T, S11.barAct E m y ∈ T) →
        ∀ e ∈ T₀, MulAut.conjNormal m e ∈ T₀ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let W : Subgroup E := T.comap (QuotientGroup.mk' (center E)) ⊓ (centralizer {t}).subgroupOf E
  have hWT : ∀ w : W, (QuotientGroup.mk' (center E)) (w : E) ∈ T := fun w => (mem_inf.mp w.2).1
  have hWt : ∀ w : W, ((w : E) : M) * t = t * (w : E) := fun w =>
    mem_centralizer_singleton_iff.mp (mem_subgroupOf.mp (mem_inf.mp w.2).2)
  let φ : W →* T := ((QuotientGroup.mk' (center E)).comp W.subtype).codRestrict T hWT
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨e, rfl, he⟩ := exists_fixed_lift_center hodd ht2 (hTfix y hy)
    refine ⟨⟨e, hy, mem_subgroupOf.mpr (mem_centralizer_singleton_iff.mpr ?_)⟩, rfl⟩
    exact (mul_inv_eq_iff_eq_mul.mp
      ((MulAut.conjNormal_apply t e).symm.trans (congrArg Subtype.val he))).symm
  have hker : φ.ker ≤ center W := by
    intro w hw
    have hwZ : (w : E) ∈ center E :=
      (QuotientGroup.eq_one_iff (w : E)).mp (congrArg Subtype.val hw)
    exact mem_center_iff.mpr fun v => Subtype.ext (mem_center_iff.mp hwZ v)
  haveI : Group.IsNilpotent T := hT2.isNilpotent
  haveI : Group.IsNilpotent W := Subgroup.isNilpotent_of_ker_le_center φ hker
  obtain ⟨Q⟩ := Sylow.nonempty (p := 2) (G := W)
  haveI : Subsingleton (Sylow 2 W) :=
    (Sylow.unique_of_normal Q instNormalOfIsNilpotentOfFactPrime).instSubsingleton
  have hQ : (Q : Subgroup W).map φ = ⊤ := by
    rw [← Sylow.coe_mapSurjective hφ]
    exact ((Q.mapSurjective hφ).is_maximal' (hT2.of_equiv topEquiv.symm) le_top).symm
  refine ⟨(Q : Subgroup W).map W.subtype, Q.isPGroup'.map _, le_antisymm ?_ ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact hWT w
  · intro y hy
    obtain ⟨w, hw, hwy⟩ : (⟨y, hy⟩ : T) ∈ (Q : Subgroup W).map φ := hQ ▸ mem_top _
    exact ⟨w, ⟨w, hw, rfl⟩, congrArg Subtype.val hwy⟩
  · rintro _ ⟨w, -, rfl⟩
    exact hWt w
  · intro m hmt hmT
    have hW : ∀ w : W, MulAut.conjNormal m (w : E) ∈ W := by
      intro w
      refine mem_inf.mpr ⟨?_, mem_subgroupOf.mpr (mem_centralizer_singleton_iff.mpr ?_)⟩
      · change (QuotientGroup.mk (MulAut.conjNormal m (w : E)) : E ⧸ center E) ∈ T
        rw [← S11.barAct_mk]
        exact hmT _ (hWT w)
      · rw [MulAut.conjNormal_apply]
        exact Commute.mul_left (Commute.mul_left hmt (hWt w)) (Commute.inv_left hmt)
    let α : W →* W := ((MulAut.conjNormal m).toMonoidHom.comp W.subtype).codRestrict W hW
    obtain ⟨R, hR⟩ := (Q.isPGroup'.map α).exists_le_sylow
    rw [Subsingleton.elim R Q] at hR
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨α w, hR ⟨w, hw, rfl⟩, rfl⟩

variable {O : Type*} [Group O] {ι : M →* O} {t : M} {t₀ : O} {P Ct Mb : Subgroup O}
  {Triv : O → Prop}

theorem core_of_layer (hι : Function.Injective ι) (hodd : Odd (Nat.card (center E)))
    (ht₀ : ι t = t₀) (ht2 : t * t = 1) (ht1 : t₀ ≠ 1)
    (hPι : P ≤ ι.range) (hPc : ∀ m : M, ι m ∈ P → m * t = t * m)
    (hCt : ∀ m : M, m * t = t * m → ι m ∈ Ct) (hMb : ∀ m : M, ι m ∈ Mb)
    (hK4 : ∀ T : Subgroup O, T ≤ Ct → (∀ σ ∈ T, Triv σ) → Nat.card T ∣ 4)
    (hKt : ∀ T : Subgroup O, T ≤ Ct → (∀ σ ∈ T, Triv σ) → Nat.card T = 4 → t₀ ∈ T)
    (hKe : ∀ σ ∈ Ct, Triv σ → σ * σ = 1)
    (hKc : ∀ σ ∈ Ct, Triv σ → ∀ m ∈ Mb, σ = m * t₀ * m⁻¹ → σ = t₀)
    (hO2 : ∀ T : Subgroup O, T ≤ Ct → IsPGroup 2 T → (∀ p ∈ P, ∀ x ∈ T, p * x * p⁻¹ ∈ T) →
      ∀ σ ∈ T, Triv σ)
    (T : Subgroup (E ⧸ center E)) (hTfix : ∀ y ∈ T, S11.barAct E t y = y) (hT2 : IsPGroup 2 T)
    (hTinv : ∀ σ : MulAut (E ⧸ center E), σ * S11.barAct E t = S11.barAct E t * σ →
      ∀ y ∈ T, σ y ∈ T) :
    Nat.card T ≤ 4 ∧ (Nat.card T = 4 → ∃ y₁ ∈ T, ∃ y₂ ∈ T, orderOf y₁ = 2 ∧ orderOf y₂ = 2 ∧
      ¬ IsConj y₁ y₂) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀, hT₀2, hT₀T, hT₀t, hT₀m⟩ := exists_two_lift hodd ht2 hT2 hTfix
  let f : E →* O := ι.comp E.subtype
  have hf : Function.Injective f := hι.comp E.subtype_injective
  have hCt' : T₀.map f ≤ Ct := by
    rintro _ ⟨e, he, rfl⟩
    exact hCt e (hT₀t e he)
  have hP' : ∀ p ∈ P, ∀ x ∈ T₀.map f, p * x * p⁻¹ ∈ T₀.map f := by
    intro p hp x hx
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp (hPι hp)
    obtain ⟨e, he, rfl⟩ := hx
    have hmt := hPc m hp
    refine ⟨MulAut.conjNormal m e, hT₀m m hmt (fun y hy => hTinv _ ?_ y hy) e he, ?_⟩
    · rw [← map_mul, ← map_mul, hmt]
    · change ι ((MulAut.conjNormal m e : E) : M) = ι m * ι e * (ι m)⁻¹
      rw [MulAut.conjNormal_apply, map_mul, map_mul, map_inv]
  have hTriv : ∀ σ ∈ T₀.map f, Triv σ := hO2 _ hCt' (hT₀2.map f) hP'
  have hcard : Nat.card T ∣ Nat.card T₀ := hT₀T ▸ card_map_dvd T₀ _
  have h4 : Nat.card T₀ ∣ 4 := card_map_of_injective hf ▸ hK4 _ hCt' hTriv
  refine ⟨Nat.le_of_dvd (by norm_num) (hcard.trans h4), fun hT4 => ?_⟩
  have hT₀4 : Nat.card T₀ = 4 := Nat.dvd_antisymm h4 (hT4 ▸ hcard)
  obtain ⟨et, het, hett⟩ := hKt _ hCt' hTriv (by rw [card_map_of_injective hf, hT₀4])
  have hT₀Z : ∀ e ∈ T₀, (QuotientGroup.mk e : E ⧸ center E) = 1 → e = 1 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT₀2
    have hbot : T₀ ⊓ center E = ⊥ := inf_eq_bot_of_coprime (by
      rw [hk]
      exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd))
    intro e he h1
    rw [← mem_bot, ← hbot]
    exact mem_inf.mpr ⟨he, (QuotientGroup.eq_one_iff e).mp h1⟩
  have h3 : 1 < ((T₀ : Set E) \ {1}).ncard := by
    rw [Set.ncard_diff_singleton_of_mem T₀.one_mem, ← Nat.card_coe_set_eq]
    change 1 < Nat.card T₀ - 1
    omega
  obtain ⟨eu, ⟨heu, heu1⟩, heut⟩ := Set.exists_ne_of_one_lt_ncard h3 et
  have het2 : et * et = 1 := hf (by rw [map_mul, hett, ← ht₀, ← map_mul, ht2, map_one, map_one])
  have heu2 : eu * eu = 1 := hf (by
    rw [map_mul, map_one]
    exact hKe _ (hCt' ⟨eu, heu, rfl⟩) (hTriv _ ⟨eu, heu, rfl⟩))
  have het1 : et ≠ 1 := by
    rintro rfl
    exact ht1 (by rw [← hett, map_one])
  have hmem : ∀ e ∈ T₀, (QuotientGroup.mk e : E ⧸ center E) ∈ T := fun e he => by
    rw [← hT₀T]
    exact mem_map_of_mem _ he
  have hord : ∀ e ∈ T₀, e ≠ 1 → e * e = 1 →
      orderOf (QuotientGroup.mk e : E ⧸ center E) = 2 := fun e he he1 he2 =>
    orderOf_eq_prime (by rw [pow_two, ← QuotientGroup.mk_mul, he2, QuotientGroup.mk_one])
      fun h => he1 (hT₀Z e he h)
  refine ⟨_, hmem et het, _, hmem eu heu, hord et het het1 het2, hord eu heu heu1 heu2,
    fun hc => heut (hf ?_)⟩
  obtain ⟨a, ha⟩ := isConj_iff.mp hc
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective a
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    QuotientGroup.eq] at ha
  obtain ⟨z, hz, heuz⟩ : ∃ z ∈ center E, eu = c * et * c⁻¹ * z :=
    ⟨_, ha, (mul_inv_cancel_left _ _).symm⟩
  have hz1 : z = 1 := by
    have hc2 : c * et * c⁻¹ * (c * et * c⁻¹) = 1 := by
      rw [show c * et * c⁻¹ * (c * et * c⁻¹) = c * (et * et) * c⁻¹ by group, het2, mul_one,
        mul_inv_cancel]
    have hcz : Commute z (c * et * c⁻¹) := (mem_center_iff.mp hz (c * et * c⁻¹)).symm
    have hz2 : z ^ 2 = 1 := by
      rwa [heuz, hcz.mul_mul_mul_comm, hc2, one_mul, ← pow_two] at heu2
    exact orderOf_eq_one_iff.mp ((Nat.coprime_two_right.mpr (Odd.of_dvd_nat hodd
      (orderOf_dvd_natCard (center E) hz))).eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hz2))
  rw [hett]
  refine hKc _ (hCt' ⟨eu, heu, rfl⟩) (hTriv _ ⟨eu, heu, rfl⟩) (f c) (hMb c) ?_
  rw [heuz, hz1, mul_one, map_mul, map_mul, map_inv, hett]

theorem layerData_of_layer (hι : Function.Injective ι) (hodd : Odd (Nat.card (center E)))
    (hE : commutator E = ⊤) {L₀ : Subgroup O} (ht₀ : ι t = t₀) (ht : t₀ ∈ L₀) (ht1 : t₀ ≠ 1)
    (hL₀ : L₀ ≤ ι.range) (hL8 : Nat.card L₀ = 8) (hLsq : ∀ l ∈ L₀, l * l = 1)
    (hfaith : ∀ l ∈ L₀, (∀ y ∈ E.map ι, l * y = y * l) → l = 1)
    (hPι : P ≤ ι.range) (hPc : ∀ m : M, ι m ∈ P → m * t = t * m)
    (hCt : ∀ m : M, m * t = t * m → ι m ∈ Ct) (hMb : ∀ m : M, ι m ∈ Mb)
    (hP9 : Nat.card P = 9) (hP3 : ∀ x ∈ P, x ^ 3 = 1)
    (hPn : ∀ c ∈ Ct, ∀ x ∈ P, c * x * c⁻¹ ∈ P)
    (hK4 : ∀ T : Subgroup O, T ≤ Ct → (∀ σ ∈ T, Triv σ) → Nat.card T ∣ 4)
    (hKt : ∀ T : Subgroup O, T ≤ Ct → (∀ σ ∈ T, Triv σ) → Nat.card T = 4 → t₀ ∈ T)
    (hKe : ∀ σ ∈ Ct, Triv σ → σ * σ = 1)
    (hKc : ∀ σ ∈ Ct, Triv σ → ∀ m ∈ Mb, σ = m * t₀ * m⁻¹ → σ = t₀)
    (hC32 : ∀ c ∈ Ct, c ^ 32 ∈ P)
    (hO2 : ∀ T : Subgroup O, T ≤ Ct → IsPGroup 2 T → (∀ p ∈ P, ∀ x ∈ T, p * x * p⁻¹ ∈ T) →
      ∀ σ ∈ T, Triv σ)
    (hEtop : 15120 < Nat.card E → E = ⊤) (hZ : ∃ e : E, ι e ∈ P ∧ e ∉ center E) :
    LayerData (E ⧸ center E) ((S11.barAct E).comp (L₀.comap ι).subtype).range (S11.barAct E t)
      ((P.comap (ι.comp E.subtype)).map (QuotientGroup.mk' (center E))) := by
  haveI : Group.IsPerfect E := ⟨hE⟩
  have htL : ι t ∈ L₀ := ht₀ ▸ ht
  have ht2 : t * t = 1 := hι (by rw [map_mul, ht₀, hLsq t₀ ht, map_one])
  have hfix : ∀ e : E, MulAut.conjNormal t e = e ↔ (e : M) * t = t * e := fun e => by
    rw [← Subtype.coe_inj, MulAut.conjNormal_apply, mul_inv_eq_iff_eq_mul]
    exact eq_comm
  have hkey : ∀ l : M, ι l ∈ L₀ → S11.barAct E l = 1 → l = 1 := by
    intro l hl h1
    have hc := S11.commute_of_barAct_eq_one h1
    refine hι ((hfaith _ hl ?_).trans (map_one ι).symm)
    rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, ← map_mul, hc e he]
  have hinj : Function.Injective ((S11.barAct E).comp (L₀.comap ι).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro l hl
    exact mem_bot.mpr (Subtype.ext (hkey l l.2 hl))
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    intro x hx y hy
    exact congrArg Subtype.val
      (IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (hP9.trans (by norm_num)) ⟨x, hx⟩
        ⟨y, hy⟩)
  have hf : Function.Injective (ι.comp E.subtype) := hι.comp E.subtype_injective
  refine
    { card_A := ?_
      sq_A := ?_
      mem_A := MonoidHom.mem_range.mpr ⟨⟨t, htL⟩, rfl⟩
      ne_one := fun h => ht1 (by rw [← ht₀, hkey t htL h, map_one])
      B_ne := ?_
      B_exp := ?_
      B_comm := ?_
      B_fix := ?_
      B_norm := ?_
      two_quot := ?_
      inner := ?_
      core := core_of_layer hι hodd ht₀ ht2 ht1 hPι hPc hCt hMb hK4 hKt hKe hKc hO2 }
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, ← card_map_of_injective hι,
      map_comap_eq_self hL₀, hL8]
  · rintro _ ⟨l, rfl⟩
    have hl : l * l = 1 :=
      Subtype.ext (hι (by rw [coe_mul, coe_one, map_mul, map_one]; exact hLsq _ l.2))
    rw [← map_mul, hl, map_one]
  · obtain ⟨e, heP, heZ⟩ := hZ
    intro h
    have he : (QuotientGroup.mk' (center E)) e ∈
        (P.comap (ι.comp E.subtype)).map (QuotientGroup.mk' (center E)) := mem_map_of_mem _ heP
    rw [h, mem_bot] at he
    exact heZ ((QuotientGroup.eq_one_iff e).mp he)
  · rintro _ ⟨e, he, rfl⟩
    rw [← map_pow, show e ^ 3 = 1 from hf (by rw [map_pow, map_one]; exact hP3 _ he), map_one]
  · rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    rw [← map_mul, ← map_mul,
      show e * e' = e' * e from hf (by rw [map_mul, map_mul]; exact hPcomm _ he _ he')]
  · rintro _ ⟨e, he, rfl⟩
    rw [QuotientGroup.mk'_apply, S11.barAct_mk, (hfix e).mpr (hPc _ he)]
  · rintro c hc _ ⟨e', he', rfl⟩
    obtain ⟨e, rfl, he⟩ := exists_fixed_lift_center hodd ht2 hc
    refine ⟨e * e' * e⁻¹, ?_, by simp only [map_mul, map_inv, QuotientGroup.mk'_apply]⟩
    change ι.comp E.subtype (e * e' * e⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact hPn _ (hCt _ ((hfix e).mp he)) _ he'
  · intro c hc
    obtain ⟨e, rfl, he⟩ := exists_fixed_lift_center hodd ht2 hc
    refine ⟨e ^ 32, ?_, by rw [map_pow, QuotientGroup.mk'_apply]⟩
    change ι.comp E.subtype (e ^ 32) ∈ P
    rw [map_pow]
    exact hC32 _ (hCt _ ((hfix e).mp he))
  · intro hX
    have hEt : E = ⊤ :=
      hEtop (hX.trans_le (Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective))
    have htE : t ∈ E := by
      rw [hEt]
      exact mem_top t
    exact ⟨QuotientGroup.mk ⟨t, htE⟩, S11.barAct_of_mem E ⟨t, htE⟩⟩

end Layer

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S) in
theorem odd_card_center_timmesfeldLayer : Odd (Nat.card (center (timmesfeldLayer S.Mbar))) :=
  Odd.of_dvd_nat (S5.odd_card_timmesfeldOddCore S.Mbar)
    ((card_subtype _ _).symm.dvd.trans (card_dvd_of_le (Case25.center_layer_le_oddCore S)))

theorem exists_layerData (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) {P : Subgroup S.O} (hPR : P ≤ Rbar S g t)
    (hP9 : Nat.card P = 9) (hq : CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar))
    (hfaith : ∀ l ∈ S.Lbar g, (∀ y ∈ (timmesfeldLayer S.Mbar).map S.Mbar.subtype,
      l * y = y * l) → l = 1)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1) (hPn : ∀ c ∈ S14.Ct S t, ∀ x ∈ P, c * x * c⁻¹ ∈ P)
    (hK4 : ∀ T : Subgroup S.O, T ≤ S14.Ct S t →
      (∀ σ ∈ T, ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → Nat.card T ∣ 4)
    (hKt : ∀ T : Subgroup S.O, T ≤ S14.Ct S t →
      (∀ σ ∈ T, ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → Nat.card T = 4 → t ∈ T)
    (hKe : ∀ σ ∈ S14.Ct S t, (∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) →
      σ * σ = 1)
    (hKc : ∀ σ ∈ S14.Ct S t, (∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) →
      ∀ m ∈ S.Mbar, σ = m * t * m⁻¹ → σ = t)
    (hC32 : ∀ c ∈ S14.Ct S t, c ^ 32 ∈ P)
    (hO2 : ∀ T : Subgroup S.O, T ≤ S14.Ct S t → IsPGroup 2 T →
      (∀ p ∈ P, ∀ x ∈ T, p * x * p⁻¹ ∈ T) →
        ∀ σ ∈ T, ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hEtop : 15120 < Nat.card (timmesfeldLayer S.Mbar) → timmesfeldLayer S.Mbar = ⊤)
    (hZ : ∃ e : timmesfeldLayer S.Mbar, ((e : S.Mbar) : S.O) ∈ P ∧
      e ∉ center (timmesfeldLayer S.Mbar)) :
    ∃ (A : Subgroup (MulAut (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar))))
      (τ : MulAut (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)))
      (B : Subgroup (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar))),
      LayerData (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) A τ B := by
  have hL : S.Lbar g ≤ S.Mbar.subtype.range := by
    rw [range_subtype]
    exact S.Lbar_le_Mbar g
  have hP : P ≤ S.Mbar.subtype.range := by
    rw [range_subtype]
    exact hPR.trans Rbar_le_Mbar
  have hL8 : Nat.card (S.Lbar g) = 8 := by
    rw [C.card_Lbar, hw]
    norm_num
  exact ⟨_, _, _, layerData_of_layer (M := S.Mbar) (E := timmesfeldLayer S.Mbar) (O := S.O)
    (ι := S.Mbar.subtype) (t := ⟨t, S.Lbar_le_Mbar g ht⟩) (t₀ := t) (P := P)
    (Ct := S14.Ct S t) (Mb := S.Mbar)
    (Triv := fun σ => ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    S.Mbar.subtype_injective (odd_card_center_timmesfeldLayer S) hq.1 rfl ht ht1 hL hL8
    (fun _ hl => mul_self_of_mem_Lbar S H.conj_mem hl) hfaith hP
    (fun _ hm => Subtype.ext (commute_of_mem_Rbar H.conj_mem (hPR hm)))
    (fun m hm => mem_inf.mpr ⟨m.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hm)⟩)
    (fun m => m.2) hP9 hP3 hPn hK4 hKt hKe hKc hC32 hO2 hEtop hZ⟩

end CFSG.GF2Type.Smith1979.OmegaPlus
