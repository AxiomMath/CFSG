module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36NatStabReduction
public import CFSG.Quasithin.MS93.S38OffHatMod
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqA6
public import CFSG.Quasithin.MS93.S32U

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin CFSG.Quasithin.MS93.S38H

private theorem card_map_of_inf_ker_eq_bot {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    {A : Subgroup G} (hA : A ⊓ f.ker = ⊥) : Nat.card (A.map f) = Nat.card A := by
  have hinj : Function.Injective (f.comp A.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ A ⊓ f.ker := ⟨x.2, hx⟩
    rw [hA, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext hx')
  have hrange : A.map f = (f.comp A.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

private theorem inf_ne_bot_of_card_eight {G : Type*} [Group G] [Finite G] {S A B : Subgroup G}
    (hS : Nat.card S = 24) (hA : Nat.card A = 8) (hB : Nat.card B = 8) (hAS : A ≤ S)
    (hBS : B ≤ S) : A ⊓ B ≠ ⊥ := by
  intro hAB
  have h1 := Subgroup.relIndex_inf_le (H := A) (K := B) (L := S)
  have hA3 : A.relIndex S = 3 := by
    have := Subgroup.relIndex_mul_card (H := A) (K := S)
    rw [inf_of_le_left hAS, hA, hS] at this
    omega
  have hB3 : B.relIndex S = 3 := by
    have := Subgroup.relIndex_mul_card (H := B) (K := S)
    rw [inf_of_le_left hBS, hB, hS] at this
    omega
  rw [hAB, Subgroup.relIndex_bot_left, hS, hA3, hB3] at h1
  omega

private theorem eq_of_card_cases {G : Type*} [Group G] [Finite G] {P Q : Subgroup G}
    (hPQ : Nat.card Q = Nat.card P)
    (hi : Nat.card ↥(P ⊓ Q) = 1 ∨ Nat.card ↥(P ⊓ Q) = 4 ∨ Nat.card ↥(P ⊓ Q) = 16 ∨
      Nat.card ↥(P ⊓ Q) = 64)
    (hp : Nat.card P = 1 ∨ Nat.card P = 4 ∨ Nat.card P = 16 ∨ Nat.card P = 64)
    (hs : Nat.card ↥(P ⊔ Q) = 1 ∨ Nat.card ↥(P ⊔ Q) = 4 ∨ Nat.card ↥(P ⊔ Q) = 16 ∨
      Nat.card ↥(P ⊔ Q) = 64)
    (hi1 : Nat.card ↥(P ⊓ Q) ≠ 1) (hs16 : Nat.card ↥(P ⊔ Q) ≤ 16) : Q = P := by
  by_contra hne
  have hlt1 : Nat.card ↥(P ⊓ Q) < Nat.card P := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le inf_le_left) fun h => hne ?_
    have h1 : P ⊓ Q = P := Subgroup.eq_of_le_of_card_ge inf_le_left h.symm.le
    exact (Subgroup.eq_of_le_of_card_ge (inf_eq_left.mp h1) hPQ.le).symm
  have hlt2 : Nat.card P < Nat.card ↥(P ⊔ Q) := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le le_sup_left) fun h => hne ?_
    have h1 : P = P ⊔ Q := Subgroup.eq_of_le_of_card_ge le_sup_left h.symm.le
    exact Subgroup.eq_of_le_of_card_ge (sup_eq_left.mp h1.symm) hPQ.ge
  omega

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}

private theorem tripleA6_card_stabilizer [Finite V] (hsq : ∀ v : V, v ^ 2 = 1)
    (h6 : TripleA6Six H ⊤ ⊥) {T : Subgroup (MulAut V)} (hTH : T ≤ H) (hT8 : Nat.card T = 8)
    {v : V} (hv1 : v ≠ 1) (hvT : v ∈ fixV T) : Nat.card (MulAction.stabilizer ↥H v) = 24 := by
  have hH := HatMod.of_tripleA6Six hsq h6
  have horb := (H13.Orbit.orbitTripleA6Six V H h6).1 v hv1
  have hos := (MulAction.stabilizer ↥H v).index_mul_card
  rw [MulAction.index_stabilizer, ← H13.Orbit.orbitIn_eq_orbit, ← Nat.card_coe_set_eq,
    hH.card_H] at hos
  have hle : T.subgroupOf H ≤ MulAction.stabilizer ↥H v := fun t ht =>
    MulAction.mem_stabilizer_iff.mpr (hvT (t : MulAut V) (Subgroup.mem_subgroupOf.mp ht))
  have h8 : Nat.card (T.subgroupOf H) = 8 := by
    rw [← hT8]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [h8] at hdvd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at horb
  rcases horb with h | h <;> rw [h] at hos <;> omega

private theorem tripleA6_stabilizer_inf_center_eq_bot (hH : HatMod H) {v : V} (hv1 : v ≠ 1) :
    MulAction.stabilizer ↥H v ⊓ Subgroup.center ↥H = ⊥ := by
  have := hH.finite
  obtain ⟨zH, hcen, -, hfp⟩ := hH.exists_z
  have hdvd : Nat.card ↥(MulAction.stabilizer ↥H v ⊓ Subgroup.center ↥H) ∣ 3 :=
    hH.center ▸ Subgroup.card_dvd_of_le inf_le_right
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have heq : MulAction.stabilizer ↥H v ⊓ Subgroup.center ↥H = Subgroup.center ↥H :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hH.center])
    have hzc : zH ∈ Subgroup.center ↥H := by
      rw [hcen]
      exact Subgroup.mem_zpowers zH
    rw [← heq] at hzc
    exact hv1 (hfp v (MulAction.mem_stabilizer_iff.mp hzc.1))

private theorem tripleA6_isSylowTwoOf_map (hH : HatMod H) {T' : Subgroup ↥H}
    (hT'8 : Nat.card T' = 8) :
    CFSG.QuasithinUnique.IsSylowTwoOf (T'.map (QuotientGroup.mk' (Subgroup.center ↥H))) ⊤ := by
  obtain ⟨e⟩ := hH.quot
  have hTZ : T' ⊓ (QuotientGroup.mk' (Subgroup.center ↥H)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk']
    exact Subgroup.inf_eq_bot_of_coprime (by rw [hT'8, hH.center]; norm_num)
  have hQ : Nat.card (↥H ⧸ Subgroup.center ↥H) = 360 := by
    rw [Nat.card_congr e.toEquiv]
    exact H13.Orbit.card_alt6_eq
  refine ⟨le_top, (IsPGroup.of_card (n := 3) (by rw [hT'8]; norm_num)).map _, ?_⟩
  rw [show ((T'.map (QuotientGroup.mk' (Subgroup.center ↥H))).subgroupOf ⊤).index =
    (T'.map (QuotientGroup.mk' (Subgroup.center ↥H))).index from Subgroup.relIndex_top_right _]
  have := (T'.map (QuotientGroup.mk' (Subgroup.center ↥H))).index_mul_card
  rw [card_map_of_inf_ker_eq_bot _ hTZ, hT'8, hQ] at this
  omega

private theorem tripleA6_exists_stabilizer_not_mem_normalizer [Finite V]
    (hsq : ∀ v : V, v ^ 2 = 1) (h6 : TripleA6Six H ⊤ ⊥) {T : Subgroup (MulAut V)} (hTH : T ≤ H)
    (hT8 : Nat.card T = 8) {v : V} (hv1 : v ≠ 1) (hvT : v ∈ fixV T) :
    ∃ g ∈ H, g v = v ∧ g ∉ Subgroup.normalizer (T : Set (MulAut V)) := by
  have hH := HatMod.of_tripleA6Six hsq h6
  obtain ⟨e⟩ := hH.quot
  by_contra hcon
  push Not at hcon
  have hT'8 : Nat.card (T.subgroupOf H) = 8 := by
    rw [← hT8]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
  have hSN : MulAction.stabilizer ↥H v ≤
      Subgroup.normalizer ((T.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro g hg
    rw [← Subgroup.subgroupOf_normalizer_eq hTH, Subgroup.mem_subgroupOf]
    exact hcon g g.2 (MulAction.mem_stabilizer_iff.mp hg)
  have hker := QuotientGroup.ker_mk' (Subgroup.center ↥H)
  have hTZ : T.subgroupOf H ⊓ (QuotientGroup.mk' (Subgroup.center ↥H)).ker = ⊥ := by
    rw [hker]
    exact Subgroup.inf_eq_bot_of_coprime (by rw [hT'8, hH.center]; norm_num)
  have hSZ : MulAction.stabilizer ↥H v ⊓ (QuotientGroup.mk' (Subgroup.center ↥H)).ker = ⊥ := by
    rw [hker]
    exact tripleA6_stabilizer_inf_center_eq_bot hH hv1
  have hA6 := H13.Lem1227Eq.A6Syl.of_sylow e (tripleA6_isSylowTwoOf_map hH hT'8)
  have hle := (Subgroup.map_mono (f := QuotientGroup.mk' (Subgroup.center ↥H)) hSN).trans
    ((Subgroup.le_normalizer_map _).trans hA6.normalizer)
  have := Subgroup.card_le_of_le hle
  rw [card_map_of_inf_ker_eq_bot _ hSZ, card_map_of_inf_ker_eq_bot _ hTZ,
    tripleA6_card_stabilizer hsq h6 hTH hT8 hv1 hvT, hT'8] at this
  omega

private theorem tripleA6_inf_conj_ne_bot [Finite V] (hsq : ∀ v : V, v ^ 2 = 1)
    (h6 : TripleA6Six H ⊤ ⊥) {T : Subgroup (MulAut V)} (hTH : T ≤ H) (hT8 : Nat.card T = 8)
    {v : V} (hv1 : v ≠ 1) (hvT : v ∈ fixV T) {g : MulAut V} (hgH : g ∈ H) (hgv : g v = v) :
    T ⊓ T.map (MulAut.conj g).toMonoidHom ≠ ⊥ := by
  set Tg := T.map (MulAut.conj g).toMonoidHom with hTgdef
  have hTgH : Tg ≤ H := by
    rintro _ ⟨t, ht, rfl⟩
    exact H.mul_mem (H.mul_mem hgH (hTH ht)) (H.inv_mem hgH)
  have hcardOf : ∀ {A : Subgroup (MulAut V)}, A ≤ H → Nat.card (A.subgroupOf H) = Nat.card A :=
    fun hA => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  have hTg8 : Nat.card Tg = 8 := by
    rw [hTgdef, Subgroup.card_map_of_injective (MulAut.conj g).injective, hT8]
  have hvTg : v ∈ fixV Tg := by
    rw [hTgdef, fixV_map_conj_eq]
    exact ⟨v, hvT, hgv⟩
  have hS : ∀ {A : Subgroup (MulAut V)}, v ∈ fixV A →
      A.subgroupOf H ≤ MulAction.stabilizer ↥H v := fun hA t ht =>
    MulAction.mem_stabilizer_iff.mpr (hA (t : MulAut V) (Subgroup.mem_subgroupOf.mp ht))
  have hE := inf_ne_bot_of_card_eight (tripleA6_card_stabilizer hsq h6 hTH hT8 hv1 hvT)
    (by rw [hcardOf hTH, hT8]) (by rw [hcardOf hTgH, hTg8]) (hS hvT) (hS hvTg)
  intro h
  apply hE
  rw [eq_bot_iff]
  intro x hx
  have hx' : (x : MulAut V) ∈ T ⊓ Tg :=
    ⟨Subgroup.mem_subgroupOf.mp hx.1, Subgroup.mem_subgroupOf.mp hx.2⟩
  rw [h, Subgroup.mem_bot] at hx'
  exact Subgroup.mem_bot.mpr (Subtype.ext hx')

private theorem tripleA6_fixV_conj_eq [Finite V] (hsq : ∀ v : V, v ^ 2 = 1)
    (h6 : TripleA6Six H ⊤ ⊥) {T : Subgroup (MulAut V)} (hTH : T ≤ H) (hT8 : Nat.card T = 8)
    {v : V} (hv1 : v ≠ 1) (hvT : v ∈ fixV T) {g : MulAut V} (hgH : g ∈ H) (hgv : g v = v) :
    fixV (T.map (MulAut.conj g).toMonoidHom) = fixV T := by
  have hH := HatMod.of_tripleA6Six hsq h6
  obtain ⟨zH, hcen, h3, hfp⟩ := hH.exists_z
  have hzc : ∀ x ∈ H, x * (zH : MulAut V) = (zH : MulAut V) * x :=
    fun x hx => HatMod.comm_z_of_mem hcen hx
  set Tg := T.map (MulAut.conj g).toMonoidHom with hTgdef
  have hTgH : Tg ≤ H := by
    rintro _ ⟨t, ht, rfl⟩
    exact H.mul_mem (H.mul_mem hgH (hTH ht)) (H.inv_mem hgH)
  have hvTg : v ∈ fixV Tg := by
    rw [hTgdef, fixV_map_conj_eq]
    exact ⟨v, hvT, hgv⟩
  have hz : ∀ {A : Subgroup (MulAut V)}, A ≤ H → ∀ w ∈ fixV A, (zH : MulAut V) w ∈ fixV A :=
    fun hA w hw => HatMod.z_mem_fixV (fun b hb => hzc b (hA hb)) hw
  have hsupz : ∀ w ∈ fixV T ⊔ fixV Tg, (zH : MulAut V) w ∈ fixV T ⊔ fixV Tg := by
    intro w hw
    have hle : (fixV T ⊔ fixV Tg).map (zH : MulAut V).toMonoidHom ≤ fixV T ⊔ fixV Tg := by
      rw [Subgroup.map_sup]
      exact sup_le_sup (Subgroup.map_le_iff_le_comap.mpr fun u hu => hz hTH u hu)
        (Subgroup.map_le_iff_le_comap.mpr fun u hu => hz hTgH u hu)
    exact hle ⟨w, hw, rfl⟩
  have hE16 := hH.card_fixV_le h3 hfp (E := T ⊓ Tg)
    (fun b hb => hzc b (hTH (Subgroup.mem_inf.mp hb).1))
    (tripleA6_inf_conj_ne_bot hsq h6 hTH hT8 hv1 hvT hgH hgv)
  have hpq : Nat.card (fixV Tg) = Nat.card (fixV T) := by
    rw [hTgdef, fixV_map_conj_eq]
    exact Subgroup.card_map_of_injective g.injective
  refine eq_of_card_cases hpq (HatA6.card_cases_of_inv hH.card h3 hfp (S := fixV T ⊓ fixV Tg)
    fun w hw => ⟨hz hTH w hw.1, hz hTgH w hw.2⟩) (HatA6.card_cases_of_inv hH.card h3 hfp (hz hTH))
    (HatA6.card_cases_of_inv hH.card h3 hfp hsupz) (fun h1 => ?_)
    ((Subgroup.card_le_of_le (sup_le (fixV_anti inf_le_left) (fixV_anti inf_le_right))).trans hE16)
  have hmem : v ∈ fixV T ⊓ fixV Tg := ⟨hvT, hvTg⟩
  rw [Subgroup.eq_bot_of_card_eq _ h1, Subgroup.mem_bot] at hmem
  exact hv1 hmem

theorem tripleA6_natStab [Finite V] (hsq : ∀ v : V, v ^ 2 = 1) (h6 : TripleA6Six H ⊤ ⊥)
    {T : Subgroup (MulAut V)} (hTH : T ≤ H) (hT8 : Nat.card T = 8) :
    (∃ g ∈ H, (fixV T).map g.toMonoidHom = fixV T ∧
        g ∉ Subgroup.normalizer (T : Set (MulAut V))) ∧
      ∃ g ∈ H, ∃ w ∈ fixV T, g w ∉ fixV T := by
  have hH := HatMod.of_tripleA6Six hsq h6
  have : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hH.card]; norm_num)
  have hT2 : IsPGroup 2 ↥T := IsPGroup.of_card (n := 3) (by rw [hT8]; norm_num)
  obtain ⟨⟨v, hvT⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (MS93.S32.fixV_ne_bot_of_isPGroup hsq hT2)
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  obtain ⟨g, hgH, hgv, hgN⟩ :=
    tripleA6_exists_stabilizer_not_mem_normalizer hsq h6 hTH hT8 hv1' hvT
  refine ⟨⟨g, hgH, ?_, hgN⟩, ?_⟩
  · rw [← fixV_map_conj_eq]
    exact tripleA6_fixV_conj_eq hsq h6 hTH hT8 hv1' hvT hgH hgv
  by_contra hcon
  push Not at hcon
  rcases hH.irr (fixV T) hcon with h | h
  · rw [h] at hvT
    exact hv1' (Subgroup.mem_bot.mp hvT)
  · have hbot : T = ⊥ := by
      rw [eq_bot_iff]
      intro t ht
      rw [Subgroup.mem_bot]
      exact MulEquiv.ext fun w => (h ▸ Subgroup.mem_top w : w ∈ fixV T) t ht
    rw [hbot, Subgroup.card_bot] at hT8
    omega

section ActionModel

variable {D : FFModel} (hA : D.IsActionModel)

private theorem modAct_mk_eq_iff (γ : D.Gam) {m : D.Amb} (hm : m ∈ D.sec) :
    hA.modAct γ (QuotientGroup.mk ⟨m, hm⟩ : D.Mod) = QuotientGroup.mk ⟨m, hm⟩ ↔
      D.act γ m * m⁻¹ ∈ D.ker := by
  rw [FFModel.IsActionModel.modAct_apply, FFModel.IsActionModel.modEnd_mk, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  change (D.act γ m)⁻¹ * m ∈ D.ker ↔ _
  constructor
  · intro h
    have := D.ker.inv_mem h
    simpa [mul_comm] using this
  · intro h
    have := D.ker.inv_mem h
    simpa [mul_comm] using this

private theorem isGomiModelFix_iff_mem_fixV (T₀ : Subgroup D.Gam) {m : D.Amb} (hm : m ∈ D.sec) :
    IsGomiModelFix D T₀ m ↔ (QuotientGroup.mk ⟨m, hm⟩ : D.Mod) ∈ fixV (T₀.map hA.modAct) := by
  constructor
  · rintro h _ ⟨t, ht, rfl⟩
    exact (modAct_mk_eq_iff hA t hm).mpr (h t ht)
  · intro h t ht
    exact (modAct_mk_eq_iff hA t hm).mp (h _ ⟨t, ht, rfl⟩)

private theorem modAct_injective (hD : D.Faithful) : Function.Injective hA.modAct := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro γ hγ
  rw [Subgroup.mem_bot]
  refine hD γ fun m hm => (modAct_mk_eq_iff hA γ hm).mp ?_
  rw [MonoidHom.mem_ker.mp hγ]
  rfl

private theorem gomiNatStabModel_of_modAct (hD : D.Faithful) (T₀ : Sylow 2 D.Gam)
    (h₁ : ∃ x ∈ hA.modAct.range,
      (fixV ((T₀ : Subgroup D.Gam).map hA.modAct)).map x.toMonoidHom =
          fixV ((T₀ : Subgroup D.Gam).map hA.modAct) ∧
        x ∉ Subgroup.normalizer
          (((T₀ : Subgroup D.Gam).map hA.modAct : Subgroup (MulAut D.Mod)) : Set (MulAut D.Mod)))
    (h₂ : ∃ x ∈ hA.modAct.range, ∃ w ∈ fixV ((T₀ : Subgroup D.Gam).map hA.modAct),
      x w ∉ fixV ((T₀ : Subgroup D.Gam).map hA.modAct)) :
    GomiNatStabModel D := by
  obtain ⟨_, ⟨γ, rfl⟩, hfix, hN⟩ := h₁
  obtain ⟨_, ⟨γ', rfl⟩, w, hw, hmove⟩ := h₂
  obtain ⟨⟨m, hm⟩, rfl⟩ := QuotientGroup.mk_surjective w
  refine ⟨hD, T₀, γ, γ', m, fun h => hN (Subgroup.le_normalizer_map hA.modAct ⟨γ, h, rfl⟩),
    fun m' hm' hf => ?_, hm, (isGomiModelFix_iff_mem_fixV hA _ hm).mpr hw, fun h => hmove ?_⟩
  · rw [isGomiModelFix_iff_mem_fixV hA _ (hA.sec_inv γ m' hm'), ← hfix]
    exact ⟨_, (isGomiModelFix_iff_mem_fixV hA _ hm').mp hf, rfl⟩
  · exact (isGomiModelFix_iff_mem_fixV hA _ (hA.sec_inv γ' m hm)).mp h

end ActionModel

private theorem card_sylow_two_of_card_eq_1080 {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 1080) (P : Sylow 2 G) : Nat.card (P : Subgroup G) = 8 := by
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hmul := (P : Subgroup G).card_mul_index
  have hidx := P.not_dvd_index
  have hi : (P : Subgroup G).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [hn, hG] at hmul
  rw [hn]
  have hn11 : n < 11 := by
    by_contra h
    have : 2 ^ 11 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ n ≤ 2 ^ n * (P : Subgroup G).index := Nat.le_mul_of_pos_right _ (by omega)
    omega
  interval_cases n <;> norm_num at hmul ⊢ <;> omega

theorem gomiNatStabModel_tripleA6 {K : Type} [Field K] [Finite K]
    {Γ₀ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)} (hK : Nat.card K = 4)
    (hdet : ∀ g ∈ Γ₀,
      ((g : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hhat : IsHat ↥Γ₀ ↥(alternatingGroup (Fin 6)))
    (hcen : ∀ g ∈ Subgroup.center ↥Γ₀, ∃ c : K,
      (((g : ↥Γ₀) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1) :
    GomiNatStabModel (FFModel.nat Γ₀) := by
  have hA := FFModel.nat_isActionModel Γ₀
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    (k := 2) Nat.prime_two (by norm_num) (by rw [hK]; norm_num)
  have h6 : TripleA6Six hA.modAct.range ⊤ ⊥ :=
    ⟨K, inferInstance, inferInstance, Γ₀, hK, hdet, hhat, hcen, hA.realizesMod_range⟩
  have hsqA : ∀ x : Multiplicative (Fin 3 → K), x ^ 2 = 1 := fun x => by
    rw [pow_two]
    exact congrArg Multiplicative.ofAdd
      (funext fun i => CharTwo.add_self_eq_zero (Multiplicative.toAdd x i))
  have hsq : ∀ v : (FFModel.nat Γ₀).Mod, v ^ 2 = 1 := fun v => by
    induction v using QuotientGroup.induction_on with
    | H m =>
      rw [← QuotientGroup.mk_pow, show m ^ 2 = 1 from Subtype.ext (hsqA (m : (FFModel.nat Γ₀).Amb)),
        QuotientGroup.mk_one]
  have : Finite (FFModel.nat Γ₀).Mod := (HatMod.of_tripleA6Six hsq h6).finite
  have hΓ : Nat.card (FFModel.nat Γ₀).Gam = 1080 :=
    (HatA6.quasisimple_card hhat.1.1 hhat.2.1 hhat.2.2.some).2
  have : Finite (FFModel.nat Γ₀).Gam := Nat.finite_of_card_ne_zero (by rw [hΓ]; norm_num)
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 (FFModel.nat Γ₀).Gam) := inferInstance
  have hT8 : Nat.card ((T₀ : Subgroup (FFModel.nat Γ₀).Gam).map hA.modAct) = 8 := by
    rw [Subgroup.card_map_of_injective (modAct_injective hA (FFModel.nat_faithful Γ₀))]
    exact card_sylow_two_of_card_eq_1080 hΓ T₀
  obtain ⟨h₁, h₂⟩ := tripleA6_natStab hsq h6 (Subgroup.map_le_range _ _) hT8
  exact gomiNatStabModel_of_modAct hA (FFModel.nat_faithful Γ₀) T₀ h₁ h₂

end CFSG.GroupTheory

end
