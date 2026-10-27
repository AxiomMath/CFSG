module

public import CFSG.GH74.Generic.BProg.B1.Lift0
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.Generic.BProg.B1.PilotS1Facts

public section

namespace CFSG.GH74.Generic.BProg.B3.S1SplitAux

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  Subgroup
open CFSG.GH74.Generic.BProg.B1.PilotS5 CFSG.GH74.Generic.BProg.B1.PilotS3
open CFSG.GH74.Generic.BProg.B1.PilotS1
open scoped MatrixGroups commutatorElement
open CFSG.ComponentClassification

section R

variable {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] {Y : Subgroup X}
  {z u : X} {J₁ J₂ : Subgroup X}

theorem eq_or_eq_of_isPCompIn (hodd : Odd (Nat.card F)) (hbig : 4 ≤ Nat.card F)
    (h : SplitAt F Y z u J₁ J₂) {L' : Subgroup X}
    (hL' : IsPCompIn 2 (centralizer ({u} : Set X) ⊓ Y) L') : L' = J₁ ∨ L' = J₂ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup X := centralizer ({u} : Set X) ⊓ Y with hH
  have hJ₁H : J₁ ≤ H := h.le₁
  have hJ₂H : J₂ ≤ H := h.le₂
  have hLH : L' ≤ H := hL'.1
  set Lg : Subgroup ↥H := L'.subgroupOf H with hLg
  set A₁ : Subgroup ↥H := J₁.subgroupOf H with hA₁
  set A₂ : Subgroup ↥H := J₂.subgroupOf H with hA₂
  have hLgc : IsPComponent 2 Lg := hL'.2
  have hA₁c : IsPComponent 2 A₁ := (h.isPCompIn₁ hodd hbig).2
  have hA₂c : IsPComponent 2 A₂ := (h.isPCompIn₂ hodd hbig).2
  obtain ⟨e₁⟩ := h.equiv₁
  obtain ⟨e₂⟩ := h.equiv₂
  have e₁' : ↥A₁ ≃* SL(2, F) := (Subgroup.subgroupOfEquivOfLe hJ₁H).trans e₁
  have e₂' : ↥A₂ ≃* SL(2, F) := (Subgroup.subgroupOfEquivOfLe hJ₂H).trans e₂
  have hq₁ : IsQuasisimple ↥A₁ := isQuasisimple_of_equiv_sl2 hbig e₁'
  have hq₂ : IsQuasisimple ↥A₂ := isQuasisimple_of_equiv_sl2 hbig e₂'
  by_contra hcon
  push Not at hcon
  have hne₁ : A₁ ≠ Lg := fun heq =>
    hcon.1 (Subgroup.subgroupOf_inj.1 heq.symm |> fun h' => by
      rwa [inf_of_le_left hLH, inf_of_le_left hJ₁H] at h')
  have hne₂ : A₂ ≠ Lg := fun heq =>
    hcon.2 (Subgroup.subgroupOf_inj.1 heq.symm |> fun h' => by
      rwa [inf_of_le_left hLH, inf_of_le_left hJ₂H] at h')
  have hc₁ : ⁅A₁, Lg⁆ = ⊥ :=
    CatalogueBPrimeJoin.commutes_of_quasisimple 2 A₁ Lg hA₁c hLgc hne₁ (Or.inl hq₁)
  have hc₂ : ⁅A₂, Lg⁆ = ⊥ :=
    CatalogueBPrimeJoin.commutes_of_quasisimple 2 A₂ Lg hA₂c hLgc hne₂ (Or.inl hq₂)
  have hA₁₂ : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := fun a ha b hb =>
    Subtype.ext (h.commute a ha b hb)
  have hperf : ⁅Lg, Lg⁆ = Lg :=
    Subgroup.isPerfect_iff.1
      (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hLgc)
  have hLY : Lg ≤ A₁ ⊔ A₂ := by
    have h2 : ⁅Lg, Lg⁆ ≤ A₁ ⊔ A₂ := by
      rw [Subgroup.commutator_le]
      intro g₁ _ g₂ _
      obtain ⟨j₁, hj₁, j₂, hj₂, hjj⟩ := mem_sup_of_commute h.commute
        (h.comm (g₁ : X) g₁.2.2 (g₂ : X) g₂.2.2 (Subgroup.mem_centralizer_singleton_iff.1 g₁.2.1)
          (Subgroup.mem_centralizer_singleton_iff.1 g₂.2.1))
      have : ⁅g₁, g₂⁆ = (⟨j₁, hJ₁H hj₁⟩ : ↥H) * ⟨j₂, hJ₂H hj₂⟩ := Subtype.ext hjj
      rw [this]
      exact Subgroup.mul_mem_sup hj₁ hj₂
    rwa [hperf] at h2
  have hcent₁ : ∀ a ∈ A₁, ∀ g ∈ Lg, a * g = g * a := fun a ha g hg =>
    (Subgroup.mem_centralizer_iff.1
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc₁ ha) g hg).symm
  have hcent₂ : ∀ a ∈ A₂, ∀ g ∈ Lg, a * g = g * a := fun a ha g hg =>
    (Subgroup.mem_centralizer_iff.1
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc₂ ha) g hg).symm
  have habel : ∀ g ∈ Lg, ∀ g' ∈ Lg, g * g' = g' * g := by
    intro g hg g' hg'
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute hA₁₂ (hLY hg)
    rw [mul_assoc, hcent₂ a₂ ha₂ g' hg', ← mul_assoc, hcent₁ a₁ ha₁ g' hg', mul_assoc]
  obtain ⟨Kb, hKb, -, hmap, -⟩ := hLgc
  have hab : ∀ k ∈ Kb, ∀ k' ∈ Kb, k * k' = k' * k := by
    intro k hk k' hk'
    rw [← hmap] at hk hk'
    obtain ⟨g, hg, rfl⟩ := hk
    obtain ⟨g', hg', rfl⟩ := hk'
    rw [← map_mul, ← map_mul, habel g hg g' hg']
  obtain ⟨-, -, a', b', hab'⟩ := hKb.1
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
  have hba : a * b = b * a := Subtype.ext (hab a a.2 b b.2)
  exact hab' (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hba])

end R


section Swap

variable {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] {Y : Subgroup X} {z u : X}
  {J₁ J₂ : Subgroup X}

theorem invol_swap (hodd : Odd (Nat.card F)) (hbig : 4 ≤ Nat.card F) (hY : Split1Like F Y z)
    (h : SplitAt F Y z u J₁ J₂) (hu : u ∈ Y) (huz : u ≠ z) :
    ∀ d ∈ Y, d * d = 1 → (∀ j ∈ J₂, d * j = j * d) → d = 1 ∨ d = z ∨ d = u ∨ d = z * u := by
  have hz2 : orderOf z = 2 := hY.z_ord
  have hzc : ∀ g ∈ Y, g * z = z * g := hY.z_central
  have hu2 : orderOf u = 2 := h.ord
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2]; exact pow_orderOf_eq_one z
  have huu : u * u = 1 := by rw [← pow_two, ← hu2]; exact pow_orderOf_eq_one u
  have hzu_mem : z * u ∈ Y := Y.mul_mem hY.z_mem hu
  have hcomm : z * u = u * z := (hzc u hu).symm
  have hzu2 : (z * u) * (z * u) = 1 := by
    calc (z * u) * (z * u) = z * (u * z) * u := by group
      _ = z * (z * u) * u := by rw [← hcomm]
      _ = (z * z) * (u * u) := by group
      _ = 1 := by rw [hzz, huu, one_mul]
  have hzu1 : z * u ≠ 1 := by
    intro h1
    apply huz
    have : u = z⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this, inv_eq_of_mul_eq_one_right hzz]
  have hzu : orderOf (z * u) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzu2) hzu1
  have hzuz : z * u ≠ z := fun h1 => by
    have : u = 1 := by simpa using h1
    rw [this, orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  obtain ⟨J₁', J₂', h'⟩ := hY.split (z * u) hzu_mem hzu hzuz
  have hc : centralizer ({z * u} : Set X) ⊓ Y = centralizer ({u} : Set X) ⊓ Y :=
    hY.centralizer_mul_eq u
  have hJ₁' : IsPCompIn 2 (centralizer ({u} : Set X) ⊓ Y) J₁' := by
    rw [← hc]; exact h'.isPCompIn₁ hodd hbig
  intro d hd hdd hdj
  rcases eq_or_eq_of_isPCompIn hodd hbig h hJ₁' with h1 | h1
  · exfalso
    have hm1 : z * u ∈ J₁ := h1 ▸ h'.u_mem
    exact hzu1 (Subgroup.disjoint_def.1 h.disj hm1 h.zu_mem)
  · rcases h'.invol d hd hdd (fun j hj => hdj j (h1 ▸ hj)) with h2 | h2 | h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inr h2))
    · refine Or.inr (Or.inr (Or.inl ?_))
      rw [h2, ← mul_assoc, hzz, one_mul]

end Swap


section Coprime

theorem exists_commuting_lift {K' : Type} {Q : Type*} [Group K'] [Finite K'] [Group Q] (f : K' →* Q)
    (hker : Odd (Nat.card f.ker)) {t : K'} (ht : orderOf t = 2) {c : Q} (hc : c ∈ f.range)
    (hct : c * f t = f t * c) : ∃ g : K', f g = c ∧ g * t = t * g := by
  classical
  obtain ⟨g₀, rfl⟩ := hc
  have key : ∀ a ∈ zpowers t, QuotientGroup.mk' f.ker a * QuotientGroup.mk' f.ker g₀ =
      QuotientGroup.mk' f.ker g₀ * QuotientGroup.mk' f.ker a := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← map_mul, ← map_mul]
    refine QuotientGroup.eq.2 ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_zpow, inv_mul_eq_one]
    exact (Commute.zpow_right hct k).eq.symm
  obtain ⟨g, hg1, hg2⟩ := B1.centralizer_quotient_of_pGroup f.ker hker (A := zpowers t)
    (B1.isPGroup_two_zpowers_of_orderOf ht) key
  refine ⟨g, ?_, (hg2 t (Subgroup.mem_zpowers t)).symm⟩
  have h1 := QuotientGroup.eq.1 hg1
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

theorem map_pPrimeCore_eq_one {A B : Type*} [Group A] [Finite A] [Group B] [Finite B] (ρ : A →* B)
    (hρ : Function.Surjective ρ) (hq : IsQuasisimple B) (hZ : Nat.card ↥(center B) = 2) :
    ∀ o ∈ pPrimeCore 2 A, ρ o = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ((pPrimeCore 2 A).map ρ).Normal := Subgroup.Normal.map inferInstance ρ hρ
  have hodd : ∀ o ∈ pPrimeCore 2 A, Odd (orderOf o) := fun o ho => by
    have hdvd : orderOf o ∣ Nat.card (pPrimeCore 2 A) := Subgroup.orderOf_dvd_natCard _ ho
    exact Nat.coprime_two_left.1
      ((CFSG.pPrimeCore_coprime_card (p := 2) (G := A)).coprime_dvd_right hdvd)
  have hoddρ : ∀ o ∈ pPrimeCore 2 A, Odd (orderOf (ρ o)) := fun o ho =>
    Odd.of_dvd_nat (hodd o ho) (orderOf_map_dvd ρ o)
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq hN with htop | hcen
  · exfalso
    have h2 : 2 ∣ Nat.card ↥(center B) := by rw [hZ]
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center B)) 2 h2
    have hzN : (z : B) ∈ (pPrimeCore 2 A).map ρ := by rw [htop]; trivial
    obtain ⟨o, ho, hoz⟩ := hzN
    have := hoddρ o ho
    rw [hoz, Subgroup.orderOf_coe, hz] at this
    exact absurd this (by decide)
  · intro o ho
    have hmc : ρ o ∈ center B := hcen ⟨o, ho, rfl⟩
    have h1 : orderOf (ρ o) ∣ 2 := by
      have := Subgroup.orderOf_dvd_natCard (center B) hmc
      rwa [hZ] at this
    have h2 := hoddρ o ho
    have : orderOf (ρ o) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
      · exact h
      · rw [h] at h2; exact absurd h2 (by decide)
    exact orderOf_eq_one_iff.1 this

end Coprime


section Lift

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q] (Hg : Subgroup G) (φ : ↥Hg →* Q)

@[expose] def liftComp (Jb : Subgroup Q) : Subgroup G :=
  oPrimeResidualOf 2 ((Jb.comap φ).map Hg.subtype)

variable {Hg φ}

theorem not_two_dvd_of_odd {n : ℕ} (h : Odd n) : ¬ 2 ∣ n := fun h2 =>
  (Nat.not_even_iff_odd.2 h) (even_iff_two_dvd.2 h2)

omit [Finite G] in
theorem liftComp_le (Jb : Subgroup Q) : liftComp Hg φ Jb ≤ Hg :=
  (Balance.oPrimeResidualOf_le_self _).trans (Subgroup.map_subtype_le _)

theorem isPCompIn_liftComp (hker : Odd (Nat.card φ.ker)) {Jb : Subgroup Q}
    (hJb : IsPCompIn 2 φ.range Jb) : IsPCompIn 2 Hg (liftComp Hg φ Jb) :=
  (B1.exists_isPCompIn_lift_of_odd_ker φ (not_two_dvd_of_odd hker) hJb).1

theorem map_liftComp (hker : Odd (Nat.card φ.ker)) {Jb : Subgroup Q}
    (hJb : IsPCompIn 2 φ.range Jb) : ((liftComp Hg φ Jb).subgroupOf Hg).map φ = Jb :=
  (B1.exists_isPCompIn_lift_of_odd_ker φ (not_two_dvd_of_odd hker) hJb).2

omit [Finite G] in
theorem mem_liftComp {h : G} (hh : h ∈ Hg) {Jb : Subgroup Q} (hJ : φ ⟨h, hh⟩ ∈ Jb)
    (h2 : h * h = 1) : h ∈ liftComp Hg φ Jb :=
  Balance.mem_oPrimeResidualOf_of_two_element ⟨⟨h, hh⟩, hJ, rfl⟩
    ⟨1, by rw [pow_one, pow_two]; exact h2⟩

omit [Finite G] in
theorem mem_normalizer_liftComp {g : G} (hg : g ∈ Hg) {Jb : Subgroup Q}
    (hn : φ ⟨g, hg⟩ ∈ normalizer (Jb : Set Q)) : g ∈ normalizer (liftComp Hg φ Jb : Set G) := by
  have key : ∀ (g : G) (hg : g ∈ Hg), φ ⟨g, hg⟩ ∈ normalizer (Jb : Set Q) →
      ∀ y ∈ liftComp Hg φ Jb, g * y * g⁻¹ ∈ liftComp Hg φ Jb := by
    intro g hg hn y hy
    set V : Subgroup G := (Jb.comap φ).map Hg.subtype with hV
    have hle : V.map (MulAut.conj g).toMonoidHom ≤ V := by
      rintro _ ⟨v, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨⟨g, hg⟩ * w * ⟨g, hg⟩⁻¹, ?_, rfl⟩
      show φ (⟨g, hg⟩ * w * ⟨g, hg⟩⁻¹) ∈ Jb
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hn (φ w)).1 hw
    have h1 : (oPrimeResidualOf 2 V).map (MulAut.conj g).toMonoidHom ≤
        oPrimeResidualOf 2 (V.map (MulAut.conj g).toMonoidHom) :=
      Balance.map_oPrimeResidualOf_le _ V
    have h2 : oPrimeResidualOf 2 (V.map (MulAut.conj g).toMonoidHom) ≤ oPrimeResidualOf 2 V :=
      Balance.oPrimeResidualOf_le_of_two_elements fun v hv h2 =>
        Balance.mem_oPrimeResidualOf_of_two_element (hle hv) h2
    exact h2 (h1 ⟨y, hy, rfl⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key g hg hn y hy, fun hy => ?_⟩
  have hn' : φ ⟨g⁻¹, Hg.inv_mem hg⟩ ∈ normalizer (Jb : Set Q) := by
    have : (⟨g⁻¹, Hg.inv_mem hg⟩ : ↥Hg) = ⟨g, hg⟩⁻¹ := rfl
    rw [this, map_inv]
    exact Subgroup.inv_mem _ hn
  have := key g⁻¹ (Hg.inv_mem hg) hn' _ hy
  simpa [mul_assoc] using this

variable [Fact (Nat.Prime 2)]

theorem isPCompIn_map (hker : Odd (Nat.card φ.ker)) {L : Subgroup G} (hL : IsPCompIn 2 Hg L) :
    IsPCompIn 2 φ.range ((L.subgroupOf Hg).map φ) := by
  have : Finite ↥φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  set f : ↥Hg →* ↥φ.range := φ.rangeRestrict with hf
  have hfk : ¬ 2 ∣ Nat.card f.ker := by
    rw [hf, MonoidHom.ker_rangeRestrict]; exact not_two_dvd_of_odd hker
  have hbij := (CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    (p := 2) f φ.rangeRestrict_surjective hfk).1
  have h1 : IsPComponent 2 ((L.subgroupOf Hg).map f) := hbij.mapsTo hL.2
  refine ⟨?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  · have : ((L.subgroupOf Hg).map φ).subgroupOf φ.range = (L.subgroupOf Hg).map f := by
      ext ⟨q, hq⟩
      constructor
      · rintro ⟨y, hy, hyq⟩
        exact ⟨y, hy, Subtype.ext hyq⟩
      · rintro ⟨y, hy, hyq⟩
        exact ⟨y, hy, congrArg Subtype.val hyq⟩
    rw [this]
    exact h1

theorem eq_of_map_eq (hker : Odd (Nat.card φ.ker)) {L L' : Subgroup G} (hL : IsPCompIn 2 Hg L)
    (hL' : IsPCompIn 2 Hg L')
    (h : (L.subgroupOf Hg).map φ = (L'.subgroupOf Hg).map φ) : L = L' := by
  have : Finite ↥φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  set f : ↥Hg →* ↥φ.range := φ.rangeRestrict with hf
  have hfk : ¬ 2 ∣ Nat.card f.ker := by
    rw [hf, MonoidHom.ker_rangeRestrict]; exact not_two_dvd_of_odd hker
  have hbij := (CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    (p := 2) f φ.rangeRestrict_surjective hfk).1
  have hφ : φ = φ.range.subtype.comp f := rfl
  have h2 : (L.subgroupOf Hg).map f = (L'.subgroupOf Hg).map f := by
    apply Subgroup.map_injective (Subgroup.subtype_injective φ.range)
    rw [Subgroup.map_map, Subgroup.map_map, ← hφ]
    exact h
  have h3 := hbij.injOn hL.2 hL'.2 h2
  have h4 := Subgroup.subgroupOf_inj.1 h3
  rwa [inf_of_le_left hL.1, inf_of_le_left hL'.1] at h4

end Lift


section Sl2

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q] {Hg : Subgroup G} {φ : ↥Hg →* Q}
  {F : Type} [Field F] [Finite F]

@[expose] def rhoOf (Jb : Subgroup Q) : ↥(liftComp Hg φ Jb) →* Q :=
  φ.comp (Subgroup.inclusion (liftComp_le Jb))

theorem range_rhoOf (hker : Odd (Nat.card φ.ker)) {Jb : Subgroup Q} (hJb : IsPCompIn 2 φ.range Jb) :
    (rhoOf (Hg := Hg) (φ := φ) Jb).range = Jb := by
  have hm := map_liftComp hker hJb
  ext q
  constructor
  · rintro ⟨y, rfl⟩
    have : rhoOf (Hg := Hg) (φ := φ) Jb y ∈ ((liftComp Hg φ Jb).subgroupOf Hg).map φ :=
      ⟨Subgroup.inclusion (liftComp_le (Hg := Hg) (φ := φ) Jb) y, y.2, rfl⟩
    rwa [hm] at this
  · intro hq
    rw [← hm] at hq
    obtain ⟨y, hy, rfl⟩ := hq
    exact ⟨⟨y.1, hy⟩, rfl⟩

omit [Finite G] in
theorem card_ker_rhoOf_odd (hker : Odd (Nat.card φ.ker)) (Jb : Subgroup Q) :
    Nat.Coprime 2 (Nat.card (rhoOf (Hg := Hg) (φ := φ) Jb).ker) := by
  have hk : (rhoOf (Hg := Hg) (φ := φ) Jb).ker =
      φ.ker.comap (Subgroup.inclusion (liftComp_le (Hg := Hg) (φ := φ) Jb)) := by
    rw [rhoOf, ← MonoidHom.comap_ker]
  rw [hk]
  have hdvd := Subgroup.card_comap_dvd_of_injective φ.ker
    (Subgroup.inclusion (liftComp_le (Hg := Hg) (φ := φ) Jb))
    (Subgroup.inclusion_injective _)
  exact (Nat.coprime_two_left.2 hker).coprime_dvd_right hdvd

theorem pPrimeCore_liftComp_eq_ker (hker : Odd (Nat.card φ.ker)) {Jb : Subgroup Q}
    (hJb : IsPCompIn 2 φ.range Jb) (e : ↥Jb ≃* SL(2, F)) (hodd : Odd (Nat.card F))
    (hbig : 4 ≤ Nat.card F) :
    pPrimeCore 2 ↥(liftComp Hg φ Jb) = (rhoOf (Hg := Hg) (φ := φ) Jb).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ : ↥(liftComp Hg φ Jb) →* Q := rhoOf (Hg := Hg) (φ := φ) Jb with hρ
  have : Finite ↥ρ.range := Finite.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hrange := range_rhoOf hker hJb
  have e' : ↥ρ.range ≃* SL(2, F) := (MulEquiv.subgroupCongr hrange).trans e
  have hq := isQuasisimple_of_equiv_sl2 hbig e'
  have hZ := CFSG.ClassicalInvolution.natCard_center_of_equiv_sl2 hodd e'
  apply le_antisymm
  · intro o ho
    have := map_pPrimeCore_eq_one ρ.rangeRestrict ρ.rangeRestrict_surjective hq hZ o ho
    exact congrArg Subtype.val this
  · intro k hk
    have hnorm : ρ.ker.Normal := inferInstance
    exact le_sSup (show ρ.ker ∈ {K : Subgroup ↥(liftComp Hg φ Jb) |
        K.Normal ∧ Nat.Coprime 2 (Nat.card K)} from
      ⟨hnorm, card_ker_rhoOf_odd hker Jb⟩) hk

theorem quot_liftComp_equiv (hker : Odd (Nat.card φ.ker)) {Jb : Subgroup Q}
    (hJb : IsPCompIn 2 φ.range Jb) (e : ↥Jb ≃* SL(2, F)) (hodd : Odd (Nat.card F))
    (hbig : 4 ≤ Nat.card F) :
    Nonempty (↥(liftComp Hg φ Jb) ⧸ pPrimeCore 2 ↥(liftComp Hg φ Jb) ≃* SL(2, F)) := by
  have hc := pPrimeCore_liftComp_eq_ker hker hJb e hodd hbig
  have hrange := range_rhoOf hker hJb
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
    ((QuotientGroup.quotientKerEquivRange _).trans ((MulEquiv.subgroupCongr hrange).trans e))⟩

theorem map_pPrimeCoreOf_liftComp (hker : Odd (Nat.card φ.ker)) {Jb : Subgroup Q}
    (hJb : IsPCompIn 2 φ.range Jb) (e : ↥Jb ≃* SL(2, F)) (hodd : Odd (Nat.card F))
    (hbig : 4 ≤ Nat.card F) {o : G} (ho : o ∈ pPrimeCoreOf 2 (liftComp Hg φ Jb))
    (hoH : o ∈ Hg) : φ ⟨o, hoH⟩ = 1 := by
  obtain ⟨o', ho', rfl⟩ := ho
  have h1 : o' ∈ (rhoOf (Hg := Hg) (φ := φ) Jb).ker := by
    rw [← pPrimeCore_liftComp_eq_ker hker hJb e hodd hbig]; exact ho'
  exact h1

end Sl2


section Components

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q] {Hg : Subgroup G} {φ : ↥Hg →* Q}

theorem eq_liftComp_or [Fact (Nat.Prime 2)] (hker : Odd (Nat.card φ.ker)) {Jb₁ Jb₂ : Subgroup Q}
    (h₁ : IsPCompIn 2 φ.range Jb₁) (h₂ : IsPCompIn 2 φ.range Jb₂)
    (hall : ∀ M : Subgroup Q, IsPCompIn 2 φ.range M → M = Jb₁ ∨ M = Jb₂) {L : Subgroup G}
    (hL : IsPCompIn 2 Hg L) : L = liftComp Hg φ Jb₁ ∨ L = liftComp Hg φ Jb₂ := by
  rcases hall _ (isPCompIn_map hker hL) with h | h
  · exact Or.inl (eq_of_map_eq hker hL (isPCompIn_liftComp hker h₁)
      (h.trans (map_liftComp hker h₁).symm))
  · exact Or.inr (eq_of_map_eq hker hL (isPCompIn_liftComp hker h₂)
      (h.trans (map_liftComp hker h₂).symm))

theorem pLayerOf_eq_sup [Fact (Nat.Prime 2)] (hker : Odd (Nat.card φ.ker)) {Jb₁ Jb₂ : Subgroup Q}
    (h₁ : IsPCompIn 2 φ.range Jb₁) (h₂ : IsPCompIn 2 φ.range Jb₂)
    (hall : ∀ M : Subgroup Q, IsPCompIn 2 φ.range M → M = Jb₁ ∨ M = Jb₂) :
    pLayerOf 2 Hg = liftComp Hg φ Jb₁ ⊔ liftComp Hg φ Jb₂ := by
  refine le_antisymm (sSup_le fun L hL => ?_)
    (sup_le (le_sSup (isPCompIn_liftComp hker h₁)) (le_sSup (isPCompIn_liftComp hker h₂)))
  rcases eq_liftComp_or hker h₁ h₂ hall hL with h | h
  · rw [h]; exact le_sup_left
  · rw [h]; exact le_sup_right

omit [Finite G] in
theorem mem_pPrimeCoreOf_of_subgroupOf {J H : Subgroup G} (hJH : J ≤ H) {g : G} (hgH : g ∈ H)
    (hg : (⟨g, hgH⟩ : ↥H) ∈ (pPrimeCore 2 ↥(J.subgroupOf H)).map (J.subgroupOf H).subtype) :
    g ∈ pPrimeCoreOf 2 J := by
  obtain ⟨o, ho, hoe⟩ := hg
  let e : ↥(J.subgroupOf H) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJH
  have h1 : e o ∈ pPrimeCore 2 ↥J := by
    rw [← pPrimeCore_map_iso 2 e]
    exact ⟨o, ho, rfl⟩
  refine ⟨e o, h1, ?_⟩
  have := congrArg Subtype.val hoe
  exact this

end Components

section Commutator

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_of_norm {Y : Subgroup G} {u c : G} {J : Subgroup G}
    (hn : ∀ a ∈ Y, a * u = u * a → ∀ j ∈ J, a * j * a⁻¹ ∈ J) (hc : c ∈ Y) (hcu : c * u = u * c) :
    c ∈ normalizer (J : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hn c hc hcu y hy, fun hy => ?_⟩
  have hcu' : c⁻¹ * u = u * c⁻¹ := by
    calc c⁻¹ * u = c⁻¹ * (u * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * u) * c⁻¹ := by rw [hcu]
      _ = u * c⁻¹ := by group
  have := hn c⁻¹ (Y.inv_mem hc) hcu' _ hy
  simpa [mul_assoc] using this

theorem commutator_mem_cores {H J₁ J₂ : Subgroup G} (h₁ : IsPCompIn 2 H J₁) (h₂ : IsPCompIn 2 H J₂)
    (hne : J₁ ≠ J₂) : ∀ g ∈ J₁, ∀ h ∈ J₂, ⁅g, h⁆ ∈ pPrimeCoreOf 2 J₁ ⊓ pPrimeCoreOf 2 J₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g hg h hh
  have hne' : J₁.subgroupOf H ≠ J₂.subgroupOf H := fun heq => by
    have := Subgroup.subgroupOf_inj.1 heq
    rw [inf_of_le_left h₁.1, inf_of_le_left h₂.1] at this
    exact hne this
  have hmain := (CatalogueBPrimeJoin.distinct_p_components_core_commutation
    2 Nat.prime_two (J₁.subgroupOf H) (J₂.subgroupOf H) h₁.2 h₂.2).2 hne'
  have hgA : (⟨g, h₁.1 hg⟩ : ↥H) ∈ J₁.subgroupOf H := hg
  have hhA : (⟨h, h₂.1 hh⟩ : ↥H) ∈ J₂.subgroupOf H := hh
  have hmem := hmain.2.2.1 (Subgroup.commutator_mem_commutator hgA hhA)
  have hcH : ⁅g, h⁆ ∈ H := by
    have := (⁅(⟨g, h₁.1 hg⟩ : ↥H), ⟨h, h₂.1 hh⟩⁆ : ↥H).2
    exact this
  exact ⟨mem_pPrimeCoreOf_of_subgroupOf h₁.1 hcH hmem.1,
    mem_pPrimeCoreOf_of_subgroupOf h₂.1 hcH hmem.2⟩

end Commutator

end CFSG.GH74.Generic.BProg.B3.S1SplitAux
