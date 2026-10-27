module

public import CFSG.CGT.PushingUpLit.LIT.A4.Pair
public import CFSG.CGT.PushingUpLit.LIT.A4.Leaves
public import CFSG.CGT.PushingUpLit.LIT.A4.Unique

public section

namespace CFSG.CGT.PushingUpLit.A4

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly

section General

variable {G : Type} [Group G]

theorem isKleinFour_of_card_four_sq {H : Type*} [Group H] (h4 : Nat.card H = 4)
    (hsq : ∀ x : H, x ^ 2 = 1) : IsKleinFour H := by
  refine ⟨h4, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
    h | h
  · have : Subsingleton H := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : H)
    omega
  · exact h

theorem exists_isKleinFour_of_sq [Finite G] {K : Subgroup G} (hsq : ∀ x ∈ K, x * x = 1)
    (hcard : 4 ≤ Nat.card K) : ∃ U : Subgroup G, U ≤ K ∧ IsKleinFour ↥U := by
  have hK2 : IsPGroup 2 K := isPGroup_two_of_sq hsq
  obtain ⟨n, hn⟩ := hK2.exists_card_eq
  have h4 : 2 ^ 2 ∣ Nat.card K := by
    rw [hn] at hcard ⊢
    have : 2 ≤ n := by
      by_contra hlt
      push Not at hlt
      interval_cases n <;> simp at hcard
    exact pow_dvd_pow 2 this
  obtain ⟨U', hU'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥K) 2 h4
  refine ⟨U'.map K.subtype, Subgroup.map_subtype_le U', ?_⟩
  refine isKleinFour_of_card_four_sq ?_ ?_
  · rw [Subgroup.card_map_of_injective K.subtype_injective, hU']
    norm_num
  · rintro ⟨x, y, hy, rfl⟩
    have := hsq (K.subtype y) y.2
    apply Subtype.ext
    simpa [pow_two] using this

theorem exists_central_involution [Finite G] {D : Subgroup G} (hD2 : IsPGroup 2 D) (hD1 : D ≠ ⊥) :
    ∃ e ∈ D, e ≠ 1 ∧ e * e = 1 ∧ ∀ d ∈ D, d * e = e * d := by
  have : Nontrivial ↥D := (Subgroup.nontrivial_iff_ne_bot D).2 hD1
  have : Nontrivial ↥(Subgroup.center ↥D) := hD2.center_nontrivial
  have hZ : IsPGroup 2 ↥(Subgroup.center ↥D) := hD2.to_subgroup _
  have hcard : 2 ∣ Nat.card ↥(Subgroup.center ↥D) := by
    rcases hZ.card_eq_or_dvd with h | h
    · exact absurd (Nat.card_eq_one_iff_unique.mp h).1 (not_subsingleton _)
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥D)) 2 hcard
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  refine ⟨((z : ↥D) : G), (z : ↥D).2, ?_, ?_, ?_⟩
  · intro h1
    have : z = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hz
    omega
  · have := congrArg (fun w : ↥(Subgroup.center ↥D) => ((w : ↥D) : G)) hz2
    simpa [pow_two] using this
  · intro d hd
    have := Subgroup.mem_center_iff.1 z.2 ⟨d, hd⟩
    exact congrArg Subtype.val this

theorem conjSub_eq_of_conj_mem {M E : Subgroup G} (h : ∀ k ∈ M, ∀ y ∈ E, k * y * k⁻¹ ∈ E)
    {k : G} (hk : k ∈ M) : conjSub k E = E := by
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro hx
    have := h k hk _ hx
    simpa [mul_assoc] using this
  · intro hx
    have := h k⁻¹ (M.inv_mem hk) _ hx
    simpa [mul_assoc] using this

theorem exists_normal_elem_abelian [Finite G] {M D : Subgroup G} (hD2 : IsPGroup 2 D)
    (hD1 : D ≠ ⊥) (hDn : ∀ k ∈ M, conjSub k D = D) :
    ∃ E : Subgroup G, E ≤ D ∧ E ≠ ⊥ ∧ (∀ k ∈ M, conjSub k E = E) ∧ (∀ e ∈ E, e * e = 1) ∧
      ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e := by
  let E : Subgroup G :=
    { carrier := {z | z ∈ D ∧ z * z = 1 ∧ ∀ d ∈ D, d * z = z * d}
      one_mem' := ⟨D.one_mem, by simp, fun d _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, ha2, hac⟩ ⟨hb, hb2, hbc⟩
        refine ⟨D.mul_mem ha hb, ?_, fun d hd => ?_⟩
        · have hba : b * a = a * b := hac b hb
          calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [hba]
            _ = (a * a) * (b * b) := by group
            _ = 1 := by rw [ha2, hb2, one_mul]
        · calc d * (a * b) = (d * a) * b := by group
            _ = (a * d) * b := by rw [hac d hd]
            _ = a * (d * b) := by group
            _ = a * (b * d) := by rw [hbc d hd]
            _ = a * b * d := by group
      inv_mem' := by
        rintro a ⟨ha, ha2, hac⟩
        refine ⟨D.inv_mem ha, ?_, fun d hd => ?_⟩
        · have : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
          rw [this, ha2, inv_one]
        · exact (show Commute d a from hac d hd).inv_right }
  have hE : ∀ z, z ∈ E ↔ z ∈ D ∧ z * z = 1 ∧ ∀ d ∈ D, d * z = z * d := fun z => Iff.rfl
  obtain ⟨e, heD, he1, he2, hec⟩ := exists_central_involution hD2 hD1
  refine ⟨E, fun z hz => ((hE z).1 hz).1, ?_, ?_, fun e hE' => ((hE e).1 hE').2.1, ?_⟩
  · intro hbot
    have : e ∈ E := (hE e).2 ⟨heD, he2, hec⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact he1 this
  · intro k hk
    apply conjSub_eq_of_conj_mem (M := M)
    intro k hk y hy
    obtain ⟨hyD, hy2, hyc⟩ := (hE y).1 hy
    have hkD : conjSub k D = D := hDn k hk
    refine (hE _).2 ⟨?_, ?_, fun d hd => ?_⟩
    · have := conj_mem_conjSub (g := k) hyD
      rwa [hkD] at this
    · calc k * y * k⁻¹ * (k * y * k⁻¹) = k * (y * y) * k⁻¹ := by group
        _ = 1 := by rw [hy2]; group
    · have hd' : k⁻¹ * d * k ∈ D := by
        have : d ∈ conjSub k D := by rw [hkD]; exact hd
        exact mem_conjSub_iff.1 this
      have h1 := hyc _ hd'
      calc d * (k * y * k⁻¹) = k * ((k⁻¹ * d * k) * y) * k⁻¹ := by group
        _ = k * (y * (k⁻¹ * d * k)) * k⁻¹ := by rw [h1]
        _ = k * y * k⁻¹ * d := by group
    exact hk
  · intro e he e' he'
    exact ((hE e').1 he').2.2 e ((hE e).1 he).1

theorem exists_sylow_ge [Finite G] {M B : Subgroup G} (hB : IsPGroup 2 B) (hBM : B ≤ M) :
    ∃ S : Subgroup G, S ≤ M ∧ IsPGroup 2 S ∧ ¬ 2 ∣ S.relIndex M ∧ B ≤ S := by
  have hB' : IsPGroup 2 ↥(B.subgroupOf M) := hB.comap_subtype
  obtain ⟨P, hP⟩ := hB'.exists_le_sylow
  refine ⟨(P : Subgroup ↥M).map M.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · exact P.isPGroup'.map M.subtype
  · have e : ((P : Subgroup ↥M).map M.subtype).subgroupOf M = P :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
    unfold Subgroup.relIndex
    rw [e]
    exact P.not_dvd_index
  · intro x hx
    exact ⟨⟨x, hBM hx⟩, hP (Subgroup.mem_subgroupOf.2 hx), rfl⟩

theorem relIndex_ne_zero_of_finite [Finite G] (H K : Subgroup G) : H.relIndex K ≠ 0 := by
  intro h0
  have := Subgroup.relIndex_mul_card H K
  rw [h0, zero_mul] at this
  exact (Nat.card_pos (α := ↥K)).ne' this.symm

theorem centralizer_conj_le {g d : G} {H : Subgroup G}
    (h : Subgroup.centralizer ({d} : Set G) ≤ H) :
    Subgroup.centralizer ({g * d * g⁻¹} : Set G) ≤ conjSub g H := by
  intro z hz
  rw [mem_conjSub_iff]
  apply h
  have h1 := Subgroup.mem_centralizer_iff.1 hz (g * d * g⁻¹) rfl
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  calc y * (g⁻¹ * z * g) = g⁻¹ * ((g * y * g⁻¹) * z) * g := by group
    _ = g⁻¹ * (z * (g * y * g⁻¹)) * g := by rw [h1]
    _ = g⁻¹ * z * g * y := by group

end General

section PairCent

variable {G : Type} [Group G] {M X : Subgroup G} {m : G}

@[expose] def pairCent (X : Subgroup G) (m : G) : Subgroup G :=
  Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (conjSub m X : Set G)

theorem mem_pairCent_iff {z : G} :
    z ∈ pairCent X m ↔ (∀ x ∈ X, x * z = z * x) ∧ (∀ y ∈ conjSub m X, y * z = z * y) := by
  simp only [pairCent, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]

theorem baseTwo_le_centralizer {z : G} (hz : z ∈ pairCent X m) :
    baseTwo X m ≤ Subgroup.centralizer ({z} : Set G) := by
  rw [mem_pairCent_iff] at hz
  refine sup_le (fun v hv => ?_) (fun v hv => ?_)
  · rw [Subgroup.mem_centralizer_iff]
    intro h' hh'
    rw [Set.mem_singleton_iff] at hh'
    subst hh'
    exact (hz.1 v (SolK.pCoreOf_le_self X hv)).symm
  · rw [Subgroup.mem_centralizer_iff]
    intro h' hh'
    rw [Set.mem_singleton_iff] at hh'
    subst hh'
    exact (hz.2 v (SolK.pCoreOf_le_self _ hv)).symm

theorem conjSub_pairCent (h : TwoConj M X m) {k : G} (hk : k ∈ M) :
    conjSub k (pairCent X m) = pairCent X m := by
  unfold pairCent
  rw [conjSub_inf, conjSub_centralizer, conjSub_centralizer]
  rcases twoConj_perm h hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, inf_comm]

variable [Finite G]

theorem normalizer_le_of_normal (c : A4Cfg G M X) {B : Subgroup G} (hB : IsPGroup 2 B)
    (hB1 : B ≠ ⊥) (hBn : ∀ k ∈ M, conjSub k B = B) : Subgroup.normalizer (B : Set G) ≤ M := by
  refine c.normalizer_le hB hB1 (one_mem M) ?_
  rw [conjSub_one]
  intro x hx
  have hxM : x ∈ M := c.le hx
  have := mem_normalizer_of_conjSub_eq (g₁ := x) (g₂ := 1)
    ((hBn x hxM).trans (conjSub_one B).symm)
  simpa using this

theorem baseTwo_le (c : A4Cfg G M X) (h : TwoConj M X m) : baseTwo X m ≤ M :=
  sup_le ((SolK.pCoreOf_le_self X).trans c.le)
    ((SolK.pCoreOf_le_self _).trans (c.conj_le h.1))

theorem baseTwo_ne_bot (c : A4Cfg G M X) : baseTwo X m ≠ ⊥ := by
  obtain ⟨a, ha⟩ := SolD3.exists_blk3 c.short c.nat
  obtain ⟨w, hw, hw1⟩ := ha.exists_ne_one
  intro hbot
  have : w ∈ baseTwo X m := pCoreOf_le_baseTwo X m hw
  rw [hbot, Subgroup.mem_bot] at this
  exact hw1 this

theorem pairCent_le (c : A4Cfg G M X) (h : TwoConj M X m) : pairCent X m ≤ M := by
  intro z hz
  have hA := baseTwo_le_centralizer hz
  have hAn := normalizer_le_of_normal c (isPGroup_two_of_sq (baseTwo_sq c h)) (baseTwo_ne_bot c)
    (fun k hk => conjSub_baseTwo h hk)
  apply hAn
  apply centralizer_le_normalizer' (baseTwo X m)
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact (Subgroup.mem_centralizer_iff.1 (hA ha) z (Set.mem_singleton z)).symm

theorem pairCent_inf_ne_bot (c : A4Cfg G M X) (h : TwoConj M X m) (hC : pairCent X m ≠ ⊥) :
    pairCent X m ⊓ pCoreOf 2 M ≠ ⊥ := by
  intro hD
  apply hC
  refine eq_bot_iff.2 fun z hz => Subgroup.mem_bot.2 ?_
  have hzM : z ∈ M := pairCent_le c h hz
  have hzQ : z ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqM : q ∈ M := SolK.pCoreOf_le_self M hq
    have h1 : q * z * q⁻¹ * z⁻¹ ∈ pairCent X m ⊓ pCoreOf 2 M := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have h2 : q * z * q⁻¹ ∈ pairCent X m := by
          have := conj_mem_conjSub (g := q) hz
          rwa [conjSub_pairCent h hqM] at this
        exact (pairCent X m).mul_mem h2 ((pairCent X m).inv_mem hz)
      · have h3 : z * q⁻¹ * z⁻¹ ∈ pCoreOf 2 M :=
          SolK.pCoreOf_normalized M hzM ((pCoreOf 2 M).inv_mem hq)
        have := (pCoreOf 2 M).mul_mem hq h3
        simpa [mul_assoc] using this
    rw [hD, Subgroup.mem_bot] at h1
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
  have hzQ' : z ∈ pCoreOf 2 M := c.charTwo M c.maxLocal.1 (Subgroup.mem_inf.2 ⟨hzM, hzQ⟩)
  have : z ∈ pairCent X m ⊓ pCoreOf 2 M := Subgroup.mem_inf.2 ⟨hz, hzQ'⟩
  rwa [hD, Subgroup.mem_bot] at this

end PairCent

section Stab

variable {G : Type} [Group G] {M X : Subgroup G} {m : G}

@[expose] def stabSub (M X : Subgroup G) : Subgroup G where
  carrier := {k | k ∈ M ∧ conjSub k X = X}
  one_mem' := ⟨M.one_mem, conjSub_one X⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨M.mul_mem ha hb, ?_⟩
    rw [← conjSub_conjSub, hb', ha']
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨M.inv_mem ha, ?_⟩
    calc conjSub a⁻¹ X = conjSub a⁻¹ (conjSub a X) := by rw [ha']
      _ = X := by rw [conjSub_conjSub, inv_mul_cancel, conjSub_one]

theorem mem_stabSub_iff {k : G} : k ∈ stabSub M X ↔ k ∈ M ∧ conjSub k X = X := Iff.rfl

theorem stabSub_le (M X : Subgroup G) : stabSub M X ≤ M := fun _ hk => hk.1

theorem stabSub_relIndex (h : TwoConj M X m) : (stabSub M X).relIndex M = 2 := by
  show ((stabSub M X).subgroupOf M).index = 2
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨m, h.1⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, mem_stabSub_iff, Subgroup.coe_mul]
  have hbm : (b : G) * m ∈ M := M.mul_mem b.2 h.1
  have hmul : conjSub ((b : G) * m) X = conjSub (b : G) (conjSub m X) :=
    (conjSub_conjSub _ _ _).symm
  rcases twoConj_perm h b.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inr ⟨⟨b.2, h1⟩, fun ⟨_, h3⟩ => h.2.1 ?_⟩
    rw [hmul, h2] at h3
    exact h3
  · refine Or.inl ⟨⟨hbm, ?_⟩, fun ⟨_, h3⟩ => h.2.1 ?_⟩
    · rw [hmul, h2]
    · rw [h1] at h3
      exact h3

end Stab

section Main

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {m : G}

theorem noTwoQuotient_of_a4Cfg (c : A4Cfg G M X) : NoTwoQuotient G := by
  have := c.simple
  intro N hN hP
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exfalso
    obtain ⟨a, ha⟩ := SolD3.exists_blk3 c.short c.nat
    have ha1 : a ≠ 1 := by
      intro h1
      obtain ⟨w, hw, hw1⟩ := ha.exists_ne_one
      apply hw1
      apply ha.fix w hw
      rw [h1]
      group
    obtain ⟨k, hk⟩ := hP (QuotientGroup.mk a)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, h, Subgroup.mem_bot] at hk
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    have := pow_gcd_eq_one.2 ⟨ha.cube, hk⟩
    rw [hcop] at this
    exact ha1 (by simpa using this)
  · exact h

theorem card_ge_eight (c : A4Cfg G M X) {e : G} (he : e ∈ pairCent X m) (he1 : e ≠ 1)
    {B : Subgroup G} (hB2 : IsPGroup 2 B) (hVB : pCoreOf 2 X ≤ B) (heB : e ∈ B) :
    8 ≤ Nat.card B := by
  obtain ⟨a, ha⟩ := SolD3.exists_blk3 c.short c.nat
  have h4 : Nat.card ↥(pCoreOf 2 X) = 4 := ha.card
  have heV : e ∉ pCoreOf 2 X := fun hv =>
    he1 (c.center_eq_one (SolK.pCoreOf_le_self X hv)
      (fun x hx => ((mem_pairCent_iff.1 he).1 x hx).symm))
  obtain ⟨j, hj⟩ := hB2.exists_card_eq
  have hdvd : 4 ∣ 2 ^ j := by
    rw [← hj, ← h4]
    exact Subgroup.card_dvd_of_le hVB
  have hne : Nat.card B ≠ 4 := by
    intro h4B
    have hle : Nat.card B ≤ Nat.card ↥(pCoreOf 2 X) := by rw [h4B, h4]
    have := Subgroup.eq_of_le_of_card_ge hVB hle
    exact heV (this ▸ heB)
  rw [hj] at hne ⊢
  by_contra hlt
  push Not at hlt
  have hj2 : j ≤ 2 := by
    by_contra h3
    push Not at h3
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h3
    omega
  interval_cases j <;> simp_all

theorem exists_klein_of_relIndex {M A' B : Subgroup G} {g : G} (hA : ∀ x ∈ A', x * x = 1)
    (hBA : B ≤ A') (hB8 : 8 ≤ Nat.card B) (hrel : M.relIndex (conjSub g A') ≤ 2) :
    ∃ U : Subgroup G, U ≤ M ∧ U ≤ conjSub g B ∧ IsKleinFour ↥U := by
  have hle : conjSub g B ≤ conjSub g A' := conjSub_map_le g hBA
  have h1 : M.relIndex (conjSub g B) ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right hle (relIndex_ne_zero_of_finite _ _)).trans hrel
  have h2 := Subgroup.relIndex_mul_card M (conjSub g B)
  have hcardBg : Nat.card ↥(conjSub g B) = Nat.card B := conjSub_card g B
  have hK : 4 ≤ Nat.card ↥(M ⊓ conjSub g B) := by
    have : Nat.card B ≤ 2 * Nat.card ↥(M ⊓ conjSub g B) := by
      rw [← hcardBg, ← h2]
      exact Nat.mul_le_mul_right _ h1
    omega
  have hsq : ∀ x ∈ M ⊓ conjSub g B, x * x = 1 := by
    intro x hx
    have hxB : g⁻¹ * x * g ∈ B := mem_conjSub_iff.1 (Subgroup.mem_inf.1 hx).2
    have h3 := hA _ (hBA hxB)
    calc x * x = g * (g⁻¹ * x * g * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = 1 := by rw [h3]; group
  obtain ⟨U, hUK, hU⟩ := exists_isKleinFour_of_sq hsq hK
  exact ⟨U, hUK.trans inf_le_left, hUK.trans inf_le_right, hU⟩

theorem pairCent_eq_bot (hT : HaradaTransfer211) (hL : Lemma34Two M) (c : A4Cfg G M X)
    (h : TwoConj M X m) (hSC : StrongClosureTwo M X m) : pairCent X m = ⊥ := by
  by_contra hC
  have hDne := pairCent_inf_ne_bot c h hC
  have hQn : ∀ k ∈ M, conjSub k (pCoreOf 2 M) = pCoreOf 2 M := fun k hk =>
    conjSub_eq_of_conj_mem (fun k hk y hy => SolK.pCoreOf_normalized M hk hy) hk
  have hD2 : IsPGroup 2 ↥(pairCent X m ⊓ pCoreOf 2 M) :=
    (SolK.isPGroup_pCoreOf' M).to_le inf_le_right
  have hDn : ∀ k ∈ M, conjSub k (pairCent X m ⊓ pCoreOf 2 M) = pairCent X m ⊓ pCoreOf 2 M := by
    intro k hk
    rw [conjSub_inf, conjSub_pairCent h hk, hQn k hk]
  obtain ⟨E, hED, hE1, hEn, hEsq, hEcomm⟩ := exists_normal_elem_abelian hD2 hDne hDn
  have hEC : E ≤ pairCent X m := hED.trans inf_le_left
  have hEQ : E ≤ pCoreOf 2 M := hED.trans inf_le_right
  have hAE : ∀ a ∈ baseTwo X m, ∀ e ∈ E, Commute a e := fun a ha e he =>
    (Subgroup.mem_centralizer_iff.1 (baseTwo_le_centralizer (hEC he) ha) e
      (Set.mem_singleton e)).symm
  have hAcomm := baseTwo_comm c h
  have hAsq := baseTwo_sq c h
  have hA'comm : ∀ x ∈ baseTwo X m ⊔ E, ∀ y ∈ baseTwo X m ⊔ E, x * y = y * x :=
    commute_of_mem_sup hAE hAcomm hEcomm
  have hA'sq : ∀ x ∈ baseTwo X m ⊔ E, x * x = 1 :=
    sq_eq_one_of_mem_sup hAE hAsq hEsq hAcomm hEcomm
  have hA'2 : IsPGroup 2 ↥(baseTwo X m ⊔ E) := isPGroup_two_of_sq hA'sq
  have hA'1 : baseTwo X m ⊔ E ≠ ⊥ := fun hb =>
    hE1 (eq_bot_iff.2 fun x hx => by
      have : x ∈ baseTwo X m ⊔ E := (le_sup_right : E ≤ baseTwo X m ⊔ E) hx
      rwa [hb] at this)
  have hA'n : ∀ k ∈ M, conjSub k (baseTwo X m ⊔ E) = baseTwo X m ⊔ E := fun k hk => by
    rw [conjSub_sup, conjSub_baseTwo h hk, hEn k hk]
  have hA'M : baseTwo X m ⊔ E ≤ M :=
    sup_le (baseTwo_le c h) (hEQ.trans (SolK.pCoreOf_le_self M))
  have hnorm : Subgroup.normalizer ((baseTwo X m ⊔ E : Subgroup G) : Set G) ≤ M :=
    normalizer_le_of_normal c hA'2 hA'1 hA'n
  obtain ⟨S, hSM, hS2, hSidx, hA'S⟩ := exists_sylow_ge hA'2 hA'M
  have hA'Sn : ((baseTwo X m ⊔ E).subgroupOf S).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := conj_mem_conjSub (g := (g : G)) hn
    rwa [hA'n g (hSM g.2)] at this
  have hA4 : ∀ a ∈ baseTwo X m ⊔ E, a ^ 4 = 1 := fun a ha => by
    have : a ^ 4 = (a * a) * (a * a) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    rw [this, hA'sq a ha, one_mul]
  have hsyl : ∀ g : G, (baseTwo X m ⊔ E).map (MulAut.conj g).toMonoidHom ≤ M →
      ∃ m' ∈ M, (baseTwo X m ⊔ E).map (MulAut.conj g).toMonoidHom =
        (baseTwo X m ⊔ E).map (MulAut.conj m').toMonoidHom := by
    intro g hg
    have hAg : conjSub g (baseTwo X m) ≤ M := (conjSub_map_le g le_sup_left).trans hg
    exact ⟨g, hSC g hAg, rfl⟩
  obtain ⟨g, hgM, hrel, -⟩ := hT G (noTwoQuotient_of_a4Cfg c) M (stabSub M X) S
    (baseTwo X m ⊔ E) (stabSub_le M X) (stabSub_relIndex h) hSM hS2 hSidx hA'S hA'Sn hA'comm hA4
    hnorm hsyl
  obtain ⟨e', he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hE1
  have he1' : (e' : G) ≠ 1 := fun h1 => he1 (Subtype.ext h1)
  have heE : (e' : G) ∈ E := e'.2
  have hBA' : pCoreOf 2 X ⊔ Subgroup.zpowers (e' : G) ≤ baseTwo X m ⊔ E :=
    sup_le ((pCoreOf_le_baseTwo X m).trans le_sup_left)
      (Subgroup.zpowers_le.2 ((le_sup_right : E ≤ baseTwo X m ⊔ E) heE))
  have hB2 : IsPGroup 2 ↥(pCoreOf 2 X ⊔ Subgroup.zpowers (e' : G)) := hA'2.to_le hBA'
  have hB8 : 8 ≤ Nat.card ↥(pCoreOf 2 X ⊔ Subgroup.zpowers (e' : G)) :=
    card_ge_eight c (hEC heE) he1' hB2 le_sup_left
      ((le_sup_right : Subgroup.zpowers (e' : G) ≤ _) (Subgroup.mem_zpowers _))
  obtain ⟨U, hUM, hUB, hU4⟩ := exists_klein_of_relIndex hA'sq hBA' hB8 hrel
  apply hgM
  refine hL U hUM hU4 g ?_
  intro u hu hu1
  have hd : g⁻¹ * u * g ∈ pCoreOf 2 X ⊔ Subgroup.zpowers (e' : G) := mem_conjSub_iff.1 (hUB hu)
  have hd1 : g⁻¹ * u * g ≠ 1 := fun h1 => hu1 (by
    calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  have hBX2 : pCoreOf 2 X ⊔ Subgroup.zpowers (e' : G) ≤
      Subgroup.centralizer ((conjSub m X : Subgroup G) : Set G) := by
    refine sup_le (fun v hv => ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (twoConj_commute c h v (SolK.pCoreOf_le_self X hv) y hy).symm
    · rw [Subgroup.mem_centralizer_iff]
      exact fun y hy => (mem_pairCent_iff.1 (hEC heE)).2 y hy
  have hPd : Subgroup.zpowers (g⁻¹ * u * g) ≤
      Subgroup.centralizer ((conjSub m X : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le.2 hd).trans hBX2
  have hPd2 : IsPGroup 2 ↥(Subgroup.zpowers (g⁻¹ * u * g)) :=
    hB2.to_le (Subgroup.zpowers_le.2 hd)
  have hPd1 : Subgroup.zpowers (g⁻¹ * u * g) ≠ ⊥ := fun hb =>
    hd1 (Subgroup.zpowers_eq_bot.1 hb)
  have hcent := c.centralizer_le hPd2 hPd1 h.1 hPd
  have hcent' : Subgroup.centralizer ({g⁻¹ * u * g} : Set G) ≤ M := by
    refine le_trans ?_ hcent
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have := centralizer_conj_le (g := g) hcent'
  have hu' : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
  rwa [hu'] at this

end Main

end CFSG.CGT.PushingUpLit.A4
