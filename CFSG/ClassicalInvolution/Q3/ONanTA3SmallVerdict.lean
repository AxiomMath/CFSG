module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallInner
public import CFSG.ClassicalInvolution.Q3.TA3SmallCriteria
public import CFSG.ClassicalInvolution.Q3.TA3SmallTransportEx

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

variable {Y : Type} [Group Y]

@[expose] def NoOddNormalAt3 (t : Y) : Prop :=
  ∀ o ∈ Subgroup.centralizer ({t} : Set Y), o ≠ 1 → Odd (orderOf o) →
    (∃ c ∈ Subgroup.centralizer ({t} : Set Y), Even (orderOf (o * (c * o * c⁻¹)))) ∨
    ∃ c ∈ Subgroup.centralizer ({t} : Set Y), ∃ d ∈ Subgroup.centralizer ({t} : Set Y),
      Even (orderOf (o * (c * o * c⁻¹) * (d * o * d⁻¹)))

@[expose] def Edgeless (t a b : Y) : Prop :=
  ∀ g : Y, (∀ r ∈ q8List t a b, g * r * g⁻¹ ∈ Subgroup.centralizer ({t} : Set Y)) →
    ∃ r ∈ q8List t a b, g * r * g⁻¹ = t

@[expose] def NoActs3 (t a b : Y) : Prop :=
  ∀ x ∈ Subgroup.centralizer ({t} : Set Y), ∀ k : ℕ, x ^ 3 ^ k = 1 →
    x * a = a * x ∧ x * b = b * x

@[expose] def GoodWit (t a b : Y) : Prop :=
  ∃ x ∈ Subgroup.centralizer ({t} : Set Y), x ^ 3 = 1 ∧ ¬ (x * a = a * x ∧ x * b = b * x) ∧
    ∀ y ∈ Subgroup.centralizer ({t} : Set Y), y * a = a * y → y * b = b * y → x * y = y * x

@[expose] def PairVerdict (N : Subgroup Y) (E3b : Prop) (t a b : Y) : Prop :=
  (a ∈ N ∧ b ∈ N) ∨ GoodWit t a b ∨ (Edgeless t a b ∧ NoActs3 t a b) ∨ (Edgeless t a b ∧ E3b)

@[expose] def VerdictPred (N : Subgroup Y) (E3b : Prop) (t : Y) : Prop :=
  NoOddNormalAt3 t ∧
    ∀ a b : Y, a * a = t → b * b = t → b * a = t * a * b →
      (∀ c ∈ Subgroup.centralizer ({t} : Set Y),
        c * a * c⁻¹ ∈ q8List t a b ∧ c * b * c⁻¹ ∈ q8List t a b) →
      PairVerdict N E3b t a b

section Engine

variable [Finite Y]

theorem oddCoreImg_eq_bot_3 {t : Y} (hno : NoOddNormalAt3 t) {H : Subgroup Y}
    (hH : H ≤ Subgroup.centralizer ({t} : Set Y))
    (hnorm : Subgroup.centralizer ({t} : Set Y) ≤ Subgroup.normalizer (H : Set Y)) :
    oddCoreImg H = ⊥ := by
  rw [eq_bot_iff]
  intro o ho
  by_contra hne
  have hne' : o ≠ 1 := by simpa using hne
  have hconj : ∀ c ∈ Subgroup.centralizer ({t} : Set Y), c * o * c⁻¹ ∈ oddCoreImg H :=
    fun c hc => conj_mem_oddCoreImg (hnorm hc) ho
  rcases hno o (hH (oddCoreImg_le H ho)) hne' (odd_orderOf_of_mem_oddCoreImg ho) with
    ⟨c, hc, hev⟩ | ⟨c, hc, d, hd, hev⟩
  · exact (Nat.not_even_iff_odd.mpr (odd_orderOf_of_mem_oddCoreImg
      (Subgroup.mul_mem _ ho (hconj c hc)))) hev
  · exact (Nat.not_even_iff_odd.mpr (odd_orderOf_of_mem_oddCoreImg
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ ho (hconj c hc)) (hconj d hd)))) hev

omit [Finite Y] in
theorem tightCore_eq_of_pGroup {R : Subgroup Y} (hR : IsPGroup 2 R) : tightCore R = R := by
  refine le_antisymm (tightCore_le R) fun x hx => Subgroup.subset_closure ⟨hx, ?_⟩
  obtain ⟨n, hn⟩ := hR ⟨x, hx⟩
  have hxn : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hxn)
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])

omit [Finite Y] in
theorem commute_of_mem_q8List {t a b x : Y} (hxa : x * a = a * x) (hxb : x * b = b * x)
    (hxt : x * t = t * x) {r : Y} (hr : r ∈ q8List t a b) : x * r = r * x := by
  have ha : Commute x a := hxa
  have hb : Commute x b := hxb
  have ht : Commute x t := hxt
  simp only [q8List, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (Commute.one_right x).eq
  · exact ha.eq
  · exact ht.eq
  · exact (ht.mul_right ha).eq
  · exact hb.eq
  · exact (hb.mul_right ha).eq
  · exact (hb.mul_right ht).eq
  · exact (hb.mul_right (ht.mul_right ha)).eq

theorem tightEdgeless_of_edgeless {R : Subgroup Y} {S : Sylow 2 R} {t a b : Y}
    (hd : TightDatum R S t) (hR : IsPGroup 2 R) (ha : a ∈ R) (hb : b ∈ R) (haa : a * a = t)
    (hE : Edgeless t a b) : TightEdgeless R := by
  refine TightDatum.edgeless_of_forall hd ?_
  rintro P ⟨J, ⟨g, rfl⟩, Q, rfl⟩ hPC
  have hJ : conjSub g (tightCore R) = conjSub g R := by rw [tightCore_eq_of_pGroup hR]
  have hJ2 : IsPGroup 2 (conjSub g (tightCore R)) := by
    rw [hJ]
    exact hR.of_equiv (Subgroup.equivMapOfInjective R (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)
  have hQ : (⊤ : Subgroup (conjSub g (tightCore R))) = (Q : Subgroup (conjSub g (tightCore R))) :=
    Q.is_maximal' (hJ2.of_equiv Subgroup.topEquiv.symm) le_top
  have hPJ : (Q : Subgroup (conjSub g (tightCore R))).map (conjSub g (tightCore R)).subtype =
      conjSub g (tightCore R) := by
    rw [← hQ, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hPJ, hJ] at hPC ⊢
  have hmem : ∀ r ∈ R, g * r * g⁻¹ ∈ conjSub g R := fun r hr =>
    Subgroup.mem_map.2 ⟨r, hr, by simp [MulAut.conj_apply]⟩
  obtain ⟨r, hr, hgr⟩ := hE g fun r hr => hPC (hmem r (mem_of_mem_q8List ha hb haa hr))
  rw [← hgr]
  exact hmem r (mem_of_mem_q8List ha hb haa hr)

theorem not_tightActs3_of_noActs3 {R : Subgroup Y} {S : Sylow 2 R} {t a b : Y}
    (hd : TightDatum R S t) (hlist : ∀ r ∈ R, r ∈ q8List t a b) (hN : NoActs3 t a b) :
    ¬ TightActs3 R t := by
  refine TightDatum.not_acts3_of_forall hd fun x hx k hxk => ⟨1, one_mem _, x, ?_, (one_mul x).symm⟩
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  obtain ⟨hxa, hxb⟩ := hN x hx k hxk
  have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hx
  exact (commute_of_mem_q8List hxa hxb hxt (hlist r hr)).symm

theorem verdict_of_verdictPred {N : Subgroup Y} {E3b : Prop} (hN : N.Normal) (hNtop : N ≠ ⊤)
    (hE3b : E3b → ∃ f : Y →* CFSG.Blueprint.NativeSporadic.Carrier .M12,
      Function.Surjective f ∧ IsPGroup 2 ↥f.ker)
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hP : VerdictPred N E3b t) : TightEx Y R S t ∨ GoodThreeElement R t := by
  obtain ⟨hOR, hR2, a, b, ha, hb, haa, hbb, hba, hlist⟩ :=
    datum_shape_of_odd hd hc.1 (oddCoreImg_eq_bot_3 hP.1 hd.cent hd.le_normalizer)
  have hOC : oddCoreImg (Subgroup.centralizer ({t} : Set Y)) = ⊥ :=
    oddCoreImg_eq_bot_3 hP.1 le_rfl fun g hg => Subgroup.le_normalizer hg
  have hnorm : ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      c * a * c⁻¹ ∈ q8List t a b ∧ c * b * c⁻¹ ∈ q8List t a b := fun c hc =>
    ⟨hlist _ ((Subgroup.mem_normalizer_iff.mp (hd.le_normalizer hc) a).mp ha),
      hlist _ ((Subgroup.mem_normalizer_iff.mp (hd.le_normalizer hc) b).mp hb)⟩
  rcases hP.2 a b haa hbb hba hnorm with ⟨haN, hbN⟩ | ⟨x, hx, hx3, hmove, hcomm⟩ |
    ⟨hE, hA⟩ | ⟨hE, h3b⟩
  · exact absurd hc.2.1 (not_selfGen_of_le hN hNtop fun r hr =>
      mem_of_mem_q8List haN hbN haa (hlist r hr))
  · exact Or.inr (good_of_witness hOR hOC ha hb hx hx3 hmove hcomm)
  · exact Or.inl (Or.inr (Or.inl ⟨tightEdgeless_of_edgeless hd hR2 ha hb haa hE,
      not_tightActs3_of_noActs3 hd hlist hA⟩))
  · obtain ⟨f, hf, hker⟩ := hE3b h3b
    exact Or.inl (Or.inr (Or.inr (Or.inl
      ⟨tightEdgeless_of_edgeless hd hR2 ha hb haa hE, f, hf, hker⟩)))

@[expose] def Phi (t : Y) : Prop :=
  ∀ (R : Subgroup Y) (S : Sylow 2 R), TightDatum R S t → TightCls Y R S t → ¬ TightInO2 t →
    TightEx Y R S t ∨ GoodThreeElement R t

theorem phi_of_conj {t : Y} (g : Y) (h : Phi (g * t * g⁻¹)) : Phi t := by
  intro R S hd hc hE2
  refine tightExOrGood_of_map_equiv (MulAut.conj g) hd hc hE2 ?_
  intro S' hd' hc' hE2'
  exact h _ S' hd' hc' hE2'

theorem phi_of_reps {reps : Set Y} (hreps : ∀ r ∈ reps, Phi r)
    (hcover : ∀ t : Y, orderOf t = 2 → ∃ r ∈ reps, ∃ g : Y, g * t * g⁻¹ = r) {t : Y}
    (ht : orderOf t = 2) : Phi t := by
  obtain ⟨r, hr, g, hg⟩ := hcover t ht
  exact phi_of_conj g (hg ▸ hreps r hr)

end Engine

end CFSG.ClassicalInvolution.Q3.TA3
