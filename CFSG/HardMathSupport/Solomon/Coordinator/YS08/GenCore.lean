module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.GenCoreBT
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Assembly
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.LieType.BorelTits CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

theorem lieIndexChar_eq_two_of_isCharTwoLieIndex {d : TauCeti.LieTypeIndex}
    (h : IsCharTwoLieIndex d) : lieIndexChar d = 2 := by
  cases d <;> simp_all [lieIndexChar, IsCharTwoLieIndex]

theorem isChevOfChar_two_of_isChevTwo {X : Type*} [Group X] (h : IsChevTwo X) :
    IsChevOfChar 2 X := by
  obtain ⟨d, hd, ⟨e⟩⟩ := h
  exact ⟨d, isChevIndexOfChar_of_lieIndexChar_eq (lieIndexChar_eq_two_of_isCharTwoLieIndex hd),
    ⟨e⟩⟩

theorem not_le_centerIn_of_ne_bot {Y : Type} [Group Y] [Finite Y] {K Q : Subgroup Y} {q : ℕ}
    [Fact q.Prime] (hZ : Nat.Coprime (Nat.card (Subgroup.center ↥K)) q) (hQp : IsPGroup q ↥Q)
    (hQ : Q ≠ ⊥) : ¬ Q ≤ centerIn K := by
  intro h
  obtain ⟨n, hn⟩ := hQp.exists_card_eq
  have hdvd : Nat.card Q ∣ Nat.card (centerIn K) := Subgroup.card_dvd_of_le h
  have hcard : Nat.card (centerIn K) = Nat.card (Subgroup.center ↥K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  rw [hcard, hn] at hdvd
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · apply hQ
    apply Subgroup.eq_bot_of_card_eq
    rw [hn, h0, pow_zero]
  · have hq : q ∣ Nat.card (Subgroup.center ↥K) :=
      (dvd_pow_self q (Nat.pos_iff_ne_zero.1 hpos)).trans hdvd
    have := Nat.Coprime.eq_one_of_dvd hZ.symm hq
    exact (Fact.out : q.Prime).one_lt.ne' this

theorem le_normalizer_of_conj_mem {Y : Type*} [Group Y] {E T : Subgroup Y}
    (h : ∀ e ∈ E, ∀ t ∈ T, e * t * e⁻¹ ∈ T) : E ≤ Subgroup.normalizer (T : Set Y) := by
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h e he y hy, fun hy => ?_⟩
  have := h e⁻¹ (E.inv_mem he) _ hy
  simpa [mul_assoc] using this

theorem genCore_of_constrained (hL : LieQConstrained 2) : GenCore := by
  intro Y _ _ K E J hKq hK3 hKc hEN hEel hE9 hfaith hJle hJq h3 hJL hnorm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hChev : IsChevOfChar 2 (↥K ⧸ Subgroup.center ↥K) := isChevOfChar_two_of_isChevTwo hKc
  have hZ : Nat.Coprime (Nat.card (Subgroup.center ↥K)) 2 := coprime_card_center_two hK3
  have hJK : J ≤ K := fun x hx => (hJle hx).1
  have hJE : ∀ j ∈ J, ∀ e ∈ E, e * j = j * e := fun j hj e he =>
    Subgroup.mem_centralizer_iff.1 (hJle hj).2 e he
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hnormJ : ∀ b ∈ E, b ≠ 1 → ∀ c ∈ K ⊓ Subgroup.centralizer ({b} : Set Y), ∀ j ∈ J,
      c * j * c⁻¹ ∈ J := by
    intro b hb hb1 c hc j hj
    have hjKC : j ∈ K ⊓ Subgroup.centralizer ({b} : Set Y) :=
      ⟨hJK hj, Subgroup.mem_centralizer_singleton_iff.2 (hJE j hj b hb).symm⟩
    exact (hnorm b hb hb1).conj_mem ⟨j, hjKC⟩ hj ⟨c, hc⟩
  have hJ2 : 2 ∣ Nat.card ↥J := by
    have h1 := card_eq_of_isLThreeFour hJL
    exact (show 2 ∣ Nat.card (↥J ⧸ GLAPPrimeCore 3 ↥J) by rw [h1]; norm_num).trans
      (Subgroup.card_quotient_dvd_card _)
  obtain ⟨x0, hx0⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) 2 hJ2
  have hgo : orderOf (x0 : Y) = 2 := by rw [Subgroup.orderOf_coe, hx0]
  have hg1 : (x0 : Y) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hgo
    omega
  set Q : Subgroup Y := Subgroup.zpowers (x0 : Y) with hQdef
  have hQJ : Q ≤ J := Subgroup.zpowers_le.2 x0.2
  have hQK : Q ≤ K := hQJ.trans hJK
  have hQp : IsPGroup 2 ↥Q :=
    IsPGroup.of_card (n := 1) (by rw [hQdef, Nat.card_zpowers, hgo]; norm_num)
  have hQne : Q ≠ ⊥ := by
    intro h
    have : (x0 : Y) ∈ Q := Subgroup.mem_zpowers _
    rw [h] at this
    exact hg1 (Subgroup.mem_bot.1 this)
  have hQc : ¬ Q ≤ centerIn K := not_le_centerIn_of_ne_bot hZ hQp hQne
  have hEC : ∀ e ∈ E, e ∈ Subgroup.centralizer (Q : Set Y) := fun e he =>
    Subgroup.mem_centralizer_iff.2 fun y hy => (hJE y (hQJ hy) e he).symm
  have hEQ : ∀ e ∈ E, e ∈ Subgroup.normalizer (Q : Set Y) := fun e he =>
    Subgroup.centralizer_le_normalizer (Q : Set Y) (hEC e he)
  set R : Subgroup Y := radK 2 K Q with hRdef
  have hRK : R ≤ K := radK_le 2 K Q
  have hRp : IsPGroup 2 ↥R := radK_isPGroup 2 K Q
  have hRE : ∀ e ∈ E, ∀ t ∈ R, e * t * e⁻¹ ∈ R := fun e he t ht =>
    conj_mem_radK 2 hQK (hEN he) (hEQ e he) ht
  have hRN : E ≤ Subgroup.normalizer (R : Set Y) := le_normalizer_of_conj_mem hRE
  have ha : ∀ b ∈ E, (∀ t ∈ R, b * t = t * b) → b = 1 := by
    intro b hb hbR
    apply hfaith b hb
    refine Subgroup.mem_centralizer_iff.2 fun k hk => ?_
    exact (radK_aut_trivial hL hKq hChev hZ hQK hQp hQc (hEN hb) (m := 3) (by norm_num) (hEel.2 b hb)
      (fun x hx => hJE x (hQJ hx) b hb) hbR k hk).symm
  have hex : ∃ b ∈ E, b ≠ 1 ∧ ∃ c ∈ R, b * c = c * b ∧ ∃ e ∈ E, e * c ≠ c * e := by
    by_contra hcon
    push Not at hcon
    have hRle : R ≤ Subgroup.centralizer (E : Set Y) :=
      le_of_inf_centralizer_le_three hEel hE9 hRp hRN fun b hb hb1 c hc hbc =>
        Subgroup.mem_centralizer_iff.2 fun e he => hcon b hb hb1 c hc hbc e he
    obtain ⟨e0, he0, he01⟩ : ∃ e0 ∈ E, e0 ≠ 1 := by
      by_contra h
      push Not at h
      have hbot : E = ⊥ := Subgroup.eq_bot_iff_forall _ |>.2 h
      rw [hbot, Subgroup.card_bot] at hE9
      omega
    exact he01 (ha e0 he0 fun t ht => Subgroup.mem_centralizer_iff.1 (hRle ht) e0 he0)
  obtain ⟨b, hbE, hb1, c, hcR, hbc, e, heE, hec⟩ := hex
  set RC : Subgroup Y := R ⊓ Subgroup.centralizer ({b} : Set Y) with hRC
  set S : Subgroup Y := ⁅E, RC⁆ with hS
  have hcRC : c ∈ RC := ⟨hcR, Subgroup.mem_centralizer_singleton_iff.2 hbc.symm⟩
  have hSR : S ≤ R := by
    rw [hS, Subgroup.commutator_le]
    intro e' he' c' hc'
    rw [commutatorElement_def]
    exact R.mul_mem (hRE e' he' c' hc'.1) (R.inv_mem hc'.1)
  have hSne : S ≠ ⊥ := by
    intro hbot
    have hmem : ⁅e, c⁆ ∈ S := Subgroup.commutator_mem_commutator heE hcRC
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hec hmem
  have hSK : S ≤ K := hSR.trans hRK
  have hSp : IsPGroup 2 ↥S := hRp.to_le hSR
  have hSc : ¬ S ≤ centerIn K := not_le_centerIn_of_ne_bot hZ hSp hSne
  have hRCE : ∀ e' ∈ E, ∀ x ∈ RC, e' * x * e'⁻¹ ∈ RC := by
    intro e' he' x hx
    have hxb : x * b = b * x :=
      (Subgroup.mem_centralizer_singleton_iff (g := b) (k := x)).1 hx.2
    refine ⟨hRE e' he' x hx.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    symm
    have hbe : b * e' = e' * b := hEcomm b hbE e' he'
    have hbe' : b * e'⁻¹ = e'⁻¹ * b := by
      calc b * e'⁻¹ = e'⁻¹ * (e' * b) * e'⁻¹ := by group
        _ = e'⁻¹ * (b * e') * e'⁻¹ := by rw [hbe]
        _ = e'⁻¹ * b := by group
    calc b * (e' * x * e'⁻¹) = (b * e') * x * e'⁻¹ := by group
      _ = (e' * b) * x * e'⁻¹ := by rw [hbe]
      _ = e' * (b * x) * e'⁻¹ := by group
      _ = e' * (x * b) * e'⁻¹ := by rw [← hxb]
      _ = e' * x * (b * e'⁻¹) := by group
      _ = e' * x * (e'⁻¹ * b) := by rw [hbe']
      _ = e' * x * e'⁻¹ * b := by group
  have hSE : ∀ e' ∈ E, ∀ s ∈ S, e' * s * e'⁻¹ ∈ S := by
    intro e' he' s hs
    have hmap : S.map (MulAut.conj e').toMonoidHom ≤ S := by
      rw [hS, Subgroup.map_commutator]
      refine Subgroup.commutator_mono ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact E.mul_mem (E.mul_mem he' hx) (E.inv_mem he')
      · rintro _ ⟨x, hx, rfl⟩
        exact hRCE e' he' x hx
    exact hmap ⟨s, hs, rfl⟩
  have hSN : E ≤ Subgroup.normalizer (S : Set Y) := le_normalizer_of_conj_mem hSE
  have hSJ : ∀ s ∈ S, ∀ j ∈ J, j * s = s * j := by
    have hle : S ≤ Subgroup.centralizer (J : Set Y) := by
      rw [hS, Subgroup.commutator_le]
      intro e' he' c' hc'
      rw [commutatorElement_def]
      refine Subgroup.mem_centralizer_iff.2 fun j hj => ?_
      have hc'KC : c' ∈ K ⊓ Subgroup.centralizer ({b} : Set Y) := ⟨hRK hc'.1, hc'.2⟩
      have hj1 : c'⁻¹ * j * c' ∈ J := by
        have := hnormJ b hbE hb1 c'⁻¹ ((K ⊓ Subgroup.centralizer ({b} : Set Y)).inv_mem hc'KC) j hj
        simpa using this
      have hej : e' * j = j * e' := hJE j hj e' he'
      have hej1 : e' * (c'⁻¹ * j * c') = (c'⁻¹ * j * c') * e' := hJE _ hj1 e' he'
      have hej1' : (c'⁻¹ * j * c') * e'⁻¹ = e'⁻¹ * (c'⁻¹ * j * c') := by
        calc (c'⁻¹ * j * c') * e'⁻¹ = e'⁻¹ * (e' * (c'⁻¹ * j * c')) * e'⁻¹ := by group
          _ = e'⁻¹ * ((c'⁻¹ * j * c') * e') * e'⁻¹ := by rw [hej1]
          _ = e'⁻¹ * (c'⁻¹ * j * c') := by group
      calc j * (e' * c' * e'⁻¹ * c'⁻¹) = (j * e') * c' * e'⁻¹ * c'⁻¹ := by group
        _ = (e' * j) * c' * e'⁻¹ * c'⁻¹ := by rw [← hej]
        _ = e' * c' * ((c'⁻¹ * j * c') * e'⁻¹) * c'⁻¹ := by group
        _ = e' * c' * (e'⁻¹ * (c'⁻¹ * j * c')) * c'⁻¹ := by rw [hej1']
        _ = (e' * c' * e'⁻¹ * c'⁻¹) * j := by group
    exact fun s hs j hj => Subgroup.mem_centralizer_iff.1 (hle hs) j hj
  set T : Subgroup Y := radK 2 K S with hTdef
  have hTK : T ≤ K := radK_le 2 K S
  have hTp : IsPGroup 2 ↥T := radK_isPGroup 2 K S
  have hTE : ∀ e' ∈ E, ∀ t ∈ T, e' * t * e'⁻¹ ∈ T := fun e' he' t ht =>
    conj_mem_radK 2 hSK (hEN he') (hSN he') ht
  have hTEN : E ≤ Subgroup.normalizer (T : Set Y) := le_normalizer_of_conj_mem hTE
  have hJSn : ∀ j ∈ J, j ∈ Subgroup.normalizer (S : Set Y) := fun j hj =>
    Subgroup.centralizer_le_normalizer (S : Set Y)
      (Subgroup.mem_centralizer_iff.2 fun s hs => (hSJ s hs j hj).symm)
  have hJT : ∀ j ∈ J, ∀ t ∈ T, j * t * j⁻¹ ∈ T := fun j hj t ht =>
    conj_mem_radK 2 hSK (Subgroup.le_normalizer (hJK hj)) (hJSn j hj) ht
  have hCJ : ∀ j ∈ J, (∀ t ∈ T, j * t = t * j) → ∀ j' ∈ J, j' * j = j * j' := by
    intro j hj hjT
    obtain ⟨t, ht, z, hz, hjz⟩ := radK_constrained hL hKq hChev hZ hSK hSp hSc (hJK hj) (hJSn j hj) hjT
    refine commute_of_forall_commutator_mem_center (y := j) hJq.1 (fun j₂ => ?_)
    have huJ : (j₂ : Y) * j * (j₂ : Y)⁻¹ * j⁻¹ ∈ J :=
      J.mul_mem (J.mul_mem (J.mul_mem j₂.2 hj) (J.inv_mem j₂.2)) (J.inv_mem hj)
    have hzj₂ : z * (j₂ : Y)⁻¹ = (j₂ : Y)⁻¹ * z := by
      obtain ⟨z', hz', rfl⟩ := hz
      exact congrArg Subtype.val
        (Subgroup.mem_center_iff.1 hz' ⟨(j₂ : Y)⁻¹, K.inv_mem (hJK j₂.2)⟩).symm
    have huT : (j₂ : Y) * j * (j₂ : Y)⁻¹ * j⁻¹ ∈ T := by
      rw [hjz]
      have h1 : (j₂ : Y) * (t * z) * (j₂ : Y)⁻¹ * (t * z)⁻¹ =
          ((j₂ : Y) * t * (j₂ : Y)⁻¹) * t⁻¹ := by
        calc (j₂ : Y) * (t * z) * (j₂ : Y)⁻¹ * (t * z)⁻¹
            = (j₂ : Y) * t * (z * (j₂ : Y)⁻¹) * z⁻¹ * t⁻¹ := by group
          _ = (j₂ : Y) * t * ((j₂ : Y)⁻¹ * z) * z⁻¹ * t⁻¹ := by rw [hzj₂]
          _ = ((j₂ : Y) * t * (j₂ : Y)⁻¹) * t⁻¹ := by group
      rw [h1]
      exact T.mul_mem (hJT j₂ j₂.2 t ht) (T.inv_mem ht)
    exact mem_center_of_mem_pGroup hJq h3 hTp hJT _ huJ huT
  have hA : ∀ b₁ ∈ E, b₁ ≠ 1 → ∀ v ∈ T, b₁ * v = v * b₁ → ∀ j ∈ J, j * v = v * j := by
    intro b₁ hb₁ hb11 v hv hbv
    refine commute_of_forall_commutator_mem_center (y := v) hJq.1 (fun j₂ => ?_)
    have hvKC : v ∈ K ⊓ Subgroup.centralizer ({b₁} : Set Y) :=
      ⟨hTK hv, Subgroup.mem_centralizer_singleton_iff.2 hbv.symm⟩
    have huJ : (j₂ : Y) * v * (j₂ : Y)⁻¹ * v⁻¹ ∈ J := by
      have h1 := hnormJ b₁ hb₁ hb11 v hvKC (j₂ : Y)⁻¹ (J.inv_mem j₂.2)
      have h2 := J.mul_mem j₂.2 h1
      simpa [mul_assoc] using h2
    have huT : (j₂ : Y) * v * (j₂ : Y)⁻¹ * v⁻¹ ∈ T :=
      T.mul_mem (hJT j₂ j₂.2 v hv) (T.inv_mem hv)
    exact mem_center_of_mem_pGroup hJq h3 hTp hJT _ huJ huT
  have hTle : T ≤ Subgroup.centralizer (J : Set Y) :=
    le_of_inf_centralizer_le_three hEel hE9 hTp hTEN fun b₁ hb₁ hb11 v hv hbv =>
      Subgroup.mem_centralizer_iff.2 fun j hj => hA b₁ hb₁ hb11 v hv hbv j hj
  have hall : ∀ j ∈ J, ∀ j' ∈ J, j' * j = j * j' := fun j hj =>
    hCJ j hj fun t ht => Subgroup.mem_centralizer_iff.1 (hTle ht) j hj
  have hcenter : ∀ j : ↥J, j ∈ Subgroup.center ↥J := fun j =>
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hall j j.2 g g.2)
  haveI := hJq.2
  have hsub : Subsingleton (↥J ⧸ Subgroup.center ↥J) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact QuotientGroup.eq.2 (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hcenter a)) (hcenter b))
  exact (not_nontrivial_iff_subsingleton.2 hsub) inferInstance

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
