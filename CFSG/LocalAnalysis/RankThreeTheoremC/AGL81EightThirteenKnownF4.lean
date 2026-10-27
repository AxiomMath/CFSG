module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81EightThirteenKnownCore
public import CFSG.RankThree.PartOne.SEITZX.F4Two
public import Certificates.Certificate31031

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open

namespace F4TwoPlanes

section Group

variable {G : Type*} [Group G]

private theorem exists_pow_mul_pow {a b : G} (hab : Commute a b) (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) {g : G} (hg : g ∈ Subgroup.closure ({a, b} : Set G)) :
    ∃ i < 3, ∃ j < 3, g = a ^ i * b ^ j := by
  have key : ∃ i j : ℕ, g = a ^ i * b ^ j := by
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
    | one => exact ⟨0, 0, by simp⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨i, j, rfl⟩ := ihx
      obtain ⟨k, l, rfl⟩ := ihy
      refine ⟨i + k, j + l, ?_⟩
      rw [pow_add, pow_add, mul_assoc, ← mul_assoc (b ^ j), (hab.symm.pow_pow j k).eq]
      group
    | inv x _ ih =>
      obtain ⟨i, j, rfl⟩ := ih
      refine ⟨2 * i, 2 * j, inv_eq_of_mul_eq_one_right ?_⟩
      calc a ^ i * b ^ j * (a ^ (2 * i) * b ^ (2 * j))
          = a ^ i * (b ^ j * a ^ (2 * i)) * b ^ (2 * j) := by group
        _ = a ^ i * (a ^ (2 * i) * b ^ j) * b ^ (2 * j) := by
          rw [(hab.symm.pow_pow j (2 * i)).eq]
        _ = a ^ (3 * i) * b ^ (3 * j) := by
          rw [show 3 * i = i + 2 * i by ring, show 3 * j = j + 2 * j by ring, pow_add, pow_add]
          group
        _ = 1 := by rw [pow_mul, pow_mul, ha, hb, one_pow, one_pow, one_mul]
  obtain ⟨i, j, rfl⟩ := key
  exact ⟨i % 3, Nat.mod_lt _ (by norm_num), j % 3, Nat.mod_lt _ (by norm_num), by
    rw [← pow_eq_pow_mod i ha, ← pow_eq_pow_mod j hb]⟩

private theorem card_closure_pair {a b : G} [Finite G] (hab : Commute a b) (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1)
    (hinj : ∀ i < 3, ∀ j < 3, ∀ k < 3, ∀ l < 3, a ^ i * b ^ j = a ^ k * b ^ l → i = k ∧ j = l) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) = 3 ^ 2 := by
  set X := Subgroup.closure ({a, b} : Set G)
  have haX : a ∈ X := Subgroup.subset_closure (by simp)
  have hbX : b ∈ X := Subgroup.subset_closure (by simp)
  let f : Fin 3 × Fin 3 → X := fun t =>
    ⟨a ^ (t.1 : ℕ) * b ^ (t.2 : ℕ), X.mul_mem (X.pow_mem haX _) (X.pow_mem hbX _)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun s t hst => ?_, fun g => ?_⟩
    · obtain ⟨h1, h2⟩ := hinj _ s.1.2 _ s.2.2 _ t.1.2 _ t.2.2 (congrArg Subtype.val hst)
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · obtain ⟨i, hi, j, hj, hg⟩ := exists_pow_mul_pow hab ha hb g.2
      exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), Subtype.ext hg.symm⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, Nat.card_fin]
  norm_num

private theorem mem_normalizer_of_le_comap [Finite G] {X : Subgroup G} {s : G}
    (h : X ≤ X.comap (MulAut.conj s).toMonoidHom) : s ∈ Subgroup.normalizer (X : Set G) := by
  have hmap : X.map (MulAut.conj s).toMonoidHom = X := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.map_le_iff_le_comap.2 h) ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj s).injective]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h hx, fun hx => ?_⟩
  rw [← hmap] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := by simpa [MulAut.conj_apply] using hyx
  exact this ▸ hy

private theorem mem_normalizer_closure_pair [Finite G] {a b s : G} {i j k l : ℕ}
    (h1 : s * a = a ^ i * b ^ j * s) (h2 : s * b = a ^ k * b ^ l * s) :
    s ∈ Subgroup.normalizer (Subgroup.closure ({a, b} : Set G) : Set G) := by
  set X := Subgroup.closure ({a, b} : Set G)
  have haX : a ∈ X := Subgroup.subset_closure (by simp)
  have hbX : b ∈ X := Subgroup.subset_closure (by simp)
  refine mem_normalizer_of_le_comap ((Subgroup.closure_le _).2 ?_)
  rintro x (rfl | rfl)
  · show s * x * s⁻¹ ∈ X
    rw [h1, mul_inv_cancel_right]
    exact X.mul_mem (X.pow_mem haX _) (X.pow_mem hbX _)
  · show s * x * s⁻¹ ∈ X
    rw [h2, mul_inv_cancel_right]
    exact X.mul_mem (X.pow_mem haX _) (X.pow_mem hbX _)

theorem threePlaneGen_of_four [Finite G] {u v w z : G} (huv : Commute u v) (huw : Commute u w)
    (huz : Commute u z) (hvw : Commute v w) (hvz : Commute v z) (hwz : Commute w z)
    (hu : u ^ 3 = 1) (hv : v ^ 3 = 1) (hw : w ^ 3 = 1) (hz : z ^ 3 = 1)
    (hinj₁ : ∀ i < 3, ∀ j < 3, ∀ k < 3, ∀ l < 3, u ^ i * v ^ j = u ^ k * v ^ l → i = k ∧ j = l)
    (hinj₂ : ∀ i < 3, ∀ j < 3, ∀ k < 3, ∀ l < 3, w ^ i * z ^ j = w ^ k * z ^ l → i = k ∧ j = l)
    (hwuv : ∀ i < 3, ∀ j < 3, w ≠ u ^ i * v ^ j)
    (hgen : Subgroup.normalizer (Subgroup.closure ({u, v} : Set G) : Set G) ⊔
      Subgroup.normalizer (Subgroup.closure ({w, z} : Set G) : Set G) = ⊤) :
    ThreePlaneGen G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E := Subgroup.closure ({u, v, w, z} : Set G)
  have hpair : ({u, v, w, z} : Set G).Pairwise Commute := by
    intro x hx y hy _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first
      | exact Commute.refl _
      | assumption
      | exact Commute.symm (by assumption)
  have hcomm : IsMulCommutative E := Subgroup.isMulCommutative_closure hpair
  have hexp : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    | one => exact one_pow 3
    | mul x y hx hy ihx ihy =>
      have hxy : Commute x y := congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [hxy.mul_pow, ihx, ihy, one_mul]
    | inv x _ ih => rw [inv_pow, ih, inv_one]
  have hEp : IsPGroup 3 E := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact hexp _ x.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have h1E : Subgroup.closure ({u, v} : Set G) ≤ E :=
    Subgroup.closure_mono (by intro x hx; simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx ⊢; tauto)
  have h2E : Subgroup.closure ({w, z} : Set G) ≤ E :=
    Subgroup.closure_mono (by intro x hx; simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx ⊢; tauto)
  have h1c := card_closure_pair huv hu hv hinj₁
  have h2c := card_closure_pair hwz hw hz hinj₂
  have hwE : w ∈ E := Subgroup.subset_closure (by simp)
  have hk3 : 3 ≤ k := by
    have hdvd : 3 ^ 2 ∣ 3 ^ k := h1c ▸ hk ▸ Subgroup.card_dvd_of_le h1E
    have hk2 : 2 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
    by_contra hlt
    have hk' : k = 2 := by omega
    have heq : Subgroup.closure ({u, v} : Set G) = E :=
      Subgroup.eq_of_le_of_card_ge h1E (by rw [hk, h1c, hk'])
    obtain ⟨i, hi, j, hj, hwij⟩ := exists_pow_mul_pow huv hu hv (heq ▸ hwE)
    exact hwuv i hi j hj hwij
  exact ⟨E, _, _, k, ⟨hcomm, hexp⟩, hk3, hk, h1E, h1c, h2E, h2c, hgen⟩

end Group

section Bits

open CFSG.LieType.Simplicity.TitsBits CFSG.RankThree.PartOne.SEITZX CFSG.LieType.Ree
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K] [CharP K 2]

private theorem hasBits_powPair
    {x y : adjointGroup ReeTag.F4.tag K} {X Y : ℕ} (hx : HasBits K x X) (hy : HasBits K y Y)
    (i j : ℕ) : HasBits K (x ^ i * y ^ j) (powPair X Y i j) :=
  (hasBits_pow hx i).mul (hasBits_pow hy j)

private theorem eq_of_eqP
    {g h : adjointGroup ReeTag.F4.tag K} {A B : ℕ} (hg : HasBits K g A) (hh : HasBits K h B)
    (e : eqP A B = true) : g = h :=
  (hg.eq_iff hh).2 (of_decide_eq_true e)

private theorem eqP_of_eq
    {g h : adjointGroup ReeTag.F4.tag K} {A B : ℕ} (hg : HasBits K g A) (hh : HasBits K h B)
    (e : g = h) : eqP A B = true :=
  decide_eq_true ((hg.eq_iff hh).1 e)

private theorem inj_of_nineOK
    {x y : adjointGroup ReeTag.F4.tag K} {X Y : ℕ} (hx : HasBits K x X) (hy : HasBits K y Y)
    (h : nineOK X Y = true) :
    ∀ i < 3, ∀ j < 3, ∀ k < 3, ∀ l < 3, x ^ i * y ^ j = x ^ k * y ^ l → i = k ∧ j = l := by
  intro i hi j hj k hk l hl he
  unfold nineOK at h
  simp only [List.all_eq_true, List.mem_range] at h
  have h' := h i hi j hj k hk l hl
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h'
  rcases h' with h' | h'
  · exact h'
  · have := eqP_of_eq (hasBits_powPair hx hy i j) (hasBits_powPair hx hy k l) he
    rw [h'] at this
    exact absurd this Bool.false_ne_true

private theorem hasBits_prodBits
    (c : TwoPlaneCert) : ∀ idxs : List ℕ,
    HasBits K ((idxs.map fun k => evalG K (wordOfCodes (c.gens.getD k NormGen.one).word)).prod)
      (c.prodBits idxs)
  | [] => hasBits_one
  | k :: ks => by
    rw [List.map_cons, List.prod_cons]
    exact (hasBits_codes _).mul (hasBits_prodBits c ks)

theorem TwoPlaneCert.facts
    (c : TwoPlaneCert) (hc : c.check = true) :
    let e : List ℕ → adjointGroup ReeTag.F4.tag K := fun w => evalG K (wordOfCodes w)
    e c.wu ^ 3 = 1 ∧ e c.wv ^ 3 = 1 ∧ e c.ww ^ 3 = 1 ∧ e c.wz ^ 3 = 1 ∧
    Commute (e c.wu) (e c.wv) ∧ Commute (e c.wu) (e c.ww) ∧ Commute (e c.wu) (e c.wz) ∧
    Commute (e c.wv) (e c.ww) ∧ Commute (e c.wv) (e c.wz) ∧ Commute (e c.ww) (e c.wz) ∧
    (∀ i < 3, ∀ j < 3, ∀ k < 3, ∀ l < 3,
      e c.wu ^ i * e c.wv ^ j = e c.wu ^ k * e c.wv ^ l → i = k ∧ j = l) ∧
    (∀ i < 3, ∀ j < 3, ∀ k < 3, ∀ l < 3,
      e c.ww ^ i * e c.wz ^ j = e c.ww ^ k * e c.wz ^ l → i = k ∧ j = l) ∧
    (∀ i < 3, ∀ j < 3, e c.ww ≠ e c.wu ^ i * e c.wv ^ j) ∧
    (∀ g ∈ c.gens,
      e g.word * e (c.planeX g.second) =
        e (c.planeX g.second) ^ g.i₁ * e (c.planeY g.second) ^ g.j₁ * e g.word ∧
      e g.word * e (c.planeY g.second) =
        e (c.planeX g.second) ^ g.i₂ * e (c.planeY g.second) ^ g.j₂ * e g.word) ∧
    (∀ t < 8, ((c.targets.getD t []).map fun k => e (c.gens.getD k NormGen.one).word).prod =
      e (targetWord t)) := by
  intro e
  unfold TwoPlaneCert.check at hc
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hu, hv⟩, hw⟩, hz⟩, huv⟩, huw⟩, huz⟩, hvw⟩, hvz⟩, hwz⟩, hn₁⟩, hn₂⟩, hwuv⟩,
    hgens⟩, htargets⟩ := hc
  have hU := hasBits_codes (K := K) c.wu
  have hV := hasBits_codes (K := K) c.wv
  have hW := hasBits_codes (K := K) c.ww
  have hZ := hasBits_codes (K := K) c.wz
  refine ⟨eq_of_eqP (hasBits_pow hU 3) hasBits_one hu, eq_of_eqP (hasBits_pow hV 3) hasBits_one hv,
    eq_of_eqP (hasBits_pow hW 3) hasBits_one hw, eq_of_eqP (hasBits_pow hZ 3) hasBits_one hz,
    eq_of_eqP (hU.mul hV) (hV.mul hU) huv, eq_of_eqP (hU.mul hW) (hW.mul hU) huw,
    eq_of_eqP (hU.mul hZ) (hZ.mul hU) huz, eq_of_eqP (hV.mul hW) (hW.mul hV) hvw,
    eq_of_eqP (hV.mul hZ) (hZ.mul hV) hvz, eq_of_eqP (hW.mul hZ) (hZ.mul hW) hwz,
    inj_of_nineOK hU hV hn₁, inj_of_nineOK hW hZ hn₂, ?_, ?_, ?_⟩
  · intro i hi j hj he
    have h' := hwuv i hi j hj
    rw [eqP_of_eq hW (hasBits_powPair hU hV i j) he] at h'
    exact absurd h' (by decide)
  · intro g hg
    have h := hgens g hg
    unfold TwoPlaneCert.relOK at h
    rw [Bool.and_eq_true] at h
    have hS := hasBits_codes (K := K) g.word
    have hX := hasBits_codes (K := K) (c.planeX g.second)
    have hY := hasBits_codes (K := K) (c.planeY g.second)
    exact ⟨eq_of_eqP (hS.mul hX) ((hasBits_powPair hX hY _ _).mul hS) h.1,
      eq_of_eqP (hS.mul hY) ((hasBits_powPair hX hY _ _).mul hS) h.2⟩
  · intro t ht
    exact eq_of_eqP (hasBits_prodBits c _) (hasBits_codes _) (htargets t ht)

end Bits

section Main

open CFSG.LieType.Simplicity.TitsBits CFSG.RankThree.PartOne.SEITZX CFSG.LieType.Ree
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem eq_top_of_targetWord_mem
    (hK : Nat.card K = 2)
    {N : Subgroup (adjointGroup ReeTag.F4.tag K)}
    (htarg : ∀ t < 8, evalG K (wordOfCodes (targetWord t)) ∈ N) : N = ⊤ := by
  rw [eq_top_iff, ← closure_xElement_yElement (τ := ReeTag.F4.tag) (K := K), Subgroup.closure_le]
  rintro _ ⟨i, c', rfl | rfl⟩
  · rcases eq_zero_or_eq_one_of_card_eq_two hK c' with rfl | rfl
    · rw [xElement_zero]
      exact one_mem _
    · have hi : i.val < 4 := i.2
      have := htarg i.val (by omega)
      rwa [show targetWord i.val = targetWord (⟨i.val, hi⟩ : Fin 4).val from rfl,
        evalG_targetWord_x (K := K) ⟨i.val, hi⟩] at this
  · rcases eq_zero_or_eq_one_of_card_eq_two hK c' with rfl | rfl
    · rw [show yElement (τ := ReeTag.F4.tag) (K := K) i 0 = 1 from
        Subtype.ext (Units.ext (yOp_zero i))]
      exact one_mem _
    · have hi : i.val < 4 := i.2
      have := htarg (i.val + 4) (by omega)
      rw [show targetWord (i.val + 4) = targetWord ((⟨i.val, hi⟩ : Fin 4).val + 4) from rfl,
        evalG_targetWord_y (K := K) ⟨i.val, hi⟩] at this
      rw [yElement_one_eq]
      exact this

theorem TwoPlaneCert.normalizer_sup_eq_top
    (hK : Nat.card K = 2)
    (c : TwoPlaneCert) (hc : c.check = true) :
    Subgroup.normalizer (SetLike.coe (Subgroup.closure
        {evalG K (wordOfCodes c.wu), evalG K (wordOfCodes c.wv)})) ⊔
      Subgroup.normalizer (SetLike.coe (Subgroup.closure
        {evalG K (wordOfCodes c.ww), evalG K (wordOfCodes c.wz)})) = ⊤ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hgens, htargets⟩ := c.facts (K := K) hc
  beta_reduce at hgens htargets
  refine eq_top_of_targetWord_mem hK fun t ht => ?_
  rw [← htargets t ht]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  by_cases hk : k < c.gens.length
  · have hmem : c.gens.getD k NormGen.one ∈ c.gens := by
      rw [List.getD_eq_getElem _ _ hk]
      exact List.getElem_mem hk
    obtain ⟨h1, h2⟩ := hgens _ hmem
    cases hb : (c.gens.getD k NormGen.one).second
    · rw [hb] at h1 h2
      exact Subgroup.mem_sup_left (mem_normalizer_closure_pair h1 h2)
    · rw [hb] at h1 h2
      exact Subgroup.mem_sup_right (mem_normalizer_closure_pair h1 h2)
  · rw [List.getD_eq_default _ _ (not_lt.1 hk)]
    simp [NormGen.one, wordOfCodes]

theorem threePlaneGen_F4_two
    (hK : Nat.card K = 2) : ThreePlaneGen (adjointGroup ReeTag.F4.tag K) := by
  have hc : f4ThreePlanes.check = true := Certificates.certificate31031
  obtain ⟨hu, hv, hw, hz, huv, huw, huz, hvw, hvz, hwz, hinj₁, hinj₂, hwuv, -, -⟩ :=
    f4ThreePlanes.facts (K := K) hc
  exact threePlaneGen_of_four huv huw huz hvw hvz hwz hu hv hw hz hinj₁ hinj₂ hwuv
    (f4ThreePlanes.normalizer_sup_eq_top hK hc)

end Main

end F4TwoPlanes

open CFSG.LieType.Ree CFSG.RankThree.PartOne.SEITZX

theorem threeCoreAt_F42 :
    ThreeCoreAt (TauCeti.CFSGIndex.lie CFSG.Assembly.RankThreeEven.f4TwoIndex).Group := by
  obtain ⟨X, _, _, hX, ⟨e⟩⟩ := exists_adjointF4_two_model
    (q := CFSG.Assembly.RankThreeEven.primePowerTwo) rfl rfl
    ⟨CFSG.Assembly.RankThreeEven.f4TwoIndex.2, ⟨MulEquiv.refl _⟩⟩
  have : CharP X 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 1) (le_refl 1) (by simpa using hX)
  exact threeCoreAt_of_threePlaneGen e.symm (F4TwoPlanes.threePlaneGen_F4_two hX)

end CFSG.LocalAnalysis.RankThreeTheoremC
