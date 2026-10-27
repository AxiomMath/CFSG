module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKRank
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.K1.SporadicPerm

theorem eq_of_stronglyClosed_of_witnesses {Γ : Type} [Group Γ] [Finite Γ] {Q R₀ : Subgroup Γ}
    (hQ : IsPGroup 2 Q) (hR : R₀ ≤ Q) (hne : R₀ ≠ ⊥)
    (hnorm : ∀ q ∈ Q, ∀ r ∈ R₀, q * r * q⁻¹ ∈ R₀)
    (hstrong : ∀ r ∈ R₀, r * r = 1 → ∀ g : Γ, g * r * g⁻¹ ∈ Q → g * r * g⁻¹ ∈ R₀) {z : Γ}
    (hz2 : z * z = 1) (hcen : ∀ c ∈ Q, (∀ q ∈ Q, c * q = q * c) → c = 1 ∨ c = z)
    {C : Set Γ} (hCz : ∀ c ∈ C, ∃ g : Γ, g⁻¹ * z * g = c) (hCQ : ∀ c ∈ C, c ∈ Q)
    (hgen : Q ≤ Subgroup.closure C) : R₀ = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hRn : (R₀.subgroupOf Q).Normal := by
    refine ⟨fun x hx y => ?_⟩
    have hx' : (x : Γ) ∈ R₀ := hx
    show (y : Γ) * (x : Γ) * (y : Γ)⁻¹ ∈ R₀
    exact hnorm y y.2 x hx'
  have hRne : R₀.subgroupOf Q ≠ ⊥ := by
    intro hbot
    apply hne
    rw [eq_bot_iff]
    intro a ha
    have : (⟨a, hR ha⟩ : Q) ∈ R₀.subgroupOf Q := ha
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  obtain ⟨c, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hRne)
  have hcR : ((c : Q) : Γ) ∈ R₀ := c.2.1
  have hcQ : ((c : Q) : Γ) ∈ Q := (c : Q).2
  have hcc : ∀ q ∈ Q, ((c : Q) : Γ) * q = q * ((c : Q) : Γ) := by
    intro q hq
    have := Subgroup.mem_center_iff.mp c.2.2 ⟨q, hq⟩
    exact (congrArg Subtype.val this).symm
  have hc1' : ((c : Q) : Γ) ≠ 1 := fun h' => hc1 (Subtype.ext (Subtype.ext h'))
  have hzR : z ∈ R₀ := by
    rcases hcen _ hcQ hcc with h' | h'
    · exact absurd h' hc1'
    · rw [← h']; exact hcR
  have hCR : ∀ c ∈ C, c ∈ R₀ := by
    intro c hc
    obtain ⟨g, hg⟩ := hCz c hc
    have := hstrong z hzR hz2 g⁻¹ (by simpa [hg] using hCQ c hc)
    simpa [hg] using this
  have hQR : Q ≤ R₀ := hgen.trans ((Subgroup.closure_le _).mpr hCR)
  exact le_antisymm hR hQR

@[expose] def StrongCard (X : Type) [Group X] (k : ℕ) : Prop :=
  ∀ U R₀ : Subgroup X, IsSylowTwoOf U ⊤ → R₀ ≤ U → R₀ ≠ ⊥ →
    (∀ u ∈ U, ∀ r ∈ R₀, u * r * u⁻¹ ∈ R₀) →
    (∀ r ∈ R₀, r * r = 1 → ∀ g : X, g * r * g⁻¹ ∈ U → g * r * g⁻¹ ∈ R₀) → Nat.card R₀ = 2 ^ k

theorem StrongCard.of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] {k : ℕ} (e : X ≃* Y)
    (h : StrongCard Y k) : StrongCard X k := by
  intro U R₀ hU hRU hne hnorm hstrong
  have hUY : IsSylowTwoOf (U.map e.toMonoidHom) ⊤ :=
    CFSG.Quasithin.A312.isSylowTwoOf_top_map e.toMonoidHom e.surjective hU
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have := h (U.map e.toMonoidHom) (R₀.map e.toMonoidHom) hUY (Subgroup.map_mono hRU)
    (fun hbot => hne ((Subgroup.map_eq_bot_iff_of_injective R₀ hinj).mp hbot)) ?_ ?_
  · rwa [Subgroup.card_map_of_injective hinj] at this
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨r, hr, rfl⟩
    refine ⟨u * r * u⁻¹, hnorm u hu r hr, ?_⟩
    simp
  · rintro _ ⟨r, hr, rfl⟩ hr2 g hg
    obtain ⟨g', rfl⟩ := e.surjective g
    obtain ⟨u, hu, hue⟩ := hg
    have hr2' : r * r = 1 := by
      apply e.injective
      simpa using hr2
    have hg' : g' * r * g'⁻¹ ∈ U := by
      have : g' * r * g'⁻¹ = u := by
        apply e.injective
        simpa using hue.symm
      rw [this]; exact hu
    exact ⟨g' * r * g'⁻¹, hstrong r hr hr2' g' hg', by simp⟩

@[expose] def StrongCardEx (X : Type) [Group X] (k : ℕ) : Prop :=
  ∃ U : Subgroup X, IsSylowTwoOf U ⊤ ∧ ∀ R₀ : Subgroup X, R₀ ≤ U → R₀ ≠ ⊥ →
    (∀ u ∈ U, ∀ r ∈ R₀, u * r * u⁻¹ ∈ R₀) →
    (∀ r ∈ R₀, r * r = 1 → ∀ g : X, g * r * g⁻¹ ∈ U → g * r * g⁻¹ ∈ R₀) → Nat.card R₀ = 2 ^ k

theorem StrongCard.toEx {X : Type} [Group X] [Finite X] {k : ℕ} (h : StrongCard X k) :
    StrongCardEx X k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := X)
  exact ⟨S, isSylowTwoOf_top_of_sylow S, fun R₀ hR hne hn hs =>
    h S R₀ (isSylowTwoOf_top_of_sylow S) hR hne hn hs⟩

theorem StrongCardEx.of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] {k : ℕ}
    (e : X ≃* Y) (h : StrongCardEx Y k) : StrongCardEx X k := by
  obtain ⟨U, hU, hS⟩ := h
  have hUX : IsSylowTwoOf (U.map e.symm.toMonoidHom) ⊤ :=
    CFSG.Quasithin.A312.isSylowTwoOf_top_map e.symm.toMonoidHom e.symm.surjective hU
  refine ⟨U.map e.symm.toMonoidHom, hUX, fun R₀ hR hne hnorm hstrong => ?_⟩
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hmemU : ∀ x : X, x ∈ U.map e.symm.toMonoidHom → e x ∈ U := by
    rintro x ⟨u, hu, rfl⟩
    simpa using hu
  have hmemU' : ∀ x : X, e x ∈ U → x ∈ U.map e.symm.toMonoidHom := by
    intro x hx
    exact ⟨e x, hx, by simp⟩
  have := hS (R₀.map e.toMonoidHom) ?_ ?_ ?_ ?_
  · rwa [Subgroup.card_map_of_injective hinj] at this
  · rintro _ ⟨r, hr, rfl⟩
    exact hmemU r (hR hr)
  · exact fun hbot => hne ((Subgroup.map_eq_bot_iff_of_injective R₀ hinj).mp hbot)
  · rintro u hu _ ⟨r, hr, rfl⟩
    have hu' : e.symm u ∈ U.map e.symm.toMonoidHom := ⟨u, hu, rfl⟩
    refine ⟨e.symm u * r * (e.symm u)⁻¹, hnorm _ hu' r hr, ?_⟩
    simp
  · rintro _ ⟨r, hr, rfl⟩ hr2 g hg
    have hr2' : r * r = 1 := by
      apply e.injective
      simpa using hr2
    have hg' : e.symm g * r * (e.symm g)⁻¹ ∈ U.map e.symm.toMonoidHom := by
      apply hmemU'
      simpa using hg
    refine ⟨e.symm g * r * (e.symm g)⁻¹, hstrong r hr hr2' (e.symm g) hg', ?_⟩
    simp

namespace FusionCert

@[expose] def wordTab (n : ℕ) (ta tb : Array ℕ) (w : List ℕ) : Array ℕ :=
  w.foldr (fun x acc => compArr (if x = 0 then ta else tb) acc) (Array.range n)

@[expose] def idxTab (n : ℕ) (G : List (Array ℕ)) (g gi : ℕ) (par cl : Array ℕ) :
    ℕ → ℕ → Array ℕ
  | 0, _ => Array.range n
  | f + 1, i =>
    if i = 0 then Array.range n
    else compArr (G.getD (RankCert.genIdx g gi par cl i) #[]) (idxTab n G g gi par cl f par[i]!)

@[expose] def invTabs (n : ℕ) (x y : Array ℕ) : Bool :=
  (List.range n).all (fun q => img y (img x q) == q)

@[expose] def witOK (n : ℕ) (ta tb zt : Array ℕ) (P : List ℕ) (Ts : Array (List ℕ))
    (wit : List ℕ × List ℕ × ℕ) : Bool :=
  decide (wit.2.2 < Ts.size) &&
    invTabs n (wordTab n ta tb wit.1) (wordTab n ta tb wit.2.1) &&
    decide (P.map (conjImg zt (wordTab n ta tb wit.1) (wordTab n ta tb wit.2.1)) =
      Ts[wit.2.2]!)

@[expose] def evalIdxWord (mul : ℕ → ℕ → ℕ) (cidx : List ℕ) (w : List ℕ) : ℕ :=
  w.foldr (fun p acc => mul (cidx.getD p 0) acc) 0

@[expose] def fusionCheck (n : ℕ) (B : List ℕ) (ta tb : Array ℕ) (G : List (Array ℕ))
    (Ts : Array (List ℕ)) (par cl : Array ℕ) (zi : ℕ) (wits : List (List ℕ × List ℕ × ℕ))
    (gws : List (List ℕ)) : Bool :=
  let N := Ts.size
  let g := G.length
  let mul := RankCert.mulIdx g g par cl N
  let zt := idxTab n G g g par cl N zi
  decide (zi < N) && zi != 0 && mul zi zi == 0 &&
    (List.range g).all (fun j => mul cl[j]! zi == mul zi cl[j]!) &&
    (List.range N).all (fun i =>
      !((List.range g).all fun j => mul cl[j]! i == mul i cl[j]!) || i == 0 || i == zi) &&
    wits.all (witOK n ta tb zt (ptsOf B G) Ts) &&
    (List.range g).all (fun j =>
      evalIdxWord mul (wits.map fun w => w.2.2) (gws.getD j []) == cl[j]!)

section Semantics

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem tab_one : tab n (1 : Γ) = List.range n := by
  simp [tab, one_smul]

@[expose] def wordElt (a b : Γ) (w : List ℕ) : Γ :=
  (w.map fun x => if x = 0 then a else b).prod

theorem wordTab_spec (a b : Γ) (w : List ℕ) :
    (wordTab n (tab n a).toArray (tab n b).toArray w).toList = tab n (wordElt a b w) := by
  induction w with
  | nil => simp [wordTab, wordElt, tab_one]
  | cons x w ih =>
    have h1 : wordTab n (tab n a).toArray (tab n b).toArray (x :: w) =
        compArr (if x = 0 then (tab n a).toArray else (tab n b).toArray)
          (wordTab n (tab n a).toArray (tab n b).toArray w) := rfl
    have h2 : wordElt a b (x :: w) = (if x = 0 then a else b) * wordElt a b w := by
      simp [wordElt]
    rw [h1, h2, compArr_toList, ih, tab_mul]
    by_cases hx : x = 0 <;> simp [hx]

theorem idxTab_spec {gens : List Γ} {N : ℕ} {par cl : Array ℕ} {ι : ℕ → Γ}
    (h : RankCert.Cayley N gens.length gens.length par cl gens ι) :
    ∀ (f i : ℕ), i ≤ f → i < N →
      (idxTab n (genTabs n gens) gens.length gens.length par cl f i).toList = tab n (ι i) := by
  intro f
  induction f with
  | zero =>
    intro i hif hi
    obtain rfl : i = 0 := by omega
    simp [idxTab, h.zero, tab_one]
  | succ f ih =>
    intro i hif hi
    by_cases hi0 : i = 0
    · subst hi0
      simp [idxTab, h.zero, tab_one]
    · have hpos : 0 < i := Nat.pos_of_ne_zero hi0
      obtain ⟨hgi, hιi, -⟩ := h.genIdx_spec hi hpos
      obtain ⟨hlt, -⟩ := h.parent i hi hpos
      have hGj : (genTabs n gens).getD (RankCert.genIdx gens.length gens.length par cl i) #[] =
          (tab n (gens.getD (RankCert.genIdx gens.length gens.length par cl i) 1)).toArray := by
        simp [genTabs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hgi]
      simp only [idxTab, hi0, ite_false]
      rw [hGj, compArr_toList, ih par[i]! (by omega) (hlt.trans hi), hιi, tab_mul]

theorem evalIdxWord_cons (mul : ℕ → ℕ → ℕ) (cidx : List ℕ) (q : ℕ) (w : List ℕ) :
    evalIdxWord mul cidx (q :: w) = mul (cidx.getD q 0) (evalIdxWord mul cidx w) := rfl

theorem evalIdxWord_nil (mul : ℕ → ℕ → ℕ) (cidx : List ℕ) : evalIdxWord mul cidx [] = 0 := rfl

theorem evalIdxWord_spec {gens : List Γ} {N : ℕ} {par cl : Array ℕ} {ι : ℕ → Γ}
    (h : RankCert.Cayley N gens.length gens.length par cl gens ι) (cidx : List ℕ)
    (hc : ∀ p ∈ cidx, p < N) :
    ∀ w : List ℕ,
      evalIdxWord (RankCert.mulIdx gens.length gens.length par cl N) cidx w < N ∧
      ι (evalIdxWord (RankCert.mulIdx gens.length gens.length par cl N) cidx w) =
        (w.map fun q => ι (cidx.getD q 0)).prod := by
  intro w
  induction w with
  | nil =>
    simp [evalIdxWord_nil, h.zero, h.pos]
  | cons q w ih =>
    obtain ⟨h1, h2⟩ := ih
    have hq : cidx.getD q 0 < N := by
      by_cases hqlt : q < cidx.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hqlt]
        exact hc _ (List.getElem_mem hqlt)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        exact h.pos
    obtain ⟨h3, h4⟩ := h.mulIdx_spec N (cidx.getD q 0) _ (le_of_lt hq) hq h1
    rw [evalIdxWord_cons]
    refine ⟨h3, ?_⟩
    rw [h4, h2, List.map_cons, List.prod_cons]

theorem conj_of_witOK {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (a b z : Γ) {P : List ℕ}
    (hP : ∀ p ∈ P, p < n) (Ts : Array (List ℕ))
    {wit : List ℕ × List ℕ × ℕ}
    (hwit : witOK n (tab n a).toArray (tab n b).toArray (tab n z).toArray P Ts wit = true) :
    ∃ g : Γ, rt n P (g⁻¹ * z * g) = Ts[wit.2.2]! := by
  simp only [witOK, invTabs, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, beq_iff_eq] at hwit
  obtain ⟨⟨hci, hinvt⟩, heq⟩ := hwit
  set g : Γ := wordElt a b wit.1 with hg
  set gi : Γ := wordElt a b wit.2.1 with hgi
  have hwg : wordTab n (tab n a).toArray (tab n b).toArray wit.1 = (tab n g).toArray := by
    rw [← wordTab_spec a b wit.1, Array.toArray_toList]
  have hwgi : wordTab n (tab n a).toArray (tab n b).toArray wit.2.1 = (tab n gi).toArray := by
    rw [← wordTab_spec a b wit.2.1, Array.toArray_toList]
  rw [hwg, hwgi] at hinvt heq
  have hinv : gi = g⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    apply hbase
    intro b' hb'
    rw [act_mul _ _ (hB b' hb')]
    have := hinvt b' (hB b' hb')
    simpa only [img_tab] using this
  refine ⟨g, ?_⟩
  rw [← heq, hinv]
  unfold rt
  apply List.map_congr_left
  intro p hp
  exact act_conj z g (hP p hp)

theorem lt_of_witOK {zt : Array ℕ} {P : List ℕ} {Ts : Array (List ℕ)} {ta tb : Array ℕ}
    {wit : List ℕ × List ℕ × ℕ} (hwit : witOK n ta tb zt P Ts wit = true) : wit.2.2 < Ts.size := by
  simp only [witOK, Bool.and_eq_true, decide_eq_true_eq] at hwit
  exact hwit.1.1

end Semantics

section Main

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem strongCard_of_fusionCheck {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (a b : Γ) (gens : List Γ)
    (Ts : Array (List ℕ)) (par cl : Array ℕ) (k m : ℕ) (hcard : Nat.card Γ = 2 ^ k * m)
    (hm : Odd m) (hEnum : BaseEnumOK n B (genTabs n gens) (genTabsInv n gens) Ts par cl)
    (hsize : Ts.size = 2 ^ k) {zi : ℕ} {wits : List (List ℕ × List ℕ × ℕ)}
    {gws : List (List ℕ)}
    (hcheck : fusionCheck n B (tab n a).toArray (tab n b).toArray (genTabs n gens) Ts par cl zi
      wits gws = true) :
    ∀ U R₀ : Subgroup Γ, IsSylowTwoOf U ⊤ → R₀ ≤ U → R₀ ≠ ⊥ →
      (∀ u ∈ U, ∀ r ∈ R₀, u * r * u⁻¹ ∈ R₀) →
      (∀ r ∈ R₀, r * r = 1 → ∀ g : Γ, g * r * g⁻¹ ∈ U → g * r * g⁻¹ ∈ R₀) →
      Nat.card R₀ = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι, hcay, hιQ, hsurj, hιrt⟩ :=
    RankCert.exists_cayley_of_baseEnum hB hbase gens Ts par cl hEnum
  set Q : Subgroup Γ := Subgroup.closure {x | x ∈ gens} with hQ
  have hcardQ : Nat.card Q = 2 ^ k := by
    rw [hQ, benum_card hB hbase gens Ts par cl hEnum, hsize]
  have hQp2 : IsPGroup 2 Q := IsPGroup.of_card hcardQ
  have hQindex : Q.index = m := by
    have h1 := Q.card_mul_index
    rw [hcardQ, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hQsyl : IsSylowTwoOf Q ⊤ := K1.isSylowTwoOf_top_iff.mpr ⟨hQp2, by
    rw [hQindex]; exact fun hd => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hd)⟩
  have hgl : (genTabs n gens).length = gens.length := by simp [genTabs]
  simp only [fusionCheck, hgl, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at hcheck
  obtain ⟨⟨⟨⟨⟨⟨hzN, hz0⟩, hzz⟩, hzc⟩, hcen⟩, hwits⟩, hgw⟩ := hcheck
  set mulI := RankCert.mulIdx gens.length gens.length par cl Ts.size with hmulI
  have hmul : ∀ i k, i < Ts.size → k < Ts.size →
      mulI i k < Ts.size ∧ ι (mulI i k) = ι i * ι k :=
    fun i k hi hk => hcay.mulIdx_spec Ts.size i k (le_of_lt hi) hi hk
  have hP := ptsOf_lt hB gens
  have hBP : ∀ b ∈ B, b ∈ ptsOf B (genTabs n gens) := fun b hb => List.mem_append_left _ hb
  have hinjrt : ∀ {x y : Γ}, rt n (ptsOf B (genTabs n gens)) x = rt n (ptsOf B (genTabs n gens)) y →
      x = y := fun h => rt_injective hB hBP hbase h
  set z : Γ := ι zi with hz
  have hzQ : z ∈ Q := hιQ zi hzN
  have hz2 : z * z = 1 := by
    obtain ⟨h1, h2⟩ := hmul zi zi hzN hzN
    rw [← h2, hzz, hcay.zero]
  have hgen_idx : ∀ j < gens.length, cl[j]! < Ts.size ∧ ι cl[j]! = gens.getD j 1 := by
    intro j hj
    obtain ⟨h1, h2⟩ := hcay.step 0 hcay.pos j hj
    simp only [Nat.zero_mul, Nat.zero_add] at h1 h2
    exact ⟨h1, by rw [h2, hcay.zero, mul_one]⟩
  have hgenQ : ∀ j < gens.length, gens.getD j 1 ∈ Q := by
    intro j hj
    obtain ⟨h1, h2⟩ := hgen_idx j hj
    rw [← h2]
    exact hιQ _ h1
  have hcenQ : ∀ c ∈ Q, (∀ q ∈ Q, c * q = q * c) → c = 1 ∨ c = z := by
    intro c hc hcc
    obtain ⟨i, hiN, rfl⟩ := hsurj c hc
    have hall : (List.range gens.length).all (fun j => mulI cl[j]! i == mulI i cl[j]!) = true := by
      rw [List.all_eq_true]
      intro j hj
      rw [List.mem_range] at hj
      obtain ⟨hclj, hιj⟩ := hgen_idx j hj
      obtain ⟨h1, h2⟩ := hmul cl[j]! i hclj hiN
      obtain ⟨h3, h4⟩ := hmul i cl[j]! hiN hclj
      rw [beq_iff_eq]
      apply hcay.inj _ h1 _ h3
      rw [h2, h4]
      exact (hcc (ι cl[j]!) (hιQ _ hclj)).symm
    rcases hcen i hiN with (h1 | h1) | h1
    · rw [hall] at h1
      exact absurd h1 (by simp)
    · left
      rw [h1, hcay.zero]
    · right
      rw [h1]
  set C : Set Γ := {c | ∃ wit ∈ wits, c = ι wit.2.2} with hC
  have hzt : idxTab n (genTabs n gens) gens.length gens.length par cl Ts.size zi =
      (tab n z).toArray := by
    have h1 := idxTab_spec (n := n) hcay Ts.size zi (le_of_lt hzN) hzN
    calc idxTab n (genTabs n gens) gens.length gens.length par cl Ts.size zi
        = (idxTab n (genTabs n gens) gens.length gens.length par cl Ts.size zi).toList.toArray :=
          Array.toArray_toList.symm
      _ = (tab n z).toArray := by rw [h1]
  have hCz : ∀ c ∈ C, ∃ g : Γ, g⁻¹ * z * g = c := by
    rintro c ⟨wit, hwit, rfl⟩
    have hw := hwits wit hwit
    rw [hzt] at hw
    obtain ⟨g, hg⟩ := conj_of_witOK hB hbase a b z hP Ts hw
    refine ⟨g, hinjrt ?_⟩
    rw [hg, hιrt _ (lt_of_witOK hw)]
  have hCQ : ∀ c ∈ C, c ∈ Q := by
    rintro c ⟨wit, hwit, rfl⟩
    exact hιQ _ (lt_of_witOK (hwits wit hwit))
  have hgenC : Q ≤ Subgroup.closure C := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx
    have hxj : gens.getD j 1 = x := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, hjx]
    obtain ⟨hclj, hιj⟩ := hgen_idx j hj
    have hev := hgw j hj
    set cidx := wits.map fun w => w.2.2 with hcidx
    have hcN : ∀ p ∈ cidx, p < Ts.size := by
      intro p hp
      obtain ⟨wit, hwit, rfl⟩ := List.mem_map.mp hp
      exact lt_of_witOK (hwits wit hwit)
    have hfac : ∀ q : ℕ, ι (cidx.getD q 0) ∈ Subgroup.closure C := by
      intro q
      by_cases hq : q < cidx.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
        obtain ⟨wit, hwit, hwq⟩ := List.mem_map.mp (List.getElem_mem hq)
        simp only [Option.getD_some]
        rw [← hwq]
        exact Subgroup.subset_closure ⟨wit, hwit, rfl⟩
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        simp only [Option.getD_none]
        rw [hcay.zero]
        exact one_mem _
    have hspec := evalIdxWord_spec hcay cidx hcN (gws.getD j [])
    have hprod : ((gws.getD j []).map fun q => ι (cidx.getD q 0)).prod ∈ Subgroup.closure C :=
      Subgroup.list_prod_mem _ (by
        intro y hy
        obtain ⟨q, -, rfl⟩ := List.mem_map.mp hy
        exact hfac q)
    rw [← hxj, ← hιj, ← hev, hspec.2]
    exact hprod
  intro U R₀ hU hRU hne hnorm hstrong
  obtain ⟨g₀, hg₀⟩ := Vol2Native.A312L.exists_conj_of_isSylowTwoOf hU hQsyl
  set R₁ : Subgroup Γ := R₀.map (MulAut.conj g₀).toMonoidHom with hR₁
  have hR1Q : R₁ ≤ Q := by
    rw [← hg₀]
    exact Subgroup.map_mono hRU
  have hne1 : R₁ ≠ ⊥ := by
    intro h
    exact hne ((Subgroup.map_eq_bot_iff_of_injective R₀
      (f := (MulAut.conj g₀).toMonoidHom) (MulAut.conj g₀).injective).mp h)
  have hnorm1 : ∀ q ∈ Q, ∀ r ∈ R₁, q * r * q⁻¹ ∈ R₁ := by
    intro q hq r hr
    rw [← hg₀] at hq
    obtain ⟨u, hu, rfl⟩ := hq
    obtain ⟨r₀, hr₀, rfl⟩ := hr
    refine ⟨u * r₀ * u⁻¹, hnorm u hu r₀ hr₀, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hstrong1 : ∀ r ∈ R₁, r * r = 1 → ∀ g : Γ, g * r * g⁻¹ ∈ Q → g * r * g⁻¹ ∈ R₁ := by
    intro r hr hr2 g hg
    obtain ⟨r₀, hr₀, rfl⟩ := hr
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 hg ⊢
    have hr02 : r₀ * r₀ = 1 := by
      have : g₀ * (r₀ * r₀) * g₀⁻¹ = 1 := by rw [← hr2]; group
      simpa using this
    rw [← hg₀] at hg
    obtain ⟨u, hu, hue⟩ := hg
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hue
    have hgU : (g₀⁻¹ * g * g₀) * r₀ * (g₀⁻¹ * g * g₀)⁻¹ ∈ U := by
      have : (g₀⁻¹ * g * g₀) * r₀ * (g₀⁻¹ * g * g₀)⁻¹ = u := by
        have h2 : u = g₀⁻¹ * (g * (g₀ * r₀ * g₀⁻¹) * g⁻¹) * g₀ := by
          rw [← hue]; group
        rw [h2]; group
      rw [this]
      exact hu
    have h3 := hstrong r₀ hr₀ hr02 _ hgU
    refine ⟨_, h3, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hR1 : R₁ = Q := eq_of_stronglyClosed_of_witnesses hQp2 hR1Q hne1 hnorm1 hstrong1 hz2
    hcenQ hCz hCQ hgenC
  have hcardR : Nat.card R₁ = Nat.card R₀ :=
    Subgroup.card_map_of_injective (f := (MulAut.conj g₀).toMonoidHom)
      (MulAut.conj g₀).injective
  rw [← hcardR, hR1, hcardQ]

end Main

section SLP

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]

@[expose] def FusionCertT (n : ℕ) (B : List ℕ) (ta tb : Array ℕ) (T : Array (Array ℕ))
    (qp : List (ℕ × ℕ)) (Ts : Array (List ℕ)) (par cl : Array ℕ) (k zi : ℕ)
    (wits : List (List ℕ × List ℕ × ℕ)) (gws : List (List ℕ)) : Prop :=
  (∀ p ∈ qp, p.1 < T.size ∧ p.2 < T.size) ∧
  (∀ p ∈ qp, ∀ q < n, img T[p.2]! (img T[p.1]! q) = q) ∧
  BaseEnumOK n B (qp.map fun p => T[p.1]!) (qp.map fun p => T[p.2]!) Ts par cl ∧
  Ts.size = 2 ^ k ∧
  fusionCheck n B ta tb (qp.map fun p => T[p.1]!) Ts par cl zi wits gws = true

instance (n : ℕ) (B : List ℕ) (ta tb : Array ℕ) (T : Array (Array ℕ)) (qp : List (ℕ × ℕ))
    (Ts : Array (List ℕ)) (par cl : Array ℕ) (k zi : ℕ) (wits : List (List ℕ × List ℕ × ℕ))
    (gws : List (List ℕ)) : Decidable (FusionCertT n B ta tb T qp Ts par cl k zi wits gws) := by
  unfold FusionCertT; infer_instance

@[expose] def FusionCertS (n : ℕ) (B : List ℕ) (ta tb : Array ℕ) (prog : List (ℕ × ℕ))
    (qp : List (ℕ × ℕ)) (Ts : Array (List ℕ)) (par cl : Array ℕ) (k zi : ℕ)
    (wits : List (List ℕ × List ℕ × ℕ)) (gws : List (List ℕ)) : Prop :=
  FusionCertT n B ta tb (slpTabsA ta tb prog) qp Ts par cl k zi wits gws

instance (n : ℕ) (B : List ℕ) (ta tb : Array ℕ) (prog : List (ℕ × ℕ)) (qp : List (ℕ × ℕ))
    (Ts : Array (List ℕ)) (par cl : Array ℕ) (k zi : ℕ) (wits : List (List ℕ × List ℕ × ℕ))
    (gws : List (List ℕ)) : Decidable (FusionCertS n B ta tb prog qp Ts par cl k zi wits gws) := by
  unfold FusionCertS; infer_instance

theorem strongCard_of_fusionCertS {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (a b : Γ) (prog : List (ℕ × ℕ))
    (hv : slpValidAux prog 2 = true) (qp : List (ℕ × ℕ)) (Ts : Array (List ℕ)) (par cl : Array ℕ)
    (k zi : ℕ) (wits : List (List ℕ × List ℕ × ℕ)) (gws : List (List ℕ)) (m : ℕ)
    (hcard : Nat.card Γ = 2 ^ k * m) (hm : Odd m)
    (hcert : FusionCertS n B (tab n a).toArray (tab n b).toArray prog qp Ts par cl k zi wits gws) :
    StrongCard Γ k := by
  obtain ⟨hqp, hinvt, hEnum, hsize, hcheck⟩ := hcert
  set T := slpTabsA (tab n a).toArray (tab n b).toArray prog with hT
  have hinv := slp_foldl_inv (n := n) prog #[a, b] #[(tab n a).toArray, (tab n b).toArray]
    (by simp) (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) hv
  have hE : ∀ i < T.size, tab n ((slpElts a b prog).getD i 1) = (T[i]!).toList := hinv.2
  have hE' : ∀ i < T.size, (tab n ((slpElts a b prog).getD i 1)).toArray = T[i]! := by
    intro i hi
    rw [hE i hi, Array.toArray_toList]
  have hinv_of : ∀ x y : Γ,
      (∀ q < n, img (tab n y).toArray (img (tab n x).toArray q) = q) → y = x⁻¹ := by
    intro x y hxy
    apply eq_inv_of_mul_eq_one_left
    apply hbase
    intro b hb
    rw [act_mul _ _ (hB b hb)]
    have := hxy b (hB b hb)
    simpa only [img_tab] using this
  set gens : List Γ := qp.map fun p => (slpElts a b prog).getD p.1 1 with hgens
  have hG : genTabs n gens = qp.map fun p => T[p.1]! := by
    simp only [genTabs, hgens, List.map_map]
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp_apply]
    exact hE' p.1 (hqp p hp).1
  have hGi : genTabsInv n gens = qp.map fun p => T[p.2]! := by
    simp only [genTabsInv, hgens, List.map_map]
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp_apply]
    have h1 : (slpElts a b prog).getD p.2 1 = ((slpElts a b prog).getD p.1 1)⁻¹ := by
      apply hinv_of
      rw [hE' p.1 (hqp p hp).1, hE' p.2 (hqp p hp).2]
      exact hinvt p hp
    rw [← h1]
    exact hE' p.2 (hqp p hp).2
  rw [← hG, ← hGi] at hEnum
  rw [← hG] at hcheck
  exact strongCard_of_fusionCheck hB hbase a b gens Ts par cl k m hcard hm hEnum hsize hcheck

end SLP

end FusionCert

end CFSG.QuasithinUnique.Lin2
