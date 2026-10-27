module

public import CFSG.CGT.PushingUpLit.BHS.FourFiveE

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem Hyp41.conjSub_mem_dCore {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}
    {M : Subgroup (MulAut V)} (h : Hyp41 P D) {A : Subgroup (MulAut V)}
    (hA : A ∈ dCore P D M) {x : MulAut V} (hx : x ∈ P) : conjSub x A ∈ dCore P D M := by
  refine ⟨h.conj_mem A hA.1 x hx, fun g hg => ?_⟩
  have h1 := conjSub_mono x (hA.2 (x⁻¹ * g) (P.mul_mem (P.inv_mem hx) hg))
  rwa [← conjSub_mul, mul_inv_cancel_left] at h1

theorem not_mem_dCore_of_sylow {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}
    {M L : Subgroup (MulAut V)} (h : Hyp41 P D) (hL : L ∈ lamSet P D M)
    {A : Subgroup (MulAut V)} (hA : IsSylowOf 2 A L) : A ∉ dCore P D M := by
  intro hAc
  obtain ⟨hLP, ⟨n, hn1, hSL⟩, hΛ2, hΛ3⟩ := hL
  obtain ⟨A', hA', hne⟩ := hSL.exists_sylow_ne hn1 hA
  obtain ⟨x, hxL, rfl⟩ := IsSLNatSection.sylow_conj hA hA'
  have hAc' := h.conjSub_mem_dCore hAc (hLP hxL)
  have hAD : A ∈ dInter D L := (hΛ2 A).2 hA
  have hA'D : conjSub x A ∈ dInter D L := (hΛ2 _).2 hA'
  have heq : mSet P M A = mSet P M (conjSub x A) := by
    ext Y
    constructor
    · rintro ⟨⟨g, hg, rfl⟩, -⟩
      exact ⟨⟨g, hg, rfl⟩, hAc'.2 g hg⟩
    · rintro ⟨⟨g, hg, rfl⟩, -⟩
      exact ⟨⟨g, hg, rfl⟩, hAc.2 g hg⟩
  exact hΛ3 A hAD _ hA'D (Ne.symm hne) heq

theorem four_seventeen {P : Subgroup (MulAut V)}
    {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)} (h : Hyp43 P D T M)
    (hV : ∀ v : V, v ^ 2 = 1) {L B : Subgroup (MulAut V)} (hL : L ∈ lamSet P D M)
    (hq : ∀ X ∈ dInter D L, 3 ≤ Nat.card X) (hB : B ∈ D) :
    B ≤ L ∨ ∀ l ∈ L, ∀ b ∈ B, l * b = b * l := by
  by_cases hBL : B ≤ L
  · exact Or.inl hBL
  right
  by_contra hnc
  push Not at hnc
  obtain ⟨A, n, d, -⟩ := exists_hyp413Comm h.toHyp42 hV hL hB hnc hBL
  have hn1 : 1 ≤ n := d.one_le
  have hAsyl : IsSylowOf 2 A L := d.sylowA
  have hAD : A ∈ dInter D L := (d.lam.2.2.1 A).2 hAsyl
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have h1 : n = 1 := by omega
    have h2 := hq A hAD
    rw [d.card_A, h1] at h2
    omega
  obtain ⟨K, hKL, hKA, hKsup, hKcard, hKfpf⟩ := d.sl.exists_complement hn1 hAsyl
  have h2n : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨k₀, hk₀K, hk₀1⟩ : ∃ k ∈ K, k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : K = ⊥ := eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (hcon x hx)
    rw [this, Subgroup.card_bot] at hKcard
    omega
  have hKodd : Odd (Nat.card K) := by
    rw [hKcard]
    have hev : Even (2 ^ n) := (Nat.even_pow' (by omega)).2 even_two
    obtain ⟨m, hm⟩ := hev
    exact ⟨m - 1, by omega⟩
  have hKnorm : ∀ k ∈ K, conjSub k A = A := fun k hk => by
    have : k ∈ K ⊔ A := Subgroup.mem_sup_left hk
    rw [hKsup] at this
    exact conjSub_eq_of_mem_normalizer this.1
  have hKP : K ≤ P := hKL.trans d.lam.1
  have hFsub : ∀ k ∈ K, ∀ z ∈ fixV (L ⊔ B), k z = z := fun k hk z hz =>
    hz k (Subgroup.mem_sup_left (hKL hk))
  have hXK : ∀ k ∈ K, ∀ x ∈ fixV (A ⊔ B), k x ∈ fixV (A ⊔ B) := by
    intro k hk x hx
    have hmap := map_commV_sup_of_fix (hFsub k hk) A
    rw [hKnorm k hk] at hmap
    rw [← d.commV_sup_eq] at hx ⊢
    have : k x ∈ (commV A ⊔ fixV (L ⊔ B)).map (k : MulAut V).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [hmap] at this
  set Bk : Subgroup (MulAut V) := ⨆ k : K, conjSub (k : MulAut V) B with hBk
  have hBkle : ∀ k ∈ K, conjSub k B ≤ Bk := fun k hk =>
    le_iSup (fun k : K => conjSub (k : MulAut V) B) ⟨k, hk⟩
  have hBBk : B ≤ Bk := by
    have := hBkle 1 K.one_mem
    rwa [conjSub_one] at this
  have hBkP : Bk ≤ P := iSup_le fun k => Glauberman.map_conj_le (hKP k.2) (h.le B hB)
  have hXle : fixV (A ⊔ B) ≤ fixV (A ⊔ Bk) := by
    have hA' : A ≤ cenIn ⊤ (fixV (A ⊔ B)) := fun a ha =>
      ⟨Subgroup.mem_top _, fun x hx => hx a (Subgroup.mem_sup_left ha)⟩
    have hBk' : Bk ≤ cenIn ⊤ (fixV (A ⊔ B)) := iSup_le fun k => by
      rintro _ ⟨b, hb, rfl⟩
      refine ⟨Subgroup.mem_top _, fun x hx => ?_⟩
      have hkx : (k : MulAut V)⁻¹ x ∈ fixV (A ⊔ B) := hXK _ (K.inv_mem k.2) x hx
      have hbx := hkx b (Subgroup.mem_sup_right hb)
      show ((k : MulAut V) * b * (k : MulAut V)⁻¹) x = x
      simp only [MulAut.mul_apply]
      rw [hbx]
      simp
    exact fun x hx g hg => ((sup_le hA' hBk' : A ⊔ Bk ≤ cenIn ⊤ (fixV (A ⊔ B))) hg).2 x hx
  have hcommE : commV (A ⊔ Bk) ≤ fixV (A ⊔ B) := by
    rw [B19.commV_sup, hBk, B19.commV_iSup]
    refine sup_le d.commV_A_le (iSup_le fun k => ?_)
    show commV (B.map (MulAut.conj (k : MulAut V)).toMonoidHom) ≤ _
    rw [B19.commV_map_conj]
    rintro _ ⟨u, hu, rfl⟩
    exact hXK _ k.2 u (d.commV_B_le hu)
  have hquad : IsQuadratic (A ⊔ Bk) := hcommE.trans hXle
  have hEel : IsElemAbelian2 (A ⊔ Bk) := isElemAbelian2_of_isQuadratic hV hquad
  have hEP : A ⊔ Bk ≤ P := sup_le (h.le A d.memA) hBkP
  have hmax := h.max A d.memA (A ⊔ Bk) hEel hEP
  have hAB := h.card_prod A d.memA B d.memB (Ne.symm d.ne) d.comm
  have hcardV := h.card_eq A d.memA
  have hinf : A ⊓ B = ⊥ := by
    rcases h.toHyp41.eq_or_inf_eq_bot d.memA d.memB with h1 | h1
    · exact absurd h1 d.ne
    · exact h1
  have hcardAB : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
    have := card_sup_mul_card_inf' (X := A) (Y := B) d.comm
    rwa [hinf, Subgroup.card_bot, mul_one] at this
  have hXpos : 0 < Nat.card ↥(fixV (A ⊔ B)) := Nat.card_pos
  have hEle : Nat.card ↥(A ⊔ Bk) ≤ Nat.card ↥(A ⊔ B) := by
    have h1 : Nat.card ↥(fixV (A ⊔ B)) ≤ Nat.card ↥(fixV (A ⊔ Bk)) :=
      Subgroup.card_le_of_le hXle
    refine Nat.le_of_mul_le_mul_right ?_ hXpos
    calc Nat.card ↥(A ⊔ Bk) * Nat.card ↥(fixV (A ⊔ B))
        ≤ Nat.card ↥(A ⊔ Bk) * Nat.card ↥(fixV (A ⊔ Bk)) := Nat.mul_le_mul_left _ h1
      _ ≤ Nat.card A * Nat.card ↥(fixV A) := hmax
      _ = Nat.card V := hcardV.symm
      _ = Nat.card ↥(A ⊔ B) * Nat.card ↥(fixV (A ⊔ B)) := by rw [hcardAB, ← hAB]
  have hEeq : A ⊔ B = A ⊔ Bk :=
    Subgroup.eq_of_le_of_card_ge (sup_le_sup_left hBBk A) hEle
  have hBkAB : Bk ≤ A ⊔ B := by
    rw [hEeq]
    exact le_sup_right
  have hAc : A ∉ dCore P D M := not_mem_dCore_of_sylow h.toHyp41 d.lam hAsyl
  have h416 := four_sixteen h hV d.memA d.memB d.comm hAc
  have hKB : ∀ k ∈ K, conjSub k B = B := by
    intro k hk
    rcases h416 _ (h.conj_mem B d.memB k (hKP hk)) ((hBkle k hk).trans hBkAB) with h1 | h1
    · exfalso
      have hBA : B = A := by
        rw [← FourTwoTools.conjSub_inv_conjSub k B, h1, hKnorm k⁻¹ (K.inv_mem hk)]
      exact d.ne hBA.symm
    · exact h1
  have hYK : ∀ k ∈ K, ∀ y ∈ fixV B, k y ∈ fixV B := by
    intro k hk y hy b hb
    have hb' : (k : MulAut V)⁻¹ * b * ((k : MulAut V)⁻¹)⁻¹ ∈ B := by
      have h1 : conjSub (k : MulAut V)⁻¹ B = B := hKB _ (K.inv_mem hk)
      rw [← h1]
      exact ⟨b, hb, rfl⟩
    have h2 := hy _ hb'
    have h3 : b (k y) = k (((k : MulAut V)⁻¹ * b * ((k : MulAut V)⁻¹)⁻¹) y) := by
      simp [MulAut.mul_apply]
    rw [h3, h2]
  have hfixK : fixV K ≤ fixV L := fun v hv =>
    hKfpf k₀ hk₀K hk₀1 v (by rw [hv k₀ hk₀K]; simp)
  have hcop := (coprime_decomp hKodd hV (W := fixV B) hYK).1
  have hXW : fixV (A ⊔ B) ≤ commV L ⊔ fixV (L ⊔ B) := by
    rw [← d.commV_sup_eq]
    exact sup_le_sup_right (B19.commV_mono d.leA) _
  have hBfixW : fixV B ≤ commV L ⊔ fixV (L ⊔ B) := by
    rw [← hcop]
    refine sup_le ?_ ?_
    · have h1 : commSub (fixV B) K ≤ commV K := by
        rw [commV_eq_commSub]
        exact commSub_mono le_top le_rfl
      exact h1.trans ((B19.commV_mono hKL).trans le_sup_left)
    · intro x hx
      have : x ∈ fixV L ⊓ fixV B := ⟨hfixK hx.2, hx.1⟩
      rw [← fixV_sup] at this
      exact Subgroup.mem_sup_right this
  have hcardY : Nat.card ↥(fixV B) = (2 ^ n) ^ 2 * Nat.card ↥(fixV (L ⊔ B)) := by
    have h1 := h.card_eq B d.memB
    rw [d.card_B, d.card_V_star] at h1
    have hpos : 0 < 2 ^ n := by positivity
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [← h1]
    ring
  have hWeq : fixV B = commV L ⊔ fixV (L ⊔ B) :=
    Subgroup.eq_of_le_of_card_ge hBfixW (d.card_W.trans hcardY.symm).le
  have hWinv : ∀ l ∈ L, ∀ w ∈ commV L ⊔ fixV (L ⊔ B), l w ∈ commV L ⊔ fixV (L ⊔ B) :=
    fun l hl w hw => d.invariant l (Subgroup.mem_sup_left hl) w hw
  have hmapW : ∀ l ∈ L, (commV L ⊔ fixV (L ⊔ B)).map (l : MulAut V).toMonoidHom =
      commV L ⊔ fixV (L ⊔ B) := by
    intro l hl
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact hWinv l hl w hw
    · rw [Subgroup.card_map_of_injective l.injective]
  have hfixBl : ∀ l ∈ L, fixV (conjSub l B) = commV L ⊔ fixV (L ⊔ B) := by
    intro l hl
    show fixV (B.map (MulAut.conj l).toMonoidHom) = _
    rw [Glauberman.fixV_map_conj, hWeq]
    exact hmapW l hl
  have hBL' : ∀ l ∈ L, conjSub l B = B := by
    intro l hl
    by_contra hne
    have hDl : conjSub l B ∈ D := h.conj_mem B d.memB l (d.lam.1 hl)
    have hcB : commV B ≤ commV L ⊔ fixV (L ⊔ B) := d.commV_B_le.trans hXW
    have hcBl : commV (conjSub l B) ≤ commV L ⊔ fixV (L ⊔ B) := by
      show commV (B.map (MulAut.conj l).toMonoidHom) ≤ _
      rw [B19.commV_map_conj]
      conv_rhs => rw [← hmapW l hl]
      exact Subgroup.map_mono hcB
    have hcomm' : ∀ x ∈ B, ∀ y ∈ conjSub l B, x * y = y * x :=
      FourOneTools.commute_of_commV_le (hcB.trans (hfixBl l hl).ge) (hcBl.trans hWeq.ge)
    have hprod := h.card_prod B d.memB (conjSub l B) hDl hne hcomm'
    have hfix2 : fixV (B ⊔ conjSub l B) = commV L ⊔ fixV (L ⊔ B) := by
      rw [fixV_sup, hfixBl l hl, ← hWeq, inf_idem]
    rw [hfix2, d.card_W, card_conjSub, d.card_B, d.card_V_star] at hprod
    have hFpos : 0 < Nat.card ↥(fixV (L ⊔ B)) := Nat.card_pos
    have hpos : 0 < (2 ^ n) ^ 3 * Nat.card ↥(fixV (L ⊔ B)) := by positivity
    have hq1 : 2 ^ n = 1 := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      calc (2 ^ n) ^ 3 * Nat.card ↥(fixV (L ⊔ B)) * 2 ^ n
          = 2 ^ n * 2 ^ n * ((2 ^ n) ^ 2 * Nat.card ↥(fixV (L ⊔ B))) := by ring
        _ = (2 ^ n) ^ 3 * Nat.card ↥(fixV (L ⊔ B)) := hprod.symm
        _ = (2 ^ n) ^ 3 * Nat.card ↥(fixV (L ⊔ B)) * 1 := (mul_one _).symm
    omega
  obtain ⟨D', hD', hD'ne⟩ := d.sl.exists_sylow_ne hn1 hAsyl
  obtain ⟨x, hxL, hD'x⟩ := IsSLNatSection.sylow_conj hAsyl hD'
  have hsupLA : A ⊔ D' = L := d.sl.sylow_sup_eq hn1 hAsyl hD' hD'ne.symm
  have hcommD' : ∀ d' ∈ D', ∀ b ∈ B, d' * b = b * d' := by
    intro d' hd' b hb
    rw [hD'x] at hd'
    obtain ⟨a, ha, rfl⟩ := hd'
    have hb' : x⁻¹ * b * x ∈ B := by
      have h1 : conjSub x⁻¹ B = B := hBL' x⁻¹ (L.inv_mem hxL)
      rw [← h1]
      exact ⟨b, hb, by simp⟩
    have h2 := d.comm a ha _ hb'
    show x * a * x⁻¹ * b = b * (x * a * x⁻¹)
    calc x * a * x⁻¹ * b = x * (a * (x⁻¹ * b * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * b * x) * a) * x⁻¹ := by rw [h2]
      _ = b * (x * a * x⁻¹) := by group
  have hle : A ⊔ D' ≤ Subgroup.centralizer (B : Set (MulAut V)) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => (d.comm a ha b hb).symm)
      (fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => (hcommD' a ha b hb).symm)
  rw [hsupLA] at hle
  obtain ⟨l, hl, b, hb, hne⟩ := hnc
  exact hne (Subgroup.mem_centralizer_iff.1 (hle hl) b hb).symm

end CFSG.CGT.PushingUpLit.BHS
