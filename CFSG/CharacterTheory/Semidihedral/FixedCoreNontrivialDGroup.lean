module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialQuotient
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialPGL
public import CFSG.CharacterTheory.Semidihedral.CoreFreeDihedral
public import CFSG.CharacterTheory.Semidihedral.MatrixFourGroupNormalizer

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.GorensteinWalter

variable {E : Type} [Group E]

theorem mem_of_pow_mem_of_coprime {C : Subgroup E} {g : E} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : g ^ a ∈ C) (hb : g ^ b ∈ C) : g ∈ C := by
  have hg := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one, Nat.cast_one] at hg
  have : g = (g ^ a) ^ (Nat.gcdA a b) * (g ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hg, zpow_one]
  rw [this]
  exact C.mul_mem (C.zpow_mem ha _) (C.zpow_mem hb _)

theorem inf_pPrimeCore_eq_bot_of_isPGroup [Finite E] {P : Subgroup E} (hP : IsPGroup 2 P) :
    P ⊓ CFSG.pPrimeCore 2 E = ⊥ := by
  have hO := CFSG.pPrimeCore_coprime_card (p := 2) (G := E)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP
  apply disjoint_iff.mp
  apply Subgroup.disjoint_of_coprime_natCard
  rw [hn]
  exact Nat.Coprime.pow_left n hO

theorem injOn_mk_of_isPGroup [Finite E] {P : Subgroup E} (hP : IsPGroup 2 P) :
    Set.InjOn (QuotientGroup.mk' (CFSG.pPrimeCore 2 E)) P := by
  intro x hx y hy hxy
  have h : x⁻¹ * y ∈ CFSG.pPrimeCore 2 E := (QuotientGroup.eq).mp hxy
  have hP' : x⁻¹ * y ∈ P := P.mul_mem (P.inv_mem hx) hy
  have h1 : x⁻¹ * y ∈ P ⊓ CFSG.pPrimeCore 2 E := Subgroup.mem_inf.mpr ⟨hP', h⟩
  rw [inf_pPrimeCore_eq_bot_of_isPGroup hP, Subgroup.mem_bot] at h1
  exact (inv_mul_eq_one.mp h1)

theorem odd_card_pPrimeCore [Finite E] : Odd (Nat.card (CFSG.pPrimeCore 2 E)) :=
  Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := E))

theorem conj_mem_pPrimeCore (g : E) {o : E} (ho : o ∈ CFSG.pPrimeCore 2 E) :
    g * o * g⁻¹ ∈ CFSG.pPrimeCore 2 E :=
  (CFSG.pPrimeCore_normal (p := 2) (G := E)).conj_mem o ho g

theorem isKleinFour_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [IsKleinFour X] (e : X ≃* Y) :
    IsKleinFour Y :=
  ⟨by rw [← Nat.card_congr e.toEquiv]; exact IsKleinFour.card_four,
    by rw [← Monoid.exponent_eq_of_mulEquiv e]; exact IsKleinFour.exponent_two⟩

theorem eq_one_of_mem_of_odd [Finite E] {P : Subgroup E} (hP : IsPGroup 2 P) {x : E}
    (hx : x ∈ P) (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem isPGroup_two_of_odd_eq_one {X : Type*} [Group X] [Finite X]
    (h : ∀ x : X, Odd (orderOf x) → x = 1) : IsPGroup 2 X := by
  intro x
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨k, h _ ?_⟩
  have : orderOf (x ^ 2 ^ k) = m := by
    rw [orderOf_pow' x (pow_ne_zero k two_ne_zero), hkm,
      Nat.gcd_eq_right (Dvd.intro m rfl), Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
  rw [this]
  exact hm

theorem not_isPGroup_quotient_of_cycling [Finite E] {t s g : E} {W : Subgroup E}
    (hOW : CFSG.pPrimeCore 2 E ≤ W) (htW : ∀ w ∈ W, w * t = t * w) (hst : s ≠ t)
    (hts : t * s = s * t) (hs : s * s = 1) (hgt : g * t * g⁻¹ = s) (hgs : g * s * g⁻¹ = t * s) :
    ¬ IsPGroup 2 (E ⧸ CFSG.pPrimeCore 2 E) := by
  intro h2
  obtain ⟨k, hk⟩ := h2 (QuotientGroup.mk g)
  have hgk : g ^ 2 ^ k ∈ CFSG.pPrimeCore 2 E := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hk
  have hC2 : g ^ 2 ^ k ∈ Subgroup.centralizer ({t} : Set E) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (htW _ (hOW hgk))
  have hC3 : g ^ 3 ∈ Subgroup.centralizer ({t} : Set E) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : g * (t * s) * g⁻¹ = t := by
      calc g * (t * s) * g⁻¹ = (g * t * g⁻¹) * (g * s * g⁻¹) := by group
        _ = s * (t * s) := by rw [hgt, hgs]
        _ = t * (s * s) := by rw [← mul_assoc, ← hts, mul_assoc]
        _ = t := by rw [hs, mul_one]
    have h3 : g ^ 3 * t * (g ^ 3)⁻¹ = t := by
      calc g ^ 3 * t * (g ^ 3)⁻¹ = g * (g * (g * t * g⁻¹) * g⁻¹) * g⁻¹ := by
            simp only [pow_succ, pow_zero, one_mul]; group
        _ = t := by rw [hgt, hgs, h1]
    calc g ^ 3 * t = g ^ 3 * t * (g ^ 3)⁻¹ * g ^ 3 := by group
      _ = t * g ^ 3 := by rw [h3]
  have hgC := mem_of_pow_mem_of_coprime
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)) hC2 hC3
  apply hst
  rw [← hgt]
  have := Subgroup.mem_centralizer_singleton_iff.mp hgC
  rw [this]
  group

theorem index_map_mk_eq_two [Finite E] {M₀ : Subgroup E} (hM₀ : M₀.index = 2)
    (hOM : CFSG.pPrimeCore 2 E ≤ M₀) :
    (M₀.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 E))).index = 2 := by
  rw [Subgroup.index_map_eq M₀ (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact hOM)]
  exact hM₀

theorem not_simple_of_index_two {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (hX : 2 < Nat.card X) {M : Subgroup X} (hM : M.index = 2) : False := by
  have hMn : M.Normal := Subgroup.normal_of_index_eq_two hM
  rcases hMn.eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.index_bot] at hM
    omega
  · rw [h, Subgroup.index_top] at hM
    omega

theorem not_mulEquiv_alternating_seven [Finite E] {M₀ : Subgroup E} (hM₀ : M₀.index = 2)
    (hOM : CFSG.pPrimeCore 2 E ≤ M₀)
    (e : E ⧸ CFSG.pPrimeCore 2 E ≃* alternatingGroup (Fin 7)) : False := by
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hcard : 2 < Nat.card (alternatingGroup (Fin 7)) := by
    rw [nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hidx := index_map_mk_eq_two hM₀ hOM
  apply not_simple_of_index_two hcard
    (M := (M₀.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 E))).map e.toMonoidHom)
  rw [Subgroup.index_map_eq _ e.surjective (by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]; exact bot_le)]
  exact hidx

theorem index_subgroupOf_eq_two_of_odd {X : Type*} [Group X] [Finite X] {L M : Subgroup X}
    (hLi : Odd L.index) (hM : M.index = 2) : (M.subgroupOf L).index = 2 := by
  classical
  have hLM : ¬ L ≤ M := by
    intro hle
    have h := Subgroup.relIndex_mul_index hle
    rw [hM] at h
    rw [← h] at hLi
    exact (Nat.not_even_iff_odd.mpr hLi) ⟨L.relIndex M, by ring⟩
  obtain ⟨l, hlL, hlM⟩ := Set.not_subset.mp hLM
  have hlM' : l ∉ M := hlM
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨l, hlL⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  have h := Subgroup.mul_mem_iff_of_index_two hM (a := (b : X)) (b := l)
  by_cases hb : (b : X) ∈ M
  · refine Or.inr ⟨hb, ?_⟩
    rw [h]
    simp [hb, hlM']
  · refine Or.inl ⟨?_, hb⟩
    rw [h]
    simp [hb, hlM']

theorem not_psl_of_index_two {X : Type*} [Group X] [Finite X] {L M : Subgroup X}
    (hLi : Odd L.index) (hM : M.index = 2) (K : Type*) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : L ≃* PSL2 K) (h8 : 8 ∣ Nat.card L) : False := by
  have hq3 : 3 ≤ Nat.card K := by
    rcases hK with ⟨p, n, hp, hpodd, hn, hcard⟩
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      obtain ⟨m, hm⟩ := hpodd
      omega
    rw [hcard]
    calc 3 ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n := Nat.pow_le_pow_right (by omega) hn
  rcases eq_or_lt_of_le hq3 with h3 | h4
  ·
    rw [Nat.card_congr e.toEquiv, psl2_card_formula K hK, ← h3] at h8
    norm_num at h8
  · have hsimple : IsSimpleGroup (PSL2 K) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    have hcard : 2 < Nat.card (PSL2 K) := by
      rw [psl2_card_formula K hK]
      have h1 : 4 ≤ Nat.card K := h4
      have h2 : 16 ≤ Nat.card K ^ 2 := by nlinarith
      have h3 : 4 * 15 ≤ Nat.card K * (Nat.card K ^ 2 - 1) :=
        Nat.mul_le_mul h1 (by omega)
      calc 2 < 4 * 15 / 2 := by norm_num
        _ ≤ Nat.card K * (Nat.card K ^ 2 - 1) / 2 := Nat.div_le_div_right h3
    have hidx := index_subgroupOf_eq_two_of_odd hLi hM
    apply not_simple_of_index_two hcard (M := (M.subgroupOf L).map e.toMonoidHom)
    rw [Subgroup.index_map_eq _ e.surjective (by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]; exact bot_le)]
    exact hidx

noncomputable def mulEquivMapOfInjOn {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    {H : Subgroup X} (hf : Set.InjOn f H) : H ≃* H.map f :=
  (MonoidHom.ofInjective (f := f.domRestrict H) (fun a b hab => Subtype.ext
    (hf a.2 b.2 (by simpa using hab)))).trans
    (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range H f))

theorem mulEquivMapOfInjOn_apply {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    {H : Subgroup X} (hf : Set.InjOn f H) (x : H) :
    ((mulEquivMapOfInjOn f hf x : H.map f) : Y) = f x := by
  simp only [mulEquivMapOfInjOn, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
  exact MonoidHom.ofInjective_apply _

theorem eight_dvd_card_of_odd_index [Finite E] {d s : E} (hd4 : orderOf d = 4) (hs : s * s = 1)
    (hsd : s * d * s⁻¹ = d⁻¹) (hsnot : s ∉ Subgroup.zpowers d)
    (P : Sylow 2 E) (hP : (P : Subgroup E) = Subgroup.zpowers d ⊔ Subgroup.zpowers s)
    (L : Subgroup (E ⧸ CFSG.pPrimeCore 2 E)) [L.Normal] (hLi : Odd L.index) :
    8 ∣ Nat.card L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπs : Function.Surjective (QuotientGroup.mk' (CFSG.pPrimeCore 2 E)) :=
    QuotientGroup.mk'_surjective _
  have hPp : IsPGroup 2 (P : Subgroup E) := P.isPGroup'
  have hinjP : Set.InjOn (QuotientGroup.mk' (CFSG.pPrimeCore 2 E)) (P : Subgroup E) :=
    injOn_mk_of_isPGroup hPp
  set Pbar : Sylow 2 (E ⧸ CFSG.pPrimeCore 2 E) := P.mapSurjective hπs with hPbardef
  have hPbar : (Pbar : Subgroup (E ⧸ CFSG.pPrimeCore 2 E)) =
      (P : Subgroup E).map (QuotientGroup.mk' (CFSG.pPrimeCore 2 E)) := rfl
  have hPbarL : (Pbar : Subgroup (E ⧸ CFSG.pPrimeCore 2 E)) ≤ L := by
    intro x hx
    obtain ⟨k, hk⟩ := Pbar.isPGroup' ⟨x, hx⟩
    exact mem_of_pow_two_pow_eq_one hLi (by simpa using congrArg Subtype.val hk)
  have hPcard : Nat.card (P : Subgroup E) = 8 := by
    obtain ⟨eD⟩ := MatrixFourGroupNormalizer.generatedDihedral_equiv d s hd4
      (by rw [pow_two]; exact hs) hsd hsnot
    rw [hP]
    exact (Nat.card_congr eD.toEquiv).trans DihedralGroup.nat_card
  have hPbarcard : Nat.card (Pbar : Subgroup (E ⧸ CFSG.pPrimeCore 2 E)) = 8 := by
    rw [hPbar, ← Nat.card_congr (mulEquivMapOfInjOn _ hinjP).toEquiv, hPcard]
  rw [← hPbarcard]
  exact Subgroup.card_dvd_of_le hPbarL

theorem pgl_case
    [Finite E] {d s : E} {W : Subgroup E}
    (hd4 : orderOf d = 4) (hs : s * s = 1) (hsd : s * d * s⁻¹ = d⁻¹)
    (hsnot : s ∉ Subgroup.zpowers d)
    (P : Sylow 2 E) (hP : (P : Subgroup E) = Subgroup.zpowers d ⊔ Subgroup.zpowers s)
    (hVK : IsKleinFour (Subgroup.zpowers (d * d) ⊔ Subgroup.zpowers s : Subgroup E))
    (hWcyc : IsCyclic W) (hWodd : Odd (Nat.card W))
    (hCV : Subgroup.centralizer
        ((Subgroup.zpowers (d * d) ⊔ Subgroup.zpowers s : Subgroup E) : Set E) =
      Subgroup.zpowers (d * d) ⊔ Subgroup.zpowers s ⊔ W)
    (hdW : ∀ w ∈ W, d * w * d⁻¹ = w⁻¹) (hOW : CFSG.pPrimeCore 2 E ≤ W)
    (K : Type) [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (E ⧸ CFSG.pPrimeCore 2 E)) [L.Normal] (hLi : Odd L.index)
    (e : L ≃* PGL2 K) :
    CFSG.pPrimeCore 2 E = W ∧ L = ⊤ ∧ (Nat.card K % 8 = 3 ∨ Nat.card K % 8 = 5) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπs : Function.Surjective (QuotientGroup.mk' (CFSG.pPrimeCore 2 E)) :=
    QuotientGroup.mk'_surjective _
  have hπker : (QuotientGroup.mk' (CFSG.pPrimeCore 2 E)).ker = CFSG.pPrimeCore 2 E :=
    QuotientGroup.ker_mk' _
  have hOodd : Odd (Nat.card (CFSG.pPrimeCore 2 E)) := odd_card_pPrimeCore
  have hPp : IsPGroup 2 (P : Subgroup E) := P.isPGroup'
  have hdP : d ∈ (P : Subgroup E) := hP ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers d)
  have hsP : s ∈ (P : Subgroup E) := hP ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  have hVP : (Subgroup.zpowers (d * d) ⊔ Subgroup.zpowers s : Subgroup E) ≤ P := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]; exact (P : Subgroup E).mul_mem hdP hdP
    · rw [Subgroup.zpowers_le]; exact hsP
  have hinjP : Set.InjOn (QuotientGroup.mk' (CFSG.pPrimeCore 2 E)) (P : Subgroup E) :=
    injOn_mk_of_isPGroup hPp
  have hinjV : Set.InjOn (QuotientGroup.mk' (CFSG.pPrimeCore 2 E))
      (Subgroup.zpowers (d * d) ⊔ Subgroup.zpowers s : Subgroup E) :=
    hinjP.mono (fun x hx => hVP hx)
  set Pbar : Sylow 2 (E ⧸ CFSG.pPrimeCore 2 E) := P.mapSurjective hπs with hPbardef
  have hPbar : (Pbar : Subgroup (E ⧸ CFSG.pPrimeCore 2 E)) =
      (P : Subgroup E).map (QuotientGroup.mk' (CFSG.pPrimeCore 2 E)) := rfl
  have hPbarL : (Pbar : Subgroup (E ⧸ CFSG.pPrimeCore 2 E)) ≤ L := by
    intro x hx
    obtain ⟨k, hk⟩ := Pbar.isPGroup' ⟨x, hx⟩
    exact mem_of_pow_two_pow_eq_one hLi (by simpa using congrArg Subtype.val hk)
  have hPcard : Nat.card (P : Subgroup E) = 8 := by
    obtain ⟨eD⟩ := MatrixFourGroupNormalizer.generatedDihedral_equiv d s hd4
      (by rw [pow_two]; exact hs) hsd hsnot
    rw [hP]
    exact (Nat.card_congr eD.toEquiv).trans DihedralGroup.nat_card
  have hPbarcard : Nat.card (Pbar : Subgroup (E ⧸ CFSG.pPrimeCore 2 E)) = 8 := by
    rw [hPbar, ← Nat.card_congr (mulEquivMapOfInjOn _ hinjP).toEquiv, hPcard]
  have hLcard : Nat.card L = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, pgl2_card_formula]
  have h8L : 8 ∣ Nat.card L := by
    rw [← hPbarcard]
    exact Subgroup.card_dvd_of_le hPbarL
  have hE16 : ¬ 16 ∣ Nat.card E := by
    intro h16
    have hidx := P.not_dvd_index
    have hEcard := (P : Subgroup E).card_mul_index
    rw [hPcard] at hEcard
    apply hidx
    rw [← hEcard] at h16
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 8)
      (by rw [show (8 : ℕ) * 2 = 16 by norm_num]; exact h16)
  have hL16 : ¬ 16 ∣ Nat.card L := by
    intro h16
    apply hE16
    refine h16.trans ((Subgroup.card_subgroup_dvd_card L).trans ?_)
    exact Dvd.intro _ (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm
  have hmod : Nat.card K % 8 = 3 ∨ Nat.card K % 8 = 5 :=
    card_mod_eight_of_not_dvd (odd_card_of_isOddPrimePower K hK) (hLcard ▸ hL16)
  set π : E →* E ⧸ CFSG.pPrimeCore 2 E := QuotientGroup.mk' (CFSG.pPrimeCore 2 E) with hπdef
  set V : Subgroup E := Subgroup.zpowers (d * d) ⊔ Subgroup.zpowers s with hVdef
  set Wbar : Subgroup (E ⧸ CFSG.pPrimeCore 2 E) := W.map π with hWbar
  set Vbar : Subgroup (E ⧸ CFSG.pPrimeCore 2 E) := V.map π with hVbar
  have hdbarL : π d ∈ L := hPbarL (by rw [hPbar]; exact ⟨d, hdP, rfl⟩)
  have hWbarL : Wbar ≤ L := by
    rintro _ ⟨w, hw, rfl⟩
    apply mem_of_conj_eq_inv hLi hdbarL
    rw [← map_inv, ← map_mul, ← map_mul, hdW w hw, map_inv]
  have hVbarL : Vbar ≤ L := fun x hx => hPbarL (by rw [hPbar]; exact Subgroup.map_mono hVP hx)
  have hWC : W ≤ Subgroup.centralizer (V : Set E) := by rw [hCV]; exact le_sup_right
  have hWbot : Wbar = ⊥ := by
    by_contra hne
    set A' : Subgroup (PGL2 K) := (Wbar.subgroupOf L).map e.toMonoidHom with hA'
    set V' : Subgroup (PGL2 K) := (Vbar.subgroupOf L).map e.toMonoidHom with hV'
    have eA : Wbar ≃* A' := (Subgroup.subgroupOfEquivOfLe hWbarL).symm.trans
      ((Wbar.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective)
    have eV : V ≃* V' := (mulEquivMapOfInjOn π hinjV).trans
      ((Subgroup.subgroupOfEquivOfLe hVbarL).symm.trans
        ((Vbar.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective))
    have hWbarcyc : IsCyclic Wbar :=
      isCyclic_of_surjective (π.subgroupMap W) (π.subgroupMap_surjective W)
    have hAcyc : IsCyclic A' := isCyclic_of_surjective eA.toMonoidHom eA.surjective
    have hAodd : Odd (Nat.card A') := by
      rw [← Nat.card_congr eA.toEquiv]
      exact hWodd.of_dvd_nat (Subgroup.card_map_dvd W π)
    have hAne : A' ≠ ⊥ := by
      intro hbot
      apply hne
      have h1 : Nat.card A' = 1 := by rw [hbot, Subgroup.card_bot]
      rw [← Nat.card_congr eA.toEquiv] at h1
      exact Subgroup.eq_bot_of_card_eq _ h1
    have hVK' : IsKleinFour V' := isKleinFour_of_mulEquiv eV
    have hcent : V' ≤ Subgroup.centralizer (A' : Set (PGL2 K)) := by
      intro a ha
      obtain ⟨y, hy, rfl⟩ := ha
      obtain ⟨v, hv, hvy⟩ := Subgroup.mem_subgroupOf.mp hy
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨z, hz, rfl⟩ := hb
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_subgroupOf.mp hz
      have hvw : w * v = v * w := (Subgroup.mem_centralizer_iff.mp (hWC hw) v hv).symm
      have hzy : z * y = y * z := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hvy, ← hwz, ← map_mul, ← map_mul, hvw]
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hzy]
    exact pgl2_no_kleinFour_centralizes_odd_cyclic K hK A' V' hAcyc hAne hAodd hVK' hcent
  have hWO : W ≤ CFSG.pPrimeCore 2 E := by
    intro w hw
    have h1 : π w ∈ Wbar := ⟨w, hw, rfl⟩
    rw [hWbot, Subgroup.mem_bot] at h1
    rw [← hπker]
    exact h1
  have hOW' : CFSG.pPrimeCore 2 E = W := le_antisymm hOW hWO
  have hdbar4 : orderOf (π d) = 4 := by
    have := orderOf_injective (π.domRestrict (P : Subgroup E))
      (fun a b hab => Subtype.ext (hinjP a.2 b.2 (by simpa using hab))) ⟨d, hdP⟩
    rw [MonoidHom.domRestrict_apply, Subgroup.orderOf_mk] at this
    rw [this, hd4]
  have hsbar : π s * π s = 1 := by rw [← map_mul, hs, map_one]
  have hsdbar : π s * π d * (π s)⁻¹ = (π d)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hsd, map_inv]
  have hsnotbar : π s ∉ Subgroup.zpowers (π d) := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [← map_zpow] at hk
    apply hsnot
    have hdkP : d ^ k ∈ (P : Subgroup E) := (P : Subgroup E).zpow_mem hdP k
    rw [← hinjP hdkP hsP hk]
    exact Subgroup.zpow_mem_zpowers d k
  have hPbar' : (Pbar : Subgroup (E ⧸ CFSG.pPrimeCore 2 E)) =
      Subgroup.zpowers (π d) ⊔ Subgroup.zpowers (π s) := by
    rw [hPbar, hP, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  have hVbarp : IsPGroup 2 Vbar := (hPp.to_le hVP).map π
  have hNodd : ∀ x ∈ Subgroup.normalizer
      ((Pbar : Subgroup (E ⧸ CFSG.pPrimeCore 2 E)) : Set (E ⧸ CFSG.pPrimeCore 2 E)),
      Odd (orderOf x) → x = 1 := by
    intro x hxN hxodd
    rw [hPbar'] at hxN
    obtain ⟨hxd, hxs⟩ := commute_of_odd_of_normalizes hdbar4 hsbar hsdbar hsnotbar hxodd hxN
    have hxV : ∀ v ∈ V, x * π v = π v * x := by
      intro v hv
      have hC : π v ∈ Subgroup.centralizer ({x} : Set (E ⧸ CFSG.pPrimeCore 2 E)) := by
        have hmap : V.map π ≤ Subgroup.centralizer ({x} : Set (E ⧸ CFSG.pPrimeCore 2 E)) := by
          rw [hVdef, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
          refine sup_le ?_ ?_
          · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff, map_mul]
            calc π d * π d * x = π d * (π d * x) := by group
              _ = π d * (x * π d) := by rw [← hxd]
              _ = x * (π d * π d) := by rw [← mul_assoc, ← hxd, mul_assoc]
          · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
            exact hxs.symm
        exact hmap ⟨v, hv, rfl⟩
      exact (Subgroup.mem_centralizer_singleton_iff.mp hC).symm
    obtain ⟨y, rfl⟩ := hπs x
    have hcomm : ∀ v ∈ V, y⁻¹ * v * y * v⁻¹ ∈ CFSG.pPrimeCore 2 E := by
      intro v hv
      rw [← hπker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
        mul_assoc (π y)⁻¹, ← hxV v hv]
      group
    obtain ⟨o, ho, hyo⟩ := exists_mem_centralizer_of_commutator_mem
      (fun g o ho => conj_mem_pPrimeCore g ho) odd_card_pPrimeCore
      (hPp.to_le hVP) hcomm
    rw [hCV] at hyo
    have hx : π y ∈ Vbar ⊔ Wbar := by
      have h1 : π (y * o) ∈ (V ⊔ W).map π := ⟨_, hyo, rfl⟩
      rw [Subgroup.map_sup] at h1
      have h2 : π (y * o) = π y := by
        have h3 : π o = 1 := by rw [← MonoidHom.mem_ker, hπker]; exact ho
        rw [map_mul, h3, mul_one]
      rwa [h2] at h1
    rw [hWbot, sup_bot_eq] at hx
    exact eq_one_of_mem_of_odd hVbarp hx hxodd
  have hNp : IsPGroup 2 (Subgroup.normalizer
      ((Pbar : Subgroup (E ⧸ CFSG.pPrimeCore 2 E)) : Set (E ⧸ CFSG.pPrimeCore 2 E))) :=
    isPGroup_two_of_odd_eq_one fun x hx => Subtype.ext (hNodd x x.2 (by
      rw [Subgroup.orderOf_coe]; exact hx))
  have hNeq := Pbar.is_maximal' hNp Subgroup.le_normalizer
  have hNL : Subgroup.normalizer
      ((Pbar : Subgroup (E ⧸ CFSG.pPrimeCore 2 E)) : Set (E ⧸ CFSG.pPrimeCore 2 E)) ≤ L := by
    rw [hNeq]
    exact hPbarL
  have htop := Sylow.normalizer_sup_eq_top' Pbar hPbarL
  have hLtop : L = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact sup_le hNL le_rfl
  exact ⟨hOW', hLtop, hmod⟩

theorem quotient_pgl2_of_dihedral_sylow
    [Finite E] {d s g : E} {W M₀ : Subgroup E}
    (hd4 : orderOf d = 4) (hs : s * s = 1) (hsd : s * d * s⁻¹ = d⁻¹)
    (hsnot : s ∉ Subgroup.zpowers d)
    (P : Sylow 2 E) (hP : (P : Subgroup E) = Subgroup.zpowers d ⊔ Subgroup.zpowers s)
    (hVK : IsKleinFour (Subgroup.zpowers (d * d) ⊔ Subgroup.zpowers s : Subgroup E))
    (hM₀ : M₀.index = 2)
    (hWcyc : IsCyclic W) (hWodd : Odd (Nat.card W))
    (hCV : Subgroup.centralizer
        ((Subgroup.zpowers (d * d) ⊔ Subgroup.zpowers s : Subgroup E) : Set E) =
      Subgroup.zpowers (d * d) ⊔ Subgroup.zpowers s ⊔ W)
    (hdW : ∀ w ∈ W, d * w * d⁻¹ = w⁻¹)
    (hOW : CFSG.pPrimeCore 2 E ≤ W)
    (hgt : g * (d * d) * g⁻¹ = s) (hgs : g * s * g⁻¹ = d * d * s) :
    CFSG.pPrimeCore 2 E = W ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (φ : E ⧸ CFSG.pPrimeCore 2 E ≃* PGL2 K),
      IsOddPrimePower (Nat.card K) ∧ (Nat.card K % 8 = 3 ∨ Nat.card K % 8 = 5) ∧
      (3 < Nat.card K → (M₀.map (QuotientGroup.mk' (CFSG.pPrimeCore 2 E))).map φ.toMonoidHom =
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eD⟩ := MatrixFourGroupNormalizer.generatedDihedral_equiv d s hd4
    (by rw [pow_two]; exact hs) hsd hsnot
  have e3 : (P : Subgroup E) ≃* DihedralGroup (2 ^ (3 - 1)) := by
    rw [show 2 ^ (3 - 1) = 4 by norm_num]
    exact (MulEquiv.subgroupCongr hP).trans eD
  have hHD : HasDihedralSylowTwo E :=
    CoreFreeDihedral.hasDihedralSylowTwo_of_supplied P 3 (by norm_num) e3
  have htmem : d * d ∈ Subgroup.zpowers d :=
    Subgroup.mul_mem _ (Subgroup.mem_zpowers d) (Subgroup.mem_zpowers d)
  have hst : s ≠ d * d := fun h => hsnot (h ▸ htmem)
  have hVC : (Subgroup.zpowers (d * d) ⊔ Subgroup.zpowers s : Subgroup E) ≤
      Subgroup.centralizer ((Subgroup.zpowers (d * d) ⊔ Subgroup.zpowers s :
        Subgroup E) : Set E) := by
    rw [hCV]; exact le_sup_left
  have hWC : W ≤ Subgroup.centralizer ((Subgroup.zpowers (d * d) ⊔ Subgroup.zpowers s :
      Subgroup E) : Set E) := by
    rw [hCV]; exact le_sup_right
  have htV : d * d ∈ (Subgroup.zpowers (d * d) ⊔ Subgroup.zpowers s : Subgroup E) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hsV : s ∈ (Subgroup.zpowers (d * d) ⊔ Subgroup.zpowers s : Subgroup E) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have htW : ∀ w ∈ W, w * (d * d) = d * d * w := fun w hw =>
    (Subgroup.mem_centralizer_iff.mp (hWC hw) (d * d) htV).symm
  have hts : d * d * s = s * (d * d) := Subgroup.mem_centralizer_iff.mp (hVC hsV) _ htV
  have hOM : CFSG.pPrimeCore 2 E ≤ M₀ := fun o ho =>
    mem_of_index_two_of_odd hM₀ (hWodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard W (hOW ho)))
  rcases gorensteinWalter E hHD with ⟨_, h2⟩ | ⟨_, ⟨e7⟩⟩ | ⟨_, K, hK, L, hLn, hLi, hLm⟩
  · exact absurd h2 (not_isPGroup_quotient_of_cycling hOW htW hst hts hs hgt hgs)
  · exact (not_mulEquiv_alternating_seven hM₀ hOM e7).elim
  · rcases hLm with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exfalso
      exact not_psl_of_index_two hLi (index_map_mk_eq_two hM₀ hOM) K hK e
        (eight_dvd_card_of_odd_index hd4 hs hsd hsnot P hP L hLi)
    · obtain ⟨hOW', hLtop, hmod⟩ :=
        pgl_case hd4 hs hsd hsnot P hP hVK hWcyc hWodd hCV hdW hOW K hK L hLi e
      let φ : E ⧸ CFSG.pPrimeCore 2 E ≃* PGL2 K :=
        (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hLtop.symm)).trans e
      refine ⟨hOW', K, inferInstance, inferInstance, φ, hK, hmod, fun hq => ?_⟩
      apply eq_pslRange_of_index_eq_two K hK hq
      rw [Subgroup.index_map_eq _ φ.surjective (by
        rw [(MonoidHom.ker_eq_bot_iff _).mpr φ.injective]; exact bot_le)]
      exact index_map_mk_eq_two hM₀ hOM

end CFSG.Semidihedral.FixedCoreNontrivial
