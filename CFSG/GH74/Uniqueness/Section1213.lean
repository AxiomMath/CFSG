module

public import CFSG.GH74.Uniqueness.Section1211
public import CFSG.GH74.Uniqueness.Section1213Basic
public import CFSG.GH74.Uniqueness.Section1213Fix

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem A5.exists_conj_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {P K H : Subgroup X}
    (hP : ABGLocalTools.IsSylowOf p P K) (hH : IsPGroup p H) (hHK : H ≤ K) :
    ∃ k ∈ K, ∀ h ∈ H, k⁻¹ * h * k ∈ P := by
  obtain ⟨Q, hQ⟩ := (hH.comap_subtype (K := K)).exists_le_sylow
  have hP' : ABGLocalTools.IsSylowOf p ((Q : Subgroup K).map K.subtype) K := ⟨Q, rfl⟩
  obtain ⟨k, hk, hconj⟩ := hP.exists_mem_conj hP'
  refine ⟨k, hk, fun h hh => (hconj h).mp ?_⟩
  exact ⟨⟨h, hHK hh⟩, hQ (show (⟨h, hHK hh⟩ : K) ∈ H.comap K.subtype from hh), rfl⟩

section Weak

variable {c : Ctx12 Z M} {n i : ℕ}

theorem A5.weakly_closed
    (S : ZDSetup X Z M) (h1212 : Lemma1212Stmt Z M) (hL : LData c n i)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : X} (hx : x ∈ kGrp M c.t) (hxp : orderOf x = p)
    {P₀ P : Subgroup X} (hP₀ : ABGLocalTools.IsSylowOf p P₀ (kGrp M c.t)) (hP₀P : P₀ ≤ P)
    (hPD : ABGLocalTools.IsSylowOf p P c.D) (hPX : ABGLocalTools.IsSylowOf p P ⊤) :
    ∀ g : X, g⁻¹ * x * g ∈ P → zpowers (g⁻¹ * x * g) = zpowers x := by
  intro g hgP
  have : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hxp
    exact hp.one_lt.ne' hxp.symm
  have hgood := A5.not_commute_of_mem_kGrp S h1212 hL hx hx1
  have hxP₀ : x ∈ P₀ := A5.mem_sylow_kGrp hL hp hx hxp hP₀
  have hPD' : P ≤ c.D := hPD.le
  have hPN : ∀ d ∈ P, d ∈ normalizer (kGrp M c.t : Set X) := fun d hd =>
    A5.mem_normalizer_kGrp_of_mem_D hL (hPD' hd)
  have hPC : P ≤ centralizer ({x} : Set X) := fun d hd =>
    mem_centralizer_singleton_iff.mpr (A5.commute_of_le_normalizer_zpowers hp hxp hPD.isPGroup
      (fun e he => A5.mem_normalizer_zpowers_of_mem_normalizer_kGrp hL hx (hPN e he)) d hd)
  have hMt : conjugate M c.t ≠ M := (S.prodDisc.conjugate_ne_iff (self_mem_omega M)).mpr c.htM
  obtain ⟨y, hy⟩ : ∃ y : X, y = g⁻¹ * x * g := ⟨_, rfl⟩
  rw [← hy] at hgP ⊢
  by_contra hne
  have hyo : orderOf y = p := by
    have := A5.orderOf_conj g⁻¹ x
    rwa [inv_inv, hxp, ← hy] at this
  set R : Subgroup X := P ⊓ centralizer ({y} : Set X) with hR
  have hRc : conjugate R g⁻¹ ≤ centralizer ({x} : Set X) := by
    intro z hz
    rw [mem_conjugate_iff, inv_inv] at hz
    have hzy : (g⁻¹ * z * g) * y = y * (g⁻¹ * z * g) :=
      mem_centralizer_singleton_iff.mp (mem_inf.mp hz).2
    rw [hy] at hzy
    rw [mem_centralizer_singleton_iff]
    calc z * x = g * ((g⁻¹ * z * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * z * g)) * g⁻¹ := by rw [hzy]
      _ = x * z := by group
  have hRp : IsPGroup p (conjugate R g⁻¹) :=
    isPGroup_conjugate (hPD.isPGroup.to_le (inf_le_left : R ≤ P)) g⁻¹
  have hPCx : ABGLocalTools.IsSylowOf p P (centralizer ({x} : Set X)) := hPX.of_le hPC le_top
  obtain ⟨k, hkC, hk⟩ := A5.exists_conj_le_of_isSylowOf hPCx hRp hRc
  have hkx : k * x = x * k := mem_centralizer_singleton_iff.mp hkC
  have hg'y : (k⁻¹ * g)⁻¹ * x * (k⁻¹ * g) = y := by
    rw [hy]
    calc (k⁻¹ * g)⁻¹ * x * (k⁻¹ * g) = g⁻¹ * (k * x * k⁻¹) * g := by group
      _ = g⁻¹ * x * g := by rw [hkx, mul_inv_cancel_right]
  have hg'R : ∀ r ∈ R, (k⁻¹ * g) * r * (k⁻¹ * g)⁻¹ ∈ P := by
    intro r hr
    have hz : g * r * g⁻¹ ∈ conjugate R g⁻¹ := by
      rw [mem_conjugate_iff, show g⁻¹ * (g * r * g⁻¹) * g⁻¹⁻¹ = r by group]
      exact hr
    have h1 := hk _ hz
    rwa [show k⁻¹ * (g * r * g⁻¹) * k = (k⁻¹ * g) * r * (k⁻¹ * g)⁻¹ by group] at h1
  by_cases hP₀R : P₀ ≤ R
  ·
    have hΩR : ∀ γ ∈ omegaFix M (R : Set X), γ = M ∨ γ = conjugate M c.t := fun γ hγ =>
      A5.omegaFix_sylow_kGrp S h1212 hL hp hp2 hx hx1 hP₀ hxP₀ γ (omegaFix_anti hP₀R hγ)
    have hmove : ∀ γ : Subgroup X, γ ∈ omega M → (∀ d ∈ c.D, conjugate γ d = γ) →
        conjugate γ (k⁻¹ * g) ∈ omegaFix M (R : Set X) := by
      intro γ hγ hfix
      refine ⟨conjugate_mem_omega hγ _, fun r hr => ?_⟩
      rw [conjugate_conjugate, show (k⁻¹ * g) * r = ((k⁻¹ * g) * r * (k⁻¹ * g)⁻¹) * (k⁻¹ * g) by
        group, ← conjugate_conjugate, hfix _ (hPD' (hg'R r hr))]
    have hMD : ∀ d ∈ c.D, conjugate M d = M := fun d hd =>
      (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr (mem_inf.mp hd).1
    have hMtD : ∀ d ∈ c.D, conjugate (conjugate M c.t) d = conjugate M c.t := fun d hd =>
      (S.prodDisc.conjugate_eq_iff_mem ⟨c.t, rfl⟩).mpr (mem_inf.mp hd).2
    have h1 := hΩR _ (hmove M (self_mem_omega M) hMD)
    have h2 := hΩR _ (hmove (conjugate M c.t) ⟨c.t, rfl⟩ hMtD)
    have hg'N : k⁻¹ * g ∈ normalizer (kGrp M c.t : Set X) := by
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (conjugate_injective _ (h2.trans h1.symm)) hMt
      · exact A5.mem_normalizer_kGrp_of_mem_D hL (mem_inf.mpr
          ⟨(S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mp h1,
            (S.prodDisc.conjugate_eq_iff_mem ⟨c.t, rfl⟩).mp h2⟩)
      · have hD := (A5.mem_normalizer_of_swap S hL h1 h2).1
        have h3 := mul_mem (A5.mem_normalizer_kGrp_of_mem_D hL hD) (A5.t_mem_normalizer_kGrp hL)
        rwa [mul_assoc, S.invariant.mul_self_eq_one c.ht, mul_one] at h3
      · exact absurd (conjugate_injective _ (h2.trans h1.symm)) hMt
    apply hne
    rw [← hg'y]
    have := A5.zpowers_conj_eq hL hx (inv_mem hg'N)
    rwa [inv_inv] at this
  ·
    obtain ⟨w, hwP₀, hwR⟩ := IsConcreteLE.not_le_iff_exists.mp hP₀R
    have hwP : w ∈ P := hP₀P hwP₀
    have hwy : w * y ≠ y * w := fun h =>
      hwR (mem_inf.mpr ⟨hwP, mem_centralizer_singleton_iff.mpr h⟩)
    have hxy : x * y = y * x := (mem_centralizer_singleton_iff.mp (hPC hgP)).symm
    have hyx : y ∉ zpowers x := by
      intro h
      apply hne
      apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr h)
      rw [Nat.card_zpowers, Nat.card_zpowers, hyo, hxp]
    have hyN : y ∈ normalizer (P₀ : Set X) :=
      A5.mem_normalizer_sylow_of_mem_normalizer_kGrp hL hP₀.le (hPN y hgP)
    have hP₀cyc : IsCyclic P₀ := by
      have := A5.isCyclic_kGrp hL
      exact isCyclic_of_le hP₀.le
    obtain ⟨hU2, hUexp, hUcl⟩ :=
      A5.metacyclic_plane hp hp2 hP₀cyc hP₀.isPGroup hxP₀ hxp hyo hyN hxy hyx hwP₀ hwy
    have hgoodU : ∀ u ∈ zpowers x ⊔ zpowers y, u ≠ 1 → ∀ s ∈ Z, s * u ≠ u * s := by
      intro u hu hu1 s hs hsu
      have hcomm : ∀ v ∈ zpowers u, s * v = v * s := fun v hv => by
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hv
        exact (Commute.zpow_right (show Commute s u from hsu) j).eq
      rcases hUcl u hu hu1 with h | ⟨g₁, h⟩
      · have hmem : x ∈ zpowers u := by rw [h]; exact mem_zpowers x
        exact hgood s hs (hcomm x hmem)
      · have hmem : g₁ * y * g₁⁻¹ ∈ zpowers u := by rw [h]; exact mem_zpowers _
        have h1 := hcomm _ hmem
        have hya : g₁ * y * g₁⁻¹ = (g₁ * g⁻¹) * x * (g₁ * g⁻¹)⁻¹ := by rw [hy]; group
        rw [hya] at h1
        have hsZ : (g₁ * g⁻¹)⁻¹ * s * (g₁ * g⁻¹) ∈ Z := S.invariant.2 s hs _
        apply hgood _ hsZ
        calc (g₁ * g⁻¹)⁻¹ * s * (g₁ * g⁻¹) * x
            = (g₁ * g⁻¹)⁻¹ * (s * ((g₁ * g⁻¹) * x * (g₁ * g⁻¹)⁻¹)) * (g₁ * g⁻¹) := by group
          _ = (g₁ * g⁻¹)⁻¹ * (((g₁ * g⁻¹) * x * (g₁ * g⁻¹)⁻¹) * s) * (g₁ * g⁻¹) := by rw [h1]
          _ = x * ((g₁ * g⁻¹)⁻¹ * s * (g₁ * g⁻¹)) := by group
    have hUM : zpowers x ⊔ zpowers y ≤ M :=
      (sup_le (zpowers_le.mpr (hP₀P hxP₀)) (zpowers_le.mpr hgP)).trans (hPD'.trans inf_le_left)
    have hcompl : ¬ p ∣ Nat.card (zHull Z M) := by
      rw [hL.m_card]
      intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
    have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
      p hp (zpowers x ⊔ zpowers y) (zHull Z M) (fun u => Subtype.ext (by simpa using hUexp u u.2))
      hU2 hcompl (hUM.trans (le_normalizer_zHull S.invariant M))
    have hbot : zHull Z M = ⊥ := by
      rw [hgen]
      refine iSup₂_eq_bot.mpr fun u hu1 => ?_
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨hvM, hvC⟩ := mem_inf.mp hv
      rw [mem_bot]
      by_contra hv1
      have hvZ : v ∈ Z := by
        have h1 : v ∈ zM Z M := by
          rw [hL.zM_eq]
          exact ⟨hvM, hv1⟩
        exact (show v ∈ Z ∩ (M : Set X) from h1).1
      exact hgoodU u u.2 (fun h => hu1 (Subtype.ext h)) v hvZ
        (mem_centralizer_singleton_iff.mp hvC)
    have hcard := hL.m_card
    rw [hbot, Subgroup.card_bot] at hcard
    have := Nat.one_lt_two_pow (n := n) (by have := hL.hn; omega)
    omega

end Weak

section Main

variable {c : Ctx12 Z M} {n i : ℕ}

theorem A5.omegaFix_subset_of_prime
    (S : ZDSetup X Z M) (h1212 : Lemma1212Stmt Z M)
    (hL : LData c n i) {p : ℕ} (hp : p.Prime) {x : X} (hx : x ∈ kGrp M c.t)
    (hxp : orderOf x = p) : omegaFix M ({x} : Set X) ⊆ {M, conjugate M c.t} := by
  have : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hxp
    exact hp.one_lt.ne' hxp.symm
  have hpK : p ∣ Nat.card (kGrp M c.t) := by
    rw [← hxp]
    have := orderOf_dvd_natCard (⟨x, hx⟩ : ↥(kGrp M c.t))
    rwa [Subgroup.orderOf_mk] at this
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr (A5.odd_card_kGrp hL)) (even_iff_two_dvd.mpr hpK)
  have hgood := A5.not_commute_of_mem_kGrp S h1212 hL hx hx1
  have hMt : conjugate M c.t ≠ M := (S.prodDisc.conjugate_ne_iff (self_mem_omega M)).mpr c.htM
  have ht2 : c.t * c.t = 1 := S.invariant.mul_self_eq_one c.ht
  obtain ⟨P₀, hP₀⟩ := ABGLocalTools.exists_isSylowOf p (kGrp M c.t)
  have hP₀D : P₀ ≤ c.D := hP₀.le.trans (A5.kGrp_le_D hL)
  obtain ⟨P, hPD, hP₀P⟩ : ∃ P : Subgroup X, ABGLocalTools.IsSylowOf p P c.D ∧ P₀ ≤ P := by
    obtain ⟨Q, hQ⟩ := (hP₀.isPGroup.comap_subtype (K := c.D)).exists_le_sylow
    exact ⟨(Q : Subgroup c.D).map c.D.subtype, ⟨Q, rfl⟩, fun y hy =>
      ⟨⟨y, hP₀D hy⟩, hQ (show (⟨y, hP₀D hy⟩ : c.D) ∈ P₀.comap c.D.subtype from hy), rfl⟩⟩
  have hpm : p ∣ zNum Z M := by
    have hz : zNum Z M = 2 ^ n - 1 := by
      unfold zNum
      rw [Nat.card_coe_set_eq]
      exact A2.ncard_zM hL
    rw [hz, ← hL.k_card, ← hL.k_eq']
    exact hpK
  have hPX := ((S.corollary712 (conjugate M c.t) ⟨c.t, rfl⟩ hMt p hp hp2 P hPD).2.2 hpm).2
  have hweak := A5.weakly_closed S h1212 hL hp hp2 hx hxp hP₀ hP₀P hPD hPX
  set N : Subgroup X := normalizer ((zpowers x : Subgroup X) : Set X) with hN
  set H : Subgroup X := zHull Z N with hH
  have hrank : Open.pRank 2 H ≤ 1 := (A5.lemma1212_kGrp S h1212 hL hx hx1).1.le
  have htN : c.t ∈ N := mem_normalizer_zpowers_of_inv ht2 (A5.inv_of_mem_kGrp hL hx)
  have htH : c.t ∈ H := subset_closure ⟨c.ht, htN⟩
  have hHN : ∀ h ∈ H, h ∈ N := fun h hh => Cor713.zHull_le N hh
  have hinvZ : ∀ s ∈ H, orderOf s = 2 → s ∈ Z := by
    have hrk : Open.twoRank ↥H ≤ 1 := by
      rw [Open.twoRank, ← CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2
        (by norm_num) H]
      exact hrank
    intro s hs hso
    obtain ⟨c', hc'⟩ := isConj_iff.mp (isConj_of_involutions_of_twoRank_le_one hrk
      (x := ⟨c.t, htH⟩) (y := ⟨s, hs⟩) (by rw [Subgroup.orderOf_mk]; exact S.invariant.1 _ c.ht)
      (by rw [Subgroup.orderOf_mk]; exact hso))
    have h1 : (c' : X) * c.t * (c' : X)⁻¹ = s := congrArg Subtype.val hc'
    rw [← h1]
    have := S.invariant.2 c.t c.ht (c' : X)⁻¹
    rwa [inv_inv] at this
  have hfixx : ∀ δ ∈ omegaFix M ({x} : Set X), conjugate δ x = δ := fun δ hδ =>
    hδ.2 x (Set.mem_singleton x)
  have hmk : ∀ δ ∈ omega M, conjugate δ x = δ → δ ∈ omegaFix M ({x} : Set X) :=
    fun δ hδ h => ⟨hδ, fun g hg => by rw [Set.mem_singleton_iff.mp hg]; exact h⟩
  have hA : ∀ h ∈ H, ∀ δ ∈ omegaFix M ({x} : Set X), conjugate δ h ∈ omegaFix M ({x} : Set X) := by
    intro h hh δ hδ
    have hxδ : x ∈ δ := (S.prodDisc.conjugate_eq_iff_mem hδ.1).mp (hfixx δ hδ)
    refine hmk _ (conjugate_mem_omega hδ.1 h) ?_
    rw [S.prodDisc.conjugate_eq_iff_mem (conjugate_mem_omega hδ.1 h), mem_conjugate_iff]
    have h1 : h * x * h⁻¹ ∈ zpowers x := (mem_normalizer_iff.mp (hHN h hh) x).mp (mem_zpowers x)
    exact zpowers_le.mpr hxδ h1
  have hfree : ∀ s ∈ H, orderOf s = 2 → ∀ δ ∈ omegaFix M ({x} : Set X), conjugate δ s ≠ δ := by
    intro s hs hso δ hδ hsδ
    have hsZ := hinvZ s hs hso
    have hxδ : x ∈ δ := (S.prodDisc.conjugate_eq_iff_mem hδ.1).mp (hfixx δ hδ)
    have hsδ' : s ∈ δ := (S.prodDisc.conjugate_eq_iff_mem hδ.1).mp hsδ
    obtain ⟨g, hg⟩ := hδ.1
    rw [← hg] at hxδ hsδ'
    have hodd : Odd (Nat.card (zpowers x)) := by
      rw [Nat.card_zpowers, hxp]
      exact hp.odd_of_ne_two hp2
    have hcomm := A5.commute_of_mem_point S.invariant hL.m_abelian.2 hodd hsZ (hHN s hs) hsδ'
      (zpowers_le.mpr hxδ)
    exact hgood s hsZ (hcomm x (mem_zpowers x))
  have hswap : ∀ δ ∈ omegaFix M ({x} : Set X), ∀ ζ ∈ omegaFix M ({x} : Set X), δ ≠ ζ →
      ∃ s ∈ H, orderOf s = 2 ∧ conjugate δ s = ζ := by
    intro δ hδ ζ hζ hδζ
    obtain ⟨g, hg1, hg2⟩ := S.theorem4.1 δ hδ.1 ζ hζ.1 hδζ M (self_mem_omega M)
      (conjugate M c.t) ⟨c.t, rfl⟩ hMt.symm
    have hfix : ∀ {ε B : Subgroup X}, conjugate ε g = B → conjugate ε x = ε →
        conjugate B (g⁻¹ * x * g) = B := by
      intro ε B hεB hεx
      rw [← hεB, conjugate_conjugate, show g * (g⁻¹ * x * g) = x * g by group,
        ← conjugate_conjugate, hεx]
    have hx'D : g⁻¹ * x * g ∈ c.D := mem_inf.mpr
      ⟨(S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mp (hfix hg1 (hfixx δ hδ)),
        (S.prodDisc.conjugate_eq_iff_mem ⟨c.t, rfl⟩).mp (hfix hg2 (hfixx ζ hζ))⟩
    have hx'p : IsPGroup p (zpowers (g⁻¹ * x * g)) :=
      IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, pow_one, ← hxp]
        have := A5.orderOf_conj g⁻¹ x
        rwa [inv_inv] at this)
    obtain ⟨d, hdD, hd⟩ := A5.exists_conj_le_of_isSylowOf hPD hx'p (zpowers_le.mpr hx'D)
    have hd' := hd _ (mem_zpowers _)
    have hg'x : (g * d)⁻¹ * x * (g * d) = d⁻¹ * (g⁻¹ * x * g) * d := by group
    have hzw := hweak (g * d) (by rw [hg'x]; exact hd')
    have hg'N : g * d ∈ N := by
      have h1 : (g * d)⁻¹ ∈ N := by
        refine mem_normalizer_fintype fun v hv => ?_
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hv
        rw [← conj_zpow, inv_inv, ← hzw]
        exact zpow_mem (mem_zpowers _) j
      simpa using inv_mem h1
    have hδg' : conjugate δ (g * d) = M := by
      rw [← conjugate_conjugate, hg1]
      exact (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr (mem_inf.mp hdD).1
    have hζg' : conjugate ζ (g * d) = conjugate M c.t := by
      rw [← conjugate_conjugate, hg2]
      exact (S.prodDisc.conjugate_eq_iff_mem ⟨c.t, rfl⟩).mpr (mem_inf.mp hdD).2
    refine ⟨(g * d) * c.t * (g * d)⁻¹, subset_closure ⟨?_, ?_⟩, ?_, ?_⟩
    · have := S.invariant.2 c.t c.ht (g * d)⁻¹
      rwa [inv_inv] at this
    · exact mul_mem (mul_mem hg'N htN) (inv_mem hg'N)
    · rw [A5.orderOf_conj]
      exact S.invariant.1 _ c.ht
    · rw [show (g * d) * c.t * (g * d)⁻¹ = (g * d) * (c.t * (g * d)⁻¹) by group,
        ← conjugate_conjugate, hδg', ← conjugate_conjugate, ← hζg', conjugate_conjugate,
        mul_inv_cancel, conjugate_one]
  have hMA : M ∈ omegaFix M ({x} : Set X) :=
    hmk M (self_mem_omega M) ((S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr
      (mem_inf.mp (A5.kGrp_le_D hL hx)).1)
  exact A5.subset_pair_of_pRank_le_one hrank hA hfree hswap htH (S.invariant.1 _ c.ht) hMA

end Main

theorem ZDSetup.prop1213
    (S : ZDSetup X Z M) (h1212 : Lemma1212Stmt Z M) : Prop1213Stmt Z M := by
  intro c n i hL x hx hx1
  refine Set.Subset.antisymm ?_ ?_
  · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
      (fun h => hx1 (orderOf_eq_one_iff.mp h) : orderOf x ≠ 1)
    have hord : orderOf (x ^ (orderOf x / p)) = p := orderOf_pow_orderOf_div (orderOf_pos x).ne' hpd
    have hsub := A5.omegaFix_subset_of_prime S h1212 hL hp (pow_mem hx _) hord
    intro β hβ
    apply hsub
    refine ⟨hβ.1, fun g hg => ?_⟩
    rw [Set.mem_singleton_iff.mp hg]
    have hfix : conjugate β x = β := hβ.2 x (Set.mem_singleton x)
    exact conjugate_eq_iff_mem_normalizer.mpr (pow_mem (conjugate_eq_iff_mem_normalizer.mp hfix) _)
  · have hxD := A5.kGrp_le_D hL hx
    intro β hβ
    rcases hβ with h | h
    · rw [h]
      exact ⟨self_mem_omega M, fun g hg => by
        rw [Set.mem_singleton_iff.mp hg]
        exact (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr (mem_inf.mp hxD).1⟩
    · rw [Set.mem_singleton_iff.mp h]
      exact ⟨⟨c.t, rfl⟩, fun g hg => by
        rw [Set.mem_singleton_iff.mp hg]
        exact (S.prodDisc.conjugate_eq_iff_mem ⟨c.t, rfl⟩).mpr (mem_inf.mp hxD).2⟩

end CFSG.GH74.Uniqueness
