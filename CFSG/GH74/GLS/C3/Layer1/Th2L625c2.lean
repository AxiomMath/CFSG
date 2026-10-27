module

public import CFSG.GH74.GLS.C3.Layer1.Th2L625Rank
public import CFSG.GH74.GLS.IVK.Proofs2.C3L29Rank

public section

namespace CFSG.GH74.GLS.Th2.L625

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2
  CFSG.GH74.GLS.C3.Layer1

section Elementary

variable {X : Type} [Group X]

theorem isElementaryAbelian_sup_zpowers {R : Subgroup X} {y : X} (hR : IsElementaryAbelian 2 ↥R)
    (hy2 : y * y = 1) (hcomm : ∀ r ∈ R, r * y = y * r) :
    IsElementaryAbelian 2 ↥(R ⊔ zpowers y) := by
  obtain ⟨hRc, hRsq⟩ := Back.forall_of_isElementaryAbelian hR
  have hcomm' : ∀ r ∈ R, ∀ l ∈ zpowers y, r * l = l * r := by
    intro r hr l hl
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hl
    exact (Commute.zpow_right (hcomm r hr) n).eq
  have hmul : ∀ z ∈ R ⊔ zpowers y, ∃ r ∈ R, ∃ l ∈ zpowers y, z = r * l := by
    intro z hz
    have comm : ∀ (m : R) (n : zpowers y), Commute (R.subtype m) ((zpowers y).subtype n) :=
      fun m n => hcomm' m m.2 n n.2
    have hrange := MonoidHom.noncommCoprod_range R.subtype (zpowers y).subtype comm
    rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
    rw [← hrange] at hz
    obtain ⟨⟨a, b⟩, rfl⟩ := hz
    exact ⟨a, a.2, b, b.2, rfl⟩
  have hy2' : y ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hy2
  have hysq : ∀ l ∈ zpowers y, l * l = 1 := by
    intro l hl
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hl
    rw [← zpow_add, ← two_mul, zpow_mul, hy2', one_zpow]
  have hlcomm : ∀ l ∈ zpowers y, ∀ l' ∈ zpowers y, l * l' = l' * l := by
    intro l hl l' hl'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hl
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hl'
    exact (Commute.zpow_zpow_self y n m).eq
  refine Back.isElementaryAbelian_of_forall (fun a ha b hb => ?_) (fun a ha => ?_)
  · obtain ⟨r, hr, l, hl, rfl⟩ := hmul a ha
    obtain ⟨r', hr', l', hl', rfl⟩ := hmul b hb
    have h1 : Commute r r' := hRc r hr r' hr'
    have h2 : Commute l l' := hlcomm l hl l' hl'
    have h3 : Commute r l' := hcomm' r hr l' hl'
    have h4 : Commute l r' := (hcomm' r' hr' l hl).symm
    exact ((h1.mul_right h3).mul_left (h4.mul_right h2)).eq
  · obtain ⟨r, hr, l, hl, rfl⟩ := hmul a ha
    have hc : Commute r l := hcomm' r hr l hl
    calc r * l * (r * l) = (r * l) ^ 2 := (sq _).symm
      _ = r ^ 2 * l ^ 2 := hc.mul_pow 2
      _ = (r * r) * (l * l) := by rw [sq, sq]
      _ = 1 := by rw [hRsq r hr, hysq l hl, one_mul]

end Elementary

section RankAdd

variable {G : Type} [Group G] [Finite G]

theorem two_le_pRank_kBar {K : Subgroup G}
    (hshape : HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    2 ≤ pRank 2 (kBar K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥K) := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hr : pRank 2 (kBar K) = pRank 2 ↥K :=
    GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two (pPrimeCore 2 ↥K)
      hodd
  rw [hr]
  exact Thm1.two_le_pRank_of_shape hshape

theorem pRank_CxK_add_two_le
    {x : G} {K : Subgroup G} (hxK : IsIL2Pair x K) (hL : HasL2Model (kBar K) Odd) :
    pRank 2 ↥(CxK x K) + 2 ≤ pRank 2 G := by
  have hsimple : IsSimpleGroup (kBar K) := Back.isSimpleGroup_of_hasL2Model hL
  obtain ⟨hZ, -⟩ := Bk.no_central_involution hxK.2 hsimple
  obtain ⟨V, hVel, hV4⟩ :=
    CFSG.StronglyEmbedded.SteinbergBU.exists_four_group_of_two_le_pRank (G := kBar K)
      (two_le_pRank_kBar (Or.inl hL))
  obtain ⟨hVc, hVsq⟩ := Back.forall_of_isElementaryAbelian hVel
  obtain ⟨B, hBle, hBea, hBcard⟩ := exists_elemAbelian_card_pRank (CxK x K)
  obtain ⟨m, Q, hm, hQsq, hQcard⟩ :=
    exists_big_elemAbelian K B hBea (hBle.trans inf_le_right) V hVsq
      (by rw [hV4]; exact ⟨1, by norm_num⟩) hZ
  have hQea := isElementaryAbelian_two_of_mul_self Q hQsq
  have := le_pRank_group_of_elem hQea (k := pRank 2 ↥(CxK x K) + m)
    (by rw [hQcard, hBcard, pow_add])
  omega

end RankAdd

section Aut

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem odd_card_fieldAutSub_of_isFM9_ne_nine (hF : L2Field F) (hfm : IsFM9 (Nat.card F))
    (h9 : Nat.card F ≠ 9) (e : K ≃* L2 F) : Odd (Nat.card ↥(fieldAutSub e)) := by
  obtain ⟨p, n, hp, -, -, hq⟩ := isOddPrimePower_of_L2Field hF
  rw [(ivk_1_2e F hF K e).2.2 p n hp hq]
  rcases hfm with h | ⟨hprime, -⟩
  · exact absurd h h9
  · rw [hq] at hprime
    rw [((Nat.Prime.pow_eq_iff hprime).1 rfl).2]
    exact odd_one

end Aut

section LemmaR

variable {G : Type} [Group G] [Finite G]

theorem card_le_four_mul_inf_CxK
    {x y : G} {K : Subgroup G} (hlu : IsLocallyUnbalancing x y K) {q : ℕ} (hq : IsFM9 q)
    (hL2 : HasL2Model (kBar K) (fun r => r = q)) (A : Subgroup G) (hAN : A ≤ NxK x K)
    (hAel : IsElementaryAbelian 2 ↥A) (hyA : ∀ a ∈ A, a * y = y * a) :
    Nat.card ↥A ≤ 4 * Nat.card ↥(A ⊓ CxK x K) := by
  have hyN : y ∈ normalizer (K : Set G) := hlu.2.2.2.1
  have hLn := Bk.hLn_normalizer K
  obtain ⟨hnotInn, hPGL⟩ := Bk.ivk10_bridge b_ivk_10_2L hlu hq hL2
  set yb : MulAut (kBar K) := Back.actHom hLn ⟨y, hyN⟩ with hyb
  have hyb2 : yb ^ 2 = 1 := by
    rw [hyb, ← map_pow]
    have : (⟨y, hyN⟩ : ↥(normalizer (K : Set G))) ^ 2 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hlu.2.1]
      exact pow_orderOf_eq_one y
    rw [this, map_one]
  have hyb2' : yb * yb = 1 := by rw [← sq]; exact hyb2
  obtain ⟨F, _, _, e0, hF, hFq⟩ := exists_l2Field_of_hasL2Model hq hL2
  have hfmF : IsFM9 (Nat.card F) := hFq ▸ hq
  have hAM : A ≤ normalizer (K : Set G) := hAN.trans inf_le_right
  let αA : ↥A →* MulAut (kBar K) := (Back.actHom hLn).comp (Subgroup.inclusion hAM)
  obtain ⟨hAcomm, hAsq⟩ := Back.forall_of_isElementaryAbelian hAel
  have hEcomm : ∀ a ∈ αA.range, ∀ b ∈ αA.range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have hab : a * b = b * a := Subtype.ext (hAcomm a a.2 b b.2)
    rw [← map_mul, ← map_mul, hab]
  have hEsq : ∀ a ∈ αA.range, a * a = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (hAsq a a.2)
    rw [this, map_one]
  have hEel : IsElementaryAbelian 2 ↥αA.range := Back.isElementaryAbelian_of_forall hEcomm hEsq
  have hycomm : ∀ a ∈ αA.range, a * yb = yb * a := by
    rintro _ ⟨a, rfl⟩
    rw [hyb]
    show (Back.actHom hLn) ⟨(a : G), hAM a.2⟩ * (Back.actHom hLn) ⟨y, hyN⟩ =
      (Back.actHom hLn) ⟨y, hyN⟩ * (Back.actHom hLn) ⟨(a : G), hAM a.2⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hyA a a.2)
  have hE4 : Nat.card ↥αA.range ≤ 4 := by
    by_cases h9 : Nat.card F = 9
    · have hFq' : Nat.card F = 9 := h9
      obtain ⟨e, N, -⟩ :=
        ivk_1_2a_exists F hF (kBar K) e0 (inferInstance : Nonempty (Sylow 2 (MulAut (kBar K)))).some
      have hPGL' : IsPGL2 ↥((MulAut.conj : kBar K →* MulAut (kBar K)).range ⊔ zpowers yb)
          (fun r => r = Nat.card F) := by
        obtain ⟨F₀, i1, i2, hF₀, ⟨ψ⟩⟩ := hPGL
        exact ⟨F₀, i1, i2, hF₀.trans hFq.symm, ⟨ψ⟩⟩
      have hybD : yb ∈ innDiagSub e := mem_innDiagSub_of_isPGL2 hF hfmF e N hyb2 hnotInn hPGL'
      have hEp := isElementaryAbelian_sup_zpowers hEel hyb2' hycomm
      obtain ⟨hcp, hsp⟩ := Back.forall_of_isElementaryAbelian hEp
      have hle : αA.range ≤ αA.range ⊔ zpowers yb := le_sup_left
      calc Nat.card ↥αA.range ≤ Nat.card ↥(αA.range ⊔ zpowers yb) := Subgroup.card_le_of_le hle
        _ ≤ 4 := card_le_four_of_elementary_abelian hF hFq' e N hyb2 hybD hnotInn hcp
              (fun a ha => by rw [sq]; exact hsp a ha) (Subgroup.mem_sup_right (mem_zpowers yb))
    · exact card_le_four_of_sq_aut_odd hF e0
        (odd_card_fieldAutSub_of_isFM9_ne_nine hF hfmF h9 e0) αA.range hEsq
  have hker : αA.ker = (A ⊓ CxK x K).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have hax : (a : G) ∈ centralizer ({x} : Set G) := (hAN a.2).1
    have hkey := Back.actHom_eq_one_iff_commutator_mem hLn ⟨(a : G), hAM a.2⟩
    constructor
    · intro h
      exact ⟨a.2, hax, hAM a.2, TwoThin.mem_normalizer_pPrimeCoreOf (hAM a.2),
        fun k hk => hkey.1 h k hk⟩
    · rintro ⟨-, -, -, -, h⟩
      exact hkey.2 h
  have hcard := Subgroup.card_ker_mul_card_range αA
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_left : A ⊓ CxK x K ≤ A)).toEquiv] at hcard
  calc Nat.card ↥A = Nat.card ↥(A ⊓ CxK x K) * Nat.card ↥αA.range := hcard.symm
    _ ≤ Nat.card ↥(A ⊓ CxK x K) * 4 := Nat.mul_le_mul_left _ hE4
    _ = 4 * Nat.card ↥(A ⊓ CxK x K) := mul_comm _ _

end LemmaR

end CFSG.GH74.GLS.Th2.L625

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2.L625 CFSG.GH74.GLS.C3.Layer1

theorem b_lemma625c2_proved :
    B_lemma625c2 := by
  intro G _ _ hG x y K hV hK5 hCx v w H hlu hrank hL2
  obtain ⟨p, f, hp, hf, ⟨hodd, hfm⟩, hLie⟩ := hL2
  have hL2odd : HasL2Model (kBar H) Odd := ⟨p, f, hp, hf, hodd, hLie⟩
  have hL2q : HasL2Model (kBar H) (fun r => r = p ^ f) := ⟨p, f, hp, hf, rfl, hLie⟩
  have hup : pRank 2 ↥(CxK v H) ≤ 2 := by
    have h1 := pRank_CxK_add_two_le hlu.1 hL2odd
    have h2 := hG.pRank_eq_four
    omega
  refine le_antisymm hup ?_
  by_cases hnorm : ∀ c ∈ centralizer ({v} : Set G), ∀ k ∈ H, c * k * c⁻¹ ∈ H
  ·
    obtain ⟨E, hEle, hEel, hErk⟩ := Th2.exists_elemAbelian_pRank (centralizer ({v, w} : Set G))
    have hEcard : Nat.card ↥E = 16 := by
      rw [Back.card_eq_two_pow_pRank hEel, hErk, hrank]
      norm_num
    have hEcv : ∀ e ∈ E, e ∈ centralizer ({v} : Set G) := fun e he =>
      Subgroup.centralizer_le (Set.singleton_subset_iff.2 (by simp)) (hEle he)
    have hEw : ∀ e ∈ E, e * w = w * e := fun e he =>
      (Subgroup.mem_centralizer_iff.1 (hEle he) w (by simp)).symm
    have hEN : E ≤ NxK v H := fun e he =>
      ⟨hEcv e he, U1a.mem_normalizer_of_norm hnorm (hEcv e he)⟩
    have h16 := card_le_four_mul_inf_CxK hlu (q := p ^ f) hfm hL2q E hEN hEel hEw
    rw [hEcard] at h16
    obtain ⟨hEcomm, hEsq⟩ := Back.forall_of_isElementaryAbelian hEel
    have hel : IsElementaryAbelian 2 ↥(E ⊓ CxK v H) := Back.isElementaryAbelian_of_forall
      (fun a ha b hb => hEcomm a ha.1 b hb.1) (fun a ha => hEsq a ha.1)
    have hpow := Back.card_eq_two_pow_pRank hel
    have hmono := Back.pRank_mono' (inf_le_right : E ⊓ CxK v H ≤ CxK v H)
    by_contra hlt
    push Not at hlt
    have h1 : pRank 2 ↥(E ⊓ CxK v H) ≤ 1 := by omega
    have h2 : 2 ^ pRank 2 ↥(E ⊓ CxK v H) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
    omega
  · exact two_le_pRank_CxK_of_not_normal hlu.1.2 (Or.inl hL2odd) hnorm

end CFSG.GH74.GLS
