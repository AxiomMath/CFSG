module

public import CFSG.GH74.Generic.BProg.B2.Defs
public import CFSG.GH74.Generic.BProg.B2.Lemma82Gen
public import CFSG.GH74.GLS.C3.Layer1.Back112A5
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Uniqueness CFSG.ABGLocalTools
  CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

open CFSG.GH74.GLS.C3.Layer1.Back (mem_conjugate_iff' conjugate_le_conjugate' conjugate_inv_conjugate'
  card_conjugate' pRank_conjugate' isElementaryAbelian_conjugate)

variable {G : Type} [Group G]

namespace Lemma82

theorem mem_normalizer_of_forall {K : Subgroup G} {x : G} (h1 : ∀ n ∈ K, x * n * x⁻¹ ∈ K)
    (h2 : ∀ n ∈ K, x⁻¹ * n * x ∈ K) : x ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro n
  refine ⟨h1 n, fun hn => ?_⟩
  have := h2 _ hn
  rwa [show x⁻¹ * (x * n * x⁻¹) * x = n by group] at this

theorem conj_mem_sup_of_mem_normalizer {A A' : Subgroup G} {x : G}
    (hA : x ∈ normalizer (A : Set G)) (hA' : x ∈ normalizer (A' : Set G)) :
    ∀ n ∈ A ⊔ A', x * n * x⁻¹ ∈ A ⊔ A' := by
  have key : A ⊔ A' ≤ (A ⊔ A').comap (MulAut.conj x).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun a ha => ?_)
    · exact Subgroup.mem_sup_left ((mem_normalizer_iff.1 hA a).1 ha)
    · exact Subgroup.mem_sup_right ((mem_normalizer_iff.1 hA' a).1 ha)
  exact fun n hn => key hn

theorem mem_normalizer_sup {A A' : Subgroup G} {x : G} (hA : x ∈ normalizer (A : Set G))
    (hA' : x ∈ normalizer (A' : Set G)) : x ∈ normalizer ((A ⊔ A' : Subgroup G) : Set G) := by
  refine mem_normalizer_of_forall (conj_mem_sup_of_mem_normalizer hA hA') (fun n hn => ?_)
  have := conj_mem_sup_of_mem_normalizer (inv_mem hA) (inv_mem hA') n hn
  rwa [inv_inv] at this

theorem le_normalizer_pPrimeCoreOf (M : Subgroup G) : M ≤ normalizer (pPrimeCoreOf 2 M : Set G) := by
  have hnormal : (pPrimeCore 2 ↥M).Normal := pPrimeCore_normal
  have key : ∀ m ∈ M, ∀ n ∈ pPrimeCoreOf 2 M, m * n * m⁻¹ ∈ pPrimeCoreOf 2 M := by
    intro m hm n hn
    obtain ⟨n0, hn0, rfl⟩ := Subgroup.mem_map.1 hn
    exact Subgroup.mem_map.2 ⟨⟨m, hm⟩ * n0 * ⟨m, hm⟩⁻¹, hnormal.conj_mem n0 hn0 ⟨m, hm⟩, by simp⟩
  intro m hm
  exact mem_normalizer_of_forall (key m hm) (fun n hn => by simpa using key m⁻¹ (M.inv_mem hm) n hn)

theorem odd_card_pPrimeCoreOf [Finite G] (M : Subgroup G) : Odd (Nat.card ↥(pPrimeCoreOf 2 M)) := by
  rw [pPrimeCoreOf, Subgroup.card_map_of_injective M.subtype_injective]
  exact Nat.coprime_two_left.1 pPrimeCore_coprime_card

end Lemma82

open Lemma82

theorem normalizer_pPrimeCoreOf_ne_top [Finite G] (hG : IsSimpleGroup G) {M : Subgroup G}
    (hM : IsCoatom M) (hO : pPrimeCoreOf 2 M ≠ ⊥) : normalizer (pPrimeCoreOf 2 M : Set G) ≠ ⊤ := by
  intro htop
  have hnormal : (pPrimeCoreOf 2 M).Normal := Subgroup.normalizer_eq_top_iff.1 htop
  rcases hG.eq_bot_or_eq_top_of_normal (pPrimeCoreOf 2 M) with h | h
  · exact hO h
  · exact hM.1 (top_le_iff.1 (h ▸ (Subgroup.map_subtype_le _ : pPrimeCoreOf 2 M ≤ M)))

namespace Lemma82

theorem conjugate_le_normalizer_conjugate {K L : Subgroup G} (h : G)
    (hKL : K ≤ normalizer (L : Set G)) :
    conjugate K h ≤ normalizer (conjugate L h : Set G) := by
  intro x hx
  have hx' : h * x * h⁻¹ ∈ normalizer (L : Set G) := hKL (mem_conjugate_iff'.1 hx)
  rw [mem_normalizer_iff] at hx' ⊢
  intro n
  rw [mem_conjugate_iff', mem_conjugate_iff']
  have := hx' (h * n * h⁻¹)
  rw [show h * x * h⁻¹ * (h * n * h⁻¹) * (h * x * h⁻¹)⁻¹ = h * (x * n * x⁻¹) * h⁻¹ by group] at this
  exact this

theorem centralizer_le_conjugate {E Z : Subgroup G} (h : G)
    (hZ : centralizer (conjugate E h⁻¹ : Set G) ≤ Z) : centralizer (E : Set G) ≤ conjugate Z h := by
  intro y hy
  rw [mem_conjugate_iff']
  apply hZ
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro e₀ he₀
  have he : h⁻¹ * e₀ * h ∈ E := by
    have := mem_conjugate_iff'.1 he₀
    rwa [inv_inv] at this
  have h1 := hy _ he
  calc e₀ * (h * y * h⁻¹) = h * ((h⁻¹ * e₀ * h) * y) * h⁻¹ := by group
    _ = h * (y * (h⁻¹ * e₀ * h)) * h⁻¹ := by rw [h1]
    _ = (h * y * h⁻¹) * e₀ := by group

theorem centralizer_le_gammaKC {B E : Subgroup G} {p k : ℕ} (hEB : E ≤ B) (hk : k ≤ pRank p ↥E) :
    centralizer (E : Set G) ≤ gammaKC p B k :=
  le_iSup_of_le E (le_iSup_of_le hEB (le_iSup_of_le hk le_rfl))

end Lemma82

theorem le_gammaKC_of_odd_normalized [Finite G] {B Y : Subgroup G} (hB : CFSG.IsElementaryAbelian 2 ↥B)
    (hr : 2 ≤ pRank 2 ↥B) (hBY : B ≤ normalizer (Y : Set G)) (hY : Odd (Nat.card ↥Y)) :
    Y ≤ gammaKC 2 B (pRank 2 ↥B - 1) := by
  refine (le_iSup_centralizer_hyperplanes hB hr hBY hY).trans ?_
  exact iSup_le fun E => iSup_le fun hE => iSup_le fun hk =>
    inf_le_right.trans (centralizer_le_gammaKC hE hk)

namespace Lemma82

theorem odd_card_sup_of_le_normalizer [Finite G] {A A' : Subgroup G} (hA : Odd (Nat.card ↥A))
    (hA' : Odd (Nat.card ↥A')) (hn : A' ≤ normalizer (A : Set G)) : Odd (Nat.card ↥(A ⊔ A')) := by
  by_contra hodd
  have heven : 2 ∣ Nat.card ↥(A ⊔ A') := by
    rcases Nat.even_or_odd (Nat.card ↥(A ⊔ A')) with h | h
    · exact even_iff_two_dvd.1 h
    · exact absurd h hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(A ⊔ A')) 2 heven
  have hx2 : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hxmem : (x : G) ∈ ((A ⊔ A' : Subgroup G) : Set G) := x.2
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A A' hn] at hxmem
  obtain ⟨a, ha, b, hb, hab0⟩ := hxmem
  have hab : a * b = (x : G) := hab0
  have hxx : (x : G) * x = 1 := by rw [← sq, ← hx2]; exact pow_orderOf_eq_one _
  have hxx' : a * b * (a * b) = 1 := by rw [hab]; exact hxx
  have hb2 : b * b ∈ A := by
    have h1 : b * a⁻¹ * b⁻¹ ∈ A := (mem_normalizer_iff.1 (hn hb) a⁻¹).1 (A.inv_mem ha)
    have h2 : b * b = (b * a⁻¹ * b⁻¹) * a⁻¹ := by
      calc b * b = (b * a⁻¹ * b⁻¹ * a⁻¹) * (a * b * (a * b)) := by group
        _ = (b * a⁻¹ * b⁻¹) * a⁻¹ := by rw [hxx', mul_one]
    rw [h2]
    exact A.mul_mem h1 (A.inv_mem ha)
  have hbA : b ∈ A := by
    obtain ⟨m, hm⟩ : Odd (orderOf b) := Odd.of_dvd_nat hA' (Subgroup.orderOf_dvd_natCard A' hb)
    have h2 : b ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one b
    have h1 : (b * b) ^ (m + 1) = b := by
      calc (b * b) ^ (m + 1) = b ^ (2 * m + 1 + 1) := by
            rw [← sq, ← pow_mul]
            congr 1
        _ = b := by rw [pow_succ, h2, one_mul]
    rw [← h1]
    exact A.pow_mem hb2 (m + 1)
  have hxA : (x : G) ∈ A := by rw [← hab]; exact A.mul_mem ha hbA
  have hdvd : 2 ∣ Nat.card ↥A := hx2 ▸ Subgroup.orderOf_dvd_natCard A hxA
  have hodd' := Nat.odd_iff.1 hA
  omega

end Lemma82

theorem lemma82_core [Finite G] {M B : Subgroup G} {h : G} (S : Sym8A M B h) :
    conjugate (pPrimeCoreOf 2 M) h ≤ M ∧ pPrimeCoreOf 2 M ≤ conjugate M h ∧
      sigX M h ≤ M ⊓ conjugate M h ∧ M ⊓ conjugate M h ≤ normalizer (sigX M h : Set G) ∧
      Odd (Nat.card ↥(sigX M h)) ∧
      ∀ E : Subgroup G, E ≤ conjugate B h → pRank 2 ↥B - 1 ≤ pRank 2 ↥E →
        centralizer (E : Set G) ≤ conjugate M h := by
  obtain ⟨-, -, ⟨⟨-, hBel, hBr⟩, -, hΓ⟩, -, D_le, B_le⟩ := S
  have hNM : pPrimeCoreOf 2 M ≤ M := Subgroup.map_subtype_le _
  have hMN : M ≤ normalizer (pPrimeCoreOf 2 M : Set G) := le_normalizer_pPrimeCoreOf M
  have hNodd : Odd (Nat.card ↥(pPrimeCoreOf 2 M)) := odd_card_pPrimeCoreOf M
  have hNhodd : Odd (Nat.card ↥(conjugate (pPrimeCoreOf 2 M) h)) := by
    rw [card_conjugate']
    exact hNodd
  have h7 : ∀ E : Subgroup G, E ≤ conjugate B h → pRank 2 ↥B - 1 ≤ pRank 2 ↥E →
      centralizer (E : Set G) ≤ conjugate M h := by
    intro E hE hrk
    apply centralizer_le_conjugate h
    have hE0 : conjugate E h⁻¹ ≤ B := by
      have := conjugate_le_conjugate' hE h⁻¹
      rwa [conjugate_inv_conjugate'] at this
    have hrk0 : pRank 2 ↥B - 1 ≤ pRank 2 ↥(conjugate E h⁻¹) := by
      rwa [pRank_conjugate']
    exact (centralizer_le_gammaKC hE0 hrk0).trans hΓ
  have h1 : conjugate (pPrimeCoreOf 2 M) h ≤ M :=
    (le_gammaKC_of_odd_normalized hBel hBr
      (B_le.trans (conjugate_le_normalizer_conjugate h hMN)) hNhodd).trans hΓ
  have h2 : pPrimeCoreOf 2 M ≤ conjugate M h := by
    have hDel : CFSG.IsElementaryAbelian 2 ↥(conjugate B h) := isElementaryAbelian_conjugate hBel h
    have hDr : 2 ≤ pRank 2 ↥(conjugate B h) := by rwa [pRank_conjugate']
    refine (le_iSup_centralizer_hyperplanes hDel hDr (D_le.trans hMN) hNodd).trans ?_
    refine iSup_le fun E => iSup_le fun hE => iSup_le fun hrk => ?_
    rw [pRank_conjugate'] at hrk
    exact inf_le_right.trans (h7 E hE hrk)
  have h3 : sigX M h ≤ M ⊓ conjugate M h :=
    sup_le (le_inf hNM h2) (le_inf h1 (conjugate_le_conjugate' hNM h))
  refine ⟨h1, h2, h3, ?_, ?_, h7⟩
  · intro x hx
    exact mem_normalizer_sup (hMN hx.1) (conjugate_le_normalizer_conjugate h hMN hx.2)
  · exact odd_card_sup_of_le_normalizer hNodd hNhodd (h1.trans hMN)

theorem lemma82 [Finite G] {M B : Subgroup G} {h : G} (S : Sym8A M B h)
    (hnot : normalizer (pPrimeCoreOf 2 M : Set G) ≠ ⊤) :
    conjugate (pPrimeCoreOf 2 M) h ≤ M ∧ pPrimeCoreOf 2 M ≤ conjugate M h ∧
      sigX M h ≤ M ⊓ conjugate M h ∧ M ⊓ conjugate M h ≤ normalizer (sigX M h : Set G) ∧
      Odd (Nat.card ↥(sigX M h)) ∧ ¬ sigX M h ≤ pPrimeCoreOf 2 M ∧
      ∀ E : Subgroup G, E ≤ conjugate B h → pRank 2 ↥B - 1 ≤ pRank 2 ↥E →
        centralizer (E : Set G) ≤ conjugate M h := by
  obtain ⟨h1, h2, h3, h4, h5, h7⟩ := lemma82_core S
  refine ⟨h1, h2, h3, h4, h5, ?_, h7⟩
  have hMN : M ≤ normalizer (pPrimeCoreOf 2 M : Set G) := le_normalizer_pPrimeCoreOf M
  intro hle
  have hle' : conjugate (pPrimeCoreOf 2 M) h ≤ pPrimeCoreOf 2 M := le_sup_right.trans hle
  have heq : conjugate (pPrimeCoreOf 2 M) h = pPrimeCoreOf 2 M :=
    Subgroup.eq_of_le_of_card_ge hle' (by rw [card_conjugate'])
  have hhN : h ∈ normalizer (pPrimeCoreOf 2 M : Set G) := by
    rw [mem_normalizer_iff]
    intro n
    have := mem_conjugate_iff' (H := pPrimeCoreOf 2 M) (g := h) (x := n)
    rwa [heq] at this
  have hle2 : normalizer (pPrimeCoreOf 2 M : Set G) ≤ M := by
    by_contra hlt
    exact hnot (S.maxM.2 _ (lt_of_le_not_ge hMN hlt))
  exact S.h_not (hle2 hhN)

theorem conjugate_B_le_normalizer_sigX [Finite G] {M B : Subgroup G} {h : G} (S : Sym8A M B h) :
    conjugate B h ≤ normalizer (sigX M h : Set G) :=
  fun _ hx => (lemma82_core S).2.2.2.1 ⟨S.D_le hx, conjugate_le_conjugate' S.hB.1.1 h hx⟩

theorem inf_centralizer_le_normalizer_sigX_conjugate [Finite G] {M B : Subgroup G} {h : G}
    (S : Sym8A M B h) {E : Subgroup G} (hE : E ≤ conjugate B h) (hrk : pRank 2 ↥B - 1 ≤ pRank 2 ↥E) :
    M ⊓ centralizer (E : Set G) ≤ normalizer (sigX M h : Set G) :=
  fun _ hx => (lemma82_core S).2.2.2.1 ⟨hx.1, (lemma82_core S).2.2.2.2.2 E hE hrk hx.2⟩

end CFSG.GH74.Generic.BProg.B2
