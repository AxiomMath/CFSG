module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129e
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129d

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129f

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129d
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129e
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf autBar barAut innerAut)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (centralizer_barX_eq card_barX_of_isPGroup elemAbelian_barX)

section OrbitBig

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D S F K : Subgroup G}

theorem A0_inf_F_ne_bot (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K) :
    E ⊓ A ⊓ F ≠ ⊥ := by
  intro hbot
  have hp := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  have hFA := hs.F_le_A
  have hA0el : IsElemAbelian p (E ⊓ A) := (A_el h).mono inf_le_right
  have hcard := Lemma129b.card_sup_of_commute_disjoint (H := E ⊓ A) (K := F)
    (fun x hx y hy => elemAbelian_comm (A_el h) hx.2 (hFA hy)) hbot
  have hle : (E ⊓ A) ⊔ F ≤ A := sup_le inf_le_right hFA
  have h1 : Nat.card ↥((E ⊓ A) ⊔ F) ≤ Nat.card A := Subgroup.card_le_of_le hle
  have h2 : Nat.card A ≤ p * Nat.card F := by
    have := Subgroup.card_mul_index (F.subgroupOf A)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFA).toEquiv] at this
    rw [← this, mul_comm]
    exact Nat.mul_le_mul_right _ (hs.index_le hp)
  have h3 : Nat.card (E ⊓ A : Subgroup G) * Nat.card F ≤ p * Nat.card F := by
    rw [← hcard]; exact h1.trans h2
  have h4 : Nat.card (E ⊓ A : Subgroup G) ≤ p := Nat.le_of_mul_le_mul_right h3 Nat.card_pos
  have h5 : p ^ 2 ≤ Nat.card (E ⊓ A : Subgroup G) := by
    rw [card_eq_pow_pRank hp hA0el]
    exact Nat.pow_le_pow_right hp.pos (two_le_rank_inf h)
  have : p * p ≤ p := by nlinarith
  nlinarith [hp.two_le]

theorem implementer_range_ne_bot (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (κ₀ : ↥(barX p N (E ⊓ A)) →* ↥(barX p N K))
    (hκ₀ : ∀ (a : ↥(barX p N (E ⊓ A))) (x : ↥(barX p N K)),
      ((a : barX p N (E ⊓ A)) : ↥N ⧸ GLAPPrimeCore p ↥N) * (x : ↥N ⧸ GLAPPrimeCore p ↥N) *
        ((a : barX p N (E ⊓ A)) : ↥N ⧸ GLAPPrimeCore p ↥N)⁻¹ =
      ((κ₀ a : ↥(barX p N K)) : ↥N ⧸ GLAPPrimeCore p ↥N) * (x : ↥N ⧸ GLAPPrimeCore p ↥N) *
        ((κ₀ a : ↥(barX p N K)) : ↥N ⧸ GLAPPrimeCore p ↥N)⁻¹) :
    κ₀.range ≠ ⊥ := by
  intro hbot
  have hp := prime_of h
  have hAN := A_le_N h
  apply A0_inf_F_ne_bot h hs
  rw [eq_bot_iff]
  rintro x ⟨⟨hxE, hxA⟩, hxF⟩
  have hxN : x ∈ N := hAN hxA
  have hxK : x ∈ Subgroup.normalizer (K : Set G) := hs.hFK hxF
  have hxbar : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hxN⟩ ∈ barX p N (E ⊓ A) :=
    ⟨⟨x, hxN⟩, (Subgroup.mem_subgroupOf).2 ⟨hxE, hxA⟩, rfl⟩
  have hκ1 : κ₀ ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hxN⟩, hxbar⟩ = 1 := by
    have : κ₀ ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hxN⟩, hxbar⟩ ∈ κ₀.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hcent : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hxN⟩ ∈
      Subgroup.centralizer ((barX p N K : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) :
        Set (↥N ⧸ GLAPPrimeCore p ↥N)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := hκ₀ ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hxN⟩, hxbar⟩ ⟨y, hy⟩
    rw [hκ1] at h1
    simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at h1
    calc y * QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hxN⟩
        = (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hxN⟩ * y *
            (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hxN⟩)⁻¹) *
            QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hxN⟩ := by rw [h1]
      _ = QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hxN⟩ * y := by group
  have hxc : x ∈ centBar p ⊤ K :=
    Lemma129b.mem_centBar_of_barX_centralizes hp hs.hK hxN hxK hcent
  have : x ∈ F ⊓ centBar p ⊤ K := ⟨hxF, hxc⟩
  rw [hs.hFc, Subgroup.mem_bot] at this
  exact (Subgroup.mem_bot).2 this

theorem alt_orbit_big (h23 : Input23_5) (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (D' : AltData p N K F) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hcase : CFSG.Open.pRank p A = CFSG.Open.pRank p F ∨
      (p = 3 ∧ D'.δ = 4 ∧ CFSG.Open.pRank p A = CFSG.Open.pRank p F + 1))
    (κ₀ : ↥(barX p N (E ⊓ A)) →* ↥(barX p N K))
    (hκ₀ : ∀ (a : ↥(barX p N (E ⊓ A))) (x : ↥(barX p N K)),
      ((a : barX p N (E ⊓ A)) : ↥N ⧸ GLAPPrimeCore p ↥N) * (x : ↥N ⧸ GLAPPrimeCore p ↥N) *
        ((a : barX p N (E ⊓ A)) : ↥N ⧸ GLAPPrimeCore p ↥N)⁻¹ =
      ((κ₀ a : ↥(barX p N K)) : ↥N ⧸ GLAPPrimeCore p ↥N) * (x : ↥N ⧸ GLAPPrimeCore p ↥N) *
        ((κ₀ a : ↥(barX p N K)) : ↥N ⧸ GLAPPrimeCore p ↥N)⁻¹) :
    ∃ i : Fin D'.n, p ^ CFSG.Open.pRank p F ≤ orbitLen D'.ψ κ₀.range i := by
  have hp := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 := ne_two_of h
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hAN := A_le_N h
  have hn11 := D'.hn11 hp3 hs.hr
  have hn := D'.hn
  have hδ := D'.hδ
  have hA0el : IsElemAbelian p (E ⊓ A) := (A_el h).mono inf_le_right
  have hB₀ne := implementer_range_ne_bot h hs κ₀ hκ₀
  have hB₀p : IsPGroup p κ₀.range := by
    have hFtop : IsElemAbelian p (⊤ : Subgroup ↥(barX p N (E ⊓ A))) := by
      have := (isElemAbelian_barX (p := p) (C := N) hA0el).subgroupOf (barX p N (E ⊓ A))
      rwa [Subgroup.subgroupOf_self] at this
    rw [MonoidHom.range_eq_map]
    exact (hFtop.map κ₀).isPGroup
  by_contra hno
  push Not at hno
  obtain ⟨t, ht1, hall, i₀, hi₀⟩ := exists_orbit_exponent hp D'.ψ hB₀p hB₀ne
  have htr : t < CFSG.Open.pRank p F := by
    have := hno i₀
    rw [hi₀] at this
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 this
  have hpr : p ^ CFSG.Open.pRank p F ≤ D'.n := by
    have h1 : p ^ CFSG.Open.pRank p F ≤ D'.m * p ^ CFSG.Open.pRank p F :=
      Nat.le_mul_of_pos_left _ D'.hm
    omega
  have hpn : ¬ p ∣ D'.n := by
    intro hdvd
    have h1 : p ∣ D'.m * p ^ CFSG.Open.pRank p F :=
      Dvd.dvd.mul_left (dvd_pow_self p (by have := hs.hr; omega)) _
    have h2 : p ∣ D'.δ := (Nat.dvd_add_right h1).1 (hn ▸ hdvd)
    rcases hδ with hδ | hδ <;> rw [hδ] at h2
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
    · have : p ∣ 2 ^ 2 := by simpa using h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this))
  have htn : p ^ (t + 1) < D'.n := by
    calc p ^ (t + 1) ≤ p ^ CFSG.Open.pRank p F := Nat.pow_le_pow_right hp.pos htr
      _ < D'.n := by
        have h1 : p ^ CFSG.Open.pRank p F ≤ D'.m * p ^ CFSG.Open.pRank p F :=
          Nat.le_mul_of_pos_left _ D'.hm
        omega
  obtain ⟨P, hPN, hPel, hPc, hPrank, hPK, hcov⟩ := acl_cover h23 h hpn ht1 htn D'.ψ κ₀ hκ₀ hB₀ne hall
    ⟨i₀, hi₀⟩
  have hbig : CFSG.Open.pRank p A < CFSG.Open.pRank p ((E ⊓ A) ⊔ P) := by
    have hge : CFSG.Open.pRank p P ≤ CFSG.Open.pRank p ((E ⊓ A) ⊔ P) :=
      pRank_le_of_le hp le_sup_right
    rcases hcase with hc | ⟨hp3', hδ4, hc⟩
    · have := arith_big hp3 hs.hr ht1 htr hpr
      omega
    · subst hp3'
      have hn3 : 3 ^ CFSG.Open.pRank 3 F + 4 ≤ D'.n := by
        have h1 : 3 ^ CFSG.Open.pRank 3 F ≤ D'.m * 3 ^ CFSG.Open.pRank 3 F :=
          Nat.le_mul_of_pos_left _ D'.hm
        omega
      have := arith_strict hs.hr ht1 htr hn3
      omega
  exact hs.hnc (hcov hbig)

end OrbitBig

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129f

end
