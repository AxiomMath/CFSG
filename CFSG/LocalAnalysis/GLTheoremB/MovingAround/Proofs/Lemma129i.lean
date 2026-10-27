module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129W3
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129g

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129i

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129d
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129e
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129f
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129g
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129b
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf autBar barAut innerAut)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (centralizer_barX_eq card_barX_of_isPGroup elemAbelian_barX)

section Helpers

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D S F K : Subgroup G}

theorem A_eq_sup_of_not_mem (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    {a : G} (haA : a ∈ A) (haK : a ∉ Subgroup.normalizer (K : Set G)) :
    A = F ⊔ Subgroup.zpowers a ∧ F ⊓ Subgroup.zpowers a = ⊥ := by
  have hp := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  have hFA := hs.F_le_A
  have hFne : F ≠ A := by
    intro hFA'
    apply haK
    apply hs.hFK
    rw [hFA']
    exact haA
  have haF : a ∉ F := fun haF => haK (hs.hFK haF)
  have hap : a ^ p = 1 := (A_el h).2 a haA
  have ha1 : a ≠ 1 := fun h1 => haK (h1 ▸ Subgroup.one_mem _)
  have hord : orderOf a = p := orderOf_eq_prime hap ha1
  have hFa : F ⊓ Subgroup.zpowers a = ⊥ := by
    have hcardz : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hord]
    haveI : Fact (Nat.card (Subgroup.zpowers a)).Prime := ⟨hcardz ▸ hp⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card
      ((F ⊓ Subgroup.zpowers a).subgroupOf (Subgroup.zpowers a)) with h1 | h1
    · ext x
      constructor
      · intro hx
        have : (⟨x, hx.2⟩ : Subgroup.zpowers a) ∈ (F ⊓ Subgroup.zpowers a).subgroupOf
            (Subgroup.zpowers a) := Subgroup.mem_subgroupOf.2 hx
        rw [h1, Subgroup.mem_bot] at this
        exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
      · intro hx
        rw [Subgroup.mem_bot] at hx
        rw [hx]; exact Subgroup.one_mem _
    · exfalso
      have : (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) ∈
          (F ⊓ Subgroup.zpowers a).subgroupOf (Subgroup.zpowers a) := by
        rw [h1]; exact Subgroup.mem_top _
      exact haF (Subgroup.mem_subgroupOf.1 this).1
  refine ⟨?_, hFa⟩
  have hle : F ⊔ Subgroup.zpowers a ≤ A := sup_le hFA (Subgroup.zpowers_le.2 haA)
  have hcard : Nat.card ↥(F ⊔ Subgroup.zpowers a) = Nat.card A := by
    rw [Lemma129b.card_sup_of_commute_disjoint (fun u hu b hb => ?_) hFa, card_A_of_ne hp hs hFne,
      Nat.card_zpowers, hord, mul_comm]
    exact elemAbelian_comm (A_el h) (hFA hu) ((Subgroup.zpowers_le.2 haA) hb)
  exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)).symm

theorem barX_F_le_kstar (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (hCF : A ⊓ Subgroup.normalizer (K : Set G) = F)
    {a : G} (haA : a ∈ A) (hap : a ^ p = 1) (hAeq : A = F ⊔ Subgroup.zpowers a)
    (hcapG : ∀ n : ℕ, 0 < n → n < p → a ^ n ∉ Subgroup.normalizer (K : Set G))
    (hFinner : ∀ f ∈ barX p N F, ∃ k ∈ barX p N K, ∀ y ∈ barX p N K, f * y * f⁻¹ = k * y * k⁻¹) :
    barX p N F ≤ Lemma129W.kstar p (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a, A_le_N h haA⟩)
      (barX p N K) := by
  have hp := prime_of h
  have hAN := A_le_N h
  have hKb : IsComponentOf (barX p N K) ⊤ := hs.hK.2.2.1
  intro f hf
  obtain ⟨⟨f₀, hfN⟩, hfF, rfl⟩ := hf
  have hfF' : f₀ ∈ F := (Subgroup.mem_subgroupOf).1 hfF
  obtain ⟨k, hk, hgk⟩ := hFinner _ ⟨⟨f₀, hfN⟩, hfF, rfl⟩
  exact Lemma129W2.mem_kstar_of_inner (barX p N K) _
    (kconj_comm hKb (bc_hcap hp hs.hK (hAN haA) hcapG))
    (bc_centralizer_kstar h hs hCF haA hap hAeq)
    (mk_comm_of_comm hfN (hAN haA) (elemAbelian_comm (A_el h) (hs.F_le_A hfF') haA)) hk hgk

theorem kstar_le_normalizer {Y : Type} [Group Y] {p : ℕ} {K : Subgroup Y} {a : Y}
    (hcomm : ∀ i j : Fin p, i ≠ j → ∀ x ∈ Lemma129W.kconj a K i, ∀ y ∈ Lemma129W.kconj a K j,
      x * y = y * x) (hp : 0 < p) :
    Lemma129W.kstar p a K ≤ Subgroup.normalizer (K : Set Y) := by
  refine iSup_le fun i => ?_
  by_cases hi : (i : ℕ) = 0
  · have : Lemma129W.kconj a K i = K := by
      ext x
      simp [Lemma129W.kconj, hi, MulAut.conj_apply]
    rw [this]
    exact Subgroup.le_normalizer
  · have hne : i ≠ ⟨0, hp⟩ := fun h0 => hi (by simp [h0])
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hK0 : ∀ z ∈ K, z ∈ Lemma129W.kconj a K ((⟨0, hp⟩ : Fin p) : ℕ) := fun z hz =>
      Subgroup.mem_map.2 ⟨z, hz, by simp [MulAut.conj_apply]⟩
    have hc : ∀ z ∈ K, x * z = z * x := fun z hz => hcomm i ⟨0, hp⟩ hne x hx z (hK0 z hz)
    constructor
    · intro hy
      have := hc y hy
      rw [this]
      simpa using hy
    · intro hy
      have hxz := hc _ hy
      have : y = x * y * x⁻¹ := by
        calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
          _ = x * y * x⁻¹ := by
            rw [show x⁻¹ * (x * y * x⁻¹) * x = x⁻¹ * ((x * y * x⁻¹) * x) by group, ← hxz]
            group
      rw [this]
      exact hy

theorem S_comm_M (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K) :
    ∀ s ∈ barX p N S, ∀ μ ∈ barX p N M, s * μ * s⁻¹ * μ⁻¹ ∈ barX p N (pCoreOf 2 M) := by
  rintro _ ⟨σ, hσ, rfl⟩ _ ⟨μ, hμ, rfl⟩
  have hσS : (σ : G) ∈ S := (Subgroup.mem_subgroupOf).1 hσ
  have hμM : (μ : G) ∈ M := (Subgroup.mem_subgroupOf).1 hμ
  refine ⟨σ * μ * σ⁻¹ * μ⁻¹, (Subgroup.mem_subgroupOf).2 ?_, by simp⟩
  have h1 : (σ : G) ∈ pCoreOf 2 M := hs.hS.le hσS
  have h2 : (μ : G) * (σ : G)⁻¹ * (μ : G)⁻¹ ∈ pCoreOf 2 M :=
    (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hμM) _).1 ((pCoreOf 2 M).inv_mem h1)
  have h3 := (pCoreOf 2 M).mul_mem h1 h2
  have e : ((σ * μ * σ⁻¹ * μ⁻¹ : ↥N) : G) = (σ : G) * ((μ : G) * (σ : G)⁻¹ * (μ : G)⁻¹) := by
    simp [mul_assoc]
  rw [e]
  exact h3

theorem alt_norm (h23 : Input23_5) (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (D' : AltData p N K F) : A ≤ Subgroup.normalizer (K : Set G) := by
  by_contra hAK
  have hp := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 := ne_two_of h
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hAN := A_le_N h
  have hFA' := hs.F_le_A
  have hFN : F ≤ N := hFA'.trans hAN
  have hCF := inf_normalizer_eq_of_not_le h hs hAK
  have hFne : F ≠ A := fun hFA => hAK (hFA ▸ hs.hFK)
  have hFel : IsElemAbelian p F := (A_el h).mono hFA'
  have hAr : CFSG.Open.pRank p A = CFSG.Open.pRank p F + 1 := by
    have h1 := card_A_of_ne hp hs hFne
    rw [card_eq_pow_pRank hp (A_el h), card_eq_pow_pRank hp hFel, ← pow_succ'] at h1
    exact (Nat.pow_right_injective hp.two_le) h1
  obtain ⟨a₀, ha₀EA, ha₀K⟩ := exists_a_in_A0 h hs hAr hAK hCF (AltData.hFinner D')
  have ha₀A : a₀ ∈ A := ha₀EA.2
  have ha₀N : a₀ ∈ N := hAN ha₀A
  have hap : a₀ ^ p = 1 := (A_el h).2 a₀ ha₀A
  have hcapG := hcap_of_inf_normalizer h hs hCF ha₀A ha₀K
  obtain ⟨hAeq, hFa⟩ := A_eq_sup_of_not_mem h hs ha₀A ha₀K
  have hKb : IsComponentOf (barX p N K) ⊤ := hs.hK.2.2.1
  have hcapY := bc_hcap hp hs.hK ha₀N hcapG
  have hcommY := kconj_comm hKb hcapY
  have hā : (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩) ^ p = 1 := mk_pow_eq_one ha₀N hap
  have hn11 := D'.hn11 hp3 hs.hr
  have hcenter : ∀ z ∈ barX p N K, (∀ y ∈ barX p N K, z * y = y * z) → z = 1 := by
    intro z hz hzc
    have := eq_one_of_central (K₀ := barX p N K) (n := D'.n) (by omega) D'.ψ
      (z := ⟨z, hz⟩) (fun x => Subtype.ext (hzc x x.2))
    exact congrArg Subtype.val this
  obtain ⟨Δ, π₀, hΔinj, hΔ2, hΔ3, hΔ4, hπ4, hπ5, hπ6, hπ7⟩ := Lemma129W3.exists_diagonal p
    (barX p N K) (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩) hā hcommY hcenter hcapY
  have hFa' : ∀ f ∈ F, f * a₀ = a₀ * f := fun f hf => elemAbelian_comm (A_el h) (hFA' hf) ha₀A
  have hFkstar := barX_F_le_kstar h hs hCF ha₀A hap hAeq hcapG (AltData.hFinner D')
  let K₀ : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N) := Δ.range
  let ψ₀ : ↥K₀ ≃* alternatingGroup (Fin D'.n) := (MonoidHom.ofInjective hΔinj).symm.trans D'.ψ
  have hconj : ∀ (x₀ : G) (hx₀N : x₀ ∈ N), x₀ ∈ A → ∀ w ∈ K₀,
      QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x₀, hx₀N⟩ * w *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x₀, hx₀N⟩)⁻¹ ∈ K₀ := by
    intro x₀ hx₀N hx₀A w hw
    obtain ⟨f, hfF, j, hxj⟩ := exists_mul_pow_of_mem_sup hp.pos hap hFa' (hAeq ▸ hx₀A)
    have hfN : f ∈ N := hFN hfF
    obtain ⟨y, rfl⟩ := hw
    have hπx : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x₀, hx₀N⟩ =
        QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨f, hfN⟩ *
          (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩) ^ j := by
      have : (⟨x₀, hx₀N⟩ : ↥N) = ⟨f, hfN⟩ * ⟨a₀, ha₀N⟩ ^ j := Subtype.ext hxj
      rw [this, map_mul, map_pow]
    have hfbks : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨f, hfN⟩ ∈
        Lemma129W.kstar p (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩) (barX p N K) :=
      hFkstar ⟨⟨f, hfN⟩, (Subgroup.mem_subgroupOf).2 hfF, rfl⟩
    have hfbc : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨f, hfN⟩ *
        QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩ =
        QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩ *
          QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨f, hfN⟩ :=
      mk_comm_of_comm hfN ha₀N (hFa' f hfF)
    obtain ⟨u, hu⟩ := hΔ3 _ hfbks hfbc
    have hcomm' : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩ ^ j * Δ y =
        Δ y * QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩ ^ j :=
      ((Commute.pow_right (show Commute (Δ y) (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩)
        from (hΔ2 y).2) j).eq).symm
    rw [hπx, ← hu]
    refine ⟨u * y * u⁻¹, ?_⟩
    calc Δ (u * y * u⁻¹) = Δ u * Δ y * (Δ u)⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = Δ u * ((QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩) ^ j * Δ y *
            ((QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩) ^ j)⁻¹) * (Δ u)⁻¹ := by
          rw [hcomm']; group
      _ = Δ u * (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩) ^ j * Δ y *
            (Δ u * (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩) ^ j)⁻¹ := by group
  have hnorm : barX p N (E ⊓ A) ≤ Subgroup.normalizer (K₀ : Set (↥N ⧸ GLAPPrimeCore p ↥N)) := by
    refine le_normalizer_of_conj_mem fun a ha x hx => ?_
    obtain ⟨⟨x₀, hx₀N⟩, hx₀, rfl⟩ := ha
    exact hconj x₀ hx₀N ((Subgroup.mem_subgroupOf).1 hx₀).2 x hx
  have hHp : IsPGroup p ↥(barX p N (E ⊓ A)) :=
    Lemma129.isPGroup_barX ((A_el h).mono inf_le_right).isPGroup (inf_le_right.trans hAN)
  obtain ⟨κ₀, hκ₀⟩ := exists_implementer (K₀ := K₀) (n := D'.n) (by omega) (by omega) ψ₀ hp hp2
    hnorm hHp
  have hā1 : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩ ≠ 1 := by
    intro h1
    apply ha₀K
    refine mem_normalizer_of_mk hp hs.hK ha₀N ?_
    rw [h1]
    exact Subgroup.one_mem _
  have hāmem : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩ ∈ barX p N (E ⊓ A) :=
    ⟨⟨a₀, ha₀N⟩, (Subgroup.mem_subgroupOf).2 ha₀EA, rfl⟩
  have hκā : κ₀ ⟨_, hāmem⟩ = 1 := by
    apply impl_unique (by omega) ψ₀
    intro x
    rw [← hκ₀ ⟨_, hāmem⟩ x]
    obtain ⟨y, hy⟩ := x.2
    have hc := (hΔ2 y).2
    simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one]
    rw [← hy]
    calc QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩ * Δ y *
          (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩)⁻¹
        = (Δ y * QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩) *
          (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩)⁻¹ := by rw [← hc]
      _ = Δ y := by group
  have hA0card : Nat.card (E ⊓ A : Subgroup G) ≤ p ^ CFSG.Open.pRank p F := by
    have hAcard : Nat.card A = p ^ (CFSG.Open.pRank p F + 1) := by
      rw [card_eq_pow_pRank hp (A_el h), hAr]
    have hlt : Nat.card (E ⊓ A : Subgroup G) < Nat.card A := card_lt_of_lt' (A0_lt_A h)
    have hdvd : Nat.card (E ⊓ A : Subgroup G) ∣ p ^ (CFSG.Open.pRank p F + 1) := by
      have := Subgroup.card_dvd_of_le (inf_le_right : E ⊓ A ≤ A)
      rwa [hAcard] at this
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    rw [hjeq] at hlt ⊢
    rw [hAcard] at hlt
    have : j < CFSG.Open.pRank p F + 1 := by
      by_contra hj3
      have : p ^ (CFSG.Open.pRank p F + 1) ≤ p ^ j := Nat.pow_le_pow_right hp.pos (by omega)
      omega
    exact Nat.pow_le_pow_right hp.pos (by omega)
  have hrange : Nat.card κ₀.range * p ≤ p ^ CFSG.Open.pRank p F := by
    have hordā : orderOf (⟨_, hāmem⟩ : ↥(barX p N (E ⊓ A))) = p := by
      apply orderOf_eq_prime
      · exact Subtype.ext hā
      · intro h1
        exact hā1 (congrArg Subtype.val h1)
    have hker : Subgroup.zpowers (⟨_, hāmem⟩ : ↥(barX p N (E ⊓ A))) ≤ κ₀.ker := by
      rw [Subgroup.zpowers_le]
      exact hκā
    have hdvd : p ∣ Nat.card κ₀.ker := by
      have := Subgroup.card_dvd_of_le hker
      rwa [Nat.card_zpowers, hordā] at this
    obtain ⟨c, hc⟩ := hdvd
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · exfalso
        have : 0 < Nat.card κ₀.ker := Nat.card_pos
        rw [hc, h0] at this
        simp at this
      · exact h0
    have h1 : κ₀.ker.index * Nat.card κ₀.ker = Nat.card (barX p N (E ⊓ A)) :=
      Subgroup.index_mul_card _
    rw [Subgroup.index_ker, hc, card_barX_of_isPGroup hp (inf_le_right.trans hAN)
      ((A_el h).mono inf_le_right).isPGroup] at h1
    calc Nat.card κ₀.range * p ≤ Nat.card κ₀.range * (p * c) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hcpos)
      _ = Nat.card (E ⊓ A : Subgroup G) := by rw [← h1]
      _ ≤ p ^ CFSG.Open.pRank p F := hA0card
  have hrange' : Nat.card κ₀.range ≤ p ^ (CFSG.Open.pRank p F - 1) := by
    have hr1 : p ^ CFSG.Open.pRank p F = p ^ (CFSG.Open.pRank p F - 1) * p := by
      rw [← pow_succ]
      congr 1
      have := hs.hr
      omega
    rw [hr1] at hrange
    exact Nat.le_of_mul_le_mul_right hrange hp.pos
  have hAinj : ∀ u (huA : u ∈ A), QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨u, hAN huA⟩ = 1 →
      u = 1 := by
    intro u huA hu1
    have hinj := injective_barX_comp hp (A_el h).isPGroup hAN
    have : (⟨⟨u, hAN huA⟩, (Subgroup.mem_subgroupOf).2 huA⟩ : ↥(A.subgroupOf N)) = 1 :=
      hinj (by simpa using hu1)
    exact congrArg (fun w : ↥(A.subgroupOf N) => ((w : ↥N) : G)) this
  have hB₀ne : κ₀.range ≠ ⊥ := by
    intro hbot
    obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (A0_inf_F_ne_bot h hs)
    have hyEA : (y : G) ∈ E ⊓ A := y.2.1
    have hyF : (y : G) ∈ F := y.2.2
    have hyN : (y : G) ∈ N := hAN hyEA.2
    have hyks : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨(y : G), hyN⟩ ∈
        Lemma129W.kstar p (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩) (barX p N K) :=
      hFkstar ⟨⟨(y : G), hyN⟩, (Subgroup.mem_subgroupOf).2 hyF, rfl⟩
    have hyc : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨(y : G), hyN⟩ *
        QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩ =
        QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩ *
          QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨(y : G), hyN⟩ :=
      mk_comm_of_comm hyN ha₀N (hFa' _ hyF)
    obtain ⟨u, hu⟩ := hΔ3 _ hyks hyc
    have hymem : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨(y : G), hyN⟩ ∈ barX p N (E ⊓ A) :=
      ⟨⟨(y : G), hyN⟩, (Subgroup.mem_subgroupOf).2 hyEA, rfl⟩
    have hκy : κ₀ ⟨_, hymem⟩ = 1 := by
      have : κ₀ ⟨_, hymem⟩ ∈ κ₀.range := ⟨_, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    have hu1 : u = 1 := by
      have hv' : ∀ v : ↥(barX p N K), u * v = v * u := by
        intro v
        have hx : Δ v ∈ K₀ := ⟨v, rfl⟩
        have h1 := hκ₀ ⟨_, hymem⟩ ⟨Δ v, hx⟩
        rw [hκy] at h1
        simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at h1
        rw [← hu] at h1
        have h2 : Δ (u * v * u⁻¹) = Δ v := by rw [map_mul, map_mul, map_inv]; exact h1
        have h3 := hΔinj h2
        calc u * v = (u * v * u⁻¹) * u := by group
          _ = v * u := by rw [h3]
      apply Subtype.ext
      exact hcenter (u : ↥N ⧸ GLAPPrimeCore p ↥N) u.2
        fun v hv => congrArg Subtype.val (hv' ⟨v, hv⟩)
    exact hy1 (Subtype.ext (hAinj y hyEA.2 (by rw [← hu, hu1, map_one])))
  have hA0el : IsElemAbelian p (E ⊓ A) := (A_el h).mono inf_le_right
  have hB₀p : IsPGroup p κ₀.range := by
    have hFtop : IsElemAbelian p (⊤ : Subgroup ↥(barX p N (E ⊓ A))) := by
      have := (isElemAbelian_barX (p := p) (C := N) hA0el).subgroupOf (barX p N (E ⊓ A))
      rwa [Subgroup.subgroupOf_self] at this
    rw [MonoidHom.range_eq_map]
    exact (hFtop.map κ₀).isPGroup
  obtain ⟨t, ht1, hall, i₀, hi₀⟩ := exists_orbit_exponent hp ψ₀ hB₀p hB₀ne
  have htr : t < CFSG.Open.pRank p F := by
    have h1 : p ^ t ≤ p ^ (CFSG.Open.pRank p F - 1) := by
      rw [← hi₀]
      exact (orbitLen_le_card ψ₀ κ₀.range i₀).trans hrange'
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
    have := hs.hr
    omega
  have hn := D'.hn
  have hδ := D'.hδ
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
  obtain ⟨P, hPN, hPel, hPc, hPrank, hPK, hcov⟩ := acl_cover h23 h hpn ht1 htn ψ₀ κ₀ hκ₀ hB₀ne hall
    ⟨i₀, hi₀⟩
  have hKks : K₀ ≤ Subgroup.normalizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N)) := by
    refine le_trans ?_ (kstar_le_normalizer hcommY hp.pos)
    rintro _ ⟨x, rfl⟩
    exact (hΔ2 x).1
  have ha₀P : a₀ ∉ P := by
    intro ha₀P
    have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩ ∈ barX p N P :=
      ⟨⟨a₀, ha₀N⟩, (Subgroup.mem_subgroupOf).2 ha₀P, rfl⟩
    apply ha₀K
    refine mem_normalizer_of_mk hp hs.hK ha₀N ?_
    exact hKks (hPK hmem)
  have hWel : IsElemAbelian p ((E ⊓ A) ⊔ P) := hA0el.sup_of_commute hPel hPc
  have hPlt : P < (E ⊓ A) ⊔ P := by
    refine lt_of_le_of_ne le_sup_right fun heq => ha₀P ?_
    rw [heq]
    exact Subgroup.mem_sup_left ha₀EA
  have hPrank1 : CFSG.Open.pRank p P + 1 ≤ CFSG.Open.pRank p ((E ⊓ A) ⊔ P) := by
    have h1 := card_lt_of_lt' hPlt
    rw [card_eq_pow_pRank hp hPel, card_eq_pow_pRank hp hWel] at h1
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 h1
  have hbig : CFSG.Open.pRank p A < CFSG.Open.pRank p ((E ⊓ A) ⊔ P) := by
    have := arith_big hp3 hs.hr ht1 htr hpr
    omega
  have hKM : K₀ ≤ barX p N M := hcov hbig
  have hĀS : barX p N A ≤ Subgroup.normalizer (barX p N S : Set (↥N ⧸ GLAPPrimeCore p ↥N)) :=
    barX_le_normalizer hs.hS.norm
  have hāA : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩ ∈ barX p N A :=
    barX_mono129 inf_le_right hāmem
  have hSconj : ∀ s ∈ barX p N S, ∀ i : Fin p,
      ∀ x ∈ Lemma129W.kconj (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩) (barX p N K) i,
      s * x * s⁻¹ ∈ Lemma129W.kconj (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩)
        (barX p N K) i := by
    intro s hsS i x hx
    obtain ⟨k, hk, rfl⟩ := hx
    set ā := QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩ with hādef
    have hg : (ā ^ (i : ℕ))⁻¹ ∈ barX p N A := (barX p N A).inv_mem ((barX p N A).pow_mem hāA _)
    have hs' : (ā ^ (i : ℕ))⁻¹ * s * ((ā ^ (i : ℕ))⁻¹)⁻¹ ∈ barX p N S :=
      (Subgroup.mem_normalizer_iff.1 (hĀS hg) s).1 hsS
    have hk' := Subgroup.mem_normalizer_iff.1 (hs.hSK hs') k
    have hk'' : ((ā ^ (i : ℕ))⁻¹ * s * ((ā ^ (i : ℕ))⁻¹)⁻¹) * k *
        ((ā ^ (i : ℕ))⁻¹ * s * ((ā ^ (i : ℕ))⁻¹)⁻¹)⁻¹ ∈ barX p N K := hk'.1 hk
    refine ⟨_, hk'', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hSks : ∀ s ∈ barX p N S, ∀ x ∈ Lemma129W.kstar p
      (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩) (barX p N K),
      s * x * s⁻¹ ∈ Lemma129W.kstar p (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩)
        (barX p N K) := by
    intro s hsS
    have hle : Lemma129W.kstar p (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩)
        (barX p N K) ≤ (Lemma129W.kstar p (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩)
          (barX p N K)).comap (MulAut.conj s).toMonoidHom := by
      refine iSup_le fun i x hx => ?_
      exact le_iSup (fun i : Fin p => Lemma129W.kconj
        (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩) (barX p N K) i) i
          (hSconj s hsS i x hx)
    intro x hx
    exact hle hx
  have hSnorm : ∀ s ∈ barX p N S, ∀ i : Fin p,
      s ∈ Subgroup.normalizer ((Lemma129W.kconj
        (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩) (barX p N K) i : Subgroup _) :
          Set (↥N ⧸ GLAPPrimeCore p ↥N)) := by
    intro s hsS i
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hSconj s hsS i x, fun hx => ?_⟩
    have := hSconj s⁻¹ ((barX p N S).inv_mem hsS) i _ hx
    rwa [show s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x by group] at this
  have hO2 : IsPGroup 2 ↥(barX p N (pCoreOf 2 M)) :=
    isPGroup_barX (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) h.hO
  have hT'2 : IsPGroup 2 ↥((barX p N (pCoreOf 2 M)).subgroupOf
      (Lemma129W.kstar p (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩) (barX p N K))) :=
    hO2.comap_subtype
  have hOb : IsPGroup 2 ↥(((barX p N (pCoreOf 2 M)).subgroupOf
      (Lemma129W.kstar p (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩) (barX p N K))).map
      ((barX p N K).subtype.comp π₀)) :=
    hT'2.map _
  have hcomm : ∀ s ∈ barX p N S, ∀ k ∈ barX p N K, s * k * s⁻¹ * k⁻¹ ∈
      ((barX p N (pCoreOf 2 M)).subgroupOf
        (Lemma129W.kstar p (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩) (barX p N K))).map
        ((barX p N K).subtype.comp π₀) := by
    intro s hsS k hk
    have hkM : Δ ⟨k, hk⟩ ∈ barX p N M := hKM ⟨⟨k, hk⟩, rfl⟩
    have hc := S_comm_M h hs s hsS _ hkM
    have hΔk := (hΔ2 ⟨k, hk⟩).1
    have hsΔ := hSks s hsS _ hΔk
    have hcKS := Subgroup.mul_mem _ hsΔ (Subgroup.inv_mem _ hΔk)
    refine ⟨⟨_, hcKS⟩, (Subgroup.mem_subgroupOf).2 hc, ?_⟩
    have e : (⟨s * Δ ⟨k, hk⟩ * s⁻¹ * (Δ ⟨k, hk⟩)⁻¹, hcKS⟩ :
        ↥(Lemma129W.kstar p (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩) (barX p N K))) =
        ⟨s * Δ ⟨k, hk⟩ * s⁻¹, hsΔ⟩ *
          (⟨Δ ⟨k, hk⟩, hΔk⟩ : ↥(Lemma129W.kstar p
            (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨a₀, ha₀N⟩) (barX p N K)))⁻¹ := rfl
    have h7 := hπ7 s (hSnorm s hsS) ⟨Δ ⟨k, hk⟩, hΔk⟩ hsΔ
    have h4 : π₀ ⟨Δ ⟨k, hk⟩, hΔk⟩ = ⟨k, hk⟩ := hπ4 ⟨k, hk⟩ hΔk
    rw [h4] at h7
    show ((π₀ ⟨s * Δ ⟨k, hk⟩ * s⁻¹ * (Δ ⟨k, hk⟩)⁻¹, hcKS⟩ : ↥(barX p N K)) :
      ↥N ⧸ GLAPPrimeCore p ↥N) = _
    rw [e, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, h4]
    exact congrArg (· * k⁻¹) h7
  have hbot : ⁅barX p N S, barX p N K⁆ = ⊥ :=
    commutator_eq_bot_of_cover hs.hSK le_rfl hcomm hOb
      fun T hTK hn h2 => eq_bot_of_normal_two_group hp hp2 hs.hK hTK hn h2
  exact hs.hKc (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot)

end Helpers

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129i

end
